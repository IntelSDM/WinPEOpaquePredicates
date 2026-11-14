#include "WinPEOpaquePass.h"

#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Alignment.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <random>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

using namespace llvm;

llvm::cl::opt<bool> WinPEOpaqueEnable("obfpeop", llvm::cl::init(true), llvm::cl::desc("Runtime Opaques Using Known Windows Limitations"));

static constexpr bool EnablePebWalkModule = true;
static constexpr bool EnablePebImageBase = true;
static constexpr bool EnablePebDirect = true;
static constexpr bool EnableTebDirect = true;
static constexpr bool EnableTebStackBase = true;
static constexpr bool EnableTebStackLimit = true;
static constexpr bool EnableProcessHeap = true;
static constexpr bool EnableTebSelfRef = true;
static constexpr bool EnablePebSelfRef = true;
static constexpr bool EnablePebNeTeb = true;
static constexpr bool EnablePebNeImgBase = true;
static constexpr bool EnableEatHashHit = true;
static constexpr bool EnableEatHashMiss = true;
static constexpr bool EnableDispatchScan = true;
static constexpr unsigned DispatchScanPct = 25;
static constexpr bool EnableHeapAcc = true;
static constexpr unsigned HeapAccPct = 20;
static constexpr unsigned ArbExportPct = 60;

static constexpr unsigned PerFunctionCap = 8;
static constexpr unsigned MinBBInsts = 2;
static constexpr bool SkipLoops = false;
static constexpr bool SkipEntry = false;

static constexpr unsigned ArxMinSteps = 4;
static constexpr unsigned ArxMaxSteps = 7;

static constexpr unsigned MinBadValues = 2;
static constexpr unsigned MaxBadValues = 6;

static constexpr unsigned MaxModuleIndex = 4;

static constexpr unsigned MinSourcesPerSite = 1;
static constexpr unsigned MaxSourcesPerSite = 3;

static constexpr unsigned MinScanRealSlots = 3;
static constexpr unsigned MaxScanRealSlots = 5;
static constexpr unsigned MinScanFakeSlots = 3;
static constexpr unsigned MaxScanFakeSlots = 6;
static constexpr unsigned MinScanDeadSums = 3;
static constexpr unsigned MaxScanDeadSums = 5;

static constexpr unsigned PolluteOpsMin = 4;
static constexpr unsigned PolluteOpsMax = 12;
static constexpr unsigned CorruptionSpillPctPerOp = 20;

static constexpr unsigned StealMaxCap = 6;
static constexpr unsigned StealMinRealResidue = 4;

static constexpr uint64_t FNVOffset = 0xcbf29ce484222325ULL;
static constexpr uint64_t FNVPrime = 0x100000001b3ULL;

static bool HasAnnotationTag(Function& f, const char* tag)
{
    Module* m = f.getParent();
    GlobalVariable* ga = m->getGlobalVariable("llvm.global.annotations");
    if (!ga || !ga->hasInitializer()) return false;
    auto* ca = dyn_cast<ConstantArray>(ga->getOperand(0));
    if (!ca) return false;
    for (unsigned i = 0; i < ca->getNumOperands(); ++i)
    {
        auto* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
        if (!cs || cs->getNumOperands() < 2) continue;
        if (cs->getOperand(0)->stripPointerCasts() != &f) continue;
        auto* annogv = dyn_cast<GlobalVariable>(cs->getOperand(1)->stripPointerCasts());
        if (!annogv || !annogv->hasInitializer()) continue;
        auto* cds = dyn_cast<ConstantDataSequential>(annogv->getInitializer());
        if (!cds || !cds->isString()) continue;
        if (strcmp(cds->getAsString().str().c_str(), tag) == 0) return true;
    }
    return false;
}

static bool HasObfuscateAnnotation(Function& f) { return HasAnnotationTag(f, "obfus"); }
static bool HasNoObfuscateAnnotation(Function& f) { return HasAnnotationTag(f, "noobfus"); }
static bool HasNoWinPEOpAnnotation(Function& f) { return HasAnnotationTag(f, "nowinpeop"); }

static std::mt19937_64 Rng;
static AllocaInst* PerFuncScratchAlloca = nullptr;

static unsigned DispatchScanSiteCounter = 0;
static unsigned EatLookupSiteCounter = 0;
static unsigned HeapAccSiteCounter = 0;

static bool BBAlreadyProcessed(BasicBlock* bb)
{
    Instruction* term = bb->getTerminator();
    if (!term) return true;
    return term->getMetadata("relocop.done") != nullptr;
}

static void MarkBBProcessed(BasicBlock* bb)
{
    Instruction* term = bb->getTerminator();
    if (!term) return;
    term->setMetadata("relocop.done", MDNode::get(bb->getContext(), {}));
}

static bool IsPolluteBlock(BasicBlock* bb)
{
    Instruction* term = bb->getTerminator();
    if (!term) return false;
    return term->getMetadata("relocop.pollute") != nullptr;
}

static void MarkPolluteBlock(BasicBlock* bb)
{
    Instruction* term = bb->getTerminator();
    if (!term) return;
    term->setMetadata("relocop.pollute", MDNode::get(bb->getContext(), {}));
}

static bool IsCheckBlock(BasicBlock* bb)
{
    Instruction* term = bb->getTerminator();
    if (!term) return false;
    return term->getMetadata("relocop.check") != nullptr;
}

static void MarkCheckBlock(BasicBlock* bb)
{
    Instruction* term = bb->getTerminator();
    if (!term) return;
    term->setMetadata("relocop.check", MDNode::get(bb->getContext(), {}));
}

static bool IsEHOrFuncletInterior(BasicBlock* bb)
{
    if (bb->isEHPad()) return true;
    Instruction* term = bb->getTerminator();
    if (!term) return true;
    if (isa<CatchReturnInst>(term) || isa<CleanupReturnInst>(term) || isa<ResumeInst>(term)) return true;
    for (Instruction& i : *bb)
    {
        if (auto* cb = dyn_cast<CallBase>(&i))
        {
            if (cb->countOperandBundlesOfType(LLVMContext::OB_funclet) > 0) return true;
        }
    }
    return false;
}

static Instruction* PickInsertionPoint(BasicBlock* bb)
{
    Instruction* first = bb->getFirstNonPHIOrDbgOrLifetime();
    if (!first) return nullptr;
    if ((unsigned)bb->size() < MinBBInsts) return nullptr;

    // splitting the entry block before an alloca relocates the alloca into realbb and demotes it from static to dynamic, which breaks AllocaInst::isStaticAlloca downstream; clamp `first` past the last entry alloca so every alloca stays in the head
    if (bb == &bb->getParent()->getEntryBlock())
    {
        Instruction* lastalloca = nullptr;
        for (Instruction& i : *bb)
        {
            if (isa<AllocaInst>(&i)) lastalloca = &i;
        }
        if (lastalloca)
        {
            Instruction* after = lastalloca->getNextNode();
            if (!after) return nullptr;
            BasicBlock::iterator seek(first);
            while (seek != bb->end() && &*seek != after) ++seek;
            if (seek != bb->end()) first = &*seek;
            else first = after;
        }
    }

    unsigned splittable = 0;
    for (auto it = BasicBlock::iterator(first); it != bb->end(); ++it)
    {
        if (&*it == bb->getTerminator()) break;
        ++splittable;
    }
    if (splittable == 0) return nullptr;

    const unsigned pick = (unsigned)(Rng() % splittable);
    BasicBlock::iterator it(first);
    for (unsigned i = 0; i < pick; ++i) ++it;
    if (it == bb->end()) return nullptr;
    if (&*it == bb->getTerminator()) return nullptr;
    if (isa<PHINode>(&*it)) return nullptr;
    return &*it;
}

enum class FactKind : uint8_t
{
    Top12 = 0,
    Top8,
    Top4,
    Lo16,
    Lo8,
    LoByte1,
    Hi16Zero,
    Top12At32,
    Top8At32,
    Top4At32,
    Bit47Zero,
    Count
};

struct FactInfo
{
    const char* Name;
    unsigned Shift;
    uint64_t Mask;
    uint32_t RtValue;
};

static constexpr FactInfo FactLibrary[(size_t)FactKind::Count] =
{
    { "top12", 36, 0xFFFULL, 0x7FFu },
    { "top8", 40, 0xFFULL, 0x7Fu },
    { "top4", 44, 0xFULL, 0x7u },
    { "lo16", 0, 0xFFFFULL, 0x0u },
    { "lo8", 0, 0xFFULL, 0x0u },
    { "lo_byte1", 8, 0xFFULL, 0x0u },
    { "hi16zero", 48, 0xFFFFULL, 0x0u },
    { "top12_at_32", 32, 0xFFF0ULL, 0x7FF0u },
    { "top8_at_32", 32, 0xFF00ULL, 0x7F00u },
    { "top4_at_32", 32, 0xF000ULL, 0x7000u },
    { "bit47_zero", 32, 0x8000ULL, 0x0u },
};

// AND MUST be emitted even when the shift already bounds the result; gives ida a visible masking op per site and LLVM's InstCombine won't drop the mask because it isn't a no-op from the IR's point of view, so the extraction stays recognizable in the disassembly
static Value* EmitFactExtract(IRBuilder<>& b, Value* sourcei64, FactKind kind)
{
    LLVMContext& c = b.getContext();
    IntegerType* i32 = Type::getInt32Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    const FactInfo& info = FactLibrary[(size_t)kind];

    Value* v = sourcei64;
    if (info.Shift > 0) v = b.CreateLShr(v, ConstantInt::get(i64, info.Shift), "RelocopFactShift");
    v = b.CreateAnd(v, ConstantInt::get(i64, info.Mask), "RelocopFactMask");
    return b.CreateTrunc(v, i32, "RelocopFactValue");
}

// impossible value MUST stay within [0, mask] so LLVM's KnownBits analysis cannot prove the comparison trivially false and fold the branch; values outside the mask shape are KnownBits false and InstCombine would collapse the branch, defeating the opaque
static uint32_t GenerateImpossibleForFact(FactKind kind)
{
    const FactInfo& info = FactLibrary[(size_t)kind];
    uint32_t v;
    do { v = (uint32_t)(Rng() & info.Mask); } while (v == info.RtValue);
    return v;
}

enum class SourceKind : uint8_t
{
    PebWalkModule = 0,
    PebImageBase,
    PebDirect,
    TebDirect,
    TebStackBase,
    TebStackLimit,
    ProcessHeap,
    EatHashHit,
    EatHashMiss,
    Count
};

struct SourceInfo
{
    const char* Name;
    uint32_t CompatibleFacts;
};

static constexpr uint32_t FullFactMask = (1u << (unsigned)FactKind::Count) - 1u;

static constexpr uint32_t PebTebFactMask = (1u << (unsigned)FactKind::Lo8) | (1u << (unsigned)FactKind::Hi16Zero) | (1u << (unsigned)FactKind::Bit47Zero);

static constexpr uint32_t ZeroFactMask = (1u << (unsigned)FactKind::Lo16) | (1u << (unsigned)FactKind::Lo8) | (1u << (unsigned)FactKind::LoByte1) | (1u << (unsigned)FactKind::Hi16Zero) | (1u << (unsigned)FactKind::Bit47Zero);

static constexpr SourceInfo SourceLibrary[(size_t)SourceKind::Count] =
{
    { "peb_walk_module", FullFactMask },
    { "peb_image_base", FullFactMask },
    { "peb_direct", PebTebFactMask },
    { "teb_direct", PebTebFactMask },
    { "teb_stackbase", PebTebFactMask },
    { "teb_stacklimit", PebTebFactMask },
    { "process_heap", PebTebFactMask },
    { "eat_hash_hit", FullFactMask },
    { "eat_hash_miss", ZeroFactMask },
};

enum class OpaqueKind : uint8_t { Cascade, DispatchScan };

struct BinaryImport
{
    std::string Dll;
    std::string Exp;
};

static std::unordered_map<std::string, std::string> ExportToDll;
static bool ExportCacheLoaded = false;
static std::vector<BinaryImport> WhitelistExports;
static std::vector<std::string> WhitelistDlls;
static std::vector<BinaryImport> BinaryImports;

static std::vector<std::string> ParseDllExports(const std::string& path)
{
    std::vector<std::string> result;
    std::ifstream f(path, std::ios::binary);
    if (!f.is_open()) return result;

    uint16_t dossig = 0;
    f.read((char*)&dossig, 2);
    if (dossig != 0x5A4D) return result;
    int32_t elfanew = 0;
    f.seekg(0x3C);
    f.read((char*)&elfanew, 4);

    f.seekg(elfanew);
    uint32_t pesig = 0;
    f.read((char*)&pesig, 4);
    if (pesig != 0x00004550) return result;

    f.seekg(elfanew + 4 + 2);
    uint16_t numsections = 0;
    f.read((char*)&numsections, 2);
    f.seekg(elfanew + 4 + 16);
    uint16_t sizeoptheader = 0;
    f.read((char*)&sizeoptheader, 2);

    // DataDirectory[0] (ExportTable RVA+Size) sits 112 bytes into the PE32+ OptionalHeader; the header starts at e_lfanew+24, so the absolute offset is e_lfanew+24+112; this hardcode is correct only for PE32+ (x64), which is fine because we only ships x64 modules
    f.seekg(elfanew + 24 + 112);
    uint32_t exprva = 0;
    uint32_t expsize = 0;
    f.read((char*)&exprva, 4);
    f.read((char*)&expsize, 4);
    if (!exprva) return result;

    f.seekg(elfanew + 24 + sizeoptheader);
    struct SectionInfo
    {
        uint32_t Vrva;
        uint32_t Vsize;
        uint32_t Fpos;
    };
    std::vector<SectionInfo> sects(numsections);
    for (uint16_t i = 0; i < numsections; ++i)
    {
        char name[8];
        f.read(name, 8);
        f.read((char*)&sects[i].Vsize, 4);
        f.read((char*)&sects[i].Vrva, 4);
        uint32_t sizeraw = 0;
        f.read((char*)&sizeraw, 4);
        f.read((char*)&sects[i].Fpos, 4);
        f.seekg(16, std::ios::cur);
    }

    auto rvatofile = [&](uint32_t rva) -> uint32_t
    {
        for (const auto& s : sects)
        {
            if (rva >= s.Vrva && rva < s.Vrva + s.Vsize) return s.Fpos + (rva - s.Vrva);
        }
        return 0;
    };

    const uint32_t expfile = rvatofile(exprva);
    if (!expfile) return result;
    f.seekg(expfile + 24);
    uint32_t numnames = 0;
    f.read((char*)&numnames, 4);
    uint32_t namesrva = 0;
    f.seekg(expfile + 32);
    f.read((char*)&namesrva, 4);

    const uint32_t namesfile = rvatofile(namesrva);
    if (!namesfile) return result;
    std::vector<uint32_t> namervas(numnames);
    f.seekg(namesfile);
    f.read((char*)namervas.data(), (std::streamsize)numnames * 4);

    result.reserve(numnames);
    for (uint32_t rva : namervas)
    {
        const uint32_t fp = rvatofile(rva);
        if (!fp) continue;
        f.seekg(fp);
        std::string name;
        char ch;
        while (f.get(ch) && ch != 0) name.push_back(ch);
        if (!name.empty()) result.push_back(std::move(name));
    }
    return result;
}

static void EnsureExportCache()
{
    if (ExportCacheLoaded) return;
    ExportCacheLoaded = true;

    // whitelist restricted to DLLs universally present in every Windows x64 usermode Win32 GUI process at predicate first eval time; LLVM's dllimport storage class carries NO DLL NAME, so attributing an import to a DLL the binary doesn't load (msvcrt vs ucrtbase CRT split, on demand advapi32/ole32) makes the PEB.Ldr walk return 0, which fails ArxMatch and flows into pollute on live code; anything outside this five-DLL set is silently dropped
    static constexpr const char* SystemDlls[] = {
        "ntdll.dll",
        "kernelbase.dll",
        "kernel32.dll",
        "user32.dll",
        "gdi32.dll",
    };

    const char* windir = std::getenv("WINDIR");
    const std::string sys32 = std::string(windir ? windir : "C:\\Windows") + "\\System32\\";

    for (const char* dllname : SystemDlls)
    {
        std::vector<std::string> exports = ParseDllExports(sys32 + dllname);
        if (exports.empty()) continue;
        WhitelistDlls.emplace_back(dllname);
        WhitelistExports.reserve(WhitelistExports.size() + exports.size());
        for (const auto& e : exports)
        {
            WhitelistExports.push_back({ dllname, e });
            ExportToDll.try_emplace(e, dllname);
        }
    }
}

static void PopulateBinaryImports(Module& m)
{
    BinaryImports.clear();
    EnsureExportCache();

    std::set<std::string> seen;
    for (Function& f : m)
    {
        if (!f.isDeclaration()) continue;
        if (!f.hasDLLImportStorageClass()) continue;
        std::string name = f.getName().str();
        if (!seen.insert(name).second) continue;
        auto it = ExportToDll.find(name);
        if (it == ExportToDll.end()) continue;
        BinaryImports.push_back({ it->second, name });
    }
}

struct EatPlan
{
    uint64_t ModHash;
    uint64_t ExpHash;
    uint32_t Salt;
};

struct EatSiteParams
{
    uint64_t ModHash;
    uint64_t ExpHash;
    uint32_t Salt;
};

static uint64_t Fnv1aAscii(const char* s, uint32_t salt)
{
    uint64_t h = FNVOffset ^ (uint64_t)salt;
    for (; *s; ++s)
    {
        h ^= (uint8_t)*s;
        h *= FNVPrime;
    }
    return h;
}

// hashes each ASCII char as a UTF-16 LE code unit (low byte then high byte zero) to match the loader's BaseDllName.Buffer, which is UTF-16 LE and preserves original casing; the runtime hash lowercases on the fly, so this pass time hash lowercases A-Z before the XOR or the two sides disagree and __rx_eat_lookup returns 0 for every call
static uint64_t Fnv1aUtf16LowerAscii(const char* s, uint32_t salt)
{
    uint64_t h = FNVOffset ^ (uint64_t)salt;
    for (; *s; ++s)
    {
        uint8_t c = (uint8_t)*s;
        if (c >= 'A' && c <= 'Z') c += 32;
        h ^= c;
        h *= FNVPrime;
        h ^= 0;
        h *= FNVPrime;
    }
    return h;
}

static FactKind PickCompatibleFact(uint32_t compatiblemask)
{
    SmallVector<FactKind, (size_t)FactKind::Count> compat;
    for (unsigned i = 0; i < (unsigned)FactKind::Count; ++i)
    {
        if (compatiblemask & (1u << i)) compat.push_back((FactKind)i);
    }
    assert(!compat.empty() && "SourceInfo must declare at least one fact");
    return compat[Rng() % compat.size()];
}

static SmallVector<SourceKind, (size_t)SourceKind::Count> EnumerateEnabledSources()
{
    SmallVector<SourceKind, (size_t)SourceKind::Count> candidates;
    for (unsigned i = 0; i < (unsigned)SourceKind::Count; ++i)
    {
        const SourceKind sk = (SourceKind)i;
        switch (sk)
        {
            case SourceKind::PebWalkModule: if (!EnablePebWalkModule) continue; break;
            case SourceKind::PebImageBase: if (!EnablePebImageBase) continue; break;
            case SourceKind::PebDirect: if (!EnablePebDirect) continue; break;
            case SourceKind::TebDirect: if (!EnableTebDirect) continue; break;
            case SourceKind::TebStackBase: if (!EnableTebStackBase) continue; break;
            case SourceKind::TebStackLimit: if (!EnableTebStackLimit) continue; break;
            case SourceKind::ProcessHeap: if (!EnableProcessHeap) continue; break;
            case SourceKind::EatHashHit:
                if (!EnableEatHashHit) continue;
                if (BinaryImports.empty() && WhitelistExports.empty()) continue;
                break;
            case SourceKind::EatHashMiss:
                if (!EnableEatHashMiss) continue;
                if (BinaryImports.empty() && WhitelistExports.empty()) continue;
                break;
            case SourceKind::Count: continue;
        }
        candidates.push_back(sk);
    }
    if (candidates.empty()) candidates.push_back(SourceKind::PebWalkModule);
    return candidates;
}

static Value* EmitModuleDllBase(IRBuilder<>& b, unsigned modindex)
{
    LLVMContext& c = b.getContext();
    IntegerType* i8 = Type::getInt8Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptr = PointerType::get(c, 0);
    PointerType* ptrgs = PointerType::get(c, 256);

    // GS load MUST be volatile so LLVM can't CSE identical PEB reads across sites; a none volatile load would collapse every site's gs:[0x60] into one SSA value and give an attacker a single pivot point to kill every opaque at once
    Value* gs60addr = b.CreateIntToPtr(ConstantInt::get(i64, 0x60), ptrgs, "RelocopGS60");
    LoadInst* pebint = b.CreateLoad(i64, gs60addr, "RelocopPebI");
    pebint->setAlignment(Align(8));
    pebint->setVolatile(true);
    Value* peb = b.CreateIntToPtr(pebint, ptr, "RelocopPeb");

    Value* ldrslot = b.CreateGEP(i8, peb, ConstantInt::get(i64, 0x18), "RelocopLdrSlot");
    LoadInst* ldr = b.CreateLoad(ptr, ldrslot, "RelocopLdr");
    ldr->setAlignment(Align(8));

    Value* cur = b.CreateGEP(i8, ldr, ConstantInt::get(i64, 0x10), "RelocopHead");

    // walk Flink (offset 0 of LIST_ENTRY) modindex+1 times because the first Flink read lands on the EXE itself (index 0), and InLoadOrderLinks sits at offset 0 of LDR_DATA_TABLE_ENTRY so cur IS the entry pointer after the walk
    for (unsigned i = 0; i <= modindex; ++i)
    {
        LoadInst* nxt = b.CreateLoad(ptr, cur, "RelocopFlink");
        nxt->setAlignment(Align(8));
        cur = nxt;
    }

    Value* dllbaseslot = b.CreateGEP(i8, cur, ConstantInt::get(i64, 0x30), "RelocopDllBaseSlot");
    LoadInst* dllbase = b.CreateLoad(i64, dllbaseslot, "RelocopDllBase");
    dllbase->setAlignment(Align(8));
    return dllbase;
}

static Value* EmitPebDirect(IRBuilder<>& b)
{
    LLVMContext& c = b.getContext();
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptrgs = PointerType::get(c, 256);

    Value* gs60addr = b.CreateIntToPtr(ConstantInt::get(i64, 0x60), ptrgs, "RelocopPdGS60");
    LoadInst* pebint = b.CreateLoad(i64, gs60addr, "RelocopPdPeb");
    pebint->setAlignment(Align(8));
    pebint->setVolatile(true);
    return pebint;
}

static Value* EmitTebDirect(IRBuilder<>& b)
{
    LLVMContext& c = b.getContext();
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptrgs = PointerType::get(c, 256);

    Value* gs30addr = b.CreateIntToPtr(ConstantInt::get(i64, 0x30), ptrgs, "RelocopTdGS30");
    LoadInst* tebint = b.CreateLoad(i64, gs30addr, "RelocopTdTeb");
    tebint->setAlignment(Align(8));
    tebint->setVolatile(true);
    return tebint;
}

static Value* EmitPebImageBase(IRBuilder<>& b)
{
    LLVMContext& c = b.getContext();
    IntegerType* i8 = Type::getInt8Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptr = PointerType::get(c, 0);
    PointerType* ptrgs = PointerType::get(c, 256);

    Value* gs60addr = b.CreateIntToPtr(ConstantInt::get(i64, 0x60), ptrgs, "RelocopPiGS60");
    LoadInst* pebint = b.CreateLoad(i64, gs60addr, "RelocopPiPeb");
    pebint->setAlignment(Align(8));
    pebint->setVolatile(true);
    Value* peb = b.CreateIntToPtr(pebint, ptr, "RelocopPiPebP");

    Value* imgslot = b.CreateGEP(i8, peb, ConstantInt::get(i64, 0x10), "RelocopPiImgSlot");
    LoadInst* imgbase = b.CreateLoad(i64, imgslot, "RelocopPiImg");
    imgbase->setAlignment(Align(8));
    return imgbase;
}

static Value* EmitTebStackBase(IRBuilder<>& b)
{
    LLVMContext& c = b.getContext();
    IntegerType* i8 = Type::getInt8Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptr = PointerType::get(c, 0);
    PointerType* ptrgs = PointerType::get(c, 256);

    Value* gs30addr = b.CreateIntToPtr(ConstantInt::get(i64, 0x30), ptrgs, "RelocopSbGS30");
    LoadInst* tebint = b.CreateLoad(i64, gs30addr, "RelocopSbTeb");
    tebint->setAlignment(Align(8));
    tebint->setVolatile(true);
    Value* teb = b.CreateIntToPtr(tebint, ptr, "RelocopSbTebP");

    Value* sbslot = b.CreateGEP(i8, teb, ConstantInt::get(i64, 0x08), "RelocopSbSlot");
    LoadInst* sb = b.CreateLoad(i64, sbslot, "RelocopSb");
    sb->setAlignment(Align(8));
    return sb;
}

static Value* EmitTebStackLimit(IRBuilder<>& b)
{
    LLVMContext& c = b.getContext();
    IntegerType* i8 = Type::getInt8Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptr = PointerType::get(c, 0);
    PointerType* ptrgs = PointerType::get(c, 256);

    Value* gs30addr = b.CreateIntToPtr(ConstantInt::get(i64, 0x30), ptrgs, "RelocopSlGS30");
    LoadInst* tebint = b.CreateLoad(i64, gs30addr, "RelocopSlTeb");
    tebint->setAlignment(Align(8));
    tebint->setVolatile(true);
    Value* teb = b.CreateIntToPtr(tebint, ptr, "RelocopSlTebP");

    Value* slslot = b.CreateGEP(i8, teb, ConstantInt::get(i64, 0x10), "RelocopSlSlot");
    LoadInst* sl = b.CreateLoad(i64, slslot, "RelocopSl");
    sl->setAlignment(Align(8));
    return sl;
}

static Value* EmitProcessHeap(IRBuilder<>& b)
{
    LLVMContext& c = b.getContext();
    IntegerType* i8 = Type::getInt8Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptr = PointerType::get(c, 0);
    PointerType* ptrgs = PointerType::get(c, 256);

    Value* gs60addr = b.CreateIntToPtr(ConstantInt::get(i64, 0x60), ptrgs, "RelocopPhGS60");
    LoadInst* pebint = b.CreateLoad(i64, gs60addr, "RelocopPhPeb");
    pebint->setAlignment(Align(8));
    pebint->setVolatile(true);
    Value* peb = b.CreateIntToPtr(pebint, ptr, "RelocopPhPebP");

    Value* phslot = b.CreateGEP(i8, peb, ConstantInt::get(i64, 0x30), "RelocopPhSlot");
    LoadInst* ph = b.CreateLoad(i64, phslot, "RelocopPh");
    ph->setAlignment(Align(8));
    return ph;
}

static Function* GetOrCreateHashAsciiFn(Module& m)
{
    static const char* kname = "RxHashAsciiSalted";
    if (Function* existing = m.getFunction(kname)) return existing;

    LLVMContext& c = m.getContext();
    IntegerType* i8 = Type::getInt8Ty(c);
    IntegerType* i32 = Type::getInt32Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptr = PointerType::get(c, 0);

    FunctionType* fty = FunctionType::get(i64, { ptr, i32 }, false);
    Function* f = Function::Create(fty, GlobalValue::InternalLinkage, kname, m);
    f->addFnAttr(Attribute::NoUnwind);
    f->addFnAttr(Attribute::AlwaysInline);
    f->setDoesNotThrow();

    Argument* sarg = f->getArg(0); sarg->setName("s");
    Argument* saltarg = f->getArg(1); saltarg->setName("salt");

    BasicBlock* entry = BasicBlock::Create(c, "Entry", f);
    BasicBlock* loop = BasicBlock::Create(c, "Loop", f);
    BasicBlock* body = BasicBlock::Create(c, "Body", f);
    BasicBlock* done = BasicBlock::Create(c, "Done", f);

    IRBuilder<> b(entry);
    Value* salti64 = b.CreateZExt(saltarg, i64);
    Value* h0 = b.CreateXor(ConstantInt::get(i64, FNVOffset), salti64);
    b.CreateBr(loop);

    b.SetInsertPoint(loop);
    PHINode* hphi = b.CreatePHI(i64, 2, "H");
    PHINode* pphi = b.CreatePHI(ptr, 2, "P");
    hphi->addIncoming(h0, entry);
    pphi->addIncoming(sarg, entry);
    LoadInst* ch = b.CreateLoad(i8, pphi, "C");
    ch->setAlignment(Align(1));
    Value* isnull = b.CreateICmpEQ(ch, ConstantInt::get(i8, 0), "IsNull");
    b.CreateCondBr(isnull, done, body);

    b.SetInsertPoint(body);
    Value* ci64 = b.CreateZExt(ch, i64);
    Value* hxor = b.CreateXor(hphi, ci64);
    Value* hnext = b.CreateMul(hxor, ConstantInt::get(i64, FNVPrime));
    Value* pnext = b.CreateGEP(i8, pphi, ConstantInt::get(i64, 1));
    b.CreateBr(loop);
    hphi->addIncoming(hnext, body);
    pphi->addIncoming(pnext, body);

    b.SetInsertPoint(done);
    b.CreateRet(hphi);
    return f;
}

static Function* GetOrCreateHashWideFn(Module& m)
{
    static const char* kname = "RxHashWideLowerSalted";
    if (Function* existing = m.getFunction(kname)) return existing;

    LLVMContext& c = m.getContext();
    IntegerType* i16 = Type::getInt16Ty(c);
    IntegerType* i32 = Type::getInt32Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptr = PointerType::get(c, 0);

    FunctionType* fty = FunctionType::get(i64, { ptr, i16, i32 }, false);
    Function* f = Function::Create(fty, GlobalValue::InternalLinkage, kname, m);
    f->addFnAttr(Attribute::NoUnwind);
    f->addFnAttr(Attribute::AlwaysInline);
    f->setDoesNotThrow();

    Argument* sarg = f->getArg(0); sarg->setName("s");
    Argument* lenbytes = f->getArg(1); lenbytes->setName("bytelen");
    Argument* saltarg = f->getArg(2); saltarg->setName("salt");

    BasicBlock* entry = BasicBlock::Create(c, "Entry", f);
    BasicBlock* loop = BasicBlock::Create(c, "Loop", f);
    BasicBlock* body = BasicBlock::Create(c, "Body", f);
    BasicBlock* done = BasicBlock::Create(c, "Done", f);

    IRBuilder<> b(entry);
    Value* salti64 = b.CreateZExt(saltarg, i64);
    Value* h0 = b.CreateXor(ConstantInt::get(i64, FNVOffset), salti64);
    Value* wlen = b.CreateLShr(lenbytes, ConstantInt::get(i16, 1), "Wlen");
    b.CreateBr(loop);

    b.SetInsertPoint(loop);
    PHINode* hphi = b.CreatePHI(i64, 2, "H");
    PHINode* iphi = b.CreatePHI(i16, 2, "I");
    hphi->addIncoming(h0, entry);
    iphi->addIncoming(ConstantInt::get(i16, 0), entry);
    Value* atend = b.CreateICmpEQ(iphi, wlen, "AtEnd");
    b.CreateCondBr(atend, done, body);

    b.SetInsertPoint(body);
    Value* p = b.CreateGEP(i16, sarg, iphi, "P");
    LoadInst* wc = b.CreateLoad(i16, p, "Wc");
    wc->setAlignment(Align(2));
    Value* wci32 = b.CreateZExt(wc, i32);
    Value* geA = b.CreateICmpUGE(wci32, ConstantInt::get(i32, 'A'));
    Value* leZ = b.CreateICmpULE(wci32, ConstantInt::get(i32, 'Z'));
    Value* isup = b.CreateAnd(geA, leZ);
    Value* plus32 = b.CreateAdd(wci32, ConstantInt::get(i32, 32));
    Value* lower = b.CreateSelect(isup, plus32, wci32);
    Value* lo = b.CreateAnd(lower, ConstantInt::get(i32, 0xFF));
    Value* loi64 = b.CreateZExt(lo, i64);
    Value* h1 = b.CreateXor(hphi, loi64);
    Value* h2 = b.CreateMul(h1, ConstantInt::get(i64, FNVPrime));
    Value* hi = b.CreateLShr(lower, ConstantInt::get(i32, 8));
    Value* him = b.CreateAnd(hi, ConstantInt::get(i32, 0xFF));
    Value* hii64 = b.CreateZExt(him, i64);
    Value* h3 = b.CreateXor(h2, hii64);
    Value* hnext = b.CreateMul(h3, ConstantInt::get(i64, FNVPrime));
    Value* inext = b.CreateAdd(iphi, ConstantInt::get(i16, 1));
    b.CreateBr(loop);
    hphi->addIncoming(hnext, body);
    iphi->addIncoming(inext, body);

    b.SetInsertPoint(done);
    b.CreateRet(hphi);
    return f;
}

static Function* GetOrCreateEatLookupFn(Module& m)
{
    static const char* kname = "RxEatLookup";
    if (Function* existing = m.getFunction(kname)) return existing;

    LLVMContext& c = m.getContext();
    IntegerType* i8 = Type::getInt8Ty(c);
    IntegerType* i16 = Type::getInt16Ty(c);
    IntegerType* i32 = Type::getInt32Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptr = PointerType::get(c, 0);
    PointerType* ptrgs = PointerType::get(c, 256);

    Function* fnhashascii = GetOrCreateHashAsciiFn(m);
    Function* fnhashwide = GetOrCreateHashWideFn(m);

    FunctionType* fty = FunctionType::get(i64, { i64, i64, i32 }, false);
    Function* f = Function::Create(fty, GlobalValue::InternalLinkage, kname, m);
    f->addFnAttr(Attribute::NoUnwind);
    f->addFnAttr(Attribute::AlwaysInline);
    f->setDoesNotThrow();

    Argument* modhash = f->getArg(0); modhash->setName("modhash");
    Argument* exphash = f->getArg(1); exphash->setName("exphash");
    Argument* salt = f->getArg(2); salt->setName("salt");

    BasicBlock* entry = BasicBlock::Create(c, "Entry", f);
    BasicBlock* modloop = BasicBlock::Create(c, "ModLoop", f);
    BasicBlock* checkmod = BasicBlock::Create(c, "CheckMod", f);
    BasicBlock* modnext = BasicBlock::Create(c, "ModNext", f);
    BasicBlock* foundmod = BasicBlock::Create(c, "FoundMod", f);
    BasicBlock* exploop = BasicBlock::Create(c, "ExpLoop", f);
    BasicBlock* checkexp = BasicBlock::Create(c, "CheckExp", f);
    BasicBlock* expnext = BasicBlock::Create(c, "ExpNext", f);
    BasicBlock* foundexp = BasicBlock::Create(c, "FoundExp", f);
    BasicBlock* notfound = BasicBlock::Create(c, "NotFound", f);

    IRBuilder<> b(entry);
    Value* gs60 = b.CreateIntToPtr(ConstantInt::get(i64, 0x60), ptrgs, "GS60");
    LoadInst* pebi = b.CreateLoad(i64, gs60, "PebI");
    pebi->setAlignment(Align(8));
    pebi->setVolatile(true);
    Value* peb = b.CreateIntToPtr(pebi, ptr, "Peb");
    Value* ldrslot = b.CreateGEP(i8, peb, ConstantInt::get(i64, 0x18), "LdrSlot");
    LoadInst* ldr = b.CreateLoad(ptr, ldrslot, "Ldr");
    ldr->setAlignment(Align(8));
    Value* head = b.CreateGEP(i8, ldr, ConstantInt::get(i64, 0x10), "Head");
    LoadInst* firstflink = b.CreateLoad(ptr, head, "FirstFlink");
    firstflink->setAlignment(Align(8));
    b.CreateBr(modloop);

    b.SetInsertPoint(modloop);
    PHINode* curentry = b.CreatePHI(ptr, 2, "CurEntry");
    curentry->addIncoming(firstflink, entry);
    Value* athead = b.CreateICmpEQ(curentry, head, "AtHead");
    b.CreateCondBr(athead, notfound, checkmod);

    b.SetInsertPoint(checkmod);
    Value* lenslot = b.CreateGEP(i8, curentry, ConstantInt::get(i64, 0x58), "LenSlot");
    LoadInst* namelenbytes = b.CreateLoad(i16, lenslot, "NameLenBytes");
    namelenbytes->setAlignment(Align(2));
    Value* bufslot = b.CreateGEP(i8, curentry, ConstantInt::get(i64, 0x60), "BufSlot");
    LoadInst* namebuf = b.CreateLoad(ptr, bufslot, "NameBuf");
    namebuf->setAlignment(Align(8));
    Value* thismodhash = b.CreateCall(fnhashwide, { namebuf, namelenbytes, salt }, "ThisModHash");
    Value* modmatches = b.CreateICmpEQ(thismodhash, modhash, "ModMatches");
    b.CreateCondBr(modmatches, foundmod, modnext);

    b.SetInsertPoint(modnext);
    LoadInst* nextentry = b.CreateLoad(ptr, curentry, "NextEntry");
    nextentry->setAlignment(Align(8));
    b.CreateBr(modloop);
    curentry->addIncoming(nextentry, modnext);

    b.SetInsertPoint(foundmod);
    Value* baseslot = b.CreateGEP(i8, curentry, ConstantInt::get(i64, 0x30), "BaseSlot");
    LoadInst* basei = b.CreateLoad(i64, baseslot, "BaseI");
    basei->setAlignment(Align(8));
    Value* base = b.CreateIntToPtr(basei, ptr, "Base");
    Value* elfanewslot = b.CreateGEP(i8, base, ConstantInt::get(i64, 0x3C), "ElfanewSlot");
    LoadInst* elfanew = b.CreateLoad(i32, elfanewslot, "Elfanew");
    elfanew->setAlignment(Align(4));
    Value* elfanewi64 = b.CreateSExt(elfanew, i64);
    Value* nt = b.CreateGEP(i8, base, elfanewi64, "Nt");
    Value* exprvaslot = b.CreateGEP(i8, nt, ConstantInt::get(i64, 0x88), "ExpRvaSlot");
    LoadInst* exprva = b.CreateLoad(i32, exprvaslot, "ExpRva");
    exprva->setAlignment(Align(4));
    Value* expdir = b.CreateGEP(i8, base, b.CreateZExt(exprva, i64), "ExpDir");
    Value* nnslot = b.CreateGEP(i8, expdir, ConstantInt::get(i64, 0x18), "NnSlot");
    LoadInst* numnames = b.CreateLoad(i32, nnslot, "NumNames");
    numnames->setAlignment(Align(4));
    Value* fnsrvaslot = b.CreateGEP(i8, expdir, ConstantInt::get(i64, 0x1C), "FnsRvaSlot");
    LoadInst* fnsrva = b.CreateLoad(i32, fnsrvaslot, "FnsRva");
    fnsrva->setAlignment(Align(4));
    Value* fns = b.CreateGEP(i8, base, b.CreateZExt(fnsrva, i64), "Fns");
    Value* namesrvaslot = b.CreateGEP(i8, expdir, ConstantInt::get(i64, 0x20), "NamesRvaSlot");
    LoadInst* namesrva = b.CreateLoad(i32, namesrvaslot, "NamesRva");
    namesrva->setAlignment(Align(4));
    Value* namesarr = b.CreateGEP(i8, base, b.CreateZExt(namesrva, i64), "NamesArr");
    Value* ordsrvaslot = b.CreateGEP(i8, expdir, ConstantInt::get(i64, 0x24), "OrdsRvaSlot");
    LoadInst* ordsrva = b.CreateLoad(i32, ordsrvaslot, "OrdsRva");
    ordsrva->setAlignment(Align(4));
    Value* ords = b.CreateGEP(i8, base, b.CreateZExt(ordsrva, i64), "Ords");
    b.CreateBr(exploop);

    b.SetInsertPoint(exploop);
    PHINode* iphi = b.CreatePHI(i32, 2, "I");
    iphi->addIncoming(ConstantInt::get(i32, 0), foundmod);
    Value* doneexp = b.CreateICmpUGE(iphi, numnames, "DoneExp");
    b.CreateCondBr(doneexp, notfound, checkexp);

    b.SetInsertPoint(checkexp);
    Value* namervaslot = b.CreateGEP(i32, namesarr, iphi, "NameRvaSlot");
    LoadInst* namerva = b.CreateLoad(i32, namervaslot, "NameRva");
    namerva->setAlignment(Align(4));
    Value* expname = b.CreateGEP(i8, base, b.CreateZExt(namerva, i64), "ExpName");
    Value* thisexphash = b.CreateCall(fnhashascii, { expname, salt }, "ThisExpHash");
    Value* expmatches = b.CreateICmpEQ(thisexphash, exphash, "ExpMatches");
    b.CreateCondBr(expmatches, foundexp, expnext);

    b.SetInsertPoint(expnext);
    Value* inext = b.CreateAdd(iphi, ConstantInt::get(i32, 1));
    b.CreateBr(exploop);
    iphi->addIncoming(inext, expnext);

    b.SetInsertPoint(foundexp);
    Value* ordslot = b.CreateGEP(i16, ords, iphi, "OrdSlot");
    LoadInst* ord = b.CreateLoad(i16, ordslot, "Ord");
    ord->setAlignment(Align(2));
    Value* ordi32 = b.CreateZExt(ord, i32);
    Value* funcrvaslot = b.CreateGEP(i32, fns, ordi32, "FuncRvaSlot");
    LoadInst* funcrva = b.CreateLoad(i32, funcrvaslot, "FuncRva");
    funcrva->setAlignment(Align(4));
    Value* funcptr = b.CreateGEP(i8, base, b.CreateZExt(funcrva, i64), "FuncPtr");
    Value* funci = b.CreatePtrToInt(funcptr, i64, "FuncI");
    b.CreateRet(funci);

    b.SetInsertPoint(notfound);
    b.CreateRet(ConstantInt::get(i64, 0));

    return f;
}

static Function* GetOrCreateEatLookupCachedFn(Module& m)
{
    static const char* kname = "RxEatLookupCached";
    if (Function* existing = m.getFunction(kname)) return existing;

    LLVMContext& c = m.getContext();
    IntegerType* i32 = Type::getInt32Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptr = PointerType::get(c, 0);

    Function* fnlookup = GetOrCreateEatLookupFn(m);

    FunctionType* fty = FunctionType::get(i64, { i64, i64, i32, ptr }, false);
    Function* f = Function::Create(fty, GlobalValue::InternalLinkage, kname, m);
    f->addFnAttr(Attribute::NoUnwind);
    f->addFnAttr(Attribute::AlwaysInline);
    f->setDoesNotThrow();

    Argument* mh = f->getArg(0); mh->setName("mh");
    Argument* eh = f->getArg(1); eh->setName("eh");
    Argument* salt = f->getArg(2); salt->setName("salt");
    Argument* cache = f->getArg(3); cache->setName("cache");

    BasicBlock* entry = BasicBlock::Create(c, "Entry", f);
    BasicBlock* resolve = BasicBlock::Create(c, "Resolve", f);
    BasicBlock* done = BasicBlock::Create(c, "Done", f);

    // UINT64_MAX is the sentinel for "not yet resolved" because 0 is a legitimate return from __rx_eat_lookup for the Miss case; swapping the sentinel to 0 would make every Miss site reresolve on every call and tank perf on hot code
    IRBuilder<> b(entry);
    LoadInst* cached = b.CreateLoad(i64, cache, "Cached");
    cached->setAlignment(Align(8));
    cached->setVolatile(true);
    Value* miss = b.CreateICmpEQ(cached, ConstantInt::get(i64, UINT64_MAX), "Miss");
    b.CreateCondBr(miss, resolve, done);

    b.SetInsertPoint(resolve);
    CallInst* resolved = b.CreateCall(fnlookup, { mh, eh, salt }, "Resolved");
    StoreInst* st = b.CreateStore(resolved, cache);
    st->setAlignment(Align(8));
    st->setVolatile(true);
    b.CreateBr(done);

    b.SetInsertPoint(done);
    PHINode* phi = b.CreatePHI(i64, 2, "R");
    phi->addIncoming(cached, entry);
    phi->addIncoming(resolved, resolve);
    b.CreateRet(phi);

    return f;
}

static Value* EmitEatLookupCall(IRBuilder<>& b, Module& m, const EatSiteParams& p, const Twine& name)
{
    LLVMContext& c = b.getContext();
    IntegerType* i32 = Type::getInt32Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);

    const unsigned siteid = EatLookupSiteCounter++;
    std::string cachename = "RxEatCache" + std::to_string(siteid);
    auto* cachegv = new GlobalVariable(m, i64, false, GlobalValue::InternalLinkage, ConstantInt::get(i64, UINT64_MAX), cachename);
    cachegv->setAlignment(MaybeAlign(8));

    Function* fn = GetOrCreateEatLookupCachedFn(m);
    return b.CreateCall(fn, { ConstantInt::get(i64, p.ModHash), ConstantInt::get(i64, p.ExpHash), ConstantInt::get(i32, p.Salt), cachegv }, name);
}

static Function* GetOrCreateFindModuleFn(Module& m)
{
    static const char* kname = "RxFindModule";
    if (Function* existing = m.getFunction(kname)) return existing;

    LLVMContext& c = m.getContext();
    IntegerType* i8 = Type::getInt8Ty(c);
    IntegerType* i16 = Type::getInt16Ty(c);
    IntegerType* i32 = Type::getInt32Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptr = PointerType::get(c, 0);
    PointerType* ptrgs = PointerType::get(c, 256);

    Function* fnhashwide = GetOrCreateHashWideFn(m);

    FunctionType* fty = FunctionType::get(ptr, { i64, i32 }, false);
    Function* f = Function::Create(fty, GlobalValue::InternalLinkage, kname, m);
    f->addFnAttr(Attribute::NoUnwind);
    f->addFnAttr(Attribute::AlwaysInline);
    f->setDoesNotThrow();

    Argument* modhash = f->getArg(0); modhash->setName("modhash");
    Argument* salt = f->getArg(1); salt->setName("salt");

    BasicBlock* entry = BasicBlock::Create(c, "Entry", f);
    BasicBlock* modloop = BasicBlock::Create(c, "ModLoop", f);
    BasicBlock* checkmod = BasicBlock::Create(c, "CheckMod", f);
    BasicBlock* modnext = BasicBlock::Create(c, "ModNext", f);
    BasicBlock* found = BasicBlock::Create(c, "Found", f);
    BasicBlock* notfound = BasicBlock::Create(c, "NotFound", f);

    IRBuilder<> b(entry);
    Value* gs60 = b.CreateIntToPtr(ConstantInt::get(i64, 0x60), ptrgs, "GS60");
    LoadInst* pebi = b.CreateLoad(i64, gs60, "PebI");
    pebi->setAlignment(Align(8));
    pebi->setVolatile(true);
    Value* peb = b.CreateIntToPtr(pebi, ptr, "Peb");
    Value* ldrslot = b.CreateGEP(i8, peb, ConstantInt::get(i64, 0x18), "LdrSlot");
    LoadInst* ldr = b.CreateLoad(ptr, ldrslot, "Ldr");
    ldr->setAlignment(Align(8));
    Value* head = b.CreateGEP(i8, ldr, ConstantInt::get(i64, 0x10), "Head");
    LoadInst* firstflink = b.CreateLoad(ptr, head, "FirstFlink");
    firstflink->setAlignment(Align(8));
    b.CreateBr(modloop);

    b.SetInsertPoint(modloop);
    PHINode* curentry = b.CreatePHI(ptr, 2, "CurEntry");
    curentry->addIncoming(firstflink, entry);
    Value* athead = b.CreateICmpEQ(curentry, head, "AtHead");
    b.CreateCondBr(athead, notfound, checkmod);

    b.SetInsertPoint(checkmod);
    Value* lenslot = b.CreateGEP(i8, curentry, ConstantInt::get(i64, 0x58), "LenSlot");
    LoadInst* namelenbytes = b.CreateLoad(i16, lenslot, "NameLenBytes");
    namelenbytes->setAlignment(Align(2));
    Value* bufslot = b.CreateGEP(i8, curentry, ConstantInt::get(i64, 0x60), "BufSlot");
    LoadInst* namebuf = b.CreateLoad(ptr, bufslot, "NameBuf");
    namebuf->setAlignment(Align(8));
    Value* thismodhash = b.CreateCall(fnhashwide, { namebuf, namelenbytes, salt }, "ThisModHash");
    Value* modmatches = b.CreateICmpEQ(thismodhash, modhash, "ModMatches");
    b.CreateCondBr(modmatches, found, modnext);

    b.SetInsertPoint(modnext);
    LoadInst* nextentry = b.CreateLoad(ptr, curentry, "NextEntry");
    nextentry->setAlignment(Align(8));
    b.CreateBr(modloop);
    curentry->addIncoming(nextentry, modnext);

    b.SetInsertPoint(found);
    Value* baseslot = b.CreateGEP(i8, curentry, ConstantInt::get(i64, 0x30), "BaseSlot");
    LoadInst* basei = b.CreateLoad(i64, baseslot, "BaseI");
    basei->setAlignment(Align(8));
    Value* base = b.CreateIntToPtr(basei, ptr, "Base");
    b.CreateRet(base);

    b.SetInsertPoint(notfound);
    b.CreateRet(ConstantPointerNull::get(ptr));

    return f;
}

static Function* GetOrCreateEatScanSumFn(Module& m)
{
    static const char* kname = "RxEatScanSum";
    if (Function* existing = m.getFunction(kname)) return existing;

    LLVMContext& c = m.getContext();
    IntegerType* i8 = Type::getInt8Ty(c);
    IntegerType* i16 = Type::getInt16Ty(c);
    IntegerType* i32 = Type::getInt32Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptr = PointerType::get(c, 0);

    Function* fnhashascii = GetOrCreateHashAsciiFn(m);

    StructType* slotty = StructType::get(c, { i64, i64 });

    FunctionType* fty = FunctionType::get(i64, { ptr, ptr, i32, i32 }, false);
    Function* f = Function::Create(fty, GlobalValue::InternalLinkage, kname, m);
    f->addFnAttr(Attribute::NoUnwind);
    f->addFnAttr(Attribute::AlwaysInline);
    f->setDoesNotThrow();

    Argument* base = f->getArg(0); base->setName("base");
    Argument* slots = f->getArg(1); slots->setName("slots");
    Argument* count = f->getArg(2); count->setName("count");
    Argument* salt = f->getArg(3); salt->setName("salt");

    BasicBlock* entry = BasicBlock::Create(c, "Entry", f);
    BasicBlock* exploop = BasicBlock::Create(c, "ExpLoop", f);
    BasicBlock* checkexp = BasicBlock::Create(c, "CheckExp", f);
    BasicBlock* probeloop = BasicBlock::Create(c, "ProbeLoop", f);
    BasicBlock* probechk = BasicBlock::Create(c, "ProbeCheck", f);
    BasicBlock* matched = BasicBlock::Create(c, "Matched", f);
    BasicBlock* probenext = BasicBlock::Create(c, "ProbeNext", f);
    BasicBlock* expnext = BasicBlock::Create(c, "ExpNext", f);
    BasicBlock* done = BasicBlock::Create(c, "Done", f);

    IRBuilder<> b(entry);
    Value* elfanewslot = b.CreateGEP(i8, base, ConstantInt::get(i64, 0x3C), "ElfanewSlot");
    LoadInst* elfanew = b.CreateLoad(i32, elfanewslot, "Elfanew");
    elfanew->setAlignment(Align(4));
    Value* nt = b.CreateGEP(i8, base, b.CreateSExt(elfanew, i64), "Nt");
    Value* exprvaslot = b.CreateGEP(i8, nt, ConstantInt::get(i64, 0x88), "ExpRvaSlot");
    LoadInst* exprva = b.CreateLoad(i32, exprvaslot, "ExpRva");
    exprva->setAlignment(Align(4));
    Value* expdir = b.CreateGEP(i8, base, b.CreateZExt(exprva, i64), "ExpDir");
    Value* nnslot = b.CreateGEP(i8, expdir, ConstantInt::get(i64, 0x18), "NnSlot");
    LoadInst* numnames = b.CreateLoad(i32, nnslot, "NumNames");
    numnames->setAlignment(Align(4));
    Value* namesrvaslot = b.CreateGEP(i8, expdir, ConstantInt::get(i64, 0x20), "NamesRvaSlot");
    LoadInst* namesrva = b.CreateLoad(i32, namesrvaslot, "NamesRva");
    namesrva->setAlignment(Align(4));
    Value* namesarr = b.CreateGEP(i8, base, b.CreateZExt(namesrva, i64), "NamesArr");
    b.CreateBr(exploop);

    b.SetInsertPoint(exploop);
    PHINode* iphi = b.CreatePHI(i32, 2, "I");
    PHINode* accum = b.CreatePHI(i64, 2, "Accum");
    iphi->addIncoming(ConstantInt::get(i32, 0), entry);
    accum->addIncoming(ConstantInt::get(i64, 0), entry);
    Value* atend = b.CreateICmpUGE(iphi, numnames, "AtEnd");
    b.CreateCondBr(atend, done, checkexp);

    b.SetInsertPoint(checkexp);
    Value* namervaslot = b.CreateGEP(i32, namesarr, iphi, "NameRvaSlot");
    LoadInst* namerva = b.CreateLoad(i32, namervaslot, "NameRva");
    namerva->setAlignment(Align(4));
    Value* expname = b.CreateGEP(i8, base, b.CreateZExt(namerva, i64), "ExpName");
    Value* h = b.CreateCall(fnhashascii, { expname, salt }, "H");
    b.CreateBr(probeloop);

    b.SetInsertPoint(probeloop);
    PHINode* jphi = b.CreatePHI(i32, 2, "J");
    jphi->addIncoming(ConstantInt::get(i32, 0), checkexp);
    Value* probedone = b.CreateICmpUGE(jphi, count, "ProbeDone");
    b.CreateCondBr(probedone, expnext, probechk);

    b.SetInsertPoint(probechk);
    Value* slothashslot = b.CreateGEP(slotty, slots, { jphi, ConstantInt::get(i32, 0) }, "SlotHashSlot");
    LoadInst* slothash = b.CreateLoad(i64, slothashslot, "SlotHash");
    slothash->setAlignment(Align(8));
    Value* match = b.CreateICmpEQ(slothash, h, "Match");
    b.CreateCondBr(match, matched, probenext);

    b.SetInsertPoint(matched);
    Value* slotvalslot = b.CreateGEP(slotty, slots, { jphi, ConstantInt::get(i32, 1) }, "SlotValSlot");
    LoadInst* slotval = b.CreateLoad(i64, slotvalslot, "SlotVal");
    slotval->setAlignment(Align(8));
    Value* accumhit = b.CreateAdd(accum, slotval, "AccumHit");
    b.CreateBr(expnext);

    b.SetInsertPoint(probenext);
    Value* jnext = b.CreateAdd(jphi, ConstantInt::get(i32, 1), "JNext");
    b.CreateBr(probeloop);
    jphi->addIncoming(jnext, probenext);

    b.SetInsertPoint(expnext);
    PHINode* accummerge = b.CreatePHI(i64, 2, "AccumMerge");
    accummerge->addIncoming(accum, probeloop);
    accummerge->addIncoming(accumhit, matched);
    Value* inext = b.CreateAdd(iphi, ConstantInt::get(i32, 1), "INext");
    b.CreateBr(exploop);
    iphi->addIncoming(inext, expnext);
    accum->addIncoming(accummerge, expnext);

    b.SetInsertPoint(done);
    b.CreateRet(accum);

    return f;
}

static Function* GetOrCreateHeapAccumulateFn(Module& m)
{
    static const char* kname = "RxHeapAccumulate";
    if (Function* existing = m.getFunction(kname)) return existing;

    LLVMContext& c = m.getContext();
    IntegerType* i8 = Type::getInt8Ty(c);
    IntegerType* i32 = Type::getInt32Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptr = PointerType::get(c, 0);
    PointerType* ptrgs = PointerType::get(c, 256);

    Function* fnhashascii = GetOrCreateHashAsciiFn(m);
    Function* fneatscan = GetOrCreateEatScanSumFn(m);

    StructType* slotty = StructType::get(c, { i64, i64 });

    FunctionType* fty = FunctionType::get(i64, { ptr, ptr, i32, i32, i64, i64, i32 }, false);
    Function* f = Function::Create(fty, GlobalValue::InternalLinkage, kname, m);
    f->addFnAttr(Attribute::NoUnwind);
    f->addFnAttr(Attribute::AlwaysInline);
    f->setDoesNotThrow();

    Argument* base = f->getArg(0); base->setName("base");
    Argument* slots = f->getArg(1); slots->setName("slots");
    Argument* count = f->getArg(2); count->setName("count");
    Argument* bufsize = f->getArg(3); bufsize->setName("bufsize");
    Argument* allocfni = f->getArg(4); allocfni->setName("allocfni");
    Argument* freefni = f->getArg(5); freefni->setName("freefni");
    Argument* salt = f->getArg(6); salt->setName("salt");

    BasicBlock* entry = BasicBlock::Create(c, "Entry", f);
    BasicBlock* doalloc = BasicBlock::Create(c, "DoAlloc", f);
    BasicBlock* allocchk = BasicBlock::Create(c, "AllocCheck", f);
    BasicBlock* parsehdr = BasicBlock::Create(c, "ParseHdr", f);
    BasicBlock* exploop = BasicBlock::Create(c, "ExpLoop", f);
    BasicBlock* checkexp = BasicBlock::Create(c, "CheckExp", f);
    BasicBlock* probeloop = BasicBlock::Create(c, "ProbeLoop", f);
    BasicBlock* probechk = BasicBlock::Create(c, "ProbeCheck", f);
    BasicBlock* probehit = BasicBlock::Create(c, "ProbeHit", f);
    BasicBlock* probenext = BasicBlock::Create(c, "ProbeNext", f);
    BasicBlock* expnext = BasicBlock::Create(c, "ExpNext", f);
    BasicBlock* sumloop = BasicBlock::Create(c, "SumLoop", f);
    BasicBlock* sumbody = BasicBlock::Create(c, "SumBody", f);
    BasicBlock* dofree = BasicBlock::Create(c, "DoFree", f);
    BasicBlock* dofreecall = BasicBlock::Create(c, "DoFreeCall", f);
    BasicBlock* fallback = BasicBlock::Create(c, "Fallback", f);
    BasicBlock* done = BasicBlock::Create(c, "Done", f);

    IRBuilder<> b(entry);
    Value* allocisnull = b.CreateICmpEQ(allocfni, ConstantInt::get(i64, 0), "AllocIsNull");
    b.CreateCondBr(allocisnull, fallback, doalloc);

    b.SetInsertPoint(doalloc);
    Value* gs60 = b.CreateIntToPtr(ConstantInt::get(i64, 0x60), ptrgs, "GS60");
    LoadInst* pebi = b.CreateLoad(i64, gs60, "PebI");
    pebi->setAlignment(Align(8));
    pebi->setVolatile(true);
    Value* peb = b.CreateIntToPtr(pebi, ptr, "Peb");
    Value* heapslot = b.CreateGEP(i8, peb, ConstantInt::get(i64, 0x30), "HeapSlot");
    LoadInst* heap = b.CreateLoad(ptr, heapslot, "Heap");
    heap->setAlignment(Align(8));

    Value* allocfn = b.CreateIntToPtr(allocfni, ptr, "AllocFn");
    FunctionType* allocfty = FunctionType::get(ptr, { ptr, i32, i64 }, false);
    Value* bufsize64 = b.CreateZExt(bufsize, i64, "Bufsize64");
    CallInst* buffer = b.CreateCall(allocfty, allocfn, { heap, ConstantInt::get(i32, 0x8), bufsize64 }, "Buffer");
    b.CreateBr(allocchk);

    b.SetInsertPoint(allocchk);
    Value* bufisnull = b.CreateICmpEQ(buffer, ConstantPointerNull::get(ptr), "BufIsNull");
    b.CreateCondBr(bufisnull, fallback, parsehdr);

    IRBuilder<> ph(parsehdr);
    Value* elfanewslot = ph.CreateGEP(i8, base, ConstantInt::get(i64, 0x3C), "ElfanewSlot");
    LoadInst* elfanew = ph.CreateLoad(i32, elfanewslot, "Elfanew");
    elfanew->setAlignment(Align(4));
    Value* nt = ph.CreateGEP(i8, base, ph.CreateSExt(elfanew, i64), "Nt");
    Value* exprvaslot = ph.CreateGEP(i8, nt, ConstantInt::get(i64, 0x88), "ExpRvaSlot");
    LoadInst* exprva = ph.CreateLoad(i32, exprvaslot, "ExpRva");
    exprva->setAlignment(Align(4));
    Value* expdir = ph.CreateGEP(i8, base, ph.CreateZExt(exprva, i64), "ExpDir");
    Value* nnslot = ph.CreateGEP(i8, expdir, ConstantInt::get(i64, 0x18), "NnSlot");
    LoadInst* numnames = ph.CreateLoad(i32, nnslot, "NumNames");
    numnames->setAlignment(Align(4));
    Value* namesrvaslot = ph.CreateGEP(i8, expdir, ConstantInt::get(i64, 0x20), "NamesRvaSlot");
    LoadInst* namesrva = ph.CreateLoad(i32, namesrvaslot, "NamesRva");
    namesrva->setAlignment(Align(4));
    Value* namesarr = ph.CreateGEP(i8, base, ph.CreateZExt(namesrva, i64), "NamesArr");
    ph.CreateBr(exploop);

    IRBuilder<> xb(exploop);
    PHINode* iphi = xb.CreatePHI(i32, 2, "I");
    iphi->addIncoming(ConstantInt::get(i32, 0), parsehdr);
    Value* atend = xb.CreateICmpUGE(iphi, numnames, "AtEnd");
    xb.CreateCondBr(atend, sumloop, checkexp);

    IRBuilder<> cxb(checkexp);
    Value* namervaslot = cxb.CreateGEP(i32, namesarr, iphi, "NameRvaSlot");
    LoadInst* namerva = cxb.CreateLoad(i32, namervaslot, "NameRva");
    namerva->setAlignment(Align(4));
    Value* expname = cxb.CreateGEP(i8, base, cxb.CreateZExt(namerva, i64), "ExpName");
    Value* h = cxb.CreateCall(fnhashascii, { expname, salt }, "H");
    cxb.CreateBr(probeloop);

    IRBuilder<> pb(probeloop);
    PHINode* jphi = pb.CreatePHI(i32, 2, "J");
    jphi->addIncoming(ConstantInt::get(i32, 0), checkexp);
    Value* probedone = pb.CreateICmpUGE(jphi, count, "ProbeDone");
    pb.CreateCondBr(probedone, expnext, probechk);

    IRBuilder<> pcb(probechk);
    Value* slothashslot = pcb.CreateGEP(slotty, slots, { jphi, ConstantInt::get(i32, 0) }, "SlotHashSlot");
    LoadInst* slothash = pcb.CreateLoad(i64, slothashslot, "SlotHash");
    slothash->setAlignment(Align(8));
    Value* match = pcb.CreateICmpEQ(slothash, h, "Match");
    pcb.CreateCondBr(match, probehit, probenext);

    IRBuilder<> phb(probehit);
    Value* slotvalslot = phb.CreateGEP(slotty, slots, { jphi, ConstantInt::get(i32, 1) }, "SlotValSlot");
    LoadInst* slotval = phb.CreateLoad(i64, slotvalslot, "SlotVal");
    slotval->setAlignment(Align(8));
    Value* bufslotptr = phb.CreateGEP(i64, buffer, jphi, "BufSlotPtr");
    StoreInst* bufstore = phb.CreateStore(slotval, bufslotptr);
    bufstore->setAlignment(Align(8));
    phb.CreateBr(expnext);

    IRBuilder<> pnb(probenext);
    Value* jnext = pnb.CreateAdd(jphi, ConstantInt::get(i32, 1), "JNext");
    pnb.CreateBr(probeloop);
    jphi->addIncoming(jnext, probenext);

    IRBuilder<> enb(expnext);
    Value* inext = enb.CreateAdd(iphi, ConstantInt::get(i32, 1), "INext");
    enb.CreateBr(exploop);
    iphi->addIncoming(inext, expnext);

    IRBuilder<> sb(sumloop);
    PHINode* kphi = sb.CreatePHI(i32, 2, "K");
    PHINode* acc = sb.CreatePHI(i64, 2, "Acc");
    kphi->addIncoming(ConstantInt::get(i32, 0), exploop);
    acc->addIncoming(ConstantInt::get(i64, 0), exploop);
    Value* sumdone = sb.CreateICmpUGE(kphi, count, "SumDone");
    sb.CreateCondBr(sumdone, dofree, sumbody);

    IRBuilder<> sbb(sumbody);
    Value* bufkptr = sbb.CreateGEP(i64, buffer, kphi, "BufKPtr");
    LoadInst* bufk = sbb.CreateLoad(i64, bufkptr, "BufK");
    bufk->setAlignment(Align(8));
    Value* accnext = sbb.CreateAdd(acc, bufk, "AccNext");
    Value* knext = sbb.CreateAdd(kphi, ConstantInt::get(i32, 1), "KNext");
    sbb.CreateBr(sumloop);
    kphi->addIncoming(knext, sumbody);
    acc->addIncoming(accnext, sumbody);

    // on a NULL free pointer the buffer is intentionally leaked rather than crashed on; the per site cache_gv means this is a one shot per site, so the leak is bounded at count*8 bytes per site over the process lifetime; crashing instead would turn an attacker emulator missing FreeHeap into a visible failure
    IRBuilder<> fb(dofree);
    Value* freeisnull = fb.CreateICmpEQ(freefni, ConstantInt::get(i64, 0), "FreeIsNull");
    fb.CreateCondBr(freeisnull, done, dofreecall);
    IRBuilder<> fcb(dofreecall);
    Value* freefn = fcb.CreateIntToPtr(freefni, ptr, "FreeFn");
    FunctionType* freefty = FunctionType::get(i32, { ptr, i32, ptr }, false);
    fcb.CreateCall(freefty, freefn, { heap, ConstantInt::get(i32, 0), buffer });
    fcb.CreateBr(done);

    IRBuilder<> fab(fallback);
    Value* regsum = fab.CreateCall(fneatscan, { base, slots, count, salt }, "FbSum");
    fab.CreateBr(done);

    IRBuilder<> db(done);
    PHINode* result = db.CreatePHI(i64, 3, "Result");
    result->addIncoming(acc, dofree);
    result->addIncoming(acc, dofreecall);
    result->addIncoming(regsum, fallback);
    db.CreateRet(result);

    return f;
}

static Value* EmitSourceValue(IRBuilder<>& b, Module& m, SourceKind kind, unsigned modindex, const EatSiteParams& eat)
{
    switch (kind)
    {
        case SourceKind::PebWalkModule: return EmitModuleDllBase(b, modindex);
        case SourceKind::PebImageBase: return EmitPebImageBase(b);
        case SourceKind::PebDirect: return EmitPebDirect(b);
        case SourceKind::TebDirect: return EmitTebDirect(b);
        case SourceKind::TebStackBase: return EmitTebStackBase(b);
        case SourceKind::TebStackLimit: return EmitTebStackLimit(b);
        case SourceKind::ProcessHeap: return EmitProcessHeap(b);
        case SourceKind::EatHashHit: return EmitEatLookupCall(b, m, eat, "RelocopEatHit");
        case SourceKind::EatHashMiss: return EmitEatLookupCall(b, m, eat, "RelocopEatMiss");
        case SourceKind::Count: break;
    }
    llvm_unreachable("invalid SourceKind");
}

// both GS loads at the start MUST stay volatile so LLVM can't CSE them into one; the point is a decompile with two separately sourced values whose equality is not obviously provable without Win x64-specific ABI knowledge; a CSE collapse reduces the compare to a tautology the folder can see
static Value* EmitTebSelfRefCheck(IRBuilder<>& b)
{
    LLVMContext& c = b.getContext();
    IntegerType* i8 = Type::getInt8Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptr = PointerType::get(c, 0);
    PointerType* ptrgs = PointerType::get(c, 256);

    Value* gs30a = b.CreateIntToPtr(ConstantInt::get(i64, 0x30), ptrgs, "RelocopSrTGS30A");
    LoadInst* teba = b.CreateLoad(i64, gs30a, "RelocopSrTA");
    teba->setAlignment(Align(8));
    teba->setVolatile(true);

    Value* gs30b = b.CreateIntToPtr(ConstantInt::get(i64, 0x30), ptrgs, "RelocopSrTGS30B");
    LoadInst* tebbint = b.CreateLoad(i64, gs30b, "RelocopSrTBTeb");
    tebbint->setAlignment(Align(8));
    tebbint->setVolatile(true);
    Value* tebb = b.CreateIntToPtr(tebbint, ptr, "RelocopSrTBTebP");
    Value* selfslot = b.CreateGEP(i8, tebb, ConstantInt::get(i64, 0x30), "RelocopSrTBSlot");
    LoadInst* selfval = b.CreateLoad(i64, selfslot, "RelocopSrTB");
    selfval->setAlignment(Align(8));

    return b.CreateICmpEQ(teba, selfval, "RelocopSrTCmp");
}

static Value* EmitPebSelfRefCheck(IRBuilder<>& b)
{
    LLVMContext& c = b.getContext();
    IntegerType* i8 = Type::getInt8Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptr = PointerType::get(c, 0);
    PointerType* ptrgs = PointerType::get(c, 256);

    Value* gs60a = b.CreateIntToPtr(ConstantInt::get(i64, 0x60), ptrgs, "RelocopSrPGS60");
    LoadInst* peba = b.CreateLoad(i64, gs60a, "RelocopSrPA");
    peba->setAlignment(Align(8));
    peba->setVolatile(true);

    Value* gs30b = b.CreateIntToPtr(ConstantInt::get(i64, 0x30), ptrgs, "RelocopSrPGS30");
    LoadInst* tebbint = b.CreateLoad(i64, gs30b, "RelocopSrPBTeb");
    tebbint->setAlignment(Align(8));
    tebbint->setVolatile(true);
    Value* tebb = b.CreateIntToPtr(tebbint, ptr, "RelocopSrPBTebP");
    Value* pebslot = b.CreateGEP(i8, tebb, ConstantInt::get(i64, 0x60), "RelocopSrPBSlot");
    LoadInst* pebb = b.CreateLoad(i64, pebslot, "RelocopSrPB");
    pebb->setAlignment(Align(8));

    return b.CreateICmpEQ(peba, pebb, "RelocopSrPCmp");
}

static Value* EmitPebNeTebCheck(IRBuilder<>& b)
{
    LLVMContext& c = b.getContext();
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptrgs = PointerType::get(c, 256);

    Value* gs60 = b.CreateIntToPtr(ConstantInt::get(i64, 0x60), ptrgs, "RelocopNePtGS60");
    LoadInst* peb = b.CreateLoad(i64, gs60, "RelocopNePtPeb");
    peb->setAlignment(Align(8));
    peb->setVolatile(true);

    Value* gs30 = b.CreateIntToPtr(ConstantInt::get(i64, 0x30), ptrgs, "RelocopNePtGS30");
    LoadInst* teb = b.CreateLoad(i64, gs30, "RelocopNePtTeb");
    teb->setAlignment(Align(8));
    teb->setVolatile(true);

    return b.CreateICmpEQ(peb, teb, "RelocopNePtCmp");
}

static Value* EmitPebNeImgBaseCheck(IRBuilder<>& b)
{
    LLVMContext& c = b.getContext();
    IntegerType* i8 = Type::getInt8Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptr = PointerType::get(c, 0);
    PointerType* ptrgs = PointerType::get(c, 256);

    Value* gs60a = b.CreateIntToPtr(ConstantInt::get(i64, 0x60), ptrgs, "RelocopNePiGS60A");
    LoadInst* peba = b.CreateLoad(i64, gs60a, "RelocopNePiA");
    peba->setAlignment(Align(8));
    peba->setVolatile(true);

    Value* gs60b = b.CreateIntToPtr(ConstantInt::get(i64, 0x60), ptrgs, "RelocopNePiGS60B");
    LoadInst* pebbint = b.CreateLoad(i64, gs60b, "RelocopNePiBPeb");
    pebbint->setAlignment(Align(8));
    pebbint->setVolatile(true);
    Value* pebb = b.CreateIntToPtr(pebbint, ptr, "RelocopNePiBPebP");
    Value* ibslot = b.CreateGEP(i8, pebb, ConstantInt::get(i64, 0x10), "RelocopNePiBSlot");
    LoadInst* ib = b.CreateLoad(i64, ibslot, "RelocopNePiB");
    ib->setAlignment(Align(8));

    return b.CreateICmpEQ(peba, ib, "RelocopNePiCmp");
}

enum class ArxKind : uint8_t { Add, Xor, XorInput, Rol };

struct ArxStep
{
    ArxKind Kind;
    uint32_t K;
};

static uint32_t ArxEvalU32(uint32_t seed, uint32_t input, const std::vector<ArxStep>& chain)
{
    uint32_t v = seed;
    for (const auto& st : chain)
    {
        switch (st.Kind)
        {
            case ArxKind::Add: v = v + st.K; break;
            case ArxKind::Xor: v = v ^ st.K; break;
            case ArxKind::XorInput: v = v ^ input; break;
            case ArxKind::Rol:
            {
                const unsigned r = st.K & 31u;
                v = (r == 0) ? v : ((v << r) | (v >> (32u - r)));
                break;
            }
        }
    }
    return v;
}

static std::vector<ArxStep> GenerateArxChain()
{
    const unsigned steps = ArxMinSteps + (unsigned)(Rng() % (ArxMaxSteps - ArxMinSteps + 1));
    std::vector<ArxStep> chain;
    chain.reserve(steps);
    bool hasinput = false;
    // at least one XorInput MUST land somewhere in the chain so int1 actually mixes into the state; without it the chain is pure (seed, const)-driven and LLVM's optimizer folds the whole thing to a compile-time constant that cancels the opaque; force the last step to XorInput if none has fired by then
    for (unsigned i = 0; i < steps; ++i)
    {
        unsigned sel = (unsigned)(Rng() % 4u);
        if (i == steps - 1 && !hasinput) sel = 2;
        ArxStep st{};
        switch (sel)
        {
            case 0:
                st.Kind = ArxKind::Add;
                st.K = (uint32_t)Rng();
                break;
            case 1:
                st.Kind = ArxKind::Xor;
                st.K = (uint32_t)Rng();
                break;
            case 2:
                st.Kind = ArxKind::XorInput;
                st.K = 0;
                hasinput = true;
                break;
            default:
                st.Kind = ArxKind::Rol;
                st.K = 1u + (uint32_t)(Rng() % 31u);
                break;
        }
        chain.push_back(st);
    }
    return chain;
}

static Value* EmitArxChain(IRBuilder<>& b, Value* input32, uint32_t seed, const std::vector<ArxStep>& chain)
{
    LLVMContext& c = b.getContext();
    IntegerType* i32 = Type::getInt32Ty(c);

    Value* v = ConstantInt::get(i32, seed);
    for (const auto& st : chain)
    {
        switch (st.Kind)
        {
            case ArxKind::Add:
                v = b.CreateAdd(v, ConstantInt::get(i32, st.K), "RelocopArxAdd");
                break;
            case ArxKind::Xor:
                v = b.CreateXor(v, ConstantInt::get(i32, st.K), "RelocopArxXor");
                break;
            case ArxKind::XorInput:
                v = b.CreateXor(v, input32, "RelocopArxXorInput");
                break;
            case ArxKind::Rol:
            {
                const unsigned r = st.K & 31u;
                Value* left = b.CreateShl(v, ConstantInt::get(i32, r), "RelocopArxRotL");
                Value* right = b.CreateLShr(v, ConstantInt::get(i32, 32u - r), "RelocopArxRotR");
                v = b.CreateOr(left, right, "RelocopArxRotOr");
                break;
            }
        }
    }
    return v;
}

struct PolluteSlot
{
    AllocaInst* Base;
    IntegerType* IntTy;
};

struct SlotPool
{
    SmallVector<PolluteSlot, 16> Slots32;
    SmallVector<PolluteSlot, 16> Slots64;
};

static Value* EmitSlotLoad(IRBuilder<>& b, const PolluteSlot& s)
{
    LoadInst* ld = b.CreateLoad(s.IntTy, s.Base, "RelocopPolluteLoad");
    ld->setAlignment(Align(1));
    return ld;
}

static void EmitSlotStore(IRBuilder<>& b, const PolluteSlot& s, Value* intval, bool volatilestore)
{
    StoreInst* st = b.CreateStore(intval, s.Base);
    st->setAlignment(Align(1));
    if (volatilestore) st->setVolatile(true);
}

static void CollectExistingSlots(Function& f, SlotPool& out)
{
    LLVMContext& c = f.getContext();
    IntegerType* i32 = Type::getInt32Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    const DataLayout& dl = f.getParent()->getDataLayout();

    for (Instruction& i : f.getEntryBlock())
    {
        auto* a = dyn_cast<AllocaInst>(&i);
        if (!a || !a->isStaticAlloca()) continue;
        if (a->getName().starts_with("Relocop")) continue;

        const uint64_t size = dl.getTypeAllocSize(a->getAllocatedType());
        if (size >= 8) out.Slots64.push_back({ a, i64 });
        else if (size >= 4) out.Slots32.push_back({ a, i32 });
    }
}

static AllocaInst* GetOrCreateScratchAlloca(Function& f)
{
    if (PerFuncScratchAlloca) return PerFuncScratchAlloca;
    LLVMContext& c = f.getContext();
    IRBuilder<> eb(&*f.getEntryBlock().getFirstInsertionPt());
    PerFuncScratchAlloca = eb.CreateAlloca(Type::getInt64Ty(c), nullptr, "RelocopScratch");
    PerFuncScratchAlloca->setAlignment(Align(8));
    return PerFuncScratchAlloca;
}

static void FillPolluteBlock(Function& f, BasicBlock* pollutebb, BasicBlock* realbb)
{
    LLVMContext& c = f.getContext();
    IntegerType* i32 = Type::getInt32Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);

    SlotPool pool;
    CollectExistingSlots(f, pool);

    IRBuilder<> pb(pollutebb);

    bool have32 = !pool.Slots32.empty();
    bool have64 = !pool.Slots64.empty();

    if (!have32 && !have64)
    {
        AllocaInst* scratch = GetOrCreateScratchAlloca(f);
        pool.Slots64.push_back({ scratch, i64 });
        have64 = true;
    }

    const unsigned opcount = PolluteOpsMin + (unsigned)(Rng() % (PolluteOpsMax - PolluteOpsMin + 1));

    auto pickslot = [&](IntegerType* ity) -> const PolluteSlot&
    {
        auto& slots = (ity == i64) ? pool.Slots64 : pool.Slots32;
        return slots[Rng() % slots.size()];
    };

    IntegerType* accty;
    if (have32 && have64) accty = (Rng() & 1) ? i64 : i32;
    else if (have64) accty = i64;
    else accty = i32;

    Value* acc = EmitSlotLoad(pb, pickslot(accty));

    for (unsigned n = 0; n < opcount; ++n)
    {
        const uint64_t mask = (accty == i64) ? ~uint64_t(0) : 0xFFFFFFFFu;
        const uint64_t k = ((uint64_t)Rng()) & mask;
        switch (Rng() % 6)
        {
            case 0: acc = pb.CreateAdd(acc, ConstantInt::get(accty, k), "RelocopPolluteAdd"); break;
            case 1: acc = pb.CreateXor(acc, ConstantInt::get(accty, k), "RelocopPolluteXor"); break;
            case 2: acc = pb.CreateSub(acc, ConstantInt::get(accty, k), "RelocopPolluteSub"); break;
            case 3: acc = pb.CreateOr(acc, ConstantInt::get(accty, k), "RelocopPolluteOr"); break;
            case 4: acc = pb.CreateAnd(acc, ConstantInt::get(accty, k), "RelocopPolluteAnd"); break;
            default:
            {
                const unsigned w = accty->getBitWidth();
                const unsigned shamt = 1u + (unsigned)(Rng() % (w - 1u));
                acc = pb.CreateShl(acc, ConstantInt::get(accty, shamt), "RelocopPolluteShl");
                break;
            }
        }

        if ((Rng() % 100u) < CorruptionSpillPctPerOp) EmitSlotStore(pb, pickslot(accty), acc, false);
    }

    EmitSlotStore(pb, pickslot(accty), acc, true);

    pb.CreateBr(realbb);
}

static unsigned StealIntoHead(BasicBlock* headbb, BasicBlock* realbb, unsigned maxsteal)
{
    unsigned stolen = 0;
    while (stolen < maxsteal)
    {
        Instruction* first = realbb->getFirstNonPHIOrDbgOrLifetime();
        if (!first || first->isTerminator()) break;

        if (isa<CallBase>(first)) break;
        if (isa<AllocaInst>(first)) break;
        if (isa<LandingPadInst>(first)) break;
        if (isa<CatchPadInst>(first)) break;
        if (isa<CleanupPadInst>(first)) break;
        if (first->isAtomic()) break;
        if (isa<FenceInst>(first)) break;
        if (first->mayHaveSideEffects()) break;

        // the operand check must STOP the chain the first time a candidate depends on something still later in realbb; moving such an instruction would hoist a use above its def and the verifier catches it
        bool opsok = true;
        for (Use& op : first->operands())
        {
            Value* v = op.get();
            if (auto* oi = dyn_cast<Instruction>(v))
            {
                if (oi->getParent() == realbb) { opsok = false; break; }
            }
        }
        if (!opsok) break;

        first->removeFromParent();
        first->insertInto(headbb, headbb->end());
        ++stolen;
    }
    return stolen;
}

struct ScanSlot
{
    uint64_t Hash;
    uint64_t Value;
    bool IsReal;
};

struct ScanSitePlan
{
    uint64_t ModHash = 0;
    uint32_t Salt = 0;
    SmallVector<ScanSlot, 16> Slots;
    uint64_t ExpectedSum = 0;
    SmallVector<uint64_t, 8> DeadSums;
};

static ScanSitePlan BuildScanSitePlan()
{
    ScanSitePlan plan;
    plan.Salt = (uint32_t)Rng();

    const std::string& dll = WhitelistDlls[Rng() % WhitelistDlls.size()];
    plan.ModHash = Fnv1aUtf16LowerAscii(dll.c_str(), plan.Salt);

    SmallVector<std::string, 32> dllexports;
    for (const auto& b : WhitelistExports)
    {
        if (b.Dll == dll) dllexports.push_back(b.Exp);
    }

    for (size_t i = dllexports.size(); i > 1; --i) std::swap(dllexports[i - 1], dllexports[Rng() % i]);
    const unsigned nrealdesired = MinScanRealSlots + (unsigned)(Rng() % (MaxScanRealSlots - MinScanRealSlots + 1));
    const unsigned nreal = std::min((unsigned)dllexports.size(), nrealdesired);

    SmallVector<uint64_t, 8> realvalues;
    for (unsigned i = 0; i < nreal; ++i)
    {
        ScanSlot s;
        s.Hash = Fnv1aAscii(dllexports[i].c_str(), plan.Salt);
        do { s.Value = (uint64_t)Rng(); } while (s.Value == 0);
        s.IsReal = true;
        plan.Slots.push_back(s);
        realvalues.push_back(s.Value);
        plan.ExpectedSum += s.Value;
    }

    const unsigned nfake = MinScanFakeSlots + (unsigned)(Rng() % (MaxScanFakeSlots - MinScanFakeSlots + 1));
    for (unsigned i = 0; i < nfake; ++i)
    {
        ScanSlot s;
        s.Hash = (uint64_t)Rng();
        s.Value = (uint64_t)Rng();
        s.IsReal = false;
        plan.Slots.push_back(s);
    }

    // real and fake slots MUST be shuffled together so an analyst can't visually distinguish real slots (early in table) from fake (later); ordered tables make the real/fake boundary trivial to spot in the decompile
    for (size_t i = plan.Slots.size(); i > 1; --i) std::swap(plan.Slots[i - 1], plan.Slots[Rng() % i]);

    const unsigned ndeaddesired = MinScanDeadSums + (unsigned)(Rng() % (MaxScanDeadSums - MinScanDeadSums + 1));
    const unsigned maxsubsets = (nreal >= 32) ? (unsigned)-1 : (1u << nreal) - 1u;
    const unsigned ndead = std::min(ndeaddesired, maxsubsets);

    std::set<uint64_t> used{ plan.ExpectedSum };
    unsigned attempts = 0;
    while (plan.DeadSums.size() < ndead && attempts < 200)
    {
        ++attempts;
        const unsigned mask = (unsigned)(Rng() % maxsubsets);
        uint64_t s = 0;
        for (unsigned i = 0; i < nreal; ++i)
        {
            if (mask & (1u << i)) s += realvalues[i];
        }
        if (used.insert(s).second) plan.DeadSums.push_back(s);
    }

    return plan;
}

// StealIntoHead MUST run BEFORE head_bb gets its terminator because it appends at head_bb's end; appending after a terminator leaves the terminator mid block, getTerminator() returns null and the verifier screams "does not have terminator!"
static void EmitDispatchScanBody(Function& f, BasicBlock* headbb, BasicBlock* realbb, BasicBlock* defaultpollutebb)
{
    Module& m = *f.getParent();
    LLVMContext& c = f.getContext();
    IntegerType* i32 = Type::getInt32Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    PointerType* ptr = PointerType::get(c, 0);
    StructType* slotty = StructType::get(c, { i64, i64 });

    ScanSitePlan plan = BuildScanSitePlan();

    const unsigned siteid = DispatchScanSiteCounter++;
    std::string slotsname = "RxScanSlots" + std::to_string(siteid);
    std::string cachename = "RxScanCache" + std::to_string(siteid);

    ArrayType* tablety = ArrayType::get(slotty, plan.Slots.size());
    SmallVector<Constant*, 16> slotconsts;
    for (const ScanSlot& s : plan.Slots)
    {
        slotconsts.push_back(ConstantStruct::get(slotty, { ConstantInt::get(i64, s.Hash), ConstantInt::get(i64, s.Value) }));
    }
    Constant* init = ConstantArray::get(tablety, slotconsts);
    auto* slotsgv = new GlobalVariable(m, tablety, true, GlobalValue::InternalLinkage, init, slotsname);
    slotsgv->setAlignment(MaybeAlign(8));

    auto* cachegv = new GlobalVariable(m, i64, false, GlobalValue::InternalLinkage, ConstantInt::get(i64, 0), cachename);
    cachegv->setAlignment(MaybeAlign(8));

    BasicBlock* doscanbb = BasicBlock::Create(c, "DSScan", &f, realbb);
    BasicBlock* dispatchbb = BasicBlock::Create(c, "DSDisp", &f, realbb);

    unsigned stealcap = 0;
    {
        const unsigned rbsize = (unsigned)realbb->size();
        if (rbsize > StealMinRealResidue + 1)
        {
            const unsigned headroom = rbsize - (StealMinRealResidue + 1);
            const unsigned ceiling = std::min(StealMaxCap, headroom);
            stealcap = 1u + (unsigned)(Rng() % ceiling);
        }
    }
    if (stealcap > 0) StealIntoHead(headbb, realbb, stealcap);

    IRBuilder<> hb(headbb);
    LoadInst* cached = hb.CreateLoad(i64, cachegv, "DSCached");
    cached->setAlignment(Align(8));
    cached->setVolatile(true);
    Value* already = hb.CreateICmpNE(cached, ConstantInt::get(i64, 0), "DSAlready");
    hb.CreateCondBr(already, dispatchbb, doscanbb);

    IRBuilder<> sb(doscanbb);
    Function* fnfind = GetOrCreateFindModuleFn(m);
    Function* fnscan = GetOrCreateEatScanSumFn(m);
    Value* base = sb.CreateCall(fnfind, { ConstantInt::get(i64, plan.ModHash), ConstantInt::get(i32, plan.Salt) }, "DSBase");
    Value* sum = sb.CreateCall(fnscan, { base, slotsgv, ConstantInt::get(i32, (uint32_t)plan.Slots.size()), ConstantInt::get(i32, plan.Salt) }, "DSSum");
    StoreInst* store = sb.CreateStore(sum, cachegv);
    store->setAlignment(Align(8));
    store->setVolatile(true);
    sb.CreateBr(dispatchbb);

    IRBuilder<> db(dispatchbb);
    PHINode* finalsum = db.CreatePHI(i64, 2, "DSFinal");
    finalsum->addIncoming(cached, headbb);
    finalsum->addIncoming(sum, doscanbb);

    const unsigned numcases = 1u + (unsigned)plan.DeadSums.size();
    SwitchInst* sw = db.CreateSwitch(finalsum, defaultpollutebb, numcases);
    sw->addCase(ConstantInt::get(i64, plan.ExpectedSum), realbb);

    for (uint64_t dead : plan.DeadSums)
    {
        BasicBlock* dp = BasicBlock::Create(c, "DSDeadPol", &f, realbb);
        FillPolluteBlock(f, dp, realbb);
        MarkPolluteBlock(dp);
        sw->addCase(ConstantInt::get(i64, dead), dp);
    }

    FillPolluteBlock(f, defaultpollutebb, realbb);
    MarkPolluteBlock(defaultpollutebb);

    MarkCheckBlock(doscanbb);
    MarkCheckBlock(dispatchbb);
    MarkBBProcessed(headbb);
}

static void EmitHeapAccumulatorBody(Function& f, BasicBlock* headbb, BasicBlock* realbb, BasicBlock* defaultpollutebb)
{
    Module& m = *f.getParent();
    LLVMContext& c = f.getContext();
    IntegerType* i32 = Type::getInt32Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);
    StructType* slotty = StructType::get(c, { i64, i64 });

    ScanSitePlan plan = BuildScanSitePlan();

    const unsigned siteid = HeapAccSiteCounter++;
    const std::string slotsname = "RxHaccSlots" + std::to_string(siteid);
    const std::string cachename = "RxHaccCache" + std::to_string(siteid);

    const uint64_t ntdllhash = Fnv1aUtf16LowerAscii("ntdll.dll", plan.Salt);
    const uint64_t allocfnhash = Fnv1aAscii("RtlAllocateHeap", plan.Salt);
    const uint64_t freefnhash = Fnv1aAscii("RtlFreeHeap", plan.Salt);

    ArrayType* tablety = ArrayType::get(slotty, plan.Slots.size());
    SmallVector<Constant*, 16> slotconsts;
    for (const ScanSlot& s : plan.Slots)
    {
        slotconsts.push_back(ConstantStruct::get(slotty, { ConstantInt::get(i64, s.Hash), ConstantInt::get(i64, s.Value) }));
    }
    Constant* init = ConstantArray::get(tablety, slotconsts);
    auto* slotsgv = new GlobalVariable(m, tablety, true, GlobalValue::InternalLinkage, init, slotsname);
    slotsgv->setAlignment(MaybeAlign(8));

    auto* cachegv = new GlobalVariable(m, i64, false, GlobalValue::InternalLinkage, ConstantInt::get(i64, 0), cachename);
    cachegv->setAlignment(MaybeAlign(8));

    BasicBlock* doscanbb = BasicBlock::Create(c, "HAScan", &f, realbb);
    BasicBlock* dispatchbb = BasicBlock::Create(c, "HADisp", &f, realbb);

    unsigned stealcap = 0;
    {
        const unsigned rbsize = (unsigned)realbb->size();
        if (rbsize > StealMinRealResidue + 1)
        {
            const unsigned headroom = rbsize - (StealMinRealResidue + 1);
            const unsigned ceiling = std::min(StealMaxCap, headroom);
            stealcap = 1u + (unsigned)(Rng() % ceiling);
        }
    }
    if (stealcap > 0) StealIntoHead(headbb, realbb, stealcap);

    IRBuilder<> hb(headbb);
    LoadInst* cached = hb.CreateLoad(i64, cachegv, "HACached");
    cached->setAlignment(Align(8));
    cached->setVolatile(true);
    Value* already = hb.CreateICmpNE(cached, ConstantInt::get(i64, 0), "HAAlready");
    hb.CreateCondBr(already, dispatchbb, doscanbb);

    IRBuilder<> sb(doscanbb);
    Function* fnfind = GetOrCreateFindModuleFn(m);
    Function* fnhacc = GetOrCreateHeapAccumulateFn(m);
    Value* base = sb.CreateCall(fnfind, { ConstantInt::get(i64, plan.ModHash), ConstantInt::get(i32, plan.Salt) }, "HABase");

    EatSiteParams alloceat{ ntdllhash, allocfnhash, plan.Salt };
    EatSiteParams freeeat{ ntdllhash, freefnhash, plan.Salt };
    Value* allocfni = EmitEatLookupCall(sb, m, alloceat, "HAAllocFn");
    Value* freefni = EmitEatLookupCall(sb, m, freeeat, "HAFreeFn");

    const unsigned slotcount = (unsigned)plan.Slots.size();
    const unsigned bufsize = slotcount * 8;
    Value* sum = sb.CreateCall(fnhacc, { base, slotsgv, ConstantInt::get(i32, slotcount), ConstantInt::get(i32, bufsize), allocfni, freefni, ConstantInt::get(i32, plan.Salt) }, "HASum");
    StoreInst* store = sb.CreateStore(sum, cachegv);
    store->setAlignment(Align(8));
    store->setVolatile(true);
    sb.CreateBr(dispatchbb);

    IRBuilder<> db(dispatchbb);
    PHINode* finalsum = db.CreatePHI(i64, 2, "HAFinal");
    finalsum->addIncoming(cached, headbb);
    finalsum->addIncoming(sum, doscanbb);

    const unsigned numcases = 1u + (unsigned)plan.DeadSums.size();
    SwitchInst* sw = db.CreateSwitch(finalsum, defaultpollutebb, numcases);
    sw->addCase(ConstantInt::get(i64, plan.ExpectedSum), realbb);

    for (uint64_t dead : plan.DeadSums)
    {
        BasicBlock* dp = BasicBlock::Create(c, "HADeadPol", &f, realbb);
        FillPolluteBlock(f, dp, realbb);
        MarkPolluteBlock(dp);
        sw->addCase(ConstantInt::get(i64, dead), dp);
    }

    FillPolluteBlock(f, defaultpollutebb, realbb);
    MarkPolluteBlock(defaultpollutebb);

    MarkCheckBlock(doscanbb);
    MarkCheckBlock(dispatchbb);
    MarkBBProcessed(headbb);
}

static bool TryEmitAtBB(Function& f, BasicBlock* bb, SmallVectorImpl<BasicBlock*>& worklist, SmallPtrSetImpl<BasicBlock*>& seen)
{
    if (BBAlreadyProcessed(bb)) return false;
    if (SkipEntry && bb == &f.getEntryBlock()) return false;
    if (IsEHOrFuncletInterior(bb)) return false;
    if (bb->size() < MinBBInsts) return false;

    Instruction* splitat = PickInsertionPoint(bb);
    if (!splitat) return false;

    LLVMContext& c = f.getContext();
    IntegerType* i32 = Type::getInt32Ty(c);

    BasicBlock* realbb = bb->splitBasicBlock(splitat, "Cont");
    BasicBlock* polluteelsebb = BasicBlock::Create(c, "Cont", &f, realbb);

    Instruction* splitbr = bb->getTerminator();
    splitbr->eraseFromParent();

    if (EnableDispatchScan && DispatchScanPct > 0 && !WhitelistDlls.empty() && (unsigned)(Rng() % 100u) < DispatchScanPct)
    {
        EmitDispatchScanBody(f, bb, realbb, polluteelsebb);
        if (seen.insert(realbb).second) worklist.push_back(realbb);
        return true;
    }
    if (EnableHeapAcc && HeapAccPct > 0 && !WhitelistDlls.empty() && (unsigned)(Rng() % 100u) < HeapAccPct)
    {
        EmitHeapAccumulatorBody(f, bb, realbb, polluteelsebb);
        if (seen.insert(realbb).second) worklist.push_back(realbb);
        return true;
    }

    IRBuilder<> builder(bb);

    struct SiteSource
    {
        SourceKind Kind;
        Value* Val;
        uint32_t FactMask;
        unsigned ModIndex;
    };

    SmallVector<SourceKind, (size_t)SourceKind::Count> available = EnumerateEnabledSources();
    for (size_t i = available.size(); i > 1; --i)
    {
        const size_t j = (size_t)(Rng() % i);
        std::swap(available[i - 1], available[j]);
    }
    const unsigned desired = MinSourcesPerSite + (unsigned)(Rng() % (MaxSourcesPerSite - MinSourcesPerSite + 1));
    const unsigned poolsize = std::min((unsigned)available.size(), desired);

    Module* parentm = f.getParent();
    SmallVector<SiteSource, (size_t)MaxSourcesPerSite> pool;
    pool.reserve(poolsize);
    for (unsigned i = 0; i < poolsize; ++i)
    {
        const SourceKind sk = available[i];
        const unsigned mi = (sk == SourceKind::PebWalkModule) ? (unsigned)(Rng() % MaxModuleIndex) : 0u;

        // when both import and arbitrary whitelist pools are empty, this source kind MUST be skipped (continue); EAT sources need SOME (dll, export) tuple to bake, and a zero filled plan hashes nothing but zeros, which the runtime lookup never matches, routing every call into pollute
        auto pickeattuple = [&](bool& fromarb) -> const BinaryImport*
        {
            const bool wantarb = !WhitelistExports.empty() && (unsigned)(Rng() % 100u) < (unsigned)ArbExportPct;
            if (wantarb)
            {
                fromarb = true;
                return &WhitelistExports[Rng() % WhitelistExports.size()];
            }
            if (!BinaryImports.empty())
            {
                fromarb = false;
                return &BinaryImports[Rng() % BinaryImports.size()];
            }
            if (!WhitelistExports.empty())
            {
                fromarb = true;
                return &WhitelistExports[Rng() % WhitelistExports.size()];
            }
            return nullptr;
        };
        EatSiteParams eat{ 0, 0, 0 };
        if (sk == SourceKind::EatHashHit)
        {
            bool fromarb = false;
            const BinaryImport* t = pickeattuple(fromarb);
            if (!t) continue;
            eat.Salt = (uint32_t)Rng();
            eat.ModHash = Fnv1aUtf16LowerAscii(t->Dll.c_str(), eat.Salt);
            eat.ExpHash = Fnv1aAscii(t->Exp.c_str(), eat.Salt);
        }
        else if (sk == SourceKind::EatHashMiss)
        {
            bool fromarb = false;
            const BinaryImport* t = pickeattuple(fromarb);
            if (!t) continue;
            eat.Salt = (uint32_t)Rng();
            eat.ModHash = Fnv1aUtf16LowerAscii(t->Dll.c_str(), eat.Salt);
            eat.ExpHash = (uint64_t)Rng();
        }

        Value* val = EmitSourceValue(builder, *parentm, sk, mi, eat);
        pool.push_back({ sk, val, SourceLibrary[(size_t)sk].CompatibleFacts, mi });
    }

    const unsigned nbad = MinBadValues + (unsigned)(Rng() % (MaxBadValues - MinBadValues + 1));
    const unsigned mcount = nbad + 1;
    const unsigned knownpos = (unsigned)(Rng() % mcount);

    enum class CheckFlavor : uint8_t
    {
        ArxMatch,
        DirectTrue,
        DirectFalse,
        TebSelfRef,
        PebSelfRef,
        PebNeTeb,
        PebNeImgBase
    };
    struct CheckSpec
    {
        CheckFlavor Flavor;
        unsigned SourceIdx;
        FactKind Fact;
        uint32_t CompareVal;
    };

    SmallVector<CheckFlavor, 3> trueflavors;
    trueflavors.push_back(CheckFlavor::DirectTrue);
    if (EnableTebSelfRef) trueflavors.push_back(CheckFlavor::TebSelfRef);
    if (EnablePebSelfRef) trueflavors.push_back(CheckFlavor::PebSelfRef);

    SmallVector<CheckFlavor, 3> falseflavors;
    falseflavors.push_back(CheckFlavor::DirectFalse);
    if (EnablePebNeTeb) falseflavors.push_back(CheckFlavor::PebNeTeb);
    if (EnablePebNeImgBase) falseflavors.push_back(CheckFlavor::PebNeImgBase);

    SmallVector<CheckSpec, 8> specs(mcount);
    for (unsigned i = 0; i < mcount; ++i)
    {
        const bool isknown = (i == knownpos);
        const bool usearx = (Rng() & 1u);
        specs[i].SourceIdx = (unsigned)(Rng() % pool.size());
        if (usearx)
        {
            specs[i].Flavor = CheckFlavor::ArxMatch;
        }
        else if (isknown)
        {
            specs[i].Flavor = trueflavors[Rng() % trueflavors.size()];
            if (specs[i].Flavor == CheckFlavor::DirectTrue) specs[i].Fact = PickCompatibleFact(pool[specs[i].SourceIdx].FactMask);
        }
        else
        {
            specs[i].Flavor = falseflavors[Rng() % falseflavors.size()];
            if (specs[i].Flavor == CheckFlavor::DirectFalse) specs[i].Fact = PickCompatibleFact(pool[specs[i].SourceIdx].FactMask);
        }
    }

    unsigned arxcount = 0;
    for (auto& s : specs)
    {
        if (s.Flavor == CheckFlavor::ArxMatch) ++arxcount;
    }

    Value* int2 = nullptr;
    uint32_t knownvalue = 0;
    std::vector<ArxStep> chain;
    uint32_t seed = 0;
    FactKind arxfact = FactKind::Lo8;

    // only emit the ARX chain when at least one cascade position actually consumes it; emitting it when arxcount==0 produces dead IR that LLVM's DCE strips, and the stripped site loses its primary diversity source while still paying the IR size cost at pass time
    if (arxcount > 0)
    {
        const unsigned arxsrcidx = (unsigned)(Rng() % pool.size());
        const uint32_t arxmask = pool[arxsrcidx].FactMask;
        arxfact = PickCompatibleFact(arxmask);
        const uint32_t arxinputrt = FactLibrary[(size_t)arxfact].RtValue;

        Value* int1 = EmitFactExtract(builder, pool[arxsrcidx].Val, arxfact);
        chain = GenerateArxChain();
        seed = (uint32_t)Rng();
        int2 = EmitArxChain(builder, int1, seed, chain);
        knownvalue = ArxEvalU32(seed, arxinputrt, chain);
    }

    std::set<uint32_t> arxused{ knownvalue };
    for (unsigned i = 0; i < mcount; ++i)
    {
        switch (specs[i].Flavor)
        {
            case CheckFlavor::ArxMatch:
                if (i == knownpos)
                {
                    specs[i].CompareVal = knownvalue;
                }
                else
                {
                    uint32_t v;
                    do { v = (uint32_t)Rng(); } while (!arxused.insert(v).second);
                    specs[i].CompareVal = v;
                }
                break;
            case CheckFlavor::DirectTrue:
                specs[i].CompareVal = FactLibrary[(size_t)specs[i].Fact].RtValue;
                break;
            case CheckFlavor::DirectFalse:
                specs[i].CompareVal = GenerateImpossibleForFact(specs[i].Fact);
                break;
            case CheckFlavor::TebSelfRef:
            case CheckFlavor::PebSelfRef:
            case CheckFlavor::PebNeTeb:
            case CheckFlavor::PebNeImgBase:
                break;
        }
    }

    SmallVector<BasicBlock*, 8> checks;
    checks.push_back(bb);
    for (unsigned i = 1; i < mcount; ++i) checks.push_back(BasicBlock::Create(c, "Cont", &f, realbb));

    SmallVector<BasicBlock*, 8> badpollutebbs(nbad);
    for (unsigned i = 0; i < nbad; ++i) badpollutebbs[i] = BasicBlock::Create(c, "Cont", &f, realbb);

    SmallVector<BasicBlock*, 8> matchtgts(mcount);
    unsigned badidx = 0;
    for (unsigned i = 0; i < mcount; ++i)
    {
        if (i == knownpos) { matchtgts[i] = realbb; continue; }
        matchtgts[i] = badpollutebbs[badidx++];
    }

    // every bad path gets its OWN corruption chain so SimplifyCFG can't fold the last cascade branch into `br bb` (match_tgt and next_tgt are always different blocks) and ida shows M distinct bad paths instead of a fan-in to a single pollute body
    for (unsigned i = 0; i < nbad; ++i)
    {
        FillPolluteBlock(f, badpollutebbs[i], realbb);
        MarkPolluteBlock(badpollutebbs[i]);
    }
    FillPolluteBlock(f, polluteelsebb, realbb);
    MarkPolluteBlock(polluteelsebb);

    unsigned stealcap = 0;
    {
        const unsigned rbsize = (unsigned)realbb->size();
        if (rbsize > StealMinRealResidue + 1)
        {
            const unsigned headroom = rbsize - (StealMinRealResidue + 1);
            const unsigned ceiling = std::min(StealMaxCap, headroom);
            stealcap = 1u + (unsigned)(Rng() % ceiling);
        }
    }
    if (stealcap > 0) StealIntoHead(bb, realbb, stealcap);

    builder.SetInsertPoint(bb);
    for (unsigned i = 0; i < mcount; ++i)
    {
        IRBuilder<> cb(checks[i]);
        if (i == 0) cb.SetInsertPoint(bb);

        Value* cmp = nullptr;
        switch (specs[i].Flavor)
        {
            case CheckFlavor::ArxMatch:
                cmp = cb.CreateICmpEQ(int2, ConstantInt::get(i32, specs[i].CompareVal), "RelocopCmp");
                break;
            case CheckFlavor::DirectTrue:
            case CheckFlavor::DirectFalse:
            {
                Value* lhs = EmitFactExtract(cb, pool[specs[i].SourceIdx].Val, specs[i].Fact);
                cmp = cb.CreateICmpEQ(lhs, ConstantInt::get(i32, specs[i].CompareVal), "RelocopCmp");
                break;
            }
            case CheckFlavor::TebSelfRef: cmp = EmitTebSelfRefCheck(cb); break;
            case CheckFlavor::PebSelfRef: cmp = EmitPebSelfRefCheck(cb); break;
            case CheckFlavor::PebNeTeb: cmp = EmitPebNeTebCheck(cb); break;
            case CheckFlavor::PebNeImgBase: cmp = EmitPebNeImgBaseCheck(cb); break;
        }

        BasicBlock* matchtgt = matchtgts[i];
        BasicBlock* nexttgt = (i + 1 < mcount) ? checks[i + 1] : polluteelsebb;
        cb.CreateCondBr(cmp, matchtgt, nexttgt);

        if (i > 0) MarkCheckBlock(checks[i]);
    }

    MarkBBProcessed(bb);

    if (seen.insert(realbb).second) worklist.push_back(realbb);

    return true;
}

static bool ProcessFunction(Function& f)
{
    if (f.isDeclaration()) return false;
    if (HasNoObfuscateAnnotation(f) || HasNoWinPEOpAnnotation(f)) return false;
    if (!HasObfuscateAnnotation(f)) return false;

    PerFuncScratchAlloca = nullptr;

    SmallVector<BasicBlock*, 64> worklist;
    SmallPtrSet<BasicBlock*, 32> seen;
    for (BasicBlock& bb : f)
    {
        worklist.push_back(&bb);
        seen.insert(&bb);
    }

    bool mutated = false;
    unsigned emitted = 0;

    while (!worklist.empty())
    {
        if (emitted >= PerFunctionCap) break;

        BasicBlock* bb = worklist.pop_back_val();
        if (IsPolluteBlock(bb)) continue;
        if (IsCheckBlock(bb)) continue;

        if (SkipLoops)
        {
            DominatorTree dt;
            dt.recalculate(f);
            LoopInfo li;
            li.analyze(dt);
            if (li.getLoopFor(bb) != nullptr) continue;
        }

        if (!TryEmitAtBB(f, bb, worklist, seen)) continue;

        ++emitted;
        mutated = true;
    }

    return mutated;
}

bool RunWinPEOpaque(Module& m)
{
    if (!WinPEOpaqueEnable) return false;

    std::random_device rd;
    uint64_t seed = (uint64_t)rd();
    seed ^= (uint64_t)std::chrono::high_resolution_clock::now().time_since_epoch().count();
    seed ^= ((uint64_t)rd()) << 32;
    seed ^= 0x52454C4F434F505FULL;
    Rng.seed(seed);

    // per module site counters MUST reset on every invocation so global names stay stable across runs; a stale counter from a previous module would skip indices and produce non-contiguous RxScanCache / RxHaccCache / RxEatCache names that complicate post-link analysis
    DispatchScanSiteCounter = 0;
    EatLookupSiteCounter = 0;
    HeapAccSiteCounter = 0;

    PopulateBinaryImports(m);

    bool mutated = false;
    for (Function& f : m) mutated |= ProcessFunction(f);

    // fixed point inlining loop MUST run at this pass boundary because we can't rely on the downstream pipeline including AlwaysInliner; without it sibling obfuscators see the __rx_* calls as opaque side effect operations and skip them, and the final binary ships with the helper functions themselves visible in its .text; each inline round picks up nested helpers (eat_lookup_cached → eat_lookup → hash_wide) so the loop terminates on its own once every site is flat
    unsigned inlinerounds = 0;
    for (;;)
    {
        ++inlinerounds;
        SmallVector<CallInst*, 64> toinline;
        for (Function& fn : m)
        {
            if (fn.isDeclaration()) continue;
            if (!fn.hasFnAttribute(Attribute::AlwaysInline)) continue;
            for (User* u : fn.users())
            {
                auto* ci = dyn_cast<CallInst>(u);
                if (!ci) continue;
                if (ci->getCalledFunction() != &fn) continue;
                if (ci->getFunction() == &fn) continue;
                toinline.push_back(ci);
            }
        }
        if (toinline.empty()) break;
        unsigned thisround = 0;
        for (CallInst* ci : toinline)
        {
            InlineFunctionInfo ifi;
            if (InlineFunction(*ci, ifi).isSuccess()) ++thisround;
        }
        if (thisround == 0) break;
        if (inlinerounds > 16) break;
    }

    for (Function& fn : m)
    {
        if (fn.isDeclaration()) continue;
        if (!fn.hasFnAttribute(Attribute::AlwaysInline)) continue;
        if (fn.use_empty()) fn.setLinkage(GlobalValue::InternalLinkage);
    }

    return mutated;
}

PreservedAnalyses WinPEOpaquePass::run(Module& m, ModuleAnalysisManager&)
{
    bool mutated = RunWinPEOpaque(m);
    return mutated ? PreservedAnalyses::none() : PreservedAnalyses::all();
}