#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"


#include "WinPEOpaquePass.h"
#include "llvm/IR/InlineAsm.h"

#include <ctime>
#include <cstdlib>

using namespace llvm;


struct ObfuscationPass : PassInfoMixin<ObfuscationPass>
{
    PreservedAnalyses run(Module& m, ModuleAnalysisManager&)
    {
        return PreservedAnalyses::none();
    }
};

llvm::PassPluginLibraryInfo GetPassPluginInfo()
{
    return
    {
        LLVM_PLUGIN_API_VERSION,
        "WinPEOpaquePass",
        LLVM_VERSION_STRING,
        [](PassBuilder& pb)
        {
            pb.registerOptimizerLastEPCallback([](ModulePassManager& pm, OptimizationLevel)
            {
               

               // pm.addPass(PolyMBAPass());
                //pm.addPass(ConstMBAPass());
                //pm.addPass(LinearMBAPass());
                 //  pm.addPass(NonlinearMBAOpaquePass());
pm.addPass(WinPEOpaquePass());
            });
        }
    };
}
#ifndef LLVM_BYE_LINK_INTO_TOOLS
extern "C"
__declspec(dllexport) LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
#ifdef _WIN32
#endif
    srand(time(0));
    return GetPassPluginInfo();
}
#endif