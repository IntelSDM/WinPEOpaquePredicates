#pragma once

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"

struct WinPEOpaquePass : llvm::PassInfoMixin<WinPEOpaquePass>
{
    llvm::PreservedAnalyses run(llvm::Module& m, llvm::ModuleAnalysisManager&);
};

bool RunWinPEOpaque(llvm::Module& m);

extern llvm::cl::opt<bool> WinPEOpaqueEnable;