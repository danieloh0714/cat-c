#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/SmallBitVector.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/SparseBitVector.h"
#include <set>
#include <unordered_set>
#include <vector>
#include <map>
#include <unordered_map>

using namespace llvm;

namespace {
  struct CAT : public FunctionPass {
    static char ID; 

    CAT() : FunctionPass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
	std::map<, >
	return false;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    
    bool runOnFunction (Function &F) override {
	errs() << "Function \"" << F.getName() << "\" \n";

	DominatorTree& DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();

	for (auto& B : F) {
	    for (auto& I : B) {
		errs() << "INSTRUCTION: " << I << "\n";
		errs() << "***************** GEN\n{\n";
		if (isa<CallInst>(I)) {
		    CallInst* callInst = cast<CallInst>(&I);
		    Function* calledFunction = callInst->getCalledFunction();
		    std::string calledName = calledFunction->getName();
		    if (calledName == "CAT_new" || calledName == "CAT_add" || calledName == "CAT_sub" || calledName == "CAT_set") {
			errs() << " " << I << "\n";
		    }
		}
		errs() << "}\n";
		errs() << "**************************************\n";
		errs() << "***************** KILL\n{\n";
		if (isa<CallInst>(I)) {
		    CallInst* callInst = cast<CallInst>(&I);
		    Function* calledFunction = callInst->getCalledFunction();
		    std::string calledName = calledFunction->getName();
		    if (calledName == "CAT_new" || calledName == "CAT_add" || calledName == "CAT_sub" || calledName == "CAT_set") {
			if (calledName == "CAT_new") {
			    Instruction* modVariable = &I;
			    for (auto& bb : F) {
				for (auto& i : bb) {
				    if (isa<CallInst>(i)) {
					CallInst* callInst2 = cast<CallInst>(&i);
					Function* calledFunction2 = callInst2->getCalledFunction();
					std::string calledName2 = calledFunction2->getName();
					if (calledName2 == "CAT_add" || calledName2 == "CAT_sub" || calledName2 == "CAT_set") {
					    if (modVariable == cast<Instruction>(callInst2->getArgOperand(0))) {
						errs() << " " << i << "\n";
					    }
					}
				    }
				}
			    }
			}
			else {
			    Instruction* modVariable = cast<Instruction>(callInst->getArgOperand(0));
			    for (auto& bb : F) {
				for (auto& i : bb) {
				    if (isa<CallInst>(i)) {
					CallInst* callInst2 = cast<CallInst>(&i);
					Function* calledFunction2 = callInst2->getCalledFunction();
					std::string calledName2 = calledFunction2->getName();
					if (calledName2 == "CAT_new") {
					    if (modVariable == &i) {
						errs() << " " << i << "\n";
					    }
					}
					if (calledName2 == "CAT_add" || calledName2 == "CAT_sub" || calledName2 == "CAT_set") {
					    if (&i != &I && modVariable == cast<Instruction>(callInst2->getArgOperand(0))) {
						errs() << " " << i << "\n";
					    }
					}
				    }
				}
			    }
			}
		    }
		}
		errs() << "}\n**************************************\n\n\n\n";
	    }
	}

	return false;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.addRequired<DominatorTreeWrapperPass>();
      AU.setPreservesAll();
    }
  };
}

// Next there is code to register your pass to "opt"
char CAT::ID = 0;
static RegisterPass<CAT> X("CAT", "Homework for the CAT class");

// Next there is code to register your pass to "clang"
static CAT * _PassMaker = NULL;
static RegisterStandardPasses _RegPass1(PassManagerBuilder::EP_OptimizerLast,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT());}}); // ** for -Ox
static RegisterStandardPasses _RegPass2(PassManagerBuilder::EP_EnabledOnOptLevel0,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT()); }}); // ** for -O0
