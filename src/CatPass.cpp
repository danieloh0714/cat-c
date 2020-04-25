#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

using namespace llvm;

namespace {
  struct CAT : public FunctionPass {
    static char ID; 

    CAT() : FunctionPass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
	return false;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction (Function &F) override {
      int addCount = 0;
      int subCount = 0;
      int newCount = 0;
      int getCount = 0;
      int setCount = 0;
      
      for (auto& bb : F) {
	  for (auto& I : bb) {
	      if (isa<CallInst> (I)) {
		      CallInst *callInst = cast<CallInst>(&I);
		      Function *calledFunction = callInst->getCalledFunction();
		      std::string calledName = calledFunction->getName();
		      if (calledName == "CAT_add") {
			  addCount++;
		      }
		      else if (calledName == "CAT_sub") {
			  subCount++;
		      }
		      else if (calledName == "CAT_new") {
			  newCount++;
		      }
		      else if (calledName == "CAT_get") {
			  getCount++;
		      }
		      else if (calledName == "CAT_set") {
			  setCount++;
		      }
	      }
	  }

	  std::string funcName = F.getName();
	  
	  if (addCount > 0) {
	      errs() << "H1: \"" << funcName << "\": CAT_add: " << addCount << "\n";
	  }
	  if (subCount > 0) {
	      errs() << "H1: \"" << funcName << "\": CAT_sub: " << subCount << "\n";
	  }
	  if (newCount > 0) {
	      errs() << "H1: \"" << funcName << "\": CAT_new: " << newCount << "\n";
	  }
	  if (getCount > 0) {
	      errs() << "H1: \"" << funcName << "\": CAT_get: " << getCount << "\n";
	  }
	  if (setCount > 0) {
	      errs() << "H1: \"" << funcName << "\": CAT_set: " << setCount << "\n";
	  }
	  
	  break;
      }
            
      return false;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
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
