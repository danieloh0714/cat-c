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
#include <bitset>
#include <utility>

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
	errs() << "Function \"" << F.getName() << "\" \n";

	DominatorTree& DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();

	int instCount = 0;
	for (auto& B : F) {
	    for (auto& I : B) {
		instCount++;
	    }
	}

	std::map<int, std::pair<llvm::BitVector, llvm::BitVector>> genKillMap; // pair.first is GEN; pair.second is KILL
	std::map<int, Instruction*> instMap;
	int instIndex = 0;

	// Compute GEN and KILL sets for each instruction.
	for (auto& B : F) {
	    for (auto& I : B) {
		genKillMap[instIndex].first = llvm::BitVector(instCount); // Initialize GEN set.
		genKillMap[instIndex].second = llvm::BitVector(instCount); // Initialize KILL set.
		instMap[instIndex] = &I;
	
		if (isa<CallInst>(I)) {
		    CallInst* callInst = cast<CallInst>(&I);
		    Function* calledFunction = callInst->getCalledFunction();
		    std::string calledName = calledFunction->getName();
		    if (calledName == "CAT_new" || calledName == "CAT_add" || calledName == "CAT_sub" || calledName == "CAT_set") {
			genKillMap[instIndex].first.set(instIndex);
		    }
		}
		if (isa<CallInst>(I)) {
		    CallInst* callInst = cast<CallInst>(&I);
		    Function* calledFunction = callInst->getCalledFunction();
		    std::string calledName = calledFunction->getName();
		    int killInstIndex = 0;
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
						genKillMap[instIndex].second.set(killInstIndex);
					    }
					}
				    }
				    killInstIndex++;
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
						genKillMap[instIndex].second.set(killInstIndex);
					    }
					}
					if (calledName2 == "CAT_add" || calledName2 == "CAT_sub" || calledName2 == "CAT_set") {
					    if (&i != &I && modVariable == cast<Instruction>(callInst2->getArgOperand(0))) {
						genKillMap[instIndex].second.set(killInstIndex);
					    }
					}
				    }
				    killInstIndex++;
				}
			    }
			}
		    }
		}
		instIndex++;
	    }
	}

	// Print GEN and KILL sets for each instruction.
	instIndex = 0;
	for (auto& B : F) {
	    for (auto& I : B) {
		errs() << "INSTRUCTION: " << I << "\n***************** GEN\n{\n";
		for (int i = 0; i < instCount; i++) {
		    if (genKillMap[instIndex].first[i]) {
			errs() << " " << *instMap[i] << "\n";
		    }
		}
		errs() << "}\n**************************************\n***************** KILL\n{\n";
		for (int i = 0; i < instCount; i++) {
		    if (genKillMap[instIndex].second[i]) {
			errs() << " " << *instMap[i] << "\n";
		    }
		}
		errs() << "}\n**************************************\n\n\n\n";
		instIndex++;
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
