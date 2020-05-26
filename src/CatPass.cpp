#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/IR/Constants.h"
#include <map>
#include <vector>

using namespace llvm;

namespace {
  struct CAT : public FunctionPass {
    static char ID; 
	Module *currentModule;

    CAT() : FunctionPass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
		currentModule = &M;
		return false;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction (Function &F) override {
		bool modified = false;

		DominatorTree& DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();

		int instCount = 0;
		for (auto& B : F) {
	    	for (auto& I : B) {
				instCount++;
	    	}
		}

		std::map<Instruction*, std::pair<std::pair<llvm::BitVector, llvm::BitVector>, std::pair<llvm::BitVector, llvm::BitVector>>> instGKIO; // <<GEN, KILL>, <IN, OUT>>
		std::map<int, Instruction*> instMap;
		int instIndex = 0;

		//
		// Compute GEN and KILL sets for each instruction.
		//
		for (auto& B : F) {
	    	for (auto& I : B) {
				instGKIO[&I].first.first = llvm::BitVector(instCount); // Initialize GEN set.
				instGKIO[&I].first.second = llvm::BitVector(instCount); // Initialize KILL set.
				instGKIO[&I].second.first = llvm::BitVector(instCount); // Initialize IN set.
				instGKIO[&I].second.second = llvm::BitVector(instCount); // Initialize OUT set.

				instMap[instIndex] = &I;
	
				// Compute GEN set.
				if (auto callInst = dyn_cast<CallInst>(&I)) {
			    	Function* calledFunction = callInst->getCalledFunction();
			    	std::string calledName = calledFunction->getName();
			    	if (calledName == "CAT_new" || calledName == "CAT_add" || calledName == "CAT_sub" || calledName == "CAT_set") {
						instGKIO[&I].first.first.set(instIndex);
		   	 		}
				}

				// Compute KILL set.
				if (auto callInst = dyn_cast<CallInst>(&I)) {
		    		Function* calledFunction = callInst->getCalledFunction();
		    		std::string calledName = calledFunction->getName();
		    		int killInstIndex = 0;
					if (calledName == "CAT_new") {
			    		Instruction* modVariable = &I;
			    		for (auto& bb : F) {
							for (auto& i : bb) {
				    			if (auto callInst2 = dyn_cast<CallInst>(&i)) {
									Function* calledFunction2 = callInst2->getCalledFunction();
									std::string calledName2 = calledFunction2->getName();
									if (calledName2 == "CAT_add" || calledName2 == "CAT_sub" || calledName2 == "CAT_set") {
					    				if (modVariable == cast<Instruction>(callInst2->getArgOperand(0))) {
											instGKIO[&I].first.second.set(killInstIndex);
					    				}
									}
				    			}
				    			killInstIndex++;
							}
			    		}	
					}
					else if (calledName == "CAT_add" || calledName == "CAT_sub" || calledName == "CAT_set") {
			    		Instruction* modVariable = cast<Instruction>(callInst->getArgOperand(0));
			    		for (auto& bb : F) {
							for (auto& i : bb) {
				    			if (auto callInst2 = dyn_cast<CallInst>(&i)) {
									Function* calledFunction2 = callInst2->getCalledFunction();
									std::string calledName2 = calledFunction2->getName();
									if (calledName2 == "CAT_new") {
					    				if (modVariable == &i) {
											instGKIO[&I].first.second.set(killInstIndex);
					    				}
									}
									if (calledName2 == "CAT_add" || calledName2 == "CAT_sub" || calledName2 == "CAT_set") {
					    				if (&i != &I && modVariable == cast<Instruction>(callInst2->getArgOperand(0))) {
											instGKIO[&I].first.second.set(killInstIndex);
					    				}
									}
				    			}
				    			killInstIndex++;
							}
			    		}
					}
				}

				instIndex++;
	    	}
		}

		//
		// Compute IN and OUT sets for each instruction.
		//
		bool outChange = true; // if any changes to OUT occur

		do {
			outChange = false;
			for (auto& B : F) {
				bool firstInst = true;
				Instruction* prevInst;
				for (auto& I : B) {
					// Compute IN for instruction I.
					instGKIO[&I].second.first.reset(); // reset IN to all zeros
					if (firstInst) { // if I is the first instruction in its BB, IN = U (all predecessors of BB) OUT
						for (auto pred : predecessors(&B)) {
							instGKIO[&I].second.first |= instGKIO[pred->getTerminator()].second.second;
						}
						firstInst = false;
					}
					else { // if I is not the first instruction in its BB, then IN = OUT of previous instruction
						instGKIO[&I].second.first |= instGKIO[prevInst].second.second;
					}
					prevInst = &I;

					//Compute OUT for instruction I.
					llvm::BitVector oldOut = instGKIO[&I].second.second; // bitwise operations store the value in the first operand, so we create copies
					llvm::BitVector killCopy = instGKIO[&I].first.second;
					llvm::BitVector inCopy = instGKIO[&I].second.first;
					llvm::BitVector genCopy = instGKIO[&I].first.first;

					inCopy &= killCopy.flip(); // IN - KILL
					genCopy |= inCopy; // GEN U (IN - KILL)
					instGKIO[&I].second.second = genCopy; // OUT = GEN U (IN - KILL)

					if (oldOut != instGKIO[&I].second.second) {outChange = true;}
				}
			}
		} while (outChange);

		//
		// Constant propagation.
		//
		std::vector<Instruction*> toDeletePropagation;

		for (auto& B : F) {
			for (auto& I : B) {
				if (auto callInst = dyn_cast<CallInst>(&I)) {
					Function* calledFunction = callInst->getCalledFunction();
					std::string calledName = calledFunction->getName();

					if (calledName == "CAT_get") {
						for (int i = 0; i < instCount; i++) {
							if (instGKIO[&I].second.first[i]) {
								auto matchCallInst = dyn_cast<CallInst>(instMap[i]);
								Function* matchCallFunction = matchCallInst->getCalledFunction();
								std::string matchCallName = matchCallFunction->getName();
								
								Value* operand = callInst->getArgOperand(0);
								Instruction* operandInst = cast<Instruction>(operand);

								if (instMap[i] == operandInst) {
									Value* op = operandInst->getOperand(0);
									if (auto opInt = dyn_cast<ConstantInt>(op)) {
										callInst->replaceAllUsesWith(opInt);
										toDeletePropagation.push_back(callInst);
										modified = true;
									}
								}
								else if (matchCallName == "CAT_set") {
									Value* catSetOp = instMap[i]->getOperand(0);
									if (auto catSetOpInst = dyn_cast<Instruction>(catSetOp)) {
										if (catSetOpInst == operandInst) {
											Value* op = instMap[i]->getOperand(1);
											if (auto opInt = dyn_cast<ConstantInt>(op)) {
												callInst->replaceAllUsesWith(opInt);
												toDeletePropagation.push_back(callInst);
												modified = true;
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}

		// Delete instructions that were replaced.
		for (auto I : toDeletePropagation) {
			I->eraseFromParent();
		}

		//
		// Constant folding.
		//
		std::vector<Instruction*> toDeleteFolding;

		// Check if CAT_set is in the module.
		if (currentModule->getFunction("CAT_set") == NULL) {
			return modified;
		}

		// Fold CAT_add and CAT_sub into CAT_set.
		for (auto& B : F) {
			for (auto& I : B) {
				if (auto callInst = dyn_cast<CallInst>(&I)) {
					Function* calledFunction = callInst->getCalledFunction();
					std::string calledName = calledFunction->getName();
					
					if (calledName == "CAT_add" || calledName == "CAT_sub") {
						IRBuilder<> builder(callInst);

						bool cont = false;
						for (int i = 0; i < instCount; i++) {
							if (instGKIO[&I].second.first[i]) {
								if (auto inCallInst = dyn_cast<CallInst>(instMap[i])) {
									std::string inCallName = inCallInst->getCalledFunction()->getName();
									if (!(inCallName == "CAT_new" || inCallName == "CAT_set")) {
										cont = true;
										break;
									}
								}
							}
						}

						if (cont) {continue;}
						
						Value* operandZero = callInst->getOperand(0);

						Value* operandOne = callInst->getOperand(1);
						Instruction* operandOneInst = cast<Instruction>(operandOne);
						Value* operandOneInt = dyn_cast<ConstantInt>(operandOneInst->getOperand(0));

						Value* operandTwo = callInst->getOperand(2);
						Instruction* operandTwoInst = cast<Instruction>(operandTwo);
						Value* operandTwoInt = dyn_cast<ConstantInt>(operandTwoInst->getOperand(0));

						Value* newValue;
						if (calledName == "CAT_add") {
							newValue = builder.CreateAdd(operandOneInt, operandTwoInt);
						}
						else {
							newValue = builder.CreateSub(operandOneInt, operandTwoInt);
						}

						std::vector<Value*> args = {operandZero, newValue};
						Value* foldedValue = builder.CreateCall(currentModule->getFunction("CAT_set"), args);
						auto foldedCallInst = dyn_cast<CallInst>(foldedValue);
						foldedCallInst->setTailCall();

						toDeleteFolding.push_back(callInst);
						modified = true;
					}
				}
			}
		}

		// Delete instructions that were replaced.
		for (auto I : toDeleteFolding) {
			I->eraseFromParent();
		}

		return modified;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.addRequired<DominatorTreeWrapperPass>();
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
