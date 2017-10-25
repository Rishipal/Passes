
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Module.h"

#include "llvm/Analysis/LoopInfoImpl.h"

#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Metadata.h>
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/CFG.h"
#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/DebugLoc.h>
#include "llvm/Support/raw_ostream.h"
#include "llvm/PassSupport.h"

//This file should be included after including the above headers only 

//#include "printHelper.h"

#include "Hello.h"

using namespace llvm;
#include "HelloHelper.h"


namespace
{
    struct Hello : public ModulePass
    {
        static char ID;
        Hello() : ModulePass(ID)
        {
            initializeHelloPass(*PassRegistry::getPassRegistry());
        }

        virtual void getAnalysisUsage(AnalysisUsage &AU) const override
        {
            AU.addRequired<DominatorTreeWrapperPass>();
            AU.addRequired<PostDominatorTreeWrapperPass>();
            AU.addRequired<LoopInfoWrapperPass>();
        }


        //I have not used LoopInfo here. Hence I am able to calculate the inner loops as well
        //LoopInfo.begin() does not calculate inner loops. 
        //LoopInfo.begin/end is just iterates over top level loops / outer loops
        unsigned int findNumberOfLoopsInModule(const Module &M)
        {
            unsigned int loopCount = 0;
            for (auto F = M.begin(); F != M.end(); F++)
            {
                //Placing this check here because my original .c file compiled from clang 
                //was using a system call - printf
                //and llvm passes do not run on functions which are not defined within the module? 
                //hence analysis information of DominatorTree pass was unavailable when I try to access it here
                //without this check it will crash for inputs which use printf
                if (F->isDeclaration())
                    continue;
                DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>(*const_cast<Function*>(&*F)).getDomTree();
                for (auto BB = F->begin(); BB != F->end(); BB++)
                {
                    for (auto BBSucc = succ_begin(&*BB); BBSucc != succ_end(&*BB); BBSucc++)
                    {
                        if (DT.dominates(*BBSucc, &*BB))
                        { //found a loop
                            loopCount++;
                        }
                    }
                }
            }
            return loopCount;
        }

        //LoopInfo.begin() does not calculate inner loops. 
        //LoopInfo.begin/end is just iterates over top level loops / outer loops
        //Hence, this returns only number of outer loops - verified this!
        unsigned int findLoopCountUsingLoopInfo(const Module &M)
        {
            unsigned int loopCount = 0;
            for (auto F = M.begin(); F != M.end(); F++)
            {
                //Placing this check here because my original .c file compiled from clang 
                //was using a system call - printf
                //and llvm passes do not run on functions which are not defined within the module? 
                //hence analysis information of LoopInfoWrapperPass was unavailable when I try to access it here
                //without this check it will crash for inputs which use printf
                if (F->isDeclaration())
                    continue;
                LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(*const_cast<Function*>(&*F)).getLoopInfo();
                for (auto loop = LI.begin(); loop != LI.end(); loop++)
                {
                    loopCount++;
                }
            }
            return loopCount;
        }



        //For this function F, for every outer loop, call getAllDepthSubLoopCount
        unsigned int findTotalLoopCountForFunctionUsingLoopInfo(const Function &F)
        {
            unsigned int loopCount = 0;
            LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(*const_cast<Function*>(&F)).getLoopInfo();
            for (auto loop = LI.begin(); loop != LI.end(); loop++)
            {
                loopCount++;
                loopCount += getAllDepthSubLoopCount(*loop);
            }
            return loopCount;
        }

        unsigned int findTotalLoopCountUsingLoopInfo(const Module &M)
        {
            unsigned int loopCount = 0;
            for (auto F = M.begin(); F != M.end(); F++)
            {
                //Placing this check here because my original .c file compiled from clang 
                //was using a system call - printf
                //and llvm passes do not run on functions which are not defined within the module? 
                //hence analysis information of LoopInfoWrapperPass was unavailable when I try to access it here
                //without this check it will crash for inputs which use printf
                if (F->isDeclaration())
                    continue;
                loopCount += findTotalLoopCountForFunctionUsingLoopInfo(*F);
            }
            return loopCount;
        }

        //find total number of loop exiting edges/blocks in the module
        //is number of exiting edges == number of exiting blocks??
        //Can a block that is exiting have 2 exiting edges??
        unsigned int findTotalLoopExitingEdges(const Module &M)
        {
            unsigned int numExitEdgesInModule = 0;
            for (auto F = M.begin(); F != M.end(); F++)
            {
                if (F->isDeclaration())
                    continue;
                LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(*const_cast<Function*>(&*F)).getLoopInfo();
                for (auto Loop = LI.begin(); Loop != LI.end(); Loop++)
                {
                    //call function
                    //subloops calls the same function recursive from within the function
                    numExitEdgesInModule += getNumExitingEdgesFromLoop(*Loop);
                }
            }
            return numExitEdgesInModule;
        }


        unsigned int MrCompilerMultipleEntryLoops(Module &M)
        {
            unsigned int multipleEntryLoops = 0;
            visited.clear();
            for (Module::iterator F = M.begin(); F != M.end(); F++)// : M.getFunctionList())
            {
                for (Function::iterator BB1 = F->begin(); BB1 != F->end(); BB1++)
                {
                    Function::iterator BB2 = BB1;
                    //errs() << BB1.getName() << "\n";
                    for (;BB2 != F->end(); BB2++)
                    {
                        visited.clear();

                        if (isreachable(&*BB1, &*BB2))
                        {
                            llvm::StringRef name1 = BB1->getName();
                            llvm::StringRef name2 = BB2->getName();
                            errs() << name2 << "is reachable from " << name1 << "\n";
                            for (auto succ = succ_begin(&*BB2); succ != succ_end(&*BB2); succ++)
                            {
                                errs() << "		Success of " << name2 << " is " << succ->getName() << "\n";
                                if (*succ == &*BB1)
                                {
                                    multipleEntryLoops++;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            return multipleEntryLoops;
        }


        void printControlDependenceMap(std::map< BasicBlock*, std::set<BasicBlock*> > &controlDependenceMap)
        {
            for (auto it = controlDependenceMap.begin(); it != controlDependenceMap.end(); it++)
            {
                errs() << "\n" << it->first->getName() << "is control dependent on ";
                for (auto BBList : it->second)
                {
                    errs() << BBList->getName() << " , ";
                }
            }
        }

        void dumpControlDependence(Module &M)
        {
            std::map< BasicBlock*, std::set<BasicBlock*> > controlDependenceMap;
            for (Module::iterator F = M.begin(); F != M.end(); F++)
            {
                for (Function::iterator BB1 = F->begin(); BB1 != F->end(); BB1++)
                {
                    for (Function::iterator BB2 = BB1; BB2 != F->end(); BB2++)
                    {
                        visited.clear();

                        if (isreachable(&*BB1, &*BB2))
                        {
                            errs() << "BB1: " << BB1->getName() << " BB2: " << BB2->getName() << "\n";

                            PostDominatorTree &PDT = getAnalysis<PostDominatorTreeWrapperPass>(*F).getPostDomTree();
                            DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>(*F).getDomTree();
                            //errs() << BB1->getName() << " has " << BB1->getTerminator()->getNumSuccessors() << "\n";
                            if (PDT.dominates(&*BB2, &*BB1)) continue;
                            //bool isControlDependent = false;
                            /*for (auto succ = succ_begin(&*BB1); succ != succ_end(&*BB1); succ++)
                            {
                            if (*succ == &*BB2) continue;
                            bool postDominatesSucc = PDT.dominates(&*BB2, *succ);
                            if (isControlDependent == true)
                            {
                            if (postDominatesSucc)
                            {
                            assert("This should never happen. A block BB2 can not post dominate both succ of BB1?");
                            }
                            }
                            if (postDominatesSucc)
                            {
                            controlDependenceMap[&*BB2].insert(&*BB1);
                            isControlDependent = true;
                            }
                            }*/
                            if (DT.dominates(&*BB1, &*BB2))
                            {
                                if (!PDT.dominates(&*BB2, &*BB1))
                                {
                                    controlDependenceMap[&*BB2].insert(&*BB1);
                                }
                            }

                        }
                    }
                }
            }
            printControlDependenceMap(controlDependenceMap);
        }


        void checkFastReachabilityUsingLLVM(Module &M)
        {

        }

        void printLineNumbers(Module &M)
        {
            for (Module::iterator F = M.begin(); F != M.end(); F++)
            {
                for (Function::iterator BB = F->begin(); BB != F->end(); BB++)
                {
                    for (BasicBlock::iterator inst = BB->begin(); inst != BB->end(); inst++)
                    {
                        if (DILocation* debugLoc = inst->getDebugLoc())
                        {
                            unsigned int lineNo = debugLoc->getLine();
                            inst->dump();
                            errs() << " : " << lineNo;
                        }
                    }
                }
            }

        }


        bool isALoopHeader(BasicBlock* BB)
        {

        }

        //need to be careful for loops here because header will have tail also as a predecessor 
        //but still any variable def coming from preheader is valid 
        //since the entry point of the loop will have to go through the pre-headers
        //multi-entry loops don't exist in code? -- Assumption
        std::set<Value*> intersectionOfPredOutSets(BasicBlock* BB, std::map< BasicBlock*, std::set<Value*> > soundVar_Out)
        {
            bool possibleHeader = false;
            if (!BB->getSinglePredecessor())
            {
                possibleHeader = true;
            }

            std::map<Value*, unsigned int> varCount;
            std::set<Value*> returnSet;
            unsigned int numValidPreds = 0;



            for (auto predIt = pred_begin(BB); predIt != pred_end(BB); predIt++)
            {
                BasicBlock* predBB = *predIt;
                if (possibleHeader)
                {
                    //This is not good; everytime I need to find whether block A is reachable from Block B
                    //I have to remember to clear the visited (global) vector
                    //As I was forgetting to do this, it was a bug for 4-5 days which wasted my time
                    //I will fix the reachable to be independent of global vector, perhaps make it an arg?
                    visited.clear();
                    if (isreachable(BB, predBB))
                    {
                        //predBB->BB was a backedge and BB is a header
                        //defs inside the loop should not matter because first use inside header will be unsound
                        //consider only the other predecessor(pre-header)
                        continue;
                    }
                }

                numValidPreds++;
                for (auto var : soundVar_Out[predBB])
                {
                    varCount[var]++;
                }
            }
            for (auto it : varCount)
            {
                if (it.second == numValidPreds)
                    returnSet.insert(it.first);
            }
            return returnSet;
        }

        void addInSetToOutSet(std::set<Value*> soundVar_In_Of_BB, std::set<Value*> &soundVar_Out_Of_BB)
        {
            for (auto i : soundVar_In_Of_BB)
            {
                soundVar_Out_Of_BB.insert(i);
            }
        }


        //To find out unsound vars, we establish reaching definitions first
        //To get reaching definitions in cases of loops in the input program, 
        //I need to identify the final OUT sets of every block
        //To get the final OUT sets, I need to iteratively populate the OUT sets of blocks until 
        //the OUT sets stop changing. Why?
        //Because the back edge will add  its OUT sets into the header's IN set again 
        //which will consequently change the header's successors (which may be both inside
        // and outside of the loop)
        //To know whether the OUT sets got fixed, we need to keep a prevOUT sets of all blocks and newOUT sets of all blocks
        //And compare even if one of the block's OUT set has changed
        void printUnsoundVarUses(Module &M)
        {
            std::map<BasicBlock*, std::set<Value*> > soundVar_In;
            std::map<BasicBlock*, std::set<Value*> > soundVar_Out;
            std::map<BasicBlock*, std::set<Value*> > soundVar_Def; //needed?
            std::map<BasicBlock*, std::set<Value*> > soundVar_Declared; //needed?
            std::map < Value*, std::set<BasicBlock*> > used;
            std::map<BasicBlock*, std::set<Value*> > prev_Out;
            bool changed = true;
            while (changed)
            {
                changed = false;
                prev_Out = soundVar_Out;
                soundVar_Out.clear();
                //first parse to store the def and use information of every var and block
                for (Module::iterator F = M.begin(); F != M.end(); F++)
                {
                    if (F->isDeclaration()) continue;

                    for (Function::iterator BB = F->begin(); BB != F->end(); BB++)
                    {
                        soundVar_In[&*BB] = intersectionOfPredOutSets(&*BB, soundVar_Out);
                        //soundVar_Out[&*BB] = soundVar_In[&*BB]; //this is wrong, need to add both
                        addInSetToOutSet(soundVar_In[&*BB], soundVar_Out[&*BB]);
                        for (BasicBlock::iterator inst = BB->begin(); inst != BB->end(); inst++)
                        {
                            if (LoadInst *LI = dyn_cast<LoadInst>(&*inst))
                            {//variable used
                                Value* var = LI->getPointerOperand();
                                Value* newVar = LI;
                                used[var].insert(&*BB);
                                soundVar_Out[&*BB].insert(newVar);
                            }
                            else if (StoreInst *SI = dyn_cast<StoreInst>(&*inst))
                            {
                                soundVar_Out[&*BB].insert(SI->getPointerOperand());
                                soundVar_Def[&*BB].insert(SI->getPointerOperand());
                            }
                            else if (AllocaInst *AI = dyn_cast<AllocaInst>(&*inst))
                            {
                                soundVar_Declared[&*BB].insert(AI); //AI inst pointer itself is the var's Value*
                            }
                        }

                        if (soundVar_Out[&*BB] != prev_Out[&*BB])
                            changed = true;
                    }
                }

                //second step is to identify the reaching definitions and populate the INsets
                //must use dominance information?
                // In set of Block will be intersection of Out sets of predecessors
                /*for (Module::iterator F = M.begin(); F != M.end(); F++)
                {
                for (Function::iterator BB = F->begin(); BB != F->end(); BB++)
                {
                soundVar_In[&*BB] = intersectionOfPredOutSets(&*BB, soundVar_Out);
                }
                }*/
                printINSet(soundVar_In);
                printOUTSet(soundVar_Out);
            }

            printVarUses(used);

            printINSet(soundVar_In);
            printOUTSet(soundVar_Out);


            for (Module::iterator F = M.begin(); F != M.end(); F++)
            {
                for (Function::iterator BB = F->begin(); BB != F->end(); BB++)
                {
                    for (BasicBlock::iterator inst = BB->begin(); inst != BB->end(); inst++)
                    {
                        if (LoadInst *LI = dyn_cast<LoadInst>(&*inst))
                        {
                            if (soundVar_Out[&*BB].find(LI->getPointerOperand()) == soundVar_Out[&*BB].end())
                            {

                                errs() << "Unsound var " << LI->getPointerOperand()->getName() << "used in line ";
                                if (DILocation* debugLoc = LI->getDebugLoc())
                                {
                                    unsigned int lineNo = debugLoc->getLine();
                                    //inst->dump();
                                    errs() << " : " << lineNo;
                                }
                            }
                        }
                    }
                }
            }

        }


        
        ////This is an implementation of the constant propagation pass. 
        ////It identifies new constant variables generated as a result of previous iteration and 
        //// propagates them in the current iteration
        ////It keeps doing that until we can not propagata any more constants
                
        ////    Tested with this input:
        ////              int main() {
        ////                  int c;
        ////                  c = 5;

        ////                  int a, b, sum;
        ////                  a = c;
        ////                  b = a;
        ////                  sum = a + b;
        ////                  return 0;
        ////              }


        ////    Obtained output IR:
        ////        define i32 @main() #0 {
        ////            % 1 = alloca i32, align 4
        ////            % c = alloca i32, align 4
        ////            % a = alloca i32, align 4
        ////            % b = alloca i32, align 4
        ////            % sum = alloca i32, align 4
        ////            % 2 = load i32, i32 5, align 4
        ////            % 3 = load i32, i32 5, align 4
        ////            % 4 = add nsw i32 % 2, % 3
        ////            store i32 % 4, i32* %sum, align 4
        ////            ret i32 0
        ////}
        
        void propagateConstIteratively(Module &M)
        {
            std::map<llvm::Instruction*, llvm::ConstantInt*> constants;
            std::set<Instruction*> toBeDeleted;

            bool changed = true;

            while (changed)
            {
                for (auto &F : M)
                {
                    llvm::StringRef n = "main";
                    if (F.getName() != n) continue;
                    for (auto &B : F)
                    {
                        for (auto &I : B)
                        {
                            if (StoreInst *SI = dyn_cast<StoreInst>(&I))
                            {
                                if (llvm::ConstantInt *CI = dyn_cast<llvm::ConstantInt>(SI->getValueOperand()))
                                {
                                    constants.insert(std::make_pair(dyn_cast<Instruction>(SI->getPointerOperand()), CI));
                                }
                            }
                            if (LoadInst *LI = dyn_cast<LoadInst>(&I))
                            {
                                if (llvm::ConstantInt *CI = dyn_cast<llvm::ConstantInt>(LI->getPointerOperand()))
                                {
                                    constants.insert(std::make_pair(dyn_cast<Instruction>(LI), CI));
                                }
                            }

                        }
                    }
                }

                bool foundCont = false;

                for (auto &F : M)
                {
                    llvm::StringRef n = "main";
                    if (F.getName() != n) continue;
                    for (auto &B : F)
                    {

                        for (auto &I : B)
                        {
                            if (LoadInst *LI = dyn_cast<LoadInst>(&I))
                            {
                                llvm::Value* loadFrom = LI->getPointerOperand();
                                if (llvm::ConstantInt *CI = dyn_cast<llvm::ConstantInt>(loadFrom))
                                {
                                    toBeDeleted.insert(LI);
                                }
                                if (constants.find(dyn_cast<Instruction>(loadFrom)) != constants.end())
                                {//found the use of a constant
                                    LI->setOperand(0, constants[static_cast<Instruction*>(loadFrom)]);

                                    foundCont = true;
                                }
                            }
                            if (StoreInst *SI = dyn_cast<StoreInst>(&I))
                            {
                                llvm::Value* storeWhat = SI->getValueOperand();
                                if (llvm::ConstantInt *CI = dyn_cast<llvm::ConstantInt>(storeWhat))
                                {
                                    toBeDeleted.insert(SI);
                                }
                                else
                                {
                                    if (constants.find(dyn_cast<Instruction>(storeWhat)) != constants.end())
                                    {
                                        SI->setOperand(0, constants[static_cast<Instruction*>(storeWhat)]);

                                        foundCont = true;
                                    }
                                }
                            }
                        }
                    }
                }
               
                for (auto itr : toBeDeleted)
                {
                    if(itr->use_empty())
                        itr->eraseFromParent();
                }


                if (foundCont)
                    changed = true;
                else
                    changed = false;

                constants.clear();
                toBeDeleted.clear();
            }



        }

        bool Hello::runOnModule(Module &M)
        {
            errs() << "Hello: ";
            //errs().write_escaped();
            //Adding and removing named metadata
            AddTestingMetaData(M);
            M.dump();
            RemoveTestingMetaData(M);
            M.dump();

            //Verifiying Basic passes
            unsigned int avgBBsInFuncs = findAverageNumBBsInFuncs(M);
            unsigned int avgCFGEdgesInFuncs = findAverageCFGEdgesInFuncs(M);
            unsigned int totalLoopCount = findNumberOfLoopsInModule(M);
            unsigned int outerLoopCountUsingLoopInfo = findLoopCountUsingLoopInfo(M);
            unsigned int totalLoopCountUsingLoopInfo = findTotalLoopCountUsingLoopInfo(M);
            unsigned int totalLoopExitingEdges = findTotalLoopExitingEdges(M);
            //finding multi entry loops using reachability
            unsigned int multipleEntryLoops = MrCompilerMultipleEntryLoops(M);
            assert(totalLoopCount == totalLoopCountUsingLoopInfo && "Total loops from both methods should be same");
            assert(totalLoopCount >= outerLoopCountUsingLoopInfo && "Num outer loops from LoopInfo cannot be greater than total Loops");
            assert(multipleEntryLoops >= totalLoopCountUsingLoopInfo && "MrCompiler's loop count can not be less");

            //first test reachability prints
            checkReachability(M);//tested

            checkFastReachabilityUsingLLVM(M);

            //do const propagation pass here

            //issue warning for uninitialized variables that get used. 
            //find how to check line number of the use
            printLineNumbers(M);
            //check control flow dependence between blocks
            dumpControlDependence(M);

            errs() << "\nAverage Num BBs" << avgBBsInFuncs;
            errs() << "\nAverage CFG edges" << avgCFGEdgesInFuncs;
            //errs() << "\nTotal number of loops " << totalLoopCount;
            errs() << "\n Total number of exiting edges " << totalLoopExitingEdges;
            errs() << "\n";
            printUnsoundVarUses(M);

            propagateConstIteratively(M);

            errs() << "\n";
            return true;
        }
    };
    // end of struct Hello

}
//end of namespace

char Hello::ID = 0;



INITIALIZE_PASS_BEGIN(Hello, "hello",
    "Hello World Pass", false, false)
    INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
    INITIALIZE_PASS_DEPENDENCY(PostDominatorTreeWrapperPass)
    INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
    INITIALIZE_PASS_END(Hello, "hello",
        "My hello pass", false, false)
