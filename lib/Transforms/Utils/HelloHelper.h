#pragma once
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

#include <map>
#include <set>

/*
This file has helper functions which don't depend on any llvm pass analysis usage
Hence they can be called independently by passing the appropriate argument and
would return the same result irrespective of which pass function calls them
*/

//For this Loop L, find total number of Subloops + their subloops + their subloops..and so on.
unsigned int getAllDepthSubLoopCount(const Loop* L)
{
    unsigned int loopCount = 0;
    for (auto SubLoop : L->getSubLoops())
    {
        loopCount++;
        loopCount += getAllDepthSubLoopCount(SubLoop);
    }
    return loopCount;
}

unsigned int getNumExitingEdgesFromLoop(const Loop *L)
{
    unsigned int numExitingEdges = 0;
    for (auto BB : L->getBlocks())
    {
        numExitingEdges += L->isLoopExiting(BB);
    }
    for (auto SubLoop : L->getSubLoops())
    {
        numExitingEdges += getNumExitingEdgesFromLoop(SubLoop);
    }
    return numExitingEdges;
}


void AddTestingMetaData(Module &M)
{
    auto root = M.getOrInsertNamedMetadata("Testing_MD");
    Metadata *newMD1 = (Metadata*)MDString::get(M.getContext(), "first metadata");
    Metadata* newMD2 = ValueAsMetadata::get(ConstantInt::get(Type::getInt32Ty(M.getContext()), 2));
    Metadata* v[] = { newMD1 ,newMD2 };
    MDNode* newNode = MDNode::get(M.getContext(), v);
    root->addOperand(newNode);
}

void RemoveTestingMetaData(Module &M)
{
    auto root = M.getNamedMetadata("Testing_MD");
    MDNode* node = root->getOperand(0);
    node->getOperand(node->getNumOperands() - 1)->dump();
    root->dropAllReferences();
}

unsigned int findAverageNumBBsInFuncs(const Module &M)
{
    unsigned int totalBBs = 0;
    for (auto F = M.begin(); F != M.end(); F++)
        totalBBs += F->size();
    return totalBBs / ((unsigned int)M.size());
}

unsigned int findAverageCFGEdgesInFuncs(const Module &M)
{
    unsigned int totalCFGEdges = 0;
    for (auto F = M.begin(); F != M.end(); F++)
        for (auto BB = F->begin(); BB != F->end(); BB++)
            totalCFGEdges += BB->getTerminator()->getNumSuccessors();
    return totalCFGEdges / M.size();
}


//just dumping the BB and vars used
void printVarUses(std::map<Value*, std::set<BasicBlock*> > used)
{
    for (auto it : used)
    {
        errs() << "Variable" << it.first->getName() << "used in : ";
        for (auto bb : it.second)
        {
            errs() << bb->getName() << " , ";
        }
        errs() << "\n";
    }
}



bool isreachable(const BasicBlock* from, const BasicBlock* to);
std::set<BasicBlock*> visited;


void checkReachability(const Function &F)
{
    for (auto &BB1 : F.getBasicBlockList())
    {
        for (auto &BB2 : F.getBasicBlockList())
        {
            visited.clear();
            if (isreachable(&BB1, &BB2))
            {
                errs() << BB2.getName() << "is reachable from " << BB1.getName() << "\n";
            }
        }
    }
}

bool isreachable(const BasicBlock* from, const BasicBlock* to)
{
    if (from == nullptr || to == nullptr)
        return false;
    if (from == to)
        return true;
    for (auto succ = succ_begin(from); succ != succ_end(from); succ++)
    {
        visited.insert(const_cast<BasicBlock*>(from));
        if (visited.find(const_cast<BasicBlock*>(*succ)) != visited.end())
            continue;
        if (isreachable(*succ, to))
            return true;
    }
    return false;
}

void checkReachability(const Module &M)
{
    for (const Function &F : M.getFunctionList())
    {
        checkReachability(F);
    }
}





//to print INSet or OUTSet
template<typename T>
void printSets(T soudvar_TSet)
{
    for (auto it : soudvar_TSet)
    {
        errs() << "\nBasic Block : " << it.first->getName();
        for (auto var : it.second)
        {
            errs() << var->getName() << ", ";
        }
    }
    errs() << "\n";
}

void printINSet(std::map<BasicBlock*, std::set<Value*> > soundVar_In)
{
    errs() << " \n Printing IN Sets: ";
    printSets(soundVar_In);
}

void printOUTSet(std::map<BasicBlock*, std::set<Value*> > soundVar_Out)
{
    errs() << " \n Printing OUT Sets: ";
    printSets(soundVar_Out);
}
