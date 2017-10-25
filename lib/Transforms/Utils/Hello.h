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
