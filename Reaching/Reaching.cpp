// ===- Reaching.cpp Implements reaching definitions pass -----------------------------===//
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/CFG.h" // For iterating over predecessors of a basic block
#include "llvm/Analysis/Dataflow.h"
#include <map>
#include <set>

using namespace llvm;

#define DEBUG_TYPE "reaching"


namespace {
  class valueType : public std::set<Instruction*>{
    public:
      valueType operator ^ (valueType a){
        valueType result(a);
        result.insert(this->begin(),this->end());
        return result;
      }
  };

  class ReachingDFA : public dataFlow<valueType>{
    private:
      void construct_transfer_function_objects(Function& F){
        for(auto&& bb : F.getBasicBlockList()){
          transferFunction<valueType> tf;
          BasicBlock* bb_pointer = &bb;
          tf.basic_block = bb_pointer;
          tf.is_forward = is_forward;
          tf.blockToTransferFunctionsMap = &allTransferFunctions;
          tf.blockTransferFunction = [bb_pointer](valueType in){
            valueType out(in);
            for(auto inst = bb_pointer->begin(); inst != bb_pointer->end(); ++inst){
              if(!inst->getType()->isVoidTy())
                out.insert(&*inst);
            }
            return out;
          };
          allTransferFunctions[bb_pointer] = tf;
        }
      }
    public:
      ReachingDFA(Function& F){
        is_forward = true;
        construct_transfer_function_objects(F);
      }
      std::map<Instruction*, valueType> propagate_to_instructions(Function& F, std::map<std::pair<BasicBlock*,bool>, valueType> bbFixedPoint){
        std::map<Instruction*, valueType> instructionFixedPoint;
        for(auto&& bb: F.getBasicBlockList()){
          valueType current = bbFixedPoint[std::make_pair(&bb,true)];
          for(auto inst = bb.begin(); inst != bb.end(); ++inst){
            instructionFixedPoint[&*inst] = current;
            current.insert(&*inst);
          }
        }
        return instructionFixedPoint;
      }
  };


  struct Reaching : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    Reaching() : FunctionPass(ID) {}
    bool runOnFunction(Function &F) override {
      ReachingDFA rd(F);
      std::map<std::pair<BasicBlock*, bool>, valueType> previous;
      for(auto& bb: F.getBasicBlockList()){
        valueType set_in;
        valueType set_out;
        previous[std::make_pair(&bb,true)] = set_in;
        previous[std::make_pair(&bb,false)] = set_out;
      }
      F.print(outs());
      rd.run_dataflow(F, previous);
      std::map<Instruction*, valueType> instructionFixedPoint = rd.propagate_to_instructions(F, previous);
      outs() << "Reacing Defs. Analysis\n";
      for(auto&& bb : F.getBasicBlockList()){
        bb.printAsOperand(outs());
        outs() << ":\n";
        for(auto inst = bb.begin(); inst != bb.end(); ++inst){
          valueType reachingDefs = instructionFixedPoint[&*inst];
          outs() << "{";
          std::for_each(reachingDefs.begin(), reachingDefs.end(), [](Value* v){v->printAsOperand(outs()); outs() << ", ";});
          outs() << "}\n";
          inst->print(outs());
          outs() << "\n";
        }
        outs() << "\n\n";
      }
      return false;
    }
  };
}

char Reaching::ID = 0;
static RegisterPass<Reaching> X("reaching", "Reaching Definitions pass");