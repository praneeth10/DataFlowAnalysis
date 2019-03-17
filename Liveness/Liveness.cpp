// ===- Liveness.cpp Implements liveness pass -----------------------------===//
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

#define DEBUG_TYPE "liveness"
namespace {
  class valueType : public std::set<Value*>{
    public:
      valueType operator ^ (valueType b){
        valueType result(b);
        result.insert(this->begin(),this->end());
        return result;
      }
  };

  class LivenessDFA : public dataFlow<valueType>{
    private:
      void construct_transfer_function_objects(Function& F){
        for(auto&& bb : F.getBasicBlockList()){
          transferFunction<valueType> tf;
          BasicBlock* bb_pointer = &bb;
          tf.basic_block = bb_pointer;
          tf.is_forward = false;
          tf.blockToTransferFunctionsMap = &allTransferFunctions;
          tf.blockTransferFunction = [bb_pointer](valueType out){
            valueType in(out);
            for(auto inst = bb_pointer->rbegin(); inst != bb_pointer->rend(); ++inst){
              if(isa<PHINode>(&*inst)){
                break;
              }
              in.erase((Value*)&*inst);
              for(const Use& u : inst->operands()){
                Value* val = u.get();
                if(isa<Instruction>(val) || isa<Argument>(val)){
                  in.insert(val);
                }
              }
            } 
            return in;
          };
          if(isa<PHINode>(&*(bb_pointer->begin()))){
            // Has phi nodes
            tf.has_phi_nodes = true;
            auto last_phi_inst = bb_pointer->begin();
            while(isa<PHINode>(&*last_phi_inst)){
              ++last_phi_inst;
            }
            --last_phi_inst; // This will be the last PHI instruction
            for(BasicBlock* pred : predecessors(&bb)){
              tf.transferMap[pred] = [bb_pointer,last_phi_inst, pred](valueType out){
                valueType in(out);
                auto bbiphi = last_phi_inst;
                for(bbiphi = last_phi_inst; bbiphi != bb_pointer->begin(); --bbiphi){
                  PHINode* phi = dyn_cast<PHINode>(&*bbiphi);
                  in.erase((Value*)&*bbiphi);
                  for(unsigned int idx = 0; idx < phi->getNumIncomingValues(); idx++){
                    if(phi->getIncomingBlock(idx) == pred){
                      Value* val = phi->getIncomingValue(idx);
                      if(isa<Instruction>(val) || isa<Argument>(val)){
                        in.insert(val);
                      }
                      break;
                    }
                  }
                }
                PHINode* phi = dyn_cast<PHINode>(&*bbiphi);
                in.erase((Value*)&*bbiphi);
                for(unsigned int idx = 0; idx < phi->getNumIncomingValues(); idx++){
                  if(phi->getIncomingBlock(idx) == pred){
                    Value* val = phi->getIncomingValue(idx);
                    if(isa<Instruction>(val) || isa<Argument>(val)){
                      in.insert(val);
                    }
                    break;
                  }
                }              
                return in;
              };   
            }
          }
          allTransferFunctions[&bb] = tf;
        }
      }

    public:
      LivenessDFA(Function &F){
        is_forward = false;
        construct_transfer_function_objects(F);
      }

      std::map<Instruction*,valueType> propagate_to_instructions(Function& F, std::map<std::pair<BasicBlock*, bool>, valueType>& bbFixedPoint){
        std::map<Instruction*, valueType> instructionFixedPoint;
        for(auto&& bb : F.getBasicBlockList()){
          valueType current = bbFixedPoint[std::make_pair(&bb,false)];
          for(auto inst = bb.rbegin(); inst != bb.rend(); ++inst){
            if(isa<PHINode>(&*inst)){
              break;
            }
            current.erase((Value *)&*inst);
            for(const Use& u: inst->operands()){
              Value* used = u.get();
              if(isa<Argument>(used) || isa<Instruction>(used)){
                current.insert(used);
              }
            }
            instructionFixedPoint[&*inst] = current;
          }
        }
        return instructionFixedPoint;
      }
  };

  // Hello - The first implementation, without getAnalysisUsage.
  struct Liveness : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    Liveness() : FunctionPass(ID) {}
    // typedef std::pair<BasicBlock*, bool> BasicBlockEdge;
    // typedef std::set<Value*> latticeType;
    // latticeType top;
    // dataFlow<latticeType>* liveness = new dataFlow<latticeType>(false, top);
    // latticeType construct_transfer_function(const BasicBlock* bb, latticeType x){
    //   latticeType result = x;
    //   for(auto bbi = bb->rbegin(); bbi != bb->rend(); ++bbi){
    //       result.erase((Value*)&*bbi);
    //       for(const Use& u: bbi->operands()){
    //         result.insert(u.get());
    //       }
    //   }
    //   return result;
    // }

    // latticeType meet_function(latticeType a, latticeType b){
    //   latticeType result(a);
    //   result.insert(b.begin(), b.end());
    //   return result;
    // }

    bool runOnFunction(Function &F) override {
      LivenessDFA ld(F);
      std::map<std::pair<BasicBlock*, bool>, valueType> previous;
      for(auto& bb: F.getBasicBlockList()){
        valueType set_in;
        valueType set_out;
        previous[std::make_pair(&bb,true)] = set_in;
        previous[std::make_pair(&bb,false)] = set_out;
      }
      F.print(outs());
      ld.run_dataflow(F, previous);
      std::map<Instruction*, valueType> instructionFixedPoint = ld.propagate_to_instructions(F, previous);
      outs() << "Live Variable Analysis\n";
      for(auto&& bb : F.getBasicBlockList()){
        bb.printAsOperand(outs());
        outs() << ":\n";
        for(auto inst = bb.begin(); inst != bb.end(); ++inst){
          if(!isa<PHINode>(&*inst)){
            valueType liveVars = instructionFixedPoint[&*inst];
            outs() << "{";
            std::for_each(liveVars.begin(), liveVars.end(), [](Value* v){v->printAsOperand(outs()); outs() << ", ";});
            outs() << "}\n";
          }
          inst->print(outs());
          outs() << "\n";
        }
        outs() << "\n\n";
      }


      // for(auto&& bb: F.getBasicBlockList()){
      //   outs() << "Live In Variables\n";
      //   valueType live_in = previous[std::make_pair(&bb,true)];
      //   valueType live_out = previous[std::make_pair(&bb, false)];
      //   std::for_each(live_in.begin(), live_in.end(), [](Value* v){v->printAsOperand(outs()); outs() << " ";});
      //   outs() << "\n";
      //   for(auto inst = bb.begin(); inst != bb.end(); ++inst){
      //     inst->print(outs());
      //     outs() << "\n";
      //   }
      //   outs() << "Live Out Variables\n";
      //   std::for_each(live_out.begin(), live_out.end(), [](Value* v){v->printAsOperand(outs()); outs() << " ";});
      //   outs() << "\n";
      // }
      // ++HelloCounter;
      // errs() << "Hello: ";
      // errs().write_escaped(F.getName()) << '\n';
      // return false;
      
      // Function::BasicBlockListType& basicBlockList = F.getBasicBlockList();
      // std::map<std::pair<BasicBlock*, bool>, latticeType> previous;
      // std::map<BasicBlock*,std::function<latticeType(latticeType)>> transferFunction;
      // for(auto& bb: basicBlockList){
      //   const BasicBlock* bb_pointer = &bb;
      //   latticeType set_in;
      //   latticeType set_out;
      //   std::pair<BasicBlock*, bool> bb_in_init(&bb, true);
      //   std::pair<BasicBlock*, bool> bb_out_init(&bb, false);
      //   previous[bb_in_init] = set_in;
      //   previous[bb_out_init] = set_out;
      //   transferFunction[&bb] = [this, bb_pointer](latticeType par){return construct_transfer_function(bb_pointer, par);};
      // }
      // latticeType empty;
      // std::function<latticeType(latticeType, latticeType)> meet = [this](latticeType a, latticeType b){return meet_function(a,b);};
      // liveness->run_dataflow(F, previous, transferFunction, meet);
      // for(auto& bb: basicBlockList){
      //   // outs << bb << "\n";
      //   std::pair<BasicBlock*, bool> bb_out(&bb, false);
      //   for(auto a : previous[bb_out]){
      //     outs << *a << "\n";
      //   }
      // }
      return false;
    }
  };
}

char Liveness::ID = 0;
static RegisterPass<Liveness> X("liveness", "Liveness Pass");

// namespace {
//   // Hello2 - The second implementation with getAnalysisUsage implemented.
//   struct Hello2 : public FunctionPass {
//     static char ID; // Pass identification, replacement for typeid
//     Hello2() : FunctionPass(ID) {}

//     bool runOnFunction(Function &F) override {
//       ++HelloCounter;
//       errs() << "Hello: ";
//       errs().write_escaped(F.getName()) << '\n';
//       return false;
//     }

//     // We don't modify the program, so we preserve all analyses.
//     void getAnalysisUsage(AnalysisUsage &AU) const override {
//       AU.setPreservesAll();
//     }
//   };
// }

// char Hello2::ID = 0;
// static RegisterPass<Hello2>
// Y("hello2", "Hello World Pass (with getAnalysisUsage implemented)");
