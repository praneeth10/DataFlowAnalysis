#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/CFG.h" // For iterating over predecessors of a basic block
#include <map>
#include <set>

using namespace llvm;

template<typename T>
class transferFunction{
  public: 
    bool has_phi_nodes;
    bool is_forward;
    std::map<BasicBlock*, std::function<T(T)>> transferMap; // One for each of the predecessors if phi nodes exist
    std::map<BasicBlock*, transferFunction>* blockToTransferFunctionsMap;  // Pointer to map of BasicBlock* to transferFunction*
    std::function<T(T)> blockTransferFunction;
    BasicBlock* basic_block;
    T top;
    transferFunction(){
      has_phi_nodes = false;
    };

    transferFunction(bool is_forward, std::map<BasicBlock*, std::function<T(T)>> transferMap, std::function<T(T)> blockTransferFunction, BasicBlock* basic_block) : has_phi_nodes(true), is_forward(is_forward), transferMap(transferMap), blockTransferFunction(blockTransferFunction), basic_block(basic_block) {};

    transferFunction(bool is_forward, std::map<BasicBlock*, std::function<T(T)>> blockTransferFunction, BasicBlock* basic_block) : has_phi_nodes(false), is_forward(is_forward), blockTransferFunction(blockTransferFunction), basic_block(basic_block) {};

    std::pair<T,T> forward_pass(std::map<std::pair<BasicBlock*,bool>, T>& current){
      T meet_answer = top;
      if(has_phi_nodes){
        for(BasicBlock* pred : predecessors(basic_block)){
          meet_answer = meet_answer^transferMap[pred](current[std::make_pair(pred, false)]);
        }
      }
      else{
        for(BasicBlock* pred : predecessors(basic_block)){
          meet_answer = meet_answer^current[std::make_pair(pred, false)];
        }
      }
      return std::make_pair(meet_answer, blockTransferFunction(meet_answer));
    }

    std::pair<T,T> backward_pass(std::map<std::pair<BasicBlock*,bool>, T>& current){
      T meet_answer = top;
      for(BasicBlock* succ : successors(basic_block)){
        if((*blockToTransferFunctionsMap)[succ].has_phi_nodes){
          meet_answer = meet_answer ^ (*blockToTransferFunctionsMap)[succ].transferMap[basic_block](current[std::make_pair(succ,true)]);
        }
        else{
          meet_answer = meet_answer ^ current[std::make_pair(succ, true)];
        }
      }
      return std::make_pair(blockTransferFunction(meet_answer), meet_answer);
    }

    std::pair<T,T> pass(std::map<std::pair<BasicBlock*,bool>, T>& current){
      if(is_forward){
        return forward_pass(current);
      }
      return backward_pass(current);
    }
};

template <typename T>
class dataFlow{
  public:
    bool is_forward;
    T top;
    std::map<BasicBlock*,transferFunction<T>> allTransferFunctions;
    void run_dataflow(Function &F, std::map<std::pair<BasicBlock*, bool>, T>& previous){
      Function::BasicBlockListType& basicBlockList = F.getBasicBlockList();
      bool modified = true;
      int count = 0;
      std::map<std::pair<BasicBlock*,bool>,T> next = previous;
      while(modified){
        errs() << "Pass number: " << count++ << "\n";
        modified = false;
        for(auto& bb: basicBlockList){
          std::pair<T,T> after_pass = allTransferFunctions[&bb].pass(next);
          std::pair<BasicBlock*, bool> bb_in = std::make_pair(&bb, true);
          std::pair<BasicBlock*, bool> bb_out = std::make_pair(&bb, false);
          next[bb_in] = after_pass.first;
          next[bb_out] = after_pass.second;
          if(!modified && (previous[bb_in] != next[bb_in] || previous[bb_out] != next[bb_out])){
            modified = true;
          }
        }
        previous = next;
      }
    }
};
