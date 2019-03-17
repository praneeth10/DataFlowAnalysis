// ===- Reaching.cpp Implements reaching definitions pass -----------------------------===//
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/CFG.h" // For iterating over predecessors of a basic block
#include "llvm/IR/InstIterator.h"
#include "llvm/Analysis/Dataflow.h"
#include <map>
#include <set>

using namespace llvm;

#define DEBUG_TYPE "reaching"



namespace {
  class valueType : public std::map<Value*,std::set<Value*>>{
    public:
      valueType(){}
      valueType(Function& F){
        std::set<Value*> empty;
        for(auto arg = F.arg_begin(); arg != F.arg_end(); ++arg){
          (*this)[(Value*)&*arg] = empty;
        }
        for(inst_iterator I = inst_begin(F); I != inst_end(F); ++I){
          (*this)[(Value *)&*I] = empty;
        }
      }
      void init(Function& F){
        std::set<Value*> empty;
        for(auto arg = F.arg_begin(); arg != F.arg_end(); ++arg){
          (*this)[(Value*)&*arg] = empty;
        }
        for(inst_iterator I = inst_begin(F); I != inst_end(F); ++I){
          (*this)[(Value *)&*I] = empty;
        }
      }
      valueType operator ^ (valueType a){
        valueType result(a);
        for(auto it = this->begin(); it != this->end(); ++it){
          if(result.find(it->first) == result.end()){
            result[it->first] = it->second;
          }else{
            result[it->first].insert(it->second.begin(),it->second.end());
          }
        }
        return result;
      }
  };

  class mayPoint : public dataFlow<valueType>{
    public:
      mayPoint(Function& F){
        top.init(F);
        is_forward = true;
        construct_transfer_function_objects(F);
      }

      std::map<Instruction*, valueType> propagateToInstructions(Function& F, std::map<std::pair<BasicBlock*,bool>,valueType> bb_fixed_point){
        std::map<Instruction*, valueType> inst_fixed_point;
        for(auto&& bb : F.getBasicBlockList()){
          valueType current = bb_fixed_point[std::make_pair(&bb, true)];
          for(auto inst = bb.begin(); inst != bb.end(); ++inst){
            current = instructionTransferFunction(&*inst, current);
            inst_fixed_point[&*inst] = current;
          }
        }
        return inst_fixed_point;
      }
    private:
      valueType instructionTransferFunction(Instruction* inst, valueType in){
        valueType result(in);
        std::set<Value*> points_to_set(in[(Value *)inst]);
        if(isa<AllocaInst>(inst)){
          points_to_set.insert((Value *)inst);
          result[(Value *)inst] = points_to_set;
          return result;
        }
        if(isa<BitCastInst>(inst)){
          BitCastInst* bit_cast_inst = dyn_cast<BitCastInst>(inst);
          Type* src_type = bit_cast_inst->getSrcTy();
          Type* dest_type = bit_cast_inst->getDestTy();
          if(isa<PointerType>(src_type) && isa<PointerType>(dest_type)){
            Value* used = bit_cast_inst->getOperand(0);
            std::set<Value*> used_points_to = in[used];
            result[(Value *)inst].insert(used_points_to.begin(),used_points_to.end());
          }
          return result;
        }
        if(isa<GetElementPtrInst>(inst)){
          GetElementPtrInst* get_elem_ptr_inst = dyn_cast<GetElementPtrInst>(inst);
          result[(Value*)inst].insert(get_elem_ptr_inst->getPointerOperand());
          return result;
        }
        if(isa<LoadInst>(inst)){
          if(!inst->getType()->isPointerTy()){
            return result;
          }
          Value* pointer_to_be_loaded = inst->getOperand(0);
          std::set<Value*> pointers_which_may_be_pointed_to = result[pointer_to_be_loaded];
          for(auto& pointer_which_may_be_pointed_to : pointers_which_may_be_pointed_to){
            result[(Value*)inst].insert(result[&*pointer_which_may_be_pointed_to].begin(),result[&*pointer_which_may_be_pointed_to].end());
          }
          return result;
        }
        if(isa<StoreInst>(inst)){
          StoreInst* store_inst = dyn_cast<StoreInst>(inst);
          if(!store_inst->getValueOperand()->getType()->isPointerTy()){
            return result;
          }
          std::set<Value*> value_operand_points_to = result[store_inst->getValueOperand()];
          std::set<Value*> pointer_operand_points_to = result[store_inst->getPointerOperand()];
          for(auto& it1 : pointer_operand_points_to){
            result[&*it1].insert(value_operand_points_to.begin(),value_operand_points_to.end());
          }
          return result;
        }
        if(isa<SelectInst>(inst)){
          if(!inst->getType()->isPointerTy()){
            return result;
          }
          SelectInst* select_inst = dyn_cast<SelectInst>(inst);
          std::set<Value*> true_pointer_points_to = result[select_inst->getTrueValue()];
          std::set<Value*> false_pointer_points_to = result[select_inst->getFalseValue()];
          result[(Value*)inst].insert(true_pointer_points_to.begin(),true_pointer_points_to.end());
          result[(Value*)inst].insert(false_pointer_points_to.begin(),false_pointer_points_to.end());
          return result;
        }
        if(isa<PHINode>(inst)){
          if(!inst->getType()->isPointerTy())
            return result;
          for(const Use& u: inst->operands()){
            result[(Value*)inst].insert(result[u.get()].begin(),result[u.get()].end());
          }
          return result;
        }
        return result;
      }
      void construct_transfer_function_objects(Function& F){
        for(auto&& bb : F.getBasicBlockList()){
          transferFunction<valueType> tf;
          BasicBlock* bb_pointer = &bb;
          tf.basic_block = bb_pointer;
          tf.is_forward = true;
          tf.blockToTransferFunctionsMap = &allTransferFunctions;
          tf.blockTransferFunction = [this,bb_pointer](valueType in){
            valueType out(in);
            for(auto inst = bb_pointer->begin(); inst != bb_pointer->end(); ++inst){
              out = this->instructionTransferFunction(&*inst,out);
            }
            return out;
          };
          allTransferFunctions[bb_pointer] = tf;
        }
      }
  };


  struct Maypoint : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    Maypoint() : FunctionPass(ID) {}
    bool runOnFunction(Function &F) override {
      mayPoint md(F);
      std::map<std::pair<BasicBlock*, bool>, valueType> previous;
      for(auto& bb : F.getBasicBlockList()){
        valueType in;
        valueType out;
        previous[std::make_pair(&bb,true)] = in;
        previous[std::make_pair(&bb,false)] = out;
      }
      md.run_dataflow(F,previous);
      std::map<Instruction*,valueType> instructionFixedPoint = md.propagateToInstructions(F,previous);
      for(auto&& bb : F.getBasicBlockList()){
        bb.printAsOperand(outs());
        outs() << ":\n";
        for(auto inst = bb.begin(); inst != bb.end(); ++inst){
          inst->print(outs());
          outs() << "\n";
          outs() << "{\n";
          valueType maypoint = instructionFixedPoint[&*inst];
          for(auto it = maypoint.begin(); it != maypoint.end(); ++it){
            if(it->second.size() == 0){
              continue;
            }
            it->first->printAsOperand(outs(),false);
            outs() << " : ";
            std::for_each(it->second.begin(),it->second.end(),[](Value* x){x->printAsOperand(outs(),false); outs() << ", ";});
            outs() <<"\n";
          }
          outs() << "}\n";
        }
        outs() << "\n\n";
      }
      return false;
    }
  };
}

char Maypoint::ID = 0;
static RegisterPass<Maypoint> X("Maypoint", "May point to analysis pass");