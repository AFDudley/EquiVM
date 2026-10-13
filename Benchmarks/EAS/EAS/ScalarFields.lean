import Benchmarks.EAS.EAS.PackedSlice
import Reasoning.ExternalCall
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: an ordered scalar prefix of a Solidity struct write.
structure ScalarFieldWrite where
  name : Ident
  loc : StorageLoc
  value : Value
  word : UInt256
  valueWord : valueToWord value = some word
  byteAligned : loc.bitOffset = none

def ScalarFieldWrite.apply (f : ScalarFieldWrite) (evm : EVM.State) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner f.loc.slot
    (packedSliceWord (EVM.storageLoad evm evm.executionEnv.codeOwner f.loc.slot) f.word
      (8*f.loc.offset.val) (8*f.loc.size.val))

def ScalarFieldWrite.accounts (f : ScalarFieldWrite) (σ : AccountMap) (ee : ExecutionEnv) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ f.loc.slot
    (packedSliceWord (solcSlotWord σ ee f.loc.slot) f.word (8*f.loc.offset.val) (8*f.loc.size.val))

def scalarFieldTypes (fs : List ScalarFieldWrite) : List (Ident × StorageType) :=
  fs.map fun f => (f.name,.elem f.loc.type)
def scalarFieldValues (fs : List ScalarFieldWrite) : List (Ident × Value) :=
  fs.map fun f => (f.name,f.value)
def writeScalarFields : List ScalarFieldWrite → EVM.State → EVM.State
  | [],evm => evm
  | f::fs,evm => writeScalarFields fs (f.apply evm)
def writeScalarAccounts : List ScalarFieldWrite → AccountMap → ExecutionEnv → AccountMap
  | [],σ,_ => σ
  | f::fs,σ,ee => writeScalarAccounts fs (f.accounts σ ee) ee

theorem writeScalarFields_sourceState {s0 ee σ evm} (hs : SourceState s0 ee σ evm) (fs : List ScalarFieldWrite) :
    SourceState s0 ee (writeScalarAccounts fs σ ee) (writeScalarFields fs evm) := by
  induction fs generalizing evm σ with
  | nil => exact hs
  | cons f fs ih => exact ih (hs.readModifyWrite f.loc.slot
      (fun old => packedSliceWord old f.word (8*f.loc.offset.val) (8*f.loc.size.val)))

theorem solidityWriteFields_scalarPrefix (layout : StorageLayout) (er : EvaledStorageRef)
    (fs : List ScalarFieldWrite) (evm : EVM.State) (tailTypes : List (Ident × StorageType)) (tailValues : List (Ident × Value))
    (hloc : ∀ f ∈ fs, layout {er with steps := er.steps ++ [.field f.name]} = some (.leaf f.loc)) :
    solidityWriteFields? layout evm er (scalarFieldTypes fs ++ tailTypes) (scalarFieldValues fs ++ tailValues) =
      solidityWriteFields? layout (writeScalarFields fs evm) er tailTypes tailValues := by
  induction fs generalizing evm with
  | nil => rfl
  | cons f fs ih =>
    simp only [scalarFieldTypes,scalarFieldValues,List.map_cons,List.cons_append]
    rw [solidityWriteFields?,if_pos rfl,solidityWriteStorage?]
    simp only [solidityLeafLoc?_of_leaf (hloc f (List.mem_cons_self)),EvalResult.ofOption,EvalResult.bind,bind,
      storageLocStore_packedSlice evm f.loc f.value f.word f.byteAligned f.valueWord]
    exact ih (f.apply evm) (fun x hx => hloc x (List.mem_cons_of_mem f hx))

end Benchmarks.EAS.EAS
