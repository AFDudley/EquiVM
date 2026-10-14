import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorEntry

/-! Source-side argument allocation and its initial failure case. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def constructorLocals (a : ConstructorArgs) : Store :=
  Std.HashMap.ofList
    [("owner", .address a.owner), ("morpho", .address a.morpho),
     ("initialTimelock", .int (Int.ofNat a.initialTimelock.toNat)),
     ("assetAddress", .address a.asset), ("__name", .bytes a.name),
     ("__symbol", .bytes a.symbol)]

def constructorFrame (a : ConstructorArgs) : Frame :=
  ⟨contract, constructorLocals a, initialImmutables contract⟩

theorem constructorLocals_bind (a : ConstructorArgs) :
    constructorLocals a = Std.HashMap.ofList
      (List.zip (contract.ctor.params.map Param.name) a.values) := rfl

theorem constructorFrame_name (a : ConstructorArgs) :
    (constructorFrame a).locals.get? "__name" = some (.bytes a.name) := by
  apply Std.HashMap.getElem?_ofList_of_mem (k := "__name") (by decide)
  · simp
  · simp

theorem constructorFrame_symbol (a : ConstructorArgs) :
    (constructorFrame a).locals.get? "__symbol" = some (.bytes a.symbol) := by
  apply Std.HashMap.getElem?_ofList_of_mem (k := "__symbol") (by decide)
  · simp
  · simp

namespace SourceMemory

-- LIBRARY CANDIDATE: evaluate the ABI padded size of a byte array in a local variable.
theorem constructorPaddedLengthSource {cfg : Config} {frame : Frame} {evm : State}
    {param : Ident} {bytes : ByteArray}
    (hget : frame.locals.get? param = some (.bytes bytes)) :
    evalExpr? cfg frame evm (constructorPaddedLengthExpr param) =
      .ok (.int (Int.ofNat (paddedSize bytes.size))) := by
  simp only [constructorPaddedLengthExpr, evalExpr?, hget, readLocalPath?, evalBinaryOp?,
    pure, bind, EvalResult.bind, show (32 : Int) ≠ 0 by decide, if_false]
  simp only [paddedSize, Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add,
    Int.natCast_ediv]
  rfl

theorem constructorEncodedLengthSource (a : ConstructorArgs) (evm : State) :
    evalExpr? config (constructorFrame a) evm constructorEncodedLengthExpr =
      .ok (.int (Int.ofNat a.encoded.length)) := by
  rw [constructorEncodedLengthExpr, a.encoded_length]
  apply naturalAddSource
  · apply naturalAddSource
    · simp only [evalExpr?, pure]; rfl
    · exact constructorPaddedLengthSource (constructorFrame_name a)
  · exact constructorPaddedLengthSource (constructorFrame_symbol a)

theorem constructorInitialAllocationSource {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : UInt256} (a : ConstructorArgs)
    (hv : I.weiValue = ⟨0⟩) (hsize : a.encoded.length < UInt256.size)
    (hfit : ¬ allocationFits ⟨480⟩ (UInt256.ofNat a.encoded.length)) :
    steleCtorExec config contract a.values σ σ₀ g A I .reverted := by
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hlen : evalExpr? config (constructorFrame a) evm constructorEncodedLengthExpr =
      .ok (uint256Value (UInt256.ofNat a.encoded.length)) := by
    simpa only [uint256Value, UInt256.toNat_ofNat_of_lt hsize] using
      constructorEncodedLengthSource a evm
  have hcall := allocateCallReverts (cfg := config) (frame := constructorFrame a)
    (evm := evm) (ptr := ⟨480⟩) (size := UInt256.ofNat a.encoded.length)
    (ptrExpr := .intLit 480) (sizeExpr := constructorEncodedLengthExpr)
    cursorName allocateFunction_lookup
    (by simp only [evalExpr?, pure, uint256Value]; rfl) hlen hfit
  refine .intro (evmState := evm) (argsStore := constructorLocals a)
    rfl a.values_length (constructorLocals_bind a) (.execBlockRevert ?_)
  change ExecBlock config (constructorFrame a) evm
    (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
      .internalCall allocateFunction.name [.intLit 480, constructorEncodedLengthExpr]
        cursorName :: _) .reverted
  apply ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hv))
  exact ExecBlock.consRevert hcall

end SourceMemory

theorem constructorInitialAllocationFailure {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : UInt256} (a : ConstructorArgs)
    (hcode : I.code = metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray)
    (hv : I.weiValue = ⟨0⟩) (hsize : I.code.size < UInt256.size)
    (hfit : ¬ SourceMemory.allocationFits ⟨480⟩ (UInt256.ofNat a.encoded.length)) :
    typedConstructorRefinementFor config contract a.values σ σ₀ g A I
      (immutableLayout.deployed metaMorphoV1_1Bytecode) := by
  apply constructorRefinementOfRevert hcode
    (constructorInitialAllocationRevert hcode hv hsize (by
      simpa only [List.size_toByteArray] using hfit))
  apply SourceMemory.constructorInitialAllocationSource a hv ?_ hfit
  simp only [hcode, ByteArray.size_append, List.size_toByteArray] at hsize
  omega

end Benchmarks.Morpho.MetaMorphoV1_1
