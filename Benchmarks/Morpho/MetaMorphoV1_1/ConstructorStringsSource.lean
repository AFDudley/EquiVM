import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStringsRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorPrefixSource

/-! Match both constructor string allocations with their source continuations. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

theorem constructorNameSourcePrefix (a : ConstructorArgs) (evm : State)
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound : 23666 + a.encoded.length < UInt256.size)
    (hsmall : a.argumentEnd < 2 ^ 64) (hname : a.nameEnd < 2 ^ 64) :
    ABlock config evm (constructorFrame a) contract.ctor.body
      (constructorInputFrame a [UInt256.ofNat a.nameEnd, UInt256.ofNat a.argumentEnd])
      (contract.ctor.body.drop 3) := by
  have hn := (a.string_sizes_small hsmall).1
  have hsize : 32 + paddedSize a.name.size < UInt256.size := by
    have hp : paddedSize a.name.size ≤ a.name.size + 31 := by unfold paddedSize; omega
    change _ < 2 ^ 256; omega
  have hcall := constructorStringCallReturns a evm (UInt256.ofNat a.argumentEnd) [] false
    hsize ((a.nameAllocationFits hsmall).mpr hname)
  change ExecStmt config (constructorInputFrame a [UInt256.ofNat a.argumentEnd]) evm
    (.internalCall allocateFunction.name
      [.var cursorName, .binary .add (.intLit 32) (constructorPaddedLengthExpr "__name")]
      cursorName)
    (.ok (constructorInputFrame a
      [nextCursor (UInt256.ofNat a.argumentEnd) (UInt256.ofNat (32 + paddedSize a.name.size)),
        UInt256.ofNat a.argumentEnd]) evm) at hcall
  rw [stringAllocationCursor _ _ hn] at hcall
  constructor
  intro result htail
  apply (constructorInitialAllocationPrefix a evm hv hbound
    ((constructorFirstAllocation_iff a hbound).mpr hsmall)).run
  exact ExecBlock.consNormal hcall htail

theorem constructorStringsSourcePrefix (a : ConstructorArgs) (evm : State)
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound : 23666 + a.encoded.length < UInt256.size)
    (hsmall : a.argumentEnd < 2 ^ 64) (hname : a.nameEnd < 2 ^ 64)
    (hsymbol : a.stringsEnd < 2 ^ 64) :
    ABlock config evm (constructorFrame a) contract.ctor.body
      (constructorInputFrame a [UInt256.ofNat a.stringsEnd,
        UInt256.ofNat a.nameEnd, UInt256.ofNat a.argumentEnd])
      (contract.ctor.body.drop 4) := by
  have hs := (a.string_sizes_small hsmall).2
  have hsize : 32 + paddedSize a.symbol.size < UInt256.size := by
    have hp : paddedSize a.symbol.size ≤ a.symbol.size + 31 := by unfold paddedSize; omega
    change _ < 2 ^ 256; omega
  have hcall := constructorStringCallReturns a evm (UInt256.ofNat a.nameEnd)
    [UInt256.ofNat a.argumentEnd] true hsize ((a.symbolAllocationFits hsmall hname).mpr hsymbol)
  change ExecStmt config
    (constructorInputFrame a [UInt256.ofNat a.nameEnd, UInt256.ofNat a.argumentEnd]) evm
    (.internalCall allocateFunction.name
      [.var cursorName, .binary .add (.intLit 32) (constructorPaddedLengthExpr "__symbol")]
      cursorName)
    (.ok (constructorInputFrame a
      [nextCursor (UInt256.ofNat a.nameEnd) (UInt256.ofNat (32 + paddedSize a.symbol.size)),
        UInt256.ofNat a.nameEnd, UInt256.ofNat a.argumentEnd]) evm) at hcall
  rw [stringAllocationCursor _ _ hs] at hcall
  constructor
  intro result htail
  apply (constructorNameSourcePrefix a evm hv hbound hsmall hname).run
  exact ExecBlock.consNormal hcall htail

theorem constructorNameAllocationFailure {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : UInt256} {aw : UInt256} {k C : Nat} (a : ConstructorArgs)
    (hcode : I.code = metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray)
    (hv : I.weiValue = ⟨0⟩) (hbound : 23666 + a.encoded.length < UInt256.size)
    (hsmall : a.argumentEnd < 2 ^ 64) (hname : ¬ a.nameEnd < 2 ^ 64)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2690⟩
      [⟨672⟩, UInt256.ofNat a.argumentEnd, ⟨118⟩, ⟨480⟩, UInt256.ofNat a.argumentEnd,
        UInt256.ofNat a.owner.val, a.initialTimelock, UInt256.ofNat a.morpho.val,
        UInt256.ofNat a.asset.val] (constructorArgumentMemory a) aw ByteArray.empty σ k C) :
    typedConstructorRefinementFor config contract a.values σ σ₀ g A I
      (immutableLayout.deployed metaMorphoV1_1Bytecode) := by
  apply constructorRefinementOfRevert hcode (constructorNameRevert a hsmall hname rd)
  apply constructorSourceRevertOfPrefix a (constructorInitialAllocationPrefix a _ hv hbound
    ((constructorFirstAllocation_iff a hbound).mpr hsmall))
  exact ExecBlock.consRevert (constructorStringCallReverts a _
    (UInt256.ofNat a.argumentEnd) [] false
    (by have hn := (a.string_sizes_small hsmall).1
        have hp : paddedSize a.name.size ≤ a.name.size + 31 := by unfold paddedSize; omega
        change 32 + paddedSize a.name.size < 2 ^ 256; omega)
    (fun h => hname ((a.nameAllocationFits hsmall).mp h)))

theorem constructorSymbolAllocationFailure {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : UInt256} {aw : UInt256} {k C : Nat} (a : ConstructorArgs)
    (hcode : I.code = metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray)
    (hv : I.weiValue = ⟨0⟩) (hbound : 23666 + a.encoded.length < UInt256.size)
    (hsmall : a.argumentEnd < 2 ^ 64) (hname : a.nameEnd < 2 ^ 64)
    (hsymbol : ¬ a.stringsEnd < 2 ^ 64)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2690⟩
      [UInt256.ofNat (704 + paddedSize a.name.size), UInt256.ofNat a.argumentEnd, ⟨150⟩,
        UInt256.ofNat a.argumentEnd, UInt256.ofNat a.owner.val, a.initialTimelock,
        UInt256.ofNat a.morpho.val, UInt256.ofNat a.asset.val]
      (constructorNameMemory a) aw ByteArray.empty σ k C) :
    typedConstructorRefinementFor config contract a.values σ σ₀ g A I
      (immutableLayout.deployed metaMorphoV1_1Bytecode) := by
  apply constructorRefinementOfRevert hcode
    (constructorSymbolRevert a hbound hsmall hname hsymbol rd)
  apply constructorSourceRevertOfPrefix a (constructorNameSourcePrefix a _ hv hbound hsmall hname)
  exact ExecBlock.consRevert (constructorStringCallReverts a _
    (UInt256.ofNat a.nameEnd) [UInt256.ofNat a.argumentEnd] true
    (by have hs := (a.string_sizes_small hsmall).2
        have hp : paddedSize a.symbol.size ≤ a.symbol.size + 31 := by unfold paddedSize; omega
        change 32 + paddedSize a.symbol.size < 2 ^ 256; omega)
    (fun h => hsymbol ((a.symbolAllocationFits hsmall hname).mp h)))

end Benchmarks.Morpho.MetaMorphoV1_1
