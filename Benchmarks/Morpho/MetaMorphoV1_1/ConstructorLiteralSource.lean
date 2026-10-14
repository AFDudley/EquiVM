import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStringsSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorLiteralRuntime

/-! The source semantics of the four literal reservations before constructor stores. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

namespace SourceMemory

def constructorLiteralAllocation : List Stmt :=
  [32, 32, 32, 64].map fun size =>
    .internalCall allocateFunction.name [.var cursorName, .intLit (Int.ofNat size)] cursorName

theorem constructorLiteralCallNatReturns (a : ConstructorArgs) (evm : State)
    (ptr : Nat) (cursors : List UInt256) (size : Nat)
    (halign : size % 32 = 0) (hsize : size + 31 < UInt256.size)
    (hfit : ptr + size < 2 ^ 64) :
    ExecStmt config (constructorInputFrame a (UInt256.ofNat ptr :: cursors)) evm
      (.internalCall allocateFunction.name [.var cursorName, .intLit (Int.ofNat size)] cursorName)
      (.ok (constructorInputFrame a
        (UInt256.ofNat (ptr + size) :: UInt256.ofNat ptr :: cursors)) evm) := by
  have hptr : ptr < UInt256.size := by change _ < 2 ^ 256; omega
  have h := constructorLiteralCallReturns a evm (UInt256.ofNat ptr) cursors size (by omega)
    ((alignedAllocationFitsNat ptr size hptr halign hsize).mpr hfit)
  rwa [alignedAllocationCursor ptr size halign hsize] at h

theorem constructorLiteralCallNatReverts (a : ConstructorArgs) (evm : State)
    (ptr : Nat) (cursors : List UInt256) (size : Nat) (hptr : ptr < UInt256.size)
    (halign : size % 32 = 0) (hsize : size + 31 < UInt256.size)
    (hfit : ¬ ptr + size < 2 ^ 64) :
    ExecStmt config (constructorInputFrame a (UInt256.ofNat ptr :: cursors)) evm
      (.internalCall allocateFunction.name [.var cursorName, .intLit (Int.ofNat size)] cursorName)
      .reverted :=
  constructorLiteralCallReverts a evm (UInt256.ofNat ptr) cursors size (by omega)
    (fun h => hfit ((alignedAllocationFitsNat ptr size hptr halign hsize).mp h))

theorem constructorLiteralSourceReturns (a : ConstructorArgs) (evm : State)
    (ptr : Nat) (cursors : List UInt256) (hfit : ptr + 160 < 2 ^ 64) :
    ExecBlock config (constructorInputFrame a (UInt256.ofNat ptr :: cursors)) evm
      constructorLiteralAllocation
      (.ok (constructorInputFrame a
        (UInt256.ofNat (ptr + 160) :: UInt256.ofNat (ptr + 96) :: UInt256.ofNat (ptr + 64) ::
          UInt256.ofNat (ptr + 32) :: UInt256.ofNat ptr :: cursors)) evm) := by
  have h1 := constructorLiteralCallNatReturns a evm ptr cursors 32 (by decide) (by decide) (by omega)
  have h2 := constructorLiteralCallNatReturns a evm (ptr + 32) (UInt256.ofNat ptr :: cursors)
    32 (by decide) (by decide) (by omega)
  rw [show ptr + 32 + 32 = ptr + 64 by omega] at h2
  have h3 := constructorLiteralCallNatReturns a evm (ptr + 64)
    (UInt256.ofNat (ptr + 32) :: UInt256.ofNat ptr :: cursors) 32 (by decide) (by decide) (by omega)
  rw [show ptr + 64 + 32 = ptr + 96 by omega] at h3
  have h4 := constructorLiteralCallNatReturns a evm (ptr + 96)
    (UInt256.ofNat (ptr + 64) :: UInt256.ofNat (ptr + 32) :: UInt256.ofNat ptr :: cursors)
    64 (by decide) (by decide) (by omega)
  rw [show ptr + 96 + 64 = ptr + 160 by omega] at h4
  exact .consNormal h1 (.consNormal h2 (.consNormal h3 (.consNormal h4 .nil)))

theorem constructorLiteralSourceReverts (a : ConstructorArgs) (evm : State)
    (ptr : Nat) (cursors : List UInt256) (hptr : ptr < 2 ^ 64)
    (hfit : ¬ ptr + 160 < 2 ^ 64) :
    ExecBlock config (constructorInputFrame a (UInt256.ofNat ptr :: cursors)) evm
      constructorLiteralAllocation .reverted := by
  by_cases h32 : ptr + 32 < 2 ^ 64
  · have h1 := constructorLiteralCallNatReturns a evm ptr cursors 32 (by decide) (by decide) h32
    apply ExecBlock.consNormal h1
    by_cases h64 : ptr + 64 < 2 ^ 64
    · have h2 := constructorLiteralCallNatReturns a evm (ptr + 32) (UInt256.ofNat ptr :: cursors)
        32 (by decide) (by decide) (by omega)
      rw [show ptr + 32 + 32 = ptr + 64 by omega] at h2
      apply ExecBlock.consNormal h2
      by_cases h96 : ptr + 96 < 2 ^ 64
      · have h3 := constructorLiteralCallNatReturns a evm (ptr + 64)
          (UInt256.ofNat (ptr + 32) :: UInt256.ofNat ptr :: cursors)
          32 (by decide) (by decide) (by omega)
        rw [show ptr + 64 + 32 = ptr + 96 by omega] at h3
        apply ExecBlock.consNormal h3
        exact ExecBlock.consRevert (constructorLiteralCallNatReverts a evm (ptr + 96)
          (UInt256.ofNat (ptr + 64) :: UInt256.ofNat (ptr + 32) :: UInt256.ofNat ptr :: cursors)
          64 (by change ptr + 96 < 2 ^ 256; omega) (by decide) (by decide) (by omega))
      · exact ExecBlock.consRevert (constructorLiteralCallNatReverts a evm (ptr + 64)
          (UInt256.ofNat (ptr + 32) :: UInt256.ofNat ptr :: cursors)
          32 (by change ptr + 64 < 2 ^ 256; omega) (by decide) (by decide) (by omega))
    · exact ExecBlock.consRevert (constructorLiteralCallNatReverts a evm (ptr + 32)
        (UInt256.ofNat ptr :: cursors)
        32 (by change ptr + 32 < 2 ^ 256; omega) (by decide) (by decide) (by omega))
  · exact ExecBlock.consRevert (constructorLiteralCallNatReverts a evm ptr cursors
      32 (by change ptr < 2 ^ 256; omega) (by decide) (by decide) h32)

end SourceMemory

def constructorReadyFrame (a : ConstructorArgs) : Frame :=
  constructorInputFrame a [UInt256.ofNat (a.stringsEnd + 160), UInt256.ofNat (a.stringsEnd + 96),
    UInt256.ofNat (a.stringsEnd + 64), UInt256.ofNat (a.stringsEnd + 32),
    UInt256.ofNat a.stringsEnd, UInt256.ofNat a.nameEnd, UInt256.ofNat a.argumentEnd]

theorem constructorLiteralSourcePrefix (a : ConstructorArgs) (evm : State)
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound : 23666 + a.encoded.length < UInt256.size)
    (hsmall : a.argumentEnd < 2 ^ 64) (hname : a.nameEnd < 2 ^ 64)
    (hsymbol : a.stringsEnd < 2 ^ 64) (hliteral : a.stringsEnd + 160 < 2 ^ 64) :
    ABlock config evm (constructorFrame a) contract.ctor.body
      (constructorReadyFrame a) (contract.ctor.body.drop 8) := by
  constructor
  intro result htail
  apply (constructorStringsSourcePrefix a evm hv hbound hsmall hname hsymbol).run
  change ExecBlock config _ evm (constructorLiteralAllocation ++ contract.ctor.body.drop 8) result
  exact execBlock_append (constructorLiteralSourceReturns a evm a.stringsEnd
    [UInt256.ofNat a.nameEnd, UInt256.ofNat a.argumentEnd] hliteral) htail

theorem constructorLiteralAllocationFailure {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : UInt256} (a : ConstructorArgs)
    (hcode : I.code = metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray)
    (hv : I.weiValue = ⟨0⟩) (hbound : 23666 + a.encoded.length < UInt256.size)
    (hsmall : a.argumentEnd < 2 ^ 64) (hname : a.nameEnd < 2 ^ 64)
    (hsymbol : a.stringsEnd < 2 ^ 64) (hliteral : ¬ a.stringsEnd + 160 < 2 ^ 64)
    (rd : RDrev (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I)) :
    typedConstructorRefinementFor config contract a.values σ σ₀ g A I
      (immutableLayout.deployed metaMorphoV1_1Bytecode) := by
  apply constructorRefinementOfRevert hcode rd
  apply constructorSourceRevertOfPrefix a
    (constructorStringsSourcePrefix a _ hv hbound hsmall hname hsymbol)
  change ExecBlock config _ _ (constructorLiteralAllocation ++ contract.ctor.body.drop 8) .reverted
  exact execBlock_append_term (constructorLiteralSourceReverts a _ a.stringsEnd
    [UInt256.ofNat a.nameEnd, UInt256.ofNat a.argumentEnd] hsymbol hliteral) (by intros; simp)

end Benchmarks.Morpho.MetaMorphoV1_1
