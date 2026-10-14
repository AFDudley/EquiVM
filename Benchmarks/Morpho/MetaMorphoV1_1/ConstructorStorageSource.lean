import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStorageHeader
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorLiteralSource
import Benchmarks.Morpho.MetaMorphoV1_1.StringStorageWrite

/-! The constructor's two initial empty-string assignments, including invalid headers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def constructorMetadataField (symbol : Bool) : Ident := if symbol then "_erc20Symbol" else "_erc20Name"

def constructorMetadataAssignment (symbol : Bool) : Stmt :=
  .assign .storage ⟨constructorMetadataField symbol, []⟩ (.bytesLit ByteArray.empty)

theorem constructorMetadataUnshadowed (a : ConstructorArgs) (cursors : List UInt256) (symbol : Bool) :
    (constructorInputFrame a cursors).locals.get? (constructorMetadataField symbol) = none := by
  induction cursors with
  | nil =>
    cases symbol <;> simp [constructorInputFrame, constructorFrame, constructorLocals,
      constructorMetadataField]
  | cons cursor cursors ih =>
    rw [constructorInputFrame, store_get_ne _ _ (by cases symbol <;> decide)]
    exact ih

theorem constructorMetadataResolve (a : ConstructorArgs) (cursors : List UInt256)
    (symbol : Bool) (evm : State) :
    resolveStorageRef? config (constructorInputFrame a cursors) evm
      ⟨constructorMetadataField symbol, []⟩ =
      .ok (⟨constructorMetadataField symbol, []⟩, .string) := by
  apply resolveStorageRef?_ok (constructorMetadataUnshadowed a cursors symbol)
  · simp [evalStorageRef, evalStorageRefSteps, bind, EvalResult.bind, pure]
  · rw [constructorInputFrame_contract]
    cases symbol <;> rfl

theorem constructorMetadataAssign (a : ConstructorArgs) (cursors : List UInt256)
    (symbol : Bool) (evm : State)
    (hvalid : storageStringValid (storageStringHeader evm (constructorMetadataSlot symbol))) :
    ExecStmt config (constructorInputFrame a cursors) evm (constructorMetadataAssignment symbol)
      (.ok (constructorInputFrame a cursors)
        (storageStringWriteState evm (constructorMetadataSlot symbol) ByteArray.empty)) := by
  apply ExecStmt.assign (value := .bytes ByteArray.empty) (by simp only [evalExpr?, pure])
  have hw := storageStringWriteAt (constructorMetadataField symbol) (constructorMetadataSlot symbol)
    evm ByteArray.empty (by cases symbol <;> rfl) hvalid
  simp only [assignStorageRef?, constructorMetadataResolve a cursors symbol evm, hw,
    EvalResult.bind, bind, pure]

theorem constructorMetadataAssignRevert (a : ConstructorArgs) (cursors : List UInt256)
    (symbol : Bool) (evm : State)
    (hbad : ¬ storageStringValid (storageStringHeader evm (constructorMetadataSlot symbol))) :
    ExecStmt config (constructorInputFrame a cursors) evm (constructorMetadataAssignment symbol)
      .reverted := by
  apply ExecStmt.assignStoreRevert (value := .bytes ByteArray.empty) (by simp only [evalExpr?, pure])
  have hw := storageStringWriteAtReverts (constructorMetadataField symbol) (constructorMetadataSlot symbol)
    evm ByteArray.empty (by cases symbol <;> rfl) hbad
  simp only [assignStorageRef?, constructorMetadataResolve a cursors symbol evm, hw,
    EvalResult.bind, bind]

theorem constructorInitialNameHeaderFailure {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : UInt256} {mem : ByteArray} {aw : UInt256} {k C : Nat}
    (a : ConstructorArgs)
    (hcode : I.code = metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray)
    (hbad : ¬ storageStringValid (solcSlotWord σ I ⟨3⟩))
    (hsource : ABlock config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (constructorFrame a) contract.ctor.body (constructorReadyFrame a) (contract.ctor.body.drop 8))
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨277⟩
      (UInt256.land (solcSlotWord σ I ⟨3⟩) ⟨1⟩ :: constructorMetadataPtr a.stringsEnd false ::
        storageStringLength (solcSlotWord σ I ⟨3⟩) :: ⟨0⟩ :: constructorMetadataTail a a.stringsEnd false)
      mem aw ByteArray.empty σ k C) :
    typedConstructorRefinementFor config contract a.values σ σ₀ g A I
      (immutableLayout.deployed metaMorphoV1_1Bytecode) := by
  apply constructorRefinementOfRevert hcode (constructorMetadataInvalid a a.stringsEnd false hbad rd)
  apply constructorSourceRevertOfPrefix a hsource
  exact ExecBlock.consRevert (constructorMetadataAssignRevert a _ false _ hbad)

end Benchmarks.Morpho.MetaMorphoV1_1
