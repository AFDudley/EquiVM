import Benchmarks.Morpho.MetaMorphoV1_1.MulticallReady

/-! Source entry, checked result allocation, and loop initialization for multicall. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def multicallEntryFrame (evm : State) (imms : Store) (data : List Value) : Frame :=
  ⟨contract, ((((∅ : Store).insert "data" (.array data)).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).insert "results" (.array [])).insert
      cursorName (uint256Value ⟨128⟩), imms⟩

def multicallArrayFrame (evm : State) (imms : Store) (data : List Value) : Frame :=
  let f := multicallEntryFrame evm imms data
  { f with
    locals := (f.locals.insert cursorName
      (uint256Value (UInt256.ofNat (160 + 32 * data.length)))).insert "results"
        (.array (List.replicate data.length (.bytes ByteArray.empty))) }

theorem multicallEntryFrame_data (evm : State) (imms : Store) (data : List Value) :
    (multicallEntryFrame evm imms data).locals.get? "data" = some (.array data) := by
  simp only [multicallEntryFrame,
    store_get_ne _ _ (by decide : (cursorName == "data") = false),
    store_get_ne _ _ (by decide : ("results" == "data") = false),
    store_get_ne _ _ (by decide : ("__calldata" == "data") = false), store_get_self]

theorem multicallPrefixSource (evm : State) (imms : Store) (data : List Value)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hn : data.length ≤ solcMaxU64) :
    ABlock config evm ⟨contract, (∅ : Store).insert "data" (.array data), imms⟩
      allocatedMulticallTransition.body (multicallEntryFrame evm imms data)
      (allocatedMulticallTransition.body.drop 6) := by
  constructor
  intro result htail
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (evalExpr_newArrayNat (n := 0) (value := .bytes ByteArray.empty)
      (by simp only [evalExpr?, pure]; rfl)
      (by simp only [defaultValue?, pure]))) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨128⟩)
    (by simp only [evalExpr?, pure]; rfl)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) htail
  have hl : data.length < 2 ^ 64 := lt_of_le_of_lt hn (by decide)
  exact (naturalLtSource (b := 2 ^ 64) (evalLocalArrayLength (multicallEntryFrame_data evm imms data))
    (by simp only [evalExpr?, pure])).trans (by rw [decide_eq_true hl])

theorem multicallArraySizeSource {frame : Frame} {evm : State} {data : List Value}
    (hd : frame.locals.get? "data" = some (.array data)) (hn : data.length ≤ solcMaxU64) :
    evalExpr? config frame evm
      (.binary .add (.intLit 32) (.binary .mul (.intLit 32) multicallLength)) =
      .ok (uint256Value (UInt256.ofNat (32 + 32 * data.length))) := by
  simp only [multicallLength, evalExpr?, hd, readLocalPath?, bind, EvalResult.bind,
    pure, evalBinaryOp?, uint256Value, UInt256.toNat_ofNat_of_lt (wordArraySize_lt hn),
    Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

theorem multicallArrayPrefixSource (evm : State) (imms : Store) (data : List Value)
    (hn : data.length ≤ solcMaxU64) (hf : 160 + 32 * data.length < 2 ^ 64) :
    ABlock config evm (multicallEntryFrame evm imms data)
      (allocatedMulticallTransition.body.drop 6) (multicallArrayFrame evm imms data)
      [allocatedMulticallLoop, .return [.var "results"]] := by
  constructor
  intro result htail
  have hc := allocateCallReturns (cfg := config) (frame := multicallEntryFrame evm imms data)
    (evm := evm) (ptrExpr := .var cursorName) cursorName allocateFunction_lookup
    (evalLocalValue (store_get_self _ _ _))
    (multicallArraySizeSource (multicallEntryFrame_data evm imms data) hn)
    ((wordArrayAllocationFits ⟨128⟩ hn).mpr hf)
  rw [wordArrayNextCursor _ hn] at hc
  refine ExecBlock.consNormal hc ?_
  refine ExecBlock.consNormal (ExecStmt.assign ?_ (assignLocalValue (old := .array []) ?_)) htail
  · apply evalExpr_newArrayNat (n := data.length) ?_ (by simp only [defaultValue?, pure])
    apply evalLocalArrayLength
    rw [store_get_ne _ _ (by decide : (cursorName == "data") = false)]
    exact multicallEntryFrame_data evm imms data
  · simp only [multicallEntryFrame,
      store_get_ne _ _ (by decide : (cursorName == "results") = false), store_get_self]

theorem multicallArrayRevertsSource (evm : State) (imms : Store) (data : List Value)
    (hn : data.length ≤ solcMaxU64) (hf : ¬ 160 + 32 * data.length < 2 ^ 64) :
    ExecBlock config (multicallEntryFrame evm imms data) evm
      (allocatedMulticallTransition.body.drop 6) .reverted := by
  exact ExecBlock.consRevert (allocateCallReverts (cfg := config) cursorName
    allocateFunction_lookup (evalLocalValue (store_get_self _ _ _))
    (multicallArraySizeSource (multicallEntryFrame_data evm imms data) hn)
    (fun h ↦ hf ((wordArrayAllocationFits ⟨128⟩ hn).mp h)))

theorem multicallForInit (frame : Frame) (evm : State) :
    ExecBlock config frame evm
      [.letDecl "i" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0)]
      (.ok (multicallIndexFrame frame 0) evm) :=
  ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0)
    (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem multicallArrayFrame_ready (evm : State) (imms : Store) (data : List Value) :
    MulticallReady (multicallIndexFrame (multicallArrayFrame evm imms data) 0) imms data
      (List.replicate data.length ByteArray.empty) 0
      (UInt256.ofNat (160 + 32 * data.length)) := by
  constructor <;> simp only [multicallIndexFrame, multicallArrayFrame, multicallEntryFrame,
    List.map_replicate]
  all_goals repeat first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
