import Benchmarks.EAS.EAS.HeapStatic
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a public word-returning body paired with its complete EVM execution.
def PublicWordRun (cfg : Config) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : EVM.State)
    (frame : Frame) (evm : EVM.State) (body : Body) : Prop :=
  (∃ (frame' : Frame) (evm' : EVM.State) (σ' : AccountMap) (uid : UInt256),
    ExecBlock cfg frame evm body (.returned frame' evm' (some [wordBytes32Value uid])) ∧ SourceState s0 ee σ' evm' ∧ RDret code g s0 σ' uid.toByteArray) ∨
  (ExecBlock cfg frame evm body .reverted ∧ RDrev code g s0) ∨
  (ExecBlock cfg frame evm body .staticViolation ∧ RDstatic code g s0)

theorem PublicWordRun.prepend {cfg : Config} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 evm evm1 : EVM.State}
    {frame frame1 : Frame} {front suffix : Body}
    (h : PublicWordRun cfg code ee g s0 frame1 evm1 suffix)
    (hp : ExecBlock cfg frame evm front (.ok frame1 evm1)) : PublicWordRun cfg code ee g s0 frame evm (front++suffix) := by
  rcases h with ⟨f,e,σ,uid,hb,hs,hr⟩ | ⟨hb,hr⟩ | ⟨hb,hr⟩
  · exact Or.inl ⟨f,e,σ,uid,execBlock_append hp hb,hs,hr⟩
  · exact Or.inr (Or.inl ⟨execBlock_append hp hb,hr⟩)
  · exact Or.inr (Or.inr ⟨execBlock_append hp hb,hr⟩)

theorem PublicWordRun.revertPrefix {cfg : Config} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {frame : Frame} {front suffix : Body}
    (hp : ExecBlock cfg frame evm front .reverted) (hr : RDrev code g s0) :
    PublicWordRun cfg code ee g s0 frame evm (front++suffix) :=
  Or.inr (Or.inl ⟨execBlock_append_term hp (by intros; exact nofun),hr⟩)

theorem PublicWordRun.staticPrefix {cfg : Config} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {frame : Frame} {front suffix : Body}
    (hp : ExecBlock cfg frame evm front .staticViolation) (hr : RDstatic code g s0) :
    PublicWordRun cfg code ee g s0 frame evm (front++suffix) :=
  Or.inr (Or.inr ⟨execBlock_append_term hp (by intros; exact nofun),hr⟩)

end Benchmarks.EAS.EAS
