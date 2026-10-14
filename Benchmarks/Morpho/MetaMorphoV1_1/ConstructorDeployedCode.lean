import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorRuntimeMemory
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorFinalImmutables

/-! Identify the deployment words with the successful source constructor's immutable store. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem constructorRuntimeWords_key (w : Nat → UInt256) {i : Nat} (hi : i < 11) :
    constructorRuntimeWords w ((immutableReferences.map Prod.fst).getD i "") = w (128 + 32 * i) := by
  interval_cases i <;> rfl

theorem constructorDeployedCode (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) (strictOut : ByteArray) (w : Nat → UInt256)
    (hw : ∀ i, i < 11 → w (128 + 32 * i) = (constructorImmutableValues a ok out I strictOut).getD i ⟨0⟩) :
    immutableLayout.runtime metaMorphoV1_1Bytecode (constructorRuntimeWords w) =
      immutableLayout.deployed metaMorphoV1_1Bytecode (constructorFinalImms a ok out I strictOut) := by
  apply Layout.runtime_congr
  intro site hsite
  have hk : site.2.2 ∈ immutableReferences.map Prod.fst := by
    change site ∈ immutableReferences.flatMap
      (fun (name, sites) ↦ sites.map fun off ↦ (off, 32, name)) at hsite
    obtain ⟨⟨name, sites⟩, hentry, hsite⟩ := List.mem_flatMap.mp hsite
    obtain ⟨off, _, rfl⟩ := List.mem_map.mp hsite
    exact List.mem_map.mpr ⟨(name, sites), hentry, rfl⟩
  obtain ⟨i, hi, hkey⟩ := List.mem_iff_getElem.mp hk
  have hi' : i < 11 := hi
  have hget : (immutableReferences.map Prod.fst).getD i "" = site.2.2 :=
    (List.getD_eq_getElem _ _ hi).trans hkey
  rw [← hget, constructorRuntimeWords_key w hi']
  exact (hw i hi').trans (constructorFinalImms_word a ok out I strictOut hi').symm

end Benchmarks.Morpho.MetaMorphoV1_1
