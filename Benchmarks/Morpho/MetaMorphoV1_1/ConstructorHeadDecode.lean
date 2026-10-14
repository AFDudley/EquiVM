import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorArgumentWords

/-! Decode the three addresses, timelock and first dynamic offset in constructor memory. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorAddressReturn {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256} (addr : AccountAddress)
    (hstack : R.length + 5 ≤ 1024)
    (hret : (D_J metaMorphoV1_1CreationBytecode 0).contains ret = true)
    (hread : memLoad ptr mem = UInt256.ofNat addr.val)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨2643⟩
      (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ret
      (UInt256.ofNat addr.val :: R) mem aw' rdata σ k' C' := by
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := by native_decide
  have hclean : UInt256.land (UInt256.ofNat addr.val) solcAddrMask = UInt256.ofNat addr.val :=
    addressWord_val_clean addr
  have h1 := metaMorphoV1_1Creation_block_2643_fallthrough hstack
    (by rw [hread, hmask, hclean, u256_sub_self]; rfl) rd
  obtain ⟨aw', k', C', hd⟩ := metaMorphoV1_1Creation_block_2662_packed
    (by simp only [List.length_cons]; omega) hret h1
  refine ⟨aw', k', C', ?_⟩
  simpa only [metaMorphoV1_1Creation_block_2662_stack, hread] using hd

set_option maxRecDepth 2000 in
theorem constructorDecodeHead {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} (a : ConstructorArgs)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨44⟩
      [UInt256.ofNat (480 + a.encoded.length), ⟨480⟩]
      (constructorArgumentMemory a) aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨2690⟩
      [⟨672⟩, UInt256.ofNat (480 + a.encoded.length), ⟨118⟩, ⟨480⟩,
       UInt256.ofNat (480 + a.encoded.length), UInt256.ofNat a.owner.val,
       a.initialTimelock, UInt256.ofNat a.morpho.val, UInt256.ofNat a.asset.val]
      (constructorArgumentMemory a) aw' rdata σ k' C' := by
  have ho : memLoad ⟨480⟩ (constructorArgumentMemory a) = UInt256.ofNat a.owner.val :=
    constructorArgumentMemory_headWord a ⟨0, by decide⟩
  have hm : memLoad ⟨512⟩ (constructorArgumentMemory a) = UInt256.ofNat a.morpho.val :=
    constructorArgumentMemory_headWord a ⟨1, by decide⟩
  have ht : memLoad ⟨544⟩ (constructorArgumentMemory a) = a.initialTimelock :=
    constructorArgumentMemory_headWord a ⟨2, by decide⟩
  have ha : memLoad ⟨576⟩ (constructorArgumentMemory a) = UInt256.ofNat a.asset.val :=
    constructorArgumentMemory_headWord a ⟨3, by decide⟩
  have hn : memLoad ⟨608⟩ (constructorArgumentMemory a) = UInt256.ofNat 192 :=
    constructorArgumentMemory_headWord a ⟨4, by decide⟩
  have r1 := metaMorphoV1_1Creation_block_44 (by decide) (by native_decide) rd
  obtain ⟨aw2, k2, C2, r2⟩ := constructorAddressReturn a.owner
    (by simp) (by native_decide) ho r1
  have r3 := metaMorphoV1_1Creation_block_52 (by decide) (by native_decide) r2
  obtain ⟨aw4, k4, C4, r4⟩ := constructorAddressReturn a.morpho
    (by simp) (by native_decide) hm r3
  have r5 := metaMorphoV1_1Creation_block_65 (by decide) (by native_decide) r4
  obtain ⟨aw6, k6, C6, r6⟩ := constructorAddressReturn a.asset
    (by simp) (by native_decide) ha r5
  have ht' : memLoad ((⟨480⟩ : UInt256) + UInt256.ofNat 64) (constructorArgumentMemory a) =
      a.initialTimelock := ht
  simp only [ht'] at r6
  change RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨84⟩
    [UInt256.ofNat a.asset.val, UInt256.ofNat (480 + a.encoded.length),
     UInt256.ofNat a.owner.val, a.initialTimelock, UInt256.ofNat a.morpho.val, ⟨480⟩]
    (constructorArgumentMemory a) aw6 rdata σ k6 C6 at r6
  have hn' : memLoad ((⟨480⟩ : UInt256) + UInt256.ofNat 128) (constructorArgumentMemory a) =
      UInt256.ofNat 192 := hn
  have r7 := metaMorphoV1_1Creation_block_84_fallthrough (by decide)
    (by rw [hn']; native_decide) r6
  simp only [metaMorphoV1_1Creation_block_84_fallthrough_stack, hn'] at r7
  obtain ⟨aw8, k8, C8, r8⟩ := metaMorphoV1_1Creation_block_107_packed
    (by simp) (by native_decide) r7
  exact ⟨aw8, k8, C8, r8⟩

end Benchmarks.Morpho.MetaMorphoV1_1
