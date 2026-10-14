import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.RedeemPublicSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.RedeemEntry
import Benchmarks.Morpho.MetaMorphoV1_1.UintTwoAddressesCalldata
import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositEntry

/-!
# MetaMorphoV1_1 `redeem(uint256,address,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2947; reach lemma `metaMorphoV1_1ReachRedeemBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory metaMorphoV1_1Blocks

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `redeem(uint256,address,address)`: the theorem `Correct.lean` routes selector 56 to. -/
theorem metaMorphoV1_1RedeemBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 56)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 56) rfl hsel
  have hd : dispatchMsg contract I.calldata = some redeemTransition := by
    apply metaMorphoV1_1Dispatch_redeem <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachRedeemBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let shares := calldataWord I.calldata 4
  let receiver := AccountAddress.ofNat (calldataWord I.calldata 36).toNat
  let owner := AccountAddress.ofNat (calldataWord I.calldata 68).toNat
  by_cases hwv : I.weiValue = ⟨0⟩
  · obtain ⟨k0, C0, h0⟩ := redeemReachDecoder v (by simp) hwv rd
    by_cases hlen : 100 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · rcases decodeUintTwoAddresses v (by simp) hlen hhi hsize
          (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h0 with
          ⟨hnc1, hrev⟩ | ⟨hc1, hnc2, hrev⟩ | ⟨hc1, hc2, k1, C1, h1⟩
        · exact hrev.reEquivDecodingFailed hcode hd
            ((decodeCalldata_uint256_address_address_result hlen hhi).trans (if_neg hnc1))
        · exact hrev.reEquivDecodingFailed hcode hd
            ((decodeCalldata_uint256_address_address_result hlen hhi).trans
              ((if_pos hc1).trans (if_neg hnc2)))
        · have hdec : config.externalABI.decodeCalldata? ["shares", "receiver", "owner"]
              [abiUInt256, .elem .address, .elem .address] I.calldata =
              some (redeemPublicLocals shares receiver owner) := by
            exact (decodeCalldata_uint256_address_address_result hlen hhi).trans
              ((if_pos hc1).trans (if_pos hc2))
          have hreceiver : UInt256.ofNat receiver.toNat = calldataWord I.calldata 36 := by
            simpa only [receiver, keyValueToWord_address, Fin.toNat] using
              keyValueToWord_address_of_canonical _ hc1
          have howner : UInt256.ofNat owner.toNat = calldataWord I.calldata 68 := by
            simpa only [owner, keyValueToWord_address, Fin.toNat] using
              keyValueToWord_address_of_canonical _ hc2
          have hpre := redeemPublicPrefix evm (immStore v) shares receiver owner hwv hhi
          have h2 := metaMorphoV1_1_block_2966 (immWords := wordsOf (immStore v))
            (by simp) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
          rcases accrueInterestSimulation v (by simp) hsize solcFreePtrMem_mload64
              (by decide) (by decide) (by rw [solcFreePtrMem_size]) SourceState.init
              (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2 with
            ⟨hbad, hrev⟩ | ⟨hstatic, hhalt⟩ |
              ⟨evm1, frame1, ptr1, mem1, out1, hperm, hs1, hacc,
                hhi1, hmono1, hfree1, _, hsize1, hzero1, aw3, k3, C3, h3⟩
          · exact hrev.reEquivExecutionRevert hcode hd hdec
              (ExecFuncBody.execBlockRevert (hpre.run (redeemPublicAccrualReverts hbad)))
          · exact hhalt.reEquivStaticHalt hcode hd hdec
              (ExecFuncBody.execBlockStatic (hpre.run (redeemPublicAccrualStatic hstatic)))
          · rw [← hreceiver, ← howner] at h3
            rcases redeemPublicSimulation (evm0 := evm) v (by simp) hs1 hperm hsize
                hfree1 hhi1 (by exact hmono1) hsize1 (hzero1 solcFreePtrMem_size)
                (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3 with
              ⟨hbad, hrev⟩ | ⟨evm2, final, mem2, out2, hs2, hbody, aw4, k4, C4, h4⟩
            · exact hrev.reEquivExecutionRevert hcode hd hdec
                (ExecFuncBody.execBlockRevert
                  (hpre.run (redeemPublicAccrualContinue hacc hbad)))
            · exact (maxDepositEncodeReturn v (by simp) h4).reEquivExecutionGen hcode hd hdec
                (ExecFuncBody.execBlockRet (hpre.run (redeemPublicAccrualContinue hacc hbody)))
                rfl (returnEquiv_of_encode (uint256ReturnEncoding _))
      · have hrev := decodeUintTwoAddressesRevertLength v (by simp) (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge (Nat.le_of_not_gt hhi) hsize (by decide)]
          decide) h0
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_scalar_none_huge (by decide) rfl (Nat.le_of_not_gt hhi))
    · have hrev := decodeUintTwoAddressesRevertLength v (by simp) (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort hsz (by exact Nat.lt_of_not_ge hlen) hsize (by decide)]
        decide) h0
      exact hrev.reEquivDecodingFailed hcode hd
        (decodeCalldata_scalar_none_short (by decide) (by simpa using Nat.lt_of_not_ge hlen))
  · exact dispatchedRevert hcode hd (redeemRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
