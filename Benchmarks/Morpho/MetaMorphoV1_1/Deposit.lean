import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.DepositPublicSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.UintAddressCalldata
import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositEntry

/-!
# MetaMorphoV1_1 `deposit(uint256,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 7351; reach lemma `metaMorphoV1_1ReachDepositBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `deposit(uint256,address)`: the theorem `Correct.lean` routes selector 29 to. -/
theorem metaMorphoV1_1DepositBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 29)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 29) rfl hsel
  have hd : dispatchMsg contract I.calldata = some depositTransition := by
    apply metaMorphoV1_1Dispatch_deposit <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachDepositBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let assets := calldataWord I.calldata 4
  let receiver := AccountAddress.ofNat (calldataWord I.calldata 36).toNat
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 68 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus
        · have hdec : config.externalABI.decodeCalldata? ["assets", "receiver"]
              [abiUInt256, .elem .address] I.calldata =
              some (depositPublicLocals assets receiver) := by
            exact (decodeCalldata_uint256_address_result hlen hhi).trans (if_pos hcanon)
          have hreceiver : UInt256.ofNat receiver.toNat = calldataWord I.calldata 36 := by
            simpa only [receiver, keyValueToWord_address, Fin.toNat] using
              keyValueToWord_address_of_canonical _ hcanon
          have hpre := depositPublicPrefix evm (immStore v) assets receiver hwv hhi
          obtain ⟨k1, C1, h1⟩ := depositReachAccrual v (by simp) hwv hlen hhi hsize hcanon rd
          rcases accrueInterestSimulation v (by simp) hsize solcFreePtrMem_mload64
              (by decide) (by decide) (by rw [solcFreePtrMem_size]) SourceState.init
              (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1 with
            ⟨hbad, hrev⟩ | ⟨hstatic, hhalt⟩ |
              ⟨evm1, frame1, ptr1, mem1, out1, hperm, hs1, hacc,
                hhi1, hmono1, hfree1, _, hsize1, hzero1, aw2, k2, C2, h2⟩
          · exact hrev.reEquivExecutionRevert hcode hd hdec
              (ExecFuncBody.execBlockRevert (hpre.run (depositPublicAccrualReverts hbad)))
          · exact hhalt.reEquivStaticHalt hcode hd hdec
              (ExecFuncBody.execBlockStatic (hpre.run (depositPublicAccrualStatic hstatic)))
          · rw [← hreceiver] at h2
            rcases depositPublicSimulation (evm0 := evm) v (by simp) hs1 hperm hsize
                hfree1 hhi1 (by exact hmono1) hsize1 (hzero1 solcFreePtrMem_size)
                (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2 with
              ⟨hbad, hrev⟩ | ⟨evm2, final, mem2, out2, hs2, hbody, aw3, k3, C3, h3⟩
            · exact hrev.reEquivExecutionRevert hcode hd hdec
                (ExecFuncBody.execBlockRevert
                  (hpre.run (depositPublicAccrualContinue hacc hbad)))
            · exact (maxDepositEncodeReturn v (by simp) h3).reEquivExecutionGen hcode hd hdec
                (ExecFuncBody.execBlockRet (hpre.run (depositPublicAccrualContinue hacc hbody)))
                rfl (returnEquiv_of_encode (uint256ReturnEncoding _))
        · obtain ⟨k1, C1, h1⟩ := depositReachDecoder v (by simp) hwv hlen hhi hsize rd
          exact (decodeAddressAt36Revert v (by simp) hcanon h1).reEquivDecodingFailed
            hcode hd ((decodeCalldata_uint256_address_result hlen hhi).trans (if_neg hcanon))
      · have hrev := depositRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_64 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_scalar_none_huge (by decide) rfl (Nat.le_of_not_gt hhi))
    · have hrev := depositRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_64 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd
        (decodeCalldata_scalar_none_short (by decide) (by simpa using Nat.lt_of_not_ge hlen))
  · exact dispatchedRevert hcode hd (depositRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
