import Benchmarks.Morpho.MetaMorphoV1_1.ERC4626WithdrawSource
import Benchmarks.Morpho.MetaMorphoV1_1.AccrueInterestSimulation

/-! Source-state transport for the two storage updates used by vault withdrawals. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem burnBalanceSourceState {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (owner : AccountAddress) (shares : UInt256) :
    SourceState s0 I (burnBalanceState evm owner shares).accountMap
      (burnBalanceState evm owner shares) :=
  sourceStateStoreSelf (sourceStateStoreSelf hs (balanceSlot owner)
    (UInt256.sub (balanceWord evm owner) shares)) ⟨2⟩
    (UInt256.sub (Stele.EVM.storageLoad (balanceDebitState evm owner shares)
      (balanceDebitState evm owner shares).executionEnv.codeOwner ⟨2⟩) shares)

theorem spendAllowanceSourceState {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (owner caller : AccountAddress) (shares : UInt256) :
    SourceState s0 I (spendAllowanceState evm owner caller shares).accountMap
      (spendAllowanceState evm owner caller shares) := by
  unfold spendAllowanceState
  split
  · exact ⟨hs.world, hs.env, rfl⟩
  · exact sourceStateStoreSelf hs (approvalSlot owner caller)
      (UInt256.sub (allowanceWord evm owner caller) shares)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
