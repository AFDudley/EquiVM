import Benchmarks.CurveVault.SupplyArguments
import Benchmarks.CurveVault.ApproveArguments
import Benchmarks.CurveVault.RuntimeBlocks_016
import Benchmarks.CurveVault.RuntimeBlocks_018
import Benchmarks.CurveVault.RuntimeBlocks_020

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

inductive VaultAllowanceSpendFlow where
  | transferFrom | withdraw | redeem

namespace VaultAllowanceSpendFlow
def ownerOffset : VaultAllowanceSpendFlow → Nat
  | .transferFrom => 192 | .withdraw | .redeem => 608
def allowanceOffset : VaultAllowanceSpendFlow → Nat
  | .transferFrom => 256 | .withdraw => 704 | .redeem => 640
def entry : VaultAllowanceSpendFlow → Nat
  | .transferFrom => 5804 | .withdraw => 4506 | .redeem => 5179
def prepared : VaultAllowanceSpendFlow → Nat
  | .transferFrom => 5831 | .withdraw => 4535 | .redeem => 5207
def next : VaultAllowanceSpendFlow → Nat
  | .transferFrom => 5845 | .withdraw => 4549 | .redeem => 5221
def amount (flow : VaultAllowanceSpendFlow) (I : ExecutionEnv) (mem : ByteArray) : UInt256 :=
  match flow with
  | .transferFrom => calldataWord I.calldata 68
  | .withdraw => memLoad (UInt256.ofNat 672) mem
  | .redeem => calldataWord I.calldata 4
end VaultAllowanceSpendFlow

end Benchmarks.CurveVault
