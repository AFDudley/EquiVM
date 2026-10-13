import Benchmarks.CurveVault.CreditSource

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultCreditLocals (isDeposit : Bool) (receiver : AccountAddress) (input : UInt256) : Store :=
  ((∅ : Store).insert "_receiver" (.address receiver)).insert
    (if isDeposit then "_assets" else "_shares") (.int (Int.ofNat input.toNat))

end Benchmarks.CurveVault
