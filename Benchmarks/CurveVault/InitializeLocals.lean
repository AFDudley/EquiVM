import Benchmarks.CurveVault.Common

open Solm ABI Ethereum
namespace Benchmarks.CurveVault

def vaultInitializeLocals (amm controller token collateral : UInt256) : Store :=
  ((((∅ : Store).insert "_amm_" (.address (AccountAddress.ofNat amm.toNat))).insert
    "_controller_" (.address (AccountAddress.ofNat controller.toNat))).insert
    "_borrowed_token_" (.address (AccountAddress.ofNat token.toNat))).insert
    "_collateral_token_" (.address (AccountAddress.ofNat collateral.toNat))

end Benchmarks.CurveVault
