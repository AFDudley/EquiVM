import Benchmarks.CurveVault.Common

open Ethereum
namespace Benchmarks.CurveVault

inductive VaultFlow where
  | deposit | mint | withdraw | redeem

def VaultFlow.controllerOffset : VaultFlow → Nat
  | .deposit | .mint => 608
  | .withdraw | .redeem => 704

def VaultFlow.callOffset : VaultFlow → Nat
  | .deposit | .mint => 704
  | .withdraw | .redeem => 736

def VaultFlow.saveEntry : VaultFlow → Nat
  | .deposit => 2771
  | .mint => 3775
  | .withdraw => 4664
  | .redeem => 5569

def VaultFlow.saveCall : VaultFlow → Nat
  | .deposit => 2804
  | .mint => 3808
  | .withdraw => 4697
  | .redeem => 5602

def VaultFlow.saveNext : VaultFlow → Nat
  | .deposit => 2816
  | .mint => 3820
  | .withdraw => 4709
  | .redeem => 5614

def VaultFlow.hookEntry : VaultFlow → Nat
  | .deposit => 2666
  | .mint => 3669
  | .withdraw => 4578
  | .redeem => 5474

def VaultFlow.hookCall : VaultFlow → Nat
  | .deposit => 2706
  | .mint => 3710
  | .withdraw => 4618
  | .redeem => 5522

def VaultFlow.hookNext : VaultFlow → Nat
  | .deposit => 2718
  | .mint => 3722
  | .withdraw => 4630
  | .redeem => 5534

def VaultFlow.hookName : VaultFlow → Stele.Ident
  | .deposit | .mint => "on_borrowed_token_transfer_in"
  | .withdraw | .redeem => "on_borrowed_token_transfer_out"

def VaultFlow.hookSelector : VaultFlow → UInt256
  | .deposit | .mint => UInt256.ofNat 2762502178
  | .withdraw | .redeem => UInt256.ofNat 1065911937

def VaultFlow.tokenNext : VaultFlow → Nat
  | .deposit => 2749
  | .mint => 3754
  | .withdraw => 4664
  | .redeem => 5569

end Benchmarks.CurveVault
