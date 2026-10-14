import Benchmarks.EAS.EAS.RevokeControl
import Benchmarks.EAS.EAS.Time
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

structure RevokeSite where
  kind : RevokeKind
  schema : UInt256
  data : UInt256
  revoker : AccountAddress
  available : UInt256
  last : Bool
  ret : UInt256
  schemaPtr : UInt256
  records : UInt256
  values : UInt256
  length : Nat

def revokeGuardRest (site : RevokeSite) (ee : ExecutionEnv) (R : List UInt256) : List UInt256 :=
  match site.kind with
  | .single => [UInt256.ofNat site.length,easTimeWord ee,site.schemaPtr,site.records,site.values,site.available,site.ret,site.data] ++ R
  | .many => [UInt256.ofNat site.length,site.schemaPtr,site.records,site.values,site.available,site.last.toUInt256,site.ret,site.data] ++ R
def revokeLoopStack (site : RevokeSite) (ee : ExecutionEnv) (idx : UInt256) (R : List UInt256) : List UInt256 :=
  idx::revokeGuardTail site.kind site.schema (UInt256.ofNat site.revoker.val) (revokeGuardRest site ee R)
def RevokeKind.loopPC : RevokeKind → UInt256 | .single => ⟨12257⟩ | .many => ⟨12903⟩
def RevokeKind.copyReturnPC : RevokeKind → UInt256 | .single => ⟨12585⟩ | .many => ⟨13144⟩
def revokedTopic : UInt256 := ⟨112711859747844749551422265703931386029553912681258923828578905266377347036693⟩
def revokeCopySaved (site : RevokeSite) (ee : ExecutionEnv) (request idx word : UInt256) (R : List UInt256) : List UInt256 :=
  match site.kind with
  | .single => [site.records,idx,⟨12595⟩,site.values,dbSlot word,⟨4⟩,solcAddrMask,⟨32⟩,revokedTopic,
      request,UInt256.ofNat site.revoker.val,dbSlot word+⟨1⟩,idx,⟨1⟩,UInt256.ofNat site.revoker.val,site.schema,
      UInt256.ofNat site.length,easTimeWord ee,site.schemaPtr,site.records,site.values,site.available,site.ret,site.data] ++ R
  | .many => [dbSlot word,request,idx,⟨1⟩,site.schema,UInt256.ofNat site.revoker.val,UInt256.ofNat site.length,
      site.schemaPtr,site.records,site.values,site.available,site.last.toUInt256,site.ret,site.data] ++ R

end Benchmarks.EAS.EAS
