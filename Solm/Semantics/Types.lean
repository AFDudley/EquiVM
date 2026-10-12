import Solm.Storage
import Solm.Value
import ABI.Decode
import ABI.Vyper

/-! Shared execution context: configurable ABI operations, configuration, and frames. -/

namespace Solm

open ABI

structure ExternalCallABI where
  encode? : Ident -> List Value -> Option EVM.Bytes
  /-- Decode the return data of a named external call. -/
  decode? : Ident -> EVM.Bytes -> Option (List Value)
  /-- Decode the arguments of a selected transition from the full calldata, including its
      four-byte selector. Selector matching itself belongs to `selectorDispatchMsg`. -/
  decodeCalldata? : List Ident -> List ABIType -> EVM.Bytes -> Option Store :=
    ABI.decodeCalldataWithMode .modern
  /-- Decode an explicit `abi.decode` expression. This is distinct from decoding a flat list of
      external-call return values, which may depend on the named call. -/
  decodeValue? : ABIType -> EVM.Bytes -> Option Value :=
    ABI.decodeReturnValueWithMode? .modern

/-- Install a compiler's standard calldata and value decoders while preserving the named
    external-call encoder and return decoder. Custom instances may replace either operation. -/
def ExternalCallABI.withMode (abi : ExternalCallABI) (mode : ABI.DecodeMode) : ExternalCallABI :=
  { abi with
    decodeCalldata? := ABI.decodeCalldataWithMode mode
    decodeValue? := ABI.decodeReturnValueWithMode? mode }

/-- Install a Vyper calldata decoder with capacity-bearing declarations while retaining
the ordinary `Config.externalABI` interface and the named external-call operations. -/
def ExternalCallABI.withVyperABI (abi : ExternalCallABI)
    (functions : List ABI.VyperABIFunction) : ExternalCallABI :=
  { abi.withMode .vyper with
    decodeCalldata? := ABI.decodeVyperCalldata functions }

@[simp] theorem ExternalCallABI.withMode_encode? (abi : ExternalCallABI)
    (mode : ABI.DecodeMode) : (abi.withMode mode).encode? = abi.encode? := rfl

@[simp] theorem ExternalCallABI.withMode_decode? (abi : ExternalCallABI)
    (mode : ABI.DecodeMode) : (abi.withMode mode).decode? = abi.decode? := rfl

structure Config where
  storageBackend : StorageBackend
  /-- Operations on `ContractDecl.transient`, independent of persistent storage. -/
  transientBackend : StorageBackend := StorageBackend.empty
  externalABI : ExternalCallABI
  /-- Initialisation code (creation bytecode ++ ABI-encoded constructor args) for a
      `new` of the named contract. -/
  creationCode : Ident -> List Value -> Option EVM.Bytes := fun _ _ => none

  /-- Scheme for initialisation code (creation bytecode ++ ABI-encoded constructor args) for
      deployment of the contract's constructor -/
  selfDeployment : EVM.Bytes → List Value → Option EVM.Bytes

structure Frame where
  contract : ContractDecl
  locals : Store
  /-- Values of the contract's immutables.  The constructor starts from their zero values
      (`initialImmutables`) and assigns them (`Stmt.setImmutable`); a runtime call starts from the
      values the constructor left, which the deployed code embeds. -/
  immutables : Store := ∅

end Solm
