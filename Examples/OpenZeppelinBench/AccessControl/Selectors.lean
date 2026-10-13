import Examples.OpenZeppelinBench.AccessControl.Bytecode
import Stele.Semantics

open Stele Ethereum Ethereum.EVM

namespace OpenZeppelinBench.AccessControl

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-!
# AccessControl benchmark selector facts

The deployed runtime bytes and jump-destination table live in `Bytecode.lean`.
-/

/-- `keccak("supportsInterface(bytes4)")[0:4] = 0x01ffc9a7`. -/
theorem supportsInterfaceSelectorBytes :
    (KEC (String.toByteArray (Stele.transitionSigStr supportsInterfaceTransition))).extract 0 4 =
      ⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ := by
  have hsig : Stele.transitionSigStr supportsInterfaceTransition = "supportsInterface(bytes4)" := by
    simp [Stele.transitionSigStr, ABI.printSignature, transitionSignature, supportsInterfaceTransition, bytes4, ABI.abiToSigStr, ABI.elemToSigStr]
    decide +kernel
  rw [hsig]
  decide +kernel

/-- `keccak("getRoleAdmin(bytes32)")[0:4] = 0x248a9ca3`. -/
theorem getRoleAdminSelectorBytes :
    (KEC (String.toByteArray (Stele.transitionSigStr getRoleAdminTransition))).extract 0 4 =
      ⟨#[0x24, 0x8a, 0x9c, 0xa3]⟩ := by
  have hsig : Stele.transitionSigStr getRoleAdminTransition = "getRoleAdmin(bytes32)" := by
    simp [Stele.transitionSigStr, ABI.printSignature, transitionSignature, getRoleAdminTransition, bytes32, ABI.abiToSigStr, ABI.elemToSigStr]
    decide +kernel
  rw [hsig]
  decide +kernel

/-- `keccak("grantRole(bytes32,address)")[0:4] = 0x2f2ff15d`. -/
theorem grantRoleSelectorBytes :
    (KEC (String.toByteArray (Stele.transitionSigStr grantRoleTransition))).extract 0 4 =
      ⟨#[0x2f, 0x2f, 0xf1, 0x5d]⟩ := by
  have hsig : Stele.transitionSigStr grantRoleTransition = "grantRole(bytes32,address)" := by
    simp [Stele.transitionSigStr, ABI.printSignature, transitionSignature, grantRoleTransition, addr, bytes32, ABI.abiToSigStr, ABI.elemToSigStr]
    decide +kernel
  rw [hsig]
  decide +kernel

/-- `keccak("renounceRole(bytes32,address)")[0:4] = 0x36568abe`. -/
theorem renounceRoleSelectorBytes :
    (KEC (String.toByteArray (Stele.transitionSigStr renounceRoleTransition))).extract 0 4 =
      ⟨#[0x36, 0x56, 0x8a, 0xbe]⟩ := by
  have hsig : Stele.transitionSigStr renounceRoleTransition = "renounceRole(bytes32,address)" := by
    simp [Stele.transitionSigStr, ABI.printSignature, transitionSignature, renounceRoleTransition, addr, bytes32, ABI.abiToSigStr, ABI.elemToSigStr]
    decide +kernel
  rw [hsig]
  decide +kernel

/-- `keccak("hasRole(bytes32,address)")[0:4] = 0x91d14854`. -/
theorem hasRoleSelectorBytes :
    (KEC (String.toByteArray (Stele.transitionSigStr hasRoleTransition))).extract 0 4 =
      ⟨#[0x91, 0xd1, 0x48, 0x54]⟩ := by
  have hsig : Stele.transitionSigStr hasRoleTransition = "hasRole(bytes32,address)" := by
    simp [Stele.transitionSigStr, ABI.printSignature, transitionSignature, hasRoleTransition, addr, bytes32, ABI.abiToSigStr, ABI.elemToSigStr]
    decide +kernel
  rw [hsig]
  decide +kernel

/-- `keccak("DEFAULT_ADMIN_ROLE()")[0:4] = 0xa217fddf`. -/
theorem defaultAdminRoleSelectorBytes :
    (KEC (String.toByteArray (Stele.transitionSigStr defaultAdminRoleTransition))).extract 0 4 =
      ⟨#[0xa2, 0x17, 0xfd, 0xdf]⟩ := by decide +kernel

/-- `keccak("revokeRole(bytes32,address)")[0:4] = 0xd547741f`. -/
theorem revokeRoleSelectorBytes :
    (KEC (String.toByteArray (Stele.transitionSigStr revokeRoleTransition))).extract 0 4 =
      ⟨#[0xd5, 0x47, 0x74, 0x1f]⟩ := by
  have hsig : Stele.transitionSigStr revokeRoleTransition = "revokeRole(bytes32,address)" := by
    simp [Stele.transitionSigStr, ABI.printSignature, transitionSignature, revokeRoleTransition, addr, bytes32, ABI.abiToSigStr, ABI.elemToSigStr]
    decide +kernel
  rw [hsig]
  decide +kernel

end OpenZeppelinBench.AccessControl
