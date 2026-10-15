import Benchmarks.Safe.V0_cdb2eb5.Version
import Benchmarks.Safe.V0_cdb2eb5.AddOwnerWithThreshold
import Benchmarks.Safe.V0_cdb2eb5.ApproveHash
import Benchmarks.Safe.V0_cdb2eb5.ApprovedHashes
import Benchmarks.Safe.V0_cdb2eb5.ChangeThreshold
import Benchmarks.Safe.V0_cdb2eb5.CheckNSignatures
import Benchmarks.Safe.V0_cdb2eb5.CheckNSignaturesAddress
import Benchmarks.Safe.V0_cdb2eb5.CheckSignatures
import Benchmarks.Safe.V0_cdb2eb5.CheckSignaturesAddress
import Benchmarks.Safe.V0_cdb2eb5.DisableModule
import Benchmarks.Safe.V0_cdb2eb5.DomainSeparator
import Benchmarks.Safe.V0_cdb2eb5.EnableModule
import Benchmarks.Safe.V0_cdb2eb5.ExecTransaction
import Benchmarks.Safe.V0_cdb2eb5.ExecTransactionFromModule
import Benchmarks.Safe.V0_cdb2eb5.ExecTransactionFromModuleReturnData
import Benchmarks.Safe.V0_cdb2eb5.GetModulesPaginated
import Benchmarks.Safe.V0_cdb2eb5.GetOwners
import Benchmarks.Safe.V0_cdb2eb5.GetStorageAt
import Benchmarks.Safe.V0_cdb2eb5.GetThreshold
import Benchmarks.Safe.V0_cdb2eb5.GetTransactionHash
import Benchmarks.Safe.V0_cdb2eb5.IsModuleEnabled
import Benchmarks.Safe.V0_cdb2eb5.IsOwner
import Benchmarks.Safe.V0_cdb2eb5.Nonce
import Benchmarks.Safe.V0_cdb2eb5.RemoveOwner
import Benchmarks.Safe.V0_cdb2eb5.SetFallbackHandler
import Benchmarks.Safe.V0_cdb2eb5.SetGuard
import Benchmarks.Safe.V0_cdb2eb5.SetModuleGuard
import Benchmarks.Safe.V0_cdb2eb5.Setup
import Benchmarks.Safe.V0_cdb2eb5.SignedMessages
import Benchmarks.Safe.V0_cdb2eb5.SimulateAndRevert
import Benchmarks.Safe.V0_cdb2eb5.SwapOwner
import Benchmarks.Safe.V0_cdb2eb5.Receive
import Benchmarks.Safe.V0_cdb2eb5.Fallback

/-!
Proof scaffolds for every Safe runtime entrypoint. All obligations retain the unqualified
refinement relation: arbitrary account maps, calldata (including decoding failures), call value,
gas, call depth, and either permission mode. Bodies are intentionally unproved.
-/

