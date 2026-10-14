import Benchmarks.Safe.V2_0e91d99.Version
import Benchmarks.Safe.V2_0e91d99.AddOwnerWithThreshold
import Benchmarks.Safe.V2_0e91d99.ApproveHash
import Benchmarks.Safe.V2_0e91d99.ApprovedHashes
import Benchmarks.Safe.V2_0e91d99.ChangeThreshold
import Benchmarks.Safe.V2_0e91d99.CheckNSignatures
import Benchmarks.Safe.V2_0e91d99.CheckNSignaturesAddress
import Benchmarks.Safe.V2_0e91d99.CheckSignatures
import Benchmarks.Safe.V2_0e91d99.CheckSignaturesAddress
import Benchmarks.Safe.V2_0e91d99.DisableModule
import Benchmarks.Safe.V2_0e91d99.DomainSeparator
import Benchmarks.Safe.V2_0e91d99.EnableModule
import Benchmarks.Safe.V2_0e91d99.ExecTransaction
import Benchmarks.Safe.V2_0e91d99.ExecTransactionFromModule
import Benchmarks.Safe.V2_0e91d99.ExecTransactionFromModuleReturnData
import Benchmarks.Safe.V2_0e91d99.GetModulesPaginated
import Benchmarks.Safe.V2_0e91d99.GetOwners
import Benchmarks.Safe.V2_0e91d99.GetStorageAt
import Benchmarks.Safe.V2_0e91d99.GetThreshold
import Benchmarks.Safe.V2_0e91d99.GetTransactionHash
import Benchmarks.Safe.V2_0e91d99.IsModuleEnabled
import Benchmarks.Safe.V2_0e91d99.IsOwner
import Benchmarks.Safe.V2_0e91d99.Nonce
import Benchmarks.Safe.V2_0e91d99.RemoveOwner
import Benchmarks.Safe.V2_0e91d99.SetFallbackHandler
import Benchmarks.Safe.V2_0e91d99.SetGuard
import Benchmarks.Safe.V2_0e91d99.SetModuleGuard
import Benchmarks.Safe.V2_0e91d99.Setup
import Benchmarks.Safe.V2_0e91d99.SignedMessages
import Benchmarks.Safe.V2_0e91d99.SimulateAndRevert
import Benchmarks.Safe.V2_0e91d99.SwapOwner
import Benchmarks.Safe.V2_0e91d99.Receive
import Benchmarks.Safe.V2_0e91d99.Fallback

/-!
Proof scaffolds for every Safe runtime entrypoint. All obligations retain the unqualified
refinement relation: arbitrary account maps, calldata (including decoding failures), call value,
gas, call depth, and either permission mode. Bodies are intentionally unproved.
-/

