import Benchmarks.Safe.Runs1e6.Version
import Benchmarks.Safe.Runs1e6.AddOwnerWithThreshold
import Benchmarks.Safe.Runs1e6.ApproveHash
import Benchmarks.Safe.Runs1e6.ApprovedHashes
import Benchmarks.Safe.Runs1e6.ChangeThreshold
import Benchmarks.Safe.Runs1e6.CheckNSignatures
import Benchmarks.Safe.Runs1e6.CheckNSignaturesAddress
import Benchmarks.Safe.Runs1e6.CheckSignatures
import Benchmarks.Safe.Runs1e6.CheckSignaturesAddress
import Benchmarks.Safe.Runs1e6.DisableModule
import Benchmarks.Safe.Runs1e6.DomainSeparator
import Benchmarks.Safe.Runs1e6.EnableModule
import Benchmarks.Safe.Runs1e6.ExecTransaction
import Benchmarks.Safe.Runs1e6.ExecTransactionFromModule
import Benchmarks.Safe.Runs1e6.ExecTransactionFromModuleReturnData
import Benchmarks.Safe.Runs1e6.GetModulesPaginated
import Benchmarks.Safe.Runs1e6.GetOwners
import Benchmarks.Safe.Runs1e6.GetStorageAt
import Benchmarks.Safe.Runs1e6.GetThreshold
import Benchmarks.Safe.Runs1e6.GetTransactionHash
import Benchmarks.Safe.Runs1e6.IsModuleEnabled
import Benchmarks.Safe.Runs1e6.IsOwner
import Benchmarks.Safe.Runs1e6.Nonce
import Benchmarks.Safe.Runs1e6.RemoveOwner
import Benchmarks.Safe.Runs1e6.SetFallbackHandler
import Benchmarks.Safe.Runs1e6.SetGuard
import Benchmarks.Safe.Runs1e6.SetModuleGuard
import Benchmarks.Safe.Runs1e6.Setup
import Benchmarks.Safe.Runs1e6.SignedMessages
import Benchmarks.Safe.Runs1e6.SimulateAndRevert
import Benchmarks.Safe.Runs1e6.SwapOwner
import Benchmarks.Safe.Runs1e6.Receive
import Benchmarks.Safe.Runs1e6.Fallback

/-!
Proof scaffolds for every Safe runtime entrypoint. All obligations retain the unqualified
refinement relation: arbitrary account maps, calldata (including decoding failures), call value,
gas, call depth, and either permission mode. Bodies are intentionally unproved.
-/

