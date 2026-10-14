import Benchmarks.Safe.V3_77901a5.Version
import Benchmarks.Safe.V3_77901a5.AddOwnerWithThreshold
import Benchmarks.Safe.V3_77901a5.ApproveHash
import Benchmarks.Safe.V3_77901a5.ApprovedHashes
import Benchmarks.Safe.V3_77901a5.ChangeThreshold
import Benchmarks.Safe.V3_77901a5.CheckNSignatures
import Benchmarks.Safe.V3_77901a5.CheckNSignaturesAddress
import Benchmarks.Safe.V3_77901a5.CheckSignatures
import Benchmarks.Safe.V3_77901a5.CheckSignaturesAddress
import Benchmarks.Safe.V3_77901a5.DisableModule
import Benchmarks.Safe.V3_77901a5.DomainSeparator
import Benchmarks.Safe.V3_77901a5.EnableModule
import Benchmarks.Safe.V3_77901a5.ExecTransaction
import Benchmarks.Safe.V3_77901a5.ExecTransactionFromModule
import Benchmarks.Safe.V3_77901a5.ExecTransactionFromModuleReturnData
import Benchmarks.Safe.V3_77901a5.GetModulesPaginated
import Benchmarks.Safe.V3_77901a5.GetOwners
import Benchmarks.Safe.V3_77901a5.GetStorageAt
import Benchmarks.Safe.V3_77901a5.GetThreshold
import Benchmarks.Safe.V3_77901a5.GetTransactionHash
import Benchmarks.Safe.V3_77901a5.IsModuleEnabled
import Benchmarks.Safe.V3_77901a5.IsOwner
import Benchmarks.Safe.V3_77901a5.Nonce
import Benchmarks.Safe.V3_77901a5.RemoveOwner
import Benchmarks.Safe.V3_77901a5.SetFallbackHandler
import Benchmarks.Safe.V3_77901a5.SetGuard
import Benchmarks.Safe.V3_77901a5.SetModuleGuard
import Benchmarks.Safe.V3_77901a5.Setup
import Benchmarks.Safe.V3_77901a5.SignedMessages
import Benchmarks.Safe.V3_77901a5.SimulateAndRevert
import Benchmarks.Safe.V3_77901a5.SwapOwner
import Benchmarks.Safe.V3_77901a5.Receive
import Benchmarks.Safe.V3_77901a5.Fallback

/-!
Proof scaffolds for every Safe runtime entrypoint. All obligations retain the unqualified
refinement relation: arbitrary account maps, calldata (including decoding failures), call value,
gas, call depth, and either permission mode. Bodies are intentionally unproved.
-/

