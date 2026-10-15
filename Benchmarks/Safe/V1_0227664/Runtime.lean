import Benchmarks.Safe.V1_0227664.Version
import Benchmarks.Safe.V1_0227664.AddOwnerWithThreshold
import Benchmarks.Safe.V1_0227664.ApproveHash
import Benchmarks.Safe.V1_0227664.ApprovedHashes
import Benchmarks.Safe.V1_0227664.ChangeThreshold
import Benchmarks.Safe.V1_0227664.CheckNSignatures
import Benchmarks.Safe.V1_0227664.CheckNSignaturesAddress
import Benchmarks.Safe.V1_0227664.CheckSignatures
import Benchmarks.Safe.V1_0227664.CheckSignaturesAddress
import Benchmarks.Safe.V1_0227664.DisableModule
import Benchmarks.Safe.V1_0227664.DomainSeparator
import Benchmarks.Safe.V1_0227664.EnableModule
import Benchmarks.Safe.V1_0227664.ExecTransaction
import Benchmarks.Safe.V1_0227664.ExecTransactionFromModule
import Benchmarks.Safe.V1_0227664.ExecTransactionFromModuleReturnData
import Benchmarks.Safe.V1_0227664.GetModulesPaginated
import Benchmarks.Safe.V1_0227664.GetOwners
import Benchmarks.Safe.V1_0227664.GetStorageAt
import Benchmarks.Safe.V1_0227664.GetThreshold
import Benchmarks.Safe.V1_0227664.GetTransactionHash
import Benchmarks.Safe.V1_0227664.IsModuleEnabled
import Benchmarks.Safe.V1_0227664.IsOwner
import Benchmarks.Safe.V1_0227664.Nonce
import Benchmarks.Safe.V1_0227664.RemoveOwner
import Benchmarks.Safe.V1_0227664.SetFallbackHandler
import Benchmarks.Safe.V1_0227664.SetGuard
import Benchmarks.Safe.V1_0227664.SetModuleGuard
import Benchmarks.Safe.V1_0227664.Setup
import Benchmarks.Safe.V1_0227664.SignedMessages
import Benchmarks.Safe.V1_0227664.SimulateAndRevert
import Benchmarks.Safe.V1_0227664.SwapOwner
import Benchmarks.Safe.V1_0227664.Receive
import Benchmarks.Safe.V1_0227664.Fallback

/-!
Proof scaffolds for every Safe runtime entrypoint. All obligations retain the unqualified
refinement relation: arbitrary account maps, calldata (including decoding failures), call value,
gas, call depth, and either permission mode. Bodies are intentionally unproved.
-/

