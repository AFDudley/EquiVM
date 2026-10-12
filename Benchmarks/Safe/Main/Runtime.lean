import Benchmarks.Safe.Main.Version
import Benchmarks.Safe.Main.AddOwnerWithThreshold
import Benchmarks.Safe.Main.ApproveHash
import Benchmarks.Safe.Main.ApprovedHashes
import Benchmarks.Safe.Main.ChangeThreshold
import Benchmarks.Safe.Main.CheckNSignatures
import Benchmarks.Safe.Main.CheckNSignaturesAddress
import Benchmarks.Safe.Main.CheckSignatures
import Benchmarks.Safe.Main.CheckSignaturesAddress
import Benchmarks.Safe.Main.DisableModule
import Benchmarks.Safe.Main.DomainSeparator
import Benchmarks.Safe.Main.EnableModule
import Benchmarks.Safe.Main.ExecTransaction
import Benchmarks.Safe.Main.ExecTransactionFromModule
import Benchmarks.Safe.Main.ExecTransactionFromModuleReturnData
import Benchmarks.Safe.Main.GetModulesPaginated
import Benchmarks.Safe.Main.GetOwners
import Benchmarks.Safe.Main.GetStorageAt
import Benchmarks.Safe.Main.GetThreshold
import Benchmarks.Safe.Main.GetTransactionHash
import Benchmarks.Safe.Main.IsModuleEnabled
import Benchmarks.Safe.Main.IsOwner
import Benchmarks.Safe.Main.Nonce
import Benchmarks.Safe.Main.RemoveOwner
import Benchmarks.Safe.Main.SetFallbackHandler
import Benchmarks.Safe.Main.SetGuard
import Benchmarks.Safe.Main.SetModuleGuard
import Benchmarks.Safe.Main.Setup
import Benchmarks.Safe.Main.SignedMessages
import Benchmarks.Safe.Main.SimulateAndRevert
import Benchmarks.Safe.Main.SwapOwner
import Benchmarks.Safe.Main.Receive
import Benchmarks.Safe.Main.Fallback

/-!
Proof scaffolds for every Safe runtime entrypoint. All obligations retain the unqualified
refinement relation: arbitrary account maps, calldata (including decoding failures), call value,
gas, call depth, and either permission mode. Bodies are intentionally unproved.
-/

