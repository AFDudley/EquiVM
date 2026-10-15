import Benchmarks.Safe.ViaIR.Version
import Benchmarks.Safe.ViaIR.AddOwnerWithThreshold
import Benchmarks.Safe.ViaIR.ApproveHash
import Benchmarks.Safe.ViaIR.ApprovedHashes
import Benchmarks.Safe.ViaIR.ChangeThreshold
import Benchmarks.Safe.ViaIR.CheckNSignatures
import Benchmarks.Safe.ViaIR.CheckNSignaturesAddress
import Benchmarks.Safe.ViaIR.CheckSignatures
import Benchmarks.Safe.ViaIR.CheckSignaturesAddress
import Benchmarks.Safe.ViaIR.DisableModule
import Benchmarks.Safe.ViaIR.DomainSeparator
import Benchmarks.Safe.ViaIR.EnableModule
import Benchmarks.Safe.ViaIR.ExecTransaction
import Benchmarks.Safe.ViaIR.ExecTransactionFromModule
import Benchmarks.Safe.ViaIR.ExecTransactionFromModuleReturnData
import Benchmarks.Safe.ViaIR.GetModulesPaginated
import Benchmarks.Safe.ViaIR.GetOwners
import Benchmarks.Safe.ViaIR.GetStorageAt
import Benchmarks.Safe.ViaIR.GetThreshold
import Benchmarks.Safe.ViaIR.GetTransactionHash
import Benchmarks.Safe.ViaIR.IsModuleEnabled
import Benchmarks.Safe.ViaIR.IsOwner
import Benchmarks.Safe.ViaIR.Nonce
import Benchmarks.Safe.ViaIR.RemoveOwner
import Benchmarks.Safe.ViaIR.SetFallbackHandler
import Benchmarks.Safe.ViaIR.SetGuard
import Benchmarks.Safe.ViaIR.SetModuleGuard
import Benchmarks.Safe.ViaIR.Setup
import Benchmarks.Safe.ViaIR.SignedMessages
import Benchmarks.Safe.ViaIR.SimulateAndRevert
import Benchmarks.Safe.ViaIR.SwapOwner
import Benchmarks.Safe.ViaIR.Receive
import Benchmarks.Safe.ViaIR.Fallback

/-!
Proof scaffolds for every Safe runtime entrypoint. All obligations retain the unqualified
refinement relation: arbitrary account maps, calldata (including decoding failures), call value,
gas, call depth, and either permission mode. Bodies are intentionally unproved.
-/

