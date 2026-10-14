import Benchmarks.Morpho.MetaMorphoV1_1.CalldataReference

/-! LIBRARY CANDIDATE: a bounded sequence of calldata word reads is a contiguous slice. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

theorem solcReadBytes_bounded {bytes : List UInt8} {start size : Nat}
    (hstart : start < EVM.wordModulus) (hin : start + size ≤ bytes.length) :
    solcReadBytes bytes start size = (bytes.drop start).take size := by
  have hl : ((bytes.drop start).take size).length = size := by
    simp only [List.length_take, List.length_drop]
    omega
  simp only [solcReadBytes, Nat.mod_eq_of_lt hstart, hl, Nat.sub_self,
    List.replicate_zero, List.append_nil]

theorem solcReadWords_bounded {bytes : List UInt8} {start count : Nat}
    (hword : start + 32 * count < EVM.wordModulus)
    (hin : start + 32 * count ≤ bytes.length) :
    solcReadWords bytes start count = (bytes.drop start).take (32 * count) := by
  induction count with
  | zero => simp only [solcReadWords, List.range_zero, List.flatMap_nil, Nat.mul_zero, List.take_zero]
  | succ count ih =>
      rw [solcReadWords, List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      change solcReadWords bytes start count ++
        solcReadBytes bytes (solcAdd start (32 * count)) 32 = _
      rw [ih (by omega) (by omega), solcAdd, Nat.mod_eq_of_lt (by omega),
        solcReadBytes_bounded (by omega) (by omega), Nat.mul_succ,
        List.take_add, List.drop_drop]

end Benchmarks.Morpho.MetaMorphoV1_1
