import Examples.TinyImmutable.Bytecode
import Reasoning.Dispatch

/-!
# TinyImmutable selector facts

The selectors depend only on transition names and parameter types, not on immutable values.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory
open TinyImmutable.Immutables

namespace TinyImmutable

abbrev ownerSelBytes : ByteArray := ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩
abbrev quoteSelBytes : ByteArray := ⟨#[0xed, 0x1b, 0xd7, 0x6c]⟩
abbrev scaleSelBytes : ByteArray := ⟨#[0xf5, 0x1e, 0x18, 0x1a]⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Selector fact: `keccak256("owner()")[0:4]`. -/
theorem ownerSelectorOf :
    selectorOf ownerTransition = ownerSelBytes := by
  simp only [selectorOf, ownerTransition, Stele.transitionSigStr,
    transitionSignature, ABI.printSignature]
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Selector fact: `keccak256("quote(uint256)")[0:4]`. -/
theorem quoteSelectorOf :
    selectorOf quoteTransition = quoteSelBytes := by
  have hsig : Stele.transitionSigStr quoteTransition = "quote(uint256)" := by
    simp [Stele.transitionSigStr, ABI.printSignature, transitionSignature,
      quoteTransition, uint256, uint256Int, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr,
      show Nat.repr 256 = "256" by decide +kernel]
  unfold selectorOf
  rw [hsig]
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Selector fact: `keccak256("scale()")[0:4]`. -/
theorem scaleSelectorOf :
    selectorOf scaleTransition = scaleSelBytes := by
  simp only [selectorOf, scaleTransition, Stele.transitionSigStr,
    transitionSignature, ABI.printSignature]
  decide +kernel

end TinyImmutable
