import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoExternalSource
import Benchmarks.Morpho.MetaMorphoV1_1.CursorCallSource
import Benchmarks.Morpho.MetaMorphoV1_1.AllocatedReaderCalls

/-! Caller frames across the supply loop's parameter, market, and position reads. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def supplyMorphoParamsFrame (frame : Frame) (params : ByteArray) (ptr : UInt256) : Frame :=
  cursorResultFrame frame "marketParams" (marketParamsValue params) ptr

def supplyMorphoMarketFrame (frame : Frame) (params : ByteArray) (ptr : UInt256)
    (market : ByteArray) : Frame :=
  supplyMarketReservedFrame (supplyAccruedFrame (supplyMorphoParamsFrame frame params ptr)) ptr market

def supplyMorphoReadersFrame (frame : Frame) (params : ByteArray) (ptr1 : UInt256)
    (market : ByteArray) (shares ptr2 : UInt256) : Frame :=
  cursorResultFrame (supplyMorphoMarketFrame frame params ptr1 market)
    "supplyShares" (uint256Value shares) ptr2

theorem supplyMorphoReadersFrame_preserves (frame : Frame) (params : ByteArray) (ptr1 : UInt256)
    (market : ByteArray) (shares ptr2 : UInt256) (name : Ident)
    (hc : (cursorName == name) = false) (hs : (slotsAndCursorName == name) = false)
    (hp : ("marketParams" == name) = false) (ha : ("__c1" == name) = false)
    (hm : ("market" == name) = false) (hv : ("supplyShares" == name) = false) :
    (supplyMorphoReadersFrame frame params ptr1 market shares ptr2).locals.get? name =
      frame.locals.get? name := by
  rw [supplyMorphoReadersFrame, cursorResultFrame_preserves _ _ _ _ _ hc hv hs]
  simp only [supplyMorphoMarketFrame, supplyMarketReservedFrame, supplyMarketFrame,
    supplyAccruedFrame, store_get_ne _ _ hc, store_get_ne _ _ hm, store_get_ne _ _ ha]
  exact cursorResultFrame_preserves _ _ _ _ _ hc hp hs

theorem supplyMorphoReadersFrame_params (frame : Frame) (params : ByteArray) (ptr1 : UInt256)
    (market : ByteArray) (shares ptr2 : UInt256) :
    (supplyMorphoReadersFrame frame params ptr1 market shares ptr2).locals.get? "marketParams" =
      some (marketParamsValue params) := by
  rw [supplyMorphoReadersFrame, cursorResultFrame_preserves _ _ _ _ _
    (by decide) (by decide) (by decide)]
  simp only [supplyMorphoMarketFrame, supplyMarketReservedFrame, supplyMarketFrame,
    supplyAccruedFrame,
    store_get_ne _ _ (by decide : (cursorName == "marketParams") = false),
    store_get_ne _ _ (by decide : ("market" == "marketParams") = false),
    store_get_ne _ _ (by decide : ("__c1" == "marketParams") = false)]
  exact cursorResultFrame_value _ _ _ _ (by decide)

theorem supplyMorphoReadersFrame_market (frame : Frame) (params : ByteArray) (ptr1 : UInt256)
    (market : ByteArray) (shares ptr2 : UInt256) :
    (supplyMorphoReadersFrame frame params ptr1 market shares ptr2).locals.get? "market" =
      some (marketValue market) := by
  rw [supplyMorphoReadersFrame, cursorResultFrame_preserves _ _ _ _ _
    (by decide) (by decide) (by decide)]
  simp only [supplyMorphoMarketFrame, supplyMarketReservedFrame, supplyMarketFrame,
    store_get_ne _ _ (by decide : (cursorName == "market") = false), store_get_self]

theorem supplyMorphoReadersFrame_shares (frame : Frame) (params : ByteArray) (ptr1 : UInt256)
    (market : ByteArray) (shares ptr2 : UInt256) :
    (supplyMorphoReadersFrame frame params ptr1 market shares ptr2).locals.get? "supplyShares" =
      some (uint256Value shares) := cursorResultFrame_value _ _ _ _ (by decide)

theorem supplyMorphoReadersFrame_cursor (frame : Frame) (params : ByteArray) (ptr1 : UInt256)
    (market : ByteArray) (shares ptr2 : UInt256) :
    (supplyMorphoReadersFrame frame params ptr1 market shares ptr2).locals.get? cursorName =
      some (uint256Value ptr2) := cursorResultFrame_cursor _ _ _ _

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
