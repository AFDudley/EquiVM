import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositQueueSource
import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSupplyABI
import Benchmarks.Morpho.MetaMorphoV1_1.MorphoAccrueABI

/-! Named source fragments of the allocated Morpho supply loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def supplyMorphoParams : List Stmt :=
  cursorCall allocatedMarketParamsFunction.name [.var "id"] "marketParams"

def supplyMorphoAccrual : List Stmt :=
  [.require (.binary .gt (.extCodeSize (.immutable "MORPHO")) (.intLit 0)),
   .externalCall (.var "morphoTarget") "accrueInterest" (.intLit 0) [.var "marketParams"] "__c1"]

def supplyMorphoMarket : List Stmt :=
  [.externalCall (.var "morphoTarget") "market" (.intLit 0) [.var "id"] "market" false,
   reserveBytes 384]

def supplyMorphoShares : List Stmt :=
  cursorCall allocatedSupplySharesFunction.name
    [.immutable "MORPHO", .var "id", .env .this] "supplyShares"

def supplyMorphoArithmetic : List Stmt :=
  [.internalCall "SharesMathLib_toAssetsUp"
     [.var "supplyShares", .field (.var "market") "totalSupplyAssets",
       .field (.var "market") "totalSupplyShares"] "supplyAssets",
   .internalCall "UtilsLib_zeroFloorSub" [.var "supplyCap", .var "supplyAssets"] "__c5",
   .internalCall "UtilsLib_min" [.var "__c5", .var "assets"] "toSupply"]

def supplyMorphoCall : Stmt :=
  .checkedCall (.var "morphoTarget") "supply" (.intLit 0)
    [.var "marketParams", .var "toSupply", .intLit 0, .env .this, .newBytes (.intLit 0)]
    "__ret" [reserveBytes 64,
      .assign .localVar ⟨"assets", []⟩
        (.inRange (.uint ⟨256, by decide⟩) (.binary .sub (.var "assets") (.var "toSupply")))]
    "__err" []

def supplyMorphoSupply : List Stmt :=
  [.ite (.binary .gt (.var "toSupply") (.intLit 0)) [supplyMorphoCall] [],
   .ite (.binary .eq (.var "assets") (.intLit 0))
     [.return [.tupleLit [], .var cursorName]] []]

def supplyMorphoReaders : List Stmt :=
  supplyMorphoParams ++ supplyMorphoAccrual ++ supplyMorphoMarket ++ supplyMorphoShares

def supplyMorphoIteration : List Stmt :=
  [.letDecl "id" (some abiBytes32) (.storage ⟨"supplyQueue", [.aindex (.var "i")]⟩),
   .letDecl "supplyCap" (some abiUInt256)
     (.storage ⟨"config", [.mindex (.var "id"), .field "cap"]⟩),
   .ite maxDepositCapCondition [.continue] []] ++
  supplyMorphoReaders ++ supplyMorphoArithmetic ++ supplyMorphoSupply

set_option maxRecDepth 2000 in
theorem allocatedSupplyMorphoFunction_body :
    allocatedSupplyMorphoFunction.body =
      [.letDecl "morphoTarget" (some abiAddress) (.immutable "MORPHO"),
       .for [.letDecl "i" (some abiUInt256) (.intLit 0)] maxDepositCondition maxDepositPost
         supplyMorphoIteration,
       .require (.binary .eq (.var "assets") (.intLit 0)),
       .return [.tupleLit [], .var cursorName]] := by decide +kernel

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
