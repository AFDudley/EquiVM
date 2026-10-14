import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawLoopSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.MorphoWithdrawABI

/-! Source fragments of the mutating Morpho withdrawal loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def withdrawMorphoParams : List Stmt :=
  cursorCall allocatedMarketParamsFunction.name [.var "id"] "marketParams"

def withdrawMorphoAccrued : List Stmt :=
  cursorCall allocatedAccruedSupplyBalanceFunction.name [.var "marketParams", .var "id"] "__c1"

def withdrawMorphoBalances : List Stmt :=
  [.letDecl "supplyAssets" (some abiUInt256) (.tupleGet (.var "__c1") 0),
   .letDecl "market" (some (.tuple (List.replicate 6 marketUInt128))) (.tupleGet (.var "__c1") 2)]

def withdrawMorphoLiquidity : List Stmt :=
  cursorCall allocatedWithdrawableFunction.name
    [.var "marketParams", .field (.var "market") "totalSupplyAssets",
      .field (.var "market") "totalBorrowAssets", .var "supplyAssets"] "__c2"

def withdrawMorphoMinimum : Stmt :=
  .internalCall "UtilsLib_min" [.var "__c2", .var "assets"] "toWithdraw"

def withdrawMorphoCall : Stmt :=
  .checkedCall (.var "morphoTarget") "withdraw" (.intLit 0)
    [.var "marketParams", .var "toWithdraw", .intLit 0, .env .this, .env .this]
    "__ret" [reserveBytes 64,
      .assign .localVar ⟨"assets", []⟩
        (.inRange (.uint ⟨256, by decide⟩) (.binary .sub (.var "assets") (.var "toWithdraw")))]
    "__err" []

def withdrawMorphoAttempt : List Stmt :=
  [.ite (.binary .gt (.var "toWithdraw") (.intLit 0)) [withdrawMorphoCall] [],
   .ite (.binary .eq (.var "assets") (.intLit 0))
     [.return [.tupleLit [], .var cursorName]] []]

def withdrawMorphoReaders : List Stmt :=
  withdrawMorphoParams ++ withdrawMorphoAccrued ++ withdrawMorphoBalances ++ withdrawMorphoLiquidity

def withdrawMorphoIteration : List Stmt :=
  [.letDecl "id" (some abiBytes32) (.storage ⟨"withdrawQueue", [.aindex (.var "i")]⟩)] ++
  withdrawMorphoReaders ++ withdrawMorphoMinimum :: withdrawMorphoAttempt

set_option maxRecDepth 2000 in
theorem allocatedWithdrawMorphoFunction_body :
    allocatedWithdrawMorphoFunction.body =
      [.letDecl "morphoTarget" (some abiAddress) (.immutable "MORPHO"),
       .for [.letDecl "i" (some abiUInt256) (.intLit 0)] accruedAssetsCondition accruedAssetsPost
         withdrawMorphoIteration,
       .require (.binary .eq (.var "assets") (.intLit 0)),
       .return [.tupleLit [], .var cursorName]] := by decide +kernel

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
