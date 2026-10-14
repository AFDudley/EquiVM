import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateAllocationSyntax

/-! Source fragments at the reallocation loop's execution boundaries. -/

open Stele ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def reallocateRowDeclarations : List Stmt :=
  [.letDecl "allocationTuple" none (.index (.var "allocations") (.var "i")),
   reallocateRowGuard,
   .letDecl "paramsTuple" none (.tupleGet (.var "allocationTuple") 0),
   .letDecl "params" (some reallocateParamsType)
     (.structLit "MarketParams"
       [("loanToken", .tupleGet (.var "paramsTuple") 0),
        ("collateralToken", .tupleGet (.var "paramsTuple") 1),
        ("oracle", .tupleGet (.var "paramsTuple") 2),
        ("irm", .tupleGet (.var "paramsTuple") 3),
        ("lltv", .tupleGet (.var "paramsTuple") 4)]),
   .letDecl "allocation" (some reallocateItemType)
     (.structLit "MarketAllocation"
       [("marketParams", .var "params"), ("assets", .tupleGet (.var "allocationTuple") 1)])]

def reallocateRowIdentify : List Stmt :=
  [.internalCall "MarketParamsLib_id" [.field (.var "allocation") "marketParams"] "id",
   .require (.storage ⟨"config", [.mindex (.var "id"), .field "enabled"]⟩)]

def reallocateRowAccrued : List Stmt :=
  cursorCall allocatedAccruedSupplyBalanceFunction.name
    [.field (.var "allocation") "marketParams", .var "id"] "__c3"

def reallocateRowBalances : List Stmt :=
  [.letDecl "supplyAssets" (some cursorType) (.tupleGet (.var "__c3") 0),
   .letDecl "supplyShares" (some cursorType) (.tupleGet (.var "__c3") 1)]

def reallocateWithdrawBody : List Stmt :=
  [.letDecl "shares" (some cursorType) (.intLit 0),
   .ite (.binary .eq (.field (.var "allocation") "assets") (.intLit 0))
     [.assign .localVar ⟨"shares", []⟩ (.var "supplyShares"),
      .assign .localVar ⟨"withdrawn", []⟩ (.intLit 0)] [],
   .externalCall (.var "morphoTarget") "withdraw" (.intLit 0)
     [.field (.var "allocation") "marketParams", .var "withdrawn", .var "shares",
      .env .this, .env .this] "__c5" true,
   reserveBytes 64,
   .letDecl "withdrawnAssets" (some cursorType) (.tupleGet (.var "__c5") 0),
   .letDecl "withdrawnShares" (some cursorType) (.tupleGet (.var "__c5") 1),
   .internalCall "_msgSender" [] "__c6",
   .emit "ReallocateWithdraw"
     [.var "__c6", .var "id", .var "withdrawnAssets", .var "withdrawnShares"],
   .assign .localVar ⟨"totalWithdrawn", []⟩
     (.inRange (.uint ⟨256, by decide⟩)
       (.binary .add (.var "totalWithdrawn") (.var "withdrawnAssets")))]

def reallocateSupplyBody : List Stmt :=
  [.internalCall "UtilsLib_zeroFloorSub" [.var "totalWithdrawn", .var "totalSupplied"] "__c7",
   .internalCall "UtilsLib_zeroFloorSub"
     [.field (.var "allocation") "assets", .var "supplyAssets"] "__c8",
   .letDecl "suppliedAssets" (some cursorType)
     (.ite (.binary .eq (.field (.var "allocation") "assets")
       (.intLit (Int.ofNat (2 ^ 256 - 1)))) (.var "__c7") (.var "__c8")),
   .ite (.binary .eq (.var "suppliedAssets") (.intLit 0)) [.continue] [],
   .letDecl "supplyCap" (some cursorType)
     (.storage ⟨"config", [.mindex (.var "id"), .field "cap"]⟩),
   .require (.binary .le
     (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "supplyAssets") (.var "suppliedAssets")))
     (.var "supplyCap")),
   .externalCall (.var "morphoTarget") "supply" (.intLit 0)
     [.field (.var "allocation") "marketParams", .var "suppliedAssets", .intLit 0,
      .env .this, .newBytes (.intLit 0)] "__c9" true,
   reserveBytes 64,
   .letDecl "suppliedShares" (some cursorType) (.tupleGet (.var "__c9") 1),
   .internalCall "_msgSender" [] "__c10",
   .emit "ReallocateSupply" [.var "__c10", .var "id", .var "suppliedAssets", .var "suppliedShares"],
   .assign .localVar ⟨"totalSupplied", []⟩
     (.inRange (.uint ⟨256, by decide⟩)
       (.binary .add (.var "totalSupplied") (.var "suppliedAssets")))]

def reallocateRowBranch : Stmt :=
  .ite (.binary .gt (.var "withdrawn") (.intLit 0)) reallocateWithdrawBody reallocateSupplyBody

def reallocateRowAmount : Stmt :=
  .internalCall "UtilsLib_zeroFloorSub"
    [.var "supplyAssets", .field (.var "allocation") "assets"] "withdrawn"

def reallocateRowPrefix : List Stmt :=
  [reserveBytes 64, reserveBytes 160] ++ reallocateRowDeclarations ++ reallocateRowIdentify

def reallocateRowContinuation : List Stmt :=
  reallocateRowAccrued ++ reallocateRowBalances ++ [reallocateRowAmount, reallocateRowBranch]

def reallocateIteration : List Stmt := reallocateRowPrefix ++ reallocateRowContinuation

def reallocateCondition : Expr :=
  .binary .lt (.var "i") (.arrayLength .localVar ⟨"allocations", []⟩)

def reallocatePost : List Stmt :=
  [.assign .localVar ⟨"i", []⟩
    (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "i") (.intLit 1)))]

def reallocateLoop : Stmt :=
  .for [.letDecl "i" (some cursorType) (.intLit 0)] reallocateCondition reallocatePost
    reallocateIteration

set_option maxRecDepth 2000 in
theorem allocatedReallocateTransition_body :
    allocatedReallocateTransition.body =
      (Syntax.contractSyntax.transitions[34]!).body.take 4 ++
      [.letDecl cursorName (some cursorType) (.intLit 128),
       .internalCall "_checkAllocatorRole" [] "__role",
       .letDecl "totalSupplied" (some cursorType) (.intLit 0),
       .letDecl "totalWithdrawn" (some cursorType) (.intLit 0), reallocateLoop,
       .require (.binary .eq (.var "totalWithdrawn") (.var "totalSupplied"))] := by decide +kernel

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
