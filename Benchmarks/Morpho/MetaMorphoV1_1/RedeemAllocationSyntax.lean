import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawAllocationSyntax

/-! Thread compiler allocation checks through redemption's shared withdrawal path. -/

open Stele ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def allocatedRedeemTransition : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[56]!
  { source with
    body := source.body.take 3 ++ [.letDecl cursorName (some cursorType) (.intLit 128)] ++
      (source.body.drop 3).map withdrawCursorStatement }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
