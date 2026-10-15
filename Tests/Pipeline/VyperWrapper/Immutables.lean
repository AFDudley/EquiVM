import Reasoning.VyperImmutables

/-! Vyper 0.4.3+commit.bff19ea2 `code_layout` for Wrapper. -/

namespace Tests.Pipeline.VyperWrapper

/-- Offsets are relative to the appended immutable section. -/
def immutableLayout : Reasoning.VyperImmutables.Layout :=
  { slots := [{ name := "TOKEN", offset := 0, length := 32 }], size := 32 }

end Tests.Pipeline.VyperWrapper
