import Reasoning.VyperImmutables

/-! Vyper 0.4.3+commit.bff19ea2 `code_layout` for Immutable. -/

namespace Examples.VyperImmutable

/-- Offsets are relative to the appended immutable section. -/
def immutableLayout : Reasoning.VyperImmutables.Layout :=
  { slots := [{ name := "OWNER", offset := 0, length := 32 }, { name := "LIMIT", offset := 32, length := 32 }, { name := "TAG", offset := 64, length := 32 }], size := 96 }

end Examples.VyperImmutable
