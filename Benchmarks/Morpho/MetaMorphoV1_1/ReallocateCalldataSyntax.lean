import ABI.Decode

/-! Reallocation copies each static allocation tuple from calldata at its loop access. -/

open Stele ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1

def reallocateParamsType : ABIType :=
  .tuple [.elem .address, .elem .address, .elem .address, .elem .address,
    .elem (.int (.uint ⟨256, by decide⟩))]

def reallocateItemType : ABIType :=
  .tuple [reallocateParamsType, .elem (.int (.uint ⟨256, by decide⟩))]

def reallocateCalldataPlan : CalldataPlan :=
  { materialize := [[.element]], deferErrors := [[.element]] }

def reallocateCalldataPlans : List (Nat × List CalldataPlan) :=
  [(0x7299aa31, [reallocateCalldataPlan])]

end Benchmarks.Morpho.MetaMorphoV1_1
