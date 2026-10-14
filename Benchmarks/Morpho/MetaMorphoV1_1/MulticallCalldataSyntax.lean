import ABI.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateCalldataSyntax

/-! Multicall keeps the array in calldata and copies each byte string at its loop access. -/

open Stele ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1

def multicallCalldataPlan : CalldataPlan :=
  { materialize := [[.element]], deferErrors := [[.element]] }

def multicallCalldataPlans : List (Nat × List CalldataPlan) :=
  [(0xac9650d8, [multicallCalldataPlan])]

/-- The only bytes-array input is multicall. Its nested offsets use the calldata-reference
checks at PCs 3886–3932; each element is then copied by the routine at PC 11644. -/
def decodeContractCalldata (names : List Ident) (types : List ABIType)
    (cd : ByteArray) : Option Store :=
  if types == [.dynamicArray .bytes] then
    decodeCalldataWithMode (.solc08Calldata multicallCalldataPlans) names types cd
  else if types == [.dynamicArray reallocateItemType] then
    decodeCalldataWithMode (.solc08Calldata reallocateCalldataPlans) names types cd
  else decodeCalldata names types cd

end Benchmarks.Morpho.MetaMorphoV1_1
