import Benchmarks.Morpho.MetaMorphoV1_1.BytesArrayElement
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayCalldata

/-! Relate the retained source array to the runtime calldata view. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory ABI.Solc08Calldata
open Benchmarks.EAS.Attester (arrayHead arrayHead_toNat)

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def multicallInput (cd : ByteArray) : List Value := calldataBytesArrayValues cd (arrayHead cd 4)

def multicallInputBase (cd : ByteArray) : UInt256 := UInt256.ofNat (calldataArrayOffset cd + 36)

theorem multicallInput_length {cd : ByteArray} (hc : WordArrayCalldataChecks cd) :
    (multicallInput cd).length = calldataArrayLength cd := by
  rw [multicallInput, calldataBytesArrayValues_length, arrayHead_toNat hc.offset]
  rfl

theorem multicallInputBase_eq {cd : ByteArray} (hc : WordArrayCalldataChecks cd) :
    arrayHead cd 4 + (⟨32⟩ : UInt256) = multicallInputBase cd := by
  have hs : 4 + calldataArrayOffset cd + 32 < UInt256.size := by
    have hl := hc.offset
    change calldataArrayOffset cd ≤ 18446744073709551615 at hl
    change _ < 2 ^ 256
    omega
  apply u256_inj
  rw [uadd_toNat, arrayHead_toNat hc.offset]
  change (4 + calldataArrayOffset cd + 32) % UInt256.size =
    (UInt256.ofNat (calldataArrayOffset cd + 36)).toNat
  rw [Nat.mod_eq_of_lt hs, UInt256.toNat_ofNat_of_lt (by omega)]
  omega

theorem multicallInput_getElem {cd : ByteArray} (hc : WordArrayCalldataChecks cd)
    (i : Nat) (hi : i < calldataArrayLength cd) :
    (multicallInput cd)[i]? = some (if bytesArrayAccessValid cd (multicallInputBase cd) i then
      .bytes (bytesTailData cd (bytesArrayHead cd (multicallInputBase cd) i)) else decodeFailure) := by
  rw [multicallInput, calldataBytesArrayValues_getElem _ _ _ (by
    rw [arrayHead_toNat hc.offset]; exact hi), multicallInputBase_eq hc,
    retainedCalldataBytesElement _ _ _ (by
      have hn := hc.length
      change calldataArrayLength cd ≤ 18446744073709551615 at hn
      change _ < 2 ^ 256
      omega)]

end Benchmarks.Morpho.MetaMorphoV1_1
