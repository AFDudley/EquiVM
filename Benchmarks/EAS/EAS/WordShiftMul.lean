import Benchmarks.EAS.EAS.PackedShift
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES Reasoning.EVMWord.shiftLeft5_ofNat_eq to any in-range shift and modular multiplication.
theorem wordShiftLeft_mul (word : UInt256) (shift : Nat) (hs : shift < 256) :
    UInt256.shiftLeft word (UInt256.ofNat shift) = UInt256.mul word (UInt256.ofNat (2^shift)) := by
  have hp : 2^shift < UInt256.size := Nat.pow_lt_pow_right (by decide) hs
  have hsn : (UInt256.ofNat shift).toNat = shift := ulit_toNat' _ (by change shift < 2^256; omega)
  apply u256_inj
  unfold UInt256.shiftLeft
  rw [if_neg (by change ¬ (UInt256.ofNat shift).toNat ≥ 256; rw [hsn]; omega)]
  change (word.toNat <<< (UInt256.ofNat shift).toNat)%UInt256.size = _
  rw [hsn,Nat.shiftLeft_eq,u256_mul_toNat,ulit_toNat' _ hp]

-- GENERALIZES shiftLeft5_ofNat_eq to every EVM shift and arbitrary word.
theorem wordShiftLeft_nat (word : UInt256) (shift : Nat) (hs : shift < 256) :
    UInt256.shiftLeft word (UInt256.ofNat shift) = UInt256.ofNat (2^shift*word.toNat) := by
  rw [wordShiftLeft_mul word shift hs]
  apply u256_inj
  rw [u256_mul_toNat,ulit_toNat' _ (Nat.pow_lt_pow_right (by decide) hs)]
  change (word.toNat*2^shift)%UInt256.size = (2^shift*word.toNat)%UInt256.size
  rw [Nat.mul_comm]

end Benchmarks.EAS.EAS
