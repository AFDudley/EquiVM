import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! Typed constructor inputs and their canonical deployment encoding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: the ABI right-padded byte array has the advertised padded length.
theorem abiPaddedBytes_length (b : ByteArray) :
    (padRightToWord b.toList).length = paddedSize b.size := by
  have hlen : b.toList.length = b.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [padRightToWord, List.length_append, zeroBytes, List.length_replicate, hlen]
  exact Nat.add_sub_of_le (nat_le_paddedSize _)

structure ConstructorArgs where
  owner : AccountAddress
  morpho : AccountAddress
  initialTimelock : UInt256
  asset : AccountAddress
  name : ByteArray
  symbol : ByteArray

namespace ConstructorArgs

def values (a : ConstructorArgs) : List Value :=
  [.address a.owner, .address a.morpho, .int (Int.ofNat a.initialTimelock.toNat),
   .address a.asset, .bytes a.name, .bytes a.symbol]

def encoded (a : ConstructorArgs) : List UInt8 :=
  natBytes a.owner.val ++ natBytes a.morpho.val ++ EVM.Word.toBytesBE a.initialTimelock ++
  natBytes a.asset.val ++ natBytes 192 ++ natBytes (224 + paddedSize a.name.size) ++
  natBytes a.name.size ++ padRightToWord a.name.toList ++
  natBytes a.symbol.size ++ padRightToWord a.symbol.toList

theorem params : contract.ctor.params.map Param.ty =
    [.elem .address, .elem .address, .elem (.int (.uint ⟨256, by decide⟩)),
      .elem .address, .string, .string] := rfl

set_option maxRecDepth 2000 in
theorem encode (a : ConstructorArgs) :
    encodeABIValues? (contract.ctor.params.map Param.ty) a.values = some a.encoded := by
  have ha (addr : AccountAddress) : encodeABIValue? (.elem .address) (.address addr) =
      some (natBytes addr.val) := by
    simp only [encodeABIValue?, encodeABIWord?, bind, Option.bind]
    rfl
  have ht : encodeABIValue? (.elem (.int (.uint ⟨256, by decide⟩)))
      (.int (Int.ofNat a.initialTimelock.toNat)) =
      some (EVM.Word.toBytesBE a.initialTimelock) := encodeABIValue_uint256 _
  have hs (b : ByteArray) : encodeABIValue? .string (.bytes b) =
      some (natBytes b.size ++ padRightToWord b.toList) := by
    simp only [encodeABIValue?]
  have hnat (n : Nat) : (natBytes n).length = 32 := word_toBytesBE_length_32 _
  rw [params]
  simp only [values, encodeABIValues?, abiTupleHeadSize?, isDynamicABIType,
    staticABIEncodedSize?, encodeABIValuesFrom?, ha, ht, hs,
    Bool.false_eq_true,
    if_false, if_true, bind, Option.bind, List.length_append, hnat, abiPaddedBytes_length,
    List.length_nil, List.nil_append, List.append_nil, Nat.add_zero]
  simp only [encoded, List.append_assoc, ← Nat.add_assoc]

theorem encoded_length (a : ConstructorArgs) :
    a.encoded.length = 256 + paddedSize a.name.size + paddedSize a.symbol.size := by
  simp only [encoded, List.length_append, natBytes, word_toBytesBE_length_32,
    abiPaddedBytes_length]
  omega

theorem encoded_length_mod (a : ConstructorArgs) : a.encoded.length % 32 = 0 := by
  rw [encoded_length]
  simp only [paddedSize, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul,
    Nat.zero_mod, Nat.add_zero]

theorem values_length (a : ConstructorArgs) : a.values.length = contract.ctor.params.length := rfl

end ConstructorArgs

-- LIBRARY CANDIDATE: invert one successful head/tail encoder step, retaining its continuation.
theorem encodeConstructorCons {ty : ABIType} {types : List ABIType} {values : List Value}
    {headSize : Nat} {head tail encoded : List UInt8}
    (h : encodeABIValuesFrom? (ty :: types) values headSize head tail = some encoded) :
    ∃ value rest bytes, values = value :: rest ∧ encodeABIValue? ty value = some bytes ∧
      encodeABIValuesFrom? types rest headSize
        (head ++ if isDynamicABIType ty then natBytes (headSize + tail.length) else bytes)
        (if isDynamicABIType ty then tail ++ bytes else tail) = some encoded := by
  cases values with
  | nil => simp only [encodeABIValuesFrom?] at h; contradiction
  | cons value rest =>
    simp only [encodeABIValuesFrom?] at h
    obtain ⟨bytes, hb, hh⟩ := Option.bind_eq_some_iff.mp h
    refine ⟨value, rest, bytes, rfl, hb, ?_⟩
    by_cases hd : isDynamicABIType ty = true
    · simpa only [hd, if_true] using hh
    · simpa only [hd, if_false] using hh

-- LIBRARY CANDIDATE: successful elementary address encoding determines the source value.
theorem encodeConstructorAddress {value : Value} {bytes : List UInt8}
    (h : encodeABIValue? (.elem .address) value = some bytes) :
    ∃ a : AccountAddress, value = .address a := by
  cases value <;> simp [encodeABIValue?, encodeABIWord?] at h
  exact ⟨_, rfl⟩

-- LIBRARY CANDIDATE: successful string encoding determines its byte-array source value.
theorem encodeConstructorString {value : Value} {bytes : List UInt8}
    (h : encodeABIValue? .string value = some bytes) :
    ∃ b : ByteArray, value = .bytes b := by
  cases value <;> simp only [encodeABIValue?] at h
  all_goals try contradiction
  exact ⟨_, rfl⟩

-- LIBRARY CANDIDATE: a successfully encoded uint256 is an EVM word with its natural value.
theorem encodeConstructorWord {value : Value} {bytes : List UInt8}
    (h : encodeABIValue? (.elem (.int (.uint ⟨256, by decide⟩))) value = some bytes) :
    ∃ w : UInt256, value = .int (Int.ofNat w.toNat) := by
  cases value <;> simp only [encodeABIValue?, encodeABIWord?, bind, Option.bind] at h
  all_goals try contradiction
  rename_i i
  rw [if_neg (show (256 : Nat) ≠ 0 by decide)] at h
  by_cases hi : 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow 256)
  · rw [if_pos hi] at h
    have hlt : i.toNat < UInt256.size := Int.toNat_lt hi.1 |>.mpr hi.2
    refine ⟨UInt256.ofNat i.toNat, ?_⟩
    rw [UInt256.toNat_ofNat_of_lt hlt]
    exact congrArg Value.int (Int.toNat_of_nonneg hi.1).symm
  · rw [if_neg hi] at h
    contradiction

theorem constructorEncoding_shape {values : List Value} {encoded : List UInt8}
    (h : encodeABIValues? (contract.ctor.params.map Param.ty) values = some encoded) :
    ∃ a : ConstructorArgs, values = a.values ∧ encoded = a.encoded := by
  have horig := h
  rw [ConstructorArgs.params] at h
  simp only [encodeABIValues?, abiTupleHeadSize?, isDynamicABIType,
    staticABIEncodedSize?, Bool.false_eq_true, if_false, if_true, bind, Option.bind] at h
  change encodeABIValuesFrom?
    [.elem .address, .elem .address, .elem (.int (.uint ⟨256, by decide⟩)),
      .elem .address, .string, .string] values 192 [] [] = some encoded at h
  obtain ⟨owner, vs1, _, rfl, ho, h1⟩ := encodeConstructorCons h
  obtain ⟨owner, rfl⟩ := encodeConstructorAddress ho
  obtain ⟨morpho, vs2, _, rfl, hm, h2⟩ := encodeConstructorCons h1
  obtain ⟨morpho, rfl⟩ := encodeConstructorAddress hm
  obtain ⟨timelock, vs3, _, rfl, ht, h3⟩ := encodeConstructorCons h2
  obtain ⟨timelock, rfl⟩ := encodeConstructorWord ht
  obtain ⟨asset, vs4, _, rfl, ha, h4⟩ := encodeConstructorCons h3
  obtain ⟨asset, rfl⟩ := encodeConstructorAddress ha
  obtain ⟨name, vs5, _, rfl, hn, h5⟩ := encodeConstructorCons h4
  obtain ⟨name, rfl⟩ := encodeConstructorString hn
  obtain ⟨symbol, vs6, _, rfl, hs, h6⟩ := encodeConstructorCons h5
  obtain ⟨symbol, rfl⟩ := encodeConstructorString hs
  have hnil : vs6 = [] := by
    cases vs6 with
    | nil => rfl
    | cons value rest => simp only [encodeABIValuesFrom?] at h6; contradiction
  subst vs6
  let a : ConstructorArgs := ⟨owner, morpho, timelock, asset, name, symbol⟩
  refine ⟨a, rfl, ?_⟩
  exact Option.some.inj (horig.symm.trans a.encode)

theorem constructorDeployment_shape {args : List Value} {code : ByteArray}
    (h : config.selfDeployment metaMorphoV1_1CreationBytecode args = some code) :
    ∃ a : ConstructorArgs, args = a.values ∧
      code = metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray := by
  change (do
    let bytes ← encodeABIValues? (contract.ctor.params.map Param.ty) args
    pure (metaMorphoV1_1CreationBytecode ++ bytes.toByteArray)) = some code at h
  obtain ⟨bytes, hb, hc⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, rfl, rfl⟩ := constructorEncoding_shape hb
  exact ⟨a, rfl, (Option.some.inj hc).symm⟩

theorem metaMorphoV1_1CreationBytecode_size : metaMorphoV1_1CreationBytecode.size = 23666 := by
  native_decide

theorem constructorDeployment_bounded_shape {args : List Value} {code : ByteArray}
    {I : ExecutionEnv}
    (h : config.selfDeployment metaMorphoV1_1CreationBytecode args = some code)
    (hcode : I.code = code) (hsize : I.code.size < UInt256.size) :
    ∃ a : ConstructorArgs, args = a.values ∧
      I.code = metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray ∧
      23666 + a.encoded.length < UInt256.size := by
  obtain ⟨a, rfl, rfl⟩ := constructorDeployment_shape h
  refine ⟨a, rfl, hcode, ?_⟩
  simpa only [hcode, ByteArray.size_append, metaMorphoV1_1CreationBytecode_size,
    List.size_toByteArray] using hsize

/-- The approved deployment bound makes the initial `CODESIZE - 23666` exact. -/
theorem constructorCodeSize {tail : ByteArray}
    (hsize : (metaMorphoV1_1CreationBytecode ++ tail).size < UInt256.size) :
    UInt256.sub (UInt256.ofNat (metaMorphoV1_1CreationBytecode ++ tail).size)
      (UInt256.ofNat 23666) = UInt256.ofNat tail.size := by
  have htail : tail.size < UInt256.size := by
    simp only [ByteArray.size_append, metaMorphoV1_1CreationBytecode_size] at hsize
    omega
  apply u256_inj
  rw [usub_ofNat_lit_toNat (by
      simp only [ByteArray.size_append, metaMorphoV1_1CreationBytecode_size]; omega) hsize,
    ByteArray.size_append, metaMorphoV1_1CreationBytecode_size, Nat.add_sub_cancel_left,
    UInt256.toNat_ofNat_of_lt htail]

end Benchmarks.Morpho.MetaMorphoV1_1
