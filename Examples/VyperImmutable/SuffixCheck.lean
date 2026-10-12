import Examples.VyperImmutable.ImmutableCode

open Solm

namespace Examples.VyperImmutable

private def sampleImmutables : Store :=
  ((∅ : Store).insert "OWNER" (.address (.ofNat 1)))
    |>.insert "LIMIT" (.int 7)
    |>.insert "TAG" (.fixedBytes ⟨3, by decide⟩ [0xde, 0xad, 0xbe, 0xef])

#guard immutableLayout.suffix? sampleImmutables =
  some ((Ethereum.UInt256.toByteArray (.ofNat 1)) ++
    (Ethereum.UInt256.toByteArray (.ofNat 7)) ++
    ByteArray.mk (#[0xde, 0xad, 0xbe, 0xef] ++ Array.replicate 28 0))

#guard immutableLayout.suffixWords (Reasoning.VyperImmutables.wordsOf sampleImmutables) =
  (immutableLayout.suffix? sampleImmutables).getD (ByteArray.zeroes immutableLayout.size)

#guard (deployedRuntime sampleImmutables).size = immutableBytecode.size + 96

#guard ((deployedRuntime sampleImmutables).write immutableBytecode.size
    ByteArray.empty 64 96).readWithPadding 128 32 =
  ByteArray.mk (#[0xde, 0xad, 0xbe, 0xef] ++ Array.replicate 28 0)

end Examples.VyperImmutable
