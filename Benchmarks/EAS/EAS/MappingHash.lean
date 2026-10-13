import Benchmarks.EAS.EAS.Common
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: the KECCAK opcode view of the two-word mapping hash routine.
theorem mappingHash (key slot : UInt256) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (slot.toByteArray.write 0 (key.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
        (UInt256.ofNat 32).toNat 32) = solcMappingSlot slot key :=
  twoWordHashMem_solcMappingSlot_any slot key mem

end Benchmarks.EAS.EAS
