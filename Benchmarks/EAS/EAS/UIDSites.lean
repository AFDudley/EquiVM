import Benchmarks.EAS.EAS.UIDFields
import Benchmarks.EAS.EAS.UIDHeadMemory
import Benchmarks.EAS.EAS.RuntimeBlocks_030
import Benchmarks.EAS.EAS.RuntimeBlocks_035
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

inductive UIDSite where
  | single (s1 s2 s3 s4 s5 s6 s7 s8 : UInt256)
  | many (s1 s2 s3 s4 s5 s6 : UInt256)

def uidStartPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 8110
  | .many .. => UInt256.ofNat 10326
def uidHeadPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 8254
  | .many .. => UInt256.ofNat 10470
def uidCopyReturnPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 8374
  | .many .. => UInt256.ofNat 10590
def uidHashPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 8473
  | .many .. => UInt256.ofNat 10689
def uidDonePC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 8477
  | .many .. => UInt256.ofNat 10693
def uidSaved (site : UIDSite) (src : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single s1 s2 s3 s4 s5 s6 s7 s8 => s1::s2::s3::s4::s5::s6::s7::s8::src::R
  | .many s1 s2 s3 s4 s5 s6 => s1::s2::s3::s4::s5::s6::src::R

def uidHeadStack (mem : ByteArray) (src heap dataPtr : UInt256) (a : AttestationRecord) (R : List UInt256) : List UInt256 :=
  heap::UInt256.ofNat 84::UInt256.shiftLeft (UInt256.ofNat a.attester.val) (UInt256.ofNat 96)::
    memLoad (src+UInt256.ofNat 64) mem::memLoad (src+UInt256.ofNat 96) mem::a.revocable.toUInt256::a.refUID::
    dataPtr::heap::R

end Benchmarks.EAS.EAS
