import Benchmarks.EAS.EAS.AttestIterationRun
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def attestRequestSite (site : UIDSite) (ptr : UInt256) : UIDSite :=
  match site with
  | .single .. => site
  | .many s1 s2 s3 s4 s5 _ => .many s1 s2 s3 s4 s5 ptr

def attestRequestT3 (site : UIDSite) (t3 ptr : UInt256) : UInt256 :=
  match site with
  | .single .. => ptr
  | .many .. => t3

@[simp] theorem attestRequestSite_ref (site : UIDSite) (t3 ptr : UInt256) :
    refUIDPtr (attestRequestSite site ptr) (attestRequestT3 site t3 ptr) = ptr := by cases site <;> rfl
@[simp] theorem attestRequestSite_readPC (site : UIDSite) (ptr : UInt256) :
    requestReadPC (attestRequestSite site ptr) = requestReadPC site := by cases site <;> rfl
@[simp] theorem attestRequestSite_nextPC (site : UIDSite) (ptr : UInt256) :
    recordNextPC (attestRequestSite site ptr) = recordNextPC site := by cases site <;> rfl
@[simp] theorem attestRequestSite_nextStack (site : UIDSite) (ptr schema idx t3 t4 : UInt256) (R : List UInt256) :
    recordNextStack (attestRequestSite site ptr) schema idx (attestRequestT3 site t3 ptr) t4 R =
      recordNextStack site schema idx t3 t4 R := by cases site <;> rfl
@[simp] theorem attestRequestSite_recordArray (site : UIDSite) (t3 t4 ptr : UInt256) :
    recordArrayPtr (attestRequestSite site ptr) (attestRequestT3 site t3 ptr) t4 = recordArrayPtr site t3 t4 := by cases site <;> rfl
@[simp] theorem attestRequestSite_values (site : UIDSite) (t4 ptr : UInt256) :
    recordValuesPtr (attestRequestSite site ptr) t4 = recordValuesPtr site t4 := by cases site <;> rfl
@[simp] theorem attestRequestSite_requests (site : UIDSite) (ptr : UInt256) (mem : ByteArray) :
    attestRequestArrayPtr (attestRequestSite site ptr) mem = attestRequestArrayPtr site mem := by cases site <;> rfl
@[simp] theorem attestRequestSite_schema (site : UIDSite) (ptr : UInt256) :
    requestSchemaPtr (attestRequestSite site ptr) = requestSchemaPtr site := by cases site <;> rfl
@[simp] theorem attestRequestSite_attester (site : UIDSite) (ptr : UInt256) (mem : ByteArray) :
    recordCreateAttester (attestRequestSite site ptr) mem = recordCreateAttester site mem := by cases site <;> rfl
@[simp] theorem attestRequestSite_uids (site : UIDSite) (ptr : UInt256) (mem : ByteArray) :
    recordUIDsPtr (attestRequestSite site ptr) mem = recordUIDsPtr site mem := by cases site <;> rfl
@[simp] theorem attestRequestSite_result (site : UIDSite) (ptr : UInt256) (mem : ByteArray) :
    recordResultPtr (attestRequestSite site ptr) mem = recordResultPtr site mem := by cases site <;> rfl
@[simp] theorem attestRequestSite_tail (site : UIDSite) (ptr src t3 t4 value uidPtr word : UInt256) (i : Nat) (mem : ByteArray) :
    recordTailMemory mem (attestRequestSite site ptr) src (attestRequestT3 site t3 ptr) t4 value uidPtr word i =
      recordTailMemory mem site src t3 t4 value uidPtr word i := by cases site <;> rfl

end Benchmarks.EAS.EAS
