import Benchmarks.EAS.EAS.WordArrayBridge
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def timeArrayWord (ee : ExecutionEnv) (start i : UInt256) : UInt256 :=
  calldataWord ee.calldata (UInt256.shiftLeft i (UInt256.ofNat 5) + start).toNat

end Benchmarks.EAS.EAS
