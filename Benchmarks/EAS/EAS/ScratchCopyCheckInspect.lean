import Benchmarks.EAS.EAS.MultiDelegatedAttestSource
open Solm Benchmarks.EAS.EAS
#eval reprStr ((lookupCallable? contract "_calldataWord").get!).body
#eval reprStr ((lookupCallable? contract "_checkAttestationArrayCopy").get!).body
