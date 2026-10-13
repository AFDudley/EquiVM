import Benchmarks.EAS.EAS.MultiDelegatedAttestSource
open Stele Benchmarks.EAS.EAS
#eval reprStr ((lookupCallable? contract "_calldataWord").get!).body
#eval reprStr ((lookupCallable? contract "_checkAttestationArrayCopy").get!).body
