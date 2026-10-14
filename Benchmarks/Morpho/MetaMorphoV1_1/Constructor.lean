import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorInputSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorHeadDecode
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStringsSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorLiteralSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStorageInit
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDecimalsInit
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorAssetInit
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainInit
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorOwnershipInit
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorTimelockInit
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorSetTimelockInit
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultSymbolInit
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStrictDecimalsInit
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorApproveInit
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorSuccess
import Stele.RefineWithCodeBound

/-!
# MetaMorphoV1_1 constructor correctness

Creation-code equivalence: the constructor's EVM trace (argument decode, stores, runtime-code
return) against the Stele constructor body, composed from the creation summaries.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

theorem metaMorphoV1_1ConstructorCorrect :
    typedConstructorRefinementWithCodeBound config metaMorphoV1_1CreationBytecode contract (immutableLayout.deployed metaMorphoV1_1Bytecode) := by
  intro σ σ₀ g A I args deployed hdeploy hcode hcalldata hperm hsize
  obtain ⟨a, rfl, hcode, hbound⟩ := constructorDeployment_bounded_shape hdeploy hcode hsize
  by_cases hv : I.weiValue = ⟨0⟩
  · by_cases hfit : SourceMemory.allocationFits ⟨480⟩ (UInt256.ofNat a.encoded.length)
    · obtain ⟨aw, k, C, rd⟩ := constructorReachArgumentMemory (σ := σ) (σ₀ := σ₀)
        (A := A) (g := Sat256.ofUInt256 g) a hcode hv hbound hfit
      obtain ⟨aw1, k1, C1, hhead⟩ := constructorDecodeHead a rd
      have hsmall := (SourceMemory.constructorFirstAllocation_iff a hbound).mp hfit
      by_cases hname : a.nameEnd < 2 ^ 64
      · obtain ⟨aw2, k2, C2, hnameRead⟩ := constructorDecodeName a hsmall hname hhead
        by_cases hsymbol : a.stringsEnd < 2 ^ 64
        · obtain ⟨aw3, k3, C3, hstrings⟩ := constructorDecodeSymbol a hbound hsmall hname hsymbol hnameRead
          rcases constructorLiteralAllocations a.asset a.stringsEnd (by simp)
            (by unfold ConstructorArgs.stringsEnd ConstructorArgs.nameEnd ConstructorArgs.argumentEnd; omega)
            hsymbol (constructorStringsMemory_free a hbound hsmall) hstrings with hfail | hready
          · exact constructorLiteralAllocationFailure a hcode hv hbound hsmall hname hsymbol hfail.1 hfail.2
          · obtain ⟨hliteral, aw4, k4, C4, hliterals⟩ := hready
            have hsource := constructorLiteralSourcePrefix a
              (initState σ σ₀ (Sat256.ofUInt256 g) A I) hv hbound hsmall hname hsymbol hliteral
            rcases constructorStorageInit a SourceState.init hperm
              (by unfold ConstructorArgs.stringsEnd ConstructorArgs.nameEnd ConstructorArgs.argumentEnd; omega)
              (by change a.stringsEnd + 160 < 2 ^ 256; omega) hliterals with hfail | hstores
            · exact constructorRefinementOfRevert hcode hfail.2
                (constructorSourceRevertOfPrefix a hsource hfail.1)
            · obtain ⟨mem5, aw5, k5, C5, hstoreSource, hs5, hp5, hf5, hstores⟩ := hstores
              obtain ⟨hmem0, hzero0⟩ := constructorVersionMemory_zero a hbound hsmall
              have hmem5 := le_trans hmem0 (hp5 128).size
              have hzero5 := ((hp5 128).load ⟨96⟩ (by decide) (by decide) hmem0).trans hzero0
              rcases constructorDecimalsInit a hs5 hliteral hmem5 hzero5 hf5 hstores with
                hfail | hdecimals
              · exact constructorRefinementOfRevert hcode hfail.2
                  (constructorSourceRevertOfPrefix a hsource (hstoreSource _ hfail.1))
              · obtain ⟨evm6, ok, out, aw6, k6, C6, hdecimalSource, hs6, hc6, hlo6, hp6, hf6, hdecimals⟩ := hdecimals
                obtain ⟨aw7, k7, C7, hassets⟩ := constructorAssetInit a ok out
                  (by unfold ConstructorArgs.stringsEnd ConstructorArgs.nameEnd ConstructorArgs.argumentEnd; omega)
                  (by change a.stringsEnd + 160 < 2 ^ 256; omega)
                  ((hp5 (a.stringsEnd + 160)).trans hp6) hdecimals
                have hassetSource (result : ExecResult) := constructorAssetReadySource a ok out evm6 (result := result)
                rcases constructorDomainInit a ok out hs6.env
                  (by unfold ConstructorArgs.stringsEnd ConstructorArgs.nameEnd ConstructorArgs.argumentEnd; omega)
                  (by change a.stringsEnd + 160 < 2 ^ 256; omega)
                  ((hp5 (a.stringsEnd + 160)).trans hp6) hc6 hlo6 hf6 hassets with hfail | hdomain
                · exact constructorRefinementOfRevert hcode hfail.2
                    (constructorSourceRevertOfPrefix a hsource
                      (hstoreSource _ (hdecimalSource _ (hassetSource _ hfail.1))))
                · obtain ⟨howner, hcursor8, hdomainSource, aw8, k8, C8, hdomain⟩ := hdomain
                  rcases constructorOwnershipInit a ok out hs6 hperm (by omega) hdomain with hfail | hownership
                  · exact constructorRefinementOfRevert hcode hfail.2
                      (constructorSourceRevertOfPrefix a hsource
                        (hstoreSource _ (hdecimalSource _ (hassetSource _ (hdomainSource _ hfail.1)))))
                  · obtain ⟨hmorpho, hownershipSource, hs9, aw9, k9, C9, hownership⟩ := hownership
                    rcases constructorTimelockInit (evm := ownershipState evm6 (UInt256.ofNat a.owner.val))
                      a ok out _ hownership with hfail | htimelock
                    · exact constructorRefinementOfRevert hcode hfail.2
                        (constructorSourceRevertOfPrefix a hsource
                          (hstoreSource _ (hdecimalSource _ (hassetSource _
                            (hdomainSource _ (hownershipSource _ hfail.1))))))
                    · obtain ⟨htime, htimeSource, aw10, k10, C10, htimelock⟩ := htimelock
                      obtain ⟨hsetTimeSource, hs11, hname11, hsymbol11, aw11, k11, C11, htimeSet⟩ :=
                        constructorSetTimelockInit a ok out hs9 hperm hbound hsmall hname
                          (by omega) hcursor8 ((hp5 (a.stringsEnd + 160)).trans hp6) htimelock
                      rcases constructorVaultNameInit a ok out hs11 hperm hsmall hname
                          (by omega) hname11 hsymbol11 htimeSet with hfail | hnameSet
                      · exact constructorRefinementOfRevert hcode hfail.2
                          (constructorSourceRevertOfPrefix a hsource
                            (hstoreSource _ (hdecimalSource _ (hassetSource _
                              (hdomainSource _ (hownershipSource _ (htimeSource _
                                (hsetTimeSource _ hfail.1))))))))
                      · obtain ⟨hnameSource, hs12, mem12, aw12, k12, C12, hname12, hsymbol12,
                          hp12, hf12, hnameSet⟩ := hnameSet
                        obtain ⟨hsymbol13, hp13, hf13, aw13, k13, C13, hnameEvent⟩ :=
                          constructorVaultNameEvent a ((constructorDecimalsCursor a out).toNat + 192)
                            hperm hsmall hname hcursor8 (by omega) hname12 hsymbol12 hf12 hnameSet
                        rcases constructorVaultSymbolInit a ok out
                            ((constructorDecimalsCursor a out).toNat + 192) hs12 hperm hsmall hname
                            hcursor8 (by omega) hsymbol13 hf13 hnameEvent with hfail | hsymbolSet
                        · have hbeforeEvent := constructorVaultEmitPrefix
                            (frame := constructorTimelockReadyFrame a ok out I) false
                            (constructorTimelockReadyFrame_string a ok out I false) hfail.1
                          exact constructorRefinementOfRevert hcode hfail.2
                            (constructorSourceRevertOfPrefix a hsource
                              (hstoreSource _ (hdecimalSource _ (hassetSource _
                                (hdomainSource _ (hownershipSource _ (htimeSource _
                                  (hsetTimeSource _ (hnameSource _ hbeforeEvent)))))))))
                        · obtain ⟨hsymbolSource, hs14, mem14, aw14, k14, C14, hp14, hf14,
                            hsymbolSet⟩ := hsymbolSet
                          have hm14 : 96 ≤ mem14.size := by
                            have hbuf := hsymbol13.size
                            have hpres := hp14.size
                            have hnlo : 96 ≤ a.nameEnd := by
                              unfold ConstructorArgs.nameEnd ConstructorArgs.argumentEnd; omega
                            omega
                          rcases constructorStrictDecimalsInit a ok out hs14 hperm hm14
                              (by
                                have hbase : 480 ≤ a.stringsEnd := by
                                  unfold ConstructorArgs.stringsEnd ConstructorArgs.nameEnd
                                    ConstructorArgs.argumentEnd
                                  omega
                                omega) hcursor8 hf14 hsymbolSet with hfail | hstrict
                          · have hbeforeEvent := constructorVaultEmitPrefix
                              (frame := constructorTimelockReadyFrame a ok out I) false
                              (constructorTimelockReadyFrame_string a ok out I false)
                              (hsymbolSource _ hfail.1)
                            exact constructorRefinementOfRevert hcode hfail.2
                              (constructorSourceRevertOfPrefix a hsource
                                (hstoreSource _ (hdecimalSource _ (hassetSource _
                                  (hdomainSource _ (hownershipSource _ (htimeSource _
                                    (hsetTimeSource _ (hnameSource _ hbeforeEvent)))))))))
                          · obtain ⟨evm15, out15, aw15, k15, C15, hlong15, hout15, hdecimals15,
                              halloc15, hs15, hstrictSource, hstrict⟩ := hstrict
                            have hlo : 480 ≤ a.stringsEnd := by
                              unfold ConstructorArgs.stringsEnd ConstructorArgs.nameEnd
                                ConstructorArgs.argumentEnd
                              omega
                            have hstrictPtr : (constructorStrictDecimalsPtr a out).toNat =
                                (constructorDecimalsCursor a out).toNat + 192 :=
                              UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)
                            have hzeroPrefix :=
                              (hp6.mono (show 128 ≤ a.stringsEnd + 160 by omega)).trans
                                ((constructorTimelockMemory_zeroPrefix _ a ok out I (by omega)).trans
                                  ((hp12 128).trans ((hp13.mono (by omega)).trans (hp14.mono (by omega)))))
                            have hmem14 : 128 ≤ mem14.size := le_trans hmem5 hzeroPrefix.size
                            have hzero14 := (hzeroPrefix.load ⟨96⟩ (by decide) (by decide) hmem5).trans hzero5
                            have hprefix15 := constructorFinalDecimalsMemory_prefix mem14 a out out15
                              (by rw [hstrictPtr]; omega) hlong15 (by change _ < 2 ^ 256; omega)
                            have hmem15 := le_trans hmem14 hprefix15.size
                            have hzero15 := (hprefix15.load ⟨96⟩ (by decide) (by decide) hmem14).trans hzero14
                            rcases constructorApproveInit a ok out out15 hmem15 hzero15
                                (by rw [hstrictPtr]; omega) halloc15 hdecimals15
                                (constructorStrictDecimalsMemory_free _ _ _) hs15 hstrict with hfail | happroved
                            · have hbeforeEvent := constructorVaultEmitPrefix
                                (frame := constructorTimelockReadyFrame a ok out I) false
                                (constructorTimelockReadyFrame_string a ok out I false)
                                (hsymbolSource _ (hstrictSource _ hfail.1))
                              exact constructorRefinementOfRevert hcode hfail.2
                                (constructorSourceRevertOfPrefix a hsource
                                  (hstoreSource _ (hdecimalSource _ (hassetSource _
                                    (hdomainSource _ (hownershipSource _ (htimeSource _
                                      (hsetTimeSource _ (hnameSource _ hbeforeEvent)))))))))
                            · obtain ⟨evm16, mem16, out16, cursor16, aw16, x0, x1, x2, x3, k16, C16,
                                happSource, hs16, hp16, hf16, hbound16, hlo16, hfinal⟩ := happroved
                              obtain ⟨hm16, hwords16⟩ := constructorApprovalMemory_immutable a ok out out15 I
                                (by omega) (by rw [hstrictPtr]; omega) hlong15
                                (by change _ < 2 ^ 256; omega)
                                ((hp12 416).trans ((hp13.mono (by omega)).trans (hp14.mono (by omega)))) hp16
                              have hreturn := constructorRuntime hm16 hlo16 hbound16 hf16 hfinal
                              rw [constructorDeployedCode a ok out I out15 _ hwords16,
                                ← constructorFinalFrame_immutables a ok out I out15 cursor16] at hreturn
                              have hbeforeEvent := constructorVaultEmitPrefix
                                (frame := constructorTimelockReadyFrame a ok out I) false
                                (constructorTimelockReadyFrame_string a ok out I false)
                                (hsymbolSource _ (hstrictSource _ happSource))
                              exact constructorRefinementOfSuccess hcode hreturn
                                (constructorSourceSuccessOfPrefix a hsource
                                  (hstoreSource _ (hdecimalSource _ (hassetSource _
                                    (hdomainSource _ (hownershipSource _ (htimeSource _
                                      (hsetTimeSource _ (hnameSource _ hbeforeEvent)))))))))
                                (by rw [constructorFinalFrame_immutables]; exact constructorFinalImms_fit a ok out I out15)
        · exact constructorSymbolAllocationFailure a hcode hv hbound hsmall hname hsymbol hnameRead
      · exact constructorNameAllocationFailure a hcode hv hbound hsmall hname hhead
    · exact constructorInitialAllocationFailure a hcode hv hsize hfit
  · exact constructorNonpayable a hcode hv

end Benchmarks.Morpho.MetaMorphoV1_1
