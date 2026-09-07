import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-!
# Essential distinctness under the paper unit rescaling

This is the lower-distortion input used in WZ Lemma 3.3 and in the WZ2
Section 6 analogue `prop: sticky`.

The paper states:

> `rho⁻¹ d(ell₁, ell₂) ≲ d(phi(ell₁), phi(ell₂))`.

The fixed constant `10000` absorbs the canonical Lean choice
`c(3) = 1 / 100` in the transverse unit rescaling and the bounded
re-intersection error at the target plane `z = 0`.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Strong separation of a selected source full-fiber subfamily implies ordinary
paper essential distinctness of the corresponding stable target subfamily.

All families and the coarse parent lie in the paper's fixed line class
`L₃`.  Axis provenance comes from the supplied unit-rescaled full-fiber data;
no particular target-tube constructor is assumed.
-/
def WZ2PaperStrongSourceSeparationTransferStatement : Prop :=
  ∀ {delta rho : ℝ},
    0 < delta → delta ≤ rho →
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ (cover : WZ2PaperPartitioningCover fine coarse),
          ∀ parent : Fin coarse.card,
            ∀ hrho : 0 < rho,
              rho ≤ 1 →
              WZ1PaperTubeInLineClass (coarse.tube parent) →
              ∀ {C : ENNReal},
                ∀ data :
                    WZ2PaperUnitRescaledFamilyData
                      cover parent hrho C,
                  ∀ selected :
                      Kakeya.Streamlined.TubeSubfamily
                        (cover.fullFiberSubfamily parent).family,
                    WZ1PaperIsLineClass selected.family →
                    (∀ first second, first ≠ second →
                      10000 * delta <
                        wz1PaperLineDistance
                          (selected.family.tube first)
                          (selected.family.tube second)) →
                      WZ1PaperIsEssentiallyDistinct
                        (data.targetSubfamilyForSource
                          selected).family

end Kakeya.Assouad
