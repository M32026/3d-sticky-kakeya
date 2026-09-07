import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralOneParentStatements

/-!
# Reindex a literal-paper one-parent output

Two source families with the same tubes and shadings up to a finite index
equivalence represent the same paper configuration.  Transport the complete
literal one-parent output to the reindexed source family while leaving the
literal target family and shading unchanged.
-/

noncomputable section

namespace Kakeya.Assouad

def WZ2PaperLiteralOneParentReindexStatement : Prop :=
  ∀ {delta rho sigma strongLoss outputLoss : ℝ},
    ∀ {firstFamily secondFamily :
        Kakeya.Streamlined.TubeFamily delta},
      ∀ (firstShading :
          WZ1PaperTubeShading firstFamily),
        ∀ (secondShading :
            WZ1PaperTubeShading secondFamily),
          ∀ (coarse : Kakeya.DeltaTube rho),
            ∀ (hrho : 0 < rho),
              ∀ (logExponent : ℕ),
                ∀ (indexEquiv :
                    Fin secondFamily.card ≃
                      Fin firstFamily.card),
                  (∀ index,
                    secondFamily.tube index =
                      firstFamily.tube (indexEquiv index)) →
                  (∀ index,
                    secondShading.carrier index =
                      firstShading.carrier (indexEquiv index)) →
                  ∀ (data :
                      WZ2PaperLiteralLemma3_3Data
                        (sigma := sigma)
                        (strongLoss := strongLoss)
                        (outputLoss := outputLoss)
                        firstShading coarse hrho logExponent),
                    Nonempty
                      (WZ2PaperLiteralLemma3_3Data
                        (sigma := sigma)
                        (strongLoss := strongLoss)
                        (outputLoss := outputLoss)
                        secondShading coarse hrho logExponent)

end Kakeya.Assouad

end
