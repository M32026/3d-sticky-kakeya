import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentSelectionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentQuantitativeEnvelopeStatements

/-!
# Uniform absorption for the one-parent source selection

The complete parent fiber is a subfamily of the prepared essentially-distinct
line family.  Its logarithmic cardinality loss and the fixed tree-depth loss
are therefore absorbed by the two fixed paper-refinement exponents.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedOneParentSelectionAbsorptionData
    (sourceLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb :
    ∀ {delta stableLoss : ℝ},
      0 < delta →
      delta ≤ delta₀ →
      ∀ {source : Kakeya.Streamlined.TubeFamily delta},
        ∀ {shading : WZ1PaperTubeShading source},
          ∀ {caller : Kakeya.Streamlined.AdmissibleScale delta},
            ∀ {preparationExponent : ℕ},
              ∀ (prepared :
                  WZ2PaperCallerStrictPreparationData
                    (sourceLoss := sourceLoss)
                    (stableLoss := stableLoss)
                    shading caller preparationExponent),
                ∀ parent : Fin prepared.callerStrict.coarse.card,
                  delta ≤ 1 / 10000 ∧
                    wz1PaperRefinementFraction delta 2 *
                          (packingConstant10000 : ENNReal) ≤
                        1 ∧
                    (let branchLoss : ENNReal :=
                        (2 : ENNReal) ^
                          (wz2PaperPreparedOneParentFineScaleCount
                            prepared parent)
                      let bandLoss : ENNReal :=
                        (Nat.log 2
                            (wz2PaperPreparedOneParentFiber
                              prepared parent).family.card +
                          1 : ENNReal)
                      wz1PaperRefinementFraction delta 2 *
                          (branchLoss * bandLoss) ≤
                        1)

def WZ2PropStickyPreparedOneParentSelectionAbsorptionStatement : Prop :=
  ∀ sourceLoss : ℝ,
    0 < sourceLoss →
      Nonempty
        (WZ2PaperPreparedOneParentSelectionAbsorptionData sourceLoss)

end Kakeya.Assouad

end
