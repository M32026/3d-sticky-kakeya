import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralFinalFiberStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRelativeMultiplicityNormalizationStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityNormalizationStatements

/-!
# Corrected literal-paper global output for `prop: sticky`

Item (ii) is stated directly for the final full fiber.  In particular, the
output does not hide another refinement inside each fiber after the global
balanced shading has already been selected.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperLiteralPropStickyDataV2
    {delta sigma loss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (logExponent : ℕ) where
  strongLoss : ℝ
  strongLoss_pos : 0 < strongLoss
  strongLoss_budget : 3 * strongLoss ≤ loss
  refinement : WZ1PaperRefinement shading logExponent
  refined_cubical :
    WZ1PaperIsCubicalShading refinement.refined
  coarse : Kakeya.Streamlined.TubeFamily rho.1
  cover :
    WZ2PaperPartitioningCover refinement.selected.family coarse
  coarseShading : WZ1PaperTubeShading coarse
  balanced :
    WZ1PaperBalancedCoverData
      cover.toWZ1PaperTubeCover
      refinement.refined coarseShading
  coarse_extremal_strong :
    WZ2PaperIsExtremal
      sigma strongLoss coarse coarseShading
  coarse_extremal :
    WZ2PaperIsExtremal
      sigma loss coarse coarseShading
  coarse_multiplicity_upper_strong :
    ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN rho.1
            (2 - sigma - strongLoss) *
          coarse.enncard
  coarse_cardinality_lower :
    Kakeya.realRpowENN rho.1
        (-2 + 2 * strongLoss) ≤
      coarse.enncard
  literalRescaledFiber :
    ∀ parent : Fin coarse.card,
      Nonempty
        (WZ2PaperLiteralFinalFiberData
          (sigma := sigma)
          (strongLoss := strongLoss)
          (outputLoss := loss)
          (restrictPaperShading
            (cover.fullFiberSubfamily parent)
            refinement.refined)
          (coarse.tube parent)
          coarse_extremal.delta_pos)
  coarse_multiplicity_upper :
    ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN rho.1 (2 - sigma - loss) *
          coarse.enncard
  fiber_multiplicity_upper :
    ∀ parent : Fin coarse.card,
      ∀ point,
        (wz2PaperFullFiberPointMultiplicity
            coarse refinement.refined parent point : ENNReal) ≤
          Kakeya.realRpowENN (delta / rho.1)
              (2 - sigma - loss) *
            wz2PaperFullFiberCount
              refinement.selected.family coarse parent

def WZ2PaperLiteralPropStickyStatementV2 : Prop :=
  ∃ logExponent : ℕ,
  ∀ sigma : ℝ,
    0 < sigma → sigma < 1 →
    HasWZ2PaperCriticalVolumeFloor sigma →
      ∀ outputLoss : ℝ, 0 < outputLoss →
        ∃ inputLoss delta₀ : ℝ,
          0 < inputLoss ∧
          0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ source : Kakeya.Streamlined.TubeFamily delta,
              ∀ shading : WZ1PaperTubeShading source,
                WZ2PaperExactScaleExtremal
                    sigma inputLoss source shading →
                  ∀ rho :
                      Kakeya.Streamlined.AdmissibleScale delta,
                    Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                    rho.1 ≤ Real.rpow delta outputLoss →
                      Nonempty
                        (WZ2PaperLiteralPropStickyDataV2
                          (sigma := sigma) (loss := outputLoss)
                          shading rho logExponent)

def WZ2PaperLiteralPropStickyAssemblyV2Statement : Prop :=
  WZ2PropStickyPaperMultiplicityNormalizationStatement →
  WZ2PaperRelativeMultiplicityNormalizationStatement →
  ∀ {delta sigma loss : ℝ},
    ∀ {source : Kakeya.Streamlined.TubeFamily delta},
      ∀ (shading : WZ1PaperTubeShading source),
        ∀ (rho : Kakeya.Streamlined.AdmissibleScale delta),
          ∀ (logExponent : ℕ),
            ∀ (strongLoss : ℝ),
              0 < strongLoss →
              3 * strongLoss ≤ loss →
              ∀ (refinement : WZ1PaperRefinement shading logExponent),
                WZ1PaperIsCubicalShading refinement.refined →
                ∀ (coarse :
                    Kakeya.Streamlined.TubeFamily rho.1),
                  ∀ (cover :
                      WZ2PaperPartitioningCover
                        refinement.selected.family coarse),
                    ∀ (coarseShading :
                        WZ1PaperTubeShading coarse),
                      ∀ (balanced :
                          WZ1PaperBalancedCoverData
                            cover.toWZ1PaperTubeCover
                            refinement.refined coarseShading),
                        ∀ (coarseExtremalStrong :
                            WZ2PaperIsExtremal
                              sigma strongLoss coarse coarseShading),
                          ∀ (coarseExtremal :
                              WZ2PaperIsExtremal
                                sigma loss coarse coarseShading),
                            (∀ point,
                              (coarseShading.pointMultiplicity point :
                                  ENNReal) ≤
                                Kakeya.realRpowENN rho.1
                                    (2 - sigma - strongLoss) *
                                  coarse.enncard) →
                            Kakeya.realRpowENN rho.1
                                (-2 + 2 * strongLoss) ≤
                              coarse.enncard →
                            (∀ parent : Fin coarse.card,
                              Nonempty
                                (WZ2PaperLiteralFinalFiberData
                                  (sigma := sigma)
                                  (strongLoss := strongLoss)
                                  (outputLoss := loss)
                                  (restrictPaperShading
                                    (cover.fullFiberSubfamily parent)
                                    refinement.refined)
                                  (coarse.tube parent)
                                  coarseExtremal.delta_pos)) →
                            Nonempty
                              (WZ2PaperLiteralPropStickyDataV2
                                (sigma := sigma)
                                (loss := loss)
                                shading rho logExponent)

end Kakeya.Assouad

end
