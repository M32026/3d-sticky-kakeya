import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentUniformAbsorptionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperStructuralParentwiseMergeStatements

/-!
# Uniform structural production over every prepared caller parent

Apply the one-parent structural producer to every complete caller fiber using
one common critical-floor choice and one common small-scale threshold, then
merge the resulting refinements before any global balancing.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedParentwiseStructuralProducerData
    {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss) where
  fiberProducer :
    ∀ parent : Fin prepared.callerStrict.coarse.card,
      WZ2PaperPreparedOneParentStructuralProducerData
        (outputLoss := outputLoss) prepared parent critical
  pure_nested_absorption :
    ∀ parent : Fin prepared.callerStrict.coarse.card,
      (81000000 : ENNReal) *
          (fiberProducer parent).restrictedConstant ≤
        (fiberProducer parent).targetConstant
  pure_window_absorption :
    ∀ parent : Fin prepared.callerStrict.coarse.card,
      (200 : ENNReal) * prepared.structuralConstant ≤
        (fiberProducer parent).targetConstant
  merged :
    WZ2PaperStructuralParentwiseMergeData
      prepared.callerStrict.cover
      prepared.refinement.refined
      prepared.callerStrict.rho_pos
      4
      (fun parent => (fiberProducer parent).structural)
  merged_selected_card_eq :
    merged.merged.refinement.selected.family.card =
      ∑ parent : Fin prepared.callerStrict.coarse.card,
        (fiberProducer parent).selection.refinement.selected.family.card

def WZ2PropStickyPreparedParentwiseStructuralProducerStatement : Prop :=
  ∀ {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ},
    ∀ {source : Kakeya.Streamlined.TubeFamily delta},
      ∀ {shading : WZ1PaperTubeShading source},
        ∀ {caller : Kakeya.Streamlined.AdmissibleScale delta},
          ∀ {preparationExponent : ℕ},
            ∀ (prepared :
                WZ2PaperCallerStrictPreparationData
                  (sourceLoss := sourceLoss)
                  (stableLoss := stableLoss)
                  shading caller preparationExponent),
              ∀ (critical :
                  WZ2PaperCriticalFloorSelectionData
                    sigma floorLoss strongLoss),
                ∀ (uniform :
                    WZ2PaperPreparedOneParentUniformAbsorptionData
                      sourceLoss stableLoss floorLoss strongLoss
                      outputLoss critical),
                  0 < delta →
                  delta ≤ uniform.delta₀ →
                  Real.rpow delta (1 - outputLoss) ≤ caller.1 →
                  caller.1 ≤ Real.rpow delta outputLoss →
                  0 < floorLoss →
                  floorLoss < strongLoss →
                  3 * strongLoss ≤ outputLoss →
                  Nonempty
                    (WZ2PaperPreparedParentwiseStructuralProducerData
                      (outputLoss := outputLoss) prepared critical)

end Kakeya.Assouad

end
