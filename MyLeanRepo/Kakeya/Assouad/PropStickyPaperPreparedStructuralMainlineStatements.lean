import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParameterSelection
import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedParentwiseStructuralProducerStatements

/-!
# Prepared global mainline through parentwise structural Lemma 3.3

This record stops exactly before the global coarse-parent regularization and
whole-cell balancing.  It packages no extremality or union-volume upper bound:
those are obtained only after the global `mu_fine * mu_coarse` comparison.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedStructuralMainlineData
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading source)
    (caller : Kakeya.Streamlined.AdmissibleScale delta)
    (totalExponent globalBalancingExponent : ℕ)
    (parameters :
      WZ2PaperFinalParameterSelectionData
        sigma outputLoss totalExponent globalBalancingExponent)
    (preparationSourceLoss : ℝ) where
  caller_lower_output :
    Real.rpow delta (1 - outputLoss) ≤ caller.1
  caller_upper_output :
    caller.1 ≤ Real.rpow delta outputLoss
  preparationExponent : ℕ
  prepared :
    WZ2PaperCallerStrictPreparationData
      (sourceLoss := preparationSourceLoss)
      (stableLoss := parameters.hierarchy.stableLoss)
      shading caller preparationExponent
  structural :
    WZ2PaperPreparedParentwiseStructuralProducerData
      (outputLoss := outputLoss) prepared parameters.critical

/--
The truthful global producer through the parentwise structural step.

The strict caller preparation chooses its own smaller source loss after the
critical structural loss is known.  This loss is intentionally not identified
with `parameters.hierarchy.sourceLoss`: the latter was selected for later
global bookkeeping, while the strict preparation additionally pays the
caller-tree and boundary losses.
-/
def WZ2PropStickyPaperPreparedStructuralMainlineStatement : Prop :=
  ∀ {sigma outputLoss : ℝ},
    ∀ {totalExponent globalBalancingExponent : ℕ},
      ∀ (parameters :
          WZ2PaperFinalParameterSelectionData
            sigma outputLoss totalExponent globalBalancingExponent),
        0 < outputLoss →
        outputLoss ≤ 1 →
          ∃ preparationExponent : ℕ,
            ∃ preparationSourceLoss delta₀ : ℝ,
              0 < preparationSourceLoss ∧
              preparationSourceLoss <
                parameters.hierarchy.stableLoss ∧
              16 * preparationSourceLoss <
                parameters.hierarchy.stableLoss ∧
              0 < delta₀ ∧
              delta₀ ≤ 1 ∧
              ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
                ∀ source : Kakeya.Streamlined.TubeFamily delta,
                  ∀ shading : WZ1PaperTubeShading source,
                    WZ2PaperExactScaleExtremal
                        sigma preparationSourceLoss source shading →
                      ∀ caller :
                          Kakeya.Streamlined.AdmissibleScale delta,
                        Real.rpow delta (1 - outputLoss) ≤ caller.1 →
                        caller.1 ≤ Real.rpow delta outputLoss →
                          Nonempty
                            (WZ2PaperPreparedStructuralMainlineData
                              shading caller totalExponent
                              globalBalancingExponent parameters
                              preparationSourceLoss)

end Kakeya.Assouad

end
