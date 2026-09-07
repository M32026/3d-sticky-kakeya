import MyLeanRepo.Kakeya.Assouad.PropStickyCallerNestedCWAStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyParentNestedTransitivity

/-! # Transitive closure of the caller-rooted parent nesting -/

noncomputable section

namespace Kakeya.Assouad

theorem WZ2PaperCallerStrictPreparationData.parent_nested_of_le
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (coarse fine : Fin prepared.strictScaleCount)
    (hlevels : coarse.val ≤ fine.val) :
    ∀ first second : Fin prepared.refinement.selected.family.card,
      (prepared.strictScaleData fine).cover.parent first =
          (prepared.strictScaleData fine).cover.parent second →
        (prepared.strictScaleData coarse).cover.parent first =
          (prepared.strictScaleData coarse).cover.parent second := by
  exact
    parent_nested_of_adjacent
      prepared.strictScaleData prepared.strict_parent_nested
      coarse fine hlevels

end Kakeya.Assouad

end
