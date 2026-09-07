import MyLeanRepo.Kakeya.Assouad.PureWZ2.Critical

/-!
# Quantifier-ordered pure critical-volume floor

Node 2 supplies the critical floor in the ordinary pure Definition 2.12
model.  This record fixes one floor loss and one structural-loss budget before
the small-scale threshold, preserving the quantifier order needed by the
post-deletion coarse argument.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2CriticalFloorSelectionData
    (sigma floorLoss structuralBudget : ℝ) where
  structuralLoss : ℝ
  structuralLoss_pos : 0 < structuralLoss
  structuralLoss_le : structuralLoss ≤ structuralBudget
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  volume_floor :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ∀ family : Kakeya.Streamlined.TubeFamily delta,
        family.Nonempty →
        ∀ shading : Kakeya.Streamlined.TubeShading family,
          WZ2PaperPureCWAAtNearbyScales family
              (Kakeya.realRpowENN delta (-structuralLoss)) →
          shading.IsLambdaDense
              (Kakeya.realRpowENN delta structuralLoss) →
            Kakeya.realRpowENN delta (sigma + floorLoss) ≤
              MeasureTheory.volume shading.union

theorem PureWZ2CriticalPackage.select_pure_floor
    {sigma floorLoss structuralBudget : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (floorLossPos : 0 < floorLoss)
    (structuralBudgetPos : 0 < structuralBudget) :
    Nonempty
      (PureWZ2CriticalFloorSelectionData
        sigma floorLoss structuralBudget) := by
  rcases
      critical.critical_floor
        floorLoss structuralBudget floorLossPos structuralBudgetPos
    with
    ⟨structuralLoss, delta₀, structuralLossPos, structuralLossLe,
      delta₀Pos, delta₀One, volumeFloor⟩
  exact
    ⟨{
      structuralLoss := structuralLoss
      structuralLoss_pos := structuralLossPos
      structuralLoss_le := structuralLossLe
      delta₀ := delta₀
      delta₀_pos := delta₀Pos
      delta₀_le_one := delta₀One
      volume_floor := by
        intro delta deltaPos deltaSmall family familyNonempty shading
          pureCWA dense
        exact
          volumeFloor delta deltaPos deltaSmall family familyNonempty
            shading pureCWA dense
    }⟩

end Kakeya.Assouad

end
