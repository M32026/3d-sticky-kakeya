import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CroppedExtremal

/-!
# Quantifier-ordered cropped pure critical floor

This is the cropped-shading analogue of `PureWZ2CriticalFloorSelectionData`.
It is intentionally not inferred from the ordinary critical package: that
model conversion is a separate mathematical producer.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2CroppedCriticalFloorSelectionData
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
        ∀ shading : WZ1PaperTubeShading family,
          WZ2PaperPureCWAAtNearbyScales family
              (Kakeya.realRpowENN delta (-structuralLoss)) →
          WZ1PaperIsCubicalShading shading →
          shading.IsLambdaDense
              (Kakeya.realRpowENN delta structuralLoss) →
            Kakeya.realRpowENN delta (sigma + floorLoss) ≤
              MeasureTheory.volume shading.union

theorem pureWZ2_select_cropped_critical_floor
    {sigma floorLoss structuralBudget : ℝ}
    (criticalFloor : HasWZ2PaperCroppedCriticalVolumeFloor sigma)
    (floorLoss_pos : 0 < floorLoss)
    (structuralBudget_pos : 0 < structuralBudget) :
    Nonempty
      (PureWZ2CroppedCriticalFloorSelectionData
        sigma floorLoss structuralBudget) := by
  rcases
      criticalFloor floorLoss structuralBudget
        floorLoss_pos structuralBudget_pos
    with
    ⟨structuralLoss, delta₀, structuralLoss_pos,
      structuralLoss_le, delta₀_pos, delta₀_le_one,
      volume_floor⟩
  exact
    ⟨{
      structuralLoss := structuralLoss
      structuralLoss_pos := structuralLoss_pos
      structuralLoss_le := structuralLoss_le
      delta₀ := delta₀
      delta₀_pos := delta₀_pos
      delta₀_le_one := delta₀_le_one
      volume_floor := volume_floor
    }⟩

end Kakeya.Assouad

end
