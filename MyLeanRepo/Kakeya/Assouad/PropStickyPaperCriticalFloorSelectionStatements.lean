import MyLeanRepo.Kakeya.Assouad.PropStickyStatements

/-!
# Quantifier-ordered WZ2 critical-volume floor

The Assouad paper fixes the desired lower-volume error and then chooses a
sufficiently small extremality parameter.  This dependent record retains that
choice, including the scale threshold at which it is valid.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperCriticalFloorSelectionData
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
          WZ2PaperCWAAtNearbyScales family
              (Kakeya.realRpowENN delta (-structuralLoss)) →
          WZ1PaperIsCubicalShading shading →
          shading.IsLambdaDense
              (Kakeya.realRpowENN delta structuralLoss) →
            Kakeya.realRpowENN delta (sigma + floorLoss) ≤
              MeasureTheory.volume shading.union

def WZ2PaperCriticalFloorSelectionStatement : Prop :=
  ∀ sigma floorLoss structuralBudget : ℝ,
    0 < floorLoss →
    0 < structuralBudget →
    HasWZ2PaperCriticalVolumeFloor sigma →
      Nonempty
        (WZ2PaperCriticalFloorSelectionData
          sigma floorLoss structuralBudget)

end Kakeya.Assouad

end
