import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactMultiplicityTruncation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedCriticalFloorSelection

/-!
# Extremality after exact cellwise multiplicity truncation

The exact truncation preserves the shaded union and loses at most a factor two
in indexed mass.  An explicit factor-two absorption therefore restores density
at a weaker loss, after which the cropped critical floor supplies the required
fine-volume lower bound.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

namespace PureWZ2Node05ExactMultiplicityTruncationData

/-- Exact cellwise truncation preserves cropped extremality once its factor-two
mass loss has been absorbed into the new density exponent. -/
theorem extremal_of_loss_absorption
    {delta sigma sourceLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData Y hdelta m)
    (sourceExtremal : WZ2PaperCroppedIsExtremal sigma sourceLoss fine Y)
    (hsourceOutput : sourceLoss ≤ outputLoss)
    (hAbsorb :
      2 * Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta sourceLoss) :
    WZ2PaperCroppedIsExtremal sigma outputLoss fine truncation.truncated := by
  have sourceAtOutput := sourceExtremal.mono_loss hsourceOutput
  have dense : truncation.truncated.IsLambdaDense
      (Kakeya.realRpowENN delta outputLoss) := by
    have scaled :
        (2 : ENNReal) *
              (Kakeya.realRpowENN delta outputLoss *
                (wz1PaperBodyFamily fine).mass) ≤
            2 * truncation.truncated.mass := by
      calc
        (2 : ENNReal) *
              (Kakeya.realRpowENN delta outputLoss *
                (wz1PaperBodyFamily fine).mass) =
            (2 * Kakeya.realRpowENN delta outputLoss) *
              (wz1PaperBodyFamily fine).mass := by ring
        _ ≤ Kakeya.realRpowENN delta sourceLoss *
              (wz1PaperBodyFamily fine).mass := by
          exact mul_le_mul_left hAbsorb _
        _ ≤ Y.mass := sourceExtremal.dense
        _ ≤ 2 * truncation.truncated.mass := truncation.mass_retention
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp scaled
  exact
    { delta_pos := sourceExtremal.delta_pos
      delta_le_one := sourceExtremal.delta_le_one
      nonempty := sourceExtremal.nonempty
      cwa_nearby_scales := sourceAtOutput.cwa_nearby_scales
      cubical := truncation.cubical
      dense := dense
      volume_upper := by
        rw [truncation.union_eq]
        exact sourceAtOutput.volume_upper }

/-- Paper-ordered exact-truncation output: restore extremality at the selected
structural loss, apply the critical floor, then weaken to the final loss. -/
theorem extremal_and_volume_lower_of_critical_floor
    {delta sigma sourceLoss outputLoss floorLoss structuralBudget : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData Y hdelta m)
    (sourceExtremal : WZ2PaperCroppedIsExtremal sigma sourceLoss fine Y)
    (criticalFloor : PureWZ2CroppedCriticalFloorSelectionData
      sigma floorLoss structuralBudget)
    (hsourceStructural : sourceLoss ≤ criticalFloor.structuralLoss)
    (hstructuralOutput : criticalFloor.structuralLoss ≤ outputLoss)
    (hAbsorb :
      2 * Kakeya.realRpowENN delta criticalFloor.structuralLoss ≤
        Kakeya.realRpowENN delta sourceLoss)
    (hdeltaCutoff : delta ≤ criticalFloor.delta₀) :
    WZ2PaperCroppedIsExtremal sigma outputLoss fine truncation.truncated ∧
      Kakeya.realRpowENN delta (sigma + floorLoss) ≤
        volume truncation.truncated.union := by
  have structuralExtremal := truncation.extremal_of_loss_absorption
    sourceExtremal hsourceStructural hAbsorb
  have volumeLower := criticalFloor.volume_floor delta
    structuralExtremal.delta_pos hdeltaCutoff fine structuralExtremal.nonempty
    truncation.truncated structuralExtremal.cwa_nearby_scales
    structuralExtremal.cubical structuralExtremal.dense
  exact ⟨structuralExtremal.mono_loss hstructuralOutput, volumeLower⟩

end PureWZ2Node05ExactMultiplicityTruncationData

end Kakeya.Assouad

end
