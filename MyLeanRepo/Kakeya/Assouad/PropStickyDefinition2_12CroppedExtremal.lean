import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Extremal
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements

/-!
# Section 6 extremality over pure Definition 2.12 structure

Section 6 uses the WZ cropped full-line and cubical shading convention, while
the all-scale Convex-Wolff hypothesis remains Assouad Definition 2.12 on the
underlying ordinary tube family.  This hybrid record keeps those two roles
separate.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
Section 6 extremality: pure ordinary Definition 2.12 structure together with
a cropped cubical WZ shading on the same indexed tube parameters.
-/
structure WZ2PaperCroppedIsExtremal
    {delta : ℝ}
    (sigma loss : ℝ)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading family) : Prop where
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  nonempty : family.Nonempty
  cwa_nearby_scales :
    WZ2PaperPureCWAAtNearbyScales family
      (Kakeya.realRpowENN delta (-loss))
  cubical :
    WZ1PaperIsCubicalShading shading
  dense :
    shading.IsLambdaDense
      (Kakeya.realRpowENN delta loss)
  volume_upper :
    volume shading.union ≤
      Kakeya.realRpowENN delta (sigma - loss)

/--
The critical-volume lower bound used inside the cropped Section 6 argument.

The structural hypothesis is still the pure Definition 2.12 predicate.  Only
the shading convention is cropped and cubical.
-/
def HasWZ2PaperCroppedCriticalVolumeFloor (sigma : ℝ) : Prop :=
  ∀ floorLoss structuralBudget : ℝ,
    0 < floorLoss →
    0 < structuralBudget →
    ∃ structuralLoss delta₀ : ℝ,
      0 < structuralLoss ∧
      structuralLoss ≤ structuralBudget ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
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
                volume shading.union

namespace WZ2PaperCroppedIsExtremal

/-- Weakening the loss preserves hybrid Section 6 extremality. -/
theorem mono_loss
    {delta sigma firstLoss secondLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data :
      WZ2PaperCroppedIsExtremal
        sigma firstLoss family shading)
    (hloss : firstLoss ≤ secondLoss) :
    WZ2PaperCroppedIsExtremal
      sigma secondLoss family shading := by
  have hcwaPower :
      Kakeya.realRpowENN delta (-firstLoss) ≤
        Kakeya.realRpowENN delta (-secondLoss) := by
    apply ENNReal.ofReal_mono
    exact
      Real.rpow_le_rpow_of_exponent_ge
        data.delta_pos data.delta_le_one (by linarith)
  have hdensePower :
      Kakeya.realRpowENN delta secondLoss ≤
        Kakeya.realRpowENN delta firstLoss := by
    apply ENNReal.ofReal_mono
    exact
      Real.rpow_le_rpow_of_exponent_ge
        data.delta_pos data.delta_le_one hloss
  have hvolumePower :
      Kakeya.realRpowENN delta (sigma - firstLoss) ≤
        Kakeya.realRpowENN delta (sigma - secondLoss) := by
    apply ENNReal.ofReal_mono
    exact
      Real.rpow_le_rpow_of_exponent_ge
        data.delta_pos data.delta_le_one (by linarith)
  exact
    {
      delta_pos := data.delta_pos
      delta_le_one := data.delta_le_one
      nonempty := data.nonempty
      cwa_nearby_scales :=
        data.cwa_nearby_scales.mono
          hcwaPower (by simp [Kakeya.realRpowENN])
      cubical := data.cubical
      dense :=
        (mul_le_mul_right'
          hdensePower (wz1PaperBodyFamily family).mass).trans
          data.dense
      volume_upper :=
        data.volume_upper.trans hvolumePower
    }

end WZ2PaperCroppedIsExtremal

end Kakeya.Assouad

end
