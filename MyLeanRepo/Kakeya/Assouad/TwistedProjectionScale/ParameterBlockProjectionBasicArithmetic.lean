import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionExponent
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockRepresentativeCorridor

/-!
# Basic arithmetic for paper Lemma 7.12
-/

noncomputable section

namespace Kakeya.Assouad

/-- Recentering a finite local parameter set preserves its cardinality. -/
lemma parameterLocalFullBlock_centered_enncard
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    (localBlock :
      ParameterLocalFullBlockData clustered epsilon) :
    localBlock.centeredPoints.enncard =
      localBlock.sourcePoints.enncard := by
  rw [localBlock.centeredPoints_eq]
  simp only [centeredParameterSet, DiscreteSet.enncard]
  rw [Finset.card_image_of_injective]
  intro first second heq
  exact sub_left_injective heq

/--
Divide a lower bound by one fixed positive finite `ENNReal` constant.
-/
lemma ennreal_inv_mul_le_of_le_mul
    {constant value bound : ENNReal}
    (hconstant_zero : constant ≠ 0)
    (hconstant_top : constant ≠ ⊤)
    (h : value ≤ constant * bound) :
    constant⁻¹ * value ≤ bound := by
  calc
    constant⁻¹ * value = value / constant := by
      rw [ENNReal.div_eq_inv_mul]
    _ ≤ (constant * bound) / constant := by
      gcongr
    _ = bound := by
      rw [show constant * bound = bound * constant by ring,
        ENNReal.mul_div_cancel_right
          hconstant_zero hconstant_top]

/--
Invert the normalized fine-scale ratio inside a real-power expression.
-/
lemma realRpowENN_block_div_delta
    {delta blockScale exponent : ℝ}
    (hdelta : 0 < delta)
    (hblockScale : 0 < blockScale) :
    Kakeya.realRpowENN (blockScale / delta) exponent =
      Kakeya.realRpowENN
        (delta / blockScale) (-exponent) := by
  simp only [Kakeya.realRpowENN]
  congr 1
  have hratio : 0 < delta / blockScale := by positivity
  have hinverse :
      blockScale / delta =
        (delta / blockScale)⁻¹ := by
    field_simp [hdelta.ne', hblockScale.ne']
  rw [hinverse]
  exact
    (Real.inv_rpow hratio.le exponent).trans
      (Real.rpow_neg hratio.le exponent).symm

/-- Power identity `(delta / rho)^a * rho^a = delta^a`. -/
lemma parameterBlockProjection_realRpowENN_div_mul
    {delta rho exponent : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho) :
    Kakeya.realRpowENN (delta / rho) exponent *
        Kakeya.realRpowENN rho exponent =
      Kakeya.realRpowENN delta exponent := by
  have hratio : 0 < delta / rho := by positivity
  have hreal :
      Real.rpow (delta / rho) exponent *
          Real.rpow rho exponent =
        Real.rpow delta exponent := by
    have hmul :=
      Real.mul_rpow hratio.le hrho.le (z := exponent)
    have hcancel : (delta / rho) * rho = delta := by
      field_simp [hrho.ne']
    rw [hcancel] at hmul
    exact hmul.symm
  simp only [Kakeya.realRpowENN]
  calc
    ENNReal.ofReal (Real.rpow (delta / rho) exponent) *
          ENNReal.ofReal (Real.rpow rho exponent) =
        ENNReal.ofReal
          (Real.rpow (delta / rho) exponent *
            Real.rpow rho exponent) := by
      exact
        (ENNReal.ofReal_mul
          (Real.rpow_nonneg hratio.le exponent)).symm
    _ = ENNReal.ofReal (Real.rpow delta exponent) := by
      rw [hreal]

end Kakeya.Assouad
