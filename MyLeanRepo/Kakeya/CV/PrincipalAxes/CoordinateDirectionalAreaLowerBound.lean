import MyLeanRepo.Kakeya.CV.PolynomialCylinder.RotationTransfer
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.MeasurabilitySetup
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Coordinate directional area lower bound

Away from the negligible singular locus, the polynomial unit normal has norm
one.  Its Euclidean coordinate `ℓ¹` norm therefore controls the constant
integrand defining codimension-one Hausdorff measure.
-/

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal Real BigOperators

namespace Kakeya.CV

private lemma coordinate_abs_sum_ge_norm (n : Point 3) :
    ‖n‖ ≤ ∑ i : Fin 3, |inner ℝ (eBasis i) n| := by
  let e : OrthonormalBasis (Fin 3) ℝ (Point 3) :=
    EuclideanSpace.basisFun (Fin 3) ℝ
  have hrepr : n = ∑ i : Fin 3, inner ℝ (e i) n • e i :=
    (e.sum_repr' n).symm
  have he : ∀ i : Fin 3, e i = eBasis i := by
    intro i
    ext j
    simp [e, eBasis, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single]
  calc
    ‖n‖ = ‖∑ i : Fin 3, inner ℝ (e i) n • e i‖ :=
      congrArg norm hrepr
    _ ≤ ∑ i : Fin 3, ‖inner ℝ (e i) n • e i‖ := norm_sum_le _ _
    _ = ∑ i : Fin 3, |inner ℝ (eBasis i) n| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, e.orthonormal.1 i, mul_one, Real.norm_eq_abs]
      rw [he i]

/-- On a measurable subset of a polynomial zero set, the sum of the three
coordinate directional surface areas controls codimension-one Hausdorff
measure when the singular locus is negligible. -/
lemma coordinate_directional_area_controls_surface
    (q : MvPolynomial (Fin 3) ℝ)
    (S : Set (Point 3)) (hS_meas : MeasurableSet S)
    (hS_zero : S ⊆ polynomialZeroSet q)
    (hsing : HasNegligibleSingularSet q) :
    codimensionOneMeasure 3 S ≤
      ∑ i : Fin 3, directionalSurfaceArea (eBasis i) q S := by
  let μ : Measure (Point 3) := μH[2]
  let F : Fin 3 → Point 3 → ENNReal := fun i x =>
    ENNReal.ofReal
      ‖inner ℝ (eBasis i) (polynomialUnitNormal q x)‖
  have hF_meas : ∀ i, Measurable (F i) := by
    intro i
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.inner (measurable_polynomialUnitNormal q)).norm
  have hsing_mu : μ (polynomialSingularSet q) = 0 := by
    unfold HasNegligibleSingularSet codimensionOneMeasure at hsing
    norm_num at hsing
    exact hsing
  have hnot_sing : ∀ᵐ x ∂μ, x ∉ polynomialSingularSet q := by
    rw [ae_iff]
    simpa only [not_not, setOf_mem_eq] using hsing_mu
  have hpoint : ∀ᵐ x ∂μ.restrict S,
      (1 : ENNReal) ≤ ∑ i : Fin 3, F i x := by
    rw [ae_restrict_iff' hS_meas]
    filter_upwards [hnot_sing] with x hx hxS
    have hx_zero : polynomialValue q x = 0 := hS_zero hxS
    have hgrad_ne : polynomialGradient q x ≠ 0 := by
      intro hgrad
      exact hx ⟨hx_zero, hgrad⟩
    have hnorm_ne : ‖polynomialGradient q x‖ ≠ 0 := by
      simpa [norm_eq_zero] using hgrad_ne
    have hnorm_pos : 0 < ‖polynomialGradient q x‖ :=
      lt_of_le_of_ne (norm_nonneg _) hnorm_ne.symm
    have hunit : ‖polynomialUnitNormal q x‖ = 1 := by
      rw [polynomialUnitNormal, dif_neg hnorm_ne, norm_smul,
        Real.norm_eq_abs, abs_inv, abs_of_pos hnorm_pos]
      exact inv_mul_cancel₀ hnorm_ne
    have hreal :
        1 ≤ ∑ i : Fin 3,
          ‖inner ℝ (eBasis i) (polynomialUnitNormal q x)‖ := by
      calc
        1 = ‖polynomialUnitNormal q x‖ := hunit.symm
        _ ≤ ∑ i : Fin 3,
            |inner ℝ (eBasis i) (polynomialUnitNormal q x)| :=
          coordinate_abs_sum_ge_norm _
        _ = ∑ i : Fin 3,
            ‖inner ℝ (eBasis i) (polynomialUnitNormal q x)‖ := by
          apply Finset.sum_congr rfl
          intro i _
          exact (Real.norm_eq_abs _).symm
    calc
      (1 : ENNReal) = ENNReal.ofReal 1 := by norm_num
      _ ≤ ENNReal.ofReal
          (∑ i : Fin 3,
            ‖inner ℝ (eBasis i) (polynomialUnitNormal q x)‖) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ∑ i : Fin 3, F i x := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _
        positivity
  have hmono :
      (∫⁻ _ in S, (1 : ENNReal) ∂μ) ≤
        ∫⁻ x in S, ∑ i : Fin 3, F i x ∂μ :=
    lintegral_mono_ae hpoint
  calc
    codimensionOneMeasure 3 S = μ S := by
      change μH[(3 : ℝ) - 1] S = μH[2] S
      norm_num
    _ = ∫⁻ _ in S, (1 : ENNReal) ∂μ := by simp
    _ ≤ ∫⁻ x in S, ∑ i : Fin 3, F i x ∂μ := hmono
    _ = ∑ i : Fin 3, ∫⁻ x in S, F i x ∂μ := by
      rw [lintegral_finsetSum Finset.univ]
      intro i _
      exact hF_meas i
    _ = ∑ i : Fin 3, directionalSurfaceArea (eBasis i) q S := by
      apply Finset.sum_congr rfl
      intro i _
      rfl

end Kakeya.CV
