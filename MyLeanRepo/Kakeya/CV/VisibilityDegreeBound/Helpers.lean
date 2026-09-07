import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.RotationReduction
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.GCongr

/-!
# Helper lemmas for `visibility_degree_bound`

Provides basic properties of `directionalSurfaceArea` (homogeneity,
subadditivity, evenness, monotonicity), the inclusion `closedBall c 1 ⊆
unitTube c u`, and `tripleVolume = 1` for orthonormal bases.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace Kakeya.CV

-- ============================================================================
-- Measurability of the directional surface area integrand
-- ============================================================================

/-- The integrand in `directionalSurfaceArea` is measurable. -/
lemma directionalSurfaceArea_integrand_measurable
    (e : Point 3) (p : MvPolynomial (Fin 3) ℝ) :
    Measurable (fun x : Point 3 =>
      ENNReal.ofReal ‖inner ℝ e (polynomialUnitNormal p x)‖) := by
  have hgrad_cont : Continuous (polynomialGradient p) := by
    have h1 : Continuous (fun x : Point 3 =>
        (fun i : Fin 3 => polynomialValue (MvPolynomial.pderiv i p) x)) := by
      apply continuous_pi
      intro i
      have hpoly : Continuous (fun y : Fin 3 → ℝ =>
          MvPolynomial.eval y (MvPolynomial.pderiv i p)) :=
        MvPolynomial.continuous_eval (MvPolynomial.pderiv i p)
      have hcoerce : Continuous (fun x : Point 3 => (fun j : Fin 3 => x j)) := by
        fun_prop
      have h_eq : (fun x : Point 3 => polynomialValue (MvPolynomial.pderiv i p) x) =
          (fun x : Point 3 => MvPolynomial.eval (fun j : Fin 3 => x j) (MvPolynomial.pderiv i p)) := by
        funext x
        simp [polynomialValue]
      rw [h_eq]
      exact hpoly.comp hcoerce
    exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp h1
  have hgrad_meas : Measurable (polynomialGradient p) := hgrad_cont.measurable
  have h1 : ∀ (x : Point 3), polynomialUnitNormal p x =
      ‖polynomialGradient p x‖⁻¹ • polynomialGradient p x := by
    intro x
    simp only [polynomialUnitNormal]
    by_cases h : ‖polynomialGradient p x‖ = 0
    · rw [dif_pos h]
      have hg : polynomialGradient p x = 0 := by
        simpa [norm_eq_zero] using h
      rw [hg]
      have hnorm0 : ‖(0 : Point 3)‖ = 0 := by simp
      rw [hnorm0]
      simp
    · rw [dif_neg h]
  have hnorm_meas : Measurable (fun v : Point 3 => ‖v‖) :=
    continuous_norm.measurable
  have hg_meas : Measurable (fun v : Point 3 => ‖v‖⁻¹ • v) := by
    have h1 : Measurable (fun v : Point 3 => ‖v‖⁻¹) := hnorm_meas.inv
    have h2 : Measurable (fun v : Point 3 => v) := measurable_id
    exact h1.smul h2
  have hpun_meas : Measurable (polynomialUnitNormal p) := by
    have h4 : (polynomialUnitNormal p) = (fun x : Point 3 =>
        ‖polynomialGradient p x‖⁻¹ • polynomialGradient p x) := by
      funext x
      exact h1 x
    rw [h4]
    exact hg_meas.comp hgrad_meas
  have h_inner_meas : Measurable (fun y : Point 3 => inner ℝ e y) :=
    (continuous_const.inner continuous_id).measurable
  have h5 : Measurable (fun x : Point 3 => inner ℝ e (polynomialUnitNormal p x)) :=
    h_inner_meas.comp hpun_meas
  have h6 : Measurable (fun x : Point 3 => ‖inner ℝ e (polynomialUnitNormal p x)‖) :=
    continuous_norm.measurable.comp h5
  have h7 : Measurable (fun r : ℝ => ENNReal.ofReal r) :=
    ENNReal.measurable_ofReal
  exact h7.comp h6

-- ============================================================================
-- Homogeneity
-- ============================================================================

/-- Homogeneity of directional surface area under nonnegative scaling. -/
lemma directionalSurfaceArea_homogeneity
    (c : ℝ) (hc : 0 ≤ c) (e : Point 3)
    (p : MvPolynomial (Fin 3) ℝ) (S : Set (Point 3)) :
    directionalSurfaceArea (c • e) p S =
      ENNReal.ofReal c * directionalSurfaceArea e p S := by
  have h3 : ∀ (x : Point 3),
      ENNReal.ofReal ‖inner ℝ (c • e) (polynomialUnitNormal p x)‖ =
        ENNReal.ofReal c * ENNReal.ofReal ‖inner ℝ e (polynomialUnitNormal p x)‖ := by
    intro x
    have h_inner : inner ℝ (c • e) (polynomialUnitNormal p x) =
        c * inner ℝ e (polynomialUnitNormal p x) := by
      simp [inner_smul_left]
    have h_norm : ‖inner ℝ (c • e) (polynomialUnitNormal p x)‖ =
        c * ‖inner ℝ e (polynomialUnitNormal p x)‖ := by
      rw [h_inner, norm_mul]
      have h_abs : ‖c‖ = |c| := Real.norm_eq_abs c
      rw [h_abs, abs_of_nonneg hc]
    rw [h_norm, ← ENNReal.ofReal_mul hc]
  have h_f_eq : (fun x : Point 3 =>
        ENNReal.ofReal ‖inner ℝ (c • e) (polynomialUnitNormal p x)‖) =
      (fun x : Point 3 =>
        ENNReal.ofReal c * ENNReal.ofReal ‖inner ℝ e (polynomialUnitNormal p x)‖) := by
    funext x
    exact h3 x
  simp only [directionalSurfaceArea, h_f_eq]
  have h_meas : Measurable (fun x : Point 3 =>
      ENNReal.ofReal ‖inner ℝ e (polynomialUnitNormal p x)‖) :=
    directionalSurfaceArea_integrand_measurable e p
  rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal c) h_meas]

-- ============================================================================
-- Subadditivity
-- ============================================================================

/-- Subadditivity of directional surface area. -/
lemma directionalSurfaceArea_subadditivity
    (u v : Point 3) (p : MvPolynomial (Fin 3) ℝ) (S : Set (Point 3)) :
    directionalSurfaceArea (u + v) p S ≤
      directionalSurfaceArea u p S + directionalSurfaceArea v p S := by
  let f : Point 3 → ENNReal := fun x =>
    ENNReal.ofReal ‖inner ℝ u (polynomialUnitNormal p x)‖
  let g : Point 3 → ENNReal := fun x =>
    ENNReal.ofReal ‖inner ℝ v (polynomialUnitNormal p x)‖
  have hf_meas : Measurable f := directionalSurfaceArea_integrand_measurable u p
  have hg_meas : Measurable g := directionalSurfaceArea_integrand_measurable v p
  have h2 : ∀ (x : Point 3),
      ‖inner ℝ (u + v) (polynomialUnitNormal p x)‖ ≤
        ‖inner ℝ u (polynomialUnitNormal p x)‖ +
        ‖inner ℝ v (polynomialUnitNormal p x)‖ := by
    intro x
    have h1 : inner ℝ (u + v) (polynomialUnitNormal p x) =
          inner ℝ u (polynomialUnitNormal p x) + inner ℝ v (polynomialUnitNormal p x) := by
      simp [inner_add_left]
    rw [h1]
    exact norm_add_le _ _
  have h_nonneg1 : ∀ x, 0 ≤ ‖inner ℝ u (polynomialUnitNormal p x)‖ := by
    intro x; positivity
  have h_nonneg2 : ∀ x, 0 ≤ ‖inner ℝ v (polynomialUnitNormal p x)‖ := by
    intro x; positivity
  have h3 : ∀ (x : Point 3),
      ENNReal.ofReal ‖inner ℝ (u + v) (polynomialUnitNormal p x)‖ ≤ f x + g x := by
    intro x
    have h4 : ENNReal.ofReal ‖inner ℝ (u + v) (polynomialUnitNormal p x)‖ ≤
          ENNReal.ofReal (‖inner ℝ u (polynomialUnitNormal p x)‖ +
            ‖inner ℝ v (polynomialUnitNormal p x)‖) :=
      ENNReal.ofReal_le_ofReal (h2 x)
    have h5 : ENNReal.ofReal (‖inner ℝ u (polynomialUnitNormal p x)‖ +
          ‖inner ℝ v (polynomialUnitNormal p x)‖) = f x + g x := by
      rw [ENNReal.ofReal_add (h_nonneg1 x) (h_nonneg2 x)]
    rw [h5] at h4
    exact h4
  have hfg_meas : Measurable (f + g) := hf_meas.add hg_meas
  have h3' : ∀ (x : Point 3), x ∈ S →
      ENNReal.ofReal ‖inner ℝ (u + v) (polynomialUnitNormal p x)‖ ≤ (f + g) x := by
    intro x _
    exact h3 x
  have h_main : ∫⁻ (x : Point 3) in S,
        ENNReal.ofReal ‖inner ℝ (u + v) (polynomialUnitNormal p x)‖
        ∂(MeasureTheory.Measure.hausdorffMeasure 2) ≤
      ∫⁻ (x : Point 3) in S, (f + g) x
        ∂(MeasureTheory.Measure.hausdorffMeasure 2) :=
    MeasureTheory.setLIntegral_mono hfg_meas h3'
  have h_add : ∫⁻ (x : Point 3) in S, (f + g) x
        ∂(MeasureTheory.Measure.hausdorffMeasure 2) =
      directionalSurfaceArea u p S + directionalSurfaceArea v p S := by
    simp only [directionalSurfaceArea, Pi.add_apply]
    rw [MeasureTheory.lintegral_add_left' hf_meas.aemeasurable]
  rw [h_add] at h_main
  exact h_main

-- ============================================================================
-- Evenness
-- ============================================================================

/-- Evenness of directional surface area. -/
lemma directionalSurfaceArea_evenness
    (u : Point 3) (p : MvPolynomial (Fin 3) ℝ) (S : Set (Point 3)) :
    directionalSurfaceArea (-u) p S = directionalSurfaceArea u p S := by
  have h3 : ∀ (x : Point 3),
      ENNReal.ofReal ‖inner ℝ (-u) (polynomialUnitNormal p x)‖ =
        ENNReal.ofReal ‖inner ℝ u (polynomialUnitNormal p x)‖ := by
    intro x
    have h1 : inner ℝ (-u) (polynomialUnitNormal p x) =
          -inner ℝ u (polynomialUnitNormal p x) := by
      simp [inner_neg_left]
    rw [h1, norm_neg]
  have h_f_eq : (fun x : Point 3 =>
        ENNReal.ofReal ‖inner ℝ (-u) (polynomialUnitNormal p x)‖) =
      (fun x : Point 3 =>
        ENNReal.ofReal ‖inner ℝ u (polynomialUnitNormal p x)‖) := by
    funext x
    exact h3 x
  simp only [directionalSurfaceArea, h_f_eq]

-- ============================================================================
-- Monotonicity in the set
-- ============================================================================

lemma directionalSurfaceArea_mono
    (e : Point 3) (p : MvPolynomial (Fin 3) ℝ)
    {S₁ S₂ : Set (Point 3)} (h : S₁ ⊆ S₂) :
    directionalSurfaceArea e p S₁ ≤ directionalSurfaceArea e p S₂ := by
  simp only [directionalSurfaceArea]
  exact MeasureTheory.lintegral_mono_set h

-- ============================================================================
-- Unit ball in unit tube
-- ============================================================================

/-- The unit ball centered at `c` is contained in the unit tube about the
line through `c` in any unit direction `u`. -/
lemma unitBall_subset_unitTube
    (c : Point 3) (u : Point 3) (_hu : ‖u‖ = 1) :
    Metric.closedBall c 1 ⊆ unitTube c u := by
  intro x hx
  have hxc : dist x c ≤ 1 := by
    simpa [Metric.mem_closedBall] using hx
  have hc_in_line : c ∈ affineLine c u := by
    refine ⟨0, ?_⟩
    simp
  have h : Metric.infDist x (affineLine c u) ≤ dist x c :=
    Metric.infDist_le_dist_of_mem hc_in_line
  have h' : Metric.infDist x (affineLine c u) ≤ 1 := by linarith
  simpa [unitTube] using h'

-- ============================================================================
-- tripleVolume of orthonormal basis
-- ============================================================================

/-- The triple volume of an orthonormal basis is 1. -/
lemma tripleVolume_orthonormal
    (v : Fin 3 → Point 3) (hv : Orthonormal ℝ v) :
    tripleVolume v = 1 := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := fun i j => v i j
  have hnorm : ∀ i, ‖v i‖ = 1 := hv.1
  have hpair : Pairwise (fun i j : Fin 3 => inner ℝ (v i) (v j) = 0) := hv.2
  have h_orth : ∀ (i j : Fin 3), inner ℝ (v i) (v j) = if i = j then 1 else 0 := by
    intro i j
    by_cases h : i = j
    · rw [h]
      have h6 : inner ℝ (v j) (v j) = ‖v j‖ ^ 2 := by
        exact real_inner_self_eq_norm_sq (v j)
      rw [h6, hnorm j] <;> norm_num
    · have h7 : inner ℝ (v i) (v j) = 0 := hpair h
      rw [h7] <;> simp [h]
  have h_inner_eq_sum : ∀ (i j : Fin 3),
      inner ℝ (v i) (v j) = ∑ k : Fin 3, A i k * A j k := by
    intro i j
    have h_sum : inner ℝ (v i) (v j) = ∑ k : Fin 3, inner ℝ ((v i) k) ((v j) k) := by
      rw [PiLp.inner_apply]
    rw [h_sum]
    apply Finset.sum_congr rfl
    intro k _
    simpa using mul_comm ((v j) k) ((v i) k)
  have hAAt : A * A.transpose = 1 := by
    ext i j
    simp only [A, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    have h : (∑ k : Fin 3, v i k * v j k) = inner ℝ (v i) (v j) := by
      rw [← h_inner_eq_sum i j]
    rw [h, h_orth i j]
  have hdet : (A.det) ^ 2 = 1 := by
    have h : (A * A.transpose).det = 1 := by
      rw [hAAt] <;> simp
    have h2 : (A * A.transpose).det = A.det * A.transpose.det := by
      rw [Matrix.det_mul]
    have h3 : A.transpose.det = A.det := by
      rw [Matrix.det_transpose]
    rw [h2, h3] at h <;> linarith
  have habs : |A.det| = 1 := by
    have h : A.det ^ 2 = 1 := hdet
    have h5 : A.det = 1 ∨ A.det = -1 := by
      have h6 : A.det ^ 2 - 1 = 0 := by linarith
      have h7 : (A.det - 1) * (A.det + 1) = 0 := by linarith
      have h8 : A.det - 1 = 0 ∨ A.det + 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h7
      cases h8 with
      | inl h8 =>
        have h9 : A.det = 1 := by linarith
        exact Or.inl h9
      | inr h8 =>
        have h9 : A.det = -1 := by linarith
        exact Or.inr h9
    rcases h5 with (h5 | h5) <;> rw [h5] <;> norm_num
  simpa [tripleVolume, A] using habs

-- ============================================================================
-- Extend a unit vector to an orthonormal basis of Point 3
-- ============================================================================

/-- Any unit vector in `Point 3` can be extended to an orthonormal basis
whose first element is that vector. -/
lemma exists_orthonormal_basis_with_first (e : Point 3) (he : ‖e‖ = 1) :
    ∃ (v : Fin 3 → Point 3), Orthonormal ℝ v ∧ v 0 = e := by
  let v_init : Fin 3 → Point 3 := fun i =>
    match i with
    | 0 => e
    | _ => 0
  let s : Set (Fin 3) := {0}
  have h_card : Module.finrank ℝ (Point 3) = Fintype.card (Fin 3) := by
    simp [finrank_euclideanSpace_fin]
  have hv : Orthonormal ℝ (s.restrict v_init) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    have h_mem : i.val ∈ ({(0 : Fin 3)} : Set (Fin 3)) := by
      convert i.prop using 1
      <;> simp [s]
    have hi_val : i.val = (0 : Fin 3) := by
      rw [Set.mem_singleton_iff] at h_mem
      exact h_mem
    have h_eq : s.restrict v_init i = e := by
      simp [v_init, hi_val]
      <;> rfl
    rw [h_eq]
    exact he
  rcases Orthonormal.exists_orthonormalBasis_extension_of_card_eq h_card (hv := hv)
    with ⟨b, hb⟩
  let v : Fin 3 → Point 3 := fun i => b i
  have h_v0 : v 0 = e := hb 0 (by simp [s])
  have h_orthonormal : Orthonormal ℝ v := b.orthonormal
  exact ⟨v, h_orthonormal, h_v0⟩

end Kakeya.CV
