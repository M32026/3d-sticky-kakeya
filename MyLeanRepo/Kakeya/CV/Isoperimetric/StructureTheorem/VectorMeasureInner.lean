/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: atlas
-/

import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterVariation
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DistributionalDerivative
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.TrueReducedBoundary
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry.StructureTheorem

open Perimeter

variable {n : ℕ}

/-- **Vector measure integral with density equals inner product integral.**

Given a measure `μ`, an integrable vector field `ν` with `‖ν x‖ ≤ 1` a.e.,
and an integrable test field `φ`, the vector measure integral of `φ` against
`μ.withDensityᵥ ν` (paired via `innerBilinear`) equals the Bochner integral of
`inner ℝ (φ x) (ν x)` against `μ`. -/
lemma integral_withDensityᵥ_inner {μ : Measure (E n)} {ν : E n → E n}
    (hν_int : Integrable ν μ) (hν_bound : ∀ᵐ x ∂μ, ‖ν x‖ ≤ 1)
    {φ : E n → E n} (hφ_int : Integrable φ μ) :
    ∫ᵛ x, φ x ∂[innerBilinear; μ.withDensityᵥ ν] =
      ∫ x, inner ℝ (φ x) (ν x) ∂μ := by
  let D := μ.withDensityᵥ ν
  let T := D.transpose innerBilinear
  let L : (E n) →L[ℝ] ((E n) →L[ℝ] ℝ) := innerBilinear.flip
  let g : E n → (E n →L[ℝ] ℝ) := fun x => L (ν x)
  have hg_int : Integrable g μ := L.integrable_comp hν_int

  -- Helper: inner product with bounded ν is integrable for any integrable f
  have h_inner_integrable : ∀ {f : E n → E n}, Integrable f μ →
      Integrable (fun x : E n => inner ℝ (f x) (ν x)) μ := by
    intro f hf
    have h1 : AEStronglyMeasurable (fun x : E n => inner ℝ (f x) (ν x)) μ :=
      hf.1.inner hν_int.1
    have h2 : ∀ᵐ x ∂μ, ‖inner ℝ (f x) (ν x)‖ ≤ ‖(fun x : E n => ‖f x‖) x‖ := by
      filter_upwards [hν_bound] with x hx
      have h3 : ‖inner ℝ (f x) (ν x)‖ = |inner ℝ (f x) (ν x)| := by simp
      rw [h3]
      have h4 : |inner ℝ (f x) (ν x)| ≤ ‖f x‖ * ‖ν x‖ := abs_real_inner_le_norm (f x) (ν x)
      have h5 : ‖f x‖ * ‖ν x‖ ≤ ‖f x‖ := by
        exact mul_le_of_le_one_right (norm_nonneg (f x)) hx
      have h6 : ‖(fun x : E n => ‖f x‖) x‖ = ‖f x‖ := by
        simp [abs_of_nonneg (norm_nonneg (f x))]
      rw [h6]
      exact h4.trans h5
    exact Integrable.mono hf.norm h1 h2

  -- Step 1: T = μ.withDensityᵥ g
  have hT_eq : T = μ.withDensityᵥ g := by
    apply VectorMeasure.ext
    intro s hs
    have h1 : T s = innerBilinear.flip (D s) := by rfl
    rw [h1]
    have h2 : D s = ∫ x in s, ν x ∂μ := withDensityᵥ_apply hν_int hs
    rw [h2]
    have h31 : innerBilinear.flip (∫ x in s, ν x ∂μ) = ∫ x in s, g x ∂μ := by
      apply ContinuousLinearMap.ext
      intro v
      have h4 : innerBilinear.flip (∫ x in s, ν x ∂μ) v =
          inner ℝ v (∫ x in s, ν x ∂μ) := by
        simpa [innerBilinear_apply] using rfl
      rw [h4]
      have h5 : inner ℝ v (∫ x in s, ν x ∂μ) = ∫ x in s, inner ℝ v (ν x) ∂μ :=
        (integral_inner (𝕜 := ℝ) (E := E n) hν_int.integrableOn v).symm
      rw [h5]
      have h6 : (∫ x in s, g x ∂μ) v = ∫ x in s, (g x) v ∂μ :=
        ContinuousLinearMap.integral_apply hg_int.integrableOn v
      rw [h6] <;> rfl
    have h32 : (μ.withDensityᵥ g) s = ∫ x in s, g x ∂μ :=
      withDensityᵥ_apply hg_int hs
    rw [h32]
    exact h31

  -- Step 2: D.variation ≤ μ
  have hD_var_le : D.variation ≤ μ := by
    apply Measure.le_iff.mpr
    intro s hs
    have h1 : ∀ (E : Set (E n)), MeasurableSet E → E ⊆ s → ‖D E‖ₑ ≤ μ E := by
      intro E hE _
      have h2 : ‖D E‖ₑ ≤ ∫⁻ x in E, ‖ν x‖ₑ ∂μ := by
        have hD_eq : D E = ∫ x in E, ν x ∂μ := withDensityᵥ_apply hν_int hE
        rw [hD_eq]
        exact enorm_integral_le_lintegral_enorm (f := ν)
      have h3 : ∫⁻ x in E, ‖ν x‖ₑ ∂μ ≤ ∫⁻ x in E, (1 : ENNReal) ∂μ := by
        apply lintegral_mono_ae
        have h4 : ∀ᵐ x ∂(μ.restrict E), ‖ν x‖ₑ ≤ (1 : ENNReal) := by
          have h5 : ∀ᵐ x ∂μ, ‖ν x‖ₑ ≤ (1 : ENNReal) := by
            filter_upwards [hν_bound] with x hx
            have h6 : ‖ν x‖ₑ = ENNReal.ofReal ‖ν x‖ := (ofReal_norm (ν x)).symm
            rw [h6]
            exact ENNReal.ofReal_le_one.mpr hx
          exact h5.filter_mono (ae_restrict_le (s := E))
        exact h4
      simpa using h2.trans h3
    exact VectorMeasure.variation_apply_le_of_forall_enorm_le hs h1

  have hD_var_le' : D.variation ≤ (1 : ENNReal) • μ := by
    simpa [one_smul] using hD_var_le

  -- Step 3: T is dominated by μ with constant 1
  have hT_add : ∀ (s t : Set (E n)), MeasurableSet s → MeasurableSet t →
      μ s ≠ ⊤ → μ t ≠ ⊤ → Disjoint s t → T (s ∪ t) = T s + T t := by
    intro s t hs ht _ _ hdisj
    exact cbmApplyMeasure_union D innerBilinear hs ht hdisj
  have hT_bound : ∀ (s : Set (E n)), MeasurableSet s → μ s < ⊤ → ‖T s‖ ≤ 1 * μ.real s := by
    intro s hs hμs
    have h1 : ‖T s‖ = ‖D s‖ := by
      have h_eq : T s = innerBilinear.flip (D s) := by rfl
      rw [h_eq]
      exact innerFunctional_norm (D s)
    have h2 : ‖D s‖ₑ ≤ D.variation s := VectorMeasure.enorm_measure_le_variation D s
    have h4 : D.variation s ≤ μ s := hD_var_le s
    have h5 : ‖T s‖ₑ ≤ μ s := by
      have h6 : ‖T s‖ₑ = ENNReal.ofReal ‖T s‖ := (ofReal_norm (T s)).symm
      rw [h6]
      have h7 : ‖D s‖ₑ = ENNReal.ofReal ‖D s‖ := (ofReal_norm (D s)).symm
      have h8 : ENNReal.ofReal ‖D s‖ ≤ D.variation s := by rwa [h7] at h2
      have h9 : ENNReal.ofReal ‖T s‖ = ENNReal.ofReal ‖D s‖ := by rw [h1]
      rw [h9]
      exact h8.trans h4
    have h10 : ‖T s‖ ≤ (μ s).toReal := by
      have h11 : ‖T s‖ₑ ≤ μ s := h5
      have h12 : ‖T s‖ₑ = ENNReal.ofReal ‖T s‖ := (ofReal_norm (T s)).symm
      rw [h12] at h11
      exact (ENNReal.ofReal_le_iff_le_toReal hμs.ne).mp h11
    simpa [Measure.real] using h10
  let hT_dom : DominatedFinMeasAdditive μ T 1 :=
    ⟨hT_add, hT_bound⟩

  -- Step 4: Continuity of inner product integral on L1
  let F : (E n →₁[μ] E n) → ℝ := fun f => ∫ x, inner ℝ (f x) (ν x) ∂μ
  have hF_integrable : ∀ (f : (E n →₁[μ] E n)),
      Integrable (fun x : E n => inner ℝ (f x) (ν x)) μ :=
    fun f => h_inner_integrable (L1.integrable_coeFn f)
  have hF_add : ∀ (f g : (E n →₁[μ] E n)), F (f + g) = F f + F g := by
    intro f g
    have h3 : (fun x => inner ℝ ((f + g) x) (ν x)) =ᵐ[μ]
        fun x => inner ℝ (f x) (ν x) + inner ℝ (g x) (ν x) := by
      filter_upwards [Lp.coeFn_add f g] with x hx
      simp only [hx, Pi.add_apply]
      rw [inner_add_left]
    have h4 : ∫ x, inner ℝ ((f + g) x) (ν x) ∂μ =
        ∫ x, (inner ℝ (f x) (ν x) + inner ℝ (g x) (ν x)) ∂μ :=
      integral_congr_ae h3
    have h5 : ∫ x, (inner ℝ (f x) (ν x) + inner ℝ (g x) (ν x)) ∂μ =
        (∫ x, inner ℝ (f x) (ν x) ∂μ) + ∫ x, inner ℝ (g x) (ν x) ∂μ :=
      integral_add (hF_integrable f) (hF_integrable g)
    simp only [F]
    rw [h4, h5]
  have hF_smul : ∀ (c : ℝ) (f : (E n →₁[μ] E n)), F (c • f) = c • F f := by
    intro c f
    have h3 : (fun x => inner ℝ ((c • f) x) (ν x)) =ᵐ[μ]
        fun x => c * inner ℝ (f x) (ν x) := by
      filter_upwards [Lp.coeFn_smul c f] with x hx
      have h9 : (c • f) x = c • f x := by
        exact hx.trans (Pi.smul_apply c (↑↑f) x)
      rw [h9]
      have h10 : inner ℝ (c • f x) (ν x) = c * inner ℝ (f x) (ν x) := by
        have h11 : inner ℝ (c • f x) (ν x) = (starRingEnd ℝ) c * inner ℝ (f x) (ν x) :=
          inner_smul_left (x := f x) (y := ν x) (r := c)
        have h12 : (starRingEnd ℝ) c = c := by simp
        rw [h11, h12]
      exact h10
    have h4 : ∫ x, inner ℝ ((c • f) x) (ν x) ∂μ =
        ∫ x, c * inner ℝ (f x) (ν x) ∂μ :=
      integral_congr_ae h3
    have h5 : ∫ x, c * inner ℝ (f x) (ν x) ∂μ =
        c * ∫ x, inner ℝ (f x) (ν x) ∂μ :=
      integral_const_mul c _
    simp only [F]
    rw [h4, h5] <;> rfl
  let F_lin : (E n →₁[μ] E n) →ₗ[ℝ] ℝ :=
    { toFun := F, map_add' := hF_add, map_smul' := hF_smul }
  have hF_bound : ∀ (f : (E n →₁[μ] E n)), ‖F_lin f‖ ≤ 1 * ‖f‖ := by
    intro f
    have h1 : ‖F f‖ ≤ ∫ x, ‖inner ℝ (f x) (ν x)‖ ∂μ :=
      norm_integral_le_integral_norm (fun x => inner ℝ (f x) (ν x))
    have h2 : ∫ x, ‖inner ℝ (f x) (ν x)‖ ∂μ ≤ ∫ x, ‖f x‖ ∂μ := by
      apply integral_mono_ae (hF_integrable f).norm (L1.integrable_coeFn f).norm
      filter_upwards [hν_bound] with x hx
      have h3 : ‖inner ℝ (f x) (ν x)‖ = |inner ℝ (f x) (ν x)| := by simp
      rw [h3]
      have h4 : |inner ℝ (f x) (ν x)| ≤ ‖f x‖ * ‖ν x‖ := abs_real_inner_le_norm (f x) (ν x)
      have h5 : ‖f x‖ * ‖ν x‖ ≤ ‖f x‖ := by
        exact mul_le_of_le_one_right (norm_nonneg (f x)) hx
      exact h4.trans h5
    have h6 : ‖F_lin f‖ ≤ ∫ x, ‖f x‖ ∂μ := by
      simpa [F_lin] using h1.trans h2
    have h7 : ‖f‖ = ∫ x, ‖f x‖ ∂μ := L1.norm_eq_integral_norm f
    have h8 : ‖F_lin f‖ ≤ ‖f‖ := by
      calc
        ‖F_lin f‖ ≤ ∫ x, ‖f x‖ ∂μ := h6
        _ = ‖f‖ := h7.symm
    simpa using h8
  let F_clm : (E n →₁[μ] E n) →L[ℝ] ℝ :=
    F_lin.mkContinuous 1 hF_bound

  -- Step 5: Prove identity for all integrable f using Integrable.induction
  let P : (E n → E n) → Prop := fun f =>
    setToFun μ T hT_dom f = ∫ x, inner ℝ (f x) (ν x) ∂μ
  have h_ind : ∀ (c : E n) ⦃s : Set (E n)⦄, MeasurableSet s → μ s < ⊤ → P (s.indicator fun _ => c) := by
    intro c s hs hμs
    dsimp only [P]
    rw [setToFun_indicator_const hT_dom hs hμs.ne c]
    have h4 : T s c = inner ℝ c (D s) := by
      have h41 : T s = innerBilinear.flip (D s) := by rfl
      rw [h41]
      simpa [innerBilinear_apply] using rfl
    rw [h4]
    have h5 : D s = ∫ x in s, ν x ∂μ := withDensityᵥ_apply hν_int hs
    rw [h5]
    have h6 : inner ℝ c (∫ x in s, ν x ∂μ) = ∫ x in s, inner ℝ c (ν x) ∂μ :=
      (integral_inner (𝕜 := ℝ) (E := E n) hν_int.integrableOn c).symm
    rw [h6]
    have h7 : ∫ x in s, inner ℝ c (ν x) ∂μ =
        ∫ x, inner ℝ ((s.indicator fun _ : E n => c) x) (ν x) ∂μ := by
      have h8 : (fun x : E n => inner ℝ ((s.indicator fun _ : E n => c) x) (ν x)) =
          s.indicator (fun x : E n => inner ℝ c (ν x)) := by
        funext x
        by_cases hx : x ∈ s <;> simp [hx, Set.indicator_apply] <;> aesop
      rw [h8]
      rw [integral_indicator hs]
      <;> rfl
    exact h7
  have h_add : ∀ ⦃f g : E n → E n⦄, Disjoint (Function.support f) (Function.support g) →
      Integrable f μ → Integrable g μ → P f → P g → P (f + g) := by
    intro f g _ hf hg ihf ihg
    dsimp only [P] at *
    have h9 : (fun x => inner ℝ ((f + g) x) (ν x)) =
        fun x => inner ℝ (f x) (ν x) + inner ℝ (g x) (ν x) := by
      funext x
      have h10 : (f + g) x = f x + g x := Pi.add_apply f g x
      rw [h10, inner_add_left]
    have h_int_add : ∫ x, inner ℝ ((f + g) x) (ν x) ∂μ =
        (∫ x, inner ℝ (f x) (ν x) ∂μ) + ∫ x, inner ℝ (g x) (ν x) ∂μ := by
      rw [h9]
      exact integral_add (h_inner_integrable hf) (h_inner_integrable hg)
    rw [setToFun_add hT_dom hf hg, ihf, ihg, h_int_add]
  have h_closed : IsClosed {f : (E n →₁[μ] E n) | P (f : E n → E n)} := by
    exact isClosed_eq (continuous_setToFun hT_dom) F_clm.continuous
  have h_ae : ∀ ⦃f g : E n → E n⦄, f =ᵐ[μ] g → Integrable f μ → P f → P g := by
    intro f g hfg _ ihf
    dsimp only [P] at *
    have h7 : (fun x => inner ℝ (f x) (ν x)) =ᵐ[μ] (fun x => inner ℝ (g x) (ν x)) := by
      filter_upwards [hfg] with x hx
      rw [hx]
    have h9 : setToFun μ T hT_dom g = setToFun μ T hT_dom f := (setToFun_congr_ae hT_dom hfg).symm
    rw [h9, ihf, integral_congr_ae h7]
  have h_main : ∀ (f : E n → E n), Integrable f μ → P f := by
    intro f hf
    exact Integrable.induction P h_ind h_add h_closed h_ae hf

  -- Step 6: Connect to original integral
  have h_orig : ∫ᵛ x, φ x ∂[innerBilinear; D] =
      setToFun D.variation T (dominatedFinMeasAdditive_cbmApplyMeasure D innerBilinear) φ :=
    VectorMeasure.integral_eq_setToFun (f := φ)

  have h_congr : setToFun μ T hT_dom φ =
      setToFun D.variation T (dominatedFinMeasAdditive_cbmApplyMeasure D innerBilinear) φ :=
    setToFun_congr_measure_of_integrable (1 : ENNReal) one_ne_top hD_var_le'
      hT_dom (dominatedFinMeasAdditive_cbmApplyMeasure D innerBilinear) φ hφ_int

  rw [h_orig, ←h_congr]
  exact h_main φ hφ_int

/-- **Distributional derivative integral equals inner product integral.**

For a set `S` of finite perimeter and an integrable vector field `φ`,
the vector measure integral of `φ` against the distributional derivative
`Dχ_S` equals the Bochner integral of `inner(φ, ν_S)` against the perimeter
measure, where `ν_S = measureTheoreticNormal S`. -/
lemma distributionalDerivative_integral_eq_inner (S : Set (E n))
    (hfin : perimeter S < ⊤) {φ : E n → E n}
    (hφ_int : Integrable φ (perimeterMeasure S)) :
    ∫ᵛ x, φ x ∂[innerBilinear; distributionalDerivative S] =
      ∫ x, inner ℝ (φ x) (measureTheoreticNormal S x) ∂(perimeterMeasure S) := by
  let μ := perimeterMeasure S
  let f := measureTheoreticNormal S
  have hν_int : Integrable f μ := (measureTheoreticNormal_withDensity hfin).1
  have hD_eq : distributionalDerivative S = μ.withDensityᵥ f :=
    (measureTheoreticNormal_withDensity hfin).2
  have hν_norm_one : ∀ᵐ x ∂μ, ‖f x‖ = 1 := norm_measureTheoreticNormal_eq_one hfin
  have hν_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1 := by
    filter_upwards [hν_norm_one] with x hx
    rw [hx] <;> norm_num
  rw [hD_eq]
  exact integral_withDensityᵥ_inner hν_int hν_bound hφ_int

end Geometry.StructureTheorem
