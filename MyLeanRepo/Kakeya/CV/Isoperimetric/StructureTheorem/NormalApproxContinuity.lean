import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.TrueReducedBoundary
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.ReducedBoundaryData
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.ReducedBoundaryOrientation
import Mathlib.Tactic

/-!
# Normal approximate continuity a.e.

Proves that the measure-theoretic normal is approximately continuous
with respect to perimeter measure at μ-a.e. point, using Besicovitch
differentiation. This is the correct replacement for the overly strong
`LebesgueDiffHyp`.
-/


open MeasureTheory Metric Set Filter

namespace Geometry.StructureTheorem

open Perimeter

variable {n : ℕ}

/-- Approximate continuity of the normal field: for μ-a.e. x, the average
of ‖ν(y) - ν(x)‖ over closedBall x r tends to 0 as r → 0+. -/
lemma normal_approx_continuity_ae
    {U : Set (E n)} (h_perim_finite : perimeter U < ⊤) :
    ∀ᵐ (x : E n) ∂(perimeterMeasure U),
      Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, ‖measureTheoreticNormal U y - measureTheoreticNormal U x‖ ∂(perimeterMeasure U)) /
          (perimeterMeasure U (closedBall x r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let μ := perimeterMeasure U
  let f := measureTheoreticNormal U
  have hμ_fin : μ Set.univ < ⊤ := by
    rw [← perimeter_eq_variation U h_perim_finite] <;> exact h_perim_finite
  letI : IsFiniteMeasure μ := ⟨hμ_fin⟩
  letI : IsLocallyFiniteMeasure μ := by infer_instance

  have hf_meas : Measurable f := measureTheoreticNormal_measurable h_perim_finite
  have hf_norm_one : ∀ᵐ y ∂μ, ‖f y‖ = 1 := norm_measureTheoreticNormal_eq_one h_perim_finite
  have hf_int : Integrable f μ := by
    have h_bound : ∀ᵐ y ∂μ, ‖f y‖ ≤ 1 := by
      filter_upwards [hf_norm_one] with y hy <;> rw [hy] <;> norm_num
    have h_sm : AEStronglyMeasurable f μ := hf_meas.aestronglyMeasurable
    exact Integrable.of_bound h_sm 1 h_bound

  let v := Besicovitch.vitaliFamily μ
  have h_main : ∀ᵐ (x : E n) ∂μ,
      Tendsto (fun a : Set (E n) => ⨍ y in a, ‖f y - f x‖ ∂μ) (v.filterAt x) (nhds 0) :=
    VitaliFamily.ae_tendsto_average_norm_sub v hf_int.locallyIntegrable

  filter_upwards [h_main] with x hx
  have h_tendsto_filter : Tendsto (fun r : ℝ => closedBall x r) (nhdsWithin 0 (Set.Ioi 0)) (v.filterAt x) :=
    Besicovitch.tendsto_filterAt μ x
  have h_comp : Tendsto (fun r : ℝ => ⨍ y in closedBall x r, ‖f y - f x‖ ∂μ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    hx.comp h_tendsto_filter
  have h_eq : ∀ (r : ℝ), (⨍ y in closedBall x r, ‖f y - f x‖ ∂μ) =
      (∫ y in closedBall x r, ‖f y - f x‖ ∂μ) / (μ (closedBall x r)).toReal := by
    intro r
    simp [MeasureTheory.average_eq, div_eq_mul_inv, Measure.real]
    <;> ring
  have h_final : Tendsto (fun r : ℝ => (∫ y in closedBall x r, ‖f y - f x‖ ∂μ) / (μ (closedBall x r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    convert h_comp using 1
    funext r
    exact (h_eq r).symm
  exact h_final

/-- Bridge: normal approximate continuity implies the weakened orientation
differentiation hypothesis for `|inner(ν(x), ν(y)) - 1|`. -/
lemma leb_abs_from_normal_approx_continuity
    {U : Set (E n)} {x : E n} {ν : E n}
    (h_perim_finite : perimeter U < ⊤)
    (hν_unit : ‖ν‖ = 1)
    (hν_eq : measureTheoreticNormal U x = ν)
    (h_strong : Filter.Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, ‖measureTheoreticNormal U y - measureTheoreticNormal U x‖ ∂(perimeterMeasure U)) /
          (perimeterMeasure U (closedBall x r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, |inner ℝ ν (measureTheoreticNormal U y) - 1| ∂(perimeterMeasure U)) /
          (perimeterMeasure U (closedBall x r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let μ := perimeterMeasure U
  let f := measureTheoreticNormal U
  have hμ_fin : μ Set.univ < ⊤ := by
    rw [← perimeter_eq_variation U h_perim_finite] <;> exact h_perim_finite
  letI : IsFiniteMeasure μ := ⟨hμ_fin⟩
  have hν_int : Integrable f μ := by
    have h_bound : ∀ᵐ y ∂μ, ‖f y‖ ≤ 1 := by
      have h_norm : ∀ᵐ y ∂μ, ‖f y‖ = 1 := norm_measureTheoreticNormal_eq_one h_perim_finite
      filter_upwards [h_norm] with y hy <;> rw [hy] <;> norm_num
    have h_sm : AEStronglyMeasurable f μ := (measureTheoreticNormal_measurable h_perim_finite).aestronglyMeasurable
    exact Integrable.of_bound h_sm 1 h_bound
  have h1 : ∀ y, |inner ℝ ν (f y) - 1| ≤ ‖f y - f x‖ := by
    intro y
    have h2 : inner ℝ ν (f y) - 1 = inner ℝ ν (f y - f x) := by
      have h3 : inner ℝ ν (f x) = 1 := by
        have hfx : f x = ν := by exact_mod_cast hν_eq
        rw [hfx]
        have h4 : inner ℝ ν ν = ‖ν‖ ^ 2 := inner_self_eq_norm_sq_to_K ν
        rw [h4, hν_unit] <;> norm_num
      simp [inner_sub_right, h3] <;> ring
    rw [h2]
    have h3 : |inner ℝ ν (f y - f x)| ≤ ‖ν‖ * ‖f y - f x‖ := abs_real_inner_le_norm ν (f y - f x)
    rw [hν_unit] at h3
    simpa using h3
  let L : (E n) →L[ℝ] ℝ :=
    { toFun := fun z => inner ℝ ν z
      map_add' := by simp [inner_add_right]
      map_smul' := by simp [inner_smul_right] <;> ring }
  have h_avg_le : ∀ r, ((∫ y in closedBall x r, |inner ℝ ν (f y) - 1| ∂μ) / (μ (closedBall x r)).toReal) ≤
      ((∫ y in closedBall x r, ‖f y - f x‖ ∂μ) / (μ (closedBall x r)).toReal) := by
    intro r
    by_cases h5 : (μ (closedBall x r)).toReal = 0
    · simp [h5]
    · have h6 : 0 < (μ (closedBall x r)).toReal := by
        have h7 : 0 ≤ (μ (closedBall x r)).toReal := by positivity
        exact h7.lt_of_ne (Ne.symm h5)
      have h_int1 : IntegrableOn (fun y => |inner ℝ ν (f y) - 1|) (closedBall x r) μ := by
        have h : Integrable (fun y => |inner ℝ ν (f y) - 1|) μ := by
          have h' : Integrable (fun y => inner ℝ ν (f y)) μ := L.integrable_comp hν_int
          exact h'.sub (integrable_const 1) |>.abs
        exact h.integrableOn
      have h_int2 : IntegrableOn (fun y => ‖f y - f x‖) (closedBall x r) μ := by
        exact (hν_int.sub (integrable_const (f x))).norm.integrableOn
      have h7 : ∫ y in closedBall x r, |inner ℝ ν (f y) - 1| ∂μ ≤ ∫ y in closedBall x r, ‖f y - f x‖ ∂μ :=
        setIntegral_mono_on h_int1 h_int2 measurableSet_closedBall (fun y _ => h1 y)
      exact div_le_div_of_nonneg_right h7 (by positivity)
  have h_nonneg : ∀ r, 0 ≤ ((∫ y in closedBall x r, |inner ℝ ν (f y) - 1| ∂μ) / (μ (closedBall x r)).toReal) := by
    intro r
    by_cases h5 : (μ (closedBall x r)).toReal = 0
    · simp [h5]
    · exact div_nonneg (integral_nonneg (fun _ => abs_nonneg _)) (by positivity)
  exact squeeze_zero h_nonneg h_avg_le h_strong

/-- A.e. bridge: normal approximate continuity a.e. implies the weakened
orientation differentiation hypothesis a.e. -/
lemma leb_abs_ae
    {U : Set (E n)} (h_perim_finite : perimeter U < ⊤) :
    ∀ᵐ (x : E n) ∂(perimeterMeasure U),
      ∀ (ν : E n), ‖ν‖ = 1 → measureTheoreticNormal U x = ν →
        Filter.Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, |inner ℝ ν (measureTheoreticNormal U y) - 1| ∂(perimeterMeasure U)) /
            (perimeterMeasure U (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h1 := normal_approx_continuity_ae h_perim_finite
  have h2 : ∀ᵐ (x : E n) ∂(perimeterMeasure U), ‖measureTheoreticNormal U x‖ = 1 :=
    norm_measureTheoreticNormal_eq_one h_perim_finite
  filter_upwards [h1, h2] with x hx_strong hx_norm ν hν_unit hν_eq
  exact leb_abs_from_normal_approx_continuity h_perim_finite hν_unit hν_eq hx_strong

end Geometry.StructureTheorem
