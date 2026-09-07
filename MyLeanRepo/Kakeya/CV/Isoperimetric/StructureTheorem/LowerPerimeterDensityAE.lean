import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.TrueReducedBoundary
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterMeasureSupport
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterDensityUpperBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterLowerDensityAtTRB
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.Maggi15LowerDensity
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.NormalApproxContinuity
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.M4DirectionalUpgrade
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.RBCEasyLemmas
import Mathlib.Tactic

/-!
# Structure Theorem Assembly — M1-Independent Part

Assembles lower perimeter density at μ-a.e. true reduced boundary point
using proved results.
-/


open MeasureTheory Metric Set Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

open Perimeter

variable {n : ℕ}

/-- Lower perimeter density at μ-a.e. true reduced boundary point. -/
theorem lower_perimeter_density_ae_at_trb
    {U : Set (E n)} (hU : IsOpen U) (hU_reg : U = interior (closure U))
    (hBdd : Bornology.IsBounded U) (h_perim_finite : perimeter U < ⊤) (hn : 2 ≤ n) :
    ∃ (N : Set (E n)), MeasurableSet N ∧ perimeterMeasure U N = 0 ∧
      ∀ x ∈ trueReducedBoundary U \ N,
        ∃ (c : ℝ) (r₀ : ℝ), 0 < c ∧ 0 < r₀ ∧
          ∀ (r : ℝ), 0 < r → r < r₀ →
            ENNReal.ofReal (c * r ^ (n - 1)) ≤ perimeterIn U (ball x r) := by
  let μ := perimeterMeasure U
  let ν_U := measureTheoreticNormal U

  have hμ_fin : μ Set.univ < ⊤ := by
    rw [← perimeter_eq_variation U h_perim_finite] <;> exact h_perim_finite
  letI : IsFiniteMeasure μ := ⟨hμ_fin⟩

  -- Upper density a.e.
  have h_upper_ae : ∀ᵐ (x : E n) ∂μ,
      ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterIn U (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)) :=
    perimeter_density_upper_bound hU hBdd h_perim_finite hn

  -- Directional absolute inner product Lebesgue differentiation a.e.
  have h_abs_ae : ∀ᵐ (x : E n) ∂μ,
      ∀ (w : E n),
        Filter.Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, |inner ℝ w (ν_U y)| ∂μ) / (μ (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (|inner ℝ w (ν_U x)|)) :=
    abs_inner_lebesgue_diff_ae h_perim_finite

  -- |inner(ν(x), ν(y)) - 1| average → 0 a.e.
  have h_leb_abs_ae : ∀ᵐ (x : E n) ∂μ,
      ∀ (ν : E n), ‖ν‖ = 1 → ν_U x = ν →
        Filter.Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, |inner ℝ ν (ν_U y) - 1| ∂μ) / (μ (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    leb_abs_ae h_perim_finite

  -- Two-sided volume density at TRB points (from Maggi 15.5)
  rcases maggi15_volume_lower_density hU hU_reg hBdd h_perim_finite hn with
    ⟨N_vol, hN_vol_meas, hN_vol_null, h_vol_density⟩

  -- Combine all a.e. properties
  let P : E n → Prop := fun x =>
      (∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterIn U (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1))) ∧
      (∀ (w : E n),
        Filter.Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, |inner ℝ w (ν_U y)| ∂μ) / (μ (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (|inner ℝ w (ν_U x)|))) ∧
      (∀ (ν : E n), ‖ν‖ = 1 → ν_U x = ν →
        Filter.Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, |inner ℝ ν (ν_U y) - 1| ∂μ) / (μ (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))

  have h_all_ae : ∀ᵐ (x : E n) ∂μ, P x :=
    h_upper_ae.and (h_abs_ae.and h_leb_abs_ae)

  let Bad : Set (E n) := {x | ¬P x}
  have hBad_null : μ Bad = 0 := (ae_iff).mp h_all_ae
  rcases MeasureTheory.exists_measurable_superset μ Bad with ⟨N_bad, hBad_sub, hN_bad_meas, hN_bad_eq⟩
  have hN_bad_null : μ N_bad = 0 := by rw [hN_bad_eq, hBad_null]

  let N := N_vol ∪ N_bad
  have hN_meas : MeasurableSet N := hN_vol_meas.union hN_bad_meas
  have hN_null : μ N = 0 := by
    rw [measure_union_null] <;> tauto

  refine ⟨N, hN_meas, hN_null, ?_⟩
  intro x hx
  have hx_trb : x ∈ trueReducedBoundary U := hx.1
  have hx_notN : x ∉ N := hx.2
  have hx_not_vol : x ∉ N_vol := fun h => hx_notN (Or.inl h)
  have hx_not_bad : x ∉ N_bad := fun h => hx_notN (Or.inr h)
  have hx_notBad0 : x ∉ Bad := fun h => hx_not_bad (hBad_sub h)
  have hx_all : P x := by simpa [Bad] using hx_notBad0
  rcases hx_all with ⟨h_upper_raw, h_abs_fn, h_leb_abs_fn⟩
  have hν_unit : ‖ν_U x‖ = 1 := hx_trb.2

  -- For x ∈ TRB, μ(closedBall x r) > 0 for all r > 0
  have h_pos : ∀ (r : ℝ), 0 < r → 0 < μ (closedBall x r) := by
    intro r hr
    have h1 : 0 < μ (ball x r) := hx_trb.1 r hr
    have h2 : μ (ball x r) ≤ μ (closedBall x r) := measure_mono ball_subset_closedBall
    exact lt_of_lt_of_le h1 h2

  have h_pos_real : ∀ (r : ℝ), 0 < r → 0 < (μ (closedBall x r)).toReal := by
    intro r hr
    have h3 : 0 < μ (closedBall x r) := h_pos r hr
    have h4 : μ (closedBall x r) < ⊤ := measure_lt_top μ (closedBall x r)
    exact ENNReal.toReal_pos_iff.mpr ⟨h3, h4⟩

  -- Volume density at this x
  have h_vol : ∃ (c : ℝ) (R : ℝ), 0 < c ∧ 0 < R ∧
      ∀ r, 0 < r → r < R →
        volume (U ∩ ball x r) ≥ ENNReal.ofReal (c * r ^ n) ∧
        volume ((ball x r) \ U) ≥ ENNReal.ofReal (c * r ^ n) :=
    h_vol_density x ⟨hx_trb, hx_not_vol⟩

  -- Convert upper density from perimeterIn to perimeterMeasure on closedBall
  rcases h_upper_raw with ⟨C_ud, r0_ud, hC_ud_pos, hr0_ud_pos, h_ud_bound⟩
  have h_upper_closed : ∃ (C' : ℝ) (r0' : ℝ), 0 < C' ∧ 0 < r0' ∧
      ∀ r, 0 < r → r < r0' →
        μ (closedBall x r) ≤ ENNReal.ofReal (C' * r ^ (n - 1)) :=
    upper_bound_perimeterMeasure_from_perimeterIn h_perim_finite hC_ud_pos hr0_ud_pos h_ud_bound hn

  -- h_abs_lebesgue: for w orthogonal to ν_U x, the limit is 0
  have h_abs_lebesgue : ∀ (w : E n), inner ℝ w (ν_U x) = 0 →
      Filter.Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, |inner ℝ w (ν_U y)| ∂μ) / (μ (closedBall x r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro w hw
    have h_limit := h_abs_fn w
    have h9 : |inner ℝ w (ν_U x)| = 0 := by
      rw [hw] <;> simp
    rw [h9] at h_limit
    simpa using h_limit

  -- Inner product convergence to 1
  have h_leb_abs : Filter.Tendsto (fun r : ℝ =>
      (∫ y in closedBall x r, |inner ℝ (ν_U x) (ν_U y) - 1| ∂μ) / (μ (closedBall x r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    h_leb_abs_fn (ν_U x) hν_unit rfl

  let f : ℝ → E n → ℝ := fun r y => inner ℝ (ν_U x) (ν_U y)
  have h_integrable : ∀ (r : ℝ), IntegrableOn (f r) (closedBall x r) μ := by
    intro r
    have hν_int : Integrable ν_U μ := by
      have h_bound : ∀ᵐ y ∂μ, ‖ν_U y‖ ≤ 1 := by
        have h_norm : ∀ᵐ y ∂μ, ‖ν_U y‖ = 1 := norm_measureTheoreticNormal_eq_one h_perim_finite
        filter_upwards [h_norm] with y hy <;> rw [hy] <;> norm_num
      have h_sm : AEStronglyMeasurable ν_U μ :=
        (measureTheoreticNormal_measurable h_perim_finite).aestronglyMeasurable
      exact Integrable.of_bound h_sm 1 h_bound
    let L : (E n) →L[ℝ] ℝ :=
      { toFun := fun z => inner ℝ (ν_U x) z
        map_add' := by simp [inner_add_right]
        map_smul' := by simp [inner_smul_right] <;> ring }
    exact (L.integrable_comp hν_int).integrableOn

  have h_ineq : ∀ (r : ℝ), 0 < r →
      ‖((∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) / (μ (closedBall x r)).toReal) - 1‖ ≤
      (∫ y in closedBall x r, |inner ℝ (ν_U x) (ν_U y) - 1| ∂μ) / (μ (closedBall x r)).toReal := by
    intro r hr
    set d := (μ (closedBall x r)).toReal with hd_def
    have hd_pos : 0 < d := h_pos_real r hr
    have h1 : (∫ y in closedBall x r, (1 : ℝ) ∂μ) = d := by
      simp [integral_const, hd_def] <;> rfl
    have h_int_sub : IntegrableOn (fun y => inner ℝ (ν_U x) (ν_U y) - 1) (closedBall x r) μ :=
      (h_integrable r).sub (integrable_const (1 : ℝ)).integrableOn
    have h3 : (∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) - d =
        ∫ y in closedBall x r, (inner ℝ (ν_U x) (ν_U y) - 1) ∂μ := by
      have h4 : ∫ y in closedBall x r, (inner ℝ (ν_U x) (ν_U y) - 1) ∂μ =
          (∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) - ∫ y in closedBall x r, (1 : ℝ) ∂μ :=
        integral_sub (h_integrable r) (integrable_const (1 : ℝ)).integrableOn
      rw [h4, h1]
      <;> ring
    have h2 : |(∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) - d| ≤
        ∫ y in closedBall x r, |inner ℝ (ν_U x) (ν_U y) - 1| ∂μ := by
      rw [h3]
      have h_abs : |∫ y in closedBall x r, (inner ℝ (ν_U x) (ν_U y) - 1) ∂μ| ≤
          ∫ y in closedBall x r, |inner ℝ (ν_U x) (ν_U y) - 1| ∂μ := by
        exact abs_integral_le_integral_abs
      exact h_abs
    have h4 : ‖((∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) / d) - 1‖ =
        |(∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) - d| / d := by
      have h5 : ‖((∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) / d) - 1‖ =
          |((∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) / d) - 1| := by
        exact Real.norm_eq_abs ((∫ (y : E n) in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) / d - 1)
      rw [h5]
      have h6 : ((∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) / d) - 1 =
          ((∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) - d) / d := by
        field_simp [hd_pos.ne'] <;> ring
      rw [h6]
      have h7 : |((∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) - d) / d| =
          |(∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) - d| / |d| := by
        exact abs_div _ _
      rw [h7]
      have h8 : |d| = d := abs_of_pos hd_pos
      rw [h8]
      <;> rfl
    rw [h4]
    exact div_le_div_of_nonneg_right h2 (by positivity)

  have h_inner : Filter.Tendsto (fun r : ℝ =>
      (∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) / (μ (closedBall x r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h5 : ∀ᶠ (r : ℝ) in (nhdsWithin 0 (Set.Ioi 0)),
        ‖((∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) / (μ (closedBall x r)).toReal) - 1‖ ≤
        (∫ y in closedBall x r, |inner ℝ (ν_U x) (ν_U y) - 1| ∂μ) / (μ (closedBall x r)).toReal := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact h_ineq r hr
    have h6 : Filter.Tendsto (fun r : ℝ =>
        ((∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) / (μ (closedBall x r)).toReal) - 1)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := squeeze_zero_norm' h5 h_leb_abs
    have h7 : Filter.Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) / (μ (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      simpa [tendsto_sub_nhds_zero_iff] using h6
    exact h7

  -- Apply pointwise lower density theorem
  exact perimeter_lower_density_at_trb hU hU_reg hBdd h_perim_finite hn
    x (ν_U x) hx_trb rfl hν_unit h_upper_closed h_abs_lebesgue h_inner h_vol

end Geometry.StructureTheorem
