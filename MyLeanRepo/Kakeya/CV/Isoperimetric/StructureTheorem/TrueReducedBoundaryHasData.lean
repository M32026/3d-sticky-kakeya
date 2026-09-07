import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.TrueReducedBoundary
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.ReducedBoundaryData
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterDensityUpperBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterDensityLowerBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DirectionalVariationBlowUp
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpTranslationBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpDensityHalf
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.ReducedBoundaryOrientationWeak
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.NormalApproxContinuity
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


/-!
# True Reduced Boundary Has ReducedBoundaryData

Assembles the 5 fields of `ReducedBoundaryData` at μ-a.e. true reduced boundary
point, conditional on an a.e. lower perimeter density hypothesis.

## Proof strategy

1. Collect a.e. properties: upper density, normal differentiation, scalar
   comparability, directional variation vanishing.
2. Intersect their good sets, remove the μ-null union.
3. On the remaining TRB points, verify all 5 fields.
4. Two-sided volume density comes from `perimeter_density_lower_bound`.
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

open Perimeter

variable {n : ℕ}

/-- **Conditional**: true reduced boundary points have `ReducedBoundaryData`.

Assumes lower perimeter density outside a μ-null subset of TRB. -/
theorem trueReducedBoundary_has_data
    {U : Set (E n)} (hU : IsOpen U) (hU_reg : U = interior (closure U))
    (hBdd : Bornology.IsBounded U) (h_perim_finite : perimeter U < ⊤) (hn : 2 ≤ n)
    (h_lower_density_ae : ∃ (N_lower : Set (E n)), MeasurableSet N_lower ∧
      perimeterMeasure U N_lower = 0 ∧
      ∀ x ∈ trueReducedBoundary U \ N_lower,
        ∃ (c : ℝ) (R : ℝ), 0 < c ∧ 0 < R ∧
          ∀ r, 0 < r → r < R →
            perimeterMeasure U (ball x r) ≥ ENNReal.ofReal (c * r ^ (n - 1))) :
    ∃ (N_good : Set (E n)), MeasurableSet N_good ∧
      perimeterMeasure U N_good = 0 ∧
      ∀ x ∈ trueReducedBoundary U \ N_good,
        ‖measureTheoreticNormal U x‖ = 1 ∧
        ReducedBoundaryData U x (measureTheoreticNormal U x) := by
  let μ := perimeterMeasure U
  let ν := measureTheoreticNormal U

  have hμ_fin : μ Set.univ < ⊤ := by
    have h_eq : perimeter U = μ Set.univ := perimeter_eq_variation U h_perim_finite
    rw [h_eq] at h_perim_finite; exact h_perim_finite
  letI : IsFiniteMeasure μ := ⟨hμ_fin⟩

  -- Destructure a.e. lower density
  rcases h_lower_density_ae with ⟨N_lower, hN_lower_meas, hN_lower_null, h_lower_density⟩

  -- Upper density a.e.
  have h_upper_ae : ∀ᵐ (x : E n) ∂μ,
      ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterIn U (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)) :=
    perimeter_density_upper_bound hU hBdd h_perim_finite hn

  -- Scalar comparability a.e.
  have h_scalar_ae : ∀ᵐ (x : E n) ∂μ, scalarComparabilityProperty U x :=
    scalar_comparability_ae h_perim_finite

  -- Directional vanishing at TRB (produces its own null set)
  rcases directional_vanishing_at_trb hU.measurableSet h_perim_finite hn h_upper_ae with
    ⟨N_dir, hN_dir_meas, hN_dir_null, h_dir_vanish⟩

  -- |inner(ν(x), ν(y)) - 1| differentiation a.e.
  have h_leb_abs_ae : ∀ᵐ (x : E n) ∂μ,
      ∀ (v : E n), ‖v‖ = 1 → ν x = v →
        Filter.Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, |inner ℝ v (ν y) - 1| ∂μ) / (μ (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    leb_abs_ae h_perim_finite

  -- Intersect all good sets
  let P : E n → Prop := fun x =>
      (∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterIn U (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1))) ∧
      scalarComparabilityProperty U x ∧
      (∀ (v : E n), ‖v‖ = 1 → ν x = v →
        Filter.Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, |inner ℝ v (ν y) - 1| ∂μ) / (μ (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))

  have h_all_ae : ∀ᵐ (x : E n) ∂μ, P x :=
    h_upper_ae.and (h_scalar_ae.and h_leb_abs_ae)

  let Bad : Set (E n) := {x | ¬P x}
  have hBad_null : μ Bad = 0 := (ae_iff).mp h_all_ae
  rcases MeasureTheory.exists_measurable_superset μ Bad with ⟨N_bad, hBad_sub, hN_bad_meas, hN_bad_eq⟩
  have hN_bad_null : μ N_bad = 0 := by rw [hN_bad_eq, hBad_null]

  let N_good := N_dir ∪ (N_bad ∪ N_lower)
  have hN_good_meas : MeasurableSet N_good :=
    hN_dir_meas.union (hN_bad_meas.union hN_lower_meas)
  have hN_good_null : μ N_good = 0 := by
    have h1 : μ (N_bad ∪ N_lower) = 0 := by
      rw [measure_union_null] <;> tauto
    have h2 : μ (N_dir ∪ (N_bad ∪ N_lower)) = 0 := by
      rw [measure_union_null] <;> tauto
    exact h2

  refine ⟨N_good, hN_good_meas, hN_good_null, ?_⟩
  intro x hx
  have hx_trb : x ∈ trueReducedBoundary U := hx.1
  have hx_notN : x ∉ N_good := hx.2
  have hx_notDir : x ∉ N_dir := by
    intro h; have h' : x ∈ N_good := Or.inl h
    exact hx_notN h'
  have hx_notBad : x ∉ N_bad := by
    intro h; have h' : x ∈ N_good := Or.inr (Or.inl h)
    exact hx_notN h'
  have hx_notLower : x ∉ N_lower := by
    intro h; have h' : x ∈ N_good := Or.inr (Or.inr h)
    exact hx_notN h'
  have hx_notBad0 : x ∉ Bad := fun h => hx_notBad (hBad_sub h)
  have hx_all : P x := by simpa [Bad] using hx_notBad0
  rcases hx_all with ⟨h_upper_raw, h_scalar, h_leb_abs_fn⟩

  have hν_unit : ‖ν x‖ = 1 := hx_trb.2

  -- Convert upper density from perimeterIn to perimeterMeasure on closedBall
  rcases h_upper_raw with ⟨C_ud, r0_ud, hC_ud_pos, hr0_ud_pos, h_ud_bound⟩
  have h_upper_closed : ∃ (C' : ℝ) (r0' : ℝ), 0 < C' ∧ 0 < r0' ∧
      ∀ r, 0 < r → r < r0' →
        μ (closedBall x r) ≤ ENNReal.ofReal (C' * r ^ (n - 1)) :=
    upper_bound_perimeterMeasure_from_perimeterIn h_perim_finite hC_ud_pos hr0_ud_pos h_ud_bound hn

  -- Save upper closed components for later use
  rcases h_upper_closed with ⟨C_up, R_up, hC_up_pos, hR_up_pos, h_upper_bound_closed⟩

  -- Lower density from a.e. assumption (x is outside N_lower)
  have h_lower := h_lower_density x ⟨hx_trb, hx_notLower⟩
  rcases h_lower with ⟨c_low, R_low, hc_low_pos, hR_low_pos, h_lower_bound⟩

  -- Lower real bound
  have h_lower_real : ∃ (c : ℝ) (R : ℝ), 0 < c ∧ 0 < R ∧
      ∀ r, 0 < r → r < R →
        (μ (closedBall x r)).toReal ≥ c * r ^ (n - 1) := by
    refine ⟨c_low, R_low, hc_low_pos, hR_low_pos, fun r hr hrR => ?_⟩
    have h1 : μ (ball x r) ≥ ENNReal.ofReal (c_low * r ^ (n - 1)) := h_lower_bound r hr hrR
    have h2 : μ (closedBall x r) ≥ μ (ball x r) := measure_mono (ball_subset_closedBall)
    have h3 : μ (closedBall x r) ≥ ENNReal.ofReal (c_low * r ^ (n - 1)) := le_trans h1 h2
    have h4 : μ (closedBall x r) ≠ ⊤ := measure_ne_top μ (closedBall x r)
    have h5 : ENNReal.ofReal (c_low * r ^ (n - 1)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h6 : ENNReal.ofReal (c_low * r ^ (n - 1)) ≤ μ (closedBall x r) := h3
    have h7 : (ENNReal.ofReal (c_low * r ^ (n - 1))).toReal ≤ (μ (closedBall x r)).toReal :=
      (ENNReal.toReal_le_toReal h5 h4).mpr h6
    have h8 : (ENNReal.ofReal (c_low * r ^ (n - 1))).toReal = c_low * r ^ (n - 1) := by
      have hpos : 0 ≤ c_low * r ^ (n - 1) := by positivity
      simp [hpos]
    rw [h8] at h7
    exact h7

  -- Upper real bound
  have h_upper_real : ∃ (C : ℝ) (R : ℝ), 0 < C ∧ 0 < R ∧
      ∀ r, 0 < r → r < R →
        (μ (closedBall x r)).toReal ≤ C * r ^ (n - 1) := by
    refine ⟨C_up, R_up, hC_up_pos, hR_up_pos, fun r hr hrR => ?_⟩
    have h1 : μ (closedBall x r) ≤ ENNReal.ofReal (C_up * r ^ (n - 1)) := h_upper_bound_closed r hr hrR
    have h2 : μ (closedBall x r) ≠ ⊤ := measure_ne_top μ (closedBall x r)
    have h3 : ENNReal.ofReal (C_up * r ^ (n - 1)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h4 : (μ (closedBall x r)).toReal ≤ (ENNReal.ofReal (C_up * r ^ (n - 1))).toReal :=
      (ENNReal.toReal_le_toReal h2 h3).mpr h1
    have h5 : (ENNReal.ofReal (C_up * r ^ (n - 1))).toReal = C_up * r ^ (n - 1) := by
      have hpos : 0 ≤ C_up * r ^ (n - 1) := by positivity
      simp [hpos]
    rw [h5] at h4
    exact h4

  -- Scalar comparability in the form needed
  rcases h_scalar with ⟨R_scalar, hR_scalar_pos, h_scalar'⟩
  have h_scalar_form : ∃ (R : ℝ), 0 < R ∧
      ∀ r, 0 < r → r < R →
        (∫ y in closedBall x r, inner ℝ (ν x) (ν y) ∂μ) ≥
          (1 / 2 : ℝ) * (μ (closedBall x r)).toReal :=
    ⟨R_scalar, hR_scalar_pos, h_scalar'⟩

  -- Two-sided volume density
  have h_nontrivial := perimeter_density_lower_bound hU.measurableSet h_perim_finite
    (hν_unit) rfl h_lower_real h_upper_real h_scalar_form hn

  -- Orientation differentiation at this x
  have h_leb_abs_x : Filter.Tendsto (fun r : ℝ =>
      (∫ y in closedBall x r, |inner ℝ (ν x) (ν y) - 1| ∂μ) / (μ (closedBall x r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    h_leb_abs_fn (ν x) hν_unit rfl

  -- Density lower bound in the form needed by OrientationHypothesesWeak
  have h_density_lower_form : DensityLowerBound U x n := by
    simp only [DensityLowerBound]
    exact ⟨c_low, R_low, hc_low_pos, hR_low_pos, h_lower_bound⟩

  -- Density upper bound in the form needed
  have h_density_upper_form : DensityUpperBound U x n := by
    simp only [DensityUpperBound]
    refine ⟨C_up, R_up, hC_up_pos, hR_up_pos, fun r hr hrR => ?_⟩
    have h5 : μ (ball x r) ≤ μ (closedBall x r) := measure_mono (ball_subset_closedBall)
    exact le_trans h5 (h_upper_bound_closed r hr hrR)

  -- Orientation hypothesis (weak version)
  have h_orientation_hyp : OrientationHypothesesWeak n U x (ν x) :=
    { hU := hU
      hn := hn
      h_perim_finite := h_perim_finite
      hx := hx_trb
      hν := rfl
      h_leb_abs := h_leb_abs_x
      h_density_lower := h_density_lower_form
      h_density_upper := h_density_upper_form }

  -- Field 1: volume bound (trivial)
  have h_vol_bound : ∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ENNReal), ∀ (r : ℝ), 0 < r → r < 1 →
        volume (blowUp U x r ∩ K) ≤ C := by
    intro K hK
    refine ⟨volume K, fun r _ _ => ?_⟩
    have h_sub : (blowUp U x r ∩ K) ⊆ K := by
      intro z hz; exact hz.2
    exact measure_mono h_sub

  -- Field 2: translation bound
  have h_trans_bound : ∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ℝ), ∀ (r : ℝ), 0 < r → r < 1 → ∀ (h : E n),
        volume (symmDiff (blowUp U x r) ((fun y => y + h) '' (blowUp U x r)) ∩ K) ≤
        ENNReal.ofReal (C * ‖h‖) := by
    intro K hK
    have h_upper_again : ∃ (C' : ℝ) (r0' : ℝ), 0 < C' ∧ 0 < r0' ∧
        ∀ r, 0 < r → r < r0' → μ (closedBall x r) ≤ ENNReal.ofReal (C' * r ^ (n - 1)) :=
      ⟨C_up, R_up, hC_up_pos, hR_up_pos, h_upper_bound_closed⟩
    have h_all := blow_up_translation_bound_all hU h_perim_finite hn x h_upper_again K hK
    rcases h_all with ⟨C, hC⟩
    refine ⟨C, fun r hr _ => hC r hr⟩

  -- Field 3: directional vanishing
  have h_dir_vanish_field : ∀ (K : Set (E n)), IsCompact K → ∀ (w : E n), inner ℝ w (ν x) = 0 →
      Tendsto (fun r : ℝ => directionalVariationIn (blowUp U x r) w K)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro K hK w hw
    exact h_dir_vanish x ⟨hx_trb, hx_notDir⟩ w hw K hK

  -- Field 5: orientation
  have h_orientation_field : ∀ (φ : E n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 < φ 0 →
        ∃ (r₀ : ℝ), 0 < r₀ ∧ ∀ (r : ℝ), 0 < r → r < r₀ →
          0 ≤ ∫ z in blowUp U x r, fderiv ℝ φ z (ν x) := by
    intro φ hφ hsupp hnonneg hφ0
    exact reduced_boundary_orientation_weak h_orientation_hyp φ hφ hsupp hnonneg hφ0

  -- Field 4: density (from blowUp_density_half_of_data)
  have h_density_field : Tendsto (fun r : ℝ => volume (blowUp U x r ∩ ball (0 : E n) 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (ball (0 : E n) 1) / 2)) := by
    rcases h_nontrivial with ⟨c_vol, R_vol, hc_vol_pos, hR_vol_pos, h_vol_two_sided⟩
    let R0 := min R_vol 1
    have hR0_pos : 0 < R0 := by positivity
    let s := R0 / 2
    have hs_pos : 0 < s := by positivity
    have hs_le_R0 : s ≤ R0 := by
      dsimp only [s]
      linarith [hR0_pos]
    have hs_lt_Rvol : s < R_vol := by
      dsimp only [s]
      have h6 : R0 / 2 < R0 := by linarith [hR0_pos]
      have h7 : R0 ≤ R_vol := min_le_left _ _
      linarith
    let c' := c_vol * s ^ n
    have hc'_pos : 0 < c' := by positivity
    have h_nontrivial' : ∃ (c : ℝ), 0 < c ∧ ∀ (r : ℝ), 0 < r → r < 1 →
        c * r ^ n ≤ (volume (U ∩ ball x r)).toReal ∧
        c * r ^ n ≤ (volume ((ball x r) \ U)).toReal := by
      refine ⟨c', hc'_pos, fun r hr hrR => ?_⟩
      have hr_nonneg : 0 ≤ r := by linarith
      have hrn_le_one : r ^ n ≤ 1 := by
        have h7 : r ≤ 1 := by linarith
        have h8 : 0 ≤ r := by linarith
        have h9 : r ^ n ≤ 1 ^ n := by gcongr
        simpa using h9
      by_cases h_case : r < R0
      · -- Case r < R0 ≤ R_vol: direct application
        have h_r_lt_Rvol : r < R_vol := by
          calc r < R0 := h_case
               _ ≤ R_vol := min_le_left _ _
        have h1 := h_vol_two_sided r hr h_r_lt_Rvol
        have h_ball_lt_top1 : volume (ball x r) < ⊤ := by exact measure_ball_lt_top
        have h_sub1 : (U ∩ ball x r) ⊆ ball x r := by intro z hz; exact hz.2
        have h_sub2 : ((ball x r) \ U) ⊆ ball x r := by intro z hz; exact hz.1
        have h_ne_top1 : volume (U ∩ ball x r) ≠ ⊤ :=
          ne_of_lt (lt_of_le_of_lt (measure_mono h_sub1) h_ball_lt_top1)
        have h_ne_top2 : volume ((ball x r) \ U) ≠ ⊤ :=
          ne_of_lt (lt_of_le_of_lt (measure_mono h_sub2) h_ball_lt_top1)
        have h21 : (volume (U ∩ ball x r)).toReal ≥ c_vol * r ^ n := by
          have h_eq : (ENNReal.ofReal (c_vol * r ^ n)).toReal = c_vol * r ^ n := by
            have hpos : 0 ≤ c_vol * r ^ n := by positivity
            simp [hpos]
          have h : (ENNReal.ofReal (c_vol * r ^ n)).toReal ≤ (volume (U ∩ ball x r)).toReal :=
            (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top h_ne_top1).mpr h1.1
          rw [h_eq] at h
          exact h
        have h22 : (volume ((ball x r) \ U)).toReal ≥ c_vol * r ^ n := by
          have h_eq : (ENNReal.ofReal (c_vol * r ^ n)).toReal = c_vol * r ^ n := by
            have hpos : 0 ≤ c_vol * r ^ n := by positivity
            simp [hpos]
          have h : (ENNReal.ofReal (c_vol * r ^ n)).toReal ≤ (volume ((ball x r) \ U)).toReal :=
            (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top h_ne_top2).mpr h1.2
          rw [h_eq] at h
          exact h
        have h3 : c' ≤ c_vol := by
          dsimp only [c', s]
          have h4 : s ^ n ≤ 1 := by
            have h5 : s ≤ 1 := by linarith [min_le_right R_vol (1 : ℝ)]
            have h6 : 0 ≤ s := by linarith
            have h7 : s ^ n ≤ 1 ^ n := by gcongr
            simpa using h7
          have hpos : 0 ≤ c_vol := by linarith
          nlinarith
        have h31 : c' * r ^ n ≤ c_vol * r ^ n := by
          have h5 : 0 ≤ r ^ n := by positivity
          nlinarith
        exact ⟨by linarith, by linarith⟩
      · -- Case r ≥ R0: use s = R0/2 and monotonicity
        have h_r_ge_R0 : R0 ≤ r := by linarith
        have hs_le_r : s ≤ r := by linarith
        have h1 := h_vol_two_sided s hs_pos hs_lt_Rvol
        have h_ball_mono1 : U ∩ ball x s ⊆ U ∩ ball x r := by
          intro z hz; exact ⟨hz.1, ball_subset_ball hs_le_r hz.2⟩
        have h_ball_mono2 : (ball x s) \ U ⊆ (ball x r) \ U := by
          intro z hz; exact ⟨ball_subset_ball hs_le_r hz.1, hz.2⟩
        have h_ball_s_lt_top : volume (ball x s) < ⊤ := by exact measure_ball_lt_top
        have h_sub1 : (U ∩ ball x s) ⊆ ball x s := by intro z hz; exact hz.2
        have h_sub2 : ((ball x s) \ U) ⊆ ball x s := by intro z hz; exact hz.1
        have h_ne_top1 : volume (U ∩ ball x s) ≠ ⊤ :=
          ne_of_lt (lt_of_le_of_lt (measure_mono h_sub1) h_ball_s_lt_top)
        have h_ne_top2 : volume ((ball x s) \ U) ≠ ⊤ :=
          ne_of_lt (lt_of_le_of_lt (measure_mono h_sub2) h_ball_s_lt_top)
        have h31 : (volume (U ∩ ball x s)).toReal ≥ c_vol * s ^ n := by
          have h_eq : (ENNReal.ofReal (c_vol * s ^ n)).toReal = c_vol * s ^ n := by
            have hpos : 0 ≤ c_vol * s ^ n := by positivity
            simp [hpos]
          have h : (ENNReal.ofReal (c_vol * s ^ n)).toReal ≤ (volume (U ∩ ball x s)).toReal :=
            (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top h_ne_top1).mpr h1.1
          rw [h_eq] at h
          exact h
        have h32 : (volume ((ball x s) \ U)).toReal ≥ c_vol * s ^ n := by
          have h_eq : (ENNReal.ofReal (c_vol * s ^ n)).toReal = c_vol * s ^ n := by
            have hpos : 0 ≤ c_vol * s ^ n := by positivity
            simp [hpos]
          have h : (ENNReal.ofReal (c_vol * s ^ n)).toReal ≤ (volume ((ball x s) \ U)).toReal :=
            (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top h_ne_top2).mpr h1.2
          rw [h_eq] at h
          exact h
        have h_ball_r_lt_top : volume (ball x r) < ⊤ := by exact measure_ball_lt_top
        have h_sub_r1 : (U ∩ ball x r) ⊆ ball x r := by intro z hz; exact hz.2
        have h_sub_r2 : ((ball x r) \ U) ⊆ ball x r := by intro z hz; exact hz.1
        have h_ne_top_r1 : volume (U ∩ ball x r) ≠ ⊤ :=
          ne_of_lt (lt_of_le_of_lt (measure_mono h_sub_r1) h_ball_r_lt_top)
        have h_ne_top_r2 : volume ((ball x r) \ U) ≠ ⊤ :=
          ne_of_lt (lt_of_le_of_lt (measure_mono h_sub_r2) h_ball_r_lt_top)
        have h41 : (volume (U ∩ ball x s)).toReal ≤ (volume (U ∩ ball x r)).toReal :=
          ENNReal.toReal_mono h_ne_top_r1 (measure_mono h_ball_mono1)
        have h42 : (volume ((ball x s) \ U)).toReal ≤ (volume ((ball x r) \ U)).toReal :=
          ENNReal.toReal_mono h_ne_top_r2 (measure_mono h_ball_mono2)
        have h5 : c' * r ^ n ≤ c_vol * s ^ n := by
          dsimp only [c']
          have h7 : c_vol * s ^ n * r ^ n ≤ c_vol * s ^ n := by
            have h8 : 0 ≤ c_vol * s ^ n := by positivity
            nlinarith
          exact h7
        exact ⟨by linarith, by linarith⟩
    exact blowUp_density_half_of_data hU.measurableSet x (ν x) hν_unit hn
      h_vol_bound h_trans_bound h_dir_vanish_field h_nontrivial' h_orientation_field

  exact ⟨hν_unit,
    { h_vol_bound := h_vol_bound
      h_trans_bound := h_trans_bound
      h_directional_vanishing := h_dir_vanish_field
      density := h_density_field
      h_orientation := h_orientation_field }⟩

end Geometry.StructureTheorem
