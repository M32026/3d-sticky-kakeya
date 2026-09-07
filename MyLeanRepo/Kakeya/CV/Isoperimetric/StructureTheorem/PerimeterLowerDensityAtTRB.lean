import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterDefinition
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.CutoffFunctions
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpScaling
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpLemma
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpAtTRB
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DensityEstimates
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterLowerDensity
import Mathlib.Tactic

/-!
# Phase B: Lower Perimeter Density at True Reduced Boundary Points

## Main results

1. `blowup_limit_alpha_zero`: half-space threshold α must be 0 (from two-sided density).
2. `blowup_full_halfspace_at_trb`: full blow-up convergence to `halfSpace ν`.

## References

- Maggi, *Sets of Finite Perimeter*, Theorem 15.5
-/


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

open Perimeter

variable {n : ℕ}

/-- If F is a.e. a half-space `{inner(y,ν) < α}` and has two-sided positive volume
density at 0, then α = 0. -/
lemma blowup_limit_alpha_zero
    {F : Set (E n)} (hF : MeasurableSet F) {ν : E n} (hν_unit : ‖ν‖ = 1)
    {α : ℝ} (hF_half : F =ᵐ[volume] {y | inner ℝ y ν < α})
    (h_two_sided : ∃ (c : ℝ), 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ →
      volume (F ∩ ball (0 : E n) ρ) ≥ ENNReal.ofReal (c * ρ ^ n) ∧
      volume ((ball (0 : E n) ρ) \ F) ≥ ENNReal.ofReal (c * ρ ^ n)) :
    α = 0 := by
  rcases h_two_sided with ⟨c, hc_pos, h_vol⟩
  by_cases h_pos : 0 < α
  · -- α > 0
    set ρ : ℝ := α / 2 with hρ_def
    have hρ_pos : 0 < ρ := by linarith
    have h1 : (ball (0 : E n) ρ) ⊆ {y : E n | inner ℝ y ν < α} := by
      intro y hy
      have h2 : ‖y‖ < ρ := by simpa [ball, dist_zero_right] using hy
      have h3 : inner ℝ y ν ≤ ‖y‖ * ‖ν‖ := by exact real_inner_le_norm y ν
      rw [hν_unit] at h3
      have h4 : inner ℝ y ν < α := by linarith
      exact h4
    have h4 : Set.diff (ball (0 : E n) ρ) F =ᵐ[volume] (∅ : Set (E n)) := by
      filter_upwards [hF_half] with z hz
      exact propext ⟨fun h5 => h5.2 (hz.mpr (h1 h5.1)), False.elim⟩
    have h5 : volume (Set.diff (ball (0 : E n) ρ) F) = 0 := by
      have h6 := measure_congr h4
      exact h6.trans measure_empty
    have h7 : 0 < c * ρ ^ n := by positivity
    have h8 : volume ((ball (0 : E n) ρ) \ F) ≥ ENNReal.ofReal (c * ρ ^ n) := (h_vol ρ hρ_pos).2
    have h9 : (ball (0 : E n) ρ) \ F = Set.diff (ball (0 : E n) ρ) F := by rfl
    rw [h9] at h8
    rw [h5] at h8
    have h10 : 0 < ENNReal.ofReal (c * ρ ^ n) := ENNReal.ofReal_pos.mpr h7
    exact False.elim (not_le.mpr h10 h8)
  · by_cases h_neg : α < 0
    · -- α < 0
      set ρ : ℝ := (-α) / 2 with hρ_def
      have hρ_pos : 0 < ρ := by linarith
      have hρ_lt : ρ < -α := by linarith [h_neg]
      have h1 : (ball (0 : E n) ρ) ⊆ {y : E n | inner ℝ y ν ≥ α} := by
        intro y hy
        have h2 : ‖y‖ < ρ := by simpa [ball, dist_zero_right] using hy
        have h3 : inner ℝ (-y) ν ≤ ‖(-y)‖ * ‖ν‖ := by exact real_inner_le_norm (-y) ν
        have h4 : inner ℝ (-y) ν = -inner ℝ y ν := by simp [inner_neg_left]
        have h5 : ‖(-y)‖ = ‖y‖ := by simp
        rw [h4, h5] at h3
        rw [hν_unit] at h3
        have h6 : -inner ℝ y ν ≤ ‖y‖ := by simpa using h3
        have h7 : -inner ℝ y ν < -α := by
          calc -inner ℝ y ν ≤ ‖y‖ := h6
            _ < ρ := h2
            _ < -α := hρ_lt
        have h8 : inner ℝ y ν > α := by linarith
        exact le_of_lt h8
      have h4 : Set.inter F (ball (0 : E n) ρ) =ᵐ[volume] (∅ : Set (E n)) := by
        filter_upwards [hF_half] with z hz
        exact propext ⟨fun h5 =>
          have h6 : z ∈ {y : E n | inner ℝ y ν ≥ α} := h1 h5.2
          have h7 : z ∉ {y : E n | inner ℝ y ν < α} := by simpa using h6
          h7 (hz.mp h5.1), False.elim⟩
      have h5 : volume (Set.inter F (ball (0 : E n) ρ)) = 0 := by
        have h6 := measure_congr h4
        exact h6.trans measure_empty
      have h7 : 0 < c * ρ ^ n := by positivity
      have h8 : volume (F ∩ ball (0 : E n) ρ) ≥ ENNReal.ofReal (c * ρ ^ n) := (h_vol ρ hρ_pos).1
      have h9 : F ∩ ball (0 : E n) ρ = Set.inter F (ball (0 : E n) ρ) := by rfl
      rw [h9] at h8
      rw [h5] at h8
      have h10 : 0 < ENNReal.ofReal (c * ρ ^ n) := ENNReal.ofReal_pos.mpr h7
      exact False.elim (not_le.mpr h10 h8)
    · linarith

/-- ENNReal scaling arithmetic helper:
`r^{-n} * ENNReal.ofReal(c * (r*ρ)^n) = ENNReal.ofReal(c * ρ^n)`. -/
lemma scaling_ennreal_arithmetic {r c ρ : ℝ} (hr_pos : 0 < r) (hc_pos : 0 < c)
    (hρ_pos : 0 < ρ) (n : ℕ) :
    ENNReal.ofReal (r ^ n)⁻¹ * ENNReal.ofReal (c * (r * ρ) ^ n) =
    ENNReal.ofReal (c * ρ ^ n) := by
  have h1 : 0 < r ^ n := pow_pos hr_pos n
  have h2 : 0 ≤ (r ^ n)⁻¹ := by positivity
  have h3 : 0 ≤ c * (r * ρ) ^ n := by positivity
  rw [← ENNReal.ofReal_mul h2]
  congr 1
  have h4 : (r * ρ) ^ n = r ^ n * ρ ^ n := by ring
  rw [h4]
  field_simp [h1.ne'] <;> ring

/-- Helper: transfer two-sided volume density from U to a blow-up limit F.
Returns a possibly smaller constant `c'` (specifically `c / 2^n`) because we
use `closedBall` for compact convergence and transfer to `ball`. -/
lemma transfer_two_sided_density
    {U : Set (E n)} (hU : IsOpen U) {x ν : E n} {F : Set (E n)}
    {r_seq : ℕ → ℝ} {subseq : ℕ → ℕ}
    (hr_pos : ∀ k, 0 < r_seq k) (hsub_strict : StrictMono subseq)
    (hr_tendsto : Tendsto r_seq atTop (nhds 0))
    (h_conv : ∀ (K : Set (E n)), IsCompact K →
      Tendsto (fun k => volume (symmDiff (blowUp U x (r_seq (subseq k))) F ∩ K)) atTop (nhds 0))
    (h_nontrivial : ∃ (c : ℝ) (R : ℝ), 0 < c ∧ 0 < R ∧
      ∀ r, 0 < r → r < R →
        volume (U ∩ ball x r) ≥ ENNReal.ofReal (c * r ^ n) ∧
        volume ((ball x r) \ U) ≥ ENNReal.ofReal (c * r ^ n)) :
    ∃ (c : ℝ), 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ →
      volume (F ∩ ball (0 : E n) ρ) ≥ ENNReal.ofReal (c * ρ ^ n) ∧
      volume ((ball (0 : E n) ρ) \ F) ≥ ENNReal.ofReal (c * ρ ^ n) := by
  rcases h_nontrivial with ⟨c, R_vol, hc_pos, hR_vol_pos, h_vol_two_sided⟩
  let r' := fun k => r_seq (subseq k)
  have hr'_pos : ∀ k, 0 < r' k := fun k => hr_pos (subseq k)
  have hr'_tendsto : Tendsto r' atTop (nhds 0) :=
    hr_tendsto.comp hsub_strict.tendsto_atTop
  let c' : ℝ := c / (2 ^ n)
  have hc'_pos : 0 < c' := by positivity
  refine ⟨c', hc'_pos, fun ρ hρ => ?_⟩
  set ρ' : ℝ := ρ / 2 with hρ'_def
  have hρ'_pos : 0 < ρ' := by linarith
  have hK_compact : IsCompact (closedBall (0 : E n) ρ') := isCompact_closedBall _ _
  have h_conv_int := tendsto_volume_inter_of_symmDiff (K := closedBall (0 : E n) ρ') hK_compact
    (h_conv (closedBall (0 : E n) ρ') hK_compact)
  have h_conv_compl := tendsto_volume_compl_of_symmDiff (K := closedBall (0 : E n) ρ') hK_compact
    (h_conv (closedBall (0 : E n) ρ') hK_compact)
  have h_eventually : ∀ᶠ k in atTop, r' k * ρ' < R_vol := by
    have h : Tendsto (fun k => r' k * ρ') atTop (nhds (0 * ρ')) :=
      hr'_tendsto.mul tendsto_const_nhds
    have h0 : (0 * ρ' : ℝ) = 0 := by ring
    rw [h0] at h
    exact h (Iio_mem_nhds hR_vol_pos)
  have h_lower_int : ∀ᶠ k in atTop, volume (blowUp U x (r' k) ∩ closedBall (0 : E n) ρ') ≥
      ENNReal.ofReal (c * ρ' ^ n) := by
    filter_upwards [h_eventually] with k hk
    have h1 : volume (U ∩ ball x (r' k * ρ')) ≥ ENNReal.ofReal (c * (r' k * ρ') ^ n) :=
      (h_vol_two_sided (r' k * ρ') (mul_pos (hr'_pos k) hρ'_pos) hk).1
    have h2 : volume (blowUp U x (r' k) ∩ ball (0 : E n) ρ') =
        ENNReal.ofReal ((r' k) ^ n)⁻¹ * volume (U ∩ ball x (r' k * ρ')) :=
      blow_up_volume (S := U) (x := x) (r := r' k) (R := ρ') hU.measurableSet (hr'_pos k) (by linarith)
    have h3 : volume (blowUp U x (r' k) ∩ closedBall (0 : E n) ρ') ≥
        ENNReal.ofReal ((r' k) ^ n)⁻¹ * volume (U ∩ ball x (r' k * ρ')) := by
      have h31 : volume (blowUp U x (r' k) ∩ closedBall (0 : E n) ρ') ≥
          volume (blowUp U x (r' k) ∩ ball (0 : E n) ρ') :=
        measure_mono (by intro z hz; exact ⟨hz.1, ball_subset_closedBall hz.2⟩)
      rw [h2] at h31
      exact h31
    have h4 : ENNReal.ofReal ((r' k) ^ n)⁻¹ * ENNReal.ofReal (c * (r' k * ρ') ^ n) =
        ENNReal.ofReal (c * ρ' ^ n) :=
      scaling_ennreal_arithmetic (hr'_pos k) hc_pos hρ'_pos n
    have h5 : ENNReal.ofReal ((r' k) ^ n)⁻¹ * volume (U ∩ ball x (r' k * ρ')) ≥
        ENNReal.ofReal (c * ρ' ^ n) := by
      have h51 : ENNReal.ofReal ((r' k) ^ n)⁻¹ * volume (U ∩ ball x (r' k * ρ')) ≥
          ENNReal.ofReal ((r' k) ^ n)⁻¹ * ENNReal.ofReal (c * (r' k * ρ') ^ n) :=
        mul_le_mul_left' h1 _
      rw [h4] at h51
      exact h51
    exact le_trans h5 h3
  have h_lower_compl : ∀ᶠ k in atTop, volume ((closedBall (0 : E n) ρ') \ blowUp U x (r' k)) ≥
      ENNReal.ofReal (c * ρ' ^ n) := by
    filter_upwards [h_eventually] with k hk
    have h1 : volume ((ball x (r' k * ρ')) \ U) ≥ ENNReal.ofReal (c * (r' k * ρ') ^ n) :=
      (h_vol_two_sided (r' k * ρ') (mul_pos (hr'_pos k) hρ'_pos) hk).2
    have hr_ne : (r' k) ≠ 0 := (hr'_pos k).ne'
    have hU_compl : MeasurableSet Uᶜ := hU.measurableSet.compl
    have hbc : blowUp Uᶜ x (r' k) = (blowUp U x (r' k))ᶜ := blowUp_compl hr_ne
    have h_eq1 : Set.inter (blowUp Uᶜ x (r' k)) (ball (0 : E n) ρ') =
        (ball (0 : E n) ρ') \ blowUp U x (r' k) := by
      rw [hbc]; ext y; simp [Set.inter] <;> tauto
    have h_eq2 : Uᶜ ∩ ball x (r' k * ρ') = (ball x (r' k * ρ')) \ U := by
      ext y; simp [Set.mem_compl_iff] <;> tauto
    have h_tmp := blow_up_volume (S := Uᶜ) (x := x) (r := r' k) (R := ρ') hU_compl (hr'_pos k) (by linarith)
    have h_vol1 : volume (blowUp Uᶜ x (r' k) ∩ ball (0 : E n) ρ') =
        volume ((ball (0 : E n) ρ') \ blowUp U x (r' k)) := by
      exact congr_arg volume h_eq1
    have h_vol2 : volume (Uᶜ ∩ ball x (r' k * ρ')) =
        volume ((ball x (r' k * ρ')) \ U) := by
      exact congr_arg volume h_eq2
    have h2 : volume ((ball (0 : E n) ρ') \ blowUp U x (r' k)) =
        ENNReal.ofReal ((r' k) ^ n)⁻¹ * volume ((ball x (r' k * ρ')) \ U) := by
      rw [← h_vol1, h_tmp, h_vol2]
    have h3 : volume ((closedBall (0 : E n) ρ') \ blowUp U x (r' k)) ≥
        ENNReal.ofReal ((r' k) ^ n)⁻¹ * volume ((ball x (r' k * ρ')) \ U) := by
      have h31 : volume ((closedBall (0 : E n) ρ') \ blowUp U x (r' k)) ≥
          volume ((ball (0 : E n) ρ') \ blowUp U x (r' k)) :=
        measure_mono (by intro z hz; exact ⟨ball_subset_closedBall hz.1, hz.2⟩)
      rw [h2] at h31
      exact h31
    have h4 : ENNReal.ofReal ((r' k) ^ n)⁻¹ * ENNReal.ofReal (c * (r' k * ρ') ^ n) =
        ENNReal.ofReal (c * ρ' ^ n) :=
      scaling_ennreal_arithmetic (hr'_pos k) hc_pos hρ'_pos n
    have h5 : ENNReal.ofReal ((r' k) ^ n)⁻¹ * volume ((ball x (r' k * ρ')) \ U) ≥
        ENNReal.ofReal (c * ρ' ^ n) := by
      have h51 : ENNReal.ofReal ((r' k) ^ n)⁻¹ * volume ((ball x (r' k * ρ')) \ U) ≥
          ENNReal.ofReal ((r' k) ^ n)⁻¹ * ENNReal.ofReal (c * (r' k * ρ') ^ n) :=
        mul_le_mul_left' h1 _
      rw [h4] at h51
      exact h51
    exact le_trans h5 h3
  have h_limit_int : volume (F ∩ closedBall (0 : E n) ρ') ≥ ENNReal.ofReal (c * ρ' ^ n) :=
    ge_of_tendsto h_conv_int h_lower_int
  have h_limit_compl : volume ((closedBall (0 : E n) ρ') \ F) ≥ ENNReal.ofReal (c * ρ' ^ n) :=
    ge_of_tendsto h_conv_compl h_lower_compl
  have h_subset : closedBall (0 : E n) ρ' ⊆ ball (0 : E n) ρ := by
    intro y hy
    have h2 : ‖y‖ ≤ ρ' := mem_closedBall_zero_iff.mp hy
    have h3 : ‖y‖ < ρ := by linarith
    exact mem_ball_zero_iff.mpr h3
  have h5 : volume (F ∩ ball (0 : E n) ρ) ≥ volume (F ∩ closedBall (0 : E n) ρ') :=
    measure_mono (inter_subset_inter_right _ h_subset)
  have h6 : volume ((ball (0 : E n) ρ) \ F) ≥ volume ((closedBall (0 : E n) ρ') \ F) :=
    measure_mono (diff_subset_diff h_subset Subset.rfl)
  have h7 : c * ρ' ^ n = c' * ρ ^ n := by
    simp only [c', hρ'_def]
    have h8 : (ρ / 2) ^ n = ρ ^ n / (2 ^ n) := by
      rw [div_pow]
      <;> norm_num
    rw [h8]
    <;> ring
  have h11 : ENNReal.ofReal (c * ρ' ^ n) = ENNReal.ofReal (c' * ρ ^ n) := by rw [h7]
  constructor
  · have h_final1 : ENNReal.ofReal (c' * ρ ^ n) ≤ volume (F ∩ closedBall (0 : E n) ρ') := by
      rw [← h11]
      exact h_limit_int
    exact le_trans h_final1 h5
  · have h_final2 : ENNReal.ofReal (c' * ρ ^ n) ≤ volume ((closedBall (0 : E n) ρ') \ F) := by
      rw [← h11]
      exact h_limit_compl
    exact le_trans h_final2 h6

/-- If `F =ᵐ G`, then `volume(symmDiff A F ∩ K) = volume(symmDiff A G ∩ K)`. -/
lemma volume_symmDiff_of_ae_eq {A F G K : Set (E n)} (hFG : F =ᵐ[volume] G) :
    volume (Set.inter (symmDiff A F) K) = volume (Set.inter (symmDiff A G) K) := by
  have h : Set.inter (symmDiff A F) K =ᵐ[volume] Set.inter (symmDiff A G) K := by
    filter_upwards [hFG] with z hz
    have h6 : z ∈ F ↔ z ∈ G := Iff.of_eq hz
    have h6' : z ∉ F ↔ z ∉ G := h6.not
    have h_def1 : z ∈ symmDiff A F ↔ (z ∈ A ∧ z ∉ F) ∨ (z ∈ F ∧ z ∉ A) := Set.mem_symmDiff
    have h_def2 : z ∈ symmDiff A G ↔ (z ∈ A ∧ z ∉ G) ∨ (z ∈ G ∧ z ∉ A) := Set.mem_symmDiff
    have h7 : z ∈ symmDiff A F ↔ z ∈ symmDiff A G := by
      rw [h_def1, h_def2, h6]
      <;> rfl
    exact propext ⟨fun h8 => ⟨h7.mp h8.1, h8.2⟩, fun h8 => ⟨h7.mpr h8.1, h8.2⟩⟩
  exact measure_congr h

/-- **Full blow-up convergence to `halfSpace ν` at a TRB point**.

From subsequential convergence plus two-sided density (which forces α = 0),
every sequence of blow-ups converges in L¹_loc to `halfSpace ν`. -/
theorem blowup_full_halfspace_at_trb
    {U : Set (E n)} (hU : IsOpen U) (hU_reg : U = interior (closure U))
    (hBdd : Bornology.IsBounded U) (h_perim_finite : perimeter U < ⊤) (hn : 2 ≤ n)
    (x : E n) (ν : E n) (hx_trb : x ∈ trueReducedBoundary U)
    (hν : measureTheoreticNormal U x = ν)
    (hν_unit : ‖ν‖ = 1)
    (h_upper : ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterMeasure U (closedBall x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)))
    (h_abs_lebesgue : ∀ (w : E n), inner ℝ w ν = 0 →
        Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, |inner ℝ w (measureTheoreticNormal U y)| ∂(perimeterMeasure U)) /
            (perimeterMeasure U (closedBall x r)).toReal)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (h_inner_lebesgue : Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, inner ℝ ν (measureTheoreticNormal U y) ∂(perimeterMeasure U)) /
          (perimeterMeasure U (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1))
    (h_nontrivial : ∃ (c : ℝ) (R : ℝ), 0 < c ∧ 0 < R ∧
        ∀ r, 0 < r → r < R →
          volume (U ∩ ball x r) ≥ ENNReal.ofReal (c * r ^ n) ∧
          volume ((ball x r) \ U) ≥ ENNReal.ofReal (c * r ^ n))
    (r_seq : ℕ → ℝ) (hr_pos : ∀ k, 0 < r_seq k)
    (hr_tendsto : Tendsto r_seq atTop (nhds 0))
    (K : Set (E n)) (hK : IsCompact K) :
    Tendsto (fun k => volume (symmDiff (blowUp U x (r_seq k)) (halfSpace ν) ∩ K))
      atTop (nhds 0) := by
  by_contra h_not
  let f : ℕ → ENNReal := fun k => volume (symmDiff (blowUp U x (r_seq k)) (halfSpace ν) ∩ K)
  have h_basis := ENNReal.nhds_zero_basis
  have h_exists : ∃ (a : ENNReal), 0 < a ∧ ∃ᶠ k in atTop, a ≤ f k := by
    have h1 : ¬ Tendsto f atTop (nhds 0) := h_not
    have h2 : ¬ (∀ (a : ENNReal), 0 < a → ∀ᶠ k in atTop, f k < a) := by
      rw [h_basis.tendsto_right_iff] at h1
      exact h1
    push Not at h2
    rcases h2 with ⟨a, ha_pos, h3⟩
    have h4 : ∃ᶠ k in atTop, a ≤ f k := by
      simpa [not_lt] using h3
    exact ⟨a, ha_pos, h4⟩
  rcases h_exists with ⟨a, ha_pos, h_freq⟩
  let p : ℝ → Prop := fun r => a ≤ volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ K)
  have h_freq' : ∃ᶠ k in atTop, p (r_seq k) := h_freq
  rcases Filter.subseq_forall_of_frequently hr_tendsto h_freq' with ⟨ns, hns_tendsto, hns_prop⟩
  let r' := r_seq ∘ ns
  have hr'_pos : ∀ k, 0 < r' k := fun k => hr_pos (ns k)
  have hr'_tendsto : Tendsto r' atTop (nhds 0) := hns_tendsto
  rcases blowup_subsequential_halfspace_at_trb hU hU_reg hBdd h_perim_finite hn x ν hx_trb hν hν_unit h_upper h_abs_lebesgue h_inner_lebesgue h_nontrivial r' hr'_pos hr'_tendsto
    with ⟨F, subseq, α, hsub_strict, hF_meas, h_conv, hF_half⟩
  have h_two_sided_F := transfer_two_sided_density (x := x) (ν := ν) hU hr'_pos hsub_strict hr'_tendsto h_conv h_nontrivial
  have hα_zero : α = 0 := blowup_limit_alpha_zero hF_meas hν_unit hF_half h_two_sided_F
  have hF_half0 : F =ᵐ[volume] halfSpace ν := by
    rw [hα_zero] at hF_half
    exact hF_half
  let r'' := r' ∘ subseq
  have h_conv_K : Tendsto (fun k => volume (symmDiff (blowUp U x (r'' k)) F ∩ K)) atTop (nhds 0) :=
    h_conv K hK
  have h_eq : ∀ k, volume (symmDiff (blowUp U x (r'' k)) F ∩ K) =
      volume (symmDiff (blowUp U x (r'' k)) (halfSpace ν) ∩ K) := by
    intro k
    exact volume_symmDiff_of_ae_eq hF_half0
  have h_conv_K2 : Tendsto (fun k => volume (symmDiff (blowUp U x (r'' k)) (halfSpace ν) ∩ K))
      atTop (nhds 0) := by
    convert h_conv_K using 1
    funext k
    exact (h_eq k).symm
  have h_lower : ∀ k, a ≤ volume (symmDiff (blowUp U x (r'' k)) (halfSpace ν) ∩ K) := by
    intro k
    exact hns_prop (subseq k)
  have h1 : ∀ᶠ k in atTop, volume (symmDiff (blowUp U x (r'' k)) (halfSpace ν) ∩ K) < a :=
    h_conv_K2 (Iio_mem_nhds ha_pos)
  rcases h1.exists with ⟨k, hk⟩
  have h4 : a ≤ volume (symmDiff (blowUp U x (r'' k)) (halfSpace ν) ∩ K) := h_lower k
  exact not_le.mpr hk h4

/-- Convert sequential blow-up convergence to `nhdsWithin` convergence on balls. -/
lemma blowup_convergence_seq_to_nhdsWithin
    {U : Set (E n)} {x ν : E n}
    (h_seq : ∀ (r_seq : ℕ → ℝ), (∀ k, 0 < r_seq k) → Tendsto r_seq atTop (nhds 0) →
      ∀ (K : Set (E n)), IsCompact K →
        Tendsto (fun k => volume (symmDiff (blowUp U x (r_seq k)) (halfSpace ν) ∩ K))
          atTop (nhds 0))
    (R : ℝ) (hR : 0 < R) :
    Tendsto (fun r : ℝ => volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) R))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [Filter.tendsto_iff_seq_tendsto]
  intro r_seq hr_seq
  have h1 : Tendsto r_seq atTop (nhds 0) := (tendsto_nhdsWithin_iff.mp hr_seq).1
  have h2 : ∀ᶠ k in atTop, 0 < r_seq k := (tendsto_nhdsWithin_iff.mp hr_seq).2
  rcases eventually_atTop.mp h2 with ⟨N, hN⟩
  let r' : ℕ → ℝ := fun k => r_seq (k + N)
  have hr'_pos : ∀ k, 0 < r' k := fun k => hN (k + N) (by linarith)
  have hr'_tendsto : Tendsto r' atTop (nhds 0) := h1.comp (tendsto_add_atTop_nat N)
  have hK : IsCompact (closedBall (0 : E n) R) := isCompact_closedBall _ _
  have h3 := h_seq r' hr'_pos hr'_tendsto (closedBall (0 : E n) R) hK
  have h4 : ∀ k, volume (symmDiff (blowUp U x (r' k)) (halfSpace ν) ∩ ball (0 : E n) R) ≤
      volume (symmDiff (blowUp U x (r' k)) (halfSpace ν) ∩ closedBall (0 : E n) R) := by
    intro k
    apply measure_mono
    apply inter_subset_inter_right _
    exact ball_subset_closedBall
  have h_zero : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (nhds 0) := tendsto_const_nhds
  have h5 : Tendsto (fun k => volume (symmDiff (blowUp U x (r' k)) (halfSpace ν) ∩ ball (0 : E n) R))
      atTop (nhds 0) := by
    have h_ev1 : ∀ᶠ k in atTop, (0 : ENNReal) ≤ volume (symmDiff (blowUp U x (r' k)) (halfSpace ν) ∩ ball (0 : E n) R) := by
      filter_upwards with _ <;> positivity
    have h_ev2 : ∀ᶠ k in atTop, volume (symmDiff (blowUp U x (r' k)) (halfSpace ν) ∩ ball (0 : E n) R) ≤
        volume (symmDiff (blowUp U x (r' k)) (halfSpace ν) ∩ closedBall (0 : E n) R) := by
      filter_upwards with k; exact h4 k
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h3 h_ev1 h_ev2
  let g : ℕ → ENNReal := fun k => volume (symmDiff (blowUp U x (r_seq k)) (halfSpace ν) ∩ ball (0 : E n) R)
  let g' : ℕ → ENNReal := fun k => volume (symmDiff (blowUp U x (r' k)) (halfSpace ν) ∩ ball (0 : E n) R)
  have h_sub_tendsto : Tendsto (fun k : ℕ => k - N) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun m => ⟨m + N, fun k hk => by omega⟩)
  have h7 : Tendsto (fun k : ℕ => g' (k - N)) atTop (nhds 0) := h5.comp h_sub_tendsto
  have h8 : ∀ᶠ k in atTop, (fun k : ℕ => g' (k - N)) k = g k := by
    filter_upwards [eventually_ge_atTop N] with k hk
    have h9 : k = (k - N) + N := by omega
    have h10 : r_seq k = r' (k - N) := by
      have h11 : (k - N) + N = k := by omega
      have h12 : r' (k - N) = r_seq ((k - N) + N) := by rfl
      rw [h12, h11]
    dsimp only [g, g']
    rw [h10]
  exact h7.congr' h8

/-- **Lower perimeter density at a TRB point** (from blow-up convergence).

Given full blow-up convergence to `halfSpace ν`, the Gauss-Green cutoff
argument gives `P(U; B(x,r)) ≥ c · r^(n-1)` for small `r`. -/
theorem perimeter_lower_density_from_convergence
    {U : Set (E n)} (hU : IsOpen U) (hU_reg : U = interior (closure U))
    (hBdd : Bornology.IsBounded U) (hn : 2 ≤ n)
    {x : E n} {ν : E n} (hν_unit : ‖ν‖ = 1)
    (h_blowup : ∀ (R : ℝ), 0 < R →
      Tendsto (fun r : ℝ => volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) R))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∃ (c : ℝ) (r0 : ℝ), 0 < c ∧ 0 < r0 ∧
      ∀ r, 0 < r → r < r0 →
        ENNReal.ofReal (c * r ^ (n - 1)) ≤ perimeterIn U (ball x r) := by
  set a : ℝ := 1 / 2 with ha_def
  set L : ℝ := 1 / 2 with hL_def
  set φ : E n → ℝ := radialCutoff (0 : E n) a L with hφ_def
  set f : E n → ℝ := fun z => fderiv ℝ φ z ν with hf_def
  have ha_pos : 0 < a := by norm_num
  have hL_pos : 0 < L := by norm_num
  have hU_meas : MeasurableSet U := hU.measurableSet
  have h_I_H_pos : 0 < ∫ z in halfSpace ν, f z :=
    halfspace_derivative_integral_pos hν_unit hn
  set I_H : ℝ := ∫ z in halfSpace ν, f z with hI_H_def
  have hI_H_pos : 0 < I_H := h_I_H_pos
  have h_f_cont : Continuous f := by
    have h2 : Continuous (fun z : E n => (fderiv ℝ φ z) ν) := by
      have h3 : Continuous (fun p : (E n) × (E n) => (fderiv ℝ φ p.1) p.2) :=
        (radialCutoff_contDiff ha_pos hL_pos).continuous_fderiv_apply (by simp)
      have h4 : Continuous (fun z : E n => (z, ν)) := by fun_prop
      exact h3.comp h4
    simpa [hf_def] using h2
  have h_f_support : Function.support f ⊆ closedBall (0 : E n) 1 := by
    intro z hz
    have h1 : f z ≠ 0 := by simpa [hf_def, Function.mem_support] using hz
    by_contra h2
    have h3 : z ∉ closedBall (0 : E n) 1 := h2
    have h4 : ‖z‖ > 1 := by simpa [closedBall, dist_zero_right] using h3
    have h5 : ∀ᶠ w in nhds z, ‖w‖ > 1 := by
      have h6 : Continuous (fun w : E n => ‖w‖) := by fun_prop
      exact h6.continuousAt.eventually (lt_mem_nhds h4)
    have h7 : ∀ᶠ w in nhds z, φ w = 0 := by
      filter_upwards [h5] with w hw
      have h81 : 1 ≤ ‖w‖ := le_of_lt hw
      have h82 : w ∉ ball (0 : E n) (a + L) := by
        have h9 : a + L = 1 := by simp [ha_def, hL_def] <;> norm_num
        rw [h9]
        simpa [ball, dist_zero_right] using h81
      exact radialCutoff_zero_of_not_mem_ball ha_pos hL_pos h82
    have h8 : HasFDerivAt φ (0 : E n →L[ℝ] ℝ) z := by
      have h_const : HasFDerivAt (fun _ : E n => (0 : ℝ)) (0 : E n →L[ℝ] ℝ) z :=
        hasFDerivAt_const (x := z) (c := (0 : ℝ))
      have h7' : φ =ᶠ[nhds z] (fun _ : E n => (0 : ℝ)) := by
        filter_upwards [h7] with w hw; exact hw
      exact h_const.congr_of_eventuallyEq h7'
    have h9 : fderiv ℝ φ z = 0 := h8.fderiv
    have h10 : f z = 0 := by
      simp only [hf_def, h9, zero_apply]
    contradiction
  have h_f_compact : HasCompactSupport f := by
    have h1 : tsupport f ⊆ closedBall (0 : E n) 1 := by
      calc tsupport f = closure (Function.support f) := by rfl
        _ ⊆ closure (closedBall (0 : E n) 1) := closure_mono h_f_support
        _ = closedBall (0 : E n) 1 := by simp
    exact IsCompact.of_isClosed_subset (isCompact_closedBall _ _) isClosed_closure h1
  have h_φ_support : Function.support φ ⊆ ball (0 : E n) 1 := by
    intro z hz
    have h1 : φ z ≠ 0 := by simpa [hφ_def, Function.mem_support] using hz
    by_contra h2
    have h3 : z ∉ ball (0 : E n) (a + L) := by
      have h4 : a + L = 1 := by simp [ha_def, hL_def] <;> norm_num
      rw [h4]; exact h2
    have h4 : φ z = 0 := radialCutoff_zero_of_not_mem_ball ha_pos hL_pos h3
    contradiction
  have hA_meas : ∀ r, MeasurableSet (blowUp U x r) := by
    intro r
    by_cases hr : r = 0
    · have h_simp : blowUp U x r = (fun (_ : E n) => (0 : E n)) '' U := by
        simp [blowUp, blowUpMap, hr] <;> rfl
      rw [h_simp]
      have h_img : (fun (_ : E n) => (0 : E n)) '' U = ∅ ∨ (fun (_ : E n) => (0 : E n)) '' U = {(0 : E n)} := by
        by_cases hU_empty : U = ∅
        · left; rw [hU_empty] <;> simp
        · right
          have hU_nonempty : U.Nonempty := Set.nonempty_iff_ne_empty.mpr hU_empty
          ext z; simp [hU_nonempty]
      rcases h_img with (h_img | h_img)
      · rw [h_img] <;> simp
      · rw [h_img] <;> exact measurableSet_singleton _
    · have h_blowMap_meas : MeasurableEmbedding (blowUpMap x r) :=
        blowUpMap_measurableEmbedding x hr
      exact h_blowMap_meas.measurableSet_image.mpr hU_meas
  have hH_meas : MeasurableSet (halfSpace ν) := by
    have h1 : Continuous (fun z : E n => inner ℝ z ν) := by fun_prop
    exact (isOpen_Iio.preimage h1).measurableSet
  have h_blowup2 := h_blowup 2 (by norm_num)
  have h_conv_closed : Tendsto (fun r : ℝ => volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ closedBall (0 : E n) 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h_sub : ∀ r, volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ closedBall (0 : E n) 1) ≤
        volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) 2) := by
      intro r
      apply measure_mono
      apply inter_subset_inter_right _
      exact closedBall_subset_ball (by norm_num)
    have h_zero : Tendsto (fun _ : ℝ => (0 : ENNReal)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := tendsto_const_nhds
    have h_ev1 : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), (0 : ENNReal) ≤ volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ closedBall (0 : E n) 1) := by
      filter_upwards with _ <;> positivity
    have h_ev2 : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ closedBall (0 : E n) 1) ≤
        volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) 2) := by
      filter_upwards with r <;> exact h_sub r
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_blowup2 h_ev1 h_ev2
  have h_conv_integral : Tendsto (fun r : ℝ => ∫ z in blowUp U x r, f z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds I_H) :=
    integral_convergence_of_symmDiff h_f_cont h_f_compact hA_meas hH_meas
      (isCompact_closedBall (0 : E n) 1) h_f_support h_conv_closed
  have h_eventually : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
      I_H / 2 ≤ ∫ z in blowUp U x r, f z := by
    have h_nhds : Ioo (I_H / 2) (3 * I_H / 2) ∈ nhds I_H := by
      apply Ioo_mem_nhds <;> linarith
    have h : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), (∫ z in blowUp U x r, f z) ∈ Ioo (I_H / 2) (3 * I_H / 2) :=
      h_conv_integral h_nhds
    filter_upwards [h] with r hr
    have h9 : I_H / 2 < ∫ z in blowUp U x r, f z := hr.1
    linarith
  have h_basis : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).HasBasis (fun ε => 0 < ε) (fun ε => ball (0 : ℝ) ε ∩ Set.Ioi 0) :=
    Metric.nhdsWithin_basis_ball
  rcases h_basis.eventually_iff.mp h_eventually with ⟨ε, hε_pos, hball⟩
  have hball' : ∀ (r : ℝ), r ∈ ball (0 : ℝ) ε ∩ Set.Ioi 0 → I_H / 2 ≤ ∫ z in blowUp U x r, f z := hball
  have h_r0 : ∃ r0, 0 < r0 ∧ ∀ r, 0 < r → r < r0 →
      I_H / 2 ≤ ∫ z in blowUp U x r, f z := by
    refine ⟨ε, hε_pos, fun r hr_pos hr_lt => ?_⟩
    have h1 : r ∈ ball (0 : ℝ) ε ∩ Set.Ioi 0 := by
      simp only [Set.mem_inter_iff, mem_ball, dist_zero_right, Set.mem_setOf_eq]
      exact ⟨by rw [Real.norm_eq_abs, abs_of_pos hr_pos] <;> exact hr_lt, hr_pos⟩
    exact hball' r h1
  rcases h_r0 with ⟨r0, hr0_pos, h_ineq⟩
  refine ⟨I_H / 2, r0, by linarith, hr0_pos, ?_⟩
  intro r hr_pos hr_lt
  set φ_r : E n → ℝ := fun y => φ ((1 / r) • (y - x)) with hφ_r_def
  set Φ_test : E n → E n := fun y => φ_r y • ν with hΦ_def
  have h_inner_smooth : ContDiff ℝ ∞ (fun y : E n => (1 / r) • (y - x)) := by fun_prop
  have hφ_r_smooth : ContDiff ℝ ∞ φ_r :=
    (radialCutoff_contDiff ha_pos hL_pos).comp h_inner_smooth
  have h_constν : ContDiff ℝ ∞ (fun _ : E n => ν) := contDiff_const
  have hΦ_smooth : ContDiff ℝ ∞ Φ_test := hφ_r_smooth.smul h_constν
  have hΦ_support : Function.support Φ_test ⊆ ball x r := by
    intro y hy
    have h1 : Φ_test y ≠ 0 := by simpa [Function.mem_support] using hy
    have h2 : φ_r y ≠ 0 := by
      by_contra h3
      have h4 : Φ_test y = 0 := by simp [hΦ_def, h3]
      contradiction
    have h3 : (1 / r) • (y - x) ∈ Function.support φ := by
      simpa [hφ_r_def, Function.mem_support] using h2
    have h4 : (1 / r) • (y - x) ∈ ball (0 : E n) 1 := h_φ_support h3
    have h5 : ‖(1 / r) • (y - x)‖ < 1 := by simpa [ball, dist_zero_right] using h4
    have h6 : ‖y - x‖ < r := by
      have h7 : ‖(1 / r) • (y - x)‖ = (1 / r) * ‖y - x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] <;> ring
      rw [h7] at h5
      have h8 : 0 < r := hr_pos
      calc
        ‖y - x‖ = r * ((1 / r) * ‖y - x‖) := by field_simp [h8.ne'] <;> ring
        _ < r * 1 := by gcongr
        _ = r := by ring
    simpa [ball, dist_eq_norm] using h6
  have hΦ_bound : ∀ y, ‖Φ_test y‖ ≤ 1 := by
    intro y
    have h1 : 0 ≤ φ_r y := by
      set t : ℝ := (‖(1 / r) • (y - x)‖ - a) / L with ht_def
      have h_eq : φ_r y = smoothStep t := by
        rw [hφ_r_def, hφ_def]
        simp [radialCutoff, ht_def, dist_zero_right] <;> rfl
      rw [h_eq]
      have h_s1 : smoothStep 1 = 0 := smoothStep_zero_of_one_le (by norm_num)
      by_cases h3 : t ≤ 1
      · have h4 : smoothStep t ≥ smoothStep 1 := smoothStep_antitone h3
        rw [h_s1] at h4; exact h4
      · have h5 : 1 < t := by linarith
        have h6 : smoothStep t = 0 := smoothStep_zero_of_one_le (by linarith)
        rw [h6] <;> norm_num
    have h2 : φ_r y ≤ 1 := by
      set t : ℝ := (‖(1 / r) • (y - x)‖ - a) / L with ht_def
      have h_eq : φ_r y = smoothStep t := by
        rw [hφ_r_def, hφ_def]
        simp [radialCutoff, ht_def, dist_zero_right] <;> rfl
      rw [h_eq]
      have h_s0 : smoothStep 0 = 1 := smoothStep_one_of_nonpos (by norm_num)
      by_cases h4 : 0 ≤ t
      · have h5 : smoothStep t ≤ smoothStep 0 := smoothStep_antitone h4
        rw [h_s0] at h5; exact h5
      · have h6 : t < 0 := by linarith
        have h7 : smoothStep t = 1 := smoothStep_one_of_nonpos (by linarith)
        rw [h7] <;> norm_num
    have h_norm_smul : ‖Φ_test y‖ = |φ_r y| * ‖ν‖ := by
      rw [hΦ_def]
      have h : ‖φ_r y • ν‖ = ‖φ_r y‖ * ‖ν‖ := norm_smul _ _
      rw [h]
      have h_norm : ‖φ_r y‖ = |φ_r y| := Real.norm_eq_abs (φ_r y)
      rw [h_norm]
    calc
      ‖Φ_test y‖ = |φ_r y| * ‖ν‖ := h_norm_smul
      _ = φ_r y * ‖ν‖ := by rw [abs_of_nonneg h1]
      _ = φ_r y := by rw [hν_unit] <;> ring
      _ ≤ 1 := h2
  let Φ_test_field : TestVectorField :=
    { toFun := Φ_test
      smooth := hΦ_smooth
      compact := by
        have h : Function.support Φ_test ⊆ ball x r := hΦ_support
        have h' : tsupport Φ_test ⊆ closure (ball x r) := closure_mono h
        have h'' : closure (ball x r) = closedBall x r := closure_ball x hr_pos.ne'
        rw [h''] at h'
        exact IsCompact.of_isClosed_subset (isCompact_closedBall x r) isClosed_closure h'
      bound := hΦ_bound }
  let Φ' : {Φ : TestVectorField // Function.support Φ.toFun ⊆ ball x r} :=
    ⟨Φ_test_field, hΦ_support⟩
  have h_div : divergence Φ_test = fun y => fderiv ℝ φ_r y ν :=
    divergence_smul_const hφ_r_smooth
  have h_scaling : ∫ y in U, divergence Φ_test y =
      r ^ (n - 1) * ∫ z in blowUp U x r, f z := by
    rw [h_div]
    exact scaling_derivative_integral hU_meas hn hr_pos (radialCutoff_contDiff ha_pos hL_pos)
  have h_integral_pos : 0 ≤ ∫ y in U, divergence Φ_test y := by
    rw [h_scaling]
    have h1 : I_H / 2 ≤ ∫ z in blowUp U x r, f z := h_ineq r hr_pos hr_lt
    have h1' : 0 ≤ ∫ z in blowUp U x r, f z := by linarith [hI_H_pos]
    have h2 : 0 ≤ r ^ (n - 1) := by positivity
    exact mul_nonneg h2 h1'
  have h_main : (I_H / 2) * r ^ (n - 1) ≤ ∫ y in U, divergence Φ_test y := by
    rw [h_scaling]
    have h1 : I_H / 2 ≤ ∫ z in blowUp U x r, f z := h_ineq r hr_pos hr_lt
    have h2 : 0 ≤ r ^ (n - 1) := by positivity
    nlinarith
  have h_perim : ENNReal.ofReal ((I_H / 2) * r ^ (n - 1)) ≤
      ENNReal.ofReal |∫ y in U, divergence Φ_test y| := by
    rw [abs_of_nonneg h_integral_pos]
    exact ENNReal.ofReal_le_ofReal h_main
  exact le_trans h_perim (le_iSup (fun (Ψ : {Φ : TestVectorField // Function.support Φ.toFun ⊆ ball x r}) =>
    ENNReal.ofReal |∫ y in U, divergence Ψ.val.toFun y|) Φ')

/-- **Lower perimeter density at a true reduced boundary point**.

At a TRB point with upper density, Lebesgue differentiation, and two-sided
positive volume density, there exist `c > 0` and `r0 > 0` such that for all
`0 < r < r0`:
`P(U; B(x,r)) ≥ c · r^(n-1)`.

This is the main M1 lower density bound, proved via blow-up convergence to
a half-space and the Gauss-Green cutoff argument. -/
theorem perimeter_lower_density_at_trb
    {U : Set (E n)} (hU : IsOpen U) (hU_reg : U = interior (closure U))
    (hBdd : Bornology.IsBounded U) (h_perim_finite : perimeter U < ⊤) (hn : 2 ≤ n)
    (x : E n) (ν : E n) (hx_trb : x ∈ trueReducedBoundary U)
    (hν : measureTheoreticNormal U x = ν)
    (hν_unit : ‖ν‖ = 1)
    (h_upper : ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterMeasure U (closedBall x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)))
    (h_abs_lebesgue : ∀ (w : E n), inner ℝ w ν = 0 →
        Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, |inner ℝ w (measureTheoreticNormal U y)| ∂(perimeterMeasure U)) /
            (perimeterMeasure U (closedBall x r)).toReal)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (h_inner_lebesgue : Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, inner ℝ ν (measureTheoreticNormal U y) ∂(perimeterMeasure U)) /
          (perimeterMeasure U (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1))
    (h_nontrivial : ∃ (c : ℝ) (R : ℝ), 0 < c ∧ 0 < R ∧
        ∀ r, 0 < r → r < R →
          volume (U ∩ ball x r) ≥ ENNReal.ofReal (c * r ^ n) ∧
          volume ((ball x r) \ U) ≥ ENNReal.ofReal (c * r ^ n)) :
    ∃ (c : ℝ) (r0 : ℝ), 0 < c ∧ 0 < r0 ∧
      ∀ r, 0 < r → r < r0 →
        ENNReal.ofReal (c * r ^ (n - 1)) ≤ perimeterIn U (ball x r) := by
  have h_seq := blowup_full_halfspace_at_trb hU hU_reg hBdd h_perim_finite hn x ν hx_trb hν hν_unit
    h_upper h_abs_lebesgue h_inner_lebesgue h_nontrivial
  have h_nhdsWithin : ∀ (R : ℝ), 0 < R →
      Tendsto (fun r : ℝ => volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) R))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    blowup_convergence_seq_to_nhdsWithin h_seq
  exact perimeter_lower_density_from_convergence hU hU_reg hBdd hn hν_unit h_nhdsWithin

end Geometry.StructureTheorem
