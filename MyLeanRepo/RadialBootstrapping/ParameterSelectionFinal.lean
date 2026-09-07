module

/-
  Parameter selection for radial_bootstrapping_measure_thin_tubes.

  Provides good_params_exist by explicit construction of τ, M, and per-c N, r2.
  Contains hN_ok_holds and all supporting lemmas.
-/

public import MyLeanRepo.RadialBootstrapping.HasMeasureThinTubes
public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.Constants

@[expose] public section

set_option maxHeartbeats 2000000

open MeasureTheory Metric Set
open scoped ENNReal NNReal

noncomputable section

namespace RadialBootstrapping


/-- Symmetry of mutual support distance. -/
lemma dist_symm {ν₁ ν₂ : ProbabilityMeasure Point} :
    sInf {d : ℝ | ∃ x ∈ (ν₁ : Measure Point).support,
      ∃ y ∈ (ν₂ : Measure Point).support, dist x y = d} =
    sInf {d : ℝ | ∃ y ∈ (ν₂ : Measure Point).support,
      ∃ x ∈ (ν₁ : Measure Point).support, dist y x = d} := by
  congr with d
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨y, hy, x, hx, dist_comm y x⟩
  · rintro ⟨y, hy, x, hx, rfl⟩
    exact ⟨x, hx, y, hy, dist_comm x y⟩

/-! ### Helper: geometric tail sum closed form -/

/-- The tail sum equals `2 * 2^{-τN} / (1 - 2^{-τ})`. -/
lemma geometric_sum_closed_form (τ : ℝ) (hτ : 0 < τ) (N : ℕ) :
    ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ) =
    ENNReal.ofReal (2 * (2 : ℝ) ^ (-τ * (N : ℝ)) / (1 - (2 : ℝ) ^ (-τ))) := by
  let a : ℝ := (2 : ℝ) ^ (-τ)
  have ha_pos : 0 < a := by positivity
  have ha_nonneg : 0 ≤ a := by positivity
  have ha_lt_one : a < 1 := by
    have h : (2 : ℝ) ^ (-τ) < (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    simpa using h
  have h1 : ∀ n : ℕ, ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ = a ^ (n + N) := by
    intro n
    have h_exp : (-(n + N : ℝ)) * τ = -τ * (n + N : ℝ) := by ring
    calc
      ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ
        = (2 : ℝ) ^ ((-(n + N : ℝ)) * τ) := by rw [← Real.rpow_mul (by norm_num)] <;> ring
      _ = (2 : ℝ) ^ (-τ * (n + N : ℝ)) := by rw [h_exp]
      _ = ((2 : ℝ) ^ (-τ)) ^ (n + N : ℝ) := by rw [← Real.rpow_mul (by norm_num)] <;> ring
      _ = a ^ (n + N) := by simp [a] <;> norm_cast
  have h2 : ∀ n : ℕ, (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ) = 2 * a ^ N * a ^ n := by
    intro n
    rw [h1 n]
    have h3 : a ^ (n + N) = a ^ N * a ^ n := by rw [pow_add] <;> ring
    rw [h3] <;> ring
  have h_summable : Summable (fun n : ℕ => (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ)) := by
    simp_rw [h2]
    exact (summable_geometric_of_lt_one ha_nonneg ha_lt_one).mul_left _
  have h_nonneg : ∀ n : ℕ, 0 ≤ (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ) := by intro n; positivity
  have h3 : ∑' n : ℕ, (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ) = 2 * a ^ N * (1 / (1 - a)) := by
    simp_rw [h2]
    rw [tsum_mul_left, tsum_geometric_of_lt_one ha_nonneg ha_lt_one] <;> ring
  have h4 : ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ) =
      ENNReal.ofReal (∑' n : ℕ, (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ)) := by
    exact (ENNReal.ofReal_tsum_of_nonneg h_nonneg h_summable).symm
  have ha_eq : a = (2 : ℝ) ^ (-τ) := by rfl
  have h5 : a ^ N = (2 : ℝ) ^ (-τ * (N : ℝ)) := by
    have ha_eq2 : a = (2 : ℝ) ^ (-τ) := by rfl
    rw [ha_eq2]
    have h71 : ((2 : ℝ) ^ (-τ)) ^ N = ((2 : ℝ) ^ (-τ)) ^ (N : ℝ) := by norm_cast
    rw [h71]
    have h72 : ((2 : ℝ) ^ (-τ)) ^ (N : ℝ) = (2 : ℝ) ^ ((-τ) * (N : ℝ)) := by
      rw [Real.rpow_mul (by norm_num)] <;> ring
    exact h72
  have h6 : 1 - a = 1 - (2 : ℝ) ^ (-τ) := by rw [ha_eq]
  rw [h4, h3, h5, h6] <;> ring_nf

/-! ### Helper lemmas for good_params_exist -/

/-- Key bound: if N > log(2/(c*b))/(τ*log2) and c < 1/10, b < 1,
    then N*τ > log₂20. -/
lemma Nτ_lower_bound (N : ℕ) (T τ c b : ℝ) (hτ : 0 < τ) (hc_pos : 0 < c) (hc_lt : c < 1 / 10)
    (hb_pos : 0 < b) (hb_lt_one : b < 1)
    (hN_gt_T : (N : ℝ) > T) (hT_eq : T * τ * Real.log 2 = Real.log (2 / (c * b))) :
    (N : ℝ) * τ > Real.log 20 / Real.log 2 := by
  have h1 : 0 < c * b := mul_pos hc_pos hb_pos
  have h2 : c * b < 1 / 10 := by nlinarith
  have h3 : (2 : ℝ) / (c * b) > 20 := by
    have h4 : (2 : ℝ) / (c * b) > 2 / (1 / 10 : ℝ) := by gcongr
    have h5 : (2 : ℝ) / (1 / 10 : ℝ) = 20 := by norm_num
    linarith
  have h4 : Real.log (2 / (c * b)) > Real.log 20 := Real.log_lt_log (by positivity) h3
  have h5 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h6 : T * τ < (N : ℝ) * τ := mul_lt_mul_of_pos_right hN_gt_T hτ
  have h7 : T * τ * Real.log 2 < (N : ℝ) * τ * Real.log 2 :=
    mul_lt_mul_of_pos_right h6 h5
  have h8 : (N : ℝ) * τ * Real.log 2 > Real.log 20 := by
    calc (N : ℝ) * τ * Real.log 2
      > T * τ * Real.log 2 := h7
    _ = Real.log (2 / (c * b)) := hT_eq
    _ > Real.log 20 := h4
  have h9 : (N : ℝ) * τ > Real.log 20 / Real.log 2 := by
    calc (N : ℝ) * τ
      = ((N : ℝ) * τ * Real.log 2) / Real.log 2 := by field_simp [h5.ne'] <;> ring
    _ > Real.log 20 / Real.log 2 := by gcongr
  exact h9

/-- Given N*τ > log₂20, prove r2^τ ≤ 1/6 where r2 = 2^(-N). -/
lemma r2τ_le_sixth (N : ℕ) (τ : ℝ) (hτ : 0 < τ)
    (h_Nτ : (N : ℝ) * τ > Real.log 20 / Real.log 2) :
    ((2 : ℝ) ^ (-(N : ℝ))) ^ τ ≤ 1 / 6 := by
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_gt : (N : ℝ) * τ > Real.log 6 / Real.log 2 := by
    have h6 : Real.log 20 > Real.log 6 := Real.log_lt_log (by norm_num) (by norm_num)
    have h7 : Real.log 20 / Real.log 2 > Real.log 6 / Real.log 2 := by gcongr
    calc (N : ℝ) * τ > Real.log 20 / Real.log 2 := h_Nτ
      _ > Real.log 6 / Real.log 2 := h7
  set e : ℝ := Real.log 6 / Real.log 2 with he_def
  have h_exp : ((2 : ℝ) ^ (-(N : ℝ))) ^ τ = (2 : ℝ) ^ (-((N : ℝ) * τ)) := by
    have h9 : ((2 : ℝ) ^ (-(N : ℝ))) ^ τ = (2 : ℝ) ^ ((-(N : ℝ)) * τ) :=
      (Real.rpow_mul (show (0 : ℝ) ≤ 2 from by norm_num) (-(N : ℝ)) τ).symm
    rw [h9]
    have h10 : (-(N : ℝ)) * τ = -((N : ℝ) * τ) := by ring
    rw [h10]
  rw [h_exp]
  have h9 : (2 : ℝ) ^ (-((N : ℝ) * τ)) ≤ (2 : ℝ) ^ (-e) := by
    apply Real.rpow_le_rpow_of_exponent_le
    · norm_num
    · linarith
  have h10 : (2 : ℝ) ^ e = 6 := by
    have h11 : Real.logb 2 6 = e := by simp [e, Real.logb]
    rw [← h11]
    exact Real.rpow_logb (show (0 : ℝ) < 2 from by norm_num) (show (2 : ℝ) ≠ 1 from by norm_num) (show (0 : ℝ) < 6 from by norm_num)
  have h11 : (2 : ℝ) ^ (-e) = 1 / 6 := by
    have h12 : (2 : ℝ) ^ (-e) = ((2 : ℝ) ^ e)⁻¹ := Real.rpow_neg (by norm_num) e
    rw [h12, h10] <;> ring
  rw [h11] at h9
  exact h9

/-- Given N*τ > log₂20 and κ = 14τ/(1-σ) with 0 < 1-σ ≤ 1, prove r2^κ ≤ 1/2. -/
lemma r2κ_le_half (N : ℕ) (τ σ κ : ℝ) (hτ : 0 < τ)
    (h1mσ_pos : 0 < 1 - σ) (h1mσ_le_one : 1 - σ ≤ 1)
    (hκ_def : κ = 14 * τ / (1 - σ))
    (h_Nτ : (N : ℝ) * τ > Real.log 20 / Real.log 2) :
    ((2 : ℝ) ^ (-(N : ℝ))) ^ κ ≤ 1 / 2 := by
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h5 : Real.log 20 / Real.log 2 > 1 := by
    have h6 : Real.log 20 > Real.log 2 := Real.log_lt_log (by norm_num) (by norm_num)
    have h7 : Real.log 20 / Real.log 2 > Real.log 2 / Real.log 2 := by gcongr
    have h8 : Real.log 2 / Real.log 2 = 1 := by
      field_simp [h_log2_pos.ne'] <;> ring
    rw [h8] at h7
    exact h7
  have h_Nκ_gt_one : (N : ℝ) * κ > 1 := by
    rw [hκ_def]
    have h1 : (N : ℝ) * (14 * τ / (1 - σ)) = (14 / (1 - σ)) * ((N : ℝ) * τ) := by ring
    rw [h1]
    have h2 : 14 / (1 - σ) ≥ 14 := by
      have h3 : 0 < 1 - σ := h1mσ_pos
      have h4 : 1 - σ ≤ 1 := h1mσ_le_one
      have h5 : 14 / (1 - σ) ≥ 14 / 1 := by gcongr
      have h6 : 14 / 1 = 14 := by norm_num
      linarith
    have h8 : (14 / (1 - σ)) * ((N : ℝ) * τ) ≥ 14 * ((N : ℝ) * τ) := by gcongr
    have h9 : 14 * ((N : ℝ) * τ) > 14 * (Real.log 20 / Real.log 2) := by gcongr
    have h10 : 14 * (Real.log 20 / Real.log 2) > 1 := by linarith [h5]
    linarith
  have h_exp : ((2 : ℝ) ^ (-(N : ℝ))) ^ κ = (2 : ℝ) ^ (-((N : ℝ) * κ)) := by
    have h9 : ((2 : ℝ) ^ (-(N : ℝ))) ^ κ = (2 : ℝ) ^ ((-(N : ℝ)) * κ) :=
      (Real.rpow_mul (show (0 : ℝ) ≤ 2 from by norm_num) (-(N : ℝ)) κ).symm
    rw [h9]
    have h10 : (-(N : ℝ)) * κ = -((N : ℝ) * κ) := by ring
    rw [h10]
  rw [h_exp]
  have h10 : (N : ℝ) * κ ≥ 1 := by linarith
  have h11 : (2 : ℝ) ^ (-((N : ℝ) * κ)) ≤ (2 : ℝ) ^ (-1 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le
    · norm_num
    · linarith
  have h12 : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by
    simpa using Real.rpow_neg_one (2 : ℝ)
  rw [h12] at h11
  exact h11

/-- Given N*τ > log₂20, τ < 1/100, κ ≤ 14/100, prove r2^(1-κ) ≤ √3/4. -/
lemma r21mk_le_sqrt3_4 (N : ℕ) (τ κ : ℝ) (hτ : 0 < τ) (hτ_lt_01 : τ < 1 / 100)
    (hκ_le_014 : κ ≤ 14 / 100) (hκ_nonneg : 0 ≤ κ)
    (h_Nτ : (N : ℝ) * τ > Real.log 20 / Real.log 2) :
    ((2 : ℝ) ^ (-(N : ℝ))) ^ (1 - κ) ≤ Real.sqrt 3 / 4 := by
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_Nτ_gt4 : (N : ℝ) * τ > 4 := by
    have h1 : (16 : ℝ) < 20 := by norm_num
    have h2 : Real.log 20 > Real.log 16 := Real.log_lt_log (by positivity) h1
    have h3 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] <;> ring
    have h4 : Real.log 20 / Real.log 2 > 4 := by
      calc Real.log 20 / Real.log 2
        > Real.log 16 / Real.log 2 := by gcongr
      _ = 4 := by
        rw [h3] <;> field_simp [h_log2_pos.ne'] <;> ring
    calc (N : ℝ) * τ > Real.log 20 / Real.log 2 := h_Nτ
      _ > 4 := h4
  have h_N_gt400 : (N : ℝ) > 400 := by
    have h5 : (N : ℝ) * τ > 4 := h_Nτ_gt4
    have h6 : (N : ℝ) > 4 / τ := by
      calc (N : ℝ)
        = ((N : ℝ) * τ) / τ := by field_simp [hτ.ne'] <;> ring
      _ > 4 / τ := by gcongr
    have h7 : 4 / τ > 400 := by
      have h8 : 4 / τ > 4 / (1 / 100 : ℝ) := by gcongr
      have h9 : 4 / (1 / 100 : ℝ) = 400 := by norm_num
      linarith
    linarith
  have h_1mk_ge : 1 - κ ≥ 86 / 100 := by linarith [hκ_le_014]
  have h_N1mk_gt2 : (N : ℝ) * (1 - κ) > 2 := by
    have h7 : (N : ℝ) * (1 - κ) ≥ (N : ℝ) * (86 / 100 : ℝ) := by gcongr
    have h8 : (N : ℝ) > 400 := h_N_gt400
    have h9 : (N : ℝ) * (86 / 100 : ℝ) > 400 * (86 / 100 : ℝ) := by gcongr
    have h10 : 400 * (86 / 100 : ℝ) = 344 := by norm_num
    linarith
  set target_exp : ℝ := (Real.log 4 - Real.log (Real.sqrt 3)) / Real.log 2 with htarget_def
  have h11 : 1 < Real.sqrt 3 := by
    have h12 : (1 : ℝ) < 3 := by norm_num
    have h13 : Real.sqrt 1 < Real.sqrt 3 := Real.sqrt_lt_sqrt (by linarith) h12
    have h14 : Real.sqrt 1 = 1 := Real.sqrt_one
    linarith
  have h_target_lt2 : target_exp < 2 := by
    dsimp only [target_exp]
    have h12 : 0 < Real.log (Real.sqrt 3) := Real.log_pos h11
    have h13 : Real.log 4 - Real.log (Real.sqrt 3) < 2 * Real.log 2 := by
      have h14 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] <;> ring
      rw [h14] <;> linarith
    calc (Real.log 4 - Real.log (Real.sqrt 3)) / Real.log 2
      < (2 * Real.log 2) / Real.log 2 := by gcongr
    _ = 2 := by field_simp [h_log2_pos.ne'] <;> ring
  have h_gt : (N : ℝ) * (1 - κ) > target_exp := by
    linarith [h_N1mk_gt2, h_target_lt2]
  have h_exp : ((2 : ℝ) ^ (-(N : ℝ))) ^ (1 - κ) = (2 : ℝ) ^ (-((N : ℝ) * (1 - κ))) := by
    have h9 : ((2 : ℝ) ^ (-(N : ℝ))) ^ (1 - κ) = (2 : ℝ) ^ ((-(N : ℝ)) * (1 - κ)) :=
      (Real.rpow_mul (show (0 : ℝ) ≤ 2 from by norm_num) (-(N : ℝ)) (1 - κ)).symm
    rw [h9]
    have h10 : (-(N : ℝ)) * (1 - κ) = -((N : ℝ) * (1 - κ)) := by ring
    rw [h10]
  rw [h_exp]
  have h14 : (2 : ℝ) ^ (-((N : ℝ) * (1 - κ))) ≤ (2 : ℝ) ^ (-target_exp) := by
    apply Real.rpow_le_rpow_of_exponent_le
    · norm_num
    · linarith
  have h15 : (2 : ℝ) ^ target_exp = 4 / Real.sqrt 3 := by
    have h_pos1 : (0 : ℝ) < 4 := by norm_num
    have h_pos2 : (0 : ℝ) < Real.sqrt 3 := by positivity
    have h16 : Real.logb 2 (4 / Real.sqrt 3) = target_exp := by
      rw [Real.logb, Real.log_div (show (4 : ℝ) ≠ 0 from by norm_num) (show (Real.sqrt 3 : ℝ) ≠ 0 from by positivity)]
      <;> simp [target_exp] <;> field_simp <;> ring
    rw [← h16]
    have h_ne_one : (4 / Real.sqrt 3 : ℝ) ≠ 1 := by
      have h_gt_one : (4 / Real.sqrt 3 : ℝ) > 1 := by
        have h_sq3 : Real.sqrt 3 < 4 := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 from by norm_num)]
        have h : (4 : ℝ) > Real.sqrt 3 := h_sq3
        have h2 : (4 / Real.sqrt 3 : ℝ) > 1 := by
          calc (4 / Real.sqrt 3 : ℝ)
            > Real.sqrt 3 / Real.sqrt 3 := by gcongr
          _ = 1 := by
            field_simp [h_pos2.ne'] <;> ring
        exact h2
      linarith
    exact Real.rpow_logb (show (0 : ℝ) < 2 from by norm_num) (show (2 : ℝ) ≠ 1 from by norm_num) (show (0 : ℝ) < (4 / Real.sqrt 3) from by positivity)
  have h17 : (2 : ℝ) ^ (-target_exp) = Real.sqrt 3 / 4 := by
    have h18 : (2 : ℝ) ^ (-target_exp) = ((2 : ℝ) ^ target_exp)⁻¹ := Real.rpow_neg (by norm_num) target_exp
    rw [h18, h15]
    field_simp <;> ring
  rw [h17] at h14
  exact h14

/-- Given N*τ > log₂20, τ < 1/100, κ ≤ 14/100, prove r2^(1-κ) ≤ 1/16. -/
lemma r21mk_le_16 (N : ℕ) (τ κ : ℝ) (hτ : 0 < τ) (hτ_lt_01 : τ < 1 / 100)
    (hκ_le_014 : κ ≤ 14 / 100) (h_Nτ : (N : ℝ) * τ > Real.log 20 / Real.log 2) :
    ((2 : ℝ) ^ (-(N : ℝ))) ^ (1 - κ) ≤ 1 / 16 := by
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_Nτ_gt4 : (N : ℝ) * τ > 4 := by
    have h1 : Real.log 20 / Real.log 2 > 4 := by
      have h2 : (16 : ℝ) < 20 := by norm_num
      have h3 : Real.log 20 > Real.log 16 := Real.log_lt_log (by positivity) h2
      have h4 : Real.log 16 = 4 * Real.log 2 := by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] <;> ring
      calc Real.log 20 / Real.log 2
        > Real.log 16 / Real.log 2 := by gcongr
      _ = 4 := by rw [h4] <;> field_simp [h_log2_pos.ne'] <;> ring
    linarith [h_Nτ]
  have h_1mk_ge : 1 - κ ≥ 86 / 100 := by linarith [hκ_le_014]
  have h_1mk_div_tau_ge86 : (1 - κ) / τ ≥ 86 := by
    have h8 : 1 - κ ≥ 86 / 100 := h_1mk_ge
    have h9 : τ ≤ 1 / 100 := by linarith [hτ_lt_01]
    have h10 : 1 / τ ≥ 100 := by
      have h11 : 1 / τ ≥ 1 / (1 / 100 : ℝ) := by
        apply one_div_le_one_div_of_le <;> linarith
      have h12 : 1 / (1 / 100 : ℝ) = 100 := by norm_num
      rw [h12] at h11; exact h11
    have h13 : (1 - κ) / τ = (1 - κ) * (1 / τ) := by
      field_simp [hτ.ne'] <;> ring
    rw [h13]
    have h14 : (1 - κ) * (1 / τ) ≥ (86 / 100 : ℝ) * 100 := by gcongr
    have h15 : (86 / 100 : ℝ) * 100 = 86 := by norm_num
    linarith
  have h_N1mk_ge4 : (N : ℝ) * (1 - κ) ≥ 4 := by
    have h6 : (N : ℝ) * (1 - κ) = ((N : ℝ) * τ) * ((1 - κ) / τ) := by
      field_simp [hτ.ne'] <;> ring
    rw [h6]
    have h7 : ((N : ℝ) * τ) * ((1 - κ) / τ) ≥ 4 * 86 := by gcongr
    linarith
  have h_exp : ((2 : ℝ) ^ (-(N : ℝ))) ^ (1 - κ) = (2 : ℝ) ^ (-((N : ℝ) * (1 - κ))) := by
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ 2 from by norm_num)] <;> ring_nf
  rw [h_exp]
  have h10 : (2 : ℝ) ^ (-((N : ℝ) * (1 - κ))) ≤ (2 : ℝ) ^ (-4 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le
    · norm_num
    · linarith
  have h11 : (2 : ℝ) ^ (-4 : ℝ) = 1 / 16 := by
    have h12 : (2 : ℝ) ^ (-4 : ℝ) = ((2 : ℝ) ^ (4 : ℝ))⁻¹ := Real.rpow_neg (by norm_num) 4
    rw [h12]
    have h13 : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
    rw [h13] <;> ring
  rw [h11] at h10; exact h10

/-- Exponential lower bound: exp y ≥ y²/4 for y ≥ 0. -/
lemma exp_sq_bound (y : ℝ) (hy : 0 ≤ y) : Real.exp y ≥ y^2 / 4 := by
  have h1 : Real.exp (y / 2) ≥ 1 + y / 2 := by
    linarith [Real.add_one_le_exp (y / 2)]
  have h2 : Real.exp y = (Real.exp (y / 2)) ^ 2 := by
    have h3 : y = y / 2 + y / 2 := by ring
    rw [h3, Real.exp_add] <;> ring_nf
  rw [h2]
  have h4 : 0 ≤ 1 + y / 2 := by linarith
  nlinarith

/-- Frostman bound: if N > log(20C)/(τ*log2), then 20*C*2^(-Nτ) < 1. -/
lemma frostman_bound (N : ℕ) (τ C : ℝ) (hτ : 0 < τ) (hC : 1 ≤ C)
    (hN_gt : (N : ℝ) > Real.log (20 * C) / (τ * Real.log 2)) :
    20 * C * ((2 : ℝ) ^ (-(N : ℝ))) ^ τ < 1 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_pos20C : 0 < 20 * C :=
    mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hC)
  have h10 : (N : ℝ) * τ > Real.log (20 * C) / Real.log 2 := by
    have h12 : 0 < τ := hτ
    have h13 : (N : ℝ) * τ > (Real.log (20 * C) / (τ * Real.log 2)) * τ :=
      mul_lt_mul_of_pos_right hN_gt h12
    have h14 : (Real.log (20 * C) / (τ * Real.log 2)) * τ = Real.log (20 * C) / Real.log 2 := by
      have h15 : τ ≠ 0 := hτ.ne'
      have h16 : Real.log 2 ≠ 0 := hlog2_pos.ne'
      calc (Real.log (20 * C) / (τ * Real.log 2)) * τ
        = Real.log (20 * C) * τ / (τ * Real.log 2) := by ring
      _ = Real.log (20 * C) / Real.log 2 := by
        have h17 : Real.log (20 * C) * τ = τ * Real.log (20 * C) := by ring
        rw [h17, mul_div_mul_left _ _ h15] <;> ring
    rw [h14] at h13
    exact h13
  have h15 : (N : ℝ) * τ * Real.log 2 > Real.log (20 * C) := by
    have h16 : (N : ℝ) * τ > Real.log (20 * C) / Real.log 2 := h10
    have h17 : ((N : ℝ) * τ) * Real.log 2 > (Real.log (20 * C) / Real.log 2) * Real.log 2 :=
      mul_lt_mul_of_pos_right h16 hlog2_pos
    have h18 : (Real.log (20 * C) / Real.log 2) * Real.log 2 = Real.log (20 * C) :=
      div_mul_cancel₀ (Real.log (20 * C)) hlog2_pos.ne'
    rw [h18] at h17
    exact h17
  have h_exp1 : Real.exp ((N : ℝ) * τ * Real.log 2) > Real.exp (Real.log (20 * C)) :=
    Real.exp_strictMono h15
  have h_exp2 : Real.exp ((N : ℝ) * τ * Real.log 2) = (2 : ℝ) ^ ((N : ℝ) * τ) := by
    have h_pos : (0 : ℝ) < 2 := by norm_num
    have h' : (2 : ℝ) ^ ((N : ℝ) * τ) = Real.exp (Real.log 2 * ((N : ℝ) * τ)) :=
      Real.rpow_def_of_pos h_pos ((N : ℝ) * τ)
    have h_comm : Real.log 2 * ((N : ℝ) * τ) = (N : ℝ) * τ * Real.log 2 := by ring
    rw [h_comm] at h'
    exact h'.symm
  have h_exp3 : Real.exp (Real.log (20 * C)) = 20 * C := Real.exp_log h_pos20C
  rw [h_exp2, h_exp3] at h_exp1
  have h20 : (2 : ℝ) ^ ((N : ℝ) * τ) > 20 * C := h_exp1
  have h22 : (2 : ℝ) ^ (-((N : ℝ) * τ)) < 1 / (20 * C) := by
    have h23 : (2 : ℝ) ^ (-((N : ℝ) * τ)) = ((2 : ℝ) ^ ((N : ℝ) * τ))⁻¹ :=
      Real.rpow_neg (by norm_num) _
    rw [h23]
    have h24 : ((2 : ℝ) ^ ((N : ℝ) * τ))⁻¹ < (20 * C)⁻¹ := by gcongr
    have h25 : (20 * C)⁻¹ = 1 / (20 * C) := by ring
    rw [h25] at h24
    exact h24
  have h9 : ((2 : ℝ) ^ (-(N : ℝ))) ^ τ = (2 : ℝ) ^ (-((N : ℝ) * τ)) := by
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ 2 from by norm_num)] <;> ring_nf
  rw [h9]
  calc 20 * C * (2 : ℝ) ^ (-((N : ℝ) * τ))
    < 20 * C * (1 / (20 * C)) := by gcongr
  _ = 1 := by field_simp [h_pos20C.ne'] <;> ring

/-- Delta bound: if N > 1 + log(1/δ₀)/log2, then 2 * 2^(-N) ≤ δ₀. -/
lemma delta_bound (N : ℕ) (δ₀ : ℝ) (hδ0_pos : 0 < δ₀)
    (hN_gt : (N : ℝ) > 1 + Real.log (1 / δ₀) / Real.log 2) :
    2 * (2 : ℝ) ^ (-(N : ℝ)) ≤ δ₀ := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : 1 - (N : ℝ) < -Real.log (1 / δ₀) / Real.log 2 := by
    set x : ℝ := Real.log (1 / δ₀) / Real.log 2 with hx
    have h2 : (N : ℝ) > 1 + x := hN_gt
    have h3 : x < (N : ℝ) - 1 := by linarith
    have h4 : -((N : ℝ) - 1) < -x := neg_lt_neg h3
    have h5 : -((N : ℝ) - 1) = 1 - (N : ℝ) := by ring
    have h6 : -x = -Real.log (1 / δ₀) / Real.log 2 := by
      simp [hx] <;> ring
    rw [h5, h6] at h4
    exact h4
  have h2 : (2 : ℝ) ^ (1 - (N : ℝ)) ≤ (2 : ℝ) ^ (-Real.log (1 / δ₀) / Real.log 2) := by
    apply Real.rpow_le_rpow_of_exponent_le
    · norm_num
    · exact le_of_lt h1
  have h3 : Real.log (1 / δ₀) = -Real.log δ₀ := by
    have h4 : Real.log (1 / δ₀) = Real.log 1 - Real.log δ₀ :=
      Real.log_div (by norm_num) hδ0_pos.ne'
    rw [h4, Real.log_one] <;> ring
  have h5 : -Real.log (1 / δ₀) / Real.log 2 = Real.log δ₀ / Real.log 2 := by
    rw [h3] <;> ring
  rw [h5] at h2
  have h6 : (2 : ℝ) ^ (Real.log δ₀ / Real.log 2) = δ₀ := by
    have h7 : Real.logb 2 δ₀ = Real.log δ₀ / Real.log 2 := by rfl
    rw [← h7]
    exact Real.rpow_logb (show (0 : ℝ) < 2 from by norm_num) (show (2 : ℝ) ≠ 1 from by norm_num) hδ0_pos
  rw [h6] at h2
  have h7 : 2 * (2 : ℝ) ^ (-(N : ℝ)) = (2 : ℝ) ^ (1 - (N : ℝ)) := by
    have h8 : (2 : ℝ) ^ (1 - (N : ℝ)) = (2 : ℝ) ^ ((1 : ℝ) + (-(N : ℝ))) := by ring_nf
    rw [h8]
    have h9 : (2 : ℝ) ^ ((1 : ℝ) + (-(N : ℝ))) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(N : ℝ)) :=
      Real.rpow_add (by norm_num) (1 : ℝ) (-(N : ℝ))
    rw [h9] <;> simp
  rw [h7]
  exact h2

/-- Small3 bound: exponential inequality for non-concentrated case. -/
lemma small3_bound (N : ℕ) (σ τ κ ε_F : ℝ) (hτ : 0 < τ)
    (hE_pos : 0 < ε_F - 8 * τ - 3 * κ)
    (hN_gt : (N : ℝ) > (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ)) :
    (2 : ℝ) ^ (-(2 * σ + ε_F)) *
      ((2 : ℝ) ^ (-(N : ℝ))) ^ (-(ε_F - 8 * τ - 2 * κ)) >
      80000 * ((2 : ℝ) ^ (-(N : ℝ))) ^ (-κ) := by
  set E : ℝ := ε_F - 8 * τ - 3 * κ with hE_def
  have h_ineq : (N : ℝ) * E > 2 * σ + ε_F + Real.log 80000 / Real.log 2 := by
    have h1 : (N : ℝ) > (2 * σ + ε_F + Real.log 80000 / Real.log 2) / E := hN_gt
    have h2 : 0 < E := hE_pos
    calc (N : ℝ) * E > ((2 * σ + ε_F + Real.log 80000 / Real.log 2) / E) * E := by gcongr
      _ = 2 * σ + ε_F + Real.log 80000 / Real.log 2 := by field_simp [h2.ne'] <;> ring
  have h_exp1 : ((2 : ℝ) ^ (-(N : ℝ))) ^ (-(ε_F - 8 * τ - 2 * κ)) =
      (2 : ℝ) ^ ((N : ℝ) * (ε_F - 8 * τ - 2 * κ)) := by
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ 2 from by norm_num)] <;> ring_nf
  have h_exp2 : ((2 : ℝ) ^ (-(N : ℝ))) ^ (-κ) = (2 : ℝ) ^ ((N : ℝ) * κ) := by
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ 2 from by norm_num)] <;> ring_nf
  rw [h_exp1, h_exp2]
  have h3 : (2 : ℝ) ^ (-(2 * σ + ε_F)) * (2 : ℝ) ^ ((N : ℝ) * (ε_F - 8 * τ - 2 * κ)) =
      (2 : ℝ) ^ ((N : ℝ) * (ε_F - 8 * τ - 2 * κ) - (2 * σ + ε_F)) := by
    rw [← Real.rpow_add (by norm_num)] <;> ring_nf
  rw [h3]
  have h4 : (N : ℝ) * (ε_F - 8 * τ - 2 * κ) - (2 * σ + ε_F) =
      (N : ℝ) * E + (N : ℝ) * κ - (2 * σ + ε_F) := by
    simp [hE_def] <;> ring
  rw [h4]
  have h5 : (N : ℝ) * E + (N : ℝ) * κ - (2 * σ + ε_F) > Real.log 80000 / Real.log 2 + (N : ℝ) * κ := by
    linarith [h_ineq]
  have h6 : (2 : ℝ) ^ ((N : ℝ) * E + (N : ℝ) * κ - (2 * σ + ε_F)) >
      (2 : ℝ) ^ (Real.log 80000 / Real.log 2 + (N : ℝ) * κ) := by
    apply Real.rpow_lt_rpow_of_exponent_lt
    · norm_num
    · exact h5
  have h7 : (2 : ℝ) ^ (Real.log 80000 / Real.log 2 + (N : ℝ) * κ) =
      (2 : ℝ) ^ (Real.log 80000 / Real.log 2) * (2 : ℝ) ^ ((N : ℝ) * κ) :=
    Real.rpow_add (by norm_num) (Real.log 80000 / Real.log 2) ((N : ℝ) * κ)
  have h8 : (2 : ℝ) ^ (Real.log 80000 / Real.log 2) = 80000 := by
    have h9 : Real.logb 2 80000 = Real.log 80000 / Real.log 2 := by rfl
    rw [← h9]
    exact Real.rpow_logb (show (0 : ℝ) < 2 from by norm_num) (show (2 : ℝ) ≠ 1 from by norm_num) (by positivity)
  rw [h7, h8] at h6
  exact h6

/-- Lower bound: K' / 2^(σ+τ) ≥ 2 * r0^(2τ) when K' > 4 and r0 ≤ 1. -/
lemma r0_lower_ineq (K' σ τ r0 : ℝ) (hK'_gt4 : K' > 4)
    (hστ_pos : 0 < σ + τ) (hστ_lt_one : σ + τ < 1)
    (hr0_nonneg : 0 ≤ r0) (hr0_le_one : r0 ≤ 1) (hτ : 0 < τ) :
    K' / (2 : ℝ) ^ (σ + τ) ≥ 2 * r0 ^ (2 * τ) := by
  have h1 : (2 : ℝ) ^ (σ + τ) < 2 := by
    have h2 : (2 : ℝ) ^ (σ + τ) < (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    simpa using h2
  have h3 : r0 ^ (2 * τ) ≤ 1 := by
    have h4 : 0 ≤ r0 := hr0_nonneg
    have h5 : 0 ≤ 2 * τ := by positivity
    exact Real.rpow_le_one h4 hr0_le_one h5
  have h6 : 2 * (2 : ℝ) ^ (σ + τ) * r0 ^ (2 * τ) ≤ 2 * (2 : ℝ) ^ (σ + τ) := by
    have h7 : 0 ≤ 2 * (2 : ℝ) ^ (σ + τ) := by positivity
    exact mul_le_of_le_one_right h7 h3
  have h8 : 2 * (2 : ℝ) ^ (σ + τ) < 4 := by
    have h9 : (2 : ℝ) ^ (σ + τ) < 2 := h1
    linarith
  have h10 : K' ≥ 2 * (2 : ℝ) ^ (σ + τ) * r0 ^ (2 * τ) := by linarith
  have h11 : 0 < (2 : ℝ) ^ (σ + τ) := by positivity
  have h12 : K' / (2 : ℝ) ^ (σ + τ) ≥ (2 * (2 : ℝ) ^ (σ + τ) * r0 ^ (2 * τ)) / (2 : ℝ) ^ (σ + τ) :=
    div_le_div_of_nonneg_right h10 (by positivity)
  have h13 : (2 * (2 : ℝ) ^ (σ + τ) * r0 ^ (2 * τ)) / (2 : ℝ) ^ (σ + τ) = 2 * r0 ^ (2 * τ) := by
    field_simp [h11.ne'] <;> ring
  rw [h13] at h12
  exact h12

/-- Key logarithmic inequality needed for parameter selection. -/
lemma key_log_ineq (M s σ τ c b C : ℝ) (hM : 1 ≤ M) (hM_gt2s : M > 2 * s)
    (hσ_pos : 0 < σ) (hτ : 0 < τ) (hc : 0 < c) (hc_lt : c < 1 / 10) (hb_pos : 0 < b)
    (hC : 1 ≤ C) (hK'_key : M * Real.log (10 * M) > s * Real.log (20 / b) + 2 * (σ + τ) * Real.log 2) :
    (M - s) * Real.log (1 / c) + M * Real.log (C ^ 2 * M) >
      s * Real.log (2 / b) + 2 * (σ + τ) * Real.log 2 := by
  have h1 : Real.log (1 / c) > Real.log 10 := by
    have h2 : 1 / c > 10 := by
      have h3 : c < 1 / 10 := hc_lt
      field_simp [hc.ne'] <;> linarith
    exact Real.log_lt_log (by positivity) h2
  have h2 : Real.log (C ^ 2 * M) ≥ Real.log M := by
    have h3 : C ^ 2 * M ≥ M := by
      have h4 : C ^ 2 ≥ 1 := by nlinarith
      nlinarith
    exact Real.log_le_log (by positivity) h3
  have h4 : 0 < M - s := by linarith
  have h5 : (M - s) * Real.log (1 / c) + M * Real.log (C ^ 2 * M) >
      (M - s) * Real.log 10 + M * Real.log M := by
    have h6 : (M - s) * Real.log (1 / c) > (M - s) * Real.log 10 :=
      mul_lt_mul_of_pos_left h1 h4
    have h7 : M * Real.log (C ^ 2 * M) ≥ M * Real.log M :=
      mul_le_mul_of_nonneg_left h2 (by linarith [hM])
    linarith
  have h6 : (M - s) * Real.log 10 + M * Real.log M = M * Real.log (10 * M) - s * Real.log 10 := by
    have h7 : Real.log (10 * M) = Real.log 10 + Real.log M := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (show (0 : ℝ) < M by linarith [hM]))] <;> ring
    rw [h7] <;> ring
  rw [h6] at h5
  have h8 : M * Real.log (10 * M) - s * Real.log 10 >
      s * Real.log (2 / b) + 2 * (σ + τ) * Real.log 2 := by
    have h9 : s * Real.log 10 + s * Real.log (2 / b) = s * Real.log (20 / b) := by
      have h10 : Real.log (20 / b) = Real.log 10 + Real.log (2 / b) := by
        have hpos1 : (0 : ℝ) < 10 := by norm_num
        have hpos2 : (0 : ℝ) < 2 / b := by exact div_pos (by norm_num) hb_pos
        have h11 : 20 / b = 10 * (2 / b) := by field_simp [hb_pos.ne'] <;> ring
        rw [h11, Real.log_mul hpos1.ne' hpos2.ne'] <;> ring
      rw [h10] <;> ring
    linarith [hK'_key]
  linarith

/-- Bound: r2^τ * log(1/r2) ≤ 1/100 when N > 400/(τ^2 * log 2). -/
lemma log_abs_bound (N τ : ℝ) (hτ : 0 < τ) (hN_gt : N > 400 / (τ^2 * Real.log 2)) :
    ((2 : ℝ)^(-N))^τ * Real.log (1 / ((2 : ℝ)^(-N))) ≤ 1 / 100 := by
  set x : ℝ := N * τ with hx_def
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx_pos : 0 < x := by
    have h : N > 400 / (τ^2 * Real.log 2) := hN_gt
    have h2 : 0 < 400 / (τ^2 * Real.log 2) := by positivity
    have h3 : 0 < N := by linarith
    exact mul_pos h3 hτ
  have hxl2_pos : 0 < x * Real.log 2 := mul_pos hx_pos hlog2_pos
  have hx_gt : x > 400 / (τ * Real.log 2) := by
    have h : N > 400 / (τ^2 * Real.log 2) := hN_gt
    calc x = N * τ := by rfl
      _ > (400 / (τ^2 * Real.log 2)) * τ := by gcongr
      _ = 400 / (τ * Real.log 2) := by
        field_simp [hτ.ne'] <;> ring
  have h_exp_bound : (2 : ℝ) ^ x ≥ (x * Real.log 2)^2 / 4 := by
    have h : Real.exp (x * Real.log 2) ≥ (x * Real.log 2)^2 / 4 :=
      exp_sq_bound (x * Real.log 2) (by linarith)
    have h2 : (2 : ℝ) ^ x = Real.exp (x * Real.log 2) := by
      rw [Real.rpow_def_of_pos (by norm_num)] <;> ring_nf
    rw [h2]; exact h
  have h3 : (2 : ℝ) ^ (-x) ≤ 4 / ((x * Real.log 2)^2) := by
    have h4 : (2 : ℝ) ^ x ≥ (x * Real.log 2)^2 / 4 := h_exp_bound
    have h5 : 0 < (x * Real.log 2)^2 := by exact pow_pos hxl2_pos 2
    have h6 : (2 : ℝ) ^ (-x) = ((2 : ℝ) ^ x)⁻¹ := Real.rpow_neg (by norm_num) x
    rw [h6]
    have h7 : ((2 : ℝ) ^ x)⁻¹ ≤ (((x * Real.log 2)^2 / 4))⁻¹ := by gcongr
    have h8 : (((x * Real.log 2)^2 / 4))⁻¹ = 4 / ((x * Real.log 2)^2) := by
      field_simp [h5.ne'] <;> ring
    rw [h8] at h7; exact h7
  have h7 : N = x / τ := by
    have h9 : x = N * τ := by simp [hx_def]
    rw [h9]
    field_simp [hτ.ne'] <;> ring
  have h8 : x * Real.log 2 * τ ≥ 400 := by
    have h9 : 0 < τ * Real.log 2 := by positivity
    have h10 : x * (τ * Real.log 2) > 400 := by
      calc x * (τ * Real.log 2)
        > (400 / (τ * Real.log 2)) * (τ * Real.log 2) := by gcongr
      _ = 400 := by field_simp [h9.ne'] <;> ring
    have h11 : x * Real.log 2 * τ = x * (τ * Real.log 2) := by ring
    rw [h11]; linarith
  have h_pos_main : 0 < x * Real.log 2 * τ := by positivity
  have h_main : (2 : ℝ) ^ (-x) * (N * Real.log 2) ≤ 1 / 100 := by
    rw [h7]
    have h_ineq1 : (2 : ℝ) ^ (-x) ≤ 4 / ((x * Real.log 2)^2) := h3
    have h_ineq2 : (2 : ℝ) ^ (-x) * ((x / τ) * Real.log 2) ≤
        (4 / ((x * Real.log 2)^2)) * ((x / τ) * Real.log 2) := by
      exact mul_le_mul_of_nonneg_right h_ineq1 (by positivity)
    have h_eq : (4 / ((x * Real.log 2)^2)) * ((x / τ) * Real.log 2) = 4 / (x * Real.log 2 * τ) := by
      field_simp [hτ.ne', hlog2_pos.ne'] <;> ring
    rw [h_eq] at h_ineq2
    have h_final : 4 / (x * Real.log 2 * τ) ≤ 4 / 400 := by
      gcongr
    calc (2 : ℝ) ^ (-x) * ((x / τ) * Real.log 2)
      ≤ 4 / (x * Real.log 2 * τ) := h_ineq2
    _ ≤ 4 / 400 := h_final
    _ = 1 / 100 := by norm_num
  have h9 : ((2 : ℝ) ^ (-N)) ^ τ = (2 : ℝ) ^ (-x) := by
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ 2 from by norm_num)]
    have h10 : -N * τ = -x := by
      simp [hx_def] <;> ring
    rw [h10]
  have h10 : Real.log (1 / ((2 : ℝ) ^ (-N))) = N * Real.log 2 := by
    have h_pos : (0 : ℝ) < (2 : ℝ) ^ (-N) := by positivity
    have h11 : Real.log (1 / ((2 : ℝ) ^ (-N))) = -Real.log ((2 : ℝ) ^ (-N)) := by
      rw [Real.log_div (by norm_num) h_pos.ne'] <;> simp
    rw [h11]
    have h12 : Real.log ((2 : ℝ) ^ (-N)) = (-N) * Real.log 2 := by
      rw [Real.log_rpow (by norm_num)] <;> ring
    rw [h12] <;> ring
  rw [h9, h10]; exact h_main

/-! ### Proof of good_params_exist -/

/-- K-independent lower bound used for M-selection (hN_ok).
    Includes lbE0 = log(390*C*C₁^σ)/(τ*log2) as a buffer to absorb lbE in Case 2. -/
def lowerBound_M (τ σ c C ε_F δ₀ C₁ D_T C_X D_X : ℝ) : ℝ :=
  let c0 := Real.log (2 / (c * (1 - (2 : ℝ)^(-τ)))) / (τ * Real.log 2)
  let c1 := 400 / (τ^2 * Real.log 2)
  let c2 := Real.log (20 * C) / (τ * Real.log 2)
  let c3 := 1 + Real.log (1 / δ₀) / Real.log 2
  let c4 := (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * (14 * τ / (1 - σ)))
  let c5 := Real.log (390 * C * C₁^σ) / (τ * Real.log 2)
  let c7 := 1 + Real.log (C_X * D_X) / (ε_F * Real.log 2)
  max c0 (max c1 (max c2 (max c3 (max c4 (max c5 c7)))))

/-- Combined lower bound on N for all parameter constraints.
    K-dependent lbE is added on top of lowerBound_M. -/
def lowerBound (τ σ c C ε_F δ₀ K C₁ D_T C_X D_X : ℝ) : ℝ :=
  max (lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X)
    (Real.log (390 * K * C * C₁^σ) / (2 * τ * Real.log 2))

-- Short names for the 8 components of lowerBound
abbrev lbT (τ σ c C ε_F δ₀ K C₁ D_T C_X D_X : ℝ) :=
  Real.log (2 / (c * (1 - (2 : ℝ)^(-τ)))) / (τ * Real.log 2)
abbrev lbA (τ σ c C ε_F δ₀ K C₁ D_T C_X D_X : ℝ) :=
  400 / (τ^2 * Real.log 2)
abbrev lbB (τ σ c C ε_F δ₀ K C₁ D_T C_X D_X : ℝ) :=
  Real.log (20 * C) / (τ * Real.log 2)
abbrev lbC (τ σ c C ε_F δ₀ K C₁ D_T C_X D_X : ℝ) :=
  1 + Real.log (1 / δ₀) / Real.log 2
abbrev lbD (τ σ c C ε_F δ₀ K C₁ D_T C_X D_X : ℝ) :=
  let κ := 14 * τ / (1 - σ)
  (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ)
abbrev lbE (τ σ c C ε_F δ₀ K C₁ D_T C_X D_X : ℝ) :=
  Real.log (390 * K * C * C₁^σ) / (2 * τ * Real.log 2)
abbrev lbG (τ σ c C ε_F δ₀ K C₁ D_T C_X D_X : ℝ) :=
  1 + Real.log (C_X * D_X) / (ε_F * Real.log 2)


/-! ### Accessor lemmas for lowerBound_M -/

lemma lowerBound_M_ge_T (τ σ c C ε_F δ₀ C₁ D_T C_X D_X : ℝ) :
    lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X ≥
      Real.log (2 / (c * (1 - (2 : ℝ)^(-τ)))) / (τ * Real.log 2) := by
  dsimp only [lowerBound_M]
  let b := 1 - (2 : ℝ)^(-τ)
  let c0 := Real.log (2 / (c * b)) / (τ * Real.log 2)
  let c1 := 400 / (τ^2 * Real.log 2)
  let c2 := Real.log (20 * C) / (τ * Real.log 2)
  let c3 := 1 + Real.log (1 / δ₀) / Real.log 2
  let c4 := (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * (14 * τ / (1 - σ)))
  let c5 := Real.log (390 * C * C₁^σ) / (τ * Real.log 2)
  let c7 := 1 + Real.log (C_X * D_X) / (ε_F * Real.log 2)
  let M7 := c7
  let M6 := max c5 M7
  let M5 := max c4 M6
  let M4 := max c3 M5
  let M3 := max c2 M4
  let M2 := max c1 M3
  exact le_max_left c0 M2

lemma lowerBound_M_ge_logabs (τ σ c C ε_F δ₀ C₁ D_T C_X D_X : ℝ) :
    lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X ≥ 400 / (τ^2 * Real.log 2) := by
  dsimp only [lowerBound_M]
  let b := 1 - (2 : ℝ)^(-τ)
  let c0 := Real.log (2 / (c * b)) / (τ * Real.log 2)
  let c1 := 400 / (τ^2 * Real.log 2)
  let c2 := Real.log (20 * C) / (τ * Real.log 2)
  let c3 := 1 + Real.log (1 / δ₀) / Real.log 2
  let c4 := (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * (14 * τ / (1 - σ)))
  let c5 := Real.log (390 * C * C₁^σ) / (τ * Real.log 2)
  let c7 := 1 + Real.log (C_X * D_X) / (ε_F * Real.log 2)
  let M7 := c7
  let M6 := max c5 M7
  let M5 := max c4 M6
  let M4 := max c3 M5
  let M3 := max c2 M4
  let M2 := max c1 M3
  have h1 : c1 ≤ M2 := le_max_left c1 M3
  have h2 : M2 ≤ max c0 M2 := le_max_right c0 M2
  exact le_trans h1 h2

lemma lowerBound_M_ge_frostman (τ σ c C ε_F δ₀ C₁ D_T C_X D_X : ℝ) :
    lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X ≥ Real.log (20 * C) / (τ * Real.log 2) := by
  dsimp only [lowerBound_M]
  let b := 1 - (2 : ℝ)^(-τ)
  let c0 := Real.log (2 / (c * b)) / (τ * Real.log 2)
  let c1 := 400 / (τ^2 * Real.log 2)
  let c2 := Real.log (20 * C) / (τ * Real.log 2)
  let c3 := 1 + Real.log (1 / δ₀) / Real.log 2
  let c4 := (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * (14 * τ / (1 - σ)))
  let c5 := Real.log (390 * C * C₁^σ) / (τ * Real.log 2)
  let c7 := 1 + Real.log (C_X * D_X) / (ε_F * Real.log 2)
  let M7 := c7
  let M6 := max c5 M7
  let M5 := max c4 M6
  let M4 := max c3 M5
  let M3 := max c2 M4
  let M2 := max c1 M3
  have h1 : c2 ≤ M3 := le_max_left c2 M4
  have h2 : M3 ≤ M2 := le_max_right c1 M3
  have h3 : M2 ≤ max c0 M2 := le_max_right c0 M2
  exact le_trans (le_trans h1 h2) h3

lemma lowerBound_M_ge_delta (τ σ c C ε_F δ₀ C₁ D_T C_X D_X : ℝ) :
    lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X ≥ 1 + Real.log (1 / δ₀) / Real.log 2 := by
  dsimp only [lowerBound_M]
  let b := 1 - (2 : ℝ)^(-τ)
  let c0 := Real.log (2 / (c * b)) / (τ * Real.log 2)
  let c1 := 400 / (τ^2 * Real.log 2)
  let c2 := Real.log (20 * C) / (τ * Real.log 2)
  let c3 := 1 + Real.log (1 / δ₀) / Real.log 2
  let c4 := (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * (14 * τ / (1 - σ)))
  let c5 := Real.log (390 * C * C₁^σ) / (τ * Real.log 2)
  let c7 := 1 + Real.log (C_X * D_X) / (ε_F * Real.log 2)
  let M7 := c7
  let M6 := max c5 M7
  let M5 := max c4 M6
  let M4 := max c3 M5
  let M3 := max c2 M4
  let M2 := max c1 M3
  have h1 : c3 ≤ M4 := le_max_left c3 M5
  have h2 : M4 ≤ M3 := le_max_right c2 M4
  have h3 : M3 ≤ M2 := le_max_right c1 M3
  have h4 : M2 ≤ max c0 M2 := le_max_right c0 M2
  exact le_trans (le_trans (le_trans h1 h2) h3) h4

lemma lowerBound_M_ge_epsF (τ σ c C ε_F δ₀ C₁ D_T C_X D_X : ℝ) :
    lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X ≥
      (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * (14 * τ / (1 - σ))) := by
  dsimp only [lowerBound_M]
  let b := 1 - (2 : ℝ)^(-τ)
  let c0 := Real.log (2 / (c * b)) / (τ * Real.log 2)
  let c1 := 400 / (τ^2 * Real.log 2)
  let c2 := Real.log (20 * C) / (τ * Real.log 2)
  let c3 := 1 + Real.log (1 / δ₀) / Real.log 2
  let c4 := (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * (14 * τ / (1 - σ)))
  let c5 := Real.log (390 * C * C₁^σ) / (τ * Real.log 2)
  let c7 := 1 + Real.log (C_X * D_X) / (ε_F * Real.log 2)
  let M7 := c7
  let M6 := max c5 M7
  let M5 := max c4 M6
  let M4 := max c3 M5
  let M3 := max c2 M4
  let M2 := max c1 M3
  have h1 : c4 ≤ M5 := le_max_left _ _
  have h2 : M5 ≤ M4 := le_max_right _ _
  have h3 : M4 ≤ M3 := le_max_right _ _
  have h4 : M3 ≤ M2 := le_max_right _ _
  have h5 : M2 ≤ max c0 M2 := le_max_right _ _
  exact le_trans (le_trans (le_trans (le_trans h1 h2) h3) h4) h5

lemma lowerBound_M_ge_E0 (τ σ c C ε_F δ₀ C₁ D_T C_X D_X : ℝ) :
    lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X ≥
      Real.log (390 * C * C₁^σ) / (τ * Real.log 2) := by
  dsimp only [lowerBound_M]
  let b := 1 - (2 : ℝ)^(-τ)
  let c0 := Real.log (2 / (c * b)) / (τ * Real.log 2)
  let c1 := 400 / (τ^2 * Real.log 2)
  let c2 := Real.log (20 * C) / (τ * Real.log 2)
  let c3 := 1 + Real.log (1 / δ₀) / Real.log 2
  let c4 := (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * (14 * τ / (1 - σ)))
  let c5 := Real.log (390 * C * C₁^σ) / (τ * Real.log 2)
  let c7 := 1 + Real.log (C_X * D_X) / (ε_F * Real.log 2)
  let M7 := c7
  let M6 := max c5 M7
  let M5 := max c4 M6
  let M4 := max c3 M5
  let M3 := max c2 M4
  let M2 := max c1 M3
  have h1 : c5 ≤ M6 := le_max_left _ _
  have h2 : M6 ≤ M5 := le_max_right _ _
  have h3 : M5 ≤ M4 := le_max_right _ _
  have h4 : M4 ≤ M3 := le_max_right _ _
  have h5 : M3 ≤ M2 := le_max_right _ _
  have h6 : M2 ≤ max c0 M2 := le_max_right _ _
  exact le_trans (le_trans (le_trans (le_trans (le_trans h1 h2) h3) h4) h5) h6

lemma lowerBound_M_ge_CXDX (τ σ c C ε_F δ₀ C₁ D_T C_X D_X : ℝ) :
    lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X ≥
      1 + Real.log (C_X * D_X) / (ε_F * Real.log 2) := by
  dsimp only [lowerBound_M]
  let b := 1 - (2 : ℝ)^(-τ)
  let c0 := Real.log (2 / (c * b)) / (τ * Real.log 2)
  let c1 := 400 / (τ^2 * Real.log 2)
  let c2 := Real.log (20 * C) / (τ * Real.log 2)
  let c3 := 1 + Real.log (1 / δ₀) / Real.log 2
  let c4 := (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * (14 * τ / (1 - σ)))
  let c5 := Real.log (390 * C * C₁^σ) / (τ * Real.log 2)
  let c7 := 1 + Real.log (C_X * D_X) / (ε_F * Real.log 2)
  let M7 := c7
  let M6 := max c5 M7
  let M5 := max c4 M6
  let M4 := max c3 M5
  let M3 := max c2 M4
  let M2 := max c1 M3
  have h1 : c7 ≤ M7 := by rfl
  have h2 : M7 ≤ M6 := le_max_right _ _
  have h3 : M6 ≤ M5 := le_max_right _ _
  have h4 : M5 ≤ M4 := le_max_right _ _
  have h5 : M4 ≤ M3 := le_max_right _ _
  have h6 : M3 ≤ M2 := le_max_right _ _
  have h7 : M2 ≤ max c0 M2 := le_max_right _ _
  exact le_trans (le_trans (le_trans (le_trans (le_trans (le_trans h1 h2) h3) h4) h5) h6) h7

/-! ### Accessor lemmas for lowerBound (delegate to lowerBound_M) -/

lemma lowerBound_ge_M (τ σ c C ε_F δ₀ K C₁ D_T C_X D_X : ℝ) :
    lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X ≤ lowerBound τ σ c C ε_F δ₀ K C₁ D_T C_X D_X := by
  let LM := lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X
  let lbE := Real.log (390 * K * C * C₁^σ) / (2 * τ * Real.log 2)
  have h : lowerBound τ σ c C ε_F δ₀ K C₁ D_T C_X D_X = max LM lbE := by
    rfl
  rw [h]
  exact le_max_left LM lbE

lemma lowerBound_ge_T (τ σ c C ε_F δ₀ K C₁ D_T C_X D_X : ℝ) :
    lowerBound τ σ c C ε_F δ₀ K C₁ D_T C_X D_X ≥
      Real.log (2 / (c * (1 - (2 : ℝ)^(-τ)))) / (τ * Real.log 2) := by
  have h1 : lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X ≥ _ := lowerBound_M_ge_T _ _ _ _ _ _ _ _ _ _
  exact le_trans h1 (lowerBound_ge_M _ _ _ _ _ _ _ _ _ _ _)

lemma lowerBound_ge_logabs (τ σ c C ε_F δ₀ K C₁ D_T C_X D_X : ℝ) :
    lowerBound τ σ c C ε_F δ₀ K C₁ D_T C_X D_X ≥ 400 / (τ^2 * Real.log 2) := by
  have h1 := lowerBound_M_ge_logabs τ σ c C ε_F δ₀ C₁ D_T C_X D_X
  exact le_trans h1 (lowerBound_ge_M _ _ _ _ _ _ _ _ _ _ _)

lemma lowerBound_ge_frostman (τ σ c C ε_F δ₀ K C₁ D_T C_X D_X : ℝ) :
    lowerBound τ σ c C ε_F δ₀ K C₁ D_T C_X D_X ≥ Real.log (20 * C) / (τ * Real.log 2) := by
  have h1 := lowerBound_M_ge_frostman τ σ c C ε_F δ₀ C₁ D_T C_X D_X
  exact le_trans h1 (lowerBound_ge_M _ _ _ _ _ _ _ _ _ _ _)

lemma lowerBound_ge_delta (τ σ c C ε_F δ₀ K C₁ D_T C_X D_X : ℝ) :
    lowerBound τ σ c C ε_F δ₀ K C₁ D_T C_X D_X ≥ 1 + Real.log (1 / δ₀) / Real.log 2 := by
  have h1 := lowerBound_M_ge_delta τ σ c C ε_F δ₀ C₁ D_T C_X D_X
  exact le_trans h1 (lowerBound_ge_M _ _ _ _ _ _ _ _ _ _ _)

lemma lowerBound_ge_epsF (τ σ c C ε_F δ₀ K C₁ D_T C_X D_X : ℝ) :
    lowerBound τ σ c C ε_F δ₀ K C₁ D_T C_X D_X ≥
      (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * (14 * τ / (1 - σ))) := by
  have h1 := lowerBound_M_ge_epsF τ σ c C ε_F δ₀ C₁ D_T C_X D_X
  exact le_trans h1 (lowerBound_ge_M _ _ _ _ _ _ _ _ _ _ _)

lemma lowerBound_ge_conc9 (τ σ c C ε_F δ₀ K C₁ D_T C_X D_X : ℝ) :
    lowerBound τ σ c C ε_F δ₀ K C₁ D_T C_X D_X ≥
      Real.log (390 * K * C * C₁^σ) / (2 * τ * Real.log 2) := by
  let LM := lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X
  let lbE := Real.log (390 * K * C * C₁^σ) / (2 * τ * Real.log 2)
  have h : lowerBound τ σ c C ε_F δ₀ K C₁ D_T C_X D_X = max LM lbE := by rfl
  rw [h]
  exact le_max_right LM lbE

lemma lowerBound_ge_conc11 (τ σ c C ε_F δ₀ K C₁ D_T C_X D_X : ℝ) :
    lowerBound τ σ c C ε_F δ₀ K C₁ D_T C_X D_X ≥
      1 + Real.log (C_X * D_X) / (ε_F * Real.log 2) := by
  have h1 := lowerBound_M_ge_CXDX τ σ c C ε_F δ₀ C₁ D_T C_X D_X
  exact le_trans h1 (lowerBound_ge_M _ _ _ _ _ _ _ _ _ _ _)

/-- Constraint 11: C_X*D_X ≤ (2*2^(-N))^(-ε_F). -/
lemma conc11_bound (N ε_F C_X D_X : ℝ) (hεF_pos : 0 < ε_F)
    (hC_X_pos : 0 < C_X) (hD_X_pos : 0 < D_X)
    (hN_gt : N > 1 + Real.log (C_X * D_X) / (ε_F * Real.log 2)) :
    C_X * D_X ≤ (2 * (2 : ℝ)^(-N))^(-ε_F) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2r : 2 * (2 : ℝ)^(-N) = (2 : ℝ)^(1 - N) := by
    have h3 : (2 : ℝ)^(1 - N) = (2 : ℝ)^(1 : ℝ) * (2 : ℝ)^(-N) := by
      rw [← Real.rpow_add (by norm_num)] <;> ring_nf
    rw [h3] <;> simp
  rw [h2r]
  have h4 : ((2 : ℝ)^(1 - N))^(-ε_F) = (2 : ℝ)^(ε_F * (N - 1)) := by
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ 2 from by norm_num)] <;> ring_nf
  rw [h4]
  have h_pos : 0 < C_X * D_X := mul_pos hC_X_pos hD_X_pos
  have h1 : ε_F * (N - 1) * Real.log 2 > Real.log (C_X * D_X) := by
    have h2 : N - 1 > Real.log (C_X * D_X) / (ε_F * Real.log 2) := by linarith [hN_gt]
    have h3 : 0 < ε_F * Real.log 2 := by positivity
    calc ε_F * (N - 1) * Real.log 2
      = (N - 1) * (ε_F * Real.log 2) := by ring
    _ > (Real.log (C_X * D_X) / (ε_F * Real.log 2)) * (ε_F * Real.log 2) := by gcongr
    _ = Real.log (C_X * D_X) := by field_simp [h3.ne'] <;> ring
  have h6 : (2 : ℝ)^(ε_F * (N - 1)) > C_X * D_X := by
    have h7 : Real.log ((2 : ℝ)^(ε_F * (N - 1))) = ε_F * (N - 1) * Real.log 2 := by
      rw [Real.log_rpow (by norm_num)] <;> ring
    have h8 : Real.log ((2 : ℝ)^(ε_F * (N - 1))) > Real.log (C_X * D_X) := by
      rw [h7]; exact h1
    have h_pos2 : 0 < (2 : ℝ)^(ε_F * (N - 1)) := by positivity
    have h8' : Real.log (C_X * D_X) < Real.log ((2 : ℝ)^(ε_F * (N - 1))) := h8
    exact (Real.log_lt_log_iff h_pos h_pos2).mp h8'
  exact le_of_lt h6

/-- Proves the hN_ok condition for the main theorem's fixed parameter values
    (ε_F=10, δ₀=1, C₁=D_T=C_X=D_X=1), given M is sufficiently large. -/
lemma hN_ok_holds (τ σ c C M : ℝ)
    (hτ : 0 < τ) (hτ_lt_01 : τ < 1 / 100)
    (hσ_pos : 0 < σ) (hσ_lt_one : σ < 1)
    (hτ_small : τ < (1 - σ) / 14)
    (hc : c ∈ Set.Ioo (0 : ℝ) (1 / 10))
    (hC : 1 ≤ C)
    (hM_gt2s : M > 2 * (σ + τ) / τ)
    (hM_gt400 : M > 400 / τ^2) :
    lowerBound_M τ σ c C (10 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ) + 3 <
      M * Real.log (C ^ 2 * M / c) / ((σ + τ) * Real.log 2) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt_one : Real.log 2 < 1 := by
    have h : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h' : Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by positivity) h
    rw [Real.log_exp] at h'; exact h'
  have hlog2_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
    have h1 : Real.exp (1 / 2 : ℝ) < 2 := by
      have h2 : Real.exp 1 < 3 := Real.exp_one_lt_three
      have h_pos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
      have h3 : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
        have h4 : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
          rw [← Real.exp_add] <;> norm_num
        have h5 : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) := by ring
        rw [h5]
        exact h4
      nlinarith [h2, h3, h_pos]
    have h4 : Real.log (Real.exp (1 / 2 : ℝ)) = (1 / 2 : ℝ) := Real.log_exp _
    have h5 : Real.log (Real.exp (1 / 2 : ℝ)) < Real.log 2 := Real.log_lt_log (by positivity) h1
    rw [h4] at h5; exact h5
  have h1mσ_pos : 0 < 1 - σ := by
    have h : 0 < τ := hτ
    have h' : τ < (1 - σ) / 14 := hτ_small
    have h'' : 0 < (1 - σ) / 14 := by linarith
    linarith
  have hσ_lt_one : σ < 1 := by linarith [h1mσ_pos]
  have hστ_pos : 0 < σ + τ := by linarith [hσ_pos, hτ]
  have hστ_lt_one : σ + τ < 1 := by
    have h1 : σ + τ < σ + (1 - σ) / 14 := by linarith [hτ_small]
    have h2 : σ + (1 - σ) / 14 < 1 := by
      have h3 : 0 < 1 - σ := h1mσ_pos
      nlinarith
    linarith
  have hc_pos : 0 < c := hc.1
  have h_neg_log_c_pos : 0 < -Real.log c := by
    have h1 : c < 1 := by linarith [hc.2]
    have h2 : Real.log c < 0 := Real.log_neg hc_pos h1
    linarith
  have hM_pos : 0 < M := by
    have h1 : (0 : ℝ) < 400 / τ^2 := by positivity
    linarith [hM_gt400]
  -- b = 1 - 2^(-τ) > τ/4
  set x : ℝ := τ * Real.log 2 with hx_def
  have hx_pos : 0 < x := by positivity
  have hx_lt_one : x < 1 := by
    have h1 : τ < 1 / 100 := hτ_lt_01
    nlinarith [hlog2_lt_one]
  have h_exp_le : Real.exp (-x) ≤ 1 - x / 2 := by
    have h1 : 0 < 1 + x := by linarith
    have h2 : Real.exp x ≥ 1 + x := by linarith [Real.add_one_le_exp x]
    have h3 : Real.exp (-x) = (Real.exp x)⁻¹ := by rw [Real.exp_neg]
    rw [h3]
    have h4 : (Real.exp x)⁻¹ ≤ (1 + x)⁻¹ := by gcongr
    have h6 : 1 ≤ (1 + x) * (1 - x / 2) := by nlinarith
    have h5 : (1 + x)⁻¹ ≤ 1 - x / 2 := by
      calc (1 + x)⁻¹
        = (1 + x)⁻¹ * 1 := by ring
      _ ≤ (1 + x)⁻¹ * ((1 + x) * (1 - x / 2)) := by gcongr
      _ = 1 - x / 2 := by field_simp [h1.ne'] <;> ring
    exact le_trans h4 h5
  set b : ℝ := 1 - (2 : ℝ)^(-τ) with hb_def
  have hb_gt_tau4 : b > τ / 4 := by
    have h9 : (2 : ℝ)^(-τ) = Real.exp (-x) := by
      rw [Real.rpow_def_of_pos (by norm_num)] <;> simp [hx_def] <;> ring
    have h10 : b = 1 - Real.exp (-x) := by simp [hb_def, h9]
    rw [h10]
    have h11 : x / 2 > τ / 4 := by
      simp only [hx_def]
      have h13 : (1 / 2 : ℝ) < Real.log 2 := hlog2_gt_half
      nlinarith
    have h12 : 1 - Real.exp (-x) ≥ x / 2 := by
      have h13 : Real.exp (-x) ≤ 1 - x / 2 := h_exp_le
      linarith
    have h14 : 1 - Real.exp (-x) > τ / 4 := by
      calc 1 - Real.exp (-x) ≥ x / 2 := h12
        _ > τ / 4 := h11
    exact h14
  have hb_pos : 0 < b := by linarith [hb_gt_tau4]
  have hb_lt_one : b < 1 := by
    simp [hb_def]
    have h5 : (0 : ℝ) < τ := hτ
    have h6 : (2 : ℝ)^(-τ) > 0 := by positivity
    nlinarith
  -- κ = 14τ/(1-σ) < 1
  set κ : ℝ := 14 * τ / (1 - σ) with hκ_def
  have hκ_lt_one : κ < 1 := by
    have h1 : 14 * τ < 1 - σ := by
      calc 14 * τ < 14 * ((1 - σ) / 14) := by gcongr
        _ = 1 - σ := by field_simp [h1mσ_pos.ne'] <;> ring
    rw [hκ_def]
    have h2 : 14 * τ / (1 - σ) < 1 := by
      apply (div_lt_one h1mσ_pos).mpr
      exact h1
    exact h2
  -- Expand L
  set L : ℝ := lowerBound_M τ σ c C (10 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ) with hL_def
  set c0 : ℝ := Real.log (2 / (c * b)) / (τ * Real.log 2) with hc0_def
  set c1 : ℝ := 400 / (τ^2 * Real.log 2) with hc1_def
  set c2 : ℝ := Real.log (20 * C) / (τ * Real.log 2) with hc2_def
  set c4 : ℝ := (2 * σ + (10 : ℝ) + Real.log 80000 / Real.log 2) / ((10 : ℝ) - 8 * τ - 3 * κ) with hc4_def
  set c5 : ℝ := Real.log (390 * C) / (τ * Real.log 2) with hc5_def
  have hL_expand : L = max c0 (max c1 (max c2 (max 1 (max c4 (max c5 1))))) := by
    simp [hL_def, lowerBound_M, c0, c1, c2, c4, c5, b, κ, Real.log_one]
    <;> norm_num <;> ring
  -- Component bounds
  have hc2_le_c5 : c2 ≤ c5 := by
    simp only [c2, c5]
    gcongr <;> norm_num <;> linarith [hC]
  have hden_gt6 : (10 : ℝ) - 8 * τ - 3 * κ > 6 := by
    have h1 : κ < 1 := hκ_lt_one
    have h2 : 8 * τ < 1 := by linarith [hτ_lt_01]
    nlinarith
  have hc4_lt5 : c4 < 5 := by
    have hden_pos : 0 < (10 : ℝ) - 8 * τ - 3 * κ := by linarith
    have hnum_lt30 : 2 * σ + (10 : ℝ) + Real.log 80000 / Real.log 2 < 30 := by
      have hσ_lt1 : σ < 1 := hσ_lt_one
      have hlog80000_lt17 : Real.log 80000 / Real.log 2 < 17 := by
        have h1 : (80000 : ℝ) < (2 : ℝ)^17 := by norm_num
        have h2 : Real.log 80000 < Real.log ((2 : ℝ)^17) := Real.log_lt_log (by positivity) h1
        have h3 : Real.log ((2 : ℝ)^17) = 17 * Real.log 2 := by rw [Real.log_pow] <;> ring
        rw [h3] at h2
        have h4 : Real.log 80000 / Real.log 2 < (17 * Real.log 2) / Real.log 2 := by gcongr
        have h5 : (17 * Real.log 2) / Real.log 2 = 17 := by
          field_simp [hlog2_pos.ne'] <;> ring
        rw [h5] at h4
        exact h4
      have h6 : 2 * σ < 2 := by linarith
      linarith
    have h : c4 < 30 / 6 := by
      simp only [c4]
      have hden_pos' : 0 < (10 : ℝ) - 8 * τ - 3 * κ := hden_pos
      have h' : c4 * ((10 : ℝ) - 8 * τ - 3 * κ) < 30 := by
        have h_eq : c4 * ((10 : ℝ) - 8 * τ - 3 * κ) = 2 * σ + (10 : ℝ) + Real.log 80000 / Real.log 2 := by
          simp only [c4]
          field_simp [hden_pos.ne'] <;> ring
        rw [h_eq]
        exact hnum_lt30
      have h'' : c4 < 30 / 6 := by
        calc c4
          = c4 * ((10 : ℝ) - 8 * τ - 3 * κ) / ((10 : ℝ) - 8 * τ - 3 * κ) := by field_simp [hden_pos'.ne'] <;> ring
        _ < 30 / ((10 : ℝ) - 8 * τ - 3 * κ) := by gcongr
        _ < 30 / 6 := by gcongr
      exact h''
    norm_num at h
    exact h
  -- Nonnegativity
  have hc0_nonneg : 0 ≤ c0 := by
    have h1 : c * b < 2 := by
      have h2 : c < 1 / 10 := hc.2
      have h3 : b < 1 := hb_lt_one
      nlinarith
    have h4 : 2 / (c * b) ≥ 1 := by
      have h5 : 0 < c * b := by positivity
      have h6 : c * b ≤ 2 := by linarith
      exact (one_le_div h5).mpr h6
    have h7 : 0 ≤ Real.log (2 / (c * b)) := Real.log_nonneg h4
    simp only [c0]; positivity
  have hc1_nonneg : 0 ≤ c1 := by positivity
  have hc5_nonneg : 0 ≤ c5 := by
    have h1 : 390 * C ≥ 1 := by nlinarith [hC]
    have h2 : 0 ≤ Real.log (390 * C) := Real.log_nonneg h1
    simp only [c5]; positivity
  -- L ≤ c0 + c1 + c5 + 5
  have hL_le : L ≤ c0 + c1 + c5 + 5 := by
    rw [hL_expand]
    have hc0' : c0 ≤ c0 + c1 + c5 + 5 := by linarith
    have hc1' : c1 ≤ c0 + c1 + c5 + 5 := by linarith
    have hc2' : c2 ≤ c0 + c1 + c5 + 5 := by linarith [hc2_le_c5]
    have h1' : (1 : ℝ) ≤ c0 + c1 + c5 + 5 := by linarith
    have hc4' : c4 ≤ c0 + c1 + c5 + 5 := by linarith [hc4_lt5]
    have hc5' : c5 ≤ c0 + c1 + c5 + 5 := by linarith
    have h1'' : (1 : ℝ) ≤ c0 + c1 + c5 + 5 := by linarith
    exact max_le hc0' (max_le hc1' (max_le hc2' (max_le h1' (max_le hc4' (max_le hc5' h1'')))))
  -- Bound c0
  have hc0_bound : c0 ≤ (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) := by
    have h1 : 2 / (c * b) ≤ 8 / (c * τ) := by
      have h2 : b > τ / 4 := hb_gt_tau4
      have h3 : c * b > c * (τ / 4) := by gcongr
      have h4 : 0 < c * b := by positivity
      have h5 : 0 < c * (τ / 4) := by positivity
      have h6 : 2 / (c * b) < 2 / (c * (τ / 4)) := by
        exact div_lt_div_of_pos_left (by norm_num) h5 h3
      have h7 : 2 / (c * (τ / 4)) = 8 / (c * τ) := by
        field_simp [hc_pos.ne', hτ.ne'] <;> ring
      rw [h7] at h6
      exact h6.le
    have h6 : Real.log (2 / (c * b)) ≤ Real.log (8 / (c * τ)) := Real.log_le_log (by positivity) h1
    have h7 : Real.log (8 / (c * τ)) = Real.log (8 / τ) - Real.log c := by
      have h8 : (8 / (c * τ)) = (8 / τ) / c := by field_simp [hc_pos.ne', hτ.ne'] <;> ring
      rw [h8, Real.log_div (by positivity) (ne_of_gt hc_pos)] <;> ring
    rw [h7] at h6
    simp only [c0]; gcongr
  -- Bound c5
  have hc5_bound : c5 ≤ (Real.log 390 + Real.log C) / (τ * Real.log 2) := by
    have h1 : Real.log (390 * C) = Real.log 390 + Real.log C := by
      rw [Real.log_mul (by positivity) (by linarith)] <;> ring
    simp only [c5]; rw [h1] <;> ring
  -- RHS expansion
  set RHS : ℝ := M * Real.log (C ^ 2 * M / c) / ((σ + τ) * Real.log 2) with hRHS_def
  have hRHS_expand : Real.log (C ^ 2 * M / c) = 2 * Real.log C + Real.log M - Real.log c := by
    have h_pos1 : 0 < C ^ 2 * M := by positivity
    have h4 : Real.log (C ^ 2 * M / c) = Real.log (C ^ 2 * M) - Real.log c := by
      rw [Real.log_div (ne_of_gt h_pos1) (ne_of_gt hc_pos)] <;> ring
    rw [h4]
    have h5 : Real.log (C ^ 2 * M) = Real.log (C ^ 2) + Real.log M := by
      rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt hM_pos)] <;> ring
    rw [h5]
    have h6 : Real.log (C ^ 2) = 2 * Real.log C := by rw [Real.log_pow] <;> ring
    rw [h6] <;> ring
  have hRHS_split : RHS =
      M * (2 * Real.log C) / ((σ + τ) * Real.log 2) +
      M * Real.log M / ((σ + τ) * Real.log 2) +
      M * (-Real.log c) / ((σ + τ) * Real.log 2) := by
    rw [hRHS_def, hRHS_expand] <;> ring
  have hM_div_gt : M / (σ + τ) > 2 / τ := by
    have h : M > 2 * (σ + τ) / τ := hM_gt2s
    calc M / (σ + τ) > (2 * (σ + τ) / τ) / (σ + τ) := by gcongr
      _ = 2 / τ := by field_simp [hστ_pos.ne'] <;> ring
  -- Term c domination
  have h_part_c : M * (-Real.log c) / ((σ + τ) * Real.log 2) > (-Real.log c) / (τ * Real.log 2) := by
    have h1 : M / ((σ + τ) * Real.log 2) > 1 / (τ * Real.log 2) := by
      have h2 : M / (σ + τ) > 2 / τ := hM_div_gt
      have h3 : M / ((σ + τ) * Real.log 2) = (M / (σ + τ)) / Real.log 2 := by
        field_simp [hστ_pos.ne', hlog2_pos.ne'] <;> ring
      rw [h3]
      have h4 : (M / (σ + τ)) / Real.log 2 > (2 / τ) / Real.log 2 := by gcongr
      have h5 : (2 / τ) / Real.log 2 = 2 / (τ * Real.log 2) := by
        field_simp [hτ.ne', hlog2_pos.ne'] <;> ring
      have h6 : (M / (σ + τ)) / Real.log 2 > 2 / (τ * Real.log 2) := by
        calc (M / (σ + τ)) / Real.log 2
          > (2 / τ) / Real.log 2 := h4
        _ = 2 / (τ * Real.log 2) := h5
      have h7 : (2 : ℝ) / (τ * Real.log 2) > 1 / (τ * Real.log 2) := by
        apply div_lt_div_of_pos_right
        · norm_num
        · positivity
      exact lt_trans h7 h6
    have h4 : 0 < -Real.log c := h_neg_log_c_pos
    have h5 : M * (-Real.log c) / ((σ + τ) * Real.log 2) =
        (M / ((σ + τ) * Real.log 2)) * (-Real.log c) := by ring
    rw [h5]
    have h6 : (M / ((σ + τ) * Real.log 2)) * (-Real.log c) >
        (1 / (τ * Real.log 2)) * (-Real.log c) := by
      exact mul_lt_mul_of_pos_right h1 h4
    have h7 : (1 / (τ * Real.log 2)) * (-Real.log c) = (-Real.log c) / (τ * Real.log 2) := by ring
    rw [h7] at h6
    exact h6
  -- Term C domination
  have h_part_C : M * (2 * Real.log C) / ((σ + τ) * Real.log 2) ≥ Real.log C / (τ * Real.log 2) := by
    have h_logC_nonneg : 0 ≤ Real.log C := Real.log_nonneg (by linarith)
    have h1 : M / (σ + τ) > 2 / τ := hM_div_gt
    have h2 : M * (2 * Real.log C) / ((σ + τ) * Real.log 2) =
        (M / (σ + τ)) * (2 * Real.log C) / Real.log 2 := by
      field_simp [hστ_pos.ne', hlog2_pos.ne'] <;> ring
    rw [h2]
    have h3 : (M / (σ + τ)) * (2 * Real.log C) / Real.log 2 ≥
        (2 / τ) * (2 * Real.log C) / Real.log 2 := by
      have h4' : (M / (σ + τ)) * (2 * Real.log C) ≥ (2 / τ) * (2 * Real.log C) := by
        have h5 : M / (σ + τ) > 2 / τ := h1
        have h6 : 0 ≤ 2 * Real.log C := by positivity
        exact mul_le_mul_of_nonneg_right h5.le h6
      exact div_le_div_of_nonneg_right h4' (by positivity)
    have h4 : (2 / τ) * (2 * Real.log C) / Real.log 2 = 4 * Real.log C / (τ * Real.log 2) := by
      field_simp [hτ.ne', hlog2_pos.ne'] <;> ring
    rw [h4] at h3
    have h5 : 4 * Real.log C / (τ * Real.log 2) ≥ Real.log C / (τ * Real.log 2) := by
      have h6 : 0 ≤ Real.log C := h_logC_nonneg
      have h7 : 4 * Real.log C ≥ Real.log C := by
        have h71 : 0 ≤ Real.log C := h_logC_nonneg
        linarith
      have h8 : 0 < τ * Real.log 2 := by positivity
      exact div_le_div_of_nonneg_right h7 (by positivity)
    exact le_trans h5 h3
  -- Term M domination (simplified)
  have hlogM_gt13 : Real.log M > 13 := by
    have h2 : τ^2 < 1 / 10000 := by
      have h21 : τ^2 < (1 / 100 : ℝ)^2 := by gcongr
      have h22 : (1 / 100 : ℝ)^2 = 1 / 10000 := by norm_num
      rw [h22] at h21; exact h21
    have h3 : 400 / τ^2 > (4000000 : ℝ) := by
      have h4 : 400 / τ^2 > 400 / (1 / 10000 : ℝ) := by gcongr
      have h5 : 400 / (1 / 10000 : ℝ) = 4000000 := by norm_num
      rw [h5] at h4; exact h4
    have h4 : M > (4000000 : ℝ) := by linarith [hM_gt400]
    have h5 : (4000000 : ℝ) > Real.exp 13 := by
      have h6 : Real.exp 1 < 3 := Real.exp_one_lt_three
      have h7 : Real.exp 13 = (Real.exp 1)^(13 : ℝ) := by
        have h71 := Real.exp_mul (1 : ℝ) (13 : ℝ)
        norm_num at h71 ⊢
      have h8 : (Real.exp 1)^(13 : ℝ) < (3 : ℝ)^(13 : ℝ) := by gcongr <;> linarith
      have h9 : (3 : ℝ)^(13 : ℝ) = (3 : ℝ)^13 := by norm_cast
      rw [h9] at h8
      norm_num at h8 ⊢ <;> linarith
    have h10 : Real.log M > Real.log (Real.exp 13) := Real.log_lt_log (by positivity) (by linarith)
    have h11 : Real.log (Real.exp 13) = 13 := Real.log_exp 13
    rw [h11] at h10; exact h10
  have h_part_M : M * Real.log M / ((σ + τ) * Real.log 2) >
      Real.log (8 / τ) / (τ * Real.log 2) + 400 / (τ^2 * Real.log 2) + Real.log 390 / (τ * Real.log 2) + 8 := by
    have h_pos_logM : 0 < Real.log M := by linarith [hlogM_gt13]
    have h1 : M * Real.log M / ((σ + τ) * Real.log 2) > M * Real.log M / Real.log 2 := by
      have h_pos : 0 < M * Real.log M := by positivity
      have h_den : (σ + τ) * Real.log 2 < Real.log 2 := by
        have h : σ + τ < 1 := hστ_lt_one
        have h2 : 0 < Real.log 2 := hlog2_pos
        have h3 : (σ + τ) * Real.log 2 < 1 * Real.log 2 := by
          exact mul_lt_mul_of_pos_right h h2
        simpa using h3
      have h : M * Real.log M / Real.log 2 < M * Real.log M / ((σ + τ) * Real.log 2) := by
        have h4 : 0 < (σ + τ) * Real.log 2 := by positivity
        exact div_lt_div_of_pos_left h_pos h4 h_den
      exact h
    have h2 : M * Real.log M / Real.log 2 ≥ (400 / τ^2) * Real.log M / Real.log 2 := by
      have h_pos : 0 < Real.log M := h_pos_logM
      have h : M ≥ 400 / τ^2 := by linarith [hM_gt400]
      gcongr
    have h3 : (400 / τ^2) * Real.log M / Real.log 2 > (400 / τ^2) * (13 : ℝ) / Real.log 2 := by
      have h_pos : 0 < 400 / τ^2 := by positivity
      gcongr <;> linarith [hlogM_gt13]
    have h4 : Real.log (8 / τ) < 8 / τ := by
      have h5 : 0 < 8 / τ := by positivity
      have h6 : Real.log (8 / τ) ≤ (8 / τ) - 1 := Real.log_le_sub_one_of_pos h5
      linarith
    have h5 : Real.log 390 < 390 := by
      have h6 : Real.log 390 ≤ 390 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      linarith
    have h6 : τ^2 * Real.log 2 < 1 := by
      have h7 : τ^2 < 1 / 10000 := by
        have h71 : τ^2 < (1 / 100 : ℝ)^2 := by gcongr
        have h72 : (1 / 100 : ℝ)^2 = 1 / 10000 := by norm_num
        rw [h72] at h71; exact h71
      have h8 : 0 ≤ τ^2 := by positivity
      have h9 : Real.log 2 < 1 := hlog2_lt_one
      have h10 : τ^2 * Real.log 2 ≤ τ^2 := by
        have h9' : Real.log 2 ≤ 1 := by linarith [hlog2_lt_one]
        exact mul_le_of_le_one_right h8 h9'
      linarith
    have h7 : Real.log (8 / τ) / (τ * Real.log 2) < 8 / (τ^2 * Real.log 2) := by
      have h9 : Real.log (8 / τ) < 8 / τ := h4
      have h10 : τ^2 ≤ τ := by nlinarith [hτ_lt_01]
      have h11 : Real.log (8 / τ) / (τ * Real.log 2) < (8 / τ) / (τ * Real.log 2) := by gcongr
      have h12 : (8 / τ) / (τ * Real.log 2) = 8 / (τ^2 * Real.log 2) := by
        field_simp [hτ.ne', hlog2_pos.ne'] <;> ring
      rw [h12] at h11
      exact h11
    have h8 : Real.log 390 / (τ * Real.log 2) < 390 / (τ^2 * Real.log 2) := by
      have h9 : Real.log 390 < 390 := h5
      have h10 : Real.log 390 / (τ * Real.log 2) < 390 / (τ * Real.log 2) := by gcongr
      have h11 : τ^2 < τ := by nlinarith [hτ_lt_01]
      have h12 : τ^2 * Real.log 2 < τ * Real.log 2 := by
        exact mul_lt_mul_of_pos_right h11 hlog2_pos
      have h13 : 390 / (τ * Real.log 2) < 390 / (τ^2 * Real.log 2) := by
        have h_pos390 : (0 : ℝ) < 390 := by norm_num
        have h_den_pos2 : 0 < τ^2 * Real.log 2 := by positivity
        exact div_lt_div_of_pos_left h_pos390 h_den_pos2 h12
      exact lt_trans h10 h13
    have h9 : 8 < 8 / (τ^2 * Real.log 2) := by
      have h10 : 0 < τ^2 * Real.log 2 := by positivity
      have h11 : τ^2 * Real.log 2 < 1 := h6
      have h12 : 8 / (τ^2 * Real.log 2) > 8 / 1 := by
        have h_pos8 : (0 : ℝ) < 8 := by norm_num
        have h_den_small : 0 < τ^2 * Real.log 2 := by positivity
        exact div_lt_div_of_pos_left h_pos8 h_den_small h11
      simpa using h12
    have h_pos_den : 0 < τ^2 * Real.log 2 := by positivity
    have h13a : Real.log (8 / τ) / (τ * Real.log 2) + 400 / (τ^2 * Real.log 2) + Real.log 390 / (τ * Real.log 2) + 8 <
        8 / (τ^2 * Real.log 2) + 400 / (τ^2 * Real.log 2) + 390 / (τ^2 * Real.log 2) + 8 / (τ^2 * Real.log 2) := by
      gcongr
    have h13b : 8 / (τ^2 * Real.log 2) + 400 / (τ^2 * Real.log 2) + 390 / (τ^2 * Real.log 2) + 8 / (τ^2 * Real.log 2) =
        (8 + 400 + 390 + 8) / (τ^2 * Real.log 2) := by
      field_simp [h_pos_den.ne'] <;> ring
    have h13 : Real.log (8 / τ) / (τ * Real.log 2) + 400 / (τ^2 * Real.log 2) + Real.log 390 / (τ * Real.log 2) + 8 <
        (8 + 400 + 390 + 8) / (τ^2 * Real.log 2) := by
      calc Real.log (8 / τ) / (τ * Real.log 2) + 400 / (τ^2 * Real.log 2) + Real.log 390 / (τ * Real.log 2) + 8
        < 8 / (τ^2 * Real.log 2) + 400 / (τ^2 * Real.log 2) + 390 / (τ^2 * Real.log 2) + 8 / (τ^2 * Real.log 2) := h13a
      _ = (8 + 400 + 390 + 8) / (τ^2 * Real.log 2) := h13b
    have h14 : (8 + 400 + 390 + 8 : ℝ) / (τ^2 * Real.log 2) < (400 / τ^2) * (13 : ℝ) / Real.log 2 := by
      have h15 : (400 / τ^2) * (13 : ℝ) / Real.log 2 = (400 * 13 : ℝ) / (τ^2 * Real.log 2) := by
        field_simp [hτ.ne', hlog2_pos.ne'] <;> ring
      rw [h15]
      have h16 : (8 + 400 + 390 + 8 : ℝ) < (400 * 13 : ℝ) := by norm_num
      have h17 : 0 < τ^2 * Real.log 2 := by positivity
      exact div_lt_div_of_pos_right h16 h17
    calc M * Real.log M / ((σ + τ) * Real.log 2)
      > M * Real.log M / Real.log 2 := h1
    _ ≥ (400 / τ^2) * Real.log M / Real.log 2 := h2
    _ > (400 / τ^2) * (13 : ℝ) / Real.log 2 := h3
    _ > (8 + 400 + 390 + 8 : ℝ) / (τ^2 * Real.log 2) := h14
    _ > Real.log (8 / τ) / (τ * Real.log 2) + 400 / (τ^2 * Real.log 2) + Real.log 390 / (τ * Real.log 2) + 8 := h13
  -- Final assembly
  have hL_le2 : L + 3 ≤ (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) +
      400 / (τ^2 * Real.log 2) +
      (Real.log 390 + Real.log C) / (τ * Real.log 2) + 8 := by
    calc L + 3
      ≤ c0 + c1 + c5 + 5 + 3 := by linarith [hL_le]
    _ = c0 + c1 + c5 + 8 := by ring
    _ ≤ (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) + 400 / (τ^2 * Real.log 2) + (Real.log 390 + Real.log C) / (τ * Real.log 2) + 8 := by
      have h1 : c0 ≤ (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) := hc0_bound
      have h2 : c1 = 400 / (τ^2 * Real.log 2) := by simp [c1]
      have h3 : c5 ≤ (Real.log 390 + Real.log C) / (τ * Real.log 2) := hc5_bound
      rw [h2]
      linarith
  rw [hRHS_split]
  have h_final : (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) +
      400 / (τ^2 * Real.log 2) +
      (Real.log 390 + Real.log C) / (τ * Real.log 2) + 8 <
      M * (2 * Real.log C) / ((σ + τ) * Real.log 2) +
      M * Real.log M / ((σ + τ) * Real.log 2) +
      M * (-Real.log c) / ((σ + τ) * Real.log 2) := by
    have h1 : (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) =
        Real.log (8 / τ) / (τ * Real.log 2) + (-Real.log c) / (τ * Real.log 2) := by
      field_simp [hτ.ne', hlog2_pos.ne'] <;> ring
    have h2 : (Real.log 390 + Real.log C) / (τ * Real.log 2) =
        Real.log 390 / (τ * Real.log 2) + Real.log C / (τ * Real.log 2) := by
      field_simp [hτ.ne', hlog2_pos.ne'] <;> ring
    rw [h1, h2]
    linarith [h_part_c, h_part_C, h_part_M]
  exact lt_of_le_of_lt hL_le2 h_final

/-- Case 1 of r0-large inequality: r0 = K^(-1/τ), so K ≥ 2^(τN). -/
lemma r0_large_case1 (σ τ K M N K' : ℝ) (hτ : 0 < τ) (hK : 1 ≤ K)
    (hσ_pos : 0 < σ) (hM_gt2s : M > 2 * (σ + τ) / τ)
    (hK'_ge_K : K' ≥ K ^ M) (hN_ge1 : 1 ≤ N)
    (hK_ge : K ≥ (2 : ℝ) ^ (τ * N)) :
    (2 : ℝ) ^ (σ + τ) < K' * (K ^ (-(1 / τ))) ^ (σ + τ) := by
  have h_pos_st : 0 < (σ + τ) / τ := by positivity
  have hM_gt2s' : M > 2 * ((σ + τ) / τ) := by
    have h_eq : 2 * (σ + τ) / τ = 2 * ((σ + τ) / τ) := by ring
    rw [h_eq] at hM_gt2s; exact hM_gt2s
  have h_half_pos : 0 < M - (σ + τ) / τ := by
    have h : M > 2 * ((σ + τ) / τ) := hM_gt2s'
    have h2 : 2 * ((σ + τ) / τ) > (σ + τ) / τ := by
      have h3 : (1 : ℝ) < 2 := by norm_num
      linarith [h_pos_st]
    linarith
  have h14 : 0 ≤ M - (σ + τ) / τ := by linarith
  have h19 : M - (σ + τ) / τ > (σ + τ) / τ := by linarith
  have h17 : τ * N * (M - (σ + τ) / τ) > σ + τ := by
    have h20 : N * (M - (σ + τ) / τ) ≥ M - (σ + τ) / τ := by
      calc N * (M - (σ + τ) / τ)
        ≥ 1 * (M - (σ + τ) / τ) := by gcongr
      _ = M - (σ + τ) / τ := by ring
    have h21 : τ * N * (M - (σ + τ) / τ) ≥ τ * (M - (σ + τ) / τ) := by
      have h21a : N ≥ 1 := hN_ge1
      have h21b : 0 ≤ M - (σ + τ) / τ := h14
      have h : N * (M - (σ + τ) / τ) ≥ 1 * (M - (σ + τ) / τ) :=
        mul_le_mul_of_nonneg_right h21a h21b
      have h' : τ * (N * (M - (σ + τ) / τ)) ≥ τ * (1 * (M - (σ + τ) / τ)) :=
        mul_le_mul_of_nonneg_left h (by linarith)
      simpa [mul_assoc] using h'
    have h22 : τ * (M - (σ + τ) / τ) > σ + τ := by
      have h23 : τ * (M - (σ + τ) / τ) > τ * ((σ + τ) / τ) := mul_lt_mul_of_pos_left h19 hτ
      have h24 : τ * ((σ + τ) / τ) = σ + τ := by field_simp [hτ.ne'] <;> ring
      rw [h24] at h23; exact h23
    linarith
  have h12 : K ^ (M - (σ + τ) / τ) > (2 : ℝ) ^ (σ + τ) := by
    have h15 : K ^ (M - (σ + τ) / τ) ≥ ((2 : ℝ) ^ (τ * N)) ^ (M - (σ + τ) / τ) :=
      Real.rpow_le_rpow (by positivity) hK_ge h14
    have h16 : ((2 : ℝ) ^ (τ * N)) ^ (M - (σ + τ) / τ) =
        (2 : ℝ) ^ (τ * N * (M - (σ + τ) / τ)) := by
      rw [← Real.rpow_mul (by norm_num)] <;> ring
    rw [h16] at h15
    have h20 : (2 : ℝ) ^ (τ * N * (M - (σ + τ) / τ)) > (2 : ℝ) ^ (σ + τ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h17
    exact lt_of_lt_of_le h20 h15
  have h21 : K' * (K ^ (-(1 / τ))) ^ (σ + τ) ≥ K ^ (M - (σ + τ) / τ) := by
    have h22 : K' ≥ K ^ M := hK'_ge_K
    have h23 : (K ^ (-(1 / τ))) ^ (σ + τ) = K ^ (-(σ + τ) / τ) := by
      rw [← Real.rpow_mul (by linarith)] <;> ring_nf
    rw [h23]
    have h24 : K ^ M * K ^ (-(σ + τ) / τ) = K ^ (M - (σ + τ) / τ) := by
      rw [← Real.rpow_add (by linarith)] <;> ring_nf
    rw [←h24]
    gcongr
  exact lt_of_lt_of_le h12 h21

/-- Variant of `good_params_exist` where `τ` is supplied as a parameter
    rather than constructed as `ε / 100`.

    Requires `τ ≤ ε / 100` in addition to the smallness conditions, because
    the `r2^(1-κ)` bounds need `κ = 14τ/(1-σ) ≤ 14/100`. -/
theorem good_params_exist_with_tau (β ε τ : ℝ) (hβ : 0 < β) (hε : 0 < ε)
    (hτ : 0 < τ) (hτ_lt_01 : τ < 1 / 100)
    (hτ_le_eps100 : τ ≤ ε / 100)
    (hτ_small_all : ∀ σ ∈ Set.Icc β (1 - ε), τ < (1 - σ) / 14) :
    ∃ (M : ℝ) (hM : 1 ≤ M)
      (hM_gt2s : ∀ σ ∈ Set.Icc β (1 - ε), M > 2 * (σ + τ) / τ)
      (hM_gt400 : M > 400 / τ^2),
      ∀ (σ c K C C₁ D_T C_X D_X ε_F δ₀ : ℝ)
        (hσ : σ ∈ Set.Icc β (1 - ε))
        (hc : c ∈ Set.Ioo (0 : ℝ) (1 / 10)) (hK : 1 ≤ K) (hC : 1 ≤ C)
        (hC₁_pos : 0 < C₁) (hD_T_pos : 0 < D_T)
        (hC_X_pos : 0 < C_X) (hD_X_pos : 0 < D_X)
        (hεF_pos : 0 < ε_F) (hδ0_pos : 0 < δ₀)
        (hεF_large : 8 * τ + 4 * (14 * τ / (1 - σ)) < ε_F)
        (hN_ok : lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X + 3 <
          M * Real.log (C ^ 2 * M / c) / ((σ + τ) * Real.log 2)),
        ∃ (r2 : ℝ) (N : ℕ),
          (r2 = (2 : ℝ) ^ (-(N : ℝ))) ∧
          (∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ) < ENNReal.ofReal c) ∧
          (τ < (1 - σ) / 14) ∧
          ((2 : ℝ) ^ (σ + τ) < Real.rpow (max K (C ^ 2 * M / c)) M *
            (chooseR0 K τ r2 hK hτ) ^ (σ + τ)) ∧
          (Real.rpow (max K (C ^ 2 * M / c)) M / (2 : ℝ) ^ (σ + τ) ≥
            2 * (chooseR0 K τ r2 hK hτ) ^ (2 * τ)) ∧
          (r2 ^ τ ≤ 1 / 6) ∧
          (r2 ^ (14 * τ / (1 - σ)) ≤ 1 / 2) ∧
          (r2 ^ (1 - 14 * τ / (1 - σ)) ≤ Real.sqrt 3 / 4) ∧
          (r2 ^ (1 - 14 * τ / (1 - σ)) ≤ 1 / 16) ∧
          (r2 ^ τ * Real.log (1 / r2) ≤ 1 / 100) ∧
          (20 * C * r2 ^ τ < 1) ∧
          (2 * r2 ≤ δ₀) ∧
          ((2 : ℝ) ^ (-(2 * σ + ε_F)) * r2 ^ (-(ε_F - 8 * τ - 2 * (14 * τ / (1 - σ)))) >
            80000 * r2 ^ (-(14 * τ / (1 - σ)))) ∧
          (C_X * D_X ≤ (2 * r2)^(-ε_F)) ∧
          ((N : ℝ) > lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X) := by
  -- Case split: if ε ≥ 1, interval [β, 1-ε] is empty, so vacuous
  by_cases h_eps_lt_one : ε < 1
  · -- Main case: ε < 1
    set a : ℝ := (2 : ℝ) ^ (-τ) with ha_def
    have ha_pos : 0 < a := by positivity
    have ha_lt_one : a < 1 := by
      have h : (2 : ℝ) ^ (-τ) < (2 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      simpa using h
    set b : ℝ := 1 - a with hb_def
    have hb_pos : 0 < b := by linarith [ha_lt_one]

    set S_max : ℝ := (1 - ε + τ) / τ with hS_max_def
    have h1mep : 0 < 1 - ε + τ := by linarith
    have hS_max_pos : 0 < S_max := by
      dsimp only [S_max]; positivity

    have hσ_bound1 : ∀ σ ∈ Set.Icc β (1 - ε), (σ + τ) / τ ≤ S_max := by
      intro σ hσ
      have h1 : σ ≤ 1 - ε := hσ.2
      dsimp only [S_max]; gcongr <;> linarith
    have hσ_bound2 : ∀ σ ∈ Set.Icc β (1 - ε), σ + τ ≤ 1 - ε + τ := by
      intro σ hσ; linarith [hσ.2]
    have hστ_lt_one : ∀ σ ∈ Set.Icc β (1 - ε), σ + τ < 1 := by
      intro σ hσ
      have h1 : σ ≤ 1 - ε := hσ.2
      have h2 : τ < ε / 14 := by
        calc τ ≤ ε / 100 := hτ_le_eps100
          _ < ε / 14 := by gcongr <;> norm_num
      linarith

    have hτ_small : ∀ σ ∈ Set.Icc β (1 - ε), τ < (1 - σ) / 14 := hτ_small_all

    set B : ℝ := S_max * Real.log (20 / b) + 2 * (1 - ε + τ) * Real.log 2 with hB_def
    set M : ℝ := max 1 (max (2 * S_max) (max B (400 / τ^2))) + 1 with hM_def
    have hM_ge1 : 1 ≤ M := by
      dsimp only [M]
      have h : max 1 (max (2 * S_max) (max B (400 / τ^2))) ≥ 1 := le_max_left 1 _
      linarith
    have hM_gt2S : M > 2 * S_max := by
      dsimp only [M]
      have h : max 1 (max (2 * S_max) (max B (400 / τ^2))) ≥ 2 * S_max := by
        have h2 : max (2 * S_max) (max B (400 / τ^2)) ≥ 2 * S_max := le_max_left (2 * S_max) _
        exact le_trans h2 (le_max_right 1 _)
      linarith
    have hM_gtB : M > B := by
      dsimp only [M]
      have h : max 1 (max (2 * S_max) (max B (400 / τ^2))) ≥ B := by
        have h2 : max (2 * S_max) (max B (400 / τ^2)) ≥ max B (400 / τ^2) := le_max_right (2 * S_max) _
        have h3 : max B (400 / τ^2) ≥ B := le_max_left B _
        exact le_trans (le_trans h3 h2) (le_max_right 1 _)
      linarith
    have hM_gt400divt2 : M > 400 / τ^2 := by
      dsimp only [M]
      have h : max 1 (max (2 * S_max) (max B (400 / τ^2))) ≥ 400 / τ^2 := by
        have h2 : max (2 * S_max) (max B (400 / τ^2)) ≥ max B (400 / τ^2) := le_max_right (2 * S_max) _
        have h3 : max B (400 / τ^2) ≥ 400 / τ^2 := le_max_right B _
        exact le_trans (le_trans h3 h2) (le_max_right 1 _)
      linarith

    have h_exp1_lt_10 : Real.exp 1 < (10 : ℝ) := by
      have h : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
      linarith
    have hlog10_gt1 : 1 < Real.log 10 := by
      have h : Real.log (Real.exp 1) < Real.log 10 :=
        Real.log_lt_log (by positivity) h_exp1_lt_10
      have h2 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
      rw [h2] at h; exact h

    have h_key_M : M * Real.log (10 * M) > B := by
      have h1 : 10 * M ≥ 10 := by linarith [hM_ge1]
      have h2 : Real.log (10 * M) ≥ Real.log 10 := Real.log_le_log (by linarith) h1
      have h3 : Real.log (10 * M) > 1 := by linarith [hlog10_gt1]
      have h4 : 0 < M := by linarith
      have h5 : M * Real.log (10 * M) > M := by nlinarith
      linarith [hM_gtB]

    have hM_gt2s_all : ∀ σ ∈ Set.Icc β (1 - ε), M > 2 * (σ + τ) / τ := by
      intro σ hσ
      have h1 : (σ + τ) / τ ≤ S_max := hσ_bound1 σ hσ
      have h2 : 2 * ((σ + τ) / τ) ≤ 2 * S_max := by gcongr
      have h3 : 2 * (σ + τ) / τ = 2 * ((σ + τ) / τ) := by ring
      rw [h3]
      exact lt_of_le_of_lt h2 hM_gt2S
    refine' ⟨M, hM_ge1, hM_gt2s_all, hM_gt400divt2, _⟩
    intro σ c K C C₁ D_T C_X D_X ε_F δ₀ hσ hc hK hC hC₁_pos hD_T_pos hC_X_pos hD_X_pos hεF_pos hδ0_pos hεF_large hN_ok

    set K' : ℝ := Real.rpow (max K (C ^ 2 * M / c)) M with hK'_def
    have hbase_pos : 0 < max K (C ^ 2 * M / c) := by
      have h1 : 0 < K := by linarith
      have h2 : max K (C ^ 2 * M / c) ≥ K := le_max_left _ _
      linarith
    have hK'_pos : 0 < K' := Real.rpow_pos_of_pos hbase_pos M
    have hC2M_pos : 0 < C ^ 2 * M / c := by
      have h1 : 0 < C := by linarith
      have h2 : 0 < M := by linarith
      have h3 : 0 < c := hc.1
      positivity
    have hK'_ge_geom : K' ≥ (C ^ 2 * M / c) ^ M := by
      have h1 : max K (C ^ 2 * M / c) ≥ C ^ 2 * M / c := le_max_right _ _
      have h2 : 0 ≤ C ^ 2 * M / c := by linarith
      have h3 : Real.rpow (max K (C ^ 2 * M / c)) M ≥ Real.rpow (C ^ 2 * M / c) M :=
        Real.rpow_le_rpow h2 h1 (by linarith [hM_ge1])
      simpa [hK'_def] using h3
    have hK'_ge_K : K' ≥ K ^ M := by
      have h1 : max K (C ^ 2 * M / c) ≥ K := le_max_left _ _
      have h2 : 0 ≤ K := by linarith
      have h3 : Real.rpow (max K (C ^ 2 * M / c)) M ≥ Real.rpow K M :=
        Real.rpow_le_rpow h2 h1 (by linarith [hM_ge1])
      simpa [hK'_def] using h3

    let s : ℝ := (σ + τ) / τ
    have hs_le_Smax : s ≤ S_max := hσ_bound1 σ hσ
    have hM_gt2s : M > 2 * s := by linarith [hM_gt2S, hs_le_Smax]

    have hσ_pos : 0 < σ := by linarith [hβ, hσ.1]
    have hB_bound : s * Real.log (20 / b) + 2 * (σ + τ) * Real.log 2 ≤ B := by
      have hlog_pos : 0 ≤ Real.log (20 / b) := by
        have h2 : b < 1 := by
          dsimp only [b, a]
          have h_pos : (0 : ℝ) < (2 : ℝ) ^ (-τ) := by positivity
          linarith
        have h3 : (1 : ℝ) ≤ 20 / b := by
          have h4 : b < 1 := h2
          have h5 : (20 : ℝ) / b > (20 : ℝ) / 1 := by gcongr
          have h6 : (20 : ℝ) / 1 = 20 := by norm_num
          linarith
        exact Real.log_nonneg h3
      have h11 : s * Real.log (20 / b) ≤ S_max * Real.log (20 / b) :=
        mul_le_mul_of_nonneg_right hs_le_Smax hlog_pos
      have h14 : 2 * (σ + τ) * Real.log 2 ≤ 2 * (1 - ε + τ) * Real.log 2 := by
        gcongr <;> linarith [hσ_bound2 σ hσ]
      linarith [hB_def]
    have hK'_key : M * Real.log (10 * M) > s * Real.log (20 / b) + 2 * (σ + τ) * Real.log 2 := by
      linarith [h_key_M, hB_bound]
    have h_log_ineq : (M - s) * Real.log (1 / c) + M * Real.log (C ^ 2 * M) >
        s * Real.log (2 / b) + 2 * (σ + τ) * Real.log 2 :=
      key_log_ineq M s σ τ c b C hM_ge1 hM_gt2s hσ_pos hτ hc.1 hc.2 hb_pos hC hK'_key

    let T : ℝ := Real.log (2 / (c * b)) / (τ * Real.log 2)
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hcb_pos : 0 < c * b := mul_pos hc.1 hb_pos
    have hT_pos : 0 < T := by
      dsimp only [T]
      have h1 : 2 / (c * b) > 1 := by
        have h2 : c * b < 2 := by
          have h3 : c < 1 / 10 := hc.2
          have h4 : b < 1 := by linarith [ha_pos]
          nlinarith
        have h5 : 0 < c * b := hcb_pos
        have h6 : 2 / (c * b) > 2 / 2 := by gcongr
        linarith
      have h7 : 0 < Real.log (2 / (c * b)) := Real.log_pos h1
      positivity

    let L : ℝ := lowerBound τ σ c C ε_F δ₀ K C₁ D_T C_X D_X
    have hL_ge_T : L ≥ T := by
      exact lowerBound_ge_T τ σ c C ε_F δ₀ K C₁ D_T C_X D_X
    have hL_pos : 0 < L := by linarith [hL_ge_T, hT_pos]

    let N : ℕ := ⌊L⌋.toNat + 1
    have h_floor_nonneg : 0 ≤ ⌊L⌋ := Int.floor_nonneg.mpr (by linarith [hL_pos])
    have h_toNat : (⌊L⌋.toNat : ℤ) = ⌊L⌋ := by
      rw [Int.toNat_of_nonneg h_floor_nonneg]
    have hN_eq : (N : ℝ) = (⌊L⌋ : ℝ) + 1 := by
      have h1 : (N : ℤ) = ⌊L⌋ + 1 := by
        simp [N, h_toNat] <;> omega
      exact_mod_cast h1
    have hN_gt_L : (N : ℝ) > L := by
      have h : (N : ℝ) = (⌊L⌋ : ℝ) + 1 := hN_eq
      have h2 : L < (⌊L⌋ : ℝ) + 1 := Int.lt_floor_add_one L
      linarith
    have hN_gt_lowerBound_M : (N : ℝ) > lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X := by
      have h1 : L ≥ lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X := by
        dsimp only [L, lowerBound]
        exact le_max_left _ _
      linarith [hN_gt_L, h1]
    have hN_le_L1 : (N : ℝ) ≤ L + 1 := by
      have h : (N : ℝ) = (⌊L⌋ : ℝ) + 1 := hN_eq
      have h1 : (⌊L⌋ : ℝ) ≤ L := Int.floor_le L
      linarith
    have hN_gt_T : (N : ℝ) > T := by
      calc (N : ℝ) > L := hN_gt_L
        _ ≥ T := hL_ge_T
    have hN_pos' : 0 < N := by
      have h1 : (N : ℝ) > 0 := by linarith [hN_gt_T, hT_pos]
      exact_mod_cast h1

    have h_sum_real : 2 * (2 : ℝ) ^ (-τ * (N : ℝ)) / b < c := by
      have h3 : 0 < τ * Real.log 2 := by positivity
      have h4 : T * (τ * Real.log 2) < (N : ℝ) * (τ * Real.log 2) :=
        mul_lt_mul_of_pos_right hN_gt_T h3
      have h5 : T * (τ * Real.log 2) = Real.log (2 / (c * b)) := by
        dsimp only [T]
        exact div_mul_cancel₀ (Real.log (2 / (c * b))) h3.ne'
      have h1 : τ * (N : ℝ) * Real.log 2 > Real.log (2 / (c * b)) := by
        have h6 : τ * (N : ℝ) * Real.log 2 = (N : ℝ) * (τ * Real.log 2) := by ring
        rw [h6]
        have h7 : Real.log (2 / (c * b)) < (N : ℝ) * (τ * Real.log 2) := by
          calc Real.log (2 / (c * b))
              = T * (τ * Real.log 2) := h5.symm
            _ < (N : ℝ) * (τ * Real.log 2) := h4
        exact h7
      have h_gt : (2 : ℝ) ^ (τ * (N : ℝ)) > 2 / (c * b) := by
        have h6 : Real.log ((2 : ℝ) ^ (τ * (N : ℝ))) = (τ * (N : ℝ)) * Real.log 2 :=
          Real.log_rpow (by norm_num) (τ * (N : ℝ))
        have h7 : Real.log ((2 : ℝ) ^ (τ * (N : ℝ))) > Real.log (2 / (c * b)) := by
          rw [h6]; exact h1
        have h_pos1 : 0 < (2 : ℝ) ^ (τ * (N : ℝ)) := by positivity
        have h_pos2 : 0 < 2 / (c * b) := by positivity
        have h7' : Real.log (2 / (c * b)) < Real.log ((2 : ℝ) ^ (τ * (N : ℝ))) := h7
        exact (Real.log_lt_log_iff h_pos2 h_pos1).mp h7'
      have h8 : (2 : ℝ) ^ (-τ * (N : ℝ)) < c * b / 2 := by
        have h9 : (2 : ℝ) ^ (-τ * (N : ℝ)) = ((2 : ℝ) ^ (τ * (N : ℝ)))⁻¹ := by
          have h10 : (-τ * (N : ℝ)) = -(τ * (N : ℝ)) := by ring
          rw [h10]
          have h11 : (2 : ℝ) ^ (-(τ * (N : ℝ))) = ((2 : ℝ) ^ (τ * (N : ℝ)))⁻¹ := by
            exact Real.rpow_neg (by norm_num) (τ * (N : ℝ))
          exact h11
        rw [h9]
        have h10 : 0 < 2 / (c * b) := by positivity
        have h11 : ((2 : ℝ) ^ (τ * (N : ℝ)))⁻¹ < (2 / (c * b))⁻¹ := by gcongr
        have h12 : (2 / (c * b))⁻¹ = c * b / 2 := by
          field_simp [hcb_pos.ne'] <;> ring
        rw [h12] at h11; exact h11
      have h13 : 2 * (2 : ℝ) ^ (-τ * (N : ℝ)) / b < c := by
        calc 2 * (2 : ℝ) ^ (-τ * (N : ℝ)) / b
            < 2 * (c * b / 2) / b := by gcongr
          _ = c := by field_simp [hb_pos.ne'] <;> ring
      exact h13

    have h_sum : ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ) < ENNReal.ofReal c := by
      rw [geometric_sum_closed_form τ hτ N]
      have h4 : 0 ≤ 2 * (2 : ℝ) ^ (-τ * (N : ℝ)) / (1 - (2 : ℝ) ^ (-τ)) := by positivity
      rw [ENNReal.ofReal_lt_ofReal_iff hc.1]
      have h5 : 1 - (2 : ℝ) ^ (-τ) = b := by
        simp [hb_def, ha_def] <;> ring
      rw [h5]
      exact h_sum_real

    let r2 : ℝ := (2 : ℝ) ^ (-(N : ℝ))
    have hr2_eq : r2 = (2 : ℝ) ^ (-(N : ℝ)) := by rfl
    let r0 : ℝ := chooseR0 K τ r2 hK hτ
    have hr0_def : r0 = min (K ^ (-(1 / τ))) r2 := by
      simp [r0, chooseR0]
    have hr0_pos : 0 < r0 := by
      rw [hr0_def]
      have h1 : 0 < K ^ (-(1 / τ)) := by positivity
      have h2 : 0 < r2 := by positivity
      exact lt_min h1 h2
    have hr0_le_r2 : r0 ≤ r2 := by
      rw [hr0_def]; exact min_le_right _ _

    have hK'_r0_large : (2 : ℝ) ^ (σ + τ) < K' * r0 ^ (σ + τ) := by
      have h3 : 0 < σ + τ := by linarith [hβ, hσ.1]
      by_cases h_case : K ^ (-(1 / τ)) ≤ r2
      · -- Case 1: r0 = K^(-1/τ)
        have hr0_eq : r0 = K ^ (-(1 / τ)) := by
          rw [hr0_def, min_eq_left h_case]
        rw [hr0_eq]
        have hK_ge : K ≥ (2 : ℝ) ^ (τ * (N : ℝ)) := by
          have h1 : K ^ (-(1 / τ)) ≤ r2 := h_case
          have h2 : r2 = (2 : ℝ) ^ (-(N : ℝ)) := by rfl
          rw [h2] at h1
          have h4 : K > 0 := by linarith
          have h5 : Real.log (K ^ (-(1 / τ))) ≤ Real.log ((2 : ℝ) ^ (-(N : ℝ))) :=
            Real.log_le_log (by positivity) h1
          have h6 : Real.log (K ^ (-(1 / τ))) = -(1 / τ) * Real.log K := by
            rw [Real.log_rpow (by linarith)] <;> ring
          have h7 : Real.log ((2 : ℝ) ^ (-(N : ℝ))) = -(N : ℝ) * Real.log 2 := by
            rw [Real.log_rpow (by norm_num)] <;> ring
          rw [h6, h7] at h5
          have h8 : Real.log K ≥ τ * (N : ℝ) * Real.log 2 := by
            have h9 : (1 / τ) * Real.log K ≥ (N : ℝ) * Real.log 2 := by linarith
            have h10 : 0 < τ := hτ
            calc Real.log K
              = τ * ((1 / τ) * Real.log K) := by field_simp [h10.ne'] <;> ring
            _ ≥ τ * ((N : ℝ) * Real.log 2) := by gcongr
            _ = τ * (N : ℝ) * Real.log 2 := by ring
          have h10 : K ≥ (2 : ℝ) ^ (τ * (N : ℝ)) := by
            have h11 : Real.log K ≥ Real.log ((2 : ℝ) ^ (τ * (N : ℝ))) := by
              have h12 : Real.log ((2 : ℝ) ^ (τ * (N : ℝ))) = τ * (N : ℝ) * Real.log 2 := by
                rw [Real.log_rpow (by norm_num)] <;> ring
              rw [h12]; exact h8
            exact (Real.log_le_log_iff (by positivity) (by positivity)).mp h11
          exact h10
        have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_pos'
        have hM_gt2s' : M > 2 * (σ + τ) / τ := by
          have h_eq : 2 * (σ + τ) / τ = 2 * ((σ + τ) / τ) := by ring
          rw [h_eq]
          exact hM_gt2s
        exact r0_large_case1 σ τ K M (N : ℝ) K' hτ hK (by linarith [hβ, hσ.1])
          hM_gt2s' hK'_ge_K hN_ge1 hK_ge
      · -- Case 2: r0 = r2
        have h_case' : r2 < K ^ (-(1 / τ)) := by exact lt_of_not_ge h_case
        have hr0_eq : r0 = r2 := by
          rw [hr0_def, min_eq_right (by linarith)]
        rw [hr0_eq]
        have hK_lt : K < (2 : ℝ) ^ (τ * (N : ℝ)) := by
          have h1 : K ^ (-(1 / τ)) > r2 := h_case'
          have h2 : r2 = (2 : ℝ) ^ (-(N : ℝ)) := by rfl
          rw [h2] at h1
          have hK_pos : 0 < K := by linarith
          have h3 : Real.log (K ^ (-(1 / τ))) > Real.log ((2 : ℝ) ^ (-(N : ℝ))) :=
            Real.log_lt_log (by positivity) h1
          have h4 : Real.log (K ^ (-(1 / τ))) = -(1 / τ) * Real.log K := by
            rw [Real.log_rpow (by linarith)] <;> ring
          have h5 : Real.log ((2 : ℝ) ^ (-(N : ℝ))) = -(N : ℝ) * Real.log 2 := by
            rw [Real.log_rpow (by norm_num)] <;> ring
          rw [h4, h5] at h3
          have h6 : Real.log K < τ * (N : ℝ) * Real.log 2 := by
            have h7 : (1 / τ) * Real.log K < (N : ℝ) * Real.log 2 := by linarith
            have h8 : 0 < τ := hτ
            calc Real.log K
              = τ * ((1 / τ) * Real.log K) := by field_simp [h8.ne'] <;> ring
            _ < τ * ((N : ℝ) * Real.log 2) := by gcongr
            _ = τ * (N : ℝ) * Real.log 2 := by ring
          have h9 : Real.log K < Real.log ((2 : ℝ) ^ (τ * (N : ℝ))) := by
            have h10 : Real.log ((2 : ℝ) ^ (τ * (N : ℝ))) = τ * (N : ℝ) * Real.log 2 := by
              rw [Real.log_rpow (by norm_num)] <;> ring
            rw [h10]; exact h6
          exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp h9
        let LM := lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X
        let E0 := Real.log (390 * C * C₁^σ) / (τ * Real.log 2)
        have hE0_le_LM : E0 ≤ LM := lowerBound_M_ge_E0 τ σ c C ε_F δ₀ C₁ D_T C_X D_X
        have h_N1_bound : (N : ℝ) + 1 < M * Real.log (C ^ 2 * M / c) / ((σ + τ) * Real.log 2) := by
          by_cases hL : L ≤ LM
          · -- L = LM
            have hL_eq : L = LM := by
              have hL_ge : L ≥ LM := lowerBound_ge_M τ σ c C ε_F δ₀ K C₁ D_T C_X D_X
              linarith
            have h1 : (N : ℝ) + 1 ≤ L + 2 := by linarith [hN_le_L1]
            rw [hL_eq] at h1
            linarith [hN_ok]
          · -- L > LM, so L = lbE
            have hL_gt : L > LM := by linarith
            have hL_eq : L = Real.log (390 * K * C * C₁^σ) / (2 * τ * Real.log 2) := by
              dsimp only [L, lowerBound]
              let lbE_val := Real.log (390 * K * C * C₁^σ) / (2 * τ * Real.log 2)
              have h : max LM lbE_val > LM := hL_gt
              have h' : LM ≤ lbE_val := by
                by_contra h''
                have : max LM lbE_val = LM := by
                  rw [max_eq_left] <;> linarith
                rw [this] at h; linarith
              rw [max_eq_right h']
            have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
            have h_pos1 : 0 < 390 * C * C₁^σ := by positivity
            have h_pos2 : 0 < τ * Real.log 2 := by positivity
            have h10 : Real.log (390 * K * C * C₁^σ) =
                Real.log (390 * C * C₁^σ) + Real.log K := by
              have h_comm : 390 * K * C * C₁^σ = (390 * C * C₁^σ) * K := by ring
              rw [h_comm]
              rw [Real.log_mul (by positivity) (by positivity)]
            have h11 : L < E0 / 2 + (N : ℝ) / 2 := by
              rw [hL_eq, h10]
              have h12 : Real.log K < τ * (N : ℝ) * Real.log 2 := by
                have h13 : Real.log K < Real.log ((2 : ℝ) ^ (τ * (N : ℝ))) := by
                  exact Real.log_lt_log (by positivity) hK_lt
                have h14 : Real.log ((2 : ℝ) ^ (τ * (N : ℝ))) = τ * (N : ℝ) * Real.log 2 := by
                  rw [Real.log_rpow (by norm_num)] <;> ring
                rw [h14] at h13; exact h13
              have h15 : (Real.log (390 * C * C₁^σ) + Real.log K) / (2 * τ * Real.log 2) <
                  (Real.log (390 * C * C₁^σ) + τ * (N : ℝ) * Real.log 2) / (2 * τ * Real.log 2) := by
                gcongr
              have h16 : (Real.log (390 * C * C₁^σ) + τ * (N : ℝ) * Real.log 2) / (2 * τ * Real.log 2) =
                  E0 / 2 + (N : ℝ) / 2 := by
                dsimp only [E0]
                field_simp [h_pos2.ne'] <;> ring
              rw [h16] at h15
              exact h15
            have h17 : (N : ℝ) < E0 + 2 := by
              have h18 : (N : ℝ) ≤ L + 1 := by linarith [hN_le_L1]
              linarith
            have h19 : (N : ℝ) + 1 < E0 + 3 := by linarith
            have h20 : (N : ℝ) + 1 < LM + 3 := by linarith [hE0_le_LM]
            linarith [hN_ok]
        have h1 : (C ^ 2 * M / c) ^ M > (2 : ℝ) ^ (((N : ℝ) + 1) * (σ + τ)) := by
          have h2 : M * Real.log (C ^ 2 * M / c) > ((N : ℝ) + 1) * (σ + τ) * Real.log 2 := by
            have h3 : (N : ℝ) + 1 < M * Real.log (C ^ 2 * M / c) / ((σ + τ) * Real.log 2) := h_N1_bound
            have h4 : 0 < (σ + τ) * Real.log 2 := by positivity
            have h5 : ((N : ℝ) + 1) * ((σ + τ) * Real.log 2) < M * Real.log (C ^ 2 * M / c) := by
              have h51 : ((N : ℝ) + 1) * ((σ + τ) * Real.log 2) <
                  (M * Real.log (C ^ 2 * M / c) / ((σ + τ) * Real.log 2)) * ((σ + τ) * Real.log 2) :=
                mul_lt_mul_of_pos_right h3 h4
              have h52 : (M * Real.log (C ^ 2 * M / c) / ((σ + τ) * Real.log 2)) * ((σ + τ) * Real.log 2) =
                  M * Real.log (C ^ 2 * M / c) := by
                rw [div_mul_cancel₀ _ h4.ne']
              rw [h52] at h51
              exact h51
            have h5' : M * Real.log (C ^ 2 * M / c) > ((N : ℝ) + 1) * (σ + τ) * Real.log 2 := by
              have h_eq : ((N : ℝ) + 1) * ((σ + τ) * Real.log 2) = ((N : ℝ) + 1) * (σ + τ) * Real.log 2 := by ring
              rw [h_eq] at h5
              exact h5
            exact h5'
          have h6 : Real.log ((C ^ 2 * M / c) ^ M) = M * Real.log (C ^ 2 * M / c) := by
            rw [Real.log_rpow (by positivity)] <;> ring
          have h7 : Real.log ((2 : ℝ) ^ (((N : ℝ) + 1) * (σ + τ))) =
              ((N : ℝ) + 1) * (σ + τ) * Real.log 2 := by
            rw [Real.log_rpow (by norm_num)] <;> ring
          have h8 : Real.log ((C ^ 2 * M / c) ^ M) > Real.log ((2 : ℝ) ^ (((N : ℝ) + 1) * (σ + τ))) := by
            rw [h6, h7]; exact h2
          exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp h8
        have h9 : K' ≥ (C ^ 2 * M / c) ^ M := hK'_ge_geom
        have h10 : r2 = (2 : ℝ) ^ (-(N : ℝ)) := by rfl
        rw [h10]
        have h11 : K' * ((2 : ℝ) ^ (-(N : ℝ))) ^ (σ + τ) > (2 : ℝ) ^ (σ + τ) := by
          have h12 : ((2 : ℝ) ^ (-(N : ℝ))) ^ (σ + τ) = (2 : ℝ) ^ (-(N : ℝ) * (σ + τ)) := by
            rw [← Real.rpow_mul (by norm_num)] <;> ring
          rw [h12]
          have h13 : K' * (2 : ℝ) ^ (-(N : ℝ) * (σ + τ)) ≥
              (C ^ 2 * M / c) ^ M * (2 : ℝ) ^ (-(N : ℝ) * (σ + τ)) := by gcongr
          have h14 : (C ^ 2 * M / c) ^ M * (2 : ℝ) ^ (-(N : ℝ) * (σ + τ)) >
              (2 : ℝ) ^ (σ + τ) := by
            have h15 : (C ^ 2 * M / c) ^ M > (2 : ℝ) ^ (((N : ℝ) + 1) * (σ + τ)) := h1
            have h16 : (2 : ℝ) ^ (((N : ℝ) + 1) * (σ + τ)) * (2 : ℝ) ^ (-(N : ℝ) * (σ + τ)) =
                (2 : ℝ) ^ (σ + τ) := by
              rw [← Real.rpow_add (by norm_num)] <;> ring_nf
            have h_pos_rpow : 0 < (2 : ℝ) ^ (-(N : ℝ) * (σ + τ)) := by positivity
            have h17 : (C ^ 2 * M / c) ^ M * (2 : ℝ) ^ (-(N : ℝ) * (σ + τ)) >
                (2 : ℝ) ^ (((N : ℝ) + 1) * (σ + τ)) * (2 : ℝ) ^ (-(N : ℝ) * (σ + τ)) :=
              mul_lt_mul_of_pos_right h15 h_pos_rpow
            rw [h16] at h17
            exact h17
          exact lt_of_lt_of_le h14 h13
        exact h11

    have hK'_gt4 : K' > 4 := by
      have h11 : K' ≥ (C ^ 2 * M / c) ^ M := hK'_ge_geom
      have hC2 : C ^ 2 ≥ 1 := by
        have h : 1 ≤ C := hC
        have h2 : C ^ 2 ≥ 1 ^ 2 := by gcongr
        simpa using h2
      have hC2M : C ^ 2 * M ≥ 1 := by
        have h1 : C ^ 2 ≥ 1 := hC2
        have h2 : M ≥ 1 := hM_ge1
        have h3 : C ^ 2 * M ≥ 1 * 1 := mul_le_mul h1 h2 (by linarith) (by linarith)
        simpa using h3
      have h12 : C ^ 2 * M / c > 10 := by
        have h4 : C ^ 2 * M / c ≥ 1 / c := by
          apply div_le_div_of_nonneg_right hC2M
          exact le_of_lt hc.1
        have h5 : 1 / c > 10 := by
          have h6 : c < 1 / 10 := hc.2
          have h7 : 0 < c := hc.1
          have h8 : 1 / c > 1 / (1 / 10 : ℝ) := by gcongr
          have h9 : 1 / (1 / 10 : ℝ) = 10 := by norm_num
          rw [h9] at h8
          exact h8
        linarith
      have h16 : (C ^ 2 * M / c) ^ M ≥ C ^ 2 * M / c := by
        have h17 : 1 ≤ C ^ 2 * M / c := by linarith
        have h_base_nonneg : 0 ≤ C ^ 2 * M / c := by positivity
        have h18 : (C ^ 2 * M / c) ^ M ≥ (C ^ 2 * M / c) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h17 hM_ge1
        have h19 : (C ^ 2 * M / c) ^ (1 : ℝ) = C ^ 2 * M / c := by simp
        rw [h19] at h18; exact h18
      have h20 : C ^ 2 * M / c > 4 := by linarith
      linarith
    have hστ_pos : 0 < σ + τ := by linarith [hσ_pos, hτ]
    have hr2_lt_one : r2 < 1 := by
      have h9 : (N : ℝ) ≥ 1 := by exact_mod_cast hN_pos'
      have h10 : (2 : ℝ) ^ (-(N : ℝ)) < (2 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      have h11 : (2 : ℝ) ^ (0 : ℝ) = 1 := by simp
      rw [h11] at h10
      exact h10
    have hr0_le_one : r0 ≤ 1 := by
      have h7 : r0 ≤ r2 := hr0_le_r2
      have h8 : r2 < 1 := hr2_lt_one
      linarith
    have hK'_r0_lower : K' / (2 : ℝ) ^ (σ + τ) ≥ 2 * r0 ^ (2 * τ) :=
      r0_lower_ineq K' σ τ r0 hK'_gt4 hστ_pos (hστ_lt_one σ hσ)
        (by positivity) hr0_le_one hτ

    -- Additional r constraints needed by case proofs
    set κ : ℝ := 14 * τ / (1 - σ) with hκ_def
    have h1mσ_pos : 0 < 1 - σ := by
      have h : 1 - σ ≥ ε := by linarith [hσ.2]
      linarith
    have h1mσ_le_one : 1 - σ ≤ 1 := by linarith [hσ.1, hβ]
    have hκ_lt_one : κ < 1 := by
      have h : τ < (1 - σ) / 14 := hτ_small σ hσ
      have h2 : 14 * τ < 1 - σ := by
        calc 14 * τ < 14 * ((1 - σ) / 14) := by gcongr
          _ = 1 - σ := by field_simp [h1mσ_pos.ne'] <;> ring
      dsimp only [κ]
      have h3 : 14 * τ / (1 - σ) < 1 := by
        rw [div_lt_one h1mσ_pos] <;> linarith
      exact h3
    have hκ_pos' : 0 < κ := by positivity
    have hκ_le_014 : κ ≤ 14 / 100 := by
      dsimp only [κ]
      have h1 : 1 - σ ≥ ε := by linarith [hσ.2]
      have h2 : 14 * τ / (1 - σ) ≤ 14 * τ / ε := by gcongr
      have h3 : 14 * τ / ε ≤ 14 / 100 := by
        have h4 : 14 * τ ≤ 14 * (ε / 100) := by gcongr
        have h5 : 14 * (ε / 100) = (14 / 100 : ℝ) * ε := by ring
        rw [h5] at h4
        have h6 : 0 < ε := hε
        calc (14 * τ) / ε
          ≤ (14 * (ε / 100)) / ε := by gcongr
        _ = 14 / 100 := by
          field_simp [h6.ne'] <;> ring
      linarith

    have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hT_eq : T * τ * Real.log 2 = Real.log (2 / (c * b)) := by
      dsimp only [T]; field_simp [h_log2_pos.ne'] <;> ring
    have h_Nτ_lower : (N : ℝ) * τ > Real.log 20 / Real.log 2 :=
      Nτ_lower_bound N T τ c b hτ hc.1 hc.2 hb_pos (by linarith [ha_pos]) hN_gt_T hT_eq

    have h_r2τ : r2 ^ τ ≤ 1 / 6 := by
      rw [hr2_eq]
      exact r2τ_le_sixth N τ hτ h_Nτ_lower

    have h_r2κ : r2 ^ κ ≤ 1 / 2 := by
      rw [hr2_eq]
      exact r2κ_le_half N τ σ κ hτ h1mσ_pos h1mσ_le_one hκ_def h_Nτ_lower

    have h_r21mk : r2 ^ (1 - κ) ≤ Real.sqrt 3 / 4 := by
      rw [hr2_eq]
      exact r21mk_le_sqrt3_4 N τ κ hτ hτ_lt_01 hκ_le_014 (by positivity) h_Nτ_lower

    have h_denom_pos : 0 < ε_F - 8 * τ - 3 * κ := by
      have h : 8 * τ + 4 * κ < ε_F := hεF_large
      have h' : 0 < κ := hκ_pos'
      linarith
    have hL_ge1 : L ≥ 400 / (τ^2 * Real.log 2) := lowerBound_ge_logabs τ σ c C ε_F δ₀ K C₁ D_T C_X D_X
    have hL_ge2 : L ≥ Real.log (20 * C) / (τ * Real.log 2) := lowerBound_ge_frostman τ σ c C ε_F δ₀ K C₁ D_T C_X D_X
    have hL_ge3 : L ≥ 1 + Real.log (1 / δ₀) / Real.log 2 := lowerBound_ge_delta τ σ c C ε_F δ₀ K C₁ D_T C_X D_X
    have hL_ge4 : L ≥ (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ) :=
      lowerBound_ge_epsF τ σ c C ε_F δ₀ K C₁ D_T C_X D_X
    have hL_ge7 : L ≥ 1 + Real.log (C_X * D_X) / (ε_F * Real.log 2) :=
      lowerBound_ge_conc11 τ σ c C ε_F δ₀ K C₁ D_T C_X D_X
    have hN_gt1 : (N : ℝ) > 400 / (τ^2 * Real.log 2) := by
      calc (N : ℝ) > L := hN_gt_L
        _ ≥ 400 / (τ^2 * Real.log 2) := hL_ge1
    have hN_gt2 : (N : ℝ) > Real.log (20 * C) / (τ * Real.log 2) := by
      calc (N : ℝ) > L := hN_gt_L
        _ ≥ Real.log (20 * C) / (τ * Real.log 2) := hL_ge2
    have hN_gt3 : (N : ℝ) > 1 + Real.log (1 / δ₀) / Real.log 2 := by
      calc (N : ℝ) > L := hN_gt_L
        _ ≥ 1 + Real.log (1 / δ₀) / Real.log 2 := hL_ge3
    have hN_gt4 : (N : ℝ) > (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ) := by
      calc (N : ℝ) > L := hN_gt_L
        _ ≥ _ := hL_ge4
    have hN_gt7 : (N : ℝ) > 1 + Real.log (C_X * D_X) / (ε_F * Real.log 2) := by
      calc (N : ℝ) > L := hN_gt_L
        _ ≥ _ := hL_ge7

    have h_r21mk_16 : r2 ^ (1 - κ) ≤ 1 / 16 := by
      rw [hr2_eq]
      exact r21mk_le_16 N τ κ hτ hτ_lt_01 hκ_le_014 h_Nτ_lower

    have h_log_abs : r2 ^ τ * Real.log (1 / r2) ≤ 1 / 100 := by
      rw [hr2_eq]
      exact log_abs_bound (N : ℝ) τ hτ hN_gt1

    have h_frostman : 20 * C * r2 ^ τ < 1 := by
      rw [hr2_eq]
      exact frostman_bound N τ C hτ hC hN_gt2

    have h_delta : 2 * r2 ≤ δ₀ := by
      rw [hr2_eq]
      exact delta_bound N δ₀ hδ0_pos hN_gt3

    have h_small3 : (2 : ℝ) ^ (-(2 * σ + ε_F)) *
        r2 ^ (-(ε_F - 8 * τ - 2 * κ)) > 80000 * r2 ^ (-κ) := by
      rw [hr2_eq]
      exact small3_bound N σ τ κ ε_F hτ h_denom_pos hN_gt4

    have h_conc11 : C_X * D_X ≤ (2 * r2)^(-ε_F) := by
      rw [hr2_eq]
      exact conc11_bound (N : ℝ) ε_F C_X D_X hεF_pos hC_X_pos hD_X_pos hN_gt7

    exact ⟨r2, N, hr2_eq, h_sum, hτ_small σ hσ, hK'_r0_large, hK'_r0_lower,
      h_r2τ, h_r2κ, h_r21mk, h_r21mk_16, h_log_abs, h_frostman, h_delta, h_small3,
      h_conc11, hN_gt_lowerBound_M⟩

  · -- Case ε ≥ 1: interval [β, 1-ε] is empty since β > 0 ≥ 1-ε
    let M : ℝ := 400 / τ^2 + 1
    have hM_ge1 : 1 ≤ M := by
      dsimp only [M]
      have h : 0 < 400 / τ^2 := by positivity
      linarith
    have hM_gt400 : M > 400 / τ^2 := by
      dsimp only [M] <;> linarith
    refine' ⟨M, hM_ge1,
      fun σ hσ => by
        have h1 : σ ≤ 1 - ε := hσ.2
        have h2 : 1 - ε ≤ 0 := by linarith
        have h3 : σ ≤ 0 := by linarith
        have h4 : β ≤ σ := hσ.1
        have h5 : β ≤ 0 := by linarith
        linarith [hβ],
      hM_gt400, _⟩
    intro σ c K C C₁ D_T C_X D_X ε_F δ₀ hσ hc hK hC hC₁_pos hD_T_pos hC_X_pos hD_X_pos hεF_pos hδ0_pos hεF_large hN_ok
    have h1 : σ ≤ 1 - ε := hσ.2
    have h2 : 1 - ε ≤ 0 := by linarith
    have h3 : σ ≤ 0 := by linarith
    have h4 : β ≤ σ := hσ.1
    have h5 : β ≤ 0 := by linarith
    linarith [hβ]


theorem good_params_exist (β ε : ℝ) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ (τ : ℝ) (hτ : 0 < τ) (hτ_lt_01 : τ < 1 / 100)
      (hτ_small_all : ∀ σ ∈ Set.Icc β (1 - ε), τ < (1 - σ) / 14),
      ∃ (M : ℝ) (hM : 1 ≤ M)
        (hM_gt2s : ∀ σ ∈ Set.Icc β (1 - ε), M > 2 * (σ + τ) / τ)
        (hM_gt400 : M > 400 / τ^2),
        ∀ (σ c K C C₁ D_T C_X D_X ε_F δ₀ : ℝ)
          (hσ : σ ∈ Set.Icc β (1 - ε))
          (hc : c ∈ Set.Ioo (0 : ℝ) (1 / 10)) (hK : 1 ≤ K) (hC : 1 ≤ C)
          (hC₁_pos : 0 < C₁) (hD_T_pos : 0 < D_T)
          (hC_X_pos : 0 < C_X) (hD_X_pos : 0 < D_X)
          (hεF_pos : 0 < ε_F) (hδ0_pos : 0 < δ₀)
          (hεF_large : 8 * τ + 4 * (14 * τ / (1 - σ)) < ε_F)
          (hN_ok : lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X + 3 <
            M * Real.log (C ^ 2 * M / c) / ((σ + τ) * Real.log 2)),
          ∃ (r2 : ℝ) (N : ℕ),
            (r2 = (2 : ℝ) ^ (-(N : ℝ))) ∧
            (∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ) < ENNReal.ofReal c) ∧
            (τ < (1 - σ) / 14) ∧
            ((2 : ℝ) ^ (σ + τ) < Real.rpow (max K (C ^ 2 * M / c)) M *
              (chooseR0 K τ r2 hK hτ) ^ (σ + τ)) ∧
            (Real.rpow (max K (C ^ 2 * M / c)) M / (2 : ℝ) ^ (σ + τ) ≥
              2 * (chooseR0 K τ r2 hK hτ) ^ (2 * τ)) ∧
            (r2 ^ τ ≤ 1 / 6) ∧
            (r2 ^ (14 * τ / (1 - σ)) ≤ 1 / 2) ∧
            (r2 ^ (1 - 14 * τ / (1 - σ)) ≤ Real.sqrt 3 / 4) ∧
            (r2 ^ (1 - 14 * τ / (1 - σ)) ≤ 1 / 16) ∧
            (r2 ^ τ * Real.log (1 / r2) ≤ 1 / 100) ∧
            (20 * C * r2 ^ τ < 1) ∧
            (2 * r2 ≤ δ₀) ∧
            ((2 : ℝ) ^ (-(2 * σ + ε_F)) * r2 ^ (-(ε_F - 8 * τ - 2 * (14 * τ / (1 - σ)))) >
              80000 * r2 ^ (-(14 * τ / (1 - σ)))) ∧
            (C_X * D_X ≤ (2 * r2)^(-ε_F)) ∧
            ((N : ℝ) > lowerBound_M τ σ c C ε_F δ₀ C₁ D_T C_X D_X) := by
  -- Case split: if ε ≥ 1, interval [β, 1-ε] is empty (β > 0 ≥ 1-ε), so vacuous
  by_cases h_eps_lt_one : ε < 1
  · -- Main case: ε < 1, delegate to good_params_exist_with_tau
    let τ : ℝ := ε / 100
    have hτ : 0 < τ := by positivity
    have hτ_lt_01 : τ < 1 / 100 := by
      dsimp only [τ]; have h : ε < 1 := h_eps_lt_one; linarith
    have hτ_le_eps100 : τ ≤ ε / 100 := by rfl
    have hτ_small_all : ∀ σ ∈ Set.Icc β (1 - ε), τ < (1 - σ) / 14 := by
      intro σ hσ
      have h1 : σ ≤ 1 - ε := hσ.2
      have h2 : 1 - σ ≥ ε := by linarith
      dsimp only [τ]
      have h3 : ε / 100 < ε / 14 := by gcongr <;> linarith
      linarith
    rcases good_params_exist_with_tau β ε τ hβ hε hτ hτ_lt_01 hτ_le_eps100 hτ_small_all
      with ⟨M, hM, hM_gt2s, hM_gt400, h_main⟩
    exact ⟨τ, hτ, hτ_lt_01, hτ_small_all, M, hM, hM_gt2s, hM_gt400, h_main⟩

  · -- Case ε ≥ 1: interval [β, 1-ε] is empty since β > 0 ≥ 1-ε
    let τ : ℝ := 1 / 200
    let M : ℝ := 400 / τ^2 + 1
    have hτ : 0 < τ := by norm_num
    have hτ_lt_01 : τ < 1 / 100 := by norm_num
    have hM_ge1 : 1 ≤ M := by
      dsimp only [M, τ]
      have h : 0 < 400 / (1 / 200 : ℝ)^2 := by positivity
      linarith
    have hM_gt400 : M > 400 / τ^2 := by
      dsimp only [M]
      <;> linarith
    refine' ⟨τ, hτ, hτ_lt_01,
      fun σ hσ => by
        have h1 : σ ≤ 1 - ε := hσ.2
        have h2 : 1 - ε ≤ 0 := by linarith
        have h3 : σ ≤ 0 := by linarith
        have h4 : β ≤ σ := hσ.1
        have h5 : β ≤ 0 := by linarith
        linarith [hβ],
      M, hM_ge1,
      fun σ hσ => by
        have h1 : σ ≤ 1 - ε := hσ.2
        have h2 : 1 - ε ≤ 0 := by linarith
        have h3 : σ ≤ 0 := by linarith
        have h4 : β ≤ σ := hσ.1
        have h5 : β ≤ 0 := by linarith
        linarith [hβ],
      hM_gt400, _⟩
    intro σ c K C C₁ D_T C_X D_X ε_F δ₀ hσ hc hK hC hC₁_pos hD_T_pos hC_X_pos hD_X_pos hεF_pos hδ0_pos hεF_large hN_ok
    have h1 : σ ≤ 1 - ε := hσ.2
    have h2 : 1 - ε ≤ 0 := by linarith
    have h3 : σ ≤ 0 := by linarith
    have h4 : β ≤ σ := hσ.1
    have h5 : β ≤ 0 := by linarith
    linarith [hβ]


/-- Generalized hN_ok_holds: works with arbitrary δ₀ > 0.

    The key difference from the original is that c3 = 1 + log(1/δ₀)/log 2
    can be arbitrarily large, so we add hM_delta to ensure M*log M dominates it.

    Currently keeps ε_F=10, C₁=D_T=C_X=D_X=1 hardcoded (same as original).
-/
lemma hN_ok_holds_delta (τ σ c C M δ₀ : ℝ)
    (hτ : 0 < τ) (hτ_lt_01 : τ < 1 / 100)
    (hσ_pos : 0 < σ) (hσ_lt_one : σ < 1)
    (hτ_small : τ < (1 - σ) / 14)
    (hc : c ∈ Set.Ioo (0 : ℝ) (1 / 10))
    (hC : 1 ≤ C)
    (hδ0_pos : 0 < δ₀) (hδ0_le_one : δ₀ ≤ 1)
    (hM_gt2s : M > 2 * (σ + τ) / τ)
    (hM_gt400 : M > 400 / τ^2)
    (hM_delta : M * Real.log M / ((σ + τ) * Real.log 2) >
      Real.log (8 / τ) / (τ * Real.log 2) + 400 / (τ^2 * Real.log 2) +
      Real.log 390 / (τ * Real.log 2) + 8 + Real.log (1 / δ₀) / Real.log 2) :
    lowerBound_M τ σ c C (10 : ℝ) δ₀ (1 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ) + 3 <
      M * Real.log (C ^ 2 * M / c) / ((σ + τ) * Real.log 2) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt_one : Real.log 2 < 1 := by
    have h : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h' : Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by positivity) h
    rw [Real.log_exp] at h'; exact h'
  have hlog2_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
    have h1 : Real.exp (1 / 2 : ℝ) < 2 := by
      have h2 : Real.exp 1 < 3 := Real.exp_one_lt_three
      have h_pos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
      have h3 : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
        have h4 : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
          rw [← Real.exp_add] <;> norm_num
        have h5 : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) := by ring
        rw [h5]; exact h4
      nlinarith [h2, h3, h_pos]
    have h4 : Real.log (Real.exp (1 / 2 : ℝ)) = (1 / 2 : ℝ) := Real.log_exp _
    have h5 : Real.log (Real.exp (1 / 2 : ℝ)) < Real.log 2 := Real.log_lt_log (by positivity) h1
    rw [h4] at h5; exact h5
  have h1mσ_pos : 0 < 1 - σ := by
    have h : 0 < τ := hτ
    have h' : τ < (1 - σ) / 14 := hτ_small
    have h'' : 0 < (1 - σ) / 14 := by linarith
    linarith
  have hσ_lt_one : σ < 1 := by linarith [h1mσ_pos]
  have hστ_pos : 0 < σ + τ := by linarith [hσ_pos, hτ]
  have hστ_lt_one : σ + τ < 1 := by
    have h1 : σ + τ < σ + (1 - σ) / 14 := by linarith [hτ_small]
    have h2 : σ + (1 - σ) / 14 < 1 := by
      have h3 : 0 < 1 - σ := h1mσ_pos
      nlinarith
    linarith
  have hc_pos : 0 < c := hc.1
  have h_neg_log_c_pos : 0 < -Real.log c := by
    have h1 : c < 1 := by linarith [hc.2]
    have h2 : Real.log c < 0 := Real.log_neg hc_pos h1
    linarith
  have hM_pos : 0 < M := by
    have h1 : (0 : ℝ) < 400 / τ^2 := by positivity
    linarith [hM_gt400]
  set x : ℝ := τ * Real.log 2 with hx_def
  have hx_pos : 0 < x := by positivity
  have hx_lt_one : x < 1 := by
    have h1 : τ < 1 / 100 := hτ_lt_01
    nlinarith [hlog2_lt_one]
  have h_exp_le : Real.exp (-x) ≤ 1 - x / 2 := by
    have h1 : 0 < 1 + x := by linarith
    have h2 : Real.exp x ≥ 1 + x := by linarith [Real.add_one_le_exp x]
    have h3 : Real.exp (-x) = (Real.exp x)⁻¹ := by rw [Real.exp_neg]
    rw [h3]
    have h4 : (Real.exp x)⁻¹ ≤ (1 + x)⁻¹ := by gcongr
    have h6 : 1 ≤ (1 + x) * (1 - x / 2) := by nlinarith
    have h5 : (1 + x)⁻¹ ≤ 1 - x / 2 := by
      calc (1 + x)⁻¹
        = (1 + x)⁻¹ * 1 := by ring
      _ ≤ (1 + x)⁻¹ * ((1 + x) * (1 - x / 2)) := by gcongr
      _ = 1 - x / 2 := by field_simp [h1.ne'] <;> ring
    exact le_trans h4 h5
  set b : ℝ := 1 - (2 : ℝ)^(-τ) with hb_def
  have hb_gt_tau4 : b > τ / 4 := by
    have h9 : (2 : ℝ)^(-τ) = Real.exp (-x) := by
      rw [Real.rpow_def_of_pos (by norm_num)] <;> simp [hx_def] <;> ring
    have h10 : b = 1 - Real.exp (-x) := by simp [hb_def, h9]
    rw [h10]
    have h11 : x / 2 > τ / 4 := by
      simp only [hx_def]
      have h13 : (1 / 2 : ℝ) < Real.log 2 := hlog2_gt_half
      nlinarith
    have h12 : 1 - Real.exp (-x) ≥ x / 2 := by
      have h13 : Real.exp (-x) ≤ 1 - x / 2 := h_exp_le
      linarith
    have h14 : 1 - Real.exp (-x) > τ / 4 := by
      calc 1 - Real.exp (-x) ≥ x / 2 := h12
        _ > τ / 4 := h11
    exact h14
  have hb_pos : 0 < b := by linarith [hb_gt_tau4]
  have hb_lt_one : b < 1 := by
    simp [hb_def]
    have h5 : (0 : ℝ) < τ := hτ
    have h6 : (2 : ℝ)^(-τ) > 0 := by positivity
    nlinarith
  set κ : ℝ := 14 * τ / (1 - σ) with hκ_def
  have hκ_lt_one : κ < 1 := by
    have h1 : 14 * τ < 1 - σ := by
      calc 14 * τ < 14 * ((1 - σ) / 14) := by gcongr
        _ = 1 - σ := by field_simp [h1mσ_pos.ne'] <;> ring
    rw [hκ_def]
    have h2 : 14 * τ / (1 - σ) < 1 := by
      apply (div_lt_one h1mσ_pos).mpr
      exact h1
    exact h2
  set L : ℝ := lowerBound_M τ σ c C (10 : ℝ) δ₀ (1 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ) with hL_def
  set c0 : ℝ := Real.log (2 / (c * b)) / (τ * Real.log 2) with hc0_def
  set c1 : ℝ := 400 / (τ^2 * Real.log 2) with hc1_def
  set c2 : ℝ := Real.log (20 * C) / (τ * Real.log 2) with hc2_def
  set c3 : ℝ := 1 + Real.log (1 / δ₀) / Real.log 2 with hc3_def
  set c4 : ℝ := (2 * σ + (10 : ℝ) + Real.log 80000 / Real.log 2) / ((10 : ℝ) - 8 * τ - 3 * κ) with hc4_def
  set c5 : ℝ := Real.log (390 * C) / (τ * Real.log 2) with hc5_def
  have hL_expand : L = max c0 (max c1 (max c2 (max c3 (max c4 (max c5 1))))) := by
    simp only [hL_def, lowerBound_M, c0, c1, c2, c3, c4, c5, b, κ]
    <;> simp [Real.log_one] <;> norm_num <;> ring
  have hc2_le_c5 : c2 ≤ c5 := by
    simp only [c2, c5]
    gcongr <;> norm_num <;> linarith [hC]
  have hden_gt6 : (10 : ℝ) - 8 * τ - 3 * κ > 6 := by
    have h1 : κ < 1 := hκ_lt_one
    have h2 : 8 * τ < 1 := by linarith [hτ_lt_01]
    nlinarith
  have hc4_lt5 : c4 < 5 := by
    have hden_pos : 0 < (10 : ℝ) - 8 * τ - 3 * κ := by linarith
    have hlog80000_lt17 : Real.log 80000 / Real.log 2 < 17 := by
      have h1 : (80000 : ℝ) < (2 : ℝ)^17 := by norm_num
      have h2 : Real.log 80000 < Real.log ((2 : ℝ)^17) := Real.log_lt_log (by positivity) h1
      have h3 : Real.log ((2 : ℝ)^17) = 17 * Real.log 2 := by rw [Real.log_pow] <;> ring
      rw [h3] at h2
      have h4 : Real.log 80000 / Real.log 2 < (17 * Real.log 2) / Real.log 2 := by gcongr
      have h5 : (17 * Real.log 2) / Real.log 2 = 17 := by
        field_simp [hlog2_pos.ne'] <;> ring
      rw [h5] at h4
      exact h4
    have h_goal : 2 * σ + (10 : ℝ) + Real.log 80000 / Real.log 2 < 5 * ((10 : ℝ) - 8 * τ - 3 * κ) := by
      have h1 : 2 * σ < 2 := by linarith [hσ_lt_one]
      have h2 : 8 * τ < 1 := by linarith [hτ_lt_01]
      have h3 : κ < 1 := hκ_lt_one
      nlinarith [hlog80000_lt17]
    have h : c4 < 5 := by
      rw [hc4_def]
      calc (2 * σ + (10 : ℝ) + Real.log 80000 / Real.log 2) / ((10 : ℝ) - 8 * τ - 3 * κ)
        < (5 * ((10 : ℝ) - 8 * τ - 3 * κ)) / ((10 : ℝ) - 8 * τ - 3 * κ) := by gcongr
      _ = 5 := by field_simp [hden_pos.ne'] <;> ring
    exact h
  have hc3_ge1 : c3 ≥ 1 := by
    have h1 : 0 < δ₀ := hδ0_pos
    have h2 : δ₀ ≤ 1 := hδ0_le_one
    have h3 : 1 / δ₀ ≥ 1 := by
      have h4 : 1 / δ₀ ≥ 1 / 1 := by gcongr
      simpa using h4
    have h5 : 0 ≤ Real.log (1 / δ₀) := Real.log_nonneg h3
    have h6 : 0 ≤ Real.log (1 / δ₀) / Real.log 2 := by
      apply div_nonneg h5
      exact hlog2_pos.le
    simp only [c3]
    have h7 : (1 : ℝ) + Real.log (1 / δ₀) / Real.log 2 ≥ 1 := by linarith [h6]
    exact h7
  have hc3_nonneg : 0 ≤ c3 := by linarith [hc3_ge1]
  have hc0_nonneg : 0 ≤ c0 := by
    have h1 : c * b < 2 := by
      have h2 : c < 1 / 10 := hc.2
      have h3 : b < 1 := hb_lt_one
      nlinarith
    have h4 : 2 / (c * b) ≥ 1 := by
      have h5 : 0 < c * b := by positivity
      have h6 : c * b ≤ 2 := by linarith
      exact (one_le_div h5).mpr h6
    have h7 : 0 ≤ Real.log (2 / (c * b)) := Real.log_nonneg h4
    simp only [c0]; positivity
  have hc1_nonneg : 0 ≤ c1 := by positivity
  have hc5_nonneg : 0 ≤ c5 := by
    have h1 : 390 * C ≥ 1 := by nlinarith [hC]
    have h2 : 0 ≤ Real.log (390 * C) := Real.log_nonneg h1
    simp only [c5]; positivity
  have hL_le : L ≤ c0 + c1 + c5 + 4 + c3 := by
    rw [hL_expand]
    have h_sum_nonneg : 0 ≤ c0 + c1 + c5 := by positivity
    have h_ge5 : c0 + c1 + c5 + 4 + c3 ≥ 5 := by linarith [hc3_ge1, h_sum_nonneg]
    have hc0' : c0 ≤ c0 + c1 + c5 + 4 + c3 := by linarith [hc3_nonneg]
    have hc1' : c1 ≤ c0 + c1 + c5 + 4 + c3 := by linarith [hc3_nonneg]
    have hc2' : c2 ≤ c0 + c1 + c5 + 4 + c3 := by linarith [hc2_le_c5, hc3_nonneg]
    have hc3' : c3 ≤ c0 + c1 + c5 + 4 + c3 := by linarith
    have hc4' : c4 ≤ c0 + c1 + c5 + 4 + c3 := by
      have h : c4 < 5 := hc4_lt5
      linarith [h_ge5]
    have hc5' : c5 ≤ c0 + c1 + c5 + 4 + c3 := by linarith [hc3_nonneg]
    have h1' : (1 : ℝ) ≤ c0 + c1 + c5 + 4 + c3 := by linarith [hc3_ge1]
    exact max_le hc0' (max_le hc1' (max_le hc2' (max_le hc3' (max_le hc4' (max_le hc5' h1')))))
  have hc0_bound : c0 ≤ (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) := by
    have h1 : 2 / (c * b) ≤ 8 / (c * τ) := by
      have h2 : b > τ / 4 := hb_gt_tau4
      have h3 : c * b > c * (τ / 4) := by gcongr
      have h4 : 0 < c * b := by positivity
      have h5 : 0 < c * (τ / 4) := by positivity
      have h6 : 2 / (c * b) < 2 / (c * (τ / 4)) := by
        exact div_lt_div_of_pos_left (by norm_num) h5 h3
      have h7 : 2 / (c * (τ / 4)) = 8 / (c * τ) := by
        field_simp [hc_pos.ne', hτ.ne'] <;> ring
      rw [h7] at h6
      exact h6.le
    have h6 : Real.log (2 / (c * b)) ≤ Real.log (8 / (c * τ)) := Real.log_le_log (by positivity) h1
    have h7 : Real.log (8 / (c * τ)) = Real.log (8 / τ) - Real.log c := by
      have h8 : (8 / (c * τ)) = (8 / τ) / c := by field_simp [hc_pos.ne', hτ.ne'] <;> ring
      rw [h8, Real.log_div (by positivity) (ne_of_gt hc_pos)] <;> ring
    rw [h7] at h6
    simp only [c0]; gcongr
  have hc5_bound : c5 ≤ (Real.log 390 + Real.log C) / (τ * Real.log 2) := by
    have h1 : Real.log (390 * C) = Real.log 390 + Real.log C := by
      rw [Real.log_mul (by positivity) (by linarith)] <;> ring
    simp only [c5]; rw [h1] <;> ring
  set RHS : ℝ := M * Real.log (C ^ 2 * M / c) / ((σ + τ) * Real.log 2) with hRHS_def
  have hRHS_expand : Real.log (C ^ 2 * M / c) = 2 * Real.log C + Real.log M - Real.log c := by
    have h_pos1 : 0 < C ^ 2 * M := by positivity
    have h4 : Real.log (C ^ 2 * M / c) = Real.log (C ^ 2 * M) - Real.log c := by
      rw [Real.log_div (ne_of_gt h_pos1) (ne_of_gt hc_pos)] <;> ring
    rw [h4]
    have h5 : Real.log (C ^ 2 * M) = Real.log (C ^ 2) + Real.log M := by
      rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt hM_pos)] <;> ring
    rw [h5]
    have h6 : Real.log (C ^ 2) = 2 * Real.log C := by rw [Real.log_pow] <;> ring
    rw [h6] <;> ring
  have hRHS_split : RHS =
      M * (2 * Real.log C) / ((σ + τ) * Real.log 2) +
      M * Real.log M / ((σ + τ) * Real.log 2) +
      M * (-Real.log c) / ((σ + τ) * Real.log 2) := by
    rw [hRHS_def, hRHS_expand] <;> ring
  have hM_div_gt : M / (σ + τ) > 2 / τ := by
    have h : M > 2 * (σ + τ) / τ := hM_gt2s
    calc M / (σ + τ) > (2 * (σ + τ) / τ) / (σ + τ) := by gcongr
      _ = 2 / τ := by field_simp [hστ_pos.ne'] <;> ring
  have h_part_c : M * (-Real.log c) / ((σ + τ) * Real.log 2) > (-Real.log c) / (τ * Real.log 2) := by
    have h1 : M / ((σ + τ) * Real.log 2) > 1 / (τ * Real.log 2) := by
      have h2 : M / (σ + τ) > 2 / τ := hM_div_gt
      have h3 : M / ((σ + τ) * Real.log 2) = (M / (σ + τ)) / Real.log 2 := by
        field_simp [hστ_pos.ne', hlog2_pos.ne'] <;> ring
      rw [h3]
      have h4 : (M / (σ + τ)) / Real.log 2 > (2 / τ) / Real.log 2 := by gcongr
      have h5 : (2 / τ) / Real.log 2 = 2 / (τ * Real.log 2) := by
        field_simp [hτ.ne', hlog2_pos.ne'] <;> ring
      have h6 : (M / (σ + τ)) / Real.log 2 > 2 / (τ * Real.log 2) := by
        calc (M / (σ + τ)) / Real.log 2
          > (2 / τ) / Real.log 2 := h4
        _ = 2 / (τ * Real.log 2) := h5
      have h7 : (2 : ℝ) / (τ * Real.log 2) > 1 / (τ * Real.log 2) := by
        apply div_lt_div_of_pos_right
        · norm_num
        · positivity
      exact lt_trans h7 h6
    have h4 : 0 < -Real.log c := h_neg_log_c_pos
    have h5 : M * (-Real.log c) / ((σ + τ) * Real.log 2) =
        (M / ((σ + τ) * Real.log 2)) * (-Real.log c) := by ring
    rw [h5]
    have h6 : (M / ((σ + τ) * Real.log 2)) * (-Real.log c) >
        (1 / (τ * Real.log 2)) * (-Real.log c) := by
      exact mul_lt_mul_of_pos_right h1 h4
    have h7 : (1 / (τ * Real.log 2)) * (-Real.log c) = (-Real.log c) / (τ * Real.log 2) := by ring
    rw [h7] at h6
    exact h6
  have h_part_C : M * (2 * Real.log C) / ((σ + τ) * Real.log 2) ≥ Real.log C / (τ * Real.log 2) := by
    have h_logC_nonneg : 0 ≤ Real.log C := Real.log_nonneg (by linarith)
    have h1 : M / (σ + τ) > 2 / τ := hM_div_gt
    have h2 : M * (2 * Real.log C) / ((σ + τ) * Real.log 2) =
        (M / (σ + τ)) * (2 * Real.log C) / Real.log 2 := by
      field_simp [hστ_pos.ne', hlog2_pos.ne'] <;> ring
    rw [h2]
    have h3 : (M / (σ + τ)) * (2 * Real.log C) / Real.log 2 ≥
        (2 / τ) * (2 * Real.log C) / Real.log 2 := by
      have h4' : (M / (σ + τ)) * (2 * Real.log C) ≥ (2 / τ) * (2 * Real.log C) := by
        have h5 : M / (σ + τ) > 2 / τ := h1
        have h6 : 0 ≤ 2 * Real.log C := by positivity
        exact mul_le_mul_of_nonneg_right h5.le h6
      exact div_le_div_of_nonneg_right h4' (by positivity)
    have h4 : (2 / τ) * (2 * Real.log C) / Real.log 2 = 4 * Real.log C / (τ * Real.log 2) := by
      field_simp [hτ.ne', hlog2_pos.ne'] <;> ring
    rw [h4] at h3
    have h5 : 4 * Real.log C / (τ * Real.log 2) ≥ Real.log C / (τ * Real.log 2) := by
      have h6 : 0 ≤ Real.log C := h_logC_nonneg
      have h7 : 4 * Real.log C ≥ Real.log C := by
        have h71 : 0 ≤ Real.log C := h_logC_nonneg
        linarith
      have h8 : 0 < τ * Real.log 2 := by positivity
      exact div_le_div_of_nonneg_right h7 (by positivity)
    exact le_trans h5 h3
  have hc3_expand : c3 = 1 + Real.log (1 / δ₀) / Real.log 2 := by
    simp only [c3] <;> ring
  have hL_le2 : L + 3 ≤ (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) +
      400 / (τ^2 * Real.log 2) +
      (Real.log 390 + Real.log C) / (τ * Real.log 2) + 8 +
      Real.log (1 / δ₀) / Real.log 2 := by
    calc L + 3
      ≤ c0 + c1 + c5 + 4 + c3 + 3 := by linarith [hL_le]
    _ = c0 + c1 + c5 + 7 + c3 := by ring
    _ = c0 + c1 + c5 + 8 + Real.log (1 / δ₀) / Real.log 2 := by
      rw [hc3_expand] <;> ring
    _ ≤ (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) + 400 / (τ^2 * Real.log 2) +
        (Real.log 390 + Real.log C) / (τ * Real.log 2) + 8 +
        Real.log (1 / δ₀) / Real.log 2 := by
      have h1 : c0 ≤ (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) := hc0_bound
      have h2 : c1 = 400 / (τ^2 * Real.log 2) := by simp [c1]
      have h3 : c5 ≤ (Real.log 390 + Real.log C) / (τ * Real.log 2) := hc5_bound
      have h4 : c0 + c1 + c5 + 8 + Real.log (1 / δ₀) / Real.log 2 ≤
          (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) + c1 +
          (Real.log 390 + Real.log C) / (τ * Real.log 2) + 8 +
          Real.log (1 / δ₀) / Real.log 2 := by
        exact add_le_add (add_le_add (add_le_add (add_le_add h1 (le_refl c1)) h3) (by norm_num)) (by norm_num)
      rw [h2] at h4
      exact h4
  rw [hRHS_split]
  have h_final : (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) +
      400 / (τ^2 * Real.log 2) +
      (Real.log 390 + Real.log C) / (τ * Real.log 2) + 8 +
      Real.log (1 / δ₀) / Real.log 2 <
      M * (2 * Real.log C) / ((σ + τ) * Real.log 2) +
      M * Real.log M / ((σ + τ) * Real.log 2) +
      M * (-Real.log c) / ((σ + τ) * Real.log 2) := by
    have h1 : (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) =
        Real.log (8 / τ) / (τ * Real.log 2) + (-Real.log c) / (τ * Real.log 2) := by
      field_simp [hτ.ne', hlog2_pos.ne'] <;> ring
    have h2 : (Real.log 390 + Real.log C) / (τ * Real.log 2) =
        Real.log 390 / (τ * Real.log 2) + Real.log C / (τ * Real.log 2) := by
      field_simp [hτ.ne', hlog2_pos.ne'] <;> ring
    rw [h1, h2]
    linarith [h_part_c, h_part_C, hM_delta]
  exact lt_of_le_of_lt hL_le2 h_final

/-- Fully generalized `hN_ok_holds`: works with arbitrary `ε_F`, `C_X`, `D_X`
    (with `C₁ = 1`, which is the case in FinalWiring).

    Unlike `hN_ok_holds_delta`, this version does not hardcode `ε_F = 10`
    or `C_X = D_X = 1`. The `c4` and `c7` components of `lowerBound_M` are
    included explicitly in the `hM_delta` hypothesis.

    `D_T` is irrelevant because it does not appear in `lowerBound_M`. -/
lemma hN_ok_holds_full (τ σ c C M δ₀ ε_F C_X D_X : ℝ)
    (hτ : 0 < τ) (hτ_lt_01 : τ < 1 / 100)
    (hσ_pos : 0 < σ) (hσ_lt_one : σ < 1)
    (hτ_small : τ < (1 - σ) / 14)
    (hc : c ∈ Set.Ioo (0 : ℝ) (1 / 10))
    (hC : 1 ≤ C)
    (hδ0_pos : 0 < δ₀) (hδ0_le_one : δ₀ ≤ 1)
    (hεF_pos : 0 < ε_F)
    (hεF_large : 8 * τ + 4 * (14 * τ / (1 - σ)) < ε_F)
    (hC_X_pos : 0 < C_X) (hD_X_pos : 0 < D_X)
    (hC_X_ge_one : 1 ≤ C_X) (hD_X_ge_one : 1 ≤ D_X)
    (hM_gt2s : M > 2 * (σ + τ) / τ)
    (hM_gt400 : M > 400 / τ^2)
    (hM_delta : M * Real.log M / ((σ + τ) * Real.log 2) >
      Real.log (8 / τ) / (τ * Real.log 2) + 400 / (τ^2 * Real.log 2) +
      Real.log 390 / (τ * Real.log 2) + 8 + Real.log (1 / δ₀) / Real.log 2 +
      (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * (14 * τ / (1 - σ))) +
      Real.log (C_X * D_X) / (ε_F * Real.log 2)) :
    lowerBound_M τ σ c C ε_F δ₀ (1 : ℝ) D_X C_X D_X + 3 <
      M * Real.log (C ^ 2 * M / c) / ((σ + τ) * Real.log 2) := by
  set κ : ℝ := 14 * τ / (1 - σ) with hκ_def
  have h1mσ_pos : 0 < 1 - σ := by linarith [hσ_lt_one]
  have hκ_pos : 0 < κ := by positivity
  have h_denom_pos : 0 < ε_F - 8 * τ - 3 * κ := by
    have h : 8 * τ + 4 * κ < ε_F := hεF_large
    linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc_pos : 0 < c := hc.1
  have h_neg_log_c_pos : 0 < -Real.log c := by
    have h1 : c < 1 := by linarith [hc.2]
    have h2 : Real.log c < 0 := Real.log_neg hc_pos h1
    linarith
  have hM_pos : 0 < M := by
    have h : 0 < 400 / τ^2 := by positivity
    linarith [hM_gt400]
  have hlog2_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
    have h1 : Real.exp (1 / 2 : ℝ) < 2 := by
      have h2 : Real.exp 1 < 3 := Real.exp_one_lt_three
      have h_pos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
      have h3 : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
        have h4 : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
          rw [← Real.exp_add] <;> norm_num
        have h5 : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) := by ring
        rw [h5]; exact h4
      nlinarith [h2, h3, h_pos]
    have h4 : Real.log (Real.exp (1 / 2 : ℝ)) = (1 / 2 : ℝ) := Real.log_exp _
    have h5 : Real.log (Real.exp (1 / 2 : ℝ)) < Real.log 2 := Real.log_lt_log (by positivity) h1
    rw [h4] at h5; exact h5
  have hστ_pos : 0 < σ + τ := by linarith [hσ_pos, hτ]

  -- Expand lowerBound_M with C₁ = 1
  set c0 : ℝ := Real.log (2 / (c * (1 - (2 : ℝ)^(-τ)))) / (τ * Real.log 2) with hc0_def
  set c1 : ℝ := 400 / (τ^2 * Real.log 2) with hc1_def
  set c2 : ℝ := Real.log (20 * C) / (τ * Real.log 2) with hc2_def
  set c3 : ℝ := 1 + Real.log (1 / δ₀) / Real.log 2 with hc3_def
  set c4 : ℝ := (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ) with hc4_def
  set c5 : ℝ := Real.log (390 * C) / (τ * Real.log 2) with hc5_def
  set c7 : ℝ := 1 + Real.log (C_X * D_X) / (ε_F * Real.log 2) with hc7_def

  have hL_expand : lowerBound_M τ σ c C ε_F δ₀ (1 : ℝ) D_X C_X D_X =
      max c0 (max c1 (max c2 (max c3 (max c4 (max c5 c7))))) := by
    simp only [lowerBound_M, c0, c1, c2, c3, c4, c5, c7, κ]
    <;> simp [Real.log_one] <;> ring

  -- c2 ≤ c5 since 20 < 390
  have hc2_le_c5 : c2 ≤ c5 := by
    simp only [c2, c5]
    gcongr <;> norm_num <;> linarith [hC]

  -- Non-negativity of all c_i
  have h2_pos_neg : 0 < (2 : ℝ) := by norm_num
  have h_rpow_neg : 0 < (2 : ℝ)^(-τ) := Real.rpow_pos_of_pos h2_pos_neg (-τ)
  have h_rpow_lt_one : (2 : ℝ)^(-τ) < 1 := by
    have h : (2 : ℝ)^(-τ) < (2 : ℝ)^(0 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 2 from by norm_num) (by linarith)
    simpa using h
  have h_b_pos : 0 < 1 - (2 : ℝ)^(-τ) := by
    have h : (2 : ℝ)^(-τ) < 1 := h_rpow_lt_one
    exact sub_pos_of_lt h
  have h_c0_nonneg : 0 ≤ c0 := by
    have h_arg_gt_one : 1 < 2 / (c * (1 - (2 : ℝ)^(-τ))) := by
      have h2 : c * (1 - (2 : ℝ)^(-τ)) < 1 / 10 := by
        have h3 : c < 1 / 10 := hc.2
        have h4 : 1 - (2 : ℝ)^(-τ) < 1 := by linarith [h_rpow_neg]
        nlinarith [hc_pos]
      have h5 : 0 < c * (1 - (2 : ℝ)^(-τ)) := by positivity
      have h6 : 2 / (c * (1 - (2 : ℝ)^(-τ))) > 20 := by
        have h7 : 2 / (c * (1 - (2 : ℝ)^(-τ))) > 2 / (1 / 10 : ℝ) := by gcongr
        norm_num at h7 ⊢ <;> exact h7
      linarith
    have hlog_pos : 0 < Real.log (2 / (c * (1 - (2 : ℝ)^(-τ)))) := Real.log_pos h_arg_gt_one
    have hden_pos : 0 < τ * Real.log 2 := by positivity
    exact div_nonneg hlog_pos.le hden_pos.le
  have h_c1_nonneg : 0 ≤ c1 := by positivity
  have h_c2_nonneg : 0 ≤ c2 := by
    have h1 : 1 < 20 * C := by nlinarith [hC]
    have h2 : 0 < Real.log (20 * C) := Real.log_pos h1
    have h3 : 0 < τ * Real.log 2 := by positivity
    exact div_nonneg h2.le h3.le
  have h_c3_nonneg : 0 ≤ c3 := by
    have h1 : 1 ≤ 1 / δ₀ := by
      have h2 : 0 < δ₀ := hδ0_pos
      have h3 : δ₀ ≤ 1 := hδ0_le_one
      field_simp [h2.ne'] <;> linarith
    have h4 : 0 ≤ Real.log (1 / δ₀) := Real.log_nonneg h1
    have h5 : 0 < Real.log 2 := hlog2_pos
    have h6 : 0 ≤ Real.log (1 / δ₀) / Real.log 2 := div_nonneg h4 h5.le
    have h7 : c3 = 1 + Real.log (1 / δ₀) / Real.log 2 := by simp [c3]
    rw [h7]
    linarith
  have h_c4_nonneg : 0 ≤ c4 := by positivity
  have h_c5_nonneg : 0 ≤ c5 := by
    have h1 : 1 < 390 * C := by nlinarith [hC]
    have h2 : 0 < Real.log (390 * C) := Real.log_pos h1
    have h3 : 0 < τ * Real.log 2 := by positivity
    exact div_nonneg h2.le h3.le
  have h_c7_nonneg : 0 ≤ c7 := by
    have h1 : 1 ≤ C_X * D_X := by nlinarith [hC_X_ge_one, hD_X_ge_one]
    have h2 : 0 ≤ Real.log (C_X * D_X) := Real.log_nonneg h1
    have h3 : 0 < ε_F * Real.log 2 := by positivity
    have h4 : 0 ≤ Real.log (C_X * D_X) / (ε_F * Real.log 2) := div_nonneg h2 h3.le
    have h5 : c7 = 1 + Real.log (C_X * D_X) / (ε_F * Real.log 2) := by simp [c7]
    rw [h5]
    linarith

  -- Bound L ≤ c0 + c1 + c3 + c4 + c5 + c7 (drop c2 from max since c2 ≤ c5 ≤ max c5 c7)
  have hL_le : lowerBound_M τ σ c C ε_F δ₀ (1 : ℝ) D_X C_X D_X ≤
      c0 + c1 + c3 + c4 + c5 + c7 := by
    rw [hL_expand]
    have h_c2_le_max : c2 ≤ max c3 (max c4 (max c5 c7)) := by
      have h1 : c2 ≤ c5 := hc2_le_c5
      have h2 : c5 ≤ max c5 c7 := le_max_left c5 c7
      have h3 : max c5 c7 ≤ max c4 (max c5 c7) := le_max_right c4 (max c5 c7)
      have h4 : max c4 (max c5 c7) ≤ max c3 (max c4 (max c5 c7)) := le_max_right c3 (max c4 (max c5 c7))
      exact le_trans h1 (le_trans h2 (le_trans h3 h4))
    have h_simp : max c2 (max c3 (max c4 (max c5 c7))) = max c3 (max c4 (max c5 c7)) := by
      rw [max_eq_right h_c2_le_max]
    have h_max_le : max c0 (max c1 (max c3 (max c4 (max c5 c7)))) ≤
        c0 + c1 + c3 + c4 + c5 + c7 := by
      have h1 : max c5 c7 ≤ c5 + c7 := max_le_add_of_nonneg h_c5_nonneg h_c7_nonneg
      have h2 : max c4 (max c5 c7) ≤ c4 + c5 + c7 := by
        have h21 : 0 ≤ max c5 c7 := by positivity
        have h22 : max c4 (max c5 c7) ≤ c4 + max c5 c7 := max_le_add_of_nonneg h_c4_nonneg h21
        linarith
      have h3 : max c3 (max c4 (max c5 c7)) ≤ c3 + c4 + c5 + c7 := by
        have h31 : 0 ≤ max c4 (max c5 c7) := by positivity
        have h32 : max c3 (max c4 (max c5 c7)) ≤ c3 + max c4 (max c5 c7) := max_le_add_of_nonneg h_c3_nonneg h31
        linarith [h2]
      have h4 : max c1 (max c3 (max c4 (max c5 c7))) ≤ c1 + c3 + c4 + c5 + c7 := by
        have h41 : 0 ≤ max c3 (max c4 (max c5 c7)) := by positivity
        have h42 : max c1 (max c3 (max c4 (max c5 c7))) ≤ c1 + max c3 (max c4 (max c5 c7)) := max_le_add_of_nonneg h_c1_nonneg h41
        linarith [h3]
      have h5 : max c0 (max c1 (max c3 (max c4 (max c5 c7)))) ≤ c0 + c1 + c3 + c4 + c5 + c7 := by
        have h51 : 0 ≤ max c1 (max c3 (max c4 (max c5 c7))) := by positivity
        have h52 : max c0 (max c1 (max c3 (max c4 (max c5 c7)))) ≤ c0 + max c1 (max c3 (max c4 (max c5 c7))) := max_le_add_of_nonneg h_c0_nonneg h51
        linarith [h4]
      exact h5
    rw [h_simp]
    exact h_max_le

  -- Bound c0
  set b : ℝ := 1 - (2 : ℝ)^(-τ) with hb_def
  have hb_pos : 0 < b := by
    have h : (2 : ℝ)^(-τ) < 1 := by
      have h' : (2 : ℝ)^(-τ) < (2 : ℝ)^(0 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      simpa using h'
    have h2 : b = 1 - (2 : ℝ)^(-τ) := by simp [b]
    rw [h2]
    exact sub_pos_of_lt h
  have hb_gt_tau4 : b > τ / 4 := by
    set x : ℝ := τ * Real.log 2 with hx_def
    have hx_pos : 0 < x := by positivity
    have h_exp_le : Real.exp (-x) ≤ 1 - x / 2 := by
      have h1 : 0 < 1 + x := by linarith
      have h2 : Real.exp x ≥ 1 + x := by linarith [Real.add_one_le_exp x]
      have h3 : Real.exp (-x) = (Real.exp x)⁻¹ := by rw [Real.exp_neg]
      rw [h3]
      have h4 : (Real.exp x)⁻¹ ≤ (1 + x)⁻¹ := by gcongr
      have hx_lt_one : x < 1 := by
        have h1 : τ < 1 / 100 := hτ_lt_01
        have h2 : Real.log 2 < 1 := by
          have h : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          have h' : Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by positivity) h
          rw [Real.log_exp] at h'; exact h'
        nlinarith
      have h6 : 1 ≤ (1 + x) * (1 - x / 2) := by
        have h7 : (1 + x) * (1 - x / 2) = 1 + x / 2 - x^2 / 2 := by ring
        rw [h7]
        have h8 : 0 ≤ x / 2 - x^2 / 2 := by
          have h9 : 0 ≤ x := by linarith
          have h10 : x ≤ 1 := by linarith
          nlinarith
        linarith
      have h5 : (1 + x)⁻¹ ≤ 1 - x / 2 := by
        calc (1 + x)⁻¹
          = (1 + x)⁻¹ * 1 := by ring
        _ ≤ (1 + x)⁻¹ * ((1 + x) * (1 - x / 2)) := by gcongr
        _ = 1 - x / 2 := by field_simp [h1.ne'] <;> ring
      exact le_trans h4 h5
    have h9 : (2 : ℝ)^(-τ) = Real.exp (-x) := by
      rw [Real.rpow_def_of_pos (by norm_num)] <;> simp [hx_def] <;> ring
    have h10 : b = 1 - Real.exp (-x) := by simp [hb_def, h9]
    rw [h10]
    have h11 : x / 2 > τ / 4 := by
      simp only [hx_def]
      have h12 : (1 / 2 : ℝ) < Real.log 2 := by
        have h1 : Real.exp (1 / 2 : ℝ) < 2 := by
          have h2 : Real.exp 1 < 3 := Real.exp_one_lt_three
          have h_pos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
          have h3 : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
            have h4 : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
              rw [← Real.exp_add] <;> norm_num
            have h5 : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) := by ring
            rw [h5]; exact h4
          nlinarith [h2, h3, h_pos]
        have h4 : Real.log (Real.exp (1 / 2 : ℝ)) = (1 / 2 : ℝ) := Real.log_exp _
        have h5 : Real.log (Real.exp (1 / 2 : ℝ)) < Real.log 2 := Real.log_lt_log (by positivity) h1
        rw [h4] at h5; exact h5
      nlinarith
    have h12 : 1 - Real.exp (-x) ≥ x / 2 := by
      have h13 : Real.exp (-x) ≤ 1 - x / 2 := h_exp_le
      linarith
    have h14 : 1 - Real.exp (-x) > τ / 4 := by
      calc 1 - Real.exp (-x) ≥ x / 2 := h12
        _ > τ / 4 := h11
    exact h14
  have hc0_bound : c0 ≤ (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) := by
    have h1 : 2 / (c * b) ≤ 8 / (c * τ) := by
      have h2 : b > τ / 4 := hb_gt_tau4
      have h3 : c * b > c * (τ / 4) := by gcongr
      have h4 : 0 < c * b := by positivity
      have h5 : 0 < c * (τ / 4) := by positivity
      have h6 : 2 / (c * b) < 2 / (c * (τ / 4)) := by
        exact div_lt_div_of_pos_left (by norm_num) h5 h3
      have h7 : 2 / (c * (τ / 4)) = 8 / (c * τ) := by
        field_simp [hc_pos.ne', hτ.ne'] <;> ring
      rw [h7] at h6
      exact h6.le
    have h6 : Real.log (2 / (c * b)) ≤ Real.log (8 / (c * τ)) := Real.log_le_log (by positivity) h1
    have h7 : Real.log (8 / (c * τ)) = Real.log (8 / τ) - Real.log c := by
      have h8 : (8 / (c * τ)) = (8 / τ) / c := by field_simp [hc_pos.ne', hτ.ne'] <;> ring
      rw [h8, Real.log_div (by positivity) (ne_of_gt hc_pos)] <;> ring
    rw [h7] at h6
    simp only [c0]; gcongr

  have hc5_bound : c5 ≤ (Real.log 390 + Real.log C) / (τ * Real.log 2) := by
    have h1 : Real.log (390 * C) = Real.log 390 + Real.log C := by
      rw [Real.log_mul (by positivity) (by linarith)] <;> ring
    simp only [c5]; rw [h1] <;> ring

  set RHS : ℝ := M * Real.log (C ^ 2 * M / c) / ((σ + τ) * Real.log 2) with hRHS_def
  have hRHS_expand : Real.log (C ^ 2 * M / c) = 2 * Real.log C + Real.log M - Real.log c := by
    have h_pos1 : 0 < C ^ 2 * M := by positivity
    have h4 : Real.log (C ^ 2 * M / c) = Real.log (C ^ 2 * M) - Real.log c := by
      rw [Real.log_div (ne_of_gt h_pos1) (ne_of_gt hc_pos)] <;> ring
    rw [h4]
    have h5 : Real.log (C ^ 2 * M) = Real.log (C ^ 2) + Real.log M := by
      rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt hM_pos)] <;> ring
    rw [h5]
    have h6 : Real.log (C ^ 2) = 2 * Real.log C := by rw [Real.log_pow] <;> ring
    rw [h6] <;> ring
  have hRHS_split : RHS =
      M * (2 * Real.log C) / ((σ + τ) * Real.log 2) +
      M * Real.log M / ((σ + τ) * Real.log 2) +
      M * (-Real.log c) / ((σ + τ) * Real.log 2) := by
    rw [hRHS_def, hRHS_expand] <;> ring

  have hM_div_gt : M / (σ + τ) > 2 / τ := by
    have h : M > 2 * (σ + τ) / τ := hM_gt2s
    calc M / (σ + τ) > (2 * (σ + τ) / τ) / (σ + τ) := by gcongr
      _ = 2 / τ := by field_simp [hστ_pos.ne'] <;> ring

  have h_part_c : M * (-Real.log c) / ((σ + τ) * Real.log 2) > (-Real.log c) / (τ * Real.log 2) := by
    have h1 : M / ((σ + τ) * Real.log 2) > 1 / (τ * Real.log 2) := by
      have h2 : M / (σ + τ) > 2 / τ := hM_div_gt
      have h3 : M / ((σ + τ) * Real.log 2) = (M / (σ + τ)) / Real.log 2 := by
        field_simp [hστ_pos.ne', hlog2_pos.ne'] <;> ring
      rw [h3]
      have h4 : (M / (σ + τ)) / Real.log 2 > (2 / τ) / Real.log 2 := by gcongr
      have h5 : (2 / τ) / Real.log 2 = 2 / (τ * Real.log 2) := by
        field_simp [hτ.ne', hlog2_pos.ne'] <;> ring
      have h6 : (M / (σ + τ)) / Real.log 2 > 2 / (τ * Real.log 2) := by
        calc (M / (σ + τ)) / Real.log 2
          > (2 / τ) / Real.log 2 := h4
        _ = 2 / (τ * Real.log 2) := h5
      have h7 : (2 : ℝ) / (τ * Real.log 2) > 1 / (τ * Real.log 2) := by
        apply div_lt_div_of_pos_right
        · norm_num
        · positivity
      exact lt_trans h7 h6
    have h4 : 0 < -Real.log c := h_neg_log_c_pos
    have h5 : M * (-Real.log c) / ((σ + τ) * Real.log 2) =
        (M / ((σ + τ) * Real.log 2)) * (-Real.log c) := by ring
    rw [h5]
    have h6 : (M / ((σ + τ) * Real.log 2)) * (-Real.log c) >
        (1 / (τ * Real.log 2)) * (-Real.log c) := by
      exact mul_lt_mul_of_pos_right h1 h4
    have h7 : (1 / (τ * Real.log 2)) * (-Real.log c) = (-Real.log c) / (τ * Real.log 2) := by ring
    rw [h7] at h6
    exact h6

  have h_part_C : M * (2 * Real.log C) / ((σ + τ) * Real.log 2) ≥ 2 * Real.log C / (τ * Real.log 2) := by
    have h_logC_nonneg : 0 ≤ Real.log C := Real.log_nonneg (by linarith)
    have h1 : M / (σ + τ) > 2 / τ := hM_div_gt
    have h2 : M * (2 * Real.log C) / ((σ + τ) * Real.log 2) =
        (M / (σ + τ)) * (2 * Real.log C) / Real.log 2 := by
      field_simp [hστ_pos.ne', hlog2_pos.ne'] <;> ring
    rw [h2]
    have h3 : (M / (σ + τ)) * (2 * Real.log C) / Real.log 2 ≥
        (2 / τ) * (2 * Real.log C) / Real.log 2 := by
      have h4' : (M / (σ + τ)) * (2 * Real.log C) ≥ (2 / τ) * (2 * Real.log C) := by
        have h5 : M / (σ + τ) > 2 / τ := h1
        have h6 : 0 ≤ 2 * Real.log C := by positivity
        exact mul_le_mul_of_nonneg_right h5.le h6
      exact div_le_div_of_nonneg_right h4' (by positivity)
    have h4 : (2 / τ) * (2 * Real.log C) / Real.log 2 = 4 * Real.log C / (τ * Real.log 2) := by
      field_simp [hτ.ne', hlog2_pos.ne'] <;> ring
    rw [h4] at h3
    have h5 : 4 * Real.log C / (τ * Real.log 2) ≥ 2 * Real.log C / (τ * Real.log 2) := by
      have h6 : 0 ≤ Real.log C := h_logC_nonneg
      have h7 : 4 * Real.log C ≥ 2 * Real.log C := by linarith
      have h8 : 0 < τ * Real.log 2 := by positivity
      exact div_le_div_of_nonneg_right h7 (by positivity)
    exact le_trans h5 h3

  have hL_le2 : lowerBound_M τ σ c C ε_F δ₀ (1 : ℝ) D_X C_X D_X + 3 ≤
      (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) +
      400 / (τ^2 * Real.log 2) +
      (Real.log 390 + Real.log C) / (τ * Real.log 2) +
      c4 + Real.log (C_X * D_X) / (ε_F * Real.log 2) + 8 +
      Real.log (1 / δ₀) / Real.log 2 := by
    have h_const : c3 + c7 + 3 = Real.log (C_X * D_X) / (ε_F * Real.log 2) + 5 + Real.log (1 / δ₀) / Real.log 2 := by
      simp only [c3, c7] <;> ring
    calc lowerBound_M τ σ c C ε_F δ₀ (1 : ℝ) D_X C_X D_X + 3
      ≤ c0 + c1 + c3 + c4 + c5 + c7 + 3 := by linarith [hL_le]
    _ = c0 + c1 + c5 + c4 + (c3 + c7 + 3) := by ring
    _ = c0 + c1 + c5 + c4 + Real.log (C_X * D_X) / (ε_F * Real.log 2) + 5 + Real.log (1 / δ₀) / Real.log 2 := by
      have h_eq : c0 + c1 + c5 + c4 + (c3 + c7 + 3) = c0 + c1 + c5 + c4 + Real.log (C_X * D_X) / (ε_F * Real.log 2) + 5 + Real.log (1 / δ₀) / Real.log 2 := by
        rw [h_const] <;> ring
      exact h_eq
    _ ≤ (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) + 400 / (τ^2 * Real.log 2) +
        (Real.log 390 + Real.log C) / (τ * Real.log 2) + c4 +
        Real.log (C_X * D_X) / (ε_F * Real.log 2) + 8 +
        Real.log (1 / δ₀) / Real.log 2 := by
      have h1 : c0 ≤ (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) := hc0_bound
      have h2 : c1 = 400 / (τ^2 * Real.log 2) := by simp [c1]
      have h3 : c5 ≤ (Real.log 390 + Real.log C) / (τ * Real.log 2) := hc5_bound
      rw [h2]
      gcongr <;> linarith

  rw [hRHS_split]
  have h_final : (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) +
      400 / (τ^2 * Real.log 2) +
      (Real.log 390 + Real.log C) / (τ * Real.log 2) +
      c4 + Real.log (C_X * D_X) / (ε_F * Real.log 2) + 8 +
      Real.log (1 / δ₀) / Real.log 2 <
      M * (2 * Real.log C) / ((σ + τ) * Real.log 2) +
      M * Real.log M / ((σ + τ) * Real.log 2) +
      M * (-Real.log c) / ((σ + τ) * Real.log 2) := by
    have h1 : (Real.log (8 / τ) - Real.log c) / (τ * Real.log 2) =
        Real.log (8 / τ) / (τ * Real.log 2) + (-Real.log c) / (τ * Real.log 2) := by
      field_simp [hτ.ne', hlog2_pos.ne'] <;> ring
    have h2 : (Real.log 390 + Real.log C) / (τ * Real.log 2) =
        Real.log 390 / (τ * Real.log 2) + Real.log C / (τ * Real.log 2) := by
      field_simp [hτ.ne', hlog2_pos.ne'] <;> ring
    have h_c4_eq : (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * (14 * τ / (1 - σ))) = c4 := by
      simp only [c4, hκ_def] <;> ring
    have hM_delta' : M * Real.log M / ((σ + τ) * Real.log 2) >
        Real.log (8 / τ) / (τ * Real.log 2) + 400 / (τ^2 * Real.log 2) +
        Real.log 390 / (τ * Real.log 2) + 8 + Real.log (1 / δ₀) / Real.log 2 +
        c4 + Real.log (C_X * D_X) / (ε_F * Real.log 2) := by
      simpa [h_c4_eq] using hM_delta
    have h_logC_nonneg : 0 ≤ Real.log C := Real.log_nonneg (by linarith)
    rw [h1, h2]
    have h_C_extra : 2 * Real.log C / (τ * Real.log 2) ≥ Real.log C / (τ * Real.log 2) := by
      have h : 2 * Real.log C ≥ Real.log C := by linarith
      have hpos : 0 < τ * Real.log 2 := by positivity
      exact div_le_div_of_nonneg_right h hpos.le
    linarith [h_part_c, h_part_C, hM_delta', h_C_extra]
  exact lt_of_le_of_lt hL_le2 h_final

end RadialBootstrapping
