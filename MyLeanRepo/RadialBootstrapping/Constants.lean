module

public import MyLeanRepo.OSWPrelude
public import MyLeanRepo.RadialBootstrapping.Basic

@[expose] public section

/-!
# Constants and Scale Selection for Radial Bootstrapping

This module defines the constants used in the proof of
`radial_bootstrapping_measure_thin_tubes` and proves the scale-selection
lemmas needed to pigeonhole a dyadic scale `r`.
-/

open MeasureTheory Metric Set

noncomputable section

namespace RadialBootstrapping

/-- The set of positive dyadic reals `{2^n : n ∈ ℤ}`. -/
def Dyadic : Set ℝ := {x | ∃ n : ℤ, x = (2 : ℝ) ^ n}

/-- Positive dyadic reals bounded above by `R`. -/
def DyadicLe (R : ℝ) : Set ℝ := {x ∈ Dyadic | 0 < x ∧ x ≤ R}

lemma dyadic_le_countable (R : ℝ) : Set.Countable (DyadicLe R) := by
  have h : DyadicLe R ⊆ Set.range (fun n : ℤ => (2 : ℝ) ^ n) := by
    intro x hx
    have h2 : x ∈ Dyadic := hx.1
    rcases h2 with ⟨n, rfl⟩
    exact ⟨n, by norm_num⟩
  exact Set.Countable.mono h (Set.countable_range _)

/-! ### Choice of constants -/

/-- Given `β, ε > 0`, there exist `η > 0` and `M ≥ 1` such that all the
inequalities needed in the proof hold. -/
lemma exists_eta_M (β ε : ℝ) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ (η : ℝ), 0 < η ∧
      ∃ (M : ℝ), 1 ≤ M ∧
      (∀ σ ∈ Set.Icc β (1 - ε), η < (1 - σ) / 14) := by
  use ε / 100
  constructor
  · linarith
  · use 100
    constructor
    · norm_num
    · intro σ hσ
      have h1 : 1 - σ ≥ ε := by linarith [hσ.2]
      have h2 : ε / 100 < (1 - σ) / 14 := by
        calc
          ε / 100 < ε / 14 := by gcongr <;> norm_num
          _ ≤ (1 - σ) / 14 := by gcongr
      exact h2

/-- Strengthened parameter existence: given `β, ε > 0` and a Furstenberg
uniformity bound `ε_F > 0`, there exist `η > 0` and `M ≥ 1` satisfying all
parameter conditions uniformly for `σ ∈ [β, 1-ε]`:

1. `η < (1-σ)/14` (so `κ = 14η/(1-σ) < 1`)
2. `8η + 14η/(1-σ) < √η` (non-concentrated case contradiction)
3. `3η < 1-σ` (concentrated case)
4. `η < ε_F` (Furstenberg estimate compatibility)
5. `(1+η)/η < M` (first condition for `K' · r₀^(σ+η) > 1`)

The `ε_F` parameter should be extracted from the discretised Furstenberg
estimate axiom's compact-uniformity property applied to the relevant
parameter range. -/
lemma exists_eta_M_full (β ε ε_F : ℝ)
    (hβ : 0 < β) (hε : 0 < ε) (hεF : 0 < ε_F) :
    ∃ (η : ℝ), 0 < η ∧
      ∃ (M : ℝ), 1 ≤ M ∧
        (∀ σ ∈ Set.Icc β (1 - ε), η < (1 - σ) / 14) ∧
        (∀ σ ∈ Set.Icc β (1 - ε), 8 * η + 14 * η / (1 - σ) < Real.sqrt η) ∧
        (∀ σ ∈ Set.Icc β (1 - ε), 3 * η < 1 - σ) ∧
        (∀ σ ∈ Set.Icc β (1 - ε), η < ε_F) ∧
        (∀ σ ∈ Set.Icc β (1 - ε), (1 + η) / η < M) := by
  let A : ℝ := 8 + 14 / ε
  have hA_pos : 0 < A := by positivity
  let b_epsF : ℝ := if ε_F < 1 then ε_F^2 / 2 else 1 / 2
  have h_b_epsF_pos : 0 < b_epsF := by
    dsimp only [b_epsF]; split_ifs <;> positivity
  have h_b_epsF_lt : b_epsF < ε_F := by
    dsimp only [b_epsF]
    split_ifs with h
    · -- ε_F < 1
      have h1 : 0 < ε_F := hεF
      nlinarith
    · -- ε_F ≥ 1
      have h2 : ε_F ≥ 1 := by linarith
      have h3 : (1 / 2 : ℝ) < ε_F := by linarith
      exact h3
  let η : ℝ := min (min (ε / 100) b_epsF) (min (1 / (2 * A^2)) (ε / 10))
  have hη_pos : 0 < η := by positivity
  have hη_le_eps100 : η ≤ ε / 100 :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hη_le_epsF : η ≤ b_epsF :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hη_le_1A2 : η ≤ 1 / (2 * A^2) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hη_le_eps10 : η ≤ ε / 10 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hη_lt_epsF : η < ε_F := by
    calc η ≤ b_epsF := hη_le_epsF
      _ < ε_F := h_b_epsF_lt
  have h1 : ∀ σ ∈ Set.Icc β (1 - ε), η < (1 - σ) / 14 := by
    intro σ hσ
    have h11 : 1 - σ ≥ ε := by linarith [hσ.2]
    have h12 : η < ε / 14 := by
      have h : η ≤ ε / 100 := hη_le_eps100
      have h' : ε / 100 < ε / 14 := by gcongr <;> norm_num
      linarith
    have h13 : ε / 14 ≤ (1 - σ) / 14 := by gcongr
    linarith
  have h3 : ∀ σ ∈ Set.Icc β (1 - ε), 8 * η + 14 * η / (1 - σ) < Real.sqrt η := by
    intro σ hσ
    have h11 : 1 - σ ≥ ε := by linarith [hσ.2]
    have h12 : 0 < 1 - σ := by linarith
    have h13 : 14 * η / (1 - σ) ≤ 14 * η / ε := by gcongr <;> linarith
    have h14 : 8 * η + 14 * η / (1 - σ) ≤ η * A := by
      have h15 : 8 * η + 14 * η / ε = η * A := by dsimp only [A]; ring
      linarith
    have h16 : η < 1 / A^2 := by
      calc η ≤ 1 / (2 * A^2) := hη_le_1A2
        _ < 1 / A^2 := by
          have h17 : 0 < A^2 := by positivity
          have h18 : (1 : ℝ) / (2 * A^2) < 1 / A^2 := by
            apply one_div_lt_one_div_of_lt
            · positivity
            · nlinarith
          exact h18
    have h_sqrt_lt : Real.sqrt η < 1 / A := by
      have h_pos2 : 0 < 1 / A := by positivity
      have h_sq : (Real.sqrt η)^2 < (1 / A)^2 := by
        have h1 : (Real.sqrt η)^2 = η := Real.sq_sqrt (by linarith)
        have h2 : (1 / A)^2 = 1 / A^2 := by field_simp [hA_pos.ne'] <;> ring
        rw [h1, h2]; exact h16
      nlinarith [Real.sqrt_nonneg η]
    have h_alt_lt_one : Real.sqrt η * A < 1 := by
      have h : Real.sqrt η < 1 / A := h_sqrt_lt
      have h2 : Real.sqrt η * A < (1 / A) * A := by gcongr
      have h3 : (1 / A) * A = 1 := by field_simp [hA_pos.ne'] <;> ring
      rw [h3] at h2; exact h2
    have h21 : η * A < Real.sqrt η := by
      have h22 : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη_pos
      have h23 : Real.sqrt η * Real.sqrt η = η := Real.mul_self_sqrt (by linarith)
      have h24 : η * A = Real.sqrt η * (Real.sqrt η * A) := by
        calc η * A = (Real.sqrt η * Real.sqrt η) * A := by rw [h23]
          _ = Real.sqrt η * (Real.sqrt η * A) := by ring
      rw [h24]
      have h25 : Real.sqrt η * A < 1 := h_alt_lt_one
      have h26 : Real.sqrt η * (Real.sqrt η * A) < Real.sqrt η * 1 :=
        mul_lt_mul_of_pos_left h25 h22
      simpa using h26
    exact h14.trans_lt h21
  have h4 : ∀ σ ∈ Set.Icc β (1 - ε), 3 * η < 1 - σ := by
    intro σ hσ
    have h11 : 1 - σ ≥ ε := by linarith [hσ.2]
    have h12 : 3 * η ≤ 3 * (ε / 10) := by gcongr
    have h13 : 3 * (ε / 10) < ε := by
      have h14 : 0 < ε := hε; nlinarith
    linarith
  have h2 : ∀ σ ∈ Set.Icc β (1 - ε), η < ε_F := fun _ _ => hη_lt_epsF
  let M : ℝ := 2 * ((1 + η) / η) + 10
  have hM_ge1 : 1 ≤ M := by
    dsimp only [M]
    have h_pos1 : 0 < (1 + η) / η := by positivity
    linarith
  have hM_cond : ∀ σ ∈ Set.Icc β (1 - ε), (1 + η) / η < M := by
    intro σ _
    dsimp only [M]
    have h_pos1 : 0 < (1 + η) / η := by positivity
    linarith
  exact ⟨η, hη_pos, M, hM_ge1, h1, h3, h4, h2, hM_cond⟩

/-- Given `η, c > 0`, there exists `N : ℕ` such that the sum of `2 * r^η`
over all dyadic `r = 2^{-(n+N)}` for `n ∈ ℕ` is `< c`. This is the
geometric-series tail bound. -/
lemma exists_r2 (η c : ℝ) (hη : 0 < η) (hc : 0 < c) :
    ∃ (N : ℕ),
      ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ η) < ENNReal.ofReal c := by
  let a : ℝ := (2 : ℝ) ^ (-η)
  have ha_pos : 0 < a := by positivity
  have ha_nonneg : 0 ≤ a := by positivity
  have ha_lt_one : a < 1 := by
    dsimp only [a]
    have h : (2 : ℝ) ^ (-η) < (2 : ℝ) ^ (0 : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt
      · norm_num
      · linarith
    simpa using h
  have h_eq1 : ∀ (N n : ℕ), ((2 : ℝ) ^ (-(n + N : ℝ))) ^ η = a ^ (n + N) := by
    intro N n
    have h_exp : (-(n + N : ℝ)) * η = -η * (n + N : ℝ) := by ring
    calc
      ((2 : ℝ) ^ (-(n + N : ℝ))) ^ η
        = (2 : ℝ) ^ ((-(n + N : ℝ)) * η) := by rw [← Real.rpow_mul (by norm_num)] <;> ring
      _ = (2 : ℝ) ^ (-η * (n + N : ℝ)) := by rw [h_exp]
      _ = ((2 : ℝ) ^ (-η)) ^ (n + N : ℝ) := by
        rw [← Real.rpow_mul (by norm_num)] <;> ring
      _ = a ^ (n + N) := by
        simp only [a]
        <;> norm_cast
  have h_eq2 : ∀ (N n : ℕ), (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ η) = 2 * a ^ (n + N) := by
    intro N n
    rw [h_eq1 N n] <;> ring
  have h_geom : ∑' n : ℕ, a ^ n = 1 / (1 - a) := by
    rw [tsum_geometric_of_lt_one ha_nonneg ha_lt_one] <;> ring
  have h_summable_a : Summable (fun n : ℕ => a ^ n) := by
    exact summable_geometric_of_lt_one ha_nonneg ha_lt_one
  have h_main : ∀ (N : ℕ), ∑' n : ℕ, (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ η) = 2 * a ^ N * (1 / (1 - a)) := by
    intro N
    have h5 : ∀ n : ℕ, (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ η) = 2 * a ^ N * a ^ n := by
      intro n
      rw [h_eq2 N n]
      have h6 : a ^ (n + N) = a ^ N * a ^ n := by
        rw [pow_add]
        <;> ring
      rw [h6] <;> ring
    simp_rw [h5]
    rw [tsum_mul_left, h_geom] <;> ring
  have h_summable : ∀ (N : ℕ), Summable (fun n : ℕ => (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ η)) := by
    intro N
    have h5 : ∀ n : ℕ, (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ η) = 2 * a ^ N * a ^ n := by
      intro n
      rw [h_eq2 N n]
      have h6 : a ^ (n + N) = a ^ N * a ^ n := by rw [pow_add] <;> ring
      rw [h6] <;> ring
    simp_rw [h5]
    exact h_summable_a.mul_left _
  have h5 : ∃ N : ℕ, 2 * a ^ N * (1 / (1 - a)) < c := by
    have h61 : Filter.Tendsto (fun N : ℕ => a ^ N) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one ha_nonneg ha_lt_one
    have h6 : Filter.Tendsto (fun N : ℕ => 2 * a ^ N * (1 / (1 - a))) Filter.atTop (nhds 0) := by
      have h7 : (fun N : ℕ => 2 * a ^ N * (1 / (1 - a))) = fun N : ℕ => (2 * (1 / (1 - a))) * a ^ N := by
        funext N <;> ring
      rw [h7]
      have h8 : Filter.Tendsto (fun x : ℕ => (2 * (1 / (1 - a))) * a ^ x) Filter.atTop (nhds ((2 * (1 / (1 - a))) * 0)) :=
        Filter.Tendsto.const_mul (2 * (1 / (1 - a))) h61
      simpa using h8
    exact (h6.eventually (gt_mem_nhds hc)).exists
  rcases h5 with ⟨N, hN⟩
  refine' ⟨N, _⟩
  have h_nonneg : ∀ n : ℕ, 0 ≤ (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ η) := by
    intro n <;> positivity
  have h7 : ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ η) =
      ENNReal.ofReal (∑' n : ℕ, (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ η)) := by
    exact (ENNReal.ofReal_tsum_of_nonneg h_nonneg (h_summable N)).symm
  rw [h7, h_main N]
  have h8 : 0 < c := hc
  rw [ENNReal.ofReal_lt_ofReal_iff h8]
  exact hN

/-- Choose `N` using the existence lemma. The corresponding scale is `r₂ = 2^{-N}`. -/
def chooseN (η c : ℝ) (hη : 0 < η) (hc : 0 < c) : ℕ :=
  Classical.choose (exists_r2 η c hη hc)

/-- `r₂ = 2^{-N}` where `N` is chosen so that the geometric tail is small. -/
def chooseR2 (η c : ℝ) (hη : 0 < η) (hc : 0 < c) : ℝ :=
  (2 : ℝ) ^ (-(chooseN η c hη hc : ℝ))

/-- Helper: for `y ≥ 1` and `ε > 0`, `log y ≤ y^ε / ε`. -/
lemma log_le_rpow_div (y ε : ℝ) (hy : 1 ≤ y) (hε : 0 < ε) :
    Real.log y ≤ y ^ ε / ε := by
  have h_pos : 0 < y := by linarith
  have h1 : Real.log (y ^ ε) ≤ y ^ ε - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log (y ^ ε) = ε * Real.log y := by
    rw [Real.log_rpow (by linarith)] <;> ring
  have h3 : ε * Real.log y ≤ y ^ ε - 1 := by linarith
  have h4 : Real.log y ≤ (y ^ ε - 1) / ε := by
    calc Real.log y = (ε * Real.log y) / ε := by field_simp [hε.ne'] <;> ring
      _ ≤ (y ^ ε - 1) / ε := by gcongr
  have h5 : (y ^ ε - 1) / ε ≤ y ^ ε / ε := by
    have h6 : y ^ ε - 1 ≤ y ^ ε := by linarith
    gcongr
  linarith

/-- Given `C, σ, η` with `3η < 1-σ`, there exists `r₁ > 0` such that for all
`0 < r ≤ r₁`:
1. `r^η * log(1/r) ≤ 1/100`
2. `20 * C * r^η < 1`
3. `C * r ≤ (1/6) * r^(σ+3*η)`
4. `r < 1` -/
lemma exists_r1 (C σ η : ℝ) (hC : 1 ≤ C) (hσ : 0 ≤ σ) (hη : 0 < η)
    (h3η : 3 * η < 1 - σ) :
    ∃ r1 : ℝ, 0 < r1 ∧ ∀ r : ℝ, 0 < r → r ≤ r1 →
      (r ^ η * Real.log (1 / r) ≤ 1 / 100) ∧
      (20 * C * r ^ η < 1) ∧
      (C * r ≤ (1 / 6 : ℝ) * r ^ (σ + 3 * η)) ∧
      (r < 1) := by
  have hC_pos : 0 < C := by linarith
  set α : ℝ := 1 - σ - 3 * η with hα_def
  have hα_pos : 0 < α := by linarith
  -- Condition 1: explicit bound using log y ≤ y^ε / ε
  let ε1 := ((η / 200) ^ (2 / η))
  have hε1_pos : 0 < ε1 := by positivity
  have h1 : ∀ r, 0 < r → r ≤ ε1 → r ^ η * Real.log (1 / r) ≤ 1 / 100 := by
    intro r hr hr2
    have h_r_le_1 : r ≤ 1 := by
      have h : ε1 ≤ 1 := by
        have h2 : η / 200 ≤ 1 := by linarith
        have h3 : (η / 200) ^ (2 / η) ≤ (1 : ℝ) ^ (2 / η) := Real.rpow_le_rpow (by linarith) h2 (by positivity)
        simpa using h3
      linarith
    have h_log_bound : Real.log (1 / r) ≤ (1 / r) ^ (η / 2) / (η / 2) := by
      apply log_le_rpow_div (1 / r) (η / 2) _ (by linarith)
      have h4 : 1 ≤ 1 / r := by
        apply one_le_one_div hr
        linarith
      exact h4
    have h5 : r ^ η * Real.log (1 / r) ≤ r ^ η * ((1 / r) ^ (η / 2) / (η / 2)) := by gcongr
    have h6 : r ^ η * ((1 / r) ^ (η / 2) / (η / 2)) = (2 / η) * r ^ (η / 2) := by
      have h71 : (1 / r) = r ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one] <;> field_simp
      have h7 : (1 / r) ^ (η / 2) = r ^ (-(η / 2)) := by
        rw [h71]
        have h72 : (r ^ (-1 : ℝ)) ^ (η / 2) = r ^ ((-1 : ℝ) * (η / 2)) := by
          rw [← Real.rpow_mul (by linarith)]
        rw [h72]
        have h73 : (-1 : ℝ) * (η / 2) = -(η / 2) := by ring
        rw [h73]
      have h_eq1 : r ^ η * ((1 / r) ^ (η / 2) / (η / 2)) = (r ^ η * (1 / r) ^ (η / 2)) / (η / 2) := by ring
      rw [h_eq1, h7]
      have h_sum : η + (-(η / 2)) = η / 2 := by ring
      have h8 : r ^ η * r ^ (-(η / 2)) = r ^ (η / 2) := by
        have h_add : r ^ η * r ^ (-(η / 2)) = r ^ (η + (-(η / 2))) := by
          rw [← Real.rpow_add (by linarith)]
        rw [h_add, h_sum]
      rw [h8]
      have h9 : (r ^ (η / 2)) / (η / 2) = (2 / η) * r ^ (η / 2) := by
        field_simp [hη.ne'] <;> ring
      exact h9
    rw [h6] at h5
    have h9 : r ^ (η / 2) ≤ ε1 ^ (η / 2) := by gcongr <;> linarith
    have h10 : ε1 ^ (η / 2) = η / 200 := by
      have h_pos : 0 ≤ η / 200 := by positivity
      have h : ε1 ^ (η / 2) = (η / 200) ^ ((2 / η) * (η / 2)) := by
        rw [show ε1 = (η / 200) ^ (2 / η) from rfl]
        rw [← Real.rpow_mul h_pos]
      rw [h]
      have h9 : (2 / η) * (η / 2) = 1 := by
        field_simp [hη.ne'] <;> ring
      rw [h9] <;> simp
    rw [h10] at h9
    have h11 : (2 / η) * r ^ (η / 2) ≤ (2 / η) * (η / 200) := by gcongr
    have h12 : (2 / η) * (η / 200) = 1 / 100 := by
      field_simp [hη.ne'] <;> ring
    rw [h12] at h11
    linarith
  -- Condition 2
  let ε2 := (1 / (40 * C)) ^ (1 / η)
  have hε2_pos : 0 < ε2 := by positivity
  have h2 : ∀ r, 0 < r → r ≤ ε2 → 20 * C * r ^ η < 1 := by
    intro r hr hr2
    have h : r ^ η ≤ ε2 ^ η := by gcongr <;> linarith
    have h2eq : ε2 ^ η = 1 / (40 * C) := by
      have h_pos : 0 ≤ 1 / (40 * C) := by positivity
      have h : ε2 ^ η = (1 / (40 * C)) ^ ((1 / η) * η) := by
        rw [show ε2 = (1 / (40 * C)) ^ (1 / η) from rfl]
        rw [← Real.rpow_mul h_pos]
      rw [h]
      have h9 : (1 / η) * η = 1 := by
        field_simp [hη.ne'] <;> ring
      rw [h9] <;> simp
    rw [h2eq] at h
    have h3 : 20 * C * r ^ η ≤ 20 * C * (1 / (40 * C)) := by gcongr
    have h4 : 20 * C * (1 / (40 * C)) = 1 / 2 := by
      field_simp [hC_pos.ne'] <;> ring
    rw [h4] at h3
    linarith
  -- Condition 3
  let ε3 := (1 / (6 * C)) ^ (1 / α)
  have hε3_pos : 0 < ε3 := by positivity
  have h3 : ∀ r, 0 < r → r ≤ ε3 → C * r ≤ (1 / 6 : ℝ) * r ^ (σ + 3 * η) := by
    intro r hr hr2
    have h_rα_le : r ^ α ≤ ε3 ^ α := by gcongr <;> linarith
    have h_ε3α : ε3 ^ α = 1 / (6 * C) := by
      have h_pos : 0 ≤ 1 / (6 * C) := by positivity
      have h : ε3 ^ α = (1 / (6 * C)) ^ ((1 / α) * α) := by
        rw [show ε3 = (1 / (6 * C)) ^ (1 / α) from rfl]
        rw [← Real.rpow_mul h_pos]
      rw [h]
      have h9 : (1 / α) * α = 1 := by
        field_simp [hα_pos.ne'] <;> ring
      rw [h9]
      simp
    rw [h_ε3α] at h_rα_le
    have h5 : r ^ (σ + 3 * η) = r ^ (1 - α) := by
      have h6 : σ + 3 * η = 1 - α := by linarith [hα_def]
      rw [h6]
    rw [h5]
    have h7 : r ^ (1 - α) = r / r ^ α := by
      have h8 : r ^ (1 - α) = r ^ (1 : ℝ) / r ^ α := by
        rw [Real.rpow_sub (by linarith)] <;> ring
      rw [h8] <;> simp
    rw [h7]
    have h10 : 0 < r ^ α := by positivity
    have h11 : C * r ^ α ≤ 1 / 6 := by
      calc C * r ^ α ≤ C * (1 / (6 * C)) := by gcongr
        _ = 1 / 6 := by field_simp [hC_pos.ne'] <;> ring
    have h12 : C ≤ 1 / (6 * r ^ α) := by
      calc C = (C * r ^ α) / r ^ α := by field_simp [h10.ne'] <;> ring
        _ ≤ (1 / 6) / r ^ α := by gcongr
        _ = 1 / (6 * r ^ α) := by ring
    have h9 : C * r ≤ (1 / 6 : ℝ) * (r / r ^ α) := by
      calc C * r ≤ (1 / (6 * r ^ α)) * r := by gcongr
        _ = (1 / 6 : ℝ) * (r / r ^ α) := by ring
    exact h9
  -- Condition 4
  let ε4 := (1 : ℝ) / 2
  -- Take minimum
  let r1 := min ε1 (min ε2 (min ε3 ε4))
  have hr1_pos : 0 < r1 := by positivity
  refine ⟨r1, hr1_pos, fun r hr hr2 => ?_⟩
  have h_r_le_ε1 : r ≤ ε1 := le_trans hr2 (min_le_left _ _)
  have h_r_le_ε2 : r ≤ ε2 := le_trans hr2 (le_trans (min_le_right _ _) (min_le_left _ _))
  have h_r_le_ε3 : r ≤ ε3 := le_trans hr2 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have h_r_le_ε4 : r ≤ ε4 := le_trans hr2 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  exact ⟨h1 r hr h_r_le_ε1, h2 r hr h_r_le_ε2, h3 r hr h_r_le_ε3,
    have h41 : r ≤ 1 / 2 := by simpa [ε4] using h_r_le_ε4
    by linarith⟩

/-- Given `C, σ, η`, choose `r₁ > 0` small enough for all Frostman and
discretization estimates. -/
def chooseR1 (C σ η : ℝ) (hC : 1 ≤ C) (hσ : 0 ≤ σ) (hη : 0 < η)
    (h3η : 3 * η < 1 - σ) : ℝ :=
  Classical.choose (exists_r1 C σ η hC hσ hη h3η)

/-- Specification for `chooseR1`: all four conditions hold for `0 < r ≤ chooseR1`. -/
lemma chooseR1_spec (C σ η : ℝ) (hC : 1 ≤ C) (hσ : 0 ≤ σ) (hη : 0 < η)
    (h3η : 3 * η < 1 - σ) :
    ∀ r : ℝ, 0 < r → r ≤ chooseR1 C σ η hC hσ hη h3η →
      (r ^ η * Real.log (1 / r) ≤ 1 / 100) ∧
      (20 * C * r ^ η < 1) ∧
      (C * r ≤ (1 / 6 : ℝ) * r ^ (σ + 3 * η)) ∧
      (r < 1) :=
  (Classical.choose_spec (exists_r1 C σ η hC hσ hη h3η)).2

/-- `r₀ = min(K^{-1/η}, r₂)`. -/
def chooseR0 (K η r2 : ℝ) (hK : 1 ≤ K) (hη : 0 < η) : ℝ :=
  min (K ^ (-(1 / η))) r2

/-- `K' = max(K, C^2 * M / c)^M`. -/
def chooseK' (K C M c : ℝ) : ℝ :=
  Real.rpow (max K (C ^ 2 * M / c)) M

/-! ### Key inequalities -/

/-- If `K'` is chosen large enough (via `M`), then `K' * r₀^(σ+η) > 1`.

We require two lower bounds on `M`:
1. `M > (σ+η)/η` — handles the case where `r₀ = K^{-1/η}`
2. `(C²M/c)^M > 2^{N(σ+η)}` — handles the case where `r₀ = r₂ = 2^{-N}`

Here `r₀ = min(K^{-1/η}, r₂)`. -/
lemma K'_r0_power_gt_one (β ε σ c K C η M : ℝ)
    (hβ : 0 < β) (hε : 0 < ε)
    (hσ : σ ∈ Set.Icc β (1 - ε))
    (hc : c ∈ Set.Ioo (0 : ℝ) (1 / 10))
    (hK : 1 ≤ K) (hC : 1 ≤ C)
    (hη : 0 < η) (hM : 1 ≤ M)
    (hM1 : M > (σ + η) / η)
    (hM2 : (C ^ 2 * M / c) ^ M > (2 : ℝ) ^ ((chooseN η c hη hc.1 : ℝ) * (σ + η)))
    (r0 : ℝ) (hr0 : 0 < r0)
    (h_r0_def : r0 = chooseR0 K η (chooseR2 η c hη hc.1) hK hη) :
    1 < chooseK' K C M c * r0 ^ (σ + η) := by
  set N : ℕ := chooseN η c hη hc.1 with hN_def
  set r2 : ℝ := chooseR2 η c hη hc.1 with hr2_def
  have hN_sum : ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ η) < ENNReal.ofReal c :=
    Classical.choose_spec (exists_r2 η c hη hc.1)
  have hN_pos : 1 ≤ N := by
    by_contra h
    have h0 : N = 0 := by omega
    have h_sum0 := hN_sum
    simp [h0] at h_sum0
    have ha_pos : 0 < (2 : ℝ) ^ (-η) := by positivity
    have ha_nonneg : 0 ≤ (2 : ℝ) ^ (-η) := by positivity
    have ha_lt_one : (2 : ℝ) ^ (-η) < 1 := by
      have h : (2 : ℝ) ^ (-η) < (2 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      simpa using h
    have h_geom_real : ∑' n : ℕ, (2 * ((2 : ℝ) ^ (-(n : ℝ))) ^ η) = 2 / (1 - (2 : ℝ) ^ (-η)) := by
      have h1 : ∀ n : ℕ, ((2 : ℝ) ^ (-(n : ℝ))) ^ η = ((2 : ℝ) ^ (-η)) ^ n := by
        intro n
        have h2 : ((2 : ℝ) ^ (-(n : ℝ))) ^ η = (2 : ℝ) ^ (-(n : ℝ) * η) := by
          rw [← Real.rpow_mul (by norm_num)] <;> ring
        rw [h2]
        have h3 : (-(n : ℝ) * η) = -η * (n : ℝ) := by ring
        rw [h3]
        have h4 : (2 : ℝ) ^ (-η * (n : ℝ)) = ((2 : ℝ) ^ (-η)) ^ (n : ℝ) := by
          rw [← Real.rpow_mul (by norm_num)] <;> ring
        norm_cast at h4 ⊢
        <;> exact h4
      simp_rw [h1]
      rw [tsum_mul_left, tsum_geometric_of_lt_one ha_nonneg ha_lt_one] <;> ring
    have h_summable : Summable (fun n : ℕ => (2 * ((2 : ℝ) ^ (-(n : ℝ))) ^ η)) := by
      have h1 : ∀ n : ℕ, (2 * ((2 : ℝ) ^ (-(n : ℝ))) ^ η) = 2 * ((2 : ℝ) ^ (-η)) ^ n := by
        intro n
        have h2 : ((2 : ℝ) ^ (-(n : ℝ))) ^ η = ((2 : ℝ) ^ (-η)) ^ n := by
          have h3 : ((2 : ℝ) ^ (-(n : ℝ))) ^ η = (2 : ℝ) ^ (-(n : ℝ) * η) := by
            rw [← Real.rpow_mul (by norm_num)] <;> ring
          rw [h3]
          have h4 : (-(n : ℝ) * η) = -η * (n : ℝ) := by ring
          rw [h4]
          have h5 : (2 : ℝ) ^ (-η * (n : ℝ)) = ((2 : ℝ) ^ (-η)) ^ (n : ℝ) := by
            rw [← Real.rpow_mul (by norm_num)] <;> ring
          norm_cast at h5 ⊢ <;> exact h5
        rw [h2] <;> ring
      simp_rw [h1]
      exact (summable_geometric_of_lt_one ha_nonneg ha_lt_one).mul_left 2
    have h_nonneg : ∀ n : ℕ, 0 ≤ (2 * ((2 : ℝ) ^ (-(n : ℝ))) ^ η) := by intro n; positivity
    have h9 : ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n : ℝ))) ^ η) =
        ENNReal.ofReal (∑' n : ℕ, (2 * ((2 : ℝ) ^ (-(n : ℝ))) ^ η)) := by
      exact (ENNReal.ofReal_tsum_of_nonneg h_nonneg h_summable).symm
    have h10 : 2 / (1 - (2 : ℝ) ^ (-η)) > 2 := by
      have h11 : 0 < 1 - (2 : ℝ) ^ (-η) := by linarith [ha_lt_one]
      have h12 : 1 - (2 : ℝ) ^ (-η) < 1 := by linarith [ha_pos]
      have h13 : 2 / (1 - (2 : ℝ) ^ (-η)) > 2 / 1 := by
        gcongr
      simpa using h13
    have h_sum1 : ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n : ℝ))) ^ η) =
        ENNReal.ofReal (2 / (1 - (2 : ℝ) ^ (-η))) := by
      rw [h9, h_geom_real]
    have h_eq : ∑' n : ℕ, 2 * ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹ ^ η) =
        ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n : ℝ))) ^ η) := by
      congr with n
      have h_pos : 0 ≤ ((2 : ℝ) ^ n)⁻¹ ^ η := by positivity
      have h_eq2 : ((2 : ℝ) ^ n)⁻¹ = (2 : ℝ) ^ (-(n : ℝ)) := by
        have h23 : (2 : ℝ) ^ (-(n : ℝ)) = ((2 : ℝ) ^ (n : ℝ))⁻¹ := by
          rw [Real.rpow_neg (by norm_num)]
        have h24 : (2 : ℝ) ^ (n : ℝ) = (2 : ℝ) ^ n := by norm_cast
        rw [h24] at h23
        exact h23.symm
      rw [h_eq2]
      rw [ENNReal.ofReal_mul (by positivity)]
      <;> norm_num
    rw [h_eq] at h_sum0
    have h_contra : ENNReal.ofReal (2 / (1 - (2 : ℝ) ^ (-η))) < ENNReal.ofReal c := by
      rw [← h_sum1]
      exact h_sum0
    have h14 : 2 / (1 - (2 : ℝ) ^ (-η)) < c := by
      have hpos : 0 < c := hc.1
      exact (ENNReal.ofReal_lt_ofReal_iff hpos).mp h_contra
    have h15 : c < 1 / 10 := hc.2
    have h16 : (2 : ℝ) / (1 - (2 : ℝ) ^ (-η)) > 2 := h10
    have h18 : (2 : ℝ) < c := by
      exact lt_trans h16 h14
    have h19 : (2 : ℝ) < 1 / 10 := lt_trans h18 h15
    norm_num at h19
  have hr2_eq : r2 = (2 : ℝ) ^ (-(N : ℝ)) := by
    simp [hr2_def, chooseR2, hN_def]
    <;> rfl
  have hr0_simp : r0 = min (K ^ (-(1 / η))) r2 := by
    rw [h_r0_def, chooseR0]
  have hK'_ge_K : chooseK' K C M c ≥ K ^ M := by
    have h1 : max K (C ^ 2 * M / c) ≥ K := le_max_left _ _
    have h2 : 0 ≤ K := by linarith
    have h3 : 0 ≤ max K (C ^ 2 * M / c) := by positivity
    calc
      chooseK' K C M c = (max K (C ^ 2 * M / c)) ^ M := by simp [chooseK'] <;> rfl
      _ ≥ K ^ M := by gcongr
  have hC2M_pos : 0 < C ^ 2 * M / c := by
    have hc_pos : 0 < c := hc.1
    positivity
  have hK'_ge_C2M : chooseK' K C M c ≥ (C ^ 2 * M / c) ^ M := by
    have h1 : max K (C ^ 2 * M / c) ≥ C ^ 2 * M / c := le_max_right _ _
    have h2 : 0 ≤ C ^ 2 * M / c := by positivity
    calc
      chooseK' K C M c = (max K (C ^ 2 * M / c)) ^ M := by simp [chooseK'] <;> rfl
      _ ≥ (C ^ 2 * M / c) ^ M := by gcongr
  by_cases h_case : K ^ (-(1 / η)) ≤ r2
  · -- Case 1: r0 = K^{-1/η}
    have hr0_eq : r0 = K ^ (-(1 / η)) := by
      rw [hr0_simp]
      rw [min_eq_left h_case]
    have hK_gt_one : 1 < K := by
      by_contra h
      have hK_eq : K = 1 := by linarith
      rw [hK_eq] at h_case
      have h_one : (1 : ℝ) ^ (-(1 / η)) = 1 := by simp
      rw [h_one] at h_case
      have h_r2_ge_one : r2 ≥ 1 := h_case
      have h_r2_le_half : r2 ≤ 1 / 2 := by
        rw [hr2_eq]
        have hN1 : (N : ℝ) ≥ 1 := by exact_mod_cast hN_pos
        have h : (2 : ℝ) ^ (-(N : ℝ)) ≤ (2 : ℝ) ^ (-1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le
          · norm_num
          · linarith
        have h2 : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by norm_num
        rw [h2] at h
        exact h
      have h_contra : (1 : ℝ) ≤ 1 / 2 := le_trans h_r2_ge_one h_r2_le_half
      norm_num at h_contra
    have h_power : (K ^ (-(1 / η))) ^ (σ + η) = K ^ (-(σ + η) / η) := by
      have h5 : (K ^ (-(1 / η))) ^ (σ + η) = K ^ (-(1 / η) * (σ + η)) := by
        rw [← Real.rpow_mul (by linarith)] <;> ring
      rw [h5]
      have h6 : (-(1 / η) * (σ + η)) = (-(σ + η) / η) := by ring
      rw [h6]
    have h_main : 1 < chooseK' K C M c * (K ^ (-(1 / η))) ^ (σ + η) := by
      rw [h_power]
      have h7 : chooseK' K C M c * K ^ (-(σ + η) / η) ≥ K ^ M * K ^ (-(σ + η) / η) := by
        have h_pos2 : 0 ≤ K ^ (-(σ + η) / η) := by positivity
        exact mul_le_mul_of_nonneg_right hK'_ge_K h_pos2
      have h8 : K ^ M * K ^ (-(σ + η) / η) = K ^ (M - (σ + η) / η) := by
        have h81 : K ^ M * K ^ (-(σ + η) / η) = K ^ (M + (-(σ + η) / η)) := by
          rw [← Real.rpow_add (by linarith)]
        rw [h81]
        have h82 : M + (-(σ + η) / η) = M - (σ + η) / η := by ring
        rw [h82]
      rw [h8] at h7
      have h9 : M - (σ + η) / η > 0 := by linarith
      have h10 : 1 < K ^ (M - (σ + η) / η) := by
        apply Real.one_lt_rpow <;> linarith
      exact h10.trans_le h7
    rw [hr0_eq]
    exact h_main
  · -- Case 2: r0 = r2
    have h_case2 : r2 < K ^ (-(1 / η)) := by exact lt_of_not_ge h_case
    have hr0_eq : r0 = r2 := by
      rw [hr0_simp]
      rw [min_eq_right h_case2.le]
    have h_power : ((2 : ℝ) ^ (-(N : ℝ))) ^ (σ + η) = (2 : ℝ) ^ (-(N : ℝ) * (σ + η)) := by
      rw [← Real.rpow_mul (by norm_num)] <;> ring
    have h_main : 1 < chooseK' K C M c * ((2 : ℝ) ^ (-(N : ℝ))) ^ (σ + η) := by
      rw [h_power]
      have h5 : chooseK' K C M c * (2 : ℝ) ^ (-(N : ℝ) * (σ + η)) ≥
          (C ^ 2 * M / c) ^ M * (2 : ℝ) ^ (-(N : ℝ) * (σ + η)) := by
        gcongr <;> linarith
      have h7 : (C ^ 2 * M / c) ^ M > (2 : ℝ) ^ ((N : ℝ) * (σ + η)) := hM2
      have h8 : (2 : ℝ) ^ (-(N : ℝ) * (σ + η)) > 0 := by positivity
      have h9 : (C ^ 2 * M / c) ^ M * (2 : ℝ) ^ (-(N : ℝ) * (σ + η)) >
          (2 : ℝ) ^ ((N : ℝ) * (σ + η)) * (2 : ℝ) ^ (-(N : ℝ) * (σ + η)) := by
        gcongr
      have h10 : (2 : ℝ) ^ ((N : ℝ) * (σ + η)) * (2 : ℝ) ^ (-(N : ℝ) * (σ + η)) = 1 := by
        have h11 : (N : ℝ) * (σ + η) + (-(N : ℝ) * (σ + η)) = 0 := by ring
        have h12 : (2 : ℝ) ^ ((N : ℝ) * (σ + η)) * (2 : ℝ) ^ (-(N : ℝ) * (σ + η)) =
            (2 : ℝ) ^ ((N : ℝ) * (σ + η) + (-(N : ℝ) * (σ + η))) := by
          rw [← Real.rpow_add (by norm_num)] <;> ring
        rw [h12, h11]
        <;> norm_num
      have h13 : (C ^ 2 * M / c) ^ M * (2 : ℝ) ^ (-(N : ℝ) * (σ + η)) > 1 := by
        calc
          (C ^ 2 * M / c) ^ M * (2 : ℝ) ^ (-(N : ℝ) * (σ + η))
            > (2 : ℝ) ^ ((N : ℝ) * (σ + η)) * (2 : ℝ) ^ (-(N : ℝ) * (σ + η)) := h9
          _ = 1 := h10
      exact h13.trans_le h5
    rw [hr0_eq, hr2_eq]
    exact h_main

/-- For any `r > r₀`, `K' * r^(σ+η) > 1`, so no set can have measure
`≥ K' * r^(σ+η)` under a probability measure. -/
lemma tubes_empty_above_r0 (σ η K' : ℝ)
    (hση : 0 < σ + η) (hK'pos : 0 < K')
    (r0 : ℝ) (hr0 : 0 < r0)
    (h_gt_one : 1 < K' * r0 ^ (σ + η))
    {ν : Measure (EuclideanSpace ℝ (Fin 2))} [IsProbabilityMeasure ν]
    (r : ℝ) (hr : r0 < r) :
    ∀ (s : Set (EuclideanSpace ℝ (Fin 2))),
      ν s ≤ ENNReal.ofReal (K' * r ^ (σ + η)) := by
  intro s
  have h2 : r0 ^ (σ + η) < r ^ (σ + η) := by
    apply Real.rpow_lt_rpow
    · exact le_of_lt hr0
    · exact hr
    · exact hση
  have h3 : 1 < K' * r ^ (σ + η) := by
    have h4 : r0 ^ (σ + η) ≤ r ^ (σ + η) := le_of_lt h2
    have h5 : K' * r0 ^ (σ + η) ≤ K' * r ^ (σ + η) := by
      exact mul_le_mul_of_nonneg_left h4 (le_of_lt hK'pos)
    exact lt_of_lt_of_le h_gt_one h5
  have h4 : ν s ≤ 1 := prob_le_one
  have h5 : (1 : ENNReal) ≤ ENNReal.ofReal (K' * r ^ (σ + η)) := by
    rw [ENNReal.one_le_ofReal]
    <;> linarith
  exact le_trans h4 h5

/-! ### Dyadic scale enlargement -/

/-- For any `r > 0`, there exists a dyadic `r'` with `r ≤ r' < 2*r`. -/
lemma exists_dyadic_cover (r : ℝ) (hr : 0 < r) :
    ∃ (r' : ℝ), r' ∈ Dyadic ∧ r ≤ r' ∧ r' < 2 * r := by
  let x : ℝ := Real.log r / Real.log 2
  let n : ℤ := Int.ceil x
  have h1 : (n : ℝ) - 1 < x := by
    have h1a : (n : ℝ) < x + 1 := Int.ceil_lt_add_one x
    linarith
  have h2 : x ≤ (n : ℝ) := Int.le_ceil x
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr_eq : r = (2 : ℝ) ^ x := by
    have h : Real.log r = x * Real.log 2 := by
      dsimp only [x]
      field_simp [hlog2_pos.ne'] <;> ring
    have h' : Real.log ((2 : ℝ) ^ x) = x * Real.log 2 := by
      rw [Real.log_rpow (by norm_num)] <;> ring
    have h'' : Real.log r = Real.log ((2 : ℝ) ^ x) := by rw [h, h']
    have hpos1 : 0 < r := hr
    have hpos2 : 0 < (2 : ℝ) ^ x := by positivity
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr hpos1) (Set.mem_Ioi.mpr hpos2) h''
  have h3 : (2 : ℝ) ^ ((n : ℝ) - 1) < (2 : ℝ) ^ x := by
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
  have h4 : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ (n : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
  have h3' : (2 : ℝ) ^ ((n : ℝ) - 1) < r := by
    rw [hr_eq] at *; exact h3
  have h4' : r ≤ (2 : ℝ) ^ (n : ℝ) := by
    rw [hr_eq] at *; exact h4
  have h6 : (2 : ℝ) ^ (n : ℝ) = 2 * (2 : ℝ) ^ ((n : ℝ) - 1) := by
    have h7 : (n : ℝ) = ((n : ℝ) - 1) + 1 := by ring
    rw [h7]
    rw [Real.rpow_add (by norm_num)]
    <;> simp [mul_comm]
    <;> ring
  have h5 : (2 : ℝ) ^ (n : ℝ) < 2 * r := by
    rw [h6]
    have h8 : 2 * (2 : ℝ) ^ ((n : ℝ) - 1) < 2 * r := by
      exact mul_lt_mul_of_pos_left h3' (by norm_num)
    exact h8
  have h9 : (2 : ℝ) ^ (n : ℝ) = (2 : ℝ) ^ n := by
    simp
  refine' ⟨(2 : ℝ) ^ (n : ℝ), _ , h4', h5⟩
  exact ⟨n, by simp [h9]⟩

/-- If an `r`-tube has mass `≥ K' * r^(σ+η)`, then after enlarging to a
dyadic scale `r' ∈ [r, 2r)`, the corresponding `r'`-tube has mass
`≥ (K' / 2^(σ+η)) * (r')^(σ+η)`. -/
lemma dyadic_enlargement (σ η K' r : ℝ)
    (hση : 0 < σ + η) (hr : 0 < r) (hK' : 0 < K') :
    ∃ (r' : ℝ), r' ∈ Dyadic ∧ r ≤ r' ∧ r' < 2 * r ∧
      (K' / (2 : ℝ) ^ (σ + η)) * r' ^ (σ + η) ≤ K' * r ^ (σ + η) := by
  rcases exists_dyadic_cover r hr with ⟨r', hdyad, hle, hlt⟩
  refine' ⟨r', hdyad, hle, hlt, _⟩
  have hpos2 : 0 < (2 : ℝ) := by norm_num
  have h3 : (2 * r) ^ (σ + η) = (2 : ℝ) ^ (σ + η) * r ^ (σ + η) := by
    rw [Real.mul_rpow (by norm_num) (by linarith)]
  have h1 : r' ^ (σ + η) < (2 : ℝ) ^ (σ + η) * r ^ (σ + η) := by
    have h1a : r' ^ (σ + η) < (2 * r) ^ (σ + η) := by
      apply Real.rpow_lt_rpow
      · linarith
      · exact hlt
      · exact hση
    rw [h3] at h1a
    exact h1a
  have h4 : (K' / (2 : ℝ) ^ (σ + η)) * r' ^ (σ + η) < K' * r ^ (σ + η) := by
    calc
      (K' / (2 : ℝ) ^ (σ + η)) * r' ^ (σ + η)
        < (K' / (2 : ℝ) ^ (σ + η)) * ((2 : ℝ) ^ (σ + η) * r ^ (σ + η)) := by
          gcongr
          <;> linarith
      _ = K' * r ^ (σ + η) := by
        field_simp
        <;> ring
  exact le_of_lt h4

/-! ### Scale selection -/

/-- The main scale-selection lemma.

Let `H_r` be a family of measurable sets indexed by dyadic `r`, with
`H = ⋃_{r dyadic} H_r`. Suppose:
- `(μ×ν)(H) ≥ c`
- `H_r = ∅` for `r > r₀`
- `r₀ ≤ 2^{-N}`
- The sum of `2 * r^η` over dyadic `r = 2^{-(n+N)}` is `< c`

Then there exists a dyadic `r ≤ r₀` such that `(μ×ν)(H_r) ≥ 2 * r^η`. -/
lemma scale_selection {μ ν : Measure (EuclideanSpace ℝ (Fin 2))}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (η c r0 : ℝ) (N : ℕ)
    (hη : 0 < η) (hc : 0 < c)
    (hr0 : 0 < r0) (hr0_le : r0 ≤ (2 : ℝ) ^ (-(N : ℝ)))
    (H_r : ℝ → Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (hH_meas : ∀ r, MeasurableSet (H_r r))
    (hH_union : (μ.prod ν) (⋃ r ∈ Dyadic, H_r r) ≥ ENNReal.ofReal c)
    (hH_empty : ∀ r > r0, H_r r = ∅)
    (h_sum_small : ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ η) < ENNReal.ofReal c) :
    ∃ (r : ℝ), r ∈ Dyadic ∧ 0 < r ∧ r ≤ r0 ∧
      (μ.prod ν) (H_r r) ≥ ENNReal.ofReal (2 * r ^ η) := by
  by_contra h
  push Not at h
  let f : ℕ → ℝ := fun n => (2 : ℝ) ^ (-(n + N : ℝ))
  have hf_dyadic : ∀ n : ℕ, f n ∈ Dyadic := by
    intro n
    refine' ⟨-(n + N : ℤ), _⟩
    simp [f] <;> norm_cast
  have hf_pos : ∀ n : ℕ, 0 < f n := by intro n; positivity
  have h_dyadic_cover : ∀ r ∈ Dyadic, r ≤ r0 → ∃ n : ℕ, r = f n := by
    intro r hr hle
    rcases hr with ⟨k, rfl⟩
    have hk : (k : ℝ) ≤ -(N : ℝ) := by
      by_contra h4
      have h5 : (k : ℝ) > -(N : ℝ) := by linarith
      have h6 : (2 : ℝ) ^ (k : ℝ) > (2 : ℝ) ^ (-(N : ℝ)) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        · norm_num
        · linarith
      have h7 : (2 : ℝ) ^ (k : ℝ) > r0 := by
        calc
          (2 : ℝ) ^ (k : ℝ) > (2 : ℝ) ^ (-(N : ℝ)) := h6
          _ ≥ r0 := hr0_le
      have h_eq : (2 : ℝ) ^ (k : ℝ) = (2 : ℝ) ^ k := by
        norm_cast
      have h_cont : (2 : ℝ) ^ (k : ℝ) ≤ r0 := by
        rw [h_eq]
        exact hle
      linarith
    have hk' : k ≤ -N := by exact_mod_cast hk
    have hkn : -k - N ≥ 0 := by linarith
    let n : ℕ := (-k - N).toNat
    have hn : (n : ℤ) = -k - N := by
      simp [n, Int.toNat_of_nonneg hkn]
      <;> omega
    have h9 : k = -((n : ℤ) + N) := by omega
    refine' ⟨n, _⟩
    simp [f, h9] <;> norm_cast
  have h_union_eq : (⋃ r ∈ Dyadic, H_r r) = ⋃ n : ℕ, H_r (f n) := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases Set.mem_iUnion₂.mp hx with ⟨r, hr, hxr⟩
      by_cases hle : r ≤ r0
      · rcases h_dyadic_cover r hr hle with ⟨n, rfl⟩
        exact Set.mem_iUnion.mpr ⟨n, hxr⟩
      · have h_empty : H_r r = ∅ := hH_empty r (by linarith)
        rw [h_empty] at hxr
        simpa using hxr
    · intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
      exact Set.mem_iUnion₂.mpr ⟨f n, hf_dyadic n, hxn⟩
  have h9 : ∀ n : ℕ, (μ.prod ν) (H_r (f n)) ≤ ENNReal.ofReal (2 * (f n) ^ η) := by
    intro n
    by_cases hle : f n ≤ r0
    · have hlt : (μ.prod ν) (H_r (f n)) < ENNReal.ofReal (2 * (f n) ^ η) :=
        h (f n) (hf_dyadic n) (hf_pos n) hle
      exact le_of_lt hlt
    · have h_empty : H_r (f n) = ∅ := hH_empty (f n) (by linarith)
      rw [h_empty]
      simp
      <;> positivity
  have h10 : (μ.prod ν) (⋃ n : ℕ, H_r (f n)) ≤ ∑' n : ℕ, (μ.prod ν) (H_r (f n)) := by
    exact measure_iUnion_le _
  have h11 : ∑' n : ℕ, (μ.prod ν) (H_r (f n)) ≤ ∑' n : ℕ, ENNReal.ofReal (2 * (f n) ^ η) := by
    apply ENNReal.tsum_le_tsum
    intro n
    exact h9 n
  have h12 : (μ.prod ν) (⋃ r ∈ Dyadic, H_r r) < ENNReal.ofReal c := by
    rw [h_union_eq]
    calc
      (μ.prod ν) (⋃ n : ℕ, H_r (f n))
        ≤ ∑' n : ℕ, (μ.prod ν) (H_r (f n)) := h10
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (2 * (f n) ^ η) := h11
      _ = ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ η) := by
        congr with n
        <;> simp [f]
      _ < ENNReal.ofReal c := h_sum_small
  exact not_le.mpr h12 hH_union

/-! ### Concentration parameter -/

/-- `κ = 14 * η / (1 - σ)`. -/
def kappa (η σ : ℝ) (hσ : σ < 1) : ℝ :=
  14 * η / (1 - σ)

lemma kappa_pos (η σ : ℝ) (hη : 0 < η) (hσ : σ < 1) :
    0 < kappa η σ hσ := by
  dsimp only [kappa]
  have h1 : 0 < 1 - σ := by linarith
  positivity

lemma kappa_times_diff (η σ : ℝ) (hσ : σ < 1) :
    kappa η σ hσ * (1 - σ) = 14 * η := by
  dsimp only [kappa]
  field_simp [show (1 - σ : ℝ) ≠ 0 by linarith]
  <;> ring

/-- The contradiction in the concentrated case: for `0 < r < 1` and `η > 0`,
we cannot have `r^(13*η) ≤ r^(14*η)`. -/
lemma concentrated_contradiction (η r : ℝ)
    (hη : 0 < η) (hr0 : 0 < r) (hr1 : r < 1) :
    ¬ (r ^ (13 * η) ≤ r ^ (14 * η)) := by
  have h2 : 13 * η < 14 * η := by linarith
  have h3 : r ^ (14 * η) < r ^ (13 * η) := by
    exact Real.rpow_lt_rpow_of_exponent_gt hr0 hr1 h2
  intro h
  linarith

end RadialBootstrapping
