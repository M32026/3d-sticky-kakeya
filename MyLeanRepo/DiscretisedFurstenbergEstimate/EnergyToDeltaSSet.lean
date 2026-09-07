module

/-
  Energy-to-S-set conversion for Phase 2.

  Converts the ball-growth output of `common_tube_energy_extraction` into an
  `IsDeltaSSet` statement, plus covering number lower bounds needed for RKP input.

  Main results:
  - `ball_growth_to_sset`: finite set with per-point ball-growth
    bound `|S ∩ B(q,r)| ≤ 1 + A·r^u` is a `(δ, u, C)`-set with
    `C = 2^u · (δ^{-u} + A)`.
  - `energy_extraction_to_sset`: applies the above to the output of
    `common_tube_energy_extraction`, with `A = 4E/I`.
  - `extraction_ncover_bounds`: `Ncover δ S ≤ |S|` and `Ncover δ S ≥ 1`.

  Whiteprint node: Phase2 / EnergyToDeltaSSet
  Dependencies: CommonTubeEnergyExtraction
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Phase2Ncover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
open Metric Set

noncomputable section

namespace DirecretisedFurstenbergEstimate.Phase2

/-! ### Helper: covering number vs cardinality for finite sets -/

/-- For any finite set `S`, the δ-covering number is at most `|S|`. -/
lemma ncover_le_card {X : Type*} [PseudoMetricSpace X] {δ : ℝ} (hδ : 0 < δ)
    {S : Finset X} :
    Ncover δ (S : Set X) ≤ (S.card : ENNReal) := by
  have h1 : Metric.externalCoveringNumber δ.toNNReal (S : Set X) ≤ (S : Set X).encard :=
    Metric.externalCoveringNumber_le_encard_self (A := (S : Set X))
  have h2 : (S : Set X).encard = ↑S.card := by simp
  rw [h2] at h1
  have h3 : (↑(Metric.externalCoveringNumber δ.toNNReal (S : Set X)) : ENNReal) ≤ (↑S.card : ENNReal) := by
    exact_mod_cast h1
  exact h3

/-- For a nonempty finite set, the δ-covering number is at least 1. -/
lemma ncover_nonempty_ge_one {X : Type*} [PseudoMetricSpace X] {δ : ℝ} (hδ : 0 < δ)
    {S : Finset X} (hS : S.Nonempty) :
    (1 : ENNReal) ≤ Ncover δ (S : Set X) := by
  have h_nonempty : (S : Set X).Nonempty := hS
  have h_ne_zero : Metric.externalCoveringNumber δ.toNNReal (S : Set X) ≠ 0 := by
    have h_eq : Metric.externalCoveringNumber δ.toNNReal (S : Set X) = 0 ↔ (S : Set X) = ∅ :=
      Metric.externalCoveringNumber_eq_zero
    intro h
    have h_empty : (S : Set X) = ∅ := h_eq.mp h
    have h_contra : ¬(S : Set X).Nonempty := by
      rw [h_empty]
      <;> simp
    exact h_contra h_nonempty
  have h : (1 : ℕ∞) ≤ Metric.externalCoveringNumber δ.toNNReal (S : Set X) := by
    exact Order.one_le_iff_ne_zero.mpr h_ne_zero
  have h3 : (1 : ENNReal) ≤ ↑(Metric.externalCoveringNumber δ.toNNReal (S : Set X)) := by
    exact_mod_cast h
  exact h3

/-! ### Ball-growth bound for arbitrary centers -/

/-- Convert a ball-growth bound centered at points of `S` to a bound for
arbitrary centers, using the triangle inequality with radius `2r`. -/
lemma ball_growth_arb_center {X : Type*} [MetricSpace X] {δ u A : ℝ}
    {S : Finset X} (hδ : 0 < δ) (hu : 0 ≤ u) (hA : 0 ≤ A)
    (h_growth : ∀ q ∈ S, ∀ r : ℝ, δ ≤ r →
      ((S.filter fun q' => dist q q' ≤ r).card : ℝ) ≤ 1 + A * Real.rpow r u) :
    ∀ (x : X) (r : ℝ), δ ≤ r →
      ((S.filter fun q' => dist x q' ≤ r).card : ℝ) ≤
        1 + A * Real.rpow (2 * r) u := by
  intro x r hr
  by_cases h_empty : (S.filter fun q' => dist x q' ≤ r).Nonempty
  · rcases h_empty with ⟨q, hq⟩
    have hq_in_S : q ∈ S := (Finset.mem_filter.mp hq).1
    have hq_dist : dist x q ≤ r := (Finset.mem_filter.mp hq).2
    have h_subset : S.filter (fun q' => dist x q' ≤ r) ⊆
        S.filter (fun q' => dist q q' ≤ 2 * r) := by
      intro y hy
      have hy_in_S : y ∈ S := (Finset.mem_filter.mp hy).1
      have h1 : dist x y ≤ r := (Finset.mem_filter.mp hy).2
      have h2 : dist q y ≤ dist q x + dist x y := dist_triangle q x y
      have h3 : dist q x = dist x q := dist_comm q x
      have h4 : dist q y ≤ 2 * r := by
        rw [h3] at h2; linarith
      exact Finset.mem_filter.mpr ⟨hy_in_S, h4⟩
    have h5 : ((S.filter (fun q' => dist x q' ≤ r)).card : ℝ) ≤
        ((S.filter (fun q' => dist q q' ≤ 2 * r)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card h_subset
    have h6 : δ ≤ 2 * r := by linarith
    have h7 := h_growth q hq_in_S (2 * r) h6
    exact le_trans h5 h7
  · have h9 : S.filter (fun q' => dist x q' ≤ r) = ∅ := by
      simpa using h_empty
    rw [h9]
    have h10 : 0 ≤ Real.rpow (2 * r) u := Real.rpow_nonneg (by linarith) u
    have h11 : (0 : ℝ) ≤ 1 + A * Real.rpow (2 * r) u := by
      have h12 : 0 ≤ A := hA
      nlinarith
    simpa using h11

/-! ### Main conversion: ball-growth to IsDeltaSSet -/

/-- A finite set with per-point ball-growth bound
`|S ∩ B(q,r)| ≤ 1 + A·r^u` for `r ≥ δ` is a `(δ, u, C)`-set with
`C = 2^u · (δ^{-u} + A)`. -/
lemma ball_growth_to_sset {X : Type*} [MetricSpace X]
    {δ u A : ℝ} {S : Finset X}
    (hδ : 0 < δ) (hu : 0 < u) (hA : 0 ≤ A)
    (hS_nonempty : S.Nonempty)
    (h_growth : ∀ q ∈ S, ∀ r : ℝ, δ ≤ r →
      ((S.filter fun q' => dist q q' ≤ r).card : ℝ) ≤ 1 + A * Real.rpow r u) :
    IsDeltaSSet δ u (2^u * (Real.rpow δ (-u) + A)) (S : Set X) := by
  set C : ℝ := 2^u * (Real.rpow δ (-u) + A) with hC_def
  have h_rpow_pos : 0 < Real.rpow δ (-u) := Real.rpow_pos_of_pos hδ (-u)
  have h_sum_pos : 0 < Real.rpow δ (-u) + A := by linarith
  have h_two_pow_pos : 0 < (2 : ℝ)^u := by positivity
  have hC_pos : 0 < C := by
    rw [hC_def]
    exact mul_pos h_two_pow_pos h_sum_pos
  have h_arb_growth := ball_growth_arb_center hδ hu.le hA h_growth
  refine' ⟨hS_nonempty, hδ, hC_pos, hu.le, _⟩
  intro x r hr
  have hr_pos : 0 < r := by linarith
  have h1 : Ncover δ ((S : Set X) ∩ closedBall x r) ≤
      ENNReal.ofReal (((S.filter fun q' => dist x q' ≤ r).card : ℝ)) := by
    have h_sub : (S.filter (fun q' => dist x q' ≤ r) : Set X) =
        (S : Set X) ∩ closedBall x r := by
      ext y
      simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff,
        Metric.mem_closedBall, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by simpa [dist_comm] using h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by simpa [dist_comm] using h2⟩
    rw [←h_sub]
    have h_filt : Ncover δ ((S.filter (fun q' => dist x q' ≤ r)) : Set X) ≤
        ((S.filter (fun q' => dist x q' ≤ r)).card : ENNReal) :=
      ncover_le_card hδ
    simpa using h_filt
  have h2 : ((S.filter fun q' => dist x q' ≤ r).card : ℝ) ≤
      1 + A * Real.rpow (2 * r) u := h_arb_growth x r hr
  have h3 : 1 + A * Real.rpow (2 * r) u ≤ C * Real.rpow r u := by
    have h_rpos : 0 < r := hr_pos
    have h_2r_rpow : Real.rpow (2 * r) u = (2 : ℝ)^u * Real.rpow r u :=
      Real.mul_rpow (by norm_num) h_rpos.le
    have h_ratio_ge_one : (1 : ℝ) ≤ r / δ := by
      calc (1 : ℝ) = δ / δ := by field_simp [hδ.ne']
        _ ≤ r / δ := by gcongr
    have h_ge_one : (1 : ℝ) ≤ Real.rpow (r / δ) u :=
      Real.one_le_rpow h_ratio_ge_one hu.le
    have h_2u_pos : 0 < (2 : ℝ)^u := by positivity
    have h_2u_ge_one : (1 : ℝ) ≤ (2 : ℝ)^u :=
      Real.one_le_rpow (by norm_num) hu.le
    have h_delta_neg : Real.rpow δ (-u) = (Real.rpow δ u)⁻¹ :=
      Real.rpow_neg hδ.le u
    have h_ratio_rpow : Real.rpow (r / δ) u = Real.rpow r u / Real.rpow δ u := by
      have h_pos_ratio : 0 < r / δ := by positivity
      have h_pos_r : 0 < Real.rpow r u := Real.rpow_pos_of_pos h_rpos u
      have h_pos_d : 0 < Real.rpow δ u := Real.rpow_pos_of_pos hδ u
      have h_pos_res : 0 < Real.rpow (r / δ) u := Real.rpow_pos_of_pos h_pos_ratio u
      have h_pos_div : 0 < Real.rpow r u / Real.rpow δ u := div_pos h_pos_r h_pos_d
      have h_log1 : Real.log (Real.rpow (r / δ) u) = u * Real.log (r / δ) := Real.log_rpow h_pos_ratio u
      have h_log2 : Real.log (Real.rpow r u / Real.rpow δ u) =
          Real.log (Real.rpow r u) - Real.log (Real.rpow δ u) := by
        rw [Real.log_div h_pos_r.ne' h_pos_d.ne']
      have h_log3 : Real.log (Real.rpow r u) = u * Real.log r := Real.log_rpow h_rpos u
      have h_log4 : Real.log (Real.rpow δ u) = u * Real.log δ := Real.log_rpow hδ u
      have h_log5 : Real.log (r / δ) = Real.log r - Real.log δ := by
        rw [Real.log_div (by linarith) (by linarith)]
      have h_log_eq : Real.log (Real.rpow (r / δ) u) = Real.log (Real.rpow r u / Real.rpow δ u) := by
        rw [h_log1, h_log2, h_log3, h_log4, h_log5] <;> ring
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr h_pos_res) (Set.mem_Ioi.mpr h_pos_div) h_log_eq
    have h9 : Real.rpow δ (-u) * Real.rpow r u = Real.rpow (r / δ) u := by
      rw [h_delta_neg, h_ratio_rpow]
      <;> field_simp [Real.rpow_pos_of_pos hδ u |>.ne'] <;> ring
    have h_2u_nonneg : 0 ≤ (2 : ℝ)^u := by positivity
    have h10 : (1 : ℝ) ≤ (2 : ℝ)^u := h_2u_ge_one
    have h11 : (2 : ℝ)^u ≤ (2 : ℝ)^u * Real.rpow (r / δ) u := by
      have h := mul_le_mul_of_nonneg_left h_ge_one h_2u_nonneg
      simpa using h
    have h_main : (1 : ℝ) ≤ (2 : ℝ)^u * Real.rpow δ (-u) * Real.rpow r u := by
      rw [show (2 : ℝ)^u * Real.rpow δ (-u) * Real.rpow r u =
          (2 : ℝ)^u * (Real.rpow δ (-u) * Real.rpow r u) by ring]
      rw [h9]
      exact le_trans h10 h11
    have h_rpow_nonneg : 0 ≤ Real.rpow r u := Real.rpow_nonneg h_rpos.le u
    rw [h_2r_rpow, hC_def]
    nlinarith [hA, h_rpow_nonneg, h_main]
  have h6 : (1 : ENNReal) ≤ Ncover δ (S : Set X) :=
    ncover_nonempty_ge_one hδ hS_nonempty
  have h7 : ENNReal.ofReal (C * Real.rpow r u) =
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ u := by
    have h_pos1 : 0 ≤ C := by linarith
    have h_pos2 : 0 ≤ Real.rpow r u := Real.rpow_nonneg hr_pos.le u
    have h_eq1 : ENNReal.ofReal (C * Real.rpow r u) =
        ENNReal.ofReal C * ENNReal.ofReal (Real.rpow r u) := by
      rw [ENNReal.ofReal_mul h_pos1]
    rw [h_eq1]
    have h_eq2 : ENNReal.ofReal (Real.rpow r u) = (ENNReal.ofReal r) ^ u := by
      exact Eq.symm (ENNReal.ofReal_rpow_of_nonneg hr_pos.le hu.le)
    rw [h_eq2]
  have h8 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ u ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ u * Ncover δ (S : Set X) := by
    exact le_mul_of_one_le_right (by positivity) h6
  have h4' : ENNReal.ofReal (((S.filter fun q' => dist x q' ≤ r).card : ℝ)) ≤
      ENNReal.ofReal (C * Real.rpow r u) :=
    ENNReal.ofReal_le_ofReal (le_trans h2 h3)
  calc
    Ncover δ ((S : Set X) ∩ closedBall x r)
      ≤ ENNReal.ofReal (((S.filter fun q' => dist x q' ≤ r).card : ℝ)) := h1
    _ ≤ ENNReal.ofReal (C * Real.rpow r u) := h4'
    _ = ENNReal.ofReal C * (ENNReal.ofReal r) ^ u := h7
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ u * Ncover δ (S : Set X) := h8

/-! ### Improved conversion using Ncover lower bound -/

/-- Improved conversion: if `Ncover δ S ≥ N > 0`, the S-set constant is
    `(δ^{-u} + A·2^u) / N` instead of `2^u · (δ^{-u} + A)`.

    This is critical when `S` has large covering number: the `δ^{-u}` term
    (needed for the `r = δ` case) is divided by `N`, so if `N ~ δ^{-α}`
    the effective constant becomes `~δ^{-(u-α)}`. -/
lemma ball_growth_to_sset_with_lower_bound {X : Type*} [MetricSpace X]
    {δ u A N : ℝ} {S : Finset X}
    (hδ : 0 < δ) (hu : 0 < u) (hA : 0 ≤ A) (hN : 0 < N)
    (hS_nonempty : S.Nonempty)
    (hNcover_lower : ENNReal.ofReal N ≤ Ncover δ (S : Set X))
    (h_growth : ∀ q ∈ S, ∀ r : ℝ, δ ≤ r →
      ((S.filter fun q' => dist q q' ≤ r).card : ℝ) ≤ 1 + A * Real.rpow r u) :
    IsDeltaSSet δ u ((Real.rpow δ (-u) + A * (2 : ℝ)^u) / N) (S : Set X) := by
  set C : ℝ := (Real.rpow δ (-u) + A * (2 : ℝ)^u) / N with hC_def
  have h1_pos : 0 < Real.rpow δ (-u) := Real.rpow_pos_of_pos hδ (-u)
  have h2_nonneg : 0 ≤ A * (2 : ℝ)^u := by positivity
  have h3_pos : 0 < Real.rpow δ (-u) + A * (2 : ℝ)^u := by linarith
  have hC_pos : 0 < C := by
    rw [hC_def]; exact div_pos h3_pos hN
  have h_arb_growth := ball_growth_arb_center hδ hu.le hA h_growth
  refine' ⟨hS_nonempty, hδ, hC_pos, hu.le, _⟩
  intro x r hr
  have hr_pos : 0 < r := by linarith
  have h1 : Ncover δ ((S : Set X) ∩ closedBall x r) ≤
      ENNReal.ofReal (((S.filter fun q' => dist x q' ≤ r).card : ℝ)) := by
    have h_sub : (S.filter (fun q' => dist x q' ≤ r) : Set X) =
        (S : Set X) ∩ closedBall x r := by
      ext y; simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff,
        Metric.mem_closedBall, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa [dist_comm] using h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa [dist_comm] using h2⟩
    rw [←h_sub]
    have h_filt : Ncover δ ((S.filter (fun q' => dist x q' ≤ r)) : Set X) ≤
        ((S.filter (fun q' => dist x q' ≤ r)).card : ENNReal) := ncover_le_card hδ
    simpa using h_filt
  have h2 : ((S.filter fun q' => dist x q' ≤ r).card : ℝ) ≤
      1 + A * Real.rpow (2 * r) u := h_arb_growth x r hr
  have h_2r_rpow : Real.rpow (2 * r) u = (2 : ℝ)^u * Real.rpow r u :=
    Real.mul_rpow (by norm_num) hr_pos.le
  have h4 : (1 : ℝ) ≤ Real.rpow δ (-u) * Real.rpow r u := by
    have hδu_pos : 0 < Real.rpow δ u := Real.rpow_pos_of_pos hδ u
    have hδu_le_ru : Real.rpow δ u ≤ Real.rpow r u :=
      Real.rpow_le_rpow (by linarith) (by linarith) hu.le
    have h_neg : Real.rpow δ (-u) = (Real.rpow δ u)⁻¹ := Real.rpow_neg hδ.le u
    rw [h_neg]
    have h' : (Real.rpow δ u)⁻¹ * Real.rpow r u ≥ 1 := by
      have h_mul : (Real.rpow δ u)⁻¹ * Real.rpow δ u ≤
          (Real.rpow δ u)⁻¹ * Real.rpow r u :=
        mul_le_mul_of_nonneg_left hδu_le_ru (by positivity)
      have h_id : (Real.rpow δ u)⁻¹ * Real.rpow δ u = 1 := by
        field_simp [hδu_pos.ne']
      rw [h_id] at h_mul
      exact h_mul
    exact h'
  have h3 : 1 + A * Real.rpow (2 * r) u ≤ C * Real.rpow r u * N := by
    rw [h_2r_rpow, hC_def]
    have hC_nonneg : 0 ≤ C := by linarith
    have hrpow_nonneg : 0 ≤ Real.rpow r u := Real.rpow_nonneg hr_pos.le u
    field_simp [hN.ne']
    nlinarith [hA, h4, h2_nonneg]
  have h4' : ENNReal.ofReal (((S.filter fun q' => dist x q' ≤ r).card : ℝ)) ≤
      ENNReal.ofReal (C * Real.rpow r u * N) :=
    ENNReal.ofReal_le_ofReal (le_trans h2 h3)
  have h5 : ENNReal.ofReal (C * Real.rpow r u * N) =
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ u * ENNReal.ofReal N := by
    have h_posC : 0 ≤ C := by linarith
    have h_posr : 0 ≤ Real.rpow r u := Real.rpow_nonneg hr_pos.le u
    have h_posN : 0 ≤ N := by linarith
    have h_eq1 : ENNReal.ofReal (C * Real.rpow r u * N) =
        ENNReal.ofReal C * ENNReal.ofReal (Real.rpow r u) * ENNReal.ofReal N := by
      have h_a : ENNReal.ofReal (C * Real.rpow r u * N) =
          ENNReal.ofReal (C * Real.rpow r u) * ENNReal.ofReal N := by
        rw [ENNReal.ofReal_mul (show 0 ≤ C * Real.rpow r u by positivity)]
        <;> ring
      rw [h_a]
      have h_b : ENNReal.ofReal (C * Real.rpow r u) =
          ENNReal.ofReal C * ENNReal.ofReal (Real.rpow r u) := by
        rw [ENNReal.ofReal_mul h_posC] <;> ring
      rw [h_b] <;> ring
    rw [h_eq1]
    have h_eq2 : ENNReal.ofReal (Real.rpow r u) = (ENNReal.ofReal r) ^ u := by
      exact Eq.symm (ENNReal.ofReal_rpow_of_nonneg hr_pos.le hu.le)
    rw [h_eq2] <;> ring
  have h6 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ u * ENNReal.ofReal N ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ u * Ncover δ (S : Set X) := by
    gcongr
    <;> exact hNcover_lower
  calc
    Ncover δ ((S : Set X) ∩ closedBall x r)
      ≤ ENNReal.ofReal (((S.filter fun q' => dist x q' ≤ r).card : ℝ)) := h1
    _ ≤ ENNReal.ofReal (C * Real.rpow r u * N) := h4'
    _ = ENNReal.ofReal C * (ENNReal.ofReal r) ^ u * ENNReal.ofReal N := h5
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ u * Ncover δ (S : Set X) := h6

/-! ### Wrapper for common_tube_energy_extraction output -/

/-- Apply `ball_growth_to_sset` to the output of `common_tube_energy_extraction`.

Given extraction parameters and the extracted `T₀, Q₀`, produces
`IsDeltaSSet δ u C (Q₀ : Set X)` with `C = 2^u · (δ^{-u} + 4E/I)`,
plus the cardinality lower bound `|Q₀| ≥ I/(4L)`. -/
lemma energy_extraction_to_sset {X Tube : Type*} [MetricSpace X]
    [DecidableEq X] [DecidableEq Tube]
    {δ u I E L : ℝ} {Q : Finset X} {𝒯 : Finset Tube}
    {fiber : Tube → Finset X}
    (hδ : 0 < δ) (hu : 0 < u) (hI : 0 < I) (hE : 0 ≤ E) (hL : 0 < L)
    (T₀ : Tube) (hT₀ : T₀ ∈ 𝒯)
    (Q₀ : Finset X) (hQ₀sub : Q₀ ⊆ fiber T₀)
    (hQ₀card : I ≤ 4 * L * (Q₀.card : ℝ))
    (h_ball_growth : ∀ q ∈ Q₀, ∀ r : ℝ, δ ≤ r →
      ((Q₀.filter fun q' => dist q q' ≤ r).card : ℝ) ≤
        1 + (4 * E / I) * Real.rpow r u) :
    IsDeltaSSet δ u (2^u * (Real.rpow δ (-u) + 4 * E / I)) (Q₀ : Set X) ∧
      (I / (4 * L) ≤ (Q₀.card : ℝ)) := by
  have hQ₀_nonempty : Q₀.Nonempty := by
    by_contra h
    have h' : Q₀.card = 0 := by simpa [Finset.not_nonempty_iff_eq_empty] using h
    rw [h'] at hQ₀card
    have h_pos : 0 < I := hI
    have h_contra : (I : ℝ) ≤ 0 := by simpa using hQ₀card
    exact False.elim (not_le.mpr h_pos h_contra)
  set A : ℝ := 4 * E / I with hA_def
  have hA_nonneg : 0 ≤ A := by positivity
  have h_sset : IsDeltaSSet δ u (2^u * (Real.rpow δ (-u) + A)) (Q₀ : Set X) :=
    ball_growth_to_sset hδ hu hA_nonneg hQ₀_nonempty h_ball_growth
  have h_card_lower : I / (4 * L) ≤ (Q₀.card : ℝ) := by
    have h_pos : 0 < 4 * L := by positivity
    calc
      I / (4 * L) ≤ (4 * L * (Q₀.card : ℝ)) / (4 * L) := by gcongr
      _ = (Q₀.card : ℝ) := by
        field_simp [h_pos.ne'] <;> ring
  exact ⟨h_sset, h_card_lower⟩

/-- Apply `ball_growth_to_sset_with_lower_bound` to the extraction output.

    Given an additional lower bound `Ncover δ Q₀ ≥ N`, produces a sharper
    `IsDeltaSSet` with constant `(δ^{-u} + (4E/I)·2^u) / N`. -/
lemma energy_extraction_to_sset_with_lower_bound
    {X Tube : Type*} [MetricSpace X] [DecidableEq X] [DecidableEq Tube]
    {δ u I E L N : ℝ} {Q : Finset X} {𝒯 : Finset Tube}
    {fiber : Tube → Finset X}
    (hδ : 0 < δ) (hu : 0 < u) (hI : 0 < I) (hE : 0 ≤ E) (hL : 0 < L) (hN : 0 < N)
    (T₀ : Tube) (hT₀ : T₀ ∈ 𝒯)
    (Q₀ : Finset X) (hQ₀sub : Q₀ ⊆ fiber T₀)
    (hQ₀card : I ≤ 4 * L * (Q₀.card : ℝ))
    (hNcover_lower : ENNReal.ofReal N ≤ Ncover δ (Q₀ : Set X))
    (h_ball_growth : ∀ q ∈ Q₀, ∀ r : ℝ, δ ≤ r →
      ((Q₀.filter fun q' => dist q q' ≤ r).card : ℝ) ≤
        1 + (4 * E / I) * Real.rpow r u) :
    IsDeltaSSet δ u ((Real.rpow δ (-u) + (4 * E / I) * (2 : ℝ)^u) / N) (Q₀ : Set X) ∧
      (I / (4 * L) ≤ (Q₀.card : ℝ)) := by
  have hQ₀_nonempty : Q₀.Nonempty := by
    by_contra h
    have h' : Q₀.card = 0 := by simpa [Finset.not_nonempty_iff_eq_empty] using h
    rw [h'] at hQ₀card
    have h_pos : 0 < I := hI
    have h_contra : (I : ℝ) ≤ 0 := by simpa using hQ₀card
    exact False.elim (not_le.mpr h_pos h_contra)
  set A : ℝ := 4 * E / I with hA_def
  have hA_nonneg : 0 ≤ A := by positivity
  have h_sset : IsDeltaSSet δ u ((Real.rpow δ (-u) + A * (2 : ℝ)^u) / N) (Q₀ : Set X) :=
    ball_growth_to_sset_with_lower_bound hδ hu hA_nonneg hN hQ₀_nonempty hNcover_lower h_ball_growth
  have h_card_lower : I / (4 * L) ≤ (Q₀.card : ℝ) := by
    have h_pos : 0 < 4 * L := by positivity
    calc
      I / (4 * L) ≤ (4 * L * (Q₀.card : ℝ)) / (4 * L) := by gcongr
      _ = (Q₀.card : ℝ) := by
        field_simp [h_pos.ne'] <;> ring
  exact ⟨h_sset, h_card_lower⟩

/-! ### Covering number bounds for RKP input -/

/-- Covering number bounds for the extracted set.

Upper: `Ncover δ Q₀ ≤ |Q₀|`.
Lower: `Ncover δ Q₀ ≥ 1`.

For applications in EuclideanPlane, a packing argument gives the stronger
lower bound `Ncover δ Q₀ ≥ |Q₀| / K` for a dimension-dependent constant `K`.
Combined with `|Q₀| ≥ I/(4L)`, this yields `Ncover δ Q₀ ≥ I/(4LK)`. -/
lemma extraction_ncover_bounds {X : Type*} [MetricSpace X]
    {δ : ℝ} (hδ : 0 < δ) {Q₀ : Finset X} (hQ₀_nonempty : Q₀.Nonempty) :
    Ncover δ (Q₀ : Set X) ≤ (Q₀.card : ENNReal) ∧
    (1 : ENNReal) ≤ Ncover δ (Q₀ : Set X) :=
  ⟨ncover_le_card hδ, ncover_nonempty_ge_one hδ hQ₀_nonempty⟩

end DirecretisedFurstenbergEstimate.Phase2
