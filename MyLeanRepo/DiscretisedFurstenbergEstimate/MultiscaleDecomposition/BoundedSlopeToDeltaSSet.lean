module

/-
  Generalized dictionary lemma: uniform set with code function bounded near a
  specified slope s0 is an (s0, C)-set.

  Takes absolute error bounds |f(j) - s0*j| ≤ E for all integer j ∈ [0,m].
  The constant C must be at least dictionaryConstant m Δ * Δ^(-E).

  Uses exact f(m) cancellation: the ratio bound becomes
  9^(m-j+1) * 36^m * Δ^(f(j)) ≤ C * r^s0, and f(j) ≥ s0*j - E gives
  Δ^(f(j)) ≤ Δ^(s0*j - E).

  For IsDyadicUniform, the lower bound constant is 36^m (not 4^m).
  The extra 9^m is absorbed using Δ ≤ 1/2, which gives Δ^(-4) ≥ 16 > 9.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MultiscaleDecomposition

namespace MultiscaleDecomposition

/-- Helper: `9^(m-j+1) * 36^m * Δ^(s*j-E) ≤ dictionaryConstant m Δ * Δ^(-E) * r^s`.

    Uses `Δ ≤ 1/2` to absorb the extra `9^m` from `36^m = 4^m * 9^m`. -/
lemma bounded_slope_constant_check {m : ℕ} {Δ r s E : ℝ} {j : ℕ}
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hΔ2 : Δ ≤ 1 / 2)
    (hr_pos : 0 < r) (hr_le_one : r ≤ 1)
    (hs_nonneg : 0 ≤ s) (hs_le_4 : s ≤ 4) (hE_nonneg : 0 ≤ E)
    (hm_pos : 0 < m) (hj_pos : 1 ≤ j) (hj_lt_m : j < m) (h_le : Δ ^ (j + 1) ≤ r) :
    (9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m * Real.rpow Δ (s * (j : ℝ) - E) ≤
      dictionaryConstant m Δ * Real.rpow Δ (-E) * r ^ s := by
  have h9 : (9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m ≤ (324 : ℝ) ^ m := by
    have h1 : m - j + 1 ≤ m := by omega
    have h2 : (9 : ℝ) ^ (m - j + 1) ≤ (9 : ℝ) ^ m := by gcongr <;> norm_num
    have h3 : (9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m ≤ (9 : ℝ) ^ m * (36 : ℝ) ^ m := by gcongr
    have h4 : (9 : ℝ) ^ m * (36 : ℝ) ^ m = (324 : ℝ) ^ m := by
      rw [← mul_pow] <;> norm_num
    rw [h4] at h3; exact h3
  have h_dict : Δ^(-4 : ℝ) * (324 : ℝ) ^ m = dictionaryConstant m Δ := by
    dsimp only [dictionaryConstant] <;> ring
  have h_rpow_split : Real.rpow Δ (s * (j : ℝ) - E) =
      Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) * Real.rpow Δ (-s - E) := by
    have h_sum : s * (j : ℝ) - E = s * ((j + 1 : ℕ) : ℝ) + (-s - E) := by
      simp [add_mul] <;> ring
    rw [h_sum]; exact Real.rpow_add hΔ _ _
  have h_rpow_j1 : Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) = Real.rpow (Δ ^ (j + 1)) s := by
    have h2 : Real.rpow Δ ((j + 1 : ℕ) : ℝ) = (Δ ^ (j + 1) : ℝ) := by
      simp [Real.rpow_natCast] <;> norm_cast
    have h3 : Real.rpow Δ (((j + 1 : ℕ) : ℝ) * s) = (Real.rpow Δ ((j + 1 : ℕ) : ℝ)) ^ s :=
      Real.rpow_mul hΔ.le _ _
    have h4 : s * ((j + 1 : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) * s := by ring
    have h5 : Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) = Real.rpow Δ (((j + 1 : ℕ) : ℝ) * s) := by rw [h4]
    rw [h5, h3, h2] <;> rfl
  have h_rpow_le : Real.rpow (Δ ^ (j + 1)) s ≤ r ^ s :=
    Real.rpow_le_rpow (by positivity) h_le hs_nonneg
  have h_neg_s_le : Real.rpow Δ (-s - E) ≤ Real.rpow Δ (-4 - E) := by
    have h5 : -s - E ≥ -4 - E := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le h5
  have h_combine : Real.rpow Δ (-4 - E) = Real.rpow Δ (-4) * Real.rpow Δ (-E) := by
    have h : Real.rpow Δ ((-4 : ℝ) + (-E)) = Real.rpow Δ (-4) * Real.rpow Δ (-E) := Real.rpow_add hΔ _ _
    have h_eq : (-4 : ℝ) + (-E) = -4 - E := by ring
    rw [h_eq] at h; exact h
  have h_pos_b : 0 ≤ Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) := Real.rpow_nonneg hΔ.le _
  have h_pos_c : 0 ≤ Real.rpow Δ (-s - E) := Real.rpow_nonneg hΔ.le _
  have h_step1 : ((9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m) * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) ≤
      (324 : ℝ) ^ m * r ^ s := by
    have h1 : ((9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m) * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) ≤
        (324 : ℝ) ^ m * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right h9 h_pos_b
    have h2 : (324 : ℝ) ^ m * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) ≤
        (324 : ℝ) ^ m * r ^ s :=
      have h_rpow_le' : Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) ≤ r ^ s := by
        rw [h_rpow_j1]; exact h_rpow_le
      mul_le_mul_of_nonneg_left h_rpow_le' (by positivity)
    exact le_trans h1 h2
  have h_step2 : (((9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m) * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ))) * Real.rpow Δ (-s - E) ≤
      (324 : ℝ) ^ m * r ^ s * Real.rpow Δ (-4 - E) := by
    calc (((9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m) * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ))) * Real.rpow Δ (-s - E)
      ≤ ((324 : ℝ) ^ m * r ^ s) * Real.rpow Δ (-s - E) := mul_le_mul_of_nonneg_right h_step1 h_pos_c
    _ ≤ (324 : ℝ) ^ m * r ^ s * Real.rpow Δ (-4 - E) := by
      have h_pos_all : 0 ≤ (324 : ℝ) ^ m * r ^ s := by positivity
      exact mul_le_mul_of_nonneg_left h_neg_s_le h_pos_all
  have h_main : (9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m * Real.rpow Δ (s * (j : ℝ) - E) ≤
      (324 : ℝ) ^ m * r ^ s * Real.rpow Δ (-4 - E) := by
    rw [h_rpow_split]
    have h_eq : (9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m *
          (Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ)) * Real.rpow Δ (-s - E)) =
        (((9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m) * Real.rpow Δ (s * ((j + 1 : ℕ) : ℝ))) * Real.rpow Δ (-s - E) := by ring
    rw [h_eq]; exact h_step2
  have h_rpow4 : Real.rpow Δ (-4) = (Δ ^ (-4 : ℝ)) := by rfl
  have h_final : (324 : ℝ) ^ m * r ^ s * Real.rpow Δ (-4 - E) =
      dictionaryConstant m Δ * Real.rpow Δ (-E) * r ^ s := by
    calc (324 : ℝ) ^ m * r ^ s * Real.rpow Δ (-4 - E)
      = (324 : ℝ) ^ m * r ^ s * (Real.rpow Δ (-4) * Real.rpow Δ (-E)) := by rw [h_combine]
    _ = (Δ ^ (-4 : ℝ)) * (324 : ℝ) ^ m * Real.rpow Δ (-E) * r ^ s := by
        rw [h_rpow4] <;> ring
    _ = dictionaryConstant m Δ * Real.rpow Δ (-E) * r ^ s := by
        rw [h_dict] <;> ring
  rw [h_final] at h_main
  exact h_main

/-- Generalized dictionary lemma: if the code function of a uniform set satisfies
  the lower bound `f(j) ≥ s0*j - E` for all `j ≤ m`, then the set is a
  `(Δ^m, s0, C)`-set. Only the lower bound is needed.

  Requires `C ≥ dictionaryConstant m Δ * Δ^(-E)`. -/
lemma boundedSlopeToDeltaSSet {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hΔ2 : Δ ≤ 1 / 2)
    (s0 E C : ℝ) (hs0_nonneg : 0 ≤ s0) (hs0_le_4 : s0 ≤ 4) (hE_nonneg : 0 ≤ E)
    (hC : dictionaryConstant m Δ * Real.rpow Δ (-E) ≤ C)
    (hm_pos : 0 < m)
    (h_lower : ∀ (j : ℕ), j ≤ m →
      codeFunction m Δ N (j : ℝ) ≥ s0 * (j : ℝ) - E) :
    IsDeltaSSet (Δ ^ m) s0 C P := by
  set f : ℝ → ℝ := codeFunction m Δ N with hf_def
  set δ : ℝ := Δ ^ m with hδ_def
  have hP_nonempty : P.Nonempty := h_uniform.2.2.1
  have hN_pos : ∀ i < m, N i ≥ 1 := h_uniform.2.2.2.1
  have hδ_pos : 0 < δ := by positivity
  have hC_pos : 0 < C := by
    have h1 : 0 < dictionaryConstant m Δ := by
      dsimp only [dictionaryConstant]; positivity
    have h2 : 0 < dictionaryConstant m Δ * Real.rpow Δ (-E) := mul_pos h1 (Real.rpow_pos_of_pos hΔ _)
    linarith [hC]
  have hC_ge_one : (1 : ℝ) ≤ C := by
    have h1 : (1 : ℝ) ≤ dictionaryConstant m Δ := by
      dsimp only [dictionaryConstant]
      have h2 : (1 : ℝ) ≤ Δ^(-4 : ℝ) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hΔ (by linarith) (by norm_num)
      have h3 : (1 : ℝ) ≤ (324 : ℝ) ^ m := one_le_pow₀ (by norm_num)
      calc (1 : ℝ)
        = (1 : ℝ) * (1 : ℝ) := by ring
      _ ≤ Δ^(-4 : ℝ) * (324 : ℝ) ^ m := by gcongr
    have h4 : (1 : ℝ) ≤ Real.rpow Δ (-E) := by
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hΔ hΔ1.le
      linarith
    have h5 : dictionaryConstant m Δ * Real.rpow Δ (-E) ≥ dictionaryConstant m Δ := by
      have h_pos_dict : 0 ≤ dictionaryConstant m Δ := by
        dsimp only [dictionaryConstant]; positivity
      have h6 : dictionaryConstant m Δ * (1 : ℝ) ≤ dictionaryConstant m Δ * Real.rpow Δ (-E) :=
        mul_le_mul_of_nonneg_left h4 h_pos_dict
      simpa using h6
    linarith [hC, h5]

  have h_lower_j : ∀ (j : ℕ), j ≤ m → f (j : ℝ) ≥ s0 * (j : ℝ) - E := by
    intro j hj
    exact h_lower j hj

  have h_main_goal : ∀ (x : EuclideanPlane) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
    intro x r hδ_le_r
    by_cases h_r_ge_one : 1 ≤ r
    · -- Case r ≥ 1
      have h1 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_mono_set (Set.inter_subset_left)
      have h2 : (1 : ENNReal) ≤ ENNReal.ofReal C := ENNReal.one_le_ofReal.mpr hC_ge_one
      have h31 : (1 : ℝ) ≤ r ^ s0 := Real.one_le_rpow h_r_ge_one hs0_nonneg
      have h_rpow_s : (ENNReal.ofReal r) ^ s0 = ENNReal.ofReal (r ^ s0) :=
        ENNReal.ofReal_rpow_of_nonneg (by linarith) hs0_nonneg
      have h3 : (1 : ENNReal) ≤ (ENNReal.ofReal r) ^ s0 := by
        rw [h_rpow_s]; exact ENNReal.one_le_ofReal.mpr h31
      have h4 : (1 : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 := by
        calc (1 : ENNReal)
          = (1 : ENNReal) * (1 : ENNReal) := by simp
        _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 := by gcongr
      calc (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal)
        ≤ (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h1
      _ = (1 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by simp
      _ ≤ (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by gcongr
      _ = ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by ring

    · -- Case δ ≤ r < 1
      have h_r_lt_one : r < 1 := by linarith
      have h_r_pos : 0 < r := lt_of_lt_of_le hδ_pos hδ_le_r
      let S_j : Finset ℕ := Finset.filter (fun k => Δ ^ k > r) (Finset.range m)
      have hSj_nonempty : S_j.Nonempty := by
        have h0 : 0 ∈ S_j := by
          simp only [S_j, Finset.mem_filter, Finset.mem_range]
          constructor
          · exact hm_pos
          · simpa using h_r_lt_one
        exact ⟨0, h0⟩
      let j : ℕ := S_j.max' hSj_nonempty
      have hj_mem : j ∈ S_j := Finset.max'_mem S_j hSj_nonempty
      have hj_in_range : j ∈ Finset.range m := (Finset.mem_filter.mp hj_mem).1
      have hj_lt_m : j < m := Finset.mem_range.mp hj_in_range
      have hj_le_m : j ≤ m := by linarith
      have h_gt : Δ ^ j > r := (Finset.mem_filter.mp hj_mem).2
      have h_le : Δ ^ (j + 1) ≤ r := by
        by_cases h : j + 1 < m
        · have h4 : j + 1 ∉ S_j := by
            intro h5
            have h6 : j + 1 ≤ j := Finset.le_max' S_j (j + 1) h5
            omega
          have h5 : ¬(Δ ^ (j + 1) > r) := by
            simpa [S_j, Finset.mem_filter, h] using h4
          linarith
        · have h6 : j + 1 = m := by omega
          rw [h6]; exact hδ_le_r
      by_cases h_j0 : j = 0
      · -- Case j = 0: use trivial bound covering(P ∩ B) ≤ covering(P)
        have h_r_ge_delta : Δ ≤ r := by
          have h : Δ ^ (j + 1) = Δ := by
            rw [h_j0] <;> simp
          rw [h] at h_le
          exact h_le
        have hC_ge : Δ^(-4 : ℝ) ≤ C := by
          have h1 : Δ^(-4 : ℝ) ≤ dictionaryConstant m Δ := by
            dsimp only [dictionaryConstant]
            have h2 : (1 : ℝ) ≤ (324 : ℝ) ^ m := one_le_pow₀ (by norm_num)
            calc Δ^(-4 : ℝ)
              = Δ^(-4 : ℝ) * (1 : ℝ) := by ring
            _ ≤ Δ^(-4 : ℝ) * (324 : ℝ) ^ m := by gcongr
          have h3 : (1 : ℝ) ≤ Real.rpow Δ (-E) := by
            apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hΔ hΔ1.le
            linarith
          have hpos : 0 ≤ dictionaryConstant m Δ := by
            dsimp only [dictionaryConstant]; positivity
          have h4 : dictionaryConstant m Δ ≤ dictionaryConstant m Δ * Real.rpow Δ (-E) := by
            have h41 : dictionaryConstant m Δ * (1 : ℝ) ≤ dictionaryConstant m Δ * Real.rpow Δ (-E) :=
              mul_le_mul_of_nonneg_left h3 hpos
            simpa using h41
          calc Δ^(-4 : ℝ)
            ≤ dictionaryConstant m Δ := h1
          _ ≤ dictionaryConstant m Δ * Real.rpow Δ (-E) := h4
          _ ≤ C := hC
        have h_rpow_s0 : (ENNReal.ofReal r) ^ s0 = ENNReal.ofReal (r ^ s0) :=
          ENNReal.ofReal_rpow_of_nonneg (by linarith) hs0_nonneg
        have h2 : Real.rpow Δ s0 ≤ r ^ s0 := Real.rpow_le_rpow (by positivity) h_r_ge_delta hs0_nonneg
        have h3 : Real.rpow Δ 4 ≤ Real.rpow Δ s0 := by
          apply Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le <;> linarith
        have h4 : Real.rpow Δ 4 ≤ r ^ s0 := le_trans h3 h2
        have h5 : (1 : ℝ) ≤ C * r ^ s0 := by
          have h_pos1 : 0 ≤ Δ^(-4 : ℝ) := by positivity
          have h_pos2 : 0 ≤ Real.rpow Δ 4 := Real.rpow_nonneg hΔ.le 4
          have h6 : Δ^(-4 : ℝ) * Real.rpow Δ 4 ≤ C * r ^ s0 := by
            gcongr <;> linarith
          have h7 : Δ^(-4 : ℝ) * Real.rpow Δ 4 = 1 := by
            have h82 : Δ^(-4 : ℝ) = Real.rpow Δ (-4) := by rfl
            rw [h82]
            have h9 : Real.rpow Δ (-4) * Real.rpow Δ 4 = Real.rpow Δ ((-4 : ℝ) + 4) := by
              exact (Real.rpow_add hΔ (-4 : ℝ) 4).symm
            rw [h9]
            have h10 : (-4 : ℝ) + 4 = 0 := by norm_num
            rw [h10]
            simp
          rw [h7] at h6
          exact h6
        have h6 : (1 : ENNReal) ≤ ENNReal.ofReal (C * r ^ s0) := ENNReal.one_le_ofReal.mpr h5
        have h7 : (1 : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 := by
          rw [h_rpow_s0]
          have h8 : ENNReal.ofReal C * ENNReal.ofReal (r ^ s0) = ENNReal.ofReal (C * r ^ s0) := by
            rw [← ENNReal.ofReal_mul (show 0 ≤ C by linarith)]
          rw [h8]; exact h6
        have h_mono : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
            (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
          exact_mod_cast Metric.externalCoveringNumber_mono_set (Set.inter_subset_left)
        calc (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal)
          ≤ (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h_mono
        _ = (1 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by simp
        _ ≤ (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by gcongr
        _ = ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by ring
      · -- Case j ≥ 1
        have hj_pos : 1 ≤ j := by omega
        have hΔj_pos : 0 < Δ ^ j := by positivity
        rcases ball_dyadic_squares_bound (Δ ^ j) hΔj_pos x with ⟨Sq, hSq_prop, hSq_card⟩
        have h_ball_sub : Metric.closedBall x r ⊆ Metric.closedBall x (Δ ^ j) := by
          intro y hy
          have h_dist : dist y x ≤ r := by simpa [Metric.mem_closedBall] using hy
          have h : dist y x ≤ Δ ^ j := by linarith
          simpa [Metric.mem_closedBall] using h
        have h_cover : P ∩ Metric.closedBall x r ⊆
            ⋃ p ∈ Sq, P ∩ dyadicSquare (Δ ^ j) p.1 p.2 := by
          intro y hy
          have hyP : y ∈ P := hy.1
          have hyB : y ∈ Metric.closedBall x r := hy.2
          let a : ℤ := ⌊y 0 / (Δ ^ j)⌋
          let b : ℤ := ⌊y 1 / (Δ ^ j)⌋
          have ha1 : (a : ℝ) ≤ y 0 / (Δ ^ j) := Int.floor_le _
          have ha2 : y 0 / (Δ ^ j) < (a : ℝ) + 1 := Int.lt_floor_add_one _
          have hb1 : (b : ℝ) ≤ y 1 / (Δ ^ j) := Int.floor_le _
          have hb2 : y 1 / (Δ ^ j) < (b : ℝ) + 1 := Int.lt_floor_add_one _
          have hy_sq : y ∈ dyadicSquare (Δ ^ j) a b := by
            simp only [dyadicSquare]
            constructor
            · constructor
              · calc (a : ℝ) * (Δ ^ j) ≤ (y 0 / (Δ ^ j)) * (Δ ^ j) := by gcongr
                _ = y 0 := by field_simp [hΔj_pos.ne'] <;> ring
              · calc y 0 = (y 0 / (Δ ^ j)) * (Δ ^ j) := by field_simp [hΔj_pos.ne'] <;> ring
                _ < ((a : ℝ) + 1) * (Δ ^ j) := by gcongr
            · constructor
              · calc (b : ℝ) * (Δ ^ j) ≤ (y 1 / (Δ ^ j)) * (Δ ^ j) := by gcongr
                _ = y 1 := by field_simp [hΔj_pos.ne'] <;> ring
              · calc y 1 = (y 1 / (Δ ^ j)) * (Δ ^ j) := by field_simp [hΔj_pos.ne'] <;> ring
                _ < ((b : ℝ) + 1) * (Δ ^ j) := by gcongr
          have h_intersect : (Metric.closedBall x (Δ ^ j) ∩ dyadicSquare (Δ ^ j) a b).Nonempty :=
            ⟨y, h_ball_sub hyB, hy_sq⟩
          have h_in_Sq : (a, b) ∈ Sq := hSq_prop a b h_intersect
          exact Set.mem_iUnion₂.mpr ⟨(a, b), h_in_Sq, ⟨hyP, hy_sq⟩⟩
        let B_enat : ENNReal := (9 : ENNReal) ^ (m - j) * ∏ i ∈ Finset.range (m - j), (↑(N (j + i)) : ENNReal)
        have h_each : ∀ (p : ℤ × ℤ), p ∈ Sq →
            (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) ≤ B_enat := by
          intro p _
          by_cases hne : (P ∩ dyadicSquare (Δ ^ j) p.1 p.2).Nonempty
          · exact dyadicCovering_product_upper h_uniform hj_le_m p.1 p.2 hne
          · have h_empty : P ∩ dyadicSquare (Δ ^ j) p.1 p.2 = ∅ := by
              simpa [Set.not_nonempty_iff_eq_empty] using hne
            rw [h_empty]; simp [Metric.externalCoveringNumber_empty] <;> positivity
        let A : {p : ℤ × ℤ // p ∈ Sq} → Set EuclideanPlane :=
          fun p => P ∩ dyadicSquare (Δ ^ j) p.val.1 p.val.2
        have h_sum : (Metric.externalCoveringNumber δ.toNNReal
              (⋃ p ∈ Sq, P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) ≤
            ∑ p ∈ Sq, (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) := by
          have h_iUnion : (⋃ p ∈ Sq, P ∩ dyadicSquare (Δ ^ j) p.1 p.2) = ⋃ (i : {p // p ∈ Sq}), A i := by
            ext z; simp [A, Set.mem_iUnion] <;> aesop
          rw [h_iUnion]
          have h_enat := externalCoveringNumber_iUnion_le (ε := δ.toNNReal) (A := A)
          let coeHom : ENat →+ ENNReal :=
            { toFun := fun x => ↑x
              map_zero' := by simp
              map_add' := by intro a b; exact ENat.toENNReal_add a b }
          have h_sum_coe : (↑(∑ i : {p // p ∈ Sq}, Metric.externalCoveringNumber δ.toNNReal (A i)) : ENNReal) =
              ∑ i : {p // p ∈ Sq}, (Metric.externalCoveringNumber δ.toNNReal (A i) : ENNReal) := by
            exact map_sum coeHom (fun i => Metric.externalCoveringNumber δ.toNNReal (A i)) Finset.univ
          have h_coerced : (Metric.externalCoveringNumber δ.toNNReal (⋃ (i : {p // p ∈ Sq}), A i) : ENNReal) ≤
              (↑(∑ i : {p // p ∈ Sq}, Metric.externalCoveringNumber δ.toNNReal (A i)) : ENNReal) :=
            enat_to_ennreal_mono h_enat
          rw [h_sum_coe] at h_coerced
          have h_univ : (Finset.univ : Finset {p // p ∈ Sq}) = Finset.attach Sq := by
            ext x; simp
          have h_attach : ∑ (i : {p // p ∈ Sq}), (Metric.externalCoveringNumber δ.toNNReal (A i) : ENNReal) =
              ∑ p ∈ Sq, (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) := by
            have h1 : ∑ (i : {p // p ∈ Sq}), (Metric.externalCoveringNumber δ.toNNReal (A i) : ENNReal) =
                ∑ i ∈ Finset.attach Sq, (Metric.externalCoveringNumber δ.toNNReal (A i) : ENNReal) := by
              rw [h_univ]
            rw [h1]
            have h2 : ∑ i ∈ Finset.attach Sq, (Metric.externalCoveringNumber δ.toNNReal (A i) : ENNReal) =
                ∑ p ∈ Sq, (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) := by
              apply Finset.sum_bij' (fun (x : {p // p ∈ Sq}) _ => x.val) (fun (p : ℤ × ℤ) hp => ⟨p, hp⟩)
              <;> simp [A, Subtype.ext_iff] <;> tauto
            exact h2
          rw [h_attach] at h_coerced
          exact h_coerced
        have h_upper1 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
            ∑ p ∈ Sq, (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) := by
          have h_mono : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
              (Metric.externalCoveringNumber δ.toNNReal (⋃ p ∈ Sq, P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) := by
            exact_mod_cast Metric.externalCoveringNumber_mono_set h_cover
          calc _ ≤ _ := h_mono
               _ ≤ _ := h_sum
        have h_upper2 : ∑ p ∈ Sq, (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) ≤
            (9 : ENNReal) * B_enat := by
          calc ∑ p ∈ Sq, _
            ≤ ∑ p ∈ Sq, B_enat := Finset.sum_le_sum fun i _ => h_each i ‹_›
          _ = (Sq.card : ENNReal) * B_enat := by simp [Finset.sum_const] <;> ring
          _ ≤ (9 : ENNReal) * B_enat := by
            have h_card : (Sq.card : ENNReal) ≤ (9 : ENNReal) := by exact_mod_cast hSq_card
            gcongr <;> positivity
        let Prod_N : ℝ := ∏ i ∈ Finset.range (m - j), (N (j + i) : ℝ)
        let B_real : ℝ := (9 : ℝ) ^ (m - j) * Prod_N
        have h_prod_coe : (∏ i ∈ Finset.range (m - j), (↑(N (j + i)) : ENNReal)) =
            ENNReal.ofReal Prod_N := by
          have h1 : (∏ i ∈ Finset.range (m - j), (↑(N (j + i)) : ENNReal)) =
              ↑(∏ i ∈ Finset.range (m - j), N (j + i)) := by
            rw [← Nat.cast_prod] <;> rfl
          rw [h1]
          have h2 : (↑(∏ i ∈ Finset.range (m - j), N (j + i)) : ENNReal) =
              ENNReal.ofReal ((↑(∏ i ∈ Finset.range (m - j), N (j + i)) : ℝ)) := by exact Eq.symm (ENNReal.ofReal_natCast (∏ i ∈ Finset.range (m - j), N (j + i)))
          rw [h2]
          have h3 : ((↑(∏ i ∈ Finset.range (m - j), N (j + i)) : ℝ)) = Prod_N := by
            simp [Prod_N] <;> norm_cast
          rw [h3]
        have hB_enat : B_enat = ENNReal.ofReal B_real := by
          simp [B_enat, B_real, Prod_N, h_prod_coe] <;> ring
        have h_upper3 : (9 : ENNReal) * B_enat = ENNReal.ofReal ((9 : ℝ) * B_real) := by
          rw [hB_enat]
          have h9 : (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) := by simp
          rw [h9]
          rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
        have h_upper4 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
            ENNReal.ofReal ((9 : ℝ) * B_real) := by
          calc _ ≤ (9 : ENNReal) * B_enat := le_trans h_upper1 h_upper2
               _ = ENNReal.ofReal ((9 : ℝ) * B_real) := h_upper3

        -- Product decomposition with exact f(m) cancellation
        have h_prod1 : Prod_N = (∏ i ∈ Finset.range m, (N i : ℝ)) / (∏ i ∈ Finset.range j, (N i : ℝ)) := by
          have h2 : Finset.range m = Finset.range j ∪ Finset.Ico j m := by
            ext x; simp [Finset.mem_range, Finset.mem_Ico] <;> omega
          have h3 : Disjoint (Finset.range j) (Finset.Ico j m) := by
            simp [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ico] <;> omega
          have h4 : ∏ i ∈ Finset.range m, (N i : ℝ) =
              (∏ i ∈ Finset.range j, (N i : ℝ)) * ∏ i ∈ Finset.Ico j m, (N i : ℝ) := by
            rw [h2, Finset.prod_union h3] <;> ring
          have h5 : ∏ i ∈ Finset.Ico j m, (N i : ℝ) = ∏ i ∈ Finset.range (m - j), (N (j + i) : ℝ) := by
            rw [Finset.prod_Ico_eq_prod_range] <;> rfl
          have h_pos_j : (∏ i ∈ Finset.range j, (N i : ℝ)) ≠ 0 := by
            apply (Finset.prod_pos _).ne'
            intro i hi
            have h_i_lt_j : i < j := Finset.mem_range.mp hi
            have h_i_lt_m : i < m := by linarith
            have h6 : N i ≥ 1 := hN_pos i h_i_lt_m
            exact_mod_cast (by linarith)
          have h_eq : (∏ i ∈ Finset.range j, (N i : ℝ)) * ∏ i ∈ Finset.range (m - j), (N (j + i) : ℝ) =
              ∏ i ∈ Finset.range m, (N i : ℝ) := by
            have h6 : (∏ i ∈ Finset.range j, (N i : ℝ)) * ∏ i ∈ Finset.Ico j m, (N i : ℝ) =
                ∏ i ∈ Finset.range m, (N i : ℝ) := h4.symm
            rw [h5] at h6
            exact h6
          have h_final_product : ∏ i ∈ Finset.range (m - j), (N (j + i) : ℝ) =
              (∏ i ∈ Finset.range m, (N i : ℝ)) / (∏ i ∈ Finset.range j, (N i : ℝ)) := by
            rw [← h_eq] <;> field_simp [h_pos_j] <;> ring
          simpa [Prod_N] using h_final_product
        have h_cf_m : (∏ i ∈ Finset.range m, (N i : ℝ)) = Real.rpow Δ (-(f (m : ℝ))) :=
          codeFunction_product_dyadic h_uniform hΔ hΔ1 (by linarith)
        have h_cf_j : (∏ i ∈ Finset.range j, (N i : ℝ)) = Real.rpow Δ (-(f (j : ℝ))) :=
          codeFunction_product_dyadic h_uniform hΔ hΔ1 (by linarith)

        -- Exact f(m) cancellation bound
        have h_fj_lower : f (j : ℝ) ≥ s0 * (j : ℝ) - E := h_lower_j j hj_le_m
        have h_9B : (9 : ℝ) * B_real = (9 : ℝ) ^ (m - j + 1) * Prod_N := by
          dsimp only [B_real] <;> ring

        -- Lower bound on covering(P) with exact f(m)
        have h_lower : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≥
            ENNReal.ofReal (Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m) := by
          have h1 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≥
              (↑(∏ i ∈ Finset.range m, N i) : ENNReal) / (36 : ENNReal) ^ m :=
            dyadic_covering_product_lower h_uniform hΔ hΔ1 hΔ2
          have h2 : (↑(∏ i ∈ Finset.range m, N i) : ENNReal) =
              ENNReal.ofReal (∏ i ∈ Finset.range m, (N i : ℝ)) := by
            have h21 : ∀ (n : ℕ), (↑n : ENNReal) = ENNReal.ofReal (↑n : ℝ) := by
              intro n; simp
            have h22 : ((↑(∏ i ∈ Finset.range m, N i) : ℝ)) = (∏ i ∈ Finset.range m, (N i : ℝ)) := by
              simp <;> norm_cast
            rw [h21 (∏ i ∈ Finset.range m, N i), h22]
          rw [h2] at h1
          have h3 : ENNReal.ofReal (∏ i ∈ Finset.range m, (N i : ℝ)) / (36 : ENNReal) ^ m =
              ENNReal.ofReal ((∏ i ∈ Finset.range m, (N i : ℝ)) / (36 : ℝ) ^ m) := by
            have h4 : (36 : ENNReal) ^ m = ENNReal.ofReal ((36 : ℝ) ^ m) := by simp <;> rfl
            rw [h4]
            rw [← ENNReal.ofReal_div_of_pos (show (0 : ℝ) < (36 : ℝ) ^ m by positivity)] <;> rfl
          rw [h3] at h1
          rw [h_cf_m] at h1
          exact h1

        -- Key constant check using exact f(m) cancellation:
        -- 9^(m-j+1) * 4^m * Δ^(f(j)) ≤ C * r^s0
        have h_rpow_fj : Real.rpow Δ (f (j : ℝ)) ≤ Real.rpow Δ (s0 * (j : ℝ) - E) :=
          Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le h_fj_lower
        have h_base := bounded_slope_constant_check hΔ hΔ1 hΔ2 h_r_pos h_r_lt_one.le hs0_nonneg hs0_le_4 hE_nonneg hm_pos hj_pos hj_lt_m h_le
        have h_pos_coeff : 0 ≤ (9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m := by positivity
        have h_const : (9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m * Real.rpow Δ (f (j : ℝ)) ≤
            C * r ^ s0 := by
          have h1 : (9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m * Real.rpow Δ (f (j : ℝ)) ≤
              (9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m * Real.rpow Δ (s0 * (j : ℝ) - E) :=
            mul_le_mul_of_nonneg_left h_rpow_fj h_pos_coeff
          have h2 : (9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m * Real.rpow Δ (s0 * (j : ℝ) - E) ≤
              dictionaryConstant m Δ * Real.rpow Δ (-E) * r ^ s0 := h_base
          have h_pos_r : 0 ≤ r ^ s0 := by positivity
          have h3 : dictionaryConstant m Δ * Real.rpow Δ (-E) * r ^ s0 ≤ C * r ^ s0 :=
            mul_le_mul_of_nonneg_right hC h_pos_r
          exact le_trans (le_trans h1 h2) h3

        -- Upper bound: 9*B_real ≤ C * r^s0 * Δ^(-f(m)) / 36^m
        have h_final_real : (9 : ℝ) * B_real ≤
            C * r ^ s0 * Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m := by
          rw [h_9B, h_prod1, h_cf_m, h_cf_j]
          have h_pos_fj : 0 < Real.rpow Δ (-(f (j : ℝ))) := Real.rpow_pos_of_pos hΔ _
          have h_div : Real.rpow Δ (-(f (m : ℝ))) / Real.rpow Δ (-(f (j : ℝ))) =
              Real.rpow Δ (-(f (m : ℝ)) + f (j : ℝ)) := by
            have h_sum : (-(f (m : ℝ)) + f (j : ℝ)) + (-(f (j : ℝ))) = -(f (m : ℝ)) := by ring
            have h_rpow : Real.rpow Δ ((-(f (m : ℝ)) + f (j : ℝ)) + (-(f (j : ℝ)))) =
                Real.rpow Δ (-(f (m : ℝ)) + f (j : ℝ)) * Real.rpow Δ (-(f (j : ℝ))) :=
              Real.rpow_add hΔ (-(f (m : ℝ)) + f (j : ℝ)) (-(f (j : ℝ)))
            have h_eq : Real.rpow Δ (-(f (m : ℝ))) =
                Real.rpow Δ (-(f (m : ℝ)) + f (j : ℝ)) * Real.rpow Δ (-(f (j : ℝ))) := by
              rw [h_sum] at h_rpow; exact h_rpow
            rw [h_eq] <;> field_simp [h_pos_fj.ne'] <;> ring
          rw [h_div]
          have h_eq2 : (9 : ℝ) ^ (m - j + 1) * Real.rpow Δ (-(f (m : ℝ)) + f (j : ℝ)) =
              ((9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m * Real.rpow Δ (f (j : ℝ))) *
                Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m := by
            have h_sum2 : -(f (m : ℝ)) + f (j : ℝ) = f (j : ℝ) + (-(f (m : ℝ))) := by ring
            rw [h_sum2]
            have h_rpow_add2 : Real.rpow Δ (f (j : ℝ) + (-(f (m : ℝ)))) =
                Real.rpow Δ (f (j : ℝ)) * Real.rpow Δ (-(f (m : ℝ))) :=
              Real.rpow_add hΔ (f (j : ℝ)) (-(f (m : ℝ)))
            rw [h_rpow_add2] <;> field_simp <;> ring
          rw [h_eq2]
          have h_pos_fm : 0 ≤ Real.rpow Δ (-(f (m : ℝ))) := by
            apply Real.rpow_nonneg
            exact hΔ.le
          have h_pos_36m : 0 ≤ (36 : ℝ) ^ m := by positivity
          have h_mul : ((9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m * Real.rpow Δ (f (j : ℝ))) *
                Real.rpow Δ (-(f (m : ℝ))) ≤
              (C * r ^ s0) * Real.rpow Δ (-(f (m : ℝ))) :=
            mul_le_mul_of_nonneg_right h_const h_pos_fm
          have h : ((9 : ℝ) ^ (m - j + 1) * (36 : ℝ) ^ m * Real.rpow Δ (f (j : ℝ))) *
                Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m ≤
              C * r ^ s0 * Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m :=
            div_le_div_of_nonneg_right h_mul h_pos_36m
          exact h

        have h_rpow_s : (ENNReal.ofReal r) ^ s0 = ENNReal.ofReal (r ^ s0) :=
          ENNReal.ofReal_rpow_of_nonneg (by linarith) hs0_nonneg
        have h_goal : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
            ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 *
              (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
          have h6 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 *
                (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≥
              ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 *
                ENNReal.ofReal (Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m) := by
            gcongr
          have h_step1 : ENNReal.ofReal C * ENNReal.ofReal (r ^ s0) = ENNReal.ofReal (C * r ^ s0) := by
            rw [← ENNReal.ofReal_mul (show 0 ≤ C by positivity)]
          have h_step2 : ENNReal.ofReal (C * r ^ s0) * ENNReal.ofReal (Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m) =
              ENNReal.ofReal ((C * r ^ s0) * (Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m)) := by
            rw [← ENNReal.ofReal_mul (show 0 ≤ C * r ^ s0 by positivity)]
          have h7 : ENNReal.ofReal C * ENNReal.ofReal (r ^ s0) * ENNReal.ofReal (Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m) =
              ENNReal.ofReal (C * (r ^ s0) * (Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m)) := by
            have h_assoc : ENNReal.ofReal C * ENNReal.ofReal (r ^ s0) * ENNReal.ofReal (Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m) =
                (ENNReal.ofReal C * ENNReal.ofReal (r ^ s0)) * ENNReal.ofReal (Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m) := by ring
            rw [h_assoc, h_step1, h_step2] <;> rfl
          have h_final_real3 : (9 : ℝ) * B_real ≤
              C * (r ^ s0) * (Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m) := by
            have h_eq : C * r ^ s0 * Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m =
                C * (r ^ s0) * (Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m) := by ring
            rw [h_eq] at h_final_real
            exact h_final_real
          have h8 : ENNReal.ofReal ((9 : ℝ) * B_real) ≤
              ENNReal.ofReal (C * (r ^ s0) * (Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m)) := by
            apply ENNReal.ofReal_le_ofReal
            exact h_final_real3
          have h6' : ENNReal.ofReal (C * (r ^ s0) * (Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m)) ≤
              ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
            have h_temp : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≥
                ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 * ENNReal.ofReal (Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m) := h6
            have h_temp2 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s0 * ENNReal.ofReal (Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m) =
                ENNReal.ofReal (C * (r ^ s0) * (Real.rpow Δ (-(f (m : ℝ))) / (36 : ℝ) ^ m)) := by
              rw [h_rpow_s, h7]
            rw [h_temp2] at h_temp
            exact h_temp
          exact le_trans h_upper4 (le_trans h8 h6')
        exact h_goal
  exact ⟨hP_nonempty, hδ_pos, hC_pos, hs0_nonneg, h_main_goal⟩

end MultiscaleDecomposition

end
