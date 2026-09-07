module

/-
  Regularity from bounded slope condition.

  If the code function of a uniform set satisfies |f(j) - s0*j| ≤ E for all
  integer j ∈ [0,m], then the set is regular between scales Δ^m and 1 with
  exponent s0 and constant C ≥ dictionaryConstant * Δ^(-E).

  Whiteprint node: multiscale_decomp
  Dependencies: BoundedSlopeToDeltaSSet, LinearToRegular (halfScaleConstantCheck pattern)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.BoundedSlopeToDeltaSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.LinearToRegular
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.SubintervalRescaling
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MultiscaleDecomposition

namespace MultiscaleDecomposition

/-- Constant check for bounded-slope half-scale covering:
  `9^k * Δ^(-(s*k + E)) ≤ dictionaryConstant m Δ * Δ^(-E) * (Δ^m)^(-s/2)`. -/
lemma boundedSlopeHalfScaleConstantCheck (m : ℕ) (hm_pos : 0 < m) (Δ : ℝ)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (s : ℝ) (hs_nonneg : 0 ≤ s) (hs_le_4 : s ≤ 4)
    (E : ℝ) (hE_nonneg : 0 ≤ E)
    (k : ℕ) (hk_ge : (k : ℝ) ≥ (m : ℝ) / 2) (hk_le : k ≤ m)
    (h2k_le : 2 * k ≤ m + 1) :
    (9 : ℝ) ^ k * Real.rpow Δ (-(s * (k : ℝ) + E)) ≤
      (dictionaryConstant m Δ * Real.rpow Δ (-E)) * Real.rpow (Δ ^ m) (-s / 2) := by
  have h_ineq : (3 : ℝ) ^ (m + 1) * Real.rpow Δ (-s / 2) ≤ Δ^(-4 : ℝ) * (324 : ℝ) ^ m := by
    have h6 : Real.rpow Δ (-s / 2) ≤ Δ^(-4 : ℝ) := by
      have h7 : -s / 2 ≥ (-4 : ℝ) := by linarith [hs_le_4]
      exact Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le h7
    have h8 : (3 : ℝ) ^ (m + 1) ≤ (324 : ℝ) ^ m := by
      have h9 : m ≥ 1 := by omega
      have h10 : (3 : ℝ) ^ (m + 1) = 3 * (3 : ℝ) ^ m := by simp [pow_succ] <;> ring
      rw [h10]
      have h11 : (3 : ℝ) ^ m ≤ (108 : ℝ) ^ m := by gcongr <;> norm_num
      have h12 : 3 * (3 : ℝ) ^ m ≤ 3 * (108 : ℝ) ^ m := by gcongr
      have h13 : 3 * (108 : ℝ) ^ m ≤ (324 : ℝ) ^ m := by
        have h14 : (324 : ℝ) = 3 * (108 : ℝ) := by norm_num
        rw [h14]
        have h15 : (3 * (108 : ℝ)) ^ m = (3 : ℝ) ^ m * (108 : ℝ) ^ m := by rw [mul_pow]
        rw [h15]
        have h16 : (3 : ℝ) ^ m ≥ 3 := by
          have h17 : m ≥ 1 := h9
          have h18 : ∀ n : ℕ, n ≥ 1 → (3 : ℝ) ^ n ≥ 3 := by
            intro n hn
            induction' hn with n hn ih
            · norm_num
            · simp [pow_succ] at * <;> nlinarith
          exact h18 m h17
        have h19 : 0 ≤ (108 : ℝ) ^ m := by positivity
        nlinarith
      exact h12.trans h13
    calc (3 : ℝ) ^ (m + 1) * Real.rpow Δ (-s / 2)
      ≤ (3 : ℝ) ^ (m + 1) * Δ^(-4 : ℝ) := by gcongr
    _ ≤ (324 : ℝ) ^ m * Δ^(-4 : ℝ) := by gcongr
    _ = Δ^(-4 : ℝ) * (324 : ℝ) ^ m := by ring
  have h_rpow_expand : Real.rpow Δ (-s * (((m : ℝ) + 1) / 2) - E) =
      Real.rpow Δ (-s * (m : ℝ) / 2) * Real.rpow Δ (-s / 2) * Real.rpow Δ (-E) := by
    have h_sum : -s * (((m : ℝ) + 1) / 2) - E =
        (-s * (m : ℝ) / 2) + (-s / 2) + (-E) := by ring
    rw [h_sum]
    have h_step1 : Real.rpow Δ (((-s * (m : ℝ) / 2) + (-s / 2)) + (-E)) =
        Real.rpow Δ ((-s * (m : ℝ) / 2) + (-s / 2)) * Real.rpow Δ (-E) :=
      Real.rpow_add hΔ _ _
    rw [h_step1]
    have h_step2 : Real.rpow Δ ((-s * (m : ℝ) / 2) + (-s / 2)) =
        Real.rpow Δ (-s * (m : ℝ) / 2) * Real.rpow Δ (-s / 2) :=
      Real.rpow_add hΔ _ _
    rw [h_step2] <;> ring
  have h_rpow_delta1 : Real.rpow Δ (-s * (m : ℝ) / 2) = Real.rpow (Δ ^ m) (-s / 2) := by
    have h_eq1 : -s * (m : ℝ) / 2 = (m : ℝ) * (-s / 2) := by ring
    have h_nat : Real.rpow Δ (m : ℝ) = (Δ ^ m : ℝ) := by simp
    calc
      Real.rpow Δ (-s * (m : ℝ) / 2)
        = Real.rpow Δ ((m : ℝ) * (-s / 2)) := by rw [h_eq1]
      _ = (Real.rpow Δ (m : ℝ)) ^ (-s / 2) := by
        exact Real.rpow_mul hΔ.le (m : ℝ) (-s / 2)
      _ = Real.rpow (Real.rpow Δ (m : ℝ)) (-s / 2) := by rfl
      _ = Real.rpow (Δ ^ m) (-s / 2) := by rw [h_nat]
  have h1 : (9 : ℝ) ^ k ≤ (3 : ℝ) ^ (m + 1) := by
    have h2 : (9 : ℝ) ^ k = (3 : ℝ) ^ (2 * k) := by
      have h3 : ∀ n : ℕ, (9 : ℝ) ^ n = (3 : ℝ) ^ (2 * n) := by
        intro n; induction n <;> simp [*, pow_succ] <;> ring
      exact h3 k
    have h9 : (3 : ℝ) ^ (2 * k) ≤ (3 : ℝ) ^ (m + 1) := by
      have h10 : 2 * k ≤ m + 1 := h2k_le
      have h11 : ∀ (n1 n2 : ℕ), n1 ≤ n2 → (3 : ℝ) ^ n1 ≤ (3 : ℝ) ^ n2 := by
        intro n1 n2 h
        induction' h with n2 h ih
        · simp
        · have h12 : (3 : ℝ) ^ n2 ≤ (3 : ℝ) ^ (n2 + 1) := by
            simp [pow_succ] <;> norm_num <;> nlinarith
          exact le_trans ih h12
      exact h11 (2 * k) (m + 1) h10
    rw [h2]
    exact h9
  have h4 : Real.rpow Δ (-(s * (k : ℝ) + E)) ≤
      Real.rpow Δ (-s * (((m : ℝ) + 1) / 2) - E) := by
    have h5 : -(s * (k : ℝ) + E) ≥ -s * (((m : ℝ) + 1) / 2) - E := by
      have h6 : (k : ℝ) ≤ ((m : ℝ) + 1) / 2 := by
        have h : (2 : ℝ) * (k : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast h2k_le
        linarith
      nlinarith [hs_nonneg]
    exact Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le h5
  have h_pos3 : 0 ≤ Real.rpow Δ (-s * (m : ℝ) / 2) * Real.rpow Δ (-E) :=
    mul_nonneg (Real.rpow_pos_of_pos hΔ _).le (Real.rpow_pos_of_pos hΔ _).le
  have h_pos_rpow : 0 ≤ Real.rpow Δ (-(s * (k : ℝ) + E)) :=
    Real.rpow_nonneg hΔ.le (-(s * (k : ℝ) + E))
  have h_step1 : (9 : ℝ) ^ k * Real.rpow Δ (-(s * (k : ℝ) + E)) ≤
      (3 : ℝ) ^ (m + 1) * Real.rpow Δ (-(s * (k : ℝ) + E)) :=
    mul_le_mul_of_nonneg_right h1 h_pos_rpow
  have h_step2 : (3 : ℝ) ^ (m + 1) * Real.rpow Δ (-(s * (k : ℝ) + E)) ≤
      (3 : ℝ) ^ (m + 1) * Real.rpow Δ (-s * (((m : ℝ) + 1) / 2) - E) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  calc (9 : ℝ) ^ k * Real.rpow Δ (-(s * (k : ℝ) + E))
    ≤ (3 : ℝ) ^ (m + 1) * Real.rpow Δ (-(s * (k : ℝ) + E)) := h_step1
  _ ≤ (3 : ℝ) ^ (m + 1) * Real.rpow Δ (-s * (((m : ℝ) + 1) / 2) - E) := h_step2
  _ = (3 : ℝ) ^ (m + 1) * (Real.rpow Δ (-s * (m : ℝ) / 2) * Real.rpow Δ (-s / 2) * Real.rpow Δ (-E)) := by
      rw [h_rpow_expand] <;> ring
  _ = ((3 : ℝ) ^ (m + 1) * Real.rpow Δ (-s / 2)) * (Real.rpow Δ (-s * (m : ℝ) / 2) * Real.rpow Δ (-E)) := by ring
  _ ≤ (Δ^(-4 : ℝ) * (324 : ℝ) ^ m) * (Real.rpow Δ (-s * (m : ℝ) / 2) * Real.rpow Δ (-E)) := by
      exact mul_le_mul_of_nonneg_right h_ineq h_pos3
  _ = (Δ^(-4 : ℝ) * (324 : ℝ) ^ m) * Real.rpow (Δ ^ m) (-s / 2) * Real.rpow Δ (-E) := by
      rw [h_rpow_delta1] <;> ring
  _ = (dictionaryConstant m Δ * Real.rpow Δ (-E)) * Real.rpow (Δ ^ m) (-s / 2) := by
      simp only [dictionaryConstant] <;> ring

/-- Half-scale covering bound from bounded slope condition. -/
lemma boundedSlopeHalfScaleCovering {P' : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform' : IsDyadicUniform P' m Δ N)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (s0 E C : ℝ) (hs0_nonneg : 0 ≤ s0) (hs0_le_4 : s0 ≤ 4)
    (hE_nonneg : 0 ≤ E)
    (hC : dictionaryConstant m Δ * Real.rpow Δ (-E) ≤ C)
    (hm_pos : 0 < m)
    (h_bounds : ∀ (j : ℕ), j ≤ m → |codeFunction m Δ N (j : ℝ) - s0 * (j : ℝ)| ≤ E)
    (hP'_sub : P' ⊆ dyadicSquare 1 0 0) :
    (Metric.externalCoveringNumber (Real.sqrt (Δ ^ m)).toNNReal P' : ENNReal) ≤
      ENNReal.ofReal (C * Real.rpow (Δ ^ m) (-s0 / 2)) := by
  set f : ℝ → ℝ := codeFunction m Δ N with hf_def
  set δ : ℝ := Δ ^ m with hδ_def
  let k : ℕ := Nat.ceil ((m : ℝ) / 2)
  have hk_ge : (k : ℝ) ≥ (m : ℝ) / 2 := Nat.le_ceil _
  have hk_le : k ≤ m := by
    apply Nat.ceil_le.mpr
    have h : (m : ℝ) / 2 ≤ (m : ℝ) := by linarith [hm_pos]
    exact h
  have hk_pos : 0 < k := by
    have h_pos : 0 < (m : ℝ) := by exact_mod_cast hm_pos
    have h : 0 < (m : ℝ) / 2 := by positivity
    exact Nat.ceil_pos.mpr h
  have h2k_le : 2 * k ≤ m + 1 := by
    have h_nonneg : 0 ≤ (m : ℝ) / 2 := by positivity
    have h : (k : ℝ) < (m : ℝ) / 2 + 1 := Nat.ceil_lt_add_one h_nonneg
    have h' : (2 : ℝ) * (k : ℝ) < (m : ℝ) + 2 := by linarith
    have h_int : 2 * k < m + 2 := by exact_mod_cast h'
    omega
  have h_delta_k_le_sqrt : (Δ ^ k : ℝ) ≤ Real.sqrt δ := by
    have h2 : (Δ ^ k : ℝ) ≤ Real.rpow Δ ((m : ℝ) / 2) := by
      have h_eq : (Δ ^ k : ℝ) = Real.rpow Δ (k : ℝ) := by simp
      rw [h_eq]
      exact Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le hk_ge
    have h_pos1 : 0 ≤ Real.rpow Δ ((m : ℝ) / 2) := Real.rpow_nonneg hΔ.le _
    have h_sq1 : (Real.rpow Δ ((m : ℝ) / 2)) ^ 2 = Δ ^ m := by
      have h_mul : (Real.rpow Δ ((m : ℝ) / 2)) ^ 2 =
          Real.rpow Δ ((m : ℝ) / 2) * Real.rpow Δ ((m : ℝ) / 2) := by ring
      rw [h_mul]
      have h_add : Real.rpow Δ ((m : ℝ) / 2) * Real.rpow Δ ((m : ℝ) / 2) =
          Real.rpow Δ (((m : ℝ) / 2) + ((m : ℝ) / 2)) :=
        (Real.rpow_add hΔ ((m : ℝ) / 2) ((m : ℝ) / 2)).symm
      rw [h_add]
      have h4 : (m : ℝ) / 2 + (m : ℝ) / 2 = (m : ℝ) := by ring
      rw [h4] <;> simp
    have h_sq2 : (Real.sqrt (Δ ^ m)) ^ 2 = Δ ^ m := by rw [Real.sq_sqrt] <;> positivity
    have h_pos2 : 0 ≤ Real.sqrt (Δ ^ m) := Real.sqrt_nonneg _
    have h_eq_sq : (Real.rpow Δ ((m : ℝ) / 2)) ^ 2 = (Real.sqrt (Δ ^ m)) ^ 2 := by
      rw [h_sq1, h_sq2]
    have h3 : Real.rpow Δ ((m : ℝ) / 2) = Real.sqrt (Δ ^ m) := by
      nlinarith [h_pos1, h_pos2, h_eq_sq]
    calc (Δ ^ k : ℝ)
      ≤ Real.rpow Δ ((m : ℝ) / 2) := h2
    _ = Real.sqrt (Δ ^ m) := h3
    _ = Real.sqrt δ := by rw [hδ_def]
  have h_toNNReal_le : (Δ ^ k).toNNReal ≤ (Real.sqrt δ).toNNReal := by
    apply Real.toNNReal_le_toNNReal <;> linarith [h_delta_k_le_sqrt]
  have h_anti : (Metric.externalCoveringNumber (Real.sqrt δ).toNNReal P' : ENNReal) ≤
      (Metric.externalCoveringNumber (Δ ^ k).toNNReal P' : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_anti h_toNNReal_le
  have h_uniform_k : IsDyadicUniform P' k Δ N :=
    ⟨h_uniform'.1, h_uniform'.2.1, h_uniform'.2.2.1,
     fun i hi => h_uniform'.2.2.2.1 i (by linarith),
     fun i hi => h_uniform'.2.2.2.2 i (by linarith)⟩
  have hP'_inter : (P' ∩ dyadicSquare (Δ ^ 0) 0 0).Nonempty := by
    have h1 : (Δ ^ 0 : ℝ) = 1 := by simp
    have h_eq : P' ∩ dyadicSquare (Δ ^ 0) 0 0 = P' := by rw [h1]; exact Set.inter_eq_left.mpr hP'_sub
    rw [h_eq]; exact h_uniform'.2.2.1
  have h_upper : (Metric.externalCoveringNumber (Δ ^ k).toNNReal (P' ∩ dyadicSquare (Δ ^ 0) 0 0) : ENNReal) ≤
      (9 : ENNReal) ^ k * ∏ i ∈ Finset.range k, (↑(N i) : ENNReal) := by
    simpa using dyadicCovering_product_upper h_uniform_k (by linarith) 0 0 hP'_inter
  have h_eq : P' ∩ dyadicSquare (Δ ^ 0) 0 0 = P' := by
    have h1 : (Δ ^ 0 : ℝ) = 1 := by simp
    rw [h1]
    exact Set.inter_eq_left.mpr hP'_sub
  rw [h_eq] at h_upper
  have h_f_k_upper : f (k : ℝ) ≤ s0 * (k : ℝ) + E := by
    have h := h_bounds k hk_le
    have h' : f (k : ℝ) - s0 * (k : ℝ) ≤ E := by
      linarith [abs_le.mp h]
    linarith
  have h_prod : (∏ i ∈ Finset.range k, (N i : ℝ)) = Real.rpow Δ (-(f (k : ℝ))) :=
    codeFunction_product_dyadic h_uniform' hΔ hΔ1 (by linarith)
  have h_prod_upper : (∏ i ∈ Finset.range k, (N i : ℝ)) ≤
      Real.rpow Δ (-(s0 * (k : ℝ) + E)) := by
    rw [h_prod]
    have h_exp : -(f (k : ℝ)) ≥ -(s0 * (k : ℝ) + E) := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le h_exp
  have h_const : (9 : ℝ) ^ k * Real.rpow Δ (-(s0 * (k : ℝ) + E)) ≤
      (dictionaryConstant m Δ * Real.rpow Δ (-E)) * Real.rpow (Δ ^ m) (-s0 / 2) :=
    boundedSlopeHalfScaleConstantCheck m hm_pos Δ hΔ hΔ1 s0 hs0_nonneg hs0_le_4 E hE_nonneg
      k hk_ge hk_le h2k_le
  have h_rpow_nonneg : 0 ≤ Real.rpow (Δ ^ m) (-s0 / 2) := Real.rpow_nonneg (by positivity) _
  have hC' : (dictionaryConstant m Δ * Real.rpow Δ (-E)) * Real.rpow (Δ ^ m) (-s0 / 2) ≤
      C * Real.rpow (Δ ^ m) (-s0 / 2) := by
    exact mul_le_mul_of_nonneg_right hC h_rpow_nonneg
  have h_prod_coe : (∏ i ∈ Finset.range k, (↑(N i) : ENNReal)) =
      ENNReal.ofReal (∏ i ∈ Finset.range k, (N i : ℝ)) := by
    have h1 : (∏ i ∈ Finset.range k, (↑(N i) : ENNReal)) = ↑(∏ i ∈ Finset.range k, N i) := by
      rw [← Nat.cast_prod] <;> rfl
    rw [h1]
    have h2 : (↑(∏ i ∈ Finset.range k, N i) : ENNReal) =
        ENNReal.ofReal ((↑(∏ i ∈ Finset.range k, N i) : ℝ)) := by exact Eq.symm (ENNReal.ofReal_natCast (∏ i ∈ Finset.range k, N i))
    rw [h2]
    have h3 : ((↑(∏ i ∈ Finset.range k, N i) : ℝ)) = (∏ i ∈ Finset.range k, (N i : ℝ)) := by
      simp <;> norm_cast
    rw [h3]
  rw [h_prod_coe] at h_upper
  have h4 : (9 : ENNReal) ^ k * ENNReal.ofReal (∏ i ∈ Finset.range k, (N i : ℝ)) =
      ENNReal.ofReal ((9 : ℝ) ^ k * (∏ i ∈ Finset.range k, (N i : ℝ))) := by
    have h9 : (9 : ENNReal) ^ k = ENNReal.ofReal ((9 : ℝ) ^ k) := by simp
    rw [h9]
    rw [ENNReal.ofReal_mul (by positivity)] <;> rfl
  rw [h4] at h_upper
  have h5 : ENNReal.ofReal ((9 : ℝ) ^ k * (∏ i ∈ Finset.range k, (N i : ℝ))) ≤
      ENNReal.ofReal ((9 : ℝ) ^ k * Real.rpow Δ (-(s0 * (k : ℝ) + E))) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left h_prod_upper (by positivity)
  have h_final : (Metric.externalCoveringNumber (Δ ^ k).toNNReal P' : ENNReal) ≤
      ENNReal.ofReal (C * Real.rpow (Δ ^ m) (-s0 / 2)) := by
    calc (Metric.externalCoveringNumber (Δ ^ k).toNNReal P' : ENNReal)
      ≤ ENNReal.ofReal ((9 : ℝ) ^ k * Real.rpow Δ (-(s0 * (k : ℝ) + E))) := le_trans h_upper h5
    _ ≤ ENNReal.ofReal ((dictionaryConstant m Δ * Real.rpow Δ (-E)) * Real.rpow (Δ ^ m) (-s0 / 2)) :=
        ENNReal.ofReal_le_ofReal h_const
    _ ≤ ENNReal.ofReal (C * Real.rpow (Δ ^ m) (-s0 / 2)) :=
        ENNReal.ofReal_le_ofReal hC'
  exact le_trans h_anti h_final

/-- Full regularity from bounded slope condition.

  If the code function satisfies `|f(j) - s0*j| ≤ E` for all `j ≤ m`,
  then P is `(s0, C, C)`-regular between scales `Δ^m` and `1`,
  provided `C ≥ dictionaryConstant m Δ * Δ^(-E)`. -/
lemma boundedSlopeToRegular {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hΔ2 : Δ ≤ 1 / 2)
    (s0 E C : ℝ) (hs0_nonneg : 0 ≤ s0) (hs0_le_4 : s0 ≤ 4)
    (hE_nonneg : 0 ≤ E)
    (hC : dictionaryConstant m Δ * Real.rpow Δ (-E) ≤ C)
    (hm_pos : 0 < m)
    (h_bounds : ∀ (j : ℕ), j ≤ m → |codeFunction m Δ N (j : ℝ) - s0 * (j : ℝ)| ≤ E)
    {n : ℕ} (hn_pos : 0 < n) (h1 : (1 : ℝ) = (n : ℝ) * Δ) :
    IsRegularBetweenScales P (Δ ^ m) 1 s0 C C := by
  set δ : ℝ := Δ ^ m with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have hδ_le_one : δ ≤ 1 := by
    rw [hδ_def]
    have h1' : 0 ≤ Δ := by linarith
    have h2' : Δ ≤ 1 := by linarith
    exact pow_le_one₀ h1' h2'
  have hC_pos : 0 < C := by
    have h_dict_pos : 0 < dictionaryConstant m Δ := by
      dsimp only [dictionaryConstant]; positivity
    have hE_pos : 0 < Real.rpow Δ (-E) := Real.rpow_pos_of_pos hΔ _
    have h : 0 < dictionaryConstant m Δ * Real.rpow Δ (-E) := mul_pos h_dict_pos hE_pos
    exact lt_of_lt_of_le h hC
  have h_set : IsSetBetweenScales P δ 1 s0 C := by
    refine' ⟨hδ_pos, by norm_num, hδ_le_one, hs0_nonneg, hC_pos, _⟩
    intro i j hQ
    let P' := homothetyS 1 i j '' (P ∩ dyadicSquare 1 i j)
    have h_uniform' : IsDyadicUniform P' m Δ N := by
      simpa [pow_zero] using uniform_rescaled_square_dyadic h_uniform hm_pos (by linarith) hn_pos h1 i j hQ
    have h_lower : ∀ (j : ℕ), j ≤ m →
        codeFunction m Δ N (j : ℝ) ≥ s0 * (j : ℝ) - E := by
      intro j hj
      have h := h_bounds j hj
      have h' : -(E) ≤ codeFunction m Δ N (j : ℝ) - s0 * (j : ℝ) := by
        linarith [abs_le.mp h]
      linarith
    have h_result : IsDeltaSSet (Δ ^ m) s0 C P' :=
      boundedSlopeToDeltaSSet h_uniform' hΔ hΔ1 hΔ2 s0 E C hs0_nonneg hs0_le_4 hE_nonneg hC hm_pos h_lower
    simpa [hδ_def] using h_result
  have h_reg : ∀ (i j : ℤ), (P ∩ dyadicSquare 1 i j).Nonempty →
      (Metric.externalCoveringNumber (Real.sqrt δ).toNNReal
         (homothetyS 1 i j '' (P ∩ dyadicSquare 1 i j)) : ENNReal) ≤
        ENNReal.ofReal (C * Real.rpow δ (-s0 / 2)) := by
    intro i j hQ
    let P' := homothetyS 1 i j '' (P ∩ dyadicSquare 1 i j)
    have h_uniform' : IsDyadicUniform P' m Δ N := by
      simpa [pow_zero] using uniform_rescaled_square_dyadic h_uniform hm_pos (by linarith) hn_pos h1 i j hQ
    have hP'_sub : P' ⊆ dyadicSquare 1 0 0 := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have hxQ : x ∈ dyadicSquare 1 i j := hx.2
      simp only [dyadicSquare, Set.mem_setOf_eq] at hxQ ⊢
      have h10 : (homothetyS 1 i j x) 0 = x 0 - (i : ℝ) := by simp [homothetyS] <;> rfl
      have h11 : (homothetyS 1 i j x) 1 = x 1 - (j : ℝ) := by simp [homothetyS] <;> rfl
      rw [h10, h11]
      have h_goal : (x 0 - (i : ℝ)) ∈ Set.Ico (0 : ℝ) 1 ∧ (x 1 - (j : ℝ)) ∈ Set.Ico (0 : ℝ) 1 := by
        constructor
        · exact ⟨by linarith [hxQ.1.1, hxQ.1.2], by linarith [hxQ.1.1, hxQ.1.2]⟩
        · exact ⟨by linarith [hxQ.2.1, hxQ.2.2], by linarith [hxQ.2.1, hxQ.2.2]⟩
      simpa [Set.mem_Ico, mul_one] using h_goal
    exact boundedSlopeHalfScaleCovering h_uniform' hΔ hΔ1 s0 E C hs0_nonneg hs0_le_4 hE_nonneg hC hm_pos h_bounds hP'_sub
  exact ⟨h_set, hC_pos, by simpa [div_one] using h_reg⟩

end MultiscaleDecomposition

end
