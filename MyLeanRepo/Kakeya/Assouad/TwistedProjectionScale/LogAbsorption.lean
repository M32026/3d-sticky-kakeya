import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Absorb logarithmic losses by positive powers of δ

For any `K > 0`, `B > 0`, and `n > 0`, logarithmic growth `(log δ⁻¹)^n`
is eventually dominated by `δ^{-B}`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- For any `K > 0`, `B > 0`, and `n > 0`, there exists `δ₀ > 0` such that
for all `0 < δ ≤ δ₀`, `K * (1 + log δ⁻¹)^n ≤ δ^(-B)`. -/
lemma exists_delta_log_absorbed
    (K : ℝ) (hK : 0 < K) {B : ℝ} (hB : 0 < B) {n : ℕ} (hn_pos : 0 < n) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        K * (1 + Real.log δ⁻¹)^n ≤ Real.rpow δ (-B) := by
  set c : ℝ := B / (2 * (n : ℝ)) with hc_def
  have hc_pos : 0 < c := by positivity
  have hnc : (n : ℝ) * c = B / 2 := by
    rw [hc_def]
    field_simp [hn_pos.ne'] <;> ring
  set C0 : ℝ := K * (2 / c)^n with hC0_def
  have hC0_pos : 0 < C0 := by positivity
  set X3 : ℝ := Real.rpow C0 (2 / B) with hX3_def
  have hX3_pos : 0 < X3 := by
    dsimp only [X3]
    have h_eq : Real.rpow C0 (2 / B) =
        Real.exp (Real.log C0 * (2 / B)) :=
      Real.rpow_def_of_pos hC0_pos (2 / B)
    rw [h_eq]
    exact Real.exp_pos _
  set einv : ℝ := Real.exp (-1) with heinv_def
  have heinv_pos : 0 < einv := by positivity
  set δ₀ : ℝ := min einv X3⁻¹ with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le1 : δ₀ ≤ 1 := by
    have h : einv ≤ 1 := by
      dsimp only [einv]
      have h2 : Real.exp (-1 : ℝ) < 1 :=
        Real.exp_lt_one_iff.mpr (by norm_num)
      linarith
    have h3 : δ₀ ≤ einv := min_le_left _ _
    linarith
  refine' ⟨δ₀, hδ₀_pos, hδ₀_le1, _⟩
  intro δ hδ hδ_le
  have hδ_le_einv : δ ≤ einv :=
    hδ_le.trans (min_le_left _ _)
  have hδ_leX3 : δ ≤ X3⁻¹ :=
    hδ_le.trans (min_le_right _ _)
  set x : ℝ := δ⁻¹ with hx_def
  have hx_pos : 0 < x := by positivity
  have hx_nonneg : 0 ≤ x := by linarith
  have hx_ge1 : x ≥ 1 := by
    have h3 : δ ≤ 1 := hδ_le.trans hδ₀_le1
    have h4 : δ⁻¹ ≥ 1 := by
      calc
        δ⁻¹ ≥ 1⁻¹ := by gcongr
        _ = 1 := by norm_num
    exact h4
  have hx_ge_e : x ≥ Real.exp 1 := by
    have h4 : δ⁻¹ ≥ einv⁻¹ := by gcongr
    have h5 : einv⁻¹ = Real.exp 1 := by
      dsimp only [einv]
      rw [← Real.exp_neg]
      simp
    rw [h5] at h4
    exact h4
  have hlog_ge1 : 1 ≤ Real.log x := by
    have h2 : Real.log (Real.exp 1) ≤ Real.log x :=
      Real.log_le_log (by positivity) hx_ge_e
    simpa using h2
  have hlog_le : Real.log x ≤ Real.rpow x c / c :=
    Real.log_le_rpow_div hx_nonneg hc_pos
  have h1 : 1 + Real.log x ≤ 2 * Real.log x := by
    linarith
  have h_rpow_mul :
      (Real.rpow x c)^n =
        Real.rpow x ((n : ℝ) * c) := by
    have h51 :
        (Real.rpow x c)^n =
          Real.rpow (Real.rpow x c) (n : ℝ) := by
      rw [← Real.rpow_natCast]
      rfl
    rw [h51]
    have h52 :
        Real.rpow (Real.rpow x c) (n : ℝ) =
          Real.rpow x (c * (n : ℝ)) :=
      (Real.rpow_mul hx_nonneg c (n : ℝ)).symm
    rw [h52]
    ring_nf
  have h6 :
      K * (1 + Real.log x)^n ≤
        C0 * Real.rpow x (B / 2) := by
    calc
      K * (1 + Real.log x)^n
          ≤ K * (2 * Real.log x)^n := by gcongr
      _ ≤ K * (2 * (Real.rpow x c / c))^n := by gcongr
      _ = K * ((2 / c)^n * (Real.rpow x c)^n) := by ring
      _ = K *
          ((2 / c)^n * Real.rpow x ((n : ℝ) * c)) := by
        rw [h_rpow_mul]
      _ = K * ((2 / c)^n * Real.rpow x (B / 2)) := by
        rw [hnc]
      _ = C0 * Real.rpow x (B / 2) := by
        dsimp only [C0]
        ring
  have hx_ge_X3 : x ≥ X3 := by
    have h4 : δ⁻¹ ≥ (X3⁻¹)⁻¹ := by gcongr
    have h5 : (X3⁻¹)⁻¹ = X3 := by
      field_simp [hX3_pos.ne']
    rw [h5] at h4
    exact h4
  have h7 : C0 ≤ Real.rpow x (B / 2) := by
    have h8 :
        Real.rpow X3 (B / 2) ≤
          Real.rpow x (B / 2) :=
      Real.rpow_le_rpow (by linarith) hx_ge_X3 (by linarith)
    have h9 : Real.rpow X3 (B / 2) = C0 := by
      dsimp only [X3]
      have h10 :
          Real.rpow (Real.rpow C0 (2 / B)) (B / 2) =
            Real.rpow C0 ((2 / B) * (B / 2)) :=
        (Real.rpow_mul (by positivity) (2 / B) (B / 2)).symm
      rw [h10]
      have h11 : (2 / B) * (B / 2) = 1 := by
        field_simp [hB.ne']
      rw [h11]
      exact Real.rpow_one C0
    rw [h9] at h8
    exact h8
  have h12 :
      Real.rpow x (B / 2) * Real.rpow x (B / 2) =
        Real.rpow x B := by
    have hadd :
        Real.rpow x (B / 2 + B / 2) =
          Real.rpow x (B / 2) * Real.rpow x (B / 2) :=
      Real.rpow_add hx_pos _ _
    have hsum : B / 2 + B / 2 = B := by ring
    rw [hsum] at hadd
    exact hadd.symm
  have h10 :
      C0 * Real.rpow x (B / 2) ≤ Real.rpow x B := by
    have h11 : C0 * Real.rpow x (B / 2) ≤
        Real.rpow x (B / 2) * Real.rpow x (B / 2) := by
      gcongr <;> linarith
    rw [h12] at h11
    exact h11
  have h13 :
      K * (1 + Real.log x)^n ≤ Real.rpow x B :=
    h6.trans h10
  have h14 : Real.rpow x B = Real.rpow δ (-B) := by
    have h15 : x = δ⁻¹ := by simp [hx_def]
    rw [h15]
    have h16 :
        Real.rpow δ⁻¹ B =
          Real.exp (B * Real.log δ⁻¹) := by
      calc
        Real.rpow δ⁻¹ B =
            Real.exp (Real.log δ⁻¹ * B) :=
          Real.rpow_def_of_pos (by positivity) B
        _ = Real.exp (B * Real.log δ⁻¹) := by rw [mul_comm]
    have h17 :
        Real.rpow δ (-B) =
          Real.exp ((-B) * Real.log δ) := by
      calc
        Real.rpow δ (-B) =
            Real.exp (Real.log δ * (-B)) :=
          Real.rpow_def_of_pos hδ (-B)
        _ = Real.exp ((-B) * Real.log δ) := by rw [mul_comm]
    rw [h16, h17, Real.log_inv]
    congr 1
    ring
  simpa [hx_def] using h13.trans_eq h14

/--
For any real `N > 0` and `k > 0`, there exists `δ₀ > 0` such that
for all `0 < δ ≤ δ₀`, `δ^k * (log δ⁻¹)^N ≤ 1`.
-/
lemma exists_poly_below_log_inv
    {N k : ℝ} (hN : 0 < N) (hk : 0 < k) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        Real.rpow δ k * (Real.log δ⁻¹)^N ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_nat_ge N
  have hn_ge_N : (n : ℝ) ≥ N := by exact_mod_cast hn
  have hn_pos : 0 < n := by
    by_contra h
    have h' : n = 0 := by omega
    rw [h'] at hn_ge_N
    norm_num at hn_ge_N
    linarith
  rcases
      exists_delta_log_absorbed 1 (by norm_num) hk hn_pos with
    ⟨δ₁, hδ₁_pos, hδ₁_le1, hδ₁⟩
  let δ₂ : ℝ := Real.exp (-1)
  have hδ₂_pos : 0 < δ₂ := by positivity
  let δ₀ : ℝ := min δ₁ δ₂
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro δ hδ hδ_le
  have hδ_le1 : δ ≤ δ₁ := hδ_le.trans (min_le_left _ _)
  have hδ_le2 : δ ≤ δ₂ := hδ_le.trans (min_le_right _ _)
  have h_log_ge1 : 1 ≤ Real.log δ⁻¹ := by
    have h4 : δ⁻¹ ≥ (Real.exp (-1))⁻¹ := by
      dsimp only [δ₂] at hδ_le2
      gcongr
    have h5 : (Real.exp (-1))⁻¹ = Real.exp 1 := by
      rw [← Real.exp_neg]
      simp
    rw [h5] at h4
    have h6 :
        Real.log (Real.exp 1) ≤ Real.log δ⁻¹ :=
      Real.log_le_log (by positivity) h4
    simpa using h6
  have h1 :
      (Real.log δ⁻¹)^N ≤ (Real.log δ⁻¹)^n := by
    calc
      (Real.log δ⁻¹)^N
          ≤ (Real.log δ⁻¹)^(n : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h_log_ge1 hn_ge_N
      _ = (Real.log δ⁻¹)^n := by rw [Real.rpow_natCast]
  have h2 :
      (Real.log δ⁻¹)^n ≤
        (1 + Real.log δ⁻¹)^n := by
    gcongr
    linarith
  have h4 :
      (1 + Real.log δ⁻¹)^n ≤ Real.rpow δ (-k) := by
    simpa using hδ₁ δ hδ hδ_le1
  have h5 :
      (Real.log δ⁻¹)^N ≤ Real.rpow δ (-k) :=
    h1.trans (h2.trans h4)
  have h7 :
      Real.rpow δ k * (Real.log δ⁻¹)^N ≤
        Real.rpow δ k * Real.rpow δ (-k) := by
    exact mul_le_mul_of_nonneg_left h5
      (Real.rpow_nonneg hδ.le k)
  have h8 :
      Real.rpow δ k * Real.rpow δ (-k) = 1 := by
    have h9 :
        Real.rpow δ (k + (-k)) =
          Real.rpow δ k * Real.rpow δ (-k) :=
      Real.rpow_add hδ k (-k)
    have h10 : k + (-k) = 0 := by ring
    have h11 :
        Real.rpow δ k * Real.rpow δ (-k) =
          Real.rpow δ 0 := by
      rw [h10] at h9
      exact h9.symm
    rw [h11]
    simp
  rw [h8] at h7
  exact h7

end Kakeya.Assouad
