import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements
import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Constant absorption and exponent arithmetic for WZ1 Lemma 40

Helper lemmas used in the final step of WZ1 Proposition 41:
1. Upgrade a Lemma 40 lower bound with exponent `epsilon40 - 1` and a constant
   prefactor to the target exponent `epsilon - 1`.
2. Absorb a fixed positive constant into a positive power gap for small `delta`.
3. Monotonicity of `WZ1UniformTripleDensity` in the density constant.
-/

noncomputable section

namespace Kakeya.Assouad

/--
If `X ≥ delta^(epsilon - epsilon40)`, then
`X * delta^(epsilon40 - 1) ≥ delta^(epsilon - 1)`.
This upgrades the Lemma 40 output exponent to the target exponent.
-/
lemma lemma40_exponent_upgrade
    {delta epsilon epsilon40 X : ℝ}
    (hdelta_pos : 0 < delta)
    (hX : X ≥ Real.rpow delta (epsilon - epsilon40)) :
    X * Real.rpow delta (epsilon40 - 1) ≥
      Real.rpow delta (epsilon - 1) := by
  have h_add :
      (epsilon - epsilon40) + (epsilon40 - 1) = epsilon - 1 := by
    ring
  have h1 :
      Real.rpow delta ((epsilon - epsilon40) + (epsilon40 - 1)) =
        Real.rpow delta (epsilon - epsilon40) *
          Real.rpow delta (epsilon40 - 1) :=
    Real.rpow_add hdelta_pos (epsilon - epsilon40) (epsilon40 - 1)
  have h1' :
      Real.rpow delta (epsilon - epsilon40) *
          Real.rpow delta (epsilon40 - 1) =
        Real.rpow delta (epsilon - 1) := by
    rw [← h1, h_add]
  have h2 :
      X * Real.rpow delta (epsilon40 - 1) ≥
        Real.rpow delta (epsilon - epsilon40) *
          Real.rpow delta (epsilon40 - 1) := by
    gcongr
    exact Real.rpow_nonneg hdelta_pos.le _
  rw [h1'] at h2
  exact h2

/--
ENNReal version: if the constant prefactor `X` dominates
`delta^(epsilon - epsilon40)`, then the Lemma 40 conclusion implies the
target lower bound.
-/
lemma lemma40_exponent_upgrade_ennreal
    {delta epsilon epsilon40 X : ℝ}
    (hdelta_pos : 0 < delta)
    (hX : X ≥ Real.rpow delta (epsilon - epsilon40)) :
    ENNReal.ofReal (X * Real.rpow delta (epsilon40 - 1)) ≥
      Kakeya.realRpowENN delta (epsilon - 1) := by
  have h_real := lemma40_exponent_upgrade hdelta_pos hX
  exact ENNReal.ofReal_mono h_real

/--
For any `C0 > 0` and `p < q`, there exists `delta₀ > 0` such that for all
`0 < delta ≤ delta₀`, `C0 * delta^p ≥ delta^q`.
-/
lemma exists_delta_const_mul_rpow_ge_rpow
    {C0 p q : ℝ}
    (hC0_pos : 0 < C0)
    (hpq : p < q) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        C0 * Real.rpow delta p ≥ Real.rpow delta q := by
  have h_inv_nonneg : 0 ≤ C0⁻¹ := by positivity
  rcases exists_delta_mul_rpow_le_rpow C0⁻¹ h_inv_nonneg hpq with
    ⟨delta₀, hdelta₀_pos, hdelta₀_one, hbound⟩
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta_pos hdelta_le
  have h : C0⁻¹ * Real.rpow delta q ≤ Real.rpow delta p :=
    hbound delta hdelta_pos hdelta_le
  have h' : Real.rpow delta q ≤ C0 * Real.rpow delta p := by
    calc
      Real.rpow delta q
          = C0 * (C0⁻¹ * Real.rpow delta q) := by
              field_simp [hC0_pos.ne']
      _ ≤ C0 * Real.rpow delta p := by gcongr
  exact h'

/--
Monotonicity of `WZ1UniformTripleDensity` in the density constant:
a smaller lower bound is easier to satisfy.
-/
lemma uniform_triple_density_mono
    {c1 c2 : ENNReal} {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (h : WZ1UniformTripleDensity c2 F G₁ G₂ H)
    (hle : c1 ≤ c2) :
    WZ1UniformTripleDensity c1 F G₁ G₂ H := by
  rcases h with ⟨hH_nonempty, h_density⟩
  refine ⟨hH_nonempty, ?_⟩
  rcases h_density with ⟨h_edges, h_fibers⟩
  refine ⟨h_edges, ?_⟩
  intro edge hedge I
  have h_old :
      c2 * wz1VertexCardProduct (wz1TripleVertexClasses F G₁ G₂)
          (Finset.univ \ I) ≤
        (wz1HypergraphFiber (wz1EncodeTriples H) I edge).card :=
    h_fibers edge hedge I
  have h_mul :
      c1 * wz1VertexCardProduct (wz1TripleVertexClasses F G₁ G₂)
          (Finset.univ \ I) ≤
        c2 * wz1VertexCardProduct (wz1TripleVertexClasses F G₁ G₂)
          (Finset.univ \ I) := by
    gcongr
  exact h_mul.trans h_old

/--
Monotonicity of `DiscreteSet.IsFrostman` in the constant `C`:
a larger constant gives a weaker bound.
-/
lemma DiscreteSet.IsFrostman.mono_const
    {n : ℕ} {A : DiscreteSet n} {δ s : ℝ} {C1 C2 : ENNReal}
    (h : A.IsFrostman δ s C1) (hle : C1 ≤ C2) :
    A.IsFrostman δ s C2 := by
  intro x r hδr hr1
  have h_old := h x r hδr hr1
  have h_mul :
      C1 * Kakeya.realRpowENN r s * A.enncard ≤
        C2 * Kakeya.realRpowENN r s * A.enncard := by
    gcongr
  exact h_old.trans h_mul

/--
For any `C ≥ 0` and `p > 0`, there exists `delta₀ > 0` such that
`C * delta^p < K` for all `0 < delta ≤ delta₀`, for any given `K > 0`.
-/
lemma exists_delta_const_mul_rpow_lt
    {C K p : ℝ} (hC : 0 ≤ C) (hK : 0 < K) (hp : 0 < p) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        C * Real.rpow delta p < K := by
  by_cases hC0 : C = 0
  · refine ⟨1, by norm_num, le_rfl, fun delta _ _ => ?_⟩
    rw [hC0, zero_mul]
    exact hK
  · have hC_pos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    let D : ℝ := 2 * C / K
    have hD_nonneg : 0 ≤ D := by positivity
    rcases exists_delta_mul_rpow_le_rpow
        D hD_nonneg (show (0 : ℝ) < p from hp) with
      ⟨delta₀, hdelta₀_pos, hdelta₀_one, hbound⟩
    refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
    intro delta hdelta_pos hdelta_le
    have h : D * Real.rpow delta p ≤ 1 := by
      simpa [Real.rpow_zero] using hbound delta hdelta_pos hdelta_le
    have h2 : C * Real.rpow delta p ≤ K / 2 := by
      have h3 : (2 * C / K) * Real.rpow delta p ≤ 1 := h
      calc
        C * Real.rpow delta p
            = K / 2 * ((2 * C / K) * Real.rpow delta p) := by
                field_simp [hK.ne']
        _ ≤ K / 2 * 1 := by gcongr
        _ = K / 2 := by ring
    linarith

/--
Bundle all exceptional-fraction small-delta conditions needed in
Proposition 41.
-/
lemma exists_delta_exceptional_bound
    (N : ℕ) (alpha : ℝ) (halpha : 0 < alpha) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        (3 : ℝ)^N * Real.rpow delta (2 * alpha) < 1 / 10 ∧
        2 * (3 : ℝ)^N * Real.rpow delta (2 * alpha) < 1 ∧
        4 * (3 : ℝ)^N * Real.rpow delta alpha ≤ 1 := by
  have h1 := exists_delta_const_mul_rpow_lt
    (show (0 : ℝ) ≤ (3 : ℝ)^N by positivity)
    (show (0 : ℝ) < 1 / 10 by norm_num)
    (show (0 : ℝ) < 2 * alpha by positivity)
  have h2 := exists_delta_const_mul_rpow_lt
    (show (0 : ℝ) ≤ 2 * (3 : ℝ)^N by positivity)
    (show (0 : ℝ) < 1 by norm_num)
    (show (0 : ℝ) < 2 * alpha by positivity)
  have h3 := exists_delta_mul_rpow_le_rpow
    (4 * (3 : ℝ)^N)
    (by positivity)
    (show (0 : ℝ) < alpha by positivity)
  rcases h1 with ⟨d1, hd1_pos, hd1_one, hb1⟩
  rcases h2 with ⟨d2, hd2_pos, hd2_one, hb2⟩
  rcases h3 with ⟨d3, hd3_pos, hd3_one, hb3⟩
  let delta₀ := min d1 (min d2 d3)
  have hdelta₀_pos : 0 < delta₀ :=
    lt_min hd1_pos (lt_min hd2_pos hd3_pos)
  have hdelta₀_one : delta₀ ≤ 1 :=
    le_trans (min_le_left _ _) hd1_one
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta_pos hdelta_le
  have h_le1 : delta ≤ d1 := le_trans hdelta_le (min_le_left _ _)
  have h_le2 : delta ≤ d2 :=
    le_trans (le_trans hdelta_le (min_le_right _ _)) (min_le_left _ _)
  have h_le3 : delta ≤ d3 :=
    le_trans (le_trans hdelta_le (min_le_right _ _)) (min_le_right _ _)
  have h4 := hb1 delta hdelta_pos h_le1
  have h5 := hb2 delta hdelta_pos h_le2
  have h6 : 4 * (3 : ℝ)^N * Real.rpow delta alpha ≤ 1 := by
    simpa [Real.rpow_zero] using hb3 delta hdelta_pos h_le3
  exact ⟨h4, h5, h6⟩

/--
Generic absorption algebra for WZ1 Proposition 41.
-/
lemma wz1_absorption_algebra
    {delta c0 K_final C_absorb E Dpow : ℝ}
    {N : ℕ} {alpha' epsilon M e_max A : ℝ}
    (hdelta_pos : 0 < delta)
    (hc0 : c0 = Real.rpow delta alpha')
    (hK_final_one : 1 ≤ K_final)
    (hK_final :
      K_final ≤
        40 * Dpow *
          Real.rpow delta (-(M ^ N : ℝ) * e_max - epsilon / 8))
    (hC_absorb :
      C_absorb =
        32 * (3 : ℝ)^(5 * N) / (A * 1600 * Dpow^2))
    (hE : E = 5 * alpha' + 2 * (M ^ N : ℝ) * e_max + epsilon / 4)
    (hA_one : 1 ≤ A)
    (hDpow_pos : 0 < Dpow)
    (halpha'_pos : 0 < alpha')
    (hepsilon_pos : 0 < epsilon) :
    (2 * (3 : ℝ)^N * c0)^5 / (A * K_final^2) ≥
      C_absorb * Real.rpow delta E := by
  set c_final := 2 * (3 : ℝ)^N * c0 with hc_final
  set exp1 := (-(M ^ N : ℝ) * e_max - epsilon / 8) with hexp1
  set exp2 := -2 * (M ^ N : ℝ) * e_max - epsilon / 4 with hexp2
  have hexp_eq : 2 * exp1 = exp2 := by
    simp [hexp1, hexp2] <;> ring
  have hcf5 :
      c_final^5 =
        (2 * (3 : ℝ)^N)^5 * Real.rpow delta (5 * alpha') := by
    simp only [hc_final, hc0]
    have h1 :
        (2 * (3 : ℝ)^N * Real.rpow delta alpha')^5 =
          (2 * (3 : ℝ)^N)^5 * (Real.rpow delta alpha')^5 := by
      rw [mul_pow]
    rw [h1]
    have h2 :
        (Real.rpow delta alpha')^5 =
          Real.rpow delta (5 * alpha') := by
      have h3 :
          Real.rpow delta (alpha' * 5) =
            (Real.rpow delta alpha')^(5 : ℝ) :=
        Real.rpow_mul (le_of_lt hdelta_pos) alpha' 5
      have h4 :
          (Real.rpow delta alpha')^(5 : ℝ) =
            (Real.rpow delta alpha')^5 := by
        norm_cast
      have h5 : alpha' * 5 = 5 * alpha' := by ring
      rw [h5] at h3
      exact (h3.trans h4).symm
    rw [h2] <;> ring
  have h_rpow2 :
      (Real.rpow delta exp1)^2 = Real.rpow delta exp2 := by
    have h1 :
        Real.rpow delta (exp1 * 2) =
          (Real.rpow delta exp1)^(2 : ℝ) :=
      Real.rpow_mul (le_of_lt hdelta_pos) exp1 2
    have h2 :
        (Real.rpow delta exp1)^(2 : ℝ) =
          (Real.rpow delta exp1)^2 := by
      norm_cast
    have h3 : exp1 * 2 = exp2 := by
      simp [hexp1, hexp2] <;> ring
    rw [h3] at h1
    exact (h1.trans h2).symm
  have hK2 :
      K_final^2 ≤
        (40 * Dpow)^2 * Real.rpow delta exp2 := by
    have hsq :
        K_final^2 ≤
          (40 * Dpow * Real.rpow delta exp1)^2 := by
      gcongr <;> exact hK_final
    have h_expand :
        (40 * Dpow * Real.rpow delta exp1)^2 =
          (40 * Dpow)^2 * (Real.rpow delta exp1)^2 := by
      rw [mul_pow]
    rw [h_expand, h_rpow2] at hsq
    exact hsq
  have h_denom :
      A * K_final^2 ≤
        A * ((40 * Dpow)^2 * Real.rpow delta exp2) := by
    have hA_pos : 0 < A := by linarith
    gcongr
  have h4 : 0 ≤ c_final^5 := by
    have h5 : 0 < c0 := by
      rw [hc0]
      exact Real.rpow_pos_of_pos hdelta_pos alpha'
    have h6 : 0 < c_final := by
      dsimp only [c_final]
      exact mul_pos (by positivity) h5
    exact (pow_pos h6 5).le
  have h5 : 0 < A * K_final^2 := by
    have hA_pos : 0 < A := by linarith
    have hK_pos2 : 0 < K_final := by linarith [hK_final_one]
    exact mul_pos hA_pos (pow_pos hK_pos2 2)
  have h_pos2 :
      0 < A * ((40 * Dpow)^2 * Real.rpow delta exp2) := by
    have hA_pos : 0 < A := by linarith
    have hD : 0 < (40 * Dpow)^2 := by positivity
    have hW : 0 < Real.rpow delta exp2 :=
      Real.rpow_pos_of_pos hdelta_pos _
    positivity
  have h6 :
      c_final^5 / (A * K_final^2) ≥
        c_final^5 /
          (A * ((40 * Dpow)^2 * Real.rpow delta exp2)) := by
    gcongr <;> linarith [h_denom]
  rw [hcf5] at h6
  have hZ_pos : 0 < A * (40 * Dpow)^2 := by
    have hA_pos : 0 < A := by linarith
    have hD : 0 < 40 * Dpow := by positivity
    positivity
  have hW_pos : 0 < Real.rpow delta exp2 :=
    Real.rpow_pos_of_pos hdelta_pos _
  have h7 :
      ((2 * (3 : ℝ)^N)^5 * Real.rpow delta (5 * alpha')) /
          (A * ((40 * Dpow)^2 * Real.rpow delta exp2)) =
        (((2 * (3 : ℝ)^N)^5) / (A * (40 * Dpow)^2)) *
          (Real.rpow delta (5 * alpha') /
            Real.rpow delta exp2) := by
    field_simp [hZ_pos.ne', hW_pos.ne'] <;> ring
  have h8 :
      Real.rpow delta (5 * alpha') / Real.rpow delta exp2 =
        Real.rpow delta
          (5 * alpha' + 2 * (M ^ N : ℝ) * e_max + epsilon / 4) := by
    have h9 :
        (5 * alpha') - exp2 =
          5 * alpha' + 2 * (M ^ N : ℝ) * e_max + epsilon / 4 := by
      simp [hexp2] <;> ring
    have h10 :
        Real.rpow delta ((5 * alpha') - exp2) =
          Real.rpow delta (5 * alpha') /
            Real.rpow delta exp2 := by
      have h_pos : 0 < Real.rpow delta exp2 :=
        Real.rpow_pos_of_pos hdelta_pos exp2
      have h11 :
          Real.rpow delta ((5 * alpha') - exp2) *
              Real.rpow delta exp2 =
            Real.rpow delta (5 * alpha') := by
        have h12 :=
          Real.rpow_add hdelta_pos ((5 * alpha') - exp2) exp2
        have h13 : ((5 * alpha') - exp2) + exp2 = 5 * alpha' := by
          ring
        rw [h13] at h12
        exact h12.symm
      calc
        Real.rpow delta ((5 * alpha') - exp2)
            =
              (Real.rpow delta ((5 * alpha') - exp2) *
                  Real.rpow delta exp2) /
                Real.rpow delta exp2 := by
              field_simp [h_pos.ne'] <;> ring
        _ = Real.rpow delta (5 * alpha') /
              Real.rpow delta exp2 := by
            rw [h11]
    rw [h9] at h10
    exact h10.symm
  rw [h7, h8] at h6
  have hC :
      C_absorb =
        ((2 * (3 : ℝ)^N)^5 / (A * (40 * Dpow)^2)) := by
    rw [hC_absorb] <;> ring
  rw [hC, hE]
  rw [hcf5]
  exact h6

end Kakeya.Assouad
