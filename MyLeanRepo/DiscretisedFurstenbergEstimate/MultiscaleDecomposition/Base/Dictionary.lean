module

/-
Copyright (c) 2024 The Discretised Furstenberg Estimate Team.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raven Team
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.GridHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.DyadicUniform

@[expose] public section

noncomputable section

namespace DirecretisedFurstenbergEstimate

namespace MultiscaleDecomposition

/-! # Dictionary lemma helpers

This module contains the dictionary constant and supporting lemmas:
- `dictionaryConstant`: the constant used in the dictionary lemma
- `codeFunction_value`: code function evaluation at integers
- `ball_intersects_9_squares`: ball intersects at most 9 side-L squares when r ≤ L
- `N_i_le_9`: bound N(i) ≤ 9 when Δ ≥ √2/6
- `codeFunction_product`: ∏ N(i) = Δ^{-f(j)}
- `superlinear_lower_bound`: superlinearity lower bound
- `N_i_le_ceiling`: bound N(i) by grid ball count
- `slope_le_4`: code function slope ≤ 4
-/

-- ======================================================================
-- Dictionary lemma (OS Lemma 1169)
-- ======================================================================

/-- Dictionary constant: includes `Δ^{-2}` to absorb the scale-rounding factor
`Δ^{-s}` (since `s ≤ 2`), times `36^m` for the covering-number conversion factors.
The factor 9 comes from upper bound (ball intersects 9 squares),
and 4 from lower bound (ball intersects at most 4 coarser squares). -/
def dictionaryConstant (m : ℕ) (Δ : ℝ) : ℝ := Δ^(-4 : ℝ) * (324 : ℝ) ^ m

/-- Helper: code function value at integer j. -/
lemma codeFunction_value {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    {j : ℕ} (hj : j ≤ m) :
    codeFunction m Δ N (j : ℝ) = codeFunctionPartialSum m Δ N j := by
  by_cases h0 : j = 0
  · rw [h0]
    simp [codeFunction, codeFunctionPartialSum]
    <;> norm_num
  · have h_j_pos : 0 < j := Nat.pos_of_ne_zero h0
    by_cases h_eq : j = m
    · rw [h_eq]
      by_cases hm : m = 0
      · rw [hm]
        simp [codeFunction, codeFunctionPartialSum]
      · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h1 : (m : ℝ) > 0 := by exact_mod_cast hm_pos
        have h2 : ¬(m : ℝ) ≤ 0 := by linarith
        have h3 : (m : ℝ) ≥ (m : ℝ) := by linarith
        simp [codeFunction, h2, h3]
        <;> norm_cast
    · have h_j_lt_m : j < m := by omega
      have h1 : 0 < (j : ℝ) := by exact_mod_cast h_j_pos
      have h2 : (j : ℝ) < (m : ℝ) := by exact_mod_cast h_j_lt_m
      have h_not_le0 : ¬ (j : ℝ) ≤ 0 := by linarith
      have h_not_geM : ¬ (j : ℝ) ≥ (m : ℝ) := by linarith
      have h_floor : ⌊(j : ℝ)⌋₊ = j := by simp
      have h_main : codeFunction m Δ N (j : ℝ) = codeFunctionPartialSum m Δ N j := by
        rw [codeFunction]
        rw [if_neg h_not_le0, if_neg h_not_geM]
        have h_eq : (let j' : ℕ := ⌊(j : ℝ)⌋₊
          let t : ℝ := (j : ℝ) - ↑j'
          codeFunctionPartialSum m Δ N j' +
            t * (codeFunctionPartialSum m Δ N (j' + 1) - codeFunctionPartialSum m Δ N j')) =
            codeFunctionPartialSum m Δ N j := by
          rw [h_floor]
          <;> simp <;> ring
        exact h_eq
      exact h_main

/-- A ball of radius r ≤ L intersects at most 9 dyadic squares of side L. -/
lemma ball_intersects_9_squares (L r : ℝ) (hL : 0 < L) (hr : 0 < r) (hle : r ≤ L)
    (x : EuclideanPlane) :
    ∃ (S : Finset (ℤ × ℤ)),
      (∀ (a b : ℤ), (Metric.closedBall x r ∩ dyadicSquare L a b).Nonempty → (a, b) ∈ S) ∧
      S.card ≤ 9 := by
  let k0 : ℤ := ⌊x 0 / L⌋
  let l0 : ℤ := ⌊x 1 / L⌋
  let S : Finset (ℤ × ℤ) :=
    (Finset.Icc (k0 - 1) (k0 + 1)) ×ˢ (Finset.Icc (l0 - 1) (l0 + 1))
  have h_card : S.card ≤ 9 := by
    have h1 : (Finset.Icc (k0 - 1) (k0 + 1)).card = 3 := by
      simp [Finset.card_eq_zero] <;> omega
    have h2 : (Finset.Icc (l0 - 1) (l0 + 1)).card = 3 := by
      simp [Finset.card_eq_zero] <;> omega
    have h3 : S.card = (Finset.Icc (k0 - 1) (k0 + 1)).card * (Finset.Icc (l0 - 1) (l0 + 1)).card := by
      rw [Finset.card_product]
    rw [h3, h1, h2] <;> norm_num
  have h_main : ∀ (a b : ℤ), (Metric.closedBall x r ∩ dyadicSquare L a b).Nonempty → (a, b) ∈ S := by
    intro a b h
    rcases h with ⟨y, hyball, hysq⟩
    have hdy : ‖y - x‖ ≤ r := by simpa [dist_eq_norm] using hyball
    have hsq : ‖y - x‖ ^ 2 = (y 0 - x 0)^2 + (y 1 - x 1)^2 := by
      have h : ‖y - x‖ ^ 2 = ∑ i : Fin 2, ((y - x) i)^2 := EuclideanSpace.real_norm_sq_eq (y - x)
      rw [h] <;> simp [Fin.sum_univ_two] <;> ring
    have h_norm_nonneg : 0 ≤ ‖y - x‖ := by positivity
    have h_norm_sq_le : ‖y - x‖ ^ 2 ≤ r ^ 2 := by
      have h5 : ‖y - x‖ ≤ r := hdy
      nlinarith
    have hpos1 : 0 ≤ (y 1 - x 1)^2 := by positivity
    have hpos2 : 0 ≤ (y 0 - x 0)^2 := by positivity
    have h1 : (y 0 - x 0)^2 ≤ ‖y - x‖ ^ 2 := by
      rw [hsq]; linarith [hpos1]
    have h2 : (y 1 - x 1)^2 ≤ ‖y - x‖ ^ 2 := by
      rw [hsq]; linarith [hpos2]
    have hdx0 : |y 0 - x 0| ≤ r := by
      have h3 : (y 0 - x 0)^2 ≤ r^2 := by linarith
      have h4 : |y 0 - x 0| ^ 2 ≤ r^2 := by simpa [sq_abs] using h3
      have h5 : |y 0 - x 0| ≤ r := by
        by_contra h6
        have h7 : r < |y 0 - x 0| := by linarith
        have h8 : r ^ 2 < |y 0 - x 0| ^ 2 := by nlinarith [abs_nonneg (y 0 - x 0)]
        linarith
      exact h5
    have hdy1 : |y 1 - x 1| ≤ r := by
      have h3 : (y 1 - x 1)^2 ≤ r^2 := by linarith
      have h4 : |y 1 - x 1| ^ 2 ≤ r^2 := by simpa [sq_abs] using h3
      have h5 : |y 1 - x 1| ≤ r := by
        by_contra h6
        have h7 : r < |y 1 - x 1| := by linarith
        have h8 : r ^ 2 < |y 1 - x 1| ^ 2 := by nlinarith [abs_nonneg (y 1 - x 1)]
        linarith
      exact h5
    have hya1 : (a : ℝ) * L ≤ y 0 := hysq.1.1
    have hya2 : y 0 < ((a : ℝ) + 1) * L := hysq.1.2
    have hyb1 : (b : ℝ) * L ≤ y 1 := hysq.2.1
    have hyb2 : y 1 < ((b : ℝ) + 1) * L := hysq.2.2
    have hk01 : (k0 : ℝ) ≤ x 0 / L := Int.floor_le (x 0 / L)
    have hk02 : x 0 / L < (k0 : ℝ) + 1 := Int.lt_floor_add_one (x 0 / L)
    have h_a_le : a ≤ k0 + 1 := by
      have h1 : (a : ℝ) * L ≤ y 0 := hya1
      have h2 : y 0 ≤ x 0 + r := by linarith [abs_le.mp hdx0]
      have h3 : (a : ℝ) * L ≤ x 0 + L := by linarith
      have h4 : (a : ℝ) - 1 ≤ x 0 / L := by
        have h5 : ((a : ℝ) - 1) * L ≤ x 0 := by linarith
        have h6 : ((a : ℝ) - 1) * L / L ≤ x 0 / L := by gcongr
        have h7 : ((a : ℝ) - 1) * L / L = (a : ℝ) - 1 := by field_simp [hL.ne'] <;> ring
        rw [h7] at h6; exact h6
      have h8 : (a : ℝ) - 1 < (k0 : ℝ) + 1 := by linarith [hk02]
      have h9 : (a : ℝ) < (k0 : ℝ) + 2 := by linarith
      have h10 : a < k0 + 2 := by exact_mod_cast h9
      have h11 : a ≤ k0 + 1 := by omega
      exact h11
    have h_a_ge : k0 - 1 ≤ a := by
      have h1 : y 0 < ((a : ℝ) + 1) * L := hya2
      have h2 : x 0 - r ≤ y 0 := by linarith [abs_le.mp hdx0]
      have h3 : x 0 - L < ((a : ℝ) + 1) * L := by linarith
      have h4 : x 0 / L - 1 < (a : ℝ) + 1 := by
        have h5 : (x 0 - L) / L < ((a : ℝ) + 1) := by
          have h6 : (x 0 - L) / L < (((a : ℝ) + 1) * L) / L := by gcongr
          have h7 : (((a : ℝ) + 1) * L) / L = (a : ℝ) + 1 := by field_simp [hL.ne'] <;> ring
          rw [h7] at h6; exact h6
        have h8 : (x 0 - L) / L = x 0 / L - 1 := by field_simp [hL.ne'] <;> ring
        rw [h8] at h5; exact h5
      have h9 : (k0 : ℝ) - 1 < (a : ℝ) + 1 := by linarith [hk01, h4]
      have h10 : (k0 : ℝ) - 2 < (a : ℝ) := by linarith
      have h11 : k0 - 2 < a := by exact_mod_cast h10
      have h12 : k0 - 1 ≤ a := by omega
      exact h12
    have hl01 : (l0 : ℝ) ≤ x 1 / L := Int.floor_le (x 1 / L)
    have hl02 : x 1 / L < (l0 : ℝ) + 1 := Int.lt_floor_add_one (x 1 / L)
    have h_b_le : b ≤ l0 + 1 := by
      have h1 : (b : ℝ) * L ≤ y 1 := hyb1
      have h2 : y 1 ≤ x 1 + r := by linarith [abs_le.mp hdy1]
      have h3 : (b : ℝ) * L ≤ x 1 + L := by linarith
      have h4 : (b : ℝ) - 1 ≤ x 1 / L := by
        have h5 : ((b : ℝ) - 1) * L ≤ x 1 := by linarith
        have h6 : ((b : ℝ) - 1) * L / L ≤ x 1 / L := by gcongr
        have h7 : ((b : ℝ) - 1) * L / L = (b : ℝ) - 1 := by field_simp [hL.ne'] <;> ring
        rw [h7] at h6; exact h6
      have h8 : (b : ℝ) - 1 < (l0 : ℝ) + 1 := by linarith [hl02]
      have h9 : (b : ℝ) < (l0 : ℝ) + 2 := by linarith
      have h10 : b < l0 + 2 := by exact_mod_cast h9
      have h11 : b ≤ l0 + 1 := by omega
      exact h11
    have h_b_ge : l0 - 1 ≤ b := by
      have h1 : y 1 < ((b : ℝ) + 1) * L := hyb2
      have h2 : x 1 - r ≤ y 1 := by linarith [abs_le.mp hdy1]
      have h3 : x 1 - L < ((b : ℝ) + 1) * L := by linarith
      have h4 : x 1 / L - 1 < (b : ℝ) + 1 := by
        have h5 : (x 1 - L) / L < ((b : ℝ) + 1) := by
          have h6 : (x 1 - L) / L < (((b : ℝ) + 1) * L) / L := by gcongr
          have h7 : (((b : ℝ) + 1) * L) / L = (b : ℝ) + 1 := by field_simp [hL.ne'] <;> ring
          rw [h7] at h6; exact h6
        have h8 : (x 1 - L) / L = x 1 / L - 1 := by field_simp [hL.ne'] <;> ring
        rw [h8] at h5; exact h5
      have h9 : (l0 : ℝ) - 1 < (b : ℝ) + 1 := by linarith [hl01, h4]
      have h10 : (l0 : ℝ) - 2 < (b : ℝ) := by linarith
      have h11 : l0 - 2 < b := by exact_mod_cast h10
      have h12 : l0 - 1 ≤ b := by omega
      exact h12
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨h_a_ge, h_a_le⟩,
      Finset.mem_Icc.mpr ⟨h_b_ge, h_b_le⟩⟩
  exact ⟨S, h_main, h_card⟩

/-- Bound N(i) ≤ 9 when Δ ≥ √2/6. -/
lemma N_i_le_9 {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsUniform P m Δ N) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (h : Δ ≥ Real.sqrt 2 / 6) {i : ℕ} (hi : i < m) : N i ≤ 9 := by
  have hP_ne : P.Nonempty := h_uniform.2.2.1
  rcases hP_ne with ⟨x, hx⟩
  let a : ℤ := ⌊x 0 / (Δ ^ i)⌋
  let b : ℤ := ⌊x 1 / (Δ ^ i)⌋
  have h_x_in_square : x ∈ dyadicSquare (Δ ^ i) a b := by
    have hΔi_pos : 0 < Δ ^ i := by positivity
    simp only [dyadicSquare]
    have h1a : (a : ℝ) ≤ x 0 / (Δ ^ i) := Int.floor_le (x 0 / (Δ ^ i))
    have h2a : x 0 / (Δ ^ i) < (a : ℝ) + 1 := Int.lt_floor_add_one (x 0 / (Δ ^ i))
    have h1b : (b : ℝ) ≤ x 1 / (Δ ^ i) := Int.floor_le (x 1 / (Δ ^ i))
    have h2b : x 1 / (Δ ^ i) < (b : ℝ) + 1 := Int.lt_floor_add_one (x 1 / (Δ ^ i))
    have ha1 : (a : ℝ) * (Δ ^ i) ≤ x 0 := by
      have h : (Δ ^ i) * (a : ℝ) ≤ (Δ ^ i) * (x 0 / (Δ ^ i)) := by gcongr
      have h' : (Δ ^ i) * (x 0 / (Δ ^ i)) = x 0 := by field_simp [hΔi_pos.ne'] <;> ring
      have h'' : (a : ℝ) * (Δ ^ i) = (Δ ^ i) * (a : ℝ) := by ring
      rw [h'']; linarith
    have ha2 : x 0 < ((a : ℝ) + 1) * (Δ ^ i) := by
      have h : x 0 = (Δ ^ i) * (x 0 / (Δ ^ i)) := by field_simp [hΔi_pos.ne'] <;> ring
      have h' : (Δ ^ i) * (x 0 / (Δ ^ i)) < (Δ ^ i) * ((a : ℝ) + 1) := by gcongr
      have h'' : ((a : ℝ) + 1) * (Δ ^ i) = (Δ ^ i) * ((a : ℝ) + 1) := by ring
      rw [h'']; linarith
    have hb1 : (b : ℝ) * (Δ ^ i) ≤ x 1 := by
      have h : (Δ ^ i) * (b : ℝ) ≤ (Δ ^ i) * (x 1 / (Δ ^ i)) := by gcongr
      have h' : (Δ ^ i) * (x 1 / (Δ ^ i)) = x 1 := by field_simp [hΔi_pos.ne'] <;> ring
      have h'' : (b : ℝ) * (Δ ^ i) = (Δ ^ i) * (b : ℝ) := by ring
      rw [h'']; linarith
    have hb2 : x 1 < ((b : ℝ) + 1) * (Δ ^ i) := by
      have h : x 1 = (Δ ^ i) * (x 1 / (Δ ^ i)) := by field_simp [hΔi_pos.ne'] <;> ring
      have h' : (Δ ^ i) * (x 1 / (Δ ^ i)) < (Δ ^ i) * ((b : ℝ) + 1) := by gcongr
      have h'' : ((b : ℝ) + 1) * (Δ ^ i) = (Δ ^ i) * ((b : ℝ) + 1) := by ring
      rw [h'']; linarith
    exact ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩
  have hne : (P ∩ dyadicSquare (Δ ^ i) a b).Nonempty := ⟨x, hx, h_x_in_square⟩
  have h_cov : (Metric.externalCoveringNumber (Δ ^ (i + 1)).toNNReal
      (P ∩ dyadicSquare (Δ ^ i) a b) : ENNReal) = (↑(N i) : ENNReal) :=
    h_uniform.2.2.2.2 i hi a b hne
  have hΔi_pos : 0 < Δ ^ i := by positivity
  have hΔi1_pos : 0 < Δ ^ (i + 1) := by positivity
  have hpos : 0 < Δ ^ i := by positivity
  have h_r : Δ ^ (i + 1) ≥ (Δ ^ i) * Real.sqrt 2 / 6 := by
    have h1 : Δ ^ (i + 1) = Δ * (Δ ^ i) := by ring
    rw [h1]
    have h2 : Δ ≥ Real.sqrt 2 / 6 := h
    have h3 : Δ * (Δ ^ i) ≥ (Real.sqrt 2 / 6) * (Δ ^ i) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    linarith
  rcases nine_balls_cover_square (Δ ^ i) (Δ ^ (i + 1)) hΔi_pos hΔi1_pos h_r a b with ⟨c, hcover, hcard⟩
  let ε' : NNReal := (Δ ^ (i + 1)).toNNReal
  have hε'_eq : (ε' : ℝ) = Δ ^ (i + 1) := by
    simp [ε', show 0 ≤ Δ ^ (i + 1) by positivity] <;> linarith
  have hcover' : dyadicSquare (Δ ^ i) a b ⊆ ⋃ x ∈ c, Metric.closedBall x ε' := by
    have h_eq : ∀ (x : EuclideanPlane), Metric.closedBall x (Δ ^ (i + 1)) = Metric.closedBall x ε' := by
      intro x; congr; exact hε'_eq.symm
    simpa [h_eq] using hcover
  have h10 : Metric.IsCover ε' (dyadicSquare (Δ ^ i) a b) (c : Set EuclideanPlane) := by
    rw [Metric.isCover_iff_subset_iUnion_closedBall]; exact hcover'
  have h11_enat : Metric.externalCoveringNumber ε' (dyadicSquare (Δ ^ i) a b) ≤
      (c : Set EuclideanPlane).encard := Metric.IsCover.externalCoveringNumber_le_encard h10
  have h11 : (Metric.externalCoveringNumber ε' (dyadicSquare (Δ ^ i) a b) : ENNReal) ≤
      ((c : Set EuclideanPlane).encard : ENNReal) := by exact_mod_cast h11_enat
  have h12 : ((c : Set EuclideanPlane).encard : ENNReal) ≤ (9 : ENNReal) := by
    have h13 : (c : Set EuclideanPlane).encard = ↑(c.card) := by simp
    rw [h13]
    have h14 : (c.card : ENNReal) ≤ (9 : ENNReal) := by exact_mod_cast hcard
    exact h14
  have h9 : (Metric.externalCoveringNumber ε' (dyadicSquare (Δ ^ i) a b) : ENNReal) ≤ (9 : ENNReal) :=
    le_trans h11 h12
  have h10_enat : Metric.externalCoveringNumber ε' (P ∩ dyadicSquare (Δ ^ i) a b) ≤
      Metric.externalCoveringNumber ε' (dyadicSquare (Δ ^ i) a b) :=
    Metric.externalCoveringNumber_mono_set Set.inter_subset_right
  have h10' : (Metric.externalCoveringNumber ε' (P ∩ dyadicSquare (Δ ^ i) a b) : ENNReal) ≤
      (Metric.externalCoveringNumber ε' (dyadicSquare (Δ ^ i) a b) : ENNReal) := by
    exact_mod_cast h10_enat
  have h11' : (Metric.externalCoveringNumber ε' (P ∩ dyadicSquare (Δ ^ i) a b) : ENNReal) ≤ (9 : ENNReal) :=
    le_trans h10' h9
  have h12 : (↑(N i) : ENNReal) ≤ (9 : ENNReal) := by
    have h_eq : (Metric.externalCoveringNumber ε' (P ∩ dyadicSquare (Δ ^ i) a b) : ENNReal) = (↑(N i) : ENNReal) := h_cov
    rw [←h_eq]
    exact h11'
  exact_mod_cast h12

/-- Product of N(i) relates to code function: ∏_{i<j} N(i) = Δ^{-f(j)}. -/
lemma codeFunction_product {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsUniform P m Δ N) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) {j : ℕ} (hjm : j ≤ m) :
    (∏ i ∈ Finset.range j, (N i : ℝ)) = Real.rpow Δ (-(codeFunction m Δ N (j : ℝ))) := by
  have h_code_eq : codeFunction m Δ N (j : ℝ) = codeFunctionPartialSum m Δ N j :=
    codeFunction_value hjm
  rw [h_code_eq]
  have hlog_pos : 0 < Real.log (1 / Δ) := by
    have h2 : 1 < 1 / Δ := by apply one_lt_one_div <;> linarith
    exact Real.log_pos h2
  have h_base_pos : 0 < (1 / Δ) := by positivity
  have h_base_ne_one : (1 / Δ) ≠ 1 := by
    have h2 : 1 < 1 / Δ := by apply one_lt_one_div <;> linarith
    linarith
  have hN_pos : ∀ i ∈ Finset.range j, 0 < (N i : ℝ) := by
    intro i hi
    have h_i_lt_j : i < j := Finset.mem_range.mp hi
    have h_i_lt_m : i < m := by linarith
    have h3 : N i ≥ 1 := h_uniform.2.2.2.1 i h_i_lt_m
    exact_mod_cast h3
  have h_main : Real.rpow (1 / Δ) (codeFunctionPartialSum m Δ N j) =
      ∏ i ∈ Finset.range j, (N i : ℝ) := by
    simp only [codeFunctionPartialSum]
    have h6 : Real.rpow (1 / Δ) (∑ i ∈ Finset.range j, Real.log (N i) / Real.log (1 / Δ)) =
        ∏ i ∈ Finset.range j, Real.rpow (1 / Δ) (Real.log (N i) / Real.log (1 / Δ)) := by
      exact Real.rpow_sum_of_pos h_base_pos (fun i => Real.log (N i) / Real.log (1 / Δ)) (Finset.range j)
    rw [h6]
    apply Finset.prod_congr rfl
    intro i hi
    have hNi_pos : 0 < (N i : ℝ) := hN_pos i hi
    have h7 : Real.rpow (1 / Δ) (Real.log (N i) / Real.log (1 / Δ)) = (N i : ℝ) := by
      have h8 : Real.log (N i) / Real.log (1 / Δ) = Real.logb (1 / Δ) (N i : ℝ) := by
        simp [Real.logb] <;> ring
      rw [h8]
      exact Real.rpow_logb h_base_pos h_base_ne_one hNi_pos
    exact h7
  have h4 : Real.rpow Δ (-(codeFunctionPartialSum m Δ N j)) =
      Real.rpow (1 / Δ) (codeFunctionPartialSum m Δ N j) := by
    let y := codeFunctionPartialSum m Δ N j
    have h_pos1 : 0 < Δ := hΔ
    have h_pos2 : 0 < (1 / Δ) := by positivity
    have h_log : Real.log (1 / Δ) = -Real.log Δ := by
      rw [Real.log_div (by positivity) (by positivity)] <;> simp
    have h_eq1 : Real.rpow Δ (-y) = Real.exp (Real.log Δ * (-y)) :=
      Real.rpow_def_of_pos hΔ (-y)
    have h_eq2 : Real.rpow (1 / Δ) y = Real.exp (Real.log (1 / Δ) * y) :=
      Real.rpow_def_of_pos h_pos2 y
    rw [h_eq1, h_eq2, h_log] <;> ring_nf
  rw [h4, h_main]

/-- Superlinearity gives f(x) ≥ s*x - ε*m when f(0)=0. -/
lemma superlinear_lower_bound {f : ℝ → ℝ} {m ε s : ℝ}
    (h_super : EpsSuperlinear f 0 m ε) (hs : slope f 0 m = s)
    (hf0 : f 0 = 0)
    {x : ℝ} (hx : x ∈ Set.Icc 0 m) :
    f x ≥ s * x - ε * m := by
  rcases h_super with ⟨_, h_super'⟩
  have h1 : f x ≥ linearInterpolant f 0 m x - ε * (m - 0) := h_super' x hx
  have h1' : f x ≥ linearInterpolant f 0 m x - ε * m := by
    have h_eq : ε * (m - 0) = ε * m := by ring
    rw [h_eq] at h1
    exact h1
  have h2 : linearInterpolant f 0 m x = f 0 + slope f 0 m * x := by
    simp [linearInterpolant]
  have h3 : f x ≥ f 0 + slope f 0 m * x - ε * m := by
    rw [h2] at h1'
    exact h1'
  have h4 : f 0 = 0 := hf0
  have h5 : slope f 0 m = s := hs
  rw [h4, h5] at h3
  have h6 : f x ≥ s * x - ε * m := by simpa using h3
  exact h6

/-- Bound N(i) by the number of grid balls covering a dyadic square. -/
lemma N_i_le_ceiling {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsUniform P m Δ N) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    {i : ℕ} (hi : i < m) :
    N i ≤ Nat.ceil (Real.sqrt 2 / (2 * Δ)) ^ 2 := by
  have hP_ne : P.Nonempty := h_uniform.2.2.1
  rcases hP_ne with ⟨x, hx⟩
  let a : ℤ := ⌊x 0 / (Δ ^ i)⌋
  let b : ℤ := ⌊x 1 / (Δ ^ i)⌋
  have hΔi_pos : 0 < Δ ^ i := by positivity
  have h_x_in_square : x ∈ dyadicSquare (Δ ^ i) a b := by
    simp only [dyadicSquare]
    have h1a : (a : ℝ) ≤ x 0 / (Δ ^ i) := Int.floor_le (x 0 / (Δ ^ i))
    have h2a : x 0 / (Δ ^ i) < (a : ℝ) + 1 := Int.lt_floor_add_one (x 0 / (Δ ^ i))
    have h1b : (b : ℝ) ≤ x 1 / (Δ ^ i) := Int.floor_le (x 1 / (Δ ^ i))
    have h2b : x 1 / (Δ ^ i) < (b : ℝ) + 1 := Int.lt_floor_add_one (x 1 / (Δ ^ i))
    constructor
    · constructor
      · calc (a : ℝ) * (Δ ^ i) ≤ (x 0 / (Δ ^ i)) * (Δ ^ i) := by gcongr
        _ = x 0 := by field_simp [hΔi_pos.ne'] <;> ring
      · calc x 0 = (x 0 / (Δ ^ i)) * (Δ ^ i) := by field_simp [hΔi_pos.ne'] <;> ring
        _ < ((a : ℝ) + 1) * (Δ ^ i) := by gcongr
    · constructor
      · calc (b : ℝ) * (Δ ^ i) ≤ (x 1 / (Δ ^ i)) * (Δ ^ i) := by gcongr
        _ = x 1 := by field_simp [hΔi_pos.ne'] <;> ring
      · calc x 1 = (x 1 / (Δ ^ i)) * (Δ ^ i) := by field_simp [hΔi_pos.ne'] <;> ring
        _ < ((b : ℝ) + 1) * (Δ ^ i) := by gcongr
  have hQ_nonempty : (P ∩ dyadicSquare (Δ ^ i) a b).Nonempty := ⟨x, hx, h_x_in_square⟩
  have h_cov : (Metric.externalCoveringNumber (Δ ^ (i + 1)).toNNReal
      (P ∩ dyadicSquare (Δ ^ i) a b) : ENNReal) = (↑(N i) : ENNReal) :=
    h_uniform.2.2.2.2 i hi a b hQ_nonempty
  have hΔi1_pos : 0 < Δ ^ (i + 1) := by positivity
  let k : ℕ := Nat.ceil (Real.sqrt 2 / (2 * Δ))
  have hk : (k : ℝ) ≥ (Δ ^ i) * Real.sqrt 2 / (2 * (Δ ^ (i + 1))) := by
    have h1 : (k : ℝ) ≥ Real.sqrt 2 / (2 * Δ) := Nat.le_ceil _
    have h2 : (Δ ^ i) * Real.sqrt 2 / (2 * (Δ ^ (i + 1))) = Real.sqrt 2 / (2 * Δ) := by
      field_simp [hΔi_pos.ne'] <;> ring
    rw [h2]; exact h1
  rcases grid_cover_square (Δ ^ i) (Δ ^ (i + 1)) hΔi_pos hΔi1_pos k hk a b with ⟨c, hcover, hcard⟩
  let ε' : NNReal := (Δ ^ (i + 1)).toNNReal
  have hε'_eq : (ε' : ℝ) = Δ ^ (i + 1) := by
    simp [ε', show 0 ≤ Δ ^ (i + 1) by positivity] <;> linarith
  have hcover' : Metric.IsCover ε' (dyadicSquare (Δ ^ i) a b) (c : Set EuclideanPlane) := by
    rw [Metric.isCover_iff_subset_iUnion_closedBall]
    have h_eq : ∀ (z : EuclideanPlane), Metric.closedBall z (Δ ^ (i + 1)) = Metric.closedBall z ε' := by
      intro z; congr; exact hε'_eq.symm
    simpa [h_eq] using hcover
  have h11 : (Metric.externalCoveringNumber ε' (P ∩ dyadicSquare (Δ ^ i) a b) : ENNReal) ≤
      (↑(k ^ 2) : ENNReal) := by
    have h12 : (Metric.externalCoveringNumber ε' (P ∩ dyadicSquare (Δ ^ i) a b) : ENNReal) ≤
        (Metric.externalCoveringNumber ε' (dyadicSquare (Δ ^ i) a b) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set Set.inter_subset_right
    have h13 : (Metric.externalCoveringNumber ε' (dyadicSquare (Δ ^ i) a b) : ENNReal) ≤
        ((c : Set EuclideanPlane).encard : ENNReal) := by
      exact_mod_cast Metric.IsCover.externalCoveringNumber_le_encard hcover'
    have h14 : ((c : Set EuclideanPlane).encard : ENNReal) ≤ (↑(c.card) : ENNReal) := by simp
    have h15 : (c.card : ENNReal) ≤ (↑(k ^ 2) : ENNReal) := by exact_mod_cast hcard
    exact le_trans (le_trans h12 h13) (le_trans h14 h15)
  rw [h_cov] at h11
  exact_mod_cast h11

/-- The slope s of the code function satisfies s ≤ 4. -/
lemma slope_le_4 {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsUniform P m Δ N) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    slope (codeFunction m Δ N) 0 (m : ℝ) ≤ 4 := by
  by_cases hm : m = 0
  · subst hm
    simp [slope] <;> norm_num
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
  let f := codeFunction m Δ N
  have hlog_pos : 0 < Real.log (1 / Δ) := by
    have h2 : 1 < 1 / Δ := by apply one_lt_one_div <;> linarith
    exact Real.log_pos h2
  have hN_pos : ∀ i < m, 0 < (N i : ℝ) := by
    intro i hi
    have h3 : N i ≥ 1 := h_uniform.2.2.2.1 i hi
    exact_mod_cast (by linarith)
  set x : ℝ := Real.sqrt 2 / (2 * Δ) with hx_def
  have hx_pos : 0 < x := by positivity
  have h_ceil4 : (Nat.ceil x : ℝ) ^ 2 ≤ (1 / Δ) ^ 4 := by
    by_cases h1 : Δ ≤ 1 / 2
    · -- Case Δ ≤ 1/2
      have h2 : (Nat.ceil x : ℝ) ≤ x + 1 := by
        have h3 : (Nat.ceil x : ℝ) ≤ (Nat.floor x : ℝ) + 1 := by exact_mod_cast Nat.ceil_le_floor_add_one x
        have h4 : (Nat.floor x : ℝ) ≤ x := Nat.floor_le (by linarith)
        linarith
      have h4 : x + 1 ≤ 2 / Δ := by
        have h5 : Real.sqrt 2 / 2 + Δ ≤ 2 := by
          have h6 : Real.sqrt 2 / 2 < 1 := by
            have h7 : Real.sqrt 2 < 2 := by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
            linarith
          have h8 : Δ < 1 := hΔ1
          linarith
        simp only [hx_def]
        field_simp [hΔ.ne'] <;> linarith
      have h7 : (Nat.ceil x : ℝ) ≤ 2 / Δ := by linarith
      have h8 : (Nat.ceil x : ℝ) ^ 2 ≤ (2 / Δ) ^ 2 := by gcongr
      have h9 : (2 / Δ) ^ 2 ≤ (1 / Δ) ^ 4 := by
        have h10 : 4 * Δ ^ 2 ≤ 1 := by nlinarith
        have h11 : 0 < Δ := hΔ
        have h12 : (2 / Δ) ^ 2 = 4 / Δ ^ 2 := by field_simp <;> ring
        have h13 : (1 / Δ) ^ 4 = 1 / Δ ^ 4 := by field_simp <;> ring
        rw [h12, h13]
        have h14 : 4 / Δ ^ 2 ≤ 1 / Δ ^ 4 := by
          have h15 : 0 < Δ ^ 4 := by positivity
          have h16 : 4 / Δ ^ 2 - 1 / Δ ^ 4 ≤ 0 := by
            have h17 : 4 / Δ ^ 2 - 1 / Δ ^ 4 = (4 * Δ ^ 2 - 1) / Δ ^ 4 := by
              field_simp <;> ring
            rw [h17]
            apply div_nonpos_of_nonpos_of_nonneg
            · linarith
            · positivity
          linarith
        exact h14
      exact le_trans h8 h9
    · -- Case Δ > 1/2
      have h2 : 1 / 2 < Δ := by linarith
      by_cases h3 : Δ ≤ 1 / Real.sqrt 2
      · -- Subcase 1/2 < Δ ≤ 1/√2
        have h4 : x ≤ 2 := by
          simp only [hx_def]
          have h5 : Real.sqrt 2 / (2 * Δ) ≤ 2 := by
            have h6 : 0 < Δ := hΔ
            have h7 : Real.sqrt 2 ≤ 4 * Δ := by
              have h8 : 1 / 2 < Δ := h2
              have h9 : Real.sqrt 2 < 2 := by
                nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
              have h10 : 2 ≤ 4 * Δ := by linarith
              linarith
            calc Real.sqrt 2 / (2 * Δ) ≤ (4 * Δ) / (2 * Δ) := by gcongr
              _ = 2 := by field_simp [h6.ne'] <;> ring
          exact h5
        have h5 : (Nat.ceil x : ℝ) ≤ 2 := by
          exact_mod_cast Nat.ceil_le.mpr h4
        have h6 : (Nat.ceil x : ℝ) ^ 2 ≤ 4 := by nlinarith
        have h7 : 4 ≤ (1 / Δ) ^ 4 := by
          have h8 : 1 / Δ ≥ Real.sqrt 2 := by
            have h9 : Δ ≤ 1 / Real.sqrt 2 := h3
            have h10 : 0 < Δ := hΔ
            have h11 : 1 / Δ ≥ 1 / (1 / Real.sqrt 2) := by gcongr
            have h12 : 1 / (1 / Real.sqrt 2) = Real.sqrt 2 := by
              field_simp [Real.sqrt_pos] <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
            linarith
          have h13 : (1 / Δ) ^ 4 ≥ (Real.sqrt 2) ^ 4 := by gcongr
          have h14 : (Real.sqrt 2) ^ 4 = 4 := by
            have h15 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
            calc (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
              _ = 2 ^ 2 := by rw [h15] <;> ring
              _ = 4 := by norm_num
          linarith
        nlinarith
      · -- Subcase Δ > 1/√2
        have h4 : 1 / Real.sqrt 2 < Δ := by linarith
        have h5 : x < 1 := by
          simp only [hx_def]
          have h6 : 0 < Δ := hΔ
          have h7 : Real.sqrt 2 < 2 * Δ := by
            have h8 : 1 / Real.sqrt 2 < Δ := h4
            have h91 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
            have h92 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
            have h9 : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
              have h93 : 1 / Real.sqrt 2 = Real.sqrt 2 / (Real.sqrt 2)^2 := by
                field_simp [h91.ne'] <;> ring
              rw [h93, h92]
            rw [h9] at h8
            linarith
          calc Real.sqrt 2 / (2 * Δ) < (2 * Δ) / (2 * Δ) := by gcongr
            _ = 1 := by field_simp [h6.ne'] <;> ring
        have h6 : Nat.ceil x = 1 := by
          rw [Nat.ceil_eq_iff] <;> norm_num <;> constructor <;> linarith
        rw [h6]
        have h7 : (1 : ℝ) ^ 2 ≤ (1 / Δ) ^ 4 := by
          have h8 : 1 < 1 / Δ := by apply one_lt_one_div <;> linarith
          have h9 : 1 < (1 / Δ) ^ 4 := by
            calc 1 = 1 ^ 4 := by norm_num
              _ < (1 / Δ) ^ 4 := by gcongr <;> linarith
          have h10 : (1 : ℝ) ^ 2 = 1 := by norm_num
          rw [h10]
          linarith
        exact_mod_cast h7
  have h_N_bound : ∀ i < m, (N i : ℝ) ≤ (1 / Δ) ^ 4 := by
    intro i hi
    have h1 : N i ≤ Nat.ceil x ^ 2 := N_i_le_ceiling h_uniform hΔ hΔ1 hi
    have h2 : (N i : ℝ) ≤ (Nat.ceil x : ℝ) ^ 2 := by exact_mod_cast h1
    exact le_trans h2 h_ceil4
  have h_log_bound : ∀ i ∈ Finset.range m, Real.log (N i) ≤ 4 * Real.log (1 / Δ) := by
    intro i hi
    have h_i_lt_m : i < m := Finset.mem_range.mp hi
    have h3 : (N i : ℝ) ≤ (1 / Δ) ^ 4 := h_N_bound i h_i_lt_m
    have h4 : 0 < (N i : ℝ) := hN_pos i h_i_lt_m
    have h5 : Real.log (N i) ≤ Real.log ((1 / Δ) ^ 4) := Real.log_le_log h4 h3
    have h6 : Real.log ((1 / Δ) ^ 4) = 4 * Real.log (1 / Δ) := by
      rw [Real.log_pow] <;> norm_num
    rw [h6] at h5
    exact h5
  have h_f0 : f 0 = 0 := by
    unfold f codeFunction
    simp
  have h_fm : f (m : ℝ) = codeFunctionPartialSum m Δ N m := codeFunction_value (by linarith)
  have h_sum : codeFunctionPartialSum m Δ N m ≤ (m : ℝ) * 4 := by
    dsimp only [codeFunctionPartialSum]
    have h_div : ∀ i ∈ Finset.range m, Real.log (N i) / Real.log (1 / Δ) ≤ 4 := by
      intro i hi
      have h7 : Real.log (N i) ≤ 4 * Real.log (1 / Δ) := h_log_bound i hi
      calc Real.log (N i) / Real.log (1 / Δ)
        ≤ (4 * Real.log (1 / Δ)) / Real.log (1 / Δ) := by gcongr
      _ = 4 := by field_simp [hlog_pos.ne'] <;> ring
    have h8 : ∑ i ∈ Finset.range m, Real.log (N i) / Real.log (1 / Δ) ≤ ∑ i ∈ Finset.range m, (4 : ℝ) := by
      apply Finset.sum_le_sum
      exact h_div
    have h9 : ∑ i ∈ Finset.range m, (4 : ℝ) = (m : ℝ) * 4 := by
      simp [Finset.sum_const] <;> ring
    exact le_trans h8 (le_of_eq h9)
  have h_slope : slope f 0 (m : ℝ) = (f (m : ℝ) - f 0) / (m : ℝ) := by simp [slope]
  rw [h_slope, h_fm]
  have h7 : (m : ℝ) > 0 := by exact_mod_cast hm_pos
  have h10 : codeFunctionPartialSum m Δ N m ≤ (m : ℝ) * 4 := h_sum
  have h11 : codeFunctionPartialSum m Δ N m / (m : ℝ) ≤ 4 := by
    have h_pos : 0 < (m : ℝ) := h7
    have h_div_le : codeFunctionPartialSum m Δ N m / (m : ℝ) ≤ ((m : ℝ) * 4) / (m : ℝ) :=
      div_le_div_of_nonneg_right h10 (by positivity)
    have h_eq : ((m : ℝ) * 4) / (m : ℝ) = 4 := by
      field_simp [h_pos.ne'] <;> ring
    rw [h_eq] at h_div_le
    exact h_div_le
  have h12 : f 0 = 0 := h_f0
  rw [h12]
  simpa using h11

/-! # Dyadic uniformity adaptations

These lemmas adapt the dictionary bounds for `IsDyadicUniform`, which counts
dyadic squares rather than metric balls. Key differences:
- `N_i_le_9` is false; replaced by geometric bound `N_i ≤ (1/Δ)^4`
- `slope_le_4` still holds via the geometric bound
- `codeFunction_product` transfers unchanged (only needs `N i ≥ 1`)
-/

/-- Number of integers k satisfying α < k < β is at most β - α + 1 (as Nat). -/
lemma int_count_bound {α β : ℝ} (h : α < β) :
    ∃ (s : Finset ℤ), (∀ k : ℤ, α < (k : ℝ) → (k : ℝ) < β → k ∈ s) ∧
      (s.card : ℝ) ≤ β - α + 1 := by
  let lo : ℤ := ⌈α⌉
  let hi : ℤ := ⌊β⌋
  by_cases hlo : lo ≤ hi
  · let s := Finset.Icc lo hi
    have h1 : ∀ k : ℤ, α < (k : ℝ) → (k : ℝ) < β → k ∈ s := by
      intro k hα hβ
      have h2 : lo ≤ k := by
        simp only [lo]; exact Int.ceil_le.mpr (by linarith)
      have h3 : k ≤ hi := by
        simp only [hi]; exact Int.le_floor.mpr (by linarith)
      exact Finset.mem_Icc.mpr ⟨h2, h3⟩
    have h5 : lo ≤ hi + 1 := by linarith
    have h4 : (s.card : ℤ) = hi + 1 - lo := Int.card_Icc_of_le lo hi h5
    have h4' : (s.card : ℝ) = (hi : ℝ) - (lo : ℝ) + 1 := by
      exact_mod_cast (by rw [h4] <;> ring)
    refine ⟨s, h1, ?_⟩
    rw [h4']
    have h5' : (lo : ℝ) ≥ α := Int.le_ceil α
    have h6' : (hi : ℝ) ≤ β := Int.floor_le β
    have h7 : (hi : ℝ) - (lo : ℝ) + 1 ≤ β - α + 1 := by linarith [h5', h6']
    exact h7
  · let s : Finset ℤ := ∅
    have h1 : ∀ k : ℤ, α < (k : ℝ) → (k : ℝ) < β → k ∈ s := by
      intro k hα hβ
      have h2 : lo ≤ k := by
        simp only [lo]; exact Int.ceil_le.mpr (by linarith)
      have h3 : k ≤ hi := by
        simp only [hi]; exact Int.le_floor.mpr (by linarith)
      have h4 : lo ≤ hi := by linarith
      exact False.elim (hlo h4)
    have h_pos : 0 ≤ β - α + 1 := by linarith
    refine ⟨s, h1, ?_⟩
    simp [h_pos]

/-- If A ⊆ dyadicSquare L a b, then dyadicSquareCount δ A ≤ ofReal ((L/δ + 2)^2). -/
lemma dyadicSquareCount_geometric_bound {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    {A : Set EuclideanPlane} {a b : ℤ} (hA : A ⊆ dyadicSquare L a b) :
    (dyadicSquareCount δ A : ENNReal) ≤ ENNReal.ofReal ((L / δ + 2) ^ 2) := by
  let S : Set (ℤ × ℤ) := {p | (A ∩ dyadicSquare δ p.1 p.2).Nonempty}
  have h1 : ∀ p ∈ S, (L * (a : ℝ) / δ - 1 < (p.1 : ℝ)) ∧
      ((p.1 : ℝ) < L * ((a : ℝ) + 1) / δ) := by
    intro p hp
    rcases hp with ⟨x, hxA, hxsq⟩
    have hxL : x ∈ dyadicSquare L a b := hA hxA
    have hxa1 : (a : ℝ) * L ≤ x 0 := hxL.1.1
    have hxa2 : x 0 < ((a : ℝ) + 1) * L := hxL.1.2
    have hxp1 : (p.1 : ℝ) * δ ≤ x 0 := hxsq.1.1
    have hxp2 : x 0 < ((p.1 : ℝ) + 1) * δ := hxsq.1.2
    constructor
    · have h5 : x 0 / δ < (p.1 : ℝ) + 1 := by
        calc x 0 / δ < (((p.1 : ℝ) + 1) * δ) / δ := by gcongr
          _ = (p.1 : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
      have h6 : (a : ℝ) * L / δ ≤ x 0 / δ := by
        exact div_le_div_of_nonneg_right hxa1 (by positivity)
      have h7 : (a : ℝ) * L / δ - 1 < (p.1 : ℝ) := by linarith
      have h8 : L * (a : ℝ) / δ - 1 = (a : ℝ) * L / δ - 1 := by ring
      rw [h8]; exact h7
    · have h5 : (p.1 : ℝ) ≤ x 0 / δ := by
        calc (p.1 : ℝ) = ((p.1 : ℝ) * δ) / δ := by field_simp [hδ.ne'] <;> ring
          _ ≤ x 0 / δ := by gcongr
      have h6 : x 0 / δ < ((a : ℝ) + 1) * L / δ := by
        exact div_lt_div_of_pos_right hxa2 (by positivity)
      have h7 : (p.1 : ℝ) < ((a : ℝ) + 1) * L / δ := by linarith
      have h8 : L * ((a : ℝ) + 1) / δ = ((a : ℝ) + 1) * L / δ := by ring
      rw [h8]; exact h7
  have h2 : ∀ p ∈ S, (L * (b : ℝ) / δ - 1 < (p.2 : ℝ)) ∧
      ((p.2 : ℝ) < L * ((b : ℝ) + 1) / δ) := by
    intro p hp
    rcases hp with ⟨x, hxA, hxsq⟩
    have hxL : x ∈ dyadicSquare L a b := hA hxA
    have hxb1 : (b : ℝ) * L ≤ x 1 := hxL.2.1
    have hxb2 : x 1 < ((b : ℝ) + 1) * L := hxL.2.2
    have hxp1 : (p.2 : ℝ) * δ ≤ x 1 := hxsq.2.1
    have hxp2 : x 1 < ((p.2 : ℝ) + 1) * δ := hxsq.2.2
    constructor
    · have h5 : x 1 / δ < (p.2 : ℝ) + 1 := by
        calc x 1 / δ < (((p.2 : ℝ) + 1) * δ) / δ := by gcongr
          _ = (p.2 : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
      have h6 : (b : ℝ) * L / δ ≤ x 1 / δ := by
        exact div_le_div_of_nonneg_right hxb1 (by positivity)
      have h7 : (b : ℝ) * L / δ - 1 < (p.2 : ℝ) := by linarith
      have h8 : L * (b : ℝ) / δ - 1 = (b : ℝ) * L / δ - 1 := by ring
      rw [h8]; exact h7
    · have h5 : (p.2 : ℝ) ≤ x 1 / δ := by
        calc (p.2 : ℝ) = ((p.2 : ℝ) * δ) / δ := by field_simp [hδ.ne'] <;> ring
          _ ≤ x 1 / δ := by gcongr
      have h6 : x 1 / δ < ((b : ℝ) + 1) * L / δ := by
        exact div_lt_div_of_pos_right hxb2 (by positivity)
      have h7 : (p.2 : ℝ) < ((b : ℝ) + 1) * L / δ := by linarith
      have h8 : L * ((b : ℝ) + 1) / δ = ((b : ℝ) + 1) * L / δ := by ring
      rw [h8]; exact h7
  set α1 := L * (a : ℝ) / δ - 1 with hα1
  set β1 := L * ((a : ℝ) + 1) / δ with hβ1
  set α2 := L * (b : ℝ) / δ - 1 with hα2
  set β2 := L * ((b : ℝ) + 1) / δ with hβ2
  have h_ab1 : α1 < β1 := by
    rw [hα1, hβ1]
    have h_pos : 0 < L / δ := by positivity
    have h_eq : L * ((a : ℝ) + 1) / δ = L * (a : ℝ) / δ + L / δ := by
      field_simp [hδ.ne'] <;> ring
    rw [h_eq]; linarith
  have h_ab2 : α2 < β2 := by
    rw [hα2, hβ2]
    have h_pos : 0 < L / δ := by positivity
    have h_eq : L * ((b : ℝ) + 1) / δ = L * (b : ℝ) / δ + L / δ := by
      field_simp [hδ.ne'] <;> ring
    rw [h_eq]; linarith
  rcases int_count_bound h_ab1 with ⟨K, hK_mem, hK_card⟩
  rcases int_count_bound h_ab2 with ⟨Lf, hLf_mem, hLf_card⟩
  have hS_subset : S ⊆ (↑(K ×ˢ Lf) : Set (ℤ × ℤ)) := by
    intro p hp
    have h1' := h1 p hp
    have h2' := h2 p hp
    have hpk : p.1 ∈ K := hK_mem p.1 h1'.1 h1'.2
    have hpl : p.2 ∈ Lf := hLf_mem p.2 h2'.1 h2'.2
    have h9 : p ∈ K ×ˢ Lf := by
      simp only [Finset.mem_product]; exact ⟨hpk, hpl⟩
    exact_mod_cast h9
  have hS_finite : S.Finite := Set.Finite.subset (Finset.finite_toSet (K ×ˢ Lf)) hS_subset
  have h_encard : Set.encard S ≤ ↑((K ×ˢ Lf).card) := by
    calc Set.encard S ≤ Set.encard (↑(K ×ˢ Lf)) := Set.encard_le_encard hS_subset
      _ = ↑((K ×ˢ Lf).card) := by simp
  have h_card_prod : ((K ×ˢ Lf).card : ℝ) = (K.card : ℝ) * (Lf.card : ℝ) := by
    exact_mod_cast Finset.card_product K Lf
  have h9 : ((K ×ˢ Lf).card : ℝ) ≤ (L / δ + 2) ^ 2 := by
    rw [h_card_prod]
    have h_len1 : β1 - α1 = L / δ + 1 := by
      simp only [hα1, hβ1] <;> field_simp [hδ.ne'] <;> ring
    have h_len2 : β2 - α2 = L / δ + 1 := by
      simp only [hα2, hβ2] <;> field_simp [hδ.ne'] <;> ring
    have h10 : (K.card : ℝ) ≤ β1 - α1 + 1 := hK_card
    have h11 : (Lf.card : ℝ) ≤ β2 - α2 + 1 := hLf_card
    have h10' : (K.card : ℝ) ≤ L / δ + 2 := by
      have h_eq1 : β1 - α1 + 1 = L / δ + 2 := by rw [h_len1] <;> ring
      rw [h_eq1] at h10; exact h10
    have h11' : (Lf.card : ℝ) ≤ L / δ + 2 := by
      have h_eq2 : β2 - α2 + 1 = L / δ + 2 := by rw [h_len2] <;> ring
      rw [h_eq2] at h11; exact h11
    have h12 : 0 ≤ (K.card : ℝ) := by positivity
    nlinarith
  have h_final : (↑((K ×ˢ Lf).card) : ENNReal) ≤ ENNReal.ofReal ((L / δ + 2) ^ 2) := by
    have h10 : 0 ≤ (L / δ + 2) ^ 2 := by positivity
    have h11 : ((K ×ˢ Lf).card : ℝ) ≤ (L / δ + 2) ^ 2 := h9
    have h12 : (↑((K ×ˢ Lf).card) : ENNReal) = ENNReal.ofReal ((K ×ˢ Lf).card : ℝ) := by simp
    rw [h12]
    rw [ENNReal.ofReal_le_ofReal_iff h10]; exact h11
  have h10 : (dyadicSquareCount δ A : ENNReal) = (↑(Set.encard S) : ENNReal) := by
    have h11 : dyadicSquareCount δ A = Set.encard S := by rfl
    rw [h11] <;> rfl
  rw [h10]
  exact le_trans (by exact_mod_cast h_encard) h_final

lemma helper_ineq {x : ℝ} (hx : x ≥ 2) : (x + 2) ^ 2 ≤ x ^ 4 := by
  have h1 : x ^ 2 ≥ 4 := by nlinarith
  nlinarith [sq_nonneg (x - 2), sq_nonneg (x ^ 2 - 4)]

/-- For Δ ≤ 1/2, N(i) ≤ (1/Δ)^4 under IsDyadicUniform. -/
lemma N_i_le_invDelta4 {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N) (hΔ : 0 < Δ) (hΔ2 : Δ ≤ 1 / 2)
    {i : ℕ} (hi : i < m) : (N i : ℝ) ≤ (1 / Δ) ^ 4 := by
  have hP_ne : P.Nonempty := h_uniform.2.2.1
  rcases hP_ne with ⟨x, hx⟩
  let a : ℤ := ⌊x 0 / (Δ ^ i)⌋
  let b : ℤ := ⌊x 1 / (Δ ^ i)⌋
  have hΔi_pos : 0 < Δ ^ i := by positivity
  have h_x_in_square : x ∈ dyadicSquare (Δ ^ i) a b := by
    simp only [dyadicSquare]
    have h1a : (a : ℝ) ≤ x 0 / (Δ ^ i) := Int.floor_le (x 0 / (Δ ^ i))
    have h2a : x 0 / (Δ ^ i) < (a : ℝ) + 1 := Int.lt_floor_add_one (x 0 / (Δ ^ i))
    have h1b : (b : ℝ) ≤ x 1 / (Δ ^ i) := Int.floor_le (x 1 / (Δ ^ i))
    have h2b : x 1 / (Δ ^ i) < (b : ℝ) + 1 := Int.lt_floor_add_one (x 1 / (Δ ^ i))
    constructor
    · constructor
      · calc (a : ℝ) * (Δ ^ i) ≤ (x 0 / (Δ ^ i)) * (Δ ^ i) := by gcongr
        _ = x 0 := by field_simp [hΔi_pos.ne'] <;> ring
      · calc x 0 = (x 0 / (Δ ^ i)) * (Δ ^ i) := by field_simp [hΔi_pos.ne'] <;> ring
        _ < ((a : ℝ) + 1) * (Δ ^ i) := by gcongr
    · constructor
      · calc (b : ℝ) * (Δ ^ i) ≤ (x 1 / (Δ ^ i)) * (Δ ^ i) := by gcongr
        _ = x 1 := by field_simp [hΔi_pos.ne'] <;> ring
      · calc x 1 = (x 1 / (Δ ^ i)) * (Δ ^ i) := by field_simp [hΔi_pos.ne'] <;> ring
        _ < ((b : ℝ) + 1) * (Δ ^ i) := by gcongr
  have hne : (P ∩ dyadicSquare (Δ ^ i) a b).Nonempty := ⟨x, hx, h_x_in_square⟩
  have h_unif : (dyadicSquareCount (Δ ^ (i + 1)) (P ∩ dyadicSquare (Δ ^ i) a b) : ENNReal) =
      (↑(N i) : ENNReal) := h_uniform.2.2.2.2 i hi a b hne
  have h_geom : (dyadicSquareCount (Δ ^ (i + 1)) (P ∩ dyadicSquare (Δ ^ i) a b) : ENNReal) ≤
      ENNReal.ofReal (((Δ ^ i) / (Δ ^ (i + 1)) + 2) ^ 2) :=
    dyadicSquareCount_geometric_bound hΔi_pos (by positivity) Set.inter_subset_right
  have h_ratio : (Δ ^ i) / (Δ ^ (i + 1)) = 1 / Δ := by
    field_simp [hΔ.ne'] <;> ring
  rw [h_ratio] at h_geom
  rw [h_unif] at h_geom
  have h_x_ge2 : 1 / Δ ≥ 2 := by
    have h'' : 1 / Δ ≥ 2 := by
      calc 1 / Δ ≥ 1 / (1 / 2 : ℝ) := by gcongr
        _ = 2 := by norm_num
    exact h''
  have h9 : ENNReal.ofReal (((1 / Δ + 2) ^ 2)) ≤ ENNReal.ofReal (((1 / Δ) ^ 4)) := by
    apply ENNReal.ofReal_le_ofReal
    exact helper_ineq h_x_ge2
  have h10 : (↑(N i) : ENNReal) ≤ ENNReal.ofReal (((1 / Δ) ^ 4)) := le_trans h_geom h9
  have h11 : 0 ≤ (1 / Δ) ^ 4 := by positivity
  have h12 : (N i : ℝ) ≤ (1 / Δ) ^ 4 := by
    have h13 : (↑(N i) : ENNReal) = ENNReal.ofReal (N i : ℝ) := by simp
    rw [h13] at h10
    rw [ENNReal.ofReal_le_ofReal_iff h11] at h10
    exact h10
  exact h12

/-- slope ≤ 4 for IsDyadicUniform when Δ ≤ 1/2. -/
lemma slope_le_4_dyadic {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hΔ2 : Δ ≤ 1 / 2) :
    slope (codeFunction m Δ N) 0 (m : ℝ) ≤ 4 := by
  by_cases hm : m = 0
  · subst hm; simp [slope] <;> norm_num
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
  let f := codeFunction m Δ N
  have hlog_pos : 0 < Real.log (1 / Δ) := by
    have h2 : 1 < 1 / Δ := by apply one_lt_one_div <;> linarith
    exact Real.log_pos h2
  have hN_pos : ∀ i < m, 0 < (N i : ℝ) := by
    intro i hi
    have h3 : N i ≥ 1 := h_uniform.2.2.2.1 i hi
    exact_mod_cast (by linarith)
  have h_N_bound : ∀ i < m, (N i : ℝ) ≤ (1 / Δ) ^ 4 := by
    intro i hi; exact N_i_le_invDelta4 h_uniform hΔ hΔ2 hi
  have h_log_bound : ∀ i ∈ Finset.range m, Real.log (N i) ≤ 4 * Real.log (1 / Δ) := by
    intro i hi
    have h_i_lt_m : i < m := Finset.mem_range.mp hi
    have h3 : (N i : ℝ) ≤ (1 / Δ) ^ 4 := h_N_bound i h_i_lt_m
    have h4 : 0 < (N i : ℝ) := hN_pos i h_i_lt_m
    have h5 : Real.log (N i) ≤ Real.log ((1 / Δ) ^ 4) := Real.log_le_log h4 h3
    have h6 : Real.log ((1 / Δ) ^ 4) = 4 * Real.log (1 / Δ) := by
      rw [Real.log_pow] <;> norm_num
    rw [h6] at h5; exact h5
  have h_f0 : f 0 = 0 := by unfold f codeFunction; simp
  have h_fm : f (m : ℝ) = codeFunctionPartialSum m Δ N m := codeFunction_value (by linarith)
  have h_sum : codeFunctionPartialSum m Δ N m ≤ (m : ℝ) * 4 := by
    dsimp only [codeFunctionPartialSum]
    have h_div : ∀ i ∈ Finset.range m, Real.log (N i) / Real.log (1 / Δ) ≤ 4 := by
      intro i hi
      have h7 : Real.log (N i) ≤ 4 * Real.log (1 / Δ) := h_log_bound i hi
      calc Real.log (N i) / Real.log (1 / Δ)
        ≤ (4 * Real.log (1 / Δ)) / Real.log (1 / Δ) := by gcongr
      _ = 4 := by field_simp [hlog_pos.ne'] <;> ring
    have h8 : ∑ i ∈ Finset.range m, Real.log (N i) / Real.log (1 / Δ) ≤ ∑ i ∈ Finset.range m, (4 : ℝ) := by
      apply Finset.sum_le_sum; exact h_div
    have h9 : ∑ i ∈ Finset.range m, (4 : ℝ) = (m : ℝ) * 4 := by
      simp [Finset.sum_const] <;> ring
    exact le_trans h8 (le_of_eq h9)
  have h_slope : slope f 0 (m : ℝ) = (f (m : ℝ) - f 0) / (m : ℝ) := by simp [slope]
  rw [h_slope, h_fm]
  have h7 : (m : ℝ) > 0 := by exact_mod_cast hm_pos
  have h10 : codeFunctionPartialSum m Δ N m ≤ (m : ℝ) * 4 := h_sum
  have h11 : codeFunctionPartialSum m Δ N m / (m : ℝ) ≤ 4 := by
    have h_pos : 0 < (m : ℝ) := h7
    have h_div_le : codeFunctionPartialSum m Δ N m / (m : ℝ) ≤ ((m : ℝ) * 4) / (m : ℝ) :=
      div_le_div_of_nonneg_right h10 (by positivity)
    have h_eq : ((m : ℝ) * 4) / (m : ℝ) = 4 := by
      field_simp [h_pos.ne'] <;> ring
    rw [h_eq] at h_div_le; exact h_div_le
  have h12 : f 0 = 0 := h_f0
  rw [h12]; simpa using h11

/-- Product formula for IsDyadicUniform (only needs N i ≥ 1). -/
lemma codeFunction_product_dyadic {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    {j : ℕ} (hjm : j ≤ m) :
    (∏ i ∈ Finset.range j, (N i : ℝ)) = Real.rpow Δ (-(codeFunction m Δ N (j : ℝ))) := by
  have hN_pos : ∀ i < m, N i ≥ 1 := h_uniform.2.2.2.1
  have hlog_pos : 0 < Real.log (1 / Δ) := by
    have h2 : 1 < 1 / Δ := by apply one_lt_one_div <;> linarith
    exact Real.log_pos h2
  have h_base_pos : 0 < (1 / Δ) := by positivity
  have h_base_ne_one : (1 / Δ) ≠ 1 := by
    have h2 : 1 < 1 / Δ := by apply one_lt_one_div <;> linarith
    linarith
  have h_code_eq : codeFunction m Δ N (j : ℝ) = codeFunctionPartialSum m Δ N j := codeFunction_value hjm
  rw [h_code_eq]
  have hN_pos' : ∀ i ∈ Finset.range j, 0 < (N i : ℝ) := by
    intro i hi
    have h_i_lt_j : i < j := Finset.mem_range.mp hi
    have h_i_lt_m : i < m := by linarith
    have h3 : N i ≥ 1 := hN_pos i h_i_lt_m
    exact_mod_cast h3
  have h_main : Real.rpow (1 / Δ) (codeFunctionPartialSum m Δ N j) =
      ∏ i ∈ Finset.range j, (N i : ℝ) := by
    simp only [codeFunctionPartialSum]
    have h6 : Real.rpow (1 / Δ) (∑ i ∈ Finset.range j, Real.log (N i) / Real.log (1 / Δ)) =
        ∏ i ∈ Finset.range j, Real.rpow (1 / Δ) (Real.log (N i) / Real.log (1 / Δ)) := by
      exact Real.rpow_sum_of_pos h_base_pos (fun i => Real.log (N i) / Real.log (1 / Δ)) (Finset.range j)
    rw [h6]
    apply Finset.prod_congr rfl
    intro i hi
    have hNi_pos : 0 < (N i : ℝ) := hN_pos' i hi
    have h7 : Real.rpow (1 / Δ) (Real.log (N i) / Real.log (1 / Δ)) = (N i : ℝ) := by
      have h8 : Real.log (N i) / Real.log (1 / Δ) = Real.logb (1 / Δ) (N i : ℝ) := by
        simp [Real.logb] <;> ring
      rw [h8]
      exact Real.rpow_logb h_base_pos h_base_ne_one hNi_pos
    exact h7
  have h4 : Real.rpow Δ (-(codeFunctionPartialSum m Δ N j)) =
      Real.rpow (1 / Δ) (codeFunctionPartialSum m Δ N j) := by
    let y := codeFunctionPartialSum m Δ N j
    have h_pos1 : 0 < Δ := hΔ
    have h_pos2 : 0 < (1 / Δ) := by positivity
    have h_log : Real.log (1 / Δ) = -Real.log Δ := by
      rw [Real.log_div (by positivity) (by positivity)] <;> simp
    have h_eq1 : Real.rpow Δ (-y) = Real.exp (Real.log Δ * (-y)) := Real.rpow_def_of_pos hΔ (-y)
    have h_eq2 : Real.rpow (1 / Δ) y = Real.exp (Real.log (1 / Δ) * y) := Real.rpow_def_of_pos h_pos2 y
    rw [h_eq1, h_eq2, h_log] <;> ring_nf
  rw [h4, h_main]

end MultiscaleDecomposition

end DirecretisedFurstenbergEstimate

end
