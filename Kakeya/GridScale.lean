/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The geometric grid of scales

The scales `ρ_k = δ^{k/N}`, `0 ≤ k ≤ N`, interpolating between `1` and `δ` in `N` equal
multiplicative steps, together with the arithmetic of that grid.

Every multiscale statement in this development is indexed by this grid, so it is factored out
here as a leaf: `Kakeya.Uniform` (the hierarchy `UniformTubeSet` is defined along the grid)
and `Kakeya.MultiScaleFac.Stopping` (the stopping time cuts the grid) both need it, and neither
imports the other.
-/

@[expose] public section

open MeasureTheory Real Metric


namespace Tube

/-- The `k`-th scale of the geometric grid `1 = δ^{0/N} ≥ δ^{1/N} ≥ … ≥ δ^{N/N} = δ`
interpolating between the coarse scale `1` and the fine scale `δ` in `N` equal steps.
Small `k` is coarse, large `k` is fine. -/
noncomputable def gridScale (δ : NNReal) (N k : ℕ) : NNReal := δ ^ ((k : ℝ) / (N : ℝ))

/-- The set of grid scales `{δ^{k/N} : k ≤ N}`, the scale set along which GWZ Lemma 7.7(A)
assumes uniformity of the tube family. -/
def gridScales (δ : NNReal) (N : ℕ) : Set NNReal :=
  { ρ : NNReal | ∃ k : ℕ, k ≤ N ∧ ρ = δ ^ ((k : ℝ) / (N : ℝ)) }

/-- Every grid index at most `N` names a point of the grid scale set. -/
theorem gridScale_mem_gridScales (δ : NNReal) {N k : ℕ} (hk : k ≤ N) :
    gridScale δ N k ∈ gridScales δ N := by
  exact ⟨k, hk, rfl⟩

/-- The coarse endpoint of the grid is the scale `1`. -/
@[simp]
theorem gridScale_zero (δ : NNReal) (N : ℕ) : gridScale δ N 0 = 1 := by
  simp [gridScale]

/-- The fine endpoint of the grid is the scale `δ`. -/
theorem gridScale_self (δ : NNReal) {N : ℕ} (hN : 0 < N) : gridScale δ N N = δ := by
  simp [gridScale, (Nat.cast_ne_zero.mpr hN.ne')]

/-- Grid scales are positive whenever `δ` is. -/
theorem gridScale_pos {δ : NNReal} (hδ : 0 < δ) (N k : ℕ) : 0 < gridScale δ N k := by
  unfold gridScale
  exact NNReal.rpow_pos hδ

/-- Grid scales never exceed `1`. -/
theorem gridScale_le_one {δ : NNReal} (hδ : δ ≤ 1) (N k : ℕ) : gridScale δ N k ≤ 1 := by
  unfold gridScale
  exact NNReal.rpow_le_one hδ (by positivity)

/-- The grid is antitone in the index: larger index means finer scale. -/
theorem gridScale_antitone {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ) {k l : ℕ}
    (hkl : k ≤ l) : gridScale δ N l ≤ gridScale δ N k := by
  unfold gridScale
  apply NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hN0 : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hkl) hN0

/-- The ratio of two grid scales is an explicit power of `δ`. -/
theorem gridScale_div_gridScale {δ : NNReal} (hδ : 0 < δ) (N a b : ℕ) :
    gridScale δ N a / gridScale δ N b = δ ^ (-(((b : ℝ) - (a : ℝ)) / (N : ℝ))) := by
  unfold gridScale
  rw [← NNReal.rpow_sub (ne_of_gt hδ) ((a : ℝ) / (N : ℝ)) ((b : ℝ) / (N : ℝ))]
  congr 1
  ring

/-- **The grid is strictly antitone.**  Needs `δ < 1`, unlike `gridScale_antitone`. -/
theorem gridScale_lt_gridScale {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ < 1) {N : ℕ} (hN : 0 < N)
    {k l : ℕ} (hkl : k < l) : gridScale δ N l < gridScale δ N k := by
  unfold gridScale
  exact NNReal.rpow_lt_rpow_of_exponent_gt hδ hδ1
    (by exact div_lt_div_of_pos_right (by exact_mod_cast hkl) (by exact_mod_cast hN))

/-- **Comparing two real powers of `δ` along the grid exponent scale.**  The interpolating form
of `gridScale_antitone`: for `0 < δ < 1` the map `x ↦ δ^{x/N}` is strictly antitone, so an
inequality between two such powers is exactly the reversed inequality between the exponents.
This is what converts the endpoint conditions of alternative (ii)-3, which are stated as products
of grid scales with a real power, into inequalities between the grid indices. -/
theorem rpow_div_le_rpow_div_iff {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1) {N : ℕ}
    (hN : 0 < N) (x y : ℝ) :
    (δ : ℝ) ^ (x / (N : ℝ)) ≤ (δ : ℝ) ^ (y / (N : ℝ)) ↔ y ≤ x := by
  have hδ0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [Real.rpow_le_rpow_left_iff_of_base_lt_one hδ0 hδ1]
  exact div_le_div_iff_of_pos_right hN0

/-- **The two endpoints of the interval of alternative (ii)-3 are grid powers.**  Both
`τ(θ/τ)^ε` and `θ(τ/θ)^ε` with `τ = σ_b`, `θ = σ_a` are `δ` raised to an explicit affine
combination of the block endpoints, which is what makes them comparable with grid scales through
`rpow_div_le_rpow_div_iff`. -/
theorem gridScale_mul_ratio_rpow {δ : NNReal} (hδ : 0 < δ) (N a b : ℕ) (ε : ℝ) :
    (gridScale δ N b : ℝ) * ((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ ε
      = (δ : ℝ) ^ (((b : ℝ) - ε * ((b : ℝ) - (a : ℝ))) / (N : ℝ)) := by
  have hδpos : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hδnonneg : 0 ≤ (δ : ℝ) := le_of_lt hδpos
  have hs : ∀ k : ℕ, (gridScale δ N k : ℝ) = (δ : ℝ) ^ ((k : ℝ) / (N : ℝ)) := by
    intro k
    rw [gridScale]
    exact NNReal.coe_rpow δ ((k : ℝ) / (N : ℝ))
  calc
    (gridScale δ N b : ℝ) * ((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ ε
        = (δ : ℝ) ^ ((b : ℝ) / (N : ℝ)) *
            (((δ : ℝ) ^ ((a : ℝ) / (N : ℝ))) / ((δ : ℝ) ^ ((b : ℝ) / (N : ℝ)))) ^ ε := by
              rw [hs b, hs a]
    _ = (δ : ℝ) ^ ((b : ℝ) / (N : ℝ)) *
            ((δ : ℝ) ^ (((a : ℝ) / (N : ℝ)) - ((b : ℝ) / (N : ℝ)))) ^ ε := by
              rw [← Real.rpow_sub hδpos]
    _ = (δ : ℝ) ^ ((b : ℝ) / (N : ℝ)) *
            (δ : ℝ) ^ ((((a : ℝ) / (N : ℝ)) - ((b : ℝ) / (N : ℝ))) * ε) := by
              rw [← Real.rpow_mul hδnonneg]
    _ = (δ : ℝ) ^ (((b : ℝ) / (N : ℝ)) + ((((a : ℝ) / (N : ℝ)) - ((b : ℝ) / (N : ℝ))) * ε)) := by
              rw [← Real.rpow_add hδpos]
    _ = (δ : ℝ) ^ (((b : ℝ) - ε * ((b : ℝ) - (a : ℝ))) / (N : ℝ)) := by
              congr 1
              ring

/-- **Grid indices are recovered from grid scales.**  The converse of `gridScale_antitone`,
available because the grid is strictly antitone for `δ < 1`. -/
theorem le_of_gridScale_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ < 1) {N : ℕ} (hN : 0 < N)
    {k l : ℕ} (h : gridScale δ N l ≤ gridScale δ N k) : k ≤ l := by
  by_contra hnot
  have hlk : l < k := not_le.mp hnot
  have hlt : gridScale δ N k < gridScale δ N l := gridScale_lt_gridScale hδ hδ1 hN hlk
  exact absurd hlt (not_lt.mpr h)

/-- **Consecutive grid scales are `16`-separated.**  This is the smallness threshold
`δ₀ = 16^{-N}` of GWZ Lemma 7.7(A): it is exactly what makes the grid an admissible chain for
`MultiScaleFac.frostmanConstant_fibre_le_prod`, whose gap hypothesis is a factor `16`. -/
theorem sixteen_mul_gridScale_succ_le {δ : NNReal} (hδ : 0 < δ) {N : ℕ}
    (hδ0 : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) {k : ℕ} (hk : k < N) :
    16 * gridScale δ N (k + 1) ≤ gridScale δ N k := by
  have hN0 : 0 < N := lt_of_le_of_lt (Nat.zero_le k) hk
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN0)
  have hE : 0 ≤ (1 : ℝ) / (N : ℝ) := by positivity
  have hδinv : δ ^ ((1 : ℝ) / (N : ℝ)) ≤ (1 : NNReal) / 16 := by
    calc
      δ ^ ((1 : ℝ) / (N : ℝ))
          ≤ ((16 : NNReal) ^ (-(N : ℝ))) ^ ((1 : ℝ) / (N : ℝ)) := NNReal.rpow_le_rpow hδ0 hE
      _ = (16 : NNReal) ^ ((-(N : ℝ)) * ((1 : ℝ) / (N : ℝ))) := by rw [NNReal.rpow_mul]
      _ = (16 : NNReal) ^ (-(1 : ℝ)) := by congr 1; field_simp [hNne]
      _ = (1 : NNReal) / 16 := by rw [NNReal.rpow_neg_one]; norm_num
  have hδle1 : 16 * δ ^ ((1 : ℝ) / (N : ℝ)) ≤ 1 := by
    calc
      16 * δ ^ ((1 : ℝ) / (N : ℝ)) ≤ 16 * ((1 : NNReal) / 16) := by gcongr
      _ = 1 := by norm_num
  have hfac : gridScale δ N (k + 1) = gridScale δ N k * δ ^ ((1 : ℝ) / (N : ℝ)) := by
    unfold gridScale
    rw [show (((k + 1 : ℕ) : ℝ) / (N : ℝ)) =
          (((k : ℕ) : ℝ) / (N : ℝ)) + (1 : ℝ) / (N : ℝ) by
          push_cast; field_simp [hNne]]
    rw [NNReal.rpow_add (ne_of_gt hδ)]
  calc
    16 * gridScale δ N (k + 1)
        = 16 * (gridScale δ N k * δ ^ ((1 : ℝ) / (N : ℝ))) := by rw [hfac]
    _ = gridScale δ N k * (16 * δ ^ ((1 : ℝ) / (N : ℝ))) := by ring
    _ ≤ gridScale δ N k * 1 := by gcongr
    _ = gridScale δ N k := by rw [mul_one]

/-- A grid gap of at least one step is `16`-separated: the monotone form of
`sixteen_mul_gridScale_succ_le`. -/
theorem sixteen_mul_gridScale_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ}
    (hδ0 : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) {a b : ℕ} (hab : a < b) (hb : b ≤ N) :
    16 * gridScale δ N b ≤ gridScale δ N a := by
  calc
    16 * gridScale δ N b ≤ 16 * gridScale δ N (a + 1) := by
      gcongr
      exact gridScale_antitone hδ hδ1 N (by omega : a + 1 ≤ b)
    _ ≤ gridScale δ N a := sixteen_mul_gridScale_succ_le hδ hδ0 (by omega : a < N)

/-- Telescoping product of adjacent ratios, on `ℕ`. -/
lemma prod_ratio_telescope_nat (M : ℕ) (g : ℕ → ℝ) (hg : ∀ i, 0 < g i) :
    ∏ i ∈ Finset.range M, (g i / g (i + 1)) = g 0 / g M := by
  induction M with
  | zero =>
      simp [div_self (hg 0).ne']
  | succ m ih =>
      rw [Finset.prod_range_succ, ih]
      field_simp [(hg m).ne', (hg (m + 1)).ne']

/-- The adjacent-scale ratios telescope across the grid. -/
lemma prod_ratio_telescope (M : ℕ) (ρ : Fin (M + 1) → NNReal)
    (hρ_pos : ∀ k, 0 < (ρ k : ℝ)) :
    ∏ k : Fin M, ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ))
      = (ρ 0 : ℝ) / (ρ (Fin.last M) : ℝ) := by
  set g : ℕ → ℝ := fun i => (ρ ⟨min i M, by omega⟩ : ℝ) with hg_def
  have hg_pos : ∀ i, 0 < g i := by
    intro i
    dsimp [g]
    exact hρ_pos ⟨min i M, by omega⟩
  have hg0 : g 0 = (ρ 0 : ℝ) := by
    simp [g]
  have hgM : g M = (ρ (Fin.last M) : ℝ) := by
    simp [g, Fin.last]
  have h_match : (∏ k : Fin M, ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ))) =
      ∏ i : Fin M, (g i / g (i + 1)) := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk_val_lt_M : (k : ℕ) < M := k.isLt
    have hk_val_le_M : (k : ℕ) ≤ M := Nat.le_of_lt hk_val_lt_M
    have hk_val_succ_le_M : (k : ℕ) + 1 ≤ M := by omega
    have h_castSucc : (ρ k.castSucc : ℝ) = (g (k : ℕ) : ℝ) := by
      dsimp [g]
      have hmin : min (k : ℕ) M = (k : ℕ) := Nat.min_eq_left hk_val_le_M
      have h_val : (k.castSucc : Fin (M + 1)).val = min (k : ℕ) M := by
        simp [Fin.val_castSucc]
      have h_eq : (k.castSucc : Fin (M + 1)) = ⟨min (k : ℕ) M, by omega⟩ := by
        apply Fin.ext
        exact h_val
      simp [h_eq]
    have h_succ : (ρ k.succ : ℝ) = (g ((k : ℕ) + 1) : ℝ) := by
      dsimp [g]
      have hmin : min ((k : ℕ) + 1) M = (k : ℕ) + 1 := Nat.min_eq_left hk_val_succ_le_M
      have h_val : (k.succ : Fin (M + 1)).val = min ((k : ℕ) + 1) M := by
        simp [Fin.val_succ]
      have h_eq : (k.succ : Fin (M + 1)) = ⟨min ((k : ℕ) + 1) M, by omega⟩ := by
        apply Fin.ext
        exact h_val
      simp [h_eq]
    simp [h_castSucc, h_succ]
  calc
    ∏ k : Fin M, ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ))
        = ∏ i : Fin M, (g i / g (i + 1)) := h_match
    _ = ∏ i ∈ Finset.range M, (g i / g (i + 1)) := by
      rw [Fin.prod_univ_eq_prod_range (fun i => g i / g (i + 1)) M]
    _ = g 0 / g M := prod_ratio_telescope_nat M g hg_pos
    _ = (ρ 0 : ℝ) / (ρ (Fin.last M) : ℝ) := by rw [hg0, hgM]

/-- The grid scales above the bottom one are `16`-separated from `δ`, so in particular
`8 δ ≤ σ_k` for `k < N`. -/
theorem eight_delta_le_gridScale {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N k : ℕ} (hk : k < N)
    (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) : 8 * δ ≤ gridScale δ N k := by
  have hN0 : 0 < N := lt_of_le_of_lt (Nat.zero_le k) hk
  have hkN : k + 1 ≤ N := Nat.succ_le_of_lt hk
  have hgeom : 16 * gridScale δ N (k + 1) ≤ gridScale δ N k :=
    sixteen_mul_gridScale_succ_le hδ hδN hk
  have hδσ : δ ≤ gridScale δ N (k + 1) := by
    have h' : gridScale δ N N ≤ gridScale δ N (k + 1) := gridScale_antitone hδ hδ1 N hkN
    rwa [gridScale_self δ hN0] at h'
  calc
    8 * δ ≤ 16 * δ := by
      exact mul_le_mul_of_nonneg_right (by norm_num : (8 : NNReal) ≤ 16) (le_of_lt hδ)
    _ ≤ 16 * gridScale δ N (k + 1) :=
      mul_le_mul_of_nonneg_left hδσ (by norm_num : (0 : NNReal) ≤ 16)
    _ ≤ gridScale δ N k := hgeom

end Tube
