import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.ScaleInterpolation

/-!
# Real-valued power grid

The real scale grid `s_k = δ^(k/N)` for `k : ℕ`, where `0 < N` and
`0 < δ < 1`.  This is the real-valued counterpart of
`RandomTranslation.scaleGrid`, with exact endpoints, strict descent, ratio
identity, and bracketing of every admissible scale.
-/

noncomputable section

open Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/-- The `k`-th real grid point `s_k = δ^(k/N)`. -/
def realScaleGrid (δ : ℝ) (N : ℕ) (k : ℕ) : ℝ :=
  Real.rpow δ ((k : ℝ) / (N : ℝ))

/-- The first grid point is one. -/
lemma realScaleGrid_zero (δ : ℝ) (N : ℕ) :
    realScaleGrid δ N 0 = 1 := by
  simp [realScaleGrid]

/-- The last grid point is `δ`. -/
lemma realScaleGrid_N (δ : ℝ) (N : ℕ) (hN : 0 < N) :
    realScaleGrid δ N N = δ := by
  have h : (N : ℝ) / (N : ℝ) = 1 := by
    field_simp [hN.ne']
  rw [realScaleGrid, h]
  simp

/-- Every grid point from zero through `N` lies in `[δ, 1]`. -/
lemma realScaleGrid_range (δ : ℝ) (N : ℕ) (hN : 0 < N)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (k : ℕ) (hk : k ≤ N) :
    δ ≤ realScaleGrid δ N k ∧ realScaleGrid δ N k ≤ 1 := by
  set y : ℝ := (k : ℝ) / (N : ℝ)
  have hN' : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN
  have hy_nonneg : 0 ≤ y := by
    positivity
  have hy_le_one : y ≤ 1 := by
    have hk' : (k : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hk
    exact (div_le_one hN').mpr hk'
  have hδ_le_one : δ ≤ 1 := hδ_lt_one.le
  have h_upper : realScaleGrid δ N k ≤ 1 := by
    rw [realScaleGrid]
    have h :
        Real.rpow δ y ≤ Real.rpow δ 0 :=
      Real.rpow_le_rpow_of_exponent_ge
        hδ_pos hδ_le_one hy_nonneg
    simpa using h
  have h_lower : δ ≤ realScaleGrid δ N k := by
    rw [realScaleGrid]
    have h :
        Real.rpow δ 1 ≤ Real.rpow δ y :=
      Real.rpow_le_rpow_of_exponent_ge
        hδ_pos hδ_le_one hy_le_one
    simpa using h
  exact ⟨h_lower, h_upper⟩

/-- The power grid is strictly decreasing before its last point. -/
lemma realScaleGrid_strict_desc (δ : ℝ) (N : ℕ) (hN : 0 < N)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (k : ℕ) (_hk : k < N) :
    realScaleGrid δ N (k + 1) < realScaleGrid δ N k := by
  set y : ℝ := ((k + 1 : ℕ) : ℝ) / (N : ℝ)
  set z : ℝ := (k : ℝ) / (N : ℝ)
  have hN' : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN
  have hz_lt_y : z < y := by
    have hcast : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by
      simp [Nat.cast_add]
    exact div_lt_div_of_pos_right hcast hN'
  have hpow :
      Real.rpow δ y < Real.rpow δ z :=
    Real.rpow_lt_rpow_of_exponent_gt
      hδ_pos hδ_lt_one hz_lt_y
  simpa [realScaleGrid, y, z] using hpow

/-- Correspondence with the existing ENNReal scale grid. -/
lemma realScaleGrid_ennreal (δ : ℝ) (N : ℕ) (k : ℕ) :
    ENNReal.ofReal (realScaleGrid δ N k) =
      RandomTranslation.scaleGrid δ N k := by
  simp [realScaleGrid, RandomTranslation.scaleGrid,
    Kakeya.realRpowENN]

/-- The adjacent grid points have the exact power-grid ratio. -/
lemma realScaleGrid_ratio (δ : ℝ) (N : ℕ) (hN : 0 < N)
    (hδ_pos : 0 < δ) (k : ℕ) :
    ENNReal.ofReal (realScaleGrid δ N k) =
      Kakeya.realRpowENN δ (-(1 / (N : ℝ))) *
        ENNReal.ofReal (realScaleGrid δ N (k + 1)) := by
  have h :=
    RandomTranslation.scaleGrid_ratio δ N hδ_pos hN k
  simpa [realScaleGrid_ennreal] using h

/-- Every scale in `[δ, 1]` is bracketed by consecutive grid points. -/
lemma realScaleGrid_bracket (δ : ℝ) (N : ℕ) (hN : 0 < N)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (ρ : ℝ) (hρ1 : δ ≤ ρ) (hρ2 : ρ ≤ 1) :
    ∃ k : ℕ, k < N ∧
      realScaleGrid δ N (k + 1) ≤ ρ ∧
      ρ ≤ realScaleGrid δ N k := by
  have h_main :=
    RandomTranslation.scaleGrid_bracket
      δ N hδ_pos hδ_lt_one.le hN ρ hρ1 hρ2
  rcases h_main with ⟨k, hk_lt_N, h1, h2⟩
  have h1' :
      ENNReal.ofReal (realScaleGrid δ N (k + 1)) ≤
        ENNReal.ofReal ρ := by
    rw [realScaleGrid_ennreal]
    exact h1
  have h2' :
      ENNReal.ofReal ρ ≤
        ENNReal.ofReal (realScaleGrid δ N k) := by
    rw [realScaleGrid_ennreal]
    exact h2
  have h_nonneg2 : 0 ≤ realScaleGrid δ N k :=
    Real.rpow_nonneg hδ_pos.le _
  have h_nonnegρ : 0 ≤ ρ := hδ_pos.le.trans hρ1
  have h5 : realScaleGrid δ N (k + 1) ≤ ρ :=
    (ENNReal.ofReal_le_ofReal_iff h_nonnegρ).mp h1'
  have h6 : ρ ≤ realScaleGrid δ N k :=
    (ENNReal.ofReal_le_ofReal_iff h_nonneg2).mp h2'
  exact ⟨k, hk_lt_N, h5, h6⟩

end Kakeya.Streamlined.RandomTranslation.WithShading

end
