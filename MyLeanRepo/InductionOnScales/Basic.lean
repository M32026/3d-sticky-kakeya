module

public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Induction on Scales: Foundational Lemmas

This module provides foundational lemmas for the source-faithful induction
on scales theorem (OS Proposition 5.1).

Main results:
- `coarseParentIndex_spec`: floor division characterization of the parent index
- `localSlopeCellIndex_spec`: floor division for the local slope cell
- `tube_containment_iff`: geometric containment of dyadic tubes iff interval nesting
- `containingSquare_is_containing`: the containing square indeed contains the fine square
-/

namespace InductionOnScales

open DyadicTube

-- ============================================================================
-- Basic dyadic delta properties
-- ============================================================================

lemma dyadicDelta_pos (n : ℕ) : 0 < dyadicDelta n := by
  simp [dyadicDelta] <;> positivity

lemma dyadicDelta_eq_inv (n : ℕ) : dyadicDelta n = 1 / (2 ^ n : ℝ) := by
  simp [dyadicDelta, Real.rpow_neg, Real.rpow_natCast]
  <;> field_simp
  <;> ring

/-- `1 / (dyadicDelta n)^2 = 4^n`. -/
lemma one_over_dyadicDelta_sq (n : ℕ) :
    (1 : ℝ) / (dyadicDelta n)^2 = (4 : ℝ)^n := by
  have h1 : dyadicDelta n = 1 / (2 ^ n : ℝ) := dyadicDelta_eq_inv n
  rw [h1]
  have h_pos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
  have h2 : (1 : ℝ) / ((1 / (2 ^ n : ℝ)) ^ 2) = (2 ^ n : ℝ)^2 := by
    field_simp [h_pos.ne'] <;> ring
  rw [h2]
  have h3 : (2 ^ n : ℝ)^2 = (4 ^ n : ℝ) := by
    have h4 : (2 ^ n : ℝ)^2 = (2 ^ n : ℝ) * (2 ^ n : ℝ) := by ring
    rw [h4]
    have h5 : (2 ^ n : ℝ) * (2 ^ n : ℝ) = ((2 * 2 : ℝ)^n) := by
      rw [← mul_pow] <;> norm_num
    rw [h5] <;> norm_num
  exact h3

lemma log_two_over_dyadicDelta (n : ℕ) :
    Real.log (2 / dyadicDelta n) = ((n : ℝ) + 1) * Real.log 2 := by
  have h₁ : 2 / dyadicDelta n = (2 : ℝ) ^ (n + 1) := by
    rw [dyadicDelta_eq_inv]
    field_simp
    <;> ring_nf
    <;> norm_cast
  rw [h₁]
  rw [Real.log_pow] <;> norm_num

lemma coarseRefinementFactor_pos (n m : ℕ) : 0 < coarseRefinementFactor n m := by
  unfold coarseRefinementFactor
  exact pow_pos (by norm_num) _

lemma dyadicDelta_ratio (n m : ℕ) (hnm : m ≤ n) :
    dyadicDelta n = dyadicDelta m / (coarseRefinementFactor n m : ℝ) := by
  have h₁ : (n : ℝ) = (m : ℝ) + ((n - m : ℕ) : ℝ) := by
    simp [Nat.cast_sub hnm] <;> ring
  simp only [dyadicDelta, coarseRefinementFactor]
  rw [h₁]
  simp [Real.rpow_add]
  <;> field_simp
  <;> ring

-- ============================================================================
-- Interval containment helper
-- ============================================================================

lemma Ico_subset_Ico_iff {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Set.Ico a b ⊆ Set.Ico c d ↔ c ≤ a ∧ b ≤ d := by
  constructor
  · intro h
    have ha : a ∈ Set.Ico a b := ⟨by linarith, by linarith⟩
    have h1 : c ≤ a := (h ha).1
    have h2 : b ≤ d := by
      by_contra h2
      have h3 : d < b := not_le.mp h2
      let x := max a d
      have hx1 : a ≤ x := le_max_left a d
      have hx2 : x < b := max_lt hab h3
      have hx_in : x ∈ Set.Ico a b := ⟨hx1, hx2⟩
      have hx_out : x ∉ Set.Ico c d := by
        intro h4
        have h5 : x < d := h4.2
        have h6 : d ≤ x := le_max_right a d
        linarith
      exact hx_out (h hx_in)
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩ x ⟨hxa, hxb⟩
    exact ⟨by linarith, by linarith⟩

-- ============================================================================
-- General tube set containment
-- ============================================================================

/-- Containment of general tube sets is equivalent to containment of both the
slope and intercept intervals. -/
lemma general_tube_containment_iff
    (s1 s2 i1 i2 s1' s2' i1' i2' : ℝ)
    (hs : s1 < s2) (hi : i1 < i2) (hs' : s1' < s2') (hi' : i1' < i2') :
    ({p : ℝ × ℝ | ∃ slope ∈ Set.Ico s1 s2, ∃ intercept ∈ Set.Ico i1 i2,
        p.2 = slope * p.1 + intercept} ⊆
     {p : ℝ × ℝ | ∃ slope ∈ Set.Ico s1' s2', ∃ intercept ∈ Set.Ico i1' i2',
        p.2 = slope * p.1 + intercept}) ↔
    Set.Ico s1 s2 ⊆ Set.Ico s1' s2' ∧ Set.Ico i1 i2 ⊆ Set.Ico i1' i2' := by
  constructor
  · -- Forward direction
    intro h
    -- Step 1: intercept interval containment
    have h_i : Set.Ico i1 i2 ⊆ Set.Ico i1' i2' := by
      intro y hy
      have hp : (0, y) ∈ {p : ℝ × ℝ | ∃ slope ∈ Set.Ico s1 s2, ∃ intercept ∈ Set.Ico i1 i2, p.2 = slope * p.1 + intercept} := by
        refine ⟨s1, ⟨by linarith, by linarith⟩, y, hy, by simp⟩
      have hq := h hp
      rcases hq with ⟨slope', hslope', intercept', hii', h_eq⟩
      have h_y : y = intercept' := by simpa using h_eq
      rw [h_y]
      exact hii'
    have h_i1 : i1' ≤ i1 := (Ico_subset_Ico_iff hi hi').mp h_i |>.1
    have h_i2 : i2 ≤ i2' := (Ico_subset_Ico_iff hi hi').mp h_i |>.2
    let b_T := i1
    have h_bT_ge : i1' ≤ b_T := h_i1
    have h_bT_lt : b_T < i2' := by linarith
    -- Step 2: slope interval containment
    have h_s : Set.Ico s1 s2 ⊆ Set.Ico s1' s2' := by
      apply (Ico_subset_Ico_iff hs hs').mpr
      constructor
      · -- Prove s1' ≤ s1
        by_contra h_case
        have h_s1_gt : s1 < s1' := by linarith
        set slope_s : ℝ := s1 with hslope_s
        have h_slope_in : slope_s ∈ Set.Ico s1 s2 := ⟨by linarith, by linarith⟩
        set d : ℝ := slope_s - s1' with hd
        have hd_neg : d < 0 := by linarith
        set x : ℝ := (i1' - b_T) / d + 1 with hx
        have hx_pos : 0 < x := by
          have h1 : i1' - b_T ≤ 0 := by linarith
          have h2 : (i1' - b_T) / d ≥ 0 := by
            apply div_nonneg_of_nonpos
            <;> linarith
          linarith
        have hx_ineq : b_T + d * x < i1' := by
          have h3 : d * x = (i1' - b_T) + d := by
            rw [hx]
            field_simp [hd_neg.ne] <;> ring
          linarith
        let p : ℝ × ℝ := (x, slope_s * x + b_T)
        have hp_in : p ∈ {p : ℝ × ℝ | ∃ slope ∈ Set.Ico s1 s2, ∃ intercept ∈ Set.Ico i1 i2, p.2 = slope * p.1 + intercept} := by
          refine ⟨slope_s, h_slope_in, b_T, ⟨by linarith, by linarith⟩, by simp [p]⟩
        have hq := h hp_in
        rcases hq with ⟨slope', hslope', intercept', hintercept', h_eq⟩
        have h_slope'_ge : s1' ≤ slope' := hslope'.1
        have h_intercept'_ge : i1' ≤ intercept' := hintercept'.1
        have h9 : intercept' = b_T + (slope_s - slope') * x := by
          simp [p] at h_eq ⊢ <;> linarith
        have h10 : slope_s - slope' ≤ d := by
          simp [hd] <;> linarith
        have h11 : intercept' ≤ b_T + d * x := by
          rw [h9]
          have h12 : (slope_s - slope') * x ≤ d * x := by
            exact mul_le_mul_of_nonneg_right h10 (by linarith)
          linarith
        linarith
      · -- Prove s2 ≤ s2'
        by_contra h_case
        have h_s2_gt : s2' < s2 := by linarith
        have h_exists_slope : ∃ (slope_s : ℝ), slope_s ∈ Set.Ico s1 s2 ∧ slope_s > s2' := by
          by_cases h : s1 ≤ s2'
          · use (s2' + s2) / 2
            constructor
            · exact ⟨by linarith, by linarith⟩
            · linarith
          · use s1
            constructor
            · exact ⟨by linarith, by linarith⟩
            · linarith
        rcases h_exists_slope with ⟨slope_s, hslope_in, hslope_gt⟩
        set d : ℝ := slope_s - s2' with hd
        have hd_pos : 0 < d := by linarith
        set x : ℝ := |(i2' - b_T) / d| + 1 with hx
        have hx_pos : 0 < x := by positivity
        have hx_ineq : b_T + d * x > i2' := by
          have h3 : x > (i2' - b_T) / d := by
            rw [hx]
            have h4 : |(i2' - b_T) / d| ≥ (i2' - b_T) / d := le_abs_self _
            linarith
          have h5 : d * x > i2' - b_T := by
            have h6 : x * d > i2' - b_T := by
              calc x * d
                > ((i2' - b_T) / d) * d := mul_lt_mul_of_pos_right h3 hd_pos
                _ = i2' - b_T := by field_simp [hd_pos.ne'] <;> ring
            have h7 : d * x = x * d := by ring
            rw [h7]
            exact h6
          linarith
        let p : ℝ × ℝ := (x, slope_s * x + b_T)
        have hp_in : p ∈ {p : ℝ × ℝ | ∃ slope ∈ Set.Ico s1 s2, ∃ intercept ∈ Set.Ico i1 i2, p.2 = slope * p.1 + intercept} := by
          refine ⟨slope_s, hslope_in, b_T, ⟨by linarith, by linarith⟩, by simp [p]⟩
        have hq := h hp_in
        rcases hq with ⟨slope', hslope', intercept', hintercept', h_eq⟩
        have h_slope'_lt : slope' < s2' := hslope'.2
        have h_intercept'_lt : intercept' < i2' := hintercept'.2
        have h9 : intercept' = b_T + (slope_s - slope') * x := by
          simp [p] at h_eq ⊢ <;> linarith
        have h10 : slope_s - slope' > d := by
          simp [hd] <;> linarith
        have h11 : intercept' > b_T + d * x := by
          rw [h9]
          have h12 : (slope_s - slope') * x > d * x := by
            exact mul_lt_mul_of_pos_right h10 hx_pos
          linarith
        linarith
    exact ⟨h_s, h_i⟩
  · -- Backward direction
    rintro ⟨h_s, h_i⟩ p hp
    rcases hp with ⟨slope, hslope, intercept, hintercept, h_eq⟩
    have hslope' : slope ∈ Set.Ico s1' s2' := h_s hslope
    have hintercept' : intercept ∈ Set.Ico i1' i2' := h_i hintercept
    exact ⟨slope, hslope', intercept, hintercept', h_eq⟩

-- ============================================================================
-- Coarse parent index specification
-- ============================================================================

/-- The coarse parent index `k` is the unique integer satisfying
`k * 2^(n-m) ≤ a < (k+1) * 2^(n-m)`. -/
theorem coarseParentIndex_spec (n m : ℕ) (hnm : m ≤ n) (a : ℤ) :
    let k := coarseParentIndex n m a
    let f := coarseRefinementFactor n m
    (k : ℤ) * (f : ℤ) ≤ a ∧ a < (k + 1) * (f : ℤ) := by
  dsimp only
  set k : ℤ := coarseParentIndex n m a with hk
  set f : ℕ := coarseRefinementFactor n m with hf
  have hf_pos' : (0 : ℝ) < (f : ℝ) := by
    exact_mod_cast coarseRefinementFactor_pos n m
  have h₁ : (k : ℝ) ≤ (a : ℝ) / (f : ℝ) := Int.floor_le _
  have h₂ : (a : ℝ) / (f : ℝ) < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have h_eq1 : ((a : ℝ) / (f : ℝ)) * (f : ℝ) = (a : ℝ) := by
    field_simp [hf_pos'.ne'] <;> ring
  have h₃ : (k : ℝ) * (f : ℝ) ≤ (a : ℝ) := by
    calc (k : ℝ) * (f : ℝ)
      ≤ ((a : ℝ) / (f : ℝ)) * (f : ℝ) := by gcongr
      _ = (a : ℝ) := h_eq1
  have h₄ : (a : ℝ) < ((k : ℝ) + 1) * (f : ℝ) := by
    calc (a : ℝ)
      = ((a : ℝ) / (f : ℝ)) * (f : ℝ) := h_eq1.symm
      _ < ((k : ℝ) + 1) * (f : ℝ) := by gcongr
  have h₅ : (k : ℤ) * (f : ℤ) ≤ a := by exact_mod_cast h₃
  have h₆ : a < (k + 1) * (f : ℤ) := by exact_mod_cast h₄
  exact ⟨h₅, h₆⟩

/-- The local slope cell index `k` satisfies
`k * 2^m ≤ a < (k+1) * 2^m`. -/
theorem localSlopeCellIndex_spec (m : ℕ) (a : ℤ) :
    let k := localSlopeCellIndex m a
    (k : ℤ) * (2 ^ m : ℤ) ≤ a ∧ a < (k + 1) * (2 ^ m : ℤ) := by
  dsimp only
  set k : ℤ := localSlopeCellIndex m a with hk
  have h_pos : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by positivity
  have h₁ : (k : ℝ) ≤ (a : ℝ) / ((2 ^ m : ℕ) : ℝ) := Int.floor_le _
  have h₂ : (a : ℝ) / ((2 ^ m : ℕ) : ℝ) < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have h_eq1 : ((a : ℝ) / ((2 ^ m : ℕ) : ℝ)) * ((2 ^ m : ℕ) : ℝ) = (a : ℝ) := by
    field_simp [h_pos.ne'] <;> ring
  have h₃ : (k : ℝ) * ((2 ^ m : ℕ) : ℝ) ≤ (a : ℝ) := by
    calc (k : ℝ) * ((2 ^ m : ℕ) : ℝ)
      ≤ ((a : ℝ) / ((2 ^ m : ℕ) : ℝ)) * ((2 ^ m : ℕ) : ℝ) := by gcongr
      _ = (a : ℝ) := h_eq1
  have h₄ : (a : ℝ) < ((k : ℝ) + 1) * ((2 ^ m : ℕ) : ℝ) := by
    calc (a : ℝ)
      = ((a : ℝ) / ((2 ^ m : ℕ) : ℝ)) * ((2 ^ m : ℕ) : ℝ) := h_eq1.symm
      _ < ((k : ℝ) + 1) * ((2 ^ m : ℕ) : ℝ) := by gcongr
  have h₅ : (k : ℤ) * (2 ^ m : ℤ) ≤ a := by exact_mod_cast h₃
  have h₆ : a < (k + 1) * (2 ^ m : ℤ) := by exact_mod_cast h₄
  exact ⟨h₅, h₆⟩

-- ============================================================================
-- Tube containment for dyadic tubes
-- ============================================================================

/-- A fine dyadic tube `T` at scale `n` is geometrically contained in a coarse
dyadic tube `U` at scale `m` (with `m ≤ n`) if and only if the slope and
intercept parameter intervals nest. -/
theorem tube_containment_iff {n m : ℕ} (hnm : m ≤ n)
    (T : DyadicTube n) (U : DyadicTube m) :
    T.toSet ⊆ U.toSet ↔
      (U.a : ℤ) * (coarseRefinementFactor n m : ℤ) ≤ T.a ∧
      T.a + 1 ≤ (U.a + 1) * (coarseRefinementFactor n m : ℤ) ∧
      (U.b : ℤ) * (coarseRefinementFactor n m : ℤ) ≤ T.b ∧
      T.b + 1 ≤ (U.b + 1) * (coarseRefinementFactor n m : ℤ) := by
  set f : ℕ := coarseRefinementFactor n m with hf
  set δn : ℝ := dyadicDelta n with hδn
  set δm : ℝ := dyadicDelta m with hδm
  have hf_pos : (0 : ℝ) < (f : ℝ) := by exact_mod_cast coarseRefinementFactor_pos n m
  have hδn_pos : 0 < δn := dyadicDelta_pos n
  have hδm_pos : 0 < δm := dyadicDelta_pos m
  have h_rel : δn = δm / (f : ℝ) := dyadicDelta_ratio n m hnm
  let s1 := (T.a : ℝ) * δn
  let s2 := (T.a + 1 : ℝ) * δn
  let i1 := (T.b : ℝ) * δn
  let i2 := (T.b + 1 : ℝ) * δn
  let s1' := (U.a : ℝ) * δm
  let s2' := (U.a + 1 : ℝ) * δm
  let i1' := (U.b : ℝ) * δm
  let i2' := (U.b + 1 : ℝ) * δm
  have hs : s1 < s2 := by simp [s1, s2, hδn_pos] <;> linarith
  have hi : i1 < i2 := by simp [i1, i2, hδn_pos] <;> linarith
  have hs' : s1' < s2' := by simp [s1', s2', hδm_pos] <;> linarith
  have hi' : i1' < i2' := by simp [i1', i2', hδm_pos] <;> linarith
  have h_main : T.toSet ⊆ U.toSet ↔
      Set.Ico s1 s2 ⊆ Set.Ico s1' s2' ∧ Set.Ico i1 i2 ⊆ Set.Ico i1' i2' :=
    general_tube_containment_iff s1 s2 i1 i2 s1' s2' i1' i2' hs hi hs' hi'
  rw [h_main]
  -- Helper: real interval containment ↔ integer inequalities
  have h_slope_conv : Set.Ico s1 s2 ⊆ Set.Ico s1' s2' ↔
      (U.a : ℤ) * (f : ℤ) ≤ T.a ∧ T.a + 1 ≤ (U.a + 1) * (f : ℤ) := by
    rw [Ico_subset_Ico_iff hs hs']
    constructor
    · rintro ⟨h1, h2⟩
      have h1a : (U.a : ℝ) * δm ≤ (T.a : ℝ) * δn := h1
      have h2a : (T.a + 1 : ℝ) * δn ≤ (U.a + 1 : ℝ) * δm := h2
      have h1b : (U.a : ℝ) * (f : ℝ) ≤ (T.a : ℝ) := by
        rw [h_rel] at h1a
        have h : (U.a : ℝ) * δm ≤ (T.a : ℝ) * (δm / (f : ℝ)) := h1a
        have h' : (U.a : ℝ) * (f : ℝ) ≤ (T.a : ℝ) := by
          calc (U.a : ℝ) * (f : ℝ)
            = ((U.a : ℝ) * δm) * (f : ℝ) / δm := by field_simp [hδm_pos.ne'] <;> ring
            _ ≤ ((T.a : ℝ) * (δm / (f : ℝ))) * (f : ℝ) / δm := by gcongr
            _ = (T.a : ℝ) := by field_simp [hδm_pos.ne', hf_pos.ne'] <;> ring
        exact h'
      have h2b : (T.a + 1 : ℝ) ≤ (U.a + 1 : ℝ) * (f : ℝ) := by
        rw [h_rel] at h2a
        have h : (T.a + 1 : ℝ) * (δm / (f : ℝ)) ≤ (U.a + 1 : ℝ) * δm := h2a
        have h' : (T.a + 1 : ℝ) ≤ (U.a + 1 : ℝ) * (f : ℝ) := by
          calc (T.a + 1 : ℝ)
            = ((T.a + 1 : ℝ) * (δm / (f : ℝ))) * (f : ℝ) / δm := by field_simp [hδm_pos.ne', hf_pos.ne'] <;> ring
            _ ≤ ((U.a + 1 : ℝ) * δm) * (f : ℝ) / δm := by gcongr
            _ = (U.a + 1 : ℝ) * (f : ℝ) := by field_simp [hδm_pos.ne'] <;> ring
        exact h'
      exact ⟨by exact_mod_cast h1b, by exact_mod_cast h2b⟩
    · rintro ⟨h1, h2⟩
      have h1b : (U.a : ℝ) * (f : ℝ) ≤ (T.a : ℝ) := by exact_mod_cast h1
      have h2b : (T.a + 1 : ℝ) ≤ (U.a + 1 : ℝ) * (f : ℝ) := by exact_mod_cast h2
      have h1a : (U.a : ℝ) * δm ≤ (T.a : ℝ) * δn := by
        rw [h_rel]
        calc (U.a : ℝ) * δm
          = ((U.a : ℝ) * (f : ℝ)) * (δm / (f : ℝ)) := by field_simp [hf_pos.ne'] <;> ring
          _ ≤ (T.a : ℝ) * (δm / (f : ℝ)) := by gcongr
      have h2a : (T.a + 1 : ℝ) * δn ≤ (U.a + 1 : ℝ) * δm := by
        rw [h_rel]
        calc (T.a + 1 : ℝ) * (δm / (f : ℝ))
          ≤ ((U.a + 1 : ℝ) * (f : ℝ)) * (δm / (f : ℝ)) := by gcongr
          _ = (U.a + 1 : ℝ) * δm := by field_simp [hf_pos.ne'] <;> ring
      exact ⟨h1a, h2a⟩
  have h_intercept_conv : Set.Ico i1 i2 ⊆ Set.Ico i1' i2' ↔
      (U.b : ℤ) * (f : ℤ) ≤ T.b ∧ T.b + 1 ≤ (U.b + 1) * (f : ℤ) := by
    rw [Ico_subset_Ico_iff hi hi']
    constructor
    · rintro ⟨h1, h2⟩
      have h1a : (U.b : ℝ) * δm ≤ (T.b : ℝ) * δn := h1
      have h2a : (T.b + 1 : ℝ) * δn ≤ (U.b + 1 : ℝ) * δm := h2
      have h1b : (U.b : ℝ) * (f : ℝ) ≤ (T.b : ℝ) := by
        rw [h_rel] at h1a
        have h' : (U.b : ℝ) * (f : ℝ) ≤ (T.b : ℝ) := by
          calc (U.b : ℝ) * (f : ℝ)
            = ((U.b : ℝ) * δm) * (f : ℝ) / δm := by field_simp [hδm_pos.ne'] <;> ring
            _ ≤ ((T.b : ℝ) * (δm / (f : ℝ))) * (f : ℝ) / δm := by gcongr
            _ = (T.b : ℝ) := by field_simp [hδm_pos.ne', hf_pos.ne'] <;> ring
        exact h'
      have h2b : (T.b + 1 : ℝ) ≤ (U.b + 1 : ℝ) * (f : ℝ) := by
        rw [h_rel] at h2a
        have h' : (T.b + 1 : ℝ) ≤ (U.b + 1 : ℝ) * (f : ℝ) := by
          calc (T.b + 1 : ℝ)
            = ((T.b + 1 : ℝ) * (δm / (f : ℝ))) * (f : ℝ) / δm := by field_simp [hδm_pos.ne', hf_pos.ne'] <;> ring
            _ ≤ ((U.b + 1 : ℝ) * δm) * (f : ℝ) / δm := by gcongr
            _ = (U.b + 1 : ℝ) * (f : ℝ) := by field_simp [hδm_pos.ne'] <;> ring
        exact h'
      exact ⟨by exact_mod_cast h1b, by exact_mod_cast h2b⟩
    · rintro ⟨h1, h2⟩
      have h1b : (U.b : ℝ) * (f : ℝ) ≤ (T.b : ℝ) := by exact_mod_cast h1
      have h2b : (T.b + 1 : ℝ) ≤ (U.b + 1 : ℝ) * (f : ℝ) := by exact_mod_cast h2
      have h1a : (U.b : ℝ) * δm ≤ (T.b : ℝ) * δn := by
        rw [h_rel]
        calc (U.b : ℝ) * δm
          = ((U.b : ℝ) * (f : ℝ)) * (δm / (f : ℝ)) := by field_simp [hf_pos.ne'] <;> ring
          _ ≤ (T.b : ℝ) * (δm / (f : ℝ)) := by gcongr
      have h2a : (T.b + 1 : ℝ) * δn ≤ (U.b + 1 : ℝ) * δm := by
        rw [h_rel]
        calc (T.b + 1 : ℝ) * (δm / (f : ℝ))
          ≤ ((U.b + 1 : ℝ) * (f : ℝ)) * (δm / (f : ℝ)) := by gcongr
          _ = (U.b + 1 : ℝ) * δm := by field_simp [hf_pos.ne'] <;> ring
      exact ⟨h1a, h2a⟩
  rw [h_slope_conv, h_intercept_conv]
  <;> aesop

-- ============================================================================
-- Containing square property
-- ============================================================================

/-- The `containingSquare` of a fine dyadic square `p` is the unique coarse
dyadic square that contains `p`. -/
theorem containingSquare_is_containing {n m : ℕ} (hnm : m ≤ n)
    (p : DyadicSquare n) :
    squareContained hnm p (containingSquare hnm p) := by
  set Q : DyadicSquare m := containingSquare hnm p with hQ
  have h1 := coarseParentIndex_spec n m hnm p.i
  have h2 := coarseParentIndex_spec n m hnm p.j
  dsimp only [Q, containingSquare, squareContained] at *
  <;> exact ⟨h1.1, h1.2, h2.1, h2.2⟩

-- ============================================================================
-- IsFiniteTubeSSet properties
-- ============================================================================

/-- Monotonicity of `IsFiniteTubeSSet` in the constant `C`. -/
lemma IsFiniteTubeSSet.scale_C {n : ℕ} {s C C' : ℝ} {F : Finset (DyadicTube n)}
    (h : IsFiniteTubeSSet s C F) (hCC' : C ≤ C') :
    IsFiniteTubeSSet s C' F := by
  rcases h with ⟨hne, hC, hs, hsep, hcard⟩
  refine ⟨hne, by linarith, hs, hsep, fun center r hr => ?_⟩
  have h₁ := hcard center r hr
  have h_rpos : 0 < r := (dyadicDelta_pos n).trans_le hr
  have hrp : 0 ≤ Real.rpow r s := Real.rpow_nonneg (by linarith) s
  have hfc : 0 ≤ (F.card : ℝ) := by positivity
  have h₂ : C * Real.rpow r s * (F.card : ℝ) ≤ C' * Real.rpow r s * (F.card : ℝ) := by
    nlinarith
  exact h₁.trans h₂

/-- If `G ⊆ F` and `F` is an SSet with constant `C`, and `|F| ≤ K * |G|`,
then `G` is an SSet with constant `C * K`. This is the correct subset property;
plain `G ⊆ F → IsFiniteTubeSSet s C G` is false because the denominator shrinks. -/
lemma IsFiniteTubeSSet.subset_with_loss {n : ℕ} {s C K : ℝ}
    {F G : Finset (DyadicTube n)}
    (h : IsFiniteTubeSSet s C F) (hG : G ⊆ F) (hGnonempty : G.Nonempty)
    (hK : (F.card : ℝ) ≤ K * (G.card : ℝ)) :
    IsFiniteTubeSSet s (C * K) G := by
  rcases h with ⟨hne, hC, hs, hsep, hcard⟩
  have hGpos : 0 < (G.card : ℝ) := by exact_mod_cast hGnonempty.card_pos
  have hKone : 1 ≤ K := by
    have h₁ : (G.card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast Finset.card_le_card hG
    have h₂ : (G.card : ℝ) ≤ K * (G.card : ℝ) := h₁.trans hK
    have h₃ : 1 ≤ K := by
      nlinarith
    exact h₃
  have hCK : 1 ≤ C * K := by
    have h₄ : 1 ≤ C := hC
    nlinarith
  refine ⟨hGnonempty, hCK, hs, ?_, ?_⟩
  · -- Separation condition
    intro T hT U hU hne
    exact hsep T (hG hT) U (hG hU) hne
  · -- Cardinality bound
    intro center r hr
    have hfilter : (G.filter fun T => tubeParamDist T center ≤ r) ⊆
        (F.filter fun T => tubeParamDist T center ≤ r) := by
      intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hG hx.1, hx.2⟩
    have h₁ : ((G.filter fun T => tubeParamDist T center ≤ r).card : ℝ) ≤
        ((F.filter fun T => tubeParamDist T center ≤ r).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hfilter
    have h₂ := hcard center r hr
    have h₃ : ((F.filter fun T => tubeParamDist T center ≤ r).card : ℝ) ≤
        C * Real.rpow r s * (F.card : ℝ) := h₂
    have h₄ : (F.card : ℝ) ≤ K * (G.card : ℝ) := hK
    calc ((G.filter fun T => tubeParamDist T center ≤ r).card : ℝ)
      ≤ ((F.filter fun T => tubeParamDist T center ≤ r).card : ℝ) := h₁
      _ ≤ C * Real.rpow r s * (F.card : ℝ) := h₃
      _ ≤ C * Real.rpow r s * (K * (G.card : ℝ)) := by
        have h_rpos : 0 < r := (dyadicDelta_pos n).trans_le hr
        have h₅ : 0 ≤ C * Real.rpow r s := by
          have h₆ : 0 ≤ Real.rpow r s := Real.rpow_nonneg (by linarith) s
          positivity
        exact mul_le_mul_of_nonneg_left h₄ h₅
      _ = (C * K) * Real.rpow r s * (G.card : ℝ) := by ring

end InductionOnScales
