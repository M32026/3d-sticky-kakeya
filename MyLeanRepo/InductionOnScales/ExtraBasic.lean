module

/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Induction on Scales Team
-/
public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Extra arithmetic and utility lemmas

Additional lemmas not in Basic.lean but useful for the induction proof.
-/

namespace InductionOnScales

section ExtraArithmetic

/-- `dyadicDelta n ≤ 1`. -/
lemma dyadicDelta_le_one (n : ℕ) : dyadicDelta n ≤ 1 := by
  rw [dyadicDelta_eq_inv]
  have h : (1 : ℝ) ≤ (2 ^ n : ℝ) := by
    have h2 : ∀ k : ℕ, (1 : ℝ) ≤ (2 ^ k : ℝ) := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih => simp [pow_succ] at * <;> linarith
    exact h2 n
  have h' : (1 : ℝ) / (2 ^ n : ℝ) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact h
  exact h'

/-- For `m ≤ n`, `dyadicDelta (n - m) = dyadicDelta n / dyadicDelta m`. -/
lemma dyadicDelta_relative_eq (n m : ℕ) (hnm : m ≤ n) :
    dyadicDelta (n - m) = dyadicDelta n / dyadicDelta m := by
  rw [dyadicDelta_eq_inv, dyadicDelta_eq_inv, dyadicDelta_eq_inv]
  have h2 : m + (n - m) = n := by omega
  have h3 : (2 ^ n : ℝ) = (2 ^ m : ℝ) * (2 ^ (n - m) : ℝ) := by
    have h4 : (2 ^ (m + (n - m)) : ℝ) = (2 ^ m : ℝ) * (2 ^ (n - m) : ℝ) := by
      rw [pow_add] <;> ring
    have h5 : m + (n - m) = n := h2
    rw [h5] at h4
    exact h4
  field_simp
  <;> rw [h3] <;> ring

/-- For `0 ≤ r ≤ 1` and `0 ≤ s ≤ 1`, `r ≤ r ^ s`. -/
lemma le_rpow_of_le_one {r s : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) : r ≤ r ^ s := by
  by_cases h0 : r = 0
  · subst h0
    by_cases hs0 : s = 0
    · simp [hs0]
    · have hs_pos : 0 < s := by
        apply lt_of_le_of_ne hs
        intro h
        exact hs0 h.symm
      simp [hs_pos.ne']
  · have hr_pos : 0 < r := by
      apply lt_of_le_of_ne hr
      intro h
      exact h0 h.symm
    have h_log_nonpos : Real.log r ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    have h_ineq : Real.log r ≤ s * Real.log r := by
      have h : (1 : ℝ) - s ≥ 0 := by linarith
      have h2 : (1 - s) * Real.log r ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos h h_log_nonpos
      linarith
    have h_log_rpow : Real.log (r ^ s) = s * Real.log r := Real.log_rpow hr_pos s
    have h4 : Real.log r ≤ Real.log (r ^ s) := by
      rw [h_log_rpow]
      exact h_ineq
    have h5 : r ≤ r ^ s := by
      exact (Real.log_le_log_iff (by linarith) (by positivity)).mp h4
    exact h5

/-- `coarseParentIndex` is the unique integer satisfying the nesting. -/
lemma coarseParentIndex_unique (n m : ℕ) (hnm : m ≤ n) (a k : ℤ) :
    k * (coarseRefinementFactor n m : ℤ) ≤ a →
    a < (k + 1) * (coarseRefinementFactor n m : ℤ) →
    coarseParentIndex n m a = k := by
  intro h1 h2
  let d := coarseRefinementFactor n m
  have hd_pos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast coarseRefinementFactor_pos n m
  have h1' : (k : ℝ) ≤ (a : ℝ) / (d : ℝ) := by
    have h : (k : ℝ) * (d : ℝ) ≤ (a : ℝ) := by exact_mod_cast h1
    have h' : (k : ℝ) = (k : ℝ) * (d : ℝ) / (d : ℝ) := by
      field_simp [hd_pos.ne'] <;> ring
    rw [h']
    gcongr
  have h2' : (a : ℝ) / (d : ℝ) < (k : ℝ) + 1 := by
    have h : (a : ℝ) < ((k : ℝ) + 1) * (d : ℝ) := by exact_mod_cast h2
    have h' : ((k : ℝ) + 1) * (d : ℝ) / (d : ℝ) = (k : ℝ) + 1 := by
      field_simp [hd_pos.ne'] <;> ring
    calc
      (a : ℝ) / (d : ℝ) < (((k : ℝ) + 1) * (d : ℝ)) / (d : ℝ) := by gcongr
      _ = (k : ℝ) + 1 := h'
  have h3 : ⌊(a : ℝ) / (d : ℝ)⌋ = k := by
    rw [Int.floor_eq_iff]
    exact ⟨h1', h2'⟩
  exact h3

/-- `localSlopeCellIndex` is the unique integer satisfying the nesting. -/
lemma localSlopeCellIndex_unique (m : ℕ) (a k : ℤ) :
    k * (2 ^ m : ℤ) ≤ a →
    a < (k + 1) * (2 ^ m : ℤ) →
    localSlopeCellIndex m a = k := by
  intro h1 h2
  let d : ℕ := 2 ^ m
  have hd_pos : (0 : ℝ) < (d : ℝ) := by positivity
  have h1' : (k : ℝ) ≤ (a : ℝ) / (d : ℝ) := by
    have h : (k : ℝ) * (d : ℝ) ≤ (a : ℝ) := by exact_mod_cast h1
    have h' : (k : ℝ) = (k : ℝ) * (d : ℝ) / (d : ℝ) := by
      field_simp [hd_pos.ne'] <;> ring
    rw [h']
    gcongr
  have h2' : (a : ℝ) / (d : ℝ) < (k : ℝ) + 1 := by
    have h : (a : ℝ) < ((k : ℝ) + 1) * (d : ℝ) := by exact_mod_cast h2
    have h' : ((k : ℝ) + 1) * (d : ℝ) / (d : ℝ) = (k : ℝ) + 1 := by
      field_simp [hd_pos.ne'] <;> ring
    calc
      (a : ℝ) / (d : ℝ) < (((k : ℝ) + 1) * (d : ℝ)) / (d : ℝ) := by gcongr
      _ = (k : ℝ) + 1 := h'
  have h3 : ⌊(a : ℝ) / (d : ℝ)⌋ = k := by
    rw [Int.floor_eq_iff]
    exact ⟨h1', h2'⟩
  exact h3

end ExtraArithmetic

section CoarseAnc

/-- A fine tube is geometrically contained in its coarse ancestor. -/
lemma coarseAnc_contains {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n) :
    T.toSet ⊆ (deprecatedCoordinatewiseAncestor hnm T).toSet := by
  let U := deprecatedCoordinatewiseAncestor hnm T
  let f := coarseRefinementFactor n m
  have hfa : (U.a : ℤ) * (f : ℤ) ≤ T.a ∧ T.a < (U.a + 1) * (f : ℤ) :=
    coarseParentIndex_spec n m hnm T.a
  have hfb : (U.b : ℤ) * (f : ℤ) ≤ T.b ∧ T.b < (U.b + 1) * (f : ℤ) :=
    coarseParentIndex_spec n m hnm T.b
  have h1 : (U.a : ℤ) * (f : ℤ) ≤ T.a := hfa.1
  have h2 : T.a + 1 ≤ (U.a + 1) * (f : ℤ) := by linarith
  have h3 : (U.b : ℤ) * (f : ℤ) ≤ T.b := hfb.1
  have h4 : T.b + 1 ≤ (U.b + 1) * (f : ℤ) := by linarith
  exact (tube_containment_iff hnm T U).mpr ⟨h1, h2, h3, h4⟩

end CoarseAnc

end InductionOnScales
