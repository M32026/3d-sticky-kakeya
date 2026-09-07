import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Small-scale budget for WZ1 Corollary 26

This module combines the finitely many power-smallness conditions used by the
anchored-hierarchy assembly.
-/

namespace Kakeya.Assouad

/-- A positive power is eventually below any fixed constant in `(0, 1)`. -/
lemma exists_delta_rpow_le_single
    (epsilon C : ℝ) (heps : 0 < epsilon) (hC : 0 < C) (hC_one : C < 1) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        Real.rpow delta epsilon ≤ C := by
  let bound : ℝ := Real.rpow C (1 / epsilon)
  have hbound_pos : 0 < bound :=
    Real.rpow_pos_of_pos hC (1 / epsilon)
  have h_rpow : Real.rpow bound epsilon = C := by
    have hC_nonneg : 0 ≤ C := hC.le
    have h_mul1 :
        C ^ ((1 / epsilon) * epsilon) =
          (C ^ (1 / epsilon)) ^ epsilon :=
      Real.rpow_mul hC_nonneg (1 / epsilon) epsilon
    have h_eq1 :
        (C ^ (1 / epsilon)) ^ epsilon =
          C ^ ((1 / epsilon) * epsilon) :=
      h_mul1.symm
    have h_mul2 : (1 / epsilon) * epsilon = 1 := by
      field_simp [heps.ne']
    calc
      (C ^ (1 / epsilon)) ^ epsilon
          = C ^ ((1 / epsilon) * epsilon) := h_eq1
      _ = C := by rw [h_mul2]; simp
  let delta₀ : ℝ := min bound 1
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_one : delta₀ ≤ 1 := min_le_right _ _
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta_pos hdelta_le
  have h_le : delta ≤ bound :=
    hdelta_le.trans (min_le_left _ _)
  have h :
      Real.rpow delta epsilon ≤ Real.rpow bound epsilon :=
    Real.rpow_le_rpow hdelta_pos.le h_le heps.le
  rw [h_rpow] at h
  exact h

/-- The four simultaneous small-scale inequalities used by the hierarchy
assembly. -/
lemma wz1_anchored_hierarchy_delta_exists
    (N : ℕ) (hN_pos : 0 < N)
    (hierarchyLoss transferExp : ℝ)
    (hh : 0 < hierarchyLoss)
    (htransfer : 0 < transferExp) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        Real.rpow delta (hierarchyLoss / (N : ℝ)) < 1 / 9 ∧
        Real.rpow delta
            (299 * hierarchyLoss / (400 * (N : ℝ))) ≤
          1 / 648 ∧
        Real.rpow delta
            (3 * hierarchyLoss / (4 * (N : ℝ))) ≤
          1 / 12 ∧
        Real.rpow delta transferExp ≤ 2 / 3 := by
  have hN_pos' : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN_pos
  have he1 : 0 < hierarchyLoss / (N : ℝ) := by positivity
  have he2 :
      0 < 299 * hierarchyLoss / (400 * (N : ℝ)) := by
    positivity
  have he3 :
      0 < 3 * hierarchyLoss / (4 * (N : ℝ)) := by
    positivity
  rcases
      exists_delta_rpow_le_single
        (hierarchyLoss / (N : ℝ)) (1 / 10)
        he1 (by norm_num) (by norm_num) with
    ⟨d1, hd1_pos, hd1_one, h1⟩
  rcases
      exists_delta_rpow_le_single
        (299 * hierarchyLoss / (400 * (N : ℝ))) (1 / 648)
        he2 (by norm_num) (by norm_num) with
    ⟨d2, hd2_pos, hd2_one, h2⟩
  rcases
      exists_delta_rpow_le_single
        (3 * hierarchyLoss / (4 * (N : ℝ))) (1 / 12)
        he3 (by norm_num) (by norm_num) with
    ⟨d3, hd3_pos, hd3_one, h3⟩
  rcases
      exists_delta_rpow_le_single
        transferExp (2 / 3)
        htransfer (by norm_num) (by norm_num) with
    ⟨d4, hd4_pos, hd4_one, h4⟩
  let delta₀ := min (min (min d1 d2) d3) d4
  have hpos : 0 < delta₀ := by positivity
  have hone : delta₀ ≤ 1 :=
    (min_le_left _ _).trans
      ((min_le_left _ _).trans
        ((min_le_left _ _).trans hd1_one))
  refine ⟨delta₀, hpos, hone, ?_⟩
  intro delta hdelta_pos hdelta_le
  have h_le123 : delta ≤ min (min d1 d2) d3 :=
    hdelta_le.trans (min_le_left _ _)
  have h_le12 : delta ≤ min d1 d2 :=
    h_le123.trans (min_le_left _ _)
  have h_le1 : delta ≤ d1 :=
    h_le12.trans (min_le_left _ _)
  have h_le2 : delta ≤ d2 :=
    h_le12.trans (min_le_right _ _)
  have h_le3 : delta ≤ d3 :=
    h_le123.trans (min_le_right _ _)
  have h_le4 : delta ≤ d4 :=
    hdelta_le.trans (min_le_right _ _)
  have h_cond1 :
      Real.rpow delta (hierarchyLoss / (N : ℝ)) ≤ 1 / 10 :=
    h1 delta hdelta_pos h_le1
  exact
    ⟨h_cond1.trans_lt (by norm_num),
      h2 delta hdelta_pos h_le2,
      h3 delta hdelta_pos h_le3,
      h4 delta hdelta_pos h_le4⟩

end Kakeya.Assouad
