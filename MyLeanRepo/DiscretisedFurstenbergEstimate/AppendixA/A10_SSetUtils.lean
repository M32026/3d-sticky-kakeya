module

/-
  Auxiliary S-set lemmas for A10 correct construction.

  - IsDeltaSSet.weaken_exponent: reduce exponent s to s' ≤ s (constant inflation)
  - IsDeltaSSet.translation_real: translation on ℝ preserves S-set
  - IsDeltaSSet.finite_union_simple: finite union with card*C constant

  Whiteprint node: appendix_a_alternative / a10_product_witness
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.A10

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CoveringUtils

/-! ### Exponent weakening -/

/-- Weaken the exponent of an S-set: if A is a (δ,s,C)-set and s' ≤ s,
then A is a (δ,s',C')-set for any C' ≥ max(C,1).

For r ∈ [δ,1]: r^s ≤ r^s' (base ≤ 1, larger exponent gives smaller value).
For r > 1: N_δ(A ∩ B(x,r)) ≤ N_δ(A) ≤ C' * r^s' * N_δ(A) since C' ≥ 1 and r^s' ≥ 1. -/
lemma IsDeltaSSet.weaken_exponent {X : Type*} [PseudoMetricSpace X]
    {δ s s' C C' : ℝ} {A : Set X}
    (h : IsDeltaSSet δ s C A)
    (hs' : 0 ≤ s') (h_le : s' ≤ s)
    (hC_le : C ≤ C') (h_one_le : 1 ≤ C') :
    IsDeltaSSet δ s' C' A := by
  rcases h with ⟨hne, hδ_pos, hC_pos, hs, hmain⟩
  have hC'_pos : 0 < C' := by linarith
  refine ⟨hne, hδ_pos, hC'_pos, hs', fun x r hr => ?_⟩
  by_cases h_r_le_one : r ≤ 1
  · -- Case r ≤ 1: r^s ≤ r^s' since s' ≤ s and 0 ≤ r ≤ 1
    have h_ofReal_le_one : ENNReal.ofReal r ≤ 1 :=
      ENNReal.ofReal_le_one.mpr h_r_le_one
    have h1 : (ENNReal.ofReal r) ^ s ≤ (ENNReal.ofReal r) ^ s' :=
      ENNReal.rpow_le_rpow_of_exponent_ge h_ofReal_le_one h_le
    have h_main' := hmain x r hr
    have hC_le' : ENNReal.ofReal C ≤ ENNReal.ofReal C' :=
      ENNReal.ofReal_le_ofReal hC_le
    calc (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) : ENNReal)
        ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := h_main'
      _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s' *
            (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
        gcongr
        <;> exact h1
  · -- Case r > 1: covering ≤ N_δ(A), and C' * r^s' ≥ 1
    have h_r_gt_one : 1 < r := by linarith
    have h_sub : A ∩ Metric.closedBall x r ⊆ A := by simp
    have h2 : (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h_sub
    have h4 : 1 ≤ r ^ s' := by
      have h5 : (0 : ℝ) ≤ 1 := by norm_num
      have h6 : (1 : ℝ) ≤ r := by linarith
      have h7 : (1 : ℝ) ^ s' ≤ r ^ s' := Real.rpow_le_rpow h5 h6 hs'
      have h8 : (1 : ℝ) ^ s' = 1 := by simp
      rw [h8] at h7
      exact h7
    have h3 : 1 ≤ C' * r ^ s' := by
      have h7 : 1 ≤ C' := h_one_le
      nlinarith
    have h_ofReal_mul : ENNReal.ofReal (C' * r ^ s') =
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s' := by
      have h_pos1 : 0 ≤ C' := by linarith
      have h_pos2 : 0 ≤ r := by linarith
      have h9 : ENNReal.ofReal (C' * r ^ s') =
          ENNReal.ofReal C' * ENNReal.ofReal (r ^ s') := by
        rw [ENNReal.ofReal_mul h_pos1]
      rw [h9]
      have h10 : ENNReal.ofReal (r ^ s') = (ENNReal.ofReal r) ^ s' := by
        exact Eq.symm (ENNReal.ofReal_rpow_of_nonneg h_pos2 hs')
      rw [h10]
    have h5 : (1 : ENNReal) ≤ ENNReal.ofReal (C' * r ^ s') := by
      have h6 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (C' * r ^ s') := ENNReal.ofReal_le_ofReal h3
      simpa using h6
    have h6 : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s' *
          (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
      rw [←h_ofReal_mul]
      calc (Metric.externalCoveringNumber δ.toNNReal A : ENNReal)
          = 1 * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by ring
        _ ≤ ENNReal.ofReal (C' * r ^ s') * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
          gcongr
          <;> exact h5
    exact le_trans h2 h6

/-! ### Translation on ℝ -/

/-- Translation preserves S-set exactly on ℝ. -/
lemma IsDeltaSSet.translation_real {δ s C : ℝ} {P : Set ℝ} {c : ℝ}
    (h : IsDeltaSSet δ s C P) :
    IsDeltaSSet δ s C ((fun x : ℝ => x + c) '' P) := by
  let e : ℝ ≃ᵢ ℝ :=
    { toFun := fun x => x + c
      invFun := fun y => y - c
      left_inv := by intro x; simp <;> ring
      right_inv := by intro y; simp <;> ring
      isometry_toFun := by intro x y; simp [Real.dist_eq] <;> ring }
  have hcov : ∀ (A : Set ℝ), Metric.externalCoveringNumber δ.toNNReal (e '' A) =
      Metric.externalCoveringNumber δ.toNNReal A := by
    intro A
    exact externalCoveringNumber_image_isometryEquiv e (A := A)
  refine' ⟨h.1.image e, h.2.1, h.2.2.1, h.2.2.2.1, _⟩
  intro x r hr
  let y : ℝ := x - c
  have h_set : e '' P ∩ Metric.closedBall x r = e '' (P ∩ Metric.closedBall y r) := by
    ext z
    simp only [Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨a, haP, rfl⟩, hball⟩
      have hball' : dist (e a) x ≤ r := by simpa [Metric.mem_closedBall] using hball
      have h_ball2 : dist a y ≤ r := by
        have h_dist : dist (e a) x = dist a y := by simp [e, y, Real.dist_eq] <;> ring
        rw [h_dist] at hball'
        exact hball'
      exact ⟨a, ⟨haP, h_ball2⟩, rfl⟩
    · rintro ⟨a, ⟨haP, ha2⟩, rfl⟩
      have h_dist : dist (e a) x = dist a y := by simp [e, y, Real.dist_eq] <;> ring
      have h2 : dist a y ≤ r := by simpa [Metric.mem_closedBall] using ha2
      have h_ball : dist (e a) x ≤ r := by
        calc dist (e a) x = dist a y := h_dist
          _ ≤ r := h2
      exact ⟨⟨a, haP, rfl⟩, by simpa [Metric.mem_closedBall] using h_ball⟩
  have h_goal : (Metric.externalCoveringNumber δ.toNNReal (e '' P ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal (e '' P) : ENNReal) := by
    rw [h_set]
    have h2 := hcov (P ∩ Metric.closedBall y r)
    rw [h2]
    have h3 := h.2.2.2.2 y r hr
    have h4 := hcov P
    have h5 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) =
        (Metric.externalCoveringNumber δ.toNNReal (e '' P) : ENNReal) := by
      exact_mod_cast h4.symm
    rw [h5] at h3
    exact h3
  exact h_goal

end DirecretisedFurstenbergEstimate.A10
