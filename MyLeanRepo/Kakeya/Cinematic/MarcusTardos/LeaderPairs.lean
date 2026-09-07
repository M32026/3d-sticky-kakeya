import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lemma 5: Upper bound on S^{ij} via leader pairs

Abstract version: takes the leader pair structure as assumptions and
proves the Cauchy-Schwarz bound.
-/

namespace MarcusTardos.LeaderPairs

open BigOperators Finset

variable {β : Type*} [DecidableEq β]

/--
Cauchy-Schwarz lower bound on the weighted sum of squares.

Given leader pairs with levels and intersection sizes r, proves:
  ∑ w_{level x} * r x^2 ≥ p^2 / ((K : ℝ) * V)
where V = ∑ 1/w_l and at most 4 leaders per level.
-/
lemma leader_cauchy_schwarz (K : ℕ) (hK_pos : 0 < K) (k : ℕ) (w : ℕ → ℝ)
    (hw_pos : ∀ l ∈ Icc 1 k, 0 < w l)
    (Leader : Finset β)
    (level : β → ℕ) (hlevel : ∀ x ∈ Leader, level x ∈ Icc 1 k)
    (r : β → ℝ) (hr_nonneg : ∀ x ∈ Leader, 0 ≤ r x)
    (p : ℝ) (hp_nonneg : 0 ≤ p)
    (h_sum_r : ∑ x ∈ Leader, r x = p)
    (h_at_most_K : ∀ l ∈ Icc 1 k, (Leader.filter (fun x => level x = l)).card ≤ K) :
    ∑ x ∈ Leader, w (level x) * (r x)^2 ≥ p^2 / ((K : ℝ) * ∑ l ∈ Icc 1 k, 1 / w l) := by
  let V := ∑ l ∈ Icc 1 k, 1 / w l
  have hV_nonneg : 0 ≤ V := by
    dsimp only [V]
    apply sum_nonneg
    intro l hl
    have h : 0 < w l := hw_pos l hl
    exact div_nonneg zero_le_one h.le
  let f (x : β) : ℝ := w (level x) * (r x)^2
  let g (x : β) : ℝ := 1 / w (level x)
  have hf_nonneg : ∀ x ∈ Leader, 0 ≤ f x := by
    intro x hx
    have hwl_pos : 0 < w (level x) := hw_pos (level x) (hlevel x hx)
    exact mul_nonneg hwl_pos.le (sq_nonneg (r x))
  have hg_nonneg : ∀ x ∈ Leader, 0 ≤ g x := by
    intro x hx
    have hwl_pos : 0 < w (level x) := hw_pos (level x) (hlevel x hx)
    exact div_nonneg zero_le_one hwl_pos.le
  have h_eq : ∀ x ∈ Leader, (r x)^2 = f x * g x := by
    intro x hx
    dsimp only [f, g]
    have hwl_pos : 0 < w (level x) := hw_pos (level x) (hlevel x hx)
    field_simp [hwl_pos.ne'] <;> ring
  -- Cauchy-Schwarz
  have h_cs : (∑ x ∈ Leader, r x)^2 ≤
      (∑ x ∈ Leader, f x) * (∑ x ∈ Leader, g x) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Leader hf_nonneg hg_nonneg
      (fun x hx => (h_eq x hx).le)
  -- Bound ∑_{leaders} 1/w_{level x} ≤ (K : ℝ) * V
  let fiber (l : ℕ) : Finset β := Leader.filter (fun x => level x = l)
  have h_disj : Set.PairwiseDisjoint (↑(Icc 1 k)) fiber := by
    intro l1 hl1 l2 hl2 hne
    have h_goal : Disjoint (fiber l1) (fiber l2) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 : level x = l1 := (Finset.mem_filter.mp hx1).2
      have h2 : level x = l2 := (Finset.mem_filter.mp hx2).2
      have h3 : l1 = l2 := by linarith
      exact hne h3
    simpa [Function.onFun] using h_goal
  have h_union : (Icc 1 k).biUnion fiber = Leader := by
    ext x
    have h_iff : x ∈ (Icc 1 k).biUnion fiber ↔ ∃ l ∈ Icc 1 k, x ∈ fiber l :=
      Finset.mem_biUnion
    rw [h_iff]
    constructor
    · rintro ⟨l, hl, hx⟩
      exact (Finset.mem_filter.mp hx).1
    · intro hx
      refine ⟨level x, hlevel x hx, ?_⟩
      exact Finset.mem_filter.mpr ⟨hx, rfl⟩
  have h3 : ∑ x ∈ Leader, g x =
      ∑ l ∈ Icc 1 k, ∑ x ∈ fiber l, g x := by
    have h_sum : ∑ x ∈ (Icc 1 k).biUnion fiber, g x =
        ∑ l ∈ Icc 1 k, ∑ x ∈ fiber l, g x :=
      Finset.sum_biUnion h_disj
    have h : ∑ x ∈ (Icc 1 k).biUnion fiber, g x = ∑ x ∈ Leader, g x := by
      rw [h_union]
    rw [← h]
    exact h_sum
  have h4 : ∑ l ∈ Icc 1 k, ∑ x ∈ fiber l, g x ≤
      ∑ l ∈ Icc 1 k, (K : ℝ) * (1 / w l) := by
    apply sum_le_sum
    intro l hl
    have h5 : (fiber l).card ≤ K := h_at_most_K l hl
    have h6 : ∑ x ∈ fiber l, g x =
        (fiber l).card * (1 / w l) := by
      have h7 : ∀ x ∈ fiber l, g x = 1 / w l := by
        intro x hx
        have h8 : level x = l := (Finset.mem_filter.mp hx).2
        dsimp only [g]
        rw [h8]
      rw [Finset.sum_congr rfl h7, Finset.sum_const]
      <;> ring
    rw [h6]
    have h9 : 0 ≤ 1 / w l := by
      have h10 : 0 < w l := hw_pos l hl
      exact div_nonneg zero_le_one h10.le
    have h5' : ((fiber l).card : ℝ) ≤ (K : ℝ) := by exact_mod_cast h5
    exact mul_le_mul_of_nonneg_right h5' h9
  have h5 : ∑ l ∈ Icc 1 k, (K : ℝ) * (1 / w l) = (K : ℝ) * V := by
    dsimp only [V]
    rw [Finset.mul_sum]
    <;> rfl
  have h_bound : ∑ x ∈ Leader, g x ≤ (K : ℝ) * V := by
    rw [h3]
    have h4' : ∑ l ∈ Icc 1 k, ∑ x ∈ fiber l, g x ≤ ∑ l ∈ Icc 1 k, (K : ℝ) * (1 / w l) := h4
    rw [h5] at h4'
    exact h4'
  rw [h_sum_r] at h_cs
  have h6 : 0 ≤ ∑ x ∈ Leader, f x := by
    exact sum_nonneg hf_nonneg
  have h7 : 0 ≤ ∑ x ∈ Leader, g x := by
    exact sum_nonneg hg_nonneg
  have hV_pos : 0 ≤ V := hV_nonneg
  by_cases hV : V = 0
  · -- V = 0 implies ∑ g = 0, which implies p = 0
    have hg0 : ∑ x ∈ Leader, g x = 0 := by
      have h_le : ∑ x ∈ Leader, g x ≤ (K : ℝ) * V := h_bound
      rw [hV] at h_le
      have h1 : ∑ x ∈ Leader, g x ≤ 0 := by simpa using h_le
      have h2 : 0 ≤ ∑ x ∈ Leader, g x := h7
      linarith
    have h1 : p^2 ≤ (∑ x ∈ Leader, f x) * (∑ x ∈ Leader, g x) := h_cs
    rw [hg0] at h1
    have h2 : p^2 ≤ 0 := by simpa using h1
    have h3 : p = 0 := by nlinarith [sq_nonneg p]
    have h_goal : ∑ x ∈ Leader, f x ≥ p^2 / ((K : ℝ) * V) := by
      rw [h3]
      have h4 : (0 : ℝ)^2 / ((K : ℝ) * V) = 0 := by simp
      rw [h4]
      exact h6
    exact h_goal
  · -- V > 0
    have hV_pos' : 0 < V := by
      exact lt_of_le_of_ne hV_nonneg (Ne.symm hV)
    have h8 : p^2 ≤ (∑ x ∈ Leader, f x) * ((K : ℝ) * V) := by
      have h9 : (∑ x ∈ Leader, f x) * (∑ x ∈ Leader, g x) ≤ (∑ x ∈ Leader, f x) * ((K : ℝ) * V) := by
        exact mul_le_mul_of_nonneg_left h_bound h6
      linarith
    have hK_ne : (K : ℝ) ≠ 0 := by exact_mod_cast hK_pos.ne'
    have hKV_pos : 0 < (K : ℝ) * V := mul_pos (by exact_mod_cast hK_pos) hV_pos'
    have h10 : (∑ x ∈ Leader, f x) ≥ p^2 / ((K : ℝ) * V) := by
      calc
        (∑ x ∈ Leader, f x)
          = ((∑ x ∈ Leader, f x) * ((K : ℝ) * V)) / ((K : ℝ) * V) := by
            field_simp [hKV_pos.ne'] <;> ring
        _ ≥ p^2 / ((K : ℝ) * V) := by gcongr
    exact h10

/--
Main leader-pair upper bound on S^{ij}.
-/
lemma leader_pair_bound (K : ℕ) (hK_pos : 0 < K) (k : ℕ) (w : ℕ → ℝ)
    (hw_pos : ∀ l ∈ Icc 1 k, 0 < w l)
    (Leader : Finset β)
    (level : β → ℕ) (hlevel : ∀ x ∈ Leader, level x ∈ Icc 1 k)
    (r : β → ℝ) (hr_nonneg : ∀ x ∈ Leader, 0 ≤ r x)
    (p : ℝ) (hp_nonneg : 0 ≤ p)
    (h_sum_r : ∑ x ∈ Leader, r x = p)
    (h_at_most_K : ∀ l ∈ Icc 1 k, (Leader.filter (fun x => level x = l)).card ≤ K)
    (S_ij : ℝ)
    (h_S_upper : S_ij ≤ p * (∑ l ∈ Icc 1 k, w l) -
        ∑ x ∈ Leader, w (level x) * (r x)^2) :
    S_ij ≤ p * (∑ l ∈ Icc 1 k, w l) -
        p^2 / ((K : ℝ) * ∑ l ∈ Icc 1 k, 1 / w l) := by
  have h_cs := leader_cauchy_schwarz K hK_pos k w hw_pos Leader level hlevel r hr_nonneg
    p hp_nonneg h_sum_r h_at_most_K
  linarith

end MarcusTardos.LeaderPairs
