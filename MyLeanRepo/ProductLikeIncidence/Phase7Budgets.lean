module

/-
# Phase7 Budgets — Direction Mass and Double Counting

Budget lemmas for the Phase7 bad-direction Frostman mass argument.

## Main results
- `double_counting_good_directions`: extract Θ_bad with per-direction density ≥ c/2
- `sector_absorb_edir`: sector absorb budget with direction mass exponent ε_dir
- `frostman_budget_edir`: Frostman transport budget with direction mass exponent ε_dir

## Parameter distinction
- `ε_sel`: small Kaufman/energy selection threshold (10·ε_sel < η_work)
- `ε_dir`: Phase7 bad-direction Frostman mass exponent (≈ 3·η, from double counting)

These are separate parameters serving different purposes.

## Whiteprint node
`phase7_double_counting_density`
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Finset ENNReal Bornology Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-! ## Double Counting Lemma -/

/-- Extract a large subset of directions with high point-incidence.

Given a finite set of directions `Y`, a finite set of points `A`, and a family
`T y` of points associated with each direction, if every point `p ∈ A` belongs
to at least `c · |Y|` direction families, then there exists a subset `Θ_bad ⊆ Y`
of cardinality at least `(c/2) · |Y|` such that for every `y ∈ Θ_bad`,
`|A ∩ T y| ≥ (c/2) · |A|`.

Proof by Markov inequality on the complement. -/
lemma double_counting_good_directions
    {α β : Type*}
    (Y : Finset α)
    (A : Finset β)
    (T : α → Finset β)
    (c : ℝ)
    (hc_pos : 0 < c)
    (hc_le_one : c ≤ 1)
    (h_mult : ∀ p ∈ A,
      ({y ∈ Y | p ∈ T y}.card : ℝ) ≥ c * Y.card) :
    ∃ (Θ_bad : Finset α),
      Θ_bad ⊆ Y ∧
      (Θ_bad.card : ℝ) ≥ (c / 2) * Y.card ∧
      ∀ y ∈ Θ_bad, ((A ∩ T y).card : ℝ) ≥ (c / 2) * A.card := by
  let B : Finset α := Y.filter (fun y => ((A ∩ T y).card : ℝ) < (c / 2) * A.card)
  have hB_sub : B ⊆ Y := filter_subset _ _
  let Θ_bad : Finset α := Y \ B
  have hΘ_sub : Θ_bad ⊆ Y := by simp [Θ_bad]
  have h_good_property : ∀ y ∈ Θ_bad, ((A ∩ T y).card : ℝ) ≥ (c / 2) * A.card := by
    intro y hy
    have h_y_in_Y : y ∈ Y := hΘ_sub hy
    have h_y_not_B : y ∉ B := (Finset.mem_sdiff.mp hy).2
    by_contra h
    have h' : ((A ∩ T y).card : ℝ) < (c / 2) * A.card := by linarith
    have h_y_in_B : y ∈ B := by
      rw [mem_filter]; exact ⟨h_y_in_Y, h'⟩
    exact h_y_not_B h_y_in_B
  let ind : α → β → ℕ := fun y p => if p ∈ T y then 1 else 0
  have h1 : ∀ y, (A ∩ T y).card = ∑ p ∈ A, ind y p := by
    intro y
    have h2 : A ∩ T y = A.filter (fun p => p ∈ T y) := by ext x; simp
    rw [h2, Finset.card_filter]
  have h3 : ∀ p, (Y.filter (fun y => p ∈ T y)).card = ∑ y ∈ Y, ind y p := by
    intro p
    rw [Finset.card_filter]
  have h_sum1 : ∑ y ∈ Y, (A ∩ T y).card = ∑ y ∈ Y, ∑ p ∈ A, ind y p := by
    apply Finset.sum_congr rfl
    intro y _
    exact h1 y
  have h_sum2 : ∑ y ∈ Y, ∑ p ∈ A, ind y p = ∑ p ∈ A, ∑ y ∈ Y, ind y p := by
    rw [Finset.sum_comm]
  have h_sum3 : ∑ p ∈ A, ∑ y ∈ Y, ind y p = ∑ p ∈ A, (Y.filter (fun y => p ∈ T y)).card := by
    apply Finset.sum_congr rfl
    intro p _
    exact (h3 p).symm
  have h_sum : (∑ y ∈ Y, (A ∩ T y).card : ℝ) =
      (∑ p ∈ A, (Y.filter (fun y => p ∈ T y)).card : ℝ) := by
    exact_mod_cast Eq.trans h_sum1 (Eq.trans h_sum2 h_sum3)
  have h_sum_lower : (∑ y ∈ Y, (A ∩ T y).card : ℝ) ≥ c * (Y.card : ℝ) * (A.card : ℝ) := by
    rw [h_sum]
    have h_terms : ∀ p ∈ A, ((Y.filter (fun y => p ∈ T y)).card : ℝ) ≥ c * (Y.card : ℝ) := h_mult
    have h_sum_ge : (∑ p ∈ A, ((Y.filter (fun y => p ∈ T y)).card : ℝ)) ≥
        ∑ p ∈ A, (c * (Y.card : ℝ)) := Finset.sum_le_sum h_terms
    have h_final : (∑ p ∈ A, (c * (Y.card : ℝ))) = c * (Y.card : ℝ) * (A.card : ℝ) := by
      simp [mul_comm]
    linarith [h_sum_ge, h_final]
  have hB_sum_le : (∑ y ∈ B, (A ∩ T y).card : ℝ) ≤
      (B.card : ℝ) * ((c / 2) * A.card) := by
    have h21 : ∀ y ∈ B, ((A ∩ T y).card : ℝ) ≤ (c / 2) * A.card := by
      intro y hy
      have h : ((A ∩ T y).card : ℝ) < (c / 2) * A.card := by
        rw [mem_filter] at hy; exact hy.2
      exact le_of_lt h
    have h22 : (∑ y ∈ B, (A ∩ T y).card : ℝ) ≤ ∑ y ∈ B, ((c / 2) * A.card) :=
      Finset.sum_le_sum h21
    simpa [Finset.sum_const] using h22
  have hΘ_sum_le : (∑ y ∈ Θ_bad, (A ∩ T y).card : ℝ) ≤
      (Θ_bad.card : ℝ) * (A.card : ℝ) := by
    have h31 : ∀ y ∈ Θ_bad, ((A ∩ T y).card : ℝ) ≤ (A.card : ℝ) := by
      intro y _
      have h_sub : A ∩ T y ⊆ A := by simp
      exact_mod_cast Finset.card_le_card h_sub
    have h32 : (∑ y ∈ Θ_bad, (A ∩ T y).card : ℝ) ≤ ∑ y ∈ Θ_bad, (A.card : ℝ) :=
      Finset.sum_le_sum h31
    simpa [Finset.sum_const] using h32
  have h_disj : Disjoint B Θ_bad := by
    exact Finset.disjoint_sdiff
  have h_union : B ∪ Θ_bad = Y := by
    exact Finset.union_sdiff_of_subset hB_sub
  have h_sum_split : (∑ y ∈ Y, (A ∩ T y).card : ℝ) =
      (∑ y ∈ B, (A ∩ T y).card : ℝ) + (∑ y ∈ Θ_bad, (A ∩ T y).card : ℝ) := by
    have h : Y = B ∪ Θ_bad := h_union.symm
    rw [h]
    rw [Finset.sum_union h_disj]
  have h_card_add : (B.card : ℝ) + (Θ_bad.card : ℝ) = (Y.card : ℝ) := by
    have h'' : (B ∪ Θ_bad).card = B.card + Θ_bad.card :=
      Finset.card_union_of_disjoint h_disj
    have h3 : B ∪ Θ_bad = Y := h_union
    norm_cast at h'' ⊢
    rw [h3] at h''
    exact h''.symm
  have h_card_diff : (Θ_bad.card : ℝ) = (Y.card : ℝ) - (B.card : ℝ) := by
    linarith
  have h_pos1 : 0 < 1 - c / 2 := by linarith
  have hB_card_lt : (B.card : ℝ) ≤ (1 - c / 2) * Y.card := by
    by_cases hA : A.card = 0
    · have hB_empty : B = ∅ := by
        simp only [B, Finset.filter_eq_empty_iff]
        intro y _
        rw [hA] <;> norm_num
      rw [hB_empty] <;> simp <;> positivity
    · have hA_pos : 0 < (A.card : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hA
      by_contra h
      have h' : (B.card : ℝ) > (1 - c / 2) * Y.card := by linarith
      have h_sum_upper : (∑ y ∈ Y, (A ∩ T y).card : ℝ) <
          c * (Y.card : ℝ) * (A.card : ℝ) := by
        have h_total : (∑ y ∈ Y, (A ∩ T y).card : ℝ) =
            (∑ y ∈ B, (A ∩ T y).card : ℝ) + (∑ y ∈ Θ_bad, (A ∩ T y).card : ℝ) := h_sum_split
        rw [h_total]
        have h9 : (∑ y ∈ B, (A ∩ T y).card : ℝ) + (∑ y ∈ Θ_bad, (A ∩ T y).card : ℝ) ≤
            (B.card : ℝ) * ((c / 2) * A.card) + (Θ_bad.card : ℝ) * (A.card : ℝ) := by
          linarith [hB_sum_le, hΘ_sum_le]
        have h10 : (B.card : ℝ) * ((c / 2) * A.card) + (Θ_bad.card : ℝ) * (A.card : ℝ) =
            (A.card : ℝ) * ((c / 2) * (B.card : ℝ) + (Θ_bad.card : ℝ)) := by ring
        rw [h10] at h9
        rw [h_card_diff] at h9
        have h11 : (A.card : ℝ) * ((c / 2) * (B.card : ℝ) + ((Y.card : ℝ) - (B.card : ℝ))) <
            c * (Y.card : ℝ) * (A.card : ℝ) := by
          have h12 : 0 < (A.card : ℝ) := hA_pos
          have h13 : (c / 2) * (B.card : ℝ) + ((Y.card : ℝ) - (B.card : ℝ)) < c * (Y.card : ℝ) := by
            have h14 : 0 < 1 - c / 2 := h_pos1
            nlinarith [sq_nonneg (c / 2), h']
          have h14 : (A.card : ℝ) * ((c / 2) * (B.card : ℝ) + ((Y.card : ℝ) - (B.card : ℝ))) <
              (A.card : ℝ) * (c * (Y.card : ℝ)) := mul_lt_mul_of_pos_left h13 hA_pos
          have h15 : (A.card : ℝ) * (c * (Y.card : ℝ)) = c * (Y.card : ℝ) * (A.card : ℝ) := by ring
          rw [h15] at h14
          exact h14
        exact lt_of_le_of_lt h9 h11
      have h_cont : (∑ y ∈ Y, (A ∩ T y).card : ℝ) ≥ c * (Y.card : ℝ) * (A.card : ℝ) := h_sum_lower
      exact False.elim (not_le.mpr h_sum_upper h_cont)
  have hΘ_card : (Θ_bad.card : ℝ) ≥ (c / 2) * Y.card := by
    rw [h_card_diff]
    linarith
  exact ⟨Θ_bad, hΘ_sub, hΘ_card, h_good_property⟩

/-- Variant of `double_counting_good_directions` for the case `T y ⊆ A`.

Takes a caller-provided decidable predicate `P` equivalent to `p ∈ T y`, which
avoids expensive `DecidableEq` instance resolution on `β` (e.g. `EuclideanSpace`
with classical choice). -/
lemma double_counting_good_directions_subset
    {α β : Type*}
    (Y : Finset α)
    (A : Finset β)
    (T : α → Finset β)
    (P : β → α → Prop)
    [hPdec : ∀ (p : β), DecidablePred (P p)]
    (hP : ∀ p y, P p y ↔ p ∈ T y)
    (c : ℝ)
    (hc_pos : 0 < c)
    (hc_le_one : c ≤ 1)
    (hT_sub_A : ∀ y ∈ Y, T y ⊆ A)
    (h_mult : ∀ p ∈ A,
      (↑(∑ y ∈ Y, (if P p y then 1 else 0)) : ℝ) ≥ c * ↑Y.card) :
    ∃ (Θ_bad : Finset α),
      Θ_bad ⊆ Y ∧
      (Θ_bad.card : ℝ) ≥ (c / 2) * Y.card ∧
      ∀ y ∈ Θ_bad, ((T y).card : ℝ) ≥ (c / 2) * A.card := by
  let B : Finset α := Y.filter (fun y => ((T y).card : ℝ) < (c / 2) * A.card)
  have hB_sub : B ⊆ Y := filter_subset _ _
  let Θ_bad : Finset α := Y \ B
  have hΘ_sub : Θ_bad ⊆ Y := by simp [Θ_bad]
  have h_good_property : ∀ y ∈ Θ_bad, ((T y).card : ℝ) ≥ (c / 2) * A.card := by
    intro y hy
    have h_y_in_Y : y ∈ Y := hΘ_sub hy
    have h_y_not_B : y ∉ B := (Finset.mem_sdiff.mp hy).2
    by_contra h
    have h' : ((T y).card : ℝ) < (c / 2) * A.card := by linarith
    have h_y_in_B : y ∈ B := by
      rw [mem_filter]; exact ⟨h_y_in_Y, h'⟩
    exact h_y_not_B h_y_in_B
  let ind : α → β → ℕ := fun y p => if P p y then 1 else 0
  have h1 : ∀ y ∈ Y, (T y).card = ∑ p ∈ A, ind y p := by
    intro y hy
    have h_sub : T y ⊆ A := hT_sub_A y hy
    have h2 : T y = A.filter (fun p => P p y) := by
      ext x
      simp only [Finset.mem_filter]
      have h3 : x ∈ T y ↔ x ∈ A ∧ P x y := by
        constructor
        · intro h4; exact ⟨h_sub h4, (hP x y).mpr h4⟩
        · rintro ⟨h4, h5⟩; exact (hP x y).mp h5
      exact h3
    rw [h2, Finset.card_filter]
  have h3 : ∀ p, (Y.filter (fun y => P p y)).card = ∑ y ∈ Y, ind y p := by
    intro p
    rw [Finset.card_filter] <;> rfl
  have h_sum1 : ∑ y ∈ Y, (T y).card = ∑ y ∈ Y, ∑ p ∈ A, ind y p := by
    apply Finset.sum_congr rfl
    intro y hy
    exact h1 y hy
  have h_sum2 : ∑ y ∈ Y, ∑ p ∈ A, ind y p = ∑ p ∈ A, ∑ y ∈ Y, ind y p := by
    rw [Finset.sum_comm]
  have h_sum3 : ∑ p ∈ A, ∑ y ∈ Y, ind y p = ∑ p ∈ A, (Y.filter (fun y => P p y)).card := by
    apply Finset.sum_congr rfl
    intro p _
    exact (h3 p).symm
  have h_sum : (∑ y ∈ Y, (T y).card : ℝ) =
      (∑ p ∈ A, (Y.filter (fun y => P p y)).card : ℝ) := by
    exact_mod_cast Eq.trans h_sum1 (Eq.trans h_sum2 h_sum3)
  have h_sum_lower : (∑ y ∈ Y, (T y).card : ℝ) ≥ c * (Y.card : ℝ) * (A.card : ℝ) := by
    rw [h_sum]
    have h4 : ∀ p ∈ A, ((Y.filter (fun y => P p y)).card : ℝ) ≥ c * ↑Y.card := by
      intro p hp
      have h51 : (Y.filter (fun y => P p y)).card = ∑ y ∈ Y, (if P p y then 1 else 0) := by
        rw [Finset.card_filter] <;> rfl
      have h5 : ((Y.filter (fun y => P p y)).card : ℝ) =
          (↑(∑ y ∈ Y, (if P p y then 1 else 0)) : ℝ) := by
        exact_mod_cast h51
      rw [h5]
      exact h_mult p hp
    have h_terms : ∀ p ∈ A, ((Y.filter (fun y => P p y)).card : ℝ) ≥ c * (Y.card : ℝ) := h4
    have h_sum_ge : (∑ p ∈ A, ((Y.filter (fun y => P p y)).card : ℝ)) ≥
        ∑ p ∈ A, (c * (Y.card : ℝ)) := Finset.sum_le_sum h_terms
    have h_final : (∑ p ∈ A, (c * (Y.card : ℝ))) = c * (Y.card : ℝ) * (A.card : ℝ) := by
      simp [mul_comm]
    linarith [h_sum_ge, h_final]
  have hB_sum_le : (∑ y ∈ B, (T y).card : ℝ) ≤
      (B.card : ℝ) * ((c / 2) * A.card) := by
    have h21 : ∀ y ∈ B, ((T y).card : ℝ) ≤ (c / 2) * A.card := by
      intro y hy
      have h : ((T y).card : ℝ) < (c / 2) * A.card := by
        rw [mem_filter] at hy; exact hy.2
      exact le_of_lt h
    have h22 : (∑ y ∈ B, (T y).card : ℝ) ≤ ∑ y ∈ B, ((c / 2) * A.card) :=
      Finset.sum_le_sum h21
    simpa [Finset.sum_const] using h22
  have hΘ_sum_le : (∑ y ∈ Θ_bad, (T y).card : ℝ) ≤
      (Θ_bad.card : ℝ) * (A.card : ℝ) := by
    have h31 : ∀ y ∈ Θ_bad, ((T y).card : ℝ) ≤ (A.card : ℝ) := by
      intro y _
      have h_sub : T y ⊆ A := hT_sub_A y (hΘ_sub ‹_›)
      exact_mod_cast Finset.card_le_card h_sub
    have h32 : (∑ y ∈ Θ_bad, (T y).card : ℝ) ≤ ∑ y ∈ Θ_bad, (A.card : ℝ) :=
      Finset.sum_le_sum h31
    simpa [Finset.sum_const] using h32
  have h_disj : Disjoint B Θ_bad := by
    exact Finset.disjoint_sdiff
  have h_union : B ∪ Θ_bad = Y := by
    have h : Θ_bad = Y \ B := by rfl
    rw [h]
    exact Finset.union_sdiff_of_subset hB_sub
  have h_sum_split : (∑ y ∈ Y, (T y).card : ℝ) =
      (∑ y ∈ B, (T y).card : ℝ) + (∑ y ∈ Θ_bad, (T y).card : ℝ) := by
    have h : Y = B ∪ Θ_bad := h_union.symm
    rw [h]
    rw [Finset.sum_union h_disj]
  have h_card_add : (B.card : ℝ) + (Θ_bad.card : ℝ) = (Y.card : ℝ) := by
    have h'' : (B ∪ Θ_bad).card = B.card + Θ_bad.card :=
      Finset.card_union_of_disjoint h_disj
    have h3 : B ∪ Θ_bad = Y := h_union
    norm_cast at h'' ⊢
    rw [h3] at h''
    exact h''.symm
  have h_card_diff : (Θ_bad.card : ℝ) = (Y.card : ℝ) - (B.card : ℝ) := by
    linarith
  have h_pos1 : 0 < 1 - c / 2 := by linarith
  have hB_card_lt : (B.card : ℝ) ≤ (1 - c / 2) * Y.card := by
    by_cases hA : A.card = 0
    · have hB_empty : B = ∅ := by
        simp only [B, Finset.filter_eq_empty_iff]
        intro y _
        rw [hA] <;> norm_num
      rw [hB_empty] <;> simp <;> positivity
    · have hA_pos : 0 < (A.card : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hA
      by_contra h
      have h' : (B.card : ℝ) > (1 - c / 2) * Y.card := by linarith
      have h_sum_upper : (∑ y ∈ Y, (T y).card : ℝ) <
          c * (Y.card : ℝ) * (A.card : ℝ) := by
        have h_total : (∑ y ∈ Y, (T y).card : ℝ) =
            (∑ y ∈ B, (T y).card : ℝ) + (∑ y ∈ Θ_bad, (T y).card : ℝ) := h_sum_split
        rw [h_total]
        have h9 : (∑ y ∈ B, (T y).card : ℝ) + (∑ y ∈ Θ_bad, (T y).card : ℝ) ≤
            (B.card : ℝ) * ((c / 2) * A.card) + (Θ_bad.card : ℝ) * (A.card : ℝ) := by
          linarith [hB_sum_le, hΘ_sum_le]
        have h10 : (B.card : ℝ) * ((c / 2) * A.card) + (Θ_bad.card : ℝ) * (A.card : ℝ) =
            (A.card : ℝ) * ((c / 2) * (B.card : ℝ) + (Θ_bad.card : ℝ)) := by ring
        rw [h10] at h9
        rw [h_card_diff] at h9
        have h11 : (A.card : ℝ) * ((c / 2) * (B.card : ℝ) + ((Y.card : ℝ) - (B.card : ℝ))) <
            c * (Y.card : ℝ) * (A.card : ℝ) := by
          have h12 : 0 < (A.card : ℝ) := hA_pos
          have h13 : (c / 2) * (B.card : ℝ) + ((Y.card : ℝ) - (B.card : ℝ)) < c * (Y.card : ℝ) := by
            have h14 : 0 < 1 - c / 2 := h_pos1
            nlinarith [sq_nonneg (c / 2), h']
          have h14 : (A.card : ℝ) * ((c / 2) * (B.card : ℝ) + ((Y.card : ℝ) - (B.card : ℝ))) <
              (A.card : ℝ) * (c * (Y.card : ℝ)) := mul_lt_mul_of_pos_left h13 hA_pos
          have h15 : (A.card : ℝ) * (c * (Y.card : ℝ)) = c * (Y.card : ℝ) * (A.card : ℝ) := by ring
          rw [h15] at h14
          exact h14
        exact lt_of_le_of_lt h9 h11
      have h_cont : (∑ y ∈ Y, (T y).card : ℝ) ≥ c * (Y.card : ℝ) * (A.card : ℝ) := h_sum_lower
      exact False.elim (not_le.mpr h_sum_upper h_cont)
  have hΘ_card : (Θ_bad.card : ℝ) ≥ (c / 2) * Y.card := by
    rw [h_card_diff]
    linarith
  exact ⟨Θ_bad, hΘ_sub, hΘ_card, h_good_property⟩

/-! ## Direction Failure Budgets with ε_dir -/

/-- Sector absorb budget with ε_dir ≤ 3η.

We need `C_ν * δ^τ ≤ δ^{ε_dir} / 2`.
Since `ε_dir ≤ 3η` and `δ < 1`, `δ^{ε_dir} ≥ δ^{3η}`, so it suffices to prove
`C_ν * δ^τ ≤ δ^{3η} / 2`, which follows from τ > 8η.
-/
lemma sector_absorb_edir
    {δ τ η ε_dir : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hη_pos : 0 < η)
    (hτ_gt_8eta : τ > 8 * η)
    (h_edir_pos : 0 < ε_dir)
    (h_edir_le_3eta : ε_dir ≤ 3 * η)
    (C_Y : ℝ) (hC_Y_le : C_Y ≤ δ ^ (-η))
    (C_ν : ℝ) (hC_ν_le : C_ν ≤ 3 * C_Y * (2 : ℝ) ^ τ)
    (hδ_small : δ ^ (τ - 4 * η) ≤ 1 / (6 * (2 : ℝ) ^ τ)) :
    C_ν * δ ^ τ ≤ δ ^ ε_dir / 2 := by
  have h3 : C_ν * δ ^ τ ≤ 3 * (2 : ℝ) ^ τ * δ ^ (τ - η) := by
    calc C_ν * δ ^ τ
      ≤ (3 * C_Y * (2 : ℝ) ^ τ) * δ ^ τ := by gcongr
    _ ≤ 3 * (δ ^ (-η)) * (2 : ℝ) ^ τ * δ ^ τ := by gcongr
    _ = 3 * (2 : ℝ) ^ τ * (δ ^ (-η) * δ ^ τ) := by ring
    _ = 3 * (2 : ℝ) ^ τ * δ ^ (τ - η) := by
      have h_eq : δ ^ (-η) * δ ^ τ = δ ^ (τ - η) := by
        rw [← Real.rpow_add hδ_pos] <;> ring_nf
      rw [h_eq]
  have h5 : 3 * (2 : ℝ) ^ τ * δ ^ (τ - η) ≤ δ ^ (3 * η) / 2 := by
    have h6 : δ ^ (τ - η) = δ ^ (3 * η) * δ ^ (τ - 4 * η) := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf <;> ring
    rw [h6]
    have h8 : 3 * (2 : ℝ) ^ τ * δ ^ (τ - 4 * η) ≤ 1 / 2 := by
      have h9 : 3 * (2 : ℝ) ^ τ * δ ^ (τ - 4 * η) ≤
          3 * (2 : ℝ) ^ τ * (1 / (6 * (2 : ℝ) ^ τ)) := by gcongr <;> linarith
      have h10 : 0 < (2 : ℝ) ^ τ := by positivity
      have h11 : 3 * (2 : ℝ) ^ τ * (1 / (6 * (2 : ℝ) ^ τ)) = 1 / 2 := by
        field_simp [h10.ne'] <;> ring
      rw [h11] at h9; exact h9
    have h12 : 3 * (2 : ℝ) ^ τ * (δ ^ (3 * η) * δ ^ (τ - 4 * η)) =
        δ ^ (3 * η) * (3 * (2 : ℝ) ^ τ * δ ^ (τ - 4 * η)) := by ring
    rw [h12]
    have h13 : δ ^ (3 * η) * (3 * (2 : ℝ) ^ τ * δ ^ (τ - 4 * η)) ≤
        δ ^ (3 * η) * (1 / 2) := by exact mul_le_mul_of_nonneg_left h8 (by positivity)
    linarith
  have h6 : δ ^ (3 * η) / 2 ≤ δ ^ ε_dir / 2 := by
    have h7 : δ ^ (3 * η) ≤ δ ^ ε_dir :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos (le_of_lt hδ_lt_one) h_edir_le_3eta
    linarith
  exact le_trans (le_trans h3 h5) h6

/-- Frostman budget with ε_dir ≤ 3η.

We need `C_ν * 8 * δ^{-ε_dir} * L_chart^τ ≤ K_work * δ^{-εnc}`.
Since `ε_dir ≤ 3η` and `δ < 1`, `δ^{-ε_dir} ≤ δ^{-3η}`, so it suffices to prove
the bound with exponent 3η.
-/
lemma frostman_budget_edir
    {δ τ η εnc ε_dir : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hη_pos : 0 < η)
    (hτ_pos : 0 < τ)
    (h_edir_pos : 0 < ε_dir)
    (h_edir_le_3eta : ε_dir ≤ 3 * η)
    (C_Y : ℝ) (hC_Y_le : C_Y ≤ δ ^ (-η))
    (C_ν : ℝ) (hC_ν_pos : 0 < C_ν) (hC_ν_le : C_ν ≤ 3 * C_Y * (2 : ℝ) ^ τ)
    (L_chart K_work : ℝ)
    (hL_chart_ge_one : 1 ≤ L_chart)
    (hK_work_pos : 0 < K_work)
    (henc_gt_4eta : εnc > 4 * η)
    (hδ_small : δ ^ (εnc - 4 * η) ≤ K_work / (24 * (2 : ℝ) ^ τ * L_chart ^ τ)) :
    C_ν * (8 : ℝ) * δ ^ (-ε_dir) * L_chart ^ τ ≤ K_work * δ ^ (-εnc) := by
  have h_monotone : δ ^ (-ε_dir) ≤ δ ^ (-(3 * η)) := by
    have h : -(3 * η) ≤ -ε_dir := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hδ_pos (le_of_lt hδ_lt_one) h
  have h1 : C_ν * (8 : ℝ) * δ ^ (-ε_dir) * L_chart ^ τ ≤
      C_ν * (8 : ℝ) * δ ^ (-(3 * η)) * L_chart ^ τ := by
    have h_pos1 : 0 ≤ C_ν * (8 : ℝ) := by positivity
    have h_pos2 : 0 ≤ L_chart ^ τ := by positivity
    have h : δ ^ (-ε_dir) * L_chart ^ τ ≤ δ ^ (-(3 * η)) * L_chart ^ τ :=
      mul_le_mul_of_nonneg_right h_monotone h_pos2
    have h' : C_ν * (8 : ℝ) * (δ ^ (-ε_dir) * L_chart ^ τ) ≤
        C_ν * (8 : ℝ) * (δ ^ (-(3 * η)) * L_chart ^ τ) :=
      mul_le_mul_of_nonneg_left h h_pos1
    have h_eq1 : C_ν * (8 : ℝ) * δ ^ (-ε_dir) * L_chart ^ τ =
        C_ν * (8 : ℝ) * (δ ^ (-ε_dir) * L_chart ^ τ) := by ring
    have h_eq2 : C_ν * (8 : ℝ) * δ ^ (-(3 * η)) * L_chart ^ τ =
        C_ν * (8 : ℝ) * (δ ^ (-(3 * η)) * L_chart ^ τ) := by ring
    rw [h_eq1, h_eq2]
    exact h'
  have h2 : C_ν * (8 : ℝ) * δ ^ (-(3 * η)) * L_chart ^ τ ≤
      (24 : ℝ) * (2 : ℝ) ^ τ * L_chart ^ τ * δ ^ (-(4 * η)) := by
    calc C_ν * (8 : ℝ) * δ ^ (-(3 * η)) * L_chart ^ τ
      ≤ (3 * C_Y * (2 : ℝ) ^ τ) * (8 : ℝ) * δ ^ (-(3 * η)) * L_chart ^ τ := by gcongr
    _ ≤ 3 * (δ ^ (-η)) * (2 : ℝ) ^ τ * (8 : ℝ) * δ ^ (-(3 * η)) * L_chart ^ τ := by gcongr
    _ = (24 : ℝ) * (2 : ℝ) ^ τ * L_chart ^ τ * (δ ^ (-η) * δ ^ (-(3 * η))) := by ring
    _ = (24 : ℝ) * (2 : ℝ) ^ τ * L_chart ^ τ * δ ^ (-(4 * η)) := by
      have h_eq : δ ^ (-η) * δ ^ (-(3 * η)) = δ ^ (-(4 * η)) := by
        rw [← Real.rpow_add hδ_pos]; ring_nf
      rw [h_eq]
  have h5 : δ ^ (-(εnc - 4 * η)) ≥ (24 : ℝ) * (2 : ℝ) ^ τ * L_chart ^ τ / K_work := by
    have h_recip : δ ^ (-(εnc - 4 * η)) = 1 / δ ^ (εnc - 4 * η) := by
      rw [Real.rpow_neg (le_of_lt hδ_pos) (εnc - 4 * η)] <;> field_simp
    rw [h_recip]
    have h7 : 1 / δ ^ (εnc - 4 * η) ≥ 1 / (K_work / (24 * (2 : ℝ) ^ τ * L_chart ^ τ)) := by gcongr
    have h8 : 1 / (K_work / (24 * (2 : ℝ) ^ τ * L_chart ^ τ)) =
        (24 * (2 : ℝ) ^ τ * L_chart ^ τ) / K_work := by
      field_simp [hK_work_pos.ne'] <;> ring
    rw [h8] at h7; exact h7
  have hK_pos : 0 < K_work := hK_work_pos
  have h4 : (24 : ℝ) * (2 : ℝ) ^ τ * L_chart ^ τ ≤ K_work * δ ^ (-(εnc - 4 * η)) := by
    have h9 : (24 : ℝ) * (2 : ℝ) ^ τ * L_chart ^ τ / K_work ≤ δ ^ (-(εnc - 4 * η)) := h5
    have h10 : (24 : ℝ) * (2 : ℝ) ^ τ * L_chart ^ τ =
        K_work * ((24 : ℝ) * (2 : ℝ) ^ τ * L_chart ^ τ / K_work) := by
      field_simp [hK_pos.ne'] <;> ring
    rw [h10]; gcongr
  have h7 : δ ^ (-(4 * η)) * δ ^ (-(εnc - 4 * η)) = δ ^ (-εnc) := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf
  have h_goal : (24 : ℝ) * (2 : ℝ) ^ τ * L_chart ^ τ * δ ^ (-(4 * η)) ≤
      K_work * δ ^ (-εnc) := by
    calc (24 : ℝ) * (2 : ℝ) ^ τ * L_chart ^ τ * δ ^ (-(4 * η))
      ≤ (K_work * δ ^ (-(εnc - 4 * η))) * δ ^ (-(4 * η)) := by gcongr
    _ = K_work * (δ ^ (-(4 * η)) * δ ^ (-(εnc - 4 * η))) := by ring
    _ = K_work * δ ^ (-εnc) := by rw [h7]
  exact le_trans (le_trans h1 h2) h_goal

end ProductLikeIncidence.ProductReduction
