import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Definitions
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Order function for intersection-reverse sequences

Defines the order function `f(B, a, b)` used in the Marcus--Tardos proof
and proves its basic properties, including the sum characterization for
intersection-reverse lists.
-/

namespace MarcusTardos

variable {α : Type*} [DecidableEq α]

section posOf_lemmas

/-- Distinct elements in a list have distinct first-occurrence positions. -/
lemma posOf_distinct : ∀ (B : List α) (a b : α), a ∈ B → b ∈ B → a ≠ b → posOf a B ≠ posOf b B := by
  intro B
  induction B with
  | nil =>
    intro a b ha hb hne
    simp at ha
  | cons x xs ih =>
    intro a b ha hb hne
    simp only [posOf]
    by_cases hxa : x = a
    · rw [if_pos hxa]
      by_cases hxb : x = b
      · exfalso
        exact hne (hxa.symm.trans hxb)
      · rw [if_neg hxb] <;> simp <;> omega
    · by_cases hxb : x = b
      · rw [if_neg hxa, if_pos hxb] <;> simp <;> omega
      · rw [if_neg hxa, if_neg hxb]
        have hxs_a : a ∈ xs := by
          simp only [List.mem_cons] at ha
          rcases ha with (h | h)
          · exfalso; exact hxa h.symm
          · exact h
        have hxs_b : b ∈ xs := by
          simp only [List.mem_cons] at hb
          rcases hb with (h | h)
          · exfalso; exact hxb h.symm
          · exact h
        have h' : posOf a xs ≠ posOf b xs := ih a b hxs_a hxs_b hne
        have h_goal : (1 + posOf a xs) ≠ (1 + posOf b xs) := by
          intro h_eq
          have h'' : posOf a xs = posOf b xs := by
            simpa [add_left_inj] using h_eq
          exact h' h''
        exact h_goal

/-- For a nodup list, `posOf` is injective on elements of the list. -/
lemma posOf_nodup_inj {B : List α} (hB : B.Nodup) {a b : α}
    (ha : a ∈ B) (hb : b ∈ B) (h : posOf a B = posOf b B) : a = b := by
  by_cases hne : a = b
  · exact hne
  · exfalso
    exact posOf_distinct B a b ha hb hne h

/-- For a nodup list, distinct elements have distinct positions. -/
lemma posOf_nodup_ne {B : List α} (hB : B.Nodup) {a b : α}
    (ha : a ∈ B) (hb : b ∈ B) (hne : a ≠ b) :
    posOf a B ≠ posOf b B :=
  posOf_distinct B a b ha hb hne

end posOf_lemmas

section orderFun

/--
Order function: `1` if `a` precedes `b` in `B`, `-1` if `b` precedes `a`,
`0` if either symbol is absent from `B`.
-/
def orderFun (B : List α) (a b : α) : ℤ :=
  if a ∉ B ∨ b ∉ B then 0
  else if posOf a B < posOf b B then 1
  else -1

/-- Product of order functions for two lists. -/
def orderFun2 (B B' : List α) (a b : α) : ℤ :=
  orderFun B a b * orderFun B' a b

-- Property 1
lemma orderFun_eq_zero_iff {B : List α} {a b : α} :
    orderFun B a b = 0 ↔ a ∉ B ∨ b ∉ B := by
  simp only [orderFun]
  constructor
  · intro h
    by_cases h' : a ∉ B ∨ b ∉ B
    · exact h'
    · have h1 : a ∈ B := by
        by_contra h1
        exact h' (Or.inl h1)
      have h2 : b ∈ B := by
        by_contra h2
        exact h' (Or.inr h2)
      simp [h1, h2] at h <;> omega
  · intro h
    simp [h]

-- Property 2
lemma orderFun_ne_zero {B : List α} {a b : α}
    (ha : a ∈ B) (hb : b ∈ B) (hne : a ≠ b) :
    orderFun B a b ≠ 0 := by
  rw [orderFun]
  have h : ¬(a ∉ B ∨ b ∉ B) := by
    intro h'
    cases h' with
    | inl h1 => exact h1 ha
    | inr h2 => exact h2 hb
  simp [h] <;> omega

-- Property 3: anti-symmetry (for distinct symbols)
lemma orderFun_anti_symm {B : List α} {a b : α}
    (ha : a ∈ B) (hb : b ∈ B) (hne : a ≠ b) :
    orderFun B a b = -orderFun B b a := by
  have hne' : posOf a B ≠ posOf b B := posOf_distinct B a b ha hb hne
  have h : posOf a B < posOf b B ∨ posOf b B < posOf a B :=
    Nat.lt_or_gt_of_ne hne'
  rcases h with (h | h)
  · have h1 : orderFun B a b = 1 := by
      simp [orderFun, ha, hb, h]
    have h2 : orderFun B b a = -1 := by
      simp [orderFun, hb, ha] <;> omega
    rw [h1, h2] <;> norm_num
  · have h1 : orderFun B a b = -1 := by
      simp [orderFun, ha, hb] <;> omega
    have h2 : orderFun B b a = 1 := by
      simp [orderFun, hb, ha, h]
    rw [h1, h2] <;> norm_num

-- Property 4
lemma orderFun_sq_eq_one {B : List α} {a b : α}
    (ha : a ∈ B) (hb : b ∈ B) (hne : a ≠ b) :
    (orderFun B a b)^2 = 1 := by
  have hne' : orderFun B a b ≠ 0 := orderFun_ne_zero ha hb hne
  have : orderFun B a b = 1 ∨ orderFun B a b = -1 := by
    simp [orderFun, ha, hb] <;> omega
  rcases this with (h | h)
  · rw [h] <;> norm_num
  · rw [h] <;> norm_num

-- Property 5: exactly one of 1 or -1
lemma orderFun_exactly_one {B : List α} (hB : B.Nodup) {a b : α}
    (ha : a ∈ B) (hb : b ∈ B) (hne : a ≠ b) :
    (orderFun B a b = 1 ∨ orderFun B a b = -1) ∧
    ¬(orderFun B a b = 1 ∧ orderFun B a b = -1) := by
  have hne' : posOf a B ≠ posOf b B := posOf_nodup_ne hB ha hb hne
  have h : posOf a B < posOf b B ∨ posOf b B < posOf a B :=
    Nat.lt_or_gt_of_ne hne'
  constructor
  · rcases h with (h | h)
    · left
      simp [orderFun, ha, hb, h]
    · right
      simp [orderFun, ha, hb, h] <;> omega
  · intro hcont
    rcases hcont with ⟨h1, h2⟩
    rw [h1] at h2
    norm_num at h2

-- Property 6: same pairs give f2 = 1
lemma orderFun2_same {B B' : List α} {a b : α}
    (ha : a ∈ B) (hb : b ∈ B) (ha' : a ∈ B') (hb' : b ∈ B')
    (hne : a ≠ b)
    (h_agree : (posOf a B < posOf b B) ↔ (posOf a B' < posOf b B')) :
    orderFun2 B B' a b = 1 := by
  by_cases hlt : posOf a B < posOf b B
  · have hlt' : posOf a B' < posOf b B' := h_agree.mp hlt
    have h1 : orderFun B a b = 1 := by
      simp [orderFun, ha, hb, hlt]
    have h2 : orderFun B' a b = 1 := by
      simp [orderFun, ha', hb', hlt']
    rw [orderFun2, h1, h2] <;> norm_num
  · have hnlt' : ¬(posOf a B' < posOf b B') := by
      exact mt h_agree.mpr hlt
    have hne_B' : posOf a B' ≠ posOf b B' := posOf_distinct B' a b ha' hb' hne
    have hgt' : posOf b B' < posOf a B' := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hnlt') hne_B'.symm
    have h1 : orderFun B a b = -1 := by
      simp [orderFun, ha, hb, hlt] <;> omega
    have h2 : orderFun B' a b = -1 := by
      simp [orderFun, ha', hb', hgt'] <;> omega
    rw [orderFun2, h1, h2] <;> norm_num

-- Property 7: different pairs give f2 = -1
lemma orderFun2_different {B B' : List α} {a b : α}
    (hB : B.Nodup) (hB' : B'.Nodup)
    (ha : a ∈ B) (hb : b ∈ B) (ha' : a ∈ B') (hb' : b ∈ B')
    (hne : a ≠ b)
    (h_reverse : (posOf a B < posOf b B) ↔ (posOf b B' < posOf a B')) :
    orderFun2 B B' a b = -1 := by
  have hne_B : posOf a B ≠ posOf b B := posOf_nodup_ne hB ha hb hne
  have hne_B' : posOf a B' ≠ posOf b B' := posOf_nodup_ne hB' ha' hb' hne
  by_cases hlt : posOf a B < posOf b B
  · have hrev : posOf b B' < posOf a B' := h_reverse.mp hlt
    have h1 : orderFun B a b = 1 := by
      simp [orderFun, ha, hb, hlt]
    have h2 : orderFun B' a b = -1 := by
      simp [orderFun, ha', hb', hrev] <;> omega
    rw [orderFun2, h1, h2] <;> norm_num
  · have hgt : posOf b B < posOf a B := by omega
    have hrev' : ¬(posOf b B' < posOf a B') := by
      exact mt h_reverse.mpr hlt
    have hle : posOf a B' ≤ posOf b B' := Nat.le_of_not_gt hrev'
    have hlt' : posOf a B' < posOf b B' := Nat.lt_of_le_of_ne hle hne_B'
    have h1 : orderFun B a b = -1 := by
      simp [orderFun, ha, hb, hlt] <;> omega
    have h2 : orderFun B' a b = 1 := by
      simp [orderFun, ha', hb', hlt']
    rw [orderFun2, h1, h2] <;> norm_num

-- Property 8: f2(B, B', a, b) = f2(B, B', b, a)
lemma orderFun2_symm {B B' : List α} {a b : α}
    (ha : a ∈ B) (hb : b ∈ B) (ha' : a ∈ B') (hb' : b ∈ B')
    (hne : a ≠ b) :
    orderFun2 B B' a b = orderFun2 B B' b a := by
  have h1 : orderFun B a b = -orderFun B b a := orderFun_anti_symm ha hb hne
  have h2 : orderFun B' a b = -orderFun B' b a := orderFun_anti_symm ha' hb' hne
  have h3 : (-orderFun B b a) * (-orderFun B' b a) =
      orderFun B b a * orderFun B' b a := by
    have h4 : ∀ (x y : ℤ), (-x) * (-y) = x * y := by
      intro x y
      calc
        (-x) * (-y) = -(x * (-y)) := by rw [neg_mul]
        _ = -(-(x * y)) := by rw [mul_neg]
        _ = x * y := by rw [neg_neg]
    exact h4 _ _
  calc
    orderFun2 B B' a b
      = orderFun B a b * orderFun B' a b := by rfl
    _ = (-orderFun B b a) * (-orderFun B' b a) := by rw [h1, h2]
    _ = orderFun B b a * orderFun B' b a := h3
    _ = orderFun2 B B' b a := by rfl

end orderFun

section sum_characterization

/--
For intersection-reverse nodup lists, every pair of distinct common symbols
has `orderFun2 = -1`.
-/
lemma orderFun2_eq_neg_one_of_intersectionReverse {B B' : List α}
    (hB : B.Nodup) (hB' : B'.Nodup)
    (h : IsIntersectionReverse B B') {a b : α}
    (ha : a ∈ B) (hb : b ∈ B) (hne : a ≠ b)
    (ha' : a ∈ B') (hb' : b ∈ B') :
    orderFun2 B B' a b = -1 := by
  have h_reverse : (posOf a B < posOf b B) ↔ (posOf b B' < posOf a B') :=
    h a ha b hb hne ha' hb'
  exact orderFun2_different hB hB' ha hb ha' hb' hne h_reverse

/--
For intersection-reverse nodup lists, the sum of `orderFun2` over all
ordered pairs of distinct common symbols equals `|I| - |I|²`.
-/
lemma sum_orderFun2_of_intersectionReverse {B B' : List α}
    (hB : B.Nodup) (hB' : B'.Nodup)
    (h : IsIntersectionReverse B B') :
    ∑ p ∈ (B.toFinset ∩ B'.toFinset).offDiag,
      orderFun2 B B' p.1 p.2 =
    ((B.toFinset ∩ B'.toFinset).card : ℤ) -
    ((B.toFinset ∩ B'.toFinset).card : ℤ)^2 := by
  let I : Finset α := B.toFinset ∩ B'.toFinset
  have h_main : ∀ (p : α × α), p ∈ I.offDiag → orderFun2 B B' p.1 p.2 = -1 := by
    intro p hp
    have hpe : p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≠ p.2 := Finset.mem_offDiag.mp hp
    rcases hpe with ⟨h1, h2, hne⟩
    have h1' : p.1 ∈ B.toFinset ∧ p.1 ∈ B'.toFinset := Finset.mem_inter.mp h1
    have h2' : p.2 ∈ B.toFinset ∧ p.2 ∈ B'.toFinset := Finset.mem_inter.mp h2
    have ha_B : p.1 ∈ B := by
      have h : p.1 ∈ B.toFinset := h1'.1
      simpa [List.mem_toFinset] using h
    have hb_B : p.2 ∈ B := by
      have h : p.2 ∈ B.toFinset := h2'.1
      simpa [List.mem_toFinset] using h
    have ha_B' : p.1 ∈ B' := by
      have h : p.1 ∈ B'.toFinset := h1'.2
      simpa [List.mem_toFinset] using h
    have hb_B' : p.2 ∈ B' := by
      have h : p.2 ∈ B'.toFinset := h2'.2
      simpa [List.mem_toFinset] using h
    exact orderFun2_eq_neg_one_of_intersectionReverse hB hB' h ha_B hb_B hne ha_B' hb_B'
  have h_sum : ∑ p ∈ I.offDiag, orderFun2 B B' p.1 p.2 =
      ∑ p ∈ I.offDiag, (-1 : ℤ) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact h_main p hp
  have h2 : I.card ≤ I.card * I.card := by
    by_cases h4 : I.card = 0
    · rw [h4] <;> simp
    · have h5 : 0 < I.card := Nat.pos_of_ne_zero h4
      exact Nat.le_mul_of_pos_right I.card h5
  have h_card : (I.offDiag.card : ℤ) = (I.card : ℤ)^2 - (I.card : ℤ) := by
    have h : I.offDiag.card = I.card * I.card - I.card := by
      rw [Finset.offDiag_card] <;> ring
    rw [h]
    rw [Nat.cast_sub h2]
    <;> simp [pow_two] <;> ring
  calc
    ∑ p ∈ I.offDiag, orderFun2 B B' p.1 p.2
      = ∑ p ∈ I.offDiag, (-1 : ℤ) := h_sum
    _ = (-1 : ℤ) * (I.offDiag.card : ℤ) := by
      rw [Finset.sum_const] <;> ring
    _ = (I.card : ℤ) - (I.card : ℤ)^2 := by
      rw [h_card] <;> ring

end sum_characterization

end MarcusTardos
