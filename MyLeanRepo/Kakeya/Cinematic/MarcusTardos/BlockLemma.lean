import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.OrderFunction
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.BlockStructure
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.CutPoint
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Block lemma (Marcus--Tardos Lemma 2)

For intersection-reverse cyclic sequences split into consecutive blocks,
at most one block pair is singular, and we bound the sum of orderFun2
for singular and intersection-reverse block pairs.
-/

namespace MarcusTardos

variable {α : Type*} [DecidableEq α]

section ReversalRotation

/--
Two lists have the "reversal-rotation" structure on their common elements:
the common set is partitioned into S and T, where within each part the
orders are reversed, but every element of S precedes every element of T
in both lists. This is the structure of a singular block pair.
-/
def IsReversalRotation (B B' : List α) : Prop :=
  ∃ (S T : Finset α),
    Disjoint S T ∧
    S ∪ T = B.toFinset ∩ B'.toFinset ∧
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      (posOf a B < posOf b B ↔ posOf b B' < posOf a B')) ∧
    (∀ a ∈ T, ∀ b ∈ T, a ≠ b →
      (posOf a B < posOf b B ↔ posOf b B' < posOf a B')) ∧
    (∀ a ∈ S, ∀ b ∈ T,
      posOf a B < posOf b B ∧ posOf a B' < posOf b B')

/--
For a reversal-rotation pair, the sum of orderFun2 over all ordered
pairs of distinct common elements is at most `r = |S ∪ T|`.
The exact value is `r - (s - t)^2`.
-/
lemma sum_orderFun2_of_reversalRotation {B B' : List α}
    (hB : B.Nodup) (hB' : B'.Nodup)
    (h : IsReversalRotation B B') :
    ∑ p ∈ (B.toFinset ∩ B'.toFinset).offDiag,
      orderFun2 B B' p.1 p.2 ≤
    ((B.toFinset ∩ B'.toFinset).card : ℤ) := by
  rcases h with ⟨S, T, h_disj, h_cover, h_rev_S, h_rev_T, h_before⟩
  let I : Finset α := B.toFinset ∩ B'.toFinset
  let s : ℕ := S.card
  let t : ℕ := T.card
  have hI : I = S ∪ T := h_cover.symm
  have h_card : I.card = s + t := by
    have h' : I.card = (S ∪ T).card := by rw [hI]
    rw [h', Finset.card_union_of_disjoint h_disj]
  have h_memI_S : ∀ x ∈ S, x ∈ I := by
    intro x hx
    have h : x ∈ S ∪ T := Finset.mem_union_left T hx
    exact hI ▸ h
  have h_memI_T : ∀ x ∈ T, x ∈ I := by
    intro x hx
    have h : x ∈ S ∪ T := Finset.mem_union_right S hx
    exact hI ▸ h
  have h_inB : ∀ x ∈ I, x ∈ B := by
    intro x hx
    simpa [List.mem_toFinset] using (Finset.mem_inter.mp hx).1
  have h_inB' : ∀ x ∈ I, x ∈ B' := by
    intro x hx
    simpa [List.mem_toFinset] using (Finset.mem_inter.mp hx).2
  -- Cross pairs S × T have f2 = 1
  have h_cross1 : ∀ p ∈ S ×ˢ T, orderFun2 B B' p.1 p.2 = 1 := by
    intro p hp
    have ha : p.1 ∈ S := (Finset.mem_product.mp hp).1
    have hb : p.2 ∈ T := (Finset.mem_product.mp hp).2
    have h_before' : posOf p.1 B < posOf p.2 B ∧ posOf p.1 B' < posOf p.2 B' :=
      h_before p.1 ha p.2 hb
    have haB : p.1 ∈ B := h_inB p.1 (h_memI_S p.1 ha)
    have hbB : p.2 ∈ B := h_inB p.2 (h_memI_T p.2 hb)
    have haB' : p.1 ∈ B' := h_inB' p.1 (h_memI_S p.1 ha)
    have hbB' : p.2 ∈ B' := h_inB' p.2 (h_memI_T p.2 hb)
    have h1 : orderFun B p.1 p.2 = 1 := by
      simp [orderFun, haB, hbB, h_before'.1]
    have h2 : orderFun B' p.1 p.2 = 1 := by
      simp [orderFun, haB', hbB', h_before'.2]
    rw [orderFun2, h1, h2] <;> norm_num
  -- Cross pairs T × S have f2 = 1
  have h_cross2 : ∀ p ∈ T ×ˢ S, orderFun2 B B' p.1 p.2 = 1 := by
    intro p hp
    have ha : p.1 ∈ T := (Finset.mem_product.mp hp).1
    have hb : p.2 ∈ S := (Finset.mem_product.mp hp).2
    have hne : p.1 ≠ p.2 := by
      intro h_eq
      have h : p.2 ∈ T := h_eq ▸ ha
      exact (Finset.disjoint_left.mp h_disj) hb h
    have h_before' : posOf p.2 B < posOf p.1 B ∧ posOf p.2 B' < posOf p.1 B' :=
      h_before p.2 hb p.1 ha
    have haB : p.1 ∈ B := h_inB p.1 (h_memI_T p.1 ha)
    have hbB : p.2 ∈ B := h_inB p.2 (h_memI_S p.2 hb)
    have haB' : p.1 ∈ B' := h_inB' p.1 (h_memI_T p.1 ha)
    have hbB' : p.2 ∈ B' := h_inB' p.2 (h_memI_S p.2 hb)
    have hnlt1 : ¬(posOf p.1 B < posOf p.2 B) := by omega
    have hnlt2 : ¬(posOf p.1 B' < posOf p.2 B') := by omega
    have h1 : orderFun B p.1 p.2 = -1 := by
      simp [orderFun, haB, hbB, hnlt1, h_before'.1]
    have h2 : orderFun B' p.1 p.2 = -1 := by
      simp [orderFun, haB', hbB', hnlt2, h_before'.2]
    rw [orderFun2, h1, h2] <;> norm_num
  -- Within S pairs have f2 = -1
  have h_within_S : ∀ p ∈ S.offDiag, orderFun2 B B' p.1 p.2 = -1 := by
    intro p hp
    have hpe : p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2 := Finset.mem_offDiag.mp hp
    rcases hpe with ⟨ha, hb, hne⟩
    exact orderFun2_different hB hB'
      (h_inB p.1 (h_memI_S p.1 ha))
      (h_inB p.2 (h_memI_S p.2 hb))
      (h_inB' p.1 (h_memI_S p.1 ha))
      (h_inB' p.2 (h_memI_S p.2 hb))
      hne (h_rev_S p.1 ha p.2 hb hne)
  -- Within T pairs have f2 = -1
  have h_within_T : ∀ p ∈ T.offDiag, orderFun2 B B' p.1 p.2 = -1 := by
    intro p hp
    have hpe : p.1 ∈ T ∧ p.2 ∈ T ∧ p.1 ≠ p.2 := Finset.mem_offDiag.mp hp
    rcases hpe with ⟨ha, hb, hne⟩
    exact orderFun2_different hB hB'
      (h_inB p.1 (h_memI_T p.1 ha))
      (h_inB p.2 (h_memI_T p.2 hb))
      (h_inB' p.1 (h_memI_T p.1 ha))
      (h_inB' p.2 (h_memI_T p.2 hb))
      hne (h_rev_T p.1 ha p.2 hb hne)
  -- Partition I.offDiag using offDiag_union
  have h_partition : I.offDiag = S.offDiag ∪ T.offDiag ∪ (S ×ˢ T) ∪ (T ×ˢ S) := by
    have h_union : (S ∪ T).offDiag = S.offDiag ∪ T.offDiag ∪ (S ×ˢ T) ∪ (T ×ˢ S) :=
      Finset.offDiag_union h_disj
    have h : I.offDiag = (S ∪ T).offDiag := by rw [hI]
    rw [h, h_union]
  -- Disjointness of the four parts
  have h_disj1 : Disjoint S.offDiag T.offDiag := by
    apply Finset.disjoint_left.mpr
    intro p hp1 hp2
    have h1 : p.1 ∈ S := (Finset.mem_offDiag.mp hp1).1
    have h2 : p.1 ∈ T := (Finset.mem_offDiag.mp hp2).1
    exact (Finset.disjoint_left.mp h_disj) h1 h2
  have h_disj2 : Disjoint (S.offDiag ∪ T.offDiag) (S ×ˢ T) := by
    apply Finset.disjoint_left.mpr
    intro p hp1 hp2
    have h21 : p.1 ∈ S := (Finset.mem_product.mp hp2).1
    have h22 : p.2 ∈ T := (Finset.mem_product.mp hp2).2
    rw [Finset.mem_union] at hp1
    rcases hp1 with (hp1 | hp1)
    · have h : p.2 ∈ S := (Finset.mem_offDiag.mp hp1).2.1
      exact (Finset.disjoint_left.mp h_disj) h h22
    · have h : p.1 ∈ T := (Finset.mem_offDiag.mp hp1).1
      exact (Finset.disjoint_left.mp h_disj) h21 h
  have h_disj3 : Disjoint (S.offDiag ∪ T.offDiag ∪ (S ×ˢ T)) (T ×ˢ S) := by
    apply Finset.disjoint_left.mpr
    intro p hp1 hp2
    have h21 : p.1 ∈ T := (Finset.mem_product.mp hp2).1
    have h22 : p.2 ∈ S := (Finset.mem_product.mp hp2).2
    rw [Finset.mem_union] at hp1
    rcases hp1 with (hp1 | hp1)
    · rw [Finset.mem_union] at hp1
      rcases hp1 with (h | h)
      · have h' : p.1 ∈ S := (Finset.mem_offDiag.mp h).1
        exact (Finset.disjoint_left.mp h_disj) h' h21
      · have h' : p.2 ∈ T := (Finset.mem_offDiag.mp h).2.1
        exact (Finset.disjoint_left.mp h_disj) h22 h'
    · have h' : p.1 ∈ S := (Finset.mem_product.mp hp1).1
      exact (Finset.disjoint_left.mp h_disj) h' h21
  -- Compute the sum
  rw [h_partition]
  rw [Finset.sum_union h_disj3, Finset.sum_union h_disj2, Finset.sum_union h_disj1]
  rw [Finset.sum_congr rfl h_within_S, Finset.sum_congr rfl h_within_T,
      Finset.sum_congr rfl h_cross1, Finset.sum_congr rfl h_cross2]
  have h_s_le : S.card ≤ S.card * S.card := by
    cases S.card with
    | zero => norm_num
    | succ k => simp [Nat.mul_succ]
  have h_t_le : T.card ≤ T.card * T.card := by
    cases T.card with
    | zero => norm_num
    | succ k => simp [Nat.mul_succ]
  have h_cast_s : ((S.card * S.card - S.card : ℕ) : ℤ) =
      (S.card : ℤ) * (S.card : ℤ) - (S.card : ℤ) := by
    rw [Nat.cast_sub h_s_le, Nat.cast_mul]
  have h_cast_t : ((T.card * T.card - T.card : ℕ) : ℤ) =
      (T.card : ℤ) * (T.card : ℤ) - (T.card : ℤ) := by
    rw [Nat.cast_sub h_t_le, Nat.cast_mul]
  have h_nsmul1 : ∀ (n : ℕ), n • (-1 : ℤ) = - (n : ℤ) := by
    intro n; simp
  have h_nsmul2 : ∀ (n : ℕ), n • (1 : ℤ) = (n : ℤ) := by
    intro n; simp
  have h_main : ∑ _ ∈ S.offDiag, (-1 : ℤ) + ∑ _ ∈ T.offDiag, (-1 : ℤ) +
      ∑ _ ∈ S ×ˢ T, (1 : ℤ) + ∑ _ ∈ T ×ˢ S, (1 : ℤ) ≤ (I.card : ℤ) := by
    simp only [Finset.sum_const, Finset.offDiag_card, Finset.card_product]
    rw [h_nsmul1 (S.card * S.card - S.card), h_nsmul1 (T.card * T.card - T.card),
        h_nsmul2 (S.card * T.card), h_nsmul2 (T.card * S.card)]
    rw [h_cast_s, h_cast_t, h_card]
    simp [Nat.cast_add, mul_comm]
    <;> ring_nf <;> nlinarith [sq_nonneg ((S.card : ℤ) - (T.card : ℤ))]
  exact h_main

end ReversalRotation

/-! ### Boundary-spanning helper -/

/--
At most one block from a totally-ordered disjoint family contains elements
from both S and T, when every S element precedes every T element in `l`.
-/
private lemma at_most_one_intersects_both {α : Type*} [DecidableEq α]
    (l : List α) (B : ℕ → List α) (indices : Finset ℕ)
    (h_total : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      (∀ x ∈ B i, ∀ y ∈ B j, posOf x l < posOf y l) ∨
      (∀ x ∈ B j, ∀ y ∈ B i, posOf x l < posOf y l))
    (S T : Finset α)
    (hST : ∀ s ∈ S, ∀ t ∈ T, posOf s l < posOf t l) :
    ∃ i0 : ℕ, ∀ i ∈ indices,
      (∃ s ∈ S, s ∈ B i) → (∃ t ∈ T, t ∈ B i) → i = i0 := by
  by_cases h : ∃ i ∈ indices,
      (∃ s ∈ S, s ∈ B i) ∧ (∃ t ∈ T, t ∈ B i)
  · rcases h with ⟨i0, hi0, ⟨s0, hs0, hs0B⟩, ⟨t0, ht0, ht0B⟩⟩
    refine' ⟨i0, _⟩
    intro i hi hS hT
    by_cases h_eq : i = i0
    · exact h_eq
    · rcases hS with ⟨s, hs, hsB⟩
      rcases hT with ⟨t, ht, htB⟩
      have h_order' := h_total i hi i0 hi0 h_eq
      rcases h_order' with (h_before | h_after)
      · have h1 : posOf t l < posOf s0 l := h_before t htB s0 hs0B
        have h2 : posOf s0 l < posOf t l := hST s0 hs0 t ht
        exact False.elim (lt_asymm h1 h2)
      · have h1 : posOf t0 l < posOf s l := h_after t0 ht0B s hsB
        have h2 : posOf s l < posOf t0 l := hST s hs t0 ht0
        exact False.elim (lt_asymm h1 h2)
  · exact ⟨0, fun i hi hS hT => False.elim (h ⟨i, hi, hS, hT⟩)⟩

end MarcusTardos
