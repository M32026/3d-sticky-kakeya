import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Definitions
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.OrderFunction
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.LeaderConfig
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Direct bound on S^{ij} via flip analysis

For a pair of cyclically IR sequences, each dyadic block pair has
orderFun2 sum ≤ intersection cardinality. This follows from analyzing
how rotation cuts flip the relative order of element pairs.

## Key lemma
- `orderFun_rotation_flip`: order flips iff exactly one element crosses cut

## Whiteprint node
- `DirectBound`
-/

namespace MarcusTardos.DirectBound

open BigOperators Finset LeaderConfig

variable {α : Type*} [DecidableEq α]

/-! ### posOf on append -/

/-- If x is in the left part, posOf on append equals posOf on left. -/
private lemma posOf_append_left {x : α} {L1 L2 : List α} (h1 : x ∈ L1) :
    posOf x (L1 ++ L2) = posOf x L1 := by
  have h_main : ∀ (L : List α), x ∈ L → posOf x (L ++ L2) = posOf x L := by
    intro L
    induction L with
    | nil => intro h; contradiction
    | cons a L ih =>
      intro h_in
      by_cases hxa : a = x
      · simp [posOf, hxa]
      · have h4 : x ∈ L := by
          simp only [List.mem_cons] at h_in <;> tauto
        have h_ih := ih h4
        simp [posOf, hxa, h_ih]
  exact h_main L1 h1

/-- If x is not in the left part, posOf on append shifts by left length. -/
private lemma posOf_append_right {x : α} {L1 L2 : List α} (h1 : x ∉ L1) (h2 : x ∈ L2) :
    posOf x (L1 ++ L2) = L1.length + posOf x L2 := by
  have h_main : ∀ (L : List α), x ∉ L → posOf x (L ++ L2) = L.length + posOf x L2 := by
    intro L
    induction L with
    | nil =>
      intro h
      simp [posOf]
    | cons a L ih =>
      intro h_notin
      have h3 : a ≠ x := by intro h; exact h_notin (by simp [h])
      have h4 : x ∉ L := by
        simp only [List.mem_cons] at h_notin <;> tauto
      have h_ih := ih h4
      simp [posOf, h3, h_ih, List.length_cons] <;> ring
  exact h_main L1 h1

/-! ### Flip property under rotation -/

/--
Flip lemma: for x,y ∈ A, their order is flipped by rotation at n iff
exactly one is in take n and the other in drop n.
-/
lemma orderFun_rotation_flip {A : List α} (hA : A.Nodup) (n : ℕ) {x y : α}
    (hx : x ∈ A) (hy : y ∈ A) (hne : x ≠ y) :
    orderFun A x y = -orderFun (A.drop n ++ A.take n) x y ↔
      ((x ∈ A.take n ∧ y ∈ A.drop n) ∨ (x ∈ A.drop n ∧ y ∈ A.take n)) := by
  let L := A.drop n
  let R := A.take n
  let A_rot := L ++ R
  have h_disj : List.Disjoint R L := by
    have h : (R ++ L).Nodup := by rw [List.take_append_drop] <;> exact hA
    exact (List.nodup_append').mp h |>.2.2
  have h_posOf_take : ∀ {z : α}, z ∈ R →
      posOf z A_rot = L.length + posOf z A := by
    intro z hz
    have h1 : z ∉ L := h_disj hz
    have h2 : posOf z R = posOf z A := posOf_take_eq hA hz
    rw [posOf_append_right h1 hz, h2]
  have h_posOf_drop : ∀ {z : α}, z ∈ L →
      posOf z A_rot = posOf z A - n := by
    intro z hz
    have h1 : posOf z A = n + posOf z L := posOf_drop_eq hA hz
    have h2 : posOf z A_rot = posOf z L := posOf_append_left hz
    rw [h2]
    have h3 : posOf z L = posOf z A - n := by omega
    exact h3
  have hlen : L.length = A.length - n := by simp [L]
  have h_xin_rot : x ∈ A_rot := by
    change x ∈ L ++ R
    have h : x ∈ R ++ L := by rw [List.take_append_drop] <;> exact hx
    have h' : x ∈ R ∨ x ∈ L := List.mem_append.mp h
    rcases h' with (hR | hL)
    · exact List.mem_append.mpr (Or.inr hR)
    · exact List.mem_append.mpr (Or.inl hL)
  have h_yin_rot : y ∈ A_rot := by
    change y ∈ L ++ R
    have h : y ∈ R ++ L := by rw [List.take_append_drop] <;> exact hy
    have h' : y ∈ R ∨ y ∈ L := List.mem_append.mp h
    rcases h' with (hR | hL)
    · exact List.mem_append.mpr (Or.inr hR)
    · exact List.mem_append.mpr (Or.inl hL)
  have h_orderFun_eq : ∀ {a b : α}, a ∈ A → b ∈ A → a ≠ b →
      (posOf a A < posOf b A ↔ posOf a A_rot < posOf b A_rot) →
      orderFun A a b = orderFun A_rot a b := by
    intro a b ha hb hne' h_iff
    have ha_rot : a ∈ A_rot := by
      change a ∈ L ++ R
      have h : a ∈ R ++ L := by rw [List.take_append_drop] <;> exact ha
      have h' : a ∈ R ∨ a ∈ L := List.mem_append.mp h
      rcases h' with (hR | hL)
      · exact List.mem_append.mpr (Or.inr hR)
      · exact List.mem_append.mpr (Or.inl hL)
    have hb_rot : b ∈ A_rot := by
      change b ∈ L ++ R
      have h : b ∈ R ++ L := by rw [List.take_append_drop] <;> exact hb
      have h' : b ∈ R ∨ b ∈ L := List.mem_append.mp h
      rcases h' with (hR | hL)
      · exact List.mem_append.mpr (Or.inr hR)
      · exact List.mem_append.mpr (Or.inl hL)
    by_cases h6 : posOf a A < posOf b A
    · have h7 : posOf a A_rot < posOf b A_rot := h_iff.mp h6
      simp [orderFun, ha, hb, ha_rot, hb_rot, h6, h7]
    · have h7 : ¬(posOf a A_rot < posOf b A_rot) := by
        intro h8; exact h6 (h_iff.mpr h8)
      simp [orderFun, ha, hb, ha_rot, hb_rot, h6, h7]
  constructor
  · -- Assume order is flipped, prove one is take and one is drop
    intro h
    by_cases hxt : x ∈ R
    · by_cases hyt : y ∈ R
      · -- both in take: order not flipped, contradiction
        have hx' := h_posOf_take hxt
        have hy' := h_posOf_take hyt
        have h4 : posOf x A < posOf y A ↔ posOf x A_rot < posOf y A_rot := by
          rw [hx', hy'] <;> omega
        have h5 : orderFun A x y = orderFun A_rot x y := h_orderFun_eq hx hy hne h4
        rw [h5] at h
        have h6 : orderFun A_rot x y ≠ 0 := by
          intro h_eq0
          have h_contra : x ∉ A_rot ∨ y ∉ A_rot := orderFun_eq_zero_iff.mp h_eq0
          rcases h_contra with (h | h)
          · exact h h_xin_rot
          · exact h h_yin_rot
        have h7 : orderFun A_rot x y = 0 := by linarith
        exact False.elim (h6 h7)
      · -- x in take, y not in take ⇒ y in drop
        have hyd : y ∈ L := by
          have h : y ∈ R ++ L := by rw [List.take_append_drop] <;> exact hy
          exact (List.mem_append.mp h).resolve_left hyt
        exact Or.inl ⟨hxt, hyd⟩
    · -- x not in take ⇒ x in drop
      have hxd : x ∈ L := by
        have h : x ∈ R ++ L := by rw [List.take_append_drop] <;> exact hx
        exact (List.mem_append.mp h).resolve_left hxt
      by_cases hyt : y ∈ R
      · exact Or.inr ⟨hxd, hyt⟩
      · -- both in drop: order not flipped, contradiction
        have hyd : y ∈ L := by
          have h : y ∈ R ++ L := by rw [List.take_append_drop] <;> exact hy
          exact (List.mem_append.mp h).resolve_left hyt
        have hx' := h_posOf_drop hxd
        have hy' := h_posOf_drop hyd
        have h_xge : n ≤ posOf x A := posOf_ge_of_mem_drop hA hxd
        have h_yge : n ≤ posOf y A := posOf_ge_of_mem_drop hA hyd
        have h4 : posOf x A < posOf y A ↔ posOf x A_rot < posOf y A_rot := by
          rw [hx', hy']
          have h9 : n ≤ posOf x A := h_xge
          have h10 : n ≤ posOf y A := h_yge
          constructor <;> intro h <;> omega
        have h5 : orderFun A x y = orderFun A_rot x y := h_orderFun_eq hx hy hne h4
        rw [h5] at h
        have h6 : orderFun A_rot x y ≠ 0 := by
          intro h_eq0
          have h_contra : x ∉ A_rot ∨ y ∉ A_rot := orderFun_eq_zero_iff.mp h_eq0
          rcases h_contra with (h | h)
          · exact h h_xin_rot
          · exact h h_yin_rot
        have h7 : orderFun A_rot x y = 0 := by linarith
        exact False.elim (h6 h7)
  · -- Assume one take one drop, prove order flipped
    rintro (⟨hxt, hyd⟩ | ⟨hxd, hyt⟩)
    · -- x take, y drop
      have hx' := h_posOf_take hxt
      have hy' := h_posOf_drop hyd
      have h5 : posOf x A < n := posOf_lt_of_mem_take hA hxt
      have h6 : n ≤ posOf y A := posOf_ge_of_mem_drop hA hyd
      have h4 : posOf x A < posOf y A := by omega
      have h_y_lt : posOf y A < A.length := posOf_lt_length hy
      have h7 : posOf y A_rot < posOf x A_rot := by
        rw [hy', hx', hlen]
        omega
      have h8 : orderFun A x y = 1 := by
        simp [orderFun, hx, hy, h4]
      have h9 : orderFun A_rot x y = -1 := by
        have h10 : ¬(posOf x A_rot < posOf y A_rot) := by
          intro h11; exact lt_asymm h7 h11
        simp [orderFun, h_xin_rot, h_yin_rot, h10, h7]
      rw [h8, h9] <;> norm_num
    · -- x drop, y take
      have hx' := h_posOf_drop hxd
      have hy' := h_posOf_take hyt
      have h5 : posOf y A < n := posOf_lt_of_mem_take hA hyt
      have h6 : n ≤ posOf x A := posOf_ge_of_mem_drop hA hxd
      have h4 : posOf y A < posOf x A := by omega
      have h_x_lt : posOf x A < A.length := posOf_lt_length hx
      have h7 : posOf x A_rot < posOf y A_rot := by
        rw [hx', hy', hlen]
        omega
      have h8 : orderFun A x y = -1 := by
        have h10 : ¬(posOf x A < posOf y A) := by
          intro h11; exact lt_asymm h4 h11
        simp [orderFun, hx, hy, h10]
      have h9 : orderFun A_rot x y = 1 := by
        simp [orderFun, h_xin_rot, h_yin_rot, h7]
      rw [h8, h9] <;> norm_num

end MarcusTardos.DirectBound
