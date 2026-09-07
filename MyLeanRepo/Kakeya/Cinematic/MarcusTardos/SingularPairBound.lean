import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Definitions
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.OrderFunction
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.DyadicDecomposition
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.BlockStructure
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.TransitionSpanning
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.DirectBound
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.SameCrossCharacterization
import Mathlib.Tactic
import Mathlib.Data.Finset.Card

/-!
# At most one singular block pair per level

For cyclically IR nodup lists A, B, prove that at each dyadic level l,
at most one block pair is not intersection reverse.
-/

namespace MarcusTardos.SingularPairBound

open BigOperators Finset TransitionSpanning

variable {α : Type*} [DecidableEq α]

/-! ### Helper lemmas -/

/-- Rotation preserves nodup. -/
private lemma rot_nodup {A : List α} (hA : A.Nodup) (n : ℕ) :
    (A.drop n ++ A.take n).Nodup := by
  have h1 : (A.drop n).Nodup := hA.sublist (List.drop_sublist n A)
  have h2 : (A.take n).Nodup := hA.sublist (List.take_sublist n A)
  have h3 : List.Disjoint (A.take n) (A.drop n) := by
    have h : (A.take n ++ A.drop n).Nodup := by
      rw [List.take_append_drop] <;> exact hA
    exact (List.nodup_append').mp h |>.2.2
  exact (List.nodup_append').mpr ⟨h1, h2, h3.symm⟩

/-- orderFun returns ±1 when both elements are in the list and distinct. -/
private lemma orderFun_values {A : List α} {x y : α}
    (hx : x ∈ A) (hy : y ∈ A) (_hne : x ≠ y) :
    orderFun A x y = 1 ∨ orderFun A x y = -1 := by
  have h_not : ¬(x ∉ A ∨ y ∉ A) := by tauto
  by_cases hlt : posOf x A < posOf y A
  · left; rw [orderFun, if_neg h_not, if_pos hlt]
  · right; rw [orderFun, if_neg h_not, if_neg hlt]

/-- Propositional XOR equivalence for Same/Cross characterization. -/
private lemma xor_equiv (a1 a2 b1 b2 : Prop) [Decidable a1] [Decidable a2] [Decidable b1] [Decidable b2] :
    (((a1 ∧ ¬a2) ∨ (¬a1 ∧ a2)) ∧ ¬((b1 ∧ ¬b2) ∨ (¬b1 ∧ b2)) ∨
     (¬((a1 ∧ ¬a2) ∨ (¬a1 ∧ a2))) ∧ ((b1 ∧ ¬b2) ∨ (¬b1 ∧ b2))) ↔
    ((((a1 ∧ b1) ∨ (¬a1 ∧ ¬b1)) ∧ ((a2 ∧ ¬b2) ∨ (¬a2 ∧ b2))) ∨
     (((a1 ∧ ¬b1) ∨ (¬a1 ∧ b1)) ∧ ((a2 ∧ b2) ∨ (¬a2 ∧ ¬b2)))) := by
  by_cases h1 : a1 <;> by_cases h2 : a2 <;> by_cases h3 : b1 <;> by_cases h4 : b2 <;>
    simp [h1, h2, h3, h4]

/-- Converse of orderFun2_different: orderFun2=-1 iff posOf order is reversed. -/
private lemma orderFun2_eq_neg_one_iff {B B' : List α} (hB : B.Nodup) (hB' : B'.Nodup)
    {a b : α} (ha : a ∈ B) (hb : b ∈ B) (ha' : a ∈ B') (hb' : b ∈ B') (hne : a ≠ b) :
    orderFun2 B B' a b = -1 ↔ ((posOf a B < posOf b B) ↔ (posOf b B' < posOf a B')) := by
  constructor
  · intro h
    have hne_B : posOf a B ≠ posOf b B := posOf_nodup_ne hB ha hb hne
    have hne_B' : posOf a B' ≠ posOf b B' := posOf_nodup_ne hB' ha' hb' hne
    constructor
    · intro hlt
      have h1 : orderFun B a b = 1 := by simp [orderFun, ha, hb, hlt]
      have h2 : orderFun B' a b = -1 := by
        simp only [orderFun2] at h; rw [h1] at h; linarith
      simp [orderFun, ha', hb'] at h2 <;> omega
    · intro hrev
      have h1 : orderFun B' a b = -1 := by simp [orderFun, ha', hb', hrev] <;> omega
      have h2 : orderFun B a b = 1 := by
        simp only [orderFun2] at h; rw [h1] at h; linarith
      simp [orderFun, ha, hb] at h2 <;> omega
  · intro h
    exact orderFun2_different hB hB' ha hb ha' hb' hne h

/-! ### Same/Cross orderFun2 characterization (from dune) -/

/--
For cyclically IR lists with rotation cuts, `orderFun2 A B x y = 1` iff
one element is in `Same` and the other in `Cross`.
-/
lemma orderFun2_same_cross_iff {A B A_rot B_rot : List α} {n m : ℕ}
    (hA : A.Nodup) (hB : B.Nodup)
    (hA_rot : A_rot = A.drop n ++ A.take n)
    (hB_rot : B_rot = B.drop m ++ B.take m)
    (hIR : IsIntersectionReverse A_rot B_rot)
    {x y : α} (hxI : x ∈ A.toFinset ∩ B.toFinset)
    (hyI : y ∈ A.toFinset ∩ B.toFinset) (hne : x ≠ y) :
    let takeA := (A.take n).toFinset
    let dropA := (A.drop n).toFinset
    let takeB := (B.take m).toFinset
    let dropB := (B.drop m).toFinset
    let Same := (A.toFinset ∩ B.toFinset ∩ takeA ∩ takeB) ∪
                (A.toFinset ∩ B.toFinset ∩ dropA ∩ dropB)
    let Cross := (A.toFinset ∩ B.toFinset ∩ takeA ∩ dropB) ∪
                 (A.toFinset ∩ B.toFinset ∩ dropA ∩ takeB)
    (orderFun2 A B x y = 1 ↔ (x ∈ Same ∧ y ∈ Cross) ∨ (x ∈ Cross ∧ y ∈ Same)) := by
  exact SameCrossCharacterization.orderFun2_same_cross_iff hA hB hA_rot hB_rot hIR hxI hyI hne

/-! ### Order helpers for append and sublists -/

private lemma posOf_append_left {x : α} {L1 L2 : List α} (h1 : x ∈ L1) :
    posOf x (L1 ++ L2) = posOf x L1 := by
  induction L1 with
  | nil => contradiction
  | cons a L1 ih =>
    by_cases hxa : a = x
    · simp [posOf, hxa]
    · have h4 : x ∈ L1 := by simp [List.mem_cons, hxa] at h1 <;> tauto
      simp [posOf, hxa, ih h4]

private lemma posOf_append_right {x : α} {L1 L2 : List α} (h1 : x ∉ L1) (h2 : x ∈ L2) :
    posOf x (L1 ++ L2) = L1.length + posOf x L2 := by
  induction L1 with
  | nil => simp [posOf]
  | cons a L1 ih =>
    have h3 : a ≠ x := by intro h; exact h1 (by simp [h])
    have h4 : x ∉ L1 := by simp [List.mem_cons, h3] at h1 <;> tauto
    simp [posOf, h3, ih h4, List.length_cons] <;> ring

/-- In `L1 ++ L2` with disjoint parts, any element of `L1` precedes any element of `L2`. -/
private lemma posOf_left_before_right {L1 L2 : List α} (h_disj : List.Disjoint L1 L2)
    {x y : α} (hx : x ∈ L1) (hy : y ∈ L2) :
    posOf x (L1 ++ L2) < posOf y (L1 ++ L2) := by
  have h_y_not_L1 : y ∉ L1 := fun hyL1 => h_disj hyL1 hy
  have h1 : posOf x (L1 ++ L2) = posOf x L1 := posOf_append_left hx
  have h2 : posOf y (L1 ++ L2) = L1.length + posOf y L2 := posOf_append_right h_y_not_L1 hy
  rw [h1, h2]
  have h3 : posOf x L1 < L1.length := posOf_lt_length hx
  omega

/-- Transfer posOf order between two lists via a common sublist. -/
private lemma posOf_transfer {A B C : List α} (hA : A.Nodup) (hB : B.Nodup)
    (hC_A : C.Sublist A) (hC_B : C.Sublist B) {x y : α}
    (hx : x ∈ C) (hy : y ∈ C) (hne : x ≠ y) :
    (posOf x A < posOf y A) ↔ (posOf x B < posOf y B) := by
  have h1 := posOf_sublist_lt hC_A hA hx hy hne
  have h2 := posOf_sublist_lt hC_B hB hx hy hne
  exact h1.symm.trans h2

/-- take/drop are disjoint for nodup lists. -/
private lemma take_drop_disjoint {A : List α} (hA : A.Nodup) (n : ℕ) :
    List.Disjoint (A.take n) (A.drop n) := by
  have h : (A.take n ++ A.drop n).Nodup := by rw [List.take_append_drop] <;> exact hA
  exact (List.nodup_append').mp h |>.2.2

/-! ### Singular block pair characterization -/

/-- If block pair intersection is all Same or all Cross, it is IR. -/
lemma block_pair_ir_if_subset {A B : List α} (hA : A.Nodup) (hB : B.Nodup)
    (Same Cross : Finset α) (h_disj : Disjoint Same Cross)
    (h_char : ∀ {x y : α}, x ∈ A.toFinset ∩ B.toFinset →
      y ∈ A.toFinset ∩ B.toFinset → x ≠ y →
      (orderFun2 A B x y = 1 ↔ (x ∈ Same ∧ y ∈ Cross) ∨ (x ∈ Cross ∧ y ∈ Same)))
    {s t : List Bool}
    (h_sub : ((block A s).toFinset ∩ (block B t).toFinset) ⊆ Same ∨
             ((block A s).toFinset ∩ (block B t).toFinset) ⊆ Cross) :
    IsIntersectionReverse (block A s) (block B t) := by
  let I_st : Finset α := (block A s).toFinset ∩ (block B t).toFinset
  have hA_block : (block A s).Nodup := hA.sublist (block_sublist A s)
  have hB_block : (block B t).Nodup := hB.sublist (block_sublist B t)
  intro a ha b hb hne ha' hb'
  have haI : a ∈ I_st := by
    simp only [I_st, Finset.mem_inter, List.mem_toFinset] <;> exact ⟨ha, ha'⟩
  have hbI : b ∈ I_st := by
    simp only [I_st, Finset.mem_inter, List.mem_toFinset] <;> exact ⟨hb, hb'⟩
  have haI' : a ∈ A.toFinset ∩ B.toFinset := by
    have h1 : a ∈ A := (block_sublist A s).subset ha
    have h2 : a ∈ B := (block_sublist B t).subset ha'
    simp [List.mem_toFinset, h1, h2]
  have hbI' : b ∈ A.toFinset ∩ B.toFinset := by
    have h1 : b ∈ A := (block_sublist A s).subset hb
    have h2 : b ∈ B := (block_sublist B t).subset hb'
    simp [List.mem_toFinset, h1, h2]
  have h_both_same : (a ∈ Same ∧ b ∈ Same) ∨ (a ∈ Cross ∧ b ∈ Cross) := by
    rcases h_sub with (h_sub | h_sub)
    · exact Or.inl ⟨h_sub haI, h_sub hbI⟩
    · exact Or.inr ⟨h_sub haI, h_sub hbI⟩
  have h_not1 : ¬((a ∈ Same ∧ b ∈ Cross) ∨ (a ∈ Cross ∧ b ∈ Same)) := by
    rcases h_both_same with (h | h)
    · have h_a_not_Cross : a ∉ Cross := Finset.disjoint_left.mp h_disj h.1
      have h_b_not_Cross : b ∉ Cross := Finset.disjoint_left.mp h_disj h.2
      intro h2; rcases h2 with (h2 | h2)
      · exact h_b_not_Cross h2.2
      · exact h_a_not_Cross h2.1
    · have h_a_not_Same : a ∉ Same := Finset.disjoint_right.mp h_disj h.1
      have h_b_not_Same : b ∉ Same := Finset.disjoint_right.mp h_disj h.2
      intro h2; rcases h2 with (h2 | h2)
      · exact h_a_not_Same h2.1
      · exact h_b_not_Same h2.2
  have h_char' : orderFun2 A B a b = 1 ↔ _ := h_char haI' hbI' hne
  have h_ne1 : orderFun2 A B a b ≠ 1 := mt h_char'.mp h_not1
  have h_vals : orderFun A a b = 1 ∨ orderFun A a b = -1 :=
    orderFun_values ((block_sublist A s).subset ha) ((block_sublist A s).subset hb) hne
  have h_vals2 : orderFun B a b = 1 ∨ orderFun B a b = -1 :=
    orderFun_values ((block_sublist B t).subset ha') ((block_sublist B t).subset hb') hne
  have h_eq_neg1 : orderFun2 A B a b = -1 := by
    rcases h_vals with (h1 | h1) <;> rcases h_vals2 with (h2 | h2) <;>
      simp [orderFun2, h1, h2] at h_ne1 ⊢ <;> tauto
  have h_rev : (posOf a A < posOf b A) ↔ (posOf b B < posOf a B) :=
    (orderFun2_eq_neg_one_iff hA hB
      ((block_sublist A s).subset ha) ((block_sublist A s).subset hb)
      ((block_sublist B t).subset ha') ((block_sublist B t).subset hb') hne).mp h_eq_neg1
  have h1 : posOf a (block A s) < posOf b (block A s) ↔ posOf a A < posOf b A :=
    posOf_sublist_lt (block_sublist A s) hA ha hb hne
  have h2 : posOf b (block B t) < posOf a (block B t) ↔ posOf b B < posOf a B :=
    posOf_sublist_lt (block_sublist B t) hB hb' ha' hne.symm
  rw [h1, h2]
  exact h_rev

/-! ### Main result: at most one singular block pair -/

/-- At most one dyadic block pair at level `l` fails to be intersection reverse. -/
lemma at_most_one_singular_pair {A B : List α} (hA : A.Nodup) (hB : B.Nodup)
    (hcir : IsCyclicIntersectionReverse A B) (l : ℕ) :
    ∃ (st0 : List Bool × List Bool),
      ∀ (s t : List Bool), s.length = l → t.length = l →
        ¬ IsIntersectionReverse (block A s) (block B t) → (s, t) = st0 := by
  rcases hcir with ⟨A_rot, B_rot, ⟨n, hA_rot⟩, ⟨m, hB_rot⟩, hIR⟩
  let I := A.toFinset ∩ B.toFinset
  let takeA := (A.take n).toFinset
  let dropA := (A.drop n).toFinset
  let takeB := (B.take m).toFinset
  let dropB := (B.drop m).toFinset
  let Q11 := I ∩ takeA ∩ takeB
  let Q00 := I ∩ dropA ∩ dropB
  let Q10 := I ∩ takeA ∩ dropB
  let Q01 := I ∩ dropA ∩ takeB
  let Same : Finset α := Q11 ∪ Q00
  let Cross : Finset α := Q10 ∪ Q01

  have hQ11_sub_I : Q11 ⊆ I := by
    intro z hz; have h1 : z ∈ I ∩ takeA := (Finset.mem_inter.mp hz).1
    exact (Finset.mem_inter.mp h1).1
  have hQ00_sub_I : Q00 ⊆ I := by
    intro z hz; have h1 : z ∈ I ∩ dropA := (Finset.mem_inter.mp hz).1
    exact (Finset.mem_inter.mp h1).1
  have hQ10_sub_I : Q10 ⊆ I := by
    intro z hz; have h1 : z ∈ I ∩ takeA := (Finset.mem_inter.mp hz).1
    exact (Finset.mem_inter.mp h1).1
  have hQ01_sub_I : Q01 ⊆ I := by
    intro z hz; have h1 : z ∈ I ∩ dropA := (Finset.mem_inter.mp hz).1
    exact (Finset.mem_inter.mp h1).1
  have hSame_sub_I : Same ⊆ I := Finset.union_subset hQ11_sub_I hQ00_sub_I
  have hCross_sub_I : Cross ⊆ I := Finset.union_subset hQ10_sub_I hQ01_sub_I
  have hSame_A : Same ⊆ A.toFinset := by
    intro z hz; have hzI : z ∈ I := hSame_sub_I hz; exact (Finset.mem_inter.mp hzI).1
  have hCross_A : Cross ⊆ A.toFinset := by
    intro z hz; have hzI : z ∈ I := hCross_sub_I hz; exact (Finset.mem_inter.mp hzI).1
  have hSame_B : Same ⊆ B.toFinset := by
    intro z hz; have hzI : z ∈ I := hSame_sub_I hz; exact (Finset.mem_inter.mp hzI).2
  have hCross_B : Cross ⊆ B.toFinset := by
    intro z hz; have hzI : z ∈ I := hCross_sub_I hz; exact (Finset.mem_inter.mp hzI).2
  have h_quad : Q11 = ∅ ∨ Q00 = ∅ := by
    by_cases h11 : Q11 = ∅
    · exact Or.inl h11
    · have h_main : ∀ y, y ∉ Q00 := by
        intro y
        by_contra hy
        rcases Finset.nonempty_iff_ne_empty.mpr h11 with ⟨x, hx⟩
        have hx1 : x ∈ I ∩ takeA := (Finset.mem_inter.mp hx).1
        have hx_takeB : x ∈ takeB := (Finset.mem_inter.mp hx).2
        have hx_I : x ∈ I := (Finset.mem_inter.mp hx1).1
        have hx_takeA : x ∈ takeA := (Finset.mem_inter.mp hx1).2
        have hy1 : y ∈ I ∩ dropA := (Finset.mem_inter.mp hy).1
        have hy_dropB : y ∈ dropB := (Finset.mem_inter.mp hy).2
        have hy_I : y ∈ I := (Finset.mem_inter.mp hy1).1
        have hy_dropA : y ∈ dropA := (Finset.mem_inter.mp hy1).2
        have hxA : x ∈ A := by simpa [I, List.mem_toFinset] using (Finset.mem_inter.mp hx_I).1
        have hxB : x ∈ B := by simpa [I, List.mem_toFinset] using (Finset.mem_inter.mp hx_I).2
        have hyA : y ∈ A := by simpa [I, List.mem_toFinset] using (Finset.mem_inter.mp hy_I).1
        have hyB : y ∈ B := by simpa [I, List.mem_toFinset] using (Finset.mem_inter.mp hy_I).2
        have hx_takeA' : x ∈ A.take n := by simpa [takeA, List.mem_toFinset] using hx_takeA
        have hx_takeB' : x ∈ B.take m := by simpa [takeB, List.mem_toFinset] using hx_takeB
        have hy_dropA' : y ∈ A.drop n := by simpa [dropA, List.mem_toFinset] using hy_dropA
        have hy_dropB' : y ∈ B.drop m := by simpa [dropB, List.mem_toFinset] using hy_dropB
        have h_disjA : List.Disjoint (A.drop n) (A.take n) := (take_drop_disjoint hA n).symm
        have h_disjB : List.Disjoint (B.drop m) (B.take m) := (take_drop_disjoint hB m).symm
        have hne : x ≠ y := by
          intro h; rw [h] at hx_takeA'; exact (take_drop_disjoint hA n) hx_takeA' hy_dropA'
        have h_y_before_x_Arot : posOf y A_rot < posOf x A_rot := by
          rw [hA_rot]; exact posOf_left_before_right h_disjA hy_dropA' hx_takeA'
        have h_y_before_x_Brot : posOf y B_rot < posOf x B_rot := by
          rw [hB_rot]; exact posOf_left_before_right h_disjB hy_dropB' hx_takeB'
        have hy_Arot : y ∈ A_rot := by rw [hA_rot]; exact List.mem_append_left _ hy_dropA'
        have hx_Arot : x ∈ A_rot := by rw [hA_rot]; exact List.mem_append_right _ hx_takeA'
        have hy_Brot : y ∈ B_rot := by rw [hB_rot]; exact List.mem_append_left _ hy_dropB'
        have hx_Brot : x ∈ B_rot := by rw [hB_rot]; exact List.mem_append_right _ hx_takeB'
        have hIR' : posOf y A_rot < posOf x A_rot ↔ posOf x B_rot < posOf y B_rot :=
          hIR y hy_Arot x hx_Arot hne.symm hy_Brot hx_Brot
        have h_contra : posOf x B_rot < posOf y B_rot := hIR'.mp h_y_before_x_Arot
        exact lt_asymm h_y_before_x_Brot h_contra
      have hQ00 : Q00 = ∅ := by
        by_contra h
        have hne : Q00.Nonempty := Finset.nonempty_iff_ne_empty.mpr h
        rcases hne with ⟨y, hy⟩
        exact h_main y hy
      exact Or.inr hQ00
  have h_partition : Same ∪ Cross = I := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset hSame_sub_I hCross_sub_I
    · intro z hz
      have hzA : z ∈ A := by simpa [I, List.mem_toFinset] using (Finset.mem_inter.mp hz).1
      have hzB : z ∈ B := by simpa [I, List.mem_toFinset] using (Finset.mem_inter.mp hz).2
      have h1 : z ∈ takeA ∨ z ∈ dropA := by
        have h2 : z ∈ A.take n ∨ z ∈ A.drop n := List.mem_append.mp (by rw [List.take_append_drop] <;> exact hzA)
        rcases h2 with (h2 | h2) <;> simp [takeA, dropA, List.mem_toFinset, h2]
      have h2 : z ∈ takeB ∨ z ∈ dropB := by
        have h3 : z ∈ B.take m ∨ z ∈ B.drop m := List.mem_append.mp (by rw [List.take_append_drop] <;> exact hzB)
        rcases h3 with (h3 | h3) <;> simp [takeB, dropB, List.mem_toFinset, h3]
      rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2)
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (by simp [Q11, Finset.mem_inter, hz, h1, h2]))))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl (by simp [Q10, Finset.mem_inter, hz, h1, h2]))))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (by simp [Q01, Finset.mem_inter, hz, h1, h2]))))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (by simp [Q00, Finset.mem_inter, hz, h1, h2]))))
  have h_take_drop_A_disj : Disjoint takeA dropA := by
    have h : List.Disjoint (A.take n) (A.drop n) := by
      have h' : (A.take n ++ A.drop n).Nodup := by rw [List.take_append_drop] <;> exact hA
      exact (List.nodup_append').mp h' |>.2.2
    apply Finset.disjoint_left.mpr
    intro x hx1 hx2
    have h1 : x ∈ A.take n := by simpa [takeA, List.mem_toFinset] using hx1
    have h2 : x ∈ A.drop n := by simpa [dropA, List.mem_toFinset] using hx2
    exact h h1 h2
  have h_take_drop_B_disj : Disjoint takeB dropB := by
    have h : List.Disjoint (B.take m) (B.drop m) := by
      have h' : (B.take m ++ B.drop m).Nodup := by rw [List.take_append_drop] <;> exact hB
      exact (List.nodup_append').mp h' |>.2.2
    apply Finset.disjoint_left.mpr
    intro x hx1 hx2
    have h1 : x ∈ B.take m := by simpa [takeB, List.mem_toFinset] using hx1
    have h2 : x ∈ B.drop m := by simpa [dropB, List.mem_toFinset] using hx2
    exact h h1 h2
  have h_disj : Disjoint Same Cross := by
    have h11_10 : Disjoint Q11 Q10 := by
      apply Finset.disjoint_left.mpr
      intro z hz1 hz2
      have hzB1 : z ∈ takeB := (Finset.mem_inter.mp hz1).2
      have hzB2 : z ∈ dropB := (Finset.mem_inter.mp hz2).2
      exact Finset.disjoint_left.mp h_take_drop_B_disj hzB1 hzB2
    have h11_01 : Disjoint Q11 Q01 := by
      apply Finset.disjoint_left.mpr
      intro z hz1 hz2
      have hzA1 : z ∈ takeA := (Finset.mem_inter.mp (Finset.mem_inter.mp hz1).1).2
      have hzA2 : z ∈ dropA := (Finset.mem_inter.mp (Finset.mem_inter.mp hz2).1).2
      exact Finset.disjoint_left.mp h_take_drop_A_disj hzA1 hzA2
    have h00_10 : Disjoint Q00 Q10 := by
      apply Finset.disjoint_left.mpr
      intro z hz1 hz2
      have hzA1 : z ∈ dropA := (Finset.mem_inter.mp (Finset.mem_inter.mp hz1).1).2
      have hzA2 : z ∈ takeA := (Finset.mem_inter.mp (Finset.mem_inter.mp hz2).1).2
      exact Finset.disjoint_left.mp h_take_drop_A_disj hzA2 hzA1
    have h00_01 : Disjoint Q00 Q01 := by
      apply Finset.disjoint_left.mpr
      intro z hz1 hz2
      have hzB1 : z ∈ dropB := (Finset.mem_inter.mp hz1).2
      have hzB2 : z ∈ takeB := (Finset.mem_inter.mp hz2).2
      exact Finset.disjoint_left.mp h_take_drop_B_disj hzB2 hzB1
    have h_same_cross : Disjoint Same Cross := by
      rw [Finset.disjoint_union_left]
      constructor
      · rw [Finset.disjoint_union_right] <;> exact ⟨h11_10, h11_01⟩
      · rw [Finset.disjoint_union_right] <;> exact ⟨h00_10, h00_01⟩
    exact h_same_cross
  have h_char : ∀ {x y : α}, x ∈ I → y ∈ I → x ≠ y →
      (orderFun2 A B x y = 1 ↔ (x ∈ Same ∧ y ∈ Cross) ∨ (x ∈ Cross ∧ y ∈ Same)) := by
    intro x y hx hy hne
    exact orderFun2_same_cross_iff hA hB hA_rot hB_rot hIR hx hy hne

  rcases h_quad with (hQ11 | hQ00)

  · -- Case 1: Q11 = ∅, Cross before Same
    have hA_rot_nodup : A_rot.Nodup := by rw [hA_rot]; exact rot_nodup hA n
    have hB_rot_nodup : B_rot.Nodup := by rw [hB_rot]; exact rot_nodup hB m
    have h_disjA_list : List.Disjoint (A.take n) (A.drop n) := take_drop_disjoint hA n
    have h_disjB_list : List.Disjoint (B.take m) (B.drop m) := take_drop_disjoint hB m
    have h_dropA_transfer : ∀ {x y : α}, x ∈ A.drop n → y ∈ A.drop n → x ≠ y →
        (posOf x A < posOf y A ↔ posOf x A_rot < posOf y A_rot) := by
      intro x y hx hy hne
      exact posOf_transfer hA hA_rot_nodup (List.drop_sublist n A)
        (by rw [hA_rot]; exact List.sublist_append_left _ _) hx hy hne
    have h_dropB_transfer : ∀ {x y : α}, x ∈ B.drop m → y ∈ B.drop m → x ≠ y →
        (posOf x B < posOf y B ↔ posOf x B_rot < posOf y B_rot) := by
      intro x y hx hy hne
      exact posOf_transfer hB hB_rot_nodup (List.drop_sublist m B)
        (by rw [hB_rot]; exact List.sublist_append_left _ _) hx hy hne
    have h_Same_eq : Same = Q00 := by simp [Same, hQ11]
    have h_Cross_eq : Cross = Q10 ∪ Q01 := by simp [Cross]
    have h_orderA : ∀ x ∈ Cross, ∀ y ∈ Same, posOf x A < posOf y A := by
      intro x hx y hy
      have hy_Q00 : y ∈ Q00 := by rw [h_Same_eq] at hy; exact hy
      have hy_Q00' : y ∈ I ∧ y ∈ dropA ∧ y ∈ dropB := by
        simpa [Q00, Finset.mem_inter] using hy_Q00
      rcases hy_Q00' with ⟨_, hy_dropA, hy_dropB⟩
      have hy_dropA' : y ∈ A.drop n := by simpa [dropA, List.mem_toFinset] using hy_dropA
      have hy_dropB' : y ∈ B.drop m := by simpa [dropB, List.mem_toFinset] using hy_dropB
      have h_x_cross : x ∈ Q10 ∨ x ∈ Q01 := by
        rw [h_Cross_eq] at hx; exact Finset.mem_union.mp hx
      have hne : x ≠ y := by
        intro h
        have h_y_Cross : y ∈ Cross := by simpa [h] using hx
        exact Finset.disjoint_left.mp h_disj hy h_y_Cross
      rcases h_x_cross with (h_x_Q10 | h_x_Q01)
      · -- x ∈ Q10: takeA, dropB → take before drop in A
        have h_x_Q10' : x ∈ I ∧ x ∈ takeA ∧ x ∈ dropB := by
          simpa [Q10, Finset.mem_inter] using h_x_Q10
        rcases h_x_Q10' with ⟨_, hx_takeA, _⟩
        have hx_takeA' : x ∈ A.take n := by simpa [takeA, List.mem_toFinset] using hx_takeA
        have h_goal : posOf x (A.take n ++ A.drop n) < posOf y (A.take n ++ A.drop n) :=
          posOf_left_before_right h_disjA_list hx_takeA' hy_dropA'
        simpa [List.take_append_drop] using h_goal
      · -- x ∈ Q01: dropA, takeB → transfer from B_rot
        have h_x_Q01' : x ∈ I ∧ x ∈ dropA ∧ x ∈ takeB := by
          simpa [Q01, Finset.mem_inter] using h_x_Q01
        rcases h_x_Q01' with ⟨_, hx_dropA, hx_takeB⟩
        have hx_dropA' : x ∈ A.drop n := by simpa [dropA, List.mem_toFinset] using hx_dropA
        have hx_takeB' : x ∈ B.take m := by simpa [takeB, List.mem_toFinset] using hx_takeB
        have h_y_before_x_Brot : posOf y B_rot < posOf x B_rot := by
          rw [hB_rot]; exact posOf_left_before_right h_disjB_list.symm hy_dropB' hx_takeB'
        have hy_Arot : y ∈ A_rot := by rw [hA_rot]; exact List.mem_append_left _ hy_dropA'
        have hx_Arot : x ∈ A_rot := by rw [hA_rot]; exact List.mem_append_left _ hx_dropA'
        have hy_Brot : y ∈ B_rot := by rw [hB_rot]; exact List.mem_append_left _ hy_dropB'
        have hx_Brot : x ∈ B_rot := by rw [hB_rot]; exact List.mem_append_right _ hx_takeB'
        have hIR' : posOf y A_rot < posOf x A_rot ↔ posOf x B_rot < posOf y B_rot :=
          hIR y hy_Arot x hx_Arot hne.symm hy_Brot hx_Brot
        have h_not : ¬(posOf x B_rot < posOf y B_rot) := lt_asymm h_y_before_x_Brot
        have h_not2 : ¬(posOf y A_rot < posOf x A_rot) := mt hIR'.mp h_not
        have h_ne_pos : posOf x A_rot ≠ posOf y A_rot := posOf_nodup_ne hA_rot_nodup hx_Arot hy_Arot hne
        have h_x_before_y_Arot : posOf x A_rot < posOf y A_rot :=
          Nat.lt_of_le_of_ne (Nat.le_of_not_gt h_not2) h_ne_pos
        exact (h_dropA_transfer hx_dropA' hy_dropA' hne).mpr h_x_before_y_Arot
    have h_orderB : ∀ x ∈ Cross, ∀ y ∈ Same, posOf x B < posOf y B := by
      intro x hx y hy
      have hy_Q00 : y ∈ Q00 := by rw [h_Same_eq] at hy; exact hy
      have hy_Q00' : y ∈ I ∧ y ∈ dropA ∧ y ∈ dropB := by
        simpa [Q00, Finset.mem_inter] using hy_Q00
      rcases hy_Q00' with ⟨_, hy_dropA, hy_dropB⟩
      have hy_dropA' : y ∈ A.drop n := by simpa [dropA, List.mem_toFinset] using hy_dropA
      have hy_dropB' : y ∈ B.drop m := by simpa [dropB, List.mem_toFinset] using hy_dropB
      have h_x_cross : x ∈ Q10 ∨ x ∈ Q01 := by
        rw [h_Cross_eq] at hx; exact Finset.mem_union.mp hx
      have hne : x ≠ y := by
        intro h
        have h_y_Cross : y ∈ Cross := by simpa [h] using hx
        exact Finset.disjoint_left.mp h_disj hy h_y_Cross
      rcases h_x_cross with (h_x_Q10 | h_x_Q01)
      · -- x ∈ Q10: takeA, dropB → transfer from A_rot
        have h_x_Q10' : x ∈ I ∧ x ∈ takeA ∧ x ∈ dropB := by
          simpa [Q10, Finset.mem_inter] using h_x_Q10
        rcases h_x_Q10' with ⟨_, hx_takeA, hx_dropB⟩
        have hx_takeA' : x ∈ A.take n := by simpa [takeA, List.mem_toFinset] using hx_takeA
        have hx_dropB' : x ∈ B.drop m := by simpa [dropB, List.mem_toFinset] using hx_dropB
        have h_y_before_x_Arot : posOf y A_rot < posOf x A_rot := by
          rw [hA_rot]; exact posOf_left_before_right h_disjA_list.symm hy_dropA' hx_takeA'
        have hy_Arot : y ∈ A_rot := by rw [hA_rot]; exact List.mem_append_left _ hy_dropA'
        have hx_Arot : x ∈ A_rot := by rw [hA_rot]; exact List.mem_append_right _ hx_takeA'
        have hy_Brot : y ∈ B_rot := by rw [hB_rot]; exact List.mem_append_left _ hy_dropB'
        have hx_Brot : x ∈ B_rot := by rw [hB_rot]; exact List.mem_append_left _ hx_dropB'
        have hIR' : posOf y A_rot < posOf x A_rot ↔ posOf x B_rot < posOf y B_rot :=
          hIR y hy_Arot x hx_Arot hne.symm hy_Brot hx_Brot
        have h_x_before_y_Brot : posOf x B_rot < posOf y B_rot := hIR'.mp h_y_before_x_Arot
        exact (h_dropB_transfer hx_dropB' hy_dropB' hne).mpr h_x_before_y_Brot
      · -- x ∈ Q01: dropA, takeB → take before drop in B
        have h_x_Q01' : x ∈ I ∧ x ∈ dropA ∧ x ∈ takeB := by
          simpa [Q01, Finset.mem_inter] using h_x_Q01
        rcases h_x_Q01' with ⟨_, _, hx_takeB⟩
        have hx_takeB' : x ∈ B.take m := by simpa [takeB, List.mem_toFinset] using hx_takeB
        have h_goal : posOf x (B.take m ++ B.drop m) < posOf y (B.take m ++ B.drop m) :=
          posOf_left_before_right h_disjB_list hx_takeB' hy_dropB'
        simpa [List.take_append_drop] using h_goal
    rcases at_most_one_block_spans_transition hA l Cross Same hCross_A hSame_A h_orderA with ⟨s0, hs0⟩
    rcases at_most_one_block_spans_transition hB l Cross Same hCross_B hSame_B h_orderB with ⟨t0, ht0⟩
    refine' ⟨(s0, t0), _⟩
    intro s t hs_len ht_len hsing
    let I_st : Finset α := (block A s).toFinset ∩ (block B t).toFinset
    have hI_st_sub : I_st ⊆ I := by
      intro z hz
      have h1 : z ∈ block A s := by
        have h : z ∈ (block A s).toFinset := (Finset.mem_inter.mp hz).1
        exact (List.mem_toFinset).mp h
      have h2 : z ∈ block B t := by
        have h : z ∈ (block B t).toFinset := (Finset.mem_inter.mp hz).2
        exact (List.mem_toFinset).mp h
      have h3 : z ∈ A := (block_sublist A s).subset h1
      have h4 : z ∈ B := (block_sublist B t).subset h2
      simp [I, List.mem_toFinset, h3, h4]
    have h_not_sub_Same : ¬(I_st ⊆ Same) := by
      intro h; exact hsing (block_pair_ir_if_subset hA hB Same Cross h_disj h_char (Or.inl h))
    have h_not_sub_Cross : ¬(I_st ⊆ Cross) := by
      intro h; exact hsing (block_pair_ir_if_subset hA hB Same Cross h_disj h_char (Or.inr h))
    have h_exists_Cross : ∃ x, x ∈ I_st ∧ x ∈ Cross := by
      by_contra h; push Not at h
      have h' : I_st ⊆ Same := by
        intro z hz
        have hzI : z ∈ I := hI_st_sub hz
        have h1 : z ∈ Same ∪ Cross := by rw [h_partition] <;> exact hzI
        simp only [Finset.mem_union] at h1
        rcases h1 with (h1 | h1) <;> tauto
      exact h_not_sub_Same h'
    have h_exists_Same : ∃ y, y ∈ I_st ∧ y ∈ Same := by
      by_contra h; push Not at h
      have h' : I_st ⊆ Cross := by
        intro z hz
        have hzI : z ∈ I := hI_st_sub hz
        have h1 : z ∈ Same ∪ Cross := by rw [h_partition] <;> exact hzI
        simp only [Finset.mem_union] at h1
        rcases h1 with (h1 | h1) <;> tauto
      exact h_not_sub_Cross h'
    rcases h_exists_Cross with ⟨x, hxI_st, hxCross⟩
    rcases h_exists_Same with ⟨y, hyI_st, hySame⟩
    have hx_A : x ∈ block A s := by
      have h : x ∈ (block A s).toFinset := (Finset.mem_inter.mp hxI_st).1
      exact (List.mem_toFinset).mp h
    have hx_B : x ∈ block B t := by
      have h : x ∈ (block B t).toFinset := (Finset.mem_inter.mp hxI_st).2
      exact (List.mem_toFinset).mp h
    have hy_A : y ∈ block A s := by
      have h : y ∈ (block A s).toFinset := (Finset.mem_inter.mp hyI_st).1
      exact (List.mem_toFinset).mp h
    have hy_B : y ∈ block B t := by
      have h : y ∈ (block B t).toFinset := (Finset.mem_inter.mp hyI_st).2
      exact (List.mem_toFinset).mp h
    have h_s_eq : s = s0 := hs0 s hs_len ⟨x, hxCross, hx_A⟩ ⟨y, hySame, hy_A⟩
    have h_t_eq : t = t0 := ht0 t ht_len ⟨x, hxCross, hx_B⟩ ⟨y, hySame, hy_B⟩
    exact Prod.ext h_s_eq h_t_eq

  · -- Case 2: Q00 = ∅, Same before Cross
    have hA_rot_nodup : A_rot.Nodup := by rw [hA_rot]; exact rot_nodup hA n
    have hB_rot_nodup : B_rot.Nodup := by rw [hB_rot]; exact rot_nodup hB m
    have h_disjA_list : List.Disjoint (A.take n) (A.drop n) := take_drop_disjoint hA n
    have h_disjB_list : List.Disjoint (B.take m) (B.drop m) := take_drop_disjoint hB m
    have h_takeA_transfer : ∀ {x y : α}, x ∈ A.take n → y ∈ A.take n → x ≠ y →
        (posOf x A < posOf y A ↔ posOf x A_rot < posOf y A_rot) := by
      intro x y hx hy hne
      exact posOf_transfer hA hA_rot_nodup (List.take_sublist n A)
        (by rw [hA_rot]; exact List.sublist_append_right _ _) hx hy hne
    have h_takeB_transfer : ∀ {x y : α}, x ∈ B.take m → y ∈ B.take m → x ≠ y →
        (posOf x B < posOf y B ↔ posOf x B_rot < posOf y B_rot) := by
      intro x y hx hy hne
      exact posOf_transfer hB hB_rot_nodup (List.take_sublist m B)
        (by rw [hB_rot]; exact List.sublist_append_right _ _) hx hy hne
    have h_Same_eq : Same = Q11 := by simp [Same, hQ00]
    have h_Cross_eq : Cross = Q10 ∪ Q01 := by simp [Cross]
    have h_Same_eq : Same = Q11 := by simp [Same, hQ00]
    have h_Cross_eq : Cross = Q10 ∪ Q01 := by simp [Cross]
    have h_orderA : ∀ x ∈ Same, ∀ y ∈ Cross, posOf x A < posOf y A := by
      intro x hx y hy
      have hx_Q11 : x ∈ Q11 := by rw [h_Same_eq] at hx; exact hx
      have hx_Q11' : x ∈ I ∧ x ∈ takeA ∧ x ∈ takeB := by
        simpa [Q11, Finset.mem_inter] using hx_Q11
      rcases hx_Q11' with ⟨_, hx_takeA, hx_takeB⟩
      have hx_takeA' : x ∈ A.take n := by simpa [takeA, List.mem_toFinset] using hx_takeA
      have hx_takeB' : x ∈ B.take m := by simpa [takeB, List.mem_toFinset] using hx_takeB
      have h_y_cross : y ∈ Q10 ∨ y ∈ Q01 := by
        rw [h_Cross_eq] at hy; exact Finset.mem_union.mp hy
      have hne : x ≠ y := by
        intro h
        have h_y_Same : y ∈ Same := by
          have h' : y = x := h.symm
          rw [h']
          exact hx
        exact Finset.disjoint_left.mp h_disj h_y_Same hy
      rcases h_y_cross with (h_y_Q10 | h_y_Q01)
      · -- y ∈ Q10: takeA, dropB → both in takeA, transfer from B_rot
        have h_y_Q10' : y ∈ I ∧ y ∈ takeA ∧ y ∈ dropB := by
          simpa [Q10, Finset.mem_inter] using h_y_Q10
        rcases h_y_Q10' with ⟨_, hy_takeA, hy_dropB⟩
        have hy_takeA' : y ∈ A.take n := by simpa [takeA, List.mem_toFinset] using hy_takeA
        have hy_dropB' : y ∈ B.drop m := by simpa [dropB, List.mem_toFinset] using hy_dropB
        have h_y_before_x_Brot : posOf y B_rot < posOf x B_rot := by
          rw [hB_rot]; exact posOf_left_before_right h_disjB_list.symm hy_dropB' hx_takeB'
        have hy_Arot : y ∈ A_rot := by rw [hA_rot]; exact List.mem_append_right _ hy_takeA'
        have hx_Arot : x ∈ A_rot := by rw [hA_rot]; exact List.mem_append_right _ hx_takeA'
        have hy_Brot : y ∈ B_rot := by rw [hB_rot]; exact List.mem_append_left _ hy_dropB'
        have hx_Brot : x ∈ B_rot := by rw [hB_rot]; exact List.mem_append_right _ hx_takeB'
        have hIR' : posOf y A_rot < posOf x A_rot ↔ posOf x B_rot < posOf y B_rot :=
          hIR y hy_Arot x hx_Arot hne.symm hy_Brot hx_Brot
        have h_not : ¬(posOf x B_rot < posOf y B_rot) := lt_asymm h_y_before_x_Brot
        have h_not2 : ¬(posOf y A_rot < posOf x A_rot) := mt hIR'.mp h_not
        have h_ne_pos : posOf x A_rot ≠ posOf y A_rot := posOf_nodup_ne hA_rot_nodup hx_Arot hy_Arot hne
        have h_x_before_y_Arot : posOf x A_rot < posOf y A_rot :=
          Nat.lt_of_le_of_ne (Nat.le_of_not_gt h_not2) h_ne_pos
        exact (h_takeA_transfer hx_takeA' hy_takeA' hne).mpr h_x_before_y_Arot
      · -- y ∈ Q01: dropA, takeB → take before drop in A
        have h_y_Q01' : y ∈ I ∧ y ∈ dropA ∧ y ∈ takeB := by
          simpa [Q01, Finset.mem_inter] using h_y_Q01
        rcases h_y_Q01' with ⟨_, hy_dropA, _⟩
        have hy_dropA' : y ∈ A.drop n := by simpa [dropA, List.mem_toFinset] using hy_dropA
        have h_goal : posOf x (A.take n ++ A.drop n) < posOf y (A.take n ++ A.drop n) :=
          posOf_left_before_right h_disjA_list hx_takeA' hy_dropA'
        simpa [List.take_append_drop] using h_goal
    have h_orderB : ∀ x ∈ Same, ∀ y ∈ Cross, posOf x B < posOf y B := by
      intro x hx y hy
      have hx_Q11 : x ∈ Q11 := by rw [h_Same_eq] at hx; exact hx
      have hx_Q11' : x ∈ I ∧ x ∈ takeA ∧ x ∈ takeB := by
        simpa [Q11, Finset.mem_inter] using hx_Q11
      rcases hx_Q11' with ⟨_, hx_takeA, hx_takeB⟩
      have hx_takeA' : x ∈ A.take n := by simpa [takeA, List.mem_toFinset] using hx_takeA
      have hx_takeB' : x ∈ B.take m := by simpa [takeB, List.mem_toFinset] using hx_takeB
      have h_y_cross : y ∈ Q10 ∨ y ∈ Q01 := by
        rw [h_Cross_eq] at hy; exact Finset.mem_union.mp hy
      have hne : x ≠ y := by
        intro h
        have h_y_Same : y ∈ Same := by
          have h' : y = x := h.symm
          rw [h']
          exact hx
        exact Finset.disjoint_left.mp h_disj h_y_Same hy
      rcases h_y_cross with (h_y_Q10 | h_y_Q01)
      · -- y ∈ Q10: takeA, dropB → take before drop in B
        have h_y_Q10' : y ∈ I ∧ y ∈ takeA ∧ y ∈ dropB := by
          simpa [Q10, Finset.mem_inter] using h_y_Q10
        rcases h_y_Q10' with ⟨_, _, hy_dropB⟩
        have hy_dropB' : y ∈ B.drop m := by simpa [dropB, List.mem_toFinset] using hy_dropB
        have h_goal : posOf x (B.take m ++ B.drop m) < posOf y (B.take m ++ B.drop m) :=
          posOf_left_before_right h_disjB_list hx_takeB' hy_dropB'
        simpa [List.take_append_drop] using h_goal
      · -- y ∈ Q01: dropA, takeB → both in takeB, transfer from A_rot
        have h_y_Q01' : y ∈ I ∧ y ∈ dropA ∧ y ∈ takeB := by
          simpa [Q01, Finset.mem_inter] using h_y_Q01
        rcases h_y_Q01' with ⟨_, hy_dropA, hy_takeB⟩
        have hy_dropA' : y ∈ A.drop n := by simpa [dropA, List.mem_toFinset] using hy_dropA
        have hy_takeB' : y ∈ B.take m := by simpa [takeB, List.mem_toFinset] using hy_takeB
        have h_y_before_x_Arot : posOf y A_rot < posOf x A_rot := by
          rw [hA_rot]; exact posOf_left_before_right h_disjA_list.symm hy_dropA' hx_takeA'
        have hy_Arot : y ∈ A_rot := by rw [hA_rot]; exact List.mem_append_left _ hy_dropA'
        have hx_Arot : x ∈ A_rot := by rw [hA_rot]; exact List.mem_append_right _ hx_takeA'
        have hy_Brot : y ∈ B_rot := by rw [hB_rot]; exact List.mem_append_right _ hy_takeB'
        have hx_Brot : x ∈ B_rot := by rw [hB_rot]; exact List.mem_append_right _ hx_takeB'
        have hIR' : posOf y A_rot < posOf x A_rot ↔ posOf x B_rot < posOf y B_rot :=
          hIR y hy_Arot x hx_Arot hne.symm hy_Brot hx_Brot
        have h_x_before_y_Brot : posOf x B_rot < posOf y B_rot := hIR'.mp h_y_before_x_Arot
        exact (h_takeB_transfer hx_takeB' hy_takeB' hne).mpr h_x_before_y_Brot
    rcases at_most_one_block_spans_transition hA l Same Cross hSame_A hCross_A h_orderA with ⟨s0, hs0⟩
    rcases at_most_one_block_spans_transition hB l Same Cross hSame_B hCross_B h_orderB with ⟨t0, ht0⟩
    refine' ⟨(s0, t0), _⟩
    intro s t hs_len ht_len hsing
    let I_st : Finset α := (block A s).toFinset ∩ (block B t).toFinset
    have hI_st_sub : I_st ⊆ I := by
      intro z hz
      have h1 : z ∈ block A s := by
        have h : z ∈ (block A s).toFinset := (Finset.mem_inter.mp hz).1
        exact (List.mem_toFinset).mp h
      have h2 : z ∈ block B t := by
        have h : z ∈ (block B t).toFinset := (Finset.mem_inter.mp hz).2
        exact (List.mem_toFinset).mp h
      have h3 : z ∈ A := (block_sublist A s).subset h1
      have h4 : z ∈ B := (block_sublist B t).subset h2
      simp [I, List.mem_toFinset, h3, h4]
    have h_not_sub_Same : ¬(I_st ⊆ Same) := by
      intro h; exact hsing (block_pair_ir_if_subset hA hB Same Cross h_disj h_char (Or.inl h))
    have h_not_sub_Cross : ¬(I_st ⊆ Cross) := by
      intro h; exact hsing (block_pair_ir_if_subset hA hB Same Cross h_disj h_char (Or.inr h))
    have h_exists_Same : ∃ x, x ∈ I_st ∧ x ∈ Same := by
      by_contra h; push Not at h
      have h' : I_st ⊆ Cross := by
        intro z hz
        have hzI : z ∈ I := hI_st_sub hz
        have h1 : z ∈ Same ∪ Cross := by rw [h_partition] <;> exact hzI
        simp only [Finset.mem_union] at h1
        rcases h1 with (h1 | h1) <;> tauto
      exact h_not_sub_Cross h'
    have h_exists_Cross : ∃ y, y ∈ I_st ∧ y ∈ Cross := by
      by_contra h; push Not at h
      have h' : I_st ⊆ Same := by
        intro z hz
        have hzI : z ∈ I := hI_st_sub hz
        have h1 : z ∈ Same ∪ Cross := by rw [h_partition] <;> exact hzI
        simp only [Finset.mem_union] at h1
        rcases h1 with (h1 | h1) <;> tauto
      exact h_not_sub_Same h'
    rcases h_exists_Same with ⟨x, hxI_st, hxSame⟩
    rcases h_exists_Cross with ⟨y, hyI_st, hyCross⟩
    have hx_A : x ∈ block A s := by
      have h : x ∈ (block A s).toFinset := (Finset.mem_inter.mp hxI_st).1
      exact (List.mem_toFinset).mp h
    have hx_B : x ∈ block B t := by
      have h : x ∈ (block B t).toFinset := (Finset.mem_inter.mp hxI_st).2
      exact (List.mem_toFinset).mp h
    have hy_A : y ∈ block A s := by
      have h : y ∈ (block A s).toFinset := (Finset.mem_inter.mp hyI_st).1
      exact (List.mem_toFinset).mp h
    have hy_B : y ∈ block B t := by
      have h : y ∈ (block B t).toFinset := (Finset.mem_inter.mp hyI_st).2
      exact (List.mem_toFinset).mp h
    have h_s_eq : s = s0 := hs0 s hs_len ⟨x, hxSame, hx_A⟩ ⟨y, hyCross, hy_A⟩
    have h_t_eq : t = t0 := ht0 t ht_len ⟨x, hxSame, hx_B⟩ ⟨y, hyCross, hy_B⟩
    exact Prod.ext h_s_eq h_t_eq

end MarcusTardos.SingularPairBound
