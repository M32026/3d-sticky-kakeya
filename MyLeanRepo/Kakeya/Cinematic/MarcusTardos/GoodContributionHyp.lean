import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Definitions
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.OrderFunction
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.DyadicDecomposition
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.BlockStructure
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.DirectBound
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.SameCrossCharacterization
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.GoodContributionAlgebra
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# GoodContributionHyp for cyclically IR lists

Defines `GoodContributionHyp A B` as the property that every block pair
has nonnegative good contribution, and proves it for cyclically IR lists.
-/

namespace MarcusTardos.GoodContributionHyp

open BigOperators Finset

variable {α : Type*} [DecidableEq α]

/-- `orderFun` is preserved under sublists (for nodup lists). -/
lemma orderFun_sublist_eq {A C : List α} (hC : C.Sublist A) (hA : A.Nodup)
    {x y : α} (hxC : x ∈ C) (hyC : y ∈ C) (hne : x ≠ y) :
    orderFun C x y = orderFun A x y := by
  have hxA : x ∈ A := hC.subset hxC
  have hyA : y ∈ A := hC.subset hyC
  have h_pos : posOf x C < posOf y C ↔ posOf x A < posOf y A :=
    posOf_sublist_lt hC hA hxC hyC hne
  by_cases hlt : posOf x C < posOf y C
  · have hltA : posOf x A < posOf y A := h_pos.mp hlt
    have h1 : orderFun C x y = 1 := by simp [orderFun, hxC, hyC, hlt]
    have h2 : orderFun A x y = 1 := by simp [orderFun, hxA, hyA, hltA]
    rw [h1, h2]
  · have hnltA : ¬(posOf x A < posOf y A) := mt h_pos.mpr hlt
    have hne' : posOf x C ≠ posOf y C := posOf_distinct C x y hxC hyC hne
    have hgtC : posOf y C < posOf x C := by
      have hle : posOf y C ≤ posOf x C := Nat.le_of_not_gt hlt
      exact Nat.lt_of_le_of_ne hle hne'.symm
    have hne'A : posOf x A ≠ posOf y A := posOf_distinct A x y hxA hyA hne
    have hgtA : posOf y A < posOf x A := by
      have hle : posOf y A ≤ posOf x A := Nat.le_of_not_gt hnltA
      exact Nat.lt_of_le_of_ne hle hne'A.symm
    have h1 : orderFun C x y = -1 := by
      simp [orderFun, hxC, hyC, hlt, hgtC] <;> omega
    have h2 : orderFun A x y = -1 := by
      simp [orderFun, hxA, hyA, hnltA, hgtA] <;> omega
    rw [h1, h2]

/-- `orderFun2` is preserved under sublists. -/
lemma orderFun2_sublist_eq {A B C D : List α}
    (hC : C.Sublist A) (hD : D.Sublist B)
    (hA : A.Nodup) (hB : B.Nodup)
    {x y : α} (hxC : x ∈ C) (hyC : y ∈ C)
    (hxD : x ∈ D) (hyD : y ∈ D) (hne : x ≠ y) :
    orderFun2 C D x y = orderFun2 A B x y := by
  have h1 : orderFun C x y = orderFun A x y := orderFun_sublist_eq hC hA hxC hyC hne
  have h2 : orderFun D x y = orderFun B x y := orderFun_sublist_eq hD hB hxD hyD hne
  have h3 : orderFun2 C D x y = orderFun C x y * orderFun D x y := by rfl
  have h4 : orderFun2 A B x y = orderFun A x y * orderFun B x y := by rfl
  rw [h3, h4, h1, h2]

/--
Good contribution hypothesis: every block pair has nonnegative contribution `r - c ≥ 0`.
-/
def GoodContributionHyp (A B : List α) : Prop :=
  ∀ (s t : List Bool),
    let Bs := block A s
    let Bt := block B t
    let I := Bs.toFinset ∩ Bt.toFinset
    (I.card : ℤ) - ∑ p ∈ I.offDiag, orderFun2 Bs Bt p.1 p.2 ≥ 0

/-- Prove GoodContributionHyp for cyclically intersection-reverse lists. -/
lemma good_contribution_hyp {A B : List α} (hA : A.Nodup) (hB : B.Nodup)
    (hcir : IsCyclicIntersectionReverse A B) :
    GoodContributionHyp A B := by
  rcases hcir with ⟨A_rot, B_rot, h_rotA, h_rotB, hIR⟩
  rcases h_rotA with ⟨n, hA_rot⟩
  rcases h_rotB with ⟨m, hB_rot⟩
  intro s t
  dsimp only
  let Bs := block A s
  let Bt := block B t
  let I : Finset α := Bs.toFinset ∩ Bt.toFinset
  let takeA : Finset α := (A.take n).toFinset
  let dropA : Finset α := (A.drop n).toFinset
  let takeB : Finset α := (B.take m).toFinset
  let dropB : Finset α := (B.drop m).toFinset
  let I_global : Finset α := A.toFinset ∩ B.toFinset
  let SameGlobal : Finset α := (takeA ∩ takeB) ∪ (dropA ∩ dropB)
  let CrossGlobal : Finset α := (takeA ∩ dropB) ∪ (dropA ∩ takeB)
  let Same_st : Finset α := I ∩ SameGlobal
  let Cross_st : Finset α := I ∩ CrossGlobal
  have hBs_nodup : Bs.Nodup := block_nodup hA s
  have hBt_nodup : Bt.Nodup := block_nodup hB t
  have hBs_sub : Bs.Sublist A := block_sublist A s
  have hBt_sub : Bt.Sublist B := block_sublist B t
  have hI_sub_global : I ⊆ I_global := by
    intro z hz
    have hzBs : z ∈ Bs := List.mem_toFinset.mp (Finset.mem_inter.mp hz).1
    have hzBt : z ∈ Bt := List.mem_toFinset.mp (Finset.mem_inter.mp hz).2
    have hzA : z ∈ A := hBs_sub.subset hzBs
    have hzB : z ∈ B := hBt_sub.subset hzBt
    simp only [I_global, Finset.mem_inter, List.mem_toFinset] <;> exact ⟨hzA, hzB⟩
  have h_list_disjA : List.Disjoint (A.take n) (A.drop n) := by
    have h : (A.take n ++ A.drop n).Nodup := by
      rw [List.take_append_drop] <;> exact hA
    exact (List.nodup_append').mp h |>.2.2
  have h_list_disjB : List.Disjoint (B.take m) (B.drop m) := by
    have h : (B.take m ++ B.drop m).Nodup := by
      rw [List.take_append_drop] <;> exact hB
    exact (List.nodup_append').mp h |>.2.2
  have h_disjA : Disjoint takeA dropA := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    have h1 : z ∈ A.take n := by simpa [takeA, List.mem_toFinset] using hz1
    have h2 : z ∈ A.drop n := by simpa [dropA, List.mem_toFinset] using hz2
    exact h_list_disjA h1 h2
  have h_disjB : Disjoint takeB dropB := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    have h1 : z ∈ B.take m := by simpa [takeB, List.mem_toFinset] using hz1
    have h2 : z ∈ B.drop m := by simpa [dropB, List.mem_toFinset] using hz2
    exact h_list_disjB h1 h2
  have h_disj_global : Disjoint SameGlobal CrossGlobal := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [SameGlobal, CrossGlobal, Finset.mem_union] at hz1 hz2
    rcases hz1 with (h1 | h1)
    · rcases hz2 with (h2 | h2)
      · have h1B : z ∈ takeB := (Finset.mem_inter.mp h1).2
        have h2B : z ∈ dropB := (Finset.mem_inter.mp h2).2
        exact Finset.disjoint_left.mp h_disjB h1B h2B
      · have h1A : z ∈ takeA := (Finset.mem_inter.mp h1).1
        have h2A : z ∈ dropA := (Finset.mem_inter.mp h2).1
        exact Finset.disjoint_left.mp h_disjA h1A h2A
    · rcases hz2 with (h2 | h2)
      · have h1A : z ∈ dropA := (Finset.mem_inter.mp h1).1
        have h2A : z ∈ takeA := (Finset.mem_inter.mp h2).1
        exact Finset.disjoint_left.mp h_disjA h2A h1A
      · have h1B : z ∈ dropB := (Finset.mem_inter.mp h1).2
        have h2B : z ∈ takeB := (Finset.mem_inter.mp h2).2
        exact Finset.disjoint_left.mp h_disjB h2B h1B
  have h_disj : Disjoint Same_st Cross_st := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    have h1 : z ∈ SameGlobal := (Finset.mem_inter.mp hz1).2
    have h2 : z ∈ CrossGlobal := (Finset.mem_inter.mp hz2).2
    exact Finset.disjoint_left.mp h_disj_global h1 h2
  have h_partition : Same_st ∪ Cross_st = I := by
    apply Finset.Subset.antisymm
    · have h1 : Same_st ⊆ I := by
        intro z hz
        exact (Finset.mem_inter.mp hz).1
      have h2 : Cross_st ⊆ I := by
        intro z hz
        exact (Finset.mem_inter.mp hz).1
      exact Finset.union_subset h1 h2
    · intro z hz
      have hzI : z ∈ I := hz
      have hz_global : z ∈ I_global := hI_sub_global hzI
      have hzA : z ∈ A := by
        have h : z ∈ Bs := List.mem_toFinset.mp (Finset.mem_inter.mp hzI).1
        exact hBs_sub.subset h
      have hzB : z ∈ B := by
        have h : z ∈ Bt := List.mem_toFinset.mp (Finset.mem_inter.mp hzI).2
        exact hBt_sub.subset h
      have h_covA : z ∈ takeA ∨ z ∈ dropA := by
        have h : z ∈ A.take n ++ A.drop n := by rw [List.take_append_drop] <;> exact hzA
        rcases List.mem_append.mp h with (h | h)
        · left; simpa [takeA, List.mem_toFinset] using h
        · right; simpa [dropA, List.mem_toFinset] using h
      have h_covB : z ∈ takeB ∨ z ∈ dropB := by
        have h : z ∈ B.take m ++ B.drop m := by rw [List.take_append_drop] <;> exact hzB
        rcases List.mem_append.mp h with (h | h)
        · left; simpa [takeB, List.mem_toFinset] using h
        · right; simpa [dropB, List.mem_toFinset] using h
      rcases h_covA with (hA1 | hA2) <;> rcases h_covB with (hB1 | hB2)
      · have hz_same : z ∈ SameGlobal := by
          simp only [SameGlobal, Finset.mem_union]
          left
          exact Finset.mem_inter.mpr ⟨hA1, hB1⟩
        have hz_st : z ∈ Same_st := Finset.mem_inter.mpr ⟨hzI, hz_same⟩
        exact Finset.mem_union_left _ hz_st
      · have hz_cross : z ∈ CrossGlobal := by
          simp only [CrossGlobal, Finset.mem_union]
          left
          exact Finset.mem_inter.mpr ⟨hA1, hB2⟩
        have hz_st : z ∈ Cross_st := Finset.mem_inter.mpr ⟨hzI, hz_cross⟩
        exact Finset.mem_union_right _ hz_st
      · have hz_cross : z ∈ CrossGlobal := by
          simp only [CrossGlobal, Finset.mem_union]
          right
          exact Finset.mem_inter.mpr ⟨hA2, hB1⟩
        have hz_st : z ∈ Cross_st := Finset.mem_inter.mpr ⟨hzI, hz_cross⟩
        exact Finset.mem_union_right _ hz_st
      · have hz_same : z ∈ SameGlobal := by
          simp only [SameGlobal, Finset.mem_union]
          right
          exact Finset.mem_inter.mpr ⟨hA2, hB2⟩
        have hz_st : z ∈ Same_st := Finset.mem_inter.mpr ⟨hzI, hz_same⟩
        exact Finset.mem_union_left _ hz_st
  have h_char : ∀ (x y : α), x ∈ I → y ∈ I → x ≠ y →
      (orderFun2 Bs Bt x y = 1 ↔ (x ∈ Same_st ∧ y ∈ Cross_st) ∨ (x ∈ Cross_st ∧ y ∈ Same_st)) := by
    intro x y hxI hyI hne
    have hxBs : x ∈ Bs := List.mem_toFinset.mp (Finset.mem_inter.mp hxI).1
    have hyBs : y ∈ Bs := List.mem_toFinset.mp (Finset.mem_inter.mp hyI).1
    have hxBt : x ∈ Bt := List.mem_toFinset.mp (Finset.mem_inter.mp hxI).2
    have hyBt : y ∈ Bt := List.mem_toFinset.mp (Finset.mem_inter.mp hyI).2
    have hxA : x ∈ A := hBs_sub.subset hxBs
    have hyA : y ∈ A := hBs_sub.subset hyBs
    have hxB : x ∈ B := hBt_sub.subset hxBt
    have hyB : y ∈ B := hBt_sub.subset hyBt
    have hxI' : x ∈ I_global := by
      simp only [I_global, Finset.mem_inter, List.mem_toFinset] <;> exact ⟨hxA, hxB⟩
    have hyI' : y ∈ I_global := by
      simp only [I_global, Finset.mem_inter, List.mem_toFinset] <;> exact ⟨hyA, hyB⟩
    have h_transfer : orderFun2 Bs Bt x y = orderFun2 A B x y :=
      orderFun2_sublist_eq hBs_sub hBt_sub hA hB hxBs hyBs hxBt hyBt hne
    have h_global_char : orderFun2 A B x y = 1 ↔
        ((x ∈ (I_global ∩ takeA ∩ takeB) ∪ (I_global ∩ dropA ∩ dropB)) ∧
         (y ∈ (I_global ∩ takeA ∩ dropB) ∪ (I_global ∩ dropA ∩ takeB)) ∨
        (x ∈ (I_global ∩ takeA ∩ dropB) ∪ (I_global ∩ dropA ∩ takeB)) ∧
         (y ∈ (I_global ∩ takeA ∩ takeB) ∪ (I_global ∩ dropA ∩ dropB))) :=
      SameCrossCharacterization.orderFun2_same_cross_iff hA hB hA_rot hB_rot hIR hxI' hyI' hne
    have h_Same_char_eq : (I_global ∩ takeA ∩ takeB) ∪ (I_global ∩ dropA ∩ dropB) = I_global ∩ SameGlobal := by
      have h' : (I_global ∩ takeA ∩ takeB) = I_global ∩ (takeA ∩ takeB) := by
        ext z; simp [Finset.mem_inter]
      have h'' : (I_global ∩ dropA ∩ dropB) = I_global ∩ (dropA ∩ dropB) := by
        ext z; simp [Finset.mem_inter]
      rw [h', h'']
      exact (Finset.inter_union_distrib_left I_global (takeA ∩ takeB) (dropA ∩ dropB)).symm
    have h_Cross_char_eq : (I_global ∩ takeA ∩ dropB) ∪ (I_global ∩ dropA ∩ takeB) = I_global ∩ CrossGlobal := by
      have h' : (I_global ∩ takeA ∩ dropB) = I_global ∩ (takeA ∩ dropB) := by
        ext z; simp [Finset.mem_inter]
      have h'' : (I_global ∩ dropA ∩ takeB) = I_global ∩ (dropA ∩ takeB) := by
        ext z; simp [Finset.mem_inter]
      rw [h', h'']
      exact (Finset.inter_union_distrib_left I_global (takeA ∩ dropB) (dropA ∩ takeB)).symm
    rw [h_transfer, h_global_char, h_Same_char_eq, h_Cross_char_eq]
    have h1 : x ∈ I ∩ SameGlobal ↔ x ∈ I_global ∩ SameGlobal := by
      constructor
      · intro h
        have h' : x ∈ I := (Finset.mem_inter.mp h).1
        have h'' : x ∈ SameGlobal := (Finset.mem_inter.mp h).2
        exact Finset.mem_inter.mpr ⟨hI_sub_global h', h''⟩
      · intro h
        have h' : x ∈ I_global := (Finset.mem_inter.mp h).1
        have h'' : x ∈ SameGlobal := (Finset.mem_inter.mp h).2
        have hxI'' : x ∈ I := hxI
        exact Finset.mem_inter.mpr ⟨hxI'', h''⟩
    have h2 : y ∈ I ∩ CrossGlobal ↔ y ∈ I_global ∩ CrossGlobal := by
      constructor
      · intro h
        have h' : y ∈ I := (Finset.mem_inter.mp h).1
        have h'' : y ∈ CrossGlobal := (Finset.mem_inter.mp h).2
        exact Finset.mem_inter.mpr ⟨hI_sub_global h', h''⟩
      · intro h
        have h' : y ∈ I_global := (Finset.mem_inter.mp h).1
        have h'' : y ∈ CrossGlobal := (Finset.mem_inter.mp h).2
        exact Finset.mem_inter.mpr ⟨hyI, h''⟩
    have h3 : x ∈ I ∩ CrossGlobal ↔ x ∈ I_global ∩ CrossGlobal := by
      constructor
      · intro h
        have h' : x ∈ I := (Finset.mem_inter.mp h).1
        have h'' : x ∈ CrossGlobal := (Finset.mem_inter.mp h).2
        exact Finset.mem_inter.mpr ⟨hI_sub_global h', h''⟩
      · intro h
        have h' : x ∈ I_global := (Finset.mem_inter.mp h).1
        have h'' : x ∈ CrossGlobal := (Finset.mem_inter.mp h).2
        exact Finset.mem_inter.mpr ⟨hxI, h''⟩
    have h4 : y ∈ I ∩ SameGlobal ↔ y ∈ I_global ∩ SameGlobal := by
      constructor
      · intro h
        have h' : y ∈ I := (Finset.mem_inter.mp h).1
        have h'' : y ∈ SameGlobal := (Finset.mem_inter.mp h).2
        exact Finset.mem_inter.mpr ⟨hI_sub_global h', h''⟩
      · intro h
        have h' : y ∈ I_global := (Finset.mem_inter.mp h).1
        have h'' : y ∈ SameGlobal := (Finset.mem_inter.mp h).2
        exact Finset.mem_inter.mpr ⟨hyI, h''⟩
    rw [h1, h2, h3, h4]
  have h_main := MarcusTardos.GoodContributionClean.r_minus_c_eq_sq
    Same_st Cross_st h_partition h_disj h_char
  rw [h_main]
  exact sq_nonneg _

end MarcusTardos.GoodContributionHyp
