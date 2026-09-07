import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Definitions
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.OrderFunction
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.DirectBound
import Mathlib.Tactic
import Mathlib.Data.Finset.Card

/-!
# Same/Cross characterization for cyclically IR lists

For cyclically intersection-reverse lists with rotation cuts,
`orderFun2 A B x y = 1` iff exactly one of `x,y` is in `Same` and the other in `Cross`.
-/

namespace MarcusTardos.SameCrossCharacterization

variable {α : Type*} [DecidableEq α]

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
  simp [orderFun, hx, hy]
  omega

/-- Propositional XOR equivalence for Same/Cross characterization. -/
private lemma xor_equiv (a1 a2 b1 b2 : Prop) [Decidable a1] [Decidable a2] [Decidable b1] [Decidable b2] :
    (((a1 ∧ ¬a2) ∨ (¬a1 ∧ a2)) ∧ ¬((b1 ∧ ¬b2) ∨ (¬b1 ∧ b2)) ∨
     (¬((a1 ∧ ¬a2) ∨ (¬a1 ∧ a2))) ∧ ((b1 ∧ ¬b2) ∨ (¬b1 ∧ b2))) ↔
    ((((a1 ∧ b1) ∨ (¬a1 ∧ ¬b1)) ∧ ((a2 ∧ ¬b2) ∨ (¬a2 ∧ b2))) ∨
     (((a1 ∧ ¬b1) ∨ (¬a1 ∧ b1)) ∧ ((a2 ∧ b2) ∨ (¬a2 ∧ ¬b2)))) := by
  by_cases h1 : a1 <;> by_cases h2 : a2 <;> by_cases h3 : b1 <;> by_cases h4 : b2 <;>
    simp [h1, h2, h3, h4]

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
  dsimp only
  let takeA : Finset α := (A.take n).toFinset
  let dropA : Finset α := (A.drop n).toFinset
  let takeB : Finset α := (B.take m).toFinset
  let dropB : Finset α := (B.drop m).toFinset
  let I : Finset α := A.toFinset ∩ B.toFinset
  let Same : Finset α := (I ∩ takeA ∩ takeB) ∪ (I ∩ dropA ∩ dropB)
  let Cross : Finset α := (I ∩ takeA ∩ dropB) ∪ (I ∩ dropA ∩ takeB)
  have hxA : x ∈ A := by simpa [List.mem_toFinset] using (Finset.mem_inter.mp hxI).1
  have hxB : x ∈ B := by simpa [List.mem_toFinset] using (Finset.mem_inter.mp hxI).2
  have hyA : y ∈ A := by simpa [List.mem_toFinset] using (Finset.mem_inter.mp hyI).1
  have hyB : y ∈ B := by simpa [List.mem_toFinset] using (Finset.mem_inter.mp hyI).2
  have h_covA : ∀ (z : α), z ∈ A → z ∈ takeA ∨ z ∈ dropA := by
    intro z hz
    have h : z ∈ A.take n ++ A.drop n := by rw [List.take_append_drop] <;> exact hz
    rcases List.mem_append.mp h with (h | h)
    · left; simpa [takeA, List.mem_toFinset] using h
    · right; simpa [dropA, List.mem_toFinset] using h
  have h_covB : ∀ (z : α), z ∈ B → z ∈ takeB ∨ z ∈ dropB := by
    intro z hz
    have h : z ∈ B.take m ++ B.drop m := by rw [List.take_append_drop] <;> exact hz
    rcases List.mem_append.mp h with (h | h)
    · left; simpa [takeB, List.mem_toFinset] using h
    · right; simpa [dropB, List.mem_toFinset] using h
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
  have h1A_rot : x ∈ A_rot := by
    rw [hA_rot]
    have hcov := h_covA x hxA
    rcases hcov with (h | h)
    · exact List.mem_append_right _ (by simpa [takeA, List.mem_toFinset] using h)
    · exact List.mem_append_left _ (by simpa [dropA, List.mem_toFinset] using h)
  have h2A_rot : y ∈ A_rot := by
    rw [hA_rot]
    have hcov := h_covA y hyA
    rcases hcov with (h | h)
    · exact List.mem_append_right _ (by simpa [takeA, List.mem_toFinset] using h)
    · exact List.mem_append_left _ (by simpa [dropA, List.mem_toFinset] using h)
  have h1B_rot : x ∈ B_rot := by
    rw [hB_rot]
    have hcov := h_covB x hxB
    rcases hcov with (h | h)
    · exact List.mem_append_right _ (by simpa [takeB, List.mem_toFinset] using h)
    · exact List.mem_append_left _ (by simpa [dropB, List.mem_toFinset] using h)
  have h2B_rot : y ∈ B_rot := by
    rw [hB_rot]
    have hcov := h_covB y hyB
    rcases hcov with (h | h)
    · exact List.mem_append_right _ (by simpa [takeB, List.mem_toFinset] using h)
    · exact List.mem_append_left _ (by simpa [dropB, List.mem_toFinset] using h)
  have h_flipA : (orderFun A x y = -orderFun A_rot x y) ↔
      ((x ∈ (A.take n).toFinset ∧ y ∈ (A.drop n).toFinset) ∨
       (x ∈ (A.drop n).toFinset ∧ y ∈ (A.take n).toFinset)) := by
    have h_orig := DirectBound.orderFun_rotation_flip hA n hxA hyA hne
    have h2 : (orderFun A x y = -orderFun A_rot x y) ↔
        (orderFun A x y = -orderFun (A.drop n ++ A.take n) x y) := by
      rw [hA_rot]
    have h3 : ((x ∈ A.take n ∧ y ∈ A.drop n) ∨ (x ∈ A.drop n ∧ y ∈ A.take n)) ↔
        ((x ∈ (A.take n).toFinset ∧ y ∈ (A.drop n).toFinset) ∨
         (x ∈ (A.drop n).toFinset ∧ y ∈ (A.take n).toFinset)) := by
      simp [List.mem_toFinset] <;> rfl
    exact h2.trans (h_orig.trans h3)
  have h_flipB : (orderFun B x y = -orderFun B_rot x y) ↔
      ((x ∈ (B.take m).toFinset ∧ y ∈ (B.drop m).toFinset) ∨
       (x ∈ (B.drop m).toFinset ∧ y ∈ (B.take m).toFinset)) := by
    have h_orig := DirectBound.orderFun_rotation_flip hB m hxB hyB hne
    have h2 : (orderFun B x y = -orderFun B_rot x y) ↔
        (orderFun B x y = -orderFun (B.drop m ++ B.take m) x y) := by
      rw [hB_rot]
    have h3 : ((x ∈ B.take m ∧ y ∈ B.drop m) ∨ (x ∈ B.drop m ∧ y ∈ B.take m)) ↔
        ((x ∈ (B.take m).toFinset ∧ y ∈ (B.drop m).toFinset) ∨
         (x ∈ (B.drop m).toFinset ∧ y ∈ (B.take m).toFinset)) := by
      simp [List.mem_toFinset] <;> rfl
    exact h2.trans (h_orig.trans h3)
  have h3 : orderFun2 A_rot B_rot x y = -1 :=
    orderFun2_eq_neg_one_of_intersectionReverse
      (by rw [hA_rot] <;> exact rot_nodup hA n)
      (by rw [hB_rot] <;> exact rot_nodup hB m)
      hIR h1A_rot h2A_rot hne h1B_rot h2B_rot
  set flipA : Prop := (x ∈ takeA ∧ y ∈ dropA) ∨ (x ∈ dropA ∧ y ∈ takeA) with hflipA_def
  set flipB : Prop := (x ∈ takeB ∧ y ∈ dropB) ∨ (x ∈ dropB ∧ y ∈ takeB) with hflipB_def
  have h4 : orderFun A x y = 1 ∨ orderFun A x y = -1 := orderFun_values hxA hyA hne
  have h5 : orderFun B x y = 1 ∨ orderFun B x y = -1 := orderFun_values hxB hyB hne
  have h_fAr : orderFun A_rot x y = 1 ∨ orderFun A_rot x y = -1 := orderFun_values h1A_rot h2A_rot hne
  have h_fBr : orderFun B_rot x y = 1 ∨ orderFun B_rot x y = -1 := orderFun_values h1B_rot h2B_rot hne
  have h_eqA : flipA → orderFun A x y = -orderFun A_rot x y := by
    intro h
    have h' : (x ∈ takeA ∧ y ∈ dropA) ∨ (x ∈ dropA ∧ y ∈ takeA) := by
      exact h
    exact h_flipA.mpr h'
  have h_eqB : flipB → orderFun B x y = -orderFun B_rot x y := by
    intro h
    have h' : (x ∈ takeB ∧ y ∈ dropB) ∨ (x ∈ dropB ∧ y ∈ takeB) := by
      exact h
    exact h_flipB.mpr h'
  have h_eqA' : ¬flipA → orderFun A x y = orderFun A_rot x y := by
    intro hn
    have hn' : ¬((x ∈ takeA ∧ y ∈ dropA) ∨ (x ∈ dropA ∧ y ∈ takeA)) := by exact hn
    have h6 : ¬(orderFun A x y = -orderFun A_rot x y) := mt h_flipA.mp hn'
    rcases h4 with (h4 | h4) <;> rcases h_fAr with (h_fAr | h_fAr) <;>
      simp [h4, h_fAr] at h6 ⊢ <;> omega
  have h_eqB' : ¬flipB → orderFun B x y = orderFun B_rot x y := by
    intro hn
    have hn' : ¬((x ∈ takeB ∧ y ∈ dropB) ∨ (x ∈ dropB ∧ y ∈ takeB)) := by exact hn
    have h6 : ¬(orderFun B x y = -orderFun B_rot x y) := mt h_flipB.mp hn'
    rcases h5 with (h5 | h5) <;> rcases h_fBr with (h_fBr | h_fBr) <;>
      simp [h5, h_fBr] at h6 ⊢ <;> omega
  have h_main1 : orderFun2 A B x y = 1 ↔
      (flipA ∧ ¬flipB) ∨ (¬flipA ∧ flipB) := by
    constructor
    · intro h
      by_cases hA' : flipA
      · by_cases hB' : flipB
        · exfalso
          have h9 : (orderFun A x y) * (orderFun B x y) = -1 := by
            calc
              (orderFun A x y) * (orderFun B x y)
                = (-orderFun A_rot x y) * (-orderFun B_rot x y) := by rw [h_eqA hA', h_eqB hB']
              _ = (orderFun A_rot x y) * (orderFun B_rot x y) := by ring
              _ = orderFun2 A_rot B_rot x y := by rfl
              _ = -1 := h3
          have h10 : orderFun2 A B x y = (orderFun A x y) * (orderFun B x y) := by rfl
          rw [h10] at h
          rw [h9] at h <;> norm_num at h
        · exact Or.inl ⟨hA', hB'⟩
      · by_cases hB' : flipB
        · exact Or.inr ⟨hA', hB'⟩
        · exfalso
          have h9 : (orderFun A x y) * (orderFun B x y) = -1 := by
            calc
              (orderFun A x y) * (orderFun B x y)
                = (orderFun A_rot x y) * (orderFun B_rot x y) := by rw [h_eqA' hA', h_eqB' hB']
              _ = orderFun2 A_rot B_rot x y := by rfl
              _ = -1 := h3
          have h10 : orderFun2 A B x y = (orderFun A x y) * (orderFun B x y) := by rfl
          rw [h10] at h
          rw [h9] at h <;> norm_num at h
    · rintro (⟨hA', hB'⟩ | ⟨hA', hB'⟩)
      · have h9 : (orderFun A x y) * (orderFun B x y) = 1 := by
          calc
            (orderFun A x y) * (orderFun B x y)
              = (-orderFun A_rot x y) * (orderFun B_rot x y) := by rw [h_eqA hA', h_eqB' hB']
            _ = -((orderFun A_rot x y) * (orderFun B_rot x y)) := by ring
            _ = -orderFun2 A_rot B_rot x y := by rfl
            _ = 1 := by rw [h3] <;> norm_num
        have h10 : orderFun2 A B x y = (orderFun A x y) * (orderFun B x y) := by rfl
        rw [h10, h9]
      · have h9 : (orderFun A x y) * (orderFun B x y) = 1 := by
          calc
            (orderFun A x y) * (orderFun B x y)
              = (orderFun A_rot x y) * (-orderFun B_rot x y) := by rw [h_eqA' hA', h_eqB hB']
            _ = -((orderFun A_rot x y) * (orderFun B_rot x y)) := by ring
            _ = -orderFun2 A_rot B_rot x y := by rfl
            _ = 1 := by rw [h3] <;> norm_num
        have h10 : orderFun2 A B x y = (orderFun A x y) * (orderFun B x y) := by rfl
        rw [h10, h9]
  have h_dAx : x ∈ dropA ↔ x ∉ takeA := by
    constructor
    · intro h1 h2
      exact Finset.disjoint_left.mp h_disjA h2 h1
    · intro hn
      exact (h_covA x hxA).resolve_left hn
  have h_dAy : y ∈ dropA ↔ y ∉ takeA := by
    constructor
    · intro h1 h2
      exact Finset.disjoint_left.mp h_disjA h2 h1
    · intro hn
      exact (h_covA y hyA).resolve_left hn
  have h_dBx : x ∈ dropB ↔ x ∉ takeB := by
    constructor
    · intro h1 h2
      exact Finset.disjoint_left.mp h_disjB h2 h1
    · intro hn
      exact (h_covB x hxB).resolve_left hn
  have h_dBy : y ∈ dropB ↔ y ∉ takeB := by
    constructor
    · intro h1 h2
      exact Finset.disjoint_left.mp h_disjB h2 h1
    · intro hn
      exact (h_covB y hyB).resolve_left hn
  let a1 := x ∈ takeA
  let a2 := y ∈ takeA
  let b1 := x ∈ takeB
  let b2 := y ∈ takeB
  have h_fA : flipA ↔ (a1 ∧ ¬a2) ∨ (¬a1 ∧ a2) := by
    rw [hflipA_def]
    simp [h_dAx, h_dAy] <;> rfl
  have h_fB : flipB ↔ (b1 ∧ ¬b2) ∨ (¬b1 ∧ b2) := by
    rw [hflipB_def]
    simp [h_dBx, h_dBy] <;> rfl
  have h_Sx : x ∈ Same ↔ (a1 ∧ b1) ∨ (¬a1 ∧ ¬b1) := by
    have h11 : x ∈ (I ∩ takeA ∩ takeB) ↔ a1 ∧ b1 := by
      constructor
      · intro h
        have h' : x ∈ I ∧ x ∈ takeA ∧ x ∈ takeB := by simpa [Finset.mem_inter] using h
        exact ⟨h'.2.1, h'.2.2⟩
      · rintro ⟨h1, h2⟩
        simp only [Finset.mem_inter]
        exact ⟨⟨hxI, h1⟩, h2⟩
    have h22 : x ∈ (I ∩ dropA ∩ dropB) ↔ (¬a1) ∧ (¬b1) := by
      constructor
      · intro h
        have h' : x ∈ I ∧ x ∈ dropA ∧ x ∈ dropB := by simpa [Finset.mem_inter] using h
        have hna : ¬a1 := h_dAx.mp h'.2.1
        have hnb : ¬b1 := h_dBx.mp h'.2.2
        exact ⟨hna, hnb⟩
      · rintro ⟨h1, h2⟩
        have hda : x ∈ dropA := h_dAx.mpr h1
        have hdb : x ∈ dropB := h_dBx.mpr h2
        simp only [Finset.mem_inter]
        exact ⟨⟨hxI, hda⟩, hdb⟩
    have h : x ∈ Same ↔ x ∈ (I ∩ takeA ∩ takeB) ∨ x ∈ (I ∩ dropA ∩ dropB) := by
      simp [Same] <;> rfl
    rw [h, h11, h22]
  have h_Cx : x ∈ Cross ↔ (a1 ∧ ¬b1) ∨ (¬a1 ∧ b1) := by
    have h12 : x ∈ (I ∩ takeA ∩ dropB) ↔ a1 ∧ (¬b1) := by
      constructor
      · intro h
        have h' : x ∈ I ∧ x ∈ takeA ∧ x ∈ dropB := by simpa [Finset.mem_inter] using h
        have hnb : ¬b1 := h_dBx.mp h'.2.2
        exact ⟨h'.2.1, hnb⟩
      · rintro ⟨h1, h2⟩
        have hdb : x ∈ dropB := h_dBx.mpr h2
        simp only [Finset.mem_inter]
        exact ⟨⟨hxI, h1⟩, hdb⟩
    have h21 : x ∈ (I ∩ dropA ∩ takeB) ↔ (¬a1) ∧ b1 := by
      constructor
      · intro h
        have h' : x ∈ I ∧ x ∈ dropA ∧ x ∈ takeB := by simpa [Finset.mem_inter] using h
        have hna : ¬a1 := h_dAx.mp h'.2.1
        exact ⟨hna, h'.2.2⟩
      · rintro ⟨h1, h2⟩
        have hda : x ∈ dropA := h_dAx.mpr h1
        simp only [Finset.mem_inter]
        exact ⟨⟨hxI, hda⟩, h2⟩
    have h : x ∈ Cross ↔ x ∈ (I ∩ takeA ∩ dropB) ∨ x ∈ (I ∩ dropA ∩ takeB) := by
      simp [Cross] <;> rfl
    rw [h, h12, h21]
  have h_Sy : y ∈ Same ↔ (a2 ∧ b2) ∨ (¬a2 ∧ ¬b2) := by
    have h11 : y ∈ (I ∩ takeA ∩ takeB) ↔ a2 ∧ b2 := by
      constructor
      · intro h
        have h' : y ∈ I ∧ y ∈ takeA ∧ y ∈ takeB := by simpa [Finset.mem_inter] using h
        exact ⟨h'.2.1, h'.2.2⟩
      · rintro ⟨h1, h2⟩
        simp only [Finset.mem_inter]
        exact ⟨⟨hyI, h1⟩, h2⟩
    have h22 : y ∈ (I ∩ dropA ∩ dropB) ↔ (¬a2) ∧ (¬b2) := by
      constructor
      · intro h
        have h' : y ∈ I ∧ y ∈ dropA ∧ y ∈ dropB := by simpa [Finset.mem_inter] using h
        have hna : ¬a2 := h_dAy.mp h'.2.1
        have hnb : ¬b2 := h_dBy.mp h'.2.2
        exact ⟨hna, hnb⟩
      · rintro ⟨h1, h2⟩
        have hda : y ∈ dropA := h_dAy.mpr h1
        have hdb : y ∈ dropB := h_dBy.mpr h2
        simp only [Finset.mem_inter]
        exact ⟨⟨hyI, hda⟩, hdb⟩
    have h : y ∈ Same ↔ y ∈ (I ∩ takeA ∩ takeB) ∨ y ∈ (I ∩ dropA ∩ dropB) := by
      simp [Same] <;> rfl
    rw [h, h11, h22]
  have h_Cy : y ∈ Cross ↔ (a2 ∧ ¬b2) ∨ (¬a2 ∧ b2) := by
    have h12 : y ∈ (I ∩ takeA ∩ dropB) ↔ a2 ∧ (¬b2) := by
      constructor
      · intro h
        have h' : y ∈ I ∧ y ∈ takeA ∧ y ∈ dropB := by simpa [Finset.mem_inter] using h
        have hnb : ¬b2 := h_dBy.mp h'.2.2
        exact ⟨h'.2.1, hnb⟩
      · rintro ⟨h1, h2⟩
        have hdb : y ∈ dropB := h_dBy.mpr h2
        simp only [Finset.mem_inter]
        exact ⟨⟨hyI, h1⟩, hdb⟩
    have h21 : y ∈ (I ∩ dropA ∩ takeB) ↔ (¬a2) ∧ b2 := by
      constructor
      · intro h
        have h' : y ∈ I ∧ y ∈ dropA ∧ y ∈ takeB := by simpa [Finset.mem_inter] using h
        have hna : ¬a2 := h_dAy.mp h'.2.1
        exact ⟨hna, h'.2.2⟩
      · rintro ⟨h1, h2⟩
        have hda : y ∈ dropA := h_dAy.mpr h1
        simp only [Finset.mem_inter]
        exact ⟨⟨hyI, hda⟩, h2⟩
    have h : y ∈ Cross ↔ y ∈ (I ∩ takeA ∩ dropB) ∨ y ∈ (I ∩ dropA ∩ takeB) := by
      simp [Cross] <;> rfl
    rw [h, h12, h21]
  have h_equiv : ((flipA ∧ ¬flipB) ∨ (¬flipA ∧ flipB)) ↔
      ((x ∈ Same ∧ y ∈ Cross) ∨ (x ∈ Cross ∧ y ∈ Same)) := by
    rw [h_fA, h_fB, h_Sx, h_Cx, h_Sy, h_Cy]
    exact xor_equiv a1 a2 b1 b2
  rw [h_main1, h_equiv]

end MarcusTardos.SameCrossCharacterization
