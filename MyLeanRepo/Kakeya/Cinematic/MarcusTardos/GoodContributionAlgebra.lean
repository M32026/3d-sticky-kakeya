import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Definitions
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.OrderFunction
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.DyadicDecomposition
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.BlockStructure
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.DirectBound
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Good contribution lemma (clean version)

Core algebraic identity: `r - c = (a - b)^2 ≥ 0`.
-/

namespace MarcusTardos.GoodContributionClean

open BigOperators Finset

variable {α : Type*} [DecidableEq α]

/-- orderFun returns ±1 when both elements are in the list and distinct. -/
private lemma orderFun_values {A : List α} {x y : α}
    (hx : x ∈ A) (hy : y ∈ A) (_hne : x ≠ y) :
    orderFun A x y = 1 ∨ orderFun A x y = -1 := by
  have h : orderFun A x y = 1 ∨ orderFun A x y = -1 := by
    simp [orderFun, hx, hy]
    omega
  exact h

/--
Core algebraic lemma: `r - c = (a - b)^2`.
-/
lemma r_minus_c_eq_sq {Bs Bt : List α}
    (Same Cross : Finset α)
    (h_partition : Same ∪ Cross = Bs.toFinset ∩ Bt.toFinset)
    (h_disj : Disjoint Same Cross)
    (h_char : ∀ (x y : α), x ∈ Bs.toFinset ∩ Bt.toFinset → y ∈ Bs.toFinset ∩ Bt.toFinset → x ≠ y →
      (orderFun2 Bs Bt x y = 1 ↔ (x ∈ Same ∧ y ∈ Cross) ∨ (x ∈ Cross ∧ y ∈ Same))) :
    ((Bs.toFinset ∩ Bt.toFinset).card : ℤ) -
      ∑ p ∈ (Bs.toFinset ∩ Bt.toFinset).offDiag, orderFun2 Bs Bt p.1 p.2 =
    ((Same.card : ℤ) - (Cross.card : ℤ))^2 := by
  let I : Finset α := Bs.toFinset ∩ Bt.toFinset
  let a : ℕ := Same.card
  let b : ℕ := Cross.card
  have h_card : I.card = a + b := by
    have h_eq : (Same ∪ Cross).card = I.card := congr_arg Finset.card h_partition
    have h : I.card = (Same ∪ Cross).card := h_eq.symm
    rw [h, Finset.card_union_of_disjoint h_disj]
  let S1 : Finset (α × α) := Same ×ˢ Cross
  let S2 : Finset (α × α) := Cross ×ˢ Same
  let Srest : Finset (α × α) := I.offDiag \ (S1 ∪ S2)
  have h_disj12 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 : p.1 ∈ Same := (Finset.mem_product.mp hp1).1
    have h2 : p.1 ∈ Cross := (Finset.mem_product.mp hp2).1
    exact Finset.disjoint_left.mp h_disj h1 h2
  have h_sub1 : S1 ⊆ I.offDiag := by
    intro p hp
    have h4 : p.1 ∈ Same ∧ p.2 ∈ Cross := Finset.mem_product.mp hp
    have h1I : p.1 ∈ I := h_partition.subset (Finset.mem_union_left _ h4.1)
    have h2I : p.2 ∈ I := h_partition.subset (Finset.mem_union_right _ h4.2)
    have hne : p.1 ≠ p.2 := by
      intro h; rw [h] at h4; exact Finset.disjoint_left.mp h_disj h4.1 h4.2
    exact Finset.mem_offDiag.mpr ⟨h1I, h2I, hne⟩
  have h_sub2 : S2 ⊆ I.offDiag := by
    intro p hp
    have h4 : p.1 ∈ Cross ∧ p.2 ∈ Same := Finset.mem_product.mp hp
    have h1I : p.1 ∈ I := h_partition.subset (Finset.mem_union_right _ h4.1)
    have h2I : p.2 ∈ I := h_partition.subset (Finset.mem_union_left _ h4.2)
    have hne : p.1 ≠ p.2 := by
      intro h; rw [h] at h4; exact Finset.disjoint_left.mp h_disj h4.2 h4.1
    exact Finset.mem_offDiag.mpr ⟨h1I, h2I, hne⟩
  have h_union : S1 ∪ S2 ⊆ I.offDiag := Finset.union_subset h_sub1 h_sub2
  have h_sum1 : ∑ p ∈ S1, orderFun2 Bs Bt p.1 p.2 = (a : ℤ) * (b : ℤ) := by
    have h : ∀ p ∈ S1, orderFun2 Bs Bt p.1 p.2 = 1 := by
      intro p hp
      have h4 : p.1 ∈ Same ∧ p.2 ∈ Cross := Finset.mem_product.mp hp
      have h1I : p.1 ∈ I := h_partition.subset (Finset.mem_union_left _ h4.1)
      have h2I : p.2 ∈ I := h_partition.subset (Finset.mem_union_right _ h4.2)
      have hne : p.1 ≠ p.2 := by
        intro h; rw [h] at h4; exact Finset.disjoint_left.mp h_disj h4.1 h4.2
      exact (h_char p.1 p.2 h1I h2I hne).mpr (Or.inl h4)
    rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_product] <;> ring
  have h_sum2 : ∑ p ∈ S2, orderFun2 Bs Bt p.1 p.2 = (a : ℤ) * (b : ℤ) := by
    have h : ∀ p ∈ S2, orderFun2 Bs Bt p.1 p.2 = 1 := by
      intro p hp
      have h4 : p.1 ∈ Cross ∧ p.2 ∈ Same := Finset.mem_product.mp hp
      have h1I : p.1 ∈ I := h_partition.subset (Finset.mem_union_right _ h4.1)
      have h2I : p.2 ∈ I := h_partition.subset (Finset.mem_union_left _ h4.2)
      have hne : p.1 ≠ p.2 := by
        intro h; rw [h] at h4; exact Finset.disjoint_left.mp h_disj h4.2 h4.1
      exact (h_char p.1 p.2 h1I h2I hne).mpr (Or.inr h4)
    rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_product] <;> ring
  have h_sum_rest : ∑ p ∈ Srest, orderFun2 Bs Bt p.1 p.2 = -((Srest.card : ℤ)) := by
    have h : ∀ p ∈ Srest, orderFun2 Bs Bt p.1 p.2 = -1 := by
      intro p hp
      have h5 : p ∈ I.offDiag := Finset.mem_sdiff.mp hp |>.1
      have h6 : p ∉ S1 ∪ S2 := Finset.mem_sdiff.mp hp |>.2
      have hpe : p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≠ p.2 := Finset.mem_offDiag.mp h5
      have h7 : ¬((p.1 ∈ Same ∧ p.2 ∈ Cross) ∨ (p.1 ∈ Cross ∧ p.2 ∈ Same)) := by
        simpa [S1, S2, Finset.mem_union, Finset.mem_product] using h6
      have h8 : orderFun2 Bs Bt p.1 p.2 ≠ 1 := by
        intro h9; exact h7 ((h_char p.1 p.2 hpe.1 hpe.2.1 hpe.2.2).mp h9)
      have h10 : p.1 ∈ Bs := by simpa [List.mem_toFinset] using (Finset.mem_inter.mp hpe.1).1
      have h11 : p.2 ∈ Bs := by simpa [List.mem_toFinset] using (Finset.mem_inter.mp hpe.2.1).1
      have h12 : p.1 ∈ Bt := by simpa [List.mem_toFinset] using (Finset.mem_inter.mp hpe.1).2
      have h13 : p.2 ∈ Bt := by simpa [List.mem_toFinset] using (Finset.mem_inter.mp hpe.2.1).2
      have h14 : orderFun Bs p.1 p.2 = 1 ∨ orderFun Bs p.1 p.2 = -1 := orderFun_values h10 h11 hpe.2.2
      have h15 : orderFun Bt p.1 p.2 = 1 ∨ orderFun Bt p.1 p.2 = -1 := orderFun_values h12 h13 hpe.2.2
      have h9 : orderFun2 Bs Bt p.1 p.2 = 1 ∨ orderFun2 Bs Bt p.1 p.2 = -1 := by
        have h_def : orderFun2 Bs Bt p.1 p.2 = orderFun Bs p.1 p.2 * orderFun Bt p.1 p.2 := by rfl
        rw [h_def]
        rcases h14 with (h14 | h14) <;> rcases h15 with (h15 | h15)
        · left; rw [h14, h15] <;> norm_num
        · right; rw [h14, h15] <;> norm_num
        · right; rw [h14, h15] <;> norm_num
        · left; rw [h14, h15] <;> norm_num
      rcases h9 with (h9 | h9) <;> tauto
    rw [Finset.sum_congr rfl h, Finset.sum_const] <;> ring
  have h_card_S12 : (S1 ∪ S2).card = 2 * a * b := by
    rw [Finset.card_union_of_disjoint h_disj12, Finset.card_product, Finset.card_product] <;> ring
  let r : ℕ := I.card
  have hr_card : r = a + b := h_card
  have h_part2 : I.offDiag = S1 ∪ S2 ∪ Srest := by
    ext p; simp only [Srest, Finset.mem_union, Finset.mem_sdiff] <;> tauto
  have h_disj_all : Disjoint (S1 ∪ S2) Srest := Finset.disjoint_sdiff
  have h_sum_all : ∑ p ∈ I.offDiag, orderFun2 Bs Bt p.1 p.2 =
      (a : ℤ) * (b : ℤ) + (a : ℤ) * (b : ℤ) - (Srest.card : ℤ) := by
    rw [h_part2, Finset.sum_union h_disj_all, Finset.sum_union h_disj12, h_sum1, h_sum2, h_sum_rest] <;> ring
  by_cases h_r0 : r = 0
  · have hI_empty : I = ∅ := by simpa [Finset.card_eq_zero, r] using h_r0
    have hSame_empty : Same = ∅ := by
      have h : Same ⊆ Same ∪ Cross := by simp
      have h' : Same ⊆ I := by rw [h_partition] at *; exact h
      rw [hI_empty] at h'; simpa using h'
    have hCross_empty : Cross = ∅ := by
      have h : Cross ⊆ Same ∪ Cross := by simp
      have h' : Cross ⊆ I := by rw [h_partition] at *; exact h
      rw [hI_empty] at h'; simpa using h'
    have h_ie : I.offDiag = ∅ := by rw [hI_empty] <;> simp
    have h_a0 : a = 0 := by
      simp [a, hSame_empty]
    have h_b0 : b = 0 := by
      simp [b, hCross_empty]
    have h_goal : (I.card : ℤ) - ∑ p ∈ I.offDiag, orderFun2 Bs Bt p.1 p.2 = ((a : ℤ) - (b : ℤ))^2 := by
      have hIcard : I.card = 0 := by rw [hI_empty] <;> simp
      rw [hIcard, h_ie, h_a0, h_b0] <;> simp
    simpa [a, b] using h_goal
  · have hr_pos : 0 < r := Nat.pos_of_ne_zero h_r0
    have h_le : (S1 ∪ S2).card ≤ I.offDiag.card := Finset.card_le_card h_union
    have h_off_int : (I.offDiag.card : ℤ) = (r : ℤ) * ((r : ℤ) - 1) := by
      have h1 : I.offDiag.card = r * (r - 1) := by
        rw [Finset.offDiag_card, show I.card = r from rfl]
        have h2 : 1 ≤ r := hr_pos
        have h3 : r * r - r = r * (r - 1) := by
          obtain ⟨r', hr'⟩ : ∃ r', r = r' + 1 := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 from by linarith)
          rw [hr']
          simp [Nat.mul_succ]
        exact h3
      rw [h1]
      have h2 : 0 < r := hr_pos
      have h3 : ((r * (r - 1) : ℕ) : ℤ) = (r : ℤ) * ((r : ℤ) - 1) := by
        simp [Nat.cast_mul, Nat.cast_sub (show 1 ≤ r from h2)]
      exact h3
    have h1sdiff : Srest.card = I.offDiag.card - (S1 ∪ S2).card := by
      have h_eq : Srest = I.offDiag \ (S1 ∪ S2) := by rfl
      rw [h_eq, Finset.card_sdiff]
      have h_inter : (S1 ∪ S2) ∩ I.offDiag = S1 ∪ S2 := by
        rw [Finset.inter_comm]
        exact Finset.inter_eq_right.mpr h_union
      rw [h_inter]
    have h_rest_int : (Srest.card : ℤ) = (I.offDiag.card : ℤ) - ((S1 ∪ S2).card : ℤ) := by
      rw [h1sdiff, Nat.cast_sub h_le]
    have h_main_eq : ∑ p ∈ I.offDiag, orderFun2 Bs Bt p.1 p.2 =
        (a : ℤ) * (b : ℤ) + (a : ℤ) * (b : ℤ) - ((I.offDiag.card : ℤ) - ((S1 ∪ S2).card : ℤ)) := by
      rw [h_sum_all, h_rest_int]
    rw [h_main_eq, h_card_S12, h_off_int]
    have hrab : (r : ℤ) = (a : ℤ) + (b : ℤ) := by exact_mod_cast hr_card
    have h_goal : (r : ℤ) - ((a : ℤ) * (b : ℤ) + (a : ℤ) * (b : ℤ) - ((r : ℤ) * ((r : ℤ) - 1) - ((2 * a * b : ℕ) : ℤ))) =
        ((a : ℤ) - (b : ℤ))^2 := by
      have h_cast : ((2 * a * b : ℕ) : ℤ) = 2 * (a : ℤ) * (b : ℤ) := by
        simp [mul_assoc]
      rw [h_cast, hrab]
      ring
    exact h_goal

/-- Corollary: `r - c ≥ 0`. -/
lemma good_contribution_of_partition {Bs Bt : List α}
    (Same Cross : Finset α)
    (h_partition : Same ∪ Cross = Bs.toFinset ∩ Bt.toFinset)
    (h_disj : Disjoint Same Cross)
    (h_char : ∀ (x y : α), x ∈ Bs.toFinset ∩ Bt.toFinset → y ∈ Bs.toFinset ∩ Bt.toFinset → x ≠ y →
      (orderFun2 Bs Bt x y = 1 ↔ (x ∈ Same ∧ y ∈ Cross) ∨ (x ∈ Cross ∧ y ∈ Same))) :
    ((Bs.toFinset ∩ Bt.toFinset).card : ℤ) -
      ∑ p ∈ (Bs.toFinset ∩ Bt.toFinset).offDiag, orderFun2 Bs Bt p.1 p.2 ≥ 0 := by
  have h_main := r_minus_c_eq_sq Same Cross h_partition h_disj h_char
  rw [h_main]
  exact sq_nonneg _

end MarcusTardos.GoodContributionClean
