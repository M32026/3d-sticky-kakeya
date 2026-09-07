import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingUniformRefinementStatement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# One-level branching uniformization

Given two nested partition levels where every occupied level-1 cell has equal
cardinality `M`, produce a subset `A'` such that every occupied level-0 parent
has exactly `2^k` occupied level-1 children for some fixed `k`, with retention
loss at most `2 * (Nat.log 2 childBound + 1)`.
-/

open Finset

namespace Kakeya.Assouad

lemma one_level_branching_uniformization
    {α : Type} [DecidableEq α]
    (A₁ : Finset α) (hA₁ : A₁.Nonempty)
    (P : ℕ → Finset (Finset α))
    (childBound : ℕ) (hcb : 0 < childBound)
    (M : ℕ)
    (h0_disj : ∀ c₁ ∈ P 0, ∀ c₂ ∈ P 0, c₁ ≠ c₂ → Disjoint c₁ c₂)
    (h0_cover : A₁ ⊆ Finset.biUnion (P 0) id)
    (h1_disj : ∀ c₁ ∈ P 1, ∀ c₂ ∈ P 1, c₁ ≠ c₂ → Disjoint c₁ c₂)
    (h1_cover : A₁ ⊆ Finset.biUnion (P 1) id)
    (h_refine : ∀ child ∈ P 1, ∃ parent ∈ P 0, child ⊆ parent)
    (h_childBound : ∀ parent ∈ P 0, (partitionChildren P 0 parent).card ≤ childBound)
    (hM : ∀ cell ∈ P 1, (A₁ ∩ cell).Nonempty → (A₁ ∩ cell).card = M) :
    ∃ (A' : Finset α) (k : ℕ),
        A'.Nonempty ∧
        A' ⊆ A₁ ∧
        (A₁.card : ℝ) ≤ (2 * (Nat.log 2 childBound + 1) : ℝ) * (A'.card : ℝ) ∧
        2 ^ k ≤ childBound ∧
        (∀ parent ∈ P 0, (A' ∩ parent).Nonempty →
          (occupiedPartitionChildren A' P 0 parent).card = 2 ^ k) ∧
        (∀ cell ∈ P 1, (A' ∩ cell).Nonempty → A' ∩ cell = A₁ ∩ cell) := by
  let occupiedParents := (P 0).filter (fun p => (A₁ ∩ p).Nonempty)
  let c (p : Finset α) := (occupiedPartitionChildren A₁ P 0 p).card
  let bin (p : Finset α) := Nat.log 2 (c p)
  let K := Finset.range (Nat.log 2 childBound + 1)

  have hmem_inter : ∀ {x : α} {s t : Finset α}, x ∈ s ∩ t → x ∈ s ∧ x ∈ t := by
    intro x s t h
    simpa [Finset.mem_inter] using h

  have h_c_pos : ∀ p ∈ occupiedParents, 0 < c p := by
    intro p hp
    have h_p_in_P0 : p ∈ P 0 := (mem_filter.mp hp).1
    have h_p_occ : (A₁ ∩ p).Nonempty := (mem_filter.mp hp).2
    rcases h_p_occ with ⟨x, hx⟩
    have h_x_in_A1 : x ∈ A₁ := (hmem_inter hx).1
    have h_x_in_p : x ∈ p := (hmem_inter hx).2
    have h9 : x ∈ Finset.biUnion (P 1) id := h1_cover h_x_in_A1
    rcases mem_biUnion.mp h9 with ⟨child, hchild, hxchild⟩
    have h10 : x ∈ child := hxchild
    rcases h_refine child hchild with ⟨parent, hparent, hsub⟩
    have h12 : x ∈ parent := hsub h10
    have h13 : parent = p := by
      by_cases h : parent = p
      · exact h
      · have h14 : Disjoint parent p := h0_disj parent hparent p h_p_in_P0 h
        have h15 : x ∈ parent ∩ p := Finset.mem_inter.mpr ⟨h12, h_x_in_p⟩
        have h16 : x ∈ (∅ : Finset α) := h14.le_bot h15
        simp at h16
    have h17 : child ⊆ p := by rw [h13] at hsub; exact hsub
    have h18 : child ∈ partitionChildren P 0 p := by
      simp only [partitionChildren, mem_filter] <;> exact ⟨hchild, h17⟩
    have h19 : (A₁ ∩ child).Nonempty := ⟨x, Finset.mem_inter.mpr ⟨h_x_in_A1, h10⟩⟩
    have h20 : child ∈ occupiedPartitionChildren A₁ P 0 p := by
      simp only [occupiedPartitionChildren, mem_filter] <;> exact ⟨h18, h19⟩
    exact Finset.card_pos.mpr ⟨child, h20⟩

  have h_c_bound : ∀ p ∈ occupiedParents, c p ≤ childBound := by
    intro p hp
    have h_p_in_P0 : p ∈ P 0 := (mem_filter.mp hp).1
    have h1 : occupiedPartitionChildren A₁ P 0 p ⊆ partitionChildren P 0 p :=
      filter_subset _ _
    have h2 : c p ≤ (partitionChildren P 0 p).card := card_le_card h1
    have h3 : (partitionChildren P 0 p).card ≤ childBound := h_childBound p h_p_in_P0
    exact le_trans h2 h3

  have h_bin_in_K : ∀ p ∈ occupiedParents, bin p ∈ K := by
    intro p hp
    have h1 : c p ≤ childBound := h_c_bound p hp
    have h2 : bin p ≤ Nat.log 2 childBound := Nat.log_mono_right h1
    simp only [K, mem_range] <;> omega

  let binParents (b : ℕ) := occupiedParents.filter (fun p => bin p = b)
  let binMass (b : ℕ) := M * ∑ p ∈ binParents b, c p
  let occupiedChildren := (P 1).filter (fun child => (A₁ ∩ child).Nonempty)

  have h_disj_parents : ∀ p1 ∈ occupiedParents, ∀ p2 ∈ occupiedParents, p1 ≠ p2 →
      Disjoint (occupiedPartitionChildren A₁ P 0 p1)
        (occupiedPartitionChildren A₁ P 0 p2) := by
    intro p1 hp1 p2 hp2 hne
    have h1 : p1 ∈ P 0 := (mem_filter.mp hp1).1
    have h2 : p2 ∈ P 0 := (mem_filter.mp hp2).1
    have h3 : Disjoint p1 p2 := h0_disj p1 h1 p2 h2 hne
    rw [Finset.disjoint_left]
    intro child h4 h5
    have h6 : (A₁ ∩ child).Nonempty := (mem_filter.mp h4).2
    rcases h6 with ⟨x, hx⟩
    have h7 : x ∈ child := (hmem_inter hx).2
    have h8 : child ⊆ p1 := (mem_filter.mp (mem_filter.mp h4).1).2
    have h9 : child ⊆ p2 := (mem_filter.mp (mem_filter.mp h5).1).2
    have h10 : x ∈ p1 := h8 h7
    have h11 : x ∈ p2 := h9 h7
    have h12 : x ∈ p1 ∩ p2 := Finset.mem_inter.mpr ⟨h10, h11⟩
    have h13 : x ∈ (∅ : Finset α) := h3.le_bot h12
    simp at h13

  have h_occ_children_eq : occupiedChildren =
      Finset.biUnion occupiedParents
        (fun p => occupiedPartitionChildren A₁ P 0 p) := by
    ext child
    simp only [occupiedChildren, mem_biUnion, mem_filter]
    constructor
    · rintro ⟨hchild, hocc⟩
      rcases h_refine child hchild with ⟨parent, hparent, hsub⟩
      have h_parent_occ : (A₁ ∩ parent).Nonempty := by
        rcases hocc with ⟨x, hx⟩
        have h_x_in_A1 : x ∈ A₁ := (hmem_inter hx).1
        have h_x_in_child : x ∈ child := (hmem_inter hx).2
        exact ⟨x, Finset.mem_inter.mpr ⟨h_x_in_A1, hsub h_x_in_child⟩⟩
      have h_parent_in_occ : parent ∈ occupiedParents := by
        simp only [occupiedParents, mem_filter] <;> exact ⟨hparent, h_parent_occ⟩
      have h_child_in_part : child ∈ partitionChildren P 0 parent := by
        simp only [partitionChildren, mem_filter] <;> exact ⟨hchild, hsub⟩
      have h_child_in_occ_part : child ∈ occupiedPartitionChildren A₁ P 0 parent := by
        simp only [occupiedPartitionChildren, mem_filter] <;> exact ⟨h_child_in_part, hocc⟩
      exact ⟨parent, h_parent_in_occ, h_child_in_occ_part⟩
    · rintro ⟨p, hp, hmem⟩
      have h1 : child ∈ partitionChildren P 0 p := (mem_filter.mp hmem).1
      have h2 : (A₁ ∩ child).Nonempty := (mem_filter.mp hmem).2
      have h3 : child ∈ P 1 := (mem_filter.mp h1).1
      exact ⟨h3, h2⟩

  have h_disj_inter1 :
      (occupiedChildren : Set (Finset α)).PairwiseDisjoint (fun child => A₁ ∩ child) := by
    intro c1 hc1 c2 hc2 hne
    have h1 : c1 ∈ P 1 := (mem_filter.mp hc1).1
    have h2 : c2 ∈ P 1 := (mem_filter.mp hc2).1
    have h3 : Disjoint c1 c2 := h1_disj c1 h1 c2 h2 hne
    exact h3.mono (by simp) (by simp)

  have h_A1_eq : A₁ =
      Finset.biUnion occupiedChildren (fun child => A₁ ∩ child) := by
    ext x
    simp only [mem_biUnion]
    constructor
    · intro hx
      have h9 : x ∈ Finset.biUnion (P 1) id := h1_cover hx
      rcases mem_biUnion.mp h9 with ⟨child, hchild, hxchild⟩
      have h10 : x ∈ child := hxchild
      have h11 : (A₁ ∩ child).Nonempty :=
        ⟨x, Finset.mem_inter.mpr ⟨hx, h10⟩⟩
      have h12 : child ∈ occupiedChildren := by
        simp only [occupiedChildren, mem_filter] <;> exact ⟨hchild, h11⟩
      exact ⟨child, h12, Finset.mem_inter.mpr ⟨hx, h10⟩⟩
    · rintro ⟨child, _, hx⟩
      exact (hmem_inter hx).1

  have h_A1_card :
      A₁.card = ∑ child ∈ occupiedChildren, (A₁ ∩ child).card := by
    have h_card :
        (Finset.biUnion occupiedChildren (fun child => A₁ ∩ child)).card =
          ∑ child ∈ occupiedChildren, (A₁ ∩ child).card :=
      card_biUnion h_disj_inter1
    have h_eq1 :
        A₁.card =
          (Finset.biUnion occupiedChildren (fun child => A₁ ∩ child)).card := by
      apply congr_arg Finset.card h_A1_eq
    exact h_eq1.trans h_card

  have h_sum_M :
      ∑ child ∈ occupiedChildren, (A₁ ∩ child).card =
        M * occupiedChildren.card := by
    have h : ∀ child ∈ occupiedChildren, (A₁ ∩ child).card = M := by
      intro child hchild
      have h1 : child ∈ P 1 := (mem_filter.mp hchild).1
      have h2 : (A₁ ∩ child).Nonempty := (mem_filter.mp hchild).2
      exact hM child h1 h2
    rw [sum_congr rfl h]
    simp [mul_comm]

  have h_occ_card :
      occupiedChildren.card = ∑ p ∈ occupiedParents, c p := by
    rw [h_occ_children_eq, card_biUnion h_disj_parents]

  have h_mass_decomp :
      A₁.card = M * ∑ p ∈ occupiedParents, c p := by
    rw [h_A1_card, h_sum_M, h_occ_card]

  have h_sum_binMass : ∑ b ∈ K, binMass b = A₁.card := by
    have h1 :
        ∑ b ∈ K, binMass b =
          M * ∑ b ∈ K, ∑ p ∈ binParents b, c p := by
      have h11 :
          ∑ b ∈ K, binMass b =
            ∑ b ∈ K, (M * ∑ p ∈ binParents b, c p) := by
        apply Finset.sum_congr rfl
        intro b _
        rfl
      rw [h11, Finset.mul_sum]
    rw [h1]
    have h2 :
        ∑ b ∈ K, ∑ p ∈ binParents b, c p =
          ∑ p ∈ occupiedParents, c p := by
      have h3 :
          ∑ b ∈ K, ∑ p ∈ binParents b, c p =
            ∑ b ∈ K, ∑ p ∈ occupiedParents,
              (if bin p = b then c p else 0) := by
        apply Finset.sum_congr rfl
        intro b _
        simp [binParents, Finset.sum_ite]
      rw [h3]
      have h4 :
          ∑ b ∈ K, ∑ p ∈ occupiedParents,
              (if bin p = b then c p else 0) =
            ∑ p ∈ occupiedParents, ∑ b ∈ K,
              (if bin p = b then c p else 0) := by
        rw [Finset.sum_comm]
      rw [h4]
      apply Finset.sum_congr rfl
      intro p hp
      have h5 : bin p ∈ K := h_bin_in_K p hp
      simp [h5]
    rw [h2, h_mass_decomp]

  have hK_nonempty : K.Nonempty := by simp [K]

  rcases Finset.exists_max_image K binMass hK_nonempty with
    ⟨k_opt, hk_opt, h_max⟩

  have hK_card : K.card = Nat.log 2 childBound + 1 := by simp [K]

  have h_pigeon : A₁.card ≤ K.card * binMass k_opt := by
    calc
      A₁.card = ∑ b ∈ K, binMass b := h_sum_binMass.symm
      _ ≤ ∑ b ∈ K, binMass k_opt :=
        Finset.sum_le_sum (fun j _ => h_max j ‹_›)
      _ = K.card * binMass k_opt := by simp

  have h_bounds :
      ∀ p ∈ binParents k_opt,
        2 ^ k_opt ≤ c p ∧ c p < 2 ^ (k_opt + 1) := by
    intro p hp
    have h_p_in_occ : p ∈ occupiedParents := (mem_filter.mp hp).1
    have h_bin_eq : bin p = k_opt := (mem_filter.mp hp).2
    have h_pos : 0 < c p := h_c_pos p h_p_in_occ
    have h_log_eq : Nat.log 2 (c p) = k_opt := by
      simpa [bin] using h_bin_eq
    have h_iff :
        Nat.log 2 (c p) = k_opt ↔
          2 ^ k_opt ≤ c p ∧ c p < 2 ^ (k_opt + 1) :=
      Nat.log_eq_iff (Or.inr ⟨by norm_num, h_pos.ne'⟩)
    exact h_iff.mp h_log_eq

  have h_select :
      ∀ p ∈ binParents k_opt, ∃ S : Finset (Finset α),
        S ⊆ occupiedPartitionChildren A₁ P 0 p ∧ S.card = 2 ^ k_opt := by
    intro p hp
    have h1 : 2 ^ k_opt ≤ c p := (h_bounds p hp).1
    exact Finset.exists_subset_card_eq h1

  let S : Finset α → Finset (Finset α) := fun p =>
    if h : p ∈ binParents k_opt then
      Classical.choose (h_select p h)
    else
      ∅

  have hS :
      ∀ p ∈ binParents k_opt,
        S p ⊆ occupiedPartitionChildren A₁ P 0 p ∧
          (S p).card = 2 ^ k_opt := by
    intro p hp
    have h_eq : S p = Classical.choose (h_select p hp) := by
      simp [S, hp]
    rw [h_eq]
    exact Classical.choose_spec (h_select p hp)

  let selectedChildren := Finset.biUnion (binParents k_opt) S
  let A' : Finset α :=
    Finset.biUnion selectedChildren (fun child => A₁ ∩ child)

  have h_disj_S :
      ∀ p1 ∈ binParents k_opt, ∀ p2 ∈ binParents k_opt, p1 ≠ p2 →
        Disjoint (S p1) (S p2) := by
    intro p1 hp1 p2 hp2 hne
    have h1 : S p1 ⊆ occupiedPartitionChildren A₁ P 0 p1 := (hS p1 hp1).1
    have h2 : S p2 ⊆ occupiedPartitionChildren A₁ P 0 p2 := (hS p2 hp2).1
    have h_p1_in_occ : p1 ∈ occupiedParents := (mem_filter.mp hp1).1
    have h_p2_in_occ : p2 ∈ occupiedParents := (mem_filter.mp hp2).1
    have h3 :
        Disjoint (occupiedPartitionChildren A₁ P 0 p1)
          (occupiedPartitionChildren A₁ P 0 p2) :=
      h_disj_parents p1 h_p1_in_occ p2 h_p2_in_occ hne
    exact Disjoint.mono h1 h2 h3

  have h_selected_card :
      selectedChildren.card =
        ∑ p ∈ binParents k_opt, 2 ^ k_opt := by
    rw [card_biUnion h_disj_S]
    apply Finset.sum_congr rfl
    intro p hp
    exact (hS p hp).2

  have hA'_sub : A' ⊆ A₁ := by
    intro x hx
    rcases mem_biUnion.mp hx with ⟨child, _, hxc⟩
    exact (hmem_inter hxc).1

  have h_sel_in_P1 : ∀ child ∈ selectedChildren, child ∈ P 1 := by
    intro child hchild
    rcases mem_biUnion.mp hchild with ⟨p, hp, hmem⟩
    have h2 :
        child ∈ occupiedPartitionChildren A₁ P 0 p :=
      (hS p hp).1 hmem
    exact (mem_filter.mp (mem_filter.mp h2).1).1

  have h_sel_parent :
      ∀ child ∈ selectedChildren,
        ∃ p ∈ binParents k_opt, child ⊆ p := by
    intro child hchild
    rcases mem_biUnion.mp hchild with ⟨p, hp, hmem⟩
    have h2 :
        child ∈ occupiedPartitionChildren A₁ P 0 p :=
      (hS p hp).1 hmem
    have h3 : child ⊆ p := (mem_filter.mp (mem_filter.mp h2).1).2
    exact ⟨p, hp, h3⟩

  have h_disj_A' :
      (selectedChildren : Set (Finset α)).PairwiseDisjoint
        (fun child => A₁ ∩ child) := by
    intro c1 hc1 c2 hc2 hne
    have h1 : c1 ∈ P 1 := h_sel_in_P1 c1 hc1
    have h2 : c2 ∈ P 1 := h_sel_in_P1 c2 hc2
    have h3 : Disjoint c1 c2 := h1_disj c1 h1 c2 h2 hne
    exact h3.mono (by simp) (by simp)

  have hA'_card :
      A'.card = ∑ child ∈ selectedChildren, (A₁ ∩ child).card := by
    rw [card_biUnion h_disj_A']

  have h_sum_selected_M :
      ∑ child ∈ selectedChildren, (A₁ ∩ child).card =
        M * selectedChildren.card := by
    have h : ∀ child ∈ selectedChildren, (A₁ ∩ child).card = M := by
      intro child hchild
      rcases mem_biUnion.mp hchild with ⟨p, hp, hmem⟩
      have h2 :
          child ∈ occupiedPartitionChildren A₁ P 0 p :=
        (hS p hp).1 hmem
      have h3 : child ∈ P 1 := (mem_filter.mp (mem_filter.mp h2).1).1
      have h4 : (A₁ ∩ child).Nonempty := (mem_filter.mp h2).2
      exact hM child h3 h4
    rw [sum_congr rfl h]
    simp [mul_comm]

  have hA'_card2 : A'.card = M * selectedChildren.card := by
    rw [hA'_card, h_sum_selected_M]

  have h_retention1 : binMass k_opt ≤ 2 * A'.card := by
    have h1 :
        binMass k_opt = M * ∑ p ∈ binParents k_opt, c p := by
      rfl
    rw [h1, hA'_card2, h_selected_card]
    have h2 :
        ∀ p ∈ binParents k_opt, c p ≤ 2 * 2 ^ k_opt := by
      intro p hp
      have h3 : c p < 2 ^ (k_opt + 1) := (h_bounds p hp).2
      have h4 : 2 ^ (k_opt + 1) = 2 * 2 ^ k_opt := by ring
      rw [h4] at h3
      omega
    have h5 :
        ∑ p ∈ binParents k_opt, c p ≤
          ∑ p ∈ binParents k_opt, (2 * 2 ^ k_opt) :=
      Finset.sum_le_sum h2
    have h6 :
        M * ∑ p ∈ binParents k_opt, c p ≤
          M * ∑ p ∈ binParents k_opt, (2 * 2 ^ k_opt) := by
      gcongr
    have h7 :
        M * ∑ p ∈ binParents k_opt, (2 * 2 ^ k_opt) =
          2 * (M * ∑ p ∈ binParents k_opt, 2 ^ k_opt) := by
      have h71 :
          M * ∑ p ∈ binParents k_opt, (2 * 2 ^ k_opt) =
            ∑ p ∈ binParents k_opt, (M * (2 * 2 ^ k_opt)) := by
        rw [Finset.mul_sum]
      rw [h71]
      have h72 :
          ∑ p ∈ binParents k_opt, (M * (2 * 2 ^ k_opt)) =
            ∑ p ∈ binParents k_opt, (2 * (M * 2 ^ k_opt)) := by
        apply Finset.sum_congr rfl
        intro _ _
        ring
      rw [h72]
      have h73 :
          ∑ p ∈ binParents k_opt, (2 * (M * 2 ^ k_opt)) =
            2 * ∑ p ∈ binParents k_opt, (M * 2 ^ k_opt) := by
        rw [Finset.mul_sum]
      rw [h73]
      have h74 :
          ∑ p ∈ binParents k_opt, (M * 2 ^ k_opt) =
            M * ∑ p ∈ binParents k_opt, 2 ^ k_opt := by
        rw [Finset.mul_sum]
      rw [h74]
    rw [h7] at h6
    exact h6

  have h_retention_final :
      (A₁.card : ℝ) ≤
        (2 * (Nat.log 2 childBound + 1) : ℝ) * (A'.card : ℝ) := by
    have h1 : A₁.card ≤ K.card * binMass k_opt := h_pigeon
    have h2 : binMass k_opt ≤ 2 * A'.card := h_retention1
    have h3 : A₁.card ≤ K.card * (2 * A'.card) := by
      calc
        A₁.card ≤ K.card * binMass k_opt := h1
        _ ≤ K.card * (2 * A'.card) := by gcongr
    have h4 :
        (A₁.card : ℝ) ≤ (K.card : ℝ) * (2 * (A'.card : ℝ)) := by
      exact_mod_cast h3
    have h5 :
        (K.card : ℝ) = (Nat.log 2 childBound + 1 : ℝ) := by
      rw [hK_card] <;> norm_cast
    rw [h5] at h4
    have h6 :
        (Nat.log 2 childBound + 1 : ℝ) * (2 * (A'.card : ℝ)) =
          (2 * (Nat.log 2 childBound + 1) : ℝ) * (A'.card : ℝ) := by
      ring
    rw [h6] at h4
    exact h4

  have h_k_bound : 2 ^ k_opt ≤ childBound := by
    have h1 : k_opt ∈ K := hk_opt
    have h2 : k_opt ≤ Nat.log 2 childBound := by
      simp only [K, mem_range] at h1 <;> omega
    exact Nat.pow_le_of_le_log hcb.ne' h2

  have hA'_nonempty : A'.Nonempty := by
    by_contra h
    have h' : A'.card = 0 := by
      simpa [Finset.not_nonempty_iff_eq_empty] using h
    have h9 : M * selectedChildren.card = 0 := hA'_card2.symm.trans h'
    by_cases hM0 : M = 0
    · have h10 : occupiedChildren = ∅ := by
        by_contra h11
        have h12 : occupiedChildren.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr h11
        rcases h12 with ⟨child, hchild⟩
        have h13 : (A₁ ∩ child).Nonempty := (mem_filter.mp hchild).2
        have h14 : (A₁ ∩ child).card = M :=
          hM child (mem_filter.mp hchild).1 h13
        rw [hM0] at h14
        have h15 : 0 < (A₁ ∩ child).card :=
          Finset.Nonempty.card_pos h13
        rw [h14] at h15 <;> omega
      have h11 : A₁.card = 0 := by
        rw [h_A1_card, h10] <;> simp
      have h12 : A₁ = ∅ := by simpa using h11
      exact hA₁.ne_empty h12
    · have h10 : selectedChildren.card = 0 := by
        apply (mul_eq_zero.mp h9).resolve_left hM0
      have h12 : binMass k_opt = 0 := by
        have h13 : binMass k_opt ≤ 2 * A'.card := h_retention1
        rw [h'] at h13
        omega
      have h14 : ∀ b ∈ K, binMass b = 0 := by
        intro b hb
        have h15 : binMass b ≤ binMass k_opt := h_max b hb
        omega
      have h16 : ∑ b ∈ K, binMass b = 0 := by
        rw [Finset.sum_congr rfl h14] <;> simp
      rw [h_sum_binMass] at h16
      exact hA₁.card_pos.ne' h16

  have h_child_of_A'_elem :
      ∀ {x : α}, x ∈ A' →
        ∃ child : Finset α,
          child ∈ selectedChildren ∧ x ∈ A₁ ∩ child := by
    intro x hx
    rcases mem_biUnion.mp hx with ⟨child, hchild, hxc⟩
    exact ⟨child, hchild, hxc⟩

  have h_branching :
      ∀ parent ∈ P 0, (A' ∩ parent).Nonempty →
        (occupiedPartitionChildren A' P 0 parent).card = 2 ^ k_opt := by
    intro parent hparent hocc
    have h_parent_in_bin : parent ∈ binParents k_opt := by
      rcases hocc with ⟨x, hx⟩
      have h_x_in_A' : x ∈ A' := (hmem_inter hx).1
      have h_x_in_parent : x ∈ parent := (hmem_inter hx).2
      rcases h_child_of_A'_elem h_x_in_A' with
        ⟨child, hchild_sel, hxc⟩
      have h_x_in_child : x ∈ child := (hmem_inter hxc).2
      rcases h_sel_parent child hchild_sel with
        ⟨p, hp_bin, h_child_sub_p⟩
      have h_x_in_p : x ∈ p := h_child_sub_p h_x_in_child
      have h_p_in_P0 : p ∈ P 0 :=
        (mem_filter.mp (mem_filter.mp hp_bin).1).1
      have h_parent_eq_p : parent = p := by
        by_cases h : parent = p
        · exact h
        · have h6 : Disjoint parent p :=
            h0_disj parent hparent p h_p_in_P0 h
          have h7 : x ∈ parent ∩ p :=
            Finset.mem_inter.mpr ⟨h_x_in_parent, h_x_in_p⟩
          have h8 : x ∈ (∅ : Finset α) := h6.le_bot h7
          simp at h8
      rw [h_parent_eq_p]
      exact hp_bin

    have h_eq :
        occupiedPartitionChildren A' P 0 parent = S parent := by
      ext child
      simp only [occupiedPartitionChildren, mem_filter]
      constructor
      · rintro ⟨hchild_part, hchild_occ⟩
        have h_child_in_P1 : child ∈ P 1 :=
          (mem_filter.mp hchild_part).1
        have h_child_sub_parent : child ⊆ parent :=
          (mem_filter.mp hchild_part).2
        rcases hchild_occ with ⟨x, hx⟩
        have h_x_in_A' : x ∈ A' := (hmem_inter hx).1
        have h_x_in_child : x ∈ child := (hmem_inter hx).2
        rcases h_child_of_A'_elem h_x_in_A' with
          ⟨child', hchild'_sel, hxc'⟩
        have h_x_in_child' : x ∈ child' := (hmem_inter hxc').2
        have h_child'_in_P1 : child' ∈ P 1 :=
          h_sel_in_P1 child' hchild'_sel
        have h_child_eq_child' : child = child' := by
          by_cases h : child = child'
          · exact h
          · have h6 : Disjoint child child' :=
              h1_disj child h_child_in_P1 child' h_child'_in_P1 h
            have h7 : x ∈ child ∩ child' :=
              Finset.mem_inter.mpr ⟨h_x_in_child, h_x_in_child'⟩
            have h8 : x ∈ (∅ : Finset α) := h6.le_bot h7
            simp at h8
        have hchild_sel : child ∈ selectedChildren := by
          rw [h_child_eq_child'] <;> exact hchild'_sel
        rcases mem_biUnion.mp hchild_sel with ⟨p, hp_bin, hmem⟩
        have h_child_sub_p : child ⊆ p := by
          have h2 :
              child ∈ occupiedPartitionChildren A₁ P 0 p :=
            (hS p hp_bin).1 hmem
          exact (mem_filter.mp (mem_filter.mp h2).1).2
        have h_p_in_P0 : p ∈ P 0 :=
          (mem_filter.mp (mem_filter.mp hp_bin).1).1
        have h_parent_eq_p : parent = p := by
          by_cases h : parent = p
          · exact h
          · have h6 : Disjoint parent p :=
              h0_disj parent hparent p h_p_in_P0 h
            have h7 : x ∈ parent ∩ p :=
              Finset.mem_inter.mpr
                ⟨h_child_sub_parent h_x_in_child,
                  h_child_sub_p h_x_in_child⟩
            have h8 : x ∈ (∅ : Finset α) := h6.le_bot h7
            simp at h8
        have h_final : child ∈ S parent := by
          rw [h_parent_eq_p]
          exact hmem
        exact h_final
      · intro hmem
        have h1 :
            child ∈ occupiedPartitionChildren A₁ P 0 parent :=
          (hS parent h_parent_in_bin).1 hmem
        have h2 : child ∈ partitionChildren P 0 parent :=
          (mem_filter.mp h1).1
        have h3 : (A₁ ∩ child).Nonempty := (mem_filter.mp h1).2
        have h4 : A₁ ∩ child ⊆ A' := by
          intro y hy
          exact mem_biUnion.mpr
            ⟨child,
              mem_biUnion.mpr ⟨parent, h_parent_in_bin, hmem⟩,
              hy⟩
        have h5 : (A' ∩ child).Nonempty := by
          rcases h3 with ⟨y, hy⟩
          have h_y_in_A' : y ∈ A' := h4 hy
          have h_y_in_child : y ∈ child := (hmem_inter hy).2
          exact ⟨y, Finset.mem_inter.mpr ⟨h_y_in_A', h_y_in_child⟩⟩
        exact ⟨h2, h5⟩

    rw [h_eq]
    exact (hS parent h_parent_in_bin).2

  have h_preservation :
      ∀ cell ∈ P 1, (A' ∩ cell).Nonempty →
        A' ∩ cell = A₁ ∩ cell := by
    intro cell hcell hocc
    rcases hocc with ⟨x, hx⟩
    have h_x_in_A' : x ∈ A' := (hmem_inter hx).1
    have h_x_in_cell : x ∈ cell := (hmem_inter hx).2
    rcases h_child_of_A'_elem h_x_in_A' with
      ⟨child, hchild_sel, hxc⟩
    have h_x_in_child : x ∈ child := (hmem_inter hxc).2
    have h_child_in_P1 : child ∈ P 1 :=
      h_sel_in_P1 child hchild_sel
    have h_cell_eq_child : cell = child := by
      by_cases h : cell = child
      · exact h
      · have h6 : Disjoint cell child :=
          h1_disj cell hcell child h_child_in_P1 h
        have h7 : x ∈ cell ∩ child :=
          Finset.mem_inter.mpr ⟨h_x_in_cell, h_x_in_child⟩
        have h8 : x ∈ (∅ : Finset α) := h6.le_bot h7
        simp at h8
    rw [h_cell_eq_child]
    have h9 : child ∈ selectedChildren := hchild_sel
    have h10 : A₁ ∩ child ⊆ A' := by
      intro y hy
      exact mem_biUnion.mpr ⟨child, h9, hy⟩
    have h11 : A' ⊆ A₁ := hA'_sub
    ext y
    simp only [mem_inter]
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨h11 hy1, hy2⟩
    · intro hy
      exact ⟨h10 (Finset.mem_inter.mpr hy), hy.2⟩

  exact
    ⟨A', k_opt, hA'_nonempty, hA'_sub, h_retention_final,
      h_k_bound, h_branching, h_preservation⟩

end Kakeya.Assouad
