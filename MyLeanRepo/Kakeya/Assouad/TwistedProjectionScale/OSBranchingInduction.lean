import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OneLevelBranchingUniformization
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# OS branching uniform refinement — multiscale induction

Process a nested partition tree from finest to coarsest level. At each level,
apply the one-level branching uniformization lemma and propagate previously
obtained branching data to deeper levels via the preservation property.
-/

open Finset

namespace Kakeya.Assouad

variable {α : Type} [DecidableEq α]

/-- Every cell at level `j` has an ancestor at level `k ≤ j`. -/
lemma os_branching_find_ancestor
    (P : ℕ → Finset (Finset α))
    (levels : ℕ)
    (h_child_parent : ∀ l, l < levels →
      ∀ child ∈ P (l + 1), ∃ parent ∈ P l, child ⊆ parent)
    {k j : ℕ} (hkj : k ≤ j) (hjt : j ≤ levels) :
    ∀ cell ∈ P j, ∃ ancestor ∈ P k, cell ⊆ ancestor := by
  induction j with
  | zero =>
    have h_k0 : k = 0 := by omega
    subst h_k0
    intro cell hcell
    exact ⟨cell, hcell, rfl.subset⟩
  | succ j ih =>
    by_cases h : k ≤ j
    · intro cell hcell
      have h_j_lt : j < levels := by omega
      rcases h_child_parent j h_j_lt cell hcell with
        ⟨parent, hparent, hsub⟩
      rcases ih h (by omega) parent hparent with
        ⟨ancestor, hancestor, hsub'⟩
      exact ⟨ancestor, hancestor, hsub.trans hsub'⟩
    · have h_kj : k = j + 1 := by omega
      subst h_kj
      intro cell hcell
      exact ⟨cell, hcell, rfl.subset⟩

/-- Uniformize the `n` deepest levels of a locally bounded partition tree. -/
lemma os_branching_induction
    (A : Finset α) (hA : A.Nonempty)
    (levels childBound : ℕ) (hcb_pos : 0 < childBound)
    (P : ℕ → Finset (Finset α))
    (h_partition : ∀ level ≤ levels,
      (∀ cell ∈ P level, cell.Nonempty ∧ cell ⊆ A) ∧
      (∀ cell₁ ∈ P level, ∀ cell₂ ∈ P level,
        cell₁ ≠ cell₂ → Disjoint cell₁ cell₂) ∧
      A ⊆ Finset.biUnion (P level) id)
    (h_atomic : ∀ cell ∈ P levels, cell.card = 1)
    (h_child_parent : ∀ l, l < levels →
      ∀ child ∈ P (l + 1), ∃ parent ∈ P l, child ⊆ parent)
    (h_children_bound : ∀ l, l < levels →
      ∀ parent ∈ P l,
        (partitionChildren P l parent).card ≤ childBound)
    (n : ℕ) (hn : n ≤ levels) :
    ∃ (A' : Finset α) (branchExponent : ℕ → ℕ),
      A'.Nonempty ∧ A' ⊆ A ∧
      (A.card : ℝ) ≤
        (2 * (Nat.log 2 childBound + 1) : ℝ) ^ n *
          (A'.card : ℝ) ∧
      (∀ i, levels - n ≤ i → i < levels →
        2 ^ branchExponent i ≤ childBound) ∧
      (∀ i, levels - n ≤ i → i < levels →
        ∀ parent ∈ P i, (A' ∩ parent).Nonempty →
          (occupiedPartitionChildren A' P i parent).card =
            2 ^ branchExponent i) ∧
      (∃ M : ℕ, ∀ cell ∈ P (levels - n),
        (A' ∩ cell).Nonempty → (A' ∩ cell).card = M) := by
  induction n with
  | zero =>
    let branchExponent : ℕ → ℕ := fun _ => 0
    refine ⟨A, branchExponent, hA, rfl.subset, ?_, ?_, ?_, ?_⟩
    · simp [pow_zero] <;> norm_cast
    · intro i h1 h2
      exfalso
      omega
    · intro i h1 h2
      exfalso
      omega
    · refine ⟨1, fun cell hcell hne => ?_⟩
      have h1 : (A ∩ cell).card ≤ cell.card :=
        Finset.card_le_card (by simp)
      have h2 : cell.card = 1 := h_atomic cell hcell
      have h3 : 0 < (A ∩ cell).card := hne.card_pos
      rw [h2] at h1
      omega
  | succ n ih =>
    have h_n_le : n ≤ levels := by linarith
    rcases ih h_n_le with
      ⟨A₁, branchExponent₁, hA₁_nonempty, hA₁_sub, hA₁_ret,
        hA₁_branch_bound, hA₁_branch_unif, ⟨M₁, hM₁_eq⟩⟩

    set level : ℕ := levels - (n + 1) with hlevel_def
    have h_n_lt : n < levels := by linarith
    have h_level_lt : level < levels := by omega
    have h_level_add_one : level + 1 = levels - n := by omega

    let Q : ℕ → Finset (Finset α) := fun k => P (level + k)

    have hQ0_disj :
        ∀ c₁ ∈ Q 0, ∀ c₂ ∈ Q 0, c₁ ≠ c₂ → Disjoint c₁ c₂ :=
      (h_partition level (by omega)).2.1
    have hQ0_cover : A₁ ⊆ Finset.biUnion (Q 0) id :=
      hA₁_sub.trans (h_partition level (by omega)).2.2
    have hQ1_disj :
        ∀ c₁ ∈ Q 1, ∀ c₂ ∈ Q 1, c₁ ≠ c₂ → Disjoint c₁ c₂ :=
      (h_partition (level + 1) (by omega)).2.1
    have hQ1_cover : A₁ ⊆ Finset.biUnion (Q 1) id :=
      hA₁_sub.trans (h_partition (level + 1) (by omega)).2.2
    have hQ_refine :
        ∀ child ∈ Q 1, ∃ parent ∈ Q 0, child ⊆ parent :=
      h_child_parent level h_level_lt
    have hQ_childBound :
        ∀ parent ∈ Q 0,
          (partitionChildren Q 0 parent).card ≤ childBound :=
      h_children_bound level h_level_lt
    have hQM :
        ∀ cell ∈ Q 1,
          (A₁ ∩ cell).Nonempty → (A₁ ∩ cell).card = M₁ := by
      rw [show Q 1 = P (level + 1) from rfl]
      rw [h_level_add_one]
      exact hM₁_eq

    rcases one_level_branching_uniformization
        A₁ hA₁_nonempty Q childBound hcb_pos M₁
        hQ0_disj hQ0_cover hQ1_disj hQ1_cover
        hQ_refine hQ_childBound hQM with
      ⟨A', k, hA'_nonempty, hA'_sub_A₁, hA'_ret,
        h_k_bound, h_branch_level_Q, h_preservation_Q⟩

    let factor : ℝ := 2 * (Nat.log 2 childBound + 1)
    let branchExponent : ℕ → ℕ := fun i =>
      if i = level then k else branchExponent₁ i

    have hA'_sub_A : A' ⊆ A := hA'_sub_A₁.trans hA₁_sub

    have h_main_ret :
        (A.card : ℝ) ≤ factor ^ (n + 1) * (A'.card : ℝ) := by
      calc
        (A.card : ℝ) ≤ factor ^ n * (A₁.card : ℝ) := hA₁_ret
        _ ≤ factor ^ n * (factor * (A'.card : ℝ)) := by gcongr
        _ = factor ^ (n + 1) * (A'.card : ℝ) := by ring

    have h_branch_level :
        ∀ parent ∈ P level, (A' ∩ parent).Nonempty →
          (occupiedPartitionChildren A' P level parent).card =
            2 ^ k := by
      intro parent hparent hne
      have h1 :
          occupiedPartitionChildren A' Q 0 parent =
            occupiedPartitionChildren A' P level parent := by
        rfl
      have h2 := h_branch_level_Q parent hparent hne
      rw [h1] at h2
      exact h2

    have h_preservation :
        ∀ cell ∈ P (level + 1), (A' ∩ cell).Nonempty →
          A' ∩ cell = A₁ ∩ cell := by
      intro cell hcell hne
      exact h_preservation_Q cell hcell hne

    have h_preservation_propagates :
        ∀ j : ℕ, level + 1 ≤ j → j ≤ levels →
          ∀ cell : Finset α, cell ∈ P j →
            (A' ∩ cell).Nonempty → A' ∩ cell = A₁ ∩ cell := by
      intro j hj1 hj2 cell hcell hne
      have h_anc :
          ∃ ancestor ∈ P (level + 1), cell ⊆ ancestor :=
        os_branching_find_ancestor
          P levels h_child_parent (by linarith) hj2 cell hcell
      rcases h_anc with ⟨ancestor, hancestor, hsub⟩
      have hsub' : A' ∩ cell ⊆ A' ∩ ancestor := by
        intro x hx
        have h_x1 : x ∈ A' := (Finset.mem_inter.mp hx).1
        have h_x2 : x ∈ cell := (Finset.mem_inter.mp hx).2
        exact Finset.mem_inter.mpr ⟨h_x1, hsub h_x2⟩
      have h_anc_ne : (A' ∩ ancestor).Nonempty := hne.mono hsub'
      have h_eq : A' ∩ ancestor = A₁ ∩ ancestor :=
        h_preservation ancestor hancestor h_anc_ne
      have h1 : A' ∩ cell = (A' ∩ ancestor) ∩ cell := by
        ext x
        simp [hsub] <;> tauto
      rw [h1, h_eq]
      ext x
      simp [hsub] <;> tauto

    have h_branch_bound' :
        ∀ i, levels - (n + 1) ≤ i → i < levels →
          2 ^ branchExponent i ≤ childBound := by
      intro i hi1 hi2
      by_cases h : i = level
      · rw [h, show branchExponent level = k from by simp [branchExponent]]
        exact h_k_bound
      · have h_gt : level < i := by
          simp [hlevel_def] at *
          omega
        have h_i_ge : levels - n ≤ i := by omega
        have h_old :
            2 ^ branchExponent₁ i ≤ childBound :=
          hA₁_branch_bound i h_i_ge hi2
        have h_be : branchExponent i = branchExponent₁ i := by
          simp [branchExponent, h] <;> tauto
        rw [h_be]
        exact h_old

    have h_branch_deeper :
        ∀ i, level < i → i < levels →
          ∀ parent ∈ P i, (A' ∩ parent).Nonempty →
            (occupiedPartitionChildren A' P i parent).card =
              2 ^ branchExponent i := by
      intro i hi1 hi2 parent hparent hne
      have h_eq_parent : A' ∩ parent = A₁ ∩ parent :=
        h_preservation_propagates i hi1 (by omega) parent hparent hne
      have h_i_ge : levels - n ≤ i := by omega
      have h_children_eq :
          occupiedPartitionChildren A' P i parent =
            occupiedPartitionChildren A₁ P i parent := by
        ext child
        simp only [occupiedPartitionChildren, Finset.mem_filter]
        constructor
        · rintro ⟨h1, h2⟩
          have h_c_in_next : child ∈ P (i + 1) :=
            (Finset.mem_filter.mp h1).1
          have h3 : (A' ∩ child).Nonempty := h2
          have h4 : level + 1 ≤ i + 1 := by omega
          have h5 : i + 1 ≤ levels := by omega
          have h6 : A' ∩ child = A₁ ∩ child :=
            h_preservation_propagates
              (i + 1) h4 h5 child h_c_in_next h3
          exact ⟨h1, by rw [h6] at h3; exact h3⟩
        · rintro ⟨h1, h2⟩
          have h3 : (A₁ ∩ child).Nonempty := h2
          have h4 : child ⊆ parent := (Finset.mem_filter.mp h1).2
          have h_pint : parent ∩ child = child :=
            Finset.inter_eq_right.mpr h4
          have h5 : A' ∩ child = (A' ∩ parent) ∩ child := by
            calc
              A' ∩ child = A' ∩ (parent ∩ child) := by rw [h_pint]
              _ = (A' ∩ parent) ∩ child := by rw [Finset.inter_assoc]
          have h6 : (A₁ ∩ parent) ∩ child = A₁ ∩ child := by
            calc
              (A₁ ∩ parent) ∩ child =
                  A₁ ∩ (parent ∩ child) := by rw [Finset.inter_assoc]
              _ = A₁ ∩ child := by rw [h_pint]
          have h7 : A' ∩ child = A₁ ∩ child := by
            rw [h5, h_eq_parent, h6]
          exact ⟨h1, by rw [h7]; exact h3⟩
      have hne' : (A₁ ∩ parent).Nonempty := by
        rw [← h_eq_parent]
        exact hne
      have h_be : branchExponent i = branchExponent₁ i := by
        have h_ne_level : i ≠ level := by omega
        simp [branchExponent, h_ne_level] <;> tauto
      rw [h_children_eq, h_be]
      exact hA₁_branch_unif i h_i_ge hi2 parent hparent hne'

    have h_branch_all :
        ∀ i, levels - (n + 1) ≤ i → i < levels →
          ∀ parent ∈ P i, (A' ∩ parent).Nonempty →
            (occupiedPartitionChildren A' P i parent).card =
              2 ^ branchExponent i := by
      intro i hi1 hi2 parent hparent hne
      by_cases h : i = level
      · subst h
        have h_be : branchExponent level = k := by
          simp [branchExponent]
        rw [h_be]
        exact h_branch_level parent hparent hne
      · have h_gt : level < i := by
          simp [hlevel_def] at *
          omega
        exact h_branch_deeper i h_gt hi2 parent hparent hne

    have h_new_equal_card :
        ∃ M : ℕ, ∀ cell ∈ P level,
          (A' ∩ cell).Nonempty → (A' ∩ cell).card = M := by
      refine ⟨2 ^ k * M₁, fun parent hparent hne => ?_⟩
      let occChildren :=
        occupiedPartitionChildren A' P level parent
      have h_occ_card : occChildren.card = 2 ^ k :=
        h_branch_level parent hparent hne

      have h_disj_children :
          (occChildren : Set (Finset α)).PairwiseDisjoint
            (fun child => A' ∩ child) := by
        intro c1 hc1 c2 hc2 hne
        have h1 : c1 ∈ P (level + 1) :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp hc1).1).1
        have h2 : c2 ∈ P (level + 1) :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp hc2).1).1
        have h_disj_cells : Disjoint c1 c2 :=
          (h_partition (level + 1) (by omega)).2.1
            c1 h1 c2 h2 hne
        exact h_disj_cells.mono (by simp) (by simp)

      have h_union :
          A' ∩ parent =
            Finset.biUnion occChildren (fun child => A' ∩ child) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_biUnion,
          occupiedPartitionChildren, partitionChildren,
          Finset.mem_filter]
        constructor
        · rintro ⟨hx_A', hx_parent⟩
          have hcov : x ∈ Finset.biUnion (P (level + 1)) id :=
            hA'_sub_A₁.trans hQ1_cover hx_A'
          rcases Finset.mem_biUnion.mp hcov with
            ⟨child, hchild, hx_child⟩
          rcases hQ_refine child hchild with ⟨p', hp', hsub⟩
          have h_x_in_p' : x ∈ p' := hsub hx_child
          have h_p'_eq : p' = parent := by
            by_cases hneq : p' = parent
            · exact hneq
            · have h_disj : Disjoint p' parent :=
                hQ0_disj p' hp' parent hparent hneq
              have h_contra : x ∈ p' ∩ parent :=
                Finset.mem_inter.mpr ⟨h_x_in_p', hx_parent⟩
              have h_bot : x ∈ (∅ : Finset α) :=
                h_disj.le_bot h_contra
              simp at h_bot
          have hsub_parent : child ⊆ parent := h_p'_eq ▸ hsub
          have h_child_occ : (A' ∩ child).Nonempty :=
            ⟨x, Finset.mem_inter.mpr ⟨hx_A', hx_child⟩⟩
          have h_child_in_occ :
              child ∈
                occupiedPartitionChildren A' P level parent := by
            simp only [occupiedPartitionChildren,
              partitionChildren, Finset.mem_filter]
            exact ⟨⟨hchild, hsub_parent⟩, h_child_occ⟩
          exact
            ⟨child, h_child_in_occ, ⟨hx_A', hx_child⟩⟩
        · rintro ⟨child, hfilter, hx⟩
          have h_child_sub : child ⊆ parent :=
            (Finset.mem_filter.mp
              (Finset.mem_filter.mp hfilter).1).2
          exact ⟨hx.1, h_child_sub hx.2⟩

      have h_card :
          (A' ∩ parent).card =
            ∑ child ∈ occChildren, (A' ∩ child).card := by
        rw [h_union, Finset.card_biUnion h_disj_children]

      have h_each :
          ∀ child ∈ occChildren, (A' ∩ child).card = M₁ := by
        intro child hc
        have h_c_in_next : child ∈ P (level + 1) :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
        have h_ne : (A' ∩ child).Nonempty :=
          (Finset.mem_filter.mp hc).2
        have h_eq : A' ∩ child = A₁ ∩ child :=
          h_preservation child h_c_in_next h_ne
        rw [h_eq]
        have h_c_in_levels_n : child ∈ P (levels - n) := by
          rw [← h_level_add_one]
          exact h_c_in_next
        exact hM₁_eq child h_c_in_levels_n
          (by rw [← h_eq]; exact h_ne)

      have h_sum :
          ∑ child ∈ occChildren, (A' ∩ child).card =
            occChildren.card * M₁ := by
        rw [Finset.sum_congr rfl h_each]
        simp [Finset.sum_const] <;> ring

      rw [h_card, h_sum, h_occ_card] <;> ring

    exact
      ⟨A', branchExponent, hA'_nonempty, hA'_sub_A,
        h_main_ret, h_branch_bound', h_branch_all,
        h_new_equal_card⟩

end Kakeya.Assouad
