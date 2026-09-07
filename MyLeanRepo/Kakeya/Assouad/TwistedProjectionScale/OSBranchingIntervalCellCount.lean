import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingInduction
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingIntervalCellCountStatement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace Kakeya.Assouad

theorem os_branching_interval_cell_count :
    OSBranchingIntervalCellCountStatement := by
  intro α _ A levels partition h_partition h_atomic h_child_parent
    A' hA'_nonempty hA'_sub branchExponent h_branching
  have h_main :
      ∀ difference : ℕ, ∀ coarseLevel fineLevel : ℕ,
        fineLevel - coarseLevel = difference →
        coarseLevel ≤ fineLevel →
        fineLevel ≤ levels →
        ∃ descendantCount : ℕ,
          0 < descendantCount ∧
            ∀ parent ∈
                occupiedPartitionCells A' partition coarseLevel,
              ((occupiedPartitionCells A' partition fineLevel).filter
                fun child => child ⊆ parent).card =
                  descendantCount := by
    intro difference
    induction difference with
    | zero =>
      intro coarseLevel fineLevel _ h_le h_fine_le
      have h_level_eq : fineLevel = coarseLevel := by
        omega
      refine ⟨1, by norm_num, fun parent hparent => ?_⟩
      have h_parent_partition : parent ∈ partition coarseLevel :=
        (Finset.mem_filter.mp hparent).1
      have h_parent_occupied : (A' ∩ parent).Nonempty :=
        (Finset.mem_filter.mp hparent).2
      have h_set :
          ((occupiedPartitionCells A' partition fineLevel).filter
            fun child => child ⊆ parent) = {parent} := by
        apply Finset.ext
        intro child
        rw [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hchild, hchild_subset⟩
          have h_child_partition : child ∈ partition fineLevel :=
            (Finset.mem_filter.mp hchild).1
          have h_child_occupied : (A' ∩ child).Nonempty :=
            (Finset.mem_filter.mp hchild).2
          have h_child_partition' : child ∈ partition coarseLevel := by
            rwa [h_level_eq] at h_child_partition
          have h_child_nonempty : child.Nonempty :=
            h_child_occupied.mono Finset.inter_subset_right
          by_cases h_eq : child = parent
          · exact h_eq
          · have h_disjoint : Disjoint child parent :=
              (h_partition coarseLevel (by omega)).2.1
                child h_child_partition' parent h_parent_partition h_eq
            have h_inter_empty : child ∩ parent = ∅ :=
              Finset.disjoint_iff_inter_eq_empty.mp h_disjoint
            have h_inter_self : child ∩ parent = child :=
              Finset.inter_eq_left.mpr hchild_subset
            exact False.elim
              (h_child_nonempty.ne_empty
                (h_inter_self.symm.trans h_inter_empty))
        · intro h_eq
          rw [h_eq]
          have h_parent_fine : parent ∈ partition fineLevel := by
            rwa [h_level_eq]
          exact
            ⟨Finset.mem_filter.mpr
                ⟨h_parent_fine, h_parent_occupied⟩,
              rfl.subset⟩
      rw [h_set]
      simp
    | succ difference ih =>
      intro coarseLevel fineLevel h_difference h_le h_fine_le
      have h_coarse_lt : coarseLevel < fineLevel := by
        omega
      let middleLevel : ℕ := coarseLevel + 1
      have h_middle_le : middleLevel ≤ fineLevel := by
        omega
      have h_difference' : fineLevel - middleLevel = difference := by
        omega
      rcases ih middleLevel fineLevel h_difference'
          h_middle_le h_fine_le with
        ⟨descendantCount, h_descendant_pos, h_descendant_eq⟩
      have h_coarse_lt_levels : coarseLevel < levels := by
        omega
      let levelIndex : Fin levels :=
        ⟨coarseLevel, h_coarse_lt_levels⟩
      let branchCount : ℕ := 2 ^ branchExponent levelIndex
      refine
        ⟨branchCount * descendantCount, by positivity,
          fun parent hparent => ?_⟩
      let occupiedChildren :=
        occupiedPartitionChildren A' partition coarseLevel parent
      have h_parent_partition : parent ∈ partition coarseLevel :=
        (Finset.mem_filter.mp hparent).1
      have h_parent_occupied : (A' ∩ parent).Nonempty :=
        (Finset.mem_filter.mp hparent).2
      have h_occupied_card :
          occupiedChildren.card = branchCount :=
        h_branching levelIndex parent h_parent_partition h_parent_occupied
      have h_extract :
          ∀ child ∈ occupiedChildren,
            child ∈ partition middleLevel ∧
              child ⊆ parent ∧
              (A' ∩ child).Nonempty := by
        intro child hchild
        have h1 :=
          Finset.mem_filter.mp hchild
        have h2 :=
          Finset.mem_filter.mp h1.1
        exact ⟨h2.1, h2.2, h1.2⟩
      have h_decomposition :
          ((occupiedPartitionCells A' partition fineLevel).filter
              fun fineCell => fineCell ⊆ parent) =
            Finset.biUnion occupiedChildren fun child =>
              (occupiedPartitionCells A' partition fineLevel).filter
                fun fineCell => fineCell ⊆ child := by
        apply Finset.ext
        intro fineCell
        rw [Finset.mem_filter, Finset.mem_biUnion]
        constructor
        · rintro ⟨h_fine, h_fine_parent⟩
          have h_fine_partition : fineCell ∈ partition fineLevel :=
            (Finset.mem_filter.mp h_fine).1
          have h_fine_occupied : (A' ∩ fineCell).Nonempty :=
            (Finset.mem_filter.mp h_fine).2
          rcases os_branching_find_ancestor partition levels
              h_child_parent (by omega) h_fine_le
              fineCell h_fine_partition with
            ⟨child, h_child_partition, h_fine_child⟩
          rcases h_child_parent coarseLevel h_coarse_lt_levels
              child h_child_partition with
            ⟨otherParent, h_other_partition, h_child_other⟩
          have h_child_occupied : (A' ∩ child).Nonempty := by
            exact h_fine_occupied.mono fun point hpoint =>
              Finset.mem_inter.mpr
                ⟨(Finset.mem_inter.mp hpoint).1,
                  h_fine_child (Finset.mem_inter.mp hpoint).2⟩
          rcases h_fine_occupied with ⟨point, hpoint⟩
          have hpoint_fine := (Finset.mem_inter.mp hpoint).2
          have hpoint_other :
              point ∈ otherParent :=
            h_child_other (h_fine_child hpoint_fine)
          have hpoint_parent : point ∈ parent :=
            h_fine_parent hpoint_fine
          have h_parent_eq : otherParent = parent := by
            by_cases h_eq : otherParent = parent
            · exact h_eq
            · have h_disjoint : Disjoint otherParent parent :=
                (h_partition coarseLevel (by omega)).2.1
                  otherParent h_other_partition
                  parent h_parent_partition h_eq
              have h_contra : point ∈ otherParent ∩ parent :=
                Finset.mem_inter.mpr
                  ⟨hpoint_other, hpoint_parent⟩
              exact False.elim (by
                have : point ∈ (∅ : Finset α) :=
                  h_disjoint.le_bot h_contra
                simpa using this)
          have h_child_parent : child ⊆ parent := by
            rwa [h_parent_eq] at h_child_other
          have h_child_occupied_membership :
              child ∈ occupiedChildren :=
            Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr
                  ⟨h_child_partition, h_child_parent⟩,
                h_child_occupied⟩
          exact
            ⟨child, h_child_occupied_membership,
              Finset.mem_filter.mpr ⟨h_fine, h_fine_child⟩⟩
        · rintro ⟨child, hchild, h_fine⟩
          exact
            ⟨(Finset.mem_filter.mp h_fine).1,
              (Finset.mem_filter.mp h_fine).2.trans
                (h_extract child hchild).2.1⟩
      have h_disjoint :
          (occupiedChildren : Set (Finset α)).PairwiseDisjoint
            (fun child =>
              (occupiedPartitionCells A' partition fineLevel).filter
                fun fineCell => fineCell ⊆ child) := by
        intro first hfirst second hsecond hne
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro fineCell h_fine_first h_fine_second
        have h_first_subset :=
          (Finset.mem_filter.mp h_fine_first).2
        have h_second_subset :=
          (Finset.mem_filter.mp h_fine_second).2
        have h_partition_disjoint : Disjoint first second :=
          (h_partition middleLevel (by omega)).2.1
            first (h_extract first hfirst).1
            second (h_extract second hsecond).1 hne
        have h_fine_occupied :=
          (Finset.mem_filter.mp
            (Finset.mem_filter.mp h_fine_first).1).2
        have h_fine_nonempty : fineCell.Nonempty :=
          h_fine_occupied.mono Finset.inter_subset_right
        have h_subset_inter : fineCell ⊆ first ∩ second :=
          Finset.subset_inter h_first_subset h_second_subset
        have h_inter_empty : first ∩ second = ∅ :=
          Finset.disjoint_iff_inter_eq_empty.mp
            h_partition_disjoint
        rw [h_inter_empty] at h_subset_inter
        exact h_fine_nonempty.ne_empty
          (Finset.subset_empty.mp h_subset_inter)
      have h_each :
          ∀ child ∈ occupiedChildren,
            ((occupiedPartitionCells A' partition fineLevel).filter
              fun fineCell => fineCell ⊆ child).card =
                descendantCount := by
        intro child hchild
        exact h_descendant_eq child
          (Finset.mem_filter.mpr
            ⟨(h_extract child hchild).1,
              (h_extract child hchild).2.2⟩)
      rw [h_decomposition, Finset.card_biUnion h_disjoint]
      have h_sum :
          ∑ child ∈ occupiedChildren,
              ((occupiedPartitionCells A' partition fineLevel).filter
                fun fineCell => fineCell ⊆ child).card =
            occupiedChildren.card * descendantCount := by
        rw [Finset.sum_congr rfl h_each]
        simp [Finset.sum_const]
      rw [h_sum, h_occupied_card]
  intro coarseLevel fineLevel h_coarse_le h_fine_le
  exact h_main (fineLevel - coarseLevel)
    coarseLevel fineLevel rfl h_coarse_le h_fine_le

end Kakeya.Assouad
