import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingCellCardinalityStatement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Cell cardinalities in an exact branching tree

Descending induction from atomic terminal cells shows that every occupied
cell at a fixed level contains the same number of retained leaves.
-/

namespace Kakeya.Assouad

theorem os_branching_cell_cardinality :
    OSBranchingCellCardinalityStatement := by
  intro α _ A levels P h_partition h_atomic h_child_parent
    A' hA'_nonempty hA'_sub branchExponent h_branching
  have h_main : ∀ (n : ℕ), n ≤ levels →
      ∃ (cellCard : ℕ), 0 < cellCard ∧
        ∀ cell ∈ P (levels - n), (A' ∩ cell).Nonempty →
          (A' ∩ cell).card = cellCard := by
    intro n
    induction n with
    | zero =>
      intro hn
      refine ⟨1, by norm_num, fun cell hcell hne => ?_⟩
      have h1 : (A' ∩ cell).card ≤ cell.card :=
        Finset.card_le_card (by simp)
      have h2 : cell.card = 1 := h_atomic cell hcell
      have h3 : 0 < (A' ∩ cell).card := hne.card_pos
      rw [h2] at h1
      omega
    | succ n ih =>
      intro hn
      by_cases h : n + 1 ≤ levels
      · have h_n_lt : n < levels := by omega
        set k : ℕ := levels - (n + 1) with hk_def
        have h_k_lt : k < levels := by omega
        have h_k_add_one : k + 1 = levels - n := by omega
        rcases ih (by omega) with ⟨M, hM_pos, hM_eq⟩
        let be : Fin levels := ⟨k, h_k_lt⟩
        let cellCard := 2 ^ branchExponent be * M
        have h_pos : 0 < cellCard := by positivity
        refine ⟨cellCard, h_pos, fun parent hparent hne => ?_⟩
        let occChildren := occupiedPartitionChildren A' P k parent
        have h_occ_card :
            occChildren.card = 2 ^ branchExponent be :=
          h_branching be parent hparent hne

        have h_disj_children :
            (occChildren : Set (Finset α)).PairwiseDisjoint
              (fun child => A' ∩ child) := by
          intro c1 hc1 c2 hc2 hne
          have h1 : c1 ∈ P (k + 1) :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp hc1).1).1
          have h2 : c2 ∈ P (k + 1) :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp hc2).1).1
          have h_disj_cells : Disjoint c1 c2 :=
            (h_partition (k + 1) (by omega)).2.1
              c1 h1 c2 h2 hne
          exact h_disj_cells.mono (by simp) (by simp)

        have h_union :
            A' ∩ parent =
              Finset.biUnion occChildren (fun child => A' ∩ child) := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_biUnion]
          constructor
          · rintro ⟨hx_A', hx_parent⟩
            have hcov : x ∈ Finset.biUnion (P (k + 1)) id :=
              hA'_sub.trans
                ((h_partition (k + 1) (by omega)).2.2) hx_A'
            rcases Finset.mem_biUnion.mp hcov with
              ⟨child, hchild, hx_child⟩
            rcases h_child_parent k h_k_lt child hchild with
              ⟨p', hp', hsub⟩
            have h_x_in_p' : x ∈ p' := hsub hx_child
            have h_p'_eq : p' = parent := by
              by_cases hneq : p' = parent
              · exact hneq
              · have h_disj : Disjoint p' parent :=
                  (h_partition k (by omega)).2.1
                    p' hp' parent hparent hneq
                have h_contra : x ∈ p' ∩ parent :=
                  Finset.mem_inter.mpr ⟨h_x_in_p', hx_parent⟩
                have h_bot : x ∈ (∅ : Finset α) :=
                  h_disj.le_bot h_contra
                simp at h_bot
            have hsub_parent : child ⊆ parent := h_p'_eq ▸ hsub
            have h_child_occ : (A' ∩ child).Nonempty :=
              ⟨x, Finset.mem_inter.mpr ⟨hx_A', hx_child⟩⟩
            have h_child_in_occ : child ∈ occChildren := by
              simp only [occChildren, occupiedPartitionChildren,
                partitionChildren, Finset.mem_filter]
              exact ⟨⟨hchild, hsub_parent⟩, h_child_occ⟩
            exact ⟨child, h_child_in_occ, hx_A', hx_child⟩
          · rintro ⟨child, hfilter, hx⟩
            have h_child_sub : child ⊆ parent := by
              simp only [occChildren, occupiedPartitionChildren,
                partitionChildren, Finset.mem_filter] at hfilter
              exact hfilter.1.2
            exact ⟨hx.1, h_child_sub hx.2⟩

        have h_each :
            ∀ child ∈ occChildren, (A' ∩ child).card = M := by
          intro child hc
          have h_c_in_next : child ∈ P (k + 1) :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
          have h_ne : (A' ∩ child).Nonempty :=
            (Finset.mem_filter.mp hc).2
          have h_c_in_level : child ∈ P (levels - n) := by
            rw [← h_k_add_one]
            exact h_c_in_next
          exact hM_eq child h_c_in_level h_ne

        have h_card :
            (A' ∩ parent).card =
              ∑ child ∈ occChildren, (A' ∩ child).card := by
          rw [h_union, Finset.card_biUnion h_disj_children]

        have h_sum :
            (∑ child ∈ occChildren, (A' ∩ child).card) =
              occChildren.card * M := by
          rw [Finset.sum_congr rfl h_each]
          simp [Finset.sum_const]

        rw [h_card, h_sum, h_occ_card]
      · have h_n_eq : n = levels := by omega
        have h_eq : levels - (n + 1) = levels - n := by omega
        rw [h_eq]
        exact ih (by omega)
  intro level hlevel
  have h_exists :
      ∃ (n : ℕ), n ≤ levels ∧ levels - n = level := by
    refine ⟨levels - level, by omega, ?_⟩
    omega
  rcases h_exists with ⟨n, hn, rfl⟩
  exact h_main n hn

end Kakeya.Assouad
