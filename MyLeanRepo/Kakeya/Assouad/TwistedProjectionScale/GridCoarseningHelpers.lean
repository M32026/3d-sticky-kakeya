import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridPartitionTree
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingIntervalCellCountStatement

/-!
# Grid index coarsening and unique cell containment helpers

Two families of lemmas for the delta-grid partition tree:

1. **Index coarsening**: equality of `tubeParameterGridIndex` at a finer level
   implies equality at any coarser level. Generalizes the one-step
   `floor_child_div_base_eq_floor_parent4`.
2. **Unique parent**: in a nested disjoint partition tree, every cell at level
   `L` is contained in a unique cell at any level `l ≤ L`. Also works for
   `occupiedPartitionCells`.

These are used by the four-block package and other grid-OS transitions.
-/

noncomputable section

namespace Kakeya.Assouad

-- =====================================================================
-- Grid index coarsening
-- =====================================================================

/-- One-step coarsening of grid indices. -/
lemma tubeParameterGridIndex_coarsen_one
    {base level : ℕ} (hbase : 1 ≤ base) {p q : Point 4}
    (h : tubeParameterGridIndex base (level + 1) p =
         tubeParameterGridIndex base (level + 1) q) :
    tubeParameterGridIndex base level p =
      tubeParameterGridIndex base level q := by
  funext i
  have h1 : ⌊p i * (base ^ (level + 1) : ℝ)⌋ =
           ⌊q i * (base ^ (level + 1) : ℝ)⌋ :=
    congrFun h i
  have h2 : ⌊p i * (base ^ (level + 1) : ℝ)⌋ / (base : ℤ) =
           ⌊p i * (base ^ level : ℝ)⌋ :=
    floor_child_div_base_eq_floor_parent4 hbase (p i)
  have h3 : ⌊q i * (base ^ (level + 1) : ℝ)⌋ / (base : ℤ) =
           ⌊q i * (base ^ level : ℝ)⌋ :=
    floor_child_div_base_eq_floor_parent4 hbase (q i)
  simp only [tubeParameterGridIndex]
  rw [← h2, ← h3, h1]

/--
Coarsening: if two points have the same grid index at level `L`,
they have the same index at every level `l ≤ L`.
-/
lemma tubeParameterGridIndex_coarsening
    {base L l : ℕ} (hbase : 1 ≤ base) {p q : Point 4}
    (h : tubeParameterGridIndex base L p =
         tubeParameterGridIndex base L q)
    (hle : l ≤ L) :
    tubeParameterGridIndex base l p =
      tubeParameterGridIndex base l q := by
  induction L with
  | zero =>
    have h_l0 : l = 0 := by omega
    rw [h_l0]
    exact h
  | succ L ih =>
    by_cases h_l : l = L + 1
    · rw [h_l]
      exact h
    · have h_l_le : l ≤ L := by omega
      have h' := tubeParameterGridIndex_coarsen_one hbase h
      exact ih h' h_l_le

/--
A grid cell at level `L` is contained in the grid cell of any representative
point at a coarser level `l ≤ L`.
-/
lemma tubeParameterGridCell_nesting_multi
    {base L l : ℕ} (hbase : 1 ≤ base)
    {A : DiscreteSet 4} {p : Point 4} (hle : l ≤ L) :
    tubeParameterGridCell base L A p ⊆
      tubeParameterGridCell base l A p := by
  intro q hq
  have hqA : q ∈ A := (Finset.mem_filter.mp hq).1
  have h_idx : tubeParameterGridIndex base L q =
               tubeParameterGridIndex base L p :=
    (Finset.mem_filter.mp hq).2
  have h_coarse : tubeParameterGridIndex base l q =
                  tubeParameterGridIndex base l p :=
    tubeParameterGridIndex_coarsening hbase h_idx hle
  exact Finset.mem_filter.mpr ⟨hqA, h_coarse⟩

-- =====================================================================
-- Unique parent cell in a nested partition tree
-- =====================================================================

/--
Existence of a parent at level `l` for a cell at level `L ≥ l`,
given one-step nesting and the level bound.
-/
lemma partition_nesting_multi
    {α : Type} [DecidableEq α]
    {P : ℕ → Finset (Finset α)}
    {levels : ℕ}
    (hnesting : ∀ level, level < levels →
      ∀ child ∈ P (level + 1), ∃ parent ∈ P level, child ⊆ parent)
    (l : ℕ) :
    ∀ (L : ℕ), l ≤ L → L ≤ levels →
      ∀ {child : Finset α}, child ∈ P L →
        ∃ parent ∈ P l, child ⊆ parent := by
  intro L
  induction L with
  | zero =>
    intro hle hL child hchild
    have h_l0 : l = 0 := by omega
    subst h_l0
    exact ⟨child, hchild, by simp⟩
  | succ L ih =>
    intro hle hL child hchild
    by_cases h_l : l = L + 1
    · subst h_l
      exact ⟨child, hchild, by simp⟩
    · have h_l_le : l ≤ L := by omega
      have hL' : L < levels := by omega
      rcases hnesting L hL' child hchild with ⟨parent, hparent, hsub⟩
      rcases ih h_l_le (by omega) hparent with ⟨grandparent, hgp, hgsub⟩
      exact ⟨grandparent, hgp, Finset.Subset.trans hsub hgsub⟩

/--
Uniqueness of the parent: two distinct cells at the same level are disjoint,
so a nonempty child cannot be contained in both.
-/
lemma partition_unique_parent
    {α : Type} [DecidableEq α]
    {A : Finset α}
    {P : ℕ → Finset (Finset α)}
    {levels : ℕ}
    (hpartition : ∀ level ≤ levels,
      (∀ cell ∈ P level, cell.Nonempty ∧ cell ⊆ A) ∧
      (∀ cell₁ ∈ P level, ∀ cell₂ ∈ P level,
        cell₁ ≠ cell₂ → Disjoint cell₁ cell₂) ∧
      A ⊆ Finset.biUnion (P level) id)
    (hnesting : ∀ level, level < levels →
      ∀ child ∈ P (level + 1), ∃ parent ∈ P level, child ⊆ parent)
    {L l : ℕ} (hle : l ≤ L) (hL : L ≤ levels)
    {child : Finset α} (hchild : child ∈ P L) :
    ∃! parent : Finset α, parent ∈ P l ∧ child ⊆ parent := by
  have hchild_nonempty : child.Nonempty :=
    (hpartition L hL).1 child hchild |>.1
  have hexists : ∃ parent ∈ P l, child ⊆ parent :=
    partition_nesting_multi hnesting l L hle hL hchild
  rcases hexists with ⟨parent, hparent, hsub⟩
  refine ⟨parent, ⟨hparent, hsub⟩, fun other hother => ?_⟩
  have hother_p : other ∈ P l := hother.1
  have hother_sub : child ⊆ other := hother.2
  by_cases hne : other = parent
  · exact hne
  · have hdisj : Disjoint parent other :=
      (hpartition l (by omega)).2.1 parent hparent other hother_p (by tauto)
    rcases hchild_nonempty with ⟨x, hx⟩
    have hxp : x ∈ parent := hsub hx
    have hxo : x ∈ other := hother_sub hx
    have h_empty : parent ∩ other = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hdisj
    have h_contra : x ∈ parent ∩ other :=
      Finset.mem_inter.mpr ⟨hxp, hxo⟩
    rw [h_empty] at h_contra
    simp at h_contra

/--
If a child cell is occupied by `A'`, its parent is also occupied.
-/
lemma occupied_parent_of_occupied_child
    {α : Type} [DecidableEq α]
    {A' child parent : Finset α}
    (hsub : child ⊆ parent)
    (h_occ : (A' ∩ child).Nonempty) :
    (A' ∩ parent).Nonempty :=
  h_occ.mono fun _ hx =>
    Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
      hsub (Finset.mem_inter.mp hx).2⟩

/--
For occupied cells: every occupied fine cell has a unique occupied coarse
parent, and the parent is the same as the unique partition parent.
-/
lemma occupiedPartitionCells_unique_parent
    {α : Type} [DecidableEq α]
    {A : Finset α}
    {A' : Finset α}
    {P : ℕ → Finset (Finset α)}
    {levels : ℕ}
    (hpartition : ∀ level ≤ levels,
      (∀ cell ∈ P level, cell.Nonempty ∧ cell ⊆ A) ∧
      (∀ cell₁ ∈ P level, ∀ cell₂ ∈ P level,
        cell₁ ≠ cell₂ → Disjoint cell₁ cell₂) ∧
      A ⊆ Finset.biUnion (P level) id)
    (hnesting : ∀ level, level < levels →
      ∀ child ∈ P (level + 1), ∃ parent ∈ P level, child ⊆ parent)
    {L l : ℕ} (hle : l ≤ L) (hL : L ≤ levels)
    {child : Finset α}
    (hchild : child ∈ occupiedPartitionCells A' P L) :
    ∃! parent : Finset α,
      parent ∈ occupiedPartitionCells A' P l ∧ child ⊆ parent := by
  have hchild_p : child ∈ P L :=
    (Finset.mem_filter.mp hchild).1
  have hchild_occ : (A' ∩ child).Nonempty :=
    (Finset.mem_filter.mp hchild).2
  rcases partition_unique_parent hpartition hnesting hle hL hchild_p
    with ⟨parent, ⟨hparent, hsub⟩, huniq⟩
  have hparent_occ : (A' ∩ parent).Nonempty :=
    occupied_parent_of_occupied_child hsub hchild_occ
  have hparent_occ_cell : parent ∈ occupiedPartitionCells A' P l :=
    Finset.mem_filter.mpr ⟨hparent, hparent_occ⟩
  refine ⟨parent, ⟨hparent_occ_cell, hsub⟩, fun other hother => ?_⟩
  have hother_p : other ∈ P l := (Finset.mem_filter.mp hother.1).1
  exact huniq other ⟨hother_p, hother.2⟩

end Kakeya.Assouad
