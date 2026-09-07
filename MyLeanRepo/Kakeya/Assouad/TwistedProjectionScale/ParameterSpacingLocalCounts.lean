import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CubicGridRefinedCells
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingSelectedCell

/-!
# Local occupied-cell counts below the selected spacing cell
-/

noncomputable section

namespace Kakeya.Assouad

lemma selectedCell_cellCount_eq_descendants
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (profile :
      ParameterSpacingProfileAssemblyData
        (epsilon := epsilon) clustered)
    (selectedCell :
      ParameterSpacingSelectedCellData profile)
    (fineLevel : ℕ)
    (hcoarse_fine :
      profile.selected.selectedLevel.val ≤ fineLevel) :
    cellCount profile.tree.base
        selectedCell.points fineLevel =
      ((occupiedPartitionCells
          profile.tree.refinedPoints
          profile.tree.partition fineLevel).filter
        fun child => child ⊆ selectedCell.cell).card := by
  rw [selectedCell.points_eq,
    profile.tree.partition_eq]
  exact cellCount_inter_parent_eq_descendants
    (profile.tree.base_ge_three.trans' (by omega))
    profile.tree.refined_subset
    hcoarse_fine
    (by simpa [profile.tree.partition_eq] using
      selectedCell.cell_mem)
    (by simpa [selectedCell.points_eq] using
      selectedCell.points_nonempty)

lemma selectedCell_uniform_count
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (profile :
      ParameterSpacingProfileAssemblyData
        (epsilon := epsilon) clustered)
    (selectedCell :
      ParameterSpacingSelectedCellData profile)
    (fineLevel : ℕ)
    (hcoarse_fine :
      profile.selected.selectedLevel.val ≤ fineLevel)
    (hfine_terminal :
      fineLevel ≤ profile.tree.levels) :
    ∃ descendantCount : ℕ,
      0 < descendantCount ∧
      cellCount profile.tree.base
          selectedCell.points fineLevel =
        descendantCount := by
  rcases os_branching_interval_cell_count
      (α := Point 3)
      clustered.points profile.tree.levels
      profile.tree.partition
      profile.tree.partition_tree
      profile.tree.terminal_atomic
      profile.tree.child_parent
      profile.tree.refinedPoints
      profile.tree.refined_nonempty
      profile.tree.refined_subset
      profile.tree.branchExponent
      profile.tree.exact_branching
      profile.selected.selectedLevel.val
      fineLevel hcoarse_fine hfine_terminal with
    ⟨descendantCount, hpositive, hcount⟩
  have hselected_occupied :
      selectedCell.cell ∈
        occupiedPartitionCells
          profile.tree.refinedPoints
          profile.tree.partition
          profile.selected.selectedLevel.val :=
    Finset.mem_filter.mpr
      ⟨selectedCell.cell_mem,
        by simpa [selectedCell.points_eq] using
          selectedCell.points_nonempty⟩
  refine ⟨descendantCount, hpositive, ?_⟩
  rw [selectedCell_cellCount_eq_descendants
    profile selectedCell fineLevel hcoarse_fine]
  exact hcount selectedCell.cell hselected_occupied

lemma selectedCell_uniform_cell_card
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (profile :
      ParameterSpacingProfileAssemblyData
        (epsilon := epsilon) clustered)
    (selectedCell :
      ParameterSpacingSelectedCellData profile)
    (level : ℕ)
    (hcoarse_level :
      profile.selected.selectedLevel.val ≤ level)
    (hlevel_terminal :
      level ≤ profile.tree.levels) :
    ∃ cellCard : ℕ,
      0 < cellCard ∧
      ∀ cell ∈ cubicGridPartition
          profile.tree.base level selectedCell.points,
        cell.card = cellCard := by
  rcases os_branching_cell_cardinality
      (α := Point 3)
      clustered.points profile.tree.levels
      profile.tree.partition
      profile.tree.partition_tree
      profile.tree.terminal_atomic
      profile.tree.child_parent
      profile.tree.refinedPoints
      profile.tree.refined_nonempty
      profile.tree.refined_subset
      profile.tree.branchExponent
      profile.tree.exact_branching
      level hlevel_terminal with
    ⟨cellCard, hcellCard_pos, hcellCard⟩
  refine ⟨cellCard, hcellCard_pos, ?_⟩
  intro localCell hlocalCell
  have hparent_grid :
      selectedCell.cell ∈
        cubicGridPartition profile.tree.base
          profile.selected.selectedLevel.val
          clustered.points := by
    simpa [profile.tree.partition_eq] using
      selectedCell.cell_mem
  have hparent_occupied :
      (profile.tree.refinedPoints ∩
        selectedCell.cell).Nonempty := by
    simpa [selectedCell.points_eq] using
      selectedCell.points_nonempty
  have hpartition_image :=
    cubicGridPartition_inter_parent_eq_image_descendants
      (profile.tree.base_ge_three.trans' (by omega))
      profile.tree.refined_subset
      hcoarse_level hparent_grid hparent_occupied
  rw [selectedCell.points_eq] at hlocalCell
  rw [hpartition_image] at hlocalCell
  rcases Finset.mem_image.mp hlocalCell with
    ⟨ambientCell, hambient, rfl⟩
  have hambient_occupied :=
    (Finset.mem_filter.mp hambient).1
  have hambient_mem :=
    (Finset.mem_filter.mp hambient_occupied).1
  have hambient_nonempty :=
    (Finset.mem_filter.mp hambient_occupied).2
  exact hcellCard ambientCell
    (by simpa [profile.tree.partition_eq] using hambient_mem)
    hambient_nonempty

lemma selectedCell_count_mul_cellCard
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (profile :
      ParameterSpacingProfileAssemblyData
        (epsilon := epsilon) clustered)
    (selectedCell :
      ParameterSpacingSelectedCellData profile)
    (level : ℕ)
    (hcoarse_level :
      profile.selected.selectedLevel.val ≤ level)
    (hlevel_terminal :
      level ≤ profile.tree.levels) :
    ∃ cellCard : ℕ,
      0 < cellCard ∧
      cellCount profile.tree.base
          selectedCell.points level *
          cellCard =
        selectedCell.points.card := by
  rcases selectedCell_uniform_cell_card
      profile selectedCell level
      hcoarse_level hlevel_terminal with
    ⟨cellCard, hpositive, hsame⟩
  refine ⟨cellCard, hpositive, ?_⟩
  rw [cellCount]
  have hsum :=
    cubicGridPartition_sum_card
      (base := profile.tree.base)
      (level := level)
      (A := selectedCell.points)
  rw [Finset.sum_congr rfl
    (fun cell hcell => hsame cell hcell),
    Finset.sum_const] at hsum
  simpa [mul_comm] using hsum

lemma global_cellCount_eq_coarse_mul_selected
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (profile :
      ParameterSpacingProfileAssemblyData
        (epsilon := epsilon) clustered)
    (selectedCell :
      ParameterSpacingSelectedCellData profile)
    (fineLevel : ℕ)
    (hcoarse_fine :
      profile.selected.selectedLevel.val ≤ fineLevel)
    (hfine_terminal :
      fineLevel ≤ profile.tree.levels) :
    cellCount profile.tree.base
        profile.tree.refinedPoints fineLevel =
      cellCount profile.tree.base
          profile.tree.refinedPoints
          profile.selected.selectedLevel.val *
        cellCount profile.tree.base
          selectedCell.points fineLevel := by
  rcases selectedCell_uniform_count
      profile selectedCell fineLevel
      hcoarse_fine hfine_terminal with
    ⟨descendantCount, hpositive, hselected_count⟩
  rcases os_branching_interval_cell_count
      (α := Point 3)
      clustered.points profile.tree.levels
      profile.tree.partition
      profile.tree.partition_tree
      profile.tree.terminal_atomic
      profile.tree.child_parent
      profile.tree.refinedPoints
      profile.tree.refined_nonempty
      profile.tree.refined_subset
      profile.tree.branchExponent
      profile.tree.exact_branching
      profile.selected.selectedLevel.val
      fineLevel hcoarse_fine hfine_terminal with
    ⟨globalDescendantCount, _hglobal_positive,
      hglobal_count⟩
  have hselected_occupied :
      selectedCell.cell ∈
        occupiedPartitionCells
          profile.tree.refinedPoints
          profile.tree.partition
          profile.selected.selectedLevel.val :=
    Finset.mem_filter.mpr
      ⟨selectedCell.cell_mem,
        by simpa [selectedCell.points_eq] using
          selectedCell.points_nonempty⟩
  have hdesc_eq :
      globalDescendantCount = descendantCount := by
    have hglobal_selected :=
      hglobal_count selectedCell.cell
        hselected_occupied
    rw [← selectedCell_cellCount_eq_descendants
      profile selectedCell fineLevel hcoarse_fine,
      hselected_count] at hglobal_selected
    exact hglobal_selected.symm
  subst globalDescendantCount
  have hcoarse_card :
      (occupiedPartitionCells
          profile.tree.refinedPoints
          profile.tree.partition
          profile.selected.selectedLevel.val).card =
        cellCount profile.tree.base
          profile.tree.refinedPoints
          profile.selected.selectedLevel.val := by
    rw [profile.tree.partition_eq]
    symm
    exact cellCount_restrict_eq_occupied
      profile.tree.refined_subset
  have hfine_card :
      (occupiedPartitionCells
          profile.tree.refinedPoints
          profile.tree.partition fineLevel).card =
        cellCount profile.tree.base
          profile.tree.refinedPoints fineLevel := by
    rw [profile.tree.partition_eq]
    symm
    exact cellCount_restrict_eq_occupied
      profile.tree.refined_subset
  let coarseCells :=
    occupiedPartitionCells
      profile.tree.refinedPoints
      profile.tree.partition
      profile.selected.selectedLevel.val
  let fineCells :=
    occupiedPartitionCells
      profile.tree.refinedPoints
      profile.tree.partition fineLevel
  have hcover :
      fineCells =
        coarseCells.biUnion fun parent =>
          fineCells.filter fun child =>
            child ⊆ parent := by
    apply Finset.ext
    intro child
    simp only [fineCells, coarseCells,
      Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hchild
      have hchild_partition :=
        (Finset.mem_filter.mp hchild).1
      rcases os_branching_find_ancestor
          profile.tree.partition profile.tree.levels
          profile.tree.child_parent
          hcoarse_fine hfine_terminal
          child hchild_partition with
        ⟨parent, hparent, hsub⟩
      have hchild_nonempty :=
        (Finset.mem_filter.mp hchild).2
      have hparent_nonempty :
          (profile.tree.refinedPoints ∩ parent).Nonempty := by
        rcases hchild_nonempty with ⟨point, hp⟩
        exact ⟨point, Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hp).1,
            hsub (Finset.mem_inter.mp hp).2⟩⟩
      exact ⟨parent,
        Finset.mem_filter.mpr
          ⟨hparent, hparent_nonempty⟩,
        hchild, hsub⟩
    · rintro ⟨parent, _hparent, hchild, _hsub⟩
      exact hchild
  have hdisjoint :
      (coarseCells : Set (DiscreteSet 3)).PairwiseDisjoint
        (fun parent =>
          fineCells.filter fun child =>
            child ⊆ parent) := by
    intro first hfirst second hsecond hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro child hchild_first hchild_second
    have hsub_first :=
      (Finset.mem_filter.mp hchild_first).2
    have hsub_second :=
      (Finset.mem_filter.mp hchild_second).2
    have hchild_nonempty :
        child.Nonempty := by
      have hoccupied :=
        (Finset.mem_filter.mp hchild_first).1
      exact ((Finset.mem_filter.mp hoccupied).2).mono
        Finset.inter_subset_right
    rcases hchild_nonempty with ⟨point, hp⟩
    have hfirst_mem :=
      (Finset.mem_filter.mp hfirst).1
    have hsecond_mem :=
      (Finset.mem_filter.mp hsecond).1
    have hcell_disjoint :=
      (profile.tree.partition_tree
        profile.selected.selectedLevel.val
        profile.selected.selectedLevel.is_lt.le).2.1
        first hfirst_mem second hsecond_mem hne
    exact (Finset.disjoint_left.mp hcell_disjoint)
      (hsub_first hp) (hsub_second hp)
  have heach :
      ∀ parent ∈ coarseCells,
        (fineCells.filter fun child =>
          child ⊆ parent).card =
          descendantCount := by
    intro parent hparent
    exact hglobal_count parent hparent
  have hcard :
      fineCells.card =
        coarseCells.card * descendantCount := by
    rw [hcover, Finset.card_biUnion hdisjoint]
    rw [Finset.sum_congr rfl heach,
      Finset.sum_const]
    ring
  rw [← hfine_card, ← hcoarse_card,
    hselected_count]
  exact hcard

lemma selectedCell_local_growth
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (profile :
      ParameterSpacingProfileAssemblyData
        (epsilon := epsilon) clustered)
    (selectedCell :
      ParameterSpacingSelectedCellData profile)
    (fineLevel : Fin (profile.tree.levels + 1))
    (hcoarse_fine :
      profile.selected.selectedLevel.val ≤ fineLevel.val) :
    Real.rpow (profile.tree.base : ℝ)
          (((fineLevel.val -
              profile.selected.selectedLevel.val : ℕ) : ℝ) *
            parameterSpacingSuffixDimension epsilon) ≤
      (cellCount profile.tree.base
        selectedCell.points fineLevel.val : ℝ) := by
  have hglobal :=
    profile.selected.cellCount_growth
      fineLevel hcoarse_fine
  have hfactor :=
    global_cellCount_eq_coarse_mul_selected
      profile selectedCell fineLevel.val
      hcoarse_fine fineLevel.is_le
  rw [hfactor] at hglobal
  have hcoarse_pos :
      0 <
        (cellCount profile.tree.base
          profile.tree.refinedPoints
          profile.selected.selectedLevel.val : ℝ) := by
    exact_mod_cast
      (cubicGridPartition_nonempty
        profile.tree.refined_nonempty).card_pos
  have hglobal' :
      Real.rpow (profile.tree.base : ℝ)
            (((fineLevel.val -
                profile.selected.selectedLevel.val : ℕ) : ℝ) *
              parameterSpacingSuffixDimension epsilon) *
          (cellCount profile.tree.base
            profile.tree.refinedPoints
            profile.selected.selectedLevel.val : ℝ) ≤
        (cellCount profile.tree.base
          selectedCell.points fineLevel.val : ℝ) *
          (cellCount profile.tree.base
            profile.tree.refinedPoints
            profile.selected.selectedLevel.val : ℝ) := by
    simpa [Nat.cast_mul, mul_comm] using hglobal
  exact le_of_mul_le_mul_right hglobal' hcoarse_pos

end Kakeya.Assouad
