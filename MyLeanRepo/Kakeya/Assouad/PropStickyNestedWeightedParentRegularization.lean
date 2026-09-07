import MyLeanRepo.Kakeya.Assouad.PropStickyNestedWeightedParentRegularizationStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyNestedWeightedLowerRegularization
import MyLeanRepo.Kakeya.Assouad.PropStickyNestedParentPartitions

/-! # Weighted regularization for nested parent maps -/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem wz2_prop_sticky_nested_weighted_parent_regularization :
    WZ2PropStickyNestedWeightedParentRegularizationStatement := by
  intro indexType _ _ weight hfinite scaleCount Parent _ _ parent hnested
  let partition : ℕ → Finset (Finset indexType) :=
    fun level =>
      if hlevel : level < scaleCount then
        finiteParentPartition (parent ⟨level, hlevel⟩)
      else ∅
  have hpartition :
      ∀ level < scaleCount,
        (∀ cell ∈ partition level,
            cell ⊆ (Finset.univ : Finset indexType)) ∧
        (∀ first ∈ partition level,
          ∀ second ∈ partition level,
            first ≠ second → Disjoint first second) ∧
        (Finset.univ : Finset indexType) ⊆
          Finset.biUnion (partition level) id := by
    intro level hlevel
    have hpartitionEq :
        partition level =
          finiteParentPartition (parent ⟨level, hlevel⟩) := by
      simp [partition, hlevel]
    rw [hpartitionEq]
    exact
      ⟨finiteParentPartition_cells_subset _,
        finiteParentPartition_pairwiseDisjoint _,
        finiteParentPartition_covers _⟩
  have hrefine :
      ∀ level, level + 1 < scaleCount →
        ∀ child ∈ partition (level + 1),
          ∃ parentCell ∈ partition level,
            child ⊆ parentCell := by
    intro level hnext child hchild
    have hlevel : level < scaleCount :=
      Nat.lt_of_succ_lt hnext
    have hchildPartition :
        partition (level + 1) =
          finiteParentPartition
            (parent ⟨level + 1, hnext⟩) := by
      simp [partition, hnext]
    have hparentPartition :
        partition level =
          finiteParentPartition
            (parent ⟨level, hlevel⟩) := by
      simp [partition, hlevel]
    rw [hchildPartition] at hchild
    rcases Finset.mem_image.mp hchild with
      ⟨anchor, _, rfl⟩
    let parentCell : Finset indexType :=
      Finset.univ.filter fun index =>
        parent ⟨level, hlevel⟩ index =
          parent ⟨level, hlevel⟩ anchor
    have hparentCell :
        parentCell ∈
          finiteParentPartition
            (parent ⟨level, hlevel⟩) :=
      Finset.mem_image.mpr
        ⟨anchor, Finset.mem_univ anchor, rfl⟩
    have hsubset :
        (Finset.univ.filter fun index =>
            parent ⟨level + 1, hnext⟩ index =
              parent ⟨level + 1, hnext⟩ anchor) ⊆
          parentCell := by
      intro index hindex
      have hchildEq :
          parent ⟨level + 1, hnext⟩ index =
            parent ⟨level + 1, hnext⟩ anchor :=
        (Finset.mem_filter.mp hindex).2
      have hparentEq :
          parent ⟨level, hlevel⟩ index =
            parent ⟨level, hlevel⟩ anchor := by
        exact
          hnested level hnext index anchor hchildEq
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ index, hparentEq⟩
    rw [hparentPartition]
    exact ⟨parentCell, hparentCell, hsubset⟩
  rcases
      wz2_prop_sticky_nested_weighted_lower_regularization
        indexType Finset.univ weight scaleCount partition
        hpartition hrefine (by simpa using hfinite) with
    ⟨selected, _, hretained, hlower⟩
  refine
    ⟨{
      selected := selected
      retained_weight := by
        simpa using hretained
      parent_weight_floor := ?_
    }⟩
  intro coordinate value hnonempty
  let cell : Finset indexType :=
    Finset.univ.filter fun index =>
      parent coordinate index = value
  have hcell :
      cell ∈ finiteParentPartition
        (parent coordinate) := by
    rcases hnonempty with ⟨index, hindex⟩
    have hindexValue :
        parent coordinate index = value :=
      (Finset.mem_filter.mp hindex).2
    have hcellEq :
        cell =
          Finset.univ.filter fun other =>
            parent coordinate other =
              parent coordinate index := by
      ext other
      simp [cell, hindexValue]
    rw [hcellEq]
    exact
      Finset.mem_image.mpr
        ⟨index, Finset.mem_univ index, rfl⟩
  have hcoordinatePartition :
      partition coordinate.val =
        finiteParentPartition (parent coordinate) := by
    have hcoordinate : coordinate.val < scaleCount :=
      coordinate.isLt
    simp [partition, hcoordinate]
  have hlowerCell :=
    hlower coordinate.val coordinate.isLt cell
  rw [hcoordinatePartition] at hlowerCell
  have hselectedCell :
      selected ∩ cell =
        selected.filter fun index =>
          parent coordinate index = value := by
    ext index
    simp [cell, and_left_comm, and_assoc]
  have hcellNonempty :
      (selected ∩ cell).Nonempty := by
    rwa [hselectedCell]
  have hbound := hlowerCell hcell hcellNonempty
  rw [hselectedCell] at hbound
  have hcard :
      (finiteParentPartition (parent coordinate)).card ≤
        Fintype.card (Parent coordinate) := by
    let allParentFibers :
        Finset (Finset indexType) :=
      Finset.univ.image fun value : Parent coordinate =>
        Finset.univ.filter fun index =>
          parent coordinate index = value
    have hsubset :
        finiteParentPartition (parent coordinate) ⊆
          allParentFibers := by
      intro fiber hfiber
      rcases Finset.mem_image.mp hfiber with
        ⟨anchor, _, rfl⟩
      exact
        Finset.mem_image.mpr
          ⟨parent coordinate anchor,
            Finset.mem_univ _, rfl⟩
    calc
      (finiteParentPartition (parent coordinate)).card ≤
          allParentFibers.card :=
        Finset.card_le_card hsubset
      _ ≤ (Finset.univ :
          Finset (Parent coordinate)).card :=
        Finset.card_image_le
      _ = Fintype.card (Parent coordinate) := by
        simp
  exact hbound.trans (by
    gcongr)

end Kakeya.Assouad

end
