import MyLeanRepo.Kakeya.Assouad.PropStickyFullFiberHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickySelectedHitCover

/-! # Nested parent-map partitions on a selected fine family -/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The occupied fibers of a finite parent map. -/
def finiteParentPartition
    {source parentType : Type}
    [Fintype source] [DecidableEq source]
    [DecidableEq parentType]
    (parent : source → parentType) :
    Finset (Finset source) :=
  Finset.univ.image fun anchor =>
    Finset.univ.filter fun source => parent source = parent anchor

theorem finiteParentPartition_cells_subset
    {source parentType : Type}
    [Fintype source] [DecidableEq source]
    [DecidableEq parentType]
    (parent : source → parentType) :
    ∀ cell ∈ finiteParentPartition parent,
      cell ⊆ (Finset.univ : Finset source) := by
  intro cell _
  exact Finset.subset_univ cell

theorem finiteParentPartition_pairwiseDisjoint
    {source parentType : Type}
    [Fintype source] [DecidableEq source]
    [DecidableEq parentType]
    (parent : source → parentType) :
    ∀ first ∈ finiteParentPartition parent,
      ∀ second ∈ finiteParentPartition parent,
        first ≠ second → Disjoint first second := by
  intro first hfirst second hsecond hne
  rcases Finset.mem_image.mp hfirst with
    ⟨firstAnchor, _, rfl⟩
  rcases Finset.mem_image.mp hsecond with
    ⟨secondAnchor, _, hsecondEq⟩
  by_cases hparent :
      parent firstAnchor = parent secondAnchor
  · have hcellEq :
        (Finset.univ.filter fun source =>
            parent source = parent firstAnchor) =
          (Finset.univ.filter fun source =>
            parent source = parent secondAnchor) := by
      ext source
      simp [hparent]
    exact (hne (hcellEq.trans hsecondEq)).elim
  rw [← hsecondEq]
  simp only [Finset.disjoint_left]
  intro source hsourceFirst hsourceSecond
  have hfirst :
      parent source = parent firstAnchor :=
    (Finset.mem_filter.mp hsourceFirst).2
  have hsecond :
      parent source = parent secondAnchor :=
    (Finset.mem_filter.mp hsourceSecond).2
  exact hparent (hfirst.symm.trans hsecond)

theorem finiteParentPartition_covers
    {source parentType : Type}
    [Fintype source] [DecidableEq source]
    [DecidableEq parentType]
    (parent : source → parentType) :
    (Finset.univ : Finset source) ⊆
      Finset.biUnion (finiteParentPartition parent) id := by
  intro source _
  let cell :=
    Finset.univ.filter fun other =>
      parent other = parent source
  have hcell :
      cell ∈ finiteParentPartition parent :=
    Finset.mem_image.mpr
      ⟨source, Finset.mem_univ source, rfl⟩
  have hsource : source ∈ cell := by
    simp [cell]
  exact Finset.mem_biUnion.mpr
    ⟨cell, hcell, hsource⟩

theorem finiteParentPartition_nested
    {source fineParent coarseParent : Type}
    [Fintype source] [DecidableEq source]
    [DecidableEq fineParent] [DecidableEq coarseParent]
    (fine : source → fineParent)
    (coarse : source → coarseParent)
    (hnested :
      ∀ first second,
        fine first = fine second →
          coarse first = coarse second) :
    ∀ child ∈ finiteParentPartition fine,
      ∃ parent ∈ finiteParentPartition coarse,
        child ⊆ parent := by
  intro child hchild
  rcases Finset.mem_image.mp hchild with
    ⟨anchor, _, rfl⟩
  let parentCell :=
    Finset.univ.filter fun source =>
      coarse source = coarse anchor
  have hparentCell :
      parentCell ∈ finiteParentPartition coarse :=
    Finset.mem_image.mpr
      ⟨anchor, Finset.mem_univ anchor, rfl⟩
  refine ⟨parentCell, hparentCell, ?_⟩
  intro source hsource
  have hfine :
      fine source = fine anchor :=
    (Finset.mem_filter.mp hsource).2
  have hcoarse :
      coarse source = coarse anchor :=
    hnested source anchor hfine
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ source, hcoarse⟩

theorem WZ2PaperPartitioningCover.selected_parent_maps_nested
    {delta rho sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarseRho : Kakeya.Streamlined.TubeFamily rho}
    {coarseSigma : Kakeya.Streamlined.TubeFamily sigma}
    (coverRho : WZ2PaperPartitioningCover fine coarseRho)
    (coverSigma : WZ2PaperPartitioningCover fine coarseSigma)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (hscale : 2 * rho ≤ sigma) :
    ∀ first second : Fin selected.family.card,
      coverRho.parent (selected.embedding first) =
          coverRho.parent (selected.embedding second) →
        coverSigma.parent (selected.embedding first) =
          coverSigma.parent (selected.embedding second) := by
  intro first second hparent
  exact
    coverRho.fiber_parent_stable coverSigma hscale
      (coverRho.parent (selected.embedding first))
      rfl hparent.symm

theorem WZ2PaperPartitioningCover.restricted_parent_maps_nested
    {delta rho sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarseRho : Kakeya.Streamlined.TubeFamily rho}
    {coarseSigma : Kakeya.Streamlined.TubeFamily sigma}
    (coverRho : WZ2PaperPartitioningCover fine coarseRho)
    (coverSigma : WZ2PaperPartitioningCover fine coarseSigma)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (hnested :
      ∀ first second : Fin fine.card,
        coverRho.parent first = coverRho.parent second →
          coverSigma.parent first = coverSigma.parent second) :
    ∀ first second : Fin selected.family.card,
      (coverRho.restrictToHitParents selected).parent first =
          (coverRho.restrictToHitParents selected).parent second →
        (coverSigma.restrictToHitParents selected).parent first =
          (coverSigma.restrictToHitParents selected).parent second := by
  intro first second hparent
  change
    coverRho.hitParent selected first =
      coverRho.hitParent selected second at hparent
  change
    coverSigma.hitParent selected first =
      coverSigma.hitParent selected second
  apply
    (coverSigma.hitParentSubfamily selected).embedding.injective
  rw [coverSigma.hitParent_ambient, coverSigma.hitParent_ambient]
  apply hnested
  have hambient :=
    congrArg
      (coverRho.hitParentSubfamily selected).embedding hparent
  simpa only [
    WZ2PaperPartitioningCover.restrictToHitParents,
    WZ2PaperPartitioningCover.hitParent_ambient] using hambient

end Kakeya.Assouad

end
