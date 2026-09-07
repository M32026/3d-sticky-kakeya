import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-!
# Canonical source subfamilies along one paper fiber-tree edge

Fix an exact `sigma` parent.  The source fine family is its complete full
fiber.  At a finer exact scale `rho`, the source middle family consists of
the distinct `rho` parents hit by those fine tubes.  This module supplies the
canonical indexed subfamilies and the surjective induced parent map.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- `rho` parents hit by one complete `sigma` source fiber. -/
def wz2PaperFiberTreeMiddleIndices
    {delta rho sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarseRho : Kakeya.Streamlined.TubeFamily rho}
    {coarseSigma : Kakeya.Streamlined.TubeFamily sigma}
    (coverRho : WZ2PaperPartitioningCover fine coarseRho)
    (coverSigma : WZ2PaperPartitioningCover fine coarseSigma)
    (anchor : Fin coarseSigma.card) :
    Finset (Fin coarseRho.card) :=
  (wz2PaperFullFiberIndices fine coarseSigma anchor).image
    coverRho.parent

/-- Canonical middle subfamily formed by those hit `rho` parents. -/
def wz2PaperFiberTreeMiddleSubfamily
    {delta rho sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarseRho : Kakeya.Streamlined.TubeFamily rho}
    {coarseSigma : Kakeya.Streamlined.TubeFamily sigma}
    (coverRho : WZ2PaperPartitioningCover fine coarseRho)
    (coverSigma : WZ2PaperPartitioningCover fine coarseSigma)
    (anchor : Fin coarseSigma.card) :
    Kakeya.Streamlined.TubeSubfamily coarseRho :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset coarseRho
    (wz2PaperFiberTreeMiddleIndices coverRho coverSigma anchor)

/-- Canonical fine subfamily: the full source fiber over the sigma anchor. -/
def wz2PaperFiberTreeFineSubfamily
    {delta rho sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarseRho : Kakeya.Streamlined.TubeFamily rho}
    {coarseSigma : Kakeya.Streamlined.TubeFamily sigma}
    (coverRho : WZ2PaperPartitioningCover fine coarseRho)
    (coverSigma : WZ2PaperPartitioningCover fine coarseSigma)
    (anchor : Fin coarseSigma.card) :
    Kakeya.Streamlined.TubeSubfamily fine :=
  coverSigma.fullFiberSubfamily anchor

/-- The middle index assigned to one fine source in the anchor fiber. -/
def wz2PaperFiberTreeMiddleParent
    {delta rho sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarseRho : Kakeya.Streamlined.TubeFamily rho}
    {coarseSigma : Kakeya.Streamlined.TubeFamily sigma}
    (coverRho : WZ2PaperPartitioningCover fine coarseRho)
    (coverSigma : WZ2PaperPartitioningCover fine coarseSigma)
    (anchor : Fin coarseSigma.card) :
    Fin (wz2PaperFiberTreeFineSubfamily
        coverRho coverSigma anchor).family.card →
      Fin (wz2PaperFiberTreeMiddleSubfamily
        coverRho coverSigma anchor).family.card := fun source =>
  let ambientSource :=
    (wz2PaperFiberTreeFineSubfamily
      coverRho coverSigma anchor).embedding source
  let ambientParent := coverRho.parent ambientSource
  let hmem :
      ambientParent ∈
        wz2PaperFiberTreeMiddleIndices coverRho coverSigma anchor := by
    apply Finset.mem_image.mpr
    exact
      ⟨ambientSource,
        coverSigma.fullFiberSubfamily_mem anchor source,
        rfl⟩
  let indices :=
    wz2PaperFiberTreeMiddleIndices coverRho coverSigma anchor
  let equivalence : Fin indices.card ≃ indices :=
    Finset.orderIsoOfFin indices rfl
  equivalence.symm ⟨ambientParent, hmem⟩

@[simp] theorem wz2PaperFiberTreeMiddleParent_ambient
    {delta rho sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarseRho : Kakeya.Streamlined.TubeFamily rho}
    {coarseSigma : Kakeya.Streamlined.TubeFamily sigma}
    (coverRho : WZ2PaperPartitioningCover fine coarseRho)
    (coverSigma : WZ2PaperPartitioningCover fine coarseSigma)
    (anchor : Fin coarseSigma.card)
    (source : Fin (wz2PaperFiberTreeFineSubfamily
      coverRho coverSigma anchor).family.card) :
    (wz2PaperFiberTreeMiddleSubfamily
        coverRho coverSigma anchor).embedding
        (wz2PaperFiberTreeMiddleParent
          coverRho coverSigma anchor source) =
      coverRho.parent
        ((wz2PaperFiberTreeFineSubfamily
          coverRho coverSigma anchor).embedding source) := by
  let indices :=
    wz2PaperFiberTreeMiddleIndices coverRho coverSigma anchor
  let equivalence : Fin indices.card ≃ indices :=
    Finset.orderIsoOfFin indices rfl
  change
    ((Kakeya.Streamlined.TubeSubfamily.fromFinset
      coarseRho indices).embedding
      (wz2PaperFiberTreeMiddleParent
        coverRho coverSigma anchor source)) =
      coverRho.parent
        ((wz2PaperFiberTreeFineSubfamily
          coverRho coverSigma anchor).embedding source)
  change
    (equivalence
      (equivalence.symm
        ⟨coverRho.parent
            ((wz2PaperFiberTreeFineSubfamily
              coverRho coverSigma anchor).embedding source),
          _⟩)).1 =
      coverRho.parent
        ((wz2PaperFiberTreeFineSubfamily
          coverRho coverSigma anchor).embedding source)
  exact congrArg Subtype.val
    (equivalence.apply_symm_apply _)

theorem wz2PaperFiberTreeMiddleParent_surjective
    {delta rho sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarseRho : Kakeya.Streamlined.TubeFamily rho}
    {coarseSigma : Kakeya.Streamlined.TubeFamily sigma}
    (coverRho : WZ2PaperPartitioningCover fine coarseRho)
    (coverSigma : WZ2PaperPartitioningCover fine coarseSigma)
    (anchor : Fin coarseSigma.card) :
    Function.Surjective
      (wz2PaperFiberTreeMiddleParent
        coverRho coverSigma anchor) := by
  intro middle
  let indices :=
    wz2PaperFiberTreeMiddleIndices coverRho coverSigma anchor
  have hmiddle :
      (wz2PaperFiberTreeMiddleSubfamily
          coverRho coverSigma anchor).embedding middle ∈
        wz2PaperFiberTreeMiddleIndices coverRho coverSigma anchor :=
    Finset.orderEmbOfFin_mem indices rfl middle
  rcases Finset.mem_image.mp hmiddle with
    ⟨ambientSource, hsourceFiber, hparent⟩
  let fiberIndices :=
    wz2PaperFullFiberIndices fine coarseSigma anchor
  let fiberIso : Fin fiberIndices.card ≃o fiberIndices :=
    Finset.orderIsoOfFin fiberIndices rfl
  let rawSource : Fin fiberIndices.card :=
    fiberIso.symm ⟨ambientSource, hsourceFiber⟩
  let source :
      Fin (wz2PaperFiberTreeFineSubfamily
        coverRho coverSigma anchor).family.card :=
    ⟨rawSource.1, by
      simpa [fiberIndices, wz2PaperFiberTreeFineSubfamily,
        WZ2PaperPartitioningCover.fullFiberSubfamily,
        wz2PaperFullFiberSubfamily,
        Kakeya.Streamlined.TubeSubfamily.fromFinset] using
        rawSource.2⟩
  refine ⟨source, ?_⟩
  apply
    (wz2PaperFiberTreeMiddleSubfamily
      coverRho coverSigma anchor).embedding.injective
  rw [wz2PaperFiberTreeMiddleParent_ambient]
  have hsourceAmbient :
      (wz2PaperFiberTreeFineSubfamily
          coverRho coverSigma anchor).embedding source =
        ambientSource := by
    have hraw :
        ↑(fiberIso rawSource) = ambientSource :=
      congrArg Subtype.val
        (fiberIso.apply_symm_apply ⟨ambientSource, hsourceFiber⟩)
    have hsourceRaw : source.1 = rawSource.1 := rfl
    change
      Finset.orderEmbOfFin
          fiberIndices
          rfl source =
        ambientSource
    rw [← Finset.coe_orderIsoOfFin_apply]
    have hsourceCast : source = rawSource := by
      apply Fin.ext
      exact hsourceRaw
    rw [hsourceCast]
    exact hraw
  rw [hsourceAmbient, ← hparent]

end Kakeya.Assouad

end
