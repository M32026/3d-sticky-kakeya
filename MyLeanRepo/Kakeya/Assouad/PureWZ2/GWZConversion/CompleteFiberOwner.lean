import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.CompleteFiberOverlap

/-!
# Auxiliary owners from complete GWZ fibers

Choose one legal parent for each retained fine source index from the complete
fixed-dilation incidence relation.  This is an ordinary finite choice used
for later simultaneous regularization; it is not GWZ's assigned-parent API.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- One auxiliary owner map chosen from complete full-fiber incidence. -/
structure PureWZ2CompleteFiberOwnerData
    {delta A : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {constant : ENNReal}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    (scaleData :
      PureWZ2GWZScaleData (A := A) source scale constant)
    {retainedCard : ℕ}
    (sourceIndex : Fin retainedCard ↪ Fin source.card) where
  owner : Fin retainedCard → Fin scaleData.coarse.card
  owner_mem :
    ∀ index,
      sourceIndex index ∈
        scaleData.fullFiberIndices (owner index)
  complete_parent_degree :
    ∀ index,
      (Finset.univ.filter fun parent :
        Fin scaleData.coarse.card =>
          sourceIndex index ∈
            scaleData.fullFiberIndices parent).card ≤
        pureWZ2CompleteFiberOverlapBound A

/--
Choose auxiliary owners directly from the complete geometric fibers and
attach the complete-parent overlap bound.
-/
theorem pureWZ2_complete_fiber_owner
    {delta A : ℝ}
    (hdelta : 0 < delta)
    (hA : 1 ≤ A)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {constant : ENNReal}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    (scaleData :
      PureWZ2GWZScaleData (A := A) source scale constant)
    (hscaleSmall : scale.1 ≤ 1 / (200 * A))
    {retainedCard : ℕ}
    (sourceIndex : Fin retainedCard ↪ Fin source.card) :
    Nonempty
      (PureWZ2CompleteFiberOwnerData
        scaleData sourceIndex) := by
  let owner : Fin retainedCard →
      Fin scaleData.coarse.card := fun index =>
    Classical.choose
      (scaleData.full_fibers_cover (sourceIndex index))
  have owner_mem :
      ∀ index,
        sourceIndex index ∈
          scaleData.fullFiberIndices (owner index) := by
    intro index
    exact
      Classical.choose_spec
        (scaleData.full_fibers_cover (sourceIndex index))
  have hdegree :=
    pureWZ2_complete_fiber_parent_overlap
      hdelta hA scaleData hscaleSmall
  exact
    ⟨{
      owner := owner
      owner_mem := owner_mem
      complete_parent_degree := fun index =>
        hdegree (sourceIndex index)
    }⟩

end Kakeya.Assouad

end
