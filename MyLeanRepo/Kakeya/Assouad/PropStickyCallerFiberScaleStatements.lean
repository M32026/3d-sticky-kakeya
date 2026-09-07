import MyLeanRepo.Kakeya.Assouad.PropStickyLeafStatements
import MyLeanRepo.Kakeya.Assouad.PropStickySelectedScaleCover

/-! # Exact strict-scale witnesses on one complete caller fiber -/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperCallerFiberScaleData
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (callerParent : Fin prepared.callerStrict.coarse.card)
    (coordinate : Fin prepared.strictScaleCount) where
  scaleData :
    WZ2PaperScaleCoverData
      (prepared.callerStrict.cover.fullFiberSubfamily
        callerParent).family
      (prepared.strictScale coordinate)
      prepared.structuralConstant
  coarse_eq :
    scaleData.coarse =
      ((prepared.strictScaleData coordinate).cover
        |>.hitParentSubfamily
          (prepared.callerStrict.cover.fullFiberSubfamily
            callerParent)).family
  cover_eq :
    HEq scaleData.cover
      ((prepared.strictScaleData coordinate).cover
        |>.restrictToHitParents
          (prepared.callerStrict.cover.fullFiberSubfamily
            callerParent))
  synchronization :
    (∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
      let scaleData :=
        Classical.choice
          (prepared.sourceExactCWA.2.2.2 rho)
      WZ2PaperPureInternalCoverSynchronization
        source scaleData.coarse scaleData.cover) →
      WZ2PaperPureInternalCoverSynchronization
        (prepared.callerStrict.cover.fullFiberSubfamily
          callerParent).family
        scaleData.coarse scaleData.cover
  ambientParent :
    Fin scaleData.coarse.card →
      Fin (prepared.strictScaleData coordinate).coarse.card
  ambientParent_injective : Function.Injective ambientParent
  ambientParent_tube_eq :
    ∀ parent,
      scaleData.coarse.tube parent =
        (prepared.strictScaleData coordinate).coarse.tube
          (ambientParent parent)
  parent_ambient_eq :
    ∀ sourceIndex,
      ambientParent (scaleData.cover.parent sourceIndex) =
        (prepared.strictScaleData coordinate).cover.parent
          ((prepared.callerStrict.cover.fullFiberSubfamily
            callerParent).embedding sourceIndex)
  full_fiber_complete :
    ∀ parent : Fin scaleData.coarse.card,
      Finset.image
          (prepared.callerStrict.cover.fullFiberSubfamily
            callerParent).embedding
          (wz2PaperFullFiberIndices
            (prepared.callerStrict.cover.fullFiberSubfamily
              callerParent).family
            scaleData.coarse parent) =
        wz2PaperFullFiberIndices
          prepared.refinement.selected.family
          (prepared.strictScaleData coordinate).coarse
          (ambientParent parent)
  coarse_strongly_separated :
    ∀ first second : Fin scaleData.coarse.card,
      first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * (prepared.strictScale coordinate).1 <
          wz1PaperLineDistance
            (scaleData.coarse.tube first)
            (scaleData.coarse.tube second)

end Kakeya.Assouad

end
