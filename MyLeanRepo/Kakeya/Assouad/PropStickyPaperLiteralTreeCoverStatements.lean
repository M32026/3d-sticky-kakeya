import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFiberTreeStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFiberTreeSubfamilies
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescalingStatements

/-!
# Literal-paper rescaling along one source fiber-tree edge

This is the literal-map replacement for the two old-map geometric boundaries
of `WZ2PaperRescaledTreeCoverData`.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Carrier containment after one common literal-paper rescaling.
-/
def WZ2PaperLiteralCommonRescalingCarrierTransferStatement : Prop :=
  ∀ {delta rho sigma : ℝ},
    0 < delta →
    100 * delta ≤ rho →
    rho ≤ sigma →
    ∀ (hsigma : 0 < sigma),
      sigma ≤ 1 →
      ∀ (fine : Kakeya.DeltaTube delta)
        (middle : Kakeya.DeltaTube rho)
        (anchor : Kakeya.DeltaTube sigma),
        WZ1PaperTubeInLineClass fine →
        WZ1PaperTubeInLineClass middle →
        WZ1PaperTubeInLineClass anchor →
        WZ1PaperTubeCovers fine middle →
        WZ2PaperTubeCarrierCovers fine middle →
        WZ1PaperTubeCovers fine anchor →
        WZ2PaperDilatedTubeCovers 2 middle anchor →
        ∀ (targetFine : Kakeya.DeltaTube (delta / sigma))
          (targetMiddle : Kakeya.DeltaTube (rho / sigma)),
          WZ1PaperTubeInLineClass targetFine →
          WZ1PaperTubeInLineClass targetMiddle →
          tubeAxisLine targetFine =
              wz2PaperLiteralUnitRescalingMap anchor hsigma ''
                tubeAxisLine fine →
          tubeAxisLine targetMiddle =
              wz2PaperLiteralUnitRescalingMap anchor hsigma ''
                tubeAxisLine middle →
            WZ2PaperTubeCarrierCovers targetFine targetMiddle

structure WZ2PaperLiteralRescaledTreeCoverData
    {delta rho sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarseRho : Kakeya.Streamlined.TubeFamily rho}
    {coarseSigma : Kakeya.Streamlined.TubeFamily sigma}
    (coverRho : WZ2PaperPartitioningCover fine coarseRho)
    (coverSigma : WZ2PaperPartitioningCover fine coarseSigma)
    (anchor : Fin coarseSigma.card)
    (hsigma : 0 < sigma) where
  sourceFine : Kakeya.Streamlined.TubeSubfamily fine
  sourceFine_is_anchor_fiber :
    ∀ index, coverSigma.parent (sourceFine.embedding index) = anchor
  sourceMiddle : Kakeya.Streamlined.TubeSubfamily coarseRho
  sourceMiddle_parent :
    Fin sourceFine.family.card → Fin sourceMiddle.family.card
  sourceMiddle_parent_surjective :
    Function.Surjective sourceMiddle_parent
  source_parent_eq :
    ∀ index,
      coverRho.parent (sourceFine.embedding index) =
        sourceMiddle.embedding (sourceMiddle_parent index)
  targetFine : Kakeya.Streamlined.TubeFamily (delta / sigma)
  targetFineIndex :
    Fin targetFine.card → Fin sourceFine.family.card
  targetFineIndex_bijective :
    Function.Bijective targetFineIndex
  targetFine_axis :
    ∀ index,
      tubeAxisLine (targetFine.tube index) =
        wz2PaperLiteralUnitRescalingMap
            (coarseSigma.tube anchor) hsigma ''
          tubeAxisLine
            (sourceFine.family.tube (targetFineIndex index))
  targetFine_line_class : WZ1PaperIsLineClass targetFine
  targetMiddle :
    Kakeya.Streamlined.TubeFamily (rho / sigma)
  targetMiddleIndex :
    Fin targetMiddle.card → Fin sourceMiddle.family.card
  targetMiddleIndex_bijective :
    Function.Bijective targetMiddleIndex
  targetMiddle_axis :
    ∀ index,
      tubeAxisLine (targetMiddle.tube index) =
        wz2PaperLiteralUnitRescalingMap
            (coarseSigma.tube anchor) hsigma ''
          tubeAxisLine
            (sourceMiddle.family.tube (targetMiddleIndex index))
  targetMiddle_line_class :
    WZ1PaperIsLineClass targetMiddle
  targetParent :
    Fin targetFine.card → Fin targetMiddle.card
  targetParent_surjective :
    Function.Surjective targetParent
  targetParent_source_eq :
    ∀ index,
      sourceMiddle_parent (targetFineIndex index) =
        targetMiddleIndex (targetParent index)
  target_carrier_covers :
    ∀ index,
      WZ2PaperTubeCarrierCovers
        (targetFine.tube index)
        (targetMiddle.tube (targetParent index))

def WZ2PaperLiteralRescaledTreeCoverStatement : Prop :=
  WZ2PaperFiberTreeEdgeStatement →
  WZ2PaperLiteralCanonicalUnitRescaledTubeStatement →
  WZ2PaperLiteralCommonRescalingCarrierTransferStatement →
  ∀ {delta rho sigma : ℝ},
    0 < delta →
    100 * delta ≤ rho →
    2 * rho ≤ sigma →
    ∀ hsigma : 0 < sigma,
      sigma ≤ 1 →
      ∀ {fine : Kakeya.Streamlined.TubeFamily delta}
        {coarseRho : Kakeya.Streamlined.TubeFamily rho}
        {coarseSigma : Kakeya.Streamlined.TubeFamily sigma},
        WZ1PaperIsLineClass fine →
        WZ1PaperIsLineClass coarseRho →
        WZ1PaperIsLineClass coarseSigma →
        ∀ (coverRho :
            WZ2PaperPartitioningCover fine coarseRho)
          (coverSigma :
            WZ2PaperPartitioningCover fine coarseSigma)
          (anchor : Fin coarseSigma.card),
          Nonempty
            (WZ2PaperLiteralRescaledTreeCoverData
              coverRho coverSigma anchor hsigma)

end Kakeya.Assouad

end
