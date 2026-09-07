import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryNestedLocalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GeneralJohnToJohnCWATransport
import Mathlib.Tactic

/-!
# Ordinary nested rescaling through an independent middle family

The public scale witness supplying full-fiber uniformity and Convex Wolff
bounds need not itself carry the line geometry used in the lower
localization argument.  This module transfers those analytic fields to a
second middle family with the same finite fibers, then applies the closed
ordinary nested-scale producer to that family.

No aligned exact-source object is used.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/--
The local data needed to transport one old full-fiber CWA to the John chart
of the corresponding parent in an independent middle family.
-/
structure WZ2PaperMiddleFamilyFiberTransport
    {delta sourceScale middleScale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceScale}
    {middle : Kakeya.Streamlined.TubeFamily middleScale}
    {sourceParent : Fin sourceCoarse.card}
    (middleParent : Fin middle.card)
    {C K : ENNReal}
    (sourceFiber :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := sourceCoarse) sourceParent C) where
  normalization :
    WZ2PaperAssouadUnitRescalingData (middle.tube middleParent)
  indexEquiv :
    Fin
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := fine) (coarse := middle)
          middleParent normalization).card ≃
      Fin
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := fine) (coarse := sourceCoarse)
          sourceParent sourceFiber.normalization).card
  carrier_containment :
    ∀ targetIndex,
      wz2PaperGeneralJohnToJohnCoordinateChange
            sourceFiber.normalization normalization ''
          ((wz2PaperPureUnitRescaledFullFiberBodyFamily
            (fine := fine) (coarse := sourceCoarse)
            sourceParent sourceFiber.normalization).body
              (indexEquiv targetIndex)).carrier ⊆
        ((wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := fine) (coarse := middle)
          middleParent normalization).body targetIndex).carrier
  outerJohnVolume_le :
    volume normalization.parent_convex_body.outerJohnEllipsoid ≤
      K *
        volume
          sourceFiber.normalization.parent_convex_body.outerJohnEllipsoid

/--
Data identifying the strict fibers of an analytic CWA scale with those of an
independent geometric middle family.

The target normalization is canonical.  The only analytic comparison needed
to move the old fiber CWA to that normalization is the displayed outer-John
volume bound.
-/
structure WZ2PaperMiddleFamilyScaleBridge
    {delta sourceScale middleScale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C K : ENNReal}
    (analytic :
      WZ2PaperPureScaleCoverData fine sourceScale C)
    (middle : Kakeya.Streamlined.TubeFamily middleScale) where
  middle_pos : 0 < middleScale
  cover : WZ2PaperPurePartitioningCover fine middle
  parentEquiv : Fin middle.card ≃ Fin analytic.coarse.card
  parent_commutes :
    ∀ source,
      parentEquiv (cover.parent source) =
        analytic.cover.parent source
  loss_one : 1 ≤ K
  loss_ne_top : K ≠ ⊤
  fiberTransport :
    ∀ parent
      (sourceFiber :
        WZ2PaperPureUnitRescaledFullFiberData
          (fine := fine) (coarse := analytic.coarse)
          (parentEquiv parent) C),
      WZ2PaperMiddleFamilyFiberTransport
        (middle := middle) parent (K := K) sourceFiber

namespace WZ2PaperMiddleFamilyScaleBridge

variable
    {delta sourceScale middleScale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C K : ENNReal}
    {analytic :
      WZ2PaperPureScaleCoverData fine sourceScale C}
    {middle : Kakeya.Streamlined.TubeFamily middleScale}
    (bridge :
      WZ2PaperMiddleFamilyScaleBridge (K := K) analytic middle)

include bridge

theorem fullFiberIndices_eq
    (parent : Fin middle.card) :
    wz2PaperOrdinaryFullFiberIndices fine middle parent =
      wz2PaperOrdinaryFullFiberIndices
        fine analytic.coarse (bridge.parentEquiv parent) := by
  ext source
  rw [
    bridge.cover.mem_fullFiber_iff_parent_eq
      bridge.middle_pos.le parent source,
    analytic.cover.mem_fullFiber_iff_parent_eq
      analytic.rho_pos.le (bridge.parentEquiv parent) source
  ]
  constructor
  · intro parentEq
    rw [← bridge.parent_commutes source]
    exact congrArg bridge.parentEquiv parentEq
  · intro parentEq
    apply bridge.parentEquiv.injective
    rw [bridge.parent_commutes source]
    exact parentEq

theorem fullFiberCount_eq
    (parent : Fin middle.card) :
    wz2PaperOrdinaryFullFiberCount fine middle parent =
      wz2PaperOrdinaryFullFiberCount
        fine analytic.coarse (bridge.parentEquiv parent) := by
  unfold wz2PaperOrdinaryFullFiberCount
  rw [bridge.fullFiberIndices_eq parent]

/--
Transfer the analytic scale witness to the independent middle family.

The strict fibers agree through `parentEquiv`; only the parent John chart
changes.  Consequently the loss is `K`, not a second copy of the original
constant.
-/
noncomputable def middleScaleData :
    WZ2PaperPureScaleCoverData fine middleScale (K * C) where
  delta_pos := analytic.delta_pos
  rho_pos := bridge.middle_pos
  coarse := middle
  cover := bridge.cover
  full_fiber_uniform := by
    intro first second
    rw [
      WZ2PaperMiddleFamilyScaleBridge.fullFiberCount_eq bridge first,
      WZ2PaperMiddleFamilyScaleBridge.fullFiberCount_eq bridge second
    ]
    calc
      wz2PaperOrdinaryFullFiberCount fine analytic.coarse
            (bridge.parentEquiv first) ≤
          C *
            wz2PaperOrdinaryFullFiberCount fine analytic.coarse
              (bridge.parentEquiv second) :=
        analytic.full_fiber_uniform
          (bridge.parentEquiv first) (bridge.parentEquiv second)
      _ ≤
          (K * C) *
            wz2PaperOrdinaryFullFiberCount fine analytic.coarse
              (bridge.parentEquiv second) := by
        gcongr
        calc
          C = 1 * C := by simp
          _ ≤ K * C := by
            exact mul_le_mul_left bridge.loss_one C
  rescaledFiber parent := by
    let sourceFiber :=
      Classical.choice
        (analytic.rescaledFiber (bridge.parentEquiv parent))
    let transport := bridge.fiberTransport parent sourceFiber
    exact
      ⟨{
        normalization := transport.normalization
        convex_wolff :=
          wz2PaperBodyConvexWolffBound_of_generalJohnToJohnTransport
            (source :=
              wz2PaperPureUnitRescaledFullFiberBodyFamily
                (fine := fine) (coarse := analytic.coarse)
                (bridge.parentEquiv parent) sourceFiber.normalization)
            (target :=
              wz2PaperPureUnitRescaledFullFiberBodyFamily
                (fine := fine) (coarse := middle)
                parent transport.normalization)
            (C := C) (K := K)
            sourceFiber.normalization transport.normalization
            bridge.loss_ne_top
            transport.outerJohnVolume_le
            transport.indexEquiv transport.carrier_containment
            sourceFiber.convex_wolff
      }⟩

/--
Ordinary nested rescaling with the analytic scale and the line-aware middle
family separated.

All line-cover, anchor, separation, and localization hypotheses concern
`middle`.  The old `analytic.coarse` appears only through its exact fibers and
their CWA certificates.
-/
noncomputable def ordinaryNestedScale
    {sigma : ℝ}
    (hsigma : 0 < sigma)
    (hdeltaMiddle : 100 * delta ≤ middleScale)
    (hmiddleSigma : middleScale ≤ sigma)
    (hsigmaOne : sigma ≤ 1)
    (anchor : Kakeya.DeltaTube sigma)
    (hfine : WZ1PaperIsLineClass fine)
    (hmiddle : WZ1PaperIsLineClass middle)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hFineMiddle :
      ∀ source,
        WZ1PaperTubeCovers
          (fine.tube source)
          (middle.tube (bridge.cover.parent source)))
    (hFineAnchor :
      ∀ source, WZ1PaperTubeCovers (fine.tube source) anchor)
    (hMiddleAnchor :
      ∀ parent,
        WZ2PaperDilatedTubeCovers 2
          (middle.tube parent) anchor)
    (hMiddleSeparated :
      ∀ first second, first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * middleScale <
          wz1PaperLineDistance
            (middle.tube first) (middle.tube second))
    (localization :
      WZ2PaperOrdinaryNestedTargetLocalization
        fine middle anchor hsigma) :
    WZ2PaperPureScaleCoverData
      (wz2PaperLiteralOrdinaryRescaledFamily fine anchor hsigma)
      (middleScale / sigma)
      (max (K * C) ((81000000 : ENNReal) * (K * C))) :=
  wz2PaperPureScaleCoverData.ordinaryNestedScale
    (WZ2PaperMiddleFamilyScaleBridge.middleScaleData bridge)
    hsigma hdeltaMiddle hmiddleSigma hsigmaOne anchor
    hfine hmiddle hanchor hFineMiddle hFineAnchor
    hMiddleAnchor hMiddleSeparated localization

end WZ2PaperMiddleFamilyScaleBridge

end Kakeya.Assouad

end
