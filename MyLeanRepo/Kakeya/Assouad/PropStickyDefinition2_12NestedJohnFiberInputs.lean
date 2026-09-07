import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnCWATransport

/-!
# Index and carrier inputs for nested actual-John transport

Once a target public ordinary full fiber is identified with one complete
source full fiber, the remaining index equivalence and pointwise carrier
containment are finite bookkeeping.  This module isolates that bookkeeping
from both the public cover construction and the Jacobian estimate.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Exact source-index equality for a target ordinary full fiber produces the
finite index equivalence and pointwise actual-John containment needed by the
nested affine CWA transport.
-/
structure WZ2PaperNestedActualJohnFullFiberTransportInputs
    {delta rho sigma : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily delta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily rho}
    {targetFine : Kakeya.Streamlined.TubeFamily (delta / sigma)}
    {targetCoarse : Kakeya.Streamlined.TubeFamily (rho / sigma)}
    (anchor : Kakeya.DeltaTube sigma)
    (hsigma : 0 < sigma)
    (sourceParent : Fin sourceCoarse.card)
    (targetParent : Fin targetCoarse.card)
    (sourceJohn :
      WZ2PaperAssouadUnitRescalingData
        (sourceCoarse.tube sourceParent))
    (targetJohn :
      WZ2PaperAssouadUnitRescalingData
        (targetCoarse.tube targetParent)) where
  indexEquiv :
    Fin
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := targetFine) (coarse := targetCoarse)
          targetParent targetJohn).card ≃
      Fin
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := sourceFine) (coarse := sourceCoarse)
          sourceParent sourceJohn).card
  carrier_containment :
    ∀ targetIndex,
      wz2PaperNestedJohnCoordinateChange
            (anchor := anchor) hsigma sourceJohn targetJohn ''
          ((wz2PaperPureUnitRescaledFullFiberBodyFamily
            (fine := sourceFine) (coarse := sourceCoarse)
            sourceParent sourceJohn).body
              (indexEquiv targetIndex)).carrier ⊆
        ((wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := targetFine) (coarse := targetCoarse)
          targetParent targetJohn).body targetIndex).carrier

/--
Construct the nested actual-John transport inputs from one exact full-fiber
source-index equality.

`sourceIndex` identifies every target fine tube with its source fine tube.
The containment premise concerns the literal first-stage affine image in the
ordinary target carrier; it is precisely what the public ordinary rescaling
producer proves.
-/
noncomputable def wz2PaperNestedActualJohnFullFiberTransportInputs_of_sourceImage
    {delta rho sigma : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily delta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily rho}
    {targetFine : Kakeya.Streamlined.TubeFamily (delta / sigma)}
    {targetCoarse : Kakeya.Streamlined.TubeFamily (rho / sigma)}
    (anchor : Kakeya.DeltaTube sigma)
    (hsigma : 0 < sigma)
    (sourceParent : Fin sourceCoarse.card)
    (targetParent : Fin targetCoarse.card)
    (sourceIndex : Fin targetFine.card → Fin sourceFine.card)
    (sourceIndex_injective : Function.Injective sourceIndex)
    (fullFiber_source_indices :
      Finset.image sourceIndex
          (wz2PaperOrdinaryFullFiberIndices
            targetFine targetCoarse targetParent) =
        wz2PaperOrdinaryFullFiberIndices
          sourceFine sourceCoarse sourceParent)
    (literal_image_subset :
      ∀ target,
        target ∈
            wz2PaperOrdinaryFullFiberIndices
              targetFine targetCoarse targetParent →
          wz2PaperLiteralUnitRescalingMap anchor hsigma ''
              (sourceFine.tube (sourceIndex target)).carrier ⊆
            (targetFine.tube target).carrier)
    (sourceJohn :
      WZ2PaperAssouadUnitRescalingData
        (sourceCoarse.tube sourceParent))
    (targetJohn :
      WZ2PaperAssouadUnitRescalingData
        (targetCoarse.tube targetParent)) :
    WZ2PaperNestedActualJohnFullFiberTransportInputs
      (sourceFine := sourceFine) (sourceCoarse := sourceCoarse)
      (targetFine := targetFine) (targetCoarse := targetCoarse)
      anchor hsigma sourceParent targetParent sourceJohn targetJohn := by
  let sourceFiber :=
    wz2PaperOrdinaryFullFiberIndices
      sourceFine sourceCoarse sourceParent
  let targetFiber :=
    wz2PaperOrdinaryFullFiberIndices
      targetFine targetCoarse targetParent
  let targetToSource :
      {target : Fin targetFine.card // target ∈ targetFiber} →
        {source : Fin sourceFine.card // source ∈ sourceFiber} :=
    fun target =>
      ⟨sourceIndex target.1, by
        dsimp only [sourceFiber, targetFiber]
        rw [← fullFiber_source_indices]
        exact Finset.mem_image.mpr ⟨target.1, target.2, rfl⟩⟩
  have htargetToSourceInjective :
      Function.Injective targetToSource := by
    intro first second heq
    apply Subtype.ext
    exact sourceIndex_injective
      (congrArg Subtype.val heq)
  have htargetToSourceSurjective :
      Function.Surjective targetToSource := by
    intro source
    have hsource :
        source.1 ∈ Finset.image sourceIndex targetFiber := by
      rw [fullFiber_source_indices]
      exact source.2
    rcases Finset.mem_image.mp hsource with
      ⟨target, htarget, hindex⟩
    refine ⟨⟨target, htarget⟩, ?_⟩
    apply Subtype.ext
    exact hindex
  let subtypeEquiv :
      {target : Fin targetFine.card // target ∈ targetFiber} ≃
        {source : Fin sourceFine.card // source ∈ sourceFiber} :=
    Equiv.ofBijective targetToSource
      ⟨htargetToSourceInjective, htargetToSourceSurjective⟩
  let targetFiberEquiv :=
    wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := targetFine) (coarse := targetCoarse) targetParent
  let sourceFiberEquiv :=
    wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := sourceFine) (coarse := sourceCoarse) sourceParent
  let indexEquiv :=
    (targetFiberEquiv.trans subtypeEquiv).trans sourceFiberEquiv.symm
  refine
    {
      indexEquiv := indexEquiv
      carrier_containment := ?_
    }
  intro targetIndex
  let targetSource := targetFiberEquiv targetIndex
  have htargetSource :
      targetSource.1 ∈ targetFiber :=
    targetSource.2
  have hsourceIndex :
      (sourceFiberEquiv (indexEquiv targetIndex)).1 =
        sourceIndex targetSource.1 := by
    simp [indexEquiv, targetSource, subtypeEquiv, targetToSource,
      targetFiberEquiv, sourceFiberEquiv]
  change
    wz2PaperNestedJohnCoordinateChange
          (anchor := anchor) hsigma sourceJohn targetJohn ''
        (sourceJohn.map ''
          (sourceFine.tube
            ((sourceFiberEquiv (indexEquiv targetIndex)).1)).carrier) ⊆
      targetJohn.map ''
        (targetFine.tube targetSource.1).carrier
  rw [hsourceIndex,
    wz2PaperNestedJohnCoordinateChange_image
      (anchor := anchor) hsigma sourceJohn targetJohn]
  exact Set.image_mono
    (literal_image_subset targetSource.1 htargetSource)

/-- Apply the closed Jacobian theorem to one complete nested actual-John
fiber. -/
theorem wz2PaperBodyConvexWolffBound_of_nestedActualJohnFullFiber
    {delta rho sigma : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily delta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily rho}
    {targetFine : Kakeya.Streamlined.TubeFamily (delta / sigma)}
    {targetCoarse : Kakeya.Streamlined.TubeFamily (rho / sigma)}
    {anchor : Kakeya.DeltaTube sigma}
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hrhoSigma : rho ≤ sigma)
    (hsigmaOne : sigma ≤ 1)
    (sourceParent : Fin sourceCoarse.card)
    (targetParent : Fin targetCoarse.card)
    (sourceJohn :
      WZ2PaperAssouadUnitRescalingData
        (sourceCoarse.tube sourceParent))
    (targetJohn :
      WZ2PaperAssouadUnitRescalingData
        (targetCoarse.tube targetParent))
    (inputs :
      WZ2PaperNestedActualJohnFullFiberTransportInputs
        (sourceFine := sourceFine) (sourceCoarse := sourceCoarse)
        (targetFine := targetFine) (targetCoarse := targetCoarse)
        anchor hsigma sourceParent targetParent sourceJohn targetJohn)
    {C : ENNReal}
    (hsource :
      WZ2PaperBodyConvexWolffBound
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := sourceFine) (coarse := sourceCoarse)
          sourceParent sourceJohn)
        C) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := targetFine) (coarse := targetCoarse)
        targetParent targetJohn)
      ((81000000 : ENNReal) * C) :=
  wz2PaperBodyConvexWolffBound_of_nestedCanonicalJohnTransport
    hsigma sourceJohn targetJohn
    inputs.indexEquiv inputs.carrier_containment
    (wz2PaperNestedJohnCoordinateChange_inverse_volume
      hrho hsigma hrhoSigma hsigmaOne
      sourceJohn targetJohn)
    hsource

end Kakeya.Assouad

end
