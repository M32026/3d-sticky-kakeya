import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryEnvelopeJohnTransport
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureQuotientCoverData
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12QuotientBodyCWA

/-!
# Parentwise actual-body CWA for an envelope quotient

This module isolates the generic finite assembly after a public ordinary
envelope cover has been constructed.  The public cover is required to have
the historical nested-quotient parent map and exactly the same complete
fibers.  No such cover is inferred from the internal line-cover data.

Inside each envelope parent, actual-John bodies from the complete fine fiber
of the corresponding actual parent are first transported directly to the
factor-`19` envelope John chart.  They are then grouped onto the complete
caller full fiber by a carrier-faithful uniform `BodyFamily` cover.
-/

noncomputable section

namespace Kakeya.Assouad

/--
The exact index and carrier data needed inside one envelope parent.

`transportedBodies` retains the multiplicity of the complete actual-parent
fine fiber.  Its first comparison is one-to-one and uses the direct
actual-John to envelope-John coordinate change.  Its second comparison may be
many-to-one and is recorded by the generic uniform body cover.
-/
structure WZ2PaperPureQuotientEnvelopeParentBodyData
    {delta caller actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {callerCoarse : Kakeya.Streamlined.TubeFamily caller}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    (actualParent : Fin actualCoarse.card)
    {C bodyK : ENNReal}
    (actualFiber :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := actualCoarse)
        actualParent C)
    (envelopeNormalization :
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope
          (actualCoarse.tube actualParent))) where
  transportedBodies : Kakeya.Streamlined.BodyFamily
  transportIndexEquiv :
    Fin transportedBodies.card ≃
      Fin
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := fine) (coarse := actualCoarse)
          actualParent actualFiber.normalization).card
  transportCarrierContainment :
    ∀ targetIndex,
      wz2PaperOrdinaryEnvelopeJohnCoordinateChange
            actualFiber.normalization envelopeNormalization ''
          ((wz2PaperPureUnitRescaledFullFiberBodyFamily
            (fine := fine) (coarse := actualCoarse)
            actualParent actualFiber.normalization).body
              (transportIndexEquiv targetIndex)).carrier ⊆
        (transportedBodies.body targetIndex).carrier
  bodyCover :
    WZ2PaperPureQuotientBodyCoverData
      transportedBodies
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := callerCoarse)
        (coarse := wz2PaperOrdinaryEnvelopeFamily actualCoarse)
        actualParent envelopeNormalization)
      bodyK

namespace WZ2PaperPureQuotientEnvelopeParentBodyData

/-- Direct actual-John to envelope-John transport for the complete fine
fiber, before grouping by caller parent. -/
theorem transported_convexWolff
    {delta caller actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {callerCoarse : Kakeya.Streamlined.TubeFamily caller}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    {actualParent : Fin actualCoarse.card}
    {C bodyK : ENNReal}
    {actualFiber :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := actualCoarse)
        actualParent C}
    {envelopeNormalization :
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope
          (actualCoarse.tube actualParent))}
    (data :
      WZ2PaperPureQuotientEnvelopeParentBodyData
        (callerCoarse := callerCoarse) (bodyK := bodyK)
        actualParent actualFiber envelopeNormalization)
    (hactual : 0 < actual) :
    WZ2PaperBodyConvexWolffBound
      data.transportedBodies ((185193 : ENNReal) * C) := by
  exact
    wz2PaperBodyConvexWolffBound_of_ordinaryEnvelopeJohnTransport
      hactual (actualCoarse.tube actualParent)
      actualFiber.normalization envelopeNormalization
      data.transportIndexEquiv data.transportCarrierContainment
      actualFiber.convex_wolff

/-- The complete caller full fiber in this envelope parent has the desired
`bodyK * (185193 * C)` actual-body Convex-Wolff bound. -/
theorem envelopeFullFiber_convexWolff
    {delta caller actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {callerCoarse : Kakeya.Streamlined.TubeFamily caller}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    {actualParent : Fin actualCoarse.card}
    {C bodyK : ENNReal}
    {actualFiber :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := actualCoarse)
        actualParent C}
    {envelopeNormalization :
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope
          (actualCoarse.tube actualParent))}
    (data :
      WZ2PaperPureQuotientEnvelopeParentBodyData
        (callerCoarse := callerCoarse) (bodyK := bodyK)
        actualParent actualFiber envelopeNormalization)
    (hactual : 0 < actual) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := callerCoarse)
        (coarse := wz2PaperOrdinaryEnvelopeFamily actualCoarse)
        actualParent envelopeNormalization)
      (bodyK * ((185193 : ENNReal) * C)) :=
  data.bodyCover.convexWolff
    (data.transported_convexWolff hactual)

end WZ2PaperPureQuotientEnvelopeParentBodyData

/-- The canonical complete actual-parent fine fiber, written directly in the
envelope parent's John chart. -/
noncomputable def wz2PaperPureQuotientEnvelopeTransportedBodyFamily
    {delta actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    (actualParent : Fin actualCoarse.card)
    {C : ENNReal}
    (actualFiber :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := actualCoarse)
        actualParent C)
    (envelopeNormalization :
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope
          (actualCoarse.tube actualParent))) :
    Kakeya.Streamlined.BodyFamily where
  card :=
    (wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := fine) (coarse := actualCoarse)
      actualParent actualFiber.normalization).card
  body sourceIndex :=
    ⟨envelopeNormalization.map ''
      (fine.tube
        ((wz2PaperOrdinaryFullFiberIndexEquiv actualParent)
          sourceIndex).1).carrier⟩

/-- The canonical parent map from the complete actual-parent fine fiber to
the caller parents in the corresponding public envelope full fiber. -/
noncomputable def wz2PaperPureQuotientEnvelopeBodyParent
    {delta caller actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {callerCoarse : Kakeya.Streamlined.TubeFamily caller}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    {callerInternal :
      WZ2PaperPartitioningCover fine callerCoarse}
    {actualInternal :
      WZ2PaperPartitioningCover fine actualCoarse}
    {quotientK C : ENNReal}
    (callerSynchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine callerCoarse callerInternal)
    (actualSynchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine actualCoarse actualInternal)
    (quotient :
      WZ2PaperNestedQuotientCoverData
        callerInternal actualInternal quotientK)
    (envelopeCover :
      WZ2PaperPurePartitioningCover
        callerCoarse (wz2PaperOrdinaryEnvelopeFamily actualCoarse))
    (envelopeParentEq :
      ∀ callerIndex,
        envelopeCover.parent callerIndex =
          quotient.parent callerIndex)
    (hactual : 0 < actual)
    (actualParent : Fin actualCoarse.card)
    (actualFiber :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := actualCoarse)
        actualParent C)
    (envelopeNormalization :
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope
          (actualCoarse.tube actualParent))) :
    Fin
        (wz2PaperPureQuotientEnvelopeTransportedBodyFamily
          actualParent actualFiber envelopeNormalization).card →
      Fin
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := callerCoarse)
          (coarse := wz2PaperOrdinaryEnvelopeFamily actualCoarse)
          actualParent envelopeNormalization).card :=
  fun sourceIndex =>
    let source :=
      (wz2PaperOrdinaryFullFiberIndexEquiv actualParent) sourceIndex
    let callerIndex := callerInternal.parent source.1
    let targetIndexEquiv :=
      wz2PaperOrdinaryFullFiberIndexEquiv
        (fine := callerCoarse)
        (coarse := wz2PaperOrdinaryEnvelopeFamily actualCoarse)
        actualParent
    targetIndexEquiv.symm
      ⟨callerIndex, by
        rw [envelopeCover.mem_fullFiber_iff_parent_eq
          (mul_nonneg (by norm_num) hactual.le)]
        rw [envelopeParentEq callerIndex, quotient.compatible source.1]
        have hpublicActual :
            actualSynchronization.publicCover.parent source.1 =
              actualParent :=
          (actualSynchronization.publicCover.mem_fullFiber_iff_parent_eq
            hactual.le actualParent source.1).mp source.2
        exact
          (actualSynchronization.parent_eq source.1).symm.trans
            hpublicActual⟩

/-- Every caller body in one public envelope full fiber is hit by the
canonical fine-to-caller parent map. -/
theorem wz2PaperPureQuotientEnvelopeBodyParent_surjective
    {delta caller actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {callerCoarse : Kakeya.Streamlined.TubeFamily caller}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    {callerInternal :
      WZ2PaperPartitioningCover fine callerCoarse}
    {actualInternal :
      WZ2PaperPartitioningCover fine actualCoarse}
    {quotientK C : ENNReal}
    (callerSynchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine callerCoarse callerInternal)
    (actualSynchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine actualCoarse actualInternal)
    (quotient :
      WZ2PaperNestedQuotientCoverData
        callerInternal actualInternal quotientK)
    (envelopeCover :
      WZ2PaperPurePartitioningCover
        callerCoarse (wz2PaperOrdinaryEnvelopeFamily actualCoarse))
    (envelopeParentEq :
      ∀ callerIndex,
        envelopeCover.parent callerIndex =
          quotient.parent callerIndex)
    (hactual : 0 < actual)
    (actualParent : Fin actualCoarse.card)
    (actualFiber :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := actualCoarse)
        actualParent C)
    (envelopeNormalization :
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope
          (actualCoarse.tube actualParent))) :
    Function.Surjective
      (wz2PaperPureQuotientEnvelopeBodyParent
        callerSynchronization actualSynchronization quotient
        envelopeCover envelopeParentEq hactual actualParent
        actualFiber envelopeNormalization) := by
  intro targetIndex
  let targetIndexEquiv :=
    wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := callerCoarse)
      (coarse := wz2PaperOrdinaryEnvelopeFamily actualCoarse)
      actualParent
  let targetCaller := targetIndexEquiv targetIndex
  rcases callerInternal.parent_surjective targetCaller.1 with
    ⟨source, hsourceCaller⟩
  have htargetParent :
      envelopeCover.parent targetCaller.1 = actualParent :=
    (envelopeCover.mem_fullFiber_iff_parent_eq
      (mul_nonneg (by norm_num) hactual.le)
      actualParent targetCaller.1).mp targetCaller.2
  have hsourceActualParent :
      actualInternal.parent source = actualParent := by
    rw [← quotient.compatible source, hsourceCaller]
    exact (envelopeParentEq targetCaller.1).symm.trans htargetParent
  have hsourceActual :
      source ∈
        wz2PaperOrdinaryFullFiberIndices
          fine actualCoarse actualParent := by
    rw [actualSynchronization.publicCover.mem_fullFiber_iff_parent_eq
      hactual.le]
    exact
      (actualSynchronization.parent_eq source).trans
        hsourceActualParent
  let sourceIndexEquiv :=
    wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := fine) (coarse := actualCoarse) actualParent
  let sourceIndex := sourceIndexEquiv.symm ⟨source, hsourceActual⟩
  refine ⟨sourceIndex, ?_⟩
  apply targetIndexEquiv.injective
  apply Subtype.ext
  simpa [wz2PaperPureQuotientEnvelopeBodyParent,
    sourceIndex, sourceIndexEquiv, targetIndexEquiv, targetCaller]
    using hsourceCaller

/-- The canonical body parent is carrier-faithful because the caller public
cover contains every fine tube assigned to that caller parent. -/
theorem wz2PaperPureQuotientEnvelopeBodyParent_carrierContained
    {delta caller actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {callerCoarse : Kakeya.Streamlined.TubeFamily caller}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    {callerInternal :
      WZ2PaperPartitioningCover fine callerCoarse}
    {actualInternal :
      WZ2PaperPartitioningCover fine actualCoarse}
    {quotientK C : ENNReal}
    (callerSynchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine callerCoarse callerInternal)
    (actualSynchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine actualCoarse actualInternal)
    (quotient :
      WZ2PaperNestedQuotientCoverData
        callerInternal actualInternal quotientK)
    (envelopeCover :
      WZ2PaperPurePartitioningCover
        callerCoarse (wz2PaperOrdinaryEnvelopeFamily actualCoarse))
    (envelopeParentEq :
      ∀ callerIndex,
        envelopeCover.parent callerIndex =
          quotient.parent callerIndex)
    (hactual : 0 < actual)
    (actualParent : Fin actualCoarse.card)
    (actualFiber :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := actualCoarse)
        actualParent C)
    (envelopeNormalization :
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope
          (actualCoarse.tube actualParent)))
    (sourceIndex :
      Fin
        (wz2PaperPureQuotientEnvelopeTransportedBodyFamily
          actualParent actualFiber envelopeNormalization).card) :
    ((wz2PaperPureQuotientEnvelopeTransportedBodyFamily
      actualParent actualFiber envelopeNormalization).body
        sourceIndex).carrier ⊆
      ((wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := callerCoarse)
        (coarse := wz2PaperOrdinaryEnvelopeFamily actualCoarse)
        actualParent envelopeNormalization).body
          (wz2PaperPureQuotientEnvelopeBodyParent
            callerSynchronization actualSynchronization quotient
            envelopeCover envelopeParentEq hactual actualParent
            actualFiber envelopeNormalization sourceIndex)).carrier := by
  let source :=
    (wz2PaperOrdinaryFullFiberIndexEquiv actualParent) sourceIndex
  have hcaller :
      (fine.tube source.1).carrier ⊆
        (callerCoarse.tube
          (callerInternal.parent source.1)).carrier := by
    have hmember :=
      callerSynchronization.publicCover.parent_mem_fullFiber source.1
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at hmember
    rw [callerSynchronization.parent_eq source.1] at hmember
    exact hmember
  change
    envelopeNormalization.map '' (fine.tube source.1).carrier ⊆
      envelopeNormalization.map ''
        (callerCoarse.tube
          (((wz2PaperOrdinaryFullFiberIndexEquiv
            (fine := callerCoarse)
            (coarse := wz2PaperOrdinaryEnvelopeFamily actualCoarse)
            actualParent)
              (wz2PaperPureQuotientEnvelopeBodyParent
                callerSynchronization actualSynchronization quotient
                envelopeCover envelopeParentEq hactual actualParent
                actualFiber envelopeNormalization sourceIndex)).1)).carrier
  have hindex :
      ((wz2PaperOrdinaryFullFiberIndexEquiv
        (fine := callerCoarse)
        (coarse := wz2PaperOrdinaryEnvelopeFamily actualCoarse)
        actualParent)
          (wz2PaperPureQuotientEnvelopeBodyParent
            callerSynchronization actualSynchronization quotient
            envelopeCover envelopeParentEq hactual actualParent
            actualFiber envelopeNormalization sourceIndex)).1 =
        callerInternal.parent source.1 := by
    simp [wz2PaperPureQuotientEnvelopeBodyParent, source]
  rw [hindex]
  exact Set.image_mono hcaller

/--
Generic parentwise envelope assembly with all public/internal provenance
exposed.

The exact full-fiber equality is an input, not a consequence of the internal
line-cover quotient.  It is used to transport the historical quotient
uniformity to the public ordinary envelope cover.  The actual-body fields are
then sufficient to build the existing pure quotient scale inputs.
-/
structure WZ2PaperPureQuotientEnvelopeBodyCWAData
    {delta caller actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {callerCoarse : Kakeya.Streamlined.TubeFamily caller}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    (callerInternal :
      WZ2PaperPartitioningCover fine callerCoarse)
    (actualInternal :
      WZ2PaperPartitioningCover fine actualCoarse)
    (quotientK bodyK C : ENNReal) where
  delta_pos : 0 < delta
  caller_pos : 0 < caller
  actual_pos : 0 < actual
  callerSynchronization :
    WZ2PaperPureInternalCoverSynchronization
      fine callerCoarse callerInternal
  actualSynchronization :
    WZ2PaperPureInternalCoverSynchronization
      fine actualCoarse actualInternal
  quotient :
    WZ2PaperNestedQuotientCoverData
      callerInternal actualInternal quotientK
  envelopeCover :
    WZ2PaperPurePartitioningCover
      callerCoarse (wz2PaperOrdinaryEnvelopeFamily actualCoarse)
  envelope_parent_eq :
    ∀ callerIndex,
      envelopeCover.parent callerIndex =
        quotient.parent callerIndex
  envelope_full_fiber_eq :
    ∀ actualParent : Fin actualCoarse.card,
      wz2PaperOrdinaryFullFiberIndices
          callerCoarse
          (wz2PaperOrdinaryEnvelopeFamily actualCoarse)
          actualParent =
        quotient.cover.fiberIndices actualParent
  actualFiber :
    ∀ actualParent,
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := actualCoarse)
        actualParent C
  envelopeNormalization :
    ∀ actualParent : Fin actualCoarse.card,
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope
          (actualCoarse.tube actualParent))
  grouping_fiber_uniform :
    ∀ actualParent first second,
      ((Finset.univ.filter fun source =>
        wz2PaperPureQuotientEnvelopeBodyParent
            callerSynchronization actualSynchronization quotient
            envelopeCover envelope_parent_eq actual_pos actualParent
            (actualFiber actualParent)
            (envelopeNormalization actualParent) source =
          first).card : ENNReal) ≤
        bodyK *
          ((Finset.univ.filter fun source =>
            wz2PaperPureQuotientEnvelopeBodyParent
                callerSynchronization actualSynchronization quotient
                envelopeCover envelope_parent_eq actual_pos actualParent
                (actualFiber actualParent)
                (envelopeNormalization actualParent) source =
              second).card : ENNReal)

namespace WZ2PaperPureQuotientEnvelopeBodyCWAData

/-- The canonical transported family and canonical fine-to-caller map produce
the generic parentwise body package. -/
noncomputable def parentBody
    {delta caller actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {callerCoarse : Kakeya.Streamlined.TubeFamily caller}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    {callerInternal :
      WZ2PaperPartitioningCover fine callerCoarse}
    {actualInternal :
      WZ2PaperPartitioningCover fine actualCoarse}
    {quotientK bodyK C : ENNReal}
    (data :
      WZ2PaperPureQuotientEnvelopeBodyCWAData
        callerInternal actualInternal quotientK bodyK C)
    (actualParent : Fin actualCoarse.card) :
    WZ2PaperPureQuotientEnvelopeParentBodyData
      (callerCoarse := callerCoarse) (bodyK := bodyK)
      actualParent (data.actualFiber actualParent)
      (data.envelopeNormalization actualParent) where
  transportedBodies :=
    wz2PaperPureQuotientEnvelopeTransportedBodyFamily
      actualParent (data.actualFiber actualParent)
      (data.envelopeNormalization actualParent)
  transportIndexEquiv := Equiv.cast (by rfl)
  transportCarrierContainment := by
    intro sourceIndex
    change
      wz2PaperOrdinaryEnvelopeJohnCoordinateChange
            (data.actualFiber actualParent).normalization
            (data.envelopeNormalization actualParent) ''
          ((data.actualFiber actualParent).normalization.map ''
            (fine.tube
              ((wz2PaperOrdinaryFullFiberIndexEquiv actualParent)
                sourceIndex).1).carrier) ⊆
        (data.envelopeNormalization actualParent).map ''
          (fine.tube
            ((wz2PaperOrdinaryFullFiberIndexEquiv actualParent)
              sourceIndex).1).carrier
    rw [wz2PaperOrdinaryEnvelopeJohnCoordinateChange_image]
  bodyCover := {
    parent :=
      wz2PaperPureQuotientEnvelopeBodyParent
        data.callerSynchronization data.actualSynchronization
        data.quotient data.envelopeCover data.envelope_parent_eq
        data.actual_pos actualParent (data.actualFiber actualParent)
        (data.envelopeNormalization actualParent)
    parent_surjective :=
      wz2PaperPureQuotientEnvelopeBodyParent_surjective
        data.callerSynchronization data.actualSynchronization
        data.quotient data.envelopeCover data.envelope_parent_eq
        data.actual_pos actualParent (data.actualFiber actualParent)
        (data.envelopeNormalization actualParent)
    carrier_contained :=
      wz2PaperPureQuotientEnvelopeBodyParent_carrierContained
        data.callerSynchronization data.actualSynchronization
        data.quotient data.envelopeCover data.envelope_parent_eq
        data.actual_pos actualParent (data.actualFiber actualParent)
        (data.envelopeNormalization actualParent)
    fiber_uniform := data.grouping_fiber_uniform actualParent
  }

/-- Exact envelope-fiber equality transports the nested quotient's
`quotientK^2` assigned-fiber uniformity to genuine public full fibers. -/
theorem envelope_full_fiber_uniform
    {delta caller actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {callerCoarse : Kakeya.Streamlined.TubeFamily caller}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    {callerInternal :
      WZ2PaperPartitioningCover fine callerCoarse}
    {actualInternal :
      WZ2PaperPartitioningCover fine actualCoarse}
    {quotientK bodyK C : ENNReal}
    (data :
      WZ2PaperPureQuotientEnvelopeBodyCWAData
        callerInternal actualInternal quotientK bodyK C) :
    WZ2PaperPureFullFibersAreCUniform
      callerCoarse
      (wz2PaperOrdinaryEnvelopeFamily actualCoarse)
      (quotientK * quotientK) := by
  intro first second
  rw [wz2PaperOrdinaryFullFiberCount,
    wz2PaperOrdinaryFullFiberCount,
    data.envelope_full_fiber_eq first,
    data.envelope_full_fiber_eq second]
  exact data.quotient.assigned_fiber_uniform first second

/-- Every complete public envelope fiber has actual-John CWA with the exact
loss `bodyK * (185193 * C)`. -/
theorem envelopeFullFiber_convexWolff
    {delta caller actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {callerCoarse : Kakeya.Streamlined.TubeFamily caller}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    {callerInternal :
      WZ2PaperPartitioningCover fine callerCoarse}
    {actualInternal :
      WZ2PaperPartitioningCover fine actualCoarse}
    {quotientK bodyK C : ENNReal}
    (data :
      WZ2PaperPureQuotientEnvelopeBodyCWAData
        callerInternal actualInternal quotientK bodyK C)
    (actualParent : Fin actualCoarse.card) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := callerCoarse)
        (coarse := wz2PaperOrdinaryEnvelopeFamily actualCoarse)
        actualParent (data.envelopeNormalization actualParent))
      (bodyK * ((185193 : ENNReal) * C)) :=
  (data.parentBody actualParent).envelopeFullFiber_convexWolff
    data.actual_pos

/-- Package the parentwise result in the exact interface consumed by
`WZ2PaperPureQuotientScaleInputs`. -/
noncomputable def toPureQuotientScaleInputs
    {delta caller actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {callerCoarse : Kakeya.Streamlined.TubeFamily caller}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    {callerInternal :
      WZ2PaperPartitioningCover fine callerCoarse}
    {actualInternal :
      WZ2PaperPartitioningCover fine actualCoarse}
    {quotientK bodyK C : ENNReal}
    (data :
      WZ2PaperPureQuotientEnvelopeBodyCWAData
        callerInternal actualInternal quotientK bodyK C) :
    WZ2PaperPureQuotientScaleInputs
      data.envelopeCover
      (quotientK * quotientK)
      bodyK
      ((185193 : ENNReal) * C) where
  delta_pos := data.caller_pos
  sigma_pos := mul_pos (by norm_num) data.actual_pos
  middle_full_fiber_uniform := data.envelope_full_fiber_uniform
  normalization := data.envelopeNormalization
  sourceBodies := fun actualParent =>
    (data.parentBody actualParent).transportedBodies
  source_cwa := fun actualParent =>
    (data.parentBody actualParent).transported_convexWolff
      data.actual_pos
  bodyCover := fun actualParent =>
    (data.parentBody actualParent).bodyCover

/-- The resulting pure scale witness keeps quotient-cover uniformity and
actual-body CWA as separate losses. -/
noncomputable def toPureScaleData
    {delta caller actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {callerCoarse : Kakeya.Streamlined.TubeFamily caller}
    {actualCoarse : Kakeya.Streamlined.TubeFamily actual}
    {callerInternal :
      WZ2PaperPartitioningCover fine callerCoarse}
    {actualInternal :
      WZ2PaperPartitioningCover fine actualCoarse}
    {quotientK bodyK C : ENNReal}
    (data :
      WZ2PaperPureQuotientEnvelopeBodyCWAData
        callerInternal actualInternal quotientK bodyK C) :
    WZ2PaperPureScaleCoverData
      callerCoarse (19 * actual)
      (max (quotientK * quotientK)
        (bodyK * ((185193 : ENNReal) * C))) :=
  data.toPureQuotientScaleInputs.toPureScaleData

end WZ2PaperPureQuotientEnvelopeBodyCWAData

end Kakeya.Assouad

end
