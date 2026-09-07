import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationCanonicalCropScalars
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureNearbyTopLevelCWA
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.VolumeUtils
import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers

/-!
# Rigid transport of literal pure nearby-scale CWA

One common affine isometry transports the whole Definition 2.12 witness:
the fine and coarse indexed families, strict and doubled carrier relations,
complete-fiber cardinality uniformity, and every actual outer-John rescaled
body CWA.  No subfamily inheritance is used.

The final section records the exact remaining convention bridge from ordinary
unit-segment carriers to cropped paper carriers.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem rigid_map_add
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (point vector : Point3) :
    frame (point + vector) =
      frame point + frame.linearIsometryEquiv vector := by
  have mapped := frame.map_vadd point vector
  simpa [vadd_eq_add, add_comm] using mapped

private theorem rigid_image_image_symm
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (set : Set Point3) :
    frame.symm '' (frame '' set) = set := by
  ext point
  simp

private theorem rigid_image_subset_iff
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {first second : Set Point3} :
    frame '' first ⊆ frame '' second ↔ first ⊆ second := by
  constructor
  · intro inclusion point pointMem
    have imageMem : frame point ∈ frame '' second :=
      inclusion ⟨point, pointMem, rfl⟩
    rcases imageMem with ⟨target, targetMem, targetEq⟩
    have targetPoint : target = point :=
      frame.injective targetEq
    simpa [targetPoint] using targetMem
  · exact Set.image_mono

private theorem pureWZ2RigidImageTube_midpoint
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {rho : ℝ}
    (tube : Kakeya.DeltaTube rho) :
    wz2PaperTubeMidpoint (pureWZ2RigidImageTube frame tube) =
      frame (wz2PaperTubeMidpoint tube) := by
  rw [wz2PaperTubeMidpoint, wz2PaperTubeMidpoint]
  symm
  simpa [pureWZ2RigidImageTube] using
    rigid_map_add frame tube.base
      ((1 / 2 : ℝ) • tube.direction)

private theorem pureWZ2RigidImageTube_centeredDilatedCarrier
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (factor : ℝ)
    {rho : ℝ}
    (tube : Kakeya.DeltaTube rho) :
    wz2PaperCenteredDilatedCarrier factor
        (pureWZ2RigidImageTube frame tube) =
      frame '' wz2PaperCenteredDilatedCarrier factor tube := by
  have mapHomothety :
      ∀ source,
        AffineMap.homothety
            (frame (wz2PaperTubeMidpoint tube)) factor
            (frame source) =
          frame
            (AffineMap.homothety
              (wz2PaperTubeMidpoint tube) factor source) := by
    intro source
    simpa [AffineMap.homothety_apply,
      AffineMap.lineMap_apply] using
      (frame.toAffineEquiv.apply_lineMap
        (wz2PaperTubeMidpoint tube) source factor).symm
  ext point
  constructor
  · rintro ⟨imageSource, imageSourceMem, rfl⟩
    rw [pureWZ2RigidImageTube_carrier frame tube] at imageSourceMem
    rcases imageSourceMem with ⟨source, sourceMem, rfl⟩
    refine
      ⟨AffineMap.homothety
          (wz2PaperTubeMidpoint tube) factor source,
        ⟨source, sourceMem, rfl⟩, ?_⟩
    rw [pureWZ2RigidImageTube_midpoint,
      mapHomothety]
  · rintro ⟨sourceImage, ⟨source, sourceMem, rfl⟩, rfl⟩
    refine
      ⟨frame source, ?_, ?_⟩
    · rw [pureWZ2RigidImageTube_carrier frame tube]
      exact ⟨source, sourceMem, rfl⟩
    · rw [pureWZ2RigidImageTube_midpoint,
        mapHomothety]

private theorem pureWZ2RigidImage_fullFiberIndices
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) :
    wz2PaperOrdinaryFullFiberIndices
        (pureWZ2RigidImageFamily frame fine)
        (pureWZ2RigidImageFamily frame coarse) parent =
      wz2PaperOrdinaryFullFiberIndices fine coarse parent := by
  change
    Finset.univ.filter
        (fun source : Fin fine.card =>
          (pureWZ2RigidImageTube
              frame (fine.tube source)).carrier ⊆
            (pureWZ2RigidImageTube
              frame (coarse.tube parent)).carrier) =
      Finset.univ.filter
        (fun source : Fin fine.card =>
          (fine.tube source).carrier ⊆
            (coarse.tube parent).carrier)
  ext source
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro sourceMem
    rw [pureWZ2RigidImageTube_carrier,
      pureWZ2RigidImageTube_carrier] at sourceMem
    exact (rigid_image_subset_iff frame).mp sourceMem
  · intro sourceMem
    rw [pureWZ2RigidImageTube_carrier,
      pureWZ2RigidImageTube_carrier]
    exact (rigid_image_subset_iff frame).mpr sourceMem

private theorem pureWZ2RigidImage_dilatedFiberIndices
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (factor : ℝ)
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) :
    wz2PaperOrdinaryDilatedFiberIndices factor
        (pureWZ2RigidImageFamily frame fine)
        (pureWZ2RigidImageFamily frame coarse) parent =
      wz2PaperOrdinaryDilatedFiberIndices factor fine coarse parent := by
  change
    Finset.univ.filter
        (fun source : Fin fine.card =>
          (pureWZ2RigidImageTube
              frame (fine.tube source)).carrier ⊆
            wz2PaperCenteredDilatedCarrier factor
              (pureWZ2RigidImageTube
                frame (coarse.tube parent))) =
      Finset.univ.filter
        (fun source : Fin fine.card =>
          (fine.tube source).carrier ⊆
            wz2PaperCenteredDilatedCarrier factor
              (coarse.tube parent))
  ext source
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro sourceMem
    rw [pureWZ2RigidImageTube_carrier,
      pureWZ2RigidImageTube_centeredDilatedCarrier] at sourceMem
    exact (rigid_image_subset_iff frame).mp sourceMem
  · intro sourceMem
    rw [pureWZ2RigidImageTube_carrier,
      pureWZ2RigidImageTube_centeredDilatedCarrier]
    exact (rigid_image_subset_iff frame).mpr sourceMem

private theorem pureWZ2RigidImage_partitioningCover
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse) :
    WZ2PaperPurePartitioningCover
      (pureWZ2RigidImageFamily frame fine)
      (pureWZ2RigidImageFamily frame coarse) where
  covers source := by
    rcases cover.covers source with ⟨parent, sourceMem⟩
    refine ⟨parent, ?_⟩
    rwa [pureWZ2RigidImage_fullFiberIndices]
  doubled_fibers_disjoint first second distinct := by
    rw [pureWZ2RigidImage_dilatedFiberIndices,
      pureWZ2RigidImage_dilatedFiberIndices]
    exact cover.doubled_fibers_disjoint first second distinct

private theorem pureWZ2RigidImage_fullFibersUniform
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {C : ENNReal}
    (uniform : WZ2PaperPureFullFibersAreCUniform fine coarse C) :
    WZ2PaperPureFullFibersAreCUniform
      (pureWZ2RigidImageFamily frame fine)
      (pureWZ2RigidImageFamily frame coarse) C := by
  intro first second
  simp only [wz2PaperOrdinaryFullFiberCount]
  rw [pureWZ2RigidImage_fullFiberIndices,
    pureWZ2RigidImage_fullFiberIndices]
  exact uniform first second

private theorem pureWZ2RigidImage_essentiallyDistinct
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily rho}
    (distinct : WZ2PaperOrdinaryIsEssentiallyDistinct family) :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      (pureWZ2RigidImageFamily frame family) := by
  change
    ∀ first second : Fin family.card, first ≠ second →
      ¬(pureWZ2RigidImageTube
          frame (family.tube first)).carrier ⊆
          wz2PaperCenteredDilatedCarrier 2
            (pureWZ2RigidImageTube frame (family.tube second)) ∧
        ¬(pureWZ2RigidImageTube
          frame (family.tube second)).carrier ⊆
          wz2PaperCenteredDilatedCarrier 2
            (pureWZ2RigidImageTube frame (family.tube first))
  intro first second firstNeSecond
  rcases distinct first second firstNeSecond with
    ⟨forward, backward⟩
  constructor
  · intro inclusion
    apply forward
    rw [pureWZ2RigidImageTube_carrier,
      pureWZ2RigidImageTube_centeredDilatedCarrier] at inclusion
    exact (rigid_image_subset_iff frame).mp inclusion
  · intro inclusion
    apply backward
    rw [pureWZ2RigidImageTube_carrier,
      pureWZ2RigidImageTube_centeredDilatedCarrier] at inclusion
    exact (rigid_image_subset_iff frame).mp inclusion

private theorem rigid_image_ellipsoid
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (center : Point3)
    (linear : Point3 ≃ₗ[ℝ] Point3) :
    frame '' JohnEllipsoid.ellipsoid center linear =
      JohnEllipsoid.ellipsoid
        (frame center)
        (linear.trans
          frame.linearIsometryEquiv.toLinearEquiv) := by
  ext point
  simp only [JohnEllipsoid.ellipsoid, Set.mem_image,
    Set.mem_vadd_set]
  constructor
  · rintro
      ⟨sourcePoint,
        ⟨sourceVector,
          ⟨unitVector, unitVectorMem, sourceVectorEq⟩,
          sourcePointEq⟩,
        rfl⟩
    refine
      ⟨frame.linearIsometryEquiv sourceVector,
        ⟨unitVector, unitVectorMem, ?_⟩, ?_⟩
    · rw [← sourceVectorEq]
      rfl
    · rw [← sourcePointEq]
      simpa [vadd_eq_add, add_comm] using
        (frame.map_vadd center sourceVector).symm
  · rintro
      ⟨targetVector,
        ⟨unitVector, unitVectorMem, targetVectorEq⟩,
        pointEq⟩
    let sourceVector := linear unitVector
    let sourcePoint := center +ᵥ sourceVector
    refine
      ⟨sourcePoint,
        ⟨sourceVector,
          ⟨unitVector, unitVectorMem, rfl⟩, rfl⟩, ?_⟩
    have targetVectorValue :
        targetVector =
          frame.linearIsometryEquiv sourceVector := by
      exact targetVectorEq.symm
    calc
      frame sourcePoint =
          frame center +ᵥ
            frame.linearIsometryEquiv sourceVector := by
        simpa [sourcePoint, vadd_eq_add, add_comm] using
          frame.map_vadd center sourceVector
      _ = frame center +ᵥ targetVector := by
        rw [targetVectorValue]
      _ = point := pointEq

private theorem rigid_image_isConvexBody
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {set : Set Point3}
    (body : JohnEllipsoid.IsConvexBody set) :
    JohnEllipsoid.IsConvexBody (frame '' set) := by
  refine ⟨?_, ?_, ?_⟩
  · exact body.1.affine_image frame.toAffineMap
  · exact body.2.1.image frame.continuous
  · have interiorEq :
        interior (frame '' set) =
          frame '' interior set := by
      exact (frame.toHomeomorph.image_interior set).symm
    rw [interiorEq]
    exact body.2.2.image frame

private theorem rigid_image_isOuterJohnEllipsoid
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {set : Set Point3}
    (body : JohnEllipsoid.IsConvexBody set) :
    JohnEllipsoid.IsOuterJohnEllipsoid
      (frame '' set)
      (frame body.outerJohnEllipsoidCenter)
      (body.outerJohnEllipsoidMap.trans
        frame.linearIsometryEquiv.toLinearEquiv) := by
  let sourceCenter := body.outerJohnEllipsoidCenter
  let sourceLinear := body.outerJohnEllipsoidMap
  let targetCenter := frame sourceCenter
  let targetLinear :=
    sourceLinear.trans frame.linearIsometryEquiv.toLinearEquiv
  have sourceSpec :
      JohnEllipsoid.IsOuterJohnEllipsoid
        set sourceCenter sourceLinear :=
    body.outerJohnEllipsoid_spec
  have candidateImage :
      frame '' JohnEllipsoid.ellipsoid
          sourceCenter sourceLinear =
        JohnEllipsoid.ellipsoid
          targetCenter targetLinear :=
    rigid_image_ellipsoid
      frame sourceCenter sourceLinear
  refine ⟨?_, ?_⟩
  · rw [← candidateImage]
    exact Set.image_mono sourceSpec.1
  · intro competitorCenter competitorLinear targetContainment
    let sourceCompetitorCenter := frame.symm competitorCenter
    let sourceCompetitorLinear :=
      competitorLinear.trans
        frame.symm.linearIsometryEquiv.toLinearEquiv
    have sourceCompetitorImage :
        frame.symm ''
            JohnEllipsoid.ellipsoid
              competitorCenter competitorLinear =
          JohnEllipsoid.ellipsoid
            sourceCompetitorCenter sourceCompetitorLinear :=
      rigid_image_ellipsoid
        frame.symm competitorCenter competitorLinear
    have sourceContainment :
        set ⊆
          JohnEllipsoid.ellipsoid
            sourceCompetitorCenter sourceCompetitorLinear := by
      rw [← sourceCompetitorImage]
      intro point pointMem
      exact
        ⟨frame point,
          targetContainment ⟨point, pointMem, rfl⟩,
          frame.symm_apply_apply point⟩
    have sourceMinimal :
        volume
            (JohnEllipsoid.ellipsoid
              sourceCenter sourceLinear) ≤
          volume
            (JohnEllipsoid.ellipsoid
              sourceCompetitorCenter sourceCompetitorLinear) :=
      sourceSpec.2
        sourceCompetitorCenter sourceCompetitorLinear
        sourceContainment
    have sourceMeasurable :
        MeasurableSet
          (JohnEllipsoid.ellipsoid
            sourceCenter sourceLinear) :=
      JohnEllipsoid.ellipsoid_compact.measurableSet
    have competitorMeasurable :
        MeasurableSet
          (JohnEllipsoid.ellipsoid
            competitorCenter competitorLinear) :=
      JohnEllipsoid.ellipsoid_compact.measurableSet
    have candidateVolume :
        volume
            (JohnEllipsoid.ellipsoid
              targetCenter targetLinear) =
          volume
            (JohnEllipsoid.ellipsoid
              sourceCenter sourceLinear) := by
      rw [← candidateImage]
      exact
        Kakeya.Streamlined.AffineIsometryEquiv.volume_image
          frame
          (JohnEllipsoid.ellipsoid sourceCenter sourceLinear)
          sourceMeasurable
    have competitorVolume :
        volume
            (JohnEllipsoid.ellipsoid
              sourceCompetitorCenter sourceCompetitorLinear) =
          volume
            (JohnEllipsoid.ellipsoid
              competitorCenter competitorLinear) := by
      rw [← sourceCompetitorImage]
      exact
        Kakeya.Streamlined.AffineIsometryEquiv.volume_image
          frame.symm
          (JohnEllipsoid.ellipsoid
            competitorCenter competitorLinear)
          competitorMeasurable
    rw [candidateVolume]
    exact sourceMinimal.trans_eq competitorVolume

private theorem rigid_target_outerJohn_image
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {rho : ℝ}
    (parent : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (sourceNormalization :
      WZ2PaperAssouadUnitRescalingData parent)
    (targetNormalization :
      WZ2PaperAssouadUnitRescalingData
        (pureWZ2RigidImageTube frame parent)) :
    frame ''
        sourceNormalization.parent_convex_body.outerJohnEllipsoid =
      targetNormalization.parent_convex_body.outerJohnEllipsoid := by
  let sourceBody := sourceNormalization.parent_convex_body
  let targetBody := targetNormalization.parent_convex_body
  have carrierEq :
      (pureWZ2RigidImageTube frame parent).carrier =
        frame '' parent.carrier :=
    pureWZ2RigidImageTube_carrier frame parent
  have candidateSpec :
      JohnEllipsoid.IsOuterJohnEllipsoid
        (frame '' parent.carrier)
        (frame sourceBody.outerJohnEllipsoidCenter)
        (sourceBody.outerJohnEllipsoidMap.trans
          frame.linearIsometryEquiv.toLinearEquiv) :=
    rigid_image_isOuterJohnEllipsoid frame sourceBody
  have candidateSpecTarget :
      JohnEllipsoid.IsOuterJohnEllipsoid
        (pureWZ2RigidImageTube frame parent).carrier
        (frame sourceBody.outerJohnEllipsoidCenter)
        (sourceBody.outerJohnEllipsoidMap.trans
          frame.linearIsometryEquiv.toLinearEquiv) := by
    rw [carrierEq]
    exact candidateSpec
  have candidateEq :
      JohnEllipsoid.ellipsoid
          (frame sourceBody.outerJohnEllipsoidCenter)
          (sourceBody.outerJohnEllipsoidMap.trans
            frame.linearIsometryEquiv.toLinearEquiv) =
        targetBody.outerJohnEllipsoid :=
    targetBody.outerJohnEllipsoid_unique _ _ candidateSpecTarget
  calc
    frame '' sourceBody.outerJohnEllipsoid =
        JohnEllipsoid.ellipsoid
          (frame sourceBody.outerJohnEllipsoidCenter)
          (sourceBody.outerJohnEllipsoidMap.trans
            frame.linearIsometryEquiv.toLinearEquiv) :=
      rigid_image_ellipsoid frame
        sourceBody.outerJohnEllipsoidCenter
        sourceBody.outerJohnEllipsoidMap
    _ = targetBody.outerJohnEllipsoid := candidateEq

private noncomputable def rigid_actualJohn_coordinateChange
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {rho : ℝ}
    {parent : Kakeya.DeltaTube rho}
    (sourceNormalization :
      WZ2PaperAssouadUnitRescalingData parent)
    (targetNormalization :
      WZ2PaperAssouadUnitRescalingData
        (pureWZ2RigidImageTube frame parent)) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  (sourceNormalization.map.symm.trans frame.toAffineEquiv).trans
    targetNormalization.map

private noncomputable def rigid_fullFiberIndexEquiv
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) :
    Fin
        (wz2PaperOrdinaryFullFiberIndices
          (pureWZ2RigidImageFamily frame fine)
          (pureWZ2RigidImageFamily frame coarse) parent).card ≃
      Fin
        (wz2PaperOrdinaryFullFiberIndices fine coarse parent).card :=
  Equiv.cast <|
    congrArg Fin <|
      congrArg Finset.card <|
        pureWZ2RigidImage_fullFiberIndices frame fine coarse parent

private theorem orderIsoOfFin_cast_value
    {alpha : Type*}
    [LinearOrder alpha]
    (first second : Finset alpha)
    (setsEq : first = second)
    (index : Fin first.card) :
    ((second.orderIsoOfFin rfl)
      ((Equiv.cast
        (congrArg Fin (congrArg Finset.card setsEq))) index)).1 =
      ((first.orderIsoOfFin rfl) index).1 := by
  subst second
  rfl

private theorem rigid_fullFiberIndexEquiv_sourceIndex
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card)
    (targetIndex :
      Fin
        (wz2PaperOrdinaryFullFiberIndices
          (pureWZ2RigidImageFamily frame fine)
          (pureWZ2RigidImageFamily frame coarse) parent).card) :
    ((wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := fine) (coarse := coarse) parent)
        (rigid_fullFiberIndexEquiv
          frame fine coarse parent targetIndex)).1 =
      ((wz2PaperOrdinaryFullFiberIndexEquiv
        (fine := pureWZ2RigidImageFamily frame fine)
        (coarse := pureWZ2RigidImageFamily frame coarse) parent)
          targetIndex).1 := by
  exact
    orderIsoOfFin_cast_value
      (wz2PaperOrdinaryFullFiberIndices
        (pureWZ2RigidImageFamily frame fine)
        (pureWZ2RigidImageFamily frame coarse) parent)
      (wz2PaperOrdinaryFullFiberIndices fine coarse parent)
      (pureWZ2RigidImage_fullFiberIndices
        frame fine coarse parent)
      targetIndex

private theorem rigid_actualJohn_coordinateChange_image_set
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {rho : ℝ}
    {parent : Kakeya.DeltaTube rho}
    (sourceNormalization :
      WZ2PaperAssouadUnitRescalingData parent)
    (targetNormalization :
      WZ2PaperAssouadUnitRescalingData
        (pureWZ2RigidImageTube frame parent))
    (set : Set Point3) :
    rigid_actualJohn_coordinateChange
          frame sourceNormalization targetNormalization ''
        (sourceNormalization.map '' set) =
      targetNormalization.map '' (frame '' set) := by
  ext point
  constructor
  · rintro
      ⟨sourceNormalizedPoint,
        ⟨sourcePoint, sourcePointMem, rfl⟩, rfl⟩
    refine
      ⟨frame sourcePoint,
        ⟨sourcePoint, sourcePointMem, rfl⟩, ?_⟩
    simp [rigid_actualJohn_coordinateChange]
  · rintro
      ⟨imagePoint, ⟨sourcePoint, sourcePointMem, rfl⟩, rfl⟩
    refine
      ⟨sourceNormalization.map sourcePoint,
        ⟨sourcePoint, sourcePointMem, rfl⟩, ?_⟩
    simp [rigid_actualJohn_coordinateChange]

private theorem rigid_actualJohn_coordinateChange_inverse_volume
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {rho : ℝ}
    (parent : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (sourceNormalization :
      WZ2PaperAssouadUnitRescalingData parent)
    (targetNormalization :
      WZ2PaperAssouadUnitRescalingData
        (pureWZ2RigidImageTube frame parent))
    (targetSet : Set Point3) :
    volume
        ((rigid_actualJohn_coordinateChange
          frame sourceNormalization targetNormalization).symm ''
          targetSet) ≤
      (1 : ENNReal) * volume targetSet := by
  let coordinateChange :=
    rigid_actualJohn_coordinateChange
      frame sourceNormalization targetNormalization
  have outerImage :=
    rigid_target_outerJohn_image
      frame parent hrho sourceNormalization targetNormalization
  have sourceOuterMeasurable :
      MeasurableSet
        sourceNormalization.parent_convex_body.outerJohnEllipsoid :=
    JohnEllipsoid.ellipsoid_compact.measurableSet
  have outerVolumeEq :
      volume
          targetNormalization.parent_convex_body.outerJohnEllipsoid =
        volume
          sourceNormalization.parent_convex_body.outerJohnEllipsoid := by
    rw [← outerImage]
    exact
      Kakeya.Streamlined.AffineIsometryEquiv.volume_image
        frame
        sourceNormalization.parent_convex_body.outerJohnEllipsoid
        sourceOuterMeasurable
  have coordinateBall :
      coordinateChange ''
          Metric.closedBall (0 : Point3) 1 =
        Metric.closedBall (0 : Point3) 1 := by
    ext point
    constructor
    · rintro ⟨sourcePoint, sourcePointMem, rfl⟩
      have sourceOuterMem :
          sourceNormalization.map.symm sourcePoint ∈
            sourceNormalization.parent_convex_body.outerJohnEllipsoid := by
        have imageMem :
            sourcePoint ∈
              sourceNormalization.map ''
                sourceNormalization.parent_convex_body.outerJohnEllipsoid := by
          rwa [sourceNormalization.outerJohn_image]
        rcases imageMem with
          ⟨outerPoint, outerPointMem, outerPointEq⟩
        have outerPointValue :
            outerPoint = sourceNormalization.map.symm sourcePoint := by
          apply sourceNormalization.map.injective
          simpa using outerPointEq
        simpa [outerPointValue] using outerPointMem
      have targetOuterMem :
          frame (sourceNormalization.map.symm sourcePoint) ∈
            targetNormalization.parent_convex_body.outerJohnEllipsoid := by
        rw [← outerImage]
        exact
          ⟨sourceNormalization.map.symm sourcePoint,
            sourceOuterMem, rfl⟩
      have targetBallMem :=
        Set.mem_of_mem_of_subset targetOuterMem
          (Set.subset_def.mpr fun _ h => h)
      rw [← targetNormalization.outerJohn_image]
      exact
        ⟨frame (sourceNormalization.map.symm sourcePoint),
          targetOuterMem, rfl⟩
    · intro pointMem
      rw [← targetNormalization.outerJohn_image] at pointMem
      rcases pointMem with ⟨targetOuterPoint, targetOuterMem, rfl⟩
      rw [← outerImage] at targetOuterMem
      rcases targetOuterMem with
        ⟨sourceOuterPoint, sourceOuterMem, rfl⟩
      let sourceBallPoint :=
        sourceNormalization.map sourceOuterPoint
      have sourceBallMem :
          sourceBallPoint ∈ Metric.closedBall (0 : Point3) 1 := by
        rw [← sourceNormalization.outerJohn_image]
        exact ⟨sourceOuterPoint, sourceOuterMem, rfl⟩
      refine ⟨sourceBallPoint, sourceBallMem, ?_⟩
      simp [sourceBallPoint, coordinateChange,
        rigid_actualJohn_coordinateChange]
  have coordinateBallSymm :
      coordinateChange.symm ''
          Metric.closedBall (0 : Point3) 1 =
        Metric.closedBall (0 : Point3) 1 := by
    calc
      coordinateChange.symm ''
            Metric.closedBall (0 : Point3) 1 =
          coordinateChange.symm ''
            (coordinateChange ''
              Metric.closedBall (0 : Point3) 1) := by
        exact congrArg
          (fun set : Set Point3 => coordinateChange.symm '' set)
          coordinateBall.symm
      _ = Metric.closedBall (0 : Point3) 1 := by
        ext point
        simp
  rw [wz2PaperAffineEquiv_volume_image_eq]
  have ballPos :
      0 < volume (Metric.closedBall (0 : Point3) 1) :=
    Metric.measure_closedBall_pos volume (0 : Point3) (by norm_num)
  have ballTop :
      volume (Metric.closedBall (0 : Point3) 1) ≠ ⊤ :=
    (ProperSpace.isCompact_closedBall (0 : Point3) 1).measure_ne_top
  have determinantFactor :
      ENNReal.ofReal
          |LinearMap.det
            (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| =
        1 := by
    have volumeFormula :=
      wz2PaperAffineEquiv_volume_image_eq
        coordinateChange.symm (Metric.closedBall (0 : Point3) 1)
    rw [coordinateBallSymm] at volumeFormula
    have scaled :
        ENNReal.ofReal
              |LinearMap.det
                (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| *
            volume (Metric.closedBall (0 : Point3) 1) ≤
          1 * volume (Metric.closedBall (0 : Point3) 1) := by
      simpa using volumeFormula.symm.le
    exact
      (ENNReal.mul_le_mul_iff_left ballPos.ne' ballTop).mp scaled
      |>.antisymm <| by
        have scaledReverse :
            1 * volume (Metric.closedBall (0 : Point3) 1) ≤
              ENNReal.ofReal
                    |LinearMap.det
                      (coordinateChange.symm.linear :
                        Point3 →ₗ[ℝ] Point3)| *
                volume (Metric.closedBall (0 : Point3) 1) := by
          simpa using volumeFormula.le
        exact
          (ENNReal.mul_le_mul_iff_left ballPos.ne' ballTop).mp
            scaledReverse
  rw [determinantFactor, one_mul]

private theorem pureWZ2RigidImage_rescaledFiber
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {C : ENNReal}
    (hrho : 0 < rho)
    (parent : Fin coarse.card)
    (source :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := coarse) parent C) :
    Nonempty
      (WZ2PaperPureUnitRescaledFullFiberData
        (fine := pureWZ2RigidImageFamily frame fine)
        (coarse := pureWZ2RigidImageFamily frame coarse)
        parent C) := by
  let targetNormalization :=
    WZ2PaperAssouadUnitRescalingData.ofTube
      ((pureWZ2RigidImageFamily frame coarse).tube parent) hrho
  let sourceBodies :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := fine) (coarse := coarse) parent source.normalization
  let targetBodies :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := pureWZ2RigidImageFamily frame fine)
      (coarse := pureWZ2RigidImageFamily frame coarse)
      parent targetNormalization
  have targetCWA :
      WZ2PaperBodyConvexWolffBound targetBodies C := by
    have transported :
        WZ2PaperBodyConvexWolffBound targetBodies ((1 : ENNReal) * C) := by
      let indexEquiv :
          Fin targetBodies.card ≃ Fin sourceBodies.card :=
        rigid_fullFiberIndexEquiv frame fine coarse parent
      apply
        wz2PaperBodyConvexWolffBound_of_affineTransport
          (source := sourceBodies) (target := targetBodies)
          (rigid_actualJohn_coordinateChange
            frame source.normalization targetNormalization)
          indexEquiv
      · intro targetIndex
        let sourceIndex :=
          ((wz2PaperOrdinaryFullFiberIndexEquiv
            (fine := fine) (coarse := coarse) parent)
              (indexEquiv targetIndex)).1
        let targetSourceIndex :=
          ((wz2PaperOrdinaryFullFiberIndexEquiv
            (fine := pureWZ2RigidImageFamily frame fine)
            (coarse := pureWZ2RigidImageFamily frame coarse)
            parent) targetIndex).1
        have sourceIndexEq :
            sourceIndex = targetSourceIndex :=
          rigid_fullFiberIndexEquiv_sourceIndex
            frame fine coarse parent targetIndex
        change
          rigid_actualJohn_coordinateChange
                frame source.normalization targetNormalization ''
              (source.normalization.map ''
                (fine.tube sourceIndex).carrier) ⊆
            targetNormalization.map ''
              ((pureWZ2RigidImageFamily frame fine).tube
                targetSourceIndex).carrier
        rw [sourceIndexEq,
          pureWZ2RigidImageFamily_carrier]
        exact
          (rigid_actualJohn_coordinateChange_image_set
            frame source.normalization targetNormalization
            (fine.tube targetSourceIndex).carrier).le
      · exact
          rigid_actualJohn_coordinateChange_inverse_volume
            frame (coarse.tube parent) hrho
              source.normalization targetNormalization
      · exact source.convex_wolff
    simpa using transported
  exact
    ⟨{
      normalization := targetNormalization
      convex_wolff := targetCWA
    }⟩

private noncomputable def pureWZ2RigidImage_scaleData
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData family rho C) :
    WZ2PaperPureScaleCoverData
      (pureWZ2RigidImageFamily frame family) rho C where
  delta_pos := data.delta_pos
  rho_pos := data.rho_pos
  coarse := pureWZ2RigidImageFamily frame data.coarse
  cover := pureWZ2RigidImage_partitioningCover frame data.cover
  full_fiber_uniform :=
    pureWZ2RigidImage_fullFibersUniform
      frame data.full_fiber_uniform
  rescaledFiber parent := by
    rcases data.rescaledFiber parent with ⟨source⟩
    exact
      pureWZ2RigidImage_rescaledFiber
        (fine := family) (coarse := data.coarse)
        frame data.rho_pos parent source

private noncomputable def pureWZ2RigidImage_nearbyData
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {rho₀ : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    (data : WZ2PaperPureNearbyScaleCoverData family rho₀ C) :
    WZ2PaperPureNearbyScaleCoverData
      (pureWZ2RigidImageFamily frame family) rho₀ C where
  rho := data.rho
  requested_le := data.requested_le
  within_factor := data.within_factor
  scaleData := pureWZ2RigidImage_scaleData frame data.scaleData

/--
Literal Definition 2.12 is invariant under one common affine isometry.

The coarse family is transported pointwise.  Strict and doubled fibers are
definitionally the same finite index sets after proving the corresponding
carrier-image identities.  Each target actual-John family is obtained from
the source actual-John family by the exact normalization composition
`targetJohn ∘ frame ∘ sourceJohn⁻¹`; its inverse Jacobian is one because the
two outer-John ellipsoids are rigid images.
-/
theorem pureWZ2RigidImageFamily_pureCWA
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    {C : ENNReal}
    (source :
      WZ2PaperPureCWAAtNearbyScales family C) :
    WZ2PaperPureCWAAtNearbyScales
      (pureWZ2RigidImageFamily frame family) C := by
  refine
    ⟨source.1, source.2.1,
      pureWZ2RigidImage_essentiallyDistinct frame source.2.2.1,
      ?_⟩
  intro requested
  rcases source.2.2.2 requested with ⟨nearby⟩
  exact ⟨pureWZ2RigidImage_nearbyData frame nearby⟩

/--
The ordinary top-level CWA of the rigid image follows by first transporting
the complete literal pure nearby-scale witness.
-/
theorem pureWZ2RigidImageFamily_ordinaryTopCWA
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta loss outputLoss : ℝ}
    (lossPos : 0 < loss)
    (lossLeOne : loss ≤ 1)
    (deltaLeOne : delta ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (familyNonempty : family.Nonempty)
    (source :
      WZ2PaperPureCWAAtNearbyScales
        family (Kakeya.realRpowENN delta (-loss)))
    (scaleAbsorption :
      ∀ rho : ℝ,
        0 < rho →
        delta ≤ rho →
        rho ≤ 1 →
        Real.rpow delta loss ≤ rho →
          ENNReal.ofReal (4 / rho ^ 2) *
              Kakeya.realRpowENN delta (-loss) ≤
            Kakeya.realRpowENN delta (-outputLoss)) :
    WZ2PaperBodyConvexWolffBound
      (pureWZ2RigidImageFamily frame family).toBodyFamily
      (Kakeya.realRpowENN delta (-outputLoss)) := by
  apply
    pureWZ2_pureNearby_to_ordinaryTopCWA
      lossPos lossLeOne deltaLeOne
      (show
        (pureWZ2RigidImageFamily frame family).Nonempty
        from familyNonempty)
      (pureWZ2RigidImageFamily_pureCWA frame family source)
  exact scaleAbsorption

/--
The thinnest convention premise for the cropped top-level conclusion is the
pointwise inclusion of each ordinary rigid-image carrier in its cropped
paper carrier.  Line-class information alone does not imply this bounded
support condition.
-/
theorem pureWZ2RigidImageFamily_croppedTopCWA
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta loss outputLoss : ℝ}
    (lossPos : 0 < loss)
    (lossLeOne : loss ≤ 1)
    (deltaLeOne : delta ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (familyNonempty : family.Nonempty)
    (source :
      WZ2PaperPureCWAAtNearbyScales
        family (Kakeya.realRpowENN delta (-loss)))
    (scaleAbsorption :
      ∀ rho : ℝ,
        0 < rho →
        delta ≤ rho →
        rho ≤ 1 →
        Real.rpow delta loss ≤ rho →
          ENNReal.ofReal (4 / rho ^ 2) *
              Kakeya.realRpowENN delta (-loss) ≤
            Kakeya.realRpowENN delta (-outputLoss))
    (carrierSubset :
      ∀ index,
        ((pureWZ2RigidImageFamily frame family).tube index).carrier ⊆
          wz1PaperTubeCarrier
            ((pureWZ2RigidImageFamily frame family).tube index)) :
    WZ2PaperConvexWolffBound
      (pureWZ2RigidImageFamily frame family)
      (Kakeya.realRpowENN delta (-outputLoss)) :=
  wz2PaperOrdinaryCWA_to_paper_of_carrier_subset
    carrierSubset
    (pureWZ2RigidImageFamily_ordinaryTopCWA
      frame lossPos lossLeOne deltaLeOne familyNonempty
      source scaleAbsorption)

/--
Axis-box support supplies the exact ordinary-to-cropped carrier bridge.  The
line-class hypothesis is retained explicitly for normalization consumers,
although the counting implication itself only needs bounded support.
-/
private theorem ordinary_carrier_subset_paper_of_axisBox
    {delta : ℝ}
    (deltaNonnegative : 0 ≤ delta)
    (tube : Kakeya.DeltaTube delta)
    (axisBoxSupport :
      tube.carrier ⊆ Kakeya.Streamlined.axisBox 2 2 2) :
    tube.carrier ⊆ wz1PaperTubeCarrier tube := by
  intro point pointMem
  constructor
  · exact
      Metric.cthickening_mono
        (by linarith : delta ≤ 6 * delta)
        (tubeAxisLine tube)
        (Metric.cthickening_subset_of_subset delta
          (wz2_paper_unitSegment_subset_axisLine tube)
          pointMem)
  · exact axisBoxSupport pointMem

theorem pureWZ2RigidImageFamily_croppedTopCWA_of_axisBox
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta loss outputLoss : ℝ}
    (deltaNonnegative : 0 ≤ delta)
    (lossPos : 0 < loss)
    (lossLeOne : loss ≤ 1)
    (deltaLeOne : delta ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (familyNonempty : family.Nonempty)
    (source :
      WZ2PaperPureCWAAtNearbyScales
        family (Kakeya.realRpowENN delta (-loss)))
    (lineClass :
      WZ1PaperIsLineClass
        (pureWZ2RigidImageFamily frame family))
    (axisBoxSupport :
      ∀ index,
        ((pureWZ2RigidImageFamily frame family).tube index).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (scaleAbsorption :
      ∀ rho : ℝ,
        0 < rho →
        delta ≤ rho →
        rho ≤ 1 →
        Real.rpow delta loss ≤ rho →
          ENNReal.ofReal (4 / rho ^ 2) *
              Kakeya.realRpowENN delta (-loss) ≤
            Kakeya.realRpowENN delta (-outputLoss)) :
    WZ2PaperConvexWolffBound
      (pureWZ2RigidImageFamily frame family)
      (Kakeya.realRpowENN delta (-outputLoss)) := by
  have _ := lineClass
  apply
    pureWZ2RigidImageFamily_croppedTopCWA
      frame lossPos lossLeOne deltaLeOne familyNonempty
      source scaleAbsorption
  intro index
  exact
    ordinary_carrier_subset_paper_of_axisBox
      deltaNonnegative
      ((pureWZ2RigidImageFamily frame family).tube index)
      (axisBoxSupport index)

end Kakeya.Assouad

end
