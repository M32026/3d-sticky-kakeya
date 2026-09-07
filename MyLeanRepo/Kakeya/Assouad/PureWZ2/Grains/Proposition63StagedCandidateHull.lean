import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSpatialHull
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSpatialPropertyThreePullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteIntervalGridOneScaleLocalAD
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CroppedExtremal

/-!
# Extremality transport through the common spatial hull

This file packages the common transport used after a staged candidate has
been constructed inside the current shading.  The common spatial hull has
the candidate's union, at least the candidate's mass, and restores all
current tube memberships at surviving points.  Consequently, candidate
extremality transports without changing the loss.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

/-- For a fixed source shading, the common spatial hull depends on its
candidate only through the candidate's shaded union. -/
theorem paperCommonSpatialHull_eq_of_union_eq
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    {first second : WZ1PaperTubeShading family}
    (hunion : first.union = second.union) :
    paperCommonSpatialHull source first =
      paperCommonSpatialHull source second := by
  have hcarrier :
      (paperCommonSpatialHull source first).carrier =
        (paperCommonSpatialHull source second).carrier := by
    funext index
    simp only [paperCommonSpatialHull]
    rw [hunion]
  cases hfirst : paperCommonSpatialHull source first with
  | mk carrierFirst measurableFirst subsetFirst =>
      cases hsecond : paperCommonSpatialHull source second with
      | mk carrierSecond measurableSecond subsetSecond =>
          have hcarrier' : carrierFirst = carrierSecond := by
            simpa only [hfirst, hsecond] using hcarrier
          subst carrierSecond
          rfl

/-- A cubical extremal candidate remains extremal after restoring all current
tube memberships over its shaded union.  Cubicality of `current` is necessary
because the hull can be strictly larger than the candidate carrierwise. -/
theorem paperCommonSpatialHull_extremal
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {current candidate : WZ1PaperTubeShading family}
    (hsub : PaperIsSubshading candidate current)
    (hcurrentCubical : WZ1PaperIsCubicalShading current)
    (hcandidateCubical : WZ1PaperIsCubicalShading candidate)
    (hcandidateExtremal :
      WZ2PaperCroppedIsExtremal sigma loss family candidate) :
    WZ2PaperCroppedIsExtremal sigma loss family
      (paperCommonSpatialHull current candidate) := by
  refine
    { delta_pos := hcandidateExtremal.delta_pos
      delta_le_one := hcandidateExtremal.delta_le_one
      nonempty := hcandidateExtremal.nonempty
      cwa_nearby_scales := hcandidateExtremal.cwa_nearby_scales
      cubical :=
        paperCommonSpatialHull_cubical
          hcurrentCubical hcandidateCubical
      dense := hcandidateExtremal.dense.trans
        (paperCommonSpatialHull_mass_lower hsub)
      volume_upper := ?_ }
  rw [paperCommonSpatialHull_union hsub]
  exact hcandidateExtremal.volume_upper

/-- An interval-covering certificate transports to the common spatial hull
because the hull and the candidate have exactly the same shaded union. -/
theorem paperCommonSpatialHull_intervalCovering
    {delta queryScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {current candidate : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    {resolutionScale windowScale : NNReal}
    {constant : ENNReal}
    (hsub : PaperIsSubshading candidate current)
    (hcover : PureWZ2IntervalCoveringAt candidate planeMap queryScale
      resolutionScale windowScale constant) :
    PureWZ2IntervalCoveringAt
      (paperCommonSpatialHull current candidate) planeMap queryScale
      resolutionScale windowScale constant := by
  intro point center
  have hpointCandidate : (point : Point3) ∈ candidate.union := by
    rw [← paperCommonSpatialHull_union hsub]
    exact point.property
  have hcandidateCover := hcover ⟨point, hpointCandidate⟩ center
  simpa only [paperCommonSpatialHull_union hsub] using hcandidateCover

/-- A plane-map variation estimate transports to the common spatial hull
without changing either scale, again by equality of shaded unions. -/
theorem paperCommonSpatialHull_planeVariation
    {delta spatialScale variationScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {current candidate : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    (hsub : PaperIsSubshading candidate current)
    (hvariation : ∀ first ∈ candidate.union,
      ∀ second ∈ candidate.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) :
    ∀ first ∈ (paperCommonSpatialHull current candidate).union,
      ∀ second ∈ (paperCommonSpatialHull current candidate).union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale := by
  rw [paperCommonSpatialHull_union hsub]
  exact hvariation

/-- The fine Property-Three pullback depends on the coarse shading only
through its shaded union. -/
theorem propertyThreeFinePullbackShading_eq_of_union_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    {first second : WZ1PaperTubeShading coarse}
    (hunion : first.union = second.union) :
    propertyThreeFinePullbackShading cover fineShading first =
      propertyThreeFinePullbackShading cover fineShading second := by
  have hcarrier :
      (propertyThreeFinePullbackShading cover fineShading first).carrier =
        (propertyThreeFinePullbackShading cover fineShading second).carrier := by
    funext index
    rw [propertyThreeFinePullbackShading_carrier,
      propertyThreeFinePullbackShading_carrier, hunion]
  cases hfirst : propertyThreeFinePullbackShading cover fineShading first with
  | mk carrierFirst measurableFirst subsetFirst =>
      cases hsecond :
          propertyThreeFinePullbackShading cover fineShading second with
      | mk carrierSecond measurableSecond subsetSecond =>
          have hcarrier' : carrierFirst = carrierSecond := by
            simpa only [hfirst, hsecond] using hcarrier
          subst carrierSecond
          rfl

/-- For a fixed sticky witness and source shading, the ambient common hull
also depends on the coarse Property-Three shading only through its union. -/
theorem ambientPropertyThreeCommonHull_eq_of_union_eq
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    {first second : WZ1PaperTubeShading sticky.coarse}
    (hunion : first.union = second.union) :
    ambientPropertyThreeCommonHull sticky first =
      ambientPropertyThreeCommonHull sticky second := by
  have hpullback := propertyThreeFinePullbackShading_eq_of_union_eq
    sticky.cover sticky.refined hunion
  simp only [ambientPropertyThreeCommonHull, ambientPropertyThreePullback]
  rw [hpullback]

end Kakeya.Assouad.PureWZ2

end
