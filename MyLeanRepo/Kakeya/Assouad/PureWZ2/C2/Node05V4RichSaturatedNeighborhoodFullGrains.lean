import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichNeighborhoodFullGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSaturatedFullLocalGrain

/-!
# Saturated full grains on the selected direct-rich neighborhood

For every side-`sqrt rho` parent already selected by the fixed-global-line
neighborhood, this module constructs the heavy local grain inside the
same-height saturation of that parent.  The selected neighborhood witness is
kept as the literal P1 normal anchor.

The resulting local graph uses the exact-slice global AD estimate only at the
Fubini height selected inside each grain.  The horizontal saturation remains
an auxiliary carrier for the normal-first argument; it is not promoted to a
tube shading and it does not replace the source used by the later incidence
graph.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

/-- Same-height saturated full grains on exactly the parents selected by the
direct-rich global-neighborhood step. -/
structure PureWZ2Node05V4RichSaturatedNeighborhoodFullGrainData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    (neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback) where
  fullGrainFor : ∀ y (_hy : y ∈ neighborhood.sample),
    PureWZ2Node05V4RichSaturatedFullLocalGrainData
      (eta := eta) pullback (neighborhood.cube y)
  fullGrain_anchor_eq : ∀ y (hy : y ∈ neighborhood.sample),
    (fullGrainFor y hy).anchor = neighborhood.witness y

namespace PureWZ2PreCommonBinGlobalGrainNeighborhoodData

/-- Construct one saturated full grain on every selected neighborhood
parent.  The single source-volume premise is independent of the runtime
parent; the parent dependence is discharged by the two balanced-cell floors. -/
theorem saturatedFullGrains
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    (neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hsourcePower :
      ((32 * Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta sigma *
            Kakeya.realRpowENN rho (2 - sigma)) *
          ENNReal.ofReal rho) *
          Kakeya.realRpowENN (4 * rhoRequested.1)
            (3 / 2 + sigma / 2 + eta) ≤
        (Kakeya.realRpowENN rhoRequested.1 3 *
            Kakeya.realRpowENN (delta / rhoRequested.1)
              (sigma + 2 * twoScale.first.rich.terminalLoss)) *
          Kakeya.realRpowENN rhoRequested.1
            (3 / 2 + sigma / 2 + twoScale.second.terminalLoss))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rhoRequested.1) (-eta)) :
    Nonempty (PureWZ2Node05V4RichSaturatedNeighborhoodFullGrainData
      (eta := eta) neighborhood) := by
  have hanchorSource : ∀ y (hy : y ∈ neighborhood.sample),
      neighborhood.witness y ∈ current.grain.shading.union := by
    intro y hy
    exact pullback.subshading.union_subset
      (neighborhood.witness_mem_pullback y hy).1
  have hanchorParent : ∀ y (hy : y ∈ neighborhood.sample),
      neighborhood.witness y ∈
        wz1PaperGridCube sqrtRequested.1 (neighborhood.cube y) := by
    intro y hy
    exact pullback.preCommonBinFinePullback_subset_parent
      (neighborhood.witness_mem_pullback y hy)
  have hsourceFloor : ∀ y (hy : y ∈ neighborhood.sample),
      Kakeya.realRpowENN (4 * rhoRequested.1)
          (3 / 2 + sigma / 2 + eta) ≤
        volume
          (pullback.sameHeightParentSaturation (neighborhood.cube y)) := by
    intro y hy
    exact pullback.sameHeightParentSaturation_volume_lower
      (neighborhood.cube_active hy) _ hsourcePower
  have hfull : ∀ y (hy : y ∈ neighborhood.sample),
      ∃ grain : PureWZ2Node05V4RichSaturatedFullLocalGrainData
          (eta := eta) pullback (neighborhood.cube y),
        grain.anchor = neighborhood.witness y := by
    intro y hy
    rcases pullback.saturatedFullLocalGrainAt
        (neighborhood.cube y) (neighborhood.cube_active hy)
        (neighborhood.witness y) (hanchorSource y hy)
        (hanchorParent y hy) hbridge hcertificateOne
        (hsourceFloor y hy) hlocalPower with
      ⟨grain, hgrainAnchor⟩
    exact ⟨grain, hgrainAnchor⟩
  let fullGrainFor : ∀ y (hy : y ∈ neighborhood.sample),
      PureWZ2Node05V4RichSaturatedFullLocalGrainData
        (eta := eta) pullback (neighborhood.cube y) :=
    fun y hy => Classical.choose (hfull y hy)
  exact ⟨{
    fullGrainFor := fullGrainFor
    fullGrain_anchor_eq := fun y hy => Classical.choose_spec (hfull y hy)
  }⟩

end PureWZ2PreCommonBinGlobalGrainNeighborhoodData

namespace PureWZ2Node05V4RichSaturatedNeighborhoodFullGrainData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback}
    (data : PureWZ2Node05V4RichSaturatedNeighborhoodFullGrainData
      (eta := eta) neighborhood)

/-- The auxiliary local graph `g` obtained from the saturated full grains.
No whole-parent or future-slab global AD hypothesis appears here. -/
theorem localGraph
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hCpower : 160 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN (4 * rhoRequested.1) (-eta))
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hPlanarSmall : 32 * Real.rpow (4 * rhoRequested.1) eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rhoRequested.1) ≤ 1)
    (habsorb :
      Real.rpow (4 * rhoRequested.1) (1 - 4 * eta / sigma) ≤
        Real.sqrt (4 * rhoRequested.1) / 14) :
    ∃ g : ℝ → ℝ,
      LipschitzOnWith 64 g Set.univ ∧
      (∀ y, |g y| ≤ 2) ∧
      ∀ y (hy : y ∈ neighborhood.sample),
        g y =
          (data.fullGrainFor y hy).normal (2 : Fin 3) /
            (data.fullGrainFor y hy).normal (0 : Fin 3) := by
  let normal : Point3 → Point3 := fun point =>
    if hpoint : point ∈ current.grain.shading.union then
      current.grain.localGrains.planeMap ⟨point, hpoint⟩ else 0
  have hanchorSource : ∀ y (hy : y ∈ neighborhood.sample),
      neighborhood.witness y ∈ current.grain.shading.union := by
    intro y hy
    exact pullback.subshading.union_subset
      (neighborhood.witness_mem_pullback y hy).1
  have hnormalEq : ∀ y (hy : y ∈ neighborhood.sample),
      (data.fullGrainFor y hy).normal =
        normal (neighborhood.witness y) := by
    intro y hy
    let grain := data.fullGrainFor y hy
    calc
      grain.normal = current.grain.localGrains.planeMap
          ⟨grain.anchor, grain.anchor_mem_source⟩ := grain.normal_eq
      _ = current.grain.localGrains.planeMap
          ⟨neighborhood.witness y, hanchorSource y hy⟩ := by
        congr 1
        apply Subtype.ext
        exact data.fullGrain_anchor_eq y hy
      _ = normal (neighborhood.witness y) := by
        simp [normal, hanchorSource y hy]
  have hnormalVertical : ∀ y ∈ neighborhood.sample,
      |normal (neighborhood.witness y) (2 : Fin 3)| ≤ 1 / 2 := by
    intro y hy
    simp only [normal, dif_pos (hanchorSource y hy)]
    exact current.grain.planeMap_vertical_bound _
  have hnormalFirst : ∀ y ∈ neighborhood.sample,
      1 / 4 ≤ |normal (neighborhood.witness y) (0 : Fin 3)| := by
    intro y hy
    let grain := data.fullGrainFor y hy
    have hfirst := grain.normal_first hbridge hsigma hsigmaOne heta hetaSigma
      (by simpa only [grain.certificateScale_eq] using hCpower)
      hcertificateOne
      (by simpa only [grain.certificateScale_eq] using hPlanarSmall)
      (by simpa only [grain.certificateScale_eq] using hrootSmall20)
      (by simpa only [grain.certificateScale_eq] using habsorb)
    rwa [hnormalEq y hy] at hfirst
  have hnormalDist : ∀ first ∈ neighborhood.sample,
      ∀ second ∈ neighborhood.sample,
        dist (normal (neighborhood.witness first))
            (normal (neighborhood.witness second)) ≤
          dist (neighborhood.witness first) (neighborhood.witness second) := by
    intro first hfirst second hsecond
    simp only [normal, dif_pos (hanchorSource first hfirst),
      dif_pos (hanchorSource second hsecond)]
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using
      current.grain.localGrains.planeMap_lipschitz.dist_le_mul
        (⟨neighborhood.witness first, hanchorSource first hfirst⟩ :
          {point : Point3 // point ∈ current.grain.shading.union})
        (⟨neighborhood.witness second, hanchorSource second hsecond⟩ :
          {point : Point3 // point ∈ current.grain.shading.union})
  rcases wz1_lemma23_local_graph_extension_of_distortion
      neighborhood.sample neighborhood.witness normal
      hnormalVertical hnormalFirst hnormalDist neighborhood.witness_dist with
    ⟨g, hgLip, hgBound, hgEq⟩
  refine ⟨g, hgLip, hgBound, ?_⟩
  intro y hy
  rw [hnormalEq y hy]
  exact hgEq y hy

end PureWZ2Node05V4RichSaturatedNeighborhoodFullGrainData

end Kakeya.Assouad

end
