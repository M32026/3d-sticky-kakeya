import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BallProjectionLargeScaleAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperADScaleRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RelaxedLocalGrainData

/-!
# Every-scale local AD from one critical Property-(P) scale

One Property-(P) refinement is enough for all local query scales.  Below the
critical scale, shrink the spatial ball and refine the minimum AD scale.
Above the critical scale, use the diameter of the query ball directly.  Both
arguments stay on the same shading, so no independent refinements are
intersected.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set

/-- Points in a cropped paper shading lie in the fixed box, hence in the
radius-three ball. -/
private lemma paperShading_point_norm_le_three
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {point : Point3}
    (hpoint : point ∈ shading.union) :
    ‖point‖ ≤ 3 := by
  rcases hpoint with ⟨index, hindex⟩
  have hcarrier := shading.subset_body index hindex
  have hbox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 := hcarrier.2
  have hcoordinates :
      |point 0| ≤ 1 ∧ |point 1| ≤ 1 ∧ |point 2| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hbox
  have hnormSquare :
      ‖point‖ ^ 2 = point 0 ^ 2 + point 1 ^ 2 + point 2 ^ 2 := by
    have h := EuclideanSpace.real_norm_sq_eq point
    simpa [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] using h
  have hzero : point 0 ^ 2 ≤ 1 := by
    nlinarith [abs_le.mp hcoordinates.1]
  have hone : point 1 ^ 2 ≤ 1 := by
    nlinarith [abs_le.mp hcoordinates.2.1]
  have htwo : point 2 ^ 2 ≤ 1 := by
    nlinarith [abs_le.mp hcoordinates.2.2]
  have hnormNonnegative : 0 ≤ ‖point‖ := norm_nonneg _
  nlinarith [hnormSquare]

/-- Scalar projection of any subset of a paper shading onto a unit vector is
contained in `[-4,4]`. -/
private lemma scalarProjection_paper_bounded
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {plane : Point3}
    (hplane : ‖plane‖ = 1)
    (set : Set ℝ)
    (hset : set ⊆ scalarProjection plane shading.union) :
    set ⊆ Set.Icc (-4 : ℝ) 4 := by
  intro value hvalue
  rcases hset hvalue with ⟨point, hpoint, rfl⟩
  have hinner : |inner ℝ point plane| ≤ ‖point‖ * ‖plane‖ :=
    abs_real_inner_le_norm point plane
  have hbound : |inner ℝ point plane| ≤ 4 := by
    calc
      |inner ℝ point plane| ≤ ‖point‖ * ‖plane‖ := hinner
      _ = ‖point‖ := by rw [hplane, mul_one]
      _ ≤ 3 := paperShading_point_norm_le_three hpoint
      _ ≤ 4 := by norm_num
  exact abs_le.mp hbound

/-- Extend a critical-scale paper AD estimate to every query scale in
`[delta,1]`.  The two quantitative costs are exposed explicitly. -/
theorem local_projection_ad_all_scales_of_critical
    {delta sigma criticalScale outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (hplaneUnit : ∀ point, ‖planeMap point‖ = 1)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma < 1)
    (houtputLoss : 0 < outputLoss)
    (hcriticalPos : 0 < criticalScale)
    (hcriticalOne : criticalScale ≤ 1)
    (sourceConstant : ENNReal)
    (hcritical : ∀ point : {point : Point3 // point ∈ shading.union},
      PureWZ2PaperADSet1
        (scalarProjection (planeMap point)
          (shading.union ∩ Metric.closedBall (point : Point3)
            (Real.sqrt criticalScale)))
        criticalScale (1 - sigma) sourceConstant)
    (hsmallCost :
      10 * ((10 * sourceConstant) *
          ENNReal.ofReal (10 * criticalScale / delta)) ≤
        Kakeya.realRpowENN delta (-outputLoss))
    (hlargeEndpoint :
      3 * (2 / Real.sqrt criticalScale) ^ sigma ≤
        delta ^ (-outputLoss)) :
    ∀ queryScale : ℝ, delta ≤ queryScale → queryScale ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt queryScale)))
          queryScale (1 - sigma)
          (Kakeya.realRpowENN delta (-outputLoss)) := by
  intro queryScale hdeltaQuery hqueryOne point
  have hqueryPos : 0 < queryScale := hdelta.trans_le hdeltaQuery
  have htargetTop : Kakeya.realRpowENN delta (-outputLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  by_cases hqueryCritical : queryScale ≤ criticalScale
  · have hbounded :
        scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt criticalScale)) ⊆
          Set.Icc (-4 : ℝ) 4 := by
      apply scalarProjection_paper_bounded (hplaneUnit point)
      intro value hvalue
      rcases hvalue with ⟨source, hsource, rfl⟩
      exact ⟨source, hsource.1, rfl⟩
    have hratio :
        10 * criticalScale / queryScale ≤
          10 * criticalScale / delta := by
      have hcriticalNonnegative : 0 ≤ 10 * criticalScale := by positivity
      exact div_le_div_of_nonneg_left hcriticalNonnegative hdelta
        hdeltaQuery
    have hcostMono :
        10 * ((10 * sourceConstant) *
            ENNReal.ofReal (10 * criticalScale / queryScale)) ≤
          10 * ((10 * sourceConstant) *
            ENNReal.ofReal (10 * criticalScale / delta)) := by
      gcongr
    have hcost :
        10 * ((10 * sourceConstant) *
            ENNReal.ofReal (10 * criticalScale / queryScale)) ≤
          Kakeya.realRpowENN delta (-outputLoss) := by
      exact hcostMono.trans hsmallCost
    exact local_projection_ad_below_critical_scale_absorb
      hcriticalPos hcriticalOne hqueryPos hqueryCritical hbounded
      (hcritical point) hcost htargetTop
  · have hcriticalQuery : criticalScale < queryScale := lt_of_not_ge hqueryCritical
    have hsqrtCriticalPos : 0 < Real.sqrt criticalScale :=
      Real.sqrt_pos.mpr hcriticalPos
    have hsqrtQueryPos : 0 < Real.sqrt queryScale :=
      Real.sqrt_pos.mpr hqueryPos
    have hsqrtMono : Real.sqrt criticalScale ≤ Real.sqrt queryScale :=
      Real.sqrt_le_sqrt hcriticalQuery.le
    have hratio : 2 / Real.sqrt queryScale ≤
        2 / Real.sqrt criticalScale := by
      exact div_le_div_of_nonneg_left (by norm_num) hsqrtCriticalPos
        hsqrtMono
    have hpower :
        (2 / Real.sqrt queryScale) ^ sigma ≤
          (2 / Real.sqrt criticalScale) ^ sigma := by
      exact Real.rpow_le_rpow (by positivity) hratio hsigma.le
    have hendpoint :
        3 * (2 / Real.sqrt queryScale) ^ sigma ≤
          delta ^ (-outputLoss) :=
      (mul_le_mul_of_nonneg_left hpower (by norm_num)).trans
        hlargeEndpoint
    exact ball_projection_large_scale_ad
      hdelta hdeltaOne hqueryPos hqueryOne houtputLoss hsigma hsigmaOne
      (hplaneUnit point) (fun _ hpoint => hpoint.2) hendpoint

/-- Package the preceding scale split as the final local-grain structure. -/
noncomputable def localGrainData_of_critical
    {delta sigma criticalScale outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (hplaneLipschitz : LipschitzWith 1 planeMap)
    (hplaneUnit : ∀ point, ‖planeMap point‖ = 1)
    (hplaneIncidence : ∀ index point,
      ∀ hpoint : point ∈ shading.carrier index,
        |inner ℝ (family.tube index).direction
          (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ delta)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma < 1)
    (houtputLoss : 0 < outputLoss)
    (hcriticalPos : 0 < criticalScale)
    (hcriticalOne : criticalScale ≤ 1)
    (sourceConstant : ENNReal)
    (hcritical : ∀ point : {point : Point3 // point ∈ shading.union},
      PureWZ2PaperADSet1
        (scalarProjection (planeMap point)
          (shading.union ∩ Metric.closedBall (point : Point3)
            (Real.sqrt criticalScale)))
        criticalScale (1 - sigma) sourceConstant)
    (hsmallCost :
      10 * ((10 * sourceConstant) *
          ENNReal.ofReal (10 * criticalScale / delta)) ≤
        Kakeya.realRpowENN delta (-outputLoss))
    (hlargeEndpoint :
      3 * (2 / Real.sqrt criticalScale) ^ sigma ≤
        delta ^ (-outputLoss)) :
    PureWZ2LocalGrainData shading sigma
      (Kakeya.realRpowENN delta (-outputLoss)) where
  planeMap := planeMap
  planeMap_lipschitz := hplaneLipschitz
  planeMap_unit := hplaneUnit
  planeMap_incidence := hplaneIncidence
  local_ad := local_projection_ad_all_scales_of_critical
    planeMap hplaneUnit hdelta hdeltaOne hsigma hsigmaOne houtputLoss
    hcriticalPos hcriticalOne sourceConstant hcritical hsmallCost
    hlargeEndpoint

/-- Arbitrary-Lipschitz version of `localGrainData_of_critical`.  Lemma 4.12
does not normalize the plane-map Lipschitz coefficient; Proposition 6.3 pays
for that only in its final mild rescaling. -/
noncomputable def relaxedLocalGrainData_of_critical
    {delta sigma criticalScale outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {L : NNReal}
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (hplaneLipschitz : LipschitzWith L planeMap)
    (hplaneUnit : ∀ point, ‖planeMap point‖ = 1)
    (hplaneIncidence : ∀ index point,
      ∀ hpoint : point ∈ shading.carrier index,
        |inner ℝ (family.tube index).direction
          (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ delta)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma < 1)
    (houtputLoss : 0 < outputLoss)
    (hcriticalPos : 0 < criticalScale)
    (hcriticalOne : criticalScale ≤ 1)
    (sourceConstant : ENNReal)
    (hcritical : ∀ point : {point : Point3 // point ∈ shading.union},
      PureWZ2PaperADSet1
        (scalarProjection (planeMap point)
          (shading.union ∩ Metric.closedBall (point : Point3)
            (Real.sqrt criticalScale)))
        criticalScale (1 - sigma) sourceConstant)
    (hsmallCost :
      10 * ((10 * sourceConstant) *
          ENNReal.ofReal (10 * criticalScale / delta)) ≤
        Kakeya.realRpowENN delta (-outputLoss))
    (hlargeEndpoint :
      3 * (2 / Real.sqrt criticalScale) ^ sigma ≤
        delta ^ (-outputLoss)) :
    PureWZ2RelaxedLocalGrainData shading sigma
      (Kakeya.realRpowENN delta (-outputLoss)) L where
  planeMap := planeMap
  planeMap_lipschitz := hplaneLipschitz
  planeMap_unit := hplaneUnit
  planeMap_incidence := hplaneIncidence
  local_ad := local_projection_ad_all_scales_of_critical
    planeMap hplaneUnit hdelta hdeltaOne hsigma hsigmaOne houtputLoss
    hcriticalPos hcriticalOne sourceConstant hcritical hsmallCost
    hlargeEndpoint

end Kakeya.Assouad.PureWZ2

end
