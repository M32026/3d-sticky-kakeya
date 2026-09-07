import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSameHeightSaturation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichFullLocalGrain

/-!
# Direct-rich full local grains on the same-height saturation

The heavy-fibre source is the horizontal saturation supported only at actual
post-source heights.  Its volume is paid by the two dependent balanced-cell
floors, its local projection is transferred from the P1 plane map, and its
global projection is controlled by the P1 exact slice at the very same height.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

structure PureWZ2Node05V4RichSaturatedFullLocalGrainData
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta rho eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (parent : WZ2PaperCellIndex) where
  parent_active : parent ∈ twoScale.secondBalancedCover.activeCells
  anchor : Point3
  anchor_mem_source : anchor ∈ current.grain.shading.union
  anchor_mem_parent : anchor ∈ wz1PaperGridCube sqrtRequested.1 parent
  normal : Point3
  normal_eq :
    normal = current.grain.localGrains.planeMap
      ⟨anchor, anchor_mem_source⟩
  certificateScale : ℝ := 4 * rhoRequested.1
  certificateScale_eq : certificateScale = 4 * rhoRequested.1
  localConstant : ENNReal :=
    160 * Kakeya.realRpowENN delta (-inputLoss)
  localConstant_eq :
    localConstant = 160 * Kakeya.realRpowENN delta (-inputLoss)
  saturatedSource : Set Point3 := pullback.sameHeightParentSaturation parent
  saturatedSource_eq :
    saturatedSource = pullback.sameHeightParentSaturation parent
  saturatedSource_measurable : MeasurableSet saturatedSource
  saturatedSource_nonempty : saturatedSource.Nonempty
  saturatedSource_volume_lower :
    Kakeya.realRpowENN certificateScale
        (3 / 2 + sigma / 2 + eta) ≤ volume saturatedSource
  fiber :
    WZ1Lemma23ProjectionHeavyFiberInSource
      certificateScale sigma localConstant normal anchor saturatedSource
  grain_volume :
    Kakeya.realRpowENN certificateScale (2 + 2 * eta) ≤
      volume fiber.grain

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta rho eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)

/-- Construct the almost-full local grain on one same-height saturated parent. -/
theorem saturatedFullLocalGrainAt
    (parent : WZ2PaperCellIndex)
    (hparent : parent ∈ twoScale.secondBalancedCover.activeCells)
    (anchor : Point3)
    (hanchorSource : anchor ∈ current.grain.shading.union)
    (hanchorParent : anchor ∈ wz1PaperGridCube sqrtRequested.1 parent)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rhoRequested.1)
          (3 / 2 + sigma / 2 + eta) ≤
        volume (pullback.sameHeightParentSaturation parent))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rhoRequested.1) (-eta)) :
    ∃ data : PureWZ2Node05V4RichSaturatedFullLocalGrainData
        (eta := eta) pullback parent,
      data.anchor = anchor := by
  let certificateScale := 4 * rhoRequested.1
  let localConstant : ENNReal :=
    160 * Kakeya.realRpowENN delta (-inputLoss)
  let saturatedSource := pullback.sameHeightParentSaturation parent
  let normal := current.grain.localGrains.planeMap ⟨anchor, hanchorSource⟩
  have hrhoRequested : 0 < rhoRequested.1 :=
    twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hrho : 0 < rho := by simpa only [pullback.rhoRequested_eq] using hrhoRequested
  have hroot : 0 < sqrtRequested.1 :=
    twoScale.secondSticky.coarse_extremal.delta_pos
  have hcertificate : 0 < certificateScale := by
    dsimp only [certificateScale]
    positivity
  have hcertificateOne' : certificateScale ≤ 1 := by
    simpa only [certificateScale] using hcertificateOne
  have hsqrtCertificate : Real.sqrt certificateScale = 2 * sqrtRequested.1 := by
    dsimp only [certificateScale]
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt (4 : ℝ) = 2 by norm_num,
      ← twoScale.sqrtRequested_eq]
  have hsaturatedMeas : MeasurableSet saturatedSource :=
    pullback.sameHeightParentSaturation_measurable parent
  have hsaturatedNonempty : saturatedSource.Nonempty := by
    have hpositive : 0 < volume saturatedSource := by
      have htarget : 0 < Kakeya.realRpowENN certificateScale
          (3 / 2 + sigma / 2 + eta) :=
        ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hcertificate _)
      exact htarget.trans_le hsourceFloor
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hpositive
    simpa using hpositive
  have hsaturatedParent : saturatedSource ⊆
      wz1PaperGridCube sqrtRequested.1 parent :=
    pullback.sameHeightParentSaturation_subset_parent
  have hsaturatedBall : saturatedSource ⊆
      Metric.closedBall anchor (Real.sqrt certificateScale) := by
    intro point hpoint
    rw [hsqrtCertificate, Metric.mem_closedBall]
    exact le_of_lt (wz1_paper_grid_cube_diameter_lt_two_rho
      hroot (hsaturatedParent hpoint) hanchorParent)
  have hnormalUnit : ‖normal‖ = 1 :=
    current.grain.localGrains.planeMap_unit _
  have hdeltaCertificate : delta ≤ certificateScale := by
    calc
      delta ≤ rhoRequested.1 := rhoRequested.property.1
      _ ≤ 4 * rhoRequested.1 := by nlinarith
  have hsourceAD :
      IsADSet1
        (scalarProjection normal
          (current.grain.shading.union ∩
            Metric.closedBall anchor (Real.sqrt certificateScale)))
        certificateScale (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
    have hliteral := current.grain.localGrains.local_ad certificateScale
      hdeltaCertificate hcertificateOne' ⟨anchor, hanchorSource⟩
    simpa only [normal] using
      hbridge.1 _ certificateScale (1 - sigma)
        (Kakeya.realRpowENN delta (-inputLoss))
        (scalarProjection_paperShading_subset_Icc
          (current.grain.localGrains.planeMap_unit _) Set.inter_subset_left)
        hliteral
  have hprojectionThick : scalarProjection normal saturatedSource ⊆
      Metric.cthickening (2 * rhoRequested.1)
        (scalarProjection normal
          (current.grain.shading.union ∩
            Metric.closedBall anchor (Real.sqrt certificateScale))) := by
    rintro value ⟨point, hpoint, rfl⟩
    change point ∈ pullback.sameHeightParentSaturation parent at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointSat⟩
    have hcellData := Finset.mem_filter.mp hcell
    rcases wz1PaperGridCubeSameHeightSaturation_exists_source_same_height
        (pullback.sameHeightSourceCell_subset_cube cell) hpointSat with
      ⟨sourcePoint, hsourcePoint, _hheight⟩
    have hsourceCurrent : sourcePoint ∈ current.grain.shading.union :=
      pullback.subshading.union_subset hsourcePoint.1.1
    have hsourceParent : sourcePoint ∈
        wz1PaperGridCube sqrtRequested.1 parent := by
      have hpointParent := pullback.standardSecondParent_cell_subset
        hcellData.1 hsourcePoint.2
      simpa only [hcellData.2] using hpointParent
    have hsourceBall : sourcePoint ∈
        Metric.closedBall anchor (Real.sqrt certificateScale) := by
      rw [hsqrtCertificate, Metric.mem_closedBall]
      exact le_of_lt (wz1_paper_grid_cube_diameter_lt_two_rho
        hroot hsourceParent hanchorParent)
    have hsourceProjection : inner ℝ sourcePoint normal ∈
        scalarProjection normal
          (current.grain.shading.union ∩
            Metric.closedBall anchor (Real.sqrt certificateScale)) :=
      ⟨sourcePoint, ⟨hsourceCurrent, hsourceBall⟩, rfl⟩
    have hpointRho : point ∈ wz1PaperGridCube rho cell :=
      wz1PaperGridCubeSameHeightSaturation_subset_cube rho cell
        (pullback.sameHeightSourceCell cell) hpointSat
    have hpointSourceDist : dist point sourcePoint ≤ 2 * rho :=
      le_of_lt (wz1_paper_grid_cube_diameter_lt_two_rho hrho
        hpointRho hsourcePoint.2)
    have hprojectionDist :
        dist (inner ℝ point normal) (inner ℝ sourcePoint normal) ≤
          2 * rhoRequested.1 := by
      have hinner := abs_real_inner_le_norm (point - sourcePoint) normal
      have hdist : dist point sourcePoint ≤ 2 * rhoRequested.1 := by
        simpa only [pullback.rhoRequested_eq] using hpointSourceDist
      rw [Real.dist_eq]
      have heq : inner ℝ point normal - inner ℝ sourcePoint normal =
          inner ℝ (point - sourcePoint) normal := by
        simp [inner_sub_left]
      rw [heq]
      exact hinner.trans (by simpa [hnormalUnit, dist_eq_norm] using hdist)
    exact Metric.mem_cthickening_of_dist_le _ _ _ _
      hsourceProjection hprojectionDist
  have hsaturatedCoarse : saturatedSource ⊆
      twoScale.secondRefinedFineShading.union :=
    pullback.sameHeightParentSaturation_subset_secondRefined parent
  have hprojectionBounded : scalarProjection normal saturatedSource ⊆
      Set.Icc (-4 : ℝ) 4 :=
    scalarProjection_paperShading_subset_Icc hnormalUnit hsaturatedCoarse
  have hsourceADRaw := hsourceAD.generalized_thickening
    hprojectionThick hprojectionBounded hcertificate
      (by positivity : 0 < 2 * rhoRequested.1)
  have hratio : (2 * rhoRequested.1) / certificateScale = (1 / 2 : ℝ) := by
    dsimp only [certificateScale]
    field_simp [hrhoRequested.ne']
    norm_num
  have hsaturatedAD : IsADSet1 (scalarProjection normal saturatedSource)
      certificateScale (1 - sigma) localConstant := by
    rw [hratio] at hsourceADRaw
    have hceil : Nat.ceil (1 / 2 : ℝ) = 1 := by
      rw [Nat.ceil_eq_iff] <;> norm_num
    rw [hceil] at hsourceADRaw
    convert hsourceADRaw using 1 <;>
      dsimp only [localConstant] <;> norm_num <;> ring
  have hlocalTop : localConstant ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])
  rcases wz1_lemma23_projection_heavy_fiber_in_source
      localConstant normal anchor saturatedSource hnormalUnit
      hsaturatedMeas hsaturatedNonempty hsaturatedBall hsaturatedAD
      hcertificate hcertificateOne' hlocalTop with ⟨fiber⟩
  have hlocalOne : 1 ≤ localConstant := hsaturatedAD.2.2.2.1
  have hgrainVolume :
      Kakeya.realRpowENN certificateScale (2 + 2 * eta) ≤
        volume fiber.grain :=
    fiber.grain_volume_of_source_lower hcertificate hlocalOne
      (by simpa only [localConstant, certificateScale] using hlocalPower)
      (by simpa only [certificateScale, saturatedSource] using hsourceFloor)
  exact ⟨{
    parent_active := hparent
    anchor := anchor
    anchor_mem_source := hanchorSource
    anchor_mem_parent := hanchorParent
    normal := normal
    normal_eq := rfl
    certificateScale := certificateScale
    certificateScale_eq := rfl
    localConstant := localConstant
    localConstant_eq := rfl
    saturatedSource := saturatedSource
    saturatedSource_eq := rfl
    saturatedSource_measurable := hsaturatedMeas
    saturatedSource_nonempty := hsaturatedNonempty
    saturatedSource_volume_lower := by
      simpa only [certificateScale, saturatedSource] using hsourceFloor
    fiber := fiber
    grain_volume := hgrainVolume }, rfl⟩

end PureWZ2Node05V4RichTwoScaleCellPullbackData

namespace PureWZ2Node05V4RichSaturatedFullLocalGrainData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta rho eta : ℝ}
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
    {parent : WZ2PaperCellIndex}
    (data : PureWZ2Node05V4RichSaturatedFullLocalGrainData
      (eta := eta) pullback parent)

def graphLeft : ℝ :=
  max (-1 : ℝ)
    (((parent.2.2 : ℝ) + 1) * sqrtRequested.1 -
      Real.sqrt data.certificateScale)

theorem parentHeightWindow_subset_unit
    (hparent : parent ∈ twoScale.secondBalancedCover.activeCells) :
    Set.Icc
        ((parent.2.2 : ℝ) * sqrtRequested.1)
        (((parent.2.2 : ℝ) + 1) * sqrtRequested.1) ⊆
      Set.Icc (-1 : ℝ) 1 := by
  have hroot : 0 < sqrtRequested.1 :=
    twoScale.secondSticky.coarse_extremal.delta_pos
  have hheightIco : Set.Ico
      ((parent.2.2 : ℝ) * sqrtRequested.1)
      (((parent.2.2 : ℝ) + 1) * sqrtRequested.1) ⊆
      Set.Icc (-1 : ℝ) 1 := by
    intro height hheight
    let point : Point3 :=
      point3 (((parent.1 : ℝ) + 1 / 2) * sqrtRequested.1)
        (((parent.2.1 : ℝ) + 1 / 2) * sqrtRequested.1) height
    have hpointCell :
        point ∈ wz1PaperGridCube sqrtRequested.1 parent := by
      rw [wz1PaperGridCube_eq_Ico hroot parent]
      change
        (parent.1 : ℝ) * sqrtRequested.1 ≤ point 0 ∧
        point 0 < ((parent.1 : ℝ) + 1) * sqrtRequested.1 ∧
        (parent.2.1 : ℝ) * sqrtRequested.1 ≤ point 1 ∧
        point 1 < ((parent.2.1 : ℝ) + 1) * sqrtRequested.1 ∧
        (parent.2.2 : ℝ) * sqrtRequested.1 ≤ point 2 ∧
        point 2 < ((parent.2.2 : ℝ) + 1) * sqrtRequested.1
      have hp0 :
          point 0 = ((parent.1 : ℝ) + 1 / 2) * sqrtRequested.1 := by
        simp [point, point3]
      have hp1 :
          point 1 = ((parent.2.1 : ℝ) + 1 / 2) * sqrtRequested.1 := by
        simp [point, point3]
      have hp2 : point 2 = height := by simp [point, point3]
      rw [hp0, hp1, hp2]
      constructor
      · nlinarith
      constructor
      · nlinarith
      constructor
      · nlinarith
      constructor
      · nlinarith
      constructor
      · exact hheight.1
      · exact hheight.2
    have hcoarse : point ∈ twoScale.secondFinalCoarseShading.union := by
      rw [twoScale.secondBalancedCover.coarse_union_eq]
      exact Set.mem_iUnion₂.mpr
        ⟨parent, hparent, hpointCell⟩
    have hbox := shading_union_subset_axisBox hcoarse
    have hp2 : point (2 : Fin 3) = height := by simp [point, point3]
    rw [← hp2]
    simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
  have hnondegenerate :
      (parent.2.2 : ℝ) * sqrtRequested.1 <
        ((parent.2.2 : ℝ) + 1) * sqrtRequested.1 := by
    nlinarith
  rw [← closure_Ico hnondegenerate.ne]
  exact closure_minimal hheightIco isClosed_Icc

theorem graphWindow_subset_unit
    (hcertificateOne : data.certificateScale ≤ 1) :
    Set.Ico data.graphLeft
        (data.graphLeft + Real.sqrt data.certificateScale) ⊆
      Set.Icc (-1 : ℝ) 1 := by
  have hroot : 0 < sqrtRequested.1 :=
    twoScale.secondSticky.coarse_extremal.delta_pos
  have hparentHeightWindow := parentHeightWindow_subset_unit data.parent_active
  intro z hz
  have hleft : (-1 : ℝ) ≤ data.graphLeft := le_max_left _ _
  have hright : data.graphLeft + Real.sqrt data.certificateScale ≤ 1 := by
    dsimp only [graphLeft]
    by_cases hcase : (-1 : ℝ) ≥
        (((parent.2.2 : ℝ) + 1) * sqrtRequested.1 -
          Real.sqrt data.certificateScale)
    · rw [max_eq_left hcase]
      have hsqrtOne := Real.sqrt_le_one.mpr hcertificateOne
      linarith
    · rw [max_eq_right (le_of_not_ge hcase)]
      have hparentRight : ((parent.2.2 : ℝ) + 1) * sqrtRequested.1 ≤ 1 :=
        (hparentHeightWindow ⟨by linarith, le_rfl⟩).2
      linarith
  exact ⟨hleft.trans hz.1, hz.2.le.trans hright⟩

def toGeometry
    (hcertificateOne : data.certificateScale ≤ 1) :
    WZ1Lemma23FullLocalGrainGeometryGeneralized
      data.certificateScale eta current.grain.globalGrains.slope := by
  have hroot : 0 < sqrtRequested.1 :=
    twoScale.secondSticky.coarse_extremal.delta_pos
  have hsqrtCertificate :
      Real.sqrt data.certificateScale = 2 * sqrtRequested.1 := by
    rw [data.certificateScale_eq, Real.sqrt_mul (by norm_num),
      show Real.sqrt (4 : ℝ) = 2 by norm_num, ← twoScale.sqrtRequested_eq]
  have hgrainHeight : ∀ point ∈ data.fiber.grain,
      point (2 : Fin 3) ∈ Set.Ico data.graphLeft
        (data.graphLeft + Real.sqrt data.certificateScale) := by
    intro point hpoint
    have hsaturated : point ∈ pullback.sameHeightParentSaturation parent := by
      rw [← data.saturatedSource_eq]
      exact data.fiber.grain_in_source hpoint
    have hparent := pullback.sameHeightParentSaturation_subset_parent hsaturated
    rw [wz1PaperGridCube_eq_Ico hroot parent] at hparent
    have hparentHeightWindow := parentHeightWindow_subset_unit data.parent_active
    have hleftBase : data.graphLeft ≤ (parent.2.2 : ℝ) * sqrtRequested.1 := by
      dsimp only [graphLeft]
      apply max_le
      · exact (hparentHeightWindow
          ⟨le_rfl, by nlinarith [hroot]⟩).1
      · rw [hsqrtCertificate]
        nlinarith
    refine ⟨hleftBase.trans hparent.2.2.2.2.1, ?_⟩
    have hright : ((parent.2.2 : ℝ) + 1) * sqrtRequested.1 ≤
        data.graphLeft + Real.sqrt data.certificateScale := by
      have hmax := le_max_right (-1 : ℝ)
        (((parent.2.2 : ℝ) + 1) * sqrtRequested.1 -
          Real.sqrt data.certificateScale)
      dsimp only [graphLeft]
      linarith
    exact hparent.2.2.2.2.2.trans_le hright
  have hwindow := data.graphWindow_subset_unit hcertificateOne
  exact
    { grain := data.fiber.grain
      grain_measurable := data.fiber.grain_measurable
      grain_finite := data.fiber.grain_finite
      heightLeft := data.graphLeft
      grain_height := hgrainHeight
      grain_volume := data.grain_volume
      center := data.anchor
      normal := data.normal
      localProjectionCenter := data.fiber.center
      normal_unit := by
        rw [data.normal_eq]
        exact current.grain.localGrains.planeMap_unit _
      normal_vertical := by
        rw [data.normal_eq]
        exact current.grain.planeMap_vertical_bound _
      grain_square := data.fiber.grain_square
      grain_local_strip := data.fiber.grain_local_strip
      slope_small := fun z hz =>
        current.grain.globalGrains.slope_bound z (hwindow hz) }

theorem normal_first
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hCpower : 160 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN data.certificateScale (-eta))
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hPlanarSmall : 32 * Real.rpow data.certificateScale eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt data.certificateScale ≤ 1)
    (habsorb : Real.rpow data.certificateScale (1 - 4 * eta / sigma) ≤
      Real.sqrt data.certificateScale / 14) :
    1 / 4 ≤ |data.normal (0 : Fin 3)| := by
  have hcertificateOne' : data.certificateScale ≤ 1 := by
    simpa only [data.certificateScale_eq] using hcertificateOne
  have hconstantTop :
      (160 * Kakeya.realRpowENN delta (-inputLoss) : ENNReal) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN])
  have hcertificatePos : 0 < data.certificateScale := by
    rw [data.certificateScale_eq]
    have hrhoRequested : 0 < rhoRequested.1 :=
      twoScale.first.publicSticky.coarse_extremal.delta_pos
    positivity
  change 1 / 4 ≤
    |(data.toGeometry hcertificateOne').normal (0 : Fin 3)|
  apply wz1_lemma23_full_grain_normal_first_component_generalized_of_fubini
    data.certificateScale sigma eta
      (160 * Kakeya.realRpowENN delta (-inputLoss))
      current.grain.globalGrains.slope
      hcertificatePos hcertificateOne'
      hsigma hsigmaOne heta hetaSigma hconstantTop hCpower
      hPlanarSmall hrootSmall20 habsorb
      (data.toGeometry hcertificateOne')
  intro z hz _hslice
  have hzUnit := data.graphWindow_subset_unit hcertificateOne' hz
  refine ⟨scalarProjection
      (globalGrainDirection (current.grain.globalGrains.slope z))
      (horizontalSlice data.saturatedSource z), ?_, ?_⟩
  · simpa only [data.saturatedSource_eq, data.certificateScale_eq,
      pullback.rhoRequested_eq] using
      pullback.sameHeightParentSaturation_exactAD hbridge
        (by simpa only [pullback.rhoRequested_eq] using hcertificateOne)
        parent z hzUnit
  · rintro value ⟨point, hpoint, rfl⟩
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    have hsource := data.fiber.grain_in_source hlift
    refine ⟨point3 (point 0) (point 1) z,
      ⟨hsource, by simp [point3]⟩, ?_⟩
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ, point3]

end PureWZ2Node05V4RichSaturatedFullLocalGrainData

end Kakeya.Assouad

end
