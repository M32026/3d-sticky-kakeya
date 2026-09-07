import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSecondStageSource
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.WZ1.GeneralizedThickening
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ProjectionHeavyFiberInSource
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23FullGrainNormalBound

/-!
# Full local grains from the direct-rich second balanced cover

The volume carrier is the genuine first-coarse shading inside one active
side-`sqrt rho` cell.  Its normal and local AD certificate are pulled from a
genuine point of the original `delta`-source.  The construction runs at the
constant-weakened scale `4 * rho`, exactly as in the paper-faithful
heterogeneous WZ Lemma 5.3 infrastructure.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

structure PureWZ2Node05V4RichFullLocalGrainData
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
    {witnesses : PureWZ2Node05V4RichCoarseCellWitnessData twoScale}
    {parent : WZ2PaperCellIndex}
    (source : PureWZ2Node05V4RichSecondStageSourceData
      (parent := parent) pullback witnesses) where
  anchor : Point3
  anchor_mem_source : anchor ∈ current.grain.shading.union
  anchor_mem_parent :
    anchor ∈ wz1PaperGridCube sqrtRequested.1 parent
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
  fiber :
    WZ1Lemma23ProjectionHeavyFiberInSource
      certificateScale sigma localConstant
        normal anchor source.fullSource
  source_volume_lower :
    Kakeya.realRpowENN certificateScale
        (3 / 2 + sigma / 2 + eta) ≤ volume source.fullSource
  grain_volume :
    Kakeya.realRpowENN certificateScale (2 + 2 * eta) ≤
      volume fiber.grain

namespace PureWZ2Node05V4RichSecondStageSourceData

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
    {witnesses : PureWZ2Node05V4RichCoarseCellWitnessData twoScale}
    {parent : WZ2PaperCellIndex}
    (source : PureWZ2Node05V4RichSecondStageSourceData
      (parent := parent) pullback witnesses)

/-- Construct an almost-full local grain at a specified genuine P1 anchor in
the same second-cover parent.  This is the form used by the fixed-line global
neighborhood, whose already selected witness must remain the literal anchor. -/
theorem fullLocalGrainAt
    (anchor : Point3)
    (hanchorSource : anchor ∈ current.grain.shading.union)
    (hanchorParent :
      anchor ∈ wz1PaperGridCube sqrtRequested.1 parent)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rhoRequested.1)
          (3 / 2 + sigma / 2 + eta) ≤
        Kakeya.realRpowENN rhoRequested.1
          (3 / 2 + sigma / 2 + twoScale.second.terminalLoss))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rhoRequested.1) (-eta)) :
    ∃ data : PureWZ2Node05V4RichFullLocalGrainData
        (eta := eta) source, data.anchor = anchor := by
  let certificateScale := 4 * rhoRequested.1
  let localConstant : ENNReal :=
    160 * Kakeya.realRpowENN delta (-inputLoss)
  let normal := current.grain.localGrains.planeMap ⟨anchor, hanchorSource⟩
  have hrho : 0 < rhoRequested.1 :=
    twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hcertificate : 0 < certificateScale := by
    dsimp only [certificateScale]
    positivity
  have hdeltaCertificate : delta ≤ certificateScale := by
    calc
      delta ≤ rhoRequested.1 := rhoRequested.property.1
      _ ≤ 4 * rhoRequested.1 := by nlinarith
  have hsqrtCertificate :
      Real.sqrt certificateScale = 2 * sqrtRequested.1 := by
    dsimp only [certificateScale]
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt (4 : ℝ) = 2 by norm_num,
      ← twoScale.sqrtRequested_eq]
  have hnormalUnit : ‖normal‖ = 1 :=
    current.grain.localGrains.planeMap_unit _
  have hsourceAD :
      IsADSet1
        (scalarProjection normal
          (current.grain.shading.union ∩
            Metric.closedBall anchor (Real.sqrt certificateScale)))
        certificateScale (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
    have hliteral := current.grain.localGrains.local_ad certificateScale
      hdeltaCertificate hcertificateOne ⟨anchor, hanchorSource⟩
    simpa only [normal] using
      hbridge.1 _ certificateScale (1 - sigma)
        (Kakeya.realRpowENN delta (-inputLoss))
        (scalarProjection_paperShading_subset_Icc
          (current.grain.localGrains.planeMap_unit _) Set.inter_subset_left)
        hliteral
  have hprojectionThick :
      scalarProjection normal source.fullSource ⊆
        Metric.cthickening (2 * rhoRequested.1)
          (scalarProjection normal
            (current.grain.shading.union ∩
              Metric.closedBall anchor (Real.sqrt certificateScale))) := by
    rintro value ⟨point, hpoint, rfl⟩
    let finePoint := witnesses.witness (source.ownerCell point)
    have hfineSource : finePoint ∈ current.grain.shading.union :=
      ⟨witnesses.sourceIndex (source.ownerCell point),
        witnesses.witness_mem_source (source.ownerCell point)
          (source.owner_active point hpoint)⟩
    have hfineBall :
        finePoint ∈ Metric.closedBall anchor (Real.sqrt certificateScale) := by
      rw [hsqrtCertificate]
      rw [Metric.mem_closedBall]
      exact le_of_lt
        (wz1_paper_grid_cube_diameter_lt_two_rho
          twoScale.secondSticky.coarse_extremal.delta_pos
          (source.owner_witness_mem_parent point hpoint) hanchorParent)
    have hfineProjection : inner ℝ finePoint normal ∈
        scalarProjection normal
          (current.grain.shading.union ∩
            Metric.closedBall anchor (Real.sqrt certificateScale)) :=
      ⟨finePoint, ⟨hfineSource, hfineBall⟩, rfl⟩
    have hpointFine : dist point finePoint ≤ 2 * rhoRequested.1 :=
      le_of_lt (wz1_paper_grid_cube_diameter_lt_two_rho hrho
        (source.point_mem_owner point hpoint)
        (witnesses.witness_mem_cell (source.ownerCell point)
          (source.owner_active point hpoint)))
    have hprojectionDist :
        dist (inner ℝ point normal) (inner ℝ finePoint normal) ≤
          2 * rhoRequested.1 := by
      rw [Real.dist_eq]
      have heq :
          inner ℝ point normal - inner ℝ finePoint normal =
            inner ℝ (point - finePoint) normal := by
        simp [inner_sub_left]
      rw [heq]
      exact (abs_real_inner_le_norm (point - finePoint) normal).trans
        (by simpa [hnormalUnit, dist_eq_norm] using hpointFine)
    exact Metric.mem_cthickening_of_dist_le _ _ _ _
      hfineProjection hprojectionDist
  have hprojectionBounded :
      scalarProjection normal source.fullSource ⊆ Set.Icc (-4 : ℝ) 4 :=
    scalarProjection_paperShading_subset_Icc hnormalUnit
      source.fullSource_subset_first_coarse
  have hsourceADRaw := hsourceAD.generalized_thickening
    hprojectionThick hprojectionBounded hcertificate
      (by positivity : 0 < 2 * rhoRequested.1)
  have hratio :
      (2 * rhoRequested.1) / certificateScale = (1 / 2 : ℝ) := by
    dsimp only [certificateScale]
    field_simp [hrho.ne']
    norm_num
  have hsourceADCoarse :
      IsADSet1 (scalarProjection normal source.fullSource)
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
      localConstant normal anchor source.fullSource hnormalUnit
      source.fullSource_measurable source.fullSource_nonempty
      (by
        intro point hpoint
        have hpointParent :
            point ∈ wz1PaperGridCube sqrtRequested.1 parent := by
          rw [source.fullSource_eq] at hpoint
          exact hpoint.2
        rw [hsqrtCertificate, Metric.mem_closedBall]
        exact le_of_lt
          (wz1_paper_grid_cube_diameter_lt_two_rho
            twoScale.secondSticky.coarse_extremal.delta_pos
            hpointParent hanchorParent))
      hsourceADCoarse hcertificate hcertificateOne hlocalTop with
    ⟨fiber⟩
  have hsourceLower :
      Kakeya.realRpowENN certificateScale
          (3 / 2 + sigma / 2 + eta) ≤ volume source.fullSource := by
    calc
      _ ≤ Kakeya.realRpowENN rhoRequested.1
          (3 / 2 + sigma / 2 + twoScale.second.terminalLoss) := by
            simpa only [certificateScale] using hsourceFloor
      _ ≤ volume source.fullSource := source.fullSource_rho_power_lower
  have hlocalOne : 1 ≤ localConstant := hsourceADCoarse.2.2.2.1
  have hgrainVolume :
      Kakeya.realRpowENN certificateScale (2 + 2 * eta) ≤
        volume fiber.grain :=
    fiber.grain_volume_of_source_lower hcertificate hlocalOne
      (by simpa only [localConstant, certificateScale] using hlocalPower)
      hsourceLower
  refine
    ⟨{ certificateScale := certificateScale
       certificateScale_eq := rfl
       anchor := anchor
       anchor_mem_source := hanchorSource
       anchor_mem_parent := hanchorParent
       normal := normal
       normal_eq := rfl
       localConstant := localConstant
       localConstant_eq := rfl
       fiber := fiber
       source_volume_lower := hsourceLower
       grain_volume := hgrainVolume }, rfl⟩

/-- Backward-compatible constructor using the canonical first-cell witness
chosen by `secondStageSourceAt`. -/
theorem fullLocalGrain
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rhoRequested.1)
          (3 / 2 + sigma / 2 + eta) ≤
        Kakeya.realRpowENN rhoRequested.1
          (3 / 2 + sigma / 2 + twoScale.second.terminalLoss))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rhoRequested.1) (-eta)) :
    Nonempty (PureWZ2Node05V4RichFullLocalGrainData
      (eta := eta) source) := by
  rcases source.fullLocalGrainAt
      (witnesses.witness source.anchorCell)
      ⟨witnesses.sourceIndex source.anchorCell,
        witnesses.witness_mem_source source.anchorCell source.anchor_active⟩
      source.anchor_witness_mem_parent hbridge hcertificateOne
        hsourceFloor hlocalPower with ⟨data, _⟩
  exact ⟨data⟩

end PureWZ2Node05V4RichSecondStageSourceData

namespace PureWZ2Node05V4RichFullLocalGrainData

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
    {witnesses : PureWZ2Node05V4RichCoarseCellWitnessData twoScale}
    {parent : WZ2PaperCellIndex}
    {source : PureWZ2Node05V4RichSecondStageSourceData
      (parent := parent) pullback witnesses}
    (data : PureWZ2Node05V4RichFullLocalGrainData
      (eta := eta) source)

/-- Left endpoint of the only height window on which the WZ Lemma 5.3
full-grain input consumes global slice AD. -/
def graphLeft : ℝ :=
  max (-1 : ℝ)
    (source.heightLeft + sqrtRequested.1 - Real.sqrt data.certificateScale)

theorem graphWindow_subset_unit
    (hcertificateOne : data.certificateScale ≤ 1) :
    Set.Ico data.graphLeft
        (data.graphLeft + Real.sqrt data.certificateScale) ⊆
      Set.Icc (-1 : ℝ) 1 := by
  have hroot : 0 < sqrtRequested.1 :=
    twoScale.secondSticky.coarse_extremal.delta_pos
  have hsourceWindowClosed :
      Set.Icc source.heightLeft (source.heightLeft + sqrtRequested.1) ⊆
        Set.Icc (-1 : ℝ) 1 := by
    have hnondegenerate :
        source.heightLeft < source.heightLeft + sqrtRequested.1 := by linarith
    rw [← closure_Ico hnondegenerate.ne]
    exact closure_minimal source.height_window isClosed_Icc
  intro z hz
  have hleft : (-1 : ℝ) ≤ data.graphLeft := le_max_left _ _
  have hright : data.graphLeft + Real.sqrt data.certificateScale ≤ 1 := by
    dsimp only [graphLeft]
    by_cases hcase : (-1 : ℝ) ≥
        source.heightLeft + sqrtRequested.1 - Real.sqrt data.certificateScale
    · rw [max_eq_left hcase]
      have hsqrtOne := Real.sqrt_le_one.mpr hcertificateOne
      linarith
    · rw [max_eq_right (le_of_not_ge hcase)]
      have hsourceRight : source.heightLeft + sqrtRequested.1 ≤ 1 :=
        (hsourceWindowClosed ⟨by linarith [hroot], le_rfl⟩).2
      linarith
  exact ⟨hleft.trans hz.1, hz.2.le.trans hright⟩

/-- The direct-rich full grain before any global exact-slice certificate is
attached.  This is the input used by the Fubini-selected-height normal-first
interface. -/
def toFullLocalGrainGeometry
    (hcertificateOne : data.certificateScale ≤ 1) :
    WZ1Lemma23FullLocalGrainGeometryGeneralized
      data.certificateScale eta current.grain.globalGrains.slope := by
  let root := sqrtRequested.1
  let graphLeft := data.graphLeft
  have hgraphLeftEq : graphLeft =
      max (-1 : ℝ)
        (source.heightLeft + root - Real.sqrt data.certificateScale) := rfl
  have hroot : 0 < root := twoScale.secondSticky.coarse_extremal.delta_pos
  have hsqrtCertificate :
      Real.sqrt data.certificateScale = 2 * root := by
    rw [data.certificateScale_eq, Real.sqrt_mul (by norm_num),
      show Real.sqrt (4 : ℝ) = 2 by norm_num, ← twoScale.sqrtRequested_eq]
  have hsourceWindowClosed :
      Set.Icc source.heightLeft (source.heightLeft + root) ⊆
        Set.Icc (-1 : ℝ) 1 := by
    have hnondegenerate :
        source.heightLeft < source.heightLeft + root := by linarith
    rw [← closure_Ico hnondegenerate.ne]
    exact closure_minimal source.height_window isClosed_Icc
  have hgrainHeight :
      ∀ point ∈ data.fiber.grain,
        point (2 : Fin 3) ∈
          Set.Ico graphLeft
            (graphLeft + Real.sqrt data.certificateScale) := by
    intro point hpoint
    have hp := source.source_height point (data.fiber.grain_in_source hpoint)
    have hminusOne : (-1 : ℝ) ≤ source.heightLeft :=
      (hsourceWindowClosed ⟨le_rfl, by linarith [hroot]⟩).1
    have hsecond :
        source.heightLeft + root - Real.sqrt data.certificateScale ≤
          source.heightLeft := by
      rw [hsqrtCertificate]
      linarith
    have hleft : graphLeft ≤ source.heightLeft :=
      hgraphLeftEq.trans_le (max_le hminusOne hsecond)
    refine ⟨hleft.trans hp.1, ?_⟩
    have hright : source.heightLeft + root ≤
        graphLeft + Real.sqrt data.certificateScale := by
      have hmax := le_max_right (-1 : ℝ)
        (source.heightLeft + root - Real.sqrt data.certificateScale)
      rw [← hgraphLeftEq] at hmax
      linarith
    exact hp.2.trans_le hright
  have hgraphWindow :
      Set.Ico graphLeft (graphLeft + Real.sqrt data.certificateScale) ⊆
        Set.Icc (-1 : ℝ) 1 := by
    simpa only [graphLeft] using data.graphWindow_subset_unit hcertificateOne
  exact
    { grain := data.fiber.grain
      grain_measurable := data.fiber.grain_measurable
      grain_finite := data.fiber.grain_finite
      heightLeft := graphLeft
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
        current.grain.globalGrains.slope_bound z (hgraphWindow hz) }

/-- Package the direct-rich coarse local grain for the closed WZ Lemma 5.3
normal-tilt argument.  Global AD is required only on the actual height window
of this grain, rather than on the whole ambient interval. -/
def toFullLocalGrainInputOnWindow
    (C : ENNReal)
    (hcertificateOne : data.certificateScale ≤ 1)
    (hglobalAD : ∀ z ∈ Set.Ico data.graphLeft
        (data.graphLeft + Real.sqrt data.certificateScale),
      IsADSet1
        (scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope z))
          (horizontalSlice source.fullSource z))
        data.certificateScale (1 - sigma) C) :
    WZ1Lemma23FullLocalGrainInputGeneralized
      data.certificateScale sigma eta C
        current.grain.globalGrains.slope := by
  let root := sqrtRequested.1
  let graphLeft := data.graphLeft
  have hgraphLeftEq : graphLeft =
      max (-1 : ℝ)
        (source.heightLeft + root - Real.sqrt data.certificateScale) := rfl
  have hroot : 0 < root := twoScale.secondSticky.coarse_extremal.delta_pos
  have hsqrtCertificate :
      Real.sqrt data.certificateScale = 2 * root := by
    rw [data.certificateScale_eq, Real.sqrt_mul (by norm_num),
      show Real.sqrt (4 : ℝ) = 2 by norm_num, ← twoScale.sqrtRequested_eq]
  have hsourceWindowClosed :
      Set.Icc source.heightLeft (source.heightLeft + root) ⊆
        Set.Icc (-1 : ℝ) 1 := by
    have hnondegenerate :
        source.heightLeft < source.heightLeft + root := by linarith
    rw [← closure_Ico hnondegenerate.ne]
    exact closure_minimal source.height_window isClosed_Icc
  have hgrainHeight :
      ∀ point ∈ data.fiber.grain,
        point (2 : Fin 3) ∈
          Set.Ico graphLeft
            (graphLeft + Real.sqrt data.certificateScale) := by
    intro point hpoint
    have hp := source.source_height point (data.fiber.grain_in_source hpoint)
    have hminusOne : (-1 : ℝ) ≤ source.heightLeft :=
      (hsourceWindowClosed ⟨le_rfl, by linarith [hroot]⟩).1
    have hsecond :
        source.heightLeft + root - Real.sqrt data.certificateScale ≤
          source.heightLeft := by
      rw [hsqrtCertificate]
      linarith
    have hleft : graphLeft ≤ source.heightLeft :=
      hgraphLeftEq.trans_le (max_le hminusOne hsecond)
    refine ⟨hleft.trans hp.1, ?_⟩
    have hright : source.heightLeft + root ≤
        graphLeft + Real.sqrt data.certificateScale := by
      have hmax := le_max_right (-1 : ℝ)
        (source.heightLeft + root - Real.sqrt data.certificateScale)
      rw [← hgraphLeftEq] at hmax
      linarith
    exact hp.2.trans_le hright
  have hgraphWindow :
      Set.Ico graphLeft (graphLeft + Real.sqrt data.certificateScale) ⊆
        Set.Icc (-1 : ℝ) 1 := by
    simpa only [graphLeft] using data.graphWindow_subset_unit hcertificateOne
  exact
    { grain := data.fiber.grain
      grain_measurable := data.fiber.grain_measurable
      grain_finite := data.fiber.grain_finite
      heightLeft := graphLeft
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
        current.grain.globalGrains.slope_bound z (hgraphWindow hz)
      projected := fun z =>
        scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope z))
          (horizontalSlice source.fullSource z)
      globalAD := hglobalAD
      global_projection_sub := by
        intro z _hz
        rintro value ⟨point, hpoint, rfl⟩
        have hlift : point3 (point 0) (point 1) z ∈ data.fiber.grain :=
          wz1Lemma23_mem_planarSlice_iff.mp hpoint
        have hsource := data.fiber.grain_in_source hlift
        refine ⟨point3 (point 0) (point 1) z,
          ⟨hsource, by simp [point3]⟩, ?_⟩
        change inner ℝ (point3 (point 0) (point 1) z)
            (globalGrainDirection (current.grain.globalGrains.slope z)) =
          point 0 + current.grain.globalGrains.slope z * point 1
        rw [PiLp.inner_apply]
        simp [Fin.sum_univ_succ, globalGrainDirection, point3] }

/-- Compatibility wrapper for callers that already have global AD on the
whole paper height interval. -/
def toFullLocalGrainInput
    (C : ENNReal)
    (hcertificateOne : data.certificateScale ≤ 1)
    (hglobalAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope z))
          (horizontalSlice twoScale.first.finalCoarseShading.union z))
        data.certificateScale (1 - sigma) C) :
    WZ1Lemma23FullLocalGrainInputGeneralized
      data.certificateScale sigma eta C
        current.grain.globalGrains.slope := by
  apply data.toFullLocalGrainInputOnWindow C hcertificateOne
  intro z hz
  apply (hglobalAD z (data.graphWindow_subset_unit hcertificateOne hz)).mono
  · rintro value ⟨point, hpoint, rfl⟩
    refine ⟨point, ⟨source.fullSource_subset_first_coarse hpoint.1, hpoint.2⟩, rfl⟩

/-- The direct-rich local grain has a quantitatively horizontal normal once
global AD is supplied on its actual selected-parent height window. -/
theorem normal_firstOfFubini
    (C : ENNReal)
    (hglobalAt :
      ∀ z (hz : z ∈ Set.Ico data.graphLeft
          (data.graphLeft + Real.sqrt data.certificateScale)),
        Kakeya.realRpowENN data.certificateScale (3 / 2 + 2 * eta) ≤
            volume (wz1Lemma23PlanarSlice data.fiber.grain z) →
        ∃ projected : Set ℝ,
          IsADSet1 projected data.certificateScale (1 - sigma) C ∧
          (fun point : Point2 => point 0 +
              current.grain.globalGrains.slope z * point 1) ''
              wz1Lemma23PlanarSlice data.fiber.grain z ⊆ projected)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hCtop : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN data.certificateScale (-eta))
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hPlanarSmall : 32 * Real.rpow data.certificateScale eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt data.certificateScale ≤ 1)
    (habsorb :
      Real.rpow data.certificateScale (1 - 4 * eta / sigma) ≤
        Real.sqrt data.certificateScale / 14) :
    1 / 4 ≤ |data.normal (0 : Fin 3)| := by
  have hcertificatePos : 0 < data.certificateScale := by
    rw [data.certificateScale_eq]
    exact mul_pos (by norm_num)
      twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hcertificateOne' : data.certificateScale ≤ 1 := by
    rw [data.certificateScale_eq]
    exact hcertificateOne
  exact wz1_lemma23_full_grain_normal_first_component_generalized_of_fubini
    data.certificateScale sigma eta C current.grain.globalGrains.slope
    hcertificatePos hcertificateOne' hsigma hsigmaOne heta hetaSigma
    hCtop hCpower hPlanarSmall hrootSmall20 habsorb
    (data.toFullLocalGrainGeometry hcertificateOne') hglobalAt

/-- The direct-rich local grain has a quantitatively horizontal normal once
global AD is supplied on its actual selected-parent height window. -/
theorem normal_firstOnWindow
    (C : ENNReal)
    (hglobalAD : ∀ z ∈ Set.Ico data.graphLeft
        (data.graphLeft + Real.sqrt data.certificateScale),
      IsADSet1
        (scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope z))
          (horizontalSlice source.fullSource z))
        data.certificateScale (1 - sigma) C)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hCtop : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN data.certificateScale (-eta))
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hPlanarSmall : 32 * Real.rpow data.certificateScale eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt data.certificateScale ≤ 1)
    (habsorb :
      Real.rpow data.certificateScale (1 - 4 * eta / sigma) ≤
        Real.sqrt data.certificateScale / 14) :
    1 / 4 ≤ |data.normal (0 : Fin 3)| := by
  apply data.normal_firstOfFubini C ?_ hsigma hsigmaOne heta hetaSigma
    hCtop hCpower hcertificateOne hPlanarSmall hrootSmall20 habsorb
  intro z hz _hslice
  refine ⟨scalarProjection
      (globalGrainDirection (current.grain.globalGrains.slope z))
      (horizontalSlice source.fullSource z), hglobalAD z hz, ?_⟩
  rintro value ⟨point, hpoint, rfl⟩
  have hlift : point3 (point 0) (point 1) z ∈ data.fiber.grain :=
    wz1Lemma23_mem_planarSlice_iff.mp hpoint
  have hsource := data.fiber.grain_in_source hlift
  refine ⟨point3 (point 0) (point 1) z,
    ⟨hsource, by simp [point3]⟩, ?_⟩
  change inner ℝ (point3 (point 0) (point 1) z)
      (globalGrainDirection (current.grain.globalGrains.slope z)) =
    point 0 + current.grain.globalGrains.slope z * point 1
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_succ, globalGrainDirection, point3]

/-- Compatibility wrapper from whole first-coarse exact-slice AD. -/
theorem normal_first
    (C : ENNReal)
    (hglobalAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope z))
          (horizontalSlice twoScale.first.finalCoarseShading.union z))
        data.certificateScale (1 - sigma) C)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hCtop : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN data.certificateScale (-eta))
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hPlanarSmall : 32 * Real.rpow data.certificateScale eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt data.certificateScale ≤ 1)
    (habsorb :
      Real.rpow data.certificateScale (1 - 4 * eta / sigma) ≤
        Real.sqrt data.certificateScale / 14) :
    1 / 4 ≤ |data.normal (0 : Fin 3)| := by
  apply data.normal_firstOnWindow C ?_ hsigma hsigmaOne heta hetaSigma
    hCtop hCpower hcertificateOne hPlanarSmall hrootSmall20 habsorb
  intro z hz
  have hcertificateOne' : data.certificateScale ≤ 1 := by
    rw [data.certificateScale_eq]
    exact hcertificateOne
  apply (hglobalAD z (data.graphWindow_subset_unit hcertificateOne' hz)).mono
  rintro value ⟨point, hpoint, rfl⟩
  refine ⟨point, ⟨source.fullSource_subset_first_coarse hpoint.1, hpoint.2⟩, rfl⟩

end PureWZ2Node05V4RichFullLocalGrainData

end Kakeya.Assouad

end
