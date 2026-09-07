import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightGraphEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSaturatedNeighborhoodCarrier
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSourceVolumePopularHeightAssignment

/-!
# Anchored graph carrier on the joint-height source envelope

The production graph is the graph-scale cell partition of the complete
source-`delta`-cell envelope selected before any graph operation.  Its union
is exactly that envelope and its global AD bound is inherited monotonically
from the same current source.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

namespace PureWZ2Node05V4RichSourceVolumePopularHeightData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
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
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {volumePopular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex}
    {B₀ threshold : ENNReal}
    {block : volumePopular.JointHeightCommonBinData B₀ threshold}
    (envelope : volumePopular.JointHeightGraphEnvelopeData block)

namespace JointHeightGraphEnvelopeData

def jointGraphScale
    (_envelope : volumePopular.JointHeightGraphEnvelopeData block) : ℝ :=
  256 * rho

theorem jointGraphScale_pos : 0 < envelope.jointGraphScale := by
  unfold jointGraphScale
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  positivity

def jointCarrierCells : Finset WZ2PaperCellIndex :=
  (wz1Lemma23BoundedCells envelope.jointGraphScale
      envelope.jointGraphScale_pos).filter fun cell =>
    (envelope.shading.union ∩
      wz1Lemma23Cell envelope.jointGraphScale cell).Nonempty

abbrev JointCarrierCell :=
  {cell : WZ2PaperCellIndex // cell ∈ envelope.jointCarrierCells}

def jointCarrierCellTube
    (cell : envelope.JointCarrierCell) :
    Kakeya.DeltaTube envelope.jointGraphScale where
  base := Classical.choose
      (Finset.mem_filter.mp cell.property).2 -
    (1 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  direction := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  direction_unit := by simp

theorem jointCarrierCell_subset_tube
    (cell : envelope.JointCarrierCell) :
    wz1Lemma23Cell envelope.jointGraphScale cell.1 ⊆
      (envelope.jointCarrierCellTube cell).carrier := by
  intro point hpoint
  let tube := envelope.jointCarrierCellTube cell
  let center := Classical.choose (Finset.mem_filter.mp cell.property).2
  have hcenterCell :
      center ∈ wz1Lemma23Cell envelope.jointGraphScale cell.1 :=
    (Classical.choose_spec (Finset.mem_filter.mp cell.property).2).2
  have hcenter : center ∈ Kakeya.unitSegment tube.base tube.direction := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    dsimp [tube, center, jointCarrierCellTube]
    module
  apply Metric.mem_cthickening_of_dist_le point center
    envelope.jointGraphScale
    (Kakeya.unitSegment tube.base tube.direction) hcenter
  apply wz1Lemma23_same_cell_dist envelope.jointGraphScale_pos
  exact hpoint.trans hcenterCell.symm

def jointCarrierFamily : Kakeya.Streamlined.TubeFamily
    envelope.jointGraphScale where
  card := envelope.jointCarrierCells.card
  tube index := envelope.jointCarrierCellTube
    (envelope.jointCarrierCells.equivFin.symm index)

def jointCarrierShading : Kakeya.Streamlined.TubeShading
    envelope.jointCarrierFamily where
  carrier index :=
    envelope.shading.union ∩
      wz1Lemma23Cell envelope.jointGraphScale
        ((envelope.jointCarrierCells.equivFin.symm index).1)
  measurable_carrier _ :=
    (measurableSet_shading_union envelope.shading).inter
      (wz1Lemma23Cell_measurable envelope.jointGraphScale_pos _)
  subset_body index := fun _ hpoint =>
    envelope.jointCarrierCell_subset_tube
      (envelope.jointCarrierCells.equivFin.symm index) hpoint.2

theorem jointCarrierShading_union :
    envelope.jointCarrierShading.union = envelope.shading.union := by
  apply Set.Subset.antisymm
  · rintro point ⟨_index, hpoint⟩
    exact hpoint.1
  · intro point hpoint
    let cell := wz1Lemma23CellIndex envelope.jointGraphScale point
    have hnorm := norm_le_two_of_mem_paperShading
      (envelope.subshading_current.union_subset hpoint)
    have hcellBounded :
        cell ∈ wz1Lemma23BoundedCells envelope.jointGraphScale
          envelope.jointGraphScale_pos :=
      wz1Lemma23_index_mem_bounded_two envelope.jointGraphScale_pos hnorm
    have hpointCell :
        point ∈ wz1Lemma23Cell envelope.jointGraphScale cell := rfl
    have hcell : cell ∈ envelope.jointCarrierCells :=
      Finset.mem_filter.mpr
        ⟨hcellBounded, ⟨point, hpoint, hpointCell⟩⟩
    let index : Fin envelope.jointCarrierCells.card :=
      envelope.jointCarrierCells.equivFin ⟨cell, hcell⟩
    refine ⟨index, hpoint, ?_⟩
    simpa [index] using hpointCell

theorem jointCarrier_exactAD
    (hgraphOne : envelope.jointGraphScale ≤ 1)
    (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    IsADSet1
      (scalarProjection
        (globalGrainDirection (current.grain.globalGrains.slope z))
        (horizontalSlice envelope.jointCarrierShading.union z))
      envelope.jointGraphScale (1 - sigma)
      (2 * Kakeya.realRpowENN delta (-inputLoss)) := by
  rw [envelope.jointCarrierShading_union]
  have hpaper :
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope z))
          (horizontalSlice envelope.shading.union z))
        delta (1 - sigma) (Kakeya.realRpowENN delta (-inputLoss)) := by
    apply (current.grain.globalGrains.global_ad z hz).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact ⟨point,
      ⟨envelope.subshading_current.union_subset hpoint.1, hpoint.2⟩, rfl⟩
  have hbounded :
      scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope z))
          (horizontalSlice envelope.shading.union z) ⊆
        Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨point, hpoint, rfl⟩
    have hbox := shading_union_subset_axisBox
      (envelope.subshading_current.union_subset hpoint.1)
    have hx : |point 0| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.1
    have hy : |point 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    have hslope := current.grain.globalGrains.slope_bound z hz
    have hformula :
        inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope z)) =
          point 0 + current.grain.globalGrains.slope z * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    change inner ℝ point
        (globalGrainDirection
          (current.grain.globalGrains.slope z)) ∈ Set.Icc (-4 : ℝ) 4
    rw [hformula]
    apply abs_le.mp
    calc
      |point 0 + current.grain.globalGrains.slope z * point 1| ≤
          |point 0| +
            |current.grain.globalGrains.slope z| * |point 1| := by
        simpa [abs_mul] using abs_add_le (point 0)
          (current.grain.globalGrains.slope z * point 1)
      _ ≤ 1 + 3 * 1 := by gcongr
      _ = 4 := by norm_num
  have hinternal :
      IsADSet1
        (scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope z))
          (horizontalSlice envelope.shading.union z))
        delta (1 - sigma)
        (2 * Kakeya.realRpowENN delta (-inputLoss)) :=
    hpaper.toIsADSet1 hbounded
  have hdeltaGraph : delta ≤ envelope.jointGraphScale := by
    have hdeltaRho : delta ≤ rho := by
      rw [← pullback.rhoRequested_eq]
      exact rhoRequested.property.1
    have hrho : 0 < rho := by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos
    unfold jointGraphScale
    linarith
  exact hinternal.coarsen_scale envelope.jointGraphScale_pos
    hdeltaGraph hgraphOne

noncomputable def jointGraphInput
    (hgraphOne : envelope.jointGraphScale ≤ 1) :
    PureWZ2AnchoredGraphGlobalInput
      (delta := envelope.jointGraphScale)
      (rho := envelope.jointGraphScale) (sigma := sigma)
      envelope.jointCarrierShading
      (2 * Kakeya.realRpowENN delta (-inputLoss)) where
  rho_pos := envelope.jointGraphScale_pos
  delta_le_rho := le_rfl
  rho_le_one := hgraphOne
  sourceSlope := current.grain.globalGrains.slope
  sourceSlope_lipschitz := current.grain.globalGrains.slope_lipschitz
  sourceSlope_bound := current.grain.globalGrains.slope_bound
  constant_ne_top := ENNReal.mul_ne_top (by norm_num)
    (by simp [Kakeya.realRpowENN])
  shadow_ball := by
    intro point hpoint
    rw [envelope.jointCarrierShading_union] at hpoint
    have hnorm := norm_le_two_of_mem_paperShading
      (envelope.subshading_current.union_subset hpoint)
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  shadow_coordinate := by
    intro point hpoint coordinate
    rw [envelope.jointCarrierShading_union] at hpoint
    have hbox := shading_union_subset_axisBox
      (envelope.subshading_current.union_subset hpoint)
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  exactAD := envelope.jointCarrier_exactAD hgraphOne

/-- The complete source-cell graph envelope stays in the fixed common-bin
strip selected on the same joint-height source. -/
theorem joint_fixedLine_localization
    (point : Point3) (hpoint : point ∈ envelope.shading.union) :
    |inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope (point (2 : Fin 3)))) -
        (block.bin : ℝ) * Real.sqrt rho| ≤
      14 * Real.sqrt rho := by
  let root := Real.sqrt rho
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hroot : 0 < root := Real.sqrt_pos.mpr hrho
  have hrhoOne : rho ≤ 1 := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.2
  have hrhoRoot : rho ≤ root := by
    dsimp only [root]
    nlinarith [Real.sq_sqrt hrho.le, Real.sqrt_nonneg rho]
  have hdeltaRho : delta ≤ rho := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.1
  rcases envelope.point_near_fixedBin point hpoint with
    ⟨anchor, hanchor, hdist⟩
  have hanchorJoint : anchor ∈ volumePopular.jointSourceSet :=
    hanchor.1.1
  have hanchorHeight :
      anchor (2 : Fin 3) ∈ volumePopular.jointPopularHeights :=
    hanchor.2
  have hreferenceRange :=
    volumePopular.jointPopularHeight_mem_paperRange block.referenceHeight_mem
  have hanchorReference :
      |anchor (2 : Fin 3) - block.referenceHeight| ≤ root := by
    exact volumePopular.jointPopularHeights_close
      hanchorHeight block.referenceHeight_mem
  have hpointAnchorCoordinate :
      ∀ coordinate : Fin 3,
        |point coordinate - anchor coordinate| < 2 * delta := by
    intro coordinate
    have hcoordinateLe := PiLp.dist_apply_le point anchor coordinate
    have hcoordinateLe' :
        |point coordinate - anchor coordinate| ≤ dist point anchor := by
      simpa [Real.dist_eq] using hcoordinateLe
    exact hcoordinateLe'.trans_lt hdist
  have hpointHeightRange :
      point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := by
    have hbox := shading_union_subset_axisBox
      (envelope.subshading_current.union_subset hpoint)
    simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
  have hpointReference :
      |point (2 : Fin 3) - block.referenceHeight| ≤ root + 2 * delta := by
    calc
      _ ≤ |point (2 : Fin 3) - anchor (2 : Fin 3)| +
          |anchor (2 : Fin 3) - block.referenceHeight| := by
        simpa using abs_sub_le
          (point (2 : Fin 3)) (anchor (2 : Fin 3)) block.referenceHeight
      _ ≤ 2 * delta + root := by
        gcongr
        exact (hpointAnchorCoordinate 2).le
      _ = root + 2 * delta := by ring
  have hslopeDifference :
      |current.grain.globalGrains.slope (point (2 : Fin 3)) -
          current.grain.globalGrains.slope block.referenceHeight| ≤
        root + 2 * delta := by
    have hlip :=
      current.grain.globalGrains.slope_lipschitz.dist_le_mul
        (point (2 : Fin 3)) hpointHeightRange
        block.referenceHeight hreferenceRange
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    exact hlip.trans hpointReference
  have hpointY : |point (1 : Fin 3)| ≤ 1 := by
    have hbox := shading_union_subset_axisBox
      (envelope.subshading_current.union_subset hpoint)
    simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
  have hslopeProjection :
      |inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope (point (2 : Fin 3)))) -
          inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight))| ≤
        root + 2 * delta := by
    have hformula :
        inner ℝ point
              (globalGrainDirection
                (current.grain.globalGrains.slope (point (2 : Fin 3)))) -
            inner ℝ point
              (globalGrainDirection
                (current.grain.globalGrains.slope block.referenceHeight)) =
          (current.grain.globalGrains.slope (point (2 : Fin 3)) -
              current.grain.globalGrains.slope block.referenceHeight) *
            point (1 : Fin 3) := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      ring
    rw [hformula, abs_mul]
    calc
      _ ≤ (root + 2 * delta) * 1 := by
        exact mul_le_mul hslopeDifference hpointY
          (abs_nonneg _)
          (add_nonneg hroot.le
            (mul_nonneg (by norm_num) current.grain.extremal.delta_pos.le))
      _ = root + 2 * delta := by ring
  have hreferenceSlope :=
    current.grain.globalGrains.slope_bound
      block.referenceHeight hreferenceRange
  have hspatialProjection :
      |inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight)) -
          inner ℝ anchor
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight))| ≤
        8 * delta := by
    have hformula :
        inner ℝ point
              (globalGrainDirection
                (current.grain.globalGrains.slope block.referenceHeight)) -
            inner ℝ anchor
              (globalGrainDirection
                (current.grain.globalGrains.slope block.referenceHeight)) =
          (point 0 - anchor 0) +
            current.grain.globalGrains.slope block.referenceHeight *
              (point 1 - anchor 1) := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      ring
    rw [hformula]
    calc
      _ ≤ |point 0 - anchor 0| +
          |current.grain.globalGrains.slope block.referenceHeight| *
            |point 1 - anchor 1| := by
        simpa [abs_mul] using abs_add_le (point 0 - anchor 0)
          (current.grain.globalGrains.slope block.referenceHeight *
            (point 1 - anchor 1))
      _ ≤ 2 * delta + 3 * (2 * delta) := by
        gcongr <;> exact (hpointAnchorCoordinate _).le
      _ = 8 * delta := by ring
  have hanchorLabel :
      pureWZ2FixedCommonBinLabel current.grain.globalGrains.slope
        block.referenceHeight root anchor = block.bin := by
    simpa [root, jointFixedBinHeightRegion,
      pureWZ2FixedCommonBinRegion] using hanchor.1.2
  have hfloor :
      Int.floor
        (inner ℝ anchor
          (globalGrainDirection
            (current.grain.globalGrains.slope block.referenceHeight)) /
          root) = block.bin := by
    simpa [pureWZ2FixedCommonBinLabel, root] using hanchorLabel
  have hanchorStrip :
      |inner ℝ anchor
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight)) -
          (block.bin : ℝ) * root| ≤ root := by
    have hlower := Int.floor_le
      (inner ℝ anchor
        (globalGrainDirection
          (current.grain.globalGrains.slope block.referenceHeight)) / root)
    have hupper := Int.lt_floor_add_one
      (inner ℝ anchor
        (globalGrainDirection
          (current.grain.globalGrains.slope block.referenceHeight)) / root)
    rw [hfloor] at hlower hupper
    rw [abs_le]
    constructor
    · have := (le_div_iff₀ hroot).mp hlower
      linarith
    · have := (div_lt_iff₀ hroot).mp hupper
      linarith
  calc
    _ ≤
        |inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope (point (2 : Fin 3)))) -
          inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight))| +
        |inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight)) -
          inner ℝ anchor
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight))| +
        |inner ℝ anchor
            (globalGrainDirection
              (current.grain.globalGrains.slope block.referenceHeight)) -
          (block.bin : ℝ) * root| := by
      have hone := abs_sub_le
        (inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope (point (2 : Fin 3)))))
        (inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope block.referenceHeight)))
        ((block.bin : ℝ) * root)
      have htwo := abs_sub_le
        (inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope block.referenceHeight)))
        (inner ℝ anchor
          (globalGrainDirection
            (current.grain.globalGrains.slope block.referenceHeight)))
        ((block.bin : ℝ) * root)
      linarith
    _ ≤ (root + 2 * delta) + 8 * delta + root := by gcongr
    _ ≤ 14 * root := by
      have hdeltaRoot : delta ≤ root := hdeltaRho.trans hrhoRoot
      linarith

/-- Prepare the production graph.  The first callback uses the source slab
and the second uses the same fixed-bin line. -/
theorem jointGraphPreparation
    (hgraphOne : envelope.jointGraphScale ≤ 1)
    (hwindowAbsorb :
      envelope.jointGraphScale + 5 * Real.sqrt rho ≤
        Real.sqrt envelope.jointGraphScale) :
    Nonempty
      (PureWZ2AnchoredGraphPreparationData
        (envelope.jointGraphInput hgraphOne)) := by
  apply pureWZ2_anchoredGraphPreparation
    (envelope.jointGraphInput hgraphOne)
  · intro global hslope
    let root := Real.sqrt rho
    let slabLeft := volumePopular.jointSlabLeft
    let left :=
      slabLeft - 2 * delta - envelope.jointGraphScale / 2
    refine ⟨left, ?_⟩
    intro cell hcell
    have hactive :=
      (wz1Lemma23_mem_active_iff envelope.jointCarrierShading
        envelope.jointGraphScale_pos cell).mp hcell
    rcases hactive.2 with ⟨point, hpoint, hpointCell⟩
    have hpointEnvelope : point ∈ envelope.shading.union := by
      rwa [envelope.jointCarrierShading_union] at hpoint
    rcases envelope.point_near_fixedBin point hpointEnvelope with
      ⟨anchor, hanchor, hdist⟩
    have hanchorHeight := volumePopular.jointSourceSet_height
      anchor hanchor.1.1
    have hcoordinateLe := PiLp.dist_apply_le point anchor (2 : Fin 3)
    have hcoordinate :
        |point (2 : Fin 3) - anchor (2 : Fin 3)| < 2 * delta := by
      have hcoordinate' :
          |point (2 : Fin 3) - anchor (2 : Fin 3)| ≤
            dist point anchor := by
        simpa [Real.dist_eq] using hcoordinateLe
      exact hcoordinate'.trans_lt hdist
    have hcenter :=
      ((wz1_lemma23_snapped_cell_geometry envelope.jointGraphScale
        envelope.jointGraphScale_pos hgraphOne).2.1
        cell point hpointCell).1 (2 : Fin 3)
    rw [abs_le] at hcenter
    rw [abs_lt] at hcoordinate
    constructor
    · dsimp only [left, slabLeft]
      linarith [hanchorHeight.1, hcoordinate.1, hcenter.1]
    · dsimp only [left, slabLeft]
      have hdeltaRho : delta ≤ rho := by
        rw [← pullback.rhoRequested_eq]
        exact rhoRequested.property.1
      have hrho : 0 < rho := by
        rw [← pullback.rhoRequested_eq]
        exact twoScale.first.publicSticky.coarse_extremal.delta_pos
      have hrhoOne : rho ≤ 1 := by
        rw [← pullback.rhoRequested_eq]
        exact rhoRequested.property.2
      have hrhoRoot : rho ≤ Real.sqrt rho := by
        nlinarith [Real.sq_sqrt hrho.le, Real.sqrt_nonneg rho]
      have hdeltaRoot : delta ≤ Real.sqrt rho :=
        hdeltaRho.trans hrhoRoot
      linarith [hanchorHeight.2, hcoordinate.2, hcenter.2,
        hwindowAbsorb]
  · intro global hslope
    refine ⟨fun _ => (block.bin : ℝ) * Real.sqrt rho, ?_⟩
    intro graphHeightIndex hgraphHeightIndex
    rintro value ⟨point, hpoint, rfl⟩
    have hpointEnvelope : point ∈ envelope.shading.union := by
      rw [envelope.jointCarrierShading_union] at hpoint
      exact hpoint.1
    have hbound := envelope.joint_fixedLine_localization point hpointEnvelope
    have hsqrtGraph :
        Real.sqrt envelope.jointGraphScale = 16 * Real.sqrt rho := by
      unfold jointGraphScale
      rw [Real.sqrt_mul (by norm_num),
        show Real.sqrt (256 : ℝ) = 16 by norm_num]
    rw [Metric.mem_closedBall, Real.dist_eq, hslope]
    change
      |inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope
              (global.selectedHeight graphHeightIndex))) -
        (block.bin : ℝ) * Real.sqrt rho| ≤
        Real.sqrt envelope.jointGraphScale
    rw [← hpoint.2]
    rw [hsqrtGraph]
    exact hbound.trans (by
      have hrho : 0 < rho := by
        rw [← pullback.rhoRequested_eq]
        exact twoScale.first.publicSticky.coarse_extremal.delta_pos
      nlinarith [Real.sqrt_pos.mpr hrho])

/-- Canonical representatives of the runtime graph cells. -/
structure JointGraphRepresentativeData
    {hgraphOne : envelope.jointGraphScale ≤ 1}
    (prep : PureWZ2AnchoredGraphPreparationData
      (envelope.jointGraphInput hgraphOne)) where
  representative : WZ2PaperCellIndex → Point3
  representative_mem :
    ∀ cell ∈ prep.windowed.global.cells,
      representative cell ∈ envelope.jointCarrierShading.union
  representative_index :
    ∀ cell ∈ prep.windowed.global.cells,
      wz1Lemma23CellIndex envelope.jointGraphScale
        (representative cell) = cell

theorem jointGraphRepresentatives
    {hgraphOne : envelope.jointGraphScale ≤ 1}
    (prep : PureWZ2AnchoredGraphPreparationData
      (envelope.jointGraphInput hgraphOne)) :
    Nonempty (envelope.JointGraphRepresentativeData prep) := by
  let cells := prep.windowed.global.cells
  let representative : WZ2PaperCellIndex → Point3 := fun cell =>
    if hcell : cell ∈ cells then
      wz1Lemma23CellRepresentative envelope.jointCarrierShading
        envelope.jointGraphScale_pos
        ⟨cell, prep.windowed.global.cells_active hcell⟩
    else 0
  exact ⟨{
    representative := representative
    representative_mem := by
      intro cell hcell
      change cell ∈ cells at hcell
      simp only [representative, dif_pos hcell]
      exact wz1Lemma23CellRepresentative_mem_union
        envelope.jointCarrierShading envelope.jointGraphScale_pos _
    representative_index := by
      intro cell hcell
      change cell ∈ cells at hcell
      simp only [representative, dif_pos hcell]
      exact wz1Lemma23CellRepresentative_index
        envelope.jointCarrierShading envelope.jointGraphScale_pos _
  }⟩

/-- The generic bounded-fibre height bridge is now discharged on the actual
joint-height production graph carrier. -/
theorem jointTheorem52HeightAssignment
    (outerEnvelope :
      PureWZ2Node05V4RichSourceVolumePopularEnvelopeData volumePopular)
    {hgraphOne : envelope.jointGraphScale ≤ 1}
    {prep : PureWZ2AnchoredGraphPreparationData
      (envelope.jointGraphInput hgraphOne)}
    (representatives : envelope.JointGraphRepresentativeData prep)
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := envelope.jointGraphScale) (sigma := sigma)
      (2 * Kakeya.realRpowENN delta (-inputLoss))
      prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {finalLoss : ℝ}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (output : PureWZ2AnchoredTheorem52Output finiteGraph projection) :
    Nonempty
      (PureWZ2Node05V4RichHeightAssignmentData
        output.richHeightIndices volumePopular.popular.heightIndices) := by
  apply pureWZ2Node05V4Rich_sourceVolumePopularHeightAssignment
    outerEnvelope output
      (show envelope.jointGraphScale = 256 * rho from rfl)
      representatives.representative
      representatives.representative_mem
      representatives.representative_index
  intro point hpoint
  rw [envelope.jointCarrierShading_union] at hpoint
  rcases envelope.point_near_volumePopular point hpoint with
    ⟨anchor, hanchor, hdist⟩
  refine ⟨anchor, hanchor, ?_⟩
  have hdeltaRho : delta ≤ rho := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.1
  linarith

/-- Weighted original-family source return on the runtime graph's assigned
heights; every retained source point remains in the continuous paper `Z_S`. -/
theorem jointTheorem52AssignedSourceMass
    {hgraphOne : envelope.jointGraphScale ≤ 1}
    {prep : PureWZ2AnchoredGraphPreparationData
      (envelope.jointGraphInput hgraphOne)}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := envelope.jointGraphScale) (sigma := sigma)
      (2 * Kakeya.realRpowENN delta (-inputLoss))
      prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {finalLoss : ℝ}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (output : PureWZ2AnchoredTheorem52Output finiteGraph projection)
    (assignment : PureWZ2Node05V4RichHeightAssignmentData
      output.richHeightIndices volumePopular.popular.heightIndices) :
    Nonempty
      (PureWZ2Node05V4RichAssignedSourceMassData
        volumePopular output assignment) :=
  pureWZ2Node05V4Rich_assignedSourceMass
    volumePopular output assignment
      (show envelope.jointGraphScale = 256 * rho from rfl)

end JointHeightGraphEnvelopeData

end PureWZ2Node05V4RichSourceVolumePopularHeightData

end Kakeya.Assouad

end
