import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingLineDistance
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12LocalizedDoubledFiber
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12LocalizedEssentialDistinctness
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureFiberRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDoubledParentCarrierCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureSharedParentDirection
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CommonContainerBaseClosenessBaseFive
import MyLeanRepo.Kakeya.Assouad.WZ1.PaperPackingRefinement

/-!
# Representative parent cover for Proposition 6.3 mild rescaling

For one source Definition 2.12 scale, select one target image line from each
complete source fiber.  Recenter it canonically and enlarge only its radius.
All target fine tubes above that source fiber are then strictly contained in
the corresponding target parent.  A later finite strong-separation selection
turns this preliminary assignment into the literal public partitioning cover.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Metric Set

attribute [local instance] Classical.propDecidable

private theorem proposition63_tube_carrier_containment_from_closeness
    {delta rho : ℝ} (hdelta : 0 ≤ delta) (hrho : 0 ≤ rho)
    (fine : Kakeya.DeltaTube delta) (coarse : Kakeya.DeltaTube rho)
    (hclose : ‖fine.base - coarse.base‖ +
        ‖fine.direction - coarse.direction‖ + delta ≤ rho) :
    fine.carrier ⊆ coarse.carrier := by
  have hfineCompact : IsCompact
      (Kakeya.unitSegment fine.base fine.direction) :=
    isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  have hfineUnion : fine.carrier =
      ⋃ point ∈ Kakeya.unitSegment fine.base fine.direction,
        Metric.closedBall point delta :=
    hfineCompact.cthickening_eq_biUnion_closedBall hdelta
  have hcoarseCompact : IsCompact
      (Kakeya.unitSegment coarse.base coarse.direction) :=
    isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  have hcoarseUnion : coarse.carrier =
      ⋃ point ∈ Kakeya.unitSegment coarse.base coarse.direction,
        Metric.closedBall point rho :=
    hcoarseCompact.cthickening_eq_biUnion_closedBall hrho
  intro point hpoint
  rw [hfineUnion] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨fineAxisPoint, hfineAxisPoint, hpointFine⟩
  rcases hfineAxisPoint with ⟨parameter, hparameter, hfineAxisPoint⟩
  let coarseAxisPoint := coarse.base + parameter • coarse.direction
  have hcoarseAxisPoint : coarseAxisPoint ∈
      Kakeya.unitSegment coarse.base coarse.direction :=
    ⟨parameter, hparameter, rfl⟩
  have haxisDistance : dist fineAxisPoint coarseAxisPoint ≤
      ‖fine.base - coarse.base‖ +
        ‖fine.direction - coarse.direction‖ := by
    rw [dist_eq_norm, ← hfineAxisPoint]
    have hvector :
        fine.base + parameter • fine.direction - coarseAxisPoint =
          (fine.base - coarse.base) +
            parameter • (fine.direction - coarse.direction) := by
      dsimp only [coarseAxisPoint]
      module
    rw [hvector]
    calc
      ‖(fine.base - coarse.base) +
          parameter • (fine.direction - coarse.direction)‖ ≤
        ‖fine.base - coarse.base‖ +
          ‖parameter • (fine.direction - coarse.direction)‖ :=
        norm_add_le _ _
      _ = ‖fine.base - coarse.base‖ +
          |parameter| * ‖fine.direction - coarse.direction‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖fine.base - coarse.base‖ +
          ‖fine.direction - coarse.direction‖ := by
        have hparameterAbs : |parameter| ≤ 1 := by
          rw [abs_of_nonneg hparameter.1]
          exact hparameter.2
        have hdirectionNonnegative :
            0 ≤ ‖fine.direction - coarse.direction‖ := norm_nonneg _
        have hscaledDirection :
            |parameter| * ‖fine.direction - coarse.direction‖ ≤
              ‖fine.direction - coarse.direction‖ :=
          mul_le_of_le_one_left hdirectionNonnegative hparameterAbs
        exact add_le_add_right hscaledDirection _
  have hpointCoarse : dist point coarseAxisPoint ≤ rho := by
    calc
      dist point coarseAxisPoint ≤
          dist point fineAxisPoint +
            dist fineAxisPoint coarseAxisPoint := dist_triangle _ _ _
      _ ≤ delta +
          (‖fine.base - coarse.base‖ +
            ‖fine.direction - coarse.direction‖) := by
        gcongr
        simpa [Metric.mem_closedBall] using hpointFine
      _ ≤ rho := by linarith
  rw [hcoarseUnion]
  exact Set.mem_iUnion₂.mpr
    ⟨coarseAxisPoint, hcoarseAxisPoint, by
      simpa [Metric.mem_closedBall] using hpointCoarse⟩

/-- On the canonical centered representatives, a line-distance budget gives
strict containment after increasing only the parent radius. -/
private theorem proposition63_centered_carrier_subset_relabel_of_lineDistance
    {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (first second : Kakeya.DeltaTube delta)
    (hfirstLine : WZ1PaperTubeInLineClass first)
    (hsecondLine : WZ1PaperTubeInLineClass second)
    (hfirstCentered : proposition63CenteredTube first = first)
    (hsecondCentered : proposition63CenteredTube second = second)
    (hbudget :
      (3 / 2 : ℝ) * wz1PaperLineDistance first second + delta ≤ rho) :
    first.carrier ⊆
      (wz2PaperRelabelTube (targetScale := rho) second).carrier := by
  have hzeroFirst : wz1TubeAxisZeroPoint first =
      wz2PaperTubeMidpoint first := by
    rw [← hfirstCentered, proposition63CenteredTube_midpoint]
    exact (wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
      hfirstLine.vertical
      (by rw [hfirstCentered]; exact wz1TubeAxisZeroPoint_mem_axis first)
      (by
        rw [hfirstCentered]
        exact wz1TubeAxisZeroPoint_coord_two first hfirstLine.vertical)).symm
  have hzeroSecond : wz1TubeAxisZeroPoint second =
      wz2PaperTubeMidpoint second := by
    rw [← hsecondCentered, proposition63CenteredTube_midpoint]
    exact (wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
      hsecondLine.vertical
      (by rw [hsecondCentered]; exact wz1TubeAxisZeroPoint_mem_axis second)
      (by
        rw [hsecondCentered]
        exact wz1TubeAxisZeroPoint_coord_two second hsecondLine.vertical)).symm
  have hdirectionFirst : first.direction = wz1PaperDirection first := by
    have h := congrArg (fun tube => tube.direction) hfirstCentered
    change wz1PaperDirection first = first.direction at h
    exact h.symm
  have hdirectionSecond : second.direction = wz1PaperDirection second := by
    have h := congrArg (fun tube => tube.direction) hsecondCentered
    change wz1PaperDirection second = second.direction at h
    exact h.symm
  have hbase : ‖first.base - second.base‖ ≤
      dist (wz1TubeAxisZeroPoint first)
          (wz1TubeAxisZeroPoint second) +
        (1 / 2 : ℝ) * InnerProductGeometry.angle
          (wz1PaperDirection first) (wz1PaperDirection second) := by
    have hbaseVector : first.base - second.base =
        (wz1TubeAxisZeroPoint first -
          wz1TubeAxisZeroPoint second) -
        (1 / 2 : ℝ) •
          (wz1PaperDirection first - wz1PaperDirection second) := by
      rw [hzeroFirst, hzeroSecond]
      dsimp only [wz2PaperTubeMidpoint]
      rw [hdirectionFirst, hdirectionSecond]
      module
    rw [hbaseVector]
    calc
      ‖(wz1TubeAxisZeroPoint first - wz1TubeAxisZeroPoint second) -
          (1 / 2 : ℝ) •
            (wz1PaperDirection first - wz1PaperDirection second)‖ ≤
        ‖wz1TubeAxisZeroPoint first - wz1TubeAxisZeroPoint second‖ +
          ‖(1 / 2 : ℝ) •
            (wz1PaperDirection first - wz1PaperDirection second)‖ :=
        norm_sub_le _ _
      _ = dist (wz1TubeAxisZeroPoint first)
            (wz1TubeAxisZeroPoint second) +
          (1 / 2 : ℝ) *
            ‖wz1PaperDirection first - wz1PaperDirection second‖ := by
        rw [dist_eq_norm, norm_smul, Real.norm_eq_abs]
        norm_num
      _ ≤ dist (wz1TubeAxisZeroPoint first)
            (wz1TubeAxisZeroPoint second) +
          (1 / 2 : ℝ) * InnerProductGeometry.angle
            (wz1PaperDirection first) (wz1PaperDirection second) := by
        gcongr
        exact unit_norm_sub_le_angle
          (wz1PaperDirection_norm first)
          (wz1PaperDirection_norm second)
  have hdirection : ‖first.direction - second.direction‖ ≤
      InnerProductGeometry.angle
        (wz1PaperDirection first) (wz1PaperDirection second) := by
    rw [hdirectionFirst, hdirectionSecond]
    exact unit_norm_sub_le_angle
      (wz1PaperDirection_norm first)
      (wz1PaperDirection_norm second)
  apply proposition63_tube_carrier_containment_from_closeness
    hdelta.le hrho.le
  change ‖first.base - second.base‖ +
      ‖first.direction - second.direction‖ + delta ≤ rho
  have hdistNonnegative : 0 ≤ dist
      (wz1TubeAxisZeroPoint first)
      (wz1TubeAxisZeroPoint second) := dist_nonneg
  have hangleNonnegative : 0 ≤ InnerProductGeometry.angle
      (wz1PaperDirection first) (wz1PaperDirection second) :=
    InnerProductGeometry.angle_nonneg _ _
  have hmetric :
      dist (wz1TubeAxisZeroPoint first)
            (wz1TubeAxisZeroPoint second) +
          InnerProductGeometry.angle
            (wz1PaperDirection first) (wz1PaperDirection second) =
        wz1PaperLineDistance first second := rfl
  calc
    ‖first.base - second.base‖ +
          ‖first.direction - second.direction‖ + delta ≤
        dist (wz1TubeAxisZeroPoint first)
            (wz1TubeAxisZeroPoint second) +
          (3 / 2 : ℝ) * InnerProductGeometry.angle
            (wz1PaperDirection first) (wz1PaperDirection second) +
          delta := by linarith
    _ ≤ (3 / 2 : ℝ) *
          wz1PaperLineDistance first second + delta := by
      rw [← hmetric]
      linarith
    _ ≤ rho := hbudget

/-- The same-axis radius-`2 delta` ordinary tube lies in the centered
two-fold dilation of the original ordinary tube. -/
private theorem proposition63_radiusTwo_carrier_subset_doubled
    {delta : ℝ} (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta) :
    (wz2PaperRelabelTube (targetScale := 2 * delta) tube).carrier ⊆
      wz2PaperCenteredDilatedCarrier 2 tube := by
  intro point hpoint
  change point ∈ Metric.cthickening (2 * delta)
      (Kakeya.unitSegment tube.base tube.direction) at hpoint
  have hsegmentCompact : IsCompact
      (Kakeya.unitSegment tube.base tube.direction) :=
    isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  rcases exists_dist_le_of_mem_cthickening_closed hsegmentCompact.isClosed
      (by positivity : 0 ≤ 2 * delta) hpoint with
    ⟨axisPoint, haxisPoint, hpointDistance⟩
  let center := wz2PaperTubeMidpoint tube
  let contractedPoint := center + (1 / 2 : ℝ) • (point - center)
  let contractedAxis := center + (1 / 2 : ℝ) • (axisPoint - center)
  have hcenterSegment : center ∈
      Kakeya.unitSegment tube.base tube.direction :=
    ⟨1 / 2, by norm_num, rfl⟩
  have hcontractedAxis : contractedAxis ∈
      Kakeya.unitSegment tube.base tube.direction := by
    rcases haxisPoint with ⟨parameter, hparameter, rfl⟩
    refine ⟨1 / 4 + parameter / 2, ?_, ?_⟩
    · constructor <;> linarith [hparameter.1, hparameter.2]
    · dsimp only [contractedAxis, center, wz2PaperTubeMidpoint]
      module
  have hcontractedDistance : dist contractedPoint contractedAxis ≤ delta := by
    rw [dist_eq_norm]
    have hvector : contractedPoint - contractedAxis =
        (1 / 2 : ℝ) • (point - axisPoint) := by
      dsimp only [contractedPoint, contractedAxis]
      module
    rw [hvector, norm_smul, Real.norm_eq_abs]
    norm_num
    simpa [dist_eq_norm] using
      (mul_le_mul_of_nonneg_left hpointDistance
        (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hcontractedCarrier : contractedPoint ∈ tube.carrier :=
    Metric.mem_cthickening_of_dist_le contractedPoint contractedAxis delta _
      hcontractedAxis hcontractedDistance
  refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
  rw [AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  dsimp only [contractedPoint, center]
  module

/-- On centered same-scale tubes, line distance at most `2 delta / 3`
contradicts ordinary essential distinctness. -/
private theorem proposition63_centered_carrier_subset_doubled_of_lineDistance
    {delta : ℝ} (hdelta : 0 < delta)
    (first second : Kakeya.DeltaTube delta)
    (hfirstLine : WZ1PaperTubeInLineClass first)
    (hsecondLine : WZ1PaperTubeInLineClass second)
    (hfirstCentered : proposition63CenteredTube first = first)
    (hsecondCentered : proposition63CenteredTube second = second)
    (hdistance : wz1PaperLineDistance first second ≤ (2 / 3 : ℝ) * delta) :
    first.carrier ⊆ wz2PaperCenteredDilatedCarrier 2 second := by
  have hcontain := proposition63_centered_carrier_subset_relabel_of_lineDistance
    hdelta (by positivity : 0 < 2 * delta) first second
    hfirstLine hsecondLine hfirstCentered hsecondCentered
    (by
      calc
        (3 / 2 : ℝ) * wz1PaperLineDistance first second + delta ≤
            (3 / 2 : ℝ) * ((2 / 3 : ℝ) * delta) + delta := by gcongr
        _ = 2 * delta := by ring)
  exact hcontain.trans
    (proposition63_radiusTwo_carrier_subset_doubled hdelta second)

/-- Preliminary one-scale parent data before the simultaneous
strong-separation and degree-regularization passes. -/
structure Proposition63MildRescalingParentCoverData
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    (sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant)
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center)
    (targetRho : ℝ) where
  source_nonempty : sourceFine.Nonempty
  source_line_class : WZ1PaperIsLineClass sourceFine
  source_paper_distinct : WZ1PaperIsEssentiallyDistinct sourceFine
  source_midpoint_local : ∀ source,
    ‖wz2PaperTubeMidpoint (sourceFine.tube source)‖ ≤ 3
  raw_line_class : WZ1PaperIsLineClass raw.family
  center_height : |center 2| ≤ 2
  target_rho_pos : 0 < targetRho
  target_rho_budget :
    (3 / 2 : ℝ) * (1300000 * scale * sourceRho) +
        scale * sourceDelta ≤
      targetRho

/-- The smallest explicit target-parent radius used by the canonical mild
rescaling construction. -/
def proposition63MildRescalingTargetRho
    (sourceDelta sourceRho scale : ℝ) : ℝ :=
  (3 / 2 : ℝ) * (1300000 * scale * sourceRho) +
    scale * sourceDelta

/-- Package one source Definition-2.12 scale into the geometric parent-cover
input at its canonical enlarged target radius. -/
theorem Proposition63MildRescalingParentCoverData.ofSource
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    (sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant)
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center)
    (sourceNonempty : sourceFine.Nonempty)
    (sourceLine : WZ1PaperIsLineClass sourceFine)
    (sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFine)
    (sourceMidpoint : ∀ source,
      ‖wz2PaperTubeMidpoint (sourceFine.tube source)‖ ≤ 3)
    (rawLine : WZ1PaperIsLineClass raw.family)
    (hcenterHeight : |center 2| ≤ 2) :
    Proposition63MildRescalingParentCoverData sourceScale hscale raw
      (proposition63MildRescalingTargetRho
        sourceDelta sourceRho scale) where
  source_nonempty := sourceNonempty
  source_line_class := sourceLine
  source_paper_distinct := sourceDistinct
  source_midpoint_local := sourceMidpoint
  raw_line_class := rawLine
  center_height := hcenterHeight
  target_rho_pos := by
    dsimp only [proposition63MildRescalingTargetRho]
    have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
    exact add_pos
      (mul_pos (by norm_num)
        (mul_pos (mul_pos (by norm_num) hscalePos) sourceScale.rho_pos))
      (mul_pos hscalePos sourceScale.delta_pos)
  target_rho_budget := le_rfl

namespace Proposition63MildRescalingParentCoverData

/-- Pick one source line from each nonempty complete source full fiber. -/
noncomputable def sourceRepresentative
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho)
    (parent : Fin sourceScale.coarse.card) : Fin sourceFine.card :=
  Classical.choose
    (sourceScale.cover.fullFiber_nonempty_of_uniform
      data.source_nonempty sourceScale.full_fiber_uniform parent)

theorem sourceRepresentative_mem
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho)
    (parent : Fin sourceScale.coarse.card) :
    data.sourceRepresentative parent ∈
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceScale.coarse parent :=
  Classical.choose_spec
    (sourceScale.cover.fullFiber_nonempty_of_uniform
      data.source_nonempty sourceScale.full_fiber_uniform parent)

theorem sourceRepresentative_parent
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho)
    (parent : Fin sourceScale.coarse.card) :
    sourceScale.cover.parent (data.sourceRepresentative parent) = parent :=
  (sourceScale.cover.mem_fullFiber_iff_parent_eq
    sourceScale.rho_pos.le parent (data.sourceRepresentative parent)).mp
      (data.sourceRepresentative_mem parent)

/-- The ordinary target parent is the centered image-line representative of
the corresponding source full fiber, relabelled at `targetRho`. -/
def parentFamily
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho) :
    Kakeya.Streamlined.TubeFamily targetRho where
  card := sourceScale.coarse.card
  tube parent := wz2PaperRelabelTube (targetScale := targetRho)
    ((proposition63MildRescalingFamily hscale raw).tube
      (data.sourceRepresentative parent))

theorem parentFamily_lineClass
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho) :
    WZ1PaperIsLineClass data.parentFamily := by
  intro parent
  exact wz2PaperRelabelTube_lineClass
    (proposition63MildRescalingFamily_lineClass
      hscale raw data.raw_line_class (data.sourceRepresentative parent))

/-- Source-parent representatives form a quantitative packing subfamily of
the original paper-line family. -/
def representativePackingFamily
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho) :
    Kakeya.Streamlined.TubeFamily sourceDelta where
  card := sourceScale.coarse.card
  tube parent := sourceFine.tube (data.sourceRepresentative parent)

theorem sourceRepresentative_injective
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho) :
    Function.Injective data.sourceRepresentative := by
  intro first second heq
  have hparents := congrArg sourceScale.cover.parent heq
  simpa [data.sourceRepresentative_parent first,
    data.sourceRepresentative_parent second] using hparents

theorem representativePacking_lineClass
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho) :
    WZ1PaperIsLineClass data.representativePackingFamily := by
  intro parent
  exact data.source_line_class (data.sourceRepresentative parent)

theorem representativePacking_paperDistinct
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho) :
    WZ1PaperIsEssentiallyDistinct data.representativePackingFamily := by
  intro first second hne
  have hrepresentativeNe : data.sourceRepresentative first ≠
      data.sourceRepresentative second :=
    data.sourceRepresentative_injective.ne hne
  change sourceDelta < wz1PaperLineDistance
    (sourceFine.tube (data.sourceRepresentative first))
    (sourceFine.tube (data.sourceRepresentative second))
  exact data.source_paper_distinct _ _ hrepresentativeNe

/-- Number of representative parents in a target line-metric ball. -/
def parentConflictDegree
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (_data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho) : ℕ :=
  (2 * Nat.ceil
    (8 * (14 * (2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
      targetRho)) / sourceDelta) + 1) ^ 5

theorem parentConflict_degree
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho)
    (parent : Fin sourceScale.coarse.card) :
    ((Finset.univ : Finset (Fin sourceScale.coarse.card)).filter
      (fun other =>
        wz1PaperLineDistance
            (data.parentFamily.tube parent)
            (data.parentFamily.tube other) ≤
          2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
            targetRho)).card ≤ data.parentConflictDegree := by
  let sep := 2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
    targetRho
  have hsep : 0 < sep := by
    dsimp only [sep, wz2PaperLocalizedDoubledFiberLineDistanceConstant]
    nlinarith [data.target_rho_pos]
  have hpacking := tube_packing_bound_general
    data.representativePacking_paperDistinct
    data.representativePacking_lineClass
    sourceScale.delta_pos (14 * sep) (by positivity) parent
  have hdistance : ∀ first second,
      wz1PaperLineDistance (data.representativePackingFamily.tube first)
          (data.representativePackingFamily.tube second) ≤
        14 * wz1PaperLineDistance (data.parentFamily.tube first)
          (data.parentFamily.tube second) := by
    intro first second
    change wz1PaperLineDistance
        (sourceFine.tube (data.sourceRepresentative first))
        (sourceFine.tube (data.sourceRepresentative second)) ≤ _
    exact proposition63_source_lineDistance_le_fourteen_mul_target
      hscale center data.center_height
      (sourceFine.tube (data.sourceRepresentative first))
      (sourceFine.tube (data.sourceRepresentative second))
      ((proposition63MildRescalingFamily hscale raw).tube
        (data.sourceRepresentative first))
      ((proposition63MildRescalingFamily hscale raw).tube
        (data.sourceRepresentative second))
      (data.source_line_class _) (data.source_line_class _)
      (proposition63MildRescalingFamily_lineClass
        hscale raw data.raw_line_class _)
      (proposition63MildRescalingFamily_lineClass
        hscale raw data.raw_line_class _)
      (proposition63MildRescalingFamily_axis_provenance hscale raw _)
      (proposition63MildRescalingFamily_axis_provenance hscale raw _)
      (proposition63MildRescalingFamily_direction_provenance hscale raw _)
      (proposition63MildRescalingFamily_direction_provenance hscale raw _)
  let neighbors :=
    (Finset.univ : Finset (Fin sourceScale.coarse.card)).filter
      (fun other =>
        wz1PaperLineDistance
            (data.parentFamily.tube parent)
            (data.parentFamily.tube other) ≤ sep)
  let sourceBall :=
    (Finset.univ : Finset (Fin sourceScale.coarse.card)).filter
      (fun other =>
        wz1PaperLineDistance
            (data.representativePackingFamily.tube other)
            (data.representativePackingFamily.tube parent) ≤ 14 * sep)
  have hsubset : neighbors ⊆ sourceBall := by
    intro other hother
    have htarget := (Finset.mem_filter.mp hother).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [wz1PaperLineDistance_symm]
    exact (hdistance parent other).trans (by gcongr)
  have hcard : neighbors.card ≤ sourceBall.card :=
    Finset.card_le_card hsubset
  change neighbors.card ≤ data.parentConflictDegree
  have hpacking' : sourceBall.card ≤ data.parentConflictDegree := by
    change Nat.le sourceBall.card data.parentConflictDegree
    change Nat.le sourceBall.card _ at hpacking
    simpa only [sourceBall, sep, parentConflictDegree] using hpacking
  exact hcard.trans hpacking'

/-- Two line-class source tubes in one ordinary carrier parent have paper
line distance `O(sourceRho)`, without requiring the parent itself to lie in
the paper line class.  For small parent radii this follows by comparing the
two positive-chart axes through their common carrier; for larger radii the
fixed line-class window gives an absolute bound. -/
theorem common_source_parent_sourceLineDistance
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho)
    (first second : Fin sourceFine.card)
    (hparent : sourceScale.cover.parent first =
      sourceScale.cover.parent second) :
    wz1PaperLineDistance (sourceFine.tube first)
        (sourceFine.tube second) ≤
      100000 * sourceRho := by
  let commonParent := sourceScale.cover.parent first
  have hfirstMem := sourceScale.cover.parent_mem_fullFiber first
  have hsecondMem := sourceScale.cover.parent_mem_fullFiber second
  rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at hfirstMem hsecondMem
  have hsecondParent :
      sourceScale.cover.parent second = commonParent := hparent.symm
  rw [hsecondParent] at hsecondMem
  by_cases hsmall : sourceRho ≤ 1 / 10000
  · have hsourceDirections :
        ‖wz1PaperDirection (sourceFine.tube first) -
            wz1PaperDirection (sourceFine.tube second)‖ ≤
          8 * sourceRho :=
      paper_directions_close_of_shared_carrier_parent
        sourceScale.delta_pos.le sourceScale.rho_pos
        (by linarith)
        (data.source_line_class first) (data.source_line_class second)
        hfirstMem hsecondMem
    have hfirstBaseMidpoint :
        dist (sourceFine.tube first).base
            (wz2PaperTubeMidpoint (sourceFine.tube first)) = 1 / 2 := by
      rw [dist_eq_norm]
      dsimp only [wz2PaperTubeMidpoint]
      rw [show
        (sourceFine.tube first).base -
            ((sourceFine.tube first).base +
              (1 / 2 : ℝ) • (sourceFine.tube first).direction) =
          -(1 / 2 : ℝ) • (sourceFine.tube first).direction by module,
        norm_smul, Real.norm_eq_abs,
        (sourceFine.tube first).direction_unit]
      norm_num
    have hfirstBaseNorm : ‖(sourceFine.tube first).base‖ ≤ 5 := by
      calc
        ‖(sourceFine.tube first).base‖ =
            dist (sourceFine.tube first).base 0 := by
          rw [dist_zero_right]
        _ ≤ dist (sourceFine.tube first).base
              (wz2PaperTubeMidpoint (sourceFine.tube first)) +
            dist (wz2PaperTubeMidpoint (sourceFine.tube first)) 0 :=
          dist_triangle _ _ _
        _ = 1 / 2 +
            ‖wz2PaperTubeMidpoint (sourceFine.tube first)‖ := by
          rw [hfirstBaseMidpoint, dist_zero_right]
        _ ≤ 1 / 2 + 3 := by gcongr; exact data.source_midpoint_local first
        _ ≤ 5 := by norm_num
    rcases base_closeness_from_common_containment_base_five
        sourceScale.delta_pos.le sourceScale.rho_pos.le
        (sourceFine.tube first) (sourceFine.tube second)
        (sourceScale.coarse.tube commonParent)
        hfirstMem hsecondMem hfirstBaseNorm hsmall with
      ⟨point, hpointAxis, hbasePoint, _⟩
    let height := (sourceFine.tube first).base (2 : Fin 3)
    let firstDirection := wz1PaperDirection (sourceFine.tube first)
    let secondDirection := wz1PaperDirection (sourceFine.tube second)
    let firstSlope := (firstDirection 2)⁻¹ • firstDirection
    let secondSlope := (secondDirection 2)⁻¹ • secondDirection
    let firstZero := wz1TubeAxisZeroPoint (sourceFine.tube first)
    let secondZero := wz1TubeAxisZeroPoint (sourceFine.tube second)
    let secondAtHeight :=
      wz1PaperAxisPointAtHeight (sourceFine.tube second) height
    have hbasePointDistance :
        dist (sourceFine.tube first).base point ≤ 20 * sourceRho := by
      simpa [dist_eq_norm] using hbasePoint
    have hsameHeight : dist secondAtHeight
        (sourceFine.tube first).base ≤ 40 * sourceRho := by
      exact (wz1Paper_axisPointAtHeight_dist_point_le_two_mul
        (data.source_line_class second)
        (sourceFine.tube first).base point hpointAxis).trans (by
          linarith [hbasePointDistance])
    have hheight : |height| ≤ 5 := by
      have hcoordinate := PiLp.norm_apply_le
        (sourceFine.tube first).base (2 : Fin 3)
      rw [Real.norm_eq_abs] at hcoordinate
      exact hcoordinate.trans hfirstBaseNorm
    have hslope : ‖firstSlope - secondSlope‖ ≤ 48 * sourceRho := by
      exact (proposition63_paperSlope_sub_norm_le_six_norm_sub
        (sourceFine.tube first) (sourceFine.tube second)
        (data.source_line_class first)
        (data.source_line_class second)).trans (by
          nlinarith [hsourceDirections])
    have hfirstExpansion :
        wz1PaperAxisPointAtHeight (sourceFine.tube first) height =
          firstZero + height • firstSlope := by
      dsimp only [wz1PaperAxisPointAtHeight, firstZero, firstSlope,
        firstDirection]
      rw [div_eq_mul_inv, smul_smul]
    have hsecondExpansion : secondAtHeight =
        secondZero + height • secondSlope := by
      dsimp only [secondAtHeight, wz1PaperAxisPointAtHeight, secondZero,
        secondSlope, secondDirection]
      rw [div_eq_mul_inv, smul_smul]
    have hfirstAtHeight :
        wz1PaperAxisPointAtHeight (sourceFine.tube first) height =
          (sourceFine.tube first).base := by
      apply dist_eq_zero.mp
      apply le_antisymm
      · simpa using wz1Paper_axisPointAtHeight_dist_le_of_axis_point
          (data.source_line_class first) height 0
          (show (sourceFine.tube first).base ∈
              tubeAxisLine (sourceFine.tube first) by
            exact ⟨0, by simp⟩) (by simp [height])
      · exact dist_nonneg
    have hzeroVector : firstZero - secondZero =
        ((sourceFine.tube first).base - secondAtHeight) -
          height • (firstSlope - secondSlope) := by
      rw [← hfirstAtHeight, hfirstExpansion, hsecondExpansion]
      module
    have hzeroDistance : dist firstZero secondZero ≤ 280 * sourceRho := by
      rw [dist_eq_norm, hzeroVector]
      calc
        ‖((sourceFine.tube first).base - secondAtHeight) -
            height • (firstSlope - secondSlope)‖ ≤
          ‖(sourceFine.tube first).base - secondAtHeight‖ +
            ‖height • (firstSlope - secondSlope)‖ := norm_sub_le _ _
        _ = dist (sourceFine.tube first).base secondAtHeight +
            |height| * ‖firstSlope - secondSlope‖ := by
          rw [dist_eq_norm, norm_smul, Real.norm_eq_abs]
        _ ≤ 40 * sourceRho + 5 * (48 * sourceRho) := by
          gcongr
          simpa [dist_comm] using hsameHeight
        _ = 280 * sourceRho := by ring
    have hangle : InnerProductGeometry.angle firstDirection secondDirection ≤
        16 * sourceRho := by
      calc
        InnerProductGeometry.angle firstDirection secondDirection ≤
            (Real.pi / 2) * ‖firstDirection - secondDirection‖ :=
          angle_le_pi_div_two_mul_unit_norm_sub
            (wz1PaperDirection_norm (sourceFine.tube first))
            (wz1PaperDirection_norm (sourceFine.tube second))
        _ ≤ 2 * ‖firstDirection - secondDirection‖ := by
          exact mul_le_mul_of_nonneg_right
            (by linarith [Real.pi_lt_four]) (norm_nonneg _)
        _ ≤ 2 * (8 * sourceRho) := by gcongr
        _ = 16 * sourceRho := by ring
    change dist firstZero secondZero +
        InnerProductGeometry.angle firstDirection secondDirection ≤
      100000 * sourceRho
    linarith [sourceScale.rho_pos]
  · have hrhoLarge : 1 / 10000 < sourceRho := lt_of_not_ge hsmall
    let firstZero := wz1TubeAxisZeroPoint (sourceFine.tube first)
    let secondZero := wz1TubeAxisZeroPoint (sourceFine.tube second)
    have hfirstZeroNorm : ‖firstZero‖ ≤ 3 := by
      simpa [firstZero] using proposition63CenteredTube_midpoint_norm_le_three
        (sourceFine.tube first) (data.source_line_class first)
    have hsecondZeroNorm : ‖secondZero‖ ≤ 3 := by
      simpa [secondZero] using proposition63CenteredTube_midpoint_norm_le_three
        (sourceFine.tube second) (data.source_line_class second)
    have hzeroDistance : dist firstZero secondZero ≤ 6 := by
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith)
    have hangle : InnerProductGeometry.angle
        (wz1PaperDirection (sourceFine.tube first))
        (wz1PaperDirection (sourceFine.tube second)) ≤ 4 := by
      exact (InnerProductGeometry.angle_le_pi _ _).trans
        (le_of_lt Real.pi_lt_four)
    change dist firstZero secondZero +
        InnerProductGeometry.angle
          (wz1PaperDirection (sourceFine.tube first))
          (wz1PaperDirection (sourceFine.tube second)) ≤
      100000 * sourceRho
    linarith

/-- Two target fine tubes whose source lines lie in the same source full
fiber have line distance at most `1300000 * scale * sourceRho`.  This is the
ordinary Definition 2.12 same-fiber estimate followed by the forward
isotropic line-distance estimate. -/
theorem common_source_parent_lineDistance
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho)
    (first second : Fin sourceFine.card)
    (hparent : sourceScale.cover.parent first =
      sourceScale.cover.parent second) :
    wz1PaperLineDistance
        ((proposition63MildRescalingFamily hscale raw).tube first)
        ((proposition63MildRescalingFamily hscale raw).tube second) ≤
      1300000 * scale * sourceRho := by
  have hsourceDistance :=
    data.common_source_parent_sourceLineDistance first second hparent
  have htargetDistance :=
    proposition63_target_lineDistance_le_thirteen_mul_scale_source
    hscale center data.center_height
    (sourceFine.tube first) (sourceFine.tube second)
    ((proposition63MildRescalingFamily hscale raw).tube first)
    ((proposition63MildRescalingFamily hscale raw).tube second)
    (data.source_line_class first) (data.source_line_class second)
    (proposition63MildRescalingFamily_lineClass
      hscale raw data.raw_line_class first)
    (proposition63MildRescalingFamily_lineClass
      hscale raw data.raw_line_class second)
    (proposition63MildRescalingFamily_axis_provenance hscale raw first)
    (proposition63MildRescalingFamily_axis_provenance hscale raw second)
    (proposition63MildRescalingFamily_direction_provenance hscale raw first)
    (proposition63MildRescalingFamily_direction_provenance hscale raw second)
  calc
    wz1PaperLineDistance
          ((proposition63MildRescalingFamily hscale raw).tube first)
          ((proposition63MildRescalingFamily hscale raw).tube second) ≤
        13 * scale *
          wz1PaperLineDistance (sourceFine.tube first)
            (sourceFine.tube second) := htargetDistance
    _ ≤ 13 * scale * (100000 * sourceRho) := by
      gcongr
    _ = 1300000 * scale * sourceRho := by ring

/-- A target tube is contained in an arbitrary relabelled target
representative as soon as the explicit centered line-distance budget fits
inside the new radius.  This is the scale-flexible containment interface used
by the quotient-parent construction. -/
theorem target_carrier_subset_relabel_of_lineDistance
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho)
    {rho : ℝ} (hrho : 0 < rho)
    (first second : Fin sourceFine.card)
    (hbudget :
      (3 / 2 : ℝ) *
          wz1PaperLineDistance
            ((proposition63MildRescalingFamily hscale raw).tube first)
            ((proposition63MildRescalingFamily hscale raw).tube second) +
        scale * sourceDelta ≤ rho) :
    ((proposition63MildRescalingFamily hscale raw).tube first).carrier ⊆
      (wz2PaperRelabelTube (targetScale := rho)
        ((proposition63MildRescalingFamily hscale raw).tube second)).carrier := by
  let targetFine := proposition63MildRescalingFamily hscale raw
  exact proposition63_centered_carrier_subset_relabel_of_lineDistance
    (mul_pos (lt_of_lt_of_le zero_lt_one hscale) sourceScale.delta_pos)
    hrho (targetFine.tube first) (targetFine.tube second)
    (proposition63MildRescalingFamily_lineClass
      hscale raw data.raw_line_class first)
    (proposition63MildRescalingFamily_lineClass
      hscale raw data.raw_line_class second)
    (proposition63MildRescalingFamily_centered
      hscale raw data.raw_line_class first)
    (proposition63MildRescalingFamily_centered
      hscale raw data.raw_line_class second)
    hbudget

/-- Every target fine tube is strictly contained in the radius-enlarged
centered image-line representative of its source full fiber. -/
theorem assigned_containment
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho)
    (target : Fin sourceFine.card) :
    ((proposition63MildRescalingFamily hscale raw).tube target).carrier ⊆
      (data.parentFamily.tube
        (sourceScale.cover.parent target)).carrier := by
  have hdistance := data.common_source_parent_lineDistance target
    (data.sourceRepresentative (sourceScale.cover.parent target))
    (by rw [data.sourceRepresentative_parent])
  have htargetLine := proposition63MildRescalingFamily_lineClass
    hscale raw data.raw_line_class
  have hcontain := proposition63_centered_carrier_subset_relabel_of_lineDistance
    (mul_pos (lt_of_lt_of_le zero_lt_one hscale) sourceScale.delta_pos)
    data.target_rho_pos
    ((proposition63MildRescalingFamily hscale raw).tube target)
    ((proposition63MildRescalingFamily hscale raw).tube
      (data.sourceRepresentative (sourceScale.cover.parent target)))
    (htargetLine target)
    (htargetLine (data.sourceRepresentative
      (sourceScale.cover.parent target)))
    (proposition63MildRescalingFamily_centered
      hscale raw data.raw_line_class target)
    (proposition63MildRescalingFamily_centered
      hscale raw data.raw_line_class
        (data.sourceRepresentative (sourceScale.cover.parent target)))
    (hdistance |> fun h => data.target_rho_budget.trans' <| by
      gcongr)
  exact hcontain

/-- The preliminary parent assignment determined by the source strict cover.
Strong separation is intentionally not included here. -/
def toPreAssignedParentCover
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho) :
    let targetFine := proposition63MildRescalingFamily hscale raw
    (∀ source,
      (targetFine.tube source).carrier ⊆
        (data.parentFamily.tube
          (sourceScale.cover.parent source)).carrier) ∧
      WZ1PaperIsLineClass targetFine ∧
      WZ1PaperIsLineClass data.parentFamily ∧
      (∀ source, ‖wz2PaperTubeMidpoint (targetFine.tube source)‖ ≤ 3) := by
  dsimp only
  exact ⟨data.assigned_containment,
    proposition63MildRescalingFamily_lineClass
      hscale raw data.raw_line_class,
    data.parentFamily_lineClass,
    proposition63MildRescalingFamily_midpoint_local
      hscale raw data.raw_line_class⟩

/-- A strongly separated subfamily of the preliminary parents yields a
literal Definition 2.12 cover.  This is the exact post-selection interface
used by the finite nearby-scale schedule. -/
def toPartitioningCoverOfSeparated
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho)
    (selected : WZ2PaperPureTubeSubfamily
      (proposition63MildRescalingFamily hscale raw))
    (selectedParents : WZ2PaperPureTubeSubfamily data.parentFamily)
    (assignedParent : Fin selected.family.card →
      Fin selectedParents.family.card)
    (hassignedSurjective : Function.Surjective assignedParent)
    (hassignedAmbient : ∀ source,
      selectedParents.embedding (assignedParent source) =
        sourceScale.cover.parent (selected.embedding source))
    (hseparated : ∀ first second : Fin selectedParents.family.card,
      first ≠ second →
        2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant * targetRho <
          wz1PaperLineDistance
            (selectedParents.family.tube first)
            (selectedParents.family.tube second)) :
    WZ2PaperPurePartitioningCover
      selected.family selectedParents.family where
  covers source := by
    refine ⟨assignedParent source, ?_⟩
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    rw [selected.tube_eq, selectedParents.tube_eq, hassignedAmbient]
    exact data.assigned_containment (selected.embedding source)
  doubled_fibers_disjoint :=
    wz2_paper_localized_ordinary_dilatedFiberIndices_disjoint
      (mul_pos (lt_of_lt_of_le zero_lt_one hscale) sourceScale.delta_pos)
      data.target_rho_pos
      ((proposition63MildRescalingFamily_lineClass
        hscale raw data.raw_line_class).subfamily selected.toTubeSubfamily)
      (data.parentFamily_lineClass.subfamily selectedParents.toTubeSubfamily)
      (fun source => by
        change ‖wz2PaperTubeMidpoint (selected.family.tube source)‖ ≤ 3
        rw [selected.tube_eq]
        exact proposition63MildRescalingFamily_midpoint_local
          hscale raw data.raw_line_class (selected.embedding source))
      hseparated

/-- The same separation certificate also gives ordinary essential
distinctness for the retained target fine family. -/
theorem selected_ordinaryDistinct_of_separated
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (data : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho)
    (selected : WZ2PaperPureTubeSubfamily
      (proposition63MildRescalingFamily hscale raw))
    (hseparated : ∀ first second : Fin selected.family.card,
      first ≠ second →
        wz2PaperLocalizedDoubledFiberLineDistanceConstant *
            (scale * sourceDelta) <
          wz1PaperLineDistance
            (selected.family.tube first)
            (selected.family.tube second)) :
    WZ2PaperOrdinaryIsEssentiallyDistinct selected.family := by
  apply wz2_paper_localized_ordinary_isEssentiallyDistinct
    (mul_pos (lt_of_lt_of_le zero_lt_one hscale) sourceScale.delta_pos)
    ((proposition63MildRescalingFamily_lineClass
      hscale raw data.raw_line_class).subfamily selected.toTubeSubfamily)
  · intro source
    change ‖wz2PaperTubeMidpoint (selected.family.tube source)‖ ≤ 3
    rw [selected.tube_eq]
    exact proposition63MildRescalingFamily_midpoint_local
      hscale raw data.raw_line_class (selected.embedding source)
  · exact hseparated

end Proposition63MildRescalingParentCoverData

end Kakeya.Assouad.PureWZ2

end
