import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSaturatedNeighborhoodCarrier
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinAnchoredPreparationABI
import MyLeanRepo.Kakeya.Assouad.WZ1.GlobalGrainDirectionGeometry

/-!
# Direct-rich graph preparation on the saturated neighborhood

The graph carrier is the same-height saturation of the exact aggregate source.
It retains the saturation volume lower bound, while every point has a genuine
source witness at the same height.  These witnesses transfer all-height global
AD and fixed-line localization at graph scale `256 * rho`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

namespace PureWZ2PreCommonBinGlobalGrainNeighborhoodData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss : ℝ}
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

abbrev graphScale : ℝ := neighborhood.saturatedGraphScale

theorem graphScale_pos : 0 < neighborhood.graphScale :=
  neighborhood.saturatedGraphScale_pos

/-- Finite-tube presentation of the auxiliary same-height saturation.  This
presentation is used only by the combinatorial graph API; it does not assert
CWA, extremality, or original-tube provenance. -/
def graphShadow : Kakeya.Streamlined.TubeShading
    neighborhood.saturatedGraphFamily :=
  neighborhood.saturatedGraphShading

theorem graphShadow_union :
    neighborhood.graphShadow.union =
      neighborhood.saturatedUnion :=
  neighborhood.saturatedGraphShading_union

theorem graph_union_height :
    ∀ point ∈ neighborhood.graphShadow.union,
      point (2 : Fin 3) ∈
        Set.Ico
          ((neighborhood.heightIndex.1 : ℝ) * Real.sqrt rho)
          ((neighborhood.heightIndex.1 : ℝ) * Real.sqrt rho +
            Real.sqrt rho) := by
  intro point hpoint
  rw [neighborhood.graphShadow_union] at hpoint
  exact neighborhood.saturatedUnion_height point hpoint

theorem graph_fixedLine_localization
    (hheightAbsorb :
      neighborhood.saturatedGraphScale + 2 * Real.sqrt rho ≤
        16 * Real.sqrt rho) :
    ∀ point ∈ neighborhood.graphShadow.union,
      |inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope (point (2 : Fin 3)))) -
        neighborhood.lineLevel| ≤
      16 * Real.sqrt rho := by
  intro point hpoint
  rw [neighborhood.graphShadow_union] at hpoint
  rcases neighborhood.saturatedUnion_exists_source_same_height hpoint with
    ⟨y, hy, _hpointParent, sourcePoint, hsourcePullback, hheightEq, hdist⟩
  have hfixed := neighborhood.pullback_global_line_localized
    y hy sourcePoint hsourcePullback
  have hfixed' :
      |inner ℝ sourcePoint
          (globalGrainDirection
            (current.grain.globalGrains.slope neighborhood.lineHeight)) -
        neighborhood.lineLevel| ≤
      14 * Real.sqrt rho := by
    simpa only [pullback.sqrtRequested_eq] using hfixed
  have hsource := neighborhood.aggregate_sub_source.union_subset (by
    rw [neighborhood.aggregate_union_eq]
    exact Set.mem_iUnion₂.mpr ⟨y, hy, hsourcePullback⟩)
  have hbox := shading_union_subset_axisBox
    (neighborhood.saturatedUnion_subset_secondRefined hpoint)
  have hpointHeight : point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
  have hheight := neighborhood.graph_union_height point (by
    rw [neighborhood.graphShadow_union]
    exact hpoint)
  have hheightDist :
      |point (2 : Fin 3) - neighborhood.lineHeight| ≤ Real.sqrt rho := by
    have hline := neighborhood.lineHeight_mem_slab
    rw [abs_le]
    constructor <;> linarith [hheight.1, hheight.2, hline.1, hline.2]
  have hslopeDifference :
      |current.grain.globalGrains.slope (point (2 : Fin 3)) -
          current.grain.globalGrains.slope neighborhood.lineHeight| ≤
        Real.sqrt rho := by
    have hlip := current.grain.globalGrains.slope_lipschitz.dist_le_mul
      (point (2 : Fin 3)) hpointHeight
      neighborhood.lineHeight neighborhood.lineHeight_mem
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    exact hlip.trans hheightDist
  have hyCoord : |point (1 : Fin 3)| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
  have hprojectionDifference :
      |inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope (point (2 : Fin 3)))) -
          inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope neighborhood.lineHeight))| ≤
        Real.sqrt rho := by
    have hformula :
        inner ℝ point
              (globalGrainDirection
                (current.grain.globalGrains.slope (point (2 : Fin 3)))) -
            inner ℝ point
              (globalGrainDirection
          (current.grain.globalGrains.slope neighborhood.lineHeight)) =
          (current.grain.globalGrains.slope (point (2 : Fin 3)) -
              current.grain.globalGrains.slope neighborhood.lineHeight) *
            point (1 : Fin 3) := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      ring
    rw [hformula, abs_mul]
    calc
      _ ≤ Real.sqrt rho * 1 := by gcongr
      _ = Real.sqrt rho := by ring
  have hsourceProjectionDifference :
      |inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope neighborhood.lineHeight)) -
          inner ℝ sourcePoint
            (globalGrainDirection
              (current.grain.globalGrains.slope neighborhood.lineHeight))| ≤
        8 * rho := by
    rw [show inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope neighborhood.lineHeight)) -
        inner ℝ sourcePoint
          (globalGrainDirection
            (current.grain.globalGrains.slope neighborhood.lineHeight)) =
      inner ℝ (point - sourcePoint)
        (globalGrainDirection
          (current.grain.globalGrains.slope neighborhood.lineHeight)) by
      simp [inner_sub_left]]
    calc
      _ ≤ ‖point - sourcePoint‖ *
          ‖globalGrainDirection
            (current.grain.globalGrains.slope neighborhood.lineHeight)‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (2 * rho) * 4 := by
        exact mul_le_mul
          (by simpa [dist_eq_norm] using hdist)
          (globalGrainDirection_norm_le_4
            (current.grain.globalGrains.slope_bound
              neighborhood.lineHeight neighborhood.lineHeight_mem))
          (norm_nonneg _)
          (by
            have hrho : 0 < rho := by
              rw [← pullback.rhoRequested_eq]
              exact twoScale.first.publicSticky.coarse_extremal.delta_pos
            positivity)
      _ = 8 * rho := by ring
  have hpointFixed :
      |inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope neighborhood.lineHeight)) -
          neighborhood.lineLevel| ≤
        8 * rho + 14 * Real.sqrt rho := by
    calc
      _ ≤ |inner ℝ point
              (globalGrainDirection
                (current.grain.globalGrains.slope neighborhood.lineHeight)) -
            inner ℝ sourcePoint
              (globalGrainDirection
                (current.grain.globalGrains.slope neighborhood.lineHeight))| +
          |inner ℝ sourcePoint
              (globalGrainDirection
                (current.grain.globalGrains.slope neighborhood.lineHeight)) -
            neighborhood.lineLevel| := by
        simpa using abs_sub_le
          (inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope neighborhood.lineHeight)))
          (inner ℝ sourcePoint
            (globalGrainDirection
              (current.grain.globalGrains.slope neighborhood.lineHeight)))
          neighborhood.lineLevel
      _ ≤ 8 * rho + 14 * Real.sqrt rho :=
        add_le_add hsourceProjectionDifference hfixed'
  calc
    |inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope (point (2 : Fin 3)))) -
        neighborhood.lineLevel| ≤
      |inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope (point (2 : Fin 3)))) -
          inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope neighborhood.lineHeight))| +
        |inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope neighborhood.lineHeight)) -
          neighborhood.lineLevel| := by
      simpa using abs_sub_le
        (inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope (point (2 : Fin 3)))))
        (inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope neighborhood.lineHeight)))
        neighborhood.lineLevel
    _ ≤ Real.sqrt rho + (8 * rho + 14 * Real.sqrt rho) :=
      add_le_add hprojectionDifference hpointFixed
    _ ≤ 16 * Real.sqrt rho := by
      have hrho : 0 < rho := by
        rw [← pullback.rhoRequested_eq]
        exact twoScale.first.publicSticky.coarse_extremal.delta_pos
      have hsmall : 8 * rho ≤ Real.sqrt rho := by
        have hgraph : 256 * rho ≤ 14 * Real.sqrt rho := by
          simpa only [saturatedGraphScale] using
            (show neighborhood.saturatedGraphScale ≤ 14 * Real.sqrt rho by
              linarith [hheightAbsorb])
        nlinarith
      linarith

/-- Exact all-height global input on the genuine aggregate source. -/
noncomputable def graphInput
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : neighborhood.saturatedGraphScale ≤ 1) :
    PureWZ2AnchoredGraphGlobalInput
      (delta := neighborhood.saturatedGraphScale)
      (rho := neighborhood.saturatedGraphScale) (sigma := sigma)
      neighborhood.graphShadow
      (160 * Kakeya.realRpowENN delta (-inputLoss)) where
  rho_pos := neighborhood.saturatedGraphScale_pos
  delta_le_rho := le_rfl
  rho_le_one := hgraphOne
  sourceSlope := current.grain.globalGrains.slope
  sourceSlope_lipschitz := current.grain.globalGrains.slope_lipschitz
  sourceSlope_bound := current.grain.globalGrains.slope_bound
  constant_ne_top := ENNReal.mul_ne_top (by norm_num)
    (by simp [Kakeya.realRpowENN])
  shadow_ball := by
    intro point hpoint
    rw [neighborhood.graphShadow_union] at hpoint
    have hcoarse := neighborhood.saturatedUnion_subset_secondRefined hpoint
    have hnorm := norm_le_two_of_mem_paperShading hcoarse
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  shadow_coordinate := by
    intro point hpoint coordinate
    rw [neighborhood.graphShadow_union] at hpoint
    have hcoarse := neighborhood.saturatedUnion_subset_secondRefined hpoint
    have hbox := shading_union_subset_axisBox hcoarse
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  exactAD := by
    intro z hz
    rw [neighborhood.graphShadow_union]
    exact neighborhood.saturatedUnion_exactAD hbridge hgraphOne z hz

/-- Graph preparation on the auxiliary same-height saturation.  The scale
`256*rho` is only the finite graph discretization scale; the saturated local
grains that certify normal-first remain at scale `4*rho`. -/
theorem graphPreparation
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : neighborhood.saturatedGraphScale ≤ 1)
    (hheightAbsorb :
      neighborhood.saturatedGraphScale + 2 * Real.sqrt rho ≤
        16 * Real.sqrt rho) :
    Nonempty
      (PureWZ2AnchoredGraphPreparationData
        (neighborhood.graphInput hbridge hgraphOne :
          PureWZ2AnchoredGraphGlobalInput
            (delta := neighborhood.saturatedGraphScale)
            (rho := neighborhood.saturatedGraphScale)
            (sigma := sigma) neighborhood.graphShadow
            (160 * Kakeya.realRpowENN delta (-inputLoss)))) := by
  apply pureWZ2_anchoredGraphPreparation
    (neighborhood.graphInput hbridge hgraphOne)
  · intro global hslope
    let root := Real.sqrt rho
    let slabLeft :=
      (neighborhood.heightIndex.1 : ℝ) * root
    let left := slabLeft - neighborhood.saturatedGraphScale / 2
    have hrho : 0 < rho := by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos
    have hroot : 0 < root := Real.sqrt_pos.mpr hrho
    have hsqrtGraph :
        Real.sqrt neighborhood.saturatedGraphScale = 16 * root := by
      dsimp only [saturatedGraphScale, root]
      rw [Real.sqrt_mul (by norm_num),
        show Real.sqrt (256 : ℝ) = 16 by norm_num]
    refine ⟨left, ?_⟩
    intro cell hcell
    have hactive :=
      (wz1Lemma23_mem_active_iff neighborhood.graphShadow
        neighborhood.saturatedGraphScale_pos cell).mp hcell
    rcases hactive.2 with ⟨point, hpoint, hpointCell⟩
    have hheight := neighborhood.graph_union_height point hpoint
    have hcenter :=
      ((wz1_lemma23_snapped_cell_geometry neighborhood.saturatedGraphScale
        neighborhood.saturatedGraphScale_pos hgraphOne).2.1
        cell point hpointCell).1 (2 : Fin 3)
    rw [abs_le] at hcenter
    constructor
    · dsimp only [left, slabLeft]
      linarith [hheight.1, hcenter.2]
    · dsimp only [left, slabLeft]
      rw [hsqrtGraph]
      linarith [hheight.2, hcenter.1, hheightAbsorb]
  · intro global hslope
    have hsqrtGraph :
        Real.sqrt neighborhood.saturatedGraphScale = 16 * Real.sqrt rho := by
      dsimp only [saturatedGraphScale]
      rw [Real.sqrt_mul (by norm_num),
        show Real.sqrt (256 : ℝ) = 16 by norm_num]
    refine ⟨fun _ => neighborhood.lineLevel, ?_⟩
    intro heightIndex hheightIndex
    rintro value ⟨point, hpoint, rfl⟩
    have hfixed := neighborhood.graph_fixedLine_localization hheightAbsorb
      point hpoint.1
    rw [Metric.mem_closedBall, Real.dist_eq, hslope]
    change
      |inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope
              (global.selectedHeight heightIndex))) -
        neighborhood.lineLevel| ≤
        Real.sqrt neighborhood.saturatedGraphScale
    rw [← hpoint.2, hsqrtGraph]
    exact hfixed.trans (by
      have hrho : 0 < rho := by
        rw [← pullback.rhoRequested_eq]
        exact twoScale.first.publicSticky.coarse_extremal.delta_pos
      nlinarith [Real.sqrt_pos.mpr hrho])

end PureWZ2PreCommonBinGlobalGrainNeighborhoodData

end Kakeya.Assouad

end
