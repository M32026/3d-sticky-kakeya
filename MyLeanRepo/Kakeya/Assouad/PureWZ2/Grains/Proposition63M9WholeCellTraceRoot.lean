import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9WholeCellTraceSource
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9SameExtremizerAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9TrivialTopLevelCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63TopLevelCWA
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRootCover

/-!
# Root data from the whole-cell ordinary trace

This file names the charted ordinary source and its public cropped ambient,
then packages the geometric receipts needed at the first-chart re-entry.
Scalar scheduling is deliberately kept outside this interface.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

variable
    {delta Delta sigma stickyLoss localLoss commonSliceLoss chartLoss
      tau epsilon₁ epsilon₃ coefficient initialInputLoss
      initialOutputLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration
      sigma initialInputLoss delta}
    {firstScale : WZ2PaperRequestedScale delta}
    {logExponent normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := initialOutputLoss) initialSource
      normalizationExponent)
    {firstSticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      initialNormalized.croppedRefined firstScale logExponent}
    {retainedFactor : ENNReal}
    (first : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := coefficient)
      firstSticky Delta retainedFactor)
    (output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := chartLoss)
      (first.wholeCellShading initialNormalized)
      (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos)
    (massLower :
      Kakeya.realRpowENN (delta / firstScale.1) chartLoss *
            output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / firstScale.1 : ℝ) ^ 2)) *
          (first.wholeCellOrdinaryTrace initialNormalized).mass)

/-- The charted ordinary extremal source obtained from the exact whole-cell
normalization trace. -/
noncomputable def Proposition63FirstChartData.wholeCellTraceOrdinarySource :
    PureWZ2ExtremalConfiguration sigma chartLoss
      (delta / firstScale.1) :=
  first.wholeCellChartOrdinaryExtremalSourceOfTraceMass
    initialNormalized output massLower

/-- The selected horizontal-chart transport of the public cropped literal
shading attached to the same whole-cell output. -/
def Proposition63FirstChartData.wholeCellTraceAmbient :
    WZ1PaperTubeShading
      (first.wholeCellTraceOrdinarySource
        initialNormalized output massLower).family :=
  first.chartSelection.chartLabel.chart.transportPaperShading
    (output.rescalingCertificate.publicShading
      output.literalShading.targetShading)

/-- Minimal geometric root package for the whole-cell trace source. -/
structure Proposition63M9WholeCellTraceRootData : Prop where
  source_sub_ambient : ∀ index,
    (first.wholeCellTraceOrdinarySource
        initialNormalized output massLower).shading.carrier index ⊆
      (first.wholeCellTraceAmbient
        initialNormalized output massLower).carrier index
  source_axial_window : ∀ index point,
    point ∈ (first.wholeCellTraceOrdinarySource
        initialNormalized output massLower).shading.carrier index →
      |point (2 : Fin 3)| ≤ 1 / 25
  ambient_cubical : WZ1PaperIsCubicalShading
    (first.wholeCellTraceAmbient initialNormalized output massLower)
  ambient_extremal : WZ2PaperCroppedIsExtremal sigma chartLoss
    (first.wholeCellTraceOrdinarySource
      initialNormalized output massLower).family
    (first.wholeCellTraceAmbient initialNormalized output massLower)
  ambient_line_class : WZ1PaperIsLineClass
    (first.wholeCellTraceOrdinarySource
      initialNormalized output massLower).family
  /-- The exact literal unit-rescaling axis, followed by the selected
  horizontal chart, keeps every ambient paper direction in the sharp
  `pi / 6` vertical cone. -/
  ambient_direction_vertical : ∀ index,
    Real.sqrt 3 / 2 ≤
      wz1PaperDirection
        ((first.wholeCellTraceOrdinarySource
          initialNormalized output massLower).family.tube index)
          (2 : Fin 3)

/-- Assemble the whole-cell trace root directly from the existing exact-trace
source and horizontal-chart transport lemmas. -/
theorem proposition63_m9_wholeCellTraceRoot :
    Proposition63M9WholeCellTraceRootData
      initialNormalized first output massLower := by
  let chart := first.chartSelection.chartLabel.chart
  have ambientExtremal : WZ2PaperCroppedIsExtremal sigma chartLoss
      (first.wholeCellTraceOrdinarySource
        initialNormalized output massLower).family
      (first.wholeCellTraceAmbient
        initialNormalized output massLower) := by
    exact chart.transportPaperCroppedExtremal output.extremal
  refine {
    source_sub_ambient := ?_
    source_axial_window := ?_
    ambient_cubical := ambientExtremal.cubical
    ambient_extremal := ambientExtremal
    ambient_line_class := ?_
    ambient_direction_vertical := ?_
  }
  · exact proposition63ChartOrdinaryExtremalSourceOfTraceMass_sub_normalized
      initialNormalized
      (first.wholeCellSelected initialNormalized)
      (first.wholeCellShading initialNormalized)
      (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos output massLower chart
  · exact proposition63ChartOrdinaryExtremalSourceOfTraceMass_axial_window
      initialNormalized
      (first.wholeCellSelected initialNormalized)
      (first.wholeCellShading initialNormalized)
      (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos
      (firstSticky.cover.coarse_line_class first.metricFiber.parent)
      output massLower chart
  · exact chart.transportFamily_lineClass
      output.rescalingCertificate.publicFamily
      (output.rescalingCertificate.publicFamily_line_class
        output.familyData.target_line_class)
  · intro index
    let literalIndex := output.rescalingCertificate.section6Index.symm index
    have hsection :
        output.rescalingCertificate.section6Index literalIndex = index :=
      output.rescalingCertificate.section6Index.apply_symm_apply index
    have hpublicLine : WZ1PaperTubeInLineClass
        (output.rescalingCertificate.publicFamily.tube index) :=
      output.rescalingCertificate.publicFamily_line_class
        output.familyData.target_line_class index
    have hliteralLine : WZ1PaperTubeInLineClass
        (output.familyData.targetFamily.tube literalIndex) :=
      output.familyData.target_line_class literalIndex
    have hpublicAxis :
        tubeAxisLine (output.rescalingCertificate.publicFamily.tube index) =
          tubeAxisLine (output.familyData.targetFamily.tube literalIndex) := by
      rw [← hsection]
      exact output.rescalingCertificate.same_axis literalIndex
    have hpublicDirection :
        wz1PaperDirection
            (output.rescalingCertificate.publicFamily.tube index) =
          wz1PaperDirection
            (output.familyData.targetFamily.tube literalIndex) :=
      paperDirection_eq_of_same_axis hpublicLine hliteralLine hpublicAxis
    have hliteralVertical : Real.sqrt 3 / 2 ≤
        wz1PaperDirection
            (output.familyData.targetFamily.tube literalIndex)
          (2 : Fin 3) := by
      exact literal_target_paperDirection_vertical_ge_sqrt_three_half
        firstSticky.coarse_extremal.delta_pos
        (firstSticky.coarse_extremal.delta_le_one)
        (firstSticky.cover.fine_line_class.subfamily
          first.metricFiber.fiberFamily
          (output.familyData.sourceIndex literalIndex))
        (by
          rw [first.metricFiber.fiberFamily.tube_eq]
          apply (mem_wz2PaperFullFiberIndices_iff
            first.metricFiber.parent
            (first.metricFiber.fiberFamily.embedding
              (output.familyData.sourceIndex literalIndex))).mp
          exact Finset.orderEmbOfFin_mem _ _ _)
        hliteralLine (output.familyData.target_axis literalIndex)
    change Real.sqrt 3 / 2 ≤
      wz1PaperDirection
        (transportTube chart.isometry
          (output.rescalingCertificate.publicFamily.tube index)) 2
    rw [chart.paperDirection_transportTube,
      chart.isometry_preserves_coord2, hpublicDirection]
    exact hliteralVertical

/-- Any tube subfamily selected from the first charted trace family retains
the exact literal-image vertical-direction margin. -/
theorem Proposition63M9WholeCellTraceRootData.subfamily_direction_vertical
    (rootData : Proposition63M9WholeCellTraceRootData
      initialNormalized first output massLower)
    (selected : Kakeya.Streamlined.TubeSubfamily
      (first.wholeCellTraceOrdinarySource
        initialNormalized output massLower).family)
    (index : Fin selected.family.card) :
    Real.sqrt 3 / 2 ≤
      wz1PaperDirection (selected.family.tube index) (2 : Fin 3) := by
  rw [selected.tube_eq]
  exact rootData.ambient_direction_vertical (selected.embedding index)

/-- The charted public ambient has a family-free top-level CWA constant.
This uses only its line-class geometry and the quadratic volume floor of one
cropped paper tube; no support or rescaling-certificate strengthening is
needed. -/
theorem Proposition63FirstChartData.wholeCellTraceAmbient_topLevelCWA
    (ratio_small : delta / firstScale.1 ≤ 1 / 12) :
    WZ2PaperConvexWolffBound
      (first.wholeCellTraceOrdinarySource
        initialNormalized output massLower).family
      (Kakeya.realRpowENN (delta / firstScale.1) (-2 : ℝ)) := by
  exact wz2_paper_lineClass_trivial_topLevelCWA
    (div_pos first.delta_pos
      (first.delta_pos.trans_le firstScale.2.1))
    ratio_small
    (first.wholeCellTraceOrdinarySource
      initialNormalized output massLower).family
    (proposition63_m9_wholeCellTraceRoot
      initialNormalized first output massLower).ambient_line_class

end Kakeya.Assouad.PureWZ2
