import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCWASchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalBallCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicTubeParameterForward
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LineClassNormalizationTubeParameters

/-!
# Geometric inputs for the direct half-offset terminal CWA schedule

This module supplies the fixed line-distortion factor and the elementary
line-class geometry required by `directHalfOffsetTerminal_cwa_schedule`.  It
does not construct the packetwise actual-John estimate used later to close
nearby CWA.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2DirectCommonYSourceAssembly
namespace TerminalGeometry
namespace PureWZ2ExternalWeightRegularizationData

variable {logExponent : ℕ} {sigma epsilon delta : ℝ}
  {commonSource : PureWZ2DirectCommonYSourceAssembly
    logExponent sigma epsilon delta}

/-- Uniform distortion of the paper line metric under the actual triangular
half-offset map followed by `diag(lambda, 1, lambda)`. -/
def directHalfOffsetTerminalLineFactor : ℝ :=
  288 * pureWZ2DirectHalfOffsetTerminalLambda

theorem directHalfOffsetTerminalLineFactor_nonneg :
    0 ≤ directHalfOffsetTerminalLineFactor := by
  unfold directHalfOffsetTerminalLineFactor
  positivity [pureWZ2DirectHalfOffsetTerminalLambda_pos]

theorem directHalfOffsetTerminal_source_line_class
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount) :
    WZ1PaperIsLineClass regularization.selected.family := by
  exact commonSource.halfOffsetAssembly.cfg.line_class.subfamily
    regularization.selected

theorem directHalfOffsetTerminal_source_base_le_five
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount) :
    ∀ source, ‖(regularization.selected.family.tube source).base‖ ≤ 5 := by
  intro source
  rw [regularization.selected.tube_eq]
  exact (commonSource.halfOffsetAssembly.cfg.bounded_base _).trans (by norm_num)

theorem directHalfOffsetTerminal_preTarget_line_class
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount) :
    WZ1PaperIsLineClass
      (DirectHalfOffsetTerminalRequestedCWAPreTarget
        (commonSource := commonSource) regularization) := by
  exact (TerminalGeometry.line_class_subfamily commonSource terminal
    cleanup.family).subfamily
      (halfOffsetTerminalCleanupTargetSubfamily
        (commonSource := commonSource) regularization)

theorem directHalfOffsetTerminal_preTarget_centered
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount)
    (index : Fin (DirectHalfOffsetTerminalRequestedCWAPreTarget
      (commonSource := commonSource) regularization).card) :
    pureWZ2PaperCenteredTube
        ((DirectHalfOffsetTerminalRequestedCWAPreTarget
          (commonSource := commonSource) regularization).tube index) =
      (DirectHalfOffsetTerminalRequestedCWAPreTarget
        (commonSource := commonSource) regularization).tube index := by
  let target := halfOffsetTerminalCleanupTargetPreimage
    (commonSource := commonSource) regularization index
  let ambient := cleanup.originalIndex commonSource target
  change pureWZ2PaperCenteredTube (terminal.centeredFamily.tube ambient) =
    terminal.centeredFamily.tube ambient
  change pureWZ2PaperCenteredTube
      (pureWZ2PaperCenteredTube (terminal.family.tube ambient)) =
    pureWZ2PaperCenteredTube (terminal.family.tube ambient)
  exact pureWZ2PaperCenteredTube_idempotent _
    (TerminalGeometry.line_class commonSource terminal ambient)

theorem directHalfOffsetTerminal_preTarget_midpoint_le_three
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount) :
    ∀ target, ‖wz2PaperTubeMidpoint
      ((DirectHalfOffsetTerminalRequestedCWAPreTarget
        (commonSource := commonSource) regularization).tube target)‖ ≤ 3 := by
  intro target
  rw [← directHalfOffsetTerminal_preTarget_centered regularization target]
  exact pureWZ2PaperCenteredTube_midpoint_norm_le_three _
    (directHalfOffsetTerminal_preTarget_line_class regularization target)

theorem directHalfOffsetTerminal_preTarget_packing_distinct
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount) :
    WZ1PaperIsEssentiallyDistinct
      (wz2PaperRelabelFamily
        (sourceScale := terminal.targetDelta)
        (targetScale := (2 / 3 : ℝ) * terminal.targetDelta)
        (DirectHalfOffsetTerminalRequestedCWAPreTarget
          (commonSource := commonSource) regularization)) := by
  intro first second hne
  change (2 / 3 : ℝ) * terminal.targetDelta <
    wz1PaperLineDistance
      (wz2PaperRelabelTube
        ((DirectHalfOffsetTerminalRequestedCWAPreTarget
          (commonSource := commonSource) regularization).tube first))
      (wz2PaperRelabelTube
        ((DirectHalfOffsetTerminalRequestedCWAPreTarget
          (commonSource := commonSource) regularization).tube second))
  rw [wz2PaperRelabelTube_lineDistance_both]
  have hpaper := pureWZ2_centered_ordinaryDistinct_packingFamily_paperDistinct
    commonSource.halfOffsetLineClassTargetDelta_pos
    (directHalfOffsetTerminal_preTarget_line_class regularization) (by
      intro i j hij
      simpa only [directHalfOffsetTerminal_preTarget_centered regularization i,
        directHalfOffsetTerminal_preTarget_centered regularization j] using
        halfOffsetTerminalCleanupTargetSubfamily_distinct
          (commonSource := commonSource) regularization i j hij)
  have hraw := hpaper first second hne
  change (2 / 3 : ℝ) * terminal.targetDelta <
    wz1PaperLineDistance
      (wz2PaperRelabelTube
        (pureWZ2PaperCenteredTube
          ((DirectHalfOffsetTerminalRequestedCWAPreTarget
            (commonSource := commonSource) regularization).tube first)))
      (wz2PaperRelabelTube
        (pureWZ2PaperCenteredTube
          ((DirectHalfOffsetTerminalRequestedCWAPreTarget
            (commonSource := commonSource) regularization).tube second))) at hraw
  rw [wz2PaperRelabelTube_lineDistance_both,
    pureWZ2PaperCenteredTube_lineDistance _ _
      (directHalfOffsetTerminal_preTarget_line_class regularization first)
      (directHalfOffsetTerminal_preTarget_line_class regularization second)] at hraw
  exact hraw

theorem directHalfOffsetTerminal_preTarget_carrier_subset_relabel
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount) :
    ∀ {rho : ℝ}, 0 < rho → ∀ first second,
      (3 / 2 : ℝ) * wz1PaperLineDistance
          ((DirectHalfOffsetTerminalRequestedCWAPreTarget
            (commonSource := commonSource) regularization).tube first)
          ((DirectHalfOffsetTerminalRequestedCWAPreTarget
            (commonSource := commonSource) regularization).tube second) +
        terminal.targetDelta ≤ rho →
      ((DirectHalfOffsetTerminalRequestedCWAPreTarget
        (commonSource := commonSource) regularization).tube first).carrier ⊆
        (wz2PaperRelabelTube (targetScale := rho)
          ((DirectHalfOffsetTerminalRequestedCWAPreTarget
            (commonSource := commonSource) regularization).tube second)).carrier := by
  intro rho hrho first second hbudget
  have hcontain := pureWZ2_centered_carrier_subset_relabel_of_lineDistance
    commonSource.halfOffsetLineClassTargetDelta_pos hrho
    ((DirectHalfOffsetTerminalRequestedCWAPreTarget
      (commonSource := commonSource) regularization).tube first)
    ((DirectHalfOffsetTerminalRequestedCWAPreTarget
      (commonSource := commonSource) regularization).tube second) hbudget
  rw [directHalfOffsetTerminal_preTarget_centered regularization first,
    directHalfOffsetTerminal_preTarget_centered regularization second] at hcontain
  exact hcontain

/-- The final source regularization uses the ambient source family with no
geometric change, so its selected tubes retain their literal terminal axes. -/
theorem directHalfOffsetTerminal_preTarget_axis_source
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount)
    (target : Fin (DirectHalfOffsetTerminalRequestedCWAPreTarget
      (commonSource := commonSource) regularization).card) :
    tubeAxisLine
        ((DirectHalfOffsetTerminalRequestedCWAPreTarget
          (commonSource := commonSource) regularization).tube target) =
      TerminalGeometry.totalAffineMap commonSource terminal ''
        tubeAxisLine (regularization.selected.family.tube target) := by
  let cleanupTarget := halfOffsetTerminalCleanupTargetPreimage
    (commonSource := commonSource) regularization target
  have htarget := TerminalGeometry.centeredFamily_axis_totalAffineMap
    commonSource terminal (cleanup.originalIndex commonSource cleanupTarget)
  have hsource := halfOffsetTerminalCleanupTargetPreimage_source
    (commonSource := commonSource) regularization target
  change centeredSourceParent commonSource terminal
      (cleanup.originalIndex commonSource cleanupTarget) =
    regularization.selected.embedding target at hsource
  change tubeAxisLine
      (cleanup.family.family.tube cleanupTarget) =
    TerminalGeometry.totalAffineMap commonSource terminal ''
      tubeAxisLine (regularization.selected.family.tube target)
  change tubeAxisLine
      (terminal.centeredFamily.tube
        (cleanup.originalIndex commonSource cleanupTarget)) = _
  have htube :
      (conflictSourceFamily commonSource).tube
          (centeredSourceParent commonSource terminal
            (cleanup.originalIndex commonSource cleanupTarget)) =
        regularization.selected.family.tube target := by
    rw [hsource]
    exact (regularization.selected.tube_eq target).symm
  rw [htarget, htube]

private theorem lineClassNormalizationTubeParams_sub_le
    (center : Point3) {lambda width : ℝ}
    (hlambda : 1 ≤ lambda) (hcenterHeight : |center 2| ≤ 1)
    (first second : TubeParams)
    (ha : |first.a - second.a| ≤ width)
    (hb : |first.b - second.b| ≤ width)
    (hc : |first.c - second.c| ≤ width)
    (hd : |first.d - second.d| ≤ width) :
    let firstTarget := pureWZ2LineClassNormalizationTubeParams center lambda first
    let secondTarget := pureWZ2LineClassNormalizationTubeParams center lambda second
    |firstTarget.a - secondTarget.a| ≤ 2 * lambda * width ∧
      |firstTarget.b - secondTarget.b| ≤ 2 * lambda * width ∧
      |firstTarget.c - secondTarget.c| ≤ 2 * lambda * width ∧
      |firstTarget.d - secondTarget.d| ≤ 2 * lambda * width := by
  dsimp only
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  have hwidth : 0 ≤ width := (abs_nonneg _).trans ha
  have hdiff := pureWZ2LineClassNormalizationTubeParams_sub_eq
    center lambda first second
  rw [hdiff.1, hdiff.2.1, hdiff.2.2.1, hdiff.2.2.2]
  constructor
  · rw [abs_mul, abs_of_pos hlambdaPos]
    calc
      lambda * |(first.a - second.a) +
          center 2 * (first.c - second.c)| ≤
          lambda * (|first.a - second.a| +
            |center 2| * |first.c - second.c|) := by
            gcongr
            simpa [abs_mul] using abs_add_le
              (first.a - second.a) (center 2 * (first.c - second.c))
      _ ≤ lambda * (width + 1 * width) := by gcongr
      _ = 2 * lambda * width := by ring
  constructor
  · calc
      |(first.b - second.b) + center 2 * (first.d - second.d)| ≤
          |first.b - second.b| + |center 2| * |first.d - second.d| := by
            simpa [abs_mul] using abs_add_le
              (first.b - second.b) (center 2 * (first.d - second.d))
      _ ≤ width + 1 * width := by gcongr
      _ ≤ 2 * lambda * width := by nlinarith
  constructor
  · exact hc.trans (by nlinarith)
  · rw [abs_div, abs_of_pos hlambdaPos]
    calc
      |first.d - second.d| / lambda ≤ width / lambda := by gcongr
      _ ≤ 2 * lambda * width := by
        apply (div_le_iff₀ hlambdaPos).2
        nlinarith [mul_self_nonneg (lambda - 1)]

/-- The explicit fixed line-metric distortion under the literal total map. -/
theorem directHalfOffsetTerminal_preTarget_lineDistance_le
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount) :
    ∀ first second,
      wz1PaperLineDistance
          ((DirectHalfOffsetTerminalRequestedCWAPreTarget
            (commonSource := commonSource) regularization).tube first)
          ((DirectHalfOffsetTerminalRequestedCWAPreTarget
            (commonSource := commonSource) regularization).tube second) ≤
        directHalfOffsetTerminalLineFactor *
          wz1PaperLineDistance
            (regularization.selected.family.tube first)
            (regularization.selected.family.tube second) := by
  intro first second
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let targetFine := DirectHalfOffsetTerminalRequestedCWAPreTarget
    (commonSource := commonSource) regularization
  have hsourceVertical : ∀ index,
      (regularization.selected.family.tube index).direction 2 ≠ 0 := by
    intro index hzero
    have hvertical :=
      (directHalfOffsetTerminal_source_line_class regularization index).vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  have htargetVertical : ∀ index,
      (targetFine.tube index).direction 2 ≠ 0 := by
    intro index hzero
    have hvertical :=
      (directHalfOffsetTerminal_preTarget_line_class regularization index).vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  let middleFamily :=
    (wz2PaperNonemptyCarrierSubfamily terminal.box.restricted).family
  let originalIndex : Fin targetFine.card → Fin terminal.centeredFamily.card :=
    fun target => cleanup.originalIndex commonSource
      (halfOffsetTerminalCleanupTargetPreimage
        (commonSource := commonSource) regularization target)
  have hmiddleVertical : ∀ index,
      (middleFamily.tube (originalIndex index)).direction 2 ≠ 0 := by
    intro index hzero
    have hvertical := commonSource.halfOffsetLineClassTerminalSource_line_class
      terminal.retubing terminal.box (originalIndex index) |>.vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  have hmiddleAxis : ∀ index,
      tubeAxisLine (middleFamily.tube (originalIndex index)) =
        anisotropicCenteredRescalingMap
          (pureWZ2DirectGeometrySlope source) source.c source.d source.m
          (pureWZ2DirectAnisotropicCenter terminal.retubing.popular) ''
            tubeAxisLine (regularization.selected.family.tube index) := by
    intro index
    have haxis := selectedFamily_axis_anisotropic commonSource terminal
      (originalIndex index)
    have hsourceIndex :
        centeredSourceParent commonSource terminal (originalIndex index) =
          regularization.selected.embedding index := by
      exact halfOffsetTerminalCleanupTargetPreimage_source
        (commonSource := commonSource) regularization index
    rw [hsourceIndex, ← regularization.selected.tube_eq index] at haxis
    exact haxis
  have htargetAxis : ∀ index,
      tubeAxisLine (targetFine.tube index) =
        pureWZ2LineClassNormalizationMap terminal.box.center
          pureWZ2DirectHalfOffsetTerminalLambda ''
            tubeAxisLine (middleFamily.tube (originalIndex index)) := by
    intro index
    exact centeredFamily_axis_lineClassNormalization commonSource terminal
      (originalIndex index)
  have hfirstMiddleParams := tubeParamsOfTube_eq_anisotropicCentered_of_axis_image
    (pureWZ2DirectGeometrySlope source) source.ordered
    (pureWZ2DirectAnisotropicCenter terminal.retubing.popular)
    (regularization.selected.family.tube first) (hsourceVertical first)
    (middleFamily.tube (originalIndex first)) (hmiddleVertical first)
    (hmiddleAxis first)
  have hsecondMiddleParams := tubeParamsOfTube_eq_anisotropicCentered_of_axis_image
    (pureWZ2DirectGeometrySlope source) source.ordered
    (pureWZ2DirectAnisotropicCenter terminal.retubing.popular)
    (regularization.selected.family.tube second) (hsourceVertical second)
    (middleFamily.tube (originalIndex second)) (hmiddleVertical second)
    (hmiddleAxis second)
  have hfirstTargetParams :=
    tubeParamsOfTube_eq_pureWZ2LineClassNormalization_of_axis_image
      terminal.box.center pureWZ2DirectHalfOffsetTerminalLambda_pos
      (middleFamily.tube (originalIndex first)) (hmiddleVertical first)
      (targetFine.tube first) (htargetVertical first) (htargetAxis first)
  have hsecondTargetParams :=
    tubeParamsOfTube_eq_pureWZ2LineClassNormalization_of_axis_image
      terminal.box.center pureWZ2DirectHalfOffsetTerminalLambda_pos
      (middleFamily.tube (originalIndex second)) (hmiddleVertical second)
      (targetFine.tube second) (htargetVertical second) (htargetAxis second)
  let width := wz1PaperLineDistance
    (regularization.selected.family.tube first)
    (regularization.selected.family.tube second)
  have hwidth : 0 ≤ width := by
    dsimp only [width, wz1PaperLineDistance]
    exact add_nonneg dist_nonneg
      (InnerProductGeometry.angle_nonneg _ _)
  have hsourceCluster := tubeParamsOfTube_cluster_of_paperLineDistance
    (directHalfOffsetTerminal_source_line_class regularization first)
    (directHalfOffsetTerminal_source_line_class regularization second)
    (show wz1PaperLineDistance
      (regularization.selected.family.tube first)
      (regularization.selected.family.tube second) ≤ width from le_rfl)
  have hsourceClusterSix :
      |(tubeParamsOfTube (regularization.selected.family.tube first)).a -
        (tubeParamsOfTube (regularization.selected.family.tube second)).a| ≤ 6 * width ∧
      |(tubeParamsOfTube (regularization.selected.family.tube first)).b -
        (tubeParamsOfTube (regularization.selected.family.tube second)).b| ≤ 6 * width ∧
      |(tubeParamsOfTube (regularization.selected.family.tube first)).c -
        (tubeParamsOfTube (regularization.selected.family.tube second)).c| ≤ 6 * width ∧
      |(tubeParamsOfTube (regularization.selected.family.tube first)).d -
        (tubeParamsOfTube (regularization.selected.family.tube second)).d| ≤ 6 * width := by
    exact ⟨hsourceCluster.1.trans (by nlinarith),
      hsourceCluster.2.1.trans (by nlinarith), hsourceCluster.2.2.1,
      hsourceCluster.2.2.2⟩
  have hmid : |source.c + (source.d - source.c) / 2| ≤ 1 := by
    rw [abs_le]
    exact ⟨source.left_mem.trans (by linarith [source.ordered]),
      (by linarith [source.ordered] :
        source.c + (source.d - source.c) / 2 ≤ source.d) |>.trans
          source.right_mem⟩
  have hgmid :
      |pureWZ2DirectGeometrySlope source
        (source.c + (source.d - source.c) / 2)| ≤ 1 := by
    simpa [pureWZ2DirectGeometrySlope] using
      (source.geometrySlope_normalized _
        ⟨source.left_mem.trans (by linarith [source.ordered]),
          (by linarith [source.ordered] :
            source.c + (source.d - source.c) / 2 ≤ source.d) |>.trans
              source.right_mem⟩).1
  have hmiddleCluster := anisotropicCenteredTubeParams_sub_le
    (pureWZ2DirectGeometrySlope source) source.c source.d source.m
    (pureWZ2DirectAnisotropicCenter terminal.retubing.popular) (6 * width)
    source.ordered (by
      rw [source.length_eq, commonSource.halfOffsetAssembly.horizontalSource_scale]
      linarith [commonSource.halfOffsetAssembly.rho_tiny])
    source.slopeScale_pos source.slopeScale_le_one hgmid hmid
    (by positivity)
    (tubeParamsOfTube (regularization.selected.family.tube first))
    (tubeParamsOfTube (regularization.selected.family.tube second))
    hsourceClusterSix.1 hsourceClusterSix.2.1
    hsourceClusterSix.2.2.1 hsourceClusterSix.2.2.2
  rw [← hfirstMiddleParams, ← hsecondMiddleParams] at hmiddleCluster
  have hcenterHeight : |terminal.box.center 2| ≤ 1 := by
    simpa [wz1MildRescalingSourceWindow, Set.mem_setOf_eq] using
      terminal.box.center_mem (2 : Fin 3)
  have htargetCluster := lineClassNormalizationTubeParams_sub_le
    terminal.box.center pureWZ2DirectHalfOffsetTerminalLambda_one_le
    hcenterHeight
    (tubeParamsOfTube (middleFamily.tube (originalIndex first)))
    (tubeParamsOfTube (middleFamily.tube (originalIndex second)))
    hmiddleCluster.1 hmiddleCluster.2.1
    hmiddleCluster.2.2.1 hmiddleCluster.2.2.2
  rw [← hfirstTargetParams, ← hsecondTargetParams] at htargetCluster
  have htargetClusterFinal :
      |(tubeParamsOfTube (targetFine.tube first)).a -
        (tubeParamsOfTube (targetFine.tube second)).a| ≤
          48 * pureWZ2DirectHalfOffsetTerminalLambda * width ∧
      |(tubeParamsOfTube (targetFine.tube first)).b -
        (tubeParamsOfTube (targetFine.tube second)).b| ≤
          48 * pureWZ2DirectHalfOffsetTerminalLambda * width ∧
      |(tubeParamsOfTube (targetFine.tube first)).c -
        (tubeParamsOfTube (targetFine.tube second)).c| ≤
          48 * pureWZ2DirectHalfOffsetTerminalLambda * width ∧
      |(tubeParamsOfTube (targetFine.tube first)).d -
        (tubeParamsOfTube (targetFine.tube second)).d| ≤
          48 * pureWZ2DirectHalfOffsetTerminalLambda * width := by
    convert htargetCluster using 1 <;> ring
  have hraw := wz1PaperLineDistance_le_of_tubeParams_close
    (directHalfOffsetTerminal_preTarget_line_class regularization first)
    (directHalfOffsetTerminal_preTarget_line_class regularization second)
    (mul_nonneg
      (mul_nonneg (by norm_num) pureWZ2DirectHalfOffsetTerminalLambda_pos.le)
      hwidth)
    htargetClusterFinal.1 htargetClusterFinal.2.1
    htargetClusterFinal.2.2.1 htargetClusterFinal.2.2.2
  dsimp only [width] at hraw ⊢
  unfold directHalfOffsetTerminalLineFactor
  nlinarith

/-- Instantiate the terminal CWA schedule with all geometric inputs supplied
by the literal fixed-`lambda` half-offset construction. -/
theorem directHalfOffsetTerminal_cwa_schedule_of_geometry
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount)
    (hsourceTwo : 2 < regularization.outputConstant)
    (hlevels : ENNReal.ofReal (1 / delta) ≤
      regularization.outputConstant ^ parentLevelCount)
    (hsourceScheduleConstant : regularization.outputConstant *
      regularization.outputConstant ≤ sourceScheduleConstant) :
    ∃ scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (commonSource := commonSource)
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization,
      scheduleData.lineFactor = directHalfOffsetTerminalLineFactor := by
  apply directHalfOffsetTerminal_cwa_schedule regularization hsourceTwo
    commonSource.halfOffsetAssembly.cfg.extremal.delta_le_one hlevels
    hsourceScheduleConstant
    directHalfOffsetTerminalLineFactor
    (by
      unfold directHalfOffsetTerminalLineFactor
      nlinarith [pureWZ2DirectHalfOffsetTerminalLambda_one_le])
    (directHalfOffsetTerminal_source_line_class regularization)
    (directHalfOffsetTerminal_source_base_le_five regularization)
    (directHalfOffsetTerminal_preTarget_midpoint_le_three regularization)
    (directHalfOffsetTerminal_preTarget_packing_distinct regularization)
    (directHalfOffsetTerminal_preTarget_carrier_subset_relabel regularization)
    (directHalfOffsetTerminal_preTarget_lineDistance_le regularization)

end PureWZ2ExternalWeightRegularizationData
end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
