import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalBallCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCentered
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperCenteredConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperParameterFrostman
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LineClassNormalizationTubeParameters
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicCenteredConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalDistinctCleanup

/-!
# Centered-conflict degree of the direct half-offset terminal

The terminal family is only a reindexed occupied subfamily of the original
configuration.  Consequently this file never transfers Convex--Wolff control
to that subfamily.  Instead, it counts conflicts in the *original*
`cfg.family`, using an explicit source-index map and exact supporting-line
provenance for the actual composite terminal map.

The terminal-to-source index map and its literal supporting-line covariance
are constructed below.  The remaining quantitative issue is genuinely
geometric: the actual total map has an upper-triangular horizontal shear, so
it is not silently identified with the unrelated rotation-diagonal template.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

namespace TerminalGeometry

/-- The unmodified top-level configuration is the only family to which the
Convex--Wolff hypothesis is applied in this module. -/
abbrev conflictSourceFamily : Kakeya.Streamlined.TubeFamily delta :=
  commonSource.halfOffsetAssembly.cfg.family

/-- The Frostman consequence used below comes from the original configuration
and its stored top-level Convex--Wolff certificate, not from a terminal
subfamily. -/
theorem conflictSource_parameter_frostman :
    TubeParameterFrostmanBound (conflictSourceFamily commonSource)
      (3200 * Kakeya.realRpowENN delta
        (-commonSource.halfOffsetAssembly.technicalLoss)) := by
  exact paper_tubeParameterFrostmanBound_of_croppedConvexWolff
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
    (conflictSourceFamily commonSource)
    commonSource.halfOffsetAssembly.cfg.line_class
    (Kakeya.realRpowENN delta
      (-commonSource.halfOffsetAssembly.technicalLoss))
    commonSource.halfOffsetAssembly.cfg.top_level_cwa

/-- An injective terminal-to-source provenance map has one-point fibers.
This is the counting receipt needed after conflicts have been pulled back to
the original source parameters. -/
theorem sourceParent_fiber_le_one
    (terminal : commonSource.TerminalGeometry)
    (sourceParent : Fin terminal.centeredFamily.card →
      Fin (conflictSourceFamily commonSource).card)
    (hsourceParent : Function.Injective sourceParent)
    (source : Fin (conflictSourceFamily commonSource).card) :
    ((Finset.univ : Finset (Fin terminal.centeredFamily.card)).filter
      fun target => sourceParent target = source).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro first hfirst second hsecond
  apply hsourceParent
  have hfirst' := (Finset.mem_filter.mp hfirst).2
  have hsecond' := (Finset.mem_filter.mp hsecond).2
  exact hfirst'.trans hsecond'.symm

/-- The literal source-index provenance of the final centered terminal.

The first embedding removes empty occupied `(x,z)` terminal carriers; the
second is the original popular-box embedding into `cfg.family`.  Centering
does not change this index type. -/
def centeredSourceParent
    (terminal : commonSource.TerminalGeometry) :
    Fin terminal.centeredFamily.card →
      Fin (conflictSourceFamily commonSource).card := fun target =>
  (wz2PaperNonemptyCarrierSubfamily
    terminal.retubing.popular.popular.restricted).embedding
    ((wz2PaperNonemptyCarrierSubfamily terminal.box.restricted).embedding
      target)

theorem centeredSourceParent_injective
    (terminal : commonSource.TerminalGeometry) :
    Function.Injective (centeredSourceParent commonSource terminal) := by
  intro first second heq
  apply (wz2PaperNonemptyCarrierSubfamily terminal.box.restricted).embedding.injective
  apply (wz2PaperNonemptyCarrierSubfamily
    terminal.retubing.popular.popular.restricted).embedding.injective
  exact heq

/-- The centered terminal supporting line is the image of the actual ambient
source supporting line by the literal composite affine map. -/
theorem centeredFamily_axis_totalAffineMap
    (terminal : commonSource.TerminalGeometry) (target : Fin terminal.centeredFamily.card) :
    tubeAxisLine (terminal.centeredFamily.tube target) =
      totalAffineMap commonSource terminal ''
        tubeAxisLine ((conflictSourceFamily commonSource).tube
          (centeredSourceParent commonSource terminal target)) := by
  let selectedIndex : Fin terminal.retubing.popular.family.card :=
    (wz2PaperNonemptyCarrierSubfamily terminal.box.restricted).embedding target
  let ambientIndex : Fin commonSource.halfOffsetAssembly.cfg.family.card :=
    (wz2PaperNonemptyCarrierSubfamily
      terminal.retubing.popular.popular.restricted).embedding selectedIndex
  rw [centeredFamily_tube, pureWZ2PaperCenteredTube_axis]
  change tubeAxisLine
      (pureWZ2LineClassNormalizationTube terminal.box.center
        pureWZ2DirectHalfOffsetTerminalLambda
        pureWZ2DirectHalfOffsetTerminalLambda_pos
        ((wz2PaperNonemptyCarrierSubfamily terminal.box.restricted).family.tube
          target)) = _
  rw [pureWZ2LineClassNormalizationTube_axis]
  rw [(wz2PaperNonemptyCarrierSubfamily terminal.box.restricted).tube_eq target]
  rw [terminal.retubing.raw.axis selectedIndex]
  change pureWZ2LineClassNormalizationMap terminal.box.center
      pureWZ2DirectHalfOffsetTerminalLambda ''
        (anisotropicCenteredRescalingMap
          (pureWZ2DirectGeometrySlope
            commonSource.halfOffsetAssembly.horizontalSource)
          commonSource.halfOffsetAssembly.horizontalSource.c
          commonSource.halfOffsetAssembly.horizontalSource.d
          commonSource.halfOffsetAssembly.horizontalSource.m
          (pureWZ2DirectAnisotropicCenter terminal.retubing.popular) ''
            tubeAxisLine
              (commonSource.halfOffsetAssembly.cfg.family.tube ambientIndex)) = _
  rw [Set.image_image]
  rfl

/-- Before the final line-class normalization, the selected occupied family is
the literal anisotropic image of the original source family. -/
theorem selectedFamily_axis_anisotropic
    (terminal : commonSource.TerminalGeometry)
    (target : Fin terminal.centeredFamily.card) :
    tubeAxisLine
        ((wz2PaperNonemptyCarrierSubfamily terminal.box.restricted).family.tube
          target) =
      anisotropicCenteredRescalingMap
        (pureWZ2DirectGeometrySlope
          commonSource.halfOffsetAssembly.horizontalSource)
        commonSource.halfOffsetAssembly.horizontalSource.c
        commonSource.halfOffsetAssembly.horizontalSource.d
        commonSource.halfOffsetAssembly.horizontalSource.m
        (pureWZ2DirectAnisotropicCenter terminal.retubing.popular) ''
          tubeAxisLine ((conflictSourceFamily commonSource).tube
            (centeredSourceParent commonSource terminal target)) := by
  let selectedIndex : Fin terminal.retubing.popular.family.card :=
    (wz2PaperNonemptyCarrierSubfamily terminal.box.restricted).embedding target
  let ambientIndex : Fin commonSource.halfOffsetAssembly.cfg.family.card :=
    (wz2PaperNonemptyCarrierSubfamily
      terminal.retubing.popular.popular.restricted).embedding selectedIndex
  rw [(wz2PaperNonemptyCarrierSubfamily terminal.box.restricted).tube_eq target]
  rw [terminal.retubing.raw.axis selectedIndex]
  change anisotropicCenteredRescalingMap
      (pureWZ2DirectGeometrySlope
        commonSource.halfOffsetAssembly.horizontalSource)
      commonSource.halfOffsetAssembly.horizontalSource.c
      commonSource.halfOffsetAssembly.horizontalSource.d
      commonSource.halfOffsetAssembly.horizontalSource.m
      (pureWZ2DirectAnisotropicCenter terminal.retubing.popular) ''
        tubeAxisLine (commonSource.halfOffsetAssembly.cfg.family.tube ambientIndex) = _
  rfl

/-- The final centered family is the exact line-class normalization of the
selected anisotropic family, at the level of supporting lines. -/
theorem centeredFamily_axis_lineClassNormalization
    (terminal : commonSource.TerminalGeometry)
    (target : Fin terminal.centeredFamily.card) :
    tubeAxisLine (terminal.centeredFamily.tube target) =
      pureWZ2LineClassNormalizationMap terminal.box.center
        pureWZ2DirectHalfOffsetTerminalLambda ''
          tubeAxisLine
            ((wz2PaperNonemptyCarrierSubfamily terminal.box.restricted).family.tube
              target) := by
  rw [centeredFamily_tube, pureWZ2PaperCenteredTube_axis]
  exact pureWZ2LineClassNormalizationTube_axis terminal.box.center
    pureWZ2DirectHalfOffsetTerminalLambda
    pureWZ2DirectHalfOffsetTerminalLambda_pos
    ((wz2PaperNonemptyCarrierSubfamily terminal.box.restricted).family.tube target)

/-- Final conflicts pull back through the literal line-class map before the
anisotropic inverse is applied. -/
theorem source_parameter_cluster_of_totalAffineMap_centered_conflict
    (hInverse : AnisotropicTubeParamsInverseClusterStatement)
    (terminal : commonSource.TerminalGeometry)
    (reference other : Fin terminal.centeredFamily.card)
    (hconflict : pureWZ2PaperCenteredConflict terminal.centeredFamily reference other) :
    let source := commonSource.halfOffsetAssembly.horizontalSource
    let width := 100 * (1200 * pureWZ2DirectHalfOffsetTerminalLambda *
      terminal.targetDelta) / (source.m * (source.d - source.c) ^ 2)
    |(tubeParams (F := conflictSourceFamily commonSource)
      (centeredSourceParent commonSource terminal reference)).a -
      (tubeParams (F := conflictSourceFamily commonSource)
        (centeredSourceParent commonSource terminal other)).a| ≤ width ∧
    |(tubeParams (F := conflictSourceFamily commonSource)
      (centeredSourceParent commonSource terminal reference)).b -
      (tubeParams (F := conflictSourceFamily commonSource)
        (centeredSourceParent commonSource terminal other)).b| ≤ width ∧
    |(tubeParams (F := conflictSourceFamily commonSource)
      (centeredSourceParent commonSource terminal reference)).c -
      (tubeParams (F := conflictSourceFamily commonSource)
        (centeredSourceParent commonSource terminal other)).c| ≤ width ∧
    |(tubeParams (F := conflictSourceFamily commonSource)
      (centeredSourceParent commonSource terminal reference)).d -
      (tubeParams (F := conflictSourceFamily commonSource)
        (centeredSourceParent commonSource terminal other)).d| ≤ width := by
  dsimp only
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let middleFamily :=
    (wz2PaperNonemptyCarrierSubfamily terminal.box.restricted).family
  have hsourceVertical : ∀ index,
      ((conflictSourceFamily commonSource).tube index).direction (2 : Fin 3) ≠ 0 := by
    intro index hzero
    have hvertical := commonSource.halfOffsetAssembly.cfg.line_class index |>.vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  have hmiddleVertical : ∀ index,
      (middleFamily.tube index).direction (2 : Fin 3) ≠ 0 := by
    intro index hzero
    have hvertical := (commonSource.halfOffsetLineClassTerminalSource_line_class
      terminal.retubing terminal.box index).vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  have htargetVertical : ∀ index,
      (terminal.centeredFamily.tube index).direction (2 : Fin 3) ≠ 0 := by
    intro index hzero
    have hvertical := (TerminalGeometry.centeredFamily_line_class
      commonSource terminal index).vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  have hlineDistance :
      wz1PaperLineDistance (terminal.centeredFamily.tube reference)
        (terminal.centeredFamily.tube other) ≤
        wz2PaperLocalizedDoubledFiberLineDistanceConstant * terminal.targetDelta := by
    rcases hconflict with ⟨_hne, hcontain | hcontain⟩
    · exact wz2_paper_localized_centered_doubled_containment_lineDistance_le
        commonSource.halfOffsetLineClassTargetDelta_pos
        commonSource.halfOffsetLineClassTargetDelta_pos
        (TerminalGeometry.centeredFamily_line_class commonSource terminal reference)
        (TerminalGeometry.centeredFamily_line_class commonSource terminal other)
        (pureWZ2PaperCenteredTube_midpoint_norm_le_three _
          (TerminalGeometry.line_class commonSource terminal reference)) hcontain
    · have h := wz2_paper_localized_centered_doubled_containment_lineDistance_le
        commonSource.halfOffsetLineClassTargetDelta_pos
        commonSource.halfOffsetLineClassTargetDelta_pos
        (TerminalGeometry.centeredFamily_line_class commonSource terminal other)
        (TerminalGeometry.centeredFamily_line_class commonSource terminal reference)
        (pureWZ2PaperCenteredTube_midpoint_norm_le_three _
          (TerminalGeometry.line_class commonSource terminal other)) hcontain
      rw [wz1PaperLineDistance_symm]
      exact h
  have hfinalCluster := tubeParamsOfTube_cluster_of_paperLineDistance
    (TerminalGeometry.centeredFamily_line_class commonSource terminal reference)
    (TerminalGeometry.centeredFamily_line_class commonSource terminal other) hlineDistance
  have hfinalBound :
      |(tubeParamsOfTube (terminal.centeredFamily.tube reference)).a -
        (tubeParamsOfTube (terminal.centeredFamily.tube other)).a| ≤ 600 * terminal.targetDelta ∧
      |(tubeParamsOfTube (terminal.centeredFamily.tube reference)).b -
        (tubeParamsOfTube (terminal.centeredFamily.tube other)).b| ≤ 600 * terminal.targetDelta ∧
      |(tubeParamsOfTube (terminal.centeredFamily.tube reference)).c -
        (tubeParamsOfTube (terminal.centeredFamily.tube other)).c| ≤ 600 * terminal.targetDelta ∧
      |(tubeParamsOfTube (terminal.centeredFamily.tube reference)).d -
        (tubeParamsOfTube (terminal.centeredFamily.tube other)).d| ≤ 600 * terminal.targetDelta := by
    dsimp only [wz2PaperLocalizedDoubledFiberLineDistanceConstant] at hlineDistance hfinalCluster
    have hdelta := commonSource.halfOffsetLineClassTargetDelta_pos
    exact ⟨hfinalCluster.1.trans (by nlinarith), hfinalCluster.2.1.trans (by nlinarith),
      by convert hfinalCluster.2.2.1 using 1 <;> ring,
      by convert hfinalCluster.2.2.2 using 1 <;> ring⟩
  have hrefParams := tubeParamsOfTube_eq_pureWZ2LineClassNormalization_of_axis_image
    terminal.box.center pureWZ2DirectHalfOffsetTerminalLambda_pos
    (middleFamily.tube reference) (hmiddleVertical reference)
    (terminal.centeredFamily.tube reference) (htargetVertical reference)
    (centeredFamily_axis_lineClassNormalization commonSource terminal reference)
  have hotherParams := tubeParamsOfTube_eq_pureWZ2LineClassNormalization_of_axis_image
    terminal.box.center pureWZ2DirectHalfOffsetTerminalLambda_pos
    (middleFamily.tube other) (hmiddleVertical other)
    (terminal.centeredFamily.tube other) (htargetVertical other)
    (centeredFamily_axis_lineClassNormalization commonSource terminal other)
  rw [hrefParams, hotherParams] at hfinalBound
  have hcenterHeight : |terminal.box.center 2| ≤ 1 := by
    simpa [wz1MildRescalingSourceWindow, Set.mem_setOf_eq] using
      terminal.box.center_mem (2 : Fin 3)
  have hmiddleBound := pureWZ2LineClassNormalizationTubeParams_inverse_cluster_le
    terminal.box.center pureWZ2DirectHalfOffsetTerminalLambda_one_le hcenterHeight
    (tubeParamsOfTube (middleFamily.tube reference))
    (tubeParamsOfTube (middleFamily.tube other))
    hfinalBound.1 hfinalBound.2.1 hfinalBound.2.2.1 hfinalBound.2.2.2
  have hrefRaw := tubeParamsOfTube_eq_anisotropicCentered_of_axis_image
    (pureWZ2DirectGeometrySlope source) source.ordered
    (pureWZ2DirectAnisotropicCenter terminal.retubing.popular)
    ((conflictSourceFamily commonSource).tube
      (centeredSourceParent commonSource terminal reference))
    (hsourceVertical _) (middleFamily.tube reference) (hmiddleVertical _)
    (selectedFamily_axis_anisotropic commonSource terminal reference)
  have hotherRaw := tubeParamsOfTube_eq_anisotropicCentered_of_axis_image
    (pureWZ2DirectGeometrySlope source) source.ordered
    (pureWZ2DirectAnisotropicCenter terminal.retubing.popular)
    ((conflictSourceFamily commonSource).tube
      (centeredSourceParent commonSource terminal other))
    (hsourceVertical _) (middleFamily.tube other) (hmiddleVertical _)
    (selectedFamily_axis_anisotropic commonSource terminal other)
  rw [hrefRaw, hotherRaw] at hmiddleBound
  have hdiff := anisotropicCenteredTubeParams_sub_eq
    (pureWZ2DirectGeometrySlope source) source.c source.d source.m
    (pureWZ2DirectAnisotropicCenter terminal.retubing.popular)
    (tubeParamsOfTube ((conflictSourceFamily commonSource).tube
      (centeredSourceParent commonSource terminal reference)))
    (tubeParamsOfTube ((conflictSourceFamily commonSource).tube
      (centeredSourceParent commonSource terminal other)))
  have hrawBound :
      |(anisotropicTubeParams (pureWZ2DirectGeometrySlope source) source.c source.d source.m
          (tubeParamsOfTube ((conflictSourceFamily commonSource).tube
            (centeredSourceParent commonSource terminal reference)))).a -
        (anisotropicTubeParams (pureWZ2DirectGeometrySlope source) source.c source.d source.m
          (tubeParamsOfTube ((conflictSourceFamily commonSource).tube
            (centeredSourceParent commonSource terminal other)))).a| ≤
          1200 * pureWZ2DirectHalfOffsetTerminalLambda * terminal.targetDelta ∧
      |(anisotropicTubeParams (pureWZ2DirectGeometrySlope source) source.c source.d source.m
          (tubeParamsOfTube ((conflictSourceFamily commonSource).tube
            (centeredSourceParent commonSource terminal reference)))).b -
        (anisotropicTubeParams (pureWZ2DirectGeometrySlope source) source.c source.d source.m
          (tubeParamsOfTube ((conflictSourceFamily commonSource).tube
            (centeredSourceParent commonSource terminal other)))).b| ≤
          1200 * pureWZ2DirectHalfOffsetTerminalLambda * terminal.targetDelta ∧
      |(anisotropicTubeParams (pureWZ2DirectGeometrySlope source) source.c source.d source.m
          (tubeParamsOfTube ((conflictSourceFamily commonSource).tube
            (centeredSourceParent commonSource terminal reference)))).c -
        (anisotropicTubeParams (pureWZ2DirectGeometrySlope source) source.c source.d source.m
          (tubeParamsOfTube ((conflictSourceFamily commonSource).tube
            (centeredSourceParent commonSource terminal other)))).c| ≤
          1200 * pureWZ2DirectHalfOffsetTerminalLambda * terminal.targetDelta ∧
      |(anisotropicTubeParams (pureWZ2DirectGeometrySlope source) source.c source.d source.m
          (tubeParamsOfTube ((conflictSourceFamily commonSource).tube
            (centeredSourceParent commonSource terminal reference)))).d -
        (anisotropicTubeParams (pureWZ2DirectGeometrySlope source) source.c source.d source.m
          (tubeParamsOfTube ((conflictSourceFamily commonSource).tube
            (centeredSourceParent commonSource terminal other)))).d| ≤
          1200 * pureWZ2DirectHalfOffsetTerminalLambda * terminal.targetDelta := by
    exact ⟨by rw [← hdiff.1]; convert hmiddleBound.1 using 1 <;> ring,
      by rw [← hdiff.2.1]; convert hmiddleBound.2.1 using 1 <;> ring,
      by rw [← hdiff.2.2.1]; convert hmiddleBound.2.2.1 using 1 <;> ring,
      by rw [← hdiff.2.2.2]; convert hmiddleBound.2.2.2 using 1 <;> ring⟩
  have hmidMem : source.c + (source.d - source.c) / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · exact source.left_mem.trans (by linarith [source.ordered])
    · have hmidLe : source.c + (source.d - source.c) / 2 ≤ source.d := by
        linarith [source.ordered]
      exact hmidLe.trans source.right_mem
  simpa only [tubeParams] using hInverse
    (pureWZ2DirectGeometrySlope source) source.c source.d source.m
    (1200 * pureWZ2DirectHalfOffsetTerminalLambda * terminal.targetDelta)
    source.ordered (by
      rw [source.length_eq, commonSource.halfOffsetAssembly.horizontalSource_scale]
      nlinarith [commonSource.halfOffsetAssembly.rho_tiny])
    (by intro z hz; exact ⟨source.left_mem.trans hz.1, hz.2.trans source.right_mem⟩)
    source.slopeScale_pos source.slopeScale_le_one
    (by simpa [pureWZ2DirectGeometrySlope] using
      (source.geometrySlope_normalized _ hmidMem).1)
    (by
      have hdelta := commonSource.halfOffsetLineClassTargetDelta_pos
      have hlambda := pureWZ2DirectHalfOffsetTerminalLambda_pos
      nlinarith)
    (tubeParamsOfTube ((conflictSourceFamily commonSource).tube
      (centeredSourceParent commonSource terminal reference)))
    (tubeParamsOfTube ((conflictSourceFamily commonSource).tube
      (centeredSourceParent commonSource terminal other)))
    hrawBound.1 hrawBound.2.1 hrawBound.2.2.1 hrawBound.2.2.2

/-- The original-source parameter radius forced by one actual final centered
terminal conflict. -/
def actualConflictWidth (terminal : commonSource.TerminalGeometry) : ℝ :=
  100 * (1200 * pureWZ2DirectHalfOffsetTerminalLambda * terminal.targetDelta) /
    (commonSource.halfOffsetAssembly.horizontalSource.m *
      (commonSource.halfOffsetAssembly.horizontalSource.d -
        commonSource.halfOffsetAssembly.horizontalSource.c) ^ 2)

/-- The actual centered-conflict degree bound, with Frostman control retained
on the original top-level source family. -/
def actualConflictDegreeBound
    (terminal : commonSource.TerminalGeometry) : ENNReal :=
  (3200 * Kakeya.realRpowENN delta
    (-commonSource.halfOffsetAssembly.technicalLoss)) *
    Kakeya.realRpowENN (actualConflictWidth commonSource terminal) 2 *
      (conflictSourceFamily commonSource).enncard

/-- The actual terminal conflict degree is counted in the original source
family.  No terminal subfamily receives a Convex--Wolff inheritance claim. -/
theorem centered_conflict_degree_le
    (hInverse : AnisotropicTubeParamsInverseClusterStatement)
    (terminal : commonSource.TerminalGeometry)
    (width : ℝ)
    (hwidth : width = 100 *
      (1200 * pureWZ2DirectHalfOffsetTerminalLambda * terminal.targetDelta) /
      (commonSource.halfOffsetAssembly.horizontalSource.m *
        (commonSource.halfOffsetAssembly.horizontalSource.d -
          commonSource.halfOffsetAssembly.horizontalSource.c) ^ 2))
    (hsourceWidth : delta ≤ width) (hwidthOne : width ≤ 1) :
    ∀ reference : Fin terminal.centeredFamily.card,
      (((Finset.univ : Finset (Fin terminal.centeredFamily.card)).filter
        (pureWZ2PaperCenteredConflict terminal.centeredFamily reference)).card : ENNReal) ≤
        (3200 * Kakeya.realRpowENN delta
          (-commonSource.halfOffsetAssembly.technicalLoss)) *
          Kakeya.realRpowENN width 2 *
            (conflictSourceFamily commonSource).enncard := by
  intro reference
  let conflicts : Finset (Fin terminal.centeredFamily.card) :=
    Finset.univ.filter (pureWZ2PaperCenteredConflict terminal.centeredFamily reference)
  let sourceConflicts : Finset (Fin (conflictSourceFamily commonSource).card) :=
    conflicts.image (centeredSourceParent commonSource terminal)
  let sourceCluster : Finset (Fin (conflictSourceFamily commonSource).card) :=
    Finset.univ.filter fun source =>
      |(tubeParams (F := conflictSourceFamily commonSource) source).a -
        (tubeParams (F := conflictSourceFamily commonSource)
          (centeredSourceParent commonSource terminal reference)).a| ≤ width ∧
      |(tubeParams (F := conflictSourceFamily commonSource) source).b -
        (tubeParams (F := conflictSourceFamily commonSource)
          (centeredSourceParent commonSource terminal reference)).b| ≤ width ∧
      |(tubeParams (F := conflictSourceFamily commonSource) source).c -
        (tubeParams (F := conflictSourceFamily commonSource)
          (centeredSourceParent commonSource terminal reference)).c| ≤ width ∧
      |(tubeParams (F := conflictSourceFamily commonSource) source).d -
        (tubeParams (F := conflictSourceFamily commonSource)
          (centeredSourceParent commonSource terminal reference)).d| ≤ width
  have hsourceSubset : sourceConflicts ⊆ sourceCluster := by
    intro source hsource
    rcases Finset.mem_image.mp hsource with ⟨target, htarget, rfl⟩
    have hconflict := (Finset.mem_filter.mp htarget).2
    have hcluster := source_parameter_cluster_of_totalAffineMap_centered_conflict
      commonSource hInverse terminal reference target hconflict
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hwidth]
    exact ⟨by simpa [abs_sub_comm] using hcluster.1,
      by simpa [abs_sub_comm] using hcluster.2.1,
      by simpa [abs_sub_comm] using hcluster.2.2.1,
      by simpa [abs_sub_comm] using hcluster.2.2.2⟩
  have hsourceCard : (sourceConflicts.card : ENNReal) ≤
      (3200 * Kakeya.realRpowENN delta
        (-commonSource.halfOffsetAssembly.technicalLoss)) *
        Kakeya.realRpowENN width 2 * (conflictSourceFamily commonSource).enncard := by
    calc
      (sourceConflicts.card : ENNReal) ≤ (sourceCluster.card : ENNReal) := by
        exact_mod_cast Finset.card_le_card hsourceSubset
      _ ≤ (3200 * Kakeya.realRpowENN delta
          (-commonSource.halfOffsetAssembly.technicalLoss)) *
          Kakeya.realRpowENN width 2 * (conflictSourceFamily commonSource).enncard := by
        simpa [TubeParameterFrostmanBound, sourceCluster] using
          (conflictSource_parameter_frostman commonSource) width hsourceWidth hwidthOne
            (centeredSourceParent commonSource terminal reference)
  have htargetCard : conflicts.card ≤ sourceConflicts.card := by
    have hinj := centeredSourceParent_injective commonSource terminal
    change conflicts.card ≤
      (conflicts.image (centeredSourceParent commonSource terminal)).card
    exact Nat.le_of_eq (Finset.card_image_of_injective _ hinj).symm
  have htargetCardENN : (conflicts.card : ENNReal) ≤
      (sourceConflicts.card : ENNReal) := by
    exact_mod_cast htargetCard
  exact htargetCardENN.trans hsourceCard

/-- The weighted distinct-cleanup constructor for the literal terminal family.
The only remaining numerical obligations are that its actual pulled-back
source radius lies in the Frostman range. -/
theorem toDistinctCleanup
    (hInverse : AnisotropicTubeParamsInverseClusterStatement)
    (terminal : commonSource.TerminalGeometry)
    (hsourceWidth : delta ≤ actualConflictWidth commonSource terminal)
    (hwidthOne : actualConflictWidth commonSource terminal ≤ 1) :
    Nonempty (PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal (actualConflictDegreeBound commonSource terminal)) := by
  apply centered_distinct_selection commonSource terminal
    (actualConflictDegreeBound commonSource terminal)
  intro reference
  simpa [actualConflictDegreeBound, actualConflictWidth] using
    centered_conflict_degree_le commonSource hInverse terminal
      (actualConflictWidth commonSource terminal) rfl hsourceWidth hwidthOne reference

/-- Generic adapter from literal total-map covariance to the older
rotation-diagonal counting theorem.  It is not the actual half-offset
instantiation: that map has a triangular horizontal shear. -/
theorem totalAffineMap_source_axis
    (terminal : commonSource.TerminalGeometry)
    (sourceParent : Fin terminal.centeredFamily.card →
      Fin (conflictSourceFamily commonSource).card)
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hdiagonal : ∀ point : Point3,
      totalAffineMap commonSource terminal point =
        pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale 1 point)
    (hactualAxis : ∀ target,
      tubeAxisLine (terminal.centeredFamily.tube target) =
        totalAffineMap commonSource terminal ''
          tubeAxisLine
            ((conflictSourceFamily commonSource).tube (sourceParent target))) :
    ∀ target,
      tubeAxisLine (terminal.centeredFamily.tube target) =
        pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale 1 ''
            tubeAxisLine
              ((conflictSourceFamily commonSource).tube (sourceParent target)) := by
  intro target
  rw [hactualAxis target]
  ext point
  simp only [Set.mem_image]
  constructor
  · rintro ⟨sourcePoint, hsourcePoint, rfl⟩
    exact ⟨sourcePoint, hsourcePoint, (hdiagonal sourcePoint).symm⟩
  · rintro ⟨sourcePoint, hsourcePoint, hpoint⟩
    exact ⟨sourcePoint, hsourcePoint, (hdiagonal sourcePoint).trans hpoint⟩

/-- Centered-conflict degree bound for the literal final terminal family.

`sourceParent` must be the composition of the actual occupied-terminal and
anisotropic-retubing embeddings into `cfg.family`; `hsourceParent` is exactly
the required source-index provenance.  No CWA statement is assumed for the
terminal family or for either intermediate subfamily. -/
theorem centered_conflict_degree_le_of_totalAffineMap_provenance
    (terminal : commonSource.TerminalGeometry)
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hframe : |frameSlope| ≤ 1)
    (hanchor : |center 2| ≤ 1)
    (hheight : 0 < heightScale)
    (htransverse : 0 < transverseScale)
    (sourceParent : Fin terminal.centeredFamily.card →
      Fin (conflictSourceFamily commonSource).card)
    (hsourceParent : Function.Injective sourceParent)
    (hdiagonal : ∀ point : Point3,
      totalAffineMap commonSource terminal point =
        pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale 1 point)
    (hactualAxis : ∀ target,
      tubeAxisLine (terminal.centeredFamily.tube target) =
        totalAffineMap commonSource terminal ''
          tubeAxisLine
            ((conflictSourceFamily commonSource).tube (sourceParent target)))
    (width : ℝ)
    (hwidth : width = 16 * (1 + heightScale) *
      (1 + transverseScale⁻¹) * (600 * terminal.targetDelta))
    (hsourceWidth : delta ≤ width)
    (hwidthOne : width ≤ 1) :
    ∀ reference : Fin terminal.centeredFamily.card,
      (((Finset.univ : Finset (Fin terminal.centeredFamily.card)).filter
        (pureWZ2PaperCenteredConflict terminal.centeredFamily reference)).card :
          ENNReal) ≤
        (3200 * Kakeya.realRpowENN delta
          (-commonSource.halfOffsetAssembly.technicalLoss)) *
          Kakeya.realRpowENN width 2 *
            (conflictSourceFamily commonSource).enncard := by
  have haxis := totalAffineMap_source_axis commonSource terminal sourceParent
    frameSlope center heightScale transverseScale hdiagonal hactualAxis
  have hsourceVertical : ∀ source,
      ((conflictSourceFamily commonSource).tube source).direction (2 : Fin 3) ≠ 0 := by
    intro source hzero
    have hvertical := commonSource.halfOffsetAssembly.cfg.line_class source |>.vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  have htargetVertical : ∀ target,
      (terminal.centeredFamily.tube target).direction (2 : Fin 3) ≠ 0 := by
    intro target hzero
    have hvertical := (TerminalGeometry.centeredFamily_line_class
      commonSource terminal target).vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  have hFrostman := conflictSource_parameter_frostman commonSource
  simpa using affine_centered_conflict_degree_le
    frameSlope center heightScale transverseScale hframe hanchor
    commonSource.halfOffsetLineClassTargetDelta_pos hheight htransverse
    (conflictSourceFamily commonSource) terminal.centeredFamily sourceParent 1
    (sourceParent_fiber_le_one commonSource terminal sourceParent hsourceParent)
    commonSource.halfOffsetAssembly.cfg.line_class
    (terminal.centeredFamily_line_class)
    (fun target => pureWZ2PaperCenteredTube_midpoint_norm_le_three _
      (TerminalGeometry.line_class commonSource terminal target))
    haxis hsourceVertical htargetVertical
    (3200 * Kakeya.realRpowENN delta
      (-commonSource.halfOffsetAssembly.technicalLoss))
    (conflictSourceFamily commonSource).enncard
    (by
      simpa [TubeParameterFrostmanBound] using hFrostman)
      width hwidth hsourceWidth hwidthOne

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
