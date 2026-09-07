import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Extremal
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnFiberInputs
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryNestedCover
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingProducer
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralDilatedCanonicalRescaledTube
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralDilatedDistinctness

/-!
# Ordinary pure nested scale after one common literal rescaling

This module assembles the public Definition 2.12 witness on the pointwise
midpoint-centered ordinary target families.  The source witness supplies the
pure cover, exact full-fiber uniformity, and actual outer-John CWA.  The
literal strong-separation theorem supplies the target parent separation.

For finite unit-segment carriers, target line separation alone does not imply
centered-doubled-fiber disjointness.  The exact missing localization
provenance is therefore explicit below: containment in one centered doubled
target parent must force target line distance at most `800` times the target
middle scale.  A caller may prove this from a common unit-ball child, or
supply an equivalent direct localization theorem.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
The minimal localization provenance needed to turn the closed
`1600 * (rho / sigma)` literal separation into ordinary centered-doubled
fiber disjointness.
-/
structure WZ2PaperOrdinaryNestedTargetLocalization
    {delta rho sigma : ℝ}
    (sourceFine : Kakeya.Streamlined.TubeFamily delta)
    (sourceMiddle : Kakeya.Streamlined.TubeFamily rho)
    (anchor : Kakeya.DeltaTube sigma)
    (hsigma : 0 < sigma) : Prop where
  centered_doubled_lineDistance_le :
    ∀ (target : Fin
        (wz2PaperLiteralOrdinaryRescaledFamily
          sourceFine anchor hsigma).card)
      (parent : Fin
        (wz2PaperLiteralOrdinaryRescaledFamily
          sourceMiddle anchor hsigma).card),
      ((wz2PaperLiteralOrdinaryRescaledFamily
        sourceFine anchor hsigma).tube target).carrier ⊆
          wz2PaperCenteredDilatedCarrier 2
            ((wz2PaperLiteralOrdinaryRescaledFamily
              sourceMiddle anchor hsigma).tube parent) →
        wz1PaperLineDistance
            ((wz2PaperLiteralOrdinaryRescaledFamily
              sourceFine anchor hsigma).tube target)
            ((wz2PaperLiteralOrdinaryRescaledFamily
              sourceMiddle anchor hsigma).tube parent) ≤
          800 * (rho / sigma)

/--
Strict ordinary carrier nesting under one common literal rescaling uses only
the fine-to-middle strict line cover and ordinary carrier containment.  In
particular, no historical middle-to-anchor strict cover is needed.
-/
private theorem wz2PaperLiteralOrdinary_nested_cover_minimal
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hdeltaRho : 100 * delta ≤ rho)
    (hsigmaOne : sigma ≤ 1)
    (fine : Kakeya.DeltaTube delta)
    (middle : Kakeya.DeltaTube rho)
    (anchor : Kakeya.DeltaTube sigma)
    (hcoverFineMiddle : WZ1PaperTubeCovers fine middle)
    (hcarrierFineMiddle : fine.carrier ⊆ middle.carrier) :
    (wz2PaperLiteralOrdinaryRescaledTube fine anchor hsigma).carrier ⊆
      (wz2PaperLiteralOrdinaryRescaledTube middle anchor hsigma).carrier := by
  let targetFine :=
    wz2PaperLiteralOrdinaryRescaledTube fine anchor hsigma
  let targetMiddle :=
    wz2PaperLiteralOrdinaryRescaledTube middle anchor hsigma
  have hdeltaSigma : 0 < delta / sigma := div_pos hdelta hsigma
  have hmidpointSource :
      dist (wz2PaperTubeMidpoint fine) (wz2PaperTubeMidpoint middle) ≤
        5 * rho :=
    wz2PaperSourceMidpoint_dist_le_five_mul_of_carrier_subset
      hdelta hrho fine middle hcarrierFineMiddle
  have hmidpointTarget :
      dist (wz2PaperTubeMidpoint targetFine)
          (wz2PaperTubeMidpoint targetMiddle) ≤
        rho / (20 * sigma) := by
    have hfineMidpoint :
        wz2PaperTubeMidpoint targetFine =
          wz2PaperLiteralUnitRescalingMap anchor hsigma
            (wz2PaperTubeMidpoint fine) := by
      dsimp only [targetFine, wz2PaperTubeMidpoint,
        wz2PaperLiteralOrdinaryRescaledTube]
      module
    have hmiddleMidpoint :
        wz2PaperTubeMidpoint targetMiddle =
          wz2PaperLiteralUnitRescalingMap anchor hsigma
            (wz2PaperTubeMidpoint middle) := by
      dsimp only [targetMiddle, wz2PaperTubeMidpoint,
        wz2PaperLiteralOrdinaryRescaledTube]
      module
    rw [hfineMidpoint, hmiddleMidpoint]
    rw [dist_eq_norm, wz2PaperLiteralUnitRescalingMap_sub]
    calc
      ‖wz2PaperLiteralUnitRescalingLinear anchor
          (wz2PaperTubeMidpoint fine -
            wz2PaperTubeMidpoint middle)‖ ≤
          ‖wz2PaperTubeMidpoint fine -
            wz2PaperTubeMidpoint middle‖ / (100 * sigma) :=
        wz2PaperLiteralUnitRescalingLinear_norm_le
          anchor hsigma hsigmaOne _
      _ ≤ (5 * rho) / (100 * sigma) := by
        gcongr
        simpa [dist_eq_norm] using hmidpointSource
      _ = rho / (20 * sigma) := by
        field_simp [hsigma.ne']
        ring
  have hdirectionTarget :
      ‖targetFine.direction - targetMiddle.direction‖ ≤
        rho / (2 * sigma) :=
    wz2PaperLiteralOrdinaryRescaledDirection_dist_le
      hsigma hsigmaOne fine middle anchor hcoverFineMiddle
  intro point hpoint
  have hcompact :
      IsCompact
        (Kakeya.unitSegment targetFine.base targetFine.direction) :=
    isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  change point ∈ Metric.cthickening (delta / sigma)
    (Kakeya.unitSegment targetFine.base targetFine.direction) at hpoint
  rw [hcompact.cthickening_eq_biUnion_closedBall hdeltaSigma.le] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨fineAxisPoint, hfineAxisPoint, hpointFineAxis⟩
  rcases hfineAxisPoint with ⟨parameter, hparameter, rfl⟩
  let middleAxisPoint :=
    targetMiddle.base + parameter • targetMiddle.direction
  have hmiddleAxisPoint :
      middleAxisPoint ∈
        Kakeya.unitSegment targetMiddle.base targetMiddle.direction :=
    ⟨parameter, hparameter, rfl⟩
  have hpointFineAxisDist :
      dist point
          (targetFine.base + parameter • targetFine.direction) ≤
        delta / sigma := by
    simpa [Metric.mem_closedBall] using hpointFineAxis
  have haxisPointDist :
      dist (targetFine.base + parameter • targetFine.direction)
          middleAxisPoint ≤
        rho / (20 * sigma) +
          (1 / 2 : ℝ) * (rho / (2 * sigma)) := by
    rw [dist_eq_norm]
    have hdecompose :
        targetFine.base + parameter • targetFine.direction -
            middleAxisPoint =
          (wz2PaperTubeMidpoint targetFine -
              wz2PaperTubeMidpoint targetMiddle) +
            (parameter - 1 / 2) •
              (targetFine.direction - targetMiddle.direction) := by
      dsimp only [middleAxisPoint]
      unfold wz2PaperTubeMidpoint
      module
    rw [hdecompose]
    calc
      ‖(wz2PaperTubeMidpoint targetFine -
            wz2PaperTubeMidpoint targetMiddle) +
          (parameter - 1 / 2) •
            (targetFine.direction - targetMiddle.direction)‖ ≤
          ‖wz2PaperTubeMidpoint targetFine -
              wz2PaperTubeMidpoint targetMiddle‖ +
            ‖(parameter - 1 / 2) •
              (targetFine.direction -
                targetMiddle.direction)‖ :=
        norm_add_le _ _
      _ =
          ‖wz2PaperTubeMidpoint targetFine -
              wz2PaperTubeMidpoint targetMiddle‖ +
            |parameter - 1 / 2| *
              ‖targetFine.direction -
                targetMiddle.direction‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤
          rho / (20 * sigma) +
            (1 / 2 : ℝ) * (rho / (2 * sigma)) := by
        gcongr
        · simpa [dist_eq_norm] using hmidpointTarget
        · rw [abs_le]
          constructor <;> linarith [hparameter.1, hparameter.2]
  apply Metric.mem_cthickening_of_dist_le point middleAxisPoint
    (rho / sigma)
    (Kakeya.unitSegment targetMiddle.base targetMiddle.direction)
    hmiddleAxisPoint
  calc
    dist point middleAxisPoint ≤
        dist point
            (targetFine.base + parameter • targetFine.direction) +
          dist
            (targetFine.base + parameter • targetFine.direction)
            middleAxisPoint :=
      dist_triangle _ _ _
    _ ≤
        delta / sigma +
          (rho / (20 * sigma) +
            (1 / 2 : ℝ) * (rho / (2 * sigma))) := by
      gcongr
    _ ≤ rho / sigma := by
      field_simp [hsigma.ne']
      nlinarith [hdeltaRho]

/-- Assigned strict target nesting with no middle-to-anchor strict premise. -/
private theorem
    wz2PaperLiteralOrdinary_assigned_target_containment_minimal
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hdeltaRho : 100 * delta ≤ rho)
    (hsigmaOne : sigma ≤ 1)
    (sourceFine : Kakeya.Streamlined.TubeFamily delta)
    (sourceMiddle : Kakeya.Streamlined.TubeFamily rho)
    (anchor : Kakeya.DeltaTube sigma)
    (sourceCover :
      WZ2PaperPurePartitioningCover sourceFine sourceMiddle)
    (hFineMiddle :
      ∀ source,
        WZ1PaperTubeCovers
          (sourceFine.tube source)
          (sourceMiddle.tube (sourceCover.parent source)))
    (target : Fin
      (wz2PaperLiteralOrdinaryRescaledFamily
        sourceFine anchor hsigma).card) :
    ((wz2PaperLiteralOrdinaryRescaledFamily
      sourceFine anchor hsigma).tube target).carrier ⊆
      ((wz2PaperLiteralOrdinaryRescaledFamily
        sourceMiddle anchor hsigma).tube
        (wz2PaperLiteralOrdinaryRescaledFamilyTargetIndex
          sourceMiddle anchor hsigma
          (sourceCover.parent
            (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
              sourceFine anchor hsigma target)))).carrier := by
  let source :=
    wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
      sourceFine anchor hsigma target
  apply
    wz2PaperLiteralOrdinary_nested_cover_minimal
      hdelta hrho hsigma hdeltaRho hsigmaOne
      (sourceFine.tube source)
      (sourceMiddle.tube (sourceCover.parent source))
      anchor
      (hFineMiddle source)
  exact
    (mem_wz2PaperOrdinaryFullFiberIndices_iff
      (sourceCover.parent source) source).mp
      (sourceCover.parent_mem_fullFiber source)

/-- Pure target cover from exact target doubled-fiber disjointness. -/
private theorem
    wz2PaperLiteralOrdinaryPurePartitioningCover_minimal
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hdeltaRho : 100 * delta ≤ rho)
    (hsigmaOne : sigma ≤ 1)
    (sourceFine : Kakeya.Streamlined.TubeFamily delta)
    (sourceMiddle : Kakeya.Streamlined.TubeFamily rho)
    (anchor : Kakeya.DeltaTube sigma)
    (sourceCover :
      WZ2PaperPurePartitioningCover sourceFine sourceMiddle)
    (hFineMiddle :
      ∀ source,
        WZ1PaperTubeCovers
          (sourceFine.tube source)
          (sourceMiddle.tube (sourceCover.parent source)))
    (hDoubledFibers :
      ∀ first second, first ≠ second →
        Disjoint
          (wz2PaperOrdinaryDilatedFiberIndices 2
            (wz2PaperLiteralOrdinaryRescaledFamily
              sourceFine anchor hsigma)
            (wz2PaperLiteralOrdinaryRescaledFamily
              sourceMiddle anchor hsigma)
            first)
          (wz2PaperOrdinaryDilatedFiberIndices 2
            (wz2PaperLiteralOrdinaryRescaledFamily
              sourceFine anchor hsigma)
            (wz2PaperLiteralOrdinaryRescaledFamily
              sourceMiddle anchor hsigma)
            second)) :
    WZ2PaperPurePartitioningCover
      (wz2PaperLiteralOrdinaryRescaledFamily
        sourceFine anchor hsigma)
      (wz2PaperLiteralOrdinaryRescaledFamily
        sourceMiddle anchor hsigma) where
  covers target := by
    let source :=
      wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
        sourceFine anchor hsigma target
    let assigned :=
      wz2PaperLiteralOrdinaryRescaledFamilyTargetIndex
        sourceMiddle anchor hsigma (sourceCover.parent source)
    refine ⟨assigned, ?_⟩
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    exact
      wz2PaperLiteralOrdinary_assigned_target_containment_minimal
        hdelta hrho hsigma hdeltaRho hsigmaOne
        sourceFine sourceMiddle anchor sourceCover hFineMiddle target
  doubled_fibers_disjoint := hDoubledFibers

/-- Exact complete source-index equality for the minimal target cover. -/
private theorem
    wz2PaperLiteralOrdinary_fullFiber_source_indices_minimal
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hdeltaRho : 100 * delta ≤ rho)
    (hsigmaOne : sigma ≤ 1)
    (sourceFine : Kakeya.Streamlined.TubeFamily delta)
    (sourceMiddle : Kakeya.Streamlined.TubeFamily rho)
    (anchor : Kakeya.DeltaTube sigma)
    (sourceCover :
      WZ2PaperPurePartitioningCover sourceFine sourceMiddle)
    (hFineMiddle :
      ∀ source,
        WZ1PaperTubeCovers
          (sourceFine.tube source)
          (sourceMiddle.tube (sourceCover.parent source)))
    (hDoubledFibers :
      ∀ first second, first ≠ second →
        Disjoint
          (wz2PaperOrdinaryDilatedFiberIndices 2
            (wz2PaperLiteralOrdinaryRescaledFamily
              sourceFine anchor hsigma)
            (wz2PaperLiteralOrdinaryRescaledFamily
              sourceMiddle anchor hsigma)
            first)
          (wz2PaperOrdinaryDilatedFiberIndices 2
            (wz2PaperLiteralOrdinaryRescaledFamily
              sourceFine anchor hsigma)
            (wz2PaperLiteralOrdinaryRescaledFamily
              sourceMiddle anchor hsigma)
            second))
    (targetParent : Fin
      (wz2PaperLiteralOrdinaryRescaledFamily
        sourceMiddle anchor hsigma).card) :
    Finset.image
        (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
          sourceFine anchor hsigma)
        (wz2PaperOrdinaryFullFiberIndices
          (wz2PaperLiteralOrdinaryRescaledFamily
            sourceFine anchor hsigma)
          (wz2PaperLiteralOrdinaryRescaledFamily
            sourceMiddle anchor hsigma)
          targetParent) =
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceMiddle
        (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
          sourceMiddle anchor hsigma targetParent) := by
  let targetCover :=
    wz2PaperLiteralOrdinaryPurePartitioningCover_minimal
      hdelta hrho hsigma hdeltaRho hsigmaOne
      sourceFine sourceMiddle anchor sourceCover hFineMiddle
      hDoubledFibers
  ext source
  constructor
  · intro hsource
    rcases Finset.mem_image.mp hsource with
      ⟨target, htarget, htargetSource⟩
    rw [sourceCover.mem_fullFiber_iff_parent_eq hrho.le]
    rw [targetCover.mem_fullFiber_iff_parent_eq
      (div_nonneg hrho.le hsigma.le)] at htarget
    have htargetParent :
        targetCover.parent target =
          wz2PaperLiteralOrdinaryRescaledFamilyTargetIndex
            sourceMiddle anchor hsigma
            (sourceCover.parent
              (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
                sourceFine anchor hsigma target)) := by
      apply
        targetCover.fullFiber_parent_unique
          (div_nonneg hrho.le hsigma.le)
          (targetCover.parent_mem_fullFiber target)
      rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
      exact
        wz2PaperLiteralOrdinary_assigned_target_containment_minimal
          hdelta hrho hsigma hdeltaRho hsigmaOne
          sourceFine sourceMiddle anchor sourceCover hFineMiddle target
    rw [htargetParent] at htarget
    have hparent :
        sourceCover.parent
            (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
              sourceFine anchor hsigma target) =
          wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
            sourceMiddle anchor hsigma targetParent := by
      apply Fin.ext
      exact congrArg Fin.val htarget
    rw [← htargetSource]
    exact hparent
  · intro hsource
    rw [sourceCover.mem_fullFiber_iff_parent_eq hrho.le] at hsource
    rcases
      (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex_bijective
        sourceFine anchor hsigma).surjective source with
      ⟨target, htargetSource⟩
    refine Finset.mem_image.mpr ⟨target, ?_, htargetSource⟩
    rw [targetCover.mem_fullFiber_iff_parent_eq
      (div_nonneg hrho.le hsigma.le)]
    have hassigned :
        target ∈
          wz2PaperOrdinaryFullFiberIndices
            (wz2PaperLiteralOrdinaryRescaledFamily
              sourceFine anchor hsigma)
            (wz2PaperLiteralOrdinaryRescaledFamily
              sourceMiddle anchor hsigma)
            (wz2PaperLiteralOrdinaryRescaledFamilyTargetIndex
              sourceMiddle anchor hsigma
              (sourceCover.parent
                (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
                  sourceFine anchor hsigma target))) := by
      rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
      exact
        wz2PaperLiteralOrdinary_assigned_target_containment_minimal
          hdelta hrho hsigma hdeltaRho hsigmaOne
          sourceFine sourceMiddle anchor sourceCover hFineMiddle target
    have hparent :=
      (targetCover.mem_fullFiber_iff_parent_eq
        (div_nonneg hrho.le hsigma.le)
        (wz2PaperLiteralOrdinaryRescaledFamilyTargetIndex
          sourceMiddle anchor hsigma
          (sourceCover.parent
            (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
              sourceFine anchor hsigma target)))
        target).mp hassigned
    apply Fin.ext
    calc
      (targetCover.parent target).val =
          (sourceCover.parent
            (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
              sourceFine anchor hsigma target)).val := by
        exact congrArg Fin.val hparent
      _ = (sourceCover.parent source).val := by
        rw [htargetSource]
      _ =
          (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
            sourceMiddle anchor hsigma targetParent).val := by
        exact congrArg Fin.val hsource
      _ = targetParent.val := rfl

/-- The midpoint-centered ordinary target remains in the paper line class. -/
theorem wz2PaperLiteralOrdinaryRescaledTube_lineClass
    {delta sigma : ℝ}
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1)
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube sigma)
    (hsource : WZ1PaperTubeInLineClass source)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hcover : WZ2PaperDilatedTubeCovers 2 source anchor) :
    WZ1PaperTubeInLineClass
      (wz2PaperLiteralOrdinaryRescaledTube source anchor hsigma) := by
  let canonical :=
    Classical.choice
      (wz2_paper_literal_canonical_dilated_unit_rescaled_tube
        hsigma hsigmaOne source anchor hsource hanchor hcover)
  let target :=
    wz2PaperLiteralOrdinaryRescaledTube source anchor hsigma
  have hcanonicalDirection :
      wz1PaperDirection canonical.target =
        NormedSpace.normalize
          (wz2PaperLiteralUnitRescalingLinear anchor
            (wz1PaperDirection source)) :=
    literal_target_direction_eq_normalize_of_inner_pos
      hsigma hsource canonical.target_line_class canonical.target_axis
      (by
        have hinner := hcover.inner_direction_ge_half hsigmaOne
        linarith)
  have htargetDirection :
      target.direction =
        NormedSpace.normalize
          (wz2PaperLiteralUnitRescalingLinear anchor
            (wz1PaperDirection source)) := by
    rfl
  have hstoredVertical :
      0 < target.direction (2 : Fin 3) := by
    rw [htargetDirection, ← hcanonicalDirection]
    linarith [canonical.target_line_class.1]
  have htargetVertical :
      (1 / 2 : ℝ) ≤
        wz1PaperDirection target (2 : Fin 3) := by
    unfold wz1PaperDirection
    rw [if_pos hstoredVertical.le]
    rw [htargetDirection, ← hcanonicalDirection]
    exact canonical.target_line_class.1
  have haxis :
      tubeAxisLine target =
        tubeAxisLine canonical.target := by
    exact
      wz2PaperLiteralOrdinaryRescaledTube_same_axis
        source anchor hsigma canonical.target canonical.target_axis
  have hzero :
      wz1TubeAxisZeroPoint target =
        wz1TubeAxisZeroPoint canonical.target := by
    apply
      wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
        (show (1 / 2 : ℝ) ≤ |target.direction (2 : Fin 3)| by
          rw [abs_of_pos hstoredVertical]
          simpa [wz1PaperDirection, if_pos hstoredVertical.le] using
            htargetVertical)
    · rw [haxis]
      exact wz1TubeAxisZeroPoint_mem_axis canonical.target
    · exact
        wz1TubeAxisZeroPoint_coord_two canonical.target
          canonical.target_line_class.vertical
  refine ⟨htargetVertical, ?_, ?_⟩
  · rw [hzero]
    exact canonical.target_line_class.2.1
  · rw [hzero]
    exact canonical.target_line_class.2.2

/-- Pointwise ordinary rescaling preserves the paper line class. -/
theorem wz2PaperLiteralOrdinaryRescaledFamily_lineClass
    {delta sigma : ℝ}
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1)
    (source : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube sigma)
    (hsource : WZ1PaperIsLineClass source)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hcover :
      ∀ index,
        WZ2PaperDilatedTubeCovers 2 (source.tube index) anchor) :
    WZ1PaperIsLineClass
      (wz2PaperLiteralOrdinaryRescaledFamily
        source anchor hsigma) := by
  intro index
  exact
    wz2PaperLiteralOrdinaryRescaledTube_lineClass
      hsigma hsigmaOne
      (source.tube index) anchor
      (hsource index) hanchor (hcover index)

/--
The Section 6 literal family synchronized with the pointwise ordinary public
fine family.  The source map is the identity.
-/
noncomputable def wz2PaperLiteralOrdinaryRescaledFamilyLiteralData
    {delta sigma : ℝ}
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1)
    (source : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube sigma)
    (hsource : WZ1PaperIsLineClass source)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hcover :
      ∀ index, WZ1PaperTubeCovers (source.tube index) anchor) :
    WZ2PaperLiteralUnitRescaledFamilyData source anchor hsigma where
  targetFamily :=
    wz2PaperLiteralOrdinaryRescaledFamily source anchor hsigma
  sourceIndex :=
    wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
      source anchor hsigma
  sourceIndex_bijective :=
    wz2PaperLiteralOrdinaryRescaledFamilySourceIndex_bijective
      source anchor hsigma
  target_line_class :=
    wz2PaperLiteralOrdinaryRescaledFamily_lineClass
      hsigma hsigmaOne source anchor hsource hanchor
      (fun index => by
        have hstrict := hcover index
        unfold WZ1PaperTubeCovers at hstrict
        unfold WZ2PaperDilatedTubeCovers
        linarith)
  target_axis target :=
    wz2PaperLiteralOrdinaryRescaledTube_axis
      (source.tube
        (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
          source anchor hsigma target))
      anchor hsigma

/--
The synchronized actual-Assouad/literal certificate whose public family is
definitionally the pointwise midpoint-centered ordinary family.
-/
noncomputable def wz2PaperLiteralOrdinaryRescaledFamilyCertificate
    {delta sigma : ℝ}
    (hdelta : 0 < delta)
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1)
    (source : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube sigma)
    (hsource : WZ1PaperIsLineClass source)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hcover :
      ∀ index, WZ1PaperTubeCovers (source.tube index) anchor) :
    WZ2PaperAssouadToLiteralRescalingCertificate
      hsigma
      (WZ2PaperAssouadUnitRescalingData.ofTube anchor hsigma)
      (wz2PaperLiteralOrdinaryRescaledFamilyLiteralData
        hsigma hsigmaOne source anchor hsource hanchor hcover)
      4000000 :=
  wz2PaperAssouadToLiteralRescalingFixed
    hdelta hsigma hsigmaOne source anchor hcover
    (wz2PaperLiteralOrdinaryRescaledFamilyLiteralData
      hsigma hsigmaOne source anchor hsource hanchor hcover)

theorem wz2PaperLiteralOrdinaryRescaledFamilyCertificate_publicFamily
    {delta sigma : ℝ}
    (hdelta : 0 < delta)
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1)
    (source : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube sigma)
    (hsource : WZ1PaperIsLineClass source)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hcover :
      ∀ index, WZ1PaperTubeCovers (source.tube index) anchor) :
    (wz2PaperLiteralOrdinaryRescaledFamilyCertificate
      hdelta hsigma hsigmaOne source anchor
      hsource hanchor hcover).publicFamily =
        wz2PaperLiteralOrdinaryRescaledFamily
          source anchor hsigma := by
  rfl

/--
Produce the complete public pure scale witness after one common literal
rescaling.

Strict full-fiber cardinalities are transported exactly, while every actual
outer-John full-fiber CWA is transported with the closed loss `81000000`.
-/
noncomputable def wz2PaperPureScaleCoverData.ordinaryNestedScale
    {delta rho sigma : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (sourceScale : WZ2PaperPureScaleCoverData sourceFine rho C)
    (hsigma : 0 < sigma)
    (hdeltaRho : 100 * delta ≤ rho)
    (hrhoSigma : rho ≤ sigma)
    (hsigmaOne : sigma ≤ 1)
    (anchor : Kakeya.DeltaTube sigma)
    (hfine : WZ1PaperIsLineClass sourceFine)
    (hmiddle : WZ1PaperIsLineClass sourceScale.coarse)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hFineMiddle :
      ∀ source,
        WZ1PaperTubeCovers
          (sourceFine.tube source)
          (sourceScale.coarse.tube
            (sourceScale.cover.parent source)))
    (hFineAnchor :
      ∀ source, WZ1PaperTubeCovers (sourceFine.tube source) anchor)
    (hMiddleAnchor :
      ∀ parent,
        WZ2PaperDilatedTubeCovers 2
          (sourceScale.coarse.tube parent) anchor)
    (hMiddleSeparated :
      ∀ first second, first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * rho <
          wz1PaperLineDistance
            (sourceScale.coarse.tube first)
            (sourceScale.coarse.tube second))
    (localization :
      WZ2PaperOrdinaryNestedTargetLocalization
        sourceFine sourceScale.coarse anchor hsigma) :
    WZ2PaperPureScaleCoverData
      (wz2PaperLiteralOrdinaryRescaledFamily
        sourceFine anchor hsigma)
      (rho / sigma)
      (max C ((81000000 : ENNReal) * C)) := by
  let targetFine :=
    wz2PaperLiteralOrdinaryRescaledFamily
      sourceFine anchor hsigma
  let targetMiddle :=
    wz2PaperLiteralOrdinaryRescaledFamily
      sourceScale.coarse anchor hsigma
  have htargetFineLine : WZ1PaperIsLineClass targetFine :=
    wz2PaperLiteralOrdinaryRescaledFamily_lineClass
      hsigma hsigmaOne sourceFine anchor
      hfine hanchor
      (fun source => by
        have hstrict := hFineAnchor source
        unfold WZ1PaperTubeCovers at hstrict
        unfold WZ2PaperDilatedTubeCovers
        linarith)
  have htargetMiddleLine : WZ1PaperIsLineClass targetMiddle :=
    wz2PaperLiteralOrdinaryRescaledFamily_lineClass
      hsigma hsigmaOne sourceScale.coarse anchor
      hmiddle hanchor hMiddleAnchor
  have hTargetSeparated :
      ∀ first second, first ≠ second →
        1600 * (rho / sigma) <
          wz1PaperLineDistance
            (targetMiddle.tube first)
            (targetMiddle.tube second) := by
    intro first second hne
    exact
      wz2_paper_literal_dilated_strong_separation
        sourceScale.rho_pos hrhoSigma hsigma hsigmaOne
        (sourceScale.coarse.tube first)
        (sourceScale.coarse.tube second)
        anchor
        (hmiddle first) (hmiddle second) hanchor
        (hMiddleAnchor first) (hMiddleAnchor second)
        (hMiddleSeparated first second hne)
        (targetMiddle.tube first)
        (targetMiddle.tube second)
        (htargetMiddleLine first)
        (htargetMiddleLine second)
        (wz2PaperLiteralOrdinaryRescaledTube_axis
          (sourceScale.coarse.tube first) anchor hsigma)
        (wz2PaperLiteralOrdinaryRescaledTube_axis
          (sourceScale.coarse.tube second) anchor hsigma)
  have hDoubledFibers :
      ∀ first second, first ≠ second →
        Disjoint
          (wz2PaperOrdinaryDilatedFiberIndices
            2 targetFine targetMiddle first)
          (wz2PaperOrdinaryDilatedFiberIndices
            2 targetFine targetMiddle second) := by
    intro first second hne
    rw [Finset.disjoint_left]
    intro target hfirst hsecond
    rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff] at hfirst hsecond
    have hfirstDistance :=
      localization.centered_doubled_lineDistance_le
        target first hfirst
    have hsecondDistance :=
      localization.centered_doubled_lineDistance_le
        target second hsecond
    have htriangle :=
      wz1PaperLineDistance_triangle
        (targetMiddle.tube first)
        (targetFine.tube target)
        (targetMiddle.tube second)
    have hsymmetry :
        wz1PaperLineDistance
            (targetMiddle.tube first)
            (targetFine.tube target) =
          wz1PaperLineDistance
            (targetFine.tube target)
            (targetMiddle.tube first) :=
      wz1PaperLineDistance_symm _ _
    rw [hsymmetry] at htriangle
    linarith [hTargetSeparated first second hne]
  let targetCover :=
    wz2PaperLiteralOrdinaryPurePartitioningCover_minimal
      sourceScale.delta_pos sourceScale.rho_pos hsigma
      hdeltaRho hsigmaOne
      sourceFine sourceScale.coarse anchor sourceScale.cover
      hFineMiddle hDoubledFibers
  have hSourceIndices :
      ∀ targetParent : Fin targetMiddle.card,
        Finset.image
            (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
              sourceFine anchor hsigma)
            (wz2PaperOrdinaryFullFiberIndices
              targetFine targetMiddle targetParent) =
          wz2PaperOrdinaryFullFiberIndices
            sourceFine sourceScale.coarse
            (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
              sourceScale.coarse anchor hsigma targetParent) := by
    intro targetParent
    exact
      wz2PaperLiteralOrdinary_fullFiber_source_indices_minimal
        sourceScale.delta_pos sourceScale.rho_pos hsigma
        hdeltaRho hsigmaOne
        sourceFine sourceScale.coarse anchor sourceScale.cover
        hFineMiddle hDoubledFibers targetParent
  have hCount :
      ∀ targetParent : Fin targetMiddle.card,
        wz2PaperOrdinaryFullFiberCount
            targetFine targetMiddle targetParent =
          wz2PaperOrdinaryFullFiberCount
            sourceFine sourceScale.coarse
            (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
              sourceScale.coarse anchor hsigma targetParent) := by
    intro targetParent
    unfold wz2PaperOrdinaryFullFiberCount
    rw [← hSourceIndices targetParent]
    norm_cast
    exact
      (Finset.card_image_of_injective _
        (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex_bijective
          sourceFine anchor hsigma).injective).symm
  refine
    {
      delta_pos := div_pos sourceScale.delta_pos hsigma
      rho_pos := div_pos sourceScale.rho_pos hsigma
      coarse := targetMiddle
      cover := targetCover
      full_fiber_uniform := ?_
      rescaledFiber := ?_
    }
  · intro first second
    rw [hCount first, hCount second]
    exact
      (sourceScale.full_fiber_uniform
        (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
          sourceScale.coarse anchor hsigma first)
        (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
          sourceScale.coarse anchor hsigma second)).trans <| by
        gcongr
        exact le_max_left _ _
  · intro targetParent
    let sourceParent :=
      wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
        sourceScale.coarse anchor hsigma targetParent
    let sourceFiber :=
      Classical.choice (sourceScale.rescaledFiber sourceParent)
    let targetJohn :=
      WZ2PaperAssouadUnitRescalingData.ofTube
        (targetMiddle.tube targetParent)
        (div_pos sourceScale.rho_pos hsigma)
    let transportInputs :=
      wz2PaperNestedActualJohnFullFiberTransportInputs_of_sourceImage
        anchor hsigma sourceParent targetParent
        (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
          sourceFine anchor hsigma)
        (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex_bijective
          sourceFine anchor hsigma).injective
        (hSourceIndices targetParent)
        (fun target _ =>
          wz2PaperLiteralOrdinary_family_literal_image_subset
            sourceScale.delta_pos hsigma hsigmaOne
            sourceFine anchor hFineAnchor target)
        sourceFiber.normalization targetJohn
    have htransported :
        WZ2PaperBodyConvexWolffBound
          (wz2PaperPureUnitRescaledFullFiberBodyFamily
            (fine := targetFine) (coarse := targetMiddle)
            targetParent targetJohn)
          ((81000000 : ENNReal) * C) :=
      wz2PaperBodyConvexWolffBound_of_nestedActualJohnFullFiber
        sourceScale.rho_pos hsigma hrhoSigma hsigmaOne
        sourceParent targetParent
        sourceFiber.normalization targetJohn
        transportInputs sourceFiber.convex_wolff
    refine
      ⟨{
        normalization := targetJohn
        convex_wolff := fun convexSet hconvex =>
          (htransported convexSet hconvex).trans ?_
      }⟩
    gcongr
    exact le_max_right _ _

end Kakeya.Assouad

end
