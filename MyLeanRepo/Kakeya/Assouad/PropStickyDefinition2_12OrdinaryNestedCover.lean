import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryRescaledTube
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralCommonRescalingLineCoverHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Factor2Packing

/-!
# Ordinary nested cover after literal paper rescaling

The repaired public target is centered at the transformed source midpoint and
uses the paper-positive source direction. This module proves strict ordinary
carrier nesting under one common literal rescaling and transports one source
pure cover to the pointwise target families.

The pure partitioning theorem assumes genuine pairwise disjointness of the
centered doubled target-middle carriers. A lower bound on the paper
`lineDistance` alone is not sufficient for finite unit-segment carriers:
two nearly vertical lines can be far apart at `z = 0` while their unit
segments are centered near a common intersection far from `z = 0`. Their
centered doubles then overlap. Thus the historical cropped full-line
separation theorem is not identified with the public centered `2A` condition.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric

/-- The repaired target carrier is invariant under source reversal. -/
theorem wz2PaperLiteralOrdinaryRescaledTube_reverse_carrier
    {delta sigma : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube sigma)
    (hsigma : 0 < sigma)
    (hline : WZ1PaperTubeInLineClass source) :
    (wz2PaperLiteralOrdinaryRescaledTube
        (reverseTube source) anchor hsigma).carrier =
      (wz2PaperLiteralOrdinaryRescaledTube
        source anchor hsigma).carrier := by
  rw [wz2PaperLiteralOrdinaryRescaledTube_reverse
    source anchor hsigma hline]

lemma wz2PaperSourceMidpoint_dist_le_five_mul_of_carrier_subset
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (fine : Kakeya.DeltaTube delta)
    (middle : Kakeya.DeltaTube rho)
    (hcontained : fine.carrier ⊆ middle.carrier) :
    dist (wz2PaperTubeMidpoint fine) (wz2PaperTubeMidpoint middle) ≤
      5 * rho := by
  rcases containment_alignment_bound hdelta.le hrho fine middle hcontained with
    hsame | hreversed
  · rw [dist_eq_norm]
    have hdecompose :
        wz2PaperTubeMidpoint fine - wz2PaperTubeMidpoint middle =
          (fine.base - middle.base) +
            (1 / 2 : ℝ) • (fine.direction - middle.direction) := by
      unfold wz2PaperTubeMidpoint
      module
    rw [hdecompose]
    calc
      ‖(fine.base - middle.base) +
          (1 / 2 : ℝ) • (fine.direction - middle.direction)‖ ≤
          ‖fine.base - middle.base‖ +
            ‖(1 / 2 : ℝ) • (fine.direction - middle.direction)‖ :=
        norm_add_le _ _
      _ = ‖middle.base - fine.base‖ +
          (1 / 2 : ℝ) * ‖fine.direction - middle.direction‖ := by
        rw [norm_sub_rev, norm_smul, Real.norm_eq_abs]
        norm_num
      _ ≤ 3 * rho + (1 / 2 : ℝ) * (4 * rho) := by
        exact add_le_add hsame.2
          (mul_le_mul_of_nonneg_left hsame.1 (by norm_num))
      _ = 5 * rho := by ring
  · rw [dist_eq_norm]
    have hdecompose :
        wz2PaperTubeMidpoint fine - wz2PaperTubeMidpoint middle =
          ((fine.base + fine.direction) - middle.base) -
            (1 / 2 : ℝ) • (fine.direction + middle.direction) := by
      unfold wz2PaperTubeMidpoint
      module
    rw [hdecompose]
    calc
      ‖((fine.base + fine.direction) - middle.base) -
          (1 / 2 : ℝ) • (fine.direction + middle.direction)‖ ≤
          ‖(fine.base + fine.direction) - middle.base‖ +
            ‖(1 / 2 : ℝ) • (fine.direction + middle.direction)‖ :=
        norm_sub_le _ _
      _ = ‖middle.base - (fine.base + fine.direction)‖ +
          (1 / 2 : ℝ) * ‖fine.direction + middle.direction‖ := by
        rw [norm_sub_rev, norm_smul, Real.norm_eq_abs]
        norm_num
      _ ≤ 3 * rho + (1 / 2 : ℝ) * (4 * rho) := by
        exact add_le_add hreversed.2
          (mul_le_mul_of_nonneg_left hreversed.1 (by norm_num))
      _ = 5 * rho := by ring

lemma wz2PaperLiteralOrdinaryRescaledDirection_dist_le
    {delta rho sigma : ℝ}
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1)
    (fine : Kakeya.DeltaTube delta)
    (middle : Kakeya.DeltaTube rho)
    (anchor : Kakeya.DeltaTube sigma)
    (hcover : WZ1PaperTubeCovers fine middle) :
    ‖(wz2PaperLiteralOrdinaryRescaledTube fine anchor hsigma).direction -
        (wz2PaperLiteralOrdinaryRescaledTube middle anchor hsigma).direction‖ ≤
      rho / (2 * sigma) := by
  let fineDirection := wz1PaperDirection fine
  let middleDirection := wz1PaperDirection middle
  let anchorDirection := wz1PaperDirection anchor
  let rotation := householderToE3 anchorDirection
    (wz1PaperDirection_norm anchor)
  let fineRotated := rotation fineDirection
  let middleRotated := rotation middleDirection
  let fineImage := transverseScaleLin sigma fineRotated
  let middleImage := transverseScaleLin sigma middleRotated
  have hfineRotatedNorm : ‖fineRotated‖ = 1 := by
    rw [show ‖fineRotated‖ = ‖fineDirection‖ by
      exact householderToE3_norm anchorDirection
        (wz1PaperDirection_norm anchor) fineDirection]
    exact wz1PaperDirection_norm fine
  have hmiddleRotatedNorm : ‖middleRotated‖ = 1 := by
    rw [show ‖middleRotated‖ = ‖middleDirection‖ by
      exact householderToE3_norm anchorDirection
        (wz1PaperDirection_norm anchor) middleDirection]
    exact wz1PaperDirection_norm middle
  have hfineImageNorm : 1 ≤ ‖fineImage‖ :=
    transverseScaleLin_norm_ge_one hfineRotatedNorm hsigma hsigmaOne
  have hmiddleImageNorm : 1 ≤ ‖middleImage‖ :=
    transverseScaleLin_norm_ge_one hmiddleRotatedNorm hsigma hsigmaOne
  have hsourceDirection :
      ‖fineDirection - middleDirection‖ ≤ rho / 2 :=
    (unit_norm_sub_le_angle
      (wz1PaperDirection_norm fine)
      (wz1PaperDirection_norm middle)).trans hcover.components.2
  have himageDifference :
      ‖fineImage - middleImage‖ ≤ rho / (2 * sigma) := by
    have hlinear :
        fineImage - middleImage =
          transverseScaleLin sigma
            (rotation (fineDirection - middleDirection)) := by
      dsimp only [fineImage, middleImage, fineRotated, middleRotated]
      rw [← map_sub, ← map_sub]
    rw [hlinear]
    calc
      ‖transverseScaleLin sigma
          (rotation (fineDirection - middleDirection))‖ ≤
          (1 / sigma) * ‖rotation (fineDirection - middleDirection)‖ :=
        transverseScaleLin_norm_bound sigma hsigma hsigmaOne _
      _ = (1 / sigma) * ‖fineDirection - middleDirection‖ := by
        rw [householderToE3_norm]
      _ ≤ (1 / sigma) * (rho / 2) := by gcongr
      _ = rho / (2 * sigma) := by
        field_simp [hsigma.ne']
  have hnormalize :
      ‖NormedSpace.normalize fineImage -
          NormedSpace.normalize middleImage‖ ≤
        rho / (2 * sigma) :=
    (norm_normalize_sub_normalize_le_norm_sub
      hfineImageNorm hmiddleImageNorm).trans himageDifference
  change
    ‖NormedSpace.normalize
          (wz2PaperLiteralUnitRescalingLinear anchor fineDirection) -
        NormedSpace.normalize
          (wz2PaperLiteralUnitRescalingLinear anchor middleDirection)‖ ≤
      rho / (2 * sigma)
  have hfineLiteral :
      wz2PaperLiteralUnitRescalingLinear anchor fineDirection =
        (1 / 100 : ℝ) • fineImage := by rfl
  have hmiddleLiteral :
      wz2PaperLiteralUnitRescalingLinear anchor middleDirection =
        (1 / 100 : ℝ) • middleImage := by rfl
  rw [hfineLiteral, hmiddleLiteral,
    NormedSpace.normalize_smul_of_pos (by norm_num : (0 : ℝ) < 1 / 100),
    NormedSpace.normalize_smul_of_pos (by norm_num : (0 : ℝ) < 1 / 100)]
  exact hnormalize

theorem wz2_paper_literal_ordinary_nested_cover
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hdeltaRho : 100 * delta ≤ rho)
    (_hrhoSigma : rho ≤ sigma)
    (hsigmaOne : sigma ≤ 1)
    (fine : Kakeya.DeltaTube delta)
    (middle : Kakeya.DeltaTube rho)
    (anchor : Kakeya.DeltaTube sigma)
    (_hfine : WZ1PaperTubeInLineClass fine)
    (_hmiddle : WZ1PaperTubeInLineClass middle)
    (_hanchor : WZ1PaperTubeInLineClass anchor)
    (hcoverFineMiddle : WZ1PaperTubeCovers fine middle)
    (hcarrierFineMiddle : fine.carrier ⊆ middle.carrier)
    (_hcoverFineAnchor : WZ1PaperTubeCovers fine anchor)
    (_hcoverMiddleAnchor : WZ1PaperTubeCovers middle anchor) :
    (wz2PaperLiteralOrdinaryRescaledTube fine anchor hsigma).carrier ⊆
      (wz2PaperLiteralOrdinaryRescaledTube middle anchor hsigma).carrier := by
  let targetFine := wz2PaperLiteralOrdinaryRescaledTube fine anchor hsigma
  let targetMiddle := wz2PaperLiteralOrdinaryRescaledTube middle anchor hsigma
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
          (wz2PaperTubeMidpoint fine - wz2PaperTubeMidpoint middle)‖ ≤
          ‖wz2PaperTubeMidpoint fine - wz2PaperTubeMidpoint middle‖ /
            (100 * sigma) :=
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
      IsCompact (Kakeya.unitSegment targetFine.base targetFine.direction) :=
    isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  change point ∈ Metric.cthickening (delta / sigma)
    (Kakeya.unitSegment targetFine.base targetFine.direction) at hpoint
  rw [hcompact.cthickening_eq_biUnion_closedBall hdeltaSigma.le] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨fineAxisPoint, hfineAxisPoint, hpointFineAxis⟩
  rcases hfineAxisPoint with ⟨parameter, hparameter, rfl⟩
  let middleAxisPoint := targetMiddle.base + parameter • targetMiddle.direction
  have hmiddleAxisPoint :
      middleAxisPoint ∈
        Kakeya.unitSegment targetMiddle.base targetMiddle.direction :=
    ⟨parameter, hparameter, rfl⟩
  have hpointFineAxisDist :
      dist point (targetFine.base + parameter • targetFine.direction) ≤
        delta / sigma := by
    simpa [Metric.mem_closedBall] using hpointFineAxis
  have haxisPointDist :
      dist (targetFine.base + parameter • targetFine.direction)
          middleAxisPoint ≤
        rho / (20 * sigma) + (1 / 2 : ℝ) * (rho / (2 * sigma)) := by
    rw [dist_eq_norm]
    have hdecompose :
        targetFine.base + parameter • targetFine.direction - middleAxisPoint =
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
              (targetFine.direction - targetMiddle.direction)‖ :=
        norm_add_le _ _
      _ = ‖wz2PaperTubeMidpoint targetFine -
              wz2PaperTubeMidpoint targetMiddle‖ +
            |parameter - 1 / 2| *
              ‖targetFine.direction - targetMiddle.direction‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ rho / (20 * sigma) +
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
        dist point (targetFine.base + parameter • targetFine.direction) +
          dist (targetFine.base + parameter • targetFine.direction)
            middleAxisPoint := dist_triangle _ _ _
    _ ≤ delta / sigma +
          (rho / (20 * sigma) + (1 / 2 : ℝ) * (rho / (2 * sigma))) := by
      gcongr
    _ ≤ rho / sigma := by
      field_simp [hsigma.ne']
      nlinarith [hdeltaRho]

attribute [local instance] Classical.propDecidable

/-- Apply the repaired ordinary constructor pointwise, preserving indices. -/
noncomputable def wz2PaperLiteralOrdinaryRescaledFamily
    {delta sigma : ℝ}
    (source : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube sigma)
    (hsigma : 0 < sigma) :
    Kakeya.Streamlined.TubeFamily (delta / sigma) where
  card := source.card
  tube index :=
    wz2PaperLiteralOrdinaryRescaledTube
      (source.tube index) anchor hsigma

/--
The actual centered-doubled separation required by Definition 2.12.

This is a stronger conditional input; this module does not derive it from the
historical cropped full-line `lineDistance` separation.
-/
def WZ2PaperOrdinaryCenteredDoubledSeparated
    {rho : ℝ}
    (family : Kakeya.Streamlined.TubeFamily rho) : Prop :=
  ∀ first second, first ≠ second →
    Disjoint
      (wz2PaperCenteredDilatedCarrier 2 (family.tube first))
      (wz2PaperCenteredDilatedCarrier 2 (family.tube second))

/-- The pointwise ordinary construction has the identity source index. -/
def wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
    {delta sigma : ℝ}
    (source : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube sigma)
    (hsigma : 0 < sigma) :
    Fin (wz2PaperLiteralOrdinaryRescaledFamily source anchor hsigma).card →
      Fin source.card :=
  fun index => index

@[simp] theorem wz2PaperLiteralOrdinaryRescaledFamilySourceIndex_apply
    {delta sigma : ℝ}
    (source : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube sigma)
    (hsigma : 0 < sigma)
    (index : Fin
      (wz2PaperLiteralOrdinaryRescaledFamily source anchor hsigma).card) :
    wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
        source anchor hsigma index = index :=
  rfl

theorem wz2PaperLiteralOrdinaryRescaledFamilySourceIndex_bijective
    {delta sigma : ℝ}
    (source : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube sigma)
    (hsigma : 0 < sigma) :
    Function.Bijective
      (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
        source anchor hsigma) := by
  constructor
  · intro first second h
    exact Fin.ext (congrArg Fin.val h)
  · intro sourceIndex
    exact ⟨sourceIndex, rfl⟩

/-- The inverse identity reindex from a source family to its target family. -/
def wz2PaperLiteralOrdinaryRescaledFamilyTargetIndex
    {delta sigma : ℝ}
    (source : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube sigma)
    (hsigma : 0 < sigma) :
    Fin source.card →
      Fin (wz2PaperLiteralOrdinaryRescaledFamily source anchor hsigma).card :=
  fun index => index

@[simp] theorem wz2PaperLiteralOrdinaryRescaledFamilyTargetIndex_apply
    {delta sigma : ℝ}
    (source : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube sigma)
    (hsigma : 0 < sigma)
    (index : Fin source.card) :
    wz2PaperLiteralOrdinaryRescaledFamilyTargetIndex
        source anchor hsigma index = index :=
  rfl

/-- The repaired ordinary target over the source-cover parent strictly
contains the corresponding target fine tube. -/
theorem wz2PaperLiteralOrdinary_assigned_target_containment
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hdeltaRho : 100 * delta ≤ rho)
    (hrhoSigma : rho ≤ sigma)
    (hsigmaOne : sigma ≤ 1)
    (sourceFine : Kakeya.Streamlined.TubeFamily delta)
    (sourceMiddle : Kakeya.Streamlined.TubeFamily rho)
    (anchor : Kakeya.DeltaTube sigma)
    (sourceCover : WZ2PaperPurePartitioningCover sourceFine sourceMiddle)
    (hfine : WZ1PaperIsLineClass sourceFine)
    (hmiddle : WZ1PaperIsLineClass sourceMiddle)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hFineMiddle : ∀ source,
      WZ1PaperTubeCovers
        (sourceFine.tube source)
        (sourceMiddle.tube (sourceCover.parent source)))
    (hFineAnchor : ∀ source,
      WZ1PaperTubeCovers (sourceFine.tube source) anchor)
    (hMiddleAnchor : ∀ middleIndex,
      WZ1PaperTubeCovers (sourceMiddle.tube middleIndex) anchor)
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
  change
    (wz2PaperLiteralOrdinaryRescaledTube
      (sourceFine.tube source) anchor hsigma).carrier ⊆
      (wz2PaperLiteralOrdinaryRescaledTube
        (sourceMiddle.tube (sourceCover.parent source))
        anchor hsigma).carrier
  exact
    wz2_paper_literal_ordinary_nested_cover
      hdelta hrho hsigma hdeltaRho hrhoSigma hsigmaOne
      (sourceFine.tube source)
      (sourceMiddle.tube (sourceCover.parent source)) anchor
      (hfine source) (hmiddle (sourceCover.parent source)) hanchor
      (hFineMiddle source)
      ((mem_wz2PaperOrdinaryFullFiberIndices_iff
        (sourceCover.parent source) source).mp
        (sourceCover.parent_mem_fullFiber source))
      (hFineAnchor source) (hMiddleAnchor (sourceCover.parent source))

/-- Target strict full-fiber membership is exactly the transported source
cover parent. -/
theorem wz2PaperLiteralOrdinary_target_mem_fullFiber_iff_parent_eq
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hdeltaRho : 100 * delta ≤ rho)
    (hrhoSigma : rho ≤ sigma)
    (hsigmaOne : sigma ≤ 1)
    (sourceFine : Kakeya.Streamlined.TubeFamily delta)
    (sourceMiddle : Kakeya.Streamlined.TubeFamily rho)
    (anchor : Kakeya.DeltaTube sigma)
    (sourceCover : WZ2PaperPurePartitioningCover sourceFine sourceMiddle)
    (hfine : WZ1PaperIsLineClass sourceFine)
    (hmiddle : WZ1PaperIsLineClass sourceMiddle)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hFineMiddle : ∀ source,
      WZ1PaperTubeCovers
        (sourceFine.tube source)
        (sourceMiddle.tube (sourceCover.parent source)))
    (hFineAnchor : ∀ source,
      WZ1PaperTubeCovers (sourceFine.tube source) anchor)
    (hMiddleAnchor : ∀ middleIndex,
      WZ1PaperTubeCovers (sourceMiddle.tube middleIndex) anchor)
    (hTargetSeparated :
      WZ2PaperOrdinaryCenteredDoubledSeparated
        (wz2PaperLiteralOrdinaryRescaledFamily
          sourceMiddle anchor hsigma))
    (candidate : Fin
      (wz2PaperLiteralOrdinaryRescaledFamily
        sourceMiddle anchor hsigma).card)
    (target : Fin
      (wz2PaperLiteralOrdinaryRescaledFamily
        sourceFine anchor hsigma).card) :
    target ∈ wz2PaperOrdinaryFullFiberIndices
        (wz2PaperLiteralOrdinaryRescaledFamily
          sourceFine anchor hsigma)
        (wz2PaperLiteralOrdinaryRescaledFamily
          sourceMiddle anchor hsigma)
        candidate ↔
      sourceCover.parent
          (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
            sourceFine anchor hsigma target) =
        wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
          sourceMiddle anchor hsigma candidate := by
  let source :=
    wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
      sourceFine anchor hsigma target
  let assigned :=
    wz2PaperLiteralOrdinaryRescaledFamilyTargetIndex
      sourceMiddle anchor hsigma (sourceCover.parent source)
  have hassigned :=
    wz2PaperLiteralOrdinary_assigned_target_containment
      hdelta hrho hsigma hdeltaRho hrhoSigma hsigmaOne
      sourceFine sourceMiddle anchor sourceCover
      hfine hmiddle hanchor hFineMiddle hFineAnchor hMiddleAnchor target
  rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
  change
    ((wz2PaperLiteralOrdinaryRescaledFamily
        sourceFine anchor hsigma).tube target).carrier ⊆
        ((wz2PaperLiteralOrdinaryRescaledFamily
          sourceMiddle anchor hsigma).tube candidate).carrier ↔
      sourceCover.parent source =
        wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
          sourceMiddle anchor hsigma candidate
  constructor
  · intro hcandidate
    by_contra hneSource
    have hne : assigned ≠ candidate := by
      intro heq
      apply hneSource
      apply Fin.ext
      exact congrArg Fin.val heq
    have hscaleMiddle : 0 ≤ rho / sigma := div_nonneg hrho.le hsigma.le
    have hassignedDoubled := hassigned.trans
      (wz2_paper_carrier_subset_centeredDilatedTwo
        ((wz2PaperLiteralOrdinaryRescaledFamily
          sourceMiddle anchor hsigma).tube assigned) hscaleMiddle)
    have hcandidateDoubled := hcandidate.trans
      (wz2_paper_carrier_subset_centeredDilatedTwo
        ((wz2PaperLiteralOrdinaryRescaledFamily
          sourceMiddle anchor hsigma).tube candidate) hscaleMiddle)
    have hmidpoint :
        wz2PaperTubeMidpoint
            ((wz2PaperLiteralOrdinaryRescaledFamily
              sourceFine anchor hsigma).tube target) ∈
          ((wz2PaperLiteralOrdinaryRescaledFamily
            sourceFine anchor hsigma).tube target).carrier :=
      wz2_paper_tubeMidpoint_mem_carrier _
        (div_nonneg hdelta.le hsigma.le)
    exact
      Set.disjoint_left.mp (hTargetSeparated assigned candidate hne)
        (hassignedDoubled hmidpoint)
        (hcandidateDoubled hmidpoint)
  · intro hparent
    have hcandidate : assigned = candidate := by
      apply Fin.ext
      exact congrArg Fin.val hparent
    rw [← hcandidate]
    exact hassigned

/-- Source strict full-fiber membership is exactly the source-cover parent. -/
theorem wz2PaperLiteralOrdinary_source_mem_fullFiber_iff_parent_eq
    {delta rho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily delta}
    {sourceMiddle : Kakeya.Streamlined.TubeFamily rho}
    (sourceCover : WZ2PaperPurePartitioningCover sourceFine sourceMiddle)
    (hrho : 0 ≤ rho)
    (candidate : Fin sourceMiddle.card)
    (source : Fin sourceFine.card) :
    source ∈ wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceMiddle candidate ↔
      sourceCover.parent source = candidate :=
  sourceCover.mem_fullFiber_iff_parent_eq hrho candidate source

/-- The target ordinary family is a pure partitioning cover when the target
middle centered doubles are genuinely pairwise disjoint. -/
theorem wz2PaperLiteralOrdinaryPurePartitioningCover
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hdeltaRho : 100 * delta ≤ rho)
    (hrhoSigma : rho ≤ sigma)
    (hsigmaOne : sigma ≤ 1)
    (sourceFine : Kakeya.Streamlined.TubeFamily delta)
    (sourceMiddle : Kakeya.Streamlined.TubeFamily rho)
    (anchor : Kakeya.DeltaTube sigma)
    (sourceCover : WZ2PaperPurePartitioningCover sourceFine sourceMiddle)
    (hfine : WZ1PaperIsLineClass sourceFine)
    (hmiddle : WZ1PaperIsLineClass sourceMiddle)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hFineMiddle : ∀ source,
      WZ1PaperTubeCovers
        (sourceFine.tube source)
        (sourceMiddle.tube (sourceCover.parent source)))
    (hFineAnchor : ∀ source,
      WZ1PaperTubeCovers (sourceFine.tube source) anchor)
    (hMiddleAnchor : ∀ middleIndex,
      WZ1PaperTubeCovers (sourceMiddle.tube middleIndex) anchor)
    (hTargetSeparated :
      WZ2PaperOrdinaryCenteredDoubledSeparated
        (wz2PaperLiteralOrdinaryRescaledFamily
          sourceMiddle anchor hsigma)) :
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
    rw [wz2PaperLiteralOrdinary_target_mem_fullFiber_iff_parent_eq
      hdelta hrho hsigma hdeltaRho hrhoSigma hsigmaOne
      sourceFine sourceMiddle anchor sourceCover
      hfine hmiddle hanchor hFineMiddle hFineAnchor hMiddleAnchor
      hTargetSeparated assigned target]
    rfl
  doubled_fibers_disjoint first second hne := by
    rw [Finset.disjoint_left]
    intro target hfirst hsecond
    rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff] at hfirst hsecond
    have hmidpoint :
        wz2PaperTubeMidpoint
            ((wz2PaperLiteralOrdinaryRescaledFamily
              sourceFine anchor hsigma).tube target) ∈
          ((wz2PaperLiteralOrdinaryRescaledFamily
            sourceFine anchor hsigma).tube target).carrier :=
      wz2_paper_tubeMidpoint_mem_carrier _
        (div_nonneg hdelta.le hsigma.le)
    exact
      Set.disjoint_left.mp (hTargetSeparated first second hne)
        (hfirst hmidpoint) (hsecond hmidpoint)

/--
The target ordinary family is a pure partitioning cover when the exact
Definition 2.12 doubled-fiber disjointness is supplied directly.

Unlike `wz2PaperLiteralOrdinaryPurePartitioningCover`, this constructor does
not require the two doubled parent carriers themselves to be disjoint.
-/
theorem wz2PaperLiteralOrdinaryPurePartitioningCoverOfFiberDisjoint
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hdeltaRho : 100 * delta ≤ rho)
    (hrhoSigma : rho ≤ sigma)
    (hsigmaOne : sigma ≤ 1)
    (sourceFine : Kakeya.Streamlined.TubeFamily delta)
    (sourceMiddle : Kakeya.Streamlined.TubeFamily rho)
    (anchor : Kakeya.DeltaTube sigma)
    (sourceCover : WZ2PaperPurePartitioningCover sourceFine sourceMiddle)
    (hfine : WZ1PaperIsLineClass sourceFine)
    (hmiddle : WZ1PaperIsLineClass sourceMiddle)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hFineMiddle : ∀ source,
      WZ1PaperTubeCovers
        (sourceFine.tube source)
        (sourceMiddle.tube (sourceCover.parent source)))
    (hFineAnchor : ∀ source,
      WZ1PaperTubeCovers (sourceFine.tube source) anchor)
    (hMiddleAnchor : ∀ middleIndex,
      WZ1PaperTubeCovers (sourceMiddle.tube middleIndex) anchor)
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
      wz2PaperLiteralOrdinary_assigned_target_containment
        hdelta hrho hsigma hdeltaRho hrhoSigma hsigmaOne
        sourceFine sourceMiddle anchor sourceCover
        hfine hmiddle hanchor hFineMiddle hFineAnchor hMiddleAnchor target
  doubled_fibers_disjoint := hDoubledFibers

/-- Exact source-index equality in the form consumed by nested John
transport. -/
theorem wz2PaperLiteralOrdinary_fullFiber_source_indices
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hdeltaRho : 100 * delta ≤ rho)
    (hrhoSigma : rho ≤ sigma)
    (hsigmaOne : sigma ≤ 1)
    (sourceFine : Kakeya.Streamlined.TubeFamily delta)
    (sourceMiddle : Kakeya.Streamlined.TubeFamily rho)
    (anchor : Kakeya.DeltaTube sigma)
    (sourceCover : WZ2PaperPurePartitioningCover sourceFine sourceMiddle)
    (hfine : WZ1PaperIsLineClass sourceFine)
    (hmiddle : WZ1PaperIsLineClass sourceMiddle)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hFineMiddle : ∀ source,
      WZ1PaperTubeCovers
        (sourceFine.tube source)
        (sourceMiddle.tube (sourceCover.parent source)))
    (hFineAnchor : ∀ source,
      WZ1PaperTubeCovers (sourceFine.tube source) anchor)
    (hMiddleAnchor : ∀ middleIndex,
      WZ1PaperTubeCovers (sourceMiddle.tube middleIndex) anchor)
    (hTargetSeparated :
      WZ2PaperOrdinaryCenteredDoubledSeparated
        (wz2PaperLiteralOrdinaryRescaledFamily
          sourceMiddle anchor hsigma))
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
  ext source
  constructor
  · intro hsource
    rcases Finset.mem_image.mp hsource with
      ⟨target, htarget, htargetSource⟩
    rw [sourceCover.mem_fullFiber_iff_parent_eq hrho.le]
    rw [wz2PaperLiteralOrdinary_target_mem_fullFiber_iff_parent_eq
      hdelta hrho hsigma hdeltaRho hrhoSigma hsigmaOne
      sourceFine sourceMiddle anchor sourceCover
      hfine hmiddle hanchor hFineMiddle hFineAnchor hMiddleAnchor
      hTargetSeparated targetParent target] at htarget
    rw [htargetSource] at htarget
    exact htarget
  · intro hsource
    rw [sourceCover.mem_fullFiber_iff_parent_eq hrho.le] at hsource
    rcases
      (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex_bijective
        sourceFine anchor hsigma).surjective source with
      ⟨target, htargetSource⟩
    refine Finset.mem_image.mpr ⟨target, ?_, htargetSource⟩
    rw [wz2PaperLiteralOrdinary_target_mem_fullFiber_iff_parent_eq
      hdelta hrho hsigma hdeltaRho hrhoSigma hsigmaOne
      sourceFine sourceMiddle anchor sourceCover
      hfine hmiddle hanchor hFineMiddle hFineAnchor hMiddleAnchor
      hTargetSeparated targetParent target]
    rw [htargetSource]
    exact hsource

/-- Exact source-index equality for the fiber-disjoint constructor. -/
theorem
    wz2PaperLiteralOrdinary_fullFiber_source_indices_ofFiberDisjoint
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hdeltaRho : 100 * delta ≤ rho)
    (hrhoSigma : rho ≤ sigma)
    (hsigmaOne : sigma ≤ 1)
    (sourceFine : Kakeya.Streamlined.TubeFamily delta)
    (sourceMiddle : Kakeya.Streamlined.TubeFamily rho)
    (anchor : Kakeya.DeltaTube sigma)
    (sourceCover : WZ2PaperPurePartitioningCover sourceFine sourceMiddle)
    (hfine : WZ1PaperIsLineClass sourceFine)
    (hmiddle : WZ1PaperIsLineClass sourceMiddle)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hFineMiddle : ∀ source,
      WZ1PaperTubeCovers
        (sourceFine.tube source)
        (sourceMiddle.tube (sourceCover.parent source)))
    (hFineAnchor : ∀ source,
      WZ1PaperTubeCovers (sourceFine.tube source) anchor)
    (hMiddleAnchor : ∀ middleIndex,
      WZ1PaperTubeCovers (sourceMiddle.tube middleIndex) anchor)
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
    wz2PaperLiteralOrdinaryPurePartitioningCoverOfFiberDisjoint
      hdelta hrho hsigma hdeltaRho hrhoSigma hsigmaOne
      sourceFine sourceMiddle anchor sourceCover
      hfine hmiddle hanchor hFineMiddle hFineAnchor hMiddleAnchor
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
        wz2PaperLiteralOrdinary_assigned_target_containment
          hdelta hrho hsigma hdeltaRho hrhoSigma hsigmaOne
          sourceFine sourceMiddle anchor sourceCover
          hfine hmiddle hanchor hFineMiddle hFineAnchor hMiddleAnchor
          target
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
        wz2PaperLiteralOrdinary_assigned_target_containment
          hdelta hrho hsigma hdeltaRho hrhoSigma hsigmaOne
          sourceFine sourceMiddle anchor sourceCover
          hfine hmiddle hanchor hFineMiddle hFineAnchor hMiddleAnchor
          target
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

/-- Every target fine tube contains the exact first-stage literal image of its
source carrier. -/
theorem wz2PaperLiteralOrdinary_family_literal_image_subset
    {delta sigma : ℝ}
    (hdelta : 0 < delta)
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1)
    (sourceFine : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube sigma)
    (hFineAnchor : ∀ source,
      WZ1PaperTubeCovers (sourceFine.tube source) anchor)
    (target : Fin
      (wz2PaperLiteralOrdinaryRescaledFamily
        sourceFine anchor hsigma).card) :
    wz2PaperLiteralUnitRescalingMap anchor hsigma ''
        (sourceFine.tube
          (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
            sourceFine anchor hsigma target)).carrier ⊆
      ((wz2PaperLiteralOrdinaryRescaledFamily
        sourceFine anchor hsigma).tube target).carrier := by
  exact
    wz2PaperLiteral_image_carrier_subset_ordinary
      hdelta
      (sourceFine.tube
        (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
          sourceFine anchor hsigma target))
      anchor hsigma hsigmaOne
      (hFineAnchor
        (wz2PaperLiteralOrdinaryRescaledFamilySourceIndex
          sourceFine anchor hsigma target))

end Kakeya.Assouad
