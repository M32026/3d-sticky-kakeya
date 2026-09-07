import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CoaxialLineClass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CanonicalRescaledTubeSupport
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper
import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingIsotropicVolume

/-!
# One tube per source line in the final Proposition 6.3 rescaling

The raw isotropic rediscretization has `ceil scale` unit-length children over
every source tube.  Those siblings have the same coaxial line, so the raw
indexed family is not the family asserted by the paper's mild-rescaling
lemma.  This module uses one canonical raw child only to name that common
line, and then replaces its stored unit segment by the canonical segment
centred at the height-zero point of the line.

The construction is deliberately geometric only.  It records the exact
source-index equivalence, coaxial-line provenance, line-class inheritance,
and containment of the image of the restricted paper shading.  It does not
assert Definition 2.12 CWA; that requires a synchronized coarse retubing and
actual-John fiber transport.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set

attribute [local instance] Classical.propDecidable

/-- The first canonical slot of a positive isotropic rediscretization. -/
noncomputable def proposition63CanonicalIsotropicSlot
    {scale : ℝ} (hscale : 1 ≤ scale) : Fin (Nat.ceil scale) :=
  ⟨0, (Nat.one_le_ceil_iff (a := scale)).mpr
    (lt_of_lt_of_le zero_lt_one hscale)⟩

/-- The canonical ordinary unit tube on a paper coaxial line: use the
positively oriented paper direction and centre the stored unit segment at
the point of height zero.  This is the ordinary-tube representative of the
image line in the paper's mild-rescaling lemma. -/
def proposition63CenteredTube
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    Kakeya.DeltaTube delta where
  base := wz1TubeAxisZeroPoint tube -
    (1 / 2 : ℝ) • wz1PaperDirection tube
  direction := wz1PaperDirection tube
  direction_unit := wz1PaperDirection_norm tube

/-- Canonical centering changes neither the supporting affine line nor its
paper carrier. -/
theorem proposition63CenteredTube_axis
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    tubeAxisLine (proposition63CenteredTube tube) = tubeAxisLine tube := by
  ext point
  simp only [tubeAxisLine, Set.mem_setOf_eq]
  constructor
  · rintro ⟨parameter, rfl⟩
    rcases wz1TubeAxisZeroPoint_mem_axis tube with
      ⟨zeroParameter, hzeroParameter⟩
    change ∃ targetParameter : ℝ,
      (wz1TubeAxisZeroPoint tube -
          (1 / 2 : ℝ) • wz1PaperDirection tube) +
          parameter • wz1PaperDirection tube =
        tube.base + targetParameter • tube.direction
    unfold wz1PaperDirection
    split_ifs
    · refine ⟨zeroParameter - 1 / 2 + parameter, ?_⟩
      rw [hzeroParameter]
      module
    · refine ⟨zeroParameter + 1 / 2 - parameter, ?_⟩
      rw [hzeroParameter]
      module
  · rintro ⟨parameter, rfl⟩
    rcases wz1TubeAxisZeroPoint_mem_axis tube with
      ⟨zeroParameter, hzeroParameter⟩
    change ∃ targetParameter : ℝ,
      tube.base + parameter • tube.direction =
        (wz1TubeAxisZeroPoint tube -
          (1 / 2 : ℝ) • wz1PaperDirection tube) +
          targetParameter • wz1PaperDirection tube
    unfold wz1PaperDirection
    split_ifs
    · refine ⟨parameter - zeroParameter + 1 / 2, ?_⟩
      rw [hzeroParameter]
      module
    · refine ⟨zeroParameter - parameter + 1 / 2, ?_⟩
      rw [hzeroParameter]
      module

/-- The stored unit segment of the canonical tube is centred at the
height-zero point of its supporting line. -/
@[simp] theorem proposition63CenteredTube_midpoint
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    wz2PaperTubeMidpoint (proposition63CenteredTube tube) =
      wz1TubeAxisZeroPoint tube := by
  simp only [wz2PaperTubeMidpoint, proposition63CenteredTube]
  module

/-- Canonical centering preserves the oriented paper direction. -/
@[simp] theorem proposition63CenteredTube_paperDirection
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube) :
    wz1PaperDirection (proposition63CenteredTube tube) =
      wz1PaperDirection tube := by
  have hpositive : 0 ≤ wz1PaperDirection tube 2 := by
    linarith [hline.1]
  change (if 0 ≤ wz1PaperDirection tube 2 then
      wz1PaperDirection tube else -wz1PaperDirection tube) =
    wz1PaperDirection tube
  rw [if_pos hpositive]

/-- The canonical representative is idempotent on a paper line. -/
@[simp] theorem proposition63CenteredTube_idem
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube) :
    proposition63CenteredTube (proposition63CenteredTube tube) =
      proposition63CenteredTube tube := by
  rw [Kakeya.DeltaTube.mk.injEq]
  constructor
  · change
      wz1TubeAxisZeroPoint (proposition63CenteredTube tube) -
          (1 / 2 : ℝ) •
            wz1PaperDirection (proposition63CenteredTube tube) =
        wz1TubeAxisZeroPoint tube -
          (1 / 2 : ℝ) • wz1PaperDirection tube
    rw [proposition63CenteredTube_paperDirection tube hline]
    have hcenteredLine :
        WZ1PaperTubeInLineClass (proposition63CenteredTube tube) :=
      paperTubeInLineClass_of_same_axis hline
        (proposition63CenteredTube_axis tube)
    have hzero := wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
      hcenteredLine.vertical
      (show wz1TubeAxisZeroPoint tube ∈
          tubeAxisLine (proposition63CenteredTube tube) by
        rw [proposition63CenteredTube_axis]
        exact wz1TubeAxisZeroPoint_mem_axis tube)
      (wz1TubeAxisZeroPoint_coord_two tube hline.vertical)
    rw [hzero]
  · exact proposition63CenteredTube_paperDirection tube hline

/-- The canonical midpoint is uniformly localized in the paper line class. -/
theorem proposition63CenteredTube_midpoint_norm_le_three
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube) :
    ‖wz2PaperTubeMidpoint (proposition63CenteredTube tube)‖ ≤ 3 := by
  rw [proposition63CenteredTube_midpoint]
  let point := wz1TubeAxisZeroPoint tube
  have hzero : point 2 = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube hline.vertical
  have hnorm :
      ‖point‖ ^ 2 = point 0 ^ 2 + point 1 ^ 2 + point 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    ring
  have hzeroBounds := abs_le.mp hline.2.1
  have honeBounds := abs_le.mp hline.2.2
  have hzeroBound : point 0 ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    nlinarith
  have honeBound : point 1 ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    nlinarith
  change ‖point‖ ≤ 3
  nlinarith [norm_nonneg point]

/-- The raw-child index selected over one source index. -/
def proposition63MildRescalingRawIndex
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceShading center) :
    Fin sourceFamily.card ↪ Fin raw.family.card :=
  { toFun := fun source =>
      raw.childAt source (proposition63CanonicalIsotropicSlot hscale)
    inj' := by
      intro first second heq
      have hparent := congrArg raw.sourceParent heq
      simpa [raw.sourceParent_childAt] using hparent }

/-- Put the canonical centred unit segment on the rescaled coaxial line of
every source tube.  The first raw child is used only as a witness naming the
common rescaled line. -/
def proposition63MildRescalingFamily
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceShading center) :
    Kakeya.Streamlined.TubeFamily (scale * sourceDelta) where
  card := sourceFamily.card
  tube source := proposition63CenteredTube <|
    raw.family.tube
      (proposition63MildRescalingRawIndex hscale raw source)

/-- The isotropic similarity as an affine equivalence.  This is the common
physical coordinate change used later between the source and target
outer-John charts. -/
noncomputable def proposition63IsotropicAffineEquiv
    (center : Point3) (scale : ℝ) (hscale : 0 < scale) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  AffineEquiv.ofLinearEquiv
    (LinearEquiv.smulOfNeZero ℝ Point3 scale hscale.ne') center 0

@[simp] theorem proposition63IsotropicAffineEquiv_apply
    (center : Point3) (scale : ℝ) (hscale : 0 < scale)
    (point : Point3) :
    proposition63IsotropicAffineEquiv center scale hscale point =
      wz1IsotropicRescalingMap center scale point := by
  rw [proposition63IsotropicAffineEquiv, AffineEquiv.ofLinearEquiv_apply]
  simp only [LinearEquiv.smulOfNeZero_apply, vsub_eq_sub, vadd_eq_add,
    add_zero, wz1IsotropicRescalingMap]

/-- The retubed family has definitionally the same cardinality as the source
family. -/
@[simp] theorem proposition63MildRescalingFamily_card
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceShading center) :
    (proposition63MildRescalingFamily hscale raw).card =
      sourceFamily.card := rfl

/-- The selected target and source index types are canonically identical. -/
def proposition63MildRescalingIndexEquiv
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceShading center) :
    Fin (proposition63MildRescalingFamily hscale raw).card ≃
      Fin sourceFamily.card :=
  Equiv.refl _

/-- Every selected target tube has the isotropic image of its corresponding
source coaxial line. -/
theorem proposition63MildRescalingFamily_axis_provenance
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceShading center)
    (index : Fin (proposition63MildRescalingFamily hscale raw).card) :
    tubeAxisLine ((proposition63MildRescalingFamily hscale raw).tube index) =
      wz1IsotropicRescalingMap center scale ''
        tubeAxisLine (sourceFamily.tube index) := by
  change tubeAxisLine
      (proposition63CenteredTube
        (raw.family.tube
          (proposition63MildRescalingRawIndex hscale raw index))) = _
  rw [proposition63CenteredTube_axis]
  rw [raw.axis_provenance]
  rw [show raw.sourceParent
      (proposition63MildRescalingRawIndex hscale raw index) = index by
    exact raw.sourceParent_childAt index
      (proposition63CanonicalIsotropicSlot hscale)]

/-- The centred target uses the positively oriented paper direction of the
corresponding source line. -/
theorem proposition63MildRescalingFamily_direction_provenance
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceShading center)
    (index : Fin (proposition63MildRescalingFamily hscale raw).card) :
    ((proposition63MildRescalingFamily hscale raw).tube index).direction =
      wz1PaperDirection (sourceFamily.tube index) := by
  change wz1PaperDirection
      (raw.family.tube
        (proposition63MildRescalingRawIndex hscale raw index)) = _
  have hdirection := raw.direction_provenance
    (proposition63MildRescalingRawIndex hscale raw index)
  have hparent : raw.sourceParent
      (proposition63MildRescalingRawIndex hscale raw index) = index :=
    raw.sourceParent_childAt index
      (proposition63CanonicalIsotropicSlot hscale)
  rw [hparent] at hdirection
  unfold wz1PaperDirection
  rw [hdirection]

/-- Any line-class proof for the raw rediscretization restricts to the
one-per-source family. -/
theorem proposition63MildRescalingFamily_lineClass
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceShading center)
    (hraw : WZ1PaperIsLineClass raw.family) :
    WZ1PaperIsLineClass
      (proposition63MildRescalingFamily hscale raw) := by
  intro index
  apply paperTubeInLineClass_of_same_axis
    (hraw (proposition63MildRescalingRawIndex hscale raw index))
  exact proposition63CenteredTube_axis _

/-- Every target tube is already the canonical centred representative of its
paper line. -/
theorem proposition63MildRescalingFamily_centered
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceShading center)
    (hraw : WZ1PaperIsLineClass raw.family)
    (index : Fin (proposition63MildRescalingFamily hscale raw).card) :
    proposition63CenteredTube
        ((proposition63MildRescalingFamily hscale raw).tube index) =
      (proposition63MildRescalingFamily hscale raw).tube index := by
  exact proposition63CenteredTube_idem _
    (hraw (proposition63MildRescalingRawIndex hscale raw index))

/-- The canonical target midpoints lie in the fixed local window used by the
ordinary doubled-fibre separation lemma. -/
theorem proposition63MildRescalingFamily_midpoint_local
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceShading center)
    (hraw : WZ1PaperIsLineClass raw.family)
    (index : Fin (proposition63MildRescalingFamily hscale raw).card) :
    ‖wz2PaperTubeMidpoint
        ((proposition63MildRescalingFamily hscale raw).tube index)‖ ≤ 3 := by
  exact proposition63CenteredTube_midpoint_norm_le_three _
    (hraw (proposition63MildRescalingRawIndex hscale raw index))

/-- At the small target radii used in Proposition 6.3, every canonical
one-per-line target tube is supported in the ordinary unit ball.  The sharper
midpoint estimate here uses the defining `L₃` bounds at height zero. -/
theorem proposition63MildRescalingFamily_isInUnitBall
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hsourceDelta : 0 < sourceDelta)
    (hscale : 1 ≤ scale)
    (hscaleDelta : scale * sourceDelta ≤ 1 / 54)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceShading center)
    (hraw : WZ1PaperIsLineClass raw.family) :
    (proposition63MildRescalingFamily hscale raw).IsInUnitBall := by
  intro index
  let target := (proposition63MildRescalingFamily hscale raw).tube index
  have htargetLine : WZ1PaperTubeInLineClass target :=
    proposition63MildRescalingFamily_lineClass hscale raw hraw index
  have htargetCentered : proposition63CenteredTube target = target :=
    proposition63MildRescalingFamily_centered hscale raw hraw index
  have hmidpointZero : wz2PaperTubeMidpoint target 2 = 0 := by
    rw [← htargetCentered, proposition63CenteredTube_midpoint]
    exact wz1TubeAxisZeroPoint_coord_two target htargetLine.vertical
  have hmidpointZeroBound :
      |wz2PaperTubeMidpoint target 0| ≤ 1 / 3 := by
    rw [← htargetCentered, proposition63CenteredTube_midpoint]
    exact htargetLine.2.1
  have hmidpointOneBound :
      |wz2PaperTubeMidpoint target 1| ≤ 1 / 3 := by
    rw [← htargetCentered, proposition63CenteredTube_midpoint]
    exact htargetLine.2.2
  have hmidpointNormSq :
      ‖wz2PaperTubeMidpoint target‖ ^ 2 =
        (wz2PaperTubeMidpoint target 0) ^ 2 +
          (wz2PaperTubeMidpoint target 1) ^ 2 +
            (wz2PaperTubeMidpoint target 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    ring
  have hzeroSq : (wz2PaperTubeMidpoint target 0) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    nlinarith [abs_le.mp hmidpointZeroBound]
  have honeSq : (wz2PaperTubeMidpoint target 1) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    nlinarith [abs_le.mp hmidpointOneBound]
  have hmidpointNorm : ‖wz2PaperTubeMidpoint target‖ ≤ 13 / 27 := by
    have hnormNonnegative : 0 ≤ ‖wz2PaperTubeMidpoint target‖ := norm_nonneg _
    rw [hmidpointZero] at hmidpointNormSq
    norm_num at hmidpointNormSq
    nlinarith
  apply tube_isInUnitBall_of_midpoint_margin
    (mul_pos (lt_of_lt_of_le zero_lt_one hscale) hsourceDelta) target
  calc
    ‖wz2PaperTubeMidpoint target‖ + (1 / 2 + scale * sourceDelta) ≤
        13 / 27 + (1 / 2 + 1 / 54) := by
      gcongr
    _ ≤ 1 := by norm_num

/-- The full isotropic image of one source unit tube lies in a controlled
homothetic enlargement of its canonical centered target tube.  This is the
physical-space comparison used between the source and target John charts. -/
theorem proposition63_isotropic_source_carrier_subset_target_homothety
    {sourceDelta scale : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceShading center)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hrawLine : WZ1PaperIsLineClass raw.family)
    (hsourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3)
    (hcenterHeight : |center 2| ≤ 2)
    (index : Fin sourceFamily.card) :
    proposition63IsotropicAffineEquiv center scale
          (lt_of_lt_of_le zero_lt_one hscale) ''
        (sourceFamily.tube index).carrier ⊆
      AffineMap.homothety
          (wz2PaperTubeMidpoint
            ((proposition63MildRescalingFamily hscale raw).tube index))
          (22 * scale + 3) ''
        ((proposition63MildRescalingFamily hscale raw).tube index).carrier := by
  let source := sourceFamily.tube index
  let target := (proposition63MildRescalingFamily hscale raw).tube index
  let affine := proposition63IsotropicAffineEquiv center scale
    (lt_of_lt_of_le zero_lt_one hscale)
  let factor : ℝ := 22 * scale + 3
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hfactorPos : 0 < factor := by dsimp only [factor]; linarith
  have hfactorOne : 1 ≤ factor := by dsimp only [factor]; linarith
  have htargetLine : WZ1PaperTubeInLineClass target :=
    proposition63MildRescalingFamily_lineClass hscale raw
      hrawLine index
  have htargetCentered : proposition63CenteredTube target = target :=
    proposition63MildRescalingFamily_centered hscale raw
      hrawLine index
  have htargetMidpointTwo : wz2PaperTubeMidpoint target 2 = 0 := by
    rw [← htargetCentered, proposition63CenteredTube_midpoint]
    exact wz1TubeAxisZeroPoint_coord_two target htargetLine.vertical
  have htargetDirection : target.direction = wz1PaperDirection source :=
    proposition63MildRescalingFamily_direction_provenance hscale raw index
  have htargetDirectionTwo : (1 / 2 : ℝ) ≤ target.direction 2 := by
    rw [htargetDirection]
    exact (hsourceLine index).1
  have htargetAxis : tubeAxisLine target =
      affine '' tubeAxisLine source := by
    simpa [affine, proposition63IsotropicAffineEquiv_apply] using
      proposition63MildRescalingFamily_axis_provenance hscale raw index
  intro imagePoint himagePoint
  rcases himagePoint with ⟨point, hpoint, rfl⟩
  have hsourceCompact : IsCompact
      (Kakeya.unitSegment source.base source.direction) :=
    isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  rcases exists_dist_le_of_mem_cthickening_closed
      hsourceCompact.isClosed hsourceDelta.le hpoint with
    ⟨axisPoint, haxisPoint, hpointAxis⟩
  have haxisLine : axisPoint ∈ tubeAxisLine source := by
    rcases haxisPoint with ⟨parameter, _hparameter, hpointEq⟩
    exact ⟨parameter, hpointEq.symm⟩
  have himageAxis : affine axisPoint ∈ tubeAxisLine target := by
    rw [htargetAxis]
    exact ⟨axisPoint, haxisLine, rfl⟩
  have haxisAroundMidpoint : tubeAxisLine target =
      {point | ∃ parameter : ℝ, point =
        wz2PaperTubeMidpoint target + parameter • target.direction} := by
    ext point
    simp only [tubeAxisLine, Set.mem_setOf_eq]
    constructor
    · rintro ⟨parameter, rfl⟩
      exact ⟨parameter - 1 / 2, by
        dsimp only [wz2PaperTubeMidpoint]
        module⟩
    · rintro ⟨parameter, rfl⟩
      exact ⟨parameter + 1 / 2, by
        dsimp only [wz2PaperTubeMidpoint]
        module⟩
  rw [haxisAroundMidpoint] at himageAxis
  rcases himageAxis with ⟨parameter, haxisImage⟩
  have haxisPointNorm : ‖axisPoint‖ ≤ 7 / 2 := by
    rcases haxisPoint with ⟨t, ht, rfl⟩
    have hmidpointDifference :
        source.base + t • source.direction - wz2PaperTubeMidpoint source =
          (t - 1 / 2) • source.direction := by
      dsimp only [wz2PaperTubeMidpoint]
      module
    calc
      ‖source.base + t • source.direction‖ ≤
          ‖wz2PaperTubeMidpoint source‖ +
            ‖source.base + t • source.direction -
              wz2PaperTubeMidpoint source‖ := by
        simpa [add_comm] using norm_add_le
          (wz2PaperTubeMidpoint source)
          (source.base + t • source.direction -
            wz2PaperTubeMidpoint source)
      _ = ‖wz2PaperTubeMidpoint source‖ + |t - 1 / 2| := by
        rw [hmidpointDifference, norm_smul, Real.norm_eq_abs,
          source.direction_unit, mul_one]
      _ ≤ 3 + 1 / 2 := by
        exact add_le_add (hsourceMidpoint index) <|
          abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      _ = 7 / 2 := by norm_num
  have haxisCoordinate : |axisPoint 2| ≤ 7 / 2 :=
    (PiLp.norm_apply_le axisPoint 2).trans haxisPointNorm
  have himageCoordinate : |affine axisPoint 2| ≤ (11 / 2) * scale := by
    rw [proposition63IsotropicAffineEquiv_apply]
    simp only [wz1IsotropicRescalingMap, PiLp.smul_apply, smul_eq_mul]
    rw [abs_mul, abs_of_pos hscalePos]
    calc
      scale * |axisPoint 2 - center 2| ≤
          scale * (|axisPoint 2| + |center 2|) := by
        gcongr
        calc
          |axisPoint 2 - center 2| = |axisPoint 2 + (-center 2)| := by ring_nf
          _ ≤ |axisPoint 2| + |-center 2| := abs_add_le _ _
          _ = |axisPoint 2| + |center 2| := by rw [abs_neg]
      _ ≤ scale * (7 / 2 + 2) := by gcongr
      _ = (11 / 2) * scale := by ring
  have hparameterBound : |parameter| ≤ 11 * scale := by
    have hcoordinate : affine axisPoint 2 =
        parameter * target.direction 2 := by
      rw [haxisImage]
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        htargetMidpointTwo, zero_add]
    have habsCoordinate : |affine axisPoint 2| =
        |parameter| * target.direction 2 := by
      rw [hcoordinate, abs_mul, abs_of_nonneg
        (le_trans (by norm_num) htargetDirectionTwo)]
    have hproduct : |parameter| * target.direction 2 ≤
        (11 / 2) * scale := by
      rw [← habsCoordinate]
      exact himageCoordinate
    nlinarith [mul_le_mul_of_nonneg_left htargetDirectionTwo
      (abs_nonneg parameter)]
  let contractedAxis := wz2PaperTubeMidpoint target +
    (parameter / factor) • target.direction
  let contractedPoint := wz2PaperTubeMidpoint target +
    factor⁻¹ • (affine point - wz2PaperTubeMidpoint target)
  have hparameterContracted :
      1 / 2 + parameter / factor ∈ Set.Icc (0 : ℝ) 1 := by
    have habs : |parameter / factor| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hfactorPos]
      apply (div_le_iff₀ hfactorPos).2
      calc
        |parameter| ≤ 11 * scale := hparameterBound
        _ ≤ (1 / 2 : ℝ) * factor := by
          dsimp only [factor]
          linarith
    exact ⟨by linarith [abs_le.mp habs |>.1],
      by linarith [abs_le.mp habs |>.2]⟩
  have hcontractedAxis : contractedAxis ∈
      Kakeya.unitSegment target.base target.direction := by
    refine ⟨1 / 2 + parameter / factor, hparameterContracted, ?_⟩
    dsimp only [contractedAxis, wz2PaperTubeMidpoint]
    module
  have himageDistance : dist (affine point) (affine axisPoint) =
      scale * dist point axisPoint := by
    simp only [affine, proposition63IsotropicAffineEquiv_apply,
      wz1IsotropicRescalingMap, dist_eq_norm]
    rw [show
      scale • (point - center) - scale • (axisPoint - center) =
        scale • (point - axisPoint) by module,
      norm_smul, Real.norm_eq_abs, abs_of_pos hscalePos]
  have hcontractedDistance :
      dist contractedPoint contractedAxis ≤ scale * sourceDelta := by
    have hcontractedAxisEq : contractedAxis =
        wz2PaperTubeMidpoint target +
          factor⁻¹ • (affine axisPoint - wz2PaperTubeMidpoint target) := by
      rw [haxisImage]
      dsimp only [contractedAxis]
      simp only [div_eq_mul_inv, smul_smul]
      module
    rw [hcontractedAxisEq, dist_eq_norm]
    have hdifference : contractedPoint -
          (wz2PaperTubeMidpoint target +
            factor⁻¹ • (affine axisPoint - wz2PaperTubeMidpoint target)) =
        factor⁻¹ • (affine point - affine axisPoint) := by
      dsimp only [contractedPoint]
      module
    rw [hdifference, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hfactorPos), ← dist_eq_norm, himageDistance]
    calc
      factor⁻¹ * (scale * dist point axisPoint) ≤
          factor⁻¹ * (scale * sourceDelta) := by gcongr
      _ ≤ 1 * (scale * sourceDelta) := by
        gcongr
        exact (inv_le_one₀ hfactorPos).2 hfactorOne
      _ = scale * sourceDelta := one_mul _
  have hcontractedCarrier : contractedPoint ∈ target.carrier :=
    Metric.mem_cthickening_of_dist_le contractedPoint contractedAxis
      (scale * sourceDelta) _ hcontractedAxis hcontractedDistance
  refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
  rw [AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  have hcontractedDifference : contractedPoint -
      wz2PaperTubeMidpoint target =
        factor⁻¹ • (affine point - wz2PaperTubeMidpoint target) := by
    simp [contractedPoint]
  rw [hcontractedDifference, smul_smul,
    mul_inv_cancel₀ hfactorPos.ne', one_smul]
  abel

/-- A restricted source paper-shading point in the popular box is carried by
the corresponding one-per-line target paper tube. -/
theorem proposition63MildRescalingFamily_image_mem_paperCarrier
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceShading center)
    (hscale : 1 ≤ scale)
    (hsourceDelta : 0 < sourceDelta)
    (hscaleDeltaSmall : scale * sourceDelta < 1 / 54)
    (width : ℝ)
    (hwidth : width = 1 / (9 * scale) - 6 * sourceDelta)
    (index : Fin (proposition63MildRescalingFamily hscale raw).card)
    (point : Point3)
    (hpoint : point ∈
      wz1PaperTubeCarrier
        (sourceFamily.tube index))
    (hbox : ∀ coordinate : Fin 3,
      |point coordinate - center coordinate| ≤ width) :
    wz1IsotropicRescalingMap center scale point ∈
      wz1PaperTubeCarrier
        ((proposition63MildRescalingFamily hscale raw).tube index) := by
  apply proposition63_rescaled_point_in_paper_carrier
    hsourceDelta (lt_of_lt_of_le zero_lt_one hscale)
    hscaleDeltaSmall center width hwidth hpoint hbox
  exact proposition63MildRescalingFamily_axis_provenance hscale raw index

/-- The exact image shading on the one-per-source retubed family. -/
noncomputable def proposition63MildRescalingShading
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceRawShading center)
    (sourcePaperShading : WZ1PaperTubeShading sourceFamily)
    (region : Set Point3)
    (hsourceDelta : 0 < sourceDelta)
    (hscaleDeltaSmall : scale * sourceDelta < 1 / 54)
    (width : ℝ)
    (hwidth : width = 1 / (9 * scale) - 6 * sourceDelta)
    (hregionMeasurable : MeasurableSet region)
    (hregionBox : ∀ point ∈ region, ∀ coordinate : Fin 3,
      |point coordinate - center coordinate| ≤ width) :
    WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw) where
  carrier index :=
    wz1IsotropicRescalingMap center scale ''
      (sourcePaperShading.carrier index ∩ region)
  measurable_carrier index := by
    let inverse : Point3 → Point3 :=
      wz1IsotropicRescalingInverse center scale
    have hscalePos : 0 < scale :=
      lt_of_lt_of_le zero_lt_one hscale
    have himage :
        wz1IsotropicRescalingMap center scale ''
            (sourcePaperShading.carrier index ∩ region) =
          inverse ⁻¹' (sourcePaperShading.carrier index ∩ region) := by
      ext point
      constructor
      · rintro ⟨source, hsource, rfl⟩
        have hinverse : inverse
            (wz1IsotropicRescalingMap center scale source) = source := by
          ext coordinate
          simp [inverse, wz1IsotropicRescalingMap,
            wz1IsotropicRescalingInverse]
          field_simp [hscalePos.ne']
          ring
        simpa [hinverse] using hsource
      · intro hsource
        refine ⟨inverse point, hsource, ?_⟩
        ext coordinate
        simp [inverse, wz1IsotropicRescalingMap,
          wz1IsotropicRescalingInverse]
        field_simp [hscalePos.ne']
    rw [himage]
    exact (sourcePaperShading.measurable_carrier index).inter
      hregionMeasurable |>.preimage
        (continuous_const.add
          (continuous_const.smul continuous_id)).measurable
  subset_body index point hpoint := by
    rcases hpoint with ⟨sourcePoint, hsourcePoint, rfl⟩
    exact proposition63MildRescalingFamily_image_mem_paperCarrier
      raw hscale hsourceDelta hscaleDeltaSmall width hwidth index
      sourcePoint
      (sourcePaperShading.subset_body index hsourcePoint.1)
      (hregionBox sourcePoint hsourcePoint.2)

/-- The retubed shading is exactly the isotropic image of the common spatial
restriction of the source shading. -/
theorem proposition63MildRescalingShading_union
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceRawShading center)
    (sourcePaperShading : WZ1PaperTubeShading sourceFamily)
    (region : Set Point3)
    (hsourceDelta : 0 < sourceDelta)
    (hscaleDeltaSmall : scale * sourceDelta < 1 / 54)
    (width : ℝ)
    (hwidth : width = 1 / (9 * scale) - 6 * sourceDelta)
    (hregionMeasurable : MeasurableSet region)
    (hregionBox : ∀ point ∈ region, ∀ coordinate : Fin 3,
      |point coordinate - center coordinate| ≤ width) :
    (proposition63MildRescalingShading hscale raw sourcePaperShading
      region hsourceDelta hscaleDeltaSmall width hwidth
      hregionMeasurable hregionBox).union =
      wz1IsotropicRescalingMap center scale ''
        (sourcePaperShading.union ∩ region) := by
  ext point
  constructor
  · rintro ⟨index, sourcePoint, hsourcePoint, rfl⟩
    exact ⟨sourcePoint, ⟨⟨index, hsourcePoint.1⟩, hsourcePoint.2⟩, rfl⟩
  · rintro ⟨sourcePoint, ⟨⟨index, hsourcePoint⟩, hsourceRegion⟩, rfl⟩
    exact ⟨index, sourcePoint, ⟨hsourcePoint, hsourceRegion⟩, rfl⟩

/-- The canonical one-per-source target shading has exactly the cubic
isotropic Jacobian times the mass of the source shading restricted to the
common popular region.  In particular, no `ceil scale` child multiplicity
appears. -/
theorem proposition63MildRescalingShading_mass
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceRawShading center)
    (sourcePaperShading : WZ1PaperTubeShading sourceFamily)
    (region : Set Point3)
    (hsourceDelta : 0 < sourceDelta)
    (hscaleDeltaSmall : scale * sourceDelta < 1 / 54)
    (width : ℝ)
    (hwidth : width = 1 / (9 * scale) - 6 * sourceDelta)
    (hregionMeasurable : MeasurableSet region)
    (hregionBox : ∀ point ∈ region, ∀ coordinate : Fin 3,
      |point coordinate - center coordinate| ≤ width) :
    (proposition63MildRescalingShading hscale raw sourcePaperShading
      region hsourceDelta hscaleDeltaSmall width hwidth
      hregionMeasurable hregionBox).mass =
      ENNReal.ofReal (scale ^ 3) *
        ∑ index : Fin sourceFamily.card,
          MeasureTheory.volume
            (sourcePaperShading.carrier index ∩ region) := by
  change (∑ index : Fin sourceFamily.card,
      MeasureTheory.volume (wz1IsotropicRescalingMap center scale ''
        (sourcePaperShading.carrier index ∩ region))) = _
  calc
    (∑ index : Fin sourceFamily.card,
        MeasureTheory.volume (wz1IsotropicRescalingMap center scale ''
          (sourcePaperShading.carrier index ∩ region))) =
        ∑ index : Fin sourceFamily.card,
          ENNReal.ofReal (scale ^ 3) *
            MeasureTheory.volume
              (sourcePaperShading.carrier index ∩ region) := by
      apply Finset.sum_congr rfl
      intro index _
      exact volume_image_wz1IsotropicRescalingMap
        (lt_of_lt_of_le zero_lt_one hscale) center
        ((sourcePaperShading.measurable_carrier index).inter
          hregionMeasurable)
    _ = ENNReal.ofReal (scale ^ 3) *
        ∑ index : Fin sourceFamily.card,
          MeasureTheory.volume
            (sourcePaperShading.carrier index ∩ region) := by
      rw [Finset.mul_sum]

/-- A per-source-tube density floor becomes a target density floor under the
exact isotropic Jacobian.  The target body costs only the quadratic paper-tube
volume factor, leaving one positive factor of `scale`. -/
theorem proposition63MildRescalingShading_dense
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceRawShading center)
    (sourcePaperShading : WZ1PaperTubeShading sourceFamily)
    (region : Set Point3)
    (hsourceDelta : 0 < sourceDelta)
    (hscaleDeltaSmall : scale * sourceDelta < 1 / 54)
    (width : ℝ)
    (hwidth : width = 1 / (9 * scale) - 6 * sourceDelta)
    (hregionMeasurable : MeasurableSet region)
    (hregionBox : ∀ point ∈ region, ∀ coordinate : Fin 3,
      |point coordinate - center coordinate| ≤ width)
    (hsourceRegion : ∀ index,
      sourcePaperShading.carrier index ⊆ region)
    (hrawLine : WZ1PaperIsLineClass raw.family)
    (density : ENNReal)
    (hsourcePerTube : ∀ index,
      density * Kakeya.realRpowENN sourceDelta 2 ≤
        MeasureTheory.volume (sourcePaperShading.carrier index)) :
    (proposition63MildRescalingShading hscale raw sourcePaperShading
      region hsourceDelta hscaleDeltaSmall width hwidth
      hregionMeasurable hregionBox).IsLambdaDense
        ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
          ENNReal.ofReal scale * density) := by
  let targetFamily := proposition63MildRescalingFamily hscale raw
  let targetShading := proposition63MildRescalingShading hscale raw
    sourcePaperShading region hsourceDelta hscaleDeltaSmall width hwidth
    hregionMeasurable hregionBox
  let geometryConstant : ENNReal :=
    55296 * Kakeya.deltaTubeVolume 1
  have htargetDeltaPos : 0 < scale * sourceDelta :=
    mul_pos (lt_of_lt_of_le zero_lt_one hscale) hsourceDelta
  have htargetDeltaSmall : scale * sourceDelta ≤ 1 / 24 :=
    hscaleDeltaSmall.le.trans (by norm_num)
  let fullTarget : WZ1PaperTubeShading targetFamily :=
    { carrier := fun index => wz1PaperTubeCarrier (targetFamily.tube index)
      measurable_carrier := fun index =>
        wz1PaperTubeCarrier_measurable (targetFamily.tube index)
      subset_body := fun _ => Set.Subset.rfl }
  have targetBodyUpper : (wz1PaperBodyFamily targetFamily).mass ≤
      geometryConstant * Kakeya.realRpowENN (scale * sourceDelta) 2 *
        targetFamily.enncard := by
    have upper := wz2_paper_shading_mass_upper htargetDeltaPos
      htargetDeltaSmall
      (proposition63MildRescalingFamily_lineClass hscale raw hrawLine)
      fullTarget
    change (wz1PaperBodyFamily targetFamily).mass ≤ _ at upper
    simpa only [geometryConstant] using upper
  have sourceMassLower : density *
      (Kakeya.realRpowENN sourceDelta 2 * sourceFamily.enncard) ≤
        sourcePaperShading.mass := by
    change density *
        (Kakeya.realRpowENN sourceDelta 2 * (sourceFamily.card : ENNReal)) ≤
      ∑ index : Fin sourceFamily.card,
        MeasureTheory.volume (sourcePaperShading.carrier index)
    calc
      density *
          (Kakeya.realRpowENN sourceDelta 2 *
            (sourceFamily.card : ENNReal)) =
          ∑ _index : Fin sourceFamily.card,
            density * Kakeya.realRpowENN sourceDelta 2 := by
        simp [Finset.sum_const]
        ring
      _ ≤ ∑ index : Fin sourceFamily.card,
          MeasureTheory.volume (sourcePaperShading.carrier index) :=
        Finset.sum_le_sum fun index _ => hsourcePerTube index
  have targetMass : targetShading.mass =
      ENNReal.ofReal (scale ^ 3) * sourcePaperShading.mass := by
    rw [show targetShading =
        proposition63MildRescalingShading hscale raw sourcePaperShading
          region hsourceDelta hscaleDeltaSmall width hwidth
          hregionMeasurable hregionBox by rfl,
      proposition63MildRescalingShading_mass]
    congr 1
    apply Finset.sum_congr rfl
    intro index _
    rw [Set.inter_eq_left.mpr (hsourceRegion index)]
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have targetPower : Kakeya.realRpowENN (scale * sourceDelta) 2 =
      ENNReal.ofReal (scale ^ 2) *
        Kakeya.realRpowENN sourceDelta 2 := by
    simp only [Kakeya.realRpowENN]
    have hmul : Real.rpow (scale * sourceDelta) 2 =
        Real.rpow scale 2 * Real.rpow sourceDelta 2 :=
      Real.mul_rpow hscalePos.le hsourceDelta.le
    have hscaleTwo : Real.rpow scale 2 = scale ^ 2 := by
      norm_num [Real.rpow_natCast]
    rw [hmul, hscaleTwo]
    exact ENNReal.ofReal_mul (sq_nonneg scale)
  have geometryPos : 0 < geometryConstant := by
    dsimp only [geometryConstant]
    apply ENNReal.mul_pos (by norm_num)
    have hvolume := tube_volume_scaling.2.1
      (1 : ℝ) (by norm_num) (by norm_num)
    exact hvolume.1.ne'
  have geometryTop : geometryConstant ≠ ⊤ := by
    dsimp only [geometryConstant]
    apply ENNReal.mul_ne_top (by norm_num)
    have hvolume := tube_volume_scaling.2.1
      (1 : ℝ) (by norm_num) (by norm_num)
    exact hvolume.2
  rw [Kakeya.Streamlined.Shading.IsLambdaDense]
  have targetBodyScaled :
      (geometryConstant⁻¹ * ENNReal.ofReal scale * density) *
          (wz1PaperBodyFamily targetFamily).mass ≤
        (geometryConstant⁻¹ * ENNReal.ofReal scale * density) *
          (geometryConstant *
            Kakeya.realRpowENN (scale * sourceDelta) 2 *
              targetFamily.enncard) :=
    mul_le_mul_left' targetBodyUpper _
  calc
    (geometryConstant⁻¹ * ENNReal.ofReal scale * density) *
          (wz1PaperBodyFamily targetFamily).mass ≤
        (geometryConstant⁻¹ * ENNReal.ofReal scale * density) *
          (geometryConstant *
            Kakeya.realRpowENN (scale * sourceDelta) 2 *
              targetFamily.enncard) := targetBodyScaled
    _ = ENNReal.ofReal (scale ^ 3) *
        (density * Kakeya.realRpowENN sourceDelta 2 *
          sourceFamily.enncard) := by
      rw [targetPower]
      rw [show targetFamily.enncard = sourceFamily.enncard by rfl]
      calc
        (geometryConstant⁻¹ * ENNReal.ofReal scale * density) *
              (geometryConstant *
                (ENNReal.ofReal (scale ^ 2) *
                  Kakeya.realRpowENN sourceDelta 2) *
                sourceFamily.enncard) =
            (geometryConstant⁻¹ * geometryConstant) *
              (ENNReal.ofReal scale * ENNReal.ofReal (scale ^ 2)) *
              (density * Kakeya.realRpowENN sourceDelta 2 *
                sourceFamily.enncard) := by ring
        _ = (ENNReal.ofReal scale * ENNReal.ofReal (scale ^ 2)) *
              (density * Kakeya.realRpowENN sourceDelta 2 *
                sourceFamily.enncard) := by
          rw [ENNReal.inv_mul_cancel geometryPos.ne' geometryTop, one_mul]
        _ = ENNReal.ofReal (scale ^ 3) *
              (density * Kakeya.realRpowENN sourceDelta 2 *
                sourceFamily.enncard) := by
          rw [← ENNReal.ofReal_mul hscalePos.le]
          congr 2
          ring
    _ ≤ ENNReal.ofReal (scale ^ 3) * sourcePaperShading.mass := by
      simpa only [mul_assoc] using
        mul_le_mul_left' sourceMassLower (ENNReal.ofReal (scale ^ 3))
    _ = targetShading.mass := targetMass.symm

/-- Whole source cells and a whole-cell common region remain whole target
cells under the grid-aligned isotropic similarity. -/
theorem proposition63MildRescalingShading_cubical
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hscale : 1 ≤ scale)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceRawShading center)
    (sourcePaperShading : WZ1PaperTubeShading sourceFamily)
    (region : Set Point3)
    (hsourceDelta : 0 < sourceDelta)
    (hscaleDeltaSmall : scale * sourceDelta < 1 / 54)
    (width : ℝ)
    (hwidth : width = 1 / (9 * scale) - 6 * sourceDelta)
    (hregionMeasurable : MeasurableSet region)
    (hregionBox : ∀ point ∈ region, ∀ coordinate : Fin 3,
      |point coordinate - center coordinate| ≤ width)
    (hcenterGrid : ∀ coordinate : Fin 3,
      ∃ cell : ℤ, center coordinate = (cell : ℝ) * sourceDelta)
    (hsourceCubical : WZ1PaperIsCubicalShading sourcePaperShading)
    (hregionCubical : ∀ point ∈ region,
      wz1PaperGridCube sourceDelta
        (wz1PaperGridIndex sourceDelta point) ⊆ region) :
    WZ1PaperIsCubicalShading
      (proposition63MildRescalingShading hscale raw sourcePaperShading
        region hsourceDelta hscaleDeltaSmall width hwidth
        hregionMeasurable hregionBox) := by
  intro index point hpoint
  change point ∈ wz1IsotropicRescalingMap center scale ''
    (sourcePaperShading.carrier index ∩ region) at hpoint
  exact proposition63_cubical_set_rescaling hsourceDelta
    (lt_of_lt_of_le zero_lt_one hscale) center hcenterGrid
    (sourcePaperShading.carrier index ∩ region)
    (proposition63_cubical_set_intersection
      (sourcePaperShading.carrier index) region
      (hsourceCubical index) hregionCubical) point hpoint

/-- If every source tube meets the shifted mild-rescaling core, then every
raw isotropic child lies in the paper line class.  The witness in the core
anchors the rescaled axis inside the fixed transverse window; no property of
the arbitrary raw source shading is used. -/
theorem proposition63_mild_rescaling_raw_line_class
    {sourceDelta scale : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hscale : 1 ≤ scale)
    (hscaleDeltaSmall : scale * sourceDelta < 1 / 54)
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourcePaperShading : WZ1PaperTubeShading sourceFamily)
    (sourceLine : WZ1PaperIsLineClass sourceFamily)
    (center : Point3)
    (source_meets_core : ∀ index,
      (sourcePaperShading.carrier index ∩
        pureWZ2ShiftedOriginGridCore sourceDelta scale center).Nonempty)
    {sourceRawShading : Kakeya.Streamlined.TubeShading sourceFamily}
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceRawShading center) :
    WZ1PaperIsLineClass raw.family := by
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  let width : ℝ := 1 / (9 * scale) - 6 * sourceDelta
  intro child
  let source := raw.sourceParent child
  have hdirection :
      (1 / 2 : ℝ) ≤ |(sourceFamily.tube source).direction (2 : Fin 3)| :=
    (sourceLine source).vertical
  rcases source_meets_core source with ⟨point, point_shading, point_core⟩
  have point_window : ∀ coordinate : Fin 3,
      |point coordinate - center coordinate| ≤ width := by
    have point_cell : point ∈ wz1PaperGridCube sourceDelta
        (wz1PaperGridIndex sourceDelta point) :=
      (mem_wz1PaperGridCube sourceDelta _ point).mpr rfl
    exact point_core point_cell
  have point_paper : point ∈
      wz1PaperTubeCarrier (sourceFamily.tube source) :=
    sourcePaperShading.subset_body source point_shading
  rcases exists_dist_le_of_mem_cthickening_closed
      (isClosed_tubeAxisLine (sourceFamily.tube source))
      (by positivity) point_paper.1 with
    ⟨axisPoint, axisPoint_mem, axisPoint_distance⟩
  have axisPoint_window : ∀ coordinate : Fin 3,
      |axisPoint coordinate - center coordinate| ≤
        width + 6 * sourceDelta := by
    intro coordinate
    have coordinate_distance :
        |axisPoint coordinate - point coordinate| ≤
          ‖axisPoint - point‖ :=
      proposition63_point3_coord_abs_le_norm
        (axisPoint - point) coordinate
    have distance_eq : ‖axisPoint - point‖ = dist point axisPoint := by
      rw [dist_comm, dist_eq_norm]
    rw [distance_eq] at coordinate_distance
    calc
      |axisPoint coordinate - center coordinate| ≤
          |point coordinate - center coordinate| +
            |axisPoint coordinate - point coordinate| := by
        rw [show axisPoint coordinate - center coordinate =
          (point coordinate - center coordinate) +
            (axisPoint coordinate - point coordinate) by ring]
        exact abs_add_le _ _
      _ ≤ width + 6 * sourceDelta :=
        add_le_add (point_window coordinate)
          (coordinate_distance.trans axisPoint_distance)
  have width_identity : width + 6 * sourceDelta = 1 / (9 * scale) := by
    dsimp only [width]
    ring
  let targetPoint := wz1IsotropicRescalingMap center scale axisPoint
  have targetPoint_axis : targetPoint ∈ tubeAxisLine (raw.family.tube child) := by
    rw [raw.axis_provenance child]
    exact ⟨axisPoint, axisPoint_mem, rfl⟩
  have targetPoint_bound : ∀ coordinate : Fin 3,
      |targetPoint coordinate| ≤ 1 / 9 := by
    intro coordinate
    have relative : |axisPoint coordinate - center coordinate| ≤
        1 / (9 * scale) := by
      rw [← width_identity]
      exact axisPoint_window coordinate
    have value : targetPoint coordinate =
        scale * (axisPoint coordinate - center coordinate) := by
      simp [targetPoint, wz1IsotropicRescalingMap]
    rw [value, abs_mul, abs_of_pos hscalePos]
    calc
      scale * |axisPoint coordinate - center coordinate| ≤
          scale * (1 / (9 * scale)) := by gcongr
      _ = 1 / 9 := by field_simp [hscalePos.ne']
  have zero_bound : ∀ coordinate : Fin 3,
      |wz1TubeAxisZeroPoint (raw.family.tube child) coordinate| ≤ 1 / 3 := by
    have target_vertical :
        (1 / 2 : ℝ) ≤ |(raw.family.tube child).direction (2 : Fin 3)| := by
      rw [raw.direction_provenance child]
      exact hdirection
    have bound := zero_point_bound_from_axis_point target_vertical targetPoint
      targetPoint_axis (1 / 9) (by norm_num) targetPoint_bound
    intro coordinate
    convert bound coordinate using 1 <;> norm_num
  have direction_two :
      (1 / 2 : ℝ) ≤ wz1PaperDirection (raw.family.tube child) (2 : Fin 3) := by
    have absolute :
        (1 / 2 : ℝ) ≤ |(raw.family.tube child).direction (2 : Fin 3)| := by
      rw [raw.direction_provenance child]
      exact hdirection
    by_cases nonnegative : 0 ≤ (raw.family.tube child).direction (2 : Fin 3)
    · simpa [wz1PaperDirection, nonnegative, abs_of_nonneg nonnegative]
        using absolute
    · have negative : (raw.family.tube child).direction (2 : Fin 3) < 0 :=
        lt_of_not_ge nonnegative
      simpa [wz1PaperDirection, nonnegative, abs_of_neg negative]
        using absolute
  exact ⟨direction_two, zero_bound 0, zero_bound 1⟩

/-- The ordinary shading fed to raw isotropic rediscretization.  Its carrier
is only an auxiliary coverage witness; the final paper shading is built from
the selected paper carrier itself. -/
def proposition63MildRescalingRawSourceShading
    {sourceDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (hsourceDelta : 0 < sourceDelta)
    (sourcePaperShading : WZ1PaperTubeShading sourceFamily) :
    Kakeya.Streamlined.TubeShading sourceFamily where
  carrier index := sourcePaperShading.carrier index ∩
    (sourceFamily.tube index).carrier
  measurable_carrier index :=
    (sourcePaperShading.measurable_carrier index).inter
      (wz2_paper_ordinary_tube_carrier_measurable
        (sourceFamily.tube index) hsourceDelta)
  subset_body index point hpoint := hpoint.2

/-- Construct the raw isotropic rediscretization used by the final
one-line-per-source retubing.  This wrapper keeps the genuine multi-child
rediscretization visible at the M9 assembly boundary. -/
theorem proposition63_mild_rescaling_raw
    {sourceDelta scale : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hscale : 1 ≤ scale)
    (hscaleDeltaOne : scale * sourceDelta ≤ 1)
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (hsourceNonempty : sourceFamily.Nonempty)
    (sourcePaperShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) :
    Nonempty (WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily
        (proposition63MildRescalingRawSourceShading
          hsourceDelta sourcePaperShading) center) := by
  exact wz1_isotropic_tube_rediscretization sourceDelta scale
    hsourceDelta hscale hscaleDeltaOne sourceFamily hsourceNonempty
    (proposition63MildRescalingRawSourceShading
      hsourceDelta sourcePaperShading) center

end Kakeya.Assouad.PureWZ2

end
