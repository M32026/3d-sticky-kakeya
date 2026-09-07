import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12LocalizedDoubledFiber
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDoubledParentCarrierCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DiagonalTubeCloseness

/-!
# Canonically centered ordinary tubes and paper line distance

The cropped paper carrier depends only on the supporting line, but the public
Definition 2.12 carrier also depends on the chosen unit segment.  The
canonical representative below uses the positively oriented paper direction
and centers that segment at the axis point of height zero.  On this model,
small paper line distance gives literal centered-doubled containment.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Same supporting line and radius, with positive paper orientation and the
ordinary midpoint equal to the height-zero axis point. -/
def pureWZ2PaperCenteredTube
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    Kakeya.DeltaTube delta where
  base := wz1TubeAxisZeroPoint tube -
    (1 / 2 : ℝ) • wz1PaperDirection tube
  direction := wz1PaperDirection tube
  direction_unit := wz1PaperDirection_norm tube

@[simp] theorem pureWZ2PaperCenteredTube_direction
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    (pureWZ2PaperCenteredTube tube).direction =
      wz1PaperDirection tube := rfl

@[simp] theorem pureWZ2PaperCenteredTube_midpoint
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    wz2PaperTubeMidpoint (pureWZ2PaperCenteredTube tube) =
      wz1TubeAxisZeroPoint tube := by
  simp only [wz2PaperTubeMidpoint, pureWZ2PaperCenteredTube]
  module

theorem pureWZ2PaperCenteredTube_axis
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    tubeAxisLine (pureWZ2PaperCenteredTube tube) = tubeAxisLine tube := by
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

/-- A small ordinary tube whose midpoint is the height-zero point of a paper
line-class axis already lies inside the fixed paper crop. -/
theorem pureWZ2_centered_lineClass_carrier_subset_paper
    {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 24)
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube)
    (hmidpoint : wz2PaperTubeMidpoint tube 2 = 0) :
    tube.carrier ⊆ wz1PaperTubeCarrier tube := by
  intro point hpoint
  have hsegmentCompact :
      IsCompact (Kakeya.unitSegment tube.base tube.direction) := by
    exact isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  have haxis : ∃ axisPoint : Point3,
      axisPoint ∈ Kakeya.unitSegment tube.base tube.direction ∧
        dist point axisPoint ≤ delta := by
    rw [show tube.carrier = Metric.cthickening delta
        (Kakeya.unitSegment tube.base tube.direction) by
      rfl, hsegmentCompact.cthickening_eq_biUnion_closedBall hdelta.le]
      at hpoint
    simpa [Set.mem_iUnion, Metric.mem_closedBall] using hpoint
  rcases haxis with ⟨axisPoint, ⟨parameter, hparameter, rfl⟩, herror⟩
  let error : Point3 := point - (tube.base + parameter • tube.direction)
  have herrorNorm : ‖error‖ ≤ delta := by
    simpa [error, dist_eq_norm] using herror
  have hpointEq :
      point = tube.base + parameter • tube.direction + error := by
    simp [error]
  have hparameterHalf : |parameter - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hparameter.1, hparameter.2]
  have hdifference :
      tube.base + parameter • tube.direction + error -
          wz2PaperTubeMidpoint tube =
        (parameter - 1 / 2 : ℝ) • tube.direction + error := by
    simp only [wz2PaperTubeMidpoint]
    module
  have hdistance :
      ‖tube.base + parameter • tube.direction + error -
          wz2PaperTubeMidpoint tube‖ ≤ delta + 1 / 2 := by
    rw [hdifference]
    calc
      ‖(parameter - 1 / 2 : ℝ) • tube.direction + error‖ ≤
          ‖(parameter - 1 / 2 : ℝ) • tube.direction‖ + ‖error‖ :=
        norm_add_le _ _
      _ = |parameter - 1 / 2| + ‖error‖ := by
        rw [norm_smul, Real.norm_eq_abs, tube.direction_unit, mul_one]
      _ ≤ 1 / 2 + delta := add_le_add hparameterHalf herrorNorm
      _ = delta + 1 / 2 := by ring
  have hdistancePoint :
      ‖point - wz2PaperTubeMidpoint tube‖ ≤ delta + 1 / 2 := by
    rw [hpointEq]
    exact hdistance
  have hzero :
      wz1TubeAxisZeroPoint tube = wz2PaperTubeMidpoint tube := by
    apply wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
      hline.vertical
    · exact ⟨1 / 2, rfl⟩
    · exact hmidpoint
  have hcoord : ∀ coordinate : Fin 3,
      |point coordinate - wz2PaperTubeMidpoint tube coordinate| ≤
        delta + 1 / 2 := by
    intro coordinate
    have happly := PiLp.norm_apply_le
      (point - wz2PaperTubeMidpoint tube) coordinate
    simpa [Real.norm_eq_abs] using happly.trans hdistancePoint
  have hmidpointZero : |wz2PaperTubeMidpoint tube 0| ≤ 1 / 3 := by
    rw [← hzero]
    exact hline.2.1
  have hmidpointOne : |wz2PaperTubeMidpoint tube 1| ≤ 1 / 3 := by
    rw [← hzero]
    exact hline.2.2
  have hpointZero : |point 0| ≤ 1 := by
    calc
      |point 0| = |(point 0 - wz2PaperTubeMidpoint tube 0) +
          wz2PaperTubeMidpoint tube 0| := by ring_nf
      _ ≤ |point 0 - wz2PaperTubeMidpoint tube 0| +
          |wz2PaperTubeMidpoint tube 0| := abs_add_le _ _
      _ ≤ (delta + 1 / 2) + 1 / 3 :=
        add_le_add (hcoord 0) hmidpointZero
      _ ≤ 1 := by linarith
  have hpointOne : |point 1| ≤ 1 := by
    calc
      |point 1| = |(point 1 - wz2PaperTubeMidpoint tube 1) +
          wz2PaperTubeMidpoint tube 1| := by ring_nf
      _ ≤ |point 1 - wz2PaperTubeMidpoint tube 1| +
          |wz2PaperTubeMidpoint tube 1| := abs_add_le _ _
      _ ≤ (delta + 1 / 2) + 1 / 3 :=
        add_le_add (hcoord 1) hmidpointOne
      _ ≤ 1 := by linarith
  have hpointTwo : |point 2| ≤ 1 := by
    calc
      |point 2| = |point 2 - wz2PaperTubeMidpoint tube 2| := by
        rw [hmidpoint, sub_zero]
      _ ≤ delta + 1 / 2 := hcoord 2
      _ ≤ 1 := by linarith
  constructor
  · exact Metric.cthickening_mono
      (by linarith : delta ≤ 6 * delta) (tubeAxisLine tube)
      (Metric.cthickening_subset_of_subset delta (by
        rintro axisPoint ⟨axisParameter, _haxisParameter, rfl⟩
        exact ⟨axisParameter, rfl⟩) hpoint)
  · rw [hpointEq]
    simpa [Kakeya.Streamlined.axisBox] using
      (show
        |(tube.base + parameter • tube.direction + error) 0| ≤ 1 ∧
        |(tube.base + parameter • tube.direction + error) 1| ≤ 1 ∧
        |(tube.base + parameter • tube.direction + error) 2| ≤ 1 from
        ⟨by simpa [hpointEq] using hpointZero,
          by simpa [hpointEq] using hpointOne,
          by simpa [hpointEq] using hpointTwo⟩)

theorem pureWZ2PaperCenteredTube_paperCarrier
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    wz1PaperTubeCarrier (pureWZ2PaperCenteredTube tube) =
      wz1PaperTubeCarrier tube := by
  unfold wz1PaperTubeCarrier
  rw [pureWZ2PaperCenteredTube_axis]

@[simp] theorem pureWZ2PaperCenteredTube_zeroPoint
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube) :
    wz1TubeAxisZeroPoint (pureWZ2PaperCenteredTube tube) =
      wz1TubeAxisZeroPoint tube := by
  have hvertical : wz1PaperDirection tube 2 ≠ 0 := by
    linarith [hline.1]
  have hzeroTwo : wz1TubeAxisZeroPoint tube 2 = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube hline.vertical
  unfold wz1TubeAxisZeroPoint
  change
    (wz1TubeAxisZeroPoint tube -
        (1 / 2 : ℝ) • wz1PaperDirection tube) -
      (((wz1TubeAxisZeroPoint tube -
          (1 / 2 : ℝ) • wz1PaperDirection tube) 2) /
        wz1PaperDirection tube 2) • wz1PaperDirection tube =
      wz1TubeAxisZeroPoint tube
  have hquotient :
      ((wz1TubeAxisZeroPoint tube -
          (1 / 2 : ℝ) • wz1PaperDirection tube) 2) /
          wz1PaperDirection tube 2 = -(1 / 2 : ℝ) := by
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hzeroTwo]
    field_simp [hvertical]
    ring
  rw [hquotient]
  module

@[simp] theorem pureWZ2PaperCenteredTube_paperDirection
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube) :
    wz1PaperDirection (pureWZ2PaperCenteredTube tube) =
      wz1PaperDirection tube := by
  have hpositive : 0 ≤ wz1PaperDirection tube 2 := by
    linarith [hline.1]
  change (if 0 ≤ wz1PaperDirection tube 2 then
      wz1PaperDirection tube else -wz1PaperDirection tube) =
    wz1PaperDirection tube
  rw [if_pos hpositive]

theorem pureWZ2PaperCenteredTube_lineDistance
    {firstScale secondScale : ℝ}
    (first : Kakeya.DeltaTube firstScale)
    (second : Kakeya.DeltaTube secondScale)
    (hfirst : WZ1PaperTubeInLineClass first)
    (hsecond : WZ1PaperTubeInLineClass second) :
    wz1PaperLineDistance
        (pureWZ2PaperCenteredTube first)
        (pureWZ2PaperCenteredTube second) =
      wz1PaperLineDistance first second := by
  simp [wz1PaperLineDistance, hfirst, hsecond]

private theorem pureWZ2_radiusTwoCenteredCarrier_subset_doubled
    {delta : ℝ} (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta) :
    (wz2PaperRelabelTube (targetScale := 2 * delta) tube).carrier ⊆
      wz2PaperCenteredDilatedCarrier 2 tube := by
  intro point hpoint
  change point ∈ Metric.cthickening (2 * delta)
      (Kakeya.unitSegment tube.base tube.direction) at hpoint
  have haxisClosed : IsClosed
      (Kakeya.unitSegment tube.base tube.direction) :=
    (isCompact_Icc.image (by fun_prop)).isClosed
  rcases exists_dist_le_of_mem_cthickening_closed haxisClosed
      (by positivity : 0 ≤ 2 * delta) hpoint with
    ⟨axisPoint, haxisPoint, hpointDist⟩
  let center := wz2PaperTubeMidpoint tube
  let source : Point3 := center + (1 / 2 : ℝ) • (point - center)
  let sourceAxis : Point3 :=
    center + (1 / 2 : ℝ) • (axisPoint - center)
  have hcenterAxis : center ∈
      Kakeya.unitSegment tube.base tube.direction :=
    ⟨1 / 2, by norm_num, rfl⟩
  have hsourceAxis : sourceAxis ∈
      Kakeya.unitSegment tube.base tube.direction := by
    rcases haxisPoint with ⟨parameter, hparameter, rfl⟩
    refine ⟨(1 / 4 + parameter / 2), ?_, ?_⟩
    · rcases hparameter with ⟨hparameter0, hparameter1⟩
      constructor <;> linarith
    · dsimp only [sourceAxis, center, wz2PaperTubeMidpoint]
      module
  have hsourceCarrier : source ∈ tube.carrier := by
    have hdist : dist source sourceAxis ≤ delta := by
      rw [dist_eq_norm]
      have hvector : source - sourceAxis =
          (1 / 2 : ℝ) • (point - axisPoint) := by
        dsimp only [source, sourceAxis]
        module
      rw [hvector, norm_smul, Real.norm_eq_abs]
      norm_num
      have hraw : ‖point - axisPoint‖ ≤ 2 * delta := by
        simpa [dist_eq_norm] using hpointDist
      linarith
    exact Metric.mem_cthickening_of_dist_le source sourceAxis delta _
      hsourceAxis hdist
  refine ⟨source, hsourceCarrier, ?_⟩
  change (2 : ℝ) • (source - center) + center = point
  dsimp only [source]
  module

/-- On canonically centered same-scale representatives, paper line distance
at most the tube radius forces literal centered-doubled containment. -/
theorem pureWZ2_centered_carrier_subset_doubled_of_lineDistance_le
    {delta : ℝ} (hdelta : 0 < delta)
    (first second : Kakeya.DeltaTube delta)
    (hdistance : wz1PaperLineDistance first second ≤ (2 / 3 : ℝ) * delta) :
    (pureWZ2PaperCenteredTube first).carrier ⊆
      wz2PaperCenteredDilatedCarrier 2
        (pureWZ2PaperCenteredTube second) := by
  let firstCentered := pureWZ2PaperCenteredTube first
  let secondCentered := pureWZ2PaperCenteredTube second
  let enlarged : Kakeya.DeltaTube (2 * delta) :=
    wz2PaperRelabelTube (targetScale := 2 * delta) secondCentered
  have hzero : dist (wz1TubeAxisZeroPoint first)
      (wz1TubeAxisZeroPoint second) +
      InnerProductGeometry.angle
        (wz1PaperDirection first) (wz1PaperDirection second) ≤
          (2 / 3 : ℝ) * delta :=
    hdistance
  have hcontain : firstCentered.carrier ⊆ enlarged.carrier := by
    have hdirection :
        ‖firstCentered.direction - secondCentered.direction‖ ≤
          InnerProductGeometry.angle
            (wz1PaperDirection first) (wz1PaperDirection second) := by
      exact unit_norm_sub_le_angle
        (wz1PaperDirection_norm first) (wz1PaperDirection_norm second)
    apply tube_containment_from_closeness hdelta.le (by positivity)
    have hbaseVector : firstCentered.base - secondCentered.base =
        (wz1TubeAxisZeroPoint first - wz1TubeAxisZeroPoint second) -
          (1 / 2 : ℝ) •
            (wz1PaperDirection first - wz1PaperDirection second) := by
      change
        (wz1TubeAxisZeroPoint first -
            (1 / 2 : ℝ) • wz1PaperDirection first) -
          (wz1TubeAxisZeroPoint second -
            (1 / 2 : ℝ) • wz1PaperDirection second) = _
      module
    have hbase : ‖firstCentered.base - secondCentered.base‖ ≤
        dist (wz1TubeAxisZeroPoint first)
            (wz1TubeAxisZeroPoint second) +
          (1 / 2 : ℝ) *
            ‖wz1PaperDirection first - wz1PaperDirection second‖ := by
      rw [hbaseVector]
      calc
        ‖(wz1TubeAxisZeroPoint first - wz1TubeAxisZeroPoint second) -
              (1 / 2 : ℝ) •
                (wz1PaperDirection first - wz1PaperDirection second)‖
            ≤ ‖wz1TubeAxisZeroPoint first - wz1TubeAxisZeroPoint second‖ +
                ‖(1 / 2 : ℝ) •
                  (wz1PaperDirection first - wz1PaperDirection second)‖ :=
              norm_sub_le _ _
        _ = _ := by
          rw [norm_smul, Real.norm_eq_abs, dist_eq_norm]
          norm_num
    change ‖firstCentered.base - secondCentered.base‖ +
        ‖firstCentered.direction - secondCentered.direction‖ + delta ≤
          2 * delta
    have htotal :
        ‖firstCentered.base - secondCentered.base‖ +
            ‖firstCentered.direction - secondCentered.direction‖ ≤
          dist (wz1TubeAxisZeroPoint first)
              (wz1TubeAxisZeroPoint second) +
            (3 / 2 : ℝ) *
              InnerProductGeometry.angle
                (wz1PaperDirection first) (wz1PaperDirection second) := by
      calc
        ‖firstCentered.base - secondCentered.base‖ +
              ‖firstCentered.direction - secondCentered.direction‖
            ≤ (dist (wz1TubeAxisZeroPoint first)
                  (wz1TubeAxisZeroPoint second) +
                (1 / 2 : ℝ) *
                  ‖wz1PaperDirection first - wz1PaperDirection second‖) +
              InnerProductGeometry.angle
                (wz1PaperDirection first) (wz1PaperDirection second) :=
              add_le_add hbase hdirection
        _ ≤ dist (wz1TubeAxisZeroPoint first)
                (wz1TubeAxisZeroPoint second) +
              (3 / 2 : ℝ) *
                InnerProductGeometry.angle
                  (wz1PaperDirection first) (wz1PaperDirection second) := by
            have hchord := unit_norm_sub_le_angle
              (wz1PaperDirection_norm first)
              (wz1PaperDirection_norm second)
            linarith
    calc
      ‖firstCentered.base - secondCentered.base‖ +
            ‖firstCentered.direction - secondCentered.direction‖ + delta
          ≤ (dist (wz1TubeAxisZeroPoint first)
                (wz1TubeAxisZeroPoint second) +
              (3 / 2 : ℝ) *
                InnerProductGeometry.angle
                  (wz1PaperDirection first) (wz1PaperDirection second)) +
              delta := by
            linarith
      _ ≤ 2 * delta := by
        have hangle := InnerProductGeometry.angle_nonneg
          (wz1PaperDirection first) (wz1PaperDirection second)
        have hangleLe :
            InnerProductGeometry.angle
                (wz1PaperDirection first) (wz1PaperDirection second) ≤
              (2 / 3 : ℝ) * delta := by
          have hdist : 0 ≤ dist (wz1TubeAxisZeroPoint first)
              (wz1TubeAxisZeroPoint second) := dist_nonneg
          linarith
        linarith
  exact hcontain.trans
    (pureWZ2_radiusTwoCenteredCarrier_subset_doubled
      hdelta secondCentered)

/-- Same axes as the input family, canonically centered and assigned the
packing radius `2 delta / 3`. -/
def pureWZ2CenteredPackingFamily
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta) :
    Kakeya.Streamlined.TubeFamily ((2 / 3 : ℝ) * delta) where
  card := family.card
  tube index :=
    wz2PaperRelabelTube (targetScale := (2 / 3 : ℝ) * delta)
      (pureWZ2PaperCenteredTube (family.tube index))

/-- Public centered distinctness of the canonical radius-`delta`
representatives implies paper line-distance distinctness for the same axes at
the exact packing radius `2 delta / 3`. -/
theorem pureWZ2_centered_ordinaryDistinct_packingFamily_paperDistinct
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta)
    (hline : WZ1PaperIsLineClass family)
    (hdistinct : WZ2PaperOrdinaryIsEssentiallyDistinct
      { card := family.card
        tube := fun index => pureWZ2PaperCenteredTube (family.tube index) }) :
    WZ1PaperIsEssentiallyDistinct
      (pureWZ2CenteredPackingFamily family) := by
  unfold WZ1PaperIsEssentiallyDistinct
  change ∀ first second : Fin family.card, first ≠ second → _
  intro first second hne
  by_contra hnot
  have hlineDistanceEq : wz1PaperLineDistance
      ((pureWZ2CenteredPackingFamily family).tube first)
      ((pureWZ2CenteredPackingFamily family).tube second) =
        wz1PaperLineDistance (family.tube first) (family.tube second) := by
    change wz1PaperLineDistance
        (wz2PaperRelabelTube
          (pureWZ2PaperCenteredTube (family.tube first)))
        (wz2PaperRelabelTube
          (pureWZ2PaperCenteredTube (family.tube second))) = _
    rw [wz2PaperRelabelTube_lineDistance_both]
    exact pureWZ2PaperCenteredTube_lineDistance _ _
      (hline first) (hline second)
  have hle : wz1PaperLineDistance
      (family.tube first) (family.tube second) ≤
        (2 / 3 : ℝ) * delta := by
    rw [← hlineDistanceEq]
    exact le_of_not_gt hnot
  have hcontain :=
    pureWZ2_centered_carrier_subset_doubled_of_lineDistance_le
      hdelta (family.tube first) (family.tube second) hle
  exact (hdistinct first second hne).1 hcontain

/-! ## Height-zero based canonical representative -/

/-- The paper-metric canonical ordinary tube: its unit segment starts at the
height-zero axis point and follows the positively oriented paper direction. -/
def pureWZ2PaperZeroBasedTube
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    Kakeya.DeltaTube delta where
  base := wz1TubeAxisZeroPoint tube
  direction := wz1PaperDirection tube
  direction_unit := wz1PaperDirection_norm tube

@[simp] theorem pureWZ2PaperZeroBasedTube_midpoint
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    wz2PaperTubeMidpoint (pureWZ2PaperZeroBasedTube tube) =
      wz1TubeAxisZeroPoint tube +
        (1 / 2 : ℝ) • wz1PaperDirection tube := rfl

theorem pureWZ2PaperZeroBasedTube_axis
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    tubeAxisLine (pureWZ2PaperZeroBasedTube tube) = tubeAxisLine tube := by
  ext point
  simp only [tubeAxisLine, Set.mem_setOf_eq, pureWZ2PaperZeroBasedTube]
  constructor
  · rintro ⟨parameter, rfl⟩
    rcases wz1TubeAxisZeroPoint_mem_axis tube with
      ⟨zeroParameter, hzeroParameter⟩
    unfold wz1PaperDirection
    split_ifs
    · exact ⟨zeroParameter + parameter, by rw [hzeroParameter]; module⟩
    · exact ⟨zeroParameter - parameter, by rw [hzeroParameter]; module⟩
  · rintro ⟨parameter, rfl⟩
    rcases wz1TubeAxisZeroPoint_mem_axis tube with
      ⟨zeroParameter, hzeroParameter⟩
    unfold wz1PaperDirection
    split_ifs
    · exact ⟨parameter - zeroParameter, by rw [hzeroParameter]; module⟩
    · exact ⟨zeroParameter - parameter, by rw [hzeroParameter]; module⟩

theorem pureWZ2PaperZeroBasedTube_paperCarrier
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    wz1PaperTubeCarrier (pureWZ2PaperZeroBasedTube tube) =
      wz1PaperTubeCarrier tube := by
  unfold wz1PaperTubeCarrier
  rw [pureWZ2PaperZeroBasedTube_axis]

@[simp] theorem pureWZ2PaperZeroBasedTube_zeroPoint
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube) :
    wz1TubeAxisZeroPoint (pureWZ2PaperZeroBasedTube tube) =
      wz1TubeAxisZeroPoint tube := by
  have hvertical : wz1PaperDirection tube 2 ≠ 0 := by
    linarith [hline.1]
  have hzeroTwo : wz1TubeAxisZeroPoint tube 2 = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube hline.vertical
  change wz1TubeAxisZeroPoint tube -
      ((wz1TubeAxisZeroPoint tube) 2 / wz1PaperDirection tube 2) •
        wz1PaperDirection tube = wz1TubeAxisZeroPoint tube
  rw [hzeroTwo, zero_div, zero_smul, sub_zero]

@[simp] theorem pureWZ2PaperZeroBasedTube_paperDirection
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube) :
    wz1PaperDirection (pureWZ2PaperZeroBasedTube tube) =
      wz1PaperDirection tube := by
  have hpositive : 0 ≤ wz1PaperDirection tube 2 := by
    linarith [hline.1]
  change (if 0 ≤ wz1PaperDirection tube 2 then
      wz1PaperDirection tube else -wz1PaperDirection tube) =
    wz1PaperDirection tube
  rw [if_pos hpositive]

/-- Positive orientation is idempotent even before imposing the horizontal
line-class window. -/
@[simp] theorem pureWZ2PaperZeroBasedTube_paperDirection_eq
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    wz1PaperDirection (pureWZ2PaperZeroBasedTube tube) =
      wz1PaperDirection tube := by
  change (if 0 ≤ wz1PaperDirection tube 2 then
      wz1PaperDirection tube else -wz1PaperDirection tube) =
    wz1PaperDirection tube
  rw [if_pos]
  unfold wz1PaperDirection
  split_ifs with hdirection
  · exact hdirection
  · have hnegative : tube.direction 2 < 0 := lt_of_not_ge hdirection
    simpa using hnegative.le

theorem pureWZ2PaperZeroBasedTube_lineDistance
    {firstScale secondScale : ℝ}
    (first : Kakeya.DeltaTube firstScale)
    (second : Kakeya.DeltaTube secondScale)
    (hfirst : WZ1PaperTubeInLineClass first)
    (hsecond : WZ1PaperTubeInLineClass second) :
    wz1PaperLineDistance
        (pureWZ2PaperZeroBasedTube first)
        (pureWZ2PaperZeroBasedTube second) =
      wz1PaperLineDistance first second := by
  simp [wz1PaperLineDistance, hfirst, hsecond]

theorem pureWZ2PaperZeroBasedTube_lineClass
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass tube) :
    WZ1PaperTubeInLineClass (pureWZ2PaperZeroBasedTube tube) := by
  have hzero := pureWZ2PaperZeroBasedTube_zeroPoint tube hline
  have hdirection := pureWZ2PaperZeroBasedTube_paperDirection tube hline
  exact ⟨by rw [hdirection]; exact hline.1,
    by rw [hzero]; exact hline.2.1,
    by rw [hzero]; exact hline.2.2⟩

/-- In the zero-based model no half-chord base loss appears, so distance at
most `delta` already gives centered-doubled containment. -/
theorem pureWZ2_zeroBased_carrier_subset_doubled_of_lineDistance_le
    {delta : ℝ} (hdelta : 0 < delta)
    (first second : Kakeya.DeltaTube delta)
    (hfirst : WZ1PaperTubeInLineClass first)
    (hsecond : WZ1PaperTubeInLineClass second)
    (hdistance : wz1PaperLineDistance first second ≤ delta) :
    (pureWZ2PaperZeroBasedTube first).carrier ⊆
      wz2PaperCenteredDilatedCarrier 2
        (pureWZ2PaperZeroBasedTube second) := by
  let firstZero := pureWZ2PaperZeroBasedTube first
  let secondZero := pureWZ2PaperZeroBasedTube second
  let enlarged : Kakeya.DeltaTube (2 * delta) :=
    wz2PaperRelabelTube (targetScale := 2 * delta) secondZero
  have hcontain : firstZero.carrier ⊆ enlarged.carrier := by
    apply tube_containment_from_closeness hdelta.le (by positivity)
    change
      ‖wz1TubeAxisZeroPoint first - wz1TubeAxisZeroPoint second‖ +
          ‖wz1PaperDirection first - wz1PaperDirection second‖ + delta ≤
        2 * delta
    have hchord := unit_norm_sub_le_angle
      (wz1PaperDirection_norm first) (wz1PaperDirection_norm second)
    have hmetric :
        ‖wz1TubeAxisZeroPoint first - wz1TubeAxisZeroPoint second‖ +
            InnerProductGeometry.angle
              (wz1PaperDirection first) (wz1PaperDirection second) ≤ delta := by
      simpa [wz1PaperLineDistance, dist_eq_norm] using hdistance
    linarith
  exact hcontain.trans
    (pureWZ2_radiusTwoCenteredCarrier_subset_doubled hdelta secondZero)

def pureWZ2PaperZeroBasedFamily
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta) :
    Kakeya.Streamlined.TubeFamily delta where
  card := family.card
  tube index := pureWZ2PaperZeroBasedTube (family.tube index)

@[simp] theorem pureWZ2PaperZeroBasedTube_idempotent
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass
      (pureWZ2PaperZeroBasedTube tube)) :
    pureWZ2PaperZeroBasedTube (pureWZ2PaperZeroBasedTube tube) =
      pureWZ2PaperZeroBasedTube tube := by
  change
    Kakeya.DeltaTube.mk
        (wz1TubeAxisZeroPoint (pureWZ2PaperZeroBasedTube tube))
        (wz1PaperDirection (pureWZ2PaperZeroBasedTube tube)) _ =
      Kakeya.DeltaTube.mk
        (wz1TubeAxisZeroPoint tube)
        (wz1PaperDirection tube) _
  have hdirection :
      wz1PaperDirection (pureWZ2PaperZeroBasedTube tube) =
        wz1PaperDirection tube :=
    pureWZ2PaperZeroBasedTube_paperDirection_eq tube
  have hpaperVertical :
      (1 / 2 : ℝ) ≤ wz1PaperDirection tube 2 := by
    rw [← hdirection]
    exact hline.1
  have hvertical :
      (1 / 2 : ℝ) ≤ |tube.direction 2| := by
    unfold wz1PaperDirection at hpaperVertical
    split_ifs at hpaperVertical with hdirection
    · simpa [abs_of_nonneg hdirection] using hpaperVertical
    · have hnegative : tube.direction 2 < 0 := lt_of_not_ge hdirection
      simpa [abs_of_neg hnegative] using hpaperVertical
  have hzeroTwo : wz1TubeAxisZeroPoint tube 2 = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube hvertical
  have hzero :
      wz1TubeAxisZeroPoint (pureWZ2PaperZeroBasedTube tube) =
        wz1TubeAxisZeroPoint tube := by
    change wz1TubeAxisZeroPoint tube -
        ((wz1TubeAxisZeroPoint tube) 2 / wz1PaperDirection tube 2) •
          wz1PaperDirection tube = wz1TubeAxisZeroPoint tube
    rw [hzeroTwo, zero_div, zero_smul, sub_zero]
  rw [Kakeya.DeltaTube.mk.injEq]
  exact ⟨hzero, hdirection⟩

/-- Centered ordinary distinctness of the zero-based model implies the exact
paper line-distance distinctness needed by packing. -/
theorem pureWZ2_zeroBased_ordinaryDistinct_implies_paperDistinct
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta)
    (hline : WZ1PaperIsLineClass family)
    (hdistinct : WZ2PaperOrdinaryIsEssentiallyDistinct
      (pureWZ2PaperZeroBasedFamily family)) :
    WZ1PaperIsEssentiallyDistinct family := by
  intro first second hne
  by_contra hnot
  have hle : wz1PaperLineDistance
      (family.tube first) (family.tube second) ≤ delta := le_of_not_gt hnot
  have hcontain := pureWZ2_zeroBased_carrier_subset_doubled_of_lineDistance_le
    hdelta (family.tube first) (family.tube second)
      (hline first) (hline second) hle
  exact (hdistinct first second hne).1 hcontain

end Kakeya.Assouad

end
