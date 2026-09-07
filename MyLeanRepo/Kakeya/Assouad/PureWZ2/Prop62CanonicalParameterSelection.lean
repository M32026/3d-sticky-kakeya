import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62BoundedPureScheduleProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CompressedPureSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CanonicalMetricPreliminary

/-!
# Proposition 6.2: canonical packet and mesh parameters

The metric-parent construction does not use arbitrary mesh parameters.  Once
the old schedule has been compressed around the last retained upper level and
the paper packet level, use

* mesh width `rho / 100`;
* residue stride base `40000`;
* midpoint bound `5`.

The sole remaining scalar producer obligation is recorded by
`PureWZ2Prop62CompressionCertificate`: it identifies the two old coordinates,
proves the paper packet scale is at most `rho / 1000`, and supplies the finite
rounding route after deleting the old levels strictly between them.
-/

noncomputable section

namespace Kakeya.Assouad

def pureWZ2Prop62MetricMeshWidth (rho : ℝ) : ℝ :=
  rho / 100

def pureWZ2Prop62ResidueStrideBase : ℕ :=
  40000

def pureWZ2Prop62CompressedScaleWindow
    (scaleWindow : ENNReal) : ENNReal :=
  1000 * scaleWindow ^ 3

theorem pureWZ2Prop62CompressedScaleWindow_finite
    {scaleWindow : ENNReal}
    (finite : WZ2PaperFiniteErrorConstant scaleWindow) :
    WZ2PaperFiniteErrorConstant
      (pureWZ2Prop62CompressedScaleWindow scaleWindow) := by
  constructor
  · calc
      (1 : ENNReal) = 1 * 1 := by simp
      _ ≤ 1000 * scaleWindow ^ 3 := by
        exact
          mul_le_mul
            (by norm_num)
            (one_le_pow₀ finite.1)
            (by simp) (by simp)
  · exact
      ENNReal.mul_ne_top (by norm_num) <|
        ENNReal.pow_ne_top finite.2

theorem scaleWindow_le_pureWZ2Prop62CompressedScaleWindow
    {scaleWindow : ENNReal}
    (finite : WZ2PaperFiniteErrorConstant scaleWindow) :
    scaleWindow ≤
      pureWZ2Prop62CompressedScaleWindow scaleWindow := by
  unfold pureWZ2Prop62CompressedScaleWindow
  have squareOne : (1 : ENNReal) ≤ scaleWindow ^ 2 :=
    one_le_pow₀ finite.1
  calc
    scaleWindow = 1 * scaleWindow := by simp
    _ ≤ scaleWindow ^ 2 * scaleWindow :=
      mul_le_mul_right' squareOne scaleWindow
    _ ≤ 1000 * (scaleWindow ^ 2 * scaleWindow) := by
      simpa only [one_mul] using
        mul_le_mul_right'
          (show (1 : ENNReal) ≤ 1000 by norm_num)
          (scaleWindow ^ 2 * scaleWindow)
    _ = 1000 * scaleWindow ^ 3 := by ring

structure PureWZ2Prop62CompressionCertificate
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {depthBound : ℕ}
    (bounded :
      PureWZ2Prop62BoundedPureSchedule
        fine ambientConstant scaleWindow depthBound)
    (rho : ℝ) where
  upperCoordinate : Fin bounded.schedule.levelCount
  packetCoordinate : Fin bounded.schedule.levelCount
  upper_before_packet :
    upperCoordinate.1 < packetCoordinate.1
  rho_le_upperScale :
    rho ≤ bounded.schedule.actualScale upperCoordinate
  packetScale_lt :
    bounded.schedule.actualScale packetCoordinate < rho / 1000
  scale_bridge :
    bounded.schedule.actualScale upperCoordinate ≤
      1000 * scaleWindow.toReal ^ 2 *
        bounded.schedule.actualScale packetCoordinate

namespace PureWZ2Prop62CompressionCertificate

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {depthBound : ℕ}
    {bounded :
      PureWZ2Prop62BoundedPureSchedule
        fine ambientConstant scaleWindow depthBound}
    (certificate :
      PureWZ2Prop62CompressionCertificate bounded rho)

theorem compressed_rounding :
    ∀ requested : WZ2PaperRequestedScale delta,
      ∃ coordinate :
          Fin
            (bounded.schedule.compressedLevelCount
              certificate.upperCoordinate certificate.packetCoordinate),
        requested.1 ≤
            bounded.schedule.actualScale
              (bounded.schedule.compressedAmbientCoordinate
                certificate.upperCoordinate certificate.packetCoordinate
                certificate.upper_before_packet coordinate) ∧
          ENNReal.ofReal
              (bounded.schedule.actualScale
                (bounded.schedule.compressedAmbientCoordinate
                  certificate.upperCoordinate certificate.packetCoordinate
                  certificate.upper_before_packet coordinate)) <
            pureWZ2Prop62CompressedScaleWindow scaleWindow *
              ENNReal.ofReal requested.1 := by
  intro requested
  rcases bounded.schedule.rounding requested with
    ⟨coordinate, requestedLe, withinWindow⟩
  by_cases hprefix :
      coordinate.1 < certificate.upperCoordinate.1 + 1
  · let selected :
        Fin
          (bounded.schedule.compressedLevelCount
            certificate.upperCoordinate certificate.packetCoordinate) :=
      ⟨coordinate.1, by
        unfold PureWZ2Prop62PureSchedule.compressedLevelCount
        omega⟩
    have ambientEq :
        bounded.schedule.compressedAmbientCoordinate
            certificate.upperCoordinate certificate.packetCoordinate
            certificate.upper_before_packet selected =
          coordinate := by
      apply Fin.ext
      exact
        bounded.schedule.compressedAmbientCoordinate_of_lt
          certificate.upperCoordinate certificate.packetCoordinate
          certificate.upper_before_packet selected hprefix
    refine ⟨selected, ?_, ?_⟩
    · rwa [ambientEq]
    · rw [ambientEq]
      exact withinWindow.trans_le <| by
        gcongr
        exact
          scaleWindow_le_pureWZ2Prop62CompressedScaleWindow
            bounded.schedule.scaleWindow_finite
  · by_cases hsuffix :
        certificate.packetCoordinate.1 ≤ coordinate.1
    · let selected :
          Fin
            (bounded.schedule.compressedLevelCount
              certificate.upperCoordinate certificate.packetCoordinate) :=
        ⟨certificate.upperCoordinate.1 + 1 +
            (coordinate.1 - certificate.packetCoordinate.1), by
          unfold PureWZ2Prop62PureSchedule.compressedLevelCount
          have packetLe :
              certificate.packetCoordinate.1 ≤
                bounded.schedule.levelCount :=
            Nat.le_of_lt certificate.packetCoordinate.2
          have coordinateLt := coordinate.2
          omega⟩
      have selectedSuffix :
          ¬ selected.1 < certificate.upperCoordinate.1 + 1 := by
        dsimp only [selected]
        omega
      have ambientVal :
          (bounded.schedule.compressedAmbientCoordinate
            certificate.upperCoordinate certificate.packetCoordinate
            certificate.upper_before_packet selected).1 =
              coordinate.1 := by
        rw [
          bounded.schedule.compressedAmbientCoordinate_of_not_lt
            certificate.upperCoordinate certificate.packetCoordinate
            certificate.upper_before_packet selected selectedSuffix
        ]
        dsimp only [selected]
        omega
      have ambientEq :
          bounded.schedule.compressedAmbientCoordinate
              certificate.upperCoordinate certificate.packetCoordinate
              certificate.upper_before_packet selected =
            coordinate :=
        Fin.ext ambientVal
      refine ⟨selected, ?_, ?_⟩
      · rwa [ambientEq]
      · rw [ambientEq]
        exact withinWindow.trans_le <| by
          gcongr
          exact
            scaleWindow_le_pureWZ2Prop62CompressedScaleWindow
              bounded.schedule.scaleWindow_finite
    · have upperLeCoordinate :
          certificate.upperCoordinate.1 ≤ coordinate.1 := by
        omega
      have coordinateLtPacket :
          coordinate.1 < certificate.packetCoordinate.1 := by
        omega
      have requestedLeUpper :
          requested.1 ≤
            bounded.schedule.actualScale certificate.upperCoordinate :=
        requestedLe.trans <|
          bounded.schedule.actualScale_antitone
            certificate.upperCoordinate coordinate upperLeCoordinate
      have packetLeCoordinate :
          bounded.schedule.actualScale certificate.packetCoordinate ≤
            bounded.schedule.actualScale coordinate :=
        bounded.schedule.actualScale_antitone
          coordinate certificate.packetCoordinate coordinateLtPacket.le
      let selected :=
        bounded.schedule.compressedUpperCoordinate
          certificate.upperCoordinate certificate.packetCoordinate
      have ambientEq :
          bounded.schedule.compressedAmbientCoordinate
              certificate.upperCoordinate certificate.packetCoordinate
              certificate.upper_before_packet selected =
            certificate.upperCoordinate :=
        bounded.schedule.compressedAmbientCoordinate_upper_eq
          certificate.upperCoordinate certificate.packetCoordinate
          certificate.upper_before_packet
      have bridgeZero :
          (1000 : ENNReal) * scaleWindow ^ 2 ≠ 0 := by
        exact mul_ne_zero (by norm_num) <|
          pow_ne_zero _ <|
            ne_of_gt <|
              zero_lt_one.trans_le
                bounded.schedule.scaleWindow_finite.1
      have bridgeTop :
          (1000 : ENNReal) * scaleWindow ^ 2 ≠ ⊤ := by
        exact ENNReal.mul_ne_top (by norm_num) <|
          ENNReal.pow_ne_top bounded.schedule.scaleWindow_finite.2
      have scaledWindow :
          ((1000 : ENNReal) * scaleWindow ^ 2) *
              ENNReal.ofReal
                (bounded.schedule.actualScale coordinate) <
            ((1000 : ENNReal) * scaleWindow ^ 2) *
              (scaleWindow * ENNReal.ofReal requested.1) := by
        simpa only [mul_comm] using
          ENNReal.mul_lt_mul_left bridgeZero bridgeTop withinWindow
      have scaleBridgeENN :
          ENNReal.ofReal
              (bounded.schedule.actualScale
                certificate.upperCoordinate) ≤
            ((1000 : ENNReal) * scaleWindow ^ 2) *
              ENNReal.ofReal
                (bounded.schedule.actualScale
                  certificate.packetCoordinate) := by
        have raw := ENNReal.ofReal_mono certificate.scale_bridge
        have scaleWindowNonnegative :
            0 ≤ scaleWindow.toReal :=
          ENNReal.toReal_nonneg
        have scaleWindowSquareNonnegative :
            0 ≤ 1000 * scaleWindow.toReal ^ 2 := by
          positivity
        rw [
          ENNReal.ofReal_mul scaleWindowSquareNonnegative,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1000),
          ENNReal.ofReal_pow scaleWindowNonnegative,
          ENNReal.ofReal_toReal bounded.schedule.scaleWindow_finite.2
        ] at raw
        norm_num at raw
        simpa only [mul_assoc] using raw
      refine ⟨selected, ?_, ?_⟩
      · rwa [ambientEq]
      · rw [ambientEq]
        calc
          ENNReal.ofReal
              (bounded.schedule.actualScale
                certificate.upperCoordinate) ≤
              ((1000 : ENNReal) * scaleWindow ^ 2) *
                ENNReal.ofReal
                  (bounded.schedule.actualScale
                    certificate.packetCoordinate) :=
            scaleBridgeENN
          _ ≤
              ((1000 : ENNReal) * scaleWindow ^ 2) *
                ENNReal.ofReal
                  (bounded.schedule.actualScale coordinate) := by
            exact
              mul_le_mul_left'
                (ENNReal.ofReal_mono packetLeCoordinate) _
          _ <
              ((1000 : ENNReal) * scaleWindow ^ 2) *
                (scaleWindow * ENNReal.ofReal requested.1) :=
            scaledWindow
          _ =
              pureWZ2Prop62CompressedScaleWindow scaleWindow *
                ENNReal.ofReal requested.1 := by
            unfold pureWZ2Prop62CompressedScaleWindow
            ring

/--
Choose the last retained upper coordinate and the paper packet coordinate by
rounding `rho` and `rho / (1000 * scaleWindow.toReal)`, respectively.
-/
theorem exists_compressionCertificate
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (packetRequestedLower :
      delta ≤ rho / (1000 * scaleWindow.toReal)) :
    Nonempty
      (PureWZ2Prop62CompressionCertificate bounded rho) := by
  have scaleWindowRealOne :
      1 ≤ scaleWindow.toReal := by
    simpa only [ENNReal.toReal_one] using
      ENNReal.toReal_mono
        bounded.schedule.scaleWindow_finite.2
        bounded.schedule.scaleWindow_finite.1
  have scaleWindowRealPos :
      0 < scaleWindow.toReal := lt_of_lt_of_le zero_lt_one scaleWindowRealOne
  have denominatorPos :
      0 < 1000 * scaleWindow.toReal := by positivity
  have packetRequestedLeRho :
      rho / (1000 * scaleWindow.toReal) ≤ rho := by
    apply (div_le_iff₀ denominatorPos).2
    nlinarith [mul_nonneg rhoPos.le
      (sub_nonneg.mpr <| by nlinarith [scaleWindowRealOne])]
  let upperRequested : WZ2PaperRequestedScale delta :=
    ⟨rho, packetRequestedLower.trans packetRequestedLeRho,
      rhoLeOne⟩
  let packetRequested : WZ2PaperRequestedScale delta :=
    ⟨rho / (1000 * scaleWindow.toReal),
      packetRequestedLower,
      packetRequestedLeRho.trans rhoLeOne⟩
  rcases bounded.schedule.rounding upperRequested with
    ⟨upperCoordinate, rhoLeUpper, upperWithin⟩
  rcases bounded.schedule.rounding packetRequested with
    ⟨packetCoordinate, packetRequestedLe, packetWithin⟩
  have packetScaleLt :
      bounded.schedule.actualScale packetCoordinate < rho / 1000 := by
    have targetPos : 0 < rho / 1000 := by positivity
    apply (ENNReal.ofReal_lt_ofReal_iff targetPos).mp
    calc
      ENNReal.ofReal
          (bounded.schedule.actualScale packetCoordinate) <
          scaleWindow * ENNReal.ofReal packetRequested.1 :=
        packetWithin
      _ = ENNReal.ofReal (rho / 1000) := by
        have scaleWindowRepresentation :
            ENNReal.ofReal scaleWindow.toReal = scaleWindow :=
          ENNReal.ofReal_toReal
            bounded.schedule.scaleWindow_finite.2
        have requestedIdentity :
            scaleWindow.toReal * packetRequested.1 = rho / 1000 := by
          dsimp only [packetRequested]
          field_simp [scaleWindowRealPos.ne']
        rw [← scaleWindowRepresentation,
          ← ENNReal.ofReal_mul scaleWindowRealPos.le,
          requestedIdentity]
  have packetFractionLtRho : rho / 1000 < rho := by
    exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1000)).2 <| by
      nlinarith
  have upperBeforePacket :
      upperCoordinate.1 < packetCoordinate.1 := by
    by_contra notBefore
    have packetLeUpper :
        packetCoordinate.1 ≤ upperCoordinate.1 := by omega
    have upperScaleLePacket :=
      bounded.schedule.actualScale_antitone
        packetCoordinate upperCoordinate packetLeUpper
    nlinarith
  have upperScaleLt :
      bounded.schedule.actualScale upperCoordinate <
        scaleWindow.toReal * rho := by
    have targetPos :
        0 < scaleWindow.toReal * rho := by positivity
    apply (ENNReal.ofReal_lt_ofReal_iff targetPos).mp
    calc
      ENNReal.ofReal
          (bounded.schedule.actualScale upperCoordinate) <
          scaleWindow * ENNReal.ofReal upperRequested.1 :=
        upperWithin
      _ = ENNReal.ofReal (scaleWindow.toReal * rho) := by
        have scaleWindowRepresentation :
            ENNReal.ofReal scaleWindow.toReal = scaleWindow :=
          ENNReal.ofReal_toReal
            bounded.schedule.scaleWindow_finite.2
        dsimp only [upperRequested]
        calc
          scaleWindow * ENNReal.ofReal rho =
              ENNReal.ofReal scaleWindow.toReal *
                ENNReal.ofReal rho := by
            rw [scaleWindowRepresentation]
          _ = ENNReal.ofReal (scaleWindow.toReal * rho) := by
            rw [ENNReal.ofReal_mul scaleWindowRealPos.le]
  have scaleBridge :
      bounded.schedule.actualScale upperCoordinate ≤
        1000 * scaleWindow.toReal ^ 2 *
          bounded.schedule.actualScale packetCoordinate := by
    have exactBridge :
        scaleWindow.toReal * rho =
          1000 * scaleWindow.toReal ^ 2 *
            packetRequested.1 := by
      dsimp only [packetRequested]
      field_simp [scaleWindowRealPos.ne']
    calc
      bounded.schedule.actualScale upperCoordinate ≤
          scaleWindow.toReal * rho :=
        upperScaleLt.le
      _ =
          1000 * scaleWindow.toReal ^ 2 *
            packetRequested.1 :=
        exactBridge
      _ ≤
          1000 * scaleWindow.toReal ^ 2 *
            bounded.schedule.actualScale packetCoordinate := by
        gcongr
  exact
    ⟨{
      upperCoordinate := upperCoordinate
      packetCoordinate := packetCoordinate
      upper_before_packet := upperBeforePacket
      rho_le_upperScale := rhoLeUpper
      packetScale_lt := packetScaleLt
      scale_bridge := scaleBridge
    }⟩

noncomputable def compressedSchedule :
    PureWZ2Prop62PureSchedule
      fine ambientConstant
      (pureWZ2Prop62CompressedScaleWindow scaleWindow) :=
  bounded.schedule.compress
    certificate.upperCoordinate certificate.packetCoordinate
    certificate.upper_before_packet
    (pureWZ2Prop62CompressedScaleWindow scaleWindow)
    (pureWZ2Prop62CompressedScaleWindow_finite
      bounded.schedule.scaleWindow_finite)
    certificate.compressed_rounding

abbrev compressedPacketCoordinate :
    Fin certificate.compressedSchedule.levelCount :=
  bounded.schedule.compressedPacketCoordinate
    certificate.upperCoordinate certificate.packetCoordinate

theorem compressed_levelCount_le :
    certificate.compressedSchedule.levelCount ≤ depthBound := by
  apply le_trans ?_ bounded.levelCount_le
  change
    bounded.schedule.compressedLevelCount
        certificate.upperCoordinate certificate.packetCoordinate ≤
      bounded.schedule.levelCount
  unfold PureWZ2Prop62PureSchedule.compressedLevelCount
  have packetLe :
      certificate.packetCoordinate.1 ≤
        bounded.schedule.levelCount :=
    Nat.le_of_lt certificate.packetCoordinate.2
  have upperSuccLePacket :
      certificate.upperCoordinate.1 + 1 ≤
        certificate.packetCoordinate.1 := by
    exact Nat.succ_le_iff.mpr certificate.upper_before_packet
  calc
    certificate.upperCoordinate.1 + 1 +
          (bounded.schedule.levelCount -
            certificate.packetCoordinate.1) ≤
        certificate.packetCoordinate.1 +
          (bounded.schedule.levelCount -
            certificate.packetCoordinate.1) :=
      Nat.add_le_add_right upperSuccLePacket _
    _ = bounded.schedule.levelCount :=
      Nat.add_sub_of_le packetLe

theorem compressed_packetScale_lt :
    certificate.compressedSchedule.actualScale
        certificate.compressedPacketCoordinate <
      rho / 1000 := by
  simpa [compressedSchedule, compressedPacketCoordinate] using
    certificate.packetScale_lt

theorem compressed_packetScale_lt_rho
    (rhoPos : 0 < rho) :
    certificate.compressedSchedule.actualScale
        certificate.compressedPacketCoordinate < rho := by
  have thousandOne : (1 : ℝ) < 1000 := by norm_num
  have fractionLt : rho / 1000 < rho := by
    exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1000)).2 <| by
      nlinarith
  exact certificate.compressed_packetScale_lt.trans fractionLt

theorem compressed_allAncestryCoordinatesUpper :
    ∀ coordinate :
        certificate.compressedSchedule.AncestryCoordinate
          certificate.compressedPacketCoordinate,
      rho ≤
        certificate.compressedSchedule.actualScale
          (certificate.compressedSchedule.ancestryAmbientCoordinate
            certificate.compressedPacketCoordinate coordinate) := by
  intro coordinate
  let compressedAmbient :=
    certificate.compressedSchedule.ancestryAmbientCoordinate
      certificate.compressedPacketCoordinate coordinate
  let ambient :=
    bounded.schedule.compressedAmbientCoordinate
      certificate.upperCoordinate certificate.packetCoordinate
      certificate.upper_before_packet compressedAmbient
  have coordinateLeUpper :
      compressedAmbient.1 ≤ certificate.upperCoordinate.1 := by
    change coordinate.1 ≤ certificate.upperCoordinate.1
    have coordinateLt :
        coordinate.1 < certificate.upperCoordinate.1 + 1 := by
      simpa only [
        PureWZ2Prop62PureSchedule.compressedPacketCoordinate
      ] using coordinate.isLt
    exact Nat.lt_succ_iff.mp coordinateLt
  have hprefix :
      compressedAmbient.1 < certificate.upperCoordinate.1 + 1 := by
    omega
  have ambientVal :
      ambient.1 = compressedAmbient.1 :=
    bounded.schedule.compressedAmbientCoordinate_of_lt
      certificate.upperCoordinate certificate.packetCoordinate
      certificate.upper_before_packet compressedAmbient hprefix
  have ambientLeUpper :
      ambient.1 ≤ certificate.upperCoordinate.1 := by
    rw [ambientVal]
    exact coordinateLeUpper
  have upperLeAmbient :
      bounded.schedule.actualScale certificate.upperCoordinate ≤
        bounded.schedule.actualScale ambient :=
    bounded.schedule.actualScale_antitone
      ambient certificate.upperCoordinate ambientLeUpper
  have targetEq :
      certificate.compressedSchedule.actualScale
          (certificate.compressedSchedule.ancestryAmbientCoordinate
            certificate.compressedPacketCoordinate coordinate) =
        bounded.schedule.actualScale ambient := by
    rfl
  rw [targetEq]
  exact certificate.rho_le_upperScale.trans upperLeAmbient

theorem metricMeshWidth_pos
    (rhoPos : 0 < rho) :
    0 < pureWZ2Prop62MetricMeshWidth rho := by
  unfold pureWZ2Prop62MetricMeshWidth
  positivity

theorem six_metricMeshWidth_le
    (rhoPos : 0 < rho) :
    6 * pureWZ2Prop62MetricMeshWidth rho ≤ rho / 2 := by
  unfold pureWZ2Prop62MetricMeshWidth
  nlinarith

theorem metricMesh_strongSeparation
    (rhoPos : 0 < rho) :
    360 * rho <
      (((pureWZ2Prop62ResidueStrideBase + 1 : ℕ) : ℝ) - 1) *
        pureWZ2Prop62MetricMeshWidth rho := by
  unfold pureWZ2Prop62ResidueStrideBase
    pureWZ2Prop62MetricMeshWidth
  norm_num
  linarith

theorem metricMesh_packetBound
    (rhoPos : 0 < rho) :
    (16 * 5 + 44) *
          certificate.compressedSchedule.actualScale
            certificate.compressedPacketCoordinate +
        6 * pureWZ2Prop62MetricMeshWidth rho ≤
      rho / 2 := by
  have packetSmall := certificate.compressed_packetScale_lt
  unfold pureWZ2Prop62MetricMeshWidth
  norm_num at packetSmall ⊢
  nlinarith

/--
Construct the canonical preliminary metric-parent object with every mesh
parameter fixed by the paper-facing compression certificate.
-/
theorem canonicalMetricPreliminary
    (weight : Fin fine.card → ENNReal)
    (totalFinite :
      (∑ source : Fin fine.card, weight source) ≠ ⊤)
    (totalPos :
      0 < ∑ source : Fin fine.card, weight source)
    (rhoPos : 0 < rho)
    (fineNonempty : fine.Nonempty)
    (fineLine : WZ1PaperIsLineClass fine)
    (actualScaleLeOne :
      ∀ coordinate,
        certificate.compressedSchedule.actualScale coordinate ≤ 1)
    (fineBoundedBase : HasBoundedBase fine 4) :
    Nonempty
      (PureWZ2Prop62CanonicalMetricPreliminaryOutput
        (rho := rho)
        certificate.compressedSchedule
        (pureWZ2Prop62MetricMeshWidth rho)
        certificate.compressedPacketCoordinate weight 5
        pureWZ2Prop62ResidueStrideBase) := by
  exact
    pureWZ2_prop62_canonical_metric_preliminary
      certificate.compressedSchedule
      (pureWZ2Prop62MetricMeshWidth rho)
      certificate.compressedPacketCoordinate weight 5
      pureWZ2Prop62ResidueStrideBase
      totalFinite totalPos rhoPos fineNonempty fineLine
      actualScaleLeOne fineBoundedBase
      (PureWZ2Prop62AncestryMetricPreliminaryOutput.fine_midpoint_norm_le_five
        fineBoundedBase)
      (metricMeshWidth_pos (rho := rho) rhoPos)
      (metricMesh_strongSeparation (rho := rho) rhoPos)
      (certificate.metricMesh_packetBound rhoPos)

/--
Finish the metric-parent lemma from a canonical preliminary output.  The
schedule-depth, residue-stride, mesh-width, packet-scale, ancestry, and
axis-box obligations are all discharged from producer provenance.
-/
theorem metricParentsOutput_of_smallDelta
    {weight : Fin fine.card → ENNReal}
    (canonical :
      PureWZ2Prop62CanonicalMetricPreliminaryOutput
        (rho := rho)
        certificate.compressedSchedule
        (pureWZ2Prop62MetricMeshWidth rho)
        certificate.compressedPacketCoordinate weight 5
        pureWZ2Prop62ResidueStrideBase)
    (deltaPos : 0 < delta)
    (deltaLe :
      delta ≤
        PureWZ2Prop62AncestryMetricPreliminaryOutput.pureWZ2Prop62CanonicalMassThreshold
          depthBound pureWZ2Prop62ResidueStrideBase)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (scaleSeparation : 100 * delta ≤ rho)
    (fineUnitBall : fine.IsInUnitBall)
    (fineBoundedBase : HasBoundedBase fine 4) :
    Nonempty
      (PureWZ2Prop62MetricParentsOutput
        (rho := rho)
        (certificate.compressedSchedule.scaleData
          certificate.compressedPacketCoordinate)
        weight 10) := by
  apply
    canonical.metricParentsOutput_of_smallDelta
      depthBound pureWZ2Prop62ResidueStrideBase
      deltaPos deltaLe certificate.compressed_levelCount_le
      canonical.preliminary_residueStrideBase.le rhoPos rhoLeOne
      (fun coordinate =>
        bounded.actualScale_le_one
          (bounded.schedule.compressedAmbientCoordinate
            certificate.upperCoordinate certificate.packetCoordinate
            certificate.upper_before_packet coordinate))
      (metricMeshWidth_pos (rho := rho) rhoPos)
      (certificate.compressed_packetScale_lt_rho rhoPos)
      (six_metricMeshWidth_le (rho := rho) rhoPos)
      certificate.compressed_allAncestryCoordinatesUpper
      scaleSeparation
  · intro source
    rw [canonical.finalMetricRestriction.fineSelected.tube_eq,
      canonical.output.metric.mesh.complete.selectedFine.tube_eq]
    intro point pointMem
    apply wz2_paper_unitBall_subset_axisBox
    exact
      fineUnitBall
        (canonical.output.metric.mesh.complete.selectedFine.embedding
          (canonical.finalMetricRestriction.fineSelected.embedding source))
        pointMem
  · exact fineBoundedBase

end PureWZ2Prop62CompressionCertificate

structure PureWZ2Prop62CanonicalMetricParentsProducerOutput
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {depthBound : ℕ}
    (bounded :
      PureWZ2Prop62BoundedPureSchedule
        fine ambientConstant scaleWindow depthBound)
    (weight : Fin fine.card → ENNReal) where
  compression :
    PureWZ2Prop62CompressionCertificate bounded rho
  preliminary :
    PureWZ2Prop62CanonicalMetricPreliminaryOutput
      (rho := rho)
      compression.compressedSchedule
      (pureWZ2Prop62MetricMeshWidth rho)
      compression.compressedPacketCoordinate weight 5
      pureWZ2Prop62ResidueStrideBase
  output :
    PureWZ2Prop62MetricParentsOutput
      (rho := rho)
      (compression.compressedSchedule.scaleData
        compression.compressedPacketCoordinate)
      weight 10

/--
Canonical paper-order metric-parent producer.

No schedule depth, mesh width, residue stride, packet coordinate, ancestry
cut, coloring, conflict relation, or mass-retention inequality is supplied by
the caller.
-/
theorem pureWZ2_prop62_canonical_metric_parents
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {depthBound : ℕ}
    (bounded :
      PureWZ2Prop62BoundedPureSchedule
        fine ambientConstant scaleWindow depthBound)
    (weight : Fin fine.card → ENNReal)
    (totalFinite :
      (∑ source : Fin fine.card, weight source) ≠ ⊤)
    (totalPos :
      0 < ∑ source : Fin fine.card, weight source)
    (deltaPos : 0 < delta)
    (deltaLe :
      delta ≤
        PureWZ2Prop62AncestryMetricPreliminaryOutput.pureWZ2Prop62CanonicalMassThreshold
          depthBound pureWZ2Prop62ResidueStrideBase)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (packetRequestedLower :
      delta ≤ rho / (1000 * scaleWindow.toReal))
    (scaleSeparation : 100 * delta ≤ rho)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineUnitBall : fine.IsInUnitBall)
    (fineBoundedBase : HasBoundedBase fine 4) :
    Nonempty
      (PureWZ2Prop62CanonicalMetricParentsProducerOutput
        (rho := rho) bounded weight) := by
  have fineNonempty : fine.Nonempty := by
    by_contra notNonempty
    have cardZero : fine.card = 0 :=
      Nat.eq_zero_of_not_pos notNonempty
    have totalZero :
        (∑ source : Fin fine.card, weight source) = 0 := by
      apply Finset.sum_eq_zero
      intro source _sourceMem
      exact False.elim <| by
        have sourceLt : source.1 < 0 := by
          simpa only [cardZero] using source.2
        omega
    rw [totalZero] at totalPos
    exact (lt_self_iff_false 0).mp totalPos
  let compression :=
    Classical.choice <|
      PureWZ2Prop62CompressionCertificate.exists_compressionCertificate
        (bounded := bounded) rhoPos rhoLeOne packetRequestedLower
  let preliminary :=
    Classical.choice <|
      compression.canonicalMetricPreliminary
        weight totalFinite totalPos rhoPos fineNonempty fineLine
        (fun coordinate =>
          bounded.actualScale_le_one
            (bounded.schedule.compressedAmbientCoordinate
              compression.upperCoordinate compression.packetCoordinate
              compression.upper_before_packet coordinate))
        fineBoundedBase
  let output :=
    Classical.choice <|
      compression.metricParentsOutput_of_smallDelta
        preliminary deltaPos deltaLe rhoPos rhoLeOne
        scaleSeparation fineUnitBall fineBoundedBase
  exact
    ⟨{
      compression := compression
      preliminary := preliminary
      output := output
    }⟩

end Kakeya.Assouad

end
