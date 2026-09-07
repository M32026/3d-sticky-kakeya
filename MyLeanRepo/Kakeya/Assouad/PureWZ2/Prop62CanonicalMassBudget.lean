import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CanonicalColorBundle
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerCenterEnvelopeConflictDegree
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBoundaryLogCoefficient
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLinePackingCardinality

/-!
# Proposition 6.2: canonical metric-parent mass budget

For fixed schedule depth and mesh-residue modulus, every structural loss is
an absolute constant.  The two dyadic losses are controlled by the
polynomial cardinality of a bounded ordinary essentially-distinct family.
Both bounds fit inside `log(1 / delta)^2` below one explicit common threshold.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

def pureWZ2Prop62CanonicalStructuralBound
    (depthBound strideBaseBound : ℕ) : ENNReal :=
  max
    (((strideBaseBound + 1 : ℕ) : ENNReal) ^ 4 *
      ((pureWZ2OrdinaryLineConflictDegree + 1 : ℕ) : ENNReal) ^
        depthBound)
    (max
      (((pureWZ2OrdinaryLineConflictDegree + 1 : ℕ) : ENNReal) ^
        (depthBound + 1))
      ((2 : ENNReal) ^ (depthBound + 2)))

def pureWZ2Prop62OrdinaryCardLogConstant : ℝ :=
  max
    (Real.log (2 * (643 : ℝ) ^ 6) / Real.log 2 + 1)
    (6 / Real.log 2)

theorem pureWZ2Prop62CanonicalStructuralBound_ne_top
    (depthBound strideBaseBound : ℕ) :
    pureWZ2Prop62CanonicalStructuralBound
        depthBound strideBaseBound ≠ ⊤ := by
  unfold pureWZ2Prop62CanonicalStructuralBound
  apply max_ne_top
  · exact
      ENNReal.mul_ne_top
        (ENNReal.pow_ne_top (by simp))
        (ENNReal.pow_ne_top (by simp))
  · exact
      max_ne_top
        (ENNReal.pow_ne_top (by simp))
        (ENNReal.pow_ne_top (by simp))

theorem pureWZ2Prop62_ordinary_card_log_bound
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    {cardinality : ℕ}
    (cardinalityPos : 0 < cardinality)
    (cardinalityBound :
      cardinality ≤
        (2 * Nat.ceil (320 / delta) + 1) ^ 6) :
    (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
      pureWZ2Prop62OrdinaryCardLogConstant *
        (1 + Real.log delta⁻¹) := by
  have logTwoPos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  have logInvNonnegative : 0 ≤ Real.log delta⁻¹ := by
    apply Real.log_nonneg
    exact (one_le_inv₀ deltaPos).mpr deltaLeOne
  have constantFirst :
      Real.log (2 * (643 : ℝ) ^ 6) / Real.log 2 + 1 ≤
        pureWZ2Prop62OrdinaryCardLogConstant :=
    le_max_left _ _
  have constantSecond :
      6 / Real.log 2 ≤
        pureWZ2Prop62OrdinaryCardLogConstant :=
    le_max_right _ _
  have doubleCardinalityPos : 0 < 2 * cardinality := by
    positivity
  have ceilPositive : 0 < Nat.ceil (320 / delta) := by
    apply Nat.ceil_pos.mpr
    positivity
  have ceilLt :
      (Nat.ceil (320 / delta) : ℝ) <
        320 / delta + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have baseLe :
      ((2 * Nat.ceil (320 / delta) + 1 : ℕ) : ℝ) ≤
        643 / delta := by
    have threeLe : (3 : ℝ) ≤ 3 / delta := by
      calc
        (3 : ℝ) = 3 / 1 := by norm_num
        _ ≤ 3 / delta := by gcongr
    have middle :
        ((2 * Nat.ceil (320 / delta) + 1 : ℕ) : ℝ) <
          640 / delta + 3 := by
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      calc
        2 * (Nat.ceil (320 / delta) : ℝ) + 1 <
            2 * (320 / delta + 1) + 1 := by
          gcongr
        _ = 640 / delta + 3 := by ring
    calc
      ((2 * Nat.ceil (320 / delta) + 1 : ℕ) : ℝ) ≤
          640 / delta + 3 := middle.le
      _ ≤ 640 / delta + 3 / delta := by gcongr
      _ = 643 / delta := by
        field_simp [deltaPos.ne']
        ring
  have cardinalityReal :
      (cardinality : ℝ) ≤
        ((2 * Nat.ceil (320 / delta) + 1 : ℕ) : ℝ) ^ 6 := by
    exact_mod_cast cardinalityBound
  have basePowerLe :
      ((2 * Nat.ceil (320 / delta) + 1 : ℕ) : ℝ) ^ 6 ≤
        (643 / delta) ^ 6 := by
    gcongr
  have quotientPower :
      (643 / delta) ^ 6 =
        (643 : ℝ) ^ 6 * delta ^ (-6 : ℝ) := by
    have inversePower :
        delta ^ (-6 : ℝ) = (delta ^ 6)⁻¹ := by
      rw [Real.rpow_neg deltaPos.le]
      norm_cast
    rw [inversePower]
    field_simp [deltaPos.ne']
  have polynomialCardinality :
      ((2 * cardinality : ℕ) : ℝ) ≤
        (2 * (643 : ℝ) ^ 6) *
          delta ^ (-6 : ℝ) := by
    calc
      ((2 * cardinality : ℕ) : ℝ) =
          2 * (cardinality : ℝ) := by norm_num
      _ ≤
          2 *
            (((2 * Nat.ceil (320 / delta) + 1 : ℕ) : ℝ) ^ 6) := by
        gcongr
      _ ≤ 2 * (643 / delta) ^ 6 := by
        gcongr
      _ =
          (2 * (643 : ℝ) ^ 6) *
            delta ^ (-6 : ℝ) := by
        rw [quotientPower]
        ring
  have natLog :
      (Nat.log 2 (2 * cardinality) : ℝ) ≤
        Real.log ((2 * cardinality : ℕ) : ℝ) /
          Real.log 2 := by
    have powerLe :
        (2 : ℕ) ^ Nat.log 2 (2 * cardinality) ≤
          2 * cardinality :=
      Nat.pow_log_le_self 2 doubleCardinalityPos.ne'
    have powerLeReal :
        (2 : ℝ) ^ Nat.log 2 (2 * cardinality) ≤
          ((2 * cardinality : ℕ) : ℝ) := by
      exact_mod_cast powerLe
    have logarithm :=
      Real.log_le_log (by positivity) powerLeReal
    rw [Real.log_pow] at logarithm
    exact (le_div_iff₀ logTwoPos).mpr (by simpa using logarithm)
  have cardLog :
      Real.log ((2 * cardinality : ℕ) : ℝ) ≤
        Real.log
          ((2 * (643 : ℝ) ^ 6) *
            delta ^ (-6 : ℝ)) :=
    Real.log_le_log (by exact_mod_cast doubleCardinalityPos)
      polynomialCardinality
  have productLog :
      Real.log
          ((2 * (643 : ℝ) ^ 6) *
            delta ^ (-6 : ℝ)) =
        Real.log (2 * (643 : ℝ) ^ 6) +
          6 * Real.log delta⁻¹ := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_rpow deltaPos (-6 : ℝ), Real.log_inv]
    ring
  calc
    (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
        Real.log ((2 * cardinality : ℕ) : ℝ) /
            Real.log 2 + 1 := by
      linarith
    _ ≤
        Real.log
            ((2 * (643 : ℝ) ^ 6) *
              delta ^ (-6 : ℝ)) /
            Real.log 2 + 1 := by
      gcongr
    _ =
        (Real.log (2 * (643 : ℝ) ^ 6) /
            Real.log 2 + 1) +
          (6 / Real.log 2) * Real.log delta⁻¹ := by
      rw [productLog]
      field_simp [logTwoPos.ne']
      ring
    _ ≤
        pureWZ2Prop62OrdinaryCardLogConstant +
          pureWZ2Prop62OrdinaryCardLogConstant *
            Real.log delta⁻¹ := by
      gcongr
    _ =
        pureWZ2Prop62OrdinaryCardLogConstant *
          (1 + Real.log delta⁻¹) := by
      ring

namespace PureWZ2Prop62AncestryMetricPreliminaryOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow}
    {scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule}
    {sourceConflict :
      PureWZ2Prop62SourceConflictColoringData fine}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {weight : Fin fine.card → ENNReal}
    {preliminary :
      PureWZ2Prop62AncestryPreliminarySelectionData
        schedule scheduled rho width packetCoordinate
        schedule.CanonicalColor
        (schedule.canonicalColor scheduled sourceConflict)
        weight}
    {M : ℝ}
    (output :
      PureWZ2Prop62AncestryMetricPreliminaryOutput
        schedule scheduled width packetCoordinate
        schedule.CanonicalColor
        (schedule.canonicalColor scheduled sourceConflict)
        weight preliminary M)

theorem upperColorCoordinate_card_le_levelCount :
    Fintype.card (schedule.UpperCoordinate rho packetCoordinate) ≤
      schedule.levelCount := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective
      (fun coordinate :
        schedule.UpperCoordinate rho packetCoordinate => coordinate.1)
      (fun first second equality => Subtype.ext equality)

theorem canonicalStructuralMassLoss_le
    {depthBound strideBaseBound : ℕ}
    (depthLe : schedule.levelCount ≤ depthBound)
    (strideLe :
      preliminary.residueStrideBase ≤ strideBaseBound) :
    output.canonicalStructuralMassLoss ≤
      pureWZ2Prop62CanonicalStructuralBound
        depthBound strideBaseBound := by
  have residueCard :
      Fintype.card
          (Fin 4 → ZMod (preliminary.residueStrideBase + 1)) =
        (preliminary.residueStrideBase + 1) ^ 4 := by
    simp [Fintype.card_fun]
  have residueBaseLe :
      preliminary.residueStrideBase + 1 ≤
        strideBaseBound + 1 := by
    omega
  have residuePowerLe :
      (preliminary.residueStrideBase + 1) ^ 4 ≤
        (strideBaseBound + 1) ^ 4 :=
    Nat.pow_le_pow_left residueBaseLe 4
  have upperColorCard :
      Fintype.card
          (schedule.UpperColorVector rho packetCoordinate) =
        (pureWZ2OrdinaryLineConflictDegree + 1) ^
          Fintype.card
            (schedule.UpperCoordinate rho packetCoordinate) := by
    simp [Fintype.card_pi]
  have upperPowerLe :
      (pureWZ2OrdinaryLineConflictDegree + 1) ^
          Fintype.card
            (schedule.UpperCoordinate rho packetCoordinate) ≤
        (pureWZ2OrdinaryLineConflictDegree + 1) ^ depthBound := by
    exact
      Nat.pow_le_pow_right (by positivity) <|
        (upperColorCoordinate_card_le_levelCount
          (schedule := schedule) (rho := rho)
          (packetCoordinate := packetCoordinate)).trans depthLe
  have perCellLe :
      (Fintype.card
          (Fin 4 → ZMod (preliminary.residueStrideBase + 1)) : ENNReal) *
        (Fintype.card
          (schedule.UpperColorVector rho packetCoordinate) : ENNReal) ≤
      ((strideBaseBound + 1 : ℕ) : ENNReal) ^ 4 *
        ((pureWZ2OrdinaryLineConflictDegree + 1 : ℕ) : ENNReal) ^
          depthBound := by
    rw [residueCard, upperColorCard]
    exact_mod_cast
      Nat.mul_le_mul residuePowerLe upperPowerLe
  have globalColorLe :
      (Fintype.card
        (∀ coordinate : schedule.CanonicalColorCoordinate,
          schedule.CanonicalColor coordinate) : ENNReal) ≤
        ((pureWZ2OrdinaryLineConflictDegree + 1 : ℕ) : ENNReal) ^
          (depthBound + 1) := by
    rw [schedule.canonicalColor_card]
    exact_mod_cast
      Nat.pow_le_pow_right (by positivity) (by omega)
  have treeLe :
      (2 : ENNReal) ^ (schedule.levelCount + 2) ≤
        (2 : ENNReal) ^ (depthBound + 2) := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  unfold canonicalStructuralMassLoss
  dsimp only
  exact
    max_le
      (perCellLe.trans <| le_max_left _ _)
      (max_le
        (globalColorLe.trans <|
          (le_max_left _ _).trans (le_max_right _ _))
        (treeLe.trans <|
          (le_max_right _ _).trans (le_max_right _ _)))

theorem fine_midpoint_norm_le_five
    (fineBoundedBase : HasBoundedBase fine 4)
    (source : Fin fine.card) :
    ‖wz2PaperTubeMidpoint (fine.tube source)‖ ≤ 5 := by
  dsimp only [wz2PaperTubeMidpoint]
  calc
    ‖(fine.tube source).base +
        (1 / 2 : ℝ) • (fine.tube source).direction‖ ≤
        ‖(fine.tube source).base‖ +
          ‖(1 / 2 : ℝ) • (fine.tube source).direction‖ :=
      norm_add_le _ _
    _ = ‖(fine.tube source).base‖ + 1 / 2 := by
      rw [norm_smul, (fine.tube source).direction_unit]
      norm_num
    _ ≤ 5 := by
      linarith [fineBoundedBase source]

theorem ambientDyadic_le_logSquare_of_raw
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    (fineNonempty : fine.Nonempty)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine)
    (fineBoundedBase : HasBoundedBase fine 4)
    (rawAbsorption :
      ENNReal.ofReal
          ((2 * pureWZ2Prop62OrdinaryCardLogConstant) *
            (1 + Real.log delta⁻¹)) ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2) :
    (2 * (Nat.log 2 (2 * fine.card) + 1) : ENNReal) ≤
      (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 := by
  let scaleCount := Nat.ceil (320 / delta)
  have rawCard :
      fine.card ≤ (2 * scaleCount + 1) ^ 6 := by
    have raw :=
      wz2PaperOrdinary_local_six_grid_card_bound
        deltaPos (show (0 : ℝ) ≤ 5 by norm_num)
        fineDistinct Finset.univ (0 : Point3) <| by
          intro source _
          simpa [dist_zero_right] using
            fine_midpoint_norm_le_five
              (fine := fine) fineBoundedBase source
    have firstArgument :
        5 / (delta / 64) = 320 / delta := by
      field_simp [deltaPos.ne']
      norm_num
    have secondArgument :
        1 / (delta / 64) ≤ 320 / delta := by
      have identity : 1 / (delta / 64) = 64 / delta := by
        field_simp [deltaPos.ne']
      rw [identity]
      exact div_le_div_of_nonneg_right (by norm_num) deltaPos.le
    have firstCeil :
        Nat.ceil (5 / (delta / 64)) = scaleCount := by
      rw [firstArgument]
    have secondCeil :
        Nat.ceil (1 / (delta / 64)) ≤ scaleCount :=
      Nat.ceil_mono secondArgument
    simpa only [Finset.card_univ, Fintype.card_fin] using
      raw.trans <| by
        rw [firstCeil]
        calc
          (2 * scaleCount + 1) ^ 3 *
              (2 * Nat.ceil (1 / (delta / 64)) + 1) ^ 3 ≤
            (2 * scaleCount + 1) ^ 3 *
              (2 * scaleCount + 1) ^ 3 := by
            gcongr
          _ = (2 * scaleCount + 1) ^ 6 := by ring
  have rawLog :=
    pureWZ2Prop62_ordinary_card_log_bound
      deltaPos deltaLeOne
      fineNonempty
      rawCard
  have rawENN :
      (Nat.log 2 (2 * fine.card) + 1 : ENNReal) ≤
        ENNReal.ofReal
          (pureWZ2Prop62OrdinaryCardLogConstant *
            (1 + Real.log delta⁻¹)) := by
    have converted := ENNReal.ofReal_mono rawLog
    have castEq :
        ENNReal.ofReal
            (Nat.log 2 (2 * fine.card) + 1 : ℝ) =
          (Nat.log 2 (2 * fine.card) + 1 : ENNReal) := by
      rw [ENNReal.ofReal_add (by positivity)]
      norm_num
      positivity
    rwa [castEq] at converted
  calc
    (2 * (Nat.log 2 (2 * fine.card) + 1) : ENNReal) ≤
        (2 : ENNReal) *
          ENNReal.ofReal
            (pureWZ2Prop62OrdinaryCardLogConstant *
              (1 + Real.log delta⁻¹)) := by
      gcongr
    _ =
        ENNReal.ofReal
          ((2 * pureWZ2Prop62OrdinaryCardLogConstant) *
            (1 + Real.log delta⁻¹)) := by
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    _ ≤ _ := rawAbsorption

/--
For fixed schedule depth and residue modulus, one common small-scale threshold
supplies both scalar gates in `CanonicalMetricMassRetentionBudget`.
-/
theorem exists_canonicalMetricMassRetentionBudget
    (depthBound strideBaseBound : ℕ) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta rho : ℝ},
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
          ∀ {ambientConstant scaleWindow : ENNReal},
            ∀ {schedule :
                PureWZ2Prop62PureSchedule
                  fine ambientConstant scaleWindow},
              ∀ {scheduled :
                  PureWZ2Prop62ScheduledParentColoringData schedule},
                ∀ {sourceConflict :
                    PureWZ2Prop62SourceConflictColoringData fine},
                  ∀ {width : ℝ},
                    ∀ {packetCoordinate : Fin schedule.levelCount},
                      ∀ {weight : Fin fine.card → ENNReal},
                        ∀ {preliminary :
                            PureWZ2Prop62AncestryPreliminarySelectionData
                              schedule scheduled rho width packetCoordinate
                              schedule.CanonicalColor
                              (schedule.canonicalColor
                                scheduled sourceConflict)
                              weight},
                          ∀ {M : ℝ},
                            ∀ (output :
                                PureWZ2Prop62AncestryMetricPreliminaryOutput
                                  schedule scheduled width packetCoordinate
                                  schedule.CanonicalColor
                                  (schedule.canonicalColor
                                    scheduled sourceConflict)
                                  weight preliminary M),
                              0 < delta →
                              delta ≤ delta₀ →
                              schedule.levelCount ≤ depthBound →
                              preliminary.residueStrideBase ≤
                                strideBaseBound →
                              HasBoundedBase fine 4 →
                              output.CanonicalMetricMassRetentionBudget := by
  let structural :=
    pureWZ2Prop62CanonicalStructuralBound
      depthBound strideBaseBound
  let coefficient : ℝ :=
    max structural.toReal
      (2 * pureWZ2Prop62OrdinaryCardLogConstant)
  have coefficientNonnegative : 0 ≤ coefficient := by
    exact ENNReal.toReal_nonneg.trans (le_max_left _ _)
  rcases
      exists_delta_boundary_log_square
        coefficient coefficientNonnegative
    with ⟨delta₀, delta₀Pos, delta₀LeOne, logarithmBound⟩
  refine ⟨delta₀, delta₀Pos, delta₀LeOne, ?_⟩
  intro delta rho fine ambientConstant scaleWindow schedule scheduled
    sourceConflict width packetCoordinate weight preliminary M output
    deltaPos deltaLe depthLe strideLe fineBoundedBase
  have logData :=
    logarithmBound delta deltaPos deltaLe
  have logIdentity :
      Real.log (1 / delta) = Real.log delta⁻¹ := by
    congr 1
    field_simp [deltaPos.ne']
  have logPositive : 0 < Real.log (1 / delta) := by
    rw [logIdentity]
    linarith [logData.1]
  have structuralFinite : structural ≠ ⊤ :=
    pureWZ2Prop62CanonicalStructuralBound_ne_top
      depthBound strideBaseBound
  have structuralRepresentation :
      structural = ENNReal.ofReal structural.toReal :=
    (ENNReal.ofReal_toReal structuralFinite).symm
  have structuralRealLe :
      structural.toReal ≤
        coefficient * (1 + Real.log delta⁻¹) := by
    calc
      structural.toReal ≤ coefficient :=
        le_max_left _ _
      _ ≤ coefficient * (1 + Real.log delta⁻¹) := by
        have logNonnegative : 0 ≤ Real.log delta⁻¹ := by
          linarith [logData.1]
        nlinarith
  have logSquareIdentity :
      ENNReal.ofReal ((Real.log delta⁻¹) ^ 2) =
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 := by
    rw [logIdentity]
    exact
      (ENNReal.ofReal_pow
        (show 0 ≤ Real.log delta⁻¹ by
          linarith [logData.1]) 2)
  have structuralBudget :
      output.canonicalStructuralMassLoss ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 := by
    calc
      output.canonicalStructuralMassLoss ≤ structural :=
        output.canonicalStructuralMassLoss_le depthLe strideLe
      _ = ENNReal.ofReal structural.toReal :=
        structuralRepresentation
      _ ≤
          ENNReal.ofReal
            (coefficient * (1 + Real.log delta⁻¹)) :=
        ENNReal.ofReal_mono structuralRealLe
      _ ≤ ENNReal.ofReal ((Real.log delta⁻¹) ^ 2) :=
        ENNReal.ofReal_mono logData.2
      _ = _ := logSquareIdentity
  have rawCoefficientLe :
      (2 * pureWZ2Prop62OrdinaryCardLogConstant) *
          (1 + Real.log delta⁻¹) ≤
        coefficient * (1 + Real.log delta⁻¹) := by
    exact
      mul_le_mul_of_nonneg_right
        (le_max_right _ _)
        (by linarith [logData.1])
  have rawAbsorption :
      ENNReal.ofReal
          ((2 * pureWZ2Prop62OrdinaryCardLogConstant) *
            (1 + Real.log delta⁻¹)) ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 := by
    calc
      ENNReal.ofReal
          ((2 * pureWZ2Prop62OrdinaryCardLogConstant) *
            (1 + Real.log delta⁻¹)) ≤
        ENNReal.ofReal
          (coefficient * (1 + Real.log delta⁻¹)) :=
        ENNReal.ofReal_mono rawCoefficientLe
      _ ≤ ENNReal.ofReal ((Real.log delta⁻¹) ^ 2) :=
        ENNReal.ofReal_mono logData.2
      _ = _ := logSquareIdentity
  have fineNonempty : fine.Nonempty := by
    rcases output.selectedPreliminary_nonempty with
      ⟨source, _sourceMem⟩
    exact Nat.zero_lt_of_lt
      (output.metric.mesh.complete.selectedFine.embedding source).isLt
  exact
    {
      logBase_pos := ENNReal.ofReal_pos.mpr logPositive
      structural := structuralBudget
      ambientDyadic :=
        ambientDyadic_le_logSquare_of_raw
          deltaPos (deltaLe.trans delta₀LeOne)
          fineNonempty schedule.fine_distinct
          fineBoundedBase rawAbsorption
    }

/-- Uniform small-scale threshold for the canonical metric-parent mass loss. -/
noncomputable def pureWZ2Prop62CanonicalMassThreshold
    (depthBound strideBaseBound : ℕ) : ℝ :=
  Classical.choose <|
    exists_canonicalMetricMassRetentionBudget
      depthBound strideBaseBound

theorem pureWZ2Prop62CanonicalMassThreshold_pos
    (depthBound strideBaseBound : ℕ) :
    0 <
      pureWZ2Prop62CanonicalMassThreshold
        depthBound strideBaseBound :=
  (Classical.choose_spec <|
    exists_canonicalMetricMassRetentionBudget
      depthBound strideBaseBound).1

theorem pureWZ2Prop62CanonicalMassThreshold_le_one
    (depthBound strideBaseBound : ℕ) :
    pureWZ2Prop62CanonicalMassThreshold
        depthBound strideBaseBound ≤ 1 :=
  (Classical.choose_spec <|
    exists_canonicalMetricMassRetentionBudget
      depthBound strideBaseBound).2.1

theorem canonicalMetricMassRetentionBudget_of_smallDelta
    (depthBound strideBaseBound : ℕ)
    (deltaPos : 0 < delta)
    (deltaLe :
      delta ≤
        pureWZ2Prop62CanonicalMassThreshold
          depthBound strideBaseBound)
    (depthLe : schedule.levelCount ≤ depthBound)
    (strideLe :
      preliminary.residueStrideBase ≤ strideBaseBound)
    (fineBoundedBase : HasBoundedBase fine 4) :
    output.CanonicalMetricMassRetentionBudget :=
  (Classical.choose_spec <|
    exists_canonicalMetricMassRetentionBudget
      depthBound strideBaseBound).2.2
    output deltaPos deltaLe depthLe strideLe fineBoundedBase

/--
Canonical metric-parent output below the uniform mass threshold.  No mass
retention premise or logarithmic budget is supplied by the caller.
-/
theorem metricParentsOutput_canonical_of_smallDelta
    (depthBound strideBaseBound : ℕ)
    (deltaPos : 0 < delta)
    (deltaLe :
      delta ≤
        pureWZ2Prop62CanonicalMassThreshold
          depthBound strideBaseBound)
    (depthLe : schedule.levelCount ≤ depthBound)
    (strideLe :
      preliminary.residueStrideBase ≤ strideBaseBound)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (actualScaleLeOne :
      ∀ coordinate, schedule.actualScale coordinate ≤ 1)
    (widthPos : 0 < width)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (scaleSeparation : 100 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.finalMetricRestriction.fineSelected.family.tube
          source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (fineBoundedBase : HasBoundedBase fine 4) :
    Nonempty
      (PureWZ2Prop62MetricParentsOutput
        (rho := rho) (schedule.scaleData packetCoordinate)
        weight 10) :=
  output.metricParentsOutput_canonical
    rhoPos rhoLeOne actualScaleLeOne widthPos
    packetScaleLtRho sixWidthLe
    allAncestryCoordinatesUpper scaleSeparation fineAxisBox
    fineBoundedBase
    (output.canonicalMetricMassRetentionBudget_of_smallDelta
      depthBound strideBaseBound deltaPos deltaLe
      depthLe strideLe fineBoundedBase)

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
