import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyRegularizedNearbyCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantOneScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerCenterEnvelopeConflictDegree
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Uniform nearby-CWA schedule for one re-entrant hierarchy step

The synchronized post-grain selector pays only finite degree and
polylogarithmic regularization losses.  This module selects a scale cutoff
before the runtime family is known and absorbs those losses using the
six-parameter packing bound for an ordinary essentially-distinct family with
bounded basepoints.

This schedule is deliberately limited to the two CWA losses.  The later
ordinary-mass re-entry inequality also contains the actual ordinary density
and refinement fractions, so it remains a separate runtime scalar gate.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Fixed logarithmic coefficient for an ordinary family whose basepoints
lie in the radius-four ball. -/
def pureWZ2HierarchyOrdinaryCardLogConstant : ℝ :=
  max
    (Real.log (2 * (643 : ℝ) ^ 6) / Real.log 2 + 1)
    (6 / Real.log 2)

/-- Convert the six-dimensional polynomial packing bound into the uniform
logarithmic envelope used by the CWA selector. -/
theorem pureWZ2Hierarchy_ordinary_card_log_bound_of_raw
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    {cardinality : ℕ}
    (cardinalityPos : 0 < cardinality)
    (cardinalityBound :
      cardinality ≤
        (2 * Nat.ceil (320 / delta) + 1) ^ 6) :
    (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
      pureWZ2HierarchyOrdinaryCardLogConstant *
        (1 + Real.log delta⁻¹) := by
  have logTwoPos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  have logInvNonnegative : 0 ≤ Real.log delta⁻¹ := by
    apply Real.log_nonneg
    exact (one_le_inv₀ deltaPos).mpr deltaLeOne
  have constantFirst :
      Real.log (2 * (643 : ℝ) ^ 6) / Real.log 2 + 1 ≤
        pureWZ2HierarchyOrdinaryCardLogConstant :=
    le_max_left _ _
  have constantSecond :
      6 / Real.log 2 ≤ pureWZ2HierarchyOrdinaryCardLogConstant :=
    le_max_right _ _
  have doubleCardinalityPos : 0 < 2 * cardinality := by
    positivity
  have ceilLt :
      (Nat.ceil (320 / delta) : ℝ) < 320 / delta + 1 :=
    Nat.ceil_lt_add_one (by positivity)
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
            2 * (320 / delta + 1) + 1 := by gcongr
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
    have inversePower : delta ^ (-6 : ℝ) = (delta ^ 6)⁻¹ := by
      rw [Real.rpow_neg deltaPos.le]
      norm_cast
    rw [inversePower]
    field_simp [deltaPos.ne']
  have polynomialCardinality :
      ((2 * cardinality : ℕ) : ℝ) ≤
        (2 * (643 : ℝ) ^ 6) * delta ^ (-6 : ℝ) := by
    calc
      ((2 * cardinality : ℕ) : ℝ) = 2 * (cardinality : ℝ) := by
        norm_num
      _ ≤ 2 *
          (((2 * Nat.ceil (320 / delta) + 1 : ℕ) : ℝ) ^ 6) := by
        gcongr
      _ ≤ 2 * (643 / delta) ^ 6 := by gcongr
      _ = (2 * (643 : ℝ) ^ 6) * delta ^ (-6 : ℝ) := by
        rw [quotientPower]
        ring
  have natLog :
      (Nat.log 2 (2 * cardinality) : ℝ) ≤
        Real.log ((2 * cardinality : ℕ) : ℝ) / Real.log 2 := by
    have powerLe :
        (2 : ℕ) ^ Nat.log 2 (2 * cardinality) ≤ 2 * cardinality :=
      Nat.pow_log_le_self 2 doubleCardinalityPos.ne'
    have powerLeReal :
        (2 : ℝ) ^ Nat.log 2 (2 * cardinality) ≤
          ((2 * cardinality : ℕ) : ℝ) := by
      exact_mod_cast powerLe
    have logarithm := Real.log_le_log (by positivity) powerLeReal
    rw [Real.log_pow] at logarithm
    exact (le_div_iff₀ logTwoPos).mpr (by simpa using logarithm)
  have cardLog :
      Real.log ((2 * cardinality : ℕ) : ℝ) ≤
        Real.log ((2 * (643 : ℝ) ^ 6) * delta ^ (-6 : ℝ)) :=
    Real.log_le_log (by exact_mod_cast doubleCardinalityPos)
      polynomialCardinality
  have productLog :
      Real.log ((2 * (643 : ℝ) ^ 6) * delta ^ (-6 : ℝ)) =
        Real.log (2 * (643 : ℝ) ^ 6) + 6 * Real.log delta⁻¹ := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_rpow deltaPos (-6 : ℝ), Real.log_inv]
    ring
  calc
    (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
        Real.log ((2 * cardinality : ℕ) : ℝ) / Real.log 2 + 1 := by
      linarith
    _ ≤ Real.log ((2 * (643 : ℝ) ^ 6) * delta ^ (-6 : ℝ)) /
          Real.log 2 + 1 := by
      gcongr
    _ = (Real.log (2 * (643 : ℝ) ^ 6) / Real.log 2 + 1) +
          (6 / Real.log 2) * Real.log delta⁻¹ := by
      rw [productLog]
      field_simp [logTwoPos.ne']
      ring
    _ ≤ pureWZ2HierarchyOrdinaryCardLogConstant +
          pureWZ2HierarchyOrdinaryCardLogConstant * Real.log delta⁻¹ := by
      gcongr
    _ = pureWZ2HierarchyOrdinaryCardLogConstant *
          (1 + Real.log delta⁻¹) := by ring

/-- The logarithmic cardinality envelope available for every runtime family
in the re-entrant hierarchy. -/
theorem pureWZ2HierarchyReentrantOrdinary_card_log_bound
    {sigma inputLoss delta : ℝ}
    {normalizationExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent) :
    (Nat.log 2 (2 * current.grain.family.card) + 1 : ℝ) ≤
      pureWZ2HierarchyOrdinaryCardLogConstant *
        (1 + Real.log delta⁻¹) := by
  have rawCard :
      current.grain.family.card ≤
        (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by
    have raw :=
      wz2PaperOrdinary_local_six_grid_card_bound
        current.grain.extremal.delta_pos
        (show (0 : ℝ) ≤ 5 by norm_num)
        current.grain.extremal.cwa_nearby_scales.2.2.1
        Finset.univ (0 : Point3) <| by
          intro source _
          dsimp only [wz2PaperTubeMidpoint]
          calc
            ‖(current.grain.family.tube source).base +
                (1 / 2 : ℝ) •
                  (current.grain.family.tube source).direction - 0‖ =
                ‖(current.grain.family.tube source).base +
                  (1 / 2 : ℝ) •
                    (current.grain.family.tube source).direction‖ := by simp
            _ ≤ ‖(current.grain.family.tube source).base‖ +
                ‖(1 / 2 : ℝ) •
                  (current.grain.family.tube source).direction‖ :=
              norm_add_le _ _
            _ = ‖(current.grain.family.tube source).base‖ + 1 / 2 := by
              rw [norm_smul,
                (current.grain.family.tube source).direction_unit]
              norm_num
            _ ≤ 5 := by
              linarith [current.reentry.geometry.ordinary_bounded_base source]
    have firstArgument :
        5 / (delta / 64) = 320 / delta := by
      field_simp [current.grain.extremal.delta_pos.ne']
      norm_num
    have secondArgument :
        1 / (delta / 64) ≤ 320 / delta := by
      have identity : 1 / (delta / 64) = 64 / delta := by
        field_simp [current.grain.extremal.delta_pos.ne']
      rw [identity]
      exact div_le_div_of_nonneg_right (by norm_num)
        current.grain.extremal.delta_pos.le
    have firstCeil :
        Nat.ceil (5 / (delta / 64)) = Nat.ceil (320 / delta) := by
      rw [firstArgument]
    have secondCeil :
        Nat.ceil (1 / (delta / 64)) ≤ Nat.ceil (320 / delta) :=
      Nat.ceil_mono secondArgument
    simpa only [Finset.card_univ, Fintype.card_fin] using
      raw.trans <| by
        rw [firstCeil]
        calc
          (2 * Nat.ceil (320 / delta) + 1) ^ 3 *
                (2 * Nat.ceil (1 / (delta / 64)) + 1) ^ 3 ≤
              (2 * Nat.ceil (320 / delta) + 1) ^ 3 *
                (2 * Nat.ceil (320 / delta) + 1) ^ 3 := by
            gcongr
          _ = (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by ring
  exact
    pureWZ2Hierarchy_ordinary_card_log_bound_of_raw
      current.grain.extremal.delta_pos
      current.grain.extremal.delta_le_one
      current.grain.extremal.nonempty rawCard

/-- A cutoff chosen before the runtime family which absorbs exactly the
degree/restriction and cardinality losses of the weighted nearby-CWA
regularizer. -/
structure PureWZ2HierarchyNearbyCWASchedule
    (inputLoss densityLoss inputEta outputEta : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {cardinality : ℕ},
        (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
          pureWZ2HierarchyOrdinaryCardLogConstant *
            (1 + Real.log delta⁻¹) →
        wz2PaperPureNearbyRestrictionConstant
            (Kakeya.realRpowENN delta (-inputLoss))
            (Kakeya.realRpowENN delta inputEta *
              Kakeya.deltaTubeVolume delta)
            (pureWZ2SpatialCellDegreeConstant
              (densityLoss - inputLoss) cardinality)
            (pureWZ2SpatialCellRegularizationLoss
                (densityLoss - inputLoss) cardinality *
              Kakeya.deltaTubeVolume delta) ≤
          Kakeya.realRpowENN delta (-densityLoss) ∧
        Kakeya.realRpowENN delta outputEta *
            pureWZ2SpatialCellRegularizationLoss
              (densityLoss - inputLoss) cardinality ≤
          Kakeya.realRpowENN delta inputEta

/-- Choose the uniform CWA cutoff from the three honest positive exponent
gaps: positive rounding, room for the weighted restriction term, and room
for cardinality retention. -/
theorem exists_pureWZ2HierarchyNearbyCWASchedule
    {inputLoss densityLoss inputEta outputEta : ℝ}
    (densityLoss_pos : 0 < densityLoss)
    (input_loss_lt_density : inputLoss < densityLoss)
    (restriction_gap_pos :
      0 < densityLoss - inputEta - 2 * inputLoss)
    (cardinality_gap_pos : 0 < outputEta - inputEta) :
    Nonempty (PureWZ2HierarchyNearbyCWASchedule
      inputLoss densityLoss inputEta outputEta) := by
  let epsilon : ℝ := densityLoss - inputLoss
  let levelCount : ℕ := geometricScaleCount epsilon
  let logCoefficient : ℝ := pureWZ2HierarchyOrdinaryCardLogConstant
  let degreeCoefficient : ENNReal :=
    16 * (levelCount : ENNReal)
  let restrictionCoefficient : ENNReal :=
    128 * (levelCount : ENNReal)
  have epsilon_pos : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  have levelCount_pos : 0 < levelCount := by
    dsimp only [levelCount, geometricScaleCount]
    omega
  have logCoefficient_nonneg : 0 ≤ logCoefficient := by
    dsimp only [logCoefficient, pureWZ2HierarchyOrdinaryCardLogConstant]
    positivity
  have degreeCoefficient_top : degreeCoefficient ≠ ⊤ := by
    dsimp only [degreeCoefficient]
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)
  have restrictionCoefficient_top : restrictionCoefficient ≠ ⊤ := by
    dsimp only [restrictionCoefficient]
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)
  rcases exists_delta_C_pow_log_absorbed_ennreal
      degreeCoefficient degreeCoefficient_top
      logCoefficient logCoefficient_nonneg densityLoss_pos levelCount_pos with
    ⟨degreeDelta, degreeDelta_pos, degreeDelta_one, degreeBound⟩
  rcases exists_delta_C_pow_log_absorbed_ennreal
      restrictionCoefficient restrictionCoefficient_top
      logCoefficient logCoefficient_nonneg restriction_gap_pos
      (show 0 < 2 * levelCount + 1 by omega) with
    ⟨restrictionDelta, restrictionDelta_pos, restrictionDelta_one,
      restrictionBound⟩
  rcases exists_delta_C_pow_log_absorbed_ennreal
      (8 : ENNReal) (by norm_num)
      logCoefficient logCoefficient_nonneg cardinality_gap_pos
      (show 0 < levelCount + 1 by omega) with
    ⟨cardinalityDelta, cardinalityDelta_pos, cardinalityDelta_one,
      cardinalityBound⟩
  let delta₀ := min degreeDelta (min restrictionDelta cardinalityDelta)
  have delta₀_pos : 0 < delta₀ :=
    lt_min degreeDelta_pos
      (lt_min restrictionDelta_pos cardinalityDelta_pos)
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := delta₀_pos
    delta₀_le_one := (min_le_left _ _).trans degreeDelta_one
    absorb := ?_
  }⟩
  intro delta delta_pos delta_le cardinality cardLogReal
  have delta_one : delta ≤ 1 :=
    delta_le.trans ((min_le_left _ _).trans degreeDelta_one)
  let logTerm : ENNReal :=
    (Nat.log 2 (2 * cardinality) + 1 : ENNReal)
  let envelope : ENNReal :=
    ENNReal.ofReal
      (logCoefficient * (1 + Real.log delta⁻¹))
  have logTerm_le : logTerm ≤ envelope := by
    have converted := ENNReal.ofReal_mono cardLogReal
    have castEq :
        ENNReal.ofReal
            (Nat.log 2 (2 * cardinality) + 1 : ℝ) =
          (Nat.log 2 (2 * cardinality) + 1 : ENNReal) := by
      rw [ENNReal.ofReal_add (by positivity)]
      norm_num
      positivity
    simpa [logTerm, envelope, logCoefficient, castEq] using converted
  have degreeAbsolute :
      degreeCoefficient * envelope ^ levelCount ≤
        Kakeya.realRpowENN delta (-densityLoss) :=
    degreeBound delta delta_pos
      (delta_le.trans <| min_le_left _ _)
  have restrictionAbsolute :
      restrictionCoefficient * envelope ^ (2 * levelCount + 1) ≤
        Kakeya.realRpowENN delta
          (-(densityLoss - inputEta - 2 * inputLoss)) :=
    restrictionBound delta delta_pos
      (delta_le.trans <| (min_le_right _ _).trans (min_le_left _ _))
  have cardinalityAbsolute :
      (8 : ENNReal) * envelope ^ (levelCount + 1) ≤
        Kakeya.realRpowENN delta (-(outputEta - inputEta)) :=
    cardinalityBound delta delta_pos
      (delta_le.trans <| (min_le_right _ _).trans (min_le_right _ _))
  let ambientConstant := Kakeya.realRpowENN delta (-inputLoss)
  let densityWeight := Kakeya.realRpowENN delta inputEta
  let tubeVolume := Kakeya.deltaTubeVolume delta
  let degreeConstant :=
    pureWZ2SpatialCellDegreeConstant epsilon cardinality
  let regularizationLoss :=
    pureWZ2SpatialCellRegularizationLoss epsilon cardinality
  have tubeVolume_pos : 0 < tubeVolume :=
    (tube_volume_scaling.2.1 delta delta_pos delta_one).1
  have tubeVolume_top : tubeVolume ≠ ⊤ :=
    (tube_volume_scaling.2.1 delta delta_pos delta_one).2
  have densityWeight_zero : densityWeight ≠ 0 := by
    dsimp only [densityWeight, Kakeya.realRpowENN]
    exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos delta_pos inputEta)).ne'
  have densityWeight_top : densityWeight ≠ ⊤ := by
    simp [densityWeight, Kakeya.realRpowENN]
  have ambient_le :
      ambientConstant ≤ Kakeya.realRpowENN delta (-densityLoss) := by
    dsimp only [ambientConstant]
    exact pure_wz2_rpowENN_antitone delta_pos delta_one (by linarith)
  have degree_le :
      degreeConstant ≤ Kakeya.realRpowENN delta (-densityLoss) := by
    calc
      degreeConstant = degreeCoefficient * logTerm ^ levelCount := by
        simp [degreeConstant, degreeCoefficient, levelCount, epsilon,
          pureWZ2SpatialCellDegreeConstant, logTerm]
      _ ≤ degreeCoefficient * envelope ^ levelCount := by gcongr
      _ ≤ Kakeya.realRpowENN delta (-densityLoss) := degreeAbsolute
  have regularization_le :
      regularizationLoss ≤
        Kakeya.realRpowENN delta (-(outputEta - inputEta)) := by
    calc
      regularizationLoss =
          (8 : ENNReal) * logTerm ^ (levelCount + 1) := by
        simp [regularizationLoss, levelCount, epsilon,
          pureWZ2SpatialCellRegularizationLoss, logTerm]
      _ ≤ (8 : ENNReal) * envelope ^ (levelCount + 1) := by gcongr
      _ ≤ Kakeya.realRpowENN delta (-(outputEta - inputEta)) :=
        cardinalityAbsolute
  have secondTermEq :
      (((densityWeight * tubeVolume)⁻¹ *
          (ambientConstant * (regularizationLoss * tubeVolume) *
            degreeConstant)) * ambientConstant) =
        (restrictionCoefficient *
            logTerm ^ (2 * levelCount + 1)) *
          Kakeya.realRpowENN delta
            (-(inputEta + 2 * inputLoss)) := by
    have densityInv : densityWeight⁻¹ =
        Kakeya.realRpowENN delta (-inputEta) := by
      dsimp only [densityWeight]
      exact pure_wz2_realRpowENN_inv delta_pos
    have volumeCancel : tubeVolume⁻¹ * tubeVolume = 1 :=
      ENNReal.inv_mul_cancel tubeVolume_pos.ne' tubeVolume_top
    have ambientSquared : ambientConstant * ambientConstant =
        Kakeya.realRpowENN delta (-2 * inputLoss) := by
      dsimp only [ambientConstant]
      rw [← realRpowENN_add delta_pos]
      congr 2
      ring
    have powerProduct :
        Kakeya.realRpowENN delta (-inputEta) *
            Kakeya.realRpowENN delta (-2 * inputLoss) =
          Kakeya.realRpowENN delta (-(inputEta + 2 * inputLoss)) := by
      rw [← realRpowENN_add delta_pos]
      congr 2
      ring
    rw [ENNReal.mul_inv]
    · rw [densityInv]
      change
        (Kakeya.realRpowENN delta (-inputEta) * tubeVolume⁻¹ *
            (ambientConstant * (regularizationLoss * tubeVolume) *
              degreeConstant)) * ambientConstant = _
      rw [show
          Kakeya.realRpowENN delta (-inputEta) * tubeVolume⁻¹ *
                (ambientConstant * (regularizationLoss * tubeVolume) *
                  degreeConstant) * ambientConstant =
              (tubeVolume⁻¹ * tubeVolume) *
                (Kakeya.realRpowENN delta (-inputEta) *
                  (ambientConstant * ambientConstant) *
                  (regularizationLoss * degreeConstant)) by ring]
      rw [volumeCancel, one_mul, ambientSquared, powerProduct]
      dsimp only [regularizationLoss, degreeConstant,
        pureWZ2SpatialCellRegularizationLoss,
        pureWZ2SpatialCellDegreeConstant, levelCount, epsilon, logTerm,
        restrictionCoefficient]
      ring
    · exact Or.inl densityWeight_zero
    · exact Or.inl densityWeight_top
  have secondTerm_le :
      (((densityWeight * tubeVolume)⁻¹ *
          (ambientConstant * (regularizationLoss * tubeVolume) *
            degreeConstant)) * ambientConstant) ≤
        Kakeya.realRpowENN delta (-densityLoss) := by
    rw [secondTermEq]
    calc
      (restrictionCoefficient *
            logTerm ^ (2 * levelCount + 1)) *
          Kakeya.realRpowENN delta (-(inputEta + 2 * inputLoss)) ≤
        (restrictionCoefficient *
            envelope ^ (2 * levelCount + 1)) *
          Kakeya.realRpowENN delta (-(inputEta + 2 * inputLoss)) := by
            gcongr
      _ ≤ Kakeya.realRpowENN delta
            (-(densityLoss - inputEta - 2 * inputLoss)) *
          Kakeya.realRpowENN delta (-(inputEta + 2 * inputLoss)) := by
            gcongr
      _ = Kakeya.realRpowENN delta (-densityLoss) := by
        rw [← realRpowENN_add delta_pos]
        congr 2
        ring
  constructor
  · change max ambientConstant (max degreeConstant
      (((densityWeight * tubeVolume)⁻¹ *
          (ambientConstant * (regularizationLoss * tubeVolume) *
            degreeConstant)) * ambientConstant)) ≤ _
    exact max_le ambient_le (max_le degree_le secondTerm_le)
  · change Kakeya.realRpowENN delta outputEta * regularizationLoss ≤
      Kakeya.realRpowENN delta inputEta
    calc
      Kakeya.realRpowENN delta outputEta * regularizationLoss ≤
          Kakeya.realRpowENN delta outputEta *
            Kakeya.realRpowENN delta (-(outputEta - inputEta)) := by
        gcongr
      _ = Kakeya.realRpowENN delta inputEta := by
        rw [← realRpowENN_add delta_pos]
        congr 2
        ring

namespace PureWZ2HierarchyNearbyCWASchedule

variable {inputLoss densityLoss inputEta outputEta : ℝ}
    (schedule : PureWZ2HierarchyNearbyCWASchedule
      inputLoss densityLoss inputEta outputEta)

/-- Apply the preselected cutoff to the exact runtime hierarchy family. -/
theorem absorb_current
    {sigma delta : ℝ}
    {normalizationExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent)
    (delta_le : delta ≤ schedule.delta₀) :
    wz2PaperPureNearbyRestrictionConstant
        (Kakeya.realRpowENN delta (-inputLoss))
        (Kakeya.realRpowENN delta inputEta *
          Kakeya.deltaTubeVolume delta)
        (pureWZ2SpatialCellDegreeConstant
          (densityLoss - inputLoss) current.grain.family.card)
        (pureWZ2SpatialCellRegularizationLoss
            (densityLoss - inputLoss) current.grain.family.card *
          Kakeya.deltaTubeVolume delta) ≤
      Kakeya.realRpowENN delta (-densityLoss) ∧
    Kakeya.realRpowENN delta outputEta *
        pureWZ2SpatialCellRegularizationLoss
          (densityLoss - inputLoss) current.grain.family.card ≤
      Kakeya.realRpowENN delta inputEta :=
  schedule.absorb current.grain.extremal.delta_pos delta_le
    (pureWZ2HierarchyReentrantOrdinary_card_log_bound current)

end PureWZ2HierarchyNearbyCWASchedule

end Kakeya.Assouad

end
