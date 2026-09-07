import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryLineConflictPacking

/-!
# Bounded source-family cardinality and logarithmic envelope

This low-level module isolates the six-parameter packing estimate needed by
the large-slope regularization chain.  It deliberately avoids importing the
Proposition 6.2 canonical schedule stack.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Absolute coefficient in the logarithmic bound for a bounded ordinary
essentially-distinct source family. -/
def pureWZ2BoundedSourceCardLogConstant : ℝ :=
  max
    (Real.log (2 * (643 : ℝ) ^ 6) / Real.log 2 + 1)
    (6 / Real.log 2)

/-- Convert the polynomial six-parameter cardinality estimate into a real
logarithmic bound. -/
theorem pureWZ2_bounded_source_card_log_bound
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    {cardinality : ℕ}
    (cardinalityPos : 0 < cardinality)
    (cardinalityBound :
      cardinality ≤
        (2 * Nat.ceil (320 / delta) + 1) ^ 6) :
    (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
      pureWZ2BoundedSourceCardLogConstant *
        (1 + Real.log delta⁻¹) := by
  have logTwoPos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  have logInvNonnegative : 0 ≤ Real.log delta⁻¹ := by
    apply Real.log_nonneg
    exact (one_le_inv₀ deltaPos).mpr deltaLeOne
  have constantFirst :
      Real.log (2 * (643 : ℝ) ^ 6) / Real.log 2 + 1 ≤
        pureWZ2BoundedSourceCardLogConstant :=
    le_max_left _ _
  have constantSecond :
      6 / Real.log 2 ≤
        pureWZ2BoundedSourceCardLogConstant :=
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
        pureWZ2BoundedSourceCardLogConstant +
          pureWZ2BoundedSourceCardLogConstant *
            Real.log delta⁻¹ := by
      gcongr
    _ =
        pureWZ2BoundedSourceCardLogConstant *
          (1 + Real.log delta⁻¹) := by
      ring

theorem pureWZ2_bounded_source_midpoint_norm_le_five
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (boundedBase : HasBoundedBase family 4)
    (source : Fin family.card) :
    ‖wz2PaperTubeMidpoint (family.tube source)‖ ≤ 5 := by
  dsimp only [wz2PaperTubeMidpoint]
  calc
    ‖(family.tube source).base +
        (1 / 2 : ℝ) • (family.tube source).direction‖ ≤
        ‖(family.tube source).base‖ +
          ‖(1 / 2 : ℝ) • (family.tube source).direction‖ :=
      norm_add_le _ _
    _ = ‖(family.tube source).base‖ + 1 / 2 := by
      rw [norm_smul, (family.tube source).direction_unit]
      norm_num
    _ ≤ 5 := by
      linarith [boundedBase source]

/-- A bounded-base ordinary essentially-distinct family has polynomial
cardinality at scale `delta`. -/
theorem pureWZ2_bounded_source_card_le
    {delta : ℝ}
    (deltaPos : 0 < delta)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (familyDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct family)
    (boundedBase : HasBoundedBase family 4) :
    family.card ≤ (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by
  let scaleCount := Nat.ceil (320 / delta)
  have raw :=
    wz2PaperOrdinary_local_six_grid_card_bound
      deltaPos (show (0 : ℝ) ≤ 5 by norm_num)
      familyDistinct Finset.univ (0 : Point3) <| by
        intro source _
        simpa [dist_zero_right] using
          pureWZ2_bounded_source_midpoint_norm_le_five
            (family := family) boundedBase source
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

/-- ENNReal bridge from the bounded-source cardinality estimate to the
log-square budget used by external-weight regularization. -/
theorem pureWZ2_bounded_source_ambient_dyadic_le_logSquare_of_raw
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (familyNonempty : family.Nonempty)
    (familyDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct family)
    (boundedBase : HasBoundedBase family 4)
    (rawAbsorption :
      ENNReal.ofReal
          ((2 * pureWZ2BoundedSourceCardLogConstant) *
            (1 + Real.log delta⁻¹)) ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2) :
    (2 * (Nat.log 2 (2 * family.card) + 1) : ENNReal) ≤
      (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 := by
  have rawCard :=
    pureWZ2_bounded_source_card_le
      deltaPos familyDistinct boundedBase
  have rawLog :=
    pureWZ2_bounded_source_card_log_bound
      deltaPos deltaLeOne familyNonempty rawCard
  have rawENN :
      (Nat.log 2 (2 * family.card) + 1 : ENNReal) ≤
        ENNReal.ofReal
          (pureWZ2BoundedSourceCardLogConstant *
            (1 + Real.log delta⁻¹)) := by
    have converted := ENNReal.ofReal_mono rawLog
    have castEq :
        ENNReal.ofReal
            (Nat.log 2 (2 * family.card) + 1 : ℝ) =
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) := by
      rw [ENNReal.ofReal_add (by positivity)]
      norm_num
      positivity
    rwa [castEq] at converted
  calc
    (2 * (Nat.log 2 (2 * family.card) + 1) : ENNReal) ≤
        (2 : ENNReal) *
          ENNReal.ofReal
            (pureWZ2BoundedSourceCardLogConstant *
              (1 + Real.log delta⁻¹)) := by
      gcongr
    _ =
        ENNReal.ofReal
          ((2 * pureWZ2BoundedSourceCardLogConstant) *
            (1 + Real.log delta⁻¹)) := by
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    _ ≤ _ := rawAbsorption

end Kakeya.Assouad

end
