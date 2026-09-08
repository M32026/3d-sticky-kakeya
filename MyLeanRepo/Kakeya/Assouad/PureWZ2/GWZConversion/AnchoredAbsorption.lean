import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AnchoredNearbyAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FixedBallCardLog
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ExponentInequality
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Quantitative absorption for the reanchored Node 9 route

All geometric and combinatorial losses are explicit fixed constants times a
fixed power of `log(1/delta)`.  This module absorbs them into the requested
output power before the source family is quantified.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Fixed color-vector coefficient in the simultaneous selection loss. -/
def pureWZ2AnchoredColorCoefficient
    (A : ℝ) (coordinateCount : ℕ) : ENNReal :=
  (Fintype.card
    (Fin coordinateCount →
      Fin (pureWZ2AnchoredCoarseConflictDegree A + 1)) :
      ENNReal) * 8

/-- Fixed owner-degree coefficient. -/
def pureWZ2AnchoredDegreeCoefficient
    (coordinateCount : ℕ) : ENNReal :=
  16 * (coordinateCount : ENNReal)

/-- Fixed localization and fine-distinctness loss. -/
def pureWZ2AnchoredLocalizationCoefficient
    (R radius : ℝ) : ENNReal :=
  (pureWZ2LocalizationCellCount R radius : ENNReal) *
    (pureWZ2ReanchoredPaperConflictLossBound : ENNReal)

/-- Fixed coefficient dominating the raw selected shaded-mass loss. -/
def pureWZ2AnchoredMassCoefficient
    (A R radius : ℝ) (coordinateCount : ℕ) : ENNReal :=
  pureWZ2AnchoredLocalizationCoefficient R radius *
    pureWZ2AnchoredColorCoefficient A coordinateCount

/-- Fixed coefficient dominating both small- and top-scale CWA constants. -/
def pureWZ2AnchoredCWACoefficient
    (A R radius : ℝ) (coordinateCount : ℕ) : ENNReal :=
  let localization :=
    pureWZ2AnchoredLocalizationCoefficient R radius
  let color :=
    pureWZ2AnchoredColorCoefficient A coordinateCount
  let degree :=
    pureWZ2AnchoredDegreeCoefficient coordinateCount
  let small :=
    27 * 212776173 * 1280 *
      (pureWZ2CompleteFiberOverlapBound A : ENNReal) *
      localization * color * degree
  let top :=
    27 * 212776173 * 1280 *
      (pureWZ2UnitScaleCompleteFiberOverlapBound A : ENNReal) *
      localization * color
  max 1 (max degree (max small top))

/-- A finite constant is eventually below `log(1/delta)`. -/
theorem pureWZ2_fixed_below_log
    (constant : ENNReal)
    (constant_ne_top : constant ≠ ⊤) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        constant ≤ ENNReal.ofReal (Real.log (1 / delta)) := by
  let constantReal := constant.toReal
  let delta₀ := min (Real.exp (-constantReal)) (Real.exp (-1))
  have hdelta₀ : 0 < delta₀ := by positivity
  have hdelta₀One : delta₀ ≤ 1 := by
    exact (min_le_right _ _).trans
      (Real.exp_lt_one_iff.mpr (by norm_num)).le
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hsmall
  have hdeltaConstant :
      delta ≤ Real.exp (-constantReal) :=
    hsmall.trans (min_le_left _ _)
  have hlogDelta :
      Real.log delta ≤ -constantReal := by
    have :=
      Real.log_le_log hdelta hdeltaConstant
    simpa using this
  have hlogInv :
      constantReal ≤ Real.log (1 / delta) := by
    rw [Real.log_div (by norm_num) hdelta.ne', Real.log_one]
    linarith
  rw [← ENNReal.ofReal_toReal constant_ne_top]
  exact ENNReal.ofReal_mono hlogInv

/--
Absorption package used by the final Node 9 assembly.
-/
theorem pureWZ2_anchored_absorption
    (A R radius outputLoss inputLoss : ℝ)
    (hA : 1 ≤ A)
    (hR : 1 ≤ R)
    (hradius : 0 < radius)
    (houtputLoss : 0 < outputLoss)
    (hinputLoss : 0 < inputLoss)
    (htriple : 3 * inputLoss < outputLoss)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount) :
    let logExponent := coordinateCount + 2
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ familyCard : ℕ,
          ((Nat.log 2 (2 * familyCard) + 1 : ℝ) ≤
            pureWZ2FixedBallCardLogConstant R *
              (1 + Real.log delta⁻¹)) →
          let inputConstant :=
            Kakeya.realRpowENN delta (-inputLoss)
          let density :=
            Kakeya.realRpowENN delta inputLoss
          let selectionRetention :=
            pureWZ2FiniteAnchoredRetentionConstant
              A coordinateCount familyCard
          let degreeConstant :=
            pureWZ2FiniteAnchoredDegreeConstant
              coordinateCount familyCard
          let globalRetention :=
            pureWZ2ReanchoredGlobalRetentionConstant
              density
              (pureWZ2LocalizationCellCount R radius)
              pureWZ2ReanchoredPaperConflictLossBound
              selectionRetention
          let fiberRatio :=
            pureWZ2ReanchoredFiberRatioConstant
              inputConstant
              (pureWZ2CompleteFiberOverlapBound A)
              globalRetention degreeConstant
          pureWZ2AnchoredReferenceScaleConstant
              degreeConstant inputConstant fiberRatio ≤
            Kakeya.realRpowENN delta (-outputLoss) ∧
          pureWZ2TopScaleConstant
              inputConstant
              (pureWZ2UnitScaleCompleteFiberOverlapBound A)
              globalRetention ≤
            Kakeya.realRpowENN delta (-outputLoss) ∧
          ((pureWZ2LocalizationCellCount R radius : ENNReal) *
              (pureWZ2ReanchoredPaperConflictLossBound : ENNReal) *
              selectionRetention) ≤
            (ENNReal.ofReal (Real.log (1 / delta))) ^ logExponent := by
  dsimp only
  let logExponent := coordinateCount + 2
  let polylogPower := 2 * coordinateCount + 2
  let gap := outputLoss - 3 * inputLoss
  have hgap : 0 < gap := by
    dsimp only [gap]
    linarith
  let cwaCoefficient :=
    pureWZ2AnchoredCWACoefficient
      A R radius coordinateCount
  have hlocalizationFinite :
      pureWZ2AnchoredLocalizationCoefficient R radius ≠ ⊤ := by
    dsimp only [pureWZ2AnchoredLocalizationCoefficient]
    exact ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top _)
      (ENNReal.natCast_ne_top _)
  have hcolorFinite :
      pureWZ2AnchoredColorCoefficient A coordinateCount ≠ ⊤ := by
    dsimp only [pureWZ2AnchoredColorCoefficient]
    exact ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top _) (by norm_num)
  have hdegreeFinite :
      pureWZ2AnchoredDegreeCoefficient coordinateCount ≠ ⊤ := by
    dsimp only [pureWZ2AnchoredDegreeCoefficient]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.natCast_ne_top _)
  have hsmallFinite :
      27 * 212776173 * 1280 *
            (pureWZ2CompleteFiberOverlapBound A : ENNReal) *
            pureWZ2AnchoredLocalizationCoefficient R radius *
            pureWZ2AnchoredColorCoefficient A coordinateCount *
            pureWZ2AnchoredDegreeCoefficient coordinateCount ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top
              (ENNReal.mul_ne_top (by norm_num) (by norm_num))
              (by norm_num))
            (ENNReal.natCast_ne_top _))
          hlocalizationFinite)
        hcolorFinite)
      hdegreeFinite
  have htopFinite :
      27 * 212776173 * 1280 *
            (pureWZ2UnitScaleCompleteFiberOverlapBound A : ENNReal) *
            pureWZ2AnchoredLocalizationCoefficient R radius *
            pureWZ2AnchoredColorCoefficient A coordinateCount ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top (by norm_num) (by norm_num))
            (by norm_num))
          (ENNReal.natCast_ne_top _))
        hlocalizationFinite)
      hcolorFinite
  have hcwaFinite : cwaCoefficient ≠ ⊤ := by
    dsimp only [cwaCoefficient,
      pureWZ2AnchoredCWACoefficient]
    exact max_ne_top ENNReal.one_ne_top
      (max_ne_top hdegreeFinite
        (max_ne_top hsmallFinite htopFinite))
  have hlogCoefficientNonnegative :
      0 ≤ pureWZ2FixedBallCardLogConstant R := by
    dsimp only [pureWZ2FixedBallCardLogConstant]
    exact le_max_of_le_right (by positivity)
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        (n := polylogPower)
        cwaCoefficient hcwaFinite
        (pureWZ2FixedBallCardLogConstant R)
        hlogCoefficientNonnegative hgap
        (by dsimp only [polylogPower]; omega) with
    ⟨deltaCWA, hdeltaCWA, hdeltaCWAOne, hcwaAbsorb⟩
  let massExtra :=
    pureWZ2AnchoredMassCoefficient A R radius coordinateCount *
      (ENNReal.ofReal
        (2 * pureWZ2FixedBallCardLogConstant R)) ^
          (coordinateCount + 1)
  have hmassExtraFinite : massExtra ≠ ⊤ := by
    dsimp only [massExtra,
      pureWZ2AnchoredMassCoefficient]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hlocalizationFinite hcolorFinite)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  rcases pureWZ2_fixed_below_log massExtra hmassExtraFinite with
    ⟨deltaMass, hdeltaMass, hdeltaMassOne, hmassAbsorb⟩
  let delta₀ :=
    min (1 / 200)
      (min (Real.exp (-1)) (min deltaCWA deltaMass))
  have hdelta₀ : 0 < delta₀ := by positivity
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans (by norm_num)
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hsmall familyCard hcardLog
  have hdeltaOne : delta ≤ 1 :=
    hsmall.trans hdelta₀One
  have hdeltaCWA' : delta ≤ deltaCWA :=
    hsmall.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaMass' : delta ≤ deltaMass :=
    hsmall.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
  have hdeltaExp : delta ≤ Real.exp (-1) :=
    hsmall.trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  let logTerm : ENNReal :=
    (Nat.log 2 (2 * familyCard) + 1 : ENNReal)
  let logBound : ENNReal :=
    ENNReal.ofReal
      (pureWZ2FixedBallCardLogConstant R *
        (1 + Real.log delta⁻¹))
  have hlogTerm : logTerm ≤ logBound := by
    have hrepresentation :
        logTerm =
          ENNReal.ofReal
            ((Nat.log 2 (2 * familyCard) + 1 : ℝ)) := by
      dsimp only [logTerm]
      norm_cast
    rw [hrepresentation]
    exact ENNReal.ofReal_mono hcardLog
  let inputConstant :=
    Kakeya.realRpowENN delta (-inputLoss)
  let density :=
    Kakeya.realRpowENN delta inputLoss
  have hdensityInverse :
      density⁻¹ = inputConstant := by
    dsimp only [density, inputConstant, Kakeya.realRpowENN]
    have hpower : 0 < Real.rpow delta inputLoss :=
      Real.rpow_pos_of_pos hdelta _
    calc
      (ENNReal.ofReal (Real.rpow delta inputLoss))⁻¹ =
          ENNReal.ofReal
            ((Real.rpow delta inputLoss)⁻¹) :=
        (ENNReal.ofReal_inv_of_pos hpower).symm
      _ = ENNReal.ofReal
          (Real.rpow delta (-inputLoss)) := by
        congr 1
        exact (Real.rpow_neg hdelta.le inputLoss).symm
  have hinputOne : 1 ≤ inputConstant := by
    dsimp only [inputConstant, Kakeya.realRpowENN]
    have hreal :
        1 ≤ Real.rpow delta (-inputLoss) := by
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        hdelta hdeltaOne (by linarith)
    simpa using ENNReal.ofReal_mono hreal
  have hlogOne : 1 ≤ logBound := by
    have hlogInv : 1 ≤ Real.log delta⁻¹ := by
      have hlogDelta :
          Real.log delta ≤ -1 := by
        have :=
          Real.log_le_log hdelta
            (hsmall.trans <|
              (min_le_right _ _).trans (min_le_left _ _))
        simpa using this
      rw [Real.log_inv]
      linarith
    have hcoefficient :
        1 ≤ pureWZ2FixedBallCardLogConstant R := by
      dsimp only [pureWZ2FixedBallCardLogConstant]
      apply le_max_of_le_left
      have hbase : (1 : ℝ) ≤ 37 * R := by
        nlinarith
      have hpow : (1 : ℝ) ≤ (37 * R) ^ 6 :=
        one_le_pow₀ hbase
      have hargument :
          (1 : ℝ) < 2 * (37 * R) ^ 6 := by
        nlinarith
      have hlogPositive :
          0 < Real.log (2 * (37 * R) ^ 6) := by
        exact Real.log_pos hargument
      have hlogTwo : 0 < Real.log 2 :=
        Real.log_pos (by norm_num)
      have hquotNonnegative :
          0 ≤
            Real.log (2 * (37 * R) ^ 6) /
              Real.log 2 :=
        div_nonneg hlogPositive.le hlogTwo.le
      linarith
    have hreal :
        1 ≤ pureWZ2FixedBallCardLogConstant R *
          (1 + Real.log delta⁻¹) := by
      nlinarith
    dsimp only [logBound]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_mono hreal
  let selectionRetention :=
    pureWZ2FiniteAnchoredRetentionConstant
      A coordinateCount familyCard
  let degreeConstant :=
    pureWZ2FiniteAnchoredDegreeConstant
      coordinateCount familyCard
  let globalRetention :=
    pureWZ2ReanchoredGlobalRetentionConstant
      density
      (pureWZ2LocalizationCellCount R radius)
      pureWZ2ReanchoredPaperConflictLossBound
      selectionRetention
  let fiberRatio :=
    pureWZ2ReanchoredFiberRatioConstant
      inputConstant
      (pureWZ2CompleteFiberOverlapBound A)
      globalRetention degreeConstant
  have hselectionRetention :
      selectionRetention ≤
        pureWZ2AnchoredColorCoefficient A coordinateCount *
          logBound ^ (coordinateCount + 1) := by
    calc
      selectionRetention =
          pureWZ2AnchoredColorCoefficient A coordinateCount *
            logTerm ^ (coordinateCount + 1) := by
        rfl
      _ ≤
          pureWZ2AnchoredColorCoefficient A coordinateCount *
            logBound ^ (coordinateCount + 1) := by
        exact mul_le_mul_left'
          (pow_le_pow_left' hlogTerm _) _
  have hdegree :
      degreeConstant ≤
        pureWZ2AnchoredDegreeCoefficient coordinateCount *
          logBound ^ coordinateCount := by
    calc
      degreeConstant =
          pureWZ2AnchoredDegreeCoefficient coordinateCount *
            logTerm ^ coordinateCount := by
        rfl
      _ ≤
          pureWZ2AnchoredDegreeCoefficient coordinateCount *
            logBound ^ coordinateCount := by
        exact mul_le_mul_left'
          (pow_le_pow_left' hlogTerm _) _
  have hglobal :
      globalRetention ≤
        inputConstant *
          (pureWZ2AnchoredLocalizationCoefficient R radius *
            pureWZ2AnchoredColorCoefficient A coordinateCount) *
          logBound ^ (coordinateCount + 1) := by
    calc
      globalRetention =
          inputConstant *
            pureWZ2AnchoredLocalizationCoefficient R radius *
            selectionRetention := by
        dsimp only [globalRetention,
          pureWZ2ReanchoredGlobalRetentionConstant,
          pureWZ2AnchoredLocalizationCoefficient]
        rw [hdensityInverse]
        ring
      _ ≤
          inputConstant *
            pureWZ2AnchoredLocalizationCoefficient R radius *
            (pureWZ2AnchoredColorCoefficient A coordinateCount *
              logBound ^ (coordinateCount + 1)) := by
        simpa [mul_assoc] using
          mul_le_mul_left' hselectionRetention
            (inputConstant *
              pureWZ2AnchoredLocalizationCoefficient R radius)
      _ = _ := by ring
  have hfiber :
      fiberRatio ≤
        ((pureWZ2CompleteFiberOverlapBound A : ENNReal) *
          pureWZ2AnchoredLocalizationCoefficient R radius *
          pureWZ2AnchoredColorCoefficient A coordinateCount *
          pureWZ2AnchoredDegreeCoefficient coordinateCount) *
          inputConstant ^ 2 *
          logBound ^ (2 * coordinateCount + 1) := by
    dsimp only [fiberRatio,
      pureWZ2ReanchoredFiberRatioConstant]
    calc
      inputConstant *
            ((pureWZ2CompleteFiberOverlapBound A : ENNReal) *
              globalRetention) *
            degreeConstant
          ≤
        inputConstant *
            ((pureWZ2CompleteFiberOverlapBound A : ENNReal) *
              (inputConstant *
              (pureWZ2AnchoredLocalizationCoefficient R radius *
                pureWZ2AnchoredColorCoefficient A coordinateCount) *
              logBound ^ (coordinateCount + 1))) *
            (pureWZ2AnchoredDegreeCoefficient coordinateCount *
              logBound ^ coordinateCount) := by
        exact mul_le_mul
          (mul_le_mul_left'
            (mul_le_mul_left' hglobal _) _)
          hdegree (by positivity) (by positivity)
      _ =
          ((pureWZ2CompleteFiberOverlapBound A : ENNReal) *
            pureWZ2AnchoredLocalizationCoefficient R radius *
            pureWZ2AnchoredColorCoefficient A coordinateCount *
            pureWZ2AnchoredDegreeCoefficient coordinateCount) *
            inputConstant ^ 2 *
            (logBound ^ (coordinateCount + 1) *
              logBound ^ coordinateCount) := by
        ring
      _ = _ := by
        rw [show
          logBound ^ (coordinateCount + 1) *
              logBound ^ coordinateCount =
            logBound ^ (2 * coordinateCount + 1) by
              rw [← pow_add]
              congr 1
              omega]
  have hcwaRaw :
      pureWZ2AnchoredReferenceScaleConstant
          degreeConstant inputConstant fiberRatio ≤
        cwaCoefficient * inputConstant ^ 3 *
          logBound ^ polylogPower := by
    apply max_le
    · calc
        degreeConstant ≤
            pureWZ2AnchoredDegreeCoefficient coordinateCount *
              logBound ^ coordinateCount := hdegree
        _ ≤ cwaCoefficient * logBound ^ coordinateCount := by
          exact mul_le_mul_right'
            (show
              pureWZ2AnchoredDegreeCoefficient coordinateCount ≤
                cwaCoefficient by
              dsimp only [cwaCoefficient,
                pureWZ2AnchoredCWACoefficient]
              exact le_max_of_le_right (le_max_left _ _)) _
        _ ≤ cwaCoefficient *
              logBound ^ polylogPower := by
          exact mul_le_mul_left'
            (pow_le_pow_right₀ hlogOne
              (by dsimp only [polylogPower]; omega)) _
        _ ≤ cwaCoefficient * inputConstant ^ 3 *
              logBound ^ polylogPower := by
          have hcube : 1 ≤ inputConstant ^ 3 :=
            one_le_pow₀ hinputOne
          calc
            cwaCoefficient * logBound ^ polylogPower =
                cwaCoefficient * 1 *
                  logBound ^ polylogPower := by ring
            _ ≤ cwaCoefficient * inputConstant ^ 3 *
                  logBound ^ polylogPower := by
              exact mul_le_mul_right'
                (mul_le_mul_left' hcube _) _
    · dsimp only [pureWZ2ReanchoredStrictFrostmanConstant]
      calc
        27 * (212776173 * inputConstant * fiberRatio * 1280)
            ≤
          27 * (212776173 * inputConstant *
            (((pureWZ2CompleteFiberOverlapBound A : ENNReal) *
              pureWZ2AnchoredLocalizationCoefficient R radius *
              pureWZ2AnchoredColorCoefficient A coordinateCount *
              pureWZ2AnchoredDegreeCoefficient coordinateCount) *
              inputConstant ^ 2 *
              logBound ^ (2 * coordinateCount + 1)) * 1280) := by
            gcongr
        _ =
          (27 * 212776173 * 1280 *
            (pureWZ2CompleteFiberOverlapBound A : ENNReal) *
            pureWZ2AnchoredLocalizationCoefficient R radius *
            pureWZ2AnchoredColorCoefficient A coordinateCount *
            pureWZ2AnchoredDegreeCoefficient coordinateCount) *
            inputConstant ^ 3 *
            logBound ^ (2 * coordinateCount + 1) := by
          ring
        _ ≤ cwaCoefficient * inputConstant ^ 3 *
              logBound ^ (2 * coordinateCount + 1) := by
          exact mul_le_mul_right'
            (mul_le_mul_right'
              (show
                27 * 212776173 * 1280 *
                    (pureWZ2CompleteFiberOverlapBound A : ENNReal) *
                    pureWZ2AnchoredLocalizationCoefficient R radius *
                    pureWZ2AnchoredColorCoefficient A coordinateCount *
                    pureWZ2AnchoredDegreeCoefficient coordinateCount ≤
                  cwaCoefficient by
                dsimp only [cwaCoefficient,
                  pureWZ2AnchoredCWACoefficient]
                exact le_max_of_le_right
                  (le_max_of_le_right (le_max_left _ _))) _) _
        _ ≤ cwaCoefficient * inputConstant ^ 3 *
              logBound ^ polylogPower := by
          exact mul_le_mul_left'
            (pow_le_pow_right₀ hlogOne
              (by dsimp only [polylogPower]; omega)) _
  have htopRaw :
      pureWZ2TopScaleConstant
          inputConstant
          (pureWZ2UnitScaleCompleteFiberOverlapBound A)
          globalRetention ≤
        cwaCoefficient * inputConstant ^ 3 *
          logBound ^ polylogPower := by
    apply max_le
    · calc
        (1 : ENNReal) ≤ cwaCoefficient := by
          dsimp only [cwaCoefficient,
            pureWZ2AnchoredCWACoefficient]
          exact le_max_left _ _
        _ ≤ cwaCoefficient * inputConstant ^ 3 := by
          simpa using
            mul_le_mul_left' (one_le_pow₀ hinputOne) cwaCoefficient
        _ ≤ cwaCoefficient * inputConstant ^ 3 *
              logBound ^ polylogPower := by
          simpa using
            mul_le_mul_left' (one_le_pow₀ hlogOne)
              (cwaCoefficient * inputConstant ^ 3)
    · dsimp only [pureWZ2UnitScaleAggregateFrostmanConstant]
      calc
        27 * (212776173 * 1280 * inputConstant *
            (pureWZ2UnitScaleCompleteFiberOverlapBound A : ENNReal) *
            globalRetention)
            ≤
          27 * (212776173 * 1280 * inputConstant *
            (pureWZ2UnitScaleCompleteFiberOverlapBound A : ENNReal) *
            (inputConstant *
              (pureWZ2AnchoredLocalizationCoefficient R radius *
                pureWZ2AnchoredColorCoefficient A coordinateCount) *
              logBound ^ (coordinateCount + 1))) := by
            gcongr
        _ =
          (27 * 212776173 * 1280 *
            (pureWZ2UnitScaleCompleteFiberOverlapBound A : ENNReal) *
            pureWZ2AnchoredLocalizationCoefficient R radius *
            pureWZ2AnchoredColorCoefficient A coordinateCount) *
            inputConstant ^ 2 *
            logBound ^ (coordinateCount + 1) := by
          ring
        _ ≤ cwaCoefficient * inputConstant ^ 2 *
              logBound ^ (coordinateCount + 1) := by
          exact mul_le_mul_right'
            (mul_le_mul_right'
              (show
                27 * 212776173 * 1280 *
                    (pureWZ2UnitScaleCompleteFiberOverlapBound A : ENNReal) *
                    pureWZ2AnchoredLocalizationCoefficient R radius *
                    pureWZ2AnchoredColorCoefficient A coordinateCount ≤
                  cwaCoefficient by
                dsimp only [cwaCoefficient,
                  pureWZ2AnchoredCWACoefficient]
                exact le_max_of_le_right
                  (le_max_of_le_right (le_max_right _ _))) _) _
        _ ≤ cwaCoefficient * inputConstant ^ 3 *
              logBound ^ (coordinateCount + 1) := by
          exact mul_le_mul_right'
            (mul_le_mul_left'
              (show inputConstant ^ 2 ≤ inputConstant ^ 3 by
                exact pow_le_pow_right₀ hinputOne (by norm_num)) _) _
        _ ≤ cwaCoefficient * inputConstant ^ 3 *
              logBound ^ polylogPower := by
          exact mul_le_mul_left'
            (pow_le_pow_right₀ hlogOne
              (by dsimp only [polylogPower]; omega)) _
  have hcwaLog :=
    hcwaAbsorb delta hdelta hdeltaCWA'
  have hinputCube :
      inputConstant ^ 3 =
        Kakeya.realRpowENN delta (-3 * inputLoss) := by
    calc
      inputConstant ^ 3 =
          inputConstant * inputConstant * inputConstant := by ring
      _ =
          Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta (-inputLoss) *
              Kakeya.realRpowENN delta (-inputLoss) := by
        rfl
      _ = Kakeya.realRpowENN delta (-3 * inputLoss) := by
        rw [← realRpowENN_add hdelta,
          ← realRpowENN_add hdelta]
        congr 1
        ring
  have hcwaFinal :
      cwaCoefficient * inputConstant ^ 3 *
          logBound ^ polylogPower ≤
        Kakeya.realRpowENN delta (-outputLoss) := by
    calc
      cwaCoefficient * inputConstant ^ 3 *
            logBound ^ polylogPower =
          inputConstant ^ 3 *
            (cwaCoefficient * logBound ^ polylogPower) := by ring
      _ ≤ inputConstant ^ 3 *
            Kakeya.realRpowENN delta (-gap) := by
        gcongr
      _ =
          Kakeya.realRpowENN delta (-3 * inputLoss) *
            Kakeya.realRpowENN delta (-gap) := by
        rw [hinputCube]
      _ = Kakeya.realRpowENN delta (-outputLoss) := by
        rw [← realRpowENN_add hdelta]
        congr 1
        dsimp only [gap]
        ring
  have hlogInvOne :
      1 ≤ Real.log (1 / delta) := by
    have hlogDelta :
        Real.log delta ≤ -1 := by
      have :=
        Real.log_le_log hdelta hdeltaExp
      simpa using this
    rw [Real.log_div (by norm_num) hdelta.ne', Real.log_one]
    linarith
  let logBase := ENNReal.ofReal (Real.log (1 / delta))
  have hlogBaseOne : 1 ≤ logBase := by
    simpa [logBase] using ENNReal.ofReal_mono hlogInvOne
  have hlogBoundByBase :
      logBound ≤
        ENNReal.ofReal
            (2 * pureWZ2FixedBallCardLogConstant R) *
          logBase := by
    have hreal :
        pureWZ2FixedBallCardLogConstant R *
            (1 + Real.log delta⁻¹) ≤
          (2 * pureWZ2FixedBallCardLogConstant R) *
            Real.log (1 / delta) := by
      rw [show Real.log delta⁻¹ =
        Real.log (1 / delta) by
          congr 1
          field_simp]
      have hcoefficient :
          0 ≤ pureWZ2FixedBallCardLogConstant R :=
        hlogCoefficientNonnegative
      nlinarith
    have hproduct :
        ENNReal.ofReal
            ((2 * pureWZ2FixedBallCardLogConstant R) *
              Real.log (1 / delta)) =
          ENNReal.ofReal
              (2 * pureWZ2FixedBallCardLogConstant R) *
            logBase := by
      rw [ENNReal.ofReal_mul]
      positivity
    rw [← hproduct]
    exact ENNReal.ofReal_mono hreal
  have hmassRaw :
      (pureWZ2LocalizationCellCount R radius : ENNReal) *
          (pureWZ2ReanchoredPaperConflictLossBound : ENNReal) *
          selectionRetention ≤
        massExtra * logBase ^ (coordinateCount + 1) := by
    calc
      (pureWZ2LocalizationCellCount R radius : ENNReal) *
            (pureWZ2ReanchoredPaperConflictLossBound : ENNReal) *
            selectionRetention
          ≤
        pureWZ2AnchoredMassCoefficient A R radius coordinateCount *
          logTerm ^ (coordinateCount + 1) := by
        dsimp only [selectionRetention,
          pureWZ2FiniteAnchoredRetentionConstant,
          pureWZ2AnchoredMassCoefficient,
          pureWZ2AnchoredLocalizationCoefficient,
          pureWZ2AnchoredColorCoefficient, logTerm]
        ring_nf
        exact le_rfl
      _ ≤
        pureWZ2AnchoredMassCoefficient A R radius coordinateCount *
          logBound ^ (coordinateCount + 1) := by
        gcongr
      _ ≤ massExtra * logBase ^ (coordinateCount + 1) := by
        dsimp only [massExtra]
        have hpow :=
          pow_le_pow_left' hlogBoundByBase
            (coordinateCount + 1)
        rw [mul_pow] at hpow
        simpa [mul_assoc] using
          mul_le_mul_left' hpow
            (pureWZ2AnchoredMassCoefficient
              A R radius coordinateCount)
  have hmassConstant :=
    hmassAbsorb delta hdelta hdeltaMass'
  have hmassFinal :
      (pureWZ2LocalizationCellCount R radius : ENNReal) *
          (pureWZ2ReanchoredPaperConflictLossBound : ENNReal) *
          selectionRetention ≤
        logBase ^ logExponent := by
    calc
      _ ≤ massExtra * logBase ^ (coordinateCount + 1) :=
        hmassRaw
      _ ≤ logBase * logBase ^ (coordinateCount + 1) := by
        gcongr
      _ = logBase ^ logExponent := by
        dsimp only [logExponent]
        rw [show coordinateCount + 2 =
          (coordinateCount + 1) + 1 by omega, pow_succ]
        ring
  exact
    ⟨hcwaRaw.trans hcwaFinal,
      htopRaw.trans hcwaFinal,
      hmassFinal⟩

end Kakeya.Assouad

end
