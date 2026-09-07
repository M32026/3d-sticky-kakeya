import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientMassLedger
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import Mathlib.Tactic

/-!
# Proposition 6.2 quotient power budget

This module contains only the final scalar bookkeeping.

The six factors in the quotient mass ledger are grouped into five
logarithmic buckets:

1. base structural selection;
2. the global strong upper-colour vector;
3. the whole-fibre cardinality bin;
4. source colour together with the leaf-weight bin;
5. the single weighted tree cleanup.

If each bucket costs at most `log(1 / delta)^2`, their product is cancelled
by `wz1PaperRefinementFraction delta 10`.

The second part records the independent power bookkeeping.  With
`Cstar = delta ^ (-A * eta)`, every fixed coefficient times at most five
copies of `Cstar` is eventually bounded by `delta ^ (-6 * A * eta)`.
The constants, including `K` and `fixedLoss`, are explicit parameters and may
depend on `eta`, `c0`, or a depth bound; the exponent `6 * A` does not.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The final quotient CWA exponent; it depends only on the fixed integer `A`. -/
def pureWZ2Prop62ProxyQuotientCWAPower (A : ℕ) : ℕ :=
  6 * A

@[simp] lemma pureWZ2Prop62ProxyQuotientCWAPower_mul_eta
    (A : ℕ) (eta : ℝ) :
    (pureWZ2Prop62ProxyQuotientCWAPower A : ℝ) * eta =
      6 * (A : ℝ) * eta := by
  unfold pureWZ2Prop62ProxyQuotientCWAPower
  push_cast
  ring

/--
Five `log^2` buckets cancel against the absolute logarithmic refinement
exponent ten.
-/
theorem pureWZ2_prop62_five_log_square_absorption
    {delta : ℝ}
    {baseLoss upperVectorLoss fiberBinLoss
      sourceColorLoss leafBinLoss cleanupLoss totalLoss : ENNReal}
    (logBase_pos :
      0 < ENNReal.ofReal (Real.log (1 / delta)))
    (totalLoss_eq :
      totalLoss =
        baseLoss * upperVectorLoss * fiberBinLoss *
          sourceColorLoss * leafBinLoss * cleanupLoss)
    (base_bucket :
      baseLoss ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2)
    (upper_vector_bucket :
      upperVectorLoss ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2)
    (fiber_bin_bucket :
      fiberBinLoss ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2)
    (source_leaf_bucket :
      sourceColorLoss * leafBinLoss ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2)
    (cleanup_bucket :
      cleanupLoss ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2) :
    wz1PaperRefinementFraction delta 10 * totalLoss ≤ 1 := by
  let logBase : ENNReal :=
    ENNReal.ofReal (Real.log (1 / delta))
  have logBase_ne_zero : logBase ≠ 0 :=
    logBase_pos.ne'
  have logBase_ne_top : logBase ≠ ⊤ := by
    exact ENNReal.ofReal_ne_top
  have totalLoss_le :
      totalLoss ≤ logBase ^ 10 := by
    rw [totalLoss_eq]
    calc
      baseLoss * upperVectorLoss * fiberBinLoss *
            sourceColorLoss * leafBinLoss * cleanupLoss =
          baseLoss * upperVectorLoss * fiberBinLoss *
            (sourceColorLoss * leafBinLoss) * cleanupLoss := by
        ring
      _ ≤
          logBase ^ 2 * logBase ^ 2 * logBase ^ 2 *
            logBase ^ 2 * logBase ^ 2 := by
        gcongr
      _ = logBase ^ 10 := by ring
  change logBase⁻¹ ^ 10 * totalLoss ≤ 1
  rw [← ENNReal.inv_pow]
  calc
    (logBase ^ 10)⁻¹ * totalLoss ≤
        (logBase ^ 10)⁻¹ * logBase ^ 10 := by
      gcongr
    _ = 1 :=
      ENNReal.inv_mul_cancel
        (pow_ne_zero _ logBase_ne_zero)
        (ENNReal.pow_ne_top logBase_ne_top)

namespace PureWZ2Prop62ProxyQuotientMassLedger

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    {metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {Color : Type*}
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    {baseSelectedParents :
      Finset (Fin metric.metricParents.card)}
    {strongUpperSelectedParents :
      Finset (Fin metric.metricParents.card)}
    {completeFiber :
      Fin metric.metricParents.card →
        Finset (Fin fine.card)}
    {fiberCard :
      Fin metric.metricParents.card → ℕ}
    {parentWeight :
      Fin metric.metricParents.card → ENNReal}
    {owner :
      Fin fine.card → Fin metric.metricParents.card}
    {sourceColor : Fin fine.card → Color}
    {fiberCardBound : ℕ}
    {preCore :
      PureWZ2Prop62PreCoreSelectionData
        (Fin fine.card) (Fin metric.metricParents.card) Color
        strongUpperSelectedParents completeFiber fiberCard parentWeight owner
        sourceColor weight fiberCardBound}
    {preliminarySubsetSelection :
      preCore.preliminary ⊆
        (quotient.selectProxyResidueUpperAncestryPerCell
          rho width packetCoordinate strideBase weight).selected}
    {receipt :
      PureWZ2Prop62CleanupReceipt
        (pureWZ2Prop62ProxyQuotientAuxiliaryLevel
          schedule fineNonempty quotient rho width packetCoordinate).tree
        preCore.preliminary}
    {metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    (ledger :
      PureWZ2Prop62ProxyQuotientMassLedger
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight metric baseSelectedParents
        strongUpperSelectedParents completeFiber fiberCard
        parentWeight owner sourceColor fiberCardBound preCore
        preliminarySubsetSelection receipt metricCore)

/--
Ledger-specific form of the five-bucket logarithmic budget.  The source
colour and leaf-weight bin deliberately share one bucket.
-/
theorem five_log_square_absorption
    (logBase_pos :
      0 < ENNReal.ofReal (Real.log (1 / delta)))
    (base_bucket :
      ledger.baseSelectionLoss ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2)
    (upper_vector_bucket :
      ledger.upperColorLoss ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2)
    (fiber_bin_bucket :
      ledger.fiberBinLoss ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2)
    (source_leaf_bucket :
      ledger.sourceColorLoss * ledger.leafBinLoss ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2)
    (cleanup_bucket :
      ledger.cleanupLoss ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2) :
    wz1PaperRefinementFraction delta 10 *
        ledger.totalLoss ≤ 1 :=
  pureWZ2_prop62_five_log_square_absorption
    logBase_pos ledger.totalLoss_eq base_bucket
    upper_vector_bucket fiber_bin_bucket source_leaf_bucket
    cleanup_bucket

end PureWZ2Prop62ProxyQuotientMassLedger

/-- Natural powers of one source-scale `rpow` combine their exponents. -/
lemma pureWZ2Prop62_realRpowENN_pow
    {delta exponent : ℝ}
    (delta_pos : 0 < delta)
    (power : ℕ) :
    (Kakeya.realRpowENN delta exponent) ^ power =
      Kakeya.realRpowENN delta ((power : ℝ) * exponent) := by
  induction power with
  | zero =>
      simp [Kakeya.realRpowENN]
  | succ power inductionHypothesis =>
      rw [pow_succ, inductionHypothesis,
        Subunit.realRpowENN_mul delta_pos]
      congr 1
      push_cast
      ring

/--
A finite coefficient multiplying at most five copies of `Cstar` is absorbed
by six copies for all sufficiently small `delta`.
-/
theorem exists_pureWZ2Prop62_fixed_mul_Cstar_pow_le_six
    (fixed : ENNReal)
    (fixed_ne_top : fixed ≠ ⊤)
    {loss : ℝ} (loss_pos : 0 < loss)
    (power : ℕ) (power_le_five : power ≤ 5) :
    ∃ delta0 : ℝ,
      0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        fixed *
            (Kakeya.realRpowENN delta (-loss)) ^ power ≤
          Kakeya.realRpowENN delta (-6 * loss) := by
  let gap : ℝ := (6 - (power : ℝ)) * loss
  have power_lt_six : (power : ℝ) < 6 := by
    exact_mod_cast (show power < 6 by omega)
  have gap_pos : 0 < gap := by
    dsimp only [gap]
    positivity
  rcases
      exists_delta_realRpowENN_bound
        fixed fixed_ne_top gap_pos with
    ⟨delta0, delta0_pos, delta0_le_one, fixed_bound⟩
  refine ⟨delta0, delta0_pos, delta0_le_one, ?_⟩
  intro delta delta_pos delta_le
  calc
    fixed *
          (Kakeya.realRpowENN delta (-loss)) ^ power ≤
        Kakeya.realRpowENN delta (-gap) *
          (Kakeya.realRpowENN delta (-loss)) ^ power := by
      gcongr
      exact fixed_bound delta delta_pos delta_le
    _ =
        Kakeya.realRpowENN delta (-6 * loss) := by
      rw [pureWZ2Prop62_realRpowENN_pow delta_pos,
        Subunit.realRpowENN_mul delta_pos]
      congr 1
      dsimp only [gap]
      ring

/--
The ratio and cleanup-density hypotheses place the actual inserted-fibre
constant below a fixed coefficient times `Cstar^5`.
-/
theorem pureWZ2Prop62_inserted_fiber_constant_le_envelope
    {Cstar fixedLoss insertedCoefficient : ENNReal}
    {K ratio : ℝ}
    (Cstar_ne_top : Cstar ≠ ⊤)
    (K_nonneg : 0 ≤ K)
    (ratio_nonneg : 0 ≤ ratio)
    (ratio_le : ratio ≤ K * Cstar.toReal)
    {Λ : ENNReal}
    (Lambda_le : Λ ≤ fixedLoss * Cstar ^ 2) :
    insertedCoefficient * ENNReal.ofReal (ratio ^ 2) *
          Cstar * Λ ≤
      (insertedCoefficient * ENNReal.ofReal (K ^ 2) *
          fixedLoss) * Cstar ^ 5 := by
  have ratioSquare :
      ratio ^ 2 ≤ (K * Cstar.toReal) ^ 2 := by
    nlinarith
  have ratioENN :
      ENNReal.ofReal (ratio ^ 2) ≤
        ENNReal.ofReal (K ^ 2) * Cstar ^ 2 := by
    calc
      ENNReal.ofReal (ratio ^ 2) ≤
          ENNReal.ofReal ((K * Cstar.toReal) ^ 2) :=
        ENNReal.ofReal_mono ratioSquare
      _ = ENNReal.ofReal (K ^ 2) * Cstar ^ 2 := by
        rw [show
          (K * Cstar.toReal) ^ 2 =
            K ^ 2 * Cstar.toReal ^ 2 by ring,
          ENNReal.ofReal_mul (sq_nonneg K),
          ENNReal.ofReal_pow ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal Cstar_ne_top]
  calc
    insertedCoefficient * ENNReal.ofReal (ratio ^ 2) *
          Cstar * Λ ≤
        insertedCoefficient *
            (ENNReal.ofReal (K ^ 2) * Cstar ^ 2) *
          Cstar * (fixedLoss * Cstar ^ 2) := by
      gcongr
    _ =
        (insertedCoefficient * ENNReal.ofReal (K ^ 2) *
          fixedLoss) * Cstar ^ 5 := by
      ring

/-- The upper-parent CWA expression uses three copies of `Cstar`. -/
theorem pureWZ2Prop62_upper_parent_constant_le_envelope
    {Cstar fixedLoss upperCoefficient Λ : ENNReal}
    (Lambda_le : Λ ≤ fixedLoss * Cstar ^ 2) :
    (Λ * Cstar) * upperCoefficient ≤
      (upperCoefficient * fixedLoss) * Cstar ^ 3 := by
  calc
    (Λ * Cstar) * upperCoefficient ≤
        ((fixedLoss * Cstar ^ 2) * Cstar) * upperCoefficient := by
      gcongr
    _ = (upperCoefficient * fixedLoss) * Cstar ^ 3 := by
      ring

/-- The upper strict-fibre uniformity expression also uses three `Cstar`s. -/
theorem pureWZ2Prop62_upper_uniformity_constant_le_envelope
    {Cstar fixedLoss uniformityCoefficient Λ : ENNReal}
    (Lambda_le : Λ ≤ fixedLoss * Cstar ^ 2) :
    uniformityCoefficient * Cstar * Λ ≤
      (uniformityCoefficient * fixedLoss) * Cstar ^ 3 := by
  calc
    uniformityCoefficient * Cstar * Λ ≤
        uniformityCoefficient * Cstar * (fixedLoss * Cstar ^ 2) := by
      gcongr
    _ =
        (uniformityCoefficient * fixedLoss) * Cstar ^ 3 := by
      ring

/--
A cubic scale window, including `16 * Cstar^3`, is dominated by the
corresponding conservative fifth-power envelope whenever `Cstar ≥ 1`.
-/
theorem pureWZ2Prop62_scale_window_three_le_five
    {Cstar windowCoefficient : ENNReal}
    (Cstar_one : 1 ≤ Cstar) :
    windowCoefficient * Cstar ^ 3 ≤
      windowCoefficient * Cstar ^ 5 := by
  have square_one : 1 ≤ Cstar ^ 2 :=
    one_le_pow₀ Cstar_one
  have power_le : Cstar ^ 3 ≤ Cstar ^ 5 := by
    calc
      Cstar ^ 3 = Cstar ^ 3 * 1 := by simp
      _ ≤ Cstar ^ 3 * Cstar ^ 2 :=
        mul_le_mul_left' square_one _
      _ = Cstar ^ 5 := by ring
  exact mul_le_mul_left' power_le windowCoefficient

/--
Simultaneous scalar output for the inserted fibre, upper-parent CWA,
upper-fibre uniformity, and a conservative fifth-power requested-scale
window.
-/
structure PureWZ2Prop62ProxyQuotientPowerBudgetData
    (A : ℕ) (eta delta K : ℝ)
    (fixedLoss insertedCoefficient upperCoefficient
      uniformityCoefficient windowCoefficient : ENNReal) : Prop where
  delta_pos :
    0 < delta
  delta_le_one :
    delta ≤ 1
  Cstar_one :
    1 ≤ Kakeya.realRpowENN delta (-((A : ℝ) * eta))
  inserted_fiber :
    ∀ {ratio : ℝ} {Λ : ENNReal},
      0 ≤ ratio →
      ratio ≤ K *
        (Kakeya.realRpowENN delta
          (-((A : ℝ) * eta))).toReal →
      Λ ≤ fixedLoss *
        (Kakeya.realRpowENN delta (-((A : ℝ) * eta))) ^ 2 →
      insertedCoefficient * ENNReal.ofReal (ratio ^ 2) *
            Kakeya.realRpowENN delta (-((A : ℝ) * eta)) * Λ ≤
        Kakeya.realRpowENN delta (-6 * (A : ℝ) * eta)
  upper_parent :
    ∀ {Λ : ENNReal},
      Λ ≤ fixedLoss *
        (Kakeya.realRpowENN delta (-((A : ℝ) * eta))) ^ 2 →
      (Λ * Kakeya.realRpowENN delta (-((A : ℝ) * eta))) *
          upperCoefficient ≤
        Kakeya.realRpowENN delta (-6 * (A : ℝ) * eta)
  upper_uniformity :
    ∀ {Λ : ENNReal},
      Λ ≤ fixedLoss *
        (Kakeya.realRpowENN delta (-((A : ℝ) * eta))) ^ 2 →
      uniformityCoefficient *
          Kakeya.realRpowENN delta (-((A : ℝ) * eta)) * Λ ≤
        Kakeya.realRpowENN delta (-6 * (A : ℝ) * eta)
  scale_window :
    windowCoefficient *
        (Kakeya.realRpowENN delta
          (-((A : ℝ) * eta))) ^ 5 ≤
      Kakeya.realRpowENN delta (-6 * (A : ℝ) * eta)

namespace PureWZ2Prop62ProxyQuotientPowerBudgetData

variable
    {A : ℕ} {eta delta K : ℝ}
    {fixedLoss insertedCoefficient upperCoefficient
      uniformityCoefficient windowCoefficient : ENNReal}
    (budget :
      PureWZ2Prop62ProxyQuotientPowerBudgetData
        A eta delta K fixedLoss insertedCoefficient
          upperCoefficient uniformityCoefficient windowCoefficient)

/-- Rewrite the common target using the Nat-valued public CWA power. -/
theorem target_eq_cwaPower :
    Kakeya.realRpowENN delta (-6 * (A : ℝ) * eta) =
      Kakeya.realRpowENN delta
        (-(pureWZ2Prop62ProxyQuotientCWAPower A : ℝ) * eta) := by
  congr 1
  unfold pureWZ2Prop62ProxyQuotientCWAPower
  push_cast
  ring

include budget

/--
The same budget accepts an actual cubic window, for example by taking
`windowCoefficient = 16`.
-/
theorem scale_window_three :
    windowCoefficient *
        (Kakeya.realRpowENN delta
          (-((A : ℝ) * eta))) ^ 3 ≤
      Kakeya.realRpowENN delta (-6 * (A : ℝ) * eta) := by
  rcases budget with
    ⟨_deltaPos, _deltaLeOne, CstarOne,
      _insertedFiber, _upperParent, _upperUniformity,
      scaleWindow⟩
  exact
    (pureWZ2Prop62_scale_window_three_le_five
      CstarOne).trans scaleWindow

end PureWZ2Prop62ProxyQuotientPowerBudgetData

/--
Uniformly absorb all four final constants into exponent `6 * A * eta`.
Every large coefficient is explicit.  Only their finiteness and `K ≥ 0` are
required.
-/
theorem exists_pureWZ2Prop62ProxyQuotientPowerBudget
    (A : ℕ) (A_ge_one : 1 ≤ A)
    (eta K : ℝ)
    (eta_pos : 0 < eta)
    (K_nonneg : 0 ≤ K)
    (fixedLoss insertedCoefficient upperCoefficient
      uniformityCoefficient windowCoefficient : ENNReal)
    (fixedLoss_ne_top : fixedLoss ≠ ⊤)
    (insertedCoefficient_ne_top : insertedCoefficient ≠ ⊤)
    (upperCoefficient_ne_top : upperCoefficient ≠ ⊤)
    (uniformityCoefficient_ne_top : uniformityCoefficient ≠ ⊤)
    (windowCoefficient_ne_top : windowCoefficient ≠ ⊤) :
    ∃ delta0 : ℝ,
      0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        PureWZ2Prop62ProxyQuotientPowerBudgetData
          A eta delta K fixedLoss insertedCoefficient
          upperCoefficient uniformityCoefficient windowCoefficient := by
  let loss : ℝ := (A : ℝ) * eta
  have loss_pos : 0 < loss := by
    dsimp only [loss]
    positivity
  let insertedFixed :=
    insertedCoefficient * ENNReal.ofReal (K ^ 2) * fixedLoss
  let upperFixed := upperCoefficient * fixedLoss
  let uniformityFixed := uniformityCoefficient * fixedLoss
  have insertedFixed_ne_top : insertedFixed ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top insertedCoefficient_ne_top
        ENNReal.ofReal_ne_top)
      fixedLoss_ne_top
  have upperFixed_ne_top : upperFixed ≠ ⊤ :=
    ENNReal.mul_ne_top upperCoefficient_ne_top fixedLoss_ne_top
  have uniformityFixed_ne_top : uniformityFixed ≠ ⊤ :=
    ENNReal.mul_ne_top uniformityCoefficient_ne_top
      fixedLoss_ne_top
  rcases
      exists_pureWZ2Prop62_fixed_mul_Cstar_pow_le_six
        insertedFixed insertedFixed_ne_top loss_pos 5 (by omega) with
    ⟨insertedScale, insertedScale_pos, insertedScale_le_one,
      insertedBound⟩
  rcases
      exists_pureWZ2Prop62_fixed_mul_Cstar_pow_le_six
        upperFixed upperFixed_ne_top loss_pos 3 (by omega) with
    ⟨upperScale, upperScale_pos, upperScale_le_one,
      upperBound⟩
  rcases
      exists_pureWZ2Prop62_fixed_mul_Cstar_pow_le_six
        uniformityFixed uniformityFixed_ne_top loss_pos 3
        (by omega) with
    ⟨uniformityScale, uniformityScale_pos,
      uniformityScale_le_one, uniformityBound⟩
  rcases
      exists_pureWZ2Prop62_fixed_mul_Cstar_pow_le_six
        windowCoefficient windowCoefficient_ne_top loss_pos 5
        (by omega) with
    ⟨windowScale, windowScale_pos, windowScale_le_one,
      windowBound⟩
  let delta0 :=
    min insertedScale
      (min upperScale (min uniformityScale windowScale))
  have delta0_pos : 0 < delta0 := by
    exact lt_min insertedScale_pos <|
      lt_min upperScale_pos <|
        lt_min uniformityScale_pos windowScale_pos
  have delta0_le_one : delta0 ≤ 1 :=
    (min_le_left _ _).trans insertedScale_le_one
  refine ⟨delta0, delta0_pos, delta0_le_one, ?_⟩
  intro delta delta_pos delta_le
  have delta_le_inserted : delta ≤ insertedScale :=
    delta_le.trans (min_le_left _ _)
  have delta_le_upper : delta ≤ upperScale :=
    delta_le.trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have delta_le_uniformity : delta ≤ uniformityScale :=
    delta_le.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have delta_le_window : delta ≤ windowScale :=
    delta_le.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
  let Cstar := Kakeya.realRpowENN delta (-loss)
  let target := Kakeya.realRpowENN delta (-6 * loss)
  have Cstar_ne_top : Cstar ≠ ⊤ := by
    simp [Cstar, Kakeya.realRpowENN]
  have Cstar_one : 1 ≤ Cstar := by
    have exponent_le : -loss ≤ 0 := by
      linarith
    have powerBound :=
      pure_wz2_rpowENN_antitone
        delta_pos (delta_le.trans delta0_le_one) exponent_le
    simpa [Cstar, Kakeya.realRpowENN] using powerBound
  have insertedEnvelope :
      insertedFixed * Cstar ^ 5 ≤ target :=
    insertedBound delta delta_pos delta_le_inserted
  have upperEnvelope :
      upperFixed * Cstar ^ 3 ≤ target :=
    upperBound delta delta_pos delta_le_upper
  have uniformityEnvelope :
      uniformityFixed * Cstar ^ 3 ≤ target :=
    uniformityBound delta delta_pos delta_le_uniformity
  have windowEnvelope :
      windowCoefficient * Cstar ^ 5 ≤ target :=
    windowBound delta delta_pos delta_le_window
  exact
    {
      delta_pos := delta_pos
      delta_le_one := delta_le.trans delta0_le_one
      Cstar_one := by
        simpa [Cstar, loss] using Cstar_one
      inserted_fiber := by
        intro ratio Λ ratio_nonneg ratio_le Lambda_le
        calc
          insertedCoefficient * ENNReal.ofReal (ratio ^ 2) *
                Kakeya.realRpowENN delta (-((A : ℝ) * eta)) * Λ ≤
              insertedFixed * Cstar ^ 5 := by
            apply
              pureWZ2Prop62_inserted_fiber_constant_le_envelope
                Cstar_ne_top K_nonneg ratio_nonneg
            · simpa [Cstar, loss] using ratio_le
            · simpa [Cstar, loss] using Lambda_le
          _ ≤
              Kakeya.realRpowENN delta
                (-6 * (A : ℝ) * eta) := by
            convert insertedEnvelope using 1 <;>
              dsimp only [target, loss] <;> ring
      upper_parent := by
        intro Λ Lambda_le
        calc
          (Λ * Kakeya.realRpowENN delta (-((A : ℝ) * eta))) *
                upperCoefficient ≤
              upperFixed * Cstar ^ 3 := by
            apply pureWZ2Prop62_upper_parent_constant_le_envelope
            simpa [Cstar, loss] using Lambda_le
          _ ≤
              Kakeya.realRpowENN delta
                (-6 * (A : ℝ) * eta) := by
            convert upperEnvelope using 1 <;>
              dsimp only [target, loss] <;> ring
      upper_uniformity := by
        intro Λ Lambda_le
        calc
          uniformityCoefficient *
                Kakeya.realRpowENN delta (-((A : ℝ) * eta)) * Λ ≤
              uniformityFixed * Cstar ^ 3 := by
            apply
              pureWZ2Prop62_upper_uniformity_constant_le_envelope
            simpa [Cstar, loss] using Lambda_le
          _ ≤
              Kakeya.realRpowENN delta
                (-6 * (A : ℝ) * eta) := by
            convert uniformityEnvelope using 1 <;>
              dsimp only [target, loss] <;> ring
      scale_window := by
        convert windowEnvelope using 1 <;>
          dsimp only [Cstar, target, loss] <;> ring
    }

end Kakeya.Assouad

end
