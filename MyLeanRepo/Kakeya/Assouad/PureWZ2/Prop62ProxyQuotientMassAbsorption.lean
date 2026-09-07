import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientPowerBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientPreCoreAdapter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CanonicalMassBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CallerAnchoredRequestedScaleSchedule
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBoundaryLogCoefficient
import Mathlib.Tactic

/-!
# Proposition 6.2 quotient mass absorption

This module closes the logarithmic bookkeeping for the six factors in one
`PureWZ2Prop62ProxyQuotientMassLedger`.

The fixed bounds are selected from `A`, `eta`, and the arbitrary caller
constant `c0`, before `delta`, the schedule, or either tube family is
introduced.  The two genuinely cardinality-dependent factors are represented
by fixed coefficients multiplying `1 + log (delta⁻¹)`.

The six factors are grouped into five buckets:

* base structural loss;
* strong upper-colour-vector loss;
* whole-fibre `DMinus` bin loss;
* source-colour loss times the leaf-weight-bin loss;
* the one weighted-cleanup loss.

Each bucket is bounded by `log(1 / delta)^2`, so the product is cancelled by
`wz1PaperRefinementFraction delta 10`.  The cleanup factor occurs exactly
once.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Bounds fixed before the small scale is chosen.

The parameters make the permitted dependency explicit: these constants may
depend on `A`, `eta`, and `c0`, but not on `delta`, a schedule, a family, or
their cardinalities.
-/
structure PureWZ2Prop62ProxyQuotientMassFixedBounds
    (A : ℕ) (eta c0 : ℝ) where
  baseStructural : ENNReal
  baseStructural_ne_top : baseStructural ≠ ⊤
  strongUpperVector : ENNReal
  strongUpperVector_ne_top : strongUpperVector ≠ ⊤
  fiberBinCoefficient : ℝ
  fiberBinCoefficient_nonneg : 0 ≤ fiberBinCoefficient
  sourceColor : ENNReal
  sourceColor_ne_top : sourceColor ≠ ⊤
  leafBinCoefficient : ℝ
  leafBinCoefficient_nonneg : 0 ≤ leafBinCoefficient
  weightedCleanup : ENNReal
  weightedCleanup_ne_top : weightedCleanup ≠ ⊤

namespace PureWZ2Prop62ProxyQuotientMassFixedBounds

variable
    {A : ℕ} {eta c0 : ℝ}
    (bounds :
      PureWZ2Prop62ProxyQuotientMassFixedBounds A eta c0)

/-- One real coefficient dominating all five logarithmic buckets. -/
def envelopeCoefficient : ℝ :=
  max bounds.baseStructural.toReal <|
    max bounds.strongUpperVector.toReal <|
      max bounds.fiberBinCoefficient <|
        max
          (bounds.sourceColor.toReal *
            bounds.leafBinCoefficient)
          bounds.weightedCleanup.toReal

theorem envelopeCoefficient_nonneg :
    0 ≤ bounds.envelopeCoefficient := by
  exact ENNReal.toReal_nonneg.trans <| le_max_left _ _

theorem baseStructural_toReal_le :
    bounds.baseStructural.toReal ≤
      bounds.envelopeCoefficient :=
  le_max_left _ _

theorem strongUpperVector_toReal_le :
    bounds.strongUpperVector.toReal ≤
      bounds.envelopeCoefficient :=
  (le_max_left _ _).trans <| le_max_right _ _

theorem fiberBinCoefficient_le :
    bounds.fiberBinCoefficient ≤
      bounds.envelopeCoefficient :=
  (le_max_left _ _).trans <|
    (le_max_right _ _).trans <| le_max_right _ _

theorem sourceLeafCoefficient_le :
    bounds.sourceColor.toReal *
        bounds.leafBinCoefficient ≤
      bounds.envelopeCoefficient :=
  (le_max_left _ _).trans <|
    (le_max_right _ _).trans <|
      (le_max_right _ _).trans <| le_max_right _ _

theorem weightedCleanup_toReal_le :
    bounds.weightedCleanup.toReal ≤
      bounds.envelopeCoefficient :=
  (le_max_right _ _).trans <|
    (le_max_right _ _).trans <|
      (le_max_right _ _).trans <| le_max_right _ _

end PureWZ2Prop62ProxyQuotientMassFixedBounds

/--
Concrete fixed envelope for the quotient ledger.  Apart from the one
caller-supplied base structural bound, every entry is determined by the fixed
schedule-depth bound and the fixed source-colour type.
-/
noncomputable def pureWZ2Prop62ProxyQuotientGeometryMassBounds
    (A : ℕ) (eta c0 : ℝ)
    (depthBound : ℕ)
    (SourceColor : Type*) [Fintype SourceColor]
    (baseStructural : ENNReal)
    (baseStructural_ne_top : baseStructural ≠ ⊤) :
    PureWZ2Prop62ProxyQuotientMassFixedBounds A eta c0 where
  baseStructural := baseStructural
  baseStructural_ne_top := baseStructural_ne_top
  strongUpperVector :=
    ((pureWZ2Prop62UpperEnvelopeConflictDegree + 1 : ℕ) :
      ENNReal) ^ depthBound
  strongUpperVector_ne_top := ENNReal.pow_ne_top (by simp)
  fiberBinCoefficient :=
    pureWZ2Prop62OrdinaryCardLogConstant
  fiberBinCoefficient_nonneg := by
    unfold pureWZ2Prop62OrdinaryCardLogConstant
    positivity
  sourceColor := Fintype.card SourceColor
  sourceColor_ne_top := by simp
  leafBinCoefficient :=
    2 * pureWZ2Prop62OrdinaryCardLogConstant
  leafBinCoefficient_nonneg := by
    unfold pureWZ2Prop62OrdinaryCardLogConstant
    positivity
  weightedCleanup :=
    (2 : ENNReal) ^ (depthBound + 2)
  weightedCleanup_ne_top := ENNReal.pow_ne_top (by simp)

private theorem fixed_ennreal_le_log_square
    {fixed : ENNReal} {coefficient logarithm : ℝ}
    (fixed_ne_top : fixed ≠ ⊤)
    (fixed_le : fixed.toReal ≤ coefficient)
    (logarithm_nonneg : 0 ≤ logarithm)
    (envelope :
      coefficient * (1 + logarithm) ≤ logarithm ^ 2) :
    fixed ≤ (ENNReal.ofReal logarithm) ^ 2 := by
  have fixedRepresentation :
      fixed = ENNReal.ofReal fixed.toReal :=
    (ENNReal.ofReal_toReal fixed_ne_top).symm
  have fixedRealBound :
      fixed.toReal ≤ coefficient * (1 + logarithm) := by
    calc
      fixed.toReal ≤ coefficient := fixed_le
      _ ≤ coefficient * (1 + logarithm) := by
        have coefficient_nonneg :
            0 ≤ coefficient :=
          ENNReal.toReal_nonneg.trans fixed_le
        nlinarith
  rw [fixedRepresentation]
  calc
    ENNReal.ofReal fixed.toReal ≤
        ENNReal.ofReal
          (coefficient * (1 + logarithm)) :=
      ENNReal.ofReal_mono fixedRealBound
    _ ≤ ENNReal.ofReal (logarithm ^ 2) :=
      ENNReal.ofReal_mono envelope
    _ = (ENNReal.ofReal logarithm) ^ 2 :=
      ENNReal.ofReal_pow logarithm_nonneg 2

private theorem log_linear_ennreal_le_log_square
    {loss : ENNReal} {factor coefficient logarithm : ℝ}
    (loss_le :
      loss ≤
        ENNReal.ofReal (factor * (1 + logarithm)))
    (factor_le : factor ≤ coefficient)
    (logarithm_nonneg : 0 ≤ logarithm)
    (envelope :
      coefficient * (1 + logarithm) ≤ logarithm ^ 2) :
    loss ≤ (ENNReal.ofReal logarithm) ^ 2 := by
  calc
    loss ≤
        ENNReal.ofReal (factor * (1 + logarithm)) :=
      loss_le
    _ ≤
        ENNReal.ofReal (coefficient * (1 + logarithm)) := by
      apply ENNReal.ofReal_mono
      exact
        mul_le_mul_of_nonneg_right factor_le <| by
          linarith
    _ ≤ ENNReal.ofReal (logarithm ^ 2) :=
      ENNReal.ofReal_mono envelope
    _ = (ENNReal.ofReal logarithm) ^ 2 :=
      ENNReal.ofReal_pow logarithm_nonneg 2

/--
Small-scale certificate for six named ledger factors.

All fixed bounds precede `delta0`.  At runtime the caller supplies the exact
six factor estimates for its ledger; the conclusion is the final logarithmic
retention inequality.
-/
theorem exists_pureWZ2Prop62ProxyQuotientMassAbsorption
    (A : ℕ) (eta c0 : ℝ)
    (bounds :
      PureWZ2Prop62ProxyQuotientMassFixedBounds A eta c0) :
    ∃ delta0 : ℝ,
      0 < delta0 ∧ delta0 ≤ 1 / 100 ∧
      ∀ {delta : ℝ},
        0 < delta →
        delta ≤ delta0 →
        ∀ {baseLoss upperColorLoss fiberBinLoss
            sourceColorLoss leafBinLoss cleanupLoss totalLoss : ENNReal},
          totalLoss =
              baseLoss * upperColorLoss * fiberBinLoss *
                sourceColorLoss * leafBinLoss * cleanupLoss →
          baseLoss ≤ bounds.baseStructural →
          upperColorLoss ≤ bounds.strongUpperVector →
          fiberBinLoss ≤
            ENNReal.ofReal
              (bounds.fiberBinCoefficient *
                (1 + Real.log delta⁻¹)) →
          sourceColorLoss ≤ bounds.sourceColor →
          leafBinLoss ≤
            ENNReal.ofReal
              (bounds.leafBinCoefficient *
                (1 + Real.log delta⁻¹)) →
          cleanupLoss ≤ bounds.weightedCleanup →
          wz1PaperRefinementFraction delta 10 * totalLoss ≤ 1 := by
  rcases
      exists_delta_boundary_log_square
        bounds.envelopeCoefficient
        bounds.envelopeCoefficient_nonneg with
    ⟨logScale, logScale_pos, logScale_le_one, logEnvelope⟩
  let delta0 := min (1 / 100 : ℝ) logScale
  have delta0_pos : 0 < delta0 :=
    lt_min (by norm_num) logScale_pos
  have delta0_le_one_hundred :
      delta0 ≤ 1 / 100 := min_le_left _ _
  refine
    ⟨delta0, delta0_pos, delta0_le_one_hundred, ?_⟩
  intro delta delta_pos delta_le
  intro baseLoss upperColorLoss fiberBinLoss
    sourceColorLoss leafBinLoss cleanupLoss totalLoss
  intro totalLoss_eq baseLoss_le upperColorLoss_le
    fiberBinLoss_le sourceColorLoss_le leafBinLoss_le
    cleanupLoss_le
  have delta_le_logScale :
      delta ≤ logScale :=
    delta_le.trans (min_le_right _ _)
  have logData :=
    logEnvelope delta delta_pos delta_le_logScale
  have logEq :
      Real.log (1 / delta) = Real.log delta⁻¹ := by
    congr 1
    field_simp [delta_pos.ne']
  have logPositive :
      0 < Real.log (1 / delta) := by
    rw [logEq]
    linarith [logData.1]
  have logNonnegative :
      0 ≤ Real.log delta⁻¹ := by
    linarith [logData.1]
  have baseBucket :
      baseLoss ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 := by
    rw [logEq]
    exact
      (baseLoss_le.trans <|
        fixed_ennreal_le_log_square
          bounds.baseStructural_ne_top
          bounds.baseStructural_toReal_le
          logNonnegative logData.2)
  have upperBucket :
      upperColorLoss ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 := by
    rw [logEq]
    exact
      upperColorLoss_le.trans <|
        fixed_ennreal_le_log_square
          bounds.strongUpperVector_ne_top
          bounds.strongUpperVector_toReal_le
          logNonnegative logData.2
  have fiberBucket :
      fiberBinLoss ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 := by
    rw [logEq]
    exact
      log_linear_ennreal_le_log_square
        fiberBinLoss_le bounds.fiberBinCoefficient_le
        logNonnegative logData.2
  have sourceLeafRaw :
      sourceColorLoss * leafBinLoss ≤
        ENNReal.ofReal
          ((bounds.sourceColor.toReal *
              bounds.leafBinCoefficient) *
            (1 + Real.log delta⁻¹)) := by
    calc
      sourceColorLoss * leafBinLoss ≤
          bounds.sourceColor *
            ENNReal.ofReal
              (bounds.leafBinCoefficient *
                (1 + Real.log delta⁻¹)) := by
        gcongr
      _ =
          ENNReal.ofReal bounds.sourceColor.toReal *
            ENNReal.ofReal
              (bounds.leafBinCoefficient *
                (1 + Real.log delta⁻¹)) := by
        rw [ENNReal.ofReal_toReal
          bounds.sourceColor_ne_top]
      _ =
          ENNReal.ofReal
            (bounds.sourceColor.toReal *
              (bounds.leafBinCoefficient *
                (1 + Real.log delta⁻¹))) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      _ =
          ENNReal.ofReal
            ((bounds.sourceColor.toReal *
                bounds.leafBinCoefficient) *
              (1 + Real.log delta⁻¹)) := by
        congr 1
        ring
  have sourceLeafBucket :
      sourceColorLoss * leafBinLoss ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 := by
    rw [logEq]
    exact
      log_linear_ennreal_le_log_square
        sourceLeafRaw bounds.sourceLeafCoefficient_le
        logNonnegative logData.2
  have cleanupBucket :
      cleanupLoss ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 := by
    rw [logEq]
    exact
      cleanupLoss_le.trans <|
        fixed_ennreal_le_log_square
          bounds.weightedCleanup_ne_top
          bounds.weightedCleanup_toReal_le
          logNonnegative logData.2
  exact
    pureWZ2_prop62_five_log_square_absorption
      (ENNReal.ofReal_pos.mpr logPositive)
      totalLoss_eq baseBucket upperBucket
      fiberBucket sourceLeafBucket cleanupBucket

/-- Canonical threshold extracted from the six-factor absorption theorem. -/
noncomputable def pureWZ2Prop62ProxyQuotientMassThreshold
    (A : ℕ) (eta c0 : ℝ)
    (bounds :
      PureWZ2Prop62ProxyQuotientMassFixedBounds A eta c0) : ℝ :=
  Classical.choose <|
    exists_pureWZ2Prop62ProxyQuotientMassAbsorption
      A eta c0 bounds

theorem pureWZ2Prop62ProxyQuotientMassThreshold_pos
    (A : ℕ) (eta c0 : ℝ)
    (bounds :
      PureWZ2Prop62ProxyQuotientMassFixedBounds A eta c0) :
    0 <
      pureWZ2Prop62ProxyQuotientMassThreshold
        A eta c0 bounds :=
  (Classical.choose_spec <|
    exists_pureWZ2Prop62ProxyQuotientMassAbsorption
      A eta c0 bounds).1

theorem pureWZ2Prop62ProxyQuotientMassThreshold_le_one_hundred
    (A : ℕ) (eta c0 : ℝ)
    (bounds :
      PureWZ2Prop62ProxyQuotientMassFixedBounds A eta c0) :
    pureWZ2Prop62ProxyQuotientMassThreshold
        A eta c0 bounds ≤
      1 / 100 :=
  (Classical.choose_spec <|
    exists_pureWZ2Prop62ProxyQuotientMassAbsorption
      A eta c0 bounds).2.1

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
Concrete quotient-ledger closure.

The only remaining external numerical factor bound is
`base_structural_bound`.  `upper_loss_eq` is merely provenance identifying
the ledger field with the already constructed global upper-colour selection.
The upper, `DMinus`-bin, source-colour, leaf-bin, and cleanup bounds are
derived from their defining fields.
-/
theorem final_refinement_absorption_of_ledger_geometry
    {A : ℕ} {eta c0 : ℝ}
    (depthBound : ℕ)
    (baseStructural : ENNReal)
    (baseStructural_ne_top : baseStructural ≠ ⊤)
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    (adapter :
      PureWZ2Prop62ProxyQuotientPreCoreAdapterData
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight metric
        coloring
        Color sourceColor)
    {adapterPreliminarySubsetSelection :
      adapter.preCore.preliminary ⊆
        (quotient.selectProxyResidueUpperAncestryPerCell
          rho width packetCoordinate strideBase weight).selected}
    {adapterReceipt :
      PureWZ2Prop62CleanupReceipt
        (pureWZ2Prop62ProxyQuotientAuxiliaryLevel
          schedule fineNonempty quotient rho width packetCoordinate).tree
        adapter.preCore.preliminary}
    (concreteLedger :
      PureWZ2Prop62ProxyQuotientMassLedger
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight metric Finset.univ
        adapter.global.selectedParents
        metric.ambientCompleteMetricFiber
        (fun parent =>
          (metric.ambientCompleteMetricFiber parent).card)
        metric.metricParentWeight metric.ambientMetricParentOf
        sourceColor metric.selectedFine.card adapter.preCore
        adapterPreliminarySubsetSelection adapterReceipt metricCore)
    (upper_loss_eq :
      concreteLedger.upperColorLoss =
        adapter.global.upperColorLoss)
    (delta_pos : 0 < delta)
    (delta_le :
      delta ≤
        pureWZ2Prop62ProxyQuotientMassThreshold
          A eta c0
            (pureWZ2Prop62ProxyQuotientGeometryMassBounds
              A eta c0 depthBound Color baseStructural
                baseStructural_ne_top))
    (depth_le : schedule.levelCount ≤ depthBound)
    (fineBoundedBase : HasBoundedBase fine 4)
    (base_structural_bound :
      concreteLedger.baseSelectionLoss ≤ baseStructural) :
    wz1PaperRefinementFraction delta 10 *
        concreteLedger.totalLoss ≤ 1 := by
  let bounds :=
    pureWZ2Prop62ProxyQuotientGeometryMassBounds
      A eta c0 depthBound Color baseStructural
        baseStructural_ne_top
  have delta_le_one :
      delta ≤ 1 := by
    exact delta_le.trans <|
      (pureWZ2Prop62ProxyQuotientMassThreshold_le_one_hundred
        A eta c0 bounds).trans (by norm_num)
  have upperColorBound :
      concreteLedger.upperColorLoss ≤ bounds.strongUpperVector := by
    rw [upper_loss_eq]
    exact adapter.global.upperColorLoss_le_depthBound depth_le
  have selectedFineCardLe :
      metric.selectedFine.card ≤ fine.card := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective
        metric.mesh.complete.selectedFine.embedding
        metric.mesh.complete.selectedFine.embedding.injective
  have selectedFineCardLeDouble :
      metric.selectedFine.card ≤ 2 * fine.card := by
    omega
  have fineCardPositive : 0 < fine.card := fineNonempty
  have fineCardBound :
      fine.card ≤
        (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by
    have localBound :=
      wz2PaperOrdinary_local_six_grid_card_bound
        delta_pos (show (0 : ℝ) ≤ 5 by norm_num)
        schedule.fine_distinct Finset.univ (0 : Point3) <| by
          intro source _
          simpa [dist_zero_right] using
            PureWZ2Prop62AncestryMetricPreliminaryOutput.fine_midpoint_norm_le_five
              (fine := fine) fineBoundedBase source
    have firstArgument :
        5 / (delta / 64) = 320 / delta := by
      field_simp [delta_pos.ne']
      norm_num
    have secondArgument :
        1 / (delta / 64) ≤ 320 / delta := by
      have identity :
          1 / (delta / 64) = 64 / delta := by
        field_simp [delta_pos.ne']
      rw [identity]
      exact div_le_div_of_nonneg_right (by norm_num) delta_pos.le
    have firstCeil :
        Nat.ceil (5 / (delta / 64)) =
          Nat.ceil (320 / delta) := by
      rw [firstArgument]
    have secondCeil :
        Nat.ceil (1 / (delta / 64)) ≤
          Nat.ceil (320 / delta) :=
      Nat.ceil_mono secondArgument
    simpa only [Finset.card_univ, Fintype.card_fin] using
      localBound.trans <| by
        rw [firstCeil]
        calc
          (2 * Nat.ceil (320 / delta) + 1) ^ 3 *
                (2 * Nat.ceil (1 / (delta / 64)) + 1) ^ 3 ≤
              (2 * Nat.ceil (320 / delta) + 1) ^ 3 *
                (2 * Nat.ceil (320 / delta) + 1) ^ 3 := by
            gcongr
          _ = (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by
            ring
  have ambientLogReal :=
    pureWZ2Prop62_ordinary_card_log_bound
      delta_pos delta_le_one fineCardPositive fineCardBound
  have ambientLogENN :
      (Nat.log 2 (2 * fine.card) + 1 : ENNReal) ≤
        ENNReal.ofReal
          (pureWZ2Prop62OrdinaryCardLogConstant *
            (1 + Real.log delta⁻¹)) := by
    have converted := ENNReal.ofReal_mono ambientLogReal
    have castEq :
        ENNReal.ofReal
            (Nat.log 2 (2 * fine.card) + 1 : ℝ) =
          (Nat.log 2 (2 * fine.card) + 1 : ENNReal) := by
      rw [ENNReal.ofReal_add (by positivity)]
      norm_num
      positivity
    rwa [castEq] at converted
  have fiberLogLe :
      Nat.log 2 metric.selectedFine.card + 1 ≤
        Nat.log 2 (2 * fine.card) + 1 :=
    Nat.add_le_add_right
      (Nat.log_mono_right selectedFineCardLeDouble) 1
  have fiberBinBound :
      concreteLedger.fiberBinLoss ≤
        ENNReal.ofReal
          (bounds.fiberBinCoefficient *
            (1 + Real.log delta⁻¹)) := by
    rw [concreteLedger.fiberBinLoss_eq,
      adapter.preCore.retention.fiberBinLoss_eq]
    calc
      (Nat.log 2 metric.selectedFine.card + 1 : ENNReal) ≤
          (Nat.log 2 (2 * fine.card) + 1 : ENNReal) := by
        exact_mod_cast fiberLogLe
      _ ≤
          ENNReal.ofReal
            (pureWZ2Prop62OrdinaryCardLogConstant *
              (1 + Real.log delta⁻¹)) :=
        ambientLogENN
      _ =
          ENNReal.ofReal
            (bounds.fiberBinCoefficient *
              (1 + Real.log delta⁻¹)) := by
        rfl
  have sourceColorBound :
      concreteLedger.sourceColorLoss ≤ bounds.sourceColor := by
    rw [concreteLedger.sourceColorLoss_eq,
      adapter.preCore.retention.sourceColorLoss_eq]
    rfl
  have colorSelectedCardLe :
      adapter.preCore.leafBin.colorSelected.card ≤ fine.card :=
    by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card
          (Finset.subset_univ adapter.preCore.leafBin.colorSelected)
  have doubledColorSelectedCardLe :
      2 * adapter.preCore.leafBin.colorSelected.card ≤
        2 * fine.card := by
    omega
  have leafLogLe :
      adapter.preCore.leafBin.dyadicBinCount ≤
        Nat.log 2 (2 * fine.card) + 1 := by
    rw [adapter.preCore.leafBin.dyadicBinCount_eq]
    exact
      Nat.add_le_add_right
        (Nat.log_mono_right doubledColorSelectedCardLe) 1
  have leafBinBound :
      concreteLedger.leafBinLoss ≤
        ENNReal.ofReal
          (bounds.leafBinCoefficient *
            (1 + Real.log delta⁻¹)) := by
    rw [concreteLedger.leafBinLoss_eq,
      adapter.preCore.retention.leafBinLoss_eq]
    have doubledAmbientLog :
        (2 * (Nat.log 2 (2 * fine.card) + 1) : ENNReal) ≤
          2 *
            ENNReal.ofReal
              (pureWZ2Prop62OrdinaryCardLogConstant *
                (1 + Real.log delta⁻¹)) := by
      gcongr
    calc
      (2 * adapter.preCore.leafBin.dyadicBinCount : ENNReal) ≤
          (2 * (Nat.log 2 (2 * fine.card) + 1) : ENNReal) := by
        exact_mod_cast Nat.mul_le_mul_left 2 leafLogLe
      _ ≤
          2 *
            ENNReal.ofReal
              (pureWZ2Prop62OrdinaryCardLogConstant *
                (1 + Real.log delta⁻¹)) :=
        doubledAmbientLog
      _ =
          ENNReal.ofReal
            ((2 * pureWZ2Prop62OrdinaryCardLogConstant) *
              (1 + Real.log delta⁻¹)) := by
        rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num]
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      _ =
          ENNReal.ofReal
            (bounds.leafBinCoefficient *
              (1 + Real.log delta⁻¹)) := by
        rfl
  have cleanupBound :
      concreteLedger.cleanupLoss ≤ bounds.weightedCleanup := by
    rw [concreteLedger.cleanupLoss_eq]
    exact pow_le_pow_right₀ (by norm_num) <| by omega
  exact
    (Classical.choose_spec <|
      exists_pureWZ2Prop62ProxyQuotientMassAbsorption
        A eta c0 bounds).2.2
      delta_pos delta_le concreteLedger.totalLoss_eq
      base_structural_bound upperColorBound fiberBinBound
      sourceColorBound leafBinBound cleanupBound

/--
Caller-anchored specialization.  The cleanup loss is bounded using the
geometric schedule's public level-count bound, so no separate depth estimate
is required from the caller.
-/
theorem final_refinement_absorption_of_anchored_ledger_geometry
    {A : ℕ} {eta c0 delta rho K : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (deltaLtOne : delta < 1)
    (stepPos : 0 < pureWZ2Prop62CallerStep A eta)
    (separation :
      4 * ambientConstant.toReal ≤
        Real.rpow delta (-pureWZ2Prop62CallerStep A eta))
    (anchored :
      PureWZ2Prop62CallerAnchoredScheduleData
        (rho := rho) (K := K)
        (R := Real.rpow delta (-pureWZ2Prop62CallerStep A eta))
        ambient
        (pureWZ2Prop62RequestedScaleSchedule
          delta (pureWZ2Prop62CallerStep A eta) ambientConstant
            ambient.1 deltaLtOne stepPos separation))
    {anchoredFineNonempty : fine.Nonempty}
    {anchoredQuotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        anchored.laminar anchoredFineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin anchored.laminar.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    {metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) anchored.laminar anchoredFineNonempty
          anchoredQuotient width
          packetCoordinate strideBase weight}
    {Color : Type*}
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    {sourceColor : Fin fine.card → Color}
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := anchoredQuotient) rho packetCoordinate}
    (adapter :
      PureWZ2Prop62ProxyQuotientPreCoreAdapterData
        anchored.laminar anchoredFineNonempty anchoredQuotient
        width packetCoordinate strideBase weight metric coloring
        Color sourceColor)
    {adapterPreliminarySubsetSelection :
      adapter.preCore.preliminary ⊆
        (anchoredQuotient.selectProxyResidueUpperAncestryPerCell
          rho width packetCoordinate strideBase weight).selected}
    {adapterReceipt :
      PureWZ2Prop62CleanupReceipt
        (pureWZ2Prop62ProxyQuotientAuxiliaryLevel
          anchored.laminar anchoredFineNonempty anchoredQuotient rho width
            packetCoordinate).tree
        adapter.preCore.preliminary}
    {metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) anchored.laminar anchoredFineNonempty
          anchoredQuotient width packetCoordinate strideBase weight}
    (concreteLedger :
      PureWZ2Prop62ProxyQuotientMassLedger
        anchored.laminar anchoredFineNonempty anchoredQuotient
        width packetCoordinate strideBase weight metric Finset.univ
        adapter.global.selectedParents
        metric.ambientCompleteMetricFiber
        (fun parent =>
          (metric.ambientCompleteMetricFiber parent).card)
        metric.metricParentWeight metric.ambientMetricParentOf
        sourceColor metric.selectedFine.card adapter.preCore
        adapterPreliminarySubsetSelection adapterReceipt metricCore)
    (upper_loss_eq :
      concreteLedger.upperColorLoss =
        adapter.global.upperColorLoss)
    (baseStructural : ENNReal)
    (baseStructural_ne_top : baseStructural ≠ ⊤)
    (delta_pos : 0 < delta)
    (delta_le :
      delta ≤
        pureWZ2Prop62ProxyQuotientMassThreshold
          A eta c0
            (pureWZ2Prop62ProxyQuotientGeometryMassBounds
              A eta c0
                (Nat.ceil (1 / (2 * (A : ℝ) * eta)) + 2)
                Color baseStructural baseStructural_ne_top))
    (fineBoundedBase : HasBoundedBase fine 4)
    (base_structural_bound :
      concreteLedger.baseSelectionLoss ≤ baseStructural) :
    wz1PaperRefinementFraction delta 10 *
        concreteLedger.totalLoss ≤ 1 := by
  apply concreteLedger.final_refinement_absorption_of_ledger_geometry
    (Nat.ceil (1 / (2 * (A : ℝ) * eta)) + 2)
    baseStructural baseStructural_ne_top adapter upper_loss_eq
    delta_pos delta_le
  · exact
      (pureWZ2Prop62CallerAnchoredScheduleData_geometric_levelCount_le
        ambient deltaLtOne stepPos separation anchored).trans_eq <| by
          rw [pureWZ2Prop62CallerStep_eq]
  · exact fineBoundedBase
  · exact base_structural_bound

/--
Ledger specialization of the uniform small-scale certificate.  Each of the
six factors is named separately, and `ledger.totalLoss_eq` ensures that the
single cleanup factor is used exactly once.
-/
theorem final_refinement_absorption_of_smallDelta
    {A : ℕ} {eta c0 : ℝ}
    (bounds :
      PureWZ2Prop62ProxyQuotientMassFixedBounds A eta c0)
    (delta0 : ℝ)
    (certificate :
      0 < delta0 ∧
      delta0 ≤ 1 / 100 ∧
      ∀ {scale : ℝ},
        0 < scale →
        scale ≤ delta0 →
        ∀ {baseLoss upperColorLoss fiberBinLoss
            sourceColorLoss leafBinLoss cleanupLoss totalLoss : ENNReal},
          totalLoss =
              baseLoss * upperColorLoss * fiberBinLoss *
                sourceColorLoss * leafBinLoss * cleanupLoss →
          baseLoss ≤ bounds.baseStructural →
          upperColorLoss ≤ bounds.strongUpperVector →
          fiberBinLoss ≤
            ENNReal.ofReal
              (bounds.fiberBinCoefficient *
                (1 + Real.log scale⁻¹)) →
          sourceColorLoss ≤ bounds.sourceColor →
          leafBinLoss ≤
            ENNReal.ofReal
              (bounds.leafBinCoefficient *
                (1 + Real.log scale⁻¹)) →
          cleanupLoss ≤ bounds.weightedCleanup →
          wz1PaperRefinementFraction scale 10 * totalLoss ≤ 1)
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ delta0)
    (base_structural_bound :
      ledger.baseSelectionLoss ≤ bounds.baseStructural)
    (strong_upper_vector_bound :
      ledger.upperColorLoss ≤ bounds.strongUpperVector)
    (DMinus_bin_bound :
      ledger.fiberBinLoss ≤
        ENNReal.ofReal
          (bounds.fiberBinCoefficient *
            (1 + Real.log delta⁻¹)))
    (source_color_bound :
      ledger.sourceColorLoss ≤ bounds.sourceColor)
    (leaf_bin_bound :
      ledger.leafBinLoss ≤
        ENNReal.ofReal
          (bounds.leafBinCoefficient *
            (1 + Real.log delta⁻¹)))
    (weighted_cleanup_bound :
      ledger.cleanupLoss ≤ bounds.weightedCleanup) :
    wz1PaperRefinementFraction delta 10 *
        ledger.totalLoss ≤ 1 := by
  exact
    certificate.2.2 delta_pos delta_le ledger.totalLoss_eq
      base_structural_bound strong_upper_vector_bound
      DMinus_bin_bound source_color_bound leaf_bin_bound
      weighted_cleanup_bound

/-- Apply the canonical threshold without manually carrying its specification. -/
theorem final_refinement_absorption_of_le_threshold
    {A : ℕ} {eta c0 : ℝ}
    (bounds :
      PureWZ2Prop62ProxyQuotientMassFixedBounds A eta c0)
    (delta_pos : 0 < delta)
    (delta_le :
      delta ≤
        pureWZ2Prop62ProxyQuotientMassThreshold
          A eta c0 bounds)
    (base_structural_bound :
      ledger.baseSelectionLoss ≤ bounds.baseStructural)
    (strong_upper_vector_bound :
      ledger.upperColorLoss ≤ bounds.strongUpperVector)
    (DMinus_bin_bound :
      ledger.fiberBinLoss ≤
        ENNReal.ofReal
          (bounds.fiberBinCoefficient *
            (1 + Real.log delta⁻¹)))
    (source_color_bound :
      ledger.sourceColorLoss ≤ bounds.sourceColor)
    (leaf_bin_bound :
      ledger.leafBinLoss ≤
        ENNReal.ofReal
          (bounds.leafBinCoefficient *
            (1 + Real.log delta⁻¹)))
    (weighted_cleanup_bound :
      ledger.cleanupLoss ≤ bounds.weightedCleanup) :
    wz1PaperRefinementFraction delta 10 *
        ledger.totalLoss ≤ 1 := by
  exact
    (Classical.choose_spec <|
      exists_pureWZ2Prop62ProxyQuotientMassAbsorption
        A eta c0 bounds).2.2
      delta_pos delta_le ledger.totalLoss_eq
      base_structural_bound strong_upper_vector_bound
      DMinus_bin_bound source_color_bound leaf_bin_bound
      weighted_cleanup_bound

end PureWZ2Prop62ProxyQuotientMassLedger

end Kakeya.Assouad

end
