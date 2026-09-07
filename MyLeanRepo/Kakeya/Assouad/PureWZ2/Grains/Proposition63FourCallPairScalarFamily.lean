import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallFrozenChoiceProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallInnerMassSchedule

/-!
# Fixed-delta pair-scalar family for the Proposition 6.3 four-call schedule

Every ordered pair receives its scale package, square-root and robust requested
scales, and pair-local scalar core before runtime.  The resulting exact factor
functions feed the existing common-cutoff mass-schedule constructor.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- All scalar data canonically chosen for one ordered-pair index. -/
structure Proposition63FourCallPairScalarDataAt
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale
      incidence : ℝ}
    {gridN : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (sourceCoefficient : NNReal)
    (index : ℕ)
    (hindex : index < (finiteIntervalOrderedPairs gridN).length) where
  scales : Proposition63FourCallOrderedPairIndexScales grid index
  sqrtPackage : Proposition63FourCallFrozenChoiceSqrtScalePackage
    (backward.loss (index + 1)) scales
  robustPackage : Proposition63FourCallFrozenRobustScalePackage
    (backward.seed index hindex) scales
  core : Proposition63FourCallPairScalarCoreAt grid backward.loss
    (backward.seed index hindex) sourceCoefficient incidence
    backward.rootNormalizationLoss scales sqrtPackage.sqrtRequested
    robustPackage.requested

/-- Complete fixed-delta scalar and mass data.  The actual mass schedule remains
explicitly conditional on the current `delta` lying below the common cutoff. -/
structure Proposition63FourCallPairScalarFamilyData
    {delta sigma inputLoss discreteLoss intervalLoss gridOutputLoss queryScale
      incidence : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (sourceCoefficient : NNReal) where
  pair : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
    Proposition63FourCallPairScalarDataAt (incidence := incidence) backward grid
      sourceCoefficient index hindex
  massSeed : ∀ index (_hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
    Proposition63FourCallInnerMassSeedAt root grid
      (backward.loss index) (backward.loss (index + 1)) index
  massCutoff : Proposition63FourCallInnerMassFamilyCutoff
    (finiteIntervalOrderedPairs gridN).length
    (fun index hindex => (massSeed index hindex).absorption.delta₀)
  uniformMassSchedule : delta ≤ massCutoff.delta₀ →
    Proposition63FourCallUniformMassSchedule grid backward.loss
      (proposition63FourCallInnerLeftFactor
        (loss := backward.loss) massSeed)
      (proposition63FourCallInnerRightFactor
        (loss := backward.loss) massSeed)

/-- Construct the complete fixed-delta pair-scalar family and its common mass
cutoff.  The cutoff premise is retained in the returned schedule field. -/
theorem proposition63_four_call_pair_scalar_family
    {delta sigma inputLoss discreteLoss intervalLoss gridOutputLoss queryScale
      incidence : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (sourceCoefficient : NNReal)
    (delta_pos : 0 < delta)
    (delta_lt_one : delta < 1)
    (sigma_lt_one : sigma < 1)
    (discreteLoss_pos : 0 < discreteLoss)
    (discreteLoss_lt_half : discreteLoss < 1 / 2)
    (query_small : 2 * Real.rpow queryScale (discreteLoss / 2) ≤ 1)
    (delta_le_query : delta ≤ queryScale)
    (sqrt_query_small : 2 * Real.sqrt queryScale ≤ 1)
    (outputLoss_le_half : gridOutputLoss ≤ 1 / 2)
    (rho_sqrt_small : ∀ index (_hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      ∀ scales : Proposition63FourCallOrderedPairIndexScales grid index,
        scales.rhoHat.1 ≤ 1 / 144)
    (rho_small : ∀ index (_hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      ∀ scales : Proposition63FourCallOrderedPairIndexScales grid index,
        scales.rhoHat.1 ≤ 1 / 24) :
    Nonempty (Proposition63FourCallPairScalarFamilyData (incidence := incidence)
      backward root grid sourceCoefficient) := by
  classical
  let pair : ∀ index (hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallPairScalarDataAt (incidence := incidence) backward grid
        sourceCoefficient index hindex := fun index hindex => by
    let scales := (grid.orderedPairIndexScales delta_pos discreteLoss_pos
      query_small delta_le_query sqrt_query_small hindex).some
    let sqrtPackage := scales.choiceSqrtScalePackage
      (backward.loss (index + 1))
      (backward.loss_pos (index + 1) (by omega))
      ((backward.loss_le_terminal (index + 1) (by omega)).trans
        outputLoss_le_half)
      (rho_sqrt_small index hindex scales)
    let robustPackage := scales.choiceRobustScalePackage
      (backward.seed index hindex) discreteLoss_lt_half
    let core := proposition63_four_call_pair_scalar_core backward.loss
      (backward.seed index hindex) sourceCoefficient incidence
      backward.rootNormalizationLoss scales sqrtPackage.sqrtRequested
      robustPackage.requested sigma_lt_one
    exact {
      scales := scales
      sqrtPackage := sqrtPackage
      robustPackage := robustPackage
      core := core
    }
  let scales := fun index hindex => (pair index hindex).scales
  let sqrtRequested := fun index hindex =>
    (pair index hindex).sqrtPackage.sqrtRequested
  let robustScale := fun index hindex =>
    (pair index hindex).robustPackage.requested
  let core := fun index hindex => (pair index hindex).core
  let massWitness := proposition63_four_call_uniform_mass_schedule_of_core
    backward root grid sourceCoefficient scales sqrtRequested robustScale core
    (fun index hindex => rho_small index hindex (scales index hindex))
    delta_pos delta_lt_one
  let massSeed := Classical.choose massWitness
  let cutoffWitness := Classical.choose_spec massWitness
  let massCutoff := Classical.choose cutoffWitness
  let schedule := Classical.choose_spec cutoffWitness
  refine ⟨{
    pair := pair
    massSeed := massSeed
    massCutoff := massCutoff
    uniformMassSchedule := schedule
  }⟩

end Kakeya.Assouad.PureWZ2
