import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallFinalCandidateAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteIntervalCoveringIteration
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63AlignedInnerIntervalGrid
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPairMass
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Exact M5 callback bridge for one ordered pair

The caller supplies only an available four-call runtime and the four scalar
receipts produced by M4.  The nested cover and ancestry pullback are selected
internally as fields of that runtime.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- Fixed combinatorial cost in the nested interval cover after cancelling
the three positive query-scale quotients. -/
noncomputable def proposition63NestedIntervalCoefficient (K : ℝ) : ENNReal :=
  (((2 * Nat.ceil (Real.sqrt 3) + 2) * 5 *
      (2 * Nat.ceil (8 * K) + 2) * (13 ^ 3) * 5 * 4 * 9 *
      (2 * Nat.ceil (2 * K) + 2) : ℕ) : ENNReal)

/-- Family-free pre-runtime absorption of the fixed nested-cover coefficient. -/
structure Proposition63NestedIntervalAbsorptionData
    (K : ℝ) (firstConstant : ENNReal) (discreteLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    proposition63NestedIntervalCoefficient K * firstConstant ≤
      Kakeya.realRpowENN delta (-discreteLoss)

theorem proposition63_nested_interval_absorption
    (K : ℝ) (firstConstant : ENNReal)
    (hfirstConstantFinite : firstConstant ≠ ⊤)
    {discreteLoss : ℝ} (hdiscreteLoss : 0 < discreteLoss) :
    Nonempty (Proposition63NestedIntervalAbsorptionData
      K firstConstant discreteLoss) := by
  have hcoefficientFinite :
      proposition63NestedIntervalCoefficient K ≠ ⊤ := by
    unfold proposition63NestedIntervalCoefficient
    exact ENNReal.coe_ne_top
  rcases exists_delta_realRpowENN_bound
      (proposition63NestedIntervalCoefficient K * firstConstant)
      (ENNReal.mul_ne_top hcoefficientFinite hfirstConstantFinite)
      hdiscreteLoss with
    ⟨delta₀, hdelta₀, hdelta₀One, habsorb⟩
  exact ⟨{ delta₀ := delta₀
           delta₀_pos := hdelta₀
           delta₀_le_one := hdelta₀One
           absorb := fun hdelta hsmall => habsorb _ hdelta hsmall }⟩

theorem proposition63_nestedCandidateIntervalBound_le_paper
    {fineDelta rho tau sigma discreteLoss : ℝ}
    (K : ℝ) (firstConstant : ENNReal)
    (absorption : Proposition63NestedIntervalAbsorptionData
      K firstConstant discreteLoss)
    (hfineDelta : 0 < fineDelta)
    (hfineSmall : fineDelta ≤ absorption.delta₀)
    (hrho : 0 < rho) :
    Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound
        rho rho (8 * K * rho) K (13 ^ 3)
        (firstConstant * Kakeya.realRpowENN (tau / rho) (1 - sigma)) ≤
      ENNReal.ofReal (Real.rpow fineDelta (-discreteLoss) *
        Real.rpow (tau / rho) (1 - sigma)) := by
  have hsqrt : (rho * Real.sqrt 3) / rho = Real.sqrt 3 := by
    field_simp [hrho.ne']
  have hnormal : (8 * K * rho) / rho = 8 * K := by
    field_simp [hrho.ne']
  have hcell : (2 * K * rho) / rho = 2 * K := by
    field_simp [hrho.ne']
  have hfixed := absorption.absorb hfineDelta hfineSmall
  calc
    Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound
          rho rho (8 * K * rho) K (13 ^ 3)
          (firstConstant * Kakeya.realRpowENN (tau / rho) (1 - sigma)) =
        (proposition63NestedIntervalCoefficient K * firstConstant) *
          Kakeya.realRpowENN (tau / rho) (1 - sigma) := by
      simp only [
        Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound,
        Proposition63NestedPointCoverData.FullGrainCells.nestedRegionIntervalBound,
        Proposition63NestedPointCoverData.FullGrainCells.nestedCellIntervalBound,
        hsqrt, hnormal, hcell, proposition63NestedIntervalCoefficient]
      push_cast
      ring
    _ ≤ Kakeya.realRpowENN fineDelta (-discreteLoss) *
          Kakeya.realRpowENN (tau / rho) (1 - sigma) :=
      by gcongr
    _ = ENNReal.ofReal (Real.rpow fineDelta (-discreteLoss) *
          Real.rpow (tau / rho) (1 - sigma)) := by
      exact (ENNReal.ofReal_mul
        (Real.rpow_nonneg hfineDelta.le (-discreteLoss))).symm

/-- The terminal prepared shading inherits unit norm from the fixed call-one
plane map through the exact M3 ancestry chain. -/
theorem Proposition63FourCallRuntimeAssemblyData.plane_unit_on_prepared
    {delta sigma inputLoss normalizationLoss outputLoss tau firstLoss
      secondLoss finalLoss incidence fineReentryLoss : ℝ}
    {fineSource : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {fineNormalizationExponent : ℕ}
    {fineNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) fineSource fineNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading fineNormalized.croppedFamily}
    {fineCurrentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) fineNormalized fineCurrent}
    {schedule : Proposition63RichFourCallScheduleData sigma outputLoss}
    {hfineReentryLoss : 0 < fineReentryLoss}
    {rho : WZ2PaperRequestedScale delta}
    {rootAxialWindow : ∀ index point,
      point ∈ (fineCurrentReentry.normalization.toPropStickyReentryData
          hfineReentryLoss
          fineCurrentReentry.reentry_normalization_loss_pos).geometry.frame ''
          (fineCurrentReentry.normalization.toPropStickyReentryData
            hfineReentryLoss
            fineCurrentReentry.reentry_normalization_loss_pos).geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8}
    {sourceCoefficient : NNReal}
    {robustScale targetScale sqrtRequested : WZ2PaperRequestedScale rho.1}
    {firstConstant finalConstant : ENNReal}
    (runtime : Proposition63FourCallRuntimeAssemblyData
      (tau := tau) (firstLoss := firstLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (incidence := incidence)
      fineCurrentReentry schedule hfineReentryLoss rho rootAxialWindow
      sourceCoefficient robustScale targetScale sqrtRequested
      firstConstant finalConstant) :
    ∀ point ∈ runtime.nested.prepared.refined.shading.union,
      ‖runtime.currentMap.planeMap point‖ = 1 := by
  intro point hpoint
  apply runtime.currentMap.unit point
  apply runtime.currentReentry.normalization_croppedRefined_union_subset_current
  have htarget : point ∈ runtime.target.data.refined.union := by
    rw [← extendShading_union runtime.target.data.selected]
    rw [← runtime.nested_eq]
    exact runtime.nested.prepared_union_subset_current hpoint
  have htargetNormalized :
      point ∈ runtime.targetReentry.normalization.croppedRefined.union :=
    refined_union_subset_shading runtime.target.data htarget
  have houterAmbient : point ∈
      (extendShading runtime.outer.data.selected runtime.outer.data.refined).union :=
    runtime.targetReentry.normalization_croppedRefined_union_subset_current
      htargetNormalized
  have houter : point ∈ runtime.outer.data.refined.union := by
    simpa only [extendShading_union runtime.outer.data.selected] using houterAmbient
  exact refined_union_subset_shading runtime.outer.data houter

/-- Construct the final plane-cover receipt from the fixed coefficient and
the Lipschitz certificate already produced by M3.  The remaining premises
are scalar cover-budget and scale inequalities. -/
noncomputable def Proposition63FourCallRuntimeAssemblyData.planeCoverReceipt
    {delta sigma inputLoss normalizationLoss outputLoss tau firstLoss
      secondLoss finalLoss incidence fineReentryLoss : ℝ}
    {fineSource : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {fineNormalizationExponent : ℕ}
    {fineNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) fineSource fineNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading fineNormalized.croppedFamily}
    {fineCurrentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) fineNormalized fineCurrent}
    {schedule : Proposition63RichFourCallScheduleData sigma outputLoss}
    {hfineReentryLoss : 0 < fineReentryLoss}
    {rho : WZ2PaperRequestedScale delta}
    {rootAxialWindow : ∀ index point,
      point ∈ (fineCurrentReentry.normalization.toPropStickyReentryData
          hfineReentryLoss
          fineCurrentReentry.reentry_normalization_loss_pos).geometry.frame ''
          (fineCurrentReentry.normalization.toPropStickyReentryData
            hfineReentryLoss
            fineCurrentReentry.reentry_normalization_loss_pos).geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8}
    {sourceCoefficient : NNReal}
    {robustScale targetScale sqrtRequested : WZ2PaperRequestedScale rho.1}
    {firstConstant finalConstant : ENNReal}
    (runtime : Proposition63FourCallRuntimeAssemblyData
      (tau := tau) (firstLoss := firstLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (incidence := incidence)
      fineCurrentReentry schedule hfineReentryLoss rho rootAxialWindow
      sourceCoefficient robustScale targetScale sqrtRequested
      firstConstant finalConstant)
    (hcoefficientOne : 1 ≤
      (((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ))
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget : (512 : ENNReal) *
      ((2 * Nat.ceil (2 *
          (((4 : NNReal) *
            (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)) + 2 :
          ENNReal) *
        (finalConstant * Kakeya.realRpowENN
          (sqrtRequested.1 / rho.1) (1 - sigma))) ≤
      (coverBudget : ENNReal))
    (hsqrtConstantFinite : finalConstant * Kakeya.realRpowENN
      (sqrtRequested.1 / rho.1) (1 - sigma) ≠ ⊤)
    (hnormalErrorTau : 8 *
      (((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ) *
        rho.1 ≤ tau)
    (hhullTau : rho.1 * Real.sqrt 3 ≤ tau) :
    Proposition63FourCallPlaneCoverReceipt runtime.currentMap.planeMap
      runtime.nested.prepared.refined.shading.union rho.1 tau
      (finalConstant * Kakeya.realRpowENN
        (sqrtRequested.1 / rho.1) (1 - sigma)) :=
  { plane_unit := runtime.plane_unit_on_prepared
    coefficient := 4 *
      (lipschitzExtensionConstant Point3 * sourceCoefficient)
    coefficient_one := hcoefficientOne
    plane_lipschitz := runtime.currentLipschitz
    coverBudget := coverBudget
    coverBudget_pos := hcoverBudgetPos
    cover_budget := hcoverBudget
    sqrtConstant_finite := hsqrtConstantFinite
    normalErrorTau := hnormalErrorTau
    hullTau := hhullTau }

/-- Turn the M4 receipts for the runtime selected at one ordered grid pair
into exactly the callback result consumed by
`Proposition63InnerIntervalGridData.runIteration`. -/
theorem proposition63_four_call_ordered_pair_step
    {delta sigma inputLoss normalizationLoss outputLoss tau firstLoss
      secondLoss finalLoss incidence fineReentryLoss discreteLoss
      intervalLoss gridOutputLoss queryScale : ℝ}
    {fineSource : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {fineNormalizationExponent : ℕ}
    {fineNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) fineSource fineNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading fineNormalized.croppedFamily}
    {fineCurrentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) fineNormalized fineCurrent}
    {schedule : Proposition63RichFourCallScheduleData sigma outputLoss}
    {hfineReentryLoss : 0 < fineReentryLoss}
    {rho : WZ2PaperRequestedScale delta}
    {rootAxialWindow : ∀ index point,
      point ∈ (fineCurrentReentry.normalization.toPropStickyReentryData
          hfineReentryLoss
          fineCurrentReentry.reentry_normalization_loss_pos).geometry.frame ''
          (fineCurrentReentry.normalization.toPropStickyReentryData
            hfineReentryLoss
            fineCurrentReentry.reentry_normalization_loss_pos).geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8}
    {sourceCoefficient : NNReal}
    {robustScale targetScale sqrtRequested : WZ2PaperRequestedScale rho.1}
    {firstConstant finalConstant : ENNReal}
    {gridN index : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (loss : ℕ → ℝ) (leftFactor rightFactor : ℕ → ENNReal)
    (hindex : index < (finiteIntervalOrderedPairs gridN).length)
    (runtime : Proposition63FourCallRuntimeAssemblyData
      (tau := tau) (firstLoss := firstLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (incidence := incidence)
      fineCurrentReentry schedule hfineReentryLoss rho rootAxialWindow
      sourceCoefficient robustScale targetScale sqrtRequested
      firstConstant finalConstant)
    (criticalInputs : Proposition63FourCallCriticalTailInputs
      runtime)
    (planeInputs : Proposition63FourCallPlaneCoverReceipt
      runtime.currentMap.planeMap
      runtime.nested.prepared.refined.shading.union
      rho.1 tau
      (finalConstant * Kakeya.realRpowENN
        (sqrtRequested.1 / rho.1) (1 - sigma)))
    (currentInputs : Proposition63FourCallCurrentReceipt
      (sigma := sigma) fineCurrent rho.1)
    (massInputs : Proposition63FourCallMassReceipt
      (Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound
        rho.1 rho.1
          (8 * (planeInputs.coefficient : ℝ) * rho.1)
          (planeInputs.coefficient : ℝ) (13 ^ 3)
          (firstConstant * Kakeya.realRpowENN (tau / rho.1) (1 - sigma)))
      (proposition63DependentFinePullbackLeft fineCurrentReentry
        runtime.rich1.data runtime.pullback.retentionFactor
        (ENNReal.ofReal ((criticalInputs.cellVolumeFloor / 2) /
            (4 * (2 * sqrtRequested.1) ^ 2)) *
          (((1 : ENNReal) / 2) / (2 * (planeInputs.coverBudget : ENNReal))) *
          (runtime.nested.secondRetainedFactor *
            ((73 / 100 : ENNReal) *
              runtime.nested.reentry.normalizationWeight) *
            runtime.nested.firstRetainedFactor)))
      (proposition63DependentFinePullbackRight fineCurrentReentry
        ((runtime.nested.reentry.regularized.regularizationLoss *
            runtime.nested.prepared.preparationLoss) *
          (2 * ENNReal.ofReal (4 * rho.1))))
      delta criticalInputs.outputCandidateLoss currentInputs.fineCurrentLoss
      planeInputs.coefficient criticalInputs.spatialScale
      criticalInputs.variationScale)
    (hlogicalRho_le :
      (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) ≤ rho.1)
    (hrho_le_two : rho.1 ≤
      2 * (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ))
    (htau : tau =
      (grid.scale (finiteIntervalOrderedPair gridN index).2 : ℝ))
    (hnextLoss : criticalInputs.outputCandidateLoss = loss (index + 1))
    (hconstant : 2 * massInputs.targetConstant ≤
      proposition63FourCallOrderedPairConstant grid index)
    (hleft : massInputs.targetLeft = leftFactor index)
    (hright : massInputs.targetRight = rightFactor index) :
    ∃ next : WZ1PaperTubeShading fineNormalized.croppedFamily,
      PaperIsSubshading next fineCurrent ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union, next.pointMultiplicity point =
        fineCurrent.pointMultiplicity point) ∧
      WZ2PaperCroppedIsExtremal sigma (loss (index + 1))
        fineNormalized.croppedFamily next ∧
      WZ2PaperConvexWolffBound fineNormalized.croppedFamily
        (Kakeya.realRpowENN delta (-(loss (index + 1)))) ∧
      PureWZ2IntervalCoveringAt next
        runtime.currentMap.planeMap
        (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
        (grid.scale (finiteIntervalOrderedPair gridN index).1)
        (grid.scale (finiteIntervalOrderedPair gridN index).2)
        (ENNReal.ofReal
          (Real.rpow delta (-discreteLoss) *
            Real.rpow
              ((grid.scale (finiteIntervalOrderedPair gridN index).2 : ℝ) /
                (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ))
              (1 - sigma))) ∧
      leftFactor index * fineCurrent.mass ≤ rightFactor index * next.mass := by
  have hpair := finiteIntervalOrderedPair_valid hindex
  have hkLe : (finiteIntervalOrderedPair gridN index).1 ≤ gridN :=
    hpair.1.le.trans hpair.2
  have hkPos := grid.scale_pos _ hkLe
  have hjPos := grid.scale_pos _ hpair.2
  have hkNN : Real.toNNReal
      (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) =
        grid.scale (finiteIntervalOrderedPair gridN index).1 := by
    ext
    exact Real.coe_toNNReal _ hkPos.le
  have hjNN : Real.toNNReal
      (grid.scale (finiteIntervalOrderedPair gridN index).2 : ℝ) =
        grid.scale (finiteIntervalOrderedPair gridN index).2 := by
    ext
    exact Real.coe_toNNReal _ hjPos.le
  rcases runtime.finalCandidate criticalInputs planeInputs currentInputs
      massInputs with
    ⟨next, hsub, hcubical, hmultiplicity, hextremal, hcwa, hcover, hmass, _⟩
  have hlogicalNN :
      grid.scale (finiteIntervalOrderedPair gridN index).1 ≤
        Real.toNNReal rho.1 := by
    change (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) ≤
      (Real.toNNReal rho.1 : ℝ)
    simpa only [Real.coe_toNNReal _ criticalInputs.query_pos.le] using
      hlogicalRho_le
  have hrhoNNTwo : Real.toNNReal rho.1 ≤
      2 * grid.scale (finiteIntervalOrderedPair gridN index).1 := by
    change (Real.toNNReal rho.1 : ℝ) ≤
      2 * (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
    simpa only [Real.coe_toNNReal _ criticalInputs.query_pos.le] using
      hrho_le_two
  have htransport :=
    pureWZ2IntervalCoveringAt_mono_query_refine_resolution_two
      hlogicalRho_le hkPos hlogicalNN hrhoNNTwo hcover
  have hcoverTarget := pureWZ2IntervalCoveringAt_mono_constant
    hconstant htransport
  refine ⟨next, hsub, hcubical, hmultiplicity, ?_, ?_, ?_, ?_⟩
  · simpa only [hnextLoss] using hextremal
  · simpa only [hnextLoss] using hcwa
  · simpa only [htau, hjNN, proposition63FourCallOrderedPairConstant] using
      hcoverTarget
  · simpa only [hleft, hright] using hmass

end Kakeya.Assouad.PureWZ2
