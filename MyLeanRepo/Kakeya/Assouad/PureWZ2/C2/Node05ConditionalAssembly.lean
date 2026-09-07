import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.VerticalFinalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleStatements
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyPopularityAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyMixedPopularityAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleLossMonotonicity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyOrdinaryPrefix
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64Constants
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64Lemma35Scale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64PreparedLocalGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64Lemma35LocalCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64ThreeTubeCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureCubicalGlobalSlabAD

/-!
# Conditional assembly of pure WZ2 Node 5

This module isolates the two remaining paper-level producers.  All local
geometry, raw Proposition 27, analytic vertical normalization, and final AD
assembly sit behind these boundaries.  Neither producer is replaced by a
historical uniform tube structure.
-/

noncomputable section

namespace Kakeya.Assouad

/-- One arbitrarily small raw/normalized output before Lemma-8
rediscretization. -/
structure PureWZ2NormalizedHierarchyOutput
    (sigma workLoss sourceDelta : ℝ) where
  inputLoss : ℝ
  source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss sourceDelta
  hierarchyLoss : ℝ
  hierarchy :
    PureWZ2LocallyLinearHierarchyData
      source workLoss hierarchyLoss
  rawLoss : ℝ
  extensionConstant : ℝ
  raw :
    PureWZ2RawC2GlobalGrainData
      hierarchy.shading sigma
      (Kakeya.realRpowENN sourceDelta (-workLoss))
      rawLoss extensionConstant
  globalBounds : PureWZ2RawC2GlobalBoundData raw
  raw_global_slab_ad :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (globalGrainProjection raw.slope
          (globalGrainSlab hierarchy.shading.union z sourceDelta))
        sourceDelta (1 - sigma)
          (24000 * Kakeya.realRpowENN sourceDelta (-workLoss))
  prepared : PureWZ2Proposition64PreparedData hierarchy raw
  extensionConstant_eq :
    extensionConstant = pureWZ2Proposition64ExtensionConstant
  normalization_eq :
    prepared.normalization = pureWZ2Proposition64NormalizationConstant
  normalization_nine : 9 ≤ prepared.normalization
  halfHeight_small : prepared.slab.halfHeight ≤ 1 / 20
  halfHeight_slab_ad : prepared.slab.halfHeight ≤ 1 / 90
  lemma35_parameter_window :
    24000 * pureWZ2Proposition64NormalizationConstant *
        (45 * pureWZ2Proposition64Lemma35Scale) * sourceDelta ≤
      prepared.slab.halfHeight
  valueBudget :
    3 * prepared.slab.halfHeight * extensionConstant *
      Real.rpow sourceDelta (-rawLoss) ≤ prepared.normalization
  firstBudget :
    prepared.slab.halfHeight * extensionConstant *
      Real.rpow sourceDelta (-rawLoss) ≤ prepared.normalization
  secondBudget :
    prepared.slab.halfHeight ^ 2 * extensionConstant *
      Real.rpow sourceDelta (-rawLoss) ≤ prepared.normalization

/-- A normalized ordinary hierarchy together with the two quantitative
receipts that survive Corollary 5.6 popularity and compactification.  This is
kept separate from `PureWZ2NormalizedHierarchyOutput`: the mixed terminal
route does not furnish a global multiplicity band and must not be silently
strengthened. -/
structure PureWZ2QuantitativeNormalizedHierarchyOutput
    (sigma workLoss sourceDelta : ℝ) where
  densityLoss : ℝ
  quantitativeInputLoss : ℝ
  inputLoss_le_workLoss : quantitativeInputLoss ≤ workLoss
  quantitativeSource :
    PureWZ2QuantitativeGrainConfiguration sigma quantitativeInputLoss sourceDelta
  quantitativeHierarchyLoss : ℝ
  hierarchyLoss_pos : 0 < quantitativeHierarchyLoss
  quantitative :
    PureWZ2QuantitativeLocallyLinearHierarchyData quantitativeSource
      workLoss quantitativeHierarchyLoss densityLoss
  hierarchyLoss_upper :
    quantitativeHierarchyLoss ≤
      1 / (quantitative.hierarchy.hierarchy.levelCount : ℝ)
  normalized : PureWZ2NormalizedHierarchyOutput sigma workLoss sourceDelta
  inputLoss_eq : normalized.inputLoss = quantitativeInputLoss
  source_eq : HEq normalized.source quantitativeSource
  hierarchyLoss_eq :
    normalized.hierarchyLoss = quantitativeHierarchyLoss
  hierarchy_eq : HEq normalized.hierarchy quantitative.hierarchy
  normalized_mass_retention :
    ENNReal.ofReal (1 / 6) *
        (Kakeya.realRpowENN sourceDelta densityLoss *
          (wz1PaperBodyFamily normalized.source.family).mass) ≤
      normalized.hierarchy.shading.mass

/-- The exact height `delta^(3/N)` cancels the Proposition-5.7 loss
`1/N + 2 * hierarchyLoss` as soon as `hierarchyLoss ≤ 1/N`.  Thus the
normalizing factor is the fixed absolute constant `max 1 A`, independent of
the source scale. -/
private theorem pureWZ2_proposition64_fixed_normalization_budget
    {sourceDelta hierarchyLoss extensionConstant : ℝ} {levelCount : ℕ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceDeltaOne : sourceDelta ≤ 1)
    (hextensionConstant : 1 ≤ extensionConstant)
    (hhierarchyLoss : hierarchyLoss ≤ 1 / (levelCount : ℝ)) :
    3 * pureWZ2Proposition64HalfHeight sourceDelta levelCount *
        extensionConstant *
          Real.rpow sourceDelta
            (-(1 / (levelCount : ℝ) + 2 * hierarchyLoss)) ≤
      max 9 (3 * extensionConstant) := by
  have hexponent :
      0 ≤ 3 / (levelCount : ℝ) -
        (1 / (levelCount : ℝ) + 2 * hierarchyLoss) := by
    have hgap : 0 ≤ 1 / (levelCount : ℝ) - hierarchyLoss :=
      sub_nonneg.mpr hhierarchyLoss
    calc
      0 ≤ 2 * (1 / (levelCount : ℝ) - hierarchyLoss) :=
        mul_nonneg (by norm_num) hgap
      _ = 3 / (levelCount : ℝ) -
          (1 / (levelCount : ℝ) + 2 * hierarchyLoss) := by ring
  have hpower :
      Real.rpow sourceDelta
          (3 / (levelCount : ℝ) -
            (1 / (levelCount : ℝ) + 2 * hierarchyLoss)) ≤ 1 :=
    Real.rpow_le_one hsourceDelta.le hsourceDeltaOne hexponent
  have hcombine :
      Real.rpow sourceDelta (3 / (levelCount : ℝ)) *
          Real.rpow sourceDelta
            (-(1 / (levelCount : ℝ) + 2 * hierarchyLoss)) =
        Real.rpow sourceDelta
          (3 / (levelCount : ℝ) -
            (1 / (levelCount : ℝ) + 2 * hierarchyLoss)) := by
    calc
      _ = Real.rpow sourceDelta
          (3 / (levelCount : ℝ) +
            -(1 / (levelCount : ℝ) + 2 * hierarchyLoss)) :=
        (Real.rpow_add hsourceDelta _ _).symm
      _ = _ := by ring
  have hextensionNonneg : 0 ≤ extensionConstant :=
    zero_le_one.trans hextensionConstant
  calc
    3 * pureWZ2Proposition64HalfHeight sourceDelta levelCount *
          extensionConstant *
            Real.rpow sourceDelta
              (-(1 / (levelCount : ℝ) + 2 * hierarchyLoss)) =
        (3 / 2 : ℝ) * extensionConstant *
          (Real.rpow sourceDelta (3 / (levelCount : ℝ)) *
            Real.rpow sourceDelta
              (-(1 / (levelCount : ℝ) + 2 * hierarchyLoss))) := by
      unfold pureWZ2Proposition64HalfHeight
      ring
    _ = (3 / 2 : ℝ) * extensionConstant *
        Real.rpow sourceDelta
          (3 / (levelCount : ℝ) -
            (1 / (levelCount : ℝ) + 2 * hierarchyLoss)) := by
      rw [hcombine]
    _ ≤ (3 / 2 : ℝ) * extensionConstant * 1 := by gcongr
    _ ≤ 3 * extensionConstant := by nlinarith [hextensionNonneg]
    _ ≤ max 9 (3 * extensionConstant) := le_max_right _ _

/-- The closed Proposition-27 and analytic-normalization leaves turn a pure
anchored hierarchy into the pre-Lemma-8 output. -/
theorem PureWZ2LocallyLinearHierarchyData.toNormalizedHierarchyOutputWithEq
    {sigma inputLoss sourceDelta workLoss hierarchyLoss : ℝ}
    {source :
      PureWZ2QuantitativeGrainConfiguration sigma inputLoss sourceDelta}
    (hierarchy :
      PureWZ2LocallyLinearHierarchyData
        source workLoss hierarchyLoss)
    (hinputWork : inputLoss ≤ workLoss)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hhierarchyLoss : 0 ≤ hierarchyLoss)
    (hhierarchyLossUpper :
      hierarchyLoss ≤ 1 / (hierarchy.hierarchy.levelCount : ℝ))
    (hcostAbsorb :
      (hierarchy.hierarchy.levelCount : ℝ) * 136 ≤
        Real.rpow sourceDelta (-hierarchyLoss))
    (hhalfHeightSmall :
      pureWZ2Proposition64HalfHeight sourceDelta
        hierarchy.hierarchy.levelCount ≤ 1 / 90)
    (hparameterWindow :
      24000 * pureWZ2Proposition64NormalizationConstant *
          (45 * pureWZ2Proposition64Lemma35Scale) * sourceDelta ≤
        pureWZ2Proposition64HalfHeight sourceDelta
          hierarchy.hierarchy.levelCount) :
    Nonempty
      { output : PureWZ2NormalizedHierarchyOutput
          sigma workLoss sourceDelta //
        output.inputLoss = inputLoss ∧
          HEq output.source source ∧
          output.source.family = source.family ∧
          output.hierarchyLoss = hierarchyLoss ∧
            HEq output.hierarchy hierarchy ∧
              output.hierarchy.hierarchy.levelCount =
                hierarchy.hierarchy.levelCount ∧
              (wz1PaperBodyFamily output.source.family).mass =
                (wz1PaperBodyFamily source.family).mass ∧
              output.hierarchy.shading.mass = hierarchy.shading.mass } := by
  let A := pureWZ2Proposition64ExtensionConstant
  have hA : WZ1SmoothSegmentExtensionAtConstantStatement A :=
    pureWZ2Proposition64ExtensionConstant_spec
  rcases hierarchy.ordinaryRawGlobalGrains
      hA hhierarchyLoss hcostAbsorb with ⟨ordinaryRaw⟩
  let raw := ordinaryRaw.raw
  let globalBounds := ordinaryRaw.globalBounds
  let rawLoss : ℝ :=
    1 / (hierarchy.hierarchy.levelCount : ℝ) + 2 * hierarchyLoss
  let normalization : ℝ :=
    pureWZ2Proposition64NormalizationConstant
  have hnormalization : 1 ≤ normalization :=
    pureWZ2Proposition64NormalizationConstant_one
  have hnormalizationBudget :
      ∀ slab : PureWZ2Proposition64ShortSlab hierarchy,
        2 * slab.halfHeight * A * Real.rpow sourceDelta (-rawLoss) ≤
          normalization := by
    intro slab
    have hthree :
        3 * slab.halfHeight * A * Real.rpow sourceDelta (-rawLoss) ≤
          normalization := by
      rw [slab.halfHeight_eq]
      simpa [rawLoss, normalization, A,
        pureWZ2Proposition64NormalizationConstant] using
        (pureWZ2_proposition64_fixed_normalization_budget
          hierarchy.delta_pos hierarchy.delta_le_one
          raw.extensionConstant_one hhierarchyLossUpper)
    have hnonneg : 0 ≤ slab.halfHeight * A *
        Real.rpow sourceDelta (-rawLoss) := by
      exact mul_nonneg
        (mul_nonneg slab.halfHeight_pos.le
          (zero_le_one.trans raw.extensionConstant_one))
        (Real.rpow_pos_of_pos hierarchy.delta_pos _).le
    nlinarith
  rcases hierarchy.prepareProposition64 raw normalization hnormalization
      hnormalizationBudget with ⟨⟨prepared, prepared_normalization⟩⟩
  have hvalueBudget :
      3 * prepared.slab.halfHeight * A *
        Real.rpow sourceDelta (-rawLoss) ≤ prepared.normalization := by
    rw [prepared_normalization]
    rw [prepared.slab.halfHeight_eq]
    simpa [rawLoss, normalization, A,
      pureWZ2Proposition64NormalizationConstant] using
      (pureWZ2_proposition64_fixed_normalization_budget
        hierarchy.delta_pos hierarchy.delta_le_one
        raw.extensionConstant_one hhierarchyLossUpper)
  have hfirstBudget :
      prepared.slab.halfHeight * A *
        Real.rpow sourceDelta (-rawLoss) ≤ prepared.normalization := by
    rw [prepared_normalization]
    have hbase := hnormalizationBudget prepared.slab
    have hnonneg : 0 ≤ prepared.slab.halfHeight * A *
        Real.rpow sourceDelta (-rawLoss) := by
      exact mul_nonneg
        (mul_nonneg prepared.slab.halfHeight_pos.le
          (zero_le_one.trans raw.extensionConstant_one))
        (Real.rpow_pos_of_pos hierarchy.delta_pos _).le
    nlinarith
  have hsecondBudget :
      prepared.slab.halfHeight ^ 2 * A *
        Real.rpow sourceDelta (-rawLoss) ≤ prepared.normalization := by
    rw [prepared_normalization]
    have hfirst : prepared.slab.halfHeight * A *
        Real.rpow sourceDelta (-rawLoss) ≤ normalization := by
      rw [← prepared_normalization]
      exact hfirstBudget
    have hhalf := prepared.slab.halfHeight_le_one
    have hnonneg : 0 ≤ A * Real.rpow sourceDelta (-rawLoss) := by
      exact mul_nonneg (zero_le_one.trans raw.extensionConstant_one)
        (Real.rpow_pos_of_pos hierarchy.delta_pos _).le
    have hsq : prepared.slab.halfHeight ^ 2 ≤ prepared.slab.halfHeight := by
      nlinarith [prepared.slab.halfHeight_pos.le,
        sq_nonneg prepared.slab.halfHeight]
    calc
      prepared.slab.halfHeight ^ 2 * A *
          Real.rpow sourceDelta (-rawLoss) ≤
        prepared.slab.halfHeight * A *
          Real.rpow sourceDelta (-rawLoss) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsq
                (zero_le_one.trans raw.extensionConstant_one))
              (Real.rpow_pos_of_pos hierarchy.delta_pos _).le
      _ ≤ normalization := hfirst
  let output : PureWZ2NormalizedHierarchyOutput
      sigma workLoss sourceDelta :=
    { inputLoss := inputLoss
      source := source
      hierarchyLoss := hierarchyLoss
      hierarchy := hierarchy
      rawLoss := rawLoss
      extensionConstant := A
      raw := raw
      globalBounds := globalBounds
      raw_global_slab_ad := by
        intro z hz
        have hsourceFull := source.globalGrains.paperGlobalSlabAD
          hierarchy.delta_pos hierarchy.delta_le_one source.cubical
            hbridge z hz
        have hsourceRestricted :
            PureWZ2PaperADSet1
              (globalGrainProjection hierarchy.sourceGlobalGrains.slope
                (globalGrainSlab hierarchy.shading.union z sourceDelta))
              sourceDelta (1 - sigma)
                (4000 * Kakeya.realRpowENN sourceDelta (-inputLoss)) :=
          hsourceFull.mono (by
            rw [hierarchy.source_slope_eq]
            apply Set.image_mono
            intro point hpoint
            exact
              ⟨⟨hierarchy.subshading.union_subset hpoint.1.1, hpoint.1.2⟩,
                hpoint.2⟩)
        have hconstant :
            4000 * Kakeya.realRpowENN sourceDelta (-inputLoss) ≤
              4000 * Kakeya.realRpowENN sourceDelta (-workLoss) := by
          gcongr
          exact pureWZ2_grain_constant_mono hierarchy.delta_pos
            hierarchy.delta_le_one hinputWork
        have hsource := hsourceRestricted.mono_constant hconstant (by
          exact ENNReal.mul_ne_top (by norm_num)
            (by simp [Kakeya.realRpowENN]))
        have hperturbed := hsource.perturb_by_delta (target :=
          globalGrainProjection raw.slope
            (globalGrainSlab hierarchy.shading.union z sourceDelta))
        convert hperturbed (by
          rintro value ⟨point, hpoint, rfl⟩
          let sourceValue := inner ℝ point
            (globalGrainDirection (hierarchy.sourceGlobalGrains.slope (point 2)))
          refine ⟨sourceValue, ⟨point, hpoint, rfl⟩, ?_⟩
          have hpointHeight : point 2 ∈ Set.Icc (-1 : ℝ) 1 := hpoint.2
          have hactive : horizontalSlice hierarchy.shading.union (point 2) ≠ ∅ :=
            Set.nonempty_iff_ne_empty.mp ⟨point, hpoint.1.1, rfl⟩
          have hslope := ordinaryRaw.slope_close_on_active
            (point 2) hpointHeight hactive
          have hbox := shading_union_subset_axisBox hpoint.1.1
          have hy : |point 1| ≤ 1 := by
            simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
          dsimp only [sourceValue]
          have hformula :
              inner ℝ point (globalGrainDirection (raw.slope (point 2))) -
                  inner ℝ point
                    (globalGrainDirection
                      (hierarchy.sourceGlobalGrains.slope (point 2))) =
                (raw.slope (point 2) -
                  hierarchy.sourceGlobalGrains.slope (point 2)) * point 1 := by
            simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
            ring
          rw [hformula, abs_mul]
          have hslope' :
              |raw.slope (point 2) -
                hierarchy.sourceGlobalGrains.slope (point 2)| ≤ sourceDelta := by
            simpa [raw, abs_sub_comm] using hslope
          calc
            |raw.slope (point 2) -
                  hierarchy.sourceGlobalGrains.slope (point 2)| * |point 1| ≤
                sourceDelta * 1 := by
              exact mul_le_mul hslope' hy (abs_nonneg _)
                hierarchy.delta_pos.le
            _ = sourceDelta := by ring) using 1 <;> ring
      prepared := prepared
      extensionConstant_eq := rfl
      normalization_eq := prepared_normalization
      normalization_nine := by
        rw [prepared_normalization]
        exact pureWZ2Proposition64NormalizationConstant_nine
      halfHeight_small := by
        rw [prepared.slab.halfHeight_eq]
        exact hhalfHeightSmall.trans (by norm_num)
      halfHeight_slab_ad := by
        rw [prepared.slab.halfHeight_eq]
        exact hhalfHeightSmall
      lemma35_parameter_window := by
        rw [prepared.slab.halfHeight_eq]
        exact hparameterWindow
      valueBudget := hvalueBudget
      firstBudget := hfirstBudget
      secondBudget := hsecondBudget }
  exact ⟨⟨output, rfl, HEq.rfl, rfl, rfl, HEq.rfl, rfl, rfl, rfl⟩⟩

/-- Compatibility projection of the normalization theorem. -/
theorem PureWZ2LocallyLinearHierarchyData.toNormalizedHierarchyOutput
    {sigma inputLoss sourceDelta workLoss hierarchyLoss : ℝ}
    {source :
      PureWZ2QuantitativeGrainConfiguration sigma inputLoss sourceDelta}
    (hierarchy :
      PureWZ2LocallyLinearHierarchyData
        source workLoss hierarchyLoss)
    (hinputWork : inputLoss ≤ workLoss)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hhierarchyLoss : 0 ≤ hierarchyLoss)
    (hhierarchyLossUpper :
      hierarchyLoss ≤ 1 / (hierarchy.hierarchy.levelCount : ℝ))
    (hcostAbsorb :
      (hierarchy.hierarchy.levelCount : ℝ) * 136 ≤
        Real.rpow sourceDelta (-hierarchyLoss))
    (hhalfHeightSmall :
      pureWZ2Proposition64HalfHeight sourceDelta
        hierarchy.hierarchy.levelCount ≤ 1 / 90)
    (hparameterWindow :
      24000 * pureWZ2Proposition64NormalizationConstant *
          (45 * pureWZ2Proposition64Lemma35Scale) * sourceDelta ≤
        pureWZ2Proposition64HalfHeight sourceDelta
          hierarchy.hierarchy.levelCount) :
    Nonempty
      (PureWZ2NormalizedHierarchyOutput
        sigma workLoss sourceDelta) := by
  rcases hierarchy.toNormalizedHierarchyOutputWithEq hinputWork hbridge hhierarchyLoss
      hhierarchyLossUpper hcostAbsorb hhalfHeightSmall hparameterWindow with
    ⟨output⟩
  exact ⟨output.1⟩

/-- Normalize an ordinary quantitative hierarchy without losing its
multiplicity cap or indexed-mass receipt. -/
theorem PureWZ2QuantitativeLocallyLinearHierarchyData.toNormalizedHierarchyOutput
    {sigma inputLoss sourceDelta workLoss hierarchyLoss densityLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss sourceDelta}
    (quantitative :
      PureWZ2QuantitativeLocallyLinearHierarchyData source workLoss
        hierarchyLoss densityLoss)
    (hinputWork : inputLoss ≤ workLoss)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hhierarchyLossUpper :
      hierarchyLoss ≤
        1 / (quantitative.hierarchy.hierarchy.levelCount : ℝ))
    (hcostAbsorb :
      (quantitative.hierarchy.hierarchy.levelCount : ℝ) * 136 ≤
        Real.rpow sourceDelta (-hierarchyLoss))
    (hhalfHeightSmall :
      pureWZ2Proposition64HalfHeight sourceDelta
        quantitative.hierarchy.hierarchy.levelCount ≤ 1 / 90)
    (hparameterWindow :
      24000 * pureWZ2Proposition64NormalizationConstant *
          (45 * pureWZ2Proposition64Lemma35Scale) * sourceDelta ≤
        pureWZ2Proposition64HalfHeight sourceDelta
          quantitative.hierarchy.hierarchy.levelCount) :
    Nonempty
      (PureWZ2QuantitativeNormalizedHierarchyOutput
        sigma workLoss sourceDelta) := by
  rcases quantitative.hierarchy.toNormalizedHierarchyOutputWithEq
      hinputWork hbridge hhierarchyLoss.le hhierarchyLossUpper hcostAbsorb hhalfHeightSmall
        hparameterWindow with
    ⟨output⟩
  exact ⟨{
    densityLoss := densityLoss
    quantitativeInputLoss := inputLoss
    inputLoss_le_workLoss := hinputWork
    quantitativeSource := source
    quantitativeHierarchyLoss := hierarchyLoss
    hierarchyLoss_pos := hhierarchyLoss
    quantitative := quantitative
    hierarchyLoss_upper := hhierarchyLossUpper
    normalized := output.1
    inputLoss_eq := output.2.1
    source_eq := output.2.2.1
    hierarchyLoss_eq := output.2.2.2.2.1
    hierarchy_eq := output.2.2.2.2.2.1
    normalized_mass_retention := by
      rw [output.2.2.2.2.2.2.2.2, output.2.2.2.2.2.2.2.1]
      exact quantitative.mass_retention }⟩

/-- Minimal output still owed by the Pure Corollary-26 iteration.

All Proposition-27 and analytic-normalization fields are deliberately absent:
they are derived by `toNormalizedHierarchyOutput`.
-/
structure PureWZ2BudgetedHierarchyOutput
    (sigma workLoss sourceDelta : ℝ) where
  inputLoss : ℝ
  inputLoss_le_workLoss : inputLoss ≤ workLoss
  source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss sourceDelta
  hierarchyLoss : ℝ
  hierarchyLoss_nonneg : 0 ≤ hierarchyLoss
  hierarchy :
    PureWZ2LocallyLinearHierarchyData
      source workLoss hierarchyLoss
  hierarchyLoss_upper :
    hierarchyLoss ≤ 1 / (hierarchy.hierarchy.levelCount : ℝ)
  cost_absorb :
    (hierarchy.hierarchy.levelCount : ℝ) * 136 ≤
      Real.rpow sourceDelta (-hierarchyLoss)
  short_slab_small :
    pureWZ2Proposition64HalfHeight sourceDelta
      hierarchy.hierarchy.levelCount ≤ 1 / 90
  lemma35_parameter_window :
    24000 * pureWZ2Proposition64NormalizationConstant *
        (45 * pureWZ2Proposition64Lemma35Scale) * sourceDelta ≤
      pureWZ2Proposition64HalfHeight sourceDelta
        hierarchy.hierarchy.levelCount

namespace PureWZ2BudgetedHierarchyOutput

/-- Attach the two Proposition 6.4 short-slab budgets to a hierarchy produced
below the preselected `N`-dependent threshold. -/
def ofHierarchyScaleThreshold
    {sigma workLoss sourceDelta : ℝ}
    {inputLoss hierarchyLoss : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss sourceDelta)
    (hinputWork : inputLoss ≤ workLoss)
    (hhierarchyLoss : 0 ≤ hierarchyLoss)
    (hierarchy : PureWZ2LocallyLinearHierarchyData
      source workLoss hierarchyLoss)
    (hhierarchyLossUpper :
      hierarchyLoss ≤ 1 / (hierarchy.hierarchy.levelCount : ℝ))
    (hcostAbsorb :
      (hierarchy.hierarchy.levelCount : ℝ) * 136 ≤
        Real.rpow sourceDelta (-hierarchyLoss))
    (threshold : PureWZ2Proposition64HierarchyScaleThreshold
      hierarchy.hierarchy.levelCount)
    (hsourceSmall : sourceDelta ≤ threshold.delta₀) :
    PureWZ2BudgetedHierarchyOutput sigma workLoss sourceDelta :=
  { inputLoss := inputLoss
    inputLoss_le_workLoss := hinputWork
    source := source
    hierarchyLoss := hierarchyLoss
    hierarchyLoss_nonneg := hhierarchyLoss
    hierarchy := hierarchy
    hierarchyLoss_upper := hhierarchyLossUpper
    cost_absorb := hcostAbsorb
    short_slab_small := threshold.halfHeight_slab_ad
      source.extremal.delta_pos hsourceSmall
    lemma35_parameter_window := threshold.parameter_window
      source.extremal.delta_pos hsourceSmall }

/-- Discharge the closed Proposition-27 and normalization tail. -/
theorem normalize
    {sigma workLoss sourceDelta : ℝ}
    (data : PureWZ2BudgetedHierarchyOutput
      sigma workLoss sourceDelta)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty
      (PureWZ2NormalizedHierarchyOutput
        sigma workLoss sourceDelta) :=
  data.hierarchy.toNormalizedHierarchyOutput
    data.inputLoss_le_workLoss hbridge data.hierarchyLoss_nonneg
      data.hierarchyLoss_upper data.cost_absorb
      data.short_slab_small data.lemma35_parameter_window

end PureWZ2BudgetedHierarchyOutput

namespace PureWZ2MixedRawHierarchyData

/-- Run the closed mixed-terminal popularity construction and attach the two
hierarchy-depth-dependent Proposition-6.4 scale budgets.  This is the final
mechanical assembly after the source-parametric ordinary and exact-terminal
producers and the outer numerical schedule have supplied their receipts. -/
theorem toBudgetedHierarchyOutput
    {sigma inputLoss sourceDelta finalLoss hierarchyLoss workLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss sourceDelta}
    (data : PureWZ2MixedRawHierarchyData source finalLoss hierarchyLoss)
    (hinputHierarchy : inputLoss ≤ hierarchyLoss)
    (hhierarchyWork : hierarchyLoss ≤ workLoss)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hfinalHierarchy : finalLoss ≤ hierarchyLoss)
    (hfinalLevelZero : finalLoss ≤
      hierarchyLoss / (4 * (data.levelCount : ℝ)))
    (hdeltaStrict : sourceDelta < 1)
    (hgeometric : Real.rpow sourceDelta
      (hierarchyLoss / (data.levelCount : ℝ)) < 1 / 9)
    (hlevelZero :
      pureWZ2HierarchySlabConstant sourceDelta sigma finalLoss *
          ENNReal.ofReal (12 * Real.rpow sourceDelta
            (hierarchyLoss / (data.levelCount : ℝ))) <
        Kakeya.realRpowENN sourceDelta
          (sigma + hierarchyLoss / (4 * (data.levelCount : ℝ))))
    (hremoved :
      pureWZ2HierarchySlabConstant sourceDelta sigma finalLoss *
          ENNReal.ofReal
            (12 * ∑ level : Fin data.levelCount,
              Real.rpow
                (wz1Corollary26Scale sourceDelta
                  data.levelCount level) hierarchyLoss) ≤
        ENNReal.ofReal (1 / 3) * MeasureTheory.volume data.shading.union)
    (hfinalVolume :
      Kakeya.realRpowENN sourceDelta (sigma + hierarchyLoss) <
        ENNReal.ofReal (2 / 3) *
          Kakeya.realRpowENN sourceDelta (sigma + finalLoss))
    (hhierarchyLossUpper : hierarchyLoss ≤ 1 / (data.levelCount : ℝ))
    (hcostAbsorb :
      (data.levelCount : ℝ) * 136 ≤
        Real.rpow sourceDelta (-hierarchyLoss))
    (threshold : PureWZ2Proposition64HierarchyScaleThreshold data.levelCount)
    (hsourceSmall : sourceDelta ≤ threshold.delta₀) :
    Nonempty (PureWZ2BudgetedHierarchyOutput
      sigma workLoss sourceDelta) := by
  rcases data.toLocallyLinearHierarchyWithLevelCount hbridge hsigma hsigmaOne
      hhierarchyLoss hfinalHierarchy hfinalLevelZero hdeltaStrict
      hgeometric hlevelZero hremoved hfinalVolume with
      ⟨⟨rawHierarchy, hlevelCount⟩⟩
  let hierarchy := rawHierarchy.mono_finalLoss hhierarchyWork
  exact ⟨{
    inputLoss := inputLoss
    inputLoss_le_workLoss := hinputHierarchy.trans hhierarchyWork
    source := source
    hierarchyLoss := hierarchyLoss
    hierarchyLoss_nonneg := hhierarchyLoss.le
    hierarchy := hierarchy
    hierarchyLoss_upper := by
      change hierarchyLoss ≤ 1 / (rawHierarchy.hierarchy.levelCount : ℝ)
      rw [hlevelCount]
      exact hhierarchyLossUpper
    cost_absorb := by
      change (rawHierarchy.hierarchy.levelCount : ℝ) * 136 ≤
        Real.rpow sourceDelta (-hierarchyLoss)
      rw [hlevelCount]
      exact hcostAbsorb
    short_slab_small := by
      change pureWZ2Proposition64HalfHeight sourceDelta
        rawHierarchy.hierarchy.levelCount ≤ 1 / 90
      rw [hlevelCount]
      exact threshold.halfHeight_slab_ad source.extremal.delta_pos hsourceSmall
    lemma35_parameter_window := by
      change 24000 * pureWZ2Proposition64NormalizationConstant *
          (45 * pureWZ2Proposition64Lemma35Scale) * sourceDelta ≤
        pureWZ2Proposition64HalfHeight sourceDelta
          rawHierarchy.hierarchy.levelCount
      rw [hlevelCount]
      exact threshold.parameter_window source.extremal.delta_pos hsourceSmall }⟩

end PureWZ2MixedRawHierarchyData

namespace PureWZ2QuantitativeMixedRawHierarchyData

/-- Normalize a quantitative mixed-terminal hierarchy while preserving the
pointwise multiplicity cap and indexed-mass receipt.  The only loss weakening
changes the grain constants; its shading and quantitative fields are literal. -/
theorem toQuantitativeNormalizedHierarchyOutput
    {sigma inputLoss sourceDelta finalLoss hierarchyLoss workLoss densityLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss sourceDelta}
    (data : PureWZ2QuantitativeMixedRawHierarchyData
      source finalLoss hierarchyLoss densityLoss)
    (hinputHierarchy : inputLoss ≤ hierarchyLoss)
    (hhierarchyWork : hierarchyLoss ≤ workLoss)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hfinalHierarchy : finalLoss ≤ hierarchyLoss)
    (hfinalLevelZero : finalLoss ≤
      hierarchyLoss / (4 * (data.mixed.levelCount : ℝ)))
    (hdeltaStrict : sourceDelta < 1)
    (hgeometric : Real.rpow sourceDelta
      (hierarchyLoss / (data.mixed.levelCount : ℝ)) < 1 / 9)
    (hlevelZero :
      pureWZ2HierarchySlabConstant sourceDelta sigma finalLoss *
          ENNReal.ofReal (12 * Real.rpow sourceDelta
            (hierarchyLoss / (data.mixed.levelCount : ℝ))) <
        Kakeya.realRpowENN sourceDelta
          (sigma + hierarchyLoss / (4 * (data.mixed.levelCount : ℝ))))
    (hremoved :
      pureWZ2HierarchySlabConstant sourceDelta sigma finalLoss *
          ENNReal.ofReal
            (12 * ∑ level : Fin data.mixed.levelCount,
              Real.rpow
                (wz1Corollary26Scale sourceDelta
                  data.mixed.levelCount level) hierarchyLoss) ≤
        ENNReal.ofReal (1 / 3) *
          MeasureTheory.volume data.mixed.shading.union)
    (hfinalVolume :
      Kakeya.realRpowENN sourceDelta (sigma + hierarchyLoss) <
        ENNReal.ofReal (2 / 3) *
          Kakeya.realRpowENN sourceDelta (sigma + finalLoss))
    (hhierarchyLossUpper :
      hierarchyLoss ≤ 1 / (data.mixed.levelCount : ℝ))
    (hcostAbsorb :
      (data.mixed.levelCount : ℝ) * 136 ≤
        Real.rpow sourceDelta (-hierarchyLoss))
    (threshold : PureWZ2Proposition64HierarchyScaleThreshold
      data.mixed.levelCount)
    (hsourceSmall : sourceDelta ≤ threshold.delta₀) :
    Nonempty (PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta) := by
  rcases data.toQuantitativeLocallyLinearHierarchyWithLevelCount
      hbridge hsigma hsigmaOne hhierarchyLoss hfinalHierarchy
      hfinalLevelZero hdeltaStrict hgeometric hlevelZero hremoved
      hfinalVolume with ⟨quantitativeRaw⟩
  let hierarchy := quantitativeRaw.1.hierarchy.mono_finalLoss hhierarchyWork
  have hshading : hierarchy.shading =
      quantitativeRaw.1.hierarchy.shading := rfl
  let quantitative : PureWZ2QuantitativeLocallyLinearHierarchyData
      source workLoss hierarchyLoss densityLoss := {
    hierarchy := hierarchy
    multiplicity := quantitativeRaw.1.multiplicity
    multiplicity_pos := quantitativeRaw.1.multiplicity_pos
    pointMultiplicity_upper := by
      rw [hshading]
      exact quantitativeRaw.1.pointMultiplicity_upper
    mass_retention := by
      rw [hshading]
      exact quantitativeRaw.1.mass_retention }
  have hlevelCount : quantitative.hierarchy.hierarchy.levelCount =
      data.mixed.levelCount := by
    change quantitativeRaw.1.hierarchy.hierarchy.levelCount =
      data.mixed.levelCount
    exact quantitativeRaw.2
  apply quantitative.toNormalizedHierarchyOutput
    (hinputHierarchy.trans hhierarchyWork) hbridge hhierarchyLoss
  · rw [hlevelCount]
    exact hhierarchyLossUpper
  · rw [hlevelCount]
    exact hcostAbsorb
  · rw [hlevelCount]
    exact threshold.halfHeight_slab_ad source.extremal.delta_pos hsourceSmall
  · rw [hlevelCount]
    exact threshold.parameter_window source.extremal.delta_pos hsourceSmall

end PureWZ2QuantitativeMixedRawHierarchyData

/-- Outer scalar schedule for one already assembled source-faithful mixed
hierarchy.  Every field is indexed by the actual mixed output, so no runtime
family, shading, or depth can be substituted. -/
structure PureWZ2MixedHierarchyBudgetReceipt
    {sigma finalLoss hierarchyLoss sourceDelta : ℝ}
    {N : ℕ}
    (construction : PureWZ2MixedHierarchyConstructionData
      sigma finalLoss hierarchyLoss sourceDelta N)
    (workLoss : ℝ) where
  hierarchyLoss_le_workLoss : hierarchyLoss ≤ workLoss
  finalLoss_le_hierarchy : finalLoss ≤ hierarchyLoss
  finalLoss_le_level_zero :
    finalLoss ≤ hierarchyLoss /
      (4 * (construction.mixed.levelCount : ℝ))
  delta_strict : sourceDelta < 1
  geometric : Real.rpow sourceDelta
    (hierarchyLoss / (construction.mixed.levelCount : ℝ)) < 1 / 9
  level_zero :
    pureWZ2HierarchySlabConstant sourceDelta sigma finalLoss *
        ENNReal.ofReal (12 * Real.rpow sourceDelta
          (hierarchyLoss / (construction.mixed.levelCount : ℝ))) <
      Kakeya.realRpowENN sourceDelta
        (sigma + hierarchyLoss /
          (4 * (construction.mixed.levelCount : ℝ)))
  removed :
    pureWZ2HierarchySlabConstant sourceDelta sigma finalLoss *
        ENNReal.ofReal
          (12 * ∑ level : Fin construction.mixed.levelCount,
            Real.rpow
              (wz1Corollary26Scale sourceDelta
                construction.mixed.levelCount level) hierarchyLoss) ≤
      ENNReal.ofReal (1 / 3) *
        MeasureTheory.volume construction.mixed.shading.union
  final_volume :
    Kakeya.realRpowENN sourceDelta (sigma + hierarchyLoss) <
      ENNReal.ofReal (2 / 3) *
        Kakeya.realRpowENN sourceDelta (sigma + finalLoss)
  hierarchyLoss_upper :
    hierarchyLoss ≤ 1 / (construction.mixed.levelCount : ℝ)
  cost_absorb :
    (construction.mixed.levelCount : ℝ) * 136 ≤
      Real.rpow sourceDelta (-hierarchyLoss)
  threshold : PureWZ2Proposition64HierarchyScaleThreshold
    construction.mixed.levelCount
  source_small : sourceDelta ≤ threshold.delta₀

namespace PureWZ2MixedHierarchyConstructionData

/-- Complete the R3 hierarchy once the outer numerical schedule has been
verified for this exact source-faithful mixed construction. -/
theorem toBudgetedHierarchyOutput
    {sigma finalLoss hierarchyLoss sourceDelta workLoss : ℝ}
    {N : ℕ}
    (construction : PureWZ2MixedHierarchyConstructionData
      sigma finalLoss hierarchyLoss sourceDelta N)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (budget : PureWZ2MixedHierarchyBudgetReceipt construction workLoss) :
    Nonempty (PureWZ2BudgetedHierarchyOutput
      sigma workLoss sourceDelta) :=
  construction.mixed.toBudgetedHierarchyOutput
    construction.terminalInputLoss_le_hierarchy
    budget.hierarchyLoss_le_workLoss hbridge hsigma hsigmaOne
    hhierarchyLoss budget.finalLoss_le_hierarchy
    budget.finalLoss_le_level_zero budget.delta_strict
    budget.geometric budget.level_zero budget.removed budget.final_volume
    budget.hierarchyLoss_upper budget.cost_absorb budget.threshold
    budget.source_small

end PureWZ2MixedHierarchyConstructionData

namespace PureWZ2NormalizedHierarchyOutput

/-- Instantiate the fixed Lemma-3.5 scales at an output-independent source
ceiling selected from the caller's requested final scale. -/
theorem lemma35ScaleData
    {sigma workLoss sourceDelta targetDelta₀ : ℝ}
    (output : PureWZ2NormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀) :
    PureWZ2Proposition64Lemma35ScaleData sourceDelta
      output.prepared.slab.halfHeight targetDelta₀ :=
  pureWZ2Proposition64_lemma35ScaleData
    output.source.extremal.delta_pos output.prepared.slab.halfHeight_pos
      output.halfHeight_slab_ad hsourceSmall output.lemma35_parameter_window

/-- The one common horizontal window selected from the normalized
Proposition 6.4 slab. -/
noncomputable def lemma35CommonWindow
    {sigma workLoss sourceDelta : ℝ}
    (output : PureWZ2NormalizedHierarchyOutput
      sigma workLoss sourceDelta) :=
  Classical.choice <|
    output.prepared.selectCommonWindow output.normalization_nine

/-- The exact inverse-transpose plane map on the common-window affine image,
at the image radius fixed by the Lemma-3.5 scale receipt. -/
noncomputable def lemma35ExactPlaneMap
    {sigma workLoss sourceDelta targetDelta₀ : ℝ}
    (output : PureWZ2NormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀) :=
  let scales := output.lemma35ScaleData hsourceSmall
  let common := output.lemma35CommonWindow
  Classical.choice <|
    output.prepared.exactImageLocalGrains common output.halfHeight_small
      output.normalization_nine scales.sourceDelta_le_image
      scales.image_radius scales.sourceDelta_small

/-- Execute the common-window, exact-affine-image, isotropic-box, and
Kirszbraun-normalization geometry on the one hierarchy output. -/
noncomputable def lemma35LocalCleanup
    {sigma workLoss sourceDelta targetDelta₀ : ℝ}
    (output : PureWZ2NormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀) :=
  let scales := output.lemma35ScaleData hsourceSmall
  let exactData := output.lemma35ExactPlaneMap hsourceSmall
  Classical.choice <|
    scales.assembleExactLocalCleanup _ exactData output.normalization_eq

/-- The complete dependent geometric prefix of the paper's final Lemma 3.5
step.  Every field is constructed from one normalized hierarchy output, so
the common window, exact affine image, transported plane map, and isotropic
cleanup cannot be mixed with witnesses from another configuration. -/
structure PureWZ2Proposition64Lemma35GeometricData
    {sigma workLoss sourceDelta targetDelta₀ : ℝ}
    (output : PureWZ2NormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀) where
  scales : PureWZ2Proposition64Lemma35ScaleData sourceDelta
    output.prepared.slab.halfHeight targetDelta₀
  scales_eq : scales = output.lemma35ScaleData hsourceSmall
  common : PureWZ2Proposition64CommonWindowData
    output.prepared.restrictedRaw.slope output.prepared.slab.center
      output.prepared.slab.anchorHeight output.prepared.slab.halfHeight
      output.prepared.normalization output.source.family
      output.prepared.slab.shading
  common_eq : common = output.lemma35CommonWindow
  exactData :
    let selectedSource :=
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        output.source.family common.selected
    let selectedShading : WZ1PaperTubeShading selectedSource.family :=
      restrictPaperShading selectedSource output.prepared.slab.shading
    let selectedSub : ∀ index, selectedShading.carrier index ⊆
        output.hierarchy.shading.carrier (selectedSource.embedding index) :=
      fun index point hpoint => output.prepared.slab.subshading
        (selectedSource.embedding index) hpoint
    let selectedLocal := output.hierarchy.localGrains.restrictSubfamilyWithShading
      selectedSource selectedShading selectedSub
    let imageBox : ∀ index, ∀ point ∈ selectedShading.carrier index,
        pureWZ2Proposition64TranslatedMap
            output.prepared.restrictedRaw.slope output.prepared.slab.center
            output.prepared.slab.anchorHeight output.prepared.slab.halfHeight
            output.prepared.normalization common.translation point ∈
          Kakeya.Streamlined.axisBox 2 2 2 :=
      common.image_mem_axisBox output.source.extremal.delta_pos
        scales.sourceDelta_small output.prepared.slab.halfHeight_pos
        (by linarith [output.halfHeight_small]) output.normalization_nine
        output.prepared.normalized.anchor_value_bound output.source.line_class
        output.prepared.shading_subset_shortSlab
    PureWZ2Proposition64ExactPlaneMapData
      (targetDelta := pureWZ2Proposition64Lemma35ImageDelta sourceDelta)
      (g := output.prepared.restrictedRaw.slope)
      (slabCenter := output.prepared.slab.center)
      (anchorHeight := output.prepared.slab.anchorHeight)
      (halfHeight := output.prepared.slab.halfHeight)
      (normalization := output.prepared.normalization)
      (translation := common.translation)
      (hhalfHeight := output.prepared.slab.halfHeight_pos)
      (hnormalization := output.normalization_nine)
      (hsourceDelta := output.source.extremal.delta_pos)
      (hanchorSlope := output.prepared.normalized.anchor_value_bound)
      (hradius := scales.image_radius)
      (hsourceLine := output.source.line_class.subfamily selectedSource)
      (himageBox := imageBox) selectedLocal
  cleanup : PureWZ2Proposition64Lemma35LocalCleanupData
    (width := pureWZ2Proposition64Lemma35Width)
    (scale := pureWZ2Proposition64Lemma35Scale)
    (pureWZ2Proposition64ExactImageShading
      output.source.extremal.delta_pos output.prepared.restrictedRaw.slope
      output.prepared.slab.center output.prepared.slab.anchorHeight
      output.prepared.slab.halfHeight output.prepared.normalization
      common.translation output.prepared.slab.halfHeight_pos
      output.normalization_nine
      output.prepared.normalized.anchor_value_bound scales.image_radius
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        output.source.family common.selected).family
      (restrictPaperShading
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          output.source.family common.selected) output.prepared.slab.shading)
      (output.source.line_class.subfamily
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          output.source.family common.selected))
      (common.image_mem_axisBox output.source.extremal.delta_pos
        scales.sourceDelta_small output.prepared.slab.halfHeight_pos
        (by linarith [output.halfHeight_small]) output.normalization_nine
        output.prepared.normalized.anchor_value_bound output.source.line_class
        output.prepared.shading_subset_shortSlab))
    exactData.planeMap pureWZ2Proposition64Lemma35TargetK
      scales.imageDelta_pos scales.finalDelta_pos
      (scales.finalDelta_le_one_ninety_six.trans (by norm_num))
      scales.scale_one scales.retube_radius

/-- Construct the whole dependent geometric prefix once. -/
noncomputable def lemma35GeometricData
    {sigma workLoss sourceDelta targetDelta₀ : ℝ}
    (output : PureWZ2NormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀) :
    PureWZ2Proposition64Lemma35GeometricData output hsourceSmall :=
  let scales := output.lemma35ScaleData hsourceSmall
  let common := output.lemma35CommonWindow
  let exactData := output.lemma35ExactPlaneMap hsourceSmall
  { scales := scales
    scales_eq := rfl
    common := common
    common_eq := rfl
    exactData := exactData
    cleanup := output.lemma35LocalCleanup hsourceSmall }

end PureWZ2NormalizedHierarchyOutput

/-- Pure same-configuration finite hierarchy producer.  Any same-extremizer
restoration needed inside the construction is a Node-5-private obligation; it
is not part of the exact paper-facing Node-4 hypothesis below. -/
def PureWZ2BudgetedHierarchyFromCriticalStatement : Prop :=
  PureWZ2PropStickyCapability →
    PureWZ2PaperADBridgeStatement →
      PureWZ2GrainsFromCriticalStatement →
        ∀ sigma : ℝ,
          PureWZ2CriticalPackage sigma →
            ∀ workLoss sourceDelta₀ : ℝ,
              0 < workLoss → 0 < sourceDelta₀ →
                ∃ sourceDelta : ℝ,
                  0 < sourceDelta ∧ sourceDelta ≤ sourceDelta₀ ∧
                    Nonempty
                      (PureWZ2BudgetedHierarchyOutput
                        sigma workLoss sourceDelta)

/-- Pure same-configuration Corollary-26 hierarchy and raw Proposition-27
producer, including all uniform small-scale budgets. -/
def PureWZ2NormalizedHierarchyFromCriticalStatement : Prop :=
  PureWZ2PropStickyCapability →
    PureWZ2PaperADBridgeStatement →
      PureWZ2GrainsFromCriticalStatement →
        ∀ sigma : ℝ,
          PureWZ2CriticalPackage sigma →
            ∀ workLoss sourceDelta₀ : ℝ,
              0 < workLoss → 0 < sourceDelta₀ →
                ∃ sourceDelta : ℝ,
                  0 < sourceDelta ∧ sourceDelta ≤ sourceDelta₀ ∧
                    Nonempty
                      (PureWZ2NormalizedHierarchyOutput
                        sigma workLoss sourceDelta)

/-- The minimal budgeted hierarchy producer implies the normalized producer. -/
theorem pureWZ2_normalizedHierarchyFromCritical_of_budgeted
    (producer : PureWZ2BudgetedHierarchyFromCriticalStatement) :
    PureWZ2NormalizedHierarchyFromCriticalStatement := by
  intro sticky adBridge grainsFromCritical
    sigma critical workLoss sourceDelta₀
    hworkLoss hsourceDelta₀
  rcases producer sticky adBridge grainsFromCritical sigma critical
      workLoss sourceDelta₀ hworkLoss hsourceDelta₀ with
    ⟨sourceDelta, hsourceDelta, hsourceSmall, budgeted⟩
  rcases budgeted with ⟨budgeted⟩
  exact
    ⟨sourceDelta, hsourceDelta, hsourceSmall, budgeted.normalize adBridge⟩

/-- Paper Lemma 8 after the analytic normalization.

The source threshold is chosen after the requested final threshold.  This is
the quantifier order needed to guarantee that the rediscretized final radius
is at most the caller's `targetDelta₀`.
-/
def PureWZ2VerticalRediscretizationProducerStatement : Prop :=
  ∀ sigma workLoss outputLoss targetDelta₀ : ℝ,
    0 < workLoss → 0 < outputLoss → 0 < targetDelta₀ →
      ∃ sourceDelta₀ : ℝ, 0 < sourceDelta₀ ∧
        ∀ sourceDelta : ℝ,
          0 < sourceDelta → sourceDelta ≤ sourceDelta₀ →
            ∀ output :
                PureWZ2NormalizedHierarchyOutput
                  sigma workLoss sourceDelta,
              ∃ finalDelta : ℝ,
                0 < finalDelta ∧ finalDelta ≤ targetDelta₀ ∧
                  Nonempty
                    (PureWZ2VerticalRediscretizationData
                      output.prepared.normalized finalDelta outputLoss)

/-- The two paper-level producers imply the frozen Node-5 statement. -/
theorem pureWZ2_c2_grains_of_producers
    (hierarchyProducer :
      PureWZ2NormalizedHierarchyFromCriticalStatement)
    (verticalProducer :
      PureWZ2VerticalRediscretizationProducerStatement) :
    PureWZ2C2GrainsStatement := by
  intro subunit criticalExtraction propSticky grains
  have propStickyOutput :=
    propSticky subunit criticalExtraction
  rcases propStickyOutput with ⟨propStickyCapability⟩
  have grainsOutput :=
    grains subunit criticalExtraction propSticky
  have hierarchyFromCritical :=
    hierarchyProducer
      propStickyCapability grainsOutput.1 grainsOutput.2
  intro sigma critical outputLoss targetDelta₀
    houtputLoss htargetDelta₀
  let workLoss : ℝ := outputLoss / 2
  have hworkLoss : 0 < workLoss := by
    dsimp only [workLoss]
    positivity
  rcases verticalProducer sigma workLoss outputLoss targetDelta₀
      hworkLoss houtputLoss htargetDelta₀ with
    ⟨sourceDelta₀, hsourceDelta₀, verticalAt⟩
  rcases hierarchyFromCritical sigma critical workLoss sourceDelta₀
      hworkLoss hsourceDelta₀ with
    ⟨sourceDelta, hsourceDelta, hsourceSmall, output⟩
  rcases output with ⟨output⟩
  rcases verticalAt sourceDelta hsourceDelta hsourceSmall output with
    ⟨finalDelta, hfinalDelta, hfinalSmall, final⟩
  rcases final with ⟨final⟩
  exact
    ⟨finalDelta, hfinalDelta, hfinalSmall,
      ⟨final.toC2GrainConfiguration⟩⟩

/-- Node 5 directly from the two genuinely open producer boundaries. -/
theorem pureWZ2_c2_grains_of_budgetedHierarchy_and_verticalRediscretization
    (hierarchyProducer :
      PureWZ2BudgetedHierarchyFromCriticalStatement)
    (verticalProducer :
      PureWZ2VerticalRediscretizationProducerStatement) :
    PureWZ2C2GrainsStatement :=
  pureWZ2_c2_grains_of_producers
    (pureWZ2_normalizedHierarchyFromCritical_of_budgeted
      hierarchyProducer)
    verticalProducer

end Kakeya.Assouad

end
