import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HierarchyShadow
import MyLeanRepo.Kakeya.Assouad.WZ1.RawGlobalGrainsFromMultiscaleCorrections
import MyLeanRepo.Kakeya.Assouad.WZ1.BudgetedSegmentConversionAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothSegmentExtension
import MyLeanRepo.Kakeya.Assouad.WZ1.TelescopingSum

/-!
# Raw Proposition 27 output on a pure paper hierarchy

The smooth-segment construction is carrier-independent.  This module applies
the closed Proposition 27 core directly to a pure anchored hierarchy, without
introducing a historical uniform tube structure.  Exact-slice paper AD is
transported by the literal one-dimensional perturbation theorem.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The raw `C²` slope on one final pure paper configuration. -/
structure PureWZ2RawC2GlobalGrainData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (sigma : ℝ) (C : ENNReal) (rawLoss extensionConstant : ℝ) where
  slope : SlopeFunction
  extensionConstant_one : 1 ≤ extensionConstant
  value_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |slope z| ≤ extensionConstant * Real.rpow delta (-rawLoss)
  first_derivative_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |deriv slope z| ≤ extensionConstant * Real.rpow delta (-rawLoss)
  second_derivative_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |deriv (deriv slope) z| ≤
        extensionConstant * Real.rpow delta (-rawLoss)
  /-- On an occupied height, the raw slope remains in a fixed interval.
  This is the `|g(z_*)| lesssim 1` input used by Proposition 6.4. -/
  active_value_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice shading.union z ≠ ∅ → |slope z| ≤ 8
  global_ad :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (slope z))
          (horizontalSlice shading.union z))
        delta (1 - sigma) (6 * C)

namespace PureWZ2RawC2GlobalGrainData

/-- Restrict raw Proposition 5.7 data to a subshading on the same paper tube
family.  All analytic bounds are unchanged; the upper AD condition is
hereditary under the induced slice inclusion. -/
noncomputable def restrict
    {delta sigma rawLoss extensionConstant : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading refined : WZ1PaperTubeShading family}
    {C : ENNReal}
    (raw : PureWZ2RawC2GlobalGrainData
      sourceShading sigma C rawLoss extensionConstant)
    (hsub : PureWZ2PaperIsSubshading refined sourceShading) :
    PureWZ2RawC2GlobalGrainData
      refined sigma C rawLoss extensionConstant where
  slope := raw.slope
  extensionConstant_one := raw.extensionConstant_one
  value_bound := raw.value_bound
  first_derivative_bound := raw.first_derivative_bound
  second_derivative_bound := raw.second_derivative_bound
  active_value_bound := by
    intro z hz hactive
    apply raw.active_value_bound z hz
    intro hempty
    apply hactive
    ext point
    constructor
    · intro hpoint
      have hpointSource : point ∈ horizontalSlice sourceShading.union z := by
        exact ⟨hsub.union_subset hpoint.1, hpoint.2⟩
      rw [hempty] at hpointSource
      exact hpointSource.elim
    · intro hpoint
      exact hpoint.elim
  global_ad := by
    intro z hz
    apply (raw.global_ad z hz).mono
    apply Set.image_mono
    intro point hpoint
    exact ⟨hsub.union_subset hpoint.1, hpoint.2⟩

end PureWZ2RawC2GlobalGrainData

/-- Extra all-height analytic bounds supplied by the ordinary Proposition-27
smooth correction.  They are deliberately separate from raw grain data:
the terminal affine producer has the same local raw interface but an affine
slope need not be bounded on the whole real line. -/
structure PureWZ2RawC2GlobalBoundData
    {delta sigma rawLoss extensionConstant : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (raw : PureWZ2RawC2GlobalGrainData
      shading sigma C rawLoss extensionConstant) where
  value_bound :
    ∀ z : ℝ,
      |raw.slope z| ≤ extensionConstant * Real.rpow delta (-rawLoss)
  first_derivative_bound :
    ∀ z : ℝ,
      |deriv raw.slope z| ≤ extensionConstant * Real.rpow delta (-rawLoss)
  second_derivative_bound :
    ∀ z : ℝ,
      |deriv (deriv raw.slope) z| ≤
        extensionConstant * Real.rpow delta (-rawLoss)

/-- Ordinary Proposition-27 output together with the active-height comparison
to the exact source slope used to construct it.  This receipt is kept out of
`PureWZ2RawC2GlobalGrainData`: the affine terminal route has no such source
slope comparison and must not be silently strengthened. -/
structure PureWZ2OrdinaryRawC2Output
    {sigma inputLoss delta finalLoss hierarchyLoss A : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (hierarchy :
      PureWZ2LocallyLinearHierarchyData source finalLoss hierarchyLoss) where
  raw : PureWZ2RawC2GlobalGrainData
    hierarchy.shading sigma
      (Kakeya.realRpowENN delta (-finalLoss))
      (1 / (hierarchy.hierarchy.levelCount : ℝ) + 2 * hierarchyLoss) A
  globalBounds : PureWZ2RawC2GlobalBoundData raw
  slope_close_on_active :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice hierarchy.shading.union z ≠ ∅ →
        |hierarchy.sourceGlobalGrains.slope z - raw.slope z| ≤ delta

namespace PureWZ2RawC2GlobalBoundData

/-- Restriction changes only the shading, so an ordinary all-height bound
certificate restricts definitionally with the raw slope. -/
noncomputable def restrict
    {delta sigma rawLoss extensionConstant : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading refined : WZ1PaperTubeShading family}
    {C : ENNReal}
    {raw : PureWZ2RawC2GlobalGrainData
      sourceShading sigma C rawLoss extensionConstant}
    (bounds : PureWZ2RawC2GlobalBoundData raw)
    (hsub : PureWZ2PaperIsSubshading refined sourceShading) :
    PureWZ2RawC2GlobalBoundData (raw.restrict hsub) where
  value_bound := bounds.value_bound
  first_derivative_bound := bounds.first_derivative_bound
  second_derivative_bound := bounds.second_derivative_bound

end PureWZ2RawC2GlobalBoundData

/-- Apply the carrier-independent Proposition 27 core to a pure hierarchy,
retaining the active-height comparison to its exact source slope. -/
theorem PureWZ2LocallyLinearHierarchyData.ordinaryRawGlobalGrains
    {sigma inputLoss delta finalLoss hierarchyLoss A : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data :
      PureWZ2LocallyLinearHierarchyData
        source finalLoss hierarchyLoss)
    (hA : WZ1SmoothSegmentExtensionAtConstantStatement A)
    (hhierarchyLoss : 0 ≤ hierarchyLoss)
    (hcostAbsorb :
      (data.hierarchy.levelCount : ℝ) * 136 ≤
        Real.rpow delta (-hierarchyLoss)) :
    Nonempty (PureWZ2OrdinaryRawC2Output (A := A) data) := by
  let shadow :=
    pureWZ2PartialActiveCellShading data.shading data.delta_pos
  have hunion : shadow.union = data.shading.union :=
    pureWZ2PartialActiveCellShading_union data.shading
      data.delta_pos
  let hierarchy := data.hierarchy.toPartialActiveCellShadow
    data.delta_pos
  have hlevelZero :
      ∀ level, ∀ trapezoid ∈ hierarchy.trapezoids level,
        (level : ℕ) = 0 →
          |trapezoid.affine trapezoid.left| ≤ 4 ∧
            |trapezoid.affine trapezoid.right| ≤ 4 := by
    exact data.hierarchy.levelZero_endpoint_bound
      data.delta_pos data.delta_le_one
      (by
        intro z hz
        simpa [data.source_slope_eq] using
          source.globalGrains.slope_bound z hz)
  rcases multiscaleSlopeCorrectionCore_of_hierarchy hierarchy
      data.delta_pos data.delta_le_one
      hhierarchyLoss hlevelZero hcostAbsorb with
    ⟨corrections, hcorrections⟩
  rcases wz1_raw_global_slope_from_multiscale_data A hA corrections with
    ⟨raw⟩
  have hrawClose :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        horizontalSlice data.shading.union z ≠ ∅ →
          |data.sourceGlobalGrains.slope z - raw.slope z| ≤ delta := by
    intro z hz hactive
    have hactiveShadow : horizontalSlice shadow.union z ≠ ∅ := by
      rwa [hunion]
    have hlastPos : 0 < hierarchy.levelCount := by
      exact lt_of_lt_of_le (by norm_num) hierarchy.levelCount_two
    let last : Fin hierarchy.levelCount :=
      ⟨hierarchy.levelCount - 1, by omega⟩
    rcases hierarchy.active_height_coverage last z hz hactiveShadow with
      ⟨trapezoid, htrapezoid, hzTrapezoid⟩
    have hsum := telescoping_segment_sum hierarchy
      data.delta_pos hz hactiveShadow last
      (by simp [last]) trapezoid htrapezoid hzTrapezoid
    have hscale :
        wz1Corollary26Scale delta hierarchy.levelCount last = delta := by
      dsimp only [wz1Corollary26Scale, last]
      have hcountPos : 0 < (hierarchy.levelCount : ℝ) := by
        positivity
      have hexponent :
          (((hierarchy.levelCount - 1 : ℕ) : ℝ) + 1) /
              (hierarchy.levelCount : ℝ) = 1 := by
        have hnat : hierarchy.levelCount - 1 + 1 =
            hierarchy.levelCount := by omega
        rw [show ((hierarchy.levelCount - 1 : ℕ) : ℝ) + 1 =
          (hierarchy.levelCount : ℝ) by exact_mod_cast hnat]
        field_simp
      rw [hexponent]
      exact Real.rpow_one delta
    have happ := hierarchy.slope_approximation last trapezoid htrapezoid
      z hzTrapezoid hactiveShadow
    rw [hscale] at happ
    have hrawActive := raw.slope_on_active z hz hactiveShadow
    rw [hrawActive]
    rw [hcorrections z, hsum]
    exact happ
  have hglobal :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        PureWZ2PaperADSet1
          (scalarProjection
            (globalGrainDirection (raw.slope z))
            (horizontalSlice data.shading.union z))
          delta (1 - sigma)
          (6 * Kakeya.realRpowENN delta (-finalLoss)) := by
    intro z hz
    apply (data.sourceGlobalGrains.global_ad z hz).perturb_by_delta
    rintro value ⟨point, hpoint, rfl⟩
    let sourceValue := inner ℝ point
      (globalGrainDirection (data.sourceGlobalGrains.slope z))
    refine ⟨sourceValue, ⟨point, hpoint, rfl⟩, ?_⟩
    have hpointSource : point ∈ data.shading.union := hpoint.1
    have hbox := shading_union_subset_axisBox hpointSource
    have hy : |point 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    have hactive : horizontalSlice data.shading.union z ≠ ∅ :=
      Set.nonempty_iff_ne_empty.mp ⟨point, hpoint⟩
    have hslope := hrawClose z hz hactive
    dsimp only [sourceValue]
    have hformula :
        inner ℝ point (globalGrainDirection (raw.slope z)) -
            inner ℝ point
              (globalGrainDirection (data.sourceGlobalGrains.slope z)) =
          (raw.slope z - data.sourceGlobalGrains.slope z) * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      ring
    rw [hformula, abs_mul]
    have hslope' :
        |raw.slope z - data.sourceGlobalGrains.slope z| ≤ delta := by
      simpa [abs_sub_comm] using hslope
    calc
      |raw.slope z - data.sourceGlobalGrains.slope z| * |point 1| ≤
          delta * 1 := by
        exact mul_le_mul hslope' hy (abs_nonneg _)
          data.delta_pos.le
      _ = delta := by ring
  let pureRaw : PureWZ2RawC2GlobalGrainData data.shading sigma
      (Kakeya.realRpowENN delta (-finalLoss))
      (1 / (data.hierarchy.levelCount : ℝ) + 2 * hierarchyLoss) A := {
    slope := raw.slope
    extensionConstant_one := raw.extensionConstant_one
    value_bound := raw.value_bound
    first_derivative_bound := raw.first_derivative_bound
    second_derivative_bound := raw.second_derivative_bound
    active_value_bound := by
      intro z hz hactive
      have hsourceBound : |data.sourceGlobalGrains.slope z| ≤ 3 :=
        data.sourceGlobalGrains.slope_bound z hz
      have hclose := hrawClose z hz hactive
      have htriangle : |raw.slope z| ≤
          |data.sourceGlobalGrains.slope z| +
            |raw.slope z - data.sourceGlobalGrains.slope z| := by
        calc
          |raw.slope z| = |data.sourceGlobalGrains.slope z +
              (raw.slope z - data.sourceGlobalGrains.slope z)| := by ring_nf
          _ ≤ |data.sourceGlobalGrains.slope z| +
              |raw.slope z - data.sourceGlobalGrains.slope z| :=
            abs_add_le _ _
      calc
        |raw.slope z| ≤ |data.sourceGlobalGrains.slope z| +
            |raw.slope z - data.sourceGlobalGrains.slope z| := htriangle
        _ ≤ 3 + delta := by
          gcongr
          simpa [abs_sub_comm] using hclose
        _ ≤ 8 := by linarith [data.delta_le_one]
    global_ad := hglobal }
  exact ⟨{
    raw := pureRaw
    globalBounds := {
      value_bound := raw.global_value_bound
      first_derivative_bound := raw.global_first_derivative_bound
      second_derivative_bound := raw.global_second_derivative_bound }
    slope_close_on_active := hrawClose }⟩

/-- Compatibility projection retaining the historical raw/global-bounds API. -/
theorem PureWZ2LocallyLinearHierarchyData.rawGlobalGrains
    {sigma inputLoss delta finalLoss hierarchyLoss A : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data :
      PureWZ2LocallyLinearHierarchyData source finalLoss hierarchyLoss)
    (hA : WZ1SmoothSegmentExtensionAtConstantStatement A)
    (hhierarchyLoss : 0 ≤ hierarchyLoss)
    (hcostAbsorb :
      (data.hierarchy.levelCount : ℝ) * 136 ≤
        Real.rpow delta (-hierarchyLoss)) :
    Nonempty
      { raw : PureWZ2RawC2GlobalGrainData
          data.shading sigma
          (Kakeya.realRpowENN delta (-finalLoss))
          (1 / (data.hierarchy.levelCount : ℝ) + 2 * hierarchyLoss) A //
        PureWZ2RawC2GlobalBoundData raw } := by
  rcases data.ordinaryRawGlobalGrains hA hhierarchyLoss hcostAbsorb with
    ⟨output⟩
  exact ⟨⟨output.raw, output.globalBounds⟩⟩

end Kakeya.Assouad

end
