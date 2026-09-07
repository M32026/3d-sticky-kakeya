import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalAnalyticSchedule

/-!
# Loss monotonicity for pure one-scale outputs

The analytic construction is run with a small working loss.  This adapter
weakens the result to any larger requested loss without changing its family,
shading, plane map, source slope, scale, or trapezoid hierarchy.
-/

noncomputable section

namespace Kakeya.Assouad

theorem PureWZ2LocallyLinearOneScaleData.mono_loss
    {sigma inputLoss delta workLoss requestedLoss rho : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2LocallyLinearOneScaleData source workLoss rho)
    (hloss : workLoss ≤ requestedLoss) :
    Nonempty
      (PureWZ2LocallyLinearOneScaleData source requestedLoss rho) := by
  let hself : PureWZ2PaperIsSubshading data.shading data.shading :=
    fun _ => Set.Subset.rfl
  have hconstant :
      Kakeya.realRpowENN delta (-workLoss) ≤
        Kakeya.realRpowENN delta (-requestedLoss) :=
    pureWZ2_grain_constant_mono data.extremal.delta_pos
      data.extremal.delta_le_one hloss
  have hconstantTop :
      Kakeya.realRpowENN delta (-requestedLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := data.localGrains.restrictWithConstant
    hself hconstant hconstantTop
  let globalGrains := data.globalGrains.restrict
    hself hconstant hconstantTop
  have hvolumePower :
      Kakeya.realRpowENN delta (sigma + requestedLoss) ≤
        Kakeya.realRpowENN delta (sigma + workLoss) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge
      data.extremal.delta_pos data.extremal.delta_le_one (by linarith)
  have hlength :
      ∀ trapezoid ∈ data.trapezoids,
        Real.rpow rho (1 / 2 + requestedLoss) ≤ trapezoid.length ∧
          trapezoid.length ≤ Real.sqrt rho := by
    intro trapezoid htrapezoid
    have hpower :
        Real.rpow rho (1 / 2 + requestedLoss) ≤
          Real.rpow rho (1 / 2 + workLoss) :=
      Real.rpow_le_rpow_of_exponent_ge
        data.rho_pos data.rho_le_one (by linarith)
    exact ⟨hpower.trans (data.length_bounds trapezoid htrapezoid).1,
      (data.length_bounds trapezoid htrapezoid).2⟩
  exact ⟨{
    rho_pos := data.rho_pos
    delta_le_rho := data.delta_le_rho
    rho_le_one := data.rho_le_one
    shading := data.shading
    subshading := data.subshading
    whole_cells := data.whole_cells
    extremal := data.extremal.mono_loss hloss
    volume_lower := hvolumePower.trans data.volume_lower
    localGrains := localGrains
    planeMap_vertical_bound := by
      intro point
      exact data.planeMap_vertical_bound point
    globalGrains := globalGrains
    slope_eq := data.slope_eq
    trapezoids := data.trapezoids
    trapezoids_nonempty := data.trapezoids_nonempty
    height_eq := data.height_eq
    slope_bound := data.slope_bound
    length_bounds := hlength
    separated_cores := data.separated_cores
    slope_approximation := by
      intro trapezoid htrapezoid z hz hslice
      have hslope : globalGrains.slope = data.globalGrains.slope := rfl
      rw [hslope]
      exact data.slope_approximation trapezoid htrapezoid z hz hslice
    active_height_coverage := data.active_height_coverage
  }⟩

namespace PureWZ2LocallyLinearHierarchyData

/-- Weaken only the final loss of a completed hierarchy.  The geometric
hierarchy loss, shading, trapezoids, and source-slope provenance are unchanged. -/
noncomputable def mono_finalLoss
    {sigma inputLoss delta firstLoss secondLoss hierarchyLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2LocallyLinearHierarchyData
      source firstLoss hierarchyLoss)
    (hloss : firstLoss ≤ secondLoss) :
    PureWZ2LocallyLinearHierarchyData
      source secondLoss hierarchyLoss := by
  let hself : PureWZ2PaperIsSubshading data.shading data.shading :=
    fun _ => Set.Subset.rfl
  have hconstant :
      Kakeya.realRpowENN delta (-firstLoss) ≤
        Kakeya.realRpowENN delta (-secondLoss) :=
    pureWZ2_grain_constant_mono data.delta_pos data.delta_le_one hloss
  have hconstantTop :
      Kakeya.realRpowENN delta (-secondLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := data.localGrains.restrictWithConstant
    hself hconstant hconstantTop
  let globalGrains := data.sourceGlobalGrains.restrict
    hself hconstant hconstantTop
  have hvolumePower :
      Kakeya.realRpowENN delta (sigma + secondLoss) ≤
        Kakeya.realRpowENN delta (sigma + firstLoss) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge
      data.delta_pos data.delta_le_one (by linarith)
  exact
    { levelCount := data.levelCount
      levelCount_two := data.levelCount_two
      delta_pos := data.delta_pos
      delta_le_one := data.delta_le_one
      shading := data.shading
      subshading := data.subshading
      volume_lower := hvolumePower.trans data.volume_lower
      localGrains := localGrains
      planeMap_vertical_bound := by
        intro point
        exact data.planeMap_vertical_bound point
      sourceGlobalGrains := globalGrains
      source_slope_eq := data.source_slope_eq
      hierarchy := data.hierarchy }

@[simp] theorem mono_finalLoss_levelCount
    {sigma inputLoss delta firstLoss secondLoss hierarchyLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2LocallyLinearHierarchyData
      source firstLoss hierarchyLoss)
    (hloss : firstLoss ≤ secondLoss) :
    (data.mono_finalLoss hloss).hierarchy.levelCount =
      data.hierarchy.levelCount := rfl

end PureWZ2LocallyLinearHierarchyData

end Kakeya.Assouad
