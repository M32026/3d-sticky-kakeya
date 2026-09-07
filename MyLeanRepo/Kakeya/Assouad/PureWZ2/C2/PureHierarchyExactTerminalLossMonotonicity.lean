import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyExactTerminalAssembly

/-!
# Loss monotonicity for exact terminal hierarchy levels

An exact terminal level constructed at a smaller working loss remains valid
at a larger requested loss.  The source, shading, trapezoids, and source-slope
provenance are unchanged.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Weaken an exact terminal level to a larger loss without changing its
geometric data. -/
noncomputable def PureWZ2ExactTerminalLevelData.mono_loss
    {sigma inputLoss delta firstLoss secondLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2ExactTerminalLevelData source firstLoss)
    (hloss : firstLoss ≤ secondLoss) :
    PureWZ2ExactTerminalLevelData source secondLoss := by
  let hself : PureWZ2PaperIsSubshading data.shading data.shading :=
    fun _ => Set.Subset.rfl
  have hconstant :
      Kakeya.realRpowENN delta (-firstLoss) ≤
        Kakeya.realRpowENN delta (-secondLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one hloss
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
      source.extremal.delta_pos source.extremal.delta_le_one (by linarith)
  have hlength :
      ∀ trapezoid ∈ data.trapezoids,
        Real.rpow delta (1 / 2 + secondLoss) ≤ trapezoid.length ∧
          trapezoid.length ≤ Real.sqrt delta := by
    intro trapezoid htrapezoid
    have hpower :
        Real.rpow delta (1 / 2 + secondLoss) ≤
          Real.rpow delta (1 / 2 + firstLoss) :=
      Real.rpow_le_rpow_of_exponent_ge
        source.extremal.delta_pos source.extremal.delta_le_one (by linarith)
    exact
      ⟨hpower.trans (data.length_bounds trapezoid htrapezoid).1,
        (data.length_bounds trapezoid htrapezoid).2⟩
  exact
    { shading := data.shading
      subshading := data.subshading
      volume_lower := hvolumePower.trans data.volume_lower
      localGrains := localGrains
      planeMap_vertical_bound := data.planeMap_vertical_bound
      sourceGlobalGrains := globalGrains
      source_slope_eq := by
        change data.sourceGlobalGrains.slope = source.globalGrains.slope
        exact data.source_slope_eq
      trapezoids := data.trapezoids
      trapezoids_nonempty := data.trapezoids_nonempty
      height_eq := data.height_eq
      slope_bound := data.slope_bound
      length_bounds := hlength
      separated_cores := data.separated_cores
      slope_approximation := by
        intro trapezoid htrapezoid z hz hslice
        change |data.sourceGlobalGrains.slope z - trapezoid.affine z| ≤ delta
        exact data.slope_approximation trapezoid htrapezoid z hz hslice
      active_height_coverage := data.active_height_coverage }

@[simp] theorem PureWZ2ExactTerminalLevelData.mono_loss_shading
    {sigma inputLoss delta firstLoss secondLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2ExactTerminalLevelData source firstLoss)
    (hloss : firstLoss ≤ secondLoss) :
    (data.mono_loss hloss).shading = data.shading := rfl

@[simp] theorem PureWZ2ExactTerminalLevelData.mono_loss_trapezoids
    {sigma inputLoss delta firstLoss secondLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2ExactTerminalLevelData source firstLoss)
    (hloss : firstLoss ≤ secondLoss) :
    (data.mono_loss hloss).trapezoids = data.trapezoids := rfl

@[simp] theorem PureWZ2ExactTerminalLevelData.mono_loss_source_slope
    {sigma inputLoss delta firstLoss secondLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2ExactTerminalLevelData source firstLoss)
    (hloss : firstLoss ≤ secondLoss) :
    (data.mono_loss hloss).sourceGlobalGrains.slope =
      source.globalGrains.slope := data.source_slope_eq

end Kakeya.Assouad

end
