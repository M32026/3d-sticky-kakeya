import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MetricFiberInput

/-!
# The first Proposition 6.3 refinement and metric fibre

This module packages the part of `wz2_63.tex` preceding the common-slice
argument.  Property Three and finite planiness are first run on the genuine
pullback of one Node-3 sticky output.  Their final shading is then viewed as a
refinement of that same output's `sticky.refined`, with an explicit density
lower bound.  Only after that bookkeeping has been completed do we choose a
complete metric fibre.

The original balanced cover and the frozen full-fibre rescaling certificates
are used verbatim; no replacement family or independently chosen extremizer
enters this stage.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The first planiness output, rebased on the actual Node-3 fine shading,
together with the density lower bound used to select a complete metric
fibre. -/
structure Proposition63FirstStageData
    {delta sigma stickyLoss localLoss coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (sourceDensity : ENNReal) where
  delta_pos : 0 < delta
  initial : PropertyThreeSelectedInitialLocalData
    (sigma := sigma) (outputLoss := localLoss)
    (coefficient := coefficient) sticky.refined
  incidence_le_parent_half : initial.incidence ≤ rho.1 / 2
  source_density :
    sourceDensity * sticky.selected.family.enncard *
        Kakeya.realRpowENN delta 2 ≤
      initial.planiness.refinement.shading.mass

/-- The ambient density actually carried by the first finite-planiness
refinement.  This is a quotient of its shaded mass by the genuine selected
family size and the fine tube-volume scale; it is not a free parameter. -/
noncomputable def proposition63CanonicalAmbientDensity
    {delta sigma outputLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading fine}
    (initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := outputLoss)
      (coefficient := coefficient) source) : ENNReal :=
  initial.planiness.refinement.shading.mass /
    (fine.enncard * Kakeya.realRpowENN delta 2)

/-- The canonical ambient density recovers the full mass after multiplying
by the actual family size and fine cross-sectional scale. -/
theorem proposition63CanonicalAmbientDensity_spec
    {delta sigma outputLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading fine}
    (initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := outputLoss)
      (coefficient := coefficient) source)
    (hdelta : 0 < delta)
    (hfine : fine.Nonempty) :
    proposition63CanonicalAmbientDensity initial * fine.enncard *
        Kakeya.realRpowENN delta 2 =
      initial.planiness.refinement.shading.mass := by
  have hcardZero : fine.enncard ≠ 0 := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using hfine.ne'
  have hcardTop : fine.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hpowerZero : Kakeya.realRpowENN delta 2 ≠ 0 := by
    simp [Kakeya.realRpowENN, hdelta.ne']
  have hpowerTop : Kakeya.realRpowENN delta 2 ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hdenomZero :
      fine.enncard * Kakeya.realRpowENN delta 2 ≠ 0 :=
    mul_ne_zero hcardZero hpowerZero
  have hdenomTop :
      fine.enncard * Kakeya.realRpowENN delta 2 ≠ ⊤ :=
    ENNReal.mul_ne_top hcardTop hpowerTop
  change
    (initial.planiness.refinement.shading.mass /
        (fine.enncard * Kakeya.realRpowENN delta 2)) *
        fine.enncard * Kakeya.realRpowENN delta 2 = _
  rw [mul_assoc, ENNReal.div_mul_cancel hdenomZero hdenomTop]

/-- Compose the Property-Three pullback loss with finite planiness, without
changing the Node-3 family.  The only quantitative input left to the outer
small-scale argument is the displayed absorption into the normalized
one-sided mass-loss constant. -/
theorem proposition63_first_stage
    {delta sigma stickyLoss localLoss tau epsilon₁ epsilon₃ coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (pullbackInitial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient)
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propP.propertyThree))
    (hdelta : 0 < delta)
    (hincidence :
      (pullbackInitial.onStickyRefined sticky propP hdelta).incidence ≤
        rho.1 / 2)
    (sourceDensity : ENNReal)
    (habsorb :
      sourceDensity * sticky.selected.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        (pullbackInitial.onStickyRefined sticky propP hdelta).planiness.massLoss⁻¹ *
          sticky.refined.mass) :
    Nonempty (Proposition63FirstStageData
      (localLoss := localLoss) (coefficient := coefficient)
      sticky sourceDensity) := by
  let initial := pullbackInitial.onStickyRefined sticky propP hdelta
  have hsourceDensity :
      sourceDensity * sticky.selected.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        initial.planiness.refinement.shading.mass := by
    exact habsorb.trans
      initial.planiness.massLoss_inv_mul_source_mass_le
  exact ⟨{
    delta_pos := hdelta
    initial := initial
    incidence_le_parent_half := hincidence
    source_density := hsourceDensity
  }⟩

namespace Proposition63FirstStageData

/-- Select the paper's complete metric fibre using the original balanced
cover and the original frozen Node-3 rescaling certificate. -/
theorem metricFiberInput
    {delta sigma stickyLoss localLoss coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent}
    {sourceDensity : ENNReal}
    (stage : Proposition63FirstStageData
      (localLoss := localLoss) (coefficient := coefficient)
      sticky sourceDensity) :
    ∃ rebalanced : Proposition63InitialRebalancedData
        (outputLoss := localLoss) (coefficient := coefficient)
        sticky.balanced stage.initial stage.delta_pos,
      Nonempty (Proposition63MetricFiberInputData
        (stickyLoss := stickyLoss) (localLoss := localLoss)
        (coefficient := coefficient) (hdelta := stage.delta_pos) rebalanced
        sticky.coarse_extremal.delta_pos) := by
  let rebalanced : Proposition63InitialRebalancedData
      sticky.balanced stage.initial stage.delta_pos :=
    { shading := stage.initial.planiness.refinement.shading
      subshading := stage.initial.planiness.refinement.subshading
      cubical := stage.initial.planiness.refinement.cubical
      mass_pos := stage.initial.planiness_mass_pos
      incidence_le_parent_half := stage.incidence_le_parent_half
      localGrains := stage.initial.localGrains }
  have hcoarseNonempty : sticky.coarse.Nonempty := by
    let sourceIndex : Fin sticky.selected.family.card :=
      ⟨0, sticky.selected_nonempty⟩
    rcases sticky.cover.covers sourceIndex with ⟨parent, _⟩
    exact Nat.zero_lt_of_lt parent.isLt
  refine ⟨rebalanced, ?_⟩
  exact proposition63_metric_fiber_input sticky.rescaledFiber rebalanced
    sourceDensity (by
      change sourceDensity * sticky.selected.family.enncard *
          Kakeya.realRpowENN delta 2 ≤ rebalanced.shading.mass
      exact stage.source_density) hcoarseNonempty

end Proposition63FirstStageData

end Kakeya.Assouad.PureWZ2

end
