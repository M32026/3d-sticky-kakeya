import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeSelectedLocalGrain

/-!
# Initial local grains for Proposition 6.3

The paper constructs local grains before choosing its exact power-scale
metric fibre.  Consequently this continuation records only a genuine
subshading of the Node-3 fine shading and local grains on that same shading.
It deliberately imposes no integral relation between the fine and parent
scales.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- A provenance-preserving local-grain refinement of one balanced fine
shading. -/
structure Proposition63InitialRebalancedData
    {delta rho sigma outputLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (original : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := outputLoss)
      (coefficient := coefficient) fineShading)
    (hdelta : 0 < delta) where
  shading : WZ1PaperTubeShading fine
  subshading : PaperIsSubshading shading fineShading
  cubical : WZ1PaperIsCubicalShading shading
  mass_pos : 0 < shading.mass
  incidence_le_parent_half : initial.incidence ≤ rho / 2
  localGrains : Proposition63InitialWeakLocalGrainData
    (incidence := initial.incidence) shading sigma
    (Kakeya.realRpowENN delta (-outputLoss))
    (Real.toNNReal coefficient)

/-- Retain the initial finite-planiness shading and its local grains without
an integer-alignment or exact-rebalancing hypothesis. -/
theorem proposition63_initial_rebalance
    {delta rho sigma outputLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (original : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := outputLoss)
      (coefficient := coefficient) fineShading)
    (hdelta : 0 < delta)
    (hincidence : initial.incidence ≤ rho / 2) :
    Nonempty (Proposition63InitialRebalancedData
      original initial hdelta) := by
  exact ⟨{
    shading := initial.planiness.refinement.shading
    subshading := initial.planiness.refinement.subshading
    cubical := initial.planiness.refinement.cubical
    mass_pos := initial.planiness_mass_pos
    incidence_le_parent_half := hincidence
    localGrains := initial.localGrains
  }⟩

end Kakeya.Assouad.PureWZ2

end
