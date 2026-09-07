import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RebalancedFiniteRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SourceWitnessCoarsePlaneMapBalanced

/-!
# Push a rebalanced finite plane map to the coarse family

Finite planiness refinements may delete individual tube memberships.  The
rebalancing step restores an honest balanced cover on a further fine
subshading.  This module records that the existing weak plane map restricts
to the rebalanced shading and can then be sampled on the source-witness
coarse shading.

No new geometric or quantitative hypothesis is introduced here: incidence
and the Lipschitz coefficient are unchanged by restriction, and the only
coarse error is the explicit sampling budget of
`source_witness_coarse_plane_map_lipschitz_one_balanced`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- Restrict a finite weak plane map through exact rebalancing, then push it
to an exact-incidence Lip-1 map on a source-witness coarse shading. -/
theorem rebalanced_source_witness_coarse_plane_map_lipschitz_one
    {delta rho incidence target : ℝ}
    {K : NNReal}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading candidate : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (original :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hdelta : 0 < delta)
    (rebalanced :
      PureWZ2RebalancedFiniteRefinementData original candidate hdelta)
    (planeMap : PaperWZ1WeakPlaneMapData candidate incidence)
    (hlipschitz : LipschitzWith K
      (fun point : {point : Point3 // point ∈ candidate.union} =>
        planeMap.planeMap point))
    (hrho : 0 < rho)
    (hK : (K : ℝ) ≤ 1 / 5)
    (hbudget :
      incidence + (K : ℝ) * (rho * Real.sqrt 3) + rho / 2 ≤
        target) :
    ∃ sourceWitness :
        PureWZ2SourceWitnessCoarseShadingData rebalanced.balanced,
      Nonempty
        (PureWZ2SourceWitnessCoarseLipschitzBalancedData
          (target := target) sourceWitness) := by
  have hrefinedUnion : rebalanced.balancing.refined.union ⊆
      candidate.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, rebalanced.refined_subshading index hpoint⟩
  let refinedPlaneMap :
      PaperWZ1WeakPlaneMapData rebalanced.balancing.refined incidence :=
    paperWeakPlaneMapRestrict planeMap rebalanced.refined_subshading
  have hrefinedLipschitz : LipschitzWith K
      (fun point :
          {point : Point3 // point ∈ rebalanced.balancing.refined.union} =>
        refinedPlaneMap.planeMap point) := by
    intro first second
    exact hlipschitz
      ⟨first, hrefinedUnion first.prop⟩
      ⟨second, hrefinedUnion second.prop⟩
  rcases source_witness_coarse_shading rebalanced.balanced with
    ⟨sourceWitness⟩
  exact ⟨sourceWitness,
    source_witness_coarse_plane_map_lipschitz_one_balanced
      sourceWitness hrho refinedPlaneMap hrefinedLipschitz hK hbudget⟩

end Kakeya.Assouad.PureWZ2

end
