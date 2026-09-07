import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SourceWitnessCoarsePlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WholeCellBalancedRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSpatialInvariant

/-!
# Balanced output of the source-witness coarse plane-map refinement

The mod-three residue refinement is not an arbitrary coarse subshading.  At
every surviving point it preserves the complete active parent set.  Hence it
is exactly a common-spatial restriction, and the frozen balanced cover can be
restricted to those whole coarse cells without a hereditary-sticky premise.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The source-witness Lip-1 coarse map together with the honest balanced
cover induced on its selected common-spatial shading. -/
structure PureWZ2SourceWitnessCoarseLipschitzBalancedData
    {delta rho target : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (sourceWitness : PureWZ2SourceWitnessCoarseShadingData balanced) where
  selected : WZ1PaperTubeShading coarse
  planeMap : PaperWZ1WeakPlaneMapData selected target
  subshading : PaperIsSubshading selected sourceWitness.shading
  cubical : WZ1PaperIsCubicalShading selected
  pointMultiplicity_eq : ∀ point ∈ selected.union,
    selected.pointMultiplicity point =
      sourceWitness.shading.pointMultiplicity point
  mass_retention : sourceWitness.shading.mass ≤ 27 * selected.mass
  lipschitz : LipschitzWith 1
    (fun point : {point : Point3 // point ∈ selected.union} =>
      planeMap.planeMap point)
  /-- The sampled normal is constant on each cell of the coarse `rho` grid.
  This is the exact cellwise part of the paper's `existenceOfPlaneMap` output
  retained for the subsequent finite grain-structure iteration. -/
  planeMap_cellwise : ∀ first second,
    wz1PaperGridIndex rho first = wz1PaperGridIndex rho second →
      planeMap.planeMap first = planeMap.planeMap second
  common_spatial : ∀ parent,
    selected.carrier parent =
      sourceWitness.shading.carrier parent ∩ selected.union
  balancedRestriction : PureWZ2BalancedCoverData cover
    (propertyThreeFinePullbackShading cover fineShading selected) selected

/-- Upgrade the source-witness coarse plane-map theorem with the balanced
cover that is already implicit in its multiplicity-preserving residue
restriction. -/
theorem source_witness_coarse_plane_map_lipschitz_one_balanced
    {delta rho incidence target : ℝ}
    {K : NNReal}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (sourceWitness : PureWZ2SourceWitnessCoarseShadingData balanced)
    (hrho : 0 < rho)
    (finePlaneMap : PaperWZ1WeakPlaneMapData fineShading incidence)
    (hfineLipschitz : LipschitzWith K
      (fun point : {point : Point3 // point ∈ fineShading.union} =>
        finePlaneMap.planeMap point))
    (hK : (K : ℝ) ≤ 1 / 5)
    (hbudget :
      incidence + (K : ℝ) * (rho * Real.sqrt 3) + rho / 2 ≤ target) :
    Nonempty
      (PureWZ2SourceWitnessCoarseLipschitzBalancedData
        (target := target) sourceWitness) := by
  rcases source_witness_coarse_plane_map_lipschitz_one
      sourceWitness hrho finePlaneMap hfineLipschitz hK hbudget with
    ⟨selected, planeMap, hsub, hcubical, hmultiplicity, hmass,
      hcellwise, hlipschitz⟩
  have hcommon : ∀ parent,
      selected.carrier parent =
        sourceWitness.shading.carrier parent ∩ selected.union :=
    carrier_eq_source_inter_union_of_multiplicity_eq
      hsub hmultiplicity
  let restrictedBalanced : PureWZ2BalancedCoverData cover
      (propertyThreeFinePullbackShading cover fineShading selected) selected :=
    wholeCellBalancedRestriction sourceWitness.balanced
      hsub hcubical hcommon
  exact ⟨{
    selected := selected
    planeMap := planeMap
    subshading := hsub
    cubical := hcubical
    pointMultiplicity_eq := hmultiplicity
    mass_retention := hmass
    lipschitz := hlipschitz
    planeMap_cellwise := hcellwise
    common_spatial := hcommon
    balancedRestriction := restrictedBalanced
  }⟩

end Kakeya.Assouad.PureWZ2

end
