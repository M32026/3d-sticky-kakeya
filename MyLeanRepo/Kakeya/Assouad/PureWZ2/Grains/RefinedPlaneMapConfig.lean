import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ExtremalTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiplicityPreservingVariation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TwoScaleLipschitzBridge

/-!
# Quantitative plane maps on genuine shading refinements

The frozen grain theorem may refine its shading, but the historical A1 glue
incorrectly asked for a plane map on the complete input shading.  This module
records the paper-faithful replacement: a cubical subshading, a genuine weak
plane map on that subshading, an explicit mass-retention factor, and optional
point-multiplicity preservation for later finite-scale coordination.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- A quantitative plane-map refinement of one cropped paper shading. -/
structure RefinedPlaneMapConfig
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (incidence lipschitzConstant : ℝ) (massLoss : ENNReal) where
  shading : WZ1PaperTubeShading family
  subshading : PaperIsSubshading shading source
  cubical : WZ1PaperIsCubicalShading shading
  planeMap : PaperWZ1WeakPlaneMapData shading incidence
  lipschitz :
    LipschitzWith (Real.toNNReal lipschitzConstant)
      (fun point : {point : Point3 // point ∈ shading.union} =>
        planeMap.planeMap point)
  mass_retention :
    source.mass ≤ massLoss * shading.mass
  massLoss_pos : 0 < massLoss
  massLoss_ne_top : massLoss ≠ ⊤
  pointMultiplicity_eq :
    ∀ point ∈ shading.union,
      shading.pointMultiplicity point = source.pointMultiplicity point

namespace RefinedPlaneMapConfig

lemma subshading_union
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {selected source : WZ1PaperTubeShading family}
    (hsub : PaperIsSubshading selected source) :
    selected.union ⊆ source.union := by
  rintro point ⟨index, hpoint⟩
  exact ⟨index, hsub index hpoint⟩

/-- Restrict a quantitative plane-map refinement once more along a common
spatial restriction.  The caller supplies the new cubicality, mass factor,
and preservation identity; the underlying plane map is unchanged. -/
def restrict
    {delta incidence lipschitzConstant : ℝ}
    {firstLoss secondLoss : ENNReal}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (data :
      RefinedPlaneMapConfig source incidence lipschitzConstant firstLoss)
    (selected : WZ1PaperTubeShading family)
    (hselectedSub : PaperIsSubshading selected data.shading)
    (hselectedCubical : WZ1PaperIsCubicalShading selected)
    (hselectedMass :
      data.shading.mass ≤ secondLoss * selected.mass)
    (hsecondLossPos : 0 < secondLoss)
    (hsecondLossFinite : secondLoss ≠ ⊤)
    (hselectedMultiplicity :
      ∀ point ∈ selected.union,
        selected.pointMultiplicity point = data.shading.pointMultiplicity point) :
    RefinedPlaneMapConfig source incidence lipschitzConstant
      (firstLoss * secondLoss) where
  shading := selected
  subshading index := (hselectedSub index).trans (data.subshading index)
  cubical := hselectedCubical
  planeMap := paperWeakPlaneMapRestrict data.planeMap hselectedSub
  lipschitz := by
    have hselectedData : selected.union ⊆ data.shading.union :=
      subshading_union hselectedSub
    intro first second
    exact data.lipschitz
      ⟨first, hselectedData first.prop⟩
      ⟨second, hselectedData second.prop⟩
  mass_retention := by
    calc
      source.mass ≤ firstLoss * data.shading.mass := data.mass_retention
      _ ≤ firstLoss * (secondLoss * selected.mass) := by gcongr
      _ = (firstLoss * secondLoss) * selected.mass := by ring
  massLoss_pos := ENNReal.mul_pos
    data.massLoss_pos.ne' hsecondLossPos.ne'
  massLoss_ne_top :=
    ENNReal.mul_ne_top data.massLoss_ne_top hsecondLossFinite
  pointMultiplicity_eq := by
    intro point hpoint
    have hpointData : point ∈ data.shading.union :=
      subshading_union hselectedSub hpoint
    exact (hselectedMultiplicity point hpoint).trans
      (data.pointMultiplicity_eq point hpointData)

/-- Transfer cropped extremality from the source shading to a quantitative
plane-map refinement, paying exactly its recorded mass-loss factor. -/
theorem extremal
    {delta incidence lipschitzConstant sigma sourceLoss targetLoss : ℝ}
    {massLoss : ENNReal}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (data :
      RefinedPlaneMapConfig source incidence lipschitzConstant massLoss)
    (hsourceExtremal :
      WZ2PaperCroppedIsExtremal
        sigma sourceLoss family source)
    (hloss : sourceLoss ≤ targetLoss)
    (hslack :
      massLoss * Kakeya.realRpowENN delta targetLoss ≤
        Kakeya.realRpowENN delta sourceLoss)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (htargetLoss : 0 < targetLoss) :
    WZ2PaperCroppedIsExtremal
      sigma targetLoss family data.shading :=
  by
    have hinverseMass : massLoss⁻¹ * source.mass ≤ data.shading.mass := by
      calc
        massLoss⁻¹ * source.mass ≤
            massLoss⁻¹ * (massLoss * data.shading.mass) := by
          exact mul_le_mul_left' data.mass_retention massLoss⁻¹
        _ = data.shading.mass := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel
            data.massLoss_pos.ne' data.massLoss_ne_top, one_mul]
    exact transfer_cropped_extremal_to_subshading
      massLoss data.massLoss_pos data.massLoss_ne_top
      hsourceExtremal data.subshading hinverseMass data.cubical
      hloss hslack hdelta hdeltaOne htargetLoss

/-- Package the two-scale Lipschitz refinement in the quantitative interface.
This is the terminal bridge used after a finite family of one-scale variation
estimates has been coordinated on one nested shading. -/
theorem of_two_scale_variation
    {delta rho coefficient incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hcoefficient : 0 ≤ coefficient)
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (planeMap : PaperWZ1WeakPlaneMapData source incidence)
    (hcell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second)
    (hcoarse : ∀ first ∈ source.union, ∀ second ∈ source.union,
      dist first second ≤ rho →
        dist (planeMap.planeMap first)
          (planeMap.planeMap second) ≤ coefficient * rho) :
    Nonempty
      (RefinedPlaneMapConfig source incidence
        (max (coefficient * rho / delta) (2 / rho)) 27) := by
  rcases paper_fine_cell_residue_refinement_cubical
      (scale := 0) planeMap.planeMap hdelta hsourceCubical (by
        intro first _ second _ hgrid
        rw [hcell first second hgrid]
        simp) with
    ⟨selected, hselectedSub, hselectedCubical, hfineVariation,
      hselectedMultiplicity, hmass⟩
  let selectedPlaneMap := paperWeakPlaneMapRestrict planeMap hselectedSub
  have hfineEquality : ∀ first ∈ selected.union,
      ∀ second ∈ selected.union, dist first second ≤ delta →
        selectedPlaneMap.planeMap first =
          selectedPlaneMap.planeMap second := by
    intro first hfirst second hsecond hdist
    have hzero := hfineVariation first hfirst second hsecond hdist
    exact dist_eq_zero.mp (le_antisymm hzero dist_nonneg)
  have hcoarseSelected : ∀ first ∈ selected.union,
      ∀ second ∈ selected.union, dist first second ≤ rho →
        dist (selectedPlaneMap.planeMap first)
          (selectedPlaneMap.planeMap second) ≤ coefficient * rho := by
    intro first hfirst second hsecond hdist
    have hfirstSource : first ∈ source.union :=
      subshading_union hselectedSub hfirst
    have hsecondSource : second ∈ source.union :=
      subshading_union hselectedSub hsecond
    exact hcoarse first hfirstSource second hsecondSource hdist
  have hlipschitz := paper_two_scale_lipschitz_bridge
    hdelta hrho hcoefficient selectedPlaneMap.planeMap
    selectedPlaneMap.unit hfineEquality hcoarseSelected
  refine ⟨{
    shading := selected
    subshading := hselectedSub
    cubical := hselectedCubical
    planeMap := selectedPlaneMap
    lipschitz := hlipschitz
    mass_retention := ?_
    massLoss_pos := by norm_num
    massLoss_ne_top := by norm_num
    pointMultiplicity_eq := hselectedMultiplicity
  }⟩
  simpa using hmass

end RefinedPlaneMapConfig

end Kakeya.Assouad.PureWZ2

end
