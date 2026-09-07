import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SubfamilyShadingExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ExtremalCWATransfer

/-!
# Extend a grain configuration from a tube subfamily

The geometric construction may run on a genuine tube subfamily selected by
Node 3.  Extending its shading by empty carriers preserves the union and
mass exactly.  Hence local and global AD transport without changing their
sets, while the incidence field only needs the subfamily tube identity.

Family-level extremality is supplied separately: this module is only the
dependent reindexing boundary and does not assert hereditary CWA.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- Cubicality survives zero-extension from a tube subfamily. -/
lemma extendShading_cubical
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {shading : WZ1PaperTubeShading selected.family}
    (hcubical : WZ1PaperIsCubicalShading shading) :
    WZ1PaperIsCubicalShading (extendShading selected shading) := by
  intro ambientIndex point hpoint other hother
  by_cases himage : ∃ selectedIndex,
      selected.embedding selectedIndex = ambientIndex
  · rcases himage with ⟨selectedIndex, rfl⟩
    rw [extendShading_carrier_mem] at hpoint ⊢
    exact hcubical selectedIndex point hpoint hother
  · rw [extendShading_carrier_empty himage] at hpoint
    exact False.elim hpoint

/-- Strict local grains transport through the zero-extension. -/
def PureWZ2LocalGrainData.extendSubfamily
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {shading : WZ1PaperTubeShading selected.family}
    {C : ENNReal}
    (data : PureWZ2LocalGrainData shading sigma C) :
    PureWZ2LocalGrainData (extendShading selected shading) sigma C := by
  let hunion : (extendShading selected shading).union = shading.union :=
    extendShading_union selected shading
  let planeMap :
      {point : Point3 // point ∈ (extendShading selected shading).union} →
        Point3 :=
    fun point => data.planeMap ⟨point, hunion ▸ point.prop⟩
  refine
    { planeMap := planeMap
      planeMap_lipschitz := ?_
      planeMap_unit := ?_
      planeMap_incidence := ?_
      local_ad := ?_ }
  · intro first second
    exact data.planeMap_lipschitz
      ⟨first, hunion ▸ first.prop⟩ ⟨second, hunion ▸ second.prop⟩
  · intro point
    exact data.planeMap_unit ⟨point, hunion ▸ point.prop⟩
  · intro ambientIndex point hpoint
    by_cases himage : ∃ selectedIndex,
        selected.embedding selectedIndex = ambientIndex
    · rcases himage with ⟨selectedIndex, rfl⟩
      rw [extendShading_carrier_mem] at hpoint
      simpa only [selected.tube_eq] using
        data.planeMap_incidence selectedIndex point hpoint
    · rw [extendShading_carrier_empty himage] at hpoint
      exact False.elim hpoint
  · intro rho hdeltaRho hrhoOne point
    have hsource := data.local_ad rho hdeltaRho hrhoOne
      ⟨point, hunion ▸ point.prop⟩
    simpa only [hunion] using hsource

/-- Global grains transport through the zero-extension because the complete
shaded union is unchanged. -/
def PureWZ2LipschitzGlobalGrainData.extendSubfamily
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {shading : WZ1PaperTubeShading selected.family}
    {C : ENNReal}
    (data : PureWZ2LipschitzGlobalGrainData shading sigma C) :
    PureWZ2LipschitzGlobalGrainData
      (extendShading selected shading) sigma C := by
  let hunion : (extendShading selected shading).union = shading.union :=
    extendShading_union selected shading
  exact
    { f := data.f
      lipschitz := data.lipschitz
      paper_ad := by
        intro z
        simpa only [hunion] using data.paper_ad z }

/-- Assemble an ambient-family configuration by zero-extending one selected
shading and its two grain certificates.  Ambient line class, extremality, and
top-level CWA remain explicit inputs; none is inferred from the subfamily. -/
def grainConfigurationOfSubfamilyExtension
    {sigma loss delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {shading : WZ1PaperTubeShading selected.family}
    (hline : WZ1PaperIsLineClass family)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hambientExtremal : WZ2PaperCroppedIsExtremal sigma loss family
      (extendShading selected shading))
    (hambientCWA : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-loss)))
    (globalGrains : PureWZ2LipschitzGlobalGrainData shading sigma
      (Kakeya.realRpowENN delta (-loss)))
    (localGrains : PureWZ2LocalGrainData shading sigma
      (Kakeya.realRpowENN delta (-loss))) :
    PureWZ2GrainConfiguration sigma loss delta := by
  exact
    { family := family
      shading := extendShading selected shading
      line_class := hline
      cubical := extendShading_cubical selected hcubical
      extremal := hambientExtremal
      top_level_cwa := hambientCWA
      globalGrains := globalGrains.extendSubfamily selected
      localGrains := localGrains.extendSubfamily selected }

/-- Complete the zero-extension step from a genuine tube subfamily.  The
selected shading only has to be a carrierwise refinement of the ambient
source shading, and its full mass loss is exposed.  In particular, nearby
CWA is never inherited by the selected tube family: it stays on `family` and
enters the final configuration through the ambient extremal certificate. -/
theorem subfamily_grain_configuration_extension
    {sigma sourceLoss outputLoss delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {shading : WZ1PaperTubeShading selected.family}
    (hline : WZ1PaperIsLineClass family)
    (hsourceExtremal :
      WZ2PaperCroppedIsExtremal sigma sourceLoss family source)
    (hsourceCWA : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-sourceLoss)))
    (hsub : ∀ index, shading.carrier index ⊆
      source.carrier (selected.embedding index))
    (hcubical : WZ1PaperIsCubicalShading shading)
    (massLoss : ENNReal)
    (hmassLossPos : 0 < massLoss)
    (hmassLossFinite : massLoss ≠ ⊤)
    (hmass : massLoss⁻¹ * source.mass ≤ shading.mass)
    (hloss : sourceLoss ≤ outputLoss)
    (hslack : massLoss * Kakeya.realRpowENN delta outputLoss ≤
      Kakeya.realRpowENN delta sourceLoss)
    (houtputLoss : 0 < outputLoss)
    (globalGrains : PureWZ2LipschitzGlobalGrainData shading sigma
      (Kakeya.realRpowENN delta (-outputLoss)))
    (localGrains : PureWZ2LocalGrainData shading sigma
      (Kakeya.realRpowENN delta (-outputLoss))) :
    Nonempty (PureWZ2GrainConfiguration sigma outputLoss delta) := by
  have hextendedSub : PaperIsSubshading
      (extendShading selected shading) source := by
    intro ambientIndex point hpoint
    by_cases himage : ∃ selectedIndex,
        selected.embedding selectedIndex = ambientIndex
    · rcases himage with ⟨selectedIndex, rfl⟩
      rw [extendShading_carrier_mem] at hpoint
      exact hsub selectedIndex hpoint
    · rw [extendShading_carrier_empty himage] at hpoint
      exact False.elim hpoint
  have hextendedMass : massLoss⁻¹ * source.mass ≤
      (extendShading selected shading).mass := by
    rw [extendShading_mass]
    exact hmass
  have hextendedExtremal : WZ2PaperCroppedIsExtremal
      sigma outputLoss family (extendShading selected shading) :=
    transfer_cropped_extremal_to_subshading
      massLoss hmassLossPos hmassLossFinite hsourceExtremal
      hextendedSub hextendedMass (extendShading_cubical selected hcubical)
      hloss hslack hsourceExtremal.delta_pos
      hsourceExtremal.delta_le_one houtputLoss
  have hextendedCWA : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-outputLoss)) :=
    PureWZ2.transfer_cwa_to_subshading
      (_shading1 := source)
      (_shading2 := extendShading selected shading)
      hsourceCWA hloss hsourceExtremal.delta_pos
      hsourceExtremal.delta_le_one
  exact ⟨grainConfigurationOfSubfamilyExtension selected hline hcubical
    hextendedExtremal hextendedCWA globalGrains localGrains⟩

end Kakeya.Assouad

end
