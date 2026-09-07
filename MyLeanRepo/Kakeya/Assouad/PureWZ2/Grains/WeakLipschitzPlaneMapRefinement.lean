import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RefinedPlaneMapConfig
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SubfamilyShadingExtension

/-!
# Quantitative weak plane-map refinements

The dense and sparse planiness branches do not preserve point multiplicity
relative to the original ambient shading.  This interface records the data
they genuinely share: a cubical subshading, a unit weak plane map, a unit
Lipschitz bound, and an explicit two-sided mass account.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- Restrict a weak plane map to a tube subfamily without changing its
ambient point function. -/
noncomputable def PaperWZ1WeakPlaneMapData.restrictSubfamily
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (planeMap : PaperWZ1WeakPlaneMapData shading incidence)
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    PaperWZ1WeakPlaneMapData
      (restrictPaperShading selected shading) incidence where
  planeMap := planeMap.planeMap
  measurable := planeMap.measurable
  unit := by
    intro point hpoint
    rcases hpoint with ⟨index, hindex⟩
    exact planeMap.unit point ⟨selected.embedding index, hindex⟩
  incidence := by
    intro index point hpoint
    have hraw := planeMap.incidence (selected.embedding index) point hpoint
    simpa only [selected.tube_eq] using hraw

/-- Extend a weak plane map from a genuine tube subfamily by empty carriers.
The underlying point function is unchanged, and the incidence claim outside
the selected indices is vacuous. -/
noncomputable def PaperWZ1WeakPlaneMapData.extendSubfamily
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {shading : WZ1PaperTubeShading selected.family}
    (planeMap : PaperWZ1WeakPlaneMapData shading incidence) :
    PaperWZ1WeakPlaneMapData (extendShading selected shading) incidence where
  planeMap := planeMap.planeMap
  measurable := planeMap.measurable
  unit := by
    intro point hpoint
    rw [extendShading_union selected shading] at hpoint
    exact planeMap.unit point hpoint
  incidence := by
    intro ambientIndex point hpoint
    by_cases himage : ∃ selectedIndex,
        selected.embedding selectedIndex = ambientIndex
    · rcases himage with ⟨selectedIndex, rfl⟩
      rw [extendShading_carrier_mem] at hpoint
      simpa only [selected.tube_eq] using
        planeMap.incidence selectedIndex point hpoint
    · rw [extendShading_carrier_empty himage] at hpoint
      exact False.elim hpoint

/-- A Lipschitz certificate is unchanged by zero-extension because the shaded
union is unchanged. -/
theorem paperWeakPlaneMap_extendSubfamily_lipschitz
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {shading : WZ1PaperTubeShading selected.family}
    (planeMap : PaperWZ1WeakPlaneMapData shading incidence)
    {K : NNReal}
    (hlipschitz : LipschitzWith K
      (fun point : {point : Point3 // point ∈ shading.union} =>
        planeMap.planeMap point)) :
    LipschitzWith K
      (fun point : {point : Point3 //
        point ∈ (extendShading selected shading).union} =>
          (PaperWZ1WeakPlaneMapData.extendSubfamily
            selected planeMap).planeMap point) := by
  have hunion : (extendShading selected shading).union ⊆ shading.union := by
    rw [extendShading_union selected shading]
  intro first second
  exact hlipschitz
    ⟨first, hunion first.prop⟩ ⟨second, hunion second.prop⟩

/-- Cellwise constancy is unchanged by zero-extension because the underlying
point function is unchanged. -/
theorem paperWeakPlaneMap_extendSubfamily_cellwise
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {shading : WZ1PaperTubeShading selected.family}
    (planeMap : PaperWZ1WeakPlaneMapData shading incidence)
    (hcellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        planeMap.planeMap first = planeMap.planeMap second) :
    ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        (PaperWZ1WeakPlaneMapData.extendSubfamily
          selected planeMap).planeMap first =
        (PaperWZ1WeakPlaneMapData.extendSubfamily
          selected planeMap).planeMap second :=
  hcellwise

/-- Reindex a Lipschitz weak plane map along a tube subfamily, allowing the
target shading to be presented through an explicit equality.  Packaging the
dependent equality here avoids repeated transports of the union subtype in
downstream regularization assemblies. -/
theorem weak_plane_map_lipschitz_of_subfamily_eq
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (planeMap : PaperWZ1WeakPlaneMapData shading incidence)
    {K : NNReal}
    (hlipschitz : LipschitzWith K
      (fun point : {point : Point3 // point ∈ shading.union} =>
        planeMap.planeMap point))
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (targetShading : WZ1PaperTubeShading selected.family)
    (htarget : targetShading = restrictPaperShading selected shading) :
    ∃ targetMap : PaperWZ1WeakPlaneMapData targetShading incidence,
      LipschitzWith K
        (fun point : {point : Point3 // point ∈ targetShading.union} =>
          targetMap.planeMap point) := by
  subst targetShading
  let targetMap :=
    Kakeya.Assouad.PureWZ2.PaperWZ1WeakPlaneMapData.restrictSubfamily
      planeMap selected
  have hunion :
      (restrictPaperShading selected shading).union ⊆ shading.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨selected.embedding index, hpoint⟩
  refine ⟨targetMap, ?_⟩
  intro first second
  exact hlipschitz
    ⟨first, hunion first.prop⟩ ⟨second, hunion second.prop⟩

/-- A quantitative weak-plane-map refinement.  Keeping the coefficient in
the interface prevents a later Lip-1 wrapper from erasing the `1/100` bound
needed by the coarse Property-(P) chart. -/
structure QuantitativeWeakLipschitzPlaneMapRefinement
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (incidence : ℝ)
    (coefficient : NNReal)
    (leftFactor rightFactor : ENNReal) where
  shading : WZ1PaperTubeShading family
  subshading : PaperIsSubshading shading source
  cubical : WZ1PaperIsCubicalShading shading
  planeMap : PaperWZ1WeakPlaneMapData shading incidence
  /-- The selected map remains constant on each fine grid cell.  Retaining
  this certificate is what lets the same map seed a later finite-scale
  Lemma-4.12 iteration. -/
  planeMap_cellwise : ∀ first second,
    wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second
  lipschitz : LipschitzWith coefficient
    (fun point : {point : Point3 // point ∈ shading.union} =>
      planeMap.planeMap point)
  mass_retention :
    leftFactor * source.mass ≤ rightFactor * shading.mass

/-- A quantitative Lip-1 weak-plane-map refinement. -/
structure WeakLipschitzPlaneMapRefinement
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (incidence : ℝ)
    (leftFactor rightFactor : ENNReal) where
  shading : WZ1PaperTubeShading family
  subshading : PaperIsSubshading shading source
  cubical : WZ1PaperIsCubicalShading shading
  planeMap : PaperWZ1WeakPlaneMapData shading incidence
  lipschitz : LipschitzWith 1
    (fun point : {point : Point3 // point ∈ shading.union} =>
      planeMap.planeMap point)
  mass_retention :
    leftFactor * source.mass ≤ rightFactor * shading.mass

/-- Reindex a quantitative weak-map refinement along a tube subfamily.  The
caller supplies the exact reindexed mass inequality; it is not inherited from
the ambient refinement automatically. -/
noncomputable def QuantitativeWeakLipschitzPlaneMapRefinement.restrictSubfamily
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {coefficient : NNReal}
    {leftFactor rightFactor : ENNReal}
    (data : QuantitativeWeakLipschitzPlaneMapRefinement
      source incidence coefficient leftFactor rightFactor)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (hmass : leftFactor * (restrictPaperShading selected source).mass ≤
      rightFactor * (restrictPaperShading selected data.shading).mass) :
    QuantitativeWeakLipschitzPlaneMapRefinement
      (restrictPaperShading selected source) incidence coefficient
      leftFactor rightFactor where
  shading := restrictPaperShading selected data.shading
  subshading := fun index point hpoint => data.subshading _ hpoint
  cubical := restrictPaperShading_cubical selected data.cubical
  planeMap :=
    Kakeya.Assouad.PureWZ2.PaperWZ1WeakPlaneMapData.restrictSubfamily
      data.planeMap selected
  planeMap_cellwise := data.planeMap_cellwise
  lipschitz := by
    have hunion : (restrictPaperShading selected data.shading).union ⊆
        data.shading.union := by
      rintro point ⟨index, hpoint⟩
      exact ⟨selected.embedding index, hpoint⟩
    intro first second
    exact data.lipschitz
      ⟨first, hunion first.prop⟩ ⟨second, hunion second.prop⟩
  mass_retention := hmass

/-- A refinement of a zero-extended source has no support outside the
selected tube subfamily.  Restricting it back therefore preserves its mass
exactly and supplies the quantitative reindexing inequality automatically. -/
noncomputable def
    QuantitativeWeakLipschitzPlaneMapRefinement.restrictZeroExtension
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {source : WZ1PaperTubeShading selected.family}
    {coefficient : NNReal}
    {leftFactor rightFactor : ENNReal}
    (data : QuantitativeWeakLipschitzPlaneMapRefinement
      (extendShading selected source) incidence coefficient
      leftFactor rightFactor) :
    QuantitativeWeakLipschitzPlaneMapRefinement
      source incidence coefficient leftFactor rightFactor := by
  let restrictedSource :=
    restrictPaperShading selected (extendShading selected source)
  have hsourceCarrier : ∀ index, restrictedSource.carrier index =
      source.carrier index := fun index => extendShading_carrier_mem
  have hsourceMass : restrictedSource.mass = source.mass := by
    rw [restrictPaperShading_mass]
    change (∑ index : Fin selected.family.card,
      MeasureTheory.volume
        ((extendShading selected source).carrier
          (selected.embedding index))) = source.mass
    simp_rw [extendShading_carrier_mem]
    rfl
  let restricted := data.restrictSubfamily selected (by
    rw [hsourceMass]
    have hdataMass := data.mass_retention
    rw [extendShading_mass selected source] at hdataMass
    have hcandidateMass :
        (restrictPaperShading selected data.shading).mass =
          data.shading.mass := by
      rw [restrictPaperShading_mass]
      change (∑ index : Fin selected.family.card,
          MeasureTheory.volume
            (data.shading.carrier (selected.embedding index))) =
        data.shading.mass
      let candidateSupport : Fin family.card → ENNReal := fun ambientIndex =>
        MeasureTheory.volume (data.shading.carrier ambientIndex)
      have hzero : ∀ ambientIndex,
          (¬ ∃ index, selected.embedding index = ambientIndex) →
          candidateSupport ambientIndex = 0 := by
        intro ambientIndex himage
        have hsub := data.subshading ambientIndex
        have hempty : (extendShading selected source).carrier ambientIndex = ∅ :=
          extendShading_carrier_empty himage
        have hcarrier : data.shading.carrier ambientIndex = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro point hpoint
          have := hsub hpoint
          rwa [hempty] at this
        simp [candidateSupport, hcarrier]
      rw [show data.shading.mass =
          ∑ index : Fin family.card, candidateSupport index by rfl]
      let image : Finset (Fin family.card) :=
        Finset.image selected.embedding Finset.univ
      have hsumImage : (∑ index : Fin family.card, candidateSupport index) =
          ∑ ambientIndex ∈ image, candidateSupport ambientIndex := by
        rw [← Finset.sum_subset (Finset.subset_univ image)]
        intro ambientIndex _ hnotImage
        apply hzero ambientIndex
        intro himage
        rcases himage with ⟨index, hindex⟩
        apply hnotImage
        exact Finset.mem_image.mpr ⟨index, Finset.mem_univ _, hindex⟩
      rw [hsumImage]
      have himageSum :
          (∑ ambientIndex ∈ image, candidateSupport ambientIndex) =
            ∑ index : Fin selected.family.card,
              candidateSupport (selected.embedding index) := by
        exact Finset.sum_image
          (s := (Finset.univ : Finset (Fin selected.family.card)))
          (g := selected.embedding) (f := candidateSupport)
          selected.embedding.injective.injOn
      rw [himageSum]
    rw [hcandidateMass]
    exact hdataMass)
  exact {
    shading := restricted.shading
    subshading := fun index point hpoint => by
      rw [← hsourceCarrier index]
      exact restricted.subshading index hpoint
    cubical := restricted.cubical
    planeMap := restricted.planeMap
    planeMap_cellwise := restricted.planeMap_cellwise
    lipschitz := restricted.lipschitz
    mass_retention := by
      have hmass := restricted.mass_retention
      change leftFactor * restrictedSource.mass ≤
        rightFactor * restricted.shading.mass at hmass
      rw [hsourceMass] at hmass
      exact hmass
  }

/-- Restricting a refinement of a zero-extension back to the genuine tube
subfamily preserves the retained shading mass exactly. -/
lemma QuantitativeWeakLipschitzPlaneMapRefinement.restrictZeroExtension_mass
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {source : WZ1PaperTubeShading selected.family}
    {coefficient : NNReal}
    {leftFactor rightFactor : ENNReal}
    (data : QuantitativeWeakLipschitzPlaneMapRefinement
      (extendShading selected source) incidence coefficient
      leftFactor rightFactor) :
    (data.restrictZeroExtension selected).shading.mass = data.shading.mass := by
  change (restrictPaperShading selected data.shading).mass = data.shading.mass
  rw [restrictPaperShading_mass]
  let candidateSupport : Fin family.card → ENNReal := fun ambientIndex =>
    MeasureTheory.volume (data.shading.carrier ambientIndex)
  have hzero : ∀ ambientIndex,
      (¬ ∃ index, selected.embedding index = ambientIndex) →
      candidateSupport ambientIndex = 0 := by
    intro ambientIndex himage
    have hsub := data.subshading ambientIndex
    have hempty : (extendShading selected source).carrier ambientIndex = ∅ :=
      extendShading_carrier_empty himage
    have hcarrier : data.shading.carrier ambientIndex = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro point hpoint
      have := hsub hpoint
      rwa [hempty] at this
    simp [candidateSupport, hcarrier]
  rw [show data.shading.mass =
      ∑ index : Fin family.card, candidateSupport index by rfl]
  let image : Finset (Fin family.card) :=
    Finset.image selected.embedding Finset.univ
  have hsumImage : (∑ index : Fin family.card, candidateSupport index) =
      ∑ ambientIndex ∈ image, candidateSupport ambientIndex := by
    rw [← Finset.sum_subset (Finset.subset_univ image)]
    intro ambientIndex _ hnotImage
    apply hzero ambientIndex
    intro himage
    rcases himage with ⟨index, hindex⟩
    apply hnotImage
    exact Finset.mem_image.mpr ⟨index, Finset.mem_univ _, hindex⟩
  rw [hsumImage]
  symm
  exact Finset.sum_image
    (s := (Finset.univ : Finset (Fin selected.family.card)))
    (g := selected.embedding) (f := candidateSupport)
    selected.embedding.injective.injOn

/-- Forget a quantitative constant which is at most one. -/
def QuantitativeWeakLipschitzPlaneMapRefinement.toWeak
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {coefficient : NNReal}
    {leftFactor rightFactor : ENNReal}
    (data : QuantitativeWeakLipschitzPlaneMapRefinement
      source incidence coefficient leftFactor rightFactor)
    (hcoefficient : coefficient ≤ 1) :
    WeakLipschitzPlaneMapRefinement
      source incidence leftFactor rightFactor where
  shading := data.shading
  subshading := data.subshading
  cubical := data.cubical
  planeMap := data.planeMap
  lipschitz := data.lipschitz.weaken hcoefficient
  mass_retention := data.mass_retention

end Kakeya.Assouad.PureWZ2

end
