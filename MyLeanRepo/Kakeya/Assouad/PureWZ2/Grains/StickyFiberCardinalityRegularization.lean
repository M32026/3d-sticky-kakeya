import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CoarseTopLevelCWABridge
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantOwnerExactificationHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.DyadicBand
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.WeightBinning

/-!
# Complete-parent fiber-cardinality regularization for the frozen pure sticky ABI

The frozen `PureWZ2PropStickyData` exposes the Section 6 line-cover ABI, not
the stronger literal `WZ2PaperPartitioningCover`.  This file therefore first
proves complete-parent restriction directly for `PureWZ2Section6Cover`.  No
literal-carrier or doubled-fiber certificate is inserted as an extra input.

The final selection dyadically regularizes the cardinalities of the complete
parent fibers, weighted by their full shaded masses.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Restriction of a frozen Section 6 line cover to a nonempty set of coarse
parents, retaining every fine tube in each selected complete fiber. -/
structure PureWZ2Section6CompleteParentRestrictionData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (selectedParents : Finset (Fin coarse.card)) where
  selectedParents_nonempty : selectedParents.Nonempty
  selectedCoarse :
    Kakeya.Streamlined.TubeSubfamily coarse
  selectedCoarse_eq :
    selectedCoarse =
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        coarse selectedParents
  selectedCoarseEquiv :
    Fin selectedCoarse.family.card ≃ selectedParents
  selectedCoarseEquiv_val :
    ∀ parent,
      (selectedCoarseEquiv parent).1 =
        selectedCoarse.embedding parent
  selectedFineIndices : Finset (Fin fine.card)
  selectedFineIndices_eq :
    selectedFineIndices =
      Finset.univ.filter fun source =>
        cover.toPaperTubeCover.parent source ∈ selectedParents
  selectedFine :
    Kakeya.Streamlined.TubeSubfamily fine
  selectedFine_eq :
    selectedFine =
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        fine selectedFineIndices
  selectedFineEquiv :
    Fin selectedFine.family.card ≃ selectedFineIndices
  selectedFineEquiv_val :
    ∀ source,
      (selectedFineEquiv source).1 =
        selectedFine.embedding source
  selectedFineShading :
    WZ1PaperTubeShading selectedFine.family
  selectedFineShading_eq :
    selectedFineShading =
      restrictPaperShading selectedFine shading
  selectedFine_cubical :
    WZ1PaperIsCubicalShading selectedFineShading
  restrictedCover :
    PureWZ2Section6Cover
      selectedFine.family selectedCoarse.family
  restricted_parent_spec :
    ∀ index,
      selectedCoarse.embedding
          (restrictedCover.toPaperTubeCover.parent index) =
        cover.toPaperTubeCover.parent
          (selectedFine.embedding index)
  full_fiber_complete :
    ∀ parent : Fin selectedCoarse.family.card,
      Finset.image selectedFine.embedding
          (wz2PaperFullFiberIndices
            selectedFine.family selectedCoarse.family parent) =
        wz2PaperFullFiberIndices fine coarse
          (selectedCoarse.embedding parent)

theorem pure_wz2_section6_complete_parent_restriction
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (shadingCubical : WZ1PaperIsCubicalShading shading)
    (selectedParents : Finset (Fin coarse.card))
    (selectedParentsNonempty : selectedParents.Nonempty) :
    Nonempty
      (PureWZ2Section6CompleteParentRestrictionData
        cover shading selectedParents) := by
  let lineCover := cover.toPaperTubeCover
  let selectedCoarse :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      coarse selectedParents
  let selectedCoarseEquiv :
      Fin selectedCoarse.family.card ≃ selectedParents :=
    (selectedParents.orderIsoOfFin rfl).toEquiv
  let selectedFineIndices : Finset (Fin fine.card) :=
    Finset.univ.filter fun source =>
      lineCover.parent source ∈ selectedParents
  let selectedFine :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      fine selectedFineIndices
  let selectedFineShading :=
    restrictPaperShading selectedFine shading
  have hSelectedFineMem :
      ∀ index : Fin selectedFine.family.card,
        selectedFine.embedding index ∈ selectedFineIndices :=
    fun index =>
      Finset.orderEmbOfFin_mem selectedFineIndices rfl index
  have hAmbientParentMem :
      ∀ index : Fin selectedFine.family.card,
        lineCover.parent (selectedFine.embedding index) ∈
          selectedParents := by
    intro index
    exact (Finset.mem_filter.mp (hSelectedFineMem index)).2
  let restrictedParent :
      Fin selectedFine.family.card →
        Fin selectedCoarse.family.card := fun index =>
    selectedCoarseEquiv.symm
      ⟨lineCover.parent (selectedFine.embedding index),
        hAmbientParentMem index⟩
  have hRestrictedParentAmbient :
      ∀ index,
        selectedCoarse.embedding (restrictedParent index) =
          lineCover.parent (selectedFine.embedding index) := by
    intro index
    change
      (selectedParents.orderEmbOfFin rfl)
          (selectedCoarseEquiv.symm
            ⟨lineCover.parent (selectedFine.embedding index),
              hAmbientParentMem index⟩) =
        lineCover.parent (selectedFine.embedding index)
    exact congrArg Subtype.val
      (selectedCoarseEquiv.apply_symm_apply
        ⟨lineCover.parent (selectedFine.embedding index),
          hAmbientParentMem index⟩)
  have hSelectedFineSurjective :
      ∀ source ∈ selectedFineIndices,
        ∃ index : Fin selectedFine.family.card,
          selectedFine.embedding index = source := by
    intro source hsource
    let member : selectedFineIndices := ⟨source, hsource⟩
    let index : Fin selectedFine.family.card :=
      (selectedFineIndices.orderIsoOfFin rfl).symm member
    exact
      ⟨index, congrArg Subtype.val
        (selectedFineIndices.orderIsoOfFin rfl
          |>.apply_symm_apply member)⟩
  have hRestrictedParentSurjective :
      Function.Surjective restrictedParent := by
    intro parent
    let ambientParent := selectedCoarse.embedding parent
    rcases lineCover.parent_surjective ambientParent with
      ⟨ambientSource, hsourceParent⟩
    have hparentMem : ambientParent ∈ selectedParents := by
      change
        (selectedParents.orderEmbOfFin rfl parent :
          Fin coarse.card) ∈ selectedParents
      exact Finset.orderEmbOfFin_mem selectedParents rfl parent
    have hsourceSelected : ambientSource ∈ selectedFineIndices := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hsourceParent.symm ▸ hparentMem⟩
    rcases hSelectedFineSurjective ambientSource hsourceSelected with
      ⟨index, hindex⟩
    refine ⟨index, ?_⟩
    apply selectedCoarse.embedding.injective
    rw [hRestrictedParentAmbient, hindex, hsourceParent]
  let restrictedCover :
      PureWZ2Section6Cover
        selectedFine.family selectedCoarse.family :=
    { fine_line_class := cover.fine_line_class.subfamily selectedFine
      coarse_line_class :=
        cover.coarse_line_class.subfamily selectedCoarse
      covers := by
        intro index
        refine ⟨restrictedParent index, ?_⟩
        rw [selectedFine.tube_eq, selectedCoarse.tube_eq,
          hRestrictedParentAmbient]
        exact lineCover.parent_covers (selectedFine.embedding index)
      parent_hit := by
        intro parent
        rcases hRestrictedParentSurjective parent with ⟨index, hindex⟩
        refine ⟨index, ?_⟩
        rw [selectedFine.tube_eq, selectedCoarse.tube_eq, ← hindex,
          hRestrictedParentAmbient]
        exact lineCover.parent_covers (selectedFine.embedding index)
      coarse_essentially_distinct :=
        cover.coarse_essentially_distinct.subfamily selectedCoarse }
  have hParent :
      ∀ index,
        selectedCoarse.embedding
            (restrictedCover.toPaperTubeCover.parent index) =
          lineCover.parent (selectedFine.embedding index) := by
    intro index
    apply lineCover.parent_unique
      (selectedFine.embedding index)
    rw [← selectedFine.tube_eq index,
      ← selectedCoarse.tube_eq
        (restrictedCover.toPaperTubeCover.parent index)]
    exact restrictedCover.toPaperTubeCover.parent_covers index
  have hComplete :
      ∀ parent : Fin selectedCoarse.family.card,
        Finset.image selectedFine.embedding
            (wz2PaperFullFiberIndices
              selectedFine.family selectedCoarse.family parent) =
          wz2PaperFullFiberIndices fine coarse
            (selectedCoarse.embedding parent) := by
    intro parent
    ext source
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨index, hindex, rfl⟩
      have hparent :
          restrictedCover.toPaperTubeCover.parent index = parent :=
        (restrictedCover.toPaperTubeCover.parent_unique
          index parent
          ((mem_wz2PaperFullFiberIndices_iff parent index).mp
            hindex)).symm
      rw [cover.fullFiberIndices_eq]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hParent index, hparent]
    · intro hsource
      have hsourceParent :
          lineCover.parent source =
            selectedCoarse.embedding parent := by
        have hsource' :
            source ∈ lineCover.fiberIndices
              (selectedCoarse.embedding parent) := by
          rwa [← cover.fullFiberIndices_eq]
        exact (Finset.mem_filter.mp hsource').2
      have hsourceSelected : source ∈ selectedFineIndices := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hsourceParent]
        change
          (selectedParents.orderEmbOfFin rfl parent :
            Fin coarse.card) ∈ selectedParents
        exact Finset.orderEmbOfFin_mem selectedParents rfl parent
      rcases hSelectedFineSurjective source hsourceSelected with
        ⟨index, hindex⟩
      have hrestrictedParent :
          restrictedCover.toPaperTubeCover.parent index = parent := by
        apply selectedCoarse.embedding.injective
        rw [hParent index, hindex, hsourceParent]
      refine ⟨index, ?_, hindex⟩
      rw [restrictedCover.fullFiberIndices_eq]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hrestrictedParent⟩
  exact
    ⟨{
      selectedParents_nonempty := selectedParentsNonempty
      selectedCoarse := selectedCoarse
      selectedCoarse_eq := rfl
      selectedCoarseEquiv := selectedCoarseEquiv
      selectedCoarseEquiv_val := fun _ => rfl
      selectedFineIndices := selectedFineIndices
      selectedFineIndices_eq := rfl
      selectedFine := selectedFine
      selectedFine_eq := rfl
      selectedFineEquiv :=
        (selectedFineIndices.orderIsoOfFin rfl).toEquiv
      selectedFineEquiv_val := fun _ => rfl
      selectedFineShading := selectedFineShading
      selectedFineShading_eq := rfl
      selectedFine_cubical :=
        restrictPaperShading_cubical selectedFine shadingCubical
      restrictedCover := restrictedCover
      restricted_parent_spec := hParent
      full_fiber_complete := hComplete
    }⟩

/-- Complete-parent restriction preserves the cardinality of every retained
full fiber. -/
theorem PureWZ2Section6CompleteParentRestrictionData.full_fiber_card_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {selectedParents : Finset (Fin coarse.card)}
    (data : PureWZ2Section6CompleteParentRestrictionData
      cover shading selectedParents)
    (parent : Fin data.selectedCoarse.family.card) :
    (data.restrictedCover.toPaperTubeCover.fiberIndices parent).card =
      (cover.toPaperTubeCover.fiberIndices
        (data.selectedCoarse.embedding parent)).card := by
  rw [← data.restrictedCover.fullFiberIndices_eq,
    ← cover.fullFiberIndices_eq]
  have himage := congrArg Finset.card (data.full_fiber_complete parent)
  rw [Finset.card_image_of_injective _ data.selectedFine.embedding.injective]
    at himage
  exact himage

/-- Complete-parent restriction preserves the point multiplicity of every
retained full fiber. -/
theorem PureWZ2Section6CompleteParentRestrictionData.full_fiber_pointMultiplicity_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {selectedParents : Finset (Fin coarse.card)}
    (data : PureWZ2Section6CompleteParentRestrictionData
      cover shading selectedParents)
    (parent : Fin data.selectedCoarse.family.card)
    (point : Point3) :
    data.restrictedCover.toPaperTubeCover.fiberPointMultiplicity
        data.selectedFineShading parent point =
      cover.toPaperTubeCover.fiberPointMultiplicity shading
        (data.selectedCoarse.embedding parent) point := by
  let localFiber := wz2PaperFullFiberIndices
    data.selectedFine.family data.selectedCoarse.family parent
  let ambientFiber := wz2PaperFullFiberIndices
    fine coarse (data.selectedCoarse.embedding parent)
  have himage :
      Finset.image data.selectedFine.embedding
          (localFiber.filter fun source =>
            point ∈ data.selectedFineShading.carrier source) =
        ambientFiber.filter fun source => point ∈ shading.carrier source := by
    ext ambientSource
    constructor
    · intro hsource
      rcases Finset.mem_image.mp hsource with
        ⟨localSource, hlocal, rfl⟩
      have hlocalData := Finset.mem_filter.mp hlocal
      apply Finset.mem_filter.mpr
      constructor
      · have hmemImage : data.selectedFine.embedding localSource ∈
            Finset.image data.selectedFine.embedding
              (wz2PaperFullFiberIndices
                data.selectedFine.family data.selectedCoarse.family parent) :=
          Finset.mem_image.mpr ⟨localSource, hlocalData.1, rfl⟩
        rw [data.full_fiber_complete parent] at hmemImage
        simpa [ambientFiber] using hmemImage
      · rw [data.selectedFineShading_eq] at hlocalData
        exact hlocalData.2
    · intro hsource
      have hambient := Finset.mem_filter.mp hsource
      have hmemImage : ambientSource ∈
          Finset.image data.selectedFine.embedding
            (wz2PaperFullFiberIndices
              data.selectedFine.family data.selectedCoarse.family parent) := by
        rw [data.full_fiber_complete parent]
        simpa [ambientFiber] using hambient.1
      rcases Finset.mem_image.mp hmemImage with
        ⟨localSource, hlocalFiber, hlocalAmbient⟩
      apply Finset.mem_image.mpr
      refine ⟨localSource, ?_, hlocalAmbient⟩
      apply Finset.mem_filter.mpr
      constructor
      · exact hlocalFiber
      · rw [data.selectedFineShading_eq]
        change point ∈ shading.carrier
          (data.selectedFine.embedding localSource)
        rw [hlocalAmbient]
        exact hambient.2
  change
    ((data.restrictedCover.toPaperTubeCover.fiberIndices parent).filter
      fun source => point ∈ data.selectedFineShading.carrier source).card =
    ((cover.toPaperTubeCover.fiberIndices
      (data.selectedCoarse.embedding parent)).filter
      fun source => point ∈ shading.carrier source).card
  rw [← data.restrictedCover.fullFiberIndices_eq,
    ← cover.fullFiberIndices_eq]
  have himageCard := congrArg Finset.card himage
  rw [Finset.card_image_of_injective _
    data.selectedFine.embedding.injective] at himageCard
  exact himageCard

/-- The selected fine shading remains point-compatible with the restricted
coarse shading on the selected parent family. -/
theorem PureWZ2Section6CompleteParentRestrictionData.point_compatibility
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {selectedParents : Finset (Fin coarse.card)}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (data : PureWZ2Section6CompleteParentRestrictionData
      cover fineShading selectedParents) :
    ∀ source point,
      point ∈ data.selectedFineShading.carrier source →
        point ∈
          (restrictPaperShading data.selectedCoarse coarseShading).carrier
            (data.restrictedCover.toPaperTubeCover.parent source) := by
  intro source point hpoint
  rw [data.selectedFineShading_eq] at hpoint
  change point ∈ coarseShading.carrier
    (data.selectedCoarse.embedding
      (data.restrictedCover.toPaperTubeCover.parent source))
  rw [data.restricted_parent_spec]
  exact balanced.point_compatibility
    (data.selectedFine.embedding source)
    (cover.toPaperTubeCover.parent
      (data.selectedFine.embedding source))
    (cover.toPaperTubeCover.parent_covers
      (data.selectedFine.embedding source)) point hpoint

theorem PureWZ2Section6CompleteParentRestrictionData.selectedCoarse_embedding_mem
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {selectedParents : Finset (Fin coarse.card)}
    (data : PureWZ2Section6CompleteParentRestrictionData
      cover shading selectedParents)
    (parent : Fin data.selectedCoarse.family.card) :
    data.selectedCoarse.embedding parent ∈ selectedParents := by
  rw [← data.selectedCoarseEquiv_val parent]
  exact (data.selectedCoarseEquiv parent).2

/-- The mass of the complete-parent restriction is the sum of the ambient
full-fiber shaded masses over the selected parents. -/
theorem PureWZ2Section6CompleteParentRestrictionData.selected_mass_eq_finset
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {selectedParents : Finset (Fin coarse.card)}
    (data : PureWZ2Section6CompleteParentRestrictionData
      cover shading selectedParents) :
    data.selectedFineShading.mass =
      ∑ parent ∈ selectedParents,
        cover.toPaperTubeCover.fiberShadedMass shading parent := by
  rw [data.selectedFineShading_eq, restrictPaperShading_mass]
  calc
    (∑ index : Fin data.selectedFine.family.card,
        volume
          (shading.carrier (data.selectedFine.embedding index))) =
        ∑ source : data.selectedFineIndices,
          volume (shading.carrier source.1) := by
      exact Fintype.sum_equiv data.selectedFineEquiv
        (fun index : Fin data.selectedFine.family.card =>
          volume
            (shading.carrier (data.selectedFine.embedding index)))
        (fun source : data.selectedFineIndices =>
          volume (shading.carrier source.1))
        (fun index => by rw [data.selectedFineEquiv_val index])
    _ = ∑ source ∈ data.selectedFineIndices,
          volume (shading.carrier source) :=
      Finset.sum_coe_sort data.selectedFineIndices
        (fun source => volume (shading.carrier source))
    _ = ∑ parent ∈ selectedParents,
          ∑ source ∈
              cover.toPaperTubeCover.fiberIndices parent,
            volume (shading.carrier source) := by
      rw [data.selectedFineIndices_eq]
      symm
      let selected : Finset (Fin fine.card) :=
        Finset.univ.filter fun source =>
          cover.toPaperTubeCover.parent source ∈ selectedParents
      have hpartition :=
        Finset.sum_fiberwise_of_maps_to
          (s := Finset.univ.filter fun source : Fin fine.card =>
            cover.toPaperTubeCover.parent source ∈ selectedParents)
          (t := selectedParents)
          (g := cover.toPaperTubeCover.parent)
          (f := fun source => volume (shading.carrier source))
          (fun source hsource =>
            (Finset.mem_filter.mp hsource).2)
      calc
        (∑ parent ∈ selectedParents,
            ∑ source ∈
                cover.toPaperTubeCover.fiberIndices parent,
              volume (shading.carrier source)) =
            ∑ parent ∈ selectedParents,
              ∑ source ∈ selected with
                  cover.toPaperTubeCover.parent source = parent,
                volume (shading.carrier source) := by
          apply Finset.sum_congr rfl
          intro parent hparent
          apply Finset.sum_congr
          · ext source
            simp only [selected, WZ1PaperTubeCover.fiberIndices,
              Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro h
              exact ⟨h ▸ hparent, h⟩
            · exact fun h => h.2
          · intro source _
            rfl
        _ = ∑ source ∈ selected,
              volume (shading.carrier source) := by
          simpa [selected] using hpartition
    _ = _ := rfl

/-- The full fibers of a frozen Section 6 line cover partition the fine
shaded mass. -/
theorem PureWZ2Section6Cover.sum_fiberShadedMass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (shading : WZ1PaperTubeShading fine) :
    (∑ parent : Fin coarse.card,
        cover.toPaperTubeCover.fiberShadedMass shading parent) =
      shading.mass := by
  change
    (∑ parent : Fin coarse.card,
        ∑ source ∈ cover.toPaperTubeCover.fiberIndices parent,
          volume (shading.carrier source)) =
      ∑ source : Fin fine.card, volume (shading.carrier source)
  simpa [WZ1PaperTubeCover.fiberIndices] using
    (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Fin fine.card)))
      (t := (Finset.univ : Finset (Fin coarse.card)))
      (g := cover.toPaperTubeCover.parent)
      (f := fun source => volume (shading.carrier source))
      (fun _ _ => Finset.mem_univ _))

/-- A complete-parent restriction of one frozen sticky output whose complete
fibers lie in one factor-two cardinality band. -/
structure PureWZ2StickyFiberCardinalityRegularizationData
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent) where
  bandLower : ℝ
  bandLower_pos : 0 < bandLower
  selectedParents : Finset (Fin sticky.coarse.card)
  restriction :
    PureWZ2Section6CompleteParentRestrictionData
      sticky.cover sticky.refined selectedParents
  retained_mass :
    sticky.refined.mass ≤
      restriction.selectedFineShading.mass *
        ENNReal.ofReal
          (Real.logb 2
              ((sticky.selected.family.card : ℝ) / 1) + 1)
  fiber_cardinality_band :
    ∀ parent : Fin restriction.selectedCoarse.family.card,
      ENNReal.ofReal bandLower ≤
          ((restriction.restrictedCover.toPaperTubeCover
            |>.fiberIndices parent).card : ENNReal) ∧
        ((restriction.restrictedCover.toPaperTubeCover
          |>.fiberIndices parent).card : ENNReal) ≤
          ENNReal.ofReal (2 * bandLower)
  fiber_uniform :
    ∀ first second : Fin restriction.selectedCoarse.family.card,
      ((restriction.restrictedCover.toPaperTubeCover
        |>.fiberIndices first).card : ENNReal) ≤
        2 *
          ((restriction.restrictedCover.toPaperTubeCover
            |>.fiberIndices second).card : ENNReal)

private theorem pure_wz2_sticky_fiber_cardinality_bounds
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent) :
    let value : Fin sticky.coarse.card → ENNReal := fun parent =>
      (sticky.cover.toPaperTubeCover.fiberIndices parent).card
    (∀ parent, ENNReal.ofReal 1 ≤ value parent) ∧
      (∀ parent,
        value parent ≤
          ENNReal.ofReal (sticky.selected.family.card : ℝ)) := by
  dsimp only
  constructor
  · intro parent
    rcases sticky.cover.toPaperTubeCover.parent_surjective parent with
      ⟨sourceIndex, hsource⟩
    have hmem :
        sourceIndex ∈
          sticky.cover.toPaperTubeCover.fiberIndices parent := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsource⟩
    have hcard :
        1 ≤
          (sticky.cover.toPaperTubeCover.fiberIndices parent).card :=
      Finset.one_le_card.mpr ⟨sourceIndex, hmem⟩
    simpa using (show
      (1 : ENNReal) ≤
        ((sticky.cover.toPaperTubeCover.fiberIndices parent).card :
          ENNReal) by exact_mod_cast hcard)
  · intro parent
    have hsubset :
        sticky.cover.toPaperTubeCover.fiberIndices parent ⊆
          (Finset.univ : Finset (Fin sticky.selected.family.card)) :=
      Finset.subset_univ _
    have hcard := Finset.card_le_card hsubset
    have hcard' :
        (sticky.cover.toPaperTubeCover.fiberIndices parent).card ≤
          sticky.selected.family.card := by
      simpa using hcard
    simpa using (show
      ((sticky.cover.toPaperTubeCover.fiberIndices parent).card :
          ENNReal) ≤
        (sticky.selected.family.card : ENNReal) by
      exact_mod_cast hcard')

private theorem pure_wz2_sticky_coarse_nonempty
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent) :
    (Finset.univ : Finset (Fin sticky.coarse.card)).Nonempty := by
  rcases sticky.selected_nonempty with hselected
  let sourceIndex : Fin sticky.selected.family.card :=
    ⟨0, hselected⟩
  exact ⟨sticky.cover.toPaperTubeCover.parent sourceIndex,
    Finset.mem_univ _⟩

private theorem pure_wz2_sticky_cardinality_regularization_of_band
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (M : ℝ)
    (selectedParents : Finset (Fin sticky.coarse.card))
    (hM : 1 ≤ M)
    (hSelected : selectedParents.Nonempty)
    (hBand :
      ∀ parent ∈ selectedParents,
        ENNReal.ofReal M ≤
            ((sticky.cover.toPaperTubeCover
              |>.fiberIndices parent).card : ENNReal) ∧
          ((sticky.cover.toPaperTubeCover
            |>.fiberIndices parent).card : ENNReal) ≤
            ENNReal.ofReal (2 * M))
    (hRetained :
      sticky.refined.mass ≤
        (∑ parent ∈ selectedParents,
          sticky.cover.toPaperTubeCover.fiberShadedMass
            sticky.refined parent) *
          ENNReal.ofReal
            (Real.logb 2
                ((sticky.selected.family.card : ℝ) / 1) + 1)) :
    Nonempty
      (PureWZ2StickyFiberCardinalityRegularizationData sticky) := by
  rcases pure_wz2_section6_complete_parent_restriction
      sticky.cover sticky.refined sticky.refined_cubical
      selectedParents hSelected with
    ⟨restriction⟩
  have hRestrictedBand :
      ∀ parent : Fin restriction.selectedCoarse.family.card,
        ENNReal.ofReal M ≤
            ((restriction.restrictedCover.toPaperTubeCover
              |>.fiberIndices parent).card : ENNReal) ∧
          ((restriction.restrictedCover.toPaperTubeCover
            |>.fiberIndices parent).card : ENNReal) ≤
            ENNReal.ofReal (2 * M) := by
    intro parent
    rw [restriction.full_fiber_card_eq parent]
    exact hBand (restriction.selectedCoarse.embedding parent)
      (restriction.selectedCoarse_embedding_mem parent)
  have hUniform :
      ∀ first second : Fin restriction.selectedCoarse.family.card,
        ((restriction.restrictedCover.toPaperTubeCover
          |>.fiberIndices first).card : ENNReal) ≤
          2 *
            ((restriction.restrictedCover.toPaperTubeCover
              |>.fiberIndices second).card : ENNReal) := by
    intro first second
    calc
      ((restriction.restrictedCover.toPaperTubeCover
        |>.fiberIndices first).card : ENNReal) ≤
          ENNReal.ofReal (2 * M) := (hRestrictedBand first).2
      _ = 2 * ENNReal.ofReal M := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ ≤ 2 *
          ((restriction.restrictedCover.toPaperTubeCover
            |>.fiberIndices second).card : ENNReal) := by
        gcongr
        exact (hRestrictedBand second).1
  exact
    ⟨{
      bandLower := M
      bandLower_pos := lt_of_lt_of_le (by norm_num) hM
      selectedParents := selectedParents
      restriction := restriction
      retained_mass := by
        rw [restriction.selected_mass_eq_finset]
        exact hRetained
      fiber_cardinality_band := hRestrictedBand
      fiber_uniform := hUniform
    }⟩

/-- Weighted factor-two regularization of the complete fibers in any frozen
sticky output.  The positive-mass branch uses the full-fiber shaded masses as
weights.  If the total refined mass is zero, a unit-weight band is used only
to preserve a nonempty genuine family; the displayed mass retention is then
automatic. -/
theorem pure_wz2_sticky_fiber_cardinality_regularization
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent) :
    Nonempty
      (PureWZ2StickyFiberCardinalityRegularizationData sticky) := by
  let parents : Finset (Fin sticky.coarse.card) := Finset.univ
  let value : Fin sticky.coarse.card → ENNReal := fun parent =>
    (sticky.cover.toPaperTubeCover.fiberIndices parent).card
  let weight : Fin sticky.coarse.card → ENNReal := fun parent =>
    sticky.cover.toPaperTubeCover.fiberShadedMass
      sticky.refined parent
  have hFineCard :
      (1 : ℝ) ≤ sticky.selected.family.card := by
    exact_mod_cast sticky.selected_nonempty
  have hBounds :=
    pure_wz2_sticky_fiber_cardinality_bounds sticky
  have hLower :
      ∀ parent ∈ parents, ENNReal.ofReal 1 ≤ value parent := by
    intro parent _
    exact hBounds.1 parent
  have hUpper :
      ∀ parent ∈ parents,
        value parent ≤
          ENNReal.ofReal (sticky.selected.family.card : ℝ) := by
    intro parent _
    exact hBounds.2 parent
  have hWeightSum :
      (∑ parent ∈ parents, weight parent) = sticky.refined.mass := by
    simpa [parents, weight] using
      sticky.cover.sum_fiberShadedMass sticky.refined
  rcases mass_weighted_dyadic_band
      parents value weight
      1 (sticky.selected.family.card : ℝ)
      (by norm_num) hFineCard hLower hUpper with
    ⟨M, selectedParents, hM, hSubset, hBand, hRetained⟩
  by_cases hSelected : selectedParents.Nonempty
  · apply pure_wz2_sticky_cardinality_regularization_of_band
      sticky M selectedParents hM hSelected hBand
    rw [← hWeightSum]
    exact hRetained
  · have hSelectedEmpty : selectedParents = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hSelected
    have hMassZero : sticky.refined.mass = 0 := by
      rw [← hWeightSum]
      have hzero :
          (∑ parent ∈ parents, weight parent) ≤ 0 := by
        calc
          (∑ parent ∈ parents, weight parent) ≤
              (∑ parent ∈ selectedParents, weight parent) *
                ENNReal.ofReal
                  (Real.logb 2
                      ((sticky.selected.family.card : ℝ) / 1) + 1) :=
            hRetained
          _ = 0 := by rw [hSelectedEmpty]; simp
      exact bot_unique hzero
    rcases mass_weighted_dyadic_band
        parents value (fun _ => (1 : ENNReal))
        1 (sticky.selected.family.card : ℝ)
        (by norm_num) hFineCard hLower hUpper with
      ⟨M', selectedParents', hM', hSubset', hBand', hUnitRetained⟩
    have hSelected' : selectedParents'.Nonempty := by
      by_contra hempty
      have hEmpty : selectedParents' = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hempty
      have hParents : parents.Nonempty :=
        pure_wz2_sticky_coarse_nonempty sticky
      have hPositive :
          0 < ∑ _parent ∈ parents, (1 : ENNReal) := by
        rw [Finset.sum_const]
        simp only [nsmul_eq_mul, mul_one]
        exact_mod_cast hParents.card_pos
      have hzero :
          (∑ _parent ∈ parents, (1 : ENNReal)) ≤ 0 := by
        calc
          (∑ _parent ∈ parents, (1 : ENNReal)) ≤
              (∑ _parent ∈ selectedParents', (1 : ENNReal)) *
                ENNReal.ofReal
                  (Real.logb 2
                      ((sticky.selected.family.card : ℝ) / 1) + 1) :=
            hUnitRetained
          _ = 0 := by rw [hEmpty]; simp
      exact (not_le.mpr hPositive) hzero
    apply pure_wz2_sticky_cardinality_regularization_of_band
      sticky M' selectedParents' hM' hSelected' hBand'
    rw [hMassZero]
    exact bot_le

/-- The complete-parent restricted shading is a genuine subshading of the
ambient source shading after composing its two tube-subfamily embeddings. -/
theorem PureWZ2StickyFiberCardinalityRegularizationData.restricted_mass_le_source_restrict
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent}
    (data : PureWZ2StickyFiberCardinalityRegularizationData sticky) :
    data.restriction.selectedFineShading.mass ≤
      (restrictPaperShading
        (sticky.selected.comp data.restriction.selectedFine)
        sourceShading).mass := by
  rw [data.restriction.selectedFineShading_eq,
    restrictPaperShading_mass, restrictPaperShading_mass]
  apply Finset.sum_le_sum
  intro index _
  apply measure_mono
  exact sticky.subshading
    (data.restriction.selectedFine.embedding index)

/-- Source CWA transfers to the complete-parent cardinality-regularized fine
family.  The exact cost is one source-density inverse, the original sticky
refinement inverse, the new logarithmic band factor, and the fixed carrier
geometry constant. -/
theorem PureWZ2StickyFiberCardinalityRegularizationData.restricted_fine_top_level_cwa
    {delta sigma sourceLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent}
    (data : PureWZ2StickyFiberCardinalityRegularizationData sticky)
    (sourceExtremal :
      WZ2PaperCroppedIsExtremal
        sigma sourceLoss source sourceShading)
    (sourceLine : WZ1PaperIsLineClass source)
    (hdeltaSmall : delta ≤ 1 / 24)
    (C : ENNReal)
    (sourceCWA : WZ2PaperConvexWolffBound source C) :
    WZ2PaperConvexWolffBound
      data.restriction.selectedFine.family
      (((Kakeya.realRpowENN delta sourceLoss)⁻¹ *
          ((wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
            ENNReal.ofReal
              (Real.logb 2
                ((sticky.selected.family.card : ℝ) / 1) + 1) *
            (55296 * Kakeya.deltaTubeVolume 1))) * C) := by
  let density : ENNReal :=
    Kakeya.realRpowENN delta sourceLoss
  let fraction : ENNReal :=
    wz2PaperPureRefinementFraction delta logExponent
  let bandLoss : ENNReal :=
    ENNReal.ofReal
      (Real.logb 2
        ((sticky.selected.family.card : ℝ) / 1) + 1)
  let geometryConstant : ENNReal :=
    55296 * Kakeya.deltaTubeVolume 1
  let totalLoss : ENNReal := fraction⁻¹ * bandLoss
  let composed := sticky.selected.comp data.restriction.selectedFine
  have hdeltaStrict : delta < 1 := by
    linarith
  have hfractionZero : fraction ≠ 0 := by
    change wz1PaperRefinementFraction delta logExponent ≠ 0
    exact wz1PaperRefinementFraction_ne_zero
      sourceExtremal.delta_pos hdeltaStrict logExponent
  have hfractionTop : fraction ≠ ⊤ := by
    change wz1PaperRefinementFraction delta logExponent ≠ ⊤
    exact wz1PaperRefinementFraction_ne_top
      sourceExtremal.delta_pos hdeltaStrict logExponent
  have hdensityZero : density ≠ 0 := by
    simp [density, Kakeya.realRpowENN,
      Real.rpow_pos_of_pos sourceExtremal.delta_pos]
  have hdensityTop : density ≠ ⊤ := by
    simp [density, Kakeya.realRpowENN]
  have hbody :
      Kakeya.realRpowENN delta 2 * source.enncard ≤
        (wz1PaperBodyFamily source).mass :=
    PureWZ2.paperBodyFamily_mass_lower_rpow_two
      sourceExtremal.delta_pos
      (hdeltaSmall.trans (by norm_num)) sourceLine
  have hambientMass :
      density * source.enncard *
          Kakeya.realRpowENN delta 2 ≤
        sourceShading.mass := by
    calc
      density * source.enncard * Kakeya.realRpowENN delta 2 =
          density *
            (Kakeya.realRpowENN delta 2 * source.enncard) := by
        ring
      _ ≤ density * (wz1PaperBodyFamily source).mass := by
        gcongr
      _ ≤ sourceShading.mass := sourceExtremal.dense
  have hsourceToRefined :
      sourceShading.mass ≤ fraction⁻¹ * sticky.refined.mass := by
    calc
      sourceShading.mass =
          (fraction⁻¹ * fraction) * sourceShading.mass := by
        rw [ENNReal.inv_mul_cancel hfractionZero hfractionTop, one_mul]
      _ = fraction⁻¹ * (fraction * sourceShading.mass) := by
        rw [mul_assoc]
      _ ≤ fraction⁻¹ * sticky.refined.mass := by
        gcongr
        exact sticky.retained_mass
  have hretained :
      sourceShading.mass ≤
        totalLoss *
          (restrictPaperShading composed sourceShading).mass := by
    calc
      sourceShading.mass ≤ fraction⁻¹ * sticky.refined.mass :=
        hsourceToRefined
      _ ≤ fraction⁻¹ *
          (data.restriction.selectedFineShading.mass * bandLoss) := by
        gcongr
        exact data.retained_mass
      _ = totalLoss *
          data.restriction.selectedFineShading.mass := by
        dsimp only [totalLoss]
        ring
      _ ≤ totalLoss *
          (restrictPaperShading composed sourceShading).mass := by
        gcongr
        exact data.restricted_mass_le_source_restrict
  have hcardinality :
      density * source.enncard ≤
        (totalLoss * geometryConstant) *
          composed.family.enncard := by
    simpa [geometryConstant] using
      wz2PaperWeightedCardinality_retained_from_subfamily_mass
        sourceExtremal.delta_pos hdeltaSmall sourceLine
        sourceShading composed density totalLoss
        hambientMass hretained
  change WZ2PaperConvexWolffBound composed.family
    (((Kakeya.realRpowENN delta sourceLoss)⁻¹ *
        ((wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
          ENNReal.ofReal
            (Real.logb 2
              ((sticky.selected.family.card : ℝ) / 1) + 1) *
          (55296 * Kakeya.deltaTubeVolume 1))) * C)
  simpa [density, fraction, bandLoss, totalLoss, geometryConstant] using
    sourceCWA.subfamily_of_weighted_cardinality
      composed hdensityZero hdensityTop hcardinality

/-- Factor-two fiber regularity transfers the restricted-fine top-level CWA
to the corresponding nonempty restricted coarse family. -/
theorem PureWZ2StickyFiberCardinalityRegularizationData.restricted_coarse_top_level_cwa
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent}
    (data : PureWZ2StickyFiberCardinalityRegularizationData sticky)
    (hdelta : 0 < delta)
    (hscale : 6 * delta ≤ rho.1)
    (C : ENNReal)
    (fineCWA :
      WZ2PaperConvexWolffBound
        data.restriction.selectedFine.family C) :
    WZ2PaperConvexWolffBound
      data.restriction.selectedCoarse.family (2 * C) := by
  let cover := data.restriction.restrictedCover.toPaperTubeCover
  apply paperConvexWolffBound_of_uniform_cover
      cover.parent cover.parent_surjective
      (fun fineIndex => ?_) 2 C data.fiber_uniform fineCWA
  exact wz2PaperTubeCarrierCovers_of_strict_cover
    hdelta sticky.coarse_extremal.delta_pos hscale
    (data.restriction.restrictedCover.fine_line_class fineIndex)
    (data.restriction.restrictedCover.coarse_line_class
      (cover.parent fineIndex))
    (cover.parent_covers fineIndex)

/-- Simultaneous complete-fiber cardinality and shaded-mass regularization.
The mass band is selected inside the parents retained by the first weighted
cardinality band, so both conclusions refer to the original frozen sticky
fibers and may be consumed by `sticky.rescaledFiber` without changing its
parent type. -/
structure PureWZ2StickyFiberMassCardinalityRegularizationData
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent) where
  cardinality :
    PureWZ2StickyFiberCardinalityRegularizationData sticky
  massBins : ℕ
  massBins_eq :
    massBins =
      Nat.log 2 (2 * cardinality.selectedParents.card) + 1
  selectedParentMembers : Finset cardinality.selectedParents
  selectedParentMembers_nonempty : selectedParentMembers.Nonempty
  massLevel : ENNReal
  massLevel_pos : 0 < massLevel
  mass_band :
    ∀ parent ∈ selectedParentMembers,
      massLevel ≤
          sticky.cover.toPaperTubeCover.fiberShadedMass
            sticky.refined parent.1 ∧
        sticky.cover.toPaperTubeCover.fiberShadedMass
            sticky.refined parent.1 ≤
          2 * massLevel
  retained_mass :
    sticky.refined.mass ≤
      ENNReal.ofReal
          (Real.logb 2
            ((sticky.selected.family.card : ℝ) / 1) + 1) *
        (2 * (massBins : ENNReal)) *
          ∑ parent ∈ selectedParentMembers,
            sticky.cover.toPaperTubeCover.fiberShadedMass
              sticky.refined parent.1
  cardinality_band :
    ∀ parent ∈ selectedParentMembers,
      ENNReal.ofReal cardinality.bandLower ≤
          ((sticky.cover.toPaperTubeCover.fiberIndices parent.1).card :
            ENNReal) ∧
        ((sticky.cover.toPaperTubeCover.fiberIndices parent.1).card :
            ENNReal) ≤
          ENNReal.ofReal (2 * cardinality.bandLower)
  average_density_comparable :
    ∀ first ∈ selectedParentMembers,
      ∀ second ∈ selectedParentMembers,
        sticky.cover.toPaperTubeCover.fiberShadedMass
              sticky.refined first.1 *
            ((sticky.cover.toPaperTubeCover.fiberIndices second.1).card :
              ENNReal) ≤
          4 *
            (sticky.cover.toPaperTubeCover.fiberShadedMass
                sticky.refined second.1 *
              ((sticky.cover.toPaperTubeCover.fiberIndices first.1).card :
                ENNReal))

theorem pure_wz2_sticky_fiber_mass_cardinality_regularization
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (hrefinedMass : 0 < sticky.refined.mass) :
    Nonempty
      (PureWZ2StickyFiberMassCardinalityRegularizationData sticky) := by
  rcases pure_wz2_sticky_fiber_cardinality_regularization sticky with
    ⟨cardinality⟩
  let Parent := cardinality.selectedParents
  let weight : Parent → ENNReal := fun parent =>
    sticky.cover.toPaperTubeCover.fiberShadedMass
      sticky.refined parent.1
  have htotal :
      cardinality.restriction.selectedFineShading.mass =
        ∑ parent : Parent, weight parent := by
    rw [cardinality.restriction.selected_mass_eq_finset]
    exact (Finset.sum_coe_sort cardinality.selectedParents
      (fun parent =>
        sticky.cover.toPaperTubeCover.fiberShadedMass
          sticky.refined parent)).symm
  have htotalPos :
      0 < cardinality.restriction.selectedFineShading.mass := by
    have hband := cardinality.retained_mass
    by_contra hzero
    have hselectedZero :
        cardinality.restriction.selectedFineShading.mass = 0 := by
      simpa using hzero
    rw [hselectedZero, zero_mul] at hband
    exact (not_le.mpr hrefinedMass) hband
  have htotalTop :
      cardinality.restriction.selectedFineShading.mass ≠ ⊤ := by
    change
      (∑ index : Fin cardinality.restriction.selectedFine.family.card,
        volume
          (cardinality.restriction.selectedFineShading.carrier index)) ≠ ⊤
    apply ENNReal.sum_ne_top.2
    intro index _
    have hle :
        volume
            (cardinality.restriction.selectedFineShading.carrier index) ≤
          volume (Kakeya.Streamlined.axisBox 2 2 2) :=
      measure_mono <|
        (cardinality.restriction.selectedFineShading.subset_body index).trans
          Set.inter_subset_right
    exact ne_top_of_le_ne_top (by
      rw [Kakeya.Streamlined.volume_axisBox
        2 2 2 (by norm_num) (by norm_num) (by norm_num)]
      exact ENNReal.ofReal_ne_top) hle
  rcases ennreal_dyadic_bin weight
      cardinality.restriction.selectedFineShading.mass
      htotal htotalTop htotalPos with
    ⟨bins, selected, hbins, hselected, hretention, _hthreshold,
      massLevel, hmassLevel, hmassBand⟩
  have hcardBand :
      ∀ parent ∈ selected,
        ENNReal.ofReal cardinality.bandLower ≤
            ((sticky.cover.toPaperTubeCover.fiberIndices parent.1).card :
              ENNReal) ∧
          ((sticky.cover.toPaperTubeCover.fiberIndices parent.1).card :
              ENNReal) ≤
            ENNReal.ofReal (2 * cardinality.bandLower) := by
    intro parent _
    have hmem : parent.1 ∈ cardinality.selectedParents := parent.2
    have ambient := cardinality.fiber_cardinality_band
      (cardinality.restriction.selectedCoarseEquiv.symm parent)
    rw [cardinality.restriction.full_fiber_card_eq] at ambient
    have hembedding :
        cardinality.restriction.selectedCoarse.embedding
            (cardinality.restriction.selectedCoarseEquiv.symm parent) =
          parent.1 := by
      rw [← cardinality.restriction.selectedCoarseEquiv_val]
      exact congrArg Subtype.val
        (cardinality.restriction.selectedCoarseEquiv.apply_symm_apply parent)
    simpa [hembedding] using ambient
  have haverage :
      ∀ first ∈ selected, ∀ second ∈ selected,
        weight first *
            ((sticky.cover.toPaperTubeCover.fiberIndices second.1).card :
              ENNReal) ≤
          4 *
            (weight second *
              ((sticky.cover.toPaperTubeCover.fiberIndices first.1).card :
                ENNReal)) := by
    intro first hfirst second hsecond
    have hfirstMass := (hmassBand first hfirst).2
    have hsecondMass := (hmassBand second hsecond).1
    have hfirstCard := (hcardBand first hfirst).1
    have hsecondCard := (hcardBand second hsecond).2
    calc
      weight first *
          ((sticky.cover.toPaperTubeCover.fiberIndices second.1).card :
            ENNReal) ≤
          (2 * massLevel) *
            ENNReal.ofReal (2 * cardinality.bandLower) := by gcongr
      _ = 4 * (massLevel * ENNReal.ofReal cardinality.bandLower) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
        ring
      _ ≤ 4 *
          (weight second *
            ((sticky.cover.toPaperTubeCover.fiberIndices first.1).card :
              ENNReal)) := by gcongr
  have hretained :
      sticky.refined.mass ≤
        ENNReal.ofReal
            (Real.logb 2
              ((sticky.selected.family.card : ℝ) / 1) + 1) *
          (2 * (bins : ENNReal)) *
            ∑ parent ∈ selected, weight parent := by
    calc
      sticky.refined.mass ≤
          cardinality.restriction.selectedFineShading.mass *
            ENNReal.ofReal
              (Real.logb 2
                ((sticky.selected.family.card : ℝ) / 1) + 1) :=
        cardinality.retained_mass
      _ ≤
          ((∑ parent ∈ selected, weight parent) * (bins : ENNReal) * 2) *
            ENNReal.ofReal
              (Real.logb 2
                ((sticky.selected.family.card : ℝ) / 1) + 1) := by
        gcongr
        rw [htotal]
        have hhalf :
            (∑ parent : Parent, weight parent) / 2 ≤
              (∑ parent ∈ selected, weight parent) *
                (bins : ENNReal) := by
          rw [← htotal]
          exact hretention
        calc
          (∑ parent : Parent, weight parent) =
              (∑ parent : Parent, weight parent) / 2 +
                (∑ parent : Parent, weight parent) / 2 :=
            (ENNReal.add_halves _).symm
          _ ≤
              (∑ parent ∈ selected, weight parent) * (bins : ENNReal) +
                (∑ parent ∈ selected, weight parent) *
                  (bins : ENNReal) :=
            add_le_add hhalf hhalf
          _ = ((∑ parent ∈ selected, weight parent) *
                (bins : ENNReal)) * 2 := by ring
      _ = _ := by ring
  exact
    ⟨{
      cardinality := cardinality
      massBins := bins
      massBins_eq := by
        simpa [Parent] using hbins
      selectedParentMembers := selected
      selectedParentMembers_nonempty := hselected
      massLevel := massLevel
      massLevel_pos := hmassLevel
      mass_band := hmassBand
      retained_mass := hretained
      cardinality_band := hcardBand
      average_density_comparable := haverage
    }⟩

/-- Choose one genuine original parent from the simultaneous band.  Its
complete fiber carries at least the average selected mass, with the exact
number of selected parents left visible. -/
theorem PureWZ2StickyFiberMassCardinalityRegularizationData.exists_heavy_parent
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent}
    (data : PureWZ2StickyFiberMassCardinalityRegularizationData sticky) :
    ∃ parent : Fin sticky.coarse.card,
      parent ∈ data.cardinality.selectedParents ∧
      (data.selectedParentMembers.card : ENNReal) *
          sticky.cover.toPaperTubeCover.fiberShadedMass
            sticky.refined parent ≥
        ∑ member ∈ data.selectedParentMembers,
          sticky.cover.toPaperTubeCover.fiberShadedMass
            sticky.refined member.1 ∧
      ENNReal.ofReal data.cardinality.bandLower ≤
          ((sticky.cover.toPaperTubeCover.fiberIndices parent).card :
            ENNReal) ∧
      ((sticky.cover.toPaperTubeCover.fiberIndices parent).card :
          ENNReal) ≤
        ENNReal.ofReal (2 * data.cardinality.bandLower) := by
  let weight : data.cardinality.selectedParents → ENNReal := fun member =>
    sticky.cover.toPaperTubeCover.fiberShadedMass
      sticky.refined member.1
  obtain ⟨member, hmember, hmax⟩ :=
    Finset.exists_max_image data.selectedParentMembers weight
      data.selectedParentMembers_nonempty
  have hsum :
      (∑ other ∈ data.selectedParentMembers, weight other) ≤
        ∑ _other ∈ data.selectedParentMembers, weight member := by
    exact Finset.sum_le_sum fun other hother => hmax other hother
  have hsumConst :
      (∑ _other ∈ data.selectedParentMembers, weight member) =
        (data.selectedParentMembers.card : ENNReal) * weight member := by
    rw [Finset.sum_const]
    simp [nsmul_eq_mul]
  rw [hsumConst] at hsum
  exact
    ⟨member.1, member.2, hsum,
      (data.cardinality_band member hmember).1,
      (data.cardinality_band member hmember).2⟩

/-- Every parent selected by the simultaneous band still has the original
frozen rescaled-full-fiber output.  This is a provenance bridge only; it does
not replace the abstract certificate by the concrete midpoint-centered one. -/
theorem PureWZ2StickyFiberMassCardinalityRegularizationData.selected_rescaledFiber
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent}
    (data : PureWZ2StickyFiberMassCardinalityRegularizationData sticky)
    (member : data.cardinality.selectedParents)
    (_hmember : member ∈ data.selectedParentMembers) :
    Nonempty
      (WZ2PaperPureRescaledFullFiberOutput
        (sigma := sigma) (loss := outputLoss)
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            sticky.selected.family
            (wz2PaperFullFiberIndices
              sticky.selected.family sticky.coarse member.1))
          sticky.refined)
        (sticky.coarse.tube member.1)
        sticky.coarse_extremal.delta_pos) :=
  sticky.rescaledFiber member.1

end Kakeya.Assouad

end
