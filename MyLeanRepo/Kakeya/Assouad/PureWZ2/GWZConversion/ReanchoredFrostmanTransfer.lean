import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AxialReanchoringEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FrostmanTransfer
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume

/-!
# Frostman transfer through bounded axial reanchoring

Transfer one original complete-fiber Frostman certificate to a selected
reanchored strict fiber.

The proof uses:

* explicit inclusion of selected source indices in the original complete
  fiber;
* an ambient-to-selected cardinality ratio;
* the common convex envelope for bounded axial reanchoring;
* an explicit comparison between the reanchored parent volume and the
  original fixed-dilation parent volume.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Mass of a finite subfamily of equal-radius tubes. -/
private theorem pureWZ2_tubeSubfamily_mass_eq_card_mul
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (selected : Finset (Fin family.card)) :
    (Kakeya.Streamlined.TubeSubfamily.fromFinset
        family selected).family.toBodyFamily.mass =
      (selected.card : ENNReal) * Kakeya.deltaTubeVolume delta := by
  let sub :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset family selected
  have hvolume :
      ∀ index : Fin sub.family.card,
        (sub.family.toBodyFamily.body index).volume =
          Kakeya.deltaTubeVolume delta := by
    intro index
    let canonical : Kakeya.DeltaTube delta :=
      {
        base := 0
        direction := EuclideanSpace.single (0 : Fin 3) 1
        direction_unit := by simp
      }
    change (sub.family.tube index).volume =
      Kakeya.deltaTubeVolume delta
    exact
      Kakeya.Streamlined.tube_volume_eq
        (sub.family.tube index) canonical
  change
    (∑ index : Fin selected.card,
      (sub.family.toBodyFamily.body index).volume) =
      (selected.card : ENNReal) * Kakeya.deltaTubeVolume delta
  simp only [hvolume]
  rw [Finset.sum_const]
  simp

/--
Transfer an original complete-fiber Frostman certificate to a selected
reanchored strict fiber.
-/
theorem pureWZ2_reanchored_strict_fiber_frostman
    {delta rho A : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hA : 1 ≤ A)
    {source reanchored : Kakeya.Streamlined.TubeFamily delta}
    (sourceIndex : Fin reanchored.card ↪ Fin source.card)
    (axialShift : Fin reanchored.card → ℝ)
    (direction_eq :
      ∀ index,
        (reanchored.tube index).direction =
          (source.tube (sourceIndex index)).direction)
    (source_base_eq :
      ∀ index,
        (source.tube (sourceIndex index)).base =
          (reanchored.tube index).base +
            axialShift index •
              (reanchored.tube index).direction)
    (axialShift_bound :
      ∀ index, |axialShift index| ≤ 1)
    (originalParent : Kakeya.DeltaTube rho)
    (reanchoredParent : Kakeya.DeltaTube (8 * A * rho))
    (selected : Finset (Fin reanchored.card))
    (selected_nonempty : selected.Nonempty)
    (completeFiber : Finset (Fin source.card))
    (selected_mem_complete :
      ∀ index ∈ selected,
        sourceIndex index ∈ completeFiber)
    (complete_mem_carrier :
      ∀ index ∈ completeFiber,
        (source.tube index).carrier ⊆
          wz2PaperCenteredDilatedCarrier A originalParent)
    (C cardinalityRatio volumeRatio : ENNReal)
    (ambient_cardinality_ratio :
      (completeFiber.card : ENNReal) ≤
        cardinalityRatio * (selected.card : ENNReal))
    (complete_frostman :
      ∀ convexSet : Set Point3,
        Convex ℝ convexSet →
        convexSet ⊆
            wz2PaperCenteredDilatedCarrier A originalParent →
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
              source completeFiber).family.toBodyFamily.containedMass
                convexSet *
              volume
                (wz2PaperCenteredDilatedCarrier A originalParent) ≤
            C *
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                source completeFiber).family.toBodyFamily.mass *
              volume convexSet)
    (parent_volume_ratio :
      volume reanchoredParent.carrier ≤
        volumeRatio *
          volume
            (wz2PaperCenteredDilatedCarrier A originalParent)) :
    ∀ convexSet : Set Point3,
      Convex ℝ convexSet →
      convexSet ⊆ reanchoredParent.carrier →
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
            reanchored selected).family.toBodyFamily.containedMass
              convexSet *
            volume reanchoredParent.carrier ≤
          (212776173 * C * cardinalityRatio * volumeRatio) *
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              reanchored selected).family.toBodyFamily.mass *
            volume convexSet := by
  let selectedSub :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset reanchored selected
  let completeSub :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset source completeFiber
  have hdeltaVolumePos :
      0 < Kakeya.deltaTubeVolume delta := by
    have hlower :
        ENNReal.ofReal (2 * delta ^ 2) ≤
          Kakeya.deltaTubeVolume delta :=
      Kakeya.Streamlined.tube_volume_ge_two_delta_sq
        delta hdelta
    exact
      (show 0 < ENNReal.ofReal (2 * delta ^ 2) by
        apply ENNReal.ofReal_pos.mpr
        positivity).trans_le hlower
  have hdeltaVolumeTop :
      Kakeya.deltaTubeVolume delta ≠ ⊤ := by
    let canonical : Kakeya.DeltaTube delta :=
      {
        base := 0
        direction := EuclideanSpace.single (0 : Fin 3) 1
        direction_unit := by simp
      }
    have hvolume :
        Kakeya.deltaTubeVolume delta =
          volume canonical.carrier := by
      exact
        (Kakeya.Streamlined.tube_volume_eq
          canonical canonical).symm
    rw [hvolume]
    exact
      wz2_paper_ordinary_tube_volume_ne_top
        canonical hdelta
  intro convexSet hconvex hconvexParent
  let selectedContained : Finset (Fin reanchored.card) :=
    selected.filter fun index =>
      (reanchored.tube index).carrier ⊆ convexSet
  by_cases hcontainedEmpty : selectedContained = ∅
  · have hselectedContainedMass :
        selectedSub.family.toBodyFamily.containedMass convexSet = 0 := by
      change
        (∑ index : Fin selected.card
          with (selectedSub.family.tube index).carrier ⊆ convexSet,
          (selectedSub.family.toBodyFamily.body index).volume) = 0
      rw [Finset.sum_eq_zero]
      intro index hindex
      have hambient :
          selected.orderEmbOfFin rfl index ∈ selectedContained := by
        rw [Finset.mem_filter]
        exact
          ⟨Finset.orderEmbOfFin_mem selected rfl index,
            by
              simpa only [selectedSub,
                Kakeya.Streamlined.TubeSubfamily.fromFinset] using
                (Finset.mem_filter.mp hindex).2⟩
      rw [hcontainedEmpty] at hambient
      exact (Finset.notMem_empty _ hambient).elim
    rw [hselectedContainedMass, zero_mul]
    positivity
  · have hcontainedNonempty :
        selectedContained.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hcontainedEmpty
    rcases
        pureWZ2_bounded_axial_reanchoring_common_envelope
          hdelta sourceIndex axialShift direction_eq
          source_base_eq axialShift_bound
          selectedContained hcontainedNonempty
          convexSet hconvex
          (by
            intro index hindex
            exact (Finset.mem_filter.mp hindex).2) with
      ⟨envelope, henvelopeConvex, henvelopeVolume,
        hsourceEnvelope⟩
    let clippedEnvelope :=
      envelope ∩
        wz2PaperCenteredDilatedCarrier A originalParent
    have hclippedConvex :
        Convex ℝ clippedEnvelope := by
      exact henvelopeConvex.inter
        (Convex.affine_image
          (AffineMap.homothety
            (wz2PaperTubeMidpoint originalParent) A)
          (wz2_paper_ordinary_tube_carrier_convex
            originalParent))
    have hclippedSubset :
        clippedEnvelope ⊆
          wz2PaperCenteredDilatedCarrier A originalParent :=
      Set.inter_subset_right
    have hselectedToComplete :
        selectedSub.family.toBodyFamily.containedMass convexSet ≤
          completeSub.family.toBodyFamily.containedMass
            clippedEnvelope := by
      let selectedIndices :
          Finset (Fin selectedSub.family.card) :=
        Finset.univ.filter fun index =>
          (selectedSub.family.tube index).carrier ⊆ convexSet
      let completeIndices :
          Finset (Fin completeSub.family.card) :=
        Finset.univ.filter fun index =>
          (completeSub.family.tube index).carrier ⊆
            clippedEnvelope
      let selectedAmbient :
          Fin selectedSub.family.card → Fin reanchored.card :=
        selectedSub.embedding
      have hselectedAmbientMem :
          ∀ index ∈ selectedIndices,
            selectedAmbient index ∈ selectedContained := by
        intro index hindex
        rw [Finset.mem_filter]
        constructor
        · exact Finset.orderEmbOfFin_mem selected rfl index
        · have hcontained :=
            (Finset.mem_filter.mp hindex).2
          rw [selectedSub.tube_eq] at hcontained
          exact hcontained
      have hcompleteRange :
          ∀ index ∈ selectedIndices,
            ∃ target : Fin completeSub.family.card,
              completeSub.embedding target =
                sourceIndex (selectedAmbient index) := by
        intro index hindex
        have hmember :
            sourceIndex (selectedAmbient index) ∈
              completeFiber :=
          selected_mem_complete
            (selectedAmbient index)
            (Finset.mem_filter.mp
              (hselectedAmbientMem index hindex)).1
        let equivalence :=
          completeFiber.orderIsoOfFin rfl
        exact
          ⟨equivalence.symm
              ⟨sourceIndex (selectedAmbient index), hmember⟩,
            congrArg Subtype.val
              (equivalence.apply_symm_apply
                ⟨sourceIndex (selectedAmbient index), hmember⟩)⟩
      let target :
          ∀ index : Fin selectedSub.family.card,
            index ∈ selectedIndices →
              Fin completeSub.family.card :=
        fun index hindex =>
          Classical.choose (hcompleteRange index hindex)
      have htargetSpec :
          ∀ index hindex,
            completeSub.embedding (target index hindex) =
              sourceIndex (selectedAmbient index) := by
        intro index hindex
        exact
          Classical.choose_spec
            (hcompleteRange index hindex)
      let embedding :
          {index // index ∈ selectedIndices} ↪
            Fin completeSub.family.card := by
        refine
          ⟨fun index => target index.1 index.2, ?_⟩
        intro first second heq
        have hambient :
            completeSub.embedding
                (target first.1 first.2) =
              completeSub.embedding
                (target second.1 second.2) :=
          congrArg completeSub.embedding heq
        have hsource :
            sourceIndex (selectedAmbient first.1) =
              sourceIndex (selectedAmbient second.1) :=
          (htargetSpec first.1 first.2).symm.trans
            (hambient.trans
              (htargetSpec second.1 second.2))
        apply Subtype.ext
        exact selectedSub.embedding.injective
          (sourceIndex.injective hsource)
      have htargetContained :
          ∀ index : {index // index ∈ selectedIndices},
            embedding index ∈ completeIndices := by
        intro index
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_univ _
        · have hsourceCarrier :
              (source.tube
                (sourceIndex
                  (selectedAmbient index.1))).carrier ⊆
                envelope :=
            hsourceEnvelope
              (selectedAmbient index.1)
              (hselectedAmbientMem index.1 index.2)
          have hsourceComplete :
              (source.tube
                (sourceIndex
                  (selectedAmbient index.1))).carrier ⊆
                wz2PaperCenteredDilatedCarrier A originalParent := by
            have hmember :
                sourceIndex (selectedAmbient index.1) ∈
                  completeFiber :=
              selected_mem_complete
                (selectedAmbient index.1)
                (Finset.mem_filter.mp
                  (hselectedAmbientMem index.1 index.2)).1
            exact complete_mem_carrier
              (sourceIndex (selectedAmbient index.1)) hmember
          have htube :
              completeSub.family.tube (embedding index) =
                source.tube
                  (sourceIndex
                    (selectedAmbient index.1)) := by
            rw [completeSub.tube_eq]
            change
              source.tube
                  (completeSub.embedding
                    (target index.1 index.2)) =
                source.tube
                  (sourceIndex
                    (selectedAmbient index.1))
            rw [htargetSpec index.1 index.2]
          rw [htube]
          exact Set.subset_inter hsourceCarrier hsourceComplete
      have hcard :
          selectedIndices.card ≤ completeIndices.card := by
        have himage :
            Finset.image embedding Finset.univ ⊆
              completeIndices := by
          intro targetIndex htargetIndex
          rcases Finset.mem_image.mp htargetIndex with
            ⟨index, _, rfl⟩
          exact htargetContained index
        calc
          selectedIndices.card =
              (Finset.univ :
                Finset {index // index ∈ selectedIndices}).card := by
            simp
          _ =
              (Finset.image embedding
                (Finset.univ :
                  Finset {index // index ∈ selectedIndices})).card := by
            rw [Finset.card_image_of_injective
              _ embedding.injective]
          _ ≤ completeIndices.card :=
            Finset.card_le_card himage
      have hmassSelected :
          selectedSub.family.toBodyFamily.containedMass convexSet =
            (selectedIndices.card : ENNReal) *
              Kakeya.deltaTubeVolume delta := by
        change
          (∑ index ∈ selectedIndices,
            (selectedSub.family.toBodyFamily.body index).volume) =
              _
        have hvol :
            ∀ index : Fin selectedSub.family.card,
              (selectedSub.family.toBodyFamily.body index).volume =
                Kakeya.deltaTubeVolume delta := by
          intro index
          let canonical : Kakeya.DeltaTube delta :=
            {
              base := 0
              direction := EuclideanSpace.single (0 : Fin 3) 1
              direction_unit := by simp
            }
          change (selectedSub.family.tube index).volume =
            Kakeya.deltaTubeVolume delta
          exact
            Kakeya.Streamlined.tube_volume_eq
              (selectedSub.family.tube index) canonical
        simp only [hvol]
        rw [Finset.sum_const]
        simp
      have hmassComplete :
          completeSub.family.toBodyFamily.containedMass
              clippedEnvelope =
            (completeIndices.card : ENNReal) *
              Kakeya.deltaTubeVolume delta := by
        change
          (∑ index ∈ completeIndices,
            (completeSub.family.toBodyFamily.body index).volume) =
              _
        have hvol :
            ∀ index : Fin completeSub.family.card,
              (completeSub.family.toBodyFamily.body index).volume =
                Kakeya.deltaTubeVolume delta := by
          intro index
          let canonical : Kakeya.DeltaTube delta :=
            {
              base := 0
              direction := EuclideanSpace.single (0 : Fin 3) 1
              direction_unit := by simp
            }
          change (completeSub.family.tube index).volume =
            Kakeya.deltaTubeVolume delta
          exact
            Kakeya.Streamlined.tube_volume_eq
              (completeSub.family.tube index) canonical
        simp only [hvol]
        rw [Finset.sum_const]
        simp
      rw [hmassSelected, hmassComplete]
      exact mul_le_mul_right'
        (by exact_mod_cast hcard)
        (Kakeya.deltaTubeVolume delta)
    have hfrost :=
      complete_frostman
        clippedEnvelope hclippedConvex hclippedSubset
    have hselectedMass :
        selectedSub.family.toBodyFamily.mass =
          (selected.card : ENNReal) *
            Kakeya.deltaTubeVolume delta :=
      pureWZ2_tubeSubfamily_mass_eq_card_mul
        reanchored selected
    have hcompleteMass :
        completeSub.family.toBodyFamily.mass =
          (completeFiber.card : ENNReal) *
            Kakeya.deltaTubeVolume delta :=
      pureWZ2_tubeSubfamily_mass_eq_card_mul
        source completeFiber
    have hmassRatio :
        completeSub.family.toBodyFamily.mass ≤
          cardinalityRatio *
            selectedSub.family.toBodyFamily.mass := by
      rw [hselectedMass, hcompleteMass]
      calc
        (completeFiber.card : ENNReal) *
              Kakeya.deltaTubeVolume delta
            ≤
          (cardinalityRatio * (selected.card : ENNReal)) *
              Kakeya.deltaTubeVolume delta := by
          exact mul_le_mul_right'
            ambient_cardinality_ratio
            (Kakeya.deltaTubeVolume delta)
        _ =
          cardinalityRatio *
            ((selected.card : ENNReal) *
              Kakeya.deltaTubeVolume delta) := by
          ring
    calc
      selectedSub.family.toBodyFamily.containedMass convexSet *
            volume reanchoredParent.carrier
          ≤
        completeSub.family.toBodyFamily.containedMass
              clippedEnvelope *
            (volumeRatio *
              volume
                (wz2PaperCenteredDilatedCarrier A
                  originalParent)) := by
        gcongr
      _ =
        volumeRatio *
          (completeSub.family.toBodyFamily.containedMass
              clippedEnvelope *
            volume
              (wz2PaperCenteredDilatedCarrier A
                originalParent)) := by
        ring
      _ ≤
        volumeRatio *
          (C * completeSub.family.toBodyFamily.mass *
            volume clippedEnvelope) := by
        gcongr
      _ ≤
        volumeRatio *
          (C *
            (cardinalityRatio *
              selectedSub.family.toBodyFamily.mass) *
            volume clippedEnvelope) := by
        exact mul_le_mul_left'
          (mul_le_mul_right'
            (mul_le_mul_left' hmassRatio C)
            (volume clippedEnvelope))
          volumeRatio
      _ ≤
        volumeRatio *
          (C *
            (cardinalityRatio *
              selectedSub.family.toBodyFamily.mass) *
            ((212776173 : ENNReal) * volume convexSet)) := by
        exact mul_le_mul_left'
          (mul_le_mul_left'
            ((measure_mono Set.inter_subset_left).trans
              henvelopeVolume)
            (C *
              (cardinalityRatio *
                selectedSub.family.toBodyFamily.mass)))
          volumeRatio
      _ =
        (212776173 * C * cardinalityRatio * volumeRatio) *
          selectedSub.family.toBodyFamily.mass *
          volume convexSet := by
        ring

end Kakeya.Assouad

end
