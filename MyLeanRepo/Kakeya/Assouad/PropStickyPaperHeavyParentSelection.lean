import MyLeanRepo.Kakeya.Assouad.PropStickyPaperHeavyParentSelectionStatements

/-!
# Select mass-comparable coarse parents

Apply dyadic binning to canonical full-fiber shaded masses and pull the
selected parent bin back to a genuine fine-tube subfamily.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

lemma selectedFineIndices_eq_biUnion
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (S : Finset (Fin coarse.card)) :
    (Finset.univ.filter fun source : Fin fine.card =>
      cover.parent source ∈ S) =
    Finset.biUnion S (fun parent => cover.fiberIndices parent) := by
  ext source
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion, WZ1PaperTubeCover.fiberIndices]
  constructor
  · intro h
    refine ⟨cover.parent source, h, ?_⟩
    simp
  · rintro ⟨parent, hparent, hsource⟩
    have h_eq : cover.parent source = parent := by
      simpa [Finset.mem_filter, Finset.mem_univ] using hsource
    rw [h_eq]
    exact hparent

lemma fibers_disjoint
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    {p1 p2 : Fin coarse.card} (hne : p1 ≠ p2) :
    Disjoint (cover.fiberIndices p1) (cover.fiberIndices p2) := by
  rw [Finset.disjoint_left]
  intro source h1 h2
  have hp1 : cover.parent source = p1 := by
    simpa [WZ1PaperTubeCover.fiberIndices, Finset.mem_filter] using h1
  have hp2 : cover.parent source = p2 := by
    simpa [WZ1PaperTubeCover.fiberIndices, Finset.mem_filter] using h2
  have h : p1 = p2 := by
    rw [← hp1, hp2]
  exact hne h

lemma sum_selectedFine_eq_sum_parents
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (S : Finset (Fin coarse.card)) :
    ∑ source ∈ (Finset.univ.filter fun source : Fin fine.card =>
      cover.parent source ∈ S), volume (shading.carrier source) =
    ∑ parent ∈ S,
      (restrictPaperShading (cover.fullFiberSubfamily parent) shading).mass := by
  have h_union : (Finset.univ.filter fun source : Fin fine.card =>
      cover.parent source ∈ S) =
      Finset.biUnion S (fun parent => cover.fiberIndices parent) :=
    selectedFineIndices_eq_biUnion cover S
  rw [h_union]
  have h_disj : ∀ p1 ∈ S, ∀ p2 ∈ S, p1 ≠ p2 →
      Disjoint (cover.fiberIndices p1) (cover.fiberIndices p2) := by
    intro p1 _ p2 _ hne
    exact fibers_disjoint cover hne
  rw [Finset.sum_biUnion h_disj]
  apply Finset.sum_congr rfl
  intro parent _
  have h_fiber_eq :
      cover.fiberIndices parent =
        wz2PaperFullFiberIndices fine coarse parent :=
    (cover.fullFiberIndices_eq parent).symm
  rw [h_fiber_eq]
  exact (cover.fullFiberShading_mass shading parent).symm

theorem heavy_selected_full_fiber_complete
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selectedParents : Finset (Fin coarse.card))
    (selectedFineIndices : Finset (Fin fine.card))
    (selectedFineIndices_eq :
      selectedFineIndices =
        Finset.univ.filter fun source =>
          cover.parent source ∈ selectedParents)
    (selected :
      Kakeya.Streamlined.TubeSubfamily fine)
    (selected_eq :
      selected =
        Kakeya.Streamlined.TubeSubfamily.fromFinset
          fine selectedFineIndices)
    (hit_eq :
      cover.hitParentIndices selected = selectedParents) :
    ∀ parent : Fin (cover.hitParentSubfamily selected).family.card,
      Finset.image selected.embedding
          (wz2PaperFullFiberIndices
            selected.family
            (cover.hitParentSubfamily selected).family
            parent) =
        wz2PaperFullFiberIndices fine coarse
          ((cover.hitParentSubfamily selected).embedding parent) := by
  subst selected
  let selected :
      Kakeya.Streamlined.TubeSubfamily fine :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      fine selectedFineIndices
  intro parent
  let ambientParent :=
    (cover.hitParentSubfamily selected).embedding parent
  let restrictedCover := cover.restrictToHitParents selected
  let restrictedFiberIndices :=
    wz2PaperFullFiberIndices selected.family
      (cover.hitParentSubfamily selected).family parent
  let originalFiberIndices :=
    wz2PaperFullFiberIndices fine coarse ambientParent
  have ambient_mem : ambientParent ∈ selectedParents := by
    have h :
        ambientParent ∈ cover.hitParentIndices selected :=
      Finset.orderEmbOfFin_mem
        (cover.hitParentIndices selected) rfl parent
    rwa [hit_eq] at h
  have restricted_fiber :
      restrictedFiberIndices =
        Finset.univ.filter fun index : Fin selected.family.card =>
          cover.parent (selected.embedding index) = ambientParent := by
    ext index
    have h :
        index ∈ restrictedFiberIndices ↔
          restrictedCover.parent index = parent :=
      restrictedCover.mem_fullFiber_iff_parent parent index
    rw [h]
    have ambient_eq :
        (cover.hitParentSubfamily selected).embedding
            (cover.hitParent selected index) =
          cover.parent (selected.embedding index) :=
      cover.hitParent_ambient selected index
    constructor
    · intro parent_eq
      change cover.hitParent
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            fine selectedFineIndices) index = parent at parent_eq
      have source_parent :
          cover.parent
              ((Kakeya.Streamlined.TubeSubfamily.fromFinset
                fine selectedFineIndices).embedding index) =
            ambientParent := by
        calc
          cover.parent
              ((Kakeya.Streamlined.TubeSubfamily.fromFinset
                fine selectedFineIndices).embedding index) =
              (cover.hitParentSubfamily
                (Kakeya.Streamlined.TubeSubfamily.fromFinset
                  fine selectedFineIndices)).embedding
                (cover.hitParent
                  (Kakeya.Streamlined.TubeSubfamily.fromFinset
                    fine selectedFineIndices) index) :=
            (cover.hitParent_ambient
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                fine selectedFineIndices) index).symm
          _ = ambientParent := by rw [parent_eq]
      simpa [Finset.mem_filter, Finset.mem_univ] using source_parent
    · intro source_mem
      have source_parent :
          cover.parent
              ((Kakeya.Streamlined.TubeSubfamily.fromFinset
                fine selectedFineIndices).embedding index) =
            ambientParent := by
        simpa [Finset.mem_filter, Finset.mem_univ] using source_mem
      change cover.hitParent
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            fine selectedFineIndices) index = parent
      apply
        (cover.hitParentSubfamily
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            fine selectedFineIndices)).embedding.injective
      rw [cover.hitParent_ambient, source_parent]
  apply Finset.ext
  intro source
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨index, index_mem, rfl⟩
    have index_mem' : index ∈ restrictedFiberIndices := by
      simpa [restrictedFiberIndices] using index_mem
    rw [restricted_fiber] at index_mem'
    have parent_eq :
        cover.parent (selected.embedding index) = ambientParent :=
      (Finset.mem_filter.mp index_mem').2
    exact
      (cover.mem_fullFiber_iff_parent
        ambientParent (selected.embedding index)).mpr parent_eq
  · intro source_mem
    have parent_eq :
        cover.parent source = ambientParent :=
      (cover.mem_fullFiber_iff_parent ambientParent source).mp
        source_mem
    have source_selected : source ∈ selectedFineIndices := by
      rw [selectedFineIndices_eq]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [parent_eq]
      exact ambient_mem
    let sourceSubtype : selectedFineIndices :=
      ⟨source, source_selected⟩
    let index : Fin selected.family.card :=
      (selectedFineIndices.orderIsoOfFin rfl).symm sourceSubtype
    have embedding_eq : selected.embedding index = source := by
      subst selected
      exact congrArg Subtype.val
        ((selectedFineIndices.orderIsoOfFin rfl).apply_symm_apply
          sourceSubtype)
    have index_mem : index ∈ restrictedFiberIndices := by
      rw [restricted_fiber]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [embedding_eq, parent_eq]
    exact ⟨index, index_mem, embedding_eq⟩

theorem wz2_paper_heavy_parent_selection :
    WZ2PaperHeavyParentSelectionStatement := by
  intro delta rho fine hfine coarse cover shading hmass_pos hmass_ne_top
  let w : Fin coarse.card → ENNReal := fun parent =>
    (restrictPaperShading (cover.fullFiberSubfamily parent) shading).mass
  have hsum : ∑ parent : Fin coarse.card, w parent = shading.mass :=
    cover.sum_fullFiberShading_mass shading
  rcases ennreal_dyadic_bin w shading.mass hsum.symm hmass_ne_top hmass_pos with
    ⟨bins, selectedParents, hbins_eq, hselected_nonempty, hmass_retention,
      _hthreshold, ⟨c, hc_pos, hband⟩⟩
  let selectedFineIndices : Finset (Fin fine.card) :=
    Finset.univ.filter fun source => cover.parent source ∈ selectedParents
  let selected : Kakeya.Streamlined.TubeSubfamily fine :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset fine selectedFineIndices
  let selectedShading : WZ1PaperTubeShading selected.family :=
    restrictPaperShading selected shading

  have h_emb_mem : ∀ (idx : Fin selected.family.card),
      selected.embedding idx ∈ selectedFineIndices := by
    intro idx
    exact Finset.orderEmbOfFin_mem selectedFineIndices rfl idx

  have h_selected_mass : selectedShading.mass =
      ∑ parent ∈ selectedParents, w parent := by
    rw [restrictPaperShading_mass]
    have h1 : ∑ index : Fin selected.family.card,
          volume (shading.carrier (selected.embedding index)) =
        ∑ source ∈ selectedFineIndices, volume (shading.carrier source) := by
      let e : Fin selected.family.card ≃ selectedFineIndices :=
        (selectedFineIndices.orderIsoOfFin rfl).toEquiv
      calc
        ∑ index : Fin selected.family.card,
            volume (shading.carrier (selected.embedding index))
          = ∑ source : selectedFineIndices,
              volume (shading.carrier (source : Fin fine.card)) := by
            exact Fintype.sum_equiv e
              (fun index => volume (shading.carrier (selected.embedding index)))
              (fun source => volume (shading.carrier (source : Fin fine.card)))
              (fun _ => rfl)
        _ = ∑ source ∈ selectedFineIndices, volume (shading.carrier source) := by
            exact Finset.sum_coe_sort selectedFineIndices
              (fun source => volume (shading.carrier source))
    rw [h1]
    exact sum_selectedFine_eq_sum_parents cover shading selectedParents

  have h_retained :
      shading.mass ≤ 2 * (bins : ENNReal) * selectedShading.mass := by
    have h1 : shading.mass / 2 ≤ selectedShading.mass * (bins : ENNReal) := by
      rw [h_selected_mass]
      exact hmass_retention
    have h2 : shading.mass / 2 + shading.mass / 2 ≤
        selectedShading.mass * (bins : ENNReal) +
          selectedShading.mass * (bins : ENNReal) := by
      exact add_le_add h1 h1
    have h3 : shading.mass / 2 + shading.mass / 2 = shading.mass :=
      ENNReal.add_halves shading.mass
    have h4 :
        selectedShading.mass * (bins : ENNReal) +
            selectedShading.mass * (bins : ENNReal) =
          2 * (selectedShading.mass * (bins : ENNReal)) := by
      ring
    rw [h3, h4] at h2
    have h5 : 2 * (selectedShading.mass * (bins : ENNReal)) =
        2 * (bins : ENNReal) * selectedShading.mass := by
      ring
    rw [h5] at h2
    exact h2

  have h_hit_eq :
      cover.hitParentIndices selected = selectedParents := by
    ext p
    simp only [WZ2PaperPartitioningCover.hitParentIndices, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨idx, _, rfl⟩
      have h : selected.embedding idx ∈ selectedFineIndices := h_emb_mem idx
      have h' : cover.parent (selected.embedding idx) ∈ selectedParents := by
        simp only [selectedFineIndices, Finset.mem_filter, Finset.mem_univ,
          true_and] at h
        exact h
      exact h'
    · intro hp
      have h_nonempty :
          (wz2PaperFullFiberIndices fine coarse p).Nonempty :=
        cover.fullFiber_nonempty p
      rcases h_nonempty with ⟨source, hsource⟩
      have h_parent : cover.parent source = p :=
        (cover.mem_fullFiber_iff_parent p source).mp hsource
      have h_source_selected : source ∈ selectedFineIndices := by
        simp only [selectedFineIndices, Finset.mem_filter, Finset.mem_univ,
          true_and]
        rw [h_parent]
        exact hp
      let source' : selectedFineIndices := ⟨source, h_source_selected⟩
      let idx : Fin selected.family.card :=
        (selectedFineIndices.orderIsoOfFin rfl).symm source'
      have h_emb : selected.embedding idx = source := by
        exact congrArg Subtype.val
          ((selectedFineIndices.orderIsoOfFin rfl).apply_symm_apply source')
      refine ⟨idx, ?_⟩
      rw [h_emb, h_parent]

  have h_restricted_band :
      ∀ (parent :
          Fin (cover.hitParentSubfamily selected).family.card),
        c ≤ (restrictPaperShading
              ((cover.restrictToHitParents selected).fullFiberSubfamily
                parent)
              selectedShading).mass ∧
          (restrictPaperShading
              ((cover.restrictToHitParents selected).fullFiberSubfamily
                parent)
              selectedShading).mass ≤ 2 * c := by
    intro parent
    let ambientParent :=
      (cover.hitParentSubfamily selected).embedding parent
    let restrictedCover := cover.restrictToHitParents selected
    let restrictedFiberIndices :=
      wz2PaperFullFiberIndices selected.family
        (cover.hitParentSubfamily selected).family parent
    let originalFiberIndices :=
      wz2PaperFullFiberIndices fine coarse ambientParent

    have h_ambient_in_selected : ambientParent ∈ selectedParents := by
      have h1 : ambientParent ∈ cover.hitParentIndices selected :=
        Finset.orderEmbOfFin_mem (cover.hitParentIndices selected) rfl parent
      rw [h_hit_eq] at h1
      exact h1

    have h_restricted_fiber :
        restrictedFiberIndices =
          Finset.univ.filter fun idx : Fin selected.family.card =>
            cover.parent (selected.embedding idx) = ambientParent := by
      ext idx
      have h1 : idx ∈ restrictedFiberIndices ↔
          restrictedCover.parent idx = parent :=
        restrictedCover.mem_fullFiber_iff_parent parent idx
      rw [h1]
      have h2 :
          restrictedCover.parent idx =
            cover.hitParent selected idx := rfl
      rw [h2]
      have h3 :
          (cover.hitParentSubfamily selected).embedding
              (cover.hitParent selected idx) =
            cover.parent (selected.embedding idx) :=
        cover.hitParent_ambient selected idx
      constructor
      · intro h
        have h4 :
            cover.parent (selected.embedding idx) = ambientParent := by
          rw [← h3, h]
        simpa [Finset.mem_filter, Finset.mem_univ] using h4
      · intro h
        have h4 :
            cover.parent (selected.embedding idx) = ambientParent := by
          simpa [Finset.mem_filter, Finset.mem_univ] using h
        have h5 :
            (cover.hitParentSubfamily selected).embedding
                (cover.hitParent selected idx) =
              (cover.hitParentSubfamily selected).embedding parent := by
          rw [h3, h4]
        exact
          (cover.hitParentSubfamily selected).embedding.injective h5

    let f : Fin selected.family.card → Fin fine.card :=
      fun idx => selected.embedding idx

    have h_map_into : ∀ idx ∈ restrictedFiberIndices,
        f idx ∈ originalFiberIndices := by
      intro idx hidx
      rw [h_restricted_fiber] at hidx
      have h4 : cover.parent (f idx) = ambientParent :=
        (Finset.mem_filter.mp hidx).2
      exact
        (cover.mem_fullFiber_iff_parent ambientParent (f idx)).mpr h4

    have h_image :
        Finset.image f restrictedFiberIndices =
          originalFiberIndices := by
      apply Finset.ext
      intro source
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨idx, hidx, rfl⟩
        exact h_map_into idx hidx
      · intro hsource
        have h_parent : cover.parent source = ambientParent :=
          (cover.mem_fullFiber_iff_parent ambientParent source).mp hsource
        have h_source_in_selected : source ∈ selectedFineIndices := by
          simp only [selectedFineIndices, Finset.mem_filter,
            Finset.mem_univ, true_and]
          rw [h_parent]
          exact h_ambient_in_selected
        let source' : selectedFineIndices :=
          ⟨source, h_source_in_selected⟩
        let idx : Fin selected.family.card :=
          (selectedFineIndices.orderIsoOfFin rfl).symm source'
        have h_emb : f idx = source := by
          exact congrArg Subtype.val
            ((selectedFineIndices.orderIsoOfFin rfl).apply_symm_apply source')
        have h_idx_in_fiber : idx ∈ restrictedFiberIndices := by
          rw [h_restricted_fiber]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have h6 : cover.parent (f idx) = ambientParent := by
            rw [congrArg cover.parent h_emb, h_parent]
          exact h6
        exact ⟨idx, h_idx_in_fiber, h_emb⟩

    have h_inj : Set.InjOn f restrictedFiberIndices := by
      intro idx1 _ idx2 _ h
      exact selected.embedding.injective h

    let g : Fin fine.card → ENNReal :=
      fun x => volume (shading.carrier x)
    have h_sum_image :
        ∑ idx ∈ restrictedFiberIndices, g (f idx) =
          ∑ source ∈ Finset.image f restrictedFiberIndices,
            g source := by
      have h :
          ∑ source ∈ Finset.image f restrictedFiberIndices,
              g source =
            ∑ idx ∈ restrictedFiberIndices, g (f idx) :=
        Finset.sum_image h_inj
      exact h.symm
    have h_sum_eq :
        ∑ idx ∈ restrictedFiberIndices,
            volume (shading.carrier (f idx)) =
          ∑ source ∈ originalFiberIndices,
            volume (shading.carrier source) := by
      have h1 :
          ∑ idx ∈ restrictedFiberIndices,
              volume (shading.carrier (f idx)) =
            ∑ idx ∈ restrictedFiberIndices, g (f idx) := by
        apply Finset.sum_congr rfl
        intro _ _
        rfl
      have h2 :
          ∑ source ∈ Finset.image f restrictedFiberIndices,
              g source =
            ∑ source ∈ originalFiberIndices,
              volume (shading.carrier source) := by
        rw [h_image]
      rw [h1, h_sum_image, h2]

    have h_mass_eq :
        (restrictPaperShading
            (restrictedCover.fullFiberSubfamily parent)
            selectedShading).mass =
          (restrictPaperShading
            (cover.fullFiberSubfamily ambientParent)
            shading).mass := by
      calc
        (restrictPaperShading
            (restrictedCover.fullFiberSubfamily parent)
            selectedShading).mass =
          ∑ idx ∈ restrictedFiberIndices,
            volume (selectedShading.carrier idx) := by
              exact
                restrictedCover.fullFiberShading_mass
                  selectedShading parent
        _ =
          ∑ idx ∈ restrictedFiberIndices,
            volume (shading.carrier (f idx)) := by
              apply Finset.sum_congr rfl
              intro idx _
              rfl
        _ =
          ∑ source ∈ originalFiberIndices,
            volume (shading.carrier source) := h_sum_eq
        _ =
          (restrictPaperShading
            (cover.fullFiberSubfamily ambientParent)
            shading).mass := by
              exact
                (cover.fullFiberShading_mass
                  shading ambientParent).symm

    rw [h_mass_eq]
    exact hband ambientParent h_ambient_in_selected

  have hbins_eq' :
      bins = Nat.log 2 (2 * coarse.card) + 1 := by
    simpa [Fintype.card_fin] using hbins_eq
  refine
    ⟨bins, hbins_eq', selectedParents, hselected_nonempty,
      c, hc_pos, hband, selectedFineIndices, rfl, selected,
      rfl, selectedShading, rfl, h_hit_eq, h_retained,
      heavy_selected_full_fiber_complete
        cover selectedParents selectedFineIndices rfl selected rfl
        h_hit_eq,
      h_restricted_band⟩

end Kakeya.Assouad

end
