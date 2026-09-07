import MyLeanRepo.Kakeya.Assouad.PropStickyPaperStructuralMergedFiberReindexStatements

/-! # Reindex one structurally merged full fiber -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_structural_merged_fiber_reindex :
    WZ2PaperStructuralMergedFiberReindexStatement := by
  intro delta rho sigma strongLoss outputLoss fine coarse cover shading hrho
    logExponent fiberData merged parent
  let fiberSubfamily :=
    merged.restrictedCover.fullFiberSubfamily parent
  let selectedFamily := merged.merged.refinement.selected.family
  have hParentEq :
      ∀ index : Fin selectedFamily.card,
        merged.restrictedCover.parent index =
          (merged.merged.indexEquiv index).1 := by
    intro index
    rw [merged.restricted_parent_eq index,
      merged.selected_embedding_eq index]
    exact
      (cover.mem_fullFiber_iff_parent
        (merged.merged.indexEquiv index).1 _).mp
        (cover.fullFiberSubfamily_mem
          (merged.merged.indexEquiv index).1 _)
  let fullFiberSet :=
    wz2PaperFullFiberIndices selectedFamily coarse parent
  let SigmaType :=
    Σ currentParent : Fin coarse.card,
      Fin (fiberData currentParent).refinement.selected.family.card
  have hSigmaType :
      ∀ index : Fin selectedFamily.card,
        index ∈ fullFiberSet ↔
          (merged.merged.indexEquiv index).1 = parent := by
    intro index
    rw [merged.restrictedCover.mem_fullFiber_iff_parent,
      hParentEq index]
  have hFirstComponent :
      ∀ index,
        (merged.merged.indexEquiv
          (fiberSubfamily.embedding index)).1 = parent := by
    intro index
    exact
      (hSigmaType (fiberSubfamily.embedding index)).mp
        (merged.restrictedCover.fullFiberSubfamily_mem parent index)
  have hSigmaFiber :
      ∀ (first second : Fin coarse.card)
        (h : first = second)
        (index : Fin (fiberData first).refinement.selected.family.card),
        (⟨second, h ▸ index⟩ : SigmaType) =
          ⟨first, index⟩ := by
    intro first second h index
    induction h
    rfl
  let fiberEquiv :
      Fin fiberSubfamily.family.card ≃
        {index : Fin selectedFamily.card // index ∈ fullFiberSet} :=
    (fullFiberSet.orderIsoOfFin rfl).toEquiv
  let sigmaEquiv :
      {index : Fin selectedFamily.card // index ∈ fullFiberSet} ≃
        {index : SigmaType // index.1 = parent} :=
    { toFun := fun index =>
        ⟨merged.merged.indexEquiv index,
          (hSigmaType index).mp index.property⟩
      invFun := fun index =>
        ⟨merged.merged.indexEquiv.symm index,
          (hSigmaType _).mpr (by
            simpa using index.property)⟩
      left_inv := by
        intro index
        apply Subtype.ext
        exact merged.merged.indexEquiv.left_inv index
      right_inv := by
        intro index
        apply Subtype.ext
        exact merged.merged.indexEquiv.right_inv index }
  let localEquiv :
      {index : SigmaType // index.1 = parent} ≃
        Fin (fiberData parent).refinement.selected.family.card :=
    { toFun := fun index => index.property ▸ index.val.2
      invFun := fun index => ⟨⟨parent, index⟩, rfl⟩
      left_inv := by
        intro index
        apply Subtype.ext
        dsimp only
        have h : index.val.1 = parent := index.property
        exact hSigmaFiber index.val.1 parent h index.val.2
      right_inv := by
        intro index
        rfl }
  let localIndex :
      Fin fiberSubfamily.family.card →
        Fin (fiberData parent).refinement.selected.family.card :=
    fun index => localEquiv (sigmaEquiv (fiberEquiv index))
  have hLocalIndex :
      ∀ index,
        localIndex index =
          (hFirstComponent index) ▸
            (merged.merged.indexEquiv
              (fiberSubfamily.embedding index)).2 := by
    intro index
    rfl
  let tubeAt (index : SigmaType) :=
    fine.tube
      ((cover.fullFiberSubfamily index.1).embedding
        ((fiberData index.1).refinement.selected.embedding
          index.2))
  let carrierAt (index : SigmaType) :=
    (fiberData index.1).refinement.refined.carrier index.2
  have hTube :
      ∀ index,
        fiberSubfamily.family.tube index =
          (fiberData parent).refinement.selected.family.tube
            (localIndex index) := by
    intro index
    set selectedIndex := fiberSubfamily.embedding index with hSelectedIndex
    let sigmaIndex : SigmaType :=
      merged.merged.indexEquiv selectedIndex
    have hFirst : sigmaIndex.1 = parent :=
      hFirstComponent index
    have hLocal :
        localIndex index = hFirst ▸ sigmaIndex.2 :=
      hLocalIndex index
    rw [hLocal]
    have hSelected :
        merged.merged.refinement.selected.embedding selectedIndex =
          (cover.fullFiberSubfamily sigmaIndex.1).embedding
            ((fiberData sigmaIndex.1).refinement.selected.embedding
              sigmaIndex.2) :=
      merged.selected_embedding_eq selectedIndex
    have hSigma :
        sigmaIndex =
          (⟨parent, hFirst ▸ sigmaIndex.2⟩ : SigmaType) := by
      have hFirst' :
          (⟨parent, hFirst ▸ sigmaIndex.2⟩ : SigmaType) =
            ⟨sigmaIndex.1, sigmaIndex.2⟩ :=
        hSigmaFiber sigmaIndex.1 parent hFirst sigmaIndex.2
      have hEta :
          sigmaIndex = ⟨sigmaIndex.1, sigmaIndex.2⟩ :=
        Sigma.eta sigmaIndex
      exact hEta.trans hFirst'.symm
    calc
      fiberSubfamily.family.tube index =
          selectedFamily.tube selectedIndex :=
        fiberSubfamily.tube_eq index
      _ =
          fine.tube
            (merged.merged.refinement.selected.embedding
              selectedIndex) :=
        merged.merged.refinement.selected.tube_eq selectedIndex
      _ = tubeAt sigmaIndex := by
        rw [hSelected]
      _ = tubeAt
          (⟨parent, hFirst ▸ sigmaIndex.2⟩ : SigmaType) :=
        congrArg tubeAt hSigma
      _ =
          (cover.fullFiberSubfamily parent).family.tube
            ((fiberData parent).refinement.selected.embedding
              (hFirst ▸ sigmaIndex.2)) := by
        exact
          ((cover.fullFiberSubfamily parent).tube_eq _).symm
      _ =
          (fiberData parent).refinement.selected.family.tube
            (hFirst ▸ sigmaIndex.2) := by
        exact
          ((fiberData parent).refinement.selected.tube_eq _).symm
  have hCarrier :
      ∀ index,
        (restrictPaperShading fiberSubfamily
          merged.merged.refinement.refined).carrier index =
          (fiberData parent).refinement.refined.carrier
            (localIndex index) := by
    intro index
    set selectedIndex := fiberSubfamily.embedding index with hSelectedIndex
    let sigmaIndex : SigmaType :=
      merged.merged.indexEquiv selectedIndex
    have hFirst : sigmaIndex.1 = parent :=
      hFirstComponent index
    have hLocal :
        localIndex index = hFirst ▸ sigmaIndex.2 :=
      hLocalIndex index
    rw [hLocal]
    have hSigma :
        sigmaIndex =
          (⟨parent, hFirst ▸ sigmaIndex.2⟩ : SigmaType) := by
      have hFirst' :
          (⟨parent, hFirst ▸ sigmaIndex.2⟩ : SigmaType) =
            ⟨sigmaIndex.1, sigmaIndex.2⟩ :=
        hSigmaFiber sigmaIndex.1 parent hFirst sigmaIndex.2
      have hEta :
          sigmaIndex = ⟨sigmaIndex.1, sigmaIndex.2⟩ :=
        Sigma.eta sigmaIndex
      exact hEta.trans hFirst'.symm
    calc
      (restrictPaperShading fiberSubfamily
          merged.merged.refinement.refined).carrier index =
          merged.merged.refinement.refined.carrier selectedIndex := by
        rfl
      _ = carrierAt sigmaIndex :=
        merged.refined_carrier_eq selectedIndex
      _ =
          carrierAt
            (⟨parent, hFirst ▸ sigmaIndex.2⟩ : SigmaType) :=
        congrArg carrierAt hSigma
  let totalEquiv :
      Fin fiberSubfamily.family.card ≃
        Fin (fiberData parent).refinement.selected.family.card :=
    (fiberEquiv.trans sigmaEquiv).trans localEquiv
  exact
    ⟨{
      localIndex := localIndex
      localIndex_bijective := totalEquiv.bijective
      tube_eq := hTube
      carrier_eq := hCarrier
    }⟩

end Kakeya.Assouad

end
