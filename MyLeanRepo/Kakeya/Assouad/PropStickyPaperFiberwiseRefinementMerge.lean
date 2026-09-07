import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFiberwiseRefinementMergeStatements
import Mathlib.Algebra.BigOperators.Fin

/-!
# Merge refinements from all full parent fibers
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

theorem wz2_paper_fiberwise_refinement_merge :
    WZ2PaperFiberwiseRefinementMergeStatement := by
  intro delta rho fine coarse cover shading logExponent fiberRefinement
  let N := ∑ parent : Fin coarse.card,
    (fiberRefinement parent).selected.family.card
  let SigmaType := Σ parent : Fin coarse.card,
    Fin (fiberRefinement parent).selected.family.card
  let e : Fin N ≃ SigmaType := finSigmaFinEquiv.symm
  let g : Fin N → Fin fine.card := fun i =>
    (cover.fullFiberSubfamily (e i).1).embedding
      ((fiberRefinement (e i).1).selected.embedding (e i).2)
  have hg_inj : Function.Injective g := by
    intro i j h
    rcases hei : e i with ⟨pi, li⟩
    rcases hej : e j with ⟨pj, lj⟩
    have hgi : g i =
        (cover.fullFiberSubfamily pi).embedding
          ((fiberRefinement pi).selected.embedding li) := by
      dsimp only [g]
      rw [hei]
    have hgj : g j =
        (cover.fullFiberSubfamily pj).embedding
          ((fiberRefinement pj).selected.embedding lj) := by
      dsimp only [g]
      rw [hej]
    have h' :
        (cover.fullFiberSubfamily pi).embedding
            ((fiberRefinement pi).selected.embedding li) =
          (cover.fullFiberSubfamily pj).embedding
            ((fiberRefinement pj).selected.embedding lj) := by
      rw [← hgi, ← hgj, h]
    have h1 : cover.parent (g i) = pi := by
      rw [hgi]
      exact
        (cover.mem_fullFiber_iff_parent pi _).mp
          (cover.fullFiberSubfamily_mem pi _)
    have h2 : cover.parent (g j) = pj := by
      rw [hgj]
      exact
        (cover.mem_fullFiber_iff_parent pj _).mp
          (cover.fullFiberSubfamily_mem pj _)
    have hparent : pi = pj := by
      rw [← h1, h, h2]
    subst hparent
    have h3 :
        (cover.fullFiberSubfamily pi).embedding
            ((fiberRefinement pi).selected.embedding li) =
          (cover.fullFiberSubfamily pi).embedding
            ((fiberRefinement pi).selected.embedding lj) :=
      h'
    have h4 :
        (fiberRefinement pi).selected.embedding li =
          (fiberRefinement pi).selected.embedding lj :=
      (cover.fullFiberSubfamily pi).embedding.injective h3
    have h5 : li = lj :=
      (fiberRefinement pi).selected.embedding.injective h4
    have h6 : e i = e j := by
      rw [hei, hej]
      congr
    exact e.injective h6
  let gEmb : Fin N ↪ Fin fine.card :=
    { toFun := g
      inj' := hg_inj }
  let globalSelected : Kakeya.Streamlined.TubeSubfamily fine :=
    { family :=
        { card := N
          tube := fun i => fine.tube (gEmb i) }
      embedding := gEmb
      tube_eq := fun _ => rfl }
  let parentOf (i : Fin N) : Fin coarse.card := (e i).1
  let localOf (i : Fin N) :
      Fin (fiberRefinement (parentOf i)).selected.family.card :=
    (e i).2
  let globalRefined : WZ1PaperTubeShading globalSelected.family :=
    { carrier := fun i =>
        (fiberRefinement (parentOf i)).refined.carrier (localOf i)
      measurable_carrier := fun i =>
        (fiberRefinement (parentOf i)).refined.measurable_carrier
          (localOf i)
      subset_body := fun i => by
        let parent := parentOf i
        let localIdx := localOf i
        have h_local :
            (fiberRefinement parent).refined.carrier localIdx ⊆
              wz1PaperTubeCarrier
                ((fiberRefinement parent).selected.family.tube
                  localIdx) :=
          (fiberRefinement parent).refined.subset_body localIdx
        have h_tube_eq :
            (fiberRefinement parent).selected.family.tube localIdx =
              globalSelected.family.tube i := by
          rw [
            (fiberRefinement parent).selected.tube_eq localIdx,
            (cover.fullFiberSubfamily parent).tube_eq
          ]
          rfl
        rw [h_tube_eq] at h_local
        exact h_local }
  have h_subshading : ∀ i,
      globalRefined.carrier i ⊆
        shading.carrier (globalSelected.embedding i) := by
    intro i
    let parent := parentOf i
    let localIdx := localOf i
    have h_local :
        (fiberRefinement parent).refined.carrier localIdx ⊆
          (restrictPaperShading
            (cover.fullFiberSubfamily parent) shading).carrier
            ((fiberRefinement parent).selected.embedding localIdx) :=
      (fiberRefinement parent).subshading localIdx
    have h_restrict :
        (restrictPaperShading
          (cover.fullFiberSubfamily parent) shading).carrier
            ((fiberRefinement parent).selected.embedding localIdx) =
          shading.carrier
            ((cover.fullFiberSubfamily parent).embedding
              ((fiberRefinement parent).selected.embedding localIdx)) :=
      rfl
    rw [h_restrict] at h_local
    exact h_local
  have h_mass : globalRefined.mass =
      ∑ parent : Fin coarse.card,
        (fiberRefinement parent).refined.mass := by
    have h : globalRefined.mass =
        ∑ x : SigmaType,
          volume ((fiberRefinement x.1).refined.carrier x.2) := by
      simp [globalRefined, Kakeya.Streamlined.Shading.mass]
      exact
        Fintype.sum_equiv e
          (fun i => volume (globalRefined.carrier i))
          (fun x => volume ((fiberRefinement x.1).refined.carrier x.2))
          (fun i => rfl)
    rw [h]
    rw [Fintype.sum_sigma]
      <;> simp [Kakeya.Streamlined.Shading.mass]
      <;> rfl
  have h_retained :
      wz1PaperRefinementFraction delta logExponent * shading.mass ≤
        globalRefined.mass := by
    have h1 : ∀ parent : Fin coarse.card,
        wz1PaperRefinementFraction delta logExponent *
            (restrictPaperShading
              (cover.fullFiberSubfamily parent) shading).mass ≤
          (fiberRefinement parent).refined.mass :=
      fun parent => (fiberRefinement parent).retained_mass
    have h2 :
        wz1PaperRefinementFraction delta logExponent *
            (∑ parent : Fin coarse.card,
              (restrictPaperShading
                (cover.fullFiberSubfamily parent) shading).mass) ≤
          ∑ parent : Fin coarse.card,
            (fiberRefinement parent).refined.mass := by
      calc
        wz1PaperRefinementFraction delta logExponent *
              (∑ parent : Fin coarse.card,
                (restrictPaperShading
                  (cover.fullFiberSubfamily parent) shading).mass) =
            ∑ parent : Fin coarse.card,
              wz1PaperRefinementFraction delta logExponent *
                (restrictPaperShading
                  (cover.fullFiberSubfamily parent) shading).mass := by
          rw [Finset.mul_sum]
        _ ≤ ∑ parent : Fin coarse.card,
            (fiberRefinement parent).refined.mass := by
          apply Finset.sum_le_sum
          intro parent _
          exact h1 parent
    have h3 :
        (∑ parent : Fin coarse.card,
          (restrictPaperShading
            (cover.fullFiberSubfamily parent) shading).mass) =
          shading.mass :=
      cover.sum_fullFiberShading_mass shading
    rw [h3] at h2
    rw [h_mass]
    exact h2
  let refinement : WZ1PaperRefinement shading logExponent :=
    { selected := globalSelected
      refined := globalRefined
      subshading := h_subshading
      retained_mass := h_retained }
  have h_cubical :
      (∀ parent,
        WZ1PaperIsCubicalShading (fiberRefinement parent).refined) →
        WZ1PaperIsCubicalShading refinement.refined := by
    intro h index point hpoint
    exact h (parentOf index) (localOf index) point hpoint
  have h_nonempty :
      (∀ parent index,
        ((fiberRefinement parent).refined.carrier index).Nonempty) →
        ∀ index, (refinement.refined.carrier index).Nonempty := by
    intro h index
    exact h (parentOf index) (localOf index)
  exact
    ⟨{
      refinement := refinement
      indexEquiv := e
      selected_embedding_eq := by
        intro index
        rfl
      refined_carrier_eq := by
        intro index
        rfl
      selected_card_eq := by rfl
      refined_mass_eq := h_mass
      refined_cubical := h_cubical
      refined_nonempty := h_nonempty
    }⟩

/-- One full fiber of a fiberwise merge is exactly a finite reindexing of the
local selected family used at that parent. -/
structure WZ2PaperFiberwiseMergedFullFiberReindexData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {logExponent : ℕ}
    {fiberRefinement :
      ∀ parent : Fin coarse.card,
        WZ1PaperRefinement
          (restrictPaperShading (cover.fullFiberSubfamily parent) shading)
          logExponent}
    (merged : WZ2PaperFiberwiseRefinementMergeData
      cover shading logExponent fiberRefinement)
    (parent : Fin coarse.card) where
  localIndex :
    Fin (wz2PaperFullFiberSubfamily
      merged.refinement.selected.family coarse parent).family.card →
      Fin (fiberRefinement parent).selected.family.card
  localIndex_bijective : Function.Bijective localIndex
  tube_eq :
    ∀ index,
      (wz2PaperFullFiberSubfamily
        merged.refinement.selected.family coarse parent).family.tube index =
        (fiberRefinement parent).selected.family.tube (localIndex index)
  carrier_eq :
    ∀ index,
      (restrictPaperShading
        (wz2PaperFullFiberSubfamily
          merged.refinement.selected.family coarse parent)
        merged.refinement.refined).carrier index =
        (fiberRefinement parent).refined.carrier (localIndex index)

/-- Construct the canonical reindexing of one full fiber of a fiberwise
merge. -/
theorem WZ2PaperFiberwiseRefinementMergeData.fullFiberReindex
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    {logExponent : ℕ}
    {fiberRefinement :
      ∀ parent : Fin coarse.card,
        WZ1PaperRefinement
          (restrictPaperShading (cover.fullFiberSubfamily parent) shading)
          logExponent}
    (merged : WZ2PaperFiberwiseRefinementMergeData
      cover shading logExponent fiberRefinement)
    (parent : Fin coarse.card) :
    Nonempty (WZ2PaperFiberwiseMergedFullFiberReindexData merged parent) := by
  let fiberSubfamily :=
    wz2PaperFullFiberSubfamily
      merged.refinement.selected.family coarse parent
  let selectedFamily := merged.refinement.selected.family
  have parentEq : ∀ index : Fin selectedFamily.card,
      cover.parent (merged.refinement.selected.embedding index) =
        (merged.indexEquiv index).1 := by
    intro index
    rw [merged.selected_embedding_eq index]
    exact
      (cover.mem_fullFiber_iff_parent
        (merged.indexEquiv index).1 _).mp
        (cover.fullFiberSubfamily_mem (merged.indexEquiv index).1 _)
  let fullFiberSet :=
    wz2PaperFullFiberIndices selectedFamily coarse parent
  let SigmaType :=
    Σ currentParent : Fin coarse.card,
      Fin (fiberRefinement currentParent).selected.family.card
  have hSigmaType : ∀ index : Fin selectedFamily.card,
      index ∈ fullFiberSet ↔ (merged.indexEquiv index).1 = parent := by
    intro index
    rw [mem_wz2PaperFullFiberIndices_iff]
    constructor
    · intro covered
      have ambientCovered :
          WZ1PaperTubeCovers
            (fine.tube (merged.refinement.selected.embedding index))
            (coarse.tube parent) := by
        rw [← merged.refinement.selected.tube_eq index]
        exact covered
      have actualParent :=
        (cover.mem_fullFiber_iff_parent parent
          (merged.refinement.selected.embedding index)).mp
          ((mem_wz2PaperFullFiberIndices_iff parent _).mpr ambientCovered)
      exact (parentEq index).symm.trans actualParent
    · intro indexParent
      have actualParent :
          cover.parent (merged.refinement.selected.embedding index) = parent :=
        (parentEq index).trans indexParent
      have ambientCovered :=
        (mem_wz2PaperFullFiberIndices_iff parent _).mp
          ((cover.mem_fullFiber_iff_parent parent
            (merged.refinement.selected.embedding index)).mpr actualParent)
      rw [merged.refinement.selected.tube_eq index]
      exact ambientCovered
  have hFirstComponent : ∀ index,
      (merged.indexEquiv
        (fiberSubfamily.embedding index)).1 = parent := by
    intro index
    exact
      (hSigmaType (fiberSubfamily.embedding index)).mp
        (Finset.orderEmbOfFin_mem fullFiberSet rfl index)
  have hSigmaFiber :
      ∀ (first second : Fin coarse.card)
        (h : first = second)
        (index : Fin (fiberRefinement first).selected.family.card),
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
        ⟨merged.indexEquiv index.1, (hSigmaType index.1).mp index.2⟩
      invFun := fun index =>
        ⟨merged.indexEquiv.symm index.1,
          (hSigmaType _).mpr (by simpa using index.2)⟩
      left_inv := by
        intro index
        apply Subtype.ext
        exact merged.indexEquiv.left_inv index
      right_inv := by
        intro index
        apply Subtype.ext
        exact merged.indexEquiv.right_inv index }
  let localEquiv :
      {index : SigmaType // index.1 = parent} ≃
        Fin (fiberRefinement parent).selected.family.card :=
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
        Fin (fiberRefinement parent).selected.family.card :=
    fun index => localEquiv (sigmaEquiv (fiberEquiv index))
  have hLocalIndex : ∀ index,
      localIndex index =
        (hFirstComponent index) ▸
          (merged.indexEquiv (fiberSubfamily.embedding index)).2 := by
    intro index
    rfl
  let tubeAt (index : SigmaType) :=
    fine.tube
      ((cover.fullFiberSubfamily index.1).embedding
        ((fiberRefinement index.1).selected.embedding index.2))
  let carrierAt (index : SigmaType) :=
    (fiberRefinement index.1).refined.carrier index.2
  have hTube : ∀ index,
      fiberSubfamily.family.tube index =
        (fiberRefinement parent).selected.family.tube
          (localIndex index) := by
    intro index
    set selectedIndex := fiberSubfamily.embedding index with hSelectedIndex
    let sigmaIndex : SigmaType := merged.indexEquiv selectedIndex
    have hFirst : sigmaIndex.1 = parent := hFirstComponent index
    have hLocal :
        localIndex index = hFirst ▸ sigmaIndex.2 := hLocalIndex index
    rw [hLocal]
    have hSelected :
        merged.refinement.selected.embedding selectedIndex =
          (cover.fullFiberSubfamily sigmaIndex.1).embedding
            ((fiberRefinement sigmaIndex.1).selected.embedding sigmaIndex.2) :=
      merged.selected_embedding_eq selectedIndex
    have hSigma :
        sigmaIndex =
          (⟨parent, hFirst ▸ sigmaIndex.2⟩ : SigmaType) := by
      have hFirst' :
          (⟨parent, hFirst ▸ sigmaIndex.2⟩ : SigmaType) =
            ⟨sigmaIndex.1, sigmaIndex.2⟩ :=
        hSigmaFiber sigmaIndex.1 parent hFirst sigmaIndex.2
      have hEta : sigmaIndex = ⟨sigmaIndex.1, sigmaIndex.2⟩ :=
        Sigma.eta sigmaIndex
      exact hEta.trans hFirst'.symm
    calc
      fiberSubfamily.family.tube index = selectedFamily.tube selectedIndex :=
        fiberSubfamily.tube_eq index
      _ = fine.tube (merged.refinement.selected.embedding selectedIndex) :=
        merged.refinement.selected.tube_eq selectedIndex
      _ = tubeAt sigmaIndex := by rw [hSelected]
      _ = tubeAt (⟨parent, hFirst ▸ sigmaIndex.2⟩ : SigmaType) :=
        congrArg tubeAt hSigma
      _ = (cover.fullFiberSubfamily parent).family.tube
            ((fiberRefinement parent).selected.embedding
              (hFirst ▸ sigmaIndex.2)) := by
        exact ((cover.fullFiberSubfamily parent).tube_eq _).symm
      _ = (fiberRefinement parent).selected.family.tube
            (hFirst ▸ sigmaIndex.2) := by
        exact ((fiberRefinement parent).selected.tube_eq _).symm
  have hCarrier : ∀ index,
      (restrictPaperShading fiberSubfamily
        merged.refinement.refined).carrier index =
          (fiberRefinement parent).refined.carrier
            (localIndex index) := by
    intro index
    set selectedIndex := fiberSubfamily.embedding index with hSelectedIndex
    let sigmaIndex : SigmaType := merged.indexEquiv selectedIndex
    have hFirst : sigmaIndex.1 = parent := hFirstComponent index
    have hLocal :
        localIndex index = hFirst ▸ sigmaIndex.2 := hLocalIndex index
    rw [hLocal]
    have hSigma :
        sigmaIndex =
          (⟨parent, hFirst ▸ sigmaIndex.2⟩ : SigmaType) := by
      have hFirst' :
          (⟨parent, hFirst ▸ sigmaIndex.2⟩ : SigmaType) =
            ⟨sigmaIndex.1, sigmaIndex.2⟩ :=
        hSigmaFiber sigmaIndex.1 parent hFirst sigmaIndex.2
      have hEta : sigmaIndex = ⟨sigmaIndex.1, sigmaIndex.2⟩ :=
        Sigma.eta sigmaIndex
      exact hEta.trans hFirst'.symm
    calc
      (restrictPaperShading fiberSubfamily
          merged.refinement.refined).carrier index =
          merged.refinement.refined.carrier selectedIndex := by rfl
      _ = carrierAt sigmaIndex := merged.refined_carrier_eq selectedIndex
      _ = carrierAt (⟨parent, hFirst ▸ sigmaIndex.2⟩ : SigmaType) :=
        congrArg carrierAt hSigma
  let totalEquiv :
      Fin fiberSubfamily.family.card ≃
        Fin (fiberRefinement parent).selected.family.card :=
    (fiberEquiv.trans sigmaEquiv).trans localEquiv
  exact ⟨{
    localIndex := localIndex
    localIndex_bijective := totalEquiv.bijective
    tube_eq := hTube
    carrier_eq := hCarrier
  }⟩

end Kakeya.Assouad

end
