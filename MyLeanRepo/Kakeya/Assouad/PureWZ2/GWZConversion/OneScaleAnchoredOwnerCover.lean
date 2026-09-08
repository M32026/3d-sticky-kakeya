import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AnchoredParentContainment
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.CompleteFiberOwner
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.LocalizedDistinctReanchoring

/-!
# One-scale anchored owner cover

At one small exact GWZ reference scale:

1. choose one auxiliary owner from each complete full fiber;
2. retain exactly the owner parents that are hit;
3. canonically reanchor those parents at the common localization center;
4. obtain a surjective strict ordinary tube cover of the already reanchored
   fine family.

The owner map is chosen from complete containment incidence and remains
explicitly separate from every GWZ assigned-parent API.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined

attribute [local instance] Classical.propDecidable

/-- One active anchored parent cover at one exact GWZ reference scale. -/
structure PureWZ2OneScaleAnchoredOwnerCoverData
    {delta A : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    (fine : PureWZ2LocalizedDistinctReanchoringData sourceShading)
    {constant : ENNReal}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    (scaleData :
      PureWZ2GWZScaleData (A := A) source scale constant) where
  owner : Fin fine.family.card → Fin scaleData.coarse.card
  owner_mem :
    ∀ index,
      fine.sourceIndex index ∈
        scaleData.fullFiberIndices (owner index)
  complete_parent_degree :
    ∀ index,
      (Finset.univ.filter fun parent :
        Fin scaleData.coarse.card =>
          fine.sourceIndex index ∈
            scaleData.fullFiberIndices parent).card ≤
        pureWZ2CompleteFiberOverlapBound A
  activeParents : Finset (Fin scaleData.coarse.card)
  activeParents_eq :
    activeParents = Finset.univ.image owner
  coarse : Kakeya.Streamlined.TubeFamily (8 * A * scale.1)
  originalParent :
    Fin coarse.card ↪ Fin scaleData.coarse.card
  tube_eq_reanchored_parent :
    ∀ parent,
      coarse.tube parent =
        pureWZ2ReanchoredParentTube
          (A := A) fine.center
          (scaleData.coarse.tube (originalParent parent))
  cover : Kakeya.Streamlined.TubeCover fine.family coarse
  cover_original_owner :
    ∀ index,
      originalParent (cover.parent index) = owner index

/--
Build the active-parent anchored cover at one small exact reference scale.
-/
theorem pureWZ2_one_scale_anchored_owner_cover
    {delta A : ℝ}
    (hdelta : 0 < delta)
    (hA : 1 ≤ A)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    (fine : PureWZ2LocalizedDistinctReanchoringData sourceShading)
    (hfineRadius : fine.radius ≤ 1 / 4)
    {constant : ENNReal}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    (scaleData :
      PureWZ2GWZScaleData (A := A) source scale constant)
    (hscaleSmall : scale.1 ≤ 1 / (200 * A)) :
    Nonempty
      (PureWZ2OneScaleAnchoredOwnerCoverData
        fine scaleData) := by
  rcases
      pureWZ2_complete_fiber_owner
        hdelta hA scaleData hscaleSmall
        fine.sourceIndex with
    ⟨ownerData⟩
  let owner := ownerData.owner
  let activeParents :
      Finset (Fin scaleData.coarse.card) :=
    Finset.univ.image owner
  let originalParent :
      Fin activeParents.card ↪ Fin scaleData.coarse.card :=
    (activeParents.orderEmbOfFin rfl).toEmbedding
  let coarse :
      Kakeya.Streamlined.TubeFamily (8 * A * scale.1) :=
    { card := activeParents.card
      tube := fun parent =>
        pureWZ2ReanchoredParentTube
          (A := A) fine.center
          (scaleData.coarse.tube (originalParent parent)) }
  have hownerActive :
      ∀ index, owner index ∈ activeParents := by
    intro index
    exact
      Finset.mem_image.mpr
        ⟨index, Finset.mem_univ index, rfl⟩
  let activeParentEquiv :
      Fin activeParents.card ≃ activeParents :=
    activeParents.orderIsoOfFin rfl
  let parent :
      Fin fine.family.card → Fin coarse.card := fun index =>
    activeParentEquiv.symm
      ⟨owner index, hownerActive index⟩
  have horiginalParent :
      ∀ index,
        originalParent (parent index) = owner index := by
    intro index
    change
      activeParents.orderEmbOfFin rfl
          (activeParentEquiv.symm
            ⟨owner index, hownerActive index⟩) =
        owner index
    exact congrArg Subtype.val
      (activeParentEquiv.apply_symm_apply
        ⟨owner index, hownerActive index⟩)
  have hparentSurjective :
      Function.Surjective parent := by
    intro activeIndex
    have hactiveMember :
        originalParent activeIndex ∈ activeParents :=
      Finset.orderEmbOfFin_mem activeParents rfl activeIndex
    have himage :
        originalParent activeIndex ∈
          Finset.univ.image owner := by
      simpa [activeParents] using hactiveMember
    rcases Finset.mem_image.mp himage with
      ⟨index, _, howner⟩
    refine ⟨index, ?_⟩
    apply activeParentEquiv.injective
    have hparentImage :
        activeParentEquiv (parent index) =
          ⟨owner index, hownerActive index⟩ :=
      activeParentEquiv.apply_symm_apply
        ⟨owner index, hownerActive index⟩
    rw [hparentImage]
    apply Subtype.ext
    exact howner
  have hnested :
      ∀ index,
        (fine.family.tube index).carrier ⊆
          (coarse.tube (parent index)).carrier := by
    intro index
    rcases fine.source_meets_ball index with
      ⟨point, hpointShading, hpointBall⟩
    have hpointSource :
        point ∈
          (source.tube (fine.sourceIndex index)).carrier :=
      sourceShading.subset_body
        (fine.sourceIndex index) hpointShading
    have hcomplete :
        (source.tube (fine.sourceIndex index)).carrier ⊆
          wz2PaperCenteredDilatedCarrier A
            (scaleData.coarse.tube (owner index)) := by
      have hmember := ownerData.owner_mem index
      rw [scaleData.fullFiberIndices_eq] at hmember
      exact (Finset.mem_filter.mp hmember).2
    have hcontainment :=
      pureWZ2_reanchored_complete_parent_containment
        hdelta
        (show 0 < scale.1 by
          have := scale.property.1
          linarith)
        hA scale.property.1 hscaleSmall
        fine.radius_pos.le hfineRadius
        hpointSource hpointBall hcomplete
    rw [fine.tube_eq_reanchored index]
    change
      (pureWZ2ReanchoredTube fine.center
          (source.tube (fine.sourceIndex index))).carrier ⊆
        (pureWZ2ReanchoredParentTube
          (A := A) fine.center
          (scaleData.coarse.tube
            (originalParent (parent index)))).carrier
    rw [horiginalParent index]
    exact hcontainment
  let cover :
      Kakeya.Streamlined.TubeCover fine.family coarse :=
    { parent := parent
      parent_surjective := hparentSurjective
      nested := hnested }
  exact
    ⟨{
      owner := owner
      owner_mem := ownerData.owner_mem
      complete_parent_degree :=
        ownerData.complete_parent_degree
      activeParents := activeParents
      activeParents_eq := rfl
      coarse := coarse
      originalParent := originalParent
      tube_eq_reanchored_parent := fun _ => rfl
      cover := cover
      cover_original_owner := horiginalParent
    }⟩

end Kakeya.Assouad

end
