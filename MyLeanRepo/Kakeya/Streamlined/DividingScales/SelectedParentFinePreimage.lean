import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.SingleScaleCover
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# Complete assigned fine preimage of selected parents

Given a surjective dilated cover and a selected coarse subfamily, retain
exactly all fine indices whose assigned parent belongs to that selected
subfamily.  The restricted parent map remains surjective and preserves the
same dilation.

This is an auxiliary harmless refinement used when a terminal carried family
is pulled backward through a fresh outer edge.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- Ambient fine indices assigned to one selected coarse subfamily. -/
def selectedParentFinePreimageIndices
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (cover : DilatedTubeCover A fine coarse)
    (selected : TubeSubfamily coarse) :
    Finset (Fin fine.card) := by
  classical
  exact Finset.univ.filter fun i =>
    cover.parent i ∈ Finset.image selected.embedding Finset.univ

/-- The complete assigned fine preimage of a selected coarse subfamily. -/
def selectedParentFinePreimage
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (cover : DilatedTubeCover A fine coarse)
    (selected : TubeSubfamily coarse) :
    TubeSubfamily fine :=
  TubeSubfamily.fromFinset fine
    (selectedParentFinePreimageIndices cover selected)

/-- Every selected fine index embeds into the defining ambient preimage. -/
lemma selectedParentFinePreimage_embedding_mem
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (cover : DilatedTubeCover A fine coarse)
    (selected : TubeSubfamily coarse)
    (i : Fin (selectedParentFinePreimage cover selected).family.card) :
    (selectedParentFinePreimage cover selected).embedding i ∈
      selectedParentFinePreimageIndices cover selected := by
  change
    Fin (selectedParentFinePreimageIndices cover selected).card at i
  change
    (selectedParentFinePreimageIndices cover selected).orderEmbOfFin rfl i ∈
      selectedParentFinePreimageIndices cover selected
  exact Finset.orderEmbOfFin_mem _ rfl i

/-- The assigned ambient parent of every selected fine index lies in the
selected coarse image. -/
lemma selectedParentFinePreimage_parent_mem
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (cover : DilatedTubeCover A fine coarse)
    (selected : TubeSubfamily coarse)
    (i : Fin (selectedParentFinePreimage cover selected).family.card) :
    cover.parent ((selectedParentFinePreimage cover selected).embedding i) ∈
      Finset.image selected.embedding Finset.univ := by
  have hi :=
    selectedParentFinePreimage_embedding_mem cover selected i
  simpa [selectedParentFinePreimageIndices] using hi

/-- Selected coarse index corresponding to one assigned ambient parent. -/
def selectedParentFinePreimageParent
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (cover : DilatedTubeCover A fine coarse)
    (selected : TubeSubfamily coarse)
    (i : Fin (selectedParentFinePreimage cover selected).family.card) :
    Fin selected.family.card :=
  Classical.choose <|
    Finset.mem_image.mp
      (selectedParentFinePreimage_parent_mem cover selected i)

lemma selectedParentFinePreimageParent_spec
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (cover : DilatedTubeCover A fine coarse)
    (selected : TubeSubfamily coarse)
    (i : Fin (selectedParentFinePreimage cover selected).family.card) :
    selected.embedding
        (selectedParentFinePreimageParent cover selected i) =
      cover.parent
        ((selectedParentFinePreimage cover selected).embedding i) :=
  (Classical.choose_spec <|
    Finset.mem_image.mp
      (selectedParentFinePreimage_parent_mem cover selected i)).2

/-- The complete assigned preimage still covers every selected parent with
the original dilation. -/
def selectedParentFinePreimageCover
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (cover : DilatedTubeCover A fine coarse)
    (selected : TubeSubfamily coarse) :
    DilatedTubeCover A
      (selectedParentFinePreimage cover selected).family
      selected.family where
  parent := selectedParentFinePreimageParent cover selected
  parent_surjective := by
    intro j
    rcases cover.parent_surjective (selected.embedding j) with
      ⟨ambient, hambient⟩
    have hmem :
        ambient ∈ selectedParentFinePreimageIndices cover selected := by
      simp [selectedParentFinePreimageIndices, hambient]
    have himage :
        ambient ∈
          Finset.image
            (selectedParentFinePreimage cover selected).embedding
            Finset.univ := by
      have himage_eq :
          Finset.image
              (selectedParentFinePreimage cover selected).embedding
              Finset.univ =
            selectedParentFinePreimageIndices cover selected := by
        change
          Finset.image
              ((selectedParentFinePreimageIndices cover selected)
                |>.orderEmbOfFin rfl)
              Finset.univ =
            selectedParentFinePreimageIndices cover selected
        exact
          Finset.image_orderEmbOfFin_univ
            (selectedParentFinePreimageIndices cover selected) rfl
      rw [himage_eq]
      exact hmem
    rcases Finset.mem_image.mp himage with ⟨i, _, hi⟩
    refine ⟨i, ?_⟩
    apply selected.embedding.injective
    rw [selectedParentFinePreimageParent_spec]
    rw [hi, hambient]
  nested := by
    intro i
    change
      ((selectedParentFinePreimage cover selected).family.tube i).carrier ⊆
        dilatedTubeCarrier A
          (selected.family.tube
            (selectedParentFinePreimageParent cover selected i))
    rw [(selectedParentFinePreimage cover selected).tube_eq i,
      selected.tube_eq,
      selectedParentFinePreimageParent_spec]
    exact
      cover.nested
        ((selectedParentFinePreimage cover selected).embedding i)

end Kakeya.Streamlined
