import MyLeanRepo.Kakeya.Streamlined.DividingScales.OccupiedProjectiveSupportingLineTubeRealization
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ProjectiveSupportingLineConflictBounds
import MyLeanRepo.Kakeya.Streamlined.DividingScales.SelectedParentFinePreimage
import MyLeanRepo.Kakeya.Streamlined.DividingScales.PeriodicIntegerGridColoring
import MyLeanRepo.Kakeya.Streamlined.DilatedCoverUniformization

/-!
# Periodic essentially-distinct selection of supporting-line parents

At one scale, the occupied supporting-line grid gives a surjective candidate
`LocalDilatedTubeCover 31 21`.  If one fixed residue modulus dominates the
non-essential-distinctness coordinate range, a heavy periodic color class is
pairwise essentially distinct.

The parent weight is its complete fine-fiber cardinality.  Restricting to the
selected parents and their full fine preimage therefore retains at least the
reciprocal `modulus^12` share of the original fine cardinality while
preserving parent surjectivity and all local-cover geometry.
-/

noncomputable section

namespace Kakeya.Streamlined

open scoped Classical
open GeometricLemmas

/-- Closed one-scale output of periodic supporting-line ED selection. -/
structure PeriodicSupportingLineEDSelectionPackage
    {delta rho : ℝ}
    (family : TubeFamily delta)
    (base level modulus : ℕ)
    (candidate :
      LocalDilatedTubeCover 31 21 family
        (occupiedProjectiveSupportingLineRepresentativeFamily
          (rho := rho) family base level)) where
  selectedParents :
    Finset (Fin
      (occupiedProjectiveSupportingLineRepresentativeFamily
        (rho := rho) family base level).card)
  selectedCoarse :
    TubeSubfamily
      (occupiedProjectiveSupportingLineRepresentativeFamily
        (rho := rho) family base level)
  selectedCoarse_eq :
    selectedCoarse =
      TubeSubfamily.fromFinset _ selectedParents
  selectedFine :
    TubeSubfamily family
  selectedFine_eq :
    selectedFine =
      selectedParentFinePreimage
        candidate.toDilatedTubeCover selectedCoarse
  restrictedCover :
    LocalDilatedTubeCover 31 21
      selectedFine.family selectedCoarse.family
  coarseEssentiallyDistinct :
    selectedCoarse.family.IsEssentiallyDistinct
  fullPreimage :
    ∀ index : Fin family.card,
      index ∈ Finset.image selectedFine.embedding Finset.univ ↔
        candidate.parent index ∈ selectedParents
  fineCardinalityRetention :
    family.enncard ≤
      (modulus ^ 12 : ℕ) * selectedFine.family.enncard

/-- The periodic one-level label of one candidate parent. -/
def supportingLinePeriodicColor
    {delta rho : ℝ}
    (family : TubeFamily delta)
    (base level modulus : ℕ)
    (hmodulus : 0 < modulus)
    (parentIndex :
      Fin
        (occupiedProjectiveSupportingLineRepresentativeFamily
          (rho := rho) family base level).card) :
    Fin 1 → Fin 12 → Fin modulus :=
  periodicIntegerGridColor modulus hmodulus
    (fun _ =>
      integerGridLabel base level
        (projectiveSupportingLineCoordinates
          ((occupiedProjectiveSupportingLineRepresentativeFamily
            (rho := rho) family base level).tube parentIndex)))

/--
One periodic color class yields essentially-distinct parents and its complete
fine preimage, with exact `modulus^12` cardinality loss.
-/
theorem exists_periodicSupportingLineEDSelection
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    (family : TubeFamily delta)
    (hfamilyBall : family.IsInUnitBall)
    (base level modulus : ℕ)
    (hbase : 1 ≤ base)
    (hmeshRho : (base ^ level : ℝ)⁻¹ ≤ rho)
    (hmodulus : 0 < modulus)
    (hconflictRange :
      (3000 * rho) * (base ^ level : ℝ) + 1 <
        (modulus : ℝ)) :
    Nonempty
      (PeriodicSupportingLineEDSelectionPackage
        family base level modulus
        (occupiedProjectiveSupportingLineLocalCover
          hdelta hrho hrhoOne hdeltaRho family hfamilyBall
          base level hbase hmeshRho)) := by
  let coarse :=
    occupiedProjectiveSupportingLineRepresentativeFamily
      (rho := rho) family base level
  let candidate :
      LocalDilatedTubeCover 31 21 family coarse :=
    occupiedProjectiveSupportingLineLocalCover
      hdelta hrho hrhoOne hdeltaRho family hfamilyBall
      base level hbase hmeshRho
  let label : Fin coarse.card → Fin 1 → Fin 12 → ℤ :=
    fun parentIndex _ =>
      integerGridLabel base level
        (projectiveSupportingLineCoordinates
          (coarse.tube parentIndex))
  have hlabelInjective : Function.Injective label := by
    intro first second hlabel
    apply
      occupiedProjectiveSupportingLineRepresentativeFamily_gridLabel_injective
        family base level
    exact congrFun hlabel 0
  let conflict : Fin coarse.card → Fin coarse.card → Prop :=
    fun first second =>
      ¬(coarse.tube first).EssentiallyDistinct
        (coarse.tube second)
  have hconflict :
      ∀ first second,
        conflict first second →
        ∀ gridLevel coordinate,
          |label first gridLevel coordinate -
              label second gridLevel coordinate| <
            (modulus : ℤ) := by
    intro first second hfirstSecond _gridLevel coordinate
    apply
      projectiveSupportingLineGridLabel_abs_sub_lt_of_not_essentiallyDistinct
        hrho hrhoOne
        (occupiedProjectiveSupportingLineRepresentativeFamily_midpoint_norm_le_one
          family hfamilyBall base level first)
        hfirstSecond hconflictRange coordinate
  let weight : Fin coarse.card → ENNReal :=
    candidate.toDilatedTubeCover.toFactoring.fiberCount
  rcases
      exists_heavy_periodicIntegerGridColor_class
        hmodulus
        (Finset.univ : Finset (Fin coarse.card))
        label hlabelInjective weight conflict hconflict with
    ⟨selectedParents, _hsubset, hfree, hweight⟩
  let selectedCoarse : TubeSubfamily coarse :=
    TubeSubfamily.fromFinset coarse selectedParents
  let selectedFine : TubeSubfamily family :=
    selectedParentFinePreimage
      candidate.toDilatedTubeCover selectedCoarse
  let restrictedCover :
      LocalDilatedTubeCover 31 21
        selectedFine.family selectedCoarse.family :=
    {
      toDilatedTubeCover :=
        selectedParentFinePreimageCover
          candidate.toDilatedTubeCover selectedCoarse
      transverse_midpoint_close := by
        intro index
        have hparent :
            selectedCoarse.embedding
                ((selectedParentFinePreimageCover
                  candidate.toDilatedTubeCover selectedCoarse).parent index) =
              candidate.parent (selectedFine.embedding index) := by
          change
            selectedCoarse.embedding
                (selectedParentFinePreimageParent
                  candidate.toDilatedTubeCover selectedCoarse index) =
              candidate.parent
                ((selectedParentFinePreimage
                  candidate.toDilatedTubeCover selectedCoarse).embedding index)
          exact
            selectedParentFinePreimageParent_spec
              candidate.toDilatedTubeCover selectedCoarse index
        rw [selectedFine.tube_eq index, selectedCoarse.tube_eq]
        rw [hparent]
        exact
          candidate.transverse_midpoint_close
            (selectedFine.embedding index)
      direction_close_or_reverse := by
        intro index
        have hparent :
            selectedCoarse.embedding
                ((selectedParentFinePreimageCover
                  candidate.toDilatedTubeCover selectedCoarse).parent index) =
              candidate.parent (selectedFine.embedding index) := by
          change
            selectedCoarse.embedding
                (selectedParentFinePreimageParent
                  candidate.toDilatedTubeCover selectedCoarse index) =
              candidate.parent
                ((selectedParentFinePreimage
                  candidate.toDilatedTubeCover selectedCoarse).embedding index)
          exact
            selectedParentFinePreimageParent_spec
              candidate.toDilatedTubeCover selectedCoarse index
        rw [selectedFine.tube_eq index, selectedCoarse.tube_eq]
        rw [hparent]
        exact
          candidate.direction_close_or_reverse
            (selectedFine.embedding index)
    }
  have hcoarseED :
      selectedCoarse.family.IsEssentiallyDistinct := by
    intro first second hne
    let ambientFirst := selectedCoarse.embedding first
    let ambientSecond := selectedCoarse.embedding second
    have hfirstMem :
        ambientFirst ∈ selectedParents :=
      Finset.orderEmbOfFin_mem selectedParents rfl first
    have hsecondMem :
        ambientSecond ∈ selectedParents :=
      Finset.orderEmbOfFin_mem selectedParents rfl second
    have hambientNe : ambientFirst ≠ ambientSecond := by
      intro heq
      exact hne (selectedCoarse.embedding.injective heq)
    have hnotConflict :=
      hfree ambientFirst hfirstMem
        ambientSecond hsecondMem hambientNe
    rw [selectedCoarse.tube_eq first,
      selectedCoarse.tube_eq second]
    exact Classical.byContradiction fun hconflict =>
      hnotConflict hconflict
  have hfull :
      ∀ index : Fin family.card,
        index ∈ Finset.image selectedFine.embedding Finset.univ ↔
          candidate.parent index ∈ selectedParents := by
    intro index
    have himage :
        Finset.image selectedCoarse.embedding Finset.univ =
          selectedParents :=
      Finset.image_orderEmbOfFin_univ selectedParents rfl
    change
      index ∈
          Finset.image selectedFine.embedding Finset.univ ↔
        candidate.parent index ∈ selectedParents
    rw [show
      Finset.image selectedFine.embedding Finset.univ =
        selectedParentFinePreimageIndices
          candidate.toDilatedTubeCover selectedCoarse by
            change
              Finset.image
                  (selectedParentFinePreimageIndices
                    candidate.toDilatedTubeCover selectedCoarse
                    |>.orderEmbOfFin rfl)
                  Finset.univ =
                selectedParentFinePreimageIndices
                  candidate.toDilatedTubeCover selectedCoarse
            exact
              Finset.image_orderEmbOfFin_univ
                (selectedParentFinePreimageIndices
                  candidate.toDilatedTubeCover selectedCoarse) rfl]
    have hparentIff :
        candidate.parent index ∈
            Finset.image selectedCoarse.embedding Finset.univ ↔
          candidate.parent index ∈ selectedParents := by
      rw [himage]
    unfold selectedParentFinePreimageIndices
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hparentIff
  have hselectedFineCard :
      selectedFine.family.enncard =
        ∑ parent ∈ selectedParents,
          candidate.toDilatedTubeCover.toFactoring.fiberCount parent := by
    change
      ((selectedParentFinePreimageIndices
        candidate.toDilatedTubeCover selectedCoarse).card : ENNReal) =
        ∑ parent ∈ selectedParents,
          candidate.toDilatedTubeCover.toFactoring.fiberCount parent
    rw [show
      selectedParentFinePreimageIndices
          candidate.toDilatedTubeCover selectedCoarse =
        candidate.toDilatedTubeCover.toFactoring.fiberIndicesOver
          selectedParents by
            ext index
            have hselectedImage :
                index ∈ Finset.image selectedFine.embedding Finset.univ ↔
                  candidate.parent index ∈ selectedParents :=
              hfull index
            have hpreimageImage :
                Finset.image selectedFine.embedding Finset.univ =
                  selectedParentFinePreimageIndices
                    candidate.toDilatedTubeCover selectedCoarse := by
              change
                Finset.image
                    (selectedParentFinePreimageIndices
                      candidate.toDilatedTubeCover selectedCoarse
                      |>.orderEmbOfFin rfl)
                    Finset.univ =
                  selectedParentFinePreimageIndices
                    candidate.toDilatedTubeCover selectedCoarse
              exact
                Finset.image_orderEmbOfFin_univ
                  (selectedParentFinePreimageIndices
                    candidate.toDilatedTubeCover selectedCoarse) rfl
            have hleft :
                index ∈
                    selectedParentFinePreimageIndices
                      candidate.toDilatedTubeCover selectedCoarse ↔
                  candidate.parent index ∈ selectedParents := by
              rw [← hpreimageImage]
              exact hselectedImage
            exact hleft.trans <|
              (candidate.toDilatedTubeCover.toFactoring.mem_fiberIndicesOver_iff
                selectedParents index).symm]
    exact
      candidate.toDilatedTubeCover.toFactoring.fiberIndicesOver_card
        selectedParents
  have htotalWeight :
      ∑ parent : Fin coarse.card, weight parent =
        family.enncard := by
    exact candidate.toDilatedTubeCover.toFactoring.sum_fiberCount
  have hretention :
      family.enncard ≤
        (modulus ^ 12 : ℕ) *
          selectedFine.family.enncard := by
    have hcolors :
        modulus ^ (1 * 12) = modulus ^ 12 := by norm_num
    rw [← htotalWeight, hselectedFineCard]
    simpa [hcolors, weight] using hweight
  exact ⟨{
    selectedParents := selectedParents
    selectedCoarse := selectedCoarse
    selectedCoarse_eq := rfl
    selectedFine := selectedFine
    selectedFine_eq := rfl
    restrictedCover := restrictedCover
    coarseEssentiallyDistinct := hcoarseED
    fullPreimage := hfull
    fineCardinalityRetention := hretention
  }⟩

end Kakeya.Streamlined
