import MyLeanRepo.Kakeya.Integration.CompetitorHierarchyBridge
import MyLeanRepo.Kakeya.Streamlined.DividingScales.BranchPreservingMaximalEDReassignment
import MyLeanRepo.Kakeya.Streamlined.DividingScales.DyadicSupportingLineScaleBracketing
import MyLeanRepo.Kakeya.Streamlined.DividingScales.OccupiedProjectiveSupportingLineTubeRealization
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ProjectiveSupportingLineMidpointContainment
import MyLeanRepo.Kakeya.Streamlined.DividingScales.SurjectiveDilatedCoverComposition.Proof
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.MidpointBound
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.UniversalNonDistinctGeometry.Proof

/-!
# A one-scale supporting-line quotient of the competitor hierarchy

At one exact competitor grid scale, first quotient the occupied raw nodes by
a dyadic supporting-line cell.  Then compress the cell representatives to a
maximal essentially-distinct subfamily and reassign every cell to one of its
conflicting selected representatives.

The fine source family is unchanged.  In particular this construction does
not pay a second fine-family selection loss.  Its parent map is the explicit
composition

`source -> raw occupied node -> supporting-line cell -> ED representative`.

The first geometric cover has fixed dilation `67`: occupied raw nodes have
midpoint norm at most `3`, because every one contains a source tube in the
unit ball, and the bounded-midpoint supporting-line calculation gives
`13 + 18 * 3 = 67`.  The maximal-ED reassignment costs the support-free
dilation `1000`; their honest transitive composition is `140407`.
-/

noncomputable section

open scoped Classical

namespace Kakeya.Integration

open Kakeya.Streamlined
open Kakeya.Streamlined.GeometricLemmas

/-- Fixed dilation from an occupied raw node to its supporting-line cell. -/
def competitorSupportingLineCellDilation : ℝ := 67

/-- Fixed dilation after also merging cells to maximal ED representatives. -/
def competitorSupportingLineQuotientDilation : ℝ :=
  composedDilatedCoverDilation competitorSupportingLineCellDilation 1000

@[simp] theorem competitorSupportingLineQuotientDilation_eq :
    competitorSupportingLineQuotientDilation = 140407 := by
  norm_num [competitorSupportingLineQuotientDilation,
    competitorSupportingLineCellDilation, composedDilatedCoverDilation]

namespace CompetitorStickyInput

variable {delta : NNReal} {ι : Type*} {N : ℕ} {C : NNReal}
  {lambda frostmanConstant : ENNReal} {supportRadius : ℝ}

/--
The closed one-scale quotient package.  The unit-ball premise is kept at the
constructor boundary rather than added to `CompetitorStickyInput`: it comes
from the public Sticky theorem at its call site.
-/
structure OneScaleSupportingLineQuotientPackage
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (hN : 0 < N) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsourceBall : input.source.IsInUnitBall)
    (k : ℕ) (hk : k ≤ N) where
  grid :
    DyadicSupportingLineGridLevel
      (Tube.gridScale delta N k : ℝ)
  cellCover :
    DilatedTubeCover competitorSupportingLineCellDilation
      (input.levelCoarse k)
      (occupiedProjectiveSupportingLineRepresentativeFamily
        (rho := (Tube.gridScale delta N k : ℝ))
        (input.levelCoarse k) 2 grid.level)
  cellCover_parent :
    ∀ rawParent,
      cellCover.parent rawParent =
        occupiedProjectiveSupportingLineRealizedParent
          (rho := (Tube.gridScale delta N k : ℝ))
          (input.levelCoarse k) 2 grid.level rawParent
  reassignment :
    BranchPreservingMaximalEDPackage
      (occupiedProjectiveSupportingLineRepresentativeFamily
        (rho := (Tube.gridScale delta N k : ℝ))
        (input.levelCoarse k) 2 grid.level)
      (fun _ => Unit)
  quotientCover :
    DilatedTubeCover competitorSupportingLineQuotientDilation
      input.source reassignment.selectedFamily.family
  quotientCover_parent :
    ∀ sourceIndex,
      quotientCover.parent sourceIndex =
        reassignment.representative
          (cellCover.parent (input.levelParent k sourceIndex))

namespace OneScaleSupportingLineQuotientPackage

variable
    {input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius}
    {hN : 0 < N} {hdelta : 0 < delta} {hdeltaOne : delta ≤ 1}
    {hsourceBall : input.source.IsInUnitBall}
    {k : ℕ} {hk : k ≤ N}
    (package :
      input.OneScaleSupportingLineQuotientPackage
        hN hdelta hdeltaOne hsourceBall k hk)

/-- The original occupied hierarchy node of one source tube. -/
def rawParentOfSource (sourceIndex : Fin input.source.card) :
    Fin (input.levelCoarse k).card :=
  input.levelParent k sourceIndex

/-- The supporting-line cell of one occupied raw node. -/
def rawParentToCell (rawParent : Fin (input.levelCoarse k).card) :
    Fin
      (occupiedProjectiveSupportingLineRepresentativeFamily
        (rho := (Tube.gridScale delta N k : ℝ))
        (input.levelCoarse k) 2 package.grid.level).card :=
  package.cellCover.parent rawParent

/-- The selected ED representative of one supporting-line cell. -/
def cellToQuotient
    (cell : Fin
      (occupiedProjectiveSupportingLineRepresentativeFamily
        (rho := (Tube.gridScale delta N k : ℝ))
        (input.levelCoarse k) 2 package.grid.level).card) :
    Fin package.reassignment.selectedFamily.family.card :=
  package.reassignment.representative cell

/-- The selected ED quotient parent of one occupied raw node. -/
def rawParentToQuotient (rawParent : Fin (input.levelCoarse k).card) :
    Fin package.reassignment.selectedFamily.family.card :=
  cellToQuotient package (rawParentToCell package rawParent)

/-- The selected ED quotient parent of one source tube. -/
def quotientParentOfSource (sourceIndex : Fin input.source.card) :
    Fin package.reassignment.selectedFamily.family.card :=
  package.quotientCover.parent sourceIndex

/-- The public name of the one-scale ED quotient family. -/
abbrev quotientCoarse :
    Kakeya.Streamlined.TubeFamily (Tube.gridScale delta N k : ℝ) :=
  package.reassignment.selectedFamily.family

/-- The quotient family is genuinely pairwise essentially distinct. -/
theorem quotientCoarse_essentiallyDistinct :
    (quotientCoarse package).IsEssentiallyDistinct :=
  BranchPreservingMaximalEDPackage.selectedFamily_essentiallyDistinct
    package.reassignment

/-- Exact source/raw/quotient parent compatibility. -/
theorem rawParentToQuotient_rawParentOfSource
    (sourceIndex : Fin input.source.card) :
    rawParentToQuotient package
        (rawParentOfSource (input := input) (k := k) sourceIndex) =
      quotientParentOfSource package sourceIndex := by
  change
    package.reassignment.representative
        (package.cellCover.parent (input.levelParent k sourceIndex)) =
      package.quotientCover.parent sourceIndex
  exact (package.quotientCover_parent sourceIndex).symm

/-- Raw occupied nodes assigned to one selected quotient parent. -/
def rawParentsInQuotient
    (quotientParent :
      Fin package.reassignment.selectedFamily.family.card) :
    Finset (Fin (input.levelCoarse k).card) :=
  Finset.univ.filter fun rawParent =>
    rawParentToQuotient package rawParent = quotientParent

/--
The quotient assigned fiber is exactly the union of the original raw
assigned classes mapped to that quotient parent.  This is an equality of
source occurrences, not merely a cardinality comparison.
-/
theorem quotient_fiberIndices_eq_biUnion_raw_fibers
    (quotientParent :
      Fin package.reassignment.selectedFamily.family.card) :
    package.quotientCover.toFactoring.fiberIndices quotientParent =
      (rawParentsInQuotient package quotientParent).biUnion fun rawParent =>
        (input.levelStrictCover hk).toFactoring.fiberIndices rawParent := by
  ext sourceIndex
  simp only [Factoring.fiberIndices, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_biUnion]
  constructor
  · intro hsource
    refine ⟨input.levelParent k sourceIndex, ?_, ?_⟩
    · simp only [rawParentsInQuotient, Finset.mem_filter, Finset.mem_univ,
        true_and]
      change
        rawParentToQuotient package (input.levelParent k sourceIndex) =
          quotientParent
      exact
        (rawParentToQuotient_rawParentOfSource package sourceIndex).trans hsource
    · change input.levelParent k sourceIndex = input.levelParent k sourceIndex
      rfl
  · rintro ⟨rawParent, hraw, hsourceRaw⟩
    have hraw' :
        rawParentToQuotient package rawParent = quotientParent := by
      simpa [rawParentsInQuotient] using hraw
    change input.levelParent k sourceIndex = rawParent at hsourceRaw
    change package.quotientCover.parent sourceIndex = quotientParent
    rw [package.quotientCover_parent, hsourceRaw]
    exact hraw'

end OneScaleSupportingLineQuotientPackage

/-- Construct the one-scale quotient without selecting any source tube. -/
theorem exists_oneScaleSupportingLineQuotientPackage
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (hN : 0 < N) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsourceBall : input.source.IsInUnitBall)
    (k : ℕ) (hk : k ≤ N) :
    Nonempty
      (input.OneScaleSupportingLineQuotientPackage
        hN hdelta hdeltaOne hsourceBall k hk) := by
  let rho : ℝ := (Tube.gridScale delta N k : ℝ)
  have hdeltaReal : 0 < (delta : ℝ) := by exact_mod_cast hdelta
  have hrho : 0 < rho := by
    exact_mod_cast Tube.gridScale_pos hdelta N k
  have hrhoOne : rho ≤ 1 := by
    exact_mod_cast Tube.gridScale_le_one hdeltaOne N k
  have hdeltaRho : (delta : ℝ) ≤ rho := by
    exact_mod_cast (show delta ≤ Tube.gridScale delta N k by
      calc
        delta = Tube.gridScale delta N N :=
          (Tube.gridScale_self delta hN).symm
        _ ≤ Tube.gridScale delta N k :=
          Tube.gridScale_antitone hdelta hdeltaOne N hk)
  rcases exists_dyadicSupportingLineGridLevel hrho hrhoOne with ⟨grid⟩
  let raw := input.levelCoarse k
  let cell :=
    occupiedProjectiveSupportingLineRepresentativeFamily
      (rho := rho) raw 2 grid.level
  have hrawMidpoint :
      ∀ rawParent, ‖tubeMidpoint (raw.tube rawParent)‖ ≤ 3 := by
    intro rawParent
    exact coarse_tube_midpoint_bound
      (input.levelStrictCover hk) hsourceBall hrho.le hrhoOne rawParent
  have hcellMidpoint :
      ∀ cellParent, ‖tubeMidpoint (cell.tube cellParent)‖ ≤ 3 := by
    intro cellParent
    let occupiedLabel :=
      (occupiedProjectiveSupportingLineLabelEquiv
        raw 2 grid.level).symm cellParent
    let representative :=
      occupiedProjectiveSupportingLineRepresentative
        raw 2 grid.level occupiedLabel
    change ‖tubeMidpoint (withRadius rho (raw.tube representative))‖ ≤ 3
    simpa only [withRadius_midpoint] using hrawMidpoint representative
  let cellCover :
      DilatedTubeCover competitorSupportingLineCellDilation raw cell :=
    { parent :=
        occupiedProjectiveSupportingLineRealizedParent
          (rho := rho) raw 2 grid.level
      parent_surjective :=
        occupiedProjectiveSupportingLineRealizedParent_surjective
          (rho := rho) raw 2 grid.level
      nested := fun rawParent => by
        let occupiedLabel :=
          tubeProjectiveSupportingLineGridParent raw 2 grid.level rawParent
        let representative :=
          occupiedProjectiveSupportingLineRepresentative
            raw 2 grid.level occupiedLabel
        have hlabel :=
          original_and_supportingLineRepresentative_label_eq
            raw 2 grid.level rawParent
        have hcontained :=
          carrier_subset_dilated_of_supportingLineGridLabel_eq_of_midpoint_bound
            hrho.le hrho hrhoOne le_rfl
            (by norm_num : 1 ≤ 2)
            (dyadicSupportingLine_mesh_le grid)
            (R := (3 : ℝ)) (by norm_num)
            (hrawMidpoint rawParent) (hrawMidpoint representative) hlabel
        norm_num [competitorSupportingLineCellDilation] at hcontained
        simpa only [competitorSupportingLineCellDilation, cell, raw,
          occupiedProjectiveSupportingLineRepresentativeFamily,
          occupiedProjectiveSupportingLineRealizedParent,
          occupiedProjectiveSupportingLineLabelEquiv,
          Equiv.symm_apply_apply, occupiedLabel, representative] using hcontained }
  let reassignment :
      BranchPreservingMaximalEDPackage cell (fun _ => Unit) :=
    Classical.choice <|
      exists_branchPreservingMaximalEDPackage
        cell (fun _ => Unit) (fun _ _ _ => rfl)
  let cellToQuotientCover :
      DilatedTubeCover 1000 cell reassignment.selectedFamily.family :=
    { parent := reassignment.representative
      parent_surjective := reassignment.representative_surjective
      nested := fun cellParent => by
        have hselectedTube :
            reassignment.selectedFamily.family.tube
                (reassignment.representative cellParent) =
              cell.tube
                (reassignment.selectedEmbedding
                  (reassignment.representative cellParent)) :=
          TubeSubfamily.tube_eq _ _
        rw [hselectedTube]
        rcases reassignment.representative_eq_or_conflict cellParent with
          heq | hconflict
        · rw [show
            reassignment.selectedEmbedding
                (reassignment.representative cellParent) = cellParent by
              exact heq]
          exact self_dilated_containment 1000 (by norm_num)
            (cell.tube cellParent)
        · exact
            (universal_non_distinct_geometry
              hrho hrhoOne
              (cell.tube cellParent)
              (cell.tube
                (reassignment.selectedEmbedding
                  (reassignment.representative cellParent)))
              hconflict).2.2 }
  let quotientCover :
      DilatedTubeCover competitorSupportingLineQuotientDilation
        input.source reassignment.selectedFamily.family :=
    { parent := fun sourceIndex =>
        reassignment.representative
          (cellCover.parent (input.levelParent k sourceIndex))
      parent_surjective :=
        reassignment.representative_surjective.comp
          (cellCover.parent_surjective.comp
            (input.levelParent_surjective k))
      nested := fun sourceIndex => by
        let rawParent := input.levelParent k sourceIndex
        let cellParent := cellCover.parent rawParent
        have hsourceCell :
            (input.source.tube sourceIndex).carrier ⊆
              dilatedTubeCarrier competitorSupportingLineCellDilation
                (cell.tube cellParent) :=
          (input.source_carrier_subset_assigned_node hk sourceIndex).trans
            (cellCover.nested rawParent)
        have hcellQuotient := cellToQuotientCover.nested cellParent
        simpa only [competitorSupportingLineQuotientDilation,
          composedDilatedCoverDilation,
          rawParent, cellParent] using
          dilated_containment_transitive
            (A := competitorSupportingLineCellDilation) (E := (1000 : ℝ))
            (by norm_num [competitorSupportingLineCellDilation])
            (by norm_num) hdeltaReal hdeltaRho hrho le_rfl hrho hrhoOne
            (input.source.tube sourceIndex) (cell.tube cellParent)
            (reassignment.selectedFamily.family.tube
              (reassignment.representative cellParent))
            (hsourceBall sourceIndex) hsourceCell hcellQuotient }
  exact ⟨{
    grid := grid
    cellCover := cellCover
    cellCover_parent := fun _ => rfl
    reassignment := reassignment
    quotientCover := quotientCover
    quotientCover_parent := fun _ => rfl
  }⟩

end CompetitorStickyInput
end Kakeya.Integration

end
