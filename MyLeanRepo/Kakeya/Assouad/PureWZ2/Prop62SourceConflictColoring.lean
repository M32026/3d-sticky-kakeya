import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryLineConflictPacking
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.WeightedGraphSelection

/-!
# Proposition 6.2 preliminary source-conflict color

Before the one augmented-tree cleanup, color the ambient fine tubes by the
frozen `12000000 * delta` line-distance conflict graph.  This color is one
coordinate of the paper's single preliminary dependent color vector.  Hence
every later leaf core is monochromatic for it, without a post-final tube
selection.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62SourceConflictColoringData
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta) where
  color :
    Fin family.card → Fin (pureWZ2OrdinaryLineConflictDegree + 1)
  proper :
    ∀ first second, first ≠ second →
      wz1PaperLineDistance
          (family.tube first) (family.tube second) ≤
        wz2PaperLiteralSourceSeparationFactor * delta →
      color first ≠ color second

theorem pureWZ2_prop62_source_conflict_coloring
    {delta : ℝ}
    (deltaPos : 0 < delta)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (line : WZ1PaperIsLineClass family)
    (boundedBase : HasBoundedBase family 8)
    (distinct : WZ2PaperOrdinaryIsEssentiallyDistinct family) :
    Nonempty (PureWZ2Prop62SourceConflictColoringData family) := by
  let conflict : Fin family.card → Fin family.card → Prop :=
    fun first second =>
      second ≠ first ∧
        wz1PaperLineDistance
            (family.tube second) (family.tube first) ≤
          wz2PaperLiteralSourceSeparationFactor * delta
  have symmetric :
      ∀ first second, conflict first second → conflict second first := by
    intro first second hconflict
    refine ⟨hconflict.1.symm, ?_⟩
    rw [wz1PaperLineDistance_symm]
    exact hconflict.2
  have irreflexive :
      ∀ index, ¬ conflict index index := by
    intro index hconflict
    exact hconflict.1 rfl
  rcases
      pureWZ2_greedy_proper_coloring
        (D := pureWZ2OrdinaryLineConflictDegree)
        symmetric irreflexive
        (fun fixed => by
          rw [Finset.filter_congr_decidable]
          have subset :
              (Finset.univ.filter fun other =>
                conflict fixed other) ⊆
                Finset.univ.filter fun other =>
                  wz1PaperLineDistance
                      (family.tube other) (family.tube fixed) ≤
                    wz2PaperLiteralSourceSeparationFactor * delta := by
            intro other otherMem
            exact
              Finset.mem_filter.mpr
                ⟨Finset.mem_univ other,
                  (Finset.mem_filter.mp otherMem).2.2⟩
          have packing :=
            pureWZ2_ordinary_line_conflict_degree
              deltaPos line boundedBase distinct fixed
          exact (Finset.card_le_card subset).trans packing)
    with ⟨color, proper⟩
  exact
    ⟨{
      color := color
      proper := by
        intro first second indexNe distanceClose
        apply proper first second
        refine ⟨indexNe.symm, ?_⟩
        rw [wz1PaperLineDistance_symm]
        exact distanceClose
    }⟩

namespace PureWZ2Prop62SourceConflictColoringData

variable
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (coloring : PureWZ2Prop62SourceConflictColoringData family)

theorem stronglySeparated_on
    {selected : Finset (Fin family.card)}
    {selectedColor :
      Fin (pureWZ2OrdinaryLineConflictDegree + 1)}
    (monochromatic :
      ∀ index ∈ selected,
        coloring.color index = selectedColor) :
    ∀ first ∈ selected, ∀ second ∈ selected, first ≠ second →
      wz2PaperLiteralSourceSeparationFactor * delta <
        wz1PaperLineDistance
          (family.tube first) (family.tube second) := by
  intro first firstMem second secondMem indexNe
  by_contra notSeparated
  have colorNe :=
    coloring.proper first second indexNe (le_of_not_gt notSeparated)
  exact
    colorNe <|
      (monochromatic first firstMem).trans
        (monochromatic second secondMem).symm

theorem subfamily_stronglySeparated
    (selected : WZ2PaperPureTubeSubfamily family)
    {selectedColor :
      Fin (pureWZ2OrdinaryLineConflictDegree + 1)}
    (monochromatic :
      ∀ source,
        coloring.color (selected.embedding source) = selectedColor) :
    ∀ first second, first ≠ second →
      wz2PaperLiteralSourceSeparationFactor * delta <
        wz1PaperLineDistance
          (selected.family.tube first)
          (selected.family.tube second) := by
  intro first second indexNe
  have ambientNe :
      selected.embedding first ≠ selected.embedding second :=
    selected.embedding.injective.ne indexNe
  have colorNe :=
    coloring.proper
      (selected.embedding first) (selected.embedding second) ambientNe
  rw [selected.tube_eq, selected.tube_eq]
  by_contra notSeparated
  exact
    colorNe (le_of_not_gt notSeparated) <|
      (monochromatic first).trans (monochromatic second).symm

end PureWZ2Prop62SourceConflictColoringData

end Kakeya.Assouad

end
