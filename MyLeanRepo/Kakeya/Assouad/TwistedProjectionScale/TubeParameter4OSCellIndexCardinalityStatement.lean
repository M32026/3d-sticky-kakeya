import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingCellCardinalityStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameter4OSFiberLiftStatement

/-!
# Indexed tube cardinality in OS-uniform four-parameter cells

The generic OS consequence counts distinct retained parameter points in one
occupied cell.  Section 7 needs the number of indexed tubes in that cell.
The complete-fiber lift gives every retained point between `m` and `2m`
indices, so same-level indexed cell counts are comparable by a factor two.
-/

noncomputable section

namespace Kakeya.Assouad

/--
At every grid level, all occupied cells of an OS-uniform complete-fiber lift
contain comparable numbers of selected indexed tubes.
-/
def TubeParameter4OSCellIndexCardinalityStatement : Prop :=
  OSBranchingCellCardinalityStatement →
    ∀ {delta : ℝ},
      ∀ family : Kakeya.Streamlined.TubeFamily delta,
        ∀ active : Finset (Fin family.card),
          ∀ regularized :
              TubeParameter4FiberRegularizationData family active,
            ∀ base levels : ℕ,
              2 ≤ base →
              ∀ fineScale : ℝ,
                0 < fineScale →
                (indexedTubeParameterSet4
                    regularized.selected).IsDeltaSeparated
                  fineScale →
                4 < fineScale * (base ^ levels : ℝ) →
              ∀ uniform :
                  TubeParameter4OSFiberLiftData
                    regularized base levels,
                let ambientParameters :=
                  indexedTubeParameterSet4 regularized.selected
                let partition : ℕ → Finset (Finset (Point 4)) :=
                  fun level =>
                    tubeParameterGridPartition
                      base level ambientParameters
                ∀ level : ℕ, level ≤ levels →
                  ∃ cellCard : ℕ,
                    0 < cellCard ∧
                      ∀ cell ∈ partition level,
                        (uniform.selectedParameters ∩ cell).Nonempty →
                          cellCard ≤
                            (uniform.selected.filter fun index =>
                              indexedTubeParameterPoint4 index ∈ cell).card ∧
                          (uniform.selected.filter fun index =>
                              indexedTubeParameterPoint4 index ∈ cell).card <
                            2 * cellCard

end Kakeya.Assouad
