import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridPartitionTreeStatement
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# Orponen--Shmerkin uniform refinement of tube parameters

This boundary applies the generic local-branching refinement to the actual
four-dimensional supporting-line parameter points of an indexed tube family.
It performs only the initial uniform refinement in the proof of Proposition
7.1; coarse-tube realization and induced shadings are later boundaries.

The active parameter indices are explicit because shadings may vanish on some
indexed tubes.  The input map is required to be injective on the active set;
this is the paper's harmless infinitesimal-perturbation/deduplication step
made explicit rather than silently treating a multiset as a set.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Four-dimensional supporting-line point attached to one tube index. -/
def indexedTubeParameterPoint4
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (index : Fin family.card) : Point 4 :=
  tubeParameterPoint4 (tubeParams index)

/-- The parameter points carried by a finite active index set. -/
def indexedTubeParameterSet4
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (active : Finset (Fin family.card)) :
    DiscreteSet 4 :=
  active.image indexedTubeParameterPoint4

/--
Uniform parameter refinement data.

`selected` is a genuine tube subfamily of the original indexed family.
`selectedParameters` is exactly the image of its ambient indices.  The
branching certificate is stated on the fixed ambient parameter grid tree, so
later selected scales refer to the same cells.
-/
structure TubeParameterOSUniformRefinementData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (active : Finset (Fin family.card))
    (base levels : ℕ) where
  selected : Finset (Fin family.card)
  selected_nonempty : selected.Nonempty
  selected_subset : selected ⊆ active
  selectedParameters : DiscreteSet 4
  selectedParameters_eq :
    selectedParameters =
      selected.image indexedTubeParameterPoint4
  selectedParameters_nonempty : selectedParameters.Nonempty
  cardinality_eq :
    selected.card = selectedParameters.card
  retention :
    (active.card : ℝ) ≤
      (2 * (Nat.log 2 ((base + 1) ^ 4) + 1) : ℝ) ^ levels *
        (selected.card : ℝ)
  branchExponent : Fin levels → ℕ
  branch_bound :
    ∀ level : Fin levels,
      2 ^ branchExponent level ≤ (base + 1) ^ 4
  branch_uniform :
    let ambientParameters := indexedTubeParameterSet4 active
    let P : ℕ → Finset (Finset (Point 4)) :=
      fun level =>
        tubeParameterGridPartition base level ambientParameters
    ∀ level : Fin levels,
      ∀ parent ∈ P level,
        (selectedParameters ∩ parent).Nonempty →
          (occupiedPartitionChildren
            selectedParameters P level parent).card =
              2 ^ branchExponent level

/--
Apply the closed 4D grid tree and generic OS branching theorem to the active
tube parameters.
-/
def TubeParameterOSUniformRefinementStatement : Prop :=
  TubeParameterGridPartitionTreeStatement →
    OSBranchingUniformRefinementStatement →
      ∀ {delta : ℝ},
        ∀ family : Kakeya.Streamlined.TubeFamily delta,
          ∀ active : Finset (Fin family.card),
            active.Nonempty →
            Set.InjOn
              (indexedTubeParameterPoint4 (family := family))
              (active : Set (Fin family.card)) →
            ∀ base levels : ℕ,
              2 ≤ base →
              ∀ fineScale : ℝ,
                0 < fineScale →
                (indexedTubeParameterSet4 active).IsDeltaSeparated
                  fineScale →
                4 < fineScale * (base ^ levels : ℝ) →
                  Nonempty
                    (TubeParameterOSUniformRefinementData
                      active base levels)

end Kakeya.Assouad
