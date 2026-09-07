import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingUniformRefinementStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameters

/-!
# Four-dimensional tube-parameter grid tree

Paper Proposition 7.1 first makes the tube family uniform across a nested
partition of the four supporting-line parameters `(a,b,c,d)`.  This module
freezes only that Euclidean partition geometry.

At level `k`, parameter points are grouped by

`floor (coordinate * base^k)`, coordinatewise in `R^4`.

The partitions are nested, each parent has at most `(base + 1)^4` children,
and sufficiently fine terminal cells are singletons for a separated parameter
set.  These are exactly the hypotheses consumed by the already closed
`OSBranchingUniformRefinementStatement`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The four supporting-line parameters as one Euclidean point. -/
def tubeParameterPoint4 (params : TubeParams) : Point 4 :=
  WithLp.toLp 2 fun i : Fin 4 =>
    match i with
    | 0 => params.a
    | 1 => params.b
    | 2 => params.c
    | 3 => params.d

/-- Integer index of a `base^(-level)` parameter cell. -/
def tubeParameterGridIndex
    (base level : ℕ) (point : Point 4) : Fin 4 → ℤ :=
  fun coordinate =>
    ⌊point coordinate * (base ^ level : ℝ)⌋

/-- Points of `A` lying in the same parameter cell as `point`. -/
def tubeParameterGridCell
    (base level : ℕ) (A : DiscreteSet 4) (point : Point 4) :
    DiscreteSet 4 :=
  A.filter fun candidate =>
    tubeParameterGridIndex base level candidate =
      tubeParameterGridIndex base level point

/-- Nonempty occupied parameter cells at one level. -/
def tubeParameterGridPartition
    (base level : ℕ) (A : DiscreteSet 4) :
    Finset (DiscreteSet 4) :=
  A.image (tubeParameterGridCell base level A)

/--
The four-dimensional parameter grids form a locally bounded atomic partition
tree.

Points in one terminal cell are at distance strictly below
`4 / base^levels`; hence the strict mesh premise makes each occupied terminal
cell a singleton.
-/
def TubeParameterGridPartitionTreeStatement : Prop :=
  ∀ A : DiscreteSet 4,
    A.Nonempty →
    ∀ base levels : ℕ,
      2 ≤ base →
      ∀ fineScale : ℝ,
        0 < fineScale →
        A.IsDeltaSeparated fineScale →
        4 < fineScale * (base ^ levels : ℝ) →
        let P : ℕ → Finset (Finset (Point 4)) :=
          fun level => tubeParameterGridPartition base level A
        (∀ level ≤ levels,
          (∀ cell ∈ P level, cell.Nonempty ∧ cell ⊆ A) ∧
          (∀ cell₁ ∈ P level, ∀ cell₂ ∈ P level,
            cell₁ ≠ cell₂ → Disjoint cell₁ cell₂) ∧
          A ⊆ Finset.biUnion (P level) id) ∧
        (∀ cell ∈ P levels, cell.card = 1) ∧
        (∀ level, level < levels →
          ∀ child ∈ P (level + 1),
            ∃ parent ∈ P level, child ⊆ parent) ∧
        ∀ level, level < levels →
          ∀ parent ∈ P level,
            (partitionChildren P level parent).card ≤
              (base + 1) ^ 4

end Kakeya.Assouad
