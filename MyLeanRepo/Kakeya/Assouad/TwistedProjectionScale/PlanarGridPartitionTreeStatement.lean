import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingUniformRefinementStatement

/-!
# Nested planar grid partitions with local branching bounds

This is the geometric producer consumed by the Orponen--Shmerkin branching
uniformization.  At level `k`, points are grouped by the integer pair
`(floor (x * base^k), floor (y * base^k))`.

The partitions are nested.  Each parent has at most `(base + 1)^2` children,
independently of the total number of occupied cells.  At a sufficiently fine
terminal mesh, separation of the input point set makes every occupied
terminal cell a singleton.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Integer index of the planar `base^(-level)` grid cell containing `p`. -/
def planarGridIndex
    (base level : ℕ) (p : Point2) : ℤ × ℤ :=
  (⌊p 0 * (base ^ level : ℝ)⌋,
    ⌊p 1 * (base ^ level : ℝ)⌋)

/-- The points of `A` in the same planar grid cell as `p`. -/
def planarGridCell
    (base level : ℕ) (A : DiscreteSet 2) (p : Point2) :
    DiscreteSet 2 :=
  A.filter fun q => planarGridIndex base level q =
    planarGridIndex base level p

/-- The nonempty occupied planar grid cells at one level. -/
def planarGridPartition
    (base level : ℕ) (A : DiscreteSet 2) :
    Finset (DiscreteSet 2) :=
  A.image (planarGridCell base level A)

/--
The floor-grid partitions form a locally bounded atomic tree.

The mesh premise is deliberately strict.  Points in one terminal grid cell
have Euclidean distance strictly below `2 / base^levels`; hence a
`fineScale`-separated set has singleton terminal cells when
`2 < fineScale * base^levels`.
-/
def PlanarGridPartitionTreeStatement : Prop :=
  ∀ A : DiscreteSet 2,
    A.Nonempty →
    ∀ base levels : ℕ,
      2 ≤ base →
      ∀ fineScale : ℝ,
        0 < fineScale →
        A.IsDeltaSeparated fineScale →
        2 < fineScale * (base ^ levels : ℝ) →
        let P : ℕ → Finset (Finset Point2) :=
          fun level => planarGridPartition base level A
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
              (base + 1) ^ 2

end Kakeya.Assouad
