import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridAtomizationStatement

/-!
# Finite terminal-grid cover of the Section 7 projection rectangle

The normalized twisted projection is contained in
`[-51,51] × [-1,1]`.  At any positive integer grid scale, the floor index of
every point in this rectangle lies in an explicit finite integer box.  The
corresponding grid center has the same index, so its projected-fiber grid atom
contains the point.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Safe integer-index radius for the fixed Section 7 projection rectangle. -/
def section7GridIndexBound (base levels : ℕ) : ℕ :=
  52 * base ^ levels + 1

/--
The fixed projection rectangle is covered by the terminal grid atoms indexed
by `boundedPlanarGridCenters`.

The theorem is stated for an arbitrary subset `band` of the rectangle because
that is the exact premise consumed by projected-fiber atomization.
-/
def Section7ProjectionRectangleGridCoverStatement : Prop :=
  ∀ base levels : ℕ,
    3 ≤ base →
      ∀ band : Set Point2,
        band ⊆ section7ProjectionRectangle →
          band ⊆
            finiteAtomUnion
              (boundedPlanarGridCenters
                base levels
                (section7GridIndexBound base levels))
              (projectedFiberGridAtom band base levels)

end Kakeya.Assouad
