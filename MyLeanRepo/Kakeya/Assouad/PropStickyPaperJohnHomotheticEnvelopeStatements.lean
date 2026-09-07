import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.GeneralInclusionMain
import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Common homothetic envelope from the outer John ellipsoid

This is the convex-geometric leaf needed after unit-scale carrier
homothetic containment.

For a three-dimensional convex body `convexBody`, let `ellipsoid` be its
outer John ellipsoid.  The general John inclusion gives

`homothety center (1 / 3) '' ellipsoid ⊆ convexBody ⊆ ellipsoid`.

Since an ellipsoid is centrally symmetric, every set
`homothety point 100 '' convexBody`, with `point ∈ convexBody`, is contained
in the common set `homothety center 199 '' ellipsoid`.  Its volume is at most

`27 * 199^3 * volume convexBody = 212776173 * volume convexBody`.

The statement exposes only the common-envelope consequence, so downstream
code does not depend on a particular representation of the John ellipsoid.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

def WZ2PaperJohnHomotheticEnvelopeStatement : Prop :=
  ∀ (convexBody : Set Point3),
    ∀ (hbody : JohnEllipsoid.IsConvexBody convexBody),
      ∃ envelope : Set Point3,
        Convex ℝ envelope ∧
        volume envelope ≤
          (212776173 : ENNReal) * volume convexBody ∧
        ∀ point ∈ convexBody,
          AffineMap.homothety point (100 : ℝ) '' convexBody ⊆
            envelope

end Kakeya.Assouad

end
