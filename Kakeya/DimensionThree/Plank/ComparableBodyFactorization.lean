/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.KatzTao
public import Kakeya.DimensionThree.Prism
public import Kakeya.DimensionThree.Plank.TubeParentPacking
public import Kakeya.DimensionThree.Plank.Factorization

/-!
# Section 6: the comparable-body interface

Two definitions used throughout Section 6 to keep the *actual* body on which GWZ Proposition 5.1
factors the fine tube family apart from the exact Lean `Plank` handed to GWZ Lemma 6.4.

Conflating them is a normalisation bug.  `Plank a b = Prism3D a b 1` and `Prism3D` records
half-widths, so an exact Lean plank has longitudinal **extent 2**, whereas a `Tube ρ` is the
`ρ`-neighbourhood of a **unit** segment and so has diameter at most `1 + 2ρ`.  An exact plank inside
a coarse `ρ`-tube therefore forces `1/2 ≤ ρ` (`Kakeya.Plank.half_le_of_le_tube`), which made the
hypotheses of Proposition 6.6(A) unsatisfiable at every small scale.  The paper asks only for
dimensions *comparable* to `a × b × 1`, and the factorisation's actual outer bodies — convex hulls
of fine tubes lying in one coarse tube — have longitudinal extent `≈ 1`, matching the leaves.

`Kakeya.ContainsFlatDisc` isolates the one half of plank comparability that the Scale comparison
consumes, in a normalisation-free form, and `Kakeya.ComparableBodyFactorization` is the resulting
replacement for `Kakeya.PlankFactorization` in Proposition 6.6(A)'s hypotheses.  The geometry about
them — that every `Prism3D` supplies a flat disc, and that a flat disc inside a `ρ`-tube forces
`b ≤ ρ` — lives in `Kakeya/DimensionThree/Plank/LocalFactorizationGeometry.lean`.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Kakeya

open ConvexSpaceBody

-- `Kakeya.ContainsFlatDisc` is defined in `Kakeya/DimensionThree/Plank/Factorization.lean`;
-- this file reuses that single definition rather than duplicating it.

/-- **The Section-6-local factorisation datum.**

The Section-6 replacement for `Kakeya.PlankFactorization` in Proposition 6.6(A)'s hypotheses.  It
carries the *actual* outer bodies of the local factorisation and requires them only to be
*comparable* to `a × b × 1` planks, never equal to them:

* `le_body` and `body_le` say that `body x` is the convex hull of the fine bodies it collects —
  `body_le` is the minimality half, which is what puts an outer body inside its coarse parent;
* `wide` is the transverse *lower* bound, the surviving half of plank comparability;
* `isKatzTao` is the Katz--Tao property of the outer family, retained verbatim.

What is deliberately absent is `parts_are_planks`.  With that equality the outer body was an exact
`Prism3D a b 1` of longitudinal extent `2`, which cannot fit inside a `ρ`-tube of diameter
`1 + 2ρ` unless `1/2 ≤ ρ`; the hypotheses of Proposition 6.6(A) were therefore unsatisfiable for
small `ρ`.  With only `wide` the outer body may have longitudinal extent `≈ 1`, matching the fine
leaves, and the whole configuration is available at every scale.

The disc radius is `min b (1/2)` rather than `b` so that the datum stays faithful when `b > 1/2`:
an extent-`1` body of transverse half-widths `a ≤ b` contains a flat disc of radius `b` only while
`b ≤ 1/2`.  The Scale comparison then returns `b ≤ 2 * ρ`
(`Kakeya.b_le_two_mul_of_comparableBodyFactorization`), with the absolute constant `2`. -/
structure ComparableBodyFactorization (b : ℝ≥0) {ι : Type*} (s : Finset ι)
    (Tb : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (C₀ : ℝ≥0) where
  /-- Index type of the outer cells. -/
  Cell : Type
  /-- The outer cells actually used. -/
  cells : Finset Cell
  /-- The *actual* outer body of a cell. -/
  body : Cell → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))
  /-- The cell collecting each fine body. -/
  cellOf : ι → Cell
  /-- Every fine index is collected by a cell in use. -/
  cellOf_mem : ∀ i ∈ s, cellOf i ∈ cells
  /-- Every fine body lies in the body of its cell. -/
  le_body : ∀ i ∈ s, Tb i ≤ body (cellOf i)
  /-- Minimality of the outer body: it is contained in every convex body containing the fine bodies
  it collects.  The convex hull satisfies this, and it is what places an outer body inside its
  coarse parent tube. -/
  body_le : ∀ x ∈ cells, ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
    (∀ i ∈ s, cellOf i = x → Tb i ≤ K) → body x ≤ K
  /-- Transverse lower bound: each outer body contains a flat disc of radius `min b (1/2)`. -/
  wide : ∀ x ∈ cells, ContainsFlatDisc (min b (1 / 2)) (body x).carrier
  /-- The outer family is Katz--Tao with constant `C₀`. -/
  isKatzTao : IsKatzTao cells body (C₀ : ENNReal)

end Kakeya

end

end
