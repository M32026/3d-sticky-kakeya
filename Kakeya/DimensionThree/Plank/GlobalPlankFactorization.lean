/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.PrismGeometry
public import Kakeya.DimensionThree.Plank.FrostmanPlankEstimate
public import Kakeya.DimensionThree.Plank.ComparableBodyFactorization

/-!
# Section 6: the *global* factorisation datum of GWZ Proposition 6.6(B)

Proposition 6.6(B) factors the **coarse `ρ`-tube family** by a *single* family of `a × b × 1`
planks, so its geometry is the mirror image of Proposition 6.6(A)'s: there the outer bodies sat
*inside* a coarse `ρ`-tube, here the coarse `ρ`-tubes sit *inside* the outer bodies.  The two
consequences of that reversal are proved here.

## The scale relation `ρ ≤ a` is forced, not assumed

A `ρ`-tube contains a ball of radius `ρ`, and the least width of an `a × b × 1` plank is `a`, so a
`ρ`-tube inside such a plank forces `ρ ≤ a` (`Kakeya.Tube.rho_le_of_le_prism3D`,
`Kakeya.GlobalComparableBodyFactorization.rho_le`).  This is the exact opposite of Proposition 6.6(A),
where the derived relation is `b ≤ 2ρ` (`Kakeya.b_le_two_mul_of_comparableBodyFactorization`) and `ρ ≤ a`
is *false*.  Proposition 6.6(B) therefore keeps `ρ ≤ a`: it is part of the paper's hypothesis
`δ ≤ ρ ≲ a ≤ b ≤ 1` and it is implied by the factorisation datum itself.

## The exact `parts_are_planks` equality is still unsatisfiable — for a new reason

`Kakeya.PlankFactorization` demands that each outer body be *equal* to an exact `Prism3D a b 1`.
In Proposition 6.6(A) that equality forced `1/2 ≤ ρ` through the longitudinal normalisation
(`Kakeya.Plank.half_le_of_le_tube`).  That longitudinal obstruction is absent here — a unit-length
`ρ`-tube fits comfortably inside a body of longitudinal extent `2` — but a different and equally
fatal one appears: an outer body is the convex hull of a union of `ρ`-tubes, i.e. of *round*
capsules, and a box vertex can never be produced by such a hull.  Indeed the vertex is an extreme
point, so it must already lie in one of the capsules, whose inscribed ball of radius `ρ` would then
have to fit into the box corner; comparing the two transverse coordinates gives `√2 ρ ≤ ρ`.  Hence
`ρ = 0` (`Kakeya.Prism3D.ne_convexHull_biUnion_tubes`,
`Kakeya.not_plankFactorization_tubes_of_pos`), and the hypotheses of Proposition 6.6(B) in the
`PlankFactorization` form were unsatisfiable at every positive scale.

`Kakeya.GlobalComparableBodyFactorization` is the replacement.  It keeps the hull structure and the
Katz--Tao property and demands only *comparability* with an `a × b × 1` plank: containment in one
(the half the Scale comparison consumes) together with the normalisation-free transverse lower bound
`Kakeya.ContainsFlatDisc` (the half that keeps the eccentricity gain `(a/b) ^ β` honest).  It is
deliberately *not* `Kakeya.ComparableBodyFactorization`: part (A)'s datum records a transverse lower bound
and no containment, because there the containment is supplied by the coarse parent, whereas here the
containment is the whole point.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal Classical

noncomputable section

namespace Kakeya

/-! ### Additional estimates

On the source branch this file also carried the `Prism3D`/`Tube` corner-obstruction geometry and
the comparable-fibre counting lemmas.  Both groups are already in this development, in
`Kakeya/DimensionThree/Plank/PrismGeometry.lean`, so they are not duplicated here; only the three
declarations below are new.
-/

/-- **Proposition 6.6(B) in the `PlankFactorization` form is unsatisfiable.**  A
`Kakeya.PlankFactorization` of a nonempty family of `ρ`-tubes with `0 < ρ` cannot exist: each part
of the underlying `Finpartition` is nonempty, so its outer body is the convex hull of a nonempty
union of `ρ`-tubes, and `Kakeya.Prism3D.ne_convexHull_biUnion_tubes` forbids that body from being an
exact `a × b × 1` plank.

Since Proposition 6.6(B) assumes `δ ≤ ρ` with `0 < δ`, this is exactly the statement that its old
hypotheses were vacuous. -/
theorem not_plankFactorization_tubes_of_pos {κ : Type*} [DecidableEq κ] {a b ρ C₀ : ℝ≥0}
    {hab : a ≤ b} {hb1 : b ≤ 1} (hρ : 0 < ρ) {r : Finset κ} (hr : r.Nonempty)
    (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (Fz : PlankFactorization a b hab hb1 r (fun k => (R k).toConvexSpaceBody) C₀) : False := by
  obtain ⟨t, ht⟩ := Fz.parts_nonempty (Finset.nonempty_iff_ne_empty.mp hr)
  have htne : t.Nonempty := Fz.nonempty_of_mem_parts ht
  rcases Fz.parts_are_planks t ht with ⟨Q, hQ⟩
  exact (Prism3D.ne_convexHull_biUnion_tubes (c := 1) hρ htne R Q) hQ

/-! ### The Part-(B) factorisation datum -/

/-- **The global (Part-(B)) factorisation datum.**

The Proposition 6.6(B) replacement for `Kakeya.PlankFactorization`.  A *single* family of outer
cells factors the whole coarse family `Tb` (in the application, the `ρ`-tube family), and the outer
bodies are only required to be *comparable* to `a × b × 1` planks:

* `le_body` and `body_le` say that `body x` behaves like the convex hull of the coarse bodies it
  collects — `le_body` is the containment half, which is what puts a `ρ`-tube inside its outer
  plank, and `body_le` is the minimality half;
* `le_plank` is the transverse *upper* bound: the outer body fits inside an exact `a × b × 1` plank.
  This is the half the Scale comparison consumes, and it yields `ρ ≤ a`
  (`Kakeya.GlobalComparableBodyFactorization.rho_le`);
* `wide` is the normalisation-free transverse *lower* bound, so that the outer bodies really have
  the eccentricity `a/b` that the conclusion's gain `(a/b) ^ β` is paid for;
* `isKatzTao` is the Katz--Tao property of the outer family, which is what licenses the `γ = 0`
  application of GWZ Lemma 6.1 to the outer family (`Kakeya.gammaZeroSlabBound`).

What is deliberately absent is `Kakeya.PlankFactorization.parts_are_planks`.  With that equality an
outer body would be an exact box, whose vertex cannot be produced by a convex hull of `ρ`-tubes:
`Kakeya.not_plankFactorization_tubes_of_pos` shows the hypothesis then forces `ρ = 0`.  Containment
in a plank has no such defect.

The disc radius in `wide` is `min b (1/2)`, as in `Kakeya.ComparableBodyFactorization`, so that the datum
stays satisfiable when `b > 1/2`: a body of longitudinal extent `≈ 1` and transverse half-widths
`a ≤ b` contains a flat disc of radius `b` only while `b ≤ 1/2`.

No longitudinal lower bound is imposed: a cell in `cells` collects at least one coarse body (else
`body_le` applied to a small `K` fails), and a `ρ`-tube already has diameter `≥ 1`, so longitudinal
extent `≈ 1` is a consequence of `le_body` rather than an extra demand. -/
structure GlobalComparableBodyFactorization (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    {ι : Type*} (s : Finset ι)
    (Tb : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (C₀ : ℝ≥0) where
  /-- Index type of the outer cells. -/
  Cell : Type
  /-- The outer cells actually used. -/
  cells : Finset Cell
  /-- The *actual* outer body of a cell. -/
  body : Cell → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))
  /-- The cell collecting each coarse body. -/
  cellOf : ι → Cell
  /-- Every coarse index is collected by a cell in use. -/
  cellOf_mem : ∀ i ∈ s, cellOf i ∈ cells
  /-- Every coarse body lies in the body of its cell. -/
  le_body : ∀ i ∈ s, Tb i ≤ body (cellOf i)
  /-- Minimality of the outer body: it is contained in every convex body containing the coarse
  bodies it collects. -/
  body_le : ∀ x ∈ cells, ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
    (∀ i ∈ s, cellOf i = x → Tb i ≤ K) → body x ≤ K
  /-- Transverse upper bound: each outer body fits in an `a × b × 1` plank. -/
  le_plank : ∀ x ∈ cells, ∃ Q : Plank a b hab hb1, body x ≤ Q.toConvexSpaceBody
  /-- Transverse lower bound: each outer body contains a flat disc of radius `min b (1/2)`. -/
  wide : ∀ x ∈ cells, ContainsFlatDisc (min b (1 / 2)) (body x).carrier
  /-- The outer family is Katz--Tao with constant `C₀`. -/
  isKatzTao : IsKatzTao cells body (C₀ : ENNReal)

/-- **The scale relation of GWZ Proposition 6.6(B), derived from its own data.**

If a global factorisation collects a nonempty family of `ρ`-tubes, then `ρ ≤ a`: the tube sits in
the body of its cell, which sits in an `a × b × 1` plank, and a `ρ`-tube inside such a plank forces
`ρ ≤ a` (`Kakeya.Tube.rho_le_of_le_prism3D`).

So Proposition 6.6(B)'s hypothesis `ρ ≤ a` is not an extra assumption but a consequence of the
factorisation datum — the exact opposite of Proposition 6.6(A), where `ρ ≤ a` is inconsistent with
the local factorisation and `b ≤ 2ρ` is what is derived. -/
theorem GlobalComparableBodyFactorization.rho_le {κ : Type*} {a b ρ C₀ : ℝ≥0}
    {hab : a ≤ b} {hb1 : b ≤ 1} {r : Finset κ} (hr : r.Nonempty)
    {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
    (Fz : GlobalComparableBodyFactorization a b hab hb1 r (fun k => (R k).toConvexSpaceBody) C₀) :
    ρ ≤ a := by
  obtain ⟨k, hk⟩ := hr
  have hcell : Fz.cellOf k ∈ Fz.cells := Fz.cellOf_mem k hk
  obtain ⟨Q, hQ⟩ := Fz.le_plank (Fz.cellOf k) hcell
  have hR : (R k).toConvexSpaceBody ≤ Q.toConvexSpaceBody :=
    le_trans (Fz.le_body k hk) hQ
  exact Tube.rho_le_of_le_prism3D (R k) Q hR

/-! ### Inner slab non-concentration: the Part-(B) concentration step

The concentration parameter of Proposition 6.6(B) is *not* the part-(A) one.  The outer plank family
is Katz--Tao, so GWZ Lemma 6.1 is applied to it with `γ = 0`, where the slab hypothesis is vacuous
(`Kakeya.gammaZeroSlabBound`): no concentration bound, and in particular no cross-parent overlap
loss, is needed for the outer family.  The concentration that *is* needed is for the inner,
rescaled family, with `γ = 1` and a sub-polynomial constant.  The counting core of that bound is the
following (blueprint `lem:factorInnerSlabNonconcentration`).
-/

end Kakeya

end

end