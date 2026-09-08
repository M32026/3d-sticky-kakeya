/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank
public import Kakeya.PartialEstimates
public import Kakeya.Factorization
public import Kakeya.ShadedUniform
public import Kakeya.Uniform

/-!
# Main estimates from GWZ Section 6

This file carries the factorization data used by the statements of GWZ Section 6 —
`Kakeya.PlankFactorization`, `Kakeya.ContainsFlatDisc`, `Kakeya.GlobalPlankFactorization`,
`Kakeya.PersistentPlankFactorization` — the plank obstruction `Kakeya.convexHull_tubes_ne_prism`,
and the statement of Proposition 6.6(A) (`Kakeya.tubeMultiplicityOfLocalPlankFactorisation`,
vacuously true; see its docstring).  Proposition 6.6(B),
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`, was stated here until it was proved; it now
lives, with its proof, in `Kakeya/DimensionThree/Plank/Prop66BClose.lean`, which imports this
file.  Lemma 6.4 is stated and proved elsewhere (see the note before Proposition 6.6 below).

-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal

noncomputable section

namespace Kakeya

/-- A factorization whose outer bodies are `a × b × 1` planks.

**Warning: unsatisfiable over tubes.**  The field `parts_are_planks` asks the convex hull of each
block to *equal* an exact plank.  A `Finpartition`'s parts are nonempty, and by
`Kakeya.Plank.convexHull_biUnion_ne_of_tube` (`Kakeya/RelativePlank.lean`) the convex hull of a
nonempty family of `δ`-tubes with `δ > 0` is never an exact plank: a plank vertex has a
three-dimensional normal cone, while the boundary of a positive-radius tube is smooth.  So over any
family of positive-radius tubes with a nonempty index set this structure is uninhabited — see
`Kakeya.not_plankFactorization_of_tube` and `Kakeya.not_plankFactorization_of_shadedTube` — and a
theorem quantifying over it is vacuous.

Use `Kakeya.GlobalPlankFactorization` or `Kakeya.PersistentPlankFactorization`, below, for any
statement whose inner family is a family of tubes: both ask only for containment in a plank, not
equality with one.  `PlankFactorization` is retained only because the exact-hull reading is the
literal reading of [GWZ]'s "𝕎 is a family of `a × b × 1` planks factoring 𝕍" and it is worth
having the obstruction attached to a named object. -/
structure PlankFactorization {ι : Type*} [DecidableEq ι]
    (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    (s : Finset ι) (V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (C₀ : ℝ≥0)
    extends ConvexSpaceBody.Factorization s V C₀ where
  parts_are_planks : ∀ part ∈ parts, ∃ Q : Plank a b hab hb1,
    part.convexHull_biUnion V = Q.toConvexSpaceBody

/-- A set contains a flat disc of radius `b` if it contains a translate of the `b`-ball in some
two-dimensional linear subspace. -/
def ContainsFlatDisc (b : ℝ≥0) (S : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ (c : EuclideanSpace ℝ (Fin 3)) (P : Submodule ℝ (EuclideanSpace ℝ (Fin 3))),
    Module.finrank ℝ P = 2 ∧ ∀ v ∈ P, ‖v‖ ≤ (b : ℝ) → c + v ∈ S

/-- Containing a flat disc is antitone in the radius: a set holding a disc of radius `b` holds
every smaller concentric disc in the same plane. -/
theorem ContainsFlatDisc.mono {b b' : ℝ≥0} {S : Set (EuclideanSpace ℝ (Fin 3))}
    (h : ContainsFlatDisc b S) (hb : b' ≤ b) : ContainsFlatDisc b' S := by
  obtain ⟨c, P, hP, hmem⟩ := h
  exact ⟨c, P, hP, fun v hv hnorm => hmem v hv (hnorm.trans (by exact_mod_cast hb))⟩

/-- A global factorization of coarse tubes by bodies comparable to `a × b × 1` planks, with an
explicit transverse comparability constant `Cw ≥ 1`.

The factor bodies are their actual convex hulls. They need only be contained in representative
planks, rather than equal to exact rectangular prisms. The flat-disc condition supplies the
lower bound on their two long dimensions, up to `Cw`.

This is the repaired datum for GWZ Proposition 6.6(B).  It replaces the unsatisfiable
`Kakeya.PlankFactorization.parts_are_planks` (hull **equals** plank, refuted over tubes by
`Kakeya.convexHull_tubes_ne_prism`) by the pair `le_plank` (hull **≤** plank) and `wide` (a
transverse lower bound).  Both halves are needed: without `le_plank` the conclusion's `(a/b) ^ β`
is not paid for from above, and without `wide` the datum is satisfied by bodies far thinner than
`b` in the middle direction, for which the asserted gain `(a/b) ^ β` is simply false — take outer
bodies that are honest `a × a × 1` planks and declare `b := 1`.

**Why `wide` carries a constant.**  In the first repair (Weikun He, `d835ff4f5` on
`origin/hwk/lemma66B`) the disc radius was exactly `min b (1/2)`, with no constant.  That is
*tight*, and jointly with `le_plank` it is unsatisfiable by the intended producer.  A covering or
John-ellipsoid argument applied to the hull `W` of a block of coarse tubes returns a two-sided
comparison with an absolute constant: `W ⊆ plank (C * a, C * b, 1)` and `W ⊇ disc (c * b)` with
`c < 1 < C`.  To feed the unconstanted structure one must pick a single middle half-width `B` with
`W ⊆ plank (·, B, ·)` — forcing `B ≥ C * b` — and `min B (1/2) ≤ c * b` — forcing `B ≤ c * b` when
`c * b < 1/2`.  Since `c * b < C * b`, no such `B` exists.  Dividing the disc radius by `Cw` is
exactly the slack needed, and it is the tree's established pattern: `Kakeya.IsPlankOfDimensions`
in `Kakeya/Factoring/FlatPrisms.lean` carries the same explicit `C ≥ 1` two-sidedly on all three
affine thicknesses.

Relaxing `wide` **weakens** the structure (`Kakeya.GlobalPlankFactorization.mono_Cw`), hence
strengthens any theorem quantifying over it; a consumer must therefore pay for `Cw`, and
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`
(`Kakeya/DimensionThree/Plank/Prop66BClose.lean`) does so with the sub-polynomial budget
`Cw ≤ δ ^ (-η)` that the statement already spends on `Cpar` and `C₀`.

The pair is satisfiable, including by hulls of `ρ`-tube blocks: at `a = b = ρ ≤ 1 / 2` such a hull
contains `Metric.closedBall 0 ρ`, hence a flat `ρ`-disc, while fitting inside a `ρ × ρ × 1`
plank. -/
structure GlobalPlankFactorization {κ : Type*} [DecidableEq κ]
    (Cw a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    (r : Finset κ) (R : κ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (C₀ : ℝ≥0)
    extends ConvexSpaceBody.Factorization r R C₀ where
  /-- The transverse comparability constant is at least one. -/
  one_le_Cw : 1 ≤ Cw
  /-- Every factor body is contained in a representative `a × b × 1` plank. -/
  le_plank : ∀ part ∈ parts, ∃ P : Plank a b hab hb1,
    part.convexHull_biUnion R ≤ P.toConvexSpaceBody
  /-- Every factor body contains a flat disc at the middle plank scale, up to the transverse
  comparability constant `Cw`. -/
  wide : ∀ part ∈ parts,
    ContainsFlatDisc (min b (1 / 2) / Cw) (part.convexHull_biUnion R).carrier

/-- **The `Cw`-parameterised `wide` really is a weakening.**  Enlarging the transverse
comparability constant preserves the datum, so every factorization satisfying the unconstanted
`wide` of the first repair (`Cw = 1`) is a `GlobalPlankFactorization` for every `Cw ≥ 1`, and a
theorem quantifying over the `Cw`-form is stronger than one quantifying over the `1`-form. -/
def GlobalPlankFactorization.mono_Cw {κ : Type*} [DecidableEq κ]
    {Cw Cw' a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {r : Finset κ}
    {R : κ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {C₀ : ℝ≥0}
    (Fz : GlobalPlankFactorization Cw a b hab hb1 r R C₀) (hCw : Cw ≤ Cw') :
    GlobalPlankFactorization Cw' a b hab hb1 r R C₀ where
  toFactorization := Fz.toFactorization
  one_le_Cw := Fz.one_le_Cw.trans hCw
  le_plank := Fz.le_plank
  wide := fun part hpart => by
    refine (Fz.wide part hpart).mono ?_
    have h0 : (0 : ℝ≥0) < Cw := lt_of_lt_of_le zero_lt_one Fz.one_le_Cw
    gcongr


/-! ### The `parts_are_planks` obstruction

`Kakeya.tubeMultiplicityOfLocalPlankFactorisation` (GWZ 6.6(A)) below is stated for
factorizations of *tube* bodies whose parts' convex hulls are required to be **exactly equal** to
planks (`PlankFactorization.parts_are_planks`).  That requirement is unsatisfiable, and the next
two lemmas prove it: the convex hull of a nonempty finite family of `δ`-tubes with `δ > 0` is a
Minkowski sum `K + closedBall 0 δ`, hence has no corner, while a prism carrier has one.  So
6.6(A) is vacuously true; see its docstring.

`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` (GWZ 6.6(B)) is **no longer** stated over that
equality: it now takes a `Kakeya.GlobalPlankFactorization`, whose `le_plank` is an inclusion, and
so escapes this obstruction.  It is proved, in `Kakeya/DimensionThree/Plank/Prop66BClose.lean`;
see its docstring there.
-/

section PlankObstruction

open scoped Pointwise

/-- The `δ`-neighbourhood of a set, written as a Minkowski sum, is its union of closed balls. -/
private lemma add_closedBall_zero_eq_biUnion
    (S : Set (EuclideanSpace ℝ (Fin 3))) (δ : ℝ) :
    S + Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) δ =
      ⋃ z ∈ S, Metric.closedBall z δ := by
  ext p
  simp only [Set.mem_add, Set.mem_iUnion, Metric.mem_closedBall, exists_prop, dist_eq_norm]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, by simpa [add_sub_cancel_left, norm_sub_rev] using hy⟩
  · rintro ⟨z, hz, hpz⟩
    exact ⟨z, hz, p - z, by simpa using hpz, by abel⟩

/-- **A convex hull of tubes is never a prism.**

If `t` is a nonempty finite family of `δ`-tubes with `δ > 0`, the convex hull of the union of
their carriers is never equal to the carrier of a `Prism3D`.

The tube carrier is `segment + closedBall 0 δ`, so the hull is `K + closedBall 0 δ` with
`K = convexHull ℝ (⋃ segments)`.  Let `e₀, e₁` be two axes of the prism, with half-widths
`r₀, r₁`, and let `p := center + r₀ • e₀ + r₁ • e₁` be the corresponding corner, which lies in
the prism.  Writing `p = k + w` with `k ∈ K` and `‖w‖ ≤ δ`, the points `k + δ • e₀` and
`k + δ • e₁` also lie in `K + closedBall 0 δ`, hence in the prism, which forces
`⟪e₀, w⟫ ≥ δ` and `⟪e₁, w⟫ ≥ δ`.  Then Cauchy–Schwarz applied to `e₀ + e₁` gives
`2δ ≤ ‖e₀ + e₁‖ * ‖w‖ = √2 * δ`, contradicting `δ > 0`. -/
private theorem convexHull_tubes_ne_prism {δ : ℝ≥0} (hδ : 0 < δ) {ι : Type*} {t : Finset ι}
    (_ht : t.Nonempty) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
    {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c} (P : Prism3D a b c hab hbc)
    (h : (Convexity.convexHull ℝ
        (⋃ i ∈ t, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))))
      = (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))) : False := by
  have hδ' : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  set S : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ i ∈ t, segment ℝ (T i).x (T i).y with hS
  have hcap : (⋃ i ∈ t, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) =
      S + Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) δ := by
    rw [add_closedBall_zero_eq_biUnion]
    ext p
    simp only [hS, (T _).carrier_eq, Set.mem_iUnion, exists_prop]
    tauto
  rw [hcap, Convexity.convexHull_eq_convexHull, convexHull_add,
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) δ).convexHull_eq] at h
  set K : Set (EuclideanSpace ℝ (Fin 3)) := _root_.convexHull ℝ S with hK
  set e : Fin 3 → EuclideanSpace ℝ (Fin 3) := fun j => P.basis j with he
  set r : Fin 3 → ℝ := fun j => ((P.thicknesses j : ℝ≥0) : ℝ) with hr
  have hP : ∀ x : EuclideanSpace ℝ (Fin 3),
      x ∈ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ↔
        ∀ j, |inner ℝ (e j) (x - P.center)| ≤ r j := fun x => by
    simpa [he, hr, OrthonormalBasis.repr_apply_apply, vsub_eq_sub, inner_sub_right] using
      P.mem_carrier_iff x
  have hortho : ∀ i j : Fin 3, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => by simpa [he] using orthonormal_iff_ite.mp P.basis.orthonormal i j
  have hrnn : ∀ j, 0 ≤ r j := fun j => by positivity
  set p : EuclideanSpace ℝ (Fin 3) := P.center + (r 0 • e 0 + r 1 • e 1) with hp
  have hpc : p - P.center = r 0 • e 0 + r 1 • e 1 := by simp [hp]
  have hphi0 : inner ℝ (e 0) (p - P.center) = r 0 := by
    rw [hpc]; simp [he, inner_add_right, real_inner_smul_right, P.basis.norm_eq_one]
  have hphi1 : inner ℝ (e 1) (p - P.center) = r 1 := by
    rw [hpc]; simp [he, inner_add_right, real_inner_smul_right, P.basis.norm_eq_one]
  have hphi2 : inner ℝ (e 2) (p - P.center) = 0 := by
    rw [hpc]; simp [he, inner_add_right, real_inner_smul_right]
  have hpmem : p ∈ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    refine (hP p).2 fun j => ?_
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by revert j; decide
    rcases hj with rfl | rfl | rfl
    · rw [hphi0, abs_of_nonneg (hrnn 0)]
    · rw [hphi1, abs_of_nonneg (hrnn 1)]
    · rw [hphi2]; simpa using hrnn 2
  rw [← h] at hpmem
  obtain ⟨k, hk, w, hw, hkw⟩ := hpmem
  have hwn : ‖w‖ ≤ (δ : ℝ) := by simpa using hw
  have hmemK : ∀ j : Fin 3,
      k + (δ : ℝ) • e j ∈ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    intro j
    rw [← h]
    refine ⟨k, hk, (δ : ℝ) • e j, ?_, rfl⟩
    simp [norm_smul, he, P.basis.norm_eq_one, abs_of_nonneg hδ'.le]
  have hcoord : ∀ j : Fin 3, inner ℝ (e j) (k - P.center) + (δ : ℝ) ≤ r j := by
    intro j
    have h2 := (hP _).1 (hmemK j) j
    have hrw : k + (δ : ℝ) • e j - P.center = (k - P.center) + (δ : ℝ) • e j := by abel
    rw [hrw, inner_add_right, real_inner_smul_right, hortho j j, if_pos rfl, mul_one] at h2
    exact (abs_le.1 h2).2
  have hsplit : ∀ j : Fin 3, inner ℝ (e j) (p - P.center)
      = inner ℝ (e j) (k - P.center) + inner ℝ (e j) w := by
    intro j
    rw [← hkw, show k + w - P.center = (k - P.center) + w by abel, inner_add_right]
  have hw0 : (δ : ℝ) ≤ inner ℝ (e 0) w := by
    have h1 := hsplit 0
    rw [hphi0] at h1
    have h2 := hcoord 0
    linarith
  have hw1 : (δ : ℝ) ≤ inner ℝ (e 1) w := by
    have h1 := hsplit 1
    rw [hphi1] at h1
    have h2 := hcoord 1
    linarith
  have hsum : (2 : ℝ) * (δ : ℝ) ≤ inner ℝ (e 0 + e 1) w := by
    rw [inner_add_left]; linarith
  have hunorm : ‖e 0 + e 1‖ ^ 2 = 2 := by
    rw [norm_add_sq_real, hortho 0 1, P.basis.norm_eq_one, P.basis.norm_eq_one]
    norm_num
  have hcs : inner ℝ (e 0 + e 1) w ≤ ‖e 0 + e 1‖ * ‖w‖ := real_inner_le_norm _ _
  nlinarith [norm_nonneg (e 0 + e 1), norm_nonneg w]

end PlankObstruction

open Classical in
/-- **A factorization through fixed outer plank bodies.**

`Kakeya.PlankFactorization` requires `part.convexHull_biUnion V = Q.toConvexSpaceBody`, an equality
that any thinning of the inner family destroys — and which, over tubes of positive radius, no
family satisfies at all (see the warning on `PlankFactorization`).  That equality is not what the
consumers of GWZ Proposition 6.6 use.  GWZ Lemma 6.4 has no inner family at all, and GWZ Lemma 5.1
needs only that each inner body lies in the outer body of its own block, together with a Frostman
constant for that block.

`PersistentPlankFactorization` keeps exactly those: the outer bodies of the blocks actually used
*are* planks, the outer family is Katz--Tao, and each block is dense enough inside its own outer
body.  Crucially the outer bodies are *free data* on a `ConvexSpaceBody.FactorFamily` rather than
hulls of the inner blocks, so nothing forces them to be spanned by the inner family and the
obstruction of `Kakeya.Plank.convexHull_biUnion_ne_of_tube` does not apply: a `δ`-tube fits inside
an `a × b × 1` plank whenever `δ ≤ a`.  It is also stable under restricting the fibres while
holding the outer bodies fixed, which is what the joint regularization of
`Kakeya/RelativePlank.lean` produces.

This declaration lives here, rather than next to its main users in `Kakeya/RelativePlank.lean`,
for a historical reason: GWZ Proposition 6.6(B),
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`, followed it in this file until it was proved
and moved to `Kakeya/DimensionThree/Plank/Prop66BClose.lean`.  That theorem is stated over
`Kakeya.GlobalPlankFactorization` above, not over this structure (see the section note below). -/
structure PersistentPlankFactorization {ι ω : Type*}
    (F : ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι ω)
    (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1) (C₀ : ℝ≥0) : Prop where
  /-- The outer body of every block that still carries an inner member is an `a × b × 1` plank. -/
  outer_are_planks : ∀ j ∈ F.innerSet.image F.parent, ∃ Q : Plank a b hab hb1,
    F.outerBody j = Q.toConvexSpaceBody
  /-- The family of those outer bodies is Katz--Tao with constant `C₀`. -/
  outer_isKatzTao : IsKatzTao (F.innerSet.image F.parent) F.outerBody (C₀ : ℝ≥0∞)
  /-- Each block is, up to `C₀`, as dense inside its own outer body as the whole inner family is
  anywhere.  This is the Frostman input of GWZ Lemma 5.1. -/
  maxDensity_le_mul : ∀ j ∈ F.innerSet.image F.parent,
    maxDensity F.innerSet F.innerBody ≤
      (C₀ : ℝ≥0∞) * densityIn (F.fiber j) F.innerBody (F.outerBody j)

/-! ### GWZ Lemma 6.4

`Kakeya.FrostmanEstimate.plankEstimate` is **not** stated in this file. Keeping the sorried copy here made the environment reject the import outright, so it
has been deleted rather than left as a shadow.

The two statements are *not* interchangeable, so 6.4 must not be re-stated here: the proved one
quantifies `∃ C_NC, 1 ≤ C_NC ∧ …` outermost and fixes `ι : Type u`, asks for the window as a
containment in `Metric.closedBall 0 plankWindowRadius` rather than through
`Kakeya.Plank.IsWindowedFamily`, and takes `Kakeya.Plank.IsThickeningNonconcentrated` in place of
the explicit thickening count.  The conclusion is identical. -/

/-! ### GWZ Proposition 6.6

6.6(A) below is the statement carried by library, unchanged, and still vacuously
true.  The Section 8 branch had replaced it by
`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'` (a different, non-interchangeable scale
regime); that substitution is not adopted here, because it is a change to a statement the master
development owns.

6.6(B) **has** been restated, over `Kakeya.GlobalPlankFactorization` above, precisely to repair
its vacuity; the first correction is Weikun He's (`d835ff4f5` on `origin/hwk/lemma66B`) and the
`Cw`-parameterised `wide` that makes that correction *supplyable* is steps.  The restated
theorem, `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`, is **proved** and lives in
`Kakeya/DimensionThree/Plank/Prop66BClose.lean`.  It is not the Section 8 branch's
restatement over `PersistentPlankFactorization`, which is a different datum.
`PersistentPlankFactorization` above is kept regardless, since `Kakeya/RelativePlank.lean` is
stated over it.
-/

open Classical in
/-- GWZ Proposition 6.6(A): local plank factorization.

**WARNING — THIS STATEMENT IS VACUOUSLY TRUE AND DOES NOT FORMALIZE GWZ PROPOSITION 6.6(A).**

The proof below is a genuine, compiler-checked proof of the statement exactly as written, but it
proceeds by deriving `False` from the hypotheses whenever `q` is nonempty, and by
`ShadedBody.multiplicity_empty` otherwise.  The defect is the field
`PlankFactorization.parts_are_planks`, which demands the **exact equality**
`part.convexHull_biUnion V = Q.toConvexSpaceBody` of the convex hull of a part with a plank.
Here `V i = (T i).toConvexSpaceBody` is a `δ`-tube body, i.e. a capsule
(`Tube.carrier_eq`), so the hull of a nonempty part is a Minkowski sum
`K + Metric.closedBall 0 δ`, which for `δ > 0` has no corner, whereas a plank carrier is a box
and does (`Kakeya.convexHull_tubes_ne_prism`).  Hence `Fz` cannot exist for a nonempty `q`, and
nothing about multiplicity is actually being asserted.

The repaired datum is `ComparableBodyFactorization` on the branch
`origin/wjq/lem5.1-section6-remain`
(`lean/kakeya/Kakeya/DimensionThree/Plank/ComparableBodyFactorization.lean`), which deliberately
omits `parts_are_planks` and replaces it by a comparability hypothesis between the hull and a
plank.  Restating Proposition 6.6(A) over that structure is the outstanding mathematical work;
this file's statement must not be relied on. -/
theorem tubeMultiplicityOfLocalPlankFactorisation {β : ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0),
      ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        δ ≤ δ₀ →
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∃ C : ℝ≥0, C ≤ δ ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet q T
            (Tube.ssfGridLen δ) C)) →
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
          {κ : Type} (r : Finset κ)
          (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (assign : ι → κ),
          δ ≤ ρ → ρ ≤ a →
          (∀ i ∈ q, assign i ∈ r ∧
            (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody) →
          ∀ (C₀ : ℝ≥0), C₀ ≤ δ ^ (-η) →
            ∀ (Fz : ∀ k ∈ r, PlankFactorization a b hab hb1
              {i ∈ q | assign i = k} (fun i => (T i).toConvexSpaceBody) C₀),
          ∀ (CF : ENNReal), 1 ≤ CF → CF ≠ ⊤ →
            IsFrostmanIn q (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall CF →
            ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
              (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2)
                * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
                * (δ : ENNReal) ^ (-2 * β)
                * ((δ : ENNReal) ^ 2 * (q.card : ENNReal)) ^ (1 - β / 2) := by
  intro ε hε
  refine ⟨1, one_pos, 1, one_pos, ?_⟩
  intro ι q δ hδ0 T _ _ _ _ ρ a b hab hb1 κ r R assign _ _ hassign C₀ _ Fz CF _ _ _
  rcases q.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp
  · exfalso
    obtain ⟨hk, -⟩ := hassign i hi
    obtain ⟨part, hpart, hipart⟩ :=
      (Fz (assign i) hk).toFinpartition.exists_mem (Finset.mem_filter.2 ⟨hi, rfl⟩)
    obtain ⟨Q, hQ⟩ := (Fz (assign i) hk).parts_are_planks part hpart
    have hne : part.Nonempty := ⟨i, hipart⟩
    have hc := congrArg
      (fun B : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) =>
        (B.carrier : Set (EuclideanSpace ℝ (Fin 3)))) hQ
    simp only [Finset.Nonempty.convexHull_biUnion_carrier hne] at hc
    exact convexHull_tubes_ne_prism hδ0 hne (fun j => (T j).toTube) Q hc

end Kakeya

end
