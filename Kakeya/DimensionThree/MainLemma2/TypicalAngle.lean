/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.DimensionThree.MainLemma2.ThinConfig

/-!
# The typical-angle package at a ball

This file carries the single bundle `Kakeya.VeryNotSticky.TypicalAngleData`, the output of
blueprint Proposition `lem:ml2typicalangle` at a ball `B ∈ 𝔅` of Configuration
`hyp:ml2setup`: a presentation of the factoring family `𝕎'_B` as a family of planks, a
`⪆ 1` refinement `(𝕎''_B, Y_{𝕎''_B})` of `(𝕎'_B, Y_{𝕎'_B})`, and an angle `θ ∈ [a/b, 1]`
that is typical for the refinement.

It lives in its own file because it is produced in one place
(`Kakeya.VeryNotSticky.exists_isTypicalAnglePlank`, in
`Kakeya.DimensionThree.MainLemma2.NonSlabCase`) and consumed in two mutually incomparable
ones — the transverse leaf `Kakeya.VeryNotSticky.goalMult_of_theta_ge` and the tangential
leaf `Kakeya.VeryNotSticky.goalMult_of_theta_lt` — so neither of those files can be the home
of the definition.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

universe u

/-- **The normal of a convex body of `ℝ³`, at the ambient dimension** (blueprint
`def:ml2bodyNormal`): `Kakeya.NonSlab.bodyNormal` with the proof `finrank_euclideanSpace_fin`
of `dim ℝ³ = 3` supplied once.

Folding it into a definition of its own is not cosmetic. Elaborating
`NonSlab.bodyNormal finrank_euclideanSpace_fin _` at `E := EuclideanSpace ℝ (Fin 3)` costs the
`finrank` proof plus five instance searches, and the tangential argument mentions the normal
dozens of times — in `Kakeya.VeryNotSticky.IsSlabFamily`, in the packing argument of
`Kakeya.VeryNotSticky.tangentialSlabFibreCount` and in every `Finset.image` and `Set.InjOn`
around it. Written out, those occurrences exhaust the heartbeat budget of a single
declaration; folded, they do not. Keep it folded: use `norm_bodyNormal`,
`bodyNormal_ne_zero` and `axisAngle_eq_lineAngle` rather than `simp`/`unfold`. -/
noncomputable def bodyNormal (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    EuclideanSpace ℝ (Fin 3) :=
  NonSlab.bodyNormal finrank_euclideanSpace_fin W

/-- The normal is a unit vector, which is the `hunit` hypothesis of
`Kakeya.NonSlab.card_le_coneDirectionCount`. -/
lemma norm_bodyNormal (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    ‖bodyNormal W‖ = 1 :=
  NonSlab.norm_bodyNormal finrank_euclideanSpace_fin W

/-- The normal is nonzero, being a unit vector. -/
lemma bodyNormal_ne_zero (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    bodyNormal W ≠ 0 := by
  intro h
  simpa [h] using norm_bodyNormal W

/-- **The angle between the normals of two convex bodies of `ℝ³`** (blueprint
`def:ml2axisAngle`): `∠(n(W), n(W'))`, the quantity the blueprint writes `∠(v(W), v(W'))`
throughout the tangential subsubsection, with `n(·) = Kakeya.NonSlab.bodyNormal` the rank-`2`
direction of the outer prism — the direction of *smallest* affine thickness — and the angle
taken between the *lines* `ℝ n(W)`, `ℝ n(W')`, so that the sign ambiguity of `bodyNormal` is
harmless.

**Why the normal and not the long axis.** This definition used to read
`Kakeya.NonSlab.bodyAxis`, the rank-`0` direction, i.e. the *longest* half-width. That was a
mismatch with the only hypothesis that ever bounds this quantity between two bodies, the
typicality `Kakeya.VeryNotSticky.TypicalAngleData.htyp`: `Kakeya.IsTypicalPlankAngle` measures
angles through `Kakeya.effectivePlankAngle`, hence through `Kakeya.Prism3D.angle`, which is
`arccos |⟪P₁.basis 0, P₂.basis 0⟫|`; and for `Plank a b = Prism3D a b 1` with `a ≤ b ≤ 1` the
half-widths are *ascending*, so `basis 0` is the smallest of them — the plank's normal. Since
`Metric.thickness` is antitone in the rank, the matching direction of a body is
`outerPrism.basis 2`, not `outerPrism.basis 0`. The two are different quantities in `ℝ³` and
no bound on one gives a bound on the other, so the old reading left the typicality hypothesis
inapplicable to the bodies. Blueprint `note:ml2slabAxisSeparationCorrection` already
identified the normal as the direction that separates two slabs; the Lean now reads it.

`Kakeya.NonSlab.bodyAxis` is *not* obsolete: it remains the right direction where a body is
compared with a tube of one of its blocks (`Kakeya.NonSlab.lineAngle_bodyAxis_le`, used in
`Kakeya/DimensionThree/MainLemma2/NonSlabSplit.lean`). Only the tangential subsubsection
changes.

**Why it lives here and not in `TangentialCase.lean`.** It is read by the field
`Kakeya.VeryNotSticky.TypicalAngleData.hangle` below as well as by
`Kakeya.VeryNotSticky.IsSlabFamily`, and this file is upstream of both consumers.

The abbreviation is a Lean convenience, for the reason recorded on
`Kakeya.VeryNotSticky.bodyNormal`: it keeps the expensive term folded at the dozens of places
where the tangential argument reads an angle. -/
noncomputable def axisAngle (W W' : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) : ℝ :=
  NonSlab.lineAngle (bodyNormal W) (bodyNormal W')

/-- `axisAngle` unfolded onto `Kakeya.NonSlab.lineAngle`, as a `rfl`-lemma. Rewriting with this
is far cheaper than `simp [axisAngle]`: it keeps `Kakeya.VeryNotSticky.bodyNormal` folded, and
so avoids re-elaborating `finrank_euclideanSpace_fin` and the five instance searches around it
at every occurrence. That cost is the reason both abbreviations exist. -/
lemma axisAngle_eq_lineAngle (W W' : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    axisAngle W W' = NonSlab.lineAngle (bodyNormal W) (bodyNormal W') := rfl

/-- `axisAngle` is symmetric: it is `Kakeya.NonSlab.lineAngle`, a metric on unoriented
directions. -/
lemma axisAngle_comm (W W' : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    axisAngle W W' = axisAngle W' W :=
  NonSlab.lineAngle_comm _ _

/-- `axisAngle` is nonnegative. -/
lemma axisAngle_nonneg (W W' : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    0 ≤ axisAngle W W' :=
  NonSlab.lineAngle_nonneg _ _

/-- The triangle inequality for `axisAngle`, exact because `Kakeya.NonSlab.lineAngle` is the
quotient metric on unoriented directions. This is the step
`∠(n(S), n(W₁)) ≤ ∠(n(S), n(W₂)) + ∠(n(W₂), n(W₁))` of blueprint
`lem:ml2tangentialSlabFibreCount`. -/
lemma axisAngle_le_add (W W' W'' : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    axisAngle W W'' ≤ axisAngle W W' + axisAngle W' W'' :=
  NonSlab.lineAngle_le_add _ _ _

/-- A body makes angle `0` with itself: its normal is a unit vector, hence nonzero. -/
@[simp] lemma axisAngle_self (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    axisAngle W W = 0 :=
  NonSlab.lineAngle_self (bodyNormal_ne_zero W)

/-- **The angle between two prisms built on the bodies' own frames is the bodies' angle.**

`Kakeya.Prism3D.angle` is `arccos |⟪P.basis 0, Q.basis 0⟫|` and
`Kakeya.VeryNotSticky.axisAngle` is `Kakeya.NonSlab.lineAngle` of the two normals, which is the
same `arccos` by `Kakeya.NonSlab.lineAngle_eq_arccos_abs_inner`; and the rank-`0` vector of
`Kakeya.NonSlab.bodyFrame` *is* the normal, by `Kakeya.NonSlab.bodyFrame_zero`.

This is the identity that turns the typicality of the plank angles produced by
`Kakeya.findingTypicalAngleOfIntersection_perScale` into the display `anglebound`, i.e. into the
field `Kakeya.VeryNotSticky.TypicalAngleData.hangle`. Its hypotheses are exactly what the
prescribed-frame enclosure `Kakeya.VeryNotSticky.plankWindowEnclosure` returns, recorded as
`Kakeya.VeryNotSticky.PlankPresentationData.hbasis`. -/
lemma prism_angle_eq_axisAngle {a₁ b₁ c₁ a₂ b₂ c₂ : NNReal}
    {h₁ : a₁ ≤ b₁} {h₁' : b₁ ≤ c₁} {h₂ : a₂ ≤ b₂} {h₂' : b₂ ≤ c₂}
    (P : Prism3D a₁ b₁ c₁ h₁ h₁') (Q : Prism3D a₂ b₂ c₂ h₂ h₂')
    (W W' : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (hP : P.basis = bodyFrame W) (hQ : Q.basis = bodyFrame W') :
    P.angle Q = axisAngle W W' := by
  rw [Prism3D.angle_def P Q, hP, hQ]
  rw [bodyFrame_zero W, bodyFrame_zero W']
  rw [axisAngle_eq_lineAngle]
  rw [NonSlab.lineAngle_eq_arccos_abs_inner (norm_bodyNormal W) (norm_bodyNormal W')]
  rfl

/-- **The typical angle of intersection, with its plank presentation and its refinement**
(blueprint Proposition `lem:ml2typicalangle`, `def:typicalAnglePlank`).

At a ball `B ∈ 𝔅` this is the whole output of blueprint `lem:ml2typicalangle`, produced by
`Kakeya.VeryNotSticky.exists_isTypicalAnglePlank` and consumed verbatim by both angular
leaves and by `Kakeya.VeryNotSticky.tangentialSlabDecomp`. Its three groups of fields are:

* the *plank presentation* `P` of `𝕎'_B = (tc.thinBall hB).bodies'` as a family of
  `a' × b' × 1` planks with the same aspect ratio, `hratio : a'/b' = a/b`, together with the
  clause `hwin` that `ShadedPlank.reduction_to_slab` needs and that a freely given plank family
  cannot supply (blueprint `lem:ml2plankPresentation`); an essential-distinctness clause `hPed`
  stood beside it until R26 deleted that field;
* the *refinement* `(𝕎''_B, Y_{𝕎''_B})`, recorded as the shading `YW` on the same index set
  together with `hrefine` and the refinement factor `c ≥ δ^{2η}` of `hc` — this
  development's rendering of `⪆ 1`, `η` being the smallest positive exponent of the section
  (blueprint `lem:ml2fullnessRefine`, `lem:ml2multRefine`) — and the fullness `hfull` of the
  refined pair, which is asserted here, where `YW` is produced, rather than assumed by a
  consumer;
* the *angle* `θ ∈ [a'/b', 1]` and its typicality constant `Ctyp`, with the two-sided bound
  `hCtyp1 : 1 ≤ Ctyp` / `hCtyp : Ctyp ≤ (δ^{1-exscal})^{-η/256}` on that constant and the
  typicality `htyp` itself. The lower bound is what makes `Ctyp` a genuine *loss*, in the
  sense of the constant/exponent convention ; it costs the producer
  `Kakeya.VeryNotSticky.exists_isTypicalAnglePlank` nothing, since both
  `Kakeya.IsTypicalPlankAngle` and `ShadedBody.HasCConstantMultiplicity` only weaken as the
  constant grows and the upper bound `(δ^{1-exscal})^{-η/256}` is itself `≥ 1`, so the
  constant `C` returned by `Kakeya.findingTypicalAngleOfIntersection_perScale` may be replaced by
  `max 1 C`. It is used in `Kakeya.VeryNotSticky.tangentialSlabFibreCount`, whose cone
  aperture step is `∠(n(S), n(W₁)) ≤ 2θ + Ctyp θ ≤ 3 Ctyp θ` (the slab clause (S3) being read
  at `2θ`), and hence in the lower bound `1 ≤ Cμ` recorded in
  `Kakeya.VeryNotSticky.IsSlabDecompMultConstant`.

Bundling is what keeps the two angular leaves and `tangentialSlabDecomp` from each
re-listing fourteen binders; the alternative was three verbatim copies of this list.

The angle clause is stated at `a'/b'` and not at `a/b`, matching the form in which
`Kakeya.findingTypicalAngleOfIntersection_perScale` produces it; `hθab'` below converts it using
`hratio`.

The bundle is indexed by the transverse parameter `τ'` because its fullness clause `hfullP` is
asserted only under the transverse-case guard `δ^{-τ'} a/b ≤ θ`, the sole regime in which GWZ invoke Lemma 6.13 and the only place the clause
is read. -/
structure TypicalAngleData (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs) (τ' : ℝ) where
  /-- the smaller plank dimension -/
  a' : NNReal
  /-- the middle plank dimension -/
  b' : NNReal
  /-- the planks are `a' × b' × 1` with `a' ≤ b'` -/
  hab' : a' ≤ b'
  /-- the planks are `a' × b' × 1` with `b' ≤ 1` -/
  hb1' : b' ≤ 1
  /-- the plank presentation of `𝕎'_B` (blueprint `lem:ml2plankPresentation`) -/
  P : bd.ω → Plank a' b' hab' hb1'
  /-- the shading `Y_{𝕎''_B}` of the refinement -/
  YW : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3))
  /-- the typical angle of intersection -/
  θ : NNReal
  /-- the refinement factor, `⪆ 1` -/
  c : NNReal
  /-- the typicality constant `C_{lem:ml2typicalangle}` -/
  Ctyp : NNReal
  /-- the subfamily `𝕊* ⊆ 𝕎'_B` on which the planks *are* pairwise essentially distinct; see
  `Kakeya.VeryNotSticky.plankSelectionConstant` for why the whole family will not do -/
  sel : Finset bd.ω
  /-- `𝕊*` is a subfamily of `𝕎'_B` -/
  hsel : sel ⊆ (tc.thinBall hB).bodies'
  /-- the planks have the aspect ratio of the factoring bodies -/
  hratio : a' / b' = cfg.a / cfg.b
  /-- the refinement is `⪆ 1`; the selection factor of
  `Kakeya.VeryNotSticky.plankSelectionConstant` is already absorbed here, against the slack in
  the bound on `Ctyp`, so this clause is unchanged at `δ^{2η}` -/
  hc : cfg.δ ^ (2 * cfg.η) ≤ c
  /-- `(𝕎''_B, Y_{𝕎''_B})` restricted to `𝕊*` is a `c`-refinement of `(𝕎'_B, Y_{𝕎'_B})`; the
  index set drops to `𝕊*`, which `ShadedBody.IsRefinement` permits -/
  hrefine : ShadedBody.IsCRefinement sel YW
    (tc.thinBall hB).bodies' (tc.thinBall hB).W c
  /-- `θ` is at least the aspect ratio -/
  hθab : a' / b' ≤ θ
  /-- `θ` is at most one -/
  hθ1 : θ ≤ 1
  /-- the planks are localized in the Section 6 window -/
  hwin : Plank.IsWindowedFamily sel P
  /-- **The refined pair retains the fullness of (T2), at the exponent `8η`.**

  This is (T2), `Kakeya.ThinCase.ThinBall.fullness_bodies` — `δ^{6η} ≤ C λ(𝕎'_B, Y_{𝕎'_B})` at
  the `tb` index `2η` — propagated through the `c`-refinement of `hrefine`, which costs the
  second factor `δ^{2η}` by `hc` and `ShadedBody.IsCRefinement.mul_fullness_le`. The two factors
  are independent and neither can be dropped, which is why the exponent is `8η` and not `6η`;
  the same exponent appears for the same reason in `Kakeya.VeryNotSticky.tangentialSlabDecomp`.

  **Why it is not `(a')^η ≤ λ(𝕊*, Y_{𝕎''_B})`.** That is the form
  `ShadedPlank.reduction_to_slab` wants, and it is the form this field used to carry, but it
  is not reachable from Configurations `hyp:ml2setup` and `hyp:ml2thinsetup`: `a' ≥ δ/r₁` by
  `Kakeya.VeryNotSticky.PlankPresentationData.hδa'`, so `(a')^η ≥ δ^{(1-exscal)η}`, whereas
  the largest lower bound on the fullness available anywhere in the configuration is the
  `δ^{6η}` of (T2), and `(1-exscal)η < 6η`. The gap is a positive power of `δ`, so no constant
  and no smallness hypothesis on `δ` can close it — shrinking `δ` makes it worse. The
  blueprint records the same computation in the closing note of `lem:ml2typicalangle` ("what
  this proposition does *not* produce") and concludes that the `(a')^η` fullness is a
  mathematical input owed by whatever produces the bodies, not by
  `Kakeya.VeryNotSticky.exists_isTypicalAnglePlank`. What this field carries is therefore the
  strongest fullness the producer can actually supply.

  **The exponent is `8η`.** It follows
  `Kakeya.ThinCase.ThinBall.fullness_bodies`, which is asserted at `δ^{3η}` in the structure's
  own index `η` (see that field for why `3η` is the honest value there) and is read by
  `Kakeya.VeryNotSticky.ThinConfig.tb` at the index `2 · cfg.η`, the (C5) exponent in the density clause, i.e. at `δ^{6η}`: the chain here is `δ^{2η}` from `hc` times
  `δ^{6η}` from (T2). This field has no term-level users, so nothing downstream spends it.

  **What that costs downstream.** `Kakeya.VeryNotSticky.transverseFill` asks the plank-to-slab
  reduction for a conclusion at `δ^{5η}`, and this field is not enough for it at *any* exponent
  `η'` at which the reduction may be invoked: the fullness hypothesis `(a')^{η'} ≤ λ` together
  with `a' ≤ C₀ δ^{1-τ-exscal}` forces `η' > 8η`, while the conclusion together with
  `a' ≥ δ^{1-exscal}` and `exscal < 1/2` forces `η' < 5η/2`. So restating this field was not a
  reformulation of the transverse input but the removal of it: the `(a')^η` form is now absent
  from the development, and `transverseFill` cannot be closed until it is threaded in from
  where the factoring bodies are produced. Its docstring carries the computation. -/
  hfull : cfg.δ ^ (8 * cfg.η) ≤ tc.C * ShadedBody.fullness sel YW
  /-- the typicality constant is a genuine multiplicative loss. Without it the aperture step
  `∠(n(S), n(W₁)) ≤ 2θ + Ctyp θ ≤ 3 Ctyp θ` of
  `Kakeya.VeryNotSticky.tangentialSlabFibreCount` (the slab clause (S3) read at `2θ`, the step is `0 ≤ 2θ (Ctyp - 1)`) fails, and that lemma's constant
  `Kakeya.VeryNotSticky.slabDecompFibreConstant`, which is `∝ Ctyp²`, degenerates to `0` at
  `Ctyp = 0` -/
  hCtyp1 : 1 ≤ Ctyp
  /-- the typicality constant is sub-polynomial in `δ⁻¹` -/
  hCtyp : Ctyp ≤ (cfg.δ ^ (1 - cfg.exscal)) ^ (-(cfg.η / 256))
  /-- the refinement has constant multiplicity with constant `Ctyp` -/
  hconst : ShadedBody.HasCConstantMultiplicity sel YW Ctyp
  /-- `θ` is typical for the refinement (blueprint `def:typicalAnglePlank`) -/
  htyp : Kakeya.IsTypicalPlankAngle sel YW P θ Ctyp
    (Real.toNNReal (Kakeya.plankAngleScaleA a'))
  /-- **(GWZ 6.13's transport datum) the plank-angle bound over each shade fibre at the
  *absolute* constant `1`**: for every shaded point, the maximal effective plank angle over the
  indices shading it is at most `θ` itself, with no constant.

  **This is not a new assumption. It is information the tree already derives and was throwing
  away.** It is the last conclusion clause of
  `Kakeya.findingTypicalAngleOfIntersection_perScale`, produced at `C = 1` in the rescaled
  coordinates, and until now it was consumed at the Section-6 → Section-9 interface by
  `Kakeya.VeryNotSticky.axisAngle_of_maxPlankAngleBound` — which spends it and returns only
  `hangle`, the **body**-axis form at the **non-absolute** `Ctyp` — and then discarded. The
  producer already has it in hand; this field records it.

  **Why the `Ctyp`-scaled clauses cannot replace it.** `htyp` above gives
  `Kakeya.HasMaxPlankAngleBound sel YW P θ Ctyp` through
  `Kakeya.IsTypicalPlankAngle.hasMaxPlankAngleBound`, and that is the wrong side: `Ctyp` is
  bounded only by `(δ')^{-η/256}` (`hCtyp`), which is *unbounded* as `δ → 0`, so no smallness
  hypothesis on `δ` recovers an absolute constant from it. GWZ 6.13's radius transport needs the
  angle controlled by `θ` alone; see
  `Kakeya.VeryNotSticky.effectivePlankAngle_le_of_hasMaxPlankAngleBound_one`, which is exactly
  what this field unlocks and what the `Ctyp` form does not give.

  It is recorded for the stored shading `YW` and the stored planks `P`, i.e. in the original
  coordinates; `Kakeya.VeryNotSticky.HasMaxPlankAngleBound.congr_image` is the transport that
  carries it there from the rescaled coordinates at the same constant, and it costs nothing —
  `Kakeya.HasMaxPlankAngleBound` sees a shading only through `shadeFibre`. -/
  hmaxAbs : Kakeya.HasMaxPlankAngleBound sel YW P θ 1
  /-- **Typicality read on the bodies** (blueprint `anglebound`): two bodies of `𝕎''_B`
  sharing a shaded point have normals at angle at most `C_{lem:ml2typicalangle} θ`.

  This is the display `\eqref{anglebound}` that the blueprint proof of
  `lem:ml2tangentialSlabFibreCount` opens with, and it is the only form in which that lemma
  uses typicality.

  **Why it is a field and not a consequence of `htyp`.** The blueprint identifies each body
  `W ∈ 𝕎''_B` with the plank enclosing `L_B(W)` and reads one angle off both. In Lean the two
  are distinct data and the identification is *not available*:

  * `htyp` bounds `Kakeya.effectivePlankAngle (P i) (P j)`, i.e. the angle between
    `(P i).basis 0` and `(P j).basis 0`;
  * `axisAngle (bd.Wb i) (bd.Wb j)` is the angle between `outerPrism.basis (bd.Wb i) 2` and
    `outerPrism.basis (bd.Wb j) 2`.

  The planks are produced by `Kakeya.VeryNotSticky.plankPresentation` through
  `Kakeya.VeryNotSticky.plankWindowEnclosure` and
  `Kakeya.Prism3D.exists_superset_of_hasThicknesses`, and that last one builds its prism on
  `(outerPrism.basis h3 hK hKne).reindex Fin.revPerm` for `K = L_B '' (bd.Wb j).carrier` — the
  frame of the *rescaled* body. So `(P j).basis 0` is the outer-prism normal of `L_B(W)`,
  while `axisAngle` reads that of `W`, and `Metric.outerPrism.basis` is choice-derived (a
  cluster point selected in `outerPrism.exists_limit`) with no equivariance under the
  homothety `L_B` and no rigidity: for a body two of whose affine thicknesses are comparable
  the witnessing frame is not determined even up to a small angle. Moreover the two existential
  statements between the construction and here discard the frame altogether, so no consumer of
  `plankPresentation` can name `(P j).basis` at all.

  The gap is *not* absorbable by a quantitative comparison. The enclosure
  `L_B '' (bd.Wb j).carrier ⊆ (P j).carrier` together with (C4) pins the two normals only to
  within an angle `≍ C(bd.C₀) · a/b`, and the aperture budget of
  `Kakeya.VeryNotSticky.tangentialSlabFibreCount` has no room for it: that lemma must reach
  `∠ ≤ 3 Ctyp δ^{-τ'} a/b` from `∠ ≤ 2θ + Ctyp θ` (the slab clause (S3) at `2θ`), and the only slack is `2 (Ctyp - 1) θ`, which vanishes at `Ctyp = 1`. So an
  additive `C(bd.C₀) a/b ≤ C(bd.C₀) θ` breaks the constant
  `Kakeya.VeryNotSticky.slabDecompFibreConstant` exactly.

  Recording `anglebound` here is therefore the faithful rendering: it is what the blueprint
  means by "θ is typical for `(𝕎''_B, Y_{𝕎''_B})`" when the family is read as bodies rather
  than as planks. The obligation lands on the producer
  `Kakeya.VeryNotSticky.exists_isTypicalAnglePlank`, which is proved and discharges it through
  `Kakeya.VeryNotSticky.axisAngle_of_maxPlankAngleBound`: the planks of its presentation are
  built on the frame of the body (`hbasis : (P i).basis = bodyFrame (Wb i)`), which is the
  route described next, and the field is returned at the constant `Ctyp` (that lemma asks
  `2 ≤ Ctyp`, and spends the absolute-constant form recorded as `hmaxAbs` above). The route:
  have `plankWindowEnclosure` build the plank on a *prescribed* frame, so that
  `plankPresentation` can hand it the frame of `bd.Wb j` itself, transported unchanged by the
  homothety `L_B`; then `(P j).basis 0 = NonSlab.bodyNormal (bd.Wb j)` on the nose and this
  field follows from `htyp`. -/
  hangle : ∀ x : EuclideanSpace ℝ (Fin 3), ∀ i ∈ sel, ∀ j ∈ sel,
    x ∈ (YW i).shade → x ∈ (YW j).shade →
      axisAngle (bd.Wb i) (bd.Wb j) ≤ (Ctyp : ℝ) * (θ : ℝ)
  /-- **(iv) The shaded plank family `(𝒫, Y_𝒫)`** (blueprint item (iv) of the conclusion of
  `lem:ml2typicalangle`).

  `ShadedPlank.reduction_to_slab_atTypicalAngle` consumes a plank family *with its shading
  attached*, and its refinement hypothesis `ShadedBody.IsCRefinement` demands the carriers of
  the refining family to be *equal* to the planks. The pair `(P, YW)` above cannot serve: `P`
  is a bare plank family and `YW` carries the original-coordinate bodies. So the producer
  hands over the packaged family as well; re-running
  `Kakeya.VeryNotSticky.plankPresentation` at the consumer would produce a *fresh* family and
  not the one the angle `θ` was found for. -/
  SP : bd.ω → ShadedPlank a' b' hab' hb1'
  /-- the planks of `SP` are the presentation `P`, so the windowedness `hwin` and the
  typicality `htyp` above are statements about `SP` as well -/
  hSP : ShadedPlank.planks SP = P
  /-- the shaded-body carriers of `SP` are the planks' own carriers -/
  hSPcarrier : ∀ i, ((SP i).carrier : Set (EuclideanSpace ℝ (Fin 3))) = (P i).carrier
  /-- **(v) The plank-carried refinement `Y''_𝒫`** (blueprint item (v) of the conclusion of
  `lem:ml2typicalangle`): the shading `YW` read at the plank carriers, which is the form
  `ShadedPlank.reduction_to_slab_atTypicalAngle` consumes. -/
  YP : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3))
  /-- `(𝒫, Y''_𝒫)` is a `C_{lem:ml2typicalangle}⁻¹`-refinement of `(𝒫, Y_𝒫)` -/
  hPrefine : ShadedBody.IsCRefinement sel YP sel (ShadedPlank.bodies SP) Ctyp⁻¹
  /-- `(𝒫, Y''_𝒫)` has `C_{lem:ml2typicalangle}`-constant multiplicity -/
  hPconst : ShadedBody.HasCConstantMultiplicity sel YP Ctyp
  /-- `θ` is typical for `(𝒫, Y''_𝒫)` -/
  hPtyp : Kakeya.IsTypicalPlankAngle sel YP (ShadedPlank.planks SP) θ Ctyp
    (Real.toNNReal (Kakeya.plankAngleScaleA a'))
  /-- **(GWZ 6.13's transport datum, at the plank-carried pair) the plank-angle bound over each
  shade fibre of `Y''_𝒫` at the *absolute* constant `1`.**

  `Kakeya.VeryNotSticky.TypicalAngleData.hmaxAbs` records the same datum for the *stored* pair
  `(P, YW)`, and that is **not** the pair the reduction is fired at:
  `Kakeya.VeryNotSticky.transverseFillPlankEstimate` applies
  `Kakeya.VeryNotSticky.CaseScale.transverseFill_threshold` at `(ShadedPlank.planks SP, YP)`, and no
  other field of this structure relates `YP` to `YW` — `hPrefine` refines `YP` against
  `ShadedPlank.bodies SP`, not against `YW`. So `hmaxAbs` does not reach the call site and this
  field is needed in addition to it, not instead of it.

  Like `hPtyp` beside it, it costs nothing at the producer: the constructor holds the
  rescaled-coordinate bound `hmax` and `YP` is built from the same shading, so
  `Kakeya.VeryNotSticky.shadedPlankOf_hasMaxPlankAngleBound` carries it across exactly as
  `Kakeya.VeryNotSticky.shadedPlankOf_isTypicalPlankAngle` carries `hPtyp`.

  **Why the `Ctyp`-scaled clause cannot replace it.** `hPtyp` gives
  `Kakeya.HasMaxPlankAngleBound sel YP (ShadedPlank.planks SP) θ Ctyp` through
  `Kakeya.IsTypicalPlankAngle.hasMaxPlankAngleBound`, and `Ctyp` is bounded only by
  `(δ')^(-(η/256))`, which is unbounded as `δ → 0`. Both consumers —
  `Plank.exists_slabCover_of_absoluteAngle`, which asks at the literal constant `2`, and
  `Plank.localAngleConcentration_of_preassemblyData`, whose angle constant is bound *before* the
  configuration — require a constant fixed before `a`. -/
  hmaxAbsP : Kakeya.HasMaxPlankAngleBound sel YP (ShadedPlank.planks SP) θ 1
  /-- **(O5) In the transverse case, the plank family is `(a')^η`-full**.

  This is the fullness hypothesis `λ(𝒫, Y) ≥ a^η` of GWZ Lemma 6.13 (`gwz.txt` l.979-980), the
  hypothesis of `ShadedPlank.reduction_to_slab_atTypicalAngle`, and it is *not* derivable from
  (T2) — GWZ (95), `λ ⪆ δ^{2η}` (l.2188): see `Kakeya.VeryNotSticky.TypicalAngleData.hfull`
  below for the computation showing that the two exponents differ by a positive power of `δ`.
  It is a mathematical input of the branch, owed by Configuration `hyp:ml2thinsetup`, and it
  reaches `Kakeya.VeryNotSticky.exists_isTypicalAnglePlank` as the clause
  `Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness`.

  It is asserted only under the transverse-case guard `δ^{-τ'} a/b ≤ θ` (GWZ l.2224), which is
  where GWZ invoke Lemma 6.13 and the only place this field is read
  (`Kakeya.VeryNotSticky.transverseFillPlankEstimate`, hypothesis `htrans`); the tangential
  leaf never reads it. With `hθ1` the guard yields `δ^{-τ'} a/b ≤ 1`, the guard of the
  `CaseScale` clause, which is how the producer discharges this field. -/
  hfullP : cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ θ →
    a' ^ (16 * cfg.η) ≤ ShadedBody.fullness sel (ShadedPlank.bodies SP)
  /-- the multiplicity of the plank family at the rescaled scale `δ' = δ/r₁` -/
  hmultP : ((cfg.δ / cfg.r₁ : NNReal) : ENNReal) ^ (-(16 * cfg.η)) ≤
    ShadedBody.multiplicity sel (ShadedPlank.bodies SP)
  /-- the middle plank dimension is comparable to `b / r₁` from below, with the constant
  `C₀` of (C4); this is what `Kakeya.VeryNotSticky.transverseFillTransport` consumes as its
  hypothesis `hcomp`, the radius `θ b` being reached from the transported radius
  `r₁ θ b'` only up to that constant -/
  hb'lower : bd.C₀⁻¹ * (cfg.b / cfg.r₁) ≤ b'
  /-- the rescaled scale is at most the short plank dimension -/
  hδa' : cfg.δ / cfg.r₁ ≤ a'
  /-- the short plank dimension is less than one -/
  ha'1 : a' < 1
  /-- the cardinality bridge, with the constant and the exponent both fixed before the scale;
  this is `Kakeya.VeryNotSticky.plankCard` after the tenth clause `plankCard_bias` has paid
  for `C_bias` and the conversion `δ^{-3ϱ} ≤ (δ')^{-6ϱ}` has moved the remaining power to the
  rescaled scale -/
  hcard : (sel.card : NNReal) ≤ plankCardConstant *
    (cfg.δ / cfg.r₁ : NNReal) ^ (-(plankCardExponent + 6 * cfg.ϱ))
  /-- **The rescaling bridge at the unrefined plank family, in subset form** (blueprint
  `plankRescalingBridge`).

  A subfamily of `(𝒫, Y_𝒫)` — recorded through its shadings alone, since
  `ShadedPlank.reduction_to_slab_atTypicalAngle` produces it with the *plank* carriers —
  pulls back to a subfamily of `(𝕊*, Y_{𝕎'_B})`, transporting local volume estimates with the
  radii multiplied by `2 r₁`, the normalizing scale of the plank presentation (the shaded
  bodies of the factoring proposition are enlargements of the geometric bodies of (C4) and do
  not fit in `B̄(ctr, r₁)`; see `Kakeya.VeryNotSticky.plankPresentation`).

  This is the level the reduction's output lives at: that lemma concludes
  `ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y)`, i.e. a refinement of the *base*
  family `(𝒫, Y_𝒫)` and not of the refined `(𝒫, Y''_𝒫)`, so `hbridgeP` below does not apply
  to it. No mass clause is carried, for the same reason: the reduction bounds `|s'|` and
  `λ(s', Y')` from below only by the constants `cP` and `cLam`, which it quantifies
  existentially with no sub-polynomial bound on their reciprocals. -/
  hbridgeP0 : ∀ (t : Finset bd.ω) (Z : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3))),
    t ⊆ sel → (∀ i ∈ t, (Z i).shade ⊆ (ShadedPlank.bodies SP i).shade) →
    ∃ Z' : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)),
      (∀ i ∈ t, (Z' i).shade ⊆ ((tc.thinBall hB).W i).shade) ∧
      ∀ (x' : EuclideanSpace ℝ (Fin 3)) (r' R' : ℝ) (K : ENNReal),
        K * MeasureTheory.volume (Metric.closedBall x' r') ≤
          MeasureTheory.volume (ShadedBody.iUnionShade t Z ∩ Metric.closedBall x' R') →
        ∃ x : EuclideanSpace ℝ (Fin 3),
          K * MeasureTheory.volume (Metric.ball x (2 * (cfg.r₁ : ℝ) * r')) ≤
            MeasureTheory.volume
              (ShadedBody.iUnionShade t Z' ∩ Metric.ball x (2 * (cfg.r₁ : ℝ) * R'))
  /-- **The rescaling bridge at the refined plank family, in subset form** (blueprint
  `plankRescalingBridge`, second level): a further refinement of `(𝒫, Y''_𝒫)` pulls back to a
  `c₂`-refinement of `(𝕊*, Y_{𝕎''_B})` transporting local volume estimates. It is the fourth
  clause of `Kakeya.VeryNotSticky.PlankPresentationData.hbridge`, instantiated at the very
  refinement that produced `YW`, which is why it can speak about `YW` and not merely about a
  fresh pull-back. -/
  hbridgeP : ∀ (c₂ : NNReal) (t : Finset bd.ω)
    (Z : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3))),
    t ⊆ sel → (∀ i ∈ t, (Z i).shade ⊆ (YP i).shade) →
    (c₂ : ENNReal) * (∑ i ∈ sel, MeasureTheory.volume (YP i).shade) ≤
      ∑ i ∈ t, MeasureTheory.volume (Z i).shade →
    ∃ Z' : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)),
      ShadedBody.IsCRefinement t Z' sel YW c₂ ∧
      (∀ i ∈ t, (Z' i).shade ⊆ (YW i).shade) ∧
      ∀ (x' : EuclideanSpace ℝ (Fin 3)) (r' R' : ℝ) (K : ENNReal),
        K * MeasureTheory.volume (Metric.closedBall x' r') ≤
          MeasureTheory.volume (ShadedBody.iUnionShade t Z ∩ Metric.closedBall x' R') →
        ∃ x : EuclideanSpace ℝ (Fin 3),
          K * MeasureTheory.volume (Metric.ball x (2 * (cfg.r₁ : ℝ) * r')) ≤
            MeasureTheory.volume
              (ShadedBody.iUnionShade t Z' ∩ Metric.ball x (2 * (cfg.r₁ : ℝ) * R'))

namespace TypicalAngleData

variable {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {tc : ThinConfig cfg bd} {B : bd.bι}
  {hB : B ∈ bd.bs} {τ' : ℝ}

/-- The angle clause read at the aspect ratio `a/b` of the factoring bodies, which is the
form the tangential case uses. -/
lemma hθab' (ta : TypicalAngleData cfg tc hB τ') : cfg.a / cfg.b ≤ ta.θ :=
  ta.hratio ▸ ta.hθab

end TypicalAngleData

end Kakeya.VeryNotSticky
