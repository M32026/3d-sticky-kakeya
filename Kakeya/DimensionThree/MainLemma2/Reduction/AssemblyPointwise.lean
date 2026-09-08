/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.Assembly
public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyUniform
public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyClosed

/-!
# `GWZ Lemma 9.1 ⟹ GWZ Main Lemma 2` — the *pointwise* assembly

`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_frostmanEstimate_of_lemma91`
(`Reduction/Assembly.lean`) derives the protected Main Lemma 2 from **three** hypotheses:

1. `Kakeya.ML2Assembly.Lemma91Uniform`, the `β`-uniform *strengthening* of the protected GWZ
   Lemma 9.1;
2. `Kakeya.ML2Assembly.GeometricCore`, stated over a window `[β₀,1]`;
3. the small-cardinality case `Kakeya.ML2Assembly.SmallCard`.

This module derives the same conclusion from **two**, dropping (1) outright and keeping (3)
*definitionally unchanged* (`Kakeya.ML2Assembly.SmallCardHyp` below is the third binder of the
three-hypothesis assembly, copied verbatim; the `example` immediately after it feeds that very
binder and so is the compiler's own proof that the two slots have the same type).

## Why (1) can go, and why it cannot go alone

`Kakeya.VNSUniform.mainLemma2Statement_of_pointwise_drop` manufactures the `MonotoneOn ν` clause
of Main Lemma 2 out of `Kakeya.VNSUniform.estimateSet_shape` — the estimate set
`A = {β ∈ (0,1] | K_KT β ∧ K_F β}` is a nonempty up-set containing its own infimum — so only a
*pointwise* drop is needed and no uniformity in `β` is required anywhere.  That is what makes (1)
removable; `Kakeya.VNSUniform.no_monotoneOn_drop_of_open_threshold` shows in the other direction
that uniformity of Lemma 9.1 could never have been the whole story, since in the one shape of `A`
that `estimateSet_shape` excludes the protected conclusion is outright false.

Removing (1) **alone** buys nothing, and this is the load-bearing point.  The field
`Kakeya.ML2Assembly.Lemma91Params.body` reads

  `∀ ζ, 0 < ζ → ∀ β ∈ Set.Icc β₀ 1, VNSBody β ϖ ζ (gain ζ) (dens ζ)`,

so even instantiated at `β₀ = β` it still demands the whole window `[β,1]`.  Hence
`Kakeya.ML2Assembly.GeometricCore` as written cannot be fed by the non-uniform, protected Lemma
9.1, and plugging it into the pointwise reduction removes no obligation.  The window has to come
out of the geometric interface as well, which is what `Kakeya.ML2Assembly.Lemma91ParamsAt`,
`Kakeya.ML2Assembly.GeometricCoreAt` and `Kakeya.ML2Assembly.PointwiseCore` are for.  Restating
that interface is free: `GeometricCore` has no producer anywhere in the tree.

## Nothing is relocated into a harder place

`Kakeya.ML2Assembly.pointwiseCore_of_lemma91Uniform_of_geometricCore` proves

  `Lemma91Uniform → GeometricCore → PointwiseCore`,

i.e. the single new obligation is *implied by the pair it replaces*.  The difficulty is therefore
weakened, not moved.  In the other direction `Kakeya.ML2Assembly.exists_lemma91ParamsAt` proves
that the per-exponent parameter package is available with **no hypothesis at all**: it is
Skolemised out of the protected `Kakeya.multiplicity_le_of_card_isEssDistinct_ge`, consumed here
as a *term*.  So a producer of `Kakeya.ML2Assembly.GeometricCoreAt` really is handed GWZ Lemma
9.1's data at the exponent it is working at, and
`Kakeya.ML2Assembly.pointwiseCore_of_geometricCoreAt` converts that into `PointwiseCore` for free.

## What is *not* changed

* the protected Main Lemma 2 statement: the conclusion below is `∃ ν, …` written out, and it is
  pinned to `Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate` by the tripwires in
  `Kakeya/DimensionThree/MainLemma2Ptw.lean` (this module cannot carry them itself, because
  `Kakeya.DimensionThree.MainLemma2` still routes through the abandoned Wang--Zahl subtree and
  `Reduction/` must stay clear of it);
* the small-cardinality hypothesis, which is `Kakeya.ML2Assembly.SmallCardHyp`, definitionally the
  third binder of the three-hypothesis assembly;
* the substance of the geometric core — GWZ Lemma 7.7(B), Theorem 7.3(B), the two-scale split, the
  rescaling and the eccentric/non-eccentric analysis are untouched;
* GWZ Lemma 9.1's own open leaf (`Kakeya.VeryNotSticky.exists_setup_caseSideData`).

## The prose obstruction in `Reduction/Assembly.lean` is refuted here, in the kernel

The docstring of `Kakeya.ML2Assembly.Lemma91Uniform` argues that per-`β` drops "never assemble
into a uniform one by pure analysis".  They do:
`Kakeya.ML2Assembly.katzTaoDropSet_nonempty_of_pointwiseDrop` derives that docstring's own
predicate, `Kakeya.ML2Reduction.katzTaoDropSet β₀ ≠ ∅` for every `β₀ ∈ (0,1]`, from the pointwise
drop alone.  The prose counts what `Kakeya.KatzTaoEstimate.mono` does to the *hypotheses* of a drop
and omits what it does to the *conclusion*: a drop at `b` serves every exponent `≥ b` at the full
drop, so the induced cover of `[β₀,1]` is by right rays, not by left neighbourhoods, and one ray
suffices.  Consequently `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_pointwiseCore_via_envelope`
reaches the protected statement through `Reduction/Envelope.lean` as well, from the same two
hypotheses: deleting `Lemma91Uniform` strands neither route.

## Additivity

Nothing in `Reduction/Assembly.lean` is edited or removed by this module.  With it in place the
following become unreachable from the two-hypothesis route and are candidates for deletion once
the wider Section-9 sequencing allows:
`Kakeya.ML2Assembly.Lemma91Uniform`, `Lemma91Params`, `exists_lemma91Params`,
`lemma91_of_lemma91Uniform`, `isSpine_mono_beta`, and Part 1 of
`Kakeya/DimensionThree/MainLemma2/VeryNotStickyUniform.lean` (with it the
`UniformPlankExponent` / `@[irreducible] Classical.choose plankFrostmanExponent` blocker).
-/

@[expose] public section

open MeasureTheory Topology Filter ShadedBody ConvexSpaceBody

namespace Kakeya.ML2Assembly

universe u

/-! ## GWZ Lemma 9.1 as a term -/

/-- **GWZ Lemma 9.1, as a term rather than a hypothesis.**

`Kakeya.ML2Assembly.Lemma91` is the conclusion of the protected
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge` with every binder written out, and
`Reduction/Assembly.lean` already pins the two together with an anonymous `example`.  That
`example` cannot be applied, so the assembly could not consume it; this is the same fact as a
named theorem, and it is what lets the pointwise route use Lemma 9.1 without assuming it.

It is also the **one line to edit** if Lemma 9.1 is strengthened.  Strengthening is permitted —
extra conclusion clauses may be added when a consumer provably needs them — and it changes the
shape of the existential, breaking any `obtain` pattern written against it.  Routing the pointwise
reduction through this single term confines that breakage here. -/
theorem lemma91 : Lemma91.{u} :=
  fun _β hβ hβ1 ↦ Kakeya.multiplicity_le_of_card_isEssDistinct_ge hβ hβ1

/-! ## The parameters of Lemma 9.1 at a single exponent -/

/-- The parameter package of GWZ Lemma 9.1 **at one exponent `β`**: the window exponent `ϖ` and
the two exponent *functions* `gain = ν(β,·)`, `dens = η(β,·)` that `Kakeya.ML2Spine.IsSpine` is
stated against.

This is `Kakeya.ML2Assembly.Lemma91Params` with the window `Set.Icc β₀ 1` of its `body` field
collapsed to the single point `β` — see
`Kakeya.ML2Assembly.lemma91ParamsAt_of_lemma91Params`, which shows that no information is lost by
pointwise-ing the interface: the uniform package is exactly this one, held at every `β` of its
window. -/
structure Lemma91ParamsAt (β ϖ : ℝ) (gain dens : ℝ → ℝ) : Prop where
  /-- The window exponent is positive. -/
  window_pos : 0 < ϖ
  /-- The gain function is positive on positive tolerances. -/
  gain_pos : ∀ ζ : ℝ, 0 < ζ → 0 < gain ζ
  /-- The density function is positive on positive tolerances. -/
  dens_pos : ∀ ζ : ℝ, 0 < ζ → 0 < dens ζ
  /-- **The centring margin** (refined proof l.5987 `q = min{a₀/10, ν₀/100, ε_out/100}` and l.6089
  `4q ≤ η₀`): the density exponent leaves room for four times the preparation exponent
  `q = gain ζ / 100`.  It is what lets the reduction hand Lemma 9.1 a *centred* family: the
  canonical cover's fibre is bounded by `Δ_max` (l.4812 with l.5996–6002), so the centring's
  multiplicity loss and the density it consumes are the same exponent, and the site can only supply
  it by reading `Lemma91At` at `ηd := q + cst` (`Kakeya.ML2Reduction.Lemma91At.mono_dens`).  It is
  **not** a property of Lemma 9.1 — the gain is shrunk to arrange it, at no cost, in
  `Kakeya.ML2Assembly.exists_lemma91ParamsAt`. -/
  gain_le_dens : ∀ ζ : ℝ, 0 < ζ → gain ζ / 25 ≤ dens ζ
  /-- At every tolerance the body of Lemma 9.1 holds at `β` with these three exponents. -/
  body : ∀ ζ : ℝ, 0 < ζ → VNSBody.{u} β ϖ ζ (gain ζ) (dens ζ)

/-- The `β`-uniform package is *literally* the per-exponent package, held at every exponent of its
window.  So the pointwise interface asks for no more than the uniform one delivers at each point,
and pointwise-ing loses nothing. -/
theorem lemma91ParamsAt_of_lemma91Params {β₀ ϖ : ℝ} {gain dens : ℝ → ℝ}
    (h : Lemma91Params.{u} β₀ ϖ gain dens) {β : ℝ} (hβ : β ∈ Set.Icc β₀ 1) :
    Lemma91ParamsAt.{u} β ϖ gain dens :=
  ⟨h.window_pos, h.gain_pos, h.dens_pos, h.gain_le_dens, fun ζ hζ ↦ h.body ζ hζ β hβ⟩

/-- **The parameters of GWZ Lemma 9.1, packaged as functions — with no hypothesis.**

Skolemisation of the protected `Kakeya.multiplicity_le_of_card_isEssDistinct_ge` at one exponent,
routed through `Kakeya.ML2Assembly.lemma91`.  Unlike `Kakeya.ML2Assembly.exists_lemma91Params`,
which needs the assumed `Kakeya.ML2Assembly.Lemma91Uniform`, this theorem assumes nothing: Lemma
9.1 is consumed as a term, so every consumer of `Kakeya.ML2Assembly.Lemma91ParamsAt` is consuming
GWZ Lemma 9.1 itself. -/
theorem exists_lemma91ParamsAt {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ (ϖ : ℝ) (gain dens : ℝ → ℝ), Lemma91ParamsAt.{u} β ϖ gain dens := by
  classical
  obtain ⟨ϖ, hϖ, hζ⟩ := lemma91.{u} β hβ hβ1
  refine ⟨ϖ, fun ζ ↦ if hz : 0 < ζ then
      min ((hζ ζ hz).choose) (25 * ((hζ ζ hz).choose_spec.2).choose) else 1,
    fun ζ ↦ if hz : 0 < ζ then ((hζ ζ hz).choose_spec.2).choose else 1, hϖ, ?_, ?_, ?_, ?_⟩
  · intro ζ hz
    simp only [dif_pos hz]
    have hν := (hζ ζ hz).choose_spec.1
    have hη := ((hζ ζ hz).choose_spec.2).choose_spec.1
    exact lt_min hν (by linarith)
  · intro ζ hz
    simp only [dif_pos hz]
    exact ((hζ ζ hz).choose_spec.2).choose_spec.1
  · intro ζ hz
    simp only [dif_pos hz]
    have hmin := min_le_right ((hζ ζ hz).choose)
      (25 * ((hζ ζ hz).choose_spec.2).choose)
    linarith
  · intro ζ hz
    simp only [dif_pos hz]
    exact VNSBody.mono_gain (min_le_left _ _)
      (((hζ ζ hz).choose_spec.2).choose_spec.2)

/-! ## The geometric core, restated pointwise -/

/-- **The geometric core of the GWZ reduction, at one exponent.**

`Kakeya.ML2Assembly.GeometricCore` with the window `[β₀,1]` collapsed to the single exponent `β`:
the Katz--Tao exponent `ε₁` of Theorem 7.3(B) and the density exponent `η` may be chosen *after*
`β`, and the input package is the per-exponent `Kakeya.ML2Assembly.Lemma91ParamsAt`, which the
**protected**, non-uniform Lemma 9.1 supplies (`Kakeya.ML2Assembly.exists_lemma91ParamsAt`).

Everything else is as in `Kakeya.ML2Assembly.GeometricCore`: the drop is
`Kakeya.ML2Spine.spineNu β ϖ ε₁ gain dens`, which has **no `ε` argument**, Theorem 7.3(B) is read
at the absolute accuracy `Kakeya.ML2Spine.absAccuracy β = β/2`, and the gain asked of the window
branch is `4` times the drop, the `4` being the exponent of the crude cardinality bound
`Kakeya.ML2Assembly.card_le_rpow_neg_four`.

The two hypotheses `K_KT β` and `K_F β` are in the statement because every geometric input of the
chain consumes them; they are exactly what is available at the point of use. -/
def GeometricCoreAt : Prop :=
  ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 → Lemma91ParamsAt.{u} β ϖ gain dens →
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      Dichotomy.{u} β (β / 2) (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) η

/-- **The single geometric obligation of the pointwise route.**

At every exponent `β ∈ (0,1]` where both partial estimates hold, produce an `ε`-free drop `c > 0`
inside the budget `2c ≤ β`, together with a density exponent `η` for which the GWZ dichotomy
`Kakeya.ML2Assembly.Dichotomy` holds at absolute accuracy `β/2` and gain `4c`.

This is deliberately *not* parameterised by Lemma 9.1's exponents: a producer may obtain them for
itself, with no hypothesis, from `Kakeya.ML2Assembly.exists_lemma91ParamsAt`, and
`Kakeya.ML2Assembly.pointwiseCore_of_geometricCoreAt` is that route.  Stating the obligation this
way is what makes it *implied by the pair it replaces*
(`Kakeya.ML2Assembly.pointwiseCore_of_lemma91Uniform_of_geometricCore`).

There is no `ε` binder here, and none in `Kakeya.ML2Assembly.Dichotomy`, so the drop is still
chosen before the accuracy, per Prof. Hong Wang's clarification of 2026-08-30;
`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy` refutes the alternative reading. -/
def PointwiseCore : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 1 →
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    ∃ c : ℝ, 0 < c ∧ 2 * c ≤ β ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      Dichotomy.{u} β (β / 2) (4 * c) η

/-- **The `β`-parameterised pointwise core gives the abstract one**, with GWZ Lemma 9.1 supplying
the parameter package as a term and `Kakeya.ML2Spine.spineNu` supplying the drop.  The two budgets
`0 < c` and `2c ≤ β` are `Kakeya.ML2Spine.spineNu_pos` and `Kakeya.ML2Spine.two_spineNu_le`. -/
theorem pointwiseCore_of_geometricCoreAt (h : GeometricCoreAt.{u}) : PointwiseCore.{u} := by
  intro β hβ hβ1 hKT hKF
  obtain ⟨ϖ, gain, dens, hp⟩ := exists_lemma91ParamsAt.{u} hβ hβ1
  obtain ⟨ε₁, hε₁, η, hη0, hη1, hdich⟩ := h β ϖ gain dens hβ hβ1 hp hKT hKF
  exact ⟨ML2Spine.spineNu β ϖ ε₁ gain dens,
    ML2Spine.spineNu_pos hβ hp.window_pos hε₁ hp.gain_pos hp.dens_pos,
    ML2Spine.two_spineNu_le hβ hβ1 hp.window_pos hε₁ hp.gain_pos hp.dens_pos,
    η, hη0, hη1, hdich⟩

/-- **The new obligation is implied by the two it replaces.**

`Kakeya.ML2Assembly.Lemma91Uniform` together with the windowed
`Kakeya.ML2Assembly.GeometricCore` produce `Kakeya.ML2Assembly.PointwiseCore`.  So dropping the
uniform companion and pointwise-ing the geometric interface is a **weakening** of the residue, not
a trade: no difficulty is relocated into a deeper or harder place.

The window is collapsed by instantiating the old core at `β₀ = β`, where `Set.Icc β 1` contains
`β` by `le_rfl`. -/
theorem pointwiseCore_of_lemma91Uniform_of_geometricCore
    (h91 : Lemma91Uniform.{u}) (hcore : GeometricCore.{u}) : PointwiseCore.{u} := by
  intro β hβ hβ1 hKT hKF
  obtain ⟨ϖ, gain, dens, hp⟩ := exists_lemma91Params h91 hβ hβ1
  obtain ⟨ε₁, hε₁, hdich⟩ := hcore β ϖ gain dens hβ hβ1 hp
  obtain ⟨η, hη0, hη1, hd⟩ := hdich β ⟨le_rfl, hβ1⟩ hKT hKF
  exact ⟨ML2Spine.spineNu β ϖ ε₁ gain dens,
    ML2Spine.spineNu_pos hβ hp.window_pos hε₁ hp.gain_pos hp.dens_pos,
    ML2Spine.two_spineNu_le hβ hβ1 hp.window_pos hε₁ hp.gain_pos hp.dens_pos,
    η, hη0, hη1, hd⟩

/-! ## The small-cardinality hypothesis, unchanged -/

/-- **The third binder of `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_frostmanEstimate_of_lemma91`,
copied verbatim.**

Naming it changes nothing: the `example` immediately below feeds a term of this type into that
very binder of the three-hypothesis assembly, so the compiler certifies that the pointwise route
asks for the small-cardinality case at exactly the same strength — not a stronger stand-in, and
not a weaker one either. -/
def SmallCardHyp : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 1 →
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    ∀ γ : ℝ, β / 2 ≤ γ → γ < β → SmallCard.{u} γ

/-- **Fidelity compatibility for the small-cardinality hypothesis.**  If
`Kakeya.ML2Assembly.SmallCardHyp` ever drifts from the third binder of the three-hypothesis
assembly, this stops compiling. -/
example (h91 : Lemma91Uniform.{u}) (hcore : GeometricCore.{u}) (hsmall : SmallCardHyp.{u}) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β) :=
  katzTaoEstimate_sub_of_frostmanEstimate_of_lemma91 h91 hcore hsmall

/-! ## The old envelope interface, discharged from the same two hypotheses -/

/-- **The pointwise drop**, as a named `Prop`: at every exponent where both partial estimates
hold, *some* positive drop is available.  Nothing here is uniform in `β` — neither the drop nor any
of Lemma 9.1's exponents — and this is exactly the hypothesis of
`Kakeya.VNSUniform.mainLemma2Statement_of_pointwise_drop`, named so that it can be quantified over
and fed to more than one consumer. -/
def PointwiseDrop : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 1 →
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    ∃ d : ℝ, 0 < d ∧ KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - d)

/-- **The two hypotheses of this module produce the pointwise drop.**

One application of `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` at the exponent in hand:
the geometric obligation supplies the drop `c`, the budget `2c ≤ β` and the dichotomy at gain `4c`,
and the small-cardinality hypothesis supplies its other branch at `γ = β - c`, which is in
`[β/2, β)` because `0 < c` and `2c ≤ β`. -/
theorem pointwiseDrop_of_pointwiseCore (hcore : PointwiseCore.{u}) (hsmall : SmallCardHyp.{u}) :
    PointwiseDrop.{u} := by
  intro β hβ hβ1 hKT hKF
  obtain ⟨c, hc, h2c, η, hη0, hη1, hdich⟩ := hcore β hβ hβ1 hKT hKF
  exact ⟨c, hc, katzTaoEstimate_sub_of_dichotomy hc h2c hη0 hη1 le_rfl hdich
    (hsmall β hβ hβ1 hKT hKF (β - c) (by linarith) (by linarith))⟩

/-- **The uniform drop set of `Reduction/Envelope.lean` is nonempty above every threshold, given
only the pointwise drop.**

This is the refutation of the prose obstruction carried by the docstring of
`Kakeya.ML2Assembly.Lemma91Uniform` (`Reduction/Assembly.lean`), and it is stated against that
docstring's own predicate, `Kakeya.ML2Reduction.katzTaoDropSet`, not against a paraphrase.  The
docstring asserts that "per-`β` drops never assemble into a uniform one by pure analysis"; they do.

Where the prose goes wrong: it counts what `Kakeya.KatzTaoEstimate.mono` does to the *hypotheses*
of a drop and omits what it does to the *conclusion*.  Since
`KatzTaoEstimate.mono : a ≤ b → K_KT a → K_KT b`, a drop established at `b` yields `K_KT x` for
every `x ≥ b - d`, so it serves every exponent `≥ b` at the **full** drop and with no loss.  The
induced cover of `[β₀,1]` is therefore by right rays `[b,1]`, not by the left neighbourhoods
`[b - c b, b]` the docstring describes, and a cover by right rays of a set with a least element has
a one-element subcover.

The least element is supplied by `Kakeya.VNSUniform.estimateSet_shape`: the estimate set
`A = {β ∈ (0,1] | K_KT β ∧ K_F β}` either is all of `(0,1]` — in which case every drop is
admissible and `β₀/2` will do — or contains its own infimum `m`, and then **one** application of
the pointwise drop, at `m`, serves the whole window.  The witness is `min d (β₀/2)`, the `β₀/2`
only to land inside `(0,1]` and to keep the drop below the exponent. -/
theorem katzTaoDropSet_nonempty_of_pointwiseDrop (h : PointwiseDrop.{u}) :
    ∀ β₀ ∈ Set.Ioc (0 : ℝ) 1, (ML2Reduction.katzTaoDropSet.{u} β₀).Nonempty := by
  rintro β₀ ⟨hβ₀, hβ₀1⟩
  rcases Kakeya.VNSUniform.estimateSet_shape.{u} with hall | ⟨m, hm, hm1, hKTm, hFm, hleast⟩
  · refine ⟨β₀ / 2, ⟨by linarith, by linarith⟩, ?_⟩
    rintro β ⟨hβ0, hβ1⟩ _ _
    exact hall (β - β₀ / 2) (by linarith) (by linarith)
  · obtain ⟨d, hd, hKTd⟩ := h m hm hm1 hKTm hFm
    refine ⟨min d (β₀ / 2), ⟨lt_min hd (by linarith), by
      have := min_le_right d (β₀ / 2); linarith⟩, ?_⟩
    rintro β ⟨hβ0, hβ1⟩ hKT hF
    have hmβ : m ≤ β := hleast β (by linarith) hβ1 hKT hF
    refine KatzTaoEstimate.mono ?_ hKTd
    have : min d (β₀ / 2) ≤ d := min_le_left _ _
    linarith

/-- **The envelope route of `Reduction/Envelope.lean` also closes from the two hypotheses.**

So deleting `Kakeya.ML2Assembly.Lemma91Uniform` strands nothing: the `MonotoneOn ν` bookkeeping
can still be done through `Kakeya.ML2Reduction.katzTaoEstimate_sub_of_nonempty_katzTaoDropSet`,
which is the route the three-hypothesis assembly takes, with the uniformity supplied by
`Kakeya.VNSUniform.estimateSet_shape` instead of by a strengthening of Lemma 9.1.  This theorem
and `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_frostmanEstimate_of_pointwiseCore` prove the same
statement by the two different routes. -/
theorem katzTaoEstimate_sub_of_pointwiseCore_via_envelope
    (hcore : PointwiseCore.{u}) (hsmall : SmallCardHyp.{u}) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β) :=
  ML2Reduction.katzTaoEstimate_sub_of_nonempty_katzTaoDropSet.{u}
    (katzTaoDropSet_nonempty_of_pointwiseDrop (pointwiseDrop_of_pointwiseCore hcore hsmall))

/-! ## The assembly, from two hypotheses -/

/-- **GWZ Lemma 9.1 ⟹ GWZ Main Lemma 2, from two hypotheses.**

The conclusion is, verbatim, the statement of the protected
`Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate`; the tripwires that pin it to the
protected declaration are in `Kakeya/DimensionThree/MainLemma2Ptw.lean`.  GWZ Lemma 9.1 is **not**
a hypothesis here: it is consumed as a term wherever it is needed
(`Kakeya.ML2Assembly.exists_lemma91ParamsAt`, reached through
`Kakeya.ML2Assembly.pointwiseCore_of_geometricCoreAt`).

The two hypotheses are

* `hcore`, the single geometric obligation `Kakeya.ML2Assembly.PointwiseCore`;
* `hsmall`, the small-cardinality case `Kakeya.ML2Assembly.SmallCardHyp`, definitionally the same
  binder the three-hypothesis assembly takes.

The `MonotoneOn ν` clause — the sole reason the three-hypothesis assembly needed
`Kakeya.ML2Assembly.Lemma91Uniform` — is discharged by
`Kakeya.VNSUniform.mainLemma2Statement_of_pointwise_drop`, i.e. by
`Kakeya.VNSUniform.estimateSet_shape`, and not by any uniformity of Lemma 9.1. -/
theorem katzTaoEstimate_sub_of_frostmanEstimate_of_pointwiseCore
    (hcore : PointwiseCore.{u}) (hsmall : SmallCardHyp.{u}) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β) :=
  Kakeya.VNSUniform.mainLemma2Statement_of_pointwise_drop.{u}
    (pointwiseDrop_of_pointwiseCore hcore hsmall)

/-- **The same, from the `β`-parameterised pointwise core.**  This is the form a producer working
inside the GWZ chain will meet: it is handed the exponents `(ϖ, gain, dens)` that the protected
Lemma 9.1 supplies at `β`, and owes the dichotomy at gain `4 · spineNu`. -/
theorem katzTaoEstimate_sub_of_frostmanEstimate_of_geometricCoreAt
    (hcore : GeometricCoreAt.{u}) (hsmall : SmallCardHyp.{u}) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β) :=
  katzTaoEstimate_sub_of_frostmanEstimate_of_pointwiseCore
    (pointwiseCore_of_geometricCoreAt hcore) hsmall

/-- **The three-hypothesis route factors through the two-hypothesis one.**  Anything the old
assembly could prove, the new one proves from strictly less: this is
`Kakeya.ML2Assembly.pointwiseCore_of_lemma91Uniform_of_geometricCore` read as a statement about
the two assemblies, and it is the check that the reduction from three obligations to two is a
weakening and not a rewrite. -/
example (h91 : Lemma91Uniform.{u}) (hcore : GeometricCore.{u}) (hsmall : SmallCardHyp.{u}) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β) :=
  katzTaoEstimate_sub_of_frostmanEstimate_of_pointwiseCore
    (pointwiseCore_of_lemma91Uniform_of_geometricCore h91 hcore) hsmall

end Kakeya.ML2Assembly
