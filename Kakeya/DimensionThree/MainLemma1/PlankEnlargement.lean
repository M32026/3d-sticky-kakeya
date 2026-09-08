/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.PlankTube
public import Kakeya.Tube.Dilate

/-!
# Main Lemma 1: the plank case of the enlargement lemma

This file holds the single plank-level statement of the repaired plank case of GWZ's Lemma 3.1,
`Kakeya.ml1Boot.subset_dilate_rescale_of_thickness_le` (blueprint
`lem:ml1bootEnlargementPlank`).  It is the only member of that group naming a dimension and a
thickness; the seven tube- and vector-level statements it is assembled from live in
`Kakeya/Tube/Dilate.lean`, the tube-level core being
`Kakeya.Tube.subset_dilate_rescale_of_subset_dilate`.

## What was repaired, and into what shape

The plank case as the source states it — `K` an `a × b × 1` plank containing a unit-length tube
`T₀` lies in a concentric rescaling `T₀^{(C σ)}` — is **false** in the conventions of this
development, and blueprint `note:ml1bootEnlargementTubeStatus` records the retraction.  The
cause is the half-width convention: `Kakeya.IsPlankOfDimensions` makes an `a × b × 1` plank a
rectangular prism of *half*-widths `a, b, 1`, so its long axis has extent `2`, whereas
`Tube.rescale` keeps the unit core of `T₀` and so has longitudinal extent only `1 + 2 r`.  An
endpoint of the plank stands at distance `1 / 2` from the core, forcing `r ≥ 1 / 2` however
small `σ` is: the failure is longitudinal and of size `Θ(1)`, so no constant absorbs it.

What stands in its place is a statement of a **different shape**: a homothety by `Λ = 8 Λ₀` of a
concentric rescaling at radius `3 Λ₀ σ`, i.e. a containment in
`Kakeya.Tube.dilate (T₀.rescale (3 * Λ₀ * σ)) (8 * Λ₀)`, a body of longitudinal extent `8 Λ₀` and
transverse radius `24 Λ₀² σ`, where `Λ₀ ≥ 1` is the normalization at which the first affine
thickness of `K` is bounded.  At `Λ₀ = 1` this is the absolute form
`Kakeya.Tube.dilate (T₀.rescale (3 * σ)) 8` of blueprint
`def:ml1bootEnlargementPlankConstant`.  Two things about that shape are not free, and blueprint
`def:ml1bootEnlargementPlankConstant` works out the witnesses: the conclusion cannot be
strengthened to a concentric rescaling `T₀^{(r)}` with `r = O(σ)`, and the radius factor may not
be read *after* the homothety.

## The circumradius gap, now closed

The hypothesis is `Metric.thickness ℝ K 0 ≤ Λ₀` and no longer `≤ 1`.  The fixed normalization `1`
asked `K` to sit in a ball of radius `1`, which an `a × b × 1` plank of
`Kakeya.IsPlankOfDimensions C a b` does **not** satisfy — its first affine thickness is its
circumradius `√(1 + a² + b²) > 1`.  That residual gap was of size `Θ(σ²)`, hence absorbable into
constants, and it is now absorbed: both generalizations blueprint `lem:ml1bootEnlargementPlank`
names are carried out — a general normalization `Λ₀` in
`Kakeya.ml1Boot.prism_subset_unitCoreTube` (and hence in `Kakeya.ml1Boot.subset_plankTube`) and a
general ratio `c` in `Kakeya.Tube.subset_dilate_rescale_of_subset_dilate`.  The plank predicate
asserts `τ₀ ≤ C` outright, so a plank is admitted at `Λ₀ = C`, `σ = C * b`.

## What this still does not discharge

The *shape* obstruction is untouched and is not a matter of constants: the output is a homothety,
and item `item:fibreStep5aBodies` of `note:ml1bootLowerFrostmanFibre` asks for a concentric
rescaling of a coarse node tube.  What has changed on the consumer side is that
`Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` — the local density bound (5.10a) — is now
stated at an arbitrary container, so *that* consumer no longer needs a rescale-shaped region and
can be read at the homothety this lemma produces.

The import of `Kakeya.Tube.Dilate` is deliberate and is *not* an oversight for `lake shake` to
remove: the proof below uses the tube-level core
`Kakeya.Tube.subset_dilate_rescale_of_subset_dilate` as its second input, alongside
`Kakeya.ml1Boot.subset_plankTube`.
-/

@[expose] public section

open MeasureTheory Metric

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Enlargement, plank case, in the homothety-then-rescale shape** (blueprint
`lem:ml1bootEnlargementPlank`, GWZ Lemma 3.1 plank case).

Let `K ⊆ ℝ³` be nonempty and compact with affine thicknesses `τ₀(K) ≤ Λ₀`, `τ₁(K) ≤ σ` and
`τ₂(K) ≤ σ` for some normalization `Λ₀ ≥ 1`, and let `T₀` be a tube of unit length and arbitrary
radius `σ₀` with `T₀ ⊆ K`.  Then

`K ⊆ (8 Λ₀) · (T₀^{(3 Λ₀ σ)})`,

a body of longitudinal extent `8 Λ₀` and transverse radius `24 Λ₀² σ`.  At `Λ₀ = 1` this is the
earlier statement `K ⊆ 8 · (T₀^{(3σ)})` verbatim (blueprint
`def:ml1bootEnlargementPlankConstant`).

Two steps and no fresh geometry.  `Kakeya.ml1Boot.subset_plankTube`, read with `C * b = σ` at the
normalization `Λ₀`, supplies a `σ`-tube `T` — the tube attached to `K` through its outer prism —
with `K ⊆ (2 Λ₀) · T`; then `Kakeya.Tube.subset_dilate_rescale_of_subset_dilate` at `δ = σ` and
ratio `c = 2 Λ₀` with the given `T₀` returns the claim.  Its two budgets are met with the
longitudinal one to spare and the transverse one on the nose:
`2 c = 4 Λ₀ ≤ 8 Λ₀ = Λ` and `6 c² σ = 24 Λ₀² σ = Λ · (3 Λ₀ σ)`.  The docstring of
`Kakeya.Tube.subset_dilate_rescale_of_subset_dilate` works out the two-case reading of the
transverse estimate that keeps it free of any upper bound on `σ`.

**The circumradius gap is now closed.**  The earlier fixed normalization `τ₀(K) ≤ 1` excluded a
genuine `a × b × 1` plank of `Kakeya.IsPlankOfDimensions C a b`, whose first affine thickness is
its circumradius `√(1 + a² + b²) > 1`; the plank predicate itself asserts `τ₀ ≤ C`, so such a
plank satisfies the hypotheses here at `Λ₀ = C` with `σ = C * b`, giving
`K ⊆ (8 C) · (T₀^{(3 C² b)})`.  Blueprint `note:ml1bootEnlargementTubeStatus` records the gap and
`lem:ml1bootEnlargementPlank` names the two generalizations — a general `Λ₀` in
`Kakeya.ml1Boot.prism_subset_unitCoreTube` and a general ratio `c` in the tube-level core — that
absorb it; both are now carried out.

One bookkeeping point for whoever proves this.  `Kakeya.ml1Boot.plankTube` is indexed by the
*product* of its two arguments, `plankTube hdim C b hW hWne : Tube (C * b) E`, so the natural
instantiation `C = 1`, `b = σ` — the one matching the hypotheses `τ₁(K), τ₂(K) ≤ σ` as
`(1 : ℝ) * σ` — yields a `Tube (1 * σ) E` and not a `Tube σ E`.  For `NNReal` the radius `1 * σ`
is not definitionally `σ`, and the radius is a *type index*, so closing the gap needs a rewrite
of `one_mul` through that index — `subst`-ing an `h : (1 : NNReal) * σ = σ` before the tube is
ever named, or transporting the containment along it — and not a `simp` on the goal alone.
Instantiating instead at `C = σ`, `b = 1` merely moves the problem to `mul_one`.

The hypotheses are stated at the thicknesses rather than at a plank because that is the form
`Kakeya.ml1Boot.subset_plankTube` takes and because nothing in the proof uses the prism
structure.  No upper bound on `σ` and no relation between `σ₀` and `σ` is imposed. -/
theorem subset_dilate_rescale_of_thickness_le (hdim : Module.finrank ℝ E = 3) {σ σ₀ Λ₀ : NNReal}
    (hΛ₀ : 1 ≤ Λ₀) {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    (hτ₀ : thickness ℝ K 0 ≤ (Λ₀ : ℝ)) (hτ₁ : thickness ℝ K 1 ≤ (σ : ℝ))
    (hτ₂ : thickness ℝ K 2 ≤ (σ : ℝ))
    (T₀ : Tube σ₀ E) (hT₀ : T₀.carrier ⊆ K) :
    K ⊆ (Kakeya.Tube.dilate (T₀.rescale (3 * Λ₀ * σ)) (8 * (Λ₀ : ℝ))).carrier := by
  have hΛ₀R : 1 ≤ (Λ₀ : ℝ) := by exact_mod_cast hΛ₀
  have hV : K ⊆ (Kakeya.Tube.dilate (Kakeya.ml1Boot.plankTube hdim 1 σ hK hKne)
      (2 * (Λ₀ : ℝ))).carrier :=
    Kakeya.ml1Boot.subset_plankTube hdim 1 σ hΛ₀R hK hKne hτ₀
      (by simpa using hτ₁) (by simpa using hτ₂)
  have h : K ⊆ (Kakeya.Tube.dilate (T₀.rescale (3 * Λ₀ * σ)) (8 * (Λ₀ : ℝ))).carrier :=
    Kakeya.Tube.subset_dilate_rescale_of_subset_dilate
      (Kakeya.ml1Boot.plankTube hdim 1 σ hK hKne) T₀
      (by linarith) (by linarith) (by
        push_cast
        ring_nf
        nlinarith)
      hT₀ hV
  exact h

end ml1Boot

end Kakeya
