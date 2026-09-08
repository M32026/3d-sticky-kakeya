/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountClause

/-!
# Building the canonical cover on the rescaled bodies (step 10, clause `hcnt`)

Blueprint: `blueprint/src/GWZAdapted/section9.tex`, the non-eccentric case, the invocation of
GWZ Lemma 9.1 at `ζ = η_j/2`.

`Reduction/SpineCountClause.lean` reduces the count clause of `Kakeya.ML2Reduction.Lemma91At` to
the existence, at each scale `ρ` of Lemma 9.1's window, of *one* essentially distinct all-used
`ρ`-tube family over the **rescaled bodies**
`spineFamily (spineRescaleUnit …) 𝕋 i`, of cardinality at least
`spineOuterCountLoss R · ρ^{-2-ζ}` (`Kakeya.ML2Reduction.outerCanonicalCover_of_canonicalCover`,
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover`).  Its own docstring
records what it does not do:

> "What this file does **not** do is *build* the canonical cover on the rescaled bodies."

and names the two residues: (a) the upstairs family at `ρ_up = ρ θ`, and (b) the arithmetic that
`spineOuterCountLoss R · refineToEssDistinctLeaves.C 3 · Δ_max` fits inside the count budget.
**This file builds it**, from the upstairs cover, and does both.

## The interface, and why it is stated over explicit hypotheses

The upstairs cover is produced by the spine's step 8 — `Kakeya.ML2Spine.spine_tube_card_lower` —
and the rescaled datum by the plank factoring; neither is assembled yet.  So the theorems here
take the upstairs cover as an **explicit hypothesis bundle** rather than as another unit's
existential output.  The bundle, at one scale `ρ` of the window, is:

* `t : Finset κ₀`, `W : κ₀ → Tube (ρ * θ)` — the upstairs `ρ_up`-tubes, `ρ_up = ρ θ`;
* `hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier` — the parents live in the coarse tube.  In the
  assembly this is the cover hierarchy's own containment, `Kakeya.ML2Reduction.tube_le_coarseNode`
  (the *ancestor fibre* inclusion, with no dilation);
* `hused : ∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier` — the cover is all-used upstairs;
* `D`, `Ced` with `maxDensity` of the *pushed-down* `ρ`-tubes at most `D` and
  `refineToEssDistinctLeaves.C 3 * D ≤ Ced` — the essential-distinctness price, i.e. `Δ_max`;
* the count `ρ^{-2-ζ'} ≤ |t|` at a **reading exponent `ζ' ≥ ζ`**, and the slack
  `Ced · spineOuterCountLoss R ≤ ρ^{-(ζ' - ζ)}`.

The scale `ρ_up = ρ θ` is forced: `Kakeya.ML2Reduction.outerTube_used_of_used` needs
`Tube.IsRescalingSituation θ ρ_up ρ R 3`, whose `out_le_ratio` field is `ρ ≤ ρ_up / θ`, and
`ρ_up / θ ≤ 4 ρ` on the other side; `ρ_up = ρ θ` makes both an equality and a `ρ ≤ 4 ρ`
respectively (`Kakeya.ML2Reduction.isRescalingSituation_scaledUp`,
`Kakeya.ML2Reduction.ratio_scaledUp`).

## The count budget, and the two hypotheses that force it

`Kakeya.ML2Reduction.count_budget_of_slack` is the whole of residue (b):

```
Ced · (Λ · ρ^{-2-ζ}) ≤ ρ^{-(ζ'-ζ)} · ρ^{-2-ζ} = ρ^{-2-ζ'} ≤ |t|.
```

So the two losses `Λ = spineOuterCountLoss R` (the body→outer-tube transport) and
`Ced ≥ refineToEssDistinctLeaves.C 3 · Δ_max` (the essential-distinctness refinement) are paid
for **entirely out of the gap `ζ' - ζ` between the exponent step 8 delivers and the exponent
Lemma 9.1 is read at**, and by nothing else.  It does *not* fit at `ζ' = ζ`: at `ζ' = ζ` the
slack hypothesis reads `Ced · Λ ≤ 1`, which is false whenever `Δ_max ≥ 1`, and `Δ_max ≥ 1`
always (a nonempty family has density at least `1` in a body it fills).  **The budget therefore
closes if and only if Lemma 9.1 is read at a strictly smaller `ζ` than step 8 delivers**, and
`Lemma91ParamsAt` grants exactly that freedom — its body is `∀ ζ > 0, VNSBody β ϖ ζ …`, so the
consumer picks `ζ`.  `Kakeya.ML2Reduction.slack_of_exponents` prices the gap in exponents: if
`Ced ≤ ρ^{-a}` and `Λ ≤ ρ^{-c}` then `a + c ≤ ζ' - ζ` suffices.  Since `Λ` is a constant
(dimension and `R` only) and `Δ_max ≤ δ̃^{-η'}` on the spine's route, `c` is `0⁺` and `a` is of
order `η'`; the spine's own gap `ζ' - ζ = η_j/4` at `ζ' = η_j/2` is what pays.

## Main declarations

* `Kakeya.ML2Reduction.count_budget_of_slack` — residue (b): the count budget, in one line of
  `rpow` arithmetic.
* `Kakeya.ML2Reduction.slack_of_exponents` — the budget's slack hypothesis from exponents.
* `Kakeya.ML2Reduction.isRescalingSituation_scaledUp`,
  `Kakeya.ML2Reduction.ratio_scaledUp` — the rescaling situation at `ρ_up = ρ θ`.
* `Kakeya.ML2Reduction.canonicalCoverAt_of_upstairs` — residue (a) at one scale: the canonical
  cover on the rescaled bodies, from the upstairs cover.
* `Kakeya.ML2Reduction.canonicalCover_of_upstairs` — the same over the whole window, i.e. the
  `hcanon` binder of
  `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover`, produced.
* `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_upstairs` — step 10 with `hcnt`
  replaced by the upstairs bundle.
* `Kakeya.ML2Reduction.count_clause_at_uniformised` — the same count clause at the *uniformised*
  family `(s', U')`, which is the form a direct application of
  `Kakeya.ML2Reduction.Lemma91At` needs and the route around that wrapper's pinned `huni`.
* `Kakeya.ML2Reduction.not_count_budget_at_equal_reading` — the **refutation** that the
  budget could be paid at `ζ' = ζ`, resting on
  `Kakeya.ML2Reduction.two_le_refineToEssDistinctLeaves_C_three`,
  `Kakeya.ML2Reduction.one_le_maxDensity_tube` and
  `Kakeya.ML2Reduction.le_volume_c_three_coe`.
* `Kakeya.ML2Reduction.canonicalCover_mono`,
  `Kakeya.ML2Reduction.used_of_used_of_carrier_eq` — the two transports a consumer needs when the
  family it holds is a subfamily, or a shade-shrunk version, of the one the cover was built over.
-/

@[expose] public section

open MeasureTheory Metric Set ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

universe u

variable {θ τ σ : NNReal}

/-! ## Residue (b): the count budget -/

/-- **The count budget of step 10's canonical cover.**

The two losses of the push-down — `Ced ≥ refineToEssDistinctLeaves.C 3 · Δ_max` for the
essential-distinctness refinement and `Lam = spineOuterCountLoss R` for the body→outer-tube
transport — are paid for out of the gap between the exponent `ζ'` at which step 8 delivers the
count and the exponent `ζ` at which Lemma 9.1 is read.  Nothing else pays for them: with
`ζ' = ζ` the hypothesis `hslack` degenerates to `Ced · Lam ≤ 1`.

Neither constant needs to be nonnegative for this: the two positivity binders one expects here
are inert and are therefore absent. -/
theorem count_budget_of_slack {ρ : NNReal} (hρ0 : 0 < ρ) {ζ ζ' : ℝ}
    {Ced Lam : ℝ} (hslack : Ced * Lam ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    {n : ℕ} (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (n : ℝ)) :
    Ced * (Lam * (ρ : ℝ) ^ (-2 - ζ)) ≤ (n : ℝ) := by
  have hρ : (0 : ℝ) < (ρ : ℝ) := hρ0
  have hmul : (ρ : ℝ) ^ (-(ζ' - ζ)) * (ρ : ℝ) ^ (-2 - ζ) = (ρ : ℝ) ^ (-2 - ζ') := by
    rw [← Real.rpow_add hρ]; ring_nf
  calc Ced * (Lam * (ρ : ℝ) ^ (-2 - ζ)) = Ced * Lam * (ρ : ℝ) ^ (-2 - ζ) := by ring
    _ ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) * (ρ : ℝ) ^ (-2 - ζ) :=
        mul_le_mul_of_nonneg_right hslack (Real.rpow_nonneg hρ.le _)
    _ = (ρ : ℝ) ^ (-2 - ζ') := hmul
    _ ≤ (n : ℝ) := hcard

/-- **The slack hypothesis of `Kakeya.ML2Reduction.count_budget_of_slack`, priced in exponents.**
If the essential-distinctness price is `Ced ≤ ρ^{-a}` and the transport loss is `Lam ≤ ρ^{-c}`,
then `a + c ≤ ζ' - ζ` suffices.  `0 ≤ Ced` is inert. -/
theorem slack_of_exponents {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {a c ζ ζ' : ℝ}
    {Ced Lam : ℝ} (hLam0 : 0 ≤ Lam)
    (hCed : Ced ≤ (ρ : ℝ) ^ (-a)) (hLam : Lam ≤ (ρ : ℝ) ^ (-c))
    (hsum : a + c ≤ ζ' - ζ) :
    Ced * Lam ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) := by
  have hρ : (0 : ℝ) < (ρ : ℝ) := hρ0
  have hρ1' : (ρ : ℝ) ≤ 1 := hρ1
  calc Ced * Lam ≤ (ρ : ℝ) ^ (-a) * (ρ : ℝ) ^ (-c) :=
        mul_le_mul hCed hLam hLam0 (Real.rpow_nonneg hρ.le _)
    _ = (ρ : ℝ) ^ (-(a + c)) := by rw [← Real.rpow_add hρ]; ring_nf
    _ ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) := Real.rpow_le_rpow_of_exponent_ge hρ hρ1' (by linarith)

/-! ## The rescaling situation at the upstairs scale `ρ_up = ρ θ` -/

/-- **The rescaling situation of the push-down.**  `Kakeya.ML2Reduction.outerTube_used_of_used`
pushes a family of `ρ_up`-tubes inside a `θ`-tube down to `ρ`-tubes, and needs
`Tube.IsRescalingSituation θ ρ_up ρ R 3`.  At `ρ_up = ρ θ` every field is inherited from the
step-10 situation `Tube.IsRescalingSituation θ τ σ R 3` except the two that mention `ρ`:
positivity, and the truncation `ρ ≤ 1/4` — which for `ρ` in Lemma 9.1's window
`[σ^{1-ϖ}, σ^ϖ]` is a threshold on `σ`, free under `∀ᶠ δ`. -/
theorem isRescalingSituation_scaledUp {R : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) {ρ : NNReal}
    (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4) :
    Tube.IsRescalingSituation θ (ρ * θ) ρ R 3 where
  pos_ambient := hsit.pos_ambient
  inner_le_ambient := by
    have hρ1 : ρ ≤ 1 := by rw [← NNReal.coe_le_coe]; push_cast; linarith
    calc ρ * θ ≤ 1 * θ := by gcongr
      _ = θ := one_mul θ
  ambient_le_one := hsit.ambient_le_one
  pos_out := hρ0
  out_le_quarter := hρ4
  out_le_ratio := by
    have hθ : (0 : ℝ) < (θ : ℝ) := hsit.pos_ambient
    push_cast
    rw [mul_div_assoc, div_self (ne_of_gt hθ), mul_one]
  normalizationConst_le_radius := hsit.normalizationConst_le_radius

/-- **The ratio hypothesis of the push-down at `ρ_up = ρ θ`**: `ρ_up / θ = ρ ≤ 4 ρ`. -/
theorem ratio_scaledUp (hθ : 0 < θ) (ρ : NNReal) :
    ((ρ * θ : NNReal) : ℝ) / (θ : ℝ) ≤ 4 * (ρ : ℝ) := by
  have hθ' : (0 : ℝ) < (θ : ℝ) := hθ
  push_cast
  rw [mul_div_assoc, div_self (ne_of_gt hθ'), mul_one]
  nlinarith [ρ.coe_nonneg]

/-! ## Residue (a): the canonical cover on the rescaled bodies -/

/-- **The canonical cover on the rescaled bodies, at one scale of Lemma 9.1's window.**

From an upstairs all-used cover of `𝕋` by `ρ θ`-tubes inside `T₀`, of cardinality at least
`ρ^{-2-ζ'}`: push it down through `Kakeya.ML2Reduction.outerTube` (which preserves "used" and the
index `Finset`, `Kakeya.ML2Reduction.outerTube_used_of_used`), refine to an essentially distinct
subfamily (`Kakeya.ML2Reduction.canonicalCoverAt_of_used_of_maxDensity`), and pay both losses out
of the exponent gap (`Kakeya.ML2Reduction.count_budget_of_slack`).  The output is exactly the
scale-`ρ` instance of the `hcanon` binder of
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover`. -/
theorem canonicalCoverAt_of_upstairs
    {R ζ ζ' : ℝ} (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4)
    {κ₀ : Type u} (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3)))
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier)
    {D : ENNReal} {Ced : NNReal} (hCed : 0 < Ced)
    (hD : Kakeya.maxDensity t
      (fun k ↦ (outerTube hsit.pos_ambient T₀ hR ρ (W k)).toConvexSpaceBody) ≤ D)
    (hedloss : Kakeya.Tube.refineToEssDistinctLeaves.C 3 * D ≤ (Ced : ENNReal))
    (hslack : (Ced : ℝ) * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ∃ (κ₁ : Type u) (u : Finset κ₁) (V : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      ((u : Set κ₁).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
      (∀ j ∈ u, ∃ i ∈ s,
        (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
          ≤ (V j).toConvexSpaceBody) ∧
      (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (u.card : ℝ) := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hρ1 : ρ ≤ 1 := by rw [← NNReal.coe_le_coe]; push_cast; linarith
  have hsit' : Tube.IsRescalingSituation θ (ρ * θ) ρ R 3 :=
    isRescalingSituation_scaledUp hsit hρ0 hρ4
  have husedDown := outerTube_used_of_used (E := EuclideanSpace ℝ (Fin 3)) hfr hsit' hR
    (ratio_scaledUp hsit.pos_ambient ρ) T₀ (τ := τ) 𝕋 (s := s) W hsubW hused
  exact canonicalCoverAt_of_used_of_maxDensity hsit.pos_ambient T₀ (hR := hR) 𝕋 hρ0 hρ1
    t (fun k ↦ outerTube hsit.pos_ambient T₀ hR ρ (W k)) hCed hD hedloss husedDown
    (count_budget_of_slack hρ0 hslack hcard)

/-- **The canonical cover on the rescaled bodies, over the whole of Lemma 9.1's window.**

This is the `hcanon` binder of
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover`, produced from the
upstairs cover.  `hwin4` is the window truncation `σ^ϖ ≤ 1/4`, a threshold on `σ` and free under
`∀ᶠ δ` for `ϖ > 0`; it is what supplies `Tube.IsRescalingSituation`'s `out_le_quarter` at every
scale of the window at once. -/
theorem canonicalCover_of_upstairs
    {R ϖ ζ ζ' : ℝ} (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hσ0 : 0 < σ) (hwin4 : ((σ ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hup : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3)))
        (D : ENNReal) (Ced : NNReal),
        0 < Ced ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        Kakeya.maxDensity t
          (fun k ↦ (outerTube hsit.pos_ambient T₀ hR ρ (W k)).toConvexSpaceBody) ≤ D ∧
        Kakeya.Tube.refineToEssDistinctLeaves.C 3 * D ≤ (Ced : ENNReal) ∧
        (Ced : ℝ) * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ j ∈ t, ∃ i ∈ s,
          (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
            ≤ (W j).toConvexSpaceBody) ∧
        (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (t.card : ℝ) := by
  intro ρ hρ
  have hρ0 : 0 < ρ := lt_of_lt_of_le (NNReal.rpow_pos hσ0) hρ.1
  have hρ4 : (ρ : ℝ) ≤ 1 / 4 := le_trans (NNReal.coe_le_coe.mpr hρ.2) hwin4
  obtain ⟨κ₀, t, W, D, Ced, hCed, hsubW, hused, hD, hedloss, hslack, hcard⟩ := hup ρ hρ
  exact canonicalCoverAt_of_upstairs hsit hR T₀ 𝕋 hρ0 hρ4 t W hsubW hused hCed hD hedloss
    hslack hcard

/-! ## Step 10, over the upstairs interface -/

/-- **STEP 10, with the count clause built from the upstairs cover.**

`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover` with its `hcanon`
binder discharged by `Kakeya.ML2Reduction.canonicalCover_of_upstairs`.  Every hypothesis is now
either granted by the step-10 rescaling situation, a threshold on `σ`, or a clause of the
upstairs cover — nothing about the *rescaled bodies* is left to the caller.

The `huni` binder is inherited verbatim from
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer`; it is pinned to whichever family `𝕋`
this statement is instantiated at, so a caller holding uniformity only for a *refined*,
shade-shrunk family instantiates the whole statement at that family and uses
`Kakeya.ML2Reduction.used_of_used_of_carrier_eq` / `Kakeya.ML2Reduction.canonicalCover_mono` to
move the cover across. -/
theorem multiplicity_le_of_lemma91At_outer_of_upstairs
    {β ϖ ζ ζ' ν ηd cst : ℝ} {R : ℝ}
    (hL : Lemma91At.{u} β ϖ ζ ν ηd σ)
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).  Symbol-indexed
    --: the same text in this statement's own `ζ`, `ϖ`, `ηd`.
    -- The criterion's derivation needs the scale `< 1` (monotonicity of `s^{-x}` in `x`).
    -- MEASURED: available here, and strictly stronger — `hsit.out_le_quarter` gives
    -- `(σ : ℝ) ≤ 1/4` (`Kakeya/Tube/Rescale.lean:2627`), and this statement carries `hsit`.
    -- So `σ ≤ 1` is a citation, not an added binder.
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (hσ0 : 0 < σ) (hϖ : 0 ≤ ϖ)
    (hwin4 : ((σ ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3))) {α : Type u} (s : Finset α)
    (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier)
    (hloss : outerLoss R ≤ σ ^ (-cst))
    (hmax : Kakeya.maxDensity s (fun i ↦ (𝕋 i).toConvexSpaceBody)
      ≤ (σ : ENNReal) ^ (-(ηd - cst)))
    (hfull : σ ^ (ηd - cst) ≤ ShadedBody.fullness s (fun i ↦ (𝕋 i).toShadedBody))
    (hcen : ∀ i ∈ s, (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toTube.IsCentred)
    (huni : ∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (σ : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s
      (outerFamily hsit.pos_ambient T₀ hR σ 𝕋) (Tube.ssfGridLen σ) C))
    (hup : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3)))
        (D : ENNReal) (Ced : NNReal),
        0 < Ced ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        Kakeya.maxDensity t
          (fun k ↦ (outerTube hsit.pos_ambient T₀ hR ρ (W k)).toConvexSpaceBody) ≤ D ∧
        Kakeya.Tube.refineToEssDistinctLeaves.C 3 * D ≤ (Ced : ENNReal) ∧
        (Ced : ℝ) * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ShadedBody.multiplicity s (fun i ↦ (𝕋 i).toShadedBody)
      ≤ (σ : ENNReal) ^ ν * (s.card : ENNReal) ^ β :=
  multiplicity_le_of_lemma91At_outer_of_canonicalCover hL hζ hsit hR hR1 hτσ hσ0 hϖ T₀ s 𝕋 hsub
    hloss hmax hfull hcen huni
    (canonicalCover_of_upstairs hsit hR hσ0 hwin4 T₀ 𝕋 hup)

/-- **The count clause of `Kakeya.ML2Reduction.Lemma91At` at the *uniformised* family, built from
the upstairs cover.**

This is the route around the `huni` pinning of
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer`.  That binder asks for a
`ShadedTube.ShadedUniformTubeSet s (outerFamily … 𝕋) …` — the outer family *on the nose* — while
`Kakeya.ML2Reduction.exists_outerShadedUniformTubeSet` returns a witness on a **subfamily**
`s' ⊆ s` against a **shade-shrunk** `U'`, and a shrunk shading is in general **not** of the form
`outerFamily … 𝕋'`.  So the wrapper's `huni` is not dischargeable from the tree's own uniformiser,
and the fix is the one recorded for `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer`:
apply `Kakeya.ML2Reduction.Lemma91At` **directly**, since it quantifies over an arbitrary family
`(s, T)`.  This theorem produces exactly the count clause that direct application needs, at
`(s', U')`.

`hU` is the uniformiser's own first output clause; the count clause reads only
`toConvexSpaceBody`, i.e. only the tube, so it transports at **zero** loss.

**The interface constraint this exposes, and it is the one a consumer must plan for:** the
`∃ i ∈ s'` of the used clause is *not* recoverable from `∃ i ∈ s` — `Kakeya.ML2Reduction.
canonicalCover_mono` only enlarges the index set.  So the upstairs cover has to be built over the
**post-uniformisation** index set `s'`: uniformise first, then build the cover.  A cover built over
`s` and then narrowed to `s'` loses the "all-used" clause outright. -/
theorem count_clause_at_uniformised
    {R ϖ ζ ζ' : ℝ} (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (hσ0 : 0 < σ) (hϖ : 0 ≤ ϖ)
    (hwin4 : ((σ ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s' : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (U' : α → ShadedTube σ (EuclideanSpace ℝ (Fin 3)))
    (hU : ∀ i, (U' i).toTube = (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toTube)
    (hsub : ∀ i ∈ s', (𝕋 i).carrier ⊆ T₀.carrier)
    (hup : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3)))
        (D : ENNReal) (Ced : NNReal),
        0 < Ced ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        Kakeya.maxDensity t
          (fun k ↦ (outerTube hsit.pos_ambient T₀ hR ρ (W k)).toConvexSpaceBody) ≤ D ∧
        Kakeya.Tube.refineToEssDistinctLeaves.C 3 * D ≤ (Ced : ENNReal) ∧
        (Ced : ℝ) * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ).Pairwise
          (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s', (U' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ) := by
  intro ρ hρ
  obtain ⟨κ, tρ, Tρ, hED, hused, hcard⟩ :=
    outerCanonicalCover_of_canonicalCover hsit hR hτσ hσ0 hϖ T₀ 𝕋 hsub
      (canonicalCover_of_upstairs hsit hR hσ0 hwin4 T₀ 𝕋 hup) ρ hρ
  refine ⟨κ, tρ, Tρ, hED, fun j hj ↦ ?_, hcard⟩
  obtain ⟨i, hi, hle⟩ := hused j hj
  refine ⟨i, hi, ?_⟩
  have hb : (U' i).toConvexSpaceBody
      = (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toConvexSpaceBody := by
    rw [show (U' i).toConvexSpaceBody = ((U' i).toTube).toConvexSpaceBody from rfl,
      show (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toConvexSpaceBody
        = ((outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toTube).toConvexSpaceBody from rfl, hU i]
  rw [hb]
  exact hle

/-! ## The two transports a consumer needs -/

/-- **The canonical-cover datum is monotone in the index set.**  A cover all-used over a
subfamily `s₁ ⊆ s₂` is all-used over `s₂`; this is the direction in which step 10's output is
pushed back from a refined family to the original one. -/
theorem canonicalCover_mono {R : ℝ} {hθ : 0 < θ} (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {hR : 0 < R} {α : Type u} {s₁ s₂ : Finset α}
    (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3))) (hs : s₁ ⊆ s₂)
    {ρ : NNReal} {κ₀ : Type u} {t : Finset κ₀} {W : κ₀ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
    (hused : ∀ j ∈ t, ∃ i ∈ s₁,
      (spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody ≤ (W j).toConvexSpaceBody) :
    ∀ j ∈ t, ∃ i ∈ s₂,
      (spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody
        ≤ (W j).toConvexSpaceBody := by
  intro j hj
  obtain ⟨i, hi, hle⟩ := hused j hj
  exact ⟨i, hs hi, hle⟩

/-- **The upstairs "used" clause only sees carriers.**  A shading refinement — a family with the
same carriers and smaller shades, which is what every uniformiser on this route returns — inherits
the upstairs all-used clause verbatim.  This is how a consumer whose `huni` witness lives on a
shade-shrunk family keeps the cover it built for the original one. -/
theorem used_of_used_of_carrier_eq {α : Type u} {s : Finset α} {κ₀ : Type u} {t : Finset κ₀}
    {ρup : NNReal} {W : κ₀ → Tube ρup (EuclideanSpace ℝ (Fin 3))}
    (𝕋 𝕋' : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hcar : ∀ i ∈ s, (𝕋' i).carrier = (𝕋 i).carrier)
    (hused : ∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) :
    ∀ k ∈ t, ∃ i ∈ s, (𝕋' i).carrier ⊆ (W k).carrier := by
  intro k hk
  obtain ⟨i, hi, hle⟩ := hused k hk
  exact ⟨i, hi, by rw [hcar i hi]; exact hle⟩

/-! ## The budget does not close at an equal reading exponent — a refutation -/

/-- **`Tube.le_volume.c 3 = 4 π / 9`**, in closed form.  `Real.Gamma (5/2) = (3/4) √π` by two
applications of `Real.Gamma_add_one` from `Real.Gamma_one_half_eq`.  Recorded because the
essential-distinctness price `Tube.refineToEssDistinctLeaves.C 3` divides by this constant, and the
refutation below needs it bounded above. -/
theorem le_volume_c_three_coe : ((Tube.le_volume.c 3 : NNReal) : ℝ) = 4 * Real.pi / 9 := by
  change Real.sqrt Real.pi ^ 3 / Real.Gamma (((3 : ℕ) : ℝ) / 2 + 1) / 3 = 4 * Real.pi / 9
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h1 : (((3 : ℕ) : ℝ) / 2 + 1) = 3 / 2 + 1 := by norm_num
  have hG32 : Real.Gamma (3 / 2 : ℝ) = 1 / 2 * Real.sqrt Real.pi := by
    have h : (3 / 2 : ℝ) = 1 / 2 + 1 := by norm_num
    rw [h, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  have hG52 : Real.Gamma (3 / 2 + 1 : ℝ) = 3 / 4 * Real.sqrt Real.pi := by
    rw [Real.Gamma_add_one (by norm_num), hG32]; ring
  rw [h1, hG52]
  have hsq : Real.sqrt Real.pi ^ 3 = Real.pi * Real.sqrt Real.pi := by
    have h := Real.sq_sqrt Real.pi_pos.le
    nlinarith [h]
  rw [hsq]
  field_simp
  ring

/-- **The essential-distinctness price is at least `2`.**  `refineToEssDistinctLeaves.C 3 =
overlapContainment.C 3 · volume_le.C 3 / le_volume.c 3`, and
`overlapContainment.C 3 = ofReal (C₃')` with `C₃' = tubeOverlapCoreClose.C 3 ^ 3 > 9 ^ 3`, while
`le_volume.c 3 = 4 π / 9 ≤ 2` (`Kakeya.ML2Reduction.le_volume_c_three_coe`).  `Kakeya/Tube/
CoverCountComparable.lean:172` records that the constant "carries no positivity lemma of its own";
this is that lemma, in the only form the count budget needs. -/
theorem two_le_refineToEssDistinctLeaves_C_three :
    (2 : ENNReal) ≤ Kakeya.Tube.refineToEssDistinctLeaves.C 3 := by
  have hcne : (Tube.le_volume.c 3 : ENNReal) ≠ 0 := by
    simp [(Tube.le_volume.c_pos 3).ne']
  have hcnt : (Tube.le_volume.c 3 : ENNReal) ≠ ⊤ := by simp
  rw [Kakeya.Tube.refineToEssDistinctLeaves.C, ENNReal.le_div_iff_mul_le (Or.inl hcne)
    (Or.inl hcnt)]
  have hc2 : (Tube.le_volume.c 3 : ENNReal) ≤ 2 := by
    have h : ((Tube.le_volume.c 3 : NNReal) : ℝ) ≤ 2 := by
      rw [le_volume_c_three_coe]; nlinarith [Real.pi_le_four]
    have h2 : (Tube.le_volume.c 3 : NNReal) ≤ 2 := by
      rw [← NNReal.coe_le_coe]; simpa using h
    exact_mod_cast h2
  have hA : (4 : ENNReal) ≤ Kakeya.Tube.overlapContainment.C 3 := by
    have h9 : (9 : ℝ) < Kakeya.Tube.tubeOverlapCoreClose.C 3 := by
      have h : (0 : ℝ) < 2 * 4 ^ 3 / (Tube.le_volume.c 3 : ℝ) := by
        have := Tube.le_volume.c_pos 3
        positivity
      unfold Kakeya.Tube.tubeOverlapCoreClose.C; linarith
    have h4 : (4 : ℝ) ≤ Kakeya.Tube.tubeDilateVolume.C' 3
        (Kakeya.Tube.tubeOverlapCoreClose.C 3) := by
      unfold Kakeya.Tube.tubeDilateVolume.C'
      have h2c : (4 : ℝ) ≤ Kakeya.Tube.tubeOverlapCoreClose.C 3 := by linarith
      calc (4 : ℝ) ≤ 4 ^ 3 := by norm_num
        _ ≤ Kakeya.Tube.tubeOverlapCoreClose.C 3 ^ 3 := by gcongr
    calc (4 : ENNReal) = ENNReal.ofReal 4 := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal h4
  have hB : (1 : ENNReal) ≤ ((Tube.volume_le.C 3 : NNReal) : ENNReal) := by
    have h : (1 : NNReal) ≤ Tube.volume_le.C 3 := by
      unfold Tube.volume_le.C; norm_num
    exact_mod_cast h
  calc (2 : ENNReal) * (Tube.le_volume.c 3 : ENNReal) ≤ 2 * 2 := by gcongr
    _ = 4 * 1 := by norm_num
    _ ≤ Kakeya.Tube.overlapContainment.C 3 * ((Tube.volume_le.C 3 : NNReal) : ENNReal) :=
        mul_le_mul' hA hB

/-- **A nonempty family of `ρ`-tubes has maximal density at least `1`** (`ρ > 0`): every tube has
positive volume (`Tube.le_volume`), so `Kakeya.one_le_maxDensity` applies.  This is what makes the
`Δ_max`-price of the essential-distinctness refinement unavoidable. -/
theorem one_le_maxDensity_tube {ι : Type*} {t : Finset ι} {ρ : NNReal} (hρ : 0 < ρ)
    (V : ι → Tube ρ (EuclideanSpace ℝ (Fin 3))) {k : ι} (hk : k ∈ t) :
    1 ≤ Kakeya.maxDensity t (fun j ↦ (V j).toConvexSpaceBody) := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  refine Kakeya.one_le_maxDensity ⟨k, hk, ?_⟩
  have h := Tube.le_volume (V k)
  rw [hfr] at h
  refine lt_of_lt_of_le ?_ h
  have h0 : (0 : NNReal) < Tube.le_volume.c 3 * ρ ^ (3 - 1) := by
    have := Tube.le_volume.c_pos 3
    positivity
  exact_mod_cast h0

/-- **REFUTATION: the count budget cannot be paid at an equal reading exponent.**

If Lemma 9.1 is read at the *same* `ζ` at which step 8 delivers the count — `ζ' = ζ` — then the
slack hypothesis of `Kakeya.ML2Reduction.count_budget_of_slack` reads
`Ced · spineOuterCountLoss R ≤ ρ^0 = 1`, and that is **false** for every nonempty pushed-down
cover: `1 ≤ Δ_max` (`Kakeya.ML2Reduction.one_le_maxDensity_tube`) and
`2 ≤ refineToEssDistinctLeaves.C 3` (`Kakeya.ML2Reduction.two_le_refineToEssDistinctLeaves_C_three`)
force `2 ≤ Ced`, while `1 ≤ spineOuterCountLoss R`
(`Kakeya.ML2Reduction.one_le_spineOuterCountLoss`).

So the exponent gap `ζ' - ζ > 0` is **necessary**, not merely convenient: `Λ · C₃ · Δ_max` fits the
count budget *only* out of that gap.  `Lemma91ParamsAt`'s body `∀ ζ > 0, VNSBody β ϖ ζ …` grants
the gap, so this is a constraint on the consumer's choice of `ζ`, not an obstruction. -/
theorem not_count_budget_at_equal_reading {ρ : NNReal} {ζ R : ℝ} {D : ENNReal} {Ced : NNReal}
    (hD : 1 ≤ D)
    (hedloss : Kakeya.Tube.refineToEssDistinctLeaves.C 3 * D ≤ (Ced : ENNReal))
    (hslack : (Ced : ℝ) * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ - ζ))) : False := by
  have h2 : (2 : ENNReal) ≤ (Ced : ENNReal) := by
    calc (2 : ENNReal) = 2 * 1 := by ring
      _ ≤ Kakeya.Tube.refineToEssDistinctLeaves.C 3 * D :=
          mul_le_mul' two_le_refineToEssDistinctLeaves_C_three hD
      _ ≤ (Ced : ENNReal) := hedloss
  have h2' : (2 : ℝ) ≤ (Ced : ℝ) := by
    have h : (2 : NNReal) ≤ Ced := by exact_mod_cast h2
    exact_mod_cast h
  have hΛ : (1 : ℝ) ≤ (spineOuterCountLoss R : ℝ) := one_le_spineOuterCountLoss R
  have hrhs : (ρ : ℝ) ^ (-(ζ - ζ)) = 1 := by
    rw [sub_self, neg_zero, Real.rpow_zero]
  rw [hrhs] at hslack
  nlinarith [hslack, h2', hΛ]

end Kakeya.ML2Reduction

end
