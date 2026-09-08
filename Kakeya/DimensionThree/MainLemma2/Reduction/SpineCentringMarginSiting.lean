/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteRowPack
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreAssembly

/-!
# The centring margin, sited where the source sites it rules that the `hnu` row at sites 3–6 is
a **charging error, not a quantifier-order inversion**: the sites write
`gain(x) + 3 qc ≤ gain(x)`, billing the centring margin to the very account it is a fraction of.
The previous hand's `Kakeya.ML2Core.hnu_false_at_matched_tolerance`
(`Reduction/SpineSiteEDSplit.lean`) is the refutation; this leaf is the repair, in the source's
own siting — **option (b)**, and with **no existing statement edited**.

## What the source does (l.5980–6110)

* `q = min{a₀/10, ν₀/100, ε_out/100}`, l.5988.  The margin is sized against `ν₀`, the **one-trial
  statement's gain**, an *outer* quantity; `ν₀` is the same number that fixes `g = min{ν₀/4, ω/2}`
  at l.5981.  No tolerance appears in the sizing — so **not** option (a).
* The centring and canonical-tower preparation runs on `(𝔾,Y) → (𝕋,Y')` **before** the trial
  (l.5990–5993, l.6107–6110), and its total cost is `μ(𝔾,Y) ≤ d^{-3q} μ(𝕋,Y')`,
  `eq:defect-preparation` l.6090–6095.
* The `3q` is **three reserved powers in the multiplicity ledger**, itemised at l.6083–6086:
  one absorbs the canonical fibre size, one the threaded-tower selection, and the last all fixed
  numerical constants.  The four absorptions they discharge are `eq:defect-absorb-preparation`
  l.6067–6071 and reduce to l.6078–6082.

`centringMargin_threeReservations` transcribes the itemisation, and
`centringMargin_sourceSizing` the sizing row.

## The repair, and why no existing statement had to change

The eliminator `Kakeya.ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover` **already** carries
the source's shape: it binds Lemma 9.1 at `ν₀`, carries the ledger row `hνqc : ν + 3 qc ≤ ν₀` as a
*separate* hypothesis, and pays `d^{-3q}` through the hand-back's `multiplicity_le`.  Nothing in it
is wrong.  What is wrong is only the **instantiation** at sites 3–6, which sets

  `ν₀ := gain(x) + 3 qc`,   `ν := gain(x)`,   `hνqc := le_rfl`,

so that Lemma 9.1 is *demanded* at `gain(x) + 3 qc` — the account it is drawn from.
`fine_factor_sourceSited` below is the same eliminator at the source's instantiation

  `ν₀ := gain(x)`,   `ν := gain(x) − 3 qc`,   `hνqc := le_of_eq (by ring)`,

i.e. Lemma 9.1 at **its own delivered exponent**, with the `3 qc` moved off `ν` and paid as its own
multiplicity-ledger factor, exactly as at l.6091.  It compiles, and it needs no `hnu` at all.

## What is still owed, as a WRITTEN REQUEST (no statement is edited here)

The six middle-factor sites bind `hL91` at `gain(x) + 3 qc`.  Those binders are existing statements,
so this leaf does not touch them.  The request is:

1. In each of the six site theorems, change the binder
   `(hL91 : Lemma91At β ϖ ζ (gain (spineRung β ϖ ε₁ gain dens (k+1) / 2) + 3 * qc) ηd δ')`
   to `(hL91 : Lemma91At β ϖ ζ (gain (spineRung β ϖ ε₁ gain dens (k+1) / 2)) ηd δ')`,
   and re-tie the internal `fine_factor_of_lemma91At_of_canonicalCover` call from
   `(ν := gain (…)) … le_rfl` to `(ν := gain (…) − 3 * qc) … (le_of_eq (by ring))`.
2. The `3 qc` then appears in `h10`'s exponent and must be absorbed downstream against the trial's
   aggregate gain, at the source's ratio `q ≤ ν₀/100` (`centringMargin_sourceSizing` prices it:
   the surviving exponent is at least `97/100` of `ν₀`).
3. `Kakeya.ML2Assembly.Lemma91ParamsAt`'s quantifier order is **not** touched, and `qc` itself is not adjusted.

Sites: `Kakeya.ML2Core.fine_factor_of_lemma91At_of_step8`,
`…of_edCover`, `…middle_factor_of_lineEDNodes_sharp` and their three companions —
`Reduction/SpineMiddleFactor.lean:448,696`, `Reduction/SpineMiddleProducer.lean:406,785`.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

universe u

/-- **The source's sizing row for the centring margin**, l.5988: `q ≤ ν₀/100`, with `ν₀` the
one-trial statement's gain.  What it buys, at l.6091: after paying `d^{-3q}` the surviving
exponent is `ν₀ − 3q ≥ (97/100)·ν₀`, still positive.  The margin is a *three-percent* charge
against an **outer** quantity — this is the whole difference from the sites' current siting, where
it is an absolute demand for `3 qc` of headroom inside a quantity of size `gain x`. -/
theorem centringMargin_sourceSizing {q ν₀ : ℝ} (hν₀ : 0 < ν₀) (hq : q ≤ ν₀ / 100) :
    (97 / 100) * ν₀ ≤ ν₀ - 3 * q ∧ 0 < ν₀ - 3 * q := by
  constructor <;> linarith

/-- **The three reserved powers of `q`**, l.6083–6086: "one absorbs the canonical fibre size, one
the threaded-tower selection, and the last all fixed numerical constants."  Transcribed by name:
given the three absorptions of `eq:defect-absorb-preparation` (l.6067–6070) — the fibre-size row
`R ≤ d^{-q}`, the selection row `F₁ R ≤ d^{-3q}` written against the residual `2q`, and the
constants row `384 δ^{-q} ≤ d^{-2q}` — their product is the ledger factor `d^{-3q}` and no more.

The point of stating it is that `3` is not a fitted constant: it is `1 + 1 + 1`, one power per
named absorption, and dropping any one of the three leaves a factor the ledger cannot pay. -/
theorem centringMargin_threeReservations {d q fibre selection constants : ℝ}
    (hd0 : 0 < d) (_hd1 : d ≤ 1) (_hq0 : 0 ≤ q)
    (hfibre : fibre ≤ d ^ (-q)) (hselection : selection ≤ d ^ (-q))
    (hconstants : constants ≤ d ^ (-q))
    (_hf0 : 0 ≤ fibre) (hs0 : 0 ≤ selection) (hc0 : 0 ≤ constants) :
    fibre * selection * constants ≤ d ^ (-(3 * q)) := by
  have hpow : (0:ℝ) < d ^ (-q) := Real.rpow_pos_of_pos hd0 _
  have hmul : d ^ (-q) * d ^ (-q) * d ^ (-q) = d ^ (-(3 * q)) := by
    rw [← Real.rpow_add hd0, ← Real.rpow_add hd0]; ring_nf
  calc fibre * selection * constants
      ≤ d ^ (-q) * d ^ (-q) * d ^ (-q) := by
        have h1 : fibre * selection ≤ d ^ (-q) * d ^ (-q) :=
          mul_le_mul hfibre hselection hs0 hpow.le
        exact mul_le_mul h1 hconstants hc0 (by positivity)
    _ = d ^ (-(3 * q)) := hmul

/-- The source's margin budget discharges `hνqc` by an identity. Charging the
same margin to the target gain would require `g + 3 * qc ≤ g`, which
`hnu_false_at_matched_tolerance` refutes whenever `qc > 0`. -/
theorem sourceSited_ledgerRow (g qc : ℝ) : (g - 3 * qc) + 3 * qc ≤ g := le_of_eq (by ring)

/-- The companion refutation, restated here so the two rows sit in one place: the sites' row is
false for every positive `qc`, so it is not a budget shortfall that a smaller constant would fix.
(`Kakeya.ML2Core.hnu_false_at_matched_tolerance` is the existing form.) -/
theorem oldSiting_ledgerRow_false (g qc : ℝ) (hqc : 0 < qc) : ¬ (g + 3 * qc ≤ g) := by
  intro h; linarith

/-- **The repair, : the eliminator at the source's instantiation.**

`Kakeya.ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover` with
`ν₀ := gain(x)` and `ν := gain(x) − 3 qc`, i.e. Lemma 9.1 bound at **its own delivered exponent**
and the centring cost `d^{-3 qc}` charged as its own multiplicity-ledger factor, in the source's
order (centring before trial, l.5990–5993 / l.6090–6095).

There is **no `hnu`**: the ledger row `hνqc` is discharged by `le_of_eq`, not by a comparison of
`gain(x)` with itself.  That is the whole of the repair. -/
theorem fine_factor_sourceSited
    {β ϖ ζ ηd cst qc ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ} {b δt δ' : NNReal} {R : ℝ}
    (hL : Lemma91At.{u} β ϖ ζ (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2)) ηd δ')
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ)) (hδ'0 : 0 < δ') (hϖ0 : 0 ≤ ϖ)
    (hβ0 : 0 ≤ β) (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3))) (m : EuclideanSpace ℝ (Fin 3))
    {α : Type u} {s s' : Finset α} (hs' : s' ⊆ s)
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (hU : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ m qc s s' 𝕋 U')
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier)
    (hloss : outerLoss R ≤ δ' ^ (-cst))
    (huni : ∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ') C))
    (hcnt : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ).Pairwise
          (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s', (U' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) :
    ShadedBody.multiplicity s
        (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' 𝕋 i).toShadedBody)
      ≤ (δ' : ENNReal) ^ (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) - 3 * qc)
        * (s.card : ENNReal) ^ β :=
  fine_factor_of_lemma91At_of_canonicalCover
    (ν := gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) - 3 * qc)
    (ν₀ := gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2))
    hL hζ hsit hR hR1 hτσ hδ'0 hϖ0 hβ0 hqc0 (le_of_eq (by ring)) h3qc T₀ m hs' 𝕋 U' hU hsub
    hloss huni hcnt

end Kakeya.ML2Reduction

end
