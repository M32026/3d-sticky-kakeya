/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentringMarginSiting
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineLineEDMiddle

/-!
# The six middle-factor sites, source-sited: `hnu` removed, the `3 qc` in the ledger

 The sites' `hnu` row is a **charging error**: they demand Lemma 9.1
at `gain(x) + 3 qc`, the account the centring margin is drawn from.  The source (refined
l.5980–6110) sizes the margin against the **trial's** gain, `q ≤ ν₀/100` (l.5988), and spends it as
its own multiplicity-ledger factor `μ(𝔾,Y) ≤ d^{-3q} μ(𝕋,Y')` (l.6090–6095), reserving three
powers of `q` (l.6083–6086).  `Reduction/SpineCentringMarginSiting.lean` transcribes that and
compiles the repaired eliminator instantiation (`fine_factor_sourceSited`); this leaf carries it
through to the six sites.

## What is here, and what is NOT

**Additive siblings.**  Every original is kept, untouched.  For each of the six sites and for the
two step-11 assemblers they run through, this leaf adds a `_sourceSited` twin.  Each twin is
binder-for-binder the original with exactly three changes:

1. `hL91` at `gain(spineRung β ϖ ε₁ gain dens (k+1) / 2)`, **not** at that `+ 3 qc`;
2. a new binder `hqsize : qc ≤ gain(…)/100` — the source's own sizing row, l.5988;
3. `hκ` reserves the margin: `κ + 3 qc ≤ …` instead of `κ ≤ …`.

and, inside the proof, the eliminator is instantiated at `ν₀ := gain(…)`, `ν := gain(…) − 3 qc`,
with `hνqc` discharged by `le_of_eq (by ring)` — never by a comparison of `gain(x)` with itself.

**The conclusion of every twin is to its original's.**  That is the property that
makes this additive rather than a fork: any consumer that reads `hmid` off an original reads the
same `hmid` off the twin.  In particular a producer of `HfacPostDropFour`
(`Reduction/SpineHfacWire.lean:233`) can be wired through the twins with **no `hnu` anywhere**;
`w400gen`'s `exists_hfacFourConclusion_of_factors` is not in the tree at this tip, so the wiring
is stated here as the conclusion identity and not as a call.

## Where the `3 qc` actually goes

At step 11 the fine factor enters as `hf : muf ≤ δ'^ν · Nf^β` and the numeric row is
`θ ≤ (1-ε₂)·ν − 2η' − κ` (`multiplicity_le_of_two_factors_rescaled`).  Lowering `ν` by `3 qc`
costs `(1-ε₂)·3 qc ≤ 3 qc`, which is exactly what `hκ`'s reservation pays.  So the margin is
billed to the **multiscale-loss budget** — the multiplicity ledger — which is the source's own
account, and `hqsize` is what keeps `gain(…) − 3 qc` non-negative (`3 qc ≤ 3·gain/100 ≤ gain`).

## Pins

`ctl/CTL_sites_oldsiting.lean` reverts all six twins to the old instantiation
(`ν := gain(…)`, `le_rfl`; delegating sites re-pointed at the un-sited callee) and **fails to
elaborate**, one error per site.  That is the compatibility check: the old `hnu` shape
does not typecheck against the new binder.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

universe u

/-- **Step 11, source-sited.**  `Kakeya.ML2Reduction.spine_multiplicity_le_two_factors` with the
fine factor read at `gain(…) − 3 qc` and the margin reserved inside the multiscale-loss budget
(`hκ : κ + 3 qc ≤ 20 η_k/ε₂`).  The conclusion is the original's, unchanged.  `hqsize` is the
source's sizing row `q ≤ ν₀/100` (l.5988) and is what makes the lowered exponent non-negative. -/
theorem spine_multiplicity_le_two_factors_sourceSited
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    {δt b δ' : NNReal} {mu mub muf L Cu : ENNReal} {Nb Nf N : ℕ} {κ qc : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    (hsplit : mu ≤ L * (mub * muf))
    (hb : mub ≤ (δt : ENNReal) ^
          (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k / (ML2Spine.spineDiv ϖ ε₁ * β))))
        * (Nb : ENNReal) ^ β)
    (hf : muf ≤ (δ' : ENNReal)
          ^ (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) - 3 * qc)
        * (Nf : ENNReal) ^ β)
    (hcard : (Nb : ENNReal) * (Nf : ENNReal) ≤ Cu * (N : ENNReal))
    (hL : L * Cu ^ β ≤ (δt : ENNReal) ^ (-κ))
    (hqc0 : 0 ≤ qc)
    (hqsize : qc ≤ gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) / 100)
    (hκ : κ + 3 * qc
      ≤ 20 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁) :
    mu ≤ (δt : ENNReal) ^
          (10 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁)
        * (N : ENNReal) ^ β := by
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  have hpos : (0 : ℝ) < ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2 := by
    have := hsp.rung_pos (k + 1)
    linarith
  have hg : 0 ≤ gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) := (hgain _ hpos).le
  have hν : 0 ≤ gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) - 3 * qc := by linarith
  have hε₂0 : 0 < ML2Spine.spineEps₂ ϖ ε₁ := ML2Spine.spineEps₂_pos hϖ hε₁
  have hbud := spineRung_gainBudget_of_rescaleLoss hβ0 hβ1 hϖ hε₁ hgain hdens hk hκ
  refine multiplicity_le_of_two_factors_rescaled (by simpa using hδ0.ne')
    (by exact_mod_cast hδ1) hβ0.le hν (hsp.eps₂_le_half.trans (by norm_num))
    (rescaledScale_le hδ0 hbw hprod) hsplit hb hf hcard hL ?_
  nlinarith [hbud, hε₂0, hqc0]

/-- **Source-sited twin of
`Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover`.**

Binder for binder the original, with three changes and no others:
* `hL91` is bound at `gain(spineRung β ϖ ε₁ gain dens (k+1) / 2)` — Lemma 9.1 at its
  **own delivered exponent** — instead of at that exponent `+ 3 qc`;
* the source's sizing row `hqsize : qc ≤ gain(…)/100` is added (l.5988, `q ≤ ν₀/100`);
* the multiscale-loss budget reserves the margin: `hκ` reads `κ + 3 qc ≤ …`.

The **conclusion is to the original's**, so every consumer that reads
`hmid` from the original reads it unchanged from this twin — and with no `hnu`
anywhere.  Routed through `spine_multiplicity_le_two_factors_sourceSited`.
`Kakeya.ML2Core.hnu_false_at_matched_tolerance` refutes the original's row. -/
theorem spine_multiplicity_le_nonEccentric_of_canonicalCover_sourceSited
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    {δt b δ' : NNReal} {R : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1) (hδ'0 : 0 < δ') (hb1 : b ≤ 1) (hδtb : δt ≤ b)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))} {ηc : ℝ}
    (hcoarse : ∀ (dt : NNReal), dt ≠ 0 → dt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} (t : Finset ι) (T : ι → ShadedTube b (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ closedBall 0 1) →
        (ShadedBody.fullness t (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc →
        Kakeya.maxDensity t (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (dt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β))) →
        ShadedBody.multiplicity t (fun i ↦ (T i).toShadedBody)
          ≤ (dt : ENNReal) ^ (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β)))) * (t.card : ENNReal) ^ β)
    (hballb : ∀ j, (Zρ j).carrier ⊆ closedBall 0 1)
    (hfullb : (ShadedBody.fullness t' (fun j ↦ (Zρ j).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc)
    (hDb : Kakeya.maxDensity t' (fun j ↦ (Zρ j).toConvexSpaceBody)
      ≤ (δt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (ML2Spine.spineDiv ϖ ε₁ * β))))
    {α : Type u} {fib s' : Finset α} (hs' : s' ⊆ fib)
    {Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3))}
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3))) (m : EuclideanSpace ℝ (Fin 3))
    (hsubfib : ∀ i ∈ fib, (Z' i).carrier ⊆ T₀.carrier)
    {cst ζ ηd qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ m qc fib s' Z' U')
    (hL91 : Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2)) ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : outerLoss R ≤ δ' ^ (-cst))
    (hmax : Kakeya.maxDensity fib (fun i ↦ (Z' i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    (huni : ∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ') C))
    (hcnt : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ).Pairwise
          (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s', (U' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ))
    {Cf mu L Cu : ENNReal} {N : ℕ} {κ : ℝ}
    (hCf1 : (1 : ENNReal) ≤ Cf)
    (hsplit : mu ≤ L * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
      * ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)))
    (hcard : (t'.card : ENNReal) * (fib.card : ENNReal) ≤ Cu * (N : ENNReal))
    (hLoss : L * Cf * Cu ^ β ≤ (δt : ENNReal) ^ (-κ))
    (hqsize : qc ≤ gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) / 100)
    (hκ : κ + 3 * qc
      ≤ 20 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁) :
    mu ≤ (δt : ENNReal) ^
        (10 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁)
      * (N : ENNReal) ^ β := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  -- step 4: the coarse factor at the ambient scale `δ̃`
  have hb4 := hcoarse δt (ne_of_gt hδ0) hδtb hb1 t' Zρ hballb hfullb hDb
  -- step 10 on the REPRESENTED family, SOURCE-SITED: `hL91` is Lemma 9.1 at `gain(…)` and the
  -- `3 qc` is the eliminator's own ledger factor (refined l.6090-6095), so `ν₀` is `gain(…)`
  -- and `ν` is `gain(…) − 3 qc`, discharged by `le_of_eq`, never by `hnu`.  `hUshade`, `hret`
  -- and `hretm` are deleted: the centred representative's shading is the `normalise` image,
  -- so the first two are FALSE (V-1).
  have h10 := fine_factor_of_lemma91At_of_canonicalCover
    (ν := gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) - 3 * qc)
    hL91 hζ hsit hR hR1 hτσ hδ'0 hϖ.le hβ0.le hqc0 (le_of_eq (by ring)) h3qc T₀ m hs' Z' U' hcb
    hsubfib hloss
    huni hcnt
  have h10' : ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)
      ≤ (δ' : ENNReal) ^ (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) - 3 * qc)
        * (fib.card : ENNReal) ^ β := by
    rw [← outerFamily_multiplicity hn hsit hR hτσ hsubfib]
    exact h10
  -- step 9's split; `Cf` keeps its text and needs only `1 ≤ Cf`
  have hsplit2 : mu ≤ (L * Cf) * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
      * ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)) := by
    refine hsplit.trans (mul_le_mul' ?_ le_rfl)
    calc L = L * 1 := (mul_one L).symm
      _ ≤ L * Cf := by gcongr
  exact spine_multiplicity_le_two_factors_sourceSited hβ0 hβ1 hϖ hε₁ hgain hdens hk hδ0 hδ1
    hbw hprod hsplit2 hb4 h10' hcard hLoss hqc0.le hqsize hκ

end Kakeya.ML2Reduction

namespace Kakeya.ML2Core

universe u

/-- **Step 11 at the sharp exponent, source-sited.**
`Kakeya.ML2Core.spine_multiplicity_le_two_factors_sharp` with the same three changes; the sharp
budget `κ + 3 qc ≤ η_k/(20 e)` reserves the margin. -/
theorem spine_multiplicity_le_two_factors_sharp_sourceSited
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    {δt b δ' : NNReal} {mu mub muf L Cu : ENNReal} {Nb Nf N : ℕ} {κ qc : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    (hsplit : mu ≤ L * (mub * muf))
    (hb : mub ≤ (δt : ENNReal) ^
          (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k / (ML2Spine.spineDiv ϖ ε₁ * β))))
        * (Nb : ENNReal) ^ β)
    (hf : muf ≤ (δ' : ENNReal)
          ^ (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) - 3 * qc)
        * (Nf : ENNReal) ^ β)
    (hcard : (Nb : ENNReal) * (Nf : ENNReal) ≤ Cu * (N : ENNReal))
    (hL : L * Cu ^ β ≤ (δt : ENNReal) ^ (-κ))
    (hqc0 : 0 ≤ qc)
    (hqsize : qc ≤ gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) / 100)
    (hκ : κ + 3 * qc
      ≤ ML2Spine.spineRung β ϖ ε₁ gain dens k / (20 * ML2Spine.spineDiv ϖ ε₁)) :
    mu ≤ (δt : ENNReal) ^
          (47 * ML2Spine.spineRung β ϖ ε₁ gain dens k / (5 * ML2Spine.spineDiv ϖ ε₁))
        * (N : ENNReal) ^ β := by
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  have hpos : (0 : ℝ) < ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2 := by
    have := hsp.rung_pos (k + 1)
    linarith
  have hg : 0 ≤ gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) := (hgain _ hpos).le
  have hν : 0 ≤ gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) - 3 * qc := by linarith
  have hε₂0 : 0 < ML2Spine.spineEps₂ ϖ ε₁ := ML2Spine.spineEps₂_pos hϖ hε₁
  have hbud := spineRung_gainBudget_sharp hβ0 hβ1 hϖ hε₁ hgain hdens hk hκ
  refine ML2Reduction.multiplicity_le_of_two_factors_rescaled (by simpa using hδ0.ne')
    (by exact_mod_cast hδ1) hβ0.le hν (hsp.eps₂_le_half.trans (by norm_num))
    (ML2Reduction.rescaledScale_le hδ0 hbw hprod) hsplit hb hf hcard hL ?_
  nlinarith [hbud, hε₂0, hqc0]


open Classical in
/-- **Source-sited twin of `Kakeya.ML2Core.middle_factor_of_edNodes`.**

Binder for binder the original, with three changes and no others:
* `hL91` is bound at `gain(spineRung β ϖ ε₁ gain dens (k+1) / 2)` — Lemma 9.1 at its
  **own delivered exponent** — instead of at that exponent `+ 3 qc`;
* the source's sizing row `hqsize : qc ≤ gain(…)/100` is added (l.5988, `q ≤ ν₀/100`);
* the multiscale-loss budget reserves the margin: `hκ` reads `κ + 3 qc ≤ …`.

The **conclusion is to the original's**, so every consumer that reads
`hmid` from the original reads it unchanged from this twin — and with no `hnu`
anywhere.  Routed through the site-1 twin above.
`Kakeya.ML2Core.hnu_false_at_matched_tolerance` refutes the original's row. -/
theorem middle_factor_of_edNodes_sourceSited
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    -- the ambient window and the transport 
    {δ θ τ δt : NNReal} {Rout : ℝ} {w : ℝ}
    (hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3) (hRout : 0 < Rout)
    (hτθ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (δt : ℝ))
    (Tθ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {fib : Finset α}
    (Y : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsubOut : ∀ j ∈ fib, (Y j).carrier ⊆ Tθ.carrier)
    (hw : 0 ≤ w) (hsep : δt ≤ δ ^ w)
    -- the rescaled world 
    {b δ' : NNReal} {R : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1) (hδ'0 : 0 < δ') (hb1 : b ≤ 1) (hδtb : δt ≤ b)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))} {ηc : ℝ}
    (hcoarse : ∀ (dt : NNReal), dt ≠ 0 → dt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} (t : Finset ι) (T : ι → ShadedTube b (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ closedBall 0 1) →
        (ShadedBody.fullness t (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc →
        Kakeya.maxDensity t (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (dt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β))) →
        ShadedBody.multiplicity t (fun i ↦ (T i).toShadedBody)
          ≤ (dt : ENNReal) ^ (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β)))) * (t.card : ENNReal) ^ β)
    (hballb : ∀ j, (Zρ j).carrier ⊆ closedBall 0 1)
    (hfullb : (ShadedBody.fullness t' (fun j ↦ (Zρ j).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc)
    (hDb : Kakeya.maxDensity t' (fun j ↦ (Zρ j).toConvexSpaceBody)
      ≤ (δt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (ML2Spine.spineDiv ϖ ε₁ * β))))
    {s' : Finset α} (hs' : s' ⊆ fib)
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (hsubfib : ∀ i ∈ fib,
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier ⊆ T₀.carrier)
    {cst ζ ζ' ηd : ℝ}
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc fib s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ mm ϖ ζ s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hL91 : ML2Reduction.Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2)) ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (hmax : Kakeya.maxDensity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    -- AA/AB: tightened to the constant the producer actually returns
    -- (`ShadedTube.ssfUniformConst 3`, `Kakeya/ShadedUniform.lean:895`), with the threshold the
    -- loose bracket used to quantify away carried explicitly.  Discharged at wiring time by
    -- `exists_outerShadedUniformTubeSet_ssf` + `exists_threshold_coe_const_le_rpow_neg`.
    -- this binder is ALSO where the line-ED levels row is sourced.  The witness carries
    -- a uniform hierarchy, and `Kakeya.VeryNotSticky.lineEDLevelsAt_C3_of_huni` turns it (with
    -- `hcb`'s `centred`/`contained`/`small` rows and the uniformiser's own grid threshold) into
    -- `LineEDLevelsAt C₃ lineEDLevelsConstant _` at the NAMED constant (
    -- ): the datum is DERIVED here, never an ambient field.
    (huni : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3)))
    -- the ONE open input
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    -- stated on the CONTRACTED-bottom window `[δ'^{1-ϖ}/C, δ'^{ϖ}]`, because the
    -- centring hand-back reads the cover at `ρ/C`.  A producer of
    -- this clause must supply it on the wide window, not merely on Lemma 9.1's.
    (hED : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j l ↦ _root_.IsEssentiallyDistinct (W j).carrier (W l).carrier) ∧
        (∀ l ∈ t, (W l).carrier ⊆ T₀.carrier) ∧
        (∀ l ∈ t, ∃ i ∈ s',
          (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier
            ⊆ (W l).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    -- this is `hbudget` with `centringCountLossConstant R ·` at the head of the left-hand
    -- side, so it IMPLIES `hbudget`; `hbudget` is retained only because keeps its text
    -- tree-wide.  Discharged by `exists_threshold_hup_budget`'s argument at the
    -- new constant, never assumed; `ζ < ζ'` (`hgap`) is its side condition.
    (hcntbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hgap : ζ ≤ ζ')
    -- step 9, the cardinality multiplicativity and the loss ledger
    {Cf L Cu : ENNReal} {Nm : ℕ} {κ : ℝ}
    (hCf1 : (1 : ENNReal) ≤ Cf)
    (hsplit : ShadedBody.multiplicity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)
      ≤ L * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦
            (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)))
    (hcard : (t'.card : ENNReal) * (fib.card : ENNReal) ≤ Cu * (Nm : ENNReal))
    (hLoss : L * Cf * Cu ^ β ≤ (δt : ENNReal) ^ (-κ))
    (hqsize : qc ≤ gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) / 100)
    (hκ : κ + 3 * qc
      ≤ 20 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ENNReal) ^ (w * (10 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / ML2Spine.spineEps₂ ϖ ε₁)) * (Nm : ENNReal) ^ β := by
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  have hgm : 0 ≤ 10 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁ := by
    have h1 := hsp.rung_pos k
    have h2 := hsp.eps₂_pos
    positivity
  refine middle_factor_of_rescaled hsitOut hRout hτθ Tθ Y hsubOut hgm hw hsep ?_
  exact ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover_sourceSited hβ0 hβ1 hϖ
    hε₁ hgain
    hdens hk hδ0 hδ1 hδ'0 hb1 hδtb hbw hprod hcoarse hballb hfullb hDb hs' hsit hR hR1 hτσ T₀ mm
    hsubfib hqc0 h3qc hcb hL91 hζ hloss hmax hfull
    (Kakeya.VeryNotSticky.huni_loose_of_tight huni)
    (fun ρ hρ ↦ hct ρ hρ
      (by
        -- the cover is read at the CONTRACTED radius; `hED` moved, `hbudget` did NOT —
        -- `Kakeya.ML2Reduction.budget_descends` carries it from `ρ` down to `ρ/C` 
        have hmem := Kakeya.VeryNotSticky.mem_widened_window_of_mem hρ
        have hc0 : 0 < ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant :=
          lt_of_lt_of_le (div_pos (NNReal.rpow_pos hδ'0)
            Kakeya.VeryNotSticky.edWindowContractionConstant_pos) hmem.1
        obtain ⟨κ₀, t, W, hEDt, hsubW, hused, hcard⟩ := hED _ hmem
        obtain ⟨κ₁, t₈, W', M, hsubW', hused', hM', hMρ', hcard'⟩ :=
          hstep8_of_essDistinct t W hEDt hsubW hused hcard
        exact ML2Reduction.canonicalCoverAt_of_step8_const (m := 0) (ζ' := ζ')
          (Kc := (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ))
          hsit hR T₀ _ hc0
          (le_trans (by exact_mod_cast hmem.2) hwin4) t₈ W' hsubW' hused' hM' hMρ' hcard'
          (ML2Reduction.budget_descends
            (h := ML2Reduction.hbud_of_hcntbudget (NNReal.coe_nonneg _)
              (by simpa using hcntbudget ρ hρ))
            (hρ'0 := by exact_mod_cast hc0)
            (hle := by exact_mod_cast Kakeya.VeryNotSticky.div_centringCoverRadiusConstant_le ρ)
            (he := by linarith))))
    hCf1 hsplit hcard hLoss hqsize hκ


open Classical in
/-- **Source-sited twin of `Kakeya.ML2Core.middle_factor_of_edNodes_sharp`.**

Binder for binder the original, with three changes and no others:
* `hL91` is bound at `gain(spineRung β ϖ ε₁ gain dens (k+1) / 2)` — Lemma 9.1 at its
  **own delivered exponent** — instead of at that exponent `+ 3 qc`;
* the source's sizing row `hqsize : qc ≤ gain(…)/100` is added (l.5988, `q ≤ ν₀/100`);
* the multiscale-loss budget reserves the margin: `hκ` reads `κ + 3 qc ≤ …`.

The **conclusion is to the original's**, so every consumer that reads
`hmid` from the original reads it unchanged from this twin — and with no `hnu`
anywhere.  Routed through `spine_multiplicity_le_two_factors_sharp_sourceSited`.
`Kakeya.ML2Core.hnu_false_at_matched_tolerance` refutes the original's row. -/
theorem middle_factor_of_edNodes_sharp_sourceSited
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    -- the ambient window and the transport 
    {δ θ τ δt : NNReal} {Rout : ℝ} {w : ℝ}
    (hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3) (hRout : 0 < Rout)
    (hτθ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (δt : ℝ))
    (Tθ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {fib : Finset α}
    (Y : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsubOut : ∀ j ∈ fib, (Y j).carrier ⊆ Tθ.carrier)
    (hw : 0 ≤ w) (hsep : δt ≤ δ ^ w)
    -- the rescaled world 
    {b δ' : NNReal} {R : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1) (hδ'0 : 0 < δ') (hb1 : b ≤ 1) (hδtb : δt ≤ b)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))} {ηc : ℝ}
    (hcoarse : ∀ (dt : NNReal), dt ≠ 0 → dt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} (t : Finset ι) (T : ι → ShadedTube b (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ closedBall 0 1) →
        (ShadedBody.fullness t (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc →
        Kakeya.maxDensity t (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (dt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β))) →
        ShadedBody.multiplicity t (fun i ↦ (T i).toShadedBody)
          ≤ (dt : ENNReal) ^ (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β)))) * (t.card : ENNReal) ^ β)
    (hballb : ∀ j, (Zρ j).carrier ⊆ closedBall 0 1)
    (hfullb : (ShadedBody.fullness t' (fun j ↦ (Zρ j).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc)
    (hDb : Kakeya.maxDensity t' (fun j ↦ (Zρ j).toConvexSpaceBody)
      ≤ (δt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (ML2Spine.spineDiv ϖ ε₁ * β))))
    {s' : Finset α} (hs' : s' ⊆ fib)
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (hsubfib : ∀ i ∈ fib,
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier ⊆ T₀.carrier)
    {cst ζ ζ' ηd : ℝ}
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc fib s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ mm ϖ ζ s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hL91 : ML2Reduction.Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2)) ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (hmax : Kakeya.maxDensity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    -- AA/AB: tightened to the constant the producer actually returns
    -- (`ShadedTube.ssfUniformConst 3`, `Kakeya/ShadedUniform.lean:895`), with the threshold the
    -- loose bracket used to quantify away carried explicitly.  Discharged at wiring time by
    -- `exists_outerShadedUniformTubeSet_ssf` + `exists_threshold_coe_const_le_rpow_neg`.
    -- this binder is ALSO where the line-ED levels row is sourced.  The witness carries
    -- a uniform hierarchy, and `Kakeya.VeryNotSticky.lineEDLevelsAt_C3_of_huni` turns it (with
    -- `hcb`'s `centred`/`contained`/`small` rows and the uniformiser's own grid threshold) into
    -- `LineEDLevelsAt C₃ lineEDLevelsConstant _` at the NAMED constant (
    -- ): the datum is DERIVED here, never an ambient field.
    (huni : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3)))
    -- the ONE open input
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    -- stated on the CONTRACTED-bottom window `[δ'^{1-ϖ}/C, δ'^{ϖ}]`, because the
    -- centring hand-back reads the cover at `ρ/C`.  A producer of
    -- this clause must supply it on the wide window, not merely on Lemma 9.1's.
    (hED : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j l ↦ _root_.IsEssentiallyDistinct (W j).carrier (W l).carrier) ∧
        (∀ l ∈ t, (W l).carrier ⊆ T₀.carrier) ∧
        (∀ l ∈ t, ∃ i ∈ s',
          (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier
            ⊆ (W l).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    -- this is `hbudget` with `centringCountLossConstant R ·` at the head of the left-hand
    -- side, so it IMPLIES `hbudget`; `hbudget` is retained only because keeps its text
    -- tree-wide.  Discharged by `exists_threshold_hup_budget`'s argument at the
    -- new constant, never assumed; `ζ < ζ'` (`hgap`) is its side condition.
    (hcntbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hgap : ζ ≤ ζ')
    -- step 9, the cardinality multiplicativity and the loss ledger
    {Cf L Cu : ENNReal} {Nm : ℕ} {κ : ℝ}
    (hCf1 : (1 : ENNReal) ≤ Cf)
    (hsplit : ShadedBody.multiplicity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)
      ≤ L * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦
            (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)))
    (hcard : (t'.card : ENNReal) * (fib.card : ENNReal) ≤ Cu * (Nm : ENNReal))
    (hLoss : L * Cf * Cu ^ β ≤ (δt : ENNReal) ^ (-κ))
    (hqsize : qc ≤ gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) / 100)
    (hκ : κ + 3 * qc
      ≤ ML2Spine.spineRung β ϖ ε₁ gain dens k / (20 * ML2Spine.spineDiv ϖ ε₁)) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ENNReal) ^ (w * (47 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (5 * ML2Spine.spineDiv ϖ ε₁))) * (Nm : ENNReal) ^ β := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  have hgm : 0 ≤ 47 * ML2Spine.spineRung β ϖ ε₁ gain dens k / (5 * ML2Spine.spineDiv ϖ ε₁) := by
    have h1 := hsp.rung_pos k
    have h2 := hsp.div_pos
    positivity
  refine middle_factor_of_rescaled hsitOut hRout hτθ Tθ Y hsubOut hgm hw hsep ?_
  set Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)) :=
    ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y with hZ'
  have hb4 := hcoarse δt (ne_of_gt hδ0) hδtb hb1 t' Zρ hballb hfullb hDb
  -- Step 10 on the REPRESENTED family (the UNPRIMED eliminator): the hand-back's `3 qc`
  -- transport is inside it, so the `3 qc` is charged exactly once, on `hL91`'s gain (V-3).
  -- `Cf` keeps its text in `hLoss` and needs only `1 ≤ Cf`.
  have h10 := ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover
    (ν := gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) - 3 * qc)
    hL91 hζ hsit hR hR1 hτσ hδ'0 hϖ.le hβ0.le hqc0 (le_of_eq (by ring)) h3qc T₀ mm hs'
    (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U' hcb hsubfib hloss
    (Kakeya.VeryNotSticky.huni_loose_of_tight huni)
    (fun ρ hρ ↦ hct ρ hρ
      (by
        -- the cover is read at the CONTRACTED radius; `hED` moved, `hbudget` did NOT —
        -- `Kakeya.ML2Reduction.budget_descends` carries it from `ρ` down to `ρ/C` 
        have hmem := Kakeya.VeryNotSticky.mem_widened_window_of_mem hρ
        have hc0 : 0 < ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant :=
          lt_of_lt_of_le (div_pos (NNReal.rpow_pos hδ'0)
            Kakeya.VeryNotSticky.edWindowContractionConstant_pos) hmem.1
        obtain ⟨κ₀, t, W, hEDt, hsubW, hused, hcard⟩ := hED _ hmem
        obtain ⟨κ₁, t₈, W', M, hsubW', hused', hM', hMρ', hcard'⟩ :=
          hstep8_of_essDistinct t W hEDt hsubW hused hcard
        exact ML2Reduction.canonicalCoverAt_of_step8_const (m := 0) (ζ' := ζ')
          (Kc := (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ))
          hsit hR T₀ _ hc0
          (le_trans (by exact_mod_cast hmem.2) hwin4) t₈ W' hsubW' hused' hM' hMρ' hcard'
          (ML2Reduction.budget_descends
            (h := ML2Reduction.hbud_of_hcntbudget (NNReal.coe_nonneg _)
              (by simpa using hcntbudget ρ hρ))
            (hρ'0 := by exact_mod_cast hc0)
            (hle := by exact_mod_cast Kakeya.VeryNotSticky.div_centringCoverRadiusConstant_le ρ)
            (he := by linarith))))
  have h10' : ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)
      ≤ (δ' : ENNReal) ^ (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) - 3 * qc)
        * (fib.card : ENNReal) ^ β := by
    rw [← ML2Reduction.outerFamily_multiplicity hn hsit hR hτσ hsubfib]
    exact h10
  have hsplit2 : ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)
      ≤ (L * Cf) * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)) := by
    refine hsplit.trans (mul_le_mul' ?_ le_rfl)
    calc L = L * 1 := (mul_one L).symm
      _ ≤ L * Cf := by gcongr
  exact spine_multiplicity_le_two_factors_sharp_sourceSited hβ0 hβ1 hϖ hε₁ hgain hdens hk hδ0
    hδ1 hbw hprod
    hsplit2 hb4 h10' hcard hLoss hqc0.le hqsize hκ


open Classical in
/-- **Source-sited twin of `Kakeya.ML2Core.middle_factor_of_canonicalCover_sharp`.**

Binder for binder the original, with three changes and no others:
* `hL91` is bound at `gain(spineRung β ϖ ε₁ gain dens (k+1) / 2)` — Lemma 9.1 at its
  **own delivered exponent** — instead of at that exponent `+ 3 qc`;
* the source's sizing row `hqsize : qc ≤ gain(…)/100` is added (l.5988, `q ≤ ν₀/100`);
* the multiscale-loss budget reserves the margin: `hκ` reads `κ + 3 qc ≤ …`.

The **conclusion is to the original's**, so every consumer that reads
`hmid` from the original reads it unchanged from this twin — and with no `hnu`
anywhere.  Routed through `spine_multiplicity_le_two_factors_sharp_sourceSited`.
`Kakeya.ML2Core.hnu_false_at_matched_tolerance` refutes the original's row. -/
theorem middle_factor_of_canonicalCover_sharp_sourceSited
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    -- the ambient window and the transport 
    {δ θ τ δt : NNReal} {Rout : ℝ} {w : ℝ}
    (hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3) (hRout : 0 < Rout)
    (hτθ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (δt : ℝ))
    (Tθ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {fib : Finset α}
    (Y : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsubOut : ∀ j ∈ fib, (Y j).carrier ⊆ Tθ.carrier)
    (hw : 0 ≤ w) (hsep : δt ≤ δ ^ w)
    -- the rescaled world 
    {b δ' : NNReal} {R : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1) (hδ'0 : 0 < δ') (hb1 : b ≤ 1) (hδtb : δt ≤ b)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))} {ηc : ℝ}
    (hcoarse : ∀ (dt : NNReal), dt ≠ 0 → dt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} (t : Finset ι) (T : ι → ShadedTube b (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ closedBall 0 1) →
        (ShadedBody.fullness t (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc →
        Kakeya.maxDensity t (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (dt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β))) →
        ShadedBody.multiplicity t (fun i ↦ (T i).toShadedBody)
          ≤ (dt : ENNReal) ^ (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β)))) * (t.card : ENNReal) ^ β)
    (hballb : ∀ j, (Zρ j).carrier ⊆ closedBall 0 1)
    (hfullb : (ShadedBody.fullness t' (fun j ↦ (Zρ j).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc)
    (hDb : Kakeya.maxDensity t' (fun j ↦ (Zρ j).toConvexSpaceBody)
      ≤ (δt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (ML2Spine.spineDiv ϖ ε₁ * β))))
    {s' : Finset α} (hs' : s' ⊆ fib)
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (hsubfib : ∀ i ∈ fib,
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier ⊆ T₀.carrier)
    {cst ζ ηd : ℝ}
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc fib s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hL91 : ML2Reduction.Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2)) ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (hmax : Kakeya.maxDensity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    (huni : ∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ') C))
    -- step 10's datum, factored out: the count clause at the CENTRED representatives, which is
    -- `Kakeya.ML2Reduction.Lemma91At`'s clause verbatim.  A caller holding the canonical cover on
    -- the *rescaled bodies* reaches this through `Kakeya.VeryNotSticky.CountTransport`.
    (hcnt : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      ∃ (κ₁ : Type u) (tρ : Finset κ₁) (Tρ : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ₁).Pairwise
          (fun j l ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ l).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s', (U' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ))
    -- step 9, the cardinality multiplicativity and the loss ledger
    {Cf L Cu : ENNReal} {Nm : ℕ} {κ : ℝ}
    (hCf1 : (1 : ENNReal) ≤ Cf)
    (hsplit : ShadedBody.multiplicity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)
      ≤ L * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦
            (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)))
    (hcard : (t'.card : ENNReal) * (fib.card : ENNReal) ≤ Cu * (Nm : ENNReal))
    (hLoss : L * Cf * Cu ^ β ≤ (δt : ENNReal) ^ (-κ))
    (hqsize : qc ≤ gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) / 100)
    (hκ : κ + 3 * qc
      ≤ ML2Spine.spineRung β ϖ ε₁ gain dens k / (20 * ML2Spine.spineDiv ϖ ε₁)) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ENNReal) ^ (w * (47 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (5 * ML2Spine.spineDiv ϖ ε₁))) * (Nm : ENNReal) ^ β := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  have hgm : 0 ≤ 47 * ML2Spine.spineRung β ϖ ε₁ gain dens k / (5 * ML2Spine.spineDiv ϖ ε₁) := by
    have h1 := hsp.rung_pos k
    have h2 := hsp.div_pos
    positivity
  refine middle_factor_of_rescaled hsitOut hRout hτθ Tθ Y hsubOut hgm hw hsep ?_
  set Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)) :=
    ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y with hZ'
  have hb4 := hcoarse δt (ne_of_gt hδ0) hδtb hb1 t' Zρ hballb hfullb hDb
  -- Step 10 on the REPRESENTED family.  The hand-back's transport is *inside* the eliminator, so
  -- the `3 qc` is charged exactly once — in `hL91`'s gain (V-3).  `hU`, `hUshade`, `hret` and
  -- `hretm` are gone: the centred representative is the `normalise` image of the rescaled body,
  -- not the rescaled body, so `hU`/`hUshade` are false and `Cf` needs only `1 ≤ Cf`.
  have h10 := ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover
    (ν := gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) - 3 * qc)
    hL91 hζ hsit hR hR1 hτσ hδ'0 hϖ.le hβ0.le hqc0 (le_of_eq (by ring)) h3qc T₀ mm hs' Z' U'
    hcb hsubfib hloss
    huni hcnt
  have h10' : ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)
      ≤ (δ' : ENNReal) ^ (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) - 3 * qc)
        * (fib.card : ENNReal) ^ β := by
    rw [← ML2Reduction.outerFamily_multiplicity hn hsit hR hτσ hsubfib]
    exact h10
  have hsplit2 : ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)
      ≤ (L * Cf) * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)) := by
    refine hsplit.trans (mul_le_mul' ?_ le_rfl)
    calc L = L * 1 := (mul_one L).symm
      _ ≤ L * Cf := by gcongr
  exact spine_multiplicity_le_two_factors_sharp_sourceSited hβ0 hβ1 hϖ hε₁ hgain hdens hk hδ0
    hδ1 hbw hprod
    hsplit2 hb4 h10' hcard hLoss hqc0.le hqsize hκ


open Classical in
/-- **Source-sited twin of `Kakeya.ML2Core.middle_factor_of_edNodes_sharp'`.**

Binder for binder the original, with three changes and no others:
* `hL91` is bound at `gain(spineRung β ϖ ε₁ gain dens (k+1) / 2)` — Lemma 9.1 at its
  **own delivered exponent** — instead of at that exponent `+ 3 qc`;
* the source's sizing row `hqsize : qc ≤ gain(…)/100` is added (l.5988, `q ≤ ν₀/100`);
* the multiscale-loss budget reserves the margin: `hκ` reads `κ + 3 qc ≤ …`.

The **conclusion is to the original's**, so every consumer that reads
`hmid` from the original reads it unchanged from this twin — and with no `hnu`
anywhere.  Routed through the site-4 twin above.
`Kakeya.ML2Core.hnu_false_at_matched_tolerance` refutes the original's row. -/
theorem middle_factor_of_edNodes_sharp'_sourceSited
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    -- the ambient window and the transport 
    {δ θ τ δt : NNReal} {Rout : ℝ} {w : ℝ}
    (hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3) (hRout : 0 < Rout)
    (hτθ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (δt : ℝ))
    (Tθ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {fib : Finset α}
    (Y : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsubOut : ∀ j ∈ fib, (Y j).carrier ⊆ Tθ.carrier)
    (hw : 0 ≤ w) (hsep : δt ≤ δ ^ w)
    -- the rescaled world 
    {b δ' : NNReal} {R : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1) (hδ'0 : 0 < δ') (hb1 : b ≤ 1) (hδtb : δt ≤ b)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))} {ηc : ℝ}
    (hcoarse : ∀ (dt : NNReal), dt ≠ 0 → dt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} (t : Finset ι) (T : ι → ShadedTube b (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ closedBall 0 1) →
        (ShadedBody.fullness t (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc →
        Kakeya.maxDensity t (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (dt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β))) →
        ShadedBody.multiplicity t (fun i ↦ (T i).toShadedBody)
          ≤ (dt : ENNReal) ^ (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β)))) * (t.card : ENNReal) ^ β)
    (hballb : ∀ j, (Zρ j).carrier ⊆ closedBall 0 1)
    (hfullb : (ShadedBody.fullness t' (fun j ↦ (Zρ j).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc)
    (hDb : Kakeya.maxDensity t' (fun j ↦ (Zρ j).toConvexSpaceBody)
      ≤ (δt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (ML2Spine.spineDiv ϖ ε₁ * β))))
    {s' : Finset α} (hs' : s' ⊆ fib)
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (hsubfib : ∀ i ∈ fib,
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier ⊆ T₀.carrier)
    {cst ζ ζ' ηd : ℝ}
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc fib s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ mm ϖ ζ s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hL91 : ML2Reduction.Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2)) ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (hmax : Kakeya.maxDensity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    -- AA/AB: tightened to the constant the producer actually returns
    -- (`ShadedTube.ssfUniformConst 3`, `Kakeya/ShadedUniform.lean:895`), with the threshold the
    -- loose bracket used to quantify away carried explicitly.  Discharged at wiring time by
    -- `exists_outerShadedUniformTubeSet_ssf` + `exists_threshold_coe_const_le_rpow_neg`.
    -- this binder is ALSO where the line-ED levels row is sourced.  The witness carries
    -- a uniform hierarchy, and `Kakeya.VeryNotSticky.lineEDLevelsAt_C3_of_huni` turns it (with
    -- `hcb`'s `centred`/`contained`/`small` rows and the uniformiser's own grid threshold) into
    -- `LineEDLevelsAt C₃ lineEDLevelsConstant _` at the NAMED constant (
    -- ): the datum is DERIVED here, never an ambient field.
    (huni : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3)))
    -- the ONE open input
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    -- CONTRACTED-bottom window `[δ'^{1-ϖ}/C, δ'^{ϖ}]` — the hand-back reads the cover
    -- at `ρ/C`.  A producer must supply this clause on the wide
    -- window.  `hbudget` below did NOT move: `Kakeya.ML2Reduction.budget_descends` carries
    -- it from `ρ` down to `ρ/C`, at the cost of the reading gap `hgap`.
    (hED : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j l ↦ _root_.IsEssentiallyDistinct (W j).carrier (W l).carrier) ∧
        (∀ l ∈ t, (W l).carrier ⊆ T₀.carrier) ∧
        (∀ l ∈ t, ∃ i ∈ s',
          (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier
            ⊆ (W l).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    -- this is `hbudget` with `centringCountLossConstant R ·` at the head of the left-hand
    -- side, so it IMPLIES `hbudget`; `hbudget` is retained only because keeps its text
    -- tree-wide.  Discharged by `exists_threshold_hup_budget`'s argument at the
    -- new constant, never assumed; `ζ < ζ'` (`hgap`) is its side condition.
    (hcntbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hgap : ζ ≤ ζ')
    -- step 9, the cardinality multiplicativity and the loss ledger
    {Cf L Cu : ENNReal} {Nm : ℕ} {κ : ℝ}
    (hCf1 : (1 : ENNReal) ≤ Cf)
    (hsplit : ShadedBody.multiplicity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)
      ≤ L * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦
            (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)))
    (hcard : (t'.card : ENNReal) * (fib.card : ENNReal) ≤ Cu * (Nm : ENNReal))
    (hLoss : L * Cf * Cu ^ β ≤ (δt : ENNReal) ^ (-κ))
    (hqsize : qc ≤ gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) / 100)
    (hκ : κ + 3 * qc
      ≤ ML2Spine.spineRung β ϖ ε₁ gain dens k / (20 * ML2Spine.spineDiv ϖ ε₁)) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ENNReal) ^ (w * (47 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (5 * ML2Spine.spineDiv ϖ ε₁))) * (Nm : ENNReal) ^ β :=
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  middle_factor_of_canonicalCover_sharp_sourceSited hβ0 hβ1 hϖ hε₁ hgain hdens hk hsitOut hRout
    hτθ Tθ Y
    hsubOut hw hsep hδ0 hδ1 hδ'0 hb1 hδtb hbw hprod hcoarse hballb hfullb hDb hs' hsit hR hR1
    hτσ T₀ hsubfib mm hqc0 h3qc hcb hL91 hζ hloss hmax hfull
    (Kakeya.VeryNotSticky.huni_loose_of_tight huni)
    (fun ρ hρ ↦ hct ρ hρ
      (by
        -- the cover is read at the CONTRACTED radius; `hED` moved, `hbudget` did NOT —
        -- `Kakeya.ML2Reduction.budget_descends` carries it from `ρ` down to `ρ/C` 
        have hmem := Kakeya.VeryNotSticky.mem_widened_window_of_mem hρ
        have hc0 : 0 < ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant :=
          lt_of_lt_of_le (div_pos (NNReal.rpow_pos hδ'0)
            Kakeya.VeryNotSticky.edWindowContractionConstant_pos) hmem.1
        obtain ⟨κ₀, t, W, hEDt, hsubW, hused, hcard⟩ := hED _ hmem
        obtain ⟨κ₁, t₈, W', M, hsubW', hused', hM', hMρ', hcard'⟩ :=
          hstep8_of_essDistinct t W hEDt hsubW hused hcard
        exact ML2Reduction.canonicalCoverAt_of_step8_const (m := 0) (ζ' := ζ')
          (Kc := (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ))
          hsit hR T₀ _ hc0
          (le_trans (by exact_mod_cast hmem.2) hwin4) t₈ W' hsubW' hused' hM' hMρ' hcard'
          (ML2Reduction.budget_descends
            (h := ML2Reduction.hbud_of_hcntbudget (NNReal.coe_nonneg _)
              (by simpa using hcntbudget ρ hρ))
            (hρ'0 := by exact_mod_cast hc0)
            (hle := by exact_mod_cast Kakeya.VeryNotSticky.div_centringCoverRadiusConstant_le ρ)
            (he := by linarith))))
    hCf1 hsplit hcard hLoss hqsize hκ


open Classical in
/-- **Source-sited twin of `Kakeya.ML2Core.middle_factor_of_lineEDNodes_sharp`.**

Binder for binder the original, with three changes and no others:
* `hL91` is bound at `gain(spineRung β ϖ ε₁ gain dens (k+1) / 2)` — Lemma 9.1 at its
  **own delivered exponent** — instead of at that exponent `+ 3 qc`;
* the source's sizing row `hqsize : qc ≤ gain(…)/100` is added (l.5988, `q ≤ ν₀/100`);
* the multiscale-loss budget reserves the margin: `hκ` reads `κ + 3 qc ≤ …`.

The **conclusion is to the original's**, so every consumer that reads
`hmid` from the original reads it unchanged from this twin — and with no `hnu`
anywhere.  Routed through the site-4 twin above.
`Kakeya.ML2Core.hnu_false_at_matched_tolerance` refutes the original's row. -/
theorem middle_factor_of_lineEDNodes_sharp_sourceSited
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    -- the ambient window and the transport 
    {δ θ τ δt : NNReal} {Rout : ℝ} {w : ℝ}
    (hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3) (hRout : 0 < Rout)
    (hτθ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (δt : ℝ))
    (Tθ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {fib : Finset α}
    (Y : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsubOut : ∀ j ∈ fib, (Y j).carrier ⊆ Tθ.carrier)
    (hw : 0 ≤ w) (hsep : δt ≤ δ ^ w)
    -- the rescaled world 
    {b δ' : NNReal} {R : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1) (hδ'0 : 0 < δ') (hb1 : b ≤ 1) (hδtb : δt ≤ b)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))} {ηc : ℝ}
    (hcoarse : ∀ (dt : NNReal), dt ≠ 0 → dt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} (t : Finset ι) (T : ι → ShadedTube b (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ closedBall 0 1) →
        (ShadedBody.fullness t (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc →
        Kakeya.maxDensity t (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (dt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β))) →
        ShadedBody.multiplicity t (fun i ↦ (T i).toShadedBody)
          ≤ (dt : ENNReal) ^ (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β)))) * (t.card : ENNReal) ^ β)
    (hballb : ∀ j, (Zρ j).carrier ⊆ closedBall 0 1)
    (hfullb : (ShadedBody.fullness t' (fun j ↦ (Zρ j).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc)
    (hDb : Kakeya.maxDensity t' (fun j ↦ (Zρ j).toConvexSpaceBody)
      ≤ (δt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (ML2Spine.spineDiv ϖ ε₁ * β))))
    {s' : Finset α} (hs' : s' ⊆ fib)
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (hsubfib : ∀ i ∈ fib,
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier ⊆ T₀.carrier)
    {cst ζ ζ' ηd : ℝ}
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc fib s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ mm ϖ ζ s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hL91 : ML2Reduction.Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2)) ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (hmax : Kakeya.maxDensity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    -- AA/AB: tightened to the constant the producer actually returns
    -- (`ShadedTube.ssfUniformConst 3`, `Kakeya/ShadedUniform.lean:895`), with the threshold the
    -- loose bracket used to quantify away carried explicitly.  Discharged at wiring time by
    -- `exists_outerShadedUniformTubeSet_ssf` + `exists_threshold_coe_const_le_rpow_neg`.
    -- this binder is ALSO where the line-ED levels row is sourced.  The witness carries
    -- a uniform hierarchy, and `Kakeya.VeryNotSticky.lineEDLevelsAt_C3_of_huni` turns it (with
    -- `hcb`'s `centred`/`contained`/`small` rows and the uniformiser's own grid threshold) into
    -- `LineEDLevelsAt C₃ lineEDLevelsConstant _` at the NAMED constant (
    -- ): the datum is DERIVED here, never an ambient field.
    (huni : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3)))
    -- the ONE open input, line-based
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    {A : ℕ} (hA0 : 0 < A)
    -- CONTRACTED-bottom window `[δ'^{1-ϖ}/C, δ'^{ϖ}]` — the hand-back reads the cover
    -- at `ρ/C`.  A producer must supply this clause on the wide
    -- window.  `hbudget` below did NOT move: `Kakeya.ML2Reduction.budget_descends` carries
    -- it from `ρ` down to `ρ/C`, at the cost of the reading gap `hgap`.
    (hEDline : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3) A t W ∧
        (∀ l ∈ t, (W l).carrier ⊆ T₀.carrier) ∧
        (∀ l ∈ t, ∃ i ∈ s',
          (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier
            ⊆ (W l).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (A : ℝ) * (ML2Reduction.lineEDPushConstant R : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    -- this is `hbudget` with `centringCountLossConstant R ·` at the head of the left-hand
    -- side, so it IMPLIES `hbudget`; `hbudget` is retained only because keeps its text
    -- tree-wide.  Discharged by `exists_threshold_hup_budget`'s argument at the
    -- new constant, never assumed; `ζ < ζ'` (`hgap`) is its side condition.  The `A` here is
    -- `hEDline`'s carried line-ED constant — the same `A` that `hbudget` above already prices,
    -- not a fresh variable: the twin's whole price is that constant (`A₁ = 2·641⁶` at the
    -- refined reading), and it is a threshold on the scale, not an exponent.  This is the one
    -- site whose left-hand side is `A · lineEDPushConstant R · spineOuterCountLoss R` rather
    -- than the `⌈…⌉₊` form, so it is the first threshold to check.
    (hcntbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (A : ℝ) * (ML2Reduction.lineEDPushConstant R : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hgap : ζ ≤ ζ')
    -- step 9, the cardinality multiplicativity and the loss ledger
    {Cf L Cu : ENNReal} {Nm : ℕ} {κ : ℝ}
    (hCf1 : (1 : ENNReal) ≤ Cf)
    (hsplit : ShadedBody.multiplicity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)
      ≤ L * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦
            (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)))
    (hcard : (t'.card : ENNReal) * (fib.card : ENNReal) ≤ Cu * (Nm : ENNReal))
    (hLoss : L * Cf * Cu ^ β ≤ (δt : ENNReal) ^ (-κ))
    (hqsize : qc ≤ gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) / 100)
    (hκ : κ + 3 * qc
      ≤ ML2Spine.spineRung β ϖ ε₁ gain dens k / (20 * ML2Spine.spineDiv ϖ ε₁)) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ENNReal) ^ (w * (47 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (5 * ML2Spine.spineDiv ϖ ε₁))) * (Nm : ENNReal) ^ β :=
  middle_factor_of_canonicalCover_sharp_sourceSited hβ0 hβ1 hϖ hε₁ hgain hdens hk hsitOut hRout
    hτθ Tθ Y
    hsubOut hw hsep hδ0 hδ1 hδ'0 hb1 hδtb hbw hprod hcoarse hballb hfullb hDb hs' hsit hR hR1
    hτσ T₀ hsubfib mm hqc0 h3qc hcb hL91 hζ hloss hmax hfull
    (Kakeya.VeryNotSticky.huni_loose_of_tight huni)
    (fun ρ hρ ↦ hct ρ hρ
      (by
        -- as above, through the LINE-based pointwise cover
        have hmem := Kakeya.VeryNotSticky.mem_widened_window_of_mem hρ
        have hc0 : 0 < ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant :=
          lt_of_lt_of_le (div_pos (NNReal.rpow_pos hδ'0)
            Kakeya.VeryNotSticky.edWindowContractionConstant_pos) hmem.1
        obtain ⟨κ₀, t, W, hline, hsubW, hused, hcard⟩ := hEDline _ hmem
        exact ML2Reduction.canonicalCoverAt_of_upstairs_lineED_const (ζ' := ζ')
          (Kc := (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ))
          (NNReal.coe_nonneg _) hsit hR T₀ _ hc0
          (le_trans (by exact_mod_cast hmem.2) hwin4) t W hsubW hused hA0 hline
          (ML2Reduction.budget_descends
            (h := by
              have h1 := ML2Reduction.le_of_mul_spineOuterCountLoss (R := R)
                (x := (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ) * (A : ℝ)
                  * (ML2Reduction.lineEDPushConstant R : ℝ)) (by positivity)
                (hcntbudget ρ hρ)
              have hEq : (A : ℝ) * (ML2Reduction.lineEDPushConstant R : ℝ)
                    * (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
                  = (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ) * (A : ℝ)
                    * (ML2Reduction.lineEDPushConstant R : ℝ) := by ring
              rw [hEq]; exact h1)
            (hρ'0 := by exact_mod_cast hc0)
            (hle := by exact_mod_cast Kakeya.VeryNotSticky.div_centringCoverRadiusConstant_le ρ)
            (he := by linarith)) hcard))
    hCf1 hsplit hcard hLoss hqsize hκ


end Kakeya.ML2Core

end
