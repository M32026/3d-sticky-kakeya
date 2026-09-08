/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.KKTResidualProps
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCardBand

/-!
# The large-family partial Katz--Tao estimate `L(γ)`, and the reduction's branch (i)

steps **A0** . Two things are established here.

## 1. `L(γ)`, the conclusion-side large-family restriction

`Kakeya.ML2Cap.KatzTaoEstimateLargeOne` is a token-copy of GWZ Definition 3.4
(`Kakeya.KatzTaoEstimate`) with **one extra binder** after fullness,

  `(δ : ℝ)⁻¹ ≤ (s.card : ℝ)`,

i.e. Prof. Hong Wang's standing assumption `|𝕋| > δ^{-1}` (clarification of 2026-08-30, part 3).
The restriction lives **on the conclusion side, in a new definition**: no cardinality clause is
added to the hypothesis side of `Kakeya.KatzTaoEstimate`, and nothing existing is edited. That
placement is not cosmetic — a clause on `Kakeya.KatzTaoEstimate` itself breaks the two internal
sites that consume it at small families (GWZ Lemma 6.1's high branch and Lemma 9.1's tangential
fibres; `Kakeya.KKTResidual.residualA_iff_katzTaoEstimate`,
`Kakeya.KKTResidual.strict_clause_false_at_fibre`).

The threshold is `δ^{-1}`, exactly the one `Kakeya.ML2Assembly.Dichotomy` carries, and one power
weaker than the `δ^{-2}` of `Kakeya.KKTResidual.KatzTaoEstimateStrict`; hence
`Kakeya.ML2Cap.strict_of_largeOne` but not the converse.

## 2. What branch (i) of the reduction closes with no `SmallCard`

`Kakeya.ML2Cap.largeOne_of_dichotomy` is the body of
`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` **with the `hsmall` hypothesis deleted**:
under the two `ε`-free budgets `2c ≤ β` and `4c ≤ g`, the GWZ dichotomy at absolute accuracy
`β/2` gives `L(β - c)` outright. Alternative (i) closes by
`Kakeya.MainLemma2.Reduction.katzTaoGoal_of_absoluteLoss_of_card_ge` at threshold exponent `θ₀ = 1`
(budget `β/2 ≤ ε + (β - c)`, which needs `θ₀ ≤ 1` and is where `2c ≤ β` is spent); alternative
(ii) is verbatim the tree's, through the crude cardinality bound
`Kakeya.ML2Assembly.card_le_rpow_neg_four` and
`Kakeya.ML2Reduction.le_rpow_mul_rpow_of_gain`. Note that the `min η ηs` of the tree's version
disappears with `hsmall`: there is only one density exponent left to serve.

**Why this is the band's first steps.** The band  is
`Kakeya.ML2Assembly.SmallCard`, and `Kakeya.ML2Squeeze.smallCard_iff_katzTaoEstimate` shows it
is not a fragment of Main Lemma 2 but a restatement of `K_KT` at the same exponent. So the band
cannot be discharged from `K_KT(β)`; it has to be proved *from the large-family estimate*, by
the Cap Lemma `L(γ) → K_KT(γ)` of §1.2 (steps A2--A6, not proved here). This file pins
that Cap Lemma's hypothesis: `largeOne_of_dichotomy` shows in the kernel that everything the
reduction's branch (i) delivers is `L(β - c)`, and that no `SmallCard` is used in delivering
it, so `L` is exactly the object A2--A6 must consume.

`Kakeya.ML2Cap.smallCard_of_katzTaoEstimate` is the re-export that closes the loop on the other
side: once the Cap Lemma turns `L(β - c)` into `K_KT(β - c)`, the reduction's remaining hypothesis
`Kakeya.ML2Assembly.SmallCard (β - c)` follows by dropping a binder, and
`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` needs nothing further. (Two homonyms already
exist: `Kakeya.ML2Band.smallCard_of_katzTaoEstimate`, and one of the same short name in
`Reduction/BandSqueezeAlt.lean` under the `ML2BandSqz` prefix, which is outside this module's
import closure.  This declaration is a definitional re-export of the former under the
`Kakeya.ML2Cap` prefix, not a reproof.)

Nothing in this file is left unproved; no `axiom`, `opaque` or `native_decide` is declared; no
existing declaration is edited; and no module of the abandoned Wang--Zahl route is imported.
-/

@[expose] public section

open MeasureTheory Topology ConvexSpaceBody Filter ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Cap

universe u

/-! ## The definition -/

section Definition

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **`L(γ)`, the large-family partial Katz--Tao estimate.**  GWZ Definition 3.4
(`Kakeya.KatzTaoEstimate`, verbatim) with the extra hypothesis `δ^{-1} ≤ |𝕋|` after fullness —
Prof. Hong Wang's standing assumption for Main Lemma 2, and exactly the cardinality binder of
`Kakeya.ML2Assembly.Dichotomy`.

This is a **new definition**: the clause is on the conclusion side and
`Kakeya.KatzTaoEstimate` is untouched. -/
def KatzTaoEstimateLargeOne (γ : ℝ) : Prop := ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (- η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
      ∑ i ∈ s, volume (T i).shade ≤ δ ^ (- ε) * s.card ^ γ * volume (⋃ i ∈ s, (T i).shade)

end Definition

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `L(γ)` is monotone in the exponent, exactly as `Kakeya.KatzTaoEstimate.mono` is: a family with
`δ^{-1} ≤ |𝕋|` is in particular non-empty, so `|𝕋|^γ ≤ |𝕋|^{γ'}` for `γ ≤ γ'`. -/
theorem KatzTaoEstimateLargeOne.mono {γ γ' : ℝ} (hγγ' : γ ≤ γ')
    (h : KatzTaoEstimateLargeOne.{u} E γ) : KatzTaoEstimateLargeOne.{u} E γ' := by
  intro ε hε
  obtain ⟨η, hη, hh⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hh] with δ hh_δ
  intro ι s T hball hKT hfull hcard
  by_cases hcard0 : s.card = 0
  · have hs : s = ∅ := Finset.card_eq_zero.mp hcard0
    subst hs; simp
  refine (hh_δ s T hball hKT hfull hcard).trans ?_
  have hone : (1 : ENNReal) ≤ (s.card : ENNReal) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcard0
  gcongr

/-- GWZ Definition 3.4 implies its large-family restriction — drop the clause.  This is the
fidelity tripwire for the token-copy: if `Kakeya.KatzTaoEstimate` or
`Kakeya.ML2Cap.KatzTaoEstimateLargeOne` drifts apart from it, this one-liner stops compiling. -/
theorem largeOne_of_katzTaoEstimate {γ : ℝ} (h : KatzTaoEstimate.{u} E γ) :
    KatzTaoEstimateLargeOne.{u} E γ := by
  intro ε hε
  obtain ⟨η, hη, hh⟩ := h ε hε
  exact ⟨η, hη, hh.mono fun δ hδ ι s T hball hKT hfull _ => hδ s T hball hKT hfull⟩

end Basic

/-! ## `L` is stronger than the compiled `δ^{-2}` clause -/

/-- The `δ^{-1}` threshold is weaker as a hypothesis than the `δ^{-2}` one, so `L(γ)` implies
`Kakeya.KKTResidual.KatzTaoEstimateStrict γ`.  (Not conversely: on the band
`δ^{-1} ≤ |𝕋| < δ^{-2}` the strict estimate says nothing.) -/
theorem strict_of_largeOne {γ : ℝ}
    (h : KatzTaoEstimateLargeOne.{u} (EuclideanSpace ℝ (Fin 3)) γ) :
    KKTResidual.KatzTaoEstimateStrict.{u} (EuclideanSpace ℝ (Fin 3)) γ := by
  intro ε hε
  obtain ⟨η, hη, hh⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hh, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδ hmem
  obtain ⟨hδ0, hδ1⟩ := hmem
  intro ι s T hball hKT hfull hcard
  refine hδ s T hball hKT hfull ?_
  have h1 : (δ : ℝ) ^ (-1 : ℝ) ≤ (δ : ℝ) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ0) (by exact_mod_cast hδ1.le)
      (by norm_num)
  rw [Real.rpow_neg_one] at h1
  exact h1.trans hcard

/-! ## Branch (i) of the reduction, with `SmallCard` deleted -/

/-- **The dichotomy closes the large-family half of Main Lemma 2, with no `SmallCard`.**

The body of `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` minus its `hsmall` hypothesis.
The two `ε`-free budgets are unchanged:

* `2c ≤ β` — alternative (i), `ε₀ = β/2 ≤ ε + θ₀(β - c)` at the threshold exponent `θ₀ = 1` of
  `Kakeya.ML2Assembly.Dichotomy`, for **every** `ε > 0`;
* `4c ≤ g` — alternative (ii), `4c ≤ g + ε`, the `4` being the exponent of
  `Kakeya.ML2Assembly.card_le_rpow_neg_four`.

The small-cardinality case never arises, because the cardinality binder of
`Kakeya.ML2Cap.KatzTaoEstimateLargeOne` is exactly the one `Kakeya.ML2Assembly.Dichotomy`
demands: the `rcases lt_or_ge (s.card : ℝ) ((δ : ℝ)⁻¹)` of the tree's version, and with it the
`min η ηs`, both disappear. -/
theorem largeOne_of_dichotomy {β g η c : ℝ}
    (hc : 0 < c) (hcβ : 2 * c ≤ β) (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g)
    (hdich : ML2Assembly.Dichotomy.{u} β (β / 2) g η) :
    KatzTaoEstimateLargeOne.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) := by
  intro ε hε
  refine ⟨η, hη0, ?_⟩
  filter_upwards [hdich, ML2Assembly.eventually_card_thresholds] with δ hδdich hδthr
  obtain ⟨hδ0, hδ1, hδC⟩ := hδthr
  intro ι s T hball hKT hfull hge
  rcases hδdich s T hball hKT hfull hge with hmass | hmass
  · -- alternative (i): the absolute-accuracy bound, paid for by `|𝕋| ≥ δ⁻¹`
    exact Kakeya.MainLemma2.Reduction.katzTaoGoal_of_absoluteLoss_of_card_ge hδ0 hδ1
      (V := fun i ↦ (T i).toShadedBody) (ε := ε) (ε₀ := β / 2) (γ := β - c)
      (by linarith) (by linarith) hge hmass
  · -- alternative (ii): the `δ`-gain, converted by the crude cardinality bound
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0]
      simp
    have hcardle : (s.card : ℝ) ≤ (δ : ℝ) ^ (-4 : ℝ) :=
      ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s T hball hη1 hKT
    have hcoef : (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β
        ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ (β - c) :=
      Kakeya.ML2Reduction.le_rpow_mul_rpow_of_gain (β := β) (K := 4) hδ0 hδ1 hpos hc.le
        (by linarith) hcardle le_rfl
    calc ∑ i ∈ s, volume (T i).shade
        ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade) := hmass
      _ ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ (β - c)
            * volume (⋃ i ∈ s, (T i).shade) := by gcongr

/-! ## The re-export that closes the loop -/

/-- **Re-export.**  `Kakeya.ML2Assembly.SmallCard γ` is `K_KT(γ)` with the band hypothesis thrown
away (`Kakeya.ML2Band.smallCard_of_katzTaoEstimate`).  It is stated here so that the Cap-Lemma
chain `L(β - c) → K_KT(β - c) → SmallCard (β - c)` is available under one prefix; by
`Kakeya.ML2Squeeze.smallCard_iff_katzTaoEstimate` the converse holds too, which is precisely why
the band is not a fragment and has to be reached from `L`. -/
theorem smallCard_of_katzTaoEstimate {γ : ℝ}
    (h : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ) : ML2Assembly.SmallCard.{u} γ :=
  Kakeya.ML2Band.smallCard_of_katzTaoEstimate h

/-- **The shape of the Cap Lemma, as an implication scheme.**  What steps A2--A6 have to
supply is `KatzTaoEstimateLargeOne → KatzTaoEstimate` at the same exponent; composed with
`Kakeya.ML2Cap.largeOne_of_dichotomy` and `Kakeya.ML2Cap.smallCard_of_katzTaoEstimate` it
discharges `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy`'s `hsmall` from the dichotomy
alone. -/
theorem katzTaoEstimate_sub_of_dichotomy_of_capLemma {β g η c : ℝ}
    (hcap : KatzTaoEstimateLargeOne.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - c))
    (hc : 0 < c) (hcβ : 2 * c ≤ β) (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g)
    (hdich : ML2Assembly.Dichotomy.{u} β (β / 2) g η) :
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) :=
  hcap (largeOne_of_dichotomy hc hcβ hη0 hη1 hg hdich)

end Kakeya.ML2Cap
