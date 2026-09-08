/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.Envelope
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParams
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCardLower
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEveryScale
public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyCase

/-!
# `GWZ Lemma 9.1 ⟹ GWZ Main Lemma 2` — the assembly

  `Kakeya.multiplicity_le_of_card_isEssDistinct_ge`  ⟹
  `Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate`.

Both endpoints are protected declarations and neither is touched: the hypothesis
`Kakeya.ML2Assembly.Lemma91` is pinned to the first by the compiling `example` just below its
definition, and the conclusion of
`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_frostmanEstimate_of_lemma91` is the second verbatim.

## What is proved here

* `Kakeya.ML2Assembly.lemma91_of_lemma91Uniform` — the `β`-uniform companion of Lemma 9.1 implies
  Lemma 9.1, so it is a genuine strengthening rather than a sideways move;
* `Kakeya.ML2Assembly.exists_lemma91Params` — Skolemisation of the uniform companion into the
  window exponent `ϖ` and the two exponent functions `gain = ν(β,·)`, `dens = η(β,·)` that
  `Kakeya.ML2Spine.IsSpine` is stated against;
* `Kakeya.ML2Assembly.card_le_rpow_neg_four` — the crude cardinality bound `|𝕋| ≤ δ^{-4}`;
* `Kakeya.ML2Assembly.isSpine_mono_beta` — a spine built at `β₀` is a spine at every `β ≥ β₀`,
  which is what makes one drop serve the whole window `[β₀,1]`;
* `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` — the dichotomy at one exponent, plus the
  small-cardinality case, gives `K_KT(β - c)` **for every accuracy `ε > 0`** from two `ε`-free
  budgets `2c ≤ β` and `4c ≤ g`;
* `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_frostmanEstimate_of_lemma91` — the assembly.

## What is left open, and where

Two hypotheses, both named and both genuinely mathematical:

* `Kakeya.ML2Assembly.GeometricCore` — GWZ Lemma 7.7(B) followed by Theorem 7.3(B) (alternative
  (i)) or by the two-scale split, the rescaling and the eccentric/non-eccentric analysis
  (alternative (ii)). * the small-cardinality case `Kakeya.ML2Assembly.SmallCard` — the complement of Prof. Hong Wang's
  standing assumption `|𝕋| > δ^{-1}`, which the hypotheses of `Kakeya.KatzTaoEstimate` do not
  supply.

and one strengthening of the input, `Kakeya.ML2Assembly.Lemma91Uniform`, forced by the
`MonotoneOn ν` clause of the protected Main Lemma 2 statement.

## The `ν`-before-`ε` discipline

Following Prof. Hong Wang's clarification of 2026-08-30, the drop is
`Kakeya.ML2Spine.spineNu β₀ ϖ ε₁ gain dens`, which has **no `ε` argument**, and Theorem 7.3(B) is
read at the absolute accuracy `Kakeya.ML2Spine.absAccuracy β = β/2`.  Neither `Dichotomy` nor
`GeometricCore` has an `ε` binder.  `Kakeya.ML2Spine.not_epsFree_of_outerAccuracy` proves that
reading 7.3(B) at the outer `ε` instead makes an `ε`-free drop impossible.
-/

@[expose] public section

open MeasureTheory Topology Filter ShadedBody ConvexSpaceBody

namespace Kakeya.ML2Assembly

universe u

/-- The body of GWZ Lemma 9.1 at exponent `β`, window exponent `ϖ`, tolerance `ζ`, gain `ν` and
density exponent `η` — copied verbatim from the protected
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`. -/
def VNSBody (β ϖ ζ ν η : ℝ) : Prop :=
  KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
  FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
  ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
    (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
    (∀ i ∈ s, (T i).toTube.IsCentred) →
    (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
    maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
    ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
    (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - ϖ)) (δ ^ ϖ) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ).Pairwise
          (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
    multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      (δ : ENNReal) ^ ν * (s.card : ENNReal) ^ β

/-- **GWZ Lemma 9.1**, exactly as the protected declaration states it. -/
def Lemma91 : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 1 →
    ∃ ϖ > (0 : ℝ), ∀ ζ > (0 : ℝ), ∃ ν > (0 : ℝ), ∃ η > (0 : ℝ), VNSBody.{u} β ϖ ζ ν η

/- The fidelity compatibility `example : Lemma91 := fun _ hβ hβ1 ↦ Kakeya.multiplicity_le_of_card_isEssDistinct_ge hβ hβ1`
lives in `MainLemma2/VeryNotStickyClosed.lean` since the  A.5 relocation of Lemma 9.1 downstream of
its producers; this module is upstream of that file. -/

/-! ## The `β`-uniform companion of Lemma 9.1 -/

/-- **The `β`-uniform companion of GWZ Lemma 9.1.**

Same body as `Kakeya.ML2Assembly.Lemma91`, but with the three exponents `ϖ`, `ν(ζ)`, `η(ζ)`
chosen *before* `β` ranges over the compact window `[β₀, 1]`.

Why the assembly needs this and the bare `Lemma91` does not suffice.  The protected Main Lemma 2
asks for a **monotone** `ν : ℝ → ℝ`, and `Kakeya.ML2Reduction.katzTaoDropSet` reduces that
demand — with no loss — to: for every `β₀ ∈ (0,1]` there is a single drop `c > 0` valid for every
`β ∈ [β₀,1]`.  The only transfer available between exponents is *downwards*
(`KatzTaoEstimate.mono` and `FrostmanEstimate.mono` turn the data at `β` into the data at any
`b ≥ β`), so a drop `d` established at `b` serves at `β ≤ b` only with the loss `d - (b - β)`.
The induced cover of `[β₀,1]` is therefore by **left** neighbourhoods `[b - c b, b]`, and such
covers admit no finite subpartition: for `c b = b - β₀` every transfer to `β` yields exactly
`β - β₀`, which tends to `0`.  So per-`β` drops never assemble into a uniform one by pure
analysis, and the uniformity has to come from the proof of Lemma 9.1 itself. -/
def Lemma91Uniform : Prop :=
  ∀ β₀ : ℝ, 0 < β₀ → β₀ ≤ 1 →
    ∃ ϖ > (0 : ℝ), ∀ ζ > (0 : ℝ), ∃ ν > (0 : ℝ), ∃ η > (0 : ℝ),
      ∀ β ∈ Set.Icc β₀ 1, VNSBody.{u} β ϖ ζ ν η

/-- The uniform companion is a genuine **strengthening** of Lemma 9.1: it implies it.  (The
converse fails; see the docstring of `Kakeya.ML2Assembly.Lemma91Uniform`.)  This is the check
that the hypothesis of the assembly is not incomparable to, or weaker than, the protected
statement. -/
theorem lemma91_of_lemma91Uniform (h : Lemma91Uniform.{u}) : Lemma91.{u} := by
  intro β hβ hβ1
  obtain ⟨ϖ, hϖ, hζ⟩ := h β hβ hβ1
  refine ⟨ϖ, hϖ, fun ζ hζ' ↦ ?_⟩
  obtain ⟨ν, hν, η, hη, hbody⟩ := hζ ζ hζ'
  exact ⟨ν, hν, η, hη, hbody β ⟨le_rfl, hβ1⟩⟩

/-! ## How `VNSBody` may be weakened -/

/-- **The gain of Lemma 9.1's body may be shrunk.**  `δ ≤ 1` eventually, so `δ^ν ≤ δ^{ν'}` for
`ν' ≤ ν` and the conclusion only weakens.  (The `∀ᶠ δ in 𝓝[>] 0` prefix supplies `δ ≤ 1`; this is
why the shrink is stated on `VNSBody` and **not** on `Kakeya.ML2Reduction.Lemma91At`, which has no
`δ ≤ 1` binder.)

This is the `Kakeya.ML2Assembly` twin of `Kakeya.VNSUniform.VNSBody.mono_gain`: the two `VNSBody`s
are the same `Prop`-valued function, but their files sit on separate branches of the import graph,
so neither can cite the other's copy. -/
theorem VNSBody.mono_gain {β ϖ ζ ν ν' η : ℝ} (hνν' : ν' ≤ ν) (h : VNSBody.{u} β ϖ ζ ν η) :
    VNSBody.{u} β ϖ ζ ν' η := by
  intro hKT hF
  filter_upwards [h hKT hF, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with δ hδ hδ1
  intro ι s T hball hcen huni hmax hfull hcount
  refine (hδ s T hball hcen huni hmax hfull hcount).trans ?_
  have hδ1' : (δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr hδ1.2.le
  exact mul_le_mul_of_nonneg_right
    (ENNReal.rpow_le_rpow_of_exponent_ge hδ1' hνν') zero_le

/-- The parameter package that the assembly extracts from `Kakeya.ML2Assembly.Lemma91Uniform` at
the threshold `β₀`: the window exponent `ϖ` and the two exponent *functions* `gain = ν(β,·)` and
`dens = η(β,·)` that `Kakeya.ML2Spine.IsSpine` is stated against. -/
structure Lemma91Params (β₀ ϖ : ℝ) (gain dens : ℝ → ℝ) : Prop where
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
  /-- At every tolerance and every exponent in `[β₀,1]`, the body of Lemma 9.1 holds with these
  three exponents. -/
  body : ∀ ζ : ℝ, 0 < ζ → ∀ β ∈ Set.Icc β₀ 1, VNSBody.{u} β ϖ ζ (gain ζ) (dens ζ)

/-- **The parameters of Lemma 9.1, packaged as functions.**  Skolemisation of
`Kakeya.ML2Assembly.Lemma91Uniform` at a fixed threshold `β₀`. -/
theorem exists_lemma91Params (h : Lemma91Uniform.{u}) {β₀ : ℝ} (hβ₀ : 0 < β₀) (hβ₀1 : β₀ ≤ 1) :
    ∃ (ϖ : ℝ) (gain dens : ℝ → ℝ), Lemma91Params.{u} β₀ ϖ gain dens := by
  classical
  obtain ⟨ϖ, hϖ, hζ⟩ := h β₀ hβ₀ hβ₀1
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
    intro β hβ
    exact VNSBody.mono_gain (min_le_left _ _)
      ((((hζ ζ hz).choose_spec.2).choose_spec.2) β hβ)

/-! ## The crude cardinality bound -/

/-- **`|𝕋| ≤ δ^{-4}` for any Katz--Tao family of `δ`-tubes in `B₁`.**

The blueprint's `⪅` hides this: `∑_i |T_i| ≤ Δ_max(𝕋)·|B₁|` and every `δ`-tube in `ℝ³` has
volume `≳ δ²`, so `|𝕋| ≲ Δ_max(𝕋)·δ^{-2}`.  With `Δ_max(𝕋) ≤ δ^{-η}`, `η ≤ 1` and `δ` small
enough that the dimensional constant of `Kakeya.Tube.card_le_of_densityIn_le` is below `δ^{-1}`,
the bound is `δ^{-4}`.

This is the *upper* cardinality bound that converts the `δ`-gain of the window branch into a drop
in the exponent of `|𝕋|`; it is the `hcard` hypothesis of
`Kakeya.ML2Reduction.le_rpow_mul_rpow_of_gain`.  It is not to be confused with the *lower* bound
`δ⁻¹ ≤ |𝕋|` of Prof. Wang's clarification, which is spent in the other branch and is genuinely
open. -/
theorem card_le_rpow_neg_four {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδC : (Tube.card_le_of_densityIn_le.C 3 : ENNReal) ≤ (δ : ENNReal) ^ (-1 : ℝ))
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    {η : ℝ} (hη1 : η ≤ 1)
    (hmax : maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η)) :
    (s.card : ℝ) ≤ (δ : ℝ) ^ (-4 : ℝ) := by
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
    simp
  have hδE0 : (0 : ENNReal) < (δ : ENNReal) := by exact_mod_cast hδ0
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  -- the raw bound of `Tube.card_le_of_densityIn_le`
  have hden : densityIn s (fun i ↦ (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall ≤ (δ : ENNReal) ^ (-η) :=
    (le_maxDensity s _ _).trans hmax
  have hraw := Tube.card_le_of_densityIn_le (E := EuclideanSpace ℝ (Fin 3)) (δ := δ)
    (s := s) (T := fun i ↦ (T i).toTube) hδ0.ne' hball hden
  rw [hE] at hraw
  norm_num at hraw
  -- `δ ^ (-η) ≤ δ ^ (-1)`
  have hstep1 : (δ : ENNReal) ^ (-η) ≤ (δ : ENNReal) ^ (-1 : ℝ) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
  have hzpow : (δ : ENNReal) ^ (-2 : ℤ) = (δ : ENNReal) ^ (-2 : ℝ) := by
    rw [← ENNReal.rpow_intCast]
    norm_num
  have hkey : (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-4 : ℝ) := by
    refine hraw.trans ?_
    rw [hzpow]
    calc (Tube.card_le_of_densityIn_le.C 3 : ENNReal) * (δ : ENNReal) ^ (-η)
            * (δ : ENNReal) ^ (-2 : ℝ)
        ≤ (δ : ENNReal) ^ (-1 : ℝ) * (δ : ENNReal) ^ (-1 : ℝ) * (δ : ENNReal) ^ (-2 : ℝ) := by
          gcongr
      _ = (δ : ENNReal) ^ (-4 : ℝ) := by
          rw [← ENNReal.rpow_add _ _ hδE0.ne' ENNReal.coe_ne_top,
            ← ENNReal.rpow_add _ _ hδE0.ne' ENNReal.coe_ne_top]
          norm_num
  -- transfer to `ℝ`
  rw [← ENNReal.coe_rpow_of_ne_zero hδ0.ne',
    show ((s.card : ENNReal)) = ((s.card : NNReal) : ENNReal) by simp,
    ENNReal.coe_le_coe, ← NNReal.coe_le_coe] at hkey
  simpa [NNReal.coe_rpow] using hkey

/-- The thresholds under which `Kakeya.ML2Assembly.card_le_rpow_neg_four` applies hold for all
small `δ`. -/
theorem eventually_card_thresholds :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      0 < δ ∧ δ ≤ 1 ∧
        (Tube.card_le_of_densityIn_le.C 3 : ENNReal) ≤ (δ : ENNReal) ^ (-1 : ℝ) := by
  set C : NNReal := Tube.card_le_of_densityIn_le.C 3 with hC
  have hpos : (0 : NNReal) < (C + 1)⁻¹ := by positivity
  have hmem : Set.Ioo (0 : NNReal) (min 1 (C + 1)⁻¹) ∈ 𝓝[>] (0 : NNReal) :=
    Ioo_mem_nhdsGT (lt_min zero_lt_one hpos)
  filter_upwards [hmem] with δ hδ
  obtain ⟨hδ0, hδlt⟩ := hδ
  have hδ1 : δ ≤ 1 := (lt_of_lt_of_le hδlt (min_le_left _ _)).le
  refine ⟨hδ0, hδ1, ?_⟩
  have hδinv : δ ≤ (C + 1)⁻¹ := (lt_of_lt_of_le hδlt (min_le_right _ _)).le
  have hCδ : C * δ ≤ 1 := by
    have h1 : (C + 1) * δ ≤ (C + 1) * (C + 1)⁻¹ := by
      gcongr
    rw [mul_inv_cancel₀ (by positivity)] at h1
    exact le_trans (by gcongr; exact le_self_add) h1
  have hCle : (C : ENNReal) ≤ (δ : ENNReal)⁻¹ := by
    rw [ENNReal.le_inv_iff_mul_le]
    calc (C : ENNReal) * (δ : ENNReal) = ((C * δ : NNReal) : ENNReal) := by
          rw [ENNReal.coe_mul]
      _ ≤ ((1 : NNReal) : ENNReal) := by exact_mod_cast hCδ
      _ = 1 := by simp
  calc (C : ENNReal) ≤ (δ : ENNReal)⁻¹ := hCle
    _ = (δ : ENNReal) ^ (-1 : ℝ) := by
        rw [ENNReal.rpow_neg, ENNReal.rpow_one]

/-! ## The dichotomy at one exponent, and the two ways it closes -/

/-- **The GWZ Lemma 7.7(B) dichotomy at exponent `β`, in the form the reduction consumes.**

For every sufficiently small `δ` and every family `(𝕋, Y) = (s, T)` of shaded `δ`-tubes in `B₁`
that is `δ^{-η}` Katz--Tao and has fullness at least `δ^η`, one of the two alternatives of the
blueprint proof of Main Lemma 2 holds:

* **alternative (i), the every-scale branch.**  Conclusion (i) of `dividingScalesLemmaB` makes
  `𝕋` Katz--Tao at every scale, and Theorem 7.3(B) — read, per Prof. Hong Wang's clarification of
  2026-08-30, at the **absolute** accuracy `ε₀ = Kakeya.ML2Spine.absAccuracy β = β/2` and *not* at
  the outer `ε` — gives `μ(𝕋,Y) ≤ δ^{-ε₀}`.  The branch also has to deliver `δ⁻¹ ≤ |𝕋|`: that is
  the `|𝕋| > δ^{-1}` of the clarification, and this is the one and only place in the reduction
  where it is spent (`Kakeya.ML2Reduction.le_rpow_mul_rpow_of_card_ge`), because `δ^{-β/2}` can be
  paid for only by `|𝕋|^{β-ν} ≥ δ^{-(β-ν)}`.  That the trivial bound cannot substitute is
  `Kakeya.MainLemma2.Reduction.trivialBranch_cost_sharp`.  Here `|𝕋| > δ^{-1}` is a *hypothesis*
  of the dichotomy, exactly as it is a standing assumption of the blueprint proof; the complementary
  case is `Kakeya.ML2Assembly.SmallCard`.  Without it the dichotomy is outright **false**: a single
  fully shaded `δ`-tube has `Δ_max = 1 ≤ δ^{-η}`, `λ = 1 ≥ δ^η` and `μ = 1`, which satisfies
  neither `μ ≤ δ^{-β/2}` nor `μ ≤ δ^g·1^β`.

* **alternative (ii), the window branch.**  Conclusion (ii) of `dividingScalesLemmaB`, followed by
  the two-scale split, the rescaling and the eccentric/non-eccentric case analysis, gives a
  genuine positive `δ`-gain `μ(𝕋,Y) ≤ δ^{g}|𝕋|^{β}` with `g = g(β) > 0` independent of `ε`.

Both alternatives are stated in **mass form** (`∑ |Y_i| ≤ … · |⋃ Y_i|`) rather than through
`ShadedBody.multiplicity`, because that is the form of the conclusion of `Kakeya.KatzTaoEstimate`;
`ShadedBody.multiplicity_le_iff` converts.

Neither `η` nor `g` may depend on the outer accuracy `ε`.  That is exactly the content of
`Kakeya.ML2Spine.exists_ml2SpineParams` and of its converse
`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy`, and it is why `Dichotomy` has no `ε` binder. -/
def Dichotomy (β ε₀ g η : ℝ) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
      (∑ i ∈ s, volume (T i).shade
            ≤ (δ : ENNReal) ^ (-ε₀) * volume (⋃ i ∈ s, (T i).shade))
        ∨ (∑ i ∈ s, volume (T i).shade
            ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade))

/-- **The small-cardinality case, `|𝕋| < δ^{-1}`.**

`Kakeya.ML2Assembly.Dichotomy` is stated under Prof. Hong Wang's standing assumption
`|𝕋| > δ^{-1}`, which the blueprint proof of Main Lemma 2 makes silently and which the hypotheses
of `Kakeya.KatzTaoEstimate` do **not** supply.  This predicate is the complementary case.

It is not a restatement of the goal in disguise.  Two things are known about it:

* the sub-band `|𝕋| ≤ δ^{-η}` is already discharged, by
  `Kakeya.MainLemma2.Reduction.katzTaoGoal_of_card_le_rpow` at `θ = η`, whose cost condition
  `η(1-γ) ≤ ε` is met by choosing `η` after `ε`.  So the genuinely open band is
  `δ^{-η} < |𝕋| < δ^{-1}`;
* on that band no ε-free argument from `K_KT(β)` alone can work:
  `Kakeya.MainLemma2.Reduction.trivialBranch_cost_sharp` shows the trivial bound `μ ≤ |𝕋|` costs
  exactly `δ^{-(1-γ)}`, and `K_KT(β)` at accuracy `ε'` costs `ε' + c`, i.e. an `ε`-dependent drop.
  This is Prof. Wang's remark: in the bilinear case `|𝕋| > δ^{-1}` is automatic, and otherwise
  broad--narrow supplies the improvement. -/
def SmallCard (γ : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), η ≤ 1 ∧
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (s.card : ℝ) < (δ : ℝ)⁻¹ →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (T i).shade)

/-! ### Weakening the two hypotheses of `Kakeya.KatzTaoEstimate` in the exponent `η` -/

/-- A `δ^{-η}` Katz--Tao family is `δ^{-η'}` Katz--Tao for every `η' ≥ η`. -/
theorem isKatzTao_of_exponent_le {δ : NNReal} (hδ1 : δ ≤ 1) {ι : Type*} {s : Finset ι}
    {W : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {η η' : ℝ} (h : η ≤ η')
    (hKT : IsKatzTao s W ((δ : ENNReal) ^ (-η))) :
    IsKatzTao s W ((δ : ENNReal) ^ (-η')) := by
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  exact le_trans hKT (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith))

/-- Fullness at least `δ^η` is fullness at least `δ^{η'}` for every `η' ≥ η`. -/
theorem le_of_rpow_exponent_le {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {η η' : ℝ} (h : η ≤ η')
    {x : NNReal} (hx : x ≥ δ ^ η) : x ≥ δ ^ η' :=
  le_trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 h) hx

/-- **The dichotomy closes Main Lemma 2 at one exponent.**

Given the dichotomy at `β` with absolute accuracy `ε₀ = β/2`, gain `g`, and a drop `c` obeying the
two `ε`-free budgets

* `2c ≤ β`   (alternative (i): `ε₀ = β/2 ≤ ε + (β - c)` for **every** `ε > 0`), and
* `4c ≤ g`   (alternative (ii): `K·c ≤ g + ε` for **every** `ε > 0`, with `K = 4` the exponent of
  the crude cardinality bound `Kakeya.ML2Assembly.card_le_rpow_neg_four`),

the improved partial estimate `K_KT(β - c)` holds.

The two budgets are the whole reason the drop can be chosen before the accuracy.  `2c ≤ β` is
`Kakeya.ML2Spine.two_spineNu_le`; `4c ≤ g` is what the window branch has to deliver. -/
theorem katzTaoEstimate_sub_of_dichotomy {β g η c : ℝ}
    (hc : 0 < c) (hcβ : 2 * c ≤ β) (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g)
    (hdich : Dichotomy.{u} β (β / 2) g η) (hsmall : SmallCard.{u} (β - c)) :
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) := by
  intro ε hε
  obtain ⟨ηs, hηs0, hηs1, hsm⟩ := hsmall ε hε
  refine ⟨min η ηs, lt_min hη0 hηs0, ?_⟩
  filter_upwards [hdich, hsm, eventually_card_thresholds] with δ hδdich hδsm hδthr
  obtain ⟨hδ0, hδ1, hδC⟩ := hδthr
  intro ι s T hball hKT hfull
  -- weaken the two hypotheses from `min η ηs` to each of `η` and `ηs`
  have hKTη : IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) :=
    isKatzTao_of_exponent_le hδ1 (min_le_left _ _) hKT
  have hKTηs : IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-ηs)) :=
    isKatzTao_of_exponent_le hδ1 (min_le_right _ _) hKT
  have hfullη : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η :=
    le_of_rpow_exponent_le hδ0 hδ1 (min_le_left _ _) hfull
  have hfullηs : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ ηs :=
    le_of_rpow_exponent_le hδ0 hδ1 (min_le_right _ _) hfull
  rcases lt_or_ge (s.card : ℝ) ((δ : ℝ)⁻¹) with hlt | hge
  · -- the small-cardinality case, `|𝕋| < δ⁻¹`
    exact hδsm s T hball hKTηs hfullηs hlt
  rcases hδdich s T hball hKTη hfullη hge with hmass | hmass
  · -- alternative (i): the absolute-accuracy bound, paid for by `|𝕋| ≥ δ⁻¹`
    exact Kakeya.MainLemma2.Reduction.katzTaoGoal_of_absoluteLoss_of_card_ge hδ0 hδ1
      (V := fun i ↦ (T i).toShadedBody) (ε := ε) (ε₀ := β / 2) (γ := β - c)
      (by linarith) (by linarith) hge hmass
  · -- alternative (ii): the `δ`-gain, converted by the crude cardinality bound
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0]
      simp
    have hcardle : (s.card : ℝ) ≤ (δ : ℝ) ^ (-4 : ℝ) :=
      card_le_rpow_neg_four hδ0 hδ1 hδC s T hball hη1 hKTη
    have hcoef : (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β
        ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ (β - c) :=
      Kakeya.ML2Reduction.le_rpow_mul_rpow_of_gain (β := β) (K := 4) hδ0 hδ1 hpos hc.le
        (by linarith) hcardle le_rfl
    calc ∑ i ∈ s, volume (T i).shade
        ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade) := hmass
      _ ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ (β - c)
            * volume (⋃ i ∈ s, (T i).shade) := by gcongr

/-! ## The spine at the threshold serves the whole window -/

/-- **`IsSpine` is monotone in `β`.**

Only two fields of `Kakeya.ML2Spine.IsSpine` mention `β`, namely `sep_le` and `gain_budget`, and
both contain `β` only through the eccentricity threshold `12 η_k/(e β)`, which *decreases* as `β`
grows.  So a spine built at the threshold `β₀` is a spine at every `β ∈ [β₀, 1]`.

This is what makes the drop `Kakeya.ML2Spine.spineNu β₀ ϖ ε₁ gain dens` — a function of `β₀` and
of Lemma 9.1's `β`-uniform data only — legitimate for the whole window `[β₀,1]`, which is what
`Kakeya.ML2Reduction.katzTaoDropSet` demands.  Together with
`Kakeya.ML2Assembly.Lemma91Uniform` it is the entire content of the `β`-uniformity step. -/
theorem isSpine_mono_beta {β₀ β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (h : ML2Spine.IsSpine β₀ ϖ ε₁ gain dens ε₂ e N η) (hβ₀ : 0 < β₀) (hle : β₀ ≤ β) :
    ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η := by
  have he : 0 < e := h.div_pos
  have hβ : 0 < β := lt_of_lt_of_le hβ₀ hle
  have hkey : ∀ k : ℕ, 12 * η k / (e * β) ≤ 12 * η k / (e * β₀) := by
    intro k
    have hηk : 0 < η k := h.rung_pos k
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by nlinarith)
  refine { h with sep_le := ?_, gain_budget := ?_ }
  · intro k hk
    exact (hkey k).trans (h.sep_le k hk)
  · intro k hk
    have h1 := hkey k
    have h2 := h.gain_budget k hk
    linarith

/-! ## The open geometric core, and the assembly -/

/-- **The open geometric core of the GWZ reduction.**

Everything the proof of Main Lemma 2 needs beyond the bookkeeping proved in this file.

Given `β₀ ∈ (0,1]` and the `β`-uniform parameters `(ϖ, gain, dens)` of Lemma 9.1 at threshold `β₀`
(`Kakeya.ML2Assembly.Lemma91Params`), produce

* the Katz--Tao exponent `ε₁ > 0` of Theorem 7.3(B) at the **absolute** accuracy
  `Kakeya.ML2Spine.absAccuracy β = β/2` — this is the `ε₁` argument of
  `Kakeya.ML2Spine.IsSpine`, and `Kakeya.ML2Spine.spineRung_isSpine` then builds the whole ladder
  `ε₂, N, e, (η_k)` from `(ϖ, ε₁, gain, dens)` with **no dependence on the outer `ε`**;
* and, at every exponent `β` of the window `[β₀,1]` for which `K_KT(β)` and `K_F(β)` hold, the
  dichotomy `Kakeya.ML2Assembly.Dichotomy` at absolute accuracy `β/2` and gain
  `4 · Kakeya.ML2Spine.spineNu β₀ ϖ ε₁ gain dens`.

The factor `4` is the exponent of the crude cardinality bound
`Kakeya.ML2Assembly.card_le_rpow_neg_four`; the blueprint's own budget for the window branch is
`ν(β,η_j/2) - 2η'_{j-1} ≥ 10 η_{j-1}/ε₂`, i.e. `Kakeya.ML2Spine.IsSpine.gain_budget`, which is
strictly stronger than what is asked here.

`Kakeya.ML2Assembly.isSpine_mono_beta` is what makes the `β`-uniform reading legitimate: the
single ladder built at `β₀` is a legal `IsSpine β …` for every `β ∈ [β₀,1]`.

**How to supply the single `ε₁` for the whole window.**  `ε₁` is bound before `β`, while
`Kakeya.ML2Reduction.exists_everyScale_exponent` returns the accuracy-to-exponent map `Eexp` of
Theorem 7.3(B) and `Eexp (absAccuracy β) = Eexp (β/2)` varies with `β`.  Read 7.3(B) at the
**threshold** accuracy `β₀/2` instead and take `ε₁ = Eexp (β₀/2)`: the resulting every-scale bound
`μ(𝕋,Y) ≤ δ^{-β₀/2}` is *stronger* than the `μ(𝕋,Y) ≤ δ^{-β/2}` this `Dichotomy` asks for, since
`β₀ ≤ β` and `δ ≤ 1`.  No monotonicity of `Eexp` is needed.

**The `4096 ≤ N` side condition lives inside this hypothesis, not in its statement.**
`StickyKakeya.dividingScalesKatzTao` (GWZ Lemma 7.7(B)) requires `4096 ≤ N`, which
`Kakeya.ML2Spine.IsSpine` does not currently imply; see
`Kakeya.ML2Reduction.four_thousand_le_of_div_eq`.  Nothing in `GeometricCore` mentions `N`, so
the repair of `Kakeya.ML2Spine.spineEps₂` does not touch this interface. -/
def GeometricCore : Prop :=
  ∀ (β₀ ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β₀ → β₀ ≤ 1 → Lemma91Params.{u} β₀ ϖ gain dens →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ β ∈ Set.Icc β₀ 1,
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
          Dichotomy.{u} β (β / 2) (4 * ML2Spine.spineNu β₀ ϖ ε₁ gain dens) η

/-- **GWZ Lemma 9.1 ⟹ GWZ Main Lemma 2.**

The conclusion is, verbatim, the statement of the protected
`Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate`.  The hypotheses are

* `h91`, the `β`-uniform companion of the protected
  `Kakeya.multiplicity_le_of_card_isEssDistinct_ge` — see
  `Kakeya.ML2Assembly.lemma91_of_lemma91Uniform` for the fact that it implies Lemma 9.1, and the
  docstring of `Kakeya.ML2Assembly.Lemma91Uniform` for why the bare Lemma 9.1 cannot replace it;
* `hcore`, the geometric chain of the blueprint proof (`Kakeya.ML2Assembly.GeometricCore`);
* `hsmall`, the small-cardinality case `Kakeya.ML2Assembly.SmallCard`, i.e. the complement of the
  standing assumption `|𝕋| > δ^{-1}` that the blueprint proof makes silently.

1. the `MonotoneOn ν` bookkeeping, via `Kakeya.ML2Reduction.katzTaoDropSet` and
   `Kakeya.ML2Reduction.katzTaoEstimate_sub_of_nonempty_katzTaoDropSet`;
2. the `β`-uniformity of the drop over the window `[β₀,1]`, via
   `Kakeya.ML2Assembly.isSpine_mono_beta` and `Kakeya.ML2Spine.spineNu`;
3. the discipline "`ν` before `ε`": the drop is
   `Kakeya.ML2Spine.spineNu β₀ ϖ ε₁ gain dens`, which has no `ε` argument, and Theorem 7.3(B) is
   read at `Kakeya.ML2Spine.absAccuracy β = β/2`
   (`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy` refutes the alternative);
4. both `ε`-free budgets, `2ν ≤ β` (`Kakeya.ML2Spine.two_spineNu_le`) and `4ν ≤ g`, and the two
   arithmetic conversions that close the two branches for **every** accuracy `ε > 0`
   (`Kakeya.ML2Reduction.le_rpow_mul_rpow_of_card_ge`,
   `Kakeya.ML2Reduction.le_rpow_mul_rpow_of_gain`,
   `Kakeya.MainLemma2.Reduction.katzTaoGoal_of_absoluteLoss_of_card_ge`);
5. the crude cardinality bound `|𝕋| ≤ δ^{-4}` that turns the `δ`-gain into a drop in the exponent
   of `|𝕋|` (`Kakeya.ML2Assembly.card_le_rpow_neg_four`). -/
theorem katzTaoEstimate_sub_of_frostmanEstimate_of_lemma91
    (h91 : Lemma91Uniform.{u}) (hcore : GeometricCore.{u})
    (hsmall : ∀ β : ℝ, 0 < β → β ≤ 1 →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ γ : ℝ, β / 2 ≤ γ → γ < β → SmallCard.{u} γ) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β) := by
  refine Kakeya.ML2Reduction.katzTaoEstimate_sub_of_nonempty_katzTaoDropSet.{u} ?_
  rintro β₀ ⟨hβ₀, hβ₀1⟩
  obtain ⟨ϖ, gain, dens, hparams⟩ := exists_lemma91Params h91 hβ₀ hβ₀1
  obtain ⟨ε₁, hε₁, hdich⟩ := hcore β₀ ϖ gain dens hβ₀ hβ₀1 hparams
  have hc : 0 < ML2Spine.spineNu β₀ ϖ ε₁ gain dens :=
    ML2Spine.spineNu_pos hβ₀ hparams.window_pos hε₁ hparams.gain_pos hparams.dens_pos
  have h2c : 2 * ML2Spine.spineNu β₀ ϖ ε₁ gain dens ≤ β₀ :=
    ML2Spine.two_spineNu_le hβ₀ hβ₀1 hparams.window_pos hε₁ hparams.gain_pos hparams.dens_pos
  refine ⟨ML2Spine.spineNu β₀ ϖ ε₁ gain dens, ⟨hc, by linarith⟩, ?_⟩
  rintro β hβmem hKT hKF
  obtain ⟨η, hη0, hη1, hd⟩ := hdich β hβmem hKT hKF
  exact katzTaoEstimate_sub_of_dichotomy hc (by linarith [hβmem.1]) hη0 hη1 le_rfl hd
    (hsmall β (by linarith [hβmem.1]) hβmem.2 hKT hKF _ (by linarith [hβmem.1]) (by linarith))

/-! ## Bridge to the every-scale branch of `Reduction/SpineEveryScale.lean` -/

/-- **The every-scale branch, converted into the first disjunct of
`Kakeya.ML2Assembly.Dichotomy`.**

`Kakeya.ML2Reduction.exists_everyScale_multiplicity_le` — GWZ Theorem 7.3(B) read at the absolute
accuracy `ε₀` — delivers `μ(𝕋,Y) ≤ ENNReal.ofReal (δ^{-ε₀})`, in *multiplicity* form and with the
power computed in `ℝ`.  `Dichotomy` asks for the same bound in *mass* form with the power computed
in `ENNReal`.  This is the conversion, and it is exactly `ShadedBody.multiplicity_le_iff` composed
with `Kakeya.ML2Reduction.ofReal_rpow_coe`.

Its purpose is to make the fit between the two interfaces compiler-checked rather than asserted:
instantiating the first disjunct of `Dichotomy` at `ε₀ = β/2` is now a one-line call. -/
theorem dichotomy_everyScale_branch {δ : NNReal} (hδ0 : 0 < δ) {ι : Type*} {s : Finset ι}
    (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) {ε₀ : ℝ}
    (h : ShadedBody.multiplicity s (fun i ↦ (V i).toShadedBody)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε₀))) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (δ : ENNReal) ^ (-ε₀) * volume (⋃ i ∈ s, (V i).shade) := by
  rw [← Kakeya.ML2Reduction.ofReal_rpow_coe hδ0]
  exact (ShadedBody.multiplicity_le_iff s (fun i ↦ (V i).toShadedBody)).mp h

end Kakeya.ML2Assembly
