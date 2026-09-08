/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.KatzTaoPlankEstimate
public import Kakeya.DimensionThree.MainLemma2.NonSlabSplit
public import Kakeya.DimensionThree.MainLemma2.Reduction.AccuracyCardExchange

/-!
# The residual propositions under a cardinality-restricted `K_KT`

**Question.**  Replace GWZ Definition 3.4 (`Kakeya.KatzTaoEstimate`) by the
restricted estimate `K_KT'(β)` — the same statement with the extra hypothesis `δ^{-2} ≤ |𝕋|`
(strict form) or `δ^{-2+η} ≤ |𝕋|` with the prover's `η` (slack form).  Do the propositions needed
at the two blocking application sites — GWZ Lemma 6.1's high branch (site A) and Lemma 9.1's
tangential fibres (site D) — still *follow* from `K_KT'(β)` together with everything in scope
there?  Truth cannot discriminate (every conclusion is a Kakeya-type estimate), so the test is
derivability.

**What this file establishes, all compiled and axiom-clean.**

* `KatzTaoEstimateStrict`, `KatzTaoEstimateSlack` are verbatim copies of Definition 3.4 with the
  respective clause; `KatzTaoEstimateSmall E β C` is Definition 3.4 restricted to families with
  `|𝕋| < δ^{-C}` ("small-family `K_KT`").  Trivially `K_KT → Slack → Strict` and `K_KT → Small C`;
  conversely `Strict ∧ Small 2 → K_KT` and `Slack ∧ Small 2 → K_KT` by the obvious case split
  (`katzTaoEstimate_iff_strict_and_small`, `katzTaoEstimate_iff_slack_and_small`).
* **In `ℝ³` the small-family estimate is not a fragment: `Small C ↔ K_KT` for every `C > 0`**
  (`small_iff_katzTaoEstimate`), by the tree's affine squeeze
  `Kakeya.ML2Squeeze.smallCardCut_iff_katzTaoEstimate`.  Consequently `Strict ∧ Small 2 ↔ K_KT`
  is true but `Strict` is redundant in it.
* **Site A.**  `ResidualA β` is the callback consumed by `Kakeya.KatzTaoEstimate.plankEstimate`
  (the threshold form of generalized Lemma 3.7, `Kakeya.exists_b0_multiplicity_bound`), stated
  exactly as it is quantified there: over *every* `(b/8)`-tube family in the unit ball, with a
  fullness hypothesis and **no** cardinality lower bound.  `ResidualA β ↔ K_KT β`
  (`residualA_iff_katzTaoEstimate`; the forward direction pads the family and takes `τ = δ`), hence
  `ResidualA β ↔ Small C` for every `C > 0` and `Strict → (ResidualA ↔ Small 2)`.  So at site A
  `K_KT' + everything in scope ⊢ ResidualA ⟺ small-family K_KT ⟺ K_KT`: the clause hands the
  whole estimate back as the residual.
* **Site D.**  `ResidualD cfg := cfg.KTScaleData cfg.ϱ`, the field `SplitInputs.katzTao` consumes
  (verbatim: `ktScaleData_iff`).  From `K_KT` it follows by the existing `ktScaleData_of_le` route,
  packaged with explicit thresholds (`ktScaleData_of_katzTaoEstimate`).  From the strict/slack
  clause it does **not**: the fibres `𝕋[T_{ρ₂}]` obey only the upper bound
  `Kakeya.VeryNotSticky.nonslabFibreCount`, and from that bound alone every clause
  `δ^{-2+θ} ≤ |𝕋[T_{ρ₂}]|` is *false* on the lower part of the window
  (`fibre_card_lt_rpow`, `strict_clause_false_at_fibre`, `capped_clause_false_at_fibre`).  What
  the split actually consumes is the fibre-restricted datum `FibreKTData`; it follows from
  `Small C` at the fibre exponent `C_D = 2 + η − exscal(2+ζ) + μ` (`fibreKTData_of_small`), and
  the whole-family datum from `Small (2 + η + μ)` (`ktScaleData_of_small`) — but in `ℝ³` each of
  these `Small C` is again the full `K_KT`.
* **Site F.**  With the clause on the *target* family, branch (i) of the reduction closes at the
  absolute accuracy `ε₀ = β/2` through `katzTaoGoal_of_absoluteLoss_of_card_ge_rpow` at `θ = 2`
  (`branch_i_of_strict_clause`), and the assembly no longer needs `SmallCard`
  (`strict_sub_of_dichotomy`, `slack_sub_of_dichotomy`, the `hsmall`-free analogues of
  `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy`).

**Summary in one line.**  The clause moves the band from the reduction's branch (i) into Lemma 6.1
and Lemma 9.1's tangential case; the residual at each site is small-family `K_KT`, and in `ℝ³`
small-family `K_KT` at any positive cardinality exponent is `K_KT` itself.

Nothing in this file is left unproved, no `axiom` or `opaque` is declared, no existing
declaration is edited, and the import closure (370 modules) contains no module of the abandoned
route (`Plank/`, `MainLemma2/NonSlab*`, `MainLemma2/Reduction/*` only).
-/

@[expose] public section

open MeasureTheory Topology ConvexSpaceBody Filter ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.KKTResidual

universe u

/-! ## 0. The restricted estimates -/

section Definitions

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **`K_KT'(β)`, strict form.**  GWZ Definition 3.4 (`Kakeya.KatzTaoEstimate`, verbatim) with the
extra hypothesis `δ^{-2} ≤ |𝕋|` after fullness. -/
def KatzTaoEstimateStrict (β : ℝ) : Prop := ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (- η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      (δ : ℝ) ^ (-2 : ℝ) ≤ (s.card : ℝ) →
      ∑ i ∈ s, volume (T i).shade ≤ δ ^ (- ε) * s.card ^ β * volume (⋃ i ∈ s, (T i).shade)

/-- **`K_KT'(β)`, slack form.**  Definition 3.4 with the extra hypothesis `δ^{-2+η} ≤ |𝕋|`, `η`
the prover's own loss exponent. -/
def KatzTaoEstimateSlack (β : ℝ) : Prop := ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (- η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      (δ : ℝ) ^ (-2 + η) ≤ (s.card : ℝ) →
      ∑ i ∈ s, volume (T i).shade ≤ δ ^ (- ε) * s.card ^ β * volume (⋃ i ∈ s, (T i).shade)

/-- **Small-family `K_KT` at cardinality exponent `C`.**  Definition 3.4 restricted to families
with `|𝕋| < δ^{-C}`. -/
def KatzTaoEstimateSmall (β C : ℝ) : Prop := ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (- η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      (s.card : ℝ) < (δ : ℝ) ^ (-C) →
      ∑ i ∈ s, volume (T i).shade ≤ δ ^ (- ε) * s.card ^ β * volume (⋃ i ∈ s, (T i).shade)

variable {E}

/-- A `δ^{-η}` Katz–Tao family is `δ^{-η'}` Katz–Tao for every `η' ≥ η` (general `E`; the tree's
`Kakeya.ML2Assembly.isKatzTao_of_exponent_le` is pinned to `ℝ³`). -/
theorem isKatzTao_of_exponent_le' {δ : NNReal} (hδ1 : δ ≤ 1) {ι : Type*} {s : Finset ι}
    {W : ι → ConvexSpaceBody E} {η η' : ℝ} (h : η ≤ η')
    (hKT : IsKatzTao s W ((δ : ENNReal) ^ (-η))) :
    IsKatzTao s W ((δ : ENNReal) ^ (-η')) :=
  hKT.mono (ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1) (by linarith))

/-- Definition 3.4 implies its strict restriction (drop the clause). -/
theorem strict_of_katzTaoEstimate {β : ℝ} (h : KatzTaoEstimate.{u} E β) :
    KatzTaoEstimateStrict.{u} E β := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ
  intro ι s T hball hKT hfull _
  exact hδ s T hball hKT hfull

/-- Definition 3.4 implies its slack restriction (drop the clause). -/
theorem slack_of_katzTaoEstimate {β : ℝ} (h : KatzTaoEstimate.{u} E β) :
    KatzTaoEstimateSlack.{u} E β := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ
  intro ι s T hball hKT hfull _
  exact hδ s T hball hKT hfull

/-- Definition 3.4 implies small-family `K_KT` at every exponent (drop the clause). -/
theorem small_of_katzTaoEstimate {β : ℝ} (C : ℝ) (h : KatzTaoEstimate.{u} E β) :
    KatzTaoEstimateSmall.{u} E β C := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ
  intro ι s T hball hKT hfull _
  exact hδ s T hball hKT hfull

/-- The slack form implies the strict form: `δ^{-2+η} ≤ δ^{-2} ≤ |𝕋|` for `δ ≤ 1`. -/
theorem strict_of_slack {β : ℝ} (h : KatzTaoEstimateSlack.{u} E β) :
    KatzTaoEstimateStrict.{u} E β := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδ hδ01
  obtain ⟨hδ0, hδ1⟩ := hδ01
  intro ι s T hball hKT hfull hcard
  refine hδ s T hball hKT hfull (le_trans ?_ hcard)
  exact Real.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ0) (by exact_mod_cast hδ1.le)
    (by linarith)

/-- **`Strict ∧ Small 2 → K_KT`.**  Case split on `δ^{-2} ≤ |𝕋|`. -/
theorem katzTaoEstimate_of_strict_of_small {β : ℝ}
    (hS : KatzTaoEstimateStrict.{u} E β) (hs : KatzTaoEstimateSmall.{u} E β 2) :
    KatzTaoEstimate.{u} E β := by
  intro ε hε
  obtain ⟨η₁, hη₁, hev₁⟩ := hS ε hε
  obtain ⟨η₂, hη₂, hev₂⟩ := hs ε hε
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, ?_⟩
  filter_upwards [hev₁, hev₂, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with δ h₁ h₂ hδ01
  obtain ⟨hδ0, hδ1⟩ := hδ01
  intro ι s T hball hKT hfull
  rcases le_or_gt ((δ : ℝ) ^ (-2 : ℝ)) (s.card : ℝ) with hge | hlt
  · exact h₁ s T hball (isKatzTao_of_exponent_le' hδ1.le (min_le_left _ _) hKT)
      (Kakeya.ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_left _ _) hfull) hge
  · exact h₂ s T hball (isKatzTao_of_exponent_le' hδ1.le (min_le_right _ _) hKT)
      (Kakeya.ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_right _ _) hfull) hlt

/-- **`Slack ∧ Small 2 → K_KT`.**  Case split on `δ^{-2+η₁} ≤ |𝕋|`; below it `|𝕋| < δ^{-2}`. -/
theorem katzTaoEstimate_of_slack_of_small {β : ℝ}
    (hS : KatzTaoEstimateSlack.{u} E β) (hs : KatzTaoEstimateSmall.{u} E β 2) :
    KatzTaoEstimate.{u} E β := by
  intro ε hε
  obtain ⟨η₁, hη₁, hev₁⟩ := hS ε hε
  obtain ⟨η₂, hη₂, hev₂⟩ := hs ε hε
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, ?_⟩
  filter_upwards [hev₁, hev₂, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with δ h₁ h₂ hδ01
  obtain ⟨hδ0, hδ1⟩ := hδ01
  intro ι s T hball hKT hfull
  rcases le_or_gt ((δ : ℝ) ^ (-2 + η₁)) (s.card : ℝ) with hge | hlt
  · exact h₁ s T hball (isKatzTao_of_exponent_le' hδ1.le (min_le_left _ _) hKT)
      (Kakeya.ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_left _ _) hfull) hge
  · refine h₂ s T hball (isKatzTao_of_exponent_le' hδ1.le (min_le_right _ _) hKT)
      (Kakeya.ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_right _ _) hfull)
      (lt_of_lt_of_le hlt ?_)
    exact Real.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ0) (by exact_mod_cast hδ1.le)
      (by linarith)

/-- **Summary (general `E`).**  `K_KT ↔ Strict ∧ Small 2`. -/
theorem katzTaoEstimate_iff_strict_and_small {β : ℝ} :
    KatzTaoEstimate.{u} E β ↔
      KatzTaoEstimateStrict.{u} E β ∧ KatzTaoEstimateSmall.{u} E β 2 :=
  ⟨fun h => ⟨strict_of_katzTaoEstimate h, small_of_katzTaoEstimate 2 h⟩,
    fun h => katzTaoEstimate_of_strict_of_small h.1 h.2⟩

/-- **Summary (general `E`).**  `K_KT ↔ Slack ∧ Small 2`. -/
theorem katzTaoEstimate_iff_slack_and_small {β : ℝ} :
    KatzTaoEstimate.{u} E β ↔
      KatzTaoEstimateSlack.{u} E β ∧ KatzTaoEstimateSmall.{u} E β 2 :=
  ⟨fun h => ⟨slack_of_katzTaoEstimate h, small_of_katzTaoEstimate 2 h⟩,
    fun h => katzTaoEstimate_of_slack_of_small h.1 h.2⟩

end Definitions

/-! ## 0'. In `ℝ³`, small-family `K_KT` at any positive exponent is `K_KT` (the tree's squeeze) -/

section Space3

/-- Small-family `K_KT` at exponent `C` is `Kakeya.ML2Squeeze.SmallCardCut C β` up to the
harmless conjunct `η ≤ 1` (shrink the witness). -/
theorem smallCardCut_of_small {β C : ℝ}
    (h : KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) β C) :
    Kakeya.ML2Squeeze.SmallCardCut.{u} C β := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := h ε hε
  refine ⟨min η 1, lt_min hη one_pos, min_le_right _ _, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδ hδ01
  obtain ⟨hδ0, hδ1⟩ := hδ01
  intro ι s T hball hKT hfull hcard
  exact hδ s T hball (isKatzTao_of_exponent_le' hδ1.le (min_le_left _ _) hKT)
    (Kakeya.ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_left _ _) hfull) hcard

/-- The converse: `SmallCardCut C β` is small-family `K_KT` at exponent `C`. -/
theorem small_of_smallCardCut {β C : ℝ} (h : Kakeya.ML2Squeeze.SmallCardCut.{u} C β) :
    KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) β C := by
  intro ε hε
  obtain ⟨η, hη, _, hev⟩ := h ε hε
  exact ⟨η, hη, hev⟩

/-- **In `ℝ³`, small-family `K_KT` at any exponent `C > 0` is `K_KT`** — the tree's affine
squeeze `Kakeya.ML2Squeeze.smallCardCut_iff_katzTaoEstimate`.  So "small-family `K_KT`" is never
a proper fragment of the estimate. -/
theorem small_iff_katzTaoEstimate {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 < C) :
    KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) β C ↔
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β :=
  ⟨fun h => (Kakeya.ML2Squeeze.smallCardCut_iff_katzTaoEstimate hβ hC).mp
      (smallCardCut_of_small h),
    fun h => small_of_katzTaoEstimate C h⟩

/-- Consequently, in `ℝ³` the strict conjunct of `katzTaoEstimate_iff_strict_and_small` is
redundant: `Small 2` alone is `K_KT`. -/
theorem katzTaoEstimate_iff_small_two {β : ℝ} (hβ : 0 ≤ β) :
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β ↔
      KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) β 2 :=
  (small_iff_katzTaoEstimate hβ two_pos).symm

end Space3


/-! ## 1. Site A — GWZ Lemma 6.1's high branch (`Kakeya.KatzTaoEstimate.plankEstimate`) -/

section SiteA

/-- **`ResidualA β`** — the bound the high branch of `Kakeya.KatzTaoEstimate.plankEstimate` needs
on the selected slab's `(b/8)`-tube family `A`, quantified exactly as the callback `hKT` of
`plankKT_highBranch` / `plankKT_post37` is produced at the call site
(`Plank/KatzTaoPlankEstimate.lean`: `fun τ hτ0 hτd t T' => hKT0 (b / 8) hb8pos hb8δ τ hτ0 hτd t T'`,
with `hKT0` from `Kakeya.exists_b0_multiplicity_bound`).  This is the threshold form of
generalized Lemma 3.7: the family binder ranges over *every* `δ`-tube family in the unit ball with
fullness `≥ τ^{ηKT}`, and there is **no** cardinality lower bound, because the site has none
(`#A` may be `1` or any `M`). -/
def ResidualA (β : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ ηKT : ℝ, 0 < ηKT ∧ ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧
    ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ → ∀ τ : ℝ≥0, 0 < τ → τ ≤ δ →
      ∀ {κ : Type u} (t : Finset κ) (T : κ → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
        τ ^ ηKT ≤ ShadedBody.fullness t (fun i => (T i).toShadedBody) →
        ShadedBody.multiplicity t (fun i => (T i).toShadedBody) ≤
          (τ : ENNReal) ^ (-ε)
            * (maxDensity t (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
            * (t.card : ENNReal) ^ β

/-- **Full `K_KT(β)` gives `ResidualA β`** — this is `Kakeya.exists_b0_multiplicity_bound`, i.e.
Lemma 3.7 (`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize`) in threshold form; it is how the
tree's `plankEstimate` consumes its `hKKT`. -/
theorem residualA_of_katzTaoEstimate {β : ℝ} (hβ0 : 0 ≤ β)
    (h : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) : ResidualA.{u} β :=
  fun ε hε => exists_b0_multiplicity_bound hβ0 h ε hε

/-- `fullness` only depends on the bodies indexed by `s`. -/
theorem fullness_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} (s : Finset ι) {V W : ι → ShadedBody E} (h : ∀ i ∈ s, V i = W i) :
    ShadedBody.fullness s V = ShadedBody.fullness s W := by
  unfold ShadedBody.fullness ShadedBody.fullness'
  rw [Finset.sum_congr rfl fun i hi => congrArg (fun B : ShadedBody E => volume B.shade) (h i hi),
    Finset.sum_congr rfl fun i hi => congrArg (fun B : ShadedBody E => volume B.carrier) (h i hi)]

/-- **`ResidualA β` gives back full `K_KT(β)`.**  Take `τ = δ`; pad the family outside `s` by one
of its own tubes so that the `∀ i` ball hypothesis of the callback holds; the `Δ_max^{1-β}` factor
is absorbed because `Δ_max ≤ δ^{-η}` with `η ≤ ε/2`; `ShadedBody.multiplicity_le_iff` converts to
mass form.  No cardinality information is used anywhere. -/
theorem katzTaoEstimate_of_residualA {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (h : ResidualA.{u} β) : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β := by
  classical
  intro ε hε
  obtain ⟨ηKT, hηKT, δ₀, hδ₀, hR⟩ := h (ε / 2) (half_pos hε)
  refine ⟨min ηKT (ε / 2), lt_min hηKT (half_pos hε), ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < min δ₀ 1 from lt_min hδ₀ zero_lt_one)]
    with δ hδ
  obtain ⟨hδ0, hδlt⟩ := hδ
  have hδδ₀ : δ ≤ δ₀ := hδlt.le.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδlt.le.trans (min_le_right _ _)
  intro ι s T hball hKT hfull
  rcases s.eq_empty_or_nonempty with hs | ⟨i₀, hi₀⟩
  · subst hs; simp
  -- pad the family outside `s` with the tube `T i₀`
  obtain ⟨T', hT'⟩ : ∃ T' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)),
      T' = fun i => if i ∈ s then T i else T i₀ := ⟨_, rfl⟩
  have hT'eq : ∀ i ∈ s, T' i = T i := fun i hi => by simp [hT', hi]
  have hball' : ∀ i, (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i
    by_cases hi : i ∈ s
    · rw [hT'eq i hi]; exact hball i hi
    · rw [hT']; simp only [hi, if_false]; exact hball i₀ hi₀
  have hbody : ∀ i ∈ s, (T' i).toShadedBody = (T i).toShadedBody :=
    fun i hi => by rw [hT'eq i hi]
  have hconv : ∀ i ∈ s, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody :=
    fun i hi => by rw [hT'eq i hi]
  have hmult : multiplicity s (fun i => (T' i).toShadedBody)
      = multiplicity s (fun i => (T i).toShadedBody) :=
    Kakeya.multiplicity_eq_of_eqOn _ s hbody
  have hΔ : maxDensity s (fun i => (T' i).toConvexSpaceBody)
      = maxDensity s (fun i => (T i).toConvexSpaceBody) := maxDensity_congr hconv
  have hfull' : δ ^ ηKT ≤ ShadedBody.fullness s (fun i => (T' i).toShadedBody) := by
    rw [fullness_congr s hbody]
    exact (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (min_le_left _ _)).trans hfull
  have hmain := hR δ hδ0 hδδ₀ δ hδ0 le_rfl s T' hball' hfull'
  rw [hmult, hΔ] at hmain
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hδE0 : (δ : ENNReal) ≠ 0 := by exact_mod_cast hδ0.ne'
  have h1β : (0 : ℝ) ≤ 1 - β := by linarith
  have hΔle : (maxDensity s (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
      ≤ (δ : ENNReal) ^ (-(ε / 2)) := by
    calc (maxDensity s (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
        ≤ ((δ : ENNReal) ^ (-(min ηKT (ε / 2)))) ^ (1 - β) := ENNReal.rpow_le_rpow hKT h1β
      _ = (δ : ENNReal) ^ (-(min ηKT (ε / 2)) * (1 - β)) := by rw [← ENNReal.rpow_mul]
      _ ≤ (δ : ENNReal) ^ (-(ε / 2)) := by
          apply ENNReal.rpow_le_rpow_of_exponent_ge hδE1
          have hm : min ηKT (ε / 2) ≤ ε / 2 := min_le_right _ _
          have hm0 : 0 ≤ min ηKT (ε / 2) := le_min hηKT.le (half_pos hε).le
          nlinarith [mul_le_mul_of_nonneg_left (show 1 - β ≤ 1 by linarith) hm0]
  have hfin : multiplicity s (fun i => (T i).toShadedBody)
      ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ β := by
    calc multiplicity s (fun i => (T i).toShadedBody)
        ≤ (δ : ENNReal) ^ (-(ε / 2))
            * (maxDensity s (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
            * (s.card : ENNReal) ^ β := hmain
      _ ≤ (δ : ENNReal) ^ (-(ε / 2)) * (δ : ENNReal) ^ (-(ε / 2)) * (s.card : ENNReal) ^ β := by
          gcongr
      _ = (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ β := by
          rw [← ENNReal.rpow_add _ _ hδE0 ENNReal.coe_ne_top]
          congr 2
          ring
  rw [multiplicity_le_iff] at hfin
  exact hfin

/-- **Site A, the statement-level fact.**  The callback the high branch consumes is *equivalent*
to clause-free `K_KT(β)` (GWZ Remark 6.2 in the tree's own terms). -/
theorem residualA_iff_katzTaoEstimate {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ResidualA.{u} β ↔ KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β :=
  ⟨katzTaoEstimate_of_residualA hβ0 hβ1, residualA_of_katzTaoEstimate hβ0⟩

/-- `ResidualA` implies the strict restricted estimate (so `Strict` is the weaker side). -/
theorem strict_of_residualA {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (h : ResidualA.{u} β) :
    KatzTaoEstimateStrict.{u} (EuclideanSpace ℝ (Fin 3)) β :=
  strict_of_katzTaoEstimate (katzTaoEstimate_of_residualA hβ0 hβ1 h)

/-- **Decomposition at site A: `Strict ∧ Small 2 → ResidualA`** (through full `K_KT` and Lemma
3.7).  This is the only route from `K_KT'` to the site's proposition: the strict/slack estimate is
never applied to the slab family `A` directly, because `A` carries no cardinality lower bound. -/
theorem residualA_of_strict_of_small {β : ℝ} (hβ0 : 0 ≤ β)
    (hS : KatzTaoEstimateStrict.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hs : KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) β 2) : ResidualA.{u} β :=
  residualA_of_katzTaoEstimate hβ0 (katzTaoEstimate_of_strict_of_small hS hs)

/-- The slack analogue. -/
theorem residualA_of_slack_of_small {β : ℝ} (hβ0 : 0 ≤ β)
    (hS : KatzTaoEstimateSlack.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hs : KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) β 2) : ResidualA.{u} β :=
  residualA_of_katzTaoEstimate hβ0 (katzTaoEstimate_of_slack_of_small hS hs)

/-- **The decisive direction: `ResidualA β → Small C` for every `C`.**  No slab-tiling
construction is needed: the callback is quantified over *all* `δ`-tube families (`τ = δ`), so the
small-family estimate is literally an instance of it. -/
theorem small_of_residualA {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (C : ℝ) (h : ResidualA.{u} β) :
    KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) β C :=
  small_of_katzTaoEstimate C (katzTaoEstimate_of_residualA hβ0 hβ1 h)

/-- **Site A, conclusion.**  Under `K_KT'(β)` (strict), the residual proposition is equivalent to
small-family `K_KT` at exponent `2` — and, by `small_iff_katzTaoEstimate`, to full `K_KT(β)`. -/
theorem residualA_iff_small_of_strict {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (_hS : KatzTaoEstimateStrict.{u} (EuclideanSpace ℝ (Fin 3)) β) :
    ResidualA.{u} β ↔ KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) β 2 :=
  ⟨small_of_residualA hβ0 hβ1 2, fun hs => residualA_of_strict_of_small hβ0 _hS hs⟩

/-- `ResidualA β ↔ Small C` for every `C > 0` (no clause hypothesis needed at all). -/
theorem residualA_iff_small {β C : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hC : 0 < C) :
    ResidualA.{u} β ↔ KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) β C :=
  (residualA_iff_katzTaoEstimate hβ0 hβ1).trans (small_iff_katzTaoEstimate hβ0 hC).symm

end SiteA

/-! ## 4. Site F — branch (i) of the reduction under the target clause -/

section SiteF

/-- **Branch (i) closes at `ε₀ = β/2` under the strict clause on the target family**:
`Kakeya.ML2Exchange.katzTaoGoal_of_absoluteLoss_of_card_ge_rpow` at `θ = 2`, budget
`β/2 ≤ ε + 2(β − c)`, which holds for every `ε > 0` once `2c ≤ β`. -/
theorem branch_i_of_strict_clause {ι : Type*} {s : Finset ι}
    {V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {β c ε : ℝ} (hc0 : 0 ≤ c) (hcβ : 2 * c ≤ β) (hε : 0 < ε)
    (hcard : (δ : ℝ) ^ (-2 : ℝ) ≤ (s.card : ℝ))
    (h : ∑ i ∈ s, volume (V i).shade
          ≤ (δ : ENNReal) ^ (-(β / 2)) * volume (⋃ i ∈ s, (V i).shade)) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ (β - c) * volume (⋃ i ∈ s, (V i).shade) :=
  Kakeya.ML2Exchange.katzTaoGoal_of_absoluteLoss_of_card_ge_rpow hδ hδ1 (θ := 2) (γ := β - c)
    (by linarith) (by linarith) hcard h

/-- **The assembly without `SmallCard`, strict target.**  The `hsmall`-free analogue of
`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy`: with the clause on the target family the
small-cardinality case never arises, branch (i) is `branch_i_of_strict_clause`, branch (ii) is
verbatim the tree's. -/
theorem strict_sub_of_dichotomy {β g η c : ℝ}
    (hc : 0 < c) (hcβ : 2 * c ≤ β) (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g)
    (hdich : Kakeya.ML2Assembly.Dichotomy.{u} β (β / 2) g η) :
    KatzTaoEstimateStrict.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) := by
  intro ε hε
  refine ⟨η, hη0, ?_⟩
  filter_upwards [hdich, Kakeya.ML2Assembly.eventually_card_thresholds] with δ hδdich hδthr
  obtain ⟨hδ0, hδ1, hδC⟩ := hδthr
  intro ι s T hball hKT hfull hcard
  have hge : (δ : ℝ)⁻¹ ≤ (s.card : ℝ) := by
    have h1 : (δ : ℝ) ^ (-1 : ℝ) ≤ (δ : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ0) (by exact_mod_cast hδ1)
        (by norm_num)
    rw [Real.rpow_neg_one] at h1
    exact h1.trans hcard
  rcases hδdich s T hball hKT hfull hge with hmass | hmass
  · exact branch_i_of_strict_clause (V := fun i ↦ (T i).toShadedBody) hδ0 hδ1 hc.le hcβ hε
      hcard hmass
  · rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0]
      simp
    have hcardle : (s.card : ℝ) ≤ (δ : ℝ) ^ (-4 : ℝ) :=
      Kakeya.ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s T hball hη1 hKT
    have hcoef : (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β
        ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ (β - c) :=
      Kakeya.ML2Reduction.le_rpow_mul_rpow_of_gain (β := β) (K := 4) hδ0 hδ1 hpos hc.le
        (by linarith) hcardle le_rfl
    calc ∑ i ∈ s, volume (T i).shade
        ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade) := hmass
      _ ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ (β - c)
            * volume (⋃ i ∈ s, (T i).shade) := by gcongr

/-- **The assembly without `SmallCard`, slack target.**  The prover's `η ≤ 1` makes the clause
`δ^{-2+η} ≤ |𝕋|` imply Wang's `δ^{-1} ≤ |𝕋|`, and branch (i) closes by the tree's
`katzTaoGoal_of_absoluteLoss_of_card_ge` (θ = 1). -/
theorem slack_sub_of_dichotomy {β g η c : ℝ}
    (hc : 0 < c) (hcβ : 2 * c ≤ β) (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g)
    (hdich : Kakeya.ML2Assembly.Dichotomy.{u} β (β / 2) g η) :
    KatzTaoEstimateSlack.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) := by
  intro ε hε
  refine ⟨η, hη0, ?_⟩
  filter_upwards [hdich, Kakeya.ML2Assembly.eventually_card_thresholds] with δ hδdich hδthr
  obtain ⟨hδ0, hδ1, hδC⟩ := hδthr
  intro ι s T hball hKT hfull hcard
  have hge : (δ : ℝ)⁻¹ ≤ (s.card : ℝ) := by
    have h1 : (δ : ℝ) ^ (-1 : ℝ) ≤ (δ : ℝ) ^ (-2 + η) :=
      Real.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ0) (by exact_mod_cast hδ1)
        (by linarith)
    rw [Real.rpow_neg_one] at h1
    exact h1.trans hcard
  rcases hδdich s T hball hKT hfull hge with hmass | hmass
  · exact Kakeya.MainLemma2.Reduction.katzTaoGoal_of_absoluteLoss_of_card_ge hδ0 hδ1
      (V := fun i ↦ (T i).toShadedBody) (ε := ε) (ε₀ := β / 2) (γ := β - c)
      (by linarith) (by linarith) hge hmass
  · rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0]
      simp
    have hcardle : (s.card : ℝ) ≤ (δ : ℝ) ^ (-4 : ℝ) :=
      Kakeya.ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s T hball hη1 hKT
    have hcoef : (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β
        ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ (β - c) :=
      Kakeya.ML2Reduction.le_rpow_mul_rpow_of_gain (β := β) (K := 4) hδ0 hδ1 hpos hc.le
        (by linarith) hcardle le_rfl
    calc ∑ i ∈ s, volume (T i).shade
        ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade) := hmass
      _ ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ (β - c)
            * volume (⋃ i ∈ s, (T i).shade) := by gcongr

/-- **Where the band goes.**  What the strict assembly delivers is `Strict (β − c)`; what the next
bootstrap step's sites A and D need is full `K_KT(β − c)`, i.e. additionally `Small 2` at `β − c`
(`katzTaoEstimate_iff_strict_and_small`) — the very band the clause removed from branch (i). -/
theorem katzTaoEstimate_sub_of_dichotomy_of_small {β g η c : ℝ}
    (hc : 0 < c) (hcβ : 2 * c ≤ β) (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g)
    (hdich : Kakeya.ML2Assembly.Dichotomy.{u} β (β / 2) g η)
    (hs : KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) 2) :
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) :=
  katzTaoEstimate_of_strict_of_small (strict_sub_of_dichotomy hc hcβ hη0 hη1 hg hdich) hs

end SiteF

/-! ## 2. Site D — Lemma 9.1's tangential case, the fibres `𝕋[T_{ρ₂}]` -/

section SiteD

/-- **`ResidualD cfg`** — the datum the non-slab split consumes: the field `katzTao` of
`Kakeya.VeryNotSticky.SplitInputs`, i.e. `cfg.KTScaleData cfg.ϱ` verbatim
(`MainLemma2/NonSlabSplit.lean`, consumed by `Kakeya.VeryNotSticky.nonslabKKT` /
`nonslabKKTPow`). -/
def ResidualD (cfg : VeryNotSticky.{u}) : Prop := cfg.KTScaleData cfg.ϱ

/-- `Kakeya.VeryNotSticky.KTScaleData`, unfolded — a definitional check that the reading is
verbatim: the `K_KT` cross-section at the configuration's scale `δ`, over every subfamily
`s' ⊆ cfg.s`, with **no** size clause. -/
theorem ktScaleData_iff (cfg : VeryNotSticky.{u}) (ε : ℝ) :
    cfg.KTScaleData ε ↔
      ∀ s' : Finset cfg.ι, s' ⊆ cfg.s →
        ConvexSpaceBody.IsKatzTao s' (fun i ↦ (cfg.T i).toConvexSpaceBody)
          ((cfg.δ : ENNReal) ^ (-cfg.η)) →
        ShadedBody.fullness s' (fun i ↦ (cfg.T i).toShadedBody) ≥ cfg.δ ^ (2 * cfg.η) →
        multiplicity s' (fun i ↦ (cfg.T i).toShadedBody) ≤
          (cfg.δ : ENNReal) ^ (-ε) * (s'.card : ENNReal) ^ cfg.β :=
  Iff.rfl

/-- **(a) From full `K_KT(β)`**, with the thresholds made explicit: `K_KT(β)` at accuracy `ε`
yields `η₁(ε, β) > 0` and `δ₀(ε, β) > 0` such that every configuration at exponent `β` with
`δ ≤ δ₀` and `2η ≤ η₁` has `KTScaleData ε`.  This is the existing route
`Kakeya.VeryNotSticky.ktScaleData_of_le` (which takes the cross-section as a hypothesis) fed by
`mem_nhdsGT_iff_exists_Ioc_subset` on the eventual clause of `Kakeya.KatzTaoEstimate`. -/
theorem ktScaleData_of_katzTaoEstimate {β : ℝ}
    (h : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) (ε : ℝ) (hε : 0 < ε) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧
      ∀ cfg : VeryNotSticky.{u}, cfg.β = β → cfg.δ ≤ δ₀ → 2 * cfg.η ≤ η₁ →
        cfg.KTScaleData ε := by
  obtain ⟨η₁, hη₁, hev⟩ := h ε hε
  obtain ⟨u, hu0, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  refine ⟨η₁, hη₁, u, hu0, ?_⟩
  intro cfg hβ hδ hη
  refine VeryNotSticky.ktScaleData_of_le cfg hη ?_
  intro s' T' hball hKT hfull
  have hcs := hsub ⟨cfg.hδ, hδ⟩ s' T' hball hKT hfull
  rw [multiplicity_le_iff, hβ]
  exact hcs

/-- The same at `ε = cfg.ϱ`, from the configuration's own field `ktEstimate`: `ResidualD cfg`
holds once `δ` is below the threshold and `2η` below the exponent threshold belonging to
`(cfg.ϱ, cfg.β)`. -/
theorem residualD_thresholds (cfg : VeryNotSticky.{u}) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧
      (cfg.δ ≤ δ₀ → 2 * cfg.η ≤ η₁ → ResidualD cfg) := by
  obtain ⟨η₁, hη₁, δ₀, hδ₀, H⟩ := ktScaleData_of_katzTaoEstimate cfg.ktEstimate cfg.ϱ cfg.hϱ
  exact ⟨η₁, hη₁, δ₀, hδ₀, fun hδ hη => H cfg rfl hδ hη⟩

/-! ### (b) The strict/slack clause is *false* on the fibres, from the upper bound alone -/

/-- **Pure-exponent form** (port of the site-D verifier's `capped_clause_false_from_upper_bound`,
).  With exactly the hypothesis shapes of
`Kakeya.VeryNotSticky.nonslabFibreCount` — `hfib : N·#sub ≤ #s`, `hcount : ρ^{-2-ζ} ≤ C·N` — the
Katz–Tao count `#s ≤ C'·δ^{-2-η}` and `ρ ≤ δ^r`, the clause `δ^{-2+θ} ≤ #sub` fails as soon as
`C·C'·δ^{r(2+ζ)-η-θ} < 1`, i.e. for all small `δ` once `r(2+ζ) > η + θ`. -/
theorem fibre_card_lt_rpow (δ ρ ζ η θ r C C' N sub s : ℝ)
    (hδ0 : 0 < δ) (hρ : 0 < ρ) (hρle : ρ ≤ δ ^ r) (hζ : 0 ≤ ζ)
    (hC : 0 < C) (hsub0 : 0 ≤ sub) (hN : 0 ≤ N)
    (hfib : N * sub ≤ s) (hcount : ρ ^ (-2 - ζ) ≤ C * N) (hs : s ≤ C' * δ ^ (-2 - η))
    (hsmall : C * C' * δ ^ (r * (2 + ζ) - η - θ) < 1) :
    sub < δ ^ (-2 + θ) := by
  have h1 : ρ ^ (2 + ζ) * ρ ^ (-2 - ζ) = 1 := by
    rw [← Real.rpow_add hρ]
    have hexp : (2 + ζ) + (-2 - ζ) = (0 : ℝ) := by ring
    rw [hexp, Real.rpow_zero]
  have hρpow_nonneg : 0 ≤ ρ ^ (2 + ζ) := Real.rpow_nonneg hρ.le _
  have hstep : 1 ≤ C * ρ ^ (2 + ζ) * N := by
    calc (1 : ℝ) = ρ ^ (2 + ζ) * ρ ^ (-2 - ζ) := h1.symm
      _ ≤ ρ ^ (2 + ζ) * (C * N) := mul_le_mul_of_nonneg_left hcount hρpow_nonneg
      _ = C * ρ ^ (2 + ζ) * N := by ring
  have hsub1 : sub ≤ C * ρ ^ (2 + ζ) * s := by
    calc sub = 1 * sub := (one_mul _).symm
      _ ≤ (C * ρ ^ (2 + ζ) * N) * sub := mul_le_mul_of_nonneg_right hstep hsub0
      _ = C * ρ ^ (2 + ζ) * (N * sub) := by ring
      _ ≤ C * ρ ^ (2 + ζ) * s :=
          mul_le_mul_of_nonneg_left hfib (mul_nonneg hC.le hρpow_nonneg)
  have hρpow : ρ ^ (2 + ζ) ≤ δ ^ (r * (2 + ζ)) := by
    rw [Real.rpow_mul hδ0.le]
    exact Real.rpow_le_rpow hρ.le hρle (by linarith)
  have hkey : δ ^ (r * (2 + ζ)) * δ ^ (-2 - η) =
      δ ^ (r * (2 + ζ) - η - θ) * δ ^ (-2 + θ) := by
    rw [← Real.rpow_add hδ0, ← Real.rpow_add hδ0]
    congr 1
    ring
  have hδpow_pos : 0 < δ ^ (-2 + θ) := Real.rpow_pos_of_pos hδ0 _
  have hs_nonneg : 0 ≤ s := le_trans (mul_nonneg hN hsub0) hfib
  calc sub ≤ C * ρ ^ (2 + ζ) * s := hsub1
    _ ≤ C * δ ^ (r * (2 + ζ)) * (C' * δ ^ (-2 - η)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hρpow hC.le
        · exact hs
        · exact hs_nonneg
        · exact mul_nonneg hC.le (Real.rpow_nonneg hδ0.le _)
    _ = C * C' * (δ ^ (r * (2 + ζ)) * δ ^ (-2 - η)) := by ring
    _ = (C * C' * δ ^ (r * (2 + ζ) - η - θ)) * δ ^ (-2 + θ) := by rw [hkey]; ring
    _ < 1 * δ ^ (-2 + θ) := mul_lt_mul_of_pos_right hsmall hδpow_pos
    _ = δ ^ (-2 + θ) := one_mul _

/-- **The Katz–Tao count of the configuration's family**, in real form:
`#𝕋 ≤ C_KT · δ^{-2-η}` from `Δ_max(𝕋) ≤ δ^{-η}` and `𝕋 ⊆ B₁`
(`Kakeya.Tube.card_le_of_densityIn_le`, the route of
`Kakeya.ML2Assembly.card_le_rpow_neg_four` without the crude rounding). -/
theorem card_le_config (cfg : VeryNotSticky.{u}) :
    (cfg.s.card : ℝ) ≤
      (Tube.card_le_of_densityIn_le.C 3 : ℝ) * (cfg.δ : ℝ) ^ (-2 - cfg.η) := by
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hδE0 : (cfg.δ : ENNReal) ≠ 0 := by exact_mod_cast cfg.hδ.ne'
  have hden : densityIn cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall ≤ (cfg.δ : ENNReal) ^ (-cfg.η) :=
    (le_maxDensity cfg.s _ _).trans cfg.maxDensity_le
  have hraw := Tube.card_le_of_densityIn_le (E := EuclideanSpace ℝ (Fin 3)) (δ := cfg.δ)
    (s := cfg.s) (T := fun i ↦ (cfg.T i).toTube) cfg.hδ.ne' cfg.contained hden
  rw [hE] at hraw
  norm_num at hraw
  have hzpow : (cfg.δ : ENNReal) ^ (-2 : ℤ) = (cfg.δ : ENNReal) ^ (-2 : ℝ) := by
    rw [← ENNReal.rpow_intCast]
    norm_num
  have hkey : (cfg.s.card : ENNReal) ≤
      (Tube.card_le_of_densityIn_le.C 3 : ENNReal) * (cfg.δ : ENNReal) ^ (-2 - cfg.η) := by
    refine hraw.trans ?_
    rw [hzpow, mul_assoc, ← ENNReal.rpow_add _ _ hδE0 ENNReal.coe_ne_top]
    apply le_of_eq
    congr 2
    ring
  rw [← ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne', ← ENNReal.coe_mul,
    show ((cfg.s.card : ENNReal)) = ((cfg.s.card : NNReal) : ENNReal) by simp,
    ENNReal.coe_le_coe, ← NNReal.coe_le_coe] at hkey
  simpa [NNReal.coe_rpow] using hkey

/-- **The capped clause is false on a fibre** (tree-level form).  For a configuration `cfg`, a
fibre `sub` obeying the two counting hypotheses of `nonslabFibreCount` at the fibre scale
`ρ₂ ≤ δ^r`, and `δ` below the fixed-scale threshold `hsmall`, one has `¬ (δ^{-2+θ} ≤ #sub)`.
Nothing about `sub` beyond the printed upper bound is used. -/
theorem capped_clause_false_at_fibre (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    {sub : Finset cfg.ι} (N : ℕ)
    (hfib : (N : ℝ) * (sub.card : ℝ) ≤ (cfg.s.card : ℝ))
    (hcount : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
      ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ℝ) ^ 2 * (N : ℝ))
    {r θ : ℝ} (hρle : (cfg.rho2 : ℝ) ≤ (cfg.δ : ℝ) ^ r)
    (hsmall : ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ℝ) ^ 2
      * (Tube.card_le_of_densityIn_le.C 3 : ℝ)
      * (cfg.δ : ℝ) ^ (r * (2 + cfg.ζ) - cfg.η - θ) < 1) :
    ¬ ((cfg.δ : ℝ) ^ (-2 + θ) ≤ (sub.card : ℝ)) := by
  have hC : (0 : ℝ) < ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ℝ) ^ 2 := by
    have h1 : (1 : NNReal) ≤ NonSlab.bodyAngleConstant C₀ := NonSlab.one_le_bodyAngleConstant hC₀
    have h2 : (0 : ℝ) < ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ℝ) := by
      have : (0 : NNReal) < 2 * NonSlab.bodyAngleConstant C₀ := by
        have : (0 : NNReal) < NonSlab.bodyAngleConstant C₀ := lt_of_lt_of_le one_pos h1
        positivity
      exact_mod_cast this
    positivity
  exact not_le.mpr (fibre_card_lt_rpow (cfg.δ : ℝ) (cfg.rho2 : ℝ) cfg.ζ cfg.η θ r _ _ N
    (sub.card : ℝ) (cfg.s.card : ℝ) (by exact_mod_cast cfg.hδ)
    (by exact_mod_cast VeryNotSticky.rho2_pos cfg) hρle cfg.hζ.le hC (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hfib hcount (card_le_config cfg) hsmall)

/-- **The strict clause `δ^{-2} ≤ #sub` is false on a fibre** (θ = 0): the hypothesis of
`KatzTaoEstimateStrict` is unavailable for the family the tangential case applies `K_KT` to, so
`Strict` contributes nothing there. -/
theorem strict_clause_false_at_fibre (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    {sub : Finset cfg.ι} (N : ℕ)
    (hfib : (N : ℝ) * (sub.card : ℝ) ≤ (cfg.s.card : ℝ))
    (hcount : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
      ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ℝ) ^ 2 * (N : ℝ))
    {r : ℝ} (hρle : (cfg.rho2 : ℝ) ≤ (cfg.δ : ℝ) ^ r)
    (hsmall : ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ℝ) ^ 2
      * (Tube.card_le_of_densityIn_le.C 3 : ℝ)
      * (cfg.δ : ℝ) ^ (r * (2 + cfg.ζ) - cfg.η) < 1) :
    ¬ ((cfg.δ : ℝ) ^ (-2 : ℝ) ≤ (sub.card : ℝ)) := by
  have h := capped_clause_false_at_fibre cfg hC₀ N hfib hcount (θ := 0) hρle
    (by simpa using hsmall)
  simpa using h

/-- **The slack clause `δ^{-2+ηKT} ≤ #sub` is false on a fibre** (θ = the prover's `ηKT`). -/
theorem slack_clause_false_at_fibre (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    {sub : Finset cfg.ι} (N : ℕ)
    (hfib : (N : ℝ) * (sub.card : ℝ) ≤ (cfg.s.card : ℝ))
    (hcount : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
      ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ℝ) ^ 2 * (N : ℝ))
    {r ηKT : ℝ} (hρle : (cfg.rho2 : ℝ) ≤ (cfg.δ : ℝ) ^ r)
    (hsmall : ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ℝ) ^ 2
      * (Tube.card_le_of_densityIn_le.C 3 : ℝ)
      * (cfg.δ : ℝ) ^ (r * (2 + cfg.ζ) - cfg.η - ηKT) < 1) :
    ¬ ((cfg.δ : ℝ) ^ (-2 + ηKT) ≤ (sub.card : ℝ)) :=
  capped_clause_false_at_fibre cfg hC₀ N hfib hcount hρle hsmall

/-- The exponent margin of the strict refutation is positive on the whole window `exscal ≤ r`
as soon as `2η < exscal` (the tree's standing relation between `η` and `exscal`); so
`strict_clause_false_at_fibre` applies at every fibre scale of the non-slab case for all small
`δ`. -/
theorem strict_margin_pos {exscal r ζ η : ℝ} (hex : 0 ≤ exscal) (hζ : 0 ≤ ζ)
    (hr : exscal ≤ r) (hη : 2 * η < exscal) : 0 < r * (2 + ζ) - η := by
  nlinarith [mul_le_mul_of_nonneg_right hr (by linarith : (0 : ℝ) ≤ 2 + ζ)]

/-- The capped margin `r(2+ζ) − η − θ` is positive iff `r > (θ + η)/(2+ζ)`; for Wang's `θ = 1`
this is the lower half of the window. -/
theorem capped_margin_pos_iff {r ζ η θ : ℝ} (hζ : 0 ≤ ζ) :
    0 < r * (2 + ζ) - η - θ ↔ (θ + η) / (2 + ζ) < r := by
  have h2 : (0 : ℝ) < 2 + ζ := by linarith
  rw [div_lt_iff₀ h2]
  constructor <;> intro h <;> linarith

/-- The fixed-scale thresholds `K · δ^m < 1` used above hold for all small `δ` when `m > 0`. -/
theorem eventually_const_mul_rpow_lt_one {K m : ℝ} (hK : 0 ≤ K) (hm : 0 < m) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), K * δ ^ m < 1 := by
  filter_upwards [absorb_const_le_rpow_neg (C := 2 * K + 1) (η := m) (by linarith) hm,
    self_mem_nhdsWithin] with δ hδ hδ0
  have hδ0' : (0 : ℝ) < δ := hδ0
  have hpow : 0 < δ ^ m := Real.rpow_pos_of_pos hδ0' _
  have hneg : δ ^ (-m) = (δ ^ m)⁻¹ := Real.rpow_neg hδ0'.le _
  rw [hneg] at hδ
  have h1 : (2 * K + 1) * δ ^ m ≤ 1 := by
    calc (2 * K + 1) * δ ^ m ≤ (δ ^ m)⁻¹ * δ ^ m := mul_le_mul_of_nonneg_right hδ hpow.le
      _ = 1 := inv_mul_cancel₀ hpow.ne'
  nlinarith

/-! ### (c) What the split consumes, and small-family `K_KT` at the fibre exponent -/

/-- **The fibre-restricted cross-section**: `KTScaleData` restricted to the subfamilies that
`Kakeya.VeryNotSticky.nonslabKKTPow` actually feeds it — fibres `sub = 𝕋[T_{ρ₂*}]` with the two
counting hypotheses of `nonslabFibreCount`. -/
def FibreKTData (cfg : VeryNotSticky.{u}) (C₀ : NNReal) (ε : ℝ) : Prop :=
  ∀ sub : Finset cfg.ι, sub ⊆ cfg.s → ∀ N : ℕ,
    (N : ℝ) * (sub.card : ℝ) ≤ (cfg.s.card : ℝ) →
    (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
      ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ℝ) ^ 2 * (N : ℝ) →
    ConvexSpaceBody.IsKatzTao sub (fun i ↦ (cfg.T i).toConvexSpaceBody)
      ((cfg.δ : ENNReal) ^ (-cfg.η)) →
    ShadedBody.fullness sub (fun i ↦ (cfg.T i).toShadedBody) ≥ cfg.δ ^ (2 * cfg.η) →
    multiplicity sub (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ENNReal) ^ (-ε) * (sub.card : ENNReal) ^ cfg.β

/-- `KTScaleData` restricts to the fibre datum. -/
theorem fibreKTData_of_ktScaleData (cfg : VeryNotSticky.{u}) (C₀ : NNReal) {ε : ℝ}
    (h : cfg.KTScaleData ε) : FibreKTData cfg C₀ ε :=
  fun sub hsub _ _ _ hKT hfull => h sub hsub hKT hfull

/-- **`nonslabKKTPow` re-proved from the fibre datum alone**: the split's consumption of
`KTScaleData` is exactly at fibres.  Statement and proof are those of
`Kakeya.VeryNotSticky.nonslabKKTPow` with `hKT : FibreKTData` in place of `KTScaleData`, at
the fibre-count constant `K = 1` of the datum's own shape. -/
theorem nonslabKKTPow_of_fibreKTData (cfg : VeryNotSticky.{u}) (hβ1 : cfg.β ≤ 1)
    {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    (hKT : FibreKTData cfg C₀ cfg.ϱ)
    (hCδ : ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ENNReal) ^ 2 ≤
      (cfg.δ : ENNReal) ^ (-cfg.η))
    {sub : Finset cfg.ι} (hsub : sub ⊆ cfg.s)
    (hfull : ShadedBody.fullness sub (fun i ↦ (cfg.T i).toShadedBody) ≥ cfg.δ ^ (2 * cfg.η))
    (N : ℕ) (hfib : (N : ℝ) * (sub.card : ℝ) ≤ (cfg.s.card : ℝ))
    (hcount : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
      ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ℝ) ^ 2 * (N : ℝ)) :
    multiplicity sub (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ + cfg.η)) *
        ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β := by
  have hmult := hKT sub hsub N hfib hcount
    (ConvexSpaceBody.IsKatzTao.subset
      ((ConvexSpaceBody.IsKatzTao_def cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)).mpr
        cfg.maxDensity_le) hsub) hfull
  have hfib1 : (N : ℝ) * (sub.card : ℝ) ≤ ((1 : NNReal) : ℝ) * (cfg.s.card : ℝ) := by
    simpa using hfib
  -- the count constant of `nonslabFibreCount`/`nonslabFibreCountPow` is a parameter since
  -- This datum uses the fixed comparison constant.
  -- `Ccnt = (2 C_{lem:ml2bodyAngle}(C₀))²` and `M = 1`, so no statement in this file changes
  have hcount1 : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
      (((2 * NonSlab.bodyAngleConstant C₀ : NNReal) ^ 2 : NNReal) : ℝ) * (N : ℝ) := by
    simpa [NNReal.coe_pow] using hcount
  have hCδ1 : ((1 : NNReal) : ENNReal) *
      (((2 * NonSlab.bodyAngleConstant C₀ : NNReal) ^ 2 : NNReal) : ENNReal) ≤
        (cfg.δ : ENNReal) ^ (-((1 : ℝ) * cfg.η)) := by
    simpa [ENNReal.coe_pow] using hCδ
  have hcard := VeryNotSticky.nonslabFibreCount cfg (VeryNotSticky.rho2_pos cfg) N hfib1 hcount1
  have hpow0 := VeryNotSticky.nonslabFibreCountPow cfg hβ1 (M := 1) zero_le_one hCδ1 hcard
  have hpow : (sub.card : ENNReal) ^ cfg.β ≤ (cfg.δ : ENNReal) ^ (-cfg.η) *
      ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β := by
    simpa using hpow0
  have hδne0 : (cfg.δ : ENNReal) ≠ 0 := by
    exact_mod_cast ne_of_gt cfg.hδ
  have hδneTop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hexp : (cfg.δ : ENNReal) ^ (-cfg.η) * (cfg.δ : ENNReal) ^ (-cfg.ϱ) =
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ + cfg.η)) := by
    rw [← ENNReal.rpow_add (-cfg.η) (-cfg.ϱ) hδne0 hδneTop]
    congr
    ring
  calc
    multiplicity sub (fun i ↦ (cfg.T i).toShadedBody) ≤
        (cfg.δ : ENNReal) ^ (-cfg.ϱ) * (sub.card : ENNReal) ^ cfg.β := hmult
    _ = (sub.card : ENNReal) ^ cfg.β * (cfg.δ : ENNReal) ^ (-cfg.ϱ) := by
      rw [mul_comm]
    _ ≤ ((cfg.δ : ENNReal) ^ (-cfg.η) *
          ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β) *
          (cfg.δ : ENNReal) ^ (-cfg.ϱ) := by
      exact mul_le_mul_left hpow _
    _ = (cfg.δ : ENNReal) ^ (-(cfg.ϱ + cfg.η)) *
          ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β := by
      rw [mul_right_comm, hexp]

/-- **The fibre cardinality exponent.**  From the upper bound `nonslabFibreCount` and the window
top `ρ₂ ≤ δ^{exscal}` (`Kakeya.VeryNotSticky.rho2_range`), every fibre has
`#sub < δ^{-C_D}` with `C_D = 2 + η − exscal·(2+ζ) + μ`, for any margin `μ > 0` once
`(2 C_{bodyAngle}(C₀))² · C_KT · δ^μ < 1`.  This is the smallest exponent covering the fibres
uniformly over the window (at `r = exscal`; deeper fibres are smaller still). -/
theorem fibre_card_lt (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    {sub : Finset cfg.ι} (N : ℕ)
    (hfib : (N : ℝ) * (sub.card : ℝ) ≤ (cfg.s.card : ℝ))
    (hcount : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
      ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ℝ) ^ 2 * (N : ℝ))
    (hρle : (cfg.rho2 : ℝ) ≤ (cfg.δ : ℝ) ^ cfg.exscal) {μ : ℝ}
    (hthr : ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ℝ) ^ 2
      * (Tube.card_le_of_densityIn_le.C 3 : ℝ) * (cfg.δ : ℝ) ^ μ < 1) :
    (sub.card : ℝ) < (cfg.δ : ℝ) ^ (-(2 + cfg.η - cfg.exscal * (2 + cfg.ζ) + μ)) := by
  have h := not_le.mp (capped_clause_false_at_fibre cfg hC₀ N hfib hcount
    (θ := cfg.exscal * (2 + cfg.ζ) - cfg.η - μ) hρle (by
      have : cfg.exscal * (2 + cfg.ζ) - cfg.η - (cfg.exscal * (2 + cfg.ζ) - cfg.η - μ) = μ := by
        ring
      rw [this]; exact hthr))
  have : (-2 + (cfg.exscal * (2 + cfg.ζ) - cfg.η - μ) : ℝ)
      = -(2 + cfg.η - cfg.exscal * (2 + cfg.ζ) + μ) := by ring
  rw [this] at h
  exact h

/-- The window-top bound `ρ₂ ≤ δ^{exscal}` in real form, from the tree's
`Kakeya.VeryNotSticky.rho2_range` under the non-slab hypothesis `b ≤ δ^{exscal} r₁`. -/
theorem rho2_le_rpow_exscal (cfg : VeryNotSticky.{u}) (hexscal : cfg.exscal ≤ 1 / 2)
    (hnotslab : cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁) :
    (cfg.rho2 : ℝ) ≤ (cfg.δ : ℝ) ^ cfg.exscal := by
  have h := (VeryNotSticky.rho2_range cfg cfg.hδ cfg.hδ1 hexscal hnotslab).1.2
  have h' : ((cfg.rho2 : NNReal) : ℝ) ≤ ((cfg.δ ^ cfg.exscal : NNReal) : ℝ) := by
    exact_mod_cast h
  simpa [NNReal.coe_rpow] using h'

/-- Monotonicity in the exponent: a fibre below `δ^{-C_D}` is below `δ^{-C}` for every
`C ≥ C_D`. -/
theorem fibre_card_lt_of_le (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    {sub : Finset cfg.ι} (N : ℕ)
    (hfib : (N : ℝ) * (sub.card : ℝ) ≤ (cfg.s.card : ℝ))
    (hcount : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
      ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ℝ) ^ 2 * (N : ℝ))
    (hρle : (cfg.rho2 : ℝ) ≤ (cfg.δ : ℝ) ^ cfg.exscal) {μ C : ℝ}
    (hthr : ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ℝ) ^ 2
      * (Tube.card_le_of_densityIn_le.C 3 : ℝ) * (cfg.δ : ℝ) ^ μ < 1)
    (hCD : 2 + cfg.η - cfg.exscal * (2 + cfg.ζ) + μ ≤ C) :
    (sub.card : ℝ) < (cfg.δ : ℝ) ^ (-C) :=
  lt_of_lt_of_le (fibre_card_lt cfg hC₀ N hfib hcount hρle hthr)
    (Real.rpow_le_rpow_of_exponent_ge (by exact_mod_cast cfg.hδ) (by exact_mod_cast cfg.hδ1)
      (by linarith))

/-- **(c) Small-family `K_KT` at exponent `C` gives the fibre datum**, for every configuration
whose fibres are `< δ^{-C}` (which `fibre_card_lt_of_le` certifies at `C ≥ C_D`).  The route is
`ktScaleData_of_katzTaoEstimate`'s, with the size clause discharged at each fibre. -/
theorem fibreKTData_of_small {β C : ℝ}
    (h : KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) β C) (ε : ℝ) (hε : 0 < ε) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧
      ∀ cfg : VeryNotSticky.{u}, cfg.β = β → cfg.δ ≤ δ₀ → 2 * cfg.η ≤ η₁ →
        ∀ C₀ : NNReal,
        (∀ sub : Finset cfg.ι, ∀ N : ℕ, (N : ℝ) * (sub.card : ℝ) ≤ (cfg.s.card : ℝ) →
          (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
            ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ℝ) ^ 2 * (N : ℝ) →
          (sub.card : ℝ) < (cfg.δ : ℝ) ^ (-C)) →
        FibreKTData cfg C₀ ε := by
  obtain ⟨η₁, hη₁, hev⟩ := h ε hε
  obtain ⟨u, hu0, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  refine ⟨η₁, hη₁, u, hu0, ?_⟩
  intro cfg hβ hδ hη C₀ hsize sub hsubs N hfib hcount hKT hfull
  have hball : ∀ i ∈ sub, (cfg.T i).carrier ⊆ Metric.closedBall 0 1 :=
    fun i hi => cfg.contained i (hsubs hi)
  have hη1 : cfg.η ≤ η₁ := le_trans (by linarith [cfg.hη]) hη
  have hKT' : ConvexSpaceBody.IsKatzTao sub (fun i ↦ (cfg.T i).toConvexSpaceBody)
      ((cfg.δ : ENNReal) ^ (-η₁)) :=
    isKatzTao_of_exponent_le' cfg.hδ1 hη1 hKT
  have hfull' : ShadedBody.fullness sub (fun i ↦ (cfg.T i).toShadedBody) ≥ cfg.δ ^ η₁ :=
    Kakeya.ML2Assembly.le_of_rpow_exponent_le cfg.hδ cfg.hδ1 hη hfull
  have hcs := hsub ⟨cfg.hδ, hδ⟩ sub cfg.T hball hKT' hfull' (hsize sub N hfib hcount)
  rw [multiplicity_le_iff, hβ]
  exact hcs

/-- **Whole-family version**: small-family `K_KT` at exponent `C` gives `KTScaleData` itself for
every configuration with `#𝕋 < δ^{-C}` — which needs `C > 2 + η`
(`config_card_lt`), since every subfamily `s' ⊆ 𝕋` must be covered, `𝕋` included. -/
theorem ktScaleData_of_small {β C : ℝ}
    (h : KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) β C) (ε : ℝ) (hε : 0 < ε) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧
      ∀ cfg : VeryNotSticky.{u}, cfg.β = β → cfg.δ ≤ δ₀ → 2 * cfg.η ≤ η₁ →
        (cfg.s.card : ℝ) < (cfg.δ : ℝ) ^ (-C) → cfg.KTScaleData ε := by
  obtain ⟨η₁, hη₁, hev⟩ := h ε hε
  obtain ⟨u, hu0, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  refine ⟨η₁, hη₁, u, hu0, ?_⟩
  intro cfg hβ hδ hη hcard s' hs' hKT hfull
  have hball : ∀ i ∈ s', (cfg.T i).carrier ⊆ Metric.closedBall 0 1 :=
    fun i hi => cfg.contained i (hs' hi)
  have hη1 : cfg.η ≤ η₁ := le_trans (by linarith [cfg.hη]) hη
  have hKT' : ConvexSpaceBody.IsKatzTao s' (fun i ↦ (cfg.T i).toConvexSpaceBody)
      ((cfg.δ : ENNReal) ^ (-η₁)) :=
    isKatzTao_of_exponent_le' cfg.hδ1 hη1 hKT
  have hfull' : ShadedBody.fullness s' (fun i ↦ (cfg.T i).toShadedBody) ≥ cfg.δ ^ η₁ :=
    Kakeya.ML2Assembly.le_of_rpow_exponent_le cfg.hδ cfg.hδ1 hη hfull
  have hlt : (s'.card : ℝ) < (cfg.δ : ℝ) ^ (-C) :=
    lt_of_le_of_lt (by exact_mod_cast Finset.card_le_card hs') hcard
  have hcs := hsub ⟨cfg.hδ, hδ⟩ s' cfg.T hball hKT' hfull' hlt
  rw [multiplicity_le_iff, hβ]
  exact hcs

/-- The whole family is below `δ^{-(2+η+μ)}` once `C_KT · δ^μ < 1`. -/
theorem config_card_lt (cfg : VeryNotSticky.{u}) {μ : ℝ}
    (hthr : (Tube.card_le_of_densityIn_le.C 3 : ℝ) * (cfg.δ : ℝ) ^ μ < 1) :
    (cfg.s.card : ℝ) < (cfg.δ : ℝ) ^ (-(2 + cfg.η + μ)) := by
  have hδ0 : (0 : ℝ) < cfg.δ := by exact_mod_cast cfg.hδ
  have hkey : (cfg.δ : ℝ) ^ (-2 - cfg.η) = (cfg.δ : ℝ) ^ μ * (cfg.δ : ℝ) ^ (-(2 + cfg.η + μ)) := by
    rw [← Real.rpow_add hδ0]
    congr 1
    ring
  have hpos : 0 < (cfg.δ : ℝ) ^ (-(2 + cfg.η + μ)) := Real.rpow_pos_of_pos hδ0 _
  calc (cfg.s.card : ℝ) ≤ (Tube.card_le_of_densityIn_le.C 3 : ℝ) * (cfg.δ : ℝ) ^ (-2 - cfg.η) :=
        card_le_config cfg
    _ = ((Tube.card_le_of_densityIn_le.C 3 : ℝ) * (cfg.δ : ℝ) ^ μ)
          * (cfg.δ : ℝ) ^ (-(2 + cfg.η + μ)) := by rw [hkey]; ring
    _ < 1 * (cfg.δ : ℝ) ^ (-(2 + cfg.η + μ)) := mul_lt_mul_of_pos_right hthr hpos
    _ = (cfg.δ : ℝ) ^ (-(2 + cfg.η + μ)) := one_mul _

/-- **Site D, conclusion.**  In `ℝ³` the fibre exponent buys nothing: small-family `K_KT` at the
fibre exponent (indeed at any `C > 0`) is full `K_KT`, so `fibreKTData_of_small` is
`ktScaleData_of_katzTaoEstimate` in disguise, and `ResidualD` follows from `K_KT'` only through
the same `Small` that `K_KT'` lacks. -/
theorem small_fibre_iff_katzTaoEstimate {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 < C) :
    KatzTaoEstimateSmall.{u} (EuclideanSpace ℝ (Fin 3)) β C ↔
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β :=
  small_iff_katzTaoEstimate hβ hC

end SiteD

end Kakeya.KKTResidual
