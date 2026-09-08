/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimates
public import Kakeya.Bootstrap
public import Kakeya.Asymptotics
public import Kakeya.DimensionThree.FrostmanEstimateOne

/-!
# The two-parameter partial estimates `K_KT(β, ω)` and `K_F(β, ω)`

Guth-Wang-Zahl state Main Lemma 2 with an exponent drop `ν = ν(β)` produced before the
accuracy `ε`, but their proof produces `ν` only after `ε`.  The detailed Wang-Zahl paper
avoids this by carrying a *second* parameter `ω` in each assertion: a budget standing in the
same power of `δ` as the accuracy, out of which a fixed accuracy can be paid.  Wang-Zahl
Definition 1.5 defines `D(σ, ω)` and `E(σ, ω)`; the gain of Wang-Zahl Proposition 1.7 is
taken in `ω` rather than in `σ`; the `σ`-gain follows by a trade against the packing bound;
and `ω = 0` is recovered by soft closedness.

This module builds the corresponding layer over the development's own one-parameter
`Kakeya.KatzTaoEstimate` and `Kakeya.FrostmanEstimate`, together with the outer-scheme
machinery that consumes it.  Nothing here modifies the one-parameter definitions or any part
of the existing Main Lemma 2 reduction; the module states the corresponding implications.

Contents.

* `Kakeya.KatzTaoEstimateOmega` and `Kakeya.FrostmanEstimateOmega`: the two-parameter
  assertions, with `δ ^ (-ε)` replaced by `δ ^ (-ω - ε)`.  They specialize at `ω = 0` to the
  one-parameter definitions (`Kakeya.katzTaoEstimateOmega_zero`,
  `Kakeya.frostmanEstimateOmega_zero`).
* The elementary transfer lemmas: monotonicity in `ω` and in `β`, the passage from the
  one-parameter assertion, and the `ω`-absorption
  `Kakeya.KatzTaoEstimateOmega.of_forall_gt`.  The absorption is *not* a limit: at accuracy
  `ε` one instantiates the hypothesis at `ω' = ω + ε/2` and inner accuracy `ε/2`.  It cannot
  be written as a limit, because the witnesses `η` and `δ₀` are produced after both `ω'` and
  `ε`, with no uniformity in either.
* The packing bound `Kakeya.eventually_card_le_rpow_neg_three`, and the two consequences that
  need it: the `ω`-to-`β` trade `Kakeya.KatzTaoEstimateOmega.trade` and closedness in `β`
  at fixed `ω` (`Kakeya.KatzTaoEstimateOmega.of_forall_gt_beta`).
* The two-parameter descent `Kakeya.ioc_subset_of_sub_mem_of_monotoneOn_param`, which is the
  existing single-parameter `Kakeya.ioc_subset_of_sub_mem_of_monotoneOn` read at a fixed `ω`.
* The assembly `Kakeya.katzTaoEstimate_of_mainLemma2Omega`: from a two-parameter Main Lemma 2
  in the shape of Wang-Zahl Proposition 1.7, taken as a hypothesis, the one-parameter
  `K_KT(β)` follows for every `β ∈ (0, 1]`.
-/

@[expose] public section

open MeasureTheory Topology ConvexSpaceBody Filter ShadedBody

namespace Kakeya

universe u

section Definitions

variable
  (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The two-parameter Katz-Tao estimate `K_KT(β, ω)`.

This is `Kakeya.KatzTaoEstimate` with the accuracy factor `δ ^ (-ε)` of the conclusion
replaced by `δ ^ (-ω - ε)`.  The budget `ω` is a parameter of the assertion, hence available
*before* the accuracy `ε`, which is what lets an input be read at an accuracy fixed in
advance. -/
def KatzTaoEstimateOmega (β ω : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (- η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      ∑ i ∈ s, volume (T i).shade ≤
        δ ^ (- ω - ε) * s.card ^ β * volume (⋃ i ∈ s, (T i).shade)

/-- The two-parameter Frostman estimate `K_F(β, ω)`.

This is `Kakeya.FrostmanEstimate` with the factor `δ ^ (-ε - 2 * β)` of the conclusion
replaced by `δ ^ (-ω - ε - 2 * β)`. -/
def FrostmanEstimateOmega (β ω : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
        (δ ^ (- η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        δ ^ (- ω - ε - 2 * β) * (s.card * δ ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2)

/-- At `ω = 0` the two-parameter Katz-Tao estimate is the one-parameter one. -/
theorem katzTaoEstimateOmega_zero {β : ℝ} :
    KatzTaoEstimateOmega.{u} E β 0 ↔ KatzTaoEstimate.{u} E β := by
  simp only [KatzTaoEstimateOmega, KatzTaoEstimate, neg_zero, zero_sub]

/-- At `ω = 0` the two-parameter Frostman estimate is the one-parameter one. -/
theorem frostmanEstimateOmega_zero {β : ℝ} :
    FrostmanEstimateOmega.{u} E β 0 ↔ FrostmanEstimate.{u} E β := by
  simp only [FrostmanEstimateOmega, FrostmanEstimate, neg_zero, zero_sub]

end Definitions

section Transfer

variable
  {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `K_KT(β, ω)` is monotone in the budget `ω`: a smaller budget is a stronger statement,
because `δ ≤ 1`. -/
theorem KatzTaoEstimateOmega.mono_omega {β ω ω' : ℝ} (hωω' : ω ≤ ω')
    (h : KatzTaoEstimateOmega.{u} E β ω) : KatzTaoEstimateOmega.{u} E β ω' := by
  intro ε hε
  rcases h ε hε with ⟨η, hη, hev⟩
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with δ hδ_ev hδ01
  obtain ⟨hδ0, hδ1⟩ := hδ01
  intro ι s T hball hKT hfull
  refine (hδ_ev s T hball hKT hfull).trans ?_
  have hpow : (δ : ENNReal) ^ (-ω - ε) ≤ (δ : ENNReal) ^ (-ω' - ε) := by
    exact ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1.le)
      (by linarith [hωω'])
  gcongr

/-- `K_F(β, ω)` is monotone in the budget `ω`. -/
theorem FrostmanEstimateOmega.mono_omega {β ω ω' : ℝ} (hωω' : ω ≤ ω')
    (h : FrostmanEstimateOmega.{u} E β ω) : FrostmanEstimateOmega.{u} E β ω' := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with δ hδ_ev hδIoo
  obtain ⟨hδ0, hδ1⟩ := hδIoo
  intro ι s T hball hpair hFr hfull
  refine (hδ_ev s T hball hpair hFr hfull).trans ?_
  have hpow : (δ : ENNReal) ^ (-ω - ε - 2 * β) ≤ (δ : ENNReal) ^ (-ω' - ε - 2 * β) := by
    exact ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1.le) (by linarith)
  gcongr

/-- `K_KT(·, ω)` is monotone in the exponent `β` at fixed budget, by the same argument as
`Kakeya.KatzTaoEstimate.mono`.  The step is accuracy-preserving: the accuracy witness `η` is
unchanged. -/
theorem KatzTaoEstimateOmega.mono {β β' ω : ℝ} (hββ' : β ≤ β')
    (h : KatzTaoEstimateOmega.{u} E β ω) : KatzTaoEstimateOmega.{u} E β' ω := by
  intro ε hε
  obtain ⟨η, hη, hh⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hh] with δ hh_δ
  intro ι s T hball hKT hfull
  by_cases hcard : s.card = 0
  · have hs : s = ∅ := Finset.card_eq_zero.mp hcard
    subst hs; simp
  refine (hh_δ s T hball hKT hfull).trans ?_
  have hone : (1 : ENNReal) ≤ (s.card : ENNReal) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcard
  gcongr

/-- The one-parameter estimate implies the two-parameter one at every nonnegative budget:
instantiate the accuracy at `ω + ε`. -/
theorem KatzTaoEstimate.toOmega {β ω : ℝ} (hω : 0 ≤ ω) (h : KatzTaoEstimate.{u} E β) :
    KatzTaoEstimateOmega.{u} E β ω := by
  intro ε hε
  have hωε : 0 < ω + ε := lt_of_le_of_lt hω (lt_add_of_pos_right _ hε)
  obtain ⟨η, hη, hev⟩ := h (ω + ε) hωε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ_ev
  intro ι s T hball hKT hfull
  convert hδ_ev s T hball hKT hfull using 3
  ring

/-- The one-parameter Frostman estimate implies the two-parameter one at every nonnegative
budget. -/
theorem FrostmanEstimate.toOmega {β ω : ℝ} (hω : 0 ≤ ω) (h : FrostmanEstimate.{u} E β) :
    FrostmanEstimateOmega.{u} E β ω := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := h (ω + ε) (add_pos_of_nonneg_of_pos hω hε)
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ_ev
  intro ι s T hball hpair hFr hfull
  have hδ_ev' := hδ_ev s T hball hpair hFr hfull
  rw [show -(ω + ε) - 2 * β = -ω - ε - 2 * β by ring] at hδ_ev'
  exact hδ_ev'

/-- **Absorption of the budget** (Wang-Zahl, closedness in `ω`).  If `K_KT(β, ω')` holds for
every `ω' > ω`, then `K_KT(β, ω)` holds.

This is *not* a limit and must not be proved as one: given the accuracy `ε`, instantiate the
hypothesis at `ω' = ω + ε/2` and inner accuracy `ε/2`, and note
`-(ω + ε/2) - ε/2 = -ω - ε`.  A limiting argument fails, because the witnesses `η` and `δ₀`
are produced after both `ω'` and `ε` and there is no uniformity in either. -/
theorem KatzTaoEstimateOmega.of_forall_gt {β ω : ℝ}
    (h : ∀ ω' > ω, KatzTaoEstimateOmega.{u} E β ω') : KatzTaoEstimateOmega.{u} E β ω := by
  intro ε hε
  rcases h (ω + ε / 2) (by linarith) (ε / 2) (by positivity) with ⟨η, hη, hev⟩
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ_ev
  intro ι s T hball hKT hfull
  convert hδ_ev s T hball hKT hfull using 3
  ring

/-- The one-parameter estimate is exactly the two-parameter one at all positive budgets. -/
theorem katzTaoEstimate_iff_forall_omega_pos {β : ℝ} :
    KatzTaoEstimate.{u} E β ↔ ∀ ω > (0 : ℝ), KatzTaoEstimateOmega.{u} E β ω := by
  constructor
  · intro h ω hω
    exact KatzTaoEstimate.toOmega hω.le h
  · intro h
    exact (katzTaoEstimateOmega_zero (E := E)).mp (KatzTaoEstimateOmega.of_forall_gt h)

/-- The accuracy witness of `K_KT(β, ω)` may always be taken below any prescribed bound `M`:
shrinking `η` strengthens both hypotheses of the assertion. -/
theorem KatzTaoEstimateOmega.small_eta {β ω : ℝ} (h : KatzTaoEstimateOmega.{u} E β ω)
    {ε : ℝ} (hε : 0 < ε) {M : ℝ} (hM : 0 < M) :
    ∃ η, 0 < η ∧ η ≤ M ∧ ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (- η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        ∑ i ∈ s, volume (T i).shade ≤
          δ ^ (- ω - ε) * s.card ^ β * volume (⋃ i ∈ s, (T i).shade) := by
  obtain ⟨η₀, hη₀, hev⟩ := h ε hε
  refine ⟨min η₀ M, lt_min hη₀ hM, min_le_right _ _, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with δ hδ_ev ⟨hδ0, hδ1⟩
  intro ι s T hball hKT hfull
  refine hδ_ev s T hball ?_ ?_
  · exact hKT.mono (ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1.le)
      (neg_le_neg (min_le_left η₀ M)))
  · exact (NNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ0)
      (by exact_mod_cast hδ1.le) (min_le_left η₀ M)).trans hfull

end Transfer

section Packing

variable
  {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **The packing bound.**  In `ℝ³`, a family of `δ`-tubes in the unit ball whose maximal
density is at most `δ ^ (-η)` with `0 ≤ η ≤ 1/2` has at most `δ ^ (-3)` members, once `δ` is
small enough to absorb the dimensional constant of
`Kakeya.Tube.card_le_of_densityIn_le`.

This is the input for both the `ω`-to-`β` trade and closedness in `β`.  It is the same
inequality as the one inside `Kakeya.ML2Reduction.multiplicity_le_of_gain`, but that lemma is
not reusable here: it takes a `Kakeya.ML2Reduction.ReductionConfig`, which carries a uniform
structure and pairwise essential distinctness, neither of which is available among the
hypotheses of `K_KT`.

`_hη0` records the blueprint's range `0 ≤ η ≤ 1/2` but is not consumed: for `η < 0` and
`δ ≤ 1` the factor `δ ^ (-η)` is at most `1`, so the bound only improves. -/
theorem eventually_card_le_rpow_neg_three (hn : Module.finrank ℝ E = 3)
    {η : ℝ} (_hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (- η)) →
        (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-3 : ℝ) := by
  set n : ℕ := Module.finrank ℝ E with hn_def
  set C : NNReal := Tube.card_le_of_densityIn_le.C n with hC_def
  have hC_pos : 0 < (C : ℝ) + 1 := by positivity
  have h_abs : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, (C : ENNReal) ≤ (δ : ENNReal) ^ (-(1 / 2) : ℝ) := by
    have h_abs_real : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), (C : ℝ) + 1 ≤ δ ^ (-(1 / 2) : ℝ) :=
      absorb_const_le_rpow_neg (C := (C : ℝ) + 1) (η := 1 / 2) hC_pos (by norm_num)
    have h_abs_nn : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), (C : ℝ) + 1 ≤ (δ : ℝ) ^ (-(1 / 2) : ℝ) :=
      nnreal_eventually_of_real_eventually h_abs_real
    filter_upwards [h_abs_nn, self_mem_nhdsWithin] with δ h_le hδ_pos
    rw [← ENNReal.ofReal_coe_nnreal,
      ennreal_coe_nnreal_rpow (by exact_mod_cast hδ_pos) (-(1 / 2) : ℝ)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  filter_upwards [h_abs, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hC_le hδ01
  obtain ⟨hδ0, hδ1⟩ := hδ01
  intro ι s T hball hKT
  have hη_le : (δ : ENNReal) ^ (-η) ≤ (δ : ENNReal) ^ (-(1 / 2) : ℝ) := by
    exact ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1.le) (by linarith)
  have hδ_ne : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδ_ne_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc
    (s.card : ENNReal) ≤ (C : ENNReal) * (δ : ENNReal) ^ (-η) *
        (δ : ENNReal) ^ (-((n : ℝ) - 1)) := by
      convert Tube.card_le_of_densityIn_le (δ := δ) (T := fun i ↦ (T i).toTube)
        (by exact_mod_cast hδ0.ne') hball
        ((le_maxDensity s _ _).trans hKT) using 2
      rw [show (-((n : ℝ) - 1) : ℝ) = ((-(((n : ℕ) : ℤ) - 1) : ℤ) : ℝ) from by
        push_cast; ring, ENNReal.rpow_intCast]
    _ ≤ (δ : ENNReal) ^ (-(1 / 2) : ℝ) * (δ : ENNReal) ^ (-(1 / 2) : ℝ) *
        (δ : ENNReal) ^ (-((n : ℝ) - 1)) := by
      gcongr
    _ = (δ : ENNReal) ^ (-3 : ℝ) := by
      rw [← ENNReal.rpow_add (-(1 / 2) : ℝ) (-(1 / 2) : ℝ) hδ_ne hδ_ne_top]
      rw [← ENNReal.rpow_add (-(1 / 2) + -(1 / 2) : ℝ) (-((n : ℝ) - 1)) hδ_ne hδ_ne_top]
      rw [hn]
      norm_num

/-- **The `ω`-to-`β` trade** (Wang-Zahl, the sentence after Proposition 1.7).  A gain of `g`
in the budget buys a drop of `g/3` in the cardinality exponent, at no cost in accuracy,
because `|𝕋| ≤ δ ^ (-3)`.

The divisor is `3` and not Wang-Zahl's `4` because the development's packing bound is
`|𝕋| ≤ δ ^ (-3)` in `ℝ³`; see `Kakeya.eventually_card_le_rpow_neg_three`. -/
theorem KatzTaoEstimateOmega.trade (hn : Module.finrank ℝ E = 3) {β ω g : ℝ} (hg : 0 ≤ g)
    (h : KatzTaoEstimateOmega.{u} E β (ω - g)) :
    KatzTaoEstimateOmega.{u} E (β - g / 3) ω := by
  intro ε hε
  rcases small_eta h hε (show (0 : ℝ) < 1 / 2 by norm_num) with ⟨η, hηpos, hηle, hev⟩
  refine ⟨η, hηpos, ?_⟩
  filter_upwards [hev, eventually_card_le_rpow_neg_three hn hηpos.le hηle,
    Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hevδ hcardδ ⟨hδ0, hδ1⟩
  intro ι s T hball hKT hfull
  by_cases hcard : s.card = 0
  · have hs : s = ∅ := Finset.card_eq_zero.mp hcard
    subst hs
    simp
  · have hcard0 : (s.card : ENNReal) ≠ 0 := by
      exact_mod_cast hcard
    have hcardtop : (s.card : ENNReal) ≠ ⊤ := by
      exact ENNReal.natCast_ne_top s.card
    have hδ0ne : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδ0)
    have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hg3 : 0 ≤ g / 3 := by positivity
    have hpow_card_g : (s.card : ENNReal) ^ (g / 3) ≤ (δ : ENNReal) ^ (-g) := by
      calc
        (s.card : ENNReal) ^ (g / 3) ≤ ((δ : ENNReal) ^ (-3 : ℝ)) ^ (g / 3) := by
          exact ENNReal.rpow_le_rpow (hcardδ s T hball hKT) hg3
        _ = (δ : ENNReal) ^ (-g) := by
          rw [← ENNReal.rpow_mul (δ : ENNReal) (-3 : ℝ) (g / 3)]
          congr 1
          ring
    have hpow_card :
        (s.card : ENNReal) ^ β ≤ (δ : ENNReal) ^ (-g) * (s.card : ENNReal) ^ (β - g / 3) := by
      calc
        (s.card : ENNReal) ^ β =
            (s.card : ENNReal) ^ (β - g / 3) * (s.card : ENNReal) ^ (g / 3) := by
          rw [← ENNReal.rpow_add (β - g / 3) (g / 3) hcard0 hcardtop]
          congr 1
          ring
        _ ≤ (s.card : ENNReal) ^ (β - g / 3) * (δ : ENNReal) ^ (-g) := by
          gcongr
        _ = (δ : ENNReal) ^ (-g) * (s.card : ENNReal) ^ (β - g / 3) := by
          rw [mul_comm]
    have hpow_delta :
        (δ : ENNReal) ^ (-(ω - g) - ε) * (δ : ENNReal) ^ (-g) = (δ : ENNReal) ^ (-ω - ε) := by
      rw [← ENNReal.rpow_add (-(ω - g) - ε) (-g) hδ0ne hδtop]
      congr 1
      ring
    calc
      ∑ i ∈ s, volume (T i).shade
          ≤ δ ^ (-(ω - g) - ε) * s.card ^ β * volume (⋃ i ∈ s, (T i).shade) :=
            hevδ s T hball hKT hfull
      _ ≤ δ ^ (-(ω - g) - ε) * (δ ^ (-g) * s.card ^ (β - g / 3)) *
            volume (⋃ i ∈ s, (T i).shade) := by
        gcongr
      _ = δ ^ (-ω - ε) * s.card ^ (β - g / 3) * volume (⋃ i ∈ s, (T i).shade) := by
        rw [← mul_assoc, hpow_delta]

/-- **Closedness in `β` at fixed budget.**  If `K_KT(β', ω)` holds for every `β' > β`, then
`K_KT(β, ω)` holds: given the accuracy `ε`, apply the hypothesis at `β' = β + ε/6` and
accuracy `ε/2`, and pay the difference out of `|𝕋| ≤ δ ^ (-3)`. -/
theorem KatzTaoEstimateOmega.of_forall_gt_beta (hn : Module.finrank ℝ E = 3) {β ω : ℝ}
    (h : ∀ β' > β, KatzTaoEstimateOmega.{u} E β' ω) : KatzTaoEstimateOmega.{u} E β ω := by
  intro ε hε
  have hβ' : KatzTaoEstimateOmega.{u} E (β + ε / 6) ω := h (β + ε / 6) (by linarith)
  rcases KatzTaoEstimateOmega.small_eta hβ' (by positivity : 0 < ε / 2)
      (by norm_num : 0 < (1 / 2 : ℝ)) with ⟨η, hηpos, hηle, hev⟩
  refine ⟨η, hηpos, ?_⟩
  filter_upwards [hev, eventually_card_le_rpow_neg_three (E := E) hn hηpos.le hηle,
    Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hevδ hcardδ hδ01
  obtain ⟨hδ0, hδ1⟩ := hδ01
  intro ι s T hball hKT hfull
  by_cases hcard0 : s.card = 0
  · have hs : s = ∅ := Finset.card_eq_zero.mp hcard0
    subst hs
    simp
  · have hcard_ne0 : (s.card : ENNReal) ≠ 0 := by exact_mod_cast hcard0
    have hcard_ne_top : (s.card : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hδ_ne0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
    have hδ_ne_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hstep : (s.card : ENNReal) ^ (ε / 6) ≤ (δ : ENNReal) ^ (-ε / 2) := by
      calc
        (s.card : ENNReal) ^ (ε / 6) ≤ ((δ : ENNReal) ^ (-3 : ℝ)) ^ (ε / 6) := by
          exact ENNReal.rpow_le_rpow (hcardδ s T hball hKT) (by positivity : 0 ≤ ε / 6)
        _ = (δ : ENNReal) ^ ((-3 : ℝ) * (ε / 6)) := by
          rw [← ENNReal.rpow_mul (δ : ENNReal) (-3 : ℝ) (ε / 6)]
        _ = (δ : ENNReal) ^ (-ε / 2) := by
          congr 1
          ring
    calc
      ∑ i ∈ s, volume (T i).shade
          ≤ δ ^ (-ω - ε / 2) * (s.card : ENNReal) ^ (β + ε / 6) * volume (⋃ i ∈ s, (T i).shade) :=
            hevδ s T hball hKT hfull
      _ = δ ^ (-ω - ε / 2) * ((s.card : ENNReal) ^ β * (s.card : ENNReal) ^ (ε / 6))
            * volume (⋃ i ∈ s, (T i).shade) := by
            rw [ENNReal.rpow_add β (ε / 6) hcard_ne0 hcard_ne_top]
      _ ≤ δ ^ (-ω - ε / 2) * ((s.card : ENNReal) ^ β * (δ : ENNReal) ^ (-ε / 2))
            * volume (⋃ i ∈ s, (T i).shade) := by
            gcongr
      _ = δ ^ (-ω - ε / 2) * (δ : ENNReal) ^ (-ε / 2) * (s.card : ENNReal) ^ β
            * volume (⋃ i ∈ s, (T i).shade) := by
            ring
      _ = δ ^ (-ω - ε) * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade) := by
            rw [← ENNReal.rpow_add (-ω - ε / 2) (-ε / 2) hδ_ne0 hδ_ne_top]
            rw [show (-ω - ε / 2) + (-ε / 2) = -ω - ε by ring]

/-- Closedness in `β` in sequence form: if `b k → β` and `K_KT(b k, ω)` holds for every `k`,
then `K_KT(β, ω)` holds.  Monotonicity of `b` is not needed. -/
theorem KatzTaoEstimateOmega.of_tendsto (hn : Module.finrank ℝ E = 3) {β ω : ℝ} {b : ℕ → ℝ}
    (hb : Filter.Tendsto b Filter.atTop (𝓝 β))
    (h : ∀ k, KatzTaoEstimateOmega.{u} E (b k) ω) : KatzTaoEstimateOmega.{u} E β ω := by
  refine KatzTaoEstimateOmega.of_forall_gt_beta hn ?_
  intro β' hβ'
  rcases (hb.eventually (eventually_lt_nhds hβ')).exists with ⟨k, hk⟩
  exact KatzTaoEstimateOmega.mono hk.le (h k)

end Packing

section MultiplicityBound

variable
  {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- For any divisor `c > 0` and exponent `η > 0`, eventually
`exp(-δ^(-η)/c) ≤ 1/5` as `δ → 0⁺`. -/
private lemma absorb_exp_le_div_five {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), Real.exp (-δ ^ (-η) / c) ≤ 1/5 := by
  filter_upwards [absorb_const_le_rpow_neg
    (mul_pos hc (Real.log_pos (by norm_num : (1 : ℝ) < 5))) hη] with δ hδ
  rw [show (-δ ^ (-η) / c : ℝ) = -(δ ^ (-η) / c) from by ring]
  refine (Real.exp_le_exp.mpr (show -(δ ^ (-η) / c) ≤ -Real.log 5 by
    rw [neg_le_neg_iff, le_div_iff₀ hc]; linarith)).trans ?_
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  norm_num

/-- Eventually `2^β ≤ δ^(-ε)` as `δ → 0⁺`, for any `β : ℝ` and `ε > 0`. -/
private lemma absorb_two_rpow_le_rpow_neg (β : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), (2 : ℝ) ^ β ≤ δ ^ (-ε) :=
  absorb_const_le_rpow_neg (Real.rpow_pos_of_pos two_pos β) hε

/-- Eventually `4 * K^4 ≤ δ^(-η)` as `δ → 0⁺`, for `K, η > 0`. -/
private lemma absorb_four_K4_le_rpow_neg {K η : ℝ} (_hK : 0 < K) (hη : 0 < η) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), 4 * K ^ 4 ≤ δ ^ (-η) :=
  absorb_const_le_rpow_neg (by positivity) hη

/-- Eventually `exp(-δ^(η/2 - 2η/2) / (8K^2)) ≤ 1/5` as `δ → 0⁺`. -/
private lemma absorb_exp_K_le_div_five {K η : ℝ} (_hK : 0 < K) (hη : 0 < η) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ),
      Real.exp (-δ ^ (η / 2 - 2 * η / 2) / (8 * K ^ 2)) ≤ 1/5 := by
  filter_upwards [absorb_exp_le_div_five (by positivity : (0 : ℝ) < 8 * K^2)
    (half_pos hη)] with δ hδ
  rwa [show (η / 2 - 2 * η / 2 : ℝ) = -(η / 2) from by ring]

/-- Eventually `δ ≤ 1/5` as `δ → 0⁺`. -/
private lemma absorb_delta_le_div_five :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), δ ≤ 1/5 := by
  apply Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1/5))
  intro δ hδ
  simp only [Set.mem_Ioo] at hδ
  linarith [hδ.2]

/-- The lower volume bound for a `δ`-tube, in `ℝ`-valued (`volume.real`) form.
TODO: remove use of volume.real
-/
private lemma tube_le_volume_real {δ : NNReal} (T : ShadedTube δ E) :
    (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤
      volume.real T.carrier := by
  have hreal := ENNReal.toReal_mono T.isCompact'.measure_lt_top.ne (Tube.le_volume T.toTube)
  simpa [MeasureTheory.Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.coe_toReal] using hreal

/-- **The ω-form of [GWZ, Lemma 3.7]**: `K_KT(β, ω)` implies a multiplicity bound for families of
`δ`-tubes at any value of `Δ_max(𝕋)`.

This is `Kakeya.KatzTaoEstimate.multiplicity_bound` verbatim with the accuracy factor `δ^{-ε}` of
the conclusion replaced by `δ^{-ω-ε}`, and it is proved by that lemma's proof with the same
replacement.  The budget rides through the passage to a random subfamily
(`Kakeya.exists_random_subset`) as a scalar and changes no step of it: the assertion is read at
accuracy `ε/4`, returning `δ^{-ω-ε/4}` in place of `δ^{-ε/4}`, and the three subsequent absorptions
— the factor `2^β`, the refinement loss `δ^{-2η_K}` and the density factor — are each free of `ω`.
The final exponent comparison is `2η_K + ω + ε/2 ≤ ω + ε`, in which `ω` cancels, so it is the same
comparison `2η_K ≤ ε/2` that the `ω = 0` proof makes; in particular no sign hypothesis on `ω` is
needed.

The scale charged is the single scale `δ`, the family's own thickness.  Charging it elsewhere is
what `note:ml2redOmegaFailureMode` prices; the own-scale discipline of the window branch is arranged
by the consumers in `Kakeya/DimensionThree/MainLemma2/Reduction/OmegaInputs.lean`, which read this
lemma at the leaf scale rather than at the configuration scale. -/
theorem KatzTaoEstimateOmega.multiplicity_bound {β ω : ℝ} (hβ_0 : 0 ≤ β)
    (h : KatzTaoEstimateOmega.{u} E β ω) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
        (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (δ : ℝ) ^ η →
        multiplicity s (fun i ↦ (T i).toShadedBody) ≤
          (δ : ENNReal) ^ (-ω - ε) *
            (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
            (s.card : ENNReal) ^ β := by
  intro ε hε
  obtain ⟨η1, hη1_pos, hKKT⟩ := h (ε / 4) (by linarith)
  set η_K := min (η1 / 2) (ε / 8) with hη_K_def
  have hη_K_pos : 0 < η_K := lt_min (half_pos hη1_pos) (by linarith)
  refine ⟨η_K / 2, half_pos hη_K_pos, ?_⟩
  set c_low : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hc_low_def
  have hc_low_pos : 0 < c_low := NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  set c_up : ℝ := (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) with hc_up_def
  set K_unif : ℝ := c_up / c_low with hK_unif_def
  have hK_unif_pos : 0 < K_unif := div_pos (NNReal.coe_pos.mpr (Tube.volume_le.C_pos _)) hc_low_pos
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  -- Density test family constants: the discretization constants of
  -- `exists_localized_finite_test_family_maxDensity` at radius `R = 1`. The exponent is padded by
  -- `+1` so that the multiplicative constant `Ctest` can be absorbed into `δ ^ (-Mtest)` for
  -- small `δ` (the `hδ_lt_invCtest` conjunct below).
  set Ctest : ℝ := (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ)
    with hCtest_def
  set Mtest : ℝ := exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) + 1
    with hMtest_def
  have hCtest_pos : 0 < Ctest :=
    NNReal.coe_pos.mpr (exists_volume_bounded_prism_discretization.C_pos _)
  have hMtest_pos : 0 < Mtest := by
    rw [hMtest_def]
    linarith [exists_volume_bounded_prism_discretization.M_pos (Module.finrank ℝ E)]
  filter_upwards [hKKT,
      (nnreal_eventually_of_real_eventually (p := fun δ => δ < 1)
        (nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one))),
      (nnreal_eventually_of_real_eventually (p := fun δ => 0 < δ)
        (self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ)),
      nnreal_eventually_of_real_eventually
        (absorb_two_rpow_le_rpow_neg β (ε := ε / 4) (by linarith)),
      nnreal_eventually_of_real_eventually
        (absorb_four_K4_le_rpow_neg (K := K_unif) (η := η_K / 2) hK_unif_pos (half_pos hη_K_pos)),
      nnreal_eventually_of_real_eventually
        (absorb_log_le_rpow_neg (C := Ctest) (M := 8 * Mtest + 8) (η := η_K)
          hCtest_pos (by linarith) hη_K_pos),
      nnreal_eventually_of_real_eventually
        (absorb_exp_K_le_div_five (K := K_unif) (η := η_K) hK_unif_pos hη_K_pos),
      nnreal_eventually_of_real_eventually absorb_delta_le_div_five,
      nnreal_eventually_of_real_eventually (p := fun δ => δ < 1 / Ctest)
        (nhdsWithin_le_nhds (Iio_mem_nhds (one_div_pos.mpr hCtest_pos)))]
    with δNN hδ_KKT hδ_lt_one hδ_pos h_2β_le hδ_small_K hδ_small_b
         hδ5_c hδ5_b hδ_lt_invCtest
  set δ : ℝ := (δNN : ℝ) with hδ_def
  have hδNN_pos : (0 : NNReal) < δNN := by exact_mod_cast hδ_pos
  intro ι s T hB hfull
  set W := fun i ↦ (T i).toConvexSpaceBody with hW
  set V := fun i ↦ (T i).toShadedBody with hV
  set Δ : ℝ := (maxDensity s W).toReal with hΔ_def
  have hT_vol_lb_real : ∀ i,
      c_low * δ ^ (Module.finrank ℝ E - 1) ≤ volume.real (T i).carrier :=
    fun i => tube_le_volume_real (T i)
  rcases eq_or_ne s ∅ with rfl | hs
  · simp only [ShadedBody.multiplicity_empty]
    exact bot_le
  · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hvol_pos : 0 < volume (W i₀).carrier :=
      (ENNReal.toReal_pos_iff.mp (lt_of_lt_of_le
        (mul_pos hc_low_pos (pow_pos hδ_pos _)) (hT_vol_lb_real i₀))).1
    have hΔ_pos : 0 < Δ :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (one_le_maxDensity ⟨i₀, hi₀, hvol_pos⟩)).ne'
        (maxDensity_ne_top s W)
    have hT_unif : ∀ i ∈ s, ∀ j ∈ s,
        volume.real (T i).carrier ≤ K_unif * volume.real (T j).carrier := fun i _ j _ =>
      calc volume.real (T i).carrier
          ≤ c_up * δ ^ (Module.finrank ℝ E - 1) :=
            by
              have hRHS_fin :
                  (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
                      (δNN : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ :=
                ENNReal.mul_ne_top ENNReal.coe_ne_top
                  (ENNReal.pow_ne_top ENNReal.coe_ne_top)
              have hreal := ENNReal.toReal_mono hRHS_fin
                (Tube.volume_le (by exact_mod_cast hδ_lt_one.le) (T i).toTube)
              simpa [MeasureTheory.Measure.real, hc_up_def, hδ_def,
                ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal] using hreal
        _ = K_unif * (c_low * δ ^ (Module.finrank ℝ E - 1)) := by
              rw [hK_unif_def, ← mul_assoc, div_mul_cancel₀ _ hc_low_pos.ne']
        _ ≤ K_unif * volume.real (T j).carrier :=
              mul_le_mul_of_nonneg_left (hT_vol_lb_real j) hK_unif_pos.le
    have htest_real : ∃ KTest : Finset (ConvexSpaceBody E),
        (∀ K ∈ KTest, K ≤ ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))) ∧
        (KTest.card : ℝ) ≤ (δ : ℝ) ^ (-Mtest) ∧ ∀ u : Finset ι, u ⊆ s →
        ∃ K ∈ KTest, (maxDensity u (fun i ↦ (T i).toConvexSpaceBody)).toReal ≤
        Ctest * (densityIn u (fun i ↦ (T i).toConvexSpaceBody) K).toReal := by
      obtain ⟨KTest, hKT_sub, hKT_card, hKT_test⟩ :=
        exists_localized_finite_test_family_maxDensity.{u, _} (E := E) (r := δNN) (R := 1)
          hδNN_pos (by exact_mod_cast hδ_lt_one.le) le_rfl
      refine ⟨KTest, ?_, ?_, fun u _hu => ?_⟩
      · -- The test bodies sit in `B(0,1)`, hence a fortiori in its unit thickening.
        intro K hK x hx
        exact Metric.self_subset_cthickening _
          (by simpa only [NNReal.coe_one, ConvexSpaceBody.closedUnitBall_carrier]
            using hKT_sub K hK hx)
      · -- Absorb the multiplicative constant `Ctest` into the padded exponent `Mtest = M + 1`.
        set M : ℝ := exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) with hM_def
        have hcard_real : (KTest.card : ℝ) ≤ Ctest * δ ^ (-M) := by
          rw [NNReal.one_rpow, mul_one] at hKT_card
          rw [hCtest_def, hδ_def]
          exact_mod_cast hKT_card
        have hCtest_le : Ctest ≤ δ ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one, inv_eq_one_div, le_div_iff₀ hδ_pos]
          calc Ctest * δ = δ * Ctest := mul_comm _ _
            _ ≤ 1 := ((lt_div_iff₀ hCtest_pos).mp hδ_lt_invCtest).le
        have hsplit : δ ^ (-Mtest) = δ ^ (-M) * δ ^ (-1 : ℝ) := by
          rw [← Real.rpow_add hδ_pos, hMtest_def]
          congr 1
          ring
        calc (KTest.card : ℝ) ≤ Ctest * δ ^ (-M) := hcard_real
          _ ≤ δ ^ (-1 : ℝ) * δ ^ (-M) :=
              mul_le_mul_of_nonneg_right hCtest_le (Real.rpow_nonneg hδ_pos.le _)
          _ = δ ^ (-M) * δ ^ (-1 : ℝ) := mul_comm _ _
          _ = δ ^ (-Mtest) := hsplit.symm
      · obtain ⟨K, hK_mem, hK_le⟩ :=
          hKT_test u (fun i ↦ (T i).toConvexSpaceBody)
            (fun i _ => by simpa only [NNReal.coe_one] using hB i)
            (fun i _ => by
              rw [Metric.ethickness.scale_eq]
              exact (T i).toTube.le_ethickness_finrank_sub_one)
        refine ⟨K, hK_mem, ?_⟩
        have h_ennr := ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.coe_ne_top (densityIn_ne_top _ _ _)) hK_le
        rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, ← hCtest_def] at h_ennr
    obtain ⟨s', hs'_sub, hs'_ne, hs'_card_ub, hs'_KT, hs'_full, hs'_mu⟩ :=
        exists_random_subset E (η₁ := η_K / 2) (c := 2 * η_K) (half_pos hη_K_pos)
          (by linarith) s T hB (Finset.nonempty_iff_ne_empty.mpr hs) hδ_pos
          K_unif hK_unif_pos hT_unif hδ_small_K
          Mtest Ctest hMtest_pos hCtest_pos htest_real
          hδ_small_b hδ5_c hδ5_b hfull
    have hηK_le_half : η_K ≤ η1 / 2 := min_le_left _ _
    have hs'_KT' : IsKatzTao s' W ((δNN : ENNReal) ^ (-η1)) :=
      hs'_KT.mono <| by
        rw [ennreal_coe_nnreal_rpow hδ_pos]
        exact ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le (by linarith))
    have hs'_full' : (δNN : NNReal) ^ η1 ≤ ShadedBody.fullness s' V := by
      rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
      calc (δ : ℝ) ^ η1
          ≤ (δ : ℝ) ^ η_K := Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le
            (by linarith [hη_K_pos])
        _ = (δ : ℝ) ^ (2 * (η_K / 2)) := by congr 1; ring
        _ ≤ _ := hs'_full
    -- ENNReal multiplicity bound for `s'`, obtained from `hδ_KKT`.
    have hmu_s'_le_enn : ShadedBody.multiplicity s' V ≤
        (δNN : ENNReal) ^ (-ω - ε / 4) * (s'.card : ENNReal) ^ β := by
      rw [ShadedBody.multiplicity_le_iff, mul_assoc]
      have : ∀ i ∈ s', (T i).carrier ⊆ Metric.closedBall 0 1 := fun i hi => hB i
      exact (hδ_KKT s' T this hs'_KT' hs'_full').trans_eq (mul_assoc _ _ _)
    -- The ℝ-valued multiplicity bound for `s'` (derived by `.toReal`).
    have h_mu_s'_R_le : multiplicityRLocal E s' V ≤
        δ ^ (-ω - ε / 4) * (s'.card : ℝ) ^ β := by
      have h_top : (δNN : ENNReal) ^ (-ω - ε / 4) * (s'.card : ENNReal) ^ β ≠ ⊤ :=
        ENNReal.mul_ne_top (by rw [ennreal_coe_nnreal_rpow hδ_pos]; exact ENNReal.ofReal_ne_top)
          (ENNReal.rpow_ne_top_of_nonneg hβ_0 (ENNReal.natCast_ne_top _))
      simpa [multiplicityRLocal, ENNReal.toReal_mul, ennreal_coe_nnreal_rpow_toReal hδ_pos,
        ← ENNReal.toReal_rpow] using ENNReal.toReal_mono h_top hmu_s'_le_enn
    have h_mu_s_R_le : multiplicityRLocal E s V ≤
        δ ^ (-ω - ε) * Δ ^ (1 - β) * (s.card : ℝ) ^ β := by
      calc multiplicityRLocal E s V
        _ ≤ δ ^ (-(2 * η_K)) * Δ * multiplicityRLocal E s' V := hs'_mu
        _ ≤ δ ^ (-(2 * η_K)) * Δ * (δ ^ (-ω - ε / 4) * (s'.card : ℝ) ^ β) :=
              mul_le_mul_of_nonneg_left
                h_mu_s'_R_le
                (mul_nonneg (Real.rpow_nonneg hδ_pos.le _) ENNReal.toReal_nonneg)
        _ ≤ δ ^ (-(2 * η_K)) * Δ * (δ ^ (-ω - ε / 4) * (2 * (s.card : ℝ) * Δ⁻¹) ^ β) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (Nat.cast_nonneg _) hs'_card_ub hβ_0)
                (Real.rpow_nonneg hδ_pos.le _))
              (mul_nonneg (Real.rpow_nonneg hδ_pos.le _) ENNReal.toReal_nonneg)
        _ ≤ δ ^ (-(2 * η_K)) * Δ * (δ ^ (-ω - ε / 2) * ((s.card : ℝ) * Δ⁻¹) ^ β) := by
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.rpow_nonneg hδ_pos.le _)
                ENNReal.toReal_nonneg)
              rw [show (2 : ℝ) * s.card * Δ⁻¹ = (2 : ℝ) * (s.card * Δ⁻¹) from by ring,
                  Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2)
                (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr ENNReal.toReal_nonneg)),
                show δ ^ (-ω - ε / 4) * ((2 : ℝ) ^ β * (s.card * Δ⁻¹) ^ β)
                  = (δ ^ (-ω - ε / 4) * (2 : ℝ) ^ β) * (s.card * Δ⁻¹) ^ β from by ring]
              exact mul_le_mul_of_nonneg_right
                (calc δ ^ (-ω - ε / 4) * (2 : ℝ) ^ β
                    ≤ δ ^ (-ω - ε / 4) * δ ^ (-(ε / 4)) :=
                      mul_le_mul_of_nonneg_left h_2β_le (Real.rpow_nonneg hδ_pos.le _)
                  _ = δ ^ (-ω - ε / 2) := by rw [← Real.rpow_add hδ_pos]; congr 1; ring)
                (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _)
                  (inv_nonneg.mpr ENNReal.toReal_nonneg)) _)
        _ = δ ^ (-(2 * η_K + ω + ε / 2)) * Δ ^ (1 - β) * (s.card : ℝ) ^ β := by
              rw [Real.mul_rpow (Nat.cast_nonneg _) (inv_nonneg.mpr ENNReal.toReal_nonneg),
              show (Δ⁻¹ : ℝ) ^ β = Δ ^ (-β) from by rw [Real.inv_rpow ENNReal.toReal_nonneg,
                  ← Real.rpow_neg ENNReal.toReal_nonneg],
              show δ ^ (-(2 * η_K)) * Δ * (δ ^ (-ω - ε / 2) * ((s.card) ^ β * Δ ^ (-β)))
                      = (δ ^ (-(2 * η_K)) * δ ^ (-ω - ε / 2)) * (Δ * Δ ^ (-β)) * (s.card) ^ β
                      from by ring,
               ← Real.rpow_add hδ_pos,
               show -(2 * η_K) + (-ω - ε / 2) = -(2 * η_K + ω + ε / 2) from by ring,
              show Δ * Δ ^ (-β) = Δ ^ (1 : ℝ) * Δ ^ (-β) from by rw [Real.rpow_one],
                ← Real.rpow_add hΔ_pos, show (1 : ℝ) + -β = 1 - β from by ring]
        _ ≤ δ ^ (-ω - ε) * Δ ^ (1 - β) * (s.card : ℝ) ^ β := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ENNReal.toReal_nonneg _)
              exact Real.rpow_le_rpow_of_exponent_ge hδ_pos (le_of_lt hδ_lt_one)
                (by linarith [min_le_right (η1 / 2) (ε / 8)])
    -- Lift the real-valued bound to ENNReal and match the goal.
    have h_mu_ne_top : ShadedBody.multiplicity s V ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (ShadedBody.multiplicity_le_card s V)
    refine ((ENNReal.le_ofReal_iff_toReal_le h_mu_ne_top
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hδ_pos.le _)
        (Real.rpow_nonneg ENNReal.toReal_nonneg _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))).2 h_mu_s_R_le).trans ?_
    have h_card_eq : ENNReal.ofReal ((s.card : ℝ) ^ β) = (s.card : ENNReal) ^ β := by
      rw [show ((s.card : ℝ) ^ β : ℝ) = ((s.card : ENNReal) ^ β).toReal from by
            rw [← ENNReal.toReal_rpow]; simp,
          ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg hβ_0 (ENNReal.natCast_ne_top _))]
    rw [show (δ ^ (-ω - ε) * Δ ^ (1 - β) * (s.card : ℝ) ^ β : ℝ)
          = δ ^ (-ω - ε) * (Δ ^ (1 - β) * (s.card : ℝ) ^ β) from by ring,
        ENNReal.ofReal_mul (Real.rpow_nonneg hδ_pos.le _),
        ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _),
        ← ennreal_coe_nnreal_rpow hδ_pos,
        show ENNReal.ofReal (Δ ^ (1 - β)) = (maxDensity s W) ^ (1 - β) from by
          rw [← ENNReal.ofReal_rpow_of_pos hΔ_pos, hΔ_def,
              ENNReal.ofReal_toReal (maxDensity_ne_top s W)],
        h_card_eq, mul_assoc]

end MultiplicityBound

section Bootstrap

/-- **The two-parameter descent.**  At each fixed budget `ω`, a two-parameter predicate `S`
that is up-closed in its first argument, holds at `1`, and is closed under
`γ ↦ γ - ν γ ω` on `(0, 1]` for a `ν (·) ω` that is monotone and strictly positive there,
holds on all of `(0, 1]`.

This is the existing single-parameter `Kakeya.ioc_subset_of_sub_mem_of_monotoneOn` read at
the fixed `ω`: no new engine is needed.  In particular the argument is an infimum argument
and not an iteration, so it needs **no** lower bound on `ν (·) ω` over `(0, 1]`; the step may
tend to `0` as `γ ↓ 0` without harming the conclusion. -/
theorem ioc_subset_of_sub_mem_of_monotoneOn_param {S : ℝ → ℝ → Prop} {ν : ℝ → ℝ → ℝ} {ω : ℝ}
    (h1 : ∀ γ γ', γ ≤ γ' → S γ ω → S γ' ω)
    (h2 : S 1 ω)
    (h3 : ∀ γ ∈ Set.Ioc (0 : ℝ) 1, S γ ω → S (γ - ν γ ω) ω)
    (h4 : MonotoneOn (fun γ ↦ ν γ ω) (Set.Ioc (0 : ℝ) 1))
    (h5 : ∀ γ ∈ Set.Ioc (0 : ℝ) 1, 0 < ν γ ω) :
    ∀ γ ∈ Set.Ioc (0 : ℝ) 1, S γ ω := by
  intro γ hγ
  exact ioc_subset_of_sub_mem_of_monotoneOn (s := {γ | S γ ω}) (f := fun γ ↦ ν γ ω)
    h1 h2 h3 h4 h5 hγ

end Bootstrap

section Assembly

/-- **The outer scheme delivers.**  Given a two-parameter Main Lemma 2 in the shape of
Wang-Zahl Proposition 1.7 — a drop `g` produced before any accuracy, positive and monotone in
`β` at each fixed `ω > 0`, taking `K_KT(β, ω)` and `K_F(β, ω)` to `K_KT(β, ω - g β ω)` — and
a two-parameter Main Lemma 1 in the development's non-sharp shape, the one-parameter
`K_KT(β)` follows for every `β ∈ (0, 1]`.

The route is: fix `ω > 0`; run the descent `Kakeya.ioc_subset_of_sub_mem_of_monotoneOn_param` at
that `ω` with step `g (·) ω / 6`, whose self-improvement step is the two-parameter Main
Lemma 2 followed by the trade `Kakeya.KatzTaoEstimateOmega.trade`; the base point `γ = 1` is
`Kakeya.KatzTao_one` and `Kakeya.frostmanEstimate_one` pushed up by
`Kakeya.KatzTaoEstimate.toOmega` and `Kakeya.FrostmanEstimate.toOmega`; then remove the
budget by `Kakeya.katzTaoEstimate_iff_forall_omega_pos`, whose backward direction is the
absorption `Kakeya.KatzTaoEstimateOmega.of_forall_gt`.

The halving of the step to `g (·) ω / 6` pays, exactly as in
`Kakeya.katzTaoEstimateDimensionThree`, for the non-sharpness of Main Lemma 1.

Which properties of `g` are consumed: positivity on `(0, 1] × (0, ∞)`, and monotonicity in
`β` at fixed `ω`.  Notably the Wang-Zahl side condition `g β ω ≤ ω / 2` is **not** consumed:
the trade tolerates a negative residual budget, since `K_KT(β, ω')` for `ω' ≤ 0` is merely a
stronger statement.  It is therefore omitted from the hypotheses. -/
theorem katzTaoEstimate_of_mainLemma2Omega
    (g : ℝ → ℝ → ℝ)
    (hg_pos : ∀ β ω : ℝ, 0 < β → β ≤ 1 → 0 < ω → 0 < g β ω)
    (hg_mono : ∀ ω : ℝ, 0 < ω → MonotoneOn (fun β ↦ g β ω) (Set.Ioc (0 : ℝ) 1))
    (hML2 : ∀ β ω : ℝ, 0 < β → β ≤ 1 → 0 < ω →
      KatzTaoEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) β ω →
      FrostmanEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) β ω →
      KatzTaoEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) β (ω - g β ω))
    (hML1 : ∀ β γ ω : ℝ, 0 ≤ β → β < γ → γ ≤ 1 → 0 < ω →
      KatzTaoEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) β ω →
      FrostmanEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) γ ω)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β := by
  rw [katzTaoEstimate_iff_forall_omega_pos]
  intro ω hω
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  set S : ℝ → ℝ → Prop := fun γ ω ↦ KatzTaoEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) γ ω
  set ν : ℝ → ℝ → ℝ := fun γ ω ↦ g γ ω / 6
  have h1 : ∀ γ γ', γ ≤ γ' → S γ ω → S γ' ω := by
    intro γ γ' hle hS
    exact KatzTaoEstimateOmega.mono hle hS
  have h2 : S 1 ω := by
    dsimp [S]
    exact KatzTaoEstimate.toOmega hω.le KatzTao_one
  have h3 : ∀ γ ∈ Set.Ioc (0 : ℝ) 1, S γ ω → S (γ - ν γ ω) ω := by
    intro γ hγ hS
    dsimp [ν]
    have hγ_pos : 0 < γ := hγ.1
    have hγ_le_one : γ ≤ 1 := hγ.2
    by_cases hγ_eq_one : γ = 1
    · subst hγ_eq_one
      dsimp [S] at hS ⊢
      have hF : FrostmanEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) 1 ω :=
        FrostmanEstimate.toOmega hω.le frostmanEstimate_one
      have hKT_sub : KatzTaoEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) 1 (ω - g 1 ω) :=
        hML2 1 ω (by norm_num) (by norm_num) hω hS hF
      have hKT_traded : KatzTaoEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) (1 - g 1 ω / 3) ω :=
        KatzTaoEstimateOmega.trade hn (hg_pos 1 ω (by norm_num) (by norm_num) hω).le hKT_sub
      have h_ineq : 1 - g 1 ω / 3 ≤ 1 - g 1 ω / 6 := by
        have hg1_pos : 0 < g 1 ω := hg_pos 1 ω (by norm_num) (by norm_num) hω
        nlinarith
      exact KatzTaoEstimateOmega.mono h_ineq hKT_traded
    · have hγ_lt_one : γ < 1 := lt_of_le_of_ne hγ_le_one hγ_eq_one
      set γ' := min 1 (γ + g γ ω / 6) with hγ'_def
      have hγ'_pos : 0 < γ' := by
        refine lt_min_iff.mpr ?_
        constructor
        · norm_num
        · nlinarith [hg_pos γ ω hγ_pos hγ_le_one hω]
      have hγ'_le_one : γ' ≤ 1 := min_le_left _ _
      have hγ_lt_γ' : γ < γ' := by
        have h_lt : γ < γ + g γ ω / 6 := by
          have hgγ_pos : 0 < g γ ω := hg_pos γ ω hγ_pos hγ_le_one hω
          nlinarith
        refine lt_min_iff.mpr ⟨hγ_lt_one, h_lt⟩
      have hγ_le_γ' : γ ≤ γ' := le_of_lt hγ_lt_γ'
      have hγ'_Ioc : γ' ∈ Set.Ioc (0 : ℝ) 1 := ⟨hγ'_pos, hγ'_le_one⟩
      dsimp [S] at hS ⊢
      have h_K_F_γ' : FrostmanEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) γ' ω :=
        hML1 γ γ' ω (le_of_lt hγ_pos) hγ_lt_γ' hγ'_le_one hω hS
      have h_K_KT_γ' : KatzTaoEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) γ' ω :=
        KatzTaoEstimateOmega.mono hγ_le_γ' hS
      have h_K_KT_γ'_sub :
          KatzTaoEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) (γ' - g γ' ω / 3) ω :=
        KatzTaoEstimateOmega.trade hn (hg_pos γ' ω hγ'_pos hγ'_le_one hω).le
          (hML2 γ' ω hγ'_pos hγ'_le_one hω h_K_KT_γ' h_K_F_γ')
      have h_ineq : γ' - g γ' ω / 3 ≤ γ - g γ ω / 6 := by
        have hg_le : g γ ω ≤ g γ' ω := hg_mono ω hω hγ hγ'_Ioc hγ_le_γ'
        have hγ'_le : γ' ≤ γ + g γ ω / 6 := min_le_right _ _
        nlinarith
      exact KatzTaoEstimateOmega.mono h_ineq h_K_KT_γ'_sub
  have h4 : MonotoneOn (fun γ ↦ ν γ ω) (Set.Ioc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    dsimp [ν]
    have hg_le : g x ω ≤ g y ω := hg_mono ω hω hx hy hxy
    nlinarith
  have h5 : ∀ γ ∈ Set.Ioc (0 : ℝ) 1, 0 < ν γ ω := by
    intro γ hγ
    dsimp [ν]
    have hgγ_pos : 0 < g γ ω := hg_pos γ ω hγ.1 hγ.2 hω
    nlinarith
  have h_Ioc_sub : Set.Ioc (0 : ℝ) 1 ⊆ {γ' | S γ' ω} :=
    ioc_subset_of_sub_mem_of_monotoneOn_param h1 h2 h3 h4 h5
  have hβ_Ioc : β ∈ Set.Ioc (0 : ℝ) 1 := ⟨hβ, hβ1⟩
  exact h_Ioc_sub hβ_Ioc

end Assembly

end Kakeya
