/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.Assembly

/-!
# The open cardinality band of Main Lemma 2

`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_frostmanEstimate_of_lemma91` splits every family of
`δ`-tubes at the threshold `|𝕋| = δ^{-1}` of Prof. Hong Wang's clarification.  Above the threshold
the GWZ chain runs (`Kakeya.ML2Assembly.Dichotomy`); below it the assembly assumes
`Kakeya.ML2Assembly.SmallCard`.  This module is about `SmallCard`: what it really asks, how much of
it is already paid for, and what the exact residue is.

## The answer, in one line

`SmallCard γ` is **Main Lemma 2's own conclusion, restricted to `|𝕋| < δ^{-1}`**, and the part of
it that is not already implied by `K_KT(β)` is exactly the band

  `δ^{-ε/(2(β-γ))} < |𝕋| < δ^{-1}`,

on which one needs an accuracy-free gain.  Nothing weaker suffices: the three inequalities the
assembly has at its disposal are each *strictly* too weak there, and that is proved here.

## What is proved

Reductions (all `↔` or `→` into the assembly's own `SmallCard`, hence tripwires against drift):

* `Kakeya.ML2Band.bandGoal_iff_smallCard` — `BandGoal γ`, the band-restricted obligation, is
  *equivalent* to `Kakeya.ML2Assembly.SmallCard γ` for every `γ < 1`.  So restricting attention to
  the band loses nothing, and the equivalence breaks the moment `SmallCard` changes;
* `Kakeya.ML2Band.smallCardAt_of_katzTaoEstimate` — `K_KT(β)` alone **proves** `SmallCard γ` at
  every accuracy `ε > β - γ`.  The open part of `SmallCard` is only `ε ≤ β - γ`;
* `Kakeya.ML2Band.smallCardAt_of_bandGoalAt_of_katzTaoEstimate` and
  `Kakeya.ML2Band.smallCard_of_residualBand` — with `K_KT(β)` spent on the low sub-band, the
  residue is the single cut `θ = ε/(2(β-γ))`, i.e. the band displayed above;
* `Kakeya.ML2Band.bandGoalAt_of_one_le_cut` — a cut at `θ ≥ 1` is vacuous, which is why the band
  closes by itself once `ε ≥ 2(β-γ)`.

Sufficient extra inputs, i.e. what would close the band:

* `Kakeya.ML2Band.smallCard_of_bandDichotomy` — the band analogue of
  `Kakeya.ML2Assembly.Dichotomy`: either `μ ≤ δ^{-ε}` or `μ ≤ δ^{g}|𝕋|^{β}`, for families with
  `|𝕋| < δ^{-1}`.  It closes `SmallCard (β - c)` at the budget **`c ≤ g`**, not the `4c ≤ g` the
  large-cardinality branch has to pay: below `δ^{-1}` the crude bound `|𝕋| ≤ δ^{-4}` is replaced
  by `|𝕋| ≤ δ^{-1}`, and the conversion constant drops from `4` to `1`;
* `Kakeya.ML2Band.smallCard_of_bandKakeya` — the stronger, simpler input `μ ≤ δ^{-ε}` on the band.

Sharpness — each of the three inequalities available to the assembly is strictly too weak:

* `Kakeya.ML2Band.trivialRoute_insufficient` — `μ ≤ |𝕋|` costs `θ(1-γ)` at `|𝕋| = δ^{-θ}`;
  `Kakeya.ML2Band.not_katzTaoGoal_of_const_of_cost` turns this into an actual **counterexample**:
  a family of coincident bodies violates the goal as soon as `ε < θ(1-γ)`, so the cost condition of
  `Kakeya.MainLemma2.Reduction.katzTaoGoal_of_card_le_rpow` cannot be relaxed.
  `Kakeya.ML2Band.card_le_of_isKatzTao_const` says where that witness lives: a coincident family is
  Katz--Tao only at a constant `≥ |𝕋|`, so it inhabits exactly the sub-band `|𝕋| ≤ δ^{-η}`;
* `Kakeya.ML2Band.katzTaoRoute_insufficient` — `K_KT(β)` at any accuracy `ε'` is strictly weaker
  than the goal whenever `ε < ε' + θ(β-γ)`.  At the top of the band (`θ = 1`) this holds for every
  `ε ≤ β - γ` and every `ε' > 0`, which is the precise sense in which `K_KT(β)` runs out;
* `Kakeya.ML2Band.absoluteLossRoute_insufficient` — the *first* alternative of the dichotomy,
  `μ ≤ δ^{-ε₀}` at an absolute `ε₀`, is **useless** on the band: it is strictly weaker than the
  goal whenever `ε + θγ < ε₀`.  `Kakeya.ML2Band.absoluteLoss_needs_delta_inv` specialises this to
  the assembly's own parameters (`ε₀ = β/2`, `γ = β/2`, the extreme allowed by `2c ≤ β`) and shows
  the threshold `δ^{-1}` is *exactly* the one that makes
  `Kakeya.MainLemma2.Reduction.katzTaoGoal_of_absoluteLoss_of_card_ge` fire: for every `a < 1` the
  route fails on `|𝕋| ≤ δ^{-a}` once `ε < (1-a)β/2`.  So the band cannot be closed by strengthening
  Theorem 7.3(B); only a genuine `δ`-gain works.

Non-vacuity and the shape of the difficulty:

* `Kakeya.ML2Band.smallCard_of_katzTaoEstimate` — `SmallCard γ` is `K_KT(γ)` with a hypothesis
  discarded, so it is true (it is an instance of the development's own conclusion) and it is *not*
  the kind of obligation that can be discharged by bookkeeping: the assembly asks for it at the
  improved exponent `γ = β - c`;
* `Kakeya.ML2Band.singleton_satisfies_absoluteLoss`, `Kakeya.ML2Band.singleton_fails_gain` — the
  one-element family, which pins down what the single-tube example recorded in the docstring of
  `Kakeya.ML2Assembly.Dichotomy` does and does not refute, and shows why
  `Kakeya.ML2Band.BandDichotomy` has to be a disjunction.

The bilinear case, formally:

* `Kakeya.ML2Band.not_cover_count_of_card_lt_inv` and
  `Kakeya.ML2Band.not_scaleCount_of_card_lt_inv` — the third bullet of GWZ Lemma 9.1
  (`|𝕋_ρ| ≥ ρ^{-2-ζ}` for `ρ = δ^{1-b}`, `b ≤ 1/2`) is **impossible** when `|𝕋| < δ^{-1}`.  This is
  the contrapositive of `Kakeya.MainLemma2.Reduction.delta_inv_le_card_of_scaleCount_bullet` and is
  the formal content of "if `𝕋` is bilinear the count is automatic": the band consists exactly of
  the families that fail the very-not-sticky count at every admissible scale.

## What is *not* here

No broad--narrow decomposition, and no `bilinear` predicate.  The Lean tree has no broadness
apparatus outside the abandoned `Kakeya.DimensionThree.MainLemma2.WangZahl.*` subtree
(`IsBroadAtScale` in `WangZahl/WolffHairbrush.lean`), which Section 9 may not import; the
GWZ-adapted blueprint never mentions broadness.  Building it is a geometric development, not a
bookkeeping one, and nothing in this file pretends otherwise.
-/

@[expose] public section

open MeasureTheory Topology Filter ShadedBody ConvexSpaceBody

namespace Kakeya.ML2Band

universe u

/-- Abbreviation for the ambient space of Main Lemma 2. -/
abbrev Space3 := EuclideanSpace ℝ (Fin 3)

/-- **The band obligation.**

`Kakeya.ML2Assembly.SmallCard γ` with the extra hypothesis `δ^{-θ} < |𝕋|`, for an arbitrary cut
`θ > 0` handed in together with the accuracy.  By `Kakeya.ML2Band.bandGoal_iff_smallCard` this is
*equivalent* to `SmallCard γ` whenever `γ < 1`: the sub-band `|𝕋| ≤ δ^{-θ}` is paid for by the
trivial bound at `θ = ε/(1-γ)`, and conversely the extra hypothesis can always be dropped.

Quantifier order matters here and is the one the assembly needs: `ε` first, then `θ`, then `η`.
Both `θ` and `η` may depend on `ε`; nothing may depend on `δ`, `ι`, `s` or `T`. -/
def BandGoal (γ : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ θ > (0 : ℝ), ∃ η > (0 : ℝ), η ≤ 1 ∧
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (δ : ℝ) ^ (-θ) < (s.card : ℝ) →
        (s.card : ℝ) < (δ : ℝ)⁻¹ →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (T i).shade)

/-- `Kakeya.ML2Band.BandGoal` at one accuracy `ε` and one cut `θ`: the residue of `SmallCard γ`
above `|𝕋| = δ^{-θ}`. -/
def BandGoalAt (γ ε θ : ℝ) : Prop :=
  ∃ η > (0 : ℝ), η ≤ 1 ∧
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (δ : ℝ) ^ (-θ) < (s.card : ℝ) →
        (s.card : ℝ) < (δ : ℝ)⁻¹ →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (T i).shade)

/-- `Kakeya.ML2Band.BandGoal` is the conjunction of its slices, definitionally. -/
theorem bandGoal_iff_forall_bandGoalAt {γ : ℝ} :
    BandGoal.{u} γ ↔ ∀ ε > (0 : ℝ), ∀ θ > (0 : ℝ), BandGoalAt.{u} γ ε θ := Iff.rfl

/-! ### `BandGoal` is exactly `SmallCard` -/

/-- **The band obligation implies the assembly's `SmallCard`.**

The cut is taken at `θ = ε/(1-γ)`, the exact point where the trivial bound `μ ≤ |𝕋|` stops paying:
`Kakeya.MainLemma2.Reduction.katzTaoGoal_of_card_le_rpow` needs `θ(1-γ) ≤ ε`, and
`Kakeya.ML2Band.not_katzTaoGoal_of_const_of_cost` shows that condition cannot be relaxed. -/
theorem smallCard_of_bandGoal {γ : ℝ} (hγ1 : γ < 1) (h : BandGoal.{u} γ) :
    ML2Assembly.SmallCard.{u} γ := by
  intro ε hε
  have hden : (0 : ℝ) < 1 - γ := by linarith
  set θ : ℝ := ε / (1 - γ) with hθdef
  have hθ0 : 0 < θ := div_pos hε hden
  obtain ⟨η, hη0, hη1, hband⟩ := h ε hε θ hθ0
  refine ⟨η, hη0, hη1, ?_⟩
  filter_upwards [hband, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with
    δ hbandδ hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  intro ι s T hball hKT hfull hcard
  rcases le_or_gt ((s.card : ℝ)) ((δ : ℝ) ^ (-θ)) with hlow | hhigh
  · refine Kakeya.MainLemma2.Reduction.katzTaoGoal_of_card_le_rpow
      (E := Space3) (V := fun i ↦ (T i).toShadedBody) hδ0 hδ1.le hγ1.le ?_ hlow
    rw [hθdef, div_mul_cancel₀]
    exact ne_of_gt hden
  · exact hbandδ s T hball hKT hfull hhigh hcard

/-- **Conversely, `SmallCard` gives the band obligation**, by forgetting the cut.  Together with
`Kakeya.ML2Band.smallCard_of_bandGoal` this shows the restriction to the band costs nothing. -/
theorem bandGoal_of_smallCard {γ : ℝ} (h : ML2Assembly.SmallCard.{u} γ) : BandGoal.{u} γ := by
  intro ε hε θ _
  obtain ⟨η, hη0, hη1, hsm⟩ := h ε hε
  refine ⟨η, hη0, hη1, ?_⟩
  filter_upwards [hsm] with δ hδ
  intro ι s T hball hKT hfull _ hcard
  exact hδ s T hball hKT hfull hcard

/-- **Fidelity compatibility.**  `Kakeya.ML2Band.BandGoal` and `Kakeya.ML2Assembly.SmallCard` are the
same obligation.  If the assembly's `SmallCard` ever drifts — a binder moved, a hypothesis added or
dropped — this equivalence stops compiling, so no work in this file can silently come to be about a
different statement than the one the assembly consumes. -/
theorem bandGoal_iff_smallCard {γ : ℝ} (hγ1 : γ < 1) :
    BandGoal.{u} γ ↔ ML2Assembly.SmallCard.{u} γ :=
  ⟨smallCard_of_bandGoal hγ1, bandGoal_of_smallCard⟩

/-! ### A single accuracy -/

/-- `Kakeya.ML2Assembly.SmallCard` at one accuracy `ε`.  Splitting `SmallCard` by accuracy is what
makes it possible to say *which* accuracies are already proved (`ε > β - γ`) and which are open. -/
def SmallCardAt (γ ε : ℝ) : Prop :=
  ∃ η > (0 : ℝ), η ≤ 1 ∧
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (s.card : ℝ) < (δ : ℝ)⁻¹ →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (T i).shade)

/-- `Kakeya.ML2Assembly.SmallCard` is the conjunction of its accuracy slices, definitionally.
A second compatibility against drift in `SmallCard`. -/
theorem smallCard_iff_forall_smallCardAt {γ : ℝ} :
    ML2Assembly.SmallCard.{u} γ ↔ ∀ ε > (0 : ℝ), SmallCardAt.{u} γ ε := Iff.rfl

/-! ### The arithmetic of an exponent drop paid for by a cardinality cap -/

/-- **An exponent drop `β ↝ γ` costs `θ(β-γ)` on `|𝕋| ≤ δ^{-θ}`.**

The one arithmetic fact behind everything below: on a family with at most `δ^{-θ}` tubes, a bound
`μ ≤ δ^{-ε'}|𝕋|^{β}` becomes `μ ≤ δ^{-ε}|𝕋|^{γ}` as soon as `ε' + θ(β-γ) ≤ ε`.

The `θ = 1` instance is the whole of what `K_KT(β)` contributes below `δ^{-1}`, and the constant
`θ(β-γ)` there is sharp: see `Kakeya.ML2Band.katzTaoRoute_insufficient`. -/
theorem katzTaoGoal_of_exponent_drop
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*}
    {s : Finset ι} {V : ι → ShadedBody E} {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {ε ε' β γ θ : ℝ} (hγβ : γ ≤ β) (hcost : ε' + θ * (β - γ) ≤ ε)
    (hcard : (s.card : ℝ) ≤ (δ : ℝ) ^ (-θ))
    (h : ∑ i ∈ s, volume (V i).shade
          ≤ (δ : ENNReal) ^ (-ε') * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (V i).shade)) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (V i).shade) := by
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · rw [Finset.card_eq_zero.mp h0]; simp
  have hN0 : (s.card : ENNReal) ≠ 0 := by simpa using hpos.ne'
  have hNtop : (s.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hδE0 : (0 : ENNReal) < (δ : ENNReal) := by exact_mod_cast hδ0
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hcardE : (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-θ) :=
    Kakeya.MainLemma2.Reduction.natCast_le_coe_rpow hδ0 hcard
  have hstep : (s.card : ENNReal) ^ (β - γ) ≤ (δ : ENNReal) ^ (-(θ * (β - γ))) := by
    calc (s.card : ENNReal) ^ (β - γ)
        ≤ ((δ : ENNReal) ^ (-θ)) ^ (β - γ) := ENNReal.rpow_le_rpow hcardE (by linarith)
      _ = (δ : ENNReal) ^ (-(θ * (β - γ))) := by rw [← ENNReal.rpow_mul]; congr 1; ring
  have hsplit : (s.card : ENNReal) ^ β
      = (s.card : ENNReal) ^ γ * (s.card : ENNReal) ^ (β - γ) := by
    rw [← ENNReal.rpow_add _ _ hN0 hNtop]; congr 1; ring
  have hexp : (δ : ENNReal) ^ (-(ε' + θ * (β - γ))) ≤ (δ : ENNReal) ^ (-ε) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
  have hcoef : (δ : ENNReal) ^ (-ε') * (s.card : ENNReal) ^ β
      ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ := by
    calc (δ : ENNReal) ^ (-ε') * (s.card : ENNReal) ^ β
        = (δ : ENNReal) ^ (-ε') *
            ((s.card : ENNReal) ^ γ * (s.card : ENNReal) ^ (β - γ)) := by rw [hsplit]
      _ ≤ (δ : ENNReal) ^ (-ε') *
            ((s.card : ENNReal) ^ γ * (δ : ENNReal) ^ (-(θ * (β - γ)))) := by gcongr
      _ = ((δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ (-(θ * (β - γ)))) *
            (s.card : ENNReal) ^ γ := by ring
      _ = (δ : ENNReal) ^ (-(ε' + θ * (β - γ))) * (s.card : ENNReal) ^ γ := by
          rw [← ENNReal.rpow_add _ _ hδE0.ne' ENNReal.coe_ne_top]; congr 2; ring
      _ ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ := by gcongr
  exact h.trans (by gcongr)

/-! ### What `K_KT(β)` alone buys on the band -/

/-- **`K_KT(β)` closes the small-cardinality case at every accuracy coarser than the drop.**

`|𝕋| < δ^{-1}` gives `|𝕋|^{β} ≤ |𝕋|^{γ} δ^{-(β-γ)}`, so `K_KT(β)` read at accuracy `ε - (β-γ)`
already delivers the goal — provided that number is positive, i.e. `ε > β - γ`.

This is the positive half of the answer about `Kakeya.ML2Assembly.SmallCard`: with `γ = β - c` the
open part of `SmallCard (β - c)` is exactly the accuracies `ε ≤ c`.  Since `c` is `ε`-free by
Prof. Hong Wang's discipline (`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy`), those accuracies
cannot be legislated away. -/
theorem smallCardAt_of_katzTaoEstimate {β γ ε : ℝ} (hγβ : γ ≤ β)
    (hε : β - γ < ε) (hKT : KatzTaoEstimate.{u} Space3 β) :
    SmallCardAt.{u} γ ε := by
  have hε'0 : 0 < ε - (β - γ) := by linarith
  obtain ⟨η, hη0, hev⟩ := hKT (ε - (β - γ)) hε'0
  refine ⟨min η 1, lt_min hη0 one_pos, min_le_right _ _, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδev hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  intro ι s T hball hKT' hfull hcard
  have hKTη : IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) :=
    ML2Assembly.isKatzTao_of_exponent_le hδ1.le (min_le_left _ _) hKT'
  have hfullη : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η :=
    ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_left _ _) hfull
  refine katzTaoGoal_of_exponent_drop (V := fun i ↦ (T i).toShadedBody) hδ0 hδ1.le hγβ
    (θ := 1) (by linarith) ?_ (hδev s T hball hKTη hfullη)
  rw [Real.rpow_neg_one]; exact hcard.le

/-- **The residual band, once `K_KT(β)` has been spent.**

Splitting at `θ = ε/(2(β-γ))` and paying the low side with `K_KT(β)` at accuracy `ε/2` (via
`Kakeya.ML2Band.katzTaoGoal_of_exponent_drop`), the only hypothesis is on

  `δ^{-ε/(2(β-γ))} < |𝕋| < δ^{-1}`.

This is strictly better than the naive cut `θ = ε/(1-γ)` used by
`Kakeya.ML2Band.smallCard_of_bandGoal`, because `β - γ` is the small quantity (`= c`, the drop) and
`1 - γ` is not.  It also makes the collapse visible: by
`Kakeya.ML2Band.bandGoalAt_of_one_le_cut` the band is empty as soon as `ε ≥ 2(β-γ)`. -/
theorem smallCardAt_of_bandGoalAt_of_katzTaoEstimate {β γ ε : ℝ} (hγβ : γ < β) (hε : 0 < ε)
    (hKT : KatzTaoEstimate.{u} Space3 β)
    (hband : BandGoalAt.{u} γ ε (ε / (2 * (β - γ)))) : SmallCardAt.{u} γ ε := by
  have hβγ : 0 < β - γ := by linarith
  obtain ⟨η₁, hη₁0, hev₁⟩ := hKT (ε / 2) (by linarith)
  obtain ⟨η₂, hη₂0, hη₂1, hev₂⟩ := hband
  refine ⟨min (min η₁ 1) η₂, lt_min (lt_min hη₁0 one_pos) hη₂0, le_trans (min_le_left _ _)
    (min_le_right _ _), ?_⟩
  filter_upwards [hev₁, hev₂, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with
    δ hδ₁ hδ₂ hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  intro ι s T hball hKT' hfull hcard
  have hKTη₁ : IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η₁)) :=
    ML2Assembly.isKatzTao_of_exponent_le hδ1.le
      (le_trans (min_le_left _ _) (min_le_left _ _)) hKT'
  have hfullη₁ : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η₁ :=
    ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le
      (le_trans (min_le_left _ _) (min_le_left _ _)) hfull
  have hKTη₂ : IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η₂)) :=
    ML2Assembly.isKatzTao_of_exponent_le hδ1.le (min_le_right _ _) hKT'
  have hfullη₂ : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η₂ :=
    ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_right _ _) hfull
  rcases le_or_gt ((s.card : ℝ)) ((δ : ℝ) ^ (-(ε / (2 * (β - γ))))) with hlow | hhigh
  · refine katzTaoGoal_of_exponent_drop (V := fun i ↦ (T i).toShadedBody) hδ0 hδ1.le hγβ.le
      (θ := ε / (2 * (β - γ))) ?_ hlow (hδ₁ s T hball hKTη₁ hfullη₁)
    have : ε / (2 * (β - γ)) * (β - γ) = ε / 2 := by field_simp
    rw [this]; linarith
  · exact hδ₂ s T hball hKTη₂ hfullη₂ hhigh hcard

/-! ### Two sufficient inputs for the band -/

/-- **The band dichotomy** — the small-cardinality analogue of `Kakeya.ML2Assembly.Dichotomy`.

For families with `|𝕋| < δ^{-1}`: either the accuracy-quality bound `μ ≤ δ^{-ε}`, or an
accuracy-free gain `μ ≤ δ^{g}|𝕋|^{β}`.

Two remarks on the statement, both of which are the reason it is *this* and not something simpler.

* **The first alternative must be read at the outer `ε`, not at an absolute `ε₀`.**  On the band an
  absolute loss is worthless: `Kakeya.ML2Band.absoluteLossRoute_insufficient` shows
  `δ^{-ε}|𝕋|^{γ} < δ^{-ε₀}` whenever `ε + θγ < ε₀`, and the cut `θ` shrinks with `ε`.  This is the
  exact opposite of the large-cardinality branch, where `|𝕋| ≥ δ^{-1}` makes `|𝕋|^{γ} ≥ δ^{-γ}`
  absorb `ε₀ = β/2` for free (`Kakeya.MainLemma2.Reduction.katzTaoGoal_of_absoluteLoss_of_card_ge`).
* **The second alternative cannot be asked for alone.**  `μ ≥ 1` always, while `δ^{g}|𝕋|^{β} < 1`
  whenever `|𝕋|^{β} < δ^{-g}`; a single fully shaded tube already refutes it.  So the disjunction is
  necessary, and the first alternative is what covers the bottom of the range. -/
def BandDichotomy (β g : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), η ≤ 1 ∧
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (s.card : ℝ) < (δ : ℝ)⁻¹ →
        (∑ i ∈ s, volume (T i).shade
            ≤ (δ : ENNReal) ^ (-ε) * volume (⋃ i ∈ s, (T i).shade))
          ∨ (∑ i ∈ s, volume (T i).shade
            ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade))

/-- **The Kakeya bound on the band**: `μ ≤ δ^{-ε}` for families with `|𝕋| < δ^{-1}`.

The strongest of the sufficient inputs, and the cleanest statement of what the band really asks:
the Kakeya multiplicity estimate itself, for families of fewer than `δ^{-1}` tubes.  It implies
`Kakeya.ML2Band.BandDichotomy` at every gain (`Kakeya.ML2Band.bandDichotomy_of_bandKakeya`) and
`Kakeya.ML2Assembly.SmallCard γ` at every `γ ≥ 0`. -/
def BandKakeya : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), η ≤ 1 ∧
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (s.card : ℝ) < (δ : ℝ)⁻¹ →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ (-ε) * volume (⋃ i ∈ s, (T i).shade)

/-- **`Kakeya.ML2Band.BandDichotomy` closes the band, at the budget `c ≤ g`.**

Compare `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy`, which needs `4c ≤ g`: there the
gain has to be converted using the crude bound `|𝕋| ≤ δ^{-4}`
(`Kakeya.ML2Assembly.card_le_rpow_neg_four`), here using `|𝕋| ≤ δ^{-1}`, so the conversion constant
`K` of `Kakeya.ML2Reduction.le_rpow_mul_rpow_of_gain` drops from `4` to `1`.  The band is therefore
*cheaper* than the main branch in the only budget that the spine has to balance. -/
theorem smallCard_of_bandDichotomy {β g c : ℝ} (hc : 0 < c) (hcg : c ≤ g) (hγ : 0 ≤ β - c)
    (h : BandDichotomy.{u} β g) : ML2Assembly.SmallCard.{u} (β - c) := by
  intro ε hε
  obtain ⟨η, hη0, hη1, hev⟩ := h ε hε
  refine ⟨η, hη0, hη1, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδev hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  intro ι s T hball hKT hfull hcard
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · rw [Finset.card_eq_zero.mp h0]; simp
  have hN1 : (1 : ENNReal) ≤ (s.card : ENNReal) := by exact_mod_cast hpos
  have hcardle : ((s.card : ℝ)) ≤ (δ : ℝ) ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one]; exact hcard.le
  rcases hδev s T hball hKT hfull hcard with h1 | h2
  · refine h1.trans ?_
    have hone : (1 : ENNReal) ≤ (s.card : ENNReal) ^ (β - c) := by
      calc (1 : ENNReal) = (s.card : ENNReal) ^ (0 : ℝ) := ENNReal.rpow_zero.symm
        _ ≤ (s.card : ENNReal) ^ (β - c) := ENNReal.rpow_le_rpow_of_exponent_le hN1 hγ
    calc (δ : ENNReal) ^ (-ε) * volume (⋃ i ∈ s, (T i).shade)
        = (δ : ENNReal) ^ (-ε) * 1 * volume (⋃ i ∈ s, (T i).shade) := by ring
      _ ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ (β - c)
            * volume (⋃ i ∈ s, (T i).shade) := by gcongr
  · have hcoef : (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β
        ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ (β - c) :=
      Kakeya.ML2Reduction.le_rpow_mul_rpow_of_gain (β := β) (K := 1) hδ0 hδ1.le hpos hc.le
        (by linarith) (by simpa using hcardle) le_rfl
    exact h2.trans (by gcongr)

/-- **`Kakeya.ML2Band.BandKakeya` closes the band at every exponent `γ ≥ 0`**, since `|𝕋| ≥ 1`
makes `|𝕋|^{γ} ≥ 1`.  In particular it closes `SmallCard γ` for every `γ` the assembly may ask
for, with no budget condition at all. -/
theorem smallCard_of_bandKakeya {γ : ℝ} (hγ : 0 ≤ γ) (h : BandKakeya.{u}) :
    ML2Assembly.SmallCard.{u} γ := by
  intro ε hε
  obtain ⟨η, hη0, hη1, hev⟩ := h ε hε
  refine ⟨η, hη0, hη1, ?_⟩
  filter_upwards [hev] with δ hδev
  intro ι s T hball hKT hfull hcard
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · rw [Finset.card_eq_zero.mp h0]; simp
  have hN1 : (1 : ENNReal) ≤ (s.card : ENNReal) := by exact_mod_cast hpos
  have hone : (1 : ENNReal) ≤ (s.card : ENNReal) ^ γ := by
    calc (1 : ENNReal) = (s.card : ENNReal) ^ (0 : ℝ) := ENNReal.rpow_zero.symm
      _ ≤ (s.card : ENNReal) ^ γ := ENNReal.rpow_le_rpow_of_exponent_le hN1 hγ
  refine (hδev s T hball hKT hfull hcard).trans ?_
  calc (δ : ENNReal) ^ (-ε) * volume (⋃ i ∈ s, (T i).shade)
      = (δ : ENNReal) ^ (-ε) * 1 * volume (⋃ i ∈ s, (T i).shade) := by ring
    _ ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ
          * volume (⋃ i ∈ s, (T i).shade) := by gcongr

/-- `Kakeya.ML2Band.BandKakeya` is the first alternative of `Kakeya.ML2Band.BandDichotomy`, at
every exponent and every gain. -/
theorem bandDichotomy_of_bandKakeya {β g : ℝ} (h : BandKakeya.{u}) : BandDichotomy.{u} β g := by
  intro ε hε
  obtain ⟨η, hη0, hη1, hev⟩ := h ε hε
  refine ⟨η, hη0, hη1, ?_⟩
  filter_upwards [hev] with δ hδev
  intro ι s T hball hKT hfull hcard
  exact Or.inl (hδev s T hball hKT hfull hcard)

/-! ### Sharpness: the two routes available to the assembly both fail on the band -/

section Sharp

variable {δ : ℝ}

/-- **The trivial route is sharp.**  At `|𝕋| ≥ δ^{-θ}` the trivial bound `μ ≤ |𝕋|` is strictly
weaker than the goal `μ ≤ δ^{-ε}|𝕋|^{γ}` as soon as `ε < θ(1-γ)`.

This is `Kakeya.MainLemma2.Reduction.trivialBranch_cost_sharp` at a general cardinality rather than
only at `|𝕋| = δ^{-1}`; `Kakeya.ML2Band.not_katzTaoGoal_of_const_of_cost` upgrades it from a
comparison of bounds to a refutation by an actual family. -/
theorem trivialRoute_insufficient {ε γ θ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hγ1 : γ ≤ 1)
    (hbudget : ε < θ * (1 - γ)) {N : ℝ} (hN0 : 0 < N) (hN : δ ^ (-θ) ≤ N) :
    δ ^ (-ε) * N ^ γ < N := by
  have hpow : δ ^ (-(θ * (1 - γ))) ≤ N ^ (1 - γ) := by
    calc δ ^ (-(θ * (1 - γ))) = (δ ^ (-θ)) ^ (1 - γ) := by
          rw [← Real.rpow_mul hδ0.le]; congr 1; ring
      _ ≤ N ^ (1 - γ) := Real.rpow_le_rpow (Real.rpow_nonneg hδ0.le _) hN (by linarith)
  have hstrict : δ ^ (-ε) < δ ^ (-(θ * (1 - γ))) :=
    Real.rpow_lt_rpow_of_exponent_gt hδ0 hδ1 (by linarith)
  calc δ ^ (-ε) * N ^ γ < δ ^ (-(θ * (1 - γ))) * N ^ γ := by
        exact mul_lt_mul_of_pos_right hstrict (Real.rpow_pos_of_pos hN0 _)
    _ ≤ N ^ (1 - γ) * N ^ γ := by
        exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hN0.le _)
    _ = N := by rw [← Real.rpow_add hN0]; simp

/-- **The `K_KT(β)` route is sharp.**  At `|𝕋| ≥ δ^{-θ}` the bound `μ ≤ δ^{-ε'}|𝕋|^{β}` supplied by
`K_KT(β)` is strictly weaker than the goal `μ ≤ δ^{-ε}|𝕋|^{γ}` as soon as `ε < ε' + θ(β-γ)`.

Read at `θ = 1`, the top of the band: for **every** accuracy `ε' > 0` at which `K_KT(β)` may be
invoked, and every `ε ≤ β - γ`, the hypothesis is strictly too weak.  Together with
`Kakeya.ML2Band.smallCardAt_of_katzTaoEstimate` this determines the contribution of `K_KT(β)` to
`SmallCard γ` exactly: all accuracies `ε > β - γ`, and none below. -/
theorem katzTaoRoute_insufficient {ε ε' β γ θ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hγβ : γ ≤ β)
    (hbudget : ε < ε' + θ * (β - γ)) {N : ℝ} (hN0 : 0 < N) (hN : δ ^ (-θ) ≤ N) :
    δ ^ (-ε) * N ^ γ < δ ^ (-ε') * N ^ β := by
  have hpow : δ ^ (-(θ * (β - γ))) ≤ N ^ (β - γ) := by
    calc δ ^ (-(θ * (β - γ))) = (δ ^ (-θ)) ^ (β - γ) := by
          rw [← Real.rpow_mul hδ0.le]; congr 1; ring
      _ ≤ N ^ (β - γ) := Real.rpow_le_rpow (Real.rpow_nonneg hδ0.le _) hN (by linarith)
  have hstrict : δ ^ (-ε) < δ ^ (-(ε' + θ * (β - γ))) :=
    Real.rpow_lt_rpow_of_exponent_gt hδ0 hδ1 (by linarith)
  have hsplit : δ ^ (-(ε' + θ * (β - γ))) = δ ^ (-ε') * δ ^ (-(θ * (β - γ))) := by
    rw [← Real.rpow_add hδ0]; congr 1; ring
  calc δ ^ (-ε) * N ^ γ < δ ^ (-(ε' + θ * (β - γ))) * N ^ γ :=
        mul_lt_mul_of_pos_right hstrict (Real.rpow_pos_of_pos hN0 _)
    _ = δ ^ (-ε') * (δ ^ (-(θ * (β - γ))) * N ^ γ) := by rw [hsplit]; ring
    _ ≤ δ ^ (-ε') * (N ^ (β - γ) * N ^ γ) := by
        have := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hN0.le γ)
        exact mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hδ0.le _)
    _ = δ ^ (-ε') * N ^ β := by rw [← Real.rpow_add hN0]; congr 2; ring

/-- **The absolute-loss route is useless below `δ^{-1}`.**  If `|𝕋| ≤ δ^{-θ}` then the goal
`μ ≤ δ^{-ε}|𝕋|^{γ}` is strictly *stronger* than `μ ≤ δ^{-ε₀}` whenever `ε + θγ < ε₀`.

Since the cut `θ` shrinks with `ε` (it is `ε/(1-γ)`, or `ε/(2(β-γ))` after `K_KT(β)` is spent) while
`ε₀` is absolute, the hypothesis `ε + θγ < ε₀` holds for all small `ε`.  So Theorem 7.3(B) — the
source of alternative (i) of `Kakeya.ML2Assembly.Dichotomy`, read at the absolute accuracy
`Kakeya.ML2Spine.absAccuracy β = β/2` — contributes **nothing** on the band, however strong it is
made, unless its accuracy is allowed to depend on the outer `ε`, which
`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy` forbids. -/
theorem absoluteLossRoute_insufficient {ε ε₀ γ θ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ)
    (hbudget : ε + θ * γ < ε₀) {N : ℝ} (hN0 : 0 < N) (hN : N ≤ δ ^ (-θ)) :
    δ ^ (-ε) * N ^ γ < δ ^ (-ε₀) := by
  have hpow : N ^ γ ≤ δ ^ (-(θ * γ)) := by
    calc N ^ γ ≤ (δ ^ (-θ)) ^ γ := Real.rpow_le_rpow hN0.le hN hγ
      _ = δ ^ (-(θ * γ)) := by rw [← Real.rpow_mul hδ0.le]; congr 1; ring
  have hstrict : δ ^ (-(ε + θ * γ)) < δ ^ (-ε₀) :=
    Real.rpow_lt_rpow_of_exponent_gt hδ0 hδ1 (by linarith)
  calc δ ^ (-ε) * N ^ γ ≤ δ ^ (-ε) * δ ^ (-(θ * γ)) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hδ0.le _)
    _ = δ ^ (-(ε + θ * γ)) := by rw [← Real.rpow_add hδ0]; congr 1; ring
    _ < δ ^ (-ε₀) := hstrict

/-- **The threshold `δ^{-1}` of the assembly is sharp.**

At the assembly's own parameters — `ε₀ = β/2` and `γ = β/2`, the extreme permitted by the `ε`-free
budget `2c ≤ β` (`Kakeya.ML2Spine.two_spineNu_le`) — the absolute-loss route fails on `|𝕋| ≤ δ^{-a}`
for every `a < 1` and every `ε < (1-a)β/2`.  So no threshold below `δ^{-1}` would let
`Kakeya.MainLemma2.Reduction.katzTaoGoal_of_absoluteLoss_of_card_ge` fire, and the case split of
`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` is at the only place it can be. -/
theorem absoluteLoss_needs_delta_inv {β a ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hβ : 0 ≤ β)
    (hε : ε < (1 - a) * (β / 2)) {N : ℝ} (hN0 : 0 < N) (hN : N ≤ δ ^ (-a)) :
    δ ^ (-ε) * N ^ (β / 2) < δ ^ (-(β / 2)) :=
  absoluteLossRoute_insufficient hδ0 hδ1 (by linarith) (by nlinarith) hN0 hN

end Sharp

/-! ### The constant family: where the trivial branch stops, and why -/

section Const

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- Bridge, dual to `Kakeya.MainLemma2.Reduction.natCast_le_coe_rpow`: a real cardinality *lower*
bound `δ^{-θ} ≤ N` becomes the one in `[0,∞]`. -/
theorem coe_rpow_le_natCast {δ : NNReal} (hδ : 0 < δ) {θ : ℝ} {n : ℕ}
    (h : (δ : ℝ) ^ (-θ) ≤ (n : ℝ)) : (δ : ENNReal) ^ (-θ) ≤ (n : ENNReal) := by
  rw [← ENNReal.coe_rpow_of_ne_zero hδ.ne']
  rw [show ((n : ENNReal)) = ((n : NNReal) : ENNReal) by simp]
  rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simpa [NNReal.coe_rpow] using h

/-- **A constant family is Katz--Tao only at a constant at least its cardinality.**

Testing `Δ_max` on the body itself gives `densityIn = |s|`, so `IsKatzTao s (fun _ ↦ V₀) C` forces
`|s| ≤ C`.  With `C = δ^{-η}` this locates the coincident-family counterexample of
`Kakeya.ML2Band.not_katzTaoGoal_of_const_of_cost` precisely: it lives in `|𝕋| ≤ δ^{-η}` and nowhere
else, which is why it certifies the sharpness of the trivial branch rather than refuting
`SmallCard`. -/
theorem card_le_of_isKatzTao_const (s : Finset ι) (V₀ : ConvexSpaceBody E)
    (hv0 : volume V₀.carrier ≠ 0) {C : ENNReal} (h : IsKatzTao s (fun _ ↦ V₀) C) :
    (s.card : ENNReal) ≤ C := by
  have hvtop : volume V₀.carrier ≠ ⊤ := V₀.isCompact.measure_ne_top
  have hall : ∀ i ∈ s, (fun _ : ι ↦ V₀) i ≤ V₀ := fun _ _ ↦ le_rfl
  have hd : densityIn s (fun _ ↦ V₀) V₀ = (s.card : ENNReal) := by
    rw [densityIn_of_all_le hall, Finset.sum_const, nsmul_eq_mul]
    exact ENNReal.mul_div_cancel_right hv0 hvtop
  calc (s.card : ENNReal) = densityIn s (fun _ ↦ V₀) V₀ := hd.symm
    _ ≤ maxDensity s (fun _ ↦ V₀) := le_maxDensity s _ V₀
    _ ≤ C := h

/-- **The cost condition of the trivial branch is sharp.**

A family of `|s|` coincident shaded bodies has multiplicity exactly `|s|`
(`Kakeya.MainLemma2.Reduction.multiplicity_const`), so it violates the goal
`μ ≤ δ^{-ε}|𝕋|^{γ}` as soon as `|s| ≥ δ^{-θ}` with `ε < θ(1-γ)`.  Hence the hypothesis
`θ(1-γ) ≤ ε` of `Kakeya.MainLemma2.Reduction.katzTaoGoal_of_card_le_rpow` cannot be weakened, and
the cut used by `Kakeya.ML2Band.smallCard_of_bandGoal` is at the largest possible place.

By `Kakeya.ML2Band.card_le_of_isKatzTao_const` such a family is `δ^{-η}`-Katz--Tao only when
`|s| ≤ δ^{-η}`, so this is sharpness of the *trivial branch*, not a refutation of
`Kakeya.ML2Assembly.SmallCard` — which is true, being an instance of the theorem the whole
development is proving. -/
theorem not_katzTaoGoal_of_const_of_cost (s : Finset ι) (hs : s.Nonempty) (V₀ : ShadedBody E)
    (hv : volume V₀.shade ≠ 0) {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1) {ε γ θ : ℝ}
    (hγ1 : γ ≤ 1) (hcost : ε < θ * (1 - γ))
    (hcard : (δ : ℝ) ^ (-θ) ≤ (s.card : ℝ)) :
    ¬ (∑ i ∈ s, volume ((fun _ : ι ↦ V₀) i).shade
        ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ *
            volume (⋃ i ∈ s, ((fun _ : ι ↦ V₀) i).shade)) := by
  refine Kakeya.MainLemma2.Reduction.katzTaoGoal_fails_of_const s hs V₀ hv ?_
  have hpos : 0 < s.card := Finset.card_pos.mpr hs
  have hN0 : (s.card : ENNReal) ≠ 0 := by simpa using hpos.ne'
  have hNtop : (s.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hNγ0 : (s.card : ENNReal) ^ γ ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hN0, hNtop]
  have hNγtop : (s.card : ENNReal) ^ γ ≠ ⊤ := by
    simp [ENNReal.rpow_eq_top_iff, hN0, hNtop]
  have hδE0 : (0 : ENNReal) < (δ : ENNReal) := by exact_mod_cast hδ0
  have hδE1 : (δ : ENNReal) < 1 := by exact_mod_cast hδ1
  have hcardE : (δ : ENNReal) ^ (-θ) ≤ (s.card : ENNReal) := coe_rpow_le_natCast hδ0 hcard
  have hpow : (δ : ENNReal) ^ (-(θ * (1 - γ))) ≤ (s.card : ENNReal) ^ (1 - γ) := by
    calc (δ : ENNReal) ^ (-(θ * (1 - γ))) = ((δ : ENNReal) ^ (-θ)) ^ (1 - γ) := by
          rw [← ENNReal.rpow_mul]; congr 1; ring
      _ ≤ (s.card : ENNReal) ^ (1 - γ) := ENNReal.rpow_le_rpow hcardE (by linarith)
  have hstrict : (δ : ENNReal) ^ (-ε) < (δ : ENNReal) ^ (-(θ * (1 - γ))) :=
    ENNReal.rpow_lt_rpow_of_exponent_gt hδE0 hδE1 (by linarith)
  calc (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ
      = (s.card : ENNReal) ^ γ * (δ : ENNReal) ^ (-ε) := mul_comm _ _
    _ < (s.card : ENNReal) ^ γ * (δ : ENNReal) ^ (-(θ * (1 - γ))) :=
        ENNReal.mul_lt_mul_right hNγ0 hNγtop hstrict
    _ = (δ : ENNReal) ^ (-(θ * (1 - γ))) * (s.card : ENNReal) ^ γ := mul_comm _ _
    _ ≤ (s.card : ENNReal) ^ (1 - γ) * (s.card : ENNReal) ^ γ := by gcongr
    _ = (s.card : ENNReal) := by
        rw [← ENNReal.rpow_add _ _ hN0 hNtop]; simp

end Const

/-! ### The very-not-sticky count empties the band -/

/-- **A cover-indexed very-not-sticky count is impossible below `δ^{-1}`.**

Contrapositive of `Kakeya.MainLemma2.Reduction.delta_inv_le_card_of_cover_count`.  This is the
formal content of "if `𝕋` is bilinear, `|𝕋| > δ^{-1}` is automatic": the third bullet of GWZ
Lemma 9.1 already forces `|𝕋| ≥ δ^{-1}` at any scale `ρ = δ^{1-b}` with `b ≤ 1/2`, so the band
consists exactly of the families for which that count fails at every admissible scale. -/
theorem not_cover_count_of_card_lt_inv {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (R : ι → κ → Prop)
    (hcov : ∀ i ∈ s, ∃ j ∈ t, R i j)
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {b ζ : ℝ} (hb : b ≤ 1 / 2) (hζ : 0 ≤ ζ)
    (hlt : (s.card : ℝ) < (δ : ℝ)⁻¹) :
    ¬ (∀ t' : Finset κ, t' ⊆ t → (∀ i ∈ s, ∃ j ∈ t', R i j) →
        ((δ ^ (1 - b) : NNReal) : ℝ) ^ (-2 - ζ) ≤ (t'.card : ℝ)) := fun h ↦
  absurd (Kakeya.MainLemma2.Reduction.delta_inv_le_card_of_cover_count
    s t R hcov hδ hδ1 hb hζ h) (not_le.mpr hlt)

/-- **The bullet-shaped form**, matching the third hypothesis of
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge` verbatim. -/
theorem not_scaleCount_of_card_lt_inv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {ι κ : Type*} [DecidableEq κ] {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {exscal ζ : ℝ} (hex : exscal ≤ 1 / 2) (hζ : 0 ≤ ζ)
    (s : Finset ι) (T : ι → ShadedTube δ E)
    (tρ : Finset κ) (Tρ : κ → Tube (δ ^ (1 - exscal)) E)
    (hcov : ∀ i ∈ s, ∃ j ∈ tρ, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody)
    (hpair : (tρ : Set κ).Pairwise
      (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier))
    (hlt : (s.card : ℝ) < (δ : ℝ)⁻¹) :
    ¬ (∀ (t' : Finset κ) (Tρ' : κ → Tube (δ ^ (1 - exscal)) E),
        (∀ i ∈ s, ∃ j ∈ t', (T i).toConvexSpaceBody ≤ (Tρ' j).toConvexSpaceBody) →
        (t' : Set κ).Pairwise
          (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ' j).carrier (Tρ' k).carrier) →
        ((δ ^ (1 - exscal) : NNReal) : ℝ) ^ (-2 - ζ) ≤ (t'.card : ℝ)) := fun h ↦
  absurd (Kakeya.MainLemma2.Reduction.delta_inv_le_card_of_scaleCount_bullet
    hδ hδ1 hex hζ s T tρ Tρ hcov hpair h) (not_le.mpr hlt)

/-! ### The band is empty at coarse accuracies -/

/-- **A cut at `θ ≥ 1` leaves nothing**: `δ^{-θ} ≥ δ^{-1}` for `δ ≤ 1`, so the two band hypotheses
`δ^{-θ} < |𝕋|` and `|𝕋| < δ^{-1}` are contradictory and `BandGoalAt` holds vacuously.

This is the mechanical reason `Kakeya.ML2Band.smallCardAt_of_katzTaoEstimate` works: at accuracies
`ε ≥ 2(β-γ)` the residual cut `ε/(2(β-γ))` is `≥ 1` and there is no band left. -/
theorem bandGoalAt_of_one_le_cut {γ ε θ : ℝ} (hθ : 1 ≤ θ) : BandGoalAt.{u} γ ε θ := by
  refine ⟨1, one_pos, le_rfl, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  intro ι s T _ _ _ hlow hhigh
  have hδ0R : (0 : ℝ) < (δ : ℝ) := hδ0
  have hδ1R : ((δ : ℝ)) ≤ 1 := by exact_mod_cast hδ1.le
  have : ((δ : ℝ))⁻¹ ≤ (δ : ℝ) ^ (-θ) := by
    rw [← Real.rpow_neg_one (δ : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_ge hδ0R hδ1R (by linarith)
  exact absurd (lt_of_lt_of_le hhigh this) (not_lt.mpr hlow.le)

/-- **The verdict, in one statement.**

Given `K_KT(β)`, the assembly's `Kakeya.ML2Assembly.SmallCard γ` follows from — and, by
`Kakeya.ML2Band.bandGoal_of_smallCard`, is no stronger than — the single obligation

  for every `ε > 0`: `μ(𝕋,Y) ≤ δ^{-ε}|𝕋|^{γ}` on `δ^{-ε/(2(β-γ))} < |𝕋| < δ^{-1}`.

That band is empty for `ε ≥ 2(β-γ)` and grows to the whole range as `ε → 0`.  It is not closable by
any of the three inequalities the assembly holds — see the three `*_insufficient` theorems above —
and what closes it is `Kakeya.ML2Band.BandDichotomy` (equivalently, the window branch of the GWZ
chain extended below `δ^{-1}`, at the cheaper budget `c ≤ g`) or the stronger
`Kakeya.ML2Band.BandKakeya`. -/
theorem smallCard_of_residualBand {β γ : ℝ} (hγβ : γ < β)
    (hKT : KatzTaoEstimate.{u} Space3 β)
    (h : ∀ ε > (0 : ℝ), BandGoalAt.{u} γ ε (ε / (2 * (β - γ)))) :
    ML2Assembly.SmallCard.{u} γ :=
  fun ε hε ↦ smallCardAt_of_bandGoalAt_of_katzTaoEstimate hγβ hε hKT (h ε hε)

/-! ### `SmallCard` is true, and what that costs -/

/-- **`SmallCard γ` is `K_KT(γ)` with a hypothesis thrown away.**

So `Kakeya.ML2Assembly.SmallCard γ` is not false — it is an instance of the very statement the
development is proving — but it is also not cheap: the assembly asks for it at `γ = β - c`, i.e. at
the *improved* exponent, which is exactly the conclusion of Main Lemma 2.  This, and not any defect
of the statement, is why the band is open: below `δ^{-1}` the GWZ chain has nothing to say, and
`K_KT(β)` at the *old* exponent runs out at `ε = β - γ`
(`Kakeya.ML2Band.smallCardAt_of_katzTaoEstimate`, `Kakeya.ML2Band.katzTaoRoute_insufficient`). -/
theorem smallCard_of_katzTaoEstimate {γ : ℝ} (h : KatzTaoEstimate.{u} Space3 γ) :
    ML2Assembly.SmallCard.{u} γ := by
  intro ε hε
  obtain ⟨η, hη0, hev⟩ := h ε hε
  refine ⟨min η 1, lt_min hη0 one_pos, min_le_right _ _, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδev hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  intro ι s T hball hKT hfull _
  exact hδev s T hball
    (ML2Assembly.isKatzTao_of_exponent_le hδ1.le (min_le_left _ _) hKT)
    (ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_left _ _) hfull)

/-! ### The single-tube example, and what it does and does not refute -/

section Singleton

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **A one-element family satisfies alternative (i) of the dichotomy.**

The docstring of `Kakeya.ML2Assembly.Dichotomy` records a single fully shaded `δ`-tube as
satisfying "neither `μ ≤ δ^{-β/2}` nor `μ ≤ δ^{g}|𝕋|^{β}`".  The first half of that sentence is
inaccurate as written: a one-element family has `μ = 1`, and `1 ≤ δ^{-ε₀}` for every `ε₀ ≥ 0` and
every `δ ≤ 1`, so alternative (i) *holds*.

The example is nevertheless a genuine refutation of the shape it was aimed at — the earlier draft in
which `δ^{-1} ≤ |𝕋|` was a **conjunct of each disjunct** rather than a hypothesis, where the tube
fails both disjuncts for the trivial reason that `δ^{-1} ≤ 1` is false.  Recorded here so that the
distinction is compiler-checked rather than left to a docstring. -/
theorem singleton_satisfies_absoluteLoss (i : ι) (V : ι → ShadedBody E) {δ : NNReal}
    (hδ1 : δ ≤ 1) {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) :
    ∑ j ∈ ({i} : Finset ι), volume (V j).shade
      ≤ (δ : ENNReal) ^ (-ε₀) * volume (⋃ j ∈ ({i} : Finset ι), (V j).shade) := by
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hone : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-ε₀) := by
    rw [ENNReal.rpow_neg, ENNReal.one_le_inv]
    exact ENNReal.rpow_le_one hδE1 hε₀
  simp only [Finset.sum_singleton, Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
  calc volume (V i).shade = 1 * volume (V i).shade := (one_mul _).symm
    _ ≤ (δ : ENNReal) ^ (-ε₀) * volume (V i).shade := by gcongr

/-- **A one-element family refutes alternative (ii) of the dichotomy.**

`μ = 1` while `δ^{g}|𝕋|^{β} = δ^{g} < 1` for `g > 0`, so the gain branch cannot be asked for on its
own below `δ^{-1}`: this is why `Kakeya.ML2Band.BandDichotomy` is a disjunction and not the bare
inequality `μ ≤ δ^{g}|𝕋|^{β}`. -/
theorem singleton_fails_gain (i : ι) (V : ι → ShadedBody E) (hv : volume (V i).shade ≠ 0)
    {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1) {g β : ℝ} (hg : 0 < g) :
    ¬ (∑ j ∈ ({i} : Finset ι), volume (V j).shade
        ≤ (δ : ENNReal) ^ g * (({i} : Finset ι).card : ENNReal) ^ β *
            volume (⋃ j ∈ ({i} : Finset ι), (V j).shade)) := by
  have hvtop : volume (V i).shade ≠ ⊤ :=
    ne_top_of_le_ne_top (V i).isCompact.measure_ne_top (measure_mono (V i).shade_subset)
  have hδE0 : (0 : ENNReal) < (δ : ENNReal) := by exact_mod_cast hδ0
  have hδE1 : (δ : ENNReal) < 1 := by exact_mod_cast hδ1
  have hlt : (δ : ENNReal) ^ g < 1 := by
    calc (δ : ENNReal) ^ g < (δ : ENNReal) ^ (0 : ℝ) :=
          ENNReal.rpow_lt_rpow_of_exponent_gt hδE0 hδE1 hg
      _ = 1 := ENNReal.rpow_zero
  intro h
  simp only [Finset.sum_singleton, Finset.mem_singleton, Set.iUnion_iUnion_eq_left,
    Finset.card_singleton, Nat.cast_one, ENNReal.one_rpow, mul_one] at h
  have hcontr : volume (V i).shade < volume (V i).shade := by
    calc volume (V i).shade ≤ (δ : ENNReal) ^ g * volume (V i).shade := h
      _ = volume (V i).shade * (δ : ENNReal) ^ g := mul_comm _ _
      _ < volume (V i).shade * 1 := ENNReal.mul_lt_mul_right hv hvtop hlt
      _ = volume (V i).shade := mul_one _
  exact absurd hcontr (lt_irrefl _)

end Singleton

end Kakeya.ML2Band
