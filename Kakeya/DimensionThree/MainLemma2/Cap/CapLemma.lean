/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Cap.LargeOne
public import Kakeya.DimensionThree.MainLemma2.Cap.BroadBound
public import Kakeya.DimensionThree.MainLemma2.Cap.NarrowMass

/-!
# The cap induction of the Cap Lemma

This file assembles the bilinear broad--narrow **cap induction** whose endpoint is the Cap Lemma
`L(γ) ⇒ K_KT(γ)` . It combines the following estimates:

* `Kakeya.ML2Cap.KatzTaoEstimateLargeOne` and `Kakeya.ML2Cap.Arith.*`
  (`Cap/LargeOne.lean`, `Cap/Arith.lean`);
* the pointwise broad/narrow decomposition, `Kakeya.CapBroadNarrow.*`
  (`Cap/BroadNarrow.lean`);
* the bilinear broad bound, `Kakeya.CapBroadBound.exists_broad_level_const`
  (`Cap/BroadBound.lean`);
* the narrow mass accounting, `Kakeya.CapBroadNarrow.mult_le_max_caps_of_lintegral` and
  `Kakeya.CapBroadNarrow.broad_or_narrow_dominated` (`Cap/NarrowMass.lean`).

## The shape of the induction

`Kakeya.ML2Cap.LevelData` is the numerical data of one level: a scale `δ_k`, a Katz--Tao bound,
a fullness floor, and a *budget* `M_k` such that the level's claim
(`Kakeya.ML2Cap.LevelData.Holds`) is

  every family of `δ_k`-tubes in `B₁` inside those two bounds has `μ ≤ M_k · |𝕋|^γ`.

The budget is a multiple of the level's **own** cardinality, not of the level-`0` cardinality.
That is deliberate and it is what removes `N` from the whole bookkeeping: the cap subfamilies of
the narrow-mass estimate are `Finset`-subsets of the family (`capFamily_subset`), so `|𝕋_{k+1}| ≤ |𝕋_k|` and
the level-`k` conclusion follows from the level-`(k+1)` one with no reference to the original
family.

`Kakeya.ML2Cap.level_step` is one step, and it is a three-way case split on the level's family:

* **(a) the large leaf** (`Kakeya.ML2Cap.level_large`), `|𝕋| ≥ δ_k⁻¹`: the large-family estimate
  `L(γ)`, read at the level's own scale, closes the level outright. `Kakeya.ML2Cap.LargeOneAt` is
  the body of `Kakeya.ML2Cap.KatzTaoEstimateLargeOne` at a fixed scale, and
  `Kakeya.ML2Cap.largeOne_iff_eventually_largeOneAt` is `Iff.rfl` — a token-copy certificate, so
  the two cannot drift apart without breaking this file.
* **(b) the bottom** (`Kakeya.ML2Cap.level_bottom`), at the last level with `|𝕋| < δ_{k*}⁻¹`: the
  trivial bound `μ ≤ |𝕋|` (`ShadedBody.multiplicity_le_card`) already fits inside the budget.
  `Kakeya.ML2Cap.level_last` is (a) and (b) together.
* **(c) broad/narrow** at angular scale `θ = δ_k^c` and cap radius `4θ`, split by `Kakeya.CapBroadNarrow.broad_or_narrow_dominated`:
  - broad (`Kakeya.ML2Cap.level_broad`) uses `exists_broad_level_const`, unchanged;
  - narrow uses the cap pigeonhole `mult_le_max_caps_of_lintegral` at threshold
    `λ_k / (8 C_P)` — a factor `8` — followed by the **seam** below, a factor `2`. So the
    induction loses `16` per level, and `Kakeya.ML2Cap.capFactor_narrow` shows the canonical
    budget `M_k = 16^{k*-k} δ^{-ε/2}` absorbs exactly that.

## The one named hypothesis: the cap-rescaling seam

`Kakeya.ML2Cap.CapSeam` is the *only* hypothesis of `level_step` that this file does not
discharge. It says: a family localised to a `4θ`-cap about a unit direction `p`, inside `B₁`, at
the level's Katz--Tao bound and with fullness at least `λ_k/(8 C_P)`, has multiplicity at most
`2 ·` the next level's budget, given the next level's claim. It is the composite of

* cap rescaling (`Kakeya.CapRescale.exists_capRescaledFamily` in
  `Cap/Rescale.lean`), which transports multiplicity exactly and costs
  `capLoss = (4 * 64)^6` on fullness and on `Δ_max`; and
* the geometric column construction: measurable columns are instantiated
  by `Kakeya.CapRescale.IsCapColumn`. Its incidence count is `K = 9`,
  giving `72 = 8 * 9`, and `mult_cap_le_max_columns` contributes the
  column factor `2` by taking `b = 1`.

These geometric declarations are references to separate modules, outside
this module's import closure. Stating the composite as one named `Prop` is what keeps the seam a single statement rather
than a silent mismatch.

## The scheme, and what remains

`Kakeya.ML2Cap.CapScheme` bundles the level sequence with every side condition the induction
uses, and `Kakeya.ML2Cap.katzTaoEstimate_of_largeOne_of_scheme` proves the Cap Lemma from a
*producer* of schemes: `L(γ)` plus, for every accuracy `ε`, a scheme eventually in `δ`. The
numeric core of a scheme is supplied here —

* `Kakeya.ML2Cap.capFactor` and its four lemmas (`capFactor_large`, `capFactor_broad`,
  `capFactor_bottom`, `capFactor_narrow`, `capFactor_entry_of_le`) discharge all five budget
  conditions for the canonical budget, the last of them from
  `Kakeya.ML2Cap.Arith.total_loss` at the per-level constant `16`;
* `Kakeya.ML2Cap.capBottom_cond` is the bottom-level side condition from a scale floor;
* `Kakeya.ML2Cap.capEta` is the exponent the assembly runs at, and
  `Kakeya.ML2Cap.capEta_le_plan` compares it with the plan's `(ε/2)·min(η_L, 3γ/4)/8`.

A scheme producer supplies: the scale
sequence `δ_k` with `δ ≤ δ_k ≤ δ^{(1-c)^k}` (`capScale` iterated, which carries a factor
`1/16` per level), the Katz--Tao and fullness sequences `C₁^k δ^{-η}` and `c₁^k δ^{η}` with the
eventual absorptions `C₁^{k*} ≤ δ^{-η}` and `c₁^{-k*} ≤ δ^{-η}`, the availability of `L(γ)` at
every level scale (through `Kakeya.StickyKakeya.exists_threshold_of_eventually_nhdsGT`), and the
seam.

## Where the gain is, and where it is not

`Kakeya.ML2Cap.Arith.broad_level`'s `c ≤ γ` binder is unused in that estimate, so this file takes the broad bound
from `Kakeya.CapBroadBound.exists_broad_level_const` — which keeps the `δ_k^{γ-c}` factor
explicit — and never from `broad_level_mult_le_of_gain`. The one place a sign statement is used
is `Kakeya.ML2Cap.capFactor_broad`, through `Kakeya.ML2Cap.Arith.gain_is_positive_power`, and it
is used only as `δ_k^{γ-c} ≤ 1`. With the per-level
fullness and `Δ_max` losses carried by the seam (where the rescaling pays them) rather than by the
broad bound, the positive power `δ_k^{3γ/4}` is slack the accounting does not need to spend, and
the `ε/2` half of the outer budget covers `C₃` and `λ_k^{-2}` on its own. A successor that moves
those losses back out of the seam will need it.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology ConvexSpaceBody
open Kakeya.CapBroadNarrow Kakeya.CapBroadBound
open scoped NNReal ENNReal

namespace Kakeya.ML2Cap

universe u v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Level data -/

/-- The numerical data of one level of the cap induction. -/
structure LevelData where
  /-- The scale of the level. -/
  scale : NNReal
  /-- The Katz--Tao bound of the level. -/
  ktBound : ENNReal
  /-- The fullness lower bound of the level. -/
  full : NNReal
  /-- The multiplicity bound of the level, as a factor of `|𝕋| ^ γ`. -/
  factor : ENNReal

/-- The level statement. -/
def LevelData.Holds (L : LevelData) (E : Type v) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (γ : ℝ) : Prop :=
  ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube L.scale E),
    (∀ i ∈ s, (T i).carrier ⊆ closedBall 0 1) →
    IsKatzTao s (fun i => (T i).toConvexSpaceBody) L.ktBound →
    L.full ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody) →
    ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
      ≤ L.factor * (s.card : ENNReal) ^ γ

/-! ## The estimate at a fixed scale -/

/-- The body of `Kakeya.KatzTaoEstimate` at a fixed scale. -/
def EstimateAt (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (δ : NNReal) (ε γ η : ℝ) : Prop :=
  ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
    (∀ i ∈ s, (T i).carrier ⊆ closedBall 0 1) →
    IsKatzTao s (fun i => (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
    ShadedBody.fullness s (fun i => (T i).toShadedBody) ≥ δ ^ η →
    ∑ i ∈ s, volume (T i).shade
      ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (T i).shade)

/-- The body of `Kakeya.ML2Cap.KatzTaoEstimateLargeOne` at a fixed scale. -/
def LargeOneAt (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (δ : NNReal) (ε γ η : ℝ) : Prop :=
  ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
    (∀ i ∈ s, (T i).carrier ⊆ closedBall 0 1) →
    IsKatzTao s (fun i => (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
    ShadedBody.fullness s (fun i => (T i).toShadedBody) ≥ δ ^ η →
    (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
    ∑ i ∈ s, volume (T i).shade
      ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (T i).shade)

theorem katzTaoEstimate_iff_eventually_estimateAt (γ : ℝ) :
    KatzTaoEstimate.{u} E γ ↔
      ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0, EstimateAt.{u} E δ ε γ η :=
  Iff.rfl

theorem largeOne_iff_eventually_largeOneAt (γ : ℝ) :
    KatzTaoEstimateLargeOne.{u} E γ ↔
      ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0, LargeOneAt.{u} E δ ε γ η :=
  Iff.rfl


/-! ## Case (a): the large leaf -/

/-- **Case (a) of `level_step`: the large leaf.**  At a level whose family is large
(`|𝕋| ≥ δ_k⁻¹`) the large-family estimate `L(γ)`, read at the level's own scale, closes the
level outright. -/
theorem level_large {L : LevelData} {γ ε ηL : ℝ}
    (hL : LargeOneAt.{u} E L.scale ε γ ηL)
    (hkt : L.ktBound ≤ (L.scale : ENNReal) ^ (-ηL))
    (hfull : (L.scale : NNReal) ^ ηL ≤ L.full)
    (hfac : (L.scale : ENNReal) ^ (-ε) ≤ L.factor)
    {ι : Type u} (s : Finset ι) (T : ι → ShadedTube L.scale E)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ closedBall 0 1)
    (hKT : IsKatzTao s (fun i => (T i).toConvexSpaceBody) L.ktBound)
    (hfl : L.full ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody))
    (hcard : (L.scale : ℝ)⁻¹ ≤ (s.card : ℝ)) :
    ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
      ≤ L.factor * (s.card : ENNReal) ^ γ := by
  have hsum := hL s T hball (hKT.mono hkt) (le_trans hfull hfl) hcard
  rw [ShadedBody.multiplicity_le_iff]
  refine hsum.trans ?_
  gcongr

/-! ## Case (b): the bottom level -/

/-- **Case (b) of the induction: the bottom level.**  At the bottom the trivial bound
`μ ≤ |𝕋|` already fits inside the level's budget, because the level is only reached with
`|𝕋| < δ_k⁻¹`. -/
theorem level_bottom {L : LevelData} {γ : ℝ} (hγ1 : γ ≤ 1)
    (hscale : 0 < L.scale)
    (hfac : ENNReal.ofReal (((L.scale : ℝ)⁻¹) ^ (1 - γ)) ≤ L.factor)
    {ι : Type u} (s : Finset ι) (T : ι → ShadedTube L.scale E)
    (hcard : (s.card : ℝ) ≤ (L.scale : ℝ)⁻¹) :
    ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
      ≤ L.factor * (s.card : ENNReal) ^ γ := by
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · have hs : s = ∅ := Finset.card_eq_zero.mp h0
    subst hs
    simp
  have hcard1 : (1 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hpos
  have hM0 : (0 : ℝ) < (L.scale : ℝ)⁻¹ := by
    have : (0 : ℝ) < (L.scale : ℝ) := NNReal.coe_pos.mpr hscale
    positivity
  have hsplit : ((s.card : ENNReal)) = (s.card : ENNReal) ^ (1 - γ) * (s.card : ENNReal) ^ γ := by
    rw [← ENNReal.rpow_add _ _ (by exact_mod_cast hpos.ne') (by simp)]
    simp
  have hstep : (s.card : ENNReal) ^ (1 - γ) ≤ ENNReal.ofReal (((L.scale : ℝ)⁻¹) ^ (1 - γ)) := by
    have hle : ((s.card : ℝ)) ^ (1 - γ) ≤ ((L.scale : ℝ)⁻¹) ^ (1 - γ) :=
      Real.rpow_le_rpow (by positivity) hcard (by linarith)
    calc (s.card : ENNReal) ^ (1 - γ)
        = ENNReal.ofReal (((s.card : ℝ)) ^ (1 - γ)) := by
          rw [← ENNReal.ofReal_natCast s.card,
            ENNReal.ofReal_rpow_of_pos (by positivity)]
      _ ≤ ENNReal.ofReal (((L.scale : ℝ)⁻¹) ^ (1 - γ)) := ENNReal.ofReal_le_ofReal hle
  calc ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
      ≤ (s.card : ENNReal) := ShadedBody.multiplicity_le_card s _
    _ = (s.card : ENNReal) ^ (1 - γ) * (s.card : ENNReal) ^ γ := hsplit
    _ ≤ L.factor * (s.card : ENNReal) ^ γ := by gcongr; exact hstep.trans hfac


/-! ## Case (c), broad half -/

/-- The broad level bound of band item A3, as a property of the constant `C₃`; the body of
`Kakeya.CapBroadBound.exists_broad_level_const`. -/
def IsBroadLevelConst (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (C₃ : ℝ) : Prop :=
  ∀ {δ : NNReal}, 0 < δ → δ ≤ 1 → ∀ {θ γ c : ℝ}, 0 ≤ c → c ≤ γ → γ ≤ 1 →
      θ = (δ : ℝ) ^ c → ∀ (P : DirNet E θ), P.points.Nonempty →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
        1 ≤ (s.card : ℝ) → (s.card : ℝ) ≤ (δ : ℝ)⁻¹ →
      ∀ {l : NNReal}, 0 < l → l ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody) →
      (∑ i ∈ s, volume (T i).shade
        ≤ 2 * ∫⁻ x in broadSet P.points s T (4 * θ), ((mult s T x : ℕ) : ENNReal)) →
      ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
        ≤ ENNReal.ofReal (C₃ * ((s.card : ℝ) ^ γ * (δ : ℝ) ^ (γ - c) * (((l : ℝ) ^ 2)⁻¹)))

/-- Band item A3 supplies a broad level constant. -/
theorem exists_isBroadLevelConst (hn : 1 < Module.finrank ℝ E) :
    ∃ C₃ : ℝ, 0 < C₃ ∧ IsBroadLevelConst.{u} E C₃ :=
  exists_broad_level_const hn

/-- **Case (c) of `level_step`, broad half.**  If at least half the shade mass sits on the broad
set of the level's net, band item A3 closes the level with no recursion at all. -/
theorem level_broad {L : LevelData} {γ c C₃ θ : ℝ}
    (hB : IsBroadLevelConst.{u} E C₃) (hC₃ : 0 ≤ C₃)
    (hδ0 : 0 < L.scale) (hδ1 : L.scale ≤ 1) (hc0 : 0 ≤ c) (hcγ : c ≤ γ) (hγ1 : γ ≤ 1)
    (hθ : θ = (L.scale : ℝ) ^ c) (P : DirNet E θ) (hP : P.points.Nonempty)
    (hl0 : 0 < L.full)
    (hfac : ENNReal.ofReal (C₃ * ((L.scale : ℝ) ^ (γ - c) * (((L.full : ℝ) ^ 2)⁻¹)))
      ≤ L.factor)
    {ι : Type u} (s : Finset ι) (T : ι → ShadedTube L.scale E)
    (hcard1 : 1 ≤ (s.card : ℝ)) (hcardδ : (s.card : ℝ) ≤ (L.scale : ℝ)⁻¹)
    (hfl : L.full ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody))
    (hdom : ∑ i ∈ s, volume (T i).shade
      ≤ 2 * ∫⁻ x in broadSet P.points s T (4 * θ), ((mult s T x : ℕ) : ENNReal)) :
    ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
      ≤ L.factor * (s.card : ENNReal) ^ γ := by
  have hbnd := hB hδ0 hδ1 hc0 hcγ hγ1 hθ P hP s T hcard1 hcardδ hl0 hfl hdom
  refine hbnd.trans ?_
  have hcard0 : (0 : ℝ) < (s.card : ℝ) := by linarith
  have hrw : (s.card : ENNReal) ^ γ = ENNReal.ofReal ((s.card : ℝ) ^ γ) := by
    rw [← ENNReal.ofReal_natCast s.card, ENNReal.ofReal_rpow_of_pos hcard0]
  rw [hrw]
  have hsplit : C₃ * ((s.card : ℝ) ^ γ * (L.scale : ℝ) ^ (γ - c) * (((L.full : ℝ) ^ 2)⁻¹))
      = (C₃ * ((L.scale : ℝ) ^ (γ - c) * (((L.full : ℝ) ^ 2)⁻¹))) * ((s.card : ℝ) ^ γ) := by
    ring
  have hpow : (0 : ℝ) ≤ (L.scale : ℝ) ^ (γ - c) := Real.rpow_nonneg (by positivity) _
  rw [hsplit, ENNReal.ofReal_mul (by positivity)]
  gcongr


/-! ## The A5 seam and one level of the induction -/

/-- **The cap-rescaling seam (band item A5 plus the A4-to-A5 column bridge).** -/
def CapSeam (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L L' : LevelData) (γ c : ℝ) : Prop :=
  ∀ {ι : Type u} (u : Finset ι) (W : ι → ShadedTube L.scale E) (p : E), ‖p‖ = 1 →
    (∀ i ∈ u, (W i).carrier ⊆ closedBall 0 1) →
    (∀ i ∈ u, dirDist (W i).direction p ≤ 4 * (L.scale : ℝ) ^ c) →
    IsKatzTao u (fun i => (W i).toConvexSpaceBody) L.ktBound →
    (L.full : ENNReal) / (8 * capPackingConst E)
      ≤ (ShadedBody.fullness u (fun i => (W i).toShadedBody) : ENNReal) →
    L'.Holds.{u} E γ →
    ShadedBody.multiplicity u (fun i => (W i).toShadedBody)
      ≤ 2 * (L'.factor * (u.card : ENNReal) ^ γ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Every direction net over a nontrivial space has a point. -/
theorem dirNet_points_nonempty [Nontrivial E] {θ : ℝ} (P : DirNet E θ) :
    P.points.Nonempty := by
  obtain ⟨w, hw⟩ : ∃ w : E, ‖w‖ = 1 := exists_norm_eq E (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨q, hq, -⟩ := P.cover w hw
  exact ⟨q, hq⟩

/-- **One level of the cap induction.** -/
theorem level_step {L L' : LevelData} {γ c C₃ ε ηL : ℝ}
    (hn : 1 < Module.finrank ℝ E)
    (hc0 : 0 ≤ c) (hcγ : c ≤ γ) (hγ1 : γ ≤ 1)
    (hδ0 : 0 < L.scale) (hδ1 : L.scale ≤ 1) (hl0 : 0 < L.full)
    (hLA : LargeOneAt.{u} E L.scale ε γ ηL)
    (hkt : L.ktBound ≤ (L.scale : ENNReal) ^ (-ηL))
    (hfullA : (L.scale : NNReal) ^ ηL ≤ L.full)
    (hfacA : (L.scale : ENNReal) ^ (-ε) ≤ L.factor)
    (hB : IsBroadLevelConst.{u} E C₃) (hC₃ : 0 ≤ C₃)
    (hfacB : ENNReal.ofReal (C₃ * ((L.scale : ℝ) ^ (γ - c) * (((L.full : ℝ) ^ 2)⁻¹)))
      ≤ L.factor)
    (hseam : CapSeam.{u} E L L' γ c)
    (hfacN : 16 * L'.factor ≤ L.factor)
    (hnext : L'.Holds.{u} E γ) :
    L.Holds.{u} E γ := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (lt_trans Nat.zero_lt_one hn)
  have hγ0 : 0 ≤ γ := le_trans hc0 hcγ
  have hδ0r : (0 : ℝ) < (L.scale : ℝ) := NNReal.coe_pos.mpr hδ0
  have hδ1r : (L.scale : ℝ) ≤ 1 := NNReal.coe_le_one.mpr hδ1
  intro ι s T hball hKT hfl
  by_cases hlarge : (L.scale : ℝ)⁻¹ ≤ (s.card : ℝ)
  · exact level_large hLA hkt hfullA hfacA s T hball hKT hfl hlarge
  rw [not_le] at hlarge
  have hcardδ : (s.card : ℝ) ≤ (L.scale : ℝ)⁻¹ := hlarge.le
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · have hs : s = ∅ := Finset.card_eq_zero.mp h0
    subst hs; simp
  have hcard1 : (1 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hpos
  -- the level's angular scale and net
  set θ : ℝ := (L.scale : ℝ) ^ c with hθ
  have hθ0 : 0 < θ := Real.rpow_pos_of_pos hδ0r c
  have hθ1 : θ ≤ 1 := Real.rpow_le_one hδ0r.le hδ1r hc0
  obtain ⟨P⟩ := exists_dirNet (E := E) hθ0 hθ1
  have hP : P.points.Nonempty := dirNet_points_nonempty P
  rcases broad_or_narrow_dominated P.points s T (4 * θ) with hbroad | hnar
  · exact level_broad hB hC₃ hδ0 hδ1 hc0 hcγ hγ1 hθ P hP hl0 hfacB s T hcard1 hcardδ hfl hbroad
  -- narrow: A4's cap pigeonhole, then the seam
  have hM : (∑ i ∈ s, volume (T i).shade) ≠ 0 :=
    ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos s _ (lt_of_lt_of_le hl0 hfl)
  obtain ⟨k, hcapfull, hcapmult⟩ :=
    mult_le_max_caps_of_lintegral (E := E) hθ0 P (le_refl (4 * θ)) s T
      (t := (L.full : ENNReal) / (8 * capPackingConst E))
      (le_trans ENNReal.mul_div_le (ENNReal.coe_le_coe.mpr hfl)) hM hnar
  set pk : E := netEnum P.points k with hpk
  set u : Finset ι := capFamily s T pk (4 * θ) with hu
  set A : Set E := narrowPart P.points s T (4 * θ) k with hA
  have hAmeas : MeasurableSet A := measurableSet_narrowPart P.points s T (4 * θ) k
  set W : ι → ShadedTube L.scale E := capShadeFam T A hAmeas with hW
  have husub : u ⊆ s := capFamily_subset s T pk (4 * θ)
  have hpnorm : ‖pk‖ = 1 := P.norm_eq_one _ (netEnum_mem P.points k)
  have hWball : ∀ i ∈ u, (W i).carrier ⊆ closedBall 0 1 := by
    intro i hi
    simpa [hW] using hball i (husub hi)
  have hWdir : ∀ i ∈ u, dirDist (W i).direction pk ≤ 4 * (L.scale : ℝ) ^ c := by
    intro i hi
    have := (mem_capFamily.1 (by simpa [hu] using hi)).2
    simpa [hW, hθ] using this
  have hWkt : IsKatzTao u (fun i => (W i).toConvexSpaceBody) L.ktBound := by
    simpa [hW] using hKT.subset husub
  have hseamout := hseam u W pk hpnorm hWball hWdir hWkt (by simpa [hW, hu, hA] using hcapfull)
    hnext
  have hcardu : (u.card : ENNReal) ≤ (s.card : ENNReal) :=
    Nat.cast_le.mpr (Finset.card_le_card husub)
  calc ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
      ≤ 8 * ShadedBody.multiplicity u (fun i => (W i).toShadedBody) := by
        simpa [hW, hu, hA] using hcapmult
    _ ≤ 8 * (2 * (L'.factor * (u.card : ENNReal) ^ γ)) := by gcongr
    _ = (16 * L'.factor) * (u.card : ENNReal) ^ γ := by ring
    _ ≤ L.factor * (s.card : ENNReal) ^ γ := by gcongr


/-! ## The last level, and the downward induction -/

/-- **The bottom level of the induction**, cases (a) and (b) together. -/
theorem level_last {L : LevelData} {γ ε ηL : ℝ} (hγ1 : γ ≤ 1) (hδ0 : 0 < L.scale)
    (hLA : LargeOneAt.{u} E L.scale ε γ ηL)
    (hkt : L.ktBound ≤ (L.scale : ENNReal) ^ (-ηL))
    (hfullA : (L.scale : NNReal) ^ ηL ≤ L.full)
    (hfacA : (L.scale : ENNReal) ^ (-ε) ≤ L.factor)
    (hfacBot : ENNReal.ofReal (((L.scale : ℝ)⁻¹) ^ (1 - γ)) ≤ L.factor) :
    L.Holds.{u} E γ := by
  intro ι s T hball hKT hfl
  by_cases hlarge : (L.scale : ℝ)⁻¹ ≤ (s.card : ℝ)
  · exact level_large hLA hkt hfullA hfacA s T hball hKT hfl hlarge
  · rw [not_le] at hlarge
    exact level_bottom hγ1 hδ0 hfacBot s T hlarge.le

/-- **The downward induction over the levels.** -/
theorem levels_holds {γ : ℝ} (L : ℕ → LevelData) (K : ℕ)
    (hbot : (L K).Holds.{u} E γ)
    (hstep : ∀ k, k < K → (L (k + 1)).Holds.{u} E γ → (L k).Holds.{u} E γ) :
    (L 0).Holds.{u} E γ := by
  have key : ∀ j k, k + j = K → (L k).Holds.{u} E γ := by
    intro j
    induction j with
    | zero =>
      intro k hk
      obtain rfl : k = K := by omega
      exact hbot
    | succ j ih =>
      intro k hk
      exact hstep k (by omega) (ih (k + 1) (by omega))
  intro ι s T
  exact key K 0 (by simp) s T

/-! ## The scheme, and the Cap Lemma modulo the scheme -/

/-- **A cap level scheme.** -/
structure CapScheme (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (γ ε η ηL C₃ : ℝ) (δ : NNReal) where
  /-- The depth `k*` of the induction. -/
  depth : ℕ
  /-- The angular exponent `c`. -/
  cexp : ℝ
  /-- The level data. -/
  level : ℕ → LevelData
  /-- `0 ≤ c`. -/
  cexp_nonneg : 0 ≤ cexp
  /-- `c ≤ γ`: the angular loss is paid by the cardinality-weighted target. -/
  cexp_le : cexp ≤ γ
  /-- Every level scale is positive. -/
  scale_pos : ∀ k ≤ depth, 0 < (level k).scale
  /-- Every level scale is at most `1`. -/
  scale_le_one : ∀ k ≤ depth, (level k).scale ≤ 1
  /-- Every level's fullness floor is positive. -/
  full_pos : ∀ k ≤ depth, 0 < (level k).full
  /-- The large-family estimate `L(γ)` holds at every level scale, at accuracy `ε/2`. -/
  large : ∀ k ≤ depth, LargeOneAt.{u} E (level k).scale (ε / 2) γ ηL
  /-- The level's Katz--Tao bound is inside `L(γ)`'s hypothesis at the level's scale. -/
  kt_le : ∀ k ≤ depth, (level k).ktBound ≤ ((level k).scale : ENNReal) ^ (-ηL)
  /-- The level's fullness floor is inside `L(γ)`'s hypothesis at the level's scale. -/
  full_ge : ∀ k ≤ depth, ((level k).scale : NNReal) ^ ηL ≤ (level k).full
  /-- The level's budget covers the large leaf. -/
  factor_large : ∀ k ≤ depth, ((level k).scale : ENNReal) ^ (-(ε / 2)) ≤ (level k).factor
  /-- The level's budget covers the broad case. -/
  factor_broad : ∀ k ≤ depth,
    ENNReal.ofReal (C₃ * (((level k).scale : ℝ) ^ (γ - cexp)
      * ((((level k).full : ℝ)) ^ 2)⁻¹)) ≤ (level k).factor
  /-- The cap-rescaling seam, at every non-bottom level. -/
  seam : ∀ k < depth, CapSeam.{u} E (level k) (level (k + 1)) γ cexp
  /-- The level's budget covers the narrow case: the induction loses a factor `16` per level. -/
  factor_narrow : ∀ k < depth, 16 * (level (k + 1)).factor ≤ (level k).factor
  /-- The bottom level's budget covers the trivial bound. -/
  factor_bottom :
    ENNReal.ofReal ((((level depth).scale : ℝ)⁻¹) ^ (1 - γ)) ≤ (level depth).factor
  /-- Level `0` is the given scale. -/
  entry_scale : (level 0).scale = δ
  /-- Level `0`'s Katz--Tao bound is implied by the target's. -/
  entry_kt : (δ : ENNReal) ^ (-η) ≤ (level 0).ktBound
  /-- Level `0`'s fullness floor is implied by the target's. -/
  entry_full : (level 0).full ≤ (δ : NNReal) ^ η
  /-- Level `0`'s budget is inside the target's. -/
  entry_factor : (level 0).factor ≤ (δ : ENNReal) ^ (-ε)

/-- Every level of a scheme holds, by the downward induction. -/
theorem CapScheme.level_zero_holds {γ ε η ηL C₃ : ℝ} {δ : NNReal}
    (hn : 1 < Module.finrank ℝ E) (hγ1 : γ ≤ 1)
    (hB : IsBroadLevelConst.{u} E C₃) (hC₃ : 0 ≤ C₃)
    (sch : CapScheme.{u} E γ ε η ηL C₃ δ) :
    (sch.level 0).Holds.{u} E γ := by
  refine levels_holds (γ := γ) sch.level sch.depth ?_ ?_
  · exact level_last hγ1 (sch.scale_pos _ le_rfl) (sch.large _ le_rfl) (sch.kt_le _ le_rfl)
      (sch.full_ge _ le_rfl) (sch.factor_large _ le_rfl) sch.factor_bottom
  · intro k hk hnext
    exact level_step hn sch.cexp_nonneg sch.cexp_le hγ1 (sch.scale_pos _ hk.le)
      (sch.scale_le_one _ hk.le) (sch.full_pos _ hk.le) (sch.large _ hk.le) (sch.kt_le _ hk.le)
      (sch.full_ge _ hk.le) (sch.factor_large _ hk.le) hB hC₃ (sch.factor_broad _ hk.le)
      (sch.seam k hk) (sch.factor_narrow k hk) hnext

/-- A level statement at the target's own scale is the target's fixed-scale estimate. -/
theorem estimateAt_of_holds {δ : NNReal} {L : LevelData} {γ ε η : ℝ} (hs : L.scale = δ)
    (hkt : (δ : ENNReal) ^ (-η) ≤ L.ktBound) (hfull : L.full ≤ (δ : NNReal) ^ η)
    (hfac : L.factor ≤ (δ : ENNReal) ^ (-ε))
    (h : L.Holds.{u} E γ) : EstimateAt.{u} E δ ε γ η := by
  subst hs
  intro ι s T hball hKT hfl
  have hb := h s T hball (hKT.mono hkt) (le_trans hfull hfl)
  rw [ShadedBody.multiplicity_le_iff] at hb
  exact hb.trans (mul_le_mul_left (mul_le_mul_left hfac _) _)

/-- **The Cap Lemma, modulo the level scheme.** -/
theorem katzTaoEstimate_of_largeOne_of_scheme {γ : ℝ} (hn : 1 < Module.finrank ℝ E)
    (hγ1 : γ ≤ 1)
    (hL : KatzTaoEstimateLargeOne.{u} E γ)
    (hprod : ∀ ε > (0 : ℝ), ∀ ηL C₃ : ℝ, 0 < ηL → 0 < C₃ → IsBroadLevelConst.{u} E C₃ →
      (∀ᶠ (d : NNReal) in 𝓝[>] 0, LargeOneAt.{u} E d (ε / 2) γ ηL) →
      ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
        Nonempty (CapScheme.{u} E γ ε η ηL C₃ δ)) :
    KatzTaoEstimate.{u} E γ := by
  intro ε hε
  obtain ⟨C₃, hC₃, hB⟩ := exists_isBroadLevelConst.{u} (E := E) hn
  obtain ⟨ηL, hηL, hev⟩ := hL (ε / 2) (by linarith)
  obtain ⟨η, hη, hsch⟩ := hprod ε hε ηL C₃ hηL hC₃ hB hev
  refine ⟨η, hη, ?_⟩
  filter_upwards [hsch] with δ hδ
  obtain ⟨sch⟩ := hδ
  exact estimateAt_of_holds sch.entry_scale sch.entry_kt sch.entry_full sch.entry_factor
    (sch.level_zero_holds hn hγ1 hB hC₃.le)


/-! ## The canonical budget sequence, and the total loss -/

/-- `(δ : ℝ≥0∞) ^ p` as an `ENNReal.ofReal`. -/
theorem coe_rpow_eq_ofReal {δ : NNReal} (hδ : 0 < δ) (p : ℝ) :
    (δ : ENNReal) ^ p = ENNReal.ofReal ((δ : ℝ) ^ p) := by
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_pos (NNReal.coe_pos.mpr hδ)]

/-- **The canonical budget sequence of the cap induction**, `M_k = 16^{k*-k} · δ^{-ε/2}`. -/
noncomputable def capFactor (δ : NNReal) (ε : ℝ) (K k : ℕ) : ENNReal :=
  16 ^ (K - k) * (δ : ENNReal) ^ (-(ε / 2))

/-- **The narrow step is exact for the canonical budget.** -/
theorem capFactor_narrow (δ : NNReal) (ε : ℝ) {K k : ℕ} (hk : k < K) :
    16 * capFactor δ ε K (k + 1) ≤ capFactor δ ε K k := by
  have hsucc : K - k = (K - (k + 1)) + 1 := by omega
  rw [capFactor, capFactor, hsucc, pow_succ]
  ring_nf
  exact le_rfl

/-- **The canonical budget covers the large leaf at every level.** -/
theorem capFactor_large {δ d : NNReal} {ε : ℝ} {K k : ℕ} (hδd : δ ≤ d) (hε : 0 ≤ ε) :
    (d : ENNReal) ^ (-(ε / 2)) ≤ capFactor δ ε K k := by
  have hbase : (δ : ENNReal) ^ (ε / 2) ≤ (d : ENNReal) ^ (ε / 2) :=
    ENNReal.rpow_le_rpow (by exact_mod_cast hδd) (by linarith)
  have hstep : (d : ENNReal) ^ (-(ε / 2)) ≤ (δ : ENNReal) ^ (-(ε / 2)) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.mpr hbase
  refine hstep.trans ?_
  rw [capFactor]
  exact le_mul_of_one_le_left (by simp) (one_le_pow₀ (by norm_num))

/-- **The canonical budget covers the trivial bound at the bottom level.** -/
theorem capFactor_bottom {δ d : NNReal} {ε γ : ℝ} (K : ℕ) (hδ0 : 0 < δ)
    (h : ((d : ℝ)⁻¹) ^ (1 - γ) ≤ (δ : ℝ) ^ (-(ε / 2))) :
    ENNReal.ofReal (((d : ℝ)⁻¹) ^ (1 - γ)) ≤ capFactor δ ε K K := by
  rw [capFactor, Nat.sub_self, pow_zero, one_mul, coe_rpow_eq_ofReal hδ0]
  exact ENNReal.ofReal_le_ofReal h

/-- **The total loss of the induction is inside the outer accuracy.** -/
theorem capFactor_entry {δ : NNReal} {ε : ℝ} {K : ℕ} (hδ0 : 0 < δ)
    (h : (16 : ℝ) ^ (K : ℝ) * (δ : ℝ) ^ (-(ε / 2)) ≤ (δ : ℝ) ^ (-ε)) :
    capFactor δ ε K 0 ≤ (δ : ENNReal) ^ (-ε) := by
  rw [capFactor, Nat.sub_zero, coe_rpow_eq_ofReal hδ0, coe_rpow_eq_ofReal hδ0]
  have h16 : (16 : ENNReal) ^ K = ENNReal.ofReal ((16 : ℝ) ^ (K : ℝ)) := by
    rw [Real.rpow_natCast, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  rw [h16, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal h


/-- **The canonical budget covers the broad case.**  The `δ_k^{γ-c}` factor that band item A3
keeps explicit is used here *only* through `Kakeya.ML2Cap.Arith.gain_is_positive_power`, i.e.
only as `≤ 1`: with the per-level fullness and Katz--Tao losses carried by the seam rather than
by the broad bound, the positive power is slack the accounting does not have to spend. -/
theorem capFactor_broad {δ d l : NNReal} {ε γ c C₃ : ℝ} {K k : ℕ}
    (hd0 : 0 < d) (hd1 : d ≤ 1) (hcγ : c ≤ γ) (hC₃ : 0 ≤ C₃) (hδ0 : 0 < δ)
    (h : C₃ * (((l : ℝ)) ^ 2)⁻¹ ≤ (δ : ℝ) ^ (-(ε / 2))) :
    ENNReal.ofReal (C₃ * ((d : ℝ) ^ (γ - c) * (((l : ℝ)) ^ 2)⁻¹)) ≤ capFactor δ ε K k := by
  have hgain : (d : ℝ) ^ (γ - c) ≤ 1 :=
    Arith.gain_is_positive_power (NNReal.coe_pos.mpr hd0) (NNReal.coe_le_one.mpr hd1) hcγ
  have hgain0 : (0 : ℝ) ≤ (d : ℝ) ^ (γ - c) := Real.rpow_nonneg (by positivity) _
  have hchain : C₃ * ((d : ℝ) ^ (γ - c) * (((l : ℝ)) ^ 2)⁻¹) ≤ (δ : ℝ) ^ (-(ε / 2)) := by
    refine le_trans ?_ h
    have : (d : ℝ) ^ (γ - c) * (((l : ℝ)) ^ 2)⁻¹ ≤ (((l : ℝ)) ^ 2)⁻¹ := by
      nlinarith [inv_nonneg.mpr (sq_nonneg ((l : ℝ)))]
    exact mul_le_mul_of_nonneg_left this hC₃
  refine le_trans (ENNReal.ofReal_le_ofReal hchain) ?_
  rw [← coe_rpow_eq_ofReal hδ0, capFactor]
  exact le_mul_of_one_le_left (by simp) (one_le_pow₀ (by norm_num))

/-- **The bottom-level side condition, from the scale floor.**  At the bottom the family has
`|𝕋| < δ_{k*}⁻¹`, and `δ_{k*} ≥ δ^{a}` with `a (1-γ) ≤ ε/2` makes the trivial bound fit. -/
theorem capBottom_cond {δ d : NNReal} {ε γ a : ℝ} (hδ0 : 0 < δ) (hδ1 : (δ : ℝ) ≤ 1)
    (hγ1 : γ ≤ 1) (hd : (δ : ℝ) ^ a ≤ (d : ℝ)) (ha : a * (1 - γ) ≤ ε / 2) :
    ((d : ℝ)⁻¹) ^ (1 - γ) ≤ (δ : ℝ) ^ (-(ε / 2)) := by
  have hδ0r : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ0
  have hpa : (0 : ℝ) < (δ : ℝ) ^ a := Real.rpow_pos_of_pos hδ0r a
  have hd0 : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le hpa hd
  have hinv : (d : ℝ)⁻¹ ≤ ((δ : ℝ) ^ a)⁻¹ := by gcongr
  calc ((d : ℝ)⁻¹) ^ (1 - γ)
      ≤ (((δ : ℝ) ^ a)⁻¹) ^ (1 - γ) :=
        Real.rpow_le_rpow (by positivity) hinv (by linarith)
    _ = (δ : ℝ) ^ (-(a * (1 - γ))) := by
        rw [← Real.rpow_neg hδ0r.le, ← Real.rpow_mul hδ0r.le]
        congr 1
        ring
    _ ≤ (δ : ℝ) ^ (-(ε / 2)) :=
        Real.rpow_le_rpow_of_exponent_ge hδ0r hδ1 (by linarith)

/-- **The total loss over the whole induction**, from `Kakeya.ML2Cap.Arith.total_loss` at the
per-level constant `C_s = 16`: the assembled budget `16^{k*} δ^{-ε/2}` is inside `δ^{-ε}` for
every `δ ≤ 16^{-2k*/ε}`. -/
theorem capFactor_entry_of_le {δ : NNReal} {ε : ℝ} {K : ℕ} (hδ0 : 0 < δ) (hε : 0 < ε)
    (hδ : (δ : ℝ) ≤ (16 : ℝ) ^ (-(2 * (K : ℝ) / ε))) :
    capFactor δ ε K 0 ≤ (δ : ENNReal) ^ (-ε) :=
  capFactor_entry hδ0
    (Arith.total_loss (by norm_num) hε K (NNReal.coe_pos.mpr hδ0) hδ)

/-! ## The `η` of the assembly -/

/-- **The exponent the assembly runs at**, `η = (1-c)^{k*} · min(η_L, 3γ/4) / 8` at `c = γ/4`. -/
noncomputable def capEta (γ ηL : ℝ) (K : ℕ) : ℝ := (1 - γ / 4) ^ K * min ηL (3 * γ / 4) / 8

theorem capEta_pos {γ ηL : ℝ} {K : ℕ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hηL : 0 < ηL) :
    0 < capEta γ ηL K := by
  have h1 : (0 : ℝ) < 1 - γ / 4 := by nlinarith
  have h2 : (0 : ℝ) < min ηL (3 * γ / 4) := lt_min hηL (by nlinarith)
  have := pow_pos h1 K
  rw [capEta]
  positivity

/-- **The `η` achieved, against the plan's `(ε/2)·min(η_L, 3γ/4)/8`.**  At any depth `k*` with
`(1-γ/4)^{k*} ≤ ε/2` — which is what `Kakeya.ML2Cap.Arith.exists_depth` provides — the achieved
`η` is at most the plan's, and equals it up to the factor `(1-γ/4)^{k*}/(ε/2) ∈ (1-γ/4, 1]` when
`k*` is least. -/
theorem capEta_le_plan {γ ε ηL : ℝ} {K : ℕ} (hηL : 0 < ηL) (hγ0 : 0 < γ)
    (hdepth : (1 - γ / 4) ^ K ≤ ε / 2) :
    capEta γ ηL K ≤ (ε / 2) * min ηL (3 * γ / 4) / 8 := by
  have h2 : (0 : ℝ) < min ηL (3 * γ / 4) := lt_min hηL (by nlinarith)
  rw [capEta]
  have := mul_le_mul_of_nonneg_right hdepth h2.le
  linarith

/-- A depth for the induction exists, at any accuracy: `Kakeya.ML2Cap.Arith.exists_depth`. -/
theorem exists_capDepth {γ ε : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) :
    ∃ K : ℕ, (1 - γ / 4) ^ K ≤ ε / 2 :=
  Arith.exists_depth (c := γ / 4) (by linarith) (by nlinarith) (by linarith)

end Kakeya.ML2Cap
