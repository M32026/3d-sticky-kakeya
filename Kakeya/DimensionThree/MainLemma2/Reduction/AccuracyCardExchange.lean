/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.BandSqueeze
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParams

/-!
# The accuracy–cardinality exchange: why the every-scale branch cannot be re-cut

`Reduction/GainFloor.lean` settles the **gain** column of the every-scale branch: a gain-shaped
conclusion `μ ≤ δ^{g}|𝕋|^β` with no cardinality clause is *false*
(`Kakeya.ML2GainFloor.not_gainOnly`), with a clause below the Katz--Tao ceiling it is still false
(`not_gainBand_of_lt_katzTaoCeiling`), and with any clause `δ^{-θ} ≤ |𝕋|`, `θ > 0`, its residue is
the goal (`gainBand_residue_is_the_goal`).  *There is no third column* — for gains.

This file settles the **accuracy** column, which `GainFloor.lean` does not touch, and it settles it
at every absolute accuracy rather than at the one the development happens to use.

## The exchange

`Kakeya.ML2Assembly.Dichotomy`'s first alternative delivers an accuracy `μ ≤ δ^{-ε₀}` and its
cardinality hypothesis is `δ⁻¹ ≤ |𝕋|`, i.e. the threshold `θ = 1`.  **That threshold is not
forced; it is a rounding.**  Converting the accuracy into the goal
`∑|Y| ≤ δ^{-ε}|𝕋|^{γ}|⋃Y|` at `γ = β - c` needs only

```
ε₀ ≤ ε + θ · γ                         (the large side, θ arbitrary)
```

— `Kakeya.ML2Exchange.katzTaoGoal_of_absoluteLoss_of_card_ge_rpow`, which is
`Kakeya.MainLemma2.Reduction.katzTaoGoal_of_absoluteLoss_of_card_ge` with its hard-wired `θ = 1`
released.  Symmetrically the complementary band is discharged for free by the trivial bound exactly
when

```
θ · (1 - γ) ≤ ε                        (the small side)
```

— `Kakeya.MainLemma2.Reduction.katzTaoGoal_of_card_le_rpow`, already general in `θ`.  The two have
been in the tree side by side, at different `θ` conventions, and nobody asked when they meet.
**They meet exactly when**

```
ε₀ · (1 - γ) ≤ ε.
```

That is `Kakeya.ML2Exchange.exists_threshold_iff`, an equivalence: a threshold closing both sides
exists *iff* the absolute accuracy obeys that bound.  Two immediate consequences:

* `Kakeya.ML2Exchange.epsFree_accuracy_nonpos` — **an `ε`-free accuracy that closes the band at
  every outer accuracy must be non-positive.**  So no positive `ε`-free `ε₀` avoids a residue, at
  *any* threshold: lowering `θ` below `1` does not help, and neither does lowering `ε₀`.  What is
  left over is `Kakeya.ML2Squeeze.SmallCardCut θ γ`, which
  `Kakeya.ML2Squeeze.smallCardCut_iff_katzTaoEstimate` shows is the goal, for every `θ > 0`.
* `Kakeya.ML2Exchange.exists_threshold_of_le` — and the bound is *sufficient*: if `ε₀` may shrink
  with `ε`, the band closes and there is no residue at all.

## The dilemma

The second bullet is the only escape, and it is closed by the other end of the reduction.  Reading
Theorem 7.3(B) at an accuracy that shrinks with the outer `ε` makes an `ε`-free gain impossible
(`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy'`), and Main Lemma 2 needs the drop `c` — hence the
target exponent `β - c` — chosen **before** `ε`, because `Kakeya.KatzTaoEstimate (β - c)` binds `ε`
inside.  `Kakeya.ML2Exchange.ml2_accuracy_horns` puts the two refutations in one statement:

> **neither** an `ε`-free positive absolute accuracy (the band never closes) **nor** an
> `ε`-dependent one (the gain dies) supports the reduction.

Together with `GainFloor.lean`'s trichotomy for gain-shaped branches this exhausts the shapes the
every-scale branch can have: accuracy or gain, at any threshold, at any accuracy.  **The
obstruction is not the strength of the branch and not the position of the cut; it is that the cut
exists at all.**

## How this sits beside what was already proved

Three results in the tree bracket this one, and none of them is it.

* `Kakeya.ML2Band.absoluteLossRoute_insufficient` (`Reduction/SpineCardBand.lean`) is the
  **necessity** half of Part I's budget, already at a general threshold: below `ε₀ ≤ ε + θγ` the
  bound the branch would need is strictly false on every family with `|𝕋| ≤ δ^{-θ}`.  Part I
  supplies the matching **sufficiency**, at the measure level a consumer can use; the tree had
  sufficiency only at `θ = 1`.  Together the budget is exact.
* `Kakeya.ML2Squeeze.forall_cut_circular` says: **if** the residue is nonempty, it is the theorem,
  at every threshold.  `Kakeya.ML2Exchange.epsFree_accuracy_nonpos` says the residue **is** always
  nonempty, at every positive `ε`-free accuracy.  Those are different statements, and the argument
  needs both: without the second, "lower the threshold until the residue vanishes" is still open;
  the exchange closes it by showing the threshold that would do so does not exist.
* `Kakeya.ML2Squeeze.producer_of_smallCardCut_is_producer_of_goal` is the acceptance filter for a
  *proposed* residue.  Part II is upstream of it: it says which residues can even be proposed.

## The one cut that is not a cardinality cut, and why it collapses too

Cutting on GWZ Lemma 9.1's own side condition `Kakeya.ML2Squeeze.ScaleCount` instead of on `|𝕋|`
looks like an escape — essential distinctness is affine-covariant, so the squeeze of
`Reduction/BandSqueezeAlt.lean` does not obviously reach it, and
`Kakeya.ML2Squeeze.gainOnlyMult_of_lemma91Body` shows Lemma 9.1 delivers the gain on exactly the
families that satisfy it.  It is not an escape.
`Kakeya.ML2Squeeze.not_scaleCount_of_card_lt_delta_inv` shows `ScaleCount` **fails on every family
below the band**, so the residue of the `ScaleCount` cut *contains* the residue of the `δ⁻¹` cut,
and by `Kakeya.ML2Squeeze.forall_cut_circular` the latter is already the theorem.  A finer cut with
a larger residue is not progress.  This is recorded here so the idea is not re-costed a third time.

## What is *not* claimed

Nothing here refutes GWZ Main Lemma 2, GWZ Lemma 9.1, or Theorem 7.3(B). What is refuted is one
*reduction shape*: a two-case split of the tube families by a `δ`-power cardinality threshold, with
the every-scale case closed from a `β`-only bound. GWZ's own §9 carries no cardinality hypothesis;
`Reduction/BandSqueezeAlt.lean` localises why the one introduced here cannot be a real restriction
(the band compares an affine invariant to a non-invariant), and this file prices what it would cost
if it could.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology ShadedBody ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Exchange

/-! ## Part I — the large-cardinality branch at a general threshold -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **The large-cardinality branch, at an arbitrary threshold `θ`.**

`Kakeya.MainLemma2.Reduction.katzTaoGoal_of_absoluteLoss_of_card_ge` is this theorem with
`θ = 1` hard-wired, both in the hypothesis `δ⁻¹ ≤ |𝕋|` and in the budget `ε₀ ≤ ε + γ`.  Releasing
`θ` is what makes the exchange with the small side visible: the branch closes on
`δ^{-θ} ≤ |𝕋|` as soon as `ε₀ ≤ ε + θγ`, so the threshold the every-scale branch really needs is
`θ ≥ (ε₀ - ε)/γ`, and **`Kakeya.ML2Assembly.Dichotomy`'s `δ⁻¹` is a rounding of it, not a
requirement** (`Kakeya.ML2Exchange.absAccuracy_threshold_le_one`). -/
theorem katzTaoGoal_of_absoluteLoss_of_card_ge_rpow {s : Finset ι} {V : ι → ShadedBody E}
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε ε₀ γ θ : ℝ} (hγ0 : 0 ≤ γ)
    (hloss : ε₀ ≤ ε + θ * γ) (hcard : (δ : ℝ) ^ (-θ) ≤ (s.card : ℝ))
    (h : ∑ i ∈ s, volume (V i).shade
          ≤ (δ : ENNReal) ^ (-ε₀) * volume (⋃ i ∈ s, (V i).shade)) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (V i).shade) := by
  have hd0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
  have hdtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hd1 : (δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr hδ1
  have hcardE : (δ : ENNReal) ^ (-θ) ≤ (s.card : ENNReal) :=
    Kakeya.ML2Band.coe_rpow_le_natCast hδ hcard
  have hpow : (δ : ENNReal) ^ (-(θ * γ)) ≤ (s.card : ENNReal) ^ γ := by
    have heq : (δ : ENNReal) ^ (-(θ * γ)) = ((δ : ENNReal) ^ (-θ)) ^ γ := by
      rw [← ENNReal.rpow_mul, neg_mul]
    rw [heq]
    exact ENNReal.rpow_le_rpow hcardE hγ0
  have hkey : (δ : ENNReal) ^ (-ε₀) ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ := by
    calc (δ : ENNReal) ^ (-ε₀)
        ≤ (δ : ENNReal) ^ (-ε + -(θ * γ)) :=
          ENNReal.rpow_le_rpow_of_exponent_ge hd1 (by linarith)
      _ = (δ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-(θ * γ)) := ENNReal.rpow_add _ _ hd0 hdtop
      _ ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ := by gcongr
  exact h.trans (by gcongr)

/-! ## Part II — the exchange identity -/

/-- **THE EXCHANGE.**  A cardinality threshold `θ ≥ 0` closing *both* sides — the large side
`ε₀ ≤ ε + θγ` (Part I) and the small side `θ(1-γ) ≤ ε`
(`Kakeya.MainLemma2.Reduction.katzTaoGoal_of_card_le_rpow`) — exists **iff**
`ε₀(1-γ) ≤ ε`.

Read left to right this prices the every-scale branch's absolute accuracy in units of the outer
accuracy; read right to left it says nothing else is needed.  The witness on the right-to-left side
is `θ = ε/(1-γ)`, the largest threshold the small side allows. -/
theorem exists_threshold_iff {ε ε₀ γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε) :
    (∃ θ : ℝ, 0 ≤ θ ∧ ε₀ ≤ ε + θ * γ ∧ θ * (1 - γ) ≤ ε) ↔ ε₀ * (1 - γ) ≤ ε := by
  have h1γ : 0 < 1 - γ := by linarith
  constructor
  · rintro ⟨θ, _hθ0, hlarge, hsmall⟩
    have hA : ε₀ * (1 - γ) ≤ (ε + θ * γ) * (1 - γ) :=
      mul_le_mul_of_nonneg_right hlarge h1γ.le
    have hB : θ * (1 - γ) * γ ≤ ε * γ := mul_le_mul_of_nonneg_right hsmall hγ0
    nlinarith [hA, hB]
  · intro hle
    have hθ : ε / (1 - γ) * (1 - γ) = ε := div_mul_cancel₀ _ h1γ.ne'
    refine ⟨ε / (1 - γ), by positivity, ?_, le_of_eq hθ⟩
    have key : (ε + ε / (1 - γ) * γ) * (1 - γ) = ε := by field_simp; ring
    have h2 : ε₀ * (1 - γ) ≤ (ε + ε / (1 - γ) * γ) * (1 - γ) := by rw [key]; exact hle
    exact le_of_mul_le_mul_right h2 h1γ

/-- The right-to-left half, named: **if the absolute accuracy may shrink with the outer accuracy,
the cardinality split disappears.**  This is the only escape from
`Kakeya.ML2Exchange.epsFree_accuracy_nonpos`, and `Kakeya.ML2Exchange.ml2_accuracy_horns` closes
it. -/
theorem exists_threshold_of_le {ε ε₀ γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hle : ε₀ * (1 - γ) ≤ ε) :
    ∃ θ : ℝ, 0 ≤ θ ∧ ε₀ ≤ ε + θ * γ ∧ θ * (1 - γ) ≤ ε :=
  (exists_threshold_iff hγ0 hγ1 hε).mpr hle

/-- **An `ε`-free absolute accuracy that closes the band at every outer accuracy is non-positive.**

The headline of this file.  It is stronger than "the threshold `δ⁻¹` leaves a residue": it says
**every** threshold does, at **every** positive `ε`-free accuracy.  So the residue
`Kakeya.ML2Assembly.SmallCard` is not an artefact of the particular constants `ε₀ = β/2` and
`θ = 1` that `Kakeya.ML2Assembly.Dichotomy` uses — no choice of either removes it. -/
theorem epsFree_accuracy_nonpos {ε₀ γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (h : ∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 ≤ θ ∧ ε₀ ≤ ε + θ * γ ∧ θ * (1 - γ) ≤ ε) :
    ε₀ ≤ 0 := by
  have h1γ : 0 < 1 - γ := by linarith
  by_contra hpos
  rw [not_le] at hpos
  have hε : 0 < ε₀ * (1 - γ) / 2 := by positivity
  have hkey := (exists_threshold_iff hγ0 hγ1 hε).mp (h _ hε)
  nlinarith [hkey]

/-- The contrapositive in the form the reduction meets it: at a positive `ε`-free accuracy there
is an outer accuracy at which **no** threshold closes both sides. -/
theorem exists_accuracy_without_threshold {ε₀ γ : ℝ} (hε₀ : 0 < ε₀) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ¬ ∃ θ : ℝ, 0 ≤ θ ∧ ε₀ ≤ ε + θ * γ ∧ θ * (1 - γ) ≤ ε := by
  have h1γ : 0 < 1 - γ := by linarith
  refine ⟨ε₀ * (1 - γ) / 2, by positivity, ?_⟩
  intro hex
  have hkey := (exists_threshold_iff hγ0 hγ1 (by positivity)).mp hex
  nlinarith [hkey]

/-! ## Part III — the threshold `Kakeya.ML2Assembly.Dichotomy` uses is a rounding -/

/-- **The sharp threshold.**  The large side forces `θ ≥ (ε₀ - ε)/γ` and nothing more. -/
theorem threshold_lower_bound {ε ε₀ γ θ : ℝ} (hγ : 0 < γ) (hloss : ε₀ ≤ ε + θ * γ) :
    (ε₀ - ε) / γ ≤ θ := by
  rw [div_le_iff₀ hγ]
  linarith

/-- **`δ⁻¹` is a rounding of `δ^{-ε₀/γ}`.**  At the development's own data — the absolute accuracy
`Kakeya.ML2Spine.absAccuracy β = β/2` and the target exponent `γ = β - c` under the `ε`-free budget
`2c ≤ β` — the threshold the every-scale branch actually needs is at most `1`, with equality only
at `c = β/2`.  So `Kakeya.ML2Assembly.Dichotomy`'s hypothesis `δ⁻¹ ≤ |𝕋|` may be weakened to
`δ^{-(β/2)/(β-c)} ≤ |𝕋|` for free.

**This does not rescue the reduction**, and that is the point of stating it: by
`Kakeya.ML2Squeeze.smallCardCut_iff_katzTaoEstimate` the complement of *any* positive threshold is
the goal, and by `Kakeya.ML2Exchange.epsFree_accuracy_nonpos` no positive `ε`-free accuracy makes
the complement empty.  Lowering the threshold is the obvious next idea and it is worth exactly
nothing. -/
theorem absAccuracy_threshold_le_one {β c : ℝ} (hc : 0 < c) (hcβ : 2 * c ≤ β) :
    β / 2 / (β - c) ≤ 1 := by
  have hγ : 0 < β - c := by linarith
  rw [div_le_one hγ]
  linarith

/-! ## Part IV — the dilemma -/

variable {β ϖ : ℝ} {gain dens : ℝ → ℝ}

/-- **BOTH HORNS, IN ONE STATEMENT.**

* **Left horn.**  A positive `ε`-free absolute accuracy `ε₀` does **not** close the cardinality
  band at every outer accuracy — at any threshold whatever
  (`Kakeya.ML2Exchange.epsFree_accuracy_nonpos`).  So the every-scale branch read at an absolute
  accuracy always leaves a residue, and by
  `Kakeya.ML2Squeeze.smallCardCut_iff_katzTaoEstimate` that residue is Main Lemma 2's own
  conclusion.
* **Right horn.**  Reading Theorem 7.3(B) at an accuracy that shrinks with the outer `ε` — the one
  thing that *would* close the band, by `Kakeya.ML2Exchange.exists_threshold_of_le` — makes an
  `ε`-free gain `ν > 0` impossible (`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy'`), and Main
  Lemma 2 needs the drop chosen before `ε`.

Neither horn is escapable by choosing constants: the left one quantifies over **all** thresholds
and **all** positive `ε`-free accuracies, and the right one over all exponent maps `E` normalised
by `E a ≤ a`.  With `Reduction/GainFloor.lean`'s trichotomy for gain-shaped branches, the
every-scale branch has no remaining shape. -/
theorem ml2_accuracy_horns {E : ℝ → ℝ} (hE : ∀ a : ℝ, 0 < a → E a ≤ a) {ν : ℝ} (hν : 0 < ν)
    {ε₀ γ : ℝ} (hε₀ : 0 < ε₀) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (¬ ∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 ≤ θ ∧ ε₀ ≤ ε + θ * γ ∧ θ * (1 - γ) ≤ ε)
      ∧ (¬ ∀ ε : ℝ, 0 < ε → ∃ ε₂ e : ℝ, ∃ N : ℕ, ∃ η : ℕ → ℝ,
          Kakeya.ML2Spine.IsSpine β ϖ (E ε) gain dens ε₂ e N η ∧ ν ≤ η 1) :=
  ⟨fun h => absurd (epsFree_accuracy_nonpos hγ0 hγ1 h) (not_le.mpr hε₀),
    fun h => Kakeya.ML2Spine.not_epsFree_of_outerAccuracy' hE hν h⟩


/-! ## Part V — the source, quoted, and where the split actually comes from

Everything above is arithmetic about the reduction as this development cuts it.  This part records
what GWZ *write*, transcribed from `pdftotext -layout` of `kakeya-streamlined-2601.14411.pdf`, so
that the comparison rests on the paper rather than on our own docstrings.

**GWZ Theorem 7.3 (p. 25).**

> For all `ϵ > 0`, there exists `η, δ₀ > 0` so that the following holds for all `δ ∈ (0, δ₀]`.
> Let `(T, Y)` be a uniform set of `δ`-tubes in `B₁ ⊂ R³`, with `λ(T, Y) ≥ δ^η`.
> **(A)** If `T` is Frostman at every scale with error `δ^{-η}`, then `|U(T, Y)| ≥ δ^ϵ`.
> **(B)** If `T` is Katz-Tao at every scale with error `δ^{-η}`, then `µ(T, Y) ≤ δ^{-ϵ}`.

Three hypotheses — uniform, `λ(T,Y) ≥ δ^η`, Katz--Tao at every scale with error `δ^{-η}` — and a
bare conclusion `µ(T,Y) ≤ δ^{-ϵ}`.  **No cardinality hypothesis and no `|T|^β` factor.**

**GWZ, proof of Main Lemma 2 using Lemma 9.1, Conclusion (i) (p. 33).**

> Apply Lemma 7.7(B) to `T`.  If Conclusion (i) holds, then (provided we select `ϵ₂ ≤ ϵ₁/5`) we
> have that `T` is `δ^{-ϵ₁}` Katz-Tao at every scale, and hence by Theorem 7.3(B) we have
> `µ(T, Y) ≤ δ^{-ϵ}`, and thus (67) is satisfied.

and (67) is `µ(T, Y) ≤ δ^{-ϵ}|T|^{β-ν}`.  So the branch closes because `|T| ≥ 1` and `β - ν ≥ 0`,
**with nothing about cardinality at all**.  That step is
`Kakeya.ML2Reduction.multiplicity_le_mul_card_rpow_of_le`, already in the tree, and it is
`Kakeya.ML2Exchange.katzTaoGoal_of_absoluteLoss_of_le` below — *which is Part I at `θ = 0`.*
**GWZ's Conclusion (i) is the `θ = 0` case of the released-threshold branch and
`Kakeya.ML2Assembly.Dichotomy`'s is the `θ = 1` case; the exchange identity at `θ = 0` reads
`ε₀ ≤ ε`.**

**Our Theorem 7.3(B) is not weaker than GWZ's.**  `StickyKakeya.StickyKatzTaoEstimate`
(`Kakeya/Sticky.lean:276`) has GWZ's quantifier order (`∀ ε, ∃ η δ₀`), GWZ's three hypotheses, and
GWZ's conclusion `µ ≤ δ^{-ε}` verbatim — no cardinality clause, no `|T|^β`. It carries exactly one
hypothesis GWZ's does not: the leaf-scale density bound `Δ_max(T) ≤ δ^{-η}`
(`ConvexSpaceBody.IsKatzTao s _ (δ^{-η})`), which the node reading of "Katz--Tao at every scale"
does not imply. **That hypothesis is free at the Section-9 call site**: it is the first bullet of
GWZ Definition 3.4 (`K_KT(β)`) and therefore already in scope wherever Main Lemma 2's goal is being
proved.

**Where the split does come from, then.**  One clause, GWZ p. 32:

> Let `ϵ₁` and `δ₁` be the output of Theorem 7.3 with `ϵ` as above. … Let `ϵ₂ = ϵ₂(ϵ₁, ϵscale, β)`
> be a number to be chosen later **(since `ϵ₁` and `ϵscale` depend only on `β`, `ϵ₂` depends only
> on `β`)**.

`ϵ₁` is *defined* one sentence earlier as Theorem 7.3's output at the outer `ϵ`, so `ϵ₁ = ϵ₁(ϵ, β)`;
the parenthetical asserts `ϵ₁ = ϵ₁(β)`.  Exactly one of the two can hold, and the whole architecture
turns on which:

* **`ϵ₁ = ϵ₁(ϵ)`, the definition.**  Branch (i) closes with no cardinality clause, exactly as
  written.  But `ν = η₁ ≤ ϵ₂ ≤ ϵ₁/5` then depends on `ϵ`, while GWZ Definition 3.4 binds `ϵ`
  *outside* `K_KT(β - ν)` and Main Lemma states `ν = ν(β)`.  Refuted by
  `Kakeya.ML2Spine.not_epsFree_of_outerAccuracy'`.
* **`ϵ₁ = ϵ₁(β)`, the parenthetical.**  Then Theorem 7.3(B) must be read at a `β`-only accuracy
  `ε₀`, its conclusion is `µ ≤ δ^{-ε₀}` with `ε₀ > ε` in general, and a cardinality lower bound
  appears — `Kakeya.ML2Reduction.ofReal_rpow_neg_le_mul_card_rpow`, the one place `|𝕋| ≥ δ⁻¹` is
  spent.  Refuted by `Kakeya.ML2Exchange.epsFree_accuracy_nonpos` together with
  `Kakeya.ML2Squeeze.smallCardCut_iff_katzTaoEstimate`.

**So `δ⁻¹ ≤ |𝕋|` is not GWZ's and not an artefact of our Theorem 7.3(B): it is the forced price of
the only reading under which Main Lemma 2's `ν` is well defined.**
`Kakeya.ML2Exchange.ml2_accuracy_horns` is the pair of refutations, and this part is what anchors
it to the paper.  The remaining escape —
swapping Theorem 7.3(B)'s own quantifiers to `∃ η, ∀ ϵ` — is unavailable: an `η` bounded below at
every accuracy would say that any family Katz--Tao at every scale with that fixed error has
multiplicity `δ^{-ϵ}` for *every* `ϵ`, which is the argument inside
`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy`. -/

/-- **GWZ's Conclusion (i), verbatim in force: no cardinality hypothesis.**

Part I at `θ = 0`.  When the accuracy at which Theorem 7.3(B) was read is already below the goal's
`ε`, the every-scale branch closes on `|𝕋| ≥ 1` alone — which is what GWZ's *"and thus (67) is
satisfied"* means.  `Kakeya.ML2Reduction.multiplicity_le_mul_card_rpow_of_le` is the same step in
multiplicity form; this is the mass form, and stating it as a corollary of Part I is the point:
**the source's branch and the development's branch differ only in the value of `θ`.** -/
theorem katzTaoGoal_of_absoluteLoss_of_le {s : Finset ι} {V : ι → ShadedBody E}
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hne : s.Nonempty) {ε ε₀ γ : ℝ} (hγ0 : 0 ≤ γ)
    (hle : ε₀ ≤ ε)
    (h : ∑ i ∈ s, volume (V i).shade
          ≤ (δ : ENNReal) ^ (-ε₀) * volume (⋃ i ∈ s, (V i).shade)) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (V i).shade) := by
  refine katzTaoGoal_of_absoluteLoss_of_card_ge_rpow (θ := 0) hδ hδ1 hγ0 (by simpa using hle)
    ?_ h
  have h1 : (1 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast Finset.one_le_card.mpr hne
  simpa using h1

/-- **And a `β`-only accuracy cannot be below every outer accuracy.**  The `θ = 0` corner of
`Kakeya.ML2Exchange.exists_threshold_iff`, named because it is the corner GWZ's text sits in: the
Conclusion (i) branch as printed needs `ε₀ ≤ ε` at every `ε`, and no positive `ε`-free `ε₀` does
that.  This is why the parenthetical on p. 32 and the definition of `ϵ₁` one sentence earlier
cannot both stand. -/
theorem absoluteAccuracy_nonpos_of_le_forall {ε₀ : ℝ} (h : ∀ ε : ℝ, 0 < ε → ε₀ ≤ ε) : ε₀ ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  have := h (ε₀ / 2) (by linarith)
  linarith


/-! ## Part VI — testing the author's own reading, and the scope of Part II

Prof. Hong Wang's clarification of this argument says two things, and the development has been
using them as if they were one:

1. the absolute accuracy parameter for Theorem 7.3 — when applying Theorem 7.3, use an **absolute** `ε₀` —
   together with the independence of `nu` from the running accuracy, `ν` depends on the other `ε_i` but
   **not** on `ε`.  This is the reading under which `ν` comes out `β`-only, as Main Lemma 2
   requires.
2. *"if `𝕋` is bilinear this is automatic; in the non-bilinear case broad--narrow supplies the
   improvement"* — the **source of the cardinality lower bound** `|𝕋| > δ^{-1}`.

**These are two halves of one repair, and the formalisation has only the first half.**

### The apparent contradiction, and why there is none

`blueprint/src/GWZAdapted/section9.tex` contains **zero** occurrences of `delta^{-1}`, of "small
cardinality" and of "few tubes" in 2143 lines, and the paper itself contains **zero** occurrences of
"broad" and of "bilinear".  So neither the band nor broad--narrow is in the written proof — which is
correct and expected: **the written proof reads Theorem 7.3(B) at the outer `ε`, and at the outer
`ε` no band is needed.**  The band and broad--narrow enter together, in the clarification, precisely
because the clarification changes the accuracy to an absolute one.  Two measurements of two
different objects; both stand.

### The test: reading 2 with the band removed

At `θ = 0` — no cardinality information — `Kakeya.ML2Exchange.katzTaoGoal_of_absoluteLoss_of_le`
closes the branch from `μ ≤ δ^{-ε₀}` **iff** `ε₀ ≤ ε`, and the deficit when `ε < ε₀` is
`δ^{-(ε₀-ε)}`: a genuine positive power of `δ`, **not** a subpolynomial factor, so no `⪅` absorbs
it (`Kakeya.ML2Exchange.zeroThreshold_insufficient`, from
`Kakeya.ML2Band.absoluteLossRoute_insufficient` at `θ = 0`; see also
`Kakeya.OmegaAssessment.oneParam_fixed_loss_fails`).  And
`Kakeya.ML2Exchange.absoluteAccuracy_nonpos_of_le_forall` says no positive `ε`-free `ε₀` has
`ε₀ ≤ ε` at every `ε`.

The sharp way to say it: at `θ = 0` the branch's target is `μ(𝕋,Y) ≤ δ^{-ε}` — since
`|𝕋|^{β-ν} ≥ 1` is all the information left — **which is Theorem 7.3(B) at the outer accuracy.**
So "reading 2 with the band removed" is not a third option; it *is* reading 1.  **The band is not
an artefact of a lossy conversion: it is what an absolute accuracy costs, exactly.**

### What Part II does and does not refute

`Kakeya.ML2Exchange.epsFree_accuracy_nonpos` quantifies over pairs of budgets

* `ε₀ ≤ ε + θγ`  — the large side converts (Part I), and
* `θ(1-γ) ≤ ε`   — **the small side is discharged by the trivial bound**
  (`Kakeya.MainLemma2.Reduction.katzTaoGoal_of_card_le_rpow`).

So what it refutes, at every threshold and every positive `ε`-free accuracy, is *closing the band by
the trivial bound*.  **It does not refute reading 2**, because reading 2 does not propose to close
the band: it proposes to make the band's complement **empty**, by bilinearity or broad--narrow.
That is a different move and Part II says nothing about it.  This scope is stated here because the
opposite reading of Part II would be an easy and expensive mistake.

### The missing ingredient, named

In the *very-not-sticky* case the band is already free: GWZ Lemma 9.1's third bullet is impossible
below it (`Kakeya.ML2Band.not_scaleCount_of_card_lt_inv`, and
`Kakeya.MainLemma2.Reduction.delta_inv_le_card_of_scaleCount_bullet` the other way), so *"the band
consists exactly of the families that fail the very-not-sticky count"*.  **But branch (i) is not the
very-not-sticky case** — it is the every-scale case, and it carries no count hypothesis at all.  Its
four available facts are unit-ball containment, `Δ_max(𝕋) ≤ δ^{-η}`, `λ ≥ δ^η` and nothing else, and
`Reduction/BandSqueezeAlt.lean` shows the affine squeeze survives all four
(`Kakeya.ML2BandSqz.repair_blocks_but_is_unavailable`): the clause that *would* block it,
`Kakeya.ML2BandSqz.DirNonConcentrated` — the formal shadow of "bilinear"/broad — is exactly the one
the branch cannot hand over (`Kakeya.ML2BandSqz.not_callSiteAvailable_dirNonConcentrated`).

**So the missing ingredient is a producer of `Kakeya.ML2BandSqz.DirNonConcentrated`, or a
broad--narrow decomposition reducing to families that have it.**  The tree has no broadness
apparatus outside the abandoned `MainLemma2.WangZahl.*` subtree, which Section 9 may not import, and
the GWZ-adapted blueprint never mentions broadness.  **That is a geometric development that was
never begun — not a defect in the paper, and not something the assembly can bookkeep its way
around.**
-/

/-- **At `θ = 0` the every-scale bound is insufficient exactly when `ε < ε₀`, and the deficit is a
genuine power of `δ`.**  `Kakeya.ML2Band.absoluteLossRoute_insufficient` at `θ = 0` and `N = 1`,
which is the worst case the branch must cover (a one-tube family is Katz--Tao at every scale).

This is the form of "it cannot be absorbed": `δ^{-ε}` falls short of `δ^{-ε₀}` by the
factor `δ^{-(ε₀-ε)}`, which is subpolynomial only if `ε₀ ≤ ε`.  Hence removing the band from
reading 2 turns it back into reading 1. -/
theorem zeroThreshold_insufficient {δ ε ε₀ γ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ)
    (hlt : ε < ε₀) : δ ^ (-ε) * (1 : ℝ) ^ γ < δ ^ (-ε₀) :=
  Kakeya.ML2Band.absoluteLossRoute_insufficient (θ := 0) hδ0 hδ1 hγ (by simpa using hlt)
    one_pos (by simp)

end Kakeya.ML2Exchange
