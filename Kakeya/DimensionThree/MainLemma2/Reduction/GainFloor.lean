/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.BandSqueeze
public import Kakeya.DimensionThree.Plank.Prop66ARepaired

/-!
# The cardinality floor a **gain** carries with it, and the refutation of `GainDichotomy`

steps.  The target was to *produce* `Kakeya.ML2Squeeze.GainDichotomy` — the every-scale
branch of GWZ Main Lemma 2 upgraded from an accuracy `μ ≤ δ^{-ε₀}` to a gain `μ ≤ δ^{g}|𝕋|^β`,
with the cardinality clause of `Kakeya.ML2Assembly.Dichotomy` deleted.  It cannot be produced,
and the reason is not that the every-scale branch is too weak: **the target is false.**

## The one-line reason

`μ(𝕋, Y) = (∑|Y(T)|)/|⋃ Y(T)| ≥ 1` whenever some shading has positive measure
(`ShadedBody.one_le_multiplicity`), and the fullness hypothesis `λ ≥ δ^η` of every predicate in
this family forces exactly that.  So a gain-shaped conclusion `μ ≤ δ^g |𝕋|^β` **implies**
`1 ≤ δ^g |𝕋|^β`, i.e.

```
|𝕋| ≥ δ^{-g/β}.
```

The cardinality clause is therefore not an artifact of the *accuracy* alternative that
`Kakeya.OmegaAssessment.oneParam_fixed_loss_forces_card` prices.  It is a **corollary of the gain
itself**: `Kakeya.ML2GainFloor.card_floor_of_gain`.  Deleting the accuracy does not delete the
cardinality clause; deleting the cardinality clause makes the statement false.

## What is proved here

* `Kakeya.ML2GainFloor.one_le_gainCoeff` — any mass bound `∑|Y| ≤ c·|⋃Y|` on a family with some
  positively-shaded member forces `1 ≤ c`.  Completely general.
* `Kakeya.ML2GainFloor.card_floor_of_gain` — the gain shape forces `δ^{-g/β} ≤ |𝕋|`.
* `Kakeya.ML2GainFloor.not_gainOnly` — `Kakeya.ML2Squeeze.GainOnly β g η` is **false** for every
  `g > 0` and `η ≥ 0`, at every `β`.
* `Kakeya.ML2GainFloor.not_gainOnlyMultBody` — the same in GWZ Lemma 9.1's own currency, the
  multiplicity form `μ ≤ δ^g|𝕋|^β`.  This is **not** a refutation of Lemma 9.1: 9.1 carries
  `Kakeya.ML2Squeeze.ScaleCount`, which by `Kakeya.ML2Squeeze.scaleCount_forces_band` already
  implies `δ⁻¹ ≤ |𝕋|`.  What is refuted is the deletion of that cardinality content.
* `Kakeya.ML2GainFloor.centralCopies_accuracy` — on the same witness the *accuracy* alternative
  `μ ≤ δ^{-ε₀}` is **true**.  The two alternatives of `Kakeya.ML2Assembly.Dichotomy` are therefore
  not symmetric under deleting the cardinality clause: the accuracy survives and stays too weak,
  the gain dies.
* `Kakeya.ML2GainFloor.gainOnly_hypothesis_unsatisfiable` —
  `Kakeya.ML2Squeeze.katzTaoEstimate_sub_of_gainOnly` compiles but has no instance on its own
  budget range `4c ≤ g`, `c > 0`, `η > 0`.
* `Kakeya.ML2GainFloor.not_gainDichotomyBody` — hence `Kakeya.ML2Squeeze.GainDichotomy β g₁ g₂ η`
  is false whenever `0 < g₁` and `0 < g₂`, which is exactly the range in which
  `Kakeya.ML2Squeeze.katzTaoEstimate_sub_of_gainDichotomy` can be applied (its budget is
  `4c ≤ min g₁ g₂` with `c > 0`).
* `Kakeya.ML2GainFloor.gain_fails_on_copies` — the failure is **not** a `|𝕋| = 1` corner.  The
  gain fails on every family of `n` coincident fully-shaded `δ`-tubes, and such a family is
  admissible for every `n ≤ δ^{-η}`: so the gain is false throughout `1 ≤ |𝕋| ≤ δ^{-η}`, i.e.
  everywhere below the Katz–Tao ceiling that the hypothesis itself grants.
* `Kakeya.ML2GainFloor.GainBand` and
  `Kakeya.ML2GainFloor.katzTaoEstimateGE_sub_of_gainBand` — the strongest *true* form of the
  hypothesis is the gain restricted to a band `δ^{-θ} ≤ |𝕋|`, and it delivers exactly
  `Kakeya.ML2Squeeze.KatzTaoEstimateGE θ (β - c)`.
* `Kakeya.ML2GainFloor.gainBand_residue_is_the_goal` — and the residue of *that* is, by
  `Kakeya.ML2Squeeze.forall_cut_circular`, the conclusion of Main Lemma 2 itself, at every
  `θ > 0`.
* `Kakeya.ML2GainFloor.not_gainBand_of_lt_katzTaoCeiling` — and a band with `θ < η` is not even
  true: the window `δ^{-θ} ≤ |𝕋| ≤ δ^{-η}` always contains an integer
  (`Kakeya.ML2GainFloor.exists_card_in_window`), so a usable floor has to sit **above the
  Katz–Tao ceiling that the gain's own hypothesis grants**, which is where
  `Kakeya.ML2Assembly.Dichotomy`'s `δ⁻¹` already sits.

## The refutation is robust to the obvious patches

* **Adding essential distinctness does not help.**  The `n = 1` witness satisfies *every* pairwise
  relation vacuously (`Kakeya.ML2GainFloor.centralCopies_one_pairwise`), so `GainOnly` stays false
  with an `IsEssentiallyDistinct` clause bolted on.  (The `n ≥ 2` coincident witness of
  `Kakeya.ML2GainFloor.not_gainBand_of_lt_katzTaoCeiling` does **not** survive such a clause —
  that sharpening is about the Lean predicates as written.)
* **Adding GWZ Definition 2.2 uniformity does not help** — the witness is a uniform tube set at
  the constant `1` (`Kakeya.ML2GainFloor.centralCopies_one_uniform`).
* **Adding a small cardinality floor does not help** —
  `Kakeya.ML2GainFloor.not_gainBand_of_lt_katzTaoCeiling`.
* What *does* help is the one hypothesis GWZ Lemma 9.1 actually carries: the scale count, which
  `Kakeya.ML2Squeeze.scaleCount_forces_band` shows is already a cardinality lower bound.

## The resulting dichotomy

| gain hypothesis | verdict |
|---|---|
| no cardinality clause (`GainOnly`, `GainDichotomy`) | **false**, `not_gainOnly` |
| a clause `δ^{-θ} ≤ \|𝕋\|` with `θ < η` | **false**, `not_gainBand_of_lt_katzTaoCeiling` |
| a clause `δ^{-θ} ≤ \|𝕋\|` with `θ > 0` | **circular**, `gainBand_residue_is_the_goal` |

There is no third column.  A gain with `θ = 0` is inconsistent and a gain with `θ > 0` leaves a
residue equivalent to the goal, so **no gain-shaped every-scale branch can close Main Lemma 2 by
this route**, and no amount of geometric work on `Reduction/SpineEveryScale.lean` changes that:
the obstruction is in the shape of the conclusion, not in the strength of the branch.

## Applying the acceptance filter to this file

`Kakeya.ML2GainFloor.GainBand` is *not* of the `Kakeya.ML2Squeeze.SmallCardCut` shape — it is the
band, not the band's complement — so
`Kakeya.ML2Squeeze.producer_of_smallCardCut_is_producer_of_goal` does not apply to it and does not
rule it out.  Its circularity is proved the other way round, through
`Kakeya.ML2Squeeze.residue_of_banded` and `Kakeya.ML2Squeeze.forall_cut_circular`.  No new
cardinality cut and no accuracy binder is introduced by anything in this file: `GainBand` is
recorded as the *diagnosis*, and is not offered as a replacement obligation.

## Transcription fidelity

`Kakeya.ML2GainFloor.GainDichotomyBody` and `Kakeya.ML2GainFloor.GainOnlyMultBody` are
character-identical to `Kakeya.ML2Squeeze.GainDichotomy` and `Kakeya.ML2Squeeze.GainOnlyMult` of
the auxiliary Part VI, up to the definition name and the name of the universe variable (`w2` there,
`w` here); this was checked mechanically, not by eye.

## Dependency note

`Kakeya.ML2Squeeze.GainDichotomy` itself lives in an **auxiliary** Part VI of
`Reduction/BandSqueeze.lean` (worktree `w30`).  This file therefore restates it verbatim as
`Kakeya.ML2GainFloor.GainDichotomyBody`, refutes that, and derives the refutation of the existing
`Kakeya.ML2Squeeze.GainOnly` independently, so that nothing here waits on that patch.  When Part
VI lands, the one-line compatibility
`example : Kakeya.ML2Squeeze.GainDichotomy = Kakeya.ML2GainFloor.GainDichotomyBody := rfl`
should be added; it is omitted now only because the constant does not exist.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

open Kakeya.ML2Squeeze (Space3 GainOnly SmallCardCut KatzTaoEstimateGE)

namespace Kakeya.ML2GainFloor

/-! ## Part I — the floor a gain carries with it -/

section Floor

variable {ι : Type*}

/-- **A mass bound on a positively shaded family forces its coefficient to be at least `1`.**
This is `ShadedBody.one_le_multiplicity` read through `ShadedBody.multiplicity_le_iff`, and it is
the whole of the obstruction: the multiplicity of a family with some positively shaded member is
at least `1`, so no bound of the form `μ ≤ c` with `c < 1` can hold. -/
theorem one_le_gainCoeff (s : Finset ι) (V : ι → ShadedBody Space3) {c : ENNReal}
    (hne : ¬ ∀ i ∈ s, volume (V i).shade = 0)
    (hmass : ∑ i ∈ s, volume (V i).shade ≤ c * volume (⋃ i ∈ s, (V i).shade)) :
    1 ≤ c :=
  le_trans (ShadedBody.one_le_multiplicity s V hne)
    ((ShadedBody.multiplicity_le_iff s V).mpr hmass)

/-- The arithmetic half of the floor: `1 ≤ δ^g · n^β` is `δ^{-g/β} ≤ n`. -/
theorem card_floor_of_one_le {δ : NNReal} {n : ℕ} {g β : ℝ}
    (hδ0 : 0 < δ) (hβ : 0 < β) (hn : 0 < n)
    (h : (1 : ENNReal) ≤ (δ : ENNReal) ^ g * (n : ENNReal) ^ β) :
    (δ : ℝ) ^ (-(g / β)) ≤ (n : ℝ) := by
  have hδR : (0 : ℝ) < (δ : ℝ) := hδ0
  have hnN : ((n : NNReal)) ≠ 0 := by simpa using hn.ne'
  have hδE : (δ : ENNReal) ^ g = ((δ ^ g : NNReal) : ENNReal) :=
    (ENNReal.coe_rpow_of_ne_zero hδ0.ne' g).symm
  have hnE : (n : ENNReal) ^ β = (((n : NNReal) ^ β : NNReal) : ENNReal) := by
    rw [show ((n : ENNReal)) = (((n : NNReal)) : ENNReal) by simp]
    exact (ENNReal.coe_rpow_of_ne_zero hnN β).symm
  rw [hδE, hnE, ← ENNReal.coe_mul, ENNReal.one_le_coe_iff] at h
  have hR : (1 : ℝ) ≤ (δ : ℝ) ^ g * (n : ℝ) ^ β := by
    have := NNReal.coe_le_coe.mpr h
    push_cast [NNReal.coe_rpow] at this
    simpa using this
  have hstep : (δ : ℝ) ^ (-g) ≤ (n : ℝ) ^ β := by
    have hpos : (0 : ℝ) < (δ : ℝ) ^ g := Real.rpow_pos_of_pos hδR g
    rw [Real.rpow_neg hδR.le, inv_le_iff_one_le_mul₀ hpos]
    calc (1 : ℝ) ≤ (δ : ℝ) ^ g * (n : ℝ) ^ β := hR
      _ = (n : ℝ) ^ β * (δ : ℝ) ^ g := mul_comm _ _
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hraise := Real.rpow_le_rpow (Real.rpow_nonneg hδR.le _) hstep
    (le_of_lt (by positivity : (0 : ℝ) < 1 / β))
  rw [← Real.rpow_mul hδR.le, ← Real.rpow_mul hnR, show β * (1 / β) = 1 by field_simp,
    Real.rpow_one] at hraise
  convert hraise using 2
  field_simp

/-- **The cardinality floor is a corollary of the gain.**

If a shaded family has a positively shaded member and satisfies GWZ Lemma 9.1's conclusion
`μ ≤ δ^g |𝕋|^β`, then `|𝕋| ≥ δ^{-g/β}`.  No hypothesis of the ambient predicate is used: the
floor comes out of the *conclusion*.

Contrast `Kakeya.OmegaAssessment.oneParam_fixed_loss_forces_card`, which derives a cardinality
lower bound from the **accuracy** alternative.  The two are independent, and this one survives the
deletion of the accuracy. -/
theorem card_floor_of_gain (s : Finset ι) (V : ι → ShadedBody Space3) {δ : NNReal} {g β : ℝ}
    (hδ0 : 0 < δ) (hβ : 0 < β)
    (hne : ¬ ∀ i ∈ s, volume (V i).shade = 0)
    (hmass : ∑ i ∈ s, volume (V i).shade
      ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (V i).shade)) :
    (δ : ℝ) ^ (-(g / β)) ≤ (s.card : ℝ) := by
  have hcard : 0 < s.card := by
    rcases Finset.eq_empty_or_nonempty s with rfl | hs
    · exact absurd (by simp) hne
    · exact Finset.card_pos.mpr hs
  exact card_floor_of_one_le hδ0 hβ hcard (one_le_gainCoeff s V hne hmass)

end Floor

/-! ## Part I bis — the window between the band and the Katz–Tao ceiling -/

section Window

/-- Below the threshold `(1/2)^{1/d}` the loss `x^{-d}` has already reached `2`. -/
theorem two_le_rpow_neg {d : ℝ} (hd : 0 < d) {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ (1 / 2 : ℝ) ^ (1 / d)) : (2 : ℝ) ≤ x ^ (-d) := by
  have hth : (0 : ℝ) < (1 / 2 : ℝ) ^ (1 / d) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : x ^ d ≤ ((1 / 2 : ℝ) ^ (1 / d)) ^ d := Real.rpow_le_rpow hx0.le hx hd.le
  rw [← Real.rpow_mul (by norm_num), show (1 / d) * d = 1 by field_simp, Real.rpow_one] at h1
  have hxd : (0 : ℝ) < x ^ d := Real.rpow_pos_of_pos hx0 d
  rw [Real.rpow_neg hx0.le, le_inv_comm₀ (by norm_num) hxd]
  simpa using h1

/-- **There is an integer cardinality strictly inside the window.**  For `0 ≤ θ < η` and all small
`δ`, some `n` satisfies `δ^{-θ} ≤ n ≤ δ^{-η}`: the band `δ^{-θ}` of a hypothetical `GainBand` and
the Katz–Tao ceiling `δ^{-η}` granted by its own hypothesis overlap. -/
theorem exists_card_in_window {θ η : ℝ} (hθ : 0 ≤ θ) (hθη : θ < η) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∃ n : ℕ, 0 < n ∧ (δ : ℝ) ^ (-θ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (δ : ℝ) ^ (-η) := by
  set d : ℝ := η - θ with hd_def
  have hd : 0 < d := by simp only [hd_def]; linarith
  set t : NNReal := Real.toNNReal (min (1 / 2 : ℝ) ((1 / 2 : ℝ) ^ (1 / d))) with ht_def
  have hthpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (1 / d) := Real.rpow_pos_of_pos (by norm_num) _
  have ht0 : 0 < t := by
    rw [ht_def]
    simpa using lt_min (by norm_num : (0 : ℝ) < 1 / 2) hthpos
  filter_upwards [Ioo_mem_nhdsGT ht0] with δ hδ
  obtain ⟨hδ0, hδt⟩ := hδ
  have hδ0R : (0 : ℝ) < (δ : ℝ) := hδ0
  have hδtR : (δ : ℝ) ≤ min (1 / 2 : ℝ) ((1 / 2 : ℝ) ^ (1 / d)) := by
    have hcoe : (δ : ℝ) ≤ ((Real.toNNReal (min (1 / 2 : ℝ) ((1 / 2 : ℝ) ^ (1 / d)))) : ℝ) := by
      exact_mod_cast (by rw [ht_def] at hδt; exact hδt.le)
    refine hcoe.trans ?_
    rw [Real.coe_toNNReal _ (le_of_lt (lt_min (by norm_num) hthpos))]
  have hδhalf : (δ : ℝ) ≤ 1 / 2 := le_trans hδtR (min_le_left _ _)
  have hδ1 : (δ : ℝ) ≤ 1 := by linarith
  have h2 : (2 : ℝ) ≤ (δ : ℝ) ^ (-d) :=
    two_le_rpow_neg hd hδ0R (le_trans hδtR (min_le_right _ _))
  have hone : (1 : ℝ) ≤ (δ : ℝ) ^ (-θ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ0R hδ1 (by linarith)
  refine ⟨⌈(δ : ℝ) ^ (-θ)⌉₊, Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos hδ0R _),
    Nat.le_ceil _, ?_⟩
  have hlt : ((⌈(δ : ℝ) ^ (-θ)⌉₊ : ℝ)) < (δ : ℝ) ^ (-θ) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg hδ0R.le _)
  have hsum : (δ : ℝ) ^ (-θ) + 1 ≤ 2 * (δ : ℝ) ^ (-θ) := by linarith
  have hprod : 2 * (δ : ℝ) ^ (-θ) ≤ (δ : ℝ) ^ (-θ) * (δ : ℝ) ^ (-d) := by
    have := Real.rpow_pos_of_pos hδ0R (-θ)
    nlinarith
  have heq : (δ : ℝ) ^ (-θ) * (δ : ℝ) ^ (-d) = (δ : ℝ) ^ (-η) := by
    rw [← Real.rpow_add hδ0R]
    congr 1
    simp only [hd_def]
    ring
  linarith [hlt, hsum, hprod, heq.ge, heq.le]

end Window

/-! ## Part II — the witness: `n` coincident fully shaded `δ`-tubes -/

section Witness

universe w

/-- The index set: `n` copies, in an arbitrary universe. -/
def centralCopies (n : ℕ) : Finset (ULift.{w} ℕ) :=
  (Finset.range n).map (Equiv.ulift.{w, 0}.symm.toEmbedding)

/-- The family: `n` coincident copies of the fully shaded central unit `δ`-tube
`Kakeya.centralUnitTube`. -/
noncomputable def centralCopyFam (δ : NNReal) : ULift.{w} ℕ → ShadedTube δ Space3 :=
  fun _ => Kakeya.fullyShadedTube (Kakeya.centralUnitTube δ)

@[simp] theorem centralCopies_card (n : ℕ) : (centralCopies.{w} n).card = n := by
  simp [centralCopies]

theorem centralCopies_nonempty {n : ℕ} (hn : 0 < n) : (centralCopies.{w} n).Nonempty := by
  rw [← Finset.card_pos, centralCopies_card]; exact hn

@[simp] theorem centralCopyFam_shade (δ : NNReal) (i : ULift.{w} ℕ) :
    (centralCopyFam δ i).shade = (Kakeya.centralUnitTube δ).carrier := rfl

@[simp] theorem centralCopyFam_carrier (δ : NNReal) (i : ULift.{w} ℕ) :
    (centralCopyFam δ i).carrier = (Kakeya.centralUnitTube δ).carrier := rfl

theorem sum_shade_centralCopyFam (δ : NNReal) (n : ℕ) :
    ∑ i ∈ centralCopies.{w} n, volume (centralCopyFam δ i).shade
      = (n : ENNReal) * volume (Kakeya.centralUnitTube δ).carrier := by
  simp [centralCopyFam_shade]

theorem sum_carrier_centralCopyFam (δ : NNReal) (n : ℕ) :
    ∑ i ∈ centralCopies.{w} n, volume (centralCopyFam δ i).carrier
      = (n : ENNReal) * volume (Kakeya.centralUnitTube δ).carrier := by
  simp [centralCopyFam_carrier]

theorem iUnion_shade_centralCopyFam (δ : NNReal) {n : ℕ} (hn : 0 < n) :
    (⋃ i ∈ centralCopies.{w} n, (centralCopyFam δ i).shade)
      = (Kakeya.centralUnitTube δ).carrier := by
  obtain ⟨j, hj⟩ := centralCopies_nonempty.{w} hn
  refine Set.Subset.antisymm (Set.iUnion₂_subset fun i _ => by rw [centralCopyFam_shade]) ?_
  intro x hx
  exact Set.mem_iUnion₂.mpr ⟨j, hj, by rwa [centralCopyFam_shade]⟩

theorem centralCopyFam_ball {δ : NNReal} (hδ : δ ≤ 1 / 2) :
    ∀ i ∈ centralCopies.{w} n, (centralCopyFam δ i).carrier ⊆ Metric.closedBall 0 1 :=
  fun _ _ => Kakeya.centralUnitTube_carrier_subset_closedBall hδ

/-- `n` coincident bodies are `C`-Katz–Tao as soon as `n ≤ C`: the maximal density of a family is
at most its cardinality (`Kakeya.maxDensity_le_card`). -/
theorem centralCopyFam_katzTao {δ : NNReal} {n : ℕ} {C : ENNReal} (hC : (n : ENNReal) ≤ C) :
    ConvexSpaceBody.IsKatzTao (centralCopies.{w} n)
      (fun i ↦ (centralCopyFam δ i).toConvexSpaceBody) C := by
  rw [ConvexSpaceBody.IsKatzTao_def]
  refine le_trans (Kakeya.maxDensity_le_card _ _) ?_
  rw [centralCopies_card]
  exact hC

/-- The family is fully shaded, so its fullness is exactly `1`. -/
theorem centralCopyFam_fullness {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {n : ℕ} (hn : 0 < n) :
    ShadedBody.fullness (centralCopies.{w} n)
      (fun i ↦ (centralCopyFam δ i).toShadedBody) = 1 := by
  have hvol := Tube.volume_pos_and_lt_top hδ0 hδ1 (Kakeya.centralUnitTube δ)
  have hnE : ((n : ENNReal)) ≠ 0 := by simpa using hn.ne'
  have hmul0 : (n : ENNReal) * volume (Kakeya.centralUnitTube δ).carrier ≠ 0 :=
    mul_ne_zero hnE hvol.1.ne'
  have hmult : (n : ENNReal) * volume (Kakeya.centralUnitTube δ).carrier ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hvol.2.ne
  have h := ShadedBody.fullness_def (centralCopies.{w} n)
    (fun i ↦ (centralCopyFam δ i).toShadedBody)
  rw [show (∑ i ∈ centralCopies.{w} n, volume ((centralCopyFam δ i).toShadedBody).shade)
        = (n : ENNReal) * volume (Kakeya.centralUnitTube δ).carrier from
      sum_shade_centralCopyFam δ n,
    show (∑ i ∈ centralCopies.{w} n, volume ((centralCopyFam δ i).toShadedBody).carrier)
        = (n : ENNReal) * volume (Kakeya.centralUnitTube δ).carrier from
      sum_carrier_centralCopyFam δ n,
    ENNReal.div_self hmul0 hmult] at h
  exact_mod_cast h

/-- Transfer of a cardinality bound against `δ^{-η}` from `ℝ` to `ENNReal`. -/
theorem natCast_le_rpow_coe {δ : NNReal} {n : ℕ} {η : ℝ} (hδ0 : 0 < δ)
    (h : (n : ℝ) ≤ (δ : ℝ) ^ (-η)) : (n : ENNReal) ≤ (δ : ENNReal) ^ (-η) := by
  rw [show ((n : ENNReal)) = (((n : NNReal)) : ENNReal) by simp,
    ← ENNReal.coe_rpow_of_ne_zero hδ0.ne' (-η), ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  exact h

/-- **Every hypothesis of `Kakeya.ML2Squeeze.GainOnly` is met by the coincident family**, at every
cardinality `n` up to the Katz–Tao ceiling `δ^{-η}` that the hypothesis itself grants. -/
theorem centralCopies_admissible {δ : NNReal} {n : ℕ} {η : ℝ} (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hη : 0 ≤ η) (hn : 0 < n) (hnC : (n : ENNReal) ≤ (δ : ENNReal) ^ (-η)) :
    (∀ i ∈ centralCopies.{w} n, (centralCopyFam δ i).carrier ⊆ Metric.closedBall 0 1)
      ∧ ConvexSpaceBody.IsKatzTao (centralCopies.{w} n)
          (fun i ↦ (centralCopyFam δ i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η))
      ∧ ShadedBody.fullness (centralCopies.{w} n)
          (fun i ↦ (centralCopyFam δ i).toShadedBody) ≥ δ ^ η := by
  have hδ1 : δ ≤ 1 := le_trans hδhalf (by norm_num)
  refine ⟨centralCopyFam_ball hδhalf, centralCopyFam_katzTao hnC, ?_⟩
  rw [centralCopyFam_fullness hδ0 hδ1 hn]
  exact NNReal.rpow_le_one hδ1 hη

/-- **The gain fails on every family of coincident tubes.**

`n` coincident fully shaded `δ`-tubes have `μ = n` and `|𝕋| = n`, so a gain `μ ≤ δ^g |𝕋|^β` reads
`n ≤ δ^g n^β`; with `n^β ≤ n` this is `1 ≤ δ^g`, which is false for `g > 0` and `δ < 1`.

The hypothesis `hnβ : n^β ≤ n` holds for `n = 1` at every `β` (`ENNReal.one_rpow`) and for every
`n ≥ 1` at every `β ≤ 1`, which is Main Lemma 2's whole range. -/
theorem gain_fails_on_copies {δ : NNReal} {n : ℕ} {β g : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 0 < n) (hg : 0 < g)
    (hnβ : ((n : ENNReal)) ^ β ≤ (n : ENNReal))
    (hmass : ∑ i ∈ centralCopies.{w} n, volume (centralCopyFam δ i).shade
      ≤ (δ : ENNReal) ^ g * ((centralCopies.{w} n).card : ENNReal) ^ β
        * volume (⋃ i ∈ centralCopies.{w} n, (centralCopyFam δ i).shade)) :
    False := by
  have hvol := Tube.volume_pos_and_lt_top hδ0 hδ1.le (Kakeya.centralUnitTube δ)
  set V := volume (Kakeya.centralUnitTube δ).carrier with hV
  have hnE0 : ((n : ENNReal)) ≠ 0 := by simpa using hn.ne'
  rw [sum_shade_centralCopyFam δ n, iUnion_shade_centralCopyFam δ hn, centralCopies_card] at hmass
  -- `n · V ≤ δ^g · n^β · V ≤ (δ^g · n) · V`
  have hstep : (n : ENNReal) * V ≤ ((δ : ENNReal) ^ g * (n : ENNReal)) * V := by
    refine hmass.trans ?_
    exact mul_le_mul' (mul_le_mul' le_rfl hnβ) le_rfl
  -- cancel `V`
  have hcancel : (n : ENNReal) ≤ (δ : ENNReal) ^ g * (n : ENNReal) := by
    rw [← ENNReal.mul_le_mul_iff_right hvol.1.ne' hvol.2.ne]
    calc V * (n : ENNReal) = (n : ENNReal) * V := mul_comm _ _
      _ ≤ ((δ : ENNReal) ^ g * (n : ENNReal)) * V := hstep
      _ = V * ((δ : ENNReal) ^ g * (n : ENNReal)) := mul_comm _ _
  -- cancel `n`
  have hone : (1 : ENNReal) ≤ (δ : ENNReal) ^ g := by
    rw [← ENNReal.mul_le_mul_iff_right hnE0 (ENNReal.natCast_ne_top n)]
    calc (n : ENNReal) * 1 = (n : ENNReal) := mul_one _
      _ ≤ (δ : ENNReal) ^ g * (n : ENNReal) := hcancel
      _ = (n : ENNReal) * (δ : ENNReal) ^ g := mul_comm _ _
  exact absurd hone (not_le.mpr (ENNReal.rpow_lt_one (by exact_mod_cast hδ1) hg))

end Witness

/-! ## Part III — the refutation of `GainOnly` and of `GainDichotomy` -/

section Refutation

universe w

/-- **`Kakeya.ML2Squeeze.GainOnly β g η` is false.**

The witness is the one-element family `{T}` with `T` the fully shaded central unit `δ`-tube: it
satisfies containment in `B₁`, is `δ^{-η}`-Katz–Tao (its maximal density is at most its
cardinality `1 ≤ δ^{-η}`), and has fullness exactly `1 ≥ δ^η`; but its multiplicity is `1`, while
the gain demands `μ ≤ δ^g · 1^β = δ^g < 1`.

No hypothesis is placed on `β`, and `0 ≤ η` is only what makes the ambient hypotheses satisfiable
at all (for `η < 0` the fullness clause `λ ≥ δ^η > 1` is unsatisfiable). -/
theorem not_gainOnly {β g η : ℝ} (hg : 0 < g) (hη : 0 ≤ η) : ¬ GainOnly.{w} β g η := by
  intro h
  have hev : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      (∀ {ι : Type w} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade))
      ∧ δ ∈ Set.Ioo (0 : NNReal) (1 / 2) := by
    filter_upwards [h, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 / 2 by norm_num)] with δ h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨δ, hgain, hδ0, hδhalf⟩ := hev.exists
  have hδhalf' : δ ≤ 1 / 2 := hδhalf.le
  have hδ1 : δ < 1 := lt_of_lt_of_le hδhalf (by norm_num)
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1.le
  have hCge : ((1 : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-η) := by
    simpa using ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith : (-η : ℝ) ≤ 0)
  obtain ⟨hball, hKT, hfull⟩ := centralCopies_admissible.{w} hδ0 hδhalf' hη Nat.one_pos hCge
  exact gain_fails_on_copies (n := 1) (β := β) hδ0 hδ1 Nat.one_pos hg (by simp)
    (hgain (centralCopies.{w} 1) (centralCopyFam δ) hball hKT hfull)

/-! ### The witness meets Lemma 9.1's *other* two hypotheses as well

The `n = 1` witness satisfies every side condition GWZ Lemma 9.1 carries **except** its third
bullet, the scale count `Kakeya.ML2Squeeze.ScaleCount`.  Pairwise essential distinctness is
vacuous on a one-element family (`Kakeya.ML2GainFloor.centralCopies_one_pairwise`), and GWZ
Definition 2.2 uniformity holds at the constant `1`
(`Kakeya.ML2GainFloor.centralCopies_one_uniform`).  Since
`Kakeya.ML2Squeeze.scaleCount_forces_band` shows the third bullet already implies `δ⁻¹ ≤ |𝕋|`,
**the cardinality content of Lemma 9.1 is exactly what keeps Lemma 9.1 consistent**, and it is
exactly what `GainOnly`/`GainDichotomy` delete. -/

/-- Adding an essential-distinctness hypothesis does **not** rescue the refutation's target: every
pairwise relation holds vacuously on the one-element witness. -/
theorem centralCopies_one_pairwise (r : ULift.{w} ℕ → ULift.{w} ℕ → Prop) :
    ((centralCopies.{w} 1 : Finset (ULift.{w} ℕ)) : Set (ULift.{w} ℕ)).Pairwise r := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (centralCopies_card.{w} 1)
  rw [ha]
  simp

/-- The one-element witness is a uniform tube set at the constant `1`, so it also meets GWZ
Definition 2.2 — Lemma 9.1's second hypothesis. -/
theorem centralCopies_one_uniform {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Nonempty (ShadedTube.ShadedUniformTubeSet (centralCopies.{w} 1) (centralCopyFam δ)
      (Tube.ssfGridLen δ) 1) := by
  refine Kakeya.nonempty_shadedUniformTubeSet_of_card_le hδ0 hδ1 _ _ _ le_rfl ?_ ?_
  · rw [centralCopies_card]; norm_num
  · intro i hi j hj _ _
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (centralCopies_card.{w} 1)
    rw [ha, Finset.mem_singleton] at hi hj
    rw [hi, hj]

/-- **On the very witness that refutes the gain, the *accuracy* alternative is true.**

The coincident family has `μ ≤ |𝕋| = n ≤ δ^{-η} ≤ δ^{-ε₀}` for every `ε₀ ≥ η`.  So the two
alternatives of `Kakeya.ML2Assembly.Dichotomy` behave oppositely once the cardinality clause is
removed: the absolute-accuracy alternative `μ ≤ δ^{-ε₀}` stays **true** and is merely too weak to
close the goal, while the gain alternative `μ ≤ δ^g |𝕋|^β` becomes **false**.  Deleting the
cardinality clause therefore does not move the difficulty from one alternative to the other; it
destroys the only alternative that was strong enough. -/
theorem centralCopies_accuracy {δ : NNReal} {n : ℕ} {η ε₀ : ℝ} (hδ1 : δ ≤ 1)
    (hηε : η ≤ ε₀) (hnC : (n : ENNReal) ≤ (δ : ENNReal) ^ (-η)) :
    ShadedBody.multiplicity (centralCopies.{w} n)
      (fun i ↦ (centralCopyFam δ i).toShadedBody) ≤ (δ : ENNReal) ^ (-ε₀) := by
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  calc ShadedBody.multiplicity (centralCopies.{w} n)
        (fun i ↦ (centralCopyFam δ i).toShadedBody)
      ≤ ((centralCopies.{w} n).card : ENNReal) := ShadedBody.multiplicity_le_card _ _
    _ = (n : ENNReal) := by rw [centralCopies_card]
    _ ≤ (δ : ENNReal) ^ (-η) := hnC
    _ ≤ (δ : ENNReal) ^ (-ε₀) := ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)

/-- **The hypothesis of `Kakeya.ML2Squeeze.katzTaoEstimate_sub_of_gainOnly` has no instance.**
That reduction is stated at the budget `4c ≤ g` with `c > 0` and `0 < η`, and on exactly that
range `Kakeya.ML2Squeeze.GainOnly` is false.  So the reduction compiles but can never fire. -/
theorem gainOnly_hypothesis_unsatisfiable {β g η c : ℝ} (hc : 0 < c) (hη0 : 0 < η)
    (hg : 4 * c ≤ g) : ¬ GainOnly.{w} β g η :=
  not_gainOnly (by linarith) hη0.le

/-- **`Kakeya.ML2Squeeze.GainOnlyMult`, transcribed verbatim** from the auxiliary Part VI: the same
predicate in GWZ Lemma 9.1's own currency, the multiplicity bound `μ ≤ δ^g |𝕋|^β`. -/
def GainOnlyMultBody (β g η : ℝ) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type w} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody)
        ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β

/-- The currency conversion, reproved here: `ShadedBody.multiplicity_le_iff` is an unconditional
`iff`, so the mass form and the multiplicity form of a gain are the same statement. -/
theorem gainOnly_of_gainOnlyMultBody {β g η : ℝ} (h : GainOnlyMultBody.{w} β g η) :
    GainOnly.{w} β g η := by
  filter_upwards [h] with δ hδ
  intro ι s T hball hKT hfull
  exact (ShadedBody.multiplicity_le_iff s (fun i ↦ (T i).toShadedBody)).mp (hδ s T hball hKT hfull)

/-- **GWZ Lemma 9.1's conclusion, asked of every admissible family, is false.**

This is *not* a refutation of GWZ Lemma 9.1 itself.  Lemma 9.1 carries the scale-count hypothesis
`Kakeya.ML2Squeeze.ScaleCount`, and `Kakeya.ML2Squeeze.scaleCount_forces_band` shows that
hypothesis already implies `δ⁻¹ ≤ |𝕋|`; on that band `δ^g |𝕋|^β ≥ δ^{g-β} ≥ 1` and nothing here
applies.  What is refuted is the *deletion* of that cardinality content, which is exactly what
`Kakeya.ML2Squeeze.GainOnlyMult`, `Kakeya.ML2Squeeze.GainOnly` and
`Kakeya.ML2Squeeze.GainDichotomy` do. -/
theorem not_gainOnlyMultBody {β g η : ℝ} (hg : 0 < g) (hη : 0 ≤ η) :
    ¬ GainOnlyMultBody.{w} β g η :=
  fun h => not_gainOnly hg hη (gainOnly_of_gainOnlyMultBody h)

/-- **`Kakeya.ML2Squeeze.GainDichotomy`, transcribed verbatim** from the auxiliary Part VI of
`Reduction/BandSqueeze.lean` (worktree `w30`).  Kept under a separate name so that nothing in this
file shadows the real constant once that patch lands; the compatibility
`example : Kakeya.ML2Squeeze.GainDichotomy = GainDichotomyBody := rfl` should be added then. -/
def GainDichotomyBody (β g₁ g₂ η : ℝ) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type w} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      (ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody)
          ≤ (δ : ENNReal) ^ g₁ * (s.card : ENNReal) ^ β)
        ∨ (ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody)
          ≤ (δ : ENNReal) ^ g₂ * (s.card : ENNReal) ^ β)

/-- The dichotomy gives `Kakeya.ML2Squeeze.GainOnly` at the smaller of the two gains.  This is
`Kakeya.ML2Squeeze.gainOnlyMult_of_gainDichotomy` followed by
`Kakeya.ML2Squeeze.gainOnly_iff_gainOnlyMult`, reproved here so that this file does not depend on
the auxiliary Part VI. -/
theorem gainOnly_of_gainDichotomyBody {β g₁ g₂ η : ℝ} (h : GainDichotomyBody.{w} β g₁ g₂ η) :
    GainOnly.{w} β (min g₁ g₂) η := by
  filter_upwards [h, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδ hδ01
  obtain ⟨-, hδ1⟩ := hδ01
  intro ι s T hball hKT hfull
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1.le
  refine (ShadedBody.multiplicity_le_iff s (fun i ↦ (T i).toShadedBody)).mp ?_
  rcases hδ s T hball hKT hfull with hg | hg
  · exact hg.trans (mul_le_mul'
      (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (min_le_left _ _)) le_rfl)
  · exact hg.trans (mul_le_mul'
      (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (min_le_right _ _)) le_rfl)

/-- **The target of  is false.**

`Kakeya.ML2Squeeze.katzTaoEstimate_sub_of_gainDichotomy` needs `4c ≤ min g₁ g₂` with `c > 0`,
hence `0 < g₁` and `0 < g₂`; on exactly that range `GainDichotomy` has no model. -/
theorem not_gainDichotomyBody {β g₁ g₂ η : ℝ} (hg₁ : 0 < g₁) (hg₂ : 0 < g₂) (hη : 0 ≤ η) :
    ¬ GainDichotomyBody.{w} β g₁ g₂ η :=
  fun h => not_gainOnly (lt_min hg₁ hg₂) hη (gainOnly_of_gainDichotomyBody h)

/-- The same statement in the form the budget of
`Kakeya.ML2Squeeze.katzTaoEstimate_sub_of_gainDichotomy` presents it. -/
theorem not_gainDichotomyBody_of_budget {β g₁ g₂ η c : ℝ} (hc : 0 < c)
    (hg : 4 * c ≤ min g₁ g₂) (hη : 0 ≤ η) : ¬ GainDichotomyBody.{w} β g₁ g₂ η := by
  have h1 : 0 < min g₁ g₂ := lt_of_lt_of_le (by linarith) hg
  exact not_gainDichotomyBody (lt_of_lt_of_le h1 (min_le_left _ _))
    (lt_of_lt_of_le h1 (min_le_right _ _)) hη

end Refutation

/-! ## Part IV — the strongest true form, and why it is circular -/

section Band

universe w

/-- **The gain, banded.**  `Kakeya.ML2Squeeze.GainOnly` with the cardinality floor that
`Kakeya.ML2GainFloor.card_floor_of_gain` shows it cannot do without.  At `θ = 1` this is exactly
alternative (ii) of `Kakeya.ML2Assembly.Dichotomy` under that dichotomy's own cardinality
hypothesis. -/
def GainBand (θ β g η : ℝ) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type w} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      (δ : ℝ) ^ (-θ) ≤ (s.card : ℝ) →
      ∑ i ∈ s, volume (T i).shade
        ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade)

/-- A banded gain delivers exactly the banded estimate — no `SmallCard`, no `2c ≤ β`, and the
`ε`-free budget `4c ≤ g`.  This is `Kakeya.ML2Squeeze.katzTaoEstimateGE_sub_of_dichotomy` with
the absolute-accuracy alternative deleted as well. -/
theorem katzTaoEstimateGE_sub_of_gainBand {θ β g η c : ℝ}
    (hc : 0 < c) (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g)
    (hband : GainBand.{w} θ β g η) :
    KatzTaoEstimateGE.{w} θ (β - c) := by
  intro ε hε
  refine ⟨η, hη0, ?_⟩
  filter_upwards [hband, Kakeya.ML2Assembly.eventually_card_thresholds] with δ hδband hδthr
  obtain ⟨hδ0, hδ1, hδC⟩ := hδthr
  intro ι s T hball hKT hfull hcard
  have hmass := hδband s T hball hKT hfull hcard
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
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

/-- **A band below the Katz–Tao ceiling does not rescue the gain either.**

For `0 ≤ θ < η` the window `δ^{-θ} ≤ |𝕋| ≤ δ^{-η}` is nonempty
(`Kakeya.ML2GainFloor.exists_card_in_window`) and the coincident family sits inside it, so
`Kakeya.ML2GainFloor.GainBand θ β g η` is **false**.  Any cardinality floor that a true gain can
carry therefore has to exceed the Katz–Tao ceiling granted by the gain's own hypothesis — in
particular it cannot be taken small in the hope of shrinking the residue.  `β ≤ 1` is Main Lemma
2's own range. -/
theorem not_gainBand_of_lt_katzTaoCeiling {θ β g η : ℝ} (hθ : 0 ≤ θ) (hθη : θ < η)
    (hβ : β ≤ 1) (hg : 0 < g) : ¬ GainBand.{w} θ β g η := by
  intro h
  have hev : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      (∀ {ι : Type w} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (δ : ℝ) ^ (-θ) ≤ (s.card : ℝ) →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade))
      ∧ (∃ n : ℕ, 0 < n ∧ (δ : ℝ) ^ (-θ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (δ : ℝ) ^ (-η))
      ∧ δ ∈ Set.Ioo (0 : NNReal) (1 / 2) := by
    filter_upwards [h, exists_card_in_window hθ hθη,
      Ioo_mem_nhdsGT (show (0 : NNReal) < 1 / 2 by norm_num)] with δ h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨δ, hgain, ⟨n, hn, hlow, hhigh⟩, hδ0, hδhalf⟩ := hev.exists
  have hδhalf' : δ ≤ 1 / 2 := hδhalf.le
  have hδ1 : δ < 1 := lt_of_lt_of_le hδhalf (by norm_num)
  have hnC : (n : ENNReal) ≤ (δ : ENNReal) ^ (-η) := natCast_le_rpow_coe hδ0 hhigh
  obtain ⟨hball, hKT, hfull⟩ := centralCopies_admissible.{w} hδ0 hδhalf' (by linarith) hn hnC
  have h1n : (1 : ENNReal) ≤ (n : ENNReal) := by exact_mod_cast hn
  have hnβ : ((n : ENNReal)) ^ β ≤ (n : ENNReal) := by
    calc ((n : ENNReal)) ^ β ≤ ((n : ENNReal)) ^ (1 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_le h1n hβ
      _ = (n : ENNReal) := ENNReal.rpow_one _
  refine gain_fails_on_copies (n := n) (β := β) hδ0 hδ1 hn hg hnβ ?_
  refine hgain (centralCopies.{w} n) (centralCopyFam δ) hball hKT hfull ?_
  rw [centralCopies_card]
  exact hlow

/-- **The residue of the banded gain is Main Lemma 2's own conclusion.**

By `Kakeya.ML2Squeeze.residue_of_banded` what is left after a banded gain is
`Kakeya.ML2Squeeze.SmallCardCut θ (β - c)`, and by
`Kakeya.ML2Squeeze.forall_cut_circular` that is equivalent to `KatzTaoEstimate Space3 (β - c)` at
**every** `θ > 0`.  So a banded gain leaves an obligation equivalent to the goal. -/
theorem gainBand_residue_is_the_goal {θ β g η c : ℝ}
    (hc : 0 < c) (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g) (hθ : 0 < θ) (hγ : 0 ≤ β - c)
    (hband : GainBand.{w} θ β g η) :
    (Kakeya.KatzTaoEstimate.{w} Space3 (β - c) ↔ SmallCardCut.{w} θ (β - c))
      ∧ (SmallCardCut.{w} θ (β - c) ↔ Kakeya.KatzTaoEstimate.{w} Space3 (β - c)) :=
  ⟨Kakeya.ML2Squeeze.residue_of_banded hγ hθ
      (katzTaoEstimateGE_sub_of_gainBand hc hη0 hη1 hg hband),
    Kakeya.ML2Squeeze.forall_cut_circular hγ θ hθ⟩

/-- **The dichotomy, in one statement.**  Either the gain carries no cardinality floor, and then it
is false; or it carries a floor `θ > 0`, and then what it leaves is the goal. -/
theorem gain_horns {β g η c : ℝ} (hc : 0 < c) (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g)
    (hγ : 0 ≤ β - c) {θ : ℝ} (hθ : 0 < θ) :
    ¬ GainOnly.{w} β g η
      ∧ (GainBand.{w} θ β g η →
          (SmallCardCut.{w} θ (β - c) ↔ Kakeya.KatzTaoEstimate.{w} Space3 (β - c))) :=
  ⟨not_gainOnly (by linarith) hη0.le,
    fun hband => (gainBand_residue_is_the_goal hc hη0 hη1 hg hθ hγ hband).2⟩

end Band

end Kakeya.ML2GainFloor

end
