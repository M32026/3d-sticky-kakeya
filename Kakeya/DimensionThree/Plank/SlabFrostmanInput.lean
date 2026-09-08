/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimates

/-!
# The analytic input of the per-slab step of GWZ Lemma 6.4

This module isolates, in exactly two declarations, everything the per-slab estimate
`Plank.frostmanSlabUnionVolumeLowerBound` needs from GWZ Lemma 3.9. Nothing about planks, slabs or
fibres appears here.

## Why a separate two-scale form is needed

`Kakeya.FrostmanEstimate.multiplicity_bound_isFrostmanIn` is stated at a *single* scale: the
physical tube radius `δ` also carries the `δ^(-ε)` loss and the fullness threshold `δ^η`. Section 6
needs the two separated, because the fibre it feeds in consists of tubes of radius `b/8` while the
only fullness available is at the *plank* scale `a ≤ b`.
`Kakeya.FrostmanEstimate.generalize_tau` performs that separation but forces the Frostman constant
to be `τ^(-η)`, destroying the `CF^(1-β/2)` factor that Lemma 6.4 must keep.

`Kakeya.FrostmanEstimate.multiplicity_bound_tau_isFrostmanIn` below is the combined form — two
scales **and** a free `CF` — with the **corrected quantifier order**

`∀ᶠ δ, ∀ τ ≤ δ, ∀ family, ∀ CF`.

The order matters: `Plank.frostmanSlabUnionVolumeLowerBound` fixes its threshold `b₀` before the
plank family and hence before its Frostman constant `CF`, so a `∀ CF, ∀ᶠ δ` form (whose eventual set
of scales may depend on `CF`) cannot be used. The corrected order is available because
`Kakeya.FrostmanEstimate.multiplicity_bound` is now stated with the family's own canonical Frostman
constant, so no `CF` occurs before the `∀ᶠ δ`.

The proof is GWZ Remark 3.6's dichotomy on `τ` against `δ^C`:

* **large `τ`** (`δ^C ≤ τ`): then `τ^η ≥ δ^(Cη)`, so the fullness hypothesis feeds the single-scale
  bound at exponent `η₁ = C·η`, and `τ ≤ δ` upgrades its `δ^(-ε)` to `τ^(-ε)`;
* **small `τ`** (`τ < δ^C`): then `τ^(-ε)` alone already dominates the trivial cardinality bound
  `multiplicity ≤ |s| ≲ δ^(-2n)` from `Tube.card_le_of_EssDistinct`; this is
  `Kakeya.FrostmanEstimate.generalize_small_tau`, whose `CF`-free right-hand side is smaller than
  ours because `1 ≤ CF` and `0 < 1 - β/2`.

## Universe descent

`Kakeya.FrostmanEstimate.{v}` quantifies its tube families over `ι : Type v`, but the per-slab step
runs the estimate at the representative index type `Plank.ThickenedPlank θ b _ _`, a `Type 0`.
Rather than pinning every downstream statement to `FrostmanEstimate.{0}` — which would propagate a
universe annotation through the whole Section 6 interface —
`Kakeya.FrostmanEstimate.toTypeZero` descends the hypothesis once, by running a `Type 0`-indexed family
through `ULift`. Every quantity involved (`ShadedBody.fullness`, `ShadedBody.multiplicity`,
`Finset.card`, `ConvexSpaceBody.densityIn`) is a sum or a union over the index set and is therefore
invariant under the reindexing.
-/

@[expose] public section

open MeasureTheory Topology ConvexSpaceBody Filter ShadedBody
open scoped NNReal ENNReal

namespace Kakeya

section PerSlabKF

universe v

variable
  (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Universe descent for the partial Frostman estimate.**

`Kakeya.FrostmanEstimate.{v} E β` asserts the tube multiplicity bound for families indexed by an
arbitrary `ι : Type v`. Applying it to a family indexed by a `Type 0` — which is what the Section 6
per-slab step needs, its index type being `Plank.ThickenedPlank θ b _ _` — is legitimate: reindex
along `Equiv.ulift : ULift.{v} ι ≃ ι`, whose `ULift.{v} ι` lives in `Type v`. Every quantity in the
statement is a sum or a union over the index set, hence invariant under the reindexing. -/
theorem FrostmanEstimate.toTypeZero {β : ℝ} (h : FrostmanEstimate.{v} E β) :
    FrostmanEstimate.{0} E β := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ
  intro ι s T hB hED hFrost hFull
  let e : ι ↪ ULift.{v} ι := ⟨fun i => ⟨i⟩, by
    intro a b hab
    exact congrArg ULift.down hab⟩
  let s' : Finset (ULift.{v} ι) := s.map e
  let T' : ULift.{v} ι → ShadedTube δ E := fun x => T x.down
  have hB' : ∀ x ∈ s', (T' x).carrier ⊆ Metric.closedBall 0 1 := by
    intro x hx
    rcases Finset.mem_map.mp (by simpa [s'] using hx) with ⟨i, hi, rfl⟩
    simpa [T', e] using hB i hi
  have hED' : (s' : Set (ULift.{v} ι)).Pairwise
      (fun x y => IsEssentiallyDistinct ((T' x).carrier) ((T' y).carrier)) := by
    intro a ha b hb hab
    rcases Finset.mem_map.mp (by simpa [s'] using ha) with ⟨i, hi, rfl⟩
    rcases Finset.mem_map.mp (by simpa [s'] using hb) with ⟨j, hj, rfl⟩
    have hne : i ≠ j := by
      intro hij
      exact hab (congrArg e hij)
    exact hED hi hj hne
  have hFrost' : IsFrostmanIn s' (fun x => (T' x).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall (δ ^ (-η)) := by
    intro K' hK'
    simpa [s', T', e, densityIn, Finset.sum_map, Finset.filter_map] using hFrost K' hK'
  have hFull' : ShadedBody.fullness s' (fun x => (T' x).toShadedBody) ≥ δ ^ η := by
    simpa [s', T', e, ShadedBody.fullness, ShadedBody.fullness', Finset.sum_map]
      using hFull
  have hBound : ShadedBody.multiplicity s' (fun x => (T' x).toShadedBody) ≤
      δ ^ (-ε - 2 * β) * (s'.card * δ ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) :=
    hδ s' T' hB' hED' hFrost' hFull'
  have hcard : s'.card = s.card := Finset.card_map _
  have hsum : ∑ x ∈ s', volume ((T' x).toShadedBody).shade
      = ∑ i ∈ s, volume ((T i).toShadedBody).shade := Finset.sum_map _ _ _
  have hU : (⋃ x ∈ s', ((T' x).toShadedBody).shade) = ⋃ i ∈ s, ((T i).toShadedBody).shade := by
    ext y
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨x, hx, hy⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      exact ⟨i, hi, hy⟩
    · rintro ⟨i, hi, hy⟩
      exact ⟨e i, Finset.mem_map_of_mem e hi, hy⟩
  have hmult : ShadedBody.multiplicity s' (fun x => (T' x).toShadedBody)
      = ShadedBody.multiplicity s (fun i => (T i).toShadedBody) := by
    rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div, hsum, hU]
  rw [hmult, hcard] at hBound
  exact hBound

/-- **Two-scale Frostman multiplicity bound with a free Frostman constant, corrected quantifier
order** (GWZ Lemma 3.9 in the form of GWZ Remark 3.6).

Tubes have physical radius `δ`; the analytic scale is any `0 < τ ≤ δ`, which carries both the
fullness threshold `τ^η` and the loss `τ^(-ε)`. The Frostman constant `CF` is quantified **after**
the `∀ᶠ δ` and after the family, so the eventual set of admissible scales does not depend on it.
That is exactly what `Plank.frostmanSlabUnionVolumeLowerBound` needs, since it must fix `b₀` before
seeing the plank family. -/
theorem FrostmanEstimate.multiplicity_bound_tau_isFrostmanIn {β : ℝ} (hβ_0 : 0 ≤ β) (hβ_1 : β ≤ 1)
    (hn : 1 < Module.finrank ℝ E) (h : FrostmanEstimate.{v} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ τ : NNReal, 0 < τ → τ ≤ δ →
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ τ ^ η →
      ∀ CF : ENNReal, 1 ≤ CF → CF ≠ ⊤ →
      IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall CF →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (τ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) *
        (δ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
  intro ε hε
  have hn_pos : 0 < Module.finrank ℝ E := by omega
  have hβ2_pos : 0 < 1 - β / 2 := by nlinarith [hβ_1]
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hn_pos
  set D : ℝ := Tube.card_le_of_EssDistinct.C (Module.finrank ℝ E)
  have hD_pos : 0 < D := Tube.card_le_of_EssDistinct.C_pos
  obtain ⟨C, hC_pos, hC_ev⟩ := FrostmanEstimate.generalize_small_tau E hβ_0 ε hε
    (2 * Module.finrank ℝ E) (by
      have : 0 < Module.finrank ℝ E := Module.finrank_pos
      positivity) D hD_pos
  obtain ⟨η₁, hη₁_pos, hη_base⟩ :=
    FrostmanEstimate.multiplicity_bound_isFrostmanIn E hβ_0 hβ_1 hn h ε hε
  refine ⟨η₁ / C, by positivity, ?_⟩
  filter_upwards [hη_base, hC_ev, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)]
    with δ hδ_base hδ_small (hδ_pos : 0 < δ) hδ_lt_one
  intro τ hτ_pos hτ_le ι s T hB hED hFull CF hCF1 hCF_top hFrost
  by_cases hcase : δ ^ C ≤ τ
  · have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
    have hτ_pos_real : (0 : ℝ) < (τ : ℝ) := by exact_mod_cast hτ_pos
    have h_step : (δ : ℝ) ^ η₁ ≤ (τ : ℝ) ^ (η₁ / C) := calc
      (δ : ℝ) ^ η₁ = ((δ : ℝ) ^ C) ^ (η₁ / C) := by
        rw [← Real.rpow_mul hδ_pos_real.le]; congr 1; field_simp
      _ ≤ (τ : ℝ) ^ (η₁ / C) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hδ_pos_real.le _)
          (by exact_mod_cast hcase) (by positivity)
    have hFull' : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η₁ :=
      le_trans (by exact_mod_cast h_step) hFull
    have h_mult_base := hδ_base s T hB hED hFull' CF hFrost
    have hδ_le : (δ : ENNReal) ^ (-ε) ≤ (τ : ENNReal) ^ (-ε) := by
      rw [ennreal_coe_nnreal_rpow hδ_pos_real, ennreal_coe_nnreal_rpow hτ_pos_real]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.rpow_neg hδ_pos_real.le, Real.rpow_neg hτ_pos_real.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hτ_pos_real _)
        (Real.rpow_le_rpow hτ_pos_real.le (by exact_mod_cast hτ_le) hε.le)
    refine h_mult_base.trans ?_
    gcongr
  · push Not at hcase
    have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := hδ_pos
    have hcard : (s.card : ℝ) ≤ D * (δ : ℝ) ^ (-((2 : ℝ) * (Module.finrank ℝ E))) := by
      calc (s.card : ℝ)
          ≤ D * (1 / (δ : ℝ)) ^ (2 * Module.finrank ℝ E) :=
            Tube.card_le_of_EssDistinct hδ_pos 1 s (fun i => (T i).toTube) (fun i _ => hB i) hED
        _ = D * (δ : ℝ) ^ (-((2 : ℝ) * (Module.finrank ℝ E))) := by
            congr 1; rw [one_div, inv_pow]
            rw [show (2 : ℝ) * ↑(Module.finrank ℝ E) = ↑(2 * Module.finrank ℝ E) from by
              push_cast; ring]
            rw [Real.rpow_neg hδ_pos_real.le, Real.rpow_natCast]
    have h_mult_small := hδ_small τ hτ_pos hτ_le hcase s T hcard
    have h_cf : (1 : ENNReal) ≤ CF ^ (1 - β / 2) :=
      ENNReal.one_le_rpow hCF1 hβ2_pos
    calc multiplicity s (fun i ↦ (T i).toShadedBody)
        ≤ (τ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-2 * β) *
            ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) :=
            h_mult_small
      _ ≤ (τ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (δ : ENNReal) ^ (-2 * β) *
            ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
          have h_ab : (τ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-2 * β) ≤
              (τ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (δ : ENNReal) ^ (-2 * β) := by
            calc
              (τ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-2 * β)
                  = (τ : ENNReal) ^ (-ε) * (1 * (δ : ENNReal) ^ (-2 * β)) := by rw [one_mul]
              _ ≤ (τ : ENNReal) ^ (-ε) * (CF ^ (1 - β / 2) * (δ : ENNReal) ^ (-2 * β)) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h_cf bot_le) bot_le
              _ = (τ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (δ : ENNReal) ^ (-2 * β) := by
                  rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right h_ab bot_le

end PerSlabKF

end Kakeya

end
