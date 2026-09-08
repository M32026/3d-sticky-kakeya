/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.PartBFineEssDistinct
public import Kakeya.DimensionThree.Plank.InnerEDAssembly
public import Kakeya.Tube.EssentiallyDistinctShadeSelection
public import Kakeya.DimensionThree.Plank.Prop66BCoarseScale

/-!
# GWZ Proposition 6.6(B): the essential-distinctness reduction, paid by the `Δmax ^ (1 - β)` factor

`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` (GWZ Proposition 6.6(B),
`Kakeya/DimensionThree/Plank/Factorization.lean`) carried, when this file was written, no
essential-distinctness hypothesis on its fine family, and the source statement held that
it must not acquire one.  **That point of  has since been revised by **: GWZ's
"uniform" entails fine-family essential distinctness through Definition 2.1(ii) at `ρ = δ`, so the
live statement now carries `(q : Set ι).Pairwise IsEssentiallyDistinct` beside its window (pinned as
`Kakeya.Prop66BScale.statement_of_universal_prop66B_essDistinct`), and the clause is GWZ's, not
ours.  What remains ours is the same clause at the level of Proposition 5.1 — every proved form of
the Part-(B) chain (`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData` and its
ancestors) carries it, added at `Kakeya.factoringAndMultPropGlobal_of_remark53`, where GWZ's
Proposition 5.1 has none; on the live statement it is now discharged from 6.6(B)'s own hypothesis
rather than owed.  GWZ's `Δmax(T)^{1-β}` on the right-hand side remains the reason no *density*
hypothesis is needed, and that rejection stands.

This file's reduction was written against the alternative form and remains valid for it: it proves
`statement_of_universal_prop66B_branchingFloor` — which implies the live form trivially — from the
essentially distinct case, so it is now a strengthening of the live theorem rather than a step
toward it.

This file discharges that clause **at the 6.6(B) level**, with GWZ Lemma 6.1 and the whole chain
untouched, by GWZ's own Lemma 3.7 device:

1. **the cardinality-efficient subfamily** — `Kakeya.exists_random_subset`
   (`Kakeya/Probability.lean`), GWZ's *"random subset `T′ ⊂ T` of cardinality `|T|/Δmax(T)`"*,
   exported here in `ℝ≥0∞` and with the Katz–Tao exponent **chosen by the caller**
   (`Kakeya.exists_cardEfficient_subfamily_at`): `|s'| · Δmax(s) ≤ 2|s|`, `Δmax(s') ≤ δ^{-c}`,
   `δ^c ≤ λ(s')`, and `µ(s) ≤ δ^{-c} · Δmax(s) · µ(s')`;
2. **the shade-maximising essentially distinct selection** inside `s'` —
   `Kakeya.exists_pairwise_essDistinct_subfamily_sum_shade_le`
   (`Kakeya/Tube/EssentiallyDistinctShadeSelection.lean`), at the loss `1 + C_n · Δmax(s')`, which
   is sub-polynomial *because* `s'` is Katz–Tao;
3. **the accounting** — `Kakeya.multiplicity_bound_transfer_of_cardEfficient`
   (`Kakeya/DimensionThree/Plank/PartBFineEssDistinct.lean`): the `Δmax(s)` of the multiplicity
   loss and the `Δmax(s)^{-β}` of the cardinality drop combine to exactly the `Δmax(s)^{1-β}` that
   6.6(B) already carries.

The result, `Kakeya.multiplicity_bound_of_essDistinct_subfamily_bounds`, says: **if the 6.6(B)
bound holds for every nonempty pairwise essentially distinct, Katz–Tao, full subfamily of `s`, then
it holds for `s`** — at the same constant `A = (a/b)^β`, with the loss `δ^{-ε}` and the fullness
exponent chosen in advance.  No density hypothesis appears anywhere, and no statement in the chain
is altered.

## What this does and does not close

It closes the fine-family essential-distinctness obligation of Proposition 6.6(B) **as a
reduction**: the hypothesis `hsub` is exactly the essentially distinct case, which the proved chain
supplies —
*for a family that satisfies the chain's other hypotheses*.  What it does **not** do is restrict
those other hypotheses to the subfamily: a subfamily inherits neither `Tube.IsUniformAtScale` (its
branching bracket is two-sided, `IsUniformAtScale.le_mul_card_filter`) nor a factorisation datum
(`Kakeya.GlobalPlankFactorization`, `Kakeya.Section6PartBData`) — see the module docstring of
`Kakeya/Tube/EssentiallyDistinctShadeSelection.lean`.  Discharging `hsub` from the chain therefore
still requires re-uniformising the extracted subfamily and rebuilding its datum, which is the
remaining conjunct of the 6.6(B) proof, and it sits beside the datum obligations recorded in
`Kakeya/DimensionThree/Plank/MasterScaleLemma61.lean` (`Remark53Prop51`, outer representative
distinctness, the inner-scale threshold).

## The ledger, With `5c ≤ ε` and `3c ≤ η'` the losses are: `δ^{-c}` from the multiplicity transfer of step 1;
`(δ^{-c})^{1-β} ≤ δ^{-c}` from `Δmax(u) ≤ Δmax(s') ≤ δ^{-c}`; `1 + C_n δ^{-c} ≤ δ^{-2c}` from
step 2; and `2^β ≤ 2 ≤ δ^{-c}` from the factor `2` of the cardinality clause — five factors of
`δ^{-c}`, i.e. `δ^{-ε}`.  The fullness of the selected subfamily is at least
`δ^{c} / δ^{-2c} = δ^{3c} ≥ δ^{η'}`.
-/

@[expose] public section

open MeasureTheory Topology ConvexSpaceBody Filter
open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The `ℝ` / `ℝ≥0∞` bridge for the multiplicity -/

/-- `Kakeya.multiplicityRLocal` is the `toReal` of `ShadedBody.multiplicity`, and the multiplicity
is finite, so the two determine each other. -/
theorem multiplicity_eq_ofReal_multiplicityRLocal {ι : Type*} (s : Finset ι)
    (V : ι → ShadedBody E) :
    ShadedBody.multiplicity s V = ENNReal.ofReal (multiplicityRLocal E s V) := by
  unfold multiplicityRLocal
  rw [ENNReal.ofReal_toReal
    (ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (ShadedBody.multiplicity_le_card s V))]

/-- **The multiplicity-transfer clause of `Kakeya.exists_random_subset`, in `ℝ≥0∞`.**  The
`ℝ`-valued inequality `µ(s) ≤ L · D · µ(s')` between `multiplicityRLocal`s becomes the same
inequality between `ShadedBody.multiplicity`s, for any finite `D`. -/
theorem multiplicity_le_of_multiplicityRLocal_le {ι : Type*} {s s' : Finset ι}
    (V : ι → ShadedBody E) {L : ℝ} (hL : 0 ≤ L) {D : ℝ≥0∞} (hD : D ≠ ⊤)
    (h : multiplicityRLocal E s V ≤ L * D.toReal * multiplicityRLocal E s' V) :
    ShadedBody.multiplicity s V ≤ ENNReal.ofReal L * D * ShadedBody.multiplicity s' V := by
  rw [multiplicity_eq_ofReal_multiplicityRLocal s V,
    multiplicity_eq_ofReal_multiplicityRLocal s' V]
  calc ENNReal.ofReal (multiplicityRLocal E s V)
      ≤ ENNReal.ofReal (L * D.toReal * multiplicityRLocal E s' V) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal L * D * ENNReal.ofReal (multiplicityRLocal E s' V) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hL ENNReal.toReal_nonneg), ENNReal.ofReal_mul hL,
          ENNReal.ofReal_toReal hD]

/-- The bridge with the loss written as a power of `δ`. -/
theorem multiplicity_le_rpow_mul_of_multiplicityRLocal_le {ι : Type*} {s s' : Finset ι}
    (V : ι → ShadedBody E) {δ : ℝ≥0} (hδ : 0 < δ) (c : ℝ) {D : ℝ≥0∞} (hD : D ≠ ⊤)
    (h : multiplicityRLocal E s V ≤ (δ : ℝ) ^ (-c) * D.toReal * multiplicityRLocal E s' V) :
    ShadedBody.multiplicity s V ≤ (δ : ℝ≥0∞) ^ (-c) * D * ShadedBody.multiplicity s' V := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  rw [ennreal_coe_nnreal_rpow hδR (-c)]
  exact multiplicity_le_of_multiplicityRLocal_le V (Real.rpow_nonneg hδR.le _) hD h

/-! ### Reindexing bookkeeping -/

/-- Reindexing `multiplicityRLocal` along an embedding. -/
theorem multiplicityRLocal_map {ι κ : Type*} (s : Finset κ) (e : κ ↪ ι)
    (V : ι → ShadedBody E) :
    multiplicityRLocal E (s.map e) V = multiplicityRLocal E s (fun k => V (e k)) := by
  unfold multiplicityRLocal
  rw [ShadedBody.multiplicity_map]

/-- The maximal density of a family equals that of its `Finset.attach` reindexing. -/
theorem maxDensity_attach {ι : Type*} (s : Finset ι) (W : ι → ConvexSpaceBody E) :
    maxDensity s.attach (fun i => W i.1) = maxDensity s W := by
  have h := maxDensity_map s.attach (Function.Embedding.subtype (fun x => x ∈ s)) W
  rw [Finset.attach_map_val] at h
  exact h.symm

/-- The fullness of a family equals that of its `Finset.attach` reindexing. -/
theorem fullness_attach' {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) :
    ShadedBody.fullness s.attach (fun i => V i.1) = ShadedBody.fullness s V := by
  have h := ShadedBody.fullness_map s.attach (Function.Embedding.subtype (fun x => x ∈ s)) V
  rw [Finset.attach_map_val] at h
  exact h.symm

/-- `multiplicityRLocal` of a family equals that of its `Finset.attach` reindexing. -/
theorem multiplicityRLocal_attach {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) :
    multiplicityRLocal E s.attach (fun i => V i.1) = multiplicityRLocal E s V := by
  have h := multiplicityRLocal_map s.attach (Function.Embedding.subtype (fun x => x ∈ s)) V
  rw [Finset.attach_map_val] at h
  exact h.symm

/-! ### Small asymptotic facts -/

/-- Eventually `exp(-δ^(-η)/c) ≤ 1/5` as `δ → 0⁺`, for `c, η > 0`. -/
theorem absorb_exp_neg_rpow_le_div_five {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), Real.exp (-δ ^ (-η) / c) ≤ 1 / 5 := by
  filter_upwards [absorb_const_le_rpow_neg
    (mul_pos hc (Real.log_pos (by norm_num : (1 : ℝ) < 5))) hη] with δ hδ
  rw [show (-δ ^ (-η) / c : ℝ) = -(δ ^ (-η) / c) from by ring]
  refine (Real.exp_le_exp.mpr (show -(δ ^ (-η) / c) ≤ -Real.log 5 by
    rw [neg_le_neg_iff, le_div_iff₀ hc]; linarith)).trans ?_
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  norm_num

/-- Eventually `δ ≤ 1/5` as `δ → 0⁺`. -/
theorem eventually_le_one_div_five : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), δ ≤ 1 / 5 := by
  apply Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 5))
  intro δ hδ
  simp only [Set.mem_Ioo] at hδ
  linarith [hδ.2]

/-- `1 ≤ δ ^ (-c)` in `ℝ≥0∞` for `δ ≤ 1` and `0 ≤ c`. -/
theorem one_le_ennreal_rpow_neg {δ : ℝ≥0} (hδ1 : δ ≤ 1) {c : ℝ} (hc : 0 ≤ c) :
    (1 : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-c) := by
  rw [ENNReal.rpow_neg, ENNReal.one_le_inv]
  exact ENNReal.rpow_le_one (by exact_mod_cast hδ1) hc

/-- The dimensional constant of the essentially-distinct reduction is finite, in every dimension
(the `n = 3` case is `Kakeya.refineToEssDistinctLeaves_C_three_ne_top`). -/
theorem refineToEssDistinctLeaves_C_ne_top (n : ℕ) :
    Tube.refineToEssDistinctLeaves.C n ≠ ⊤ := by
  rw [Tube.refineToEssDistinctLeaves.C]
  refine ENNReal.div_ne_top (ENNReal.mul_ne_top ?_ ENNReal.coe_ne_top) ?_
  · rw [Tube.overlapContainment.C]
    exact ENNReal.ofReal_ne_top
  · exact_mod_cast (Tube.le_volume.c_pos n).ne'

/-! ### The cardinality-efficient subfamily, at a chosen exponent, in `ℝ≥0∞` -/

/-- **GWZ Lemma 3.7's random subset, exported at a caller-chosen exponent and in `ℝ≥0∞`.**

For every `c > 0` there is a fullness exponent `η > 0` such that, for all small `δ`, every family of
shaded `δ`-tubes in the unit ball with `λ(s) ≥ δ^η` has a nonempty subfamily `s' ⊆ s` that is

* **cardinality-efficient**: `|s'| · Δmax(s) ≤ 2 · |s|`;
* **Katz–Tao at `δ^{-c}`**: `Δmax(s') ≤ δ^{-c}`;
* **full**: `δ^c ≤ λ(s')`;
* and carries the **multiplicity**: `µ(s) ≤ δ^{-c} · Δmax(s) · µ(s')`.

This is `Kakeya.exists_random_subset` with its hypothesis list discharged for a family of `δ`-tubes
in the unit ball (the discharge of `Kakeya.KatzTaoEstimate.multiplicity_bound`, reproduced), the
`ℝ` clauses converted to `ℝ≥0∞` through `Kakeya.multiplicity_le_rpow_mul_of_multiplicityRLocal_le`,
and the window hypothesis taken on `s` only (the family is reindexed along `Finset.attach`).

Compared with `Kakeya.KatzTaoEstimate.exists_cardEfficient_subfamily`, the Katz–Tao exponent is an
**input** rather than an existential output, the window hypothesis is `∀ i ∈ s` rather than
`∀ i`, and no partial Katz–Tao estimate is assumed (it was not used).  That theorem is the special
case `c := ε`, `ηKT := ε`. -/
theorem exists_cardEfficient_subfamily_at [Nontrivial E] {c : ℝ} (hc : 0 < c) :
    ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) →
      s.Nonempty →
      ∃ s' ⊆ s, s'.Nonempty ∧
        (s'.card : ℝ≥0∞) * maxDensity s (fun i ↦ (T i).toConvexSpaceBody)
          ≤ 2 * (s.card : ℝ≥0∞) ∧
        IsKatzTao s' (fun i ↦ (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-c)) ∧
        (δ : ℝ≥0) ^ c ≤ ShadedBody.fullness s' (fun i ↦ (T i).toShadedBody) ∧
        ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤
          (δ : ℝ≥0∞) ^ (-c) * maxDensity s (fun i ↦ (T i).toConvexSpaceBody) *
            ShadedBody.multiplicity s' (fun i ↦ (T i).toShadedBody) := by
  -- the input fullness exponent `η₁ = c/4 < c/2`
  set η₁ : ℝ := c / 4 with hη₁_def
  have hη₁_pos : 0 < η₁ := by positivity
  have hη₁_lt : η₁ < c / 2 := by rw [hη₁_def]; linarith
  refine ⟨η₁, hη₁_pos, ?_⟩
  set c_low : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hc_low_def
  have hc_low_pos : 0 < c_low := NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  set c_up : ℝ := (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) with hc_up_def
  set K_unif : ℝ := c_up / c_low with hK_unif_def
  have hK_unif_pos : 0 < K_unif :=
    div_pos (NNReal.coe_pos.mpr (Tube.volume_le.C_pos _)) hc_low_pos
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  -- density test family constants, padded so that `Ctest` is absorbed into `δ ^ (-Mtest)`
  set Ctest : ℝ := (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ)
    with hCtest_def
  set Mtest : ℝ := exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) + 1
    with hMtest_def
  have hCtest_pos : 0 < Ctest :=
    NNReal.coe_pos.mpr (exists_volume_bounded_prism_discretization.C_pos _)
  have hMtest_pos : 0 < Mtest := by
    rw [hMtest_def]
    linarith [exists_volume_bounded_prism_discretization.M_pos (Module.finrank ℝ E)]
  filter_upwards [
      (nnreal_eventually_of_real_eventually (p := fun δ => δ < 1)
        (nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one))),
      (nnreal_eventually_of_real_eventually (p := fun δ => 0 < δ)
        (self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ)),
      nnreal_eventually_of_real_eventually
        (absorb_const_le_rpow_neg (C := 4 * K_unif ^ 4) (by positivity) hη₁_pos),
      nnreal_eventually_of_real_eventually
        (absorb_log_le_rpow_neg (C := Ctest) (M := 8 * Mtest + 8) (η := c / 2)
          hCtest_pos (by linarith) (by positivity)),
      nnreal_eventually_of_real_eventually
        (absorb_exp_neg_rpow_le_div_five (c := 8 * K_unif ^ 2) (η := c / 4)
          (by positivity) (by positivity)),
      nnreal_eventually_of_real_eventually eventually_le_one_div_five,
      nnreal_eventually_of_real_eventually (p := fun δ => δ < 1 / Ctest)
        (nhdsWithin_le_nhds (Iio_mem_nhds (one_div_pos.mpr hCtest_pos)))]
    with δNN hδ_lt_one hδ_pos hδ_small_K hδ_small_b hδ5_c hδ5_b hδ_lt_invCtest
  set δ : ℝ := (δNN : ℝ) with hδ_def
  have hδNN_pos : (0 : NNReal) < δNN := by exact_mod_cast hδ_pos
  intro ι s T hB hfull hs
  -- reindex along `Finset.attach` so that the window hypothesis is total
  set e : {i // i ∈ s} ↪ ι := Function.Embedding.subtype (fun x => x ∈ s) with he
  set T' : {i // i ∈ s} → ShadedTube δNN E := fun i => T i.1 with hT'
  set W := fun i ↦ (T i).toConvexSpaceBody with hW
  set V := fun i ↦ (T i).toShadedBody with hV
  set W' := fun i : {i // i ∈ s} ↦ (T' i).toConvexSpaceBody with hW'
  set V' := fun i : {i // i ∈ s} ↦ (T' i).toShadedBody with hV'
  have hB' : ∀ i, (T' i).carrier ⊆ Metric.closedBall 0 1 := fun i => hB i.1 i.2
  have hs' : s.attach.Nonempty := s.attach_nonempty_iff.mpr hs
  have hfull' : ((ShadedBody.fullness s.attach V' : NNReal) : ℝ) ≥ (δ : ℝ) ^ η₁ := by
    have h := fullness_attach' s V
    change ShadedBody.fullness s.attach V' = ShadedBody.fullness s V at h
    rw [h, ge_iff_le, hδ_def, ← NNReal.coe_rpow, NNReal.coe_le_coe]
    exact hfull
  set Δ : ℝ := (maxDensity s W).toReal with hΔ_def
  have hΔ_attach : maxDensity s.attach W' = maxDensity s W := maxDensity_attach s W
  have hT_vol_lb_real : ∀ i,
      c_low * δ ^ (Module.finrank ℝ E - 1) ≤ volume.real (T i).carrier := by
    intro i
    have hreal := ENNReal.toReal_mono (T i).isCompact'.measure_lt_top.ne
      (Tube.le_volume (T i).toTube)
    simpa [MeasureTheory.Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.coe_toReal, hc_low_def, hδ_def] using hreal
  obtain ⟨i₀, hi₀⟩ := hs
  have hvol_pos : 0 < volume (W i₀).carrier :=
    (ENNReal.toReal_pos_iff.mp (lt_of_lt_of_le
      (mul_pos hc_low_pos (pow_pos hδ_pos _)) (hT_vol_lb_real i₀))).1
  have hΔ_one_le : 1 ≤ maxDensity s W := one_le_maxDensity ⟨i₀, hi₀, hvol_pos⟩
  have hΔ_ne_top : maxDensity s W ≠ ⊤ := maxDensity_ne_top s W
  have hΔ_pos : 0 < Δ :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hΔ_one_le).ne' hΔ_ne_top
  have hT_unif : ∀ i ∈ s.attach, ∀ j ∈ s.attach,
      volume.real (T' i).carrier ≤ K_unif * volume.real (T' j).carrier := fun i _ j _ =>
    calc volume.real (T' i).carrier
        ≤ c_up * δ ^ (Module.finrank ℝ E - 1) :=
          by
            have hRHS_fin :
                (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
                    (δNN : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ :=
              ENNReal.mul_ne_top ENNReal.coe_ne_top
                (ENNReal.pow_ne_top ENNReal.coe_ne_top)
            have hreal := ENNReal.toReal_mono hRHS_fin
              (Tube.volume_le (by exact_mod_cast hδ_lt_one.le) (T' i).toTube)
            simpa [MeasureTheory.Measure.real, hc_up_def, hδ_def,
              ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal] using hreal
      _ = K_unif * (c_low * δ ^ (Module.finrank ℝ E - 1)) := by
            rw [hK_unif_def, ← mul_assoc, div_mul_cancel₀ _ hc_low_pos.ne']
      _ ≤ K_unif * volume.real (T' j).carrier :=
            mul_le_mul_of_nonneg_left (hT_vol_lb_real j.1) hK_unif_pos.le
  have htest_real : ∃ KTest : Finset (ConvexSpaceBody E),
      (∀ K ∈ KTest, K ≤ ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))) ∧
      (KTest.card : ℝ) ≤ (δ : ℝ) ^ (-Mtest) ∧ ∀ u : Finset {i // i ∈ s}, u ⊆ s.attach →
      ∃ K ∈ KTest, (maxDensity u (fun i ↦ (T' i).toConvexSpaceBody)).toReal ≤
      Ctest * (densityIn u (fun i ↦ (T' i).toConvexSpaceBody) K).toReal := by
    obtain ⟨KTest, hKT_sub, hKT_card, hKT_test⟩ :=
      exists_localized_finite_test_family_maxDensity.{u, _} (E := E) (r := δNN) (R := 1)
        hδNN_pos (by exact_mod_cast hδ_lt_one.le) le_rfl
    refine ⟨KTest, ?_, ?_, fun u _hu => ?_⟩
    · intro K hK x hx
      exact Metric.self_subset_cthickening _
        (by simpa only [NNReal.coe_one, ConvexSpaceBody.closedUnitBall_carrier]
          using hKT_sub K hK hx)
    · set M : ℝ := exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) with hM_def
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
        hKT_test u (fun i ↦ (T' i).toConvexSpaceBody)
          (fun i _ => by simpa only [NNReal.coe_one] using hB' i)
          (fun i _ => by
            rw [Metric.ethickness.scale_eq]
            exact (T' i).toTube.le_ethickness_finrank_sub_one)
      refine ⟨K, hK_mem, ?_⟩
      have h_ennr := ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (densityIn_ne_top _ _ _)) hK_le
      rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, ← hCtest_def] at h_ennr
  -- the smallness thresholds in the exact shape `exists_random_subset` wants
  have hδ_small_K' : 4 * K_unif ^ 4 ≤ δ ^ (-η₁) := hδ_small_K
  have hδ_small_b' : Ctest * ((8 * Mtest + 8) * Real.log (1 / δ)) ≤ δ ^ (-c) := by
    have h := hδ_small_b
    rwa [show -(2 * (c / 2)) = -c by ring] at h
  have hδ5_c' : Real.exp (-δ ^ (η₁ - c / 2) / (8 * K_unif ^ 2)) ≤ 1 / 5 := by
    have h := hδ5_c
    rwa [show (-(c / 4) : ℝ) = η₁ - c / 2 by rw [hη₁_def]; ring] at h
  obtain ⟨s'', hs''_sub, hs''_ne, hs''_card_ub, hs''_KT, hs''_full, hs''_mu⟩ :=
      exists_random_subset E (η₁ := η₁) (c := c) hη₁_pos hη₁_lt s.attach T' hB' hs' hδ_pos
        K_unif hK_unif_pos hT_unif hδ_small_K'
        Mtest Ctest hMtest_pos hCtest_pos htest_real
        hδ_small_b' hδ5_c' hδ5_b hfull'
  -- map back to `ι`
  refine ⟨s''.map e, ?_, Finset.map_nonempty.mpr hs''_ne, ?_, ?_, ?_, ?_⟩
  · have h := (Finset.map_subset_map (f := e)).mpr hs''_sub
    rwa [he, Finset.attach_map_val] at h
  · -- cardinality efficiency, in `ℝ≥0∞`
    have hcardR : ((s''.map e).card : ℝ) * Δ ≤ 2 * (s.card : ℝ) := by
      rw [Finset.card_map]
      have h1 : (s''.card : ℝ) ≤ 2 * (s.card : ℝ) * Δ⁻¹ := by
        have := hs''_card_ub
        rwa [Finset.card_attach, hΔ_attach] at this
      calc (s''.card : ℝ) * Δ ≤ 2 * (s.card : ℝ) * Δ⁻¹ * Δ :=
            mul_le_mul_of_nonneg_right h1 hΔ_pos.le
        _ = 2 * (s.card : ℝ) := by
            rw [mul_assoc, inv_mul_cancel₀ hΔ_pos.ne', mul_one]
    have h := ENNReal.ofReal_le_ofReal hcardR
    rwa [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, hΔ_def,
      ENNReal.ofReal_toReal hΔ_ne_top, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat] at h
  · -- Katz--Tao at `δ ^ (-c)`
    have h : maxDensity (s''.map e) W = maxDensity s'' W' := maxDensity_map s'' e W
    change maxDensity (s''.map e) W ≤ _
    rw [h, ennreal_coe_nnreal_rpow hδ_pos (-c)]
    exact hs''_KT
  · -- fullness retained
    have h : ShadedBody.fullness (s''.map e) V = ShadedBody.fullness s'' V' :=
      ShadedBody.fullness_map s'' e V
    change (δNN : ℝ≥0) ^ c ≤ ShadedBody.fullness (s''.map e) V
    rw [h, ← NNReal.coe_le_coe, NNReal.coe_rpow]
    calc (δ : ℝ) ^ c
        ≤ (δ : ℝ) ^ (2 * η₁) := Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le
          (by rw [hη₁_def]; linarith)
      _ ≤ _ := hs''_full
  · -- multiplicity transfer, bridged to `ℝ≥0∞`
    have hR : multiplicityRLocal E s V ≤
        (δ : ℝ) ^ (-c) * (maxDensity s W).toReal * multiplicityRLocal E (s''.map e) V := by
      have h1 := multiplicityRLocal_attach s V
      have h2 := multiplicityRLocal_map s'' e V
      change multiplicityRLocal E s.attach V' = multiplicityRLocal E s V at h1
      change multiplicityRLocal E (s''.map e) V = multiplicityRLocal E s'' V' at h2
      rw [← h1, h2, ← hΔ_attach]
      exact hs''_mu
    exact multiplicity_le_rpow_mul_of_multiplicityRLocal_le V hδNN_pos c hΔ_ne_top hR

/-! ### The essential-distinctness reduction at the 6.6(B) level -/

/-- **GWZ Proposition 6.6(B) reduces to its essentially distinct case, at no density hypothesis.**

Fix the loss `ε`, the fullness exponent `η'` at which the essentially distinct case is available,
and a Katz–Tao exponent `c > 0` with `5c ≤ ε` and `3c ≤ η'` (for instance `c = min (ε/5) (η'/3)`).
Then there is `η > 0` such that, for all small `δ` and every family `s` of shaded
`δ`-tubes in the unit ball with `λ(s) ≥ δ^η`: if every **nonempty, pairwise essentially distinct,
Katz–Tao (at `δ^{-c}`) subfamily `u ⊆ s` with `λ(u) ≥ δ^{η'}`** satisfies

  `µ(u) ≤ A · Δmax(u)^{1-β} · |u|^β`,

then `s` itself satisfies

  `µ(s) ≤ δ^{-ε} · A · Δmax(s)^{1-β} · |s|^β`.

`A` is any `ℝ≥0∞` — for 6.6(B) it is `δ^{-ε'} · (a/b)^β`, with `ε'` the essentially distinct
case's own loss — and nothing about `Δmax(s)` is assumed.  The proof is GWZ's Lemma 3.7 device:
`Kakeya.exists_cardEfficient_subfamily_at` extracts `s' ⊆ s` with `|s'| · Δmax(s) ≤ 2|s|`,
`Δmax(s') ≤ δ^{-c}` and `µ(s) ≤ δ^{-c} Δmax(s) µ(s')`;
`Kakeya.exists_pairwise_essDistinct_subfamily_sum_shade_le` selects a pairwise essentially distinct
`u ⊆ s'` keeping the shaded mass up to `1 + C_n δ^{-c} ≤ δ^{-2c}`; the hypothesis bounds `µ(u)`; and
`Kakeya.multiplicity_bound_transfer_of_cardEfficient` combines the `Δmax(s)` of the multiplicity
loss with the `Δmax(s)^{-β}` of the cardinality drop into the `Δmax(s)^{1-β}` of the conclusion.

**This is the discharge of the fine-family essential-distinctness clause of the Part-(B) chain, as
a reduction.**  The remaining conjunct of the 6.6(B) proof is to supply `hsub` from the chain: the
chain's other hypotheses (`Tube.IsUniformAtScale`, the factorisation datum) are not inherited by
subfamilies and must be rebuilt for `u` — see the module docstring. -/
theorem multiplicity_bound_of_essDistinct_subfamily_bounds [Nontrivial E]
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {ε η' c : ℝ} (hc : 0 < c) (hcε : 5 * c ≤ ε)
    (hcη : 3 * c ≤ η') :
    ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E) (A : ℝ≥0∞),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) →
      (∀ u ⊆ s, u.Nonempty →
        (u : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        IsKatzTao u (fun i ↦ (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-c)) →
        (δ : ℝ≥0) ^ η' ≤ ShadedBody.fullness u (fun i ↦ (T i).toShadedBody) →
        ShadedBody.multiplicity u (fun i ↦ (T i).toShadedBody)
          ≤ A * (maxDensity u (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β)
              * (u.card : ℝ≥0∞) ^ β) →
      ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody)
        ≤ (δ : ℝ≥0∞) ^ (-ε) * A
            * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β)
            * (s.card : ℝ≥0∞) ^ β := by
  classical
  have hη' : 0 < η' := by linarith
  obtain ⟨η, hη, hev⟩ := exists_cardEfficient_subfamily_at (E := E) hc
  refine ⟨η, hη, ?_⟩
  set Cn : ℝ≥0∞ := Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) with hCn_def
  have hCn_top : Cn ≠ ⊤ := refineToEssDistinctLeaves_C_ne_top _
  have h1Cn_top : (1 + Cn) ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hCn_top⟩
  have h1Cn_pos : 0 < (1 + Cn).toReal :=
    ENNReal.toReal_pos (by simp) h1Cn_top
  filter_upwards [hev,
      (nnreal_eventually_of_real_eventually (p := fun δ => δ < 1)
        (nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one))),
      (nnreal_eventually_of_real_eventually (p := fun δ => 0 < δ)
        (self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ)),
      nnreal_eventually_of_real_eventually
        (absorb_const_le_rpow_neg (C := (1 + Cn).toReal) h1Cn_pos hc),
      nnreal_eventually_of_real_eventually
        (absorb_const_le_rpow_neg (C := 2) (by norm_num) hc)]
    with δ hδev hδ_lt_one hδ_pos habsC habs2
  intro ι s T A hB hfull hsub
  have hδ0 : (0 : ℝ≥0) < δ := by exact_mod_cast hδ_pos
  have hδ1 : δ ≤ 1 := by exact_mod_cast hδ_lt_one.le
  have hδE0 : (δ : ℝ≥0∞) ≠ 0 := by simpa using hδ0.ne'
  have hδEtop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hδE1 : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1
  -- the `ℝ≥0∞` forms of the two absorptions
  have hpow1 : (1 : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-c) := one_le_ennreal_rpow_neg hδ1 hc.le
  have habsC' : 1 + Cn ≤ (δ : ℝ≥0∞) ^ (-c) := by
    rw [ennreal_coe_nnreal_rpow hδ_pos (-c)]
    exact (ENNReal.le_ofReal_iff_toReal_le h1Cn_top (Real.rpow_nonneg hδ_pos.le _)).mpr habsC
  have habs2' : (2 : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-c) := by
    rw [ennreal_coe_nnreal_rpow hδ_pos (-c)]
    exact (ENNReal.le_ofReal_iff_toReal_le ENNReal.ofNat_ne_top
      (Real.rpow_nonneg hδ_pos.le _)).mpr (by simpa using habs2)
  set W := fun i ↦ (T i).toConvexSpaceBody with hW
  set V := fun i ↦ (T i).toShadedBody with hV
  -- the empty family has multiplicity `0`
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs
    simp
  -- step 1: the cardinality-efficient subfamily
  obtain ⟨s', hs'_sub, hs'_ne, hs'_card, hs'_KT, hs'_full, hs'_mu⟩ := hδev s T hB hfull hs
  -- step 2: the shade-maximising essentially distinct selection inside `s'`
  obtain ⟨u, hu_sub, hu_pair, hu_mass⟩ :=
    exists_pairwise_essDistinct_subfamily_sum_shade_le hδ0 hδ1 s' T hs'_KT
  have hloss : 1 + Cn * (δ : ℝ≥0∞) ^ (-c) ≤ (δ : ℝ≥0∞) ^ (-(2 * c)) := by
    calc 1 + Cn * (δ : ℝ≥0∞) ^ (-c)
        ≤ (δ : ℝ≥0∞) ^ (-c) + Cn * (δ : ℝ≥0∞) ^ (-c) := by gcongr
      _ = (1 + Cn) * (δ : ℝ≥0∞) ^ (-c) := by ring
      _ ≤ (δ : ℝ≥0∞) ^ (-c) * (δ : ℝ≥0∞) ^ (-c) := by gcongr
      _ = (δ : ℝ≥0∞) ^ (-(2 * c)) := by
          rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]; congr 1; ring
  have hmult_s' : ShadedBody.multiplicity s' V ≤ (δ : ℝ≥0∞) ^ (-(2 * c)) *
      ShadedBody.multiplicity u V := by
    refine (ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset s' V u V _ ?_
      hu_mass).trans (mul_le_mul' hloss le_rfl)
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hu_sub hi, hxi⟩
  -- the ambient maximal density is a positive finite number
  have hΔ_ne_top : maxDensity s W ≠ ⊤ := maxDensity_ne_top s W
  have hΔ_ne_zero : maxDensity s W ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ := hs
    have hvol : 0 < volume (W i₀).carrier := by
      refine lt_of_lt_of_le ?_ (Tube.le_volume (T i₀).toTube)
      exact ENNReal.mul_pos (by exact_mod_cast (Tube.le_volume.c_pos _).ne')
        (pow_ne_zero _ hδE0)
    exact (zero_lt_one.trans_le (one_le_maxDensity ⟨i₀, hi₀, hvol⟩)).ne'
  -- if the selection is empty, `s'` carries no shaded mass and everything is `0`
  rcases u.eq_empty_or_nonempty with hu | hu
  · have hzero : ShadedBody.multiplicity s' V = 0 := by
      have hsum : (∑ i ∈ s', volume (T i).shade) = 0 := by
        refine le_antisymm (hu_mass.trans ?_) zero_le
        rw [hu, Finset.sum_empty, mul_zero]
      rw [ShadedBody.multiplicity_eq_div]
      change (∑ i ∈ s', volume (T i).shade) / _ = 0
      rw [hsum, ENNReal.zero_div]
    calc ShadedBody.multiplicity s V
        ≤ (δ : ℝ≥0∞) ^ (-c) * maxDensity s W * ShadedBody.multiplicity s' V := hs'_mu
      _ = 0 := by rw [hzero, mul_zero]
      _ ≤ _ := zero_le
  -- step 3: the essentially distinct case, on `u`
  have hKT_u : IsKatzTao u W ((δ : ℝ≥0∞) ^ (-c)) := hs'_KT.subset hu_sub
  have hfull_u : (δ : ℝ≥0) ^ η' ≤ ShadedBody.fullness u V := by
    have h1 : ShadedBody.fullness' s' V ≤ (δ : ℝ≥0∞) ^ (-(2 * c)) * ShadedBody.fullness' u V :=
      (ShadedBody.fullness'_le_of_subset_of_sum_shade_le s' u V hu_sub hu_mass).trans
        (mul_le_mul' hloss le_rfl)
    have h2 : ((δ ^ c : ℝ≥0) : ℝ≥0∞) ≤ ShadedBody.fullness' s' V := by
      rw [← ShadedBody.coe_fullness]; exact ENNReal.coe_le_coe.mpr hs'_full
    have h3 : (δ : ℝ≥0∞) ^ (3 * c) ≤ ShadedBody.fullness' u V := by
      have hsplit : (δ : ℝ≥0∞) ^ (3 * c) = (δ : ℝ≥0∞) ^ c * (δ : ℝ≥0∞) ^ (2 * c) := by
        rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]; congr 1; ring
      have hcancel : (δ : ℝ≥0∞) ^ (-(2 * c)) * (δ : ℝ≥0∞) ^ (2 * c) = 1 := by
        rw [← ENNReal.rpow_add _ _ hδE0 hδEtop, neg_add_cancel, ENNReal.rpow_zero]
      calc (δ : ℝ≥0∞) ^ (3 * c) = (δ : ℝ≥0∞) ^ c * (δ : ℝ≥0∞) ^ (2 * c) := hsplit
        _ ≤ ShadedBody.fullness' s' V * (δ : ℝ≥0∞) ^ (2 * c) := by
            rw [ENNReal.coe_rpow_of_nonneg _ hc.le] at h2
            gcongr
        _ ≤ (δ : ℝ≥0∞) ^ (-(2 * c)) * ShadedBody.fullness' u V * (δ : ℝ≥0∞) ^ (2 * c) := by
            gcongr
        _ = ShadedBody.fullness' u V := by
            rw [mul_comm ((δ : ℝ≥0∞) ^ (-(2 * c))), mul_assoc, hcancel, mul_one]
    have h4 : (δ : ℝ≥0∞) ^ η' ≤ (δ : ℝ≥0∞) ^ (3 * c) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδE1 hcη
    have h5 : ((δ ^ η' : ℝ≥0) : ℝ≥0∞) ≤ (ShadedBody.fullness u V : ℝ≥0∞) := by
      rw [ShadedBody.coe_fullness, ENNReal.coe_rpow_of_nonneg _ hη'.le]
      exact h4.trans h3
    exact ENNReal.coe_le_coe.mp h5
  have hbound_u := hsub u (hu_sub.trans hs'_sub) hu hu_pair hKT_u hfull_u
  -- step 4: transfer `u → s'`
  have hΔu : maxDensity u W ≤ (δ : ℝ≥0∞) ^ (-c) := hKT_u
  have hcard_u : (u.card : ℝ≥0∞) ≤ (s'.card : ℝ≥0∞) := by
    exact_mod_cast Finset.card_le_card hu_sub
  have hexp : (0 : ℝ) ≤ 1 - β := by linarith
  have hsub' : ShadedBody.multiplicity s' V
      ≤ ((δ : ℝ≥0∞) ^ (-c)) ^ (1 - β) * ((δ : ℝ≥0∞) ^ (-(2 * c)) * A)
          * (s'.card : ℝ≥0∞) ^ β := by
    calc ShadedBody.multiplicity s' V
        ≤ (δ : ℝ≥0∞) ^ (-(2 * c)) * ShadedBody.multiplicity u V := hmult_s'
      _ ≤ (δ : ℝ≥0∞) ^ (-(2 * c)) * (A * (maxDensity u W) ^ (1 - β) * (u.card : ℝ≥0∞) ^ β) := by
          gcongr
      _ ≤ (δ : ℝ≥0∞) ^ (-(2 * c))
            * (A * ((δ : ℝ≥0∞) ^ (-c)) ^ (1 - β) * (s'.card : ℝ≥0∞) ^ β) := by
          gcongr
      _ = ((δ : ℝ≥0∞) ^ (-c)) ^ (1 - β) * ((δ : ℝ≥0∞) ^ (-(2 * c)) * A)
            * (s'.card : ℝ≥0∞) ^ β := by ring
  -- step 5: transfer `s' → s`, with the accounting `Δmax · Δmax^{-β} = Δmax^{1-β}`
  have hmain := multiplicity_bound_transfer_of_cardEfficient hβ0 hΔ_ne_zero hΔ_ne_top
    hs'_mu hs'_card hsub'
  -- step 6: the exponent ledger
  have hA1 : ((δ : ℝ≥0∞) ^ (-c)) ^ (1 - β) ≤ (δ : ℝ≥0∞) ^ (-c) := by
    calc ((δ : ℝ≥0∞) ^ (-c)) ^ (1 - β) ≤ ((δ : ℝ≥0∞) ^ (-c)) ^ (1 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_le hpow1 (by linarith)
      _ = (δ : ℝ≥0∞) ^ (-c) := ENNReal.rpow_one _
  have hA2 : (2 : ℝ≥0∞) ^ β ≤ (δ : ℝ≥0∞) ^ (-c) := by
    calc (2 : ℝ≥0∞) ^ β ≤ (2 : ℝ≥0∞) ^ (1 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
      _ = 2 := ENNReal.rpow_one _
      _ ≤ (δ : ℝ≥0∞) ^ (-c) := habs2'
  have hfive : (δ : ℝ≥0∞) ^ (-c) * (δ : ℝ≥0∞) ^ (-c) * (δ : ℝ≥0∞) ^ (-(2 * c))
      * (δ : ℝ≥0∞) ^ (-c) ≤ (δ : ℝ≥0∞) ^ (-ε) := by
    rw [← ENNReal.rpow_add _ _ hδE0 hδEtop, ← ENNReal.rpow_add _ _ hδE0 hδEtop,
      ← ENNReal.rpow_add _ _ hδE0 hδEtop]
    exact ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
  calc ShadedBody.multiplicity s V
      ≤ (δ : ℝ≥0∞) ^ (-c) * ((δ : ℝ≥0∞) ^ (-c)) ^ (1 - β) * ((δ : ℝ≥0∞) ^ (-(2 * c)) * A)
          * (maxDensity s W) ^ (1 - β) * (2 * (s.card : ℝ≥0∞)) ^ β := hmain
    _ = (δ : ℝ≥0∞) ^ (-c) * ((δ : ℝ≥0∞) ^ (-c)) ^ (1 - β) * (δ : ℝ≥0∞) ^ (-(2 * c))
          * (2 : ℝ≥0∞) ^ β * A * (maxDensity s W) ^ (1 - β) * (s.card : ℝ≥0∞) ^ β := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hβ0]; ring
    _ ≤ (δ : ℝ≥0∞) ^ (-c) * (δ : ℝ≥0∞) ^ (-c) * (δ : ℝ≥0∞) ^ (-(2 * c))
          * (δ : ℝ≥0∞) ^ (-c) * A * (maxDensity s W) ^ (1 - β) * (s.card : ℝ≥0∞) ^ β := by
        gcongr
    _ ≤ (δ : ℝ≥0∞) ^ (-ε) * A * (maxDensity s W) ^ (1 - β) * (s.card : ℝ≥0∞) ^ β := by
        gcongr

/-- The `∃ δ₀` reading of an `∀ᶠ δ in 𝓝[>] 0` statement (a copy of the private helper in
`Kakeya/DimensionThree/Plank/Section6PartBWiring.lean`, kept away from the `Kakeya.Sticky`
import path). -/
theorem exists_threshold_of_eventually_nhdsGT' {p : ℝ≥0 → Prop}
    (h : ∀ᶠ x : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), p x) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ x : ℝ≥0, 0 < x → x ≤ δ₀ → p x := by
  rw [Filter.eventually_iff, mem_nhdsWithin] at h
  obtain ⟨U, hU_open, hU_mem0, hU_sub⟩ := h
  obtain ⟨t, ht_pos, ht_sub⟩ := nhds_bot_basis.mem_iff.mp (hU_open.mem_nhds hU_mem0)
  refine ⟨t / 2, div_pos ht_pos (by norm_num), fun x hx_pos hx_le => ?_⟩
  have hx_lt : x < t := lt_of_le_of_lt hx_le (div_lt_self ht_pos (by norm_num))
  exact hU_sub ⟨ht_sub hx_lt, hx_pos⟩

/-- `Kakeya.multiplicity_bound_of_essDistinct_subfamily_bounds` in the `∃ δ₀` shape of
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`. -/
theorem multiplicity_bound_of_essDistinct_subfamily_bounds_threshold [Nontrivial E]
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {ε η' c : ℝ} (hc : 0 < c) (hcε : 5 * c ≤ ε)
    (hcη : 3 * c ≤ η') :
    ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0), δ₀ ≤ 1 ∧
    ∀ {ι : Type u} (s : Finset ι) {δ : ℝ≥0} (_hδ0 : 0 < δ) (T : ι → ShadedTube δ E) (A : ℝ≥0∞),
      δ ≤ δ₀ →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) →
      (∀ u ⊆ s, u.Nonempty →
        (u : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        IsKatzTao u (fun i ↦ (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-c)) →
        (δ : ℝ≥0) ^ η' ≤ ShadedBody.fullness u (fun i ↦ (T i).toShadedBody) →
        ShadedBody.multiplicity u (fun i ↦ (T i).toShadedBody)
          ≤ A * (maxDensity u (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β)
              * (u.card : ℝ≥0∞) ^ β) →
      ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody)
        ≤ (δ : ℝ≥0∞) ^ (-ε) * A
            * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β)
            * (s.card : ℝ≥0∞) ^ β := by
  obtain ⟨η, hη, hev⟩ :=
    multiplicity_bound_of_essDistinct_subfamily_bounds.{u} (E := E) hβ0 hβ1 hc hcε hcη
  obtain ⟨δ₀, hδ₀, hthr⟩ := exists_threshold_of_eventually_nhdsGT' hev
  refine ⟨η, hη, min δ₀ 1, lt_min hδ₀ one_pos, min_le_right _ _,
    fun {ι} s {δ} hδ0 T A hδ hB hfull hsub => ?_⟩
  exact hthr δ hδ0 (hδ.trans (min_le_left _ _)) s T A hB hfull hsub

/-! ### The project statement of 6.6(B), modulo its essentially distinct case -/

section ProjectStatement

open Classical in
/-- **The essentially distinct case of GWZ Proposition 6.6(B), on subfamilies.**

The hypotheses on `q` are exactly those of `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`
(window, uniformity along the grid, fullness, the plank scale, `Tube.IsUniformAtScale` with the
branching floor, and the `Cw`-parameterised `Kakeya.GlobalPlankFactorization` of the parents); the
conclusion is 6.6(B)'s inequality for every **nonempty, pairwise essentially distinct, Katz–Tao (at
`δ^{-ε}`), full subfamily `u ⊆ q`**, in the same constants.

This is the single conjunct of Proposition 6.6(B) that
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_essDistinctSubfamilyCase` leaves open. It
is what the proved Part-(B) chain (`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData`
and its ancestors, all of which carry pairwise essential distinctness of the fine family) is
*shaped* to supply — but supplying it means running that chain on `u`, whose uniformity and
factorisation datum must be rebuilt from `q`'s (a subfamily inherits neither), and converting
`(PS, Fz)` into the chain's `Kakeya.Section6PartBData` with its `Remark53Prop51` and
outer-representative clauses — the datum obligations recorded in
`Kakeya/DimensionThree/Plank/MasterScaleLemma61.lean`. -/
def Prop66BEssDistinctSubfamilyCase (β ε₂ : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0),
    ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (_hδ0 : 0 < δ)
      (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      δ ≤ δ₀ →
      (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (∃ C : ℝ≥0, C ≤ δ ^ (-η) ∧
        Nonempty (ShadedTube.ShadedUniformTubeSet q T (Tube.ssfGridLen δ) C)) →
      (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
      ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1) (Cw Cpar C₀ : ℝ≥0),
        Cw ≤ δ ^ (-η) → Cpar ≤ δ ^ (-η) → C₀ ≤ δ ^ (-η) →
        (δ : ℝ≥0) ^ (1 - ε₂) ≤ ρ → ρ ≤ a →
        ∀ (PS : Tube.IsUniformAtScale q (fun i ↦ (T i).toTube) ρ Cpar),
        (max 1 Cpar) ^ 2 ≤ PS.branchingN →
        ∀ (_Fz : GlobalPlankFactorization Cw a b hab hb1 PS.parent
          (fun k ↦ (PS.parentTube k).toConvexSpaceBody) C₀),
        ∀ u ⊆ q, u.Nonempty →
          (u : Set ι).Pairwise
            (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
          IsKatzTao u (fun i => (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-ε)) →
          (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness u (fun i => (T i).toShadedBody) →
          ShadedBody.multiplicity u (fun i => (T i).toShadedBody) ≤
            (δ : ENNReal) ^ (-ε)
              * (maxDensity u (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
              * ((a : ENNReal) / (b : ENNReal)) ^ β * (u.card : ENNReal) ^ β

open Classical in
/-- **GWZ Proposition 6.6(B), in the project statement's exact shape, from its essentially distinct
case on subfamilies.**

The conclusion is the **pre-** statement of
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` verbatim — without the fine-family
essential-distinctness binder the live statement now carries — pinned below against
`Kakeya.Prop66BScale.statement_of_universal_prop66B_branchingFloor`, which implies the live form
(`statement_of_universal_prop66B_essDistinct`) trivially; the only hypothesis beyond `0 < β ≤ 1`
is `Kakeya.Prop66BEssDistinctSubfamilyCase`.  So the fine-family
essential-distinctness clause that every proved form of the Part-(B) chain carries costs
Proposition 6.6(B) **nothing**: it is discharged by
`Kakeya.multiplicity_bound_of_essDistinct_subfamily_bounds_threshold` at the price `δ^{-ε/2}`, with
the essentially distinct case invoked at `ε/2`, no density hypothesis, and GWZ Lemma 6.1 and the
chain untouched. -/
theorem tubeMultiplicityOfGlobalPlankFactorisation_of_essDistinctSubfamilyCase {β ε₂ : ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1) (h : Prop66BEssDistinctSubfamilyCase.{u} β ε₂) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0),
      ∀ {ι : Type u} (q : Finset ι) {δ : ℝ≥0} (_hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        δ ≤ δ₀ →
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∃ C : ℝ≥0, C ≤ δ ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet q T
            (Tube.ssfGridLen δ) C)) →
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1) (Cw Cpar C₀ : ℝ≥0),
          Cw ≤ δ ^ (-η) → Cpar ≤ δ ^ (-η) → C₀ ≤ δ ^ (-η) →
          (δ : ℝ≥0) ^ (1 - ε₂) ≤ ρ → ρ ≤ a →
          ∀ (PS : Tube.IsUniformAtScale q (fun i ↦ (T i).toTube) ρ Cpar),
          (max 1 Cpar) ^ 2 ≤ PS.branchingN →
          ∀ (_Fz : GlobalPlankFactorization Cw a b hab hb1 PS.parent
            (fun k ↦ (PS.parentTube k).toConvexSpaceBody) C₀),
          ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
            (δ : ENNReal) ^ (-ε)
              * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
              * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β := by
  intro ε hε
  -- the essentially distinct case, at `ε / 2`
  obtain ⟨η', hη', δ₀', hδ₀', hED⟩ := h (ε / 2) (by positivity)
  -- the reduction, at loss `ε / 2`, fullness exponent `η'`, Katz–Tao exponent `c`
  set c : ℝ := min (ε / 10) (η' / 3) with hc_def
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hcε : 5 * c ≤ ε / 2 := by
    have := min_le_left (ε / 10) (η' / 3); rw [← hc_def] at this; linarith
  have hcη : 3 * c ≤ η' := by
    have := min_le_right (ε / 10) (η' / 3); rw [← hc_def] at this; linarith
  obtain ⟨η, hη, δ₀'', hδ₀'', hδ₀''1, hred⟩ :=
    multiplicity_bound_of_essDistinct_subfamily_bounds_threshold.{u}
      (E := EuclideanSpace ℝ (Fin 3)) hβpos.le hβle hc hcε hcη
  refine ⟨min η η', lt_min hη hη', min δ₀' δ₀'', lt_min hδ₀' hδ₀'', ?_⟩
  intro ι q δ hδ0 T hδ hB huni hfull ρ a b hab hb1 Cw Cpar C₀ hCw hCpar hC₀ hρ hρa PS hbr Fz
  have hδ' : δ ≤ δ₀' := hδ.trans (min_le_left _ _)
  have hδ'' : δ ≤ δ₀'' := hδ.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδ''.trans hδ₀''1
  have hδE0 : (δ : ℝ≥0∞) ≠ 0 := by simpa using hδ0.ne'
  have hδEtop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hδE1 : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1
  -- the shared exponent `min η η'` serves both the reduction and the essentially distinct case
  have hmin_η : (δ : ℝ≥0) ^ η ≤ (δ : ℝ≥0) ^ (min η η') :=
    NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (min_le_left _ _)
  have hmin_η' : (δ : ℝ≥0) ^ η' ≤ (δ : ℝ≥0) ^ (min η η') :=
    NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (min_le_right _ _)
  have hneg : (δ : ℝ≥0) ^ (-(min η η')) ≤ (δ : ℝ≥0) ^ (-η') :=
    NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (neg_le_neg (min_le_right _ _))
  obtain ⟨C, hC, hCne⟩ := huni
  have hhalf : (δ : ℝ≥0∞) ^ (-(ε / 2)) * (δ : ℝ≥0∞) ^ (-(ε / 2)) = (δ : ℝ≥0∞) ^ (-ε) := by
    rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]; congr 1; ring
  calc ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
      ≤ (δ : ℝ≥0∞) ^ (-(ε / 2)) * ((δ : ℝ≥0∞) ^ (-(ε / 2)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β)
          * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
          * (q.card : ℝ≥0∞) ^ β := by
        refine hred q hδ0 T _ hδ'' hB (hmin_η.trans hfull) ?_
        intro u hu hune hpair hKT hfullu
        have hKT' : IsKatzTao u (fun i => (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-(ε / 2))) :=
          hKT.mono (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith))
        have hfullu' : (δ : ℝ≥0) ^ η' ≤ ShadedBody.fullness u (fun i => (T i).toShadedBody) :=
          hfullu
        have hbound := hED q hδ0 T hδ' hB ⟨C, hC.trans hneg, hCne⟩ (hmin_η'.trans hfull)
          ρ a b hab hb1 Cw Cpar C₀ (hCw.trans hneg) (hCpar.trans hneg) (hC₀.trans hneg)
          hρ hρa PS hbr Fz u hu hune hpair hKT' hfullu'
        calc ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
            ≤ (δ : ENNReal) ^ (-(ε / 2))
                * (maxDensity u (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
                * ((a : ENNReal) / (b : ENNReal)) ^ β * (u.card : ENNReal) ^ β := hbound
          _ = (δ : ℝ≥0∞) ^ (-(ε / 2)) * ((a : ℝ≥0∞) / (b : ℝ≥0∞)) ^ β
                * (maxDensity u (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
                * (u.card : ℝ≥0∞) ^ β := by ring
    _ = (δ : ENNReal) ^ (-ε)
          * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
          * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β := by
        rw [← hhalf]; ring

open Classical in
/-- **compatibility.**  The conclusion of
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_essDistinctSubfamilyCase` is the pinned
**pre-** project statement of Proposition 6.6(B),
`Kakeya.Prop66BScale.statement_of_universal_prop66B_branchingFloor`; the live theorem's own pin is
`statement_of_universal_prop66B_essDistinct` in
`Kakeya/DimensionThree/Plank/Prop66BCoarseScale.lean`.  If the shape of that pinned form changes,
this breaks. -/
example {β ε₂ : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (h : Prop66BEssDistinctSubfamilyCase.{u} β ε₂) :
    Prop66BScale.statement_of_universal_prop66B_branchingFloor.{u} β ε₂ :=
  tubeMultiplicityOfGlobalPlankFactorisation_of_essDistinctSubfamilyCase hβpos hβle h

end ProjectStatement

end Kakeya

end

end
