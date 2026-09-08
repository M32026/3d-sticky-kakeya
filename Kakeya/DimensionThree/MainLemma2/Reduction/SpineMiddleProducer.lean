/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreWiring
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCanonicalCoverAt

/-!
# the estimate: the middle-factor producer, and the exponent it can reach

`Kakeya.ML2Core.geometricCoreAt_of_middleFactor` reduces GWZ Main Lemma 2's geometric core to a
single hypothesis, the **middle factor** at the two-scale split of a Katz--Tao dividing window,
asked at the gain `2 ε + 14 ε₁/25` for **every** Katz--Tao exponent `ε₁ > 0`.

This file measures that demand against what the existing chain delivers, and the measurement is
negative on both sides:

* **a ceiling on the demand itself** — any witness of the middle factor's own conclusion, at any
  input satisfying the wiring's binders, forces `gm ≤ 4 β`
  (`Kakeya.ML2Core.middle_gain_le_of_split`).  So the demand `2 ε + 14 ε₁/25` is met by nothing at
  all once `ε₁ > 25 (4 β - 2 ε)/14`;
* **a ceiling on the supply** — the transported exponent of the estimate
  (`Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover`, read at the ambient
  scale through `Kakeya.ML2Core.middle_factor_of_rescaled`) is at most `e³ β/24`, while the demand
  is at least `14 e` (`Kakeya.ML2Core.spine_middle_gain_lt_demand`).

The positive content is the composition itself: `Kakeya.ML2Core.middle_factor_of_edNodes_window`
produces the middle factor at the ambient scale from the **ED-node clause** alone among the
open inputs, at the exponent the chain actually reaches.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-! ## A multiplicity that is not zero is at least one -/

section OneLe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **A nonzero multiplicity is at least `1`.**

`ShadedBody.multiplicity` is `(∑ |Y_i|)/|⋃ Y_i|`, and the numerator dominates the denominator, so
the only value below `1` it can take is `0` — which happens exactly when every shade is null.  This
is `ShadedBody.one_le_multiplicity` with its hypothesis moved to the value side, where every
consumer in this file finds it. -/
theorem one_le_multiplicity_of_ne_zero (s : Finset ι) (V : ι → ShadedBody E)
    (h : ShadedBody.multiplicity s V ≠ 0) : 1 ≤ ShadedBody.multiplicity s V := by
  refine ShadedBody.one_le_multiplicity s V ?_
  intro hall
  exact h (by
    rw [ShadedBody.multiplicity_eq_div, Finset.sum_eq_zero hall, ENNReal.zero_div])

/-- **Positive shade mass forces a positive multiplicity.** -/
theorem multiplicity_ne_zero_of_mass_pos (s : Finset ι) (V : ι → ShadedBody E)
    (h : 0 < ∑ i ∈ s, volume (V i).shade) : ShadedBody.multiplicity s V ≠ 0 := by
  rw [ShadedBody.multiplicity_eq_div]
  exact (ENNReal.div_pos h.ne' (ShadedBody.volume_iUnion_shade_ne_top s V)).ne'

end OneLe

/-! ## The ceiling on the demand -/

section Ceiling

/-- **The arithmetic of the ceiling.**

A multiplicity that is at least `1` and at most `δ^{gm} n^β`, on a family of at most `δ^{-4}`
members, forces `gm ≤ 4 β`.  Nothing about tubes enters; this is the shape
`Kakeya.ML2Assembly.GeometricCoreAt` puts on the middle factor read against the wiring's own
cardinality binder `|u| ≤ δ^{-4}`. -/
theorem exponent_le_of_multiplicity_ge_one {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {β gm : ℝ} (hβ0 : 0 ≤ β) {mu : ENNReal} {n : ℕ}
    (hone : (1 : ENNReal) ≤ mu)
    (hbd : mu ≤ (δ : ENNReal) ^ gm * ((n : ℕ) : ENNReal) ^ β)
    (hn : ((n : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-(4 : ℝ))) :
    gm ≤ 4 * β := by
  have hδE0 : (δ : ENNReal) ≠ 0 := by
    simpa using hδ0.ne'
  have hδEtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδE1 : (δ : ENNReal) < 1 := by exact_mod_cast hδ1
  have hstep : (1 : ENNReal) ≤ (δ : ENNReal) ^ (gm - 4 * β) := by
    refine hone.trans (hbd.trans ?_)
    calc (δ : ENNReal) ^ gm * ((n : ℕ) : ENNReal) ^ β
        ≤ (δ : ENNReal) ^ gm * ((δ : ENNReal) ^ (-(4 : ℝ))) ^ β := by
          gcongr
      _ = (δ : ENNReal) ^ gm * (δ : ENNReal) ^ (-(4 : ℝ) * β) := by
          rw [← ENNReal.rpow_mul]
      _ = (δ : ENNReal) ^ (gm + -(4 : ℝ) * β) := by
          rw [ENNReal.rpow_add _ _ hδE0 hδEtop]
      _ = (δ : ENNReal) ^ (gm - 4 * β) := by ring_nf
  by_contra hcon
  rw [not_le] at hcon
  exact absurd hstep (not_le.mpr (ENNReal.rpow_lt_one hδE1 (by linarith)))

/-- **The ceiling, at the split's own clauses.**

`Kakeya.ML2Core.exists_twoScaleSplit_at_window`'s product clause and the wiring's mass-positivity
binder force the coarse fibre's multiplicity to be **at least `1`**: the left-hand side of the
product clause is a multiplicity of a family with positive shade mass, hence nonzero, so no factor
on the right can vanish, and a nonzero multiplicity is `≥ 1`.

Together with the cardinality ceiling `|fibre| ≤ δ^{-4}` — which the wiring supplies through
`Kakeya.ML2Core.card_activeNodes_le_card` and its binder `|u| ≤ δ^{-4}` — the middle factor's own
bound then forces **`gm ≤ 4 β`**.

**This is a ceiling on the demand, not on any proof strategy.**  Whatever produces the middle
factor, at whatever objects, the exponent it can be asked for is at most `4 β`. -/
theorem middle_gain_le_of_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {δ τ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1) {β gm : ℝ} (hβ0 : 0 ≤ β)
    {ι : Type*} {s₁ fib : Finset ι} {T : ι → ShadedTube δ E} {Yτ' : ι → ShadedTube τ E}
    {Loss A C : ENNReal}
    (hmass : 0 < ∑ i ∈ s₁, volume (T i).shade)
    (hprod : ShadedBody.multiplicity s₁ (fun i ↦ (T i).toShadedBody)
      ≤ Loss * A * ShadedBody.multiplicity fib (fun j ↦ (Yτ' j).toShadedBody) * C)
    (hbd : ShadedBody.multiplicity fib (fun j ↦ (Yτ' j).toShadedBody)
      ≤ (δ : ENNReal) ^ gm * ((fib.card : ℕ) : ENNReal) ^ β)
    (hcard : ((fib.card : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-(4 : ℝ))) :
    gm ≤ 4 * β := by
  have hleft : ShadedBody.multiplicity s₁ (fun i ↦ (T i).toShadedBody) ≠ 0 :=
    multiplicity_ne_zero_of_mass_pos s₁ (fun i ↦ (T i).toShadedBody) hmass
  have hmidne : ShadedBody.multiplicity fib (fun j ↦ (Yτ' j).toShadedBody) ≠ 0 := by
    intro h0
    rw [h0] at hprod
    simp only [mul_zero, zero_mul] at hprod
    exact hleft (le_antisymm hprod bot_le)
  exact exponent_le_of_multiplicity_ge_one hδ0 hδ1 hβ0
    (one_le_multiplicity_of_ne_zero fib (fun j ↦ (Yτ' j).toShadedBody) hmidne) hbd hcard

/-- **The coarse fibre of a retained node set is no bigger than the leaf set.**

`Kakeya.ML2Core.card_activeNodes_le_card` bounds the level-`b` node count by the leaf count, and
the coarse fibre is a subset of the retained node set, which is a subset of the active nodes. -/
theorem card_coarseFibre_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {δ : NNReal} {ι : Type*} {u : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}
    (𝒞 : Tube.ChainCoverSystem u T N σ) {a b : ℕ} {tτ' : Finset ι}
    (htτ : tτ' ⊆ ML2Reduction.activeNodes 𝒞 b) (jθ : ι) :
    (open scoped Classical in
      ({j ∈ tτ' | ML2Reduction.coarseNode 𝒞 a b j = jθ} : Finset ι)).card ≤ u.card := by
  classical
  exact le_trans (Finset.card_le_card
    ((Finset.filter_subset _ _).trans htτ)) (card_activeNodes_le_card 𝒞 b)

/-- **The ceiling, at the wiring's own binders.**

Every binder below is a piece of `Kakeya.ML2Core.geometricCoreAt_of_middleFactor`'s hypothesis
block, read at one scale `δ < 1`:

* `htτ` and `𝒞` — the retained node set sits in the level-`b` active nodes of the window's chain;
* `hcardu` — the wiring's cardinality binder `|u| ≤ δ^{-4}`;
* `hmass` — the wiring's mass-positivity binder;
* `hprod` — the seventh clause of the two-scale split, which
  `Kakeya.ML2Core.exists_twoScaleSplit_at_window` returns;
* `hbd` — the middle factor itself, at the gain `gm`.

**Conclusion: `gm ≤ 4 β`.**  So the gain the middle factor may be asked for is capped by the
cardinality binder alone, at every window, at every scale, with no geometry entering. -/
theorem middle_gain_le_of_window_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {δ τ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1) {β gm : ℝ} (hβ0 : 0 ≤ β)
    {ι : Type*} {u s₁ tτ' : Finset ι} {T : ι → ShadedTube δ E}
    {N : ℕ} {σ : ℕ → NNReal} (𝒞 : Tube.ChainCoverSystem u (fun i ↦ (T i).toTube) N σ)
    {a b : ℕ} {jθ : ι} {Yτ' : ι → ShadedTube τ E} {Loss A C : ENNReal}
    (htτ : tτ' ⊆ ML2Reduction.activeNodes 𝒞 b)
    (hcardu : (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)))
    (hmass : 0 < ∑ i ∈ s₁, volume (T i).shade)
    (hprod : ShadedBody.multiplicity s₁ (fun i ↦ (T i).toShadedBody)
      ≤ Loss * A * ShadedBody.multiplicity
          (open scoped Classical in
            ({j ∈ tτ' | ML2Reduction.coarseNode 𝒞 a b j = jθ} : Finset ι))
          (fun j ↦ (Yτ' j).toShadedBody) * C)
    (hbd : ShadedBody.multiplicity
        (open scoped Classical in
          ({j ∈ tτ' | ML2Reduction.coarseNode 𝒞 a b j = jθ} : Finset ι))
        (fun j ↦ (Yτ' j).toShadedBody)
      ≤ (δ : ENNReal) ^ gm
        * ((((open scoped Classical in
            ({j ∈ tτ' | ML2Reduction.coarseNode 𝒞 a b j = jθ} : Finset ι))).card : ℕ) :
              ENNReal) ^ β) :
    gm ≤ 4 * β := by
  classical
  have hfib := card_coarseFibre_le 𝒞 (a := a) htτ jθ
  have hcast : ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒞 a b j = jθ} : Finset ι)).card : ENNReal)
      ≤ (δ : ENNReal) ^ (-(4 : ℝ)) := by
    have h1 : ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒞 a b j = jθ} : Finset ι)).card : ENNReal)
        ≤ ((u.card : ℕ) : ENNReal) := by exact_mod_cast hfib
    have h2 : ((u.card : ℕ) : ENNReal) ≤ (((δ ^ (-(4 : ℝ)) : NNReal)) : ENNReal) := by
      exact_mod_cast hcardu
    have h3 : (((δ ^ (-(4 : ℝ)) : NNReal)) : ENNReal) = (δ : ENNReal) ^ (-(4 : ℝ)) :=
      ENNReal.coe_rpow_of_ne_zero hδ0.ne' _
    rw [h3] at h2
    exact h1.trans h2
  exact middle_gain_le_of_split hδ0 hδ1 hβ0 hmass hprod hbd hcast

end Ceiling

/-! ## The ceiling on the supply -/

section Supply

/-- **What the existing chain can put at the ambient scale, against what the wiring asks for.**

the estimate (`Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover`) proves the
middle factor at the **rescaled** thickness `δ̃` with exponent `10 η_k/ε₂`, and
`Kakeya.ML2Core.middle_factor_of_rescaled` transports it to the ambient scale at exponent
`w · (10 η_k/ε₂)`, where `w` is any exponent with `δ̃ ≤ δ^{w}`.  The only such `w` a Katz--Tao
dividing window supplies is its own separation exponent
(`Kakeya.ML2Reduction.IsKatzTaoDividingWindow.scale_sep`), which on the spine is `e`.

`Kakeya.ML2Core.geometricCoreAt_of_middleFactor` asks for the gain `2 ε + 14 ε₁/25`.

**The two do not meet, and the gap is not a constant.**  For `k < N` the rung is a *step* below the
top one, so `η_k ≤ e² β η_{k+1}/48 ≤ e³ β/48`, whence the supply is at most `e³ β/24`; while
`ε₂ ≤ ε₁/5` and `e ≤ ε₂/5` make the demand at least `14 e`.  The ratio is `e² β/336`, and
`e < 1/60` on every spine. -/
theorem spine_middle_gain_lt_demand {β ϖ ε₁ ε₂ e ε : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (hsp : ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hε : 0 < ε) {k : ℕ}
    (hstep : η k ≤ e ^ 2 * β * η (k + 1) / 48) :
    e * (10 * η k / ε₂) < 2 * ε + 14 * (ε₁ / 25) := by
  have he : 0 < e := hsp.div_pos
  have hε₂ : 0 < ε₂ := hsp.eps₂_pos
  have he5 : 5 * e ≤ ε₂ := by have := hsp.div_le; linarith
  have hε12 : ε₂ < 1 / 12 := hsp.eps₂_lt_twelfth
  have he60 : e < 1 / 60 := by linarith
  have hη1 : η (k + 1) ≤ e := hsp.rung_le_div (k + 1)
  have hηk0 : 0 < η k := hsp.rung_pos k
  have hmul : e ^ 2 * β * η (k + 1) ≤ e ^ 2 * β * e :=
    mul_le_mul_of_nonneg_left hη1 (by positivity)
  have hcube : e ^ 2 * β * e = e ^ 3 * β := by ring
  have hηk : η k ≤ e ^ 3 * β / 48 := by
    rw [hcube] at hmul; linarith [hstep, hmul]
  have hε₁ : 25 * e ≤ ε₁ := by have := hsp.eps₂_le_everyScale; linarith
  -- the supply
  have hsupply : e * (10 * η k / ε₂) ≤ e ^ 3 * β / 24 := by
    have hd : 10 * η k / ε₂ ≤ 10 * η k / (5 * e) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) he5
    have : e * (10 * η k / (5 * e)) = 2 * η k := by field_simp; ring
    calc e * (10 * η k / ε₂) ≤ e * (10 * η k / (5 * e)) := by
          exact mul_le_mul_of_nonneg_left hd he.le
      _ = 2 * η k := this
      _ ≤ e ^ 3 * β / 24 := by linarith [hηk]
  -- the demand
  have hdemand : 14 * e ≤ 14 * (ε₁ / 25) := by linarith
  have hsq : e ^ 3 < e / 3600 := by nlinarith [he, he60, mul_pos he he]
  have hβcube : e ^ 3 * β ≤ e ^ 3 := by nlinarith [pow_pos he 3, hβ1]
  have hgap : e ^ 3 * β / 24 < 14 * e := by linarith
  linarith

/-- **The same, on the constructed spine.**

`Kakeya.ML2Spine.spineStep`'s first entry is `e² β x/1024`, so
`Kakeya.ML2Spine.spineRung_eq_step` supplies the hypothesis of
`Kakeya.ML2Core.spine_middle_gain_lt_demand` at every `k` below the step count -- which is exactly
the range `Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover` is stated on
(`hk : k < spineCount ϖ ε₁`).

**So the middle factor `Kakeya.ML2Core.geometricCoreAt_of_middleFactor` asks for is out of reach of
the existing non-eccentric branch at every window step, at every `ε`, at every `ε₁`.** -/
theorem spineRung_middle_gain_lt_demand {β ϖ ε₁ ε : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hε : 0 < ε) {k : ℕ} (hk : k < ML2Spine.spineCount ϖ ε₁) :
    ML2Spine.spineDiv ϖ ε₁
        * (10 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁)
      < 2 * ε + 14 * (ε₁ / 25) := by
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  have hst := ML2Spine.spineRung_eq_step (β := β) (ϖ := ϖ) (ε₁ := ε₁)
    (gain := gain) (dens := dens) hk
  have hstep : ML2Spine.spineRung β ϖ ε₁ gain dens k
      ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2 * β * ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 48 := by
    rw [hst]
    exact ML2Spine.spineStep_le_div_48 hβ0 (hsp.rung_pos (k + 1)).le
  exact spine_middle_gain_lt_demand hsp hβ0 hβ1 hε hstep

end Supply

/-! ## The ED-node clause, into step-10 binder -/

section EdNodes

/-- **The ED-node clause produces `hcanon` binder, character for character.**

`Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover` consumes step 10 through
one binder, `hcanon`: an essentially distinct all-used cover of the rescaled family at every scale
of Lemma 9.1's window, with the loss-weighted count.  The **ED-node clause** — GWZ Definition
2.1(ii) read on the *outer* hierarchy's nodes at the scales the count is taken — enters it at
`m = 0` through `Kakeya.ML2Core.hstep8_of_essDistinct` and
`Kakeya.ML2Reduction.canonicalCover_of_step8`: the extraction spends **nothing** of the reading gap,
so the budget clause is the bare `⌈C₃⌉ · spineOuterCountLoss R ≤ ρ^{-(ζ'-ζ)}`, a threshold on `ρ`
whenever `ζ < ζ'` (`Kakeya.ML2Reduction.exists_threshold_hup_budget`).

This is the same plug `Kakeya.ML2Core.fine_factor_of_lemma91At_of_edCover` makes one level down,
stated at the interface the estimate actually reads. -/
theorem canonicalCover_of_edNodes {ϖ ζ ζ' : ℝ} {b δt δ' : NNReal} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hδ'0 : 0 < δ')
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s' : Finset α} (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (hED : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (Z' i).carrier ⊆ (W k).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ))) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      ∃ (κ₁ : Type u) (t : Finset κ₁) (W : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₁).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ j ∈ t, ∃ i ∈ s',
          (ML2Reduction.spineFamily
              (ML2Reduction.spineRescaleUnit hsit.pos_ambient T₀ hR) Z' i).toConvexSpaceBody
            ≤ (W j).toConvexSpaceBody) ∧
        (ML2Reduction.spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (t.card : ℝ) :=
  ML2Reduction.canonicalCover_of_step8 (m := 0) (ζ' := ζ') hsit hR T₀ Z' hδ'0 hwin4
    (fun ρ hρ ↦ by
      obtain ⟨κ₀, t, W, hEDt, hsubW, hused, hcard⟩ := hED ρ hρ
      exact hstep8_of_essDistinct (T₀ := T₀) (𝕋 := Z') (s' := s') t W hEDt hsubW hused hcard)
    (fun ρ hρ ↦ by simpa using hbudget ρ hρ)

end EdNodes

/-! ## the component estimates (non-eccentric), composed, with the ED-node clause as the only open input -/

section Composition

open Classical in
/-- **The middle factor at the ambient scale, from the ED-node clause.**

This is the component estimates : `Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover`
at the rescaled thickness `δ̃`, with its step-10 binder discharged by the **ED-node clause**
(`Kakeya.ML2Core.canonicalCover_of_edNodes`), transported to the ambient scale by
`Kakeya.ML2Core.middle_factor_of_rescaled`.

Read as an obligation list, every binder below is either a existing producer's output or a datum the
window hands over, **except** `hED`, which is GWZ Definition 2.1(ii) on the nodes at the scales the
count is read.  That is the one clause this composition carries.

**The exponent it reaches is `w · (10 η_k/ε₂)`,** where `w` is the window's own scale-separation
exponent (`Kakeya.ML2Reduction.IsKatzTaoDividingWindow.scale_sep`, which is `e` on the spine).
`Kakeya.ML2Core.spineRung_middle_gain_lt_demand` measures that against what
`Kakeya.ML2Core.geometricCoreAt_of_middleFactor` asks for, and they do not meet. -/
theorem middle_factor_of_edNodes
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    -- the ambient window and the transport 
    {δ θ τ δt : NNReal} {Rout : ℝ} {w : ℝ}
    (hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3) (hRout : 0 < Rout)
    (hτθ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (δt : ℝ))
    (Tθ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {fib : Finset α}
    (Y : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsubOut : ∀ j ∈ fib, (Y j).carrier ⊆ Tθ.carrier)
    (hw : 0 ≤ w) (hsep : δt ≤ δ ^ w)
    -- the rescaled world 
    {b δ' : NNReal} {R : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1) (hδ'0 : 0 < δ') (hb1 : b ≤ 1) (hδtb : δt ≤ b)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))} {ηc : ℝ}
    (hcoarse : ∀ (dt : NNReal), dt ≠ 0 → dt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} (t : Finset ι) (T : ι → ShadedTube b (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ closedBall 0 1) →
        (ShadedBody.fullness t (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc →
        Kakeya.maxDensity t (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (dt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β))) →
        ShadedBody.multiplicity t (fun i ↦ (T i).toShadedBody)
          ≤ (dt : ENNReal) ^ (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β)))) * (t.card : ENNReal) ^ β)
    (hballb : ∀ j, (Zρ j).carrier ⊆ closedBall 0 1)
    (hfullb : (ShadedBody.fullness t' (fun j ↦ (Zρ j).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc)
    (hDb : Kakeya.maxDensity t' (fun j ↦ (Zρ j).toConvexSpaceBody)
      ≤ (δt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (ML2Spine.spineDiv ϖ ε₁ * β))))
    {s' : Finset α} (hs' : s' ⊆ fib)
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (hsubfib : ∀ i ∈ fib,
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier ⊆ T₀.carrier)
    {cst ζ ζ' ηd : ℝ}
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc fib s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ mm ϖ ζ s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hL91 : ML2Reduction.Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) + 3 * qc) ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (hmax : Kakeya.maxDensity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    -- AA/AB: tightened to the constant the producer actually returns
    -- (`ShadedTube.ssfUniformConst 3`, `Kakeya/ShadedUniform.lean:895`), with the threshold the
    -- loose bracket used to quantify away carried explicitly.  Discharged at wiring time by
    -- `exists_outerShadedUniformTubeSet_ssf` + `exists_threshold_coe_const_le_rpow_neg`.
    -- this binder is ALSO where the line-ED levels row is sourced.  The witness carries
    -- a uniform hierarchy, and `Kakeya.VeryNotSticky.lineEDLevelsAt_C3_of_huni` turns it (with
    -- `hcb`'s `centred`/`contained`/`small` rows and the uniformiser's own grid threshold) into
    -- `LineEDLevelsAt C₃ lineEDLevelsConstant _` at the NAMED constant (
    -- ): the datum is DERIVED here, never an ambient field.
    (huni : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3)))
    -- the ONE open input
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    -- stated on the CONTRACTED-bottom window `[δ'^{1-ϖ}/C, δ'^{ϖ}]`, because the
    -- centring hand-back reads the cover at `ρ/C`.  A producer of
    -- this clause must supply it on the wide window, not merely on Lemma 9.1's.
    (hED : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j l ↦ _root_.IsEssentiallyDistinct (W j).carrier (W l).carrier) ∧
        (∀ l ∈ t, (W l).carrier ⊆ T₀.carrier) ∧
        (∀ l ∈ t, ∃ i ∈ s',
          (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier
            ⊆ (W l).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    -- this is `hbudget` with `centringCountLossConstant R ·` at the head of the left-hand
    -- side, so it IMPLIES `hbudget`; `hbudget` is retained only because keeps its text
    -- tree-wide.  Discharged by `exists_threshold_hup_budget`'s argument at the
    -- new constant, never assumed; `ζ < ζ'` (`hgap`) is its side condition.
    (hcntbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hgap : ζ ≤ ζ')
    -- step 9, the cardinality multiplicativity and the loss ledger
    {Cf L Cu : ENNReal} {Nm : ℕ} {κ : ℝ}
    (hCf1 : (1 : ENNReal) ≤ Cf)
    (hsplit : ShadedBody.multiplicity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)
      ≤ L * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦
            (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)))
    (hcard : (t'.card : ENNReal) * (fib.card : ENNReal) ≤ Cu * (Nm : ENNReal))
    (hLoss : L * Cf * Cu ^ β ≤ (δt : ENNReal) ^ (-κ))
    (hκ : κ ≤ 20 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ENNReal) ^ (w * (10 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / ML2Spine.spineEps₂ ϖ ε₁)) * (Nm : ENNReal) ^ β := by
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  have hgm : 0 ≤ 10 * ML2Spine.spineRung β ϖ ε₁ gain dens k / ML2Spine.spineEps₂ ϖ ε₁ := by
    have h1 := hsp.rung_pos k
    have h2 := hsp.eps₂_pos
    positivity
  refine middle_factor_of_rescaled hsitOut hRout hτθ Tθ Y hsubOut hgm hw hsep ?_
  exact ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover hβ0 hβ1 hϖ hε₁ hgain
    hdens hk hδ0 hδ1 hδ'0 hb1 hδtb hbw hprod hcoarse hballb hfullb hDb hs' hsit hR hR1 hτσ T₀ mm
    hsubfib hqc0 h3qc hcb hL91 hζ hloss hmax hfull
    (Kakeya.VeryNotSticky.huni_loose_of_tight huni)
    (fun ρ hρ ↦ hct ρ hρ
      (by
        -- the cover is read at the CONTRACTED radius; `hED` moved, `hbudget` did NOT —
        -- `Kakeya.ML2Reduction.budget_descends` carries it from `ρ` down to `ρ/C` 
        have hmem := Kakeya.VeryNotSticky.mem_widened_window_of_mem hρ
        have hc0 : 0 < ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant :=
          lt_of_lt_of_le (div_pos (NNReal.rpow_pos hδ'0)
            Kakeya.VeryNotSticky.edWindowContractionConstant_pos) hmem.1
        obtain ⟨κ₀, t, W, hEDt, hsubW, hused, hcard⟩ := hED _ hmem
        obtain ⟨κ₁, t₈, W', M, hsubW', hused', hM', hMρ', hcard'⟩ :=
          hstep8_of_essDistinct t W hEDt hsubW hused hcard
        exact ML2Reduction.canonicalCoverAt_of_step8_const (m := 0) (ζ' := ζ')
          (Kc := (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ))
          hsit hR T₀ _ hc0
          (le_trans (by exact_mod_cast hmem.2) hwin4) t₈ W' hsubW' hused' hM' hMρ' hcard'
          (ML2Reduction.budget_descends
            (h := ML2Reduction.hbud_of_hcntbudget (NNReal.coe_nonneg _)
              (by simpa using hcntbudget ρ hρ))
            (hρ'0 := by exact_mod_cast hc0)
            (hle := by exact_mod_cast Kakeya.VeryNotSticky.div_centringCoverRadiusConstant_le ρ)
            (he := by linarith))))
    hCf1 hsplit hcard hLoss hκ

end Composition

/-! ## The singleton refutation: the existing `hmid` is FALSE, not merely capped -/

section Singleton

/-- **A one-node retained set kills the middle factor at every positive gain.**

`Kakeya.ML2Core.exponent_le_of_multiplicity_ge_one` read at `n = 1`: a multiplicity that is at
least `1` and at most `δ^{gm} · 1^β` forces `gm ≤ 0`.

**This is the whole refutation of the existing `hmid`.**  Its binder block quantifies over an
*arbitrary* retained node set `t₁`, and its conclusion's `∃ tτ' ⊆ t₁` with `tτ'.Nonempty` cannot
escape a **singleton** `t₁`: then `tτ' = t₁`, every coarse fibre has at most one member, and the
cardinality factor `|fibre|^β` is `1`.   finding 6(b) diagnosed exactly this
configuration and moved the interface from `∀` to `∃` — but the `∃` ranges over subsets of `t₁`,
so it does not reach past a `t₁` that has no proper nonempty subsets. -/
theorem middle_gain_nonpos_of_card_le_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {δ τ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1) {β gm : ℝ} (hβ0 : 0 ≤ β)
    {ι : Type*} {s₁ fib : Finset ι} {T : ι → ShadedTube δ E} {Yτ' : ι → ShadedTube τ E}
    {Loss A C : ENNReal}
    (hcard1 : fib.card ≤ 1)
    (hmass : 0 < ∑ i ∈ s₁, volume (T i).shade)
    (hprod : ShadedBody.multiplicity s₁ (fun i ↦ (T i).toShadedBody)
      ≤ Loss * A * ShadedBody.multiplicity fib (fun j ↦ (Yτ' j).toShadedBody) * C)
    (hbd : ShadedBody.multiplicity fib (fun j ↦ (Yτ' j).toShadedBody)
      ≤ (δ : ENNReal) ^ gm * ((fib.card : ℕ) : ENNReal) ^ β) :
    gm ≤ 0 := by
  have hleft : ShadedBody.multiplicity s₁ (fun i ↦ (T i).toShadedBody) ≠ 0 :=
    multiplicity_ne_zero_of_mass_pos s₁ (fun i ↦ (T i).toShadedBody) hmass
  have hmidne : ShadedBody.multiplicity fib (fun j ↦ (Yτ' j).toShadedBody) ≠ 0 := by
    intro h0
    rw [h0] at hprod
    simp only [mul_zero, zero_mul] at hprod
    exact hleft (le_antisymm hprod bot_le)
  have hone : (1 : ENNReal) ≤ ShadedBody.multiplicity fib (fun j ↦ (Yτ' j).toShadedBody) :=
    one_le_multiplicity_of_ne_zero fib (fun j ↦ (Yτ' j).toShadedBody) hmidne
  have hcardE : ((fib.card : ℕ) : ENNReal) ≤ 1 := by exact_mod_cast hcard1
  have hδE0 : (δ : ENNReal) ≠ 0 := by simpa using hδ0.ne'
  have hδE1 : (δ : ENNReal) < 1 := by exact_mod_cast hδ1
  have hstep : (1 : ENNReal) ≤ (δ : ENNReal) ^ gm := by
    refine hone.trans (hbd.trans ?_)
    calc (δ : ENNReal) ^ gm * ((fib.card : ℕ) : ENNReal) ^ β
        ≤ (δ : ENNReal) ^ gm * (1 : ENNReal) ^ β := by gcongr
      _ = (δ : ENNReal) ^ gm := by rw [ENNReal.one_rpow, mul_one]
  by_contra hcon
  rw [not_le] at hcon
  exact absurd hstep (not_le.mpr (ENNReal.rpow_lt_one hδE1 hcon))

/-- **The same, phrased on the retained node set the split is chosen inside.**

If the window's retained node set `t₁` has at most one member then so does every coarse fibre of
every `tτ' ⊆ t₁`, so `Kakeya.ML2Core.middle_gain_nonpos_of_card_le_one` applies and the middle
factor is available at **no positive gain at all**.

`Kakeya.ML2Core.geometricCoreAt_of_middleFactor` asks for the gain `2 ε + 14 ε₁/25`, which is
positive for every `ε > 0` and `ε₁ > 0`. **So its hypothesis is false at every input whose
retained node set is a singleton and whose leaf mass is positive** — no cardinality ceiling, no
large `ε₁`, no exponent bookkeeping needed. -/
theorem middle_gain_nonpos_of_singleton_nodes {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {δ τ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1) {β gm : ℝ} (hβ0 : 0 ≤ β)
    {ι : Type*} {u s₁ t₁ tτ' : Finset ι} {T : ι → ShadedTube δ E} {Yτ' : ι → ShadedTube τ E}
    {N : ℕ} {σ : ℕ → NNReal} (𝒞 : Tube.ChainCoverSystem u (fun i ↦ (T i).toTube) N σ)
    {a b : ℕ} {jθ : ι} {Loss A C : ENNReal}
    (ht₁ : t₁.card ≤ 1) (htτ : tτ' ⊆ t₁)
    (hmass : 0 < ∑ i ∈ s₁, volume (T i).shade)
    (hprod : ShadedBody.multiplicity s₁ (fun i ↦ (T i).toShadedBody)
      ≤ Loss * A * ShadedBody.multiplicity
          (open scoped Classical in
            ({j ∈ tτ' | ML2Reduction.coarseNode 𝒞 a b j = jθ} : Finset ι))
          (fun j ↦ (Yτ' j).toShadedBody) * C)
    (hbd : ShadedBody.multiplicity
        (open scoped Classical in
          ({j ∈ tτ' | ML2Reduction.coarseNode 𝒞 a b j = jθ} : Finset ι))
        (fun j ↦ (Yτ' j).toShadedBody)
      ≤ (δ : ENNReal) ^ gm
        * ((((open scoped Classical in
            ({j ∈ tτ' | ML2Reduction.coarseNode 𝒞 a b j = jθ} : Finset ι))).card : ℕ) :
              ENNReal) ^ β) :
    gm ≤ 0 := by
  classical
  refine middle_gain_nonpos_of_card_le_one hδ0 hδ1 hβ0 ?_ hmass hprod hbd
  exact le_trans (Finset.card_le_card ((Finset.filter_subset _ _).trans htτ)) ht₁

end Singleton

/-! ## The sharp rung exponent: `47 η_k/(5 e)` at `δ̃`, i.e. `9.4 η_k` at the ambient scale -/

section SharpBudget

/-- **The gain budget at the sharp exponent `47 X/(5 e)`.**

`Kakeya.ML2Reduction.gainBudget_of_step_le` reads the middle factor at `10 X/ε₂`, which — since
`ε₂ ≥ 5 e` — is at most `2 X/e`.  That reading is what
`Kakeya.ML2Core.spineRung_middle_gain_lt_demand` shows is hopeless against the wiring's demand,
and it is **not** the sharpest the construction supports: `Kakeya.ML2Spine.spineStep`'s second
entry gives `ν ≥ 34 X/(e β)`, and after the `(1-ε₂)` rescaling loss and the eccentricity charge
`2 · 12 X/(e β)` what is left is `(10 - 34 ε₂) X/(e β) - κ`, i.e. **essentially `10 X/e` and not
`2 X/e`**, because `β ≤ 1`.

This lemma takes `47 X/(5 e) = 9.4 X/e` of it and leaves `X/(20 e)` for the multiscale loss.  The
arithmetic that has to close is `9.45 β + 34 ε₂ ≤ 10`, and on the constructed spine
`β ≤ 1` and `ε₂ ≤ 1/64` give `9.45 + 0.53125 = 9.98125 ≤ 10`.

**Inert hypothesis found and not carried:** `0 ≤ ε₂` is *not* needed — a negative `ε₂` only makes
the right-hand side larger — so this lemma is stated without it.

**The margin is `0.019`, and the cap `ε₂ ≤ 1/64` is load-bearing**: the abstract
`Kakeya.ML2Spine.IsSpine` only caps `ε₂ < 1/12`, at which `9.45 β + 34/12 > 10` for
`β` near `1`.  So this lemma is stated for the *construction*, not for an abstract spine — the
same distinction `Kakeya.ML2Reduction.rescaleLoss_not_free_of_isSpine_fields` draws one exponent
down. -/
theorem gainBudget_of_step_sharp {β ε₂ e X ν κ : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (he : 0 < e) (hε₂ : ε₂ ≤ 1 / 64)
    (hX : 0 < X) (hstep : X ≤ e * β * ν / 34) (hκ : κ ≤ X / (20 * e)) :
    47 * X / (5 * e) + 2 * (12 * X / (e * β)) + κ ≤ (1 - ε₂) * ν := by
  have heb : 0 < e * β := mul_pos he hβ
  have hB0 : 0 < X / (e * β) := div_pos hX heb
  have hBν : 34 * (X / (e * β)) ≤ ν := by
    rw [mul_div_assoc', div_le_iff₀ heb]
    nlinarith [hstep, heb]
  have hA : 47 * X / (5 * e) = 47 * β * (X / (e * β)) / 5 := by
    field_simp
  have hC : 2 * (12 * X / (e * β)) = 24 * (X / (e * β)) := by ring
  have hD : X / (20 * e) = β * (X / (e * β)) / 20 := by
    field_simp
  rw [hA, hC]
  rw [hD] at hκ
  nlinarith [hBν, hB0, hκ, hβ1, hε₂]

/-- **The sharp gain budget on the constructed spine.**

`Kakeya.ML2Spine.spineRung_eq_step`'s second minimum entry is
`e β · gain(η_{k+1}/2)/34`, which is exactly the `hstep` of
`Kakeya.ML2Core.gainBudget_of_step_sharp`; `Kakeya.ML2Spine.spineEps₂_le_inv64` supplies the cap
that lemma needs. -/
theorem spineRung_gainBudget_sharp {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {k : ℕ} (hk : k < ML2Spine.spineCount ϖ ε₁) {κ : ℝ}
    (hκ : κ ≤ ML2Spine.spineRung β ϖ ε₁ gain dens k / (20 * ML2Spine.spineDiv ϖ ε₁)) :
    47 * ML2Spine.spineRung β ϖ ε₁ gain dens k / (5 * ML2Spine.spineDiv ϖ ε₁)
        + 2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
            / (ML2Spine.spineDiv ϖ ε₁ * β)) + κ
      ≤ (1 - ML2Spine.spineEps₂ ϖ ε₁)
          * gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) := by
  have hsp := ML2Spine.spineRung_isSpine hβ hβ1 hϖ hε₁ hgain hdens
  have hst := ML2Spine.spineRung_eq_step (β := β) (ϖ := ϖ) (ε₁ := ε₁)
    (gain := gain) (dens := dens) hk
  have hstep : ML2Spine.spineRung β ϖ ε₁ gain dens k
      ≤ ML2Spine.spineDiv ϖ ε₁ * β
          * gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) / 34 := by
    rw [hst]
    exact (min_le_left _ _).trans (min_le_right _ _)
  exact gainBudget_of_step_sharp hβ hβ1 hsp.div_pos
    ML2Spine.spineEps₂_le_inv64 (hsp.rung_pos k) hstep hκ

/-- **Step 11 at the sharp exponent.**

`Kakeya.ML2Reduction.spine_multiplicity_le_two_factors` with
`Kakeya.ML2Core.spineRung_gainBudget_sharp` in place of
`Kakeya.ML2Reduction.spineRung_gainBudget_of_rescaleLoss`: the conclusion's exponent is
`47 η_k/(5 e)` instead of `10 η_k/ε₂`, at the price of the tighter multiscale budget
`κ ≤ η_k/(20 e)` instead of `κ ≤ 20 η_k/ε₂`.

**Why the trade is the right one.** Both budgets are spent on subpolynomial constants and can be
met by thresholds on `δ`; the exponent cannot. Transported to the ambient scale by
`Kakeya.ML2Core.middle_factor_of_rescaled` at the window's own separation exponent `e`, this reads
`δ^{47 η_k/5} = δ^{9.4 η_k}`, against `δ^{2 η_k}` for the `ε₂`-reading. -/
theorem spine_multiplicity_le_two_factors_sharp
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    {δt b δ' : NNReal} {mu mub muf L Cu : ENNReal} {Nb Nf N : ℕ} {κ : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    (hsplit : mu ≤ L * (mub * muf))
    (hb : mub ≤ (δt : ENNReal) ^
          (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k / (ML2Spine.spineDiv ϖ ε₁ * β))))
        * (Nb : ENNReal) ^ β)
    (hf : muf ≤ (δ' : ENNReal) ^ (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2))
        * (Nf : ENNReal) ^ β)
    (hcard : (Nb : ENNReal) * (Nf : ENNReal) ≤ Cu * (N : ENNReal))
    (hL : L * Cu ^ β ≤ (δt : ENNReal) ^ (-κ))
    (hκ : κ ≤ ML2Spine.spineRung β ϖ ε₁ gain dens k / (20 * ML2Spine.spineDiv ϖ ε₁)) :
    mu ≤ (δt : ENNReal) ^
          (47 * ML2Spine.spineRung β ϖ ε₁ gain dens k / (5 * ML2Spine.spineDiv ϖ ε₁))
        * (N : ENNReal) ^ β := by
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  have hpos : (0 : ℝ) < ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2 := by
    have := hsp.rung_pos (k + 1)
    linarith
  have hν : 0 ≤ gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) := (hgain _ hpos).le
  have hbud := spineRung_gainBudget_sharp hβ0 hβ1 hϖ hε₁ hgain hdens hk hκ
  refine ML2Reduction.multiplicity_le_of_two_factors_rescaled (by simpa using hδ0.ne')
    (by exact_mod_cast hδ1) hβ0.le hν (hsp.eps₂_le_half.trans (by norm_num))
    (ML2Reduction.rescaledScale_le hδ0 hbw hprod) hsplit hb hf hcard hL ?_
  linarith

end SharpBudget

/-! ## The sharp composition -/

section SharpComposition

open Classical in
/-- **The middle factor at the ambient scale, from the ED-node clause, at the SHARP exponent.**

Identical to `Kakeya.ML2Core.middle_factor_of_edNodes` except that step 11 is run through
`Kakeya.ML2Core.spine_multiplicity_le_two_factors_sharp`, so the rescaled exponent is
`47 η_k/(5 e)` rather than `10 η_k/ε₂` and the multiscale budget tightens from `20 η_k/ε₂` to
`η_k/(20 e)`.  Transported at the window's own separation exponent `w = e`
(`ML2Reduction.IsKatzTaoDividingWindow.scale_sep`) the ambient gain is

```
e · 47 η_k/(5 e)  =  47 η_k/5  =  9.4 η_k  ≥  9.4 ν
```

against `2 η_k` for the `ε₂`-reading — the factor of `4.7` that
`Kakeya.ML2Core.rung_budget_closes_of_overhead_le_four` needs and
`Kakeya.ML2Core.spineRung_middle_gain_lt_demand` shows the `ε₂`-reading does not have.

The body is `Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover`'s, inlined
because that theorem hard-codes its own exponent; every step of it is unchanged except the last. -/
theorem middle_factor_of_edNodes_sharp
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    -- the ambient window and the transport 
    {δ θ τ δt : NNReal} {Rout : ℝ} {w : ℝ}
    (hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3) (hRout : 0 < Rout)
    (hτθ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (δt : ℝ))
    (Tθ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {fib : Finset α}
    (Y : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsubOut : ∀ j ∈ fib, (Y j).carrier ⊆ Tθ.carrier)
    (hw : 0 ≤ w) (hsep : δt ≤ δ ^ w)
    -- the rescaled world 
    {b δ' : NNReal} {R : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1) (hδ'0 : 0 < δ') (hb1 : b ≤ 1) (hδtb : δt ≤ b)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))} {ηc : ℝ}
    (hcoarse : ∀ (dt : NNReal), dt ≠ 0 → dt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} (t : Finset ι) (T : ι → ShadedTube b (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ closedBall 0 1) →
        (ShadedBody.fullness t (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc →
        Kakeya.maxDensity t (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (dt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β))) →
        ShadedBody.multiplicity t (fun i ↦ (T i).toShadedBody)
          ≤ (dt : ENNReal) ^ (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β)))) * (t.card : ENNReal) ^ β)
    (hballb : ∀ j, (Zρ j).carrier ⊆ closedBall 0 1)
    (hfullb : (ShadedBody.fullness t' (fun j ↦ (Zρ j).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc)
    (hDb : Kakeya.maxDensity t' (fun j ↦ (Zρ j).toConvexSpaceBody)
      ≤ (δt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (ML2Spine.spineDiv ϖ ε₁ * β))))
    {s' : Finset α} (hs' : s' ⊆ fib)
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (hsubfib : ∀ i ∈ fib,
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier ⊆ T₀.carrier)
    {cst ζ ζ' ηd : ℝ}
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc fib s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ mm ϖ ζ s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hL91 : ML2Reduction.Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) + 3 * qc) ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (hmax : Kakeya.maxDensity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    -- AA/AB: tightened to the constant the producer actually returns
    -- (`ShadedTube.ssfUniformConst 3`, `Kakeya/ShadedUniform.lean:895`), with the threshold the
    -- loose bracket used to quantify away carried explicitly.  Discharged at wiring time by
    -- `exists_outerShadedUniformTubeSet_ssf` + `exists_threshold_coe_const_le_rpow_neg`.
    -- this binder is ALSO where the line-ED levels row is sourced.  The witness carries
    -- a uniform hierarchy, and `Kakeya.VeryNotSticky.lineEDLevelsAt_C3_of_huni` turns it (with
    -- `hcb`'s `centred`/`contained`/`small` rows and the uniformiser's own grid threshold) into
    -- `LineEDLevelsAt C₃ lineEDLevelsConstant _` at the NAMED constant (
    -- ): the datum is DERIVED here, never an ambient field.
    (huni : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3)))
    -- the ONE open input
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    -- stated on the CONTRACTED-bottom window `[δ'^{1-ϖ}/C, δ'^{ϖ}]`, because the
    -- centring hand-back reads the cover at `ρ/C`.  A producer of
    -- this clause must supply it on the wide window, not merely on Lemma 9.1's.
    (hED : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j l ↦ _root_.IsEssentiallyDistinct (W j).carrier (W l).carrier) ∧
        (∀ l ∈ t, (W l).carrier ⊆ T₀.carrier) ∧
        (∀ l ∈ t, ∃ i ∈ s',
          (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier
            ⊆ (W l).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    -- this is `hbudget` with `centringCountLossConstant R ·` at the head of the left-hand
    -- side, so it IMPLIES `hbudget`; `hbudget` is retained only because keeps its text
    -- tree-wide.  Discharged by `exists_threshold_hup_budget`'s argument at the
    -- new constant, never assumed; `ζ < ζ'` (`hgap`) is its side condition.
    (hcntbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hgap : ζ ≤ ζ')
    -- step 9, the cardinality multiplicativity and the loss ledger
    {Cf L Cu : ENNReal} {Nm : ℕ} {κ : ℝ}
    (hCf1 : (1 : ENNReal) ≤ Cf)
    (hsplit : ShadedBody.multiplicity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)
      ≤ L * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦
            (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)))
    (hcard : (t'.card : ENNReal) * (fib.card : ENNReal) ≤ Cu * (Nm : ENNReal))
    (hLoss : L * Cf * Cu ^ β ≤ (δt : ENNReal) ^ (-κ))
    (hκ : κ ≤ ML2Spine.spineRung β ϖ ε₁ gain dens k / (20 * ML2Spine.spineDiv ϖ ε₁)) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ENNReal) ^ (w * (47 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (5 * ML2Spine.spineDiv ϖ ε₁))) * (Nm : ENNReal) ^ β := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  have hgm : 0 ≤ 47 * ML2Spine.spineRung β ϖ ε₁ gain dens k / (5 * ML2Spine.spineDiv ϖ ε₁) := by
    have h1 := hsp.rung_pos k
    have h2 := hsp.div_pos
    positivity
  refine middle_factor_of_rescaled hsitOut hRout hτθ Tθ Y hsubOut hgm hw hsep ?_
  set Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)) :=
    ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y with hZ'
  have hb4 := hcoarse δt (ne_of_gt hδ0) hδtb hb1 t' Zρ hballb hfullb hDb
  -- Step 10 on the REPRESENTED family (the UNPRIMED eliminator): the hand-back's `3 qc`
  -- transport is inside it, so the `3 qc` is charged exactly once, on `hL91`'s gain (V-3).
  -- `Cf` keeps its text in `hLoss` and needs only `1 ≤ Cf`.
  have h10 := ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover
    (ν := gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2))
    hL91 hζ hsit hR hR1 hτσ hδ'0 hϖ.le hβ0.le hqc0 le_rfl h3qc T₀ mm hs'
    (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U' hcb hsubfib hloss
    (Kakeya.VeryNotSticky.huni_loose_of_tight huni)
    (fun ρ hρ ↦ hct ρ hρ
      (by
        -- the cover is read at the CONTRACTED radius; `hED` moved, `hbudget` did NOT —
        -- `Kakeya.ML2Reduction.budget_descends` carries it from `ρ` down to `ρ/C` 
        have hmem := Kakeya.VeryNotSticky.mem_widened_window_of_mem hρ
        have hc0 : 0 < ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant :=
          lt_of_lt_of_le (div_pos (NNReal.rpow_pos hδ'0)
            Kakeya.VeryNotSticky.edWindowContractionConstant_pos) hmem.1
        obtain ⟨κ₀, t, W, hEDt, hsubW, hused, hcard⟩ := hED _ hmem
        obtain ⟨κ₁, t₈, W', M, hsubW', hused', hM', hMρ', hcard'⟩ :=
          hstep8_of_essDistinct t W hEDt hsubW hused hcard
        exact ML2Reduction.canonicalCoverAt_of_step8_const (m := 0) (ζ' := ζ')
          (Kc := (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ))
          hsit hR T₀ _ hc0
          (le_trans (by exact_mod_cast hmem.2) hwin4) t₈ W' hsubW' hused' hM' hMρ' hcard'
          (ML2Reduction.budget_descends
            (h := ML2Reduction.hbud_of_hcntbudget (NNReal.coe_nonneg _)
              (by simpa using hcntbudget ρ hρ))
            (hρ'0 := by exact_mod_cast hc0)
            (hle := by exact_mod_cast Kakeya.VeryNotSticky.div_centringCoverRadiusConstant_le ρ)
            (he := by linarith))))
  have h10' : ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)
      ≤ (δ' : ENNReal) ^ (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2))
        * (fib.card : ENNReal) ^ β := by
    rw [← ML2Reduction.outerFamily_multiplicity hn hsit hR hτσ hsubfib]
    exact h10
  have hsplit2 : ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)
      ≤ (L * Cf) * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)) := by
    refine hsplit.trans (mul_le_mul' ?_ le_rfl)
    calc L = L * 1 := (mul_one L).symm
      _ ≤ L * Cf := by gcongr
  exact spine_multiplicity_le_two_factors_sharp hβ0 hβ1 hϖ hε₁ hgain hdens hk hδ0 hδ1 hbw hprod
    hsplit2 hb4 h10' hcard hLoss hκ

end SharpComposition

/-! ## The rung-level ledger: what the window branch must pay, and whether the sharp gain pays it -/

section Ledger

/-- **The window's separation exponent carries the sharp gain to the ambient scale undiminished.**

`Kakeya.ML2Core.middle_factor_of_rescaled` transports a gain `g` at `δ̃` to `w · g` at `δ`, where
`δ̃ ≤ δ^{w}`.  The sharp exponent is `47 X/(5 e)`, and the window's own
`ML2Reduction.IsKatzTaoDividingWindow.scale_sep` gives `w ≥ e` — so the `e` in the denominator
cancels and the ambient gain is `47 X/5` **whatever the window's width**.

This is the structural reason the `/e` reading matters and the `/ε₂` reading does not: `10 X/ε₂`
transports to `w · 10 X/ε₂ ≥ 10 e X/ε₂`, which is `≤ 2 X`, while `47 X/(5 e)` transports to
`≥ 9.4 X`. -/
theorem ambient_sharp_gain_ge {e w X : ℝ} (he : 0 < e) (hw : e ≤ w) (hX : 0 ≤ X) :
    47 * X / 5 ≤ w * (47 * X / (5 * e)) := by
  have h : w * (47 * X / (5 * e)) - 47 * X / 5 = (w - e) * (47 * X / (5 * e)) := by
    field_simp
    try ring
  nlinarith [div_nonneg (by linarith : (0:ℝ) ≤ 47 * X) (by positivity : (0:ℝ) ≤ 5 * e), hw, h]

/-- **The rung-level budget closes at every rung, once the pushback overhead is at most `4 ν`.**

The window branch's ledger, all at the **ambient** scale, at a window whose rung is `X = ηl m`:

```
     pushback overhead  Ω
   + the dichotomy's target        4 ν
   + the fine factor's accuracy    ε
   + the coarse factor's cost      ε + κc + X      (ML2Reduction.exists_coarse_factor_complete's
                                                    own binder `ε + (κ + ηl m) ≤ c`)
   + the multiscale loss           κ'
   ≤  the middle factor's gain     gmA
```

Every rung of a spine satisfies `X = η_m ≥ η_0 = ν` (`ML2Spine.IsSpine.rung_mono`), so the target
and the overhead — both measured in `ν` — are **dominated by the rung**, and the sharp ambient gain
`47 X/5 = 9.4 X` clears `Ω + 4ν + X ≤ 9 X` with `0.4 X` to spare for the three small terms.

**This is the whole positive content of the re-cut**: reading the coarse cost at the window's own
rung instead of at the flattened `ε₁/25`, and the middle factor at `47 η_k/(5 e)` instead of
`10 η_k/ε₂`, makes the budget close **uniformly in the window** — at `m = 0` as well as above.

**Inert hypotheses found and not carried:** `0 < ν`, `0 ≤ ε`, `0 ≤ κc`, `0 ≤ κ'` are all
unnecessary — `hsmall` and `hX` carry the whole chain — so they are not in the binder list. -/
theorem rung_budget_closes_of_overhead_le_four {ν X gmA Ω ε κc κ' : ℝ}
    (hX : ν ≤ X) (hgmA : 47 * X / 5 ≤ gmA) (hΩ : Ω ≤ 4 * ν)
    (hsmall : 2 * ε + κc + κ' ≤ 2 * ν / 5) :
    Ω + 4 * ν + ε + (ε + κc + X) + κ' ≤ gmA := by
  linarith [hX, hgmA, hΩ, hsmall]

/-- **REFUTATION: at the wiring's own overhead ledger the budget fails at the bottom rung, and the
sharp exponent does not save it.**

`Kakeya.ML2Core.geometricCoreAt_of_middleFactor`'s docstring prices the pushback at
`10 ν = 2ν + ν + 2ν + ν + 4ν`, i.e. an overhead `Ω = 6 ν` on top of the target `4 ν`.  At the
bottom rung `X = ν` the ledger then demands `Ω + 4ν + 2ε + κc + ν + κ' ≥ 11 ν`, while **no**
reading of the construction gives more than `10 ν` there — see
`Kakeya.ML2Core.ambient_gain_le_of_step`.

**So the re-cut is not optional and it is not only about the exponent**: two of the wiring's four
overhead terms (`StickyKakeya.totalLoss` and the seam constants) must be moved off `ν` onto free
thresholds, bringing `Ω` from `6 ν` to `4 ν`, before any middle factor can pay for the window
branch at `m = 0`. The other two (`2ν` for the package's cardinality loss and `2ν` for the two
`λ⁻¹`'s) are clauses of the package and are not movable. -/
theorem not_rung_budget_of_overhead_six {ν gmA Ω ε κc κ' : ℝ}
    (hν : 0 < ν) (hΩ : 6 * ν ≤ Ω) (hε : 0 ≤ ε) (hκc : 0 ≤ κc) (hκ' : 0 ≤ κ')
    (hgmA : gmA ≤ 10 * ν) :
    ¬ (Ω + 4 * ν + ε + (ε + κc + ν) + κ' ≤ gmA) := by
  intro h
  linarith [hν, hΩ, hε, hκc, hκ', hgmA, h]

/-- **The ceiling on the ambient gain, at the construction's extreme.**

`Kakeya.ML2Reduction.multiplicity_le_of_two_factors_rescaled`'s exponent hypothesis is
`θ ≤ (1-ε₂) ν_gain - 2 · 12 X/(e β) - κ`, and `Kakeya.ML2Spine.spineStep`'s second entry caps the
rung by `X ≤ e β ν_gain/34`.  **When that entry is the binding one** — i.e. at
`ν_gain = 34 X/(e β)` — the ambient gain `e θ` is at most `(10 - 34 ε₂) X/β`, which for `β ≤ 1` is
below `10 X`.

That is the number `Kakeya.ML2Core.not_rung_budget_of_overhead_six` is read against, and it is why
the sharp exponent `47/5 = 9.4` is close to optimal: the room between `9.4` and `10 - 34 ε₂` is
`0.069` at `ε₂ = 1/64`, and the multiscale budget `κ ≤ X/(20 e)` spends `0.05` of it.

**If the second entry is *not* binding — if Lemma 9.1's gain function is larger than the spine's
step needs — this ceiling does not apply and more is available.** Nothing in
`ML2Assembly.Lemma91ParamsAt` bounds `gain` from above, so this is a statement about the worst
case, and I label it as such. -/
theorem ambient_gain_le_of_step {β ε₂ e X νg θ κ : ℝ}
    (hβ : 0 < β) (he : 0 < e) (hε₂ : ε₂ ≤ 1) (hκ : 0 ≤ κ)
    (hextreme : e * β * νg / 34 ≤ X)
    (hexp : θ ≤ (1 - ε₂) * νg - 2 * (12 * X / (e * β)) - κ) :
    e * θ ≤ (10 - 34 * ε₂) * X / β := by
  have heb : 0 < e * β := mul_pos he hβ
  have hνg : νg ≤ 34 * X / (e * β) := by
    rw [le_div_iff₀ heb]; nlinarith [hextreme]
  have hgrow : (1 - ε₂) * νg ≤ (1 - ε₂) * (34 * X / (e * β)) := by
    exact mul_le_mul_of_nonneg_left hνg (by linarith)
  have hid : (1 - ε₂) * (34 * X / (e * β)) - 2 * (12 * X / (e * β))
      = (10 - 34 * ε₂) * X / (e * β) := by
    field_simp
    try ring
  have hθ : θ ≤ (10 - 34 * ε₂) * X / (e * β) - κ := by
    rw [← hid]; linarith
  have hmul : e * θ ≤ e * ((10 - 34 * ε₂) * X / (e * β) - κ) :=
    mul_le_mul_of_nonneg_left hθ he.le
  have hid2 : e * ((10 - 34 * ε₂) * X / (e * β)) = (10 - 34 * ε₂) * X / β := by
    field_simp
    try ring
  nlinarith [hmul, hid2, mul_nonneg he.le hκ]

end Ledger

/-! ## The model: the existing `hmid` is false, not vacuous -/

section Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

open Classical in
/-- **The constant hierarchy on a one-element family.**

Every node at every grid level is the same tube, rescaled to that level's radius; the assignment is
constant.  `Tube.GridCoverSystem`'s six fields are then discharged by
`Kakeya.Tube.le_rescale` (containment) and `Kakeya.Tube.rescale_le_rescale_of_radius_le`
(nestedness), with `δ ≤ δ^{k/N}` for `k ≤ N` the only arithmetic.

**A `def` and not an `∃`, for the reason `Kakeya.ML2Core.chainAtScale` is:**
`Tube.GridCoverSystem` is a *structure*, and the model below must hand a concrete one to
`Kakeya.ML2Core.geometricCoreAt_of_middleFactor`'s hypothesis. It is a construction, not a
`Prop`, and it introduces no obligation — every field is discharged here. -/
noncomputable def singletonCover {ι : Type*} (i₀ : ι) {δ : NNReal}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ) (T : ι → Tube δ E) :
    Tube.GridCoverSystem ({i₀} : Finset ι) T N where
  indexSet := fun _ => {i₀}
  assign := fun _ _ => i₀
  tube := fun k _ => (T i₀).rescale (Tube.gridScale δ N k)
  assign_mem := fun k _ i _ => Finset.mem_singleton_self i₀
  le_tube_assign := by
    intro k hk i hi
    rw [Finset.mem_singleton] at hi
    rw [hi]
    refine (T i₀).le_rescale ?_
    have hkN : ((k : ℝ) / (N : ℝ)) ≤ 1 := by
      rcases Nat.eq_zero_or_pos N with h | h
      · simp [h]
      · rw [div_le_one (by exact_mod_cast h)]
        exact_mod_cast hk
    have := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hkN
    rw [NNReal.rpow_one] at this
    simpa [Tube.gridScale] using this
  nested := fun _ _ _ _ _ _ _ => rfl
  tube_nested := by
    intro k hk i hi
    exact Tube.rescale_le_rescale_of_radius_le (T i₀)
      (Tube.gridScale_antitone hδ0 hδ1 N (Nat.le_succ k))

open Classical in
/-- **The constant hierarchy is a `Tube.UniformTubeSet` at `C = 1`.**

`branchingN ≡ 1`; bounded overlap and both branching brackets are the one-element bounds.  GWZ
Definition 2.1 is satisfied *exactly*, with the sharpest possible constant. -/
noncomputable def singletonUniform {ι : Type*} (i₀ : ι) {δ : NNReal}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ) (T : ι → Tube δ E) :
    Tube.UniformTubeSet ({i₀} : Finset ι) T N 1 where
  cover := singletonCover i₀ hδ0 hδ1 N T
  branchingN := fun _ => 1
  tube_injOn := by
    intro k hk x hx y hy _
    simp only [singletonCover, Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
    rw [hx, hy]
  boundedOverlap := by
    intro k hk V
    refine le_trans ?_ (le_refl (1 : NNReal))
    have : ((({i₀} : Finset ι).filter (fun j => ∃ i ∈ ({i₀} : Finset ι),
        (T i).toConvexSpaceBody ≤ (((singletonCover i₀ hδ0 hδ1 N T).tube k j)).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : NNReal) ≤ 1 := by
      have hsub : ({i₀} : Finset ι).filter (fun j => ∃ i ∈ ({i₀} : Finset ι),
        (T i).toConvexSpaceBody ≤ (((singletonCover i₀ hδ0 hδ1 N T).tube k j)).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) ⊆ ({i₀} : Finset ι) := by
        intro x hx
        exact (Finset.mem_filter.mp hx).1
      have hc : (({i₀} : Finset ι).filter (fun j => ∃ i ∈ ({i₀} : Finset ι),
        (T i).toConvexSpaceBody ≤ (((singletonCover i₀ hδ0 hδ1 N T).tube k j)).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤ 1 := by
        simpa using Finset.card_le_card hsub
      exact_mod_cast hc
    exact this
  card_class_le := by
    intro k hk j hj
    have hsub : Tube.coverClass ({i₀} : Finset ι) (fun _ => i₀) j ⊆ ({i₀} : Finset ι) := by
      intro x hx
      exact (Finset.mem_filter.mp hx).1
    have hc : (Tube.coverClass ({i₀} : Finset ι) (fun _ => i₀) j).card ≤ 1 := by
      simpa using Finset.card_le_card hsub
    simp only [one_mul]
    exact_mod_cast hc
  le_card_class := by
    intro k hk j hj
    simp only [singletonCover, Finset.mem_singleton] at hj
    have hne : (Tube.coverClass ({i₀} : Finset ι) (fun _ => i₀) j).Nonempty := by
      refine ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_singleton_self i₀, ?_⟩⟩
      exact hj.symm
    have h1 : 1 ≤ (Tube.coverClass ({i₀} : Finset ι) (fun _ => i₀) j).card :=
      Finset.card_pos.mpr hne
    simp only [one_mul]
    exact_mod_cast h1

omit [Nontrivial E] in
/-- **A Katz--Tao dividing window on the constant hierarchy**, at `a = 0`, `b = 1`, `m = 0`,
`η ≡ 0`, `ε_div = 0`, `C⋆ = 1`.

All seven fields of `Kakeya.ML2Reduction.IsKatzTaoDividingWindow` hold: the two density ceilings
are `Kakeya.maxDensity_le_card` on a one-element family, and the window's lower bound is
`Kakeya.one_le_maxDensity` — at `η ≡ 0` both sides of every density clause are `1`.

**This is not a degenerate reading of the structure.** `η ≡ 0` satisfies the ladder conditions of
`Kakeya.ML2Reduction.exists_dichotomy_katzTaoDividingWindow` (`0 ≤ η 0`,
`η k ≤ ε_div η (k+1)`, `η N ≤ ε_div`) at `ε_div = 0`, and
`Kakeya.ML2Core.geometricCoreAt_of_middleFactor`'s hypothesis quantifies over **arbitrary**
`ηl`, `εd`, `Nw`, `a`, `b`, `m` subject only to the structure and to `0 ≤ ηl m ≤ ε₁/25`. -/
theorem singletonWindow {ι : Type*} (i₀ : ι) {δ : NNReal}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN : 1 ≤ Tube.ssfGridLen δ) (T : ι → Tube δ E)
    (hvol : 0 < volume (T i₀).carrier) :
    ML2Reduction.IsKatzTaoDividingWindow
      (singletonUniform i₀ hδ0 hδ1 (Tube.ssfGridLen δ) T) 1 (fun _ => (0:ℝ)) 0
      (Tube.ssfGridLen δ) 0 1 0 := by
  classical
  set N := Tube.ssfGridLen δ with hNdef
  set 𝒰 := singletonUniform i₀ hδ0 hδ1 N T with h𝒰
  have hidx : ∀ k, 𝒰.cover.indexSet k = ({i₀} : Finset ι) := fun k => rfl
  have h0 : ((Tube.gridScale δ N 0 : NNReal) : ℝ) = 1 := by
    rw [Tube.gridScale_zero]; norm_num
  have hg1 : Tube.gridScale δ N 1 ≤ Tube.gridScale δ N 0 :=
    Tube.gridScale_antitone hδ0 hδ1 N (Nat.zero_le 1)
  have hδg : δ ≤ Tube.gridScale δ N 1 := by
    have hkN : ((1 : ℕ) : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN)]
      exact_mod_cast hN
    have := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hkN
    rw [NNReal.rpow_one] at this
    simpa [Tube.gridScale] using this
  have hmaxle : ∀ (W : ι → ConvexSpaceBody E),
      _root_.Kakeya.maxDensity ({i₀} : Finset ι) W ≤ 1 := by
    intro W
    simpa using _root_.Kakeya.maxDensity_le_card ({i₀} : Finset ι) W
  refine ⟨?_, ?_, hN, ?_, ?_, ?_, ?_⟩
  · exact Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  · exact Nat.zero_lt_one
  · have h1 : ((Tube.gridScale δ N 1 : NNReal) : ℝ) ≤ 1 := by
      exact_mod_cast Tube.gridScale_le_one hδ1 N 1
    rw [h0, Real.rpow_zero]
    simpa using h1
  · rw [hidx 0, h0]
    simpa using hmaxle (fun j => (𝒰.cover.tube 0 j).toConvexSpaceBody)
  · intro j hj
    have hsub : 𝒰.nodesUnder 1 0 j ⊆ ({i₀} : Finset ι) := by
      intro x hx
      exact (Finset.mem_filter.mp hx).1
    refine le_trans (_root_.Kakeya.maxDensity_mono _ hsub) ?_
    simpa using hmaxle (fun j' => (𝒰.cover.tube 1 j').toConvexSpaceBody)
  · intro ρ hρ1 _ j hj
    rw [hidx 0, Finset.mem_singleton] at hj
    rw [Real.rpow_zero] at hρ1
    have hgρ : Tube.gridScale δ N 1 ≤ ρ := by
      have : ((Tube.gridScale δ N 1 : NNReal) : ℝ) ≤ (ρ : ℝ) := by simpa using hρ1
      exact_mod_cast this
    have hnodes : i₀ ∈ 𝒰.nodesUnder 1 0 j := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_singleton_self i₀, ?_⟩
      rw [hj]
      exact Tube.rescale_le_rescale_of_radius_le (T i₀) hg1
    have hle : (T i₀).toConvexSpaceBody
        ≤ ((𝒰.cover.tube 1 i₀).rescale ρ).toConvexSpaceBody :=
      le_trans ((T i₀).le_rescale hδg) ((𝒰.cover.tube 1 i₀).le_rescale hgρ)
    have hpos : 0 < volume ((𝒰.cover.tube 1 i₀).rescale ρ).carrier :=
      lt_of_lt_of_le hvol (measure_mono hle)
    have hone : (1 : ENNReal) ≤ _root_.Kakeya.maxDensity (𝒰.nodesUnder 1 0 j)
        (fun j' => ((𝒰.cover.tube 1 j').rescale ρ).toConvexSpaceBody) :=
      _root_.Kakeya.one_le_maxDensity ⟨i₀, hnodes, hpos⟩
    rw [h0, Real.rpow_zero]
    simpa using hone

open Classical in
/-- **THE MODEL: the hypothesis of `Kakeya.ML2Core.geometricCoreAt_of_middleFactor` is FALSE.**

Not "vacuous or false" — **false**.  A single unit-length `δ`-tube centred at the origin, shaded by
the whole of its carrier, carries **every** binder of that hypothesis at every small enough `δ`:
the constant hierarchy (`Kakeya.ML2Core.singletonUniform`), the dividing window
(`Kakeya.ML2Core.singletonWindow`), the unit-ball conditions (the tube's segment is centred, so
`Kakeya.Tube.carrier_subset_closedBall_midpoint` gives `1/2 + ρ ≤ 1` for every radius the window
uses, `Kakeya.ML2Core.eventually_gridScale_le` supplying `ρ ≤ 1/2`), the density ceiling
(`maxDensity ≤ 1 ≤ δ^{-ν}`), the dense shading at `lam = 1`, the cardinality binder
(`1 ≤ δ^{-4}`) and the mass positivity (`Kakeya.Tube.le_volume`).

Its retained node set `t₁` is a **singleton**, so
`Kakeya.ML2Core.middle_gain_nonpos_of_singleton_nodes` turns the hypothesis's own conclusion into
`2 ε + 14 ε₁/25 ≤ 0`, which `0 < ε` refutes.

`β`, `ϖ`, `gain`, `dens` and the three analytic packages are carried as hypotheses because they are
not constructible here — Katz--Tao and Frostman at `β` are the development's own inputs.  That
costs nothing: the conclusion is `False`, so any instantiation of them yields the refutation. -/
theorem not_middleFactor_hypothesis (ε : ℝ) (hε : 0 < ε)
    (hmid : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{u} β ϖ gain dens →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ ε₁ : ℝ, 0 < ε₁ →
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
          NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (Cstar : ENNReal) (ηl : ℕ → ℝ) (εd : ℝ) (Nw a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar ηl εd Nw a b m →
      ∀ (v : (EuclideanSpace ℝ (Fin 3))) (t₀ t₁ : Finset ι),
        t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
        (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier ⊆ Metric.closedBall (0 :
            (EuclideanSpace ℝ (Fin 3))) 1) →
        (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier ⊆
            Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
        (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
        (a ≠ 0 → ∀ k ∈ t₀,
          ((𝒰.cover.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin
              3))) 1) →
        (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        u.Nonempty →
        _root_.Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^
            (-(ML2Spine.spineNu β ϖ ε₁ gain dens)) →
        ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
        (δ : NNReal) ^ (ML2Spine.spineNu β ϖ ε₁ gain dens) / 2 ≤ lam →
        (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
        Cstar ≤ (δ : ENNReal) ^ (-(2 * (ML2Spine.spineNu β ϖ ε₁ gain dens))) →
        0 ≤ ηl m → ηl m ≤ ε₁ / 25 →
        ((Cu : NNReal) : ENNReal) ^ (1 - β) ≤ (δ : ENNReal) ^ (-(ε + 2 * ML2Spine.spineNu β ϖ ε₁
            gain dens + ε₁ / 25)) →
        0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
        δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
        Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
        Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
      ∃ tτ' ⊆ t₁, ∃ tθ' ⊆ 𝒰.cover.indexSet a,
        ∃ (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
          (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
          (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (jθ : ι),
          (∀ j, (Yτ' j).toTube = (𝒰.cover.tube b j).translate v) ∧
          (∀ k, (Yθ k).toTube = (𝒰.cover.tube a k).translate v) ∧
          (∀ i, (Y' i).toTube = ((T i).translate v).toTube) ∧
          (a ≠ 0 → ∀ k ∈ tθ', (Yθ k).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3)))
              1) ∧
          tτ'.Nonempty ∧ tθ'.Nonempty ∧
          ShadedBody.IsCRefinement
            ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) | 𝒰.cover.assign b i ∈ tτ'} :
                Finset ι)
            (fun i ↦ (Y' i).toShadedBody) ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
            (fun i ↦ ((T i).translate v).toShadedBody)
            (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (({i ∈ u |
                𝒰.cover.assign b i ∈ t₁} : Finset ι)).card δ)⁻¹ ∧
          (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (({i ∈ u |
              𝒰.cover.assign b i ∈ t₁} : Finset ι)).card δ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
                (Tube.gridScale δ (Tube.ssfGridLen δ) b))⁻¹ *
              ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
                  i).toShadedBody)
            ≤ ShadedBody.fullness tθ' (fun k ↦ (Yθ k).toShadedBody) ∧
          (∀ jτ ∈ tτ', ∀ jθ ∈ tθ',
            ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
                i).toShadedBody)
              ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (({i ∈
                  u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card δ *
                    ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
                        tτ'.card
                      (Tube.gridScale δ (Tube.ssfGridLen δ) b) : NNReal) : ENNReal)
                * ShadedBody.multiplicity
                    ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) | 𝒰.cover.assign b i =
                        jτ} : Finset ι)
                    (fun i ↦ (Y' i).toShadedBody)
                * ShadedBody.multiplicity
                    ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι)
                    (fun j ↦ (Yτ' j).toShadedBody)
                * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)) ∧
          jθ ∈ tθ' ∧
          ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ}
              : Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
            ≤ (δ : ENNReal) ^ (2 * ε + 14 * (ε₁ / 25))
              * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset
                  ι)).card : ENNReal) ^ β)
    (β' ϖ' : ℝ) (gain' dens' : ℝ → ℝ) (hβ0' : 0 < β') (hβ1' : β' ≤ 1)
    (hp' : ML2Assembly.Lemma91ParamsAt.{u} β' ϖ' gain' dens')
    (hKT' : _root_.Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β')
    (hF' : _root_.Kakeya.FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β') :
    False := by
  have hν0 : 0 < ML2Spine.spineNu β' ϖ' 1 gain' dens' :=
    ML2Spine.spineNu_pos hβ0' hp'.window_pos one_pos hp'.gain_pos hp'.dens_pos
  have hev := hmid β' ϖ' gain' dens' hβ0' hβ1' hp' hKT' hF' 1 one_pos
  obtain ⟨d1, hd10, hd11, hd1⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le 1 le_rfl 0 1 1 one_pos
  have hgrid := eventually_gridScale_le (ρ₀ := (1/2 : NNReal)) (by norm_num)
  have hall : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, False := by
    filter_upwards [hev, hgrid, Ioc_mem_nhdsGT hd10,
      Ioc_mem_nhdsGT (show (0:NNReal) < 1/2 by norm_num)] with δ hδmid hδgrid hδd1 hδhalf
    obtain ⟨hδ0, hδd⟩ := hδd1
    obtain ⟨-, hδhalf'⟩ := hδhalf
    have hδ1 : δ ≤ 1 := hδhalf'.trans (by norm_num)
    have hδlt1 : δ < 1 := lt_of_le_of_lt hδhalf' (by norm_num)
    have hN : 1 ≤ Tube.ssfGridLen δ := (hd1 hδ0 hδd).1
    set N := Tube.ssfGridLen δ with hNdef
    -- the one tube, centred at the origin
    obtain ⟨e, he⟩ : ∃ e : EuclideanSpace ℝ (Fin 3), ‖e‖ = 1 :=
      exists_norm_eq _ zero_le_one
    have hd : dist (-((2 : ℝ)⁻¹ • e)) ((2 : ℝ)⁻¹ • e) = 1 := by
      rw [dist_eq_norm]
      have hsub : -((2 : ℝ)⁻¹ • e) - (2 : ℝ)⁻¹ • e = -e := by module
      rw [hsub, norm_neg, he]
    set T₀ : Tube δ (EuclideanSpace ℝ (Fin 3)) := Tube.mk' δ hd with hT₀
    have hmid0 : midpoint ℝ T₀.x T₀.y = 0 := by
      have : T₀.x = -((2 : ℝ)⁻¹ • e) := rfl
      have hy : T₀.y = (2 : ℝ)⁻¹ • e := rfl
      rw [this, hy, midpoint_eq_smul_add]
      module
    -- every rescale of it sits in the unit ball, provided its radius is at most `1/2`
    have hball : ∀ ρ : NNReal, ρ ≤ 1/2 →
        (T₀.rescale ρ).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      intro ρ hρ
      have hmidρ : midpoint ℝ (T₀.rescale ρ).x (T₀.rescale ρ).y = 0 := hmid0
      have := _root_.Kakeya.Tube.carrier_subset_closedBall_midpoint
        (E := EuclideanSpace ℝ (Fin 3)) (T₀.rescale ρ)
      rw [hmidρ] at this
      refine this.trans (Metric.closedBall_subset_closedBall ?_)
      have : (ρ : ℝ) ≤ 1/2 := by exact_mod_cast hρ
      linarith
    have hballT₀ : T₀.carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      have h := _root_.Kakeya.Tube.carrier_subset_closedBall_midpoint
        (E := EuclideanSpace ℝ (Fin 3)) T₀
      rw [hmid0] at h
      refine h.trans (Metric.closedBall_subset_closedBall ?_)
      have : (δ : ℝ) ≤ 1/2 := by exact_mod_cast hδhalf'
      linarith
    have hvol : 0 < volume T₀.carrier := by
      refine lt_of_lt_of_le ?_ (Tube.le_volume T₀)
      have hc := Tube.le_volume.c_pos (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
      refine ENNReal.mul_pos ?_ ?_
      · simpa using ne_of_gt hc
      · simp only [ne_eq, pow_eq_zero_iff', not_and, not_not]
        intro h0
        exact absurd (by exact_mod_cast h0 : δ = 0) (ne_of_gt hδ0)
    -- the fully shaded one-tube family, indexed by `PUnit`
    set Y : PUnit.{u+1} → ShadedTube δ (EuclideanSpace ℝ (Fin 3)) := fun _ =>
      { toTube := T₀
        shade := T₀.carrier
        measurableSet_shade := T₀.toConvexSpaceBody.isCompact.isClosed.measurableSet
        shade_subset := subset_rfl } with hY
    set u : Finset PUnit.{u+1} := {PUnit.unit} with hu
    set 𝒰 := singletonUniform (PUnit.unit : PUnit.{u+1}) hδ0 hδ1 N
      (fun i => (Y i).toTube) with h𝒰
    have hwin : ML2Reduction.IsKatzTaoDividingWindow 𝒰 1 (fun _ => (0:ℝ)) 0 N 0 1 0 :=
      singletonWindow (PUnit.unit : PUnit.{u+1}) hδ0 hδ1 hN (fun i => (Y i).toTube) hvol
    -- the scale facts
    have hg1half : Tube.gridScale δ N 1 ≤ 1/2 := hδgrid 1 le_rfl hN
    have hg0 : Tube.gridScale δ N 0 = 1 := Tube.gridScale_zero δ N
    have hδg : δ ≤ Tube.gridScale δ N 1 := by
      have hkN : ((1 : ℕ) : ℝ) / (N : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN)]
        exact_mod_cast hN
      have := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hkN
      rw [NNReal.rpow_one] at this
      simpa [Tube.gridScale] using this
    have hone_le : ∀ x : ℝ, 0 ≤ x → (1 : ENNReal) ≤ (δ : ENNReal) ^ (-x) := by
      intro x hx
      have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
      have := ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith : -x ≤ (0:ℝ))
      simpa using this
    have hν := hν0
    -- the binders
    have ht₁ : u ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain 1 := by
      rw [hu, Finset.singleton_subset_iff]
      have := ML2Reduction.assign_mem_activeNodes 𝒰.cover.toChain (k := 1) hN
        (i := (PUnit.unit : PUnit.{u+1})) (Finset.mem_singleton_self _)
      simpa using this
    have hballtube : ∀ j : PUnit.{u+1},
        ((𝒰.cover.tube 1 j).translate (0 : EuclideanSpace ℝ (Fin 3))).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      intro j x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have : y ∈ (T₀.rescale (Tube.gridScale δ N 1)).carrier := hy
      simpa using hball _ hg1half this
    have hballleaf : ∀ i : PUnit.{u+1},
        ((Y i).translate (0 : EuclideanSpace ℝ (Fin 3))).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      intro i x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have : y ∈ T₀.carrier := hy
      simpa using hballT₀ this
    have hone_leN : ∀ x : ℝ, 0 ≤ x → (1 : NNReal) ≤ δ ^ (-x) := by
      intro x hx
      have := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith : -x ≤ (0:ℝ))
      simpa using this
    have hmaxu : _root_.Kakeya.maxDensity u (fun i => (Y i).toConvexSpaceBody)
        ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β' ϖ' 1 gain' dens')) := by
      refine le_trans ?_ (hone_le _ hν.le)
      simpa [hu] using _root_.Kakeya.maxDensity_le_card u (fun i => (Y i).toConvexSpaceBody)
    have hdense : ML2Shaded.HasDenseShading 1 u (fun i => (Y i).toShadedBody) := by
      intro i _
      simp [hY]
    have hlamlow : δ ^ (ML2Spine.spineNu β' ϖ' 1 gain' dens') / 2 ≤ (1 : NNReal) := by
      have h1 : δ ^ (ML2Spine.spineNu β' ϖ' 1 gain' dens') ≤ 1 :=
        NNReal.rpow_le_one hδ1 hν.le
      calc δ ^ (ML2Spine.spineNu β' ϖ' 1 gain' dens') / 2 ≤ 1 / 2 := by gcongr
        _ ≤ 1 := by norm_num
    have hcardu : (u.card : NNReal) ≤ δ ^ (-(4:ℝ)) := by
      simpa [hu] using hone_leN 4 (by norm_num)
    have hCstar : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-(2 * ML2Spine.spineNu β' ϖ' 1 gain' dens')) :=
      hone_le _ (by linarith)
    have hCubnd : ((1 : NNReal) : ENNReal) ^ (1 - β')
        ≤ (δ : ENNReal) ^ (-(ε + 2 * ML2Spine.spineNu β' ϖ' 1 gain' dens' + 1/25)) := by
      have h1 : ((1 : NNReal) : ENNReal) ^ (1 - β') = 1 := by
        simp
      rw [h1]
      exact hone_le (ε + 2 * ML2Spine.spineNu β' ϖ' 1 gain' dens' + 1/25) (by linarith)
    have hθ1 : Tube.gridScale δ N 0 ≤ 1 := le_of_eq hg0
    have hτθ : Tube.gridScale δ N 1 ≤ Tube.gridScale δ N 0 :=
      Tube.gridScale_antitone hδ0 hδ1 N (Nat.zero_le 1)
    -- apply the middle-factor hypothesis at this model
    obtain ⟨tτ', htτ', tθ', htθ', Yτ', Yθ, Y', jθ, -, -, -, -, hτne, -, -, -, hprod, hjθ,
      hmidbd⟩ :=
      hδmid u Y 1 1 𝒰 1 (fun _ => (0:ℝ)) 0 N 0 1 0 hwin 0 (∅ : Finset PUnit.{u+1}) u
        ht₁ (fun j _ => hballtube j) (fun i _ => hballleaf i)
        (fun h => absurd rfl h) (fun h => absurd rfl h) (fun h => absurd rfl h)
        (fun i _ => hballT₀) ⟨PUnit.unit, by simp [hu]⟩
        hmaxu hdense hlamlow hcardu hCstar le_rfl (by norm_num) hCubnd
        (by
          refine lt_of_lt_of_le hvol (Finset.single_le_sum_of_canonicallyOrdered
            (f := fun i => volume (Y i).shade) (i := (PUnit.unit : PUnit.{u+1})) ?_)
          simp [hu])
        hδg hτθ hθ1
    obtain ⟨jτ, hjτ⟩ := hτne
    have hle : 2 * ε + 14 * ((1:ℝ)/25) ≤ 0 :=
      middle_gain_nonpos_of_singleton_nodes (T := Y) (Yτ' := Yτ') (t₁ := u)
        hδ0 hδlt1 hβ0'.le 𝒰.cover.toChain (by simp [hu]) htτ'
        (by
          refine lt_of_lt_of_le hvol (Finset.single_le_sum_of_canonicallyOrdered
            (f := fun i => volume (Y i).shade) (i := (PUnit.unit : PUnit.{u+1})) ?_)
          simp [hu])
        (hprod jτ hjτ jθ hjθ) hmidbd
    linarith
  obtain ⟨δ, hδ⟩ := hall.exists
  exact hδ

end Model

end Kakeya.ML2Core

end
