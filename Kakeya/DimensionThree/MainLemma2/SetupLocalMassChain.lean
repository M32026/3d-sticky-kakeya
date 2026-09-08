/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupLocalMassTransport

/-!
# The bridge chain (B3, steps `B_m`) and its interpolation assembly (step `TR`)

GWZ §9.3 (l.1994–1999) applies Lemma 5.11 at the scales `a = δ^{ηj}`, `j = 1, …, η⁻¹`, to one
uniformised family, each application "abusing notation" to rename its output `(𝕋, Y)`; the
outputs are never re-uniformised. This file is that chain, in the tree's vocabulary, on top of the one-scale bridge
`Kakeya.VeryNotSticky.localMassAt_clause_of_rhoTubesSection9` (B1) and the transport
`Kakeya.VeryNotSticky.LocalMassClauseRel` (T1) with the volume comparison
`Kakeya.VeryNotSticky.volume_biUnion_shade_le_of_shadedUniform_of_isCRefinement` (T3).

* `Kakeya.VeryNotSticky.localMassAt_clause_of_shadedUniform_parent` — **one bridge step with the
  step-0 hierarchy as parent map.** For `s ⊆ s₀` with the tubes of `(s₀, T₀)` unchanged, the
  nodes `𝒱₀.tubeUniform.cover.tube k` and the assignment `𝒱₀.tubeUniform.cover.assign k` of the
  *first* family's hierarchy are a legal parent map for `(s, T)` at every `k ≤ N`
  (`Tube.GridCoverSystem.assign_mem`, `le_tube_assign`). This is why the chain needs no
  re-uniformisation between bridges.
* `Kakeya.VeryNotSticky.exists_bridgeChain_steps` — **the chain, by induction on the number of
  steps `M`.** Starting from `(s₀, T₀)` carrying `ShadedTube.ShadedUniformTubeSet s₀ T₀ N C` in
  the unit ball, `M` bridges at the sparse grid indices `q·m`, `m < M` (those with `q·m ≤ N`),
  produce a nested `(s_M, T_M)`: an index subset with tubes unchanged and shades cut, an
  `IsCRefinement` of `(s₀, T₀)` at the accumulated retention `Λ₀⁻¹ ^ M` (each bridge is an
  `L(|s_m|)⁻¹`-refinement, `L(|s_m|) ≤ Λ₀`), and, **stored relative to `|U₀|`**
  (`LocalMassClauseRel … (volume U₀)`), the clause at every index `q·m` at gain `(9261 · Λ₀)⁻¹`
  (each bridge gives `(9261 · L(|s_m|))⁻¹ ≥ (9261 · Λ₀)⁻¹`; `K₃ = 9261 = 343 · 27`,
  `L = ShadedBody.rhoTubesSection9Loss 3 · δ`). Earlier clauses are pushed down the chain by
  `LocalMassClauseRel.mono_union`. The hypothesis `hL` is the uniform bound of
  `Kakeya.VeryNotSticky.eventually_coarseLoss_absorb` over `0 < n ≤ |s₀|`; the cardinalities
  `|s_m|` stay positive because the retained mass does (`hpos`).
* `Kakeya.VeryNotSticky.exists_bridgeChain` / `exists_bridgeChain_rpow` — the chain run for
  `N / q + 1` steps, covering every index `q·m ≤ N`; in the exponent currency `Λ₀ = δ^{-ε}`, the
  retention is `(δ^ε)^{N/q+1}` and the gain `(9261 · δ^{-ε})⁻¹`.
* `Kakeya.VeryNotSticky.sparseStep` — `q := ⌊η N / 32⌋₊`, with `sparseStep_div_le`
  (`q / N ≤ η / 32`, the interpolation gap) and `div_sparseStep_le` (**the number of steps**:
  `N / q ≤ 64 / η` once `64 ≤ η N`, so `N / q + 1 ≤ 64 / η + 1`).
* `Kakeya.VeryNotSticky.localMassAt_clause_of_chainRel` — **the interpolation (step `TR`).**
  From relative clauses at the indices `q·m ≤ N` and the volume comparison `Vol ≤ Λ · |U|`,
  the clause at **every** `k ≤ N`: with `m := k / q`, `q·m ≤ k` and `(k − q·m)/N < q/N ≤ η/s`,
  so `LocalMassClauseRel.toClauseAt` then `localMassAt_clause_mono_index_rpow` give gain
  `Λ⁻¹ · G · δ^{3η/s}`.
* `Kakeya.VeryNotSticky.localMassAt_clause_of_bridgeChain` /
  `localMassAt_of_bridgeChain` — **the assembly**: chain output `(s_J, T_J)` (a
  `c_J`-refinement of the first family) and final refinement `(s*, T*)` (a `c*`-refinement of
  `(s_J, T_J)`); every stored clause transports to `(s*, T*)` with `Λ = C⁵ / (c_J · c*)`
  (T3 through `IsCRefinement.trans`), then interpolates to every grid index; with
  `Kakeya.VeryNotSticky.localMassAt_of_forall_clause_rpow` this is
  `Kakeya.VeryNotSticky.LocalMassAt δ η'' s* T*` for every `η''` above the achieved exponent.
* `Kakeya.VeryNotSticky.rpow_le_bridgeChain_gain` — **the exponent bookkeeping.** With
  `δ^a ≤ c_J · c*`, `9261 · C⁵ ≤ δ^{-b}`, `Λ₀ ≤ δ^{-ε}` and interpolation cost `δ^θ`, the gain is
  at least `δ^{a + b + ε + θ}`.
* `Kakeya.VeryNotSticky.localMassAt_half_of_bridgeChain` — **the plan's numbers**: `a = 9η'/4`, `b = η'/4`, `ε ≤ η'/4`, `θ = 3η/32`, total
  `≤ 11η'/4 + 3η/32 ≤ 7η/16 ≤ η/2` for `8η' < η`; delivers both `LocalMassAt δ (η/2)` and
  `LocalMassAt δ η`.

Nothing here is `∀ᶠ`-quantified: thresholds (`hL`, `hK`, `hgap`, `64 ≤ η N`) are hypotheses, to
be discharged by the top-level assembly (T8) by `filter_upwards`.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody
open scoped NNReal ENNReal
open Produce

/-! ### One bridge step with the step-0 hierarchy as parent map -/

/-- **One bridge step, parent map from the first family's hierarchy.** For `s ⊆ s₀` and tubes
unchanged (`(T i).toTube = (T₀ i).toTube`), the nodes `𝒱₀.tubeUniform.cover.tube k` with the
assignment `𝒱₀.tubeUniform.cover.assign k` are a legal parent map for `(s, T)` at every `k ≤ N`,
so `Kakeya.VeryNotSticky.localMassAt_clause_of_rhoTubesSection9` applies with no uniformity of
`(s, T)` itself: this is why the chain never re-uniformises. -/
theorem localMassAt_clause_of_shadedUniform_parent {ι : Type*} {δ : ℝ≥0} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {N : ℕ} {C : ℝ≥0} {s₀ : Finset ι} {T₀ : ι → ShadedTube δ E3}
    (𝒱₀ : ShadedTube.ShadedUniformTubeSet s₀ T₀ N C)
    (hball : ∀ i ∈ s₀, (T₀ i).carrier ⊆ closedBall (0 : E3) 1)
    {s : Finset ι} {T : ι → ShadedTube δ E3} (hs : s ⊆ s₀)
    (hT : ∀ i, (T i).toTube = (T₀ i).toTube) {k : ℕ} (hk : k ≤ N) :
    ∃ (s' : Finset ι) (T' : ι → ShadedTube δ E3), s' ⊆ s ∧
      (∀ i, (T' i).toTube = (T i).toTube) ∧
      (∀ i, (T' i).shade ⊆ (T i).shade) ∧
      IsCRefinement s' (fun i ↦ (T' i).toShadedBody) s (fun i ↦ (T i).toShadedBody)
        (rhoTubesSection9Loss 3 s.card δ)⁻¹ ∧
      LocalMassClauseAt δ N k
        ((9261 * rhoTubesSection9Loss 3 s.card δ : ℝ≥0) : ℝ≥0∞)⁻¹ s' T' := by
  refine localMassAt_clause_of_rhoTubesSection9 hδ hδ1 hk T (𝒱₀.tubeUniform.cover.tube k)
    (𝒱₀.tubeUniform.cover.assign k)
    (fun i hi => 𝒱₀.tubeUniform.cover.assign_mem k hk i (hs hi)) (fun i hi => ?_)
    (fun i hi => ?_)
  · have h := 𝒱₀.tubeUniform.cover.le_tube_assign k hk i (hs hi)
    change (T i).toTube.toConvexSpaceBody ≤ _
    rw [hT i]
    exact h
  · rw [show (T i).carrier = (T i).toTube.carrier from rfl, hT i]
    exact hball i (hs hi)

/-! ### The chain -/

/-- **The bridge chain, by induction on the number of steps.**

From `(s₀, T₀)` carrying `ShadedTube.ShadedUniformTubeSet s₀ T₀ N C` in the unit ball with positive
shading mass, and a uniform bound `L(n) ≤ Λ₀` on the Lemma-5.11 loss over `0 < n ≤ |s₀|`, `M`
bridges at the grid indices `q·m` (`m < M`, those with `q·m ≤ N`), each with the step-0 hierarchy
as parent map, produce `(s_M, T_M)` with

* `s_M ⊆ s₀`, tubes unchanged, shades cut;
* the accumulated retention: `IsCRefinement` of `(s₀, T₀)` at `Λ₀⁻¹ ^ M` (the honest value is
  `∏_m L(|s_m|)⁻¹ ≥ Λ₀⁻¹ ^ M`, composed by `ShadedBody.IsCRefinement.trans`);
* the clause at every index `q·m`, **relative to `|U₀|`**, at gain `(9261 · Λ₀)⁻¹` (the honest
  gain of the bridge at step `m` is `(9261 · L(|s_m|))⁻¹ ≥ (9261 · Λ₀)⁻¹`; the clause of step `m`
  is stored by `LocalMassClauseAt.toRel` with `U_{m+1} ⊆ U₀` and pushed down the chain by
  `LocalMassClauseRel.mono_union` with `U_{m+1} ⊆ U_m`).

`|s_m| > 0` at every step because `Λ₀⁻¹ ^ m · ∑_{s₀}|Y₀| ≤ ∑_{s_m}|Y_m|` and `∑_{s₀}|Y₀| > 0`;
`1 ≤ Λ₀` is read off `hL` at `n = |s₀|`. Steps with `q·m > N` do nothing. -/
theorem exists_bridgeChain_steps {ι : Type*} {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ}
    {C : ℝ≥0} {s₀ : Finset ι} {T₀ : ι → ShadedTube δ E3}
    (𝒱₀ : ShadedTube.ShadedUniformTubeSet s₀ T₀ N C)
    (hball : ∀ i ∈ s₀, (T₀ i).carrier ⊆ closedBall (0 : E3) 1)
    (hpos : 0 < ∑ i ∈ s₀, volume (T₀ i).toShadedBody.shade) {Λ₀ : ℝ≥0}
    (hL : ∀ n : ℕ, 0 < n → n ≤ s₀.card → rhoTubesSection9Loss 3 n δ ≤ Λ₀) (q M : ℕ) :
    ∃ (s : Finset ι) (T : ι → ShadedTube δ E3), s ⊆ s₀ ∧
      (∀ i, (T i).toTube = (T₀ i).toTube) ∧
      (∀ i, (T i).shade ⊆ (T₀ i).shade) ∧
      IsCRefinement s (fun i ↦ (T i).toShadedBody) s₀ (fun i ↦ (T₀ i).toShadedBody)
        (Λ₀⁻¹ ^ M) ∧
      ∀ m : ℕ, m < M → q * m ≤ N →
        LocalMassClauseRel δ N (q * m) ((9261 * Λ₀ : ℝ≥0) : ℝ≥0∞)⁻¹ s T
          (volume (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade)) := by
  classical
  -- `1 ≤ Λ₀`, read off the loss of the first family
  have hs₀ne : s₀.Nonempty := Finset.nonempty_of_sum_ne_zero hpos.ne'
  have hΛ₁ : 1 ≤ Λ₀ :=
    (one_le_rhoTubesSection9Loss 3 s₀.card δ).trans
      (hL s₀.card (Finset.card_pos.mpr hs₀ne) le_rfl)
  have hinv1 : Λ₀⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ₁
  have hinvpos : 0 < Λ₀⁻¹ := inv_pos.mpr (lt_of_lt_of_le zero_lt_one hΛ₁)
  induction M with
  | zero =>
    refine ⟨s₀, T₀, subset_rfl, fun _ => rfl, fun _ => subset_rfl, ?_,
      fun m hm => absurd hm (Nat.not_lt_zero m)⟩
    rw [pow_zero]
    exact IsCRefinement.refl _ _
  | succ M ih =>
    obtain ⟨s, T, hsub, hT, hsh, href, hcl⟩ := ih
    by_cases hkN : q * M ≤ N
    · -- the bridge at index `q * M`
      have hcM : (0 : ℝ≥0) < Λ₀⁻¹ ^ M := pow_pos hinvpos M
      have hsne : s.Nonempty := by
        refine Finset.nonempty_of_sum_ne_zero (f := fun i => volume (T i).toShadedBody.shade) ?_
        refine ne_of_gt (lt_of_lt_of_le ?_ href.2)
        exact ENNReal.mul_pos (by exact_mod_cast hcM.ne') hpos.ne'
      have hLle : rhoTubesSection9Loss 3 s.card δ ≤ Λ₀ :=
        hL s.card (Finset.card_pos.mpr hsne) (Finset.card_le_card hsub)
      obtain ⟨s', T', hsub', hT', hsh', href', hcl'⟩ :=
        localMassAt_clause_of_shadedUniform_parent hδ hδ1 𝒱₀ hball hsub hT hkN
      have hU' : (⋃ i ∈ s', (T' i).toShadedBody.shade) ⊆ ⋃ i ∈ s, (T i).toShadedBody.shade :=
        biUnion_shade_mono hsub' fun i _ => hsh' i
      have hU₀ : (⋃ i ∈ s, (T i).toShadedBody.shade) ⊆ ⋃ i ∈ s₀, (T₀ i).toShadedBody.shade :=
        biUnion_shade_mono hsub fun i _ => hsh i
      refine ⟨s', T', hsub'.trans hsub, fun i => (hT' i).trans (hT i),
        fun i => (hsh' i).trans (hsh i), ?_, ?_⟩
      · refine (href'.trans href).mono ?_
        rw [pow_succ]
        exact mul_le_mul_right (inv_anti₀ (rhoTubesSection9Loss_pos 3 _ δ) hLle) _
      · intro m hm hqm
        rcases (Nat.lt_succ_iff.mp hm).lt_or_eq with hm' | rfl
        · exact (hcl m hm' hqm).mono_union hU'
        · refine (hcl'.toRel (measure_mono (hU'.trans hU₀))).mono_gain ?_
          exact ENNReal.inv_le_inv.mpr (ENNReal.coe_le_coe.mpr (mul_le_mul_right hLle _))
    · -- the index `q * M` lies beyond the grid: nothing to do
      refine ⟨s, T, hsub, hT, hsh, href.mono ?_, ?_⟩
      · exact pow_le_pow_of_le_one zero_le hinv1 (Nat.le_succ M)
      · intro m hm hqm
        rcases (Nat.lt_succ_iff.mp hm).lt_or_eq with hm' | rfl
        · exact hcl m hm' hqm
        · exact absurd hqm hkN

/-- **The bridge chain over the whole grid (T6).** `N / q + 1` bridges at the indices `q·m`,
`m = 0, …, N / q` — every sparse index `q·m ≤ N` — from a family carrying
`ShadedTube.ShadedUniformTubeSet s₀ T₀ N C` in the unit ball: an index subset with tubes unchanged
and shades cut, an `IsCRefinement` of `(s₀, T₀)` at retention `Λ₀⁻¹ ^ (N / q + 1)`, and the clause
at every `q·m ≤ N` at gain `(9261 · Λ₀)⁻¹`, relative to `|U₀|`. -/
theorem exists_bridgeChain {ι : Type*} {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ}
    {C : ℝ≥0} {s₀ : Finset ι} {T₀ : ι → ShadedTube δ E3}
    (𝒱₀ : ShadedTube.ShadedUniformTubeSet s₀ T₀ N C)
    (hball : ∀ i ∈ s₀, (T₀ i).carrier ⊆ closedBall (0 : E3) 1)
    (hpos : 0 < ∑ i ∈ s₀, volume (T₀ i).toShadedBody.shade) {Λ₀ : ℝ≥0}
    (hL : ∀ n : ℕ, 0 < n → n ≤ s₀.card → rhoTubesSection9Loss 3 n δ ≤ Λ₀) {q : ℕ}
    (hq : 0 < q) :
    ∃ (s : Finset ι) (T : ι → ShadedTube δ E3), s ⊆ s₀ ∧
      (∀ i, (T i).toTube = (T₀ i).toTube) ∧
      (∀ i, (T i).shade ⊆ (T₀ i).shade) ∧
      IsCRefinement s (fun i ↦ (T i).toShadedBody) s₀ (fun i ↦ (T₀ i).toShadedBody)
        (Λ₀⁻¹ ^ (N / q + 1)) ∧
      ∀ m : ℕ, q * m ≤ N →
        LocalMassClauseRel δ N (q * m) ((9261 * Λ₀ : ℝ≥0) : ℝ≥0∞)⁻¹ s T
          (volume (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade)) := by
  obtain ⟨s, T, hsub, hT, hsh, href, hcl⟩ :=
    exists_bridgeChain_steps hδ hδ1 𝒱₀ hball hpos hL q (N / q + 1)
  refine ⟨s, T, hsub, hT, hsh, href, fun m hm => hcl m ?_ hm⟩
  exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq).mpr (by rwa [mul_comm]))

/-- **The chain in the exponent currency.** With the loss bound in the shape of
`Kakeya.VeryNotSticky.eventually_coarseLoss_absorb` (`L(n) ≤ δ^{-ε}`), the retention is
`(δ^ε)^{N/q+1}` and the gain `(9261 · δ^{-ε})⁻¹`. -/
theorem exists_bridgeChain_rpow {ι : Type*} {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ}
    {C : ℝ≥0} {s₀ : Finset ι} {T₀ : ι → ShadedTube δ E3}
    (𝒱₀ : ShadedTube.ShadedUniformTubeSet s₀ T₀ N C)
    (hball : ∀ i ∈ s₀, (T₀ i).carrier ⊆ closedBall (0 : E3) 1)
    (hpos : 0 < ∑ i ∈ s₀, volume (T₀ i).toShadedBody.shade) {ε : ℝ}
    (hL : ∀ n : ℕ, 0 < n → n ≤ s₀.card →
      ((rhoTubesSection9Loss 3 n δ : ℝ≥0) : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-ε)) {q : ℕ}
    (hq : 0 < q) :
    ∃ (s : Finset ι) (T : ι → ShadedTube δ E3), s ⊆ s₀ ∧
      (∀ i, (T i).toTube = (T₀ i).toTube) ∧
      (∀ i, (T i).shade ⊆ (T₀ i).shade) ∧
      IsCRefinement s (fun i ↦ (T i).toShadedBody) s₀ (fun i ↦ (T₀ i).toShadedBody)
        ((δ ^ ε) ^ (N / q + 1)) ∧
      ∀ m : ℕ, q * m ≤ N →
        LocalMassClauseRel δ N (q * m) ((9261 * δ ^ (-ε) : ℝ≥0) : ℝ≥0∞)⁻¹ s T
          (volume (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade)) := by
  have hL' : ∀ n : ℕ, 0 < n → n ≤ s₀.card → rhoTubesSection9Loss 3 n δ ≤ δ ^ (-ε) := by
    intro n hn hns
    have h := hL n hn hns
    rw [← ENNReal.coe_rpow_of_ne_zero hδ.ne'] at h
    exact ENNReal.coe_le_coe.mp h
  obtain ⟨s, T, hsub, hT, hsh, href, hcl⟩ := exists_bridgeChain hδ hδ1 𝒱₀ hball hpos hL' hq
  refine ⟨s, T, hsub, hT, hsh, ?_, hcl⟩
  rwa [NNReal.rpow_neg, inv_inv] at href

/-- The accumulated retention in the exponent currency: `(δ^ε)^M ≥ δ^a` once `ε · M ≤ a`
(for `δ ≤ 1`). With `M = N / q + 1 ≤ 64/η + 1` and `ε = η' / (4 (64/η + 2))` this is
`≥ δ^{η'/4}`. -/
theorem rpow_le_rpow_pow_of_mul_le {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε a : ℝ} {M : ℕ}
    (h : ε * M ≤ a) : δ ^ a ≤ (δ ^ ε) ^ M := by
  rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
  exact NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 h

/-! ### The sparse step and the number of steps -/

/-- **The sparse step** `q = ⌊η N / 32⌋₊` of the bridge chain: the chain visits the grid indices
`q·m ≤ N`, spaced `≈ η/32` in the exponent. -/
noncomputable def sparseStep (η : ℝ) (N : ℕ) : ℕ := ⌊η * N / 32⌋₊

/-- The sparse step is positive once `32 ≤ η N`. -/
theorem sparseStep_pos {η : ℝ} {N : ℕ} (h : 32 ≤ η * N) : 0 < sparseStep η N := by
  unfold sparseStep
  rw [Nat.floor_pos, le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
  linarith

/-- **The interpolation gap**: `q / N ≤ η / 32`. -/
theorem sparseStep_div_le {η : ℝ} {N : ℕ} (hη : 0 ≤ η) (hN : 0 < N) :
    (sparseStep η N : ℝ) / N ≤ η / 32 := by
  unfold sparseStep
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_iff₀ hN']
  calc (⌊η * N / 32⌋₊ : ℝ) ≤ η * N / 32 := Nat.floor_le (by positivity)
    _ = η / 32 * N := by ring

/-- **The number of steps**: `N / q ≤ 64 / η` once `64 ≤ η N` (so `q ≥ η N / 64`); the chain
of `exists_bridgeChain` at `q = sparseStep η N` has `N / q + 1 ≤ 64 / η + 1` steps. -/
theorem div_sparseStep_le {η : ℝ} {N : ℕ} (hη : 0 < η) (h : 64 ≤ η * N) :
    ((N / sparseStep η N : ℕ) : ℝ) ≤ 64 / η := by
  unfold sparseStep
  have hN : (N : ℝ) ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at h
    norm_num at h
  have hq : η * N / 64 ≤ (⌊η * N / 32⌋₊ : ℝ) := by
    have h1 := Nat.sub_one_lt_floor (η * N / 32)
    have h2 : η * N / 64 ≤ η * N / 32 - 1 := by linarith
    linarith
  have hqpos : (0 : ℝ) < η * N / 64 := by linarith
  calc ((N / ⌊η * N / 32⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) / (⌊η * N / 32⌋₊ : ℝ) := Nat.cast_div_le
    _ ≤ (N : ℝ) / (η * N / 64) := div_le_div_of_nonneg_left (Nat.cast_nonneg N) hqpos hq
    _ = 64 / η := by
        field_simp

/-! ### Interpolation from the sparse chain (step `TR`) -/

/-- **Interpolation from the sparse chain.** Relative clauses at the indices `q·m ≤ N`, together
with the volume comparison `Vol ≤ Λ · |U|`, give the clause at **every** `k ≤ N` at gain
`Λ⁻¹ · G · δ^{3η/s}`: with `m := k / q`, `q·m ≤ k ≤ N` and `(k − q·m)/N = (k mod q)/N < q/N ≤ η/s`,
so `LocalMassClauseRel.toClauseAt` at `q·m` followed by
`Kakeya.VeryNotSticky.localMassAt_clause_mono_index_rpow` costs one factor `δ^{3η/s}`. -/
theorem localMassAt_clause_of_chainRel {ι : Type*} {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {N q : ℕ} (hq : 0 < q) {η s : ℝ} (hgap : (q : ℝ) / N ≤ η / s) {G Vol : ℝ≥0∞}
    {s' : Finset ι} {T : ι → ShadedTube δ E3}
    (hchain : ∀ m : ℕ, q * m ≤ N → LocalMassClauseRel δ N (q * m) G s' T Vol) {Λ : ℝ≥0}
    (hvol : Vol ≤ (Λ : ℝ≥0∞) * volume (⋃ i ∈ s', (T i).toShadedBody.shade)) {k : ℕ}
    (hk : k ≤ N) :
    LocalMassClauseAt δ N k ((Λ : ℝ≥0∞)⁻¹ * G * ((δ ^ (3 * η / s) : ℝ≥0) : ℝ≥0∞)) s' T := by
  have hqm : q * (k / q) ≤ k := by
    rw [mul_comm]
    exact Nat.div_mul_le_self k q
  have h1 : LocalMassClauseAt δ N (q * (k / q)) ((Λ : ℝ≥0∞)⁻¹ * G) s' T :=
    (hchain (k / q) (hqm.trans hk)).toClauseAt hvol
  have hmod : (k : ℝ) - ((q * (k / q) : ℕ) : ℝ) = ((k % q : ℕ) : ℝ) := by
    have h : ((q * (k / q) : ℕ) : ℝ) + ((k % q : ℕ) : ℝ) = (k : ℝ) := by
      exact_mod_cast Nat.div_add_mod k q
    linarith
  have hgap' : ((k : ℝ) - ((q * (k / q) : ℕ) : ℝ)) / (N : ℝ) ≤ η / s := by
    rw [hmod]
    refine (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)).trans hgap
    exact_mod_cast (Nat.mod_lt k hq).le
  exact localMassAt_clause_mono_index_rpow hδ hδ1 hqm hgap' h1

/-- **The assembly at one index (T7).** The chain's output `(s_J, T_J)` is a `c_J`-refinement of
the first family `(s₀, T₀)` (carrying `ShadedTube.ShadedUniformTubeSet s₀ T₀ N C` in the unit
ball) with the relative clauses at the indices `q·m ≤ N`; the final refinement `(s*, T*)` is a
`c*`-refinement of `(s_J, T_J)`. Every stored clause transports to `(s*, T*)` by
`LocalMassClauseRel.mono_union` (`U* ⊆ U_J`) and the single volume comparison
`|U₀| ≤ (C⁵ / (c_J · c*)) · |U*|`, then interpolates to every `k ≤ N`: gain
`(C⁵ / (c_J c*))⁻¹ · G · δ^{3η/s}`. -/
theorem localMassAt_clause_of_bridgeChain {ι : Type*} {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {N : ℕ} {C : ℝ≥0} {s₀ sJ sF : Finset ι} {T₀ TJ TF : ι → ShadedTube δ E3}
    (𝒱₀ : ShadedTube.ShadedUniformTubeSet s₀ T₀ N C)
    (hball : ∀ i ∈ s₀, (T₀ i).carrier ⊆ closedBall (0 : E3) 1)
    {cJ cF : ℝ≥0} (hcJ : 0 < cJ) (hcF : 0 < cF)
    (hrefJ : IsCRefinement sJ (fun i ↦ (TJ i).toShadedBody) s₀ (fun i ↦ (T₀ i).toShadedBody) cJ)
    (hrefF : IsCRefinement sF (fun i ↦ (TF i).toShadedBody) sJ (fun i ↦ (TJ i).toShadedBody) cF)
    {q : ℕ} (hq : 0 < q) {η s : ℝ} (hgap : (q : ℝ) / N ≤ η / s) {G : ℝ≥0∞}
    (hchain : ∀ m : ℕ, q * m ≤ N →
      LocalMassClauseRel δ N (q * m) G sJ TJ (volume (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade)))
    {k : ℕ} (hk : k ≤ N) :
    LocalMassClauseAt δ N k
      (((C ^ 5 / (cJ * cF) : ℝ≥0) : ℝ≥0∞)⁻¹ * G * ((δ ^ (3 * η / s) : ℝ≥0) : ℝ≥0∞)) sF TF := by
  have hUF : (⋃ i ∈ sF, (TF i).toShadedBody.shade) ⊆ ⋃ i ∈ sJ, (TJ i).toShadedBody.shade :=
    biUnion_shade_mono hrefF.1.1 fun i hi => (hrefF.1.2 i hi).2
  have hchain' : ∀ m : ℕ, q * m ≤ N →
      LocalMassClauseRel δ N (q * m) G sF TF (volume (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade)) :=
    fun m hm => (hchain m hm).mono_union hUF
  exact localMassAt_clause_of_chainRel hδ hδ1 hq hgap hchain'
    (volume_biUnion_shade_le_of_shadedUniform_of_isCRefinement_trans 𝒱₀ hball hcJ hcF hrefJ
      hrefF) hk

/-- **The assembly as `Kakeya.VeryNotSticky.LocalMassAt` (T7).** On the grid of
`Kakeya.VeryNotSticky.LocalMassAt` (`N = Tube.ssfGridLen δ`), once the transported and
interpolated gain dominates `δ^{ε'}`, the field's clause holds at every exponent `η'' ≥ ε'`. -/
theorem localMassAt_of_bridgeChain {ι : Type u} {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {C : ℝ≥0} {s₀ sJ sF : Finset ι} {T₀ TJ TF : ι → ShadedTube δ E3}
    (𝒱₀ : ShadedTube.ShadedUniformTubeSet s₀ T₀ (Tube.ssfGridLen δ) C)
    (hball : ∀ i ∈ s₀, (T₀ i).carrier ⊆ closedBall (0 : E3) 1)
    {cJ cF : ℝ≥0} (hcJ : 0 < cJ) (hcF : 0 < cF)
    (hrefJ : IsCRefinement sJ (fun i ↦ (TJ i).toShadedBody) s₀ (fun i ↦ (T₀ i).toShadedBody) cJ)
    (hrefF : IsCRefinement sF (fun i ↦ (TF i).toShadedBody) sJ (fun i ↦ (TJ i).toShadedBody) cF)
    {q : ℕ} (hq : 0 < q) {η s : ℝ} (hgap : (q : ℝ) / Tube.ssfGridLen δ ≤ η / s) {G : ℝ≥0∞}
    (hchain : ∀ m : ℕ, q * m ≤ Tube.ssfGridLen δ →
      LocalMassClauseRel δ (Tube.ssfGridLen δ) (q * m) G sJ TJ
        (volume (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade)))
    {ε' η'' : ℝ}
    (hgain : (δ : ℝ≥0∞) ^ ε' ≤
      ((C ^ 5 / (cJ * cF) : ℝ≥0) : ℝ≥0∞)⁻¹ * G * ((δ ^ (3 * η / s) : ℝ≥0) : ℝ≥0∞))
    (hε : ε' ≤ η'') :
    LocalMassAt δ η'' sF TF :=
  localMassAt_of_forall_clause_rpow hδ1 hε fun _ hk =>
    (localMassAt_clause_of_bridgeChain hδ hδ1 𝒱₀ hball hcJ hcF hrefJ hrefF hq hgap hchain
      hk).mono_gain hgain

/-! ### The exponent bookkeeping -/

/-- **The gain in the exponent currency.** With the total retention `c ≥ δ^a`, the δ-free constant
absorbed as `9261 · C⁵ ≤ δ^{-b}`, the chain's loss bound `Λ₀ ≤ δ^{-ε}` and the interpolation cost
`δ^θ`, the transported and interpolated gain
`(C⁵/c)⁻¹ · (9261 Λ₀)⁻¹ · δ^θ = c · δ^θ / (9261 · C⁵ · Λ₀)` is at least `δ^{a + b + ε + θ}`.
(If `C = 0` or `Λ₀ = 0` the gain is `⊤`.) -/
theorem rpow_le_bridgeChain_gain {δ : ℝ≥0} (hδ : 0 < δ) {C Λ₀ c : ℝ≥0} {a b ε θ : ℝ}
    (hc : δ ^ a ≤ c) (hK : 9261 * C ^ 5 ≤ δ ^ (-b)) (hΛ : Λ₀ ≤ δ ^ (-ε)) :
    (δ : ℝ≥0∞) ^ (a + b + ε + θ) ≤
      ((C ^ 5 / c : ℝ≥0) : ℝ≥0∞)⁻¹ * ((9261 * Λ₀ : ℝ≥0) : ℝ≥0∞)⁻¹ *
        ((δ ^ θ : ℝ≥0) : ℝ≥0∞) := by
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hc0 : c ≠ 0 := (lt_of_lt_of_le (NNReal.rpow_pos hδ) hc).ne'
  have hθ0 : ((δ ^ θ : ℝ≥0) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NNReal.rpow_pos hδ).ne'
  rcases eq_or_ne C 0 with hC | hC
  · have htop : ((C ^ 5 / c : ℝ≥0) : ℝ≥0∞)⁻¹ = ⊤ := by simp [hC]
    rw [htop, ENNReal.top_mul (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top), ENNReal.top_mul hθ0]
    exact le_top
  rcases eq_or_ne Λ₀ 0 with hΛ0 | hΛ0
  · have htop : ((9261 * Λ₀ : ℝ≥0) : ℝ≥0∞)⁻¹ = ⊤ := by simp [hΛ0]
    rw [htop, ENNReal.mul_top (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top), ENNReal.top_mul hθ0]
    exact le_top
  have hCc : (C ^ 5 / c : ℝ≥0) ≠ 0 := div_ne_zero (pow_ne_zero 5 hC) hc0
  have h9 : (9261 * Λ₀ : ℝ≥0) ≠ 0 := mul_ne_zero (by norm_num) hΛ0
  rw [← ENNReal.coe_inv hCc, ← ENNReal.coe_inv h9, ← ENNReal.coe_mul, ← ENNReal.coe_mul,
    ← ENNReal.coe_rpow_of_ne_zero hδ0]
  apply ENNReal.coe_le_coe.mpr
  have hb : δ ^ b * (9261 * C ^ 5) ≤ 1 := by
    calc δ ^ b * (9261 * C ^ 5) ≤ δ ^ b * δ ^ (-b) := mul_le_mul_right hK _
      _ = 1 := by rw [← NNReal.rpow_add hδ0]; simp
  have he : δ ^ ε * Λ₀ ≤ 1 := by
    calc δ ^ ε * Λ₀ ≤ δ ^ ε * δ ^ (-ε) := mul_le_mul_right hΛ _
      _ = 1 := by rw [← NNReal.rpow_add hδ0]; simp
  have hkey : δ ^ a * δ ^ b * δ ^ ε * (9261 * C ^ 5 * Λ₀) ≤ c := by
    calc δ ^ a * δ ^ b * δ ^ ε * (9261 * C ^ 5 * Λ₀)
        = δ ^ a * ((δ ^ b * (9261 * C ^ 5)) * (δ ^ ε * Λ₀)) := by ring
      _ ≤ c * (1 * 1) := by gcongr
      _ = c := by ring
  have hpos9 : (0 : ℝ≥0) < 9261 * C ^ 5 * Λ₀ := by
    have hC' : 0 < C := pos_iff_ne_zero.mpr hC
    have hΛ' : 0 < Λ₀ := pos_iff_ne_zero.mpr hΛ0
    positivity
  calc δ ^ (a + b + ε + θ) = δ ^ a * δ ^ b * δ ^ ε * δ ^ θ := by
        rw [NNReal.rpow_add hδ0, NNReal.rpow_add hδ0, NNReal.rpow_add hδ0]
    _ ≤ c / (9261 * C ^ 5 * Λ₀) * δ ^ θ := by
        gcongr
        exact (le_div_iff₀ hpos9).mpr hkey
    _ = (C ^ 5 / c)⁻¹ * (9261 * Λ₀)⁻¹ * δ ^ θ := by
        congr 1
        rw [inv_div, div_eq_mul_inv c (C ^ 5), mul_assoc c (C ^ 5)⁻¹ (9261 * Λ₀)⁻¹, ← mul_inv,
          ← div_eq_mul_inv]
        congr 1
        ring

/-- Two retentions in the exponent currency compose: `δ^{a₁} ≤ c₁`, `δ^{a₂} ≤ c₂` give
`δ^{a₁ + a₂} ≤ c₁ · c₂` (the shape of `ShadedBody.IsCRefinement.trans`). -/
theorem rpow_add_le_mul {δ : ℝ≥0} (hδ : 0 < δ) {a₁ a₂ : ℝ} {c₁ c₂ : ℝ≥0} (h₁ : δ ^ a₁ ≤ c₁)
    (h₂ : δ ^ a₂ ≤ c₂) : δ ^ (a₁ + a₂) ≤ c₁ * c₂ := by
  rw [NNReal.rpow_add hδ.ne']
  exact mul_le_mul' h₁ h₂

/-- **The exponent budget of the chain, written out.** Retention
`9η'/4` (chain `η'/4` + class-dense `2η'`), δ-free constant `η'/4`, per-bridge loss `ε ≤ η'/4`,
interpolation `3η/32`: the total is at most `11η'/4 + 3η/32 ≤ 11η/32 + 3η/32 = 7η/16`, and
`7η/16 ≤ η/2`, for every `η'` with `8η' < η`. -/
theorem bridgeChain_exponent_le {η η' ε : ℝ} (hη' : 0 < η') (h8 : 8 * η' < η)
    (hε : ε ≤ η' / 4) :
    9 * η' / 4 + η' / 4 + ε + 3 * η / 32 ≤ 7 * η / 16 ∧ 7 * η / 16 ≤ η / 2 :=
  ⟨by linarith, by linarith⟩

/-- **The plan's numbers, both slack forms.** On the grid of
`Kakeya.VeryNotSticky.LocalMassAt`, with `q` the sparse step (`q / N ≤ η / 32`), the chain's loss
bound `Λ₀ ≤ δ^{-ε}` at `ε ≤ η'/4`, the total retention `c_J · c* ≥ δ^{9η'/4}` and the δ-free
constant absorbed as `9261 · C⁵ ≤ δ^{-η'/4}`: the gain is at least
`δ^{9η'/4 + η'/4 + ε + 3η/32} ≥ δ^{11η'/4 + 3η/32}`, and `11η'/4 + 3η/32 ≤ 7η/16 ≤ η/2` for
`8η' < η`. Hence `LocalMassAt δ (η/2) s* T*`, and `LocalMassAt δ η s* T*`. -/
theorem localMassAt_half_of_bridgeChain {ι : Type u} {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {C : ℝ≥0} {s₀ sJ sF : Finset ι} {T₀ TJ TF : ι → ShadedTube δ E3}
    (𝒱₀ : ShadedTube.ShadedUniformTubeSet s₀ T₀ (Tube.ssfGridLen δ) C)
    (hball : ∀ i ∈ s₀, (T₀ i).carrier ⊆ closedBall (0 : E3) 1)
    {cJ cF : ℝ≥0} (hcJ : 0 < cJ) (hcF : 0 < cF)
    (hrefJ : IsCRefinement sJ (fun i ↦ (TJ i).toShadedBody) s₀ (fun i ↦ (T₀ i).toShadedBody) cJ)
    (hrefF : IsCRefinement sF (fun i ↦ (TF i).toShadedBody) sJ (fun i ↦ (TJ i).toShadedBody) cF)
    {η η' ε : ℝ} (hη' : 0 < η') (h8 : 8 * η' < η) (hε : ε ≤ η' / 4)
    {q : ℕ} (hq : 0 < q) (hgap : (q : ℝ) / Tube.ssfGridLen δ ≤ η / 32) {Λ₀ : ℝ≥0}
    (hΛ : Λ₀ ≤ δ ^ (-ε)) (hc : δ ^ (9 * η' / 4) ≤ cJ * cF)
    (hK : 9261 * C ^ 5 ≤ δ ^ (-(η' / 4)))
    (hchain : ∀ m : ℕ, q * m ≤ Tube.ssfGridLen δ →
      LocalMassClauseRel δ (Tube.ssfGridLen δ) (q * m) ((9261 * Λ₀ : ℝ≥0) : ℝ≥0∞)⁻¹ sJ TJ
        (volume (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade))) :
    LocalMassAt δ (η / 2) sF TF ∧ LocalMassAt δ η sF TF := by
  have hgain := rpow_le_bridgeChain_gain (θ := 3 * η / 32) hδ hc hK hΛ
  obtain ⟨hbudget, hhalf⟩ := bridgeChain_exponent_le hη' h8 hε
  have hη : 0 ≤ η := by linarith
  have hexp : 9 * η' / 4 + η' / 4 + ε + 3 * η / 32 ≤ η / 2 := hbudget.trans hhalf
  have hexp' : 9 * η' / 4 + η' / 4 + ε + 3 * η / 32 ≤ η := hexp.trans (by linarith)
  exact ⟨localMassAt_of_bridgeChain hδ hδ1 𝒱₀ hball hcJ hcF hrefJ hrefF hq hgap hchain hgain hexp,
    localMassAt_of_bridgeChain hδ hδ1 𝒱₀ hball hcJ hcF hrefJ hrefF hq hgap hchain hgain hexp'⟩

end Kakeya.VeryNotSticky
