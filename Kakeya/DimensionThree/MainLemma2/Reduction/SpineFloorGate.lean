/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.BiasedDensity
public import Kakeya.Factorization
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountFloorObstruction

/-!
# The count-floor gate : density ⇒ count, unrestricted

Two facts the count-floor derivation would use in place of the biased factorization.

* `densityIn_mul_volume_le_card_mul` (G1): if every member of `𝕍` has volume at most `v`, then
  `Δ(𝕍, W) · |W| ≤ #{i ∈ 𝕍 | V i ≤ W} · v` — the density inside a test body is paid by the
  members contained in it, so a density bound converts into a count bound.
* `exists_biasedMaximizer_densityIn_ge` (G2′): for `ϖ > 0` and a family of positive-volume bodies
  inside `U`, some hull `W = conv (⋃ i ∈ t, V i)` with `t ⊆ 𝕍` nonempty satisfies
  `(|W|/|U|)^ϖ · Δ_max(𝕍) ≤ Δ(𝕍, W)`.  This is the maximizer of `Kakeya.maxBiasedDensity` taken
  over the *whole* family: no pigeonholing, no retained subfamily, no constant.
  `exists_biasedMaximizer_card_ge` combines the two.

The companion leaf `SpineFloorGateRed` shows that the *retained* subfamily of
`nonempty_biasedFactorization` does not in general keep `Δ_max` (probe G3 of the blueprint is red);
the unrestricted form here is the only density ⇒ count route the biased device supports.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-! ## G1: density in a body gives a count -/

/-- **G1.**  The members of `𝕍` inside `W` carry the mass `Δ(𝕍, W) · |W|`; with each member of
volume at most `v`, their number is at least that mass divided by `v`.  Stated multiplicatively,
in `ℝ≥0∞`, with no side condition. -/
theorem densityIn_mul_volume_le_card_mul (𝕍 : Finset ι) (V : ι → ConvexSpaceBody E)
    (W : ConvexSpaceBody E) {v : ENNReal} (hv : ∀ i ∈ 𝕍, volume (V i).carrier ≤ v) :
    Kakeya.densityIn 𝕍 V W * volume W.carrier
      ≤ (({i ∈ 𝕍 | V i ≤ W} : Finset ι).card : ENNReal) * v := by
  classical
  rw [← Kakeya.sum_volume_eq_densityIn_mul_volume]
  have h := Finset.sum_le_sum (s := ({i ∈ 𝕍 | V i ≤ W} : Finset ι))
    (f := fun i => volume (V i).carrier) (g := fun _ => v)
    (fun i hi => hv i (Finset.mem_filter.mp hi).1)
  rwa [Finset.sum_const, nsmul_eq_mul] at h

/-- G1 for the whole family: the count of `𝕍` itself dominates the count of the members in `W`. -/
theorem densityIn_mul_volume_le_card_mul' (𝕍 : Finset ι) (V : ι → ConvexSpaceBody E)
    (W : ConvexSpaceBody E) {v : ENNReal} (hv : ∀ i ∈ 𝕍, volume (V i).carrier ≤ v) :
    Kakeya.densityIn 𝕍 V W * volume W.carrier ≤ (𝕍.card : ENNReal) * v := by
  refine (densityIn_mul_volume_le_card_mul 𝕍 V W hv).trans ?_
  have hsub : ({i ∈ 𝕍 | V i ≤ W} : Finset ι) ⊆ 𝕍 := Finset.filter_subset _ _
  exact mul_le_mul' (by exact_mod_cast Finset.card_le_card hsub) le_rfl

/-! ## G2′: the unrestricted biased maximizer -/

/-- **G2′ — the biased maximizer, with no pigeonholing and no constant.**

For a family `𝕍` of bodies inside `U` with a member of positive volume, the subfamily `t*`
maximizing the biased score (`Kakeya.scoreMaximizer`) has hull `W` with
`(|W|/|U|)^ϖ · Δ_max(𝕍) ≤ Δ(𝕍, W)`.  This is the one inequality of GWZ Lemma 9.2 that the
count floor's derivation needs, and it holds for the **original** family: no subfamily is
selected, so the profile-drop alternative (D) of the refined `lem:ml2-window-refinement` is never
triggered by this step.  Proof: `Kakeya.rpow_mul_maxDensity_le_maxBiasedDensity` gives
`|U|^{-ϖ} Δ_max ≤ σ_ϖ(t*) = Σ_{t*}|V| / |W|^{1+ϖ}`, and `Σ_{t*}|V| ≤ Σ_{𝕍[W]}|V| = Δ(𝕍,W)|W|`
since every member of `t*` lies in its own hull. -/
theorem exists_biasedMaximizer_densityIn_ge {𝕍 : Finset ι} {V : ι → ConvexSpaceBody E}
    {ϖ : ℝ} (hϖ : 0 < ϖ) (hpos : ∃ i ∈ 𝕍, 0 < volume (V i).carrier)
    {U : ConvexSpaceBody E} (hVU : ∀ i ∈ 𝕍, V i ≤ U) :
    ∃ t ⊆ 𝕍, t.Nonempty ∧
      (volume (t.convexHull_biUnion V).carrier / volume U.carrier) ^ ϖ * Kakeya.maxDensity 𝕍 V
        ≤ Kakeya.densityIn 𝕍 V (t.convexHull_biUnion V) := by
  classical
  set t := Kakeya.scoreMaximizer (Kakeya.biasedScore V ϖ) 𝕍 with ht_def
  have htsub : t ⊆ 𝕍 := Kakeya.scoreMaximizer_subset _ _
  have hUtop : volume U.carrier ≠ ∞ := U.isCompact.measure_ne_top
  obtain ⟨i₀, hi₀, hv₀⟩ := hpos
  have hUpos : 0 < volume U.carrier :=
    hv₀.trans_le (measure_mono (SetLike.coe_subset_coe.mpr (hVU i₀ hi₀)))
  have hΔpos : 0 < Kakeya.maxDensity 𝕍 V :=
    lt_of_lt_of_le zero_lt_one (Kakeya.one_le_maxDensity ⟨i₀, hi₀, hv₀⟩)
  have hkey : volume U.carrier ^ (-ϖ) * Kakeya.maxDensity 𝕍 V ≤ Kakeya.biasedScore V ϖ t :=
    Kakeya.rpow_mul_maxDensity_le_maxBiasedDensity hϖ ⟨i₀, hi₀, hv₀⟩ hVU
  have hlhs_pos : 0 < volume U.carrier ^ (-ϖ) * Kakeya.maxDensity 𝕍 V :=
    ENNReal.mul_pos (ENNReal.rpow_pos hUpos hUtop).ne' hΔpos.ne'
  -- the maximizer is nonempty (the empty score is `0`)
  have htne : t.Nonempty := by
    rcases t.eq_empty_or_nonempty with h | h
    · exfalso
      have : Kakeya.biasedScore V ϖ t = 0 := by simp [h, Kakeya.biasedScore]
      rw [this] at hkey
      exact absurd hkey (not_le.mpr hlhs_pos)
    · exact h
  refine ⟨t, htsub, htne, ?_⟩
  set W := t.convexHull_biUnion V with hW_def
  have hWcar : W.carrier = Convexity.convexHull ℝ (⋃ i ∈ t, (V i).carrier) :=
    htne.convexHull_biUnion_carrier V
  have hWtop : volume W.carrier ≠ ∞ := W.isCompact.measure_ne_top
  -- the biased score of `t`, with the hull named
  have hscore : Kakeya.biasedScore V ϖ t
      = (∑ i ∈ t, volume (V i).carrier) / volume W.carrier ^ (1 + ϖ) := by
    simp only [Kakeya.biasedScore, hWcar]
  -- the members of `t` lie in `W`, so their mass is at most `Δ(𝕍, W) · |W|`
  have htW : ∀ i ∈ t, V i ≤ W := fun i hi => Finset.le_convexHull_biUnion V hi
  have hsum : ∑ i ∈ t, volume (V i).carrier ≤ Kakeya.densityIn 𝕍 V W * volume W.carrier := by
    rw [← Kakeya.sum_volume_eq_densityIn_mul_volume]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => zero_le)
    intro i hi
    exact Finset.mem_filter.mpr ⟨htsub hi, htW i hi⟩
  -- `|W| > 0`: otherwise the score is `0`, against `hkey`
  have hsumpos : 0 < ∑ i ∈ t, volume (V i).carrier := by
    by_contra h0
    have h0' : ∑ i ∈ t, volume (V i).carrier = 0 := le_antisymm (not_lt.mp h0) zero_le
    have : Kakeya.biasedScore V ϖ t = 0 := by rw [hscore, h0', ENNReal.zero_div]
    rw [this] at hkey
    exact absurd hkey (not_le.mpr hlhs_pos)
  have hWpos : 0 < volume W.carrier := by
    by_contra h0
    have hW0 : volume W.carrier = 0 := le_antisymm (not_lt.mp h0) zero_le
    have : ∑ i ∈ t, volume (V i).carrier = 0 :=
      Finset.sum_eq_zero fun i hi =>
        measure_mono_null (SetLike.coe_subset_coe.mpr (htW i hi)) hW0
    exact absurd this hsumpos.ne'
  have hWϖ0 : volume W.carrier ^ ϖ ≠ 0 := (ENNReal.rpow_pos hWpos hWtop).ne'
  have hWϖtop : volume W.carrier ^ ϖ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hϖ.le hWtop
  -- `|U|^{-ϖ} Δ_max ≤ Δ(𝕍,W)·|W| / |W|^{1+ϖ} = Δ(𝕍,W) / |W|^ϖ`
  have h1 : volume U.carrier ^ (-ϖ) * Kakeya.maxDensity 𝕍 V
      ≤ Kakeya.densityIn 𝕍 V W * volume W.carrier / volume W.carrier ^ (1 + ϖ) := by
    calc volume U.carrier ^ (-ϖ) * Kakeya.maxDensity 𝕍 V
        ≤ Kakeya.biasedScore V ϖ t := hkey
      _ = (∑ i ∈ t, volume (V i).carrier) / volume W.carrier ^ (1 + ϖ) := hscore
      _ ≤ Kakeya.densityIn 𝕍 V W * volume W.carrier / volume W.carrier ^ (1 + ϖ) :=
          ENNReal.div_le_div_right hsum _
  have h2 : Kakeya.densityIn 𝕍 V W * volume W.carrier / volume W.carrier ^ (1 + ϖ)
      = Kakeya.densityIn 𝕍 V W / volume W.carrier ^ ϖ := by
    rw [ENNReal.rpow_add _ _ hWpos.ne' hWtop, ENNReal.rpow_one, mul_comm (volume W.carrier),
      ENNReal.mul_div_mul_right _ _ hWpos.ne' hWtop]
  have h3 : volume W.carrier ^ ϖ * (volume U.carrier ^ (-ϖ) * Kakeya.maxDensity 𝕍 V)
      ≤ Kakeya.densityIn 𝕍 V W := by
    rw [h2] at h1
    rw [mul_comm]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hWϖ0) (Or.inl hWϖtop)).mp h1
  calc (volume W.carrier / volume U.carrier) ^ ϖ * Kakeya.maxDensity 𝕍 V
      = volume W.carrier ^ ϖ * (volume U.carrier ^ (-ϖ) * Kakeya.maxDensity 𝕍 V) := by
        rw [ENNReal.div_rpow_of_nonneg _ _ hϖ.le, ENNReal.rpow_neg, div_eq_mul_inv]
        ring
    _ ≤ Kakeya.densityIn 𝕍 V W := h3

/-- **G1 ∘ G2′: the biased maximizer counts.**  With every member of volume at most `v`, the
members of `𝕍` inside the biased maximizer's hull `W` number at least
`(|W|/|U|)^ϖ · Δ_max(𝕍) · |W| / v` — the count floor's engine, on the **unrestricted** family. -/
theorem exists_biasedMaximizer_card_ge {𝕍 : Finset ι} {V : ι → ConvexSpaceBody E}
    {ϖ : ℝ} (hϖ : 0 < ϖ) (hpos : ∃ i ∈ 𝕍, 0 < volume (V i).carrier)
    {U : ConvexSpaceBody E} (hVU : ∀ i ∈ 𝕍, V i ≤ U)
    {v : ENNReal} (hv : ∀ i ∈ 𝕍, volume (V i).carrier ≤ v) :
    ∃ t ⊆ 𝕍, t.Nonempty ∧
      (volume (t.convexHull_biUnion V).carrier / volume U.carrier) ^ ϖ * Kakeya.maxDensity 𝕍 V
          * volume (t.convexHull_biUnion V).carrier
        ≤ (({i ∈ 𝕍 | V i ≤ t.convexHull_biUnion V} : Finset ι).card : ENNReal) * v := by
  classical
  obtain ⟨t, hts, htne, hden⟩ := exists_biasedMaximizer_densityIn_ge hϖ hpos hVU
  refine ⟨t, hts, htne, ?_⟩
  calc (volume (t.convexHull_biUnion V).carrier / volume U.carrier) ^ ϖ * Kakeya.maxDensity 𝕍 V
          * volume (t.convexHull_biUnion V).carrier
      ≤ Kakeya.densityIn 𝕍 V (t.convexHull_biUnion V)
          * volume (t.convexHull_biUnion V).carrier := by gcongr
    _ ≤ _ := densityIn_mul_volume_le_card_mul 𝕍 V _ hv

end Kakeya.ML2Core

end
