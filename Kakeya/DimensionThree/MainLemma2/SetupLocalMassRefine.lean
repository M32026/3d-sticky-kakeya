/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ShadeClassBandDense

/-!
# The uniformisation step and the re-tuned class-dense refinement

The multi-scale chain for `Kakeya.VeryNotSticky.LocalMassRefinementResidue` (GWZ (87)) has the
shape *uniformise once → a constant number of one-scale bridges → one class-dense refinement*.
This file supplies the two families the chain is built between, as two `∀ᶠ` lemmas
parametrised in the exponents `(η, η', η_f)`, where `δ ^ η_f` is the fullness of the *input*
family (`η_f = η` for the first step, `η_f = η + 2 η'` after the bridges have spent their loss).

* **Step U — `eventually_exists_uniformBand`.** The density band of
  `Kakeya.VeryNotSticky.exists_shadingBand` at the Markov floor `θ = δ ^ (2η - η')` (twice the
  floor used by `eventually_exists_classDenseRefinement`) with Markov fraction
  `q = δ ^ (η - 3η')`, followed by GWZ Definition 2.2 uniformisation
  (`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`) at both losses `η'/2`. Output: a
  subfamily `(s₀, T₀)` (tubes unchanged, shades cut) carrying
  `ShadedTube.ShadedUniformTubeSet s₀ T₀ (Tube.ssfGridLen δ) (ShadedTube.ssfUniformConst 3)` — the
  **δ-free** constant of the first family, which is what the C⁵ volume comparison of
  `SetupLocalMassTransport` consumes — together with the `IsCRefinement` at retention
  `δ ^ (3η'/2)`, and the band data `P = λ |T|` in the form the class-dense selection needs:
  `2 δ^{2η} |T| ≤ δ^{η'} P`, `|Y₀(i)| ≤ 2P`, and `δ^{η'/2} · #s₀ · P ≤ 2 ∑_{s₀} |Y₀|`.
* **Step CD — `eventually_exists_classDenseRefinement_slack`.** Step U followed by the
  class-dense heavy selection `ShadedTube.exists_denseSelection` at floor `t = δ^{η'} P`, light
  threshold `2t`, node threshold `θ' = δ^{η'/2}/(32(N+1))`. Output: GWZ Definition 2.2 at a capped
  constant `1 ≤ C₀ ≤ δ^{-η'}`, the per-tube floor **`2 · δ^{2η} |T| ≤ |Y'(i)|`** (the side-data
  plan's slack, doubled against `eventually_exists_classDenseRefinement`), and the
  `IsCRefinement` at retention `δ ^ (2η')`.

**Admissibility.** Both lemmas need exactly `0 < η'`, `3 η' < η`, `η ≤ 1` and `η_f ≤ η + 2 η'`:
`3η' < η` makes the Markov fraction `δ^{η - 3η'}` eventually `≤ 1/2`, `η_f ≤ η + 2η'` is the
Markov inequality `θ ≤ q · δ^{η_f}`, and `η ≤ 1` is what
`Kakeya.VNSUniform.card_le_rpow_neg_four_enn` needs for `#s ≤ δ^{-4}`. In particular the
assembly's `8 η' < η` (and a fortiori `16 η' < η`) suffices at both call sites `η_f = η` and
`η_f = η + 2η'`. No hypothesis `η ≤ η_f` is needed.
`eventually_exists_classDenseRefinement_of_slack` re-derives the statement of
`eventually_exists_classDenseRefinement` from step CD at `η_f = η` as a consistency check; the
original declaration is untouched.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube
open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

open Topology Filter

universe u

/-- `maxDensity` is monotone under index selection with the tubes unchanged. -/
theorem maxDensity_le_of_subset_of_tube_eq {ι : Type*} {δ : NNReal} {s s' : Finset ι}
    {T T' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hs : s' ⊆ s)
    (htube : ∀ i, (T' i).toTube = (T i).toTube) :
    maxDensity s' (fun i ↦ (T' i).toConvexSpaceBody) ≤
      maxDensity s (fun i ↦ (T i).toConvexSpaceBody) := by
  have h : (fun i ↦ (T' i).toConvexSpaceBody) = fun i ↦ (T i).toConvexSpaceBody := by
    funext i; exact congrArg Tube.toConvexSpaceBody (htube i)
  rw [h]
  exact Kakeya.maxDensity_mono _ hs

/-- A positive fullness lower bound forces a positive total shade mass. -/
theorem sum_volume_shade_pos_of_rpow_le_fullness {ι : Type*} {δ : NNReal} (hδ0 : 0 < δ)
    {s : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {a : ℝ}
    (hfull : δ ^ a ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody)) :
    0 < ∑ i ∈ s, volume (T i).shade :=
  pos_iff_ne_zero.mpr (ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos s
    (fun i ↦ (T i).toShadedBody) (lt_of_lt_of_le (NNReal.rpow_pos hδ0) hfull))

/-- **The band pigeonhole's refinement constant at the doubled floor beats `δ^{η'/4}`.**  At
floor `δ^{2η-η'}` and any Markov fraction `q ≤ 1/2`, the constant of
`Kakeya.VeryNotSticky.exists_shadingBand` is at least `(1/2) · (1 + (2η-η') log₂(1/δ))⁻¹`, and a
power beats the logarithm (`hlog` is the clause of `eventually_rpow_mul_add_log_le` used by
`denseBand_const_ge`; the logarithm here is one smaller than there). -/
theorem denseBand_const_ge_slack {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {η η' : ℝ}
    (hηη' : η' ≤ 2 * η) {q : NNReal} (hq : q ≤ 1 / 2)
    (hlog : (δ : ℝ) ^ (η' / 4) * (2 + ((2 * η - η') / Real.log 2) * Real.log (1 / (δ : ℝ)))
      ≤ 1 / 2) :
    δ ^ (η' / 4) ≤ (1 - q) *
      ((1 + Real.logb 2 (((δ ^ (2 * η - η') : NNReal) : ℝ)⁻¹)).toNNReal)⁻¹ := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1δ : 0 ≤ Real.log (1 / (δ : ℝ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδR]; linarith
  -- the logarithm of the inverse floor
  set X : ℝ := 1 + Real.logb 2 (((δ ^ (2 * η - η') : NNReal) : ℝ)⁻¹) with hX
  have hXeq : X = 1 + ((2 * η - η') / Real.log 2) * Real.log (1 / (δ : ℝ)) := by
    rw [hX]
    have hcoe : (((δ ^ (2 * η - η') : NNReal) : ℝ)⁻¹) = (1 / (δ : ℝ)) ^ (2 * η - η') := by
      rw [NNReal.coe_rpow, one_div, Real.inv_rpow hδR.le]
    rw [hcoe, Real.logb_rpow_eq_mul_logb_of_pos (by positivity), Real.logb, div_eq_mul_inv]
    ring
  have hX1 : 1 ≤ X := by
    rw [hXeq]
    have : 0 ≤ ((2 * η - η') / Real.log 2) * Real.log (1 / (δ : ℝ)) := by
      apply mul_nonneg _ hlog1δ
      apply div_nonneg _ hlog2.le
      linarith
    linarith
  have hXpos : 0 < X := by linarith
  have hXnn : (X.toNNReal : ℝ) = X := Real.coe_toNNReal X hXpos.le
  have hXne : X.toNNReal ≠ 0 := by
    intro h
    have := congrArg (fun y : NNReal => (y : ℝ)) h
    simp only [hXnn, NNReal.coe_zero] at this
    linarith
  -- the Markov fraction is at most `1/2`
  have hhalf : (1 / 2 : NNReal) ≤ 1 - q := by
    have h2 : q + 1 / 2 ≤ 1 := by
      calc q + 1 / 2 ≤ 1 / 2 + 1 / 2 := by gcongr
        _ = 1 := by norm_num
    exact le_tsub_of_add_le_left h2
  -- the key inequality in `NNReal`
  have hkey : δ ^ (η' / 4) ≤ (1 / 2 : NNReal) * (X.toNNReal)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (pos_iff_ne_zero.mpr hXne)]
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow, hXnn, hXeq]
    push_cast
    have hδε : (0 : ℝ) ≤ (δ : ℝ) ^ (η' / 4) := by positivity
    calc (δ : ℝ) ^ (η' / 4) * (1 + ((2 * η - η') / Real.log 2) * Real.log (1 / (δ : ℝ)))
        ≤ (δ : ℝ) ^ (η' / 4) * (2 + ((2 * η - η') / Real.log 2) * Real.log (1 / (δ : ℝ))) := by
          gcongr; norm_num
      _ ≤ 1 / 2 := hlog
  exact hkey.trans (mul_le_mul_of_nonneg_right hhalf zero_le)

/-- **Step U of the chain: the band and the uniformisation, extracted with the fullness exponent
parametrised**.

From the binders `hball`, `hmax` (at `δ^{-η}`) and a fullness `δ^{η_f} ≤ λ(s, T)`, the density
band at the Markov floor `δ^{2η-η'}` with fraction `δ^{η-3η'}` followed by GWZ Definition 2.2
uniformisation at both losses `η'/2` gives a subfamily `(s₀, T₀)` — tubes unchanged, shades cut —
with

* the Definition 2.2 bundle at the **δ-free** constant `ShadedTube.ssfUniformConst 3`;
* the `IsCRefinement` at retention `δ^{3η'/2}` (the honest value is `δ^{5η'/4}/8`), also in the
  cleared mass form;
* the band datum `P = λ |T|` with `P ≠ ⊤`, the floor `2 δ^{2η} |T| ≤ δ^{η'} P`, the per-tube cap
  `|Y₀(i)| ≤ 2P`, and `δ^{η'/2} · #s₀ · P ≤ 2 ∑_{s₀} |Y₀|` — exactly the inputs of the class-dense
  selection at floor `t = δ^{η'} P`.

Admissibility: `0 < η'`, `3η' < η`, `η ≤ 1`, `η_f ≤ η + 2η'`. -/
theorem eventually_exists_uniformBand {η η' η_f : ℝ} (hη' : 0 < η') (h3 : 3 * η' < η)
    (hη1 : η ≤ 1) (hf : η_f ≤ η + 2 * η') :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        δ ^ η_f ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) →
        ∃ s₀ ⊆ s, ∃ T₀ : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)),
          (∀ i, (T₀ i).toTube = (T i).toTube) ∧
          (∀ i, (T₀ i).shade ⊆ (T i).shade) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s₀ T₀ (Tube.ssfGridLen δ)
            (ShadedTube.ssfUniformConst 3)) ∧
          ShadedBody.IsCRefinement s₀ (fun i ↦ (T₀ i).toShadedBody) s
            (fun i ↦ (T i).toShadedBody) (δ ^ (3 * η' / 2)) ∧
          (δ : ENNReal) ^ (3 * η' / 2) * ∑ i ∈ s, volume (T i).shade
            ≤ ∑ i ∈ s₀, volume (T₀ i).shade ∧
          ∃ P : ENNReal, P ≠ ⊤ ∧
            (∀ i ∈ s₀, 2 * (δ : ENNReal) ^ (2 * η) * volume (T₀ i).carrier
              ≤ (δ : ENNReal) ^ η' * P) ∧
            (∀ i ∈ s₀, volume (T₀ i).shade ≤ 2 * P) ∧
            (δ : ENNReal) ^ (η' / 2) * ((s₀.card : ENNReal) * P)
              ≤ 2 * ∑ i ∈ s₀, volume (T₀ i).shade := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  obtain ⟨δ₁, hδ₁pos, -, Hssf⟩ := ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf.{u}
    (E := EuclideanSpace ℝ (Fin 3)) 4 (η' / 2) (η' / 2) (by linarith) (by linarith)
  have hle₁ : ∀ᶠ d : NNReal in 𝓝[>] 0, d ≤ δ₁ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ₁pos)] with d hd
    exact le_of_lt hd
  set C : NNReal := ShadedTube.ssfUniformConst 3 with hC
  filter_upwards [Kakeya.VNSUniform.eventually_card_thresholds', hle₁,
    eventually_rpow_mul_add_log_le (by linarith : 0 < η' / 4) 2 ((2 * η - η') / Real.log 2)
      (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_nnreal_mul_rpow_le_const 1 (1 / 2) (by norm_num) (by linarith : 0 < η - 3 * η'),
    eventually_nnreal_mul_rpow_le_const 8 1 (by norm_num) (by linarith : 0 < η' / 4)]
    with δ hthr hδδ₁ hlog hq8 h8'
  obtain ⟨hδ0, hδ1, hδC⟩ := hthr
  intro ι s T hball hmax hfull
  classical
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδne : δ ≠ 0 := hδ0.ne'
  have hδE0 : (δ : ENNReal) ≠ 0 := by exact_mod_cast hδne
  have hδEtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  set V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun i ↦ (T i).toShadedBody with hV
  -- `s` is nonempty
  have hsne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with h | h
    · exfalso
      rw [h] at hfull
      have h0 : ShadedBody.fullness (∅ : Finset ι) V = 0 := by
        simp [ShadedBody.fullness, ShadedBody.fullness']
      rw [h0] at hfull
      exact absurd hfull (not_le.mpr (NNReal.rpow_pos hδ0))
    · exact h
  obtain ⟨i₀, hi₀⟩ := hsne
  set v : ENNReal := volume (T i₀).carrier with hv
  have hvol : ∀ i ∈ s, volume (V i).carrier = v := fun i _ =>
    Tube.volume_carrier_eq_volume_carrier (T i).toTube (T i₀).toTube
  have hvpos := Tube.volume_pos_and_lt_top hδ0 hδ1 (T i₀).toTube
  have hv0 : v ≠ 0 := hvpos.1.ne'
  have hvtop : v ≠ ⊤ := hvpos.2.ne
  -- Step 1: the band at floor `δ^{2η-η'}`, Markov fraction `δ^{η-3η'}`
  have ha0 : 0 < δ ^ η_f := NNReal.rpow_pos hδ0
  have hθb0 : 0 < δ ^ (2 * η - η') := NNReal.rpow_pos hδ0
  have hθb1 : δ ^ (2 * η - η') ≤ 1 := NNReal.rpow_le_one hδ1 (by linarith)
  have hqhalf : δ ^ (η - 3 * η') ≤ 1 / 2 := by simpa using hq8
  have hq1 : δ ^ (η - 3 * η') < 1 := lt_of_le_of_lt hqhalf (by norm_num)
  have hθq : δ ^ (2 * η - η') ≤ δ ^ (η - 3 * η') * δ ^ η_f := by
    rw [← NNReal.rpow_add hδne]
    exact NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  obtain ⟨s₂, hs₂, lam, hlam0, hlamge, hband, href⟩ :=
    exists_shadingBand hvol hv0 ha0 hθb0 hθb1 hfull hq1 hθq
  have hc₁ : δ ^ (η' / 4) ≤ (1 - δ ^ (η - 3 * η')) *
      ((1 + Real.logb 2 (((δ ^ (2 * η - η') : NNReal) : ℝ)⁻¹)).toNNReal)⁻¹ :=
    denseBand_const_ge_slack hδ0 hδ1 (by linarith) hqhalf hlog
  -- Step 2: the uniformization
  have hcard₂ : (s₂.card : ℝ) ≤ (δ : ℝ) ^ (-((4 : ℕ) : ℝ)) := by
    have h1 : (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-4 : ℝ) :=
      Kakeya.VNSUniform.card_le_rpow_neg_four_enn hδ0 hδ1 hδC s T hball hη1 hmax
    rw [← ENNReal.coe_rpow_of_ne_zero hδne, ← ENNReal.coe_natCast, ENNReal.coe_le_coe] at h1
    have h2 : ((s.card : NNReal) : ℝ) ≤ ((δ ^ (-4 : ℝ) : NNReal) : ℝ) := NNReal.coe_le_coe.mpr h1
    rw [NNReal.coe_rpow, NNReal.coe_natCast] at h2
    have h3 : (s₂.card : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast Finset.card_le_card hs₂
    push_cast
    linarith
  obtain ⟨s₃, hs₃, T', htube, hsh, hcard₃, hfull₃, ⟨𝒱₀⟩⟩ :=
    Hssf hδ0 hδδ₁ s₂ T (fun i hi => hball i (hs₂ hi)) hcard₂
  have 𝒱 : ShadedTube.ShadedUniformTubeSet s₃ T' (Tube.ssfGridLen δ) C := by
    rw [hfr] at 𝒱₀; exact 𝒱₀
  -- the band datum
  set P : ENNReal := (lam : ENNReal) * v with hP
  have hPtop : P ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hvtop
  have hband_lb : ∀ i ∈ s₂, P ≤ 2 * volume (T i).shade := by
    intro i hi
    have h := (hband i hi).1
    rw [hvol i (hs₂ hi)] at h
    calc P = 2 * (2⁻¹ * ((lam : ENNReal) * v)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ 2 * volume (T i).shade := by gcongr
  have hband_ub : ∀ i ∈ s₂, volume (T i).shade ≤ 2 * P := by
    intro i hi
    have h := (hband i hi).2
    rw [hvol i (hs₂ hi)] at h
    exact h
  have hcar' : ∀ i ∈ s₃,
      volume (T' i).toShadedBody.carrier = volume (T i).toShadedBody.carrier := by
    intro i _
    exact congrArg volume (congrArg (fun U : Tube δ _ => U.carrier) (htube i))
  have hcar₀ : ∀ i ∈ s, volume (T' i).carrier = v := by
    intro i hi
    rw [show (T' i).carrier = (T i).carrier from congrArg (fun U : Tube δ _ => U.carrier) (htube i)]
    exact hvol i hi
  -- the `ℝ≥0∞` powers
  set a2 : ENNReal := (δ : ENNReal) ^ (η' / 2) with ha2
  set a4 : ENNReal := (δ : ENNReal) ^ (η' / 4) with ha4
  -- the mass bookkeeping
  set M₃ := ∑ i ∈ s₃, volume (T' i).shade with hM₃
  set Y₃ := ∑ i ∈ s₃, volume (T i).shade with hY₃
  set Y₂ := ∑ i ∈ s₂, volume (T i).shade with hY₂
  set Ys := ∑ i ∈ s, volume (T i).shade with hYs
  have h2 : a2 * Y₃ ≤ M₃ := by
    have h := rpow_mul_sum_shade_le_of_fullness'_le (V := fun i => (T i).toShadedBody)
      (V' := fun i => (T' i).toShadedBody) hδne hcar' hfull₃
    rw [ENNReal.coe_rpow_of_ne_zero hδne] at h
    exact h
  have h3 : (s₃.card : ENNReal) * P ≤ 2 * Y₃ := by
    rw [hY₃, Finset.mul_sum]
    calc (s₃.card : ENNReal) * P = ∑ _i ∈ s₃, P := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s₃, 2 * volume (T i).shade := Finset.sum_le_sum fun i hi => hband_lb i (hs₃ hi)
  have h4 : a2 * (s₂.card : ENNReal) ≤ (s₃.card : ENNReal) := by
    have hR : (δ : ℝ) ^ (η' / 2) * (s₂.card : ℝ) ≤ (s₃.card : ℝ) := by
      calc (δ : ℝ) ^ (η' / 2) * (s₂.card : ℝ)
          ≤ (δ : ℝ) ^ (η' / 2) * ((δ : ℝ) ^ (-(η' / 2)) * (s₃.card : ℝ)) := by gcongr
        _ = (s₃.card : ℝ) := by rw [← mul_assoc, ← Real.rpow_add hδR]; simp
    have hN' : (δ ^ (η' / 2) : NNReal) * (s₂.card : NNReal) ≤ (s₃.card : NNReal) := by
      rw [← NNReal.coe_le_coe]
      push_cast
      exact hR
    have key := ENNReal.coe_le_coe.mpr hN'
    rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδne, ENNReal.coe_natCast,
      ENNReal.coe_natCast] at key
    exact key
  have h5 : Y₂ ≤ (s₂.card : ENNReal) * (2 * P) := by
    calc Y₂ ≤ ∑ _i ∈ s₂, 2 * P := Finset.sum_le_sum hband_ub
      _ = (s₂.card : ENNReal) * (2 * P) := by rw [Finset.sum_const, nsmul_eq_mul]
  have h6 : a4 * Ys ≤ Y₂ := by
    have hr := href.2
    calc a4 * Ys = ((δ ^ (η' / 4) : NNReal) : ENNReal) * Ys := by
          rw [ENNReal.coe_rpow_of_ne_zero hδne]
      _ ≤ (((1 - δ ^ (η - 3 * η')) *
          ((1 + Real.logb 2 (((δ ^ (2 * η - η') : NNReal) : ℝ)⁻¹)).toNNReal)⁻¹ : NNReal)
            : ENNReal) * Ys := mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.mpr hc₁) zero_le
      _ ≤ Y₂ := hr
  -- `8 δ^{3η'/2} ≤ δ^{η'/2} δ^{η'/2} δ^{η'/4}`, i.e. `8 δ^{η'/4} ≤ 1`
  have h7 : 8 * (δ : ENNReal) ^ (3 * η' / 2) ≤ a2 * a2 * a4 := by
    have hN' : (8 : NNReal) * δ ^ (3 * η' / 2) ≤ δ ^ (η' / 2) * δ ^ (η' / 2) * δ ^ (η' / 4) := by
      calc (8 : NNReal) * δ ^ (3 * η' / 2) = (8 * δ ^ (η' / 4)) * δ ^ (5 * η' / 4) := by
            rw [mul_assoc, ← NNReal.rpow_add hδne]; congr 2; ring
        _ ≤ 1 * δ ^ (5 * η' / 4) := by gcongr
        _ = δ ^ (η' / 2) * δ ^ (η' / 2) * δ ^ (η' / 4) := by
            rw [one_mul, ← NNReal.rpow_add hδne, ← NNReal.rpow_add hδne]; congr 1; ring
    have h := ENNReal.coe_le_coe.mpr hN'
    rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_mul,
      ENNReal.coe_rpow_of_ne_zero hδne (3 * η' / 2),
      ENNReal.coe_rpow_of_ne_zero hδne (η' / 2), ENNReal.coe_rpow_of_ne_zero hδne (η' / 4),
      ENNReal.coe_ofNat] at h
    exact h
  have hM₃2 : M₃ ≤ 2 * M₃ := le_mul_of_one_le_left' (by norm_num)
  have hret : (δ : ENNReal) ^ (3 * η' / 2) * Ys ≤ M₃ := retention_chain hM₃2 h2 h3 h4 h5 h6 h7
  refine ⟨s₃, hs₃.trans hs₂, T', htube, hsh, ⟨𝒱⟩, ?_, hret, P, hPtop, ?_, ?_, ?_⟩
  · -- the `IsCRefinement`
    refine ⟨⟨hs₃.trans hs₂, fun i _ => ⟨congrArg Tube.toConvexSpaceBody (htube i), hsh i⟩⟩, ?_⟩
    rw [ENNReal.coe_rpow_of_ne_zero hδne]
    exact hret
  · -- the floor `2 δ^{2η} |T| ≤ δ^{η'} P`
    intro i hi
    have hl : (((2 * δ ^ (2 * η - η') : NNReal)) : ENNReal) ≤ (lam : ENNReal) :=
      ENNReal.coe_le_coe.mpr hlamge
    have hkey : 2 * (δ : ENNReal) ^ (2 * η) ≤ (δ : ENNReal) ^ η' * (lam : ENNReal) := by
      calc 2 * (δ : ENNReal) ^ (2 * η)
          = (δ : ENNReal) ^ η' * (2 * (δ : ENNReal) ^ (2 * η - η')) := by
            rw [mul_left_comm, ← ENNReal.rpow_add _ _ hδE0 hδEtop]; congr 2; ring
        _ = (δ : ENNReal) ^ η' * (((2 * δ ^ (2 * η - η') : NNReal)) : ENNReal) := by
            rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδne, ENNReal.coe_ofNat]
        _ ≤ (δ : ENNReal) ^ η' * (lam : ENNReal) := mul_le_mul_right hl _
    calc 2 * (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier
        = 2 * (δ : ENNReal) ^ (2 * η) * v := by rw [hcar₀ i (hs₂ (hs₃ hi))]
      _ ≤ (δ : ENNReal) ^ η' * (lam : ENNReal) * v := mul_le_mul_left hkey v
      _ = (δ : ENNReal) ^ η' * P := by rw [hP, mul_assoc]
  · -- the per-tube cap `|Y₀(i)| ≤ 2P`
    intro i hi
    exact (measure_mono (hsh i)).trans (hband_ub i (hs₃ hi))
  · -- `δ^{η'/2} · #s₀ · P ≤ 2 ∑_{s₀} |Y₀|`
    calc a2 * ((s₃.card : ENNReal) * P) ≤ a2 * (2 * Y₃) := by gcongr
      _ = 2 * (a2 * Y₃) := by ring
      _ ≤ 2 * M₃ := by gcongr

/-- **Step CD of the chain: the class-dense refinement re-tuned to the slack floor `2 δ^{2η}`**.

`eventually_exists_uniformBand` followed by the class-dense heavy selection
`ShadedTube.exists_denseSelection` at floor `t = δ^{η'} P`, light threshold `2t`, node threshold
`θ' = δ^{η'/2} / (32 (N+1))`. From `hball`, `hmax` (at `δ^{-η}`) and a fullness `δ^{η_f} ≤ λ(s, T)`
it yields a subfamily `(s', T')` — tubes unchanged, shades cut — with

* GWZ Definition 2.2 at a constant `1 ≤ C₀ ≤ δ^{-η'}` (`ShadedTube.denseConst`, capped by
  `denseConst_le_rpow_neg`);
* the per-tube floor `2 · δ^{2η} |T| ≤ |Y'(i)|` — the side-data plan's slack;
* the `IsCRefinement` at retention `δ^{2η'}` (the honest value is `δ^{5η'/4}/16`), also in the
  cleared mass form.

Admissibility: `0 < η'`, `3η' < η`, `η ≤ 1`, `η_f ≤ η + 2η'` (those of
`eventually_exists_uniformBand`; the selection step adds none). -/
theorem eventually_exists_classDenseRefinement_slack {η η' η_f : ℝ} (hη' : 0 < η')
    (h3 : 3 * η' < η) (hη1 : η ≤ 1) (hf : η_f ≤ η + 2 * η') :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        δ ^ η_f ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) →
        ∃ s' ⊆ s, ∃ T' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)),
          (∀ i, (T' i).toTube = (T i).toTube) ∧
          (∀ i, (T' i).shade ⊆ (T i).shade) ∧
          (∃ C₀ : NNReal, 1 ≤ C₀ ∧ (C₀ : ENNReal) ≤ (δ : ENNReal) ^ (-η') ∧
            Nonempty (ShadedTube.ShadedUniformTubeSet s' T' (Tube.ssfGridLen δ) C₀)) ∧
          (∀ i ∈ s', 2 * (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier
            ≤ volume (T' i).shade) ∧
          ShadedBody.IsCRefinement s' (fun i ↦ (T' i).toShadedBody) s
            (fun i ↦ (T i).toShadedBody) (δ ^ (2 * η')) ∧
          (δ : ENNReal) ^ (2 * η') * ∑ i ∈ s, volume (T i).shade
            ≤ ∑ i ∈ s', volume (T' i).shade := by
  obtain ⟨δ₂, hδ₂pos, -, Hpoly⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le 4 (by norm_num) 0 1 (η' / 4) (by linarith)
  have hle₂ : ∀ᶠ d : NNReal in 𝓝[>] 0, d ≤ δ₂ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ₂pos)] with d hd
    exact le_of_lt hd
  set C : NNReal := ShadedTube.ssfUniformConst 3 with hC
  filter_upwards [eventually_exists_uniformBand.{u} hη' h3 hη1 hf,
    Kakeya.VNSUniform.eventually_card_thresholds', hle₂,
    eventually_nnreal_mul_rpow_le_const (6 * C) (1 / 2) (by norm_num)
      (by linarith : 0 < 3 * η' / 4),
    eventually_nnreal_mul_rpow_le_const (32 * C) (1 / 2) (by norm_num)
      (by linarith : 0 < η' / 4),
    eventually_nnreal_mul_rpow_le_const 32 1 (by norm_num) (by linarith : 0 < η' / 2)]
    with δ HU hthr hδδ₂ h6C h32C h32
  obtain ⟨hδ0, hδ1, -⟩ := hthr
  intro ι s T hball hmax hfull
  classical
  have hδne : δ ≠ 0 := hδ0.ne'
  have hδE0 : (δ : ENNReal) ≠ 0 := by exact_mod_cast hδne
  have hδEtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  obtain ⟨s₃, hs₃, T', htube, hsh, ⟨𝒱⟩, -, hret₀, P, hPtop, hfloorP, hMP, hcardP⟩ :=
    HU s T hball hmax hfull
  -- Step 3: the dense selection
  set N := Tube.ssfGridLen δ with hN
  set θ' : NNReal := δ ^ (η' / 2) / (32 * ((N : NNReal) + 1)) with hθ'
  have hθ'pos : 0 < θ' := by positivity
  set t : ENNReal := (δ : ENNReal) ^ η' * P with ht
  set M : ENNReal := 2 * P with hM
  have hMtop : M ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hPtop
  obtain ⟨s', hs', T'', htube'', hsh'', hfloor, huni, hacc⟩ :=
    ShadedTube.exists_denseSelection 𝒱 hθ'pos t hMP hMtop
  -- the `ℝ≥0∞` powers
  set a2 : ENNReal := (δ : ENNReal) ^ (η' / 2) with ha2
  -- the mass retention
  set M₃ := ∑ i ∈ s₃, volume (T' i).shade with hM₃
  set Ys := ∑ i ∈ s, volume (T i).shade with hYs
  set ret := ∑ i ∈ s', volume (T'' i).shade with hret
  have hretf : (δ : ENNReal) ^ (2 * η') * Ys ≤ ret := by
    set ℓ := ∑ i ∈ s₃.filter (fun i => volume (T' i).shade < 2 * t), volume (T' i).shade with hℓ
    set Cc := ((N : ENNReal) + 1) * (θ' : ENNReal) * (s₃.card : ENNReal) * M with hCc
    have hM₃top : M₃ ≠ ⊤ :=
      (ENNReal.sum_lt_top.2 fun i hi => lt_of_le_of_lt (hMP i hi) hMtop.lt_top).ne
    -- `32 δ^{η'} ≤ δ^{η'/2}`
    have h32E : (32 : ENNReal) * (δ : ENNReal) ^ η' ≤ a2 := by
      have hN' : (32 : NNReal) * δ ^ η' ≤ δ ^ (η' / 2) := by
        calc (32 : NNReal) * δ ^ η' = (32 * δ ^ (η' / 2)) * δ ^ (η' / 2) := by
              rw [mul_assoc, ← NNReal.rpow_add hδne]; congr 2; ring
          _ ≤ 1 * δ ^ (η' / 2) := by gcongr
          _ = δ ^ (η' / 2) := one_mul _
      have h := ENNReal.coe_le_coe.mpr hN'
      rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδne η',
        ENNReal.coe_rpow_of_ne_zero hδne (η' / 2), ENNReal.coe_ofNat] at h
      exact h
    have hℓ1 : ℓ ≤ (s₃.card : ENNReal) * (2 * t) := by
      calc ℓ ≤ ∑ _i ∈ s₃.filter (fun i => volume (T' i).shade < 2 * t), 2 * t :=
            Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2.le
        _ = ((s₃.filter (fun i => volume (T' i).shade < 2 * t)).card : ENNReal) * (2 * t) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (s₃.card : ENNReal) * (2 * t) := by
            gcongr
            exact Finset.filter_subset _ _
    have hℓ : 8 * ℓ ≤ M₃ := by
      have h : 2 * (8 * ℓ) ≤ 2 * M₃ := by
        calc 2 * (8 * ℓ) ≤ 2 * (8 * ((s₃.card : ENNReal) * (2 * t))) := by gcongr
          _ = (32 * (δ : ENNReal) ^ η') * ((s₃.card : ENNReal) * P) := by rw [ht]; ring
          _ ≤ a2 * ((s₃.card : ENNReal) * P) := by gcongr
          _ ≤ 2 * M₃ := hcardP
      exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h
    have hCc : 8 * Cc ≤ M₃ := by
      have hθ'id : (32 : NNReal) * (((N : NNReal) + 1) * θ') = δ ^ (η' / 2) := by
        rw [hθ', ← mul_assoc]
        have hne : (32 : NNReal) * ((N : NNReal) + 1) ≠ 0 := by positivity
        rw [mul_div_cancel₀ _ hne]
      have hθ'E : (32 : ENNReal) * (((N : ENNReal) + 1) * (θ' : ENNReal)) = a2 := by
        have h := congrArg (fun x : NNReal => (x : ENNReal)) hθ'id
        rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_natCast,
          ENNReal.coe_one, ENNReal.coe_ofNat, ENNReal.coe_rpow_of_ne_zero hδne] at h
        exact h
      have h : 2 * (8 * Cc) ≤ 2 * M₃ := by
        calc 2 * (8 * Cc) = (32 * (((N : ENNReal) + 1) * (θ' : ENNReal))) *
              ((s₃.card : ENNReal) * P) := by rw [hCc, hM]; ring
          _ = a2 * ((s₃.card : ENNReal) * P) := by rw [hθ'E]
          _ ≤ 2 * M₃ := hcardP
      exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h
    have h1 : M₃ ≤ 2 * ret := total_le_two_mul_retained hM₃top hacc hℓ hCc
    -- `2 δ^{2η'} ≤ δ^{3η'/2}`
    have h2E : (2 : ENNReal) * (δ : ENNReal) ^ (2 * η') ≤ (δ : ENNReal) ^ (3 * η' / 2) := by
      have hN' : (2 : NNReal) * δ ^ (2 * η') ≤ δ ^ (3 * η' / 2) := by
        have h2half : (2 : NNReal) * δ ^ (η' / 2) ≤ 1 := by
          calc (2 : NNReal) * δ ^ (η' / 2) ≤ 32 * δ ^ (η' / 2) := by gcongr; norm_num
            _ ≤ 1 := h32
        calc (2 : NNReal) * δ ^ (2 * η') = (2 * δ ^ (η' / 2)) * δ ^ (3 * η' / 2) := by
              rw [mul_assoc, ← NNReal.rpow_add hδne]; congr 2; ring
          _ ≤ 1 * δ ^ (3 * η' / 2) := by gcongr
          _ = δ ^ (3 * η' / 2) := one_mul _
      have h := ENNReal.coe_le_coe.mpr hN'
      rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδne (2 * η'),
        ENNReal.coe_rpow_of_ne_zero hδne (3 * η' / 2), ENNReal.coe_ofNat] at h
      exact h
    have h : 2 * ((δ : ENNReal) ^ (2 * η') * Ys) ≤ 2 * ret := by
      calc 2 * ((δ : ENNReal) ^ (2 * η') * Ys) = (2 * (δ : ENNReal) ^ (2 * η')) * Ys := by ring
        _ ≤ (δ : ENNReal) ^ (3 * η' / 2) * Ys := by gcongr
        _ ≤ M₃ := hret₀
        _ ≤ 2 * ret := h1
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h
  refine ⟨s', hs'.trans hs₃, T'', fun i => (htube'' i).trans (htube i),
    fun i => (hsh'' i).trans (hsh i), ⟨ShadedTube.denseConst N C θ', ?_, ?_, huni⟩, ?_, ?_, hretf⟩
  · -- `1 ≤ C₀`
    have h1 : 1 ≤ C := ShadedTube.one_le_ssfUniformConst 3
    unfold ShadedTube.denseConst
    have h24 : (1 : NNReal) ≤ 24 * 4 ^ N := by
      calc (1 : NNReal) ≤ 24 := by norm_num
        _ = 24 * 1 := by ring
        _ ≤ 24 * 4 ^ N := by gcongr; exact one_le_pow₀ (by norm_num)
    calc (1 : NNReal) ≤ C := h1
      _ = 1 * C := (one_mul C).symm
      _ ≤ 24 * 4 ^ N * C := by gcongr
      _ ≤ 24 * 4 ^ N * C + C / θ' := le_self_add
  · -- the cap
    have hpoly : (4 : ℝ) ^ (N + 1) ≤ (δ : ℝ) ^ (-(η' / 4)) := by
      have h := (Hpoly hδ0 hδδ₂).2.2 1 (by norm_num) (by simp)
      simpa using h
    exact denseConst_le_rpow_neg hδ0 C N hpoly h6C h32C
  · -- the per-tube floor `2 δ^{2η} |T| ≤ |Y'(i)|`
    intro i hi
    rw [show (T'' i).carrier = (T' i).carrier from
      congrArg (fun U : Tube δ _ => U.carrier) (htube'' i)]
    exact (hfloorP i (hs' hi)).trans (hfloor i hi)
  · -- the `IsCRefinement`
    refine ⟨⟨hs'.trans hs₃, fun i _ => ⟨congrArg Tube.toConvexSpaceBody
      ((htube'' i).trans (htube i)), (hsh'' i).trans (hsh i)⟩⟩, ?_⟩
    rw [ENNReal.coe_rpow_of_ne_zero hδne]
    exact hretf

/-- **Consistency check: the statement of `eventually_exists_classDenseRefinement` from the
re-tuned refinement at `η_f = η`.**  The floor `δ^{2η} |T|` is half the slack floor and the
retention `δ^η` is below `δ^{2η'}` (as `2η' ≤ η`, `δ ≤ 1`).  The original declaration is not
touched; this only certifies that the re-tune generalises it. -/
theorem eventually_exists_classDenseRefinement_of_slack {η η' : ℝ} (hη' : 0 < η')
    (h8 : 8 * η' < η) (hη1 : η ≤ 1) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        δ ^ η ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) →
        ∃ s' ⊆ s, ∃ T' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)),
          (∀ i, (T' i).toTube = (T i).toTube) ∧
          (∀ i, (T' i).shade ⊆ (T i).shade) ∧
          (∃ C₀ : NNReal, 1 ≤ C₀ ∧ (C₀ : ENNReal) ≤ (δ : ENNReal) ^ (-η') ∧
            Nonempty (ShadedTube.ShadedUniformTubeSet s' T' (Tube.ssfGridLen δ) C₀)) ∧
          (∀ i ∈ s', (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier ≤ volume (T' i).shade) ∧
          (δ : ENNReal) ^ η * ∑ i ∈ s, volume (T i).shade ≤ ∑ i ∈ s', volume (T' i).shade := by
  filter_upwards [eventually_exists_classDenseRefinement_slack.{u} (η_f := η) hη'
    (by linarith) hη1 (by linarith), Kakeya.VNSUniform.eventually_card_thresholds']
    with δ H hthr
  obtain ⟨-, hδ1, -⟩ := hthr
  intro ι s T hball hmax hfull
  obtain ⟨s', hs', T', htube, hsh, huni, hfloor, -, hmass⟩ := H s T hball hmax hfull
  refine ⟨s', hs', T', htube, hsh, huni, ?_, ?_⟩
  · intro i hi
    refine le_trans ?_ (hfloor i hi)
    calc (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier
        = 1 * ((δ : ENNReal) ^ (2 * η) * volume (T' i).carrier) := (one_mul _).symm
      _ ≤ 2 * ((δ : ENNReal) ^ (2 * η) * volume (T' i).carrier) := by gcongr; norm_num
      _ = 2 * (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier := by ring
  · have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
    have hpow : (δ : ENNReal) ^ η ≤ (δ : ENNReal) ^ (2 * η') :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
    calc (δ : ENNReal) ^ η * ∑ i ∈ s, volume (T i).shade
        ≤ (δ : ENNReal) ^ (2 * η') * ∑ i ∈ s, volume (T i).shade := mul_le_mul_left hpow _
      _ ≤ ∑ i ∈ s', volume (T' i).shade := hmass

end Kakeya.VeryNotSticky
