/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleFactor
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoarseSeam

/-!
# The branch-(ii) wiring: from the window package to the mass gain

This file is composition only.  It carries the window branch of
`Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3` down to the node-restricted family on which
`Kakeya.ML2Core.mass_gain_of_three_factors` acts, and back up to the original family `(𝕋, Y)`,
which is the shape `Kakeya.ML2Assembly.Dichotomy`'s right disjunct states.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u w

variable
  {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]


section EpsOneShrink

/-- **`Kakeya.ML2Core.exists_multiplicity_quarter`, downward-closed in `ε₁`.**

The Katz--Tao exponent `ε₁` of GWZ Theorem 7.3(B) enters the existing statement only through the
hypothesis `𝒲.tubeUniform.IsKatzTaoAtEveryScale (δ^{-ε₁})`, which is *weaker* for smaller `ε₁`.
So the whole body holds at every `ε₁` below the one the theorem produces, and
`Kakeya.ML2Assembly.GeometricCoreAt` — which asks only for *some* `ε₁ > 0` — may spend that
freedom.

**This is what buys the exponent ordering the fine and coarse factors need.**
`Kakeya.ML2Core.spineNu_le_div_25` gives `ν ≤ ε₁/25`, so shrinking `ε₁` pushes the spine's bottom
rung below any prescribed positive exponent — in particular below the density exponents
`Kakeya.KatzTaoEstimate.generalize` returns, which are fixed before `ε₁` is chosen. Without it the
fine factor is unusable: its own density exponent is *strictly smaller* than its accuracy
(`η = ε η₁/(n + η₁ + 1)`), so reading it at the accuracy `ν` would need `ν < η(ν) < ν`. -/
theorem exists_multiplicity_quarter_le (hdim : Module.finrank ℝ E = 3)
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{u, u} (E := E))
    {β : ℝ} (hβ : 0 < β) :
    ∃ ε₁₀ : ℝ, 0 < ε₁₀ ∧ ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ ε₁₀ →
      ∀ {ν : ℝ}, 0 < ν → 2 * ν ≤ ε₁ →
      ∃ d : NNReal, 0 < d ∧ d ≤ 1 ∧
        ∀ {δ : NNReal}, 0 < δ → δ ≤ d →
        ∀ {ι : Type w} (s u : Finset ι) (T W : ι → ShadedTube δ E) (lam : NNReal),
          u ⊆ s →
          (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
          (∀ i, (W i).toTube = (T i).toTube) →
          Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
              ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ν)) →
          (s.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
          ENNReal.ofReal ((δ : ℝ) ^ ν) ≤ 2 * (lam : ENNReal) →
          (lam : ENNReal) ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * Tube.ssfGridLen δ + 2)
              * ShadedBody.fullness' u (fun i => (W i).toShadedBody) →
          ∀ {Cu : NNReal} (𝒲 : ShadedTube.ShadedUniformTubeSet u W (Tube.ssfGridLen δ) Cu),
            𝒲.tubeUniform.IsKatzTaoAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-ε₁))) →
            ShadedBody.multiplicity u (fun i => (W i).toShadedBody)
              ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(β / 4))) := by
  obtain ⟨ε₁₀, hε₁₀, hmain⟩ := exists_multiplicity_quarter (E := E) hdim hSFE hβ
  refine ⟨ε₁₀, hε₁₀, ?_⟩
  intro ε₁ hε₁ hle ν hν hνε
  obtain ⟨d, hd0, hd1, hbody⟩ := hmain hν (hνε.trans hle)
  refine ⟨d, hd0, hd1, ?_⟩
  intro δ hδ0 hδd ι s u T W lam hus hball htube hmax hcard hlam hfullpoly Cu 𝒲 hevery
  refine hbody hδ0 hδd s u T W lam hus hball htube hmax hcard hlam hfullpoly 𝒲 ?_
  refine hevery.mono ?_
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδ1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδd.trans hd1
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge hδR hδ1 (by linarith))

/-- **The spine's bottom rung is at most `ε₁/25`.**

`η_0 ≤ η_N = e ≤ ε₂/5 ≤ ε₁/25`, by `Kakeya.ML2Spine.IsSpine`'s `rung_mono`, `rung_top`, `div_le`
and `eps₂_le_everyScale` — the four fields the module docstring of `Reduction/SpineCoreLeft.lean`
already names.  Stated because it is the *only* handle the assembly has on how small the drop is,
and it is what makes `Kakeya.ML2Core.exists_multiplicity_quarter_le` useful. -/
theorem spineNu_le_div_25 {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    ML2Spine.spineNu β ϖ ε₁ gain dens ≤ ε₁ / 25 := by
  have hspine := ML2Spine.spineRung_isSpine hβ hβ1 hϖ hε₁ hgain hdens
  have h1 : ML2Spine.spineRung β ϖ ε₁ gain dens 0
      ≤ ML2Spine.spineRung β ϖ ε₁ gain dens (ML2Spine.spineCount ϖ ε₁) :=
    hspine.rung_mono (Nat.zero_le _)
  have h2 := hspine.rung_top
  have h3 := hspine.div_le
  have h4 : ML2Spine.spineEps₂ ϖ ε₁ ≤ ε₁ / 5 := ML2Spine.spineEps₂_le_everyScale
  rw [h2] at h1
  simp only [ML2Spine.spineNu]
  linarith

/-- **Branch (i), at every small enough Katz--Tao exponent.**

The existing `Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3` with the `∃ ε₁` replaced by
`∀ ε₁ ≤ ε₁₀`.  Only two lines of its proof change: `Kakeya.ML2Core.exists_multiplicity_quarter`
is read through `Kakeya.ML2Core.exists_multiplicity_quarter_le`, and the package
`Kakeya.ML2Core.eventually_dividingScalesPackage_dim3` already takes `ε₁` as a parameter. -/
theorem exists_dichotomyLeft_or_window_dim3_small
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))
    {β ϖ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    ∃ ε₁₀ : ℝ, 0 < ε₁₀ ∧ ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ ε₁₀ →
      ∃ (C : NNReal) (Kl cl : ℕ) (ε₂ e : ℝ) (N : ℕ) (η : ℕ → ℝ),
        1 ≤ C ∧ 4096 ≤ N ∧ e = 1 / Real.sqrt (N : ℝ) ∧
        η 0 = ML2Spine.spineNu β ϖ ε₁ gain dens ∧ 0 < η 0 ∧ η 0 ≤ 1 ∧
        ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η ∧
        ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
          0 < δ ∧ δ ≤ 1 ∧
          ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
            (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
            IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-(η 0))) →
            ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ (η 0) →
            (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
            s.Nonempty ∧
            (ML2Shading.DichotomyLeft (β / 2) s T
              ∨ ∃ u' ⊆ s, ∃ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∃ lam : NNReal,
                  δ ^ (η 0) / 2 ≤ lam ∧ 0 < lam ∧ u'.Nonempty ∧
                  (∀ i, (W i).toTube = (T i).toTube) ∧
                  (∀ i, (W i).shade ⊆ (T i).shade) ∧
                  ML2Shaded.HasDenseShading lam u' (fun i ↦ (T i).toShadedBody) ∧
                  ML2Shaded.HasComparableDensities lam⁻¹ u'
                      (fun i ↦ (T i).toShadedBody) ∧
                  (lam : ENNReal)
                        * (Tube.le_volume.c
                            (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
                        * (∑ i ∈ s, volume (T i).shade)
                      ≤ 2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0)))
                          * StickyKakeya.totalLoss C Kl cl δ)
                        * (Tube.volume_le.C
                            (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
                        * ∑ i ∈ u', volume (T i).shade ∧
                  (∑ i ∈ u', volume (T i).shade)
                      ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
                        * ∑ i ∈ u', volume (W i).shade ∧
                  volume (⋃ i ∈ u', (W i).shade) ≤ volume (⋃ i ∈ s, (T i).shade) ∧
                  (lam : ENNReal)
                      ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
                        * ShadedBody.fullness' u' (fun i ↦ (W i).toShadedBody) ∧
                  ∃ 𝒲 : ShadedUniformTubeSet u' W (ssfGridLen δ) (max C 4),
                    ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindow 𝒲.tubeUniform
                        ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) η e N a b m) := by
  classical
  obtain ⟨ε₁₀, hε₁₀, hL1all⟩ :=
    exists_multiplicity_quarter_le (E := EuclideanSpace ℝ (Fin 3))
      finrank_euclideanSpace_fin hSFE hβ
  refine ⟨ε₁₀, hε₁₀, ?_⟩
  intro ε₁ hε₁ hε₁le
  obtain ⟨C, Kl, cl, ε₂, e, N, η, hC, hN, he, hη0nu, hη00, hη01, hspine, hev⟩ :=
    eventually_dividingScalesPackage_dim3.{u} hβ hβ1 hϖ hε₁ hgain hdens
  refine ⟨C, Kl, cl, ε₂, e, N, η, hC, hN, he, hη0nu, hη00, hη01, hspine, ?_⟩
  have hνε₁ : 2 * η 0 ≤ ε₁ := by
    have h1 : η 0 ≤ η N := hspine.rung_mono (Nat.zero_le N)
    have h2 : η N = e := hspine.rung_top
    have h3 : e ≤ ε₂ / 5 := hspine.div_le
    have h4 : ε₂ ≤ ε₁ / 5 := hspine.eps₂_le_everyScale
    have h5 : 0 < ε₂ := hspine.eps₂_pos
    rw [h2] at h1
    linarith
  have hν48 : η 0 ≤ β / 48000 := by
    rw [hη0nu]
    exact ML2Inputs.spineNu_le_div_48000 hβ hβ1 hϖ hε₁ hgain hdens
  have hbud : η 0 + η 0 + η 0 + η 0 + β / 4 + η 0 + η 0 ≤ β / 2 := by linarith
  obtain ⟨d1, hd10, hd11, hL1d⟩ := hL1all ε₁ hε₁ hε₁le hη00 hνε₁
  obtain ⟨dT, hdT0, hdT1, hdT⟩ :=
    StickyKakeya.exists_threshold_totalLoss_le C hC Kl cl (η 0) hη00
  obtain ⟨dS, hdS0, hdS1, hdS⟩ :=
    ML2Shading.exists_threshold_shadingBridgeLoss_le
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) 2 4
      (a := η 0 + η 0 + η 0) (α := η 0) hη00
  obtain ⟨d2, hd20, hd21, hd2⟩ := ML2Shaded.exists_threshold_const_le_rpow_neg' 2 hη00
  filter_upwards [hev, ML2Assembly.eventually_card_thresholds,
    Ioc_mem_nhdsGT hd10, Ioc_mem_nhdsGT hdT0, Ioc_mem_nhdsGT hdS0, Ioc_mem_nhdsGT hd20]
    with δ hpkg hthr hm1 hmT hmS hm2
  obtain ⟨hδ0, hδ1, hpkgbody⟩ := hpkg
  obtain ⟨-, -, hδC⟩ := hthr
  refine ⟨hδ0, hδ1, ?_⟩
  intro ι s T hball hKT hfull hcard
  obtain ⟨hsne, s', hs's, lam, hlamlow, hlam0, hs'ne, hmass, hdense, hout⟩ :=
    hpkgbody s T hball hKT hfull hcard
  refine ⟨hsne, ?_⟩
  obtain ⟨u', hu's, W, htube, hshade, hu'ne, hdenseu, hcompu, hmassloss, hpoly, hunion,
    hfullpoly, 𝒲, halt⟩ :=
    losses_of_dividingScalesOutput (E := EuclideanSpace ℝ (Fin 3)) hδ1 hs's hmass hout
  rcases halt with hevery | hwindow
  · -- alternative (i): GWZ `section9.tex` lines 55–61
    refine Or.inl ?_
    have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
    have hmaxs : Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0))) := by
      rw [ML2Reduction.ofReal_rpow_coe hδ0]
      exact hKT
    have hcard4 : (s.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) := by
      simpa using ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s T hball hη01 hKT
    have hlamE : ENNReal.ofReal ((δ : ℝ) ^ (η 0)) ≤ 2 * (lam : ENNReal) := by
      have hnn : (δ : NNReal) ^ (η 0) ≤ 2 * lam := by
        rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 2)] at hlamlow
        calc (δ : NNReal) ^ (η 0) ≤ lam * 2 := hlamlow
          _ = 2 * lam := by ring
      have hcoe : ENNReal.ofReal ((δ : ℝ) ^ (η 0))
          = (((δ : NNReal) ^ (η 0) : NNReal) : ENNReal) := by
        rw [← NNReal.coe_rpow, ENNReal.ofReal_coe_nnreal]
      rw [hcoe]
      calc (((δ : NNReal) ^ (η 0) : NNReal) : ENNReal) ≤ ((2 * lam : NNReal) : ENNReal) :=
            ENNReal.coe_le_coe.mpr hnn
        _ = 2 * (lam : ENNReal) := by push_cast; ring
    have hmult := hL1d hδ0 hm1.2 s u' T W lam hu's hball htube hmaxs hcard4 hlamE hfullpoly
      𝒲 hevery
    have hA : ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0))) * StickyKakeya.totalLoss C Kl cl δ
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0 + η 0))) := by
      calc ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0))) * StickyKakeya.totalLoss C Kl cl δ
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0)))
              * ENNReal.ofReal ((δ : ℝ) ^ (-(η 0))) := by
            gcongr
            exact hdT hδ0 hmT.2
        _ = ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0 + η 0))) := by
            rw [ofReal_rpow_mul hδ0]
            ring_nf
    have hSBL := hdS hδ0 hmS.2 hA s.card (by simpa using hcard4)
    have htwo : (2 : ENNReal) ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0))) := by
      have hr := hd2 hδ0 hm2.2
      calc (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by simp
        _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0))) := ENNReal.ofReal_le_ofReal hr
    have hchain := sum_shade_le_shadingBridgeLoss hmassloss hpoly hunion hmult
    have hbound := sum_shade_le_rpow_of_chain hδ0 hchain hSBL le_rfl hlamE htwo
    exact dichotomyLeft_of_rpow_bound hδ0 hδ1 hbound hbud
  · exact Or.inr ⟨u', hu's, W, lam, hlamlow, hlam0, hu'ne, htube, hshade, hdenseu, hcompu,
      hmassloss, hpoly, hunion, hfullpoly, 𝒲, hwindow⟩

end EpsOneShrink

section Pushback

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] [ProperSpace E]
  {ι : Type*}

/-- **The pushback of branch (ii), in one inequality.**

The window branch produces its gain on the *node-restricted* family `s₁ ⊆ u' ⊆ s`, and
`Kakeya.ML2Assembly.Dichotomy` asks for it on `s`.  Two discards separate them, and both are paid
by the same pointwise density invariant:

* `s ⇝ u'` is the dividing-scales package's own mass loss `hmassloss`;
* `u' ⇝ s₁` is the parent seam's cardinality discard, converted to mass by
  `Kakeya.ML2Core.sum_shade_le_of_node_subfamily`.

The union moves the helpful way for free, so no third loss appears.  Everything is multiplied
out: `lam * c₃` is cancelled once at the end by `ENNReal.mul_le_mul_iff_left`, never divided by,
so no `≠ 0`/`≠ ⊤` side condition escapes into the caller beyond the two on `lam` itself. -/
theorem sum_shade_le_of_node_gain {δ : NNReal} (hδ1 : δ ≤ 1) {s u s₁ : Finset ι}
    (hus : u ⊆ s) (hs₁ : s₁ ⊆ u) {V : ι → ShadedTube δ E} {lam Kc : NNReal}
    (hlam0 : 0 < lam)
    (hdense : ML2Shaded.HasDenseShading lam u (fun i ↦ (V i).toShadedBody))
    (hcard : (u.card : NNReal) ≤ Kc * (s₁.card : NNReal))
    {A G Λ : ENNReal}
    (hmassloss : (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
        * (∑ i ∈ s, volume (V i).shade)
      ≤ A * ∑ i ∈ u, volume (V i).shade)
    (hgain : ∑ i ∈ s₁, volume (V i).shade ≤ G * volume (⋃ i ∈ s₁, (V i).shade))
    (habs : A * ((Kc : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)) * G
      ≤ ((lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal))
          * ((lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)) * Λ) :
    ∑ i ∈ s, volume (V i).shade ≤ Λ * volume (⋃ i ∈ s, (V i).shade) := by
  classical
  set c : ENNReal := (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) with hc
  set C : ENNReal := (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) with hC
  have hc0 : c ≠ 0 := by
    simpa [hc] using (Tube.le_volume.c_pos (Module.finrank ℝ E)).ne'
  have hctop : c ≠ (⊤ : ENNReal) := by simp [hc]
  have hlamE0 : ((lam : NNReal) : ENNReal) ≠ 0 := by simpa using hlam0.ne'
  have hlamEtop : ((lam : NNReal) : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
  have hK0 : (lam : ENNReal) * c ≠ 0 := mul_ne_zero hlamE0 hc0
  have hKtop : (lam : ENNReal) * c ≠ (⊤ : ENNReal) := ENNReal.mul_ne_top hlamEtop hctop
  -- the seam's discard, as a mass retention
  have hseam : (lam : ENNReal) * c * ∑ i ∈ u, volume (V i).shade
      ≤ (Kc : ENNReal) * C * ∑ i ∈ s₁, volume (V i).shade :=
    sum_shade_le_of_node_subfamily hδ1 hs₁ hdense hcard
  -- the union moves the helpful way
  have hunion : volume (⋃ i ∈ s₁, (V i).shade) ≤ volume (⋃ i ∈ s, (V i).shade) := by
    refine measure_mono ?_
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hus (hs₁ hi), hxi⟩
  refine (ENNReal.mul_le_mul_iff_left (mul_ne_zero hK0 hK0)
    (ENNReal.mul_ne_top hKtop hKtop)).mp ?_
  calc (∑ i ∈ s, volume (V i).shade) * ((lam : ENNReal) * c * ((lam : ENNReal) * c))
      = (lam : ENNReal) * c * ((lam : ENNReal) * c * ∑ i ∈ s, volume (V i).shade) := by ring
    _ ≤ (lam : ENNReal) * c * (A * ∑ i ∈ u, volume (V i).shade) := by gcongr
    _ = A * ((lam : ENNReal) * c * ∑ i ∈ u, volume (V i).shade) := by ring
    _ ≤ A * ((Kc : ENNReal) * C * ∑ i ∈ s₁, volume (V i).shade) := by gcongr
    _ ≤ A * ((Kc : ENNReal) * C * (G * volume (⋃ i ∈ s₁, (V i).shade))) := by gcongr
    _ ≤ A * ((Kc : ENNReal) * C * (G * volume (⋃ i ∈ s, (V i).shade))) := by gcongr
    _ = (A * ((Kc : ENNReal) * C) * G) * volume (⋃ i ∈ s, (V i).shade) := by ring
    _ ≤ (((lam : ENNReal) * c) * ((lam : ENNReal) * c) * Λ)
          * volume (⋃ i ∈ s, (V i).shade) := by gcongr
    _ = (Λ * volume (⋃ i ∈ s, (V i).shade))
          * ((lam : ENNReal) * c * ((lam : ENNReal) * c)) := by ring

end Pushback


section ActiveCount

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
open Classical in
/-- **An active node carries a leaf, and distinct active nodes carry distinct leaves.**

So the level-`k` node count never exceeds the leaf count.  This is the crude ceiling the
subpolynomial absorption of `Kakeya.ML2Reduction.spineScaleLoss` needs at the *node* scale, and it
is the only cardinality fact about `Kakeya.ML2Reduction.activeNodes` the wiring uses. -/
theorem card_activeNodes_le_card (𝒞 : Tube.ChainCoverSystem s T N σ) (k : ℕ) :
    (ML2Reduction.activeNodes 𝒞 k).card ≤ s.card := by
  classical
  have hsub : ML2Reduction.activeNodes 𝒞 k ⊆ s.image (𝒞.assign k) := by
    intro j hj
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hj).2
    simp only [Tube.coverClass, Finset.mem_filter] at hi
    exact Finset.mem_image.mpr ⟨i, hi.1, hi.2⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end ActiveCount

section Split

variable {ι : Type u}

open Classical in
/-- **The three factors, the seam's discard and the package's mass loss, in one inequality.**

`Kakeya.ML2Core.mass_gain_of_three_factors` lands the gain on the *node-restricted* family
`{i ∈ u | assign b i ∈ t₁}`; `Kakeya.ML2Core.sum_shade_le_of_node_gain` carries it back to the
original family `s`, which is the side `Kakeya.ML2Assembly.Dichotomy` states it on.  Nothing here
is geometric: it is the two existing rows composed, with the loss ledger written out once. -/
theorem sum_shade_gain_of_split
    {β : ℝ} (hβ0 : 0 ≤ β) {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {Cu Kc lam : NNReal} (hlam0 : 0 < lam)
    {s u : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hus : u ⊆ s)
    (hdense : ML2Shaded.HasDenseShading lam u (fun i ↦ (V i).toShadedBody))
    {Nn : ℕ} {σ : ℕ → NNReal}
    (𝒰 : Tube.ChainUniformTubeSet u (fun i ↦ (V i).toTube) Nn σ Cu)
    {a b : ℕ} (hab : a ≤ b) (haN : a ≤ Nn) (hbN : b ≤ Nn)
    {t₁ tτ' tθ' : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover b)
    (htτ : tτ' ⊆ t₁) (htθ : tθ' ⊆ 𝒰.cover.indexSet a)
    {jτ jθ : ι} (hjτ : jτ ∈ t₁)
    {Yτ' : ι → ShadedTube (σ b) (EuclideanSpace ℝ (Fin 3))}
    {Yθ : ι → ShadedTube (σ a) (EuclideanSpace ℝ (Fin 3))}
    {Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {L A : ENNReal} {εf gm εc κ g gt : ℝ}
    (hprod : ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
          (fun i ↦ (V i).toShadedBody)
        ≤ L
          * ShadedBody.multiplicity
              ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
          * ShadedBody.multiplicity
              ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover a b j = jθ} : Finset ι)
              (fun j ↦ (Yτ' j).toShadedBody)
          * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody))
    (hfine : ShadedBody.multiplicity
          ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εf)
          * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι)).card : ENNReal) ^ β)
    (hmid : ShadedBody.multiplicity
          ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover a b j = jθ} : Finset ι)
          (fun j ↦ (Yτ' j).toShadedBody)
        ≤ (δ : ENNReal) ^ gm
          * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover a b j = jθ}
                : Finset ι)).card : ENNReal) ^ β)
    (hcoarse : ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εc) * ((tθ'.card : ℕ) : ENNReal) ^ β)
    (hL : L * (((Cu ^ 5 : NNReal) : ENNReal)) ^ β ≤ (δ : ENNReal) ^ (-κ))
    (hexp : g ≤ gm - εf - εc - κ)
    (hmassloss : (lam : ENNReal)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
          * (∑ i ∈ s, volume (V i).shade)
        ≤ A * ∑ i ∈ u, volume (V i).shade)
    (hcardseam : (u.card : NNReal)
      ≤ Kc * ((({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card : NNReal))
    (habs : A * ((Kc : ENNReal)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * (δ : ENNReal) ^ g
        ≤ ((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * ((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * (δ : ENNReal) ^ gt) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (δ : ENNReal) ^ gt * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (V i).shade) := by
  classical
  have hδE0 : (δ : ENNReal) ≠ 0 := by simpa using hδ0.ne'
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hgain := mass_gain_of_three_factors (V := V) 𝒰 hab haN hbN ht₁ (htτ.trans ht₁) htθ
    (jθ := jθ) hjτ (Yτ' := Yτ') (Yθ := Yθ) (Y' := Y') hδE0 hδE1 hβ0 hprod hfine hmid hcoarse
    hL hexp
  have hcardβ : ((u.card : ℕ) : ENNReal) ^ β ≤ ((s.card : ℕ) : ENNReal) ^ β := by
    have : ((u.card : ℕ) : ENNReal) ≤ ((s.card : ℕ) : ENNReal) := by
      exact_mod_cast Finset.card_le_card hus
    exact ENNReal.rpow_le_rpow this hβ0
  refine sum_shade_le_of_node_gain hδ1 hus (Finset.filter_subset _ _) hlam0 hdense hcardseam
    hmassloss hgain ?_
  calc A * ((Kc : ENNReal)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * ((δ : ENNReal) ^ g * ((u.card : ℕ) : ENNReal) ^ β)
      = (A * ((Kc : ENNReal)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * (δ : ENNReal) ^ g) * ((u.card : ℕ) : ENNReal) ^ β := by ring
    _ ≤ (((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * ((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * (δ : ENNReal) ^ gt) * ((s.card : ℕ) : ENNReal) ^ β := by gcongr
    _ = ((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * ((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * ((δ : ENNReal) ^ gt * ((s.card : ℕ) : ENNReal) ^ β) := by ring

end Split


section Window

variable {ι : Type u}

open Classical in
/-- **The branch-(ii) wiring at one scale: from the split's three factors to the mass gain.**

The two-scale split of the estimate and the three factors enter together as one existential package
`hfac` — together, because the three factors are statements *about the objects the split
produces*, and quantifying over all objects that merely satisfy the split's output clauses would
be a strictly stronger demand than GWZ's (a one-node retained set `tτ'` satisfies them and admits
no middle gain).  What this theorem discharges is everything on either side of that package:
cardinality bound and arithmetic below it
(`Kakeya.ML2Core.sum_shade_gain_of_split`), and the two mass discards above it
(`Kakeya.ML2Core.sum_shade_le_of_node_gain`). -/
theorem sum_shade_gain_of_window
    {β : ℝ} (hβ0 : 0 ≤ β) {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {Cu Kc lam : NNReal} (hlam0 : 0 < lam)
    {s u : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hus : u ⊆ s)
    (hdense : ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody))
    (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {Cstar : ENNReal} {ηl : ℕ → ℝ} {εd : ℝ} {Nw a b m : ℕ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar ηl εd Nw a b m)
    {t₁ : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b)
    (hcardseam : (u.card : NNReal) ≤ Kc * ((({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card :
        NNReal))
    (hmasspos : 0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade)
    {A : ENNReal} {εf gm εc κ g gt : ℝ}
    (hcardu : (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)))
    (hfac : ∃ (tτ' tθ' : Finset ι)
        (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
        (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
        (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (jτ jθ : ι),
        tτ' ⊆ t₁ ∧ tθ' ⊆ 𝒰.cover.indexSet a ∧ jτ ∈ t₁ ∧ jθ ∈ tθ' ∧ tτ'.Nonempty ∧
        ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
            i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) ({i ∈ u
                | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
                    (Tube.gridScale δ (Tube.ssfGridLen δ) b) : NNReal) : ENNReal)
              * ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                  𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
              * ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j
                  = jθ} : Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody) ∧
        ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
            ≤ (δ : ENNReal) ^ (-εf) * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι)).card : ENNReal) ^ β ∧
        ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} :
            Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
            ≤ (δ : ENNReal) ^ gm * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j =
                jθ} : Finset ι)).card : ENNReal) ^ β ∧
        ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
            ≤ (δ : ENNReal) ^ (-εc) * ((tθ'.card : ℕ) : ENNReal) ^ β)
    (hL : ∀ n₁ n₂ : ℕ, 0 < n₁ → 0 < n₂ →
      (n₁ : NNReal) ≤ δ ^ (-(4 : ℝ)) → (n₂ : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₁ δ *
          ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₂
            (Tube.gridScale δ (Tube.ssfGridLen δ) b) : NNReal) : ENNReal)
        * (((Cu ^ 5 : NNReal) : ENNReal)) ^ β ≤ (δ : ENNReal) ^ (-κ))
    (hexp : g ≤ gm - εf - εc - κ)
    (hmassloss : (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
        : ENNReal)
          * (∑ i ∈ s, volume (T i).shade)
        ≤ A * ∑ i ∈ u, volume (T i).shade)
    (habs : A * ((Kc : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
        : ENNReal)) * (δ : ENNReal) ^ g
        ≤ ((lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :
            ENNReal))
          * ((lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :
              ENNReal)) * (δ : ENNReal) ^ gt) :
    ∑ i ∈ s, volume (T i).shade
      ≤ (δ : ENNReal) ^ gt * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade) := by
  classical
  have hab : a ≤ b := hwin.coarse_lt_fine.le
  have hbN : b ≤ Tube.ssfGridLen δ := hwin.fine_le_gridLen
  have haN : a ≤ Tube.ssfGridLen δ := hab.trans hbN
  obtain ⟨tτ', tθ', Yτ', Yθ, Y', jτ, jθ, htτ', htθ', hjτ, hjθ, hτne, hprod, hfine, hmid,
    hcoarse⟩ := hfac
  have hs₁ne : (({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hmasspos
    simp at hmasspos
  have hs₁pos : 0 < (({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card := Finset.card_pos.mpr
      hs₁ne
  have hτpos : 0 < tτ'.card := Finset.card_pos.mpr hτne
  have hs₁card : (((({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card : ℕ) : NNReal) ≤ δ ^ (-(4
      : ℝ)) := by
    refine le_trans ?_ hcardu
    exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
  have hτcard : ((tτ'.card : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) := by
    refine le_trans ?_ hcardu
    have h1 : tτ'.card ≤ (ML2Reduction.activeNodes 𝒰.cover.toChain b).card :=
      Finset.card_le_card (htτ'.trans ht₁)
    have h2 := card_activeNodes_le_card (E := (EuclideanSpace ℝ (Fin 3))) 𝒰.cover.toChain b
    exact_mod_cast Nat.cast_le.mpr (h1.trans h2)
  exact sum_shade_gain_of_split hβ0 hδ0 hδ1 hlam0 hus hdense 𝒰.toChain hab haN hbN ht₁ htτ'
    htθ' (jθ := jθ) hjτ hprod hfine hmid hcoarse
    (hL _ _ hs₁pos hτpos hs₁card hτcard) hexp hmassloss hcardseam habs

end Window


section LossAbsorption

/-- **The two-scale loss of the estimate, absorbed into one `δ`-power.**

`Kakeya.ML2Reduction.spineScaleLoss` is `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C`
at dilation `1`, which is subpolynomial jointly in the inner cardinality and the inner scale
(`C_leApprox`).  The two applications the two-scale split makes live at the *leaf* scale `δ` and at
the *node* scale `σ ≥ δ`, and both cardinalities are below the crude ceiling `δ^{-4}`, so the whole
product is `δ^{-10 ε}` for the `ε` the approximation is read at. -/
theorem spineScaleLoss_prod_le {n : ℕ} {δ σ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδσ : δ ≤ σ) (hσ1 : σ ≤ 1) {n₁ n₂ : ℕ} (h1 : 0 < n₁) (h2 : 0 < n₂)
    (hn1 : (n₁ : NNReal) ≤ δ ^ (-(4 : ℝ))) (hn2 : (n₂ : NNReal) ≤ δ ^ (-(4 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) {Cε : NNReal}
    (hCε : ∀ N : ℕ, 0 < N → ∀ d : NNReal, 0 < d → d ≤ 1 → ∀ c : NNReal, 1 ≤ c →
      ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C n N d c
        ≤ Cε * c ^ n * d ^ (-ε) * (N : NNReal) ^ ε) :
    ML2Reduction.spineScaleLoss n n₁ δ * ML2Reduction.spineScaleLoss n n₂ σ
      ≤ Cε ^ 2 * δ ^ (-(10 * ε)) := by
  have hσ0 : 0 < σ := lt_of_lt_of_le hδ0 hδσ
  have e1 : ML2Reduction.spineScaleLoss n n₁ δ ≤ Cε * δ ^ (-ε) * ((n₁ : ℕ) : NNReal) ^ ε := by
    simpa [ML2Reduction.spineScaleLoss] using hCε n₁ h1 δ hδ0 hδ1 1 le_rfl
  have e2 : ML2Reduction.spineScaleLoss n n₂ σ ≤ Cε * σ ^ (-ε) * ((n₂ : ℕ) : NNReal) ^ ε := by
    simpa [ML2Reduction.spineScaleLoss] using hCε n₂ h2 σ hσ0 hσ1 1 le_rfl
  have hpow : ∀ k : ℕ, ((k : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      ((k : ℕ) : NNReal) ^ ε ≤ δ ^ (-(4 * ε)) := by
    intro k hk
    calc ((k : ℕ) : NNReal) ^ ε ≤ (δ ^ (-(4 : ℝ))) ^ ε := NNReal.rpow_le_rpow hk hε.le
      _ = δ ^ (-(4 * ε)) := by rw [← NNReal.rpow_mul]; ring_nf
  have g2 : σ ^ (-ε) ≤ δ ^ (-ε) := by
    have h := ML2Core.rpow_neg_le_rpow_neg_of_le hδσ hε.le
    rwa [← ENNReal.coe_rpow_of_ne_zero hσ0.ne', ← ENNReal.coe_rpow_of_ne_zero hδ0.ne',
      ENNReal.coe_le_coe] at h
  calc ML2Reduction.spineScaleLoss n n₁ δ * ML2Reduction.spineScaleLoss n n₂ σ
      ≤ (Cε * δ ^ (-ε) * δ ^ (-(4 * ε))) * (Cε * δ ^ (-ε) * δ ^ (-(4 * ε))) := by
        refine mul_le_mul' (e1.trans ?_) (e2.trans ?_)
        · exact mul_le_mul' le_rfl (hpow n₁ hn1)
        · exact mul_le_mul' (mul_le_mul' le_rfl g2) (hpow n₂ hn2)
    _ = Cε ^ 2 * (δ ^ (-ε) * δ ^ (-(4 * ε)) * (δ ^ (-ε) * δ ^ (-(4 * ε)))) := by ring
    _ = Cε ^ 2 * δ ^ (-(10 * ε)) := by
        simp only [← NNReal.rpow_add hδ0.ne']
        congr 1
        ring_nf

end LossAbsorption

section Package

open Classical in
/-- **The window branch, wired: the package's data plus the three factors give the dichotomy.**

This is the whole of branch (ii), at a fixed Katz--Tao exponent `ε₁`.  Branch (i) enters as the
package `hpkg` — the conclusion of `Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3` (or of its
`ε₁`-parametric companion `Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3_small`) at that
`ε₁` — and everything between it and `Kakeya.ML2Assembly.Dichotomy` is discharged here: the parent
seam (at both levels, `a = 0` and `1 ≤ a`), the two-scale split, cardinality bound, the
loss ledger of GWZ Lemma 5.11's two applications, the two mass discards and the exponent budget.

The exponents are free: the fine and coarse factors enter as losses `δ^{-εf}`, `δ^{-εc}` and the
middle factor as the gain `δ^{gm}`, subject only to `hexp`, which is
`Kakeya.ML2Core.mass_gain_of_three_factors`' budget at the multiscale constant `κ = ν`, the
internal gain `g = 10 ν` and the target `4 ν`.  The `10 ν` is what the pushback costs: `2ν` for the
package's own cardinality loss, `ν` for `StickyKakeya.totalLoss`, `2ν` for the two `λ⁻¹`'s, `ν` for
the seam's constants and `4ν` for the target itself. -/
theorem dichotomy_of_windowFactors
    {β ϖ : ℝ} {gain dens : ℝ → ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) {ε₁ : ℝ}
    (hpkg : ∃ (C : NNReal) (Kl cl : ℕ) (ε₂ e : ℝ) (N : ℕ) (η : ℕ → ℝ),
        1 ≤ C ∧ 4096 ≤ N ∧ e = 1 / Real.sqrt (N : ℝ) ∧
        η 0 = ML2Spine.spineNu β ϖ ε₁ gain dens ∧ 0 < η 0 ∧ η 0 ≤ 1 ∧
        ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η ∧
        ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
          0 < δ ∧ δ ≤ 1 ∧
          ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
            (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
            IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-(η 0))) →
            ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ (η 0) →
            (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
            s.Nonempty ∧
            (ML2Shading.DichotomyLeft (β / 2) s T
              ∨ ∃ u' ⊆ s, ∃ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∃ lam : NNReal,
                  δ ^ (η 0) / 2 ≤ lam ∧ 0 < lam ∧ u'.Nonempty ∧
                  (∀ i, (W i).toTube = (T i).toTube) ∧
                  (∀ i, (W i).shade ⊆ (T i).shade) ∧
                  ML2Shaded.HasDenseShading lam u' (fun i ↦ (T i).toShadedBody) ∧
                  ML2Shaded.HasComparableDensities lam⁻¹ u'
                      (fun i ↦ (T i).toShadedBody) ∧
                  (lam : ENNReal)
                        * (Tube.le_volume.c
                            (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
                        * (∑ i ∈ s, volume (T i).shade)
                      ≤ 2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0)))
                          * StickyKakeya.totalLoss C Kl cl δ)
                        * (Tube.volume_le.C
                            (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
                        * ∑ i ∈ u', volume (T i).shade ∧
                  (∑ i ∈ u', volume (T i).shade)
                      ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
                        * ∑ i ∈ u', volume (W i).shade ∧
                  volume (⋃ i ∈ u', (W i).shade) ≤ volume (⋃ i ∈ s, (T i).shade) ∧
                  (lam : ENNReal)
                      ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
                        * ShadedBody.fullness' u' (fun i ↦ (W i).toShadedBody) ∧
                  ∃ 𝒲 : ShadedUniformTubeSet u' W (ssfGridLen δ) (max C 4),
                    ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindow 𝒲.tubeUniform
                        ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) η e N a b m))
    {εf gm εc : ℝ} (hεc : 0 < εc)
    (hexp : 10 * ML2Spine.spineNu β ϖ ε₁ gain dens
      ≤ gm - εf - εc - ML2Spine.spineNu β ϖ ε₁ gain dens)
    (hfac : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
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
        Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^
            (-(ML2Spine.spineNu β ϖ ε₁ gain dens)) →
        ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
        (δ : NNReal) ^ (ML2Spine.spineNu β ϖ ε₁ gain dens) / 2 ≤ lam →
        (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
        Cstar ≤ (δ : ENNReal) ^ (-(2 * (ML2Spine.spineNu β ϖ ε₁ gain dens))) →
        0 ≤ ηl m → ηl m ≤ ε₁ / 25 →
        ((Cu : NNReal) : ENNReal) ^ (1 - β) ≤ (δ : ENNReal) ^ (-(εc)) →
        0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
        δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
        Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
        Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
        ∃ (tτ' tθ' : Finset ι)
        (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
        (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
        (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (jτ jθ : ι),
        tτ' ⊆ t₁ ∧ tθ' ⊆ 𝒰.cover.indexSet a ∧ jτ ∈ t₁ ∧ jθ ∈ tθ' ∧ tτ'.Nonempty ∧
        ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
            i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) ({i ∈ u
                | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
                    (Tube.gridScale δ (Tube.ssfGridLen δ) b) : NNReal) : ENNReal)
              * ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                  𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
              * ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j
                  = jθ} : Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody) ∧
        ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
            ≤ (δ : ENNReal) ^ (-(εf)) * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι)).card : ENNReal) ^ β ∧
        ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} :
            Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
            ≤ (δ : ENNReal) ^ (gm) * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j =
                jθ} : Finset ι)).card : ENNReal) ^ β ∧
        ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
            ≤ (δ : ENNReal) ^ (-(εc)) * ((tθ'.card : ℕ) : ENNReal) ^ β) :
    ML2Assembly.Dichotomy.{u} β (β / 2)
      (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) (ML2Spine.spineNu β ϖ ε₁ gain dens) := by
  classical
  obtain ⟨C, Kl, cl, ε₂, e, Nsp, η, hC, hNsp, he, hη0nu, hη00, hη01, hspine, hev⟩ := hpkg
  rw [← hη0nu]
  refine dichotomy_of_dichotomyLeft_or_gain ?_
  -- the two seams, and the thresholds, all chosen before the scale
  obtain ⟨M₁, hM₁0, hseam₁⟩ := exists_windowSeam.{u} (E := EuclideanSpace ℝ (Fin 3))
  obtain ⟨M₂, hM₂0, hseam₂⟩ := exists_coarseWindowSeam.{u} (E := EuclideanSpace ℝ (Fin 3))
  set Mseam : ℕ := max M₁ M₂ with hMseam
  have hν0 : 0 < η 0 := hη00
  have hcc0 : 0 < Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
    Tube.le_volume.c_pos _
  have hCuu1 : (1 : NNReal) ≤ max C 4 := le_trans hC (le_max_left _ _)
  obtain ⟨d1, hd10, hd1⟩ :=
    ML2Reduction.exists_threshold_coe_const_le_rpow_neg
      (C := max 1 (8 * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2 *
        ((Mseam : NNReal) * max C 4 * max C 4) /
        (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2))
      (le_max_left _ _) (κ := η 0) hν0
  obtain ⟨Cε, hCε⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (η 0 / 20) (by positivity)
  obtain ⟨d2, hd20, hd2⟩ :=
    ML2Reduction.exists_threshold_const_le_rpow_neg
      (C := max 1 (Cε ^ 2 * (max C 4) ^ 5)) (le_max_left _ _)
      (κ := η 0 / 2) (by positivity)
  obtain ⟨dT, hdT0, hdT1, hdT⟩ :=
    StickyKakeya.exists_threshold_totalLoss_le C hC Kl cl (η 0) hν0
  obtain ⟨dL, hdL0, hdL1, hdL⟩ := exists_threshold_two_mul_ssfGridLen_le_log
  obtain ⟨d3, hd30, hd3⟩ :=
    ML2Reduction.exists_threshold_coe_const_le_rpow_neg (C := C) hC (κ := η 0) hν0
  obtain ⟨d4, hd40, hd4⟩ :=
    ML2Reduction.exists_threshold_coe_const_le_rpow_neg (C := max C 4) hCuu1 (κ := εc) hεc
  filter_upwards [hev, hfac, ML2Assembly.eventually_card_thresholds,
    Ioc_mem_nhdsGT hd10, Ioc_mem_nhdsGT hd20, Ioc_mem_nhdsGT hdT0, Ioc_mem_nhdsGT hdL0,
    Ioc_mem_nhdsGT hd30, Ioc_mem_nhdsGT hd40]
    with δ hpkgδ hfacδ hthr hm1 hm2 hmT hmL hm3 hm4
  rw [← hη0nu] at hfacδ
  obtain ⟨hδ0, hδ1, hbody⟩ := hpkgδ
  obtain ⟨-, -, hδC⟩ := hthr
  intro ι s T hball hKTs hfull hcard
  rcases (hbody s T hball hKTs hfull hcard).2 with hleft | hwindow
  · exact Or.inl hleft
  refine Or.inr ?_
  obtain ⟨u', hu's, W, lam, hlamlow, hlam0, hu'ne, htube, hshade, hdenseu, hcompu,
    hmassloss, hpoly, hunion, hfullpoly, 𝒲, aa, bb, mm, hwinW⟩ := hwindow
  -- the hierarchy, read on the family whose masses the dichotomy states
  obtain ⟨𝒰, hwin⟩ : ∃ 𝒰 : Tube.UniformTubeSet u' (fun i ↦ (T i).toTube)
      (Tube.ssfGridLen δ) (max C 4),
      ML2Reduction.IsKatzTaoDividingWindow 𝒰
        ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) η e Nsp aa bb mm := by
    have hfun : (fun i ↦ (W i).toTube) = (fun i ↦ (T i).toTube) := funext htube
    exact hfun ▸ ⟨𝒲.tubeUniform, hwinW⟩
  -- the crude cardinality ceiling
  have hcard4 : (s.card : ℝ) ≤ (δ : ℝ) ^ (-4 : ℝ) :=
    ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s T hball hη01 hKTs
  have hcardu : (u'.card : NNReal) ≤ δ ^ (-(4 : ℝ)) := by
    have h1 : ((u'.card : ℕ) : ℝ) ≤ (δ : ℝ) ^ (-4 : ℝ) := by
      refine le_trans ?_ hcard4
      exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hu's)
    have h2 : (((δ ^ (-(4 : ℝ)) : NNReal)) : ℝ) = (δ : ℝ) ^ (-4 : ℝ) := by
      rw [NNReal.coe_rpow]
    rw [← NNReal.coe_le_coe, h2]
    exact_mod_cast h1
  -- the seam
  have hballu' : ∀ i ∈ u', (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun i hi ↦ hball i (hu's hi)
  obtain ⟨v, t₀, t₁, ht₀, ht₁, hballt₀, hballt, hballs, hcn, hcardseam, hδτ, hτθ, hθ1⟩ :
      ∃ (v : EuclideanSpace ℝ (Fin 3)) (t₀ t₁ : Finset ι),
        (aa ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain aa) ∧
        t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain bb ∧
        (aa ≠ 0 → ∀ k ∈ t₀, ((𝒰.cover.tube aa k).translate v).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
        (∀ j ∈ t₁, ((𝒰.cover.tube bb j).translate v).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
        (∀ i ∈ ({i ∈ u' | 𝒰.cover.assign bb i ∈ t₁} : Finset ι),
          ((T i).translate v).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
        (aa ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain aa bb j ∈ t₀) ∧
        (u'.card : NNReal) ≤ (Mseam : NNReal) * max C 4 * max C 4
          * ((({i ∈ u' | 𝒰.cover.assign bb i ∈ t₁} : Finset ι)).card : NNReal) ∧
        δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) bb ∧
        Tube.gridScale δ (Tube.ssfGridLen δ) bb ≤ Tube.gridScale δ (Tube.ssfGridLen δ) aa ∧
        Tube.gridScale δ (Tube.ssfGridLen δ) aa ≤ 1 := by
    have hMcast : ∀ n : ℕ, n ≤ Mseam → ((n : NNReal) ≤ (Mseam : NNReal)) := by
      intro n hn; exact_mod_cast Nat.cast_le.mpr hn
    rcases eq_or_ne aa 0 with ha0 | ha0
    · obtain ⟨v, t₁, ht₁, hballt, hballs, hcardseam, hδτ, hτθ, hθ1⟩ :=
        hseam₁ 𝒰 hδ0 hδ1 (hdL δ hδ0 hmL.2) hwin hballu'
      refine ⟨v, ∅, t₁, fun h ↦ absurd ha0 h, ht₁, fun h ↦ absurd ha0 h, hballt, hballs,
        fun h ↦ absurd ha0 h, ?_, hδτ, hτθ, hθ1⟩
      refine hcardseam.trans (mul_le_mul' (mul_le_mul' (mul_le_mul'
        (hMcast M₁ (le_max_left _ _)) le_rfl) le_rfl) le_rfl)
    · obtain ⟨v, t₀, t₁, ht₀, ht₁, hballt₀, hballt, hballs, hcn, hcardseam, hδτ, hτθ, hθ1⟩ :=
        hseam₂ 𝒰 hδ0 hδ1 (Nat.one_le_iff_ne_zero.mpr ha0) (hdL δ hδ0 hmL.2) hwin hballu'
      refine ⟨v, t₀, t₁, fun _ ↦ ht₀, ht₁, fun _ ↦ hballt₀, hballt, hballs, fun _ ↦ hcn,
        ?_, hδτ, hτθ, hθ1⟩
      refine hcardseam.trans (mul_le_mul' (mul_le_mul' (mul_le_mul'
        (hMcast M₂ (le_max_right _ _)) le_rfl) le_rfl) le_rfl)
  -- mass positivity, transported across both discards
  have hmass0 : 0 < ∑ i ∈ s, volume (T i).shade := by
    rw [pos_iff_ne_zero]
    intro h
    have hf : ((ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) : NNReal) : ENNReal) = 0 := by
      rw [ShadedBody.fullness_def, h, ENNReal.zero_div]
    have hf0 : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) = 0 := by exact_mod_cast hf
    have hpow : (0 : NNReal) < δ ^ (η 0) := NNReal.rpow_pos hδ0
    rw [ge_iff_le, hf0] at hfull
    exact absurd hfull (not_le.mpr hpow)
  have hcc0E : ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal)
      : ENNReal) ≠ 0 := by
    simpa using (Tube.le_volume.c_pos (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))).ne'
  have hlam0E : ((lam : NNReal) : ENNReal) ≠ 0 := by simpa using hlam0.ne'
  have hmassu' : 0 < ∑ i ∈ u', volume (T i).shade := by
    rw [pos_iff_ne_zero]
    intro h
    rw [h, mul_zero] at hmassloss
    have h0 : (lam : ENNReal)
        * ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal) : ENNReal)
        * (∑ i ∈ s, volume (T i).shade) = 0 := le_antisymm hmassloss (by simp)
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hlam0E h2
      · exact hcc0E h2
    · exact hmass0.ne' h1
  have hmasspos : 0 < ∑ i ∈ ({i ∈ u' | 𝒰.cover.assign bb i ∈ t₁} : Finset ι),
      volume (T i).shade := by
    have hret := sum_shade_le_of_node_subfamily (E := EuclideanSpace ℝ (Fin 3)) hδ1
      (Finset.filter_subset (fun i ↦ 𝒰.cover.assign bb i ∈ t₁) u') hdenseu hcardseam
    rw [pos_iff_ne_zero]
    intro h
    rw [h, mul_zero] at hret
    have h0 : (lam : ENNReal)
        * ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal) : ENNReal)
        * (∑ i ∈ u', volume (T i).shade) = 0 := le_antisymm hret (by simp)
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hlam0E h2
      · exact hcc0E h2
    · exact hmassu'.ne' h1
  -- the two-scale loss, absorbed
  have hσb1 : Tube.gridScale δ (Tube.ssfGridLen δ) bb ≤ 1 := le_trans hτθ hθ1
  have hCuu5one : (1 : NNReal) ≤ (max C 4 : NNReal) ^ 5 := one_le_pow₀ hCuu1
  have hCuu5ne : ((max C 4 : NNReal) ^ 5) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hCuu5one)
  have hLfinal : ∀ n₁ n₂ : ℕ, 0 < n₁ → 0 < n₂ →
      (n₁ : NNReal) ≤ δ ^ (-(4 : ℝ)) → (n₂ : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₁ δ *
          ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₂
            (Tube.gridScale δ (Tube.ssfGridLen δ) bb) : NNReal) : ENNReal)
        * ((((max C 4 : NNReal) ^ 5 : NNReal) : ENNReal)) ^ β ≤ (δ : ENNReal) ^ (-(η 0)) := by
    intro n₁ n₂ hn1p hn2p hn1 hn2
    have hprod := spineScaleLoss_prod_le hδ0 hδ1 hδτ hσb1 hn1p hn2p hn1 hn2
      (ε := η 0 / 20) (by positivity) hCε
    have hβpow : ((max C 4 : NNReal) ^ 5) ^ β ≤ (max C 4 : NNReal) ^ 5 := by
      calc ((max C 4 : NNReal) ^ 5) ^ β ≤ ((max C 4 : NNReal) ^ 5) ^ (1 : ℝ) :=
            NNReal.rpow_le_rpow_of_exponent_le hCuu5one hβ1
        _ = (max C 4 : NNReal) ^ 5 := by rw [NNReal.rpow_one]
    rw [← ENNReal.coe_rpow_of_ne_zero hCuu5ne, ← ENNReal.coe_mul,
      ← ENNReal.coe_rpow_of_ne_zero hδ0.ne', ENNReal.coe_le_coe]
    calc (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₁ δ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₂
              (Tube.gridScale δ (Tube.ssfGridLen δ) bb))
          * (((max C 4 : NNReal) ^ 5) ^ β)
        ≤ (Cε ^ 2 * δ ^ (-(10 * (η 0 / 20)))) * ((max C 4 : NNReal) ^ 5) :=
          mul_le_mul' hprod hβpow
      _ = (Cε ^ 2 * (max C 4 : NNReal) ^ 5) * δ ^ (-(η 0 / 2)) := by
          rw [show (10 : ℝ) * (η 0 / 20) = η 0 / 2 by ring]; ring
      _ ≤ δ ^ (-(η 0 / 2)) * δ ^ (-(η 0 / 2)) := by
          gcongr
          exact le_trans (le_max_right _ _) (hd2 δ hδ0 hm2.2)
      _ = δ ^ (-(η 0)) := by
          rw [← NNReal.rpow_add hδ0.ne']
          congr 1
          ring
  -- the pushback ledger, absorbed
  have hlamE : (δ : ENNReal) ^ (η 0) ≤ 2 * (lam : ENNReal) := by
    have hnn : (δ : NNReal) ^ (η 0) ≤ 2 * lam := by
      rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 2)] at hlamlow
      calc (δ : NNReal) ^ (η 0) ≤ lam * 2 := hlamlow
        _ = 2 * lam := by ring
    calc (δ : ENNReal) ^ (η 0) = (((δ : NNReal) ^ (η 0) : NNReal) : ENNReal) :=
          (ENNReal.coe_rpow_of_ne_zero hδ0.ne' _).symm
      _ ≤ ((2 * lam : NNReal) : ENNReal) := ENNReal.coe_le_coe.mpr hnn
      _ = 2 * (lam : ENNReal) := by push_cast; ring
  have habs : (2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0)))
          * StickyKakeya.totalLoss C Kl cl δ)
        * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * ((((Mseam : NNReal) * max C 4 * max C 4 : NNReal) : ENNReal)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * (δ : ENNReal) ^ (10 * η 0)
      ≤ ((lam : ENNReal)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * ((lam : ENNReal)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * (δ : ENNReal) ^ (4 * η 0) := by
    have hδEne : (δ : ENNReal) ≠ 0 := by simpa using hδ0.ne'
    have hδEtop : (δ : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
    have hA : ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0))) = (δ : ENNReal) ^ (-(η 0 + η 0)) :=
      ofReal_rpow_coe hδ0 _
    have hT : StickyKakeya.totalLoss C Kl cl δ ≤ (δ : ENNReal) ^ (-(η 0)) := by
      rw [← ofReal_rpow_coe hδ0]
      exact hdT hδ0 hmT.2
    have hcc2ne : (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2 ≠ 0 :=
      pow_ne_zero _ hcc0.ne'
    have hconstNN : (8 : NNReal)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2
          * ((Mseam : NNReal) * max C 4 * max C 4)
        ≤ (max 1 (8 * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2 *
            ((Mseam : NNReal) * max C 4 * max C 4) /
            (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2))
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2 := by
      refine le_trans (le_of_eq ?_) (mul_le_mul' (le_max_right _ _) le_rfl)
      rw [div_mul_cancel₀ _ hcc2ne]
    have hconst : (8 : ENNReal)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2
          * (((Mseam : NNReal) * max C 4 * max C 4 : NNReal) : ENNReal)
        ≤ (δ : ENNReal) ^ (-(η 0))
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2 := by
      have h1 : ((8 * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2
            * ((Mseam : NNReal) * max C 4 * max C 4) : NNReal) : ENNReal)
          ≤ (((max 1 (8 * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2 *
              ((Mseam : NNReal) * max C 4 * max C 4) /
              (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2))
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2
              : NNReal) : ENNReal) := ENNReal.coe_le_coe.mpr hconstNN
      have h2 := hd1 δ hδ0 hm1.2
      push_cast at h1 ⊢
      exact h1.trans (mul_le_mul' h2 le_rfl)
    have e1 : (δ : ENNReal) ^ (-(η 0)) * ((δ : ENNReal) ^ (-(η 0 + η 0))
          * (δ : ENNReal) ^ (-(η 0)) * (δ : ENNReal) ^ (10 * η 0))
        = (δ : ENNReal) ^ (6 * η 0) := by
      rw [← ENNReal.rpow_add _ _ hδEne hδEtop, ← ENNReal.rpow_add _ _ hδEne hδEtop,
        ← ENNReal.rpow_add _ _ hδEne hδEtop]
      congr 1
      ring
    have e2 : (δ : ENNReal) ^ (η 0) * (δ : ENNReal) ^ (η 0) * (δ : ENNReal) ^ (4 * η 0)
        = (δ : ENNReal) ^ (6 * η 0) := by
      rw [← ENNReal.rpow_add _ _ hδEne hδEtop, ← ENNReal.rpow_add _ _ hδEne hδEtop]
      congr 1
      ring
    refine (ENNReal.mul_le_mul_iff_left (by norm_num : (4 : ENNReal) ≠ 0)
      (by norm_num : (4 : ENNReal) ≠ (⊤ : ENNReal))).mp ?_
    calc ((2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0)))
              * StickyKakeya.totalLoss C Kl cl δ)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
            * ((((Mseam : NNReal) * max C 4 * max C 4 : NNReal) : ENNReal)
              * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
            * (δ : ENNReal) ^ (10 * η 0)) * 4
        ≤ ((2 * ((δ : ENNReal) ^ (-(η 0 + η 0)) * (δ : ENNReal) ^ (-(η 0)))
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
            * ((((Mseam : NNReal) * max C 4 * max C 4 : NNReal) : ENNReal)
              * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
            * (δ : ENNReal) ^ (10 * η 0)) * 4 := by
          rw [hA]; gcongr
      _ = ((8 : ENNReal)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2
            * (((Mseam : NNReal) * max C 4 * max C 4 : NNReal) : ENNReal))
          * ((δ : ENNReal) ^ (-(η 0 + η 0)) * (δ : ENNReal) ^ (-(η 0))
              * (δ : ENNReal) ^ (10 * η 0)) := by ring
      _ ≤ ((δ : ENNReal) ^ (-(η 0))
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2)
          * ((δ : ENNReal) ^ (-(η 0 + η 0)) * (δ : ENNReal) ^ (-(η 0))
              * (δ : ENNReal) ^ (10 * η 0)) := by gcongr
      _ = (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2
          * ((δ : ENNReal) ^ (-(η 0)) * ((δ : ENNReal) ^ (-(η 0 + η 0))
              * (δ : ENNReal) ^ (-(η 0)) * (δ : ENNReal) ^ (10 * η 0))) := by ring
      _ = (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2
          * (δ : ENNReal) ^ (6 * η 0) := by rw [e1]
      _ = (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2
          * ((δ : ENNReal) ^ (η 0) * (δ : ENNReal) ^ (η 0)) * (δ : ENNReal) ^ (4 * η 0) := by
          rw [← e2]; ring
      _ ≤ (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2
          * ((2 * (lam : ENNReal)) * (2 * (lam : ENNReal))) * (δ : ENNReal) ^ (4 * η 0) := by
          gcongr
      _ = (((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * ((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * (δ : ENNReal) ^ (4 * η 0)) * 4 := by ring
  -- and the three factors, at this scale
  -- the four numeric inputs of the coarse factor's interface
  have hδEne : (δ : ENNReal) ≠ 0 := by simpa using hδ0.ne'
  have hδEtop : (δ : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
  have hCstarB : (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ
      ≤ (δ : ENNReal) ^ (-(2 * η 0)) := by
    have hT : StickyKakeya.totalLoss C Kl cl δ ≤ (δ : ENNReal) ^ (-(η 0)) := by
      rw [← ofReal_rpow_coe hδ0]
      exact hdT hδ0 hmT.2
    calc (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ
        ≤ (δ : ENNReal) ^ (-(η 0)) * (δ : ENNReal) ^ (-(η 0)) :=
          mul_le_mul' (hd3 δ hδ0 hm3.2) hT
      _ = (δ : ENNReal) ^ (-(2 * η 0)) := by
          rw [← ENNReal.rpow_add _ _ hδEne hδEtop]
          congr 1
          ring
  have hηlm0 : (0 : ℝ) ≤ η mm := (hspine.rung_pos mm).le
  have hηlmax : η mm ≤ ε₁ / 25 := by
    have h1 : η mm ≤ η Nsp := hspine.rung_mono hwin.step_lt.le
    have h2 : η Nsp = e := hspine.rung_top
    have h3 : e ≤ ε₂ / 5 := hspine.div_le
    have h4 : ε₂ ≤ ε₁ / 5 := hspine.eps₂_le_everyScale
    rw [h2] at h1
    linarith
  have hCubnd : (((max C 4 : NNReal)) : ENNReal) ^ (1 - β) ≤ (δ : ENNReal) ^ (-εc) := by
    have hone : (1 : ENNReal) ≤ ((max C 4 : NNReal) : ENNReal) := by exact_mod_cast hCuu1
    calc (((max C 4 : NNReal)) : ENNReal) ^ (1 - β)
        ≤ (((max C 4 : NNReal)) : ENNReal) ^ (1 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_le hone (by linarith)
      _ = (((max C 4 : NNReal)) : ENNReal) := ENNReal.rpow_one _
      _ ≤ (δ : ENNReal) ^ (-εc) := hd4 δ hδ0 hm4.2
  have hmaxu' : Kakeya.maxDensity u' (fun i ↦ (T i).toConvexSpaceBody)
      ≤ (δ : ENNReal) ^ (-(η 0)) := (Kakeya.maxDensity_mono _ hu's).trans hKTs
  have hs₁ne' : ({i ∈ u' | 𝒰.cover.assign bb i ∈ t₁} : Finset ι).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hmasspos
    simp at hmasspos
  have hune : u'.Nonempty := hs₁ne'.mono (Finset.filter_subset _ _)
  have hfacw := hfacδ u' T (max C 4) lam 𝒰
    ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) η e Nsp aa bb mm hwin
    v t₀ t₁ ht₁ hballt hballs ht₀ hcn hballt₀ hballu' hune hmaxu' hdenseu hlamlow hcardu
    hCstarB hηlm0 hηlmax hCubnd hmasspos hδτ hτθ hθ1
  refine sum_shade_gain_of_window (β := β) hβ0.le hδ0 hδ1 hlam0 hu's hdenseu 𝒰 hwin ht₁
    hcardseam hmasspos
    (εf := εf) (gm := gm) (εc := εc) (κ := η 0) (g := 10 * η 0) (gt := 4 * η 0)
    hcardu hfacw hLfinal (by linarith) hmassloss habs

end Package

section TopLevel

open Classical in
/-- **`GeometricCoreAt` from the three factors at the window.**

Branch (i) is `Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3`; branch (ii) is
`Kakeya.ML2Core.dichotomy_of_windowFactors`.  The single hypothesis is the **three factors**, at
the exponents the budget forces: the fine and coarse factors as losses `δ^{-ν}` and the middle
factor as the gain `δ^{13 ν}`, where `ν = Kakeya.ML2Spine.spineNu β ϖ ε₁ gain dens` is the drop
`Kakeya.ML2Assembly.GeometricCoreAt` returns.

`13 = 10 + 1 + 1 + 1`: the `10ν` is the internal gain the pushback consumes (see
`Kakeya.ML2Core.dichotomy_of_windowFactors`), and the last three are the fine loss, the coarse loss
and the multiscale constant. -/
theorem geometricCoreAt_of_windowFactors
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))
    (hfac : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
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
        Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^
            (-(ML2Spine.spineNu β ϖ ε₁ gain dens)) →
        ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
        (δ : NNReal) ^ (ML2Spine.spineNu β ϖ ε₁ gain dens) / 2 ≤ lam →
        (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
        Cstar ≤ (δ : ENNReal) ^ (-(2 * (ML2Spine.spineNu β ϖ ε₁ gain dens))) →
        0 ≤ ηl m → ηl m ≤ ε₁ / 25 →
        ((Cu : NNReal) : ENNReal) ^ (1 - β) ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain
            dens)) →
        0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
        δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
        Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
        Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
        ∃ (tτ' tθ' : Finset ι)
        (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
        (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
        (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (jτ jθ : ι),
        tτ' ⊆ t₁ ∧ tθ' ⊆ 𝒰.cover.indexSet a ∧ jτ ∈ t₁ ∧ jθ ∈ tθ' ∧ tτ'.Nonempty ∧
        ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
            i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) ({i ∈ u
                | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
                    (Tube.gridScale δ (Tube.ssfGridLen δ) b) : NNReal) : ENNReal)
              * ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                  𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
              * ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j
                  = jθ} : Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody) ∧
        ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
            ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens)) * ((({i ∈ ({i ∈ u |
                𝒰.cover.assign b i ∈ t₁} : Finset ι) | 𝒰.cover.assign b i = jτ} : Finset ι)).card
                : ENNReal) ^ β ∧
        ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} :
            Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
            ≤ (δ : ENNReal) ^ (13 * ML2Spine.spineNu β ϖ ε₁ gain dens) * ((({j ∈ tτ' |
                ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι)).card : ENNReal) ^
                β ∧
        ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
            ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens)) * ((tθ'.card : ℕ) : ENNReal)
                ^ β) :
    ML2Assembly.GeometricCoreAt.{u} := by
  classical
  refine geometricCoreAt_of_pointwise (fun β ϖ gain dens hβ0 hβ1 hp hKT hF ↦ ?_)
  obtain ⟨ε₁, hε₁, C, Kl, cl, ε₂, e, Nsp, η, hC, hNsp, he, hη0nu, hη00, hη01, hspine, hev⟩ :=
    exists_dichotomyLeft_or_window_dim3.{u} hSFE hβ0 hβ1 hp.window_pos hp.gain_pos hp.dens_pos
  refine ⟨ε₁, hε₁, ML2Spine.spineNu β ϖ ε₁ gain dens, ?_, ?_, ?_⟩
  · rw [← hη0nu]; exact hη00
  · rw [← hη0nu]; exact hη01
  · exact dichotomy_of_windowFactors hβ0 hβ1
      ⟨C, Kl, cl, ε₂, e, Nsp, η, hC, hNsp, he, hη0nu, hη00, hη01, hspine, hev⟩
      (εf := ML2Spine.spineNu β ϖ ε₁ gain dens)
      (gm := 13 * ML2Spine.spineNu β ϖ ε₁ gain dens)
      (εc := ML2Spine.spineNu β ϖ ε₁ gain dens) (by rw [← hη0nu]; exact hη00) (by linarith)
      (hfac β ϖ gain dens hβ0 hβ1 hp hKT hF ε₁ hε₁)

end TopLevel

section SplitProducer

variable {ι : Type u}

open Classical in
/-- **the component estimates at a dividing window, at both window indices.**

The seam has been run (`Kakeya.ML2Core.exists_windowSeam` at `a = 0`,
`Kakeya.ML2Core.exists_coarseWindowSeam` at `1 ≤ a`, whose outputs are the binder block below);
this runs `Kakeya.ML2Reduction.exists_spineTwoScale` through the right one of the two existing
wrappers and returns the two-scale split together with the coarse ball condition the coarse
factor needs when `a ≠ 0`.

It exists so that a producer of the **middle factor** — the one hypothesis of
`Kakeya.ML2Core.geometricCoreAt_of_middleFactor` — does not have to re-derive the split: it calls
this and then proves its own bound at the objects this returns.  The split cannot be moved into
the consumer, because the middle factor is a statement *about the objects the split produces* and
is false for an arbitrary retained node set (a one-node `tτ'` gives a one-node coarse fibre, whose
multiplicity is `1`, above every gain `δ^{g}` with `g > 0`). -/
theorem exists_twoScaleSplit_at_window {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {Cu : NNReal} {u : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {Cstar : ENNReal} {ηl : ℕ → ℝ} {εd : ℝ} {Nw a b m : ℕ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar ηl εd Nw a b m)
    (v : (EuclideanSpace ℝ (Fin 3))) {t₀ t₁ : Finset ι}
    (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b)
    (hballt : ∀ j ∈ t₁,
      ((𝒰.cover.tube b j).translate v).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin
          3))) 1)
    (hballs : ∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι),
      ((T i).translate v).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1)
    (ht₀ : a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a)
    (hcn : a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀)
    (hballt₀ : a ≠ 0 → ∀ k ∈ t₀,
      ((𝒰.cover.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin
          3))) 1)
    (hmasspos : 0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade) :
    ∃ tτ' ⊆ t₁, ∃ tθ' ⊆ 𝒰.cover.indexSet a,
      ∃ (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
        (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
        (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
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
              * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)) := by
  classical
  have hab : a ≤ b := hwin.coarse_lt_fine.le
  have hbN : b ≤ Tube.ssfGridLen δ := hwin.fine_le_gridLen
  have haN : a ≤ Tube.ssfGridLen δ := hab.trans hbN
  obtain ⟨hδτ, hτθ, hθ1⟩ := window_scales hδ0 hδ1 hwin
  rcases eq_or_ne a 0 with ha0 | ha0
  · obtain ⟨tτ', htτ', tθ', htθ', Yτ, Yτ', Yθ, Y', -, -, hYτ', hYθ, hY'tube, -, -,
        hne, href1, -, -, hfull2, hprod⟩ :=
      exists_spineTwoScale_ofChain_translated (E := (EuclideanSpace ℝ (Fin 3))) hδ0
        𝒰.cover.toChain hab haN hbN hδτ hτθ hθ1 v ht₁ hballt hballs
    obtain ⟨hτne, hθne⟩ := hne hmasspos
    exact ⟨tτ', htτ', tθ', htθ', Yτ', Yθ, Y', hYτ', hYθ, hY'tube,
      (fun h ↦ absurd ha0 h), hτne, hθne, href1, hfull2, hprod⟩
  · obtain ⟨tτ', htτ', tθ', htθ'0, Yτ, Yτ', Yθ, Y', -, -, hYτ', hYθ, hY'tube, -, -, hballθ,
        hne, href1, -, -, hfull2, hprod⟩ :=
      exists_spineTwoScale_ofChain_coarseSeam (E := (EuclideanSpace ℝ (Fin 3))) hδ0
        𝒰.cover.toChain hab hbN hδτ hτθ hθ1 v ht₁ (hcn ha0) (hballt₀ ha0) hballt hballs
    obtain ⟨hτne, hθne⟩ := hne hmasspos
    exact ⟨tτ', htτ', tθ', htθ'0.trans ((ht₀ ha0).trans
        (ML2Reduction.activeNodes_subset _ a)), Yτ', Yθ, Y', hYτ', hYθ, hY'tube,
      (fun _ ↦ hballθ), hτne, hθne, href1, hfull2, hprod⟩

end SplitProducer

section MiddleOnly

open Classical in
/-- **`GeometricCoreAt` from the MIDDLE FACTOR alone.**

Every other input of branch (ii) is discharged: branch (i) at a Katz--Tao exponent `ε₁` small
enough to put the spine's drop `ν` below both Katz--Tao density exponents
(`Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3_small` and
`Kakeya.ML2Core.spineNu_le_div_25`), the parent seam at both levels, the two-scale split, the
**fine factor** (`Kakeya.ML2Core.exists_fine_factor_at_window`), the **coarse factor**
(`Kakeya.ML2Core.exists_coarse_factor_complete`), cardinality bound, the loss ledger of
GWZ Lemma 5.11's two applications and the two mass discards.

The accuracy `ε` at which the two Katz--Tao factors are read is a free parameter, and the middle
factor is asked for the gain `2ε + 14 ε₁/25`, which is exactly what the budget needs.

**So GWZ Main Lemma 2's geometric core reduces to the estimate — the rescaled datum `(𝕋̃, Ỹ)` at
`δ̃ = τ/θ` and its plank factoring — and to nothing else.** -/
theorem geometricCoreAt_of_middleFactor (ε : ℝ) (hε : 0 < ε)
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))
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
        Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^
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
                  ι)).card : ENNReal) ^ β) :
    ML2Assembly.GeometricCoreAt.{u} := by
  classical
  refine geometricCoreAt_of_pointwise (fun β ϖ gain dens hβ0 hβ1 hp hKT hF ↦ ?_)
  obtain ⟨ηf, hηf, hfineev⟩ :=
    exists_fine_factor_at_window.{u} (E := (EuclideanSpace ℝ (Fin 3))) hβ0.le hKT hε
  obtain ⟨ηc, hηc, hcoarseev⟩ :=
    exists_coarse_factor_complete.{u} (E := (EuclideanSpace ℝ (Fin 3))) hβ0.le hβ1 hKT hε
  obtain ⟨ε₁₀, hε₁₀, hsmall⟩ :=
    exists_dichotomyLeft_or_window_dim3_small.{u} hSFE hβ0 hβ1 hp.window_pos hp.gain_pos hp.dens_pos
  have hminpos : 0 < min ηf ηc := lt_min hηf hηc
  have hminf : min ηf ηc ≤ ηf := min_le_left _ _
  have hminc : min ηf ηc ≤ ηc := min_le_right _ _
  have hε₁ : 0 < min ε₁₀ (25 * min ηf ηc / 2) := lt_min hε₁₀ (by positivity)
  obtain ⟨C, Kl, cl, ε₂, e, Nsp, η, hC, hNsp, he, hη0nu, hη00, hη01, hspine, hev⟩ :=
    hsmall (min ε₁₀ (25 * min ηf ηc / 2)) hε₁ (min_le_left _ _)
  have hν0 : 0 < ML2Spine.spineNu β ϖ (min ε₁₀ (25 * min ηf ηc / 2)) gain dens := by
    rw [← hη0nu]
    exact hη00
  have hν25 : ML2Spine.spineNu β ϖ (min ε₁₀ (25 * min ηf ηc / 2)) gain dens ≤ min ε₁₀ (25 * min ηf
      ηc / 2) / 25 :=
    spineNu_le_div_25 hβ0 hβ1 hp.window_pos hε₁ hp.gain_pos hp.dens_pos
  have hνhalf : ML2Spine.spineNu β ϖ (min ε₁₀ (25 * min ηf ηc / 2)) gain dens ≤ min ηf ηc / 2 := by
    have h : min ε₁₀ (25 * min ηf ηc / 2) ≤ 25 * min ηf ηc / 2 := min_le_right _ _
    linarith
  refine ⟨min ε₁₀ (25 * min ηf ηc / 2), hε₁, ML2Spine.spineNu β ϖ (min ε₁₀ (25 * min ηf ηc / 2))
      gain dens, hν0, ?_, ?_⟩
  · rw [← hη0nu]; exact hη01
  refine dichotomy_of_windowFactors hβ0 hβ1
    ⟨C, Kl, cl, ε₂, e, Nsp, η, hC, hNsp, he, hη0nu, hη00, hη01, hspine, hev⟩
    (εf := ε) (gm := 2 * ε + 14 * (min ε₁₀ (25 * min ηf ηc / 2) / 25))
    (εc := ε + 2 * ML2Spine.spineNu β ϖ (min ε₁₀ (25 * min ηf ηc / 2)) gain dens + min ε₁₀ (25 *
        min ηf ηc / 2) / 25)
    (by linarith) (by linarith) ?_
  obtain ⟨Cε, hCε⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (min ηf ηc / 40) (by positivity)
  obtain ⟨d5, hd50, hd5⟩ :=
    ML2Reduction.exists_threshold_const_le_rpow_neg (C := max 1 (2 * Cε ^ 2)) (le_max_left _ _)
      (κ := min ηf ηc / 4) (by positivity)
  filter_upwards [hfineev, hcoarseev,
    hmid β ϖ gain dens hβ0 hβ1 hp hKT hF (min ε₁₀ (25 * min ηf ηc / 2)) hε₁,
    Ioc_mem_nhdsGT hd50, Ioc_mem_nhdsGT (zero_lt_one' NNReal)]
    with δ hfine hcoarse hmidδ hm5 hm01
  intro ι u T Cu lam 𝒰 Cstar ηl εd Nw a b m hwin v t₀ t₁
    ht₁ hballt hballs ht₀ hcn hballt₀ hballu hune hmaxu hdense hlamlow hcardu hCstar hηlm0
    hηlmax hCubnd hmasspos hδτ hτθ hθ1
  have hδ0 : 0 < δ := hm01.1
  have hδ1 : δ ≤ 1 := hm01.2
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hab : a ≤ b := hwin.coarse_lt_fine.le
  have hbN : b ≤ Tube.ssfGridLen δ := hwin.fine_le_gridLen
  have haN : a ≤ Tube.ssfGridLen δ := hab.trans hbN
  -- the middle factor, with the two-scale split it is a statement about
  obtain ⟨tτ', htτ', tθ', htθ', Yτ', Yθ, Y', jθ, hYτ', hYθ, hY', hballθ, hτne, hθne, href1,
    hfull2, hprod, hjθ, hmidbd⟩ :=
    hmidδ u T Cu lam 𝒰 Cstar ηl εd Nw a b m hwin v t₀ t₁ ht₁ hballt hballs ht₀ hcn hballt₀
      hballu hune hmaxu hdense hlamlow hcardu hCstar hηlm0 hηlmax hCubnd hmasspos hδτ hτθ hθ1
  -- cardinality ceilings
  have hs₁ne : (({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hmasspos
    simp at hmasspos
  have hs₁pos : 0 < (({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card := Finset.card_pos.mpr
      hs₁ne
  have hτpos : 0 < tτ'.card := Finset.card_pos.mpr hτne
  have hs₁card : (((({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card : ℕ) : NNReal) ≤ δ ^ (-(4
      : ℝ)) := by
    refine le_trans ?_ hcardu
    exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
  have hτcard : ((tτ'.card : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) := by
    refine le_trans ?_ hcardu
    have h1 : tτ'.card ≤ (ML2Reduction.activeNodes 𝒰.cover.toChain b).card :=
      Finset.card_le_card (htτ'.trans ht₁)
    have h2 := card_activeNodes_le_card (E := (EuclideanSpace ℝ (Fin 3))) 𝒰.cover.toChain b
    exact_mod_cast Nat.cast_le.mpr (h1.trans h2)
  have hSSL := spineScaleLoss_prod_le (n := (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) hδ0 hδ1
      hδτ (le_trans hτθ hθ1)
    hs₁pos hτpos hs₁card hτcard (ε := min ηf ηc / 40) (by positivity) hCε
  have hSSL2one : (1 : NNReal)
      ≤ ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
          (Tube.gridScale δ (Tube.ssfGridLen δ) b) :=
    ML2Reduction.one_le_spineScaleLoss _ _ _
  have hSSL1pos : 0 < ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
      (({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card δ :=
    lt_of_lt_of_le zero_lt_one (ML2Reduction.one_le_spineScaleLoss _ _ _)
  have hSSLpos : 0 < ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
      (({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card δ
      * ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
          (Tube.gridScale δ (Tube.ssfGridLen δ) b) :=
    mul_pos hSSL1pos (lt_of_lt_of_le zero_lt_one hSSL2one)
  have key : ∀ x y z : NNReal, 0 < x → x * z ≤ y → z ≤ x⁻¹ * y := by
    intro x y z hx h
    calc z = x⁻¹ * (x * z) := by rw [← mul_assoc, inv_mul_cancel₀ hx.ne', one_mul]
      _ ≤ x⁻¹ * y := by gcongr
  have hlam2 : (δ : NNReal) ^ ML2Spine.spineNu β ϖ (min ε₁₀ (25 * min ηf ηc / 2)) gain dens ≤ 2 *
      lam := by
    rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 2)] at hlamlow
    calc (δ : NNReal) ^ ML2Spine.spineNu β ϖ (min ε₁₀ (25 * min ηf ηc / 2)) gain dens ≤ lam * 2 :=
        hlamlow
      _ = 2 * lam := by ring
  have hlamfull : lam ≤ ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i
      ↦ (T i).toShadedBody) := by
    have h := (hdense.subset (Finset.filter_subset _ _)).le_fullness_tube hδ0 hs₁ne
    rw [← ShadedBody.coe_fullness] at h
    exact_mod_cast h
  have habs2 : ∀ θ : ℝ, min ηf ηc ≤ θ →
      (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (({i ∈ u |
          𝒰.cover.assign b i ∈ t₁} : Finset ι)).card δ
        * ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
            (Tube.gridScale δ (Tube.ssfGridLen δ) b))
        * δ ^ θ ≤ ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
            i).toShadedBody) := by
    intro θ hθ
    refine le_trans ?_ hlamfull
    refine le_of_mul_le_mul_left ?_ (by norm_num : (0 : NNReal) < 2)
    refine le_trans ?_ hlam2
    calc 2 * ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (({i ∈ u
        | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card δ
            * ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) b)) * δ ^ θ)
        ≤ 2 * ((Cε ^ 2 * δ ^ (-(10 * (min ηf ηc / 40)))) * δ ^ θ) := by gcongr
      _ = (2 * Cε ^ 2) * (δ ^ (-(min ηf ηc / 4)) * δ ^ θ) := by
          rw [show (10 : ℝ) * (min ηf ηc / 40) = min ηf ηc / 4 by ring]; ring
      _ = (2 * Cε ^ 2) * δ ^ (θ - min ηf ηc / 4) := by
          rw [← NNReal.rpow_add hδ0.ne']
          congr 2
          ring
      _ = (2 * Cε ^ 2) * (δ ^ (min ηf ηc / 4) * δ ^ (θ - min ηf ηc / 2)) := by
          rw [← NNReal.rpow_add hδ0.ne']
          congr 2
          ring
      _ = ((2 * Cε ^ 2) * δ ^ (min ηf ηc / 4)) * δ ^ (θ - min ηf ηc / 2) := by ring
      _ ≤ 1 * δ ^ (θ - min ηf ηc / 2) := by
          gcongr
          calc (2 * Cε ^ 2) * δ ^ (min ηf ηc / 4)
              ≤ δ ^ (-(min ηf ηc / 4)) * δ ^ (min ηf ηc / 4) := by
                gcongr
                exact le_trans (le_max_right 1 (2 * Cε ^ 2)) (hd5 δ hδ0 hm5.2)
            _ = 1 := by
                rw [← NNReal.rpow_add hδ0.ne']
                simp
      _ = δ ^ (θ - min ηf ηc / 2) := one_mul _
      _ ≤ δ ^ ML2Spine.spineNu β ϖ (min ε₁₀ (25 * min ηf ηc / 2)) gain dens :=
          NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  -- the fine factor
  have hfullf : (δ : NNReal) ^ ηf
      ≤ (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (({i ∈ u |
          𝒰.cover.assign b i ∈ t₁} : Finset ι)).card δ)⁻¹
        * ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
            i).toShadedBody) := by
    refine key _ _ _ hSSL1pos ?_
    refine le_trans ?_ (habs2 ηf hminf)
    gcongr
    exact le_mul_of_one_le_right' hSSL2one
  have hmaxf : Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηf) := by
    refine hmaxu.trans ?_
    exact ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
  obtain ⟨jτ, hjτ, hfinebd⟩ :=
    hfine (s := u) (s₁ := ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)) (t := tτ') (V := T) (Y
        := Y') (v := v)
      (pτ := 𝒰.cover.assign b)
      (c := (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (({i ∈ u |
          𝒰.cover.assign b i ∈ t₁} : Finset ι)).card δ)⁻¹)
      (Finset.filter_subset _ _) hY' hballs href1 hτne hmaxf hfullf
  -- the coarse factor
  have hfullc : (δ : NNReal) ^ ηc ≤ ShadedBody.fullness tθ' (fun k ↦ (Yθ k).toShadedBody) :=
    le_trans (key _ _ _ hSSLpos (habs2 ηc hminc)) hfull2
  have hcoarsebd := hcoarse (𝒰 := 𝒰) (Cstar := Cstar) (ηl := ηl) (εd := εd) (N := Nw)
    (a := a) (b := b) (m := m) (κ := 2 * ML2Spine.spineNu β ϖ (min ε₁₀ (25 * min ηf ηc / 2)) gain
        dens) (c := ε + 2 * ML2Spine.spineNu β ϖ (min ε₁₀ (25 * min ηf ηc / 2)) gain dens + min
        ε₁₀ (25 * min ηf ηc / 2) / 25)
    (t := tθ') (Yθ := Yθ) (v := v)
    hδ0 hδ1 hune hballu hwin hηlm0 (by linarith) hCstar (by linarith) hCubnd htθ' hYθ
    hballθ hfullc
  exact ⟨tτ', tθ', Yτ', Yθ, Y', jτ, jθ, htτ', htθ', htτ' hjτ, hjθ, hτne,
    hprod jτ hjτ jθ hjθ, hfinebd, hmidbd, hcoarsebd⟩

end MiddleOnly


end Kakeya.ML2Core

end
