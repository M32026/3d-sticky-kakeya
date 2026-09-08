/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleProducer

/-!
# The rung-level re-cut of the branch-(ii) wiring

`Kakeya.ML2Core.geometricCoreAt_of_middleFactor` reduces the geometric core to a middle-factor
hypothesis whose binder block is satisfiable by a single fully shaded tube
(`Kakeya.ML2Core.not_middleFactor_hypothesis`), so the theorem is unusable.  Two things in that
block are responsible, and both are repaired here.

* **The window's rung function was abstract.**  The block quantified over an arbitrary
  `ηl : ℕ → ℝ` with only `0 ≤ ηl m ≤ ε₁/25`, so the refuting model could take `ηl ≡ 0`, at which
  the window's density lower bound `IsKatzTaoDividingWindow.le_window_maxDensity` — GWZ's
  `tildeDeltaLargeDeltamax`, the source of the count clause — says nothing.  The block below pins
  the window to the **constructed** spine `Kakeya.ML2Spine.spineRung`, whose rungs are positive
  (`Kakeya.ML2Core.two_le_card_nodesUnder_of_spineWindow` is the consequence: no coarse
  node of such a window has a one-node middle family).
* **The exponents were fixed before the window.**  `Kakeya.ML2Core.dichotomy_of_windowFactors`
  takes `εf, gm, εc` as reals, so the coarse cost `ε + κ + η_m` had to be flattened to `ε₁/25`
  while the middle gain was asked for uniformly; `Kakeya.ML2Core.spineRung_middle_gain_lt_demand`
  shows the two never meet.  `Kakeya.ML2Core.dichotomy_of_rungFactors` reads both at the window's
  own rung `X = η_m`, where `Kakeya.ML2Core.rung_budget_closes_of_overhead_le_four` closes.

The third change is the one that makes the arithmetic *satisfiable*: the input density exponent
of the dichotomy is decoupled from the spine's bottom rung.  The two Katz--Tao factors are read at
an accuracy `ε = ν/20`, and their density exponents `η_f, η_c` are then whatever `K_KT(β)`
returns — possibly far below `ν`.  The fullness floor the window branch hands them is
`λ ≥ δ^{η_in}/2` where `η_in` is the *input* density exponent, so choosing
`η_in ≤ min η_f η_c / 2` is a choice about the statement's density slot (which
`Kakeya.ML2Assembly.GeometricCoreAt` leaves free), not about the spine.  The existing wiring made
`ν` small instead, by shrinking `ε₁`, which shrinks the middle gain with it.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-! ## The window package with the constructed spine pinned

`Kakeya.ML2Inputs.exists_shaded_dividingScales_of_dichotomyHypotheses` builds its ladder from
`Kakeya.ML2Inputs.exists_dividingScalesLadder`, which *is* the constructed spine, but its statement
hides that behind `∃ η`.  The consumers below need the rungs by name, so the same proof is run with
the spine written out. -/

section SpinePackage

/-- **GWZ Lemma 7.7(B) on the constructed spine, returning the level twin.**
`exists_shaded_dividingScales_spine` with the conclusion
`Kakeya.ML2Inputs.DividingScalesOutputLevels`.  The existing statement is the corollary below. -/
theorem exists_shaded_dividingScales_spine_levels (K₀ : ℕ)
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {α : ℝ} (hα : 0 < α) :
    ∃ (C d : NNReal) (Kl cl : ℕ),
      1 ≤ C ∧ 0 < d ∧ d ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ d →
      ∀ (s : Finset ι) (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))), s.Nonempty →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
        Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens))) →
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
        ∀ lam : NNReal, 0 < lam →
        ML2Shaded.HasDenseShading lam s (fun i => (V i).toShadedBody) →
        ML2Inputs.DividingScalesOutputLevels C Kl cl ε₁ α (ML2Spine.spineDiv ϖ ε₁)
          (ML2Spine.spineCount ϖ ε₁) (ML2Spine.spineRung β ϖ ε₁ gain dens) s V lam := by
  classical
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hspine := ML2Spine.spineRung_isSpine hβ hβ1 hϖ hε₁ hgain hdens
  have hN : 4096 ≤ ML2Spine.spineCount ϖ ε₁ := hspine.four_thousand_le_stepCount
  have he : ML2Spine.spineDiv ϖ ε₁ = 1 / Real.sqrt (ML2Spine.spineCount ϖ ε₁ : ℝ) :=
    hspine.div_eq
  have hη0 : 0 ≤ ML2Spine.spineRung β ϖ ε₁ gain dens 0 := (hspine.rung_pos 0).le
  have hηstep : ∀ k < ML2Spine.spineCount ϖ ε₁,
      ML2Spine.spineRung β ϖ ε₁ gain dens k
        ≤ ML2Spine.spineDiv ϖ ε₁ * ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) :=
    fun k hk => ML2Reduction.rung_le_div_mul_rung_succ hspine hβ hβ1 hk
  have hηN : ML2Spine.spineRung β ϖ ε₁ gain dens (ML2Spine.spineCount ϖ ε₁)
      ≤ ML2Spine.spineDiv ϖ ε₁ := le_of_eq hspine.rung_top
  have hε₂₁ : ML2Spine.spineEps₂ ϖ ε₁ ≤ ε₁ / 5 := hspine.eps₂_le_everyScale
  have h5e : 5 * ML2Spine.spineDiv ϖ ε₁ ≤ ML2Spine.spineEps₂ ϖ ε₁ := by
    have := hspine.div_le
    linarith
  obtain ⟨C, δ₀, Kl, cl, hC, hδ₀0, hδ₀1, hmain⟩ :=
    ML2Shaded.exists_shaded_dividingScalesKatzTao_dense.{u} (E := EuclideanSpace ℝ (Fin 3))
      hn (ML2Spine.spineCount ϖ ε₁) hN he
      (uniformConst (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))
  have h5e₁ : 5 * ML2Spine.spineDiv ϖ ε₁ ≤ ε₁ / 5 := by linarith
  obtain ⟨δ₁, hδ₁0, hδ₁1, habs⟩ :=
    ML2Reduction.exists_threshold_katzTaoError_le C hC Kl cl hε₁ h5e₁
  obtain ⟨δ₂, hδ₂0, hδ₂1, hinputs⟩ :=
    ML2Inputs.exists_dividingScalesInputs.{u} (E := EuclideanSpace ℝ (Fin 3)) K₀
      (ML2Spine.spineRung β ϖ ε₁ gain dens 0) hα
  refine ⟨C, min (min δ₀ δ₁) δ₂, Kl, cl, hC,
    lt_min (lt_min hδ₀0 hδ₁0) hδ₂0, ((min_le_left _ _).trans (min_le_left _ _)).trans hδ₀1, ?_⟩
  intro ι δ hδ0 hδd s V hsne hball hD hcardK lam hlam hdense
  have hδδ₀ : δ ≤ δ₀ := hδd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδδ₁ : δ ≤ δ₁ := hδd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδδ₂ : δ ≤ δ₂ := hδd.trans (min_le_right _ _)
  -- the input package, on the underlying tubes
  have hball' : ∀ i ∈ s, ((V i).toTube).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3))
      1 := hball
  have hD' : Kakeya.maxDensity s (fun i => ((V i).toTube).toConvexSpaceBody)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineRung β ϖ ε₁ gain dens 0))) :=
    le_trans (le_of_eq (Kakeya.maxDensity_congr (fun i _ => rfl))) hD
  obtain ⟨u, hus, hballu, hED, hDens, hstruct, hcard1⟩ :=
    hinputs hδ0 hδδ₂ s (fun i => (V i).toTube) hball' hD' hcardK
  have hune : u.Nonempty := ML2Shaded.nonempty_of_card_le_mul hsne hcard1
  have hballu' : ∀ i ∈ u, (V i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    hballu
  have hED' : (u : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct ((V i).carrier) ((V j).carrier)) := by
    intro i hi j hj hne
    exact hED hi hj hne
  have hDens' : Kakeya.maxDensity u (fun i => (V i).toConvexSpaceBody)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineRung β ϖ ε₁ gain dens 0))) :=
    le_trans (le_of_eq (Kakeya.maxDensity_congr (fun i _ => rfl))) hDens
  -- GWZ 7.7(B), one-sided form, on the package
  obtain ⟨u', hu'u, W, hu'ne, htube, hshade, hcard2, hmass, hdense', hcomp', hfull, -,
      𝒲, halt⟩ :=
    hmain (ι := ι) (δ := δ) hδ0 hδδ₀ (ML2Spine.spineRung β ϖ ε₁ gain dens) hη0 hηstep hηN u V
      hune hballu' hED' hstruct.some hDens' lam hlam (hdense.subset hus)
  refine ⟨u, hus, u', hu'u, W, hu'ne, htube, hshade, ?_, hmass, hdense', hcomp', hfull,
    𝒲, ?_⟩
  · calc (s.card : ENNReal)
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineRung β ϖ ε₁ gain dens 0 + α)))
            * (u.card : ENNReal) := hcard1
      _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineRung β ϖ ε₁ gain dens 0 + α)))
            * (StickyKakeya.totalLoss C Kl cl δ * (u'.card : ENNReal)) :=
          mul_le_mul' le_rfl hcard2
      _ = ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineRung β ϖ ε₁ gain dens 0 + α)))
            * StickyKakeya.totalLoss C Kl cl δ * (u'.card : ENNReal) := by ring
  · rcases halt with hKT | ⟨a, b, m, hm, hab, hb, hsep, h1, h2, h3, hlev, hband⟩
    · exact Or.inl (hKT.mono (habs hδ0 hδδ₁))
    · exact Or.inr ⟨a, b, m, ⟨⟨hm, hab, hb, hsep, h1, h2, h3⟩, hlev, hband⟩⟩

/-- **GWZ Lemma 7.7(B) in its one-sided shaded form, on the constructed spine.**

`Kakeya.ML2Inputs.exists_shaded_dividingScales_of_dichotomyHypotheses` with the ladder
`(ε₂, e, N, η) := (spineEps₂, spineDiv, spineCount, spineRung)` written out instead of
existentially bound.  The body is that theorem's, with the ladder facts read off
`Kakeya.ML2Spine.spineRung_isSpine`. -/
theorem exists_shaded_dividingScales_spine (K₀ : ℕ)
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {α : ℝ} (hα : 0 < α) :
    ∃ (C d : NNReal) (Kl cl : ℕ),
      1 ≤ C ∧ 0 < d ∧ d ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ d →
      ∀ (s : Finset ι) (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))), s.Nonempty →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
        Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens))) →
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
        ∀ lam : NNReal, 0 < lam →
        ML2Shaded.HasDenseShading lam s (fun i => (V i).toShadedBody) →
        ML2Inputs.DividingScalesOutput C Kl cl ε₁ α (ML2Spine.spineDiv ϖ ε₁)
          (ML2Spine.spineCount ϖ ε₁) (ML2Spine.spineRung β ϖ ε₁ gain dens) s V lam := by
  obtain ⟨C, d, Kl, cl, hC, hd0, hd1, hmain⟩ :=
    exists_shaded_dividingScales_spine_levels.{u} K₀ hβ hβ1 hϖ hε₁ hgain hdens hα
  exact ⟨C, d, Kl, cl, hC, hd0, hd1, fun hδ0 hδd s V hsne hball hKT hcard lam hlam hdense =>
    (hmain hδ0 hδd s V hsne hball hKT hcard lam hlam hdense).toDividingScalesOutput⟩


/-- `eventually_shaded_dividingScales_spine`, returning the level twin
`Kakeya.ML2Inputs.DividingScalesOutputLevels`.  The existing statement is the corollary below. -/
theorem eventually_shaded_dividingScales_spine_levels
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {α : ℝ} (hα : 0 < α) :
    ∃ (C : NNReal) (Kl cl : ℕ), 1 ≤ C ∧
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
        ∀ {ι : Type u} (s : Finset ι) (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          s.Nonempty →
          (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
          IsKatzTao s (fun i => (V i).toConvexSpaceBody)
            ((δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens))) →
          ∀ lam : NNReal, 0 < lam →
          ML2Shaded.HasDenseShading lam s (fun i => (V i).toShadedBody) →
          ML2Inputs.DividingScalesOutputLevels C Kl cl ε₁ α (ML2Spine.spineDiv ϖ ε₁)
            (ML2Spine.spineCount ϖ ε₁) (ML2Spine.spineRung β ϖ ε₁ gain dens) s V lam := by
  classical
  obtain ⟨C, d, Kl, cl, hC, hd0, hd1, hmain⟩ :=
    exists_shaded_dividingScales_spine_levels.{u} 4 hβ hβ1 hϖ hε₁ hgain hdens hα
  have hν1 : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ 1 := by
    have h := ML2Inputs.spineNu_le_div_48000 hβ hβ1 hϖ hε₁ hgain hdens
    linarith
  refine ⟨C, Kl, cl, hC, ?_⟩
  filter_upwards [ML2Assembly.eventually_card_thresholds, Ioc_mem_nhdsGT hd0]
    with δ hthr hδmem
  obtain ⟨hδ0, hδ1, hδC⟩ := hthr
  obtain ⟨-, hδd⟩ := hδmem
  intro ι s V hsne hball hKT lam hlam hdense
  have hDens : Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens))) := by
    rw [ML2Reduction.ofReal_rpow_coe hδ0]
    exact hKT
  have hcardK : (s.card : ℝ) ≤ (δ : ℝ) ^ (-((4 : ℕ) : ℝ)) := by
    have h := ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s V hball hν1 hKT
    simpa using h
  exact hmain hδ0 hδd s V hsne hball hDens hcardK lam hlam hdense

/-- `Kakeya.ML2Inputs.eventually_shaded_dividingScales_dim3` on the constructed spine. -/
theorem eventually_shaded_dividingScales_spine
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {α : ℝ} (hα : 0 < α) :
    ∃ (C : NNReal) (Kl cl : ℕ), 1 ≤ C ∧
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
        ∀ {ι : Type u} (s : Finset ι) (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          s.Nonempty →
          (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
          IsKatzTao s (fun i => (V i).toConvexSpaceBody)
            ((δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens))) →
          ∀ lam : NNReal, 0 < lam →
          ML2Shaded.HasDenseShading lam s (fun i => (V i).toShadedBody) →
          ML2Inputs.DividingScalesOutput C Kl cl ε₁ α (ML2Spine.spineDiv ϖ ε₁)
            (ML2Spine.spineCount ϖ ε₁) (ML2Spine.spineRung β ϖ ε₁ gain dens) s V lam := by
  obtain ⟨C, Kl, cl, hC, hev⟩ :=
    eventually_shaded_dividingScales_spine_levels.{u} hβ hβ1 hϖ hε₁ hgain hdens hα
  exact ⟨C, Kl, cl, hC, hev.mono fun δ hδ => fun s V hsne hball hKT lam hlam hdense =>
    (hδ s V hsne hball hKT lam hlam hdense).toDividingScalesOutput⟩


/-- `eventually_dividingScalesPackage_spine`, returning the level twin
`Kakeya.ML2Inputs.DividingScalesOutputLevels`.  The existing statement is the corollary below. -/
theorem eventually_dividingScalesPackage_spine_levels
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {ηin : ℝ} (hηinν : ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens) :
    ∃ (C : NNReal) (Kl cl : ℕ), 1 ≤ C ∧
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
        0 < δ ∧ δ ≤ 1 ∧
        ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
          IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-ηin)) →
          ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ ηin →
          (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
          s.Nonempty ∧
          ∃ s' ⊆ s, ∃ lam : NNReal,
            δ ^ ηin / 2 ≤ lam ∧ 0 < lam ∧ s'.Nonempty ∧
            (∑ i ∈ s, volume (T i).shade) ≤ 2 * ∑ i ∈ s', volume (T i).shade ∧
            ML2Shaded.HasDenseShading lam s' (fun i ↦ (T i).toShadedBody) ∧
            ML2Inputs.DividingScalesOutputLevels C Kl cl ε₁ (ML2Spine.spineNu β ϖ ε₁ gain dens)
              (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁)
              (ML2Spine.spineRung β ϖ ε₁ gain dens) s' T lam := by
  classical
  have hν0 : 0 < ML2Spine.spineNu β ϖ ε₁ gain dens :=
    ML2Spine.spineNu_pos hβ hϖ hε₁ hgain hdens
  obtain ⟨C, Kl, cl, hC, hev⟩ :=
    eventually_shaded_dividingScales_spine_levels.{u} hβ hβ1 hϖ hε₁ hgain hdens
      (α := ML2Spine.spineNu β ϖ ε₁ gain dens) hν0
  refine ⟨C, Kl, cl, hC, ?_⟩
  filter_upwards [hev, Ioc_mem_nhdsGT (zero_lt_one' NNReal)] with δ hδmain hδmem
  obtain ⟨hδ0, hδ1⟩ := hδmem
  refine ⟨hδ0, hδ1, ?_⟩
  intro ι s T hball hKT hfull hcard
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hsne : s.Nonempty := nonempty_of_inv_le_card hδ0 hδ1 hcard
  obtain ⟨s', hs's, lam, hlamlow, hlam0, hs'ne, hmass, hdense⟩ :=
    exists_denseShading_dichotomy (E := EuclideanSpace ℝ (Fin 3)) hδ0 s T hfull
  have hballs' : ∀ i ∈ s', (T i).carrier ⊆ Metric.closedBall 0 1 :=
    fun i hi => hball i (hs's hi)
  have hKTs' : IsKatzTao s' (fun i ↦ (T i).toConvexSpaceBody)
      ((δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens))) :=
    le_trans (Kakeya.maxDensity_mono (fun i ↦ (T i).toConvexSpaceBody) hs's)
      (le_trans hKT (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)))
  have hout := hδmain s' T hs'ne hballs' hKTs' lam hlam0 hdense
  exact ⟨hsne, s', hs's, lam, hlamlow, hlam0, hs'ne, hmass, hdense, hout⟩

/-- **GC-P1 on the constructed spine, at an input density exponent `η_in ≤ ν`.**

`Kakeya.ML2Core.eventually_dividingScalesPackage_dim3` with two changes: the ladder is the
constructed spine, written out; and the dichotomy's two density hypotheses are read at an
exponent `η_in ≤ ν` of the consumer's choice, so that the dense-shading floor
`Kakeya.ML2Core.exists_denseShading_dichotomy` returns is `δ^{η_in}/2` and not `δ^{ν}/2`.

That floor is what the two Katz--Tao factors of the window branch read their fullness against, and
`Kakeya.KatzTaoEstimate` returns a density exponent that may be far below the accuracy it is asked
at; `η_in` is the slot that absorbs it.  The absorption budget `α` of the package stays at `ν`,
because it is spent against the spine's own `η 0 = ν` and nothing forces it lower. -/
theorem eventually_dividingScalesPackage_spine
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {ηin : ℝ} (hηinν : ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens) :
    ∃ (C : NNReal) (Kl cl : ℕ), 1 ≤ C ∧
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
        0 < δ ∧ δ ≤ 1 ∧
        ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
          IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-ηin)) →
          ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ ηin →
          (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
          s.Nonempty ∧
          ∃ s' ⊆ s, ∃ lam : NNReal,
            δ ^ ηin / 2 ≤ lam ∧ 0 < lam ∧ s'.Nonempty ∧
            (∑ i ∈ s, volume (T i).shade) ≤ 2 * ∑ i ∈ s', volume (T i).shade ∧
            ML2Shaded.HasDenseShading lam s' (fun i ↦ (T i).toShadedBody) ∧
            ML2Inputs.DividingScalesOutput C Kl cl ε₁ (ML2Spine.spineNu β ϖ ε₁ gain dens)
              (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁)
              (ML2Spine.spineRung β ϖ ε₁ gain dens) s' T lam := by
  obtain ⟨C, Kl, cl, hC, hev⟩ :=
    eventually_dividingScalesPackage_spine_levels.{u} hβ hβ1 hϖ hε₁ hgain hdens hηinν
  refine ⟨C, Kl, cl, hC, hev.mono fun δ hδ => ⟨hδ.1, hδ.2.1, fun s T hball hKT hfull hcard => ?_⟩⟩
  obtain ⟨hsne, s', hs's, lam, hlamlow, hlam0, hs'ne, hmass, hdense, hout⟩ :=
    hδ.2.2 s T hball hKT hfull hcard
  exact ⟨hsne, s', hs's, lam, hlamlow, hlam0, hs'ne, hmass, hdense, hout.toDividingScalesOutput⟩


end SpinePackage

/-! ## Branch (i) at every small Katz--Tao exponent, on the spine, at input density `η_in` -/

section DichotomySpine

/-- **`exists_dichotomyLeft_or_window_spine` with the window read as
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels`** (§2.6).  One identifier differs from
the existing text: the window in the right disjunct is the level twin, carrying the source's
multiplicity-free level clause and the two-level density band.  The existing statement is the
corollary below, by the parent projection; its proof is the one that used to sit here, with
`losses_of_dividingScalesOutputLevels` in place of `losses_of_dividingScalesOutput`. -/
theorem exists_dichotomyLeft_or_window_spine_levels
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))
    {β ϖ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    ∃ ε₁₀ : ℝ, 0 < ε₁₀ ∧ ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ ε₁₀ →
      ∀ ηin : ℝ, ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens →
      ∃ (C : NNReal) (Kl cl : ℕ), 1 ≤ C ∧
        ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
          0 < δ ∧ δ ≤ 1 ∧
          ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
            (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
            IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-ηin)) →
            ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ ηin →
            (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
            s.Nonempty ∧
            (ML2Shading.DichotomyLeft (β / 2) s T
              ∨ ∃ u' ⊆ s, ∃ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∃ lam : NNReal,
                  δ ^ ηin / 2 ≤ lam ∧ 0 < lam ∧ u'.Nonempty ∧
                  (∀ i, (W i).toTube = (T i).toTube) ∧
                  (∀ i, (W i).shade ⊆ (T i).shade) ∧
                  ML2Shaded.HasDenseShading lam u' (fun i ↦ (T i).toShadedBody) ∧
                  ML2Shaded.HasComparableDensities lam⁻¹ u'
                      (fun i ↦ (T i).toShadedBody) ∧
                  (lam : ENNReal)
                        * (Tube.le_volume.c
                            (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
                        * (∑ i ∈ s, volume (T i).shade)
                      ≤ 2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                              + ML2Spine.spineNu β ϖ ε₁ gain dens)))
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
                    ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindowLevels 𝒲.tubeUniform
                        ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
                        (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
                        (ML2Spine.spineCount ϖ ε₁) a b m) := by
  classical
  obtain ⟨ε₁₀, hε₁₀, hL1all⟩ :=
    exists_multiplicity_quarter_le (E := EuclideanSpace ℝ (Fin 3))
      finrank_euclideanSpace_fin hSFE hβ
  refine ⟨ε₁₀, hε₁₀, ?_⟩
  intro ε₁ hε₁ hε₁le ηin hηinν
  obtain ⟨C, Kl, cl, hC, hev⟩ :=
    eventually_dividingScalesPackage_spine_levels.{u} hβ hβ1 hϖ hε₁ hgain hdens hηinν
  refine ⟨C, Kl, cl, hC, ?_⟩
  have hν0 : 0 < ML2Spine.spineNu β ϖ ε₁ gain dens :=
    ML2Spine.spineNu_pos hβ hϖ hε₁ hgain hdens
  have hν25 : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ ε₁ / 25 :=
    spineNu_le_div_25 hβ hβ1 hϖ hε₁ hgain hdens
  have hνε₁ : 2 * ML2Spine.spineNu β ϖ ε₁ gain dens ≤ ε₁ := by linarith
  have hν48 : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ β / 48000 :=
    ML2Inputs.spineNu_le_div_48000 hβ hβ1 hϖ hε₁ hgain hdens
  have hν1 : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ 1 := by linarith
  have hηin1 : ηin ≤ 1 := hηinν.trans hν1
  have hbud : ML2Spine.spineNu β ϖ ε₁ gain dens + ML2Spine.spineNu β ϖ ε₁ gain dens
      + ML2Spine.spineNu β ϖ ε₁ gain dens + ML2Spine.spineNu β ϖ ε₁ gain dens + β / 4
      + ML2Spine.spineNu β ϖ ε₁ gain dens + ML2Spine.spineNu β ϖ ε₁ gain dens ≤ β / 2 := by
    linarith
  obtain ⟨d1, hd10, hd11, hL1d⟩ := hL1all ε₁ hε₁ hε₁le hν0 hνε₁
  obtain ⟨dT, hdT0, hdT1, hdT⟩ :=
    StickyKakeya.exists_threshold_totalLoss_le C hC Kl cl _ hν0
  obtain ⟨dS, hdS0, hdS1, hdS⟩ :=
    ML2Shading.exists_threshold_shadingBridgeLoss_le
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) 2 4
      (a := ML2Spine.spineNu β ϖ ε₁ gain dens + ML2Spine.spineNu β ϖ ε₁ gain dens
        + ML2Spine.spineNu β ϖ ε₁ gain dens) (α := ML2Spine.spineNu β ϖ ε₁ gain dens) hν0
  obtain ⟨d2, hd20, hd21, hd2⟩ := ML2Shaded.exists_threshold_const_le_rpow_neg' 2 hν0
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
    losses_of_dividingScalesOutputLevels (E := EuclideanSpace ℝ (Fin 3)) hδ1 hs's hmass hout
  rcases halt with hevery | hwindow
  · -- alternative (i): GWZ `section9.tex` lines 55–61, exactly as in the existing theorem
    refine Or.inl ?_
    have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
    have hmaxs : Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens))) := by
      rw [ML2Reduction.ofReal_rpow_coe hδ0]
      exact le_trans hKT (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith))
    have hcard4 : (s.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) := by
      simpa using ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s T hball hηin1 hKT
    have hlamE : ENNReal.ofReal ((δ : ℝ) ^ (ML2Spine.spineNu β ϖ ε₁ gain dens))
        ≤ 2 * (lam : ENNReal) := by
      have hnn : (δ : NNReal) ^ (ML2Spine.spineNu β ϖ ε₁ gain dens) ≤ 2 * lam := by
        have h1 : (δ : NNReal) ^ (ML2Spine.spineNu β ϖ ε₁ gain dens) ≤ (δ : NNReal) ^ ηin :=
          NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hηinν
        rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 2)] at hlamlow
        calc (δ : NNReal) ^ (ML2Spine.spineNu β ϖ ε₁ gain dens) ≤ (δ : NNReal) ^ ηin := h1
          _ ≤ lam * 2 := hlamlow
          _ = 2 * lam := by ring
      have hcoe : ENNReal.ofReal ((δ : ℝ) ^ (ML2Spine.spineNu β ϖ ε₁ gain dens))
          = (((δ : NNReal) ^ (ML2Spine.spineNu β ϖ ε₁ gain dens) : NNReal) : ENNReal) := by
        rw [← NNReal.coe_rpow, ENNReal.ofReal_coe_nnreal]
      rw [hcoe]
      calc (((δ : NNReal) ^ (ML2Spine.spineNu β ϖ ε₁ gain dens) : NNReal) : ENNReal)
          ≤ ((2 * lam : NNReal) : ENNReal) := ENNReal.coe_le_coe.mpr hnn
        _ = 2 * (lam : ENNReal) := by push_cast; ring
    have hmult := hL1d hδ0 hm1.2 s u' T W lam hu's hball htube hmaxs hcard4 hlamE hfullpoly
      𝒲 hevery
    have hA : ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
            + ML2Spine.spineNu β ϖ ε₁ gain dens))) * StickyKakeya.totalLoss C Kl cl δ
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
            + ML2Spine.spineNu β ϖ ε₁ gain dens + ML2Spine.spineNu β ϖ ε₁ gain dens))) := by
      calc ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
              + ML2Spine.spineNu β ϖ ε₁ gain dens))) * StickyKakeya.totalLoss C Kl cl δ
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                + ML2Spine.spineNu β ϖ ε₁ gain dens)))
              * ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens))) := by
            gcongr
            exact hdT hδ0 hmT.2
        _ = ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
              + ML2Spine.spineNu β ϖ ε₁ gain dens + ML2Spine.spineNu β ϖ ε₁ gain dens))) := by
            rw [ofReal_rpow_mul hδ0]
            ring_nf
    have hSBL := hdS hδ0 hmS.2 hA s.card (by simpa using hcard4)
    have htwo : (2 : ENNReal)
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens))) := by
      have hr := hd2 hδ0 hm2.2
      calc (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by simp
        _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens))) :=
          ENNReal.ofReal_le_ofReal hr
    have hchain := sum_shade_le_shadingBridgeLoss hmassloss hpoly hunion hmult
    have hbound := sum_shade_le_rpow_of_chain hδ0 hchain hSBL le_rfl hlamE htwo
    exact dichotomyLeft_of_rpow_bound hδ0 hδ1 hbound hbud
  · exact Or.inr ⟨u', hu's, W, lam, hlamlow, hlam0, hu'ne, htube, hshade, hdenseu, hcompu,
      hmassloss, hpoly, hunion, hfullpoly, 𝒲, hwindow⟩

/-- **`Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3_small` on the constructed spine, at an
input density exponent `η_in ≤ ν`.**

Two differences from the existing theorem, both in the right disjunct: the dividing window is
stated on the constructed spine `(spineRung, spineDiv, spineCount)` by name, and the dense-shading
floor is `δ^{η_in}/2` rather than `δ^{ν}/2`.  Branch (i) is unchanged: its inputs are the density
and fullness hypotheses at the exponent `ν`, which the hypotheses at `η_in ≤ ν` imply. -/
theorem exists_dichotomyLeft_or_window_spine
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))
    {β ϖ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    ∃ ε₁₀ : ℝ, 0 < ε₁₀ ∧ ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ ε₁₀ →
      ∀ ηin : ℝ, ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens →
      ∃ (C : NNReal) (Kl cl : ℕ), 1 ≤ C ∧
        ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
          0 < δ ∧ δ ≤ 1 ∧
          ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
            (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
            IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-ηin)) →
            ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ ηin →
            (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
            s.Nonempty ∧
            (ML2Shading.DichotomyLeft (β / 2) s T
              ∨ ∃ u' ⊆ s, ∃ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∃ lam : NNReal,
                  δ ^ ηin / 2 ≤ lam ∧ 0 < lam ∧ u'.Nonempty ∧
                  (∀ i, (W i).toTube = (T i).toTube) ∧
                  (∀ i, (W i).shade ⊆ (T i).shade) ∧
                  ML2Shaded.HasDenseShading lam u' (fun i ↦ (T i).toShadedBody) ∧
                  ML2Shaded.HasComparableDensities lam⁻¹ u'
                      (fun i ↦ (T i).toShadedBody) ∧
                  (lam : ENNReal)
                        * (Tube.le_volume.c
                            (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
                        * (∑ i ∈ s, volume (T i).shade)
                      ≤ 2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                              + ML2Spine.spineNu β ϖ ε₁ gain dens)))
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
                        ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
                        (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
                        (ML2Spine.spineCount ϖ ε₁) a b m) := by
  obtain ⟨ε₁₀, hε₁₀, hmain⟩ :=
    exists_dichotomyLeft_or_window_spine_levels.{u} hSFE hβ hβ1 hϖ hgain hdens
  refine ⟨ε₁₀, hε₁₀, fun ε₁ hε₁ hε₁le ηin hηinν => ?_⟩
  obtain ⟨C, Kl, cl, hC, hev⟩ := hmain ε₁ hε₁ hε₁le ηin hηinν
  refine ⟨C, Kl, cl, hC, hev.mono fun δ hδ => ⟨hδ.1, hδ.2.1, fun s T hball hKT hfull hcard => ?_⟩⟩
  obtain ⟨hsne, halt⟩ := hδ.2.2 s T hball hKT hfull hcard
  refine ⟨hsne, ?_⟩
  rcases halt with hL | ⟨u', hu's, W, lam, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, 𝒲, a, b,
    m, hwin⟩
  · exact Or.inl hL
  · exact Or.inr ⟨u', hu's, W, lam, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, 𝒲, a, b, m,
      hwin.toIsKatzTaoDividingWindow⟩


end DichotomySpine

/-! ## The window branch, re-cut at the rung -/

section RungPackage

open Classical in
/-- **The window branch, wired at the rung: the package plus the three factors give the dichotomy.**

`Kakeya.ML2Core.dichotomy_of_windowFactors` with the three changes the module docstring lists.

* The package `hpkg` is on the constructed spine and at the input density exponent `η_in ≤ ν`
  (`Kakeya.ML2Core.exists_dichotomyLeft_or_window_spine`), so the dense-shading floor it hands the
  factors is `δ^{η_in}/2`.
* The factor exponents are read **at the window's rung** `X = η_m`: the middle gain is `gm X`, a
  function of the rung, and the coarse cost is `εc + X` — the `+ ηl m` of
  `Kakeya.ML2Reduction.exists_coarse_factor_complete`'s own binder — instead of the flattened
  `ε₁/25`.  The budget `hexp` is then a statement about every rung `X ≥ ν`, and it is checked
  *inside* the window's scope.
* The pushback overhead is `2ν + 2η_in + θ₁ + θ₂` instead of `6ν`: the two movable terms —
  `StickyKakeya.totalLoss` and the seam constants — sit at free thresholds `θ₁, θ₂`, and the two
  `λ⁻¹`'s are read at the input density `η_in`.  Only the package's cardinality loss `δ^{-2ν}`
  stays at `ν`, being a clause of the package.  So the internal gain `g` the split has to
  produce is `g = 6ν + θ₁ + θ₂ + 2η_in`, against the target `4ν`.

The middle factor's exponent is a *function* `gm` of the rung so that a producer may hand in
`47 X/5` (`Kakeya.ML2Core.middle_factor_of_edNodes_sharp` transported at the window's own
separation exponent, `Kakeya.ML2Core.ambient_sharp_gain_ge`) or anything else that meets `hexp`. -/
theorem dichotomy_of_rungFactors
    {β ϖ : ℝ} {gain dens : ℝ → ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    {ηin : ℝ} (hηinν : ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens)
    {C : NNReal} {Kl cl : ℕ} (hC : 1 ≤ C)
    (hpkg : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      0 < δ ∧ δ ≤ 1 ∧
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-ηin)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ ηin →
        (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
        s.Nonempty ∧
        (ML2Shading.DichotomyLeft (β / 2) s T
          ∨ ∃ u' ⊆ s, ∃ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∃ lam : NNReal,
              δ ^ ηin / 2 ≤ lam ∧ 0 < lam ∧ u'.Nonempty ∧
              (∀ i, (W i).toTube = (T i).toTube) ∧
              (∀ i, (W i).shade ⊆ (T i).shade) ∧
              ML2Shaded.HasDenseShading lam u' (fun i ↦ (T i).toShadedBody) ∧
              ML2Shaded.HasComparableDensities lam⁻¹ u'
                  (fun i ↦ (T i).toShadedBody) ∧
              (lam : ENNReal)
                    * (Tube.le_volume.c
                        (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
                    * (∑ i ∈ s, volume (T i).shade)
                  ≤ 2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                          + ML2Spine.spineNu β ϖ ε₁ gain dens)))
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
                    ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
                    (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
                    (ML2Spine.spineCount ϖ ε₁) a b m))
    {gm : ℝ → ℝ} {εf εc κc κ' θ₁ θ₂ : ℝ}
    (hκc : 0 < κc) (hκ' : 0 < κ') (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hexp : ∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
      6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin
        ≤ gm X - εf - (εc + X) - κ')
    (hfac : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
          NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (Cstar : ENNReal) (a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
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
        Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ u (fun i ↦ (T i).toShadedBody) →
        (δ : NNReal) ^ ηin / 2 ≤ lam →
        (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
        Cstar ≤ (δ : ENNReal) ^ (-κc) →
        Cu ≤ max C 4 →
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
            ≤ (δ : ENNReal) ^ (gm (ML2Spine.spineRung β ϖ ε₁ gain dens m))
              * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset
                  ι)).card : ENNReal) ^ β ∧
        ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
            ≤ (δ : ENNReal) ^ (-(εc + ML2Spine.spineRung β ϖ ε₁ gain dens m))
              * ((tθ'.card : ℕ) : ENNReal) ^ β) :
    ML2Assembly.Dichotomy.{u} β (β / 2) (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) ηin := by
  classical
  have hsp := ML2Spine.spineRung_isSpine hβ0 hβ1 hϖ hε₁ hgain hdens
  have hν0 : 0 < ML2Spine.spineNu β ϖ ε₁ gain dens :=
    ML2Spine.spineNu_pos hβ0 hϖ hε₁ hgain hdens
  have hν1 : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ 1 := by
    have := ML2Inputs.spineNu_le_div_48000 hβ0 hβ1 hϖ hε₁ hgain hdens
    linarith
  have hηin1 : ηin ≤ 1 := hηinν.trans hν1
  refine dichotomy_of_dichotomyLeft_or_gain ?_
  -- the two seams, and the thresholds, all chosen before the scale
  obtain ⟨M₁, hM₁0, hseam₁⟩ := exists_windowSeam.{u} (E := EuclideanSpace ℝ (Fin 3))
  obtain ⟨M₂, hM₂0, hseam₂⟩ := exists_coarseWindowSeam.{u} (E := EuclideanSpace ℝ (Fin 3))
  set Mseam : ℕ := max M₁ M₂ with hMseam
  have hcc0 : 0 < Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
    Tube.le_volume.c_pos _
  have hCuu1 : (1 : NNReal) ≤ max C 4 := le_trans hC (le_max_left _ _)
  obtain ⟨d1, hd10, hd1⟩ :=
    ML2Reduction.exists_threshold_coe_const_le_rpow_neg
      (C := max 1 (8 * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2 *
        ((Mseam : NNReal) * max C 4 * max C 4) /
        (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2))
      (le_max_left _ _) (κ := θ₂) hθ₂
  obtain ⟨Cε, hCε⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (κ' / 20) (by positivity)
  obtain ⟨d2, hd20, hd2⟩ :=
    ML2Reduction.exists_threshold_const_le_rpow_neg
      (C := max 1 (Cε ^ 2 * (max C 4) ^ 5)) (le_max_left _ _)
      (κ := κ' / 2) (by positivity)
  obtain ⟨dT, hdT0, hdT1, hdT⟩ :=
    StickyKakeya.exists_threshold_totalLoss_le C hC Kl cl θ₁ hθ₁
  obtain ⟨dL, hdL0, hdL1, hdL⟩ := exists_threshold_two_mul_ssfGridLen_le_log
  obtain ⟨d3, hd30, hd3⟩ :=
    ML2Reduction.exists_threshold_coe_const_le_rpow_neg (C := C) hC (κ := κc / 2)
      (by positivity)
  obtain ⟨dT', hdT'0, hdT'1, hdT'⟩ :=
    StickyKakeya.exists_threshold_totalLoss_le C hC Kl cl (κc / 2) (by positivity)
  filter_upwards [hpkg, hfac, ML2Assembly.eventually_card_thresholds,
    Ioc_mem_nhdsGT hd10, Ioc_mem_nhdsGT hd20, Ioc_mem_nhdsGT hdT0, Ioc_mem_nhdsGT hdL0,
    Ioc_mem_nhdsGT hd30, Ioc_mem_nhdsGT hdT'0]
    with δ hpkgδ hfacδ hthr hm1 hm2 hmT hmL hm3 hmT'
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
        ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
        (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
        (ML2Spine.spineCount ϖ ε₁) aa bb mm := by
    have hfun : (fun i ↦ (W i).toTube) = (fun i ↦ (T i).toTube) := funext htube
    exact hfun ▸ ⟨𝒲.tubeUniform, hwinW⟩
  -- the crude cardinality ceiling
  have hcard4 : (s.card : ℝ) ≤ (δ : ℝ) ^ (-4 : ℝ) :=
    ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s T hball hηin1 hKTs
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
    have hpow : (0 : NNReal) < δ ^ ηin := NNReal.rpow_pos hδ0
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
  -- the two-scale loss, absorbed at `κ'`
  have hσb1 : Tube.gridScale δ (Tube.ssfGridLen δ) bb ≤ 1 := le_trans hτθ hθ1
  have hCuu5one : (1 : NNReal) ≤ (max C 4 : NNReal) ^ 5 := one_le_pow₀ hCuu1
  have hCuu5ne : ((max C 4 : NNReal) ^ 5) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hCuu5one)
  have hLfinal : ∀ n₁ n₂ : ℕ, 0 < n₁ → 0 < n₂ →
      (n₁ : NNReal) ≤ δ ^ (-(4 : ℝ)) → (n₂ : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₁ δ *
          ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₂
            (Tube.gridScale δ (Tube.ssfGridLen δ) bb) : NNReal) : ENNReal)
        * ((((max C 4 : NNReal) ^ 5 : NNReal) : ENNReal)) ^ β ≤ (δ : ENNReal) ^ (-κ') := by
    intro n₁ n₂ hn1p hn2p hn1 hn2
    have hprod := spineScaleLoss_prod_le hδ0 hδ1 hδτ hσb1 hn1p hn2p hn1 hn2
      (ε := κ' / 20) (by positivity) hCε
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
        ≤ (Cε ^ 2 * δ ^ (-(10 * (κ' / 20)))) * ((max C 4 : NNReal) ^ 5) :=
          mul_le_mul' hprod hβpow
      _ = (Cε ^ 2 * (max C 4 : NNReal) ^ 5) * δ ^ (-(κ' / 2)) := by
          rw [show (10 : ℝ) * (κ' / 20) = κ' / 2 by ring]; ring
      _ ≤ δ ^ (-(κ' / 2)) * δ ^ (-(κ' / 2)) := by
          gcongr
          exact le_trans (le_max_right _ _) (hd2 δ hδ0 hm2.2)
      _ = δ ^ (-κ') := by
          rw [← NNReal.rpow_add hδ0.ne']
          congr 1
          ring
  -- the pushback ledger, absorbed: `g = 6ν + θ₁ + θ₂ + 2η_in` against the target `4ν`
  have hlamE : (δ : ENNReal) ^ ηin ≤ 2 * (lam : ENNReal) := by
    have hnn : (δ : NNReal) ^ ηin ≤ 2 * lam := by
      rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 2)] at hlamlow
      calc (δ : NNReal) ^ ηin ≤ lam * 2 := hlamlow
        _ = 2 * lam := by ring
    calc (δ : ENNReal) ^ ηin = (((δ : NNReal) ^ ηin : NNReal) : ENNReal) :=
          (ENNReal.coe_rpow_of_ne_zero hδ0.ne' _).symm
      _ ≤ ((2 * lam : NNReal) : ENNReal) := ENNReal.coe_le_coe.mpr hnn
      _ = 2 * (lam : ENNReal) := by push_cast; ring
  have habs : (2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
            + ML2Spine.spineNu β ϖ ε₁ gain dens)))
          * StickyKakeya.totalLoss C Kl cl δ)
        * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * ((((Mseam : NNReal) * max C 4 * max C 4 : NNReal) : ENNReal)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * (δ : ENNReal) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)
      ≤ ((lam : ENNReal)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * ((lam : ENNReal)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) := by
    have hδEne : (δ : ENNReal) ≠ 0 := by simpa using hδ0.ne'
    have hδEtop : (δ : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
    have hA : ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
          + ML2Spine.spineNu β ϖ ε₁ gain dens)))
        = (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
          + ML2Spine.spineNu β ϖ ε₁ gain dens)) :=
      ofReal_rpow_coe hδ0 _
    have hT : StickyKakeya.totalLoss C Kl cl δ ≤ (δ : ENNReal) ^ (-θ₁) := by
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
        ≤ (δ : ENNReal) ^ (-θ₂)
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
    have e1 : (δ : ENNReal) ^ (-θ₂) * ((δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
            + ML2Spine.spineNu β ϖ ε₁ gain dens))
          * (δ : ENNReal) ^ (-θ₁)
          * (δ : ENNReal) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin))
        = (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + 2 * ηin) := by
      rw [← ENNReal.rpow_add _ _ hδEne hδEtop, ← ENNReal.rpow_add _ _ hδEne hδEtop,
        ← ENNReal.rpow_add _ _ hδEne hδEtop]
      congr 1
      ring
    have e2 : (δ : ENNReal) ^ ηin * (δ : ENNReal) ^ ηin
          * (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens)
        = (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + 2 * ηin) := by
      rw [← ENNReal.rpow_add _ _ hδEne hδEtop, ← ENNReal.rpow_add _ _ hδEne hδEtop]
      congr 1
      ring
    refine (ENNReal.mul_le_mul_iff_left (by norm_num : (4 : ENNReal) ≠ 0)
      (by norm_num : (4 : ENNReal) ≠ (⊤ : ENNReal))).mp ?_
    calc ((2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                + ML2Spine.spineNu β ϖ ε₁ gain dens)))
              * StickyKakeya.totalLoss C Kl cl δ)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
            * ((((Mseam : NNReal) * max C 4 * max C 4 : NNReal) : ENNReal)
              * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
            * (δ : ENNReal) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)) * 4
        ≤ ((2 * ((δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                + ML2Spine.spineNu β ϖ ε₁ gain dens)) * (δ : ENNReal) ^ (-θ₁))
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
            * ((((Mseam : NNReal) * max C 4 * max C 4 : NNReal) : ENNReal)
              * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
            * (δ : ENNReal) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)) * 4 := by
          rw [hA]; gcongr
      _ = ((8 : ENNReal)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2
            * (((Mseam : NNReal) * max C 4 * max C 4 : NNReal) : ENNReal))
          * ((δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                + ML2Spine.spineNu β ϖ ε₁ gain dens)) * (δ : ENNReal) ^ (-θ₁)
              * (δ : ENNReal) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)) := by
          ring
      _ ≤ ((δ : ENNReal) ^ (-θ₂)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2)
          * ((δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                + ML2Spine.spineNu β ϖ ε₁ gain dens)) * (δ : ENNReal) ^ (-θ₁)
              * (δ : ENNReal) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)) := by
          gcongr
      _ = (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2
          * ((δ : ENNReal) ^ (-θ₂) * ((δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                + ML2Spine.spineNu β ϖ ε₁ gain dens))
              * (δ : ENNReal) ^ (-θ₁)
              * (δ : ENNReal) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin))) := by
          ring
      _ = (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2
          * (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + 2 * ηin) := by rw [e1]
      _ = (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2
          * ((δ : ENNReal) ^ ηin * (δ : ENNReal) ^ ηin)
          * (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) := by
          rw [← e2]; ring
      _ ≤ (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2
          * ((2 * (lam : ENNReal)) * (2 * (lam : ENNReal)))
          * (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) := by
          gcongr
      _ = (((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * ((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens)) * 4 := by ring
  -- the numeric inputs of the factor interface
  have hδEne : (δ : ENNReal) ≠ 0 := by simpa using hδ0.ne'
  have hδEtop : (δ : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
  have hCstarB : (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ
      ≤ (δ : ENNReal) ^ (-κc) := by
    have hT : StickyKakeya.totalLoss C Kl cl δ ≤ (δ : ENNReal) ^ (-(κc / 2)) := by
      rw [← ofReal_rpow_coe hδ0]
      exact hdT' hδ0 hmT'.2
    calc (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ
        ≤ (δ : ENNReal) ^ (-(κc / 2)) * (δ : ENNReal) ^ (-(κc / 2)) :=
          mul_le_mul' (hd3 δ hδ0 hm3.2) hT
      _ = (δ : ENNReal) ^ (-κc) := by
          rw [← ENNReal.rpow_add _ _ hδEne hδEtop]
          congr 1
          ring
  have hmaxu' : Kakeya.maxDensity u' (fun i ↦ (T i).toConvexSpaceBody)
      ≤ (δ : ENNReal) ^ (-ηin) := (Kakeya.maxDensity_mono _ hu's).trans hKTs
  have hs₁ne' : ({i ∈ u' | 𝒰.cover.assign bb i ∈ t₁} : Finset ι).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hmasspos
    simp at hmasspos
  have hune : u'.Nonempty := hs₁ne'.mono (Finset.filter_subset _ _)
  have hfacw := hfacδ u' T (max C 4) lam 𝒰
    ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) aa bb mm hwin
    v t₀ t₁ ht₁ hballt hballs ht₀ hcn hballt₀ hballu' hune hmaxu' hdenseu hcompu hlamlow hcardu
    hCstarB le_rfl hmasspos hδτ hτθ hθ1
  have hX : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ ML2Spine.spineRung β ϖ ε₁ gain dens mm :=
    hsp.rung_mono (Nat.zero_le mm)
  refine sum_shade_gain_of_window (β := β) hβ0.le hδ0 hδ1 hlam0 hu's hdenseu 𝒰 hwin ht₁
    hcardseam hmasspos
    (εf := εf) (gm := gm (ML2Spine.spineRung β ϖ ε₁ gain dens mm))
    (εc := εc + ML2Spine.spineRung β ϖ ε₁ gain dens mm) (κ := κ')
    (g := 6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)
    (gt := 4 * ML2Spine.spineNu β ϖ ε₁ gain dens)
    hcardu hfacw hLfinal (hexp _ hX) hmassloss habs

open Classical in
/-- **The window branch, wired at the rung, with the window read as
`IsKatzTaoDividingWindowLevels`.**
The level twin of `Kakeya.ML2Core.dichotomy_of_rungFactors` (§2.8): the package `hpkg` hands
the twin window and the factor hypothesis `hfac` is asked only at twin windows, so a producer that
needs the source's level clause can discharge it.  Statement and proof are otherwise the existing
ones, verbatim; the seam and gain lemmas read the parent through `toIsKatzTaoDividingWindow`.

The existing docstring follows.

`Kakeya.ML2Core.dichotomy_of_windowFactors` with the three changes the module docstring lists.

* The package `hpkg` is on the constructed spine and at the input density exponent `η_in ≤ ν`
  (`Kakeya.ML2Core.exists_dichotomyLeft_or_window_spine`), so the dense-shading floor it hands the
  factors is `δ^{η_in}/2`.
* The factor exponents are read **at the window's rung** `X = η_m`: the middle gain is `gm X`, a
  function of the rung, and the coarse cost is `εc + X` — the `+ ηl m` of
  `Kakeya.ML2Reduction.exists_coarse_factor_complete`'s own binder — instead of the flattened
  `ε₁/25`.  The budget `hexp` is then a statement about every rung `X ≥ ν`, and it is checked
  *inside* the window's scope.
* The pushback overhead is `2ν + 2η_in + θ₁ + θ₂` instead of `6ν`: the two movable terms —
  `StickyKakeya.totalLoss` and the seam constants — sit at free thresholds `θ₁, θ₂`, and the two
  `λ⁻¹`'s are read at the input density `η_in`.  Only the package's cardinality loss `δ^{-2ν}`
  stays at `ν`, being a clause of the package.  So the internal gain `g` the split has to
  produce is `g = 6ν + θ₁ + θ₂ + 2η_in`, against the target `4ν`.

The middle factor's exponent is a *function* `gm` of the rung so that a producer may hand in
`47 X/5` (`Kakeya.ML2Core.middle_factor_of_edNodes_sharp` transported at the window's own
separation exponent, `Kakeya.ML2Core.ambient_sharp_gain_ge`) or anything else that meets `hexp`. -/
theorem dichotomy_of_rungFactors_levels
    {β ϖ : ℝ} {gain dens : ℝ → ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    {ηin : ℝ} (hηinν : ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens)
    {C : NNReal} {Kl cl : ℕ} (hC : 1 ≤ C)
    (hpkg : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      0 < δ ∧ δ ≤ 1 ∧
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-ηin)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ ηin →
        (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
        s.Nonempty ∧
        (ML2Shading.DichotomyLeft (β / 2) s T
          ∨ ∃ u' ⊆ s, ∃ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∃ lam : NNReal,
              δ ^ ηin / 2 ≤ lam ∧ 0 < lam ∧ u'.Nonempty ∧
              (∀ i, (W i).toTube = (T i).toTube) ∧
              (∀ i, (W i).shade ⊆ (T i).shade) ∧
              ML2Shaded.HasDenseShading lam u' (fun i ↦ (T i).toShadedBody) ∧
              ML2Shaded.HasComparableDensities lam⁻¹ u'
                  (fun i ↦ (T i).toShadedBody) ∧
              (lam : ENNReal)
                    * (Tube.le_volume.c
                        (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
                    * (∑ i ∈ s, volume (T i).shade)
                  ≤ 2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                          + ML2Spine.spineNu β ϖ ε₁ gain dens)))
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
                ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindowLevels 𝒲.tubeUniform
                    ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
                    (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
                    (ML2Spine.spineCount ϖ ε₁) a b m))
    {gm : ℝ → ℝ} {εf εc κc κ' θ₁ θ₂ : ℝ}
    (hκc : 0 < κc) (hκ' : 0 < κ') (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hexp : ∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
      6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin
        ≤ gm X - εf - (εc + X) - κ')
    (hfac : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
          NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (Cstar : ENNReal) (a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
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
        Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ u (fun i ↦ (T i).toShadedBody) →
        (δ : NNReal) ^ ηin / 2 ≤ lam →
        (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
        Cstar ≤ (δ : ENNReal) ^ (-κc) →
        Cu ≤ max C 4 →
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
            ≤ (δ : ENNReal) ^ (gm (ML2Spine.spineRung β ϖ ε₁ gain dens m))
              * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset
                  ι)).card : ENNReal) ^ β ∧
        ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
            ≤ (δ : ENNReal) ^ (-(εc + ML2Spine.spineRung β ϖ ε₁ gain dens m))
              * ((tθ'.card : ℕ) : ENNReal) ^ β) :
    ML2Assembly.Dichotomy.{u} β (β / 2) (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) ηin := by
  classical
  have hsp := ML2Spine.spineRung_isSpine hβ0 hβ1 hϖ hε₁ hgain hdens
  have hν0 : 0 < ML2Spine.spineNu β ϖ ε₁ gain dens :=
    ML2Spine.spineNu_pos hβ0 hϖ hε₁ hgain hdens
  have hν1 : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ 1 := by
    have := ML2Inputs.spineNu_le_div_48000 hβ0 hβ1 hϖ hε₁ hgain hdens
    linarith
  have hηin1 : ηin ≤ 1 := hηinν.trans hν1
  refine dichotomy_of_dichotomyLeft_or_gain ?_
  -- the two seams, and the thresholds, all chosen before the scale
  obtain ⟨M₁, hM₁0, hseam₁⟩ := exists_windowSeam.{u} (E := EuclideanSpace ℝ (Fin 3))
  obtain ⟨M₂, hM₂0, hseam₂⟩ := exists_coarseWindowSeam.{u} (E := EuclideanSpace ℝ (Fin 3))
  set Mseam : ℕ := max M₁ M₂ with hMseam
  have hcc0 : 0 < Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
    Tube.le_volume.c_pos _
  have hCuu1 : (1 : NNReal) ≤ max C 4 := le_trans hC (le_max_left _ _)
  obtain ⟨d1, hd10, hd1⟩ :=
    ML2Reduction.exists_threshold_coe_const_le_rpow_neg
      (C := max 1 (8 * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2 *
        ((Mseam : NNReal) * max C 4 * max C 4) /
        (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ^ 2))
      (le_max_left _ _) (κ := θ₂) hθ₂
  obtain ⟨Cε, hCε⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (κ' / 20) (by positivity)
  obtain ⟨d2, hd20, hd2⟩ :=
    ML2Reduction.exists_threshold_const_le_rpow_neg
      (C := max 1 (Cε ^ 2 * (max C 4) ^ 5)) (le_max_left _ _)
      (κ := κ' / 2) (by positivity)
  obtain ⟨dT, hdT0, hdT1, hdT⟩ :=
    StickyKakeya.exists_threshold_totalLoss_le C hC Kl cl θ₁ hθ₁
  obtain ⟨dL, hdL0, hdL1, hdL⟩ := exists_threshold_two_mul_ssfGridLen_le_log
  obtain ⟨d3, hd30, hd3⟩ :=
    ML2Reduction.exists_threshold_coe_const_le_rpow_neg (C := C) hC (κ := κc / 2)
      (by positivity)
  obtain ⟨dT', hdT'0, hdT'1, hdT'⟩ :=
    StickyKakeya.exists_threshold_totalLoss_le C hC Kl cl (κc / 2) (by positivity)
  filter_upwards [hpkg, hfac, ML2Assembly.eventually_card_thresholds,
    Ioc_mem_nhdsGT hd10, Ioc_mem_nhdsGT hd20, Ioc_mem_nhdsGT hdT0, Ioc_mem_nhdsGT hdL0,
    Ioc_mem_nhdsGT hd30, Ioc_mem_nhdsGT hdT'0]
    with δ hpkgδ hfacδ hthr hm1 hm2 hmT hmL hm3 hmT'
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
      ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰
        ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
        (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
        (ML2Spine.spineCount ϖ ε₁) aa bb mm := by
    have hfun : (fun i ↦ (W i).toTube) = (fun i ↦ (T i).toTube) := funext htube
    exact hfun ▸ ⟨𝒲.tubeUniform, hwinW⟩
  have hwinP := hwin.toIsKatzTaoDividingWindow
  -- the crude cardinality ceiling
  have hcard4 : (s.card : ℝ) ≤ (δ : ℝ) ^ (-4 : ℝ) :=
    ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s T hball hηin1 hKTs
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
        hseam₁ 𝒰 hδ0 hδ1 (hdL δ hδ0 hmL.2) hwinP hballu'
      refine ⟨v, ∅, t₁, fun h ↦ absurd ha0 h, ht₁, fun h ↦ absurd ha0 h, hballt, hballs,
        fun h ↦ absurd ha0 h, ?_, hδτ, hτθ, hθ1⟩
      refine hcardseam.trans (mul_le_mul' (mul_le_mul' (mul_le_mul'
        (hMcast M₁ (le_max_left _ _)) le_rfl) le_rfl) le_rfl)
    · obtain ⟨v, t₀, t₁, ht₀, ht₁, hballt₀, hballt, hballs, hcn, hcardseam, hδτ, hτθ, hθ1⟩ :=
        hseam₂ 𝒰 hδ0 hδ1 (Nat.one_le_iff_ne_zero.mpr ha0) (hdL δ hδ0 hmL.2) hwinP hballu'
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
    have hpow : (0 : NNReal) < δ ^ ηin := NNReal.rpow_pos hδ0
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
  -- the two-scale loss, absorbed at `κ'`
  have hσb1 : Tube.gridScale δ (Tube.ssfGridLen δ) bb ≤ 1 := le_trans hτθ hθ1
  have hCuu5one : (1 : NNReal) ≤ (max C 4 : NNReal) ^ 5 := one_le_pow₀ hCuu1
  have hCuu5ne : ((max C 4 : NNReal) ^ 5) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hCuu5one)
  have hLfinal : ∀ n₁ n₂ : ℕ, 0 < n₁ → 0 < n₂ →
      (n₁ : NNReal) ≤ δ ^ (-(4 : ℝ)) → (n₂ : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₁ δ *
          ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₂
            (Tube.gridScale δ (Tube.ssfGridLen δ) bb) : NNReal) : ENNReal)
        * ((((max C 4 : NNReal) ^ 5 : NNReal) : ENNReal)) ^ β ≤ (δ : ENNReal) ^ (-κ') := by
    intro n₁ n₂ hn1p hn2p hn1 hn2
    have hprod := spineScaleLoss_prod_le hδ0 hδ1 hδτ hσb1 hn1p hn2p hn1 hn2
      (ε := κ' / 20) (by positivity) hCε
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
        ≤ (Cε ^ 2 * δ ^ (-(10 * (κ' / 20)))) * ((max C 4 : NNReal) ^ 5) :=
          mul_le_mul' hprod hβpow
      _ = (Cε ^ 2 * (max C 4 : NNReal) ^ 5) * δ ^ (-(κ' / 2)) := by
          rw [show (10 : ℝ) * (κ' / 20) = κ' / 2 by ring]; ring
      _ ≤ δ ^ (-(κ' / 2)) * δ ^ (-(κ' / 2)) := by
          gcongr
          exact le_trans (le_max_right _ _) (hd2 δ hδ0 hm2.2)
      _ = δ ^ (-κ') := by
          rw [← NNReal.rpow_add hδ0.ne']
          congr 1
          ring
  -- the pushback ledger, absorbed: `g = 6ν + θ₁ + θ₂ + 2η_in` against the target `4ν`
  have hlamE : (δ : ENNReal) ^ ηin ≤ 2 * (lam : ENNReal) := by
    have hnn : (δ : NNReal) ^ ηin ≤ 2 * lam := by
      rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 2)] at hlamlow
      calc (δ : NNReal) ^ ηin ≤ lam * 2 := hlamlow
        _ = 2 * lam := by ring
    calc (δ : ENNReal) ^ ηin = (((δ : NNReal) ^ ηin : NNReal) : ENNReal) :=
          (ENNReal.coe_rpow_of_ne_zero hδ0.ne' _).symm
      _ ≤ ((2 * lam : NNReal) : ENNReal) := ENNReal.coe_le_coe.mpr hnn
      _ = 2 * (lam : ENNReal) := by push_cast; ring
  have habs : (2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
            + ML2Spine.spineNu β ϖ ε₁ gain dens)))
          * StickyKakeya.totalLoss C Kl cl δ)
        * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * ((((Mseam : NNReal) * max C 4 * max C 4 : NNReal) : ENNReal)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * (δ : ENNReal) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)
      ≤ ((lam : ENNReal)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * ((lam : ENNReal)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) := by
    have hδEne : (δ : ENNReal) ≠ 0 := by simpa using hδ0.ne'
    have hδEtop : (δ : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
    have hA : ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
          + ML2Spine.spineNu β ϖ ε₁ gain dens)))
        = (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
          + ML2Spine.spineNu β ϖ ε₁ gain dens)) :=
      ofReal_rpow_coe hδ0 _
    have hT : StickyKakeya.totalLoss C Kl cl δ ≤ (δ : ENNReal) ^ (-θ₁) := by
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
        ≤ (δ : ENNReal) ^ (-θ₂)
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
    have e1 : (δ : ENNReal) ^ (-θ₂) * ((δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
            + ML2Spine.spineNu β ϖ ε₁ gain dens))
          * (δ : ENNReal) ^ (-θ₁)
          * (δ : ENNReal) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin))
        = (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + 2 * ηin) := by
      rw [← ENNReal.rpow_add _ _ hδEne hδEtop, ← ENNReal.rpow_add _ _ hδEne hδEtop,
        ← ENNReal.rpow_add _ _ hδEne hδEtop]
      congr 1
      ring
    have e2 : (δ : ENNReal) ^ ηin * (δ : ENNReal) ^ ηin
          * (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens)
        = (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + 2 * ηin) := by
      rw [← ENNReal.rpow_add _ _ hδEne hδEtop, ← ENNReal.rpow_add _ _ hδEne hδEtop]
      congr 1
      ring
    refine (ENNReal.mul_le_mul_iff_left (by norm_num : (4 : ENNReal) ≠ 0)
      (by norm_num : (4 : ENNReal) ≠ (⊤ : ENNReal))).mp ?_
    calc ((2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                + ML2Spine.spineNu β ϖ ε₁ gain dens)))
              * StickyKakeya.totalLoss C Kl cl δ)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
            * ((((Mseam : NNReal) * max C 4 * max C 4 : NNReal) : ENNReal)
              * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
            * (δ : ENNReal) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)) * 4
        ≤ ((2 * ((δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                + ML2Spine.spineNu β ϖ ε₁ gain dens)) * (δ : ENNReal) ^ (-θ₁))
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
            * ((((Mseam : NNReal) * max C 4 * max C 4 : NNReal) : ENNReal)
              * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
            * (δ : ENNReal) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)) * 4 := by
          rw [hA]; gcongr
      _ = ((8 : ENNReal)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2
            * (((Mseam : NNReal) * max C 4 * max C 4 : NNReal) : ENNReal))
          * ((δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                + ML2Spine.spineNu β ϖ ε₁ gain dens)) * (δ : ENNReal) ^ (-θ₁)
              * (δ : ENNReal) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)) := by
          ring
      _ ≤ ((δ : ENNReal) ^ (-θ₂)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2)
          * ((δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                + ML2Spine.spineNu β ϖ ε₁ gain dens)) * (δ : ENNReal) ^ (-θ₁)
              * (δ : ENNReal) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)) := by
          gcongr
      _ = (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2
          * ((δ : ENNReal) ^ (-θ₂) * ((δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens
                + ML2Spine.spineNu β ϖ ε₁ gain dens))
              * (δ : ENNReal) ^ (-θ₁)
              * (δ : ENNReal) ^ (6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin))) := by
          ring
      _ = (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2
          * (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + 2 * ηin) := by rw [e1]
      _ = (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2
          * ((δ : ENNReal) ^ ηin * (δ : ENNReal) ^ ηin)
          * (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) := by
          rw [← e2]; ring
      _ ≤ (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) ^ 2
          * ((2 * (lam : ENNReal)) * (2 * (lam : ENNReal)))
          * (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) := by
          gcongr
      _ = (((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * ((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens)) * 4 := by ring
  -- the numeric inputs of the factor interface
  have hδEne : (δ : ENNReal) ≠ 0 := by simpa using hδ0.ne'
  have hδEtop : (δ : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
  have hCstarB : (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ
      ≤ (δ : ENNReal) ^ (-κc) := by
    have hT : StickyKakeya.totalLoss C Kl cl δ ≤ (δ : ENNReal) ^ (-(κc / 2)) := by
      rw [← ofReal_rpow_coe hδ0]
      exact hdT' hδ0 hmT'.2
    calc (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ
        ≤ (δ : ENNReal) ^ (-(κc / 2)) * (δ : ENNReal) ^ (-(κc / 2)) :=
          mul_le_mul' (hd3 δ hδ0 hm3.2) hT
      _ = (δ : ENNReal) ^ (-κc) := by
          rw [← ENNReal.rpow_add _ _ hδEne hδEtop]
          congr 1
          ring
  have hmaxu' : Kakeya.maxDensity u' (fun i ↦ (T i).toConvexSpaceBody)
      ≤ (δ : ENNReal) ^ (-ηin) := (Kakeya.maxDensity_mono _ hu's).trans hKTs
  have hs₁ne' : ({i ∈ u' | 𝒰.cover.assign bb i ∈ t₁} : Finset ι).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hmasspos
    simp at hmasspos
  have hune : u'.Nonempty := hs₁ne'.mono (Finset.filter_subset _ _)
  have hfacw := hfacδ u' T (max C 4) lam 𝒰
    ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) aa bb mm hwin
    v t₀ t₁ ht₁ hballt hballs ht₀ hcn hballt₀ hballu' hune hmaxu' hdenseu hcompu hlamlow hcardu
    hCstarB le_rfl hmasspos hδτ hτθ hθ1
  have hX : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ ML2Spine.spineRung β ϖ ε₁ gain dens mm :=
    hsp.rung_mono (Nat.zero_le mm)
  refine sum_shade_gain_of_window (β := β) hβ0.le hδ0 hδ1 hlam0 hu's hdenseu 𝒰 hwinP ht₁
    hcardseam hmasspos
    (εf := εf) (gm := gm (ML2Spine.spineRung β ϖ ε₁ gain dens mm))
    (εc := εc + ML2Spine.spineRung β ϖ ε₁ gain dens mm) (κ := κ')
    (g := 6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin)
    (gt := 4 * ML2Spine.spineNu β ϖ ε₁ gain dens)
    hcardu hfacw hLfinal (hexp _ hX) hmassloss habs

end RungPackage

/-! ## `GeometricCoreAt` from the middle factor at the rung -/

section TopLevel

open Classical in
/-- **`GeometricCoreAt` from the MIDDLE FACTOR at the window's rung.**

The re-cut of `Kakeya.ML2Core.geometricCoreAt_of_middleFactor`.  The hypothesis `hmid` differs
from the existing one in exactly the places the refutation
`Kakeya.ML2Core.not_middleFactor_hypothesis` exploits, and in the exponent:

* **the window is on the constructed spine** — `IsKatzTaoDividingWindow 𝒰 Cstar (spineRung …)
  (spineDiv …) (spineCount …) a b m` — so its density lower bound
  `IsKatzTaoDividingWindow.le_window_maxDensity` is read at the positive rung `η_{m+1}`.  This is
  GWZ's `tildeDeltaLargeDeltamax`, the input of step 8's count; the existing block let `ηl ≡ 0`
  (`Kakeya.ML2Core.two_le_card_nodesUnder_of_spineWindow` is the consequence that no
  one-node middle family survives the pinned block);
* **the middle gain is `47 η_m/5`**, the rung-level exponent
  `Kakeya.ML2Core.middle_factor_of_edNodes_sharp` reaches once transported at the window's own
  separation exponent (`Kakeya.ML2Core.ambient_sharp_gain_ge`), instead of the flattened
  `2 ε + 14 ε₁/25`;
* the block hands the producer `HasComparableDensities lam⁻¹ u` (the input of
  `Kakeya.ML2Core.sum_shade_retention`), the hierarchy constant's `δ`-free ceiling `Cu ≤ Cu₀`
  and `Cstar ≤ δ^{-ν/20}`, and is stated at an input density exponent `η_in ≤ ν` of the wiring's
  choice, which only weakens what the producer receives at `ν`.

**The order of choices, which is the whole point.**  `ε₁` (hence the spine and `ν`) first; then
the Katz--Tao accuracy `ε := ν/20` and the density exponents `η_f, η_c` it costs; then
`η_in := min (ν/20) (min η_f η_c / 2)`, the density slot `Kakeya.ML2Assembly.GeometricCoreAt`
leaves free.  The budget of `Kakeya.ML2Core.dichotomy_of_rungFactors` then reads, at a rung
`X ≥ ν`, `6ν + ν/10 + 2η_in ≤ 47X/5 - ν/20 - (ν/10 + X) - ν/20`, i.e. `6.2ν ≤ 8.4X - 0.2ν`,
which holds at `X = ν` with `2ν` to spare.  The existing wiring shrank `ν` instead of `η_in`, and
`Kakeya.ML2Core.spineRung_middle_gain_lt_demand` is what that costs. -/
theorem geometricCoreAt_of_rungMiddleFactor
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))
    (hmid : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{u} β ϖ gain dens →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ ε₁ : ℝ, 0 < ε₁ →
      ∀ ηin : ℝ, 0 < ηin → ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens →
      ∀ Cu₀ : NNReal,
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
          NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (Cstar : ENNReal) (a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
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
        Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ u (fun i ↦ (T i).toShadedBody) →
        (δ : NNReal) ^ ηin / 2 ≤ lam →
        (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
        Cstar ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)) →
        Cu ≤ Cu₀ →
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
            ≤ (δ : ENNReal) ^ (47 * ML2Spine.spineRung β ϖ ε₁ gain dens m / 5)
              * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset
                  ι)).card : ENNReal) ^ β) :
    ML2Assembly.GeometricCoreAt.{u} := by
  classical
  refine geometricCoreAt_of_pointwise (fun β ϖ gain dens hβ0 hβ1 hp hKT hF ↦ ?_)
  obtain ⟨ε₁, hε₁, hsmall⟩ :=
    exists_dichotomyLeft_or_window_spine.{u} hSFE hβ0 hβ1 hp.window_pos hp.gain_pos hp.dens_pos
  have hsp := ML2Spine.spineRung_isSpine hβ0 hβ1 hp.window_pos hε₁ hp.gain_pos hp.dens_pos
  have hν0 : 0 < ML2Spine.spineNu β ϖ ε₁ gain dens :=
    ML2Spine.spineNu_pos hβ0 hp.window_pos hε₁ hp.gain_pos hp.dens_pos
  have hν1 : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ 1 := by
    have := ML2Inputs.spineNu_le_div_48000 hβ0 hβ1 hp.window_pos hε₁ hp.gain_pos hp.dens_pos
    linarith
  -- the Katz--Tao accuracy, chosen AFTER the spine
  obtain ⟨ηf, hηf, hfineev⟩ :=
    exists_fine_factor_at_window.{u} (E := (EuclideanSpace ℝ (Fin 3))) hβ0.le hKT
      (ε := ML2Spine.spineNu β ϖ ε₁ gain dens / 20) (by positivity)
  obtain ⟨ηc, hηc, hcoarseev⟩ :=
    exists_coarse_factor_complete.{u} (E := (EuclideanSpace ℝ (Fin 3))) hβ0.le hβ1 hKT
      (ε := ML2Spine.spineNu β ϖ ε₁ gain dens / 20) (by positivity)
  -- the input density exponent, chosen AFTER the accuracy
  have hminpos : 0 < min ηf ηc := lt_min hηf hηc
  have hminf : min ηf ηc ≤ ηf := min_le_left _ _
  have hminc : min ηf ηc ≤ ηc := min_le_right _ _
  set ηin : ℝ := min (ML2Spine.spineNu β ϖ ε₁ gain dens / 20) (min ηf ηc / 2) with hηin
  have hηin0 : 0 < ηin := lt_min (by positivity) (by positivity)
  have hηin20 : ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens / 20 := min_le_left _ _
  have hηinν : ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens := by linarith
  have hηinhalf : ηin ≤ min ηf ηc / 2 := min_le_right _ _
  obtain ⟨C, Kl, cl, hC, hev⟩ := hsmall ε₁ hε₁ le_rfl ηin hηinν
  have hCuu1 : (1 : NNReal) ≤ max C 4 := le_trans hC (le_max_left _ _)
  refine ⟨ε₁, hε₁, ηin, hηin0, hηinν.trans hν1, ?_⟩
  refine dichotomy_of_rungFactors hβ0 hβ1 hp.window_pos hp.gain_pos hp.dens_pos hε₁ hηinν hC hev
    (gm := fun X ↦ 47 * X / 5) (εf := ML2Spine.spineNu β ϖ ε₁ gain dens / 20)
    (εc := ML2Spine.spineNu β ϖ ε₁ gain dens / 20 + ML2Spine.spineNu β ϖ ε₁ gain dens / 20)
    (κc := ML2Spine.spineNu β ϖ ε₁ gain dens / 20) (κ' := ML2Spine.spineNu β ϖ ε₁ gain dens / 20)
    (θ₁ := ML2Spine.spineNu β ϖ ε₁ gain dens / 20) (θ₂ := ML2Spine.spineNu β ϖ ε₁ gain dens / 20)
    (by positivity) (by positivity) (by positivity) (by positivity) ?_ ?_
  · -- the rung-level budget: `6.2 ν ≤ 8.4 X - 0.2 ν` for every `X ≥ ν`
    intro X hX
    linarith
  -- the three factors from the middle factor, at this scale
  obtain ⟨Cε, hCε⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (min ηf ηc / 40) (by positivity)
  obtain ⟨d5, hd50, hd5⟩ :=
    ML2Reduction.exists_threshold_const_le_rpow_neg (C := max 1 (2 * Cε ^ 2)) (le_max_left _ _)
      (κ := min ηf ηc / 4) (by positivity)
  obtain ⟨d6, hd60, hd6⟩ :=
    ML2Reduction.exists_threshold_coe_const_le_rpow_neg (C := max C 4) hCuu1
      (κ := ML2Spine.spineNu β ϖ ε₁ gain dens / 10) (by positivity)
  filter_upwards [hfineev, hcoarseev,
    hmid β ϖ gain dens hβ0 hβ1 hp hKT hF ε₁ hε₁ ηin hηin0 hηinν (max C 4),
    Ioc_mem_nhdsGT hd50, Ioc_mem_nhdsGT hd60, Ioc_mem_nhdsGT (zero_lt_one' NNReal)]
    with δ hfine hcoarse hmidδ hm5 hm6 hm01
  intro ι u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁
    ht₁ hballt hballs ht₀ hcn hballt₀ hballu hune hmaxu hdense hcomp hlamlow hcardu hCstar hCu
    hmasspos hδτ hτθ hθ1
  have hδ0 : 0 < δ := hm01.1
  have hδ1 : δ ≤ 1 := hm01.2
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  -- the middle factor, with the two-scale split it is a statement about
  obtain ⟨tτ', htτ', tθ', htθ', Yτ', Yθ, Y', jθ, hYτ', hYθ, hY', hballθ, hτne, hθne, href1,
    hfull2, hprod, hjθ, hmidbd⟩ :=
    hmidδ u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ ht₁ hballt hballs ht₀ hcn hballt₀
      hballu hune hmaxu hdense hcomp hlamlow hcardu hCstar hCu hmasspos hδτ hτθ hθ1
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
  have hlam2 : (δ : NNReal) ^ ηin ≤ 2 * lam := by
    rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 2)] at hlamlow
    calc (δ : NNReal) ^ ηin ≤ lam * 2 := hlamlow
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
      _ ≤ δ ^ ηin :=
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
  have hηlm0 : (0 : ℝ) ≤ ML2Spine.spineRung β ϖ ε₁ gain dens m := (hsp.rung_pos m).le
  have hCubnd : ((Cu : NNReal) : ENNReal) ^ (1 - β)
      ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20
          + ML2Spine.spineNu β ϖ ε₁ gain dens / 20 + ML2Spine.spineRung β ϖ ε₁ gain dens m)) := by
    have hone : (1 : ENNReal) ≤ ((max C 4 : NNReal) : ENNReal) := by exact_mod_cast hCuu1
    calc ((Cu : NNReal) : ENNReal) ^ (1 - β)
        ≤ (((max C 4 : NNReal)) : ENNReal) ^ (1 - β) :=
          ENNReal.rpow_le_rpow (by exact_mod_cast hCu) (by linarith)
      _ ≤ (((max C 4 : NNReal)) : ENNReal) ^ (1 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_le hone (by linarith)
      _ = (((max C 4 : NNReal)) : ENNReal) := ENNReal.rpow_one _
      _ ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 10)) := hd6 δ hδ0 hm6.2
      _ ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20
          + ML2Spine.spineNu β ϖ ε₁ gain dens / 20 + ML2Spine.spineRung β ϖ ε₁ gain dens m)) :=
          ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
  have hcoarsebd := hcoarse (𝒰 := 𝒰) (Cstar := Cstar)
    (ηl := ML2Spine.spineRung β ϖ ε₁ gain dens) (εd := ML2Spine.spineDiv ϖ ε₁)
    (N := ML2Spine.spineCount ϖ ε₁)
    (a := a) (b := b) (m := m) (κ := ML2Spine.spineNu β ϖ ε₁ gain dens / 20)
    (c := ML2Spine.spineNu β ϖ ε₁ gain dens / 20 + ML2Spine.spineNu β ϖ ε₁ gain dens / 20
        + ML2Spine.spineRung β ϖ ε₁ gain dens m)
    (t := tθ') (Yθ := Yθ) (v := v)
    hδ0 hδ1 hune hballu hwin hηlm0 (by positivity) hCstar (by linarith) hCubnd htθ' hYθ
    hballθ hfullc
  exact ⟨tτ', tθ', Yτ', Yθ, Y', jτ, jθ, htτ', htθ', htτ' hjτ, hjθ, hτne,
    hprod jτ hjτ jθ hjθ, hfinebd, hmidbd, hcoarsebd⟩

open Classical in
/-- **`GeometricCoreAt` from the MIDDLE FACTOR at the window's rung, with the window read as
`IsKatzTaoDividingWindowLevels`.**  The level twin of
`Kakeya.ML2Core.geometricCoreAt_of_rungMiddleFactor`
(§2.8, §10): the binder `hmid` is asked only at twin windows, so a floor producer that needs
the source's level clause can discharge it — this is where `hfloor'` lands.  Wired through
`exists_dichotomyLeft_or_window_spine_levels` and `dichotomy_of_rungFactors_levels`; statement and
proof are otherwise the existing ones, verbatim.

The existing docstring follows.

The re-cut of `Kakeya.ML2Core.geometricCoreAt_of_middleFactor`.  The hypothesis `hmid` differs
from the existing one in exactly the places the refutation
`Kakeya.ML2Core.not_middleFactor_hypothesis` exploits, and in the exponent:

* **the window is on the constructed spine** — `IsKatzTaoDividingWindow 𝒰 Cstar (spineRung …)
  (spineDiv …) (spineCount …) a b m` — so its density lower bound
  `IsKatzTaoDividingWindow.le_window_maxDensity` is read at the positive rung `η_{m+1}`.  This is
  GWZ's `tildeDeltaLargeDeltamax`, the input of step 8's count; the existing block let `ηl ≡ 0`
  (`Kakeya.ML2Core.two_le_card_nodesUnder_of_spineWindow` is the consequence that no
  one-node middle family survives the pinned block);
* **the middle gain is `47 η_m/5`**, the rung-level exponent
  `Kakeya.ML2Core.middle_factor_of_edNodes_sharp` reaches once transported at the window's own
  separation exponent (`Kakeya.ML2Core.ambient_sharp_gain_ge`), instead of the flattened
  `2 ε + 14 ε₁/25`;
* the block hands the producer `HasComparableDensities lam⁻¹ u` (the input of
  `Kakeya.ML2Core.sum_shade_retention`), the hierarchy constant's `δ`-free ceiling `Cu ≤ Cu₀`
  and `Cstar ≤ δ^{-ν/20}`, and is stated at an input density exponent `η_in ≤ ν` of the wiring's
  choice, which only weakens what the producer receives at `ν`.

**The order of choices, which is the whole point.**  `ε₁` (hence the spine and `ν`) first; then
the Katz--Tao accuracy `ε := ν/20` and the density exponents `η_f, η_c` it costs; then
`η_in := min (ν/20) (min η_f η_c / 2)`, the density slot `Kakeya.ML2Assembly.GeometricCoreAt`
leaves free.  The budget of `Kakeya.ML2Core.dichotomy_of_rungFactors` then reads, at a rung
`X ≥ ν`, `6ν + ν/10 + 2η_in ≤ 47X/5 - ν/20 - (ν/10 + X) - ν/20`, i.e. `6.2ν ≤ 8.4X - 0.2ν`,
which holds at `X = ν` with `2ν` to spare.  The existing wiring shrank `ν` instead of `η_in`, and
`Kakeya.ML2Core.spineRung_middle_gain_lt_demand` is what that costs. -/
theorem geometricCoreAt_of_rungMiddleFactor_levels
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))
    (hmid : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{u} β ϖ gain dens →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ ε₁ : ℝ, 0 < ε₁ →
      ∀ ηin : ℝ, 0 < ηin → ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens →
      ∀ Cu₀ : NNReal,
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
          NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (Cstar : ENNReal) (a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
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
        Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ u (fun i ↦ (T i).toShadedBody) →
        (δ : NNReal) ^ ηin / 2 ≤ lam →
        (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
        Cstar ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)) →
        Cu ≤ Cu₀ →
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
            ≤ (δ : ENNReal) ^ (47 * ML2Spine.spineRung β ϖ ε₁ gain dens m / 5)
              * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset
                  ι)).card : ENNReal) ^ β) :
    ML2Assembly.GeometricCoreAt.{u} := by
  classical
  refine geometricCoreAt_of_pointwise (fun β ϖ gain dens hβ0 hβ1 hp hKT hF ↦ ?_)
  obtain ⟨ε₁, hε₁, hsmall⟩ :=
    exists_dichotomyLeft_or_window_spine_levels.{u} hSFE hβ0 hβ1 hp.window_pos hp.gain_pos hp.dens_pos
  have hsp := ML2Spine.spineRung_isSpine hβ0 hβ1 hp.window_pos hε₁ hp.gain_pos hp.dens_pos
  have hν0 : 0 < ML2Spine.spineNu β ϖ ε₁ gain dens :=
    ML2Spine.spineNu_pos hβ0 hp.window_pos hε₁ hp.gain_pos hp.dens_pos
  have hν1 : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ 1 := by
    have := ML2Inputs.spineNu_le_div_48000 hβ0 hβ1 hp.window_pos hε₁ hp.gain_pos hp.dens_pos
    linarith
  -- the Katz--Tao accuracy, chosen AFTER the spine
  obtain ⟨ηf, hηf, hfineev⟩ :=
    exists_fine_factor_at_window.{u} (E := (EuclideanSpace ℝ (Fin 3))) hβ0.le hKT
      (ε := ML2Spine.spineNu β ϖ ε₁ gain dens / 20) (by positivity)
  obtain ⟨ηc, hηc, hcoarseev⟩ :=
    exists_coarse_factor_complete.{u} (E := (EuclideanSpace ℝ (Fin 3))) hβ0.le hβ1 hKT
      (ε := ML2Spine.spineNu β ϖ ε₁ gain dens / 20) (by positivity)
  -- the input density exponent, chosen AFTER the accuracy
  have hminpos : 0 < min ηf ηc := lt_min hηf hηc
  have hminf : min ηf ηc ≤ ηf := min_le_left _ _
  have hminc : min ηf ηc ≤ ηc := min_le_right _ _
  set ηin : ℝ := min (ML2Spine.spineNu β ϖ ε₁ gain dens / 20) (min ηf ηc / 2) with hηin
  have hηin0 : 0 < ηin := lt_min (by positivity) (by positivity)
  have hηin20 : ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens / 20 := min_le_left _ _
  have hηinν : ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens := by linarith
  have hηinhalf : ηin ≤ min ηf ηc / 2 := min_le_right _ _
  obtain ⟨C, Kl, cl, hC, hev⟩ := hsmall ε₁ hε₁ le_rfl ηin hηinν
  have hCuu1 : (1 : NNReal) ≤ max C 4 := le_trans hC (le_max_left _ _)
  refine ⟨ε₁, hε₁, ηin, hηin0, hηinν.trans hν1, ?_⟩
  refine dichotomy_of_rungFactors_levels hβ0 hβ1 hp.window_pos hp.gain_pos hp.dens_pos hε₁ hηinν hC
    hev
    (gm := fun X ↦ 47 * X / 5) (εf := ML2Spine.spineNu β ϖ ε₁ gain dens / 20)
    (εc := ML2Spine.spineNu β ϖ ε₁ gain dens / 20 + ML2Spine.spineNu β ϖ ε₁ gain dens / 20)
    (κc := ML2Spine.spineNu β ϖ ε₁ gain dens / 20) (κ' := ML2Spine.spineNu β ϖ ε₁ gain dens / 20)
    (θ₁ := ML2Spine.spineNu β ϖ ε₁ gain dens / 20) (θ₂ := ML2Spine.spineNu β ϖ ε₁ gain dens / 20)
    (by positivity) (by positivity) (by positivity) (by positivity) ?_ ?_
  · -- the rung-level budget: `6.2 ν ≤ 8.4 X - 0.2 ν` for every `X ≥ ν`
    intro X hX
    linarith
  -- the three factors from the middle factor, at this scale
  obtain ⟨Cε, hCε⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (min ηf ηc / 40) (by positivity)
  obtain ⟨d5, hd50, hd5⟩ :=
    ML2Reduction.exists_threshold_const_le_rpow_neg (C := max 1 (2 * Cε ^ 2)) (le_max_left _ _)
      (κ := min ηf ηc / 4) (by positivity)
  obtain ⟨d6, hd60, hd6⟩ :=
    ML2Reduction.exists_threshold_coe_const_le_rpow_neg (C := max C 4) hCuu1
      (κ := ML2Spine.spineNu β ϖ ε₁ gain dens / 10) (by positivity)
  filter_upwards [hfineev, hcoarseev,
    hmid β ϖ gain dens hβ0 hβ1 hp hKT hF ε₁ hε₁ ηin hηin0 hηinν (max C 4),
    Ioc_mem_nhdsGT hd50, Ioc_mem_nhdsGT hd60, Ioc_mem_nhdsGT (zero_lt_one' NNReal)]
    with δ hfine hcoarse hmidδ hm5 hm6 hm01
  intro ι u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁
    ht₁ hballt hballs ht₀ hcn hballt₀ hballu hune hmaxu hdense hcomp hlamlow hcardu hCstar hCu
    hmasspos hδτ hτθ hθ1
  have hδ0 : 0 < δ := hm01.1
  have hδ1 : δ ≤ 1 := hm01.2
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  -- the middle factor, with the two-scale split it is a statement about
  obtain ⟨tτ', htτ', tθ', htθ', Yτ', Yθ, Y', jθ, hYτ', hYθ, hY', hballθ, hτne, hθne, href1,
    hfull2, hprod, hjθ, hmidbd⟩ :=
    hmidδ u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ ht₁ hballt hballs ht₀ hcn hballt₀
      hballu hune hmaxu hdense hcomp hlamlow hcardu hCstar hCu hmasspos hδτ hτθ hθ1
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
  have hlam2 : (δ : NNReal) ^ ηin ≤ 2 * lam := by
    rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 2)] at hlamlow
    calc (δ : NNReal) ^ ηin ≤ lam * 2 := hlamlow
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
      _ ≤ δ ^ ηin :=
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
  have hηlm0 : (0 : ℝ) ≤ ML2Spine.spineRung β ϖ ε₁ gain dens m := (hsp.rung_pos m).le
  have hCubnd : ((Cu : NNReal) : ENNReal) ^ (1 - β)
      ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20
          + ML2Spine.spineNu β ϖ ε₁ gain dens / 20 + ML2Spine.spineRung β ϖ ε₁ gain dens m)) := by
    have hone : (1 : ENNReal) ≤ ((max C 4 : NNReal) : ENNReal) := by exact_mod_cast hCuu1
    calc ((Cu : NNReal) : ENNReal) ^ (1 - β)
        ≤ (((max C 4 : NNReal)) : ENNReal) ^ (1 - β) :=
          ENNReal.rpow_le_rpow (by exact_mod_cast hCu) (by linarith)
      _ ≤ (((max C 4 : NNReal)) : ENNReal) ^ (1 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_le hone (by linarith)
      _ = (((max C 4 : NNReal)) : ENNReal) := ENNReal.rpow_one _
      _ ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 10)) := hd6 δ hδ0 hm6.2
      _ ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20
          + ML2Spine.spineNu β ϖ ε₁ gain dens / 20 + ML2Spine.spineRung β ϖ ε₁ gain dens m)) :=
          ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
  have hcoarsebd := hcoarse (𝒰 := 𝒰) (Cstar := Cstar)
    (ηl := ML2Spine.spineRung β ϖ ε₁ gain dens) (εd := ML2Spine.spineDiv ϖ ε₁)
    (N := ML2Spine.spineCount ϖ ε₁)
    (a := a) (b := b) (m := m) (κ := ML2Spine.spineNu β ϖ ε₁ gain dens / 20)
    (c := ML2Spine.spineNu β ϖ ε₁ gain dens / 20 + ML2Spine.spineNu β ϖ ε₁ gain dens / 20
        + ML2Spine.spineRung β ϖ ε₁ gain dens m)
    (t := tθ') (Yθ := Yθ) (v := v)
    hδ0 hδ1 hune hballu hwin.toIsKatzTaoDividingWindow hηlm0 (by positivity) hCstar (by linarith)
    hCubnd htθ' hYθ
    hballθ hfullc
  exact ⟨tτ', tθ', Yτ', Yθ, Y', jτ, jθ, htτ', htθ', htτ' hjτ, hjθ, hτne,
    hprod jτ hjτ jθ hjθ, hfinebd, hmidbd, hcoarsebd⟩

end TopLevel

/-! ## The non-vacuity control: the pinned block excludes the refuting configuration -/

section Control

/-- **No coarse node of a spine-pinned window has a one-node middle family.**

`Kakeya.ML2Core.not_middleFactor_hypothesis` refutes the existing block with a single fully shaded
tube whose window has `ηl ≡ 0`.  With the window pinned to the constructed spine that
configuration is excluded: `IsKatzTaoDividingWindow.le_window_maxDensity` at the upper end
`ρ = θ (τ/θ)^{e}` of its range reads `(θ/τ)^{e η_{m+1}} ≤ C⋆ · Δ_max(𝕋_{τ∣θ}[T_θ] at ρ)`, and
`Δ_max ≤ #𝕋_{τ∣θ}[T_θ]`, so a one-node middle family would force
`δ^{-e² η_{m+1}} ≤ (θ/τ)^{e η_{m+1}} ≤ C⋆ ≤ δ^{-κ}` with `κ ≤ ν`, while the spine's first step
entry gives `e² η_{m+1} ≥ 48 ν/β ≥ 48 ν`.

This is GWZ's `tildeDeltaLargeDeltamax` doing its first job: it is the density lower bound from
which step 8's count clause is derived inside the producer, and it is the binder the existing block
had abstracted away.  Stated with `Cstar ≤ δ^{-κ}` at any `κ ≤ ν`, which covers the `ν/20` the
re-cut block carries. -/
theorem two_le_card_nodesUnder_of_spineWindow
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {δ Cu : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {ι : Type*} {u : Finset ι} {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    {Cstar : ENNReal} {a b m : ℕ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
      (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m)
    {κc : ℝ} (hκc : κc ≤ ML2Spine.spineNu β ϖ ε₁ gain dens)
    (hCstar : Cstar ≤ (δ : ENNReal) ^ (-κc))
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet a) :
    2 ≤ (𝒰.nodesUnder b a j).card := by
  classical
  have hsp := ML2Spine.spineRung_isSpine hβ0 hβ1 hϖ hε₁ hgain hdens
  have he0 : 0 < ML2Spine.spineDiv ϖ ε₁ := hsp.div_pos
  have he64 : ML2Spine.spineDiv ϖ ε₁ ≤ 1 / 64 := by
    have h1 := hsp.div_le
    have h2 : ML2Spine.spineEps₂ ϖ ε₁ ≤ 1 / 64 := ML2Spine.spineEps₂_le_inv64
    linarith
  have hη1pos : 0 < ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) := hsp.rung_pos (m + 1)
  have hν0 : 0 < ML2Spine.spineRung β ϖ ε₁ gain dens 0 := hsp.rung_pos 0
  have hstep : ML2Spine.spineRung β ϖ ε₁ gain dens m
      ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2 * β * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 48 := by
    rw [ML2Spine.spineRung_eq_step hwin.step_lt]
    exact ML2Spine.spineStep_le_div_48 hβ0 hη1pos.le
  have hνm : ML2Spine.spineRung β ϖ ε₁ gain dens 0 ≤ ML2Spine.spineRung β ϖ ε₁ gain dens m :=
    hsp.rung_mono (Nat.zero_le m)
  have hνκ : κc ≤ ML2Spine.spineRung β ϖ ε₁ gain dens 0 := hκc
  -- the scales
  obtain ⟨hδτ, hτθ, hθ1⟩ := window_scales hδ0 hδ1.le hwin
  have hτ0 : 0 < Tube.gridScale δ (Tube.ssfGridLen δ) b := lt_of_lt_of_le hδ0 hδτ
  have hθ0 : 0 < Tube.gridScale δ (Tube.ssfGridLen δ) a := lt_of_lt_of_le hτ0 hτθ
  have hτr : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) := hτ0
  have hθr : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) := hθ0
  have hδr : (0 : ℝ) < (δ : ℝ) := hδ0
  have hδr1 : (δ : ℝ) < 1 := hδ1
  set r : ℝ := (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
    / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) with hr_def
  have hr0 : 0 < r := div_pos hθr hτr
  have hr1 : 1 ≤ r := by
    rw [hr_def, le_div_iff₀ hτr, one_mul]
    exact_mod_cast hτθ
  have hθτr : (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
      = (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) * r := by
    rw [hr_def]
    field_simp
  have hinv : ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) = r⁻¹ := by
    rw [hr_def, inv_div]
  have hre : 0 < r ^ ML2Spine.spineDiv ϖ ε₁ := Real.rpow_pos_of_pos hr0 _
  -- `ρ := θ (τ/θ)^e`, the upper end of the window's range
  set ρ : NNReal := Tube.gridScale δ (Tube.ssfGridLen δ) a
    * (Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a)
        ^ ML2Spine.spineDiv ϖ ε₁ with hρ_def
  have hρr : (ρ : ℝ) = (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
      * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ := by
    rw [hρ_def, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_div]
  have hhi : (ρ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
      * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ := le_of_eq hρr
  have hlo : (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
      * ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ ≤ (ρ : ℝ) := by
    change (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) * r ^ ML2Spine.spineDiv ϖ ε₁ ≤ (ρ : ℝ)
    rw [hρr, hinv, Real.inv_rpow hr0.le, ← div_eq_mul_inv, le_div_iff₀ hre, hθτr]
    have hrr : r ^ ML2Spine.spineDiv ϖ ε₁ * r ^ ML2Spine.spineDiv ϖ ε₁ ≤ r := by
      rw [← Real.rpow_add hr0]
      calc r ^ (ML2Spine.spineDiv ϖ ε₁ + ML2Spine.spineDiv ϖ ε₁) ≤ r ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
        _ = r := Real.rpow_one r
    calc (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) * r ^ ML2Spine.spineDiv ϖ ε₁
          * r ^ ML2Spine.spineDiv ϖ ε₁
        = (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          * (r ^ ML2Spine.spineDiv ϖ ε₁ * r ^ ML2Spine.spineDiv ϖ ε₁) := by ring
      _ ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) * r := by gcongr
  -- the window's density lower bound at `ρ`, against the crude ceiling `Δ_max ≤ #`
  have hwm := hwin.le_window_maxDensity ρ hlo hhi j hj
  have hcardD := Kakeya.maxDensity_le_card (𝒰.nodesUnder b a j)
    (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody)
  by_contra hlt
  have hcard1 : ((𝒰.nodesUnder b a j).card : ENNReal) ≤ 1 := by
    exact_mod_cast Nat.lt_succ_iff.mp (Nat.lt_of_not_le hlt)
  have h1 : ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ))
        ^ ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1)) ≤ (δ : ENNReal) ^ (-κc) := by
    calc ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ))
          ^ ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1))
        ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder b a j)
            (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody) := hwm
      _ ≤ Cstar * 1 := by gcongr; exact hcardD.trans hcard1
      _ = Cstar := mul_one _
      _ ≤ (δ : ENNReal) ^ (-κc) := hCstar
  rw [← ML2Reduction.ofReal_rpow_coe hδ0] at h1
  have h2 : ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ))
        ^ ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) ≤ (δ : ℝ) ^ (-κc) :=
    (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hδr.le _)).mp h1
  -- `θ/ρ = r^e`
  have hθρ : (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ)
      = r ^ ML2Spine.spineDiv ϖ ε₁ := by
    rw [hρr, hinv, Real.inv_rpow hr0.le]
    field_simp
  -- `r ≥ δ^{-e}` from the window's scale separation
  have hsep := hwin.scale_sep
  have hrδ : (δ : ℝ) ^ (-(ML2Spine.spineDiv ϖ ε₁)) ≤ r := by
    have hδe : 0 < (δ : ℝ) ^ ML2Spine.spineDiv ϖ ε₁ := Real.rpow_pos_of_pos hδr _
    rw [Real.rpow_neg hδr.le, hr_def, le_div_iff₀ hτr, inv_mul_le_iff₀ hδe]
    exact hsep
  have h3 : (δ : ℝ) ^ (-(ML2Spine.spineDiv ϖ ε₁)
        * (ML2Spine.spineDiv ϖ ε₁ * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1)))
      ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ))
        ^ ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) := by
    rw [hθρ, ← Real.rpow_mul hr0.le, Real.rpow_mul hδr.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hδr.le _) hrδ (by positivity)
  have h4 := h3.trans h2
  rw [Real.rpow_le_rpow_left_iff_of_base_lt_one hδr hδr1] at h4
  -- the spine's first step entry: `e² η_{m+1} ≥ 48 ν/β ≥ 48 ν`
  have h5 : 48 * ML2Spine.spineRung β ϖ ε₁ gain dens 0
      ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2 * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) := by
    have hsq : 0 ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2 := sq_nonneg _
    have : ML2Spine.spineDiv ϖ ε₁ ^ 2 * β * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1)
        ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2 * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) := by
      nlinarith [mul_nonneg hsq hη1pos.le]
    linarith
  nlinarith [h4, h5, hν0, hνκ]

end Control

end Kakeya.ML2Core

end
