/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEccentric
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreFinal
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTrialOutcome
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorExponents

/-!
# The (P) route into `TrialOutcomeAt`

The refined source's eccentric terminal factor (l.4441–4472): alternative (P) of
`lem:ml2-window-refinement` hands an eccentric convex factor, `lem:ml2-eccentric-plank-exit` bounds
the multiplicity, and the mass retention transfers the bound back to the trial family.  In the tree
the exit is existing as `Kakeya.ML2Reduction.exists_threshold_eccentric_atPlankScale` : at the
plank scale `ρ = δ^{1-ε₂}` it takes a uniform-at-scale datum `PS`, **any** plank factoring data
`D : PlankFactoringData ρ pa pb C₀ PS.parent PS.parentTube` of the parents, the eccentricity
`IsEccentric β ε₂ η δ pa pb` of that data, and returns the clean gain
`μ(q) ≤ δ^{10η/ε₂} (#q)^β`.

`exists_trialOutcome_of_eccentric` wires that exit into the descent's interface on the **given**
hierarchy `𝒰` of the trial family `S` (C-D1, `u = S`), concluding **by name** like F7
(`∀ Λ, TrialOutcomeAt β ϖ ε₁ h gain dens 𝒰 Λ lam S T`).  What is here is the pushback:
the exit's gain `10η/ε₂` covers the `(G₂)` target `4ν`, and `Kakeya.ML2Core.sum_shade_le_of_multiplicity_le` turns the multiplicity
bound into the middle disjunct.  What is **named, not assumed** — the inputs of the exit the block
does not carry, each a binder of the per-trial statement:

* **B0** — the trial family is pairwise essentially distinct (`IsEssentiallyDistinct`); the exit's
  own hypothesis, of the species of the tree's conjunct 7;
* the shaded hierarchy over the given `𝒰` (`ShadedUniformTubeSet S T (ssfGridLen δ) Cu` with
  `tubeUniform = 𝒰`) at a constant absorbed by `δ^{-η₀}`, and the fullness at the exit's exponent
  `η₀` (the wiring's `η_in ≤ η₀`);
* **B1** — the plank-scale datum `PS : IsUniformAtScale S (T ·).toTube
  (plankScale δ ε₂) Cpar` with `(max 1 Cpar)² ≤ PS.branchingN`, a plank factoring
  `D : PlankFactoringData (plankScale δ ε₂) pa pb C₀ PS.parent PS.parentTube`, and its eccentricity
  `IsEccentric β ε₂ η δ pa pb`.  The source's (P) trigger is the eccentricity of a **biased** factor
  `W` at a window level, `ethickness ℝ W.carrier 2 ≤ δ^{η'} · ethickness ℝ W.carrier 1`; carrying that factor to plank data
  of the parents at `ρ = δ^{1-ε₂}` with `eccExponent β ε₂ η ≤ η'` is B1, and it is the (P) route's
  hypothesis.  Its exponent side is settled (`eccExponent_le_floorCap`).

`exists_trialOutcome_of_eccentric_squeeze` fixes `η := ε₂ β ε² η_{m+1}/768`, the largest value the
source's cap `η' ≤ ε² τ/64` allows through the trigger, and discharges `hgain` there.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

open Classical in
/-- **F5 — the (P) route's terminal bound, in the trial interface.**  See the module docstring. -/
theorem exists_trialOutcome_of_eccentric
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hKKT : KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β)
    {ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    {ε₂ η : ℝ} (hε₂0 : 0 < ε₂) (hε₂1 : ε₂ ≤ 1) (hη : 0 < η)
    (hgain : 4 * ML2Spine.spineNu β ϖ ε₁ gain dens ≤ 10 * η / ε₂) :
    ∃ η₀ > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (S : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (Cu lam : NNReal)
        (𝒰 : Tube.UniformTubeSet S (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu) (h : ℝ),
        (∀ i ∈ S, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        -- B0: the exit's essential distinctness of the trial family
        (S : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        -- the shaded hierarchy over the given `𝒰`, at a constant the exit absorbs
        Cu ≤ δ ^ (-η₀) →
        (∃ 𝒲 : ShadedTube.ShadedUniformTubeSet S T (Tube.ssfGridLen δ) Cu, 𝒲.tubeUniform = 𝒰) →
        -- fullness at the exit's exponent
        (δ : NNReal) ^ η₀ ≤ ShadedBody.fullness S (fun i ↦ (T i).toShadedBody) →
        -- B1: the plank-scale datum and its eccentric plank factoring
        ∀ (pa pb Cpar C₀ : NNReal), Cpar ≤ δ ^ (-η₀) → C₀ ≤ δ ^ (-η₀) →
        ∀ (PS : Tube.IsUniformAtScale S (fun i ↦ (T i).toTube)
            (ML2Reduction.plankScale δ ε₂) Cpar),
          (max 1 Cpar) ^ 2 ≤ PS.branchingN →
        ∀ (_D : ML2Reduction.PlankFactoringData (ML2Reduction.plankScale δ ε₂) pa pb C₀
            PS.parent PS.parentTube),
        Kakeya.maxDensity S (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-(η / ε₂)) →
        ML2Reduction.IsEccentric β ε₂ η δ pa pb →
        ∀ Λ : ℝ≥0∞, TrialOutcomeAt β ϖ ε₁ h gain dens 𝒰 Λ lam S T := by
  obtain ⟨η₀, hη₀, δ₀, hδ₀, hδ₀1, hexit⟩ :=
    ML2Reduction.exists_threshold_eccentric_atPlankScale hβ0 hβ1 hKKT hKF hε₂0 hε₂1 hη
  refine ⟨η₀, hη₀, ?_⟩
  filter_upwards [Ioc_mem_nhdsGT hδ₀] with δ hδ
  intro ι S T Cu lam 𝒰 h hball hED hCu hSU hfull pa pb Cpar C₀ hCpar hC₀ PS hbr D hmax hecc Λ
  obtain ⟨𝒲, -⟩ := hSU
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ.2.trans hδ₀1
  -- the exit, at the eccentric plank data
  have hmult := hexit S hδ0 T hδ.2 hball hED ⟨Cu, hCu, ⟨𝒲⟩⟩ hfull pa pb Cpar C₀ hCpar hC₀ PS hbr D
    hmax hecc
  -- its gain `10η/ε₂` covers the target `4ν`
  have hmult' : ShadedBody.multiplicity S (fun i ↦ (T i).toShadedBody)
      ≤ (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) * (S.card : ENNReal) ^ β :=
    hmult.trans (mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hgain) le_rfl)
  unfold TrialOutcomeAt
  exact Or.inr (Or.inl (sum_shade_le_of_multiplicity_le T hmult'))

open Classical in
/-- **F5 at the squeeze-maximal exponent.**  With `η := ε₂ β ε² η_{m+1} / 768` — the largest `η`
the source's cap `η' ≤ ε² τ/64` admits through the trigger `eccExponent β ε₂ η ≤ η'`
(`Kakeya.ML2Spine.eccExponent_le_floorCap`) — the exit's gain `10η/ε₂ = 10 β ε² η_{m+1}/768` covers
`4ν` at every rung, by `Kakeya.ML2Spine.ten_spineNu_le_squeeze_gain` (re-anchored `spineStep`). -/
theorem exists_trialOutcome_of_eccentric_squeeze
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hKKT : KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β) (m : ℕ) :
    ∃ η₀ > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (S : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (Cu lam : NNReal)
        (𝒰 : Tube.UniformTubeSet S (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu) (h : ℝ),
        (∀ i ∈ S, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        (S : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        Cu ≤ δ ^ (-η₀) →
        (∃ 𝒲 : ShadedTube.ShadedUniformTubeSet S T (Tube.ssfGridLen δ) Cu, 𝒲.tubeUniform = 𝒰) →
        (δ : NNReal) ^ η₀ ≤ ShadedBody.fullness S (fun i ↦ (T i).toShadedBody) →
        ∀ (pa pb Cpar C₀ : NNReal), Cpar ≤ δ ^ (-η₀) → C₀ ≤ δ ^ (-η₀) →
        ∀ (PS : Tube.IsUniformAtScale S (fun i ↦ (T i).toTube)
            (ML2Reduction.plankScale δ (ML2Spine.spineEps₂ ϖ ε₁)) Cpar),
          (max 1 Cpar) ^ 2 ≤ PS.branchingN →
        ∀ (_D : ML2Reduction.PlankFactoringData
            (ML2Reduction.plankScale δ (ML2Spine.spineEps₂ ϖ ε₁)) pa pb C₀ PS.parent PS.parentTube),
        Kakeya.maxDensity S (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (δ : ENNReal) ^ (-((ML2Spine.spineEps₂ ϖ ε₁ * β * ML2Spine.spineDiv ϖ ε₁ ^ 2
              * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 768) / ML2Spine.spineEps₂ ϖ ε₁)) →
        ML2Reduction.IsEccentric β (ML2Spine.spineEps₂ ϖ ε₁)
          (ML2Spine.spineEps₂ ϖ ε₁ * β * ML2Spine.spineDiv ϖ ε₁ ^ 2
            * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 768) δ pa pb →
        ∀ Λ : ℝ≥0∞, TrialOutcomeAt β ϖ ε₁ h gain dens 𝒰 Λ lam S T := by
  have hε₂ : 0 < ML2Spine.spineEps₂ ϖ ε₁ := ML2Spine.spineEps₂_pos hϖ hε₁
  have hε₂1 : ML2Spine.spineEps₂ ϖ ε₁ ≤ 1 := (ML2Spine.spineEps₂_le_half).trans (by norm_num)
  have hsp := ML2Spine.spineRung_isSpine hβ0 hβ1 hϖ hε₁ hgain hdens
  have he : 0 < ML2Spine.spineDiv ϖ ε₁ := ML2Spine.spineDiv_pos hϖ hε₁
  have hη : 0 < ML2Spine.spineEps₂ ϖ ε₁ * β * ML2Spine.spineDiv ϖ ε₁ ^ 2
      * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 768 := by
    have := hsp.rung_pos (m + 1)
    positivity
  have hg : 4 * ML2Spine.spineNu β ϖ ε₁ gain dens
      ≤ 10 * (ML2Spine.spineEps₂ ϖ ε₁ * β * ML2Spine.spineDiv ϖ ε₁ ^ 2
          * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 768) / ML2Spine.spineEps₂ ϖ ε₁ := by
    have h10 := ML2Spine.ten_spineNu_le_squeeze_gain hβ0 hβ1 hϖ hε₁ hgain hdens m
    have hν0 : 0 ≤ ML2Spine.spineNu β ϖ ε₁ gain dens :=
      (ML2Spine.spineNu_pos hβ0 hϖ hε₁ hgain hdens).le
    have heq : 10 * (ML2Spine.spineEps₂ ϖ ε₁ * β * ML2Spine.spineDiv ϖ ε₁ ^ 2
          * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 768) / ML2Spine.spineEps₂ ϖ ε₁
        = 10 * β * ML2Spine.spineDiv ϖ ε₁ ^ 2
            * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 768 := by
      field_simp
    rw [heq]
    linarith
  exact exists_trialOutcome_of_eccentric hβ0 hβ1 hKKT hKF hε₂ hε₂1 hη hg

/-! ### The (P) route, general in the middle gain -/

open Classical in
/-- **F5, general in the middle gain.**  The exit's gain `10η/ε₂` covers any target `g ≤ 10η/ε₂`,
and the route lands the middle disjunct of `TrialOutcomeAtGain h ε₀ g β …` at **every** `ε₀`; the
first disjunct is not touched by this route.  `g := 4ν` is `exists_trialOutcome_of_eccentric`
(`trialOutcomeAt_eq_gain`), `g := 4ν + defectMargin` is the descent's re-cut `IsTrialAt`
(`exists_trialOutcome_of_eccentric_alpha`). -/
theorem exists_trialOutcome_of_eccentric_gain
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hKKT : KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β)
    {ε₂ η g : ℝ} (hε₂0 : 0 < ε₂) (hε₂1 : ε₂ ≤ 1) (hη : 0 < η)
    (hgain : g ≤ 10 * η / ε₂) :
    ∃ η₀ > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (S : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (Cu lam : NNReal)
        (𝒰 : Tube.UniformTubeSet S (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu) (h : ℝ),
        (∀ i ∈ S, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        (S : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        Cu ≤ δ ^ (-η₀) →
        (∃ 𝒲 : ShadedTube.ShadedUniformTubeSet S T (Tube.ssfGridLen δ) Cu, 𝒲.tubeUniform = 𝒰) →
        (δ : NNReal) ^ η₀ ≤ ShadedBody.fullness S (fun i ↦ (T i).toShadedBody) →
        ∀ (pa pb Cpar C₀ : NNReal), Cpar ≤ δ ^ (-η₀) → C₀ ≤ δ ^ (-η₀) →
        ∀ (PS : Tube.IsUniformAtScale S (fun i ↦ (T i).toTube)
            (ML2Reduction.plankScale δ ε₂) Cpar),
          (max 1 Cpar) ^ 2 ≤ PS.branchingN →
        ∀ (_D : ML2Reduction.PlankFactoringData (ML2Reduction.plankScale δ ε₂) pa pb C₀
            PS.parent PS.parentTube),
        Kakeya.maxDensity S (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-(η / ε₂)) →
        ML2Reduction.IsEccentric β ε₂ η δ pa pb →
        ∀ (ε₀ : ℝ) (Λ : ℝ≥0∞), TrialOutcomeAtGain h ε₀ g β 𝒰 Λ lam S T := by
  obtain ⟨η₀, hη₀, δ₀, hδ₀, hδ₀1, hexit⟩ :=
    ML2Reduction.exists_threshold_eccentric_atPlankScale hβ0 hβ1 hKKT hKF hε₂0 hε₂1 hη
  refine ⟨η₀, hη₀, ?_⟩
  filter_upwards [Ioc_mem_nhdsGT hδ₀] with δ hδ
  intro ι S T Cu lam 𝒰 h hball hED hCu hSU hfull pa pb Cpar C₀ hCpar hC₀ PS hbr D hmax hecc ε₀ Λ
  obtain ⟨𝒲, -⟩ := hSU
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ.2.trans hδ₀1
  have hmult := hexit S hδ0 T hδ.2 hball hED ⟨Cu, hCu, ⟨𝒲⟩⟩ hfull pa pb Cpar C₀ hCpar hC₀ PS hbr D
    hmax hecc
  have hmult' : ShadedBody.multiplicity S (fun i ↦ (T i).toShadedBody)
      ≤ (δ : ENNReal) ^ g * (S.card : ENNReal) ^ β :=
    hmult.trans (mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hgain) le_rfl)
  unfold TrialOutcomeAtGain
  exact Or.inr (Or.inl (sum_shade_le_of_multiplicity_le T hmult'))

open Classical in
/-- **F5 at the descent's re-cut exponents** (`IsTrialAt` concludes
`TrialOutcomeAtGain h (β/2 − α) (4ν + α)`, `α := defectMargin`).  At the squeeze-maximal
`η := ε₂ β e² η_{m+1}/768` the exit's gain `10η/ε₂ = 10βe²η_{m+1}/768 ≥ 10ν ≥ 5ν = 4ν + α`
(`ten_spineNu_le_squeeze_gain`, `defectMargin_eq`): the (P) route pays the extra `ν` at every
rung. -/
theorem exists_trialOutcome_of_eccentric_alpha
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hKKT : KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β) (m : ℕ) :
    ∃ η₀ > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (S : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (Cu lam : NNReal)
        (𝒰 : Tube.UniformTubeSet S (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu) (h : ℝ),
        (∀ i ∈ S, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        (S : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        Cu ≤ δ ^ (-η₀) →
        (∃ 𝒲 : ShadedTube.ShadedUniformTubeSet S T (Tube.ssfGridLen δ) Cu, 𝒲.tubeUniform = 𝒰) →
        (δ : NNReal) ^ η₀ ≤ ShadedBody.fullness S (fun i ↦ (T i).toShadedBody) →
        ∀ (pa pb Cpar C₀ : NNReal), Cpar ≤ δ ^ (-η₀) → C₀ ≤ δ ^ (-η₀) →
        ∀ (PS : Tube.IsUniformAtScale S (fun i ↦ (T i).toTube)
            (ML2Reduction.plankScale δ (ML2Spine.spineEps₂ ϖ ε₁)) Cpar),
          (max 1 Cpar) ^ 2 ≤ PS.branchingN →
        ∀ (_D : ML2Reduction.PlankFactoringData
            (ML2Reduction.plankScale δ (ML2Spine.spineEps₂ ϖ ε₁)) pa pb C₀
            PS.parent PS.parentTube),
        Kakeya.maxDensity S (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (δ : ENNReal) ^ (-((ML2Spine.spineEps₂ ϖ ε₁ * β * ML2Spine.spineDiv ϖ ε₁ ^ 2
              * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 768) / ML2Spine.spineEps₂ ϖ ε₁)) →
        ML2Reduction.IsEccentric β (ML2Spine.spineEps₂ ϖ ε₁)
          (ML2Spine.spineEps₂ ϖ ε₁ * β * ML2Spine.spineDiv ϖ ε₁ ^ 2
            * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 768) δ pa pb →
        ∀ Λ : ℝ≥0∞, TrialOutcomeAtGain h (β / 2 - defectMargin β ϖ ε₁ gain dens)
          (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β 𝒰 Λ lam S T
          := by
  have hε₂ : 0 < ML2Spine.spineEps₂ ϖ ε₁ := ML2Spine.spineEps₂_pos hϖ hε₁
  have hε₂1 : ML2Spine.spineEps₂ ϖ ε₁ ≤ 1 := (ML2Spine.spineEps₂_le_half).trans (by norm_num)
  have hsp := ML2Spine.spineRung_isSpine hβ0 hβ1 hϖ hε₁ hgain hdens
  have he : 0 < ML2Spine.spineDiv ϖ ε₁ := ML2Spine.spineDiv_pos hϖ hε₁
  have hη : 0 < ML2Spine.spineEps₂ ϖ ε₁ * β * ML2Spine.spineDiv ϖ ε₁ ^ 2
      * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 768 := by
    have := hsp.rung_pos (m + 1)
    positivity
  have hg : 4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens
      ≤ 10 * (ML2Spine.spineEps₂ ϖ ε₁ * β * ML2Spine.spineDiv ϖ ε₁ ^ 2
          * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 768) / ML2Spine.spineEps₂ ϖ ε₁ := by
    have h10 := ML2Spine.ten_spineNu_le_squeeze_gain hβ0 hβ1 hϖ hε₁ hgain hdens m
    have hν0 : 0 ≤ ML2Spine.spineNu β ϖ ε₁ gain dens :=
      (ML2Spine.spineNu_pos hβ0 hϖ hε₁ hgain hdens).le
    have heq : 10 * (ML2Spine.spineEps₂ ϖ ε₁ * β * ML2Spine.spineDiv ϖ ε₁ ^ 2
          * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 768) / ML2Spine.spineEps₂ ϖ ε₁
        = 10 * β * ML2Spine.spineDiv ϖ ε₁ ^ 2
            * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 768 := by
      field_simp
    rw [heq, defectMargin_eq]
    linarith
  obtain ⟨η₀, hη₀, hev⟩ :=
    exists_trialOutcome_of_eccentric_gain hβ0 hβ1 hKKT hKF hε₂ hε₂1 hη hg
  refine ⟨η₀, hη₀, hev.mono ?_⟩
  intro δ hδ ι S T Cu lam 𝒰 h hball hED hCu hSU hfull pa pb Cpar C₀ hCpar hC₀ PS hbr D hmax hecc Λ
  exact hδ S T Cu lam 𝒰 h hball hED hCu hSU hfull pa pb Cpar C₀ hCpar hC₀ PS hbr D hmax hecc _ Λ

end Kakeya.ML2Core

end
