/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineHfacWire

/-!
# A producer for `hfac`: the three factors, and what is left of them

 measured that the post-drop factor hypothesis of the
`(F)` terminal engine — `Kakeya.ML2Core.HfacPostDrop`, equivalently
`Kakeya.ML2Core.HfacLevels` at `Cu₀ = max C 4` — had **no producer anywhere in the tree**: the
existential `∃ (tτ' tθ' : Finset ι) …` occurred eleven times, every one of them a binder.  This
file builds the producer down to the single factor that is genuinely open.

## The split

`Kakeya.ML2Core.exists_spineTwoScale_ofChain_translated` already delivers the retained node sets
`tτ', tθ'`, the three shadings `Yτ', Yθ, Y'`, their nonemptiness and the **product bound** — the
whole of `hfac`'s conclusion except its three factor estimates.  So `hfac` is exactly

* `Kakeya.ML2Core.FineRow` — the fine factor at the retained fibre.  **Discharged** here from the
  Katz--Tao estimate (`Kakeya.ML2Core.exists_threshold_fineRow`).
* `Kakeya.ML2Core.CoarseRow` — the coarse factor on the retained parents.  **Discharged** here
  from the Katz--Tao estimate *and* `Kakeya.ML2Core.CoarseStructRow`
  (`Kakeya.ML2Core.exists_threshold_coarseRow`).
* `Kakeya.ML2Core.MiddleRow` — the middle factor at the window.  **Open**; it is the GWZ gain and
  the only place where `Kakeya.VeryNotSticky.CentredHandBack`, `CountTransport`,
  `ML2Reduction.Lemma91At` and the tightened `huni` enter.

`Kakeya.ML2Core.hfacLevels_of_rows` is the assembly, and
`Kakeya.ML2Core.geometricCoreAt_of_middleRow` chains it into
`Kakeya.ML2Core.geometricCoreAt_of_hfac_witness_payload`.

## The two thresholds on `η_in`

Both discharged factors are quantified *before* `η_in`: the Katz--Tao estimate returns its own
exponent, and the fullness input of each factor is met only for `η_in` below a quarter of it.
That is why the theorems below conclude `∃ η0 > 0, ∀ η_in ≤ η0, …` and why
`Kakeya.ML2Core.geometricCoreAt_of_middleRow` asks its supplier for the rows **at arbitrarily
small `η_in`**.  The absorption of the two-scale losses into `δ^(-κ)` is
`Kakeya.ML2Core.eventually_spineScaleLoss_le`.

## What `CoarseStructRow` is, and why it is separate

`Kakeya.ML2Core.exists_coarse_factor_at_window` needs the coarse scale below a fixed threshold,
which `Kakeya.ML2Core.eventually_gridScale_le` gives **only for `1 ≤ a`**
(`Tube.gridScale δ M 0 = 1` on the nose), and it needs the retained parents inside the unit ball,
which `hfac` supplies for `t₀` and only when `a ≠ 0`.  Neither `1 ≤ a` nor
`tθ' ⊆ coarseNode '' tτ'` is returned by the two-scale split or forced by
`ML2Reduction.IsKatzTaoDividingWindow` (whose only order constraint is `a < b`), so they are
named and left as one row rather than hidden in a proof.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

/-- **The two-scale loss is subpolynomial**: below a threshold in `δ`, every
`Kakeya.ML2Reduction.spineScaleLoss n N σ` with `N ≤ δ^(-4)` and `δ ≤ σ ≤ 1` is at most
`δ^(-κ)`. -/
theorem eventually_spineScaleLoss_le (n : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ N : ℕ, 0 < N → (N : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      ∀ σ : NNReal, δ ≤ σ → σ ≤ 1 →
        ML2Reduction.spineScaleLoss n N σ ≤ δ ^ (-κ) := by
  set ε : ℝ := κ / 6 with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨Cε, hCε⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox n ε hε
  obtain ⟨δ₀, hδ₀0, hδ₀⟩ :=
    ML2Reduction.exists_threshold_const_le_rpow_neg (C := max 1 Cε) (le_max_left _ _) hε
  filter_upwards [Ioo_mem_nhdsGT (show (0:NNReal) < min 1 δ₀ from lt_min zero_lt_one hδ₀0)]
    with δ hδ N hN hNcard σ hδσ hσ1
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ ≤ 1 := le_of_lt (lt_of_lt_of_le hδ.2 (min_le_left _ _))
  have hδle : δ ≤ δ₀ := le_of_lt (lt_of_lt_of_le hδ.2 (min_le_right _ _))
  have hσ0 : 0 < σ := lt_of_lt_of_le hδ0 hδσ
  have hbase := hCε N hN σ hσ0 hσ1 1 le_rfl
  rw [one_pow, mul_one] at hbase
  have hσε : σ ^ (-ε) ≤ δ ^ (-ε) := by
    rw [NNReal.rpow_neg, NNReal.rpow_neg]
    exact inv_anti₀ (NNReal.rpow_pos hδ0) (NNReal.rpow_le_rpow hδσ hε.le)
  have hNε : (N : NNReal) ^ ε ≤ δ ^ (-(4 : ℝ) * ε) := by
    calc (N : NNReal) ^ ε ≤ (δ ^ (-(4 : ℝ))) ^ ε := NNReal.rpow_le_rpow hNcard hε.le
      _ = δ ^ (-(4 : ℝ) * ε) := by rw [← NNReal.rpow_mul]
  have hC : Cε ≤ δ ^ (-ε) := le_trans (le_max_right 1 Cε) (hδ₀ δ hδ0 hδle)
  have hprod : Cε * σ ^ (-ε) * (N : NNReal) ^ ε ≤ δ ^ (-κ) := by
    calc Cε * σ ^ (-ε) * (N : NNReal) ^ ε
        ≤ δ ^ (-ε) * δ ^ (-ε) * δ ^ (-(4 : ℝ) * ε) := by
          gcongr
      _ = δ ^ (-ε + -ε + -(4 : ℝ) * ε) := by
          rw [NNReal.rpow_add hδ0.ne' (-ε + -ε) (-(4 : ℝ) * ε),
            NNReal.rpow_add hδ0.ne' (-ε) (-ε)]
      _ = δ ^ (-κ) := by
          congr 1
          rw [hεdef]; ring
  exact le_trans hbase hprod




open Classical in
/-- **The fine factor at the retained fibre**, as a row over the two-scale split. -/
def FineRow.{u} (β ϖ ε₁ ηin εf κc : ℝ) (gain dens : ℝ → ℝ) (C : NNReal) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (Cu lam : NNReal)
      (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
      (Cstar : ENNReal) (a b m : ℕ),
      ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
        (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
    ∀ (v : EuclideanSpace ℝ (Fin 3)) (t₀ t₁ tτ' tθ' : Finset ι)
      (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
      (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
      (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
      tτ' ⊆ t₁ → tθ' ⊆ 𝒰.cover.indexSet a → tτ'.Nonempty → tθ'.Nonempty →
      (∀ j, (Yτ' j).toTube = (𝒰.cover.tube b j).translate v) →
      (∀ k, (Yθ k).toTube = (𝒰.cover.tube a k).translate v) →
      (∀ i, (Y' i).toTube = ((T i).translate v).toTube) →
      (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
      ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
      (δ : NNReal) ^ ηin / 2 ≤ lam →
      (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      Cstar ≤ (δ : ENNReal) ^ (-κc) →
      Cu ≤ max C 4 →
      0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
      ShadedBody.IsCRefinement
        ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
          𝒰.cover.assign b i ∈ tτ'} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
        ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
        (fun i ↦ ((T i).translate v).toShadedBody)
        (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
          ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ)⁻¹ →
      (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
              ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) b))⁻¹ *
          ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
            (fun i ↦ (T i).toShadedBody)
        ≤ ShadedBody.fullness tθ' (fun k ↦ (Yθ k).toShadedBody) →
      (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
      (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
      (a ≠ 0 → ∀ k ∈ t₀, ((𝒰.cover.tube a k).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
      Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
      Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
      ∃ jτ ∈ tτ',
        ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
          ≤ (δ : ENNReal) ^ (-(εf)) * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
              𝒰.cover.assign b i = jτ} : Finset ι)).card : ENNReal) ^ β

open Classical in
/-- **The middle factor at the window** — the open row: the GWZ gain on the coarse fibre of
the retained fine nodes.  Everything else in `hfac` is discharged. -/
def MiddleRow.{u} (β ϖ ε₁ ηin κc : ℝ) (gm gain dens : ℝ → ℝ) (C : NNReal) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (Cu lam : NNReal)
      (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
      (Cstar : ENNReal) (a b m : ℕ),
      ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
        (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
    ∀ (v : EuclideanSpace ℝ (Fin 3)) (t₀ t₁ tτ' tθ' : Finset ι)
      (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
      (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
      (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
      tτ' ⊆ t₁ → tθ' ⊆ 𝒰.cover.indexSet a → tτ'.Nonempty → tθ'.Nonempty →
      (∀ j, (Yτ' j).toTube = (𝒰.cover.tube b j).translate v) →
      (∀ k, (Yθ k).toTube = (𝒰.cover.tube a k).translate v) →
      (∀ i, (Y' i).toTube = ((T i).translate v).toTube) →
      (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
      ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
      (δ : NNReal) ^ ηin / 2 ≤ lam →
      (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      Cstar ≤ (δ : ENNReal) ^ (-κc) →
      Cu ≤ max C 4 →
      0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
      ShadedBody.IsCRefinement
        ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
          𝒰.cover.assign b i ∈ tτ'} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
        ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
        (fun i ↦ ((T i).translate v).toShadedBody)
        (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
          ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ)⁻¹ →
      (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
              ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) b))⁻¹ *
          ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
            (fun i ↦ (T i).toShadedBody)
        ≤ ShadedBody.fullness tθ' (fun k ↦ (Yθ k).toShadedBody) →
      (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
      (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
      (a ≠ 0 → ∀ k ∈ t₀, ((𝒰.cover.tube a k).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
      Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
      Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
      ∃ jθ ∈ tθ',
        ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} :
            Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
          ≤ (δ : ENNReal) ^ (gm (ML2Spine.spineRung β ϖ ε₁ gain dens m))
            * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset
                ι)).card : ENNReal) ^ β

open Classical in
/-- **The coarse factor on the retained parents**, as a row over the two-scale split. -/
def CoarseRow.{u} (β ϖ ε₁ ηin εc κc : ℝ) (gain dens : ℝ → ℝ) (C : NNReal) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (Cu lam : NNReal)
      (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
      (Cstar : ENNReal) (a b m : ℕ),
      ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
        (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
    ∀ (v : EuclideanSpace ℝ (Fin 3)) (t₀ t₁ tτ' tθ' : Finset ι)
      (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
      (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
      (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
      tτ' ⊆ t₁ → tθ' ⊆ 𝒰.cover.indexSet a → tτ'.Nonempty → tθ'.Nonempty →
      (∀ j, (Yτ' j).toTube = (𝒰.cover.tube b j).translate v) →
      (∀ k, (Yθ k).toTube = (𝒰.cover.tube a k).translate v) →
      (∀ i, (Y' i).toTube = ((T i).translate v).toTube) →
      (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
      ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
      (δ : NNReal) ^ ηin / 2 ≤ lam →
      (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      Cstar ≤ (δ : ENNReal) ^ (-κc) →
      Cu ≤ max C 4 →
      0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
      ShadedBody.IsCRefinement
        ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
          𝒰.cover.assign b i ∈ tτ'} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
        ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
        (fun i ↦ ((T i).translate v).toShadedBody)
        (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
          ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ)⁻¹ →
      (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
              ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) b))⁻¹ *
          ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
            (fun i ↦ (T i).toShadedBody)
        ≤ ShadedBody.fullness tθ' (fun k ↦ (Yθ k).toShadedBody) →
      (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
      (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
      (a ≠ 0 → ∀ k ∈ t₀, ((𝒰.cover.tube a k).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
      Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
      Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
      ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
        ≤ (δ : ENNReal) ^ (-(εc + ML2Spine.spineRung β ϖ ε₁ gain dens m))
          * ((tθ'.card : ℕ) : ENNReal) ^ β

open Classical in
/-- **The two structural facts the two-scale split does not return**: the window's coarse level
is positive, and the retained parents are parents of retained fine nodes. -/
def CoarseStructRow.{u} (β ϖ ε₁ ηin κc : ℝ) (gain dens : ℝ → ℝ) (C : NNReal) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (Cu lam : NNReal)
      (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
      (Cstar : ENNReal) (a b m : ℕ),
      ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
        (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
    ∀ (v : EuclideanSpace ℝ (Fin 3)) (t₀ t₁ tτ' tθ' : Finset ι)
      (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
      (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
      (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
      tτ' ⊆ t₁ → tθ' ⊆ 𝒰.cover.indexSet a → tτ'.Nonempty → tθ'.Nonempty →
      (∀ j, (Yτ' j).toTube = (𝒰.cover.tube b j).translate v) →
      (∀ k, (Yθ k).toTube = (𝒰.cover.tube a k).translate v) →
      (∀ i, (Y' i).toTube = ((T i).translate v).toTube) →
      (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
      ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
      (δ : NNReal) ^ ηin / 2 ≤ lam →
      (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      Cstar ≤ (δ : ENNReal) ^ (-κc) →
      Cu ≤ max C 4 →
      0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
      ShadedBody.IsCRefinement
        ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
          𝒰.cover.assign b i ∈ tτ'} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
        ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
        (fun i ↦ ((T i).translate v).toShadedBody)
        (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
          ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ)⁻¹ →
      (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
              ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) b))⁻¹ *
          ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
            (fun i ↦ (T i).toShadedBody)
        ≤ ShadedBody.fullness tθ' (fun k ↦ (Yθ k).toShadedBody) →
      (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
      (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
      (a ≠ 0 → ∀ k ∈ t₀, ((𝒰.cover.tube a k).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
      Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
      Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
      1 ≤ a ∧ tθ' ⊆ Finset.image (ML2Reduction.coarseNode 𝒰.cover.toChain a b) tτ'

open Classical in
/-- **The MINIMAL structural row**: the window's coarse level is positive, and the retained
parents lie in the unit ball after the seam's translation.  This is all
`Kakeya.ML2Core.exists_coarse_factor_at_window` actually needs; `Kakeya.ML2Core.CoarseStructRow`
implies it (`Kakeya.ML2Core.coarseBallRow_of_coarseStructRow`) using `hfac`'s own `t₀` rows. -/
def CoarseBallRow.{u} (β ϖ ε₁ ηin κc : ℝ) (gain dens : ℝ → ℝ) (C : NNReal) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (Cu lam : NNReal)
      (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
      (Cstar : ENNReal) (a b m : ℕ),
      ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
        (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
    ∀ (v : EuclideanSpace ℝ (Fin 3)) (t₀ t₁ tτ' tθ' : Finset ι)
      (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
      (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
      (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
      tτ' ⊆ t₁ → tθ' ⊆ 𝒰.cover.indexSet a → tτ'.Nonempty → tθ'.Nonempty →
      (∀ j, (Yτ' j).toTube = (𝒰.cover.tube b j).translate v) →
      (∀ k, (Yθ k).toTube = (𝒰.cover.tube a k).translate v) →
      (∀ i, (Y' i).toTube = ((T i).translate v).toTube) →
      (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
      ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
      (δ : NNReal) ^ ηin / 2 ≤ lam →
      (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      Cstar ≤ (δ : ENNReal) ^ (-κc) →
      Cu ≤ max C 4 →
      0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
      ShadedBody.IsCRefinement
        ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
          𝒰.cover.assign b i ∈ tτ'} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
        ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
        (fun i ↦ ((T i).translate v).toShadedBody)
        (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
          ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ)⁻¹ →
      (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
              ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) b))⁻¹ *
          ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
            (fun i ↦ (T i).toShadedBody)
        ≤ ShadedBody.fullness tθ' (fun k ↦ (Yθ k).toShadedBody) →
      (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
      (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
      (a ≠ 0 → ∀ k ∈ t₀, ((𝒰.cover.tube a k).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
      Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
      Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
      1 ≤ a ∧ ∀ k ∈ tθ', ((𝒰.cover.tube a k).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1

open Classical in
/-- **The image form implies the minimal form.**  `hfac` supplies the unit-ball containment for
`t₀` and the fact that every level-`b` retained node has its coarse parent in `t₀`, both under
`a ≠ 0`; `Kakeya.ML2Core.CoarseStructRow`'s second conjunct is what carries `tθ'` into that
image. -/
theorem coarseBallRow_of_coarseStructRow {β ϖ ε₁ ηin κc : ℝ} {gain dens : ℝ → ℝ} {C : NNReal}
    (h : CoarseStructRow.{u} β ϖ ε₁ ηin κc gain dens C) :
    CoarseBallRow.{u} β ϖ ε₁ ηin κc gain dens C := by
  filter_upwards [h] with δ hδ
  intro ι u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ tτ' tθ' Yτ' Yθ Y' ht₁ htτ' htθ' hτne hθne
    hYτ' hYθ hY'tube hballt hballs hmax hdense hlamlow hcardu hCstar hCu hmass href1 hfull2
    h4 h5 h6 hδb hba ha1
  obtain ⟨ha1le, himg⟩ := hδ u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ tτ' tθ' Yτ' Yθ Y' ht₁ htτ'
    htθ' hτne hθne hYτ' hYθ hY'tube hballt hballs hmax hdense hlamlow hcardu hCstar hCu hmass
    href1 hfull2 h4 h5 h6 hδb hba ha1
  have hane : a ≠ 0 := by omega
  refine ⟨ha1le, fun k hk => ?_⟩
  obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp (himg hk)
  exact h6 hane k (hjk ▸ h5 hane j (htτ' hj))

open Classical in
/-- **The fine row, from the Katz--Tao estimate.**  The threshold `η0 = ηfine/4` is where the
fine factor's own fullness input `δ^ηfine ≤ C⁻¹ · λ(s₁)` meets the site's dense shading
`δ^{η_in}/2 ≤ lam`, after the two-scale loss is absorbed. -/
theorem exists_threshold_fineRow {β εf : ℝ} (hβ0 : 0 ≤ β)
    (hKT : Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) (hεf : 0 < εf) :
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ {ϖ ε₁ ηin κc : ℝ} {gain dens : ℝ → ℝ} {C : NNReal},
      0 < ηin → ηin ≤ η0 → FineRow.{u} β ϖ ε₁ ηin εf κc gain dens C := by
  obtain ⟨ηfine, hηfine, hfine⟩ :=
    exists_fine_factor_at_window.{u} (E := EuclideanSpace ℝ (Fin 3)) hβ0 hKT hεf
  obtain ⟨d2, hd20, hd2⟩ :=
    ML2Reduction.exists_threshold_const_le_rpow_neg (C := 2) (by norm_num)
      (κ := ηfine / 4) (by positivity)
  refine ⟨ηfine / 4, by positivity, ?_⟩
  intro ϖ ε₁ ηin κc gain dens C hηin0 hηin
  filter_upwards [hfine,
    eventually_spineScaleLoss_le (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
      (show (0:ℝ) < ηfine / 2 by positivity),
    Ioo_mem_nhdsGT (show (0:NNReal) < min 1 d2 from lt_min zero_lt_one hd20)]
    with δ hfδ hloss hδ
  have hδ0 : (0:NNReal) < δ := hδ.1
  have hδ1 : δ ≤ 1 := le_of_lt (lt_of_lt_of_le hδ.2 (min_le_left _ _))
  have hδd2 : δ ≤ d2 := le_of_lt (lt_of_lt_of_le hδ.2 (min_le_right _ _))
  have h2 : (2:NNReal) ≤ δ ^ (-(ηfine / 4)) := hd2 δ hδ0 hδd2
  intro ι u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ tτ' tθ' Yτ' Yθ Y' ht₁ htτ' htθ' hτne hθne
    hYτ' hYθ hY'tube hballt hballs hmax hdense hlamlow hcardu hCstar hCu hmass href1 hfull2
    h4 h5 h6 hδb hba ha1
  set s₁ : Finset ι := {i ∈ u | 𝒰.cover.assign b i ∈ t₁} with hs₁
  have hs₁u : s₁ ⊆ u := Finset.filter_subset _ _
  have hs₁ne : s₁.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hmass
    simp at hmass
  -- the fine factor's density input
  have hmax' : Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody)
      ≤ (δ : ENNReal) ^ (-ηfine) := by
    refine hmax.trans (ENNReal.rpow_le_rpow_of_exponent_ge ?_ (by linarith))
    exact_mod_cast hδ1
  -- the fine factor's fullness input
  have hcards₁ : (s₁.card : NNReal) ≤ δ ^ (-(4:ℝ)) :=
    le_trans (by exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hs₁u)) hcardu
  have hL := hloss s₁.card (Finset.card_pos.mpr hs₁ne) hcards₁ δ le_rfl hδ1
  have hLpos : (0:NNReal) < ML2Reduction.spineScaleLoss
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) s₁.card δ :=
    lt_of_lt_of_le zero_lt_one (ML2Reduction.one_le_spineScaleLoss _ _ _)
  have hfullS : (δ : NNReal) ^ ηin / 2 ≤ ShadedBody.fullness s₁ (fun i ↦ (T i).toShadedBody) := by
    have h := (hdense.subset hs₁u).le_fullness_tube hδ0 hs₁ne
    rw [← ShadedBody.coe_fullness, ENNReal.coe_le_coe] at h
    exact hlamlow.trans h
  have hkey : ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
        s₁.card δ * (δ : NNReal) ^ ηfine
      ≤ ShadedBody.fullness s₁ (fun i ↦ (T i).toShadedBody) := by
    refine le_trans ?_ hfullS
    have hstep : ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
          s₁.card δ * (δ : NNReal) ^ ηfine ≤ δ ^ (-(ηfine / 2)) * δ ^ ηfine := by
      gcongr
    refine hstep.trans ?_
    rw [← NNReal.rpow_add hδ0.ne']
    have harith : -(ηfine / 2) + ηfine = ηfine / 2 := by ring
    rw [harith]
    rw [le_div_iff₀ (by norm_num : (0:NNReal) < 2), mul_comm]
    calc (2:NNReal) * δ ^ (ηfine / 2) ≤ δ ^ (-(ηfine / 4)) * δ ^ (ηfine / 2) := by gcongr
      _ = δ ^ (ηfine / 4) := by
          rw [← NNReal.rpow_add hδ0.ne']
          congr 1
          ring
      _ ≤ δ ^ ηin := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hηin
  have hfull' : (δ : NNReal) ^ ηfine
      ≤ (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
          s₁.card δ)⁻¹ * ShadedBody.fullness s₁ (fun i ↦ (T i).toShadedBody) := by
    rw [le_inv_mul_iff₀ hLpos]
    exact hkey
  exact hfδ (s := u) (s₁ := s₁) (t := tτ') (V := T) (Y := Y') (v := v)
    (pτ := 𝒰.cover.assign b) hs₁u hY'tube hballs href1 hτne hmax' hfull'


open Classical in
/-- **The coarse row, from the Katz--Tao estimate and the structural row.**

`Kakeya.ML2Core.exists_coarse_factor_at_window` is applied at `ε := εc - κc`, which is why
`κc < εc` appears: the existing coarse factor pays `κ + η_m` on top of its own `ε`, and `hfac`'s
row pays only `εc + η_m`.  The two structural facts the two-scale split does not return —
`1 ≤ a` and `tθ' ⊆ coarseNode '' tτ'` — are exactly `Kakeya.ML2Core.CoarseStructRow`. -/
theorem exists_threshold_coarseRow_of_ballRow {β ϖ ε₁ εc κc : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hKT : Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hκc : 0 ≤ κc) (hκcεc : κc < εc) :
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ {ηin : ℝ} {C : NNReal},
      0 < ηin → ηin ≤ η0 →
      CoarseBallRow.{u} β ϖ ε₁ ηin κc gain dens C →
      CoarseRow.{u} β ϖ ε₁ ηin εc κc gain dens C := by
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  obtain ⟨ηc, hηc, θ₀, hθ₀0, hθ₀1, hcoarse⟩ :=
    exists_coarse_factor_at_window.{u} (E := EuclideanSpace ℝ (Fin 3)) hβ0.le hβ1 hKT
      (show (0:ℝ) < εc - κc by linarith)
  obtain ⟨d2, hd20, hd2⟩ :=
    ML2Reduction.exists_threshold_const_le_rpow_neg (C := 2) (by norm_num)
      (κ := ηc / 4) (by positivity)
  refine ⟨ηc / 4, by positivity, ?_⟩
  intro ηin C hηin0 hηin hstruct
  filter_upwards [hstruct,
    eventually_spineScaleLoss_le (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
      (show (0:ℝ) < ηc / 4 by positivity),
    eventually_gridScale_le (ρ₀ := θ₀) hθ₀0,
    Ioo_mem_nhdsGT (show (0:NNReal) < min 1 d2 from lt_min zero_lt_one hd20)]
    with δ hst hloss hgs hδ
  have hδ0 : (0:NNReal) < δ := hδ.1
  have hδ1 : δ ≤ 1 := le_of_lt (lt_of_lt_of_le hδ.2 (min_le_left _ _))
  have hδd2 : δ ≤ d2 := le_of_lt (lt_of_lt_of_le hδ.2 (min_le_right _ _))
  have h2 : (2:NNReal) ≤ δ ^ (-(ηc / 4)) := hd2 δ hδ0 hδd2
  intro ι u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ tτ' tθ' Yτ' Yθ Y' ht₁ htτ' htθ' hτne hθne
    hYτ' hYθ hY'tube hballt hballs hmax hdense hlamlow hcardu hCstar hCu hmass href1 hfull2
    h4 h5 h6 hδb hba ha1
  obtain ⟨ha1le, hball0⟩ := hst u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ tτ' tθ' Yτ' Yθ Y' ht₁ htτ'
    htθ' hτne hθne hYτ' hYθ hY'tube hballt hballs hmax hdense hlamlow hcardu hCstar hCu hmass
    href1 hfull2 h4 h5 h6 hδb hba ha1
  set s₁ : Finset ι := {i ∈ u | 𝒰.cover.assign b i ∈ t₁} with hs₁
  have hs₁u : s₁ ⊆ u := Finset.filter_subset _ _
  have hs₁ne : s₁.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hmass
    simp at hmass
  have hcardτu : tτ'.card ≤ u.card :=
    le_trans (Finset.card_le_card (htτ'.trans ht₁))
      (card_activeNodes_le_card 𝒰.cover.toChain b)
  -- the ball row on the coarse nodes
  have hballθ : ∀ k ∈ tθ', (Yθ k).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro k hk
    have hcar : (Yθ k).carrier = ((𝒰.cover.tube a k).translate v).carrier := by
      rw [← hYθ k]
    rw [hcar]
    exact hball0 k hk
  -- the coarse scale is below the Katz--Tao threshold
  have haM : a ≤ Tube.ssfGridLen δ :=
    le_trans (le_of_lt hwin.coarse_lt_fine) hwin.fine_le_gridLen
  have hθle : Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ θ₀ := hgs a ha1le haM
  -- the fullness input
  have hcards₁ : (s₁.card : NNReal) ≤ δ ^ (-(4:ℝ)) :=
    le_trans (by exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hs₁u)) hcardu
  have hcardτ : (tτ'.card : NNReal) ≤ δ ^ (-(4:ℝ)) :=
    le_trans (by exact_mod_cast Nat.cast_le.mpr hcardτu) hcardu
  have hL1 := hloss s₁.card (Finset.card_pos.mpr hs₁ne) hcards₁ δ le_rfl hδ1
  have hL2 := hloss tτ'.card (Finset.card_pos.mpr hτne) hcardτ
    (Tube.gridScale δ (Tube.ssfGridLen δ) b) hδb (le_trans hba ha1)
  have hLpos : ∀ (N : ℕ) (σ : NNReal), (0:NNReal) < ML2Reduction.spineScaleLoss
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) N σ := fun N σ =>
    lt_of_lt_of_le zero_lt_one (ML2Reduction.one_le_spineScaleLoss _ _ _)
  have hfullS : (δ : NNReal) ^ ηin / 2 ≤ ShadedBody.fullness s₁ (fun i ↦ (T i).toShadedBody) := by
    have h := (hdense.subset hs₁u).le_fullness_tube hδ0 hs₁ne
    rw [← ShadedBody.coe_fullness, ENNReal.coe_le_coe] at h
    exact hlamlow.trans h
  have hfullθ : (δ : NNReal) ^ ηc ≤ ShadedBody.fullness tθ' (fun k ↦ (Yθ k).toShadedBody) := by
    refine le_trans ?_ hfull2
    rw [le_inv_mul_iff₀ (mul_pos (hLpos _ _) (hLpos _ _))]
    refine le_trans ?_ hfullS
    have hstep : ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
            s₁.card δ *
          ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
            (Tube.gridScale δ (Tube.ssfGridLen δ) b) * (δ : NNReal) ^ ηc
        ≤ δ ^ (-(ηc / 4)) * δ ^ (-(ηc / 4)) * δ ^ ηc := by gcongr
    refine hstep.trans ?_
    rw [← NNReal.rpow_add hδ0.ne', ← NNReal.rpow_add hδ0.ne']
    have harith : -(ηc / 4) + -(ηc / 4) + ηc = ηc / 2 := by ring
    rw [harith, le_div_iff₀ (by norm_num : (0:NNReal) < 2), mul_comm]
    calc (2:NNReal) * δ ^ (ηc / 2) ≤ δ ^ (-(ηc / 4)) * δ ^ (ηc / 2) := by gcongr
      _ = δ ^ (ηc / 4) := by rw [← NNReal.rpow_add hδ0.ne']; congr 1; ring
      _ ≤ δ ^ ηin := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hηin
  have hmain := hcoarse (δ := δ) (𝒰 := 𝒰) (Cstar := Cstar)
    (ηl := ML2Spine.spineRung β ϖ ε₁ gain dens) (εd := ML2Spine.spineDiv ϖ ε₁)
    (N := ML2Spine.spineCount ϖ ε₁) (a := a) (b := b) (m := m) (κ := κc) (t := tθ') (Yθ := Yθ)
    (v := v) hδ0 hδ1 hθle hwin.toIsKatzTaoDividingWindow (hsp.rung_pos m).le hκc hCstar htθ' hYθ
    hballθ hfullθ
  have hexp : -(εc - κc + (κc + ML2Spine.spineRung β ϖ ε₁ gain dens m))
      = -(εc + ML2Spine.spineRung β ϖ ε₁ gain dens m) := by ring
  rw [hexp] at hmain
  exact hmain

open Classical in
/-- **The coarse row from the image form of the structural row.**  `Kakeya.ML2Core.CoarseStructRow`
is what a producer would actually prove — the retained parents are parents of retained fine nodes —
and `Kakeya.ML2Core.coarseBallRow_of_coarseStructRow` turns it into the minimal form. -/
theorem exists_threshold_coarseRow {β ϖ ε₁ εc κc : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hKT : Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hκc : 0 ≤ κc) (hκcεc : κc < εc) :
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ {ηin : ℝ} {C : NNReal},
      0 < ηin → ηin ≤ η0 →
      CoarseStructRow.{u} β ϖ ε₁ ηin κc gain dens C →
      CoarseRow.{u} β ϖ ε₁ ηin εc κc gain dens C := by
  obtain ⟨η0, hη0, h⟩ :=
    exists_threshold_coarseRow_of_ballRow.{u} (β := β) (ϖ := ϖ) (ε₁ := ε₁) (εc := εc) (κc := κc)
      (gain := gain) (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens hKT hκc hκcεc
  exact ⟨η0, hη0, fun hηin0 hηin hstruct =>
    h hηin0 hηin (coarseBallRow_of_coarseStructRow hstruct)⟩

open Classical in
/-- **The assembly**: `hfac` is the two-scale split plus its three factor rows. -/
theorem hfacLevels_of_rows {β ϖ ε₁ ηin εf εc κc : ℝ} {gm gain dens : ℝ → ℝ} {C : NNReal}
    (hfine : FineRow.{u} β ϖ ε₁ ηin εf κc gain dens C)
    (hmid : MiddleRow.{u} β ϖ ε₁ ηin κc gm gain dens C)
    (hcoarse : CoarseRow.{u} β ϖ ε₁ ηin εc κc gain dens C) :
    HfacLevels.{u} β ϖ ε₁ ηin εf εc κc gm gain dens C := by
  filter_upwards [hfine, hmid, hcoarse, self_mem_nhdsWithin] with δ hf hm hc hδ0
  have hδ0' : (0:NNReal) < δ := hδ0
  intro ι u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ ht₁ hballt hballs h4 h5 h6 hballu hune hmax
    hdense hcomp hlamlow hcardu hCstar hCu hmass hδb hba ha1
  obtain ⟨tτ', htτ', tθ', htθ', Yτ, Yτ', Yθ, Y', hcard, hYτ, hYτ', hYθ, hY'tube, hY'shade,
      hYτ'shade, hne, href1, href2, hfull1, hfull2, hprod⟩ :=
    exists_spineTwoScale_ofChain_translated (E := EuclideanSpace ℝ (Fin 3)) hδ0'
      𝒰.cover.toChain (le_of_lt hwin.coarse_lt_fine)
      (le_of_lt (lt_of_lt_of_le hwin.coarse_lt_fine hwin.fine_le_gridLen))
      hwin.fine_le_gridLen hδb hba ha1 v ht₁ hballt hballs
  obtain ⟨hτne, hθne⟩ := hne hmass
  obtain ⟨jτ, hjτ, hfineB⟩ :=
    hf u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ tτ' tθ' Yτ' Yθ Y' ht₁ htτ' htθ' hτne hθne
      hYτ' hYθ hY'tube hballt hballs hmax hdense hlamlow hcardu hCstar hCu hmass
      href1 hfull2 h4 h5 h6 hδb hba ha1
  obtain ⟨jθ, hjθ, hmidB⟩ :=
    hm u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ tτ' tθ' Yτ' Yθ Y' ht₁ htτ' htθ' hτne hθne
      hYτ' hYθ hY'tube hballt hballs hmax hdense hlamlow hcardu hCstar hCu hmass
      href1 hfull2 h4 h5 h6 hδb hba ha1
  have hcoarseB :=
    hc u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ tτ' tθ' Yτ' Yθ Y' ht₁ htτ' htθ' hτne hθne
      hYτ' hYθ hY'tube hballt hballs hmax hdense hlamlow hcardu hCstar hCu hmass
      href1 hfull2 h4 h5 h6 hδb hba ha1
  exact ⟨tτ', tθ', Yτ', Yθ, Y', jτ, jθ, htτ', htθ', htτ' hjτ, hjθ, hτne,
    hprod jτ hjτ jθ hjθ, hfineB, hmidB, hcoarseB⟩



/-- **`HfacLevels` from the middle row and the structural row.**

The fine and coarse factors are discharged from the Katz--Tao estimate; what is left is the
middle factor (`Kakeya.ML2Core.MiddleRow`) and the two structural facts about the two-scale
split that `Kakeya.ML2Core.exists_spineTwoScale_ofChain_translated` does not return
(`Kakeya.ML2Core.CoarseStructRow`).  Both are needed only for `ηin` below a threshold that the
theorem produces. -/
theorem exists_threshold_hfacLevels_of_middleRow {β ϖ ε₁ εf εc κc : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hKT : Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hεf : 0 < εf) (hκc : 0 ≤ κc) (hκcεc : κc < εc) :
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ {ηin : ℝ} {gm : ℝ → ℝ} {C : NNReal},
      0 < ηin → ηin ≤ η0 →
      MiddleRow.{u} β ϖ ε₁ ηin κc gm gain dens C →
      CoarseStructRow.{u} β ϖ ε₁ ηin κc gain dens C →
      HfacLevels.{u} β ϖ ε₁ ηin εf εc κc gm gain dens C := by
  obtain ⟨η1, hη1, hfine⟩ := exists_threshold_fineRow.{u} (β := β) (εf := εf) hβ0.le hKT hεf
  obtain ⟨η2, hη2, hcoarse⟩ :=
    exists_threshold_coarseRow.{u} (β := β) (ϖ := ϖ) (ε₁ := ε₁) (εc := εc) (κc := κc)
      (gain := gain) (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens hKT hκc hκcεc
  refine ⟨min η1 η2, lt_min hη1 hη2, ?_⟩
  intro ηin gm C hηin0 hηin hmid hstruct
  exact hfacLevels_of_rows (hfine hηin0 (le_trans hηin (min_le_left _ _)))
    hmid (hcoarse hηin0 (le_trans hηin (min_le_right _ _)) hstruct)

/-- **`ML2Assembly.GeometricCoreAt` from the middle row.**

The run's closure, with the fine factor, the coarse factor, the two-scale split, the trial
supplier and the descent all discharged.  What the supplier must produce, per `(β, ϖ, gain, dens)`
and at **arbitrarily small `ηin`** (the fine and coarse factors each impose a threshold on it):

* `Kakeya.ML2Core.MiddleRow` — the middle factor at the window;
* `Kakeya.ML2Core.CoarseStructRow` — `1 ≤ a` and `tθ' ⊆ coarseNode '' tτ'`;
* `Kakeya.ML2Core.SiteWitness`, `Kakeya.ML2Core.FloorPayload` — unchanged;
* the budget `hexp` and the scalar side conditions.

Quantifier order, as in `Kakeya.ML2Core.geometricCoreAt_of_hfac_witness_payload` and for the same
reason: every `∀ᶠ (δ : NNReal)` sits inside `∀ β ϖ gain dens`,
and inside the `∀ η0` that the fine/coarse thresholds introduce. -/
theorem geometricCoreAt_of_middleRow.{v} (K' : ℕ)
    (hsup : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{v} β ϖ gain dens →
      KatzTaoEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β →
      0 < ϖ ∧ (∀ ζ, 0 < ζ → 0 < gain ζ) ∧ (∀ ζ, 0 < ζ → 0 < dens ζ) ∧
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      ∃ (C : NNReal) (Kl cl : ℕ) (aL η' εf εp εc κc κ' θ₂ : ℝ) (gm : ℝ → ℝ),
        0 < aL ∧ 1 ≤ C ∧ 0 < εf ∧ 0 < εp ∧ 0 < κc ∧ κc < εc ∧ 0 < κ' ∧ 0 < θ₂ ∧
        (∀ k : ℕ, k < ML2Spine.spineCount ϖ ε₁ →
          κc + ML2Spine.spineRung β ϖ ε₁ gain dens k ≤ 2 * η') ∧
        ∀ η0 : ℝ, 0 < η0 → ∃ ηin : ℝ, 0 < ηin ∧ ηin ≤ η0 ∧
          (∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
            6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₂ + ηin
              ≤ gm X - εf - εp - (εc + X) - κ') ∧
          MiddleRow.{v} β ϖ ε₁ ηin κc gm gain dens C ∧
          CoarseStructRow.{v} β ϖ ε₁ ηin κc gain dens C ∧
          -- The four-way split's own row: the seam at `(p, b)` and the new-parent factor at
          -- `(a, p)`.  `Kakeya.ML2Core.hfacPostDrop_of_hfacLevels` produces the three-factor text
          -- only, so after the re-cut  the fourth conjunct is a **named
          -- obligation of the supplier**, not something this wiring can manufacture.
          HfacPostDropFour.{v} β ϖ ε₁ ηin η' εf εp εc κc gm gain dens (max C 4) ∧
          SiteWitness.{v} η ηin (defectMargin β ϖ ε₁ gain dens) aL (max C 4) ∧
          FloorPayload.{v} (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens
            (polylogLoss K')) :
    ML2Assembly.GeometricCoreAt.{v} := by
  refine geometricCoreAt_of_hfac_witness_payload K' (fun β ϖ gain dens hβ0 hβ1 hp hKT hF => ?_)
  obtain ⟨hϖ, hgain, hdens, ε₁, hε₁, η, hη0, hη1, C, Kl, cl, aL, η', εf, εp, εc, κc, κ', θ₂, gm,
    haL, hC, hεf, hεp, hκc, hκcεc, hκ', hθ₂, hres, hrest⟩ := hsup β ϖ gain dens hβ0 hβ1 hp hKT hF
  obtain ⟨η0, hη00, hthr⟩ :=
    exists_threshold_hfacLevels_of_middleRow.{v} (β := β) (ϖ := ϖ) (ε₁ := ε₁) (εf := εf)
      (εc := εc) (κc := κc) (gain := gain) (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens hKT hεf
      hκc.le hκcεc
  obtain ⟨ηin, hηin0, hηin, hexp, _hmid, _hstruct, hfour, hwit, hfloor⟩ := hrest η0 hη00
  exact ⟨hϖ, hgain, hdens, ε₁, hε₁, η, hη0, hη1, max C 4, C, Kl, cl, ηin, aL, η', εf, εp, εc, κc,
    κ', θ₂, gm, haL, hC, le_trans hC (le_max_left _ _), hκc, hκ', hθ₂, hεp, hres, hexp,
    hfour, hwit, hfloor⟩

/-! ## The budget `hexp`, measured -/

/-- **`hexp` closes at the sharp ambient gain**, and it is *not* in the family.

`Kakeya.ML2Core.trialOutcome_middle_of_floorFactors_alpha`'s budget is

```
6 ν + θ₂ + η_in  ≤  gm X − εf − (εc + X) − κ'      for every rung  X ≥ ν
```

which is `Kakeya.ML2Core.rung_budget_closes_of_overhead_le_four`'s ledger at overhead
`Ω = 2 ν + θ₂ + η_in` (the target `4 ν` is already inside the `6 ν`), not at the refuted
`Ω = 6 ν` of `Kakeya.ML2Core.not_rung_budget_of_overhead_six`.  At the sharp ambient gain
`gm X = 47 X / 5` (`Kakeya.ML2Core.middle_factor_of_edNodes_sharp` transported by
`Kakeya.ML2Core.ambient_sharp_gain_ge` at the window's own separation exponent) the whole budget
reduces to the **single linear condition** `θ₂ + η_in + εf + εc + κ' ≤ 12 ν / 5`, on five free
positive parameters.

So `hexp` costs nothing structural: no constraint on `ϖ`, on `ζ' − ζ`, on `β` or on `Cu₀`, and
no threshold in `δ`.  It is a choice of five small numbers below a fixed multiple of `ν`. -/
theorem hexp_of_sharp_gain {β ϖ ε₁ ηin εf εc κ' θ₂ : ℝ} {gain dens : ℝ → ℝ}
    (hsmall : θ₂ + ηin + εf + εc + κ'
      ≤ 12 * ML2Spine.spineNu β ϖ ε₁ gain dens / 5) :
    ∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
      6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₂ + ηin
        ≤ 47 * X / 5 - εf - (εc + X) - κ' := by
  intro X hX
  linarith

/-- **The constant `12/5` is sharp at the bottom rung.**  Firing control for
`Kakeya.ML2Core.hexp_of_sharp_gain`: the budget is an equality-tight linear condition, so any
`θ₂ + η_in + εf + εc + κ'` strictly above `12 ν / 5` makes it FAIL at `X = ν`, which is where
`Kakeya.ML2Spine.IsSpine.rung_mono` puts the bottom rung. -/
theorem not_hexp_at_bottom_rung {ν θ₂ ηin εf εc κ' : ℝ}
    (hbig : 12 * ν / 5 < θ₂ + ηin + εf + εc + κ') :
    ¬ (6 * ν + θ₂ + ηin ≤ 47 * ν / 5 - εf - (εc + ν) - κ') := by
  intro h
  linarith

/-- ** condition L1, answered: the four-loss `hexp` closes, and at the SAME
constant `12ν/5`.**

With the new-parent factor `hexp` becomes
`6ν + θ₂ + η_in ≤ gm X − εf − εp − (εc + X) − κ'`.  At the
sharp ambient gain `gm X = 47X/5` the budget still collapses to one linear condition, and the
right-hand constant is **unchanged**:

```
θ₂ + η_in + εf + εp + εc + κ'  ≤  12 ν / 5
```

Six free positive parameters under the same ceiling that five sat under.  So the fourth factor
costs **no budget**, only headroom — which is exactly what the telescoping `ρ_a·(ρ_p/2ρ_a)·
(ρ_b/2ρ_p)·(δ/2ρ_b) = δ/8` predicts (l.4666-4669) and what 's condition L2 calls
a re-partition rather than a new charge.

**Family/shading:** none, a scalar budget.  **Level pair:** none; `X` ranges over the window's
rungs. -/
theorem hexp_of_sharp_gain_four {β ϖ ε₁ ηin εf εp εc κ' θ₂ : ℝ} {gain dens : ℝ → ℝ}
    (hsmall : θ₂ + ηin + εf + εp + εc + κ'
      ≤ 12 * ML2Spine.spineNu β ϖ ε₁ gain dens / 5) :
    ∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
      6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₂ + ηin
        ≤ 47 * X / 5 - εf - εp - (εc + X) - κ' := by
  intro X hX
  linarith

/-- **The four-loss refutation threshold, and the margin `εp` eats.**

`Kakeya.ML2Core.not_hexp_at_bottom_rung` with the fifth loss: the bottom rung `X = ν` refutes the
budget as soon as `12ν/5 < θ₂ + η_in + εf + εp + εc + κ'`.  The ceiling did not move; the number of
terms under it did.  This is the "strictly easier to trip" that 
asks to be reported. -/
theorem not_hexp_at_bottom_rung_four {ν θ₂ ηin εf εp εc κ' : ℝ}
    (hbig : 12 * ν / 5 < θ₂ + ηin + εf + εp + εc + κ') :
    ¬ (6 * ν + θ₂ + ηin ≤ 47 * ν / 5 - εf - εp - (εc + ν) - κ') := by
  intro h
  linarith

/-! ## `0-C`: the singleton **instance**, and why the suggested route to it is blocked -/

/-- **The one-tube hierarchy carries NO Katz--Tao dividing window at a positive rung.**

`Kakeya.ML2Core.singletonWindow` is stated at `η ≡ 0`, and the `η ≡ 0` is **load-bearing, not
incidental**: at `a = 0`, `b = 1` the field `le_window_maxDensity` demands
`(ρ_0/ρ)^{η_{m+1}} ≤ C⋆ · Δ_max` at every intermediate scale `ρ` of the window, and on a
one-element family the right-hand side is at most `C⋆ = 1` while `ρ_0 = 1` and every admissible
`ρ` is `< 1`.  Taking `ρ := ρ_1^{ε_d}` — the coarse endpoint of the admissible range, legal
because `ε_d ≤ 1/2` — the left-hand side exceeds `1`.

So the model of `Kakeya.ML2Core.not_middleFactor_hypothesis` does **not** survive the passage to a
positive rung, and 's route to the missing instance (re-run
`Kakeya.ML2Core.singletonWindowLevels` at the spine parameters) is blocked at the **parent**
structure, before the level clause is ever reached. -/
theorem not_singletonWindow_of_pos_rung {ι : Type*} (i₀ : ι) {δ : NNReal}
    (hδ0 : 0 < δ) (hδlt : δ < 1) (hδ1 : δ ≤ 1) (hN : 1 ≤ Tube.ssfGridLen δ)
    (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
    {η : ℕ → ℝ} {εd : ℝ} (hεd0 : 0 < εd) (hεdh : εd ≤ 1 / 2) (hη1 : 0 < η 1) {Nw : ℕ} :
    ¬ ML2Reduction.IsKatzTaoDividingWindow
        (singletonUniform i₀ hδ0 hδ1 (Tube.ssfGridLen δ) T) 1 η εd Nw 0 1 0 := by
  classical
  intro hw
  set M : ℕ := Tube.ssfGridLen δ with hM
  set 𝒰 := singletonUniform i₀ hδ0 hδ1 M T with h𝒰
  have hidx : ∀ k, 𝒰.cover.indexSet k = ({i₀} : Finset ι) := fun k => rfl
  set g : NNReal := Tube.gridScale δ M 1 with hg
  have hg0 : (0:ℝ) < (g : ℝ) := by exact_mod_cast Tube.gridScale_pos hδ0 M 1
  have hMpos : (0:ℝ) < (M : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hglt : (g : ℝ) < 1 := by
    have : g < 1 := by
      rw [hg, Tube.gridScale]
      exact NNReal.rpow_lt_one hδlt (by positivity)
    exact_mod_cast this
  set ρ : NNReal := g ^ εd with hρ
  have hρcoe : (ρ : ℝ) = (g : ℝ) ^ εd := by rw [hρ, NNReal.coe_rpow]
  have hρ0 : (0:ℝ) < (ρ : ℝ) := by rw [hρcoe]; positivity
  have hρ1 : (ρ : ℝ) < 1 := by
    rw [hρcoe]; exact Real.rpow_lt_one hg0.le hglt hεd0
  have hz : (Tube.gridScale δ M 0 : ℝ) = 1 := by rw [Tube.gridScale_zero]; norm_num
  have hlo : (Tube.gridScale δ M 1 : ℝ)
      * ((Tube.gridScale δ M 0 : ℝ) / (Tube.gridScale δ M 1 : ℝ)) ^ εd ≤ (ρ : ℝ) := by
    rw [← hg, hz, hρcoe, one_div, ← Real.rpow_neg_one]
    have h1 : ((g:ℝ) ^ (-1:ℝ)) ^ εd = (g:ℝ) ^ (-εd) := by
      rw [← Real.rpow_mul hg0.le]; ring_nf
    rw [h1]
    have h2 : (g:ℝ) * (g:ℝ) ^ (-εd) = (g:ℝ) ^ (1 - εd) := by
      rw [show (1:ℝ) - εd = 1 + -εd by ring, Real.rpow_add hg0, Real.rpow_one]
    rw [h2]
    exact Real.rpow_le_rpow_of_exponent_ge hg0 hglt.le (by linarith)
  have hhi : (ρ : ℝ) ≤ (Tube.gridScale δ M 0 : ℝ)
      * ((Tube.gridScale δ M 1 : ℝ) / (Tube.gridScale δ M 0 : ℝ)) ^ εd := by
    rw [← hg, hz, hρcoe]; simp
  have hmem0 : i₀ ∈ 𝒰.cover.indexSet 0 := by
    rw [hidx 0]; exact Finset.mem_singleton_self i₀
  have hres := hw.le_window_maxDensity ρ hlo hhi i₀ hmem0
  have hcard1 : (𝒰.nodesUnder 1 0 i₀).card ≤ 1 := by
    have : 𝒰.nodesUnder 1 0 i₀ ⊆ 𝒰.cover.indexSet 1 := Finset.filter_subset _ _
    have h2 := Finset.card_le_card this
    rw [hidx 1, Finset.card_singleton] at h2
    exact h2
  have hRHS : (1 : ENNReal) * Kakeya.maxDensity (𝒰.nodesUnder 1 0 i₀)
      (fun j' => ((𝒰.cover.tube 1 j').rescale ρ).toConvexSpaceBody) ≤ 1 := by
    rw [one_mul]
    refine le_trans (Kakeya.maxDensity_le_card _ _) ?_
    exact_mod_cast hcard1
  have hLHS : (1 : ENNReal) < ENNReal.ofReal
      (((Tube.gridScale δ M 0 : ℝ) / (ρ : ℝ)) ^ η 1) := by
    rw [hz]
    have hbase : (1:ℝ) < 1 / (ρ : ℝ) := by rw [lt_div_iff₀ hρ0]; linarith
    have : (1:ℝ) < (1 / (ρ : ℝ)) ^ η 1 := Real.one_lt_rpow_iff_of_pos (by positivity) |>.mpr
      (Or.inl ⟨hbase, hη1⟩)
    calc (1 : ENNReal) = ENNReal.ofReal 1 := by simp
      _ < ENNReal.ofReal ((1 / (ρ : ℝ)) ^ η 1) := by
          exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr this
  exact absurd (le_trans hres hRHS) (not_le.mpr hLHS)


/-- **The same at the spine parameters**, where `η := spineRung` is positive at every rung and
`ε_d := spineDiv ≤ 1/10`.  Since `ML2Reduction.IsKatzTaoDividingWindowLevels` extends the parent,
this refutes the twin as well: the missing `0-C` instance cannot be built on the one-tube
hierarchy. -/
theorem not_singletonWindow_at_spine {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {ι : Type*} (i₀ : ι) {δ : NNReal}
    (hδ0 : 0 < δ) (hδlt : δ < 1) (hδ1 : δ ≤ 1) (hN : 1 ≤ Tube.ssfGridLen δ)
    (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))) {Nw : ℕ} :
    ¬ ML2Reduction.IsKatzTaoDividingWindow
        (singletonUniform i₀ hδ0 hδ1 (Tube.ssfGridLen δ) T) 1
        (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁) Nw 0 1 0 := by
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  refine not_singletonWindow_of_pos_rung i₀ hδ0 hδlt hδ1 hN T
    (ML2Spine.spineDiv_pos hϖ hε₁) ?_ (hsp.rung_pos 1)
  have := ML2Spine.spineDiv_le_one hϖ hε₁
  linarith

/-! ## The source's count floor is on `nodesUnder`, not on `t₁` -/

/-- **The bridge, and it points the wrong way.**

The refined source's alternative-(F) count floor (l.4074-4079, restated as `eq:ml2-count-floor`
at l.4476-4482) reads `#𝕊''_m⟨T_p⟩ ≥ (ρ_p/ρ_m)^{2+4ζ}`, a floor on the **hierarchy's** level-`m`
descendants of a retained `p`-cell.  In the tree that object is
`Tube.UniformTubeSet.nodesUnder`, and `hfac` **already carries the clause**, verbatim, as its
fourth `(F)` row, at `ζ := spineRung β ϖ ε₁ gain dens (m+1) / 16`.

The quantity `Kakeya.ML2Core.middle_gain_nonpos_of_card_le_one` needs bounded below is a different
one: the **seam's** coarse fibre `{j ∈ t₁ | coarseNode 𝒞 a b j = k}`.  This lemma is the only
relation between them, and it is an inclusion of the seam's fibre **into** the hierarchy's
descendant set — so the source's floor bounds the *superset* below and says nothing about the
subset.  `Kakeya.ML2Core.not_card_le_of_subset_of_card_le` is that gap,. -/
theorem coarseFibre_subset_nodesUnder {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {a b : ℕ} (hab : a ≤ b) (hbN : b ≤ Tube.ssfGridLen δ)
    {t₁ : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b) (k : ι) :
    (open scoped Classical in
      ({j ∈ t₁ | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = k} : Finset ι))
      ⊆ 𝒰.nodesUnder b a k := by
  classical
  intro j hj
  obtain ⟨hjt, hjk⟩ := Finset.mem_filter.mp hj
  have hact : j ∈ ML2Reduction.activeNodes 𝒰.cover.toChain b := ht₁ hjt
  refine Finset.mem_filter.mpr ⟨ML2Reduction.activeNodes_subset _ _ hact, ?_⟩
  have := ML2Reduction.tube_le_coarseNode 𝒰.cover.toChain hab hbN hact
  rwa [hjk] at this

/-- **A lower bound on a superset is not a lower bound on a subset.**  The one-line reason the
source's count floor, faithfully transcribed as `hfac`'s fourth `(F)` row, does not block the
singleton model. -/
theorem not_card_le_of_subset_of_card_le :
    ¬ ∀ X Y : Finset ℕ, X ⊆ Y → 2 ≤ Y.card → 2 ≤ X.card := by
  intro h
  have := h {0} {0, 1} (by decide) (by decide)
  simp at this

/-! ## The hypothesis `1 ≤ a` -/

/-- **At `a = 0` the coarse factor's smallness threshold is unreachable.**

`Kakeya.ML2Core.exists_coarse_factor_at_window` returns a threshold `θ₀ ≤ 1` and demands
`Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ θ₀`.  At `a = 0` the grid scale is `1` on the nose, so
the demand is `1 ≤ θ₀`: for any threshold strictly below `1` the hypothesis is **unsatisfiable**,
not a consequence of the hypotheses.  `Kakeya.ML2Core.eventually_gridScale_le` carries the same fact as its
`1 ≤ k` hypothesis. -/
theorem not_gridScale_zero_le_of_lt_one {δ : NNReal} {N : ℕ} {θ₀ : NNReal} (hθ₀ : θ₀ < 1) :
    ¬ (Tube.gridScale δ N 0 ≤ θ₀) := by
  rw [Tube.gridScale_zero]
  exact not_le.mpr hθ₀

/-- **And nothing in the window's order data excludes `a = 0`.**

`ML2Reduction.IsKatzTaoDividingWindow`'s three order fields are `step_lt : m < N`,
`coarse_lt_fine : a < b` and `fine_le_gridLen : b ≤ ssfGridLen δ`.  They are jointly satisfiable
at `a = 0`, so `1 ≤ a` is not derivable from them.  (This does **not** settle the analytic
fields — `coarse_maxDensity_le`, `le_window_maxDensity`, `le_level_maxDensity` — which are
measured  and left open there.) -/
theorem order_data_admits_zero_coarse :
    ∃ N a b m M : ℕ, m < N ∧ a < b ∧ b ≤ M ∧ a = 0 :=
  ⟨1, 0, 1, 0, 1, by omega, by omega, by omega, rfl⟩

/-! ## Non-vacuity: `hfac` forces a NON-POSITIVE middle gain at a singleton retained node set -/

open Classical in
/-- **`hfac` forces `gm ≤ 0` wherever the retained node set is a singleton.**

`Kakeya.ML2Core.middle_gain_nonpos_of_singleton_nodes` applied to `hfac`'s **own** conclusion:
the product bound and the middle bound sit in the same existential, so at `t₁.card ≤ 1` every
coarse fibre of every `tτ' ⊆ t₁` has at most one member, the cardinality factor is `1`, and a
multiplicity that is at least `1` forces the exponent down.

`hfac`'s `t₁` is **universally quantified** subject only to `t₁ ⊆ activeNodes b`, the two ball
rows and the leaf-mass row, so nothing in `ML2Reduction.IsKatzTaoDividingWindowLevels` prevents
the adversary choosing a single active node.  Pair with
`Kakeya.ML2Core.not_gm_nonpos_of_hexp`. -/
theorem middleGain_nonpos_of_hfacLevels {β ϖ ε₁ ηin εf εc κc : ℝ} {gm gain dens : ℝ → ℝ}
    {C : NNReal} (hβ0 : 0 ≤ β) (h : HfacLevels.{u} β ϖ ε₁ ηin εf εc κc gm gain dens C) :
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
          Cstar ≤ (δ : ENNReal) ^ (-κc) →
          Cu ≤ max C 4 →
          0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
          δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
          Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
          Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
          t₁.card ≤ 1 →
          gm (ML2Spine.spineRung β ϖ ε₁ gain dens m) ≤ 0
  := by
  filter_upwards [h, Ioo_mem_nhdsGT (show (0:NNReal) < 1 from zero_lt_one)] with δ hδ hmem
  intro ι u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    h15 h16 h17 h18 h19 hcard1
  obtain ⟨tτ', tθ', Yτ', Yθ, Y', jτ, jθ, htτ', htθ', hjτ, hjθ, hτne, hprod, hfineB, hmidB,
    hcoarseB⟩ := hδ u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    h13 h14 h15 h16 h17 h18 h19
  exact middle_gain_nonpos_of_singleton_nodes hmem.1 hmem.2 hβ0 𝒰.cover.toChain hcard1 htτ' h16
    hprod hmidB


/-- **What a repair of `hfac` must actually deliver: two nodes in the COARSE FIBRE.**

The contrapositive of `Kakeya.ML2Core.middle_gain_nonpos_of_card_le_one`.  A positive middle gain
forces `2 ≤ |{j ∈ tτ' | coarseNode 𝒞 a b j = jθ}|` at the selected `jθ` — **not** merely
`2 ≤ |t₁|`.  Since `t₁ ⊇ tτ' ⊇ {j ∈ tτ' | coarseNode … = jθ}`, a cardinality row placed on `t₁`
survives to the fibre only if it also controls the seam's two subsettings; a row that does not is
a third relocation of the same quantifier and not a repair.  This is the exact specification the
refinement predicate needs. -/
theorem two_le_coarseFibre_card_of_middle_gain_pos {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {δ τ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1) {β gm : ℝ} (hβ0 : 0 ≤ β) (hgm : 0 < gm)
    {ι : Type*} {u s₁ tτ' : Finset ι} {T : ι → ShadedTube δ E} {Yτ' : ι → ShadedTube τ E}
    {N : ℕ} {σ : ℕ → NNReal} (𝒞 : Tube.ChainCoverSystem u (fun i ↦ (T i).toTube) N σ)
    {a b : ℕ} {jθ : ι} {Loss A C : ENNReal}
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
    2 ≤ (open scoped Classical in
      ({j ∈ tτ' | ML2Reduction.coarseNode 𝒞 a b j = jθ} : Finset ι)).card := by
  classical
  by_contra hcon
  exact absurd (middle_gain_nonpos_of_card_le_one hδ0 hδ1 hβ0 (by omega) hmass hprod hbd)
    (not_le.mpr hgm)

open Classical in
/-- **0-A′, answered: the count floor IS already delivered, and it does not help.**

`Kakeya.ML2Core.FloorHypothesisAt` (`SpineFloorShapeM1.lean:128-141`) carries the refined source's
alternative-(F) count floor (l.4074-4079 / `eq:ml2-count-floor` l.4476-4482) verbatim, at
`ζ := spineRung β ϖ ε₁ gain dens (m+1) / 16`; and `Kakeya.ML2Core.HfacPostDrop` — the post-drop
`hfac` of the guarded `trialOutcome_middle_of_floorFactors_alpha` — carries **the same text** as
its fourth `(F)` **antecedent**, so a producer of `hfac` may *assume* it.

This theorem is that assumption in force.  With `hF1`, `hF2` and the count floor `hF3` all
supplied, `HfacPostDrop` still forces `gm (spineRung β ϖ ε₁ gain dens m) ≤ 0` at any instance
whose retained node set `t₁` has at most one member and whose leaf mass is positive — the same
conclusion as `Kakeya.ML2Core.middleGain_nonpos_of_hfacLevels`, which does not have the floor.

**So the transport asked for in `0-A′` cannot close `hfac`: the clause is not missing, it is
already there, and it is about a different set.**  The floor bounds
`𝒰.nodesUnder m' p jp` below; what the gain consumes is `{j ∈ t₁ | coarseNode 𝒞 a b j = jθ}`;
`Kakeya.ML2Core.coarseFibre_subset_nodesUnder` is the only relation between them and it makes the
second a **subset** of the first.  `Kakeya.ML2Core.not_card_le_of_subset_of_card_le` is the
one-line reason that is worth nothing.  Pair with `Kakeya.ML2Core.not_gm_nonpos_of_hexp`. -/
theorem middleGain_nonpos_of_hfacPostDrop {β ϖ ε₁ ηin η' εf εc κc : ℝ} {gm gain dens : ℝ → ℝ}
    {Cu₀ : NNReal} (hβ0 : 0 ≤ β)
    (h : HfacPostDrop.{u} β ϖ ε₁ ηin η' εf εc κc gm gain dens Cu₀) :
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
          Cstar ≤ (δ : ENNReal) ^ (-κc) →
          Cu ≤ Cu₀ →
          0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
          δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
          Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
          Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
          -- the refined (F): the genuine parent level, its density, and the count floor
          ∀ p : ℕ, a ≤ p →
            (∀ m' : ℕ, a < m' → m' < b →
              ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
                ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
              (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
                ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
              p < m') →
            (∀ jθ ∈ 𝒰.cover.indexSet a,
              Kakeya.maxDensity (𝒰.nodesUnder p a jθ) (fun j ↦ (𝒰.cover.tube p j).toConvexSpaceBody)
                ≤ (δ : ENNReal) ^ (-(2 * η'))) →
            (∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ, ∀ m' : ℕ, a < m' → m' < b →
              ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
                ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
              (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
                ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
              p < m' →
              ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
                    ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
                ≤ ((𝒰.nodesUnder m' p jp).card : ℝ)) →
          t₁.card ≤ 1 →
          gm (ML2Spine.spineRung β ϖ ε₁ gain dens m) ≤ 0
  := by
  filter_upwards [h, Ioo_mem_nhdsGT (show (0:NNReal) < 1 from zero_lt_one)] with δ hδ hmem
  intro ι u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    h15 h16 h17 h18 h19 p hp hF1 hF2 hF3 hcard1
  obtain ⟨tτ', tθ', Yτ', Yθ, Y', jτ, jθ, htτ', htθ', hjτ, hjθ, hτne, hprod, hfineB, hmidB,
    hcoarseB⟩ := hδ u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    h13 h14 h15 h16 h17 h18 h19 p hp hF1 hF2 hF3
  exact middle_gain_nonpos_of_singleton_nodes hmem.1 hmem.2 hβ0 𝒰.cover.toChain hcard1 htτ' h16
    hprod hmidB

/-- **The budget forbids exactly what `Kakeya.ML2Core.middleGain_nonpos_of_hfacLevels` forces.**

`hexp` at the window's own rung `X = η_m ≥ ν` gives
`gm X ≥ 6ν + θ₂ + η_in + εf + εc + X + κ' > 0`, so `gm (spineRung … m) ≤ 0` is impossible.

Read with `Kakeya.ML2Core.middleGain_nonpos_of_hfacLevels`: **`hexp` and `hfac` are jointly
unsatisfiable at any instance whose retained node set `t₁` has at most one member and whose leaf
mass is positive.**  That is `Kakeya.ML2Core.not_middleFactor_hypothesis`'s singleton model
reaching the *level* twin, and it is a statement about the interface, not about this file. -/
theorem not_gm_nonpos_of_hexp {β ϖ ε₁ ηin εf εc κ' θ₂ : ℝ} {gm gain dens : ℝ → ℝ} {m : ℕ}
    (hν : 0 < ML2Spine.spineNu β ϖ ε₁ gain dens)
    (hrung : ML2Spine.spineNu β ϖ ε₁ gain dens
      ≤ ML2Spine.spineRung β ϖ ε₁ gain dens m)
    (hθ₂ : 0 < θ₂) (hηin : 0 < ηin) (hεf : 0 < εf) (hεc : 0 < εc) (hκ' : 0 < κ')
    (hexp : ∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
      6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₂ + ηin ≤ gm X - εf - (εc + X) - κ') :
    ¬ (gm (ML2Spine.spineRung β ϖ ε₁ gain dens m) ≤ 0) := by
  intro hcon
  have h := hexp (ML2Spine.spineRung β ϖ ε₁ gain dens m) hrung
  linarith

end Kakeya.ML2Core

end
