/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceLateChoice
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceWindowFork
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorTerminal
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoarseSeam

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Assembly

universe u

/-- The source parent parameter at a specified canonical finite rung. -/
noncomputable def sourceTerminalParent (β ϖ ε₁ : ℝ) (rawGain rawDens : ℝ → ℝ) (m : ℕ) : ℝ :=
  sourceParentMinimum (ML2Spine.spineDiv ϖ ε₁)
    (ML2Spine.spineRung β ϖ ε₁
      (sourceChoiceGain β rawGain rawDens) (sourceChoiceDens β rawDens) (m + 1))
    (rawGain (ML2Spine.spineRung β ϖ ε₁
      (sourceChoiceGain β rawGain rawDens) (sourceChoiceDens β rawDens) (m + 1) / 16))
    (rawDens (ML2Spine.spineRung β ϖ ε₁
      (sourceChoiceGain β rawGain rawDens) (sourceChoiceDens β rawDens) (m + 1) / 16))

/-- The net middle gain comes from the actual raw VNS output at the next rung divided by 16. -/
noncomputable def sourceTerminalNetGain (β ϖ ε₁ : ℝ) (rawGain rawDens : ℝ → ℝ) (m : ℕ) : ℝ :=
  sourceMiddleNetGain (ML2Spine.spineDiv ϖ ε₁)
    (rawGain (ML2Spine.spineRung β ϖ ε₁
      (sourceChoiceGain β rawGain rawDens) (sourceChoiceDens β rawDens) (m + 1) / 16))

end Kakeya.ML2Assembly

namespace Kakeya.ML2Core

universe u

open Classical in
/-- One rung's actual four-factor consumer input. All geometric, mass and lambda
antecedents are retained. The product and middle rows are read only for p < b. -/
def SourceHfacAtRung (δ : NNReal) (β ϖ ε₁ ηin η' εf εp εc κc net : ℝ)
    (gain dens : ℝ → ℝ) (Cu₀ : NNReal) (m : ℕ) : Prop :=
  ∀ {ι : Type u} (u : Finset ι)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam : NNReal)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (Cstar : ENNReal) (a b : ℕ),
    ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar
      (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
      (ML2Spine.spineCount ϖ ε₁) a b m →
    ∀ (v : EuclideanSpace ℝ (Fin 3)) (t₀ t₁ : Finset ι),
    t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
    (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
    (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι),
      ((T i).translate v).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
    (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
    (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
    (a ≠ 0 → ∀ k ∈ t₀, ((𝒰.cover.tube a k).translate v).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
    (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
    u.Nonempty →
    Kakeya.maxDensity u (fun i => (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
    ML2Shaded.HasDenseShading lam u (fun i => (T i).toShadedBody) →
    ML2Shaded.HasComparableDensities lam⁻¹ u (fun i => (T i).toShadedBody) →
    (δ : NNReal) ^ ηin / 2 ≤ lam →
    (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
    Cstar ≤ (δ : ENNReal) ^ (-κc) → Cu ≤ Cu₀ →
    0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
    δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
    Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
    Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
    ∀ p : ℕ, a ≤ p → p ≤ b →
    (∀ k ∈ sourceWindowLevels δ (ML2Spine.spineDiv ϖ ε₁) a b, p < k) →
    (∀ jθ ∈ 𝒰.cover.indexSet a,
      Kakeya.maxDensity (𝒰.nodesUnder p a jθ)
        (fun j => (𝒰.cover.tube p j).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-(2 * η'))) →
    (∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ,
      ∀ k ∈ sourceWindowLevels δ (ML2Spine.spineDiv ϖ ε₁) a b, p < k →
      ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ))
          ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
            ≤ ((𝒰.nodesUnder k p jp).card : ℝ)) →
    ∃ (tτ' tp' tθ' : Finset ι)
      (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
        (EuclideanSpace ℝ (Fin 3)))
      (Yp : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) p)
        (EuclideanSpace ℝ (Fin 3)))
      (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
        (EuclideanSpace ℝ (Fin 3)))
      (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (jτ jp jθ : ι),
      tτ' ⊆ t₁ ∧ tp' ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain p ∧
      tθ' ⊆ 𝒰.cover.indexSet a ∧ jτ ∈ t₁ ∧ jθ ∈ tθ' ∧ tτ'.Nonempty ∧ tp'.Nonempty ∧
      (p < b →
        ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
          (fun i => (T i).toShadedBody)
          ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
              ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
              tτ'.card (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
              tp'.card (Tube.gridScale δ (Tube.ssfGridLen δ) p) : NNReal) : ENNReal)
            * ShadedBody.multiplicity
              ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι) (fun i => (Y' i).toShadedBody)
            * ShadedBody.multiplicity
              ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j = jp} : Finset ι)
              (fun j => (Yτ' j).toShadedBody)
            * ShadedBody.multiplicity
              ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι)
              (fun k => (Yp k).toShadedBody)
            * ShadedBody.multiplicity tθ' (fun k => (Yθ k).toShadedBody)) ∧
      ShadedBody.multiplicity
        ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
          𝒰.cover.assign b i = jτ} : Finset ι) (fun i => (Y' i).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εf) *
          (({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι).card : ENNReal) ^ β ∧
      (p < b → ShadedBody.multiplicity
        ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j = jp} : Finset ι)
        (fun j => (Yτ' j).toShadedBody)
        ≤ (δ : ENNReal) ^ net *
          (({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j = jp}
            : Finset ι).card : ENNReal) ^ β) ∧
      ShadedBody.multiplicity
        ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι)
        (fun k => (Yp k).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εp) *
          (({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ}
            : Finset ι).card : ENNReal) ^ β ∧
      ShadedBody.multiplicity tθ' (fun k => (Yθ k).toShadedBody)
        ≤ (δ : ENNReal) ^ (-(εc + ML2Spine.spineRung β ϖ ε₁ gain dens m))
          * (tθ'.card : ENNReal) ^ β

open ML2Assembly

/-- The scheduled four-factor hypothesis has one threshold for the actual finite range. -/
def SourceFiniteHfac (β ϖ ε₁ ηin : ℝ) (rawGain rawDens : ℝ → ℝ)
    (acc : SourceLocalAccuracyData) (Cu₀ : NNReal) : Prop :=
  ∀ᶠ δ : NNReal in 𝓝[>] 0,
    ∀ m : ℕ, m < ML2Spine.spineCount ϖ ε₁ →
      SourceHfacAtRung.{u} δ β ϖ ε₁ ηin (sourceTerminalParent β ϖ ε₁ rawGain rawDens m)
        (acc.epsf m) (acc.epsp m) (acc.epsc m) acc.kappaC
        (sourceTerminalNetGain β ϖ ε₁ rawGain rawDens m)
        (sourceChoiceGain β rawGain rawDens) (sourceChoiceDens β rawDens) Cu₀ m

/-- The explicit count-product and loss consumer keeps the reserve as a gain. -/
theorem source_multiplicity_le_of_finite_four_factors
    {β ϖ ε₁ s ηL ηin η aL : ℝ} {rawGain rawDens : ℝ → ℝ}
    {acc : SourceLocalAccuracyData} {H : Finset ℝ}
    (hβ0 : 0 ≤ β)
    (hbudget : SourceLocalBudget β ϖ ε₁ rawGain rawDens s acc)
    (hlate : SourceLateInputBounds β ϖ ε₁ rawGain rawDens s acc H ηL ηin η aL)
    {m : ℕ} (hm : m < ML2Spine.spineCount ϖ ε₁)
    {δ : NNReal} {mu mf mm mp mc L Ccard : ENNReal} {Nf Nm Np Nc N : ℕ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hsplit : mu ≤ L * mf * mm * mp * mc)
    (hf : mf ≤ (δ : ENNReal) ^ (-(acc.epsf m)) * (Nf : ENNReal) ^ β)
    (hmid : mm ≤ (δ : ENNReal) ^ (sourceTerminalNetGain β ϖ ε₁ rawGain rawDens m)
      * (Nm : ENNReal) ^ β)
    (hpar : mp ≤ (δ : ENNReal) ^ (-(acc.epsp m)) * (Np : ENNReal) ^ β)
    (hcoarse : mc ≤ (δ : ENNReal) ^ (-(acc.epsc m + ML2Spine.spineRung β ϖ ε₁
      (sourceChoiceGain β rawGain rawDens) (sourceChoiceDens β rawDens) m)) * (Nc : ENNReal) ^ β)
    (hcard : (Nf : ENNReal) * (Nm : ENNReal) * (Np : ENNReal) * (Nc : ENNReal)
      ≤ Ccard * (N : ENNReal))
    (hL : L * Ccard ^ β ≤ (δ : ENNReal) ^ (-acc.kappaPrime)) :
    mu ≤ (δ : ENNReal) ^ (6 * ML2Spine.spineNu β ϖ ε₁
      (sourceChoiceGain β rawGain rawDens) (sourceChoiceDens β rawDens) +
        acc.reserve + acc.theta2 + ηin) * (N : ENNReal) ^ β := by
  apply multiplicity_le_of_four_factors (by simpa using hδ0.ne')
    (by exact_mod_cast hδ1) hβ0 hsplit hf hmid hpar hcoarse hcard hL
  have hb := hlate.budget m hm
  change _ ≤ sourceTerminalNetGain β ϖ ε₁ rawGain rawDens m at hb
  linarith only [hb]

open Classical in
/-- The finite engine leaves R0 available for the later refinement-loss absorption. -/
theorem source_sum_shade_le_finite_floor
    {β ϖ ε₁ s ηL ηin η aL : ℝ} {rawGain rawDens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hε₁ : 0 < ε₁)
    (hp : Lemma91ParamsAt.{u} β ϖ rawGain rawDens)
    {acc : SourceLocalAccuracyData} {H : Finset ℝ}
    (hbudget : SourceLocalBudget β ϖ ε₁ rawGain rawDens s acc)
    (hlate : SourceLateInputBounds β ϖ ε₁ rawGain rawDens s acc H ηL ηin η aL)
    {C Cu₀ : NNReal} {Kl cl : ℕ} (hC : 1 ≤ C) (hCu₀ : 1 ≤ Cu₀)
    (hfac : SourceFiniteHfac.{u} β ϖ ε₁ ηin rawGain rawDens acc Cu₀) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0,
      ∀ {ι : Type u} (S : Finset ι)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam : NNReal)
        (𝒰 : Tube.UniformTubeSet S (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (a b m : ℕ), m < ML2Spine.spineCount ϖ ε₁ →
        ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰
          ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
          (ML2Spine.spineRung β ϖ ε₁ (sourceChoiceGain β rawGain rawDens)
            (sourceChoiceDens β rawDens))
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
        (∀ i ∈ S, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        S.Nonempty →
        Kakeya.maxDensity S (fun i => (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam S (fun i => (T i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ S (fun i => (T i).toShadedBody) →
        (δ : NNReal) ^ ηin / 2 ≤ lam →
        (S.card : NNReal) ≤ δ ^ (-(4 : ℝ)) → Cu ≤ Cu₀ →
        FloorHypothesisAt β ϖ ε₁ (sourceChoiceGain β rawGain rawDens) (sourceChoiceDens β rawDens)
          (sourceTerminalParent β ϖ ε₁ rawGain rawDens m) 𝒰 a b m →
        ∑ i ∈ S, volume (T i).shade ≤
          (δ : ENNReal) ^ (6 * ML2Spine.spineNu β ϖ ε₁
            (sourceChoiceGain β rawGain rawDens) (sourceChoiceDens β rawDens) + acc.reserve)
            * (S.card : ENNReal) ^ β * volume (⋃ i ∈ S, (T i).shade) := by
  let gain := sourceChoiceGain β rawGain rawDens
  let dens := sourceChoiceDens β rawDens
  let gt := 6 * ML2Spine.spineNu β ϖ ε₁ gain dens + acc.reserve
  let κc := acc.kappaC
  let κ' := acc.kappaPrime
  let θ₂ := acc.theta2
  have hκc : 0 < κc := hbudget.coarse_density_pos
  have hκ' : 0 < κ' := hbudget.splitting_pos
  have hθ₂ : 0 < θ₂ := hbudget.terminal_accuracy_pos
  have hchoice := sourceParameterChoice hβ0 hβ1 hp
  have hsp := ML2Spine.spineRung_isSpine hβ0 hβ1 hp.window_pos hε₁
    hchoice.params.gain_pos hchoice.params.dens_pos
  obtain ⟨M₁, hM₁0, hseam₁⟩ := exists_windowSeam.{u} (E := EuclideanSpace ℝ (Fin 3))
  obtain ⟨M₂, hM₂0, hseam₂⟩ := exists_coarseWindowSeam.{u} (E := EuclideanSpace ℝ (Fin 3))
  set Mseam : ℕ := max M₁ M₂ with hMseam
  have hcc0 : 0 < Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
    Tube.le_volume.c_pos _
  obtain ⟨d1, hd10, hd1⟩ :=
    ML2Reduction.exists_threshold_coe_const_le_rpow_neg
      (C := max 1 (2 * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) *
        ((Mseam : NNReal) * Cu₀ * Cu₀) /
        (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))))
      (le_max_left _ _) (κ := θ₂) hθ₂
  obtain ⟨Cε, hCε⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (κ' / 30) (by positivity)
  obtain ⟨d2, hd20, hd2⟩ :=
    ML2Reduction.exists_threshold_const_le_rpow_neg
      (C := max 1 (Cε ^ 3 * Cu₀ ^ 8)) (le_max_left _ _)
      (κ := κ' / 2) (by positivity)
  obtain ⟨dL, hdL0, hdL1, hdL⟩ := exists_threshold_two_mul_ssfGridLen_le_log
  obtain ⟨d3, hd30, hd3⟩ :=
    ML2Reduction.exists_threshold_coe_const_le_rpow_neg (C := C) hC (κ := κc / 2)
      (by positivity)
  obtain ⟨dT', hdT'0, hdT'1, hdT'⟩ :=
    StickyKakeya.exists_threshold_totalLoss_le C hC Kl cl (κc / 2) (by positivity)
  filter_upwards [hfac, Ioc_mem_nhdsGT hd10, Ioc_mem_nhdsGT hd20, Ioc_mem_nhdsGT hdL0,
    Ioc_mem_nhdsGT hd30, Ioc_mem_nhdsGT hdT'0, Ioc_mem_nhdsGT (zero_lt_one' NNReal)]
    with δ hfacδ hm1 hm2 hmL hm3 hmT' hm01
  intro ι S T Cu lam 𝒰 a b m hm hwinL hball hSne hmaxS hdense hcomp hlamlow hcardS hCu
    hflo
  have hδ0 : 0 < δ := hm01.1
  have hδ1 : δ ≤ 1 := hm01.2
  have hwin := hwinL.toIsKatzTaoDividingWindow
  have hlam0 : 0 < lam := by
    have : (0 : NNReal) < (δ : NNReal) ^ ηin / 2 := by
      have := NNReal.rpow_pos (p := ηin) hδ0
      positivity
    exact lt_of_lt_of_le this hlamlow
  -- the seam
  obtain ⟨v, t₀, t₁, ht₀, ht₁, hballt₀, hballt, hballs, hcn, hcardseam, hδτ, hτθ, hθ1⟩ :
      ∃ (v : EuclideanSpace ℝ (Fin 3)) (t₀ t₁ : Finset ι),
        (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) ∧
        t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b ∧
        (a ≠ 0 → ∀ k ∈ t₀, ((𝒰.cover.tube a k).translate v).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
        (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
        (∀ i ∈ ({i ∈ S | 𝒰.cover.assign b i ∈ t₁} : Finset ι),
          ((T i).translate v).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
        (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) ∧
        (S.card : NNReal) ≤ (Mseam : NNReal) * Cu * Cu
          * ((({i ∈ S | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card : NNReal) ∧
        δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b ∧
        Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a ∧
        Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 := by
    have hMcast : ∀ n : ℕ, n ≤ Mseam → ((n : NNReal) ≤ (Mseam : NNReal)) := by
      intro n hn; exact_mod_cast Nat.cast_le.mpr hn
    rcases eq_or_ne a 0 with ha0 | ha0
    · obtain ⟨v, t₁, ht₁, hballt, hballs, hcardseam, hδτ, hτθ, hθ1⟩ :=
        hseam₁ 𝒰 hδ0 hδ1 (hdL δ hδ0 hmL.2) hwin hball
      refine ⟨v, ∅, t₁, fun h ↦ absurd ha0 h, ht₁, fun h ↦ absurd ha0 h, hballt, hballs,
        fun h ↦ absurd ha0 h, ?_, hδτ, hτθ, hθ1⟩
      refine hcardseam.trans (mul_le_mul' (mul_le_mul' (mul_le_mul'
        (hMcast M₁ (le_max_left _ _)) le_rfl) le_rfl) le_rfl)
    · obtain ⟨v, t₀, t₁, ht₀, ht₁, hballt₀, hballt, hballs, hcn, hcardseam, hδτ, hτθ, hθ1⟩ :=
        hseam₂ 𝒰 hδ0 hδ1 (Nat.one_le_iff_ne_zero.mpr ha0) (hdL δ hδ0 hmL.2) hwin hball
      refine ⟨v, t₀, t₁, fun _ ↦ ht₀, ht₁, fun _ ↦ hballt₀, hballt, hballs, fun _ ↦ hcn,
        ?_, hδτ, hτθ, hθ1⟩
      refine hcardseam.trans (mul_le_mul' (mul_le_mul' (mul_le_mul'
        (hMcast M₂ (le_max_right _ _)) le_rfl) le_rfl) le_rfl)
  -- mass positivity: one dense shade is already positive
  have hcc0E : ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal)
      : ENNReal) ≠ 0 := by
    simpa using (Tube.le_volume.c_pos (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))).ne'
  have hlam0E : ((lam : NNReal) : ENNReal) ≠ 0 := by simpa using hlam0.ne'
  -- mass positivity from the dense shading: one member, its carrier has positive volume
  have hmass0 : 0 < ∑ i ∈ S, volume (T i).shade := by
    obtain ⟨i₀, hi₀⟩ := hSne
    have hcar : volume ((T i₀).toShadedBody).carrier ≠ 0 :=
      ML2Shaded.volume_carrier_ne_zero hδ0 (T i₀).toTube
    have h1 : 0 < (lam : ENNReal) * volume ((T i₀).toShadedBody).carrier :=
      ENNReal.mul_pos hlam0E hcar
    have h2 : (lam : ENNReal) * volume ((T i₀).toShadedBody).carrier ≤ volume (T i₀).shade :=
      hdense i₀ hi₀
    exact lt_of_lt_of_le (h1.trans_le h2)
      (Finset.single_le_sum (f := fun i ↦ volume (T i).shade) (fun i _ => bot_le) hi₀)
  have hmasspos : 0 < ∑ i ∈ ({i ∈ S | 𝒰.cover.assign b i ∈ t₁} : Finset ι),
      volume (T i).shade := by
    have hret := sum_shade_le_of_node_subfamily (E := EuclideanSpace ℝ (Fin 3)) hδ1
      (Finset.filter_subset (fun i ↦ 𝒰.cover.assign b i ∈ t₁) S) hdense hcardseam
    rw [pos_iff_ne_zero]
    intro h
    rw [h, mul_zero] at hret
    have h0 : (lam : ENNReal)
        * ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal) : ENNReal)
        * (∑ i ∈ S, volume (T i).shade) = 0 := le_antisymm hret (by simp)
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hlam0E h2
      · exact hcc0E h2
    · exact hmass0.ne' h1
  -- the two-scale loss, absorbed at `κ'`
  have hσb1 : Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ 1 := le_trans hτθ hθ1
  have hCu₀8one : (1 : NNReal) ≤ Cu₀ ^ 8 := one_le_pow₀ hCu₀
  have hCu8le : Cu ^ 8 ≤ Cu₀ ^ 8 := pow_le_pow_left₀ zero_le hCu 8
  -- Three `spineScaleLoss` factors now, the third at the genuine-parent scale `ρ_p`
  --,
  -- and the cardinality constant is `Cu ^ 8` (four factors), not `Cu ^ 5`.
  have hLfinal : ∀ p : ℕ, p ≤ b → ∀ n₁ n₂ n₃ : ℕ, 0 < n₁ → 0 < n₂ → 0 < n₃ →
      (n₁ : NNReal) ≤ δ ^ (-(4 : ℝ)) → (n₂ : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      (n₃ : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₁ δ *
          ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₂
            (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
          ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₃
            (Tube.gridScale δ (Tube.ssfGridLen δ) p) : NNReal) : ENNReal)
        * ((((Cu : NNReal) ^ 8 : NNReal) : ENNReal)) ^ β ≤ (δ : ENNReal) ^ (-κ') := by
    intro p hpb n₁ n₂ n₃ hn1p hn2p hn3p hn1 hn2 hn3
    have hδρp : δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) p :=
      le_trans hδτ (Tube.gridScale_antitone hδ0 hδ1 _ hpb)
    have hρp1 : Tube.gridScale δ (Tube.ssfGridLen δ) p ≤ 1 := Tube.gridScale_le_one hδ1 _ _
    have hprod := spineScaleLoss_prod3_le hδ0 hδ1 hδτ hσb1 hδρp hρp1 hn1p hn2p hn3p hn1 hn2 hn3
      (ε := κ' / 30) (by positivity) hCε
    have hβpow : ((Cu : NNReal) ^ 8) ^ β ≤ Cu₀ ^ 8 := by
      calc ((Cu : NNReal) ^ 8) ^ β ≤ (Cu₀ ^ 8) ^ β := NNReal.rpow_le_rpow hCu8le hβ0.le
        _ ≤ (Cu₀ ^ 8) ^ (1 : ℝ) := NNReal.rpow_le_rpow_of_exponent_le hCu₀8one hβ1
        _ = Cu₀ ^ 8 := by rw [NNReal.rpow_one]
    rcases eq_or_ne ((Cu : NNReal) ^ 8) 0 with hCu8z | hCu8ne
    · rw [hCu8z]
      have hβne : β ≠ 0 := hβ0.ne'
      simp [ENNReal.zero_rpow_of_pos hβ0]
    rw [← ENNReal.coe_rpow_of_ne_zero hCu8ne, ← ENNReal.coe_mul,
      ← ENNReal.coe_rpow_of_ne_zero hδ0.ne', ENNReal.coe_le_coe]
    calc (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₁ δ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₂
              (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) n₃
              (Tube.gridScale δ (Tube.ssfGridLen δ) p))
          * (((Cu : NNReal) ^ 8) ^ β)
        ≤ (Cε ^ 3 * δ ^ (-(15 * (κ' / 30)))) * (Cu₀ ^ 8) :=
          mul_le_mul' hprod hβpow
      _ = (Cε ^ 3 * Cu₀ ^ 8) * δ ^ (-(κ' / 2)) := by
          rw [show (15 : ℝ) * (κ' / 30) = κ' / 2 by ring]; ring
      _ ≤ δ ^ (-(κ' / 2)) * δ ^ (-(κ' / 2)) := by
          gcongr
          exact le_trans (le_max_right _ _) (hd2 δ hδ0 hm2.2)
      _ = δ ^ (-κ') := by
          rw [← NNReal.rpow_add hδ0.ne']
          congr 1
          ring
  -- the pushback ledger with `u = S`: `A = lam·c`, budget `g = gt + θ₂ + η_in`
  have hδEne : (δ : ENNReal) ≠ 0 := by simpa using hδ0.ne'
  have hδEtop : (δ : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
  have hlamE : (δ : ENNReal) ^ ηin ≤ 2 * (lam : ENNReal) := by
    have hnn : (δ : NNReal) ^ ηin ≤ 2 * lam := by
      rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 2)] at hlamlow
      calc (δ : NNReal) ^ ηin ≤ lam * 2 := hlamlow
        _ = 2 * lam := by ring
    calc (δ : ENNReal) ^ ηin = (((δ : NNReal) ^ ηin : NNReal) : ENNReal) :=
          (ENNReal.coe_rpow_of_ne_zero hδ0.ne' _).symm
      _ ≤ ((2 * lam : NNReal) : ENNReal) := ENNReal.coe_le_coe.mpr hnn
      _ = 2 * (lam : ENNReal) := by push_cast; ring
  have hmassloss : (lam : ENNReal)
        * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
        * (∑ i ∈ S, volume (T i).shade)
      ≤ ((lam : ENNReal)
        * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * ∑ i ∈ S, volume (T i).shade := le_rfl
  have habs : ((lam : ENNReal)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * ((((Mseam : NNReal) * Cu * Cu : NNReal) : ENNReal)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * (δ : ENNReal) ^ (gt + θ₂ + ηin)
      ≤ ((lam : ENNReal)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * ((lam : ENNReal)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
        * (δ : ENNReal) ^ (gt) := by
    -- the constant `2·C_vol·Mseam·Cu²/c` is absorbed by `δ^{-θ₂}`
    have hKle : ((Mseam : NNReal) * Cu * Cu : NNReal) ≤ (Mseam : NNReal) * Cu₀ * Cu₀ := by
      gcongr
    have hconstNN : (2 : NNReal) * Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
          * ((Mseam : NNReal) * Cu * Cu)
        ≤ (max 1 (2 * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) *
            ((Mseam : NNReal) * Cu₀ * Cu₀) /
            (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))))
          * Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := by
      refine le_trans ?_ (mul_le_mul' (le_max_right _ _) le_rfl)
      rw [div_mul_cancel₀ _ hcc0.ne']
      gcongr
    have hconst : (2 : ENNReal)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
          * (((Mseam : NNReal) * Cu * Cu : NNReal) : ENNReal)
        ≤ (δ : ENNReal) ^ (-θ₂)
          * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) := by
      have h1 : ((2 * Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
            * ((Mseam : NNReal) * Cu * Cu) : NNReal) : ENNReal)
          ≤ (((max 1 (2 * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) *
              ((Mseam : NNReal) * Cu₀ * Cu₀) /
              (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))))
            * Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
              : NNReal) : ENNReal) := ENNReal.coe_le_coe.mpr hconstNN
      have h2 := hd1 δ hδ0 hm1.2
      push_cast at h1 ⊢
      exact h1.trans (mul_le_mul' h2 le_rfl)
    -- `2·C_vol·K·δ^{θ₂} ≤ c`, then `δ^{η_in} ≤ 2·lam`
    have e : (δ : ENNReal) ^ (-θ₂) * (δ : ENNReal) ^ θ₂ = 1 := by
      rw [← ENNReal.rpow_add _ _ hδEne hδEtop, neg_add_cancel, ENNReal.rpow_zero]
    have h2K : (2 : ENNReal)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
          * (((Mseam : NNReal) * Cu * Cu : NNReal) : ENNReal) * (δ : ENNReal) ^ θ₂
        ≤ (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) := by
      calc (2 : ENNReal)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
            * (((Mseam : NNReal) * Cu * Cu : NNReal) : ENNReal) * (δ : ENNReal) ^ θ₂
          ≤ ((δ : ENNReal) ^ (-θ₂)
              * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
              * (δ : ENNReal) ^ θ₂ := mul_le_mul' hconst le_rfl
        _ = (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
              * ((δ : ENNReal) ^ (-θ₂) * (δ : ENNReal) ^ θ₂) := by ring
        _ = (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) := by
              rw [e, mul_one]
    have hstep : (((Mseam : NNReal) * Cu * Cu : NNReal) : ENNReal)
          * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
          * (δ : ENNReal) ^ θ₂ * (δ : ENNReal) ^ ηin
        ≤ (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
          * (lam : ENNReal) := by
      calc (((Mseam : NNReal) * Cu * Cu : NNReal) : ENNReal)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
            * (δ : ENNReal) ^ θ₂ * (δ : ENNReal) ^ ηin
          ≤ (((Mseam : NNReal) * Cu * Cu : NNReal) : ENNReal)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
            * (δ : ENNReal) ^ θ₂ * (2 * (lam : ENNReal)) := mul_le_mul' le_rfl hlamE
        _ = ((2 : ENNReal)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
            * (((Mseam : NNReal) * Cu * Cu : NNReal) : ENNReal) * (δ : ENNReal) ^ θ₂)
            * (lam : ENNReal) := by ring
        _ ≤ (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
            * (lam : ENNReal) := mul_le_mul' h2K le_rfl
    have esplit : (δ : ENNReal) ^ (gt + θ₂ + ηin)
        = (δ : ENNReal) ^ (gt) * (δ : ENNReal) ^ θ₂
          * (δ : ENNReal) ^ ηin := by
      rw [ENNReal.rpow_add _ _ hδEne hδEtop, ENNReal.rpow_add _ _ hδEne hδEtop]
    calc ((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * ((((Mseam : NNReal) * Cu * Cu : NNReal) : ENNReal)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * (δ : ENNReal) ^ (gt + θ₂ + ηin)
        = (((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
            * (δ : ENNReal) ^ (gt))
          * ((((Mseam : NNReal) * Cu * Cu : NNReal) : ENNReal)
            * (Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
            * (δ : ENNReal) ^ θ₂ * (δ : ENNReal) ^ ηin) := by
          rw [esplit]; ring
      _ ≤ (((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
            * (δ : ENNReal) ^ (gt))
          * ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
            * (lam : ENNReal)) := mul_le_mul' le_rfl hstep
      _ = ((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * ((lam : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal))
          * (δ : ENNReal) ^ (gt) := by ring
  -- the numeric inputs of the factor interface
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
  let P := sourceTerminalParent β ϖ ε₁ rawGain rawDens m
  let net := sourceTerminalNetGain β ϖ ε₁ rawGain rawDens m
  have hexp : gt + θ₂ + ηin ≤ net - acc.epsf m - acc.epsp m -
      (acc.epsc m + ML2Spine.spineRung β ϖ ε₁ gain dens m) - κ' := by
    have hb := hlate.budget m hm
    change _ ≤ net at hb
    dsimp [gt, θ₂, κ']
    linarith only [hb]
  have main (p : ℕ) (hap : a ≤ p) (hpb : p < b)
      (hpm : ∀ k ∈ sourceWindowLevels δ (ML2Spine.spineDiv ϖ ε₁) a b, p < k)
      (hpar : ∀ jθ ∈ 𝒰.cover.indexSet a,
        Kakeya.maxDensity (𝒰.nodesUnder p a jθ)
          (fun j => (𝒰.cover.tube p j).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-(2 * P)))
      (hfloor : ∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ,
        ∀ k ∈ sourceWindowLevels δ (ML2Spine.spineDiv ϖ ε₁) a b, p < k →
          ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ))
              ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
                ≤ ((𝒰.nodesUnder k p jp).card : ℝ)) :
      ∑ i ∈ S, volume (T i).shade ≤
        (δ : ENNReal) ^ gt * (S.card : ENNReal) ^ β * volume (⋃ i ∈ S, (T i).shade) := by
    obtain ⟨tτ', tp', tθ', Yτ', Yp, Yθ, Y', jτ, jp, jθ,
      htτ', htp', htθ', hjτ, hjθ, htτ'ne, htp'ne, hprod, hf, hmid, hpar', hc⟩ :=
      hfacδ m hm S T Cu lam 𝒰 ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) a b
        hwinL v t₀ t₁ ht₁ hballt hballs ht₀ hcn hballt₀ hball hSne hmaxS hdense
        hcomp hlamlow hcardS hCstarB hCu hmasspos hδτ hτθ hθ1 p hap hpb.le hpm hpar hfloor
    exact sum_shade_gain_of_window_four (β := β) hβ0.le hδ0 hδ1 hlam0
      (Finset.Subset.refl S) hdense 𝒰 hwin hap hpb.le ht₁ hcardseam hmasspos
      (εf := acc.epsf m) (gm := net) (εp := acc.epsp m)
      (εc := acc.epsc m + ML2Spine.spineRung β ϖ ε₁ gain dens m) (κ := κ')
      (g := gt + θ₂ + ηin) (gt := gt) hcardS
      ⟨tτ', tp', tθ', Yτ', Yp, Yθ, Y', jτ, jp, jθ, htτ', htp', htθ',
        hjτ, hjθ, htτ'ne, htp'ne, hprod hpb, hf, hmid hpb, hpar', hc⟩
      (hLfinal p hpb.le) hexp hmassloss habs
  obtain ⟨p₀, hap₀, hpm₀, hpar₀, hflo₀⟩ := hflo
  by_cases hpb : p₀ < b
  · apply main p₀ hap₀ hpb
    · intro k hk
      obtain ⟨hak, hkb, hlo, hhi⟩ := (source_mem_windowLevels_iff _ _ _ _ _).mp hk
      exact hpm₀ k hak hkb hlo hhi
    · exact hpar₀
    · intro jθ hjθ jp hjp k hk hpk
      obtain ⟨hak, hkb, hlo, hhi⟩ := (source_mem_windowLevels_iff _ _ _ _ _).mp hk
      exact hflo₀ jθ hjθ jp hjp k hak hkb hlo hhi hpk
  · have hempty (k : ℕ) (hk : k ∈ sourceWindowLevels δ (ML2Spine.spineDiv ϖ ε₁) a b) : False := by
      obtain ⟨hak, hkb, hlo, hhi⟩ := (source_mem_windowLevels_iff _ _ _ _ _).mp hk
      have hpk := hpm₀ k hak hkb hlo hhi
      omega
    apply main a le_rfl hwin.coarse_lt_fine
    · exact fun k hk => (hempty k hk).elim
    · intro jθ hjθ
      have hηm : 0 ≤ ML2Spine.spineRung β ϖ ε₁ gain dens m := (hsp.rung_pos m).le
      have hpow : ENNReal.ofReal
          ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            ^ (-ML2Spine.spineRung β ϖ ε₁ gain dens m)) ≤
          (δ : ENNReal) ^ (-ML2Spine.spineRung β ϖ ε₁ gain dens m) := by
        rw [← ML2Reduction.ofReal_rpow_coe hδ0]
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hδ0)
          (by exact_mod_cast hδτ.trans hτθ) (neg_nonpos.mpr hηm)
      have hres : κc + ML2Spine.spineRung β ϖ ε₁ gain dens m ≤ 2 * P :=
        hlate.residual m hm
      calc Kakeya.maxDensity (𝒰.nodesUnder a a jθ)
              (fun j => (𝒰.cover.tube a j).toConvexSpaceBody)
          ≤ Kakeya.maxDensity (𝒰.cover.indexSet a)
            (fun j => (𝒰.cover.tube a j).toConvexSpaceBody) :=
          Kakeya.maxDensity_mono _ (Finset.filter_subset _ _)
        _ ≤ ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) *
            ENNReal.ofReal ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
              ^ (-ML2Spine.spineRung β ϖ ε₁ gain dens m)) := hwin.coarse_maxDensity_le
        _ ≤ (δ : ENNReal) ^ (-κc) *
            (δ : ENNReal) ^ (-ML2Spine.spineRung β ϖ ε₁ gain dens m) :=
          mul_le_mul' hCstarB hpow
        _ = (δ : ENNReal) ^ (-(κc + ML2Spine.spineRung β ϖ ε₁ gain dens m)) := by
          rw [← ENNReal.rpow_add _ _ hδEne hδEtop]
          congr 1
          ring
        _ ≤ (δ : ENNReal) ^ (-(2 * P)) :=
          ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1) (neg_le_neg hres)
    · exact fun jθ _ jp _ k hk _ => (hempty k hk).elim

open Classical in
/-- At the ambient hierarchy, the same refinement consumes R0 and returns the trial's
middle alternative. The potential scale and terminal gain remain explicit parameters. -/
theorem source_trialOutcome_finite_refined
    {β ϖ ε₁ s ηL ηin η aL : ℝ} {rawGain rawDens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hε₁ : 0 < ε₁)
    (hp : Lemma91ParamsAt.{u} β ϖ rawGain rawDens)
    {acc : SourceLocalAccuracyData} {H : Finset ℝ}
    (hbudget : SourceLocalBudget β ϖ ε₁ rawGain rawDens s acc)
    (hlate : SourceLateInputBounds β ϖ ε₁ rawGain rawDens s acc H ηL ηin η aL)
    {C Cu₀ : NNReal} {Kl cl : ℕ} (hC : 1 ≤ C) (hCu₀ : 1 ≤ Cu₀)
    (hfac : SourceFiniteHfac.{u} β ϖ ε₁ ηin rawGain rawDens acc Cu₀)
    (Λf : NNReal → ENNReal) {hSrc g : ℝ}
    (hg : g ≤ 6 * ML2Spine.spineNu β ϖ ε₁
      (sourceChoiceGain β rawGain rawDens) (sourceChoiceDens β rawDens)) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu : NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (a b m : ℕ), m < ML2Spine.spineCount ϖ ε₁ →
      ∀ (S : Finset ι) (hS : S ⊆ u)
        (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (lam : NNReal),
        S.Nonempty → ∀ ht : ∀ i, (Z i).toTube = (T i).toTube,
        (∀ i, (Z i).shade ⊆ (T i).shade) →
        ∀ hh : IsClassHomogeneousOn 𝒰 S,
        (∀ i ∈ S, (Z i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam S (fun i => (Z i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ S (fun i => (Z i).toShadedBody) →
        (δ : NNReal) ^ ηin / 2 ≤ lam →
        (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) → Cu ≤ Cu₀ →
        Λf δ * (δ : ENNReal) ^ acc.reserve ≤ 1 →
        @RefinedFloorHypothesis ι δ Cu β ϖ ε₁
          (sourceChoiceGain β rawGain rawDens) (sourceChoiceDens β rawDens)
          (sourceTerminalParent β ϖ ε₁ rawGain rawDens m) C Kl cl (Λf δ) S Z
          ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m →
        ∀ (ε₀ : ℝ) (Λ : ENNReal), TrialOutcomeAtGain hSrc ε₀ g β 𝒰 Λ lam S Z := by
  let gain := sourceChoiceGain β rawGain rawDens
  let dens := sourceChoiceDens β rawDens
  let c := ML2Spine.spineNu β ϖ ε₁ gain dens
  let gt := 6 * c + acc.reserve
  filter_upwards [source_sum_shade_le_finite_floor hβ0 hβ1 hε₁ hp hbudget hlate
    hC hCu₀ (Kl := Kl) (cl := cl) hfac, Ioc_mem_nhdsGT (zero_lt_one' NNReal)]
    with δ hδ hδ01
  intro ι u T Cu 𝒰 a b m hm S hS Z lam hSne ht hs hh hball hmaxS hdense
    hcomp hlamlow hcardu hCu hpay href ε₀ Λ
  let 𝒰₁ : Tube.UniformTubeSet S (fun i => (Z i).toTube) (Tube.ssfGridLen δ) Cu :=
    (𝒰.restrictOccupied hS hh).retube (funext ht)
  have hcardS : (S.card : NNReal) ≤ δ ^ (-(4 : ℝ)) := by
    have h1 : (S.card : ℝ) ≤ (u.card : ℝ) := by exact_mod_cast Finset.card_le_card hS
    have h2 : ((S.card : NNReal) : ℝ) ≤ ((δ ^ (-(4 : ℝ)) : NNReal) : ℝ) := by
      rw [NNReal.coe_rpow, NNReal.coe_natCast]
      exact h1.trans hcardu
    exact_mod_cast h2
  obtain ⟨S', W, hS', hhom, hW, hrefine, hwin', hflo'⟩ := href
  have hwin'' : ML2Reduction.IsKatzTaoDividingWindowLevels (𝒰₁.restrictOccupied hS' hhom)
      ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) (ML2Spine.spineRung β ϖ ε₁ gain dens)
      (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m :=
    isKatzTaoDividingWindowLevels_of_retube hW _ hwin'
  have hflo'' : FloorHypothesisAt β ϖ ε₁ gain dens
      (sourceTerminalParent β ϖ ε₁ rawGain rawDens m) (𝒰₁.restrictOccupied hS' hhom) a b m := hflo'
  have hball' : ∀ i ∈ S', (Z i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun i hi => hball i (hS' hi)
  have hmaxS' : Kakeya.maxDensity S' (fun i => (Z i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) :=
    (Kakeya.maxDensity_mono _ hS').trans hmaxS
  have hcardS' : (S'.card : NNReal) ≤ δ ^ (-(4 : ℝ)) :=
    le_trans (by exact_mod_cast Finset.card_le_card hS') hcardS
  have hbound := hδ S' Z Cu lam (𝒰₁.restrictOccupied hS' hhom) a b m hm hwin''
    hball' hrefine.nonempty hmaxS' (hdense.subset hS') (hcomp.subset hS')
    hlamlow hcardS' hCu hflo''
  have hcard : (S'.card : ENNReal) ^ β ≤ (S.card : ENNReal) ^ β :=
    ENNReal.rpow_le_rpow (by exact_mod_cast Finset.card_le_card hS') hβ0.le
  have hvol : volume (⋃ i ∈ S', (Z i).shade) ≤ volume (⋃ i ∈ S, (Z i).shade) :=
    measure_mono (Set.iUnion₂_subset fun i hi =>
      Set.subset_biUnion_of_mem (u := fun i => (Z i).shade) (hS' hi))
  have hsum : ∑ i ∈ S', volume (W i).shade ≤ ∑ i ∈ S', volume (Z i).shade :=
    Finset.sum_le_sum (fun i _ => measure_mono (hrefine.shade_subset i))
  have hδ0 : (δ : ENNReal) ≠ 0 := by simpa using hδ01.1.ne'
  have hΛf : Λf δ * (δ : ENNReal) ^ gt ≤ (δ : ENNReal) ^ g := by
    calc Λf δ * (δ : ENNReal) ^ gt =
        (Λf δ * (δ : ENNReal) ^ acc.reserve) * (δ : ENNReal) ^ (6 * c) := by
          dsimp [gt]
          rw [ENNReal.rpow_add _ _ hδ0 ENNReal.coe_ne_top]
          ring
      _ ≤ 1 * (δ : ENNReal) ^ (6 * c) := mul_le_mul' hpay le_rfl
      _ = (δ : ENNReal) ^ (6 * c) := one_mul _
      _ ≤ (δ : ENNReal) ^ g :=
        ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ01.2) hg
  unfold TrialOutcomeAtGain
  apply Or.inr ∘ Or.inl
  calc ∑ i ∈ S, volume (Z i).shade
      ≤ Λf δ * ∑ i ∈ S', volume (W i).shade := hrefine.retention
    _ ≤ Λf δ * ∑ i ∈ S', volume (Z i).shade := mul_le_mul' le_rfl hsum
    _ ≤ Λf δ * ((δ : ENNReal) ^ gt * (S'.card : ENNReal) ^ β *
        volume (⋃ i ∈ S', (Z i).shade)) := mul_le_mul' le_rfl hbound
    _ ≤ Λf δ * ((δ : ENNReal) ^ gt * (S.card : ENNReal) ^ β *
        volume (⋃ i ∈ S, (Z i).shade)) :=
      mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl hcard) hvol)
    _ = (Λf δ * (δ : ENNReal) ^ gt) *
        ((S.card : ENNReal) ^ β * volume (⋃ i ∈ S, (Z i).shade)) := by ring
    _ ≤ (δ : ENNReal) ^ g * ((S.card : ENNReal) ^ β * volume (⋃ i ∈ S, (Z i).shade)) :=
      mul_le_mul' hΛf le_rfl
    _ = (δ : ENNReal) ^ g * (S.card : ENNReal) ^ β * volume (⋃ i ∈ S, (Z i).shade) := by ring

section TopCell

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open Classical in
/-- The bounded top family pays its actual cardinality constant; no singleton premise occurs. -/
theorem source_outer_factor_at_zero {β c : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {t : Finset ι} (ht : t ⊆ 𝒰.cover.indexSet 0)
    (Y : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) 0)
      (EuclideanSpace ℝ (Fin 3)))
    (hpay : (Cu : ENNReal) ^ (1 - β) ≤ (δ : ENNReal) ^ (-c)) :
    ((𝒰.cover.indexSet 0).card : NNReal) ≤ Cu ∧
    ShadedBody.multiplicity t (fun i => (Y i).toShadedBody)
      ≤ (δ : ENNReal) ^ (-c) * (t.card : ENNReal) ^ β := by
  have hcard := card_indexSet_zero_le 𝒰 hs hball
  refine ⟨hcard, ?_⟩
  have htcard : (t.card : ENNReal) ≤ (Cu : ENNReal) := by
    exact_mod_cast (show (t.card : NNReal) ≤ Cu from
      (by exact_mod_cast Finset.card_le_card ht : (t.card : NNReal) ≤
        ((𝒰.cover.indexSet 0).card : NNReal)).trans hcard)
  exact (multiplicity_le_of_card_le hβ1 htcard).trans (mul_le_mul' hpay le_rfl)

open Classical in
/-- At p = a = 0 the parent fibre uses its bounded count, at radius one. -/
theorem source_parent_factor_at_zero {β εp : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {tp : Finset ι} (htp : tp ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain 0)
    (Yp : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) 0)
      (EuclideanSpace ℝ (Fin 3))) (jθ : ι)
    (hpay : (Cu : ENNReal) ^ (1 - β) ≤ (δ : ENNReal) ^ (-εp)) :
    ShadedBody.multiplicity
      ({k ∈ tp | ML2Reduction.coarseNode 𝒰.cover.toChain 0 0 k = jθ} : Finset ι)
      (fun k => (Yp k).toShadedBody)
      ≤ (δ : ENNReal) ^ (-εp) *
        (({k ∈ tp | ML2Reduction.coarseNode 𝒰.cover.toChain 0 0 k = jθ}
          : Finset ι).card : ENNReal) ^ β := by
  exact (source_outer_factor_at_zero hβ0 hβ1 𝒰 hs hball
    (fun k hk => ML2Reduction.activeNodes_subset 𝒰.cover.toChain 0
      (htp (Finset.mem_filter.mp hk).1)) Yp hpay).2

end TopCell

/-- One tail pays the two bounded-cardinality endpoint constants at every actual rung. -/
theorem source_eventually_top_cell_payments
    {β ϖ ε₁ s : ℝ} {rawGain rawDens : ℝ → ℝ} {acc : SourceLocalAccuracyData}
    (hβ1 : β ≤ 1)
    (hbudget : SourceLocalBudget β ϖ ε₁ rawGain rawDens s acc)
    {Cu₀ : NNReal} (hCu₀ : 1 ≤ Cu₀) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ Cu : NNReal, Cu ≤ Cu₀ →
      ∀ m : ℕ, m < ML2Spine.spineCount ϖ ε₁ →
        (Cu : ENNReal) ^ (1 - β) ≤ (δ : ENNReal) ^ (-(acc.epsOuter m)) ∧
        (Cu : ENNReal) ^ (1 - β) ≤ (δ : ENNReal) ^ (-(acc.epsp m)) := by
  have hrow (m : ℕ) (hm : m ∈ Finset.range (ML2Spine.spineCount ϖ ε₁)) :
      ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ Cu : NNReal, Cu ≤ Cu₀ →
        (Cu : ENNReal) ^ (1 - β) ≤ (δ : ENNReal) ^ (-(acc.epsOuter m)) ∧
        (Cu : ENNReal) ^ (1 - β) ≤ (δ : ENNReal) ^ (-(acc.epsp m)) := by
    have hm' := Finset.mem_range.mp hm
    have he : 0 < min (acc.epsOuter m) (acc.epsp m) :=
      lt_min (hbudget.outer_accuracy_pos m) (hbudget.parent_charge_pos m hm')
    obtain ⟨d, hd0, hd⟩ := ML2Reduction.exists_threshold_coe_const_le_rpow_neg
      (C := max 1 (Cu₀ ^ (1 - β))) (le_max_left _ _) he
    filter_upwards [Ioc_mem_nhdsGT hd0, Ioc_mem_nhdsGT (zero_lt_one' NNReal)]
      with δ hδ hδ1
    intro Cu hCu
    have hbase : (Cu : ENNReal) ^ (1 - β) ≤
        (δ : ENNReal) ^ (-min (acc.epsOuter m) (acc.epsp m)) := by
      calc (Cu : ENNReal) ^ (1 - β) ≤ (Cu₀ : ENNReal) ^ (1 - β) :=
          ENNReal.rpow_le_rpow (by exact_mod_cast hCu) (sub_nonneg.mpr hβ1)
        _ = ((Cu₀ ^ (1 - β) : NNReal) : ENNReal) :=
          (ENNReal.coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hCu₀)) _).symm
        _ ≤ ((max 1 (Cu₀ ^ (1 - β)) : NNReal) : ENNReal) :=
          ENNReal.coe_le_coe.mpr (le_max_right _ _)
        _ ≤ (δ : ENNReal) ^ (-min (acc.epsOuter m) (acc.epsp m)) := hd δ hδ.1 hδ.2
    exact ⟨hbase.trans (ENNReal.rpow_le_rpow_of_exponent_ge
      (by exact_mod_cast hδ1.2) (neg_le_neg (min_le_left _ _))),
      hbase.trans (ENNReal.rpow_le_rpow_of_exponent_ge
      (by exact_mod_cast hδ1.2) (neg_le_neg (min_le_right _ _)))⟩
  filter_upwards [(Filter.eventually_all_finset
    (Finset.range (ML2Spine.spineCount ϖ ε₁))).2 hrow] with δ hδ
  exact fun Cu hCu m hm => hδ m (Finset.mem_range.mpr hm) Cu hCu

/-- The complete coarse API with its fixed top-cardinality payment explicit. -/
theorem source_exists_coarse_factor_complete {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hKT : Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ᶠ δ : NNReal in 𝓝[>] 0,
      ∀ {Cu : NNReal} {ι : Type u} {s : Finset ι}
        {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}
        {𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu}
        {Cstar : ENNReal} {ηl : ℕ → ℝ} {εd : ℝ} {N a b m : ℕ}
        {κ c : ℝ} {t : Finset ι}
        {Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
          (EuclideanSpace ℝ (Fin 3))} {v : EuclideanSpace ℝ (Fin 3)},
        0 < δ → δ ≤ 1 → s.Nonempty →
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar ηl εd N a b m →
        0 ≤ ηl m → 0 ≤ κ → Cstar ≤ (δ : ENNReal) ^ (-κ) →
        ε + (κ + ηl m) ≤ c →
        (Cu : ENNReal) ^ (1 - β) ≤ (δ : ENNReal) ^ (-c) →
        t ⊆ 𝒰.cover.indexSet a →
        (∀ k, (Yθ k).toTube = (𝒰.cover.tube a k).translate v) →
        (a ≠ 0 → ∀ k ∈ t, (Yθ k).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        (δ : NNReal) ^ η ≤ ShadedBody.fullness t (fun k => (Yθ k).toShadedBody) →
        ShadedBody.multiplicity t (fun k => (Yθ k).toShadedBody)
          ≤ (δ : ENNReal) ^ (-c) * (t.card : ENNReal) ^ β := by
  exact exists_coarse_factor_complete hβ0 hβ1 hKT hε

end Kakeya.ML2Core
