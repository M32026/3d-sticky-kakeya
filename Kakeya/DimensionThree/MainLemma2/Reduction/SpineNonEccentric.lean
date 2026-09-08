/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimates
public import Kakeya.FrostmanConstant
public import Kakeya.MultiScaleSubmult
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParams
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineInheritance

/-!
# The non-eccentric case of the reduction of GWZ Main Lemma 2

Blueprint: `blueprint/src/GWZAdapted/section9.tex`, the paragraph headed
**The non-eccentric case** inside the proof of Main Lemma 2.  The step numbering below is the
one used in the blueprint's own equation labels.

Setting: `𝕋̃` is the rescaled family of `τ/θ`-tubes, `δ̃` its thickness, `ρ = δ̃^{1-ε₂}`, `𝕍` the
maximal-density factoring of `𝕋̃_ρ` into planks of affine thicknesses `1 × b × a` with
`b ≤ δ̃^{-η'_{j-1}} a`, and `𝕋̃_b` the family of `b`-tubes obtained from `𝕍`.

## What this file contains

* **Step 3** (`upperBdDeltaMaxTb`): `Δ_max(𝕋̃_b) ≤ (|T_b|/|V|) Δ_max(𝕍) ≤ δ̃^{-η'_{j-1}}`.
  Abstract core `maxDensity_le_of_nested_inj`.
* **Step 4** (`boundOnMuTTb`): `exists_multiplicity_coarse_bound`, GWZ `genKKT`
  (`Kakeya.KatzTaoEstimate.multiplicity_bound`) read at a coarse scale `dt ≤ b`.
* **Step 5**: `le_of_maxDensity_le_window` and its spine-driven form
  `spine_le_of_maxDensity_le_window` — comparing step 3 with `tildeDeltaLargeDeltamax`
  forces `b ≥ δ̃^{ε₂}`.
* **Step 6** (`goodFrostmanBoundTTRhoInsideTb`): `C_F(𝕋̃_ρ, T_b) ≲ δ^{-η'_{j-1}}`.  Abstract
  core `isFrostmanIn_of_maxDensity_le_densityIn`.  The extension to all `σ ∈ [ρ, b]` is
  `Kakeya.ML2Spine.exists_subset_isFrostmanIn_parents'` in `SpineInheritance.lean`.
* **Step 7** (`lowerBdOnDeltaMaxTTSigmaTb`): `rpow_mul_le_mul_fibre_maxDensity`, GWZ Lemma 7.4
  (`Kakeya.MultiScaleSubmult.maxDensity_le_prod_fibreDeltaMax`) read downwards.
  `exists_parent_fibre_eq_fibreDeltaMax` licenses choosing `T_b` to be a maximising fibre.
* **Step 8** (`TTSigmaBigCardinalityV1`): `tube_card_lower`, `card_lower_of_nnreal_bound` and
  `tube_rescaled_card_lower`, the last delivering the count hypothesis
  `(σ/b)^{-2-ζ} ≤ |𝕋̃_σ[T_b]|` of Lemma 9.1 in dimension `3`.  The single arithmetic threshold
  is discharged by `countThreshold_of_small` / `spine_countThreshold`, whose gap comes from
  `spine_countGap`.  `spine_tube_card_lower` is the single entry point that composes all of
  steps 3, 6, 7 and 8 against `IsSpine`.
* **Step 11** (`multTildeTLem2`): `multiplicity_le_of_two_factors` multiplies the two
  multiplicity bounds; `spine_gainBudget` and `spine_gainBudget_of_loss` verify the exponent
  inequality `ν(β, η_j/2) - 2η'_{j-1} ≥ 10 η_{j-1}/ε₂` from `IsSpine.gain_budget`.

## What this file does not contain

**Step 10** (`boundOnMuTildeTTb`) — the actual application of Lemma 9.1
(`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`) to the family rescaled by
`Kakeya.ML2Reduction.spineRescaleUnit`, and the transport of its conclusion back.  That needs
the rescaled family to be presented as a genuine `Tube δ'` family with a uniformity witness,
which is assembly-level work; the transport toolkit is `SpineRescale.lean`.

The parameter arithmetic is never re-derived here: everything goes through the fields of
`Kakeya.ML2Spine.IsSpine` (`SpineParams.lean`), and no numeric value of `ε₂`, `e` or `N` is
hard-coded.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Spine

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Step 3 -/

/-- **Coarse density from a nested subfamily.** -/
theorem maxDensity_le_of_nested_inj {ι κ : Type*} [DecidableEq ι]
    {t : Finset κ} {W : κ → ConvexSpaceBody E} {u : Finset ι} {V : ι → ConvexSpaceBody E}
    {f : κ → ι} {cW cV D : ENNReal}
    (hfinj : ∀ j ∈ t, ∀ j' ∈ t, f j = f j' → j = j')
    (hfu : ∀ j ∈ t, f j ∈ u)
    (hVW : ∀ j ∈ t, V (f j) ≤ W j)
    (hWvol : ∀ j ∈ t, volume (W j).carrier ≤ cW)
    (hVvol : ∀ j ∈ t, cV ≤ volume (V (f j)).carrier)
    (hcV : cV ≠ 0) (hcVtop : cV ≠ ⊤)
    (hD : cW * maxDensity u V ≤ D * cV) :
    maxDensity t W ≤ D := by
  classical
  rw [maxDensity_le_iff]
  intro K
  rw [densityIn_le_iff]
  -- abbreviate the filtered index set
  set A : Finset κ := {j ∈ t | W j ≤ K} with hA
  have hAt : A ⊆ t := Finset.filter_subset _ _
  -- (1)  ∑_{j ∈ A} |W j| ≤ cW * |A|
  have h1 : ∑ j ∈ A, volume (W j).carrier ≤ (A.card : ENNReal) * cW := by
    calc ∑ j ∈ A, volume (W j).carrier ≤ ∑ _j ∈ A, cW :=
          Finset.sum_le_sum fun j hj => hWvol j (hAt hj)
      _ = (A.card : ENNReal) * cW := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- (2)  cV * |A| ≤ ∑_{i ∈ u, V i ≤ K} |V i|
  have h2 : (A.card : ENNReal) * cV ≤ ∑ i ∈ {i ∈ u | V i ≤ K}, volume (V i).carrier := by
    have hmap : A.image f ⊆ {i ∈ u | V i ≤ K} := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      have hjt : j ∈ t := hAt hj
      have hjK : W j ≤ K := (Finset.mem_filter.mp hj).2
      exact Finset.mem_filter.mpr ⟨hfu j hjt, (hVW j hjt).trans hjK⟩
    have hcard : A.card = (A.image f).card :=
      (Finset.card_image_of_injOn fun j hj j' hj' h => hfinj j (hAt hj) j' (hAt hj') h).symm
    calc (A.card : ENNReal) * cV
        = ∑ _i ∈ A.image f, cV := by rw [Finset.sum_const, nsmul_eq_mul, ← hcard]
      _ ≤ ∑ i ∈ A.image f, volume (V i).carrier := by
          refine Finset.sum_le_sum fun i hi => ?_
          rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
          exact hVvol j (hAt hj)
      _ ≤ ∑ i ∈ {i ∈ u | V i ≤ K}, volume (V i).carrier :=
          Finset.sum_le_sum_of_subset hmap
  -- (3)  the right-hand sum is ≤ maxDensity u V * |K|
  have h3 : ∑ i ∈ {i ∈ u | V i ≤ K}, volume (V i).carrier ≤ maxDensity u V * volume K.carrier := by
    rw [sum_volume_eq_densityIn_mul_volume]
    gcongr
    exact le_maxDensity u V K
  -- assemble
  have key : (∑ j ∈ A, volume (W j).carrier) * cV ≤ (D * volume K.carrier) * cV := by
    calc (∑ j ∈ A, volume (W j).carrier) * cV ≤ ((A.card : ENNReal) * cW) * cV := by gcongr
      _ = cW * ((A.card : ENNReal) * cV) := by ring
      _ ≤ cW * (maxDensity u V * volume K.carrier) := mul_le_mul_right (h2.trans h3) cW
      _ = (cW * maxDensity u V) * volume K.carrier := by ring
      _ ≤ (D * cV) * volume K.carrier := by gcongr
      _ = (D * volume K.carrier) * cV := by ring
  exact (ENNReal.mul_le_mul_iff_left hcV hcVtop).mp key

/-! ### Step 6 -/

/-- **Step 6a.** -/
theorem isFrostmanIn_of_maxDensity_le_densityIn {ι : Type*} {s : Finset ι}
    {W : ι → ConvexSpaceBody E} {V Tb : ConvexSpaceBody E} {Cv C : ENNReal}
    (hVT : V ≤ Tb)
    (hmax : maxDensity s W ≤ Cv * densityIn s W V)
    (hvol : Cv * volume Tb.carrier ≤ C * volume V.carrier)
    (hV0 : volume V.carrier ≠ 0) (hVtop : volume V.carrier ≠ ⊤) :
    IsFrostmanIn s W Tb C := by
  intro K' _
  refine (le_maxDensity s W K').trans (hmax.trans ?_)
  have key : (Cv * densityIn s W V) * volume V.carrier
      ≤ (C * densityIn s W Tb) * volume V.carrier := by
    calc (Cv * densityIn s W V) * volume V.carrier
        = Cv * (densityIn s W V * volume V.carrier) := by ring
      _ ≤ Cv * (densityIn s W Tb * volume Tb.carrier) :=
          mul_le_mul_right (densityIn_mul_volume_le_of_le hVT) Cv
      _ = densityIn s W Tb * (Cv * volume Tb.carrier) := by ring
      _ ≤ densityIn s W Tb * (C * volume V.carrier) := mul_le_mul_right hvol _
      _ = (C * densityIn s W Tb) * volume V.carrier := by ring
  exact (ENNReal.mul_le_mul_iff_left hV0 hVtop).mp key

/-! ### Step 8 -/

/-- **Step 8, core form.** -/
theorem maxDensity_mul_volume_le_of_isFrostmanIn {ι : Type*} {s : Finset ι}
    {W : ι → ConvexSpaceBody E} {Tb : ConvexSpaceBody E} {CF M cs : ENNReal}
    (hne : ∃ i ∈ s, 0 < volume (W i).carrier)
    (hsub : ∀ i ∈ s, W i ≤ Tb)
    (hF : IsFrostmanIn s W Tb CF)
    (hM : M ≤ maxDensity s W)
    (hvol : ∀ i ∈ s, volume (W i).carrier ≤ cs) :
    M * volume Tb.carrier ≤ CF * ((s.card : ENNReal) * cs) := by
  classical
  obtain ⟨u, -, -, hu_eq, hu_le⟩ := exists_convexHullBiUnion_densityIn_eq_maxDensity hne
  have hK0 : u.convexHull_biUnion W ≤ Tb := hu_le Tb hsub
  have hstep : M ≤ CF * densityIn s W Tb := by
    refine hM.trans ?_
    rw [← hu_eq]
    exact hF _ hK0
  calc M * volume Tb.carrier ≤ (CF * densityIn s W Tb) * volume Tb.carrier := by gcongr
    _ = CF * (densityIn s W Tb * volume Tb.carrier) := by ring
    _ = CF * ∑ i ∈ s, volume (W i).carrier := by
        rw [← sum_volume_eq_densityIn_mul_volume' hsub]
    _ ≤ CF * ((s.card : ENNReal) * cs) := by
        refine mul_le_mul_right ?_ CF
        calc ∑ i ∈ s, volume (W i).carrier ≤ ∑ _i ∈ s, cs := Finset.sum_le_sum hvol
          _ = (s.card : ENNReal) * cs := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### Step 5 -/

/-- Cancelling a common negative exponent. -/
theorem le_of_rpow_neg_le {x y : ENNReal} {η : ℝ} (hη : 0 < η)
    (h : x ^ (-η) ≤ y ^ (-η)) : y ≤ x := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg] at h
  have h' : y ^ η ≤ x ^ η := by
    simpa using ENNReal.inv_le_inv.mp h
  exact (ENNReal.rpow_le_rpow_iff hη).mp h'

/-- **Step 5.** -/
theorem le_of_maxDensity_le_window
    {δ b : NNReal} {ε₂ ηj η' : ℝ} {Δb : ENNReal}
    (hδ0 : δ ≠ 0) (hδ1 : δ ≤ 1) (hηj : 0 < ηj)
    (hη' : η' ≤ ηj * ε₂)
    (hwin : b ≤ δ ^ ε₂ → (b : ENNReal) ^ (-ηj) ≤ Δb)
    (hup : Δb ≤ (δ : ENNReal) ^ (-η')) :
    δ ^ ε₂ ≤ b := by
  by_cases hc : b ≤ δ ^ ε₂
  · have h1 : (b : ENNReal) ^ (-ηj) ≤ (δ : ENNReal) ^ (-η') := (hwin hc).trans hup
    have hδ1' : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
    have h2 : (δ : ENNReal) ^ (-η') ≤ (δ : ENNReal) ^ (-(ηj * ε₂)) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδ1' (by linarith)
    have h3 : (δ : ENNReal) ^ (-(ηj * ε₂)) = (((δ ^ ε₂ : NNReal) : ENNReal)) ^ (-ηj) := by
      rw [ENNReal.coe_rpow_of_ne_zero hδ0, ← ENNReal.rpow_mul]
      ring_nf
    rw [h3] at h2
    exact_mod_cast le_of_rpow_neg_le hηj (h1.trans h2)
  · exact (not_le.mp hc).le

/-! ### Step 4 -/

/-- **Step 4.** -/
theorem exists_multiplicity_coarse_bound [Nontrivial E] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hKT : KatzTaoEstimate.{u} E β) {η' : ℝ} (hη' : 0 < η') :
    ∃ η > (0 : ℝ), ∀ᶠ (b : NNReal) in 𝓝[>] 0,
      ∀ (dt : NNReal), dt ≠ 0 → dt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} (t : Finset ι) (T : ι → ShadedTube b E),
        (∀ i, (T i).carrier ⊆ closedBall 0 1) →
        (ShadedBody.fullness t (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ η →
        maxDensity t (fun i ↦ (T i).toConvexSpaceBody) ≤ (dt : ENNReal) ^ (-η') →
        ShadedBody.multiplicity t (fun i ↦ (T i).toShadedBody) ≤
          (dt : ENNReal) ^ (-(2 * η')) * (t.card : ENNReal) ^ β := by
  obtain ⟨η, hη, hev⟩ := KatzTaoEstimate.multiplicity_bound (E := E) hβ0 hKT η' hη'
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with b hb
  intro dt hdt0 hdtb hb1 ι t T hball hfull hmax
  have hdt1 : (dt : ENNReal) ≤ 1 := by exact_mod_cast hdtb.trans hb1
  have hdtc0 : (dt : ENNReal) ≠ 0 := by simpa using hdt0
  -- the raw bound from `genKKT`
  have hraw := hb t T hball hfull
  refine hraw.trans ?_
  -- `b ^ (-η') ≤ dt ^ (-η')`
  have hscale : (b : ENNReal) ^ (-η') ≤ (dt : ENNReal) ^ (-η') := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.mpr
      (ENNReal.rpow_le_rpow (by exact_mod_cast hdtb) hη'.le)
  -- `Δ_max ^ (1 - β) ≤ dt ^ (-η')`
  have hdens : maxDensity t (fun i ↦ (T i).toConvexSpaceBody) ^ (1 - β)
      ≤ (dt : ENNReal) ^ (-η') := by
    calc maxDensity t (fun i ↦ (T i).toConvexSpaceBody) ^ (1 - β)
        ≤ ((dt : ENNReal) ^ (-η')) ^ (1 - β) := ENNReal.rpow_le_rpow hmax (by linarith)
      _ = (dt : ENNReal) ^ (-η' * (1 - β)) := by rw [← ENNReal.rpow_mul]
      _ ≤ (dt : ENNReal) ^ (-η') := by
          refine ENNReal.rpow_le_rpow_of_exponent_ge hdt1 ?_
          nlinarith
  calc (b : ENNReal) ^ (-η') * maxDensity t (fun i ↦ (T i).toConvexSpaceBody) ^ (1 - β)
        * (t.card : ENNReal) ^ β
      ≤ (dt : ENNReal) ^ (-η') * (dt : ENNReal) ^ (-η') * (t.card : ENNReal) ^ β := by
        gcongr
    _ = (dt : ENNReal) ^ (-(2 * η')) * (t.card : ENNReal) ^ β := by
        rw [← ENNReal.rpow_add _ _ hdtc0 (by simp)]
        ring_nf

/-! ### Step 11 -/

/-- **Step 11.** -/
theorem multiplicity_le_of_two_factors
    {δ : NNReal} {mu mub muf L Cu : ENNReal} {Nb Nf N : ℕ} {β η' ν κ θ : ℝ}
    (hδ0 : (δ : ENNReal) ≠ 0) (hδ1 : (δ : ENNReal) ≤ 1) (hβ0 : 0 ≤ β)
    (hsplit : mu ≤ L * (mub * muf))
    (hb : mub ≤ (δ : ENNReal) ^ (-(2 * η')) * (Nb : ENNReal) ^ β)
    (hf : muf ≤ (δ : ENNReal) ^ ν * (Nf : ENNReal) ^ β)
    (hcard : (Nb : ENNReal) * (Nf : ENNReal) ≤ Cu * (N : ENNReal))
    (hL : L * Cu ^ β ≤ (δ : ENNReal) ^ (-κ))
    (hexp : θ ≤ ν - 2 * η' - κ) :
    mu ≤ (δ : ENNReal) ^ θ * (N : ENNReal) ^ β := by
  have hstep1 : mub * muf
      ≤ (δ : ENNReal) ^ (ν - 2 * η') * ((Nb : ENNReal) * (Nf : ENNReal)) ^ β := by
    calc mub * muf
        ≤ ((δ : ENNReal) ^ (-(2 * η')) * (Nb : ENNReal) ^ β)
            * ((δ : ENNReal) ^ ν * (Nf : ENNReal) ^ β) := by gcongr
      _ = ((δ : ENNReal) ^ (-(2 * η')) * (δ : ENNReal) ^ ν)
            * ((Nb : ENNReal) ^ β * (Nf : ENNReal) ^ β) := by ring
      _ = (δ : ENNReal) ^ (ν - 2 * η') * ((Nb : ENNReal) * (Nf : ENNReal)) ^ β := by
          rw [← ENNReal.rpow_add _ _ hδ0 (by simp), ENNReal.mul_rpow_of_nonneg _ _ hβ0]
          ring_nf
  have hstep2 : ((Nb : ENNReal) * (Nf : ENNReal)) ^ β ≤ Cu ^ β * (N : ENNReal) ^ β := by
    calc ((Nb : ENNReal) * (Nf : ENNReal)) ^ β ≤ (Cu * (N : ENNReal)) ^ β :=
          ENNReal.rpow_le_rpow hcard hβ0
      _ = Cu ^ β * (N : ENNReal) ^ β := ENNReal.mul_rpow_of_nonneg _ _ hβ0
  calc mu ≤ L * (mub * muf) := hsplit
    _ ≤ L * ((δ : ENNReal) ^ (ν - 2 * η') * (Cu ^ β * (N : ENNReal) ^ β)) :=
        mul_le_mul' le_rfl (hstep1.trans (mul_le_mul' le_rfl hstep2))
    _ = (L * Cu ^ β) * ((δ : ENNReal) ^ (ν - 2 * η') * (N : ENNReal) ^ β) := by ring
    _ ≤ (δ : ENNReal) ^ (-κ) * ((δ : ENNReal) ^ (ν - 2 * η') * (N : ENNReal) ^ β) := by gcongr
    _ = (δ : ENNReal) ^ (ν - 2 * η' - κ) * (N : ENNReal) ^ β := by
        rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδ0 (by simp)]
        ring_nf
    _ ≤ (δ : ENNReal) ^ θ * (N : ENNReal) ^ β :=
        mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hexp) le_rfl


/-! ### Step 7 (`lowerBdOnDeltaMaxTTSigmaTb`)

GWZ Lemma 7.4 (`Kakeya.MultiScaleSubmult.maxDensity_le_prod_fibreDeltaMax`) bounds
`Δ_max(𝕋̃_σ)` by a constant times the product of the fibre maxima at the two scales.
Read together with `tildeDeltaLargeDeltamax` (`σ^{-η_j} ≤ Δ_max(𝕋̃_σ)`) and the step-3 bound
`Δ_max(𝕋̃_b) ≤ δ̃^{-η'_{j-1}}`, this becomes a *lower* bound on the fibre density
`Δ_max(𝕋̃_σ[T_b])`.  The blueprint writes the conclusion as
`Δ_max(𝕋̃_σ[T_b]) ≳ δ^{η'_{j-1}} σ^{-η_j}`; here it is kept in the division-free product form
`σ^{-η_j} · δ̃^{η'_{j-1}} ≤ L · Δ_max(𝕋̃_σ[T_b])`, which is what step 8 consumes.
-/

/-- Cancelling a factor `δ^{-η}` on the right of a product bound: from `A ≤ B · δ^{-η}` and
`δ ≠ 0`, conclude `A · δ^{η} ≤ B`. -/
theorem le_of_le_mul_rpow_neg {A B : ENNReal} {δ : NNReal} {η : ℝ}
    (hδ0 : δ ≠ 0) (h : A ≤ B * (δ : ENNReal) ^ (-η)) :
    A * (δ : ENNReal) ^ η ≤ B := by
  have hd0 : (δ : ENNReal) ≠ 0 := by simpa using hδ0
  have hdt : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc A * (δ : ENNReal) ^ η ≤ (B * (δ : ENNReal) ^ (-η)) * (δ : ENNReal) ^ η := by gcongr
    _ = B * ((δ : ENNReal) ^ (-η) * (δ : ENNReal) ^ η) := by ring
    _ = B := by
        rw [← ENNReal.rpow_add _ _ hd0 hdt]
        simp

/-- **Step 7 (blueprint `lowerBdOnDeltaMaxTTSigmaTb`).**

`hlow` is `tildeDeltaLargeDeltamax` at the scale `σ`, `hsub` is GWZ Lemma 7.4 with loss `L`
(so `Dfib` is `Δ_max(𝕋̃_σ[T_b])` and `Db` is `Δ_max(𝕋̃_b)`), and `hDb` is the step-3 bound
`upperBdDeltaMaxTb`.  The conclusion is the blueprint's
`Δ_max(𝕋̃_σ[T_b]) ≳ δ̃^{η'_{j-1}} σ^{-η_j}` in division-free form. -/
theorem rpow_mul_le_mul_fibre_maxDensity
    {σ δt : NNReal} {ηj η' : ℝ} {Dσ Dfib Db L : ENNReal}
    (hδ0 : δt ≠ 0)
    (hlow : (σ : ENNReal) ^ (-ηj) ≤ Dσ)
    (hsub : Dσ ≤ L * (Dfib * Db))
    (hDb : Db ≤ (δt : ENNReal) ^ (-η')) :
    (σ : ENNReal) ^ (-ηj) * (δt : ENNReal) ^ η' ≤ L * Dfib := by
  refine le_of_le_mul_rpow_neg hδ0 ?_
  calc (σ : ENNReal) ^ (-ηj) ≤ Dσ := hlow
    _ ≤ L * (Dfib * Db) := hsub
    _ ≤ L * (Dfib * (δt : ENNReal) ^ (-η')) := by gcongr
    _ = L * Dfib * (δt : ENNReal) ^ (-η') := by ring

open scoped Classical in
/-- The fibre supremum `D_m` of GWZ Lemma 7.4 is attained: over a nonempty set of parents there
is a parent `j` whose own fibre density equals `Kakeya.MultiScaleSubmult.fibreDeltaMax`.

This is what licenses the blueprint's "fix a tube `T_b ∈ 𝕋̃_b`" *after* Lemma 7.4 has been
applied: the lemma bounds `Δ_max(𝕋̃_σ)` by the supremum over parents, and choosing `T_b` to be
a maximiser turns that supremum back into the density of a single fibre. -/
theorem exists_parent_fibre_eq_fibreDeltaMax {α κ : Type*} (u : Finset α)
    (W : α → ConvexSpaceBody E) {v : Finset κ} (hv : v.Nonempty) (par : α → κ) :
    ∃ j ∈ v, MultiScaleSubmult.fibreDeltaMax u W v par = maxDensity {i ∈ u | par i = j} W :=
  Finset.exists_mem_eq_sup v hv (fun j => maxDensity {i ∈ u | par i = j} W)

/-! ### Step 8 (`TTSigmaBigCardinalityV1`) -/

/-- **Step 8, division-free core.**  A restatement of
`Kakeya.ML2Spine.maxDensity_mul_volume_le_of_isFrostmanIn` with the cardinality isolated on the
right, which is the shape the cardinality lower bound is read off from. -/
theorem mul_volume_le_mul_card_of_isFrostmanIn {ι : Type*} {s : Finset ι}
    {W : ι → ConvexSpaceBody E} {Tb : ConvexSpaceBody E} {CF M cs : ENNReal}
    (hne : ∃ i ∈ s, 0 < volume (W i).carrier)
    (hsub : ∀ i ∈ s, W i ≤ Tb)
    (hF : IsFrostmanIn s W Tb CF)
    (hM : M ≤ maxDensity s W)
    (hvol : ∀ i ∈ s, volume (W i).carrier ≤ cs) :
    M * volume Tb.carrier ≤ CF * cs * (s.card : ENNReal) :=
  (maxDensity_mul_volume_le_of_isFrostmanIn hne hsub hF hM hvol).trans_eq (by ring)

/-- **Steps 7 and 8 combined, one `η'` spent.**  Feeding the step-7 lower bound on
`Δ_max(𝕋̃_σ[T_b])` into the Frostman count bound inside `T_b`. -/
theorem rpow_mul_volume_le_mul_card
    {ι : Type*} {s : Finset ι} {W : ι → ConvexSpaceBody E} {Tb : ConvexSpaceBody E}
    {σ δt : NNReal} {ηj η' : ℝ} {Dσ Db L CF cs : ENNReal}
    (hδ0 : δt ≠ 0)
    (hlow : (σ : ENNReal) ^ (-ηj) ≤ Dσ)
    (hsub7 : Dσ ≤ L * (maxDensity s W * Db))
    (hDb : Db ≤ (δt : ENNReal) ^ (-η'))
    (hne : ∃ i ∈ s, 0 < volume (W i).carrier)
    (hsubT : ∀ i ∈ s, W i ≤ Tb)
    (hF : IsFrostmanIn s W Tb CF)
    (hvol : ∀ i ∈ s, volume (W i).carrier ≤ cs) :
    (σ : ENNReal) ^ (-ηj) * (δt : ENNReal) ^ η' * volume Tb.carrier
      ≤ L * (CF * cs * (s.card : ENNReal)) := by
  have h7 : (σ : ENNReal) ^ (-ηj) * (δt : ENNReal) ^ η' ≤ L * maxDensity s W :=
    rpow_mul_le_mul_fibre_maxDensity hδ0 hlow hsub7 hDb
  calc (σ : ENNReal) ^ (-ηj) * (δt : ENNReal) ^ η' * volume Tb.carrier
      ≤ (L * maxDensity s W) * volume Tb.carrier := by gcongr
    _ = L * (maxDensity s W * volume Tb.carrier) := by ring
    _ ≤ L * (CF * cs * (s.card : ENNReal)) :=
        mul_le_mul_right (mul_volume_le_mul_card_of_isFrostmanIn hne hsubT hF le_rfl hvol) L

/-- **Steps 6, 7 and 8 combined: the two factors of `δ̃^{η'_{j-1}}`.**

`hF` is step 6 (`goodFrostmanBoundTTRhoInsideTb`): the Frostman constant of `𝕋̃_σ` inside `T_b`
is at most `CF₀ · δ̃^{-η'_{j-1}}`.  Together with step 7 this yields the blueprint's
`|𝕋̃_σ[T_b]| ≳ δ̃^{2η'_{j-1}} σ^{-η_j} |T_b|/|T_σ|`, here in division-free form. -/
theorem rpow_two_mul_volume_le_mul_card
    {ι : Type*} {s : Finset ι} {W : ι → ConvexSpaceBody E} {Tb : ConvexSpaceBody E}
    {σ δt : NNReal} {ηj η' : ℝ} {Dσ Db L CF₀ cs : ENNReal}
    (hδ0 : δt ≠ 0)
    (hlow : (σ : ENNReal) ^ (-ηj) ≤ Dσ)
    (hsub7 : Dσ ≤ L * (maxDensity s W * Db))
    (hDb : Db ≤ (δt : ENNReal) ^ (-η'))
    (hne : ∃ i ∈ s, 0 < volume (W i).carrier)
    (hsubT : ∀ i ∈ s, W i ≤ Tb)
    (hF : IsFrostmanIn s W Tb (CF₀ * (δt : ENNReal) ^ (-η')))
    (hvol : ∀ i ∈ s, volume (W i).carrier ≤ cs) :
    (σ : ENNReal) ^ (-ηj) * (δt : ENNReal) ^ (2 * η') * volume Tb.carrier
      ≤ L * CF₀ * cs * (s.card : ENNReal) := by
  have h := rpow_mul_volume_le_mul_card hδ0 hlow hsub7 hDb hne hsubT hF hvol
  have h' : (σ : ENNReal) ^ (-ηj) * (δt : ENNReal) ^ η' * volume Tb.carrier
      * (δt : ENNReal) ^ η' ≤ L * CF₀ * cs * (s.card : ENNReal) := by
    refine le_of_le_mul_rpow_neg hδ0 (h.trans_eq ?_)
    ring
  refine le_trans (le_of_eq ?_) h'
  have hd0 : (δt : ENNReal) ≠ 0 := by simpa using hδ0
  have hdt : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsq : (δt : ENNReal) ^ (2 * η') = (δt : ENNReal) ^ η' * (δt : ENNReal) ^ η' := by
    rw [← ENNReal.rpow_add _ _ hd0 hdt]
    ring_nf
  rw [hsq]
  ring


/-! ### Step 8, the real-arithmetic core

The blueprint reads `TTSigmaBigCardinalityV1` as `|𝕋̃_σ[T_b]| ≳ δ̃^{2η'_{j-1}} σ^{-2-η_j}`, but
what the count hypothesis of Lemma 9.1 actually consumes is the *rescaled* count: after `T_b`
is taken to `B_1`, the `σ`-tubes become `σ' = σ/b` tubes and the requirement is
`(σ')^{-2-ζ} ≤ |𝕋'_{σ'}|`.  The volume bookkeeping produces the factor `(b/σ)^{n-1}`, which is
exactly `(σ')^{-(n-1)}`; the lemma below performs that conversion, with the leftover
`σ^{-η_j} δ̃^{2η'_{j-1}} (σ/b)^{ζ} ≥ (loss constants)` isolated as the single hypothesis
`hthr`. -/
theorem rpow_div_le_card_of_bounds
    {x y d m ηj η' ζ clo Cup L CF₀ : ℝ} {N : ℕ}
    (hx : 0 < x) (hy : 0 < y)
    (hCup : 0 < Cup) (hL : 0 < L) (hCF : 0 < CF₀)
    (hmain : clo * x ^ (-ηj) * d ^ (2 * η') * y ^ m
              ≤ L * CF₀ * Cup * x ^ m * (N : ℝ))
    (hthr : L * CF₀ * Cup ≤ clo * x ^ (ζ - ηj) * y ^ (-ζ) * d ^ (2 * η')) :
    (x / y) ^ (-m - ζ) ≤ (N : ℝ) := by
  have hB : 0 < L * CF₀ * Cup * x ^ m := by positivity
  refine le_of_mul_le_mul_right ?_ hB
  have hxy : (x / y) ^ (-m - ζ) = x ^ (-m - ζ) * y ^ (m + ζ) := by
    rw [Real.div_rpow hx.le hy.le, div_eq_mul_inv, ← Real.rpow_neg hy.le]
    congr 2
    ring
  have e1 : x ^ (-m - ζ) * x ^ m = x ^ (-ζ) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have e2 : x ^ (-ζ) * x ^ (ζ - ηj) = x ^ (-ηj) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have e3 : y ^ (m + ζ) * y ^ (-ζ) = y ^ m := by
    rw [← Real.rpow_add hy]
    congr 1
    ring
  calc (x / y) ^ (-m - ζ) * (L * CF₀ * Cup * x ^ m)
      = (x ^ (-m - ζ) * x ^ m) * y ^ (m + ζ) * (L * CF₀ * Cup) := by rw [hxy]; ring
    _ = x ^ (-ζ) * y ^ (m + ζ) * (L * CF₀ * Cup) := by rw [e1]
    _ ≤ x ^ (-ζ) * y ^ (m + ζ) * (clo * x ^ (ζ - ηj) * y ^ (-ζ) * d ^ (2 * η')) := by
        have hnn : (0 : ℝ) ≤ x ^ (-ζ) * y ^ (m + ζ) := by positivity
        exact mul_le_mul_of_nonneg_left hthr hnn
    _ = clo * (x ^ (-ζ) * x ^ (ζ - ηj)) * d ^ (2 * η') * (y ^ (m + ζ) * y ^ (-ζ)) := by ring
    _ = clo * x ^ (-ηj) * d ^ (2 * η') * y ^ m := by rw [e2, e3]
    _ ≤ L * CF₀ * Cup * x ^ m * (N : ℝ) := hmain
    _ = (N : ℝ) * (L * CF₀ * Cup * x ^ m) := by ring


/-! ### Step 8 for tubes -/

/-- **Step 8 for a family of `σ`-tubes inside a `b`-tube.**

The hypotheses are, in order: step 7 in the form
`σ^{-η_j} ≤ Δ_max(𝕋̃_σ) ≤ L·(Δ_max(𝕋̃_σ[T_b])·Δ_max(𝕋̃_b))` together with the step-3 bound
`Δ_max(𝕋̃_b) ≤ δ̃^{-η'}`, and step 6 in the form
`C_F(𝕋̃_σ[T_b], T_b) ≤ CF₀·δ̃^{-η'}`.  The conclusion is the blueprint's
`TTSigmaBigCardinalityV1` with the volume normalisations kept honest: the factor
`b^{n-1}/σ^{n-1}` is `|T_b|/|T_σ|`, which after rescaling `T_b` to the unit ball is
`(σ/b)^{-(n-1)}`. -/
theorem tube_card_lower [Nontrivial E] {ι : Type*} {s : Finset ι}
    {σ b δt : NNReal} {T : ι → Tube σ E} {Tb : Tube b E}
    {ηj η' : ℝ} {Dσ Db : ENNReal} {L CF₀ : NNReal}
    (hσ0 : σ ≠ 0) (hσ1 : σ ≤ 1) (hδ0 : δt ≠ 0)
    (hlow : (σ : ENNReal) ^ (-ηj) ≤ Dσ)
    (hsub7 : Dσ ≤ (L : ENNReal) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody) * Db))
    (hDb : Db ≤ (δt : ENNReal) ^ (-η'))
    (hs : s.Nonempty)
    (hsubT : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ Tb.toConvexSpaceBody)
    (hF : IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody) Tb.toConvexSpaceBody
            ((CF₀ : ENNReal) * (δt : ENNReal) ^ (-η'))) :
    Tube.le_volume.c (Module.finrank ℝ E) * σ ^ (-ηj) * δt ^ (2 * η')
        * b ^ (Module.finrank ℝ E - 1)
      ≤ L * CF₀ * Tube.volume_le.C (Module.finrank ℝ E)
          * σ ^ (Module.finrank ℝ E - 1) * (s.card : NNReal) := by
  classical
  set n := Module.finrank ℝ E with hn
  -- every tube of the family has positive volume, and volume at most `C n · σ^{n-1}`
  have hpos : (0 : ENNReal) < ((Tube.le_volume.c n * σ ^ (n - 1) : NNReal) : ENNReal) := by
    refine ENNReal.coe_pos.mpr ?_
    have h1 : 0 < Tube.le_volume.c n := Tube.le_volume.c_pos n
    have h2 : (0 : NNReal) < σ ^ (n - 1) := pow_pos (pos_of_ne_zero hσ0) _
    exact mul_pos h1 h2
  have hne : ∃ i ∈ s, 0 < volume ((T i).toConvexSpaceBody).carrier := by
    obtain ⟨i₀, hi₀⟩ := hs
    exact ⟨i₀, hi₀, lt_of_lt_of_le hpos (T i₀).le_volume⟩
  have hvol : ∀ i ∈ s, volume ((T i).toConvexSpaceBody).carrier
      ≤ ((Tube.volume_le.C n * σ ^ (n - 1) : NNReal) : ENNReal) :=
    fun i _ ↦ Tube.volume_le hσ1 (T i)
  -- the abstract chain of steps 6, 7 and 8
  have hchain := rpow_two_mul_volume_le_mul_card (δt := δt) (L := (L : ENNReal))
    (CF₀ := (CF₀ : ENNReal)) hδ0 hlow hsub7 hDb hne hsubT hF hvol
  -- insert the volume lower bound for the ambient `b`-tube
  have hchain2 : (σ : ENNReal) ^ (-ηj) * (δt : ENNReal) ^ (2 * η')
        * ((Tube.le_volume.c n * b ^ (n - 1) : NNReal) : ENNReal)
      ≤ (L : ENNReal) * CF₀ * ((Tube.volume_le.C n * σ ^ (n - 1) : NNReal) : ENNReal)
          * (s.card : ENNReal) := by
    refine le_trans ?_ hchain
    gcongr
    exact Tb.le_volume
  rw [← ENNReal.coe_rpow_of_ne_zero hσ0, ← ENNReal.coe_rpow_of_ne_zero hδ0] at hchain2
  have hnn : σ ^ (-ηj) * δt ^ (2 * η') * (Tube.le_volume.c n * b ^ (n - 1))
      ≤ L * CF₀ * (Tube.volume_le.C n * σ ^ (n - 1)) * (s.card : NNReal) := by
    exact_mod_cast hchain2
  calc Tube.le_volume.c n * σ ^ (-ηj) * δt ^ (2 * η') * b ^ (n - 1)
      = σ ^ (-ηj) * δt ^ (2 * η') * (Tube.le_volume.c n * b ^ (n - 1)) := by ring
    _ ≤ L * CF₀ * (Tube.volume_le.C n * σ ^ (n - 1)) * (s.card : NNReal) := hnn
    _ = L * CF₀ * Tube.volume_le.C n * σ ^ (n - 1) * (s.card : NNReal) := by ring


/-- The `ℝ`-valued reading of `Kakeya.ML2Spine.tube_card_lower` in dimension `3`, in exactly
the shape of the count hypothesis of Lemma 9.1
(`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`): after rescaling `T_b` to the unit ball the
`σ`-tubes become `σ' = σ/b` tubes and the required lower bound is `(σ')^{-2-ζ} ≤ |𝕋'_{σ'}|`.

`hthr` is the single arithmetic threshold that the parameter spine has to supply; see
`Kakeya.ML2Spine.countThreshold_of_small` and `Kakeya.ML2Spine.spine_countGap` for the
reading of it that `Kakeya.ML2Spine.IsSpine` delivers. -/
theorem card_lower_of_nnreal_bound
    {σ b δt : NNReal} {ηj η' ζ : ℝ} {clo Cup L CF₀ : NNReal} {N : ℕ}
    (hσ0 : σ ≠ 0) (hb0 : b ≠ 0) (hCup : Cup ≠ 0) (hL : L ≠ 0) (hCF : CF₀ ≠ 0)
    (hmain : clo * σ ^ (-ηj) * δt ^ (2 * η') * b ^ (2 : ℕ)
              ≤ L * CF₀ * Cup * σ ^ (2 : ℕ) * (N : NNReal))
    (hthr : (L : ℝ) * CF₀ * Cup
              ≤ (clo : ℝ) * (σ : ℝ) ^ (ζ - ηj) * (b : ℝ) ^ (-ζ) * (δt : ℝ) ^ (2 * η')) :
    ((σ / b : NNReal) : ℝ) ^ (-2 - ζ) ≤ (N : ℝ) := by
  have hx : (0 : ℝ) < (σ : ℝ) := by
    exact_mod_cast pos_of_ne_zero hσ0
  have hy : (0 : ℝ) < (b : ℝ) := by
    exact_mod_cast pos_of_ne_zero hb0
  have hCup' : (0 : ℝ) < (Cup : ℝ) := by exact_mod_cast pos_of_ne_zero hCup
  have hL' : (0 : ℝ) < (L : ℝ) := by exact_mod_cast pos_of_ne_zero hL
  have hCF' : (0 : ℝ) < (CF₀ : ℝ) := by exact_mod_cast pos_of_ne_zero hCF
  have hmainR : (clo : ℝ) * (σ : ℝ) ^ (-ηj) * (δt : ℝ) ^ (2 * η') * (b : ℝ) ^ (2 : ℕ)
      ≤ (L : ℝ) * CF₀ * Cup * (σ : ℝ) ^ (2 : ℕ) * (N : ℝ) := by
    have := NNReal.coe_le_coe.mpr hmain
    push_cast [NNReal.coe_rpow] at this
    exact this
  have hcast : ∀ z : ℝ, 0 < z → z ^ (2 : ℝ) = z ^ (2 : ℕ) := by
    intro z _
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hmainR' : (clo : ℝ) * (σ : ℝ) ^ (-ηj) * (δt : ℝ) ^ (2 * η') * (b : ℝ) ^ (2 : ℝ)
      ≤ (L : ℝ) * CF₀ * Cup * (σ : ℝ) ^ (2 : ℝ) * (N : ℝ) := by
    rw [hcast _ hx, hcast _ hy]
    exact hmainR
  have hkey : ((σ : ℝ) / (b : ℝ)) ^ (-(2 : ℝ) - ζ) ≤ (N : ℝ) :=
    rpow_div_le_card_of_bounds hx hy hCup' hL' hCF' hmainR' hthr
  rw [NNReal.coe_div]
  simpa using hkey

/-- **Step 8, end to end, in dimension 3.**  The tube-level count bound of
`Kakeya.ML2Spine.tube_card_lower` delivered in the shape Lemma 9.1 consumes. -/
theorem tube_rescaled_card_lower [Nontrivial E] (hn : Module.finrank ℝ E = 3)
    {ι : Type*} {s : Finset ι}
    {σ b δt : NNReal} {T : ι → Tube σ E} {Tb : Tube b E}
    {ηj η' ζ : ℝ} {Dσ Db : ENNReal} {L CF₀ : NNReal}
    (hσ0 : σ ≠ 0) (hσ1 : σ ≤ 1) (hb0 : b ≠ 0) (hδ0 : δt ≠ 0)
    (hL : L ≠ 0) (hCF : CF₀ ≠ 0)
    (hlow : (σ : ENNReal) ^ (-ηj) ≤ Dσ)
    (hsub7 : Dσ ≤ (L : ENNReal) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody) * Db))
    (hDb : Db ≤ (δt : ENNReal) ^ (-η'))
    (hs : s.Nonempty)
    (hsubT : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ Tb.toConvexSpaceBody)
    (hF : IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody) Tb.toConvexSpaceBody
            ((CF₀ : ENNReal) * (δt : ENNReal) ^ (-η')))
    (hthr : (L : ℝ) * CF₀ * (Tube.volume_le.C 3 : ℝ)
              ≤ (Tube.le_volume.c 3 : ℝ) * (σ : ℝ) ^ (ζ - ηj) * (b : ℝ) ^ (-ζ)
                  * (δt : ℝ) ^ (2 * η')) :
    ((σ / b : NNReal) : ℝ) ^ (-2 - ζ) ≤ (s.card : ℝ) := by
  have hmain := tube_card_lower hσ0 hσ1 hδ0 hlow hsub7 hDb hs hsubT hF
  rw [hn] at hmain
  simp only [show (3 : ℕ) - 1 = 2 from rfl] at hmain
  exact card_lower_of_nnreal_bound hσ0 hb0 (ne_of_gt (Tube.volume_le.C_pos 3)) hL hCF hmain hthr


/-! ### The count threshold is met by the parameter spine

`hthr` is the only genuinely arithmetic hypothesis of
`Kakeya.ML2Spine.card_lower_of_nnreal_bound`, and it is *not* vacuous: the two lemmas below
show it is exactly the separation `2η'_{j-1} < ε₂ η_j / 2` of the spine, plus a threshold on
`δ̃` absorbing the fixed dimensional constants. -/

/-- **`hthr` from the separation of exponents and a threshold on `δ̃`.**

Reading `ζ = η_j/2` as in the blueprint, `σ^{ζ-η_j} = σ^{-η_j/2}` and `b^{-ζ} ≥ 1`, so the
right-hand side of `hthr` is at least `clo · δ̃^{2η'_{j-1} - ε₂ η_j/2}`, using only
`σ ≤ δ̃^{ε₂}` — the upper end of the scale window `σ ∈ [δ̃^{1-ε₂}, δ̃^{ε₂}]`. -/
theorem countThreshold_of_small
    {σ b δt : NNReal} {ηj η' ζ ε₂ κ : ℝ} {clo Cup L CF₀ : NNReal}
    (hζ : ζ = ηj / 2) (hηj : 0 ≤ ηj)
    (hσ0 : σ ≠ 0) (hb0 : b ≠ 0) (hδ0 : δt ≠ 0) (hδ1 : δt ≤ 1) (hb1 : b ≤ 1)
    (hσwin : σ ≤ δt ^ ε₂)
    (hgap : 2 * η' - ε₂ * ηj / 2 ≤ -κ)
    (hsmall : (L : ℝ) * CF₀ * Cup ≤ (clo : ℝ) * (δt : ℝ) ^ (-κ)) :
    (L : ℝ) * CF₀ * Cup
      ≤ (clo : ℝ) * (σ : ℝ) ^ (ζ - ηj) * (b : ℝ) ^ (-ζ) * (δt : ℝ) ^ (2 * η') := by
  have hx : (0 : ℝ) < (σ : ℝ) := by exact_mod_cast pos_of_ne_zero hσ0
  have hy : (0 : ℝ) < (b : ℝ) := by exact_mod_cast pos_of_ne_zero hb0
  have hd : (0 : ℝ) < (δt : ℝ) := by exact_mod_cast pos_of_ne_zero hδ0
  have hd1 : (δt : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hy1 : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  have hζ0 : 0 ≤ ζ := by rw [hζ]; linarith
  have hbone : (1 : ℝ) ≤ (b : ℝ) ^ (-ζ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1 (by linarith)
  have hσR : (σ : ℝ) ≤ (δt : ℝ) ^ ε₂ := by
    have h := NNReal.coe_le_coe.mpr hσwin
    simpa [NNReal.coe_rpow] using h
  have hexp : ζ - ηj ≤ 0 := by rw [hζ]; linarith
  have hstep : (δt : ℝ) ^ (ε₂ * (ζ - ηj)) ≤ (σ : ℝ) ^ (ζ - ηj) := by
    have h := Real.rpow_le_rpow_of_nonpos hx hσR hexp
    rwa [← Real.rpow_mul hd.le] at h
  have heq : ε₂ * (ζ - ηj) + 2 * η' = 2 * η' - ε₂ * ηj / 2 := by rw [hζ]; ring
  have hdgap : (δt : ℝ) ^ (-κ) ≤ (δt : ℝ) ^ (ε₂ * (ζ - ηj) + 2 * η') :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (by rw [heq]; exact hgap)
  have hclo : (0 : ℝ) ≤ (clo : ℝ) := (clo : ℝ≥0).coe_nonneg
  calc (L : ℝ) * CF₀ * Cup ≤ (clo : ℝ) * (δt : ℝ) ^ (-κ) := hsmall
    _ ≤ (clo : ℝ) * (δt : ℝ) ^ (ε₂ * (ζ - ηj) + 2 * η') := mul_le_mul_of_nonneg_left hdgap hclo
    _ = (clo : ℝ) * ((δt : ℝ) ^ (ε₂ * (ζ - ηj)) * (δt : ℝ) ^ (2 * η')) := by
        rw [Real.rpow_add hd]
    _ ≤ (clo : ℝ) * ((σ : ℝ) ^ (ζ - ηj) * (δt : ℝ) ^ (2 * η')) := by
        refine mul_le_mul_of_nonneg_left ?_ hclo
        exact mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg hd.le _)
    _ = ((clo : ℝ) * (σ : ℝ) ^ (ζ - ηj) * (δt : ℝ) ^ (2 * η')) * 1 := by ring
    _ ≤ ((clo : ℝ) * (σ : ℝ) ^ (ζ - ηj) * (δt : ℝ) ^ (2 * η')) * (b : ℝ) ^ (-ζ) :=
        mul_le_mul_of_nonneg_left hbone (by positivity)
    _ = (clo : ℝ) * (σ : ℝ) ^ (ζ - ηj) * (b : ℝ) ^ (-ζ) * (δt : ℝ) ^ (2 * η') := by ring

/-- **The spine supplies the gap `κ = 2 e η_j > 0`.**

With the blueprint's `η'_{k} = 12 η_k/(e β)`, `IsSpine.sep_le` gives `2η'_k ≤ e η_{k+1}/2`
while `IsSpine.div_le` gives `5 e ≤ ε₂`, so
`2η'_k - ε₂ η_{k+1}/2 ≤ e η_{k+1}/2 - 5 e η_{k+1}/2 = -2 e η_{k+1}`. -/
theorem spine_countGap {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) {k : ℕ} (hk : k < N) :
    2 * (12 * η k / (e * β)) - ε₂ * η (k + 1) / 2 ≤ -(2 * e * η (k + 1)) := by
  have h1 := h.sep_le k hk
  have h2 := h.div_le
  have h3 := h.rung_pos (k + 1)
  nlinarith [mul_le_mul_of_nonneg_right h2 h3.le]

/-- The gap `κ = 2 e η_{k+1}` produced by `Kakeya.ML2Spine.spine_countGap` is positive. -/
theorem spine_countGap_pos {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) (k : ℕ) : 0 < 2 * e * η (k + 1) := by
  have := h.div_pos
  have := h.rung_pos (k + 1)
  positivity


/-! ### Blueprint-named forms of steps 3 and 6 -/

/-- **Step 3, blueprint `upperBdDeltaMaxTb`.**

`Δ_max(𝕋̃_b) ≤ (|T_b|/|V|) Δ_max(𝕍) ≤ δ̃^{-η'_{j-1}}`.  The volume band is how the call site
has the geometry: every `b`-tube of `𝕋̃_b` has volume at most `vhi ∼ |T_b|`, and the plank
`V (f j)` it was produced from has volume at least `vlo ∼ |V|`.  In the non-eccentric case
`vhi/vlo ∼ b/a ≤ δ̃^{-η'_{j-1}}`, and `Δ_max(𝕍) ≲ 1`, which together are `hratio`. -/
theorem upperBdDeltaMaxTb {ι κ : Type*} [DecidableEq ι]
    {t : Finset κ} {W : κ → ConvexSpaceBody E} {u : Finset ι} {V : ι → ConvexSpaceBody E}
    {f : κ → ι} {vhi vlo Dv : ENNReal} {δt : NNReal} {η' : ℝ}
    (hfinj : ∀ j ∈ t, ∀ j' ∈ t, f j = f j' → j = j')
    (hfu : ∀ j ∈ t, f j ∈ u)
    (hVW : ∀ j ∈ t, V (f j) ≤ W j)
    (hWvol : ∀ j ∈ t, volume (W j).carrier ≤ vhi)
    (hVvol : ∀ j ∈ t, vlo ≤ volume (V (f j)).carrier)
    (hvlo0 : vlo ≠ 0) (hvlotop : vlo ≠ ⊤)
    (hDv : maxDensity u V ≤ Dv)
    (hratio : vhi * Dv ≤ (δt : ENNReal) ^ (-η') * vlo) :
    maxDensity t W ≤ (δt : ENNReal) ^ (-η') :=
  maxDensity_le_of_nested_inj hfinj hfu hVW hWvol hVvol hvlo0 hvlotop
    (le_trans (mul_le_mul_right hDv vhi) hratio)

/-- **Step 6, blueprint `goodFrostmanBoundTTRhoInsideTb`.**

`Δ(𝕋̃_ρ, T_b) ≥ (|V|/|T_b|) Δ(𝕋̃_ρ, V) ⪆ δ^{η'_{j-1}} Δ_max(𝕋̃_ρ)`, i.e.
`C_F(𝕋̃_ρ, T_b) ≲ δ^{-η'_{j-1}}`.  `hmax` is the input `C_F(𝕋̃_ρ, V) ≤ Cv ⪅ 1` coming from the
maximal-density factoring, and `hvolratio` is the volume comparison `|V|/|T_b| ⪆ δ^{η'_{j-1}}`
in division-free form.

The extension to all `σ ∈ [ρ, b]` is the inheritance remark, available as
`Kakeya.ML2Spine.exists_subset_isFrostmanIn_parents'`. -/
theorem goodFrostmanBoundTTRhoInsideTb {ι : Type*} {s : Finset ι}
    {W : ι → ConvexSpaceBody E} {V Tb : ConvexSpaceBody E} {Cv CF₀ : ENNReal}
    {δt : NNReal} {η' : ℝ}
    (hVT : V ≤ Tb)
    (hmax : maxDensity s W ≤ Cv * densityIn s W V)
    (hvolratio : Cv * volume Tb.carrier
        ≤ CF₀ * (δt : ENNReal) ^ (-η') * volume V.carrier)
    (hV0 : volume V.carrier ≠ 0) (hVtop : volume V.carrier ≠ ⊤) :
    IsFrostmanIn s W Tb (CF₀ * (δt : ENNReal) ^ (-η')) :=
  isFrostmanIn_of_maxDensity_le_densityIn hVT hmax hvolratio hV0 hVtop

/-! ### Step 11: the gain budget of the spine -/

/-- **The exponent inequality of step 11**, `ν(β, η_j/2) - 2η'_{j-1} ≥ 10 η_{j-1}/ε₂`,
read off `IsSpine.gain_budget`.  The blueprint's `η'_{j-1} = 12 η_{j-1}/(ε₂ β)` is replaced by
the sharper `12 η_{j-1}/(e β)`; since `e ≤ ε₂`, that is the larger quantity, so this is the
stronger statement. -/
theorem spine_gainBudget {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) {k : ℕ} (hk : k < N) :
    10 * η k / ε₂ ≤ gain (η (k + 1) / 2) - 2 * (12 * η k / (e * β)) := by
  have hb := h.gain_budget k hk
  have hd := h.div_le_eps₂
  have he := h.div_pos
  have hk0 := h.rung_pos k
  have s1 : 10 * η k / ε₂ ≤ 10 * η k / e :=
    div_le_div_of_nonneg_left (by positivity) he hd
  linarith

/-- **Step 11 with the multiscale loss absorbed.**  The blueprint's `≲` in
`μ(𝕋̃, Ỹ) ⪅ μ(𝕋̃_b, ·) μ(𝕋̃[T_b], ·)` costs an exponent `κ`; the spine leaves room for it
because `e ≤ ε₂/5` makes `10 η_{j-1}/e` five times `10 η_{j-1}/ε₂`. -/
theorem spine_gainBudget_of_loss {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) {k : ℕ} (hk : k < N)
    {κ : ℝ} (hκ : κ ≤ 40 * η k / ε₂) :
    10 * η k / ε₂ ≤ gain (η (k + 1) / 2) - 2 * (12 * η k / (e * β)) - κ := by
  have hb := h.gain_budget k hk
  have he := h.div_pos
  have hd := h.div_le
  have he₂ := h.eps₂_pos
  have hk0 := h.rung_pos k
  have s1 : 50 * η k / ε₂ ≤ 10 * η k / e := by
    have hstep : 10 * η k / (ε₂ / 5) ≤ 10 * η k / e :=
      div_le_div_of_nonneg_left (by positivity) he hd
    have : 10 * η k / (ε₂ / 5) = 50 * η k / ε₂ := by
      field_simp
      ring
    linarith [this ▸ hstep]
  have s2 : 10 * η k / ε₂ + 40 * η k / ε₂ = 50 * η k / ε₂ := by
    field_simp
    ring
  linarith


/-! ### The spine-driven readings of steps 5 and 8 -/

/-- **Step 5, driven by the spine.**  The hypothesis `η'_{j-1} ≤ η_j ε₂` of
`Kakeya.ML2Spine.le_of_maxDensity_le_window` is `IsSpine.sep_le_weak` at the rung `k = j-1`, so
no arithmetic is left for the call site: comparing `tildeDeltaLargeDeltamax` at `ρ = b` with
`upperBdDeltaMaxTb` forces `b ≥ δ̃^{ε₂}`. -/
theorem spine_le_of_maxDensity_le_window
    {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) {k : ℕ} (hk : k < N)
    {δt b : NNReal} {Δb : ENNReal}
    (hδ0 : δt ≠ 0) (hδ1 : δt ≤ 1)
    (hwin : b ≤ δt ^ ε₂ → (b : ENNReal) ^ (-(η (k + 1))) ≤ Δb)
    (hup : Δb ≤ (δt : ENNReal) ^ (-(12 * η k / (e * β)))) :
    δt ^ ε₂ ≤ b :=
  le_of_maxDensity_le_window hδ0 hδ1 (h.rung_pos (k + 1))
    (by have := h.sep_le_weak hk; linarith) hwin hup

/-- **The count threshold of step 8, driven by the spine.**  This is
`Kakeya.ML2Spine.countThreshold_of_small` with `ζ = η_j/2`, `η'_{j-1} = 12 η_{j-1}/(e β)` and
the gap `κ = 2 e η_j` of `Kakeya.ML2Spine.spine_countGap`; the only remaining hypothesis is the
threshold `hsmall` on `δ̃`, whose exponent `-2 e η_j` is strictly negative
(`Kakeya.ML2Spine.spine_countGap_pos`), so it holds for all small `δ̃`. -/
theorem spine_countThreshold
    {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (h : IsSpine β ϖ ε₁ gain dens ε₂ e N η) {k : ℕ} (hk : k < N)
    {σ b δt : NNReal} {clo Cup L CF₀ : NNReal}
    (hσ0 : σ ≠ 0) (hb0 : b ≠ 0) (hδ0 : δt ≠ 0) (hδ1 : δt ≤ 1) (hb1 : b ≤ 1)
    (hσwin : σ ≤ δt ^ ε₂)
    (hsmall : (L : ℝ) * CF₀ * Cup
        ≤ (clo : ℝ) * (δt : ℝ) ^ (-(2 * e * η (k + 1)))) :
    (L : ℝ) * CF₀ * Cup
      ≤ (clo : ℝ) * (σ : ℝ) ^ (η (k + 1) / 2 - η (k + 1)) * (b : ℝ) ^ (-(η (k + 1) / 2))
          * (δt : ℝ) ^ (2 * (12 * η k / (e * β))) :=
  countThreshold_of_small rfl (h.rung_pos (k + 1)).le hσ0 hb0 hδ0 hδ1 hb1 hσwin
    (spine_countGap h hk) hsmall


/-- **Step 8, the single entry point.**

Everything the blueprint's non-eccentric case needs before Lemma 9.1 can be invoked, in one
statement: given the parameter spine at the rung `k = j-1`, the step-7 input `hlow`/`hsub7`,
the step-3 bound `hDb`, the step-6 Frostman bound `hF`, and a threshold `hsmall` on `δ̃`, the
family of `σ`-tubes inside `T_b` has at least `(σ/b)^{-2-η_j/2}` members — which is exactly the
count hypothesis of `Kakeya.multiplicity_le_of_card_isEssDistinct_ge` at `ζ = η_j/2` and
`σ' = σ/b`.

The exponent of `hsmall` is `-2 e η_j < 0` (`Kakeya.ML2Spine.spine_countGap_pos`), so `hsmall`
holds for every sufficiently small `δ̃`; no other arithmetic is left to the caller. -/
theorem spine_tube_card_lower [Nontrivial E] (hn : Module.finrank ℝ E = 3)
    {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (hspine : IsSpine β ϖ ε₁ gain dens ε₂ e N η) {k : ℕ} (hk : k < N)
    {ι : Type*} {s : Finset ι} {σ b δt : NNReal} {T : ι → Tube σ E} {Tb : Tube b E}
    {Dσ Db : ENNReal} {L CF₀ : NNReal}
    (hσ0 : σ ≠ 0) (hσ1 : σ ≤ 1) (hb0 : b ≠ 0) (hb1 : b ≤ 1)
    (hδ0 : δt ≠ 0) (hδ1 : δt ≤ 1) (hL : L ≠ 0) (hCF : CF₀ ≠ 0)
    (hσwin : σ ≤ δt ^ ε₂)
    (hlow : (σ : ENNReal) ^ (-(η (k + 1))) ≤ Dσ)
    (hsub7 : Dσ ≤ (L : ENNReal) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody) * Db))
    (hDb : Db ≤ (δt : ENNReal) ^ (-(12 * η k / (e * β))))
    (hs : s.Nonempty)
    (hsubT : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ Tb.toConvexSpaceBody)
    (hF : IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody) Tb.toConvexSpaceBody
            ((CF₀ : ENNReal) * (δt : ENNReal) ^ (-(12 * η k / (e * β)))))
    (hsmall : (L : ℝ) * CF₀ * (Tube.volume_le.C 3 : ℝ)
        ≤ (Tube.le_volume.c 3 : ℝ) * (δt : ℝ) ^ (-(2 * e * η (k + 1)))) :
    ((σ / b : NNReal) : ℝ) ^ (-2 - η (k + 1) / 2) ≤ (s.card : ℝ) :=
  tube_rescaled_card_lower hn hσ0 hσ1 hb0 hδ0 hL hCF hlow hsub7 hDb hs hsubT hF
    (spine_countThreshold hspine hk hσ0 hb0 hδ0 hδ1 hb1 hσwin hsmall)

end Kakeya.ML2Spine

end
