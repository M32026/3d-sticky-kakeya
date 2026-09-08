/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.KatzTao
public import Kakeya.DimensionThree.MainLemma1.Rescaling.UniformEveryScale
public import Kakeya.Pigeonhole
public import Kakeya.Factoring.Pigeonhole

/-!
# The middle factor at average fullness

`Kakeya.ml1Boot.multiplicity_le_middle` asks its caller for a *per-tube* two-sided shading
bracket `Λ⁻¹ μ₀ |T| ≤ |Y(T)| ≤ Λ μ₀ |T|` at an externally supplied constant `Λ`.  That
demand is not met by the producer, and the blueprint's repair is to make the middle factor
consume only the **average** fullness `δ ^ η(γ) ≤ λ(𝕌, Z)` and to perform the density
normalization *inside* the theorem, paying for it in shade mass.

This file carries out that repair.  The normalization is
`Kakeya.ml1Boot.exists_internalDensityNormalization`: discard the tubes of below-average
shading (`ShadedBody.discardLowShading`, a `1/2`-refinement), then pigeonhole the surviving
densities into a single dyadic band (`ShadedBody.exists_isCRefinement_comparable_density`).
The dyadic loss `1 + log₂ (1/a)` is bounded by the *polynomial* `4 / a`
(`Kakeya.ml1Boot.one_add_logb_le_four_div`), which is what keeps the whole bookkeeping inside
the `δ`-power ledger and makes a `C_u(δ)`-style public parameter unnecessary: the bracket
constant handed to `Kakeya.ml1Boot.exists_normalizedMiddleData` is the fixed `Λ = 2`, so the
uniformity constant `Kakeya.ml1Boot.normalizedUnif.C C_unif 2` of the rescaled family is still
chosen before `δ`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya

namespace ml1Boot

section Internal

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The dyadic pigeonholing loss is polynomial in the density floor.**

`ShadedBody.exists_isCRefinement_comparable_density` retains a `(1 + log₂ (1/a))⁻¹` fraction
of the shading mass, where `a` is the pointwise density floor.  The logarithm is bounded by
`4 / a` on `(0, 1]`, which is all this development ever needs: a `δ`-power floor
`a ≥ δ ^ e` then gives a `δ`-power loss `δ ^ (-e)`, and no `log (1/δ)`-absorption lemma is
required anywhere downstream. -/
theorem one_add_logb_le_four_div {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    1 + Real.logb 2 a⁻¹ ≤ 4 / a := by
  have hx1 : (1 : ℝ) ≤ a⁻¹ := one_le_inv_iff₀.mpr ⟨ha0, ha1⟩
  have hxpos : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha0
  have hlog : Real.log a⁻¹ ≤ a⁻¹ - 1 := Real.log_le_sub_one_of_pos hxpos
  have hlog2 : (2 : ℝ) / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlognn : 0 ≤ Real.log a⁻¹ := Real.log_nonneg hx1
  have hkey : Real.logb 2 a⁻¹ ≤ (3 / 2) * a⁻¹ := by
    rw [Real.logb, div_le_iff₀ (by linarith : (0:ℝ) < Real.log 2)]
    nlinarith [hlognn, hlog, hlog2, hxpos]
  have h4 : (4 : ℝ) / a = 4 * a⁻¹ := by rw [div_eq_mul_inv]
  rw [h4]
  linarith [hx1, hkey]


/-- **The middle factor's density normalization, done internally** (blueprint §4.3, PO-2).

From nothing but the *average* fullness `λ ≤ λ(𝕌, Z)` of a nonempty family of shaded
`τ`-tubes this produces a subfamily `u₂` on which the shading densities lie in a single
dyadic band — i.e. a two-sided per-tube bracket at the **fixed** constant `Λ = 2` — together
with the three retention certificates the middle factor pays for it in:

* the multiplicity loss `µ(u, Z) ≤ (16 / λ) µ(u₂, Z)`;
* the surviving average fullness `λ² / 16 ≤ λ(u₂, Z)`;
* the cardinality retention `(λ² / 16) |u| ≤ |u₂|`, which is what transports the Frostman
  constant by `ConvexSpaceBody.frostmanConstIn_subfamily_le`.

Every loss is a power of `λ`, hence a power of `δ` once `λ ≥ δ ^ η(γ)`; this is where
`Kakeya.ml1Boot.one_add_logb_le_four_div` is used, and it is why the caller never needs a
`log (1/δ)`-absorption lemma.

The order of the two steps is the point of the repair.  Discarding the below-average tubes
first (`ShadedBody.discardLowShading` at level `1/2`) is what bounds the number of dyadic
bands, and the dyadic band is selected *afterwards*; both steps only pass to a subfamily, so
the one-sided uniformity `Kakeya.IsFlatPrismUniform` of the input survives verbatim by
`Kakeya.IsFlatPrismUniform.mono_index`.  It is precisely because the middle factor reads
uniformity one-sidedly that "uniformize, then density-restrict" does not destroy the
uniformity and the normalization can live inside the theorem. -/
theorem exists_internalDensityNormalization [Nontrivial E] {ι : Type*} {τ : NNReal}
    (hτ0 : 0 < τ)
    {u : Finset ι} (U : ι → ShadedTube τ E) (hu : u.Nonempty)
    {lam : NNReal} (hlam0 : 0 < lam)
    (hfull : (lam : ENNReal)
      ≤ (ShadedBody.fullness u (fun k => (U k).toShadedBody) : ENNReal)) :
    ∃ u₂ ⊆ u, u₂.Nonempty ∧ ∃ μ₀ : ENNReal, 0 < μ₀ ∧
      (∀ k ∈ u₂, ((2 : NNReal) : ENNReal)⁻¹ * μ₀ * volume (U k).carrier
            ≤ volume (U k).shade ∧
          volume (U k).shade ≤ ((2 : NNReal) : ENNReal) * μ₀ * volume (U k).carrier) ∧
      ShadedBody.multiplicity u (fun k => (U k).toShadedBody)
          ≤ 16 / (lam : ENNReal)
            * ShadedBody.multiplicity u₂ (fun k => (U k).toShadedBody) ∧
      (lam : ENNReal) ^ 2 / 16
          ≤ (ShadedBody.fullness u₂ (fun k => (U k).toShadedBody) : ENNReal) ∧
      (lam : ENNReal) ^ 2 / 16 * (u.card : ENNReal) ≤ (u₂.card : ENNReal) := by
  classical
  set Y : ι → ShadedBody E := fun k => (U k).toShadedBody with hY
  obtain ⟨i₀, hi₀⟩ := hu
  have hu : u.Nonempty := ⟨i₀, hi₀⟩
  set v : ENNReal := volume (U i₀).carrier with hv_def
  have hvol : ∀ i ∈ u, volume (Y i).carrier = v := by
    intro i _
    simpa [hY, hv_def] using
      _root_.Tube.volume_carrier_eq_volume_carrier (U i).toTube (U i₀).toTube
  have hv_pos : 0 < v := by
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hδp : 0 < (τ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hτ0) (Module.finrank ℝ E - 1)
    exact lt_of_lt_of_le (ENNReal.mul_pos hc.ne' hδp.ne')
      (by simpa [hv_def] using _root_.Tube.le_volume (U i₀).toTube)
  have hv_top : v ≠ ⊤ := by
    rw [hv_def]
    exact (U i₀).isCompact.measure_ne_top
  -- the family's own fullness
  set lu : NNReal := ShadedBody.fullness u Y with hlu
  have hlam_lu : lam ≤ lu := by exact_mod_cast hfull
  have hlu0 : 0 < lu := lt_of_lt_of_le hlam0 hlam_lu
  have hlu1 : lu ≤ 1 := ShadedBody.fullness_le_one u Y
  -- total carrier and shading mass
  have hsumcar : ∑ i ∈ u, volume (Y i).carrier = (u.card : ENNReal) * v := by
    rw [Finset.sum_congr rfl hvol, Finset.sum_const, nsmul_eq_mul]
  have hcard0 : (0 : ENNReal) < (u.card : ENNReal) := by
    exact_mod_cast Finset.card_pos.mpr hu
  have hsumshade : ∑ i ∈ u, volume (Y i).shade = (lu : ENNReal) * ((u.card : ENNReal) * v) := by
    rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul u Y, hsumcar]
  have hmass_pos : 0 < ∑ i ∈ u, volume (Y i).shade := by
    rw [hsumshade]
    exact ENNReal.mul_pos (by exact_mod_cast hlu0.ne')
      (ENNReal.mul_pos hcard0.ne' hv_pos.ne').ne'
  -- Step 1: discard the tubes of below-average shading.
  set u₀ : Finset ι := ShadedBody.discardLowShading u Y (1 / 2 : NNReal) with hu₀
  have hu₀u : u₀ ⊆ u := ShadedBody.discardLowShading_subset u Y _
  have href0 : ShadedBody.IsCRefinement u₀ Y u Y (1 - (1 / 2 : NNReal)) :=
    ShadedBody.isCRefinement_discardLowShading u Y (by norm_num)
  have hhalf : (1 : NNReal) - (1 / 2 : NNReal) = (1 / 2 : NNReal) := by
    rw [← NNReal.coe_inj]; push_cast; norm_num
  rw [hhalf] at href0
  -- the pointwise density floor on `u₀`
  set aa : NNReal := (1 / 2 : NNReal) * lu with haa
  have haa0 : 0 < aa := by
    rw [haa]; exact mul_pos (by norm_num) hlu0
  have haa1 : aa ≤ 1 := by
    rw [haa]
    calc (1 / 2 : NNReal) * lu ≤ (1 / 2 : NNReal) * 1 := by gcongr
      _ ≤ 1 := by norm_num
  have hZ : ∀ i ∈ u₀, (aa : ENNReal) * volume (Y i).carrier ≤ volume (Y i).shade := by
    intro i hi
    have := ShadedBody.le_volume_shade_of_mem_discardLowShading (c := (1 / 2 : NNReal)) hi
    calc (aa : ENNReal) * volume (Y i).carrier
        = ((1 / 2 : NNReal) : ENNReal) * (lu : ENNReal) * volume (Y i).carrier := by
          rw [haa]; push_cast; ring
      _ ≤ volume (Y i).shade := this
  have hu₀ne : u₀.Nonempty := by
    rcases Finset.eq_empty_or_nonempty u₀ with h | h
    · exfalso
      have := href0.2
      rw [h] at this
      simp only [Finset.sum_empty, nonpos_iff_eq_zero, mul_eq_zero] at this
      rcases this with h1 | h2
      · exact absurd h1 (by simp)
      · exact absurd h2 hmass_pos.ne'
    · exact h
  -- Step 2: pigeonhole the surviving densities into one dyadic band.
  obtain ⟨u₂, hu₂u₀, lam2, hlam20, href2, hband, haa_lam2, -⟩ :=
    ShadedBody.exists_isCRefinement_comparable_density (V := Y) hu₀ne
      (fun i hi => hvol i (hu₀u hi)) hv_pos.ne' haa0 haa1 hZ
  set D : NNReal := (1 + Real.logb 2 ((aa : ℝ))⁻¹).toNNReal with hD
  have hlogb_nn : 0 ≤ 1 + Real.logb 2 ((aa : ℝ))⁻¹ := by
    have : 0 ≤ Real.logb 2 ((aa : ℝ))⁻¹ :=
      Real.logb_nonneg (by norm_num) (one_le_inv_iff₀.mpr ⟨by exact_mod_cast haa0,
        by exact_mod_cast haa1⟩)
    linarith
  have hDcoe : ((D : ℝ≥0) : ℝ) = 1 + Real.logb 2 ((aa : ℝ))⁻¹ :=
    Real.coe_toNNReal _ hlogb_nn
  have hD1 : 1 ≤ D := by
    rw [← NNReal.coe_le_coe, hDcoe]
    have : 0 ≤ Real.logb 2 ((aa : ℝ))⁻¹ :=
      Real.logb_nonneg (by norm_num) (one_le_inv_iff₀.mpr ⟨by exact_mod_cast haa0,
        by exact_mod_cast haa1⟩)
    push_cast
    linarith
  have hD0 : D ≠ 0 := by
    intro h; rw [h] at hD1; simp at hD1
  -- the dyadic loss is polynomial in the floor: `D * λ ≤ 8`
  have hDlu : D * lu ≤ 8 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [hDcoe]
    have hax : (aa : ℝ) = (lu : ℝ) / 2 := by rw [haa]; push_cast; ring
    have hle : 1 + Real.logb 2 ((aa : ℝ))⁻¹ ≤ 4 / (aa : ℝ) :=
      one_add_logb_le_four_div (by exact_mod_cast haa0) (by exact_mod_cast haa1)
    have hpos : (0 : ℝ) < (aa : ℝ) := by exact_mod_cast haa0
    have hlu' : (lu : ℝ) = 2 * (aa : ℝ) := by rw [hax]; ring
    rw [hlu']
    have hstep : (1 + Real.logb 2 ((aa : ℝ))⁻¹) * (2 * (aa : ℝ))
        ≤ (4 / (aa : ℝ)) * (2 * (aa : ℝ)) := by
      have h2 : (0 : ℝ) ≤ 2 * (aa : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_right hle h2
    have hcalc : (4 / (aa : ℝ)) * (2 * (aa : ℝ)) = 8 := by field_simp; norm_num
    linarith [hstep, hcalc.le, hcalc.ge]
  have hDlam : lam * D ≤ 8 := by
    calc lam * D ≤ lu * D := by gcongr
      _ = D * lu := by ring
      _ ≤ 8 := hDlu
  -- compose the two refinements
  have href : ShadedBody.IsCRefinement u₂ Y u Y ((1 / 2 : NNReal) * D⁻¹) :=
    ShadedBody.IsCRefinement.trans href2 href0
  set c : NNReal := (1 / 2 : NNReal) * D⁻¹ with hc
  have hc0 : c ≠ 0 := mul_ne_zero (by norm_num) (inv_ne_zero hD0)
  have hlam16 : lam ≤ 16 * c := by
    have h1 : (16 : NNReal) * c = 8 * D⁻¹ := by rw [hc, ← mul_assoc]; norm_num
    rw [h1, show (8 : NNReal) * D⁻¹ = 8 / D by rw [div_eq_mul_inv],
      le_div_iff₀ (pos_iff_ne_zero.mpr hD0)]
    exact hDlam
  have hcinv : c⁻¹ ≤ 16 / lam := by
    rw [le_div_iff₀ hlam0]
    calc c⁻¹ * lam ≤ c⁻¹ * (16 * c) := by gcongr
      _ = (c⁻¹ * c) * 16 := by ring
      _ = 16 := by rw [inv_mul_cancel₀ hc0, one_mul]
  have hsq : lam ^ 2 / 16 ≤ c * lam := by
    rw [div_le_iff₀ (by norm_num : (0:NNReal) < 16)]
    calc lam ^ 2 = lam * lam := by ring
      _ ≤ (16 * c) * lam := by gcongr
      _ = c * lam * 16 := by ring
  -- `u₂` is nonempty because it retains a positive share of a positive shading mass
  have hu₂ne : u₂.Nonempty := by
    rcases Finset.eq_empty_or_nonempty u₂ with h | h
    · exfalso
      have h2 := href.2
      rw [h] at h2
      simp only [Finset.sum_empty, nonpos_iff_eq_zero, mul_eq_zero] at h2
      rcases h2 with h1 | h2
      · exact hc0 (by exact_mod_cast h1)
      · exact hmass_pos.ne' h2
    · exact h
  refine ⟨u₂, hu₂u₀.trans hu₀u, hu₂ne, (lam2 : ENNReal), by exact_mod_cast hlam20, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨hlow, hhigh⟩ := hband k hk
    constructor
    · calc ((2 : NNReal) : ENNReal)⁻¹ * (lam2 : ENNReal) * volume (U k).carrier
          ≤ 1 * (lam2 : ENNReal) * volume (U k).carrier := by
            gcongr
            rw [ENNReal.inv_le_one]
            exact_mod_cast (by norm_num : (1 : NNReal) ≤ 2)
        _ = (lam2 : ENNReal) * volume (Y k).carrier := by rw [one_mul]
        _ ≤ volume (Y k).shade := hlow
    · calc volume (U k).shade = volume (Y k).shade := rfl
        _ ≤ 2 * (lam2 : ENNReal) * volume (Y k).carrier := hhigh
        _ = ((2 : NNReal) : ENNReal) * (lam2 : ENNReal) * volume (U k).carrier := by
            push_cast; rfl
  · refine le_trans (ShadedBody.multiplicity_le_of_isCRefinement u Y hc0 href) ?_
    gcongr
    calc ((c : NNReal) : ENNReal)⁻¹ = ((c⁻¹ : NNReal) : ENNReal) := (ENNReal.coe_inv hc0).symm
      _ ≤ ((16 / lam : NNReal) : ENNReal) := by exact_mod_cast hcinv
      _ = 16 / (lam : ENNReal) := by
          rw [ENNReal.coe_div hlam0.ne']; norm_num
  · have hstep := href.coe_mul_fullness_le
    calc ((lam : ENNReal)) ^ 2 / 16 = (((lam ^ 2 / 16 : NNReal)) : ENNReal) := by
          rw [ENNReal.coe_div (by norm_num)]; norm_num
      _ ≤ (((c * lam : NNReal)) : ENNReal) := by exact_mod_cast hsq
      _ = (c : ENNReal) * (lam : ENNReal) := by push_cast; ring
      _ ≤ (c : ENNReal) * (lu : ENNReal) := by gcongr
      _ ≤ (ShadedBody.fullness u₂ Y : ENNReal) := hstep
  · -- cardinality retention, read off the shading mass
    have hupper : ∑ i ∈ u₂, volume (Y i).shade ≤ (u₂.card : ENNReal) * v := by
      calc ∑ i ∈ u₂, volume (Y i).shade
          ≤ ∑ i ∈ u₂, volume (Y i).carrier :=
            Finset.sum_le_sum fun i _ => measure_mono (Y i).shade_subset
        _ = ∑ i ∈ u₂, v := Finset.sum_congr rfl fun i hi => hvol i (hu₂u₀.trans hu₀u hi)
        _ = (u₂.card : ENNReal) * v := by rw [Finset.sum_const, nsmul_eq_mul]
    have hlower : ((lam : ENNReal)) ^ 2 / 16 * (u.card : ENNReal) * v
        ≤ ∑ i ∈ u₂, volume (Y i).shade := by
      refine le_trans ?_ href.2
      rw [hsumshade]
      have hcoe : ((lam : ENNReal)) ^ 2 / 16 ≤ (c : ENNReal) * (lam : ENNReal) := by
        calc ((lam : ENNReal)) ^ 2 / 16 = (((lam ^ 2 / 16 : NNReal)) : ENNReal) := by
              rw [ENNReal.coe_div (by norm_num)]; norm_num
          _ ≤ (((c * lam : NNReal)) : ENNReal) := by exact_mod_cast hsq
          _ = (c : ENNReal) * (lam : ENNReal) := by push_cast; ring
      calc ((lam : ENNReal)) ^ 2 / 16 * (u.card : ENNReal) * v
          ≤ ((c : ENNReal) * (lam : ENNReal)) * (u.card : ENNReal) * v := by gcongr
        _ ≤ ((c : ENNReal) * (lu : ENNReal)) * (u.card : ENNReal) * v := by
            gcongr
        _ = (c : ENNReal) * ((lu : ENNReal) * ((u.card : ENNReal) * v)) := by ring
    have := le_trans hlower hupper
    rwa [ENNReal.mul_le_mul_iff_left hv_pos.ne' hv_top] at this

set_option maxHeartbeats 2000000 in
/-- The fine factor with average fullness, internally density-normalized.

This is the missing fine-side consumer for the product-only B3 interface. -/
theorem multiplicity_le_fine_avg_candidate (hdim : Module.finrank ℝ E = 3)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hKF : FrostmanEstimate.{u} E γ) :
    ∀ e > (0 : ℝ),
    ∃ ηs > (0 : ℝ), ∀ a a' A g : ℝ, 0 ≤ a → 0 ≤ a' →
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ τ : NNReal, δ ≤ τ → τ ≤ 1 →
      ∀ {ι : Type u} {u : Finset ι} (Tτ : Tube τ E) (T : ι → ShadedTube δ E),
        u.Nonempty →
        Tτ.carrier ⊆ Metric.closedBall 0 1 →
        (∀ i ∈ u, (T i).carrier ⊆ Tτ.carrier) →
        (u : Set ι).Pairwise
          (fun i i' => IsEssentiallyDistinct (T i).carrier (T i').carrier) →
        frostmanConstIn u (fun i => (T i).toConvexSpaceBody) Tτ.toConvexSpaceBody
          ≤ (δ : ENNReal) ^ (-a) →
        (δ : ENNReal) ^ g
          ≤ ShadedBody.fullness u (fun i => (T i).toShadedBody) →
        (fineFactor.C : ENNReal) * ((2 : NNReal) : ENNReal) ^ 2
            * (δ : ENNReal) ^ ηs
          ≤ (δ : ENNReal) ^ (2 * g) / 16 →
        ((δ : ENNReal) ^ (2 * g) / 16)⁻¹ * (δ : ENNReal) ^ (-a)
          ≤ (δ : ENNReal) ^ (-a') →
        16 / (δ : ENNReal) ^ g *
            ((fineFactor.C : ENNReal) ^ 2 * ((2 : NNReal) : ENNReal) ^ 2
              * (δ : ENNReal) ^ (-e)
              * (δ : ENNReal) ^ (-(1 - γ / 2) * a'))
          ≤ (δ : ENNReal) ^ (-A) →
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (δ : ENNReal) ^ (-A)
            * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
            * ((u.card : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^
                (1 - γ / 2) := by
  intro e he
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by
    rw [hdim]
    norm_num)
  obtain ⟨ηs, hηs, hraw⟩ := multiplicity_le_fine_frostmanLoss hdim hγ0 hγ1 hKF e he
  refine ⟨ηs, hηs, ?_⟩
  intro a a' A g ha ha'
  filter_upwards [hraw (2 : NNReal) (by norm_num) a' ha',
    self_mem_nhdsWithin] with δ hrawδ hδ0
  intro τ hδτ hτ1 ι u Tτ T hu hparentBall hsub hED hF hfull hfullPay hFrostPay hfinalPay
  have hδE0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδEtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  set lam : NNReal := δ ^ g with hlam
  have hlam0 : 0 < lam := by
    rw [hlam]
    exact NNReal.rpow_pos hδ0
  have hlamE : (lam : ENNReal) = (δ : ENNReal) ^ g := by
    rw [hlam, ENNReal.coe_rpow_of_ne_zero hδ0.ne']
  obtain ⟨u₂, hu₂u, hu₂ne, μ₀, hμ₀, hbracket, hmult, hfull₂, hcard₂⟩ :=
    exists_internalDensityNormalization (E := E) (ι := ι) (τ := δ) (u := u)
      (lam := lam) hδ0 T hu hlam0
      (by simpa only [hlamE] using hfull)
  have hpow : (lam : ENNReal) ^ 2 = (δ : ENNReal) ^ (2 * g) := by
    rw [hlamE, sq, ← ENNReal.rpow_add _ _ hδE0 hδEtop]
    congr 1
    ring
  have hfullFine : (fineFactor.C : ENNReal) * ((2 : NNReal) : ENNReal) ^ 2
      * (δ : ENNReal) ^ ηs
      ≤ ShadedBody.fullness u₂ (fun i => (T i).toShadedBody) := by
    calc
      (fineFactor.C : ENNReal) * ((2 : NNReal) : ENNReal) ^ 2
            * (δ : ENNReal) ^ _
          ≤ (δ : ENNReal) ^ (2 * g) / 16 := hfullPay
      _ = (lam : ENNReal) ^ 2 / 16 := by rw [hpow]
      _ ≤ ShadedBody.fullness u₂ (fun i => (T i).toShadedBody) := hfull₂
  have hfine : IsFineFibre (2 : NNReal) μ₀ ηs u₂ Tτ T := by
    exact
      { density_pos := hμ₀
        nonempty := hu₂ne
        parent_ball := hparentBall
        subset_parent := fun i hi => hsub i (hu₂u hi)
        essDistinct := hED.mono (Finset.coe_subset.mpr hu₂u)
        shade_comparable := hbracket
        fullness := hfullFine }
  obtain ⟨i₀, hi₀⟩ := hu
  set v : ENNReal := volume (T i₀).carrier with hv
  have hvol : ∀ i ∈ u, volume ((T i).toConvexSpaceBody).carrier = v := by
    intro i _
    simpa [hv] using
      _root_.Tube.volume_carrier_eq_volume_carrier (T i).toTube (T i₀).toTube
  have hparent : ∀ i ∈ u, (T i).toConvexSpaceBody ≤ Tτ.toConvexSpaceBody :=
    fun i hi => hsub i hi
  set κ : ENNReal := (δ : ENNReal) ^ (2 * g) / 16 with hκ
  have hpow0 : (δ : ENNReal) ^ (2 * g) ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ0) hδEtop).ne'
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact (ENNReal.div_pos hpow0 (by norm_num)).ne'
  have hcardκ : κ * (u.card : ENNReal) ≤ (u₂.card : ENNReal) := by
    rw [hκ, ← hpow]
    exact hcard₂
  have htransfer := frostmanConstIn_subfamily_le (v := v) (κ := κ)
    (s := u) (s' := u₂) (W := fun i => (T i).toConvexSpaceBody)
    (K := Tτ.toConvexSpaceBody) ⟨i₀, hi₀⟩ hvol hparent hu₂u hκ0 hcardκ
  have hF₂ : frostmanConstIn u₂ (fun i => (T i).toConvexSpaceBody) Tτ.toConvexSpaceBody
      ≤ (δ : ENNReal) ^ (-a') := by
    calc
      frostmanConstIn u₂ (fun i => (T i).toConvexSpaceBody) Tτ.toConvexSpaceBody
          ≤ κ⁻¹ * frostmanConstIn u (fun i => (T i).toConvexSpaceBody)
              Tτ.toConvexSpaceBody := htransfer
      _ ≤ κ⁻¹ * (δ : ENNReal) ^ (-a) := by gcongr
      _ ≤ (δ : ENNReal) ^ (-a') := by simpa only [hκ] using hFrostPay
  have hraw₂ := hrawδ τ hδτ hτ1 Tτ T hfine hF₂
  have hcardMono :
      ((u₂.card : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^
          (1 - γ / 2)
        ≤ ((u.card : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^
          (1 - γ / 2) := by
    apply ENNReal.rpow_le_rpow
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hu₂u) bot_le
    · linarith
  calc
    ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
        ≤ 16 / (lam : ENNReal) *
            ShadedBody.multiplicity u₂ (fun i => (T i).toShadedBody) := hmult
    _ ≤ 16 / (lam : ENNReal) *
          ((fineFactor.C : ENNReal) ^ 2 * ((2 : NNReal) : ENNReal) ^ 2
            * (δ : ENNReal) ^ (-e) * (δ : ENNReal) ^ (-(1 - γ / 2) * a')
            * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
            * ((u₂.card : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^
                (1 - γ / 2)) := by gcongr
    _ = (16 / (δ : ENNReal) ^ g *
          ((fineFactor.C : ENNReal) ^ 2 * ((2 : NNReal) : ENNReal) ^ 2
            * (δ : ENNReal) ^ (-e) * (δ : ENNReal) ^ (-(1 - γ / 2) * a')))
          * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u₂.card : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^
              (1 - γ / 2) := by rw [hlamE]; ring
    _ ≤ (δ : ENNReal) ^ (-A) * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^
              (1 - γ / 2) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hfinalPay bot_le) hcardMono bot_le bot_le

/-! ### The loss ledger of the internal normalization -/

/-- **Absorbing a fixed constant into a positive power of `δ`.**

The one-line eventual statement every entry of the internal-normalization ledger reduces to.
`K` is any finite constant — in the applications a fixed constant times
`Kakeya.ml1Boot.fineFactor.C` — and `c` any positive exponent. -/
theorem absorb_eventually {c : ℝ} (hc : 0 < c) {K : ENNReal} (hK : K ≠ ⊤) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), K * (δ : ENNReal) ^ c ≤ 1 := by
  rcases eq_or_ne K 0 with hK0 | hK0
  · filter_upwards with δ
    simp [hK0]
  · have hinv : 0 < K⁻¹ := by
      rw [ENNReal.inv_pos]; exact hK
    filter_upwards [ENNReal.eventually_coe_rpow_le_of_pos (ρ := c) hc hinv] with δ hδ
    calc K * (δ : ENNReal) ^ c ≤ K * K⁻¹ := by
          exact mul_le_mul_of_nonneg_left hδ (by positivity)
      _ = 1 := ENNReal.mul_inv_cancel hK0 hK

/-- **The scale facts of the middle-factor assembly**: `δ ^ ε` eventually undercuts any
prescribed radius and the threshold `1/4` of
`Kakeya.ml1Boot.exists_normalizedMiddleData`.  This is
`Kakeya.ml1Boot.middleFactor_eventually` minus the three constant absorptions, which the
average-fullness route pays at different exponents through
`Kakeya.ml1Boot.absorb_eventually`. -/
theorem middleAvg_scale_eventually {ε : ℝ} (hε0 : 0 < ε) {r : NNReal} (hr0 : 0 < r) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), 0 < δ ∧ δ ^ ε < r ∧ δ ^ ε ≤ 1 / 4 ∧
      δ ^ ε ≤ (1 / 4 : NNReal) ^ (1 / (5 * ε)) := by
  have f1 : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), (0 : NNReal) < δ := self_mem_nhdsWithin
  have hcoet : Tendsto (fun δ : NNReal => (δ : ℝ)) (𝓝[>] (0 : NNReal)) (𝓝 (0 : ℝ)) := by
    simpa using ((NNReal.continuous_coe.tendsto (0 : NNReal)).mono_left nhdsWithin_le_nhds)
  have htendR : Tendsto (fun δ : NNReal => (δ : ℝ) ^ ε) (𝓝[>] (0 : NNReal)) (𝓝 (0 : ℝ)) :=
    hcoet.rpow_const_nhds_zero hε0
  have f2 : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), δ ^ ε < r := by
    have h_ev : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), (δ : ℝ) ^ ε < (r : ℝ) :=
      htendR.eventually (eventually_lt_nhds (by exact_mod_cast hr0))
    filter_upwards [h_ev] with δ hδ
    exact_mod_cast hδ
  have f3 : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), δ ^ ε ≤ 1 / 4 := by
    have h_ev : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), (δ : ℝ) ^ ε < (1 / 4 : ℝ) :=
      htendR.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [h_ev] with δ hδ
    have hδNN : (δ : NNReal) ^ ε < (1 / 4 : NNReal) := by exact_mod_cast hδ
    exact le_of_lt hδNN
  have f3' : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal),
      δ ^ ε ≤ (1 / 4 : NNReal) ^ (1 / (5 * ε)) := by
    have hpos : (0 : ℝ) < ((1 / 4 : NNReal) ^ (1 / (5 * ε)) : NNReal) := by
      have h : (0 : NNReal) < (1 / 4 : NNReal) ^ (1 / (5 * ε)) :=
        NNReal.rpow_pos (by rw [← NNReal.coe_lt_coe]; push_cast; norm_num)
      exact_mod_cast h
    have h_ev : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal),
        (δ : ℝ) ^ ε < ((1 / 4 : NNReal) ^ (1 / (5 * ε)) : NNReal) :=
      htendR.eventually (eventually_lt_nhds hpos)
    filter_upwards [h_ev] with δ hδ
    have hδNN : (δ : NNReal) ^ ε < (1 / 4 : NNReal) ^ (1 / (5 * ε)) := by exact_mod_cast hδ
    exact le_of_lt hδNN
  filter_upwards [f1, f2, f3, f3'] with δ h1 h2 h3 h3'
  exact ⟨h1, h2, h3, h3'⟩

/-- **The exponents at which the average-fullness middle factor runs.**

Everything is read off `Kakeya.ml1Boot.middleFactor_numerics` plus the single extra
smallness hypothesis `η(γ) ≤ ε η₀ / 4`, a factor-two strengthening of the package's own
`Kakeya.ml1Boot.Params.EtaGammaSpec.etaGammaLeRescale` (`η(γ) ≤ ε η₀ / 2`) and hence
satisfiable by construction, not a new structural demand.

Writing `a = η_{j-1}`, `aλ = a γ₀ / β₀` and `e₀ = 3 η₀ / 2 + 2 η(γ)` — the Frostman loss
exponent the internal normalization inflates `η₀` to — the clauses are:

* `0 ≤ e₀` and `a + e₀ / ε ≤ 5 aλ / ε`: the rescaled Frostman exponent `aF = 5 aλ / ε` still
  dominates the inflated loss;
* `0 < 10 (aλ - a) - η(γ)`: the multiplicity room absorbs the `16 / λ` retention loss of
  `Kakeya.ml1Boot.exists_internalDensityNormalization`.  This is the one clause that needs
  `Kakeya.ml1Boot.Params.Spec.ninetySixEpsLe`: `aλ - a = a g₀ / β₀ ≥ 96 ε a`;
* `0 < ε aλ - 2 η(γ)`: the fullness room absorbs the `λ² / 16` retention loss;
* `0 < 5 aλ - ε a - e₀`: the Frostman room absorbs the inflated `e₀`. -/
theorem middleAvg_numerics {β γ₀ : ℝ} (hβ0 : 0 ≤ β) (hγ₀ : γ₀ ∈ Set.Ioc β 1)
    {ηKF ηKKT : ℝ → ℝ} {p : Params} (hp : p.Spec β γ₀) (hpη : p.EtaGammaSpec β γ₀ ηKF ηKKT)
    {γ : ℝ} (hγ : γ ∈ Set.Icc γ₀ 1) {j : ℕ} (hj1 : 1 ≤ j) (hjN : j ≤ p.N)
    (hηΓ4 : p.ηGamma γ ≤ p.ε * p.η 0 / 4) :
    0 ≤ 3 * p.η 0 / 2 + 2 * p.ηGamma γ ∧
      p.η (j - 1) + (3 * p.η 0 / 2 + 2 * p.ηGamma γ) / p.ε
        ≤ 5 * (p.η (j - 1) * γ₀ / betaPrime β γ₀) / p.ε ∧
      0 < 10 * (p.η (j - 1) * γ₀ / betaPrime β γ₀ - p.η (j - 1)) - p.ηGamma γ ∧
      0 < p.ε * (p.η (j - 1) * γ₀ / betaPrime β γ₀) - 2 * p.ηGamma γ ∧
      0 < 5 * (p.η (j - 1) * γ₀ / betaPrime β γ₀) - p.ε * p.η (j - 1)
        - (3 * p.η 0 / 2 + 2 * p.ηGamma γ) := by
  set b0 : ℝ := betaPrime β γ₀ with hb0
  set a : ℝ := p.η (j - 1) with ha
  set e : ℝ := p.ε with he
  set gΓ : ℝ := p.ηGamma γ with hgΓ
  have hb0spec := betaPrime_spec hβ0 γ₀ hγ₀
  have hb0pos : 0 < b0 := hb0spec.1
  have hb0ltγ : b0 < γ₀ := hb0spec.2
  have hγ0le1 : γ₀ ≤ 1 := hγ₀.2
  have hb0le1 : b0 ≤ 1 := le_of_lt (lt_of_lt_of_le hb0ltγ hγ0le1)
  have hepos : 0 < e := hp.epsPos
  have hele1 : e ≤ 1 := hp.epsLeOne
  have hη0pos : 0 < p.η 0 := hp.etaZeroPos
  have hsub : j - 1 ≤ p.N := le_trans (Nat.sub_le j 1) hjN
  have hmonoE : p.η 0 ≤ a :=
    hp.etaMono (Set.mem_Iic.mpr (Nat.zero_le _)) (Set.mem_Iic.mpr hsub) (Nat.zero_le _)
  have hapos : 0 < a := lt_of_lt_of_le hη0pos hmonoE
  have hgΓpos : 0 < gΓ := hpη.etaGammaPos γ hγ
  have hgap : 96 * e ≤ γ₀ - b0 := by
    have := hp.ninetySixEpsLe
    rw [gap] at this
    exact this
  obtain ⟨haL0, ha_lt, -, hFroom, -, -⟩ := middleFactor_numerics hβ0 hγ₀ hp hpη hγ hj1 hjN
  set aL : ℝ := a * γ₀ / b0 with haL
  have haLpos : 0 < aL := haL0
  have haltaL : a < aL := ha_lt
  -- the loss exponent
  have hgΓa : gΓ ≤ a / 4 := by
    have h1 : gΓ ≤ e * p.η 0 / 4 := hηΓ4
    nlinarith [hη0pos, hmonoE, hele1, hepos]
  have he₀0 : 0 ≤ 3 * p.η 0 / 2 + 2 * gΓ := by linarith
  have hea : e * a ≤ a := by nlinarith [hapos, hele1, hepos]
  -- the Frostman room, in the multiplied form
  have hfr : e * a + (3 * p.η 0 / 2 + 2 * gΓ) < 5 * aL := by
    nlinarith [hmonoE, hgΓa, haltaL, hapos, hea]
  refine ⟨he₀0, ?_, ?_, ?_, by linarith⟩
  · have hrw : a + (3 * p.η 0 / 2 + 2 * gΓ) / e
        = (e * a + (3 * p.η 0 / 2 + 2 * gΓ)) / e := by field_simp
    rw [hrw, div_le_div_iff_of_pos_right hepos]
    linarith
  · -- the multiplicity room
    have hkey : 96 * e * a ≤ aL - a := by
      have hexp : aL - a = a * (γ₀ - b0) / b0 := by
        rw [haL]; field_simp
      rw [hexp]
      rw [le_div_iff₀ hb0pos]
      have h96 : (0 : ℝ) ≤ 96 * e * a := by positivity
      calc 96 * e * a * b0 ≤ 96 * e * a * 1 := by gcongr
        _ = a * (96 * e) := by ring
        _ ≤ a * (γ₀ - b0) := by gcongr
    nlinarith [hkey, hgΓa, hapos, hepos, hele1]
  · -- the fullness room
    nlinarith [haltaL, hgΓa, hapos, hepos, hele1, hmonoE]


/-! ### The endgame algebra with a free loss constant -/

/-- **The middle-factor endgame, with the loss carried as one opaque constant.**

`Kakeya.ml1Boot.middle_le_of_rescaled` reads its loss in the shape
`C₂ Λ²` fixed by the two-sided bracket constant `Λ`.  The average-fullness route pays a
different bill — the constant of `Kakeya.ml1Boot.exists_normalizedMiddleData` at the internal
`Λ = 2` *times* the `16 / λ` retention loss of
`Kakeya.ml1Boot.exists_internalDensityNormalization`, which is a power of `δ` and not a
constant — so it needs the same algebra with `K` left free.  The proof is unchanged: the
original never used the shape of `K`, only `habs` and `hM`. -/
theorem middle_le_of_rescaled_const {ε aL a γ : ℝ} {K : ENNReal} {δ δt : NNReal} (hδ0 : 0 < δ)
    (hsep : δt ≤ δ ^ ε) (hγ1 : γ ≤ 1) (haL0 : 0 ≤ aL) (hε0 : 0 < ε)
    (habs : K * (δ : ENNReal) ^ (10 * (aL - a)) ≤ 1)
    {M M' : ENNReal} {N N' : ℕ} (hNN : N' ≤ N)
    (hM : M ≤ K * M')
    (hM' : M' ≤ (δt : ENNReal) ^ (10 * aL / ε) * (δt : ENNReal) ^ (-2 * γ)
      * ((N' : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) :
    M ≤ (δ : ENNReal) ^ (10 * a) * (δt : ENNReal) ^ (-2 * γ)
      * ((N : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  -- Key scalar bound: the fixed constant is absorbed into `δ ^ (10 a)`.
  have hkey : K * (δt : ENNReal) ^ (10 * aL / ε) ≤ (δ : ENNReal) ^ (10 * a) := by
    have hx : (0 : ℝ) ≤ 10 * aL / ε :=
      div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) haL0) (le_of_lt hε0)
    have hsep1 : (δt : ENNReal) ^ (10 * aL / ε) ≤ (δ : ENNReal) ^ (ε * (10 * aL / ε)) :=
      coe_rpow_le_rpow_mul_of_sep hδ0 hsep hx
    have hεx : ε * (10 * aL / ε) = 10 * aL := by
      field_simp [ne_of_gt hε0]
    have hδE : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδ0)
    have hδEt : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hsplit : (δ : ENNReal) ^ (10 * aL) =
        (δ : ENNReal) ^ (10 * (aL - a)) * (δ : ENNReal) ^ (10 * a) := by
      rw [← ENNReal.rpow_add (x := (δ : ENNReal)) (10 * (aL - a)) (10 * a) hδE hδEt]
      congr 1
      ring
    have h_abs : K * (δ : ENNReal) ^ (10 * (aL - a)) ≤ 1 := by
      exact habs
    calc
      K * (δt : ENNReal) ^ (10 * aL / ε)
          ≤ K * (δ : ENNReal) ^ (ε * (10 * aL / ε)) := by
            exact mul_le_mul_of_nonneg_left hsep1 bot_le
      _ = K * (δ : ENNReal) ^ (10 * aL) := by rw [hεx]
      _ = K * ((δ : ENNReal) ^ (10 * (aL - a)) * (δ : ENNReal) ^ (10 * a)) := by rw [hsplit]
      _ = (K * (δ : ENNReal) ^ (10 * (aL - a))) * (δ : ENNReal) ^ (10 * a) := by ac_rfl
      _ ≤ 1 * (δ : ENNReal) ^ (10 * a) := by
            exact mul_le_mul_of_nonneg_right (a := (δ : ENNReal) ^ (10 * a)) h_abs bot_le
      _ = (δ : ENNReal) ^ (10 * a) := by simp
  -- Bracket monotonicity in the index count `N' ≤ N`.
  have hbr : ((N' : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
      ≤ ((N : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    have hNN' : (N' : ENNReal) ≤ (N : ENNReal) := by exact_mod_cast hNN
    have hbase : (N' : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)
        ≤ (N : ENNReal) * (δt : ENNReal) ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right (a := (δt : ENNReal) ^ (2 : ℕ)) hNN' bot_le
    have hnonneg : (0 : ℝ) ≤ 1 - γ / 2 := by linarith
    exact ENNReal.rpow_le_rpow hbase hnonneg
  -- Assemble.
  calc
    M ≤ K * M' := by exact hM
    _ ≤ K * ((δt : ENNReal) ^ (10 * aL / ε) * (δt : ENNReal) ^ (-2 * γ)
        * ((N' : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
          exact mul_le_mul_of_nonneg_left hM' bot_le
    _ = (K * (δt : ENNReal) ^ (10 * aL / ε)) * (δt : ENNReal) ^ (-2 * γ)
        * ((N' : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by ac_rfl
    _ ≤ (δ : ENNReal) ^ (10 * a) * (δt : ENNReal) ^ (-2 * γ)
        * ((N : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          have h1 : (K * (δt : ENNReal) ^ (10 * aL / ε)) * (δt : ENNReal) ^ (-2 * γ)
              ≤ (δ : ENNReal) ^ (10 * a) * (δt : ENNReal) ^ (-2 * γ) := by
            exact mul_le_mul_of_nonneg_right (a := (δt : ENNReal) ^ (-2 * γ)) hkey bot_le
          exact mul_le_mul h1 hbr bot_le bot_le

/-! ### The middle factor at average fullness -/







end Internal

end ml1Boot

end Kakeya

end
