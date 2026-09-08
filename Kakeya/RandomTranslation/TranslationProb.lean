/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.Erosion
public import Kakeya.RandomTranslation.Measure

/-!
# The canonical uniform-translation instance and its probability bounds

Sampling `t` uniformly from `B(0,1) ⊆ E` and translating by `t` (or by `ρ • t`)
is the only instance of `HasUniformTranslation` the development uses. This file
builds it, together with the two probability estimates it supports: the crude
point-in-set bound `prob_smul_add_in_set_self`, and the sharp per-tube bound
`prob_tube_translate_subset_le`, which is a factor `r` better because a tube has
a unit-length core.
-/

@[expose] public section

open MeasureTheory Metric ProbabilityTheory

namespace Kakeya

/-! ### A canonical instance: uniform translation in `B(0, 1)`

The minimal construction needed to instantiate `HasUniformTranslation`:
sample `t` uniformly from `B(0, 1) ⊆ E` and let `R(t)` be the translation
`x ↦ t + x`. Translations are affine isometries, and the bound
`prob_point_in_set` reduces to translation-invariance of Lebesgue measure
plus the trivial inclusion `(K - x) ∩ B(0,1) ⊆ K - x`. -/

section UniformTranslationInstance

open scoped ENNReal

variable
  (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The uniform probability measure on the closed unit ball in `E`. -/
noncomputable def uniformBallMeasure : Measure E :=
  (volume (Metric.closedBall (0 : E) 1))⁻¹ • volume.restrict (Metric.closedBall (0 : E) 1)

private lemma volume_unitBall_pos :
    (0 : ℝ≥0∞) < volume (Metric.closedBall (0 : E) 1) :=
  Metric.measure_closedBall_pos volume 0 one_pos

private lemma volume_unitBall_ne_top :
    volume (Metric.closedBall (0 : E) 1) ≠ ⊤ :=
  ne_of_lt measure_closedBall_lt_top

private lemma volume_unitBall_ne_zero :
    volume (Metric.closedBall (0 : E) 1) ≠ 0 :=
  ne_of_gt (volume_unitBall_pos E)

instance instIsProbabilityUniformBall : IsProbabilityMeasure (uniformBallMeasure E) := by
  refine ⟨?_⟩
  change ((volume (Metric.closedBall (0 : E) 1))⁻¹ •
        volume.restrict (Metric.closedBall (0 : E) 1)) Set.univ = 1
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (volume_unitBall_ne_zero E) (volume_unitBall_ne_top E)

/-- The canonical uniform random translation on `E`: a translation by a point
sampled uniformly from the closed unit ball. -/
noncomputable instance instHasUniformTranslationSelf : HasUniformTranslation E E where
  measure := uniformBallMeasure E
  shift t := ⟨t⟩
  measurable_apply x := by
    change Measurable (fun t : E => t + x)
    exact measurable_id.add_const x
  uniformConstant := (volume.real (Metric.closedBall (0 : E) 1))⁻¹
  uniformConstantPos := by
    refine inv_pos.mpr ?_
    rw [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨volume_unitBall_pos E, measure_closedBall_lt_top⟩
  prob_point_in_set := by
    intro x K hK hKtop
    -- Show the goal in concrete form, then compute.
    change (uniformBallMeasure E) {ω : E | ω + x ∈ K} ≤
        ENNReal.ofReal (volume.real (Metric.closedBall (0 : E) 1))⁻¹ * volume K
    have hpre_eq : {ω : E | ω + x ∈ K} = (fun t : E => t + x) ⁻¹' K := rfl
    rw [hpre_eq]
    have hmeas_pre : MeasurableSet ((fun t : E => t + x) ⁻¹' K) :=
      hK.preimage (measurable_id.add_const x)
    -- Compute uniformBallMeasure on this preimage.
    have hμ : uniformBallMeasure E ((fun t : E => t + x) ⁻¹' K)
        = (volume (Metric.closedBall (0 : E) 1))⁻¹
            * volume ((fun t : E => t + x) ⁻¹' K ∩ Metric.closedBall (0 : E) 1) := by
      change ((volume (Metric.closedBall (0 : E) 1))⁻¹ •
            volume.restrict (Metric.closedBall (0 : E) 1))
              ((fun t : E => t + x) ⁻¹' K) = _
      rw [Measure.smul_apply, Measure.restrict_apply hmeas_pre, smul_eq_mul]
    -- Translation invariance: vol((·+x)⁻¹ K) = vol K.
    have htrans : volume ((fun t : E => t + x) ⁻¹' K) = volume K := by
      have : ((fun t : E => t + x) ⁻¹' K) = (fun t : E => x + t) ⁻¹' K := by
        ext t; simp [add_comm]
      rw [this]
      exact measure_preimage_add volume x K
    -- Bound vol((·+x)⁻¹K ∩ B) ≤ vol K.
    have hbound : volume ((fun t : E => t + x) ⁻¹' K ∩ Metric.closedBall (0 : E) 1)
        ≤ volume K := by
      calc volume ((fun t : E => t + x) ⁻¹' K ∩ Metric.closedBall (0 : E) 1)
          ≤ volume ((fun t : E => t + x) ⁻¹' K) := measure_mono Set.inter_subset_left
        _ = volume K := htrans
    rw [hμ]
    calc
      (volume (Metric.closedBall (0 : E) 1))⁻¹ *
          volume ((fun t : E => t + x) ⁻¹' K ∩ Metric.closedBall (0 : E) 1)
          ≤ (volume (Metric.closedBall (0 : E) 1))⁻¹ * volume K := by
        gcongr
      _ = ENNReal.ofReal (volume.real (Metric.closedBall (0 : E) 1))⁻¹ * volume K := by
        rw [ENNReal.ofReal_inv_of_pos]
        · rw [Measure.real, ENNReal.ofReal_toReal (volume_unitBall_ne_top E)]
        · rw [Measure.real, ENNReal.toReal_pos_iff]
          exact ⟨volume_unitBall_pos E, measure_closedBall_lt_top⟩

/-- **ρ-scaled point-in-set probability bound** for the canonical translation
instance.

If `0 < ρ`, `x ∈ E`, and `K` is a measurable set of finite volume, then
sampling `ω` uniformly from `B(0, 1) ⊆ E` and computing `ρ • ω + x`
lands in `K` with probability at most `(ρ^n)⁻¹ · (vol B₁)⁻¹ · vol K`,
where `n = finrank ℝ E`.

This is used in the proof of `RandomTranslation.exists_refinement` (GWZ
Lemma 7.6): there `v_j := ρ • ω_j` plays the role of a uniform random
translation of size `ρ`.

The bound holds for all `ρ > 0`; no `ρ ≤ 1` hypothesis is needed. -/
lemma prob_smul_add_in_set_self
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (x : E) {K : Set E} (hK : MeasurableSet K)
    (hKtop : volume K ≠ ⊤) :
    (uniformBallMeasure E) {ω : E | ρ • ω + x ∈ K} ≤
      ENNReal.ofReal ((ρ ^ Module.finrank ℝ E)⁻¹ *
        (volume.real (Metric.closedBall (0 : E) 1))⁻¹) * volume K := by
  have hC_nonneg :
      0 ≤ (ρ ^ Module.finrank ℝ E)⁻¹ *
        (volume.real (Metric.closedBall (0 : E) 1))⁻¹ := by positivity
  have hLHS_ne_top :
      uniformBallMeasure E {ω : E | ρ • ω + x ∈ K} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  have hRHS_ne_top :
      ENNReal.ofReal ((ρ ^ Module.finrank ℝ E)⁻¹ *
          (volume.real (Metric.closedBall (0 : E) 1))⁻¹) * volume K ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop
  refine (ENNReal.toReal_le_toReal hLHS_ne_top hRHS_ne_top).mp ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_nonneg]
  change ((uniformBallMeasure E) {ω : E | ρ • ω + x ∈ K}).toReal ≤
    (ρ ^ Module.finrank ℝ E)⁻¹ *
      (volume.real (Metric.closedBall (0 : E) 1))⁻¹ * volume.real K
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hρ_ne : ρ ≠ 0 := ne_of_gt hρ_pos
  -- Identify the set as a preimage.
  have hpre_eq : {ω : E | ρ • ω + x ∈ K} = (fun t : E => ρ • t + x) ⁻¹' K := rfl
  rw [hpre_eq]
  -- Measurability of the preimage.
  have hmeas_f : Measurable (fun t : E => ρ • t + x) :=
    (measurable_const_smul ρ).add_const x
  have hmeas_pre : MeasurableSet ((fun t : E => ρ • t + x) ⁻¹' K) :=
    hK.preimage hmeas_f
  -- Compute uniformBallMeasure on this preimage.
  have hμ : uniformBallMeasure E ((fun t : E => ρ • t + x) ⁻¹' K)
      = (volume (Metric.closedBall (0 : E) 1))⁻¹
          * volume ((fun t : E => ρ • t + x) ⁻¹' K
              ∩ Metric.closedBall (0 : E) 1) := by
    change ((volume (Metric.closedBall (0 : E) 1))⁻¹ •
          volume.restrict (Metric.closedBall (0 : E) 1))
            ((fun t : E => ρ • t + x) ⁻¹' K) = _
    rw [Measure.smul_apply, Measure.restrict_apply hmeas_pre, smul_eq_mul]
  -- Decompose the preimage: f = (· + x) ∘ (ρ • ·).
  have hpre_decomp : (fun t : E => ρ • t + x) ⁻¹' K
      = (fun t : E => ρ • t) ⁻¹' ((fun t : E => t + x) ⁻¹' K) := rfl
  -- Translation invariance.
  have htrans : volume ((fun t : E => t + x) ⁻¹' K) = volume K := by
    have heq : ((fun t : E => t + x) ⁻¹' K) = (fun t : E => x + t) ⁻¹' K := by
      ext t; simp [add_comm]
    rw [heq]
    exact measure_preimage_add volume x K
  -- Scaling invariance: vol((ρ • ·)⁻¹ S) = ofReal |(ρ^n)⁻¹| * vol S.
  have hscale : volume ((fun t : E => ρ • t) ⁻¹' ((fun t : E => t + x) ⁻¹' K))
      = ENNReal.ofReal |(ρ ^ n)⁻¹| *
          volume ((fun t : E => t + x) ⁻¹' K) := by
    exact MeasureTheory.Measure.addHaar_preimage_smul volume hρ_ne _
  -- Combine: vol(f⁻¹ K) = ofReal |(ρ^n)⁻¹| * vol K.
  have hpre_vol : volume ((fun t : E => ρ • t + x) ⁻¹' K)
      = ENNReal.ofReal |(ρ ^ n)⁻¹| * volume K := by
    rw [hpre_decomp, hscale, htrans]
  -- Bound: vol(f⁻¹ K ∩ B₁) ≤ vol(f⁻¹ K) = ofReal |(ρ^n)⁻¹| * vol K.
  have hbound : volume ((fun t : E => ρ • t + x) ⁻¹' K
        ∩ Metric.closedBall (0 : E) 1)
      ≤ ENNReal.ofReal |(ρ ^ n)⁻¹| * volume K := by
    calc volume ((fun t : E => ρ • t + x) ⁻¹' K
            ∩ Metric.closedBall (0 : E) 1)
        ≤ volume ((fun t : E => ρ • t + x) ⁻¹' K) :=
          measure_mono Set.inter_subset_left
      _ = ENNReal.ofReal |(ρ ^ n)⁻¹| * volume K := hpre_vol
  -- Now substitute.
  rw [hμ]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  -- Rearrange the RHS to put (vol B₁)⁻¹ first.
  have hpos_inv : 0 ≤ (volume.real (Metric.closedBall (0 : E) 1))⁻¹ := by
    have : 0 ≤ volume.real (Metric.closedBall (0 : E) 1) :=
      ENNReal.toReal_nonneg
    positivity
  rw [show (ρ ^ n)⁻¹ * (volume.real (Metric.closedBall (0 : E) 1))⁻¹ *
        volume.real K
      = (volume.real (Metric.closedBall (0 : E) 1))⁻¹ *
          ((ρ ^ n)⁻¹ * volume.real K) by ring]
  refine mul_le_mul_of_nonneg_left ?_ hpos_inv
  -- Goal: (vol(f⁻¹ K ∩ B₁)).toReal ≤ (ρ^n)⁻¹ * vol K.toReal.
  have hofReal_ne_top : ENNReal.ofReal |(ρ ^ n)⁻¹| ≠ ⊤ := ENNReal.ofReal_ne_top
  have hrhs_ne_top : ENNReal.ofReal |(ρ ^ n)⁻¹| * volume K ≠ ⊤ :=
    ENNReal.mul_ne_top hofReal_ne_top hKtop
  have h1 : (volume ((fun t : E => ρ • t + x) ⁻¹' K
        ∩ Metric.closedBall (0 : E) 1)).toReal
      ≤ (ENNReal.ofReal |(ρ ^ n)⁻¹| * volume K).toReal :=
    ENNReal.toReal_mono hrhs_ne_top hbound
  have habs_nn : 0 ≤ |(ρ ^ n)⁻¹| := abs_nonneg _
  have h2 : (ENNReal.ofReal |(ρ ^ n)⁻¹| * volume K).toReal
      = |(ρ ^ n)⁻¹| * volume.real K := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal habs_nn]
    rfl
  have hrho_n_pos : 0 < ρ ^ n := pow_pos hρ_pos n
  have habs_eq : |(ρ ^ n)⁻¹| = (ρ ^ n)⁻¹ := abs_of_pos (inv_pos.mpr hrho_n_pos)
  have hfinal : (volume ((fun t : E => ρ • t + x) ⁻¹' K
        ∩ Metric.closedBall (0 : E) 1)).toReal
      ≤ (ρ ^ n)⁻¹ * volume.real K := by
    have := h1
    rw [h2, habs_eq] at this
    exact this
  exact hfinal

/-- Scalar identity behind `prob_tube_translate_subset_le`: the Jacobian `(r ^ (m+1))⁻¹` of the
scaling, times the erosion constant, times the erosion gain `r`, is `C / r ^ m`.

Stated with the exponent in the form `m + 1` so that no natural subtraction appears. -/
private lemma ofReal_inv_pow_succ_mul_coe_mul_ofReal (C : NNReal) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ENNReal.ofReal ((r ^ (m + 1))⁻¹) * (C : ENNReal) * ENNReal.ofReal r
      = ENNReal.ofReal ((C : ℝ) / r ^ m) := by
  have hpos : 0 < (r ^ (m + 1))⁻¹ := inv_pos.mpr (pow_pos hr (m + 1))
  have h_nonneg_inv : 0 ≤ (r ^ (m + 1))⁻¹ := le_of_lt hpos
  have h_nonneg_prod : 0 ≤ ((r ^ (m + 1))⁻¹) * (C : ℝ) := by
    nlinarith [show 0 ≤ (C : ℝ) from NNReal.coe_nonneg C]
  have hC : (C : ENNReal) = ENNReal.ofReal (C : ℝ) := (ENNReal.ofReal_coe_nnreal (p := C)).symm
  calc
    ENNReal.ofReal ((r ^ (m + 1))⁻¹) * (C : ENNReal) * ENNReal.ofReal r
        = ENNReal.ofReal ((r ^ (m + 1))⁻¹) * ENNReal.ofReal (C : ℝ) * ENNReal.ofReal r := by
      rw [hC]
    _ = ENNReal.ofReal (((r ^ (m + 1))⁻¹) * (C : ℝ)) * ENNReal.ofReal r := by
      rw [ENNReal.ofReal_mul h_nonneg_inv]
    _ = ENNReal.ofReal ((((r ^ (m + 1))⁻¹) * (C : ℝ)) * r) := by
      rw [ENNReal.ofReal_mul h_nonneg_prod]
    _ = ENNReal.ofReal ((C : ℝ) / r ^ m) := by
      congr 1
      field_simp [hr.ne', pow_ne_zero m hr.ne']
      rw [pow_succ r m]
      ring

/-- **Sharp per-tube translation probability (Brick Y).**

Sample `ω` uniformly from `B(0,1)` and translate a `δ`-tube `T` by `r • ω`.  The probability that
the whole tube lands inside a convex body `K` is at most
`C_n · vol K / (r ^ (n - 1) · vol B₁)`.

Note the exponent `n - 1`, not `n`.  The crude point-in-set estimate
`prob_smul_add_in_set_self` (which is all the abstract `HasUniformTranslation.uniformConstant`
provides) only gives `r ^ (-n) · vol K / vol B₁`, a factor `r` too large.  The gain comes from
`Convex.volume_erosion_inter_closedBall_le`: a tube has a *unit-length* core, so it can only be
translated into `K` by vectors lying in a ball of radius `r`, and that set of vectors has volume at
most `C_n · r · vol K` rather than the trivial `vol K`.

That single factor `r` is what makes the random-translation maximal-density estimate
(GWZ Lemma 7.6(a)) independent of the number of translations. -/
lemma prob_tube_translate_subset_le [Nontrivial E] {δ : NNReal} (T : Tube δ E)
    (K : ConvexSpaceBody E) {r : ℝ} (hr_pos : 0 < r) :
    uniformBallMeasure E {ω : E | (T.translate (r • ω)).carrier ⊆ K.carrier} ≤
      ENNReal.ofReal ((translationErosionVolumeConstant (Module.finrank ℝ E) : ℝ) /
          r ^ (Module.finrank ℝ E - 1)) *
        (volume (Metric.closedBall (0 : E) 1))⁻¹ * volume K.carrier := by
  -- Eliminate natural subtraction: let n = m+1 so that n-1 = m.
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank ℝ E = m + 1 :=
    ⟨Module.finrank ℝ E - 1, by
      have := Module.finrank_pos (R := ℝ) (M := E)
      omega⟩
  have hm_sub : Module.finrank ℝ E - 1 = m := by omega
  rw [hm_sub]
  -- Abbreviations
  let B₁ : Set E := Metric.closedBall (0 : E) 1
  let Er : Set E := {v : E | (fun z : E => v + z) '' T.carrier ⊆ K.carrier}
  let S : Set E := {ω : E | (T.translate (r • ω)).carrier ⊆ K.carrier}
  -- Step 1: unfold the uniform measure
  have hμ : uniformBallMeasure E S = (volume B₁)⁻¹ * volume (S ∩ B₁) := by
    dsimp [uniformBallMeasure, S]
    rw [Measure.restrict_apply' measurableSet_closedBall]
  rw [hμ]
  -- Step 2: rewrite S as a scaling preimage
  have hS_eq : S = (fun t : E => r • t) ⁻¹' Er := by
    ext ω
    dsimp [S, Er]
    have hcarrier : (T.translate (r • ω)).carrier = ((r • ω) + ·) '' T.carrier := by
      rw [Tube.translate_carrier, Set.image_add_left]
    simp
  rw [hS_eq]
  -- Step 3: rewrite the intersection S ∩ B₁ as a scaling preimage
  have h_inter_eq : ((fun t : E => r • t) ⁻¹' Er) ∩ B₁ =
    (fun t : E => r • t) ⁻¹' (Er ∩ Metric.closedBall (0 : E) r) := by
    ext ω
    simp [B₁, Metric.mem_closedBall, dist_zero_right, norm_smul, abs_of_pos hr_pos,
      show (r * ‖ω‖ ≤ r) ↔ (‖ω‖ ≤ 1) from by
        constructor <;> intro h <;> nlinarith]
  rw [h_inter_eq]
  -- Step 4: change of variables (scaling)
  have hscale : volume ((fun t : E => r • t) ⁻¹' (Er ∩ Metric.closedBall (0 : E) r))
      = ENNReal.ofReal ((r ^ (m + 1))⁻¹) * volume (Er ∩ Metric.closedBall (0 : E) r) := by
    calc
      volume ((fun t : E => r • t) ⁻¹' (Er ∩ Metric.closedBall (0 : E) r))
          = ENNReal.ofReal (abs ((r ^ Module.finrank ℝ E)⁻¹))
              * volume (Er ∩ Metric.closedBall (0 : E) r) :=
        MeasureTheory.Measure.addHaar_preimage_smul volume hr_pos.ne' _
      _ = ENNReal.ofReal ((r ^ Module.finrank ℝ E)⁻¹) *
              volume (Er ∩ Metric.closedBall (0 : E) r) := by
        simp [abs_of_pos (by positivity : 0 < (r ^ Module.finrank ℝ E)⁻¹)]
      _ = ENNReal.ofReal ((r ^ (m + 1))⁻¹) * volume (Er ∩ Metric.closedBall (0 : E) r) := by rw [hm]
  rw [hscale]
  -- Step 5: apply Convex.volume_erosion_inter_closedBall_le (Brick X)
  have hK_convex : Convex ℝ K.carrier := K.convex
  have hx_T : T.x ∈ T.carrier := by
    rw [T.carrier_eq]
    refine Set.mem_iUnion₂.mpr ⟨T.x, left_mem_segment ℝ T.x T.y, ?_⟩
    exact Metric.mem_closedBall_self (NNReal.coe_nonneg δ)
  have hy_T : T.y ∈ T.carrier := by
    rw [T.carrier_eq]
    refine Set.mem_iUnion₂.mpr ⟨T.y, right_mem_segment ℝ T.x T.y, ?_⟩
    exact Metric.mem_closedBall_self (NNReal.coe_nonneg δ)
  have hxy : 1 ≤ dist T.x T.y := T.dist_eq_one.ge
  have h_erosion : volume (Er ∩ Metric.closedBall (0 : E) r)
      ≤ (translationErosionVolumeConstant (m + 1) : ENNReal) *
        ENNReal.ofReal r * volume K.carrier := by
    have h_erosion' : volume (Er ∩ Metric.closedBall (0 : E) r)
        ≤ translationErosionVolumeConstant (Module.finrank ℝ E) * (r.toNNReal : NNReal)
            * volume K.carrier := by
      have htemp := Kakeya.Convex.volume_erosion_inter_closedBall_le hK_convex (hx := hx_T)
        (hy := hy_T) (hxy := hxy) (v₀ := 0) (r := r.toNNReal)
      -- htemp gives the explicit set and r.toNNReal; Er is definitionally that set,
      -- and (r.toNNReal : ℝ) = r for r ≥ 0.
      simpa [Er, Real.coe_toNNReal r hr_pos.le] using htemp
    have h_dim : translationErosionVolumeConstant (Module.finrank ℝ E) =
        translationErosionVolumeConstant (m + 1) := by
      rw [hm]
    rw [h_dim] at h_erosion'
    -- The RHS of h_erosion' is (C (m+1) : ENNReal) * ((r.toNNReal : NNReal) : ENNReal) *
    --   volume K.carrier
    -- We need (C (m+1) : ENNReal) * ENNReal.ofReal r * volume K.carrier
    -- But (r.toNNReal : ENNReal) = ENNReal.ofReal r by definition (ENNReal.ofReal r = r.toNNReal)
    simpa [ENNReal.ofReal] using h_erosion'
  -- Step 6: combine the bounds
  have h_combined :
      ENNReal.ofReal ((r ^ (m + 1))⁻¹) * volume (Er ∩ Metric.closedBall (0 : E) r) ≤
        ENNReal.ofReal ((translationErosionVolumeConstant (m + 1) : ℝ) / r ^ m) *
          volume K.carrier := by
    calc
      ENNReal.ofReal ((r ^ (m + 1))⁻¹) * volume (Er ∩ Metric.closedBall (0 : E) r)
          ≤ ENNReal.ofReal ((r ^ (m + 1))⁻¹)
              * ((translationErosionVolumeConstant (m + 1) : ENNReal) *
                ENNReal.ofReal r * volume K.carrier) :=
        mul_le_mul' (le_refl _) h_erosion
      _ = (ENNReal.ofReal ((r ^ (m + 1))⁻¹)
        * (translationErosionVolumeConstant (m + 1) : ENNReal) * ENNReal.ofReal r) *
          volume K.carrier := by ring
      _ = ENNReal.ofReal ((translationErosionVolumeConstant (m + 1) : ℝ) / r ^ m) *
          volume K.carrier := by
        rw [ofReal_inv_pow_succ_mul_coe_mul_ofReal
          (translationErosionVolumeConstant (m + 1)) hr_pos m]
  -- Step 7: multiply by (volume B₁)⁻¹ on the left and match the goal
  calc
    (volume B₁)⁻¹ * (ENNReal.ofReal ((r ^ (m + 1))⁻¹)
    * volume (Er ∩ Metric.closedBall (0 : E) r))
    ≤ (volume B₁)⁻¹ * (ENNReal.ofReal ((translationErosionVolumeConstant (m + 1) : ℝ) / r ^ m)
        * volume K.carrier) :=
      mul_le_mul' (le_refl _) h_combined
    _ = ENNReal.ofReal ((translationErosionVolumeConstant (m + 1) : ℝ) / r ^ m)
        * (volume B₁)⁻¹ * volume K.carrier := by
      ring
    _ = ENNReal.ofReal ((translationErosionVolumeConstant (Module.finrank ℝ E) : ℝ) / r ^ m)
        * (volume (Metric.closedBall (0 : E) 1))⁻¹ * volume K.carrier := by
      simp [hm, B₁]

/-- The coefficient in the random-translation containment probability bound. -/
noncomputable def probConst (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (r : ℝ) : ℝ :=
  (translationErosionVolumeConstant (Module.finrank ℝ E) : ℝ) /
      r ^ (Module.finrank ℝ E - 1) *
    (volume.real (Metric.closedBall (0 : E) 1))⁻¹

/-- The translation-probability coefficient is positive at positive scales. -/
lemma probConst_pos {r : ℝ} (hr : 0 < r) : 0 < probConst E r := by
  unfold probConst
  set n := Module.finrank ℝ E with hn_def
  have hC_pos : 0 < (translationErosionVolumeConstant n : ℝ) := by
    exact_mod_cast translationErosionVolumeConstant_pos n
  have hpow_pos : 0 < r ^ (n - 1) := pow_pos hr (n - 1)
  have hvolB_pos : 0 < volume.real (Metric.closedBall (0 : E) 1) := by
    rw [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨Metric.measure_closedBall_pos volume 0 one_pos, measure_closedBall_lt_top⟩
  exact mul_pos (div_pos hC_pos hpow_pos) (inv_pos.mpr hvolB_pos)

/-- Real-valued form of `prob_tube_translate_subset_le`, which is the shape the Chernoff layer
consumes (it bounds a sum of `toReal` probabilities). -/
lemma prob_tube_translate_subset_le_toReal [Nontrivial E] {δ : NNReal} (T : Tube δ E)
    (K : ConvexSpaceBody E) {r : ℝ} (hr_pos : 0 < r) :
    (uniformBallMeasure E {ω : E | (T.translate (r • ω)).carrier ⊆ K.carrier}).toReal ≤
      (translationErosionVolumeConstant (Module.finrank ℝ E) : ℝ) / r ^ (Module.finrank ℝ E - 1) *
        (volume.real (Metric.closedBall (0 : E) 1))⁻¹ * volume.real K.carrier := by
  set n := Module.finrank ℝ E with hn_def
  set A := (translationErosionVolumeConstant n : ℝ) / r ^ (n - 1) with hA_def
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]; positivity
  -- Invoke the ENNReal version.
  have h_ennreal : uniformBallMeasure E
    {ω : E | (T.translate (r • ω)).carrier ⊆ K.carrier} ≤
    ENNReal.ofReal A * (volume (Metric.closedBall (0 : E) 1))⁻¹ * volume K.carrier :=
  prob_tube_translate_subset_le (E := E) T K hr_pos
  -- RHS ≠ ⊤
  have h_rhs_ne_top : ENNReal.ofReal A * (volume (Metric.closedBall (0 : E) 1))⁻¹
      * volume K.carrier ≠ ⊤ := by
    refine ENNReal.mul_ne_top ?_ (K.isCompact'.measure_lt_top.ne)
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    exact ENNReal.inv_ne_top.mpr (volume_unitBall_ne_zero E)
  -- toReal of the RHS product simplifies to the real-valued target
  have h_RHS_toReal : (ENNReal.ofReal A * (volume (Metric.closedBall (0 : E) 1))⁻¹
    * volume K.carrier).toReal =
    A * (volume.real (Metric.closedBall (0 : E) 1))⁻¹ * volume.real K.carrier := by
    calc
      (ENNReal.ofReal A * (volume (Metric.closedBall (0 : E) 1))⁻¹
          * volume K.carrier).toReal
          = ((ENNReal.ofReal A * (volume (Metric.closedBall (0 : E) 1))⁻¹)
              * volume K.carrier).toReal := by ring
      _ = (ENNReal.ofReal A * (volume (Metric.closedBall (0 : E) 1))⁻¹).toReal
          * (volume K.carrier).toReal := by
        rw [ENNReal.toReal_mul]
      _ = (ENNReal.ofReal A).toReal
          * ((volume (Metric.closedBall (0 : E) 1))⁻¹).toReal
          * (volume K.carrier).toReal := by
        rw [ENNReal.toReal_mul]
      _ = A * ((volume (Metric.closedBall (0 : E) 1))⁻¹).toReal
          * (volume K.carrier).toReal := by
        rw [ENNReal.toReal_ofReal hA_nonneg]
      _ = A * (volume.real (Metric.closedBall (0 : E) 1))⁻¹
          * (volume K.carrier).toReal := by
        rw [ENNReal.toReal_inv, ← MeasureTheory.Measure.real]
      _ = A * (volume.real (Metric.closedBall (0 : E) 1))⁻¹
          * volume.real K.carrier := by
        rw [← MeasureTheory.Measure.real]
  -- Apply toReal_mono and combine with the toReal computation
  calc
    (uniformBallMeasure E {ω : E | (T.translate (r • ω)).carrier ⊆ K.carrier}).toReal
        ≤ (ENNReal.ofReal A * (volume (Metric.closedBall (0 : E) 1))⁻¹
            * volume K.carrier).toReal :=
      ENNReal.toReal_mono h_rhs_ne_top h_ennreal
    _ = A * (volume.real (Metric.closedBall (0 : E) 1))⁻¹ * volume.real K.carrier :=
      h_RHS_toReal
    _ = (translationErosionVolumeConstant n : ℝ) / r ^ (n - 1) *
        (volume.real (Metric.closedBall (0 : E) 1))⁻¹ * volume.real K.carrier := by
      rfl

/-- **The `ρ`-scaled uniform random translation on `E`.**

Same sample space and probability measure as `instHasUniformTranslationSelf`
(uniform on `B(0,1)`), but the motion attached to a sample `t` is translation by
`ρ • t` rather than by `t`.  Consequently `uniformConstant` picks up the
Jacobian factor `(ρ^n)⁻¹`.

This is what the random-translation lemmas actually need: their conclusion
translates the tubes by `ρ • ω j`, so the Chernoff bad events must be phrased
against *this* action, not the unscaled one.  Because the `measure` field is
unchanged, `productMeasure` is the same measure as for the canonical instance.

Provided as a `def` rather than an `instance` (it is `ρ`-indexed); use `letI`
at the call site. -/
@[reducible] noncomputable def scaledUniformTranslationSelf {ρ : ℝ} (hρ : 0 < ρ) :
    HasUniformTranslation E E where
  measure := uniformBallMeasure E
  shift t := ⟨ρ • t⟩
  measurable_apply x := by
    change Measurable (fun t : E => ρ • t + x)
    exact (measurable_const_smul ρ).add_const x
  uniformConstant :=
    (ρ ^ Module.finrank ℝ E)⁻¹ * (volume.real (Metric.closedBall (0 : E) 1))⁻¹
  uniformConstantPos := by
    have hrho_pow_pos : 0 < ρ ^ Module.finrank ℝ E := pow_pos hρ (Module.finrank ℝ E)
    have hvolB_pos : 0 < volume.real (Metric.closedBall (0 : E) 1) := by
      rw [Measure.real, ENNReal.toReal_pos_iff]
      exact ⟨volume_unitBall_pos E, measure_closedBall_lt_top⟩
    have hpos1 : 0 < (ρ ^ Module.finrank ℝ E)⁻¹ := inv_pos.mpr hrho_pow_pos
    have hpos2 : 0 < (volume.real (Metric.closedBall (0 : E) 1))⁻¹ := inv_pos.mpr hvolB_pos
    exact mul_pos hpos1 hpos2
  prob_point_in_set := by
    intro x K hK hKtop
    change (uniformBallMeasure E) {ω : E | ρ • ω + x ∈ K} ≤
      ENNReal.ofReal ((ρ ^ Module.finrank ℝ E)⁻¹ *
        (volume.real (Metric.closedBall (0 : E) 1))⁻¹) * volume K
    exact prob_smul_add_in_set_self (E := E) (ρ := ρ) hρ x hK hKtop

end UniformTranslationInstance

end Kakeya
