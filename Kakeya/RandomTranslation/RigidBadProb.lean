/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.RigidMotionED
public import Kakeya.Tube.EDPacking.AxialAngle
public import Kakeya.Tube.EDPacking.BadAgainstSet
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# GWZ Appendix A (106) for the `BadAgainstSet` predicate

## Why this file exists

`Kakeya.prob_rigidMove_bad_le` estimates the probability that a random rigid copy of a tube is
**contained** in the `99δ`-thickening of a test tube. That is *not* the random variable the
essential-distinctness bridge needs.

The bridge (`Kakeya/Tube/EDPacking/BadAgainstSet.lean`,
`badAgainstSet_of_notED_subset_cthickening`) turns "`P` is not essentially distinct from `Q`, and
`Q` sits in the thin box `K`" into "`P` is `BadAgainstSet K`", i.e. a fixed fraction of `|P|` lies
in `K`. It cannot produce containment, and no strengthening can: two parallel `δ`-tubes of length
`1` offset by `1/2` along their common axis overlap in half their volume, so they fail to be
essentially distinct, yet neither is contained in any `O(δ)`-thickening of the other. The axial
offset is `O(1)`, not `O(δ)`. So the volume-fraction predicate is forced.

Consequently the ED conjunct of GWZ Lemma 3.8 needs (106) for `BadAgainstSet`, which is what this
file supplies.

## The two factors

For `K = cthickening (99δ) T₀.carrier`:

* **rotational** — `Kakeya.bad_axial_angle_le` says `BadAgainstSet T_i K c` forces the projective
  distance from `T_i.direction` to `T₀.direction` below `C·δ/c`. Feeding that cap radius to
  `Kakeya.rotHaar_projectiveCap_le` gives a rotational factor `≲ (δ/c)^(n-1)`.
* **translational** — a Markov bound. Averaging over translations,
  `∫ |T'_v ∩ K| dv = |T'| · |K|`, so the set of `v` for which `|T'_v ∩ K| ≥ c·|T'|` has normalised
  measure at most `|K| / (c · |B₁|)`, which is `≲ δ^(n-1)/c`. Note the tube's own volume cancels,
  so no lower bound on `|T'|` is needed.

Their product is `≲ δ^(2(n-1))`, matching the containment version.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The dimensional density threshold `c_vol / (2 · M_vol)` at which the not-essentially-distinct
bridge produces `BadAgainstSet`. Fixed by `Kakeya.notED_implies_BadAgainstSet`. -/
def edBridgeConstant (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : ℝ :=
  ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ℝ) /
    (2 * ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ))

theorem edBridgeConstant_pos : 0 < edBridgeConstant E := by
  unfold edBridgeConstant
  have hc_pos : (0 : ℝ) < ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ℝ) := by
    exact NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  have hM_pos : (0 : ℝ) < ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ) := by
    unfold Tube.volume_le.C
    push_cast
    positivity
  exact div_pos hc_pos (by linarith)

theorem edBridgeConstant_le_one [Nontrivial E] : edBridgeConstant E ≤ 1 := by
  unfold edBridgeConstant
  have h2Mv_pos : (0 : ℝ) < 2 * ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ) := by
    positivity
  rw [div_le_iff₀ h2Mv_pos]
  have hcv_le_Mv :
      ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ℝ) ≤
        ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ) := by
    obtain ⟨e, he⟩ : ∃ e : E, e ≠ 0 := exists_ne (0 : E)
    set u : E := ‖e‖⁻¹ • e with hu_def
    have hu_norm : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr he))]
      field_simp
    have hδ0 : (0 : NNReal) < 1 / 2 := by
      rw [← NNReal.coe_lt_coe]; push_cast; norm_num
    let T_wit : Tube (1 / 2 : NNReal) E :=
      Tube.ofMidpointDirection (1 / 2 : NNReal) (0 : E) u hu_norm
    have hlb := Tube.le_volume (δ := (1 / 2 : NNReal)) T_wit
    have hlb_real := ENNReal.toReal_mono T_wit.isCompact.measure_lt_top.ne hlb
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at hlb_real
    have hub := Tube.volume_le (by rw [← NNReal.coe_le_coe]; push_cast; norm_num) T_wit
    have hRHS_fin : (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
        ((1 / 2 : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ := by
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hub_real := ENNReal.toReal_mono hRHS_fin hub
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at hub_real
    have h_half_coe : (((1 / 2 : NNReal) : ℝ)) = (1 / 2 : ℝ) := by
      rw [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    rw [h_half_coe] at hlb_real hub_real
    have hchain := hlb_real.trans hub_real
    have hpow_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ (Module.finrank ℝ E - 1) :=
      pow_pos (by norm_num) _
    exact le_of_mul_le_mul_right hchain hpow_pos
  have hC_nonneg : (0 : ℝ) ≤ ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ) :=
    NNReal.coe_nonneg _
  linarith

/-! ## The Tonelli averaging identity -/

/-- Lebesgue measure is invariant under `v ↦ x - v`: the reflection-translation used in the inner
integral of the averaging identity. -/
theorem volume_setOf_neg_add_mem (A : Set E) (x : E) :
    volume {v : E | -v + x ∈ A} = volume A := by
  have h_set : {v : E | -v + x ∈ A} = (fun v : E => x - v) ⁻¹' A := by
    ext v
    simp [neg_add_eq_sub]
  rw [h_set]
  have hcomp : (fun v : E => x - v) = (fun w : E => x + w) ∘ (fun v : E => -v) := by
    funext v
    simp [sub_eq_add_neg]
  rw [hcomp, Set.preimage_comp]
  rw [MeasureTheory.Measure.measure_preimage_neg]
  rw [MeasureTheory.measure_preimage_add]

/-- **The average overlap of a translate with a fixed set.**
`∫ |A + v ∩ K| dv = |A| · |K|`, by Tonelli and translation invariance. -/
theorem lintegral_volume_inter_translate {A K : Set E}
    (hA : MeasurableSet A) (hK : MeasurableSet K) :
    ∫⁻ v : E, volume ((fun z : E => v + z) '' A ∩ K) ∂volume = volume A * volume K := by
  let S : Set (E × E) := {p : E × E | -p.1 + p.2 ∈ A ∧ p.2 ∈ K}
  have hS_meas : MeasurableSet S := by
    refine MeasurableSet.inter ?_ ?_
    · exact (continuous_fst.neg.add continuous_snd).measurable hA
    · exact measurable_snd hK
  have himg : ∀ v : E, (fun z : E => v + z) '' A = {x : E | -v + x ∈ A} := by
    intro v
    ext x
    constructor
    · rintro ⟨z, hzA, hEq⟩
      rw [← hEq]
      change -v + (v + z) ∈ A
      simpa [show -v + (v + z) = z by abel] using hzA
    · intro hx
      refine ⟨-v + x, hx, ?_⟩
      abel_nf
  have hpre₁ : ∀ v : E, Prod.mk v ⁻¹' S = (fun z : E => v + z) '' A ∩ K := by
    intro v
    ext x
    rw [himg v]
    simp [S]
  have hslice₂ : ∀ x : E, volume ((fun v : E => (v, x)) ⁻¹' S) =
      K.indicator (fun _ : E => volume A) x := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      have hfib : (fun v : E => (v, x)) ⁻¹' S = {v : E | -v + x ∈ A} := by
        ext v
        simp [S, hx]
      rw [hfib]
      exact volume_setOf_neg_add_mem A x
    · have hfib : (fun v : E => (v, x)) ⁻¹' S = ∅ := by
        ext v
        simp [S, hx]
      simp [hx, hfib]
  calc
    (∫⁻ v : E, volume ((fun z : E => v + z) '' A ∩ K) ∂volume)
      = ∫⁻ v : E, volume (Prod.mk v ⁻¹' S) ∂volume := by
          apply lintegral_congr
          intro v
          rw [hpre₁ v]
    _ = (volume.prod volume) S := (MeasureTheory.Measure.prod_apply hS_meas).symm
    _ = ∫⁻ x : E, volume ((fun v : E => (v, x)) ⁻¹' S) ∂volume :=
          MeasureTheory.Measure.prod_apply_symm hS_meas
    _ = ∫⁻ x : E, K.indicator (fun _ : E => volume A) x ∂volume := by
          apply lintegral_congr
          intro x
          exact hslice₂ x
    _ = volume A * volume K := by
          have hconst : (fun x : E => K.indicator (fun _ : E => volume A) x) =
              (fun x : E => volume A * K.indicator (fun _ : E => (1 : ENNReal)) x) := by
            funext x
            by_cases hx : x ∈ K <;> simp [hx]
          have hK_meas : Measurable (fun x : E => K.indicator (fun _ : E => (1 : ENNReal)) x) :=
            (measurable_const.indicator hK)
          rw [hconst]
          rw [MeasureTheory.lintegral_const_mul (volume A) (f := fun x : E =>
            K.indicator (fun _ : E => (1 : ENNReal)) x) hK_meas]
          congr 1
          exact MeasureTheory.lintegral_indicator_one hK

/-! ## The translational Markov factor -/

/-- Joint measurability of the overlap of a translated tube with a fixed measurable set. -/
theorem measurable_volume_inter_translate {δ : NNReal} (T : Tube δ E)
    {K : Set E} (hK : MeasurableSet K) :
    Measurable (fun v : E => volume ((T.translate v).carrier ∩ K)) := by
  have hT_meas : MeasurableSet T.carrier := T.isCompact.measurableSet
  set S : Set (E × E) := {p | -p.1 + p.2 ∈ T.carrier ∧ p.2 ∈ K}
  have hcont : Continuous (fun p : E × E => -p.1 + p.2) :=
    continuous_fst.neg.add continuous_snd
  have hS_meas : MeasurableSet S := by
    refine MeasurableSet.inter ?_ ?_
    · exact hcont.measurable hT_meas
    · exact measurable_snd hK
  have hpre : ∀ v : E, Prod.mk v ⁻¹' S = (T.translate v).carrier ∩ K := by
    intro v
    ext w
    simp only [S, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_inter_iff,
      Tube.translate_carrier]
  have h := measurable_measure_prodMk_left (ν := (volume : Measure E)) hS_meas
  simpa [hpre] using h

/-- **The translational factor, by Markov.**

The set of unit translations that push a fixed fraction `c` of the tube's volume into `K` has
normalised measure at most `|K| / (c · |B₁|)`. The tube's own volume cancels between the Markov
threshold and the averaging identity, so the bound is uniform over tubes; `0 < δ` is needed only so
that the tube is not null. -/
theorem prob_translate_bad_le [Nontrivial E] {δ : NNReal} (hδ : 0 < δ) (T : Tube δ E)
    {K : Set E} (hK : MeasurableSet K) {c : ℝ} (hc : 0 < c) :
    uniformBallMeasure E {v : E | BadAgainstSet (T.translate v) K c}
      ≤ ENNReal.ofReal c⁻¹ * (volume (Metric.closedBall (0 : E) 1))⁻¹ * volume K := by
  let B₁ : Set E := Metric.closedBall (0 : E) 1
  let μ : Measure E := volume.restrict B₁
  let f : E → ENNReal := fun v => volume ((T.translate v).carrier ∩ K)
  let ε : ENNReal := ENNReal.ofReal c * volume T.carrier
  -- Translation invariance of the volume of a tube.
  have hvol_tr : ∀ v : E, volume (T.translate v).carrier = volume T.carrier := by
    intro v
    rw [Tube.translate_carrier]
    rw [MeasureTheory.measure_preimage_add]
  -- The carrier of a translate is the image `v + T.carrier`.
  have hcarrier_img : ∀ v : E, (T.translate v).carrier = (fun z : E => v + z) '' T.carrier := by
    intro v
    rw [Tube.translate_carrier]
    exact (Set.image_add_left (a := v) (t := T.carrier)).symm
  -- Measurability of the overlap `f`.
  have hf_meas : Measurable f := by
    simpa [f] using (measurable_volume_inter_translate (T := T) (K := K) hK)
  -- The bad set is exactly the upper level set of `f` at threshold `ε`.
  let s : Set E := {v : E | ε ≤ f v}
  have hBad_eq : {v : E | BadAgainstSet (T.translate v) K c} = s := by
    ext v
    exact (show BadAgainstSet (T.translate v) K c ↔ ε ≤ f v by
      constructor
      · intro h
        unfold BadAgainstSet at h
        dsimp [ε, f] at h ⊢
        rw [hvol_tr v] at h
        exact h
      · intro h
        unfold BadAgainstSet
        dsimp [ε, f] at h ⊢
        simpa [hvol_tr v] using h)
  have hSet_meas : MeasurableSet s := by
    rw [show s = f ⁻¹' (Set.Ici ε) by
      ext v
      simp [s]]
    exact measurableSet_Ici.preimage hf_meas
  -- Combine Bad into the level set and unfold the uniform measure.
  rw [hBad_eq]
  dsimp [uniformBallMeasure]
  rw [Measure.restrict_apply' measurableSet_closedBall]
  have hrestrict_eq : μ s = volume (s ∩ B₁) := by
    simpa [μ] using (Measure.restrict_apply' measurableSet_closedBall)
  -- Markov's inequality for the restricted measure.
  have hmarkov : ε * μ s ≤ volume T.carrier * volume K := by
    calc
      ε * μ s ≤ ∫⁻ v : E, f v ∂μ := by
            simpa [s, μ] using
              (mul_meas_ge_le_lintegral (μ := μ) (f := f) hf_meas ε)
      _ ≤ ∫⁻ v : E, f v ∂volume := by
            exact lintegral_mono' (Measure.restrict_le_self (μ := volume) (s := B₁))
              (le_refl f)
      _ = volume T.carrier * volume K := by
            rw [show ∫⁻ v : E, f v ∂volume =
                  ∫⁻ v : E, volume ((fun z : E => v + z) '' T.carrier ∩ K) ∂volume by
                  apply lintegral_congr
                  intro v
                  dsimp [f]
                  rw [hcarrier_img v]]
            exact lintegral_volume_inter_translate T.isCompact.measurableSet hK
  -- The tube is not null: `0 < δ` gives `T.carrier` positive volume (via `Tube.le_volume`),
  -- whose two factors are both nonzero.
  have hm_ne : volume T.carrier ≠ 0 := by
    have hlb := Tube.le_volume (δ := δ) T
    have hpos : 0 < (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
        (δ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
      exact ENNReal.mul_pos
        (ne_of_gt (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos (Module.finrank ℝ E))))
        (ne_of_gt (ENNReal.pow_pos (by exact_mod_cast hδ) (Module.finrank ℝ E - 1)))
    exact ne_of_gt (lt_of_lt_of_le hpos hlb)
  have hm_top : volume T.carrier ≠ ⊤ := T.isCompact.measure_lt_top.ne
  -- Cancel `volume T.carrier` from the Markov bound (with `ε = ofReal c * volume T.carrier`).
  have hcancel : ENNReal.ofReal c * volume (s ∩ B₁) ≤ volume K := by
    have hα : ε * volume (s ∩ B₁) ≤ volume T.carrier * volume K := by
      simpa [hrestrict_eq] using hmarkov
    have hβ : volume T.carrier * (ENNReal.ofReal c * volume (s ∩ B₁))
        ≤ volume T.carrier * volume K := by
      simpa [ε, mul_assoc, mul_left_comm, mul_comm] using hα
    exact (ENNReal.mul_le_mul_iff_left hm_ne hm_top).mp
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hβ)
  have hboundInv : volume (s ∩ B₁) ≤ ENNReal.ofReal c⁻¹ * volume K := by
    have hc_nz : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
    have hc_ft : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
    have h₁ : volume (s ∩ B₁) ≤ (ENNReal.ofReal c)⁻¹ * volume K :=
      (ENNReal.mul_le_iff_le_inv hc_nz hc_ft).mp hcancel
    rw [← ENNReal.ofReal_inv_of_pos hc] at h₁
    exact h₁
  calc
    (volume B₁)⁻¹ * volume (s ∩ B₁)
        ≤ (volume B₁)⁻¹ * (ENNReal.ofReal c⁻¹ * volume K) := by
          exact mul_le_mul_right hboundInv (volume B₁)⁻¹
    _ = ENNReal.ofReal c⁻¹ * (volume B₁)⁻¹ * volume K := by
          ac_rfl

/-! ## GWZ (106) for `BadAgainstSet` -/

/-- A rigid motion preserves the volume of a tube's carrier. -/
theorem volume_rigidMove_carrier {δ : NNReal} (T : Tube δ E)
    (u : unitary (E →L[ℝ] E)) (v : E) :
    volume (T.rigidMove u v).carrier = volume T.carrier := by
  rw [Tube.rigidMove_carrier]
  let L : E ≃ₗᵢ[ℝ] E := Unitary.linearIsometryEquiv u
  let g : E → E := fun y : E => (L.symm : E → E) (y - v)
  have h1 : Function.LeftInverse g (Kakeya.rigidMap u v) := by
    intro x
    dsimp [g]
    rw [add_sub_cancel_right]
    rw [← Unitary.coe_linearIsometryEquiv_apply u]
    apply LinearEquiv.symm_apply_apply
  have h2 : Function.RightInverse g (Kakeya.rigidMap u v) := by
    intro y
    dsimp [g]
    change (L : E → E) (L.symm (y - v)) + v = y
    simp
  have : Kakeya.rigidMap u v '' T.carrier = g ⁻¹' T.carrier :=
    congrFun (Set.image_eq_preimage_of_inverse h1 h2) T.carrier
  rw [this]
  have hmeas_f : Measurable (Kakeya.rigidMap u v) :=
    (Kakeya.isometry_rigidMap u v).continuous.measurable
  have hmeas_g : Measurable g := by
    dsimp [g]
    exact ((L.symm : E →L[ℝ] E).continuous.comp
      (Continuous.sub continuous_id continuous_const)).measurable
  let e : E ≃ᵐ E :=
    { toEquiv := { toFun := Kakeya.rigidMap u v, invFun := g, left_inv := h1, right_inv := h2 }
      measurable_toFun := hmeas_f
      measurable_invFun := hmeas_g }
  have he : MeasurePreserving (e : E → E) volume volume := by
    change MeasurePreserving (Kakeya.rigidMap u v) volume volume
    exact Kakeya.measurePreserving_rigidMap u v
  have h_symm : MeasurePreserving (e.symm : E → E) volume volume :=
    MeasurePreserving.symm e he
  change volume ((e.symm : E → E) ⁻¹' T.carrier) = volume T.carrier
  exact MeasurePreserving.measure_preimage_equiv h_symm T.carrier

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The graph of the moved tube is closed.** Membership `y ∈ R_{u,v}(T)` is the projection, along
the *compact* factor `T.carrier`, of the closed condition `u x + v = y`; projections along compact
factors are closed maps. -/
theorem isClosed_mem_rigidMove_carrier {δ : NNReal} (T : Tube δ E) :
    IsClosed {q : (unitary (E →L[ℝ] E) × E) × E |
      q.2 ∈ (T.rigidMove q.1.1 q.1.2).carrier} := by
  have hT : IsCompact T.carrier := T.isCompact
  haveI : CompactSpace ↑T.carrier := isCompact_iff_compactSpace.mp hT
  let A : Set (((unitary (E →L[ℝ] E) × E) × E) × ↑T.carrier) :=
    {p | (p.1.1.1 : E →L[ℝ] E) (p.2 : E) + p.1.1.2 = p.1.2}
  have hA : IsClosed A := by
    have hf : Continuous (fun p : ((unitary (E →L[ℝ] E) × E) × E) × ↑T.carrier =>
        (p.1.1.1 : E →L[ℝ] E) (p.2 : E) + p.1.1.2) := by
      fun_prop
    have hg : Continuous (fun p : ((unitary (E →L[ℝ] E) × E) × E) × ↑T.carrier => p.1.2) := by
      fun_prop
    exact isClosed_eq hf hg
  have himg : IsClosed (Prod.fst '' A) := by
    exact (isClosedMap_fst_of_compactSpace (X := (unitary (E →L[ℝ] E) × E) × E)
      (Y := ↑T.carrier)) A hA
  have hset : {q : (unitary (E →L[ℝ] E) × E) × E |
      q.2 ∈ (T.rigidMove q.1.1 q.1.2).carrier} = Prod.fst '' A := by
    ext q
    constructor
    · intro hq
      change q.2 ∈ (T.rigidMove q.1.1 q.1.2).carrier at hq
      rw [Tube.rigidMove_carrier] at hq
      rw [Set.mem_image] at hq
      obtain ⟨x, hxT, hxEq⟩ := hq
      exact ⟨(q, ⟨x, hxT⟩), by simpa [A] using hxEq, rfl⟩
    · intro hq
      obtain ⟨p, hpA, hpq⟩ := hq
      subst q
      change p.1.2 ∈ (T.rigidMove p.1.1.1 p.1.1.2).carrier
      rw [Tube.rigidMove_carrier]
      exact ⟨(p.2 : E), p.2.property, by rw [Kakeya.rigidMap_apply]; exact hpA⟩
  rw [hset]
  exact himg

/-- Measurability of the overlap of a moved tube with a fixed measurable set. -/
theorem measurable_volume_inter_rigidMove {δ : NNReal} (T : Tube δ E)
    {K : Set E} (hK : MeasurableSet K) :
    Measurable (fun ω : unitary (E →L[ℝ] E) × E =>
      volume ((T.rigidMove ω.1 ω.2).carrier ∩ K)) := by
  set S : Set ((unitary (E →L[ℝ] E) × E) × E) :=
    {q | q.2 ∈ (T.rigidMove q.1.1 q.1.2).carrier ∧ q.2 ∈ K}
  have hS_meas : MeasurableSet S := by
    refine MeasurableSet.inter ?_ ?_
    · exact (isClosed_mem_rigidMove_carrier T).measurableSet
    · exact measurable_snd hK
  have hpre : ∀ ω : unitary (E →L[ℝ] E) × E,
      Prod.mk ω ⁻¹' S = (T.rigidMove ω.1 ω.2).carrier ∩ K := by
    intro ω
    ext w
    simp only [S, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_inter_iff]
  have h := measurable_measure_prodMk_left (ν := (volume : Measure E)) hS_meas
  simpa [hpre] using h

/-- Measurability of the `BadAgainstSet` event in the rigid-motion sample space. -/
theorem measurableSet_rigidMove_badAgainstSet {δ : NNReal} (T : Tube δ E)
    {K : Set E} (hK : MeasurableSet K) {c : ℝ} :
    MeasurableSet {ω : unitary (E →L[ℝ] E) × E |
      BadAgainstSet (T.rigidMove ω.1 ω.2) K c} := by
  have hU : Measurable (fun ω : unitary (E →L[ℝ] E) × E =>
      volume ((T.rigidMove ω.1 ω.2).carrier ∩ K)) :=
    measurable_volume_inter_rigidMove T hK
  have hset : {ω : unitary (E →L[ℝ] E) × E |
      BadAgainstSet (T.rigidMove ω.1 ω.2) K c} =
      {ω : unitary (E →L[ℝ] E) × E |
        ENNReal.ofReal c * volume T.carrier ≤
          volume ((T.rigidMove ω.1 ω.2).carrier ∩ K)} := by
    ext x
    have hw := volume_rigidMove_carrier T x.1 x.2
    simp only [mem_setOf_eq, BadAgainstSet, hw]
  rw [hset]
  exact measurableSet_le measurable_const hU

/-- **GWZ Appendix A, equation (106), for the `BadAgainstSet` predicate.**

This is the estimate the essential-distinctness bridge actually consumes. The exponent
`2 · (n - 1)` is the same as in the containment version `Kakeya.prob_rigidMove_bad_le`; only the
predicate is weakened from containment to a fixed-fraction overlap. -/
theorem prob_rigidMove_badAgainstSet_le [Nontrivial E] (hn : 1 < Module.finrank ℝ E) :
    ∃ (C : ENNReal) (δ₀ : NNReal), C ≠ ⊤ ∧ 0 < δ₀ ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ → ∀ (T T₀ : Tube δ E),
        T₀.carrier ⊆ Metric.closedBall (0 : E) (7 / 2) →
        rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
            BadAgainstSet (T.rigidMove ω.1 ω.2)
              (Metric.cthickening (99 * (δ : ℝ)) T₀.carrier) (edBridgeConstant E)}
          ≤ C * (δ : ENNReal) ^ (2 * (Module.finrank ℝ E - 1)) := by
  set c : ℝ := edBridgeConstant E with hc_def
  have hc_pos : 0 < c := by rw [hc_def]; exact edBridgeConstant_pos (E := E)
  have hc_le_one : c ≤ 1 := by rw [hc_def]; exact edBridgeConstant_le_one (E := E)
  obtain ⟨Cax, hCax, hAx⟩ := bad_axial_angle_le (E := E) hn
  obtain ⟨Crot, hCrot, hRot⟩ := rotHaar_projectiveCap_le (E := E)
  obtain ⟨M, hMpos, hVol⟩ := volume_cthickening_tube_le (E := E)
  set s : ℕ := Module.finrank ℝ E - 1 with hs_def
  let B₁ : Set E := Metric.closedBall (0 : E) 1
  let Cbase : ENNReal := ENNReal.ofReal c⁻¹ * (volume B₁)⁻¹
  let ρ0 : ℝ := Cax / c
  have hρ0_pos : 0 < ρ0 := by dsimp [ρ0]; exact div_pos hCax hc_pos
  let ρ0N : NNReal := ⟨ρ0, hρ0_pos.le⟩
  have hρ0N_co : (ρ0N : ℝ) = ρ0 := rfl
  let C : ENNReal := Cbase * ENNReal.ofReal M * Crot * (ρ0N : ENNReal) ^ s
  let δ₀_r : ℝ := min (min 1 (1 / 100 : ℝ)) (c / Cax)
  have hδ₀_r_pos : 0 < δ₀_r := by
    dsimp [δ₀_r]
    exact lt_min (lt_min (by norm_num) (by norm_num)) (div_pos hc_pos hCax)
  let δ₀ : NNReal := ⟨δ₀_r, hδ₀_r_pos.le⟩
  have hδ₀_pos : 0 < δ₀ := by
    dsimp [δ₀]
    exact hδ₀_r_pos
  refine ⟨C, δ₀, ?_, hδ₀_pos, ?_⟩
  · dsimp [C, Cbase, B₁]
    have hb₁ : (volume (Metric.closedBall (0 : E) 1))⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.2
        (ne_of_gt (Metric.measure_closedBall_pos volume (0 : E) zero_lt_one))
    have hρN : (ρ0N : ENNReal) ^ s ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb₁) ENNReal.ofReal_ne_top)
        hCrot) hρN
  · intro δ hδ hδ_le T T₀ hT₀B
    have hδ_le_r : (δ : ℝ) ≤ δ₀_r := by exact_mod_cast hδ_le
    have hmin01 : δ₀_r ≤ min (1 : ℝ) (1 / 100 : ℝ) := by
      dsimp [δ₀_r]
      exact min_le_left _ _
    have hminc : δ₀_r ≤ c / Cax := by
      dsimp [δ₀_r]
      exact min_le_right _ _
    have hδr_1 : (δ : ℝ) ≤ 1 := le_trans hδ_le_r (le_trans hmin01 (min_le_left _ _))
    have hδr_100 : (δ : ℝ) ≤ (1 / 100 : ℝ) :=
      le_trans hδ_le_r (le_trans hmin01 (min_le_right _ _))
    have hδr_cC : (δ : ℝ) ≤ c / Cax := le_trans hδ_le_r hminc
    have hδ1 : δ ≤ 1 := by exact_mod_cast hδr_1
    have hδ100 : δ ≤ 1 / 100 := by exact_mod_cast hδr_100
    have h100δ : (100 * δ : NNReal) ≤ 1 := by
      have h100r : (100 : ℝ) * (δ : ℝ) ≤ 1 := by nlinarith [hδr_100]
      exact_mod_cast h100r
    let ρ : ℝ := Cax * (δ : ℝ) / c
    have hρpos : 0 < ρ := by
      dsimp [ρ]
      positivity
    have hρ_le_1 : ρ ≤ 1 := by
      dsimp [ρ]
      have hCδ : Cax * (δ : ℝ) ≤ c := by
        calc
          Cax * (δ : ℝ) ≤ Cax * (c / Cax) := mul_le_mul_of_nonneg_left hδr_cC hCax.le
          _ = c := by field_simp [ne_of_gt hCax]
      exact (div_le_one₀ hc_pos).mpr hCδ
    let K : Set E := Metric.cthickening (99 * (δ : ℝ)) T₀.carrier
    have hK_meas : MeasurableSet K := by
      dsimp [K]
      exact Metric.isClosed_cthickening.measurableSet
    set A : Set (unitary (E →L[ℝ] E)) := {u |
      min ‖(u : E →L[ℝ] E) T.direction - T₀.direction‖
        ‖(u : E →L[ℝ] E) T.direction + T₀.direction‖ ≤ ρ} with hA
    have hA_meas : MeasurableSet A := by
      rw [hA]
      have hf : Continuous (fun u : unitary (E →L[ℝ] E) =>
          ‖(u : E →L[ℝ] E) T.direction - T₀.direction‖) :=
        ((continuous_unitaryApply T.direction).sub continuous_const).norm
      have hg : Continuous (fun u : unitary (E →L[ℝ] E) =>
          ‖(u : E →L[ℝ] E) T.direction + T₀.direction‖) :=
        ((continuous_unitaryApply T.direction).add continuous_const).norm
      exact (isClosed_le (Continuous.min hf hg) continuous_const).measurableSet
    have halign : ∀ u v, BadAgainstSet (T.rigidMove u v) K c →
        min ‖(u : E →L[ℝ] E) T.direction - T₀.direction‖
          ‖(u : E →L[ℝ] E) T.direction + T₀.direction‖ ≤ ρ := by
      intro u v hbad
      have hrad : (99 * (δ : ℝ)) = ((99 * δ : NNReal) : ℝ) := by
        rw [NNReal.coe_mul]
        norm_num
      have hKnn : Metric.cthickening (99 * (δ : ℝ)) T₀.carrier =
          Metric.cthickening (99 * δ : NNReal) T₀.carrier := by
        rw [hrad]
      have hbad_ax : ENNReal.ofReal c * volume (T.rigidMove u v).carrier ≤
          volume ((T.rigidMove u v).carrier ∩
            Metric.cthickening (99 * δ : NNReal) T₀.carrier) := by
        unfold BadAgainstSet at hbad
        simpa [K, hKnn] using hbad
      have hres := hAx hδ hδ1 (T.rigidMove u v) T₀ (c := c) hc_pos hc_le_one hbad_ax
      dsimp [ρ]
      simpa [Tube.rigidMove_direction] using hres
    have hpt : ∀ u : unitary (E →L[ℝ] E),
        uniformBallMeasure E {v : E | BadAgainstSet (T.rigidMove u v) K c}
          ≤ A.indicator (fun _ : unitary (E →L[ℝ] E) => Cbase * volume K) u := by
      intro u
      by_cases hu : u ∈ A
      · have hslice : {v : E | BadAgainstSet (T.rigidMove u v) K c} =
            {v : E | BadAgainstSet ((T.rigidMove u 0).translate v) K c} := by
          ext v
          unfold BadAgainstSet
          have hc : (T.rigidMove u v).carrier = ((T.rigidMove u 0).translate v).carrier := by
            have r_im : (v + ·) '' (Kakeya.rigidMap u 0 '' T.carrier) =
                Kakeya.rigidMap u v '' T.carrier := by
              rw [← Set.image_comp]
              congr 1
              funext x
              simp [Kakeya.rigidMap, add_comm]
            calc
              (T.rigidMove u v).carrier = Kakeya.rigidMap u v '' T.carrier :=
                Tube.rigidMove_carrier T u v
              _ = (v + ·) '' (Kakeya.rigidMap u 0 '' T.carrier) := r_im.symm
              _ = (v + ·) '' (T.rigidMove u 0).carrier := by simp [Tube.rigidMove_carrier]
              _ = ((T.rigidMove u 0).translate v).carrier := by simp [Tube.translate]
          simp [hc]
        rw [hslice]
        simpa [Cbase, hu] using
          prob_translate_bad_le hδ (T.rigidMove u 0) hK_meas hc_pos
      · have h_empty : {v : E | BadAgainstSet (T.rigidMove u v) K c} = (∅ : Set E) := by
          ext v
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact fun hv => hu (halign u v hv)
        rw [h_empty]
        simp [hu, measure_empty]
    have hρN : ρ.toNNReal = ρ0N * δ := by
      dsimp [ρ]
      have hρ_mul : Cax * (δ : ℝ) / c = ρ0 * (δ : ℝ) := by
        dsimp [ρ0]
        field_simp [ne_of_gt hc_pos]
      rw [hρ_mul]
      rw [Real.toNNReal_mul (p := ρ0) (q := (δ : ℝ)) hρ0_pos.le]
      rw [← hρ0N_co]
      rw [Real.toNNReal_coe, Real.toNNReal_coe]
    have hρ_pow : ((ρ.toNNReal : NNReal) : ENNReal) ^ s =
        (ρ0N : ENNReal) ^ s * (δ : ENNReal) ^ s := by
      rw [hρN, ENNReal.coe_mul, mul_pow]
    calc
      rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
            BadAgainstSet (T.rigidMove ω.1 ω.2)
              (Metric.cthickening (99 * (δ : ℝ)) T₀.carrier) c}
          = (rotHaar (E := E)).prod (uniformBallMeasure E)
              {ω : unitary (E →L[ℝ] E) × E |
                BadAgainstSet (T.rigidMove ω.1 ω.2) K c} := by
            rw [rigidMeasure]
      _ = ∫⁻ u : unitary (E →L[ℝ] E), uniformBallMeasure E (Prod.mk u ⁻¹'
            {ω : unitary (E →L[ℝ] E) × E |
              BadAgainstSet (T.rigidMove ω.1 ω.2) K c}) ∂(rotHaar (E := E)) := by
            exact Measure.prod_apply (measurableSet_rigidMove_badAgainstSet T hK_meas)
      _ = ∫⁻ u : unitary (E →L[ℝ] E), uniformBallMeasure E
              {v : E | BadAgainstSet (T.rigidMove u v) K c} ∂(rotHaar (E := E)) := by
            rfl
      _ ≤ ∫⁻ u : unitary (E →L[ℝ] E),
              A.indicator (fun _ : unitary (E →L[ℝ] E) => Cbase * volume K) u
              ∂(rotHaar (E := E)) := by
            exact lintegral_mono (fun u => hpt u)
      _ = ∫⁻ u in A, Cbase * volume K ∂(rotHaar (E := E)) := by
            rw [lintegral_indicator hA_meas]
      _ = (Cbase * volume K) * (rotHaar (E := E) A) := by
            rw [setLIntegral_const]
      _ ≤ (Cbase * volume K) * (Crot * ((ρ.toNNReal : NNReal) : ENNReal) ^ s) := by
            have hrotA : rotHaar (E := E) A ≤
                Crot * ((ρ.toNNReal : NNReal) : ENNReal) ^ s := by
              rw [hA]
              exact hRot (Tube.norm_direction T) (Tube.norm_direction T₀) hρpos hρ_le_1
            exact mul_le_mul_of_nonneg_left hrotA (by positivity)
      _ ≤ (Cbase * (ENNReal.ofReal M * (δ : ENNReal) ^ s)) *
              (Crot * ((ρ.toNNReal : NNReal) : ENNReal) ^ s) := by
            have hvolK : volume K ≤ ENNReal.ofReal M * (δ : ENNReal) ^ s := by
              dsimp [K]
              simpa [s] using hVol h100δ T₀
            have hCK : Cbase * volume K ≤
                Cbase * (ENNReal.ofReal M * (δ : ENNReal) ^ s) :=
              mul_le_mul_of_nonneg_left hvolK (by positivity)
            exact mul_le_mul_of_nonneg_right hCK (by positivity)
      _ = C * (δ : ENNReal) ^ s * (δ : ENNReal) ^ s := by
            rw [hρ_pow]
            dsimp [C, Cbase]
            ring
      _ = C * (δ : ENNReal) ^ (2 * s) := by
            rw [two_mul, pow_add]
            ring
      _ = C * (δ : ENNReal) ^ (2 * (Module.finrank ℝ E - 1)) := by
            rw [← hs_def]

/-! ## The corrected ED failure count

`Kakeya.edBadCount` counts the rigid copies **contained** in the thin box. As explained in the
header, the essential-distinctness bridge cannot produce containment, so the count that the ED
conjunct of GWZ Lemma 3.8 must control is the one below: the copies a fixed fraction of whose volume
lies in the thin box. It is the rigid-motion analogue of `Kakeya.edFailCountSet`. -/

/-- **The ED failure count of a tuple of rigid copies against a test tube.**
The number of family members whose rigid copy has at least an `edBridgeConstant E` fraction of its
volume inside the `99δ`-thickening of `T₀`. -/
def edFailCount {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E) (T₀ : Tube δ E)
    (ω : unitary (E →L[ℝ] E) × E) : ℕ :=
  (@Finset.filter ι (fun i =>
      BadAgainstSet ((T i).rigidMove ω.1 ω.2)
        (Metric.cthickening (99 * (δ : ℝ)) T₀.carrier) (edBridgeConstant E))
    (Classical.decPred _) s).card

/-- Containment is a special case of failure, so the containment count never exceeds it. -/
theorem edBadCount_le_edFailCount [Nontrivial E] {δ : NNReal} {ι : Type*}
    (s : Finset ι) (T : ι → Tube δ E) (T₀ : Tube δ E) (ω : unitary (E →L[ℝ] E) × E) :
    edBadCount s T T₀ ω ≤ edFailCount s T T₀ ω := by
  classical
  let K : Set E := Metric.cthickening (99 * (δ : ℝ)) T₀.carrier
  have hide : s.filter (fun i : ι => ((T i).rigidMove ω.1 ω.2).carrier ⊆ K) ⊆
      s.filter (fun i : ι => BadAgainstSet ((T i).rigidMove ω.1 ω.2) K (edBridgeConstant E)) := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    unfold BadAgainstSet
    rw [Set.inter_eq_self_of_subset_left hi.2]
    have hofReal : ENNReal.ofReal (edBridgeConstant E) ≤ (1 : ENNReal) :=
      ENNReal.ofReal_le_one.mpr (edBridgeConstant_le_one (E := E))
    have h_refl : volume ((T i).rigidMove ω.1 ω.2).carrier ≤
        volume ((T i).rigidMove ω.1 ω.2).carrier := le_rfl
    simpa using mul_le_mul hofReal h_refl zero_le zero_le
  simpa [edBadCount, edFailCount, K] using (Finset.card_le_card hide)

/-- **The deterministic bound for the failure count.** For a pairwise essentially distinct family
the failure count of a *single* rigid copy is at most a dimensional constant — no factor of the
number of copies appears. This is the same statement that `Kakeya.edBadCount_le` establishes
internally before weakening containment to failure. -/
theorem edFailCount_le [Nontrivial E] (hn : 1 < Module.finrank ℝ E) :
    ∃ (Cpack : ℕ) (δ₀ : NNReal), 0 < Cpack ∧ 0 < δ₀ ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ {ι : Type*} (s : Finset ι) (T : ι → Tube δ E) (T₀ : Tube δ E),
        T₀.carrier ⊆ Metric.closedBall (0 : E) (7 / 2) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        ∀ ω : unitary (E →L[ℝ] E) × E, edFailCount s T T₀ ω ≤ Cpack := by
  classical
  letI : ProperSpace E := FiniteDimensional.proper_real E
  obtain ⟨C_dim, δ₀bad, hC_dim_pos, hδ₀bad_pos, hδ₀bad_le1, hBad⟩ :=
    badAgainstSet_count_le_of_ED_thinBox (E := E) hn
  obtain ⟨M, hM_pos, hVol⟩ := volume_cthickening_tube_le (E := E)
  set c₀ : ℝ := edBridgeConstant E with hc₀_def
  set Cpack : ℕ := ⌈(C_dim : ℝ) * M ^ 2 / c₀ ^ Module.finrank ℝ E⌉₊ with hCpack_def
  have hc₀_pos : 0 < c₀ := by
    rw [hc₀_def]
    exact edBridgeConstant_pos
  have hCpack_pos : 0 < Cpack := by
    rw [hCpack_def]
    rw [Nat.ceil_pos]
    exact div_pos
      (mul_pos (by exact_mod_cast hC_dim_pos) (sq_pos_of_ne_zero (ne_of_gt hM_pos)))
      (pow_pos hc₀_pos _)
  let δ₀ : NNReal :=
    ⟨min δ₀bad (1 / 100 : ℝ), le_min hδ₀bad_pos.le (by norm_num)⟩
  have hδ₀_cast : (δ₀ : ℝ) = min δ₀bad (1 / 100 : ℝ) := rfl
  have hδ₀_pos : (0 : NNReal) < δ₀ := by
    change (0 : ℝ) < (δ₀ : ℝ)
    rw [hδ₀_cast]
    exact lt_min hδ₀bad_pos (by norm_num)
  refine ⟨Cpack, δ₀, hCpack_pos, hδ₀_pos, ?_⟩
  intro δ hδ hδ_le
  have hδR : (δ : ℝ) ≤ (δ₀ : ℝ) := by exact_mod_cast hδ_le
  have hδminR : (δ : ℝ) ≤ min δ₀bad (1 / 100 : ℝ) := by
    rw [← hδ₀_cast]
    exact hδR
  have hδle100R : (δ : ℝ) ≤ (1 / 100 : ℝ) := le_trans hδminR (min_le_right _ _)
  have hδbadR : (δ : ℝ) ≤ δ₀bad := le_trans hδminR (min_le_left _ _)
  have hδ₁ : δ ≤ (1 : NNReal) := by
    exact_mod_cast (le_trans hδminR (le_trans (min_le_left _ _) hδ₀bad_le1))
  have h100δ : (100 * δ : NNReal) ≤ 1 := by
    have h₁ : (100 : ℝ) * (δ : ℝ) ≤ 1 := by nlinarith [hδle100R]
    exact_mod_cast h₁
  intro ι s T T₀ hB2 hED ω
  let u : unitary (E →L[ℝ] E) := ω.1
  let v : E := ω.2
  let T' : ι → Tube δ E := fun i => (T i).rigidMove u 0
  have hED' : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T' i).carrier (T' j).carrier) := by
    simpa [T'] using rigidMove_pairwise_isEssentiallyDistinct hED u 0
  have hcar : ∀ i : ι, ((T i).rigidMove u v).carrier = ((T' i).translate v).carrier := by
    intro i
    have r_im : (v + ·) '' (Kakeya.rigidMap u 0 '' (T i).carrier) =
        Kakeya.rigidMap u v '' (T i).carrier := by
      rw [← Set.image_comp]
      congr 1
      funext x
      simp [Kakeya.rigidMap, add_comm]
    calc
      ((T i).rigidMove u v).carrier = Kakeya.rigidMap u v '' (T i).carrier :=
        Tube.rigidMove_carrier (T i) u v
      _ = (v + ·) '' (Kakeya.rigidMap u 0 '' (T i).carrier) := r_im.symm
      _ = (v + ·) '' ((T i).rigidMove u 0).carrier := by simp [Tube.rigidMove_carrier]
      _ = ((T' i).translate v).carrier := by simp [T', Tube.translate]
  let K : Set E := Metric.cthickening (99 * (δ : ℝ)) T₀.carrier
  have hMain : (s.filter (fun i : ι => BadAgainstSet ((T' i).translate v) K c₀)).card ≤ Cpack := by
    have hvolT₀ : volume (Metric.cthickening (99 * (δ : ℝ)) T₀.carrier) ≤
        ENNReal.ofReal M * (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
      hVol h100δ T₀
    have hB := hBad (ι := ι) (δ := δ) hδ hδbadR s T' T₀ hB2 M hM_pos hvolT₀ v hED'
    simpa [hCpack_def, c₀, K, edBridgeConstant] using hB
  have hfilter_eq :
      (fun i : ι => BadAgainstSet ((T i).rigidMove ω.1 ω.2)
        (Metric.cthickening (99 * (δ : ℝ)) T₀.carrier) (edBridgeConstant E))
      = (fun i : ι => BadAgainstSet ((T' i).translate v) K c₀) := by
    funext i
    simp [K, BadAgainstSet, edBridgeConstant, hcar, hc₀_def, u, v]
  unfold edFailCount
  rw [hfilter_eq]
  exact hMain

/-- **The expectation bound for the failure count**, by linearity of expectation from the
`BadAgainstSet` form of GWZ (106). -/
theorem lintegral_edFailCount_le [Nontrivial E] (hn : 1 < Module.finrank ℝ E) :
    ∃ (C : ENNReal) (δ₀ : NNReal), C ≠ ⊤ ∧ 0 < δ₀ ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ {ι : Type*} (s : Finset ι) (T : ι → Tube δ E) (T₀ : Tube δ E),
        T₀.carrier ⊆ Metric.closedBall (0 : E) (7 / 2) →
        ∫⁻ ω, (edFailCount s T T₀ ω : ENNReal) ∂(rigidMeasure E)
          ≤ C * (s.card : ENNReal) * (δ : ENNReal) ^ (2 * (Module.finrank ℝ E - 1)) := by
  classical
  obtain ⟨C0, d0, hC0, hd0, hKey⟩ := prob_rigidMove_badAgainstSet_le (E := E) hn
  refine ⟨C0, d0, hC0, hd0, ?_⟩
  intro δ hδ hδ_le ι s T T0 hT0B
  let K : Set E := Metric.cthickening (99 * (δ : ℝ)) T0.carrier
  have hK_meas : MeasurableSet K := by
    dsimp [K]
    exact Metric.isClosed_cthickening.measurableSet
  let P : ι → Set (unitary (E →L[ℝ] E) × E) := fun i =>
    {ω : unitary (E →L[ℝ] E) × E | BadAgainstSet ((T i).rigidMove ω.1 ω.2) K (edBridgeConstant E)}
  have hP_meas : ∀ i, MeasurableSet (P i) := by
    intro i
    dsimp [P]
    exact measurableSet_rigidMove_badAgainstSet (T := T i) (K := K) hK_meas
  have hmeas : ∀ i, Measurable (fun ω : unitary (E →L[ℝ] E) × E =>
      if ω ∈ P i then (1 : ENNReal) else 0) := by
    intro i
    exact Measurable.ite (hP_meas i) measurable_const measurable_const
  have hcount : ∀ ω : unitary (E →L[ℝ] E) × E,
      (edFailCount s T T0 ω : ENNReal) =
        ∑ i ∈ s, if ω ∈ P i then (1 : ENNReal) else 0 := by
    intro ω
    dsimp [edFailCount, P, K]
    rw [Finset.natCast_card_filter]
  have hterm : ∀ i, (∫⁻ ω : unitary (E →L[ℝ] E) × E,
      if ω ∈ P i then (1 : ENNReal) else 0 ∂(rigidMeasure E)) = rigidMeasure E (P i) := by
    intro i
    rw [show (fun ω : unitary (E →L[ℝ] E) × E =>
        if ω ∈ P i then (1 : ENNReal) else 0) = (P i).indicator (fun _ => (1 : ENNReal)) by
        funext ω
        rfl]
    exact lintegral_indicator_one (μ := rigidMeasure E) (s := P i) (hP_meas i)
  have hbound : ∀ i, rigidMeasure E (P i) ≤
      C0 * (δ : ENNReal) ^ (2 * (Module.finrank ℝ E - 1)) := by
    intro i
    dsimp [P, K]
    exact hKey hδ hδ_le (T i) T0 hT0B
  calc
    ∫⁻ ω, (edFailCount s T T0 ω : ENNReal) ∂(rigidMeasure E)
        = ∫⁻ ω, ∑ i ∈ s, if ω ∈ P i then (1 : ENNReal) else 0 ∂(rigidMeasure E) := by
          apply lintegral_congr
          intro ω
          exact hcount ω
    _ = ∑ i ∈ s, ∫⁻ ω, if ω ∈ P i then (1 : ENNReal) else 0 ∂(rigidMeasure E) := by
          exact lintegral_finsetSum' (μ := rigidMeasure E) (s := s)
            (f := fun (i : ι) (ω : unitary (E →L[ℝ] E) × E) =>
              if ω ∈ P i then (1 : ENNReal) else 0)
            (hf := fun i hi => (hmeas i).aemeasurable)
    _ ≤ ∑ i ∈ s, C0 * (δ : ENNReal) ^ (2 * (Module.finrank ℝ E - 1)) := by
          exact Finset.sum_le_sum (fun i _ => (hterm i).trans_le (hbound i))
    _ = (s.card : ENNReal) * (C0 * (δ : ENNReal) ^ (2 * (Module.finrank ℝ E - 1))) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = C0 * (s.card : ENNReal) * (δ : ENNReal) ^ (2 * (Module.finrank ℝ E - 1)) := by
          ring

/-- Measurability of the failure count as a random variable. -/
theorem measurable_edFailCount {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (T₀ : Tube δ E) :
    Measurable (fun ω : unitary (E →L[ℝ] E) × E => (edFailCount s T T₀ ω : ℝ)) := by
  classical
  have hK : MeasurableSet (Metric.cthickening (99 * (δ : ℝ)) T₀.carrier) :=
    Metric.isClosed_cthickening.measurableSet
  let P : ((unitary (E →L[ℝ] E) × E)) → ι → Prop := fun ω i =>
    BadAgainstSet ((T i).rigidMove ω.1 ω.2)
      (Metric.cthickening (99 * (δ : ℝ)) T₀.carrier) (edBridgeConstant E)
  have hmeas : ∀ i ∈ s,
      Measurable (fun ω : unitary (E →L[ℝ] E) × E => if P ω i then (1 : ℝ) else 0) := by
    intro i hi
    have hPmeas : MeasurableSet {ω : (unitary (E →L[ℝ] E) × E) | P ω i} := by
      dsimp [P]
      exact measurableSet_rigidMove_badAgainstSet (T := T i) hK
    exact Measurable.ite hPmeas measurable_const measurable_const
  have h_eq : (fun ω : (unitary (E →L[ℝ] E)) × E => (edFailCount s T T₀ ω : ℝ))
    = fun ω => s.sum (fun i => if P ω i then (1 : ℝ) else 0) := by
    funext ω
    unfold edFailCount P
    exact (Finset.sum_boole (fun i => P ω i) s).symm
  rw [h_eq]
  exact Finset.measurable_fun_sum s hmeas

end

end Kakeya

end
