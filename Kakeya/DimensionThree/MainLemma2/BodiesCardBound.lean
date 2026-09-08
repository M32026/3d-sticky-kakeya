/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThickCase
public import Kakeya.DimensionThree.MainLemma2.ThinConstantProducer

/-!
# The per-ball body count, and conjunct 2 of `SideDataObligations` closed

This file supplies the one geometric input that
`Kakeya.VeryNotSticky.thinConstantObligation_of_card_bodies` was left waiting on — the packing
bound `#𝕎_B ≤ C(C₀, Cbias) · δ^{-4}` for the bodies of a ball — and then composes it into
conjunct 2 of `Kakeya.VeryNotSticky.SideDataObligations`, which closes **outright**.

## The route

The count needs **no** essential distinctness and **no** `Tube` bridge. It is the field
`Kakeya.VeryNotSticky.BallData.bodies_antiClustering` tested against the ball itself: with
`K := ConvexSpaceBody.closedBall (bd.ctr B) r₁`,

* `Kakeya.VeryNotSticky.BallData.bodies_subset_ball` gives `bd.Wb j ≤ K` for every body, so
  `Kakeya.densityIn_of_all_le` evaluates `densityIn (bodies B) Wb K` as
  `(∑ |W_j|) / |K|`;
* `Kakeya.le_maxDensity` and `bodies_antiClustering` bound that quotient by
  `Cbias · δ^{-2ϱ}`;
* `Kakeya.VeryNotSticky.thickBodyVol` (from `bodies_thickness`) gives the per-body lower bound
  `|W_j| ≥ r₁ b a / (6 C₀³)`;
* `MeasureTheory.Measure.addHaar_closedBall` evaluates `|K| = r₁³ · |B(0,1)|`.

Hence `#𝕎_B · r₁ b a / (6C₀³) ≤ Cbias δ^{-2ϱ} r₁³ V₁`, and on the degenerate path
`a = b = δ`, using `r₁ ≤ 1` and `ϱ ≤ 1`, `#𝕎_B ≤ 6C₀³ Cbias V₁ δ^{-4}`.

The side condition `ϱ ≤ 1` is **not** a `Kakeya.VeryNotSticky` field (the configuration bounds
`ϱ` only from below, `hϱ : 0 < ϱ`); it is discharged from
`Kakeya.VeryNotSticky.CaseParams` by `Kakeya.VeryNotSticky.CaseParams.rho_le_one` below, the
exact analogue of `Kakeya.VeryNotSticky.CaseParams.eta_le_one` for the bias exponent.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter

universe u

/-! ### `ϱ ≤ 1` from the case parameters -/

/-- **`Kakeya.VeryNotSticky.CaseParams` gives `ϱ < 2^{-21}`, hence `ϱ ≤ 1`.**

The bias separation `slabBias : parameterSeparationConstant * ϱ < exscal` with
`parameterSeparationConstant = 2^20` and `scale : exscal < 1/2` give
`2^20 ϱ < 1/2`. This is the analogue of `Kakeya.VeryNotSticky.CaseParams.eta_le_one` for `ϱ`,
and it is the side condition the body count of this file needs; it is in scope at exactly the
place conjunct 2 is proved. -/
lemma CaseParams.rho_le_one {β ζ exscal ϱ η τ τ' : ℝ}
    (params : CaseParams β ζ exscal ϱ η τ τ') : ϱ ≤ 1 := by
  have h1 := params.slabBias
  have h2 := params.scale
  rw [parameterSeparationConstant] at h1
  nlinarith

/-! ### The body count -/

/-- **The body count, division-cleared and at general dimensions `(a, b)`.**

`#𝕎_B · (r₁ b a) ≤ 6 C₀³ Cbias · δ^{-2ϱ} · |B(ctr B, r₁)|`.

Uses only the existing `Kakeya.VeryNotSticky.BallData` fields `bodies_subset_ball`,
`bodies_thickness` (through `Kakeya.VeryNotSticky.thickBodyVol`) and
`bodies_antiClustering`: no essential distinctness, no tube bridge (the tube machinery is not
even in this file's import closure), and no direction count, because `Kakeya.maxDensity`
already encodes the packing. -/
theorem card_bodies_mul_le (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    {B : bd.bι} (hB : B ∈ bd.bs) :
    ((bd.bodies B).card : ENNReal) * ((cfg.r₁ * cfg.b * cfg.a : NNReal) : ENNReal)
      ≤ (((6 * bd.C₀ ^ 3 * bd.Cbias : NNReal)) : ENNReal) *
          (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) *
          volume (Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) := by
  classical
  have hr0 : (0 : ℝ) ≤ (cfg.r₁ : ℝ) := (cfg.r₁).coe_nonneg
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by
    have h : (0 : NNReal) < cfg.r₁ := NNReal.rpow_pos cfg.hδ
    exact_mod_cast h
  set K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    ConvexSpaceBody.closedBall (bd.ctr B) (cfg.r₁ : ℝ) hr0 with hK
  have hKcarr : K.carrier = Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ) := rfl
  have hKpos : volume K.carrier ≠ 0 := by
    rw [hKcarr]; exact (measure_closedBall_pos volume _ hr₁pos).ne'
  have hKtop : volume K.carrier ≠ ⊤ := by
    rw [hKcarr]; exact measure_closedBall_lt_top.ne
  have hall : ∀ j ∈ bd.bodies B, bd.Wb j ≤ K := by
    intro j hj
    have h := bd.bodies_subset_ball B hB j hj
    exact (show (bd.Wb j).carrier ⊆ K.carrier from by simpa [hKcarr] using h)
  -- the per-body volume lower bound (`thickBodyVol`, from `bodies_thickness`)
  have hlow : ∀ j ∈ bd.bodies B,
      (((6 * bd.C₀ ^ 3 : NNReal) : ENNReal))⁻¹ * ((cfg.r₁ * cfg.b * cfg.a : NNReal) : ENNReal)
        ≤ volume (bd.Wb j).carrier := fun j hj => (thickBodyVol cfg bd hB hj).1
  have hsum :
      ((bd.bodies B).card : ENNReal) *
          ((((6 * bd.C₀ ^ 3 : NNReal) : ENNReal))⁻¹ *
            ((cfg.r₁ * cfg.b * cfg.a : NNReal) : ENNReal))
        ≤ ∑ j ∈ bd.bodies B, volume (bd.Wb j).carrier := by
    have := Finset.card_nsmul_le_sum (bd.bodies B) (fun j => volume (bd.Wb j).carrier)
      ((((6 * bd.C₀ ^ 3 : NNReal) : ENNReal))⁻¹ *
        ((cfg.r₁ * cfg.b * cfg.a : NNReal) : ENNReal)) hlow
    simpa [nsmul_eq_mul] using this
  -- the density upper bound (`bodies_antiClustering` through `le_maxDensity`)
  have hdens : (∑ j ∈ bd.bodies B, volume (bd.Wb j).carrier) / volume K.carrier
      ≤ (bd.Cbias : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) := by
    have h1 : densityIn (bd.bodies B) bd.Wb K
        = (∑ j ∈ bd.bodies B, volume (bd.Wb j).carrier) / volume K.carrier :=
      densityIn_of_all_le hall
    calc (∑ j ∈ bd.bodies B, volume (bd.Wb j).carrier) / volume K.carrier
        = densityIn (bd.bodies B) bd.Wb K := h1.symm
      _ ≤ maxDensity (bd.bodies B) bd.Wb := le_maxDensity _ _ _
      _ ≤ (bd.Cbias : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) :=
          bd.bodies_antiClustering B hB
  have hclear : (∑ j ∈ bd.bodies B, volume (bd.Wb j).carrier)
      ≤ (bd.Cbias : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) * volume K.carrier :=
    (ENNReal.div_le_iff hKpos hKtop).1 hdens
  -- combine and clear the `(6 C₀³)⁻¹`
  have hchain :
      ((bd.bodies B).card : ENNReal) *
          ((((6 * bd.C₀ ^ 3 : NNReal) : ENNReal))⁻¹ *
            ((cfg.r₁ * cfg.b * cfg.a : NNReal) : ENNReal))
        ≤ (bd.Cbias : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) * volume K.carrier :=
    le_trans hsum hclear
  have h6ne : (((6 * bd.C₀ ^ 3 : NNReal) : ENNReal)) ≠ 0 := by
    have h : (6 * bd.C₀ ^ 3 : NNReal) ≠ 0 := by
      have h1 : (1 : NNReal) ≤ bd.C₀ := bd.hC₀
      positivity
    simpa using h
  have h6top : (((6 * bd.C₀ ^ 3 : NNReal) : ENNReal)) ≠ ⊤ := ENNReal.coe_ne_top
  set C6 : ENNReal := ((6 * bd.C₀ ^ 3 : NNReal) : ENNReal) with hC6
  set X : ENNReal := ((cfg.r₁ * cfg.b * cfg.a : NNReal) : ENNReal) with hX
  have hE : C6 * (((bd.bodies B).card : ENNReal) * (C6⁻¹ * X))
      = ((bd.bodies B).card : ENNReal) * X := by
    have h : C6 * (((bd.bodies B).card : ENNReal) * (C6⁻¹ * X))
        = (C6 * C6⁻¹) * (((bd.bodies B).card : ENNReal) * X) := by ring
    rw [h, ENNReal.mul_inv_cancel h6ne h6top, one_mul]
  calc ((bd.bodies B).card : ENNReal) * X
      = C6 * (((bd.bodies B).card : ENNReal) * (C6⁻¹ * X)) := hE.symm
    _ ≤ C6 * ((bd.Cbias : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) * volume K.carrier) := by
        gcongr
    _ = (((6 * bd.C₀ ^ 3 * bd.Cbias : NNReal)) : ENNReal) *
          (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) *
          volume (Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) := by
        rw [hKcarr, hC6]; push_cast; ring

/-- The `δ`-free body-count constant, in `ENNReal`. -/
noncomputable def bodiesCardConst (C₀ Cbias : NNReal) : ENNReal :=
  ((6 * C₀ ^ 3 * Cbias : NNReal) : ENNReal) *
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)

/-- The `δ`-free body-count constant, in `NNReal`: the shape
`Kakeya.VeryNotSticky.exists_thinConfig_le_of_card_bounds` consumes. -/
noncomputable def bodiesCardConstNN (C₀ Cbias : NNReal) : NNReal :=
  6 * C₀ ^ 3 * Cbias * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)).toNNReal

lemma coe_bodiesCardConstNN (C₀ Cbias : NNReal) :
    ((bodiesCardConstNN C₀ Cbias : NNReal) : ENNReal) = bodiesCardConst C₀ Cbias := by
  rw [bodiesCardConstNN, bodiesCardConst]
  push_cast
  rw [ENNReal.coe_toNNReal measure_ball_lt_top.ne]

/-- **The body count on the degenerate path `a = b = δ`**: `#𝕎_B ≤ C(C₀, Cbias) · δ^{-4}`,
from existing `Kakeya.VeryNotSticky.BallData` fields only. -/
theorem card_bodies_le (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (hϱ1 : cfg.ϱ ≤ 1) (ha : cfg.a = cfg.δ) (hb : cfg.b = cfg.δ)
    {B : bd.bι} (hB : B ∈ bd.bs) :
    ((bd.bodies B).card : ENNReal)
      ≤ bodiesCardConst bd.C₀ bd.Cbias * ((cfg.δ : ENNReal)⁻¹) ^ 4 := by
  classical
  have hδ0 : (0 : NNReal) < cfg.δ := cfg.hδ
  have hδ1 : cfg.δ ≤ 1 := cfg.hδ1
  have hr₁pos : (0 : NNReal) < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  have hr₁1 : cfg.r₁ ≤ 1 := NNReal.rpow_le_one hδ1 cfg.hexscal.le
  have hr0 : (0 : ℝ) ≤ (cfg.r₁ : ℝ) := (cfg.r₁).coe_nonneg
  have key := card_bodies_mul_le cfg bd hB
  rw [ha, hb] at key
  -- volume of the ball
  have hvol : volume (Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ))
      = ENNReal.ofReal ((cfg.r₁ : ℝ) ^ 3) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    have h := Measure.addHaar_closedBall
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) (bd.ctr B) hr0
    rw [h]
    simp
  have hofReal : ENNReal.ofReal ((cfg.r₁ : ℝ) ^ 3) = (cfg.r₁ : ENNReal) ^ 3 := by
    rw [ENNReal.ofReal_pow hr0, ENNReal.ofReal_coe_nnreal]
  rw [hvol, hofReal] at key
  -- the `ϱ`-to-`2` conversion
  have hrpow : (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) ≤ (cfg.δ : ENNReal) ^ (-(2 : ℝ)) := by
    refine ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1) ?_
    have h : (2 : ℝ) * cfg.ϱ ≤ 2 := by nlinarith [cfg.hϱ]
    linarith
  have hδinv2 : (cfg.δ : ENNReal) ^ (-(2 : ℝ)) = ((cfg.δ : ENNReal)⁻¹) ^ 2 := by
    rw [show (-(2:ℝ)) = -(2:ℕ) by norm_num, ENNReal.rpow_neg, ENNReal.rpow_natCast]
    rw [← ENNReal.inv_pow]
  rw [hδinv2] at hrpow
  -- now clear `r₁ * δ * δ`
  set V₁ : ENNReal := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) with hV₁
  set C6 : ENNReal := ((6 * bd.C₀ ^ 3 * bd.Cbias : NNReal) : ENNReal) with hC6
  set d : ENNReal := (cfg.δ : ENNReal) with hd
  set R : ENNReal := (cfg.r₁ : ENNReal) with hR
  have hdne : d ≠ 0 := by simp [hd, hδ0.ne']
  have hdtop : d ≠ ⊤ := by simp [hd]
  have hRne : R ≠ 0 := by simp [hR, hr₁pos.ne']
  have hRtop : R ≠ ⊤ := by simp [hR]
  have hRle : R ≤ 1 := by simpa [hR] using (ENNReal.coe_le_one_iff).2 hr₁1
  -- `key : card * (R * d * d) ≤ C6 * δ^{-2ϱ} * (R³ * V₁)`
  have hkey2 : ((bd.bodies B).card : ENNReal) * (R * (d * d))
      ≤ C6 * ((d⁻¹) ^ 2) * (R ^ 3 * V₁) := by
    refine le_trans (le_of_eq ?_) (le_trans key ?_)
    · push_cast; ring
    · gcongr
  have hmul : R * (d * d) ≠ 0 := by simp [hRne, hdne]
  have hmultop : R * (d * d) ≠ ⊤ :=
    ENNReal.mul_ne_top hRtop (ENNReal.mul_ne_top hdtop hdtop)
  have hfinal : ((bd.bodies B).card : ENNReal)
      ≤ C6 * ((d⁻¹) ^ 2) * (R ^ 3 * V₁) * (R * (d * d))⁻¹ := by
    rw [← ENNReal.le_div_iff_mul_le (Or.inl hmul) (Or.inl hmultop)] at hkey2
    rwa [ENNReal.div_eq_inv_mul, ← mul_comm] at hkey2
  refine le_trans hfinal ?_
  have hrw : C6 * ((d⁻¹) ^ 2) * (R ^ 3 * V₁) * (R * (d * d))⁻¹
      = (C6 * V₁) * ((d⁻¹) ^ 2 * (d * d)⁻¹) * (R ^ 3 * R⁻¹) := by
    rw [ENNReal.mul_inv (Or.inl hRne) (Or.inl hRtop)]
    ring
  rw [hrw]
  have hd2 : (d * d)⁻¹ = (d⁻¹) ^ 2 := by
    rw [ENNReal.mul_inv (Or.inl hdne) (Or.inl hdtop)]; ring
  rw [hd2]
  have hRR : R ^ 3 * R⁻¹ = R ^ 2 := by
    have h : R ^ 3 = R ^ 2 * R := by ring
    rw [h, mul_assoc, ENNReal.mul_inv_cancel hRne hRtop, mul_one]
  have hR2 : R ^ 2 ≤ 1 := by
    calc R ^ 2 ≤ (1 : ENNReal) ^ 2 := by gcongr
      _ = 1 := one_pow 2
  rw [hRR]
  calc (C6 * V₁) * (d⁻¹ ^ 2 * d⁻¹ ^ 2) * R ^ 2
      ≤ (C6 * V₁) * (d⁻¹ ^ 2 * d⁻¹ ^ 2) * 1 := by gcongr
    _ = bodiesCardConst bd.C₀ bd.Cbias * (d⁻¹) ^ 4 := by
        rw [mul_one, bodiesCardConst, hC6, hV₁]; ring

/-- **The body count in the `NNReal` shape the thin-constant pipeline consumes**:
`#𝕎_B ≤ bodiesCardConstNN C₀ Cbias · δ⁻¹ ^ 4`, at `Kbodies = 4`. -/
theorem card_bodies_le_nnreal (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (hϱ1 : cfg.ϱ ≤ 1) (ha : cfg.a = cfg.δ) (hb : cfg.b = cfg.δ)
    {B : bd.bι} (hB : B ∈ bd.bs) :
    (((bd.bodies B).card : ℕ) : NNReal)
      ≤ bodiesCardConstNN bd.C₀ bd.Cbias * cfg.δ⁻¹ ^ 4 := by
  have hδ0 : (0 : NNReal) < cfg.δ := cfg.hδ
  have h := card_bodies_le cfg bd hϱ1 ha hb hB
  rw [← coe_bodiesCardConstNN, ← ENNReal.coe_inv hδ0.ne', ← ENNReal.coe_pow,
    ← ENNReal.coe_mul] at h
  have hcast : ((bd.bodies B).card : ENNReal)
      = (((((bd.bodies B).card : ℕ) : NNReal)) : ENNReal) := by
    simp
  rw [hcast, ENNReal.coe_le_coe] at h
  exact h

/-! ### The thin-constant obligation, unconditionally -/

/-- **`Kakeya.VeryNotSticky.ThinConstantObligation`, with no remaining hypothesis.**

This is `Kakeya.VeryNotSticky.thinConstantObligation_of_card_bodies` with its `hbodies` binder
discharged. It cannot be discharged by applying that theorem: its `hbodies` quantifies over
**all** `cfg` and `bd` with no pins, whereas the body count needs `cfg.a = cfg.δ`,
`cfg.b = cfg.δ` and `cfg.ϱ = ϱ ≤ 1`, and its constant depends on `bd.C₀`, `bd.Cbias`. All five
are pinned *inside* `ThinConstantObligation`'s own `∀ᶠ`, so the count is applied there instead:
the proof re-runs the two-line composition of
`Kakeya.VeryNotSticky.exists_thinConfig_le_of_card_bounds` with
`Kakeya.VeryNotSticky.eventually_card_segs_le` and feeds
`Kakeya.VeryNotSticky.card_bodies_le_nnreal` under the pins. -/
theorem thinConstantObligation_of_le_one (β exscal ϱ η ε : ℝ) (hε : 0 < ε)
    (hη1 : η ≤ 1) (hϱ1 : ϱ ≤ 1)
    (C₀bd Cbias CF Cdil c₁ Cg : NNReal) (D : ℕ) :
    ThinConstantObligation.{u} β exscal ϱ η ε C₀bd Cbias CF Cdil c₁ Cg D := by
  rw [ThinConstantObligation]
  filter_upwards [exists_thinConfig_le_of_card_bounds ε hε C₀bd CF c₁ Cg 1
      (bodiesCardConstNN C₀bd Cbias) D 4 4,
    eventually_card_segs_le (η := η) hη1] with δ hred hseg
  intro cfg bd hδ hβ hη hexscal hϱ ha hb hC₀ hCbias hCF hCdil hc₁ hD hCg hm hCm hδw₁ hw₁one
  refine hred cfg bd hδ hC₀ hCF hc₁ hD hCg hCm hδw₁ hw₁one (hseg cfg bd hδ hη) ?_
  intro B hB
  have hϱ1' : cfg.ϱ ≤ 1 := by rw [hϱ]; exact hϱ1
  have h := card_bodies_le_nnreal cfg bd hϱ1' ha hb hB
  rwa [hC₀, hCbias] at h

/-! ### Conjunct 2 of `SideDataObligations`, closed -/

/-- **Conjunct 2 of `Kakeya.VeryNotSticky.SideDataObligations`, closed outright.**

Its conclusion is that conjunct verbatim, and it has **no** remaining cardinality or
thin-constant hypothesis: the whole chain is composed here — the body count of this file
(`Kakeya.VeryNotSticky.card_bodies_le`), the segment count and the polylogarithmic sizing of
`Kakeya.VeryNotSticky.exists_thinConfig_le_of_card_bounds`, and the existing reduction
`Kakeya.VeryNotSticky.sideDataObligations_conjunct2_of_thinConstant`.

Both side conditions come from `params`: `η ≤ 1` by
`Kakeya.VeryNotSticky.CaseParams.eta_le_one` and `ϱ ≤ 1` by
`Kakeya.VeryNotSticky.CaseParams.rho_le_one`. -/
theorem sideDataObligations_conjunct2 {β ζ exscal ϱ η τ τ' : ℝ}
    (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    {C₀bd Cbias CF Cdil c₁ Cg : NNReal} (hC₀bd : 1 ≤ C₀bd) {D : ℕ} :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
    cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
    cfg.a = cfg.δ → cfg.b = cfg.δ →
    bd.C₀ = C₀bd → bd.Cbias = Cbias → bd.CF = CF → bd.Cdil = Cdil → bd.c₁ = c₁ → bd.D = D →
    bd.Cg = Cg → bd.m = 1 → bd.Cm = 1 → cfg.δ ≤ bd.w₁ → bd.w₁ ≤ 1 →
    ∃ (tc : ThinConfig cfg bd) (thr₀ : ScaleThresholds),
      SlabScale cfg bd tc τ ∧
      CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr₀ ∧
      ((tangentialSlabDecompConstant tc.C : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) :=
  sideDataObligations_conjunct2_of_thinConstant hexscal hϱ hη params hC₀bd
    (thinConstantObligation_of_le_one β exscal ϱ η (thresholdExponent β exscal η τ)
      (thresholdExponent_pos hη params) (CaseParams.eta_le_one hη params)
      (CaseParams.rho_le_one params) C₀bd Cbias CF Cdil c₁ Cg D)

/-- **Tripwire: the conclusion above really is conjunct 2 of
`Kakeya.VeryNotSticky.SideDataObligations`.**

It rebuilds `SideDataObligations` from a hypothetical instance with its **second** component
replaced by `Kakeya.VeryNotSticky.sideDataObligations_conjunct2`. This elaborates only if that
theorem's conclusion is definitionally the second conjunct, so any drift in
`SideDataObligations`' conjunct order or conjunct-2 text breaks *this* declaration rather than
passing silently. (It is mathematically vacuous — conjuncts 1 and 6 are still open — and is
kept as an `example` so it adds no name to the API.) -/
example {β ζ exscal ϱ η τ τ' : ℝ}
    (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    {C₀bd Cbias CF Cdil c₁ Cg : NNReal} (hC₀bd : 1 ≤ C₀bd) {D : ℕ}
    (h : SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D) :
    SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D :=
  ⟨h.1, sideDataObligations_conjunct2 hexscal hϱ hη params hC₀bd, h.2.2⟩

end Kakeya.VeryNotSticky

end
