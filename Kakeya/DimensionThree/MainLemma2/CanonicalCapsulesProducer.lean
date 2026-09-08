/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.CanonicalCapsulesLevel
public import Kakeya.DimensionThree.MainLemma2.BallDataGeneralProducer

/-!
# C7-b: the canonical-capsule core meets the general-branch contract

The per-ball clauses of `Kakeya.VeryNotSticky.CoverData.capsuleCore` that the T3 core could not
deliver, and the spec theorem `exists_core_capsule_of_cover` — the canonical-capsule analogue of
`Kakeya.VeryNotSticky.exists_core_localised_of_cover` — which the general-branch producer consumes
in place of T3's:

* **SP-H** (`card_fib_le_fibreMass`): a fibre has at most `fibreMassConstant · δ^{-(η+2 exscal)}`
  members (refined `eqvnsfibresize`, l.5377): `#fibre · c₃ δ² ≤ Δ_max · |fibreBody|`
  (`CanonicalCapsulesFibre.lean`) with `|fibreBody| ≤ 1960 δ²/r₁²` at `L = r₁/4`, `ε = δ`,
  `Δ_max ≤ δ^{-η}`, `r₁ = δ^{exscal}`, `c₃ = 4π/9 > 4/3`; so the level `m = 2^k ≤ #fibre` of a
  nonempty bin sits inside the budget with `Cm = 1`.
* **The non-ED degree** (`edDegree_segs_le`): the net capsules of a ball have non-ED degree
  `≤ 2·(40·C₃+1)⁶ ≤ 2·4201⁶ = edMultiplicityConstant` (`CapsuleNet.edDegree_capsuleAt_le` at
  `ρ = 2δ`, `ε = δ`, and `C₃ = 9 + 128/c₃ ≤ 105` from `π > 3`) — the `hEDdeg` of the boundary.
* **The dilation clause** at the ceiling `capsuleDilationConstant`
  (`CanonicalCapsulesDilation.lean`, reindexed by `maxDensity_image`).
* Localisation at `11 r₁/16` and the card bound.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace Kakeya.VeryNotSticky

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The dimensional constants, numerically -/

/-- `Tube.le_volume.c 3 = 4π/9` (`Γ(5/2) = (3/4)√π`). -/
theorem le_volume_c_three_eq : ((Tube.le_volume.c 3 : NNReal) : ℝ) = 4 * Real.pi / 9 := by
  change Real.sqrt Real.pi ^ 3 / Real.Gamma (((3 : ℕ) : ℝ) / 2 + 1) / 3 = 4 * Real.pi / 9
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h1 : (((3 : ℕ) : ℝ) / 2 + 1) = 3 / 2 + 1 := by norm_num
  have hG32 : Real.Gamma (3 / 2 : ℝ) = 1 / 2 * Real.sqrt Real.pi := by
    have h : (3 / 2 : ℝ) = 1 / 2 + 1 := by norm_num
    rw [h, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  have hG52 : Real.Gamma (3 / 2 + 1 : ℝ) = 3 / 4 * Real.sqrt Real.pi := by
    rw [Real.Gamma_add_one (by norm_num), hG32]; ring
  rw [h1, hG52]
  have hsq : Real.sqrt Real.pi ^ 3 = Real.pi * Real.sqrt Real.pi := by
    have h := Real.sq_sqrt Real.pi_pos.le
    nlinarith [h]
  rw [hsq]
  field_simp
  ring

/-- `4/3 < c₃` (from `π > 3`). -/
theorem four_thirds_lt_le_volume_c_three : (4 / 3 : ℝ) < ((Tube.le_volume.c 3 : NNReal) : ℝ) := by
  rw [le_volume_c_three_eq]
  have := Real.pi_gt_three
  linarith

/-- `C₃ = 9 + 128/c₃ ≤ 105`. -/
theorem tubeOverlapCoreClose_C_three_le : Kakeya.Tube.tubeOverlapCoreClose.C 3 ≤ 105 := by
  have h : Kakeya.Tube.tubeOverlapCoreClose.C 3 =
      9 + 2 * 4 ^ 3 / ((Tube.le_volume.c 3 : NNReal) : ℝ) := edComparabilityConstant_eq
  rw [h]
  have hc := four_thirds_lt_le_volume_c_three
  have hc0 : (0 : ℝ) < ((Tube.le_volume.c 3 : NNReal) : ℝ) := by linarith
  have : 2 * 4 ^ 3 / ((Tube.le_volume.c 3 : NNReal) : ℝ) ≤ 96 := by
    rw [div_le_iff₀ hc0]; linarith
  linarith

namespace CoverData

variable {cfg : VeryNotSticky.{u}} {bι : Type u} (cd : CoverData cfg bι)

/-! ### SP-H: the fibre count inside the budget -/

theorem r₁_pos (cfg : VeryNotSticky.{u}) : (0 : ℝ) < (cfg.r₁ : ℝ) := by
  exact_mod_cast NNReal.rpow_pos cfg.hδ

theorem fibreRadius_capL (cfg : VeryNotSticky.{u}) :
    fibreRadius cfg.δ (cfg.δ : ℝ) (capL cfg) = (cfg.δ : ℝ) * (3 + 4 / (cfg.r₁ : ℝ)) := by
  have hr := r₁_pos cfg
  unfold fibreRadius capL
  field_simp
  ring

/-- The fibre body's volume constant at `L = r₁/4`, `ε = δ`: `≤ 1960 δ² / r₁²`. -/
theorem fibre_body_const_le (cfg : VeryNotSticky.{u}) :
    (2 * (1 + capL cfg)) ^ 3 * (16 : ℝ) *
        ((fibreBodyRadius cfg.δ (cfg.δ : ℝ) (capL cfg) : NNReal) : ℝ) ^ 2 ≤
      1960 * (cfg.δ : ℝ) ^ 2 / (cfg.r₁ : ℝ) ^ 2 := by
  have hr := r₁_pos cfg
  have hr1 := r₁_le_one cfg
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  have hL := capL_pos cfg
  rw [coe_fibreBodyRadius hδ0 hL, fibreRadius_capL]
  have hA : (0 : ℝ) < 2 * (1 + capL cfg) := by positivity
  have e : (2 * (1 + capL cfg)) ^ 3 * (16 : ℝ) *
      ((cfg.δ : ℝ) * (3 + 4 / (cfg.r₁ : ℝ)) / (2 * (1 + capL cfg))) ^ 2 =
      16 * (2 * (1 + capL cfg)) * ((cfg.δ : ℝ) * (3 + 4 / (cfg.r₁ : ℝ))) ^ 2 := by
    field_simp
  rw [e]
  have h1 : 2 * (1 + capL cfg) ≤ 5 / 2 := by unfold capL; linarith
  have h2 : 3 + 4 / (cfg.r₁ : ℝ) ≤ 7 / (cfg.r₁ : ℝ) := by
    have : (3 : ℝ) ≤ 3 / (cfg.r₁ : ℝ) := by
      rw [le_div_iff₀ hr]; linarith
    have e2 : (7 : ℝ) / (cfg.r₁ : ℝ) = 3 / (cfg.r₁ : ℝ) + 4 / (cfg.r₁ : ℝ) := by ring
    rw [e2]; linarith
  have h3 : (0 : ℝ) ≤ (cfg.δ : ℝ) * (3 + 4 / (cfg.r₁ : ℝ)) := by positivity
  calc 16 * (2 * (1 + capL cfg)) * ((cfg.δ : ℝ) * (3 + 4 / (cfg.r₁ : ℝ))) ^ 2
      ≤ 16 * (5 / 2) * ((cfg.δ : ℝ) * (7 / (cfg.r₁ : ℝ))) ^ 2 := by
        gcongr
    _ = 1960 * (cfg.δ : ℝ) ^ 2 / (cfg.r₁ : ℝ) ^ 2 := by
        field_simp
        ring

theorem fibreRadius_le_two_mul (cd : CoverData cfg bι) :
    fibreRadius cfg.δ (cfg.δ : ℝ) (capL cfg) ≤ 2 * (1 + capL cfg) := by
  rw [fibreRadius_capL]
  have hr := r₁_pos cfg
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  have hδr := cd.δr
  have hδ1 : (cfg.δ : ℝ) ≤ 1 / 32 := by have := r₁_le_one cfg; linarith
  have h4 : (cfg.δ : ℝ) * (4 / (cfg.r₁ : ℝ)) ≤ 1 / 8 := by
    rw [← mul_div_assoc, div_le_iff₀ hr]; linarith
  have hL0 := capL_nonneg cfg
  nlinarith

/-- `r₁² = δ^{2 exscal}` in `ℝ≥0∞`. -/
theorem r₁_sq_eq (cfg : VeryNotSticky.{u}) :
    (cfg.r₁ : ENNReal) ^ 2 = (cfg.δ : ENNReal) ^ (2 * cfg.exscal) := by
  have h1 : ((cfg.r₁ : NNReal) : ENNReal) = (cfg.δ : ENNReal) ^ cfg.exscal := by
    rw [show cfg.r₁ = cfg.δ ^ cfg.exscal from rfl,
      ENNReal.coe_rpow_of_ne_zero (by exact_mod_cast ne_of_gt cfg.hδ)]
  rw [h1, ← ENNReal.rpow_natCast ((cfg.δ : ENNReal) ^ cfg.exscal) 2, ← ENNReal.rpow_mul]
  norm_num
  ring_nf

open scoped Classical in
/-- **SP-H for the fibres** (refined `eqvnsfibresize`, l.5377): `#fibre ≤ fibreMassConstant ·
δ^{-(η + 2 exscal)}`, at `L = r₁/4`, `ε = δ`. -/
theorem card_fib_le_fibreMass {B : bι} (hB : B ∈ cd.bs) (ν : cfg.ι) :
    ((cd.fib B ν).card : ENNReal) ≤
      (fibreMassConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) := by
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  have hδpos : (0 : ℝ) < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
  have hr := r₁_pos cfg
  have hδE0 : (cfg.δ : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt cfg.hδ
  have hδEtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hr₁E0 : (cfg.r₁ : ENNReal) ≠ 0 := by exact_mod_cast (NNReal.rpow_pos cfg.hδ).ne'
  have hr₁Etop : (cfg.r₁ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hc₃pos : (0 : ℝ) < ((Tube.le_volume.c 3 : NNReal) : ℝ) := by
    have := four_thirds_lt_le_volume_c_three; linarith
  have hc₃0 : ((Tube.le_volume.c 3 : NNReal) : ENNReal) ≠ 0 := by
    exact_mod_cast (Tube.le_volume.c_pos 3).ne'
  have hc₃top : ((Tube.le_volume.c 3 : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- the compiled fibre bound
  have h := (cd.net B).card_fibre_mul_le (cd.idx_subset B) hδ0 (capL_pos cfg)
    (r := (cfg.r₁ : ℝ) / 16) cd.r16_add_δ_le_capL (fun i hi => cd.meets_of_mem_idx hB hi)
    cd.fibreRadius_le_two_mul ν
  -- the body constant, as `ofReal` of a real, bounded by `1960 δ²/r₁²`
  have hK : ENNReal.ofReal ((2 * (1 + capL cfg)) ^ 3) *
      ((Tube.volume_le.C 3 : ENNReal) *
        (fibreBodyRadius cfg.δ (cfg.δ : ℝ) (capL cfg) : ENNReal) ^ 2)
      ≤ ENNReal.ofReal (1960 * (cfg.δ : ℝ) ^ 2 / (cfg.r₁ : ℝ) ^ 2) := by
    have hC : ((Tube.volume_le.C 3 : NNReal) : ENNReal) = ENNReal.ofReal 16 := by
      rw [show (Tube.volume_le.C 3 : NNReal) = 16 by norm_num [Tube.volume_le.C]]
      norm_num
    rw [hC, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow (NNReal.coe_nonneg _),
      ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (pow_nonneg (by have := capL_nonneg cfg; positivity) 3)]
    exact ENNReal.ofReal_le_ofReal (by
      have := fibre_body_const_le cfg
      calc (2 * (1 + capL cfg)) ^ 3 *
            (16 * ((fibreBodyRadius cfg.δ (cfg.δ : ℝ) (capL cfg) : NNReal) : ℝ) ^ 2)
          = (2 * (1 + capL cfg)) ^ 3 * (16 : ℝ) *
            ((fibreBodyRadius cfg.δ (cfg.δ : ℝ) (capL cfg) : NNReal) : ℝ) ^ 2 := by ring
        _ ≤ _ := this)
  have h2 : ((cd.fib B ν).card : ENNReal) *
      (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2) ≤
      (cfg.δ : ENNReal) ^ (-cfg.η) * ENNReal.ofReal (1960 * (cfg.δ : ℝ) ^ 2 / (cfg.r₁ : ℝ) ^ 2) :=
    h.trans (mul_le_mul' cfg.maxDensity_le hK)
  -- `ofReal (1960 δ²/r₁²) = 1960 * δ² * (r₁²)⁻¹`
  have h3 : ENNReal.ofReal (1960 * (cfg.δ : ℝ) ^ 2 / (cfg.r₁ : ℝ) ^ 2) =
      1960 * (cfg.δ : ENNReal) ^ 2 * ((cfg.r₁ : ENNReal) ^ 2)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_pow hδ0, ENNReal.ofReal_pow (cfg.r₁).coe_nonneg,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal, div_eq_mul_inv]
  rw [h3] at h2
  -- cancel `δ²`, move `c₃` to the right
  have hsq0 : (cfg.δ : ENNReal) ^ 2 ≠ 0 := pow_ne_zero _ hδE0
  have hsqtop : (cfg.δ : ENNReal) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hδEtop
  have h4 : ((cd.fib B ν).card : ENNReal) * ((Tube.le_volume.c 3 : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-cfg.η) * (1960 * ((cfg.r₁ : ENNReal) ^ 2)⁻¹) := by
    refine (ENNReal.mul_le_mul_iff_left hsq0 hsqtop).1 ?_
    calc ((cd.fib B ν).card : ENNReal) * ((Tube.le_volume.c 3 : NNReal) : ENNReal) *
          (cfg.δ : ENNReal) ^ 2
        = ((cd.fib B ν).card : ENNReal) *
          (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ 2) := by ring
      _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) *
          (1960 * (cfg.δ : ENNReal) ^ 2 * ((cfg.r₁ : ENNReal) ^ 2)⁻¹) := h2
      _ = (cfg.δ : ENNReal) ^ (-cfg.η) * (1960 * ((cfg.r₁ : ENNReal) ^ 2)⁻¹) *
          (cfg.δ : ENNReal) ^ 2 := by ring
  -- `1960 ≤ 3267 c₃`
  have h5 : (1960 : ENNReal) ≤ (fibreMassConstant : ENNReal) *
      ((Tube.le_volume.c 3 : NNReal) : ENNReal) := by
    have hreal : (1960 : ℝ) ≤ 3267 * ((Tube.le_volume.c 3 : NNReal) : ℝ) := by
      have := four_thirds_lt_le_volume_c_three; linarith
    have hnn : (1960 : NNReal) ≤ 3267 * Tube.le_volume.c 3 := by exact_mod_cast hreal
    have : ((1960 : NNReal) : ENNReal) ≤ ((3267 * Tube.le_volume.c 3 : NNReal) : ENNReal) := by
      exact_mod_cast hnn
    simpa [fibreMassConstant] using this
  have hr₁sq0 : (cfg.r₁ : ENNReal) ^ 2 ≠ 0 := pow_ne_zero _ hr₁E0
  have hr₁sqtop : (cfg.r₁ : ENNReal) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hr₁Etop
  have h6 : ((cd.fib B ν).card : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-cfg.η) *
        ((fibreMassConstant : ENNReal) * ((cfg.r₁ : ENNReal) ^ 2)⁻¹) := by
    refine (ENNReal.mul_le_mul_iff_left hc₃0 hc₃top).1 ?_
    calc ((cd.fib B ν).card : ENNReal) * ((Tube.le_volume.c 3 : NNReal) : ENNReal)
        ≤ (cfg.δ : ENNReal) ^ (-cfg.η) * (1960 * ((cfg.r₁ : ENNReal) ^ 2)⁻¹) := h4
      _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) * ((fibreMassConstant : ENNReal) *
          ((Tube.le_volume.c 3 : NNReal) : ENNReal) * ((cfg.r₁ : ENNReal) ^ 2)⁻¹) := by gcongr
      _ = (cfg.δ : ENNReal) ^ (-cfg.η) *
          ((fibreMassConstant : ENNReal) * ((cfg.r₁ : ENNReal) ^ 2)⁻¹) *
          ((Tube.le_volume.c 3 : NNReal) : ENNReal) := by ring
  -- `(r₁²)⁻¹ = δ^{-2 exscal}`, and the exponents add
  have h7 : ((cfg.r₁ : ENNReal) ^ 2)⁻¹ = (cfg.δ : ENNReal) ^ (-(2 * cfg.exscal)) := by
    rw [r₁_sq_eq, ENNReal.rpow_neg]
  have h8 : (cfg.δ : ENNReal) ^ (-cfg.η) * (cfg.δ : ENNReal) ^ (-(2 * cfg.exscal)) =
      (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) := by
    rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]; ring_nf
  calc ((cd.fib B ν).card : ENNReal)
      ≤ (cfg.δ : ENNReal) ^ (-cfg.η) *
          ((fibreMassConstant : ENNReal) * ((cfg.r₁ : ENNReal) ^ 2)⁻¹) := h6
    _ = (fibreMassConstant : ENNReal) *
          ((cfg.δ : ENNReal) ^ (-cfg.η) * (cfg.δ : ENNReal) ^ (-(2 * cfg.exscal))) := by
        rw [h7]; ring
    _ = (fibreMassConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) := by
        rw [h8]

open scoped Classical in
/-- The level of a nonempty bin sits inside the fibre budget. -/
theorem pow_le_fibreMass {B : bι} (hB : B ∈ cd.bs) {ν : cfg.ι} {k : ℕ}
    (h : (cd.bin B ν (2 ^ k)).Nonempty) :
    (((2 ^ k : ℕ) : NNReal) : ENNReal) ≤
      (fibreMassConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) := by
  have h1 := cd.pow_le_card_fib_of_bin_nonempty h
  have h2 : (((2 ^ k : ℕ) : NNReal) : ENNReal) ≤ ((cd.fib B ν).card : ENNReal) := by
    exact_mod_cast h1
  exact h2.trans (cd.card_fib_le_fibreMass hB ν)

/-! ### The non-ED degree of the level's segments -/

open scoped Classical in
/-- The non-ED degree among the net capsules of a ball, as a real: `≤ 2 (40 C₃ + 1)⁶`. -/
theorem edDegree_net_le {B : bι} (hB : B ∈ cd.bs) (ν : cfg.ι) :
    (edDegree (cd.net B).net (fun μ => cd.caps B μ) ν : ℝ) ≤
      2 * (40 * Kakeya.Tube.tubeOverlapCoreClose.C 3 + 1) ^ 6 := by
  have hδpos : (0 : ℝ) < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
  have hρL : ((capρ cfg : NNReal) : ℝ) ≤ 2 * capL cfg := by
    have := cd.capρ_le_capL; have := capL_nonneg cfg; linarith
  have h := (cd.net B).edDegree_capsuleAt_le hδpos (capL_pos cfg) (capL_le_half cfg)
    (ρ := capρ cfg) (capρ_pos cfg) hρL (fun i hi => cd.norm_foot_sub_le_capL hB hi) ν
  have hcard : Fintype.card (Fin 3) = 3 := by simp
  rw [hcard, coe_capρ] at h
  refine h.trans (le_of_eq ?_)
  have e : 2 * (5 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * (2 * (cfg.δ : ℝ)))) /
      ((cfg.δ : ℝ) / 2) = 40 * Kakeya.Tube.tubeOverlapCoreClose.C 3 := by
    field_simp
    ring
  rw [e]

theorem edMultiplicityConstant_eq : edMultiplicityConstant = 2 * 4201 ^ 6 := rfl

/-- `2 (40 C₃ + 1)⁶ ≤ edMultiplicityConstant`, from `C₃ ≤ 105`. -/
theorem two_mul_pow_le_edMultiplicityConstant :
    2 * (40 * Kakeya.Tube.tubeOverlapCoreClose.C 3 + 1) ^ 6 ≤
      ((edMultiplicityConstant : ℕ) : ℝ) := by
  have h := tubeOverlapCoreClose_C_three_le
  have h0 : (0 : ℝ) ≤ 40 * Kakeya.Tube.tubeOverlapCoreClose.C 3 + 1 := by
    have := Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3; linarith
  have h1 : 40 * Kakeya.Tube.tubeOverlapCoreClose.C 3 + 1 ≤ 4201 := by linarith
  have h2 : (40 * Kakeya.Tube.tubeOverlapCoreClose.C 3 + 1) ^ 6 ≤ (4201 : ℝ) ^ 6 :=
    pow_le_pow_left₀ h0 h1 6
  calc 2 * (40 * Kakeya.Tube.tubeOverlapCoreClose.C 3 + 1) ^ 6 ≤ 2 * (4201 : ℝ) ^ 6 := by
        linarith
    _ = ((edMultiplicityConstant : ℕ) : ℝ) := by rw [edMultiplicityConstant_eq]; push_cast; ring

open scoped Classical in
/-- The non-ED degree among the level's segments of a ball is at most that among the net
capsules (the segments are a sub-family, re-indexed by `ν ↦ (ν, B)`). -/
theorem edDegree_segs_le_net {m : ℕ} {B : bι} {ν : cfg.ι} :
    edDegree (cd.segs m B) (fun q => (cd.Y m q).carrier) (ν, B) ≤
      edDegree (cd.net B).net (fun μ => cd.caps B μ) ν := by
  unfold edDegree
  refine Set.ncard_le_ncard_of_injOn Prod.fst ?_ ?_ (edDegree_set_finite _ _ _)
  · rintro q ⟨hq, hne, hED⟩
    obtain ⟨μ, hμ, -, rfl⟩ := cd.mem_segs.1 (Finset.mem_coe.1 hq)
    refine ⟨Finset.mem_coe.2 hμ, ?_, ?_⟩
    · intro h; exact hne (Prod.ext h rfl)
    · simpa [Y_carrier] using hED
  · rintro q ⟨hq, -, -⟩ q' ⟨hq', -, -⟩ hqq
    obtain ⟨μ, -, -, rfl⟩ := cd.mem_segs.1 (Finset.mem_coe.1 hq)
    obtain ⟨μ', -, -, rfl⟩ := cd.mem_segs.1 (Finset.mem_coe.1 hq')
    simp only at hqq
    rw [hqq]

open scoped Classical in
/-- **The non-ED degree bound of the level's segments** — the `hEDdeg` of the boundary theorem,
at the licensed `edMultiplicityConstant = 2 · 4201⁶`. -/
theorem edDegree_segs_le {m : ℕ} {B : bι} (hB : B ∈ cd.bs) {p : cfg.ι × bι}
    (hp : p ∈ cd.segs m B) :
    edDegree (cd.segs m B) (fun q => (cd.Y m q).carrier) p ≤ edMultiplicityConstant := by
  obtain ⟨ν, -, -, rfl⟩ := cd.mem_segs.1 hp
  have h1 := cd.edDegree_segs_le_net (m := m) (B := B) (ν := ν)
  have h2 := cd.edDegree_net_le hB ν
  have h3 := two_mul_pow_le_edMultiplicityConstant
  have : (edDegree (cd.net B).net (fun μ => cd.caps B μ) ν : ℝ) ≤
      ((edMultiplicityConstant : ℕ) : ℝ) := h2.trans h3
  exact h1.trans (by exact_mod_cast this)

/-! ### The dilation clause, localisation and the card bound -/

open scoped Classical in
/-- **The dilation clause of the level's segments** at the ceiling `capsuleDilationConstant`. -/
theorem segs_dilation (m : ℕ) {B : bι} (hB : B ∈ cd.bs) :
    (cfg.r₁ : ENNReal) ^ 2 * maxDensity (cd.segs m B) (fun p => (cd.Y m p).toConvexSpaceBody) ≤
      (capsuleDilationConstant : ENNReal) *
        maxDensity cfg.s (fun i => (cfg.T i).toConvexSpaceBody) := by
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  have hr := r₁_pos cfg
  have hL := capL_pos cfg
  -- reindex: the segments are the image of the nonempty-bin net points
  have himg : maxDensity (cd.segs m B) (fun p => (cd.Y m p).toConvexSpaceBody) =
      maxDensity ((cd.net B).net.filter fun ν => (cd.bin B ν m).Nonempty)
        (fun ν => capsuleAtBody (cfg.T ν).toTube (cd.ctr B) (capρ cfg) (capL_nonneg cfg)) := by
    unfold segs
    exact maxDensity_image _ _ (fun i _ j _ h => (Prod.mk.inj h).1) _
  have hmono : maxDensity ((cd.net B).net.filter fun ν => (cd.bin B ν m).Nonempty)
        (fun ν => capsuleAtBody (cfg.T ν).toTube (cd.ctr B) (capρ cfg) (capL_nonneg cfg)) ≤
      maxDensity (cd.net B).net
        (fun ν => capsuleAtBody (cfg.T ν).toTube (cd.ctr B) (capρ cfg) (capL_nonneg cfg)) :=
    maxDensity_mono _ (Finset.filter_subset _ _)
  -- the twin at `μ = (1+L)/L`
  have hμ1 : (1 : ℝ) ≤ (1 + capL cfg) / capL cfg := by
    rw [le_div_iff₀ hL]; linarith
  have hμL : 1 + capL cfg ≤ (1 + capL cfg) / capL cfg * capL cfg := by
    rw [div_mul_cancel₀ _ hL.ne']
  have hμρ : fibreRadius cfg.δ (cfg.δ : ℝ) (capL cfg) ≤
      (1 + capL cfg) / capL cfg * ((capρ cfg : NNReal) : ℝ) := by
    rw [fibreRadius_capL, coe_capρ]
    have hr1 := r₁_le_one cfg
    have e : (1 + capL cfg) / capL cfg * (2 * (cfg.δ : ℝ)) =
        (cfg.δ : ℝ) * (2 + 8 / (cfg.r₁ : ℝ)) := by
      unfold capL; field_simp; ring
    rw [e]
    have : (1 : ℝ) ≤ 4 / (cfg.r₁ : ℝ) := by rw [le_div_iff₀ hr]; linarith
    have h4 : (4 : ℝ) / (cfg.r₁ : ℝ) ≤ 8 / (cfg.r₁ : ℝ) - 1 := by
      have : (8 : ℝ) / (cfg.r₁ : ℝ) = 4 / (cfg.r₁ : ℝ) + 4 / (cfg.r₁ : ℝ) := by ring
      linarith
    nlinarith
  have hL4 : capL cfg ≤ 1 / 4 := by unfold capL; have := r₁_le_one cfg; linarith
  have hδL : 4 * (cfg.δ : ℝ) ≤ capL cfg := by unfold capL; have := cd.δr; linarith
  have hC := le_capsuleDilationConstant_mul (δ := cfg.δ) hL hL4 hδL
  have hcapρ : capρ cfg = 2 * cfg.δ := rfl
  have htwin := (cd.net B).ofReal_sq_mul_maxDensity_capsuleAt_le (cd.idx_subset B) hL
    (capL_le_half cfg) (r := (cfg.r₁ : ℝ) / 16) cd.r16_add_δ_le_capL
    (fun i hi => cd.meets_of_mem_idx hB hi) (ρ := capρ cfg) (μ := (1 + capL cfg) / capL cfg)
    hμ1 hμL hμρ (Cdil := (capsuleDilationConstant : ENNReal)) (by rw [hcapρ]; exact hC)
  have hr₁ : ENNReal.ofReal (4 * capL cfg) = (cfg.r₁ : ENNReal) := by
    unfold capL
    rw [show 4 * ((cfg.r₁ : ℝ) / 4) = (cfg.r₁ : ℝ) by ring, ENNReal.ofReal_coe_nnreal]
  rw [hr₁] at htwin
  rw [himg]
  exact le_trans (mul_le_mul' le_rfl hmono) htwin

open scoped Classical in
/-- The level's segments are localised at `11 r₁/16`. -/
theorem segs_localised (m : ℕ) {B : bι} (hB : B ∈ cd.bs) {p : cfg.ι × bι} (hp : p ∈ cd.segs m B) :
    (cd.Y m p).carrier ⊆ closedBall (cd.ctr B) (11 * (cfg.r₁ : ℝ) / 16) := by
  obtain ⟨ν, hν, -, rfl⟩ := cd.mem_segs.1 hp
  have hr0 : (0 : ℝ) ≤ (cfg.r₁ : ℝ) := (cfg.r₁).coe_nonneg
  exact cd.caps_subset_closedBall hB (cd.net_subset_idx B hν) (by linarith)


/-! ### The per-ball working mass of the level core -/

open scoped Classical in
theorem sum_segs_eq (m : ℕ) (B : bι) (f : cfg.ι × bι → ENNReal) :
    ∑ p ∈ cd.segs m B, f p =
      ∑ ν ∈ (cd.net B).net with (cd.bin B ν m).Nonempty, f (ν, B) := by
  unfold segs
  rw [Finset.sum_image (fun i _ j _ h => (Prod.mk.inj h).1)]

open scoped Classical in
/-- The per-ball working mass of the level-`m` core is `m` times its segments' shade mass
(exactly `m` fibre members shade every point of a segment's shade). -/
theorem ballYgMass_capsuleCore (m : ℕ) (hm : 0 < m) (hne : (cd.bs' m).Nonempty)
    {C₀ : NNReal} (hC₀ : 16 ≤ C₀) {D : ℕ} (hD : ballCoverConstant ≤ D)
    (Cg : NNReal) (hCg : 1 ≤ Cg)
    (hYg : (Cg : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (cfg.T i).shade ≤
      ∑ i ∈ cfg.s, volume (cd.Yg m i))
    {B : bι} (hB : B ∈ cd.bs) :
    ballYgMass (cd.capsuleCore m hm hne hC₀ hD Cg hCg hYg) B =
      ((m : ℕ) : ENNReal) * ∑ p ∈ cd.segs m B, volume (cd.Y m p).shade := by
  letI := indexOrder cfg
  change ∑ i ∈ cfg.s, volume (cd.Yg m i ∩ cd.P B) = _
  have h1 : ∀ i ∈ cfg.s, volume (cd.Yg m i ∩ cd.P B) =
      volume (cd.trunc B ((cd.net B).assign i) m i) := fun i _ => by rw [cd.Yg_inter_P hB m i]
  rw [Finset.sum_congr rfl h1, cd.sum_s_eq_sum_net_fib B _ (fun i _ hi => by
      rw [cd.trunc_eq_empty_of_not_mem m (fun h => hi (cd.fib_subset_idx B _ h)), measure_empty])]
  have h2 : ∀ ν ∈ (cd.net B).net,
      ∑ i ∈ cd.fib B ν, volume (cd.trunc B ((cd.net B).assign i) m i) =
        ((m : ℕ) : ENNReal) * volume (cd.bin B ν m) := by
    intro ν _
    rw [Finset.sum_congr rfl (fun i hi => by rw [(cd.mem_fib_iff.1 hi).2])]
    exact sum_volume_truncated (cd.fib B ν) (cd.S B) (fun j _ => cd.measurableSet_S B j)
      (cd.Pmeas B) m
  rw [Finset.sum_congr rfl h2, cd.sum_segs_eq m B, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs with h
  · rw [cd.Y_shade_eq_bin hm hB]
  · rw [Set.not_nonempty_iff_eq_empty.1 h, measure_empty]

end CoverData

/-! ### The heavy balls, at a scaled per-ball mass -/

open scoped Classical in
/-- `Kakeya.VeryNotSticky.exists_heavyBalls_core` with the per-ball working mass `μ` times the
segments' shade mass (for the capsule core at level `m`, `μ = m`). -/
theorem exists_heavyBalls_core_scaled {cfg : VeryNotSticky.{u}} (core : BallDataCore cfg)
    {c₁ : NNReal} (μ : ENNReal)
    (hSm : ∀ B ∈ core.bs, ballYgMass core B = μ * ∑ p ∈ core.segs B, volume (core.Y p).shade)
    (hCtop : ∑ B ∈ core.bs, ∑ p ∈ core.segs B, volume (core.Y p).carrier ≠ ⊤)
    (hS0 : ∑ B ∈ core.bs, ∑ p ∈ core.segs B, volume (core.Y p).shade ≠ 0)
    (hfull : 4 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
        ∑ B ∈ core.bs, ∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
      ∑ B ∈ core.bs, ∑ p ∈ core.segs B, volume (core.Y p).shade) :
    ∃ bs' : Finset core.bι, bs' ⊆ core.bs ∧ bs'.Nonempty ∧
      (((2 : NNReal) : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (core.Yg i) ≤
        ∑ i ∈ cfg.s, volume (restrictYg core bs' i)) ∧
      (∀ B ∈ bs', 2 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
          ∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
        ∑ p ∈ core.segs B, volume (core.Y p).shade) := by
  classical
  set Cm : core.bι → ENNReal := fun B => ∑ p ∈ core.segs B, volume (core.Y p).carrier with hCm
  set Sm : core.bι → ENNReal := fun B => ∑ p ∈ core.segs B, volume (core.Y p).shade with hSmd
  set θ : ENNReal := (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) with hθd
  have hθ : θ ≠ ⊤ := by
    rw [hθd, ← ENNReal.coe_rpow_of_ne_zero (ne_of_gt cfg.hδ), ← ENNReal.coe_mul]
    exact ENNReal.coe_ne_top
  have hheavy := exists_heavyBalls_at core.bs Cm Sm hθ hCtop hfull
  set bs' : Finset core.bι := core.bs.filter (fun B => 2 * θ * Cm B ≤ Sm B) with hbs'
  have hsub : bs' ⊆ core.bs := Finset.filter_subset _ _
  have hne : bs'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty bs' with hemp | h
    · rw [hemp, Finset.sum_empty, le_zero_iff, mul_eq_zero] at hheavy
      rcases hheavy with h2 | hS
      · exact absurd h2 (by simp)
      · exact absurd hS hS0
    · exact h
  have hretY : ((2 : NNReal) : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (core.Yg i) ≤
      ∑ i ∈ cfg.s, volume (restrictYg core bs' i) := by
    refine restrictYg_mass_of_retention core bs' hsub (K := 2) ?_
    have h1 : ∑ B ∈ core.bs, ballYgMass core B = μ * ∑ B ∈ core.bs, Sm B := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun B hB => hSm B hB
    have h2 : ∑ B ∈ bs', ballYgMass core B = μ * ∑ B ∈ bs', Sm B := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun B hB => hSm B (hsub hB)
    rw [h1, h2]
    calc ((2 : NNReal) : ENNReal)⁻¹ * (μ * ∑ B ∈ core.bs, Sm B)
        = μ * (((2 : NNReal) : ENNReal)⁻¹ * ∑ B ∈ core.bs, Sm B) := by ring
      _ ≤ μ * ∑ B ∈ bs', Sm B := by
          gcongr
          simpa using hheavy
  refine ⟨bs', hsub, hne, hretY, fun B hB => ?_⟩
  exact (Finset.mem_filter.1 hB).2

/-! ### The floors, numerically -/

/-- `81 ≤ edDilateConstant` (`C₃ = 9 + 128/c₃`, `c₃ = 4π/9 ≤ 16/9`). -/
theorem eightyone_le_edDilateConstant : (81 : NNReal) ≤ edDilateConstant := by
  unfold edDilateConstant
  rw [Real.le_toNNReal_iff_coe_le edComparabilityConstant_pos.le]
  rw [edComparabilityConstant_eq, le_volume_c_three_eq]
  have hpi := Real.pi_le_four
  have hpi0 := Real.pi_pos
  have : (72 : ℝ) ≤ 2 * 4 ^ 3 / (4 * Real.pi / 9) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  push_cast
  linarith

theorem sixteen_le_edSegmentsConstant : (16 : NNReal) ≤ edSegmentsConstant := by
  unfold edSegmentsConstant
  have := eightyone_le_edDilateConstant
  calc (16 : NNReal) ≤ 4 * 81 := by norm_num
    _ ≤ 4 * edDilateConstant := by gcongr

theorem thirtytwo_le_edRadiusConstant : (32 : NNReal) ≤ edRadiusConstant := by
  unfold edRadiusConstant
  have := eightyone_le_edDilateConstant
  calc (32 : NNReal) ≤ 8 * 81 := by norm_num
    _ ≤ 8 * edDilateConstant := by gcongr

theorem twelve288_le_edDensityConstant : (12288 : NNReal) ≤ edDensityConstant := by
  unfold edDensityConstant
  have := eightyone_le_edDilateConstant
  calc (12288 : NNReal) ≤ 4 * 81 ^ 2 := by norm_num
    _ ≤ 4 * edDilateConstant ^ 2 := by gcongr

/-! ### The polylog absorber for the level count -/

/-- `4 · (⌊log₂ n⌋ + 1) ≤ δ^{-ε}` eventually, for `n ≤ δ^{-4}`. -/
theorem eventually_numLevels_le_rpow_neg {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ∀ n : ℕ, ((n : ℝ) ≤ ((d : ℝ))⁻¹ ^ (4 : ℝ)) →
      ((4 * ((Nat.log 2 n + 1 : ℕ) : NNReal) : NNReal) : ENNReal) ≤
        (d : ENNReal) ^ (-ε) := by
  filter_upwards [eventually_ofReal_polylog_pow_le_rpow_neg (A := 4) (B := 16) (by norm_num)
      (by norm_num) 1 hε, self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with d hd hd0 hd1
  intro n hn
  have hd0' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hd1' : (d : ℝ) ≤ 1 := by exact_mod_cast hd1.2.le
  have hinv1 : (1 : ℝ) ≤ ((d : ℝ))⁻¹ := (one_le_inv₀ hd0').2 hd1'
  have hlog0 : 0 ≤ Real.logb 2 ((d : ℝ))⁻¹ := Real.logb_nonneg one_lt_two hinv1
  have hlogn : (Nat.log 2 n : ℝ) ≤ 4 * Real.logb 2 ((d : ℝ))⁻¹ := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp only [Nat.log_zero_right, Nat.cast_zero]; positivity
    · have h1 : (2 : ℝ) ^ (Nat.log 2 n) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 hn0.ne'
      have h2 : (Nat.log 2 n : ℝ) = Real.logb 2 ((2 : ℝ) ^ Nat.log 2 n) := by
        rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
      rw [h2]
      calc Real.logb 2 ((2 : ℝ) ^ Nat.log 2 n) ≤ Real.logb 2 (n : ℝ) :=
            (Real.logb_le_logb one_lt_two (by positivity) (by exact_mod_cast hn0)).2 h1
        _ ≤ Real.logb 2 (((d : ℝ))⁻¹ ^ (4 : ℝ)) :=
            (Real.logb_le_logb one_lt_two (by exact_mod_cast hn0) (by positivity)).2 hn
        _ = 4 * Real.logb 2 ((d : ℝ))⁻¹ := Real.logb_rpow_eq_mul_logb_of_pos (by positivity)
  have hreal : ((4 * ((Nat.log 2 n + 1 : ℕ) : NNReal) : NNReal) : ℝ) ≤
      (4 + 16 * Real.logb 2 ((d : ℝ))⁻¹) ^ 1 := by
    push_cast; linarith
  calc ((4 * ((Nat.log 2 n + 1 : ℕ) : NNReal) : NNReal) : ENNReal)
      = ENNReal.ofReal (((4 * ((Nat.log 2 n + 1 : ℕ) : NNReal) : NNReal) : ℝ)) :=
        (ENNReal.ofReal_coe_nnreal).symm
    _ ≤ ENNReal.ofReal ((4 + 16 * Real.logb 2 ((d : ℝ))⁻¹) ^ 1) :=
        ENNReal.ofReal_le_ofReal hreal
    _ ≤ (d : ENNReal) ^ (-ε) := hd

/-! ### The spec theorem: the canonical-capsule core of a cover -/

open scoped Classical in
/-- **The canonical-capsule core of a given cover** — the analogue of
`Kakeya.VeryNotSticky.exists_core_localised_of_cover` for the refined `propvnslocalization`
(l.3700–3724, l.5354–5473): the level `m = 2^k` of the two-constraint pigeonhole, `Cm = 1`, the
fibre budget `Cm · m ≤ fibreMassConstant · δ^{-(η+2 exscal)}` (SP-H), `Cg = 4·numLevels·2·
tierRetention`, the density retention at `c₁` (under T3's floor at `3072 c₁`), the dilation clause
at the ceiling `capsuleDilationConstant`, one shade-fraction class per ball, localisation at
`11 r₁/16`, the card bound, and — what T3's core cannot give — **the non-ED degree of the
segments of every ball at most `edMultiplicityConstant`**, in the body of the boundary's
`hEDdeg`. -/
theorem exists_core_capsule_of_cover (cfg : VeryNotSticky.{u}) {bι : Type u}
    {C₀ : NNReal} (hC₀ : 16 ≤ C₀) {D : ℕ} (hD : ballCoverConstant ≤ D)
    (hδr : 32 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (bs : Finset bι) (ctr : bι → E3) (P : bι → Set E3)
    (hbsne : bs.Nonempty)
    (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
    (hPball : ∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ))
    (hPdisj : (bs : Set bι).PairwiseDisjoint P)
    (hPmeas : ∀ B, MeasurableSet (P B))
    (hPcov : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B)
    (hoverlap : ∀ (x : E3) (t : Finset bι), t ⊆ bs →
      (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant)
    (hPne : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty)
    {c₁ : NNReal} (hc₁ : 0 < c₁)
    (hc₁' : 4 * (3072 * c₁) * (ballCoverConstant : NNReal) ≤ 1) :
    ∃ core : BallDataCore cfg,
      core.C₀ = C₀ ∧ core.D = D ∧ core.Cm = 1 ∧
      (core.Cm : ENNReal) * (core.m : ENNReal) ≤
        (fibreMassConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) ∧
      core.Cg = 4 * (numLevels cfg : NNReal) * 2 * tierRetention cfg c₁ ∧
      (∀ B ∈ core.bs, ∀ p ∈ core.segs B,
        (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
          volume (core.Y p).shade) ∧
      (∀ B ∈ core.bs, (cfg.r₁ : ENNReal) ^ 2 *
          maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) ≤
        (capsuleDilationConstant : ENNReal) *
          maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)) ∧
      (∀ B ∈ core.bs, ∀ p ∈ core.segs B, ∀ q ∈ core.segs B,
        shadeFractionClass core p = shadeFractionClass core q) ∧
      core.Localised (11 * (cfg.r₁ : ℝ) / 16) ∧
      (∀ B ∈ core.bs, (core.segs B).card ≤ cfg.s.card) ∧
      (∀ B ∈ core.bs, ∀ p ∈ core.segs B,
        {q ∈ (core.segs B : Set core.σ) | q ≠ p ∧
          ¬ _root_.IsEssentiallyDistinct (core.Y p).carrier (core.Y q).carrier}.ncard ≤
            edMultiplicityConstant) := by
  classical
  set cd : CoverData cfg bι :=
    ⟨bs, ctr, P, hbsne, hPball16, hPball, hPdisj, hPmeas, hPcov, hoverlap, hPne, hδr⟩ with hcd
  obtain ⟨k, -, hne, hYg, hfull, hS0⟩ := cd.exists_good_level hc₁'
  have hm : 0 < 2 ^ k := pow_pos two_pos k
  have h4K : (1 : NNReal) ≤ 4 * (numLevels cfg : NNReal) := by
    have := numLevels_pos cfg
    calc (1 : NNReal) ≤ 4 * 1 := by norm_num
      _ ≤ 4 * (numLevels cfg : NNReal) := by gcongr; exact_mod_cast this
  set core₀ := cd.capsuleCore (2 ^ k) hm hne hC₀ hD (4 * (numLevels cfg : NNReal)) h4K hYg
    with hcore₀
  have hbs₀ : core₀.bs = cd.bs' (2 ^ k) := rfl
  have hsegs₀ : core₀.segs = cd.segs (2 ^ k) := rfl
  have hY₀ : core₀.Y = cd.Y (2 ^ k) := rfl
  -- a ball with a nonempty bin (for SP-H)
  obtain ⟨B₀, hB₀⟩ := hne
  obtain ⟨hB₀bs, ⟨p₀, hp₀⟩⟩ := cd.mem_bs'.1 hB₀
  obtain ⟨ν₀, -, hbin₀, -⟩ := cd.mem_segs.1 hp₀
  have hSPH₀ : (((2 ^ k : ℕ) : NNReal) : ENNReal) ≤
      (fibreMassConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) :=
    cd.pow_le_fibreMass hB₀bs hbin₀
  -- the heavy balls
  have hSm : ∀ B ∈ core₀.bs, ballYgMass core₀ B =
      ((2 ^ k : ℕ) : ENNReal) * ∑ p ∈ core₀.segs B, volume (core₀.Y p).shade :=
    fun B hB => cd.ballYgMass_capsuleCore (2 ^ k) hm _ hC₀ hD _ h4K hYg (cd.bs'_subset _ hB)
  have hCtop : ∑ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).carrier ≠ ⊤ := by
    refine (ENNReal.sum_lt_top.2 fun B _ => ENNReal.sum_lt_top.2 fun p _ => ?_).ne
    exact (cd.Y (2 ^ k) p).toConvexSpaceBody.isCompact'.measure_lt_top
  obtain ⟨bs', hsub, hne', hret, hheavy⟩ :=
    exists_heavyBalls_core_scaled core₀ (c₁ := c₁) ((2 ^ k : ℕ) : ENNReal) hSm hCtop hS0 hfull
  set core₁ := core₀.restrictBalls bs' hsub hne' (K := 2) (by norm_num) hret with hcore₁
  have hfull₁ : ∀ B ∈ core₁.bs, 2 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
      ∑ p ∈ core₁.segs B, volume (core₁.Y p).carrier ≤
      ∑ p ∈ core₁.segs B, volume (core₁.Y p).shade := hheavy
  obtain ⟨k', hkne, hkret⟩ := exists_markovDyadicTier_data core₁ hc₁ hfull₁
  refine ⟨markovDyadicTierCore core₁ c₁ k' hkne hkret, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · -- SP-H: `Cm · m = 1 · 2^k`
    change ((1 : NNReal) : ENNReal) * (((2 ^ k : ℕ) : NNReal) : ENNReal) ≤ _
    rw [ENNReal.coe_one, one_mul]
    exact hSPH₀
  · change (4 * (numLevels cfg : NNReal)) * 2 * (1 : NNReal) ^ 2 * tierRetention cfg c₁ = _
    ring
  · exact markovDyadicTierCore_segs_density core₁ c₁ k' hkne hkret
  · exact tierCore_segs_dilation core₁ _ _ _ _ _
      (restrictBalls_segs_dilation core₀ bs' hsub hne' (by norm_num) hret
        (fun B hB => cd.segs_dilation (2 ^ k) (cd.bs'_subset _ hB)))
  · intro B hB p hp q hq
    exact markovDyadicTier_shadeFractionClass_eq core₁ c₁ k' hp hq
  · refine BallDataCore.Localised.tierCore ?_ _ _ _ _ _
    refine BallDataCore.Localised.restrictBalls ?_ _ _ _ _ _
    exact fun B hB p hp => cd.segs_localised (2 ^ k) (cd.bs'_subset _ hB) hp
  · intro B hB
    exact (Finset.card_le_card (markovDyadicTier_subset core₁ c₁ k' B)).trans
      (cd.card_segs_le (2 ^ k) B)
  · intro B hB p hp
    have hsubB : markovDyadicTier core₁ c₁ k' B ⊆ cd.segs (2 ^ k) B :=
      markovDyadicTier_subset core₁ c₁ k' B
    have hB' : B ∈ cd.bs := cd.bs'_subset _ (hsub hB)
    change edDegree (markovDyadicTier core₁ c₁ k' B) (fun q => (cd.Y (2 ^ k) q).carrier) p ≤ _
    exact (edDegree_mono hsubB _ p).trans (cd.edDegree_segs_le hB' (hsubB hp))


/-- The `K⁻¹`-form of a retention bound (a local copy of the producer file's private helper). -/
theorem inv_mul_le_of_le_mul_coe' {K : NNReal} (hK : 1 ≤ K) {x y : ENNReal}
    (h : x ≤ (K : ENNReal) * y) : ((K : NNReal) : ENNReal)⁻¹ * x ≤ y := by
  have hK0 : ((K : NNReal) : ENNReal) ≠ 0 := by
    simp only [ne_eq, ENNReal.coe_eq_zero]
    exact (lt_of_lt_of_le zero_lt_one hK).ne'
  have hKt : ((K : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc ((K : NNReal) : ENNReal)⁻¹ * x
      ≤ ((K : NNReal) : ENNReal)⁻¹ * (((K : NNReal) : ENNReal) * y) := by gcongr
    _ = (((K : NNReal) : ENNReal)⁻¹ * ((K : NNReal) : ENNReal)) * y := by ring
    _ = y := by rw [ENNReal.inv_mul_cancel hK0 hKt, one_mul]

/-! ### The general-branch producer at one configuration, on the capsule core -/

open scoped Classical in
/-- **`exists_ballData_general_of_cover` on the canonical-capsule core**: the same body-factoring
chain (`exists_ballFactoring_glued_localised`, `tierCore`, `exists_dimsClass_core`,
`restrictBalls`, `withDims`, `toBallData`) on `exists_core_capsule_of_cover`; `bd.Cdil` is the
ceiling `capsuleDilationConstant`, `bd.m` the level `2^k` inside SP-H, `bd.Cg` absorbs five
`δ`-free-or-polylog factors at `εg/5` each (the fifth, `4 · numLevels`, is the level count), and
the non-ED degree of the segments is carried along `tier' ⊆ core₁.segs`. -/
theorem exists_ballData_capsule_of_cover (cfg : VeryNotSticky.{u}) {bι : Type u}
    {C₀bd : NNReal} (hC₀ : 16 ≤ C₀bd) {D : ℕ} (hD : ballCoverConstant ≤ D)
    (hδr : 32 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) (hϱ21 : cfg.ϱ ≤ 1 / 21)
    (hr₁1 : 2 * cfg.r₁ ≤ 1)
    (bs : Finset bι) (ctr : bι → EuclideanSpace ℝ (Fin 3))
    (P : bι → Set (EuclideanSpace ℝ (Fin 3)))
    (hbsne : bs.Nonempty)
    (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
    (hPball : ∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ))
    (hPdisj : (bs : Set bι).PairwiseDisjoint P)
    (hPmeas : ∀ B, MeasurableSet (P B))
    (hPcov : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B)
    (hoverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
      (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant)
    (hPne : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty)
    {c₁ : NNReal} (hc₁ : 0 < c₁)
    (hc₁' : 4 * (3072 * c₁) * (ballCoverConstant : NNReal) ≤ 1)
    {εg : ℝ}
    (hA4 : (4 : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(εg / 5)))
    (hAT : ((tierRetention cfg c₁ : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(εg / 5)))
    (hAD : ((dimsClassLoss (3 / 2) cfg.δ : ℕ) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(εg / 5)))
    (hAL : ((uniformLossBound 3 cfg.s.card (cfg.δ / cfg.r₁) cfg.ϱ : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(εg / 5)))
    (hAK : ((4 * (numLevels cfg : NNReal) : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(εg / 5))) :
    ∃ (a b : NNReal) (hdims : cfg.δ ≤ a ∧ a ≤ b ∧ b ≤ cfg.δ ^ cfg.exscal)
      (bd : BallData (withDims cfg a b hdims)),
      bd.C₀ = C₀bd ∧ bd.Cbias = lemma92Bias C₀bd cfg.ϱ ∧ bd.CF = lemma92Constant cfg.ϱ ∧
      bd.Cdil = capsuleDilationConstant ∧
      bd.c₁ = c₁ ∧ bd.D = D ∧ bd.Cg ≤ cfg.δ ^ (-εg) ∧ bd.Cm = 1 ∧
      (bd.Cm : ENNReal) * (bd.m : ENNReal) ≤
        (fibreMassConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) ∧
      cfg.δ ≤ bd.w₁ ∧ bd.w₁ ≤ 1 ∧
      (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
        (bd.Wb j).carrier ⊆ closedBall (bd.ctr B) (11 * (cfg.r₁ : ℝ) / 16)) ∧
      (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
        HasThicknesses (bd.Wb j).carrier C₀bd ![(cfg.r₁ : ℝ), (b : ℝ), (a : ℝ)]) ∧
      (∀ B ∈ bd.bs, ∀ p ∈ bd.segs B,
        {q ∈ (bd.segs B : Set bd.σ) | q ≠ p ∧
          ¬ _root_.IsEssentiallyDistinct (bd.Y p).carrier (bd.Y q).carrier}.ncard ≤
            edMultiplicityConstant) := by
  classical
  have hC₀4 : 4 ≤ C₀bd := le_trans (by norm_num) hC₀
  obtain ⟨core₁, hC₀eq, hDeq, hCmeq, hSPH, hCgeq, hdens, hdil, hclass, hloc, hcard, hdeg⟩ :=
    exists_core_capsule_of_cover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj
      hPmeas hPcov hoverlap hPne hc₁ hc₁'
  have hRr : 11 * (cfg.r₁ : ℝ) / 16 ≤ (cfg.r₁ : ℝ) := by
    have : (0 : ℝ) ≤ (cfg.r₁ : ℝ) := (cfg.r₁).coe_nonneg
    linarith
  obtain ⟨tier, bodies, Wb, blk, htier, hLret, hblkmem, hsegsle, hballR, hfro, hbias,
    hanti, hsim, hinhab⟩ :=
    exists_ballFactoring_glued_localised core₁ hc₁ hdens hRr hloc
  set tier' : core₁.bι → Finset core₁.σ := fun B => tier B ∩ core₁.segs B with htier'def
  have htier'sub : ∀ B, tier' B ⊆ core₁.segs B := fun B => Finset.inter_subset_right
  have htier'le : ∀ B, tier' B ⊆ tier B := fun B => Finset.inter_subset_left
  have htier'eq : ∀ B ∈ core₁.bs, tier' B = tier B := fun B hB =>
    Finset.inter_eq_left.2 (htier B hB)
  have hr₁pos : (0 : NNReal) < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  have hdpos : (0 : NNReal) < cfg.δ / cfg.r₁ := div_pos cfg.hδ hr₁pos
  set Kbase : NNReal := uniformLossBound 3 cfg.s.card (cfg.δ / cfg.r₁) cfg.ϱ with hKbase
  have hKbase1 : 1 ≤ Kbase := one_le_uniformLossBound _ _ _ _
  set K₂ : NNReal := 2 * Kbase with hK₂def
  have hK₂1 : 1 ≤ K₂ := by
    rw [hK₂def]
    calc (1 : NNReal) = 1 * 1 := by norm_num
      _ ≤ 2 * Kbase := by
          have h2 : (1 : NNReal) ≤ 2 := by norm_num
          exact mul_le_mul' h2 hKbase1
  have hLret' : ∀ B ∈ core₁.bs, ∑ p ∈ core₁.segs B, volume (core₁.Y p).carrier ≤
      (Kbase : ENNReal) * ∑ p ∈ tier' B, volume (core₁.Y p).carrier := by
    intro B hB
    obtain ⟨p₀, hp₀⟩ := core₁.segs_nonempty B hB
    have hLb : ConvexSpaceBody.nonempty_biasedFactorization.L 3 (core₁.segs B).card
        (cfg.δ / cfg.r₁) cfg.ϱ ≤ (Kbase : ENNReal) :=
      L_le_uniformLossBound hdpos (Finset.card_pos.2 ⟨p₀, hp₀⟩) (hcard B hB)
    calc ∑ p ∈ core₁.segs B, volume (core₁.Y p).carrier
        ≤ ConvexSpaceBody.nonempty_biasedFactorization.L 3 (core₁.segs B).card
            (cfg.δ / cfg.r₁) cfg.ϱ * ∑ p ∈ tier B, volume (core₁.Y p).carrier := hLret B hB
      _ ≤ (Kbase : ENNReal) * ∑ p ∈ tier' B, volume (core₁.Y p).carrier := by
          rw [htier'eq B hB]; gcongr
  have htierne : ∀ B ∈ core₁.bs, (tier' B).Nonempty := fun B hB =>
    tier_nonempty_of_carrier_retention core₁ hB (hLret' B hB)
  have hret₂ : ∀ B ∈ core₁.bs, ((K₂ : NNReal) : ENNReal)⁻¹ *
      ∑ p ∈ core₁.segs B, volume (core₁.Y p).shade ≤
      ∑ p ∈ tier' B, volume (core₁.Y p).shade := by
    intro B hB
    obtain ⟨p₀, hp₀⟩ := core₁.segs_nonempty B hB
    have hcl : ∀ p ∈ core₁.segs B,
        shadeFractionClass core₁ p = shadeFractionClass core₁ p₀ :=
      fun p hp => hclass B hB p hp p₀ hp₀
    have hmk : ∀ p ∈ core₁.segs B, ∃ N : ℕ,
        volume (core₁.Y p).carrier ≤ 2 ^ N * volume (core₁.Y p).shade := by
      intro p hp
      refine ⟨shadeFractionClassBound (markovConst cfg c₁), ?_⟩
      have hNc : (1 : ENNReal) ≤ 2 ^ (shadeFractionClassBound (markovConst cfg c₁)) *
          ((markovConst cfg c₁ : NNReal) : ENNReal) :=
        one_le_two_pow_shadeFractionClassBound_mul (markovConst_pos cfg hc₁)
      have hcoe : ((markovConst cfg c₁ : NNReal) : ENNReal) =
          (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) := coe_markovConst cfg c₁
      calc volume (core₁.Y p).carrier = 1 * volume (core₁.Y p).carrier := (one_mul _).symm
        _ ≤ (2 ^ (shadeFractionClassBound (markovConst cfg c₁)) *
              ((markovConst cfg c₁ : NNReal) : ENNReal)) * volume (core₁.Y p).carrier :=
            mul_le_mul_of_nonneg_right hNc zero_le
        _ = 2 ^ (shadeFractionClassBound (markovConst cfg c₁)) *
              (((markovConst cfg c₁ : NNReal) : ENNReal) * volume (core₁.Y p).carrier) := by
            rw [mul_assoc]
        _ ≤ 2 ^ (shadeFractionClassBound (markovConst cfg c₁)) *
              volume (core₁.Y p).shade := by
            refine mul_le_mul_of_nonneg_left ?_ zero_le
            rw [hcoe]
            exact le_of_eq_of_le (by ring) (hdens B hB p hp)
    have hsh := shade_retention_of_carrier_retention core₁ (htier'sub B) hcl hmk (hLret' B hB)
    refine inv_mul_le_of_le_mul_coe' hK₂1 ?_
    have hcast : ((K₂ : NNReal) : ENNReal) = 2 * (Kbase : ENNReal) := by
      rw [hK₂def]; push_cast; ring
    rw [hcast, mul_assoc]
    simpa [mul_assoc] using hsh
  set core₂ := tierCore core₁ tier' htier'sub htierne hK₂1 hret₂ with hcore₂
  have hbs₂ : core₂.bs = core₁.bs := rfl
  have hsegs₂ : core₂.segs = tier' := rfl
  have hbodiesne : ∀ B ∈ core₂.bs, (bodies B).Nonempty := by
    intro B hB
    obtain ⟨p, hp⟩ := htierne B hB
    exact ⟨blk p, hblkmem B hB p (htier'le B hp)⟩
  have hinhab₂ : ∀ B ∈ core₂.bs, ∀ j ∈ bodies B, ∃ p ∈ core₂.segs B, blk p = j := by
    intro B hB j hj
    obtain ⟨p, hp, hpj⟩ := hinhab B hB j hj
    exact ⟨p, by rw [hsegs₂, htier'eq B hB]; exact hp, hpj⟩
  have hsegsle₂ : ∀ B ∈ core₂.bs, ∀ p ∈ core₂.segs B,
      (core₂.Y p).toConvexSpaceBody ≤ Wb (blk p) :=
    fun B hB p hp => hsegsle B hB p (htier'le B hp)
  have hball₂ : ∀ B ∈ core₂.bs, ∀ j ∈ bodies B,
      (Wb j).carrier ⊆ closedBall (core₂.ctr B) (cfg.r₁ : ℝ) :=
    fun B hB j hj => (hballR B hB j hj).trans (closedBall_subset_closedBall hRr)
  have hsim₂ : ∀ B ∈ core₂.bs, ∀ j ∈ bodies B, ∀ j' ∈ bodies B,
      ethickness ℝ (Wb j).carrier ≤ lemma92Constant cfg.ϱ • ethickness ℝ (Wb j').carrier :=
    hsim
  obtain ⟨a, b, w₁, hdims, bs', hsub, hne', hprof, hw, hmass⟩ :=
    exists_dimsClass_core cfg core₂ (ρ := 3 / 2) one_lt_three_halves bodies Wb blk
      (ballYgMass core₂) hbodiesne hinhab₂ hsegsle₂ hball₂ hsim₂
  set K₃ : NNReal := ((dimsClassLoss (3 / 2) cfg.δ : ℕ) : NNReal) with hK₃def
  have hK₃1 : 1 ≤ K₃ := by
    rw [hK₃def]
    have : 1 ≤ dimsClassLoss (3 / 2 : NNReal) cfg.δ := by
      unfold dimsClassLoss
      exact Nat.one_le_pow _ _ (Nat.succ_pos _)
    exact_mod_cast this
  have hK₃cast : ((K₃ : NNReal) : ENNReal) = ((dimsClassLoss (3 / 2) cfg.δ : ℕ) : ENNReal) := by
    rw [hK₃def]; push_cast; ring
  have hret₃ : ((K₃ : NNReal) : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (core₂.Yg i) ≤
      ∑ i ∈ cfg.s, volume (restrictYg core₂ bs' i) := by
    refine restrictYg_mass_of_retention core₂ bs' hsub ?_
    rw [hK₃cast]
    exact hmass
  set core₃ := core₂.restrictBalls bs' hsub hne' hK₃1 hret₃ with hcore₃
  set core₄ := BallDataCore.withDims cfg a b hdims core₃ with hcore₄
  have hbs₄ : core₄.bs = bs' := rfl
  have hsegs₄ : core₄.segs = tier' := rfl
  have hsub₁ : bs' ⊆ core₁.bs := hsub
  have hC₀₄ : core₄.C₀ = C₀bd := hC₀eq
  have hbudget : (3 / 2 : NNReal) * lemma92Constant cfg.ϱ ≤ 4 :=
    three_halves_mul_lemma92Constant_le hϱ21
  obtain ⟨hδw₁, hw₁r, hw₁prof⟩ := hw hbudget
  have hdimsC : dimsConstant core₂.C₀ (3 / 2) (lemma92Constant cfg.ϱ) = C₀bd := by
    have h2 : core₂.C₀ = C₀bd := hC₀eq
    rw [h2]
    exact dimsConstant_eq_left_of_lemma92 hC₀4 hϱ21
  refine ⟨a, b, hdims,
    core₄.toBallData (lemma92Constant cfg.ϱ) (one_le_lemma92Constant cfg.hϱ.le)
      capsuleDilationConstant one_le_capsuleDilationConstant
      (lemma92Bias C₀bd cfg.ϱ)
      (one_le_lemma92Bias (le_trans (by norm_num) hC₀4) cfg.hϱ.le) c₁ hc₁
      (core₁.bι × Finset core₁.σ) bodies Wb blk w₁
      (fun B hB p hp => hblkmem B (hsub₁ hB) p (htier'le B hp))
      (fun B hB p hp => hsegsle B (hsub₁ hB) p (htier'le B hp))
      (fun B hB j hj => by
        rw [hC₀₄, ← hdimsC]; exact hprof B hB j hj)
      (fun B hB j hj => hball₂ B (hsub₁ hB) j hj)
      (fun B hB j hj => hw₁prof B hB j hj)
      (fun B hB j hj => by
        have hseq : core₄.segs B = tier B := by
          rw [hsegs₄]; exact htier'eq B (hsub₁ hB)
        rw [hseq]
        exact hfro B (hsub₁ hB) j hj)
      (fun B hB j hj => by
        have hseq : core₄.segs B = tier B := by
          rw [hsegs₄]; exact htier'eq B (hsub₁ hB)
        rw [hseq]
        have h := hbias B (hsub₁ hB) j hj
        rw [hC₀eq] at h
        exact h)
      (fun B hB => by
        have h := hanti B (hsub₁ hB)
        rw [hC₀eq] at h
        exact h)
      (fun B hB => by
        refine le_trans (mul_le_mul_of_nonneg_left ?_ zero_le) (hdil B (hsub₁ hB))
        exact maxDensity_mono (fun p ↦ (core₁.Y p).toConvexSpaceBody) (htier'sub B))
      (fun B hB p hp => hdens B (hsub₁ hB) p (htier'sub B hp)),
    hC₀eq, rfl, rfl, rfl, rfl, hDeq, ?_, hCmeq, hSPH, hδw₁, ?_, ?_, ?_, ?_⟩
  · change core₄.Cg ≤ cfg.δ ^ (-εg)
    have hCgval : core₄.Cg = core₁.Cg * core₁.Cm ^ 2 * K₂ * K₃ := rfl
    have hδ0 : ((cfg.δ : NNReal) : ENNReal) ≠ 0 := by
      simp only [ne_eq, ENNReal.coe_eq_zero]; exact cfg.hδ.ne'
    have hδt : ((cfg.δ : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hsplit : (cfg.δ : ENNReal) ^ (-(εg / 5)) * (cfg.δ : ENNReal) ^ (-(εg / 5)) *
        (cfg.δ : ENNReal) ^ (-(εg / 5)) * (cfg.δ : ENNReal) ^ (-(εg / 5)) *
        (cfg.δ : ENNReal) ^ (-(εg / 5)) =
        (cfg.δ : ENNReal) ^ (-εg) := by
      rw [← ENNReal.rpow_add _ _ hδ0 hδt, ← ENNReal.rpow_add _ _ hδ0 hδt,
        ← ENNReal.rpow_add _ _ hδ0 hδt, ← ENNReal.rpow_add _ _ hδ0 hδt]
      congr 1
      ring
    have hADc : ((K₃ : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(εg / 5)) := by
      rw [hK₃cast]; exact hAD
    rw [← ENNReal.coe_le_coe, ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne', hCgval, hCgeq, hCmeq,
      ← hsplit]
    have hLHS : ((4 * (numLevels cfg : NNReal) * 2 * tierRetention cfg c₁ * (1 : NNReal) ^ 2 *
        K₂ * K₃ : NNReal) : ENNReal)
        = ((4 * (numLevels cfg : NNReal) : NNReal) : ENNReal) * 4 *
          ((tierRetention cfg c₁ : NNReal) : ENNReal) * ((Kbase : NNReal) : ENNReal) *
          ((K₃ : NNReal) : ENNReal) := by
      rw [hK₂def]; push_cast; ring
    rw [hLHS]
    gcongr
  · exact le_trans hw₁r hr₁1
  · intro B hB j hj
    exact hballR B (hsub₁ hB) j hj
  · intro B hB j hj
    have h := hprof B hB j hj
    rw [hdimsC] at h
    exact h
  · intro B hB p hp
    change edDegree (tier' B) (fun q => (core₁.Y q).carrier) p ≤ _
    exact (edDegree_mono (htier'sub B) _ p).trans (hdeg B (hsub₁ hB) p (htier'sub B hp))


/-! ### The producer, eventually in `δ`, on the capsule core -/

/-- **`eventually_ballDataGeneral_except_margin` on the canonical-capsule core**: the contract's
conclusion (dilation at the ceiling, `Cm = 1`, SP-H at `fibreMassConstant`) with the margin under
its guard, **and** the non-ED degree clause of the boundary's `hEDdeg`, for the produced `bd`.
The floors are `16 ≤ C₀bd` (the capsule thickness profile), `4·(3072·c₁)·D ≤ 1` (T3's fullness
at `3072 c₁`, paying the level pigeonhole) and `32δ ≤ r₁` (the dilation twin's `4δ ≤ L`). -/
theorem eventually_ballDataCapsule_except_margin (β ζ exscal ϱ η τ τ' : ℝ)
    (C₀bd Cbias CF Cdil : NNReal) (D : ℕ) (c₁ : NNReal) (εg : ℝ)
    (hCbias : Cbias = lemma92Bias C₀bd ϱ) (hCF : CF = lemma92Constant ϱ)
    (hCdil : Cdil = capsuleDilationConstant) :
    CaseParams β ζ exscal ϱ η τ τ' → 16 ≤ C₀bd → ballCoverConstant ≤ D →
    0 < c₁ → 4 * (3072 * c₁) * (ballCoverConstant : NNReal) ≤ 1 → 0 < εg →
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      32 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) →
      ∀ {bι : Type u} (bs : Finset bι) (ctr : bι → E3) (P : bι → Set E3),
        bs.Nonempty →
        (∀ B ∈ bs, P B ⊆ Metric.ball (ctr B) ((cfg.r₁ : ℝ) / 16)) →
        (∀ B ∈ bs, P B ⊆ Metric.closedBall (ctr B) (cfg.r₁ : ℝ)) →
        (bs : Set bι).PairwiseDisjoint P →
        (∀ B, MeasurableSet (P B)) →
        (∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B) →
        (∀ (x : E3) (t : Finset bι), t ⊆ bs →
          (∀ B ∈ t, x ∈ Metric.ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant) →
        (∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty) →
        ∃ (a b : NNReal) (h : cfg.δ ≤ a ∧ a ≤ b ∧ b ≤ cfg.δ ^ cfg.exscal)
          (bd : BallData (cfg.withDims a b h)),
          bd.C₀ = C₀bd ∧ bd.Cbias = Cbias ∧ bd.CF = CF ∧ bd.Cdil = Cdil ∧
          bd.c₁ = c₁ ∧ bd.D = D ∧ bd.Cg ≤ cfg.δ ^ (-εg) ∧ bd.Cm = 1 ∧
          (bd.Cm : ENNReal) * (bd.m : ENNReal) ≤
            (fibreMassConstant : ENNReal) *
              (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) ∧
          cfg.δ ≤ bd.w₁ ∧ bd.w₁ ≤ 1 ∧
          (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
            (bd.Wb j).carrier ⊆ Metric.closedBall (bd.ctr B) (11 * (cfg.r₁ : ℝ) / 16)) ∧
          (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
            HasThicknesses (bd.Wb j).carrier C₀bd ![(cfg.r₁ : ℝ), (b : ℝ), (a : ℝ)]) ∧
          ((C₀bd : ℝ) * (a : ℝ) ≤ 5 * (cfg.r₁ : ℝ) / 16 →
            ∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
              Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
                Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) ∧
          (∀ B ∈ bd.bs, ∀ p ∈ bd.segs B,
            {q ∈ (bd.segs B : Set bd.σ) | q ≠ p ∧
              ¬ _root_.IsEssentiallyDistinct (bd.Y p).carrier (bd.Y q).carrier}.ncard ≤
                edMultiplicityConstant) := by
  intro params hC₀ hD hc₁ hc₁' hεg
  by_cases hη0 : 0 < η
  · have hη1 : η ≤ 1 := by
      have h6 := params.slabDensity
      have hs := params.scale
      linarith
    have hex0 : (0 : ℝ) < exscal := by
      have h6 := params.slabDensity
      linarith
    have hex1 : exscal < 1 := by have := params.scale; linarith
    have hεg5 : (0 : ℝ) < εg / 5 := by linarith
    have hϱ21 : ϱ ≤ 1 / 21 := caseParams_ϱ_le_one_div_21 params
    filter_upwards [eventually_ennreal_le_rpow_neg (K := (4 : ENNReal)) (by simp) hεg5,
      eventually_tierRetention_le_rpow (c₁ := c₁) hc₁ hη0.le hεg5,
      eventually_dimsClassLoss_le_rpow (ρ := (3 / 2 : NNReal)) one_lt_three_halves hεg5,
      eventually_uniformLossBound_relScale_le_rpow_neg 3 (exscal := exscal) (ϖ := ϱ)
        (p := (4 : ℝ)) hex0.le hex1 hεg5,
      eventually_numLevels_le_rpow_neg hεg5,
      eventually_card_s_le_rpow (η := η) hη1,
      eventually_nnreal_mul_rpow_le_rpow (2 : NNReal) (p := exscal) (q := 0) hex0,
      self_mem_nhdsWithin] with δ h4 hT hDl hL hK hcards hr₁ hδpos
    intro cfg hδ hη hexs hϱ hδr bι bs ctr P hbsne hP16 hP hdisj hmeas hcov hover hne
    have hr₁eq : cfg.r₁ = cfg.δ ^ exscal := by rw [VeryNotSticky.r₁, hexs]
    have hr₁1 : 2 * cfg.r₁ ≤ 1 := by
      rw [hr₁eq, hδ]
      simpa using hr₁
    have hϱ21' : cfg.ϱ ≤ 1 / 21 := by rw [hϱ]; exact hϱ21
    have hA4 : (4 : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(εg / 5)) := by rw [hδ]; exact h4
    have hAT : ((tierRetention cfg c₁ : NNReal) : ENNReal) ≤
        (cfg.δ : ENNReal) ^ (-(εg / 5)) := hT cfg hδ hη
    have hAD : ((dimsClassLoss (3 / 2) cfg.δ : ℕ) : ENNReal) ≤
        (cfg.δ : ENNReal) ^ (-(εg / 5)) := by rw [hδ]; exact hDl
    have hAL : ((uniformLossBound 3 cfg.s.card (cfg.δ / cfg.r₁) cfg.ϱ : NNReal) : ENNReal) ≤
        (cfg.δ : ENNReal) ^ (-(εg / 5)) := by
      rw [hr₁eq, hϱ, hδ]
      exact hL cfg.s.card (by rw [← hδ]; exact hcards cfg hδ hη)
    have hAK : ((4 * (numLevels cfg : NNReal) : NNReal) : ENNReal) ≤
        (cfg.δ : ENNReal) ^ (-(εg / 5)) := by
      rw [hδ]
      exact hK cfg.s.card (by rw [← hδ]; exact hcards cfg hδ hη)
    obtain ⟨a, b, hdims, bd, h1, h2, h3, h4', h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
      exists_ballData_capsule_of_cover cfg hC₀ hD hδr hϱ21' hr₁1 bs ctr P hbsne hP16 hP
        hdisj hmeas hcov hover hne hc₁ hc₁' hA4 hAT hAD hAL hAK
    refine ⟨a, b, hdims, bd, h1, ?_, ?_, ?_, h5, h6, h7, h8, h9, h10, h11, h12, h13, ?_, h14⟩
    · rw [hCbias, ← hϱ]; exact h2
    · rw [hCF, ← hϱ]; exact h3
    · rw [hCdil]; exact h4'
    · intro ha B hB j hj
      exact margin_of_localised_bodies (fun j hj => h12 B hB j hj)
        (fun j hj => h13 B hB j hj) ha j hj
  · filter_upwards with δ cfg hδ hη
    exact absurd (hη ▸ cfg.hη) hη0

/-! ### The target, with the non-ED degree clause -/

/-- **`BallDataGeneralTarget`'s conclusion, and the body of the boundary's `hEDdeg` for the
produced `bd`** — byte-for-byte the target's binders and conjuncts, plus the last conjunct.  The
capsule core meets every floor of the target: `16 ≤ edSegmentsConstant`,
`12288 ≤ edDensityConstant`, `32 ≤ edRadiusConstant` (all from `81 ≤ edDilateConstant`, i.e.
`C₃ ≥ 81` from `c₃ ≤ 16/9`).  The universal `hEDdeg` binder itself is **not** a theorem (T3's
core has non-`δ`-free degree); this is its instance for the general branch's own `bd`. -/
theorem ballDataGeneralTarget_edDegree (β ζ exscal ϱ η τ τ' : ℝ) (C₀bd : NNReal) (D : ℕ)
    (c₁ : NNReal) (εg : ℝ) :
  CaseParams β ζ exscal ϱ η τ τ' → edSegmentsConstant ≤ C₀bd → ballCoverConstant ≤ D →
    0 < c₁ → edDensityConstant * c₁ * (ballCoverConstant : NNReal) ≤ 1 → 0 < εg →
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) →
      ∀ {bι : Type u} (bs : Finset bι) (ctr : bι → E3) (P : bι → Set E3),
        bs.Nonempty →
        (∀ B ∈ bs, P B ⊆ Metric.ball (ctr B) ((cfg.r₁ : ℝ) / 16)) →
        (∀ B ∈ bs, P B ⊆ Metric.closedBall (ctr B) (cfg.r₁ : ℝ)) →
        (bs : Set bι).PairwiseDisjoint P →
        (∀ B, MeasurableSet (P B)) →
        (∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B) →
        (∀ (x : E3) (t : Finset bι), t ⊆ bs →
          (∀ B ∈ t, x ∈ Metric.ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant) →
        (∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty) →
        ∃ (a b : NNReal) (h : cfg.δ ≤ a ∧ a ≤ b ∧ b ≤ cfg.δ ^ cfg.exscal)
          (bd : BallData (cfg.withDims a b h)),
          bd.C₀ = C₀bd ∧ bd.Cbias = lemma92Bias C₀bd ϱ ∧ bd.CF = lemma92Constant ϱ ∧
          bd.Cdil ≤ capsuleDilationConstant ∧
          bd.c₁ = c₁ ∧ bd.D = D ∧ bd.Cg ≤ cfg.δ ^ (-εg) ∧ bd.Cm = 1 ∧
          (bd.Cm : ENNReal) * (bd.m : ENNReal) ≤
            (fibreMassConstant : ENNReal) *
              (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) ∧
          cfg.δ ≤ bd.w₁ ∧ bd.w₁ ≤ 1 ∧
          (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
            (bd.Wb j).carrier ⊆ Metric.closedBall (bd.ctr B) (11 * (cfg.r₁ : ℝ) / 16)) ∧
          (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
            HasThicknesses (bd.Wb j).carrier C₀bd ![(cfg.r₁ : ℝ), (b : ℝ), (a : ℝ)]) ∧
          ((a : ℝ) ≤ (cfg.δ : ℝ) ^ (1 - τ) →
            ∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
              Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
                Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) ∧
          (∀ B ∈ bd.bs, ∀ p ∈ bd.segs B,
            {q ∈ (bd.segs B : Set bd.σ) | q ≠ p ∧
              ¬ _root_.IsEssentiallyDistinct (bd.Y p).carrier (bd.Y q).carrier}.ncard ≤
                edMultiplicityConstant) := by
  intro params hC₀ hD hc₁ hc₁' hεg
  have hC₀16 : 16 ≤ C₀bd := le_trans sixteen_le_edSegmentsConstant hC₀
  have hc₁3072 : 4 * (3072 * c₁) * (ballCoverConstant : NNReal) ≤ 1 := by
    refine le_trans ?_ hc₁'
    rw [show (4 : NNReal) * (3072 * c₁) = 12288 * c₁ by ring]
    gcongr
    exact twelve288_le_edDensityConstant
  have hthin : exscal < 1 - τ := by have := params.thinScale; linarith
  filter_upwards [eventually_ballDataCapsule_except_margin.{u} β ζ exscal ϱ η τ τ' C₀bd
      (lemma92Bias C₀bd ϱ) (lemma92Constant ϱ) capsuleDilationConstant D c₁ εg rfl rfl rfl
      params hC₀16 hD hc₁ hc₁3072 hεg,
    eventually_nnreal_mul_rpow_le_rpow (C₀bd * (16 / 5)) (p := 1 - τ) (q := exscal) hthin]
    with δ hprod hguard
  intro cfg hδ hη hex hϱ hrad bι bs ctr P hbsne hP16 hP hdisj hmeas hcov hover hne
  have hδr : 32 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (cfg.δ).coe_nonneg) hrad
    exact_mod_cast thirtytwo_le_edRadiusConstant
  obtain ⟨a, b, hdims, bd, h1, h2, h3, h4, h5, h6, h7, hCm, hSPH, h10, h11, hloc, hprof, hmar,
    hdeg⟩ :=
    hprod cfg hδ hη hex hϱ hδr bs ctr P hbsne hP16 hP hdisj hmeas hcov hover hne
  refine ⟨a, b, hdims, bd, h1, h2, h3, h4.le, h5, h6, h7, hCm, hSPH, h10, h11, hloc, hprof, ?_,
    hdeg⟩
  · -- the margin, from the consumer's guard
    intro ha
    refine hmar ?_
    have haN : a ≤ cfg.δ ^ (1 - τ) := by
      rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
      exact ha
    have hr₁ : cfg.r₁ = cfg.δ ^ exscal := by rw [VeryNotSticky.r₁, hex]
    have hstep : C₀bd * a ≤ 5 / 16 * cfg.r₁ := by
      have hg : C₀bd * (16 / 5) * δ ^ (1 - τ) ≤ δ ^ exscal := hguard
      have hg' : (5 / 16 : NNReal) * (C₀bd * (16 / 5) * δ ^ (1 - τ)) ≤
          (5 / 16 : NNReal) * δ ^ exscal := by gcongr
      have hcancel : (5 / 16 : NNReal) * (C₀bd * (16 / 5) * δ ^ (1 - τ))
          = C₀bd * δ ^ (1 - τ) := by
        rw [show (5 / 16 : NNReal) * (C₀bd * (16 / 5) * δ ^ (1 - τ))
              = ((5 / 16 : NNReal) * (16 / 5)) * (C₀bd * δ ^ (1 - τ)) by ring,
          show ((5 / 16 : NNReal) * (16 / 5)) = 1 by norm_num, one_mul]
      rw [hcancel] at hg'
      have haN' : a ≤ δ ^ (1 - τ) := by rw [← hδ]; exact haN
      rw [hr₁, hδ]
      refine le_trans ?_ hg'
      gcongr
    have := NNReal.coe_le_coe.2 hstep
    push_cast at this ⊢
    linarith

end Kakeya.VeryNotSticky
