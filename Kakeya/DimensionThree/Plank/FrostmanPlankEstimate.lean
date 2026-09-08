/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.FrostmanPlankReduction
public import Kakeya.Uniform
public import Kakeya.ShadedUniform

/-!
# GWZ Section 6 estimates: Frostman estimate for planks

This file formalises `Kakeya.FrostmanEstimate.plankEstimate` — GWZ Lemma 6.4 (Frostman estimate
for planks) — together with the `ENNReal`/rpow algebra and the μ-split interface it consumes.
GWZ Lemma 6.4 is proved here, resting on the sorried geometry-interface leaves in
`FrostmanPlankGeometry.lean`.

The two tube-multiplicity propositions built on top of it,
`Kakeya.tubeMultiplicityOfLocalPlankFactorisation` (GWZ Proposition 6.6(A)) and
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` (GWZ Proposition 6.6(B)), live in
`PlankFactorizationEstimate.lean`.

## Conventions

Shaded plank families are represented directly by `V : ι → ShadedPlank a b hab hb1`. This keeps
the geometric plank and its shading on one shared carrier, as for `ShadedTube` and `ShadedSlab`,
without a separate carrier-equality hypothesis. Thus fullness and multiplicity use
`fun i ↦ (V i).toShadedBody`, while max-density and the Frostman constant use
`fun i ↦ (V i).toConvexSpaceBody`.

The plank-to-tube reduction itself (`Kakeya.redPlankTube`, GWZ 6.13) uses the weaker *independent*
interface: a plank family `P : ι → Plank a b hab hb1`, a shading `Y : ι → ShadedBody _`, and the
containment `hYP : ∀ i ∈ s, (Y i).shade ⊆ (P i).carrier`. A Section 6 caller holding a bundled `V`
instantiates it with `P := fun i ↦ (V i).toPrism3D`, `Y := fun i ↦ (V i).toShadedBody` and
`hYP := fun i _ ↦ (V i).shade_subset`; no wrapper structure is needed in either direction.

The Frostman constant `C_F(PS)` is carried, as elsewhere in this development
(cf. `Kakeya.FrostmanEstimate.multiplicity_bound`), by a parameter `CF : ENNReal` together with a
Frostman hypothesis `IsFrostmanIn s (fun i ↦ (P i).toConvexSpaceBody) closedUnitBall CF`.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal Classical

noncomputable section

namespace Kakeya

/-- A lemma: for nonzero finite x,y in ENNReal, (x*y)^z = x^z * y^z for any real z. -/
private lemma mul_rpow_lemma (x y : ENNReal) (hx0 : x ≠ 0) (hx_top : x ≠ ⊤) (hy0 : y ≠ 0) (hy_top : y ≠ ⊤) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z := by
  rw [ENNReal.mul_rpow_eq_ite]
  have h_not_cond : ¬ ((x = 0 ∧ y = ⊤) ∨ (x = ⊤ ∧ y = 0)) := by
    intro h
    rcases h with (⟨hx0', hy_top'⟩ | ⟨hx_top', hy0'⟩)
    · exact hx0 hx0'
    · exact hy0 hy0'
  simp [h_not_cond]

/-- **Frostman multiplicity rpow identity, `ENNReal` form** (for GWZ Lemma 6.4).
The Frostman constant is carried directly as `CF : ENNReal` (nonzero and finite).  Proved
self-contained, by mirroring the `ℝ≥0` `calc` chain step for step in `ENNReal` under the
nonzero/finite side conditions; it does **not** reduce to an `ℝ≥0` identity via coercion. -/
theorem frostmanMultRpowIdentityENN {ε β : ℝ} {a b M : ℝ≥0} {CF : ENNReal} {ns : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hM : M ≠ 0) (hCF0 : CF ≠ 0) (hCFtop : CF ≠ ⊤) (hns : ns ≠ 0) :
    ((a : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
        * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ (-2 * β)
        * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2))
      * (8 * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
        * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (β / 2))
      = 8 * (a : ENNReal) * (b : ENNReal) * (ns : ENNReal) := by
  -- ENNReal nonzero/finite hypotheses for the coercion factors
  have ha_enn : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha
  have ha_enn_top : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hb_enn : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hb
  have hb_enn_top : (b : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hM_enn : (M : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hM
  have hM_enn_top : (M : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hns_enn : (ns : ENNReal) ≠ 0 := by
    have hns' : (ns : ℝ≥0) ≠ 0 := by exact_mod_cast hns
    exact ENNReal.coe_ne_zero.mpr hns'
  have hns_enn_top : (ns : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- derived nonzero/finite conditions
  have hb2_enn : ((b : ENNReal) ^ 2) ≠ 0 := pow_ne_zero 2 hb_enn
  have hb2_enn_top : ((b : ENNReal) ^ 2) ≠ ⊤ := ENNReal.pow_ne_top hb_enn_top
  have hb2ns_enn : ((b : ENNReal) ^ 2 * (ns : ENNReal)) ≠ 0 := mul_ne_zero hb2_enn hns_enn
  have hb2ns_enn_top : ((b : ENNReal) ^ 2 * (ns : ENNReal)) ≠ ⊤ :=
    ENNReal.mul_ne_top hb2_enn_top hns_enn_top
  have hM_inv_enn : ((M : ENNReal)⁻¹) ≠ 0 :=
    ENNReal.inv_ne_zero.mpr hM_enn_top
  have hM_inv_enn_top : ((M : ENNReal)⁻¹) ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr hM_enn
  -- The identity follows by mirroring the NNReal `calc` proof
  calc
    ((a : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
        * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ (-2 * β)
        * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2))
      * (8 * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
        * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (β / 2))
    = 8 * ((a : ENNReal) ^ (-ε) * (a : ENNReal) ^ ε) * (CF ^ (1 - β / 2) * CF ^ (β / 2 - 1))
        * (M : ENNReal) ^ (β / 2)
        * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (β / 2)
        * ((a : ENNReal) / (b : ENNReal))
        * ((b : ENNReal) ^ (-2 * β) * (b : ENNReal) ^ (2 * β))
        * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2) := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    _ = 8 * ((a : ENNReal) ^ ((-ε) + ε)) * (CF ^ ((1 - β / 2) + (β / 2 - 1)))
        * (M : ENNReal) ^ (β / 2)
        * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (β / 2)
        * ((a : ENNReal) / (b : ENNReal))
        * ((b : ENNReal) ^ ((-2 * β) + (2 * β)))
        * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2) := by
      rw [ENNReal.rpow_add (-ε) ε ha_enn ha_enn_top,
        ENNReal.rpow_add (1 - β / 2) (β / 2 - 1) hCF0 hCFtop,
        ENNReal.rpow_add (-2 * β) (2 * β) hb_enn hb_enn_top]
    _ = 8 * ((a : ENNReal) ^ (0 : ℝ)) * (CF ^ (0 : ℝ)) * (M : ENNReal) ^ (β / 2)
        * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (β / 2)
        * ((a : ENNReal) / (b : ENNReal))
        * ((b : ENNReal) ^ (0 : ℝ))
        * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2) := by
      ring
    _ = 8 * (1 : ENNReal) * (1 : ENNReal) * (M : ENNReal) ^ (β / 2)
        * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (β / 2)
        * ((a : ENNReal) / (b : ENNReal))
        * (1 : ENNReal)
        * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2) := by
      simp [ha_enn, hCF0, hb_enn]
    _ = 8 * (M : ENNReal) ^ (β / 2)
        * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (β / 2)
        * ((a : ENNReal) / (b : ENNReal))
        * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2) := by
      simp
    _ = 8 * ((a : ENNReal) / (b : ENNReal)) * (M : ENNReal) ^ (β / 2)
        * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (β / 2)
        * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2) := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    _ = 8 * ((a : ENNReal) / (b : ENNReal)) * (M : ENNReal) ^ (β / 2)
        * (((M : ENNReal)⁻¹) ^ (β / 2) * ((b : ENNReal) ^ 2) ^ (β / 2) * (ns : ENNReal) ^ (β / 2))
        * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2) := by
      calc
        8 * ((a : ENNReal) / (b : ENNReal)) * (M : ENNReal) ^ (β / 2)
          * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (β / 2)
          * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2)
        = 8 * ((a : ENNReal) / (b : ENNReal)) * (M : ENNReal) ^ (β / 2)
          * (((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2) * (ns : ENNReal)) ^ (β / 2)
          * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2) := by
          simp [mul_assoc]
        _ = 8 * ((a : ENNReal) / (b : ENNReal)) * (M : ENNReal) ^ (β / 2)
          * (((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2) ^ (β / 2) * (ns : ENNReal) ^ (β / 2))
          * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2) := by
          rw [mul_rpow_lemma ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2) (ns : ENNReal)
            (mul_ne_zero hM_inv_enn hb2_enn) (ENNReal.mul_ne_top hM_inv_enn_top hb2_enn_top)
            hns_enn hns_enn_top (β / 2)]
        _ = 8 * ((a : ENNReal) / (b : ENNReal)) * (M : ENNReal) ^ (β / 2)
          * (((M : ENNReal)⁻¹) ^ (β / 2) * ((b : ENNReal) ^ 2) ^ (β / 2) * (ns : ENNReal) ^ (β / 2))
          * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2) := by
          rw [mul_rpow_lemma ((M : ENNReal)⁻¹) ((b : ENNReal) ^ 2) hM_inv_enn hM_inv_enn_top
            hb2_enn hb2_enn_top (β / 2), mul_assoc]
    _ = 8 * ((a : ENNReal) / (b : ENNReal))
        * ((M : ENNReal) ^ (β / 2) * ((M : ENNReal)⁻¹) ^ (β / 2))
        * (((b : ENNReal) ^ 2) ^ (β / 2) * (ns : ENNReal) ^ (β / 2)
          * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2)) := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    _ = 8 * ((a : ENNReal) / (b : ENNReal))
        * ((M : ENNReal) * (M : ENNReal)⁻¹) ^ (β / 2)
        * (((b : ENNReal) ^ 2) ^ (β / 2) * (ns : ENNReal) ^ (β / 2)
          * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2)) := by
      rw [mul_rpow_lemma (M : ENNReal) ((M : ENNReal)⁻¹) hM_enn hM_enn_top hM_inv_enn hM_inv_enn_top (β / 2)]
    _ = 8 * ((a : ENNReal) / (b : ENNReal))
        * ((1 : ENNReal) ^ (β / 2))
        * (((b : ENNReal) ^ 2) ^ (β / 2) * (ns : ENNReal) ^ (β / 2)
          * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2)) := by
      have hM_mul_inv : (M : ENNReal) * (M : ENNReal)⁻¹ = (1 : ENNReal) :=
        ENNReal.mul_inv_cancel hM_enn hM_enn_top
      rw [hM_mul_inv]
    _ = 8 * ((a : ENNReal) / (b : ENNReal)) * (1 : ENNReal)
        * (((b : ENNReal) ^ 2) ^ (β / 2) * (ns : ENNReal) ^ (β / 2)
          * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2)) := by
      simp
    _ = 8 * ((a : ENNReal) / (b : ENNReal))
        * (((b : ENNReal) ^ 2) ^ (β / 2) * (ns : ENNReal) ^ (β / 2)
          * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2)) := by
      simp
    _ = 8 * ((a : ENNReal) / (b : ENNReal))
        * (((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (β / 2)
          * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2)) := by
      calc
        8 * ((a : ENNReal) / (b : ENNReal))
          * (((b : ENNReal) ^ 2) ^ (β / 2) * (ns : ENNReal) ^ (β / 2)
            * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2))
        = 8 * ((a : ENNReal) / (b : ENNReal))
          * ((((b : ENNReal) ^ 2) ^ (β / 2) * (ns : ENNReal) ^ (β / 2))
            * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2)) := by
          simp [mul_assoc]
        _ = 8 * ((a : ENNReal) / (b : ENNReal))
          * (((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (β / 2)
            * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 - β / 2)) := by
          rw [mul_rpow_lemma ((b : ENNReal) ^ 2) (ns : ENNReal) hb2_enn hb2_enn_top hns_enn hns_enn_top (β / 2),
            mul_assoc]
    _ = 8 * ((a : ENNReal) / (b : ENNReal))
        * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ ((β / 2) + (1 - β / 2)) := by
      rw [ENNReal.rpow_add (β / 2) (1 - β / 2) hb2ns_enn hb2ns_enn_top]
    _ = 8 * ((a : ENNReal) / (b : ENNReal))
        * ((b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (1 : ℝ) := by
      ring
    _ = 8 * ((a : ENNReal) / (b : ENNReal)) * ((b : ENNReal) ^ 2 * (ns : ENNReal)) := by
      simp
    _ = 8 * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ 2 * (ns : ENNReal) := by
      simp [mul_assoc]
    _ = 8 * (a : ENNReal) * (b : ENNReal) * (ns : ENNReal) := by
      calc
        8 * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ 2 * (ns : ENNReal)
          = 8 * ((a : ENNReal) * (b : ENNReal)⁻¹) * ((b : ENNReal) ^ 2) * (ns : ENNReal) := by
          simp [div_eq_mul_inv]
        _ = 8 * (a : ENNReal) * ((b : ENNReal)⁻¹ * (b : ENNReal) ^ 2) * (ns : ENNReal) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
        _ = 8 * (a : ENNReal) * (((b : ENNReal)⁻¹ * (b : ENNReal)) * (b : ENNReal)) * (ns : ENNReal) := by
          simp [mul_assoc, pow_two]
        _ = 8 * (a : ENNReal) * ((1 : ENNReal) * (b : ENNReal)) * (ns : ENNReal) := by
          simp [ENNReal.inv_mul_cancel hb_enn hb_enn_top]
        _ = 8 * (a : ENNReal) * (b : ENNReal) * (ns : ENNReal) := by
          simp

/-- **Absolute-constant absorption into `a^ε`** (choice of `b₀` for GWZ Lemma 6.4).
For a fixed positive absolute constant `cabs` and `ε > 0` there is `b₀ > 0` so that, for all
`0 < a ≤ b ≤ b₀`, `8 · a^ε ≤ cabs · a^(ε/2)` in `ENNReal`. This upgrades the aggregate bound (which
carries `a^(ε/2)` and the absolute constant `cabs`) to the factor-`8` bound with the sharper `a^ε`
by choosing `b₀` small. -/
theorem expAbsorbConstant (cabs : ℝ≥0) (hcabs : 0 < cabs) {ε : ℝ} (hε : 0 < ε) :
    ∃ b₀ : ℝ≥0, 0 < b₀ ∧ ∀ (a b : ℝ≥0), 0 < a → a ≤ b → b ≤ b₀ →
      (8 : ENNReal) * (a : ENNReal) ^ ε ≤ (cabs : ENNReal) * (a : ENNReal) ^ (ε / 2) := by
  -- choose b₀ = (cabs/8)^(2/ε)
  set b₀ := ((cabs / 8 : ℝ≥0) ^ ((2 : ℝ) / ε) : ℝ≥0) with hb₀_def
  have hcabs_div8_pos : 0 < cabs / 8 := div_pos hcabs (by norm_num : (0 : ℝ≥0) < 8)
  have hb₀_pos : 0 < b₀ := by
    dsimp [b₀]
    exact NNReal.rpow_pos hcabs_div8_pos
  refine ⟨b₀, hb₀_pos, ?_⟩
  intro a b ha hab hbb₀
  have ha₀ : a ≤ b₀ := le_trans hab hbb₀
  have ha_nonzero : a ≠ 0 := ha.ne'
  have hε_div2_nonneg : 0 ≤ ε / 2 := by nlinarith
  -- Step 1: a^(ε/2) ≤ cabs/8 in ℝ≥0
  have h_a_pow_half : a ^ (ε / 2) ≤ cabs / 8 := by
    calc
      a ^ (ε / 2) ≤ b₀ ^ (ε / 2) := NNReal.rpow_le_rpow ha₀ hε_div2_nonneg
      _ = ((cabs / 8 : ℝ≥0) ^ ((2 : ℝ) / ε)) ^ (ε / 2) := by rfl
      _ = (cabs / 8 : ℝ≥0) ^ (((2 : ℝ) / ε) * (ε / 2)) := by
        rw [← NNReal.rpow_mul (cabs / 8 : ℝ≥0) ((2 : ℝ) / ε) (ε / 2)]
      _ = (cabs / 8 : ℝ≥0) ^ (1 : ℝ) := by
        have h_exp : ((2 : ℝ) / ε) * (ε / 2) = (1 : ℝ) := by
          calc
            ((2 : ℝ) / ε) * (ε / 2) = (2 * ε) / (ε * 2) := by ring
            _ = (2 * ε) / (2 * ε) := by ring
            _ = 1 := by field_simp [hε.ne']
        rw [h_exp]
      _ = cabs / 8 := by simp
  -- Step 2: 8 * a^(ε/2) ≤ cabs in ℝ≥0
  have h_8a_pow_half : (8 : ℝ≥0) * a ^ (ε / 2) ≤ cabs := by
    calc
      (8 : ℝ≥0) * a ^ (ε / 2) ≤ (8 : ℝ≥0) * (cabs / 8) :=
        mul_le_mul_left' h_a_pow_half (8 : ℝ≥0)
      _ = cabs := by
        field_simp [show (8 : ℝ≥0) ≠ 0 from by norm_num]
  -- Step 3: lift to ENNReal: (8:ENNReal)*(a:ENNReal)^(ε/2) ≤ (cabs:ENNReal)
  have h_8a_pow_half_enn : (8 : ENNReal) * (a : ENNReal) ^ (ε / 2) ≤ (cabs : ENNReal) := by
    calc
      (8 : ENNReal) * (a : ENNReal) ^ (ε / 2) = ((8 : ℝ≥0) : ENNReal) * ((a : ENNReal) ^ (ε / 2)) := by norm_num
      _ = ((8 : ℝ≥0) : ENNReal) * ((a ^ (ε / 2) : ℝ≥0) : ENNReal) := by
        simp [ENNReal.coe_rpow_of_ne_zero ha_nonzero (ε / 2)]
      _ = ((8 : ℝ≥0) * (a ^ (ε / 2) : ℝ≥0) : ENNReal) := by norm_cast
      _ ≤ (cabs : ENNReal) := by exact_mod_cast h_8a_pow_half
  -- Step 4: (a:ENNReal)^ε = (a:ENNReal)^(ε/2) * (a:ENNReal)^(ε/2)
  have h_a_pow_ε_split : (a : ENNReal) ^ ε = (a : ENNReal) ^ (ε / 2) * (a : ENNReal) ^ (ε / 2) := by
    calc
      (a : ENNReal) ^ ε = (a : ENNReal) ^ (ε / 2 + ε / 2) := by ring
      _ = (a : ENNReal) ^ (ε / 2) * (a : ENNReal) ^ (ε / 2) := by
        rw [ENNReal.rpow_add (ε / 2) (ε / 2) (ENNReal.coe_ne_zero.mpr ha_nonzero) ENNReal.coe_ne_top]
  -- Step 5: combine
  calc
    (8 : ENNReal) * (a : ENNReal) ^ ε
        = (8 : ENNReal) * ((a : ENNReal) ^ (ε / 2) * (a : ENNReal) ^ (ε / 2)) := by rw [h_a_pow_ε_split]
    _ = ((8 : ENNReal) * (a : ENNReal) ^ (ε / 2)) * (a : ENNReal) ^ (ε / 2) := by ring
    _ ≤ (cabs : ENNReal) * (a : ENNReal) ^ (ε / 2) := mul_le_mul_right' h_8a_pow_half_enn ((a : ENNReal) ^ (ε / 2))

/-- **Multiplicity bound from the union-volume lower bound** (algebra step of GWZ Lemma 6.4).
Given the factor-`8` union-volume lower bound `VOL8` and that each shaded body is its plank
(so its carrier has volume `8·a·b`), the multiplicity bound follows by
`μ(PS,Y) ≤ (∑|carrier|)/|U| = 8ab|s|/|U| ≤ target`. Pure `ENNReal`/rpow algebra; not geometry. -/
theorem multiplicityBoundFromVolume {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1) {ε : ℝ}
    {a b : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) {M : ℝ≥0} (hM : 1 ≤ M)
    {CF : ENNReal} (hCF1 : 1 ≤ CF) (hCFtop : CF ≠ ⊤)
    {ι : Type*} (s : Finset ι) (V : ι → ShadedPlank a b hab hb1)
    (hvol8 : 8 * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
        * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (β / 2)
        ≤ volume (⋃ i ∈ s, (V i).shade)) :
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
      (a : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
        * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ (-2 * β)
        * ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (1 - β / 2) := by
  -- Step 1: handle the empty case
  rcases s.eq_empty_or_nonempty with rfl|hs
  · simp [ShadedBody.multiplicity_empty]
  -- Step 2: nonzero hypotheses
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := (ha.trans_le hab).ne'
  have hM0 : M ≠ 0 := by
    have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hM
    exact hMpos.ne'
  have hCF0 : CF ≠ 0 := by
    have hpos : (0 : ENNReal) < 1 := by norm_num
    have hCFpos : 0 < CF := hpos.trans_le hCF1
    exact hCFpos.ne'
  have hns0 : s.card ≠ 0 := Finset.card_ne_zero.mpr hs
  -- Step 3: the key identity T * den = (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))
  have hkey : ((a : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
      * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ (-2 * β)
      * ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (1 - β / 2))
    * (8 * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
      * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (β / 2))
    = (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by
    calc
      ((a : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
          * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ (-2 * β)
          * ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (1 - β / 2))
        * (8 * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
          * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (β / 2))
      = 8 * (a : ENNReal) * (b : ENNReal) * (s.card : ENNReal) :=
        frostmanMultRpowIdentityENN ha0 hb0 hM0 hCF0 hCFtop hns0
      _ = (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by
        ring
  -- Step 4: carrier sum equals `(s.card : ENNReal) * (8 * a * b)`.
  have hsum : (∑ i ∈ s, volume (V i).carrier) =
      (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by
    calc
      (∑ i ∈ s, volume (V i).carrier) =
          (∑ i ∈ s, 8 * (a : ENNReal) * (b : ENNReal)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Prism3D.volume_carrier (V i).toPrism3D]
        simp
      _ = (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by
        simp
  -- Step 5: U ≠ ⊤ and den ≠ 0 and U ≠ 0
  set den := 8 * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
      * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (β / 2) with hden
  set T := (a : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
      * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ (-2 * β)
      * ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (1 - β / 2) with hT
  set U := volume (⋃ i ∈ s, (V i).shade) with hU
  have hUtop : U ≠ ⊤ :=
    ShadedBody.volume_iUnion_shade_ne_top s (fun i => (V i).toShadedBody)
  have hden0 : den ≠ 0 := by
    dsimp [den]
    have ha_enn : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha0
    have ha_enn_top : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hb_enn : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hb0
    have hb_enn_top : (b : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hM_enn_top : (M : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hns_enn : (s.card : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (by
      have hns0' : (s.card : ℝ≥0) ≠ 0 := by exact_mod_cast hns0
      exact hns0')
    have hns_enn_top : (s.card : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hM_inv_enn : ((M : ENNReal)⁻¹) ≠ 0 := ENNReal.inv_ne_zero.mpr hM_enn_top
    have hM_inv_enn_top : ((M : ENNReal)⁻¹) ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hM0)
    have hb2_enn : ((b : ENNReal) ^ 2) ≠ 0 := pow_ne_zero 2 hb_enn
    have hb2_enn_top : ((b : ENNReal) ^ 2) ≠ ⊤ := ENNReal.pow_ne_top hb_enn_top
    have hM_mul : ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (s.card : ENNReal)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hM_inv_enn hb2_enn) hns_enn
    have hM_mul_top : ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (s.card : ENNReal)) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top hM_inv_enn_top hb2_enn_top) hns_enn_top
    -- helper lemma: nonzero finite ^ y ≠ 0
    have h_rpow_nonzero : ∀ (x : ENNReal) (y : ℝ), x ≠ 0 → x ≠ ⊤ → x ^ y ≠ 0 := by
      intro x y hx0 hx_top
      intro hzero
      rw [ENNReal.rpow_eq_zero_iff] at hzero
      rcases hzero with (⟨h0, _⟩ | ⟨htop, _⟩)
      · exact hx0 h0
      · exact hx_top htop
    have h8 : (8 : ENNReal) ≠ 0 := by norm_num
    have h1 : (a : ENNReal) ^ ε ≠ 0 := h_rpow_nonzero (a : ENNReal) ε ha_enn ha_enn_top
    have h2 : CF ^ (β / 2 - 1) ≠ 0 := h_rpow_nonzero CF (β / 2 - 1) hCF0 hCFtop
    have h3 : (b : ENNReal) ^ (2 * β) ≠ 0 := h_rpow_nonzero (b : ENNReal) (2 * β) hb_enn hb_enn_top
    have h4 : ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (β / 2) ≠ 0 :=
      h_rpow_nonzero ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (s.card : ENNReal)) (β / 2) hM_mul hM_mul_top
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h8 h1) h2) h3) h4
  have hU0 : U ≠ 0 := by
    intro hUzero
    apply hden0
    have hden_le_U : den ≤ U := hvol8
    rw [hUzero] at hden_le_U
    have h0_le_den : 0 ≤ den := by positivity
    exact le_antisymm hden_le_U h0_le_den
  -- Step 6: (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) ≤ T * U
  have hineq : (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) ≤ T * U := by
    calc
      (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) = T * den := hkey.symm
      _ ≤ T * U := mul_le_mul_left' hvol8 T
  -- Step 7: assemble the final inequality
  calc
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
        ≤ (∑ i ∈ s, volume (V i).carrier) / U :=
      ShadedBody.multiplicity_le_sum_carrier_div s (fun i => (V i).toShadedBody)
    _ = ((s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) / U := by rw [hsum]
    _ ≤ T := by
      rw [ENNReal.div_le_iff hU0 hUtop]
      exact hineq

/-- **Aggregate the per-slab volume bounds** (summation + cardinality step of GWZ Lemma 6.4).
Summing the per-slab union-volume lower bounds over the used slabs (their fibres partition `𝒯`,
so `∑_S |f_S| = |𝒯|`, which cancels the `θ^(β/2)` factor), then inserting the fibre concentration
`N ≤ Ccard·M·θ` and the cardinality comparison `|s| ≤ Ccard·N·|𝒯|` and the aggregate union
comparison `c3·∑_S |U(f_S)| ≤ Uvol`, yields the aggregate lower bound with an absolute constant.
Pure `Finset`/`ENNReal`/rpow algebra; not geometry. -/
theorem aggregateSlabVolume {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1) {ε : ℝ} (hε : 0 < ε)
    {a b : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) {θ : ℝ≥0} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    {N : ℕ} (hN1 : 1 ≤ N) {M Ccard K c3 : ℝ≥0} (hM : 1 ≤ M) (hCcard : 1 ≤ Ccard)
    (hK : 0 < K) (hc3 : 0 < c3) {CF : ENNReal} (hCF1 : 1 ≤ CF) (hCFtop : CF ≠ ⊤)
    {τ σ : Type} (Yθ : τ → ShadedBody (EuclideanSpace ℝ (Fin 3))) (𝒯 : Finset τ)
    (slabOf : τ → σ) (𝒮 : Finset σ) (ns : ℕ) (Uvol : ENNReal) (h𝒯 : 𝒯.Nonempty)
    (hpart : ∀ t ∈ 𝒯, slabOf t ∈ 𝒮)
    (hNth : (N : ℝ≥0) ≤ Ccard * M * θ)
    (hcard : (ns : ℝ≥0) ≤ Ccard * (N : ℝ≥0) * (𝒯.card : ℝ≥0))
    (hperslab : ∀ S ∈ 𝒮, (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
        * ((b : ENNReal) ^ 2) ^ (β / 2) * (θ : ENNReal) ^ (β / 2)
        * (𝒯.card : ENNReal) ^ (β / 2 - 1)
        * ((𝒯.filter (fun t => slabOf t = S)).card : ENNReal)
        ≤ (K : ENNReal) * volume (⋃ t ∈ 𝒯.filter (fun t => slabOf t = S), (Yθ t).shade))
    (hagg : (c3 : ENNReal) * ∑ S ∈ 𝒮,
        volume (⋃ t ∈ 𝒯.filter (fun t => slabOf t = S), (Yθ t).shade) ≤ Uvol) :
    (c3 : ENNReal) / (K : ENNReal) * ((Ccard : ENNReal) ^ 2) ^ (-(β / 2)) * (a : ENNReal) ^ ε
        * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
        * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (β / 2) ≤ Uvol := by
  set p := β / 2 with hp
  have hp_nonneg : 0 ≤ p := by nlinarith
  have hp_pos : 0 < p := by nlinarith
  have hβ_nonneg : 0 ≤ β := by nlinarith
  have h𝒯_ne_zero : (𝒯.card : ENNReal) ≠ 0 := by
    have h0 : 𝒯.card ≠ 0 := Finset.card_ne_zero.mpr h𝒯
    exact ENNReal.coe_ne_zero.mpr (by exact_mod_cast h0)
  have h𝒯_ne_top : (𝒯.card : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hθ_ne_zero : (θ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (by exact hθ0.ne')
  have hθ_ne_top : (θ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hK_ne_zero : (K : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hK.ne'
  have hK_ne_top : (K : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hc3_ne_zero : (c3 : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hc3.ne'
  have hc3_ne_top : (c3 : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCcard_ne_zero : (Ccard : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (by
    have hCcard_pos : 0 < Ccard := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hCcard
    exact hCcard_pos.ne')
  have hCcard_ne_top : (Ccard : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hM_ne_zero : (M : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (by
    have hM_pos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hM
    exact hM_pos.ne')
  have hM_ne_top : (M : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCcard_sq_ne_zero : ((Ccard : ENNReal)^2) ≠ 0 := pow_ne_zero 2 hCcard_ne_zero
  have hCcard_sq_ne_top : ((Ccard : ENNReal)^2) ≠ ⊤ := ENNReal.pow_ne_top hCcard_ne_top

  -- Step 1: sum hperslab over S ∈ 𝒮, factor common term
  set common : ENNReal := (a : ENNReal)^ε * CF^(p-1) * (b : ENNReal)^(2*β)
    * ((b : ENNReal)^2)^p * (θ : ENNReal)^p * (𝒯.card : ENNReal)^(p-1) with hcommon
  have hcommon_eq : common = (a : ENNReal)^ε * CF^(β/2 - 1) * (b : ENNReal)^(2*β)
    * ((b : ENNReal)^2)^(β/2) * (θ : ENNReal)^(β/2) * (𝒯.card : ENNReal)^(β/2 - 1) := by
    simp [hcommon, hp]
  have hperslab' : ∀ S ∈ 𝒮, common * ((𝒯.filter (fun t => slabOf t = S)).card : ENNReal)
    ≤ (K : ENNReal) * volume (⋃ t ∈ 𝒯.filter (fun t => slabOf t = S), (Yθ t).shade) := by
    intro S hS
    have h_eq : (a : ENNReal)^ε * CF^(β/2 - 1) * (b : ENNReal)^(2*β)
      * ((b : ENNReal)^2)^(β/2) * (θ : ENNReal)^(β/2) * (𝒯.card : ENNReal)^(β/2 - 1)
      * ((𝒯.filter (fun t => slabOf t = S)).card : ENNReal) = common * ((𝒯.filter (fun t => slabOf t = S)).card : ENNReal) := by
      rw [hcommon_eq, mul_assoc]
    rw [← h_eq]
    exact hperslab S hS

  have hsum : ∑ S ∈ 𝒮, common * ((𝒯.filter (fun t => slabOf t = S)).card : ENNReal) ≤
    ∑ S ∈ 𝒮, (K : ENNReal) * volume (⋃ t ∈ 𝒯.filter (fun t => slabOf t = S), (Yθ t).shade) :=
    Finset.sum_le_sum fun S hS => hperslab' S hS

  have hsumLHS : ∑ S ∈ 𝒮, common * ((𝒯.filter (fun t => slabOf t = S)).card : ENNReal) =
    common * (∑ S ∈ 𝒮, ((𝒯.filter (fun t => slabOf t = S)).card : ENNReal)) := by
    rw [Finset.mul_sum]

  have hsum_fibers : ∑ S ∈ 𝒮, ((𝒯.filter (fun t => slabOf t = S)).card : ENNReal) = (𝒯.card : ENNReal) := by
    have h_mapsTo : (𝒯 : Set τ).MapsTo slabOf 𝒮 := by
      intro x hx; exact hpart x hx
    have hsum_nat : ∑ S ∈ 𝒮, (𝒯.filter (fun t => slabOf t = S)).card = 𝒯.card :=
      (Finset.card_eq_sum_card_fiberwise h_mapsTo).symm
    exact_mod_cast hsum_nat

  have hsumLHS' : ∑ S ∈ 𝒮, common * ((𝒯.filter (fun t => slabOf t = S)).card : ENNReal) = common * (𝒯.card : ENNReal) := by
    rw [hsumLHS, hsum_fibers]

  have hsumRHS : ∑ S ∈ 𝒮, (K : ENNReal) * volume (⋃ t ∈ 𝒯.filter (fun t => slabOf t = S), (Yθ t).shade) =
    (K : ENNReal) * (∑ S ∈ 𝒮, volume (⋃ t ∈ 𝒯.filter (fun t => slabOf t = S), (Yθ t).shade)) := by
    rw [Finset.mul_sum]

  have hineq1 : common * (𝒯.card : ENNReal) ≤
    (K : ENNReal) * (∑ S ∈ 𝒮, volume (⋃ t ∈ 𝒯.filter (fun t => slabOf t = S), (Yθ t).shade)) := by
    calc
      common * (𝒯.card : ENNReal) = ∑ S ∈ 𝒮, common * ((𝒯.filter (fun t => slabOf t = S)).card : ENNReal) := by
        rw [hsumLHS']
      _ ≤ ∑ S ∈ 𝒮, (K : ENNReal) * volume (⋃ t ∈ 𝒯.filter (fun t => slabOf t = S), (Yθ t).shade) := hsum
      _ = (K : ENNReal) * (∑ S ∈ 𝒮, volume (⋃ t ∈ 𝒯.filter (fun t => slabOf t = S), (Yθ t).shade)) := hsumRHS

  -- Step 2: multiply by c3 and use hagg
  have hineq2 : (c3 : ENNReal) * common * (𝒯.card : ENNReal) ≤ (K : ENNReal) * Uvol := by
    calc
      (c3 : ENNReal) * common * (𝒯.card : ENNReal) = (c3 : ENNReal) * (common * (𝒯.card : ENNReal)) := by
        simp [mul_assoc]
      _ ≤ (c3 : ENNReal) * ((K : ENNReal) * (∑ S ∈ 𝒮, volume (⋃ t ∈ 𝒯.filter (fun t => slabOf t = S), (Yθ t).shade))) :=
        mul_le_mul_left' hineq1 (c3 : ENNReal)
      _ = (K : ENNReal) * ((c3 : ENNReal) * (∑ S ∈ 𝒮, volume (⋃ t ∈ 𝒯.filter (fun t => slabOf t = S), (Yθ t).shade))) := by
        simp [mul_comm, mul_left_comm, mul_assoc]
      _ ≤ (K : ENNReal) * Uvol := mul_le_mul_left' hagg (K : ENNReal)

  -- Simplify common * (𝒯.card : ENNReal) = a^ε * CF^(p-1) * b^(2β) * (b^2)^p * θ^p * (𝒯.card)^p
  have hprod_simp : common * (𝒯.card : ENNReal) = (a : ENNReal)^ε * CF^(p-1) * (b : ENNReal)^(2*β)
    * ((b : ENNReal)^2)^p * (θ : ENNReal)^p * (𝒯.card : ENNReal)^p := by
    unfold common
    calc
      ((a : ENNReal)^ε * CF^(p-1) * (b : ENNReal)^(2*β) * ((b : ENNReal)^2)^p * (θ : ENNReal)^p
        * (𝒯.card : ENNReal)^(p-1)) * (𝒯.card : ENNReal) =
      (a : ENNReal)^ε * CF^(p-1) * (b : ENNReal)^(2*β) * ((b : ENNReal)^2)^p * (θ : ENNReal)^p
        * ((𝒯.card : ENNReal)^(p-1) * (𝒯.card : ENNReal)) := by
        simp [mul_assoc]
      _ = (a : ENNReal)^ε * CF^(p-1) * (b : ENNReal)^(2*β) * ((b : ENNReal)^2)^p * (θ : ENNReal)^p
        * (𝒯.card : ENNReal)^p := by
        have h_rpow_add : (𝒯.card : ENNReal)^(p-1) * (𝒯.card : ENNReal) = (𝒯.card : ENNReal)^p := by
          calc
            (𝒯.card : ENNReal)^(p-1) * (𝒯.card : ENNReal) = (𝒯.card : ENNReal)^(p-1) * (𝒯.card : ENNReal)^(1 : ℝ) := by simp
            _ = (𝒯.card : ENNReal)^((p-1) + (1 : ℝ)) := by
              rw [ENNReal.rpow_add (p-1) (1 : ℝ) h𝒯_ne_zero h𝒯_ne_top]
            _ = (𝒯.card : ENNReal)^p := by ring
        rw [h_rpow_add]

  set B := (a : ENNReal)^ε * CF^(p-1) * (b : ENNReal)^(2*β) with hB
  set D := ((b : ENNReal)^2)^p with hD
  have hineq2' : (c3 : ENNReal) * B * D * (θ : ENNReal)^p * (𝒯.card : ENNReal)^p ≤ (K : ENNReal) * Uvol := by
    calc
      (c3 : ENNReal) * B * D * (θ : ENNReal)^p * (𝒯.card : ENNReal)^p =
        (c3 : ENNReal) * ((a : ENNReal)^ε * CF^(p-1) * (b : ENNReal)^(2*β) * ((b : ENNReal)^2)^p
          * (θ : ENNReal)^p * (𝒯.card : ENNReal)^p) := by
        simp [hB, hD, mul_assoc]
      _ = (c3 : ENNReal) * (common * (𝒯.card : ENNReal)) := by rw [hprod_simp]
      _ = (c3 : ENNReal) * common * (𝒯.card : ENNReal) := by simp [mul_assoc]
      _ ≤ (K : ENNReal) * Uvol := hineq2

  -- Step 3: derive ns ≤ Ccard^2 * M * θ * 𝒯.card in ℝ≥0, then lift to ENNReal
  have h_ns_bound_nn : (ns : ℝ≥0) ≤ Ccard ^ 2 * M * θ * (𝒯.card : ℝ≥0) := by
    have hNth' : (N : ℝ) ≤ Ccard * M * θ := by exact_mod_cast hNth
    have hcard' : (ns : ℝ) ≤ Ccard * (N : ℝ) * (𝒯.card : ℝ) := by exact_mod_cast hcard
    have htemp : (ns : ℝ) ≤ Ccard ^ 2 * M * θ * (𝒯.card : ℝ) := by
      calc
        (ns : ℝ) ≤ (Ccard : ℝ) * (N : ℝ) * (𝒯.card : ℝ) := hcard'
        _ = (Ccard : ℝ) * (𝒯.card : ℝ) * (N : ℝ) := by ring
        _ ≤ (Ccard : ℝ) * (𝒯.card : ℝ) * ((Ccard : ℝ) * (M : ℝ) * (θ : ℝ)) :=
          mul_le_mul_of_nonneg_left hNth' (by positivity)
        _ = (Ccard : ℝ)^2 * (M : ℝ) * (θ : ℝ) * (𝒯.card : ℝ) := by ring
    exact_mod_cast htemp

  have h_ns_bound_enn : (ns : ENNReal) ≤ ((Ccard : ENNReal)^2) * (M : ENNReal) * (θ : ENNReal) * (𝒯.card : ENNReal) := by
    have h' : (ns : ENNReal) ≤ (Ccard ^ 2 * M * θ * (𝒯.card : ℝ≥0) : ENNReal) := by exact_mod_cast h_ns_bound_nn
    have h_expand : (Ccard ^ 2 * M * θ * (𝒯.card : ℝ≥0) : ENNReal) = ((Ccard : ENNReal)^2) * (M : ENNReal) * (θ : ENNReal) * (𝒯.card : ENNReal) := by
      push_cast
      simp [mul_assoc]
    rw [h_expand] at h'
    exact h'

  -- Step 4: key inequality (Ccard^2)^(-p) * M^(-p) * (ns)^p ≤ θ^p * (𝒯.card)^p
  have h_cancel_Ccard : ((Ccard : ENNReal)^2)^(-p) * ((Ccard : ENNReal)^2)^p = 1 := by
    calc
      ((Ccard : ENNReal)^2)^(-p) * ((Ccard : ENNReal)^2)^p = ((Ccard : ENNReal)^2)^((-p : ℝ) + (p : ℝ)) := by
        rw [ENNReal.rpow_add (-p) p hCcard_sq_ne_zero hCcard_sq_ne_top]
      _ = ((Ccard : ENNReal)^2)^(0 : ℝ) := by ring
      _ = 1 := by simp

  have h_cancel_M : (M : ENNReal)^(-p) * (M : ENNReal)^p = 1 := by
    calc
      (M : ENNReal)^(-p) * (M : ENNReal)^p = (M : ENNReal)^((-p : ℝ) + (p : ℝ)) := by
        rw [ENNReal.rpow_add (-p) p hM_ne_zero hM_ne_top]
      _ = (M : ENNReal)^(0 : ℝ) := by ring
      _ = 1 := by simp

  have h_key_ineq : ((Ccard : ENNReal)^2)^(-p) * (M : ENNReal)^(-p) * (ns : ENNReal)^p
    ≤ (θ : ENNReal)^p * (𝒯.card : ENNReal)^p := by
    have h_pow_ns : (ns : ENNReal)^p ≤ (((Ccard : ENNReal)^2) * (M : ENNReal) * (θ : ENNReal) * (𝒯.card : ENNReal))^p :=
      ENNReal.rpow_le_rpow h_ns_bound_enn hp_nonneg
    have h_mul_pow : (((Ccard : ENNReal)^2) * (M : ENNReal) * (θ : ENNReal) * (𝒯.card : ENNReal))^p =
      ((Ccard : ENNReal)^2)^p * (M : ENNReal)^p * (θ : ENNReal)^p * (𝒯.card : ENNReal)^p := by
      calc
        (((Ccard : ENNReal)^2) * (M : ENNReal) * (θ : ENNReal) * (𝒯.card : ENNReal))^p =
          ((((Ccard : ENNReal)^2) * (M : ENNReal) * (θ : ENNReal)) * (𝒯.card : ENNReal))^p := by ring
        _ = (((Ccard : ENNReal)^2) * (M : ENNReal) * (θ : ENNReal))^p * (𝒯.card : ENNReal)^p := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp_nonneg]
        _ = ((Ccard : ENNReal)^2)^p * (M : ENNReal)^p * (θ : ENNReal)^p * (𝒯.card : ENNReal)^p := by
          simp [ENNReal.mul_rpow_of_nonneg _ _ hp_nonneg, mul_assoc]
    have h_pow_ns' : (ns : ENNReal)^p ≤ ((Ccard : ENNReal)^2)^p * (M : ENNReal)^p * (θ : ENNReal)^p * (𝒯.card : ENNReal)^p := by
      calc
        (ns : ENNReal)^p ≤ (((Ccard : ENNReal)^2) * (M : ENNReal) * (θ : ENNReal) * (𝒯.card : ENNReal))^p := h_pow_ns
        _ = ((Ccard : ENNReal)^2)^p * (M : ENNReal)^p * (θ : ENNReal)^p * (𝒯.card : ENNReal)^p := h_mul_pow
    calc
      ((Ccard : ENNReal)^2)^(-p) * (M : ENNReal)^(-p) * (ns : ENNReal)^p =
        (((Ccard : ENNReal)^2)^(-p) * (M : ENNReal)^(-p)) * (ns : ENNReal)^p := by
        simp [mul_assoc]
      _ ≤ (((Ccard : ENNReal)^2)^(-p) * (M : ENNReal)^(-p)) * (((Ccard : ENNReal)^2)^p * (M : ENNReal)^p * (θ : ENNReal)^p * (𝒯.card : ENNReal)^p) :=
        mul_le_mul_left' h_pow_ns' (((Ccard : ENNReal)^2)^(-p) * (M : ENNReal)^(-p))
      _ = (((Ccard : ENNReal)^2)^(-p) * ((Ccard : ENNReal)^2)^p) * ((M : ENNReal)^(-p) * (M : ENNReal)^p) * (θ : ENNReal)^p * (𝒯.card : ENNReal)^p := by
        simp [mul_comm, mul_left_comm, mul_assoc]
      _ = 1 * 1 * (θ : ENNReal)^p * (𝒯.card : ENNReal)^p := by simp [h_cancel_Ccard, h_cancel_M]
      _ = (θ : ENNReal)^p * (𝒯.card : ENNReal)^p := by simp

  -- Step 5: assemble the final inequality
  have h_mul_pow_simp : ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal)) ^ p =
    (M : ENNReal)^(-p) * ((b : ENNReal) ^ 2) ^ p * (ns : ENNReal) ^ p := by
    calc
      ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal)) ^ p =
        (((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2) * (ns : ENNReal)) ^ p := by
        simp [mul_assoc]
      _ = ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2) ^ p * (ns : ENNReal) ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp_nonneg]
      _ = ((M : ENNReal)⁻¹)^p * ((b : ENNReal) ^ 2) ^ p * (ns : ENNReal) ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp_nonneg, mul_assoc]
      _ = (M : ENNReal)^(-p) * ((b : ENNReal) ^ 2) ^ p * (ns : ENNReal) ^ p := by
        simp [ENNReal.inv_rpow, ENNReal.rpow_neg]

  have hX : (c3 : ENNReal) / (K : ENNReal) * B * D * ((Ccard : ENNReal)^2)^(-p) * (M : ENNReal)^(-p) * (ns : ENNReal)^p
    ≤ (c3 : ENNReal) / (K : ENNReal) * B * D * ((θ : ENNReal)^p * (𝒯.card : ENNReal)^p) := by
    calc
      (c3 : ENNReal) / (K : ENNReal) * B * D * ((Ccard : ENNReal)^2)^(-p) * (M : ENNReal)^(-p) * (ns : ENNReal)^p =
        ((c3 : ENNReal) / (K : ENNReal) * B * D) * (((Ccard : ENNReal)^2)^(-p) * (M : ENNReal)^(-p) * (ns : ENNReal)^p) := by
        simp [mul_assoc]
      _ ≤ ((c3 : ENNReal) / (K : ENNReal) * B * D) * ((θ : ENNReal)^p * (𝒯.card : ENNReal)^p) :=
        mul_le_mul_left' h_key_ineq ((c3 : ENNReal) / (K : ENNReal) * B * D)
      _ = (c3 : ENNReal) / (K : ENNReal) * B * D * ((θ : ENNReal)^p * (𝒯.card : ENNReal)^p) := by
        simp [mul_assoc]

  have h_goal_rewrite : (c3 : ENNReal) / (K : ENNReal) * ((Ccard : ENNReal) ^ 2) ^ (-(β / 2)) * (a : ENNReal) ^ ε
      * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
      * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal)) ^ (β / 2) =
    (c3 : ENNReal) / (K : ENNReal) * ((Ccard : ENNReal)^2)^(-p) * (a : ENNReal)^ε * CF^(p-1) * (b : ENNReal)^(2*β)
      * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal))^p := by
    simp [hp]

  rw [h_goal_rewrite]
  calc
    (c3 : ENNReal) / (K : ENNReal) * ((Ccard : ENNReal)^2)^(-p) * (a : ENNReal)^ε * CF^(p-1) * (b : ENNReal)^(2*β)
      * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal))^p
    = (c3 : ENNReal) / (K : ENNReal) * ((Ccard : ENNReal)^2)^(-p) * B * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal))^p := by
      simp [hB, hp, mul_assoc]
    _ = (c3 : ENNReal) / (K : ENNReal) * B * ((Ccard : ENNReal)^2)^(-p) * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (ns : ENNReal))^p := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ = (c3 : ENNReal) / (K : ENNReal) * B * ((Ccard : ENNReal)^2)^(-p) * (M : ENNReal)^(-p) * ((b : ENNReal) ^ 2) ^ p * (ns : ENNReal) ^ p := by
      rw [h_mul_pow_simp]
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ = (c3 : ENNReal) / (K : ENNReal) * B * D * ((Ccard : ENNReal)^2)^(-p) * (M : ENNReal)^(-p) * (ns : ENNReal) ^ p := by
      simp [hD, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ (c3 : ENNReal) / (K : ENNReal) * B * D * ((θ : ENNReal)^p * (𝒯.card : ENNReal)^p) := hX
    _ = (K : ENNReal)⁻¹ * ((c3 : ENNReal) * B * D * (θ : ENNReal)^p * (𝒯.card : ENNReal)^p) := by
      simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    _ ≤ (K : ENNReal)⁻¹ * ((K : ENNReal) * Uvol) :=
      mul_le_mul_left' hineq2' (K : ENNReal)⁻¹
    _ = Uvol := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hK_ne_zero hK_ne_top, one_mul]

/-! ### The retired lossless plank reduction (`NoEtaLoss`)

The declaration `Kakeya.plankReductionForFrostmanEstimateNoEtaLoss` that used to sit here has been
**deleted**. It was wrong twice over, and both defects are corrections to the paper's presentation
rather than to its mathematics.

* Its non-concentration hypothesis was the paper's *aligned* count `|{j : P_j ⊆ (P_i)_θ}| ≤ M θ`,
  whereas the representative/fibre geometry of GWZ Lemma 6.13 only ever controls a **fixed
  dilation** of the thickening. The two are not interchangeable: the essentially distinct
  counterexample recorded with `Kakeya.plankReductionForFrostmanEstimate`
  (`Kakeya/DimensionThree/Plank/FrostmanPlankReduction.lean`) satisfies the aligned count at every scale
  with the least admissible `M = b/a`, while its dilated count is `(φ b / 2a)^2`, unbounded relative
  to `M φ`.
* Its conclusions were lossless. The honest construction does not supply them:
  `Kakeya.redPlankTube_finalAssembly` delivers every clause with an `a ^ ε` factor, so running it at
  `ε := η` costs one further power of `a ^ η` per clause.

The live path is `Kakeya.plankReductionForFrostmanEstimate`, which takes the dilated hypothesis and
records the honest losses `c2 · a ^ (6η)`, `Ccard · a ^ (-3η)`, `Cloc · (CF · a ^ (-3η))` and
`c3 · a ^ (2η)`. They are paid for out of the `a ^ ε` budget by `Kakeya.etaBudgetAbsorb`, and the
conclusion of GWZ Lemma 6.4 is unchanged.

The retired docstring of the deleted interface is kept below. -/

/-! **Plank reduction in the form consumed by GWZ Lemma 6.4** — the downstream *bridge* interface
between GWZ 6.13 (`Kakeya.redPlankTube`) and GWZ Lemma 6.4. It replaces the earlier
`Plank.plankReductionUniform`, which was unusable: its `β` was unused and it silently dropped the
high-multiplicity and small-scale hypotheses that 6.13 requires.

This statement keeps the loss constants `c2, c3, Ccard` absolute (quantified before `η` and the
configuration, which is what lets GWZ Lemma 6.4 absorb them into `a ^ ε`), and exposes every
controlled loss of the reduction: the representative dilation `cThk`, the controlled slab-membership
losses `Cset`, `Cang`, the local Frostman transfer loss `Cloc`, and the slab-fibre loss `Cfib`.

Compared with the old statement it *adds* the hypothesis that is genuinely needed, namely high
multiplicity at the plank scale, `a ^ (-η) ≤ μ(PS, Y)`.

## This is **not** a purely formal specialisation of `Kakeya.redPlankTube`

The public statement of GWZ 6.13 now reads

`∀ η ε > 0, ∀ (C₀, Ncard), ∃ C ≥ 1, ∀ configuration, ∃ witnesses, …`,

with *every* quantitative loss expressed through the two uniform quantities `C⁻¹ · δ ^ ε`
(retained fractions, density lower bounds) and `C · δ ^ (-ε)` (comparability, dilation,
multiplicity loss). It would be invoked here with the technical scale `δ := a`; the remaining
hypotheses it needs (`a < 1`, `2 ≤ a ^ (-η)`, and a polynomial bound on `|s|`) can be supplied from
`b ≤ b₀` and from essential distinctness of planks in a bounded ball, which is why `b₀` is part of
the conclusion.

But the output below cannot be obtained by destructing an arbitrary witness of that public
statement, and no step here pretends otherwise. There are two independent obstructions.

*Shape of the constants.* The bridge must hand `Plank.SlabFibreGeometry`,
`Plank.frostmanThickenedSlabFibre` and `Plank.normaliseSlabFamilyToTubes` genuinely **absolute**
losses `cThk, Cset, Cang, Cloc, Cfib`, fixed before `η`, before `b₀` and before the configuration —
that is exactly what lets GWZ Lemma 6.4 absorb them into `a ^ ε` by shrinking `b₀`. Public 6.13
delivers instead the *scale-dependent* controlled losses `C · δ ^ (-ε)`. Those are the right uniform
losses for 6.13 itself, but they are not δ-independent, so they cannot be substituted for the
absolute constants without weakening this bridge. Conversely, replacing the bridge's absolute
constants by `C · a ^ (-ε)` would push an `a ^ (-ε)` into the per-slab Frostman clause, which GWZ
Lemma 6.4 cannot absorb at the point where it is used.

*Missing data.* Even ignoring the constants, the public statement does **not** give
`𝒯 = s'.image repr`, does **not** relate `Yθ` to the representative prisms, gives no ball containing
a representative, gives no representative-level slab geometry, and says nothing about the Frostman
constant of a representative fibre. Pruning an arbitrary public `𝒯` after the fact would also destroy
the per-slab fullness.

For these reasons the two declarations deliberately do **not** share a formal call: forcing one would
either weaken this bridge or invent geometric data that 6.13 does not produce. They are expected to
share their *internal* construction (the maximal essentially-distinct selection, the dyadic
pigeonhole and the typical-angle slab clustering) once that construction is formalized; at that point
the natural refactor is a single internal theorem returning a `Plank.ThickenedRepr` together with a
`Plank.SlabAssignment`, from which both the `C · δ ^ (-ε)`-controlled public statement and the
absolute-constant bridge are projections.

The interface is therefore stated over the **internal** construction, so that these data are
constructional rather than assumed:

* the refinement `s' ⊆ s` and the representative map come from a genuine
  `Plank.ThickenedRepr s' (fun i ↦ (V i).toPrism3D) θ hθ1 cThk` (`R`); a representative map survives
  a refinement via `Plank.ThickenedRepr.restrict`;
* the **active ensemble is `R.indexSet`**, which is *definitionally* `s'.image R.repr` — the image of
  the refined family under the representative map, not a pruned copy of a larger finset. Its pairwise
  essential distinctness is then a theorem (`Plank.ThickenedRepr.indexSet_pairwise`) rather than a
  hypothesis, and so is the fact that every active representative is assigned a used slab
  (`Plank.SlabAssignment.slabOf_mem_of_mem_indexSet`);
* the slab decomposition is a genuine
  `Plank.SlabAssignment s' (fun i ↦ (V i).toPrism3D) θ hθ1 R.repr Cset Cang` (`SA`), so the slab index
  type is `Slab θ hθ1` itself and `𝒮 = SA.used`;
* the per-slab Frostman clause is `Plank.frostmanThickenedSlabFibre` applied to this ensemble, and it
  carries that lemma's loss `Cloc` — `Cloc * CF` is never rewritten to `CF`.

## The shading carrier

The remaining honesty point is the shading. What 6.13 controls is
`(P i).carrier ⊆ ((Qθ (repr i)).dilation cThk).carrier`, so a shading body assembled from a fibre's
planks is carried by a *dilation* of the representative, never by the representative itself. The
conclusion therefore states the internal invariant explicitly:

`∀ Q ∈ R.indexSet, (Yθ Q).carrier = (Q.dilation Cfib).carrier`,

which is exactly the (repaired) `Plank.SlabFibreGeometry.shade_body` field. The undilated `Q` remains
the geometric object — it is the one that is pairwise essentially distinct — and nothing claims that
the dilated bodies are. The fixed volume/fullness/normalisation loss of this dilation is absorbed by
`Cfib`, which is quantified before `Closs` in `Plank.normaliseSlabFamilyToTubes` and before `K` in
`Plank.frostmanSlabUnionVolumeLowerBound`.

## Construction data

The proof constructs `s'`, `R`, `SA`, `N` and `Yθ` from the internal steps of GWZ 6.13: maximal
essentially-distinct selection, dyadic pigeonholing for constant fibre size, typical-angle slab
clustering, and the thickened-shading assembly.

Relative to the public 6.13 interface, the additional internal data used here are:
(i) the `Plank.ThickenedRepr` and `Plank.SlabAssignment` records themselves, rather than
the bare maps `Qθ`, `repr`, `slabOf` that the public statement returns; (ii) the identification of
the active ensemble with `R.indexSet`; (iii) the shading `Yθ` carried by `Q.dilation Cfib` for each
active representative; (iv) the representative-level slab geometry
(`Plank.SlabFibreGeometry`: controlled boundedness, controlled slab containment, thickness
comparability and tangency); (v) the local Frostman transfer with its loss `Cloc`; and (vi) the
upgrade of the controlled losses from the scale-dependent `C · a ^ (-ε)` to absolute constants.
Sorried bridge interface.

Its clauses omit the `η`-losses that the same reduction carries in
`Kakeya.plankReductionForFrostmanEstimate` (`Kakeya/DimensionThree/Plank/FrostmanPlankReduction.lean`),
which derives them from GWZ 6.13 and records `a ^ (-(3 * η))`, `c2 * a ^ (6 * η)` and
`a ^ (2 * η)` instead. The two statements are therefore *not* interchangeable; the honest one is the
public bridge, and this weaker local form is only what `FrostmanEstimate.plankVolumeLowerBound`
below is currently written against. -/

/-- **Elementary mass-versus-multiplicity input.** If the total shaded mass of a family dominates
`μ₀ * L` and the multiplicity of the family is at most `μ₀`, then the shading union has volume at
least `L`.

This is the only elementary ingredient the low-multiplicity branch of GWZ Lemma 6.4 needs, and it is
a direct consequence of the identity
`ShadedBody.sum_shade_eq_multiplicity_mul_union : ∑ i ∈ s, |Y i| = μ(s, Y) * |U(s, Y)|`, which is
division-free and already handles the degenerate values `0` and `⊤`. The hypotheses `μ₀ ≠ 0` and
`μ₀ ≠ ⊤` are what make the final cancellation of `μ₀` legitimate in `ENNReal`.

It replaces the earlier `Kakeya.lowMultiplicityPlankVolumeLowerBound`, which was **false**: that
statement asserted the full Lemma 6.4 lower bound in the low-multiplicity regime for arbitrary
`M ≥ 1` and `CF ≥ 1` while using neither the plank-concentration nor the Frostman hypothesis. For
`β = 1`, a singleton family with full shading and `M = CF = 1`, the plank volume is `8ab`
(`Prism3D.volume_carrier`) whereas the claimed target has the scale `8 a ^ ε b ³`, so for `ε < 1`,
fixed `b > 0` and small enough `a` the claimed inequality fails. -/
theorem le_volume_iUnion_of_multiplicity_le {ι : Type*} (s : Finset ι)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) {μ₀ L : ENNReal}
    (hμ₀0 : μ₀ ≠ 0) (hμ₀top : μ₀ ≠ ⊤)
    (hmass : μ₀ * L ≤ ∑ i ∈ s, volume (Y i).shade)
    (hmult : ShadedBody.multiplicity s Y ≤ μ₀) :
    L ≤ volume (⋃ i ∈ s, (Y i).shade) := by
  have hsum : ∑ i ∈ s, volume (Y i).shade = ShadedBody.multiplicity s Y * volume (⋃ i ∈ s, (Y i).shade) :=
    ShadedBody.sum_shade_eq_multiplicity_mul_union s Y
  have hmul : μ₀ * L ≤ ShadedBody.multiplicity s Y * volume (⋃ i ∈ s, (Y i).shade) := by
    calc
      μ₀ * L ≤ ∑ i ∈ s, volume (Y i).shade := hmass
      _ = ShadedBody.multiplicity s Y * volume (⋃ i ∈ s, (Y i).shade) := hsum
  have hμ0_mul : μ₀ * L ≤ μ₀ * volume (⋃ i ∈ s, (Y i).shade) := by
    calc
      μ₀ * L ≤ ShadedBody.multiplicity s Y * volume (⋃ i ∈ s, (Y i).shade) := hmul
      _ ≤ μ₀ * volume (⋃ i ∈ s, (Y i).shade) := mul_le_mul_right' hmult _
  have hμ0_mul' : L * μ₀ ≤ volume (⋃ i ∈ s, (Y i).shade) * μ₀ := by
    simpa [mul_comm] using hμ0_mul
  exact (ENNReal.mul_le_mul_iff_left hμ₀0 hμ₀top).mp hμ0_mul'

/-- **Absorbing a fixed finite constant into a small `b₀`.** For any positive exponent `p` and any
finite `C`, there is `b₀ > 0` with `C · b ^ p ≤ 1` for every `b ≤ b₀`. Used to absorb the fixed
unit-ball constant of the low-multiplicity branch of GWZ Lemma 6.4. -/
theorem exists_b₀_rpow_absorb {p : ℝ} (hp : 0 < p) {C : ENNReal} (hC : C ≠ ⊤) :
    ∃ b₀ : ℝ≥0, 0 < b₀ ∧ ∀ b : ℝ≥0, b ≤ b₀ → C * (b : ENNReal) ^ p ≤ 1 := by
  set c := C.toNNReal with hc_def
  have hC_eq : C = (c : ENNReal) := by
    simpa [hc_def] using (ENNReal.coe_toNNReal hC).symm
  have h_sum_pos : 0 < c + 1 := by positivity
  set b₀ := ((c + 1)⁻¹) ^ (1 / p) with hb₀_def
  have hb₀_pos : 0 < b₀ := by
    dsimp [b₀]
    have h_inv_pos : 0 < (c + 1)⁻¹ := by
      have hpos : 0 < c + 1 := h_sum_pos
      exact inv_pos.mpr hpos
    exact NNReal.rpow_pos (p := 1 / p) h_inv_pos
  have hb₀_ne_zero : b₀ ≠ 0 := hb₀_pos.ne'
  refine ⟨b₀, hb₀_pos, ?_⟩
  intro b hb
  by_cases hb0 : b = 0
  · subst hb0; simp [ENNReal.zero_rpow_of_pos hp]
  · have hb0' : (b : ℝ≥0) ≠ 0 := hb0
    have hbp_le : b ^ p ≤ b₀ ^ p := NNReal.rpow_le_rpow (z := p) hb hp.le
    have hb₀_pow_nn : b₀ ^ p = (c + 1)⁻¹ := by
      calc
        b₀ ^ p = (((c + 1)⁻¹) ^ (1 / p : ℝ)) ^ p := rfl
        _ = ((c + 1)⁻¹ : ℝ≥0) ^ ((1 / p : ℝ) * p) := by rw [NNReal.rpow_mul (c + 1)⁻¹ (1 / p) p]
        _ = ((c + 1)⁻¹ : ℝ≥0) ^ (1 : ℝ) := by
          have h_exp : (1 / p : ℝ) * p = 1 := by
            field_simp [hp.ne']
          rw [h_exp]
        _ = (c + 1)⁻¹ := by simp
    have hineq_nn : c * (c + 1)⁻¹ ≤ 1 := by
      have hpos : (c + 1 : ℝ≥0) ≠ 0 := by positivity
      calc
        c * (c + 1)⁻¹ ≤ (c + 1) * (c + 1)⁻¹ := mul_le_mul_of_nonneg_right (by
          exact le_self_add) (by positivity)
        _ = 1 := by
          field_simp [hpos]
    calc
      C * (b : ENNReal) ^ p = (c : ENNReal) * ((b : ENNReal) ^ p) := by rw [hC_eq]
      _ = (c : ENNReal) * ((b ^ p : ℝ≥0) : ENNReal) := by rw [ENNReal.coe_rpow_of_ne_zero hb0' p]
      _ ≤ (c : ENNReal) * ((b₀ ^ p : ℝ≥0) : ENNReal) := by
        refine mul_le_mul_left' (ENNReal.coe_le_coe.mpr hbp_le) (c : ENNReal)
      _ = (c : ENNReal) * ((b₀ : ENNReal) ^ p) := by
        simp [ENNReal.coe_rpow_of_ne_zero hb₀_ne_zero p]
      _ = (c : ENNReal) * (((c + 1)⁻¹ : ℝ≥0) : ENNReal) := by
        rw [← ENNReal.coe_rpow_of_ne_zero hb₀_ne_zero p, hb₀_pow_nn]
      _ = ((c * (c + 1)⁻¹ : ℝ≥0) : ENNReal) := by
        simp [ENNReal.coe_mul]
      _ ≤ 1 := by exact_mod_cast hineq_nn

/-- **Concentration at the critical angle `θ = a / b` forces `M⁻¹ ≤ a / b`.**
Every plank is contained in its own `a/b`-thickening (`Plank.subset_thickened`, since
`a ≤ (a/b)·b`), so the count in the plank-concentration hypothesis at `θ = a/b` is at least one,
giving `1 ≤ M · (a/b)`.

This is the first of the two quantitative inputs that close the low-multiplicity branch of GWZ
Lemma 6.4: it converts the `M ^ (-β/2)` factor of the target lower bound into a positive power
of `a / b`. -/
theorem inv_le_div_of_plankConcentration {ι : Type*} {s : Finset ι} {a b : ℝ≥0}
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) (V : ι → ShadedPlank a b hab hb1)
    (hs : s.Nonempty) {M : ℝ≥0} (hM : 1 ≤ M)
    (hMth : ∀ i ∈ s, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
        (({j ∈ s | (V j).carrier ⊆
            (Plank.thickened (V i).toPrism3D θ hθ1).carrier}.card : ℝ≥0))
          ≤ M * θ) :
    M⁻¹ ≤ a / b := by
  -- Step 1: b ≠ 0 because 0 < a ≤ b
  have hb0 : b ≠ 0 := (ha.trans_le hab).ne'
  -- Step 2: set θ = a / b
  set θ := a / b with hθ_def
  -- Step 3: θ ≤ 1 (since a ≤ b)
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    -- a / b ≤ 1 because a ≤ b
    apply NNReal.div_le_of_le_mul
    simpa [one_mul] using hab
  -- Step 4: a ≤ θ * b = (a / b) * b = a
  have hθa : a ≤ θ * b := by
    dsimp [θ]
    have hcalc : (a / b) * b = a := by field_simp [hb0]
    calc
      a = (a / b) * b := by symm; exact hcalc
      _ = θ * b := rfl
      _ ≤ θ * b := le_rfl
  -- Step 5: pick i ∈ s
  obtain ⟨i, hi⟩ := hs
  -- Step 6: the plank (V i) is contained in its own θ-thickening
  have hsubset : (V i).carrier ⊆ (Plank.thickened (V i).toPrism3D θ hθ1).carrier := by
    have htemp : ((V i).toPrism3D.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        (Plank.thickened (V i).toPrism3D θ hθ1).carrier :=
      Plank.subset_thickened (V i).toPrism3D hθa hθ1
    simpa using htemp
  -- Step 7: F = {j ∈ s | (V j).carrier ⊆ (Plank.thickened (V i).toPrism3D θ hθ1).carrier}
  let F := Finset.filter (fun j => (V j).carrier ⊆
    (Plank.thickened (V i).toPrism3D θ hθ1).carrier) s
  have hi_mem : i ∈ F := by
    dsimp [F]
    exact Finset.mem_filter.mpr ⟨hi, hsubset⟩
  -- Step 8: F is nonempty, so its cardinality is at least 1
  have hcard1 : (1 : ℝ≥0) ≤ (F.card : ℝ≥0) := by
    have hcard_pos : 0 < F.card := Finset.card_pos.mpr ⟨i, hi_mem⟩
    have hcard_nat : 1 ≤ F.card := by omega
    exact_mod_cast hcard_nat
  -- Step 9: The hypotheses give (F.card : ℝ≥0) ≤ M * θ
  have hcard_bound : (F.card : ℝ≥0) ≤ M * θ :=
    hMth i hi θ (le_rfl) hθ1
  -- Step 10: Combine: (1 : ℝ≥0) ≤ (F.card : ℝ≥0) ≤ M * θ = M * (a / b)
  have h_one_le_Ma_div_b : (1 : ℝ≥0) ≤ M * (a / b) := by
    calc
      (1 : ℝ≥0) ≤ (F.card : ℝ≥0) := hcard1
      _ ≤ M * θ := hcard_bound
      _ = M * (a / b) := by dsimp [θ]
  -- Step 11: M ≠ 0 (since 1 ≤ M)
  have hM0 : M ≠ 0 := by
    have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hM
    exact hMpos.ne'
  -- Step 12: M⁻¹ ≤ a / b
  calc
    M⁻¹ = M⁻¹ * (1 : ℝ≥0) := by simp
    _ ≤ M⁻¹ * (M * (a / b)) := mul_le_mul_left' h_one_le_Ma_div_b (M⁻¹ : ℝ≥0)
    _ = (M⁻¹ * M) * (a / b) := by ring
    _ = (1 : ℝ≥0) * (a / b) := by simp [hM0]
    _ = a / b := by simp

/-- **The lower bound on an admissible Frostman constant.** Testing the Frostman hypothesis on one
plank of the family — a legitimate convex test body, since the planks lie in the unit ball — gives
density at least `1` there, hence `1 ≤ CF · Δ(PS, B₁)`. Multiplying by `|B₁|` and using
`Kakeya.sum_volume_eq_densityIn_mul_volume'` together with `Prism3D.volume_carrier` turns this into
the quantitative statement that the *fixed* unit-ball volume is at most `CF · |s| · 8ab`.

Equivalently `CF ^ (β/2 - 1) ≤ Cball · (|s|·a·b) ^ (1 - β/2)`: any admissible Frostman constant is
bounded below by a quantity that shrinks with the total plank mass. This is the input the earlier
analysis of the low-multiplicity branch omitted (it used only `CF ^ (β/2 - 1) ≤ 1`). -/
theorem volume_plankWindow_le_of_isFrostmanIn {ι : Type*} {s : Finset ι} {a b : ℝ≥0}
    {hab : a ≤ b} {hb1 : b ≤ 1} (V : ι → ShadedPlank a b hab hb1)
    (ha : 0 < a) (hs : s.Nonempty) {CF : ENNReal}
    (hVball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ))
    (hFrost : IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) plankWindow CF) :
    volume (plankWindow).carrier
      ≤ CF * ((s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) := by
  set W := fun i : ι => (V i).toConvexSpaceBody with hW
  obtain ⟨i, hi⟩ := hs
  have hWiPW' : ∀ j ∈ s, W j ≤ plankWindow := by
    intro j hj
    intro x hx
    have hxV : x ∈ (V j).carrier := hx
    have hsub : (V j).carrier ⊆ (plankWindow : Set (EuclideanSpace ℝ (Fin 3))) :=
      calc
        (V j).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ) := hVball j hj
        _ = (plankWindow : Set (EuclideanSpace ℝ (Fin 3))) := by
          unfold plankWindow
          rfl
    exact hsub hxV
  have hWiPW : W i ≤ plankWindow := hWiPW' i hi
  have hvol_i : volume (W i).carrier = 8 * (a : ENNReal) * (b : ENNReal) := by
    calc
      volume (W i).carrier = volume ((V i).carrier) := by simp [hW]
      _ = volume ((V i).toPrism3D).carrier := rfl
      _ = 8 * (a : ENNReal) * (b : ENNReal) * (1 : ENNReal) :=
        Prism3D.volume_carrier (V i).toPrism3D
      _ = 8 * (a : ENNReal) * (b : ENNReal) := by simp
  have hvol_j (j : ι) (hj : j ∈ s) : volume (W j).carrier = 8 * (a : ENNReal) * (b : ENNReal) := by
    calc
      volume (W j).carrier = volume ((V j).carrier) := by simp [hW]
      _ = volume ((V j).toPrism3D).carrier := rfl
      _ = 8 * (a : ENNReal) * (b : ENNReal) * (1 : ENNReal) :=
        Prism3D.volume_carrier (V j).toPrism3D
      _ = 8 * (a : ENNReal) * (b : ENNReal) := by simp
  have hvol_i_pos : 0 < volume (W i).carrier := by
    have hpos : 0 < volume ((V i).toPrism3D).carrier :=
      Prism3D.volume_pos_of_pos (V i).toPrism3D ha
    simpa [hW] using hpos
  have hvol_i_ne_zero : volume (W i).carrier ≠ 0 := by exact ne_of_gt hvol_i_pos
  have hvol_i_ne_top : volume (W i).carrier ≠ ⊤ := by
    rw [hvol_i]
    -- 8 * (a : ENNReal) * (b : ENNReal) = (8 * (a : ENNReal)) * (b : ENNReal)
    refine ENNReal.mul_ne_top ?_ (ENNReal.coe_ne_top : (b : ENNReal) ≠ ⊤)
    refine ENNReal.mul_ne_top (by norm_num : (8 : ENNReal) ≠ ⊤) (ENNReal.coe_ne_top : (a : ENNReal) ≠ ⊤)
  have hdiv_self : volume (W i).carrier / volume (W i).carrier = 1 :=
    ENNReal.div_self hvol_i_ne_zero hvol_i_ne_top
  have h1_le_densityIn : 1 ≤ densityIn s W (W i) := by
    calc
      1 = volume (W i).carrier / volume (W i).carrier := by symm; exact hdiv_self
      _ ≤ densityIn s W (W i) := le_densityIn s W (W i) hi le_rfl
  have h_densityIn_ineq : densityIn s W (W i) ≤ CF * densityIn s W plankWindow :=
    hFrost (W i) hWiPW
  have h1_le_CF_densityPW : 1 ≤ CF * densityIn s W plankWindow := by
    calc
      1 ≤ densityIn s W (W i) := h1_le_densityIn
      _ ≤ CF * densityIn s W plankWindow := h_densityIn_ineq
  have hsum_eq : ∑ j ∈ s, volume (W j).carrier = densityIn s W plankWindow * volume plankWindow.carrier :=
    sum_volume_eq_densityIn_mul_volume' hWiPW'
  have hsum_vol : ∑ j ∈ s, volume (W j).carrier = (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by
    calc
      ∑ j ∈ s, volume (W j).carrier = ∑ j ∈ s, 8 * (a : ENNReal) * (b : ENNReal) :=
        Finset.sum_congr rfl hvol_j
      _ = (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by simp
  have h_eq : densityIn s W plankWindow * volume plankWindow.carrier
      = (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by
    calc
      densityIn s W plankWindow * volume plankWindow.carrier = ∑ j ∈ s, volume (W j).carrier := by
        symm; exact hsum_eq
      _ = (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := hsum_vol
  calc
    volume plankWindow.carrier = (1 : ENNReal) * volume plankWindow.carrier := by simp
    _ ≤ (CF * densityIn s W plankWindow) * volume plankWindow.carrier :=
      mul_le_mul_right' h1_le_CF_densityPW (volume plankWindow.carrier)
    _ = CF * (densityIn s W plankWindow * volume plankWindow.carrier) := by ring
    _ = CF * ((s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) := by rw [h_eq]

/-- **The scalar inequality of the low-multiplicity branch of GWZ Lemma 6.4.**
Writing `n = |s|`, `L` for the factor-`8` target lower bound and `massLB = a^η · (n · 8ab)` for the
lower bound on the total shaded mass supplied by the fullness hypothesis, this is exactly
`a ^ (-η) · L ≤ massLB`.

The proof combines the two quantitative inputs:

* `M⁻¹ ≤ a / b` (concentration at `θ = a/b`), which gives
  `(M⁻¹ b² n) ^ (β/2) ≤ (a b n) ^ (β/2)`;
* `Vb ≤ CF · n · 8ab` (Frostman), which gives, with `q = 1 - β/2 ≥ 0`,
  `CF ^ (β/2 - 1) ≤ (Vb ^ q)⁻¹ · (8 a b n) ^ q`.

Since `q + β/2 = 1`, the two powers of `a b n` recombine into a single factor `a b n`, and the whole
left-hand side collapses to a fixed multiple of `a ^ (ε - η) · b ^ (2β) · (a b n)`. Comparing with
`massLB = 8 · a ^ η · (a b n)` leaves `Cball · 8 ^ q · a ^ (ε - 2η) · b ^ (2β) ≤ 1`, which holds
because `2η ≤ ε` and `a ≤ 1` make `a ^ (ε - 2η) ≤ 1`, `q ≤ 1` makes `8 ^ q ≤ 8`, and `hb₀` absorbs
the rest into a small `b`. -/
theorem lowMultiplicityScalarBound {β ε η : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hη : 0 < η) (hεη : 2 * η ≤ ε)
    {a b : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    {n : ℕ} (hn : 0 < n) {M : ℝ≥0} (hM : 1 ≤ M) (hMab : M⁻¹ ≤ a / b)
    {CF : ENNReal} (hCF1 : 1 ≤ CF) (hCFtop : CF ≠ ⊤)
    {Vb : ENNReal} (hVb0 : Vb ≠ 0) (hVbtop : Vb ≠ ⊤)
    (hball : Vb ≤ CF * ((n : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))))
    (hb₀ : 8 * (Vb ^ (1 - β / 2))⁻¹ * (b : ENNReal) ^ (2 * β) ≤ 1) :
    (a : ENNReal) ^ (-η) *
        (8 * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
          * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (n : ENNReal)) ^ (β / 2))
      ≤ (a : ENNReal) ^ η * ((n : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) := by
  -- Basic nonzero/finite facts
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := by
    have hbpos : 0 < b := lt_of_lt_of_le ha hab
    exact hbpos.ne'
  have hn0 : (n : ℕ) ≠ 0 := by omega
  have hM0 : (M : ℝ≥0) ≠ 0 := by
    have hMpos : 0 < (M : ℝ≥0) := by
      have h1pos : 0 < (1 : ℝ≥0) := by norm_num
      exact h1pos.trans_le hM
    exact hMpos.ne'
  have hCF0 : CF ≠ 0 := by
    have hpos : (0 : ENNReal) < 1 := by norm_num
    have hCFpos : 0 < CF := hpos.trans_le hCF1
    exact hCFpos.ne'
  have ha_enn0 : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha0
  have ha_enn_top : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hb_enn0 : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hb0
  have hb_enn_top : (b : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hn_enn0 : (n : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (by exact_mod_cast hn0)
  have hn_enn_top : (n : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hM_enn0 : (M : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hM0
  have hM_enn_top : (M : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have ha1 : a ≤ 1 := le_trans hab hb1
  have ha1_enn : (a : ENNReal) ≤ 1 := by exact_mod_cast ha1

  -- q := 1 - β/2, so β/2 - 1 = -q and q + β/2 = 1
  set q := 1 - β / 2 with hq_def
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    nlinarith
  have hq_le_one : q ≤ 1 := by
    dsimp [q]
    nlinarith
  have hq_sum : q + β / 2 = 1 := by
    dsimp [q]
    ring
  have h_beta_div2_minus_one : β / 2 - 1 = -q := by
    dsimp [q]
    ring
  have h_beta_div2_nonneg : 0 ≤ β / 2 := by nlinarith
  have h_eps_minus_2eta_nonneg : 0 ≤ ε - 2 * η := by linarith

  -- Z := (a : ENNReal) * (b : ENNReal) * (n : ENNReal)
  set Z : ENNReal := (a : ENNReal) * (b : ENNReal) * (n : ENNReal) with hZ_def
  have hZ0 : Z ≠ 0 := mul_ne_zero (mul_ne_zero ha_enn0 hb_enn0) hn_enn0
  have hZ_top : Z ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ha_enn_top hb_enn_top) hn_enn_top
  have hZ_8Z : (n : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) = 8 * Z := by
    dsimp [Z]
    ring

  -- Step 1: (M⁻¹ * b^2 * n)^(β/2) ≤ Z^(β/2)
  have hXZ_nn : (M⁻¹ : ℝ≥0) * b ^ 2 * (n : ℝ≥0) ≤ a * b * (n : ℝ≥0) := by
    calc
      (M⁻¹ : ℝ≥0) * b ^ 2 * (n : ℝ≥0) = (M⁻¹ : ℝ≥0) * (b ^ 2 * (n : ℝ≥0)) := by ring
      _ ≤ (a / b) * (b ^ 2 * (n : ℝ≥0)) := mul_le_mul_of_nonneg_right hMab (by positivity)
      _ = (a / b) * b ^ 2 * (n : ℝ≥0) := by ring
      _ = a * b * (n : ℝ≥0) := by
        field_simp [hb0]
  have hXZ_enn : (M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (n : ENNReal) ≤ Z := by
    calc
      (M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (n : ENNReal) =
          ((M⁻¹ : ℝ≥0) : ENNReal) * ((b ^ 2 : ℝ≥0) : ENNReal) * ((n : ℝ≥0) : ENNReal) := by
        simp [ENNReal.coe_inv hM0]
      _ = (((M⁻¹ : ℝ≥0) * b ^ 2 * (n : ℝ≥0)) : ENNReal) := by simp
      _ ≤ ((a * b * (n : ℝ≥0)) : ENNReal) := by exact_mod_cast hXZ_nn
      _ = Z := by
        dsimp [Z]
  have h_step1 : ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (n : ENNReal)) ^ (β / 2) ≤ Z ^ (β / 2) :=
    ENNReal.rpow_le_rpow hXZ_enn h_beta_div2_nonneg

  -- Step 2: Frostman bound: CF^(β/2-1) ≤ (Vb^q)⁻¹ * (8 * Z^q)
  have hball_8Z : Vb ≤ CF * (8 * Z) := by
    calc
      Vb ≤ CF * ((n : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) := hball
      _ = CF * (8 * Z) := by rw [hZ_8Z]

  have hVbq_nonzero : Vb ^ q ≠ 0 := by
    intro hzero
    apply hVb0
    rcases ENNReal.rpow_eq_zero_iff.mp hzero with (⟨hVb0', hq_pos⟩ | ⟨hVbtop', hq_neg⟩)
    · exact hVb0'
    · exfalso; linarith
  have hVbq_notop : Vb ^ q ≠ ⊤ := by
    intro htop
    apply hVbtop
    rcases ENNReal.rpow_eq_top_iff.mp htop with (⟨hVb0', hq_neg⟩ | ⟨hVbtop', hq_pos⟩)
    · exfalso; linarith
    · exact hVbtop'

  have h_Vbq_rpow : Vb ^ q ≤ (CF * (8 * Z)) ^ q :=
    ENNReal.rpow_le_rpow hball_8Z hq_nonneg
  have h_CF_8Z_rpow : (CF * (8 * Z)) ^ q = CF ^ q * (8 * Z) ^ q :=
    ENNReal.mul_rpow_of_nonneg _ _ hq_nonneg
  have h_Vbq_rpow' : Vb ^ q ≤ CF ^ q * (8 * Z) ^ q :=
    calc
      Vb ^ q ≤ (CF * (8 * Z)) ^ q := h_Vbq_rpow
      _ = CF ^ q * (8 * Z) ^ q := h_CF_8Z_rpow

  have h_mul_inv1 : CF ^ (-q) * CF ^ q = 1 := by
    calc
      CF ^ (-q) * CF ^ q = CF ^ ((-q : ℝ) + q) := by
        rw [ENNReal.rpow_add (-q) q hCF0 hCFtop]
      _ = CF ^ (0 : ℝ) := by ring
      _ = 1 := by simp

  have h_CF_negq_Vbq : CF ^ (-q) * Vb ^ q ≤ (8 * Z) ^ q := by
    calc
      CF ^ (-q) * Vb ^ q ≤ CF ^ (-q) * (CF ^ q * (8 * Z) ^ q) :=
        mul_le_mul_left' h_Vbq_rpow' (CF ^ (-q))
      _ = (CF ^ (-q) * CF ^ q) * (8 * Z) ^ q := by ring
      _ = 1 * (8 * Z) ^ q := by rw [h_mul_inv1]
      _ = (8 * Z) ^ q := by simp

  have h_CF_negq_bound : CF ^ (-q) ≤ (Vb ^ q)⁻¹ * (8 * Z) ^ q := by
    calc
      CF ^ (-q) = CF ^ (-q) * (Vb ^ q * (Vb ^ q)⁻¹) := by
        simp [ENNReal.mul_inv_cancel hVbq_nonzero hVbq_notop]
      _ = (CF ^ (-q) * Vb ^ q) * (Vb ^ q)⁻¹ := by ring
      _ ≤ (8 * Z) ^ q * (Vb ^ q)⁻¹ := mul_le_mul_right' h_CF_negq_Vbq ((Vb ^ q)⁻¹)
      _ = (Vb ^ q)⁻¹ * (8 * Z) ^ q := by ring

  have h_8Z_rpow : (8 * Z) ^ q = (8 : ENNReal) ^ q * Z ^ q :=
    ENNReal.mul_rpow_of_nonneg _ _ hq_nonneg
  have h_8q_le_8 : (8 : ENNReal) ^ q ≤ (8 : ENNReal) := by
    calc
      (8 : ENNReal) ^ q ≤ (8 : ENNReal) ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ENNReal) ≤ (8 : ENNReal)) hq_le_one
      _ = (8 : ENNReal) := by simp

  have h_step2 : CF ^ (β / 2 - 1) ≤ (Vb ^ q)⁻¹ * (8 * Z ^ q) := by
    calc
      CF ^ (β / 2 - 1) = CF ^ (-q) := by rw [h_beta_div2_minus_one]
      _ ≤ (Vb ^ q)⁻¹ * (8 * Z) ^ q := h_CF_negq_bound
      _ = (Vb ^ q)⁻¹ * ((8 : ENNReal) ^ q * Z ^ q) := by rw [h_8Z_rpow]
      _ = ((Vb ^ q)⁻¹ * (8 : ENNReal) ^ q) * Z ^ q := by ring
      _ ≤ ((Vb ^ q)⁻¹ * (8 : ENNReal)) * Z ^ q :=
        mul_le_mul_right' (mul_le_mul_left' h_8q_le_8 ((Vb ^ q)⁻¹)) (Z ^ q)
      _ = (Vb ^ q)⁻¹ * (8 * Z ^ q) := by ring

  -- Step 3: Z^q * Z^(β/2) = Z^(q + β/2) = Z^1 = Z
  have h_step3 : Z ^ q * Z ^ (β / 2) = Z := by
    calc
      Z ^ q * Z ^ (β / 2) = Z ^ (q + β / 2) := by
        rw [ENNReal.rpow_add q (β / 2) hZ0 hZ_top]
      _ = Z ^ (1 : ℝ) := by rw [hq_sum]
      _ = Z := by simp

  -- Step 4: a^(-η) * a^ε ≤ a^η
  have h_a_pow_bound : (a : ENNReal) ^ (-η) * (a : ENNReal) ^ ε ≤ (a : ENNReal) ^ η := by
    calc
      (a : ENNReal) ^ (-η) * (a : ENNReal) ^ ε = (a : ENNReal) ^ ((-η : ℝ) + ε) := by
        rw [ENNReal.rpow_add (-η) ε ha_enn0 ha_enn_top]
      _ = (a : ENNReal) ^ (ε - η) := by ring
      _ = (a : ENNReal) ^ ((ε - 2 * η) + η) := by ring
      _ = (a : ENNReal) ^ (ε - 2 * η) * (a : ENNReal) ^ η := by
        rw [ENNReal.rpow_add (ε - 2 * η) η ha_enn0 ha_enn_top]
      _ ≤ 1 * (a : ENNReal) ^ η := by
        refine mul_le_mul ?_ (le_refl _) ?_ ?_
        · exact ENNReal.rpow_le_one ha1_enn h_eps_minus_2eta_nonneg
        · positivity
        · positivity
      _ = (a : ENNReal) ^ η := by simp

  -- Step 5: hb₀ in terms of q
  have hb₀_q : 8 * (Vb ^ q)⁻¹ * (b : ENNReal) ^ (2 * β) ≤ 1 := by
    simpa [hq_def] using hb₀

  -- Step 6: Assembly - the main inequality chain
  calc
    (a : ENNReal) ^ (-η) * (8 * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
        * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (n : ENNReal)) ^ (β / 2))
        = ((a : ENNReal) ^ (-η) * (8 * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)))
            * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (n : ENNReal)) ^ (β / 2) := by ring
    _ ≤ ((a : ENNReal) ^ (-η) * (8 * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β))) * Z ^ (β / 2) :=
      mul_le_mul_left' (c := Z ^ (β / 2)) h_step1 ((a : ENNReal) ^ (-η) * (8 * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)))
    _ = (a : ENNReal) ^ (-η) * (8 * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β) * Z ^ (β / 2)) := by ring
    _ = (a : ENNReal) ^ (-η) * ((8 * (a : ENNReal) ^ ε * (b : ENNReal) ^ (2 * β) * Z ^ (β / 2)) * CF ^ (β / 2 - 1)) := by ring
    _ ≤ (a : ENNReal) ^ (-η) * ((8 * (a : ENNReal) ^ ε * (b : ENNReal) ^ (2 * β) * Z ^ (β / 2)) * ((Vb ^ q)⁻¹ * (8 * Z ^ q))) := by
      have hinner : (8 * (a : ENNReal) ^ ε * (b : ENNReal) ^ (2 * β) * Z ^ (β / 2)) * CF ^ (β / 2 - 1) ≤
          (8 * (a : ENNReal) ^ ε * (b : ENNReal) ^ (2 * β) * Z ^ (β / 2)) * ((Vb ^ q)⁻¹ * (8 * Z ^ q)) :=
        mul_le_mul_left' h_step2 (8 * (a : ENNReal) ^ ε * (b : ENNReal) ^ (2 * β) * Z ^ (β / 2))
      exact mul_le_mul_left' hinner ((a : ENNReal) ^ (-η))
    _ = (a : ENNReal) ^ (-η) * (8 * (a : ENNReal) ^ ε * ((Vb ^ q)⁻¹ * (8 * Z ^ q)) * (b : ENNReal) ^ (2 * β) * Z ^ (β / 2)) := by ring
    _ = (a : ENNReal) ^ (-η) * (a : ENNReal) ^ ε * (8 * (Vb ^ q)⁻¹ * 8 * Z ^ q * (b : ENNReal) ^ (2 * β) * Z ^ (β / 2)) := by ring
    _ = ((a : ENNReal) ^ (-η) * (a : ENNReal) ^ ε) * (64 * (Vb ^ q)⁻¹ * (b : ENNReal) ^ (2 * β) * Z ^ q * Z ^ (β / 2)) := by ring
    _ = ((a : ENNReal) ^ (-η) * (a : ENNReal) ^ ε) * (64 * (Vb ^ q)⁻¹ * (b : ENNReal) ^ (2 * β) * (Z ^ q * Z ^ (β / 2))) := by ring
    _ = ((a : ENNReal) ^ (-η) * (a : ENNReal) ^ ε) * (64 * (Vb ^ q)⁻¹ * (b : ENNReal) ^ (2 * β) * Z) := by
      rw [h_step3]
    _ = ((a : ENNReal) ^ (-η) * (a : ENNReal) ^ ε) * ((8 * (Vb ^ q)⁻¹ * (b : ENNReal) ^ (2 * β)) * (8 * Z)) := by ring
    _ = (8 * (Vb ^ q)⁻¹ * (b : ENNReal) ^ (2 * β)) * (8 * (a : ENNReal) ^ (-η) * (a : ENNReal) ^ ε * Z) := by ring
    _ ≤ (8 * (Vb ^ q)⁻¹ * (b : ENNReal) ^ (2 * β)) * (8 * (a : ENNReal) ^ η * Z) := by
      refine mul_le_mul' ?_ ?_
      · rfl
      · calc
          8 * (a : ENNReal) ^ (-η) * (a : ENNReal) ^ ε * Z = (8 * Z) * ((a : ENNReal) ^ (-η) * (a : ENNReal) ^ ε) := by ring
          _ ≤ (8 * Z) * ((a : ENNReal) ^ η) := mul_le_mul_left' (c := (a : ENNReal) ^ η) h_a_pow_bound (8 * Z)
          _ = 8 * (a : ENNReal) ^ η * Z := by ring
    _ = ((8 * (Vb ^ q)⁻¹ * (b : ENNReal) ^ (2 * β)) * 8) * (a : ENNReal) ^ η * Z := by ring
    _ = (8 * (Vb ^ q)⁻¹ * (b : ENNReal) ^ (2 * β)) * (8 * (a : ENNReal) ^ η * Z) := by ring
    _ ≤ 1 * (8 * (a : ENNReal) ^ η * Z) := by
      refine mul_le_mul_right' ?_ _
      exact hb₀_q
    _ = (a : ENNReal) ^ η * (8 * Z) := by ring
    _ = (a : ENNReal) ^ η * ((n : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) := by
      rw [hZ_8Z]

/-- rpow of a nonzero finite base is nonzero. -/
private lemma rpow_ne_zero (x : ENNReal) (y : ℝ) (hx0 : x ≠ 0) (hx_top : x ≠ ⊤) : x ^ y ≠ 0 := by
  intro hz
  rw [ENNReal.rpow_eq_zero_iff] at hz
  rcases hz with (⟨h0, _⟩ | ⟨ht, _⟩) <;> [exact hx0 h0; exact hx_top ht]

/-- rpow of a nonzero finite base is not ⊤. -/
private lemma rpow_ne_top (x : ENNReal) (y : ℝ) (hx0 : x ≠ 0) (hx_top : x ≠ ⊤) : x ^ y ≠ ⊤ := by
  intro hz
  rw [ENNReal.rpow_eq_top_iff] at hz
  rcases hz with (⟨h0, _⟩ | ⟨ht, _⟩) <;> [exact hx0 h0; exact hx_top ht]

set_option maxHeartbeats 1000000 in
/-- **The master `η`-budget of GWZ Lemma 6.4.**

GWZ Lemma 6.13, as `Kakeya.plankReductionForFrostmanEstimate` delivers it, is *lossy*: its
cardinality comparison carries `a ^ (-3η)`, its local Frostman constant carries `a ^ (-3η)`, its
per-slab fullness carries `a ^ (6η)` and its slab-sum comparison carries `a ^ (2η)`. Feeding these
into `Kakeya.aggregateSlabVolume` — which is uniform in its constants, so the losses may simply be
absorbed into `Ccard`, `c3` and `CF` — produces the right-hand side below. This lemma is the single
place where the accumulated losses are paid for out of the `a ^ ε` budget.

Only three elementary facts are used, all for `0 < a ≤ 1`:

* `(a ^ (-3η)) ^ (β/2 - 1) = a ^ (3η (1 - β/2)) ≥ a ^ (3η)` — the Frostman loss, damped by
  `1 - β/2 ≤ 1`;
* `((Ccard · a ^ (-3η)) ^ 2) ^ (-β/2) = (Ccard ^ 2) ^ (-β/2) · a ^ (3ηβ) ≥ (Ccard ^ 2) ^ (-β/2)
  · a ^ (3η)` — the cardinality loss, damped by `β ≤ 1`;
* `c3 · a ^ (2η)` — the slab-sum loss.

Together they cost `a ^ (8η)`, and `8η ≤ ε/4` leaves `a ^ (3ε/4)` against the `a ^ (ε/2)` the
per-slab step supplies, so `8 · a ^ ε` fits once `a ^ (ε/4) ≤ cabs / 8`. No constant is optimised:
`8η ≤ ε/4` is a deliberately generous budget. -/
theorem etaBudgetAbsorb {β ε η : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1) (hε : 0 < ε)
    (hη : 0 < η) (hη8 : 8 * η ≤ ε / 4)
    {a : ℝ≥0} (ha : 0 < a) (ha1 : a ≤ 1)
    {Ccard c3 K : ℝ≥0} (hCcard : 1 ≤ Ccard) (hc3 : 0 < c3) (hK : 0 < K)
    (habs : a ^ (ε / 4) ≤ (c3 / K * ((Ccard : ℝ≥0) ^ 2) ^ (-(β / 2))) / 8)
    {CF : ENNReal} (hCF1 : 1 ≤ CF) (hCFtop : CF ≠ ⊤) :
    (8 : ENNReal) * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1)
      ≤ ((c3 * a ^ (2 * η) : ℝ≥0) : ENNReal) / (K : ENNReal)
        * ((((Ccard * a ^ (-(3 * η)) : ℝ≥0)) : ENNReal) ^ 2) ^ (-(β / 2))
        * (a : ENNReal) ^ (ε / 2)
        * (CF * (a : ENNReal) ^ (-(3 * η))) ^ (β / 2 - 1) := by
  -- Basic nonzero / finite facts
  have ha0 : a ≠ 0 := ha.ne'
  have ha_enn0 : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha0
  have ha_enn_top : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have ha1_enn : (a : ENNReal) ≤ 1 := by exact_mod_cast ha1
  have hCF0 : CF ≠ 0 := by
    have hpos : (0 : ENNReal) < 1 := by norm_num
    exact (hpos.trans_le hCF1).ne'
  have hCcard_enn0 : (Ccard : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (by
    have hCcard_pos : 0 < Ccard := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hCcard
    exact hCcard_pos.ne')
  have hCcard_enn_top : (Ccard : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCcard_sq_nn0 : ((Ccard : ℝ≥0) ^ 2) ≠ 0 := by
    have hCcard_pos : 0 < Ccard := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hCcard
    exact pow_ne_zero 2 hCcard_pos.ne'
  have hCcard_sq_enn0 : ((Ccard : ENNReal) ^ 2) ≠ 0 := pow_ne_zero 2 hCcard_enn0
  have hCcard_sq_enn_top : ((Ccard : ENNReal) ^ 2) ≠ ⊤ := ENNReal.pow_ne_top hCcard_enn_top
  -- rpow terms in a (finite, nonzero)
  have hY0 : (a : ENNReal) ^ (-(3 * η)) ≠ 0 := rpow_ne_zero (a : ENNReal) (-(3 * η)) ha_enn0 ha_enn_top
  have hYtop : (a : ENNReal) ^ (-(3 * η)) ≠ ⊤ := rpow_ne_top (a : ENNReal) (-(3 * η)) ha_enn0 ha_enn_top
  have hY6_0 : (a : ENNReal) ^ (-(6 * η)) ≠ 0 := rpow_ne_zero (a : ENNReal) (-(6 * η)) ha_enn0 ha_enn_top
  have hY6_top : (a : ENNReal) ^ (-(6 * η)) ≠ ⊤ := rpow_ne_top (a : ENNReal) (-(6 * η)) ha_enn0 ha_enn_top
  -- cabs
  set cabs : ℝ≥0 := c3 / K * ((Ccard : ℝ≥0) ^ 2) ^ (-(β / 2)) with hcabs_def
  have hcabsE : (cabs : ENNReal) = (c3 : ENNReal) / (K : ENNReal) * (((Ccard : ENNReal) ^ 2) ^ (-(β / 2) : ℝ)) := by
    calc
      (cabs : ENNReal) = (((c3 / K) * ((Ccard : ℝ≥0) ^ 2) ^ (-(β / 2)) : ℝ≥0) : ENNReal) := by
        exact congrArg (fun x : ℝ≥0 => (x : ENNReal)) hcabs_def
      _ = ((c3 / K : ℝ≥0) : ENNReal) * ((((Ccard : ℝ≥0) ^ 2) ^ (-(β / 2)) : ℝ≥0) : ENNReal) := by
        exact (ENNReal.coe_mul (c3 / K) (((Ccard : ℝ≥0) ^ 2) ^ (-(β / 2)))).symm
      _ = (c3 : ENNReal) / (K : ENNReal) * (((Ccard : ENNReal) ^ 2) ^ (-(β / 2))) := by
        rw [ENNReal.coe_div hK.ne']
        rw [ENNReal.coe_rpow_of_ne_zero hCcard_sq_nn0 (-(β / 2))]
        simp
  -- an a-rpow bound from habs
  have ha4' : a ^ (ε / 4) ≤ cabs / 8 := by
    simpa [← hcabs_def] using habs
  have h8a : (8 : ℝ≥0) * a ^ (ε / 4) ≤ cabs := by
    calc
      (8 : ℝ≥0) * a ^ (ε / 4) ≤ (8 : ℝ≥0) * (cabs / 8) := mul_le_mul_left' ha4' (8 : ℝ≥0)
      _ = cabs := by
        field_simp [show (8 : ℝ≥0) ≠ 0 from by norm_num]
  have h8a_enn : (8 : ENNReal) * (a : ENNReal) ^ (ε / 4) ≤ (cabs : ENNReal) := by
    calc
      (8 : ENNReal) * (a : ENNReal) ^ (ε / 4) = ((8 : ℝ≥0) : ENNReal) * ((a : ENNReal) ^ (ε / 4)) := by norm_num
      _ = ((8 : ℝ≥0) : ENNReal) * ((a ^ (ε / 4) : ℝ≥0) : ENNReal) := by
        simp [ENNReal.coe_rpow_of_ne_zero ha0 (ε / 4)]
      _ = ((8 : ℝ≥0) * (a ^ (ε / 4) : ℝ≥0) : ENNReal) := by norm_cast
      _ ≤ (cabs : ENNReal) := by exact_mod_cast h8a
  -- Step 5 damping inequalities
  have h_exp1 : 3 * η * β ≤ 3 * η := by nlinarith [hβle, hη, hβpos]
  have h3eta_le_beta : (a : ENNReal) ^ (3 * η) ≤ (a : ENNReal) ^ (3 * η * β) :=
    ENNReal.rpow_le_rpow_of_exponent_ge ha1_enn h_exp1
  have h_exp2 : 3 * η * (1 - β / 2) ≤ 3 * η := by nlinarith [hη, hβpos, hβle]
  have h3eta_le_onebeta : (a : ENNReal) ^ (3 * η) ≤ (a : ENNReal) ^ (3 * η * (1 - β / 2)) :=
    ENNReal.rpow_le_rpow_of_exponent_ge ha1_enn h_exp2
  have h_exp3 : ε / 4 + ε / 2 + 8 * η ≤ ε := by nlinarith [hη8]
  have h_eps_le : (a : ENNReal) ^ ε ≤ (a : ENNReal) ^ (ε / 4 + ε / 2 + 8 * η) :=
    ENNReal.rpow_le_rpow_of_exponent_ge ha1_enn h_exp3
  -- Recombination of powers of a
  have hsplit : (a : ENNReal) ^ (ε / 4 + ε / 2 + 8 * η) =
      (a : ENNReal) ^ (ε / 4) * (a : ENNReal) ^ (ε / 2) * (a : ENNReal) ^ (3 * η) * (a : ENNReal) ^ (3 * η) * (a : ENNReal) ^ (2 * η) := by
    rw [← ENNReal.rpow_add (ε / 4) (ε / 2) ha_enn0 ha_enn_top,
        ← ENNReal.rpow_add (ε / 4 + ε / 2) (3 * η) ha_enn0 ha_enn_top,
        ← ENNReal.rpow_add (ε / 4 + ε / 2 + 3 * η) (3 * η) ha_enn0 ha_enn_top,
        ← ENNReal.rpow_add (ε / 4 + ε / 2 + 3 * η + 3 * η) (2 * η) ha_enn0 ha_enn_top]
    congr 1
    ring
  -- Step 1/2: F1
  have hF1 : ((c3 * a ^ (2 * η) : ℝ≥0) : ENNReal) / (K : ENNReal) =
      (c3 : ENNReal) / (K : ENNReal) * (a : ENNReal) ^ (2 * η) := by
    calc
      ((c3 * a ^ (2 * η) : ℝ≥0) : ENNReal) / (K : ENNReal)
          = ((c3 : ENNReal) * (a : ENNReal) ^ (2 * η)) / (K : ENNReal) := by
            rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero ha0 (2 * η)]
      _ = ((c3 : ENNReal) * (K : ENNReal)⁻¹) * (a : ENNReal) ^ (2 * η) := by
            simp only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      _ = (c3 : ENNReal) / (K : ENNReal) * (a : ENNReal) ^ (2 * η) := by
            rw [div_eq_mul_inv]
  -- Step 3: F2
  have hm_exp : (-(3 * η)) * (2 : ℝ) = -(6 * η) := by ring
  have hm : ((a : ENNReal) ^ (-(3 * η))) ^ 2 = (a : ENNReal) ^ (-(6 * η)) := by
    rw [← ENNReal.rpow_mul_natCast (a : ENNReal) (-(3 * η)) 2]
    exact congrArg (fun e : ℝ => (a : ENNReal) ^ e) hm_exp
  have hA : ((Ccard * a ^ (-(3 * η)) : ℝ≥0) : ENNReal) ^ 2 =
      (Ccard : ENNReal) ^ 2 * (a : ENNReal) ^ (-(6 * η)) := by
    calc
      ((Ccard * a ^ (-(3 * η)) : ℝ≥0) : ENNReal) ^ 2
          = ((Ccard : ENNReal) * (a : ENNReal) ^ (-(3 * η))) ^ 2 := by
            rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero ha0 (-(3 * η))]
      _ = (Ccard : ENNReal) ^ 2 * ((a : ENNReal) ^ (-(3 * η))) ^ 2 := by
            rw [mul_pow]
      _ = (Ccard : ENNReal) ^ 2 * (a : ENNReal) ^ (-(6 * η)) := by
            rw [hm]
  have hF2_exp : (-(6 * η)) * (-(β / 2)) = 3 * η * β := by ring
  have hF2 : ((((Ccard * a ^ (-(3 * η)) : ℝ≥0)) : ENNReal) ^ 2) ^ (-(β / 2)) =
      ((Ccard : ENNReal) ^ 2) ^ (-(β / 2)) * (a : ENNReal) ^ (3 * η * β) := by
    calc
      ((((Ccard * a ^ (-(3 * η)) : ℝ≥0)) : ENNReal) ^ 2) ^ (-(β / 2))
          = ((Ccard : ENNReal) ^ 2 * (a : ENNReal) ^ (-(6 * η))) ^ (-(β / 2)) := by rw [hA]
      _ = ((Ccard : ENNReal) ^ 2) ^ (-(β / 2)) * ((a : ENNReal) ^ (-(6 * η))) ^ (-(β / 2)) := by
            rw [mul_rpow_lemma ((Ccard : ENNReal) ^ 2) ((a : ENNReal) ^ (-(6 * η)))
              hCcard_sq_enn0 hCcard_sq_enn_top hY6_0 hY6_top (-(β / 2))]
      _ = ((Ccard : ENNReal) ^ 2) ^ (-(β / 2)) * (a : ENNReal) ^ ((-(6 * η)) * (-(β / 2))) := by
            rw [← ENNReal.rpow_mul (a : ENNReal) (-(6 * η)) (-(β / 2))]
      _ = ((Ccard : ENNReal) ^ 2) ^ (-(β / 2)) * (a : ENNReal) ^ (3 * η * β) := by
            rw [hF2_exp]
  -- Step 4: F4
  have hF4_exp : (-(3 * η)) * (β / 2 - 1) = 3 * η * (1 - β / 2) := by ring
  have hF4 : (CF * (a : ENNReal) ^ (-(3 * η))) ^ (β / 2 - 1) =
      CF ^ (β / 2 - 1) * (a : ENNReal) ^ (3 * η * (1 - β / 2)) := by
    calc
      (CF * (a : ENNReal) ^ (-(3 * η))) ^ (β / 2 - 1)
          = CF ^ (β / 2 - 1) * ((a : ENNReal) ^ (-(3 * η))) ^ (β / 2 - 1) := by
            rw [mul_rpow_lemma CF ((a : ENNReal) ^ (-(3 * η))) hCF0 hCFtop hY0 hYtop (β / 2 - 1)]
      _ = CF ^ (β / 2 - 1) * (a : ENNReal) ^ ((-(3 * η)) * (β / 2 - 1)) := by
            rw [← ENNReal.rpow_mul (a : ENNReal) (-(3 * η)) (β / 2 - 1)]
      _ = CF ^ (β / 2 - 1) * (a : ENNReal) ^ (3 * η * (1 - β / 2)) := by
            rw [hF4_exp]
  -- The RHS in canonical form
  have hRightside : ((c3 * a ^ (2 * η) : ℝ≥0) : ENNReal) / (K : ENNReal)
        * ((((Ccard * a ^ (-(3 * η)) : ℝ≥0)) : ENNReal) ^ 2) ^ (-(β / 2))
        * (a : ENNReal) ^ (ε / 2)
        * (CF * (a : ENNReal) ^ (-(3 * η))) ^ (β / 2 - 1)
      = (cabs : ENNReal) * (a : ENNReal) ^ (2 * η) * (a : ENNReal) ^ (3 * η * β)
          * (a : ENNReal) ^ (3 * η * (1 - β / 2)) * (a : ENNReal) ^ (ε / 2) * CF ^ (β / 2 - 1) := by
    calc
      ((c3 * a ^ (2 * η) : ℝ≥0) : ENNReal) / (K : ENNReal)
          * ((((Ccard * a ^ (-(3 * η)) : ℝ≥0)) : ENNReal) ^ 2) ^ (-(β / 2))
          * (a : ENNReal) ^ (ε / 2)
          * (CF * (a : ENNReal) ^ (-(3 * η))) ^ (β / 2 - 1)
          = ((c3 : ENNReal) / (K : ENNReal) * (a : ENNReal) ^ (2 * η))
              * (((Ccard : ENNReal) ^ 2) ^ (-(β / 2)) * (a : ENNReal) ^ (3 * η * β))
              * (a : ENNReal) ^ (ε / 2)
              * (CF ^ (β / 2 - 1) * (a : ENNReal) ^ (3 * η * (1 - β / 2))) := by
            rw [hF1, hF2, hF4]
      _ = ((c3 : ENNReal) / (K : ENNReal) * (((Ccard : ENNReal) ^ 2) ^ (-(β / 2))))
          * (a : ENNReal) ^ (2 * η) * (a : ENNReal) ^ (3 * η * β) * (a : ENNReal) ^ (3 * η * (1 - β / 2)) * (a : ENNReal) ^ (ε / 2) * CF ^ (β / 2 - 1) := by
            simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = (cabs : ENNReal) * (a : ENNReal) ^ (2 * η) * (a : ENNReal) ^ (3 * η * β)
          * (a : ENNReal) ^ (3 * η * (1 - β / 2)) * (a : ENNReal) ^ (ε / 2) * CF ^ (β / 2 - 1) := by
            rw [← hcabsE]
  -- Main chain
  calc
    (8 : ENNReal) * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1)
        ≤ (8 : ENNReal) * (a : ENNReal) ^ (ε / 4 + ε / 2 + 8 * η) * CF ^ (β / 2 - 1) := by
          gcongr
    _ = (8 : ENNReal) * (a : ENNReal) ^ (ε / 4) * (a : ENNReal) ^ (ε / 2) * (a : ENNReal) ^ (3 * η) * (a : ENNReal) ^ (3 * η) * (a : ENNReal) ^ (2 * η) * CF ^ (β / 2 - 1) := by
          rw [hsplit]
          simp only [mul_assoc, mul_comm, mul_left_comm]
    _ ≤ (cabs : ENNReal) * (a : ENNReal) ^ (ε / 2) * (a : ENNReal) ^ (3 * η) * (a : ENNReal) ^ (3 * η) * (a : ENNReal) ^ (2 * η) * CF ^ (β / 2 - 1) := by
          gcongr
    _ ≤ (cabs : ENNReal) * (a : ENNReal) ^ (ε / 2) * (a : ENNReal) ^ (3 * η * β) * (a : ENNReal) ^ (3 * η * (1 - β / 2)) * (a : ENNReal) ^ (2 * η) * CF ^ (β / 2 - 1) := by
          gcongr
    _ = ((c3 * a ^ (2 * η) : ℝ≥0) : ENNReal) / (K : ENNReal)
          * ((((Ccard * a ^ (-(3 * η)) : ℝ≥0)) : ENNReal) ^ 2) ^ (-(β / 2))
          * (a : ENNReal) ^ (ε / 2)
          * (CF * (a : ENNReal) ^ (-(3 * η))) ^ (β / 2 - 1) := by
          rw [hRightside]
          simp only [mul_assoc, mul_comm, mul_left_comm]

/-- **GWZ Lemma 6.4 (Frostman estimate for planks).**
Suppose the partial Frostman estimate `K_F(β)` holds. For every `ε > 0` there are `η > 0` and
`b₀ > 0` with the following property. Let `0 < a ≤ b ≤ b₀` and let `PS = (P i)_{i ∈ s}` be a finite
essentially distinct family of `a × b × 1` planks contained in `B₁`, with shading `Y` (each shaded
body being the corresponding plank) satisfying `λ(PS, Y) ≥ a ^ η`. Suppose there is `M ≥ 1` such
that for every `i ∈ s` and every `a / b ≤ θ ≤ 1` the number of planks contained in the thickened
plank `(P i)_θ` is at most `M · θ`. Then, writing `C_F(PS)` for the Frostman constant `CF`,
* the union volume satisfies
  `|U(PS, Y)| ≥ a ^ ε · C_F(PS) ^ (β/2 - 1) · b ^ (2β) · (M⁻¹ b² |s|) ^ (β/2)`, and
* the multiplicity satisfies
  `μ(PS, Y) ≤ a ^ (-ε) · C_F(PS) ^ (1 - β/2) · M ^ (β/2) · (a/b) · b ^ (-2β) · (b² |s|) ^ (1 - β/2)`.

The essential-distinctness hypothesis is not stated in the blueprint prose but is mathematically
necessary (and is used by the underlying plank-to-tube reduction `redPlankTube`).

## Structure of the proof

Write `L` for the factor-`8` target lower bound and `massLB := a ^ η · (|s| · 8ab)` for the lower
bound on the total shaded mass supplied by the fullness hypothesis together with
`Prism3D.volume_carrier` (this is `ShadedBody.coe_fullness_mul_le_sum_volume_shade`). The proof
splits on the *multiplicity threshold that the plank reduction needs*, namely `a ^ (-η)` — not on a
mass-based threshold:

* **reduction branch** `a ^ (-η) ≤ μ(PS, Y)`: this is exactly the high-multiplicity hypothesis of
  `Kakeya.plankReductionForFrostmanEstimate` (and hence of GWZ 6.13). The reduction produces a
  thickened-representative ensemble with a slab decomposition; `Plank.frostmanSlabUnionVolumeLowerBound`
  supplies the per-slab bound and `Kakeya.aggregateSlabVolume` sums it, after which
  `Kakeya.expAbsorbConstant` absorbs the fixed losses into `a ^ ε` by shrinking `b₀`.
* **elementary branch** `μ(PS, Y) < a ^ (-η)`: `Kakeya.le_volume_iUnion_of_multiplicity_le` — a
  consequence of the division-free identity `ShadedBody.sum_shade_eq_multiplicity_mul_union` —
  reduces the goal to the scalar inequality `a ^ (-η) · L ≤ ∑ᵢ |Y i|`, for which `massLB` suffices.

## Why the elementary branch closes

The residual scalar inequality `a ^ (-η) · L ≤ massLB` is `Kakeya.lowMultiplicityScalarBound`. Two
quantitative inputs make it true; using only `CF ^ (β/2 - 1) ≤ 1` is not enough, and that omission
is what previously made this step look impossible.

1. **Concentration at `θ = a / b`** (`Kakeya.inv_le_div_of_plankConcentration`). A plank lies inside
   its own `a/b`-thickening (`Plank.subset_thickened`), so the count in the concentration hypothesis
   is at least one and `1 ≤ M · (a/b)`, i.e. `M⁻¹ ≤ a / b`. Hence
   `(M⁻¹ b² |s|) ^ (β/2) ≤ (a b |s|) ^ (β/2)`.
2. **The Frostman lower bound** (`Kakeya.volume_closedUnitBall_le_of_isFrostmanIn`). Testing the
   Frostman hypothesis on one plank of the family gives density `≥ 1` there, hence
   `|B₁| ≤ CF · |s| · 8ab`. With `q = 1 - β/2` this reads
   `CF ^ (β/2 - 1) ≤ (|B₁| ^ q)⁻¹ · (8 a b |s|) ^ q`: an admissible Frostman constant cannot be small
   when the total plank mass is small.

Because `q + β/2 = 1`, the two powers of `a b |s|` recombine into a single factor `a b |s|`, and the
left-hand side collapses to a fixed multiple of `a ^ (ε - 2η) · b ^ (2β) · (a b |s|)`, to be compared
with `massLB = 8 · a ^ η · (a b |s|)`. Choosing the final exponent `η := min η_perSlab (ε / 8)` makes
`ε - 2η ≥ 3ε/4 > 0`, so `a ^ (ε - 2η) ≤ 1`, and `Kakeya.exists_b₀_rpow_absorb` shrinks `b₀` enough to
absorb the fixed unit-ball constant into `b ^ (2β)`. Shrinking `η` below the per-slab exponent is
harmless in the reduction branch: since `0 < a ≤ 1`, the fullness output with exponent `4η` is
*stronger* than the per-slab hypothesis with exponent `4 η_perSlab`
(`NNReal.rpow_le_rpow_of_exponent_ge`).

The containment hypothesis `hVball` is used only to certify that each plank is an admissible
Frostman test body for the reference window. It is stated against `Kakeya.plankWindowRadius` rather
than the paper's `B₁`, because a `Plank a b` is given by half-widths and so never fits in a ball of
radius `1`; see the note on `Kakeya.plankWindowRadius`. -/
theorem FrostmanEstimate.plankVolumeLowerBound.{u} {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β) :
    ∃ C_NC : ℝ≥0, 1 ≤ C_NC ∧
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0),
      ∀ {ι : Type u} (s : Finset ι) {a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
        (V : ι → ShadedPlank a b hab hb1),
        0 < a → b ≤ b₀ →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
        (s : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        a ^ η ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) →
        ∀ (M : ℝ≥0), 1 ≤ M →
        Plank.IsThickeningNonconcentrated s (fun i => (V i).toPrism3D) C_NC M →
        ∀ (CF : ENNReal), 1 ≤ CF → CF ≠ ⊤ →
          IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) plankWindow CF →
          8 * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
              * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (β / 2)
            ≤ volume (⋃ i ∈ s, (V i).shade) := by
  rcases plankReductionForFrostmanEstimate.{u} with
    ⟨c2, c3, Ccard, cThk, Cset, Cang, Cloc, Cfib, hc2, hc3, hCcard, hcThk, hCset, hCang, hCloc,
      hCfib, hred⟩
  refine ⟨Plank.ThickenedRepr.fibreDilation cThk,
    Plank.ThickenedRepr.one_le_fibreDilation hcThk, ?_⟩
  intro ε hε
  rcases Plank.frostmanSlabUnionVolumeLowerBound hβpos hβle hKF (ε/2) (by nlinarith) c2 hc2 Cfib hCfib
      Cloc hCloc
    with ⟨ηps, hηps, b₀ps, hb₀ps, K, hK, hps⟩
  obtain ⟨η, hη, hη_le_ps, hεη, hη8⟩ :
      ∃ η : ℝ, 0 < η ∧ 6 * η ≤ 4 * ηps ∧ 2 * η ≤ ε ∧ 8 * η ≤ ε / 4 := by
    refine ⟨min (ηps / 2) (ε / 32), lt_min (by linarith) (by linarith), ?_, ?_, ?_⟩
    · have h := min_le_left (ηps / 2) (ε / 32); linarith
    · have h := min_le_right (ηps / 2) (ε / 32); linarith
    · have h := min_le_right (ηps / 2) (ε / 32); linarith
  obtain ⟨b₀red, hb₀red, hredcfg⟩ := hred hη
  set cabs : ℝ≥0 := c3 / K * ((Ccard : ℝ≥0) ^ 2) ^ (-(β / 2)) with hcabs_def
  have hcabs : 0 < cabs := by
    dsimp [cabs]
    positivity
  obtain ⟨b₀abs, hb₀abs, habs⟩ :=
    Kakeya.exists_b₀_nnreal_absorb (cabs / 8) (by positivity)
      (show (0 : ℝ) < ε / 4 by linarith)
  set Vb : ENNReal := volume (plankWindow).carrier with hVb_def
  have hVb0 : Vb ≠ 0 := by
    rw [hVb_def]
    exact (Metric.measure_closedBall_pos volume 0
      (by norm_num [plankWindowRadius] : (0 : ℝ) < (plankWindowRadius : ℝ))).ne'
  have hVbtop : Vb ≠ ⊤ := (plankWindow).isCompact.measure_ne_top
  have hVbq0 : Vb ^ (1 - β / 2) ≠ 0 := by
    intro hzero
    apply hVb0
    have hpos : 0 < (1 : ℝ) - β / 2 := by nlinarith
    rcases ENNReal.rpow_eq_zero_iff.mp hzero with (⟨hVb0', hpos'⟩ | ⟨hVbtop', hneg⟩)
    · exact hVb0'
    · exfalso; linarith
  have hCballtop : (8 : ENNReal) * (Vb ^ (1 - β / 2))⁻¹ ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.inv_ne_top.mpr hVbq0)
  obtain ⟨b₀ball, hb₀ball, hballabs⟩ :=
    exists_b₀_rpow_absorb (show (0:ℝ) < 2 * β by linarith) hCballtop
  refine ⟨η, hη, min b₀ps (min b₀abs (min b₀red b₀ball)), ?_, ?_⟩
  · exact lt_min_iff.mpr ⟨hb₀ps, lt_min_iff.mpr ⟨hb₀abs, lt_min_iff.mpr ⟨hb₀red, hb₀ball⟩⟩⟩
  intro ι s a b hab hb1 V ha hbb₀ hVball hed hlam M hM hMth CF hCF1 hCFtop hFrost
  have hb_ps : b ≤ b₀ps :=
    hbb₀.trans (calc
      min b₀ps (min b₀abs (min b₀red b₀ball)) ≤ b₀ps := min_le_left _ _)
  have hb_abs : b ≤ b₀abs :=
    hbb₀.trans (calc
      min b₀ps (min b₀abs (min b₀red b₀ball)) ≤ min b₀abs (min b₀red b₀ball) := min_le_right _ _
      _ ≤ b₀abs := min_le_left _ _)
  have hb_red : b ≤ b₀red :=
    hbb₀.trans (calc
      min b₀ps (min b₀abs (min b₀red b₀ball)) ≤ min b₀abs (min b₀red b₀ball) := min_le_right _ _
      _ ≤ min b₀red b₀ball := min_le_right _ _
      _ ≤ b₀red := min_le_left _ _)
  have hb_ball : b ≤ b₀ball :=
    hbb₀.trans (calc
      min b₀ps (min b₀abs (min b₀red b₀ball)) ≤ min b₀abs (min b₀red b₀ball) := min_le_right _ _
      _ ≤ min b₀red b₀ball := min_le_right _ _
      _ ≤ b₀ball := min_le_right _ _)
  rcases s.eq_empty_or_nonempty with rfl | hs
  · -- empty case: s = ∅, so s.card = 0, thus the whole LHS = 0 and RHS = volume(∅) = 0
    have hzero : (0 : ENNReal) ^ (β / 2) = 0 :=
      ENNReal.zero_rpow_of_pos (by nlinarith : (0 : ℝ) < β / 2)
    simp [hzero]
  by_cases hhigh : (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
  · -- HIGH multiplicity branch: use the plank reduction
    obtain ⟨s', N, θ, hθ0, hθ1, R, SA, Yθ, hs'sub, hN1, hθa, hYcarrier, hNth, hcardTs, hfibNe, hfibGeom, hfull, hfrost, hagg⟩ :=
      hredcfg s ha hab hb1 hb_red V M CF hM hCF1 hCFtop hVball hed hlam hhigh hMth hFrost
    have hpart : ∀ Q, Q ∈ R.indexSet → SA.slabOf Q ∈ SA.used :=
      fun Q hQ => Plank.SlabAssignment.slabOf_mem_of_mem_indexSet R SA hQ
    have ha1' : a ≤ 1 := hab.trans hb1
    have hone_le_neg : ∀ γ : ℝ, 0 ≤ γ → (1 : ℝ≥0) ≤ a ^ (-γ) := by
      intro γ hγ
      simpa using NNReal.rpow_le_rpow_of_exponent_ge ha ha1' (show -γ ≤ (0 : ℝ) by linarith)
    have hone_le_negE : ∀ γ : ℝ, 0 ≤ γ → (1 : ENNReal) ≤ (a : ENNReal) ^ (-γ) := by
      intro γ hγ
      rw [← ENNReal.coe_rpow_of_ne_zero ha.ne']
      exact_mod_cast hone_le_neg γ hγ
    have h3η : (0 : ℝ) ≤ 3 * η := by linarith
    have hCcard_a : (1 : ℝ≥0) ≤ Ccard * a ^ (-(3 * η)) :=
      le_trans hCcard (le_mul_of_one_le_right zero_le (hone_le_neg _ h3η))
    have hc3_a : (0 : ℝ≥0) < c3 * a ^ (2 * η) := mul_pos hc3 (NNReal.rpow_pos ha)
    have hCF_a1 : (1 : ENNReal) ≤ CF * (a : ENNReal) ^ (-(3 * η)) := by
      calc (1 : ENNReal) = 1 * 1 := (mul_one 1).symm
        _ ≤ CF * (a : ENNReal) ^ (-(3 * η)) := by gcongr; exact hone_le_negE _ h3η
    have hCF_atop : CF * (a : ENNReal) ^ (-(3 * η)) ≠ ⊤ :=
      ENNReal.mul_ne_top hCFtop (by
        rw [← ENNReal.coe_rpow_of_ne_zero ha.ne']
        exact ENNReal.coe_ne_top)
    have h𝒯 : R.indexSet.Nonempty := by
      by_contra h𝒯_empty
      have h𝒯_card0 : (R.indexSet.card : ℝ≥0) = 0 := by
        have hcard0 : R.indexSet.card = 0 :=
          Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h𝒯_empty)
        simp [hcard0]
      have hcardTs' : (s.card : ℝ≥0) ≤ 0 := by
        calc
          (s.card : ℝ≥0) ≤ Ccard * a ^ (-(3 * η)) * (N : ℝ≥0) * (R.indexSet.card : ℝ≥0) := hcardTs
          _ = Ccard * a ^ (-(3 * η)) * (N : ℝ≥0) * 0 := by rw [h𝒯_card0]
          _ = 0 := by simp
      have hs_card_pos : 0 < (s.card : ℝ≥0) := by
        have hpos : 0 < s.card := Finset.card_pos.mpr hs
        exact_mod_cast hpos
      exact (ne_of_gt hs_card_pos) (le_antisymm hcardTs' zero_le)
    have hfull_ps : ∀ S ∈ SA.used, (c2 : ℝ≥0) * a ^ (4 * ηps)
        ≤ ShadedBody.fullness (R.indexSet.filter (fun Q => SA.slabOf Q = S)) Yθ := by
      intro S hS
      refine le_trans (mul_le_mul_left' ?_ c2) (hfull S hS)
      exact NNReal.rpow_le_rpow_of_exponent_ge ha ha1' hη_le_ps
    have hNth_a : (N : ℝ≥0) ≤ Ccard * a ^ (-(3 * η)) * M * θ := by
      refine le_trans hNth ?_
      gcongr
      exact le_mul_of_one_le_right zero_le (hone_le_neg _ h3η)
    have hperslab : ∀ S ∈ SA.used, (a : ENNReal) ^ (ε / 2)
        * (CF * (a : ENNReal) ^ (-(3 * η))) ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
        * ((b : ENNReal) ^ 2) ^ (β / 2) * (θ : ENNReal) ^ (β / 2)
        * (R.indexSet.card : ENNReal) ^ (β / 2 - 1)
        * ((R.indexSet.filter (fun t => SA.slabOf t = S)).card : ENNReal)
        ≤ (K : ENNReal)
          * volume (⋃ t ∈ R.indexSet.filter (fun t => SA.slabOf t = S), (Yθ t).shade) := by
      intro S hS
      exact hps ha hab hb_ps hb1 hθ0 hθ1 hθa Yθ R.indexSet
        (R.indexSet.filter (fun Q => SA.slabOf Q = S)) S (CF * (a : ENNReal) ^ (-(3 * η)))
        (Finset.filter_subset _ _) (hfibNe S hS) hCF_a1 hCF_atop (hfibGeom S hS) (hfull_ps S hS)
        (hfrost S hS)
    have hagg_a : ((c3 * a ^ (2 * η) : ℝ≥0) : ENNReal) * ∑ S ∈ SA.used,
        volume (⋃ t ∈ R.indexSet.filter (fun t => SA.slabOf t = S), (Yθ t).shade)
        ≤ volume (⋃ i ∈ s, (V i).shade) := by
      rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero ha.ne', mul_assoc]
      simpa [mul_assoc] using hagg
    have hAgg : ((c3 * a ^ (2 * η) : ℝ≥0) : ENNReal) / (K : ENNReal)
        * ((((Ccard * a ^ (-(3 * η)) : ℝ≥0)) : ENNReal) ^ 2) ^ (-(β / 2))
        * (a : ENNReal) ^ (ε / 2)
        * (CF * (a : ENNReal) ^ (-(3 * η))) ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
        * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (β / 2)
        ≤ volume (⋃ i ∈ s, (V i).shade) :=
      aggregateSlabVolume hβpos hβle (show (0 : ℝ) < ε / 2 by nlinarith) ha hab hb1 hθ0 hθ1 hN1 hM
        hCcard_a hK hc3_a hCF_a1 hCF_atop Yθ R.indexSet SA.slabOf SA.used s.card
        (volume (⋃ i ∈ s, (V i).shade)) h𝒯 hpart hNth_a hcardTs
        hperslab hagg_a
    set X := (b : ENNReal) ^ (2 * β)
      * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (β / 2) with hX
    have hbud := etaBudgetAbsorb hβpos hβle hε hη hη8 ha ha1' hCcard hc3 hK
      (habs a b hab hb_abs) hCF1 hCFtop
    calc
      8 * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
          * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (β / 2)
          = ((8 : ENNReal) * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1)) * X := by
        dsimp [X]; ring
      _ ≤ (((c3 * a ^ (2 * η) : ℝ≥0) : ENNReal) / (K : ENNReal)
            * ((((Ccard * a ^ (-(3 * η)) : ℝ≥0)) : ENNReal) ^ 2) ^ (-(β / 2))
            * (a : ENNReal) ^ (ε / 2)
            * (CF * (a : ENNReal) ^ (-(3 * η))) ^ (β / 2 - 1)) * X :=
        mul_le_mul_right' hbud X
      _ = ((c3 * a ^ (2 * η) : ℝ≥0) : ENNReal) / (K : ENNReal)
            * ((((Ccard * a ^ (-(3 * η)) : ℝ≥0)) : ENNReal) ^ 2) ^ (-(β / 2))
            * (a : ENNReal) ^ (ε / 2)
            * (CF * (a : ENNReal) ^ (-(3 * η))) ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
            * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (β / 2) := by
        dsimp [X]; ring
      _ ≤ volume (⋃ i ∈ s, (V i).shade) := hAgg
  · -- ELEMENTARY BRANCH (low multiplicity). Here `μ(PS, Y) ≤ a ^ (-η)`, so the
    -- mass-versus-multiplicity input `Kakeya.le_volume_iUnion_of_multiplicity_le` — a consequence of
    -- the division-free identity `ShadedBody.sum_shade_eq_multiplicity_mul_union` — reduces the goal
    -- to a single scalar inequality between the target and the total shaded mass.
    have hlow' : ShadedBody.multiplicity s (fun i => (V i).toShadedBody) < (a : ENNReal) ^ (-η) :=
      not_le.mp hhigh
    have hane : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha.ne'
    have hatop : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hpow0 : (a : ENNReal) ^ (-η) ≠ 0 := by
      simp [ENNReal.rpow_eq_zero_iff, hane, hatop, hη]
    have hpowtop : (a : ENNReal) ^ (-η) ≠ ⊤ := by
      simp [ENNReal.rpow_eq_top_iff, hane, hatop, hη]
    refine le_volume_iUnion_of_multiplicity_le s (fun i => (V i).toShadedBody) hpow0 hpowtop ?_
      (le_of_lt hlow')
    · -- The scalar inequality `a ^ (-η) * L ≤ ∑ i ∈ s, |Y i|` is proved by combining the
      -- low-multiplicity scalar bound `lowMultiplicityScalarBound` with the fullness bound.
      have hs_card_pos : 0 < s.card := Finset.card_pos.mpr hs
      -- the dilated hypothesis implies the aligned count that the low branch uses
      have hMth' : ∀ i ∈ s, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
          (({j ∈ s | (V j).carrier ⊆
              (Plank.thickened (V i).toPrism3D θ hθ1).carrier}.card : ℝ≥0)) ≤ M * θ :=
        fun i hi θ' hθ'a hθ'1 =>
          Plank.IsThickeningNonconcentrated.aligned_card_le
            (Plank.ThickenedRepr.one_le_fibreDilation hcThk) hMth i hi θ' hθ'1 hθ'a
      have hMab : M⁻¹ ≤ a / b := inv_le_div_of_plankConcentration ha hab hb1 V hs hM hMth'
      have hballCF : Vb ≤ CF * ((s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) :=
        volume_plankWindow_le_of_isFrostmanIn V ha hs hVball hFrost
      have hb₀q : 8 * (Vb ^ (1 - β / 2))⁻¹ * (b : ENNReal) ^ (2 * β) ≤ 1 := by
        simpa [mul_assoc] using hballabs b hb_ball
      have hscalar := lowMultiplicityScalarBound hβpos hβle hη hεη ha hab hb1 hs_card_pos hM hMab
        hCF1 hCFtop hVb0 hVbtop hballCF hb₀q
      have hcoe : (((a ^ η : ℝ≥0)) : ENNReal) = (a : ENNReal) ^ η :=
        ENNReal.coe_rpow_of_ne_zero ha.ne' η
      have hmass : ((a ^ η : ℝ≥0) : ENNReal) * ((s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)))
          ≤ ∑ i ∈ s, volume ((V i).toShadedBody).shade := by
        refine ShadedBody.coe_fullness_mul_le_sum_volume_shade s (fun i => (V i).toShadedBody) hlam ?_
        intro i _
        rw [show volume ((fun i => (V i).toShadedBody) i).carrier = volume ((V i).toPrism3D).carrier from rfl,
          Prism3D.volume_carrier]
        simp
      exact le_trans hscalar (by
        rw [← hcoe] at *
        exact hmass)

/-- **GWZ Lemma 6.4 (Frostman estimate for planks)** — assembled from the volume lower bound. -/
theorem FrostmanEstimate.plankEstimate.{u} {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β) :
    ∃ C_NC : ℝ≥0, 1 ≤ C_NC ∧
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0),
      ∀ {ι : Type u} (s : Finset ι) {a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
        (V : ι → ShadedPlank a b hab hb1),
        0 < a → b ≤ b₀ →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
        (s : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        a ^ η ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) →
        ∀ (M : ℝ≥0), 1 ≤ M →
        Plank.IsThickeningNonconcentrated s (fun i => (V i).toPrism3D) C_NC M →
        ∀ (CF : ENNReal), 1 ≤ CF → CF ≠ ⊤ →
          IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) plankWindow CF →
          (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
              * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (β / 2)
            ≤ volume (⋃ i ∈ s, (V i).shade) ∧
          ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
            (a : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
              * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ (-2 * β)
              * ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (1 - β / 2) := by
  obtain ⟨C_NC, hC_NC, hvolAll⟩ := FrostmanEstimate.plankVolumeLowerBound.{u} hβpos hβle hKF
  refine ⟨C_NC, hC_NC, ?_⟩
  intro ε hε
  obtain ⟨η, hη, b₀, hb₀, hvol⟩ := hvolAll ε hε
  refine ⟨η, hη, b₀, hb₀, ?_⟩
  intro ι s a b hab hb1 V ha hbb₀ hVball hed hlam M hM hMth CF hCF1 hCFtop hFrost
  have hVOL8 :=
    hvol s hab hb1 V ha hbb₀ hVball hed hlam M hM hMth CF hCF1 hCFtop hFrost
  set X := (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
    * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (β / 2) with hX
  have hX_nonneg : 0 ≤ X := by
    positivity
  have hX_le_8X : X ≤ 8 * X := by
    calc
      X = 1 * X := by simp
      _ ≤ 8 * X := mul_le_mul_of_nonneg_right (by norm_num : (1 : ENNReal) ≤ 8) hX_nonneg
  refine ⟨?_, ?_⟩
  · calc
      X ≤ 8 * X := hX_le_8X
      _ = 8 * (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
          * ((M : ENNReal)⁻¹ * (b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (β / 2) := by
        simp [hX, mul_assoc]
      _ ≤ volume (⋃ i ∈ s, (V i).shade) := hVOL8
  · exact multiplicityBoundFromVolume hβpos hβle ha hab hb1 hM hCF1 hCFtop s V hVOL8


/-! ## Additional estimates

Two derived geometric facts used by the Section-6 comparable-body interface.
-/

/-! ### Derived consequences of the local factorisation

Two clauses formerly bundled into the Section-6 presentation are consequences of the
comparable-representative datum together with parentwise Katz--Tao, and are proved here rather than
assumed. -/

/-- **The within-parent count at the exact `C_NC`-dilated test body, from Katz--Tao.**

This is the derivation the provenance check asks for: the local dilated count is *not* primitive
Proposition-5.1 data.  Applying `Kakeya.isKatzTao_iff` to the convex body
`((W j)_θ).dilation C_NC` and using that every representative is an exact `a × b × 1` plank of
volume `8ab`, while the test body has volume `8 · (C_NC θ b) · (C_NC b) · C_NC`, gives

`#{x ∈ fibre : W x ⊆ (W j)_θ^{C_NC}} · 8ab ≤ C_KT · 8 C_NC³ θ b²`,

i.e. the count is at most `C_KT · C_NC³ · (b/a) · θ`.  The geometric factor is exactly `C_NC³`, the
volume ratio of the dilation, and it is absolute because `C_NC` is.

Katz--Tao is applied to **one** fibre, which downstream is one original external parent fibre; no
union of fibres is ever formed. -/
theorem card_le_of_isKatzTao_dilatedThickening
    {κ' : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (ha : 0 < a) (hb0 : 0 < b) (fibre : Finset κ') (W : κ' → Plank a b hab hb1)
    {CKT : ℝ≥0} (hKT : IsKatzTao fibre (fun x => (W x).toConvexSpaceBody) (CKT : ENNReal))
    (C_NC : ℝ≥0) (j : κ') {θ : ℝ≥0} (hθ1 : θ ≤ 1) :
    ((fibre.filter fun x => ((W x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        (((W j).thickened θ hθ1).toPrismNDim.dilation C_NC).carrier).card : ℝ≥0)
      ≤ CKT * C_NC ^ 3 * (b / a) * θ := by
  -- The `C_NC`-dilated thickened prism `K` and its ConvexSpaceBody view, and the filtered
  -- subfamily `F` whose cardinality is the goal's count.
  set K : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
      ((W j).thickened θ hθ1).toPrismNDim.dilation C_NC
  let K_cb : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := K.toConvexSpaceBody
  set F : Finset κ' := fibre.filter (fun x =>
      ((W x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ K.carrier)
  -- Katz--Tao at the test body: the aggregate carrier volume bound over the contained planks.
  have hkt_unf :
      (∑ x ∈ fibre.filter (fun x => (W x).toConvexSpaceBody ≤ K_cb),
          volume ((W x).carrier)) ≤ (CKT : ENNReal) * volume K_cb.carrier :=
    (isKatzTao_iff fibre (fun x => (W x).toConvexSpaceBody) (CKT : ENNReal)).mp hKT K_cb
  -- The two filters agree: `≤` on ConvexSpaceBody is carrier-inclusion, and
  -- `(W x).toConvexSpaceBody.carrier = (W x).carrier` definitionally.
  have hfilter : fibre.filter (fun x => (W x).toConvexSpaceBody ≤ K_cb) = F := by
    ext x
    simp only [Finset.mem_filter, F, K_cb, SetLike.le_def]
    rfl
  have hktF : (∑ x ∈ F, volume ((W x).carrier)) ≤ (CKT : ENNReal) * volume K_cb.carrier := by
    simpa [hfilter] using hkt_unf
  -- The total carrier volume of the planks in `F` is exactly `|F| · 8ab`.
  have hsum : (∑ x ∈ F, volume ((W x).carrier)) = (F.card : ENNReal) * ((8 * a * b
      : ℝ≥0) : ENNReal) := by
    calc
      (∑ x ∈ F, volume ((W x).carrier)) = (∑ x ∈ F, ((8 * a * b : ℝ≥0) : ENNReal)) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Prism3D.volume_carrier (W x), ENNReal.coe_one, mul_one]
        rw [← ENNReal.coe_ofNat, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
      _ = (F.card : ENNReal) * ((8 * a * b : ℝ≥0) : ENNReal) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  -- Carrier volume of `K` via dilation + thickened-plank volume.
  have hvolK : volume K_cb.carrier =
      (C_NC : ENNReal) ^ 3 * (8 * (θ : ENNReal) * b * b) := by
    calc
      volume K_cb.carrier = volume K.carrier := rfl
      _ = (C_NC : ENNReal) ^ 3 * volume ((W j).thickened θ hθ1).carrier := by
        rw [PrismNDim.volume_dilation]
      _ = (C_NC : ENNReal) ^ 3 * (8 * (θ : ENNReal) * b * b) := by
        rw [Plank.volume_thickened (W j) θ hθ1]
  -- ENNReal inequality: |F| · 8ab ≤ CKT · C_NC³ · (8 θ b²).
  have h_enn : (F.card : ENNReal) * ((8 * a * b : ℝ≥0) : ENNReal) ≤
      (CKT : ENNReal) * (C_NC : ENNReal) ^ 3 * (8 * (θ : ENNReal) * b * b) := by
    calc
      (F.card : ENNReal) * ((8 * a * b : ℝ≥0) : ENNReal) =
          (∑ x ∈ F, volume ((W x).carrier)) := by
        rw [← hsum]
      _ ≤ (CKT : ENNReal) * volume K_cb.carrier := hktF
      _ = (CKT : ENNReal) * ((C_NC : ENNReal) ^ 3 * (8 * (θ : ENNReal) * b * b)) := by
        rw [hvolK]
      _ = (CKT : ENNReal) * (C_NC : ENNReal) ^ 3 * (8 * (θ : ENNReal) * b * b) := by
        simp [mul_assoc]
  -- Descend to `ℝ≥0`.
  have h_nn : (F.card : ℝ≥0) * (8 * a * b) ≤ CKT * C_NC ^ 3 * (8 * θ * b * b) := by
    exact_mod_cast h_enn
  -- Divide by `8ab ≠ 0`.
  have h8ab : (0 : ℝ≥0) < 8 * a * b := by positivity
  calc
    (F.card : ℝ≥0) ≤ (CKT * C_NC ^ 3 * (8 * θ * b * b)) / (8 * a * b) := by
      rw [le_div_iff₀ h8ab]
      exact h_nn
    _ = CKT * C_NC ^ 3 * (b / a) * θ := by
      field_simp [show (8 * a * b : ℝ≥0) ≠ 0 from ne_of_gt h8ab, show (a : ℝ≥0) ≠ 0 from ha.ne']

/-- **A `δ`-tube inside an `a × b × 1` plank forces `δ ≤ a`.**

The tube contains the ball of radius `δ` about its centre, and the plank's smallest half-width is
`a`; testing the two points `centre ± δ · e₀` against the plank's thin coordinate and adding the two
inequalities gives `2δ ≤ 2a`.  This is what makes `δ ≤ a` a *derived* statement rather than an
unexplained output of the factorisation interface. -/
theorem le_thinWidth_of_tube_le_plank {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (Tb : Tube δ (EuclideanSpace ℝ (Fin 3))) (P : Plank a b hab hb1)
    (h : Tb.toConvexSpaceBody ≤ P.toConvexSpaceBody) : δ ≤ a := by
  let E := EuclideanSpace ℝ (Fin 3)
  set e0 : E := P.basis 0
  let s : ℝ := P.basis.repr (Tb.center - P.center) 0
  -- `δ ≥ 0`, and `e0` has norm one.
  have hδ_nonneg : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast NNReal.coe_nonneg δ
  have hnorm_e0 : ‖e0‖ = 1 := by simp [e0]
  -- The tube contains the closed ball of radius δ about its centre (the midpoint of the segment).
  have hcenter_seg : Tb.center ∈ segment ℝ Tb.x Tb.y := midpoint_mem_segment (𝕜 := ℝ) Tb.x Tb.y
  have hball_carrier : Metric.closedBall Tb.center (δ : ℝ) ⊆ (Tb.carrier : Set E) := by
    rw [Tb.carrier_eq]
    intro p hp
    exact Set.mem_iUnion₂.mpr ⟨Tb.center, hcenter_seg, hp⟩
  -- Carrier inclusion from the hypothesis.
  have hP_subset : (Tb.carrier : Set E) ⊆ (P.carrier : Set E) := by
    intro x hx
    exact h hx
  -- For real `r` with `|r| ≤ δ`, the point `Tb.center + r • e0` lies in the tube.
  have hpt_mem (r : ℝ) (hr : |r| ≤ (δ : ℝ)) :
      Tb.center + r • e0 ∈ (Tb.carrier : Set E) :=
    hball_carrier (by
      rw [Metric.mem_closedBall, dist_eq_norm]
      rw [show ‖Tb.center + r • e0 - Tb.center‖ = ‖r • e0‖ by abel]
      rw [norm_smul, Real.norm_eq_abs, hnorm_e0, mul_one]
      exact hr)
  -- The 0-th basis coordinate of `Tb.center + r • e0 -ᵥ P.center` is `s + r`.
  have hrepr (r : ℝ) : P.basis.repr (Tb.center + r • e0 -ᵥ P.center) 0 = s + r := by
    rw [vsub_eq_sub]
    calc
      P.basis.repr (Tb.center + r • e0 - P.center) 0
          = inner ℝ (P.basis 0) (Tb.center + r • e0 - P.center) := by
            rw [P.basis.repr_apply_apply]
      _ = inner ℝ (P.basis 0) ((Tb.center - P.center) + r • e0) := by
            congr 1
            abel
      _ = inner ℝ (P.basis 0) (Tb.center - P.center) + r * inner ℝ (P.basis 0) e0 := by
            rw [inner_add_right, inner_smul_right]
      _ = s + r * (inner ℝ (P.basis 0) e0) := by
            rw [show inner ℝ (P.basis 0) (Tb.center - P.center) = s by
              rw [← P.basis.repr_apply_apply]]
      _ = s + r := by
            rw [show inner ℝ (P.basis 0) e0 = (1 : ℝ) by
              simp [e0]]
            ring
  -- The thin half-width of the plank is `a`.
  have hthk0 : (P.thicknesses 0 : ℝ) = (a : ℝ) := by
    rw [P.thicknesses_eq]; rfl
  -- A point of the tube lying in the plank has its thin coordinate bounded by `a`.
  have hwidth (r : ℝ) (hr : |r| ≤ (δ : ℝ)) :
      |P.basis.repr (Tb.center + r • e0 -ᵥ P.center) 0| ≤ (a : ℝ) := by
    have hpt : Tb.center + r • e0 ∈ (Tb.carrier : Set E) := hpt_mem r hr
    have hpP : Tb.center + r • e0 ∈ (P.carrier : Set E) := hP_subset hpt
    have hc := (P.mem_carrier_iff (Tb.center + r • e0)).1 hpP 0
    rw [vsub_eq_sub] at hc
    rwa [hthk0] at hc
  have h1_abs : |s + (δ : ℝ)| ≤ (a : ℝ) := by
    have hw := hwidth (δ : ℝ) (by simp [abs_of_nonneg hδ_nonneg])
    rw [hrepr (δ : ℝ)] at hw
    exact hw
  have h2_abs : |s + (-(δ : ℝ))| ≤ (a : ℝ) := by
    have hw := hwidth (-(δ : ℝ)) (by rw [abs_neg, abs_of_nonneg hδ_nonneg])
    rw [hrepr (-(δ : ℝ))] at hw
    exact hw
  have hδa : (δ : ℝ) ≤ (a : ℝ) := by
    linarith [(abs_le.mp h1_abs), (abs_le.mp h2_abs)]
  exact_mod_cast hδa

end Kakeya
