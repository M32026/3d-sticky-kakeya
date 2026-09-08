/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParams
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEccentric

/-!
# Exponent bookkeeping for the (F)/(P) floor derivation

The source pins the floor exponent by `0 < η' ≤ ε² τ / 64` (refined l.4011–4016), with
`ε = ML2Spine.spineDiv ϖ ε₁` and `τ = η_{J+1} = ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1)` at a
window of rung `m`.  The tree's eccentric exit `Kakeya.ML2Core.eccentric_atPlankScale` is stated at
an exponent `η`: its trigger is `Kakeya.ML2Reduction.IsEccentric β ε₂ η`, whose exponent is
`eccExponent β ε₂ η = 12 η / (ε₂ β)`, and its multiplicity gain is `δ^{10 η / ε₂ - η₀/2}`.

**B2 of, both halves **, after the re-anchoring of `ML2Spine.spineStep`
specified in  (first entry `e² β x / 1024`, the refined source's second ladder `η̄`
saturated at its cap `e² τ / 64`):

* the trigger side of the squeeze `eccExponent β ε₂ η ≤ η' ≤ ε² τ / 64` is satisfiable at a
  `δ`-free `η` (`eccExponent_le_floorCap`): `η := ε₂ β ε² η_1 / 768` gives exactly
  `eccExponent = ε² η_1 / 64 ≤ ε² τ / 64` at every window rung;
* the squeeze caps the exit's gain at `10 β ε² τ / 768` (`eccentric_gain_le_of_squeeze`), and the
  re-anchored bottom step `ν ≤ ε² β η_1 / 1024` (`spineNu_le_step_bound`) puts a `10 ν`-sized
  target under that cap with margin `4/3` at every rung, the bottom included:
  `10 ν ≤ 10 β ε² η_{m+1} / 768` (`ten_spineNu_le_squeeze_gain`), with equality
  `10 ν = (3/4) · cap` at `m = 0` for the spine at `gain = dens = 1`
  (`ten_spineNu_eq_three_quarters_cap_at_one`); higher rungs have room by `40 η_m / 3`
  (`step_le_squeeze_gain`).
* **Firing control**: for a step constant `K` in place of `1024`, the
  inequality `10 · (ε² β η_1 / K) ≤ 10 β ε² η_1 / 768` holds iff `768 ≤ K`
  (`squeeze_gain_control_iff`); at the old `K = 48` it FAILS (`squeeze_gain_control_fails_at_48`),
  so the re-anchoring is what closes the gain side, and the arithmetic is being read.

The remaining rows are the routine F6 items: `4 η' ≤ ε² τ / 16` from the cap
(`four_mul_le_of_floorCap`), the rung monotonicity `η_1 ≤ η_{m+1}`
(`spineRung_one_le_spineRung_succ`), and  H2's margin `4 η' + ν / 20 ≤ ε² τ / 8`
(`floor_margin_H2`, discharged per §11.5).
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.ML2Spine

variable {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}

/-! ## The ladder facts used by the bookkeeping -/

/-- `η_1 ≤ η_{m+1}` for every `m`: the chain is monotone (and constant above `N`). -/
theorem spineRung_one_le_spineRung_succ (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) (m : ℕ) :
    spineRung β ϖ ε₁ gain dens 1 ≤ spineRung β ϖ ε₁ gain dens (m + 1) := by
  have hanti : Antitone (spineAux β ϖ ε₁ gain dens) :=
    spineAux_antitone hβ hβ1 hϖ hε₁ hgain hdens
  unfold spineRung
  exact hanti (by omega)

/-- **The step bound at the bottom rung**: `ν = step(η_1) ≤ ε² β η_1 / 1024`, the first entry of
`ML2Spine.spineStep` after  -/
theorem spineNu_le_step_bound (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) :
    spineNu β ϖ ε₁ gain dens
      ≤ spineDiv ϖ ε₁ ^ 2 * β * spineRung β ϖ ε₁ gain dens 1 / 1024 := by
  unfold spineNu
  rw [spineRung_eq_step (Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_spineCount hϖ hε₁))]
  unfold spineStep
  exact (min_le_left _ _).trans (min_le_left _ _)

/-- At `gain = dens = 1` the bottom step **is** its first entry: `ν = ε² β η_1 / 1024`. -/
theorem spineNu_eq_step_bound_at_one (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) :
    spineNu β ϖ ε₁ (fun _ => 1) (fun _ => 1)
      = spineDiv ϖ ε₁ ^ 2 * β * spineRung β ϖ ε₁ (fun _ => 1) (fun _ => 1) 1 / 1024 := by
  have he0 : 0 < spineDiv ϖ ε₁ := spineDiv_pos hϖ hε₁
  have he10 : spineDiv ϖ ε₁ ≤ 1 / 10 := spineDiv_le_one hϖ hε₁
  have hsp := spineRung_isSpine hβ hβ1 hϖ hε₁ (gain := fun _ => 1) (dens := fun _ => 1)
    (fun _ _ => one_pos) (fun _ _ => one_pos)
  have hr1 : spineRung β ϖ ε₁ (fun _ => 1) (fun _ => 1) 1 ≤ spineDiv ϖ ε₁ := hsp.rung_le_div 1
  have hr0 : 0 < spineRung β ϖ ε₁ (fun _ => 1) (fun _ => 1) 1 := hsp.rung_pos 1
  unfold spineNu
  rw [spineRung_eq_step (Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_spineCount hϖ hε₁))]
  unfold spineStep
  set e := spineDiv ϖ ε₁ with he
  set r := spineRung β ϖ ε₁ (fun _ => 1) (fun _ => 1) 1 with hr
  have her : e * r ≤ 1 / 100 := by
    calc e * r ≤ e * e := mul_le_mul_of_nonneg_left hr1 he0.le
      _ ≤ 1 / 10 * (1 / 10) := mul_le_mul he10 he10 he0.le (by norm_num)
      _ = 1 / 100 := by norm_num
  have heβ : 0 ≤ e * β := by positivity
  have h1 : e ^ 2 * β * r / 1024 ≤ e * β * 1 / 34 := by
    calc e ^ 2 * β * r / 1024 = (e * r) * (e * β) / 1024 := by ring
      _ ≤ (1 / 100) * (e * β) / 1024 := by gcongr
      _ ≤ e * β * 1 / 34 := by linarith
  have h2 : e ^ 2 * β * r / 1024 ≤ e * 1 / 2 := by
    have heβr : e * β * r ≤ 1 / 100 := by
      calc e * β * r ≤ e * 1 * r := by gcongr
        _ = e * r := by ring
        _ ≤ 1 / 100 := her
    calc e ^ 2 * β * r / 1024 = e * (e * β * r) / 1024 := by ring
      _ ≤ e * (1 / 100) / 1024 := by gcongr
      _ ≤ e * 1 / 2 := by linarith
  rw [min_eq_left h1, min_eq_left h2]

/-! ## F6: the cap and its consequences -/

/-- `η' ≤ ε² τ / 64` gives `4 η' ≤ ε² τ / 16` (refined l.4011, the form F6 spends). -/
theorem four_mul_le_of_floorCap {η' e τ : ℝ} (h : η' ≤ e ^ 2 * τ / 64) :
    4 * η' ≤ e ^ 2 * τ / 16 := by linarith

/-- ** H2's margin, ** (discharged, §11.5): with `4 η' ≤ ε² τ / 16` and a
step bound `ν ≤ ε² β τ / 48` (`β ≤ 1`; the re-anchored `/ 1024` bound implies it),
`4 η' + ν / 20 ≤ ε² τ / 8`. -/
theorem floor_margin_H2 {η' e τ ν β : ℝ} (hβ1 : β ≤ 1) (hτ : 0 ≤ τ)
    (hη' : 4 * η' ≤ e ^ 2 * τ / 16) (hν : ν ≤ e ^ 2 * β * τ / 48) :
    4 * η' + ν / 20 ≤ e ^ 2 * τ / 8 := by
  have he2τ : 0 ≤ e ^ 2 * τ := by positivity
  have : e ^ 2 * β * τ ≤ e ^ 2 * τ := by nlinarith
  nlinarith

/-! ## B2: the (P) squeeze `eccExponent β ε₂ η ≤ η' ≤ ε² τ / 64` -/

/-- **Trigger side, satisfiable.**  At `η := ε₂ β ε² η_1 / 768` (`δ`-free, pinned before `δ`),
`eccExponent β ε₂ η = ε² η_1 / 64 ≤ ε² η_{m+1} / 64` at every window rung `m`; so
`η' := ε² η_1 / 64` meets both bounds of the squeeze. -/
theorem eccExponent_le_floorCap (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) (m : ℕ) :
    ML2Reduction.eccExponent β (spineEps₂ ϖ ε₁)
        (spineEps₂ ϖ ε₁ * β * spineDiv ϖ ε₁ ^ 2 * spineRung β ϖ ε₁ gain dens 1 / 768)
      ≤ spineDiv ϖ ε₁ ^ 2 * spineRung β ϖ ε₁ gain dens (m + 1) / 64 := by
  have hε₂ : 0 < spineEps₂ ϖ ε₁ := spineEps₂_pos hϖ hε₁
  have hmono := spineRung_one_le_spineRung_succ hβ hβ1 hϖ hε₁ hgain hdens m
  have he2 : 0 ≤ spineDiv ϖ ε₁ ^ 2 := by positivity
  have heq : ML2Reduction.eccExponent β (spineEps₂ ϖ ε₁)
      (spineEps₂ ϖ ε₁ * β * spineDiv ϖ ε₁ ^ 2 * spineRung β ϖ ε₁ gain dens 1 / 768)
      = spineDiv ϖ ε₁ ^ 2 * spineRung β ϖ ε₁ gain dens 1 / 64 := by
    unfold ML2Reduction.eccExponent
    field_simp
    ring
  rw [heq]
  have := mul_le_mul_of_nonneg_left hmono he2
  linarith

/-- **Gain side, capped.**  Any `η` meeting the trigger squeeze `eccExponent β ε₂ η ≤ ε² τ / 64`
has exit gain `10 η / ε₂ ≤ 10 β ε² τ / 768`. -/
theorem eccentric_gain_le_of_squeeze {β ε₂ η e τ : ℝ} (hβ : 0 < β) (hε₂ : 0 < ε₂)
    (hsq : ML2Reduction.eccExponent β ε₂ η ≤ e ^ 2 * τ / 64) :
    10 * η / ε₂ ≤ 10 * β * e ^ 2 * τ / 768 := by
  unfold ML2Reduction.eccExponent at hsq
  have hpos : 0 < ε₂ * β := mul_pos hε₂ hβ
  have h1 : 12 * η ≤ e ^ 2 * τ / 64 * (ε₂ * β) := (div_le_iff₀ hpos).mp hsq
  rw [div_le_iff₀ hε₂]
  nlinarith

/-- **The gain side closes at every rung, the bottom included**: with the
re-anchored step, `10 ν ≤ 10 β ε² η_{m+1} / 768`, the squeeze-maximal exit gain. -/
theorem ten_spineNu_le_squeeze_gain (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) (m : ℕ) :
    10 * spineNu β ϖ ε₁ gain dens
      ≤ 10 * β * spineDiv ϖ ε₁ ^ 2 * spineRung β ϖ ε₁ gain dens (m + 1) / 768 := by
  have h1 := spineNu_le_step_bound (β := β) (gain := gain) (dens := dens) hϖ hε₁
  have h2 := spineRung_one_le_spineRung_succ hβ hβ1 hϖ hε₁ hgain hdens m
  have he2β : 0 ≤ spineDiv ϖ ε₁ ^ 2 * β := by positivity
  have h3 := mul_le_mul_of_nonneg_left h2 he2β
  have hM : 0 ≤ spineDiv ϖ ε₁ ^ 2 * β * spineRung β ϖ ε₁ gain dens (m + 1) :=
    le_trans (mul_nonneg he2β ((spineRung_isSpine hβ hβ1 hϖ hε₁ hgain hdens).rung_pos 1).le) h3
  have hgoal : 10 * β * spineDiv ϖ ε₁ ^ 2 * spineRung β ϖ ε₁ gain dens (m + 1) / 768
      = 10 * (spineDiv ϖ ε₁ ^ 2 * β * spineRung β ϖ ε₁ gain dens (m + 1)) / 768 := by ring
  rw [hgoal]
  linarith [h1, h3, hM]

/-- **The margin at the bottom rung is exactly `4/3`**: for the spine at `gain = dens = 1`,
`10 ν = (3/4) · (10 β ε² η_1 / 768)`. -/
theorem ten_spineNu_eq_three_quarters_cap_at_one (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hε₁ : 0 < ε₁) :
    10 * spineNu β ϖ ε₁ (fun _ => 1) (fun _ => 1)
      = 3 / 4 * (10 * β * spineDiv ϖ ε₁ ^ 2
          * spineRung β ϖ ε₁ (fun _ => 1) (fun _ => 1) (0 + 1) / 768) := by
  rw [spineNu_eq_step_bound_at_one hβ hβ1 hϖ hε₁]
  simp only [Nat.zero_add]
  ring

/-- **Firing control.**  For a hypothetical step constant `K` in place of
`1024`, `10 · (ε² β η_1 / K) ≤ 10 β ε² η_1 / 768` holds iff `768 ≤ K`. -/
theorem squeeze_gain_control_iff {e β x K : ℝ} (he : 0 < e) (hβ : 0 < β) (hx : 0 < x)
    (hK : 0 < K) :
    10 * (e ^ 2 * β * x / K) ≤ 10 * β * e ^ 2 * x / 768 ↔ 768 ≤ K := by
  have hM : 0 < 10 * (e ^ 2 * β * x) := by positivity
  have h1 : 10 * (e ^ 2 * β * x / K) = 10 * (e ^ 2 * β * x) / K := by ring
  have h2 : 10 * β * e ^ 2 * x / 768 = 10 * (e ^ 2 * β * x) / 768 := by ring
  rw [h1, h2, div_le_div_iff₀ hK (by norm_num)]
  constructor
  · intro h
    exact le_of_mul_le_mul_left h hM
  · intro h
    exact mul_le_mul_of_nonneg_left h hM.le

/-- At the old constant `K = 48` the control FAILS: the pre-§11.4 spine could not put `10 ν`
under the (P) cap. -/
theorem squeeze_gain_control_fails_at_48 {e β x : ℝ} (he : 0 < e) (hβ : 0 < β) (hx : 0 < x) :
    ¬ (10 * (e ^ 2 * β * x / 48) ≤ 10 * β * e ^ 2 * x / 768) := by
  rw [squeeze_gain_control_iff (K := 48) he hβ hx (by norm_num)]
  norm_num

/-- At `K = 1024` the control holds, with margin: `768 ≤ 1024`. -/
theorem squeeze_gain_control_at_1024 {e β x : ℝ} (he : 0 < e) (hβ : 0 < β) (hx : 0 < x) :
    10 * (e ^ 2 * β * x / 1024) ≤ 10 * β * e ^ 2 * x / 768 := by
  rw [squeeze_gain_control_iff (K := 1024) he hβ hx (by norm_num)]
  norm_num

/-- **Away from the bottom rung the cap is generous**: at rung `m < N`, the squeeze-maximal gain
`10 β ε² η_{m+1} / 768` is at least `40 η_m / 3`, because `η_m ≤ ε² β η_{m+1} / 1024`. -/
theorem step_le_squeeze_gain {m : ℕ} (hm : m < spineCount ϖ ε₁) :
    40 / 3 * spineRung β ϖ ε₁ gain dens m
      ≤ 10 * β * spineDiv ϖ ε₁ ^ 2 * spineRung β ϖ ε₁ gain dens (m + 1) / 768 := by
  have h : spineRung β ϖ ε₁ gain dens m
      ≤ spineDiv ϖ ε₁ ^ 2 * β * spineRung β ϖ ε₁ gain dens (m + 1) / 1024 := by
    rw [spineRung_eq_step hm]
    unfold spineStep
    exact (min_le_left _ _).trans (min_le_left _ _)
  linarith

end Kakeya.ML2Spine

end
