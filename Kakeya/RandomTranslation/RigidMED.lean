/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Asymptotics
public import Kakeya.RandomTranslation.RigidMotionChernoff

/-!
# The CF-free ED multiplicity cap `rigidMED`

The old random-copy argument capped the essential-distinctness multiplicity of the randomised family
by the deterministic `J`-fold union bound

`M_ED := ⌈CF⌉₊ * C_pack_ext + 1`,

which is linear in the Frostman constant and therefore forces the small-scale threshold to depend on
`CF`. That is the defect this branch removes.

The replacement is **polylogarithmic in `1/δ` and completely free of `CF`**:

`rigidMED C δ = ⌈C · (1 + log (1/δ))⌉₊ + 1`,

where `C` is a dimensional constant coming from the Chernoff threshold
(`Kakeya.edBadCount_chernoff_tail`) and the polynomial cardinality of the test-tube net.

## The absorption lemmas

Downstream, `RandCF`'s smallness envelopes need the cap to be absorbed by an arbitrary negative
power of `δ`. Since `rigidMED` is polylogarithmic this is automatic, and rather than prove one
absorption lemma per envelope conjunct we prove a single workhorse,
`Kakeya.eventually_le_rpow_neg_of_le_polylog`: *any* quantity dominated by
`C · (1 + log (1/δ))^k` is eventually `≤ δ^(-η)`, for every `η > 0` and every fixed degree `k`.
The linear and quadratic forms actually consumed (the old `S6` conjunct was quadratic in the cap)
are then immediate corollaries.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

namespace Kakeya

/-- **Robust polylog-versus-power absorption.** For every positive constant `C`, every exponent
`η > 0` and every fixed degree `k`, a degree-`k` polynomial in `log (1/δ)` is eventually
dominated by `δ^(-η)` as `δ → 0⁺`. -/
theorem absorb_polylog_le_rpow_neg {C η : ℝ} (hC : 0 < C) (hη : 0 < η) (k : ℕ) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), C * (1 + Real.log (1 / δ)) ^ k ≤ δ ^ (-η) := by
  by_cases hk : k = 0
  · filter_upwards [absorb_const_le_rpow_neg hC hη] with δ hδ
    simpa [hk] using hδ
  · let η' : ℝ := η / (2 * (k : ℝ))
    have hη' : 0 < η' := by
      dsimp [η']
      positivity
    have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hlog_le : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), Real.log (1 / δ) ≤ δ ^ (-(η' / 2)) := by
      have h := absorb_log_le_rpow_neg (C := (1 : ℝ)) (M := (1 : ℝ)) (η := η' / 4)
        (by norm_num) (by norm_num) (by positivity)
      filter_upwards [h] with δ h'
      have hE : (-(2 * (η' / 4)) : ℝ) = -(η' / 2) := by ring
      rw [hE] at h'
      simpa using h'
    have hconst1 : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), (1 : ℝ) ≤ δ ^ (-(η' / 2)) :=
      absorb_const_le_rpow_neg (C := (1 : ℝ)) (η := η' / 2) (by norm_num) (by positivity)
    have hconst2 : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), (2 : ℝ) ≤ δ ^ (-(η' / 2)) :=
      absorb_const_le_rpow_neg (C := (2 : ℝ)) (η := η' / 2) (by norm_num) (by positivity)
    have hdiff : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), 1 + Real.log (1 / δ) ≤ δ ^ (-η') := by
      filter_upwards [hconst1, hlog_le, hconst2, self_mem_nhdsWithin]
          with δ hlog1 hlog hconst2 (hδpos : 0 < δ)
      calc
        1 + Real.log (1 / δ) ≤ δ ^ (-(η' / 2)) + δ ^ (-(η' / 2)) := add_le_add hlog1 hlog
        _ = (2 : ℝ) * δ ^ (-(η' / 2)) := by ring
        _ ≤ δ ^ (-(η' / 2)) * δ ^ (-(η' / 2)) :=
          mul_le_mul_of_nonneg_right hconst2 (Real.rpow_nonneg hδpos.le _)
        _ = δ ^ (-(η' / 2) + -(η' / 2)) := (Real.rpow_add hδpos _ _).symm
        _ = δ ^ (-η') := by congr 1; ring
    have hC_add : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), C ≤ δ ^ (-(η / 2)) :=
      absorb_const_le_rpow_neg hC (by positivity)
    have hδle1 : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), δ ≤ 1 := by
      refine Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)) ?_
      intro δ hδ
      exact le_of_lt hδ.2
    have hlog_nonneg : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), 0 ≤ 1 + Real.log (1 / δ) := by
      filter_upwards [self_mem_nhdsWithin, hδle1] with δ hδpos hδle1
      have hone : (1 : ℝ) ≤ 1 / δ := by
        rw [le_div_iff₀ hδpos]
        nlinarith
      have hge : (0 : ℝ) ≤ Real.log (1 / δ) := Real.log_nonneg hone
      nlinarith
    filter_upwards [hdiff, hC_add, self_mem_nhdsWithin, hlog_nonneg]
      with δ hdiff hC_add (hδpos : 0 < δ) hlog_nonneg
    have hpow : (δ ^ (-η')) ^ k = δ ^ (-(η' * (k : ℝ))) := by
      rw [← Real.rpow_natCast (δ ^ (-η')) k]
      rw [← Real.rpow_mul hδpos.le (-η') (k : ℝ)]
      congr 1
      ring
    have hη'k : η' * (k : ℝ) = η / 2 := by
      dsimp [η']
      field_simp [hk_ne]
    calc
      C * (1 + Real.log (1 / δ)) ^ k ≤ δ ^ (-(η / 2)) * (δ ^ (-η')) ^ k := by
        exact mul_le_mul hC_add (pow_le_pow_left₀ hlog_nonneg hdiff k)
          (pow_nonneg hlog_nonneg k) (Real.rpow_nonneg hδpos.le _)
      _ = δ ^ (-(η / 2)) * δ ^ (-(η' * (k : ℝ))) := by rw [hpow]
      _ = δ ^ (-(η / 2)) * δ ^ (-(η / 2)) := by rw [hη'k]
      _ = δ ^ (-(η / 2) + -(η / 2)) := (Real.rpow_add hδpos _ _).symm
      _ = δ ^ (-η) := by congr 1; ring

/-- The workhorse form: anything dominated by a degree-`k` polylogarithm is eventually dominated by
`δ^(-η)`. Stated for `NNReal` scales, which is what the `RandCF` envelopes use. -/
theorem eventually_le_rpow_neg_of_le_polylog {C η : ℝ} (hC : 0 < C) (hη : 0 < η) (k : ℕ)
    {f : NNReal → ℝ}
    (hf : ∀ δ : NNReal, 0 < δ → (δ : ℝ) ≤ 1 →
      f δ ≤ C * (1 + Real.log (1 / (δ : ℝ))) ^ k) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, f δ ≤ (δ : ℝ) ^ (-η) := by
  have hmain : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal),
      C * (1 + Real.log (1 / (δ : ℝ))) ^ k ≤ (δ : ℝ) ^ (-η) :=
    nnreal_eventually_of_real_eventually (absorb_polylog_le_rpow_neg hC hη k)
  have hle1 : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), (δ : ℝ) ≤ 1 := by
    have hx : ∀ᶠ (x : ℝ) in 𝓝[>] (0 : ℝ), x ≤ 1 := by
      refine Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)) ?_
      intro x hx
      exact le_of_lt hx.2
    exact nnreal_eventually_of_real_eventually hx
  filter_upwards [hmain, self_mem_nhdsWithin, hle1] with δ hmain hpos hle1
  exact (hf δ hpos hle1).trans hmain

/-- **The CF-free ED multiplicity cap.** Polylogarithmic in `1/δ`; the constant `C` is dimensional
(it comes from the Chernoff threshold and the polynomial size of the test-tube net). -/
noncomputable def rigidMED (C : ℝ) (δ : NNReal) : ℕ :=
  ⌈C * (1 + Real.log (1 / (δ : ℝ)))⌉₊ + 1

theorem one_le_rigidMED (C : ℝ) (δ : NNReal) : 1 ≤ rigidMED C δ := by
  simp [rigidMED]

/-- `rigidMED` is dominated by a degree-one polylogarithm. -/
theorem rigidMED_le_polylog {C : ℝ} (hC : 0 < C) (δ : NNReal) (hδ : 0 < δ) (hδ1 : (δ : ℝ) ≤ 1) :
    ((rigidMED C δ : ℕ) : ℝ) ≤ (C + 2) * (1 + Real.log (1 / (δ : ℝ))) ^ 1 := by
  let L : ℝ := 1 + Real.log (1 / (δ : ℝ))
  have hδR : 0 < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hone : (1 : ℝ) ≤ 1 / (δ : ℝ) := one_le_one_div hδR hδ1
  have hlog : 0 ≤ Real.log (1 / (δ : ℝ)) := Real.log_nonneg hone
  have hL : (1 : ℝ) ≤ L := by
    dsimp [L]
    linarith
  have hx : 0 ≤ C * L := by
    exact mul_nonneg (le_of_lt hC) (by linarith)
  have hceil : ((⌈C * L⌉₊ : ℕ) : ℝ) ≤ C * L + 1 := (Nat.ceil_lt_add_one hx).le
  have hcard : ((rigidMED C δ : ℕ) : ℝ) = ((⌈C * L⌉₊ : ℕ) : ℝ) + 1 := by
    simp [rigidMED, L]
  have hp : (1 + Real.log (1 / (δ : ℝ))) ^ 1 = L := by
    dsimp [L]
    rw [pow_one]
  rw [hp]
  calc
    ((rigidMED C δ : ℕ) : ℝ) = ((⌈C * L⌉₊ : ℕ) : ℝ) + 1 := hcard
    _ ≤ C * L + 1 + 1 := by nlinarith [hceil]
    _ = C * L + 2 := by ring
    _ ≤ (C + 2) * L := by nlinarith [hL]

/-- The square of `rigidMED` is dominated by a degree-two polylogarithm. This is the shape the old
quadratic `S6` conjunct needs. -/
theorem rigidMED_sq_le_polylog {C : ℝ} (hC : 0 < C) (δ : NNReal) (hδ : 0 < δ)
    (hδ1 : (δ : ℝ) ≤ 1) :
    ((rigidMED C δ : ℕ) : ℝ) * (((rigidMED C δ : ℕ) : ℝ) + 1)
      ≤ ((C + 2) * (C + 3)) * (1 + Real.log (1 / (δ : ℝ))) ^ 2 := by
  let L : ℝ := 1 + Real.log (1 / (δ : ℝ))
  let R := ((rigidMED C δ : ℕ) : ℝ)
  let A : ℝ := (C + 2) * L
  have hA : A = (C + 2) * L := rfl
  have hδR : 0 < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hone : (1 : ℝ) ≤ 1 / (δ : ℝ) := one_le_one_div hδR hδ1
  have hlog : 0 ≤ Real.log (1 / (δ : ℝ)) := Real.log_nonneg hone
  have hL : (1 : ℝ) ≤ L := by
    dsimp [L]
    linarith
  have hC2 : 0 ≤ C + 2 := by linarith
  have hLnn : 0 ≤ L := by linarith [hL]
  have hAnnn : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg hC2 hLnn
  have hR_le : R ≤ A := by
    have hmain := rigidMED_le_polylog hC δ hδ hδ1
    have hp : (1 + Real.log (1 / (δ : ℝ))) ^ 1 = L := by
      dsimp [L]
      rw [pow_one]
    rw [hp] at hmain
    change ((rigidMED C δ : ℕ) : ℝ) ≤ (C + 2) * L
    exact hmain
  have hR1 : (1 : ℝ) ≤ R := by
    change (1 : ℝ) ≤ ((rigidMED C δ : ℕ) : ℝ)
    exact_mod_cast one_le_rigidMED C δ
  have hR1nn : 0 ≤ R + 1 := by linarith
  have hA1nn : 0 ≤ A + 1 := by linarith
  have hA1le : A + 1 ≤ (C + 3) * L := by
    rw [hA]
    nlinarith [hL]
  have hsp1 : R * (R + 1) ≤ A * (A + 1) :=
    mul_le_mul hR_le (by linarith) hR1nn hAnnn
  have hsp2 : A * (A + 1) ≤ A * ((C + 3) * L) :=
    mul_le_mul (le_of_eq rfl) hA1le hA1nn hAnnn
  have hryt : A * ((C + 3) * L) = (C + 2) * (C + 3) * L * L := by
    rw [hA]
    ring
  have hp2 : (1 + Real.log (1 / (δ : ℝ))) ^ 2 = L * L := by
    dsimp [L]
    rw [pow_two]
  rw [hp2]
  calc
    R * (R + 1) ≤ A * (A + 1) := hsp1
    _ ≤ A * ((C + 3) * L) := hsp2
    _ = (C + 2) * (C + 3) * L * L := hryt
    _ = ((C + 2) * (C + 3)) * (L * L) := by ring

/-- `rigidMED` is eventually absorbed by every negative power of `δ`. -/
theorem rigidMED_eventually_le_rpow_neg {C η : ℝ} (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ((rigidMED C δ : ℕ) : ℝ) ≤ (δ : ℝ) ^ (-η) :=
  eventually_le_rpow_neg_of_le_polylog (by linarith : (0 : ℝ) < C + 2) hη 1
    (fun δ hδ hδ1 => rigidMED_le_polylog hC δ hδ hδ1)

/-- The quadratic form of the cap is also eventually absorbed. -/
theorem rigidMED_sq_eventually_le_rpow_neg {C η : ℝ} (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ((rigidMED C δ : ℕ) : ℝ) * (((rigidMED C δ : ℕ) : ℝ) + 1) ≤ (δ : ℝ) ^ (-η) :=
  eventually_le_rpow_neg_of_le_polylog
    (by nlinarith : (0 : ℝ) < (C + 2) * (C + 3)) hη 2
    (fun δ hδ hδ1 => rigidMED_sq_le_polylog hC δ hδ hδ1)

end Kakeya

end
