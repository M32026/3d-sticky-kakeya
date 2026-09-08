/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.CoarseDensity

/-!
# Main Lemma 1, Case (ii): The bracketed term

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

/-! ### The bracketed term -/

section Bracket

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The bracketed term `b² |𝕋̃_b|` is close to `1`** (blueprint
`lem:ml1bootBracketTwoSided`).

There is an absolute constant `c₃ ≥ 1`, depending only on the ambient dimension `3`, such
that for a nonempty family of `b`-tubes in `B₁ ⊆ ℝ³` with
`C_F(𝕋̃_b, B₁) ≤ C_F^b` and `Δ_max(𝕋̃_b) ≤ C_Δ δ̃ ^ (-h)`,

`(c₃ C_F^b)⁻¹ ≤ b² |𝕋̃_b| ≤ c₃ C_Δ δ̃ ^ (-h)`.

A `b`-tube in `ℝ³` has volume comparable to `b²`, so `Δ(𝕋̃_b, B₁) ∼ b² |𝕋̃_b|`; the upper
bound is then `Δ(𝕋̃_b, B₁) ≤ Δ_max(𝕋̃_b)`, and the lower bound comes from
`Δ_max(𝕋̃_b) ≥ 1` together with `ConvexSpaceBody.isFrostmanIn_frostmanConstIn`.

The family is **not** asked to be pairwise essentially distinct.  Earlier revisions asked for
it and never used it: the estimate is a per-tube volume comparison (`Tube.le_volume`,
`Tube.volume_le`) followed by monotonicity of `densityIn` and `maxDensity`, with no packing
count anywhere, so the hypothesis was inert.  Nothing replaces it — in particular not the
bounded overlap of `Tube.HasBoundedOverlap`, which would be equally inert here and
which the `b`-tubes cannot supply.  Duplication in the family is harmless because both sides
scale with `|𝕋̃_b|` in the same way.  See blueprint `note:ml1bootCoarseEDInert`.

`C_F^b` is a parameter rather than a power of `δ̃`, so that the routing of the hypothesis
`C_F^b ≤ C_Δ δ̃ ^ (-η'_{j-1})` through `Kakeya.ml1Boot.exists_frostmanConstIn_coarse_le` stays
visible in the assembly; likewise the density exponent is the bare real `h`, instantiated at
`30 ε + η'_{j-1}` in `Kakeya.ml1Boot.multiplicity_coarse_le`. -/
theorem bracket_mem_Icc (hdim : Module.finrank ℝ E = 3) :
    ∃ c₃ : NNReal, 1 ≤ c₃ ∧
      ∀ {δt b : NNReal}, 0 < δt → δt ≤ b → b ≤ 1 →
      ∀ {CFb : ENNReal}, 1 ≤ CFb → ∀ {CΔ : NNReal}, 1 ≤ CΔ → ∀ {h : ℝ}, 0 ≤ h →
      ∀ {κ : Type*} {t : Finset κ} (Tb : κ → Tube b E),
        t.Nonempty →
        (∀ l ∈ t, (Tb l).carrier ⊆ Metric.closedBall 0 1) →
        frostmanConstIn t (fun l => (Tb l).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall ≤ CFb →
        maxDensity t (fun l => (Tb l).toConvexSpaceBody)
            ≤ (CΔ : ENNReal) * (δt : ENNReal) ^ (-h) →
        ((c₃ : ENNReal) * CFb)⁻¹ ≤ (t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ) ∧
          (t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ)
            ≤ (c₃ : ENNReal) * (CΔ : ENNReal) * (δt : ENNReal) ^ (-h) := by
  haveI : Nontrivial E := Module.finrank_pos_iff.mp (by rw [hdim]; norm_num)
  let n : ℕ := Module.finrank ℝ E
  let m : NNReal := Tube.le_volume.c n
  let M : NNReal := Tube.volume_le.C n
  let r : NNReal := M / (3 * m)
  let c₃ : NNReal := max 3 r
  have h_one_le_c3 : 1 ≤ c₃ := le_trans (by norm_num : (1 : NNReal) ≤ 3) (le_max_left 3 r)
  refine ⟨c₃, h_one_le_c3, ?_⟩
  intro δt b hδt hδb hb1 CFb hCFb1 CΔ hCΔ1 h hh κ t Tb ht_nonempty hball hfrost
    hmaxdens
  let d : ENNReal := (b : ENNReal)
  set W : κ → ConvexSpaceBody E := fun l => (Tb l).toConvexSpaceBody with hW
  set B₁ : ConvexSpaceBody E := ConvexSpaceBody.closedUnitBall with hB₁
  set V₁ : ENNReal := volume B₁.carrier with hV₁
  set S : ENNReal := ∑ l ∈ t, volume (W l).carrier with hS
  have hn : n = 3 := by simpa [n] using hdim
  have htwo : n - 1 = 2 := by omega
  -- tubes in the unit ball, in `≤` form
  have hT : ∀ l ∈ t, W l ≤ B₁ := by
    intro l hl x hx
    simpa [W, B₁, ConvexSpaceBody.mem_closedUnitBall] using hball l hl hx
  -- Frostman property at the `b`-tube scale
  have hfrostW : frostmanConstIn t W B₁ ≤ CFb := by simpa [W, B₁] using hfrost
  have hFr : IsFrostmanIn t W B₁ CFb := by
    simpa [W, B₁] using isFrostmanIn_of_frostmanConstIn_le (s := t)
      (W := fun l => (Tb l).toConvexSpaceBody) (K := ConvexSpaceBody.closedUnitBall) hfrost
  have hmax_le : maxDensity t W ≤ CFb * densityIn t W B₁ := by
    simpa using hFr.maxDensity_le_of_carrier_subset hT
  -- non-degeneracy
  have hpos_b : 0 < b := lt_of_lt_of_le hδt hδb
  have hd_ne : d ≠ 0 := by dsimp [d]; exact ENNReal.coe_ne_zero.mpr (ne_of_gt hpos_b)
  have hm_ne : (m : ENNReal) ≠ 0 := by
    dsimp [m]
    exact ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos n).ne'
  have hV₁ne0 : V₁ ≠ 0 := by
    dsimp [V₁, B₁]
    exact ne_of_gt ConvexSpaceBody.closedUnitBall_volume_pos
  have hV₁top : V₁ ≠ ⊤ := by
    dsimp [V₁, B₁]
    exact ConvexSpaceBody.closedUnitBall.isCompact.measure_ne_top
  have hV₁eq : V₁ = ((3 * m : NNReal) : ENNReal) := by
    dsimp [V₁, B₁, m, n]
    exact volume_closedUnitBall_eq (E := E)
  have hV₁prod : V₁ = (3 : ENNReal) * (m : ENNReal) := by
    rw [hV₁eq, ENNReal.coe_mul]
    simp
  -- per-tube volume comparisons
  have per_lower : ∀ l ∈ t, (m : ENNReal) * d ^ 2 ≤ volume (W l).carrier := by
    intro l hl
    have hv := (Tb l).le_volume
    simpa [W, m, n, d, htwo] using hv
  have per_upper : ∀ l ∈ t, volume (W l).carrier ≤ (M : ENNReal) * d ^ 2 := by
    intro l hl
    have hv := Tube.volume_le hb1 (Tb l)
    simpa [W, M, n, d, htwo] using hv
  -- positive-volume member (for `1 ≤ maxDensity`)
  have hvol_pos : ∀ l ∈ t, 0 < volume (W l).carrier := by
    intro l hl
    have hle := (Tb l).le_volume
    have hpow_ne : d ^ (n - 1) ≠ 0 := ENNReal.pow_ne_zero hd_ne (n - 1)
    have hprod_pos : 0 < (m : ENNReal) * d ^ (n - 1) := ENNReal.mul_pos hm_ne hpow_ne
    simpa [W, m, d, n] using hprod_pos.trans_le hle
  obtain ⟨l0, hl0⟩ := ht_nonempty
  have hmd1 : 1 ≤ maxDensity t W := one_le_maxDensity (s := t) (W := W) ⟨l0, hl0, hvol_pos l0 hl0⟩
  -- density spells as `S / V₁`
  have hdens_all : densityIn t W B₁ = S / V₁ := by
    simpa [W, B₁, V₁, S] using densityIn_of_all_le (s := t) (W := W) (K := B₁) hT
  -- sum bounds
  have hS_upper : S ≤ (t.card : ENNReal) * (M : ENNReal) * d ^ 2 := by
    calc
      S = ∑ l ∈ t, volume (W l).carrier := rfl
      _ ≤ ∑ _l ∈ t, ((M : ENNReal) * d ^ 2) := by
        exact Finset.sum_le_sum (fun l hl => per_upper l hl)
      _ = (t.card : ENNReal) * (M : ENNReal) * d ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hS_lower : (t.card : ENNReal) * (m : ENNReal) * d ^ 2 ≤ S := by
    calc
      (t.card : ENNReal) * (m : ENNReal) * d ^ 2 = ∑ _l ∈ t, ((m : ENNReal) * d ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ ∑ l ∈ t, volume (W l).carrier := by
        exact Finset.sum_le_sum (fun l hl => per_lower l hl)
      _ = S := rfl
  -- coefficient identity `(M:ENNReal)/V₁ = r`
  have h3m_ne : (3 * m : NNReal) ≠ 0 :=
    mul_ne_zero (by norm_num : (3 : NNReal) ≠ 0) (Tube.le_volume.c_pos n).ne'
  have hMV : (M : ENNReal) / V₁ = (r : ENNReal) := by
    dsimp [r]
    rw [hV₁eq]
    rw [← ENNReal.coe_div h3m_ne]
  -- (L1) upper bound of the bracket: `A·d² ≤ 3·densityIn`
  have hA_le3 : (t.card : ENNReal) * d ^ 2 ≤ 3 * densityIn t W B₁ := by
    have h1 : (t.card : ENNReal) * (m : ENNReal) * d ^ 2
        ≤ 3 * densityIn t W B₁ * (m : ENNReal) := by
      calc
        (t.card : ENNReal) * (m : ENNReal) * d ^ 2 ≤ S := hS_lower
        _ = densityIn t W B₁ * V₁ := by
          rw [hS, ← sum_volume_eq_densityIn_mul_volume' (s := t) (W := W) (K := B₁) hT]
        _ = 3 * densityIn t W B₁ * (m : ENNReal) := by
          rw [hV₁prod]
          ac_rfl
    have hm_top : (m : ENNReal) ≠ ⊤ := by exact ENNReal.coe_ne_top
    exact (ENNReal.mul_le_mul_iff_left hm_ne hm_top).mp
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using h1)
  -- (L2) `densityIn ≤ r · (t.card) · d²`
  have hdens_le : densityIn t W B₁ ≤ (r : ENNReal) * (t.card : ENNReal) * d ^ 2 := by
    rw [hdens_all]
    calc
      S / V₁ ≤ ((t.card : ENNReal) * (M : ENNReal) * d ^ 2) / V₁ := by
        exact ENNReal.div_le_div_right hS_upper V₁
      _ = (t.card : ENNReal) * d ^ 2 * ((M : ENNReal) / V₁) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ac_rfl
      _ = (t.card : ENNReal) * d ^ 2 * (r : ENNReal) := by rw [hMV]
      _ = (r : ENNReal) * (t.card : ENNReal) * d ^ 2 := by ac_rfl
  -- lower bound: `1 ≤ c₃·CFb·A·d²`
  have h_lower : 1 ≤ (c₃ : ENNReal) * CFb * (t.card : ENNReal) * d ^ 2 := by
    have h1 : 1 ≤ CFb * ((r : ENNReal) * (t.card : ENNReal) * d ^ 2) :=
      le_trans (le_trans hmd1 hmax_le) (mul_le_mul_right hdens_le CFb)
    have h2 : 1 ≤ (r : ENNReal) * CFb * (t.card : ENNReal) * d ^ 2 := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using h1
    have hrc : (r : ENNReal) ≤ (c₃ : ENNReal) :=
      ENNReal.coe_le_coe.mpr (le_max_right 3 r)
    have hrc' : (r : ENNReal) * CFb * (t.card : ENNReal) * d ^ 2
        ≤ (c₃ : ENNReal) * CFb * (t.card : ENNReal) * d ^ 2 := by
      gcongr
    exact le_trans h2 hrc'
  -- upper bound: `A·d² ≤ c₃·CΔ·δt^(-h)`
  have h_up : (t.card : ENNReal) * d ^ 2
      ≤ (c₃ : ENNReal) * (CΔ : ENNReal) * (δt : ENNReal) ^ (-h) := by
    have h3c : (3 : ENNReal) ≤ (c₃ : ENNReal) :=
      ENNReal.coe_le_coe.mpr (le_max_left 3 r)
    calc
      (t.card : ENNReal) * d ^ 2 ≤ 3 * densityIn t W B₁ := hA_le3
      _ ≤ 3 * maxDensity t W :=
        mul_le_mul_right (le_maxDensity (s := t) (W := W) B₁) (3 : ENNReal)
      _ ≤ 3 * ((CΔ : ENNReal) * (δt : ENNReal) ^ (-h)) :=
        mul_le_mul_right hmaxdens (3 : ENNReal)
      _ ≤ (c₃ : ENNReal) * ((CΔ : ENNReal) * (δt : ENNReal) ^ (-h)) :=
        mul_le_mul_left h3c ((CΔ : ENNReal) * (δt : ENNReal) ^ (-h))
      _ = (c₃ : ENNReal) * (CΔ : ENNReal) * (δt : ENNReal) ^ (-h) := by
        rw [mul_assoc]
  -- assemble
  constructor
  · -- (c₃·CFb)⁻¹ ≤ A·d²
    have htcard_pos : 0 < t.card := Finset.card_pos.mpr ⟨l0, hl0⟩
    have hAc_ne0 : (t.card : ENNReal) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt htcard_pos)
    have h_Ad_ne0 : (t.card : ENNReal) * d ^ 2 ≠ 0 :=
      mul_ne_zero hAc_ne0 (ENNReal.pow_ne_zero hd_ne 2)
    have h_c3CFb_ne0 : (c₃ : ENNReal) * CFb ≠ 0 :=
      mul_ne_zero (ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one h_one_le_c3)))
        (ne_of_gt (lt_of_lt_of_le zero_lt_one hCFb1))
    rw [ENNReal.inv_le_iff_le_mul (by intro h; exact h_c3CFb_ne0)
      (by intro h; exact h_Ad_ne0)]
    simpa [mul_assoc, mul_comm, mul_left_comm] using h_lower
  · simpa [d] using h_up

/-- **The volume of `B̄(0,R)` is `R ^ n` times that of the unit ball.**

The companion of `Kakeya.volume_closedBall_eq_ccov_mul_pow`, which computes the same volume
against an absolute constant; here the reference is the unit ball itself, which is what the
`densityIn` of `Kakeya.ml1Boot.bracket_mem_Icc_ball` divides by.  The power is the natural
power `R ^ Module.finrank ℝ E`, not an `rpow`. -/
theorem volume_closedBall_eq_pow_mul (R : ℝ) (hR : 0 ≤ R) :
    volume (Metric.closedBall (0 : E) R)
      = ENNReal.ofReal (R ^ Module.finrank ℝ E) * volume (Metric.closedBall (0 : E) 1) := by
  have hb := MeasureTheory.Measure.addHaar_closedBall (volume : Measure E) (0 : E) hR
  have hb1 := MeasureTheory.Measure.addHaar_closedBall (volume : Measure E) (0 : E)
    (zero_le_one : (0 : ℝ) ≤ 1)
  rw [hb, hb1]
  simp

/-- **`Kakeya.ml1Boot.bracket_mem_Icc` at an ambient radius `R ≥ 1`.**

Identical statement, with `B₁` replaced by `B̄(0,R)` in both the containment hypothesis and
the ambient body of the Frostman constant, and with the constant `c₃` replaced by
`max (3 R³) r` — the *only* change.  Nothing in the exponents moves: the unit ball enters this
lemma purely as the reference volume of `densityIn`, and rescaling that volume by `R³` is a
constant charge on `c₃`. -/
theorem bracket_mem_Icc_ball (hdim : Module.finrank ℝ E = 3) (R : NNReal) (hR : 1 ≤ R) :
    ∃ c₃ : NNReal, 1 ≤ c₃ ∧
      ∀ {δt b : NNReal}, 0 < δt → δt ≤ b → b ≤ 1 →
      ∀ {CFb : ENNReal}, 1 ≤ CFb → ∀ {CΔ : NNReal}, 1 ≤ CΔ → ∀ {h : ℝ}, 0 ≤ h →
      ∀ {κ : Type*} {t : Finset κ} (Tb : κ → Tube b E),
        t.Nonempty →
        (∀ l ∈ t, (Tb l).carrier ⊆ Metric.closedBall 0 (R : ℝ)) →
        frostmanConstIn t (fun l => (Tb l).toConvexSpaceBody)
            (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg) ≤ CFb →
        maxDensity t (fun l => (Tb l).toConvexSpaceBody)
            ≤ (CΔ : ENNReal) * (δt : ENNReal) ^ (-h) →
        ((c₃ : ENNReal) * CFb)⁻¹ ≤ (t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ) ∧
          (t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ)
            ≤ (c₃ : ENNReal) * (CΔ : ENNReal) * (δt : ENNReal) ^ (-h) := by
  haveI : Nontrivial E := Module.finrank_pos_iff.mp (by rw [hdim]; norm_num)
  let n : ℕ := Module.finrank ℝ E
  let m : NNReal := Tube.le_volume.c n
  let M : NNReal := Tube.volume_le.C n
  let r : NNReal := M / (3 * m)
  let RR : NNReal := R ^ n
  let c₃ : NNReal := max (3 * RR) r
  have h_one_le_c3 : 1 ≤ c₃ := by
    refine le_trans ?_ (le_max_left (3 * RR) r)
    have hRR : (1 : NNReal) ≤ RR := one_le_pow₀ hR
    calc (1 : NNReal) ≤ 3 * 1 := by norm_num
      _ ≤ 3 * RR := by gcongr
  refine ⟨c₃, h_one_le_c3, ?_⟩
  intro δt b hδt hδb hb1 CFb hCFb1 CΔ hCΔ1 h hh κ t Tb ht_nonempty hball hfrost hmaxdens
  let d : ENNReal := (b : ENNReal)
  set W : κ → ConvexSpaceBody E := fun l => (Tb l).toConvexSpaceBody with hW
  set BR : ConvexSpaceBody E := ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg with hBR
  set VR : ENNReal := volume BR.carrier with hVR
  set S : ENNReal := ∑ l ∈ t, volume (W l).carrier with hS
  have hn : n = 3 := by simpa [n] using hdim
  have htwo : n - 1 = 2 := by omega
  -- tubes in `B̄(0,R)`, in `≤` form
  have hT : ∀ l ∈ t, W l ≤ BR := by
    intro l hl
    exact SetLike.coe_subset_coe.mpr (hball l hl)
  -- Frostman property at the `b`-tube scale
  have hFr : IsFrostmanIn t W BR CFb :=
    isFrostmanIn_of_frostmanConstIn_le (s := t) (W := W) (K := BR) hfrost
  have hmax_le : maxDensity t W ≤ CFb * densityIn t W BR :=
    hFr.maxDensity_le_of_carrier_subset hT
  -- non-degeneracy
  have hpos_b : 0 < b := lt_of_lt_of_le hδt hδb
  have hd_ne : d ≠ 0 := by dsimp [d]; exact ENNReal.coe_ne_zero.mpr (ne_of_gt hpos_b)
  have hm_ne : (m : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos n).ne'
  have hm_top : (m : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h3m_ne : (3 * m : NNReal) ≠ 0 :=
    mul_ne_zero (by norm_num : (3 : NNReal) ≠ 0) (Tube.le_volume.c_pos n).ne'
  have h3mE_ne : ((3 * m : NNReal) : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr h3m_ne
  have h3mE_top : ((3 * m : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- the volume of the ambient ball
  have hV1 : volume (Metric.closedBall (0 : E) 1) = ((3 * m : NNReal) : ENNReal) := by
    have := volume_closedUnitBall_eq (E := E)
    rw [ConvexSpaceBody.closedUnitBall_carrier] at this
    simpa [m, n] using this
  have hVReq : VR = (RR : ENNReal) * ((3 * m : NNReal) : ENNReal) := by
    have hc : BR.carrier = Metric.closedBall (0 : E) (R : ℝ) := rfl
    rw [hVR, hc, volume_closedBall_eq_pow_mul (E := E) (R : ℝ) R.coe_nonneg, hV1]
    congr 1
    rw [show ((R : ℝ) ^ Module.finrank ℝ E) = ((R ^ n : NNReal) : ℝ) by push_cast [n]; ring]
    simp [RR]
  have hRR1 : (1 : NNReal) ≤ RR := one_le_pow₀ hR
  have hRR1E : (1 : ENNReal) ≤ (RR : ENNReal) := by exact_mod_cast hRR1
  have hVR_lower : ((3 * m : NNReal) : ENNReal) ≤ VR := by
    rw [hVReq]
    calc ((3 * m : NNReal) : ENNReal) = 1 * ((3 * m : NNReal) : ENNReal) := by ring
      _ ≤ (RR : ENNReal) * ((3 * m : NNReal) : ENNReal) := by gcongr
  -- per-tube volume comparisons
  have per_lower : ∀ l ∈ t, (m : ENNReal) * d ^ 2 ≤ volume (W l).carrier := by
    intro l hl
    have hv := (Tb l).le_volume
    simpa [W, m, n, d, htwo] using hv
  have per_upper : ∀ l ∈ t, volume (W l).carrier ≤ (M : ENNReal) * d ^ 2 := by
    intro l hl
    have hv := Tube.volume_le hb1 (Tb l)
    simpa [W, M, n, d, htwo] using hv
  have hvol_pos : ∀ l ∈ t, 0 < volume (W l).carrier := by
    intro l hl
    have hle := (Tb l).le_volume
    have hpow_ne : d ^ (n - 1) ≠ 0 := ENNReal.pow_ne_zero hd_ne (n - 1)
    have hprod_pos : 0 < (m : ENNReal) * d ^ (n - 1) := ENNReal.mul_pos hm_ne hpow_ne
    simpa [W, m, d, n] using hprod_pos.trans_le hle
  obtain ⟨l0, hl0⟩ := ht_nonempty
  have hmd1 : 1 ≤ maxDensity t W := one_le_maxDensity (s := t) (W := W) ⟨l0, hl0, hvol_pos l0 hl0⟩
  -- `S = densityIn · VR`
  have hSeq : S = densityIn t W BR * VR := by
    simpa [hS, hVR] using sum_volume_eq_densityIn_mul_volume' (s := t) (W := W) (K := BR) hT
  have hS_upper : S ≤ (t.card : ENNReal) * (M : ENNReal) * d ^ 2 := by
    calc
      S = ∑ l ∈ t, volume (W l).carrier := rfl
      _ ≤ ∑ _l ∈ t, ((M : ENNReal) * d ^ 2) := Finset.sum_le_sum (fun l hl => per_upper l hl)
      _ = (t.card : ENNReal) * (M : ENNReal) * d ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hS_lower : (t.card : ENNReal) * (m : ENNReal) * d ^ 2 ≤ S := by
    calc
      (t.card : ENNReal) * (m : ENNReal) * d ^ 2 = ∑ _l ∈ t, ((m : ENNReal) * d ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ ∑ l ∈ t, volume (W l).carrier := Finset.sum_le_sum (fun l hl => per_lower l hl)
      _ = S := rfl
  -- (L1) `card · d² ≤ 3 RR · densityIn`
  have hA_le3 : (t.card : ENNReal) * d ^ 2 ≤ 3 * (RR : ENNReal) * densityIn t W BR := by
    have h1 : (m : ENNReal) * ((t.card : ENNReal) * d ^ 2)
        ≤ (m : ENNReal) * (3 * (RR : ENNReal) * densityIn t W BR) := by
      calc (m : ENNReal) * ((t.card : ENNReal) * d ^ 2)
          = (t.card : ENNReal) * (m : ENNReal) * d ^ 2 := by ring
        _ ≤ S := hS_lower
        _ = densityIn t W BR * VR := hSeq
        _ = densityIn t W BR * ((RR : ENNReal) * ((3 * m : NNReal) : ENNReal)) := by rw [hVReq]
        _ = (m : ENNReal) * (3 * (RR : ENNReal) * densityIn t W BR) := by
              rw [ENNReal.coe_mul]
              push_cast
              ring
    exact (ENNReal.mul_le_mul_iff_left hm_ne hm_top).mp
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using h1)
  -- (L2) `densityIn ≤ r · card · d²`
  have hMr0 : (r : NNReal) * (3 * m) = M := by
    dsimp [r]
    exact div_mul_cancel₀ M h3m_ne
  have hMr : (M : ENNReal) = (r : ENNReal) * ((3 * m : NNReal) : ENNReal) := by
    rw [← ENNReal.coe_mul, hMr0]
  have hdens_le : densityIn t W BR ≤ (r : ENNReal) * (t.card : ENNReal) * d ^ 2 := by
    have h1 : densityIn t W BR * ((3 * m : NNReal) : ENNReal)
        ≤ ((r : ENNReal) * (t.card : ENNReal) * d ^ 2) * ((3 * m : NNReal) : ENNReal) := by
      calc densityIn t W BR * ((3 * m : NNReal) : ENNReal)
          ≤ densityIn t W BR * VR := by gcongr
        _ = S := hSeq.symm
        _ ≤ (t.card : ENNReal) * (M : ENNReal) * d ^ 2 := hS_upper
        _ = ((r : ENNReal) * (t.card : ENNReal) * d ^ 2) * ((3 * m : NNReal) : ENNReal) := by
              rw [hMr]; ring
    exact (ENNReal.mul_le_mul_iff_left h3mE_ne h3mE_top).mp h1
  -- lower bound
  have h_lower : 1 ≤ (c₃ : ENNReal) * CFb * (t.card : ENNReal) * d ^ 2 := by
    have h1 : 1 ≤ CFb * ((r : ENNReal) * (t.card : ENNReal) * d ^ 2) :=
      le_trans (le_trans hmd1 hmax_le) (mul_le_mul_right hdens_le CFb)
    have hrc : (r : ENNReal) ≤ (c₃ : ENNReal) := ENNReal.coe_le_coe.mpr (le_max_right _ r)
    calc (1 : ENNReal) ≤ CFb * ((r : ENNReal) * (t.card : ENNReal) * d ^ 2) := h1
      _ ≤ CFb * ((c₃ : ENNReal) * (t.card : ENNReal) * d ^ 2) := by gcongr
      _ = (c₃ : ENNReal) * CFb * (t.card : ENNReal) * d ^ 2 := by ring
  -- upper bound
  have h_up : (t.card : ENNReal) * d ^ 2
      ≤ (c₃ : ENNReal) * (CΔ : ENNReal) * (δt : ENNReal) ^ (-h) := by
    have h3c : 3 * (RR : ENNReal) ≤ (c₃ : ENNReal) := by
      have : ((3 * RR : NNReal) : ENNReal) ≤ (c₃ : ENNReal) :=
        ENNReal.coe_le_coe.mpr (le_max_left _ r)
      simpa using this
    calc
      (t.card : ENNReal) * d ^ 2 ≤ 3 * (RR : ENNReal) * densityIn t W BR := hA_le3
      _ ≤ 3 * (RR : ENNReal) * maxDensity t W := by
            gcongr
            exact le_maxDensity (s := t) (W := W) BR
      _ ≤ 3 * (RR : ENNReal) * ((CΔ : ENNReal) * (δt : ENNReal) ^ (-h)) := by gcongr
      _ ≤ (c₃ : ENNReal) * ((CΔ : ENNReal) * (δt : ENNReal) ^ (-h)) := by gcongr
      _ = (c₃ : ENNReal) * (CΔ : ENNReal) * (δt : ENNReal) ^ (-h) := by rw [mul_assoc]
  refine ⟨?_, by simpa [d] using h_up⟩
  have htcard_pos : 0 < t.card := Finset.card_pos.mpr ⟨l0, hl0⟩
  have hAc_ne0 : (t.card : ENNReal) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt htcard_pos)
  have h_Ad_ne0 : (t.card : ENNReal) * d ^ 2 ≠ 0 :=
    mul_ne_zero hAc_ne0 (ENNReal.pow_ne_zero hd_ne 2)
  have h_c3CFb_ne0 : (c₃ : ENNReal) * CFb ≠ 0 :=
    mul_ne_zero (ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one h_one_le_c3)))
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hCFb1))
  rw [ENNReal.inv_le_iff_le_mul (by intro h; exact h_c3CFb_ne0)
    (by intro h; exact h_Ad_ne0)]
  simpa [mul_assoc, mul_comm, mul_left_comm] using h_lower


end Bracket

end ml1Boot

end Kakeya
