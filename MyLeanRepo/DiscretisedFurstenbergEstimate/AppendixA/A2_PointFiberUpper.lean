module

/-
  PointFiber Upper Bound Lemma

  Proves: |pointFiber(p, U)| ≤ Δ^{-s-7ε}

  The geometric constant 6^s (from InParent → dist < 6Δ via general antilipschitz, B=3)
  is absorbed into one ε: input bound C₁*M ≤ Δ^{-2s-6ε} → intermediate 6^s·Δ^{-s-6ε}
  → absorb 6^s ≤ Δ^{-ε} → final Δ^{-s-7ε}.
  The bound 6^s ≤ Δ^{-ε} follows from hK_loss (6 ≤ Δ^{-ε}) since 6^s ≤ 6.

  This is a 1ε relaxation vs the per-coarse upper bound (which has no
  geometric constant factor). A2_SquareData.h_pointFiber_upper must use -7ε.

  Whiteprint node: appendix_a_alternative / a2_main / pointFiber_upper
  Dependencies: Interfaces, QTTC_Assembly, AffineLineLipschitzTransfer, A9_Helpers
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A9_Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineLipschitzTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.QTTC_Assembly
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA

open LemmaE
open TubesAndSlopes
open AffineLineLipschitzTransfer

/-! ========================================================================
   Geometric adapter lemmas
   ======================================================================== -/

/-- Equal floor implies |x - y| < 1. -/
private lemma floor_eq_imp_abs_lt_one {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  let k : ℤ := ⌊x⌋
  have hk : ⌊y⌋ = k := h.symm
  have h1 : (k : ℝ) ≤ x := Int.floor_le x
  have h2 : x < (k : ℝ) + 1 := Int.lt_floor_add_one x
  have h3 : (k : ℝ) ≤ y := by
    have h3a : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    rw [hk] at h3a; exact h3a
  have h4 : y < (k : ℝ) + 1 := by
    have h4a : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
    rw [hk] at h4a; exact h4a
  have h5 : x - y < 1 := by linarith
  have h6 : y - x < 1 := by linarith
  rw [abs_lt] <;> constructor <;> linarith

/-- Same parent cell ⇒ parameter distance < Δ. -/
private lemma sameCell_paramDist_lt_delta (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (T U : FineTube) (h : InParent Δ hΔ_pos T U) :
    dist (tubeSlope T, tubeIntercept T) (tubeSlope U, tubeIntercept U) < Δ := by
  let aT := tubeSlope T; let bT := tubeIntercept T
  let aU := tubeSlope U; let bU := tubeIntercept U
  have hΔ_ne : Δ ≠ 0 := hΔ_pos.ne'
  have h_cell1 : ⌊aT / Δ⌋ = ⌊aU / Δ⌋ := by
    simpa [parentCell, InParent] using congr_arg Prod.fst h
  have h_cell2 : ⌊bT / Δ⌋ = ⌊bU / Δ⌋ := by
    simpa [parentCell, InParent] using congr_arg Prod.snd h
  have ha : |aT - aU| < Δ := by
    have h3 : |aT / Δ - aU / Δ| < 1 := floor_eq_imp_abs_lt_one h_cell1
    have h4 : |aT - aU| = Δ * |aT / Δ - aU / Δ| := by
      have h5 : aT - aU = Δ * (aT / Δ - aU / Δ) := by field_simp [hΔ_ne] <;> ring
      rw [h5, abs_mul, abs_of_pos hΔ_pos]
    rw [h4]; nlinarith
  have hb : |bT - bU| < Δ := by
    have h3 : |bT / Δ - bU / Δ| < 1 := floor_eq_imp_abs_lt_one h_cell2
    have h4 : |bT - bU| = Δ * |bT / Δ - bU / Δ| := by
      have h5 : bT - bU = Δ * (bT / Δ - bU / Δ) := by field_simp [hΔ_ne] <;> ring
      rw [h5, abs_mul, abs_of_pos hΔ_pos]
    rw [h4]; nlinarith
  have h_main : dist (aT, bT) (aU, bU) = max (|aT - aU|) (|bT - bU|) := by
    simp [Prod.dist_eq] <;> rfl
  rw [h_main]; exact max_lt ha hb

/-- InParent ⇒ dist < 6Δ via affineLine_antilipschitz_general (B=3, constant 6). -/
private lemma inParent_dist_lt_sixDelta (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (T : FineTube) (U : CoarseTube) (h : InParent Δ hΔ_pos T U)
    (hvT : (getDirV T) 1 ≠ 0) (hvU : (getDirV U) 1 ≠ 0)
    (haT : |tubeSlope T| ≤ 1) (haU : |tubeSlope U| ≤ 1)
    (hbT : |tubeIntercept T| ≤ 3) (hbU : |tubeIntercept U| ≤ 3) :
    dist T U < 6 * Δ := by
  have h_param : dist (tubeSlope T, tubeIntercept T) (tubeSlope U, tubeIntercept U) < Δ :=
    sameCell_paramDist_lt_delta Δ hΔ_pos T U h
  have h_antilipschitz : dist T U ≤ 6 * dist (tubeSlope T, tubeIntercept T) (tubeSlope U, tubeIntercept U) := by
    have h := affineLine_antilipschitz_general (by norm_num) T U hvT hvU hbU
    have h6 : (3 + 3 : ℝ) = 6 := by norm_num
    rw [h6] at h
    exact h
  calc dist T U
    ≤ 6 * dist (tubeSlope T, tubeIntercept T) (tubeSlope U, tubeIntercept U) := h_antilipschitz
  _ < 6 * Δ := by
    have h7 : 6 * dist (tubeSlope T, tubeIntercept T) (tubeSlope U, tubeIntercept U) < 6 * Δ :=
      mul_lt_mul_of_pos_left h_param (by norm_num)
    linarith

/-! ========================================================================
   Main lemma: pointFiber upper bound with constant absorbed into ε
   ======================================================================== -/

/-- Per-point pointFiber upper bound: |pointFiber(p, U)| ≤ Δ^{-s-7ε}.

    Uses BallGrowth at radius 6Δ (via InParent → dist < 6Δ).
    The 6^s geometric factor is absorbed into one ε:
      - Input: C₁*M ≤ Δ^{-2s-6ε} (existing A2_Smallness.hM_upper)
      - Intermediate: 6^s * Δ^{-s-6ε}
      - Absorb: 6^s ≤ Δ^{-ε} ⇒ final ≤ Δ^{-s-7ε}

    The absorption 6^s ≤ Δ^{-ε} follows from A2_Smallness.hK_loss combined with
    QTTC's 1 ≤ K ≤ A*(log(2/Δ))^A, which gives 6 ≤ Δ^{-ε}; and 6^s ≤ 6
    since 0 ≤ s < 1. -/
lemma pointFiber_upper_bound
    (δ Δ s ε C₁ M : ℝ) (p : Plane)
    (T : Plane → Finset FineTube) (T_Q : Plane → Finset FineTube) (U : CoarseTube)
    (hδ_le_Δ : δ ≤ Δ) (hΔ_pos : 0 < Δ)
    (h_finite : BallGrowth δ s C₁ (T p))
    (hT_Q_sub : T_Q p ⊆ T p)
    (h_card : ((T p).card : ℝ) ≤ M)
    (hM_upper : C₁ * M ≤ Real.rpow Δ (-2 * s - 6 * ε))
    (hs_nonneg : 0 ≤ s)
    (hε_pos : 0 < ε)
    (hΔ_lt_one : Δ ≤ 1)
    (h_const_absorb : (6 : ℝ)^s ≤ Real.rpow Δ (-ε))
    (h_bounds : ∀ T_fine ∈ T p,
      (getDirV T_fine) 1 ≠ 0 ∧ |tubeSlope T_fine| ≤ 1 ∧ |tubeIntercept T_fine| ≤ 3)
    (hvU : (getDirV U) 1 ≠ 0)
    (haU : |tubeSlope U| ≤ 1)
    (hbU : |tubeIntercept U| ≤ 3) :
    (pointFiber Δ hΔ_pos T_Q p U).card ≤ Real.rpow Δ (-s - 7 * ε) := by
  -- Step 1: pointFiber ⊆ metric filter at radius 5Δ
  have h1 : pointFiber Δ hΔ_pos T_Q p U ⊆ (T p).filter (fun ℓ => dist ℓ U ≤ 6 * Δ) := by
    intro T_fine hT_fine
    have h2 : T_fine ∈ T_Q p := (Finset.mem_filter.mp hT_fine).1
    have h3 : InParent Δ hΔ_pos T_fine U := (Finset.mem_filter.mp hT_fine).2
    have h4 : T_fine ∈ T p := hT_Q_sub h2
    have h_bounds' := h_bounds T_fine h4
    have h_dist : dist T_fine U < 6 * Δ :=
      inParent_dist_lt_sixDelta Δ hΔ_pos T_fine U h3
        h_bounds'.1 hvU h_bounds'.2.1 haU h_bounds'.2.2 hbU
    exact Finset.mem_filter.mpr ⟨h4, h_dist.le⟩
  have h4 : δ ≤ 6 * Δ := by linarith
  -- Step 2: BallGrowth bound at radius 5Δ
  have h5 : (((T p).filter (fun ℓ => dist ℓ U ≤ 6 * Δ)).card : ℝ) ≤
      C₁ * (6 * Δ) ^ s * (T p).card :=
    h_finite.growth U (6 * Δ) h4
  have h6 : (pointFiber Δ hΔ_pos T_Q p U).card ≤
      ((T p).filter (fun ℓ => dist ℓ U ≤ 6 * Δ)).card :=
    Finset.card_le_card h1
  have h7 : ((pointFiber Δ hΔ_pos T_Q p U).card : ℝ) ≤
      (((T p).filter (fun ℓ => dist ℓ U ≤ 6 * Δ)).card : ℝ) := by
    exact_mod_cast h6
  -- Step 3: Bound |T p| by M
  have hC1 : 0 ≤ C₁ := by
    have h : 1 ≤ C₁ := h_finite.C_one
    linarith
  have hΔs : 0 ≤ (6 * Δ) ^ s := by positivity
  have hpos : 0 ≤ C₁ * (6 * Δ) ^ s := mul_nonneg hC1 hΔs
  have h8 : C₁ * (6 * Δ) ^ s * ((T p).card : ℝ) ≤ C₁ * (6 * Δ) ^ s * M :=
    mul_le_mul_of_nonneg_left h_card hpos
  -- Step 4: Factor out 6^s
  have h9 : (6 * Δ) ^ s = (6 : ℝ) ^ s * Δ ^ s := by
    rw [Real.mul_rpow (by norm_num) hΔ_pos.le] <;> ring
  -- Step 5: Calculate 6^s * Δ^{-s-6ε}
  have h10 : ((pointFiber Δ hΔ_pos T_Q p U).card : ℝ) ≤
      (6 : ℝ)^s * Real.rpow Δ (-s - 6 * ε) := by
    calc ((pointFiber Δ hΔ_pos T_Q p U).card : ℝ)
      ≤ C₁ * (6 * Δ) ^ s * ↑((T p).card) := h7.trans h5
    _ ≤ C₁ * (6 * Δ) ^ s * M := h8
    _ = (C₁ * M) * (6 * Δ) ^ s := by ring
    _ ≤ Real.rpow Δ (-2 * s - 6 * ε) * (6 * Δ) ^ s := by
      exact mul_le_mul_of_nonneg_right hM_upper hΔs
    _ = Real.rpow Δ (-2 * s - 6 * ε) * ((6 : ℝ) ^ s * Δ ^ s) := by rw [h9]
    _ = (6 : ℝ) ^ s * (Real.rpow Δ (-2 * s - 6 * ε) * Δ ^ s) := by ring
    _ = (6 : ℝ) ^ s * Real.rpow Δ (-s - 6 * ε) := by
      have h11 : Real.rpow Δ (-2 * s - 6 * ε) * Δ ^ s =
          Real.rpow Δ (-s - 6 * ε) := by
        have h12 : Δ ^ s = Real.rpow Δ s := by rfl
        rw [h12]
        have h13 : Real.rpow Δ (-2 * s - 6 * ε) * Real.rpow Δ s =
            Real.rpow Δ ((-2 * s - 6 * ε) + s) :=
          (Real.rpow_add hΔ_pos (-2 * s - 6 * ε) s).symm
        rw [h13]
        have h14 : (-2 * s - 6 * ε) + s = -s - 6 * ε := by ring
        rw [h14]
      rw [h11] <;> ring
  -- Step 6: Absorb 6^s into ε
  have h_rpow_nonneg : 0 ≤ Real.rpow Δ (-s - 6 * ε) :=
    Real.rpow_nonneg (by linarith) _
  have h11 : (6 : ℝ)^s * Real.rpow Δ (-s - 6 * ε) ≤
      Real.rpow Δ (-ε) * Real.rpow Δ (-s - 6 * ε) :=
    mul_le_mul_of_nonneg_right h_const_absorb h_rpow_nonneg
  have h12 : Real.rpow Δ (-ε) * Real.rpow Δ (-s - 6 * ε) =
      Real.rpow Δ (-s - 7 * ε) := by
    have h13 : Real.rpow Δ (-ε) * Real.rpow Δ (-s - 6 * ε) =
        Real.rpow Δ ((-ε) + (-s - 6 * ε)) :=
      (Real.rpow_add hΔ_pos (-ε) (-s - 6 * ε)).symm
    rw [h13]
    have h14 : (-ε) + (-s - 6 * ε) = -s - 7 * ε := by ring
    rw [h14]
  -- Step 7: Combine
  have h_final : ((pointFiber Δ hΔ_pos T_Q p U).card : ℝ) ≤
      Real.rpow Δ (-s - 7 * ε) :=
    calc ((pointFiber Δ hΔ_pos T_Q p U).card : ℝ)
      ≤ (6 : ℝ)^s * Real.rpow Δ (-s - 6 * ε) := h10
    _ ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-s - 6 * ε) := h11
    _ = Real.rpow Δ (-s - 7 * ε) := h12
  exact_mod_cast h_final

/-- Derive `6^s ≤ Δ^{-ε}` from `6 ≤ Δ^{-ε}` and `0 ≤ s < 1`.

    Since `6 > 1` and `0 ≤ s < 1`, we have `6^s ≤ 6^1 = 6 ≤ Δ^{-ε}`.
    The bound `6 ≤ Δ^{-ε}` follows from A2_Smallness.hK_loss combined with
    `1 ≤ A * (log(2/Δ))^A` (from QTTC: `1 ≤ K ≤ A * (log(2/Δ))^A`). -/
lemma absorb_6_pow_s
    (Δ s ε : ℝ) (hΔ_pos : 0 < Δ) (hε_pos : 0 < ε)
    (hs_nonneg : 0 ≤ s) (hs_lt_one : s < 1)
    (h6_loss : (6 : ℝ) ≤ Real.rpow Δ (-ε)) :
    (6 : ℝ)^s ≤ Real.rpow Δ (-ε) := by
  have h1 : (6 : ℝ)^s ≤ (6 : ℝ) := by
    have h2 : s ≤ (1 : ℝ) := by linarith
    have h3 : (6 : ℝ)^s ≤ (6 : ℝ)^(1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
    simpa using h3
  linarith

end DirecretisedFurstenbergEstimate.AppendixA
