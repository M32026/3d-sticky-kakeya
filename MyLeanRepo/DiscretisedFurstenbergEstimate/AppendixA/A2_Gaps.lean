module

/-
  A2 Gaps: proved lemmas for the A2_SquareData interface.

  Contains:
  - gap3_hP_Q_sset : transfer S-set from P to P_Q via cover ratio
  - hC_Q_cover_transfer_main : Ncover(C_Q) ≤ 2000 * Ncover(slope image)
  - hC_Q_slope_sset_main : slope image is (Δ, s, Δ^{-25ε})-set
  - hC_Q_slope_cover_lower_main : Ncover(slope image) ≥ Δ^{25ε-s}
  - hC_Q_slope_cover_upper_weak : Ncover(slope image) ≤ Δ^{-1-25ε} (weak bound)

  Whiteprint node: appendix_a_alternative / A2_Gaps
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_StripPacking
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.AffineLinePackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A4_PackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A4_CQpiSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBoundedHelpers2
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA.A2_RemainingGaps

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA4
open DiscretisedFurstenbergEstimate.CoveringUtils
open LemmaE

abbrev Plane := EuclideanPlane

/-! ### GAP 3: hC_Q_slope_cover_lower

  Ncover(slope image) ≥ Δ^{25ε-s}.

  Proof:
  1. affineLine_ncover_lower: |C_Q| ≤ affinePackingM * Ncover(C_Q)
  2. cover transfer: Ncover(C_Q) ≤ 2000 * Ncover(slope)
  3. Thus |C_Q| ≤ affinePackingM * 2000 * Ncover(slope)
  4. So Ncover(slope) ≥ |C_Q| / (affinePackingM * 2000)
  5. |C_Q| ≥ Δ^{-s+11ε}
  6. Smallness: affinePackingM * 2000 ≤ Δ^{-14ε}
  7. Thus Ncover(slope) ≥ Δ^{-s+11ε} * Δ^{14ε} = Δ^{25ε-s}
-/

lemma hC_Q_slope_cover_lower_main
    {Δ s ε : ℝ} {C_Q : Finset CoarseTube}
    (hΔ_pos : 0 < Δ) (hε_pos : 0 < ε) (hΔ_lt_one : Δ < 1)
    (hs : 0 < s)
    (hC_Q_sep : SeparatedAt Δ (C_Q : Set CoarseTube))
    (hC_card_lower : Real.rpow Δ (-s + 11 * ε) ≤ (C_Q.card : ℝ))
    (h_small_pack : (2000 : ENNReal) * (affinePackingM : ENNReal) ≤
        ENNReal.ofReal (Real.rpow Δ (-14 * ε)))
    (h_cover_transfer : (Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set CoarseTube) : ENNReal) ≤
        ENNReal.ofReal (2000 : ℝ) * Metric.externalCoveringNumber Δ.toNNReal (tubeSlope '' (C_Q : Set CoarseTube))) :
    ENNReal.ofReal (Real.rpow Δ (25 * ε - s)) ≤
      Metric.externalCoveringNumber Δ.toNNReal (tubeSlope '' (C_Q : Set CoarseTube)) := by
  let Nslope := Metric.externalCoveringNumber Δ.toNNReal (tubeSlope '' (C_Q : Set CoarseTube))
  let NCQ := Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set CoarseTube)
  have h1 : (C_Q.card : ENNReal) ≤ (affinePackingM : ENNReal) * NCQ :=
    affineLine_ncover_lower hΔ_pos (hS_sep := hC_Q_sep)
  have h_transfer' : NCQ ≤ (2000 : ENNReal) * Nslope := by
    have h_eq : ENNReal.ofReal (2000 : ℝ) = (2000 : ENNReal) := by norm_cast
    rw [h_eq] at h_cover_transfer
    exact h_cover_transfer
  have h2 : (C_Q.card : ENNReal) ≤ (affinePackingM : ENNReal) * ((2000 : ENNReal) * Nslope) := by
    calc (C_Q.card : ENNReal)
      ≤ (affinePackingM : ENNReal) * NCQ := h1
    _ ≤ (affinePackingM : ENNReal) * ((2000 : ENNReal) * Nslope) := by
      exact mul_le_mul_left' h_transfer' _
  let K : ENNReal := (affinePackingM : ENNReal) * (2000 : ENNReal)
  have hK_eq : (affinePackingM : ENNReal) * ((2000 : ENNReal) * Nslope) = K * Nslope := by
    rw [mul_assoc]
  have h3 : (C_Q.card : ENNReal) ≤ K * Nslope := by
    rw [hK_eq] at h2; exact h2
  have h_card_lower' : ENNReal.ofReal (Real.rpow Δ (-s + 11 * ε)) ≤ (C_Q.card : ENNReal) := by
    exact_mod_cast hC_card_lower
  have h4 : ENNReal.ofReal (Real.rpow Δ (-s + 11 * ε)) ≤ K * Nslope :=
    le_trans h_card_lower' h3
  have hK_comm : K = (2000 : ENNReal) * (affinePackingM : ENNReal) := by
    simp [K, mul_comm] <;> ring
  have h5 : K ≤ ENNReal.ofReal (Real.rpow Δ (-14 * ε)) := by
    rw [hK_comm]; exact h_small_pack
  have h6 : ENNReal.ofReal (Real.rpow Δ (-s + 11 * ε)) ≤
      ENNReal.ofReal (Real.rpow Δ (-14 * ε)) * Nslope := by
    calc ENNReal.ofReal (Real.rpow Δ (-s + 11 * ε))
      ≤ K * Nslope := h4
    _ ≤ ENNReal.ofReal (Real.rpow Δ (-14 * ε)) * Nslope := by gcongr
  have h7 : Real.rpow Δ (-14 * ε) * Real.rpow Δ (25 * ε - s) = Real.rpow Δ (-s + 11 * ε) := by
    have h_sum : (-14 * ε) + (25 * ε - s) = -s + 11 * ε := by ring
    have h_add : Real.rpow Δ ((-14 * ε) + (25 * ε - s)) =
        Real.rpow Δ (-14 * ε) * Real.rpow Δ (25 * ε - s) :=
      Real.rpow_add hΔ_pos (-14 * ε) (25 * ε - s)
    rw [h_sum] at h_add
    exact h_add.symm
  have h_nonneg1 : 0 ≤ Real.rpow Δ (-14 * ε) := Real.rpow_nonneg hΔ_pos.le _
  have h8 : ENNReal.ofReal (Real.rpow Δ (-s + 11 * ε)) =
      ENNReal.ofReal (Real.rpow Δ (-14 * ε)) * ENNReal.ofReal (Real.rpow Δ (25 * ε - s)) := by
    rw [← h7, ENNReal.ofReal_mul h_nonneg1] <;> rfl
  rw [h8] at h6
  have h_rpow_pos : 0 < Real.rpow Δ (-14 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  have h_ennreal_pos : 0 < ENNReal.ofReal (Real.rpow Δ (-14 * ε)) :=
    ENNReal.ofReal_pos.mpr h_rpow_pos
  have h_ne_zero : ENNReal.ofReal (Real.rpow Δ (-14 * ε)) ≠ 0 := h_ennreal_pos.ne'
  have h_ne_top : ENNReal.ofReal (Real.rpow Δ (-14 * ε)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_final : ENNReal.ofReal (Real.rpow Δ (25 * ε - s)) ≤ Nslope := by
    have h_cancel : ENNReal.ofReal (Real.rpow Δ (-14 * ε)) * ENNReal.ofReal (Real.rpow Δ (25 * ε - s)) ≤
        ENNReal.ofReal (Real.rpow Δ (-14 * ε)) * Nslope := h6
    have h_comm1 : ENNReal.ofReal (Real.rpow Δ (-14 * ε)) * ENNReal.ofReal (Real.rpow Δ (25 * ε - s)) =
        ENNReal.ofReal (Real.rpow Δ (25 * ε - s)) * ENNReal.ofReal (Real.rpow Δ (-14 * ε)) := by
      rw [mul_comm]
    have h_comm2 : ENNReal.ofReal (Real.rpow Δ (-14 * ε)) * Nslope =
        Nslope * ENNReal.ofReal (Real.rpow Δ (-14 * ε)) := by rw [mul_comm]
    rw [h_comm1, h_comm2] at h_cancel
    have h_iff : ENNReal.ofReal (Real.rpow Δ (25 * ε - s)) * ENNReal.ofReal (Real.rpow Δ (-14 * ε)) ≤
        Nslope * ENNReal.ofReal (Real.rpow Δ (-14 * ε)) ↔
        ENNReal.ofReal (Real.rpow Δ (25 * ε - s)) ≤ Nslope :=
      ENNReal.mul_le_mul_iff_left h_ne_zero h_ne_top
    exact h_iff.mp h_cancel
  exact h_final

/-! ### GAP 4 (TEMPORARY): hC_Q_slope_cover_upper (weak bound)

  Ncover(slope image) ≤ Δ^{-1-25ε}.

  Uses strip packing: |C_Q| ≤ Δ^{-1-5ε}, and Ncover(slope) ≤ |C_Q|.
-/

lemma hC_Q_slope_cover_upper_weak
    {Δ s ε : ℝ} {C_Q : Finset CoarseTube}
    (hΔ_pos : 0 < Δ) (hε_pos : 0 < ε) (hΔ_lt_one : Δ < 1)
    (hs : 0 < s)
    (hC_card_upper : (C_Q.card : ℝ) ≤ Real.rpow Δ (-1 - 5 * ε)) :
    (Metric.externalCoveringNumber Δ.toNNReal (tubeSlope '' (C_Q : Set CoarseTube)) : ENNReal) ≤
      ENNReal.ofReal (Real.rpow Δ (-1 - 25 * ε)) := by
  let S := tubeSlope '' (C_Q : Set CoarseTube)
  have h1 : (Metric.externalCoveringNumber Δ.toNNReal S : ENNReal) ≤ S.encard := by
    exact_mod_cast Metric.externalCoveringNumber_le_encard_self (A := S)
  have h2 : S.encard ≤ (C_Q.card : ENNReal) := by
    have h21 : S.encard ≤ (C_Q : Set CoarseTube).encard := Set.encard_image_le _ _
    have h22 : (C_Q : Set CoarseTube).encard = ↑C_Q.card := by simp
    rw [h22] at h21
    exact_mod_cast h21
  have h3 : (C_Q.card : ENNReal) ≤ ENNReal.ofReal (Real.rpow Δ (-1 - 5 * ε)) := by
    have h31 : (C_Q.card : ℝ) ≤ Real.rpow Δ (-1 - 5 * ε) := hC_card_upper
    have h32 : (C_Q.card : ENNReal) = ENNReal.ofReal (C_Q.card : ℝ) := by
      simp
    rw [h32]
    exact ENNReal.ofReal_le_ofReal h31
  have h4 : Real.rpow Δ (-1 - 5 * ε) ≤ Real.rpow Δ (-1 - 25 * ε) := by
    have h_exp : -1 - 5 * ε ≥ -1 - 25 * ε := by linarith
    have hΔ_le_one : Δ ≤ 1 := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_le_one h_exp
  calc (Metric.externalCoveringNumber Δ.toNNReal S : ENNReal)
    ≤ S.encard := h1
  _ ≤ (C_Q.card : ENNReal) := h2
  _ ≤ ENNReal.ofReal (Real.rpow Δ (-1 - 5 * ε)) := h3
  _ ≤ ENNReal.ofReal (Real.rpow Δ (-1 - 25 * ε)) := by gcongr

/-! ### GAP 1: hC_Q_cover_transfer

  Ncover(C_Q) ≤ 2000 * Ncover(slope image).

  Uses strip_covering_Q: each slope strip of width 2Δ through Q is covered
  by ≤600 Δ-balls in AffineLine space.
-/

/-- If p1, p2 ∈ squareSet Δ Q, then |p1 0 - p2 0| ≤ Δ. -/
lemma square_x_diff_le {Δ : ℝ} {Q : CoarseSquare Δ} {p1 p2 : Plane}
    (hp1 : p1 ∈ squareSet Δ Q) (hp2 : p2 ∈ squareSet Δ Q) (hΔ_pos : 0 < Δ) :
    |p1 0 - p2 0| ≤ Δ := by
  have h1 : p1 0 ∈ Set.Ico (Δ * (Q.1 : ℝ)) (Δ * ((Q.1 : ℝ) + 1)) := hp1.1
  have h2 : p2 0 ∈ Set.Ico (Δ * (Q.1 : ℝ)) (Δ * ((Q.1 : ℝ) + 1)) := hp2.1
  have h3 : Δ * (Q.1 : ℝ) ≤ p1 0 := h1.1
  have h4 : p1 0 < Δ * ((Q.1 : ℝ) + 1) := h1.2
  have h5 : Δ * (Q.1 : ℝ) ≤ p2 0 := h2.1
  have h6 : p2 0 < Δ * ((Q.1 : ℝ) + 1) := h2.2
  rw [abs_le] <;> constructor <;> linarith

/-- If p1, p2 ∈ squareSet Δ Q, then |p1 1 - p2 1| ≤ Δ. -/
lemma square_y_diff_le {Δ : ℝ} {Q : CoarseSquare Δ} {p1 p2 : Plane}
    (hp1 : p1 ∈ squareSet Δ Q) (hp2 : p2 ∈ squareSet Δ Q) (hΔ_pos : 0 < Δ) :
    |p1 1 - p2 1| ≤ Δ := by
  have h1 : p1 1 ∈ Set.Ico (Δ * (Q.2 : ℝ)) (Δ * ((Q.2 : ℝ) + 1)) := hp1.2
  have h2 : p2 1 ∈ Set.Ico (Δ * (Q.2 : ℝ)) (Δ * ((Q.2 : ℝ) + 1)) := hp2.2
  have h3 : Δ * (Q.2 : ℝ) ≤ p1 1 := h1.1
  have h4 : p1 1 < Δ * ((Q.2 : ℝ) + 1) := h1.2
  have h5 : Δ * (Q.2 : ℝ) ≤ p2 1 := h2.1
  have h6 : p2 1 < Δ * ((Q.2 : ℝ) + 1) := h2.2
  rw [abs_le] <;> constructor <;> linarith

/-- Cover a slope strip of width 2Δ through Q by ≤600 Δ-balls in AffineLine space. -/
lemma strip_covering_Q
    {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ ≤ 1 / 2)
    {C_Q : Finset CoarseTube} {Q : CoarseSquare Δ}
    (hC_Q_v : ∀ ℓ ∈ C_Q, (LemmaE.getDirV ℓ) 1 ≠ 0)
    (hC_Q_a : ∀ ℓ ∈ C_Q, |tubeSlope ℓ| ≤ 1)
    (hC_Q_b : ∀ ℓ ∈ C_Q, |tubeIntercept ℓ| ≤ 3)
    (h_strip : ∀ ℓ ∈ C_Q, ∃ (p : Plane), p ∈ squareSet Δ Q ∧ |p 1| ≤ Real.sqrt 2 ∧
        |tubeIntercept ℓ - (p 0 - tubeSlope ℓ * p 1)| ≤ 4 * Δ)
    (a_center : ℝ) :
    ∃ (C : Finset AffineLine),
      Metric.IsCover Δ.toNNReal
        ((C_Q : Set AffineLine) ∩ {ℓ | |tubeSlope ℓ - a_center| ≤ Δ}) C ∧
      C.card ≤ 1000 := by
  let S : Set AffineLine := (C_Q : Set AffineLine) ∩ {ℓ | |tubeSlope ℓ - a_center| ≤ Δ}
  by_cases hS : S.Nonempty
  · rcases hS with ⟨ℓ0, hℓ0⟩
    have hℓ0_in_CQ : ℓ0 ∈ C_Q := hℓ0.1
    have hℓ0_strip : |tubeSlope ℓ0 - a_center| ≤ Δ := hℓ0.2
    let b_center : ℝ := tubeIntercept ℓ0
    have hb_center_bound : |b_center| ≤ 3 := hC_Q_b ℓ0 hℓ0_in_CQ
    have h_b_bound : ∀ ℓ ∈ S, |tubeIntercept ℓ - b_center| ≤ (10 + 2 * Real.sqrt 2) * Δ := by
      intro ℓ hℓ
      have hℓ_in_CQ : ℓ ∈ C_Q := hℓ.1
      have hℓ_strip : |tubeSlope ℓ - a_center| ≤ Δ := hℓ.2
      have h_a_diff : |tubeSlope ℓ - tubeSlope ℓ0| ≤ 2 * Δ := by
        have h_tri : |tubeSlope ℓ - tubeSlope ℓ0| ≤ |tubeSlope ℓ - a_center| + |tubeSlope ℓ0 - a_center| := by
          calc |tubeSlope ℓ - tubeSlope ℓ0|
            = |(tubeSlope ℓ - a_center) - (tubeSlope ℓ0 - a_center)| := by ring_nf
          _ ≤ |tubeSlope ℓ - a_center| + |tubeSlope ℓ0 - a_center| := by exact abs_sub _ _
        linarith [hℓ_strip, hℓ0_strip]
      rcases h_strip ℓ hℓ_in_CQ with ⟨pℓ, hpℓ_in_Q, hpℓ_y, h_closeℓ⟩
      rcases h_strip ℓ0 hℓ0_in_CQ with ⟨p0, hp0_in_Q, hp0_y, h_close0⟩
      have h_x_diff : |pℓ 0 - p0 0| ≤ Δ := square_x_diff_le hpℓ_in_Q hp0_in_Q hΔ_pos
      have h_y_diff : |pℓ 1 - p0 1| ≤ Δ := square_y_diff_le hpℓ_in_Q hp0_in_Q hΔ_pos
      have h_middle : |(pℓ 0 - tubeSlope ℓ * pℓ 1) - (p0 0 - tubeSlope ℓ0 * p0 1)| ≤ (2 + 2 * Real.sqrt 2) * Δ := by
        have h_alg : (pℓ 0 - tubeSlope ℓ * pℓ 1) - (p0 0 - tubeSlope ℓ0 * p0 1) =
            (pℓ 0 - p0 0) - tubeSlope ℓ * (pℓ 1 - p0 1) -
            (tubeSlope ℓ - tubeSlope ℓ0) * p0 1 := by ring
        rw [h_alg]
        have h_tri : |(pℓ 0 - p0 0) - tubeSlope ℓ * (pℓ 1 - p0 1) - (tubeSlope ℓ - tubeSlope ℓ0) * p0 1| ≤
            |pℓ 0 - p0 0| + |tubeSlope ℓ * (pℓ 1 - p0 1)| + |(tubeSlope ℓ - tubeSlope ℓ0) * p0 1| := by
          have h1 : |(pℓ 0 - p0 0) - tubeSlope ℓ * (pℓ 1 - p0 1) - (tubeSlope ℓ - tubeSlope ℓ0) * p0 1| ≤
              |(pℓ 0 - p0 0) - tubeSlope ℓ * (pℓ 1 - p0 1)| + |(tubeSlope ℓ - tubeSlope ℓ0) * p0 1| := by
            exact DiscretisedFurstenbergEstimate.real_abs_sub
              (pℓ.ofLp 0 - p0.ofLp 0 - tubeSlope ℓ * (pℓ.ofLp 1 - p0.ofLp 1)) ((tubeSlope ℓ - tubeSlope ℓ0) * p0.ofLp 1)
          have h2 : |(pℓ 0 - p0 0) - tubeSlope ℓ * (pℓ 1 - p0 1)| ≤
              |pℓ 0 - p0 0| + |tubeSlope ℓ * (pℓ 1 - p0 1)| := by
            exact DiscretisedFurstenbergEstimate.real_abs_sub (pℓ.ofLp 0 - p0.ofLp 0)
              (tubeSlope ℓ * (pℓ.ofLp 1 - p0.ofLp 1))
          linarith
        rw [abs_mul, abs_mul] at h_tri
        have h_goal : |pℓ 0 - p0 0| + |tubeSlope ℓ| * |pℓ 1 - p0 1| + |tubeSlope ℓ - tubeSlope ℓ0| * |p0 1| ≤ (2 + 2 * Real.sqrt 2) * Δ := by
          have ha : |tubeSlope ℓ| ≤ 1 := hC_Q_a ℓ hℓ_in_CQ
          have hpy : |p0 1| ≤ Real.sqrt 2 := hp0_y
          calc |pℓ 0 - p0 0| + |tubeSlope ℓ| * |pℓ 1 - p0 1| + |tubeSlope ℓ - tubeSlope ℓ0| * |p0 1|
            ≤ Δ + 1 * Δ + (2 * Δ) * Real.sqrt 2 := by gcongr
          _ = (2 + 2 * Real.sqrt 2) * Δ := by ring
        exact h_tri.trans h_goal
      have h_triangle : |tubeIntercept ℓ - b_center| ≤
          |tubeIntercept ℓ - (pℓ 0 - tubeSlope ℓ * pℓ 1)| +
          |(pℓ 0 - tubeSlope ℓ * pℓ 1) - (p0 0 - tubeSlope ℓ0 * p0 1)| +
          |(p0 0 - tubeSlope ℓ0 * p0 1) - tubeIntercept ℓ0| := by
        set x := tubeIntercept ℓ
        set y := pℓ 0 - tubeSlope ℓ * pℓ 1
        set z := p0 0 - tubeSlope ℓ0 * p0 1
        set w := b_center
        have h1 : |x - w| ≤ |x - y| + |y - w| := by
          have h : x - w = (x - y) + (y - w) := by ring
          rw [h]
          have h_abs : |(x - y) + (y - w)| ≤ |x - y| + |y - w| := by exact DiscretisedFurstenbergEstimate.real_abs_add (x - y) (y - w)
          exact h_abs
        have h2 : |y - w| ≤ |y - z| + |z - w| := by
          have h : y - w = (y - z) + (z - w) := by ring
          rw [h]
          have h_abs : |(y - z) + (z - w)| ≤ |y - z| + |z - w| := by exact DiscretisedFurstenbergEstimate.real_abs_add (y - z) (z - w)
          exact h_abs
        linarith
      have h_sum : |tubeIntercept ℓ - (pℓ 0 - tubeSlope ℓ * pℓ 1)| +
          |(pℓ 0 - tubeSlope ℓ * pℓ 1) - (p0 0 - tubeSlope ℓ0 * p0 1)| +
          |(p0 0 - tubeSlope ℓ0 * p0 1) - tubeIntercept ℓ0| ≤
          4 * Δ + (2 + 2 * Real.sqrt 2) * Δ + 4 * Δ := by
        have h1 : |tubeIntercept ℓ - (pℓ 0 - tubeSlope ℓ * pℓ 1)| ≤ 4 * Δ := h_closeℓ
        have h2 : |(pℓ 0 - tubeSlope ℓ * pℓ 1) - (p0 0 - tubeSlope ℓ0 * p0 1)| ≤ (2 + 2 * Real.sqrt 2) * Δ := h_middle
        have h3 : |(p0 0 - tubeSlope ℓ0 * p0 1) - tubeIntercept ℓ0| ≤ 4 * Δ := by
          have h31 : |tubeIntercept ℓ0 - (p0 0 - tubeSlope ℓ0 * p0 1)| ≤ 4 * Δ := h_close0
          have h32 : |(p0 0 - tubeSlope ℓ0 * p0 1) - tubeIntercept ℓ0| = |tubeIntercept ℓ0 - (p0 0 - tubeSlope ℓ0 * p0 1)| := by
            rw [show (p0 0 - tubeSlope ℓ0 * p0 1) - tubeIntercept ℓ0 = -(tubeIntercept ℓ0 - (p0 0 - tubeSlope ℓ0 * p0 1)) by ring]
            rw [abs_neg]
          rw [h32]
          exact h31
        linarith
      calc |tubeIntercept ℓ - b_center|
        ≤ |tubeIntercept ℓ - (pℓ 0 - tubeSlope ℓ * pℓ 1)| +
          |(pℓ 0 - tubeSlope ℓ * pℓ 1) - (p0 0 - tubeSlope ℓ0 * p0 1)| +
          |(p0 0 - tubeSlope ℓ0 * p0 1) - tubeIntercept ℓ0| := h_triangle
      _ ≤ 4 * Δ + (2 + 2 * Real.sqrt 2) * Δ + 4 * Δ := h_sum
      _ = (10 + 2 * Real.sqrt 2) * Δ := by ring
    let step_a : ℝ := Δ / 8
    let step_b : ℝ := Δ / 2
    let I_a : Finset ℕ := Finset.range 17
    let I_b : Finset ℕ := Finset.range 53
    let a_grid (k : ℕ) : ℝ := a_center - Δ + (k : ℝ) * step_a
    let b_grid (j : ℕ) : ℝ := b_center - 13 * Δ + (j : ℝ) * step_b
    classical
    let C : Finset AffineLine :=
      (I_a ×ˢ I_b).image (fun p : ℕ × ℕ =>
        TubesAndSlopes.makeAffineLine (a_grid p.1) (b_grid p.2))
    have hC_card : C.card ≤ 1000 := by
      have h1 : C.card ≤ (I_a ×ˢ I_b).card := by exact Finset.card_image_le
      have h2 : (I_a ×ˢ I_b).card = 17 * 53 := by
        simp [I_a, I_b, Finset.card_product] <;> norm_num
      rw [h2] at h1
      have h3 : C.card ≤ 901 := h1
      linarith
    have h_cover : Metric.IsCover Δ.toNNReal S C := by
      intro ℓ hℓ
      have hℓ_in_CQ : ℓ ∈ C_Q := hℓ.1
      have hℓ_strip : |tubeSlope ℓ - a_center| ≤ Δ := hℓ.2
      set a : ℝ := tubeSlope ℓ with ha_def
      set b : ℝ := tubeIntercept ℓ with hb_def
      have ha_lo : a_center - Δ ≤ a := by linarith [abs_le.mp hℓ_strip]
      have ha_hi : a ≤ a_center + Δ := by linarith [abs_le.mp hℓ_strip]
      have h13 : (10 + 2 * Real.sqrt 2) * Δ ≤ 13 * Δ := by
        have h : 10 + 2 * Real.sqrt 2 ≤ 13 := by
          have h2 : Real.sqrt 2 ≤ 3 / 2 := by
            have h3 : Real.sqrt 2 ≤ Real.sqrt (9 / 4) := Real.sqrt_le_sqrt (by norm_num)
            have h4 : Real.sqrt (9 / 4) = 3 / 2 := by
              rw [Real.sqrt_eq_cases] <;> norm_num
            linarith
          linarith
        exact mul_le_mul_of_nonneg_right h hΔ_pos.le
      have hb_lo : b_center - 13 * Δ ≤ b := by
        have h : |b - b_center| ≤ (10 + 2 * Real.sqrt 2) * Δ := h_b_bound ℓ hℓ
        have h' : |b - b_center| ≤ 13 * Δ := le_trans h h13
        linarith [abs_le.mp h']
      have hb_hi : b ≤ b_center + 13 * Δ := by
        have h : |b - b_center| ≤ (10 + 2 * Real.sqrt 2) * Δ := h_b_bound ℓ hℓ
        have h' : |b - b_center| ≤ 13 * Δ := le_trans h h13
        linarith [abs_le.mp h']
      rcases TubesAndSlopes.real_grid_cover a (a_center - Δ) (a_center + Δ) 16
          (by norm_num) ha_lo ha_hi with ⟨k, hk_le, hk_cover⟩
      rcases TubesAndSlopes.real_grid_cover b (b_center - 13 * Δ) (b_center + 13 * Δ) 52
          (by norm_num) hb_lo hb_hi with ⟨j, hj_le, hj_cover⟩
      have hk_in : k ∈ I_a := by simp [I_a, hk_le] <;> omega
      have hj_in : j ∈ I_b := by simp [I_b, hj_le] <;> omega
      have hk_cover' : |a - a_grid k| ≤ step_a / 2 := by
        convert hk_cover using 1
        · simp [a_grid, step_a] <;> ring_nf
        · simp [step_a] <;> ring
      have hj_cover' : |b - b_grid j| ≤ step_b / 2 := by
        convert hj_cover using 1
        · simp [b_grid, step_b] <;> ring_nf
        · simp [step_b] <;> ring
      let ℓ_g := TubesAndSlopes.makeAffineLine (a_grid k) (b_grid j)
      have hℓg_in_C : ℓ_g ∈ C := by
        apply Finset.mem_image.mpr
        refine ⟨(k, j), ?_, rfl⟩
        exact Finset.mem_product.mpr ⟨hk_in, hj_in⟩
      have hℓg_v1 : (LemmaE.getDirV ℓ_g) 1 ≠ 0 :=
        TubesAndSlopes.makeAffineLine_v1 (a_grid k) (b_grid j)
      have hℓg_params : LemmaE.affineLineParams ℓ_g = (a_grid k, b_grid j) :=
        TubesAndSlopes.makeAffineLine_params (a_grid k) (b_grid j)
      have hbg_bound : |b_grid j| ≤ 10 := by
        have h_j_le : (j : ℝ) ≤ 52 := by exact_mod_cast hj_le
        have h_j_nonneg : 0 ≤ (j : ℝ) := by positivity
        have h1 : |b_grid j - b_center| ≤ 13 * Δ := by
          have h2 : b_grid j - b_center = (j : ℝ) * step_b - 13 * Δ := by
            simp [b_grid] <;> ring
          rw [h2]
          have h3 : (j : ℝ) * step_b - 13 * Δ = Δ * ((j : ℝ) / 2 - 13) := by
            simp [step_b] <;> ring
          rw [h3]
          have h4 : |(j : ℝ) / 2 - 13| ≤ 13 := by
            have h5 : -13 ≤ (j : ℝ) / 2 - 13 := by linarith
            have h6 : (j : ℝ) / 2 - 13 ≤ 13 := by linarith
            exact abs_le.mpr ⟨h5, h6⟩
          calc |Δ * ((j : ℝ) / 2 - 13)|
            = Δ * |(j : ℝ) / 2 - 13| := by rw [abs_mul, abs_of_pos hΔ_pos]
          _ ≤ Δ * 13 := by gcongr
          _ = 13 * Δ := by ring
        have h4 : |b_grid j| ≤ |b_center| + |b_grid j - b_center| := by
          simpa [Real.norm_eq_abs] using norm_add_le b_center (b_grid j - b_center)
        have h5 : |b_center| + |b_grid j - b_center| ≤ 3 + 13 * Δ := by
          linarith [hb_center_bound, h1]
        have h6 : 3 + 13 * Δ ≤ 10 := by linarith [hΔ_lt_half]
        linarith
      have hbg_bound' : |(LemmaE.affineLineParams ℓ_g).2| ≤ 10 := by
        rw [hℓg_params] <;> simpa using hbg_bound
      have h_dist : AffineLine.dist ℓ ℓ_g ≤ Δ := by
        have h_bound := TubesAndSlopes.dist_bound_general ℓ ℓ_g
          (hC_Q_v ℓ hℓ_in_CQ) hℓg_v1 (B := 10) (by norm_num) hbg_bound'
        have h_bound2 := h_bound
        rw [hℓg_params] at h_bound2
        have h1 : |a - a_grid k| ≤ Δ / 16 := by
          have h2 : step_a / 2 = Δ / 16 := by simp [step_a] <;> ring
          rw [h2] at hk_cover'
          exact hk_cover'
        have h3 : |b - b_grid j| ≤ Δ / 4 := by
          have h4 : step_b / 2 = Δ / 4 := by simp [step_b] <;> ring
          rw [h4] at hj_cover'
          exact hj_cover'
        have h4 : AffineLine.dist ℓ ℓ_g ≤ (2 + (10 : ℝ)) * |a - a_grid k| + |b - b_grid j| := h_bound2
        linarith
      have h_edist : edist ℓ ℓ_g ≤ ↑(Δ.toNNReal) := by
        have h5 : edist ℓ ℓ_g = ENNReal.ofReal (dist ℓ ℓ_g) := edist_dist ℓ ℓ_g
        rw [h5]
        have h6 : (↑(Δ.toNNReal) : ENNReal) = ENNReal.ofReal Δ := by
          have h7 : 0 ≤ Δ := by linarith
          have h8 : (Δ.toNNReal : ℝ) = Δ := by exact Real.coe_toNNReal Δ h7
          have h9 : (↑(Δ.toNNReal) : ENNReal) = ENNReal.ofReal (Δ.toNNReal : ℝ) := by exact Eq.symm ENNReal.ofReal_coe_nnreal
          rw [h9, h8]
        rw [h6]
        exact ENNReal.ofReal_le_ofReal h_dist
      exact ⟨ℓ_g, hℓg_in_C, h_edist⟩
    exact ⟨C, h_cover, hC_card⟩
  · have hS_empty : S = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using hS
    have h_cover : Metric.IsCover Δ.toNNReal S (∅ : Finset AffineLine) := by
      rw [hS_empty] <;> intro x hx; simpa using hx
    exact ⟨(∅ : Finset AffineLine), h_cover, by simp⟩

lemma hC_Q_cover_transfer_main
    {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ ≤ 1 / 2)
    {C_Q : Finset CoarseTube} {Q : CoarseSquare Δ}
    (hC_Q_sep : SeparatedAt Δ (C_Q : Set CoarseTube))
    (hC_Q_v : ∀ ℓ ∈ C_Q, (LemmaE.getDirV ℓ) 1 ≠ 0)
    (hC_Q_a : ∀ ℓ ∈ C_Q, |tubeSlope ℓ| ≤ 1)
    (hC_Q_b : ∀ ℓ ∈ C_Q, |tubeIntercept ℓ| ≤ 3)
    (h_strip : ∀ ℓ ∈ C_Q, ∃ (p : Plane), p ∈ squareSet Δ Q ∧ |p 1| ≤ Real.sqrt 2 ∧
        |tubeIntercept ℓ - (p 0 - tubeSlope ℓ * p 1)| ≤ 4 * Δ) :
    (Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set CoarseTube) : ENNReal) ≤
      ENNReal.ofReal (2000 : ℝ) *
        Metric.externalCoveringNumber Δ.toNNReal (tubeSlope '' (C_Q : Set CoarseTube)) := by
  let f : AffineLine → ℝ := tubeSlope
  let A : Set ℝ := f '' (C_Q : Set AffineLine)
  have hΔ_lt_one : Δ < 1 := by linarith
  by_cases h_top : Metric.externalCoveringNumber Δ.toNNReal A = ⊤
  · rw [h_top] <;> simp
  · have hfin : Metric.externalCoveringNumber Δ.toNNReal A < ⊤ :=
      lt_top_iff_ne_top.mpr h_top
    rcases exists_external_cover_eq hfin with ⟨C_set, hC_cover, hC_eq⟩
    have hC_finite : C_set.Finite := by
      have h : C_set.encard < ⊤ := by rw [hC_eq] <;> exact hfin
      have h_ne : C_set.encard ≠ ⊤ := h.ne
      have h_exists : ∃ (k : ℕ), (↑k : ENat) = C_set.encard := ENat.ne_top_iff_exists.mp h_ne
      rcases h_exists with ⟨k, hk⟩
      have h_le : C_set.encard ≤ ↑k := by
        rw [← hk]
      exact Set.finite_of_encard_le_coe h_le
    classical
    let C_fin : Finset ℝ := hC_finite.toFinset
    have hC_fin_eq : (C_fin : Set ℝ) = C_set := hC_finite.coe_toFinset
    let D : Finset AffineLine := C_fin.biUnion fun a_center =>
      Classical.choose (strip_covering_Q hΔ_pos hΔ_lt_half hC_Q_v hC_Q_a hC_Q_b h_strip a_center)
    have hD_cover : Metric.IsCover Δ.toNNReal (C_Q : Set AffineLine) D := by
      intro ℓ hℓ
      have h_a_in_A : f ℓ ∈ A := ⟨ℓ, hℓ, rfl⟩
      rcases hC_cover h_a_in_A with ⟨c, hc, hedistance⟩
      have hdist : dist (f ℓ) c ≤ (Δ.toNNReal : ℝ) := by
        have h_ed : edist (f ℓ) c ≤ ↑(Δ.toNNReal) := hedistance
        have h_eq2 : edist (f ℓ) c = ENNReal.ofReal (dist (f ℓ) c) := edist_dist (f ℓ) c
        rw [h_eq2] at h_ed
        have h_coe : (↑(Δ.toNNReal) : ENNReal) = ENNReal.ofReal (Δ.toNNReal : ℝ) := by
          exact Eq.symm ENNReal.ofReal_coe_nnreal
        rw [h_coe] at h_ed
        have h_nonneg : 0 ≤ (Δ.toNNReal : ℝ) := NNReal.coe_nonneg _
        exact (ENNReal.ofReal_le_ofReal_iff h_nonneg).mp h_ed
      have h_strip2 : |f ℓ - c| ≤ Δ := by
        have h_eq : dist (f ℓ) c = |f ℓ - c| := by
          simp [dist_eq_norm, Real.norm_eq_abs] <;> rfl
        rw [h_eq] at hdist
        have h_coe : (Δ.toNNReal : ℝ) = Δ := by
          have h_nonneg : 0 ≤ Δ := by linarith
          have h : (Δ.toNNReal : ℝ) = max Δ 0 := by exact Real.coe_toNNReal' Δ
          rw [h, max_eq_left h_nonneg]
        rw [h_coe] at hdist
        exact hdist
      let D_c := Classical.choose (strip_covering_Q hΔ_pos hΔ_lt_half hC_Q_v hC_Q_a hC_Q_b h_strip c)
      have hD_c_cover : Metric.IsCover Δ.toNNReal
          ((C_Q : Set AffineLine) ∩ {ℓ | |f ℓ - c| ≤ Δ}) D_c :=
        (Classical.choose_spec (strip_covering_Q hΔ_pos hΔ_lt_half hC_Q_v hC_Q_a hC_Q_b h_strip c)).1
      have hℓ_in_strip : ℓ ∈ (C_Q : Set AffineLine) ∩ {ℓ | |f ℓ - c| ≤ Δ} :=
        ⟨hℓ, h_strip2⟩
      rcases hD_c_cover hℓ_in_strip with ⟨ℓ_g, hℓg_in_Dc, hedist2⟩
      have hℓg_in_D : ℓ_g ∈ D := by
        apply Finset.mem_biUnion.mpr
        refine ⟨c, ?_, hℓg_in_Dc⟩
        have hc' : c ∈ (C_fin : Set ℝ) := by
          rw [hC_fin_eq] <;> exact hc
        exact_mod_cast hc'
      exact ⟨ℓ_g, hℓg_in_D, hedist2⟩
    have hD_card : D.card ≤ 1000 * C_fin.card := by
      calc D.card
        ≤ ∑ a ∈ C_fin, (Classical.choose (strip_covering_Q hΔ_pos hΔ_lt_half hC_Q_v hC_Q_a hC_Q_b h_strip a)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ C_fin, 1000 := by
          apply Finset.sum_le_sum
          intro a _
          exact (Classical.choose_spec (strip_covering_Q hΔ_pos hΔ_lt_half hC_Q_v hC_Q_a hC_Q_b h_strip a)).2
      _ = 1000 * C_fin.card := by simp [Finset.sum_const] <;> ring
    have h1 : (Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set AffineLine) : ENNReal) ≤ ((D : Set AffineLine).encard : ENNReal) := by
      exact_mod_cast hD_cover.externalCoveringNumber_le_encard
    have h2 : ((D : Set AffineLine).encard : ENNReal) ≤
        (1000 : ENNReal) * (Metric.externalCoveringNumber Δ.toNNReal A : ENNReal) := by
      have hA_eq : (Metric.externalCoveringNumber Δ.toNNReal A : ENNReal) = ↑C_fin.card := by
        have h5 : (C_set.encard : ENNReal) = (↑C_fin.card : ENNReal) := by
          rw [← hC_fin_eq] <;> simp
        have h61 : Metric.externalCoveringNumber Δ.toNNReal A = C_set.encard := hC_eq.symm
        have h62 : (Metric.externalCoveringNumber Δ.toNNReal A : ENNReal) = (C_set.encard : ENNReal) :=
          congr_arg (fun x : ENat => (x : ENNReal)) h61
        rw [h62, h5]
      calc ((D : Set AffineLine).encard : ENNReal)
        = ↑D.card := by simp
      _ ≤ ↑(1000 * C_fin.card) := by exact_mod_cast hD_card
      _ = (1000 : ENNReal) * (↑C_fin.card : ENNReal) := by
        simp [Nat.cast_mul] <;> ring
      _ = (1000 : ENNReal) * (Metric.externalCoveringNumber Δ.toNNReal A : ENNReal) := by
        rw [←hA_eq]
    have hA_def : A = tubeSlope '' (C_Q : Set CoarseTube) := by
      rfl
    have h3 : (1000 : ENNReal) * (Metric.externalCoveringNumber Δ.toNNReal A : ENNReal) ≤
        ENNReal.ofReal (2000 : ℝ) * (Metric.externalCoveringNumber Δ.toNNReal A : ENNReal) := by
      gcongr
      <;> norm_num
    rw [hA_def] at h3
    exact le_trans h1 (le_trans h2 h3)

/-! ### GAP 2: hC_Q_slope_sset (in progress)

  tubeSlope '' C_Q is a (Δ, s, Δ^{-25ε})-set.
-/

lemma hC_Q_slope_sset_main
    {Δ s ε C2_Q : ℝ} {C_Q : Finset CoarseTube} {Q : CoarseSquare Δ}
    (hΔ_pos : 0 < Δ) (hε_pos : 0 < ε) (hΔ_lt_one : Δ < 1)
    (hs : 0 < s) (hs1 : s < 1)
    (hC_Q_sset : IsDeltaSSet Δ s C2_Q (C_Q : Set CoarseTube))
    (hC_Q_sep : SeparatedAt Δ (C_Q : Set CoarseTube))
    (hC_Q_v : ∀ ℓ ∈ C_Q, (LemmaE.getDirV ℓ) 1 ≠ 0)
    (hC_Q_a : ∀ ℓ ∈ C_Q, |tubeSlope ℓ| ≤ 1)
    (hC_Q_b : ∀ ℓ ∈ C_Q, |tubeIntercept ℓ| ≤ 3)
    (hC2_Q_loss : C2_Q ≤ Real.rpow Δ (-10 * ε))
    (h_small_const : (1680000 : ℝ) ≤ Real.rpow Δ (-15 * ε))
    (h_cover_transfer : (Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set CoarseTube) : ENNReal) ≤
        ENNReal.ofReal (2000 : ℝ) * Metric.externalCoveringNumber Δ.toNNReal (tubeSlope '' (C_Q : Set CoarseTube)))
    (h_strip : ∀ ℓ ∈ C_Q, ∃ (p : Plane), p ∈ squareSet Δ Q ∧ |p 1| ≤ Real.sqrt 2 ∧
        |tubeIntercept ℓ - (p 0 - tubeSlope ℓ * p 1)| ≤ 4 * Δ) :
    IsDeltaSSet Δ s (Real.rpow Δ (-25 * ε)) (tubeSlope '' (C_Q : Set CoarseTube)) := by
  let f : AffineLine → ℝ := tubeSlope
  let A : Set ℝ := f '' (C_Q : Set AffineLine)
  have hT_nonempty : (C_Q : Set AffineLine).Nonempty := hC_Q_sset.1
  have hA_nonempty : A.Nonempty := hT_nonempty.image f
  -- Pick a reference point p_Q in Q with |p_Q 1| ≤ √2
  rcases hT_nonempty with ⟨ℓ₀, hℓ₀⟩
  rcases h_strip ℓ₀ hℓ₀ with ⟨p_Q, hp_Q_in_Q, hpQ_y, _⟩
  have h_pQ1 : |p_Q 1| ≤ 2 := by
    have h1 : |p_Q 1| ≤ Real.sqrt 2 := hpQ_y
    have h2 : Real.sqrt 2 ≤ 2 := by
      have h3 : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      have h4 : Real.sqrt 4 = 2 := by rw [Real.sqrt_eq_cases] <;> norm_num
      linarith
    linarith
  -- Square coordinate bound
  have h_square_x : ∀ (p : Plane), p ∈ squareSet Δ Q → |p 0 - p_Q 0| ≤ Δ := by
    intro p hp
    have h1 : Δ * (Q.1 : ℝ) ≤ p 0 ∧ p 0 < Δ * ((Q.1 : ℝ) + 1) := hp.1
    have h2 : Δ * (Q.1 : ℝ) ≤ p_Q 0 ∧ p_Q 0 < Δ * ((Q.1 : ℝ) + 1) := hp_Q_in_Q.1
    have h3 : p 0 - p_Q 0 < Δ := by linarith
    have h4 : -(Δ) < p 0 - p_Q 0 := by linarith
    have h5 : |p 0 - p_Q 0| ≤ Δ := by
      rw [abs_le] <;> constructor <;> linarith
    exact h5
  have h_square_y : ∀ (p : Plane), p ∈ squareSet Δ Q → |p 1 - p_Q 1| ≤ Δ := by
    intro p hp
    have h1 : Δ * (Q.2 : ℝ) ≤ p 1 ∧ p 1 < Δ * ((Q.2 : ℝ) + 1) := hp.2
    have h2 : Δ * (Q.2 : ℝ) ≤ p_Q 1 ∧ p_Q 1 < Δ * ((Q.2 : ℝ) + 1) := hp_Q_in_Q.2
    have h3 : p 1 - p_Q 1 < Δ := by linarith
    have h4 : -(Δ) < p 1 - p_Q 1 := by linarith
    have h5 : |p 1 - p_Q 1| ≤ Δ := by
      rw [abs_le] <;> constructor <;> linarith
    exact h5
  -- Key intercept bound relative to p_Q
  have h_intercept_pQ : ∀ ℓ ∈ C_Q, |tubeIntercept ℓ - (p_Q 0 - tubeSlope ℓ * p_Q 1)| ≤ 6 * Δ := by
    intro ℓ hℓ
    rcases h_strip ℓ hℓ with ⟨p, hp_in_Q, _, h_close⟩
    have h1 : |p 0 - p_Q 0| ≤ Δ := h_square_x p hp_in_Q
    have h2 : |p 1 - p_Q 1| ≤ Δ := h_square_y p hp_in_Q
    have h3 : |(p 0 - tubeSlope ℓ * p 1) - (p_Q 0 - tubeSlope ℓ * p_Q 1)| ≤ 2 * Δ := by
      have h4 : (p 0 - tubeSlope ℓ * p 1) - (p_Q 0 - tubeSlope ℓ * p_Q 1) =
          (p 0 - p_Q 0) - tubeSlope ℓ * (p 1 - p_Q 1) := by ring
      rw [h4]
      have h5 : |(p 0 - p_Q 0) - tubeSlope ℓ * (p 1 - p_Q 1)| ≤
          |p 0 - p_Q 0| + |tubeSlope ℓ * (p 1 - p_Q 1)| := by
        exact DiscretisedFurstenbergEstimate.real_abs_sub (p.ofLp 0 - p_Q.ofLp 0)
          (tubeSlope ℓ * (p.ofLp 1 - p_Q.ofLp 1))
      have h6 : |tubeSlope ℓ * (p 1 - p_Q 1)| = |tubeSlope ℓ| * |p 1 - p_Q 1| := by
        rw [abs_mul]
      have h5' : |(p 0 - p_Q 0) - tubeSlope ℓ * (p 1 - p_Q 1)| ≤
          |p 0 - p_Q 0| + |tubeSlope ℓ| * |p 1 - p_Q 1| := by
        calc _
          ≤ |p 0 - p_Q 0| + |tubeSlope ℓ * (p 1 - p_Q 1)| := h5
        _ = |p 0 - p_Q 0| + |tubeSlope ℓ| * |p 1 - p_Q 1| := by rw [h6]
      have h7 : |tubeSlope ℓ| ≤ 1 := hC_Q_a ℓ hℓ
      have h8 : |p 0 - p_Q 0| ≤ Δ := h_square_x p hp_in_Q
      have h9 : |p 1 - p_Q 1| ≤ Δ := h_square_y p hp_in_Q
      have h10 : |p 0 - p_Q 0| + |tubeSlope ℓ| * |p 1 - p_Q 1| ≤ 2 * Δ := by
        calc _
          ≤ Δ + 1 * Δ := by gcongr <;> linarith
        _ = 2 * Δ := by ring
      exact h5'.trans h10
    calc |tubeIntercept ℓ - (p_Q 0 - tubeSlope ℓ * p_Q 1)|
      ≤ |tubeIntercept ℓ - (p 0 - tubeSlope ℓ * p 1)| +
          |(p 0 - tubeSlope ℓ * p 1) - (p_Q 0 - tubeSlope ℓ * p_Q 1)| := by exact abs_sub_le (tubeIntercept ℓ) (p.ofLp 0 - tubeSlope ℓ * p.ofLp 1) (p_Q.ofLp 0 - tubeSlope ℓ * p_Q.ofLp 1)
    _ ≤ 4 * Δ + 2 * Δ := by gcongr
    _ = 6 * Δ := by ring
  -- Intercept difference bound
  have h_b_diff : ∀ (ℓ₁ ℓ₂ : AffineLine), ℓ₁ ∈ C_Q → ℓ₂ ∈ C_Q →
      |tubeIntercept ℓ₁ - tubeIntercept ℓ₂| ≤ 12 * Δ + 2 * |tubeSlope ℓ₁ - tubeSlope ℓ₂| := by
    intro ℓ₁ ℓ₂ h₁ h₂
    set a1 := tubeSlope ℓ₁ with ha1
    set a2 := tubeSlope ℓ₂ with ha2
    set b1 := tubeIntercept ℓ₁ with hb1
    set b2 := tubeIntercept ℓ₂ with hb2
    have h1' : |b1 - (p_Q 0 - a1 * p_Q 1)| ≤ 6 * Δ := h_intercept_pQ ℓ₁ h₁
    have h2' : |b2 - (p_Q 0 - a2 * p_Q 1)| ≤ 6 * Δ := h_intercept_pQ ℓ₂ h₂
    have h2'' : |(p_Q 0 - a2 * p_Q 1) - b2| ≤ 6 * Δ := by
      have h_comm : |(p_Q 0 - a2 * p_Q 1) - b2| = |b2 - (p_Q 0 - a2 * p_Q 1)| := by
        rw [show (p_Q 0 - a2 * p_Q 1) - b2 = -(b2 - (p_Q 0 - a2 * p_Q 1)) by ring, abs_neg]
      rw [h_comm]
      exact h2'
    have h3 : |(p_Q 0 - a1 * p_Q 1) - (p_Q 0 - a2 * p_Q 1)| = |a1 - a2| * |p_Q 1| := by
      have h4 : (p_Q 0 - a1 * p_Q 1) - (p_Q 0 - a2 * p_Q 1) = (a2 - a1) * p_Q 1 := by ring
      rw [h4, abs_mul]
      have h5 : |a2 - a1| = |a1 - a2| := by rw [show a2 - a1 = -(a1 - a2) by ring, abs_neg]
      rw [h5] <;> ring
    have h6 : |a1 - a2| * |p_Q 1| ≤ 2 * |a1 - a2| := by
      have h7 : 0 ≤ |a1 - a2| := by positivity
      have h8 : |a1 - a2| * |p_Q 1| ≤ |a1 - a2| * 2 := by
        gcongr
        <;> linarith
      have h9 : |a1 - a2| * 2 = 2 * |a1 - a2| := by ring
      linarith
    have h_tri : |b1 - b2| ≤
        |b1 - (p_Q 0 - a1 * p_Q 1)| +
        |(p_Q 0 - a1 * p_Q 1) - (p_Q 0 - a2 * p_Q 1)| +
        |(p_Q 0 - a2 * p_Q 1) - b2| := by
      have h10 : b1 - b2 = (b1 - (p_Q 0 - a1 * p_Q 1)) +
          ((p_Q 0 - a1 * p_Q 1) - (p_Q 0 - a2 * p_Q 1)) +
          ((p_Q 0 - a2 * p_Q 1) - b2) := by ring
      rw [h10]
      have h11 : |(b1 - (p_Q 0 - a1 * p_Q 1)) +
          ((p_Q 0 - a1 * p_Q 1) - (p_Q 0 - a2 * p_Q 1)) +
          ((p_Q 0 - a2 * p_Q 1) - b2)| ≤
          |b1 - (p_Q 0 - a1 * p_Q 1)| +
          |(p_Q 0 - a1 * p_Q 1) - (p_Q 0 - a2 * p_Q 1)| +
          |(p_Q 0 - a2 * p_Q 1) - b2| := by
        calc _
          ≤ |(b1 - (p_Q 0 - a1 * p_Q 1)) + ((p_Q 0 - a1 * p_Q 1) - (p_Q 0 - a2 * p_Q 1))| +
              |(p_Q 0 - a2 * p_Q 1) - b2| := by exact abs_add_le _ _
        _ ≤ |b1 - (p_Q 0 - a1 * p_Q 1)| +
              |(p_Q 0 - a1 * p_Q 1) - (p_Q 0 - a2 * p_Q 1)| +
              |(p_Q 0 - a2 * p_Q 1) - b2| := by
          have h12 : |(b1 - (p_Q 0 - a1 * p_Q 1)) + ((p_Q 0 - a1 * p_Q 1) - (p_Q 0 - a2 * p_Q 1))| ≤
              |b1 - (p_Q 0 - a1 * p_Q 1)| + |(p_Q 0 - a1 * p_Q 1) - (p_Q 0 - a2 * p_Q 1)| :=
            abs_add_le _ _
          linarith
      exact h11
    calc |b1 - b2|
      ≤ |b1 - (p_Q 0 - a1 * p_Q 1)| +
          |(p_Q 0 - a1 * p_Q 1) - (p_Q 0 - a2 * p_Q 1)| +
          |(p_Q 0 - a2 * p_Q 1) - b2| := h_tri
    _ ≤ 6 * Δ + |a1 - a2| * |p_Q 1| + 6 * Δ := by
      rw [h3]
      linarith [h1', h2'']
    _ ≤ 6 * Δ + 2 * |a1 - a2| + 6 * Δ := by gcongr
    _ = 12 * Δ + 2 * |a1 - a2| := by ring
  -- Distance bound
  have h_dist_bound : ∀ (ℓ₁ ℓ₂ : AffineLine), ℓ₁ ∈ C_Q → ℓ₂ ∈ C_Q →
      AffineLine.dist ℓ₁ ℓ₂ ≤ 7 * |tubeSlope ℓ₁ - tubeSlope ℓ₂| + 12 * Δ := by
    intro ℓ₁ ℓ₂ h₁ h₂
    set a1 := tubeSlope ℓ₁ with ha1
    set a2 := tubeSlope ℓ₂ with ha2
    set b1 := tubeIntercept ℓ₁ with hb1
    set b2 := tubeIntercept ℓ₂ with hb2
    let d := |a1 - a2|
    have h1_v1 := hC_Q_v ℓ₁ h₁
    have h2_v1 := hC_Q_v ℓ₂ h₂
    have h_dir : ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ ≤ 2 * d :=
      TubesAndSlopes.direction_proj_upper_bound ℓ₁ ℓ₂ h1_v1 h2_v1
    have h_b2 : |b2| ≤ 3 := hC_Q_b ℓ₂ h₂
    have h_off1 := TubesAndSlopes.offset_formula ℓ₁ h1_v1
    have h_off2 := TubesAndSlopes.offset_formula ℓ₂ h2_v1
    have h_off : ‖ℓ₁.offset - ℓ₂.offset‖ ≤ (3 : ℝ) * d + |b1 - b2| :=
      TubesAndSlopes.offset_diff_bound_tight h_b2 (by norm_num) ℓ₁.offset ℓ₂.offset
        h_off1.1 h_off1.2 h_off2.1 h_off2.2
    have h_b : |b1 - b2| ≤ 12 * Δ + 2 * d := h_b_diff ℓ₁ ℓ₂ h₁ h₂
    have h_dist_def : AffineLine.dist ℓ₁ ℓ₂ =
        ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ + ‖ℓ₁.offset - ℓ₂.offset‖ := by rfl
    rw [h_dist_def]
    linarith
  -- Slope Lipschitz bound
  have h_f_lip : ∀ (ℓ₁ ℓ₂ : AffineLine), ℓ₁ ∈ (C_Q : Set AffineLine) → ℓ₂ ∈ (C_Q : Set AffineLine) →
      dist (f ℓ₁) (f ℓ₂) ≤ 2 * dist ℓ₁ ℓ₂ := by
    intro ℓ₁ ℓ₂ h₁ h₂
    have h1_v1 := hC_Q_v ℓ₁ h₁
    have h2_v1 := hC_Q_v ℓ₂ h₂
    have h1_s := hC_Q_a ℓ₁ h₁
    have h2_s := hC_Q_a ℓ₂ h₂
    exact TubesAndSlopes.slope_lipschitz ℓ₁ ℓ₂ h1_v1 h2_v1 h1_s h2_s
  -- Image covering bound: Ncover(f '' S) ≤ 4 * Ncover(S)
  have h_image_bound : ∀ (S : Set AffineLine), S.Nonempty → S ⊆ (C_Q : Set AffineLine) →
      Metric.externalCoveringNumber Δ.toNNReal (f '' S) ≤
        4 * Metric.externalCoveringNumber Δ.toNNReal S := by
    intro S hS_nonempty hS_sub
    let K : NNReal := 2
    have h_lip_on : ∀ (x y : AffineLine), x ∈ S → y ∈ S →
        dist (f x) (f y) ≤ (K : ℝ) * dist x y := by
      intro x y hx hy
      have h := h_f_lip x y (hS_sub hx) (hS_sub hy)
      simpa [K] using h
    have h1 : Metric.externalCoveringNumber (2 * K * Δ.toNNReal) (f '' S) ≤
        Metric.externalCoveringNumber Δ.toNNReal S :=
      TubesAndSlopes.externalCoveringNumber_image_lipschitz_on hS_nonempty h_lip_on
    have hK_eq : (2 * K * Δ.toNNReal : NNReal) = 4 * Δ.toNNReal := by
      have hK2 : 2 * K = (4 : NNReal) := by
        apply NNReal.coe_injective
        have h : ((2 * K : NNReal) : ℝ) = 4 := by simp [K] <;> norm_num
        exact_mod_cast h
      rw [hK2] <;> ring
    let imgS : Set ℝ := f '' S
    let δ2 : NNReal := 2 * Δ.toNNReal
    let δ4 : NNReal := 4 * Δ.toNNReal
    have h2 : Metric.externalCoveringNumber Δ.toNNReal imgS ≤
        2 * Metric.externalCoveringNumber δ2 imgS :=
      TubesAndSlopes.real_covering_doubling (by positivity)
    have h3 : Metric.externalCoveringNumber δ2 imgS ≤
        2 * Metric.externalCoveringNumber δ4 imgS := by
      have h := TubesAndSlopes.real_covering_doubling (S := imgS) (by positivity : 0 < δ2)
      have h_eq : (2 * δ2 : NNReal) = δ4 := by simp [δ2, δ4] <;> ring
      rw [h_eq] at h
      exact h
    have h4 : Metric.externalCoveringNumber δ4 imgS ≤
        Metric.externalCoveringNumber Δ.toNNReal S := by
      have h6 : δ4 = 4 * Δ.toNNReal := by rfl
      have h7 : (4 * Δ.toNNReal : NNReal) = 2 * K * Δ.toNNReal := hK_eq.symm
      rw [h6, h7]
      exact h1
    calc Metric.externalCoveringNumber Δ.toNNReal imgS
      ≤ 2 * Metric.externalCoveringNumber δ2 imgS := h2
    _ ≤ 2 * (2 * Metric.externalCoveringNumber δ4 imgS) := by gcongr
    _ = 4 * Metric.externalCoveringNumber δ4 imgS := by ring
    _ ≤ 4 * Metric.externalCoveringNumber Δ.toNNReal S := by gcongr
  -- Main S-set property
  have hC_pos : 0 < Real.rpow Δ (-25 * ε) := by
    apply Real.rpow_pos_of_pos hΔ_pos
  refine' ⟨hA_nonempty, hΔ_pos, hC_pos, by linarith, _⟩
  intro x r hr
  by_cases h_nonempty : (A ∩ Metric.closedBall x r).Nonempty
  · rcases h_nonempty with ⟨a₀, ha₀⟩
    have ha₀_A : a₀ ∈ A := ha₀.1
    have ha₀_ball : a₀ ∈ Metric.closedBall x r := ha₀.2
    rcases ha₀_A with ⟨ℓ₀, hℓ₀_T, rfl⟩
    have h_dist0 : dist (f ℓ₀) x ≤ r := Metric.mem_closedBall.mp ha₀_ball
    have h' : |f ℓ₀ - x| ≤ r := by
      have h_eq : dist (f ℓ₀) x = |f ℓ₀ - x| := by
        simp [dist_eq_norm, Real.norm_eq_abs] <;> rfl
      rw [h_eq] at h_dist0
      exact h_dist0
    let S : Set AffineLine := (C_Q : Set AffineLine) ∩ {ℓ | |f ℓ - x| ≤ r}
    have hℓ₀_in_S : ℓ₀ ∈ S := ⟨hℓ₀_T, h'⟩
    have hS_nonempty : S.Nonempty := ⟨ℓ₀, hℓ₀_in_S⟩
    have hS_sub : S ⊆ (C_Q : Set AffineLine) := by intro ℓ hℓ; exact hℓ.1
    have hS1 : A ∩ Metric.closedBall x r = f '' S := by
      ext y
      simp only [A, S, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨ℓ, hℓ, rfl⟩, hball⟩
        refine ⟨ℓ, ⟨hℓ, ?_⟩, rfl⟩
        have h : dist (f ℓ) x ≤ r := hball
        have h_eq2 : dist (f ℓ) x = |f ℓ - x| := by
          simp [dist_eq_norm, Real.norm_eq_abs] <;> rfl
        have h' : |f ℓ - x| ≤ r := by
          rw [h_eq2] at h
          exact h
        exact h'
      · rintro ⟨ℓ, ⟨hℓ, hstrip⟩, rfl⟩
        have h : dist (f ℓ) x ≤ r := by
          rw [show dist (f ℓ) x = |f ℓ - x| by simp [dist_eq_norm, Real.norm_eq_abs] <;> rfl]
          exact hstrip
        exact ⟨⟨ℓ, hℓ, rfl⟩, h⟩
    have hS2 : S ⊆ Metric.closedBall ℓ₀ (26 * r) := by
      intro ℓ hℓ
      have hℓ_T : ℓ ∈ (C_Q : Set AffineLine) := hℓ.1
      have hstrip : |f ℓ - x| ≤ r := hℓ.2
      have h_slope_diff : |f ℓ - f ℓ₀| ≤ 2 * r := by
        have h1 : |f ℓ - f ℓ₀| ≤ |f ℓ - x| + |x - f ℓ₀| := by exact abs_sub_le (f ℓ) x (f ℓ₀)
        have h2 : |x - f ℓ₀| ≤ r := by
          have h3 : |f ℓ₀ - x| ≤ r := hℓ₀_in_S.2
          rw [show x - f ℓ₀ = -(f ℓ₀ - x) by ring, abs_neg]
          exact h3
        linarith
      have h_dist : AffineLine.dist ℓ ℓ₀ ≤ 7 * |f ℓ - f ℓ₀| + 12 * Δ :=
        h_dist_bound ℓ ℓ₀ hℓ_T hℓ₀_T
      have h3 : AffineLine.dist ℓ ℓ₀ ≤ 26 * r := by
        calc AffineLine.dist ℓ ℓ₀
          ≤ 7 * |f ℓ - f ℓ₀| + 12 * Δ := h_dist
        _ ≤ 7 * (2 * r) + 12 * Δ := by gcongr
        _ = 14 * r + 12 * Δ := by ring
        _ ≤ 26 * r := by linarith [hr]
      have h4 : dist ℓ ℓ₀ ≤ 26 * r := h3
      exact h4
    have hS2' : S ⊆ (C_Q : Set AffineLine) ∩ Metric.closedBall ℓ₀ (26 * r) := by
      intro ℓ hℓ
      exact ⟨hℓ.1, hS2 hℓ⟩
    have hT_sset := hC_Q_sset.2.2.2.2
    have h4 : Metric.externalCoveringNumber Δ.toNNReal
        ((C_Q : Set AffineLine) ∩ Metric.closedBall ℓ₀ (26 * r)) ≤
        ENNReal.ofReal C2_Q * (ENNReal.ofReal (26 * r)) ^ s *
          Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set AffineLine) :=
      hT_sset ℓ₀ (26 * r) (by linarith [hr])
    have h5 : Metric.externalCoveringNumber Δ.toNNReal S ≤
        Metric.externalCoveringNumber Δ.toNNReal
          ((C_Q : Set AffineLine) ∩ Metric.closedBall ℓ₀ (26 * r)) :=
      Metric.externalCoveringNumber_mono_set hS2'
    have h6 : Metric.externalCoveringNumber Δ.toNNReal (f '' S) ≤
        4 * Metric.externalCoveringNumber Δ.toNNReal S :=
      h_image_bound S hS_nonempty hS_sub
    have h7 : (ENNReal.ofReal (26 * r)) ^ s ≤ ENNReal.ofReal 26 * (ENNReal.ofReal r) ^ s := by
      have hr_nonneg : 0 ≤ r := by linarith [hr]
      have h_ineq : (26 * r) ^ s ≤ 26 * r ^ s := by
        have h1 : ((26 : ℝ) * r) ^ s = (26 : ℝ) ^ s * r ^ s := by
          rw [Real.mul_rpow] <;> linarith
        rw [h1]
        have h2 : (26 : ℝ) ^ s ≤ (26 : ℝ) := by
          have h21 : (26 : ℝ) ^ s ≤ (26 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          have h22 : (26 : ℝ) ^ (1 : ℝ) = (26 : ℝ) := by simp
          rw [h22] at h21
          exact h21
        have h3 : 0 ≤ r ^ s := Real.rpow_nonneg (by linarith) s
        exact mul_le_mul_of_nonneg_right h2 h3
      have h4' : ENNReal.ofReal ((26 * r) ^ s) ≤ ENNReal.ofReal (26 * r ^ s) :=
        ENNReal.ofReal_le_ofReal h_ineq
      have h5' : (ENNReal.ofReal (26 * r)) ^ s = ENNReal.ofReal ((26 * r) ^ s) :=
        ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith)
      have h6' : ENNReal.ofReal (26 * r ^ s) = ENNReal.ofReal 26 * (ENNReal.ofReal r) ^ s := by
        have h71 : ENNReal.ofReal (26 * r ^ s) = ENNReal.ofReal 26 * ENNReal.ofReal (r ^ s) := by
          rw [ENNReal.ofReal_mul (by positivity)]
        rw [h71]
        have h8 : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) :=
          ENNReal.ofReal_rpow_of_nonneg hr_nonneg (by linarith)
        rw [h8]
      rw [h5']
      exact h4'.trans (le_of_eq h6')
    let eT : Set AffineLine → ENNReal := fun S => (Metric.externalCoveringNumber Δ.toNNReal S : ENNReal)
    let eR : Set ℝ → ENNReal := fun S => (Metric.externalCoveringNumber Δ.toNNReal S : ENNReal)
    have h4' : eT ((C_Q : Set AffineLine) ∩ Metric.closedBall ℓ₀ (26 * r)) ≤
        ENNReal.ofReal C2_Q * (ENNReal.ofReal (26 * r)) ^ s * eT (C_Q : Set AffineLine) := by
      dsimp only [eT]
      exact_mod_cast h4
    have h5' : eT S ≤ eT ((C_Q : Set AffineLine) ∩ Metric.closedBall ℓ₀ (26 * r)) := by
      have h5_cast : (Metric.externalCoveringNumber Δ.toNNReal S : ENNReal) ≤
          (Metric.externalCoveringNumber Δ.toNNReal
            ((C_Q : Set AffineLine) ∩ Metric.closedBall ℓ₀ (26 * r)) : ENNReal) :=
        by exact_mod_cast h5
      simpa [eT] using h5_cast
    have h6' : eR (f '' S) ≤ (4 : ENNReal) * eT S := by
      dsimp only [eR, eT]
      have h : (Metric.externalCoveringNumber Δ.toNNReal (f '' S) : ENNReal) ≤
          ((4 * Metric.externalCoveringNumber Δ.toNNReal S : ℕ∞) : ENNReal) := by
        exact_mod_cast h6
      have h2 : ((4 * Metric.externalCoveringNumber Δ.toNNReal S : ℕ∞) : ENNReal) =
          (4 : ENNReal) * (Metric.externalCoveringNumber Δ.toNNReal S : ENNReal) := by
        simp
      rw [h2] at h
      exact h
    have h_global' : eT (C_Q : Set AffineLine) ≤ (2000 : ENNReal) * eR A := by
      dsimp only [eT, eR]
      have h_eq : ENNReal.ofReal (2000 : ℝ) = (2000 : ENNReal) := by norm_cast
      rw [h_eq] at h_cover_transfer
      exact h_cover_transfer
    have h_const : (208000 : ℝ) ≤ Real.rpow Δ (-15 * ε) := by
      linarith [h_small_const]
    have hC2 : ENNReal.ofReal C2_Q ≤ ENNReal.ofReal (Real.rpow Δ (-10 * ε)) := by
      gcongr <;> linarith
    have h_final_const : (4 : ENNReal) * (ENNReal.ofReal 26) * (2000 : ENNReal) * ENNReal.ofReal C2_Q ≤
        ENNReal.ofReal (Real.rpow Δ (-25 * ε)) := by
      have h1 : (4 : ENNReal) * (ENNReal.ofReal 26) * (2000 : ENNReal) = ENNReal.ofReal (208000 : ℝ) := by
        norm_cast <;> simp [ENNReal.ofReal_mul] <;> ring
      rw [h1]
      have h2 : ENNReal.ofReal (208000 : ℝ) * ENNReal.ofReal C2_Q ≤
          ENNReal.ofReal (208000 : ℝ) * ENNReal.ofReal (Real.rpow Δ (-10 * ε)) := by
        gcongr <;> linarith
      have h3 : ENNReal.ofReal (208000 : ℝ) * ENNReal.ofReal (Real.rpow Δ (-10 * ε)) =
          ENNReal.ofReal (208000 * Real.rpow Δ (-10 * ε)) := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
      have h4 : 208000 * Real.rpow Δ (-10 * ε) ≤ Real.rpow Δ (-25 * ε) := by
        have h5 : Real.rpow Δ (-25 * ε) = Real.rpow Δ (-15 * ε) * Real.rpow Δ (-10 * ε) := by
          have h6 := Real.rpow_add hΔ_pos (-15 * ε) (-10 * ε)
          have h7 : (-15 * ε) + (-10 * ε) = -25 * ε := by ring
          rw [h7] at h6
          exact h6
        rw [h5]
        have h7 : 0 ≤ Real.rpow Δ (-10 * ε) := Real.rpow_nonneg (by linarith) _
        nlinarith [h_const]
      have h5 : ENNReal.ofReal (208000 * Real.rpow Δ (-10 * ε)) ≤
          ENNReal.ofReal (Real.rpow Δ (-25 * ε)) := by
        gcongr <;> linarith
      exact le_trans h2 (le_trans (le_of_eq h3) h5)
    calc eR (A ∩ Metric.closedBall x r)
      = eR (f '' S) := by rw [hS1]
    _ ≤ (4 : ENNReal) * eT S := h6'
    _ ≤ (4 : ENNReal) * eT ((C_Q : Set AffineLine) ∩ Metric.closedBall ℓ₀ (26 * r)) := by
      gcongr <;> exact h5'
    _ ≤ (4 : ENNReal) * (ENNReal.ofReal C2_Q * (ENNReal.ofReal (26 * r)) ^ s * eT (C_Q : Set AffineLine)) := by
      gcongr <;> exact h4'
    _ ≤ (4 : ENNReal) * (ENNReal.ofReal C2_Q * (ENNReal.ofReal 26 * (ENNReal.ofReal r) ^ s) * eT (C_Q : Set AffineLine)) := by
      gcongr <;> exact h7
    _ = (4 : ENNReal) * (ENNReal.ofReal 26) * ENNReal.ofReal C2_Q * (ENNReal.ofReal r) ^ s * eT (C_Q : Set AffineLine) := by
      simp [mul_assoc] <;> ring
    _ ≤ (4 : ENNReal) * (ENNReal.ofReal 26) * ENNReal.ofReal C2_Q * (ENNReal.ofReal r) ^ s * ((2000 : ENNReal) * eR A) := by
      gcongr <;> exact h_global'
    _ = ((4 : ENNReal) * (ENNReal.ofReal 26) * (2000 : ENNReal) * ENNReal.ofReal C2_Q) * (ENNReal.ofReal r) ^ s * eR A := by
      simp [mul_assoc] <;> ring
    _ ≤ ENNReal.ofReal (Real.rpow Δ (-25 * ε)) * (ENNReal.ofReal r) ^ s * eR A := by
      gcongr
  · have h_eq : (A ∩ Metric.closedBall x r) = ∅ := by
      by_contra h
      have h' : (A ∩ Metric.closedBall x r).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr h
      exact h_nonempty h'
    rw [h_eq]
    simp [Metric.externalCoveringNumber_eq_zero.mpr h_eq]

/-! ### Gap 3: hP_Q_sset

  Transfers IsDeltaSSet from P to P_Q using cover ratio.
  Given |P| ≤ K_Q * |P_Q| and P_Q δ-separated, the S-set constant
  blows up by K_Q * 81.
-/

/-- Transfer S-set from P to subset P_Q using cardinality ratio. -/
lemma gap3_hP_Q_sset
    {δ t C_P K_Q Δ ε : ℝ}
    {P P_Q : Finset Plane}
    (hP_sset : IsDeltaSSet δ t C_P (P : Set Plane))
    (hP_Q_sub : P_Q ⊆ P)
    (hP_Q_separated : SeparatedAt δ (P_Q : Set Plane))
    (hδ_pos : 0 < δ)
    (hP_card_le : (P.card : ℝ) ≤ K_Q * (P_Q.card : ℝ))
    (hK_Q_pos : 0 < K_Q)
    (h_sset_constraint : C_P * K_Q * 81 ≤ Real.rpow Δ (-t - 10 * ε)) :
    IsDeltaSSet δ t (Real.rpow Δ (-t - 10 * ε)) (P_Q : Set Plane) := by
  have h1 : (Metric.externalCoveringNumber δ.toNNReal (P : Set Plane) : ENNReal) ≤ ↑(P.card) :=
    by exact_mod_cast Metric.externalCoveringNumber_le_encard_self (P : Set Plane)
  have h2 : (↑(P.card) : ENNReal) ≤ ENNReal.ofReal K_Q * ↑(P_Q.card) := by
    have h21 : (P.card : ℝ) ≤ K_Q * (P_Q.card : ℝ) := hP_card_le
    have h22 : (↑(P.card) : ENNReal) = ENNReal.ofReal (P.card : ℝ) := by simp
    rw [h22]
    have h23 : ENNReal.ofReal K_Q * (↑(P_Q.card) : ENNReal) = ENNReal.ofReal (K_Q * (P_Q.card : ℝ)) := by
      have h24 : (↑(P_Q.card) : ENNReal) = ENNReal.ofReal (P_Q.card : ℝ) := by simp
      rw [h24]
      rw [← ENNReal.ofReal_mul (by positivity)]
      <;> ring
    rw [h23]
    exact ENNReal.ofReal_le_ofReal h21
  have h3 : ENNReal.ofReal (1 / 81 : ℝ) * ↑(P_Q.card) ≤
      (Metric.externalCoveringNumber δ.toNNReal (P_Q : Set Plane) : ENNReal) :=
    ncover_lower_bound_separated81 hδ_pos hP_Q_separated
  have h4 : (↑(P_Q.card) : ENNReal) ≤ (81 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (P_Q : Set Plane) : ENNReal) := by
    have h41 : ENNReal.ofReal (1 / 81 : ℝ) * ↑(P_Q.card) ≤
        (Metric.externalCoveringNumber δ.toNNReal (P_Q : Set Plane) : ENNReal) := h3
    have h42 : (↑(P_Q.card) : ENNReal) = (81 : ENNReal) * (ENNReal.ofReal (1 / 81 : ℝ) * ↑(P_Q.card)) := by
      have h : (81 : ENNReal) * ENNReal.ofReal (1 / 81 : ℝ) = 1 := by
        have h51 : (81 : ENNReal) = ENNReal.ofReal (81 : ℝ) := by norm_cast
        rw [h51]
        have h52 : ENNReal.ofReal (81 : ℝ) * ENNReal.ofReal (1 / 81 : ℝ) = ENNReal.ofReal ((81 : ℝ) * (1 / 81 : ℝ)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          <;> ring
        rw [h52]
        have h53 : (81 : ℝ) * (1 / 81 : ℝ) = 1 := by norm_num
        rw [h53]
        <;> simp
      rw [← mul_assoc, h, one_mul]
    rw [h42]
    exact mul_le_mul_left' h41 _
  let K_ratio : ℝ := K_Q * 81
  have hK_ratio_pos : 0 < K_ratio := by positivity
  have h5 : (Metric.externalCoveringNumber δ.toNNReal (P : Set Plane) : ENNReal) ≤
      ENNReal.ofReal K_ratio * (Metric.externalCoveringNumber δ.toNNReal (P_Q : Set Plane) : ENNReal) := by
    calc (Metric.externalCoveringNumber δ.toNNReal (P : Set Plane) : ENNReal)
      ≤ ↑(P.card) := h1
    _ ≤ ENNReal.ofReal K_Q * ↑(P_Q.card) := h2
    _ ≤ ENNReal.ofReal K_Q * ((81 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (P_Q : Set Plane) : ENNReal)) := by gcongr
    _ = ENNReal.ofReal K_ratio * (Metric.externalCoveringNumber δ.toNNReal (P_Q : Set Plane) : ENNReal) := by
      have h_eq1 : ENNReal.ofReal K_Q * ((81 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (P_Q : Set Plane) : ENNReal)) =
          (ENNReal.ofReal K_Q * (81 : ENNReal)) * (Metric.externalCoveringNumber δ.toNNReal (P_Q : Set Plane) : ENNReal) := by rw [mul_assoc]
      rw [h_eq1]
      have h_eq2 : ENNReal.ofReal K_Q * (81 : ENNReal) = ENNReal.ofReal (K_Q * 81) := by
        have h : (81 : ENNReal) = ENNReal.ofReal (81 : ℝ) := by norm_cast
        rw [h]
        rw [← ENNReal.ofReal_mul (by positivity)]
        <;> ring
      rw [h_eq2]
      <;> rfl
  have h6 : IsDeltaSSet δ t (K_ratio * C_P) (P_Q : Set Plane) :=
    IsDeltaSSet.subset_with_cover_ratio hK_ratio_pos hP_sset
      (by exact_mod_cast hP_Q_sub) h5
  have h7 : K_ratio * C_P ≤ Real.rpow Δ (-t - 10 * ε) := by
    dsimp only [K_ratio]
    linarith [h_sset_constraint]
  exact IsDeltaSSet.mono_const h6 h7

end DirecretisedFurstenbergEstimate.AppendixA.A2_RemainingGaps
