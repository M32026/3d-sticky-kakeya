module

/-
  A4 helper: hC_Q_pi_sset and hC_Q_pi_card proofs.

  Uses the concrete packing constant affinePackingM = 9^6 from AffineLinePackingBound.

  Chain:
    Ncover(Δ, C_Q) ≤ 20 · Ncover(Δ, slopeSet)
                  ≤ 40 · Ncover(Δ, goodDirections)
                  ≤ 40 · |goodDirections| ≤ 40 · |C_Q_pi|
                  ≤ 40 · affinePackingM · Ncover(Δ, C_Q_pi)   [for sset]
    |C_Q| ≤ affinePackingM · Ncover(C_Q) ≤ 40 · affinePackingM · |C_Q_pi|  [for card]

  Requires smallness: 40 · affinePackingM ≤ Δ^{-ε}.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.AffineLinePackingBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal Classical

namespace DirecretisedFurstenbergEstimate.AppendixA4

open DirecretisedFurstenbergEstimate

/-! ### Generalized subset transfer -/

lemma IsDeltaSSet.subset_with_cover_ratio {X : Type*} [PseudoMetricSpace X]
    {δ s C : ℝ} {S S' : Set X} {K : ℝ} (hK_pos : 0 < K)
    (hS : IsDeltaSSet δ s C S)
    (hS'_sub : S' ⊆ S)
    (h_ratio : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤
               ENNReal.ofReal K * (Metric.externalCoveringNumber δ.toNNReal S')) :
    IsDeltaSSet δ s (K * C) S' := by
  rcases hS with ⟨hS_nonempty, hδ_pos, hC_pos, hs_nonneg, h_main⟩
  have hKC_pos : 0 < K * C := mul_pos hK_pos hC_pos
  have hS'_nonempty : S'.Nonempty := by
    by_contra h
    have h_empty : S' = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h
    rw [h_empty] at h_ratio
    have h_zero : Metric.externalCoveringNumber δ.toNNReal S = 0 := by
      have h_le : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤ 0 := by
        simpa [Metric.externalCoveringNumber_empty] using h_ratio
      exact le_zero_iff.mp (by exact_mod_cast h_le)
    have hS_empty : S = ∅ := Metric.externalCoveringNumber_eq_zero.mp h_zero
    rw [hS_empty] at hS_nonempty; simp at hS_nonempty
  refine' ⟨hS'_nonempty, hδ_pos, hKC_pos, hs_nonneg, _⟩
  intro x r hr
  have h_sub : S' ∩ Metric.closedBall x r ⊆ S ∩ Metric.closedBall x r := by
    intro y hy; exact ⟨hS'_sub hy.1, hy.2⟩
  have h1 : (Metric.externalCoveringNumber δ.toNNReal (S' ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall x r) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set (ε := δ.toNNReal) h_sub
  have h2 := h_main x r hr
  have hC_nonneg : 0 ≤ C := by linarith
  calc (Metric.externalCoveringNumber δ.toNNReal (S' ∩ Metric.closedBall x r) : ENNReal)
    ≤ (Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall x r) : ENNReal) := h1
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := h2
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal K * Metric.externalCoveringNumber δ.toNNReal S') := by gcongr
    _ = ENNReal.ofReal (K * C) * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal S' := by
      have h_mul : ENNReal.ofReal C * ENNReal.ofReal K = ENNReal.ofReal (K * C) := by
        rw [← ENNReal.ofReal_mul hC_nonneg, mul_comm]
      have h_assoc : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal K * Metric.externalCoveringNumber δ.toNNReal S') =
          (ENNReal.ofReal C * ENNReal.ofReal K) * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal S' := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      rw [h_assoc, h_mul] <;> simp [mul_assoc]

/-! ### Covering ratio lemma -/

lemma covering_ratio_CQ_pi
    {C_Q C_Q_pi : Finset AffineLine}
    {slopeSet goodDirections : Set ℝ}
    {Δ : ℝ} (hΔ_pos : 0 < Δ)
    (f : AffineLine → ℝ)
    (hC_Q_sep : (C_Q : Set AffineLine).Pairwise fun x y => Δ ≤ dist x y)
    (hC_Q_pi_sub : C_Q_pi ⊆ C_Q)
    (h_cover_transfer : (Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set AffineLine) : ENNReal) ≤
        ENNReal.ofReal (2000 : ℝ) * Metric.externalCoveringNumber Δ.toNNReal slopeSet)
    (h_rkp : (Metric.externalCoveringNumber Δ.toNNReal slopeSet : ENNReal) ≤
        2 * Metric.externalCoveringNumber Δ.toNNReal goodDirections)
    (h_good_img : goodDirections ⊆ f '' (C_Q_pi : Set AffineLine)) :
    (Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set AffineLine) : ENNReal) ≤
      (4000 : ENNReal) * (affinePackingM : ENNReal) *
      Metric.externalCoveringNumber Δ.toNNReal (C_Q_pi : Set AffineLine) := by
  let δnn : NNReal := Δ.toNNReal

  have h_sep_pi : (C_Q_pi : Set AffineLine).Pairwise fun x y => Δ ≤ dist x y :=
    hC_Q_sep.mono (by exact_mod_cast hC_Q_pi_sub)

  have h_good_fin : goodDirections.Finite :=
    Set.Finite.subset (C_Q_pi.finite_toSet.image f) h_good_img
  let goodDirFin : Finset ℝ := h_good_fin.toFinset

  have h31 : (Metric.externalCoveringNumber δnn goodDirections : ENNReal) ≤ ↑(goodDirFin.card) := by
    have h : Metric.externalCoveringNumber δnn goodDirections ≤ goodDirections.encard :=
      Metric.externalCoveringNumber_le_encard_self (A := goodDirections)
    have h_coe : (goodDirFin : Set ℝ) = goodDirections := Set.Finite.coe_toFinset h_good_fin
    have h2 : goodDirections.encard = ↑(goodDirFin.card) := by
      rw [← h_coe] <;> simp
    rw [h2] at h; exact_mod_cast h

  have h32 : goodDirFin.card ≤ C_Q_pi.card := by
    have h_sub : goodDirFin ⊆ C_Q_pi.image f := by
      intro x hx
      have h_in : x ∈ goodDirections := by
        simpa [goodDirFin, Set.Finite.mem_toFinset] using hx
      exact_mod_cast h_good_img h_in
    have h_card1 : goodDirFin.card ≤ (C_Q_pi.image f).card := Finset.card_le_card h_sub
    have h_card2 : (C_Q_pi.image f).card ≤ C_Q_pi.card := by exact Finset.card_image_le
    linarith

  have h33 : (Metric.externalCoveringNumber δnn goodDirections : ENNReal) ≤ ↑(C_Q_pi.card) := by
    calc (Metric.externalCoveringNumber δnn goodDirections : ENNReal)
      ≤ ↑(goodDirFin.card) := h31
    _ ≤ ↑(C_Q_pi.card) := by exact_mod_cast h32

  have h4 : (↑(C_Q_pi.card) : ENNReal) ≤
      (affinePackingM : ENNReal) * Metric.externalCoveringNumber δnn (C_Q_pi : Set AffineLine) :=
    affineLine_ncover_lower hΔ_pos (hS_sep := h_sep_pi)

  calc (Metric.externalCoveringNumber δnn (C_Q : Set AffineLine) : ENNReal)
    ≤ ENNReal.ofReal (2000 : ℝ) * Metric.externalCoveringNumber δnn slopeSet := h_cover_transfer
  _ ≤ ENNReal.ofReal (2000 : ℝ) * (2 * Metric.externalCoveringNumber δnn goodDirections) := by gcongr <;> exact h_rkp
  _ ≤ ENNReal.ofReal (2000 : ℝ) * (2 * ↑(C_Q_pi.card)) := by gcongr <;> exact h33
  _ ≤ ENNReal.ofReal (2000 : ℝ) * (2 * ((affinePackingM : ENNReal) * Metric.externalCoveringNumber δnn (C_Q_pi : Set AffineLine))) := by gcongr <;> exact h4
  _ = (4000 : ENNReal) * (affinePackingM : ENNReal) * Metric.externalCoveringNumber δnn (C_Q_pi : Set AffineLine) := by
    simp [mul_assoc, mul_comm, mul_left_comm] <;> ring

/-! ### hC_Q_pi_sset -/

lemma hC_Q_pi_sset_main
    {C_Q C_Q_pi : Finset AffineLine}
    {slopeSet goodDirections : Set ℝ}
    {Δ s ε C2_Q : ℝ}
    (hΔ_pos : 0 < Δ) (hε_pos : 0 < ε) (hΔ_lt_one : Δ < 1)
    (f : AffineLine → ℝ)
    (hC_Q_sset : IsDeltaSSet Δ s C2_Q (C_Q : Set AffineLine))
    (hC_Q_sep : (C_Q : Set AffineLine).Pairwise fun x y => Δ ≤ dist x y)
    (hC_Q_pi_sub : C_Q_pi ⊆ C_Q)
    (h_cover_transfer : (Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set AffineLine) : ENNReal) ≤
        ENNReal.ofReal (2000 : ℝ) * Metric.externalCoveringNumber Δ.toNNReal slopeSet)
    (h_rkp : (Metric.externalCoveringNumber Δ.toNNReal slopeSet : ENNReal) ≤
        2 * Metric.externalCoveringNumber Δ.toNNReal goodDirections)
    (h_good_img : goodDirections ⊆ f '' (C_Q_pi : Set AffineLine))
    (hC2_Q_loss : C2_Q ≤ Real.rpow Δ (-10 * ε))
    (h_small : (4000 : ENNReal) * (affinePackingM : ENNReal) ≤
        ENNReal.ofReal (Real.rpow Δ (-49 * ε))) :
    IsDeltaSSet Δ s (Real.rpow Δ (-59 * ε)) (C_Q_pi : Set AffineLine) := by
  let K : ℝ := 4000 * (affinePackingM : ℝ)
  have hK_pos : 0 < K := by
    dsimp only [K]
    have hM_pos : 0 < (affinePackingM : ℝ) := by
      simp [affinePackingM] <;> norm_num
    exact mul_pos (by norm_num) hM_pos
  have h_ratio := covering_ratio_CQ_pi hΔ_pos f hC_Q_sep hC_Q_pi_sub h_cover_transfer h_rkp h_good_img
  have h_ratio' : (Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set AffineLine) : ENNReal) ≤
      ENNReal.ofReal K * Metric.externalCoveringNumber Δ.toNNReal (C_Q_pi : Set AffineLine) := by
    have h_eq : (4000 : ENNReal) * (affinePackingM : ENNReal) = ENNReal.ofReal K := by
      simp [K] <;> norm_cast
    rw [h_eq] at h_ratio
    exact h_ratio
  have h6 : IsDeltaSSet Δ s (K * C2_Q) (C_Q_pi : Set AffineLine) :=
    IsDeltaSSet.subset_with_cover_ratio hK_pos hC_Q_sset
      (by exact_mod_cast hC_Q_pi_sub) h_ratio'
  have h7 : K * C2_Q ≤ Real.rpow Δ (-59 * ε) := by
    have h8 : K * C2_Q ≤ K * Real.rpow Δ (-10 * ε) := by gcongr
    have h9 : Real.rpow Δ (-59 * ε) = Real.rpow Δ (-10 * ε) * Real.rpow Δ (-49 * ε) := by
      have h10 : (-59 * ε) = (-10 * ε) + (-49 * ε) := by ring
      have h11 : Real.rpow Δ ((-10 * ε) + (-49 * ε)) = Real.rpow Δ (-10 * ε) * Real.rpow Δ (-49 * ε) :=
        Real.rpow_add hΔ_pos (-10 * ε) (-49 * ε)
      rw [h10] at *
      exact h11
    rw [h9]
    have hK_eq : ENNReal.ofReal K = (4000 : ENNReal) * (affinePackingM : ENNReal) := by
      simp [K] <;> norm_cast
    have h10 : ENNReal.ofReal K ≤ ENNReal.ofReal (Real.rpow Δ (-49 * ε)) := by
      rw [hK_eq]
      exact h_small
    have h11 : K ≤ Real.rpow Δ (-49 * ε) := by
      have h_nonneg1 : 0 ≤ K := by positivity
      have h_nonneg2 : 0 ≤ Real.rpow Δ (-49 * ε) := Real.rpow_nonneg (by linarith) _
      exact (ENNReal.ofReal_le_ofReal_iff h_nonneg2).mp h10
    have h12 : 0 ≤ Real.rpow Δ (-10 * ε) := Real.rpow_nonneg (by linarith) _
    nlinarith
  have h13 : 0 < Real.rpow Δ (-59 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  have h14 : IsDeltaSSet Δ s (Real.rpow Δ (-59 * ε)) (C_Q_pi : Set AffineLine) := by
    rcases h6 with ⟨hne, hδ, hC_old_pos, hs, hmain⟩
    refine ⟨hne, hδ, h13, hs, fun x r hr => ?_⟩
    have h15 := hmain x r hr
    calc (Metric.externalCoveringNumber Δ.toNNReal ((C_Q_pi : Set AffineLine) ∩ Metric.closedBall x r) : ENNReal)
      ≤ ENNReal.ofReal (K * C2_Q) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber Δ.toNNReal (C_Q_pi : Set AffineLine) : ENNReal) := h15
    _ ≤ ENNReal.ofReal (Real.rpow Δ (-59 * ε)) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber Δ.toNNReal (C_Q_pi : Set AffineLine) : ENNReal) := by
      gcongr <;> exact h7
  exact h14

/-! ### hC_Q_pi_card -/

lemma hC_Q_pi_card_main2
    {C_Q C_Q_pi : Finset AffineLine}
    {slopeSet goodDirections : Set ℝ}
    {Δ ε : ℝ}
    (hΔ_pos : 0 < Δ)
    (f : AffineLine → ℝ)
    (hC_Q_sep : (C_Q : Set AffineLine).Pairwise fun x y => Δ ≤ dist x y)
    (hC_Q_pi_sub : C_Q_pi ⊆ C_Q)
    (h_cover_transfer : (Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set AffineLine) : ENNReal) ≤
        ENNReal.ofReal (2000 : ℝ) * Metric.externalCoveringNumber Δ.toNNReal slopeSet)
    (h_rkp : (Metric.externalCoveringNumber Δ.toNNReal slopeSet : ENNReal) ≤
        2 * Metric.externalCoveringNumber Δ.toNNReal goodDirections)
    (h_good_img : goodDirections ⊆ f '' (C_Q_pi : Set AffineLine))
    (h_small : (4000 : ENNReal) * (affinePackingM : ENNReal) ≤
        ENNReal.ofReal (Real.rpow Δ (-ε))) :
    (C_Q.card : ℝ) ≤ Real.rpow Δ (-ε) * (C_Q_pi.card : ℝ) := by
  let δnn : NNReal := Δ.toNNReal

  have h_good_fin : goodDirections.Finite :=
    Set.Finite.subset (C_Q_pi.finite_toSet.image f) h_good_img
  let goodDirFin : Finset ℝ := h_good_fin.toFinset

  have h31 : (Metric.externalCoveringNumber δnn goodDirections : ENNReal) ≤ ↑(goodDirFin.card) := by
    have h : Metric.externalCoveringNumber δnn goodDirections ≤ goodDirections.encard :=
      Metric.externalCoveringNumber_le_encard_self (A := goodDirections)
    have h_coe : (goodDirFin : Set ℝ) = goodDirections := Set.Finite.coe_toFinset h_good_fin
    have h2 : goodDirections.encard = ↑(goodDirFin.card) := by
      rw [← h_coe] <;> simp
    rw [h2] at h; exact_mod_cast h

  have h32 : goodDirFin.card ≤ C_Q_pi.card := by
    have h_sub : goodDirFin ⊆ C_Q_pi.image f := by
      intro x hx
      have h_in : x ∈ goodDirections := by
        simpa [goodDirFin, Set.Finite.mem_toFinset] using hx
      exact_mod_cast h_good_img h_in
    have h_card1 : goodDirFin.card ≤ (C_Q_pi.image f).card := Finset.card_le_card h_sub
    have h_card2 : (C_Q_pi.image f).card ≤ C_Q_pi.card := by exact Finset.card_image_le
    linarith

  have h33 : (Metric.externalCoveringNumber δnn goodDirections : ENNReal) ≤ ↑(C_Q_pi.card) := by
    calc (Metric.externalCoveringNumber δnn goodDirections : ENNReal)
      ≤ ↑(goodDirFin.card) := h31
    _ ≤ ↑(C_Q_pi.card) := by exact_mod_cast h32

  have h1 : (↑(C_Q.card) : ENNReal) ≤
      (affinePackingM : ENNReal) * Metric.externalCoveringNumber δnn (C_Q : Set AffineLine) :=
    affineLine_ncover_lower hΔ_pos (hS_sep := hC_Q_sep)

  have h4 : (↑(C_Q.card) : ENNReal) ≤
      (4000 : ENNReal) * (affinePackingM : ENNReal) * ↑(C_Q_pi.card) := by
    calc (↑(C_Q.card) : ENNReal)
      ≤ (affinePackingM : ENNReal) * Metric.externalCoveringNumber δnn (C_Q : Set AffineLine) := h1
    _ ≤ (affinePackingM : ENNReal) * (ENNReal.ofReal (2000 : ℝ) * Metric.externalCoveringNumber δnn slopeSet) := by gcongr <;> exact h_cover_transfer
    _ ≤ (affinePackingM : ENNReal) * (ENNReal.ofReal (2000 : ℝ) * (2 * Metric.externalCoveringNumber δnn goodDirections)) := by gcongr <;> exact h_rkp
    _ ≤ (affinePackingM : ENNReal) * (ENNReal.ofReal (2000 : ℝ) * (2 * ↑(C_Q_pi.card))) := by gcongr <;> exact h33
    _ = (4000 : ENNReal) * (affinePackingM : ENNReal) * ↑(C_Q_pi.card) := by
      simp [mul_assoc, mul_comm, mul_left_comm] <;> ring

  have h5 : (↑(C_Q.card) : ENNReal) ≤
      ENNReal.ofReal (Real.rpow Δ (-ε)) * ↑(C_Q_pi.card) := by
    calc (↑(C_Q.card) : ENNReal)
      ≤ (4000 : ENNReal) * (affinePackingM : ENNReal) * ↑(C_Q_pi.card) := h4
    _ ≤ ENNReal.ofReal (Real.rpow Δ (-ε)) * ↑(C_Q_pi.card) := by gcongr <;> exact h_small

  have h_rpow_nonneg : 0 ≤ Real.rpow Δ (-ε) := Real.rpow_nonneg (by linarith) _
  have h_card_coe : (↑(C_Q_pi.card) : ENNReal) = ENNReal.ofReal (C_Q_pi.card : ℝ) := by simp
  rw [h_card_coe] at h5
  have h_mul : ENNReal.ofReal (Real.rpow Δ (-ε)) * ENNReal.ofReal (C_Q_pi.card : ℝ) =
      ENNReal.ofReal (Real.rpow Δ (-ε) * (C_Q_pi.card : ℝ)) := by
    rw [← ENNReal.ofReal_mul h_rpow_nonneg] <;> rfl
  rw [h_mul] at h5
  have h9 : (↑(C_Q.card) : ENNReal) = ENNReal.ofReal (C_Q.card : ℝ) := by simp
  rw [h9] at h5
  have h_nonneg : 0 ≤ Real.rpow Δ (-ε) * (C_Q_pi.card : ℝ) := by positivity
  exact (ENNReal.ofReal_le_ofReal_iff h_nonneg).mp h5

end DirecretisedFurstenbergEstimate.AppendixA4
