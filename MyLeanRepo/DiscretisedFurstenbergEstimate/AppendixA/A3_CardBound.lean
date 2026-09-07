module

/-
  Standalone A3 card bound lemma.

  Given Q0 with uniform |C_Q|, per-square A2 data, global tube bounds,
  and an energy bound, prove |C_Q| ≤ Δ^{-s-29ε}.

  Uses global_2s_bound_no_hP_large with the K >> 1 branch.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A3_GeometricLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A3_CoarseSquareEnergyBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Global2sBoundNoHLarge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquaresToEnergy
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HCommonWiring
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA3

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.Lagoon (squareCenter squareCenter_zero squareCenter_one point_in_square_close_to_center)
open DirecretisedFurstenbergEstimate.Global2sBound (global_2s_bound_no_hP_large tubeDecidableEq)
open DirecretisedFurstenbergEstimate.Phase2 (squareCenter_injective)

/-- The center of a coarse square lies inside the square. -/
lemma square_center_in_square {Δ : ℝ} (hΔ_pos : 0 < Δ) (Q : CoarseSquare Δ) :
    squareCenter Δ Q ∈ squareSet Δ Q := by
  have hx : squareCenter Δ Q 0 = Δ * ((Q.1 : ℝ) + 1 / 2) := squareCenter_zero Δ Q
  have hy : squareCenter Δ Q 1 = Δ * ((Q.2 : ℝ) + 1 / 2) := squareCenter_one Δ Q
  constructor
  · rw [hx]; constructor <;> linarith
  · rw [hy]; constructor <;> linarith

/-- Genuine A3 card bound: |C_Q| ≤ Δ^{-s-25ε} for all Q ∈ Q0. -/
lemma a3_card_bound_genuine
    (Δ δ s t ε : ℝ)
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (hε_pos : 0 < ε)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (ht_pos : 0 < t) (hst : s < t)
    {Qset_all Q0 : Finset (CoarseSquare Δ)}
    (sd : ∀ (Q : CoarseSquare Δ), Q ∈ Qset_all → A2_SquareData Δ δ s t ε Q)
    (hQ0_sub : Q0 ⊆ Qset_all)
    (hQ0_nonempty : Q0.Nonempty)
    (C_card_uniform : ℝ)
    (hC_card_pos : 0 < C_card_uniform)
    (hC_direct : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
      C_card_uniform ≤ ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) ∧
      ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) < 2 * C_card_uniform)
    (K_card : ℝ) (hK_card_pos : 0 < K_card)
    (C_global : Finset CoarseTube)
    (hC_global_card_upper : (C_global.card : ℝ) ≤ K_card * Real.rpow Δ (-2 * s - 3 * ε))
    (hC_Q_sub_global : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
      (sd Q (hQ0_sub hQ)).C_Q ⊆ C_global)
    (hCenter_bound : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0), ‖squareCenter Δ Q‖ ≤ 2)
    (hDist_le_3 : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0) (R : CoarseSquare Δ) (hR : R ∈ Q0),
      dist (squareCenter Δ Q) (squareCenter Δ R) ≤ 3)
    (h_energy : ∑ p ∈ (Q0.image (squareCenter Δ)),
        ∑ q ∈ (Q0.image (squareCenter Δ)).erase p, Real.rpow (dist p q) (-s) ≤
        Real.rpow Δ (-14 * ε) * ((Q0.image (squareCenter Δ)).card : ℝ)^2)
    (hQ0_card_lower : (Q0.card : ℝ) ≥ (Qset_all.card : ℝ) / Real.rpow Δ (-ε))
    (hQset_card_lower : (Qset_all.card : ℝ) ≥ Real.rpow Δ (-t + 3 * ε))
    (h_card_absorb_genuine : (8 * (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s) * K_card *
        Real.rpow Δ (-s - 27 * ε) ≤ Real.rpow Δ (-s - 29 * ε))
    (h_card_absorb_smallK : (8 : ℝ) * K_card *
        Real.rpow Δ (t - 2 * s - 7 * ε) ≤ Real.rpow Δ (-s - 29 * ε)) :
    ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
      ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) ≤ Real.rpow Δ (-s - 29 * ε) := by
  let P_thin : Finset Plane := Q0.image (squareCenter Δ)
  let Tp (p : Plane) : Finset CoarseTube :=
    if h : p ∈ P_thin then
      let Q : CoarseSquare Δ := Classical.choose (Finset.mem_image.mp h)
      let hQ : Q ∈ Q0 := (Classical.choose_spec (Finset.mem_image.mp h)).1
      (sd Q (hQ0_sub hQ)).C_Q
    else ∅
  let M_val : ℝ := 2 * C_card_uniform
  let C_common : ℝ := (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s
  let C_P : ℝ := Real.rpow Δ (-14 * ε)
  let C_T : ℝ := Real.rpow Δ (-10 * ε)
  let K_energy : ℝ := 1

  have hM_val_pos : 0 < M_val := by
    dsimp only [M_val]; exact mul_pos (by norm_num) hC_card_pos

  have hCcommon_pos : 0 < C_common := by
    dsimp only [C_common]
    have h1 : 0 < (MainAppendix.affineLine_packing_constant : ℝ) := by
      have h2 : 0 < MainAppendix.affineLine_packing_constant :=
        MainAppendix.affineLine_packing_constant_pos
      exact_mod_cast h2
    have h2 : 0 < ((800 * (54 : ℝ)) : ℝ)^s := Real.rpow_pos_of_pos (by positivity) _
    exact mul_pos h1 h2

  have hKpack_pos : 0 < (MainAppendix.affineLine_packing_constant : ℝ) := by
    have h2 : 0 < MainAppendix.affineLine_packing_constant :=
      MainAppendix.affineLine_packing_constant_pos
    exact_mod_cast h2
  have hCP_pos : 0 < C_P := Real.rpow_pos_of_pos hΔ_pos _
  have hCT_pos : 0 < C_T := Real.rpow_pos_of_pos hΔ_pos _
  have hKe_pos : 0 < K_energy := by norm_num

  have h_inj : Function.Injective (squareCenter Δ) := squareCenter_injective hΔ_pos

  have hPthin_nonempty : P_thin.Nonempty := hQ0_nonempty.image _

  have hPthin_sep : Set.Pairwise (P_thin : Set Plane) (fun p q => Δ ≤ dist p q) := by
    intro p hp q hq hne
    rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨R, hR, rfl⟩
    have hQR : Q ≠ R := by intro h; apply hne; rw [h]
    exact square_center_dist_ge hΔ_pos hQR

  have hPthin_card : P_thin.card = Q0.card := Finset.card_image_of_injective _ h_inj

  have hTp_at_center : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
      Tp (squareCenter Δ Q) = (sd Q (hQ0_sub hQ)).C_Q := by
    intro Q hQ
    have h : squareCenter Δ Q ∈ P_thin := Finset.mem_image.mpr ⟨Q, hQ, rfl⟩
    dsimp only [Tp]
    rw [dif_pos h]
    let Qc := Classical.choose (Finset.mem_image.mp h)
    have hQc1 : Qc ∈ Q0 := (Classical.choose_spec (Finset.mem_image.mp h)).1
    have hQc2 : squareCenter Δ Qc = squareCenter Δ Q :=
      (Classical.choose_spec (Finset.mem_image.mp h)).2
    have h_eq : Qc = Q := h_inj hQc2
    have h_main : ∀ (x y : CoarseSquare Δ) (hx : x ∈ Q0) (hy : y ∈ Q0),
        x = y → (sd x (hQ0_sub hx)).C_Q = (sd y (hQ0_sub hy)).C_Q := by
      intro x y hx hy hxy
      induction hxy
      <;> rfl
    exact h_main Qc Q hQc1 hQ h_eq

  have hTp_card_lower : ∀ p ∈ P_thin, (M_val / 2 : ℝ) ≤ (Tp p).card := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
    rw [hTp_at_center Q hQ]
    have h1 : C_card_uniform ≤ ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) := (hC_direct Q hQ).1
    have h2 : (M_val / 2 : ℝ) = C_card_uniform := by
      dsimp only [M_val] <;> ring
    rw [h2]; exact h1

  have hTp_card_upper : ∀ p ∈ P_thin, (Tp p).card ≤ M_val := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
    rw [hTp_at_center Q hQ]
    have h1 : ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) < 2 * C_card_uniform := (hC_direct Q hQ).2
    have h2 : (M_val : ℝ) = 2 * C_card_uniform := by dsimp only [M_val] <;> ring
    rw [h2]; exact h1.le

  -- Common tube bound
  have h_common_bound : ∀ p ∈ P_thin, ∀ q ∈ P_thin, p ≠ q →
      ((Tp p) ∩ (Tp q)).card ≤ C_common * C_T * M_val * (Δ / dist p q)^s := by
    intro p hp q hq hne
    rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨R, hR, rfl⟩
    have hQR : Q ≠ R := by intro h; apply hne; rw [h]
    rw [hTp_at_center Q hQ, hTp_at_center R hR]
    let C_Q := (sd Q (hQ0_sub hQ)).C_Q
    let C_R := (sd R (hQ0_sub hR)).C_Q
    have hC_Q_sset : IsDeltaSSet Δ s C_T (C_Q : Set CoarseTube) := by
      have h1 : IsDeltaSSet Δ s (sd Q (hQ0_sub hQ)).C2_Q (C_Q : Set CoarseTube) :=
        (sd Q (hQ0_sub hQ)).hC_Q_sset
      have h2 : (sd Q (hQ0_sub hQ)).C2_Q ≤ C_T := (sd Q (hQ0_sub hQ)).hC2_Q_loss
      refine' ⟨h1.1, h1.2.1, hCT_pos, h1.2.2.2.1, _⟩
      intro x r hr
      have h3 := h1.2.2.2.2 x r hr
      have h4 : ENNReal.ofReal (sd Q (hQ0_sub hQ)).C2_Q ≤ ENNReal.ofReal C_T :=
        ENNReal.ofReal_le_ofReal h2
      have h_goal1 : Metric.externalCoveringNumber Δ.toNNReal (C_Q ∩ Metric.closedBall x r) ≤
          ENNReal.ofReal (sd Q (hQ0_sub hQ)).C2_Q * (ENNReal.ofReal r) ^ s *
            Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set CoarseTube) :=
        h1.2.2.2.2 x r hr
      have h51 : ENNReal.ofReal (sd Q (hQ0_sub hQ)).C2_Q * (ENNReal.ofReal r) ^ s ≤
          ENNReal.ofReal C_T * (ENNReal.ofReal r) ^ s :=
        mul_le_mul_right' h4 ((ENNReal.ofReal r) ^ s)
      have h5 : ENNReal.ofReal (sd Q (hQ0_sub hQ)).C2_Q * (ENNReal.ofReal r) ^ s *
          Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set CoarseTube) ≤
          ENNReal.ofReal C_T * (ENNReal.ofReal r) ^ s *
            Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set CoarseTube) :=
        mul_le_mul_right' h51 (Metric.externalCoveringNumber Δ.toNNReal (C_Q : Set CoarseTube))
      exact le_trans h_goal1 h5
    have hC_Q_sep : SeparatedAt Δ (C_Q : Set CoarseTube) :=
      (sd Q (hQ0_sub hQ)).hC_Q_separated
    have hC_Q_card : (C_Q.card : ℝ) ≤ M_val := by
      have h1 : ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) < 2 * C_card_uniform := (hC_direct Q hQ).2
      have h2 : (M_val : ℝ) = 2 * C_card_uniform := by dsimp only [M_val] <;> ring
      rw [h2]; exact h1.le
    have hC_Q_near : ∀ ℓ ∈ C_Q, squareCenter Δ Q ∈ Metric.cthickening (53 * Δ) (ℓ.1 : Set Plane) :=
      coarse_tube_near_square_center (sd Q (hQ0_sub hQ)) hΔ_pos hδ_pos hδ_le_Δ (by linarith)
    have hC_R_near : ∀ ℓ ∈ C_R, squareCenter Δ R ∈ Metric.cthickening (53 * Δ) (ℓ.1 : Set Plane) :=
      coarse_tube_near_square_center (sd R (hQ0_sub hR)) hΔ_pos hδ_pos hδ_le_Δ (by linarith)
    have hd_pos : 0 < dist (squareCenter Δ Q) (squareCenter Δ R) := by
      have h : Δ ≤ dist (squareCenter Δ Q) (squareCenter Δ R) := square_center_dist_ge hΔ_pos hQR
      linarith
    have h_bound := arbitrary_point_common_tubes_bound (k := (53 : ℝ)) (hk := by norm_num)
      hΔ_pos hs_pos hCT_pos hM_val_pos
      (hC_Q_sset := hC_Q_sset) (hC_Q_sep := hC_Q_sep) (hC_Q_card := hC_Q_card)
      (hC_Q_near_center := hC_Q_near) (hC_R_near_center := hC_R_near)
      (hp_in_square := square_center_in_square hΔ_pos Q)
      (hq_in_square := square_center_in_square hΔ_pos R)
      (hp_bound := hCenter_bound Q hQ) (hq_bound := hCenter_bound R hR)
      (h_dist_pos := hd_pos) (h_dist_le_3 := hDist_le_3 Q hQ R hR)
    have h_rhs : (MainAppendix.affineLine_packing_constant : ℝ) * C_T * ((800 * (54 : ℝ)) : ℝ)^s * M_val *
          (Δ / dist (squareCenter Δ Q) (squareCenter Δ R))^s =
        C_common * C_T * M_val * (Δ / dist (squareCenter Δ Q) (squareCenter Δ R))^s := by
      dsimp only [C_common] <;> ring
    have h_k9 : (53 : ℝ) + 1 = (54 : ℝ) := by norm_num
    let I_hbound : Finset CoarseTube :=
      @Inter.inter (Finset CoarseTube)
        (@Finset.instInter CoarseTube (fun a b => Subtype.instDecidableEq a b)) C_Q C_R
    have h_inter_eq : (C_Q ∩ C_R) = I_hbound := by
      ext x
      simp [I_hbound, Finset.mem_inter]
      <;> tauto
    have h_main_bound : (C_Q ∩ C_R).card ≤
        (MainAppendix.affineLine_packing_constant : ℝ) * C_T * ((800 * (54 : ℝ)) : ℝ)^s * M_val *
          (Δ / dist (squareCenter Δ Q) (squareCenter Δ R))^s := by
      rw [h_inter_eq]
      have h1 : I_hbound.card ≤
          (MainAppendix.affineLine_packing_constant : ℝ) * C_T * ((800 * ((53 : ℝ) + 1)) : ℝ)^s * M_val *
            (Δ / dist (squareCenter Δ Q) (squareCenter Δ R))^s := h_bound
      rw [h_k9] at h1
      exact h1
    calc (C_Q ∩ C_R).card
      ≤ (MainAppendix.affineLine_packing_constant : ℝ) * C_T * ((800 * (54 : ℝ)) : ℝ)^s * M_val *
          (Δ / dist (squareCenter Δ Q) (squareCenter Δ R))^s := h_main_bound
    _ = C_common * C_T * M_val * (Δ / dist (squareCenter Δ Q) (squareCenter Δ R))^s := by
      dsimp only [C_common] <;> ring

  -- hC_global_card_upper is passed directly as a hypothesis

  let K : ℝ := C_common * C_P * C_T * K_energy * Δ^s * (P_thin.card : ℝ)

  have h_energy' : ∑ p ∈ P_thin, ∑ q ∈ P_thin.erase p, (dist p q)^(-s) ≤
      K_energy * C_P * (P_thin.card : ℝ)^2 := by
    have h_eq1 : ∑ p ∈ P_thin, ∑ q ∈ P_thin.erase p, (dist p q)^(-s) =
        ∑ p ∈ (Q0.image (squareCenter Δ)), ∑ q ∈ (Q0.image (squareCenter Δ)).erase p,
          Real.rpow (dist p q) (-s) := by rfl
    rw [h_eq1]
    have h : ∑ p ∈ (Q0.image (squareCenter Δ)), ∑ q ∈ (Q0.image (squareCenter Δ)).erase p, Real.rpow (dist p q) (-s) ≤
        Real.rpow Δ (-14 * ε) * ((Q0.image (squareCenter Δ)).card : ℝ)^2 := h_energy
    simpa [K_energy, C_P] using h

  have h_global : ((P_thin.biUnion Tp).card : ℝ) ≥
      (P_thin.card : ℝ) * M_val / (4 * (1 + K)) :=
    global_2s_bound_no_hP_large hΔ_pos (by linarith [hΔ_lt_half]) hs_pos hst
      hCP_pos hCT_pos hM_val_pos hCcommon_pos hKe_pos
      hPthin_nonempty hPthin_sep hTp_card_lower hTp_card_upper h_common_bound h_energy'

  have hUnion_sub : P_thin.biUnion Tp ⊆ C_global := by
    intro ℓ hℓ
    rcases Finset.mem_biUnion.mp hℓ with ⟨p, hp, hℓp⟩
    rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
    have hTp : Tp (squareCenter Δ Q) = (sd Q (hQ0_sub hQ)).C_Q := hTp_at_center Q hQ
    rw [hTp] at hℓp
    exact hC_Q_sub_global Q hQ hℓp

  have hUnion_card_le : (P_thin.biUnion Tp).card ≤ C_global.card :=
    Finset.card_le_card hUnion_sub

  have hPcard_pos : 0 < (P_thin.card : ℝ) := by
    have h : 0 < P_thin.card := Finset.card_pos.mpr hPthin_nonempty
    exact_mod_cast h

  intro Q hQ
  have hC_Q_le_M : ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) ≤ M_val := by
    have hTp_eq : Tp (squareCenter Δ Q) = (sd Q (hQ0_sub hQ)).C_Q := hTp_at_center Q hQ
    have h : ((Tp (squareCenter Δ Q)).card : ℝ) ≤ M_val :=
      hTp_card_upper (squareCenter Δ Q) (Finset.mem_image.mpr ⟨Q, hQ, rfl⟩)
    rw [hTp_eq] at h
    exact h

  by_cases hK : K ≥ 1
  · -- K ≥ 1 branch
    have h1 : 1 + K ≤ 2 * K := by linarith
    have hK_pos' : 0 < K := by linarith
    have h3 : (P_thin.card : ℝ) * M_val / (8 * K) ≤ (C_global.card : ℝ) := by
      have h_pos1 : 0 ≤ (P_thin.card : ℝ) * M_val := by positivity
      have h_pos2 : 0 < 4 * (1 + K) := by positivity
      have h_pos3 : 0 < 8 * K := by positivity
      have h4 : 4 * (1 + K) ≤ 8 * K := by linarith
      have h_div : (P_thin.card : ℝ) * M_val / (8 * K) ≤ (P_thin.card : ℝ) * M_val / (4 * (1 + K)) := by
        gcongr
      calc (P_thin.card : ℝ) * M_val / (8 * K)
        ≤ (P_thin.card : ℝ) * M_val / (4 * (1 + K)) := h_div
      _ ≤ ((P_thin.biUnion Tp).card : ℝ) := h_global
      _ ≤ (C_global.card : ℝ) := by exact_mod_cast hUnion_card_le
    have h4 : M_val ≤ 8 * (K * (C_global.card : ℝ) / (P_thin.card : ℝ)) := by
      field_simp [hPcard_pos.ne', hK_pos'.ne'] at h3 ⊢ <;> linarith
    have h5 : K * (C_global.card : ℝ) / (P_thin.card : ℝ) =
        C_common * C_P * C_T * K_energy * Δ^s * (C_global.card : ℝ) := by
      dsimp only [K]
      field_simp [hPcard_pos.ne'] <;> ring
    rw [h5] at h4
    have h6 : M_val ≤ 8 * C_common * C_P * C_T * K_energy * Δ^s * (C_global.card : ℝ) := by
      simpa [mul_assoc] using h4
    have h7 : M_val ≤ (8 * (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s) * K_card *
        Real.rpow Δ (-s - 27 * ε) := by
      calc M_val
        ≤ 8 * C_common * C_P * C_T * K_energy * Δ^s * (C_global.card : ℝ) := h6
      _ ≤ 8 * C_common * C_P * C_T * K_energy * Δ^s * (K_card * Real.rpow Δ (-2 * s - 3 * ε)) := by
          gcongr <;> exact hC_global_card_upper
      _ = (8 * (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s) * K_card *
            Real.rpow Δ (-s - 27 * ε) := by
          dsimp only [C_common, C_P, C_T, K_energy]
          have h_rpow_sum : Real.rpow Δ (-14 * ε) * Real.rpow Δ (-10 * ε) * Real.rpow Δ s *
              Real.rpow Δ (-2 * s - 3 * ε) = Real.rpow Δ (-s - 27 * ε) := by
            set a := (-14 * ε) with ha
            set b := (-10 * ε) with hb
            set c := s with hc
            set d := (-2 * s - 3 * ε) with hd
            have h_sum : a + b + c + d = -s - 27 * ε := by
              simp [ha, hb, hc, hd] <;> ring
            have h1 : Real.rpow Δ a * Real.rpow Δ b = Real.rpow Δ (a + b) :=
              (Real.rpow_add hΔ_pos a b).symm
            have h2 : Real.rpow Δ (a + b) * Real.rpow Δ c = Real.rpow Δ (a + b + c) :=
              (Real.rpow_add hΔ_pos (a + b) c).symm
            have h3 : Real.rpow Δ (a + b + c) * Real.rpow Δ d = Real.rpow Δ (a + b + c + d) :=
              (Real.rpow_add hΔ_pos (a + b + c) d).symm
            calc Real.rpow Δ a * Real.rpow Δ b * Real.rpow Δ c * Real.rpow Δ d
              = (Real.rpow Δ a * Real.rpow Δ b) * Real.rpow Δ c * Real.rpow Δ d := by ring
            _ = Real.rpow Δ (a + b) * Real.rpow Δ c * Real.rpow Δ d := by rw [h1]
            _ = Real.rpow Δ (a + b + c) * Real.rpow Δ d := by rw [h2]
            _ = Real.rpow Δ (a + b + c + d) := by rw [h3]
            _ = Real.rpow Δ (-s - 27 * ε) := by rw [h_sum]
          have h_pow_conv : (Δ ^ s) = Real.rpow Δ s := by rfl
          have h_goal : 8 * ((MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s) *
              Real.rpow Δ (-14 * ε) * Real.rpow Δ (-10 * ε) * (1 : ℝ) * (Δ ^ s) *
              (K_card * Real.rpow Δ (-2 * s - 3 * ε)) =
              (8 * (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s) * K_card *
                Real.rpow Δ (-s - 27 * ε) := by
            calc 8 * ((MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s) *
                Real.rpow Δ (-14 * ε) * Real.rpow Δ (-10 * ε) * (1 : ℝ) * (Δ ^ s) *
                (K_card * Real.rpow Δ (-2 * s - 3 * ε))
              = (8 * (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s) * K_card *
                  (Real.rpow Δ (-14 * ε) * Real.rpow Δ (-10 * ε) * (Δ ^ s) * Real.rpow Δ (-2 * s - 3 * ε)) := by ring
            _ = (8 * (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s) * K_card *
                  (Real.rpow Δ (-14 * ε) * Real.rpow Δ (-10 * ε) * Real.rpow Δ s * Real.rpow Δ (-2 * s - 3 * ε)) := by
                rw [h_pow_conv] <;> ring
            _ = (8 * (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s) * K_card *
                  Real.rpow Δ (-s - 27 * ε) := by rw [h_rpow_sum] <;> ring
          exact h_goal
    exact le_trans hC_Q_le_M (le_trans h7 h_card_absorb_genuine)
  · -- K < 1 branch
    have h1 : 1 + K < 2 := by linarith
    have h_num_nonneg : 0 ≤ (P_thin.card : ℝ) * M_val := by positivity
    have h_den1_pos : 0 < 4 * (1 + K) := by positivity
    have h_den2_pos : 0 < (8 : ℝ) := by norm_num
    have h_den_le : 4 * (1 + K) ≤ 8 := by linarith
    have h_div_le : (P_thin.card : ℝ) * M_val / 8 ≤
        (P_thin.card : ℝ) * M_val / (4 * (1 + K)) :=
      div_le_div_of_nonneg_left h_num_nonneg h_den1_pos h_den_le
    have h3 : (P_thin.card : ℝ) * M_val / 8 ≤ (C_global.card : ℝ) := by
      calc (P_thin.card : ℝ) * M_val / 8
        ≤ (P_thin.card : ℝ) * M_val / (4 * (1 + K)) := h_div_le
      _ ≤ ((P_thin.biUnion Tp).card : ℝ) := h_global
      _ ≤ (C_global.card : ℝ) := by exact_mod_cast hUnion_card_le
    have h4 : M_val ≤ 8 * (C_global.card : ℝ) / (P_thin.card : ℝ) := by
      field_simp [hPcard_pos.ne'] at h3 ⊢ <;> linarith
    have hP_lower : (P_thin.card : ℝ) ≥ (Qset_all.card : ℝ) / Real.rpow Δ (-ε) := by
      rw [hPthin_card]; exact hQ0_card_lower
    have hQset_pos : 0 < (Qset_all.card : ℝ) := by
      have h : 0 < Q0.card := Finset.card_pos.mpr hQ0_nonempty
      have h' : Q0 ⊆ Qset_all := hQ0_sub
      have h'' : 0 < Qset_all.card := Finset.card_pos.mpr (hQ0_nonempty.mono h')
      exact_mod_cast h''
    have h5 : M_val ≤ (8 : ℝ) * K_card * Real.rpow Δ (t - 2 * s - 7 * ε) := by
      calc M_val
        ≤ 8 * (C_global.card : ℝ) / (P_thin.card : ℝ) := h4
      _ ≤ 8 * (K_card * Real.rpow Δ (-2 * s - 3 * ε)) / (P_thin.card : ℝ) := by
          have h_ineq : 8 * (C_global.card : ℝ) ≤ 8 * (K_card * Real.rpow Δ (-2 * s - 3 * ε)) :=
            mul_le_mul_of_nonneg_left hC_global_card_upper (by norm_num)
          exact div_le_div_of_nonneg_right h_ineq hPcard_pos.le
      _ ≤ 8 * (K_card * Real.rpow Δ (-2 * s - 3 * ε)) / ((Qset_all.card : ℝ) / Real.rpow Δ (-ε)) := by
          have h8A_pos : 0 < 8 * (K_card * Real.rpow Δ (-2 * s - 3 * ε)) :=
            mul_pos (by norm_num) (mul_pos hK_card_pos (Real.rpow_pos_of_pos hΔ_pos _))
          have h_rpow_pos : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos _
          have h_den2_pos : 0 < (Qset_all.card : ℝ) / Real.rpow Δ (-ε) := div_pos hQset_pos h_rpow_pos
          exact div_le_div_of_nonneg_left h8A_pos.le h_den2_pos hP_lower
      _ ≤ (8 : ℝ) * K_card * Real.rpow Δ (t - 2 * s - 7 * ε) := by
          have h_rpow_pos : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos _
          have h_den_lower : (Qset_all.card : ℝ) / Real.rpow Δ (-ε) ≥
              Real.rpow Δ (-t + 3 * ε) / Real.rpow Δ (-ε) := by
            apply div_le_div_of_nonneg_right hQset_card_lower h_rpow_pos.le
          have h8A_pos : 0 < 8 * (K_card * Real.rpow Δ (-2 * s - 3 * ε)) :=
            mul_pos (by norm_num) (mul_pos hK_card_pos (Real.rpow_pos_of_pos hΔ_pos _))
          have h_pos_b : 0 < Real.rpow Δ (-t + 3 * ε) := Real.rpow_pos_of_pos hΔ_pos _
          have h_den_pos : 0 < Real.rpow Δ (-t + 3 * ε) / Real.rpow Δ (-ε) :=
            div_pos h_pos_b h_rpow_pos
          have h_main : 8 * (K_card * Real.rpow Δ (-2 * s - 3 * ε)) / ((Qset_all.card : ℝ) / Real.rpow Δ (-ε)) ≤
              8 * (K_card * Real.rpow Δ (-2 * s - 3 * ε)) / (Real.rpow Δ (-t + 3 * ε) / Real.rpow Δ (-ε)) :=
            div_le_div_of_nonneg_left h8A_pos.le h_den_pos h_den_lower
          have h_rpow1 : Real.rpow Δ (-2 * s - 3 * ε) * Real.rpow Δ (-ε) = Real.rpow Δ (-2 * s - 4 * ε) := by
            have h := Real.rpow_add hΔ_pos (-2 * s - 3 * ε) (-ε)
            have h_exp : (-2 * s - 3 * ε) + (-ε) = -2 * s - 4 * ε := by ring
            rw [h_exp] at h
            exact h.symm
          have h_mul : Real.rpow Δ ((t - 2 * s - 7 * ε) + (-t + 3 * ε)) =
              Real.rpow Δ (t - 2 * s - 7 * ε) * Real.rpow Δ (-t + 3 * ε) :=
            Real.rpow_add hΔ_pos (t - 2 * s - 7 * ε) (-t + 3 * ε)
          have h_sum : (t - 2 * s - 7 * ε) + (-t + 3 * ε) = -2 * s - 4 * ε := by ring
          rw [h_sum] at h_mul
          have h_rpow2 : Real.rpow Δ (-2 * s - 4 * ε) / Real.rpow Δ (-t + 3 * ε) = Real.rpow Δ (t - 2 * s - 7 * ε) := by
            have h : Real.rpow Δ ((-2 * s - 4 * ε) - (-t + 3 * ε)) = Real.rpow Δ (-2 * s - 4 * ε) / Real.rpow Δ (-t + 3 * ε) :=
              Real.rpow_sub hΔ_pos (-2 * s - 4 * ε) (-t + 3 * ε)
            have h_exp : (-2 * s - 4 * ε) - (-t + 3 * ε) = t - 2 * s - 7 * ε := by ring
            rw [h_exp] at h
            exact h.symm
          have h_div : (K_card * Real.rpow Δ (-2 * s - 3 * ε)) / (Real.rpow Δ (-t + 3 * ε) / Real.rpow Δ (-ε)) =
              K_card * Real.rpow Δ (-2 * s - 3 * ε) * Real.rpow Δ (-ε) / Real.rpow Δ (-t + 3 * ε) := by
            field_simp [h_pos_b.ne', h_rpow_pos.ne'] <;> ring
          have h_step1 : 8 * (K_card * Real.rpow Δ (-2 * s - 3 * ε)) / (Real.rpow Δ (-t + 3 * ε) / Real.rpow Δ (-ε)) =
              8 * (K_card * Real.rpow Δ (-2 * s - 3 * ε) * Real.rpow Δ (-ε) / Real.rpow Δ (-t + 3 * ε)) := by
            have h_pos1 : 0 < Real.rpow Δ (-t + 3 * ε) := Real.rpow_pos_of_pos hΔ_pos _
            have h_pos2 : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos _
            field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
          have h_final : 8 * (K_card * Real.rpow Δ (-2 * s - 3 * ε)) / (Real.rpow Δ (-t + 3 * ε) / Real.rpow Δ (-ε)) =
              (8 : ℝ) * K_card * Real.rpow Δ (t - 2 * s - 7 * ε) := by
            calc 8 * (K_card * Real.rpow Δ (-2 * s - 3 * ε)) / (Real.rpow Δ (-t + 3 * ε) / Real.rpow Δ (-ε))
              = 8 * (K_card * Real.rpow Δ (-2 * s - 3 * ε) * Real.rpow Δ (-ε) / Real.rpow Δ (-t + 3 * ε)) := h_step1
            _ = 8 * (K_card * Real.rpow Δ (-2 * s - 4 * ε) / Real.rpow Δ (-t + 3 * ε)) := by
              have h_mul : K_card * Real.rpow Δ (-2 * s - 3 * ε) * Real.rpow Δ (-ε) =
                  K_card * Real.rpow Δ (-2 * s - 4 * ε) := by
                have h_assoc : K_card * Real.rpow Δ (-2 * s - 3 * ε) * Real.rpow Δ (-ε) =
                    K_card * (Real.rpow Δ (-2 * s - 3 * ε) * Real.rpow Δ (-ε)) := by ring
                rw [h_assoc, h_rpow1] <;> ring
              rw [h_mul]
            _ = 8 * K_card * Real.rpow Δ (t - 2 * s - 7 * ε) := by
              have h_eq : 8 * (K_card * Real.rpow Δ (-2 * s - 4 * ε) / Real.rpow Δ (-t + 3 * ε)) =
                  8 * K_card * (Real.rpow Δ (-2 * s - 4 * ε) / Real.rpow Δ (-t + 3 * ε)) := by ring
              rw [h_eq, h_rpow2] <;> ring
          exact le_trans h_main h_final.le
    exact le_trans hC_Q_le_M (le_trans h5 h_card_absorb_smallK)

end DirecretisedFurstenbergEstimate.AppendixA3
