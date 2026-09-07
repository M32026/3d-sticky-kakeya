module

/-
  Helper to derive `h_2s_bound` for `FrontEndComposition`.

  Wraps `TwoSBoundWeak.h_2s_bound_integration`, deriving Qset nonempty,
  C_Q_pi card upper, and near-center from `A4_Output_v2` fields.
  Numerical bounds are passed explicitly.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TwoSBoundWeak
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.NearCenterTight
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AssemblyNumericalHypotheses
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA5

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.AppendixA4
open DirecretisedFurstenbergEstimate.AssemblyNumerical
open DirecretisedFurstenbergEstimate.Lagoon

/-- Derive `TwoSBoundWithLower` from `A4_Output_v2` + explicit numerical bounds. -/
lemma h_2s_bound_from_a4
    {Δ δ s u ε : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < u) (ht2 : u < 2)
    (hε_pos : 0 < ε)
    {T_source : Finset CoarseTube}
    (a4 : A4_Output_v2 Δ δ s u ε T_source)
    (C_global_A2 : Finset CoarseTube)
    (hC_Q_pi_sub : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset),
        (a4.perSquare Q hQ).C_Q_pi ⊆ C_global_A2)
    (hCenter_bound : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset),
        ‖squareCenter Δ Q‖ ≤ 2)
    (hDist_le_3 : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset)
        (R : CoarseSquare Δ) (hR : R ∈ a4.Qset),
        dist (squareCenter Δ Q) (squareCenter Δ R) ≤ 3)
    (hQset_card_upper : (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-u - ε))
    (hRKP : 576 * ε < u - s)
    (hK_large_weak : (MainAppendix.affineLine_packing_constant : ℝ) *
        ((800 * (11 : ℝ)) : ℝ)^s *
        (MainAppendix.plane_packing_constant : ℝ) * (4 : ℝ)^u *
        ((MainAppendix.plane_packing_constant : ℝ) * Real.rpow Δ (-20 * ε)) *
        Real.rpow Δ (s - u - 112 * ε) ≥ 2)
    (h_absorb_K_extra : (8 : ℝ) *
        (MainAppendix.affineLine_packing_constant : ℝ) *
        ((800 * (11 : ℝ)) : ℝ)^s *
        (MainAppendix.plane_packing_constant : ℝ) *
        MainAppendix.plane_energy_constant s u 2 *
        ((MainAppendix.plane_packing_constant : ℝ) * Real.rpow Δ (6 * ε)) ≤
        Real.rpow Δ (-ε)) :
    TwoSBoundWithLower Δ s u ε a4.Qset
      (fun Q hQ => (a4.perSquare Q hQ).C_Q_pi) C_global_A2
      (-2 * s + 210 * ε) := by
  have hQset_nonempty : a4.Qset.Nonempty := a4.hQset_sset.1

  have hC_Q_pi_card_upper : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset),
      ((a4.perSquare Q hQ).C_Q_pi.card : ℝ) ≤ Real.rpow Δ (-s - 29 * ε) := by
    intro Q hQ
    have h1 : (a4.perSquare Q hQ).C_Q_pi ⊆ (a4.perSquare Q hQ).base.C_Q :=
      (a4.perSquare Q hQ).hC_Q_pi_sub
    have h2 : ((a4.perSquare Q hQ).C_Q_pi.card : ℝ) ≤ ((a4.perSquare Q hQ).base.C_Q.card : ℝ) := by
      simpa using Finset.card_le_card h1
    have h3 : ((a4.perSquare Q hQ).base.C_Q.card : ℝ) ≤ Real.rpow Δ (-s - 29 * ε) :=
      (a4.perSquare Q hQ).hC_card_upper
    exact le_trans h2 h3

  have hC_near : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset)
      (T : CoarseTube), T ∈ (a4.perSquare Q hQ).C_Q_pi →
      squareCenter Δ Q ∈ Metric.cthickening (10 * Δ) (T.1 : Set EuclideanPlane) := by
    intro Q hQ T hT
    have h4 : T ∈ (a4.perSquare Q hQ).base.C_Q := (a4.perSquare Q hQ).hC_Q_pi_sub hT
    exact coarse_tube_near_square_center_tight
      (a4.perSquare Q hQ).base hΔ_pos hδ_pos hδ_le_Δ hΔ_lt_half.le T h4

  exact h_2s_bound_integration
    hΔ_pos hΔ_lt_half hδ_pos hδ_le_Δ
    hs hs1 hst ht2 hε_pos
    a4 C_global_A2 hC_Q_pi_sub hCenter_bound hDist_le_3 hQset_card_upper
    hQset_nonempty hC_Q_pi_card_upper hC_near
    hRKP hK_large_weak h_absorb_K_extra

/-- Derive `TwoSBoundWithLower` from `A4_Output_v2` + `AssemblyNumericalBounds`.

    Bridges the numerical bound forms:
    - `hK_large_weak`: rewrites `C_plane * Δ^(s-u-132ε)` as `(C_plane * Δ^(-20ε)) * Δ^(s-u-112ε)`
    - `h_absorb_K_extra`: uses `plane_energy_constant s u 2 = C_plane * (4^u + ...)` and `4^u ≤ 16`
      to show the helper's LHS is bounded by the Assembly bound's LHS. -/
lemma h_2s_bound_from_a4_num
    {Δ δ s u ε : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < u) (ht2 : u < 2)
    (hε_pos : 0 < ε)
    {T_source : Finset CoarseTube}
    (a4 : A4_Output_v2 Δ δ s u ε T_source)
    (C_global_A2 : Finset CoarseTube)
    (hC_Q_pi_sub : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset),
        (a4.perSquare Q hQ).C_Q_pi ⊆ C_global_A2)
    (hCenter_bound : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset),
        ‖squareCenter Δ Q‖ ≤ 2)
    (hDist_le_3 : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset)
        (R : CoarseSquare Δ) (hR : R ∈ a4.Qset),
        dist (squareCenter Δ Q) (squareCenter Δ R) ≤ 3)
    (hQset_card_upper : (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-u - ε))
    (hRKP : 576 * ε < u - s)
    (h_num : AssemblyNumericalBounds Δ s u ε) :
    TwoSBoundWithLower Δ s u ε a4.Qset
      (fun Q hQ => (a4.perSquare Q hQ).C_Q_pi) C_global_A2
      (-2 * s + 210 * ε) := by
  set C_affine := (MainAppendix.affineLine_packing_constant : ℝ)
  set C_plane := (MainAppendix.plane_packing_constant : ℝ)
  set K_energy := MainAppendix.plane_energy_constant s u 2

  -- Bridge hK_large_weak
  have h_rpow_eq : Real.rpow Δ (-20 * ε) * Real.rpow Δ (s - u - 112 * ε) =
      Real.rpow Δ (s - u - 132 * ε) := by
    have h2 : (-20 * ε) + (s - u - 112 * ε) = s - u - 132 * ε := by ring
    have h3 : Real.rpow Δ ((-20 * ε) + (s - u - 112 * ε)) =
        Real.rpow Δ (-20 * ε) * Real.rpow Δ (s - u - 112 * ε) :=
      Real.rpow_add hΔ_pos (-20 * ε) (s - u - 112 * ε)
    rw [h2] at h3
    exact h3.symm
  have hK1 : C_plane * Real.rpow Δ (s - u - 132 * ε) =
      (C_plane * Real.rpow Δ (-20 * ε)) * Real.rpow Δ (s - u - 112 * ε) := by
    calc
      C_plane * Real.rpow Δ (s - u - 132 * ε)
        = C_plane * (Real.rpow Δ (-20 * ε) * Real.rpow Δ (s - u - 112 * ε)) := by rw [h_rpow_eq]
      _ = (C_plane * Real.rpow Δ (-20 * ε)) * Real.rpow Δ (s - u - 112 * ε) := by ring
  have hK_large_weak' : C_affine * ((800 * (11 : ℝ)) : ℝ)^s * C_plane * (4 : ℝ)^u *
      (C_plane * Real.rpow Δ (-20 * ε)) * Real.rpow Δ (s - u - 112 * ε) ≥ 2 := by
    have h := h_num.hK_large_weak
    have h_eq : C_affine * ((800 * (11 : ℝ)) : ℝ)^s * C_plane * (4 : ℝ)^u *
        (C_plane * Real.rpow Δ (-20 * ε)) * Real.rpow Δ (s - u - 112 * ε) =
        C_affine * ((800 * (11 : ℝ)) : ℝ)^s * C_plane * (4 : ℝ)^u * C_plane *
        Real.rpow Δ (s - u - 132 * ε) := by
      have h1 : C_affine * ((800 * (11 : ℝ)) : ℝ)^s * C_plane * (4 : ℝ)^u *
          (C_plane * Real.rpow Δ (-20 * ε)) * Real.rpow Δ (s - u - 112 * ε) =
          C_affine * ((800 * (11 : ℝ)) : ℝ)^s * C_plane * (4 : ℝ)^u *
          ((C_plane * Real.rpow Δ (-20 * ε)) * Real.rpow Δ (s - u - 112 * ε)) := by ring
      rw [h1]
      have h2 : (C_plane * Real.rpow Δ (-20 * ε)) * Real.rpow Δ (s - u - 112 * ε) =
          C_plane * Real.rpow Δ (s - u - 132 * ε) := hK1.symm
      rw [h2] <;> ring
    rw [h_eq]
    exact h

  -- Bridge h_absorb_K_extra
  have hdenom_pos : 0 < (1 : ℝ) - (2 : ℝ)^(s - u) := by
    have h5 : s - u < 0 := by linarith
    have h7 : (1 : ℝ) < (2 : ℝ) := by norm_num
    have h6 : (2 : ℝ)^(s - u) < (2 : ℝ)^(0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt h7 h5
    have h6' : (2 : ℝ)^(s - u) < 1 := by simpa using h6
    linarith
  have hK_energy_eq : K_energy = C_plane * ((4 : ℝ)^u + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u))) := by
    have h12 : (2 * (2 : ℝ))^u = (4 : ℝ)^u := by
      have h13 : (2 * (2 : ℝ)) = (4 : ℝ) := by norm_num
      rw [h13]
    have h : MainAppendix.plane_energy_constant s u 2 =
        C_plane * ((2 * (2 : ℝ))^u + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u))) := by rfl
    have h9 : C_plane * ((2 * (2 : ℝ))^u + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u))) =
        C_plane * ((4 : ℝ)^u + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u))) := by
      rw [h12]
    have h10 : MainAppendix.plane_energy_constant s u 2 =
        C_plane * ((4 : ℝ)^u + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u))) := by
      calc MainAppendix.plane_energy_constant s u 2
        = C_plane * ((2 * (2 : ℝ))^u + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u))) := h
      _ = C_plane * ((4 : ℝ)^u + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u))) := h9
    have hK_def : K_energy = MainAppendix.plane_energy_constant s u 2 := by rfl
    exact Eq.trans hK_def h10
  have h4u : (4 : ℝ)^u ≤ 16 := by
    have h : (4 : ℝ)^u ≤ (4 : ℝ)^(2 : ℝ) := by
      gcongr <;> norm_num <;> linarith
    have h' : (4 : ℝ)^(2 : ℝ) = 16 := by norm_num
    rw [h'] at h; exact h
  have h_energy_le : K_energy ≤ C_plane * (16 + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u))) := by
    rw [hK_energy_eq]
    have hC_pos : 0 ≤ C_plane := by positivity
    have h_sum : (4 : ℝ)^u + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u)) ≤
        16 + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u)) := by linarith
    exact mul_le_mul_of_nonneg_left h_sum hC_pos
  have h_absorb_K_extra' : (8 : ℝ) * C_affine * ((800 * (11 : ℝ)) : ℝ)^s * C_plane *
      K_energy * (C_plane * Real.rpow Δ (6 * ε)) ≤ Real.rpow Δ (-ε) := by
    have h_pos1 : 0 ≤ (8 : ℝ) * C_affine * ((800 * (11 : ℝ)) : ℝ)^s * C_plane := by positivity
    have h_pos2 : 0 ≤ Real.rpow Δ (6 * ε) := Real.rpow_nonneg hΔ_pos.le _
    have h_le : (8 : ℝ) * C_affine * ((800 * (11 : ℝ)) : ℝ)^s * C_plane * K_energy *
        (C_plane * Real.rpow Δ (6 * ε)) ≤
        (8 : ℝ) * C_affine * ((800 * (11 : ℝ)) : ℝ)^s * C_plane^3 *
        (16 + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u))) * Real.rpow Δ (6 * ε) := by
      calc
        (8 : ℝ) * C_affine * ((800 * (11 : ℝ)) : ℝ)^s * C_plane * K_energy *
            (C_plane * Real.rpow Δ (6 * ε))
          = (8 : ℝ) * C_affine * ((800 * (11 : ℝ)) : ℝ)^s * C_plane^2 * K_energy *
              Real.rpow Δ (6 * ε) := by ring
        _ ≤ (8 : ℝ) * C_affine * ((800 * (11 : ℝ)) : ℝ)^s * C_plane^2 *
              (C_plane * (16 + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u)))) *
              Real.rpow Δ (6 * ε) := by
          gcongr <;> linarith [h_energy_le]
        _ = (8 : ℝ) * C_affine * ((800 * (11 : ℝ)) : ℝ)^s * C_plane^3 *
              (16 + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u))) *
              Real.rpow Δ (6 * ε) := by ring
    exact le_trans h_le h_num.h_absorb_K_extra

  exact h_2s_bound_from_a4
    hΔ_pos hΔ_lt_half hδ_pos hδ_le_Δ
    hs hs1 hst ht2 hε_pos
    a4 C_global_A2 hC_Q_pi_sub hCenter_bound hDist_le_3 hQset_card_upper
    hRKP hK_large_weak' h_absorb_K_extra'

end DirecretisedFurstenbergEstimate.AppendixA5
