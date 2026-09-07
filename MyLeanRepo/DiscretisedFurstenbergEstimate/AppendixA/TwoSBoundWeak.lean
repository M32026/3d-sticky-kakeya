module

/-
  Weak variant of mkTwoSBound_direct that accepts a parameterized Qset
  S-set constant instead of hardcoded Δ^{-12ε}.

  When C_Qimg ≤ K_extra · Δ^{-26ε}, the final bound reaches exponent -2s+210ε.

  Used to prove h_2s_bound in FrontEndComposition from A4 physical growth data,
  which yields a Qset center S-set with constant plane_packing_constant · Δ^{-20ε}.

  Whiteprint node: two_s_bound_corrected
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A5_LooseCore
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A3_GeometricLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A3_CoarseSquareEnergyBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.CommonCoarseTubesBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Global2sBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.EnergyBoundPlane
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HCommonWiring
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A4_CQpiSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.EnergyBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

set_option maxHeartbeats 500000

namespace DirecretisedFurstenbergEstimate.AppendixA5

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.AppendixA4
open DirecretisedFurstenbergEstimate.Lagoon (squareCenter squareCenter_zero squareCenter_one)
open DirecretisedFurstenbergEstimate.Global2sBound

/-- Helper: multiply two real powers of Δ with simplified exponent. -/
lemma h_rpow_eq {Δ : ℝ} (hΔ_pos : 0 < Δ) (x y z : ℝ) (h : x + y = z) :
    Real.rpow Δ x * Real.rpow Δ y = Real.rpow Δ z := by
  have h1 := Real.rpow_add hΔ_pos x y
  rw [h] at h1
  exact h1.symm

/-- Helper: multiply two real powers of Δ. -/
lemma h_rpow_mul {Δ : ℝ} (hΔ_pos : 0 < Δ) (x y : ℝ) :
    Real.rpow Δ x * Real.rpow Δ y = Real.rpow Δ (x + y) :=
  (Real.rpow_add hΔ_pos x y).symm

lemma squareCenter_injective {Δ : ℝ} (hΔ_pos : 0 < Δ) :
    Function.Injective (squareCenter Δ) := by
  intro Q1 Q2 h
  have h1 := congr_arg (fun f : EuclideanPlane => f 0) h
  have h2 := congr_arg (fun f : EuclideanPlane => f 1) h
  have hQ1 : Q1.1 = Q2.1 := by simpa [squareCenter_zero, hΔ_pos.ne'] using h1
  have hQ2 : Q1.2 = Q2.2 := by simpa [squareCenter_one, hΔ_pos.ne'] using h2
  ext <;> tauto

/-- The center of a coarse square lies inside the square. -/
lemma square_center_in_square {Δ : ℝ} (hΔ_pos : 0 < Δ) (Q : CoarseSquare Δ) :
    squareCenter Δ Q ∈ squareSet Δ Q := by
  have hx : squareCenter Δ Q 0 = Δ * ((Q.1 : ℝ) + 1 / 2) := squareCenter_zero Δ Q
  have hy : squareCenter Δ Q 1 = Δ * ((Q.2 : ℝ) + 1 / 2) := squareCenter_one Δ Q
  constructor
  · rw [hx]; constructor <;> linarith
  · rw [hy]; constructor <;> linarith

/-- Weak variant of mkTwoSBound_direct with parameterized Qset S-set constant.

    When C_Qimg ≤ K_extra · Δ^{-26ε}, produces TwoSBoundWithLower at -2s+210ε.
    The hK_large_weak condition is easier than the original hK_large because
    the weaker S-set constant makes K larger. -/
theorem mkTwoSBound_weak
    {Δ δ s t ε : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2)
    (hε_pos : 0 < ε)
    (C_Qimg : ℝ)
    (hC_Qimg_pos : 0 < C_Qimg)
    (K_extra : ℝ)
    (hK_extra_pos : 0 < K_extra)
    (hC_Qimg_le : C_Qimg ≤ K_extra * Real.rpow Δ (-26 * ε))
    (Qset : Finset (CoarseSquare Δ))
    (C : (Q : CoarseSquare Δ) → Q ∈ Qset → Finset CoarseTube)
    (hC_sset : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qset),
        IsDeltaSSet Δ s (Real.rpow Δ (-59 * ε)) (C Q hQ : Set CoarseTube))
    (hC_card_upper : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qset),
        (C Q hQ).card ≤ Real.rpow Δ (-s - 29 * ε))
    (hC_sep : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qset),
        SeparatedAt Δ (C Q hQ : Set CoarseTube))
    (hC_near : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qset) (T : CoarseTube),
        T ∈ C Q hQ → squareCenter Δ Q ∈ Metric.cthickening (10 * Δ) (T.1 : Set EuclideanPlane))
    (T_Δ : Finset CoarseTube)
    (hC_sub_TΔ : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qset), (C Q hQ : Set CoarseTube) ⊆ (T_Δ : Set CoarseTube))
    (hCenter_bound : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qset), ‖squareCenter Δ Q‖ ≤ 2)
    (hDist_le_3 : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qset) (R : CoarseSquare Δ) (hR : R ∈ Qset),
        dist (squareCenter Δ Q) (squareCenter Δ R) ≤ 3)
    (hQset_sset : IsDeltaSSet Δ t C_Qimg (Qset.image (squareCenter Δ) : Set EuclideanPlane))
    (hQset_card_upper : (Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε))
    (hRKP : 576 * ε < t - s)
    (hK_large_weak : (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (11 : ℝ)) : ℝ)^s *
        (MainAppendix.plane_packing_constant : ℝ) * (4 : ℝ)^t *
        C_Qimg * Real.rpow Δ (s - t - 112 * ε) ≥ 2)
    (hR_pos : (0 : ℝ) < (2 : ℝ))
    (h_absorb_K_extra : (8 : ℝ) * (MainAppendix.affineLine_packing_constant : ℝ) *
        ((800 * (11 : ℝ)) : ℝ)^s * (MainAppendix.plane_packing_constant : ℝ) *
        MainAppendix.plane_energy_constant s t 2 * K_extra ≤ Real.rpow Δ (-ε))
    : TwoSBoundWithLower Δ s t ε Qset C T_Δ (-2 * s + 210 * ε) := by
  classical
  let C_T : ℝ := Real.rpow Δ (-59 * ε)
  have hCT_pos : 0 < C_T := Real.rpow_pos_of_pos hΔ_pos _
  let C_T' : ℝ := Real.rpow Δ (-111 * ε)
  have hCT'_pos : 0 < C_T' := Real.rpow_pos_of_pos hΔ_pos _
  let C_common : ℝ := (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (11 : ℝ)) : ℝ)^s
  have hCcommon_pos : 0 < C_common := by
    have h1 : 0 < (MainAppendix.affineLine_packing_constant : ℝ) := by
      exact_mod_cast MainAppendix.affineLine_packing_constant_pos
    have h2 : 0 < ((800 * (11 : ℝ)) : ℝ)^s := Real.rpow_pos_of_pos (by positivity) _
    exact mul_pos h1 h2
  let C_P : ℝ := C_Qimg
  have hCP_pos : 0 < C_P := hC_Qimg_pos

  -- Plane packing constant (Δ-independent) and transferred S-set constant for P
  let K_pack_plane : ℝ := (MainAppendix.plane_packing_constant : ℝ)
  have hK_pack_plane_pos : 0 < K_pack_plane := by
    dsimp only [K_pack_plane]
    exact Nat.cast_pos.mpr MainAppendix.plane_packing_constant_pos
  let C_P' : ℝ := K_pack_plane * Real.rpow Δ (-50 * ε) * C_Qimg
  have hCP'_pos : 0 < C_P' :=
    mul_pos (mul_pos hK_pack_plane_pos (Real.rpow_pos_of_pos hΔ_pos _)) hC_Qimg_pos

  -- Uniform energy constant (depends only on Δ, s, t, R=2)
  let K_energy_uniform : ℝ := MainAppendix.plane_energy_constant s t 2
  have hK_pack_pos : 0 < MainAppendix.plane_energy_K_pack Δ hΔ_pos := by
    have h_eq : MainAppendix.plane_energy_K_pack Δ hΔ_pos = MainAppendix.plane_packing_constant := by rfl
    rw [h_eq]
    exact MainAppendix.plane_packing_constant_pos
  have h_denom_pos : 0 < (1 : ℝ) - (2 : ℝ) ^ (s - t) := by
    have h1 : s - t < 0 := by linarith
    have h2 : (2 : ℝ) ^ (s - t) < 1 := by
      have h_pos : 0 < t - s := by linarith
      have h3 : (1 : ℝ) < (2 : ℝ) ^ (t - s) := by
        have h_pos : 0 < t - s := by linarith
        have h : (1 : ℝ) ^ (t - s) < (2 : ℝ) ^ (t - s) := by gcongr <;> norm_num
        simpa using h
      have h4 : (2 : ℝ) ^ (s - t) = 1 / ((2 : ℝ) ^ (t - s)) := by
        have h5 : s - t = -(t - s) := by ring
        rw [h5, Real.rpow_neg] <;> norm_num
      rw [h4]
      have h6 : 1 / ((2 : ℝ) ^ (t - s)) < 1 := by
        apply (div_lt_one (by positivity)).mpr
        linarith
      exact h6
    linarith
  have hK_energy_uniform_pos : 0 < K_energy_uniform := by
    dsimp only [K_energy_uniform, MainAppendix.plane_energy_constant]
    have h1 : 0 < (MainAppendix.plane_energy_K_pack Δ hΔ_pos : ℝ) := by exact_mod_cast hK_pack_pos
    have h2 : 0 < (2 * (2 : ℝ)) ^ t := Real.rpow_pos_of_pos (by norm_num) t
    have h3 : 0 < (2 : ℝ) ^ s / (1 - (2 : ℝ) ^ (s - t)) := by
      apply div_pos (Real.rpow_pos_of_pos (by norm_num) s) h_denom_pos
    have h4 : 0 < (2 * (2 : ℝ)) ^ t + (2 : ℝ) ^ s / (1 - (2 : ℝ) ^ (s - t)) := by
      exact add_pos h2 h3
    exact mul_pos h1 h4

  -- Effective K_energy: uniform (applied directly to P after S-set transfer)
  let K_energy_eff : ℝ := K_energy_uniform
  have hK_energy_eff_pos : 0 < K_energy_eff := hK_energy_uniform_pos

  -- Uniform constant c for the 2s-bound (includes K_extra factor)
  let c : ℝ := 1 / (4 * C_common * K_pack_plane * K_energy_uniform * K_extra)
  have hc_pos : 0 < c := by positivity

  -- Absorption conditions for c
  have h_absorb_c2 : (2 : ℝ) / c ≤ Real.rpow Δ (-ε) := by
    dsimp only [c]
    have h1 : (2 : ℝ) / (1 / (4 * C_common * K_pack_plane * K_energy_uniform * K_extra)) =
        8 * C_common * K_pack_plane * K_energy_uniform * K_extra := by
      field_simp [hCcommon_pos.ne', hK_pack_plane_pos.ne', hK_energy_uniform_pos.ne', hK_extra_pos.ne'] <;> ring
    rw [h1]
    have h2 : 8 * C_common * K_pack_plane * K_energy_uniform * K_extra = (8 : ℝ) *
        (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (11 : ℝ)) : ℝ)^s *
        (MainAppendix.plane_packing_constant : ℝ) *
        MainAppendix.plane_energy_constant s t 2 * K_extra := by
      dsimp only [C_common, K_pack_plane, K_energy_uniform] <;> ring
    rw [h2]
    exact h_absorb_K_extra
  have h_absorb_c1 : c ≥ Real.rpow Δ ε := by
    dsimp only [c]
    have h1 : 8 * C_common * K_pack_plane * K_energy_uniform * K_extra ≤ Real.rpow Δ (-ε) := by
      have h2 : 8 * C_common * K_pack_plane * K_energy_uniform * K_extra = (8 : ℝ) *
          (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (11 : ℝ)) : ℝ)^s *
          (MainAppendix.plane_packing_constant : ℝ) *
          MainAppendix.plane_energy_constant s t 2 * K_extra := by
        dsimp only [C_common, K_pack_plane, K_energy_uniform] <;> ring
      rw [h2]; exact h_absorb_K_extra
    have h_pos : 0 < 8 * C_common * K_pack_plane * K_energy_uniform * K_extra := by positivity
    have h_pos2 : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_eq : Real.rpow Δ ε * Real.rpow Δ (-ε) = 1 := by
      have h_add : Real.rpow Δ (ε + (-ε)) = Real.rpow Δ ε * Real.rpow Δ (-ε) := Real.rpow_add hΔ_pos ε (-ε)
      have h_zero : ε + (-ε) = 0 := by ring
      rw [h_zero] at h_add
      have h_rpow0 : Real.rpow Δ 0 = 1 := by simp
      rw [h_rpow0] at h_add
      exact h_add.symm
    have h_div : (1 : ℝ) / Real.rpow Δ (-ε) = Real.rpow Δ ε := by
      have h : Real.rpow Δ ε = (1 : ℝ) / Real.rpow Δ (-ε) :=
        (eq_div_iff h_pos2.ne').mpr h_eq
      exact h.symm
    have h_final : (2 : ℝ) * Real.rpow Δ ε ≥ Real.rpow Δ ε := by
      have h9 : 0 < Real.rpow Δ ε := Real.rpow_pos_of_pos hΔ_pos ε
      linarith
    calc
      1 / (4 * C_common * K_pack_plane * K_energy_uniform * K_extra)
        = 2 / (8 * C_common * K_pack_plane * K_energy_uniform * K_extra) := by ring
      _ ≥ 2 / Real.rpow Δ (-ε) := by gcongr
      _ = 2 * ((1 : ℝ) / Real.rpow Δ (-ε)) := by ring
      _ = 2 * Real.rpow Δ ε := by rw [h_div]
      _ ≥ Real.rpow Δ ε := h_final

  -- Uniform size M_nat = ceil(Δ^{-s+23ε})
  let M_real : ℝ := Real.rpow Δ (-s + 23 * ε)
  have hM_real_pos : 0 < M_real := Real.rpow_pos_of_pos hΔ_pos _
  let M_nat : ℕ := Nat.ceil M_real
  have hM_nat_pos : 0 < M_nat := Nat.ceil_pos.mpr hM_real_pos
  have hM_nat_ge : M_real ≤ (M_nat : ℝ) := Nat.le_ceil M_real
  let M_val : ℝ := 2 * (M_nat : ℝ)
  have hM_val_pos : 0 < M_val := by positivity
  have hM_val_half : M_val / 2 = (M_nat : ℝ) := by
    dsimp only [M_val] <;> ring
  have hM_val_lower : M_val ≥ 2 * M_real := by
    have h1 : (M_nat : ℝ) ≥ M_real := hM_nat_ge
    have h2 : (2 : ℝ) * (M_nat : ℝ) ≥ 2 * M_real := by gcongr
    simpa [M_val] using h2

  change ∃ (c : ℝ), 0 < c ∧ c ≥ Real.rpow Δ ε ∧ (2 : ℝ) / c ≤ Real.rpow Δ (-ε) ∧ _
  refine ⟨c, hc_pos, h_absorb_c1, h_absorb_c2, ?_⟩
  intro Qsub hQsub_sub D hD_sub_C hQsub_card hD_card

  have hD_ge_Mnat : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qsub), (D Q hQ).card ≥ M_nat := by
    intro Q hQ
    have h1 : (D Q hQ).card ≥ M_real := hD_card Q hQ
    exact Nat.ceil_le.mpr (by exact_mod_cast h1)

  -- Choose D'(Q) ⊆ D(Q) of size M_nat
  let D' : (Q : CoarseSquare Δ) → Q ∈ Qsub → Finset CoarseTube := fun Q hQ =>
    Classical.choose (Finset.exists_subset_card_eq (hD_ge_Mnat Q hQ))
  have hD'_spec : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qsub),
      D' Q hQ ⊆ D Q hQ ∧ (D' Q hQ).card = M_nat := by
    intro Q hQ
    exact Classical.choose_spec (Finset.exists_subset_card_eq (hD_ge_Mnat Q hQ))
  have hD'_sub : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qsub), D' Q hQ ⊆ D Q hQ :=
    fun Q hQ => (hD'_spec Q hQ).1
  have hD'_card : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qsub), (D' Q hQ).card = M_nat :=
    fun Q hQ => (hD'_spec Q hQ).2
  have hD'_sub_C : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qsub),
      D' Q hQ ⊆ C Q (hQsub_sub hQ) := fun Q hQ =>
    (hD'_sub Q hQ).trans (hD_sub_C Q hQ)

  -- Point set: square centers of Qsub
  let P : Finset EuclideanPlane := Qsub.image (squareCenter Δ)
  let Qimg : Finset EuclideanPlane := Qset.image (squareCenter Δ)
  have h_inj : Function.Injective (squareCenter Δ) := squareCenter_injective hΔ_pos
  have hP_card : (P.card : ℝ) = (Qsub.card : ℝ) := by
    rw [Finset.card_image_of_injective _ h_inj] <;> rfl
  have hQimg_card : (Qimg.card : ℝ) = (Qset.card : ℝ) := by
    rw [Finset.card_image_of_injective _ h_inj] <;> rfl
  have hP_nonempty : P.Nonempty := by
    have h1 : (Qsub.card : ℝ) ≥ Real.rpow Δ (-t + 49 * ε) := hQsub_card
    have h2 : 0 < Real.rpow Δ (-t + 49 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h3 : 0 < (Qsub.card : ℝ) := by linarith
    have h4 : 0 < P.card := by
      rw [Finset.card_image_of_injective _ h_inj]
      exact_mod_cast h3
    exact Finset.card_pos.mp h4
  have hP_sep : Set.Pairwise (P : Set EuclideanPlane) (fun p q => Δ ≤ dist p q) := by
    intro p hp q hq hne
    rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨R, hR, rfl⟩
    have hQR : Q ≠ R := by intro h; apply hne; rw [h]
    exact AppendixA3.square_center_dist_ge hΔ_pos hQR

  -- Tube family map
  let Tp (p : EuclideanPlane) : Finset CoarseTube :=
    if h : p ∈ P then
      let Q : CoarseSquare Δ := Classical.choose (Finset.mem_image.mp h)
      let hQ : Q ∈ Qsub := (Classical.choose_spec (Finset.mem_image.mp h)).1
      D' Q hQ
    else ∅

  have hTp_at_center : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qsub),
      Tp (squareCenter Δ Q) = D' Q hQ := by
    intro Q hQ
    have hP_mem : squareCenter Δ Q ∈ P := Finset.mem_image.mpr ⟨Q, hQ, rfl⟩
    dsimp only [Tp]
    rw [dif_pos hP_mem]
    have hQ'_eq_Q : (Classical.choose (Finset.mem_image.mp hP_mem)) = Q := by
      have h_eq : squareCenter Δ (Classical.choose (Finset.mem_image.mp hP_mem)) = squareCenter Δ Q :=
        (Classical.choose_spec (Finset.mem_image.mp hP_mem)).2
      exact h_inj h_eq
    congr

  have hTp_card_lower : ∀ p ∈ P, (M_val / 2 : ℝ) ≤ (Tp p).card := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
    rw [hTp_at_center Q hQ, hD'_card, hM_val_half]
  have hTp_card_upper : ∀ p ∈ P, (Tp p).card ≤ M_val := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
    rw [hTp_at_center Q hQ, hD'_card]
    dsimp only [M_val] <;> norm_cast <;> omega

  -- M_C = upper bound for |C(Q)|, used in common tube bound
  let M_C : ℝ := Real.rpow Δ (-s - 29 * ε)
  have hM_C_pos : 0 < M_C := Real.rpow_pos_of_pos hΔ_pos _
  have hΔ_le_one : Δ ≤ 1 := by linarith
  have hM_C_le_scaled : M_C ≤ Real.rpow Δ (-52 * ε) * M_val := by
    have h1 : M_val ≥ 2 * Real.rpow Δ (-s + 23 * ε) := hM_val_lower
    have h_pos52 : 0 ≤ Real.rpow Δ (-52 * ε) := Real.rpow_nonneg hΔ_pos.le _
    have h2 : Real.rpow Δ (-52 * ε) * M_val ≥ 2 * Real.rpow Δ (-s - 29 * ε) := by
      have h3 : Real.rpow Δ (-52 * ε) * Real.rpow Δ (-s + 23 * ε) = Real.rpow Δ (-s - 29 * ε) :=
        h_rpow_eq hΔ_pos (-52 * ε) (-s + 23 * ε) (-s - 29 * ε) (by ring)
      calc
        Real.rpow Δ (-52 * ε) * M_val
          ≥ Real.rpow Δ (-52 * ε) * (2 * Real.rpow Δ (-s + 23 * ε)) := by gcongr <;> exact h_pos52
        _ = 2 * (Real.rpow Δ (-52 * ε) * Real.rpow Δ (-s + 23 * ε)) := by ring
        _ = 2 * Real.rpow Δ (-s - 29 * ε) := by rw [h3]
    have h_pos_s29 : 0 ≤ Real.rpow Δ (-s - 29 * ε) := Real.rpow_nonneg hΔ_pos.le _
    have h4 : M_C ≤ 2 * Real.rpow Δ (-s - 29 * ε) := by
      have h5 : M_C = Real.rpow Δ (-s - 29 * ε) := by rfl
      rw [h5]
      have h6 : Real.rpow Δ (-s - 29 * ε) ≤ 2 * Real.rpow Δ (-s - 29 * ε) := by
        have h7 : 0 ≤ Real.rpow Δ (-s - 29 * ε) := h_pos_s29
        linarith
      exact h6
    calc M_C
      ≤ 2 * Real.rpow Δ (-s - 29 * ε) := h4
    _ ≤ Real.rpow Δ (-52 * ε) * M_val := h2

  -- Common tube intersection bound: apply to C(Q), C(R) directly, then transfer to D'
  have h_common_bound : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      ((Tp p) ∩ (Tp q)).card ≤ C_common * C_T' * M_val * (Δ / dist p q)^s := by
    intro p hp q hq hne
    rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨R, hR, rfl⟩
    have hQR : Q ≠ R := by intro h; apply hne; rw [h]
    have hd_pos : 0 < dist (squareCenter Δ Q) (squareCenter Δ R) := by
      have h : Δ ≤ dist (squareCenter Δ Q) (squareCenter Δ R) := AppendixA3.square_center_dist_ge hΔ_pos hQR
      linarith
    have h_main := AppendixA3.arbitrary_point_common_tubes_bound
      (hk := show (1 : ℝ) ≤ (10 : ℝ) from by norm_num)
      hΔ_pos hs hCT_pos hM_C_pos
      (hC_Q_sset := hC_sset Q (hQsub_sub hQ))
      (hC_Q_sep := hC_sep Q (hQsub_sub hQ))
      (hC_Q_card := by exact_mod_cast hC_card_upper Q (hQsub_sub hQ))
      (hC_Q_near_center := hC_near Q (hQsub_sub hQ))
      (hC_R_near_center := hC_near R (hQsub_sub hR))
      (hp_in_square := square_center_in_square hΔ_pos Q)
      (hq_in_square := square_center_in_square hΔ_pos R)
      (hp_bound := hCenter_bound Q (hQsub_sub hQ))
      (hq_bound := hCenter_bound R (hQsub_sub hR))
      (h_dist_pos := hd_pos)
      (h_dist_le_3 := hDist_le_3 Q (hQsub_sub hQ) R (hQsub_sub hR))
    have h9 : (800 * (10 + 1 : ℝ)) = (800 * (11 : ℝ)) := by norm_num
    rw [h9] at h_main
    have h10 : (MainAppendix.affineLine_packing_constant : ℝ) * C_T * ((800 * (11 : ℝ)) : ℝ)^s * M_C *
          (Δ / dist (squareCenter Δ Q) (squareCenter Δ R))^s =
        C_common * C_T * M_C * (Δ / dist (squareCenter Δ Q) (squareCenter Δ R))^s := by
      dsimp only [C_common] <;> ring
    rw [h10] at h_main
    have h_main' : (((C Q (hQsub_sub hQ)) ∩ (C R (hQsub_sub hR))).card : ℝ) ≤
        C_common * C_T * M_C * (Δ / dist (squareCenter Δ Q) (squareCenter Δ R))^s := by
      have h_inst : (Subtype.instDecidableEq : DecidableEq CoarseTube) = (tubeDecidableEq : DecidableEq CoarseTube) :=
        Subsingleton.elim _ _
      exact h_inst ▸ h_main
    have h_sub : (D' Q hQ) ∩ (D' R hR) ⊆ (C Q (hQsub_sub hQ)) ∩ (C R (hQsub_sub hR)) := by
      exact Finset.inter_subset_inter (hD'_sub_C Q hQ) (hD'_sub_C R hR)
    have h_card : ((D' Q hQ) ∩ (D' R hR)).card ≤ ((C Q (hQsub_sub hQ)) ∩ (C R (hQsub_sub hR))).card :=
      Finset.card_le_card h_sub
    have hbase_pos : 0 < Δ / dist (squareCenter Δ Q) (squareCenter Δ R) := by positivity
    have h_CT'_eq : C_T' = C_T * Real.rpow Δ (-52 * ε) := by
      dsimp only [C_T', C_T]
      rw [h_rpow_eq hΔ_pos (-59 * ε) (-52 * ε) (-111 * ε) (by ring)]
      <;> rfl
    have h_scale : C_T * M_C ≤ C_T' * M_val := by
      rw [h_CT'_eq]
      have h : C_T * M_C ≤ C_T * (Real.rpow Δ (-52 * ε) * M_val) := by
        gcongr
        <;> exact hM_C_le_scaled
      linarith
    have h_final : (((D' Q hQ) ∩ (D' R hR)).card : ℝ) ≤
        C_common * C_T' * M_val * (Δ / dist (squareCenter Δ Q) (squareCenter Δ R))^s := by
      calc
        (((D' Q hQ) ∩ (D' R hR)).card : ℝ)
          ≤ (((C Q (hQsub_sub hQ)) ∩ (C R (hQsub_sub hR))).card : ℝ) := by exact_mod_cast h_card
        _ ≤ C_common * C_T * M_C * (Δ / dist (squareCenter Δ Q) (squareCenter Δ R))^s := h_main'
        _ ≤ C_common * C_T' * M_val * (Δ / dist (squareCenter Δ Q) (squareCenter Δ R))^s := by
          have hpos : 0 ≤ C_common * (Δ / dist (squareCenter Δ Q) (squareCenter Δ R))^s := by positivity
          have h : C_common * (Δ / dist (squareCenter Δ Q) (squareCenter Δ R))^s * (C_T * M_C) ≤
              C_common * (Δ / dist (squareCenter Δ Q) (squareCenter Δ R))^s * (C_T' * M_val) :=
            mul_le_mul_of_nonneg_left h_scale hpos
          ring_nf at h ⊢
          exact h
    rw [hTp_at_center Q hQ, hTp_at_center R hR]
    exact h_final

  -- Energy bound: transfer S-set from Qimg to P via covering ratio, then apply directly
  have hP_sub_Qset : (P : Set EuclideanPlane) ⊆ (Qimg : Set EuclideanPlane) :=
    Finset.image_mono (squareCenter Δ) hQsub_sub

  -- Step 1: covering(Qimg) ≤ |Qimg|
  have h_cov_Qimg_le_card : (Metric.externalCoveringNumber Δ.toNNReal (Qimg : Set EuclideanPlane) : ENNReal) ≤
      (Qimg.card : ENNReal) := by
    have h1 : Metric.externalCoveringNumber Δ.toNNReal (Qimg : Set EuclideanPlane) ≤
        (Qimg : Set EuclideanPlane).encard :=
      Metric.externalCoveringNumber_le_encard_self (ε := Δ.toNNReal) (A := (Qimg : Set EuclideanPlane))
    have h2 : (Metric.externalCoveringNumber Δ.toNNReal (Qimg : Set EuclideanPlane) : ENNReal) ≤
        ((Qimg : Set EuclideanPlane).encard : ENNReal) := by
      exact ENat.toENNReal_le.mpr h1
    have h3 : ((Qimg : Set EuclideanPlane).encard : ENNReal) = (Qimg.card : ENNReal) := by simp
    rw [h3] at h2
    exact h2

  -- Step 2: |Qimg| ≤ Δ^{-50ε} * |P|
  have h_card_ratio : (Qimg.card : ℝ) ≤ Real.rpow Δ (-50 * ε) * (P.card : ℝ) := by
    have h2 : (Qimg.card : ℝ) ≤ Real.rpow Δ (-t - ε) := by
      rw [hQimg_card]; exact hQset_card_upper
    have h3 : (P.card : ℝ) ≥ Real.rpow Δ (-t + 49 * ε) := by
      rw [hP_card]; exact hQsub_card
    calc (Qimg.card : ℝ)
      ≤ Real.rpow Δ (-t - ε) := h2
    _ = Real.rpow Δ (-50 * ε) * Real.rpow Δ (-t + 49 * ε) := by
      have h6 : Real.rpow Δ (-50 * ε) * Real.rpow Δ (-t + 49 * ε) = Real.rpow Δ (-t - ε) :=
        h_rpow_eq hΔ_pos (-50 * ε) (-t + 49 * ε) (-t - ε) (by ring)
      rw [h6]
    _ ≤ Real.rpow Δ (-50 * ε) * (P.card : ℝ) := by
      have h_pos : 0 ≤ Real.rpow Δ (-50 * ε) := Real.rpow_nonneg hΔ_pos.le _
      exact mul_le_mul_of_nonneg_left h3 h_pos

  have h_card_ratio_ennreal : (Qimg.card : ENNReal) ≤
      ENNReal.ofReal (Real.rpow Δ (-50 * ε)) * (P.card : ENNReal) := by
    have h5 : (Qimg.card : ENNReal) = ENNReal.ofReal (Qimg.card : ℝ) := by simp
    have h6 : (P.card : ENNReal) = ENNReal.ofReal (P.card : ℝ) := by simp
    rw [h5, h6]
    have h_pos1 : 0 ≤ Real.rpow Δ (-50 * ε) := Real.rpow_nonneg hΔ_pos.le _
    have h_pos2 : 0 ≤ (P.card : ℝ) := by positivity
    have h7 : ENNReal.ofReal (Qimg.card : ℝ) ≤
        ENNReal.ofReal (Real.rpow Δ (-50 * ε) * (P.card : ℝ)) := by
      exact ENNReal.ofReal_le_ofReal h_card_ratio
    have h8 : ENNReal.ofReal (Real.rpow Δ (-50 * ε) * (P.card : ℝ)) =
        ENNReal.ofReal (Real.rpow Δ (-50 * ε)) * ENNReal.ofReal (P.card : ℝ) := by
      rw [ENNReal.ofReal_mul h_pos1] <;> ring
    rw [h8] at h7
    exact h7

  -- Step 3: |P| ≤ K_pack_plane * covering(P)
  have hP_cov_fin : (Metric.externalCoveringNumber Δ.toNNReal (P : Set EuclideanPlane) : ENNReal) < ⊤ := by
    have h1 : Metric.externalCoveringNumber Δ.toNNReal (P : Set EuclideanPlane) ≤
        (P : Set EuclideanPlane).encard :=
      Metric.externalCoveringNumber_le_encard_self (ε := Δ.toNNReal) (A := (P : Set EuclideanPlane))
    have h2 : (Metric.externalCoveringNumber Δ.toNNReal (P : Set EuclideanPlane) : ENNReal) ≤
        ((P : Set EuclideanPlane).encard : ENNReal) := by exact ENat.toENNReal_le.mpr h1
    have h3 : ((P : Set EuclideanPlane).encard : ENNReal) = (P.card : ENNReal) := by simp
    rw [h3] at h2
    exact h2.trans_lt ENNReal.coe_lt_top

  let δnn : NNReal := Δ.toNNReal
  have hδnn_eq : (δnn : ℝ) = Δ := by
    simp [δnn, hΔ_pos.le]

  have hP_sep' : Set.Pairwise (P : Set EuclideanPlane) (fun x y => (δnn : ℝ) ≤ dist x y) := by
    simpa [hδnn_eq] using hP_sep

  have h_pack_plane_bound : ∀ (z : EuclideanPlane) (T : Set EuclideanPlane),
      Set.Pairwise T (fun x y => (δnn : ℝ) ≤ dist x y) →
      T ⊆ Metric.closedBall z (2 * (δnn : ℝ)) →
      T.Finite ∧ T.encard ≤ (MainAppendix.plane_packing_constant : ENat) := by
    intro z T hT_sep hT_sub
    have hT_sep2 : Set.Pairwise T (fun x y => Δ ≤ dist x y) := by
      simpa [hδnn_eq] using hT_sep
    have hT_sub2 : T ⊆ Metric.closedBall z (2 * Δ) := by
      simpa [hδnn_eq] using hT_sub
    exact MainAppendix.plane_packing_constant_bound Δ hΔ_pos z T hT_sep2 hT_sub2

  have hδnn_eq' : δnn = Δ.toNNReal := by simp [δnn]
  have hP_cov_fin' : (Metric.externalCoveringNumber δnn (P : Set EuclideanPlane) : ENNReal) < ⊤ := by
    rw [hδnn_eq']
    exact hP_cov_fin

  have hP_card_le_cov : ↑((P : Set EuclideanPlane).encard) ≤
      (MainAppendix.plane_packing_constant : ENNReal) *
      Metric.externalCoveringNumber δnn (P : Set EuclideanPlane) :=
    MainAppendix.separated_set_card_le_covering hP_sep' MainAppendix.plane_packing_constant
      h_pack_plane_bound hP_cov_fin'

  have hP_card_le_cov' : (P.card : ENNReal) ≤
      ENNReal.ofReal K_pack_plane * Metric.externalCoveringNumber Δ.toNNReal (P : Set EuclideanPlane) := by
    have h9 : ↑((P : Set EuclideanPlane).encard) = (P.card : ENNReal) := by simp
    have h10 : (MainAppendix.plane_packing_constant : ENNReal) = ENNReal.ofReal K_pack_plane := by
      dsimp only [K_pack_plane] <;> norm_cast
    have h11 : Metric.externalCoveringNumber δnn (P : Set EuclideanPlane) =
        Metric.externalCoveringNumber Δ.toNNReal (P : Set EuclideanPlane) := by
      rw [hδnn_eq']
    rw [h9, h10, h11] at hP_card_le_cov
    exact hP_card_le_cov

  -- Step 4: covering(Qimg) ≤ K_pack_plane * Δ^{-50ε} * covering(P)
  let K_ratio : ℝ := K_pack_plane * Real.rpow Δ (-50 * ε)
  have hK_ratio_pos : 0 < K_ratio := mul_pos hK_pack_plane_pos (Real.rpow_pos_of_pos hΔ_pos _)

  have h_cover_ratio : Metric.externalCoveringNumber Δ.toNNReal (Qimg : Set EuclideanPlane) ≤
      ENNReal.ofReal K_ratio * Metric.externalCoveringNumber Δ.toNNReal (P : Set EuclideanPlane) := by
    calc
      Metric.externalCoveringNumber Δ.toNNReal (Qimg : Set EuclideanPlane)
        ≤ (Qimg.card : ENNReal) := h_cov_Qimg_le_card
      _ ≤ ENNReal.ofReal (Real.rpow Δ (-50 * ε)) * (P.card : ENNReal) := h_card_ratio_ennreal
      _ ≤ ENNReal.ofReal (Real.rpow Δ (-50 * ε)) *
            (ENNReal.ofReal K_pack_plane * Metric.externalCoveringNumber Δ.toNNReal (P : Set EuclideanPlane)) := by
          gcongr
      _ = ENNReal.ofReal K_ratio * Metric.externalCoveringNumber Δ.toNNReal (P : Set EuclideanPlane) := by
        have h_pos_rpow : 0 ≤ Real.rpow Δ (-50 * ε) := Real.rpow_nonneg hΔ_pos.le _
        have h11 : ENNReal.ofReal (Real.rpow Δ (-50 * ε)) * ENNReal.ofReal K_pack_plane =
            ENNReal.ofReal (Real.rpow Δ (-50 * ε) * K_pack_plane) := by
          rw [←ENNReal.ofReal_mul h_pos_rpow] <;> ring
        have h_assoc : ENNReal.ofReal (Real.rpow Δ (-50 * ε)) *
            (ENNReal.ofReal K_pack_plane * Metric.externalCoveringNumber Δ.toNNReal (P : Set EuclideanPlane)) =
            (ENNReal.ofReal (Real.rpow Δ (-50 * ε)) * ENNReal.ofReal K_pack_plane) *
            Metric.externalCoveringNumber Δ.toNNReal (P : Set EuclideanPlane) := by ring
        rw [h_assoc, h11]
        have h12 : Real.rpow Δ (-50 * ε) * K_pack_plane = K_ratio := by
          dsimp only [K_ratio] <;> ring
        rw [h12] <;> ring

  -- Step 5: Transfer S-set from Qimg to P with degraded constant C_P'
  have hCP'_eq : C_P' = K_ratio * C_P := by
    dsimp only [C_P', K_ratio, C_P]
    <;> ring

  have hP_sset0 : IsDeltaSSet Δ t (K_ratio * C_P) (P : Set EuclideanPlane) :=
    AppendixA4.IsDeltaSSet.subset_with_cover_ratio (K := K_ratio)
      hK_ratio_pos hQset_sset hP_sub_Qset h_cover_ratio

  have hP_sset : IsDeltaSSet Δ t C_P' (P : Set EuclideanPlane) := by
    rw [hCP'_eq]
    exact hP_sset0

  -- Step 6: Apply energy bound directly to P with C_P'
  rcases MainAppendix.s_energy_bound_plane_exists
      hΔ_pos hs hst hR_pos hCP'_pos
      hP_sep
      hP_sset
      (fun p hp => by
        rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
        exact hCenter_bound Q (hQsub_sub hQ))
    with ⟨K_energy_P, hK_energy_pos, hK_energy_lower, hK_eq, h_energy_P⟩

  have hK_eq2 : K_energy_P = K_energy_uniform := hK_eq

  -- Convert energy bound to the form expected by global_2s_bound
  have h_energy_P' : ∑ p ∈ P, ∑ q ∈ P.erase p, dist p q ^ (-s) ≤
      K_energy_eff * C_P' * (P.card : ℝ)^2 := by
    have h_eq1 : K_energy_P = K_energy_eff := by
      rw [hK_eq2] <;> rfl
    rw [h_eq1] at h_energy_P
    exact h_energy_P

  -- Prove hP_large condition: K ≥ 2
  have hP_card_lower : (P.card : ℝ) ≥ Real.rpow Δ (-t + 49 * ε) := by
    rw [hP_card]; exact hQsub_card

  let K : ℝ := C_common * C_P' * C_T' * K_energy_eff * Δ^s * (P.card : ℝ)

  have hK_ge_two : (2 : ℝ) ≤ K := by
    have h1 : K_energy_uniform ≥ (4 : ℝ)^t := by
      have h_four : (2 * (2 : ℝ)) = (4 : ℝ) := by norm_num
      have h1' : K_energy_P ≥ (4 : ℝ)^t := by
        rw [h_four] at hK_energy_lower
        exact hK_energy_lower
      rw [hK_eq2] at h1'
      exact h1'
    have h2 : (P.card : ℝ) ≥ Real.rpow Δ (-t + 49 * ε) := hP_card_lower
    have h1 : K_energy_uniform ≥ (4 : ℝ)^t := by
      have h_four : (2 * (2 : ℝ)) = (4 : ℝ) := by norm_num
      have h1' : K_energy_P ≥ (4 : ℝ)^t := by
        rw [h_four] at hK_energy_lower
        exact hK_energy_lower
      rw [hK_eq2] at h1'
      exact h1'
    have h2 : (P.card : ℝ) ≥ Real.rpow Δ (-t + 49 * ε) := hP_card_lower
    have h_rpow_sum : Real.rpow Δ (-50 * ε) * C_Qimg * Real.rpow Δ (-111 * ε) *
        Real.rpow Δ s * Real.rpow Δ (-t + 49 * ε) =
        C_Qimg * Real.rpow Δ (s - t - 112 * ε) := by
      have h51 : Real.rpow Δ (-50 * ε) * Real.rpow Δ (-111 * ε) = Real.rpow Δ (-161 * ε) :=
        h_rpow_eq hΔ_pos (-50 * ε) (-111 * ε) (-161 * ε) (by ring)
      have h52 : Real.rpow Δ s * Real.rpow Δ (-t + 49 * ε) = Real.rpow Δ (s - t + 49 * ε) :=
        h_rpow_eq hΔ_pos s (-t + 49 * ε) (s - t + 49 * ε) (by ring)
      have h53 : Real.rpow Δ (-161 * ε) * Real.rpow Δ (s - t + 49 * ε) = Real.rpow Δ (s - t - 112 * ε) :=
        h_rpow_eq hΔ_pos (-161 * ε) (s - t + 49 * ε) (s - t - 112 * ε) (by ring)
      calc
        Real.rpow Δ (-50 * ε) * C_Qimg * Real.rpow Δ (-111 * ε) *
            Real.rpow Δ s * Real.rpow Δ (-t + 49 * ε)
          = C_Qimg * (Real.rpow Δ (-50 * ε) * Real.rpow Δ (-111 * ε)) *
              (Real.rpow Δ s * Real.rpow Δ (-t + 49 * ε)) := by ring
        _ = C_Qimg * Real.rpow Δ (-161 * ε) * Real.rpow Δ (s - t + 49 * ε) := by
          rw [h51, h52] <;> ring
        _ = C_Qimg * Real.rpow Δ (s - t - 112 * ε) := by
          have h54 : C_Qimg * Real.rpow Δ (-161 * ε) * Real.rpow Δ (s - t + 49 * ε) =
              C_Qimg * (Real.rpow Δ (-161 * ε) * Real.rpow Δ (s - t + 49 * ε)) := by ring
          rw [h54, h53] <;> ring
    have h_energy_product : K_energy_uniform * (P.card : ℝ) ≥
        (4 : ℝ)^t * Real.rpow Δ (-t + 49 * ε) := by
      have h_pos1 : 0 ≤ (4 : ℝ)^t := by positivity
      have h_pos2 : 0 ≤ Real.rpow Δ (-t + 49 * ε) := Real.rpow_nonneg hΔ_pos.le _
      nlinarith
    have h3 : C_common * K_pack_plane * Real.rpow Δ (-50 * ε) * C_Qimg * Real.rpow Δ (-111 * ε) *
        K_energy_uniform * Real.rpow Δ s * (P.card : ℝ) ≥
        C_common * K_pack_plane * Real.rpow Δ (-50 * ε) * C_Qimg * Real.rpow Δ (-111 * ε) *
        Real.rpow Δ s * ((4 : ℝ)^t * Real.rpow Δ (-t + 49 * ε)) := by
      have h_goal : C_common * K_pack_plane * Real.rpow Δ (-50 * ε) * C_Qimg * Real.rpow Δ (-111 * ε) *
          K_energy_uniform * Real.rpow Δ s * (P.card : ℝ) =
          C_common * K_pack_plane * Real.rpow Δ (-50 * ε) * C_Qimg * Real.rpow Δ (-111 * ε) *
          Real.rpow Δ s * (K_energy_uniform * (P.card : ℝ)) := by ring
      rw [h_goal]
      have h_common_nonneg : 0 ≤ C_common * K_pack_plane * Real.rpow Δ (-50 * ε) * C_Qimg * Real.rpow Δ (-111 * ε) * Real.rpow Δ s := by
        apply mul_nonneg
        · apply mul_nonneg
          · apply mul_nonneg
            · apply mul_nonneg
              · apply mul_nonneg
                · exact hCcommon_pos.le
                · exact hK_pack_plane_pos.le
              · exact Real.rpow_nonneg hΔ_pos.le _
            · exact hC_Qimg_pos.le
          · exact Real.rpow_nonneg hΔ_pos.le _
        · exact Real.rpow_nonneg hΔ_pos.le _
      exact mul_le_mul_of_nonneg_left h_energy_product h_common_nonneg
    have h4 : C_common * K_pack_plane * Real.rpow Δ (-50 * ε) * C_Qimg * Real.rpow Δ (-111 * ε) *
        Real.rpow Δ s * ((4 : ℝ)^t * Real.rpow Δ (-t + 49 * ε)) =
        C_common * K_pack_plane * C_Qimg * (4 : ℝ)^t * Real.rpow Δ (s - t - 112 * ε) := by
      have h_comm : C_common * K_pack_plane * Real.rpow Δ (-50 * ε) * C_Qimg * Real.rpow Δ (-111 * ε) *
          Real.rpow Δ s * ((4 : ℝ)^t * Real.rpow Δ (-t + 49 * ε)) =
          C_common * K_pack_plane * C_Qimg * (4 : ℝ)^t *
          (Real.rpow Δ (-50 * ε) * Real.rpow Δ (-111 * ε) *
           Real.rpow Δ s * Real.rpow Δ (-t + 49 * ε)) := by ring
      have h_rpow_sum2 : Real.rpow Δ (-50 * ε) * Real.rpow Δ (-111 * ε) *
          Real.rpow Δ s * Real.rpow Δ (-t + 49 * ε) = Real.rpow Δ (s - t - 112 * ε) := by
        have h51 : Real.rpow Δ (-50 * ε) * Real.rpow Δ (-111 * ε) = Real.rpow Δ (-161 * ε) := h_rpow_eq hΔ_pos (-50 * ε) (-111 * ε) (-161 * ε) (by ring)
        have h52 : Real.rpow Δ s * Real.rpow Δ (-t + 49 * ε) = Real.rpow Δ (s - t + 49 * ε) := h_rpow_eq hΔ_pos s (-t + 49 * ε) (s - t + 49 * ε) (by ring)
        have h53 : Real.rpow Δ (-161 * ε) * Real.rpow Δ (s - t + 49 * ε) = Real.rpow Δ (s - t - 112 * ε) := h_rpow_eq hΔ_pos (-161 * ε) (s - t + 49 * ε) (s - t - 112 * ε) (by ring)
        calc
          Real.rpow Δ (-50 * ε) * Real.rpow Δ (-111 * ε) * Real.rpow Δ s * Real.rpow Δ (-t + 49 * ε)
            = (Real.rpow Δ (-50 * ε) * Real.rpow Δ (-111 * ε)) * (Real.rpow Δ s * Real.rpow Δ (-t + 49 * ε)) := by ring
          _ = Real.rpow Δ (-161 * ε) * Real.rpow Δ (s - t + 49 * ε) := by rw [h51, h52]
          _ = Real.rpow Δ (s - t - 112 * ε) := h53
      rw [h_comm, h_rpow_sum2] <;> ring
    have h5 : C_common * K_pack_plane * Real.rpow Δ (-50 * ε) * C_Qimg * Real.rpow Δ (-111 * ε) *
        K_energy_uniform * Real.rpow Δ s * (P.card : ℝ) ≥
        C_common * (MainAppendix.plane_packing_constant : ℝ) * (4 : ℝ)^t * C_Qimg * Real.rpow Δ (s - t - 112 * ε) := by
      rw [h4] at h3
      have hKpack : K_pack_plane = (MainAppendix.plane_packing_constant : ℝ) := by rfl
      rw [hKpack] at h3
      linarith
    have hC_common_eq : C_common = (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (11 : ℝ)) : ℝ)^s := by
      dsimp only [C_common] <;> rfl
    have h_final : (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (11 : ℝ)) : ℝ)^s *
        (MainAppendix.plane_packing_constant : ℝ) * (4 : ℝ)^t *
        C_Qimg * Real.rpow Δ (s - t - 112 * ε) ≥ 2 := hK_large_weak
    have h_exp : Δ^s = Real.rpow Δ s := by rfl
    have hK_eq : K = C_common * K_pack_plane * Real.rpow Δ (-50 * ε) * C_Qimg * Real.rpow Δ (-111 * ε) *
        K_energy_uniform * Real.rpow Δ s * (P.card : ℝ) := by
      dsimp only [K, C_P', C_T', K_energy_eff, C_common, K_pack_plane]
      rw [h_exp] <;> ring
    rw [hK_eq]
    have h6 : C_common * K_pack_plane * Real.rpow Δ (-50 * ε) * C_Qimg * Real.rpow Δ (-111 * ε) *
        K_energy_uniform * Real.rpow Δ s * (P.card : ℝ) ≥
        (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (11 : ℝ)) : ℝ)^s *
        (MainAppendix.plane_packing_constant : ℝ) * (4 : ℝ)^t *
        C_Qimg * Real.rpow Δ (s - t - 112 * ε) := by
      rw [←hC_common_eq]
      exact h5
    exact le_trans h_final h6

  -- Apply global 2s bound (hP_large branch)
  have h_global : ((P.biUnion Tp).card : ℝ) ≥
      M_val * Δ^(-s) / (8 * C_common * C_P' * C_T' * K_energy_eff) :=
    Global2sBound.global_2s_bound
      (X := EuclideanPlane)
      hΔ_pos (by linarith [hΔ_lt_half]) hs hst
      hCP'_pos hCT'_pos hM_val_pos hCcommon_pos hK_energy_eff_pos
      hP_nonempty hP_sep hTp_card_lower hTp_card_upper h_common_bound h_energy_P'
      hK_ge_two

  -- Union of D'(Q) is subset of union of D(Q), which is subset of T_Δ filter
  have hUnion_sub1 : P.biUnion Tp ⊆ T_Δ.filter (fun T => ∃ Q hQ, T ∈ D Q hQ) := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨p, hp, hTp⟩
    rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
    have h_in_D' : T ∈ D' Q hQ := by
      rw [hTp_at_center Q hQ] at hTp; exact hTp
    have h_in_D : T ∈ D Q hQ := hD'_sub Q hQ h_in_D'
    have h_in_C : T ∈ C Q (hQsub_sub hQ) := hD_sub_C Q hQ h_in_D
    have h_in_TΔ : T ∈ T_Δ := hC_sub_TΔ Q (hQsub_sub hQ) h_in_C
    exact Finset.mem_filter.mpr ⟨h_in_TΔ, ⟨Q, hQ, h_in_D⟩⟩

  have hUnion_card : ((P.biUnion Tp).card : ℝ) ≤
      ((T_Δ.filter (fun T => ∃ Q hQ, T ∈ D Q hQ)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hUnion_sub1

  -- Final lower bound: use C_Qimg ≤ K_extra * Δ^{-26ε} to reach exponent -2s+210ε
  have hCP'_upper : C_P' ≤ K_pack_plane * K_extra * Real.rpow Δ (-76 * ε) := by
    dsimp only [C_P']
    have h1 : C_Qimg ≤ K_extra * Real.rpow Δ (-26 * ε) := hC_Qimg_le
    have h_pos : 0 ≤ Real.rpow Δ (-50 * ε) := Real.rpow_nonneg hΔ_pos.le _
    calc
      K_pack_plane * Real.rpow Δ (-50 * ε) * C_Qimg
        ≤ K_pack_plane * Real.rpow Δ (-50 * ε) * (K_extra * Real.rpow Δ (-26 * ε)) := by gcongr
      _ = K_pack_plane * K_extra * Real.rpow Δ (-76 * ε) := by
        have h_exp : Real.rpow Δ (-50 * ε) * Real.rpow Δ (-26 * ε) = Real.rpow Δ (-76 * ε) :=
          h_rpow_eq hΔ_pos (-50 * ε) (-26 * ε) (-76 * ε) (by ring)
        have h_align : K_pack_plane * Real.rpow Δ (-50 * ε) * (K_extra * Real.rpow Δ (-26 * ε)) =
            K_pack_plane * K_extra * (Real.rpow Δ (-50 * ε) * Real.rpow Δ (-26 * ε)) := by ring
        rw [h_align, h_exp] <;> ring

  have h_main_lower : M_val * Δ^(-s) / (8 * C_common * C_P' * C_T' * K_energy_eff) ≥
      c * Real.rpow Δ (-2 * s + 210 * ε) := by
    dsimp only [c, K_energy_eff]
    have hM_lower : M_val ≥ 2 * Real.rpow Δ (-s + 23 * ε) := hM_val_lower
    have h1 : M_val * Δ^(-s) ≥ 2 * Real.rpow Δ (-2 * s + 23 * ε) := by
      have hΔs : Δ^(-s) = Real.rpow Δ (-s) := by rfl
      have h_rpow : Real.rpow Δ (-s + 23 * ε) * Real.rpow Δ (-s) = Real.rpow Δ (-2 * s + 23 * ε) :=
        h_rpow_eq hΔ_pos (-s + 23 * ε) (-s) (-2 * s + 23 * ε) (by ring)
      calc M_val * Δ^(-s)
        ≥ (2 * Real.rpow Δ (-s + 23 * ε)) * Δ^(-s) := by gcongr <;> rfl
      _ = 2 * (Real.rpow Δ (-s + 23 * ε) * Δ^(-s)) := by ring
      _ = 2 * (Real.rpow Δ (-s + 23 * ε) * Real.rpow Δ (-s)) := by rw [hΔs]
      _ = 2 * Real.rpow Δ (-2 * s + 23 * ε) := by rw [h_rpow]
    have h_denom_upper : 8 * C_common * C_P' * C_T' * K_energy_uniform ≤
        8 * C_common * (K_pack_plane * K_extra * Real.rpow Δ (-76 * ε)) * Real.rpow Δ (-111 * ε) * K_energy_uniform := by
      gcongr
      <;> exact hCP'_upper
    have h_denom_eq : 8 * C_common * (K_pack_plane * K_extra * Real.rpow Δ (-76 * ε)) * Real.rpow Δ (-111 * ε) * K_energy_uniform =
        8 * C_common * K_pack_plane * K_extra * K_energy_uniform * Real.rpow Δ (-187 * ε) := by
      have h_exp : Real.rpow Δ (-76 * ε) * Real.rpow Δ (-111 * ε) = Real.rpow Δ (-187 * ε) :=
        h_rpow_eq hΔ_pos (-76 * ε) (-111 * ε) (-187 * ε) (by ring)
      have h_align : 8 * C_common * (K_pack_plane * K_extra * Real.rpow Δ (-76 * ε)) * Real.rpow Δ (-111 * ε) * K_energy_uniform =
          8 * C_common * K_pack_plane * K_extra * K_energy_uniform * (Real.rpow Δ (-76 * ε) * Real.rpow Δ (-111 * ε)) := by ring
      rw [h_align, h_exp] <;> ring
    have h_denom_pos : 0 < 8 * C_common * C_P' * C_T' * K_energy_uniform := by positivity
    have h_final : (2 * Real.rpow Δ (-2 * s + 23 * ε)) /
        (8 * C_common * K_pack_plane * K_extra * K_energy_uniform * Real.rpow Δ (-187 * ε)) =
        (1 / (4 * C_common * K_pack_plane * K_energy_uniform * K_extra)) * Real.rpow Δ (-2 * s + 210 * ε) := by
      set A := Real.rpow Δ (-2 * s + 23 * ε) with hA
      set B := 8 * C_common * K_pack_plane * K_energy_uniform * K_extra with hB
      set C := Real.rpow Δ (-187 * ε) with hC
      set D := 4 * C_common * K_pack_plane * K_energy_uniform * K_extra with hD
      set E := Real.rpow Δ (-2 * s + 210 * ε) with hE
      have h_eq : E * C = A := by
        simp only [hE, hC, hA]
        rw [h_rpow_eq hΔ_pos (-2 * s + 210 * ε) (-187 * ε) (-2 * s + 23 * ε) (by ring)]
      have h_pos_BC : 0 < B * C := by
        have hB_pos : 0 < B := by
          dsimp only [B]
          have h1 : 0 < (8 : ℝ) * C_common := by positivity
          have h2 : 0 < (8 : ℝ) * C_common * K_pack_plane := mul_pos h1 hK_pack_plane_pos
          have h3 : 0 < (8 : ℝ) * C_common * K_pack_plane * K_energy_uniform := mul_pos h2 hK_energy_uniform_pos
          exact mul_pos h3 hK_extra_pos
        have hC_pos : 0 < C := Real.rpow_pos_of_pos hΔ_pos _
        exact mul_pos hB_pos hC_pos
      have h_pos_D : 0 < D := by positivity
      have h_B_eq : B = 2 * D := by
        simp only [hB, hD] <;> ring
      have h_cross : (2 * A) * D = E * (B * C) := by
        calc
          (2 * A) * D = 2 * A * D := by ring
          _ = 8 * C_common * K_pack_plane * K_energy_uniform * K_extra * A := by
            simp only [hD] <;> ring
          _ = 8 * C_common * K_pack_plane * K_energy_uniform * K_extra * (E * C) := by rw [h_eq]
          _ = E * (B * C) := by
            simp only [hB] <;> ring
      have h_denom_align : (8 * C_common * K_pack_plane * K_extra * K_energy_uniform * Real.rpow Δ (-187 * ε)) = B * C := by
        dsimp only [B, C] <;> ring
      have h_div_eq : (2 * A) / (8 * C_common * K_pack_plane * K_extra * K_energy_uniform * Real.rpow Δ (-187 * ε)) = E / D := by
        rw [h_denom_align]
        rw [div_eq_div_iff h_pos_BC.ne' h_pos_D.ne']
        exact h_cross
      have h2 : (1 / D) * E = E / D := by ring
      rw [h2]
      exact h_div_eq
    have h6 : M_val * Δ^(-s) / (8 * C_common * C_P' * C_T' * K_energy_uniform) ≥
        (2 * Real.rpow Δ (-2 * s + 23 * ε)) /
        (8 * C_common * C_P' * C_T' * K_energy_uniform) := by gcongr
    have h_denom_le : 8 * C_common * C_P' * C_T' * K_energy_uniform ≤
        8 * C_common * K_pack_plane * K_extra * K_energy_uniform * Real.rpow Δ (-187 * ε) := by
      calc
        8 * C_common * C_P' * C_T' * K_energy_uniform
          ≤ 8 * C_common * (K_pack_plane * K_extra * Real.rpow Δ (-76 * ε)) * Real.rpow Δ (-111 * ε) * K_energy_uniform := h_denom_upper
        _ = 8 * C_common * K_pack_plane * K_extra * K_energy_uniform * Real.rpow Δ (-187 * ε) := h_denom_eq
    have h_num_pos : 0 < 2 * Real.rpow Δ (-2 * s + 23 * ε) := by
      have h : 0 < Real.rpow Δ (-2 * s + 23 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      positivity
    have h7 : (2 * Real.rpow Δ (-2 * s + 23 * ε)) /
        (8 * C_common * C_P' * C_T' * K_energy_uniform) ≥
        (2 * Real.rpow Δ (-2 * s + 23 * ε)) /
        (8 * C_common * K_pack_plane * K_extra * K_energy_uniform * Real.rpow Δ (-187 * ε)) := by
      exact div_le_div_of_nonneg_left h_num_pos.le (by positivity) h_denom_le
    rw [h_final] at h7
    exact le_trans h7 h6

  let S : Finset CoarseTube := T_Δ.filter (fun T => ∃ Q hQ, T ∈ D Q hQ)
  have hS_mem : ∀ T, T ∈ S ↔ T ∈ T_Δ ∧ ∃ Q hQ, T ∈ D Q hQ := by
    intro T
    simp [S, Finset.mem_filter] <;> tauto
  have hS_card : (S.card : ℝ) ≥ c * Real.rpow Δ (-2 * s + 210 * ε) := by
    calc (S.card : ℝ)
      ≥ ((P.biUnion Tp).card : ℝ) := hUnion_card
    _ ≥ M_val * Δ^(-s) / (8 * C_common * C_P' * C_T' * K_energy_eff) := h_global
    _ ≥ c * Real.rpow Δ (-2 * s + 210 * ε) := h_main_lower
  exact ⟨S, hS_mem, hS_card⟩

/-- Integration bridge: from A4_Output_v2 data + numerical/geometry hypotheses
    to TwoSBoundWithLower at -2s+210ε.

    Extracts per-square data from A4, converts Qset physical ball-growth to
    a center IsDeltaSSet via ball_growth_to_sset, and calls mkTwoSBound_weak.

    Key parameter choices:
    - C_Qimg = plane_packing_constant · Δ^{-20ε} (from ball_growth_to_sset)
    - K_extra = plane_packing_constant · Δ^{6ε} (so C_Qimg ≤ K_extra · Δ^{-26ε})

    Caller must supply:
    - hC_near: 10Δ near-center property for C_Q_pi tubes
    - hRKP, hK_large_weak, h_absorb_K_extra: numerical conditions
    - hQset_nonempty
-/
lemma h_2s_bound_integration
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
    (hQset_nonempty : a4.Qset.Nonempty)
    -- Per-square C_Q_pi cardinality bound at -29ε (matches A4 uniform bound)
    (hC_Q_pi_card_upper : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset),
        (a4.perSquare Q hQ).C_Q_pi.card ≤ Real.rpow Δ (-s - 29 * ε))
    -- Near-center geometry (must be proved from fine tube assignment)
    (hC_near : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset) (T : CoarseTube),
        T ∈ (a4.perSquare Q hQ).C_Q_pi →
        squareCenter Δ Q ∈ Metric.cthickening (10 * Δ) (T.1 : Set EuclideanPlane))
    -- Numerical conditions
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
  classical

  let C_Qimg : ℝ := (MainAppendix.plane_packing_constant : ℝ) * Real.rpow Δ (-20 * ε)
  have hC_Qimg_pos : 0 < C_Qimg := by
    dsimp only [C_Qimg]
    have h1 : 0 < (MainAppendix.plane_packing_constant : ℝ) := by
      exact_mod_cast MainAppendix.plane_packing_constant_pos
    exact mul_pos h1 (Real.rpow_pos_of_pos hΔ_pos _)

  let K_extra : ℝ := (MainAppendix.plane_packing_constant : ℝ) * Real.rpow Δ (6 * ε)
  have hK_extra_pos : 0 < K_extra := by
    dsimp only [K_extra]
    have h1 : 0 < (MainAppendix.plane_packing_constant : ℝ) := by
      exact_mod_cast MainAppendix.plane_packing_constant_pos
    exact mul_pos h1 (Real.rpow_pos_of_pos hΔ_pos _)

  have hC_Qimg_le : C_Qimg ≤ K_extra * Real.rpow Δ (-26 * ε) := by
    dsimp only [C_Qimg, K_extra]
    have h_exp : Real.rpow Δ (6 * ε) * Real.rpow Δ (-26 * ε) = Real.rpow Δ (-20 * ε) := by
      exact h_rpow_eq hΔ_pos (6 * ε) (-26 * ε) (-20 * ε) (by ring)
    have h_goal : (MainAppendix.plane_packing_constant : ℝ) * Real.rpow Δ (6 * ε) * Real.rpow Δ (-26 * ε) =
        (MainAppendix.plane_packing_constant : ℝ) * Real.rpow Δ (-20 * ε) := by
      have h : (MainAppendix.plane_packing_constant : ℝ) * Real.rpow Δ (6 * ε) * Real.rpow Δ (-26 * ε) =
          (MainAppendix.plane_packing_constant : ℝ) * (Real.rpow Δ (6 * ε) * Real.rpow Δ (-26 * ε)) := by ring
      rw [h, h_exp] <;> ring
    exact h_goal.symm.le

  -- Step 1: Extract per-square properties from A4 data
  let C : (Q : CoarseSquare Δ) → Q ∈ a4.Qset → Finset CoarseTube :=
    fun Q hQ => (a4.perSquare Q hQ).C_Q_pi

  have hC_sset : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset),
      IsDeltaSSet Δ s (Real.rpow Δ (-59 * ε)) (C Q hQ : Set CoarseTube) := by
    intro Q hQ
    exact (a4.perSquare Q hQ).hC_Q_pi_sset

  have hC_card_upper : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset),
      (C Q hQ).card ≤ Real.rpow Δ (-s - 29 * ε) := hC_Q_pi_card_upper

  have hC_sep : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset),
      SeparatedAt Δ (C Q hQ : Set CoarseTube) := by
    intro Q hQ
    have h1 : SeparatedAt Δ ((a4.perSquare Q hQ).base.C_Q : Set CoarseTube) :=
      (a4.perSquare Q hQ).base.hC_Q_separated
    exact h1.mono (a4.perSquare Q hQ).hC_Q_pi_sub

  have hC_sub_TΔ : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset),
      (C Q hQ : Set CoarseTube) ⊆ (C_global_A2 : Set CoarseTube) :=
    hC_Q_pi_sub

  -- Step 2: Convert Qset physical ball-growth to center IsDeltaSSet
  have hQset_center_sep : Set.Pairwise (a4.Qset.image (squareCenter Δ) : Set EuclideanPlane)
      (fun p p' => Δ ≤ dist p p') := by
    intro p hp p' hp' hne
    rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
    rcases Finset.mem_image.mp hp' with ⟨R, hR, rfl⟩
    have hQR : Q ≠ R := by
      intro h; apply hne; rw [h]
    exact AppendixA3.square_center_dist_ge hΔ_pos hQR

  have h_ball_equiv : ∀ (c : EuclideanPlane) (r : ℝ), Δ ≤ r →
      ((a4.Qset.image (squareCenter Δ)).filter (fun q => dist q c ≤ r)).card ≤
        (Real.rpow Δ (-20 * ε) * r^u * (a4.Qset.image (squareCenter Δ)).card : ℝ) := by
    intro c r hr
    have h_inj : Function.Injective (squareCenter Δ) := squareCenter_injective hΔ_pos
    have h_filter_eq : (a4.Qset.image (squareCenter Δ)).filter (fun q => dist q c ≤ r) =
        (a4.Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).image (squareCenter Δ) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨Q, hQ, rfl⟩, hdist⟩
        exact ⟨Q, ⟨hQ, hdist⟩, rfl⟩
      · rintro ⟨Q, ⟨hQ, hdist⟩, rfl⟩
        exact ⟨⟨Q, hQ, rfl⟩, hdist⟩
    rw [h_filter_eq]
    have h_card : ((a4.Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).image (squareCenter Δ)).card =
        (a4.Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card := by
      rw [Finset.card_image_of_injective _ h_inj]
    rw [h_card]
    have h_card2 : (a4.Qset.image (squareCenter Δ)).card = a4.Qset.card := by
      rw [Finset.card_image_of_injective _ h_inj]
    rw [h_card2]
    exact a4.hQset_phys_growth c r hr

  rcases ball_growth_to_sset hΔ_pos (Real.rpow_pos_of_pos hΔ_pos _) (by linarith)
      hQset_nonempty hQset_center_sep h_ball_equiv with
    ⟨C'_sset, hC'_sset_pos, hC'_sset_eq, hQset_center_sset⟩

  have hC'_sset_eq2 : C'_sset = C_Qimg := by
    dsimp only [C_Qimg]
    rw [hC'_sset_eq]
    <;> exact mul_comm _ _

  rw [hC'_sset_eq2] at hQset_center_sset

  -- Step 3: Call mkTwoSBound_weak
  exact mkTwoSBound_weak
    hΔ_pos hΔ_lt_half hδ_pos hδ_le_Δ
    hs hs1 hst ht2 hε_pos
    C_Qimg hC_Qimg_pos K_extra hK_extra_pos hC_Qimg_le
    a4.Qset C hC_sset hC_card_upper hC_sep hC_near
    C_global_A2 hC_sub_TΔ
    hCenter_bound hDist_le_3
    hQset_center_sset hQset_card_upper
    hRKP hK_large_weak (by norm_num) h_absorb_K_extra

end DirecretisedFurstenbergEstimate.AppendixA5
