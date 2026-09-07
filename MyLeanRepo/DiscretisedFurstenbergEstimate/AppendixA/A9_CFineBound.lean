module

/-
  A9 fine tube rescalable constant bound.

  Extracts the ~200-line proof of `16 * C_fine_resc ≤ Δ^{-501ε}` from
  A9_PerSquareBuild to reduce compilation unit size.

  Given the base packing constants K_pack, K_Q, M with their A2 bounds,
  and the fine absorption hypothesis, proves that the rescaled fine-tube
  S-set constant C_fine_resc satisfies the required upper bound.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate

open LemmaE
open DiscretisedFurstenbergEstimate.CoveringUtils

namespace AppendixA

/-- Bound on the rescaled fine-tube S-set constant.

    Given A2 base constants K_pack, K_Q, M with their standard bounds,
    proves `16 * C_fine_resc ≤ Δ^{-501ε}`.

    C_fine = max(1, K_pack * δ^{-ε}) * K_Q * Pconst * M * Pconst * Δ^{s-36ε}
    C_fine_resc = C_fine * 20^s * 1048576 * 256 * (3/2)^s * 256 * 16^s * Δ^s

    The proof absorbs all geometric constants into ε-dependent powers. -/
lemma A9_cfine_resc_bound
    (Δ δ s ε : ℝ)
    (hΔ_pos : 0 < Δ)
    (hΔ_small : 7 * Δ ≤ 1)
    (hδ_eq : δ = Δ ^ 2)
    (hs_nonneg : 0 ≤ s)
    (hs1 : s < 1)
    (hε_pos : 0 < ε)
    (K_pack K_Q M : ℝ)
    (hKpack_le : K_pack ≤ Real.rpow Δ (-2 * ε) / 6)
    (hKpack_pos : 0 < K_pack)
    (hKQ_pos : 0 < K_Q)
    (hKQ_le : K_Q ≤ Real.rpow Δ (-ε))
    (hM_pos : 0 < M)
    (hM_le : M ≤ 2 * Real.rpow Δ (-2 * s - ε))
    (hΔ_fine_absorb : (16 * (MainAppendix.affineLine_packing_constant : ℝ)^2 *
        (2 * 20 * 1048576 * 256 * (3 / 2 : ℝ) * 256 * 16)) ≤ Real.rpow Δ (-453 * ε))
    (hPconst_pos : 0 < (MainAppendix.affineLine_packing_constant : ℝ)) :
    let Pconst := (MainAppendix.affineLine_packing_constant : ℝ)
    let C_fine : ℝ :=
      (max 1 (K_pack * Real.rpow δ (-ε)) * K_Q * Pconst) * M * Pconst *
        Real.rpow Δ (s - 40 * ε)
    let C_fine_resc : ℝ :=
      C_fine * (20 : ℝ)^s * 1048576 * 256 * (3 / 2 : ℝ)^s * 256 * (16 : ℝ)^s * Δ^s
    16 * C_fine_resc ≤ Real.rpow Δ (-501 * ε) := by
  let Pconst := (MainAppendix.affineLine_packing_constant : ℝ)
  let C_fine : ℝ :=
    (max 1 (K_pack * Real.rpow δ (-ε)) * K_Q * Pconst) * M * Pconst *
      Real.rpow Δ (s - 40 * ε)
  let C_fine_resc : ℝ :=
    C_fine * (20 : ℝ)^s * 1048576 * 256 * (3 / 2 : ℝ)^s * 256 * (16 : ℝ)^s * Δ^s
  have hPconst_pos : 0 < Pconst := hPconst_pos
  have h_pos_rpow : ∀ (x : ℝ), 0 < Real.rpow Δ x := fun x => Real.rpow_pos_of_pos hΔ_pos x
  have hδ_neg : Real.rpow δ (-ε) = Real.rpow Δ (-2 * ε) := by
    rw [hδ_eq]
    have h3 : (Δ ^ 2 : ℝ) = Real.rpow Δ (2 : ℝ) := by
      have h4 : Real.rpow Δ (2 : ℝ) = (Δ ^ 2 : ℝ) := by simp
      exact h4.symm
    rw [h3]
    have h6 : Real.rpow (Real.rpow Δ (2 : ℝ)) (-ε) = Real.rpow Δ ((2 : ℝ) * (-ε)) :=
      (Real.rpow_mul (show 0 ≤ Δ from by linarith) (2 : ℝ) (-ε)).symm
    rw [h6] <;> ring_nf
  have h_rpow2 : Real.rpow Δ (-2 * ε) * Real.rpow Δ (-2 * ε) = Real.rpow Δ (-4 * ε) := by
    have h_sum : (-2 * ε) + (-2 * ε) = -4 * ε := by ring
    have h := Real.rpow_add hΔ_pos (-2 * ε) (-2 * ε)
    rw [h_sum] at h
    exact h.symm
  have h_pos_rpow2 : 0 < Real.rpow Δ (-2 * ε) := h_pos_rpow (-2 * ε)
  have h1 : max 1 (K_pack * Real.rpow δ (-ε)) ≤ Real.rpow Δ (-4 * ε) := by
    rw [hδ_neg]
    have h2 : K_pack * Real.rpow Δ (-2 * ε) ≤ Real.rpow Δ (-4 * ε) / 6 := by
      calc K_pack * Real.rpow Δ (-2 * ε)
        ≤ (Real.rpow Δ (-2 * ε) / 6) * Real.rpow Δ (-2 * ε) :=
          mul_le_mul_of_nonneg_right hKpack_le h_pos_rpow2.le
      _ = (Real.rpow Δ (-2 * ε) * Real.rpow Δ (-2 * ε)) / 6 := by ring
      _ = Real.rpow Δ (-4 * ε) / 6 := by rw [h_rpow2]
    have h4 : 1 ≤ Real.rpow Δ (-4 * ε) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hΔ_pos (by linarith) (by linarith)
    have h6 : max 1 (K_pack * Real.rpow Δ (-2 * ε)) ≤ max 1 (Real.rpow Δ (-4 * ε) / 6) := by
      apply max_le_max
      · linarith
      · exact h2
    have h7 : max 1 (Real.rpow Δ (-4 * ε) / 6) ≤ Real.rpow Δ (-4 * ε) := by
      by_cases h8 : Real.rpow Δ (-4 * ε) / 6 ≥ 1
      · rw [max_eq_right h8] <;> linarith
      · rw [max_eq_left (by linarith)] <;> linarith
    exact le_trans h6 h7
  have h20 : (20 : ℝ)^s ≤ 20 := by
    have h : (20 : ℝ)^s ≤ (20 : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (20 : ℝ)^(1 : ℝ) = 20 := by simp
    rw [h2] at h; exact h
  have h32 : (3 / 2 : ℝ)^s ≤ 3 / 2 := by
    have h : (3 / 2 : ℝ)^s ≤ (3 / 2 : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (3 / 2 : ℝ)^(1 : ℝ) = 3 / 2 := by simp
    rw [h2] at h; exact h
  have h16 : (16 : ℝ)^s ≤ 16 := by
    have h : (16 : ℝ)^s ≤ (16 : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (16 : ℝ)^(1 : ℝ) = 16 := by simp
    rw [h2] at h; exact h
  have h_rpow5 : ∀ (a b c d e : ℝ), Real.rpow Δ a * Real.rpow Δ b * Real.rpow Δ c * Real.rpow Δ d * Real.rpow Δ e =
      Real.rpow Δ (a + b + c + d + e) := by
    intro a b c d e
    have h_step1 : Real.rpow Δ a * Real.rpow Δ b = Real.rpow Δ (a + b) :=
      (Real.rpow_add hΔ_pos a b).symm
    have h_step2 : Real.rpow Δ (a + b) * Real.rpow Δ c = Real.rpow Δ (a + b + c) :=
      (Real.rpow_add hΔ_pos (a + b) c).symm
    have h_step3 : Real.rpow Δ (a + b + c) * Real.rpow Δ d = Real.rpow Δ (a + b + c + d) :=
      (Real.rpow_add hΔ_pos (a + b + c) d).symm
    have h_step4 : Real.rpow Δ (a + b + c + d) * Real.rpow Δ e = Real.rpow Δ (a + b + c + d + e) :=
      (Real.rpow_add hΔ_pos (a + b + c + d) e).symm
    calc Real.rpow Δ a * Real.rpow Δ b * Real.rpow Δ c * Real.rpow Δ d * Real.rpow Δ e
      = (Real.rpow Δ a * Real.rpow Δ b) * Real.rpow Δ c * Real.rpow Δ d * Real.rpow Δ e := by ring
    _ = Real.rpow Δ (a + b) * Real.rpow Δ c * Real.rpow Δ d * Real.rpow Δ e := by rw [h_step1]
    _ = Real.rpow Δ (a + b + c) * Real.rpow Δ d * Real.rpow Δ e := by rw [h_step2]
    _ = Real.rpow Δ (a + b + c + d) * Real.rpow Δ e := by rw [h_step3]
    _ = Real.rpow Δ (a + b + c + d + e) := by rw [h_step4]
  let R4_no_s := Real.rpow Δ (-4 * ε) * Real.rpow Δ (-ε) * Real.rpow Δ (-2 * s - ε) * Real.rpow Δ (s - 40 * ε)
  let K_const := (2 * 20 * 1048576 * 256 * (3 / 2 : ℝ) * 256 * 16)
  have hA : max 1 (K_pack * Real.rpow δ (-ε)) ≤ Real.rpow Δ (-4 * ε) := h1
  have h11 : max 1 (K_pack * Real.rpow δ (-ε)) * K_Q ≤ Real.rpow Δ (-4 * ε) * Real.rpow Δ (-ε) := by
    calc max 1 (K_pack * Real.rpow δ (-ε)) * K_Q
      ≤ Real.rpow Δ (-4 * ε) * K_Q := mul_le_mul_of_nonneg_right hA hKQ_pos.le
    _ ≤ Real.rpow Δ (-4 * ε) * Real.rpow Δ (-ε) := mul_le_mul_of_nonneg_left hKQ_le (h_pos_rpow (-4 * ε)).le
  have h12 : max 1 (K_pack * Real.rpow δ (-ε)) * K_Q * M ≤
      Real.rpow Δ (-4 * ε) * Real.rpow Δ (-ε) * (2 * Real.rpow Δ (-2 * s - ε)) := by
    calc max 1 (K_pack * Real.rpow δ (-ε)) * K_Q * M
      ≤ (Real.rpow Δ (-4 * ε) * Real.rpow Δ (-ε)) * M := mul_le_mul_of_nonneg_right h11 hM_pos.le
    _ ≤ (Real.rpow Δ (-4 * ε) * Real.rpow Δ (-ε)) * (2 * Real.rpow Δ (-2 * s - ε)) :=
      have h_mult_nonneg : 0 ≤ Real.rpow Δ (-4 * ε) * Real.rpow Δ (-ε) :=
        mul_nonneg (Real.rpow_nonneg hΔ_pos.le _) (Real.rpow_nonneg hΔ_pos.le _)
      mul_le_mul_of_nonneg_left hM_le h_mult_nonneg
  have h_posP : 0 < Pconst * Pconst * Real.rpow Δ (s - 40 * ε) := by
    exact mul_pos (mul_pos hPconst_pos hPconst_pos) (h_pos_rpow (s - 40 * ε))
  have hC_fine_bounded : C_fine ≤ 2 * Pconst^2 * R4_no_s := by
    dsimp only [C_fine]
    calc max 1 (K_pack * Real.rpow δ (-ε)) * K_Q * Pconst * M * Pconst * Real.rpow Δ (s - 40 * ε)
      = (max 1 (K_pack * Real.rpow δ (-ε)) * K_Q * M) * (Pconst * Pconst * Real.rpow Δ (s - 40 * ε)) := by ring
    _ ≤ (Real.rpow Δ (-4 * ε) * Real.rpow Δ (-ε) * (2 * Real.rpow Δ (-2 * s - ε))) * (Pconst * Pconst * Real.rpow Δ (s - 40 * ε)) := by
      exact mul_le_mul_of_nonneg_right h12 h_posP.le
    _ = 2 * Pconst^2 * R4_no_s := by
      simp only [R4_no_s] <;> ring
  let S := (20 : ℝ)^s * 1048576 * 256 * (3 / 2 : ℝ)^s * 256 * (16 : ℝ)^s
  let S' := (20 : ℝ) * 1048576 * 256 * (3 / 2 : ℝ) * 256 * (16 : ℝ)
  have hS : S ≤ S' := by
    simp only [S, S']
    have h_pos_const : 0 < (1048576 : ℝ) * (256 : ℝ) * (256 : ℝ) := by norm_num
    have h_pos1 : 0 ≤ (3 / 2 : ℝ)^s * (16 : ℝ)^s := by positivity
    have h_step1 : (20 : ℝ)^s * ((3 / 2 : ℝ)^s * (16 : ℝ)^s) ≤ (20 : ℝ) * ((3 / 2 : ℝ)^s * (16 : ℝ)^s) :=
      mul_le_mul_of_nonneg_right h20 h_pos1
    have h_pos2 : 0 ≤ (16 : ℝ)^s := by positivity
    have h32' : (3 / 2 : ℝ)^s * (16 : ℝ)^s ≤ (3 / 2 : ℝ) * (16 : ℝ)^s :=
      mul_le_mul_of_nonneg_right h32 h_pos2
    have h_pos2' : 0 ≤ (20 : ℝ) := by positivity
    have h_step2 : (20 : ℝ) * ((3 / 2 : ℝ)^s * (16 : ℝ)^s) ≤ (20 : ℝ) * ((3 / 2 : ℝ) * (16 : ℝ)^s) :=
      mul_le_mul_of_nonneg_left h32' h_pos2'
    have h_pos3 : 0 ≤ (3 / 2 : ℝ) := by positivity
    have h16' : (3 / 2 : ℝ) * (16 : ℝ)^s ≤ (3 / 2 : ℝ) * (16 : ℝ) :=
      mul_le_mul_of_nonneg_left h16 h_pos3
    have h_pos3' : 0 ≤ (20 : ℝ) := by positivity
    have h_step3 : (20 : ℝ) * ((3 / 2 : ℝ) * (16 : ℝ)^s) ≤ (20 : ℝ) * ((3 / 2 : ℝ) * (16 : ℝ)) :=
      mul_le_mul_of_nonneg_left h16' h_pos3'
    have h_eq1 : (20 : ℝ)^s * 1048576 * 256 * (3 / 2 : ℝ)^s * 256 * (16 : ℝ)^s =
        ((20 : ℝ)^s * ((3 / 2 : ℝ)^s * (16 : ℝ)^s)) * (1048576 * 256 * 256) := by ring
    have h_eq2 : (20 : ℝ) * 1048576 * 256 * (3 / 2 : ℝ) * 256 * (16 : ℝ) =
        ((20 : ℝ) * ((3 / 2 : ℝ) * (16 : ℝ))) * (1048576 * 256 * 256) := by ring
    rw [h_eq1, h_eq2]
    exact mul_le_mul_of_nonneg_right (le_trans h_step1 (le_trans h_step2 h_step3)) h_pos_const.le
  have h_rpow_sum : R4_no_s * Real.rpow Δ s = Real.rpow Δ (-46 * ε) := by
    simp only [R4_no_s]
    have h := h_rpow5 (-4 * ε) (-ε) (-2 * s - ε) (s - 40 * ε) s
    have h_total : (-4 * ε) + (-ε) + (-2 * s - ε) + (s - 40 * ε) + s = -46 * ε := by ring
    rw [h_total] at h
    exact h
  have h_eq_resc : C_fine_resc = C_fine * S * Real.rpow Δ s := by
    dsimp only [C_fine_resc, S]
    have hpow : (Δ ^ s) = Real.rpow Δ s := by simp
    rw [hpow] <;> ring
  have h_bound42 : C_fine_resc ≤ Pconst^2 * K_const * Real.rpow Δ (-46 * ε) := by
    rw [h_eq_resc]
    have h_posS : 0 < S := by positivity
    have hC_fine_bounded_S : C_fine * S ≤ (2 * Pconst^2 * R4_no_s) * S :=
      mul_le_mul_of_nonneg_right hC_fine_bounded h_posS.le
    have h_step1 : C_fine * S * Real.rpow Δ s ≤ (2 * Pconst^2 * R4_no_s) * S * Real.rpow Δ s :=
      mul_le_mul_of_nonneg_right hC_fine_bounded_S (h_pos_rpow s).le
    have hR : 0 < R4_no_s := by
      simp only [R4_no_s]
      have h1 : 0 < Real.rpow Δ (-4 * ε) * Real.rpow Δ (-ε) :=
        mul_pos (h_pos_rpow (-4 * ε)) (h_pos_rpow (-ε))
      have h2 : 0 < (Real.rpow Δ (-4 * ε) * Real.rpow Δ (-ε)) * Real.rpow Δ (-2 * s - ε) :=
        mul_pos h1 (h_pos_rpow (-2 * s - ε))
      exact mul_pos h2 (h_pos_rpow (s - 40 * ε))
    have hP2 : 0 < Pconst^2 := by positivity
    have h2P : 0 < (2 : ℝ) * Pconst^2 := mul_pos (by norm_num) hP2
    have h_pos2 : 0 < 2 * Pconst^2 * R4_no_s := mul_pos h2P hR
    have h_step2a : (2 * Pconst^2 * R4_no_s) * S ≤ (2 * Pconst^2 * R4_no_s) * S' :=
      mul_le_mul_of_nonneg_left hS h_pos2.le
    have h_step2 : (2 * Pconst^2 * R4_no_s) * S * Real.rpow Δ s ≤ (2 * Pconst^2 * R4_no_s) * S' * Real.rpow Δ s :=
      mul_le_mul_of_nonneg_right h_step2a (h_pos_rpow s).le
    have h_step3 : (2 * Pconst^2 * R4_no_s) * S' * Real.rpow Δ s = Pconst^2 * K_const * (R4_no_s * Real.rpow Δ s) := by
      simp only [K_const, S'] <;> ring
    have h_step4 : Pconst^2 * K_const * (R4_no_s * Real.rpow Δ s) = Pconst^2 * K_const * Real.rpow Δ (-46 * ε) := by
      rw [h_rpow_sum]
    rw [h_step3, h_step4] at h_step2
    exact le_trans h_step1 h_step2
  have h_weaken : Real.rpow Δ (-46 * ε) ≤ Real.rpow Δ (-48 * ε) := by
    have hΔ_lt_one : Δ < 1 := by linarith [hΔ_small]
    have hlog : Real.log Δ < 0 := Real.log_neg hΔ_pos hΔ_lt_one
    have h_exp : (-46 * ε) ≥ (-48 * ε) := by linarith
    have h_pos1 : 0 < Real.rpow Δ (-46 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_pos2 : 0 < Real.rpow Δ (-48 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h : Real.log (Real.rpow Δ (-46 * ε)) ≤ Real.log (Real.rpow Δ (-48 * ε)) := by
      have hlog1 : Real.log (Real.rpow Δ (-46 * ε)) = (-46 * ε) * Real.log Δ :=
        Real.log_rpow hΔ_pos (-46 * ε)
      have hlog2 : Real.log (Real.rpow Δ (-48 * ε)) = (-48 * ε) * Real.log Δ :=
        Real.log_rpow hΔ_pos (-48 * ε)
      rw [hlog1, hlog2]
      have hlog_neg : Real.log Δ < 0 := hlog
      nlinarith
    exact (Real.log_le_log_iff h_pos1 h_pos2).mp h
  have h_bound : C_fine_resc ≤ Pconst^2 * K_const * Real.rpow Δ (-48 * ε) := by
    calc C_fine_resc
      ≤ Pconst^2 * K_const * Real.rpow Δ (-46 * ε) := h_bound42
    _ ≤ Pconst^2 * K_const * Real.rpow Δ (-48 * ε) := by gcongr
  have h9 : 16 * C_fine_resc ≤ (16 * Pconst^2 * K_const) * Real.rpow Δ (-48 * ε) := by
    have h_step1 : 16 * C_fine_resc ≤ 16 * (Pconst^2 * K_const * Real.rpow Δ (-48 * ε)) :=
      mul_le_mul_of_nonneg_left h_bound (by positivity)
    have h_step2 : 16 * (Pconst^2 * K_const * Real.rpow Δ (-48 * ε)) = (16 * Pconst^2 * K_const) * Real.rpow Δ (-48 * ε) := by ring
    rw [h_step2] at h_step1
    exact h_step1
  have h11 : Real.rpow Δ (-453 * ε) * Real.rpow Δ (-48 * ε) = Real.rpow Δ (-501 * ε) := by
    have h_sum : (-453 * ε) + (-48 * ε) = -501 * ε := by ring
    have h : Real.rpow Δ ((-453 * ε) + (-48 * ε)) = Real.rpow Δ (-453 * ε) * Real.rpow Δ (-48 * ε) :=
      Real.rpow_add hΔ_pos (-453 * ε) (-48 * ε)
    rw [h_sum] at h
    exact h.symm
  have h_pos_rpow42 : 0 < Real.rpow Δ (-48 * ε) := h_pos_rpow (-48 * ε)
  have h12 : (16 * Pconst^2 * K_const) * Real.rpow Δ (-48 * ε) ≤
      Real.rpow Δ (-453 * ε) * Real.rpow Δ (-48 * ε) :=
    mul_le_mul_of_nonneg_right hΔ_fine_absorb h_pos_rpow42.le
  have h10 : (16 * Pconst^2 * K_const) * Real.rpow Δ (-48 * ε) ≤ Real.rpow Δ (-501 * ε) := by
    rw [h11] at *
    <;> exact h12
  exact le_trans h9 h10

end AppendixA
end DirecretisedFurstenbergEstimate
