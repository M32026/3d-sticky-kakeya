import MyLeanRepo.Kakeya.Assouad.WZ1.CubeCountGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.CrossPerturbation
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Pairwise tube intersection volume bound via angle separation
-/

noncomputable section

open Kakeya.Assouad Kakeya.Streamlined Metric
open scoped Matrix
open MeasureTheory

namespace Kakeya.Assouad

/-- `wz1Cross u u = 0`. -/
lemma wz1Cross_self (u : Point3) : wz1Cross u u = 0 := by
  have h : (u : Fin 3 → ℝ) ⨯₃ (u : Fin 3 → ℝ) = 0 := by
    simpa using Matrix.crossProduct_self u
  have h' : wz1Cross u u = WithLp.toLp 2 (0 : Fin 3 → ℝ) := by
    rw [wz1Cross, h]
  rw [h']
  <;> simp

lemma wz1Cross_anticomm (u v : Point3) : wz1Cross u v = -wz1Cross v u := by
  have h' : -((u : Fin 3 → ℝ) ⨯₃ (v : Fin 3 → ℝ)) = (v : Fin 3 → ℝ) ⨯₃ (u : Fin 3 → ℝ) :=
    cross_anticomm u v
  have h : (u : Fin 3 → ℝ) ⨯₃ (v : Fin 3 → ℝ) = -((v : Fin 3 → ℝ) ⨯₃ (u : Fin 3 → ℝ)) := by
    calc
      (u : Fin 3 → ℝ) ⨯₃ (v : Fin 3 → ℝ)
        = -(-((u : Fin 3 → ℝ) ⨯₃ (v : Fin 3 → ℝ))) := by simp
      _ = -((v : Fin 3 → ℝ) ⨯₃ (u : Fin 3 → ℝ)) := by rw [h']
  have h1 : wz1Cross u v = WithLp.toLp 2 ((u : Fin 3 → ℝ) ⨯₃ (v : Fin 3 → ℝ)) := by rfl
  rw [h1, h]
  have h2 : WithLp.toLp 2 (-((v : Fin 3 → ℝ) ⨯₃ (u : Fin 3 → ℝ))) =
      -WithLp.toLp 2 ((v : Fin 3 → ℝ) ⨯₃ (u : Fin 3 → ℝ)) := by
    exact WithLp.toLp_neg _ _
  rw [h2] <;> rfl

/--
Geometric angle lemma: separated intersection points imply angle between directions.
-/
lemma angle_from_separated_intersections
    {rho tau d alpha : ℝ}
    (hrho_pos : 0 < rho)
    (htau_pos : 0 < tau)
    (halpha_pos : 0 < alpha)
    (hd_pos : 0 < d)
    (u v_j v_k : Point3)
    (hu_unit : ‖u‖ = 1)
    (hvj_unit : ‖v_j‖ = 1)
    (hvk_unit : ‖v_k‖ = 1)
    (p_j p_k x : Point3)
    (e_j e_k : Point3)
    (s_j s_k : ℝ)
    (h_sep : ‖p_k - p_j - d • u‖ ≤ 2 * rho)
    (hx_j : x = p_j + s_j • v_j + e_j)
    (hx_k : x = p_k + s_k • v_k + e_k)
    (hej_norm : ‖e_j‖ ≤ 2 * rho)
    (hek_norm : ‖e_k‖ ≤ 2 * rho)
    (hsj_bound : |s_j| ≤ tau)
    (hsk_bound : |s_k| ≤ tau)
    (h_trans_j : ‖wz1Cross u v_j‖ ≥ alpha)
    (h_trans_k : ‖wz1Cross u v_k‖ ≥ alpha)
    (h_large : d * alpha ≥ 12 * rho) :
    ‖wz1Cross v_j v_k‖ ≥ d * alpha / (2 * tau) := by
  have h_vec_eq : p_j + s_j • v_j + e_j = p_k + s_k • v_k + e_k := by
    rw [←hx_j, hx_k]
  have h_eq1 : s_j • v_j - s_k • v_k = (p_k - p_j) + (e_k - e_j) := by
    calc
      s_j • v_j - s_k • v_k
        = (p_j + s_j • v_j + e_j) - (p_k + s_k • v_k + e_k) + (p_k - p_j) + (e_k - e_j) := by abel
      _ = (p_k - p_j) + (e_k - e_j) := by rw [h_vec_eq] <;> abel
  set w : Point3 := p_k - p_j - d • u with hw_def
  have hw_norm : ‖w‖ ≤ 2 * rho := h_sep
  have h_pk_pj : p_k - p_j = d • u + w := by
    simp [hw_def] <;> abel
  set E : Point3 := w + (e_k - e_j) with hE_def
  have h_main_eq : s_j • v_j - s_k • v_k = d • u + E := by
    rw [h_eq1, h_pk_pj, hE_def] <;> abel
  have hE_norm : ‖E‖ ≤ 6 * rho := by
    calc
      ‖E‖ ≤ ‖w‖ + ‖e_k - e_j‖ := by
        simpa [hE_def] using norm_add_le _ _
      _ ≤ ‖w‖ + ‖e_k‖ + ‖e_j‖ := by
        have h : ‖e_k - e_j‖ ≤ ‖e_k‖ + ‖e_j‖ := norm_sub_le _ _
        linarith
      _ ≤ 2 * rho + 2 * rho + 2 * rho := by gcongr <;> linarith
      _ = 6 * rho := by ring
  -- Apply wz1Cross v_j to both sides
  have h_cross_eq : wz1Cross v_j (s_j • v_j - s_k • v_k) = wz1Cross v_j (d • u + E) := by
    rw [h_main_eq]
  have h_left : wz1Cross v_j (s_j • v_j - s_k • v_k) = -s_k • wz1Cross v_j v_k := by
    have h1 : wz1Cross v_j (s_j • v_j - s_k • v_k) =
        wz1Cross v_j (s_j • v_j) - wz1Cross v_j (s_k • v_k) := by
      have h_sub : s_j • v_j - s_k • v_k = s_j • v_j + -(s_k • v_k) := by
        exact sub_eq_add_neg (s_j • v_j) (s_k • v_k)
      rw [h_sub]
      have h_add : wz1Cross v_j (s_j • v_j + -(s_k • v_k)) =
          wz1Cross v_j (s_j • v_j) + wz1Cross v_j (-(s_k • v_k)) :=
        wz1Cross_add_right v_j (s_j • v_j) (-(s_k • v_k))
      rw [h_add]
      have h_neg : wz1Cross v_j (-(s_k • v_k)) = -wz1Cross v_j (s_k • v_k) := by
        have h5 : -(s_k • v_k) = (-s_k) • v_k := by simp
        rw [h5]
        have h6 : wz1Cross v_j ((-s_k) • v_k) = (-s_k) • wz1Cross v_j v_k :=
          wz1Cross_smul_right (-s_k) v_j v_k
        rw [h6]
        have h7 : (-s_k) • wz1Cross v_j v_k = -(s_k • wz1Cross v_j v_k) := by simp
        rw [h7]
        have h8 : s_k • wz1Cross v_j v_k = wz1Cross v_j (s_k • v_k) :=
          (wz1Cross_smul_right s_k v_j v_k).symm
        rw [h8]
      rw [h_neg] <;> abel
    rw [h1]
    have h2 : wz1Cross v_j (s_j • v_j) = s_j • wz1Cross v_j v_j := wz1Cross_smul_right s_j v_j v_j
    rw [h2, wz1Cross_self v_j]
    have h4 : wz1Cross v_j (s_k • v_k) = s_k • wz1Cross v_j v_k := wz1Cross_smul_right s_k v_j v_k
    rw [h4] <;> simp
  have h_right : wz1Cross v_j (d • u + E) =
      d • wz1Cross v_j u + wz1Cross v_j E := by
    have h_add : wz1Cross v_j (d • u + E) =
        wz1Cross v_j (d • u) + wz1Cross v_j E := wz1Cross_add_right v_j (d • u) E
    rw [h_add]
    have h_smul : wz1Cross v_j (d • u) = d • wz1Cross v_j u :=
      wz1Cross_smul_right d v_j u
    rw [h_smul]
  have h_eq2 : -s_k • wz1Cross v_j v_k = d • wz1Cross v_j u + wz1Cross v_j E := by
    rw [h_left, h_right] at h_cross_eq
    exact h_cross_eq
  have h_anticomm : wz1Cross v_j u = -wz1Cross u v_j := wz1Cross_anticomm v_j u
  rw [h_anticomm] at h_eq2
  have h_eq3 : -s_k • wz1Cross v_j v_k = -d • wz1Cross u v_j + wz1Cross v_j E := by
    simpa [smul_neg] using h_eq2
  have h_final : s_k • wz1Cross v_j v_k = d • wz1Cross u v_j - wz1Cross v_j E := by
    have h' : -(s_k • wz1Cross v_j v_k) = -(d • wz1Cross u v_j) + wz1Cross v_j E := by
      simpa [neg_smul] using h_eq3
    calc
      s_k • wz1Cross v_j v_k
        = -(-(s_k • wz1Cross v_j v_k)) := by simp
      _ = -(-(d • wz1Cross u v_j) + wz1Cross v_j E) := by rw [h']
      _ = d • wz1Cross u v_j - wz1Cross v_j E := by abel
  -- Norm inequalities
  have h_left_norm : ‖s_k • wz1Cross v_j v_k‖ = |s_k| * ‖wz1Cross v_j v_k‖ := by
    rw [norm_smul] <;> rfl
  have h_d_nonneg : 0 ≤ d := hd_pos.le
  have h_right_lower : ‖d • wz1Cross u v_j - wz1Cross v_j E‖ ≥
      d * ‖wz1Cross u v_j‖ - ‖wz1Cross v_j E‖ := by
    have h1 : ‖d • wz1Cross u v_j‖ = d * ‖wz1Cross u v_j‖ := by
      have h11 : ‖d • wz1Cross u v_j‖ = |d| * ‖wz1Cross u v_j‖ := norm_smul d (wz1Cross u v_j)
      rw [h11]
      have h12 : |d| = d := abs_of_nonneg h_d_nonneg
      rw [h12] <;> ring
    have h_tri1 : ‖d • wz1Cross u v_j‖ ≤ ‖d • wz1Cross u v_j - wz1Cross v_j E‖ + ‖wz1Cross v_j E‖ := by
      calc
        ‖d • wz1Cross u v_j‖
          = ‖(d • wz1Cross u v_j - wz1Cross v_j E) + wz1Cross v_j E‖ := by congr 1; abel
        _ ≤ ‖d • wz1Cross u v_j - wz1Cross v_j E‖ + ‖wz1Cross v_j E‖ := norm_add_le _ _
    linarith [h_tri1, h1]
  have h_cross_E_bound : ‖wz1Cross v_j E‖ ≤ 6 * rho := by
    have h : ‖wz1Cross v_j E‖ ≤ ‖v_j‖ * ‖E‖ := wz1Cross_norm_le v_j E
    rw [hvj_unit] at h
    linarith [hE_norm]
  have h_norm_eq : ‖s_k • wz1Cross v_j v_k‖ = ‖d • wz1Cross u v_j - wz1Cross v_j E‖ := by
    rw [h_final]
  have h_ineq : |s_k| * ‖wz1Cross v_j v_k‖ ≥ d * ‖wz1Cross u v_j‖ - 6 * rho := by
    calc
      |s_k| * ‖wz1Cross v_j v_k‖ = ‖s_k • wz1Cross v_j v_k‖ := h_left_norm.symm
      _ = ‖d • wz1Cross u v_j - wz1Cross v_j E‖ := h_norm_eq
      _ ≥ d * ‖wz1Cross u v_j‖ - ‖wz1Cross v_j E‖ := h_right_lower
      _ ≥ d * ‖wz1Cross u v_j‖ - 6 * rho := by gcongr
  have h_trans_lower : d * ‖wz1Cross u v_j‖ ≥ d * alpha := by
    gcongr <;> linarith
  have h_ineq2 : |s_k| * ‖wz1Cross v_j v_k‖ ≥ d * alpha - 6 * rho := by linarith
  have h_half : d * alpha - 6 * rho ≥ d * alpha / 2 := by linarith
  have h_ineq3 : |s_k| * ‖wz1Cross v_j v_k‖ ≥ d * alpha / 2 := by linarith
  have h_final_result : ‖wz1Cross v_j v_k‖ ≥ d * alpha / (2 * tau) := by
    have h_pos : 0 < tau := htau_pos
    have h6 : tau * ‖wz1Cross v_j v_k‖ ≥ |s_k| * ‖wz1Cross v_j v_k‖ := by
      gcongr <;> linarith
    have h7 : tau * ‖wz1Cross v_j v_k‖ ≥ d * alpha / 2 := by linarith
    calc
      ‖wz1Cross v_j v_k‖
        = (tau * ‖wz1Cross v_j v_k‖) / tau := by field_simp [h_pos.ne'] <;> ring
      _ ≥ (d * alpha / 2) / tau := by gcongr
      _ = d * alpha / (2 * tau) := by ring
  exact h_final_result

/--
Pairwise tube intersection volume bound.
-/
lemma pairwise_tube_intersection_volume
    {rho tau : ℝ}
    (hrho_pos : 0 < rho)
    (hrho_small : rho ≤ 1 / 1000)
    (htau_pos : 0 < tau)
    (T_j T_k : DeltaTube rho)
    (q : Point3)
    {c d : ℝ}
    (hc_pos : 0 < c)
    (hd_pos : 0 < d)
    (h_cross_lower : ‖wz1Cross T_j.direction T_k.direction‖ ≥ c * d / tau)
    (h_cross_large : c * d / tau ≥ 32 * rho) :
    volume (T_j.carrier ∩ T_k.carrier ∩ Metric.ball q (3 * tau)) ≤
      ENNReal.ofReal (16 * rho^3 * tau / (c * d)) := by
  have hcross : 32 * rho ≤ ‖wz1Cross T_j.direction T_k.direction‖ := by linarith
  have h_main : volume (T_j.carrier ∩ T_k.carrier) ≤
      ENNReal.ofReal (16 * rho^3 / ‖wz1Cross T_j.direction T_k.direction‖) :=
    tube_intersection_volume_cross_bound hrho_pos hrho_small T_j T_k hcross
  let S_int := T_j.carrier ∩ T_k.carrier
  let S_ball := T_j.carrier ∩ T_k.carrier ∩ Metric.ball q (3 * tau)
  have h_subset : S_ball ⊆ S_int := by
    intro x hx
    exact ⟨hx.1.1, hx.1.2⟩
  have h1 : volume S_ball ≤ volume S_int := measure_mono h_subset
  have h_pos_cd : 0 < c * d := mul_pos hc_pos hd_pos
  have h_bound : 16 * rho^3 / ‖wz1Cross T_j.direction T_k.direction‖ ≤
      16 * rho^3 * tau / (c * d) := by
    have h_cross_pos : 0 < ‖wz1Cross T_j.direction T_k.direction‖ := by
      have h : 0 < 32 * rho := by positivity
      exact h.trans_le hcross
    have h2 : ‖wz1Cross T_j.direction T_k.direction‖ ≥ c * d / tau := h_cross_lower
    have h4 : 16 * rho^3 / ‖wz1Cross T_j.direction T_k.direction‖ ≤
        16 * rho^3 / (c * d / tau) := by
      gcongr <;> linarith
    have h5 : 16 * rho^3 / (c * d / tau) = 16 * rho^3 * tau / (c * d) := by
      field_simp [htau_pos.ne', h_pos_cd.ne'] <;> ring
    rw [h5] at h4
    exact h4
  calc
    volume S_ball
      ≤ volume S_int := h1
    _ ≤ ENNReal.ofReal (16 * rho^3 / ‖wz1Cross T_j.direction T_k.direction‖) := h_main
    _ ≤ ENNReal.ofReal (16 * rho^3 * tau / (c * d)) := by
      gcongr <;> exact h_bound

end Kakeya.Assouad
