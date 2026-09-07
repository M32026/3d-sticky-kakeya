import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.TubeBaseAlignment
import MyLeanRepo.Kakeya.Assouad.TubeAlignmentGeometry
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.Assouad.MisalignedIntersectionVolume
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Nonessential tube axis alignment

Nonessential overlap forces two unit tube axes to agree up to orientation and
an explicitly bounded basepoint displacement.
-/

noncomputable section

open Kakeya MeasureTheory Set

namespace Kakeya.Assouad

theorem nonessential_tube_axis_alignment :
    NonessentialTubeAxisAlignmentStatement := by
  intro delta hdelta hdelta1000 T U h_not_distinct
  have hoverlap :
      (2 : ENNReal)⁻¹ * max T.volume U.volume <
        MeasureTheory.volume (T.carrier ∩ U.carrier) := by
    simpa [DeltaTube.EssentiallyDistinct] using h_not_distinct
  have hT_vol_pos : 0 < T.volume := by
    have h : ENNReal.ofReal (delta ^ 2) ≤ T.volume :=
      tube_volume_lower_bound hdelta (by linarith) T
    have hpos : 0 < ENNReal.ofReal (delta ^ 2) := by
      simp [hdelta.ne'] <;> positivity
    exact hpos.trans_le h
  have hmax_pos : 0 < max T.volume U.volume :=
    hT_vol_pos.trans_le (le_max_left _ _)
  have hvol_pos :
      0 < MeasureTheory.volume (T.carrier ∩ U.carrier) := by
    have h_inv_pos : (0 : ENNReal) < (2 : ENNReal)⁻¹ :=
      ENNReal.inv_pos.mpr (by norm_num)
    have h_half_pos :
        (0 : ENNReal) <
          (2 : ENNReal)⁻¹ * max T.volume U.volume :=
      ENNReal.mul_pos h_inv_pos.ne' hmax_pos.ne'
    exact h_half_pos.trans_le hoverlap.le
  have h_nonempty : (T.carrier ∩ U.carrier).Nonempty := by
    by_contra h
    have h_empty : T.carrier ∩ U.carrier = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h
    rw [h_empty] at hvol_pos
    simp at hvol_pos
  rcases h_nonempty with ⟨x, hx⟩
  have h_inner_bounds :
      ∀ a b : Point3, ‖a‖ = 1 → ‖b‖ = 1 →
        -1 ≤ inner ℝ a b ∧ inner ℝ a b ≤ 1 := by
    intro a b ha hb
    have hca : |inner ℝ a b| ≤ ‖a‖ * ‖b‖ :=
      abs_real_inner_le_norm a b
    rw [ha, hb] at hca
    simpa using abs_le.mp hca
  have h_cos_half :
      ∀ θ : ℝ, Real.cos θ = 1 - 2 * (Real.sin (θ / 2)) ^ 2 := by
    intro θ
    have h1 :
        Real.cos (2 * (θ / 2)) =
          1 - 2 * (Real.sin (θ / 2)) ^ 2 := by
      rw [Real.cos_two_mul, Real.sin_sq] <;> ring
    convert h1 using 1 <;> ring_nf
  have h_sin_zero :
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi / 2 →
        Real.sin θ = 0 → θ = 0 := by
    intro θ hθ1 hθ2 hsin
    by_cases h : θ = 0
    · exact h
    · have hθ_pos : 0 < θ := lt_of_le_of_ne hθ1 (Ne.symm h)
      have h_pos : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi hθ_pos
          (by linarith [Real.pi_pos])
      rw [hsin] at h_pos
      linarith
  have h_arccos_le_pi2 :
      ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
        Real.arccos x ≤ Real.pi / 2 := by
    intro x hx0 _
    have h : Real.arccos x ≤ Real.arccos 0 :=
      Real.arccos_le_arccos hx0
    rwa [Real.arccos_zero] at h
  have h_sin_nonneg :
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi / 2 →
        0 ≤ Real.sin θ := by
    intro θ hθ1 hθ2
    exact Real.sin_nonneg_of_mem_Icc
      ⟨hθ1, by linarith [Real.pi_pos]⟩
  by_cases hpos : 0 ≤ inner ℝ T.direction U.direction
  · let v : Point3 := U.direction
    have hv_norm : ‖v‖ = 1 := U.direction_unit
    let θ : ℝ := Real.arccos (inner ℝ T.direction v)
    have hθ1 : 0 ≤ θ := Real.arccos_nonneg _
    have hinner_b :
        -1 ≤ inner ℝ T.direction v ∧
          inner ℝ T.direction v ≤ 1 :=
      h_inner_bounds T.direction v T.direction_unit hv_norm
    have hθ2 : θ ≤ Real.pi / 2 :=
      h_arccos_le_pi2 (inner ℝ T.direction v) hpos hinner_b.2
    have hcos : inner ℝ T.direction v = Real.cos θ := by
      rw [Real.cos_arccos hinner_b.1 hinner_b.2]
    have h_norm_eq :
        ‖T.direction - v‖ = 2 * Real.sin (θ / 2) := by
      have h1 :
          ‖T.direction - v‖ ^ 2 =
            2 * (1 - Real.cos θ) := by
        rw [norm_sub_sq_real T.direction v,
          T.direction_unit, hv_norm, hcos]
        <;> norm_num <;> ring
      have h3 : 0 ≤ Real.sin (θ / 2) :=
        Real.sin_nonneg_of_mem_Icc
          ⟨by linarith, by linarith [Real.pi_pos]⟩
      have h4 :
          ‖T.direction - v‖ ^ 2 =
            (2 * Real.sin (θ / 2)) ^ 2 := by
        rw [h1, h_cos_half θ]
        ring
      nlinarith [norm_nonneg (T.direction - v)]
    by_cases hsin : Real.sin θ = 0
    · have hθ0 : θ = 0 := h_sin_zero θ hθ1 hθ2 hsin
      have hdir : T.direction = v := by
        have hnorm : ‖T.direction - v‖ = 0 := by
          rw [h_norm_eq, hθ0]
          norm_num
        exact eq_of_sub_eq_zero (norm_eq_zero.mp hnorm)
      have hdir_bound :
          ‖T.direction - v‖ ≤ 1000 * delta := by
        rw [hdir]
        simp [hdelta.le]
      rcases base_alignment_sign_pos
          (by linarith) T U 1000 hdir_bound x hx with
        ⟨s, hs, hbase⟩
      refine
        ⟨1, U.base, Or.inl ⟨by norm_num, rfl⟩, ?_, s, hs, ?_⟩
      · simpa [v] using hdir_bound
      · rw [show (1000 + 2) * delta = 1002 * delta by ring] at hbase
        simpa using hbase
    · have hsin_pos : 0 < Real.sin θ :=
        lt_of_le_of_ne (h_sin_nonneg θ hθ1 hθ2) (Ne.symm hsin)
      by_cases hlarge : 32 * delta ≤ Real.sin θ
      · have hvol_upper :=
          misaligned_tubes_intersection_volume_upper
            hdelta hdelta1000 T U v (Or.inl rfl)
            θ hθ1 hθ2 hcos hsin_pos hlarge
        have hcontra :
            MeasureTheory.volume (T.carrier ∩ U.carrier) ≤
              (2 : ENNReal)⁻¹ * max T.volume U.volume := by
          exact hvol_upper.trans
            (mul_le_mul_right
              (le_max_left T.volume U.volume) (2 : ENNReal)⁻¹)
        exact False.elim (not_le.mpr hoverlap hcontra)
      · have hsmall : Real.sin θ < 32 * delta := by linarith
        have hdir_bound :
            ‖T.direction - v‖ ≤ 1000 * delta := by
          rw [h_norm_eq]
          have h1 : 2 * Real.sin (θ / 2) ≤ θ :=
            two_sin_half_le θ hθ1
          have h2 : θ ≤ (Real.pi / 2) * Real.sin θ :=
            le_pi2_mul_sin θ hθ1 hθ2
          have h3 :
              (Real.pi / 2) * Real.sin θ <
                (Real.pi / 2) * (32 * delta) := by
            gcongr <;> linarith
          have h5 : 16 * Real.pi * delta ≤ 1000 * delta := by
            nlinarith [Real.pi_lt_four]
          nlinarith
        rcases base_alignment_sign_pos
            (by linarith) T U 1000 hdir_bound x hx with
          ⟨s, hs, hbase⟩
        refine
          ⟨1, U.base, Or.inl ⟨by norm_num, rfl⟩, ?_, s, hs, ?_⟩
        · simpa [v] using hdir_bound
        · rw [show (1000 + 2) * delta = 1002 * delta by ring] at hbase
          simpa using hbase
  · let v : Point3 := -U.direction
    have hinner_pos : 0 ≤ inner ℝ T.direction v := by
      simpa [v, inner_smul_right] using
        show 0 ≤ -inner ℝ T.direction U.direction by linarith
    have hv_norm : ‖v‖ = 1 := by simp [v, U.direction_unit]
    let θ : ℝ := Real.arccos (inner ℝ T.direction v)
    have hθ1 : 0 ≤ θ := Real.arccos_nonneg _
    have hinner_b :
        -1 ≤ inner ℝ T.direction v ∧
          inner ℝ T.direction v ≤ 1 :=
      h_inner_bounds T.direction v T.direction_unit hv_norm
    have hθ2 : θ ≤ Real.pi / 2 :=
      h_arccos_le_pi2
        (inner ℝ T.direction v) hinner_pos hinner_b.2
    have hcos : inner ℝ T.direction v = Real.cos θ := by
      rw [Real.cos_arccos hinner_b.1 hinner_b.2]
    have h_norm_eq :
        ‖T.direction - v‖ = 2 * Real.sin (θ / 2) := by
      have h1 :
          ‖T.direction - v‖ ^ 2 =
            2 * (1 - Real.cos θ) := by
        rw [norm_sub_sq_real T.direction v,
          T.direction_unit, hv_norm, hcos]
        <;> norm_num <;> ring
      have h3 : 0 ≤ Real.sin (θ / 2) :=
        Real.sin_nonneg_of_mem_Icc
          ⟨by linarith, by linarith [Real.pi_pos]⟩
      have h4 :
          ‖T.direction - v‖ ^ 2 =
            (2 * Real.sin (θ / 2)) ^ 2 := by
        rw [h1, h_cos_half θ]
        ring
      nlinarith [norm_nonneg (T.direction - v)]
    by_cases hsin : Real.sin θ = 0
    · have hθ0 : θ = 0 := h_sin_zero θ hθ1 hθ2 hsin
      have hdir : T.direction = v := by
        have hnorm : ‖T.direction - v‖ = 0 := by
          rw [h_norm_eq, hθ0]
          norm_num
        exact eq_of_sub_eq_zero (norm_eq_zero.mp hnorm)
      have hdir_bound :
          ‖T.direction - v‖ ≤ 1000 * delta := by
        rw [hdir]
        simp [hdelta.le]
      rcases base_alignment_sign_neg
          (by linarith) T U 1000 (by simpa [v] using hdir_bound) x hx with
        ⟨s, hs, hbase⟩
      refine
        ⟨-1, U.base + U.direction,
          Or.inr ⟨by norm_num, by abel⟩, ?_, s, hs, ?_⟩
      · simpa [v] using hdir_bound
      · rw [show (1000 + 2) * delta = 1002 * delta by ring] at hbase
        simpa using hbase
    · have hsin_pos : 0 < Real.sin θ :=
        lt_of_le_of_ne (h_sin_nonneg θ hθ1 hθ2) (Ne.symm hsin)
      by_cases hlarge : 32 * delta ≤ Real.sin θ
      · have hvol_upper :=
          misaligned_tubes_intersection_volume_upper
            hdelta hdelta1000 T U v (Or.inr rfl)
            θ hθ1 hθ2 hcos hsin_pos hlarge
        have hcontra :
            MeasureTheory.volume (T.carrier ∩ U.carrier) ≤
              (2 : ENNReal)⁻¹ * max T.volume U.volume := by
          exact hvol_upper.trans
            (mul_le_mul_right
              (le_max_left T.volume U.volume) (2 : ENNReal)⁻¹)
        exact False.elim (not_le.mpr hoverlap hcontra)
      · have hsmall : Real.sin θ < 32 * delta := by linarith
        have hdir_bound :
            ‖T.direction - v‖ ≤ 1000 * delta := by
          rw [h_norm_eq]
          have h1 : 2 * Real.sin (θ / 2) ≤ θ :=
            two_sin_half_le θ hθ1
          have h2 : θ ≤ (Real.pi / 2) * Real.sin θ :=
            le_pi2_mul_sin θ hθ1 hθ2
          have h3 :
              (Real.pi / 2) * Real.sin θ <
                (Real.pi / 2) * (32 * delta) := by
            gcongr <;> linarith
          have h5 : 16 * Real.pi * delta ≤ 1000 * delta := by
            nlinarith [Real.pi_lt_four]
          nlinarith
        rcases base_alignment_sign_neg
            (by linarith) T U 1000
            (by simpa [v] using hdir_bound) x hx with
          ⟨s, hs, hbase⟩
        refine
          ⟨-1, U.base + U.direction,
            Or.inr ⟨by norm_num, by abel⟩, ?_, s, hs, ?_⟩
        · simpa [v] using hdir_bound
        · rw [show (1000 + 2) * delta = 1002 * delta by ring] at hbase
          simpa using hbase

end Kakeya.Assouad
