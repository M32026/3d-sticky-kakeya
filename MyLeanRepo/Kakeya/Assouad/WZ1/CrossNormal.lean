import MyLeanRepo.Kakeya.Assouad.WZ1.Statements

/-!
# WZ1 cross-product normal

Closed proof of the linear-algebra core of WZ1 Lemma 11.
-/

namespace Kakeya.Assouad

open Matrix

theorem wz1_cross_normal :
    WZ1CrossNormalStatement := by
  intro u v w hu hv hw kappa tau hkappa_pos hkappa_le htriple
  let cross : Point3 := wz1Cross u v
  have hcross_def :
      (cross : Fin 3 → ℝ) =
        (u : Fin 3 → ℝ) ⨯₃ (v : Fin 3 → ℝ) := by
    rfl
  have hcross_pos : 0 < ‖cross‖ := by
    linarith
  let normal : Point3 := (‖cross‖)⁻¹ • cross
  refine ⟨normal, ?_, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hcross_pos]
    field_simp [hcross_pos.ne']
  · have horthogonal : inner ℝ u cross = 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      have hstar :
          star (u : Fin 3 → ℝ) = (u : Fin 3 → ℝ) := by
        ext i
        simp
      rw [hstar, hcross_def, dotProduct_comm]
      exact dot_self_cross (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
    simp [normal, inner_smul_right, horthogonal]
  · have horthogonal : inner ℝ v cross = 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      have hstar :
          star (v : Fin 3 → ℝ) = (v : Fin 3 → ℝ) := by
        ext i
        simp
      rw [hstar, hcross_def, dotProduct_comm]
      exact dot_cross_self (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
    simp [normal, inner_smul_right, horthogonal]
  · have htriple_inner :
        inner ℝ w cross = wz1TripleProduct u v w := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      have hstar :
          star (w : Fin 3 → ℝ) = (w : Fin 3 → ℝ) := by
        ext i
        simp
      rw [hstar, hcross_def, dotProduct_comm]
      have hpermute :
          (w : Fin 3 → ℝ) ⬝ᵥ
              (u : Fin 3 → ℝ) ⨯₃ (v : Fin 3 → ℝ) =
            (u : Fin 3 → ℝ) ⬝ᵥ
              (v : Fin 3 → ℝ) ⨯₃ (w : Fin 3 → ℝ) :=
        triple_product_permutation
          (w : Fin 3 → ℝ) (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
      rw [hpermute]
      exact triple_product_eq_det
        (u : Fin 3 → ℝ) (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)
    have hnormal :
        inner ℝ w normal =
          (‖cross‖)⁻¹ * wz1TripleProduct u v w := by
      simp [normal, inner_smul_right, htriple_inner]
    rw [hnormal]
    have habs :
        |(‖cross‖)⁻¹ * wz1TripleProduct u v w| =
          |wz1TripleProduct u v w| / ‖cross‖ := by
      rw [abs_mul, abs_inv, abs_of_pos hcross_pos]
      ring
    rw [habs]
    calc
      |wz1TripleProduct u v w| / ‖cross‖
          ≤ |wz1TripleProduct u v w| / kappa := by
            gcongr
      _ ≤ tau / kappa := by
            gcongr

end Kakeya.Assouad
