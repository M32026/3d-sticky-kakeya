import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Basic facts about the anisotropic rescaling map

Injectivity and coordinate-wise characterization.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Coordinate-wise characterization of the anisotropic rescaling map. -/
lemma anisotropicRescalingMap_coord (g : SlopeFunction) (c d m : ℝ) (p : Point3) :
    (anisotropicRescalingMap g c d m p) 0 = p 0 + g (c + (d - c) / 2) * p 1 ∧
    (anisotropicRescalingMap g c d m p) 1 = (m * (d - c) / 2) * p 1 ∧
    (anisotropicRescalingMap g c d m p) 2 = 2 * (p 2 - c) / (d - c) - 1 := by
  simp [anisotropicRescalingMap, point3]

/-- The anisotropic rescaling map is injective when m > 0 and d > c. -/
lemma anisotropicRescalingMap_injective (g : SlopeFunction) {c d m : ℝ}
    (hm_pos : 0 < m) (hcd : c < d) :
    Function.Injective (anisotropicRescalingMap g c d m) := by
  set K : ℝ := m * (d - c) / 2 with hK_def
  have hK_pos : 0 < K := by positivity
  have hdc_pos : 0 < d - c := by linarith
  intro p q h
  have h0 := congr_arg (fun x : Point3 => x 0) h
  have h1 := congr_arg (fun x : Point3 => x 1) h
  have h2 := congr_arg (fun x : Point3 => x 2) h
  have hp2 : p 2 = q 2 := by
    have h_eq2 : 2 * (p 2 - c) / (d - c) - 1 = 2 * (q 2 - c) / (d - c) - 1 := by
      simpa [anisotropicRescalingMap_coord] using h2
    field_simp [hdc_pos.ne'] at h_eq2
    linarith
  have hp1 : p 1 = q 1 := by
    have h_eq1 : K * p 1 = K * q 1 := by
      simpa [anisotropicRescalingMap_coord, hK_def] using h1
    exact (mul_right_inj' hK_pos.ne').mp h_eq1
  have hp0 : p 0 = q 0 := by
    have h_eq0 : p 0 + g (c + (d - c) / 2) * p 1 = q 0 + g (c + (d - c) / 2) * q 1 := by
      simpa [anisotropicRescalingMap_coord] using h0
    rw [hp1] at h_eq0
    linarith
  have h_all : ∀ (i : Fin 3), p i = q i := by
    intro i
    fin_cases i <;> tauto
  have h_ext : p = q := by
    apply PiLp.ext
    exact h_all
  exact h_ext

end Kakeya.Assouad
