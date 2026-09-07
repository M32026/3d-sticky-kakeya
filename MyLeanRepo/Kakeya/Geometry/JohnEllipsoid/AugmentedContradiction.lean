import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Basic
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Perturbation
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.AugmentedPerturbation
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.VolumeUtils
import Mathlib.Tactic

noncomputable section

open JohnEllipsoid MeasureTheory
open scoped Pointwise Real

namespace JohnEllipsoid

variable {n : ℕ}

abbrev Mat n := Matrix (Fin n) (Fin n) ℝ

/-- Contradiction lemma: if the augmented Fritz John conditions fail, there exists
an ellipsoid containing K with strictly smaller volume than the unit ball. -/
lemma augmented_perturbation_contradiction'
    {K : Set (E n)}
    (hK : IsConvexBody K)
    (h_sub : K ⊆ Metric.closedBall (0 : E n) 1)
    (C : Mat n) (hC : C.IsSymm) (b : E n) (α : ℝ)
    (h_neg : (n : ℝ) * α - C.trace < 0)
    (hS_strict : ∀ u ∈ K, ‖u‖ = 1 → quadForm C u + 2 * inner ℝ b u < α) :
    ∃ (c : E n) (A : E n ≃ₗ[ℝ] E n),
      K ⊆ ellipsoid c A ∧
      volume (ellipsoid c A) < volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) := by
  have hK_comp : IsCompact K := hK.2.1

  -- Step 1: Get ε1 from K_subset_augmented_perturbation
  rcases K_subset_augmented_perturbation hK_comp h_sub C hC b α hS_strict with ⟨ε1, hε1_pos, hK_pert⟩

  -- Step 2: Get ε2 from augmented_perturbation_volume_less
  rcases augmented_perturbation_volume_less C hC b α h_neg with ⟨ε2, hε2_pos, h_vol⟩

  -- Step 3: Pick t ∈ (0, min(ε1, ε2))
  let ε := min ε1 ε2
  have hε_pos : 0 < ε := by positivity
  have h_t_exists : ∃ t : ℝ, 0 < t ∧ t < ε := ⟨ε / 2, by linarith, by linarith⟩
  rcases h_t_exists with ⟨t, ht_pos, ht_lt_eps⟩
  have ht_lt_eps1 : t < ε1 := by
    calc t < ε := ht_lt_eps
         _ ≤ ε1 := min_le_left _ _
  have ht_lt_eps2 : t < ε2 := by
    calc t < ε := ht_lt_eps
         _ ≤ ε2 := min_le_right _ _

  -- Step 4: K ⊆ perturbed set
  have hK_subset_pert : K ⊆ {x | quadForm (1 + t • C) x + 2 * t * inner ℝ b x ≤ 1 + t * α} :=
    hK_pert t ht_pos ht_lt_eps1

  -- Step 5: Perturbed set is an ellipsoid with det < 1
  have h_vol_t := h_vol t ⟨ht_pos, ht_lt_eps2⟩
  rcases h_vol_t with ⟨hPD, _hr_t, c_t, A_t, h_set_eq, h_det_pos, h_det_lt_one⟩

  -- Step 6: K ⊆ ellipsoid c_t A_t
  have hK_sub_ellipsoid : K ⊆ ellipsoid c_t A_t := by
    rw [←h_set_eq]
    exact hK_subset_pert

  -- Step 7: Volume comparison
  have h_vol_lt : volume (ellipsoid c_t A_t) < volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) := by
    have h_det1 : LinearMap.det ((1 : E n ≃ₗ[ℝ] E n) : E n →ₗ[ℝ] E n) = 1 := by simp
    have h_abs1 : |LinearMap.det ((1 : E n ≃ₗ[ℝ] E n) : E n →ₗ[ℝ] E n)| = 1 := by
      rw [h_det1] <;> simp
    have h_abs2 : |LinearMap.det (A_t : E n →ₗ[ℝ] E n)| = LinearMap.det (A_t : E n →ₗ[ℝ] E n) := by
      rw [abs_of_pos h_det_pos]
    have h_abs_lt : |LinearMap.det (A_t : E n →ₗ[ℝ] E n)| < |LinearMap.det ((1 : E n ≃ₗ[ℝ] E n) : E n →ₗ[ℝ] E n)| := by
      rw [h_abs2, h_abs1]
      <;> linarith
    have h_iff := volume_ellipsoid_le_iff (0 : E n) (1 : E n ≃ₗ[ℝ] E n) c_t A_t
    have h_not_le : ¬ volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) ≤ volume (ellipsoid c_t A_t) := by
      rw [h_iff]
      <;> linarith
    have h_ne : volume (ellipsoid c_t A_t) ≠ volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) := by
      intro h_eq
      have h_le : volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) ≤ volume (ellipsoid c_t A_t) := by
        rw [h_eq]
      exact h_not_le h_le
    have h_total : volume (ellipsoid c_t A_t) ≤ volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) := by
      rw [volume_ellipsoid_le_iff c_t A_t (0 : E n) (1 : E n ≃ₗ[ℝ] E n)]
      rw [h_abs2, h_abs1] <;> linarith
    exact lt_of_le_of_ne h_total h_ne

  exact ⟨c_t, A_t, hK_sub_ellipsoid, h_vol_lt⟩

end JohnEllipsoid
