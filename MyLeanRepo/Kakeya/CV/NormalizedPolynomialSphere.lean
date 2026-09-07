import MyLeanRepo.Kakeya.CV.Statements

/-!
# Normalized polynomial sphere and Borsuk--Ulam interface

Identifies the unit coefficient sphere with `TopCat.sphere` in the correct
dimension and transports the antipodal map.
-/

namespace Kakeya.CV

theorem normalized_polynomial_sphere :
    NormalizedPolynomialSphereStatement := by
  intro k P hdim
  rcases Nat.exists_eq_succ_of_ne_zero (ne_of_gt hdim) with ⟨n, hn⟩
  have hn2 : P.dim - 1 = n := by omega
  rw [hn2]
  let e_fin : Fin P.dim ≃ Fin (n + 1) := Equiv.cast (by rw [hn])
  let e_euclid : EuclideanSpace ℝ (Fin P.dim) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
    LinearIsometryEquiv.piLpCongrLeft (p := 2) (𝕜 := ℝ) (E := ℝ) e_fin
  let h_homeo : EuclideanSpace ℝ (Fin P.dim) ≃ₜ
      EuclideanSpace ℝ (Fin (n + 1)) := e_euclid.toHomeomorph
  let s : Set (EuclideanSpace ℝ (Fin P.dim)) := normalizedPolynomialParameters P
  let t : Set (EuclideanSpace ℝ (Fin (n + 1))) := Metric.sphere 0 1
  have h_symm_zero : h_homeo.symm 0 = 0 := e_euclid.symm.map_zero
  have h_preimage : h_homeo ⁻¹' t = s := by
    have h : h_homeo ⁻¹' (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) =
        Metric.sphere (h_homeo.symm 0) 1 := e_euclid.preimage_sphere 0 1
    rw [h, h_symm_zero]
    rfl
  have h_eq : s = h_homeo ⁻¹' t := h_preimage.symm
  let e_sphere : s ≃ₜ t := Homeomorph.sets h_homeo h_eq
  let h : s ≃ₜ TopCat.sphere n := e_sphere.trans Homeomorph.ulift.symm
  refine' ⟨h, _⟩
  intro x
  have h_main : h (normalizedParameterAntipodal P x) =
      TopCat.sphereAntipodal n (h x) := by
    simp only [h, Homeomorph.trans_apply]
    apply ULift.ext
    apply Subtype.ext
    simp [e_sphere, Homeomorph.sets, normalizedParameterAntipodal,
      TopCat.sphereAntipodal]
    rfl
  exact h_main

end Kakeya.CV
