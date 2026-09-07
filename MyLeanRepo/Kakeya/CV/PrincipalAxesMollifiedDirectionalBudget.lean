import MyLeanRepo.Kakeya.CV.Targets.ConcreteVisibilityHomotheticContinuity.DirectionalAreaConvex

/-!
# Principal-axis directional budgets

Homothetic containment of a selected centered ellipsoid in a dilation of the
concrete mollified visibility body bounds every principal semiaxis times its
corresponding directional area.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Kakeya.CV

theorem principalAxes_mollified_directional_budget :
    PrincipalAxesMollifiedDirectionalBudgetStatement := by
  intro k P U ε x α A b ℓ hα hℓ haxis hclose i
  have h_endpoint : ℓ i • b i ∈ JohnEllipsoid.ellipsoid 0 A := by
    rw [← haxis i, JohnEllipsoid.ellipsoid_mem_iff]
    simp
  rcases hclose.2 h_endpoint with ⟨v, hv, hv_eq⟩
  have hv_area : concreteMollifiedDirectionalArea P ε x v U ≤ 1 := hv.2
  calc
    ℓ i * concreteMollifiedDirectionalArea P ε x (b i) U =
        concreteMollifiedDirectionalArea P ε x (ℓ i • b i) U := by
          rw [concreteMollifiedDirectionalArea_homogeneous
            P ε x (ℓ i) (b i) U (hℓ i)]
    _ = concreteMollifiedDirectionalArea P ε x
          ((AffineMap.homothety 0 α) v) U := by
          rw [hv_eq]
    _ = concreteMollifiedDirectionalArea P ε x (α • v) U := by
          simp [AffineMap.homothety_apply]
    _ = α * concreteMollifiedDirectionalArea P ε x v U :=
      concreteMollifiedDirectionalArea_homogeneous P ε x α v U hα
    _ ≤ α * 1 := mul_le_mul_of_nonneg_left hv_area hα
    _ = α := mul_one α

end Kakeya.CV
