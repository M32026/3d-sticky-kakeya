import MyLeanRepo.Kakeya.CV.VisibilityDegreeBound.Helpers
import MyLeanRepo.Kakeya.CV.PolynomialMollification
import MyLeanRepo.Kakeya.CV.Mollification
import MyLeanRepo.Kakeya.CV.Targets.ConcreteMollifiedVisibility.Subadditivity
import MyLeanRepo.Kakeya.CV.Targets.ConcreteMollifiedVisibility.DirectionalAreaBounds
import MyLeanRepo.Kakeya.CV.Targets.ConcreteMollifiedVisibility.MollifiedHomogeneity
import MyLeanRepo.Kakeya.CV.Targets.ConcreteMollifiedVisibility.MollifiedBound
import MyLeanRepo.Kakeya.CV.Targets.ConcreteMollifiedVisibility.SeminormBody
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar


/-!
# Mass function properties for concrete mollified visibility

Assembles the proof that the concrete mollified visibility body is a
John-eligible centrally symmetric convex body, using extracted helper lemmas
for seminorm properties and the general seminorm-to-convex-body theorem.

## Main result

`concrete_mollified_visibility_of_mass` — given the concrete surface and
generic structural packages, proves `ConcreteMollifiedVisibilityStatement`.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal RealInnerProductSpace BigOperators

namespace Kakeya.CV

/-- The concrete mollified visibility body is a centrally symmetric convex body. -/
theorem concrete_mollified_visibility_of_mass
    (hSurface : ConcreteMollifiedSurfaceStatement) :
    ConcreteMollifiedVisibilityStatement := by
  intro k P U c ε x hU_meas hU hε

  let B_ennreal : ENNReal :=
    12 * planeConstant * ENNReal.ofReal Real.pi * (k : ℝ≥0∞)
  have hB_ne_top : B_ennreal ≠ ⊤ := by
    have h1 : planeConstant ≠ ⊤ := planeConstant_ne_top
    have h2 : ENNReal.ofReal Real.pi ≠ ⊤ := by simp
    have h3 : (12 : ENNReal) ≠ ⊤ := by simp
    have h4 : (k : ENNReal) ≠ ⊤ := by simp
    simp only [B_ennreal]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top h3 h1) h2) h4
  let B_real : ℝ := B_ennreal.toReal
  have hB_real_nonneg : 0 ≤ B_real := ENNReal.toReal_nonneg

  have hdeg : ∀ y, (parameterPolynomial P y).totalDegree ≤ k := by
    intro y
    exact (P.equiv y).2

  have h_bound_all : ∀ y u,
      directionalSurfaceArea u (parameterPolynomial P y)
        (polynomialZeroSet (parameterPolynomial P y) ∩ U) ≤
      B_ennreal * ENNReal.ofReal ‖u‖ := by
    intro y u
    exact directionalSurfaceArea_U_bound k (parameterPolynomial P y) (hdeg y) U c hU u

  have h_finite : ∀ y u,
      directionalSurfaceArea u (parameterPolynomial P y)
        (polynomialZeroSet (parameterPolynomial P y) ∩ U) ≠ ⊤ := by
    intro y u
    have h1 : _ ≤ B_ennreal * ENNReal.ofReal ‖u‖ := h_bound_all y u
    have h2 : B_ennreal * ENNReal.ofReal ‖u‖ ≠ ⊤ :=
      ENNReal.mul_ne_top hB_ne_top (by simp)
    exact ne_top_of_le_ne_top h2 h1

  let p : Point 3 → ℝ := fun u => concreteMollifiedDirectionalArea P ε x u U

  have h_p_nonneg : ∀ u, 0 ≤ p u := by
    intro u
    have h1 : ∀ y, 0 ≤ coefficientSurfaceFunctional P u U y := by
      intro y
      simpa [coefficientSurfaceFunctional] using ENNReal.toReal_nonneg
    have h2 : 0 ≤ ∫ y in Metric.ball x ε, coefficientSurfaceFunctional P u U y :=
      integral_nonneg h1
    have h3 : 0 ≤ (volume (Metric.ball (0 : CoefficientSpace P.dim) ε)).toReal⁻¹ := by positivity
    have h4 : p u = (volume (Metric.ball (0 : CoefficientSpace P.dim) ε)).toReal⁻¹ *
        ∫ y in Metric.ball x ε, coefficientSurfaceFunctional P u U y := by
      simp only [p, concreteMollifiedDirectionalArea, ballAverage] <;> rfl
    rw [h4]
    exact mul_nonneg h3 h2

  have h_p_hom : ∀ (a : ℝ) u, 0 ≤ a → p (a • u) = a * p u := by
    intro a u ha
    exact @concreteMollifiedDirectionalArea_hom k P U ε x c hU_meas hU hε hSurface a u ha

  have h_p_sub : ∀ u v, p (u + v) ≤ p u + p v := by
    intro u v
    exact @concreteMollifiedDirectionalArea_subadd k P U ε x c hU_meas hU hε hSurface h_finite u v

  have h_p_even : ∀ u, p (-u) = p u := by
    intro u
    exact @concreteMollifiedDirectionalArea_even k P U ε x c hU hε u

  have h_p_bound : ∀ u, p u ≤ B_real * ‖u‖ := by
    intro u
    exact @concreteMollifiedDirectionalArea_bound k P U c ε x hU_meas hU hε hSurface B_ennreal hB_ne_top h_bound_all h_finite u

  have h_lipschitz : ∀ (u v : Point 3), dist (p u) (p v) ≤ B_real * dist u v := by
    intro u v
    have h1 : p u ≤ p v + p (u - v) := by
      have h2 : p u = p ((u - v) + v) := by abel_nf
      rw [h2]
      have h := h_p_sub (u - v) v
      rw [add_comm (p (u - v)) (p v)] at h
      exact h
    have h3 : p v ≤ p u + p (v - u) := by
      have h4 : p v = p ((v - u) + u) := by abel_nf
      rw [h4]
      have h := h_p_sub (v - u) u
      rw [add_comm (p (v - u)) (p u)] at h
      exact h
    have h5 : p (v - u) = p (u - v) := by
      have h6 : p (-(u - v)) = p (u - v) := h_p_even (u - v)
      have h7 : -(u - v) = v - u := by abel
      rw [h7] at h6
      exact h6
    have h8 : |p u - p v| ≤ p (u - v) := by
      have h9 : p u - p v ≤ p (u - v) := by linarith
      have h10 : p v - p u ≤ p (u - v) := by linarith
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have h11 : p (u - v) ≤ B_real * ‖u - v‖ := h_p_bound (u - v)
    have h12 : dist (p u) (p v) = |p u - p v| := by simp [Real.dist_eq] <;> rfl
    have h13 : dist u v = ‖u - v‖ := by simp [dist_eq_norm] <;> rfl
    rw [h12, h13]
    linarith

  have h_p_cont : Continuous p := by
    let B_nn : NNReal := ⟨B_real, hB_real_nonneg⟩
    have h_lw : LipschitzWith B_nn p := by
      rw [lipschitzWith_iff_dist_le_mul]
      exact h_lipschitz
    exact h_lw.continuous

  have h_body := seminorm_convexBody p B_real hB_real_nonneg
    h_p_hom h_p_sub h_p_even h_p_cont h_p_bound

  have h_final : Convex ℝ (concreteMollifiedVisibilityBody P ε x U) ∧
      IsCompact (concreteMollifiedVisibilityBody P ε x U) ∧
      (interior (concreteMollifiedVisibilityBody P ε x U)).Nonempty ∧
      ∀ u, u ∈ concreteMollifiedVisibilityBody P ε x U →
        -u ∈ concreteMollifiedVisibilityBody P ε x U := by
    simpa [concreteMollifiedVisibilityBody, unitBall] using h_body

  exact ⟨⟨h_final.1, h_final.2.1, h_final.2.2.1⟩, h_final.2.2.2⟩

end Kakeya.CV
