import MyLeanRepo.Kakeya.CV.PrincipalAxes.DirectionalDisjointCoverOn
import MyLeanRepo.Kakeya.CV.GeometricMeasure.DirectionalRegularGraphCover

/-!
# Affine identity on the regular directional zero set, restricted to a measurable subset

Combines the regular graph cover with the measurable disjoint-cover additivity
to establish the affine transformation identity for directional surface area on
the regular part of a polynomial zero set, intersected with an arbitrary
measurable set `S`.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

/-- Affine identity for directional surface area on the regular zero set of `q`
in direction `i`, restricted to a measurable set `S`. -/
lemma direction_i_regular_affine_identity_on
    (p q : MvPolynomial (Fin 3) ℝ)
    (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z : Point 3) (hη : 0 < η)
    (b : OrthonormalBasis (Fin 3) ℝ (Point 3))
    (ℓ : Fin 3 → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (hA : ∀ i, A (eBasis i) = ℓ i • b i)
    (hpq : ∀ x, polynomialValue p (z + η • A x) = polynomialValue q x)
    (i : Fin 3) (S : Set (Point 3)) (hS : MeasurableSet S) :
    ENNReal.ofReal (ℓ i) *
      directionalSurfaceArea (b i) p
        ((fun y => z + η • A y) ''
          (S ∩ {x | polynomialValue q x = 0 ∧
            (polynomialGradient q x) i ≠ 0})) =
    ENNReal.ofReal
      (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
      directionalSurfaceArea (eBasis i) q
        (S ∩ {x | polynomialValue q x = 0 ∧
          (polynomialGradient q x) i ≠ 0}) := by
  obtain ⟨patches, U, g, hprops, hcover⟩ := direction_i_graph_cover q i

  let regularSet : Set (Point 3) :=
    {x | polynomialValue q x = 0 ∧ (polynomialGradient q x) i ≠ 0}

  have h1 : (⋃ n, patches n) ⊆ regularSet := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
    have hpatches_n : patches n = coordPerm i '' (graphMap (g n) '' U n) :=
      (hprops n).2.2.1
    rw [hpatches_n] at hxn
    rcases hxn with ⟨y, hy, rfl⟩
    rcases hy with ⟨u, huU, rfl⟩
    have h_zero : polynomialValue q (coordPerm i (graphMap (g n) u)) = 0 :=
      (hprops n).2.2.2.1 u huU
    have h_reg : (polynomialGradient q (coordPerm i (graphMap (g n) u))) i ≠ 0 :=
      (hprops n).2.2.2.2 u huU
    exact ⟨h_zero, h_reg⟩

  have hcover_eq : (⋃ n, patches n) = regularSet :=
    Set.Subset.antisymm h1 hcover

  have h_main := direction_i_measurable_cover_additivity_on
    p q A η z hη b ℓ hℓ hA hpq i patches U g hprops S hS

  rw [hcover_eq] at h_main
  exact h_main

end Kakeya.CV
