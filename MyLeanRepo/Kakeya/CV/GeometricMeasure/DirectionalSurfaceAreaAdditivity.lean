import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.Geometry
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Additivity of directional surface area

Directional surface area is a nonnegative integral, hence is additive over
pairwise-disjoint measurable families.
-/

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal BigOperators

namespace Kakeya.CV

/-- Directional surface area is countably additive over pairwise-disjoint
measurable sets. -/
lemma directionalSurfaceArea_iUnion {ι : Type*} [Countable ι]
    (e : Point 3) (p : MvPolynomial (Fin 3) ℝ)
    (S : ι → Set (Point 3))
    (hdisj : Pairwise fun i j => Disjoint (S i) (S j))
    (hmeas : ∀ i, MeasurableSet (S i)) :
    directionalSurfaceArea e p (⋃ i, S i) =
      ∑' i : ι, directionalSurfaceArea e p (S i) := by
  dsimp only [directionalSurfaceArea]
  exact MeasureTheory.lintegral_iUnion hmeas hdisj
    (fun x => ENNReal.ofReal ‖inner ℝ e (polynomialUnitNormal p x)‖)

/-- Directional surface area is additive over a finite pairwise-disjoint
measurable family. -/
lemma directionalSurfaceArea_finite_iUnion {ι : Type*} [Fintype ι]
    (e : Point 3) (p : MvPolynomial (Fin 3) ℝ)
    (S : ι → Set (Point 3))
    (hdisj : Pairwise fun i j => Disjoint (S i) (S j))
    (hmeas : ∀ i, MeasurableSet (S i)) :
    directionalSurfaceArea e p (⋃ i : ι, S i) =
      ∑ i : ι, directionalSurfaceArea e p (S i) := by
  rw [directionalSurfaceArea_iUnion e p S hdisj hmeas, tsum_fintype]

end Kakeya.CV
