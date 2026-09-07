import MyLeanRepo.Kakeya.Cinematic.Statements
import MyLeanRepo.Kakeya.Cinematic.Targets.PolynomialRectangleRefinement.FinalAssembly

/-!
# Quantitative large-incomparability refinement

This target records the polynomial dependence on the requested comparison
constant in PYZ Lemma 24.  That dependence is needed when the comparison
constant grows with the tangency dilation in Lemma 28.
-/

namespace Kakeya.Cinematic

theorem polynomial_rectangle_refinement :
    PolynomialRectangleRefinementStatement :=
  polynomial_rectangle_refinement_assembly

end Kakeya.Cinematic
