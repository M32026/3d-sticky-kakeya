import MyLeanRepo.Kakeya.CV.PolynomialCylinder.MainAssembly

/-!
# Polynomial cylinder estimate

Carbery--Valdimarsson Lemma 1 (Guth's cylinder estimate), specialized to
polynomial hypersurfaces and unit tubes in three dimensions.
-/

namespace Kakeya.CV

theorem polynomial_cylinder_estimate :
    PolynomialCylinderEstimateStatement :=
  polynomial_cylinder_estimate_main

end Kakeya.CV
