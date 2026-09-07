import MyLeanRepo.Kakeya.CV.MultilinearKakeya.Assembly
import MyLeanRepo.Kakeya.CV.MultilinearKakeya.Factorization
import MyLeanRepo.Kakeya.CV.MultilinearKakeya.PolynomialApplication

/-!
# Complete CV multilinear Kakeya theorem

Unconditional shaded delta-tube output consumed by WZ1.
-/

namespace Kakeya.CV

/-- The complete shaded form of WZ1 Theorem 10. -/
theorem multilinear_kakeya_three :
    MultilinearKakeyaThreeStatement :=
  multilinear_kakeya_three_of_application
    (polynomial_visibility_to_unitScale_multilinear_kakeya_of_factorization
      polynomial_visibility_to_lattice_factorization_closed)

end Kakeya.CV
