import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Tactic

/-! # Inner product and scalar triple product -/

namespace Kakeya.Assouad

open Matrix

/-- `inner w (u × v)` equals the scalar triple product of `u,v,w`. -/
lemma inner_cross_triple (u v w : Point3) :
    inner ℝ w (wz1Cross u v) = wz1TripleProduct u v w := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  have hstar : star (w : Fin 3 → ℝ) = (w : Fin 3 → ℝ) := by
    ext i
    simp
  rw [hstar]
  have hcross :
      ((wz1Cross u v) : Fin 3 → ℝ) =
        crossProduct (u : Fin 3 → ℝ) (v : Fin 3 → ℝ) := by
    rfl
  rw [hcross, dotProduct_comm]
  have hpermute :
      (w : Fin 3 → ℝ) ⬝ᵥ
          crossProduct (u : Fin 3 → ℝ) (v : Fin 3 → ℝ) =
        (u : Fin 3 → ℝ) ⬝ᵥ
          crossProduct (v : Fin 3 → ℝ) (w : Fin 3 → ℝ) :=
    triple_product_permutation
      (w : Fin 3 → ℝ) (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
  rw [hpermute]
  exact
    triple_product_eq_det
      (u : Fin 3 → ℝ) (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)

end Kakeya.Assouad
