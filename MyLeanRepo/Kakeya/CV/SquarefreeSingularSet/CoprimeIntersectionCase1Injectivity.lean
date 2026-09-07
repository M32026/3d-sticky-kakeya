import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.DivisorCylinder
import Mathlib.Algebra.Polynomial.Degree.Domain

/-!
# Injectivity and IsUnit transfer for `rename castSucc`

Small standalone lemmas using `polyEquiv` to avoid typeclass issues with
`MvPolynomial.rename_injective`.
-/

noncomputable section

open MvPolynomial Polynomial

namespace Kakeya.CV

/-- IsUnit transfers through `rename castSucc`. -/
lemma isUnit_rename_castSucc_iff {q : MvPolynomial (Fin 2) ℝ} :
    IsUnit (rename (Fin.castSucc : Fin 2 → Fin 3) q) ↔ IsUnit q := by
  constructor
  · intro h
    have h1 : IsUnit (polyEquiv (rename (Fin.castSucc : Fin 2 → Fin 3) q)) :=
      h.map polyEquiv.toRingHom
    rw [polyEquiv_rename_castSucc q] at h1
    exact Polynomial.isUnit_C.mp h1
  · intro h
    exact h.map (rename (Fin.castSucc : Fin 2 → Fin 3)).toRingHom

/-- Injectivity of `rename castSucc` from 2 to 3 variables, via `polyEquiv`. -/
lemma rename_castSucc_injective {g1 g2 : MvPolynomial (Fin 2) ℝ}
    (h : (rename (Fin.castSucc : Fin 2 → Fin 3) g1) = (rename (Fin.castSucc : Fin 2 → Fin 3) g2)) :
    g1 = g2 := by
  have h1 : polyEquiv (rename (Fin.castSucc : Fin 2 → Fin 3) g1) =
      polyEquiv (rename (Fin.castSucc : Fin 2 → Fin 3) g2) :=
    congr_arg polyEquiv h
  rw [polyEquiv_rename_castSucc g1, polyEquiv_rename_castSucc g2] at h1
  have h2 : (Polynomial.C g1 : Polynomial (MvPolynomial (Fin 2) ℝ)) = Polynomial.C g2 := h1
  have h3 : g1 = g2 := by
    have h4 : (Polynomial.C g1 : Polynomial (MvPolynomial (Fin 2) ℝ)).coeff 0 = (Polynomial.C g2).coeff 0 := by
      rw [h2]
    simpa using h4
  exact h3

end Kakeya.CV
