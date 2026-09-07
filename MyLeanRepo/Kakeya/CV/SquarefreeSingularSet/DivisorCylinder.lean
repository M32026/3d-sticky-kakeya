import MyLeanRepo.Kakeya.CV.Geometry
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Degree.Domain

/-!
# Divisors of cylinder polynomials are cylinder polynomials

If `d * h = rename castSucc g` in `MvPolynomial (Fin 3) ℝ` with `g ≠ 0`,
then `d` is also in the image of `rename castSucc` (doesn't depend on z).
-/

noncomputable section

open MvPolynomial Polynomial

namespace Kakeya.CV

/-- Equivalence `Fin 3 ≃ Option (Fin 2)` sending 2 to none. -/
def varEquiv : Fin 3 ≃ Option (Fin 2) :=
  finSuccEquiv' (2 : Fin 3)

/-- The full algebra equivalence isolating variable 2. -/
def polyEquiv :
    MvPolynomial (Fin 3) ℝ ≃ₐ[ℝ] Polynomial (MvPolynomial (Fin 2) ℝ) :=
  (MvPolynomial.renameEquiv ℝ varEquiv).trans (optionEquivLeft ℝ (Fin 2))

/-- Helper: `optionEquivLeft` maps `rename some g` to `Polynomial.C g`. -/
private lemma optionEquivLeft_rename_some (g : MvPolynomial (Fin 2) ℝ) :
    (optionEquivLeft ℝ (Fin 2)) (MvPolynomial.rename (some : Fin 2 → Option (Fin 2)) g) =
    Polynomial.C g := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp [optionEquivLeft_C] <;> rfl
  | add p q hp hq =>
    have h_add : MvPolynomial.rename (some : Fin 2 → Option (Fin 2)) (p + q) =
        MvPolynomial.rename (some : Fin 2 → Option (Fin 2)) p +
        MvPolynomial.rename (some : Fin 2 → Option (Fin 2)) q := by
      exact map_add (MvPolynomial.rename (some : Fin 2 → Option (Fin 2))) p q
    rw [h_add]
    have h_map : (optionEquivLeft ℝ (Fin 2)) (MvPolynomial.rename (some : Fin 2 → Option (Fin 2)) p +
        MvPolynomial.rename (some : Fin 2 → Option (Fin 2)) q) =
        (optionEquivLeft ℝ (Fin 2)) (MvPolynomial.rename (some : Fin 2 → Option (Fin 2)) p) +
        (optionEquivLeft ℝ (Fin 2)) (MvPolynomial.rename (some : Fin 2 → Option (Fin 2)) q) := by
      exact map_add (optionEquivLeft ℝ (Fin 2)) _ _
    rw [h_map, hp, hq]
    <;> simp [Polynomial.C_add] <;> rfl
  | mul_X p i hp =>
    have h_rename : MvPolynomial.rename (some : Fin 2 → Option (Fin 2)) (p * X i) =
        MvPolynomial.rename (some : Fin 2 → Option (Fin 2)) p * X (some i) := by
      have h_m : MvPolynomial.rename (some : Fin 2 → Option (Fin 2)) (p * X i) =
          MvPolynomial.rename (some : Fin 2 → Option (Fin 2)) p *
          MvPolynomial.rename (some : Fin 2 → Option (Fin 2)) (X i) := by
        exact map_mul (MvPolynomial.rename (some : Fin 2 → Option (Fin 2))) p (X i)
      rw [h_m, rename_X] <;> rfl
    rw [h_rename]
    rw [map_mul, hp, optionEquivLeft_X_some]
    <;> simp [Polynomial.C_mul] <;> ring

/-- `polyEquiv` maps `rename castSucc g` to `Polynomial.C g`. -/
lemma polyEquiv_rename_castSucc (g : MvPolynomial (Fin 2) ℝ) :
    polyEquiv (rename (Fin.castSucc : Fin 2 → Fin 3) g) = Polynomial.C g := by
  have h1 : ∀ (x : Fin 2), varEquiv (Fin.castSucc x) = some x := by
    intro x
    fin_cases x <;> simp [varEquiv] <;> decide
  have h_comp : (varEquiv ∘ Fin.castSucc) = (some : Fin 2 → Option (Fin 2)) := by
    funext x
    exact h1 x
  have h21 : MvPolynomial.rename varEquiv (rename (Fin.castSucc : Fin 2 → Fin 3) g) =
      MvPolynomial.rename (varEquiv ∘ Fin.castSucc) g := by
    rw [rename_rename]
  have h2 : MvPolynomial.rename varEquiv (rename (Fin.castSucc : Fin 2 → Fin 3) g) =
      MvPolynomial.rename (some : Fin 2 → Option (Fin 2)) g := by
    rw [h21, h_comp]
  have h_renameEquiv : (MvPolynomial.renameEquiv ℝ varEquiv) (rename (Fin.castSucc : Fin 2 → Fin 3) g) =
      MvPolynomial.rename varEquiv (rename (Fin.castSucc : Fin 2 → Fin 3) g) := by
    rfl
  rw [polyEquiv, AlgEquiv.trans_apply, h_renameEquiv, h2]
  exact optionEquivLeft_rename_some g

/-- Any divisor of a nonzero cylinder polynomial is itself a cylinder polynomial. -/
lemma divisor_cylinder_independent {g : MvPolynomial (Fin 2) ℝ}
    {d h : MvPolynomial (Fin 3) ℝ} (hg : g ≠ 0)
    (h_eq : d * h = rename (Fin.castSucc : Fin 2 → Fin 3) g) :
    ∃ (d2 : MvPolynomial (Fin 2) ℝ),
      d = rename (Fin.castSucc : Fin 2 → Fin 3) d2 := by
  have hd_ne_zero : d ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h_eq
    have h3 : polyEquiv (rename (Fin.castSucc : Fin 2 → Fin 3) g) = 0 := by
      rw [←h_eq] <;> simp
    have h4 : Polynomial.C g = 0 := by
      rwa [polyEquiv_rename_castSucc g] at h3
    have h5 : g = 0 := by simpa [Polynomial.C_eq_zero] using h4
    exact hg h5
  set P : Polynomial (MvPolynomial (Fin 2) ℝ) := polyEquiv d with hP_def
  set Q : Polynomial (MvPolynomial (Fin 2) ℝ) := polyEquiv h with hQ_def
  have h_mul : P * Q = Polynomial.C g := by
    have h_eq2 : polyEquiv (d * h) = polyEquiv (rename (Fin.castSucc : Fin 2 → Fin 3) g) := by
      rw [h_eq]
    have h5 : polyEquiv (d * h) = P * Q := by
      simpa [hP_def, hQ_def, map_mul] using rfl
    have h6 : polyEquiv (rename (Fin.castSucc : Fin 2 → Fin 3) g) = Polynomial.C g :=
      polyEquiv_rename_castSucc g
    rw [h5, h6] at h_eq2
    exact h_eq2
  have h_dvd : P ∣ Polynomial.C g := ⟨Q, h_mul.symm⟩
  have hC_ne_zero : (Polynomial.C g : Polynomial (MvPolynomial (Fin 2) ℝ)) ≠ 0 := by
    exact Polynomial.C_ne_zero.mpr hg
  have hdeg : P.natDegree ≤ (Polynomial.C g).natDegree :=
    Polynomial.natDegree_le_of_dvd h_dvd hC_ne_zero
  have hdeg0 : (Polynomial.C g : Polynomial (MvPolynomial (Fin 2) ℝ)).natDegree = 0 := by simp
  have hdegP : P.natDegree = 0 := by linarith
  have hP_const : ∃ (c : MvPolynomial (Fin 2) ℝ), P = Polynomial.C c := by
    refine ⟨P.coeff 0, ?_⟩
    exact Polynomial.eq_C_of_natDegree_le_zero (by linarith)
  rcases hP_const with ⟨d2, hd2_eq⟩
  refine ⟨d2, ?_⟩
  have h4 : polyEquiv d = polyEquiv (rename (Fin.castSucc : Fin 2 → Fin 3) d2) := by
    have h5 : polyEquiv d = P := by simp [hP_def]
    have h6 : polyEquiv (rename (Fin.castSucc : Fin 2 → Fin 3) d2) = Polynomial.C d2 :=
      polyEquiv_rename_castSucc d2
    rw [h5, h6, hd2_eq]
  exact polyEquiv.injective h4

end Kakeya.CV
