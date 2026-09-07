import MyLeanRepo.Kakeya.CV.Geometry
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Helper lemma: finSuccEquiv intertwines pderiv and derivative
-/

noncomputable section

open MvPolynomial Polynomial

namespace Kakeya.CV

/-- Helper: finSuccEquiv ℝ 1 intertwines pderiv 0 and Polynomial.derivative. -/
lemma finSuccEquiv1_pderiv_zero (p : MvPolynomial (Fin 2) ℝ) :
    (finSuccEquiv ℝ 1) (pderiv 0 p) = ((finSuccEquiv ℝ 1) p).derivative := by
  let e : MvPolynomial (Fin 2) ℝ →+* Polynomial (MvPolynomial (Fin 1) ℝ) :=
    (finSuccEquiv ℝ 1).toRingHom
  have hC : ∀ (a : ℝ), e (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) :=
    (finSuccEquiv ℝ 1).commutes
  have hX0 : e (MvPolynomial.X 0) = Polynomial.X := MvPolynomial.finSuccEquiv_X_zero
  have hX1 : e (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X 0) :=
    MvPolynomial.finSuccEquiv_X_succ (j := 0)
  have h_main : ∀ (q : MvPolynomial (Fin 2) ℝ),
      e (pderiv 0 q) = (e q).derivative := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
      have h1 : pderiv 0 (MvPolynomial.C a) = (0 : MvPolynomial (Fin 2) ℝ) :=
        MvPolynomial.pderiv_C
      have h2 : e (pderiv 0 (MvPolynomial.C a)) = (0 : Polynomial (MvPolynomial (Fin 1) ℝ)) := by
        have h21 : e (pderiv 0 (MvPolynomial.C a)) = e (0 : MvPolynomial (Fin 2) ℝ) :=
          congr_arg e h1
        rw [h21, e.map_zero]
      have h3 : (e (MvPolynomial.C a)).derivative = (0 : Polynomial (MvPolynomial (Fin 1) ℝ)) := by
        have h31 : e (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := hC a
        have h32 : (e (MvPolynomial.C a)).derivative =
            (Polynomial.C (MvPolynomial.C a)).derivative := by
          exact congr_arg (fun x : Polynomial (MvPolynomial (Fin 1) ℝ) => x.derivative) h31
        rw [h32, Polynomial.derivative_C]
      rw [h2, h3]
    | add q r hq hr =>
      have hpd : pderiv 0 (q + r) = pderiv 0 q + pderiv 0 r :=
        (pderiv 0).map_add q r
      have h4 : e (pderiv 0 (q + r)) = e (pderiv 0 q) + e (pderiv 0 r) := by
        have h41 : e (pderiv 0 (q + r)) = e (pderiv 0 q + pderiv 0 r) := congr_arg e hpd
        rw [h41, e.map_add]
      have h5 : (e (q + r)).derivative = (e q).derivative + (e r).derivative := by
        have h51 : e (q + r) = e q + e r := e.map_add q r
        have h52 : (e (q + r)).derivative = (e q + e r).derivative :=
          congr_arg (fun x : Polynomial (MvPolynomial (Fin 1) ℝ) => x.derivative) h51
        rw [h52, Polynomial.derivative_add]
      rw [h4, hq, hr, h5]
    | mul_X q i hq =>
      have hpd : pderiv 0 (q * MvPolynomial.X i) =
          pderiv 0 q * MvPolynomial.X i + q * pderiv 0 (MvPolynomial.X i) :=
        MvPolynomial.pderiv_mul
      have h4 : e (pderiv 0 (q * MvPolynomial.X i)) =
          e (pderiv 0 q) * e (MvPolynomial.X i) + e q * e (pderiv 0 (MvPolynomial.X i)) := by
        have h41 : e (pderiv 0 (q * MvPolynomial.X i)) =
            e (pderiv 0 q * MvPolynomial.X i + q * pderiv 0 (MvPolynomial.X i)) :=
          congr_arg e hpd
        rw [h41, e.map_add, e.map_mul, e.map_mul]
      have hXi : e (pderiv 0 (MvPolynomial.X i)) = (e (MvPolynomial.X i)).derivative := by
        by_cases h : i = 0
        · subst h
          have hpd2 : pderiv 0 (MvPolynomial.X 0) = (1 : MvPolynomial (Fin 2) ℝ) :=
            MvPolynomial.pderiv_X_self 0
          have h_left : e (pderiv 0 (MvPolynomial.X 0)) = (1 : Polynomial (MvPolynomial (Fin 1) ℝ)) := by
            have h1 : e (pderiv 0 (MvPolynomial.X 0)) = e (1 : MvPolynomial (Fin 2) ℝ) :=
              congr_arg e hpd2
            rw [h1, e.map_one]
          have h_right : (e (MvPolynomial.X 0)).derivative = (1 : Polynomial (MvPolynomial (Fin 1) ℝ)) := by
            have h2 : (e (MvPolynomial.X 0)).derivative = (Polynomial.X).derivative :=
              congr_arg (fun x : Polynomial (MvPolynomial (Fin 1) ℝ) => x.derivative) hX0
            rw [h2] <;> simp
          exact Eq.trans h_left h_right.symm
        · have h_i1 : i = 1 := by
            have hval : i.val = 1 := by omega
            exact Fin.ext hval
          subst h_i1
          have hpd2 : pderiv 0 (MvPolynomial.X 1) = (0 : MvPolynomial (Fin 2) ℝ) :=
            MvPolynomial.pderiv_X_of_ne (by decide)
          have h_left : e (pderiv 0 (MvPolynomial.X 1)) = (0 : Polynomial (MvPolynomial (Fin 1) ℝ)) := by
            have h1 : e (pderiv 0 (MvPolynomial.X 1)) = e (0 : MvPolynomial (Fin 2) ℝ) :=
              congr_arg e hpd2
            rw [h1, e.map_zero]
          have h_right : (e (MvPolynomial.X 1)).derivative = (0 : Polynomial (MvPolynomial (Fin 1) ℝ)) := by
            have h2 : (e (MvPolynomial.X 1)).derivative =
                (Polynomial.C (MvPolynomial.X 0)).derivative :=
              congr_arg (fun x : Polynomial (MvPolynomial (Fin 1) ℝ) => x.derivative) hX1
            rw [h2] <;> simp
          exact Eq.trans h_left h_right.symm
      have h5 : (e (q * MvPolynomial.X i)).derivative =
          (e q).derivative * e (MvPolynomial.X i) + e q * (e (MvPolynomial.X i)).derivative := by
        have h51 : e (q * MvPolynomial.X i) = e q * e (MvPolynomial.X i) := e.map_mul q (MvPolynomial.X i)
        have h52 : (e (q * MvPolynomial.X i)).derivative = (e q * e (MvPolynomial.X i)).derivative :=
          congr_arg (fun x : Polynomial (MvPolynomial (Fin 1) ℝ) => x.derivative) h51
        rw [h52, Polynomial.derivative_mul]
      rw [h4, hq, hXi, h5]
  exact h_main p

end Kakeya.CV
