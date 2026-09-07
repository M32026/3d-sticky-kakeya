import MyLeanRepo.Kakeya.CV.PolynomialMollification
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Squarefree.Basic

/-!
# Square factor extraction for non-squarefree polynomials

This module proves that every nonzero, non-squarefree polynomial of total degree
at most `k` in three variables over `ℝ` can be written as `q^2 * r` where `q` is
nonconstant and `deg(q) ≤ k/2`.

This is a key step in the generic polynomial regularity argument: the
non-squarefree locus is contained in the union of images of polynomial maps
from lower-dimensional coefficient spaces.
-/

noncomputable section

open MvPolynomial

namespace Kakeya.CV

/-- If a nonzero polynomial `p` of total degree at most `k` is not squarefree,
then it has a nonconstant square factor `q^2` with `deg(q) ≤ k/2`. -/
lemma exists_nonconstant_square_factor {p : MvPolynomial (Fin 3) ℝ} {k : ℕ}
    (hp : p ≠ 0) (hdeg : p.totalDegree ≤ k) (hnonsq : ¬ Squarefree p) :
    ∃ (q r : MvPolynomial (Fin 3) ℝ), p = q^2 * r ∧ 0 < q.totalDegree ∧ q.totalDegree ≤ k / 2 := by
  have h1 : ∃ (q : MvPolynomial (Fin 3) ℝ), q * q ∣ p ∧ ¬ IsUnit q := by
    have h₂ : ¬ (∀ (x : MvPolynomial (Fin 3) ℝ), x * x ∣ p → IsUnit x) := hnonsq
    have h₃ : ∃ (x : MvPolynomial (Fin 3) ℝ), ¬ ((x * x ∣ p) → IsUnit x) :=
      Classical.not_forall.mp h₂
    rcases h₃ with ⟨q, hq⟩
    have h₄ : (q * q ∣ p) ∧ ¬ IsUnit q := by simpa using hq
    exact ⟨q, h₄⟩
  rcases h1 with ⟨q, hq_dvd, hq_nunit⟩
  have hq_ne_zero : q ≠ 0 := by
    by_contra h
    rw [h] at hq_dvd
    have h0 : (0 : MvPolynomial (Fin 3) ℝ) * (0 : MvPolynomial (Fin 3) ℝ) = 0 := by simp
    rw [h0] at hq_dvd
    have hp0 : p = 0 := zero_dvd_iff.mp hq_dvd
    exact hp hp0
  have hq_pos : 0 < q.totalDegree := by
    by_contra h
    have h' : q.totalDegree = 0 := by omega
    have hq_C : q = C (q.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp h'
    have hcoeff_ne_zero : q.coeff 0 ≠ 0 := by
      intro hco
      have hq0 : q = 0 := by
        rw [hq_C, hco] ; simp
      exact hq_ne_zero hq0
    have hunit_coeff : IsUnit (q.coeff 0) := hcoeff_ne_zero.isUnit
    have hunit : IsUnit q := by
      rw [isUnit_iff_totalDegree_of_isReduced]
      exact ⟨hunit_coeff, h'⟩
    exact hq_nunit hunit
  rcases hq_dvd with ⟨r, hr⟩
  have hr_eq : p = q^2 * r := by
    have h : q * q = q^2 := by ring
    rw [h] at hr
    exact hr
  have hr_ne_zero : r ≠ 0 := by
    by_contra h
    rw [hr_eq, h] at hp
    simp at hp
  have hq2_ne_zero : q^2 ≠ 0 := pow_ne_zero 2 hq_ne_zero
  have hdeg_mul : (q^2 * r).totalDegree = (q^2).totalDegree + r.totalDegree :=
    totalDegree_mul_of_isDomain hq2_ne_zero hr_ne_zero
  have hdeg_q2 : (q^2).totalDegree = 2 * q.totalDegree := by
    have h : (q^2).totalDegree = (q * q).totalDegree := by ring_nf
    rw [h]
    have h2 := totalDegree_mul_of_isDomain hq_ne_zero hq_ne_zero
    linarith
  have h_main : 2 * q.totalDegree ≤ p.totalDegree := by
    rw [hr_eq, hdeg_mul, hdeg_q2]
    ; omega
  have h_final : q.totalDegree ≤ k / 2 := by omega
  exact ⟨q, r, hr_eq, hq_pos, h_final⟩

end Kakeya.CV
