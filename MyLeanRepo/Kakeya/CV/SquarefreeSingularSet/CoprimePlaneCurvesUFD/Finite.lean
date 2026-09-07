import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.CoprimePlaneCurvesUFD.IrreducibleCurve
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Coprime plane curves have finite intersection

Two UFD-coprime nonzero polynomials in R[x,y] have finite common zero set.
-/

noncomputable section

open MeasureTheory Metric Set MvPolynomial UniqueFactorizationMonoid Polynomial
open scoped Polynomial

namespace Kakeya.CV

/-- **Coprime plane curves finiteness**: two UFD-coprime nonzero polynomials
    in R[x,y] have finite common zero set. -/
lemma coprime_plane_curves_finite_ufd {g f : MvPolynomial (Fin 2) ℝ}
    (hg : g ≠ 0) (hf : f ≠ 0)
    (hcop : ∀ h, h ∣ g → h ∣ f → IsUnit h) :
    Set.Finite {p : P2 | polynomialValue g p = 0 ∧ polynomialValue f p = 0} := by
  classical
  let factors := (UniqueFactorizationMonoid.factors g).toFinset
  have h_irr : ∀ q ∈ factors, Irreducible q := by
    intro q hq
    exact irreducible_of_factor q (Multiset.mem_toFinset.mp hq)
  have hdiv : ∀ q ∈ factors, q ∣ g := by
    intro q hq
    have h1 : q ∣ (UniqueFactorizationMonoid.factors g).prod :=
      Multiset.dvd_prod (Multiset.mem_toFinset.mp hq)
    have h_prod : Associated (UniqueFactorizationMonoid.factors g).prod g := factors_prod hg
    exact h1.trans h_prod.dvd
  have h_main : ∀ q ∈ factors,
      Set.Finite {p : P2 | polynomialValue q p = 0 ∧ polynomialValue f p = 0} := by
    intro q hq
    have hq_irred : Irreducible q := h_irr q hq
    have hq_cop : ∀ h, h ∣ q → h ∣ f → IsUnit h := by
      intro h h1 h2
      have h3 : h ∣ g := dvd_trans h1 (hdiv q hq)
      exact hcop h h3 h2
    exact irreducible_plane_curve_finite hq_irred hf hq_cop
  let S : Set P2 := {p | polynomialValue g p = 0 ∧ polynomialValue f p = 0}
  have h_union : Set.Finite (⋃ q ∈ factors, {p : P2 | polynomialValue q p = 0 ∧ polynomialValue f p = 0}) :=
    Set.Finite.biUnion factors.finite_toSet h_main
  have h_sub : S ⊆ ⋃ q ∈ factors, {p : P2 | polynomialValue q p = 0 ∧ polynomialValue f p = 0} := by
    intro p hp
    have h1 : polynomialValue g p = 0 := hp.1
    have h_prod : Associated (UniqueFactorizationMonoid.factors g).prod g := factors_prod hg
    rcases h_prod with ⟨u, h_eq⟩
    let u' : MvPolynomial (Fin 2) ℝ := u
    have h_u_isUnit : IsUnit u' := u.isUnit
    have h_u_eval : polynomialValue u' p ≠ 0 := by
      have h2 : ∃ (c : ℝ), c ≠ 0 ∧ u' = MvPolynomial.C c :=
        isUnit_mvPolynomial_over_field.mp h_u_isUnit
      rcases h2 with ⟨c, hc, huc⟩
      rw [huc]
      have h9 : polynomialValue (MvPolynomial.C c) p = c := by
        simp [polynomialValue, MvPolynomial.eval_C]
      rw [h9]
      exact hc
    have h4 : polynomialValue g p = polynomialValue ((UniqueFactorizationMonoid.factors g).prod) p * polynomialValue u' p := by
      have h_eq2 : (UniqueFactorizationMonoid.factors g).prod * u' = g := by exact h_eq
      have h_eval_mul : polynomialValue ((UniqueFactorizationMonoid.factors g).prod * u') p =
          polynomialValue ((UniqueFactorizationMonoid.factors g).prod) p * polynomialValue u' p := by
        unfold polynomialValue
        rw [MvPolynomial.eval_mul]
      have h6 : polynomialValue g p = polynomialValue ((UniqueFactorizationMonoid.factors g).prod * u') p :=
        congr_arg (fun x : MvPolynomial (Fin 2) ℝ => polynomialValue x p) h_eq2.symm
      rw [h6, h_eval_mul]
    have h7 : polynomialValue ((UniqueFactorizationMonoid.factors g).prod) p * polynomialValue u' p = 0 := by
      rw [←h4, h1]
    have h3 : polynomialValue ((UniqueFactorizationMonoid.factors g).prod) p = 0 :=
      (mul_eq_zero.mp h7).resolve_right h_u_eval
    have h_eval_prod : polynomialValue ((UniqueFactorizationMonoid.factors g).prod) p =
        ((UniqueFactorizationMonoid.factors g).map (fun q => polynomialValue q p)).prod := by
      let v : MvPolynomial (Fin 2) ℝ →+* ℝ := MvPolynomial.eval (fun i => p i)
      have h : v ((UniqueFactorizationMonoid.factors g).prod) =
          ((UniqueFactorizationMonoid.factors g).map v).prod := by
        exact v.map_multiset_prod (UniqueFactorizationMonoid.factors g)
      simpa [polynomialValue] using h
    rw [h_eval_prod] at h3
    have h5 : ∃ (q : MvPolynomial (Fin 2) ℝ), q ∈ (UniqueFactorizationMonoid.factors g) ∧ polynomialValue q p = 0 := by
      have h6 : ((UniqueFactorizationMonoid.factors g).map (fun q => polynomialValue q p)).prod = 0 := h3
      have h7 : 0 ∈ (UniqueFactorizationMonoid.factors g).map (fun q => polynomialValue q p) :=
        Multiset.prod_eq_zero_iff.mp h6
      rcases Multiset.mem_map.mp h7 with ⟨q, hq, hq0⟩
      exact ⟨q, hq, hq0⟩
    rcases h5 with ⟨q, hq, hq0⟩
    exact Set.mem_iUnion₂.mpr ⟨q, Multiset.mem_toFinset.mpr hq, ⟨hq0, hp.2⟩⟩
  exact Set.Finite.subset h_union h_sub

end Kakeya.CV
