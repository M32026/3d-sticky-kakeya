import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.CoprimeIntersectionCase1
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.ResultantBridge
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.DivisorCylinder

/-!
# Coprime irreducible pair intersection has Hausdorff dimension at most 1

Given an irreducible polynomial `f` and a polynomial `g` coprime to `f`,
their common zero set in `ℝ³` has Hausdorff dimension at most 1.

## Proof strategy

Split on whether `pderiv 2 f = 0`:

- **Case A** (`pderiv 2 f = 0`): `f` is a cylinder polynomial (independent of `z`).
  Apply `coprime_intersection_case1` directly.

- **Case B** (`pderiv 2 f ≠ 0`): Use the resultant bridge to obtain a nonzero
  2-variable polynomial `R` that vanishes on the projection of every common zero.
  Then `{f=0, g=0} ⊆ {R=0, f=0}`. We prove `R` (as a cylinder) and `f` are coprime:
  any common divisor must be a cylinder (since it divides `R`), and since `f` is
  irreducible and not a cylinder, the divisor must be a unit. Then apply
  `coprime_intersection_case1` to `(R, f)`.
-/

noncomputable section

open MeasureTheory Metric Set MvPolynomial

namespace Kakeya.CV

/-- The common zero set of an irreducible polynomial and a coprime polynomial
    has Hausdorff dimension at most 1. -/
lemma coprime_irreducible_intersection_dimH_le_one
    {f g : MvPolynomial (Fin 3) ℝ}
    (hf : Irreducible f)
    (hcop : ∀ h, h ∣ f → h ∣ g → IsUnit h) :
    dimH {p : Point 3 | polynomialValue f p = 0 ∧ polynomialValue g p = 0} ≤ 1 := by
  have hf_ne : f ≠ 0 := Irreducible.ne_zero hf
  have hg_ne : g ≠ 0 := by
    intro hz
    have hunit : IsUnit f := hcop f dvd_rfl (by rw [hz] <;> simp)
    exact hf.not_dvd_one (isUnit_iff_dvd_one.mp hunit)

  by_cases hderiv : pderiv 2 f = 0
  · -- Case A: f is independent of variable 2 (a cylinder)
    rcases pderiv2_zero_exists_restriction f hderiv with ⟨f2, hf2_eq⟩
    have hf2_ne : f2 ≠ 0 := by
      intro hz
      rw [hf2_eq, hz] at hf_ne
      exact hf_ne rfl
    have hcop' : ∀ h, h ∣ rename (Fin.castSucc : Fin 2 → Fin 3) f2 → h ∣ g → IsUnit h := by
      intro h hdiv1 hdiv2
      have hdiv_f : h ∣ f := by
        rwa [hf2_eq]
      exact hcop h hdiv_f hdiv2
    have h_set_eq : {p : Point 3 | polynomialValue f p = 0 ∧ polynomialValue g p = 0} =
        {p : Point 3 | polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) f2) p = 0 ∧
          polynomialValue g p = 0} := by
      ext p
      simp only [Set.mem_setOf_eq]
      have h_eq1 : polynomialValue f p = polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) f2) p := by
        rw [hf2_eq]
      rw [h_eq1]
    rw [h_set_eq]
    exact coprime_intersection_case1 hf2_ne hg_ne hcop'

  · -- Case B: pderiv 2 f ≠ 0
    have hderiv' : pderiv 2 f ≠ 0 := hderiv
    rcases resultant_bridge f g hf hcop hderiv' with ⟨R, hR_ne, hR_vanish⟩
    let R3 : MvPolynomial (Fin 3) ℝ := rename (Fin.castSucc : Fin 2 → Fin 3) R

    have h_R_cop_f : ∀ h, h ∣ R3 → h ∣ f → IsUnit h := by
      intro h hdivR hdivf
      rcases hdivR with ⟨e, heq⟩
      have h_cyl : ∃ (h2 : MvPolynomial (Fin 2) ℝ), h = rename (Fin.castSucc : Fin 2 → Fin 3) h2 :=
        divisor_cylinder_independent hR_ne heq.symm
      rcases h_cyl with ⟨h2, hh2_eq⟩
      rcases hdivf with ⟨q, hq_eq⟩
      have h_disj : IsUnit h ∨ IsUnit q := hf.2 hq_eq
      cases h_disj with
      | inl hunit => exact hunit
      | inr hunitq =>
        have h_f_div_h : f ∣ h := by
          let u : (MvPolynomial (Fin 3) ℝ)ˣ := hunitq.unit
          have hq : q = (↑u : MvPolynomial (Fin 3) ℝ) := hunitq.unit_spec
          let uinv : MvPolynomial (Fin 3) ℝ := ↑u⁻¹
          have hq_inv : q * uinv = 1 := by
            rw [hq] <;> simp [uinv]
          refine' ⟨uinv, _⟩
          have h1 : f * uinv = (h * q) * uinv := by rw [hq_eq]
          have h2 : (h * q) * uinv = h * (q * uinv) := by ring
          rw [h1, h2, hq_inv] <;> ring
        rcases h_f_div_h with ⟨e2, he2_eq⟩
        have h2_ne : h2 ≠ 0 := by
          intro hz
          rw [hh2_eq, hz] at heq
          have hR3_eq0 : R3 = 0 := by simpa using heq
          have hR_eq0 : R = 0 := rename_castSucc_injective hR3_eq0
          exact hR_ne hR_eq0
        have h_f_div_eq : f * e2 = rename (Fin.castSucc : Fin 2 → Fin 3) h2 := by
          rw [←he2_eq, hh2_eq]
        have h_f_cyl : ∃ (f2 : MvPolynomial (Fin 2) ℝ),
            f = rename (Fin.castSucc : Fin 2 → Fin 3) f2 :=
          divisor_cylinder_independent h2_ne h_f_div_eq
        rcases h_f_cyl with ⟨f2, hf2_eq⟩
        have h_pderiv_zero : pderiv 2 f = 0 := by
          rw [hf2_eq]
          have h2_notin : (2 : Fin 3) ∉ (rename (Fin.castSucc : Fin 2 → Fin 3) f2).vars := by
            intro h
            rcases MvPolynomial.mem_vars_rename (Fin.castSucc : Fin 2 → Fin 3) f2 h with ⟨i, _, hi⟩
            have h_contra : (Fin.castSucc i : Fin 3) ≠ (2 : Fin 3) := by
              exact Fin.castSucc_ne_last i
            exact h_contra hi
          exact MvPolynomial.pderiv_eq_zero_of_notMem_vars h2_notin
        exact False.elim (hderiv' h_pderiv_zero)

    have h_main : dimH {p : Point 3 | polynomialValue R3 p = 0 ∧ polynomialValue f p = 0} ≤ 1 :=
      coprime_intersection_case1 hR_ne hf_ne h_R_cop_f

    have h_sub : {p : Point 3 | polynomialValue f p = 0 ∧ polynomialValue g p = 0} ⊆
        {p : Point 3 | polynomialValue R3 p = 0 ∧ polynomialValue f p = 0} := by
      intro p hp
      have h1 : polynomialValue R (proj2 p) = 0 := hR_vanish p hp.1 hp.2
      have h2 : polynomialValue R3 p = 0 := by
        rw [rename_eval_proj2 R p]
        exact h1
      exact ⟨h2, hp.1⟩

    exact le_trans (dimH_mono h_sub) h_main

end Kakeya.CV
