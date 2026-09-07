import MyLeanRepo.Kakeya.CV.Geometry
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Helper lemmas for squarefree_singularSet_null

Extracted to keep the target file small and avoid OOM during compilation.
-/

noncomputable section

open MeasureTheory Metric Set MvPolynomial UniqueFactorizationMonoid

namespace Kakeya.CV

/-- If the product of irreducible factors evaluates to zero at a point,
    one factor evaluates to zero. -/
lemma factor_product_zero_implies_factor_zero
    {p : MvPolynomial (Fin 3) ℝ} (hp : p ≠ 0) (x : Point 3)
    (hfx : polynomialValue p x = 0) :
    ∃ q ∈ UniqueFactorizationMonoid.factors p, polynomialValue q x = 0 := by
  let factors := UniqueFactorizationMonoid.factors p
  have h_exists : ∃ (u : (MvPolynomial (Fin 3) ℝ)ˣ),
      factors.prod * (↑u : MvPolynomial (Fin 3) ℝ) = p :=
    UniqueFactorizationMonoid.factors_prod hp
  let u : (MvPolynomial (Fin 3) ℝ)ˣ := Classical.choose h_exists
  have h_eq : factors.prod * (↑u : MvPolynomial (Fin 3) ℝ) = p :=
    Classical.choose_spec h_exists
  let eval_at_x := MvPolynomial.eval (fun i : Fin 3 => x i)
  have h_u_eval : eval_at_x (↑u : MvPolynomial (Fin 3) ℝ) ≠ 0 :=
    IsUnit.ne_zero (eval_at_x.isUnit_map u.isUnit)
  have h4 : eval_at_x factors.prod = 0 := by
    have h5 : eval_at_x (factors.prod * (↑u : MvPolynomial (Fin 3) ℝ)) =
        eval_at_x factors.prod * eval_at_x (↑u : MvPolynomial (Fin 3) ℝ) := by
      simp [map_mul]
    have h6 : eval_at_x (factors.prod * (↑u : MvPolynomial (Fin 3) ℝ)) = eval_at_x p := by
      rw [h_eq]
    rw [h6] at h5
    have hfx' : eval_at_x p = 0 := hfx
    rw [hfx'] at h5
    exact (mul_eq_zero.mp h5.symm).resolve_right h_u_eval
  have h_map : eval_at_x factors.prod = (factors.map eval_at_x).prod :=
    eval_at_x.map_multiset_prod factors
  rw [h_map] at h4
  have h6 : ∃ (r : ℝ), r ∈ factors.map eval_at_x ∧ r = 0 := by
    have h7 : 0 ∈ factors.map eval_at_x := by
      rw [Multiset.prod_eq_zero_iff] at h4 <;> exact h4
    exact ⟨0, h7, rfl⟩
  rcases h6 with ⟨r, hr_in, hr0⟩
  rcases Multiset.mem_map.mp hr_in with ⟨q, hq_in, rfl⟩
  exact ⟨q, hq_in, hr0⟩

/-- Finite union of sets each with Hausdorff dimension at most 1
    has Hausdorff dimension at most 1. -/
lemma finite_union_dimH_le_one {S : Finset (MvPolynomial (Fin 3) ℝ)}
    {dvp : MvPolynomial (Fin 3) ℝ}
    (h_each : ∀ q ∈ S,
      dimH {x : Point 3 | polynomialValue q x = 0 ∧ polynomialValue dvp x = 0} ≤ 1) :
    dimH (⋃ q ∈ S, {x : Point 3 | polynomialValue q x = 0 ∧ polynomialValue dvp x = 0}) ≤ 1 := by
  have h_count : (S : Set (MvPolynomial (Fin 3) ℝ)).Countable := S.finite_toSet.countable
  have h_main : dimH (⋃ q ∈ (S : Set (MvPolynomial (Fin 3) ℝ)),
      {x : Point 3 | polynomialValue q x = 0 ∧ polynomialValue dvp x = 0}) ≤ 1 := by
    rw [dimH_bUnion h_count]
    exact iSup_le (fun i => iSup_le (fun hi => h_each i hi))
  simpa [Finset.mem_coe] using h_main

end Kakeya.CV
