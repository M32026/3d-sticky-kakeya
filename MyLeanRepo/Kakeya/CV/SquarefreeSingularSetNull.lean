import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.SingularSet.GoodDirection
import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.CoprimeIrreducibleIntersection
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.SquarefreeSingularSetNullHelpers
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Negligibility of the squarefree singular locus

Proof structure:
1. If p is a unit, singular set is empty.
2. Otherwise, use `exists_good_direction` to find v.
3. Show p and D_v p are UFD-coprime using `WfDvdMonoid.exists_irreducible_factor`.
4. Singular set ⊆ {p = 0, D_v p = 0}.
5. Coprime intersection theorem gives dimH ≤ 1.
6. 2D Hausdorff measure = 0.
-/

namespace Kakeya.CV

theorem squarefree_singularSet_null :
    SquarefreeSingularSetNullStatement := by
  intro p hp hsq

  by_cases h_unit : IsUnit p
  · -- p is a unit (nonzero constant), so its zero set is empty
    have h_eval_ne_zero : ∀ (x : Point 3), polynomialValue p x ≠ 0 := by
      intro x
      have h2 : IsUnit (polynomialValue p x) :=
        h_unit.map (MvPolynomial.aeval x).toRingHom
      exact IsUnit.ne_zero h2
    have h_empty : polynomialSingularSet p = ∅ := by
      ext x
      simp only [polynomialSingularSet, Set.mem_empty_iff_false, iff_false, Set.mem_setOf_eq]
      intro h
      exact h_eval_ne_zero x h.1
    have h_goal : HasNegligibleSingularSet p := by
      dsimp only [HasNegligibleSingularSet, codimensionOneMeasure]
      rw [h_empty]
      <;> exact MeasureTheory.measure_empty
    exact h_goal

  · -- p is not a unit
    -- Step 1: Good direction
    rcases exists_good_direction p hp hsq with ⟨v, hv_good⟩
    let dvp := directionalDerivative v p

    -- Step 2: D_v p ≠ 0 (otherwise an irreducible factor of p divides 0)
    have hdvp_ne : dvp ≠ 0 := by
      by_contra hz
      rcases WfDvdMonoid.exists_irreducible_factor h_unit hp with ⟨q, hq_irred, hq_div_p⟩
      have h2 : q ∣ dvp := by rw [hz] <;> exact dvd_zero q
      exact hv_good q hq_irred hq_div_p h2

    -- Step 3: p and D_v p are UFD-coprime
    have hcop : ∀ (d : MvPolynomial (Fin 3) ℝ), d ∣ p → d ∣ dvp → IsUnit d := by
      intro d hdp hdd
      by_contra hnu
      have h_d_ne_zero : d ≠ 0 := by
        intro hz
        rw [hz] at hdp
        exact hp (zero_dvd_iff.mp hdp)
      rcases WfDvdMonoid.exists_irreducible_factor hnu h_d_ne_zero with ⟨q, hq_irred, hq_div_d⟩
      have hq_div_p : q ∣ p := dvd_trans hq_div_d hdp
      have hq_div_dvp : q ∣ dvp := dvd_trans hq_div_d hdd
      exact hv_good q hq_irred hq_div_p hq_div_dvp

    -- Step 4: Singular set ⊆ {p = 0, D_v p = 0}
    have hsub : polynomialSingularSet p ⊆
        {x | polynomialValue p x = 0 ∧ polynomialValue dvp x = 0} :=
      singularSet_subset_directionalDerivative_zero v p

    -- Step 5: Factor p into irreducibles and bound dimH of common zero set
    let factors := UniqueFactorizationMonoid.factors p
    let Sfin : Finset (MvPolynomial (Fin 3) ℝ) := factors.toFinset

    have h_irr : ∀ q ∈ Sfin, Irreducible q := by
      intro q hq
      exact UniqueFactorizationMonoid.irreducible_of_factor q
        (Multiset.mem_toFinset.mp hq)

    have h_cop_each : ∀ q ∈ Sfin,
        ∀ (h : MvPolynomial (Fin 3) ℝ), h ∣ q → h ∣ dvp → IsUnit h := by
      intro q hq h hdiv_q hdiv_dvp
      by_cases hunit : IsUnit h
      · exact hunit
      · have h_assoc : Associated q h :=
          (Irreducible.dvd_iff (h_irr q hq)).mp hdiv_q |>.resolve_left hunit
        have hq_div_dvp : q ∣ dvp := h_assoc.dvd.trans hdiv_dvp
        have hq_div_p : q ∣ p :=
          UniqueFactorizationMonoid.dvd_of_mem_factors (Multiset.mem_toFinset.mp hq)
        exact False.elim ((hv_good q (h_irr q hq) hq_div_p) hq_div_dvp)

    let Z : Set (Point 3) :=
      {x | polynomialValue p x = 0 ∧ polynomialValue dvp x = 0}
    let U : Set (Point 3) :=
      ⋃ q ∈ Sfin, {x | polynomialValue q x = 0 ∧ polynomialValue dvp x = 0}

    have hZ_sub : Z ⊆ U := by
      intro x hx
      have hf0 : polynomialValue p x = 0 := hx.1
      have hg0 : polynomialValue dvp x = 0 := hx.2
      have h5 : ∃ q ∈ factors, polynomialValue q x = 0 :=
        factor_product_zero_implies_factor_zero hp x hf0
      rcases h5 with ⟨q, hq_in, hq0⟩
      have hq_fin : q ∈ Sfin := Multiset.mem_toFinset.mpr hq_in
      exact Set.mem_iUnion₂.mpr ⟨q, hq_fin, hq0, hg0⟩

    have h_each : ∀ q ∈ Sfin,
        dimH {x : Point 3 | polynomialValue q x = 0 ∧ polynomialValue dvp x = 0} ≤ 1 := by
      intro q hq
      exact coprime_irreducible_intersection_dimH_le_one
        (h_irr q hq) (h_cop_each q hq)

    have hU_dim : dimH U ≤ 1 := finite_union_dimH_le_one h_each

    have hdim : dimH Z ≤ 1 := le_trans (dimH_mono hZ_sub) hU_dim

    -- Step 6: dimH singular set ≤ 1
    have hdim2 : dimH (polynomialSingularSet p) ≤ 1 :=
      le_trans (dimH_mono hsub) hdim

    -- Step 7: 2D Hausdorff measure = 0 since dimH < 2
    have hlt : dimH (polynomialSingularSet p) < ↑(2 : NNReal) := by
      have h9 : dimH (polynomialSingularSet p) ≤ 1 := hdim2
      exact h9.trans_lt (by norm_num)
    have h_main2 : (MeasureTheory.Measure.hausdorffMeasure (2 : ℝ)) (polynomialSingularSet p) = 0 := by
      have h' : (MeasureTheory.Measure.hausdorffMeasure ↑(2 : NNReal)) (polynomialSingularSet p) = 0 :=
        hausdorffMeasure_of_dimH_lt (d := (2 : NNReal)) hlt
      simpa using h'
    have h_cod : codimensionOneMeasure 3 (polynomialSingularSet p) =
        MeasureTheory.Measure.hausdorffMeasure (2 : ℝ) (polynomialSingularSet p) := by
      simp [codimensionOneMeasure] <;> norm_num
    simpa [HasNegligibleSingularSet, h_cod] using h_main2

end Kakeya.CV
