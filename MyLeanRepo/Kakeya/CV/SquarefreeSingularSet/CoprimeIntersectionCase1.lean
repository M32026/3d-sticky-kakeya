import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.CoprimeIntersectionCase1Helpers
import Mathlib.Topology.MetricSpace.HausdorffDimension


/-!
# Case 1 of coprime intersection theorem

Common zero set of a 2-variable polynomial cylinder and a 3-variable polynomial,
when they are coprime, has Hausdorff dimension at most 1.

Proof by strong induction on `totalDegree g + totalDegree f`.
-/

noncomputable section

open MeasureTheory Metric Set MvPolynomial UniqueFactorizationMonoid Polynomial
open scoped ENNReal

namespace Kakeya.CV

/-- Induction motive for Case 1. -/
def coprime_intersection_case1_P (m : ℕ) : Prop :=
  ∀ (g' : MvPolynomial (Fin 2) ℝ) (f' : MvPolynomial (Fin 3) ℝ),
    totalDegree g' + totalDegree f' = m →
    g' ≠ 0 → f' ≠ 0 →
    (∀ h, h ∣ rename (Fin.castSucc : Fin 2 → Fin 3) g' → h ∣ f' → IsUnit h) →
    dimH {p : Point 3 |
      polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) g') p = 0 ∧
      polynomialValue f' p = 0} ≤ 1

/-- Unit subcase: g2 is a unit, so d2 is associated to g'. -/
private lemma coprime_intersection_unit_branch
    {g' d2 g2 : MvPolynomial (Fin 2) ℝ} {f' : MvPolynomial (Fin 3) ℝ}
    (hg' : g' ≠ 0) (hf' : f' ≠ 0)
    (hcop' : ∀ h, h ∣ rename (Fin.castSucc : Fin 2 → Fin 3) g' → h ∣ f' → IsUnit h)
    (h_g'_eq : g' = d2 * g2)
    (hg2_unit : IsUnit g2)
    (hd2_nonunit : ¬ IsUnit d2)
    (hd2_dvd_pderiv : (rename (Fin.castSucc : Fin 2 → Fin 3) d2) ∣ pderiv 2 f') :
    dimH {p : Point 3 | polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) g') p = 0 ∧ polynomialValue f' p = 0} ≤ 1 := by
  let g3' := rename (Fin.castSucc : Fin 2 → Fin 3) g'
  let Z : Set (Point 3) := {p | polynomialValue g3' p = 0 ∧ polynomialValue f' p = 0}
  have h2 : Associated d2 g' := by
    rcases hg2_unit with ⟨u, hu⟩
    have h_eq1 : g' = d2 * (↑u : MvPolynomial (Fin 2) ℝ) := by
      rw [h_g'_eq, hu]
    exact ⟨u, h_eq1.symm⟩
  let h_ren : MvPolynomial (Fin 2) ℝ →+* MvPolynomial (Fin 3) ℝ :=
    (rename (Fin.castSucc : Fin 2 → Fin 3)).toRingHom
  have h3 : Associated (h_ren d2) (h_ren g') := h2.map h_ren
  have h_g3_div : g3' ∣ pderiv 2 f' := by
    have h4 : Associated (rename (Fin.castSucc : Fin 2 → Fin 3) d2) g3' := by
      convert h3 using 1 <;> rfl
    exact h4.symm.dvd.trans hd2_dvd_pderiv
  rcases cylinder_divides_pderiv_then_split hg' h_g3_div with ⟨H, R, h_split⟩
  have hR_ne : R ≠ 0 := by
    intro hz
    have h_split' : f' = g3' * H + (rename (Fin.castSucc : Fin 2 → Fin 3) R) := by
      simpa [g3'] using h_split
    have h4 : f' = g3' * H := by
      rw [h_split']
      have hR0 : (rename (Fin.castSucc : Fin 2 → Fin 3) R) = 0 := by
        rw [hz] <;> simp
      rw [hR0] <;> ring
    have h5 : g3' ∣ f' := ⟨H, h4⟩
    have h6 : IsUnit g3' := hcop' g3' (dvd_refl g3') h5
    have h7 : IsUnit g' := isUnit_rename_castSucc_iff.mp h6
    have h8 : IsUnit (d2 * g2) := by
      rw [←h_g'_eq] <;> exact h7
    have h9 : IsUnit d2 := by
      have h10 : IsUnit d2 ∧ IsUnit g2 := (IsUnit.mul_iff).mp h8
      exact h10.1
    exact hd2_nonunit h9
  have h_cop_R : ∀ (q : MvPolynomial (Fin 2) ℝ), q ∣ g' → q ∣ R → IsUnit q := by
    intro q hq1 hq2
    let q3 := rename (Fin.castSucc : Fin 2 → Fin 3) q
    have h1 : q3 ∣ g3' := h_ren.map_dvd hq1
    have h2 : q3 ∣ (rename (Fin.castSucc : Fin 2 → Fin 3) R) := h_ren.map_dvd hq2
    have h_split' : f' = g3' * H + (rename (Fin.castSucc : Fin 2 → Fin 3) R) := by
      simpa [g3'] using h_split
    have h3 : q3 ∣ f' := by
      rw [h_split']
      exact dvd_add (dvd_mul_of_dvd_left h1 H) h2
    have h4 : IsUnit q3 := hcop' q3 h1 h3
    exact isUnit_rename_castSucc_iff.mp h4
  let base_set : Set (Point 2) := {x | polynomialValue g' x = 0 ∧ polynomialValue R x = 0}
  have h_base_finite : Set.Finite base_set :=
    coprime_plane_curves_finite hg' hR_ne h_cop_R
  have hZ_eq : Z = {p : Point 3 | ∃ b ∈ base_set, p 0 = b 0 ∧ p 1 = b 1} := by
    ext p
    simp only [Z, Set.mem_setOf_eq]
    have hg3 : polynomialValue g3' p = polynomialValue g' (proj2 p) := rename_eval_proj2 g' p
    have hR' : polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) R) p =
        polynomialValue R (proj2 p) := rename_eval_proj2 R p
    have h_split' : f' = g3' * H + (rename (Fin.castSucc : Fin 2 → Fin 3) R) := by
      simpa [g3'] using h_split
    have h_f'_eval : polynomialValue f' p =
        polynomialValue g3' p * polynomialValue H p +
        polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) R) p := by
      rw [h_split']
      unfold polynomialValue
      rw [map_add, map_mul]
      <;> rfl
    constructor
    · intro h
      have h9 : polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) R) p = 0 := by
        rw [h_f'_eval, h.1] at h <;> linarith
      have h_mem : proj2 p ∈ base_set := by
        simp only [base_set, Set.mem_setOf_eq]
        exact ⟨by rw [← hg3]; exact h.1, by rw [← hR']; exact h9⟩
      refine ⟨proj2 p, h_mem, ?_⟩
      have h_eq1 : p 0 = (proj2 p) 0 := by simp [proj2]
      have h_eq2 : p 1 = (proj2 p) 1 := by simp [proj2]
      exact ⟨h_eq1, h_eq2⟩
    · rintro ⟨b, hb, h_eq⟩
      have hpb : proj2 p = b := by
        ext i; fin_cases i <;> simp [proj2, h_eq] <;> tauto
      have hg3' : polynomialValue g3' p = polynomialValue g' b := by rw [hg3, hpb]
      have hR'' : polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) R) p =
          polynomialValue R b := by rw [hR', hpb]
      have h10 : polynomialValue f' p = 0 := by
        rw [h_f'_eval, hg3', hR'', hb.1, hb.2] <;> ring
      exact ⟨by rw [hg3']; exact hb.1, h10⟩
  have h_goal : dimH Z ≤ 1 := by
    rw [hZ_eq]
    exact finite_base_cylinder_dimH_le_one h_base_finite
  simpa [Z, g3'] using h_goal

/-- Nonunit subcase: both d2 and g2 are non-units, apply induction. -/
private lemma coprime_intersection_nonunit_branch (m : ℕ)
    {g' d2 g2 : MvPolynomial (Fin 2) ℝ} {f' : MvPolynomial (Fin 3) ℝ}
    (hdeg : totalDegree g' + totalDegree f' = m)
    (hg' : g' ≠ 0) (hf' : f' ≠ 0)
    (hcop' : ∀ h, h ∣ rename (Fin.castSucc : Fin 2 → Fin 3) g' → h ∣ f' → IsUnit h)
    (h_g'_eq : g' = d2 * g2)
    (hd2_nonunit : ¬ IsUnit d2)
    (hg2_nonunit : ¬ IsUnit g2)
    (hd2_ne : d2 ≠ 0)
    (hg2_ne : g2 ≠ 0)
    (ih : ∀ k, k < m → coprime_intersection_case1_P k) :
    dimH {p : Point 3 | polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) g') p = 0 ∧ polynomialValue f' p = 0} ≤ 1 := by
  let g3' := rename (Fin.castSucc : Fin 2 → Fin 3) g'
  let Z : Set (Point 3) := {p | polynomialValue g3' p = 0 ∧ polynomialValue f' p = 0}
  have h_d2_deg : totalDegree d2 < totalDegree g' := by
    have h9 : totalDegree (d2 * g2) = totalDegree d2 + totalDegree g2 :=
      MvPolynomial.totalDegree_mul_of_isDomain hd2_ne hg2_ne
    have h10 : totalDegree g' = totalDegree (d2 * g2) := by rw [h_g'_eq]
    have h11 : totalDegree g' = totalDegree d2 + totalDegree g2 := by rw [h10, h9]
    have h12 : 0 < totalDegree g2 := by
      by_contra h13
      have h14 : totalDegree g2 = 0 := by omega
      have h15 : g2 = MvPolynomial.C (coeff 0 g2) := totalDegree_eq_zero_iff_eq_C.mp h14
      have h16 : IsUnit g2 := by
        rw [h15]
        have h17 : coeff 0 g2 ≠ 0 := by
          intro h18
          have h19 : g2 = 0 := by rw [h15, h18] <;> simp
          exact hg2_ne h19
        exact (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mpr
          ⟨coeff 0 g2, isUnit_iff_ne_zero.mpr h17, rfl⟩
      exact False.elim (hg2_nonunit h16)
    omega
  have h_g2_deg : totalDegree g2 < totalDegree g' := by
    have h9 : totalDegree (d2 * g2) = totalDegree d2 + totalDegree g2 :=
      MvPolynomial.totalDegree_mul_of_isDomain hd2_ne hg2_ne
    have h10 : totalDegree g' = totalDegree (d2 * g2) := by rw [h_g'_eq]
    have h11 : totalDegree g' = totalDegree d2 + totalDegree g2 := by rw [h10, h9]
    have h12 : 0 < totalDegree d2 := by
      by_contra h13
      have h14 : totalDegree d2 = 0 := by omega
      have h15 : d2 = MvPolynomial.C (coeff 0 d2) := totalDegree_eq_zero_iff_eq_C.mp h14
      have h16 : IsUnit d2 := by
        rw [h15]
        have h17 : coeff 0 d2 ≠ 0 := by
          intro h18
          have h19 : d2 = 0 := by rw [h15, h18] <;> simp
          exact hd2_ne h19
        exact (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mpr
          ⟨coeff 0 d2, isUnit_iff_ne_zero.mpr h17, rfl⟩
      exact False.elim (hd2_nonunit h16)
    omega
  have h_sum1 : totalDegree d2 + totalDegree f' < m := by
    linarith [hdeg, h_d2_deg]
  have h_sum2 : totalDegree g2 + totalDegree f' < m := by
    linarith [hdeg, h_g2_deg]
  have h_cop_d2 : ∀ (h : MvPolynomial (Fin 3) ℝ), h ∣ rename (Fin.castSucc : Fin 2 → Fin 3) d2 → h ∣ f' → IsUnit h := by
    intro h h1 h2
    have h3 : h ∣ g3' := by
      have h4 : g3' = (rename (Fin.castSucc : Fin 2 → Fin 3) d2) * (rename (Fin.castSucc : Fin 2 → Fin 3) g2) := by
        rw [← map_mul, ← h_g'_eq] <;> rfl
      rw [h4]
      exact dvd_mul_of_dvd_left h1 _
    exact hcop' h h3 h2
  have h_cop_g2 : ∀ (h : MvPolynomial (Fin 3) ℝ), h ∣ rename (Fin.castSucc : Fin 2 → Fin 3) g2 → h ∣ f' → IsUnit h := by
    intro h h1 h2
    have h3 : h ∣ g3' := by
      have h4 : g3' = (rename (Fin.castSucc : Fin 2 → Fin 3) d2) * (rename (Fin.castSucc : Fin 2 → Fin 3) g2) := by
        rw [← map_mul, ← h_g'_eq] <;> rfl
      rw [h4]
      exact dvd_mul_of_dvd_right h1 _
    exact hcop' h h3 h2
  have h_decomp2 : Z = {p | polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) d2) p = 0 ∧ polynomialValue f' p = 0} ∪
      {p | polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) g2) p = 0 ∧ polynomialValue f' p = 0} := by
    ext p
    simp only [Z, Set.mem_union, Set.mem_setOf_eq]
    have h7 : polynomialValue g3' p =
        polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) d2) p *
        polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) g2) p := by
      have h8 : g3' = (rename (Fin.castSucc : Fin 2 → Fin 3) d2) *
          (rename (Fin.castSucc : Fin 2 → Fin 3) g2) := by
        rw [← map_mul, ← h_g'_eq] <;> rfl
      rw [h8]
      simp [polynomialValue, MvPolynomial.eval_mul] <;> ring
    rw [h7] <;> simp [mul_eq_zero] <;> tauto
  have h_main : dimH Z ≤ 1 := by
    rw [h_decomp2, dimH_union]
    have h1_dim : dimH {p | polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) d2) p = 0 ∧ polynomialValue f' p = 0} ≤ 1 :=
      ih (totalDegree d2 + totalDegree f') h_sum1 d2 f' rfl hd2_ne hf' h_cop_d2
    have h2_dim : dimH {p | polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) g2) p = 0 ∧ polynomialValue f' p = 0} ≤ 1 :=
      ih (totalDegree g2 + totalDegree f') h_sum2 g2 f' rfl hg2_ne hf' h_cop_g2
    exact max_le h1_dim h2_dim
  simpa [Z, g3'] using h_main

/-- Non-coprime branch setup: extract d2, g2 from common divisor, then dispatch. -/
private lemma coprime_intersection_noncoprime_branch (m : ℕ)
    {g' : MvPolynomial (Fin 2) ℝ} {f' : MvPolynomial (Fin 3) ℝ}
    {d3 : MvPolynomial (Fin 3) ℝ}
    (hdeg : totalDegree g' + totalDegree f' = m)
    (hg' : g' ≠ 0) (hf' : f' ≠ 0)
    (hcop' : ∀ h, h ∣ rename (Fin.castSucc : Fin 2 → Fin 3) g' → h ∣ f' → IsUnit h)
    (ih : ∀ k, k < m → coprime_intersection_case1_P k)
    (hd3_dvd_g3 : d3 ∣ rename (Fin.castSucc : Fin 2 → Fin 3) g')
    (hd3_dvd_h : d3 ∣ pderiv 2 f')
    (h_d3_nonunit : ¬IsUnit d3) :
    dimH {p : Point 3 | polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) g') p = 0 ∧ polynomialValue f' p = 0} ≤ 1 := by
  let g3' := rename (Fin.castSucc : Fin 2 → Fin 3) g'
  rcases hd3_dvd_g3 with ⟨h1, h_eq1⟩
  rcases divisor_cylinder_independent hg' h_eq1.symm with ⟨d2, hd2_eq⟩
  have hd2_nonunit : ¬IsUnit d2 := by
    intro h
    have h' : IsUnit d3 := by
      rw [hd2_eq]
      exact h.map (rename (Fin.castSucc : Fin 2 → Fin 3)).toRingHom
    exact h_d3_nonunit h'
  have hd2_ne : d2 ≠ 0 := by
    intro hz
    have h_d3_eq : d3 = 0 := by
      rw [hd2_eq, hz] <;> simp
    have h_g3'_eq0 : g3' = 0 := by
      have h : g3' = d3 * h1 := h_eq1
      rw [h, h_d3_eq] <;> simp
    exact hg' (rename_castSucc_injective h_g3'_eq0)
  have h_h1_cylinder : ∃ (g2 : MvPolynomial (Fin 2) ℝ),
      h1 = rename (Fin.castSucc : Fin 2 → Fin 3) g2 := by
    have h_comm : h1 * d3 = g3' := by
      rw [mul_comm]
      exact h_eq1.symm
    exact divisor_cylinder_independent hg' h_comm
  rcases h_h1_cylinder with ⟨g2, hg2_eq⟩
  have h_g'_eq : g' = d2 * g2 := by
    have h5 : g3' = (rename (Fin.castSucc : Fin 2 → Fin 3) d2) *
        (rename (Fin.castSucc : Fin 2 → Fin 3) g2) := by
      rw [← hd2_eq, ← hg2_eq] <;> exact h_eq1
    have h6 : (rename (Fin.castSucc : Fin 2 → Fin 3)) (d2 * g2) = g3' := by
      rw [map_mul] <;> exact h5.symm
    have h7 : (rename (Fin.castSucc : Fin 2 → Fin 3)) (d2 * g2) =
        (rename (Fin.castSucc : Fin 2 → Fin 3)) g' := by
      simpa [g3'] using h6
    exact (rename_castSucc_injective h7).symm
  have hg2_ne : g2 ≠ 0 := by
    intro hz
    rw [h_g'_eq, hz] at hg' <;> simp at hg' <;> exact hg'
  by_cases hg2_unit : IsUnit g2
  · exact coprime_intersection_unit_branch hg' hf' hcop' h_g'_eq hg2_unit hd2_nonunit
      (hd2_eq ▸ hd3_dvd_h)
  · exact coprime_intersection_nonunit_branch m hdeg hg' hf' hcop' h_g'_eq hd2_nonunit hg2_unit hd2_ne hg2_ne ih

private lemma coprime_intersection_case1_step (m : ℕ)
    (ih : ∀ k, k < m → coprime_intersection_case1_P k) :
    coprime_intersection_case1_P m := by
  intro g' f' hdeg hg' hf' hcop'
  let g3' := rename (Fin.castSucc : Fin 2 → Fin 3) g'
  let Z : Set (Point 3) := {p | polynomialValue g3' p = 0 ∧ polynomialValue f' p = 0}
  have h_goal : dimH Z ≤ 1 := by
    by_cases hfz : pderiv 2 f' = 0
    · exact coprime_intersection_independent_z hg' hf' hcop' hfz
    · have hfz' : pderiv 2 f' ≠ 0 := hfz
      by_cases h_cop_h : (∀ h, h ∣ g3' → h ∣ pderiv 2 f' → IsUnit h)
      · -- Coprime branch: regular + singular
        let A_z : Set (Point 3) := {p |
            polynomialValue g3' p = 0 ∧ polynomialValue f' p = 0 ∧
            (polynomialGradient f' p) 2 ≠ 0}
        let Z_sing : Set (Point 3) := {p |
            polynomialValue g3' p = 0 ∧ polynomialValue f' p = 0 ∧
            (polynomialGradient f' p) 2 = 0}
        have h_decomp : Z = A_z ∪ Z_sing := by
          ext p
          simp only [Z, A_z, Z_sing, Set.mem_union, Set.mem_setOf_eq]
          <;> by_cases h : (polynomialGradient f' p) 2 = 0 <;> simp [h] <;> tauto
        have h_reg_eq : A_z = {p | polynomialValue f' p = 0 ∧ polynomialValue g3' p = 0 ∧ (polynomialGradient f' p) 2 ≠ 0} := by
          ext p; simp [A_z, and_comm, and_left_comm] <;> tauto
        have h_reg : dimH A_z ≤ 1 := by
          rw [h_reg_eq]
          exact cylinder_regular_dimH_le_one f' g' hg'
        have h_sing_sub : Z_sing ⊆ {p | polynomialValue g3' p = 0 ∧ polynomialValue (pderiv 2 f') p = 0} := by
          intro x hx
          have h2 : polynomialValue (pderiv 2 f') x = (polynomialGradient f' x) 2 := by
            simp [polynomialGradient] <;> rfl
          exact ⟨hx.1, by rw [h2, hx.2.2]⟩
        have hdeg' : totalDegree g' + totalDegree (pderiv 2 f') < m := by
          have h5 : totalDegree (pderiv 2 f') < totalDegree f' :=
            SingularSet.totalDegree_pderiv_lt hfz'
          linarith [hdeg]
        have h_sing_dim : dimH {p | polynomialValue g3' p = 0 ∧ polynomialValue (pderiv 2 f') p = 0} ≤ 1 :=
          ih (totalDegree g' + totalDegree (pderiv 2 f')) hdeg' g' (pderiv 2 f')
            rfl hg' hfz' h_cop_h
        have h_sing_dim2 : dimH Z_sing ≤ 1 :=
          le_trans (dimH_mono h_sing_sub) h_sing_dim
        have h_main : dimH Z ≤ 1 := by
          rw [h_decomp, dimH_union]
          exact max_le h_reg h_sing_dim2
        exact h_main
      · -- Non-coprime branch
        have h_exists : ∃ (d3 : MvPolynomial (Fin 3) ℝ),
            d3 ∣ g3' ∧ d3 ∣ pderiv 2 f' ∧ ¬IsUnit d3 := by
          push Not at h_cop_h
          exact h_cop_h
        rcases h_exists with ⟨d3, hd3_dvd_g3, hd3_dvd_h, h_d3_nonunit⟩
        exact coprime_intersection_noncoprime_branch m hdeg hg' hf' hcop' ih hd3_dvd_g3 hd3_dvd_h h_d3_nonunit
  simpa [Z, g3'] using h_goal

/-- Case 1: common zero set of a cylinder polynomial and a 3-variable polynomial. -/
lemma coprime_intersection_case1 {g : MvPolynomial (Fin 2) ℝ} {f : MvPolynomial (Fin 3) ℝ}
    (hg : g ≠ 0) (hf : f ≠ 0)
    (hcop : ∀ h, h ∣ (rename (Fin.castSucc : Fin 2 → Fin 3) g) → h ∣ f → IsUnit h) :
    dimH {p : Point 3 |
      polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) g) p = 0 ∧
      polynomialValue f p = 0} ≤ 1 := by
  let n : ℕ := totalDegree g + totalDegree f
  have h_main : ∀ m, coprime_intersection_case1_P m :=
    fun m => Nat.strong_induction_on m coprime_intersection_case1_step
  have h_n : coprime_intersection_case1_P n := h_main n
  exact h_n g f rfl hg hf hcop

end Kakeya.CV
