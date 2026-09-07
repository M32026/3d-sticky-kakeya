import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.GeometricLemmas
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.CylinderRegular
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.DivisorCylinder
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.AlgebraicLemmas
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.CoprimePlaneCurvesUFD.Finite
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.CoprimeIntersectionCase1Injectivity
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic


/-!
# Helper lemmas for CoprimeIntersectionCase1

Contains plane curve finiteness, polynomial restriction, cylinder dimension,
and polynomial division helpers.
-/

noncomputable section

open MeasureTheory Metric Set MvPolynomial UniqueFactorizationMonoid Polynomial
open scoped ENNReal

namespace Kakeya.CV

/-- Ring hom from 2-var to 3-var polynomials via castSucc. -/
def ren23 : MvPolynomial (Fin 2) ℝ →+* MvPolynomial (Fin 3) ℝ :=
  (MvPolynomial.rename (Fin.castSucc : Fin 2 → Fin 3)).toRingHom

/-- Intersection of two coprime nonzero plane curves is finite. -/
lemma coprime_plane_curves_finite {g h : MvPolynomial (Fin 2) ℝ}
    (hg : g ≠ 0) (hh : h ≠ 0)
    (hcop : ∀ q, q ∣ g → q ∣ h → IsUnit q) :
    Set.Finite {x : Point 2 | polynomialValue g x = 0 ∧ polynomialValue h x = 0} :=
  coprime_plane_curves_finite_ufd hg hh hcop

/-- If pderiv 2 f = 0, then f is in the image of rename castSucc. -/
lemma pderiv2_zero_exists_restriction (f : MvPolynomial (Fin 3) ℝ)
    (hf : pderiv 2 f = 0) :
    ∃ (f2 : MvPolynomial (Fin 2) ℝ), f = rename (Fin.castSucc : Fin 2 → Fin 3) f2 := by
  have h1 : (2 : Fin 3) ∉ f.vars := by
    by_contra h2
    exact SingularSet.pderiv_ne_zero_of_mem_vars h2 hf
  have h3 : ↑f.vars ⊆ Set.range (Fin.castSucc : Fin 2 → Fin 3) := by
    intro i hi
    have h4 : i ≠ 2 := by
      intro h5
      rw [h5] at hi
      exact h1 hi
    fin_cases i <;> simp <;> tauto
  rcases MvPolynomial.exists_rename_eq_of_vars_subset_range f
    (Fin.castSucc : Fin 2 → Fin 3) (Fin.castSucc_injective 2) h3 with ⟨f2, h_eq⟩
  exact ⟨f2, h_eq.symm⟩

/-- Finite base cylinder has dimH ≤ 1. -/
lemma finite_base_cylinder_dimH_le_one {B : Set (Point 2)} (hB : Set.Finite B) :
    dimH {p : Point 3 | ∃ b ∈ B, p 0 = b 0 ∧ p 1 = b 1} ≤ 1 := by
  have h_main : {p : Point 3 | ∃ b ∈ B, p 0 = b 0 ∧ p 1 = b 1} =
      ⋃ b ∈ B, {p : Point 3 | p 0 = b 0 ∧ p 1 = b 1} := by
    ext p
    simp [Set.mem_iUnion]
    <;> aesop
  rw [h_main]
  have h1 : ∀ b ∈ B, dimH {p : Point 3 | p 0 = b 0 ∧ p 1 = b 1} ≤ 1 := by
    intro b _
    let f_b : ℝ → Point 3 := fun t =>
      (EuclideanSpace.equiv (Fin 3) ℝ).symm ![b 0, b 1, t]
    have h_eq : {p : Point 3 | p 0 = b 0 ∧ p 1 = b 1} = Set.range f_b := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_range]
      constructor
      · intro h
        refine ⟨p 2, ?_⟩
        ext i
        fin_cases i <;> simp [f_b, h, EuclideanSpace.equiv] <;> tauto
      · rintro ⟨t, rfl⟩
        simp [f_b, EuclideanSpace.equiv] <;> tauto
    rw [h_eq]
    have h_lip : LipschitzWith 1 f_b := by
      have h : ∀ (x y : ℝ), dist (f_b x) (f_b y) ≤ dist x y := by
        intro x y
        have h1 : f_b x - f_b y = (EuclideanSpace.equiv (Fin 3) ℝ).symm ![0, 0, x - y] := by
          ext i
          fin_cases i <;> simp [f_b, EuclideanSpace.equiv] <;> ring
        have h2 : dist (f_b x) (f_b y) = |x - y| := by
          rw [dist_eq_norm, h1]
          let v : Point 3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm ![0, 0, x - y]
          have h_norm1 : ‖v‖ = Real.sqrt (∑ i : Fin 3, ‖v i‖ ^ 2) := EuclideanSpace.norm_eq v
          rw [h_norm1]
          have hsum : (∑ i : Fin 3, ‖v i‖ ^ 2) = (x - y)^2 := by
            simp [v, EuclideanSpace.equiv, Fin.sum_univ_succ, Real.norm_eq_abs]
            <;> ring
          rw [hsum, Real.sqrt_sq_eq_abs]
        have h3 : dist x y = |x - y| := by
          rw [dist_eq_norm]
          exact Real.norm_eq_abs (x - y)
        rw [h2, h3]
      exact LipschitzWith.mk_one h
    have h_dim : dimH (Set.range f_b) ≤ dimH (Set.univ : Set ℝ) :=
      h_lip.dimH_range_le
    have h_real : dimH (Set.univ : Set ℝ) = 1 := Real.dimH_univ
    rw [h_real] at h_dim
    exact h_dim
  have hB_count : B.Countable := hB.countable
  rw [dimH_bUnion hB_count (fun b => {p : Point 3 | p 0 = b 0 ∧ p 1 = b 1})]
  have h1' : ∀ (i : Point 2), (⨆ (_ : i ∈ B), dimH {p : Point 3 | p 0 = i 0 ∧ p 1 = i 1}) ≤ 1 := by
    intro i
    by_cases hi : i ∈ B
    · simp [hi, h1 i hi]
    · simp [hi]
  exact iSup_le h1'

/-- `polyEquiv (X 2) = Polynomial.X`. -/
private lemma polyEquiv_X2 :
    polyEquiv (X 2 : MvPolynomial (Fin 3) ℝ) = Polynomial.X := by
  have h_var : varEquiv 2 = none := by
    simp [varEquiv, finSuccEquiv'] <;> decide
  simp [polyEquiv, AlgEquiv.trans_apply, h_var, optionEquivLeft_X_none]
  <;> rfl

/-- `polyEquiv (X 0) = Polynomial.C (X 0)`. -/
private lemma polyEquiv_X0 :
    polyEquiv (X 0 : MvPolynomial (Fin 3) ℝ) = Polynomial.C (X 0) := by
  have h_var : varEquiv 0 = some 0 := by
    simp [varEquiv, finSuccEquiv'] <;> decide
  simp [polyEquiv, AlgEquiv.trans_apply, h_var, optionEquivLeft_X_some]
  <;> rfl

/-- `polyEquiv (X 1) = Polynomial.C (X 1)`. -/
private lemma polyEquiv_X1 :
    polyEquiv (X 1 : MvPolynomial (Fin 3) ℝ) = Polynomial.C (X 1) := by
  have h_var : varEquiv 1 = some 1 := by
    simp [varEquiv, finSuccEquiv'] <;> decide
  simp [polyEquiv, AlgEquiv.trans_apply, h_var, optionEquivLeft_X_some]
  <;> rfl

/-- `polyEquiv` intertwines `pderiv 2` with `Polynomial.derivative`. -/
lemma pderiv2_polyEquiv (f : MvPolynomial (Fin 3) ℝ) :
    polyEquiv (pderiv 2 f) = Polynomial.derivative (polyEquiv f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h1 : polyEquiv (pderiv 2 (C a)) = 0 := by
      simp [pderiv_C]
    have h2 : Polynomial.derivative (polyEquiv (C a)) = 0 := by
      simp [polyEquiv, optionEquivLeft_C, Polynomial.derivative_C]
    rw [h1, h2]
  | add p q hp hq =>
    have h1 : pderiv 2 (p + q) = pderiv 2 p + pderiv 2 q := by
      exact Derivation.map_add (pderiv 2) p q
    calc
      polyEquiv (pderiv 2 (p + q))
        = polyEquiv (pderiv 2 p + pderiv 2 q) := by rw [h1]
      _ = polyEquiv (pderiv 2 p) + polyEquiv (pderiv 2 q) := by rw [map_add]
      _ = Polynomial.derivative (polyEquiv p) + Polynomial.derivative (polyEquiv q) := by rw [hp, hq]
      _ = Polynomial.derivative (polyEquiv (p + q)) := by rw [←Polynomial.derivative_add, ←map_add]
  | mul_X p i hp =>
    have h2 : pderiv 2 (p * X i) = pderiv 2 p * X i + p * pderiv 2 (X i) := by
      exact pderiv_mul
    have h4 : ∀ (j : Fin 3), polyEquiv (pderiv 2 (X j)) = Polynomial.derivative (polyEquiv (X j)) := by
      intro j
      by_cases h20 : j = 2
      · rw [h20]
        simp [polyEquiv_X2, pderiv_X, Polynomial.derivative_X]
      · by_cases h01 : j = 0
        · rw [h01]
          simp [polyEquiv_X0, pderiv_X]
        · have h12 : j = 1 := by fin_cases j <;> tauto
          rw [h12]
          simp [polyEquiv_X1, pderiv_X]
    calc
      polyEquiv (pderiv 2 (p * X i))
        = polyEquiv (pderiv 2 p * X i + p * pderiv 2 (X i)) := by rw [h2]
      _ = Polynomial.derivative (polyEquiv p) * polyEquiv (X i) + polyEquiv p * polyEquiv (pderiv 2 (X i)) := by
          rw [map_add, map_mul, map_mul, hp]
      _ = Polynomial.derivative (polyEquiv p) * polyEquiv (X i) + polyEquiv p * Polynomial.derivative (polyEquiv (X i)) := by
          rw [h4 i]
      _ = Polynomial.derivative (polyEquiv (p * X i)) := by
          have h5 : Polynomial.derivative (polyEquiv (p * X i)) =
              Polynomial.derivative (polyEquiv p) * polyEquiv (X i) +
              polyEquiv p * Polynomial.derivative (polyEquiv (X i)) := by
            have h6 : polyEquiv (p * X i) = polyEquiv p * polyEquiv (X i) := by rw [map_mul]
            rw [h6, Polynomial.derivative_mul]
          exact h5.symm

/-- If a cylinder polynomial `g3` divides `pderiv 2 f`, then `f = g3 * H + R2`
where `R2` is independent of z. -/
lemma cylinder_divides_pderiv_then_split {g : MvPolynomial (Fin 2) ℝ}
    {f : MvPolynomial (Fin 3) ℝ} (hg : g ≠ 0)
    (hdiv : (rename (Fin.castSucc : Fin 2 → Fin 3) g) ∣ pderiv 2 f) :
    ∃ (H : MvPolynomial (Fin 3) ℝ) (R : MvPolynomial (Fin 2) ℝ),
      f = (rename (Fin.castSucc : Fin 2 → Fin 3) g) * H +
          (rename (Fin.castSucc : Fin 2 → Fin 3) R) := by
  let g3 := rename (Fin.castSucc : Fin 2 → Fin 3) g
  let e := polyEquiv
  have h1 : e g3 = Polynomial.C g := polyEquiv_rename_castSucc g
  have h2 : e (pderiv 2 f) = Polynomial.derivative (e f) := pderiv2_polyEquiv f
  have h3 : Polynomial.C g ∣ Polynomial.derivative (e f) := by
    have h4 : e g3 ∣ e (pderiv 2 f) := map_dvd e hdiv
    rw [h1, h2] at h4
    exact h4
  have h4 : ∀ k, g ∣ (Polynomial.derivative (e f)).coeff k :=
    (Polynomial.C_dvd_iff_dvd_coeff g (Polynomial.derivative (e f))).mp h3
  have h5 : ∀ k, g ∣ (e f).coeff (k + 1) := by
    intro k
    have hk_pos : (k + 1 : ℝ) ≠ 0 := Nat.cast_add_one_ne_zero k
    let c : MvPolynomial (Fin 2) ℝ := MvPolynomial.C (k + 1 : ℝ)
    have hc_unit : IsUnit c := by
      exact (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mpr
        ⟨(k + 1 : ℝ), IsUnit.mk0 (k + 1 : ℝ) hk_pos, rfl⟩
    have h6 : (Polynomial.derivative (e f)).coeff k = (e f).coeff (k + 1) * c := by
      rw [Polynomial.coeff_derivative]
      <;> simp [c]
      <;> norm_cast
      <;> rfl
    have h7 : g ∣ (Polynomial.derivative (e f)).coeff k := h4 k
    rw [h6] at h7
    have h8 : g ∣ (e f).coeff (k + 1) := by
      have h9 : g ∣ (e f).coeff (k + 1) * c := h7
      have h10 : (e f).coeff (k + 1) * c ∣ (e f).coeff (k + 1) := by
        rcases hc_unit with ⟨u, hu⟩
        let d : MvPolynomial (Fin 2) ℝ := ↑u⁻¹
        refine' ⟨d, _⟩
        have h11 : c * d = 1 := by
          simpa [d, hu] using u.mul_inv
        simp [mul_assoc, h11] <;> ring
      exact dvd_trans h9 h10
    exact h8
  let p : Polynomial (MvPolynomial (Fin 2) ℝ) := (e f) - Polynomial.C ((e f).coeff 0)
  have h6 : ∀ k, g ∣ p.coeff k := by
    intro k
    cases k with
    | zero =>
      simp [p, Polynomial.coeff_C] <;> exact dvd_zero g
    | succ k' =>
      have h7 : p.coeff (k' + 1) = (e f).coeff (k' + 1) := by
        have h_ne : k' + 1 ≠ 0 := Nat.succ_ne_zero k'
        simp [p, Polynomial.coeff_C, h_ne] <;> ring
      rw [h7]
      exact h5 k'
  have h7 : Polynomial.C g ∣ p := (Polynomial.C_dvd_iff_dvd_coeff g p).mpr h6
  rcases h7 with ⟨Q, hQ⟩
  have h8 : e f = Polynomial.C ((e f).coeff 0) + Polynomial.C g * Q := by
    have h9 : (e f) - Polynomial.C ((e f).coeff 0) = Polynomial.C g * Q := hQ
    have h10 : e f = Polynomial.C ((e f).coeff 0) + Polynomial.C g * Q := by
      calc
        e f = (e f) - Polynomial.C ((e f).coeff 0) + Polynomial.C ((e f).coeff 0) := by abel
        _ = Polynomial.C g * Q + Polynomial.C ((e f).coeff 0) := by rw [h9] <;> abel
        _ = Polynomial.C ((e f).coeff 0) + Polynomial.C g * Q := by abel
    exact h10
  let R : MvPolynomial (Fin 2) ℝ := (e f).coeff 0
  refine ⟨e.symm Q, R, ?_⟩
  have h10 : e f = e (g3 * e.symm Q + rename (Fin.castSucc : Fin 2 → Fin 3) R) := by
    have h11 : e (g3 * e.symm Q + rename (Fin.castSucc : Fin 2 → Fin 3) R) =
        e g3 * Q + Polynomial.C R := by
      rw [map_add, map_mul, e.apply_symm_apply, polyEquiv_rename_castSucc R]
      <;> rfl
    rw [h11, h1, h8]
    <;> simp [R]
    <;> abel
  exact e.injective h10

/-- Subcase: when f' is independent of z, common zero set of cylinder g' and f' has dimH ≤ 1. -/
lemma coprime_intersection_independent_z
    {g' : MvPolynomial (Fin 2) ℝ} {f' : MvPolynomial (Fin 3) ℝ}
    (hg' : g' ≠ 0) (hf' : f' ≠ 0)
    (hcop' : ∀ h, h ∣ (rename (Fin.castSucc : Fin 2 → Fin 3) g') → h ∣ f' → IsUnit h)
    (hfz : pderiv 2 f' = 0) :
    dimH {p : Point 3 |
      polynomialValue (rename (Fin.castSucc : Fin 2 → Fin 3) g') p = 0 ∧
      polynomialValue f' p = 0} ≤ 1 := by
  let g3' := rename (Fin.castSucc : Fin 2 → Fin 3) g'
  rcases pderiv2_zero_exists_restriction f' hfz with ⟨f2, hf2_eq⟩
  have h_f2_ne : f2 ≠ 0 := by
    intro hz
    rw [hf2_eq, hz] at hf' <;> contradiction
  have h_cop2 : ∀ q, q ∣ g' → q ∣ f2 → IsUnit q := by
    intro q hq1 hq2
    have h1 : ren23 q ∣ g3' := ren23.map_dvd hq1
    have h2 : ren23 q ∣ f' := by
      rw [hf2_eq]
      exact ren23.map_dvd hq2
    have h3 : IsUnit (ren23 q) := hcop' _ h1 h2
    exact isUnit_rename_castSucc_iff.mp h3
  let base_set : Set (Point 2) := {x | polynomialValue g' x = 0 ∧ polynomialValue f2 x = 0}
  have h_base_finite : Set.Finite base_set :=
    coprime_plane_curves_finite hg' h_f2_ne h_cop2
  let Z : Set (Point 3) := {p | polynomialValue g3' p = 0 ∧ polynomialValue f' p = 0}
  have hZ_eq : Z = {p : Point 3 | ∃ b ∈ base_set, p 0 = b 0 ∧ p 1 = b 1} := by
    ext p
    simp only [Z, Set.mem_setOf_eq]
    have hg3 : polynomialValue g3' p = polynomialValue g' (proj2 p) := rename_eval_proj2 g' p
    have hf2' : polynomialValue f' p = polynomialValue f2 (proj2 p) := by
      rw [hf2_eq] <;> exact rename_eval_proj2 f2 p
    constructor
    · intro h
      have h_mem : proj2 p ∈ base_set := by
        simp only [base_set, Set.mem_setOf_eq]
        exact ⟨by rw [← hg3]; exact h.1, by rw [← hf2']; exact h.2⟩
      refine ⟨proj2 p, h_mem, ?_⟩
      have h_eq1 : p 0 = (proj2 p) 0 := by simp [proj2]
      have h_eq2 : p 1 = (proj2 p) 1 := by simp [proj2]
      exact ⟨h_eq1, h_eq2⟩
    · rintro ⟨b, hb, h_eq⟩
      have hpb : proj2 p = b := by
        ext i; fin_cases i <;> simp [proj2, h_eq] <;> tauto
      have hg3' : polynomialValue g3' p = polynomialValue g' b := by rw [hg3, hpb]
      have hf2'' : polynomialValue f' p = polynomialValue f2 b := by rw [hf2', hpb]
      exact ⟨by rw [hg3']; exact hb.1, by rw [hf2'']; exact hb.2⟩
  have h_goal : dimH Z ≤ 1 := by
    rw [hZ_eq]
    exact finite_base_cylinder_dimH_le_one h_base_finite
  exact h_goal

end Kakeya.CV
