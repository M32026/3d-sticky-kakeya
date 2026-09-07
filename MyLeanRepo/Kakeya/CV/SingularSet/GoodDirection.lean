import MyLeanRepo.Kakeya.CV.Geometry
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Good direction lemma for squarefree singular sets

Given a nonzero squarefree polynomial `p` in three real variables, there exists
a direction `v` such that no irreducible factor of `p` divides the directional
derivative `D_v p`.
-/

noncomputable section

open MvPolynomial UniqueFactorizationMonoid

namespace Kakeya.CV

variable {p : MvPolynomial (Fin 3) ℝ}

/-- Directional derivative of a multivariable polynomial. -/
def directionalDerivative (v : Point 3) (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, C (v i) * pderiv i p

/-- Evaluation of the directional derivative equals the inner product with the gradient. -/
lemma directionalDerivative_eval (v : Point 3) (p : MvPolynomial (Fin 3) ℝ)
    (x : Point 3) :
    polynomialValue (directionalDerivative v p) x =
      inner ℝ v (polynomialGradient p x) := by
  have h1 : polynomialValue (directionalDerivative v p) x =
      ∑ i : Fin 3, v i * polynomialValue (pderiv i p) x := by
    simp [directionalDerivative, polynomialValue, map_sum]
  have h2 : inner ℝ v (polynomialGradient p x) =
      ∑ i : Fin 3, v i * polynomialValue (pderiv i p) x := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    have h3 : (polynomialGradient p x) i = polynomialValue (pderiv i p) x := by
      simp [polynomialGradient]
    rw [h3]
    <;> simp [mul_comm]
  rw [h1, h2]

/-- The singular set is contained in the common zero set of `p` and any directional derivative. -/
lemma singularSet_subset_directionalDerivative_zero (v : Point 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    polynomialSingularSet p ⊆
      {x | polynomialValue p x = 0 ∧ polynomialValue (directionalDerivative v p) x = 0} := by
  intro x hx
  have h1 : polynomialValue p x = 0 := hx.1
  have h2 : polynomialGradient p x = 0 := hx.2
  have h3 : polynomialValue (directionalDerivative v p) x =
      inner ℝ v (polynomialGradient p x) :=
    directionalDerivative_eval v p x
  constructor
  · exact h1
  · rw [h3, h2]
    simp

/-- Coefficient of n • q equals n • coeff. -/
private lemma coeff_nsmul (m : Fin 3 →₀ ℕ) (n : ℕ)
    (q : MvPolynomial (Fin 3) ℝ) :
    coeff m (n • q) = n • coeff m q := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      coeff m (n.succ • q)
        = coeff m (n • q + q) := by rw [succ_nsmul]
      _ = coeff m (n • q) + coeff m q := by rw [coeff_add]
      _ = n • coeff m q + coeff m q := by rw [ih]
      _ = n.succ • coeff m q := by rw [succ_nsmul] <;> abel

/-- Helper: coefficient of a weighted monomial sum. -/
private lemma coeff_weighted_sum (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ)
    (m : Fin 3 →₀ ℕ) (hm : m ∈ p.support) :
    coeff m (∑ m' ∈ p.support, (m' i : ℕ) • monomial m' (coeff m' p)) =
      (m i : ℝ) * coeff m p := by
  rw [coeff_sum]
  let f : (Fin 3 →₀ ℕ) → ℝ := fun m' =>
    (m' i : ℝ) * coeff m (monomial m' (coeff m' p))
  have h_step2 : ∑ m' ∈ p.support, coeff m ((m' i : ℕ) • monomial m' (coeff m' p)) =
      ∑ m' ∈ p.support, f m' := by
    apply Finset.sum_congr rfl
    intro m' _
    dsimp only [f]
    have h_smul : coeff m ((m' i : ℕ) • monomial m' (coeff m' p)) =
        (m' i : ℕ) • coeff m (monomial m' (coeff m' p)) :=
      coeff_nsmul m (m' i) (monomial m' (coeff m' p))
    rw [h_smul]
    rw [nsmul_eq_mul]
    <;> norm_cast
  rw [h_step2]
  have h₁ : ∀ (b : Fin 3 →₀ ℕ), b ∈ p.support → b ≠ m → f b = 0 := by
    intro b _ hne
    dsimp only [f]
    rw [coeff_monomial]
    <;> simp [hne]
  have h₂ : m ∉ p.support → f m = 0 := by
    intro hnm
    exfalso
    exact hnm hm
  have h_sum : ∑ m' ∈ p.support, f m' = f m :=
    Finset.sum_eq_single m h₁ h₂
  have h_fm : f m = (m i : ℝ) * coeff m p := by
    dsimp only [f]
    rw [coeff_monomial]
    <;> simp
  rw [h_sum, h_fm]

/-- Key identity: `X i * pderiv i p` is a weighted sum of the monomials of `p`. -/
lemma X_mul_pderiv_eq_sum (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    X i * pderiv i p = ∑ m ∈ p.support, (m i : ℕ) • monomial m (coeff m p) := by
  let s := p.support
  have h_expand : p = ∑ m ∈ s, monomial m (coeff m p) :=
    (support_sum_monomial_coeff p).symm
  have h_map : ∀ (s' : Finset (Fin 3 →₀ ℕ)),
      pderiv i (∑ m ∈ s', monomial m (coeff m p)) =
      ∑ m ∈ s', pderiv i (monomial m (coeff m p)) := by
    intro s'
    induction s' using Finset.induction with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have h_add : pderiv i (monomial a (coeff a p) + ∑ m ∈ s, monomial m (coeff m p)) =
          pderiv i (monomial a (coeff a p)) + pderiv i (∑ m ∈ s, monomial m (coeff m p)) := by
        exact Derivation.map_add (pderiv i) _ _
      rw [h_add, ih]
  have h_sum : pderiv i p = ∑ m ∈ s, pderiv i (monomial m (coeff m p)) := by
    have h_eq1 : pderiv i p = pderiv i (∑ m ∈ s, monomial m (coeff m p)) := by
      apply congr_arg (pderiv i)
      exact h_expand
    have h_eq2 : pderiv i (∑ m ∈ s, monomial m (coeff m p)) =
        ∑ m ∈ s, pderiv i (monomial m (coeff m p)) := h_map s
    rw [h_eq1, h_eq2]
  calc
    X i * pderiv i p
      = X i * (∑ m ∈ s, pderiv i (monomial m (coeff m p))) := by rw [h_sum]
    _ = ∑ m ∈ s, X i * pderiv i (monomial m (coeff m p)) := by rw [Finset.mul_sum]
    _ = ∑ m ∈ s, (m i : ℕ) • monomial m (coeff m p) := by
        apply Finset.sum_congr rfl
        intro m _
        exact X_mul_pderiv_monomial

/-- If all partial derivatives of `p` are zero, then `p` is constant. -/
lemma pderiv_all_zero_eq_const (p : MvPolynomial (Fin 3) ℝ)
    (h : ∀ i : Fin 3, pderiv i p = 0) :
    ∃ c : ℝ, p = C c := by
  have h1 : ∀ (i : Fin 3) (m : (Fin 3 →₀ ℕ)), m ∈ p.support → m i = 0 := by
    intro i m hm
    have h2 : X i * pderiv i p = 0 := by rw [h i]; ring
    have h3 : ∑ m' ∈ p.support, (m' i : ℕ) • monomial m' (coeff m' p) = 0 := by
      rw [←X_mul_pderiv_eq_sum i p, h2]
    have h4 : coeff m (∑ m' ∈ p.support, (m' i : ℕ) • monomial m' (coeff m' p)) = 0 := by
      rw [h3]; simp
    have h5 := coeff_weighted_sum i p m hm
    rw [h5] at h4
    have h6 : coeff m p ≠ 0 := by
      rw [mem_support_iff] at hm; exact hm
    have h7 : (m i : ℝ) = 0 := by
      apply (mul_eq_zero.mp h4).resolve_right h6
    exact_mod_cast h7
  have h_support : p.support ⊆ {0} := by
    intro m hm
    have h8 : ∀ i : Fin 3, m i = 0 := fun i => h1 i m hm
    have h9 : m = 0 := by
      ext i
      exact h8 i
    simpa using h9
  by_cases h0 : p = 0
  · exact ⟨0, by simp [h0]⟩
  · have h11 : p.support.Nonempty := by
      exact support_nonempty.mpr h0
    have h13 : 0 ∈ p.support := by
      obtain ⟨x, hx⟩ := h11
      have h14 : x = 0 := by
        have h15 : x ∈ ({0} : Finset (Fin 3 →₀ ℕ)) := h_support hx
        simpa using h15
      rw [h14] at hx
      exact hx
    have h12 : p.support = {0} := by
      apply Finset.Subset.antisymm h_support
      intro y hy
      simp only [Finset.mem_singleton] at hy
      rw [hy]
      exact h13
    have h14 : p = C (coeff 0 p) := by
      have h15 : p = ∑ m ∈ p.support, monomial m (coeff m p) :=
        (support_sum_monomial_coeff p).symm
      rw [h15, h12]
      <;> simp
    exact ⟨coeff 0 p, h14⟩

/-- If `pderiv i p ≠ 0`, then `totalDegree (pderiv i p) < totalDegree p`. -/
lemma totalDegree_pderiv_lt (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ)
    (h : pderiv i p ≠ 0) :
    totalDegree (pderiv i p) < totalDegree p := by
  have h_id : X i * pderiv i p = ∑ m ∈ p.support, (m i : ℕ) • monomial m (coeff m p) :=
    X_mul_pderiv_eq_sum i p
  have h_support : support (X i * pderiv i p) ⊆ p.support := by
    rw [h_id]
    have h1 : support (∑ m ∈ p.support, (m i : ℕ) • monomial m (coeff m p)) ⊆
        p.support.biUnion (fun m => support ((m i : ℕ) • monomial m (coeff m p))) :=
      support_sum
    have h2 : p.support.biUnion (fun m => support ((m i : ℕ) • monomial m (coeff m p))) ⊆ p.support := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨m, hm, hxm⟩
      have h3 : support ((m i : ℕ) • monomial m (coeff m p)) ⊆ support (monomial m (coeff m p)) :=
        support_smul
      have h4 : x ∈ support (monomial m (coeff m p)) := h3 hxm
      have h6 : coeff m p ≠ 0 := by rw [mem_support_iff] at hm; exact hm
      have h5 : support (monomial m (coeff m p)) = {m} := by
        have h7 : support (monomial m (coeff m p)) =
            if (coeff m p : ℝ) = 0 then (∅ : Finset (Fin 3 →₀ ℕ)) else {m} :=
          MvPolynomial.support_monomial (R := ℝ) (σ := Fin 3)
        rw [h7]
        rw [if_neg h6]
      rw [h5] at h4
      have h7 : x = m := by simpa using h4
      rw [h7]; exact hm
    exact Finset.Subset.trans h1 h2
  have h_eq1 := totalDegree_eq (p := X i * pderiv i p)
  have h_eq2 := totalDegree_eq (p := p)
  have h_td : totalDegree (X i * pderiv i p) ≤ totalDegree p := by
    rw [h_eq1, h_eq2]
    exact Finset.sup_mono h_support
  have h_ne : X i * pderiv i p ≠ 0 := mul_ne_zero (X_ne_zero i) h
  have h_eq : totalDegree (X i * pderiv i p) = totalDegree (X i) + totalDegree (pderiv i p) :=
    totalDegree_mul_of_isDomain (X_ne_zero i) h
  have h_X : totalDegree (X i : MvPolynomial (Fin 3) ℝ) = 1 :=
    totalDegree_X (R := ℝ) (σ := Fin 3) i
  rw [h_eq] at h_td
  rw [h_X] at h_td
  have h_final : 1 + totalDegree (pderiv i p) ≤ totalDegree p := h_td
  have h_last : totalDegree (pderiv i p) + 1 ≤ totalDegree p := by
    rw [add_comm] at h_final
    exact h_final
  exact Nat.lt_of_succ_le h_last

/-- An irreducible nonunit polynomial cannot divide all its partial derivatives. -/
lemma irreducible_not_dvd_all_pderiv (q : MvPolynomial (Fin 3) ℝ)
    (hq : Irreducible q) (hnc : ¬ IsUnit q) :
    ∃ i : Fin 3, ¬ (q ∣ pderiv i q) := by
  by_contra h
  push Not at h
  have h_pos : 0 < totalDegree q := by
    by_contra h'
    have h0 : totalDegree q = 0 := by omega
    have hconst : q = C (coeff 0 q) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
    have hc' : coeff 0 q ≠ 0 := by
      by_contra hc''
      have h_eq0 : q = 0 := by
        rw [hconst, hc''] <;> simp
      exact Irreducible.ne_zero hq h_eq0
    have h_c_isUnit : IsUnit (coeff 0 q) := IsUnit.mk0 (coeff 0 q) hc'
    have hunit : IsUnit (C (coeff 0 q) : MvPolynomial (Fin 3) ℝ) :=
      IsUnit.map (algebraMap ℝ (MvPolynomial (Fin 3) ℝ)) h_c_isUnit
    have hunit' : IsUnit q := by
      rw [hconst]
      exact hunit
    exact hnc hunit'
  have h_exists : ∃ i : Fin 3, pderiv i q ≠ 0 := by
    by_contra h'
    push Not at h'
    have hconst : ∃ c : ℝ, q = C c := pderiv_all_zero_eq_const q h'
    rcases hconst with ⟨c, hc⟩
    have htd : totalDegree q = 0 := by
      rw [hc]; exact totalDegree_C c
    omega
  rcases h_exists with ⟨i, hne⟩
  have hdiv : q ∣ pderiv i q := h i
  rcases hdiv with ⟨hquot, hh⟩
  have h_hne : hquot ≠ 0 := by
    by_contra h'
    rw [h'] at hh
    have : pderiv i q = 0 := by simpa using hh
    exact hne this
  have h1 : totalDegree (pderiv i q) = totalDegree q + totalDegree hquot := by
    rw [hh]
    exact totalDegree_mul_of_isDomain (Irreducible.ne_zero hq) h_hne
  have h2 : totalDegree (pderiv i q) < totalDegree q := totalDegree_pderiv_lt i q hne
  rw [h1] at h2
  omega

/-- For a squarefree `p` and irreducible factor `q`, there exists `i` such that `q ∤ pderiv i p`. -/
lemma squarefree_factor_not_dvd_pderiv (p q : MvPolynomial (Fin 3) ℝ)
    (hp : p ≠ 0) (hsq : Squarefree p) (hq : Irreducible q) (hqdiv : q ∣ p) :
    ∃ i : Fin 3, ¬ (q ∣ pderiv i p) := by
  by_contra h
  push Not at h
  rcases hqdiv with ⟨r, hr⟩
  have hqr : p = q * r := by
    exact ext p (q * r) fun m => congrArg (coeff m) hr
  have hqndivr : ¬ (q ∣ r) := by
    by_contra h3
    rcases h3 with ⟨s, hs⟩
    have h4 : p = q * q * s := by
      calc p = q * r := hqr
           _ = q * (q * s) := by rw [hs]
           _ = q * q * s := by ring
    have h5 : q * q ∣ p := by
      refine ⟨s, ?_⟩
      exact h4
    have h6 : ¬ q * q ∣ p := (squarefree_iff_no_irreducibles hp).mp hsq q hq
    exact h6 h5
  have hqprime : Prime q := Irreducible.prime hq
  have h4 : ∀ i : Fin 3, q ∣ pderiv i q := by
    intro i
    have h_leib : pderiv i (q * r) = q * (pderiv i r) + r * (pderiv i q) :=
      Derivation.leibniz (pderiv i) q r
    have h5 : pderiv i p = (pderiv i q) * r + q * (pderiv i r) := by
      rw [hqr]
      rw [h_leib] <;> ring
    have h6 : q ∣ pderiv i p := h i
    rw [h5] at h6
    have h7 : q ∣ q * (pderiv i r) := by
      refine ⟨pderiv i r, ?_⟩
      <;> ring
    have h8 : q ∣ q * (pderiv i r) + (pderiv i q) * r := by
      have h9 : q * (pderiv i r) + (pderiv i q) * r = (pderiv i q) * r + q * (pderiv i r) := by ring
      rw [h9]
      exact h6
    have h10 : q ∣ (pderiv i q) * r := (dvd_add_right h7).mp h8
    exact (hqprime.dvd_or_dvd h10).resolve_right hqndivr
  have h_contra : ∃ i, ¬ q ∣ pderiv i q :=
    irreducible_not_dvd_all_pderiv q hq (Irreducible.not_isUnit hq)
  rcases h_contra with ⟨i, hi⟩
  exact hi (h4 i)

/-- Helper: if `q` is prime and `c ≠ 0`, then `q ∣ C c * x` implies `q ∣ x`. -/
lemma prime_dvd_unit_mul_left {q x : MvPolynomial (Fin 3) ℝ} {c : ℝ}
    (hq : Prime q) (hc : c ≠ 0) (h : q ∣ C c * x) : q ∣ x := by
  have h' : q ∣ C c ∨ q ∣ x := hq.dvd_or_dvd h
  cases h' with
  | inl hqdiv =>
    have h_c_isUnit : IsUnit c := IsUnit.mk0 c hc
    have hunit : IsUnit (C c : MvPolynomial (Fin 3) ℝ) :=
      IsUnit.map (algebraMap ℝ (MvPolynomial (Fin 3) ℝ)) h_c_isUnit
    have hqnu : ¬ IsUnit q := by
      exact Prime.not_unit hq
    have h_contra : IsUnit q := by
      exact isUnit_of_dvd_unit hqdiv hunit
    exact False.elim (hqnu h_contra)
  | inr h => exact h

/-- If `q` divides `Q(t)` for three distinct values of `t`, then `q` divides all
three partial derivatives of `p`. -/
lemma three_values_implies_all_pderiv (q : MvPolynomial (Fin 3) ℝ) (hq : Prime q)
    (t1 t2 t3 : ℝ) (ht12 : t1 ≠ t2) (ht13 : t1 ≠ t3) (ht23 : t2 ≠ t3)
    (h1 : q ∣ pderiv 0 p + C t1 * pderiv 1 p + C (t1^2) * pderiv 2 p)
    (h2 : q ∣ pderiv 0 p + C t2 * pderiv 1 p + C (t2^2) * pderiv 2 p)
    (h3 : q ∣ pderiv 0 p + C t3 * pderiv 1 p + C (t3^2) * pderiv 2 p) :
    q ∣ pderiv 0 p ∧ q ∣ pderiv 1 p ∧ q ∣ pderiv 2 p := by
  set a := pderiv 0 p with ha
  set b := pderiv 1 p with hb
  set c := pderiv 2 p with hc
  have hdiff1 : q ∣ C (t2 - t1) * (b + C (t2 + t1) * c) := by
    have h : a + C t2 * b + C (t2^2) * c - (a + C t1 * b + C (t1^2) * c) =
        C (t2 - t1) * (b + C (t2 + t1) * c) := by
      simp [C_add] <;> ring
    have h' : q ∣ a + C t2 * b + C (t2^2) * c - (a + C t1 * b + C (t1^2) * c) :=
      dvd_sub h2 h1
    rw [h] at h'
    exact h'
  have hdiff2 : q ∣ C (t3 - t1) * (b + C (t3 + t1) * c) := by
    have h : a + C t3 * b + C (t3^2) * c - (a + C t1 * b + C (t1^2) * c) =
        C (t3 - t1) * (b + C (t3 + t1) * c) := by
      simp [C_add] <;> ring
    have h' : q ∣ a + C t3 * b + C (t3^2) * c - (a + C t1 * b + C (t1^2) * c) :=
      dvd_sub h3 h1
    rw [h] at h'
    exact h'
  have hne12 : (t2 - t1 : ℝ) ≠ 0 := sub_ne_zero.mpr ht12.symm
  have hne13 : (t3 - t1 : ℝ) ≠ 0 := sub_ne_zero.mpr ht13.symm
  have hne23 : (t3 - t2 : ℝ) ≠ 0 := sub_ne_zero.mpr ht23.symm
  have hq1 : q ∣ b + C (t2 + t1) * c :=
    prime_dvd_unit_mul_left hq hne12 hdiff1
  have hq2 : q ∣ b + C (t3 + t1) * c :=
    prime_dvd_unit_mul_left hq hne13 hdiff2
  have hdiff3 : q ∣ C (t3 - t2) * c := by
    have h : (b + C (t3 + t1) * c) - (b + C (t2 + t1) * c) = C (t3 - t2) * c := by
      simp [C_add] <;> ring
    have h' : q ∣ (b + C (t3 + t1) * c) - (b + C (t2 + t1) * c) := dvd_sub hq2 hq1
    rw [h] at h'
    exact h'
  have hqc : q ∣ c := prime_dvd_unit_mul_left hq hne23 hdiff3
  have hqb : q ∣ b := by
    have h : q ∣ C (t2 + t1) * c := dvd_mul_of_dvd_right hqc _
    have h' : q ∣ (b + C (t2 + t1) * c) - C (t2 + t1) * c := dvd_sub hq1 h
    have h'' : (b + C (t2 + t1) * c) - C (t2 + t1) * c = b := by
      simp [C_add] <;> ring
    rw [h''] at h'
    exact h'
  have hqa : q ∣ a := by
    have h : q ∣ C t1 * b + C (t1^2) * c := by
      apply dvd_add
      · exact dvd_mul_of_dvd_right hqb _
      · exact dvd_mul_of_dvd_right hqc _
    have h' : q ∣ (a + C t1 * b + C (t1^2) * c) - (C t1 * b + C (t1^2) * c) := dvd_sub h1 h
    have h'' : (a + C t1 * b + C (t1^2) * c) - (C t1 * b + C (t1^2) * c) = a := by
      simp [C_add] <;> ring
    rw [h''] at h'
    exact h'
  exact ⟨hqa, hqb, hqc⟩

/-- An infinite subset of ℝ contains three distinct elements. -/
lemma infinite_set_exists_triple {S : Set ℝ} (hinf : Set.Infinite S) :
    ∃ (t1 t2 t3 : ℝ), t1 ∈ S ∧ t2 ∈ S ∧ t3 ∈ S ∧
      t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3 := by
  obtain ⟨t1, ht1⟩ := hinf.nonempty
  have hinf2 : Set.Infinite (S \ {t1}) := hinf.sdiff (Set.toFinite _)
  obtain ⟨t2, ht2⟩ := hinf2.nonempty
  have h2 : t2 ∈ S ∧ t2 ≠ t1 := by
    simpa [Set.mem_sdiff_singleton] using ht2
  have ht2S : t2 ∈ S := h2.1
  have hne12 : t1 ≠ t2 := h2.2.symm
  have hinf3 : Set.Infinite (S \ {t1, t2}) := hinf.sdiff (Set.toFinite _)
  obtain ⟨t3, ht3⟩ := hinf3.nonempty
  have h3 : t3 ∈ S ∧ t3 ≠ t1 ∧ t3 ≠ t2 := by
    simpa [Set.mem_sdiff_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] using ht3
  have ht3S : t3 ∈ S := h3.1
  have hne13 : t1 ≠ t3 := h3.2.1.symm
  have hne23 : t2 ≠ t3 := h3.2.2.symm
  exact ⟨t1, t2, t3, ht1, ht2S, ht3S, hne12, hne13, hne23⟩

/-- For a squarefree `p`, there exists a direction `v` such that no irreducible factor
of `p` divides the directional derivative `D_v p`. -/
theorem exists_good_direction (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ≠ 0) (hsq : Squarefree p) :
    ∃ (v : Point 3),
      ∀ (q : MvPolynomial (Fin 3) ℝ), Irreducible q → q ∣ p →
        ¬ (q ∣ directionalDerivative v p) := by
  let factors_finset := (UniqueFactorizationMonoid.factors p).toFinset
  have h_irr : ∀ q ∈ factors_finset, Irreducible q := by
    intro q hq
    exact irreducible_of_factor q (Multiset.mem_toFinset.mp hq)
  have hdiv : ∀ q ∈ factors_finset, q ∣ p := by
    intro q hq
    have h1 : q ∣ (UniqueFactorizationMonoid.factors p).prod :=
      Multiset.dvd_prod (Multiset.mem_toFinset.mp hq)
    have h_prod : Associated (UniqueFactorizationMonoid.factors p).prod p := factors_prod hp
    exact h1.trans (Associated.dvd h_prod)
  have h_not_all : ∀ q ∈ factors_finset, ∃ i : Fin 3, ¬ (q ∣ pderiv i p) :=
    fun q hq => squarefree_factor_not_dvd_pderiv p q hp hsq (h_irr q hq) (hdiv q hq)
  let Q : ℝ → MvPolynomial (Fin 3) ℝ := fun t =>
    pderiv 0 p + C t * pderiv 1 p + C (t^2) * pderiv 2 p
  let v_fun : ℝ → Point 3 := fun t =>
    (EuclideanSpace.equiv (Fin 3) ℝ).symm
      (fun i : Fin 3 => if i = 0 then 1 else if i = 1 then t else t^2)
  have hQ_eq : ∀ (t : ℝ), directionalDerivative (v_fun t) p = Q t := by
    intro t
    simp [directionalDerivative, Q, v_fun, Fin.sum_univ_succ, Fin.sum_univ_zero]
    <;> ring
  have h_bad : ∀ q ∈ factors_finset, Set.Finite {t : ℝ | q ∣ Q t} := by
    intro q hq
    by_contra h
    push Not at h
    have h_inf : Set.Infinite {t : ℝ | q ∣ Q t} := by
      exact Set.not_finite.mp h
    have h3 := infinite_set_exists_triple h_inf
    rcases h3 with ⟨t1, t2, t3, ht1, ht2, ht3, ht12, ht13, ht23⟩
    have hqprime : Prime q := Irreducible.prime (h_irr q hq)
    have hall := three_values_implies_all_pderiv q hqprime t1 t2 t3 ht12 ht13 ht23 ht1 ht2 ht3
    have h_exists := h_not_all q hq
    rcases h_exists with ⟨i, hi⟩
    have hqi : q ∣ pderiv i p := by
      fin_cases i <;> tauto
    exact hi hqi
  let bad_set : Set ℝ := ⋃ q ∈ factors_finset, {t : ℝ | q ∣ Q t}
  have h_bad_finite : Set.Finite bad_set :=
    Set.Finite.biUnion factors_finset.finite_toSet h_bad
  have h_exists_t : ∃ t : ℝ, t ∉ bad_set :=
    Set.Finite.exists_notMem h_bad_finite
  rcases h_exists_t with ⟨t, ht⟩
  let v : Point 3 := v_fun t
  use v
  intro q hqirr hqdiv
  have hqprime : Prime q := Irreducible.prime hqirr
  have h_prod : Associated (UniqueFactorizationMonoid.factors p).prod p := factors_prod hp
  have h1 : q ∣ (UniqueFactorizationMonoid.factors p).prod :=
    hqdiv.trans (Associated.dvd h_prod.symm)
  have h_list_eq : (UniqueFactorizationMonoid.factors p).toList.prod =
      (UniqueFactorizationMonoid.factors p).prod := by simp
  have h1' : q ∣ (UniqueFactorizationMonoid.factors p).toList.prod := by
    rw [h_list_eq]
    exact h1
  have h2 : ∃ q' ∈ (UniqueFactorizationMonoid.factors p).toList, q ∣ q' :=
    (Prime.dvd_prod_iff hqprime).mp h1'
  rcases h2 with ⟨q', hq'_in_list, hqdiv'⟩
  have hq'_in : q' ∈ (UniqueFactorizationMonoid.factors p) := by
    rw [Multiset.mem_toList] at hq'_in_list
    exact hq'_in_list
  have hq'_irr : Irreducible q' := irreducible_of_factor q' hq'_in
  have hq'assoc : Associated q q' :=
    (Irreducible.dvd_irreducible_iff_associated hqirr hq'_irr).mp hqdiv'
  have hq'_fin : q' ∈ factors_finset := Multiset.mem_toFinset.mpr hq'_in
  have h_div_iff : q ∣ directionalDerivative v p ↔ q' ∣ directionalDerivative v p := by
    constructor
    · intro h
      exact hq'assoc.symm.dvd.trans h
    · intro h
      exact hq'assoc.dvd.trans h
  have h_notin : t ∉ {t : ℝ | q' ∣ Q t} := by
    intro h
    have h_in_bad : t ∈ bad_set := by
      simp only [bad_set, Set.mem_iUnion]
      exact ⟨q', hq'_fin, h⟩
    exact ht h_in_bad
  have h_final : ¬ (q' ∣ directionalDerivative v p) := by
    rw [hQ_eq t]
    exact h_notin
  rw [h_div_iff]
  exact h_final

end Kakeya.CV
