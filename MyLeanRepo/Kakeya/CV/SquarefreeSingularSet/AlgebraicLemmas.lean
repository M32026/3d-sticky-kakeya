import MyLeanRepo.Kakeya.CV.Statements
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Data.Finsupp.Order

/-!
# Algebraic lemmas for the squarefree singular set proof

This file proves:
1. `totalDegree_pderiv_lt`: partial derivative strictly lowers total degree
2. `pderiv_ne_zero_of_mem_vars`: over ℝ, derivative w.r.t. a variable in vars is nonzero
3. `irreducible_not_dvd_all_pderiv`: irreducible polynomial can't divide all its partials
4. `squarefree_exists_pderiv_not_dvd`: squarefree p, irreducible factor q ⇒ ∃ i, q ∤ pderiv i p
-/

noncomputable section

open MvPolynomial

namespace Kakeya.CV.SingularSet

variable {σ : Type*} [Finite σ] [DecidableEq σ]

/-- Subtracting one from a coordinate strictly decreases the sum of entries. -/
private lemma finsupp_sum_sub_single_lt (s : σ →₀ ℕ) (i : σ) (hsi : 0 < s i) :
    let one : σ →₀ ℕ := Finsupp.single i (1 : ℕ)
    (s - one).sum (fun _ e => e) < s.sum (fun _ e => e) := by
  let one : σ →₀ ℕ := Finsupp.single i (1 : ℕ)
  let s' : σ →₀ ℕ := s - one
  have h1 : one ≤ s := by
    intro j
    by_cases hji : j = i
    · rw [hji]; simp [one] <;> omega
    · simp [one, hji] <;> omega
  have h2 : s' + one = s := by
    ext j
    have h3 : one j ≤ s j := h1 j
    simp [s', one, Finsupp.tsub_apply, Finsupp.add_apply, h3] <;> omega
  let hhom : σ → ℕ →+ ℕ := fun _ => AddMonoidHom.id ℕ
  have h4 : (s' + one).sum (fun _ e => e) =
      s'.sum (fun _ e => e) + one.sum (fun _ e => e) := by
    exact Finsupp.sum_hom_add_index hhom
  have h5 : one.sum (fun _ e => e) = 1 := by
    simp [one, Finsupp.sum_single_index] <;> rfl
  have h6 : s.sum (fun _ e => e) = s'.sum (fun _ e => e) + 1 := by
    have h7 : (s' + one).sum (fun _ e => e) = s.sum (fun _ e => e) := by
      rw [h2] <;> rfl
    rw [← h7, h4, h5]
  have h9 : s'.sum (fun _ e => e) < s.sum (fun _ e => e) := by
    rw [h6] <;> omega
  exact h9

/-- The total degree of a nonzero partial derivative is strictly less than
the total degree of the original polynomial. -/
lemma totalDegree_pderiv_lt {p : MvPolynomial σ ℝ} {i : σ} (h : pderiv i p ≠ 0) :
    totalDegree (pderiv i p) < totalDegree p := by
  classical
  have has_sum : p = ∑ s ∈ p.support, monomial s (coeff s p) := MvPolynomial.as_sum p
  have h_pos : 0 < totalDegree p := by
    by_contra h0
    have h1 : totalDegree p = 0 := by omega
    have h2 : p = C (coeff 0 p) := totalDegree_eq_zero_iff_eq_C.mp h1
    have h3 : pderiv i p = 0 := by rw [h2]; simp
    exact h h3
  let one : σ →₀ ℕ := Finsupp.single i (1 : ℕ)
  let f : (σ →₀ ℕ) → MvPolynomial σ ℝ := fun s =>
    monomial (s - one) (coeff s p * s i)
  have h_sum : pderiv i (∑ s ∈ p.support, monomial s (coeff s p)) =
      ∑ s ∈ p.support, pderiv i (monomial s (coeff s p)) := by
    exact map_sum (pderiv i) (fun x => monomial x (coeff x p)) p.support
  have h_expr : pderiv i p = ∑ s ∈ p.support, f s := by
    have h1 : pderiv i p = pderiv i (∑ s ∈ p.support, monomial s (coeff s p)) :=
      congr_arg (pderiv i) has_sum
    rw [h1, h_sum]
    apply Finset.sum_congr rfl
    intro s _
    exact pderiv_monomial
  have h3 : ∀ s ∈ p.support, totalDegree (f s) < totalDegree p := by
    intro s hs
    by_cases hc : coeff s p * (s i : ℝ) = 0
    · have h4 : f s = 0 := by simp [f, hc]
      rw [h4]; simp <;> omega
    · have hsi : 0 < s i := by
        by_contra hz
        have hz' : s i = 0 := by omega
        rw [hz'] at hc
        simp at hc
      have h6 : totalDegree (f s) = (s - one).sum (fun _ e => e) := by
        simp [f, hc, totalDegree_monomial] <;> rfl
      rw [h6]
      have h7 : (s - one).sum (fun _ e => e) < s.sum (fun _ e => e) :=
        finsupp_sum_sub_single_lt s i hsi
      have h8 : s.sum (fun _ e => e) ≤ totalDegree p := le_totalDegree hs
      exact h7.trans_le h8
  have h5 : totalDegree (∑ s ∈ p.support, f s) < totalDegree p := by
    have h6 : totalDegree (∑ s ∈ p.support, f s) ≤ p.support.sup (fun s => totalDegree (f s)) :=
      totalDegree_finsetSum _ _
    have h7 : p.support.sup (fun s => totalDegree (f s)) < totalDegree p := by
      apply Finset.sup_lt_iff h_pos |>.mpr
      intro s hs
      exact h3 s hs
    exact h6.trans_lt h7
  rw [h_expr]
  exact h5

/-- If `i ∈ p.vars`, then `pderiv i p ≠ 0` (over ℝ). -/
lemma pderiv_ne_zero_of_mem_vars {p : MvPolynomial σ ℝ} {i : σ} (h : i ∈ p.vars) :
    pderiv i p ≠ 0 := by
  classical
  let d : ℕ := p.support.sup (fun m => m i)
  have h1 : ∃ (s : σ →₀ ℕ), s ∈ p.support ∧ 0 < s i := by
    rw [mem_vars_iff_mem_support] at h
    rcases h with ⟨s, hs, h2⟩
    have h3 : s i ≠ 0 := by simpa [Finsupp.mem_support_iff] using h2
    exact ⟨s, hs, by omega⟩
  have h_support_nonempty : p.support.Nonempty := by
    rcases h1 with ⟨s, hs, _⟩; exact ⟨s, hs⟩
  have hd_pos : 0 < d := by
    rcases h1 with ⟨s, hs, hsi⟩
    have h9 : s i ≤ d := by
      exact Finset.le_sup hs (f := fun m : σ →₀ ℕ => m i)
    omega
  have h_exists_s : ∃ (s0 : σ →₀ ℕ), s0 ∈ p.support ∧ s0 i = d := by
    have h := Finset.exists_mem_eq_sup p.support h_support_nonempty (fun m : σ →₀ ℕ => m i)
    rcases h with ⟨s0, hs0, h_eq⟩
    exact ⟨s0, hs0, h_eq.symm⟩
  rcases h_exists_s with ⟨s0, hs0, hsd⟩
  let one : σ →₀ ℕ := Finsupp.single i (1 : ℕ)
  let t : σ →₀ ℕ := s0 - one
  let f : (σ →₀ ℕ) → MvPolynomial σ ℝ := fun u =>
    monomial (u - one) (coeff u p * u i)
  have h_sum : pderiv i (∑ u ∈ p.support, monomial u (coeff u p)) =
      ∑ u ∈ p.support, pderiv i (monomial u (coeff u p)) := by
    exact map_sum (pderiv i) (fun x => monomial x (coeff x p)) p.support
  have h_expr : pderiv i p = ∑ u ∈ p.support, f u := by
    have has_sum : p = ∑ u ∈ p.support, monomial u (coeff u p) := MvPolynomial.as_sum p
    have h1 : pderiv i p = pderiv i (∑ u ∈ p.support, monomial u (coeff u p)) :=
      congr_arg (pderiv i) has_sum
    rw [h1, h_sum]
    apply Finset.sum_congr rfl
    intro u _
    exact pderiv_monomial
  have h_main : ∀ u ∈ p.support, u ≠ s0 → coeff t (f u) = 0 := by
    intro u hu hne
    by_cases h_eq : (u - one) = t
    · by_cases hui : u i = 0
      · simp [f, hui]
      · have hui_pos : 0 < u i := by omega
        have h11 : u = s0 := by
          ext j
          by_cases hji : j = i
          · rw [hji]
            have h12 : (u - one) i = (s0 - one) i := by rw [h_eq]
            simp [one, Finsupp.tsub_apply, hui_pos, hsd, hd_pos] at h12 <;> omega
          · have h13 : (u - one) j = (s0 - one) j := by rw [h_eq]
            simp [one, hji, Finsupp.tsub_apply] at h13 <;> exact h13
        exact False.elim (hne h11)
    · simp [f, h_eq, MvPolynomial.coeff_monomial]
  have h_sum2 : ∑ u ∈ p.support, coeff t (f u) = coeff t (f s0) := by
    apply Finset.sum_eq_single_of_mem s0 hs0
    intro u hu hne
    exact h_main u hu hne
  have h_s0_coeff : coeff t (f s0) = coeff s0 p * (s0 i : ℝ) := by
    simp [f, t, MvPolynomial.coeff_monomial] <;> rfl
  have h_ne_zero : coeff t (f s0) ≠ 0 := by
    rw [h_s0_coeff, hsd]
    have hc1 : coeff s0 p ≠ 0 := MvPolynomial.mem_support_iff.mp hs0
    have hc2 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 from by omega)
    exact mul_ne_zero hc1 hc2
  have h_coeff : coeff t (pderiv i p) = ∑ u ∈ p.support, coeff t (f u) := by
    rw [h_expr, MvPolynomial.coeff_sum]
  have h10 : coeff t (pderiv i p) ≠ 0 := by
    rw [h_coeff, h_sum2]
    exact h_ne_zero
  intro h11
  have h12 : coeff t (pderiv i p) = 0 := by
    rw [h11] <;> simp
  exact h10 h12

/-- An irreducible polynomial cannot divide all its partial derivatives. -/
lemma irreducible_not_dvd_all_pderiv {q : MvPolynomial (Fin 3) ℝ} (hq : Irreducible q) :
    ¬ (∀ i : Fin 3, q ∣ pderiv i q) := by
  intro h
  have h1 : ∀ i : Fin 3, pderiv i q = 0 := by
    intro i
    by_cases h2 : pderiv i q = 0
    · exact h2
    · have h3 : totalDegree q ≤ totalDegree (pderiv i q) :=
        totalDegree_le_of_dvd_of_isDomain (h i) h2
      have h4 : totalDegree (pderiv i q) < totalDegree q := totalDegree_pderiv_lt h2
      linarith
  have h2 : ∀ i : Fin 3, i ∉ q.vars := by
    intro i
    by_contra h3
    have h4 : pderiv i q ≠ 0 := pderiv_ne_zero_of_mem_vars h3
    exact h4 (h1 i)
  have h3 : q.vars = ∅ := by
    simp [Finset.ext_iff] at * <;> tauto
  have h4 : q = C (coeff 0 q) := vars_eq_empty_iff_eq_C.mp h3
  have hq_ne_zero : q ≠ 0 := Irreducible.ne_zero hq
  have h_coeff_ne_zero : coeff 0 q ≠ 0 := by
    intro h
    have h' : q = 0 := by
      rw [h4, h] <;> simp
    exact hq_ne_zero h'
  have h5 : IsUnit (coeff 0 q) := by
    exact Ne.isUnit h_coeff_ne_zero
  have h6 : IsUnit (C (coeff 0 q) : MvPolynomial (Fin 3) ℝ) :=
    h5.map (C : ℝ →+* MvPolynomial (Fin 3) ℝ)
  rw [h4] at hq
  exact Irreducible.not_isUnit hq h6

/-- For a squarefree polynomial `p`, every irreducible factor `q` fails to divide
at least one partial derivative of `p`. -/
lemma squarefree_exists_pderiv_not_dvd
    {p q : MvPolynomial (Fin 3) ℝ} (hp : Squarefree p)
    (hq : Irreducible q) (hdiv : q ∣ p) :
    ∃ i : Fin 3, ¬ (q ∣ pderiv i p) := by
  rcases hdiv with ⟨r, hr⟩
  have h_eq : p = q * r := hr
  have hq' : Prime q := Irreducible.prime hq
  have hq2 : ¬ (q ∣ r) := by
    intro h5
    have h6 : q ^ 2 ∣ p := by
      rcases h5 with ⟨r', hr'⟩
      have h7 : r = q * r' := hr'
      refine ⟨r', ?_⟩
      calc p = q * r := h_eq
           _ = q * (q * r') := by rw [h7]
           _ = q ^ 2 * r' := by ring
    have h9 : ¬ IsUnit q := Irreducible.not_isUnit hq
    have h6' : q * q ∣ p := by simpa [pow_two] using h6
    have h10 : IsUnit q := hp q h6'
    exact h9 h10
  by_contra h
  have h' : ∀ i : Fin 3, q ∣ pderiv i p := by
    intro i
    by_contra h2
    exact h ⟨i, h2⟩
  have h3 : ∀ i : Fin 3, q ∣ pderiv i q := by
    intro i
    have h4 : pderiv i p = (pderiv i q) * r + q * (pderiv i r) := by
      rw [h_eq]
      rw [pderiv_mul] <;> ring
    have h6 : q ∣ pderiv i p := h' i
    rw [h4] at h6
    have h71 : q ∣ q * (pderiv i r) := dvd_mul_right q (pderiv i r)
    have h7 : q ∣ (pderiv i q) * r := (dvd_add_left h71).mp h6
    have h8 : q ∣ (pderiv i q) ∨ q ∣ r := Prime.dvd_or_dvd hq' h7
    cases h8 with
    | inl h8 => exact h8
    | inr h8 => exfalso; exact hq2 h8
  exact irreducible_not_dvd_all_pderiv hq h3

end Kakeya.CV.SingularSet
