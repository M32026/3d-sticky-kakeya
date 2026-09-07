import MyLeanRepo.Kakeya.CV.PolynomialMollification
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Dimension lemmas for generic polynomial regularity

This file contains the combinatorial and linear-algebraic dimension counts
needed to show that non-squarefree polynomials form a negligible subset of
bounded-degree coefficient space.

## Main results

* `choose_dimension_ineq`: `C(d+3,3) + C(k-2d+3,3) < C(k+3,3)`
* `finrank_degreeLESubmodule`: `finrank ℝ (degreeLESubmodule k) = C(k+3,3)`
* `finrank_product_ineq`: product subspace has strictly smaller dimension

## Proof sketch

The dimension of polynomials of total degree ≤ k in 3 variables is the number
of monomials `x^a y^b z^c` with `a+b+c ≤ k`, which by stars-and-bars equals
`C(k+3,3)`. The multiplication map from degree ≤ d times degree ≤ k-2d into
degree ≤ k cannot be surjective because its domain has dimension
`C(d+3,3) + C(k-2d+3,3) < C(k+3,3)`.
-/

namespace Kakeya.CV

open Finset Nat

/-! ### Combinatorial inequality -/

/-- Pascal's identity for choose 3: `C(n+1,3) = C(n,3) + C(n,2)`. -/
lemma choose_pascal3 (n : ℕ) :
    Nat.choose (n + 1) 3 = Nat.choose n 3 + Nat.choose n 2 := by
  have h := Nat.choose_succ_succ n 2
  have h' : Nat.choose (n + 1) 3 = Nat.choose n 3 + Nat.choose n 2 := by
    convert h using 1 <;> ring
  exact h'

/-- Auxiliary hockey-stick identity:
`C(m+3,3) + ∑_{j=0}^{n-1} C(m+3+j,2) = C(m+n+3,3)`. -/
lemma choose_sum_aux (m n : ℕ) :
    Nat.choose (m + 3) 3 + ∑ j ∈ Finset.range n, Nat.choose (m + 3 + j) 2 =
    Nat.choose (m + n + 3) 3 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    calc
      Nat.choose (m + 3) 3 + ∑ j ∈ Finset.range (n + 1), Nat.choose (m + 3 + j) 2
        = Nat.choose (m + 3) 3 + (∑ j ∈ Finset.range n, Nat.choose (m + 3 + j) 2)
            + Nat.choose (m + 3 + n) 2 := by
          rw [Finset.sum_range_succ] <;> ring
      _ = Nat.choose (m + n + 3) 3 + Nat.choose (m + n + 3) 2 := by
          rw [ih]
          have h_add : m + 3 + n = m + n + 3 := by omega
          rw [h_add]
      _ = Nat.choose (m + n + 4) 3 := by
          have h' := choose_pascal3 (m + n + 3)
          exact h'.symm

/-- Algebraic inequality: for `d ≥ 1`, `C(2d+3,3) ≥ C(d+3,3) + 2`. -/
lemma choose_algebraic_ineq (d : ℕ) (hd : 1 ≤ d) :
    Nat.choose (2 * d + 3) 3 ≥ Nat.choose (d + 3) 3 + 2 := by
  induction d with
  | zero =>
    exfalso
    linarith
  | succ d ih =>
    by_cases h : d = 0
    · subst h
      decide
    · have ih' := ih (by omega)
      have h_eq1 : 2 * (d + 1) + 3 = 2 * d + 5 := by omega
      have h_eq2 : (d + 1) + 3 = d + 4 := by omega
      have h_pascal1 : Nat.choose (2 * d + 5) 3 =
          Nat.choose (2 * d + 3) 3 + Nat.choose (2 * d + 3) 2 + Nat.choose (2 * d + 4) 2 := by
        have h1 : Nat.choose (2 * d + 5) 3 =
            Nat.choose (2 * d + 4) 3 + Nat.choose (2 * d + 4) 2 := choose_pascal3 (2 * d + 4)
        have h2 : Nat.choose (2 * d + 4) 3 =
            Nat.choose (2 * d + 3) 3 + Nat.choose (2 * d + 3) 2 := choose_pascal3 (2 * d + 3)
        rw [h1, h2]
      have h_pascal2 : Nat.choose (d + 4) 3 =
          Nat.choose (d + 3) 3 + Nat.choose (d + 3) 2 := choose_pascal3 (d + 3)
      rw [h_eq1, h_eq2, h_pascal1, h_pascal2]
      have h7 : Nat.choose (2 * d + 4) 2 ≥ Nat.choose (d + 3) 2 := by
        apply Nat.choose_le_choose
        <;> omega
      have h8 : Nat.choose (2 * d + 3) 2 ≥ 1 := by
        have h9 : 2 ≤ 2 * d + 3 := by omega
        exact Nat.choose_pos h9
      omega

/-- The combinatorial dimension-count inequality:
for `k ≥ 2`, `1 ≤ d`, `2d ≤ k`:
`C(d+3,3) + C(k-2d+3,3) < C(k+3,3)`. -/
lemma choose_dimension_ineq (k d : ℕ) (hk : 2 ≤ k) (hd : 1 ≤ d) (h2d : 2 * d ≤ k) :
    Nat.choose (d + 3) 3 + Nat.choose (k - 2 * d + 3) 3 < Nat.choose (k + 3) 3 := by
  set m : ℕ := k - 2 * d with hm_def
  have h_k : k = 2 * d + m := by omega
  have h1 : Nat.choose (m + 3) 3 + ∑ j ∈ Finset.range (2 * d), Nat.choose (m + 3 + j) 2 =
      Nat.choose (m + 2 * d + 3) 3 := choose_sum_aux m (2 * d)
  have h2 : ∑ j ∈ Finset.range (2 * d), Nat.choose (3 + j) 2 ≤
      ∑ j ∈ Finset.range (2 * d), Nat.choose (m + 3 + j) 2 := by
    apply Finset.sum_le_sum
    intro j _
    apply Nat.choose_le_choose
    <;> omega
  have h3 : Nat.choose 3 3 + ∑ j ∈ Finset.range (2 * d), Nat.choose (3 + j) 2 =
      Nat.choose (2 * d + 3) 3 := by
    simpa [add_assoc] using choose_sum_aux 0 (2 * d)
  have h4 : Nat.choose (2 * d + 3) 3 ≥ Nat.choose (d + 3) 3 + 2 := choose_algebraic_ineq d hd
  have h5 : ∑ j ∈ Finset.range (2 * d), Nat.choose (3 + j) 2 > Nat.choose (d + 3) 3 := by
    have h6 : Nat.choose 3 3 = 1 := by norm_num
    rw [h6] at h3
    omega
  have h7 : ∑ j ∈ Finset.range (2 * d), Nat.choose (m + 3 + j) 2 > Nat.choose (d + 3) 3 := by
    linarith
  have h8 : Nat.choose (m + 2 * d + 3) 3 > Nat.choose (d + 3) 3 + Nat.choose (m + 3) 3 := by
    linarith [h1]
  have h9 : m + 2 * d + 3 = k + 3 := by omega
  have h10 : m + 3 = k - 2 * d + 3 := by omega
  rw [h9, h10] at h8
  exact h8

/-! ### Polynomial subspace dimension -/

/-- The finrank of `degreeLESubmodule k` equals `Nat.choose (k + 3) 3`,
the number of monomials in 3 variables of total degree at most `k`. -/
lemma finrank_degreeLESubmodule (k : ℕ) :
    Module.finrank ℝ (degreeLESubmodule k) = Nat.choose (k + 3) 3 := by
  let univ3 : Finset (Fin 3) := Finset.univ
  let s : Finset (Fin 3 →₀ ℕ) :=
    Finset.biUnion (Finset.range (k + 1)) (fun n => univ3.finsuppAntidiag n)
  have hS : (s : Set (Fin 3 →₀ ℕ)) = {n | n.sum (fun _ e => e) ≤ k} := by
    ext x
    simp only [s, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn, hx⟩
      have hsum : x.sum (fun _ e => e) = n := (Finset.mem_finsuppAntidiag'.mp hx).1
      rw [hsum] <;> omega
    · intro h
      refine ⟨x.sum (fun _ e => e), ?_, ?_⟩
      · omega
      · rw [Finset.mem_finsuppAntidiag']
        exact ⟨rfl, Finset.subset_univ _⟩
  letI : Fintype {x : Fin 3 →₀ ℕ // x ∈ (s : Set (Fin 3 →₀ ℕ))} :=
    Fintype.ofFinset s (fun _ => Iff.rfl)
  have h_card : s.card = Nat.choose (k + 3) 3 := by
    have h_disj : ∀ n₁ ∈ Finset.range (k + 1), ∀ n₂ ∈ Finset.range (k + 1), n₁ ≠ n₂ →
        Disjoint (univ3.finsuppAntidiag n₁) (univ3.finsuppAntidiag n₂) := by
      intro n₁ _ n₂ _ hne
      rw [Finset.disjoint_left]
      intro f hf1 hf2
      have h1 : f.sum (fun _ e => e) = n₁ := (Finset.mem_finsuppAntidiag'.mp hf1).1
      have h2 : f.sum (fun _ e => e) = n₂ := (Finset.mem_finsuppAntidiag'.mp hf2).1
      rw [h1] at h2
      exact hne h2
    have h1 : s.card = ∑ n ∈ Finset.range (k + 1), (univ3.finsuppAntidiag n).card := by
      rw [Finset.card_biUnion h_disj]
    rw [h1]
    have h2 : ∀ n ∈ Finset.range (k + 1), (univ3.finsuppAntidiag n).card = Nat.choose (n + 2) 2 := by
      intro n _
      have h3 : (univ3.finsuppAntidiag n).card = (Finset.card univ3 + n - 1).choose n :=
        Finset.card_finsuppAntidiag_nat_eq_choose (s := univ3) n
      rw [h3]
      have h4 : Finset.card univ3 = 3 := by simp [univ3]
      rw [h4]
      have h5 : (3 + n - 1).choose n = (n + 2).choose 2 := by
        have h6 : 3 + n - 1 = n + 2 := by omega
        rw [h6]
        have h7 : (n + 2).choose n = (n + 2).choose 2 :=
          Nat.choose_symm_add (a := n) (b := 2)
        exact h7
      exact h5
    rw [Finset.sum_congr rfl h2]
    have h4 := Nat.sum_range_add_choose k 2
    simpa using h4
  have h_eq1 : degreeLESubmodule k = MvPolynomial.restrictTotalDegree (Fin 3) ℝ k := by
    ext p
    simp [degreeLESubmodule, MvPolynomial.mem_restrictTotalDegree]
  have h_eq2 : MvPolynomial.restrictTotalDegree (Fin 3) ℝ k =
      MvPolynomial.restrictSupport ℝ (s : Set (Fin 3 →₀ ℕ)) := by
    rw [MvPolynomial.restrictTotalDegree, hS]
  rw [h_eq1, h_eq2]
  let b := MvPolynomial.basisRestrictSupport ℝ (s : Set (Fin 3 →₀ ℕ))
  have h_main : Module.finrank ℝ (MvPolynomial.restrictSupport ℝ (s : Set (Fin 3 →₀ ℕ))) =
      Fintype.card {x : Fin 3 →₀ ℕ // x ∈ (s : Set (Fin 3 →₀ ℕ))} :=
    Module.finrank_eq_card_basis b
  rw [h_main]
  have h_fintype_card : Fintype.card {x : Fin 3 →₀ ℕ // x ∈ (s : Set (Fin 3 →₀ ℕ))} = s.card := by
    simp
  rw [h_fintype_card, h_card]

/-- Global finite-dimensionality instance for bounded-degree polynomial subspaces. -/
instance degreeLESubmodule.finite (n : ℕ) : Module.Finite ℝ (degreeLESubmodule n) := by
  have h_eq : degreeLESubmodule n = MvPolynomial.restrictTotalDegree (Fin 3) ℝ n := by
    ext p; simp [degreeLESubmodule, MvPolynomial.mem_restrictTotalDegree]
  exact h_eq ▸ inferInstanceAs (Module.Finite ℝ (MvPolynomial.restrictTotalDegree (Fin 3) ℝ n))

/-! ### Product dimension inequality -/

/-- The product of degree-≤-d and degree-≤-(k-2d) polynomial spaces has strictly
smaller dimension than the degree-≤-k space. -/
lemma finrank_product_ineq (k d : ℕ) (hk : 2 ≤ k) (hd : 1 ≤ d) (h2d : 2 * d ≤ k) :
    Module.finrank ℝ ((degreeLESubmodule d) × (degreeLESubmodule (k - 2 * d))) <
    Module.finrank ℝ (degreeLESubmodule k) := by
  have h_eq_d : degreeLESubmodule d = MvPolynomial.restrictTotalDegree (Fin 3) ℝ d := by
    ext p; simp [degreeLESubmodule, MvPolynomial.mem_restrictTotalDegree]
  have h_eq_k2d : degreeLESubmodule (k - 2 * d) = MvPolynomial.restrictTotalDegree (Fin 3) ℝ (k - 2 * d) := by
    ext p; simp [degreeLESubmodule, MvPolynomial.mem_restrictTotalDegree]
  have h_eq_k : degreeLESubmodule k = MvPolynomial.restrictTotalDegree (Fin 3) ℝ k := by
    ext p; simp [degreeLESubmodule, MvPolynomial.mem_restrictTotalDegree]
  letI : Module.Finite ℝ (degreeLESubmodule d) := by
    exact h_eq_d ▸ inferInstanceAs (Module.Finite ℝ (MvPolynomial.restrictTotalDegree (Fin 3) ℝ d))
  letI : Module.Finite ℝ (degreeLESubmodule (k - 2 * d)) := by
    exact h_eq_k2d ▸ inferInstanceAs (Module.Finite ℝ (MvPolynomial.restrictTotalDegree (Fin 3) ℝ (k - 2 * d)))
  letI : Module.Free ℝ (degreeLESubmodule d) := by
    exact h_eq_d ▸ inferInstanceAs (Module.Free ℝ (MvPolynomial.restrictTotalDegree (Fin 3) ℝ d))
  letI : Module.Free ℝ (degreeLESubmodule (k - 2 * d)) := by
    exact h_eq_k2d ▸ inferInstanceAs (Module.Free ℝ (MvPolynomial.restrictTotalDegree (Fin 3) ℝ (k - 2 * d)))
  have h1 : Module.finrank ℝ ((degreeLESubmodule d) × (degreeLESubmodule (k - 2 * d))) =
      Module.finrank ℝ (degreeLESubmodule d) + Module.finrank ℝ (degreeLESubmodule (k - 2 * d)) :=
    Module.finrank_prod
  rw [h1]
  rw [finrank_degreeLESubmodule d, finrank_degreeLESubmodule (k - 2 * d),
    finrank_degreeLESubmodule k]
  exact choose_dimension_ineq k d hk hd h2d

/-! ### Euclidean parameterization of bounded-degree polynomials -/

/-- Finset of exponent vectors in 3 variables with total degree at most `k`. -/
def degreeLEIndexFinset (k : ℕ) : Finset (Fin 3 →₀ ℕ) :=
  Finset.biUnion (Finset.range (k + 1)) fun n =>
    (Finset.univ : Finset (Fin 3)).finsuppAntidiag n

lemma degreeLEIndexFinset_coe (k : ℕ) :
    (degreeLEIndexFinset k : Set (Fin 3 →₀ ℕ)) =
    {n : Fin 3 →₀ ℕ | n.sum (fun _ e => e) ≤ k} := by
  ext x
  simp only [degreeLEIndexFinset, Finset.mem_coe, Finset.mem_biUnion,
    Finset.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn, hx⟩
    have hsum : x.sum (fun _ e => e) = n := (Finset.mem_finsuppAntidiag'.mp hx).1
    rw [hsum]; omega
  · intro h
    refine ⟨x.sum (fun _ e => e), by omega, ?_⟩
    rw [Finset.mem_finsuppAntidiag']
    exact ⟨rfl, Finset.subset_univ _⟩

lemma degreeLESubmodule_eq_restrictSupport (k : ℕ) :
    degreeLESubmodule k =
    MvPolynomial.restrictSupport ℝ ((degreeLEIndexFinset k : Set (Fin 3 →₀ ℕ))) := by
  ext p
  have hS := degreeLEIndexFinset_coe k
  have h1 : p ∈ MvPolynomial.restrictSupport ℝ (degreeLEIndexFinset k : Set (Fin 3 →₀ ℕ)) ↔
      p.totalDegree ≤ k := by
    have h2 : MvPolynomial.restrictTotalDegree (Fin 3) ℝ k =
        MvPolynomial.restrictSupport ℝ (degreeLEIndexFinset k : Set (Fin 3 →₀ ℕ)) := by
      rw [MvPolynomial.restrictTotalDegree, hS]
    rw [← h2]
    exact MvPolynomial.mem_restrictTotalDegree (Fin 3) k p
  simpa [degreeLESubmodule] using h1.symm

/-- The monomial basis of `degreeLESubmodule k`, reindexed by `Fin (finrank)`. -/
noncomputable def degreeLEBasis (k : ℕ) :
    Module.Basis (Fin (Module.finrank ℝ (degreeLESubmodule k))) ℝ (degreeLESubmodule k) := by
  let s := degreeLEIndexFinset k
  let S : Set (Fin 3 →₀ ℕ) := ↑s
  letI : Fintype {x : Fin 3 →₀ ℕ // x ∈ S} := Fintype.ofFinset s (fun _ => Iff.rfl)
  have h_eq : degreeLESubmodule k = MvPolynomial.restrictSupport ℝ S :=
    degreeLESubmodule_eq_restrictSupport k
  let b : Module.Basis {x : Fin 3 →₀ ℕ // x ∈ S} ℝ (degreeLESubmodule k) := by
    rw [h_eq]
    exact MvPolynomial.basisRestrictSupport ℝ S
  let n := Fintype.card {x : Fin 3 →₀ ℕ // x ∈ S}
  have h_card : n = Module.finrank ℝ (degreeLESubmodule k) :=
    (Module.finrank_eq_card_basis b).symm
  let e1 : {x : Fin 3 →₀ ℕ // x ∈ S} ≃ Fin n := Fintype.equivFin _
  let e2 : Fin n ≃ Fin (Module.finrank ℝ (degreeLESubmodule k)) :=
    Equiv.cast (by rw [h_card])
  let e : {x : Fin 3 →₀ ℕ // x ∈ S} ≃ Fin (Module.finrank ℝ (degreeLESubmodule k)) :=
    e1.trans e2
  exact b.reindex e

/-- A linear equivalence from Euclidean coefficient space to the bounded-degree
polynomial submodule, using the monomial basis. -/
noncomputable def degreeLEEquiv (k : ℕ) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ (degreeLESubmodule k))) ≃ₗ[ℝ]
    degreeLESubmodule k :=
  (EuclideanSpace.equiv (Fin (Module.finrank ℝ (degreeLESubmodule k))) ℝ).toLinearEquiv.trans
    (degreeLEBasis k).equivFun.symm

/-- The equivalence expands a coefficient vector in the monomial basis. -/
lemma degreeLEEquiv_apply (k : ℕ)
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ (degreeLESubmodule k)))) :
    (degreeLEEquiv k x : MvPolynomial (Fin 3) ℝ) =
    ∑ i : Fin (Module.finrank ℝ (degreeLESubmodule k)),
      x i • (degreeLEBasis k i : MvPolynomial (Fin 3) ℝ) := by
  let e_ec := EuclideanSpace.equiv (Fin (Module.finrank ℝ (degreeLESubmodule k))) ℝ
  have h_eq : degreeLEEquiv k = e_ec.toLinearEquiv.trans (degreeLEBasis k).equivFun.symm := by
    unfold degreeLEEquiv
    <;> rfl
  rw [h_eq]
  let y : Fin (Module.finrank ℝ (degreeLESubmodule k)) → ℝ := e_ec x
  have h_y : ∀ i, y i = x i := by intro i; rfl
  have h1 : (e_ec.toLinearEquiv.trans (degreeLEBasis k).equivFun.symm) x =
      (degreeLEBasis k).equivFun.symm y := by rfl
  rw [h1, Module.Basis.equivFun_symm_apply]
  have h_sum : (↑(∑ i, y i • (degreeLEBasis k) i) : MvPolynomial (Fin 3) ℝ) =
      ∑ i, y i • (↑((degreeLEBasis k) i) : MvPolynomial (Fin 3) ℝ) := by
    rw [Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [h_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [h_y i]

end Kakeya.CV
