import MyLeanRepo.Kakeya.CV.Statements
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Sym.Card
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean parameter space for bounded-degree polynomials

Constructs the coefficient model of dimension `choose (k + 3) 3` for real
polynomials in three variables of total degree at most `k`.

## Proof

The monomials `x^a y^b z^c` with `a + b + c ≤ k` form a basis of the
degree-bounded polynomial subspace. There are `Nat.choose (k + 3) 3` such
monomials (stars and bars). We use `MvPolynomial.basisRestrictSupport` to
obtain a formal basis indexed by this monomial set, reindex it to
`Fin (Nat.choose (k + 3) 3)`, and derive the required linear equivalence
to `CoefficientSpace`.
-/

noncomputable section

namespace Kakeya.CV

/-- The cardinality of `Finset.Nat.antidiagonalTuple 3 n` is `(n + 2).choose 2`,
by stars-and-bars: the number of triples of naturals summing to `n`. -/
lemma card_antidiagonalTuple3 (n : ℕ) :
    (Finset.Nat.antidiagonalTuple 3 n).card = (n + 2).choose 2 := by
  have h1 : (Finset.univ : Finset (Fin 3)).piAntidiag n =
      Finset.Nat.antidiagonalTuple 3 n :=
    Finset.piAntidiag_univ_fin_eq_antidiagonalTuple n 3
  rw [← h1]
  have h2 : ((Finset.univ : Finset (Fin 3)).piAntidiag n).card =
      ((Finset.univ : Finset (Fin 3)).sym n).card := by
    rw [← Finset.map_sym_eq_piAntidiag (Finset.univ : Finset (Fin 3)) n]
    exact Finset.card_map _
  rw [h2]
  have h3 : Fintype.card (Sym (Fin 3) n) =
      (Fintype.card (Fin 3) + n - 1).choose n :=
    Sym.card_sym_eq_choose n
  have h4 : ((Finset.univ : Finset (Fin 3)).sym n).card =
      Fintype.card (Sym (Fin 3) n) := by
    congr
    simp
  rw [h4, h3]
  have h5 : Fintype.card (Fin 3) = 3 := by simp
  rw [h5]
  have h7 : 3 + n - 1 = n + 2 := by omega
  rw [h7]
  have h8 : n ≤ n + 2 := by omega
  have h9 : (n + 2).choose n = (n + 2).choose (n + 2 - n) := (Nat.choose_symm h8).symm
  have h10 : n + 2 - n = 2 := by omega
  rw [h10] at h9
  exact h9

/-- The finset of functions `Fin 3 → ℕ` with sum at most `k` has cardinality
`Nat.choose (k + 3) 3`. -/
lemma card_bounded_sum3 (k : ℕ) :
    (Finset.biUnion (Finset.range (k + 1))
      (fun n => Finset.Nat.antidiagonalTuple 3 n)).card =
    Nat.choose (k + 3) 3 := by
  have h_disj : ∀ (n : ℕ), n ∈ Finset.range (k + 1) →
      ∀ (m : ℕ), m ∈ Finset.range (k + 1) → n ≠ m →
        Disjoint (Finset.Nat.antidiagonalTuple 3 n)
          (Finset.Nat.antidiagonalTuple 3 m) := by
    intro n _ m _ hnm
    rw [Finset.disjoint_left]
    intro f hfn hfm
    have h1 : ∑ i : Fin 3, f i = n :=
      Finset.Nat.mem_antidiagonalTuple.mp hfn
    have h2 : ∑ i : Fin 3, f i = m :=
      Finset.Nat.mem_antidiagonalTuple.mp hfm
    rw [h1] at h2
    exact hnm h2
  rw [Finset.card_biUnion h_disj]
  rw [Finset.sum_congr rfl fun n _ => card_antidiagonalTuple3 n]
  exact Nat.sum_range_add_choose k 2

/-- There exists a finset of `Fin 3 →₀ ℕ` whose underlying set is exactly the
degree-bounded monomial exponents, with cardinality `Nat.choose (k + 3) 3`. -/
lemma monomial_finset_card (k : ℕ) :
    ∃ (s : Finset (Fin 3 →₀ ℕ)),
      (s : Set (Fin 3 →₀ ℕ)) = {x | x.sum (fun _ e => e) ≤ k} ∧
      s.card = Nat.choose (k + 3) 3 := by
  let T : Finset (Fin 3 → ℕ) :=
    Finset.biUnion (Finset.range (k + 1))
      (fun n => Finset.Nat.antidiagonalTuple 3 n)
  let e : (Fin 3 →₀ ℕ) ≃ (Fin 3 → ℕ) := Finsupp.equivFunOnFinite
  let U : Finset (Fin 3 →₀ ℕ) := Finset.image e.symm T
  have h_sum_eq : ∀ (x : Fin 3 →₀ ℕ),
      x.sum (fun _ e => e) = ∑ i : Fin 3, e x i := by
    intro x
    simp [e, Finsupp.sum_fintype]
  have hU1 : ∀ (x : Fin 3 →₀ ℕ), x ∈ U ↔ x.sum (fun _ e => e) ≤ k := by
    intro x
    simp only [U, Finset.mem_image, T, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨y, ⟨n, hn, hyn⟩, rfl⟩
      have hsum : (∑ i : Fin 3, y i) = n :=
        Finset.Nat.mem_antidiagonalTuple.mp hyn
      have h_eq : (e.symm y).sum (fun _ e => e) = n := by
        rw [h_sum_eq (e.symm y)]
        have h13 : e (e.symm y) = y := e.apply_symm_apply y
        rw [h13]
        exact hsum
      rw [h_eq]
      exact by omega
    · intro h
      refine ⟨e x, ⟨x.sum (fun _ e => e), by omega, ?_⟩, by simp⟩
      have hsum : (∑ i : Fin 3, e x i) = x.sum (fun _ e => e) := by
        rw [h_sum_eq x]
      simpa [Finset.Nat.mem_antidiagonalTuple] using hsum
  have hU_set : (U : Set (Fin 3 →₀ ℕ)) = {x | x.sum (fun _ e => e) ≤ k} := by
    ext x
    exact hU1 x
  have hUcard : U.card = T.card := Finset.card_image_of_injective _ e.symm.injective
  refine ⟨U, hU_set, ?_⟩
  rw [hUcard]
  exact card_bounded_sum3 k

theorem polynomial_parameter_space :
    PolynomialParameterSpaceStatement := by
  intro k
  let N : ℕ := Nat.choose (k + 3) 3
  rcases monomial_finset_card k with ⟨s, hs_set, hs_card⟩
  let S : Set (Fin 3 →₀ ℕ) := (s : Set (Fin 3 →₀ ℕ))
  letI : Fintype S := Fintype.ofFinset s (fun _ => Iff.rfl)
  have hFintypeCard : Fintype.card S = N := by
    rw [Fintype.card_ofFinset]
    exact hs_card
  have hS_eq : S = {x : Fin 3 →₀ ℕ | x.sum (fun _ e => e) ≤ k} := hs_set
  have h_submodule_eq : degreeLESubmodule k = MvPolynomial.restrictSupport ℝ S := by
    have h1 : degreeLESubmodule k = MvPolynomial.restrictTotalDegree (Fin 3) ℝ k := by
      ext p
      simp [degreeLESubmodule, MvPolynomial.mem_restrictTotalDegree]
    rw [h1, MvPolynomial.restrictTotalDegree, hS_eq]
  let b_raw : Module.Basis S ℝ (MvPolynomial.restrictSupport ℝ S) :=
    MvPolynomial.basisRestrictSupport ℝ S
  let b : Module.Basis S ℝ (degreeLESubmodule k) := by
    rw [h_submodule_eq]
    exact b_raw
  let e : S ≃ Fin N := Fintype.equivFinOfCardEq hFintypeCard
  let b' : Module.Basis (Fin N) ℝ (degreeLESubmodule k) := b.reindex e
  let toFun : CoefficientSpace N ≃ₗ[ℝ] (Fin N → ℝ) :=
    (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin N)).toLinearEquiv
  let equiv : CoefficientSpace N ≃ₗ[ℝ] degreeLESubmodule k :=
    toFun.trans b'.equivFun.symm
  let P : PolynomialParameterization k :=
    { dim := N
      equiv := equiv }
  exact ⟨P, by simp [P, N]⟩

end Kakeya.CV
