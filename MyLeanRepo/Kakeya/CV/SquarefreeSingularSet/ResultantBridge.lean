import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Resultant bridge lemma

Given two coprime polynomials f, g in three real variables, construct a nonzero
two-variable polynomial R such that every common zero (x,y,z) of f and g satisfies
R(x,y) = 0.

This is the algebraic bridge between coprimality and the geometric dimension bound.
-/

noncomputable section

open MvPolynomial UniqueFactorizationMonoid Polynomial
open scoped Polynomial

namespace Kakeya.CV

/-- Permutation of Fin 3 swapping 0 and 2. -/
private def swap02 : Fin 3 ≃ Fin 3 :=
  Equiv.swap (0 : Fin 3) 2

/-- Permutation of Fin 2 swapping 0 and 1. -/
private def swap01 : Fin 2 ≃ Fin 2 :=
  Equiv.swap (0 : Fin 2) 1

/-- Ring equivalence MvPolynomial(Fin 0, R) ≃+* R. -/
private def e0 (R : Type*) [CommRing R] : MvPolynomial (Fin 0) R ≃+* R :=
  let eval0 : MvPolynomial (Fin 0) R →+* R :=
    MvPolynomial.eval (fun x : Fin 0 => x.elim0)
  { toFun := eval0
    invFun := MvPolynomial.C
    left_inv := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C r => simp [eval0]
      | add p q hp hq =>
        calc MvPolynomial.C (eval0 (p + q))
          = MvPolynomial.C (eval0 p + eval0 q) := by
              congr
              exact MvPolynomial.eval_add
        _ = MvPolynomial.C (eval0 p) + MvPolynomial.C (eval0 q) := by
              exact MvPolynomial.C_add
        _ = p + q := by rw [hp, hq]
      | mul_X p i _ => exfalso; exact Fin.elim0 i
    right_inv := by intro r; simp [eval0]
    map_mul' := by intro p q; simp [eval0, MvPolynomial.eval_mul]
    map_add' := by intro p q; simp [eval0, MvPolynomial.eval_add] }

/-- Induced ring equivalence on polynomial rings. -/
private def mapPolyEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Polynomial A ≃+* Polynomial B :=
  { toFun := Polynomial.map e.toRingHom
    invFun := Polynomial.map e.symm.toRingHom
    left_inv := by
      intro p
      have h : Polynomial.map e.symm.toRingHom (Polynomial.map e.toRingHom p) =
          Polynomial.map (e.symm.toRingHom.comp e.toRingHom) p := by
        exact Polynomial.map_map e.toRingHom e.symm.toRingHom p
      rw [h]
      have h2 : e.symm.toRingHom.comp e.toRingHom = RingHom.id A := by ext x; simp
      rw [h2, Polynomial.map_id]
    right_inv := by
      intro p
      have h : Polynomial.map e.toRingHom (Polynomial.map e.symm.toRingHom p) =
          Polynomial.map (e.toRingHom.comp e.symm.toRingHom) p := by
        exact Polynomial.map_map e.symm.toRingHom e.toRingHom p
      rw [h]
      have h2 : e.toRingHom.comp e.symm.toRingHom = RingHom.id B := by ext x; simp
      rw [h2, Polynomial.map_id]
    map_mul' := by intro p q; rw [Polynomial.map_mul]
    map_add' := by intro p q; rw [Polynomial.map_add] }

/-- Equivalence MvPolynomial(Fin 1, ℝ) ≃+* Polynomial ℝ. -/
private def e1 : MvPolynomial (Fin 1) ℝ ≃+* Polynomial ℝ :=
  (MvPolynomial.finSuccEquiv ℝ 0).toRingEquiv.trans (mapPolyEquiv (e0 ℝ))

/-- Equivalence MvPolynomial(Fin 2, ℝ) ≃+* Polynomial (Polynomial ℝ).
    Used to transport GCD structure from iterated polynomial rings. -/
private def e2 : MvPolynomial (Fin 2) ℝ ≃+* Polynomial (Polynomial ℝ) :=
  (MvPolynomial.finSuccEquiv ℝ 1).toRingEquiv.trans (mapPolyEquiv e1)

/-- The resultant of f and g with respect to variable 2, returned as a
    two-variable polynomial in variables 0,1. -/
def resultantVar2 (f g : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 2) ℝ :=
  let f' := rename swap02 f
  let g' := rename swap02 g
  let F := (finSuccEquiv ℝ 2) f'
  let G := (finSuccEquiv ℝ 2) g'
  rename swap01 (Polynomial.resultant F G)

/-- Evaluation of finSuccEquiv polynomial at coefficient point y and value z. -/
private lemma finSuccEquiv_eval (p : MvPolynomial (Fin 3) ℝ) (y : Point 2) (z : ℝ) :
    Polynomial.eval z (Polynomial.map (MvPolynomial.eval y) ((finSuccEquiv ℝ 2) p)) =
    MvPolynomial.eval (fun i : Fin 3 =>
      if i = 0 then z else if i = 1 then y 0 else y 1) p := by
  let g : Fin 3 → ℝ := fun i => if i = 0 then z else if i = 1 then y 0 else y 1
  let ψ : Polynomial (MvPolynomial (Fin 2) ℝ) →+* ℝ :=
    { toFun := fun q => Polynomial.eval₂ (MvPolynomial.eval y) z q
      map_one' := by simp
      map_mul' := by simp [Polynomial.eval₂_mul]
      map_zero' := by simp
      map_add' := by simp [Polynomial.eval₂_add] }
  let Φ : MvPolynomial (Fin 3) ℝ →+* ℝ := ψ.comp (finSuccEquiv ℝ 2).toRingHom
  let eval_g : MvPolynomial (Fin 3) ℝ →+* ℝ :=
    { toFun := MvPolynomial.eval g
      map_one' := by simp
      map_mul' := by simp [MvPolynomial.eval_mul]
      map_zero' := by simp
      map_add' := by simp [MvPolynomial.eval_add] }
  have h_eval2_map : ∀ (q : Polynomial (MvPolynomial (Fin 2) ℝ)),
      Polynomial.eval z (Polynomial.map (MvPolynomial.eval y) q) = ψ q := by
    intro q
    exact Polynomial.eval_map (MvPolynomial.eval y) z
  have h_eq : Φ = eval_g := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have h2 : (finSuccEquiv ℝ 2) (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) :=
        (finSuccEquiv ℝ 2).commutes a
      have h3 : Φ (MvPolynomial.C a) = ψ ((finSuccEquiv ℝ 2) (MvPolynomial.C a)) := by rfl
      rw [h3, h2]
      simp [ψ, eval_g, Polynomial.eval₂_C]
    · have h4 : ∀ (j : Fin 3), ψ ((finSuccEquiv ℝ 2) (MvPolynomial.X j)) = eval_g (MvPolynomial.X j) := by
        intro j
        exact Fin.cases
          (by simp [ψ, eval_g, MvPolynomial.finSuccEquiv_X_zero, g, Polynomial.eval₂_X])
          (fun k : Fin 2 => by
            have hX : (finSuccEquiv ℝ 2) (MvPolynomial.X (Fin.succ k)) =
                  Polynomial.C (MvPolynomial.X k) :=
                MvPolynomial.finSuccEquiv_X_succ (j := k)
            have hg : g (Fin.succ k) = y k := by
              fin_cases k <;> simp [g] <;> rfl
            rw [hX]
            simp [ψ, eval_g, Polynomial.eval₂_C, hg])
          j
      intro i
      have h3 : Φ (MvPolynomial.X i) = ψ ((finSuccEquiv ℝ 2) (MvPolynomial.X i)) := by rfl
      rw [h3]
      exact h4 i
  have h_final : Polynomial.eval z (Polynomial.map (MvPolynomial.eval y) ((finSuccEquiv ℝ 2) p)) = Φ p := by
    exact h_eval2_map ((finSuccEquiv ℝ 2) p)
  rw [h_final, h_eq] <;> rfl

/-- Helper: finSuccEquiv commutes with pderiv 0 and polynomial derivative. -/
private lemma finSuccEquiv_pderiv_zero (p : MvPolynomial (Fin 3) ℝ) :
    (finSuccEquiv ℝ 2) (pderiv 0 p) = ((finSuccEquiv ℝ 2) p).derivative := by
  let D : MvPolynomial (Fin 3) ℝ → Polynomial (MvPolynomial (Fin 2) ℝ) :=
    fun q => ((finSuccEquiv ℝ 2) q).derivative
  let E : MvPolynomial (Fin 3) ℝ → Polynomial (MvPolynomial (Fin 2) ℝ) :=
    fun q => (finSuccEquiv ℝ 2) (pderiv 0 q)
  have h_gen : ∀ (i : Fin 3), (finSuccEquiv ℝ 2) (pderiv 0 (MvPolynomial.X i)) =
      Polynomial.derivative ((finSuccEquiv ℝ 2) (MvPolynomial.X i)) := by
    intro i
    exact Fin.cases
      (by simp [MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.pderiv_X_self,
            Polynomial.derivative_X] <;> ring)
      (fun k : Fin 2 => by
        have hX : (finSuccEquiv ℝ 2) (MvPolynomial.X (Fin.succ k)) =
              Polynomial.C (MvPolynomial.X k) :=
            MvPolynomial.finSuccEquiv_X_succ (j := k)
        have h1 : (finSuccEquiv ℝ 2) (pderiv 0 (MvPolynomial.X (Fin.succ k))) = 0 := by
          simp [MvPolynomial.pderiv_X_of_ne] <;> decide
        have h2 : Polynomial.derivative ((finSuccEquiv ℝ 2) (MvPolynomial.X (Fin.succ k))) = 0 := by
          rw [hX]
          simp [Polynomial.derivative_C]
        rw [h1, h2])
      i
  have h_main : ∀ q, E q = D q := by
    intro q
    apply MvPolynomial.induction_on q
    · intro a
      have hC : (finSuccEquiv ℝ 2) (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) :=
        (finSuccEquiv ℝ 2).commutes a
      have hE : E (MvPolynomial.C a) = 0 := by
        simp only [E, MvPolynomial.pderiv_C, map_zero]
      have hD : D (MvPolynomial.C a) = 0 := by
        simp only [D, hC, Polynomial.derivative_C]
      rw [hE, hD]
    · intro p q hp hq
      simp only [E, D, hp, hq, map_add, Polynomial.derivative_add] <;> abel
    · intro p i hp
      have h_leib : pderiv 0 (p * MvPolynomial.X i) =
          p * pderiv 0 (MvPolynomial.X i) + pderiv 0 p * MvPolynomial.X i := by
        rw [MvPolynomial.pderiv_mul] <;> ring
      have h1 : E (p * MvPolynomial.X i) =
          (finSuccEquiv ℝ 2) (p * pderiv 0 (MvPolynomial.X i) + pderiv 0 p * MvPolynomial.X i) :=
        congr_arg (fun x => (finSuccEquiv ℝ 2) x) h_leib
      rw [h1]
      have h2 : (finSuccEquiv ℝ 2) (p * pderiv 0 (MvPolynomial.X i) + pderiv 0 p * MvPolynomial.X i) =
          (finSuccEquiv ℝ 2) p * (finSuccEquiv ℝ 2) (pderiv 0 (MvPolynomial.X i)) +
          (finSuccEquiv ℝ 2) (pderiv 0 p) * (finSuccEquiv ℝ 2) (MvPolynomial.X i) := by
        simp [map_add, map_mul] <;> ring
      rw [h2]
      have h3 : (finSuccEquiv ℝ 2) (pderiv 0 (MvPolynomial.X i)) =
          Polynomial.derivative ((finSuccEquiv ℝ 2) (MvPolynomial.X i)) := h_gen i
      have h4 : (finSuccEquiv ℝ 2) (pderiv 0 p) = D p := hp
      rw [h3, h4]
      have h5 : D (p * MvPolynomial.X i) =
          (finSuccEquiv ℝ 2) p * Polynomial.derivative ((finSuccEquiv ℝ 2) (MvPolynomial.X i)) +
          Polynomial.derivative ((finSuccEquiv ℝ 2) p) * (finSuccEquiv ℝ 2) (MvPolynomial.X i) := by
        simp only [D, map_mul, Polynomial.derivative_mul] <;> ring
      rw [h5] <;> rfl
  exact h_main p

/-- Helper: if two polynomials over a field have a common root and left degree bound > 0,
    resultant with arbitrary degree bounds ≥ actual degrees is zero. -/
private lemma resultant_eq_zero_of_common_root {R : Type*} [Field R] {f g : R[X]} {z : R} {m n : ℕ}
    (hf : f.eval z = 0) (hg : g.eval z = 0)
    (hfm : f.natDegree ≤ m) (hgn : g.natDegree ≤ n) (hm_pos : 0 < m) :
    Polynomial.resultant f g m n = 0 := by
  by_cases hf0 : f = 0
  · rw [hf0, Polynomial.resultant_zero_left]
    by_cases hn_pos : 0 < n
    · simp [hn_pos.ne']
    · have hn0 : n = 0 := by omega
      rw [hn0]
      have h1 : g.natDegree ≤ 0 := by
        rw [hn0] at hgn
        exact hgn
      have h2 : g.natDegree = 0 := by omega
      have h3 : g = Polynomial.C (g.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h2
      have h4 : g.coeff 0 = 0 := by
        rw [h3] at hg
        simpa [Polynomial.eval_C] using hg
      have hg0 : g = 0 := by
        rw [h3, h4] <;> simp
      rw [hg0] <;> simp [hm_pos.ne']
  · by_cases hg0 : g = 0
    · rw [hg0, Polynomial.resultant_zero_right] <;> simp [hm_pos.ne']
    · have hff : (Polynomial.X - Polynomial.C z) ∣ f := by
        have h : (Polynomial.X - Polynomial.C z) ∣ f - Polynomial.C (f.eval z) :=
          Polynomial.X_sub_C_dvd_sub_C_eval
        rw [hf] at h
        simpa using h
      have hgg : (Polynomial.X - Polynomial.C z) ∣ g := by
        have h : (Polynomial.X - Polynomial.C z) ∣ g - Polynomial.C (g.eval z) :=
          Polynomial.X_sub_C_dvd_sub_C_eval
        rw [hg] at h
        simpa using h
      have h_ncop : ¬ IsCoprime f g := by
        intro hcop
        have hunit : IsUnit (Polynomial.X - Polynomial.C z) :=
          IsCoprime.isUnit_of_dvd' hcop hff hgg
        have hdeg : (Polynomial.X - Polynomial.C z).natDegree = 0 :=
          Polynomial.natDegree_eq_zero_of_isUnit hunit
        have h : (Polynomial.X - Polynomial.C z).natDegree = 1 := by
          simp
        rw [h] at hdeg <;> omega
      have h_base : Polynomial.resultant f g f.natDegree g.natDegree = 0 := by
        rw [Polynomial.resultant_eq_zero_iff]
        exact ⟨Or.inl hf0, h_ncop⟩
      let j : ℕ := n - g.natDegree
      have hnj : n = g.natDegree + j := by omega
      have h_right : Polynomial.resultant f g f.natDegree n = 0 := by
        rw [hnj]
        have h : Polynomial.resultant f g f.natDegree (g.natDegree + j) =
            f.coeff f.natDegree ^ j * Polynomial.resultant f g f.natDegree g.natDegree :=
          @Polynomial.resultant_add_right_deg R _ f g f.natDegree g.natDegree j (le_refl g.natDegree)
        rw [h, h_base] <;> ring
      let k : ℕ := m - f.natDegree
      have hmk : m = f.natDegree + k := by omega
      have h_left : Polynomial.resultant f g m n = 0 := by
        rw [hmk]
        have h : Polynomial.resultant f g (f.natDegree + k) n =
            (-1 : R) ^ (n * k) * g.coeff n ^ k * Polynomial.resultant f g f.natDegree n :=
          @Polynomial.resultant_add_left_deg R _ f g f.natDegree n k (le_refl f.natDegree)
        rw [h, h_right] <;> ring
      exact h_left

/-- If f(x)=0 and g(x)=0, then resultantVar2 f g evaluated at (x₀,x₁) is zero. -/
lemma resultantVar2_at_common_root {f g : MvPolynomial (Fin 3) ℝ} {x : Point 3}
    (hderiv : pderiv 2 f ≠ 0)
    (hf : polynomialValue f x = 0) (hg : polynomialValue g x = 0) :
    polynomialValue (resultantVar2 f g) (proj2 x) = 0 := by
  let y : Point 2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm
      fun i : Fin 2 => if i = 0 then x 1 else x 0
  let z : ℝ := x 2
  let f' := rename swap02 f
  let g' := rename swap02 g
  let F : Polynomial (MvPolynomial (Fin 2) ℝ) := (finSuccEquiv ℝ 2) f'
  let G : Polynomial (MvPolynomial (Fin 2) ℝ) := (finSuccEquiv ℝ 2) g'
  let p : Polynomial ℝ := Polynomial.map (MvPolynomial.eval y) F
  let q : Polynomial ℝ := Polynomial.map (MvPolynomial.eval y) G
  have hF_pos : 0 < F.natDegree := by
    by_contra h
    have hF0 : F.natDegree = 0 := by omega
    have h_const : F = Polynomial.C (F.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hF0
    have h1 : (finSuccEquiv ℝ 2) (pderiv 0 f') = F.derivative := finSuccEquiv_pderiv_zero f'
    rw [h_const] at h1
    have h2 : (finSuccEquiv ℝ 2) (pderiv 0 f') = 0 := by
      rw [h1] <;> simp
    have h3 : pderiv 0 f' = 0 := (finSuccEquiv ℝ 2).injective h2
    have h_swap : swap02 2 = 0 := by decide
    have h4 : pderiv 0 (rename swap02 f) = rename swap02 (pderiv 2 f) := by
      have h5 := MvPolynomial.pderiv_rename swap02.injective 2 f
      rw [h_swap] at h5
      exact h5
    rw [h4] at h3
    have h5 : rename swap02 (pderiv 2 f) = 0 := h3
    have h_comp : swap02.symm ∘ swap02 = id := by
      funext x
      simp [swap02, Equiv.symm_apply_apply]
    have h6 : pderiv 2 f = 0 := by
      have h7 : rename swap02.symm (rename swap02 (pderiv 2 f)) = rename swap02.symm 0 := by rw [h5]
      have h8 : rename swap02.symm (rename swap02 (pderiv 2 f)) = pderiv 2 f := by
        rw [MvPolynomial.rename_rename, h_comp]
        simp
      rw [h8] at h7
      simpa using h7
    exact hderiv h6
  let g_eval : Fin 3 → ℝ := fun i => if i = 0 then z else if i = 1 then y 0 else y 1
  have hy0 : y 0 = x 1 := by
    exact Real.ext_cauchy rfl
  have hy1 : y 1 = x 0 := by
    exact Real.ext_cauchy rfl
  have h_comp : ∀ (i : Fin 3), g_eval (swap02 i) = x i := by
    intro i
    fin_cases i
    · simpa [g_eval, swap02, z, hy1] using rfl
    · have h : g_eval (swap02 1) = x 1 := by
        have h1 : swap02 1 = 1 := by decide
        rw [h1]
        have h2 : g_eval 1 = y 0 := by simp [g_eval]
        rw [h2, hy0]
      exact h
    · simpa [g_eval, swap02, z] using rfl
  have hp : p.eval z = 0 := by
    have h1 : p.eval z = MvPolynomial.eval g_eval f' := finSuccEquiv_eval f' y z
    have h2 : MvPolynomial.eval g_eval f' = polynomialValue f x := by
      rw [MvPolynomial.eval_rename]
      have h_eq : g_eval ∘ swap02 = x := by
        funext i
        exact h_comp i
      rw [h_eq] <;> rfl
    rw [h1, h2, hf]
  have hq : q.eval z = 0 := by
    have h1 : q.eval z = MvPolynomial.eval g_eval g' := finSuccEquiv_eval g' y z
    have h2 : MvPolynomial.eval g_eval g' = polynomialValue g x := by
      rw [MvPolynomial.eval_rename]
      have h_eq : g_eval ∘ swap02 = x := by
        funext i
        exact h_comp i
      rw [h_eq] <;> rfl
    rw [h1, h2, hg]
  have hfm : p.natDegree ≤ F.natDegree := Polynomial.natDegree_map_le
  have hgn : q.natDegree ≤ G.natDegree := Polynomial.natDegree_map_le
  have h_main : Polynomial.resultant p q F.natDegree G.natDegree = 0 :=
    resultant_eq_zero_of_common_root hp hq hfm hgn hF_pos
  have h_map : Polynomial.resultant p q F.natDegree G.natDegree =
      MvPolynomial.eval y (Polynomial.resultant F G) := by
    exact @Polynomial.resultant_map_map (MvPolynomial (Fin 2) ℝ) ℝ _ _ F G F.natDegree G.natDegree (MvPolynomial.eval y)
  have h_y : ∀ (i : Fin 2), (proj2 x) (swap01 i) = y i := by
    intro i
    fin_cases i <;> simp [y, proj2, swap01] <;> rfl
  have h_final : polynomialValue (resultantVar2 f g) (proj2 x) =
      MvPolynomial.eval y (Polynomial.resultant F G) := by
    have h9 : (fun i : Fin 2 => (proj2 x) (swap01 i)) = (fun i : Fin 2 => y i) := by
      funext i
      exact h_y i
    have h10 : polynomialValue (resultantVar2 f g) (proj2 x) =
        MvPolynomial.eval (fun i : Fin 2 => (proj2 x) (swap01 i)) (Polynomial.resultant F G) := by
      simp [resultantVar2, polynomialValue, MvPolynomial.eval_rename]
      <;> rfl
    rw [h10, h9]
  rw [h_final, ←h_map, h_main]

/-- If `f` is irreducible, `pderiv 2 f ≠ 0`, and f is coprime to `g`,
    then `resultantVar2 f g ≠ 0`. -/
lemma resultantVar2_ne_zero {f g : MvPolynomial (Fin 3) ℝ}
    (hf : Irreducible f)
    (hcop : ∀ h, h ∣ f → h ∣ g → IsUnit h)
    (hderiv : pderiv 2 f ≠ 0) :
    resultantVar2 f g ≠ 0 := by
  classical
  let f' := rename swap02 f
  let g' := rename swap02 g
  let F : Polynomial (MvPolynomial (Fin 2) ℝ) := (finSuccEquiv ℝ 2) f'
  let G : Polynomial (MvPolynomial (Fin 2) ℝ) := (finSuccEquiv ℝ 2) g'

  let e0_alg : MvPolynomial (Fin 3) ℝ ≃ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
    MvPolynomial.renameEquiv ℝ swap02
  let e2_alg : MvPolynomial (Fin 3) ℝ ≃ₐ[ℝ] Polynomial (MvPolynomial (Fin 2) ℝ) :=
    finSuccEquiv ℝ 2

  have h1_irred : Irreducible f' :=
    (MulEquiv.irreducible_iff e0_alg.toRingEquiv.toMulEquiv).mpr hf
  have hF_irred : Irreducible F :=
    (MulEquiv.irreducible_iff e2_alg.toRingEquiv.toMulEquiv).mpr h1_irred

  have hF_ne_zero : F ≠ 0 := Irreducible.ne_zero hF_irred

  have hF_pos : 0 < F.natDegree := by
    by_contra h
    have hF0 : F.natDegree = 0 := by omega
    have h_const : F = Polynomial.C (F.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hF0
    have h1 : (finSuccEquiv ℝ 2) (pderiv 0 f') = F.derivative := finSuccEquiv_pderiv_zero f'
    rw [h_const] at h1
    have h2 : (finSuccEquiv ℝ 2) (pderiv 0 f') = 0 := by
      rw [h1] <;> simp
    have h3 : pderiv 0 f' = 0 := (finSuccEquiv ℝ 2).injective h2
    have h_swap : swap02 2 = 0 := by decide
    have h4 : pderiv 0 (rename swap02 f) = rename swap02 (pderiv 2 f) := by
      have h5 := MvPolynomial.pderiv_rename swap02.injective 2 f
      rw [h_swap] at h5
      exact h5
    rw [h4] at h3
    have h5 : rename swap02 (pderiv 2 f) = 0 := h3
    have h_comp : swap02.symm ∘ swap02 = id := by
      funext x
      simp [swap02]
    have h6 : pderiv 2 f = 0 := by
      have h7 : rename swap02.symm (rename swap02 (pderiv 2 f)) = rename swap02.symm 0 := by rw [h5]
      have h8 : rename swap02.symm (rename swap02 (pderiv 2 f)) = pderiv 2 f := by
        rw [MvPolynomial.rename_rename, h_comp]
        simp
      rw [h8] at h7
      simpa using h7
    exact hderiv h6

  -- Transport coefficient ring via e2 to Polynomial (Polynomial ℝ), which has NormalizedGCDMonoid
  let eq_map := mapPolyEquiv e2
  let F' := eq_map F
  let G' := eq_map G

  have hF'_irred : Irreducible F' :=
    (MulEquiv.irreducible_iff eq_map.toMulEquiv).mpr hF_irred
  have hF'_pos : 0 < F'.natDegree := by
    have h : F'.natDegree = F.natDegree :=
      Polynomial.natDegree_map_eq_of_injective e2.injective F
    rw [h] <;> exact hF_pos

  have hF'_prim : F'.IsPrimitive := by
    rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
    intro r hcr
    rcases hcr with ⟨Q, hQ⟩
    have h_eq : F' = Polynomial.C r * Q := hQ
    have h_disj : IsUnit (Polynomial.C r) ∨ IsUnit Q := hF'_irred.2 h_eq
    cases h_disj with
    | inl hunit =>
      exact (Polynomial.isUnit_C).mp hunit
    | inr hunitQ =>
      have hdegQ : Q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hunitQ
      have hQ_const : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdegQ
      have h1 : (Polynomial.C r * Q).natDegree = 0 := by
        have hle : (Polynomial.C r * Q).natDegree ≤ (Polynomial.C r).natDegree + Q.natDegree :=
          Polynomial.natDegree_mul_le
        have hCr0 : (Polynomial.C r).natDegree = 0 := Polynomial.natDegree_C r
        rw [hCr0, hdegQ] at hle
        exact Nat.eq_zero_of_le_zero hle
      have h2 : F'.natDegree = (Polynomial.C r * Q).natDegree := by rw [h_eq]
      have hdeg : F'.natDegree = 0 := by rw [h2, h1]
      rw [hdeg] at hF'_pos <;> omega

  intro h
  have h_res0 : Polynomial.resultant F G = 0 := by
    have h_inj : Function.Injective (rename swap01) :=
      (MvPolynomial.renameEquiv ℝ swap01).injective
    simpa [map_zero] using h_inj h

  have h_res'_zero : Polynomial.resultant F' G' = 0 := by
    have hF'deg : F'.natDegree = F.natDegree :=
      Polynomial.natDegree_map_eq_of_injective e2.injective F
    have hG'deg : G'.natDegree = G.natDegree :=
      Polynomial.natDegree_map_eq_of_injective e2.injective G
    have h1 : Polynomial.resultant F' G' F.natDegree G.natDegree =
        e2.toRingHom (Polynomial.resultant F G F.natDegree G.natDegree) :=
      Polynomial.resultant_map_map (φ := e2.toRingHom) F G F.natDegree G.natDegree
    have h2 : Polynomial.resultant F' G' = Polynomial.resultant F' G' F.natDegree G.natDegree := by
      rw [hF'deg, hG'deg] <;> rfl
    have h3 : Polynomial.resultant F' G' = e2.toRingHom (Polynomial.resultant F G F.natDegree G.natDegree) := by
      rw [h2, h1]
    have h4 : e2.toRingHom (Polynomial.resultant F G F.natDegree G.natDegree) =
        e2 (Polynomial.resultant F G) := by rfl
    rw [h3, h4, h_res0] <;> simp

  let R' := Polynomial (Polynomial ℝ)
  let K := FractionRing R'
  let i : R' →+* K := algebraMap R' K

  let F'_K := Polynomial.map i F'
  let G'_K := Polynomial.map i G'

  have h_inj_i : Function.Injective i := IsFractionRing.injective R' K
  have hFdeg : F'_K.natDegree = F'.natDegree :=
    Polynomial.natDegree_map_eq_of_injective h_inj_i F'
  have hGdeg : G'_K.natDegree = G'.natDegree :=
    Polynomial.natDegree_map_eq_of_injective h_inj_i G'

  have h_eq_res : Polynomial.resultant F'_K G'_K = i (Polynomial.resultant F' G') := by
    have h1 : Polynomial.resultant F'_K G'_K F'.natDegree G'.natDegree =
        i (Polynomial.resultant F' G' F'.natDegree G'.natDegree) :=
      Polynomial.resultant_map_map (φ := i) F' G' F'.natDegree G'.natDegree
    have h2 : Polynomial.resultant F'_K G'_K =
        Polynomial.resultant F'_K G'_K F'_K.natDegree G'_K.natDegree := by rfl
    rw [h2, hFdeg, hGdeg]
    exact h1
  have h_resK : Polynomial.resultant F'_K G'_K = 0 := by
    rw [h_eq_res, h_res'_zero] <;> simp

  have hF'_K_ne_zero : F'_K ≠ 0 := by
    intro hz
    have h3 : F' = 0 := (Polynomial.map_eq_zero_iff h_inj_i).mp hz
    rw [h3] at hF'_irred
    exact hF'_irred.ne_zero rfl

  have h_ncop : ¬ IsCoprime F'_K G'_K := by
    rw [Polynomial.resultant_eq_zero_iff] at h_resK
    exact h_resK.2

  have h_irred_K : Irreducible F'_K :=
    (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map hF'_prim).mp hF'_irred

  have h_dvd : F'_K ∣ G'_K := by
    by_cases hnd : F'_K ∣ G'_K
    · exact hnd
    · have h_prime : Prime F'_K := Irreducible.prime h_irred_K
      have h_cop : IsCoprime F'_K G'_K := by
        rw [h_prime.coprime_iff_not_dvd] <;> exact hnd
      exfalso
      exact h_ncop h_cop

  by_cases hG' : G' = 0
  · have hG'eq : eq_map G = eq_map 0 := by
      have h : G' = 0 := hG'
      simpa [G'] using h
    have hG : G = 0 := eq_map.injective hG'eq
    have hg0 : g' = 0 := e2_alg.toRingEquiv.injective hG
    have hg : g = 0 := e0_alg.toRingEquiv.injective hg0
    rw [hg] at hcop
    have hunit : IsUnit f := hcop f dvd_rfl (dvd_zero f)
    exact hf.1 hunit
  · have hG'_prim : G'.primPart.IsPrimitive := Polynomial.isPrimitive_primPart G'
    have hcontent_ne_zero : G'.content ≠ 0 := by
      intro hz
      have h5 : G' = 0 := Polynomial.content_eq_zero_iff.mp hz
      exact hG' h5
    have h_i_content_ne_zero : i G'.content ≠ 0 := by
      intro h
      have h' : i G'.content = i 0 := by simpa using h
      exact hcontent_ne_zero (h_inj_i h')
    have h_eq2 : G'_K = Polynomial.C (i G'.content) * Polynomial.map i G'.primPart := by
      have h6 : G' = Polynomial.C G'.content * G'.primPart := by
        exact eq_C_content_mul_primPart G'
      dsimp only [G'_K]
      have h7 : Polynomial.map i G' = Polynomial.map i (Polynomial.C G'.content * G'.primPart) := by
        exact congr_arg (Polynomial.map i) h6
      have h8 : Polynomial.map i (Polynomial.C G'.content * G'.primPart) =
          Polynomial.map i (Polynomial.C G'.content) * Polynomial.map i G'.primPart := by
        rw [Polynomial.map_mul]
      have h9 : Polynomial.map i (Polynomial.C G'.content) = Polynomial.C (i G'.content) := by simp
      have h10 : Polynomial.map i G' = Polynomial.C (i G'.content) * Polynomial.map i G'.primPart := by
        rw [h7, h8, h9]
      exact h10
    have h_dvd_prim : F'_K ∣ Polynomial.map i G'.primPart := by
      rw [h_eq2] at h_dvd
      have h_unit : IsUnit (Polynomial.C (i G'.content) : K[X]) :=
        Polynomial.isUnit_C.mpr (IsUnit.mk0 _ h_i_content_ne_zero)
      exact h_unit.dvd_mul_left.mp h_dvd
    have h_dvd_R : F' ∣ G'.primPart :=
      Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map hF'_prim hG'_prim h_dvd_prim
    have h_dvd_G' : F' ∣ G' := by
      let p := G'.primPart
      let c := G'.content
      have h11 : G' = Polynomial.C c * p := Polynomial.eq_C_content_mul_primPart G'
      have h12 : p * Polynomial.C c = G' := by
        have h13 : p * Polynomial.C c = Polynomial.C c * p := by ring
        exact h13.trans h11.symm
      have h14 : G' = p * Polynomial.C c := h12.symm
      have h10 : p ∣ G' := ⟨Polynomial.C c, h14⟩
      exact dvd_trans h_dvd_R h10

    have h_dvd_G : F ∣ G := by
      rcases h_dvd_G' with ⟨c, hc⟩
      let c' := eq_map.symm c
      have h9 : eq_map (F * c') = F' * c := by
        have hmul : eq_map (F * c') = eq_map F * eq_map c' := by exact eq_map.map_mul F c'
        rw [hmul]
        have h10 : eq_map c' = c := eq_map.apply_symm_apply c
        rw [h10] <;> rfl
      have h10 : eq_map (F * c') = eq_map G := by
        rw [h9, hc.symm] <;> rfl
      have h11 : F * c' = G := eq_map.injective h10
      exact ⟨c', h11.symm⟩
    have h_f'_div_g' : f' ∣ g' := by
      rcases h_dvd_G with ⟨c, hc⟩
      let c' := e2_alg.toRingEquiv.symm c
      have h9 : e2_alg.toRingEquiv (f' * c') = F * c := by
        have hmul : e2_alg.toRingEquiv (f' * c') = e2_alg.toRingEquiv f' * e2_alg.toRingEquiv c' := by
          exact e2_alg.toRingEquiv.map_mul f' c'
        rw [hmul]
        have h10 : e2_alg.toRingEquiv c' = c := e2_alg.toRingEquiv.apply_symm_apply c
        rw [h10] <;> rfl
      have h10 : e2_alg.toRingEquiv (f' * c') = e2_alg.toRingEquiv g' := by
        rw [h9, hc.symm] <;> rfl
      have h11 : f' * c' = g' := e2_alg.toRingEquiv.injective h10
      exact ⟨c', h11.symm⟩
    have h_f_div_g : f ∣ g := by
      rcases h_f'_div_g' with ⟨c, hc⟩
      let c' := e0_alg.toRingEquiv.symm c
      have h9 : e0_alg.toRingEquiv (f * c') = f' * c := by
        have hmul : e0_alg.toRingEquiv (f * c') = e0_alg.toRingEquiv f * e0_alg.toRingEquiv c' := by
          exact e0_alg.toRingEquiv.map_mul f c'
        rw [hmul]
        have h10 : e0_alg.toRingEquiv c' = c := e0_alg.toRingEquiv.apply_symm_apply c
        rw [h10] <;> rfl
      have h10 : e0_alg.toRingEquiv (f * c') = e0_alg.toRingEquiv g := by
        rw [h9, hc.symm] <;> rfl
      have h11 : f * c' = g := e0_alg.toRingEquiv.injective h10
      exact ⟨c', h11.symm⟩
    have hunit : IsUnit f := hcop f dvd_rfl h_f_div_g
    exact hf.1 hunit

/-- **Resultant bridge lemma**: Given coprime f,g with f irreducible and
    `pderiv 2 f ≠ 0`, there exists a nonzero 2-variable polynomial R such that
    every common zero of f,g projects to a zero of R. -/
theorem resultant_bridge (f g : MvPolynomial (Fin 3) ℝ)
    (hf : Irreducible f)
    (hcop : ∀ h, h ∣ f → h ∣ g → IsUnit h)
    (hderiv : pderiv 2 f ≠ 0) :
    ∃ (R : MvPolynomial (Fin 2) ℝ), R ≠ 0 ∧
      ∀ (x : Point 3), polynomialValue f x = 0 → polynomialValue g x = 0 →
        polynomialValue R (proj2 x) = 0 := by
  let R := resultantVar2 f g
  have hR_ne : R ≠ 0 := resultantVar2_ne_zero hf hcop hderiv
  refine ⟨R, hR_ne, ?_⟩
  intro x hfx hgx
  exact resultantVar2_at_common_root hderiv hfx hgx

end Kakeya.CV
