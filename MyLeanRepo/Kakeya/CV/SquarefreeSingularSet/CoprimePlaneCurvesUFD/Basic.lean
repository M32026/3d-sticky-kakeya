import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.GeometricLemmas
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.AlgebraicLemmas
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.CoprimePlaneCurvesUFD.PderivEquiv
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Basic machinery for coprime plane curves finiteness

Ring equivalences, evaluation lemmas, and helper theorems.
-/

noncomputable section

open MeasureTheory Metric Set MvPolynomial UniqueFactorizationMonoid Polynomial
open scoped Polynomial

namespace Kakeya.CV

/-- Convert 2-var polynomial to polynomial in y (var 0) over R[x] (var 1). -/
def asPolyY (f : MvPolynomial (Fin 2) ℝ) : Polynomial (MvPolynomial (Fin 1) ℝ) :=
  (MvPolynomial.finSuccEquiv ℝ 1) f

private def e0 : MvPolynomial (Fin 0) ℝ ≃+* ℝ :=
  { toFun := MvPolynomial.eval (fun x : Fin 0 => x.elim0)
    invFun := MvPolynomial.C
    left_inv := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C r => simp
      | add p q hp hq => simp [hp, hq, MvPolynomial.eval_add] <;> ring
      | mul_X p i _ => exfalso; exact Fin.elim0 i
    right_inv := by intro r; simp
    map_mul' := by intro p q; simp [MvPolynomial.eval_mul] <;> rfl
    map_add' := by intro p q; simp [MvPolynomial.eval_add] <;> rfl }

/-- Induced ring equivalence on polynomial rings. -/
def mapPolyEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Polynomial A ≃+* Polynomial B :=
  { toFun := Polynomial.map e.toRingHom
    invFun := Polynomial.map e.symm.toRingHom
    left_inv := by
      intro p; rw [Polynomial.map_map]
      have h2 : e.symm.toRingHom.comp e.toRingHom = RingHom.id A := by ext x; simp
      rw [h2, Polynomial.map_id]
    right_inv := by
      intro p; rw [Polynomial.map_map]
      have h2 : e.toRingHom.comp e.symm.toRingHom = RingHom.id B := by ext x; simp
      rw [h2, Polynomial.map_id]
    map_mul' := by intro p q; rw [Polynomial.map_mul]
    map_add' := by intro p q; rw [Polynomial.map_add] }

/-- Equivalence MvPolynomial(Fin 1, ℝ) ≃+* Polynomial ℝ. -/
def e1 : MvPolynomial (Fin 1) ℝ ≃+* Polynomial ℝ :=
  (MvPolynomial.finSuccEquiv ℝ 0).toRingEquiv.trans (mapPolyEquiv e0)

private lemma e1_map_C (x : ℝ) : e1 (MvPolynomial.C x) = Polynomial.C x := by
  have h_eq : (MvPolynomial.finSuccEquiv ℝ 0).symm.toRingHom.comp (Polynomial.C.comp MvPolynomial.C) = MvPolynomial.C :=
    MvPolynomial.finSuccEquiv_comp_C_eq_C (R := ℝ) 0
  have h_comp : (MvPolynomial.finSuccEquiv ℝ 0).symm (Polynomial.C (MvPolynomial.C x)) = MvPolynomial.C x := by
    have h' : ((MvPolynomial.finSuccEquiv ℝ 0).symm.toRingHom.comp (Polynomial.C.comp MvPolynomial.C)) x = MvPolynomial.C x := by
      rw [h_eq]
    simpa [RingHom.comp_apply] using h'
  have h_tmp : (MvPolynomial.finSuccEquiv ℝ 0) ((MvPolynomial.finSuccEquiv ℝ 0).symm (Polynomial.C (MvPolynomial.C x))) =
      (MvPolynomial.finSuccEquiv ℝ 0) (MvPolynomial.C x) := by
    rw [h_comp]
  have h_apply : (MvPolynomial.finSuccEquiv ℝ 0) ((MvPolynomial.finSuccEquiv ℝ 0).symm (Polynomial.C (MvPolynomial.C x))) =
      Polynomial.C (MvPolynomial.C x) := by
    exact (MvPolynomial.finSuccEquiv ℝ 0).apply_symm_apply (Polynomial.C (MvPolynomial.C x))
  have h1 : (MvPolynomial.finSuccEquiv ℝ 0) (MvPolynomial.C x) = Polynomial.C (MvPolynomial.C x) := by
    rw [h_apply] at h_tmp
    exact h_tmp.symm
  have h2 : (mapPolyEquiv e0) (Polynomial.C (MvPolynomial.C x)) = Polynomial.C (e0 (MvPolynomial.C x)) := by
    simp [mapPolyEquiv, Polynomial.map_C]
  have h3 : e0 (MvPolynomial.C x) = x := by simp [e0]
  calc e1 (MvPolynomial.C x)
    = (mapPolyEquiv e0) ((MvPolynomial.finSuccEquiv ℝ 0) (MvPolynomial.C x)) := by rfl
  _ = (mapPolyEquiv e0) (Polynomial.C (MvPolynomial.C x)) := by rw [h1]
  _ = Polynomial.C (e0 (MvPolynomial.C x)) := h2
  _ = Polynomial.C x := by rw [h3]

private lemma e1_map_X0 : e1 (MvPolynomial.X 0) = Polynomial.X := by
  have h1 : (MvPolynomial.finSuccEquiv ℝ 0) (MvPolynomial.X 0) = Polynomial.X :=
    MvPolynomial.finSuccEquiv_X_zero
  have h2 : (mapPolyEquiv e0) Polynomial.X = Polynomial.X := by
    simp [mapPolyEquiv, Polynomial.map_X]
  calc e1 (MvPolynomial.X 0)
    = (mapPolyEquiv e0) ((MvPolynomial.finSuccEquiv ℝ 0) (MvPolynomial.X 0)) := by rfl
  _ = (mapPolyEquiv e0) Polynomial.X := by rw [h1]
  _ = Polynomial.X := h2

private lemma e1_eval (p : MvPolynomial (Fin 1) ℝ) (x : ℝ) :
    Polynomial.eval x (e1 p) = MvPolynomial.eval (fun _ : Fin 1 => x) p := by
  let Φ1 : MvPolynomial (Fin 1) ℝ →+* ℝ :=
    (Polynomial.evalRingHom x).comp e1.toRingHom
  let Φ2 : MvPolynomial (Fin 1) ℝ →+* ℝ := MvPolynomial.eval (fun _ => x)
  have h : Φ1 = Φ2 := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Φ1, Φ2, e1_map_C] <;> rfl
    · intro i; fin_cases i
      · simp [Φ1, Φ2, e1_map_X0] <;> rfl
  have h4 : Φ1 p = Φ2 p := by rw [h]
  simpa [Φ1, Φ2] using h4

/-- Evaluation commutes with asPolyY. -/
lemma asPolyY_eval (f : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    Polynomial.eval y (Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 => x)) (asPolyY f)) =
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then y else x) f := by
  let s : Fin 1 → ℝ := fun _ => x
  let g : Option (Fin 1) → ℝ := fun o => Option.elim o y s
  let e_fin : Fin 2 ≃ Option (Fin 1) := _root_.finSuccEquiv 1
  let f' := MvPolynomial.rename e_fin f
  have h2 : MvPolynomial.eval g f' =
      Polynomial.eval y (Polynomial.map (MvPolynomial.eval s) (asPolyY f)) := by
    exact MvPolynomial.optionEquivLeft_elim_eval (R := ℝ) (S₁ := Fin 1) s y f'
  have h_func : g ∘ e_fin = (fun i : Fin 2 => if i = 0 then y else x) := by
    funext i
    fin_cases i <;> simp [g, e_fin, _root_.finSuccEquiv] <;> rfl
  have h1 : MvPolynomial.eval g f' = MvPolynomial.eval (fun i : Fin 2 => if i = 0 then y else x) f := by
    rw [MvPolynomial.eval_rename, h_func]
  rw [←h2, h1]

/-- asPolyY commutes with pderiv 0. -/
lemma asPolyY_pderiv {g : MvPolynomial (Fin 2) ℝ} :
    asPolyY (pderiv 0 g) = (asPolyY g).derivative :=
  finSuccEquiv1_pderiv_zero g

/-- Factor theorem for MvPolynomial (Fin 1): eval at x = 0 implies (X 0 - C x) ∣ p. -/
lemma factor_theorem_fin1 {p : MvPolynomial (Fin 1) ℝ} {x : ℝ}
    (h : MvPolynomial.eval (fun _ : Fin 1 => x) p = 0) :
    (MvPolynomial.X 0 - MvPolynomial.C x) ∣ p := by
  have h1 : Polynomial.eval x (e1 p) = 0 := by
    rw [e1_eval p x] <;> exact h
  have h2 : (Polynomial.X - Polynomial.C x) ∣ e1 p := by
    have hdiv : (Polynomial.X - Polynomial.C x) ∣ (e1 p) - Polynomial.C ((e1 p).eval x) :=
      Polynomial.X_sub_C_dvd_sub_C_eval
    rw [h1] at hdiv <;> simpa using hdiv
  have h3 : e1 (MvPolynomial.X 0 - MvPolynomial.C x) = Polynomial.X - Polynomial.C x := by
    rw [map_sub, e1_map_X0, e1_map_C]
  rcases h2 with ⟨c, hc⟩
  refine ⟨e1.symm c, ?_⟩
  have h_step1 : e1 (e1.symm c) = c := e1.apply_symm_apply c
  have h4 : e1 ((MvPolynomial.X 0 - MvPolynomial.C x) * e1.symm c) = e1 p := by
    calc e1 ((MvPolynomial.X 0 - MvPolynomial.C x) * e1.symm c)
      = e1 (MvPolynomial.X 0 - MvPolynomial.C x) * e1 (e1.symm c) := by rw [map_mul]
    _ = e1 (MvPolynomial.X 0 - MvPolynomial.C x) * c := by rw [h_step1]
    _ = (Polynomial.X - Polynomial.C x) * c := by rw [h3]
    _ = e1 p := hc.symm
  exact e1.injective h4.symm

/-- If g(c,y)=0 for all y, then (X 1 - C c) ∣ g. -/
lemma vanishes_all_y_imp_dvd {g : MvPolynomial (Fin 2) ℝ} {c : ℝ}
    (h : ∀ y : ℝ, MvPolynomial.eval (fun i : Fin 2 => if i = 0 then y else c) g = 0) :
    (MvPolynomial.X 1 - MvPolynomial.C c) ∣ g := by
  let G := asPolyY g
  let P := Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 => c)) G
  have hG_map : P = 0 := by
    by_cases hz : P = 0
    · exact hz
    · have hfin : Set.Finite {x : ℝ | P.eval x = 0} := Polynomial.finite_setOf_isRoot hz
      have hall : (Set.univ : Set ℝ) ⊆ {x : ℝ | P.eval x = 0} := by
        intro y _
        have h4 : P.eval y = 0 := asPolyY_eval g c y ▸ h y
        exact h4
      have hinf : Set.Infinite (Set.univ : Set ℝ) := Set.infinite_univ
      exfalso
      exact Set.Finite.not_infinite hfin (Set.Infinite.mono hall hinf)
  have h_coeff : ∀ n, MvPolynomial.eval (fun _ : Fin 1 => c) (G.coeff n) = 0 := by
    intro n
    have h4 : P.coeff n = 0 := by
      rw [hG_map] <;> simp
    simpa [Polynomial.coeff_map, P] using h4
  have h_dvd_coeff : ∀ n, (MvPolynomial.X 0 - MvPolynomial.C c) ∣ G.coeff n := by
    intro n
    exact factor_theorem_fin1 (h_coeff n)
  have h_dvd_G : Polynomial.C (MvPolynomial.X 0 - MvPolynomial.C c) ∣ G := by
    have h_iff : Polynomial.C (MvPolynomial.X 0 - MvPolynomial.C c) ∣ G ↔
        ∀ n, (MvPolynomial.X 0 - MvPolynomial.C c) ∣ G.coeff n :=
      Polynomial.C_dvd_iff_dvd_coeff (MvPolynomial.X 0 - MvPolynomial.C c) G
    exact h_iff.mpr h_dvd_coeff
  rcases h_dvd_G with ⟨c', hc⟩
  let e := MvPolynomial.finSuccEquiv ℝ 1
  let H' := e.symm (Polynomial.C (MvPolynomial.X 0 - MvPolynomial.C c))
  have h_eH' : e H' = Polynomial.C (MvPolynomial.X 0 - MvPolynomial.C c) := by
    dsimp only [H']
    rw [e.apply_symm_apply]
  have h_main : H' ∣ g := by
    refine ⟨e.symm c', ?_⟩
    have h_step1 : e (e.symm c') = c' := e.apply_symm_apply c'
    have h_eq1 : Polynomial.C (MvPolynomial.X 0 - MvPolynomial.C c) * c' = G := hc.symm
    have h9 : e (H' * e.symm c') = e g := by
      calc e (H' * e.symm c')
        = e H' * e (e.symm c') := by rw [map_mul]
      _ = e H' * c' := by rw [h_step1]
      _ = Polynomial.C (MvPolynomial.X 0 - MvPolynomial.C c) * c' := by rw [h_eH']
      _ = G := h_eq1
      _ = e g := by
        have hG : G = e g := by
          dsimp only [G, asPolyY] <;> rfl
        rw [hG]
    exact e.injective h9.symm
  have hC_sub : (Polynomial.C (MvPolynomial.X 0 - MvPolynomial.C c) : Polynomial (MvPolynomial (Fin 1) ℝ)) =
      Polynomial.C (MvPolynomial.X 0) - Polynomial.C (MvPolynomial.C c) := by
    rw [map_sub]
  have h1 : H' = e.symm (Polynomial.C (MvPolynomial.X 0) - Polynomial.C (MvPolynomial.C c)) := by
    dsimp only [H']
    exact congr_arg e.symm hC_sub
  have h2 : e.symm (Polynomial.C (MvPolynomial.X 0) - Polynomial.C (MvPolynomial.C c)) =
      e.symm (Polynomial.C (MvPolynomial.X 0)) - e.symm (Polynomial.C (MvPolynomial.C c)) := by
    rw [map_sub]
  have h3 : e.symm (Polynomial.C (MvPolynomial.X 0)) = MvPolynomial.X 1 := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (MvPolynomial.finSuccEquiv_X_succ (j := 0)).symm
  have h4 : e.symm (Polynomial.C (MvPolynomial.C c)) = MvPolynomial.C c := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (e.commutes c).symm
  have h_eq : H' = (MvPolynomial.X 1 - MvPolynomial.C c) := by
    rw [h1, h2, h3, h4]
  rw [h_eq] at h_main
  exact h_main

/-- Nonzero univariate polynomial has finite zero set. -/
lemma univariate_finite_roots {p : MvPolynomial (Fin 1) ℝ} (hp : p ≠ 0) :
    Set.Finite {x : ℝ | MvPolynomial.eval (fun _ : Fin 1 => x) p = 0} := by
  let q := e1 p
  have hq_ne : q ≠ 0 := by
    intro hz
    have h : p = 0 := e1.injective (by simpa [q] using hz)
    exact hp h
  have h_eval : ∀ (x : ℝ), Polynomial.eval x q = MvPolynomial.eval (fun _ : Fin 1 => x) p := by
    intro x
    exact e1_eval p x
  have h_set_eq : {x : ℝ | MvPolynomial.eval (fun _ : Fin 1 => x) p = 0} = {x : ℝ | Polynomial.eval x q = 0} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      exact (h_eval x).symm ▸ h
    · intro h
      exact (h_eval x) ▸ h
  rw [h_set_eq]
  exact Polynomial.finite_setOf_isRoot hq_ne

/-- If g and f are coprime, no nonunit polynomial in x only divides both. -/
lemma no_common_x_factor {g f : MvPolynomial (Fin 2) ℝ} {c : ℝ}
    (hcop : ∀ h, h ∣ g → h ∣ f → IsUnit h)
    (h_g : (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C c) ∣ g)
    (h_f : (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C c) ∣ f) : False := by
  have h5 : IsUnit (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C c) := hcop _ h_g h_f
  have h6 : ¬IsUnit (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C c) := by
    intro h
    have h7 : ∀ (v : Fin 2 → ℝ), MvPolynomial.eval v (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C c) ≠ 0 := by
      intro v
      have h8 : IsUnit (MvPolynomial.eval v (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C c)) :=
        h.map (MvPolynomial.eval v)
      exact IsUnit.ne_zero h8
    have h9 := h7 (fun i => if i = 1 then c else 0)
    simp at h9 <;> exact h9 rfl
  exact h6 h5

/-- Helper: units of MvPolynomial over a field are nonzero constants. -/
lemma isUnit_mvPolynomial_over_field {σ : Type*} [DecidableEq σ] {p : MvPolynomial σ ℝ} :
    IsUnit p ↔ ∃ (c : ℝ), c ≠ 0 ∧ p = MvPolynomial.C c := by
  constructor
  · intro h
    have h' := (MvPolynomial.isUnit_iff).mp h
    rcases h' with ⟨h1, h2⟩
    let c := MvPolynomial.coeff 0 p
    have hc : c ≠ 0 := IsUnit.ne_zero h1
    have h_all : ∀ (i : σ →₀ ℕ), i ≠ 0 → MvPolynomial.coeff i p = 0 := by
      intro i hi
      have hnil : IsNilpotent (MvPolynomial.coeff i p) := h2 i hi
      exact IsNilpotent.eq_zero hnil
    have h_eq : p = MvPolynomial.C c := by
      apply MvPolynomial.ext
      intro i
      by_cases hi : i = 0
      · subst hi
        simp [c, MvPolynomial.coeff_C]
      · have h4 : MvPolynomial.coeff i p = 0 := h_all i hi
        have h5 : MvPolynomial.coeff i (MvPolynomial.C c) = 0 := by
          rw [MvPolynomial.coeff_C, if_neg (Ne.symm hi)]
        rw [h4, h5]
    exact ⟨c, hc, h_eq⟩
  · rintro ⟨c, hc, rfl⟩
    have hunit : IsUnit c := isUnit_iff_ne_zero.mpr hc
    exact hunit.map (MvPolynomial.C : ℝ →+* MvPolynomial σ ℝ)

end Kakeya.CV
