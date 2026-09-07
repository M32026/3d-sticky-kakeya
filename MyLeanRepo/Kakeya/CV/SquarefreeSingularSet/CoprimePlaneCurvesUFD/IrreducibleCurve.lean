import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.GeometricLemmas
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.CoprimePlaneCurvesUFD.Basic
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.CoprimePlaneCurvesUFD.ResultantNonzero

/-!
# Irreducible plane curve intersected with coprime polynomial has finite zero set
-/

noncomputable section

open MeasureTheory Metric Set MvPolynomial UniqueFactorizationMonoid Polynomial
open scoped Polynomial

namespace Kakeya.CV

/-- Helper: if map(eval x) G = 0 for irreducible G depending on y, contradiction. -/
lemma map_eval_G_ne_zero {q : MvPolynomial (Fin 2) ℝ} {x : ℝ}
    (hq_irred : Irreducible q) (h_y : 0 ∈ q.vars) :
    Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 => x)) (asPolyY q) ≠ 0 := by
  intro hz
  let G := asPolyY q
  let e := MvPolynomial.finSuccEquiv ℝ 1
  have h_coeff0 : ∀ n, MvPolynomial.eval (fun _ : Fin 1 => x) (G.coeff n) = 0 := by
    intro n
    have h4 : (Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 => x)) G).coeff n = 0 := by
      rw [hz] <;> simp
    simpa [Polynomial.coeff_map] using h4
  have h_dvd_coeff : ∀ n, (MvPolynomial.X 0 - MvPolynomial.C x) ∣ G.coeff n := by
    intro n
    exact factor_theorem_fin1 (h_coeff0 n)
  have h_dvd_G : Polynomial.C (MvPolynomial.X 0 - MvPolynomial.C x) ∣ G := by
    have h_iff : Polynomial.C (MvPolynomial.X 0 - MvPolynomial.C x) ∣ G ↔
        ∀ n, (MvPolynomial.X 0 - MvPolynomial.C x) ∣ G.coeff n :=
      Polynomial.C_dvd_iff_dvd_coeff (MvPolynomial.X 0 - MvPolynomial.C x) G
    exact h_iff.mpr h_dvd_coeff
  rcases h_dvd_G with ⟨c', hc⟩
  let H' := e.symm (Polynomial.C (MvPolynomial.X 0 - MvPolynomial.C x))
  have h_eH' : e H' = Polynomial.C (MvPolynomial.X 0 - MvPolynomial.C x) := by
    dsimp only [H'] <;> rw [e.apply_symm_apply]
  have h_step1 : e (e.symm c') = c' := e.apply_symm_apply c'
  have h_eq1 : Polynomial.C (MvPolynomial.X 0 - MvPolynomial.C x) * c' = G := hc.symm
  have h_main : H' ∣ q := by
    refine ⟨e.symm c', ?_⟩
    have h9 : e (H' * e.symm c') = e q := by
      calc e (H' * e.symm c')
        = e H' * e (e.symm c') := by rw [map_mul]
      _ = e H' * c' := by rw [h_step1]
      _ = Polynomial.C (MvPolynomial.X 0 - MvPolynomial.C x) * c' := by rw [h_eH']
      _ = G := h_eq1
      _ = e q := by dsimp only [G, asPolyY] <;> rfl
    exact e.injective h9.symm
  have hC_sub : (Polynomial.C (MvPolynomial.X 0 - MvPolynomial.C x) : Polynomial (MvPolynomial (Fin 1) ℝ)) =
      Polynomial.C (MvPolynomial.X 0) - Polynomial.C (MvPolynomial.C x) := by
    rw [map_sub]
  have h1 : H' = e.symm (Polynomial.C (MvPolynomial.X 0) - Polynomial.C (MvPolynomial.C x)) := by
    dsimp only [H'] <;> exact congr_arg e.symm hC_sub
  have h2 : e.symm (Polynomial.C (MvPolynomial.X 0) - Polynomial.C (MvPolynomial.C x)) =
      e.symm (Polynomial.C (MvPolynomial.X 0)) - e.symm (Polynomial.C (MvPolynomial.C x)) := by
    rw [map_sub]
  have h3 : e.symm (Polynomial.C (MvPolynomial.X 0)) = MvPolynomial.X 1 := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (MvPolynomial.finSuccEquiv_X_succ (j := 0)).symm
  have h4 : e.symm (Polynomial.C (MvPolynomial.C x)) = MvPolynomial.C x := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (e.commutes x).symm
  have h_eq : H' = (MvPolynomial.X 1 - MvPolynomial.C x) := by
    rw [h1, h2, h3, h4]
  rw [h_eq] at h_main
  have h_dvd_q : (MvPolynomial.X 1 - MvPolynomial.C x) ∣ q := h_main
  have h_not_unit : ¬ IsUnit (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C x) := by
    intro h
    have h7 : ∀ (v : Fin 2 → ℝ), MvPolynomial.eval v (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C x) ≠ 0 := by
      intro v
      have h8 : IsUnit (MvPolynomial.eval v (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C x)) := h.map (MvPolynomial.eval v)
      exact IsUnit.ne_zero h8
    have h9 := h7 (fun i => if i = 1 then x else 0)
    simp at h9 <;> exact h9 rfl
  rcases h_dvd_q with ⟨b, hb⟩
  have h_eq_q : q = (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C x) * b := by
    exact hb
  have h_disj : IsUnit (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C x) ∨ IsUnit b :=
    hq_irred.2 h_eq_q
  cases h_disj with
  | inl hunit => exfalso; exact h_not_unit hunit
  | inr hunitb =>
    have h_b_isUnit : IsUnit b := hunitb
    have h2 : ∃ (c : ℝ), c ≠ 0 ∧ b = MvPolynomial.C c :=
      isUnit_mvPolynomial_over_field.mp h_b_isUnit
    rcases h2 with ⟨c, hc, huc⟩
    have h_indep : pderiv (0 : Fin 2) q = 0 := by
      rw [h_eq_q, huc]
      have h1 : (0 : Fin 2) ≠ 1 := by decide
      simp [MvPolynomial.pderiv_X_of_ne h1] <;> ring
    exact SingularSet.pderiv_ne_zero_of_mem_vars h_y h_indep

/-- Irreducible plane curve intersected with coprime polynomial has finite zero set. -/
lemma irreducible_plane_curve_finite {q f : MvPolynomial (Fin 2) ℝ}
    (hq_irred : Irreducible q) (hf : f ≠ 0)
    (hcop : ∀ h, h ∣ q → h ∣ f → IsUnit h) :
    Set.Finite {p : P2 | polynomialValue q p = 0 ∧ polynomialValue f p = 0} := by
  classical
  let S : Set P2 := {p | polynomialValue q p = 0 ∧ polynomialValue f p = 0}
  by_cases h_y : 0 ∉ q.vars
  · -- Case 1: q doesn't depend on y (var 0)
    let f_ren : Fin 1 → Fin 2 := fun _ => 1
    have hfi : Function.Injective f_ren := by
      intro a b _; fin_cases a <;> fin_cases b <;> rfl
    have h_vars : ↑q.vars ⊆ Set.range f_ren := by
      intro x hx
      have h_xne0 : x ≠ 0 := by
        intro h
        rw [h] at hx
        exact h_y hx
      fin_cases x <;> tauto
    have h1 : ∃ (q1 : MvPolynomial (Fin 1) ℝ),
        MvPolynomial.rename f_ren q1 = q :=
      MvPolynomial.exists_rename_eq_of_vars_subset_range q f_ren hfi h_vars
    rcases h1 with ⟨q1, hq1_eq⟩
    have hq1_ne : q1 ≠ 0 := by
      intro hz
      rw [←hq1_eq] at hq_irred
      rw [hz] at hq_irred
      simp at hq_irred
    let A : Set ℝ := {x | MvPolynomial.eval (fun _ : Fin 1 => x) q1 = 0}
    have hA_finite : Set.Finite A := univariate_finite_roots hq1_ne
    have h_fiber : ∀ (x : ℝ), x ∈ A → Set.Finite {p : P2 | p 1 = x ∧ p ∈ S} := by
      intro x hx
      by_cases h_f_all : ∀ y : ℝ, MvPolynomial.eval (fun i : Fin 2 => if i = 0 then y else x) f = 0
      · exfalso
        have h_fd : (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C x) ∣ f := vanishes_all_y_imp_dvd h_f_all
        have h_qd : (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C x) ∣ q := by
          have h_q1_root : MvPolynomial.eval (fun _ : Fin 1 => x) q1 = 0 := hx
          have h_all : ∀ y : ℝ, MvPolynomial.eval (fun i : Fin 2 => if i = 0 then y else x) q = 0 := by
            intro y
            have h_eval : MvPolynomial.eval (fun i : Fin 2 => if i = 0 then y else x) q =
                MvPolynomial.eval (fun _ : Fin 1 => x) q1 := by
              rw [←hq1_eq, MvPolynomial.eval_rename] <;> rfl
            rw [h_eval, h_q1_root]
          exact vanishes_all_y_imp_dvd h_all
        exact no_common_x_factor hcop h_qd h_fd
      · let Fx := Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 => x)) (asPolyY f)
        have hFx_ne : Fx ≠ 0 := by
          intro hz
          have h_all : ∀ y : ℝ, Polynomial.eval y Fx = 0 := by
            rw [hz] <;> simp
          have h' : ∀ y : ℝ, MvPolynomial.eval (fun i : Fin 2 => if i = 0 then y else x) f = 0 := by
            intro y
            exact asPolyY_eval f x y ▸ h_all y
          exact h_f_all h'
        have h_finite : Set.Finite {y : ℝ | Fx.eval y = 0} := Polynomial.finite_setOf_isRoot hFx_ne
        let g : P2 → ℝ := fun p => p 0
        have h_inj : Set.InjOn g {p : P2 | p 1 = x} := by
          intro p hp q hq h_eq
          ext i
          fin_cases i
          · exact h_eq
          · exact hp.trans hq.symm
        have h_img_sub : g '' {p : P2 | p 1 = x ∧ p ∈ S} ⊆ {y : ℝ | Fx.eval y = 0} := by
          intro y hy
          rcases hy with ⟨p, hp, rfl⟩
          have hpx : p 1 = x := hp.1
          have hpe : (p : Fin 2 → ℝ) = fun i : Fin 2 => if i = 0 then p 0 else x := by
            funext i
            fin_cases i <;> simp [hpx] <;> rfl
          have h_eval : Fx.eval (p 0) = polynomialValue f p := by
            have h1 : Fx.eval (p 0) = MvPolynomial.eval (fun i : Fin 2 => if i = 0 then p 0 else x) f :=
              asPolyY_eval f x (p 0)
            have h2 : (fun i : Fin 2 => p i) = (fun i : Fin 2 => if i = 0 then p 0 else x) := hpe
            have h3 : polynomialValue f p = MvPolynomial.eval (fun i : Fin 2 => p i) f := by rfl
            rw [h3, h2]
            exact h1
          have h_goal : Fx.eval (p 0) = 0 := by
            rw [h_eval]
            exact hp.2.2
          simpa using h_goal
        have h_img_finite : Set.Finite (g '' {p : P2 | p 1 = x ∧ p ∈ S}) :=
          Set.Finite.subset h_finite h_img_sub
        have h_inj' : Set.InjOn g {p : P2 | p 1 = x ∧ p ∈ S} := h_inj.mono (fun p hp => hp.1)
        exact Set.Finite.of_finite_image h_img_finite h_inj'
    have h_union_finite : Set.Finite (⋃ x ∈ A, {p : P2 | p 1 = x ∧ p ∈ S}) :=
      hA_finite.biUnion h_fiber
    have hS_sub : S ⊆ ⋃ x ∈ A, {p : P2 | p 1 = x ∧ p ∈ S} := by
      intro p hp
      have h_q0 : polynomialValue q p = 0 := hp.1
      have h_eval : polynomialValue q p = MvPolynomial.eval (fun _ : Fin 1 => p 1) q1 := by
        have h1 : polynomialValue q p = MvPolynomial.eval (fun i : Fin 2 => p i) q := by rfl
        rw [h1, ←hq1_eq, MvPolynomial.eval_rename] <;> rfl
      have h_xinA : p 1 ∈ A := by
        rw [h_eval] at h_q0
        exact h_q0
      exact Set.mem_iUnion₂.mpr ⟨p 1, h_xinA, by simp [hp]⟩
    exact Set.Finite.subset h_union_finite hS_sub
  · -- Case 2: q depends on y (var 0)
    have h_y' : 0 ∈ q.vars := by tauto
    let G := asPolyY q
    let F := asPolyY f
    have hG_irred : Irreducible G :=
      (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℝ 1).toRingEquiv.toMulEquiv).mpr hq_irred
    have hG_pos : 0 < G.natDegree := by
      by_contra h
      have hG0 : G.natDegree = 0 := by omega
      have h_const : G = Polynomial.C (G.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hG0
      have hderiv : pderiv (0 : Fin 2) q = 0 := by
        have h1 : asPolyY (pderiv (0 : Fin 2) q) = G.derivative := asPolyY_pderiv
        rw [h_const] at h1
        have h2 : asPolyY (pderiv (0 : Fin 2) q) = 0 := by rw [h1] <;> simp
        exact (MvPolynomial.finSuccEquiv ℝ 1).injective h2
      exact SingularSet.pderiv_ne_zero_of_mem_vars h_y' hderiv
    have hcop' : ∀ H, H ∣ G → H ∣ F → IsUnit H := by
      intro H h1 h2
      let e := MvPolynomial.finSuccEquiv ℝ 1
      let H' := e.symm H
      have h_eH' : e H' = H := e.apply_symm_apply H
      have h1' : H' ∣ q := by
        rcases h1 with ⟨c, hc⟩
        refine ⟨e.symm c, ?_⟩
        have h : e (H' * e.symm c) = e q := by
          rw [map_mul, e.apply_symm_apply c, h_eH']
          have h4 : e q = H * c := by simpa [G, asPolyY] using hc
          exact h4.symm
        have h9 : e.symm (e (H' * e.symm c)) = e.symm (e q) := congr_arg e.symm h
        have h10 : H' * e.symm c = q := by
          rwa [e.symm_apply_apply, e.symm_apply_apply] at h9
        exact h10.symm
      have h2' : H' ∣ f := by
        rcases h2 with ⟨c, hc⟩
        refine ⟨e.symm c, ?_⟩
        have h : e (H' * e.symm c) = e f := by
          rw [map_mul, e.apply_symm_apply c, h_eH']
          have h4 : e f = H * c := by simpa [F, asPolyY] using hc
          exact h4.symm
        have h9 : e.symm (e (H' * e.symm c)) = e.symm (e f) := congr_arg e.symm h
        have h10 : H' * e.symm c = f := by
          rwa [e.symm_apply_apply, e.symm_apply_apply] at h9
        exact h10.symm
      have hunit : IsUnit H' := hcop H' h1' h2'
      have hunit' : IsUnit (e H') := hunit.map e.toRingEquiv.toRingHom
      have h_eH' : e H' = H := e.apply_symm_apply H
      rwa [h_eH'] at hunit'
    let R := Polynomial.resultant G F
    have hR_ne : R ≠ 0 := resultant_ne_zero_of_coprime_irreducible hG_irred hG_pos hcop'
    let A : Set ℝ := {x | MvPolynomial.eval (fun _ : Fin 1 => x) R = 0}
    have hA_finite : Set.Finite A := univariate_finite_roots hR_ne
    have h_proj : ∀ p ∈ S, p 1 ∈ A := by
      intro p hp
      let x := p 1
      let y := p 0
      have h_eq : (fun i : Fin 2 => if i = 0 then y else x) = (fun i : Fin 2 => p i) := by
        funext i; fin_cases i <;> simp [y, x] <;> rfl
      have hgi' : MvPolynomial.eval (fun i : Fin 2 => if i = 0 then y else x) q = 0 := by
        rw [h_eq]
        simpa [polynomialValue] using hp.1
      have hf' : MvPolynomial.eval (fun i : Fin 2 => if i = 0 then y else x) f = 0 := by
        rw [h_eq]
        simpa [polynomialValue] using hp.2
      let Gx := Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 => x)) G
      let Fx := Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 => x)) F
      have hGx_root : Gx.eval y = 0 := by
        have h : Gx.eval y = MvPolynomial.eval (fun i : Fin 2 => if i = 0 then y else x) q := asPolyY_eval q x y
        rw [h, hgi']
      have hFx_root : Fx.eval y = 0 := by
        have h : Fx.eval y = MvPolynomial.eval (fun i : Fin 2 => if i = 0 then y else x) f := asPolyY_eval f x y
        rw [h, hf']
      have hGx_ne : Gx ≠ 0 := map_eval_G_ne_zero hq_irred h_y'
      have h_res_std : Gx.resultant Fx = 0 := resultant_zero_of_common_root hGx_root hFx_root hGx_ne
      have hdeg1 : Gx.natDegree ≤ G.natDegree := by
        exact Polynomial.natDegree_map_le (f := MvPolynomial.eval (fun _ : Fin 1 => x)) (p := G)
      let k1 := G.natDegree - Gx.natDegree
      have hk1 : G.natDegree = Gx.natDegree + k1 := by
        rw [Nat.add_sub_of_le hdeg1]
      have h_res1 : Gx.resultant Fx G.natDegree Fx.natDegree = 0 := by
        have hf : Gx.natDegree ≤ Gx.natDegree := by rfl
        have h : Gx.resultant Fx (Gx.natDegree + k1) Fx.natDegree =
            (-1) ^ (Fx.natDegree * k1) * Fx.coeff Fx.natDegree ^ k1 * Gx.resultant Fx Gx.natDegree Fx.natDegree :=
          Polynomial.resultant_add_left_deg (f := Gx) (g := Fx) (m := Gx.natDegree) (n := Fx.natDegree) (k := k1) hf
        have h' : G.natDegree = Gx.natDegree + k1 := hk1
        rw [h']
        rw [h, h_res_std] <;> ring
      have hdeg2 : Fx.natDegree ≤ F.natDegree := by
        exact Polynomial.natDegree_map_le (f := MvPolynomial.eval (fun _ : Fin 1 => x)) (p := F)
      let k2 := F.natDegree - Fx.natDegree
      have hk2 : F.natDegree = Fx.natDegree + k2 := by
        rw [Nat.add_sub_of_le hdeg2]
      have h_res2 : Gx.resultant Fx G.natDegree F.natDegree = 0 := by
        have hg : Fx.natDegree ≤ Fx.natDegree := by rfl
        have h : Gx.resultant Fx G.natDegree (Fx.natDegree + k2) =
            Gx.coeff G.natDegree ^ k2 * Gx.resultant Fx G.natDegree Fx.natDegree :=
          Polynomial.resultant_add_right_deg (f := Gx) (g := Fx) (m := G.natDegree) (n := Fx.natDegree) (k := k2) hg
        have h' : F.natDegree = Fx.natDegree + k2 := hk2
        rw [h']
        rw [h, h_res1] <;> ring
      have h_map : Gx.resultant Fx G.natDegree F.natDegree = MvPolynomial.eval (fun _ : Fin 1 => x) R :=
        Polynomial.resultant_map_map (φ := MvPolynomial.eval (fun _ : Fin 1 => x)) G F G.natDegree F.natDegree
      rw [h_map] at h_res2
      exact h_res2
    have h_fiber : ∀ x ∈ A, Set.Finite {p : P2 | p 1 = x ∧ p ∈ S} := by
      intro x _
      let Gx := Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 => x)) G
      have hGx_ne : Gx ≠ 0 := map_eval_G_ne_zero hq_irred h_y'
      have h_finite : Set.Finite {y : ℝ | Gx.eval y = 0} := Polynomial.finite_setOf_isRoot hGx_ne
      let mkP2 : ℝ → P2 := fun y => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun i : Fin 2 => if i = 0 then y else x)
      have h_sub : {p : P2 | p 1 = x ∧ p ∈ S} ⊆
          mkP2 '' {y : ℝ | Gx.eval y = 0} := by
        intro p hp
        have hpx : p 1 = x := hp.1
        have hpy : p 0 ∈ {y : ℝ | Gx.eval y = 0} := by
          have h_eval : Gx.eval (p 0) = polynomialValue q p := by
            have h1 : Gx.eval (p 0) = MvPolynomial.eval (fun i : Fin 2 => if i = 0 then p 0 else x) q :=
              asPolyY_eval q x (p 0)
            have h2 : (fun i : Fin 2 => p i) = (fun i : Fin 2 => if i = 0 then p 0 else x) := by
              funext i; fin_cases i <;> simp [hpx] <;> rfl
            have h3 : polynomialValue q p = MvPolynomial.eval (fun i : Fin 2 => p i) q := by rfl
            rw [h3, h2]
            exact h1
          have h_zero : Gx.eval (p 0) = 0 := by
            rw [h_eval] <;> exact hp.2.1
          exact h_zero
        refine ⟨p 0, hpy, ?_⟩
        have hpe2 : (p : Fin 2 → ℝ) = fun i : Fin 2 => if i = 0 then p 0 else x := by
          funext i; fin_cases i <;> simp [hpx] <;> rfl
        apply (WithLp.equiv 2 (Fin 2 → ℝ)).injective
        have h10 : (WithLp.equiv 2 (Fin 2 → ℝ)) (mkP2 (p 0)) = (fun i : Fin 2 => if i = 0 then p 0 else x) := by
          simp [mkP2] <;> rfl
        have h11 : (WithLp.equiv 2 (Fin 2 → ℝ)) p = (p : Fin 2 → ℝ) := by rfl
        rw [h11, h10]
        exact hpe2.symm
      exact Set.Finite.subset (Set.Finite.image _ h_finite) h_sub
    have hS_sub : S ⊆ ⋃ x ∈ A, {p : P2 | p 1 = x ∧ p ∈ S} := by
      intro p hp
      exact Set.mem_iUnion₂.mpr ⟨p 1, h_proj p hp, by simp [hp]⟩
    have hS_finite : Set.Finite S := Set.Finite.subset (hA_finite.biUnion h_fiber) hS_sub
    exact hS_finite

end Kakeya.CV
