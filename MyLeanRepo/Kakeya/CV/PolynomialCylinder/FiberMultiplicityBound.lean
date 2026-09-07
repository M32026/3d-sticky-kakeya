import MyLeanRepo.Kakeya.CV.Geometry
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

noncomputable section

open MeasureTheory MvPolynomial Set Metric
open scoped ENNReal

namespace Kakeya.CV

/-! ### Restriction to affine line -/

/-- Restriction of a multivariable polynomial to an affine line. -/
def restrictToLine {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (a e : Point n) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i : Fin n => Polynomial.C (a i) + Polynomial.X * Polynomial.C (e i)) p

lemma restrictToLine_eval {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (a e : Point n) (t : ℝ) :
    (restrictToLine p a e).eval t = polynomialValue p (a + t • e) := by
  let f : Fin n → Polynomial ℝ := fun i =>
    Polynomial.C (a i) + Polynomial.X * Polynomial.C (e i)
  have h_main : (MvPolynomial.eval₂ Polynomial.C f p).eval t =
      MvPolynomial.eval₂ ((Polynomial.evalRingHom t).comp Polynomial.C)
        (fun i => (f i).eval t) p :=
    MvPolynomial.polynomial_eval_eval₂ (x := t) Polynomial.C f p
  have h_eq1 : (restrictToLine p a e).eval t = (MvPolynomial.eval₂ Polynomial.C f p).eval t := by rfl
  rw [h_eq1, h_main]
  have h5 : ((Polynomial.evalRingHom t).comp Polynomial.C) = RingHom.id ℝ := by
    ext r
    simp
  rw [h5]
  congr with i
  simp [f, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_add]
  <;> ring

/-! ### Two-variable zero set measure zero -/

/-- A nonzero polynomial in two variables has a zero set of Lebesgue measure zero. -/
lemma mvPolynomial2_zeroSet_volume_zero (q : MvPolynomial (Fin 2) ℝ) (hq : q ≠ 0) :
    volume {x : Fin 2 → ℝ | MvPolynomial.eval x q = 0} = 0 := by
  -- Swap variables so that finSuccEquiv extracts variable 1 (inner = x1)
  -- and the leading coefficient is in variable 0 (outer = x0), matching Fubini.
  let swap01 : Fin 2 ≃ Fin 2 := Equiv.swap (0 : Fin 2) 1
  let q1 : MvPolynomial (Fin 2) ℝ := MvPolynomial.rename swap01 q
  let q_poly : Polynomial (MvPolynomial (Fin 1) ℝ) := MvPolynomial.finSuccEquiv ℝ 1 q1
  have hq_poly : q_poly ≠ 0 := by
    intro h
    have h' : q1 = 0 := (MvPolynomial.finSuccEquiv ℝ 1).injective h
    have h'' : q = 0 := by
      simpa [q1, MvPolynomial.renameEquiv] using (MvPolynomial.renameEquiv ℝ swap01).injective h'
    exact hq h''
  let m : ℕ := q_poly.natDegree
  let c_m : MvPolynomial (Fin 1) ℝ := q_poly.coeff m
  have hc_m : c_m ≠ 0 := by
    dsimp only [c_m, m]
    rw [Polynomial.coeff_natDegree]
    exact (Polynomial.leadingCoeff_ne_zero.mpr hq_poly)
  let c_m_poly : Polynomial ℝ := MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) c_m
  have hc_m_poly_ne_zero : c_m_poly ≠ 0 :=
    (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).injective.ne hc_m
  let S : Set ℝ := c_m_poly.rootSet ℝ
  have hS_finite : Set.Finite S := Polynomial.rootSet_finite c_m_poly ℝ
  have hS_null : volume S = 0 := hS_finite.measure_zero volume
  have h_ae : ∀ᵐ (x0 : ℝ) ∂volume, x0 ∉ S :=
    measure_eq_zero_iff_ae_notMem.mp hS_null
  -- Evaluation formula: eval at (x0, x1) = polynomial in x1 with coefficients evaluated at x0
  have h_eval : ∀ (x0 x1 : ℝ),
      MvPolynomial.eval (Fin.cases x0 (fun (_ : Fin 1) => x1)) q =
      (Polynomial.map (MvPolynomial.eval (fun (_ : Fin 1) => x0)) q_poly).eval x1 := by
    intro x0 x1
    let F : MvPolynomial (Fin 2) ℝ →+* Polynomial ℝ :=
      (Polynomial.mapRingHom (MvPolynomial.eval (fun (_ : Fin 1) => x0))).comp
        ((MvPolynomial.finSuccEquiv ℝ 1).toRingHom.comp
          (MvPolynomial.renameEquiv ℝ swap01).toRingHom)
    let eval_x1 : Polynomial ℝ →+* ℝ := Polynomial.evalRingHom x1
    let H : MvPolynomial (Fin 2) ℝ →+* ℝ := eval_x1.comp F
    let G : MvPolynomial (Fin 2) ℝ →+* ℝ :=
      MvPolynomial.eval₂Hom (RingHom.id ℝ) (Fin.cases x0 (fun (_ : Fin 1) => x1))
    have h_eq : ∀ (p : MvPolynomial (Fin 2) ℝ), H p = G p := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C r =>
        have h1 : F (MvPolynomial.C r) = Polynomial.C r := by
          simp [F, MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂_C,
            Polynomial.map_C, MvPolynomial.eval_C]
          <;> rfl
        have hH : H (MvPolynomial.C r) = eval_x1 (F (MvPolynomial.C r)) := by rfl
        rw [hH, h1]
        have h4 : eval_x1 (Polynomial.C r) = r := by
          simp [eval_x1, Polynomial.eval_C]
        rw [h4]
        have h3 : G (MvPolynomial.C r) = r := by
          simp [G, MvPolynomial.eval₂_C]
        rw [h3]
      | add p q hp hq =>
        rw [map_add, map_add, hp, hq]
      | mul_X p i hp =>
        have h_i : ∀ (i : Fin 2), H (MvPolynomial.X i) = G (MvPolynomial.X i) := by
          let x : Fin 2 → ℝ := Fin.cases x0 (fun (_ : Fin 1) => x1)
          have hG_def : ∀ (i : Fin 2), G (MvPolynomial.X i) = x i := by
            intro i
            have h : G = MvPolynomial.eval₂Hom (RingHom.id ℝ) x := by rfl
            rw [h]
            simp [MvPolynomial.eval₂_X]
          have h0 : H (MvPolynomial.X (0 : Fin 2)) = G (MvPolynomial.X (0 : Fin 2)) := by
            have h_step1 : (MvPolynomial.renameEquiv ℝ swap01) (MvPolynomial.X (0 : Fin 2)) = MvPolynomial.X (1 : Fin 2) := by
              simp [swap01, MvPolynomial.rename_X] <;> rfl
            have h_step2 : (MvPolynomial.finSuccEquiv ℝ 1) (MvPolynomial.X (1 : Fin 2)) = Polynomial.C (MvPolynomial.X (0 : Fin 1)) :=
              MvPolynomial.finSuccEquiv_X_succ (j := 0)
            have hF : F (MvPolynomial.X (0 : Fin 2)) = Polynomial.C x0 := by
              have h_def : F (MvPolynomial.X (0 : Fin 2)) =
                  Polynomial.map (MvPolynomial.eval (fun (_ : Fin 1) => x0))
                    ((MvPolynomial.finSuccEquiv ℝ 1) ((MvPolynomial.renameEquiv ℝ swap01) (MvPolynomial.X (0 : Fin 2)))) := by rfl
              rw [h_def, h_step1, h_step2]
              simp [Polynomial.map_C, MvPolynomial.eval_X] <;> rfl
            have hH : H (MvPolynomial.X (0 : Fin 2)) = x0 := by
              have hH_def : H (MvPolynomial.X (0 : Fin 2)) = eval_x1 (F (MvPolynomial.X (0 : Fin 2))) := by rfl
              rw [hH_def, hF]
              simp [eval_x1, Polynomial.eval_C]
            have hG : G (MvPolynomial.X (0 : Fin 2)) = x0 := by
              rw [hG_def (0 : Fin 2)] <;> simp [x, Fin.cases_zero]
            rw [hH, hG]
          have h1 : H (MvPolynomial.X (1 : Fin 2)) = G (MvPolynomial.X (1 : Fin 2)) := by
            have h_step1 : (MvPolynomial.renameEquiv ℝ swap01) (MvPolynomial.X (1 : Fin 2)) = MvPolynomial.X (0 : Fin 2) := by
              simp [swap01, MvPolynomial.rename_X] <;> rfl
            have h_step2 : (MvPolynomial.finSuccEquiv ℝ 1) (MvPolynomial.X (0 : Fin 2)) = Polynomial.X :=
              MvPolynomial.finSuccEquiv_X_zero
            have hF : F (MvPolynomial.X (1 : Fin 2)) = Polynomial.X := by
              have h_def : F (MvPolynomial.X (1 : Fin 2)) =
                  Polynomial.map (MvPolynomial.eval (fun (_ : Fin 1) => x0))
                    ((MvPolynomial.finSuccEquiv ℝ 1) ((MvPolynomial.renameEquiv ℝ swap01) (MvPolynomial.X (1 : Fin 2)))) := by rfl
              rw [h_def, h_step1, h_step2]
              simp [Polynomial.map_X] <;> rfl
            have hH : H (MvPolynomial.X (1 : Fin 2)) = x1 := by
              have hH_def : H (MvPolynomial.X (1 : Fin 2)) = eval_x1 (F (MvPolynomial.X (1 : Fin 2))) := by rfl
              rw [hH_def, hF]
              simp [eval_x1, Polynomial.eval_X]
            have hG : G (MvPolynomial.X (1 : Fin 2)) = x1 := by
              rw [hG_def (1 : Fin 2)] <;> simp [x, Fin.cases_succ] <;> rfl
            rw [hH, hG]
          exact Fin.forall_fin_two.mpr ⟨h0, h1⟩
        rw [map_mul, map_mul, hp, h_i i]
    have h : H q = G q := h_eq q
    have h' : (Polynomial.eval x1 (Polynomial.map (MvPolynomial.eval (fun (_ : Fin 1) => x0)) q_poly)) =
        MvPolynomial.eval (Fin.cases x0 (fun (_ : Fin 1) => x1)) q := by
      simpa [H, G, F, eval_x1] using h
    exact h'.symm
  -- For a.e. x0, the fiber in x1 has measure zero
  have h_main : ∀ᵐ (x0 : ℝ) ∂volume,
      volume {x1 : ℝ | MvPolynomial.eval (Fin.cases x0 (fun (_ : Fin 1) => x1)) q = 0} = 0 := by
    filter_upwards [h_ae] with x0 hx0
    let f : MvPolynomial (Fin 1) ℝ →+* ℝ := MvPolynomial.eval (fun (_ : Fin 1) => x0)
    have h_lead : f c_m ≠ 0 := by
      have h_eq : f c_m = c_m_poly.eval x0 := by
        dsimp only [f, c_m_poly]
        have h := MvPolynomial.eval₂_const_uniqueAlgEquiv
          (f := c_m) (φ := RingHom.id ℝ) (a := x0)
        simpa [Polynomial.eval₂_eq_eval_map] using h.symm
      rw [h_eq]
      simpa [S, Polynomial.mem_rootSet, hc_m_poly_ne_zero] using hx0
    let r : Polynomial ℝ := Polynomial.map f q_poly
    have h_coeff_m : r.coeff m = f c_m := by
      dsimp only [r, c_m]
      simpa [Polynomial.coeff_map] using rfl
    have h_ne : r ≠ 0 := by
      intro h
      rw [h] at h_coeff_m
      simp at h_coeff_m
      exact h_lead h_coeff_m.symm
    have h_finite : Set.Finite (r.rootSet ℝ) := Polynomial.rootSet_finite r ℝ
    have h_eq : {x1 : ℝ | MvPolynomial.eval (Fin.cases x0 (fun (_ : Fin 1) => x1)) q = 0} = r.rootSet ℝ := by
      ext x1
      have h5 : MvPolynomial.eval (Fin.cases x0 (fun (_ : Fin 1) => x1)) q = r.eval x1 := h_eval x0 x1
      have h_aeval : (Polynomial.aeval x1) r = Polynomial.eval x1 r := by rfl
      simp only [Set.mem_setOf_eq, Polynomial.mem_rootSet]
      constructor
      · intro h
        exact ⟨h_ne, by rw [h_aeval]; rw [←h5]; exact h⟩
      · rintro ⟨_, h⟩
        rw [h_aeval] at h
        rw [h5]
        exact h
    rw [h_eq]
    exact h_finite.measure_zero volume
  -- Fubini via MeasurableEquiv.finTwoArrow
  let e_meas : MeasurableEquiv (Fin 2 → ℝ) (ℝ × ℝ) := MeasurableEquiv.finTwoArrow
  let Z : Set (Fin 2 → ℝ) := {x | MvPolynomial.eval x q = 0}
  have hZ_closed : IsClosed Z := isClosed_singleton.preimage (MvPolynomial.continuous_eval (p := q))
  have hZ_meas : MeasurableSet Z := hZ_closed.measurableSet
  have h_mp : MeasurePreserving e_meas volume volume := volume_preserving_finTwoArrow ℝ
  let Z' : Set (ℝ × ℝ) := e_meas '' Z
  have hZ'_meas : MeasurableSet Z' := by
    have h : Z' = e_meas.symm ⁻¹' Z := by
      ext z
      simp only [Z', Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro h
        exact ⟨e_meas.symm z, h, e_meas.apply_symm_apply z⟩
    rw [h]
    exact hZ_meas.preimage e_meas.symm.measurable
  have h_fiber : ∀ (x0 : ℝ), {x1 : ℝ | (x0, x1) ∈ Z'} =
      {x1 : ℝ | MvPolynomial.eval (Fin.cases x0 (fun (_ : Fin 1) => x1)) q = 0} := by
    intro x0
    ext x1
    simp only [Z', Z, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, h_eq⟩
      have h_e_y : e_meas y = (y 0, y 1) := by
        dsimp only [e_meas]
        <;> rfl
      have h_pair : (y 0, y 1) = (x0, x1) := by
        rw [←h_e_y, h_eq]
      have h_y0 : y 0 = x0 := by
        exact congr_arg Prod.fst h_pair
      have h_y1 : y 1 = x1 := by
        exact congr_arg Prod.snd h_pair
      have h_y_eq : y = Fin.cases x0 (fun (_ : Fin 1) => x1) := by
        funext i
        fin_cases i <;> simp [h_y0, h_y1] <;> tauto
      rw [h_y_eq] at hy
      exact hy
    · intro h
      let y : Fin 2 → ℝ := Fin.cases x0 (fun (_ : Fin 1) => x1)
      have hy : MvPolynomial.eval y q = 0 := h
      have h_ey : e_meas y = (x0, x1) := by
        dsimp only [e_meas, y] <;> rfl
      exact ⟨y, hy, h_ey⟩
  have h_final : ∀ᵐ (x0 : ℝ) ∂volume, volume {x1 : ℝ | (x0, x1) ∈ Z'} = 0 := by
    filter_upwards [h_main] with x0 hx0
    rw [h_fiber x0]
    exact hx0
  have h_volume_prod : (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume :=
    MeasureTheory.Measure.volume_eq_prod ℝ ℝ
  have h_null : (Measure.prod volume volume) Z' = 0 :=
    Measure.measure_prod_null_of_ae_null hZ'_meas h_final
  have h_volume_Z' : volume Z' = 0 := by
    rw [h_volume_prod]
    exact h_null
  have h_volume_eq : volume Z = volume Z' := by
    have hZ_eq : Z = e_meas ⁻¹' Z' := by
      ext z
      simp [Z', Set.mem_preimage]
      <;> tauto
    rw [hZ_eq]
    have h_nm : NullMeasurableSet Z' volume := hZ'_meas.nullMeasurableSet
    exact h_mp.measure_preimage h_nm
  rw [h_volume_eq]
  exact h_volume_Z'

/-! ### Fiber multiplicity bound -/

/-- Fiber multiplicity bound: for almost every y in the plane perpendicular to e₃,
the polynomial restriction to the fiber line is nonzero and has at most k roots. -/
lemma fiberMultiplicityBound_e3 (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ≠ 0) (k : ℕ) (hk : p.totalDegree ≤ k) :
    ∀ᵐ (y : Fin 2 → ℝ) ∂volume,
      (let eqv := (EuclideanSpace.equiv (Fin 3) ℝ).symm
       let a : Point 3 := eqv (Fin.cases (y 0) (Fin.cases (y 1) (Fin.cases 0 Fin.elim0)))
       let e : Point 3 := eqv (Fin.cases 0 (Fin.cases 0 (Fin.cases 1 Fin.elim0)))
       let q := restrictToLine p a e
       q ≠ 0 ∧ Set.ncard (q.rootSet ℝ) ≤ k) := by
  let swap02 : Fin 3 ≃ Fin 3 := Equiv.swap (0 : Fin 3) 2
  let p' : MvPolynomial (Fin 3) ℝ := MvPolynomial.rename swap02 p
  let p_poly : Polynomial (MvPolynomial (Fin 2) ℝ) := MvPolynomial.finSuccEquiv ℝ 2 p'
  have hp_poly : p_poly ≠ 0 := by
    intro h
    have h' : p' = 0 := (MvPolynomial.finSuccEquiv ℝ 2).injective h
    have h'' : p = 0 := by
      simpa [p', MvPolynomial.renameEquiv] using (MvPolynomial.renameEquiv ℝ swap02).injective h'
    exact hp h''
  let m : ℕ := p_poly.natDegree
  let c_m : MvPolynomial (Fin 2) ℝ := p_poly.coeff m
  have hc_m : c_m ≠ 0 := by
    dsimp only [c_m, m]
    rw [Polynomial.coeff_natDegree]
    exact (Polynomial.leadingCoeff_ne_zero.mpr hp_poly)
  let swap01 : Fin 2 ≃ Fin 2 := Equiv.swap (0 : Fin 2) 1
  let c_m' : MvPolynomial (Fin 2) ℝ := MvPolynomial.rename swap01 c_m
  have hc_m' : c_m' ≠ 0 := (MvPolynomial.renameEquiv ℝ swap01).injective.ne hc_m
  let zeroSet : Set (Fin 2 → ℝ) := {x | MvPolynomial.eval x c_m' = 0}
  have h_null : volume zeroSet = 0 := mvPolynomial2_zeroSet_volume_zero c_m' hc_m'
  -- Degree bound: m ≤ p.totalDegree
  have h_coeff_nonzero : p_poly.coeff m ≠ 0 := by
    dsimp only [m]
    rw [Polynomial.coeff_natDegree]
    exact (Polynomial.leadingCoeff_ne_zero.mpr hp_poly)
  have h_deg_ineq : (p_poly.coeff m).totalDegree + m ≤ p'.totalDegree :=
    MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le p' m h_coeff_nonzero
  have h_rename : p'.totalDegree = p.totalDegree :=
    MvPolynomial.totalDegree_renameEquiv swap02 p
  have h_deg_bound : m ≤ p.totalDegree := by
    rw [h_rename] at h_deg_ineq
    linarith
  -- Bad set: y such that the fiber polynomial is zero
  let badSet : Set (Fin 2 → ℝ) := {y |
      Polynomial.map (MvPolynomial.eval (Fin.cases (y 1) (fun (_ : Fin 1) => y 0))) p_poly = 0}
  -- Bad set is contained in zero set of c_m'
  have h_bad_subset : badSet ⊆ zeroSet := by
    intro y hy
    have h_map_zero : Polynomial.map (MvPolynomial.eval (Fin.cases (y 1) (fun (_ : Fin 1) => y 0))) p_poly = 0 := hy
    have h_coeff_zero : (Polynomial.map (MvPolynomial.eval (Fin.cases (y 1) (fun (_ : Fin 1) => y 0))) p_poly).coeff m = 0 := by
      rw [h_map_zero] <;> simp
    have h_cm_zero : MvPolynomial.eval (Fin.cases (y 1) (fun (_ : Fin 1) => y 0)) c_m = 0 := by
      simpa [Polynomial.coeff_map] using h_coeff_zero
    have h_cm'_zero : MvPolynomial.eval y c_m' = 0 := by
      have h_rename : MvPolynomial.eval y c_m' = MvPolynomial.eval (y ∘ swap01) c_m := by
        rw [MvPolynomial.eval_rename] <;> rfl
      rw [h_rename]
      have h_comp : (y ∘ swap01) = Fin.cases (y 1) (fun (_ : Fin 1) => y 0) := by
        funext i
        fin_cases i <;> simp [swap01, Equiv.swap_apply_def] <;> tauto
      rw [h_comp]
      exact h_cm_zero
    exact h_cm'_zero
  have h_bad_null : volume badSet = 0 := measure_mono_null h_bad_subset h_null
  -- For a.e. y, fiber polynomial is nonzero and has ≤ k roots
  filter_upwards [show ∀ᵐ (y : Fin 2 → ℝ) ∂volume, y ∉ badSet from
    measure_eq_zero_iff_ae_notMem.mp h_bad_null] with y hy
  let eqv := (EuclideanSpace.equiv (Fin 3) ℝ).symm
  let a : Point 3 := eqv (Fin.cases (y 0) (Fin.cases (y 1) (Fin.cases 0 Fin.elim0)))
  let e : Point 3 := eqv (Fin.cases 0 (Fin.cases 0 (Fin.cases 1 Fin.elim0)))
  let x : Fin 2 → ℝ := Fin.cases (y 1) (fun (_ : Fin 1) => y 0)
  let q_y : Polynomial ℝ := Polynomial.map (MvPolynomial.eval x) p_poly
  have hq_y_ne_zero : q_y ≠ 0 := by
    simpa [q_y, badSet] using hy
  -- Polynomial equality: q_y = restrictToLine p a e
  have h_eq_poly : q_y = restrictToLine p a e := by
    apply Polynomial.funext
    intro t
    have h1 : q_y.eval t = MvPolynomial.eval (Fin.cons t x) p' :=
      (MvPolynomial.eval_eq_eval_mv_eval' x t p').symm
    have h2 : MvPolynomial.eval (Fin.cons t x) p' =
        MvPolynomial.eval ((Fin.cons t x) ∘ swap02) p := by
      rw [MvPolynomial.eval_rename] <;> rfl
    let v : Fin 3 → ℝ := Fin.cases (y 0) (Fin.cases (y 1) (Fin.cases 0 Fin.elim0))
    let w : Fin 3 → ℝ := Fin.cases 0 (Fin.cases 0 (Fin.cases 1 Fin.elim0))
    have hv : a = eqv v := by rfl
    have hw : e = eqv w := by rfl
    have h_key : ∀ (f : Fin 3 → ℝ) (i : Fin 3), (eqv f) i = f i := by
      intro f i
      have h1 : (EuclideanSpace.equiv (Fin 3) ℝ) (eqv f) = f :=
        (EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply f
      have h2 : (EuclideanSpace.equiv (Fin 3) ℝ) (eqv f) = (eqv f).ofLp := by rfl
      have h3 : (eqv f).ofLp = f := by
        calc
          (eqv f).ofLp = (EuclideanSpace.equiv (Fin 3) ℝ) (eqv f) := h2.symm
          _ = f := h1
      have h4 : (eqv f) i = (eqv f).ofLp i := by rfl
      rw [h4, h3]
    have hx_eq : x = Fin.cases (y 1) (fun (_ : Fin 1) => y 0) := by
      funext i <;> rfl
    have hx0 : x 0 = y 1 := by
      rw [hx_eq]
      exact Fin.cases_zero
    have hx1 : x 1 = y 0 := by
      rw [hx_eq]
      exact Real.ext_cauchy rfl
    have ha_eval : ∀ i, a i = v i := by
      intro i; rw [hv]; exact h_key v i
    have he_eval : ∀ i, e i = w i := by
      intro i; rw [hw]; exact h_key w i
    have ha0 : a 0 = y 0 := by
      rw [ha_eval 0]
      exact Fin.cases_zero
    have ha1 : a 1 = y 1 := by
      rw [ha_eval 1]
      exact Real.ext_cauchy rfl
    have ha2 : a 2 = 0 := by
      rw [ha_eval 2]
      exact EReal.coe_eq_zero.mp rfl
    have he0 : e 0 = 0 := by
      rw [he_eval 0]
      exact EReal.coe_eq_zero.mp rfl
    have he1 : e 1 = 0 := by
      rw [he_eval 1]
      exact EReal.coe_eq_zero.mp rfl
    have he2 : e 2 = 1 := by
      rw [he_eval 2]
      exact (Real.ext_cauchy rfl).symm
    have h_swap0 : swap02 0 = Fin.succ (1 : Fin 2) := by decide
    have h_swap1 : swap02 1 = Fin.succ (0 : Fin 2) := by decide
    have h_swap2 : swap02 2 = 0 := by decide
    have h3 : ((Fin.cons t x) ∘ swap02) = fun (i : Fin 3) => (a + t • e) i := by
      let f : Fin 3 → ℝ := Fin.cons t x
      have hf0 : f 0 = t := by simp [f]
      have hf1 : f 1 = x 0 := by simp [f]
      have hf2 : f 2 = x 1 := by
        have h22 : (2 : Fin 3) = Fin.succ (1 : Fin 2) := by decide
        rw [h22]
        exact @Fin.cons_succ 2 (fun (_ : Fin 3) => ℝ) t x (1 : Fin 2)
      funext i
      have h_add : (a + t • e) i = a i + t * e i := by simp
      rw [h_add]
      fin_cases i
      · have h_comp : (f ∘ swap02) 0 = f (swap02 0) := by exact rfl
        have h_goal : f (swap02 0) = f 2 := by apply congr_arg f; exact h_swap0
        have h_lhs : (f ∘ swap02) 0 = y 0 := by
          rw [h_comp, h_goal, hf2, hx1]
        have h_rhs : a 0 + t * e 0 = y 0 := by rw [ha0, he0] <;> ring
        exact h_lhs.trans h_rhs.symm
      · have h_comp : (f ∘ swap02) 1 = f (swap02 1) := by exact rfl
        have h_goal : f (swap02 1) = f 1 := by apply congr_arg f; exact h_swap1
        have h_lhs : (f ∘ swap02) 1 = y 1 := by
          rw [h_comp, h_goal, hf1, hx0]
        have h_rhs : a 1 + t * e 1 = y 1 := by rw [ha1, he1] <;> ring
        exact h_lhs.trans h_rhs.symm
      · have h_comp : (f ∘ swap02) 2 = f (swap02 2) := by exact rfl
        have h_goal : f (swap02 2) = f 0 := by apply congr_arg f; exact h_swap2
        have h_lhs : (f ∘ swap02) 2 = t := by
          rw [h_comp, h_goal, hf0]
        have h_rhs : a 2 + t * e 2 = t := by rw [ha2, he2] <;> ring
        exact h_lhs.trans h_rhs.symm
    rw [h1, h2, h3]
    exact (restrictToLine_eval p a e t).symm
  rw [h_eq_poly] at hq_y_ne_zero
  have h_card : Set.ncard ((restrictToLine p a e).rootSet ℝ) ≤ k := by
    have h2 : q_y.natDegree ≤ m := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro i hi
      have h3 : p_poly.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hi
      have h4 : (MvPolynomial.eval x) (p_poly.coeff i) = 0 := by
        rw [h3] <;> simp
      simpa [q_y, Polynomial.coeff_map] using h4
    have h4 : q_y.natDegree ≤ p.totalDegree := h2.trans h_deg_bound
    have h5 : Set.ncard (q_y.rootSet ℝ) ≤ q_y.natDegree :=
      Polynomial.ncard_rootSet_le q_y ℝ
    have h6 : Set.ncard ((restrictToLine p a e).rootSet ℝ) ≤ q_y.natDegree := by
      have h7 : (restrictToLine p a e).rootSet ℝ = q_y.rootSet ℝ := by
        rw [←h_eq_poly]
      rw [h7]
      exact h5
    have h8 : q_y.natDegree ≤ k := h4.trans hk
    linarith
  exact ⟨hq_y_ne_zero, h_card⟩

end Kakeya.CV
