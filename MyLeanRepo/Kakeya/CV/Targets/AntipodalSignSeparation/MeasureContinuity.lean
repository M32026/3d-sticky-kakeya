import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.FiberMultiplicityBound
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Measure-theoretic continuity of polynomial sign regions

This file proves two key measure-theoretic facts needed for the
antipodal sign separation argument:

1. `polynomialZeroSet3_null`: The zero set of a nonzero polynomial in
   three variables has Lebesgue measure zero.

2. `sign_volume_pos_continuity` and `sign_volume_neg_continuity`: For a
   measurable set `R` of finite volume and a sequence of polynomials
   converging pointwise in evaluation to a nonzero polynomial, the
   volumes of the positive (resp. negative) sign regions converge.

The first uses Fubini's theorem together with the existing two-variable
result `mvPolynomial2_zeroSet_volume_zero`. The second uses the dominated
convergence theorem for `ℝ≥0∞`-valued functions.
-/

noncomputable section

open MeasureTheory MvPolynomial Set
open scoped ENNReal

namespace Kakeya.CV

/-- Continuity of polynomial evaluation on Point 3. -/
lemma continuous_polynomialValue3 (p : MvPolynomial (Fin 3) ℝ) :
    Continuous (fun y : Point 3 => polynomialValue p y) := by
  have h1 : Continuous (EuclideanSpace.equiv (Fin 3) ℝ) :=
    (EuclideanSpace.equiv (Fin 3) ℝ).continuous
  have h2 : Continuous (fun f : Fin 3 → ℝ => MvPolynomial.eval f p) :=
    MvPolynomial.continuous_eval p
  exact h2.comp h1

/-- EuclideanSpace.equiv preserves null sets for measurable sets. -/
lemma euclideanEquiv_nullPreserving {n : ℕ} {s : Set (Fin n → ℝ)}
    (hs_meas : MeasurableSet s) (hs : volume s = 0) :
    volume {x : Point n | (EuclideanSpace.equiv (Fin n) ℝ) x ∈ s} = 0 := by
  let e : Point n ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have h_ac : Measure.map e volume ≪ volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure (Measure.map e volume) volume
  have h3 : Measure.map e volume s = 0 := h_ac hs
  have h_meas : Measurable e := e.continuous.measurable
  have h4 : Measure.map e volume s = volume {x : Point n | e x ∈ s} := by
    rw [Measure.map_apply h_meas hs_meas]
    <;> rfl
  rw [h4] at h3
  exact h3

/-- The zero set of a nonzero polynomial in three variables has volume zero. -/
theorem polynomialZeroSet3_null (p : MvPolynomial (Fin 3) ℝ) (hp : p ≠ 0) :
    volume (polynomialZeroSet p) = 0 := by
  -- Work in Fin 3 → ℝ, then transfer to Point 3
  let Z : Set (Fin 3 → ℝ) := {x | MvPolynomial.eval x p = 0}
  have hZ_closed : IsClosed Z :=
    isClosed_eq (MvPolynomial.continuous_eval (p := p)) continuous_const
  have hZ_meas : MeasurableSet Z := hZ_closed.measurableSet

  let q : Polynomial (MvPolynomial (Fin 2) ℝ) := MvPolynomial.finSuccEquiv ℝ 2 p
  have hq : q ≠ 0 := (MvPolynomial.finSuccEquiv ℝ 2).injective.ne hp
  let d : ℕ := q.natDegree
  let q_d : MvPolynomial (Fin 2) ℝ := q.coeff d
  have hq_d : q_d ≠ 0 := by
    dsimp only [q_d, d]
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq
  have h_ind : volume {x : Fin 2 → ℝ | MvPolynomial.eval x q_d = 0} = 0 :=
    mvPolynomial2_zeroSet_volume_zero q_d hq_d

  -- Evaluation formula
  have h_eval : ∀ (y : ℝ) (x : Fin 2 → ℝ),
      MvPolynomial.eval (Fin.cons y x) p =
        Polynomial.eval y (Polynomial.map (MvPolynomial.eval x) q) := by
    intro y x
    exact MvPolynomial.eval_eq_eval_mv_eval' x y p

  -- Measure-preserving equivalence (Fin 3 → ℝ) ≃ᵐ ℝ × (Fin 2 → ℝ)
  let e : (Fin 3 → ℝ) ≃ᵐ (ℝ × (Fin 2 → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have hmp : MeasurePreserving e volume volume :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0

  let S' : Set (ℝ × (Fin 2 → ℝ)) := e '' Z

  have hS'_meas : MeasurableSet S' := by
    have h : S' = e.symm ⁻¹' Z := by
      ext z
      simp only [S', Set.mem_image, Set.mem_preimage]
      <;> constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro h
        exact ⟨e.symm z, h, e.apply_symm_apply z⟩
    rw [h]
    exact hZ_meas.preimage e.symm.measurable

  -- For a.e. x : Fin 2 → ℝ, the fiber {y : ℝ | (y, x) ∈ S'} has measure zero
  have h_ae : ∀ᵐ (x : Fin 2 → ℝ) ∂volume,
      x ∉ {x : Fin 2 → ℝ | MvPolynomial.eval x q_d = 0} :=
    measure_eq_zero_iff_ae_notMem.mp h_ind

  have h_fiber : ∀ᵐ (x : Fin 2 → ℝ) ∂volume,
      volume {y : ℝ | (y, x) ∈ S'} = 0 := by
    filter_upwards [h_ae] with x hx
    have h_qd_eval : MvPolynomial.eval x q_d ≠ 0 := hx
    let f : MvPolynomial (Fin 2) ℝ →+* ℝ := MvPolynomial.eval x
    let r : Polynomial ℝ := Polynomial.map f q
    have h_coeff : r.coeff d = MvPolynomial.eval x q_d := by
      simp [r, f, Polynomial.coeff_map] <;> rfl
    have hr : r ≠ 0 := by
      intro h
      rw [h] at h_coeff
      simp at h_coeff
      exact h_qd_eval h_coeff.symm
    have h_finite : Set.Finite {y : ℝ | r.IsRoot y} :=
      Polynomial.finite_setOf_isRoot hr
    have h_root_eq : {y : ℝ | Polynomial.eval y r = 0} = {y : ℝ | r.IsRoot y} := by
      ext y
      simp [Polynomial.IsRoot]
    have h_fiber_eq : {y : ℝ | (y, x) ∈ S'} = {y : ℝ | Polynomial.eval y r = 0} := by
      ext y
      simp only [S', Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨z, hz, h_eq⟩
        have h3 : MvPolynomial.eval z p = 0 := hz
        have h4 : z = e.symm (y, x) := by
          have h5 : e z = (y, x) := h_eq
          have h6 : e.symm (e z) = e.symm (y, x) := by rw [h5]
          simpa using h6
        rw [h4] at h3
        have h6 : e.symm (y, x) = Fin.cons y x := by
          funext i
          fin_cases i <;> simp [e, MeasurableEquiv.piFinSuccAbove, Fin.cons] <;> rfl
        rw [h6] at h3
        have h7 : MvPolynomial.eval (Fin.cons y x) p = Polynomial.eval y (Polynomial.map (MvPolynomial.eval x) q) := h_eval y x
        rw [h7] at h3
        exact h3
      · intro h3
        have h6 : e.symm (y, x) = Fin.cons y x := by
          funext i
          fin_cases i <;> simp [e, MeasurableEquiv.piFinSuccAbove, Fin.cons] <;> rfl
        refine ⟨e.symm (y, x), ?_, e.apply_symm_apply (y, x)⟩
        have h7 : MvPolynomial.eval (e.symm (y, x)) p = MvPolynomial.eval (Fin.cons y x) p := by rw [h6]
        have h8 : MvPolynomial.eval (Fin.cons y x) p = Polynomial.eval y (Polynomial.map (MvPolynomial.eval x) q) := h_eval y x
        have h9 : MvPolynomial.eval (e.symm (y, x)) p = 0 := by
          rw [h7, h8]
          exact h3
        simpa [Z] using h9
    rw [h_fiber_eq, h_root_eq]
    exact h_finite.measure_zero volume

  -- Swap to (Fin 2 → ℝ) × ℝ for Fubini
  let S'' : Set ((Fin 2 → ℝ) × ℝ) := Prod.swap '' S'
  have hS''_meas : MeasurableSet S'' := by
    have h : S'' = (fun z : (Fin 2 → ℝ) × ℝ => (z.snd, z.fst)) ⁻¹' S' := by
      ext ⟨x, y⟩
      simp only [S'', Set.mem_image, Set.mem_preimage, Prod.mk.injEq]
      constructor
      · rintro ⟨z, hz, h_eq⟩
        have h9 : (z.snd, z.fst) = (x, y) := h_eq
        have h10 : z = (y, x) := by
          have h11 : z.snd = x := by
            exact congr_arg Prod.fst h9
          have h12 : z.fst = y := by
            exact congr_arg Prod.snd h9
          exact Prod.ext h12 h11
        rw [h10] at hz
        exact hz
      · intro hxy
        exact ⟨(y, x), hxy, by simp [Prod.swap]⟩
    rw [h]
    have h_meas : Measurable (Prod.swap : (Fin 2 → ℝ) × ℝ → ℝ × (Fin 2 → ℝ)) :=
      measurable_swap
    exact hS'_meas.preimage h_meas
  have hmp_swap : MeasurePreserving (Prod.swap : ℝ × (Fin 2 → ℝ) → (Fin 2 → ℝ) × ℝ)
      (volume.prod volume) (volume.prod volume) :=
    MeasureTheory.Measure.measurePreserving_swap

  have h_fiber2 : (fun (x : Fin 2 → ℝ) => volume ((fun y : ℝ => (x, y)) ⁻¹' S'')) =ᵐ[volume] 0 := by
    have h_eq : ∀ (x : Fin 2 → ℝ), ((fun y : ℝ => (x, y)) ⁻¹' S'') = {y : ℝ | (y, x) ∈ S'} := by
      intro x
      ext y
      simp [S'', Set.mem_preimage]
      <;> tauto
    have h' : ∀ᵐ (x : Fin 2 → ℝ) ∂volume, volume ((fun y : ℝ => (x, y)) ⁻¹' S'') = 0 := by
      filter_upwards [h_fiber] with x hx
      rw [h_eq x]
      exact hx
    exact h'

  have h_volume_prod : (volume : Measure ((Fin 2 → ℝ) × ℝ)) = volume.prod volume :=
    MeasureTheory.Measure.volume_eq_prod (Fin 2 → ℝ) ℝ

  have h_prod_null : (volume.prod volume) S'' = 0 :=
    MeasureTheory.Measure.measure_prod_null_of_ae_null hS''_meas h_fiber2

  have h_vol_S'' : volume S'' = 0 := by
    rw [h_volume_prod]
    exact h_prod_null

  have h_vol_eq : volume S' = volume S'' := by
    have h : S' = Prod.swap ⁻¹' S'' := by
      ext z
      simp [S''] <;> tauto
    rw [h]
    exact hmp_swap.measure_preimage hS''_meas.nullMeasurableSet

  have h_main : volume Z = volume S' := by
    have h : volume (e ⁻¹' S') = volume S' := hmp.measure_preimage hS'_meas.nullMeasurableSet
    have h2 : e ⁻¹' S' = Z := by
      ext z
      simp [S'] <;> tauto
    rw [h2] at h
    exact h
  have hZ_null : volume Z = 0 := by
    rw [h_main, h_vol_eq, h_vol_S'']

  -- Transfer to Point 3
  have h_transfer : polynomialZeroSet p = {x : Point 3 | (EuclideanSpace.equiv (Fin 3) ℝ) x ∈ Z} := by
    ext x
    simp [polynomialZeroSet, polynomialValue, Z]
    <;> rfl
  rw [h_transfer]
  exact euclideanEquiv_nullPreserving hZ_meas hZ_null

/-- Measurability of the positive sign region of a polynomial. -/
lemma posSignRegion_measurable (p : MvPolynomial (Fin 3) ℝ) :
    MeasurableSet {y : Point 3 | 0 < polynomialValue p y} :=
  isOpen_lt continuous_const (continuous_polynomialValue3 p) |>.measurableSet

/-- Measurability of the negative sign region of a polynomial. -/
lemma negSignRegion_measurable (p : MvPolynomial (Fin 3) ℝ) :
    MeasurableSet {y : Point 3 | polynomialValue p y < 0} :=
  isOpen_lt (continuous_polynomialValue3 p) continuous_const |>.measurableSet

/-- Continuity of the volume of the positive sign region along a
pointwise-convergent sequence of polynomials. -/
theorem sign_volume_pos_continuity
    (R : Set (Point 3)) (hRmeas : MeasurableSet R) (hRfin : volume R < ⊤)
    (pseq : ℕ → MvPolynomial (Fin 3) ℝ) (p : MvPolynomial (Fin 3) ℝ) (hp : p ≠ 0)
    (hconv : ∀ y, Filter.Tendsto (fun m => polynomialValue (pseq m) y)
        Filter.atTop (nhds (polynomialValue p y))) :
    Filter.Tendsto (fun m => volume (R ∩ {y | 0 < polynomialValue (pseq m) y}))
      Filter.atTop (nhds (volume (R ∩ {y | 0 < polynomialValue p y}))) := by
  let F : ℕ → Point 3 → ℝ≥0∞ := fun m =>
    Set.indicator (R ∩ {y | 0 < polynomialValue (pseq m) y}) 1
  let f : Point 3 → ℝ≥0∞ :=
    Set.indicator (R ∩ {y | 0 < polynomialValue p y}) 1
  let bound : Point 3 → ℝ≥0∞ := Set.indicator R 1

  have hF_meas : ∀ m, Measurable (F m) := by
    intro m
    have h1 : MeasurableSet {y : Point 3 | 0 < polynomialValue (pseq m) y} :=
      posSignRegion_measurable (pseq m)
    have h2 : MeasurableSet (R ∩ {y | 0 < polynomialValue (pseq m) y}) :=
      hRmeas.inter h1
    exact measurable_const.indicator h2

  have h_bound : ∀ m, F m ≤ᵐ[volume] bound := by
    intro m
    filter_upwards with y
    by_cases hy : y ∈ R
    · have hby : bound y = 1 := by
        simp [bound, hy, Set.indicator_apply]
      rw [hby]
      have h : F m y ≤ 1 := by
        by_cases h2 : y ∈ R ∩ {y : Point 3 | 0 < polynomialValue (pseq m) y}
        · simp [F, h2, Set.indicator_apply] <;> norm_num
        · have h3 : F m y = 0 := by
            simp [F, h2, Set.indicator_apply] <;> norm_num
          rw [h3] <;> norm_num
      exact h
    · have hFy : F m y = 0 := by
        simp [F, hy, Set.indicator_apply] <;> tauto
      have hby : bound y = 0 := by
        simp [bound, hy, Set.indicator_apply] <;> tauto
      rw [hFy, hby]

  have h_fin : ∫⁻ a, bound a ∂volume ≠ ⊤ := by
    have h : ∫⁻ a, bound a ∂volume = volume R := by
      have h' : ∫⁻ a, Set.indicator R 1 a ∂volume = ∫⁻ a in R, (1 : ℝ≥0∞) := by
        rw [lintegral_indicator hRmeas]
        <;> rfl
      rw [h']
      simp
    rw [h]
    exact hRfin.ne

  have h_null : volume (polynomialZeroSet p) = 0 := polynomialZeroSet3_null p hp

  have h_lim : ∀ᵐ y ∂volume, Filter.Tendsto (fun m => F m y) Filter.atTop (nhds (f y)) := by
    filter_upwards [show ∀ᵐ y ∂volume, y ∉ polynomialZeroSet p from
      measure_eq_zero_iff_ae_notMem.mp h_null] with y hy
    have hpy : polynomialValue p y ≠ 0 := hy
    have hconv' : Filter.Tendsto (fun m => polynomialValue (pseq m) y)
        Filter.atTop (nhds (polynomialValue p y)) := hconv y
    by_cases hR : y ∈ R
    · by_cases hpos : 0 < polynomialValue p y
      · -- p(y) > 0
        have h_nhds : ∀ᶠ (z : ℝ) in nhds (polynomialValue p y), 0 < z :=
          Ioi_mem_nhds hpos
        have h_eventually : ∀ᶠ m in Filter.atTop, 0 < polynomialValue (pseq m) y :=
          hconv'.eventually h_nhds
        have hF_eventually : ∀ᶠ m in Filter.atTop, F m y = 1 := by
          filter_upwards [h_eventually] with m hm
          simp [F, hR, hm, Set.indicator_apply] <;> tauto
        have hfy : f y = 1 := by
          simp [f, hR, hpos, Set.indicator_apply] <;> tauto
        rw [hfy]
        have h_tendsto : Filter.Tendsto (fun m => F m y) Filter.atTop (nhds 1) := by
          have h : (fun m => F m y) =ᶠ[Filter.atTop] fun _ => 1 := hF_eventually
          exact Filter.Tendsto.congr' h.symm tendsto_const_nhds
        exact h_tendsto
      · -- p(y) < 0
        have hneg : polynomialValue p y < 0 := by
          by_contra h
          have : 0 < polynomialValue p y := by
            exact lt_of_le_of_ne (by linarith) hpy.symm
          exact hpos this
        have h_nhds : ∀ᶠ (z : ℝ) in nhds (polynomialValue p y), z < 0 :=
          Iio_mem_nhds hneg
        have h_eventually : ∀ᶠ m in Filter.atTop, polynomialValue (pseq m) y < 0 :=
          hconv'.eventually h_nhds
        have hF_eventually : ∀ᶠ m in Filter.atTop, F m y = 0 := by
          filter_upwards [h_eventually] with m hm
          have hnot : ¬(0 < polynomialValue (pseq m) y) := by linarith
          simp [F, hR, hnot, Set.indicator_apply] <;> norm_num
        have hfy : f y = 0 := by
          have hnot2 : ¬(0 < polynomialValue p y) := by linarith
          simp [f, hR, hnot2, Set.indicator_apply] <;> norm_num
        rw [hfy]
        have h_tendsto : Filter.Tendsto (fun m => F m y) Filter.atTop (nhds 0) := by
          have h : (fun m => F m y) =ᶠ[Filter.atTop] fun _ => 0 := hF_eventually
          exact Filter.Tendsto.congr' h.symm tendsto_const_nhds
        exact h_tendsto
    · -- y ∉ R
      have hF_all : ∀ m, F m y = 0 := by
        intro m
        simp [F, hR, Set.indicator_apply] <;> tauto
      have hfy : f y = 0 := by
        simp [f, hR, Set.indicator_apply] <;> tauto
      rw [hfy]
      have h : ∀ᶠ m in Filter.atTop, F m y = 0 := by
        filter_upwards with m
        exact hF_all m
      have h_tendsto : Filter.Tendsto (fun m => F m y) Filter.atTop (nhds 0) := by
        have h' : (fun m => F m y) =ᶠ[Filter.atTop] fun _ => 0 := h
        exact Filter.Tendsto.congr' h'.symm tendsto_const_nhds
      exact h_tendsto

  have h_main : Filter.Tendsto (fun m => ∫⁻ a, F m a ∂volume)
      Filter.atTop (nhds (∫⁻ a, f a ∂volume)) :=
    MeasureTheory.tendsto_lintegral_of_dominated_convergence
      bound hF_meas h_bound h_fin h_lim

  have h_integral_F : ∀ m, ∫⁻ a, F m a ∂volume = volume (R ∩ {y | 0 < polynomialValue (pseq m) y}) := by
    intro m
    let S_m := R ∩ {y | 0 < polynomialValue (pseq m) y}
    have h2 : MeasurableSet S_m := hRmeas.inter (posSignRegion_measurable (pseq m))
    have h_eq : ∫⁻ a, F m a ∂volume = ∫⁻ a in S_m, (1 : ℝ≥0∞) := by
      rw [lintegral_indicator h2]
      <;> rfl
    rw [h_eq]
    exact MeasureTheory.setLIntegral_one S_m

  have h_integral_f : ∫⁻ a, f a ∂volume = volume (R ∩ {y | 0 < polynomialValue p y}) := by
    let S_p := R ∩ {y | 0 < polynomialValue p y}
    have h2 : MeasurableSet S_p := hRmeas.inter (posSignRegion_measurable p)
    have h_eq : ∫⁻ a, f a ∂volume = ∫⁻ a in S_p, (1 : ℝ≥0∞) := by
      rw [lintegral_indicator h2]
      <;> rfl
    rw [h_eq]
    exact MeasureTheory.setLIntegral_one S_p

  simpa [h_integral_F, h_integral_f] using h_main

/-- Continuity of the volume of the negative sign region along a
pointwise-convergent sequence of polynomials. -/
theorem sign_volume_neg_continuity
    (R : Set (Point 3)) (hRmeas : MeasurableSet R) (hRfin : volume R < ⊤)
    (pseq : ℕ → MvPolynomial (Fin 3) ℝ) (p : MvPolynomial (Fin 3) ℝ) (hp : p ≠ 0)
    (hconv : ∀ y, Filter.Tendsto (fun m => polynomialValue (pseq m) y)
        Filter.atTop (nhds (polynomialValue p y))) :
    Filter.Tendsto (fun m => volume (R ∩ {y | polynomialValue (pseq m) y < 0}))
      Filter.atTop (nhds (volume (R ∩ {y | polynomialValue p y < 0}))) := by
  let qseq : ℕ → MvPolynomial (Fin 3) ℝ := fun m => -pseq m
  let q : MvPolynomial (Fin 3) ℝ := -p
  have hq : q ≠ 0 := by
    intro h
    have h' : p = 0 := by simpa [q] using h
    exact hp h'
  have hconv' : ∀ y, Filter.Tendsto (fun m => polynomialValue (qseq m) y)
      Filter.atTop (nhds (polynomialValue q y)) := by
    intro y
    have h1 : (fun m => polynomialValue (qseq m) y) = fun m => -polynomialValue (pseq m) y := by
      funext m
      simp [qseq, polynomialValue, MvPolynomial.eval_neg] <;> ring
    rw [h1]
    have h2 : polynomialValue q y = -polynomialValue p y := by
      simp [q, polynomialValue, MvPolynomial.eval_neg] <;> ring
    rw [h2]
    exact (hconv y).neg
  have h_main := sign_volume_pos_continuity R hRmeas hRfin qseq q hq hconv'
  have h_eq1 : ∀ m, {y : Point 3 | 0 < polynomialValue (qseq m) y} =
      {y : Point 3 | polynomialValue (pseq m) y < 0} := by
    intro m
    ext y
    simp [qseq, polynomialValue, MvPolynomial.eval_neg]
    <;> ring_nf <;> constructor <;> intro h <;> linarith
  have h_eq2 : {y : Point 3 | 0 < polynomialValue q y} =
      {y : Point 3 | polynomialValue p y < 0} := by
    ext y
    simp [q, polynomialValue, MvPolynomial.eval_neg]
    <;> ring_nf <;> constructor <;> intro h <;> linarith
  simpa [h_eq1, h_eq2] using h_main

end Kakeya.CV
