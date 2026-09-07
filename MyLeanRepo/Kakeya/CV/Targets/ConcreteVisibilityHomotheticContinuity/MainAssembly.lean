import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.Targets.ConcreteVisibilityHomotheticContinuity.HomotheticFromUniform
import MyLeanRepo.Kakeya.CV.Targets.ConcreteVisibilityHomotheticContinuity.DirectionalAreaConvex
import MyLeanRepo.Kakeya.CV.Targets.ConcreteVisibilityHomotheticContinuity.UniformConvergence
import Mathlib.Analysis.Convex.Gauge

/-!
# Main assembly for concrete visibility homothetic continuity

Uses the Minkowski functional (gauge) of the visibility body to connect
pointwise convergence of mollified directional areas to homothetic convergence.
-/

noncomputable section

open MeasureTheory Filter
open scoped Pointwise

namespace Kakeya.CV

theorem concrete_visibility_homothetic_continuity_main
    (hSurface : ConcreteMollifiedSurfaceStatement)
    (hBody : ConcreteMollifiedVisibilityStatement) :
    ConcreteVisibilityHomotheticContinuityStatement := by
  intro k P U c ε x xseq hU_meas hU hε hxseq
  let A : CoefficientSpace P.dim → Point 3 → ℝ :=
    fun y u => concreteMollifiedDirectionalArea P ε y u U
  let p : CoefficientSpace P.dim → Point 3 → ℝ :=
    fun y u => max ‖u‖ (A y u)
  let K : CoefficientSpace P.dim → Set (Point 3) :=
    fun y => concreteMollifiedVisibilityBody P ε y U

  -- Step 1: Homogeneity of A in u
  have hAhom : ∀ (y : CoefficientSpace P.dim) (c : ℝ) (u : Point 3), 0 ≤ c →
      A y (c • u) = c * A y u := by
    intro y c u hc
    exact concreteMollifiedDirectionalArea_homogeneous P ε y c u U hc

  -- Step 2: K y = {u | p y u ≤ 1}
  have hK_eq : ∀ (y : CoefficientSpace P.dim), K y = {u | p y u ≤ 1} := by
    intro y
    ext u
    simp only [K, concreteMollifiedVisibilityBody, p, Set.mem_inter_iff, Set.mem_setOf_eq]
    have h1 : u ∈ unitBall 3 ↔ ‖u‖ ≤ 1 := by
      simp [unitBall, Metric.mem_closedBall] <;> rfl
    rw [h1]
    constructor
    · rintro ⟨h1, h2⟩; exact max_le h1 h2
    · intro h; exact ⟨le_trans (le_max_left _ _) h, le_trans (le_max_right _ _) h⟩

  -- Helper: 0 ∈ interior (K y) for all y
  have h0_interior : ∀ (y : CoefficientSpace P.dim), (0 : Point 3) ∈ interior (K y) := by
    intro y
    have hbody_y := hBody k P U c ε y hU_meas hU hε
    have hconv : Convex ℝ (K y) := hbody_y.1.1
    have hsym : ∀ (u : Point 3), u ∈ K y → -u ∈ K y := hbody_y.2
    have hint : (interior (K y)).Nonempty := hbody_y.1.2.2
    rcases hint with ⟨z, hz⟩
    let hneg_homeo : Homeomorph (Point 3) (Point 3) :=
      { toFun := fun x => -x
        invFun := fun x => -x
        left_inv := by intro x; simp
        right_inv := by intro x; simp
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    let S := Set.image hneg_homeo (interior (K y))
    have h1 : -z ∈ S := ⟨z, hz, by simp [hneg_homeo]⟩
    have h2 : IsOpen S := hneg_homeo.isOpenMap (interior (K y)) isOpen_interior
    have h3 : S ⊆ K y := by
      rintro w ⟨v, hv, rfl⟩
      have h4 : v ∈ K y := interior_subset hv
      exact hsym v h4
    have h4 : S ⊆ interior (K y) := interior_maximal h3 h2
    have hnz : -z ∈ interior (K y) := h4 h1
    have hconv_int : Convex ℝ (interior (K y)) := hconv.interior
    have h : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • (-z) ∈ interior (K y) :=
      hconv_int hz hnz (by norm_num) (by norm_num) (by norm_num)
    have h5 : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • (-z) = (0 : Point 3) := by
      simp <;> abel
    rw [h5] at h; exact h

  -- Step 3: p y u = gauge (K y) u
  have hpgauge : ∀ (y : CoefficientSpace P.dim) (u : Point 3),
      p y u = gauge (K y) u := by
    intro y u
    have hbody_y := hBody k P U c ε y hU_meas hU hε
    have hconv : Convex ℝ (K y) := hbody_y.1.1
    have h0_int : (0 : Point 3) ∈ interior (K y) := h0_interior y
    have h_nhds : K y ∈ nhds (0 : Point 3) := mem_interior_iff_mem_nhds.mp h0_int
    have habs : Absorbent ℝ (K y) := absorbent_nhds_zero h_nhds
    -- Prove gauge K y u ≤ p y u
    have h_le1 : gauge (K y) u ≤ p y u := by
      apply le_of_forall_pos_lt_add
      intro ε' hε'
      let r := p y u + ε' / 2
      have hr_pos : 0 < r := by positivity
      have h1 : ‖r⁻¹ • u‖ < 1 := by
        have h2 : ‖u‖ ≤ p y u := le_max_left _ _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr_pos)]
        have h3 : r⁻¹ * ‖u‖ < 1 := by
          have h4 : r⁻¹ * ‖u‖ ≤ r⁻¹ * p y u := by gcongr
          have h5 : r⁻¹ * p y u < 1 := by
            have h6 : p y u < r := by simp [r] <;> linarith
            have h7 : 0 < r := hr_pos
            calc r⁻¹ * p y u < r⁻¹ * r := by gcongr
              _ = 1 := by field_simp [h7.ne'] <;> ring
          exact h4.trans_lt h5
        exact h3
      have hA1 : A y (r⁻¹ • u) = r⁻¹ * A y u := hAhom y r⁻¹ u (by positivity)
      have h3 : A y (r⁻¹ • u) < 1 := by
        rw [hA1]
        have h4 : A y u ≤ p y u := le_max_right _ _
        have h5 : r⁻¹ * A y u < 1 := by
          have h6 : r⁻¹ * A y u ≤ r⁻¹ * p y u := by gcongr
          have h7 : r⁻¹ * p y u < 1 := by
            have h8 : p y u < r := by simp [r] <;> linarith
            have h9 : 0 < r := hr_pos
            calc r⁻¹ * p y u < r⁻¹ * r := by gcongr
              _ = 1 := by field_simp [h9.ne'] <;> ring
          exact h6.trans_lt h7
        exact h5
      have h4 : r⁻¹ • u ∈ K y := by
        rw [hK_eq y]
        simp only [p, Set.mem_setOf_eq]
        exact max_le h1.le h3.le
      have h5 : u ∈ r • K y := by
        refine ⟨r⁻¹ • u, h4, ?_⟩
        have h6 : r • (r⁻¹ • u) = u := by
          rw [smul_smul]
          have h7 : r * r⁻¹ = 1 := by field_simp [hr_pos.ne']
          rw [h7, one_smul]
        exact h6
      have h7 : gauge (K y) u ≤ r := gauge_le_of_mem hr_pos.le h5
      have h8 : r < p y u + ε' := by simp [r] <;> linarith
      exact h7.trans_lt h8
    -- Prove p y u ≤ gauge K y u
    have h_le2 : p y u ≤ gauge (K y) u := by
      by_contra h
      have h' : gauge (K y) u < p y u := by linarith
      rcases exists_lt_of_gauge_lt habs h' with ⟨b, hb_pos, hb_lt, v, hv, rfl⟩
      have h6 : b⁻¹ • (b • v) ∈ K y := by
        have h7 : b⁻¹ • (b • v) = v := by
          rw [smul_smul]
          have h8 : b⁻¹ * b = 1 := by field_simp [hb_pos.ne']
          rw [h8, one_smul]
        rw [h7]; exact hv
      have h7 : p y (b⁻¹ • (b • v)) ≤ 1 := by
        rw [hK_eq y] at h6 <;> simpa using h6
      have h8 : p y (b⁻¹ • (b • v)) = b⁻¹ * p y (b • v) := by
        have h9 : ‖b⁻¹ • (b • v)‖ = b⁻¹ * ‖b • v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb_pos)]
        have h10 : A y (b⁻¹ • (b • v)) = b⁻¹ * A y (b • v) := hAhom y b⁻¹ (b • v) (by positivity)
        have h11 : max (b⁻¹ * ‖b • v‖) (b⁻¹ * A y (b • v)) = b⁻¹ * p y (b • v) := by
          rw [mul_max_of_nonneg] <;> positivity
        simpa [p, h9, h10] using h11
      rw [h8] at h7
      have h12 : b⁻¹ * p y (b • v) ≤ 1 := h7
      have h13 : p y (b • v) ≤ b := by
        calc p y (b • v)
          = b * (b⁻¹ * p y (b • v)) := by field_simp [hb_pos.ne'] <;> ring
        _ ≤ b * 1 := by gcongr
        _ = b := by ring
      linarith
    exact le_antisymm h_le2 h_le1

  -- Step 4: Convexity of p y
  have hpconv : ∀ (y : CoefficientSpace P.dim), ConvexOn ℝ Set.univ (p y) := by
    intro y
    have hbody_y := hBody k P U c ε y hU_meas hU hε
    have hconv : Convex ℝ (K y) := hbody_y.1.1
    have h0_int : (0 : Point 3) ∈ interior (K y) := h0_interior y
    have h_nhds : K y ∈ nhds (0 : Point 3) := mem_interior_iff_mem_nhds.mp h0_int
    have habs : Absorbent ℝ (K y) := absorbent_nhds_zero h_nhds
    have h_sub : ∀ (u v : Point 3), gauge (K y) (u + v) ≤ gauge (K y) u + gauge (K y) v :=
      fun u v => gauge_add_le hconv habs u v
    have h_hom : ∀ (c : ℝ) (u : Point 3), 0 ≤ c →
        gauge (K y) (c • u) = c * gauge (K y) u :=
      fun c u hc => gauge_smul_of_nonneg hc u
    have h_gauge_conv : ConvexOn ℝ Set.univ (gauge (K y)) := by
      constructor
      · exact convex_univ
      · intro u _ v _ a b ha hb hab
        calc
          gauge (K y) (a • u + b • v)
            ≤ gauge (K y) (a • u) + gauge (K y) (b • v) := h_sub (a • u) (b • v)
          _ = a * gauge (K y) u + b * gauge (K y) v := by
            rw [h_hom a u ha, h_hom b v hb]
    have h_eq : (p y) = gauge (K y) := by funext u; exact hpgauge y u
    rw [h_eq]; exact h_gauge_conv

  -- Step 5: Pointwise convergence of p
  have hpt : ∀ (u : Point 3),
      Tendsto (fun n : ℕ => p (xseq n) u) atTop (nhds (p x u)) := by
    intro u
    have h_cont : Continuous (fun y : CoefficientSpace P.dim => A y u) :=
      (hSurface k P U c ε hU_meas hU hε).2 u
    have h_tendsto : Tendsto (fun n : ℕ => A (xseq n) u) atTop (nhds (A x u)) :=
      (h_cont.tendsto x).comp hxseq
    have h_norm_tendsto : Tendsto (fun n : ℕ => ‖u‖) atTop (nhds ‖u‖) := tendsto_const_nhds
    exact h_norm_tendsto.max h_tendsto

  -- Step 6: Uniform convergence using convexity
  have huni : TendstoUniformlyOn (fun n : ℕ => p (xseq n)) (p x) atTop (unitBall 3) :=
    tendstoUniformlyOn_of_convex_pointwise
      (fun n => p (xseq n)) (p x) (unitBall 3)
      (fun n => hpconv (xseq n)) (hpconv x) hpt
      (isCompact_closedBall (0 : Point 3) 1)

  -- Step 7: Non-negativity and homogeneity of gauges
  have hAm : ∀ (n : ℕ) (u : Point 3), 0 ≤ p (xseq n) u := by
    intro n u; simp [p] <;> exact le_max_of_le_right (by positivity)
  have hBm : ∀ (u : Point 3), 0 ≤ p x u := by
    intro u; simp [p] <;> exact le_max_of_le_right (by positivity)
  have hAh' : ∀ (n : ℕ) (c : ℝ) (u : Point 3), 0 ≤ c →
      p (xseq n) (c • u) = c * p (xseq n) u := by
    intro n c u hc
    have h1 : ‖c • u‖ = c * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    have h2 : A (xseq n) (c • u) = c * A (xseq n) u := hAhom (xseq n) c u hc
    have h3 : max (c * ‖u‖) (c * A (xseq n) u) = c * max ‖u‖ (A (xseq n) u) := by
      rw [mul_max_of_nonneg] <;> linarith
    simpa [p, h1, h2] using h3
  have hBh' : ∀ (c : ℝ) (u : Point 3), 0 ≤ c →
      p x (c • u) = c * p x u := by
    intro c u hc
    have h1 : ‖c • u‖ = c * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    have h2 : A x (c • u) = c * A x u := hAhom x c u hc
    have h3 : max (c * ‖u‖) (c * A x u) = c * max ‖u‖ (A x u) := by
      rw [mul_max_of_nonneg] <;> linarith
    simpa [p, h1, h2] using h3

  -- Step 8: Homothetic convergence
  have h_final : HomotheticConvergesAt 0
      (fun n => unitBall 3 ∩ {u | p (xseq n) u ≤ 1})
      (unitBall 3 ∩ {u | p x u ≤ 1}) :=
    homothetic_converges_of_uniform_gauge
      (fun n => p (xseq n)) (p x) hAm hBm hAh' hBh' huni

  -- Rewrite bodies: unitBall ∩ {p ≤ 1} = {p ≤ 1} = K
  have h_body_eq : ∀ (y : CoefficientSpace P.dim),
      (unitBall 3 ∩ {u | p y u ≤ 1}) = K y := by
    intro y
    have h9 : {u : Point 3 | p y u ≤ 1} ⊆ unitBall 3 := by
      intro u hu
      have h10 : ‖u‖ ≤ p y u := le_max_left _ _
      have h11 : ‖u‖ ≤ 1 := h10.trans hu
      simpa [unitBall, Metric.mem_closedBall] using h11
    have h10 : unitBall 3 ∩ {u | p y u ≤ 1} = {u | p y u ≤ 1} := by
      rw [Set.inter_eq_right.mpr h9]
    rw [h10]
    exact (hK_eq y).symm
  have h_eq1 : (fun n : ℕ => unitBall 3 ∩ {u | p (xseq n) u ≤ 1}) =
      (fun n : ℕ => K (xseq n)) := by
    funext n
    exact h_body_eq (xseq n)
  have h_eq2 : (unitBall 3 ∩ {u | p x u ≤ 1}) = K x := h_body_eq x
  rw [h_eq1, h_eq2] at h_final
  exact h_final

end Kakeya.CV
