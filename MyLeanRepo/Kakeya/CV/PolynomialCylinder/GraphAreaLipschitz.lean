import MyLeanRepo.Kakeya.CV.PolynomialCylinder.GraphAreaFderiv

/-!
# Graph area: Lipschitz and injectivity lemmas
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

-- ============================================================================
-- Key sorry'd lemmas
-- ============================================================================

lemma graph_weight_bound {U : Set R2} {f : R2 → ℝ} {p : MvPolynomial (Fin 3) ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    (h_zero : ∀ y ∈ U, polynomialValue p (graphMap f y) = 0)
    (h_reg : ∀ y ∈ U, (polynomialGradient p (graphMap f y)) 2 ≠ 0)
    {y : R2} (hy : y ∈ U) :
    graphAreaW p (graphMap f y) * ENNReal.ofReal |fderiv ℝ f y e02| ≤ 1 := by
  set x : R3 := graphMap f y with hx_def
  set g : R3 := polynomialGradient p x with hg_def
  have hg2 : g 2 ≠ 0 := h_reg y hy
  have hg_ne_zero : g ≠ 0 := by
    intro h
    have h5 : g 2 = 0 := by
      rw [h] <;> simp
    exact hg2 h5
  have hnorm_g_pos : 0 < ‖g‖ := norm_pos_iff.mpr hg_ne_zero
  have h_diff_at : DifferentiableAt ℝ f y :=
    hf.differentiableAt (hU.mem_nhds hy)
  -- Step 1: composition is locally zero
  have h_local_zero : (fun z : R2 => polynomialValue p (graphMap f z)) =ᶠ[nhds y] (0 : R2 → ℝ) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact h_zero z hz
  have h_fd_zero : HasFDerivAt (fun z : R2 => polynomialValue p (graphMap f z)) (0 : R2 →L[ℝ] ℝ) y := by
    have h_const : HasFDerivAt (fun (_ : R2) => (0 : ℝ)) (0 : R2 →L[ℝ] ℝ) y :=
      hasFDerivAt_const (c := (0 : ℝ)) (x := y)
    exact h_const.congr_of_eventuallyEq h_local_zero
  -- Step 2: chain rule
  have h_fd_p_at : HasFDerivAt (fun v : R3 => polynomialValue p v) (gradientCLM p (graphMap f y)) (graphMap f y) :=
    polynomialValue_fderiv p (graphMap f y)
  have h_fd_graph : HasFDerivAt (graphMap f) (graphMapFderiv f y) y :=
    graphMap_fderiv f y h_diff_at
  have h_fd_chain : HasFDerivAt (fun z : R2 => polynomialValue p (graphMap f z))
      ((gradientCLM p x).comp (graphMapFderiv f y)) y := by
    have h_eq1 : gradientCLM p (graphMap f y) = gradientCLM p x := by
      simp [hx_def]
    have h : HasFDerivAt (fun z : R2 => polynomialValue p (graphMap f z))
        ((gradientCLM p (graphMap f y)).comp (graphMapFderiv f y)) y :=
      h_fd_p_at.comp y h_fd_graph
    rw [h_eq1] at h
    exact h
  have h_key : (gradientCLM p x).comp (graphMapFderiv f y) = (0 : R2 →L[ℝ] ℝ) :=
    h_fd_chain.unique h_fd_zero
  -- Step 3: apply to e02
  have h1 : (gradientCLM p x).comp (graphMapFderiv f y) e02 = 0 := by
    rw [h_key] <;> simp
  have h2 : (gradientCLM p x).comp (graphMapFderiv f y) e02 =
      gradientCLM p x (graphMapFderiv f y e02) := by rfl
  have h3 : gradientCLM p x (graphMapFderiv f y e02) =
      g 0 + g 2 * fderiv ℝ f y e02 := by
    rw [gradientCLM_apply]
    have hg : ∀ i : Fin 3, polynomialValue (MvPolynomial.pderiv i p) x = g i := by
      intro i; simp [hg_def, polynomialGradient]
    have h_v0 : (graphMapFderiv f y e02) 0 = 1 := by simp [graphMapFderiv, e02]
    have h_v1 : (graphMapFderiv f y e02) 1 = 0 := by simp [graphMapFderiv, e02]
    have h_v2 : (graphMapFderiv f y e02) 2 = fderiv ℝ f y e02 := by simp [graphMapFderiv]
    have h_sum : ∑ i : Fin 3, polynomialValue (MvPolynomial.pderiv i p) x * (graphMapFderiv f y e02) i =
        g 0 + g 2 * fderiv ℝ f y e02 := by
      rw [Fin.sum_univ_three, hg 0, hg 1, hg 2, h_v0, h_v1, h_v2] <;> ring
    exact h_sum
  have h_eq : g 0 + g 2 * fderiv ℝ f y e02 = 0 := by
    rw [←h3, ←h2, h1]
  -- Step 4: derive |fderiv e02| = |g 0| / |g 2|
  have h_fderiv_eq : fderiv ℝ f y e02 = -g 0 / g 2 := by
    field_simp [hg2] at h_eq ⊢ <;> linarith
  have h_abs_fderiv : |fderiv ℝ f y e02| = |g 0| / |g 2| := by
    rw [h_fderiv_eq, abs_div, abs_neg]
  -- Step 5: graphAreaW = |g 2| / ‖g‖
  have h_unit : polynomialUnitNormal p x = ‖g‖⁻¹ • g := by
    rw [polynomialUnitNormal]
    have h_norm_ne_zero : ‖g‖ ≠ 0 := hnorm_g_pos.ne'
    rw [dif_neg h_norm_ne_zero] <;> rfl
  have h_inner_e3 : inner ℝ e3 g = g 2 := by
    rw [PiLp.inner_apply]
    have h_e3 : ∀ i : Fin 3, e3 i = if i = 2 then (1 : ℝ) else 0 := by
      intro i; fin_cases i <;> simp [e3] <;> decide
    have h_sum : ∑ i : Fin 3, inner ℝ (e3 i) (g i) = g 2 := by
      have h_mul : ∀ i : Fin 3, inner ℝ (e3 i) (g i) = e3 i * g i := by
        intro i
        exact Real.inner_apply (e3.ofLp i) (g.ofLp i)
      rw [Finset.sum_congr rfl (fun i _ => h_mul i)]
      rw [Fin.sum_univ_three]
      simp [h_e3] <;> ring
    exact h_sum
  have h_inner_unit : inner ℝ e3 (polynomialUnitNormal p x) = g 2 / ‖g‖ := by
    rw [h_unit, inner_smul_right, h_inner_e3]
    <;> field_simp [hnorm_g_pos.ne'] <;> ring
  have h_weight_real : ‖inner ℝ e3 (polynomialUnitNormal p x)‖ = |g 2| / ‖g‖ := by
    rw [h_inner_unit]
    have h_abs : ‖(g 2 / ‖g‖ : ℝ)‖ = |g 2 / ‖g‖| := by
      rw [Real.norm_eq_abs]
    rw [h_abs, abs_div]
    have h_norm_abs : |‖g‖| = ‖g‖ := abs_of_nonneg (by positivity)
    rw [h_norm_abs]
  -- Step 6: product bound
  have h_a_nonneg : 0 ≤ |g 2| / ‖g‖ := by positivity
  have h_b_nonneg : 0 ≤ |fderiv ℝ f y e02| := by positivity
  have h_product : (|g 2| / ‖g‖) * |fderiv ℝ f y e02| = |g 0| / ‖g‖ := by
    rw [h_abs_fderiv]
    field_simp [abs_ne_zero.mpr hg2, hnorm_g_pos.ne'] <;> ring
  have h_abs_g0_le : |g 0| ≤ ‖g‖ := by
    have h_norm_sq : ‖g‖^2 = g 0^2 + g 1^2 + g 2^2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] <;> rfl
    have h1 : |g 0|^2 ≤ ‖g‖^2 := by
      rw [h_norm_sq]
      have h2 : |g 0|^2 = g 0^2 := by simp [sq_abs]
      rw [h2]
      <;> nlinarith
    have h3 : 0 ≤ |g 0| := by positivity
    have h4 : 0 ≤ ‖g‖ := by positivity
    nlinarith
  have h_bound : |g 0| / ‖g‖ ≤ 1 := by
    exact (div_le_one hnorm_g_pos).mpr h_abs_g0_le
  have h_main : graphAreaW p x = ENNReal.ofReal (|g 2| / ‖g‖) := by
    simpa [graphAreaW, h_weight_real] using rfl
  rw [h_main]
  have h_mul : ENNReal.ofReal (|g 2| / ‖g‖) * ENNReal.ofReal |fderiv ℝ f y e02| =
      ENNReal.ofReal ((|g 2| / ‖g‖) * |fderiv ℝ f y e02|) := by
    exact Eq.symm (ENNReal.ofReal_mul h_a_nonneg)
  rw [h_mul, h_product]
  have h_final : ENNReal.ofReal (|g 0| / ‖g‖) ≤ 1 := by
    have h_pos : 0 ≤ |g 0| / ‖g‖ := by positivity
    exact ENNReal.ofReal_le_one.mpr h_bound
  exact h_final

lemma graph_weight_bound' {U : Set R2} {f : R2 → ℝ} {p : MvPolynomial (Fin 3) ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    (h_zero : ∀ y ∈ U, polynomialValue p (graphMap f y) = 0)
    (h_reg : ∀ y ∈ U, (polynomialGradient p (graphMap f y)) 2 ≠ 0)
    {y : R2} (hy : y ∈ U) :
    graphAreaW p (graphMap f y) * ENNReal.ofReal |fderiv ℝ f y e12| ≤ 1 := by
  set x : R3 := graphMap f y with hx_def
  set g : R3 := polynomialGradient p x with hg_def
  have hg2 : g 2 ≠ 0 := h_reg y hy
  have hg_ne_zero : g ≠ 0 := by
    intro h
    have h5 : g 2 = 0 := by rw [h] <;> simp
    exact hg2 h5
  have hnorm_g_pos : 0 < ‖g‖ := norm_pos_iff.mpr hg_ne_zero
  have h_diff_at : DifferentiableAt ℝ f y := hf.differentiableAt (hU.mem_nhds hy)
  have h_local_zero : (fun z : R2 => polynomialValue p (graphMap f z)) =ᶠ[nhds y] (0 : R2 → ℝ) := by
    filter_upwards [hU.mem_nhds hy] with z hz; exact h_zero z hz
  have h_fd_zero : HasFDerivAt (fun z : R2 => polynomialValue p (graphMap f z)) (0 : R2 →L[ℝ] ℝ) y := by
    have h_const : HasFDerivAt (fun (_ : R2) => (0 : ℝ)) (0 : R2 →L[ℝ] ℝ) y := hasFDerivAt_const (c := (0 : ℝ)) (x := y)
    exact h_const.congr_of_eventuallyEq h_local_zero
  have h_fd_p_at : HasFDerivAt (fun v : R3 => polynomialValue p v) (gradientCLM p (graphMap f y)) (graphMap f y) :=
    polynomialValue_fderiv p (graphMap f y)
  have h_fd_graph : HasFDerivAt (graphMap f) (graphMapFderiv f y) y := graphMap_fderiv f y h_diff_at
  have h_fd_chain : HasFDerivAt (fun z : R2 => polynomialValue p (graphMap f z))
      ((gradientCLM p x).comp (graphMapFderiv f y)) y := by
    have h_eq1 : gradientCLM p (graphMap f y) = gradientCLM p x := by simp [hx_def]
    have h := h_fd_p_at.comp y h_fd_graph
    rw [h_eq1] at h; exact h
  have h_key : (gradientCLM p x).comp (graphMapFderiv f y) = (0 : R2 →L[ℝ] ℝ) := h_fd_chain.unique h_fd_zero
  have h1 : (gradientCLM p x).comp (graphMapFderiv f y) e12 = 0 := by rw [h_key] <;> simp
  have h3 : gradientCLM p x (graphMapFderiv f y e12) = g 1 + g 2 * fderiv ℝ f y e12 := by
    rw [gradientCLM_apply]
    have hg : ∀ i : Fin 3, polynomialValue (MvPolynomial.pderiv i p) x = g i := by
      intro i; simp [hg_def, polynomialGradient]
    have h_v0 : (graphMapFderiv f y e12) 0 = 0 := by simp [graphMapFderiv, e12]
    have h_v1 : (graphMapFderiv f y e12) 1 = 1 := by simp [graphMapFderiv, e12]
    have h_v2 : (graphMapFderiv f y e12) 2 = fderiv ℝ f y e12 := by simp [graphMapFderiv]
    have h_sum : ∑ i : Fin 3, polynomialValue (MvPolynomial.pderiv i p) x * (graphMapFderiv f y e12) i =
        g 1 + g 2 * fderiv ℝ f y e12 := by
      rw [Fin.sum_univ_three, hg 0, hg 1, hg 2, h_v0, h_v1, h_v2] <;> ring
    exact h_sum
  have h_eq : g 1 + g 2 * fderiv ℝ f y e12 = 0 := by
    have h2 : (gradientCLM p x).comp (graphMapFderiv f y) e12 = gradientCLM p x (graphMapFderiv f y e12) := by rfl
    rw [←h3, ←h2, h1]
  have h_fderiv_eq : fderiv ℝ f y e12 = -g 1 / g 2 := by
    field_simp [hg2] at h_eq ⊢ <;> linarith
  have h_abs_fderiv : |fderiv ℝ f y e12| = |g 1| / |g 2| := by
    rw [h_fderiv_eq, abs_div, abs_neg]
  have h_inner_e3 : inner ℝ e3 g = g 2 := by
    rw [PiLp.inner_apply]
    have h_e3 : ∀ i : Fin 3, e3 i = if i = 2 then (1 : ℝ) else 0 := by
      intro i; fin_cases i <;> simp [e3] <;> decide
    have h_sum : ∑ i : Fin 3, inner ℝ (e3 i) (g i) = g 2 := by
      have h_mul : ∀ i : Fin 3, inner ℝ (e3 i) (g i) = e3 i * g i := by
        intro i
        exact Real.inner_apply (e3.ofLp i) (g.ofLp i)
      rw [Finset.sum_congr rfl (fun i _ => h_mul i), Fin.sum_univ_three]
      simp [h_e3] <;> ring
    exact h_sum
  have h_weight_real : ‖inner ℝ e3 (polynomialUnitNormal p x)‖ = |g 2| / ‖g‖ := by
    have h_unit : polynomialUnitNormal p x = ‖g‖⁻¹ • g := by
      rw [polynomialUnitNormal]; have h_norm_ne_zero : ‖g‖ ≠ 0 := hnorm_g_pos.ne'
      rw [dif_neg h_norm_ne_zero] <;> rfl
    have h_inner_unit : inner ℝ e3 (polynomialUnitNormal p x) = g 2 / ‖g‖ := by
      rw [h_unit, inner_smul_right, h_inner_e3] <;> field_simp [hnorm_g_pos.ne'] <;> ring
    rw [h_inner_unit]
    have h_abs : ‖(g 2 / ‖g‖ : ℝ)‖ = |g 2 / ‖g‖| := by rw [Real.norm_eq_abs]
    rw [h_abs, abs_div]; have h_norm_abs : |‖g‖| = ‖g‖ := abs_of_nonneg (by positivity)
    rw [h_norm_abs]
  have h_product : (|g 2| / ‖g‖) * |fderiv ℝ f y e12| = |g 1| / ‖g‖ := by
    rw [h_abs_fderiv]; field_simp [abs_ne_zero.mpr hg2, hnorm_g_pos.ne'] <;> ring
  have h_abs_g1_le : |g 1| ≤ ‖g‖ := by
    have h_norm_sq : ‖g‖^2 = g 0^2 + g 1^2 + g 2^2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] <;> rfl
    have h1 : |g 1|^2 ≤ ‖g‖^2 := by
      rw [h_norm_sq]; have h2 : |g 1|^2 = g 1^2 := by simp [sq_abs]
      rw [h2] <;> nlinarith
    have h3 : 0 ≤ |g 1| := by positivity
    have h4 : 0 ≤ ‖g‖ := by positivity
    nlinarith
  have h_bound : |g 1| / ‖g‖ ≤ 1 := (div_le_one hnorm_g_pos).mpr h_abs_g1_le
  have h_main : graphAreaW p x = ENNReal.ofReal (|g 2| / ‖g‖) := by
    simpa [graphAreaW, h_weight_real] using rfl
  rw [h_main]
  have h_pos1 : 0 ≤ |g 2| / ‖g‖ := by positivity
  have h_mul : ENNReal.ofReal (|g 2| / ‖g‖) * ENNReal.ofReal |fderiv ℝ f y e12| =
      ENNReal.ofReal ((|g 2| / ‖g‖) * |fderiv ℝ f y e12|) :=
    (ENNReal.ofReal_mul (hp := h_pos1)).symm
  rw [h_mul, h_product]
  have h_final : ENNReal.ofReal (|g 1| / ‖g‖) ≤ 1 := by
    have h_pos : 0 ≤ |g 1| / ‖g‖ := by positivity
    exact ENNReal.ofReal_le_one.mpr h_bound
  exact h_final

lemma graph_lipschitz_after_change_C {U : Set R2} {f : R2 → ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℝ f U) {V : Set R2} (hV : Convex ℝ V) (hV_sub : V ⊆ U)
    (h1 : ∀ y ∈ V, (fderiv ℝ f y e02)^2 ≥ (81 / 100 : ℝ) * (fderiv ℝ f y e12)^2)
    (h2 : ∀ y ∈ V, (fderiv ℝ f y e02)^2 ≥ (9025 / 10000 : ℝ)) :
    ∀ (x y : R2), x ∈ V → y ∈ V →
      ‖graphMap f x - graphMap f y‖ ≤ 2 * ‖graphG f x - graphG f y‖ := by
  intro x y hx hy
  rcases mvt_on_segment (V := V) hU hf hV hV_sub x y hx hy with ⟨ξ, hξV, h_mvt⟩
  let δx : ℝ := (x - y) 0
  let δy : ℝ := (x - y) 1
  let Δf : ℝ := f x - f y
  let c := fderiv ℝ f ξ e02
  let d := fderiv ℝ f ξ e12
  have h_Δf : Δf = c * δx + d * δy := by
    have h : fderiv ℝ f ξ (x - y) = c * δx + d * δy := fderiv_decomp f ξ (x - y)
    have h_eq : f x - f y = fderiv ℝ f ξ (x - y) := h_mvt
    have h9 : f x - f y = c * δx + d * δy := by rw [h_eq, h]
    exact h9
  have hc1 : c^2 ≥ (81 / 100 : ℝ) * d^2 := h1 ξ hξV
  have hc2 : c^2 ≥ (9025 / 10000 : ℝ) := h2 ξ hξV
  have h_alg : δx^2 ≤ 3 * δy^2 + 3 * Δf^2 := by
    have h := algebraic_ineq_C δx δy c d hc1 hc2
    have h_cd : c * δx + d * δy = Δf := by rw [h_Δf] <;> ring
    rw [h_cd] at h; exact h
  have h_norm_map : ‖graphMap f x - graphMap f y‖^2 = δx^2 + δy^2 + Δf^2 := by
    rw [norm_sq_R3 (graphMap f x - graphMap f y)]
    have h1 : (graphMap f x - graphMap f y) 0 = δx := by simp [graphMap, δx] <;> ring
    have h2 : (graphMap f x - graphMap f y) 1 = δy := by simp [graphMap, δy] <;> ring
    have h3 : (graphMap f x - graphMap f y) 2 = Δf := by simp [graphMap, Δf] <;> ring
    rw [h1, h2, h3] <;> ring
  have h_norm_G : ‖graphG f x - graphG f y‖^2 = δy^2 + Δf^2 := by
    rw [norm_sq_R2 (graphG f x - graphG f y)]
    have h1 : (graphG f x - graphG f y) 0 = δy := by simp [graphG, δy] <;> ring
    have h2 : (graphG f x - graphG f y) 1 = Δf := by simp [graphG, Δf] <;> ring
    rw [h1, h2] <;> ring
  have h_main : ‖graphMap f x - graphMap f y‖^2 ≤ 4 * ‖graphG f x - graphG f y‖^2 := by
    rw [h_norm_map, h_norm_G]; nlinarith
  have h_nonneg1 : 0 ≤ ‖graphMap f x - graphMap f y‖ := by positivity
  have h_nonneg2 : 0 ≤ ‖graphG f x - graphG f y‖ := by positivity
  nlinarith [sq_nonneg (‖graphMap f x - graphMap f y‖ - 2 * ‖graphG f x - graphG f y‖)]

lemma graph_lipschitz_after_change_C' {U : Set R2} {f : R2 → ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℝ f U) {V : Set R2} (hV : Convex ℝ V) (hV_sub : V ⊆ U)
    (h1 : ∀ y ∈ V, (fderiv ℝ f y e12)^2 ≥ (81 / 100 : ℝ) * (fderiv ℝ f y e02)^2)
    (h2 : ∀ y ∈ V, (fderiv ℝ f y e12)^2 ≥ (9025 / 10000 : ℝ)) :
    ∀ (x y : R2), x ∈ V → y ∈ V →
      ‖graphMap f x - graphMap f y‖ ≤ 2 * ‖graphG' f x - graphG' f y‖ := by
  intro x y hx hy
  rcases mvt_on_segment (V := V) hU hf hV hV_sub x y hx hy with ⟨ξ, hξV, h_mvt⟩
  let δx : ℝ := (x - y) 0
  let δy : ℝ := (x - y) 1
  let Δf : ℝ := f x - f y
  let c := fderiv ℝ f ξ e12
  let d := fderiv ℝ f ξ e02
  have h_Δf : Δf = d * δx + c * δy := by
    have h : fderiv ℝ f ξ (x - y) = d * δx + c * δy := fderiv_decomp f ξ (x - y)
    have h_eq : f x - f y = fderiv ℝ f ξ (x - y) := h_mvt
    have h9 : f x - f y = d * δx + c * δy := by rw [h_eq, h]
    exact h9
  have hc1 : c^2 ≥ (81 / 100 : ℝ) * d^2 := h1 ξ hξV
  have hc2 : c^2 ≥ (9025 / 10000 : ℝ) := h2 ξ hξV
  have h_alg : δy^2 ≤ 3 * δx^2 + 3 * Δf^2 := by
    have h := algebraic_ineq_C δy δx c d hc1 hc2
    have h_cd : c * δy + d * δx = Δf := by rw [h_Δf] <;> ring
    rw [h_cd] at h; exact h
  have h_norm_map : ‖graphMap f x - graphMap f y‖^2 = δx^2 + δy^2 + Δf^2 := by
    rw [norm_sq_R3 (graphMap f x - graphMap f y)]
    have h1 : (graphMap f x - graphMap f y) 0 = δx := by simp [graphMap, δx] <;> ring
    have h2 : (graphMap f x - graphMap f y) 1 = δy := by simp [graphMap, δy] <;> ring
    have h3 : (graphMap f x - graphMap f y) 2 = Δf := by simp [graphMap, Δf] <;> ring
    rw [h1, h2, h3] <;> ring
  have h_norm_G : ‖graphG' f x - graphG' f y‖^2 = δx^2 + Δf^2 := by
    rw [norm_sq_R2 (graphG' f x - graphG' f y)]
    have h1 : (graphG' f x - graphG' f y) 0 = δx := by simp [graphG', δx] <;> ring
    have h2 : (graphG' f x - graphG' f y) 1 = Δf := by simp [graphG', Δf] <;> ring
    rw [h1, h2] <;> ring
  have h_main : ‖graphMap f x - graphMap f y‖^2 ≤ 4 * ‖graphG' f x - graphG' f y‖^2 := by
    rw [h_norm_map, h_norm_G]; nlinarith
  have h_nonneg1 : 0 ≤ ‖graphMap f x - graphMap f y‖ := by positivity
  have h_nonneg2 : 0 ≤ ‖graphG' f x - graphG' f y‖ := by positivity
  nlinarith [sq_nonneg (‖graphMap f x - graphMap f y‖ - 2 * ‖graphG' f x - graphG' f y‖)]

lemma graphG_injective_on_convex {U : Set R2} {f : R2 → ℝ} (hU : IsOpen U)
    (hf : DifferentiableOn ℝ f U) {V : Set R2} (hV : Convex ℝ V) (hV_sub : V ⊆ U)
    (hfx : ∀ y ∈ V, fderiv ℝ f y e02 ≠ 0) :
    Set.InjOn (graphG f) V := by
  intro x hx y hy h_eq
  have h_y1 : x 1 = y 1 := by
    have h : (graphG f x) 0 = (graphG f y) 0 := by rw [h_eq]
    simpa [graphG] using h
  have h_f : f x = f y := by
    have h : (graphG f x) 1 = (graphG f y) 1 := by rw [h_eq]
    simpa [graphG] using h
  rcases mvt_on_segment (V := V) hU hf hV hV_sub x y hx hy with ⟨ξ, hξV, h_mvt⟩
  have h_y1' : (x - y) 1 = 0 := by simp [h_y1] <;> linarith
  have h_decomp : fderiv ℝ f ξ (x - y) = (fderiv ℝ f ξ e02) * ((x - y) 0) := by
    have h : fderiv ℝ f ξ (x - y) = (fderiv ℝ f ξ e02) * ((x - y) 0) + (fderiv ℝ f ξ e12) * ((x - y) 1) :=
      fderiv_decomp f ξ (x - y)
    rw [h, h_y1'] <;> ring
  have h6 : fderiv ℝ f ξ (x - y) = 0 := by
    have h7 : f x - f y = 0 := by rw [h_f] <;> linarith
    rw [←h_mvt, h7]
  have h_eq3 : (fderiv ℝ f ξ e02) * ((x - y) 0) = 0 := by
    rw [h_decomp] at h6; exact h6
  have hfx_ne : fderiv ℝ f ξ e02 ≠ 0 := hfx ξ hξV
  have h_x0 : (x - y) 0 = 0 := by
    apply (mul_eq_zero.mp h_eq3).resolve_left hfx_ne
  have h_x0' : x 0 = y 0 := by
    have h : (x - y) 0 = x 0 - y 0 := by simp
    rw [h] at h_x0; linarith
  have h_xeq : x = y := by
    ext i; fin_cases i <;> simp [h_x0', h_y1] <;> linarith
  exact h_xeq

lemma graphG'_injective_on_convex {U : Set R2} {f : R2 → ℝ} (hU : IsOpen U)
    (hf : DifferentiableOn ℝ f U) {V : Set R2} (hV : Convex ℝ V) (hV_sub : V ⊆ U)
    (hfy : ∀ y ∈ V, fderiv ℝ f y e12 ≠ 0) :
    Set.InjOn (graphG' f) V := by
  intro x hx y hy h_eq
  have h_x0 : x 0 = y 0 := by
    have h : (graphG' f x) 0 = (graphG' f y) 0 := by rw [h_eq]
    simpa [graphG'] using h
  have h_f : f x = f y := by
    have h : (graphG' f x) 1 = (graphG' f y) 1 := by rw [h_eq]
    simpa [graphG'] using h
  rcases mvt_on_segment (V := V) hU hf hV hV_sub x y hx hy with ⟨ξ, hξV, h_mvt⟩
  have h_x0' : (x - y) 0 = 0 := by simp [h_x0] <;> linarith
  have h_decomp : fderiv ℝ f ξ (x - y) = (fderiv ℝ f ξ e12) * ((x - y) 1) := by
    have h : fderiv ℝ f ξ (x - y) = (fderiv ℝ f ξ e02) * ((x - y) 0) + (fderiv ℝ f ξ e12) * ((x - y) 1) :=
      fderiv_decomp f ξ (x - y)
    rw [h, h_x0'] <;> ring
  have h6 : fderiv ℝ f ξ (x - y) = 0 := by
    have h7 : f x - f y = 0 := by rw [h_f] <;> linarith
    rw [←h_mvt, h7]
  have h_eq3 : (fderiv ℝ f ξ e12) * ((x - y) 1) = 0 := by
    rw [h_decomp] at h6; exact h6
  have hfy_ne : fderiv ℝ f ξ e12 ≠ 0 := hfy ξ hξV
  have h_y1 : (x - y) 1 = 0 := by
    apply (mul_eq_zero.mp h_eq3).resolve_left hfy_ne
  have h_y1' : x 1 = y 1 := by
    have h : (x - y) 1 = x 1 - y 1 := by simp
    rw [h] at h_y1; linarith
  have h_xeq : x = y := by
    ext i; fin_cases i <;> simp [h_x0, h_y1'] <;> linarith
  exact h_xeq

lemma graphMap_flat_lipschitz {U : Set R2} {f : R2 → ℝ} (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    {V : Set R2} (hV : Convex ℝ V) (hV_sub : V ⊆ U)
    (hfx : ∀ y ∈ V, (fderiv ℝ f y e02)^2 ≤ 1)
    (hfy : ∀ y ∈ V, (fderiv ℝ f y e12)^2 ≤ 1) :
    LipschitzOnWith (⟨Real.sqrt 3, Real.sqrt_nonneg 3⟩ : NNReal) (graphMap f) V := by
  have h_main : ∀ (x y : R2), x ∈ V → y ∈ V →
      ‖graphMap f x - graphMap f y‖ ≤ (Real.sqrt 3 : ℝ) * ‖x - y‖ := by
    intro x y hx hy
    rcases mvt_on_segment (V := V) hU hf hV hV_sub x y hx hy with ⟨ξ, hξV, h_mvt⟩
    let δx : ℝ := (x - y) 0
    let δy : ℝ := (x - y) 1
    let Δf : ℝ := f x - f y
    let c := fderiv ℝ f ξ e02
    let d := fderiv ℝ f ξ e12
    have h_Δf : Δf = c * δx + d * δy := by
      have h : fderiv ℝ f ξ (x - y) = c * δx + d * δy := fderiv_decomp f ξ (x - y)
      have h_eq : f x - f y = fderiv ℝ f ξ (x - y) := h_mvt
      have h9 : f x - f y = c * δx + d * δy := by rw [h_eq, h]
      exact h9
    have hc : c^2 ≤ 1 := hfx ξ hξV
    have hd : d^2 ≤ 1 := hfy ξ hξV
    have h_abs_c : |c| ≤ 1 := by
      have h1 : c^2 ≤ 1 := hc
      have h2 : |c|^2 ≤ 1 := by simpa [sq_abs] using h1
      nlinarith [abs_nonneg c]
    have h_abs_d : |d| ≤ 1 := by
      have h1 : d^2 ≤ 1 := hd
      have h2 : |d|^2 ≤ 1 := by simpa [sq_abs] using h1
      nlinarith [abs_nonneg d]
    have h_Δf_bound : |Δf| ≤ |δx| + |δy| := by
      rw [h_Δf]
      calc |c * δx + d * δy|
        ≤ |c * δx| + |d * δy| := by exact abs_add_le (c * δx) (d * δy)
      _ = |c| * |δx| + |d| * |δy| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * |δx| + 1 * |δy| := by gcongr <;> linarith
      _ = |δx| + |δy| := by ring
    have h_Δf_sq2 : Δf^2 ≤ 2 * (δx^2 + δy^2) := by
      have h11 : |Δf| ≤ |δx| + |δy| := h_Δf_bound
      have h12 : Δf^2 = |Δf|^2 := by simp [sq_abs]
      have h13 : 0 ≤ |Δf| := by positivity
      have h14 : 0 ≤ |δx| + |δy| := by positivity
      have h15 : |Δf|^2 ≤ (|δx| + |δy|)^2 := by
        nlinarith [h11, h13, h14]
      have h16 : |δx|^2 = δx^2 := by simp [sq_abs]
      have h17 : |δy|^2 = δy^2 := by simp [sq_abs]
      have h18 : (|δx| + |δy|)^2 ≤ 2 * (δx^2 + δy^2) := by
        nlinarith [sq_nonneg (|δx| - |δy|)]
      linarith [h12, h15, h18]
    have h_norm_map : ‖graphMap f x - graphMap f y‖^2 = δx^2 + δy^2 + Δf^2 := by
      rw [norm_sq_R3 (graphMap f x - graphMap f y)]
      <;> simp [graphMap, δx, δy, Δf]
      <;> ring
    have h_norm_v : ‖x - y‖^2 = δx^2 + δy^2 := by
      rw [norm_sq_R2 (x - y)]
      <;> simp [δx, δy]
      <;> ring
    have h_main2 : ‖graphMap f x - graphMap f y‖^2 ≤ 3 * ‖x - y‖^2 := by
      rw [h_norm_map, h_norm_v]
      nlinarith
    have h_nonneg1 : 0 ≤ ‖graphMap f x - graphMap f y‖ := by positivity
    have h_nonneg2 : 0 ≤ ‖x - y‖ := by positivity
    have h_sqrt : (Real.sqrt 3 * ‖x - y‖)^2 = 3 * ‖x - y‖^2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)] <;> ring
    have h_final2 : ‖graphMap f x - graphMap f y‖^2 ≤ (Real.sqrt 3 * ‖x - y‖)^2 := by
      rw [h_sqrt]; exact h_main2
    have h_sqrt_nonneg : 0 ≤ Real.sqrt 3 * ‖x - y‖ := by positivity
    have h_final : ‖graphMap f x - graphMap f y‖ ≤ Real.sqrt 3 * ‖x - y‖ := by
      nlinarith [h_final2, h_nonneg1, h_sqrt_nonneg]
    exact h_final
  let K : NNReal := ⟨Real.sqrt 3, Real.sqrt_nonneg 3⟩
  have h_lip : LipschitzOnWith K (graphMap f) V := by
    intro x hx y hy
    have h_norm : ‖graphMap f x - graphMap f y‖ ≤ (K : ℝ) * ‖x - y‖ := h_main x y hx hy
    have h_dist : dist (graphMap f x) (graphMap f y) ≤ (K : ℝ) * dist x y := by
      simpa [dist_eq_norm] using h_norm
    rw [edist_dist, edist_dist]
    have h_mul : (K : ENNReal) * ENNReal.ofReal (dist x y) = ENNReal.ofReal ((K : ℝ) * dist x y) := by
      have hK : (K : ENNReal) = ENNReal.ofReal (K : ℝ) := by simp
      calc
        (K : ENNReal) * ENNReal.ofReal (dist x y)
          = ENNReal.ofReal (K : ℝ) * ENNReal.ofReal (dist x y) := by rw [hK]
        _ = ENNReal.ofReal ((K : ℝ) * dist x y) := by
          exact (ENNReal.ofReal_mul K.prop).symm
    rw [h_mul]
    exact ENNReal.ofReal_le_ofReal h_dist
  exact h_lip

lemma graphMap_gen_lipschitz {U : Set R2} {f : R2 → ℝ} (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    {V : Set R2} (hV : Convex ℝ V) (hV_sub : V ⊆ U)
    (Cx Cy : ℝ) (hCx_nonneg : 0 ≤ Cx) (hCy_nonneg : 0 ≤ Cy)
    (hfx : ∀ y ∈ V, (fderiv ℝ f y e02)^2 ≤ Cx)
    (hfy : ∀ y ∈ V, (fderiv ℝ f y e12)^2 ≤ Cy) :
    LipschitzOnWith (⟨Real.sqrt (1 + Cx + Cy), Real.sqrt_nonneg _⟩ : NNReal) (graphMap f) V := by
  have h_pos : 0 ≤ 1 + Cx + Cy := by linarith
  have h_main : ∀ (x y : R2), x ∈ V → y ∈ V →
      ‖graphMap f x - graphMap f y‖ ≤ Real.sqrt (1 + Cx + Cy) * ‖x - y‖ := by
    intro x y hx hy
    rcases mvt_on_segment (V := V) hU hf hV hV_sub x y hx hy with ⟨ξ, hξV, h_mvt⟩
    let δx : ℝ := (x - y) 0
    let δy : ℝ := (x - y) 1
    let Δf : ℝ := f x - f y
    let c := fderiv ℝ f ξ e02
    let d := fderiv ℝ f ξ e12
    have h_Δf : Δf = c * δx + d * δy := by
      have h : fderiv ℝ f ξ (x - y) = c * δx + d * δy := fderiv_decomp f ξ (x - y)
      have h_eq : f x - f y = fderiv ℝ f ξ (x - y) := h_mvt
      have h9 : f x - f y = c * δx + d * δy := by rw [h_eq, h]
      exact h9
    have hc : c^2 ≤ Cx := hfx ξ hξV
    have hd : d^2 ≤ Cy := hfy ξ hξV
    have h_abs_c : |c| ≤ Real.sqrt Cx := by
      have h1 : |c|^2 ≤ Cx := by simpa [sq_abs] using hc
      nlinarith [Real.sqrt_nonneg Cx, Real.sq_sqrt hCx_nonneg, abs_nonneg c]
    have h_abs_d : |d| ≤ Real.sqrt Cy := by
      have h1 : |d|^2 ≤ Cy := by simpa [sq_abs] using hd
      nlinarith [Real.sqrt_nonneg Cy, Real.sq_sqrt hCy_nonneg, abs_nonneg d]
    have h_Δf_bound : |Δf| ≤ Real.sqrt Cx * |δx| + Real.sqrt Cy * |δy| := by
      rw [h_Δf]
      calc |c * δx + d * δy|
        ≤ |c * δx| + |d * δy| := by exact abs_add_le (c * δx) (d * δy)
      _ = |c| * |δx| + |d| * |δy| := by rw [abs_mul, abs_mul]
      _ ≤ Real.sqrt Cx * |δx| + Real.sqrt Cy * |δy| := by gcongr <;> linarith
    have h_cs : (Real.sqrt Cx * |δx| + Real.sqrt Cy * |δy|)^2 ≤ (Cx + Cy) * (δx^2 + δy^2) := by
      nlinarith [sq_nonneg (Real.sqrt Cx * |δy| - Real.sqrt Cy * |δx|),
        Real.sq_sqrt hCx_nonneg, Real.sq_sqrt hCy_nonneg, sq_abs δx, sq_abs δy]
    have h_Δf_sq : Δf^2 ≤ (Cx + Cy) * (δx^2 + δy^2) := by
      have h7 : Δf^2 = |Δf|^2 := by simp [sq_abs]
      rw [h7]
      have h8 : |Δf|^2 ≤ (Real.sqrt Cx * |δx| + Real.sqrt Cy * |δy|)^2 := by
        gcongr <;> exact h_Δf_bound
      linarith
    have h_norm_map : ‖graphMap f x - graphMap f y‖^2 = δx^2 + δy^2 + Δf^2 := by
      rw [norm_sq_R3 (graphMap f x - graphMap f y)]
      <;> simp [graphMap, δx, δy, Δf] <;> ring
    have h_norm_v : ‖x - y‖^2 = δx^2 + δy^2 := by
      rw [norm_sq_R2 (x - y)] <;> simp [δx, δy] <;> ring
    have h_main2 : ‖graphMap f x - graphMap f y‖^2 ≤ (1 + Cx + Cy) * ‖x - y‖^2 := by
      rw [h_norm_map, h_norm_v]; nlinarith
    have h_nonneg1 : 0 ≤ ‖graphMap f x - graphMap f y‖ := by positivity
    have h_nonneg2 : 0 ≤ Real.sqrt (1 + Cx + Cy) * ‖x - y‖ := by positivity
    have h_sqrt : (Real.sqrt (1 + Cx + Cy) * ‖x - y‖)^2 = (1 + Cx + Cy) * ‖x - y‖^2 := by
      rw [mul_pow, Real.sq_sqrt h_pos] <;> ring
    nlinarith
  let K : NNReal := ⟨Real.sqrt (1 + Cx + Cy), Real.sqrt_nonneg _⟩
  have h_lip : LipschitzOnWith K (graphMap f) V := by
    intro x hx y hy
    have h_norm : ‖graphMap f x - graphMap f y‖ ≤ (K : ℝ) * ‖x - y‖ := h_main x y hx hy
    have h_dist : dist (graphMap f x) (graphMap f y) ≤ (K : ℝ) * dist x y := by
      simpa [dist_eq_norm] using h_norm
    rw [edist_dist, edist_dist]
    have h_mul : (K : ENNReal) * ENNReal.ofReal (dist x y) = ENNReal.ofReal ((K : ℝ) * dist x y) := by
      have hK : (K : ENNReal) = ENNReal.ofReal (K : ℝ) := by simp
      rw [hK, ENNReal.ofReal_mul] <;> exact Real.sqrt_nonneg _
    rw [h_mul]
    exact ENNReal.ofReal_le_ofReal h_dist
  exact h_lip

end Kakeya.CV
