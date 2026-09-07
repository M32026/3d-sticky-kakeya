import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.Mollification
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterDefinition
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.MollificationGradientBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.RelativeIsoperimetric.SmoothSobolev
import Mathlib.Tactic


/-!
# Non-Sharp Isoperimetric Inequality via Mollification and Sobolev

Proves that for any measurable bounded set `S ⊆ ℝⁿ` with `n ≥ 2`:
`volume(S)^((n-1)/n) ≤ n · C(n) · perimeter(S)`

Proof route:
1. Use `mollification_gradient_bound` to get smooth u_k with
   `∫ ‖∇u_k‖ ≤ n · perimeter(S)` for large k.
2. Apply Sobolev inequality: `‖u_k‖_{n/(n-1)} ≤ C(n) · ‖∇u_k‖_1`.
3. u_k → χ_S in L¹, hence in measure, hence a.e. along a subsequence.
4. Dominated convergence gives `‖u_k‖_{L^p} → ‖χ_S‖_{L^p}`.
5. Conclude `volume(S)^((n-1)/n) ≤ n · C(n) · perimeter(S)`.

## References
- Maggi, Sets of Finite Perimeter, Theorem 12.1
- Evans-Gariepy, Measure Theory, Ch. 5
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory Convolution ContDiff Pointwise

namespace Geometry.Perimeter

variable {n : ℕ}

/-- **Non-sharp isoperimetric inequality** (perimeter form). -/
theorem non_sharp_isoperimetric_perimeter
    {n : ℕ} (hn : 2 ≤ n)
    {S : Set (E n)} (hS : MeasurableSet S) (hBdd : Bornology.IsBounded S) :
    (volume S)^((n - 1 : ℝ) / n) ≤
      (n : ENNReal) * ↑(MeasureTheory.eLpNormLESNormFDerivOneConst (E := E n) volume ((sobolevP n : ℝ))) * perimeter S := by
  haveI : Nonempty (Fin n) := by
    refine' ⟨⟨0, by omega⟩⟩
  let p : NNReal := sobolevP n
  have hp_pos : 0 < p := sobolevP_pos hn
  have hp : NNReal.HolderConjugate (Module.finrank ℝ (E n)) p := sobolevP_holderConjugate hn
  let C_S : ENNReal := ↑(MeasureTheory.eLpNormLESNormFDerivOneConst (E := E n) volume (p : ℝ))
  let χ : E n → ℝ := Set.indicator S (fun _ => (1 : ℝ))
  let C_val : ENNReal := (n : ENNReal) * C_S * perimeter S

  -- If volume S = 0, LHS = 0, trivial
  by_cases hvol0 : volume S = 0
  · rw [hvol0]
    have h_pos : 0 < ((n - 1 : ℝ) / n) := by
      have h1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n from by omega)
      have h2 : 0 < (n : ℝ) - 1 := by linarith
      have h3 : 0 < (n : ℝ) := by linarith
      exact div_pos h2 h3
    have h_zero : (0 : ENNReal) ^ ((n - 1 : ℝ) / n) = 0 :=
      ENNReal.zero_rpow_of_pos h_pos
    rw [h_zero] <;> simp

  -- Choose compact K containing S
  rcases hBdd.subset_closedBall 0 with ⟨R, hS_sub_ball⟩
  let K : Set (E n) := closedBall (0 : E n) (R + 1)
  have hK_compact : IsCompact K := isCompact_closedBall _ _
  have hK_closed : IsClosed K := isClosed_closedBall
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  have hS_sub_K : S ⊆ K := by
    intro x hx
    have h1 : dist x 0 ≤ R := hS_sub_ball hx
    have h2 : dist x 0 ≤ R + 1 := by linarith
    exact h2

  -- Mollification sequence with gradient bound
  obtain ⟨u, N, h_u_eq, h_u_smooth, h_u_bound, h_u_L1, h_grad_bound⟩ :=
    mollification_gradient_bound hS (isOpen_univ) hK_compact (by simp)

  -- Support of u_k is contained in K
  have h_u_support_K : ∀ k, Function.support (u k) ⊆ K := by
    intro k
    have h_eq : u k = Mollification.mollificationSeq hS k := congrFun h_u_eq k
    rw [h_eq]
    let ε : ℝ := 1 / (k + 2 : ℝ)
    have hε_pos : 0 < ε := by positivity
    have hε_le_one : ε ≤ 1 := by
      have h3 : (1 : ℝ) ≤ (k + 2 : ℝ) := by exact_mod_cast (by linarith)
      exact (div_le_one (by positivity)).mpr h3
    have h1 : Function.support (Mollification.mollificationSeq hS k) ⊆
        Function.support (Mollification.rho ε hε_pos) + Function.support χ :=
      MeasureTheory.support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)
    have h2 : Function.support (Mollification.rho ε hε_pos) ⊆ closedBall (0 : E n) ε := by
      have h21 : Function.support (Mollification.rho ε hε_pos) = Metric.ball (0 : E n) ε :=
        ContDiffBump.support_normed_eq (Mollification.mollifier ε hε_pos)
      rw [h21] <;> exact ball_subset_closedBall
    have h3 : Function.support χ ⊆ closure S := by
      intro x hx
      have hxS : x ∈ S := by simpa [χ, Function.mem_support, Set.indicator_apply] using hx
      exact subset_closure hxS
    have h4 : Function.support (Mollification.rho ε hε_pos) + Function.support χ ⊆
        closedBall (0 : E n) ε + closure S := Set.add_subset_add h2 h3
    have h5 : closedBall (0 : E n) ε + closure S ⊆ K := by
      intro z hz
      rcases hz with ⟨a, ha, b, hb, rfl⟩
      have h6 : dist a 0 ≤ ε := ha
      have h7 : b ∈ closure S := hb
      have h8 : dist b 0 ≤ R := by
        have h9 : closure S ⊆ closedBall (0 : E n) R := closure_minimal hS_sub_ball isClosed_closedBall
        exact h9 h7
      have h10 : dist (a + b) 0 ≤ dist a 0 + dist b 0 := by
        simpa [dist_eq_norm] using norm_add_le a b
      have h11 : dist (a + b) 0 ≤ R + 1 := by linarith
      exact h11
    exact h1.trans (h4.trans h5)

  -- u_k has compact support
  have h_u_compact_support : ∀ k, HasCompactSupport (u k) := by
    intro k
    have h_tsupport_sub : tsupport (u k) ⊆ K := closure_minimal (h_u_support_K k) hK_closed
    have h_tsupport_closed : IsClosed (tsupport (u k)) := isClosed_closure
    have h_tsupport_compact : IsCompact (tsupport (u k)) :=
      hK_compact.of_isClosed_subset h_tsupport_closed h_tsupport_sub
    exact h_tsupport_compact

  -- Derivative support also in K
  have h_deriv_support_K : ∀ k, Function.support (fderiv ℝ (u k)) ⊆ K := by
    intro k
    intro x hx
    by_contra h_notinK
    have hK_compl_open : IsOpen (Kᶜ) := hK_closed.isOpen_compl
    have h_zero_nhd : ∀ᶠ (y : E n) in nhds x, u k y = 0 := by
      filter_upwards [hK_compl_open.mem_nhds h_notinK] with y hy
      have h_y_notin_support : y ∉ Function.support (u k) := fun h => hy (h_u_support_K k h)
      simpa [Function.mem_support] using h_y_notin_support
    have h_fderiv_zero : fderiv ℝ (u k) x = 0 := by
      have h : HasFDerivAt (u k) (0 : (E n →L[ℝ] ℝ)) x :=
        hasFDerivAt_zero_of_eventually_const (0 : ℝ) h_zero_nhd
      exact h.fderiv
    have h_x_notin : x ∉ Function.support (fderiv ℝ (u k)) := by
      simpa [Function.mem_support, h_fderiv_zero] using h_fderiv_zero
    exact h_x_notin hx

  -- Global eLpNorm = restricted eLpNorm for derivative
  have h_deriv_norm_eq : ∀ k, eLpNorm (fderiv ℝ (u k)) (1 : NNReal) volume =
      eLpNorm (fderiv ℝ (u k)) (1 : NNReal) (volume.restrict K) := by
    intro k
    let g : E n → (E n →L[ℝ] ℝ) := fderiv ℝ (u k)
    have h_supp : Function.support g ⊆ K := h_deriv_support_K k
    have h_main : eLpNorm g (1 : ENNReal) (volume.restrict K) = eLpNorm g (1 : ENNReal) volume :=
      @MeasureTheory.eLpNorm_restrict_eq_of_support_subset
        (E n) _ (1 : ENNReal) volume (E n →L[ℝ] ℝ) _ _ K g h_supp
    simpa using h_main.symm

  -- perimeterIn S univ = perimeter S
  have h_perim_eq : perimeterIn S Set.univ = perimeter S := by
    dsimp only [perimeterIn, perimeter]
    apply le_antisymm
    · apply iSup_le
      intro Φ
      have h : perimeter S ≥ ENNReal.ofReal |∫ x in S, divergence Φ.val.toFun x| := by
        apply le_iSup_of_le (Φ.val) <;> rfl
      exact h
    · apply iSup_le
      intro φ
      let Φ : {Φ : TestVectorField // Function.support Φ.toFun ⊆ Set.univ} := ⟨φ, by simp⟩
      have h : perimeterIn S Set.univ ≥ ENNReal.ofReal |∫ x in S, divergence φ.toFun x| := by
        apply le_iSup_of_le Φ <;> rfl
      exact h

  -- Sobolev inequality for each u_k
  have h_sobolev : ∀ k, eLpNorm (u k) p volume ≤
      C_S * eLpNorm (fderiv ℝ (u k)) (1 : NNReal) volume := by
    intro k
    exact MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one volume
      (h_u_smooth k) (h_u_compact_support k) hp

  -- Gradient bound for k ≥ N
  have h_grad : ∀ k ≥ N, eLpNorm (fderiv ℝ (u k)) (1 : NNReal) volume ≤
      (n : ENNReal) * perimeter S := by
    intro k hk
    have h1 : eLpNorm (fderiv ℝ (u k)) (1 : NNReal) (volume.restrict K) ≤
        (n : ENNReal) * perimeter S := by
      have h2 := h_grad_bound k hk
      rw [h_perim_eq] at h2
      exact h2
    have h3 := h_deriv_norm_eq k
    rw [h3]
    exact h1

  -- Combined bound for k ≥ N
  have h_combined : ∀ k ≥ N, eLpNorm (u k) p volume ≤ C_val := by
    intro k hk
    calc
      eLpNorm (u k) p volume
        ≤ C_S * eLpNorm (fderiv ℝ (u k)) (1 : NNReal) volume := h_sobolev k
      _ ≤ C_S * ((n : ENNReal) * perimeter S) := mul_le_mul_left' (h_grad k hk) C_S
      _ = C_val := by ring

  -- p ≥ 1 (as real): from n⁻¹ + p⁻¹ = 1 and n ≥ 2
  have h_p_ge_one : 1 ≤ (p : ℝ) := by
    have h_finrank : Module.finrank ℝ (E n) = n := by simp
    have h_hc_iff := NNReal.holderConjugate_iff.mp hp
    have h_inv : ((Module.finrank ℝ (E n) : NNReal)⁻¹ : ℝ) + (p⁻¹ : ℝ) = 1 := by
      exact_mod_cast h_hc_iff.2
    have h_n_pos : 0 < (n : ℝ) := by positivity
    have h_p_pos : 0 < (p : ℝ) := by exact_mod_cast hp_pos
    have h1 : 1 / (p : ℝ) = 1 - 1 / (n : ℝ) := by
      have h2 : ((Module.finrank ℝ (E n) : NNReal)⁻¹ : ℝ) = 1 / (n : ℝ) := by
        rw [h_finrank]
        <;> simp [NNReal.coe_inv] <;> field_simp
      have h3 : ((Module.finrank ℝ (E n) : NNReal)⁻¹ : ℝ) + (p⁻¹ : ℝ) = 1 := h_inv
      rw [h2] at h3
      have h4 : (p⁻¹ : ℝ) = 1 - 1 / (n : ℝ) := by linarith
      simpa [NNReal.coe_inv] using h4
    have h3 : 1 / (p : ℝ) < 1 := by
      rw [h1]
      have h4 : 0 < 1 / (n : ℝ) := by positivity
      linarith
    have h4 : 1 < (p : ℝ) := by
      have h5 : 0 < (p : ℝ) := h_p_pos
      calc (1 : ℝ)
        = (1 / (p : ℝ)) * (p : ℝ) := by field_simp [h5.ne'] <;> ring
      _ < 1 * (p : ℝ) := by gcongr
      _ = (p : ℝ) := by ring
    linarith

  -- |u_k - χ| ≤ 1
  have h_diff_bound : ∀ k x, |u k x - χ x| ≤ 1 := by
    intro k x
    have h1 : 0 ≤ u k x ∧ u k x ≤ 1 := h_u_bound k x
    have h2 : 0 ≤ χ x ∧ χ x ≤ 1 := by
      by_cases h : x ∈ S <;> simp [χ, h] <;> norm_num
    have h3 : |u k x - χ x| ≤ 1 := by
      rw [abs_le] <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    exact h3

  -- f_k := u_k - χ is integrable
  have h_int : ∀ k, Integrable (u k - χ) volume := by
    intro k
    have h_int_uk : Integrable (u k) volume :=
      (h_u_smooth k).continuous.integrable_of_hasCompactSupport (h_u_compact_support k)
    have hS_fin_lt : volume S < ⊤ := by
      have h : volume S ≤ volume K := measure_mono hS_sub_K
      have h' : volume K < ⊤ := hK_compact.measure_lt_top
      exact h.trans_lt h'
    have h_int_χ : Integrable χ volume := by
      have h1 : IntegrableOn (fun (_ : E n) => (1 : ℝ)) S volume :=
        integrableOn_const (hs := hS_fin_lt.ne)
      have h2 : Integrable (Set.indicator S (fun (_ : E n) => (1 : ℝ))) volume :=
        (integrable_indicator_iff hS).mpr h1
      simpa [χ] using h2
    exact h_int_uk.sub h_int_χ

  -- support(u_k - χ) ⊆ K
  have h_f_supp_K : ∀ k, Function.support (u k - χ) ⊆ K := by
    intro k
    intro x hx
    by_cases h5 : x ∈ K
    · exact h5
    · have h6 : u k x = 0 := by
        have h7 : x ∉ Function.support (u k) := fun h8 => h5 (h_u_support_K k h8)
        simpa [Function.mem_support] using h7
      have h8 : χ x = 0 := by
        by_cases h9 : x ∈ S
        · exfalso; exact h5 (hS_sub_K h9)
        · simp [χ, h9]
      have h9 : (u k - χ) x = 0 := by simp [h6, h8]
      exfalso; exact hx (by simpa using h9)

  -- eLpNorm(f_k, 1) = ENNReal.ofReal(∫_K |f_k|)
  have h_eLp_one : ∀ k, eLpNorm (u k - χ) (1 : ENNReal) volume =
      ENNReal.ofReal (∫ x in K, |u k x - χ x|) := by
    intro k
    let f : E n → ℝ := u k - χ
    have h_supp : Function.support f ⊆ K := h_f_supp_K k
    have h_int_f : Integrable f volume := h_int k
    rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
    have h1 : ∫⁻ x, ‖f x‖ₑ = ENNReal.ofReal (∫ x, ‖f x‖) := by
      have h_eq : ∫ x, ‖f x‖ = (∫⁻ x, ‖f x‖ₑ).toReal :=
        MeasureTheory.integral_norm_eq_lintegral_enorm h_int_f.aestronglyMeasurable
      have h_fin : ∫⁻ x, ‖f x‖ₑ < ⊤ := h_int_f.hasFiniteIntegral
      have h : ENNReal.ofReal (∫ x, ‖f x‖) = ∫⁻ x, ‖f x‖ₑ := by
        rw [h_eq]
        rw [ENNReal.ofReal_toReal h_fin.ne]
      exact h.symm
    rw [h1]
    have h2 : ∫ x, ‖f x‖ = ∫ x in K, ‖f x‖ := by
      have h3 : ∀ x, ‖f x‖ = Set.indicator K (fun x => ‖f x‖) x := by
        intro x
        by_cases h4 : x ∈ K
        · simp [h4, Set.indicator_apply]
        · have h5 : f x = 0 := by
            have h6 : x ∉ Function.support f := fun h7 => h4 (h_supp h7)
            simpa [Function.mem_support] using h6
          simp [h4, h5, Set.indicator_apply]
      have h4 : ∫ x, ‖f x‖ = ∫ x, Set.indicator K (fun x => ‖f x‖) x := by
        congr with x
        exact h3 x
      have h5 : ∫ x, Set.indicator K (fun x => ‖f x‖) x = ∫ x in K, ‖f x‖ := by
        rw [integral_indicator hK_meas] <;> rfl
      rw [h4, h5]
    rw [h2]
    <;> simp [Real.norm_eq_abs, f]

  -- L1 convergence on K
  have h_L1_K : Filter.Tendsto (fun k => ∫ x in K, |u k x - χ x|) Filter.atTop (nhds 0) :=
    h_u_L1 K hK_compact

  -- eLpNorm(f_k, 1) → 0
  have h_eLp_one_tendsto : Filter.Tendsto (fun k => eLpNorm (u k - χ) (1 : ENNReal) volume)
      Filter.atTop (nhds 0) := by
    have h : (fun k => eLpNorm (u k - χ) (1 : ENNReal) volume) =
        fun k => ENNReal.ofReal (∫ x in K, |u k x - χ x|) := by
      funext k
      exact h_eLp_one k
    rw [h]
    have h_cont_ofReal : Continuous ENNReal.ofReal := ENNReal.continuous_ofReal
    have h : Filter.Tendsto (fun k => ENNReal.ofReal (∫ x in K, |u k x - χ x|)) Filter.atTop (nhds 0) := by
      have h' := (h_cont_ofReal.tendsto (0 : ℝ)).comp h_L1_K
      have h_zero : ENNReal.ofReal (0 : ℝ) = 0 := by simp
      rw [h_zero] at h'
      exact h'
    exact h

  -- Convergence in measure: u_k → χ
  have h_tim : TendstoInMeasure volume u atTop χ :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top
      (show (1 : ENNReal) ≠ 0 from by simp)
      (show (1 : ENNReal) ≠ ⊤ from by simp)
      (fun k => (h_u_smooth k).continuous.aestronglyMeasurable)
      ((measurable_const.indicator hS).aestronglyMeasurable)
      h_eLp_one_tendsto

  -- Extract a.e. convergent subsequence
  rcases h_tim.exists_seq_tendsto_ae with ⟨ns, hns_mono, h_ae⟩

  -- Helper: a ^ p ≤ a for a : ENNReal, a ≤ 1, p ≥ 1
  have h_enorm_pow_le : ∀ (a : ENNReal), a ≤ 1 → a ^ (p : ℝ) ≤ a := by
    intro a ha
    by_cases h0 : a = 0
    · subst h0
      have hp_pos' : 0 < (p : ℝ) := by exact_mod_cast hp_pos
      have h : (0 : ENNReal) ^ (p : ℝ) = 0 := ENNReal.zero_rpow_of_pos hp_pos'
      rw [h] <;> simp
    · have h1 : (1 : ℝ) ≤ (p : ℝ) := h_p_ge_one
      have h2 : a ^ (p : ℝ) ≤ a ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_ge ha h1
      have h3 : a ^ (1 : ℝ) = a := by simp
      rw [h3] at h2
      exact h2

  -- Dominated convergence: ∫⁻ ‖u_{ns j} - χ‖ₑ^p → 0
  let F : ℕ → E n → ENNReal := fun j x => ‖u (ns j) x - χ x‖ₑ ^ (p : ℝ)
  let bound : E n → ENNReal := Set.indicator K (fun _ => (1 : ENNReal))

  have h_bound_fin : ∫⁻ x, bound x ∂volume ≠ ⊤ := by
    have h : ∫⁻ x, bound x ∂volume = volume K := by
      simp [bound, lintegral_indicator hK_meas]
      <;> rfl
    rw [h]
    exact hK_compact.measure_lt_top.ne

  have h_pointwise : ∀ j x, F j x ≤ bound x := by
    intro j x
    by_cases hx : x ∈ K
    · -- x ∈ K: bound x = 1, and F j x ≤ ‖...‖ₑ ≤ 1
      have h1 : ‖u (ns j) x - χ x‖ₑ ≤ 1 := by
        have h2 : |u (ns j) x - χ x| ≤ 1 := h_diff_bound (ns j) x
        have h3 : ‖u (ns j) x - χ x‖ₑ = ENNReal.ofReal |u (ns j) x - χ x| := by
          rw [Real.enorm_eq_ofReal_abs]
        rw [h3]
        exact ENNReal.ofReal_le_one.mpr h2
      have h4 : F j x ≤ ‖u (ns j) x - χ x‖ₑ := h_enorm_pow_le (‖u (ns j) x - χ x‖ₑ) h1
      have h5 : bound x = 1 := by simp [bound, hx, Set.indicator_apply]
      rw [h5]
      exact le_trans h4 h1
    · -- x ∉ K: both F j x = 0 and bound x = 0
      have h6 : u (ns j) x = 0 := by
        have h7 : x ∉ Function.support (u (ns j)) := fun h8 => hx (h_u_support_K (ns j) h8)
        simpa [Function.mem_support] using h7
      have h7 : χ x = 0 := by
        by_cases h9 : x ∈ S
        · exfalso; exact hx (hS_sub_K h9)
        · simp [χ, h9]
      have h8 : (u (ns j) - χ) x = 0 := by simp [h6, h7]
      have h9 : F j x = 0 := by
        have h10 : u (ns j) x - χ x = 0 := by simpa using h8
        have h11 : ‖u (ns j) x - χ x‖ₑ = 0 := by rw [h10] <;> simp
        have hp_pos' : 0 < (p : ℝ) := by exact_mod_cast hp_pos
        have h12 : ‖u (ns j) x - χ x‖ₑ ^ (p : ℝ) = 0 := by
          rw [h11]
          exact ENNReal.zero_rpow_of_pos hp_pos'
        simpa [F] using h12
      have h10 : bound x = 0 := by simp [bound, hx, Set.indicator_apply]
      rw [h9, h10]

  have h_meas : ∀ j, Measurable (F j) := by
    intro j
    have h1 : Measurable (u (ns j)) := (h_u_smooth (ns j)).continuous.measurable
    have h2 : Measurable χ := (measurable_const.indicator hS)
    have h3 : Measurable (u (ns j) - χ) := h1.sub h2
    have h4 : Measurable (fun x => ‖(u (ns j) - χ) x‖ₑ) := h3.enorm
    have h5 : Continuous (fun y : ENNReal => y ^ (p : ℝ)) := by fun_prop
    exact h5.measurable.comp h4

  have h_lim : ∀ᵐ x ∂volume, Filter.Tendsto (fun j => F j x) Filter.atTop (nhds 0) := by
    filter_upwards [h_ae] with x hx_conv
    have h_const : Filter.Tendsto (fun (_ : ℕ) => χ x) Filter.atTop (nhds (χ x)) := tendsto_const_nhds
    have h1 : Filter.Tendsto (fun j => u (ns j) x - χ x) Filter.atTop (nhds 0) := by
      have h_sub := hx_conv.sub h_const
      simpa using h_sub
    have h2 : Filter.Tendsto (fun j => ‖u (ns j) x - χ x‖ₑ) Filter.atTop (nhds 0) := by
      have h_enorm : Filter.Tendsto (fun j => ‖u (ns j) x - χ x‖ₑ) Filter.atTop (nhds ‖(0 : ℝ)‖ₑ) := h1.enorm
      have h_zero : ‖(0 : ℝ)‖ₑ = 0 := by simp
      rw [h_zero] at h_enorm
      exact h_enorm
    have hp_pos' : 0 < (p : ℝ) := by exact_mod_cast hp_pos
    have h_cont_rpow : Continuous (fun y : ENNReal => y ^ (p : ℝ)) := by fun_prop
    have h3 : Filter.Tendsto (fun j => ‖u (ns j) x - χ x‖ₑ ^ (p : ℝ)) Filter.atTop (nhds 0) := by
      have h4 := Filter.Tendsto.comp (h_cont_rpow.tendsto (0 : ENNReal)) h2
      have h5 : (0 : ENNReal) ^ (p : ℝ) = 0 := ENNReal.zero_rpow_of_pos hp_pos'
      rw [h5] at h4
      exact h4
    exact h3

  have h_dc : Filter.Tendsto (fun j => ∫⁻ x, F j x ∂volume) Filter.atTop (nhds 0) := by
    have h_dc' : Filter.Tendsto (fun j => ∫⁻ x, F j x ∂volume) Filter.atTop (nhds (∫⁻ x, (0 : ENNReal) ∂volume)) :=
      MeasureTheory.tendsto_lintegral_of_dominated_convergence bound h_meas
        (fun j => by filter_upwards with x; exact h_pointwise j x) h_bound_fin h_lim
    have h_zero_int : ∫⁻ (x : E n), (0 : ENNReal) ∂volume = 0 := by
      exact lintegral_zero
    rw [h_zero_int] at h_dc'
    exact h_dc'

  -- eLpNorm(u_{ns j} - χ, p) → 0
  have h_Lp_diff : Filter.Tendsto (fun j => eLpNorm (u (ns j) - χ) p volume)
      Filter.atTop (nhds 0) := by
    have h_eq1 : ∀ j, eLpNorm (u (ns j) - χ) p volume ^ (p : ℝ) = ∫⁻ x, F j x ∂volume := by
      intro j
      exact MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral hp_pos.ne'
    have h_pow_tendsto : Filter.Tendsto
        (fun j => eLpNorm (u (ns j) - χ) p volume ^ (p : ℝ)) Filter.atTop (nhds 0) := by
      rw [funext h_eq1]
      exact h_dc
    have hp_pos' : 0 < (p : ℝ) := by exact_mod_cast hp_pos
    have h_cont : Continuous fun x : ENNReal => x ^ (1 / (p : ℝ)) := by
      fun_prop
    have h_main : Filter.Tendsto (fun j => (eLpNorm (u (ns j) - χ) p volume ^ (p : ℝ)) ^ (1 / (p : ℝ)))
        Filter.atTop (nhds 0) := by
      have h6 : (0 : ENNReal) ^ (1 / (p : ℝ)) = 0 := ENNReal.zero_rpow_of_pos (by positivity)
      have h7 := Filter.Tendsto.comp (h_cont.tendsto (0 : ENNReal)) h_pow_tendsto
      rw [h6] at h7
      have h8 : ((fun x : ENNReal => x ^ (1 / (p : ℝ))) ∘ fun j => eLpNorm (u (ns j) - χ) p volume ^ (p : ℝ)) =
          fun j => (eLpNorm (u (ns j) - χ) p volume ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
        funext j
        rfl
      rw [h8] at h7
      exact h7
    have h_id : ∀ j, (eLpNorm (u (ns j) - χ) p volume ^ (p : ℝ)) ^ (1 / (p : ℝ)) =
        eLpNorm (u (ns j) - χ) p volume := by
      intro j
      have h_rpow_rpow : ∀ (x : ENNReal), (x ^ (p : ℝ)) ^ (1 / (p : ℝ)) = x := by
        intro x
        by_cases h_top : x = ⊤
        · rw [h_top]
          simp [hp_pos'.ne']
        · by_cases h_zero : x = 0
          · rw [h_zero]
            simp [hp_pos'.ne']
          · have h_mul : (p : ℝ) * (1 / (p : ℝ)) = 1 := by
              field_simp [hp_pos'.ne'] <;> ring
            have h_rpow : x ^ ((p : ℝ) * (1 / (p : ℝ))) = (x ^ (p : ℝ)) ^ (1 / (p : ℝ)) :=
              ENNReal.rpow_mul x (p : ℝ) (1 / (p : ℝ))
            rw [h_mul] at h_rpow
            simpa using h_rpow.symm
      exact h_rpow_rpow _
    have h_final : Filter.Tendsto (fun j => eLpNorm (u (ns j) - χ) p volume)
        Filter.atTop (nhds 0) := by
      have h9 : (fun j => (eLpNorm (u (ns j) - χ) p volume ^ (p : ℝ)) ^ (1 / (p : ℝ))) =
          fun j => eLpNorm (u (ns j) - χ) p volume := by
        funext j
        exact h_id j
      rw [h9] at h_main
      exact h_main
    exact h_final

  -- Triangle inequality: eLpNorm χ p ≤ eLpNorm(u_{ns j} - χ, p) + eLpNorm(u_{ns j}, p)
  -- And eLpNorm(u_{ns j}, p) ≤ C_val for large j
  -- Hence eLpNorm χ p ≤ eLpNorm(u_{ns j} - χ, p) + C_val for large j
  -- Taking limit: eLpNorm χ p ≤ C_val
  have h_final : eLpNorm χ p volume ≤ C_val := by
    have h1 : ∀ j, eLpNorm χ p volume ≤
        eLpNorm (χ - u (ns j)) p volume + eLpNorm (u (ns j)) p volume := by
      intro j
      have h_eq : (χ - u (ns j)) + u (ns j) = χ := by funext x; simp
      have hp1 : (1 : ENNReal) ≤ (p : ENNReal) := by exact_mod_cast h_p_ge_one
      have hcf : AEStronglyMeasurable (χ - u (ns j)) volume :=
        (measurable_const.indicator hS).aestronglyMeasurable.sub
          (h_u_smooth (ns j)).continuous.aestronglyMeasurable
      have hcg : AEStronglyMeasurable (u (ns j)) volume :=
        (h_u_smooth (ns j)).continuous.aestronglyMeasurable
      have h : eLpNorm ((χ - u (ns j)) + u (ns j)) p volume ≤
          eLpNorm (χ - u (ns j)) p volume + eLpNorm (u (ns j)) p volume :=
        eLpNorm_add_le hcf hcg hp1
      rw [h_eq] at h
      exact h
    have h2 : ∀ j, eLpNorm (χ - u (ns j)) p volume = eLpNorm (u (ns j) - χ) p volume := by
      intro j
      have h_neg : (χ - u (ns j)) = -(u (ns j) - χ) := by
        funext x
        simp [sub_eq_add_neg]
        <;> abel
      rw [h_neg]
      exact MeasureTheory.eLpNorm_neg (u (ns j) - χ) p volume
    have h3 : ∀ j, eLpNorm χ p volume ≤
        eLpNorm (u (ns j) - χ) p volume + eLpNorm (u (ns j)) p volume := by
      intro j
      have h1j := h1 j
      rw [h2 j] at h1j
      exact h1j
    have h4 : ∀ᶠ j in Filter.atTop, eLpNorm χ p volume ≤
        eLpNorm (u (ns j) - χ) p volume + C_val := by
      have h5 : ∀ᶠ j in Filter.atTop, ns j ≥ N := hns_mono.tendsto_atTop.eventually_ge_atTop N
      filter_upwards [h5] with j hj
      have h6 : eLpNorm (u (ns j)) p volume ≤ C_val := h_combined (ns j) hj
      have h7 : eLpNorm χ p volume ≤
          eLpNorm (u (ns j) - χ) p volume + eLpNorm (u (ns j)) p volume := h3 j
      exact le_trans h7 (add_le_add_right h6 _)
    have h_sum_tendsto : Filter.Tendsto
        (fun j => eLpNorm (u (ns j) - χ) p volume + C_val)
        Filter.atTop (nhds (0 + C_val)) := h_Lp_diff.add tendsto_const_nhds
    have h_zero_add : (0 + C_val) = C_val := by simp
    rw [h_zero_add] at h_sum_tendsto
    exact ge_of_tendsto h_sum_tendsto h4

  -- Compute eLpNorm χ p = (volume S)^(1/p)
  have h_norm_χ : eLpNorm χ p volume = (volume S)^(1 / (p : ℝ)) := by
    have h1 : eLpNorm χ p volume =
        (∫⁻ x, ‖χ x‖ₑ ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
      rw [MeasureTheory.eLpNorm_nnreal_eq_lintegral hp_pos.ne'] <;> rfl
    rw [h1]
    have hp_pos' : 0 < (p : ℝ) := by exact_mod_cast hp_pos
    have h2 : ∀ᵐ x ∂volume, ‖χ x‖ₑ ^ (p : ℝ) = Set.indicator S (fun _ => (1 : ENNReal)) x := by
      filter_upwards with x
      by_cases h : x ∈ S
      · have h9 : χ x = 1 := by simp [χ, h]
        rw [h9]
        have h10 : ‖(1 : ℝ)‖ₑ = 1 := by simp
        rw [h10]
        have h11 : (1 : ENNReal) ^ (p : ℝ) = 1 := by simp
        rw [h11]
        <;> simp [Set.indicator_apply, h]
      · have h9 : χ x = 0 := by simp [χ, h]
        rw [h9]
        have h10 : ‖(0 : ℝ)‖ₑ = 0 := by simp
        rw [h10]
        have h11 : (0 : ENNReal) ^ (p : ℝ) = 0 := ENNReal.zero_rpow_of_pos hp_pos'
        rw [h11]
        <;> simp [Set.indicator_apply, h]
    have h3 : ∫⁻ x, ‖χ x‖ₑ ^ (p : ℝ) = volume S := by
      rw [lintegral_congr_ae h2]
      <;> simp [χ, lintegral_indicator hS]
    rw [h3] <;> rfl

  -- Exponent: 1/p = (n-1)/n
  have h_exp : 1 / (p : ℝ) = (n - 1 : ℝ) / n := by
    have h_finrank : Module.finrank ℝ (E n) = n := by simp
    have h_inv_nnreal2 : (Module.finrank ℝ (E n) : NNReal)⁻¹ + p⁻¹ = 1 :=
      NNReal.HolderConjugate.inv_add_inv_eq_one hp
    have h_inv2 : 1 / (Module.finrank ℝ (E n) : ℝ) + 1 / (p : ℝ) = 1 := by
      simpa [NNReal.coe_inv, NNReal.coe_add, NNReal.coe_one] using congr_arg (fun x : NNReal => (x : ℝ)) h_inv_nnreal2
    have h1 : 1 / (p : ℝ) = 1 - 1 / (n : ℝ) := by
      rw [h_finrank] at h_inv2
      linarith
    rw [h1]
    have h5 : (n : ℝ) ≠ 0 := by positivity
    field_simp [h5] <;> ring

  rw [h_norm_χ, h_exp] at h_final
  exact h_final

end Geometry.Perimeter
