import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.RelativeIsoperimetric.Cutoff
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.Mollification
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterDefinition
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.OneDDuality
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.GradientHelpers
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Tactic


/-!
# Mollification Gradient Bound — Fixed Version

Proves that for `u_k = χ_S * ρ_{1/k}`, any compact `K ⊂⊂ Ω`, and large `k`:
- `∫_K |∂_{e_i} u_k| ≤ perimeterIn S Ω` (coordinate-wise)
- `∫_K ‖∇u_k‖ ≤ n * perimeterIn S Ω` (full gradient)

## Proof outline

For each coordinate i:
1. Cutoff η=1 on K, supp η⊆Ω
2. Apply oneD_duality_exists to f=η·∂_i u_k
3. Let ψ=η·φ (supp ψ fixed compact in Ω)
4. IBP: ∫∂_i u_k·ψ = -∫u_k·∂_i ψ
5. Convolution adjoint + derivative commute: ∫u_k·∂_i ψ = ∫_S ∂_i(ψ⋆ρ_k)
6. For large k: supp(ψ⋆ρ_k)⊆Ω, |ψ⋆ρ_k|≤1 → test field bound ≤ perimeterIn
7. Duality → ∫_K |∂_i u_k| ≤ perimeterIn S Ω
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory Convolution ContDiff Topology

namespace Geometry.Perimeter

variable {n : ℕ} [Nonempty (Fin n)]

abbrev Euc n := EuclideanSpace ℝ (Fin n)

-- ============================================================================
-- 1D L¹-L∞ duality with support constraint
-- ============================================================================

/-- For continuous compactly supported `f` and open `Ω ⊃ supp f`,
for any `ε > 0`, there exists smooth compactly supported `φ` in `Ω` with
`|φ| ≤ 1` and `∫ f · φ ≥ ∫ |f| - ε`. -/
lemma oneD_duality_exists
    {f : E n → ℝ} (hf_cont : Continuous f) (hf_support : HasCompactSupport f)
    {Ω : Set (E n)} (hΩ_open : IsOpen Ω) (h_tsupport_sub : tsupport f ⊆ Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (φ : E n → ℝ), ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      Function.support φ ⊆ Ω ∧ (∀ x, |φ x| ≤ 1) ∧
      ∫ x, f x * φ x ≥ (∫ x, |f x|) - ε := by
  have hK : IsCompact (tsupport f) := hf_support
  rcases exists_smooth_cutoff hK hΩ_open h_tsupport_sub with
    ⟨η, hη_smooth, hη_compact, hη_one, hη_support, hη_bounds⟩
  rcases smooth_approximate_sign hf_cont hf_support hε with
    ⟨ψ, hψ_smooth, hψ_compact, hψ_bound, hψ_int⟩
  let φ : E n → ℝ := fun x => η x * ψ x
  have hφ_smooth : ContDiff ℝ ∞ φ := hη_smooth.mul hψ_smooth
  have hφ_compact : HasCompactSupport φ := by
    have h1 : Function.support φ ⊆ Function.support η := by
      intro x hx
      have h2 : η x ≠ 0 := by
        by_contra h3
        have h4 : φ x = 0 := by simp [φ, h3]
        exact hx h4
      simpa [Function.mem_support] using h2
    exact hη_compact.mono h1
  have hφ_support : Function.support φ ⊆ Ω := by
    intro x hx
    have h10 : η x ≠ 0 := by
      by_contra h11
      have h12 : φ x = 0 := by simp [φ, h11]
      exact hx h12
    exact hη_support (subset_closure h10)
  have hφ_bound : ∀ x, |φ x| ≤ 1 := by
    intro x
    have h1 : |φ x| = |η x| * |ψ x| := by simp [φ, abs_mul] <;> ring
    rw [h1]
    have h2 : |η x| ≤ 1 := by
      have h3 : 0 ≤ η x ∧ η x ≤ 1 := hη_bounds x
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have h4 : |ψ x| ≤ 1 := hψ_bound x
    calc |η x| * |ψ x| ≤ 1 * |ψ x| := by gcongr
      _ ≤ 1 := by linarith
  have h_eq : ∫ x, f x * φ x = ∫ x, f x * ψ x := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport f
    · have hη1 : η x = 1 := hη_one x hx
      simp [φ, hη1]
    · have hf0 : f x = 0 := by
        have h : x ∉ Function.support f := fun h' => hx (subset_closure h')
        simpa [Function.mem_support] using h
      simp [φ, hf0]
  refine' ⟨φ, hφ_smooth, hφ_compact, hφ_support, hφ_bound, _⟩
  rw [h_eq]
  exact hψ_int


/-- A C¹ function with compact support has bounded derivative, hence is Lipschitz. -/
lemma contDiff1_hasCompactSupport_lipschitz
    {F : E n → ℝ} (hF : ContDiff ℝ 1 F) (hF_support : HasCompactSupport F) :
    ∃ (C : NNReal), LipschitzWith C F := by
  let K := tsupport F
  have hK : IsCompact K := hF_support
  have h_fd_cont : Continuous (fun x => ‖fderiv ℝ F x‖) :=
    (hF.continuous_fderiv (by norm_num)).norm
  have h_bdd : BddAbove (Set.image (fun x => ‖fderiv ℝ F x‖) K) :=
    hK.bddAbove_image h_fd_cont.continuousOn
  let C : ℝ := sSup (Set.image (fun x => ‖fderiv ℝ F x‖) K)
  have hC_nonneg : 0 ≤ C := by
    by_cases h : K = ∅
    · simp [h, C]
    · rcases Set.nonempty_iff_ne_empty.mpr h with ⟨x, hx⟩
      have h0 : 0 ≤ ‖fderiv ℝ F x‖ := by positivity
      have h1 : ‖fderiv ℝ F x‖ ∈ Set.image (fun x => ‖fderiv ℝ F x‖) K := ⟨x, hx, rfl⟩
      have h2 : ‖fderiv ℝ F x‖ ≤ C := le_csSup h_bdd h1
      linarith
  have h1 : ∀ x ∈ K, ‖fderiv ℝ F x‖ ≤ C := by
    intro x hx
    exact le_csSup h_bdd ⟨x, hx, rfl⟩
  have h2 : ∀ x, ‖fderiv ℝ F x‖ ≤ C := by
    intro x
    by_cases hx : x ∈ K
    · exact h1 x hx
    · have h3 : ∀ᶠ y in nhds x, F y = 0 := by
        have h4 : IsOpen Kᶜ := hF_support.isClosed.isOpen_compl
        have h5 : Kᶜ ∈ nhds x := h4.mem_nhds hx
        filter_upwards [h5] with y hy
        have h6 : y ∉ Function.support F := by intro h7; exact hy (subset_closure h7)
        simpa [Function.mem_support] using h6
      have h5 : fderiv ℝ F x = 0 := by
        have h6 : Filter.EventuallyEq (nhds x) F (fun _ => (0 : ℝ)) := h3
        have h7 : fderiv ℝ F x = fderiv ℝ (fun _ => (0 : ℝ)) x := h6.fderiv_eq
        rw [h7]; simp
      rw [h5] <;> simp [hC_nonneg]
  have h_diff : Differentiable ℝ F := hF.differentiable (by norm_num)
  let C' : NNReal := ⟨C, hC_nonneg⟩
  have h_bound' : ∀ x, ‖fderiv ℝ F x‖₊ ≤ C' := by
    intro x
    exact NNReal.coe_le_coe.mp (h2 x)
  have h_lip : LipschitzWith C' F := lipschitzWith_of_nnnorm_fderiv_le h_diff h_bound'
  exact ⟨C', h_lip⟩

-- ============================================================================
-- Helper 2: Integral of partial derivative of compactly supported smooth F = 0
-- ============================================================================

/-- For a C¹ compactly supported function F, ∫ ∂_i F = 0. -/
lemma integral_partial_compact_support
    {F : E n → ℝ} (hF : ContDiff ℝ 1 F) (hF_support : HasCompactSupport F)
    (i : Fin n) :
    ∫ x, fderiv ℝ F x (EuclideanSpace.single i 1) = 0 := by
  have h_lip := contDiff1_hasCompactSupport_lipschitz hF hF_support
  let C := h_lip.choose
  have hF_lip : LipschitzWith C F := h_lip.choose_spec
  let e_i : E n := EuclideanSpace.single i 1
  have h_main : ∫ x : E n,
      lineDeriv ℝ (fun (_ : E n) => (1 : ℝ)) x e_i * F x =
      ∫ x : E n, lineDeriv ℝ F x (-e_i) * (1 : ℝ) :=
    LipschitzWith.integral_lineDeriv_mul_eq
      (LipschitzWith.const (1 : ℝ)) hF_lip hF_support e_i
  have h1 : ∀ x : E n, lineDeriv ℝ (fun (_ : E n) => (1 : ℝ)) x e_i = 0 := by
    intro x
    simpa [lineDeriv] using hasDerivAt_const (x : E n) (1 : ℝ)
  have h2 : ∀ x : E n, lineDeriv ℝ F x (-e_i) = -fderiv ℝ F x e_i := by
    intro x
    have h_diff_at : DifferentiableAt ℝ F x := (hF.differentiable (by norm_num)).differentiableAt
    have h3 : lineDeriv ℝ F x (-e_i) = fderiv ℝ F x (-e_i) :=
      h_diff_at.lineDeriv_eq_fderiv
    rw [h3]
    have h4 : fderiv ℝ F x (-e_i) = -fderiv ℝ F x e_i := by
      rw [map_neg] <;> rfl
    rw [h4]
  have h_lhs : ∫ x : E n, lineDeriv ℝ (fun (_ : E n) => (1 : ℝ)) x e_i * F x = 0 := by
    have h4 : (fun x : E n => lineDeriv ℝ (fun (_ : E n) => (1 : ℝ)) x e_i * F x) = fun _ => 0 := by
      funext x; rw [h1 x]; ring
    rw [h4]; simp
  have h_rhs : ∫ x : E n, lineDeriv ℝ F x (-e_i) * (1 : ℝ) = -∫ x : E n, fderiv ℝ F x e_i := by
    have h4 : ∫ x : E n, lineDeriv ℝ F x (-e_i) * (1 : ℝ) = ∫ x : E n, -fderiv ℝ F x e_i := by
      apply integral_congr_ae
      filter_upwards with x
      rw [h2 x] <;> ring
    rw [h4]
    rw [integral_neg]
  have h_eq : (0 : ℝ) = -∫ x : E n, fderiv ℝ F x e_i := by
    rw [←h_lhs, h_main, h_rhs]
  linarith

-- ============================================================================
-- Helper 3: Integration by parts
-- ============================================================================

/-- Integration by parts: ∫ ∂_i u · ψ = -∫ u · ∂_i ψ when ψ has compact support. -/
lemma integration_by_parts_compact
    {u ψ : E n → ℝ} (hu : ContDiff ℝ 1 u) (hψ : ContDiff ℝ 1 ψ)
    (hψ_support : HasCompactSupport ψ) (i : Fin n) :
    ∫ x, (fderiv ℝ u x (EuclideanSpace.single i 1)) * ψ x =
    -∫ x, u x * (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
  let F : E n → ℝ := fun x => u x * ψ x
  have hF : ContDiff ℝ 1 F := hu.mul hψ
  have hF_support : HasCompactSupport F := hψ_support.mul_left
  have h_deriv : ∀ x, fderiv ℝ F x (EuclideanSpace.single i 1) =
      (fderiv ℝ u x (EuclideanSpace.single i 1)) * ψ x +
      u x * (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    intro x
    have h1 : HasFDerivAt u (fderiv ℝ u x) x :=
      (hu.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt ψ (fderiv ℝ ψ x) x :=
      (hψ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have h3_raw : HasFDerivAt F (u x • fderiv ℝ ψ x + ψ x • fderiv ℝ u x) x := h1.mul h2
    have h_eq : (u x • fderiv ℝ ψ x + ψ x • fderiv ℝ u x) =
        (fderiv ℝ u x).smulRight (ψ x) + (u x) • (fderiv ℝ ψ x) := by
      ext z
      simp [LinearMap.smulRight_apply, LinearMap.smul_apply] <;> ring
    have h3 : HasFDerivAt F ((fderiv ℝ u x).smulRight (ψ x) + (u x) • (fderiv ℝ ψ x)) x := by
      convert h3_raw using 1
      exact h_eq.symm
    have h4 : fderiv ℝ F x = (fderiv ℝ u x).smulRight (ψ x) + (u x) • (fderiv ℝ ψ x) :=
      h3.fderiv
    rw [h4]
    <;> simp [LinearMap.smulRight_apply, LinearMap.smul_apply] <;> ring
  have h_int : ∫ x, fderiv ℝ F x (EuclideanSpace.single i 1) = 0 :=
    integral_partial_compact_support hF hF_support i
  have h5 : ∫ x, ((fderiv ℝ u x (EuclideanSpace.single i 1)) * ψ x +
      u x * (fderiv ℝ ψ x (EuclideanSpace.single i 1))) = 0 := by
    have h_eq : ∫ x, ((fderiv ℝ u x (EuclideanSpace.single i 1)) * ψ x +
        u x * (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
        ∫ x, fderiv ℝ F x (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      filter_upwards with x
      exact (h_deriv x).symm
    rw [h_eq]
    exact h_int
  have h6 : Integrable (fun x : E n => (fderiv ℝ u x (EuclideanSpace.single i 1)) * ψ x) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · have h_cont1 : Continuous (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) := by fun_prop
      exact h_cont1.mul hψ.continuous
    · exact hψ_support.mul_left
  have h7 : Integrable (fun x : E n => u x * (fderiv ℝ ψ x (EuclideanSpace.single i 1))) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · have h_cont2 : Continuous (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by fun_prop
      exact hu.continuous.mul h_cont2
    · have h_supp2 : HasCompactSupport (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)) :=
        hψ_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
      exact h_supp2.mul_left
  rw [integral_add h6 h7] at h5
  linarith

-- ============================================================================
-- Helper: Norm bound of convolution
-- ============================================================================

/-- |(ρ ⋆ h)(x)| ≤ 1 when ρ ≥ 0, ∫ρ = 1, |h| ≤ 1. -/
lemma norm_convolution_bound
    {ρ : E n → ℝ} (hρ_nonneg : ∀ x, 0 ≤ ρ x)
    (hρ_int : ∫ x, ρ x = 1) (hρ_support : HasCompactSupport ρ)
    (hρ_cont : Continuous ρ)
    {h : E n → ℝ} (hh_cont : Continuous h) (hh_bound : ∀ x, |h x| ≤ 1) :
    ∀ (x : E n), |convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x| ≤ 1 := by
  intro x
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hρ_int' : Integrable ρ volume := hρ_cont.integrable_of_hasCompactSupport hρ_support
  have h_exists : ConvolutionExists ρ h L volume :=
    hρ_support.convolutionExists_left_of_continuous_right L hρ_cont.locallyIntegrable hh_cont
  have h_int : Integrable (fun t : E n => ρ t * h (x - t)) volume := (h_exists x).integrable
  have h1 : |convolution ρ h L volume x| ≤ ∫ t : E n, ρ t * |h (x - t)| := by
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
    have h_abs : |∫ t : E n, ρ t * h (x - t)| ≤ ∫ t : E n, |ρ t * h (x - t)| :=
      abs_integral_le_integral_abs
    have h_eq : ∫ t : E n, |ρ t * h (x - t)| = ∫ t : E n, ρ t * |h (x - t)| := by
      apply integral_congr_ae
      filter_upwards with t
      have h2 : |ρ t * h (x - t)| = ρ t * |h (x - t)| := by
        rw [abs_mul]
        have h3 : |ρ t| = ρ t := abs_of_nonneg (hρ_nonneg t)
        rw [h3] <;> ring
      exact h2
    rw [h_eq] at h_abs
    exact h_abs
  have h2 : ∫ t : E n, ρ t * |h (x - t)| ≤ ∫ t : E n, ρ t := by
    have h_int2 : Integrable (fun t : E n => ρ t * |h (x - t)|) volume := by
      have h_support : Function.support (fun t : E n => ρ t * |h (x - t)|) ⊆ Function.support ρ := by
        intro t ht
        by_contra h3
        have h4 : ρ t = 0 := by simpa [Function.mem_support] using h3
        have h5 : ρ t * |h (x - t)| = 0 := by rw [h4]; ring
        exact ht h5
      have h_compact : HasCompactSupport (fun t : E n => ρ t * |h (x - t)|) :=
        hρ_support.mono h_support
      have h_cont : Continuous (fun t : E n => ρ t * |h (x - t)|) := by fun_prop
      exact h_cont.integrable_of_hasCompactSupport h_compact
    apply integral_mono h_int2 hρ_int'
    intro t
    have h3 : |h (x - t)| ≤ 1 := hh_bound (x - t)
    have h4 : 0 ≤ ρ t := hρ_nonneg t
    exact mul_le_of_le_one_right h4 h3
  calc |convolution ρ h L volume x|
    ≤ ∫ t : E n, ρ t * |h (x - t)| := h1
    _ ≤ ∫ t : E n, ρ t := h2
    _ = 1 := by rw [hρ_int] <;> norm_num

-- ============================================================================
-- Main Theorem 1: Coordinate-wise gradient bound
-- ============================================================================

/-- **Mollification gradient bound** (coordinate-wise).

For the canonical mollification sequence `u_k`, `∫_K |∂_i u_k| ≤ P(S; Ω)` for large `k`. -/
lemma mollification_partial_deriv_bound
    {S : Set (E n)} (hS : MeasurableSet S)
    {Ω : Set (E n)} (hΩ_open : IsOpen Ω)
    {K : Set (E n)} (hK_compact : IsCompact K) (hK_sub : K ⊆ Ω)
    (i : Fin n) :
    ∃ (N : ℕ),
      ∀ k ≥ N, eLpNorm (fun y => fderiv ℝ (Mollification.mollificationSeq hS k) y (EuclideanSpace.single i 1))
        (1 : NNReal) (volume.restrict K) ≤ perimeterIn S Ω := by
  let χ : E n → ℝ := Set.indicator S (fun _ => (1 : ℝ))
  let u : ℕ → E n → ℝ := fun k => Mollification.mollificationSeq hS k
  have h_u_smooth : ∀ k, ContDiff ℝ ∞ (u k) := by
    intro k
    exact Mollification.mollify_contDiff hS _ _
  have h_u_bound : ∀ k x, 0 ≤ u k x ∧ u k x ≤ 1 := by
    intro k
    exact Mollification.mollify_bound hS _ _
  have h_u_l1 : ∀ (L : Set (E n)), IsCompact L →
      Filter.Tendsto (fun k => ∫ x in L, |u k x - χ x|) Filter.atTop (nhds 0) := by
    intro L hL
    exact Mollification.mollify_tendsto_L1 hS hL
  -- Get cutoff η = 1 on K, supported in Ω
  rcases exists_smooth_cutoff hK_compact hΩ_open hK_sub with
    ⟨η, hη_smooth, hη_support, hη_one, hη_support_sub, hη_bounds⟩
  let D : Set (E n) := tsupport η
  have hD_compact : IsCompact D := hη_support.isCompact
  have hD_sub : D ⊆ Ω := hη_support_sub
  -- Distance from D to Ωᶜ > 0
  have h_dist_pos : ∃ (δ : ℝ), 0 < δ ∧ Metric.thickening δ D ⊆ Ω :=
    hD_compact.exists_thickening_subset_open hΩ_open hD_sub
  rcases h_dist_pos with ⟨δ, hδ_pos, hδ_thickening⟩
  -- Choose N such that 1/(k+2) < δ for all k ≥ N
  have h_tendsto_r : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (k + 2 : ℝ)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun k : ℕ => (k : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have h2 : Filter.Tendsto (fun k : ℕ => (k : ℝ) + 2) Filter.atTop Filter.atTop :=
      tendsto_atTop_mono (fun n => by linarith) h1
    have h3 : Filter.Tendsto (fun k : ℕ => ((k : ℝ) + 2)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp h2
    have h4 : (fun k : ℕ => (1 : ℝ) / (k + 2 : ℝ)) = fun k : ℕ => ((k : ℝ) + 2)⁻¹ := by
      funext k
      field_simp
    rw [h4]
    exact h3
  have h_exists_N : ∃ (N : ℕ), ∀ k ≥ N, (1 : ℝ) / (k + 2 : ℝ) < δ := by
    have h2 : ∀ᶠ (k : ℕ) in Filter.atTop, (1 : ℝ) / (k + 2 : ℝ) < δ :=
      h_tendsto_r (Iio_mem_nhds hδ_pos)
    exact Filter.eventually_atTop.mp h2
  rcases h_exists_N with ⟨N, hN⟩
  -- For k ≥ N, prove the bound
  have h_main : ∀ k ≥ N, eLpNorm (fun y => fderiv ℝ (u k) y (EuclideanSpace.single i 1))
      (1 : NNReal) (volume.restrict K) ≤ perimeterIn S Ω := by
    intro k hk
    set ε_k : ℝ := 1 / (k + 2 : ℝ) with hε_k_def
    have hε_k_pos : 0 < ε_k := by positivity
    have hε_k_ltδ : ε_k < δ := hN k hk
    let ρ_k : E n → ℝ := Mollification.rho ε_k hε_k_pos
    have hρ_smooth : ContDiff ℝ ∞ ρ_k := by
      exact (Mollification.mollifier ε_k hε_k_pos).contDiff_normed
    have hρ_support : HasCompactSupport ρ_k :=
      (Mollification.mollifier ε_k hε_k_pos).hasCompactSupport_normed
    have hρ_nonneg : ∀ x, 0 ≤ ρ_k x :=
      (Mollification.mollifier ε_k hε_k_pos).nonneg_normed
    have hρ_int : ∫ x, ρ_k x = 1 :=
      (Mollification.mollifier ε_k hε_k_pos).integral_normed
    have hρ_even : ∀ x, ρ_k (-x) = ρ_k x := mollifier_even ε_k hε_k_pos
    have hρ_cont : Continuous ρ_k := hρ_smooth.continuous
    have h_u_conv : u k = convolution ρ_k χ (ContinuousLinearMap.lsmul ℝ ℝ) volume := by rfl
    -- Case split on perimeterIn
    by_cases hP_top : perimeterIn S Ω = ⊤
    · rw [hP_top] <;> exact le_top
    · have hP_ne_top : perimeterIn S Ω ≠ ⊤ := hP_top
      have hP_lt_top : perimeterIn S Ω < ⊤ := lt_top_iff_ne_top.mpr hP_ne_top
      let P : ℝ := (perimeterIn S Ω).toReal
      have hP_nonneg : 0 ≤ P := by positivity
      -- Let f := η · ∂_i(u k)
      let f : E n → ℝ := fun x => η x * fderiv ℝ (u k) x (EuclideanSpace.single i 1)
      have h_fd_cont : Continuous (fun x => fderiv ℝ (u k) x (EuclideanSpace.single i 1)) := by
        have h1 : Continuous (fderiv ℝ (u k)) := (h_u_smooth k).continuous_fderiv (by norm_num)
        have h2 : Continuous (fun (L : E n →L[ℝ] ℝ) => L (EuclideanSpace.single i 1)) := by
          let eval_at_v : (E n →L[ℝ] ℝ) →L[ℝ] ℝ :=
            { toFun := fun L => L (EuclideanSpace.single i 1)
              map_add' := fun L1 L2 => rfl
              map_smul' := fun c L => rfl }
          exact eval_at_v.continuous
        exact h2.comp h1
      have hf_cont : Continuous f := hη_smooth.continuous.mul h_fd_cont
      have hf_support : HasCompactSupport f := by
        have h : Function.support f ⊆ Function.support η := by
          intro x hx
          have h2 : η x ≠ 0 := by
            by_contra h3
            have h4 : f x = 0 := by simp [f, h3]
            exact hx h4
          simpa [Function.mem_support] using h2
        exact hη_support.mono h

      have hf_sub : Function.support f ⊆ Ω := by
        intro x hx
        have h1 : η x ≠ 0 := by
          by_contra h2
          have h3 : f x = 0 := by simp [f, h2]
          exact hx h3
        have h4 : x ∈ Function.support η := by simpa [Function.mem_support] using h1
        have h5 : x ∈ D := subset_closure h4
        exact hD_sub h5
      have hf_tsupport_sub : tsupport f ⊆ Ω := by
        have h1 : Function.support f ⊆ Function.support η := by
          intro x hx
          have h2 : η x ≠ 0 := by
            by_contra h3
            have h4 : f x = 0 := by simp [f, h3]
            exact hx h4
          simpa [Function.mem_support] using h2
        have h2 : tsupport f ⊆ tsupport η := closure_mono h1
        exact h2.trans hD_sub
      -- We want ∫ |f| ≤ P
      have h_bound : ∫ x, |f x| ≤ P := by
        by_contra h_contra
        have h_strict : P < ∫ x, |f x| := by exact lt_of_not_ge h_contra
        have h_pos : 0 < (∫ x, |f x|) - P := sub_pos.mpr h_strict
        set ε' : ℝ := ((∫ x, |f x|) - P) / 2 with hε'_def
        have hε'_pos : 0 < ε' := by
          dsimp only [ε']
          exact div_pos h_pos (by norm_num)
        -- Apply duality
        rcases oneD_duality_exists hf_cont hf_support hΩ_open hf_tsupport_sub hε'_pos
          with ⟨φ, hφ_smooth, hφ_support, hφ_sub, hφ_bound, hφ_int⟩
        -- Let ψ := η · φ
        let ψ : E n → ℝ := fun x => η x * φ x
        have hη_smooth1 : ContDiff ℝ 1 η := hη_smooth.of_le (by norm_num)
        have hφ_smooth1 : ContDiff ℝ 1 φ := hφ_smooth.of_le (by norm_num)
        have hψ_smooth : ContDiff ℝ 1 ψ := hη_smooth1.mul hφ_smooth1
        have hψ_support : HasCompactSupport ψ := by
          have h1 : Function.support ψ ⊆ Function.support η := by
            intro x hx
            have h2 : η x ≠ 0 := by
              by_contra h3
              have h4 : ψ x = 0 := by simp [ψ, h3]
              exact hx h4
            simpa [Function.mem_support] using h2
          exact hη_support.mono h1
        have hψ_sub : Function.support ψ ⊆ D := by
          intro x hx
          have h1 : η x ≠ 0 := by
            by_contra h2
            have h3 : ψ x = 0 := by simp [ψ, h2]
            exact hx h3
          have h4 : x ∈ Function.support η := by simpa [Function.mem_support] using h1
          exact subset_closure h4
        have hψ_bound : ∀ x, |ψ x| ≤ 1 := by
          intro x
          have h1 : |ψ x| = |η x| * |φ x| := by simp [ψ, abs_mul] <;> ring
          rw [h1]
          have h2 : |η x| ≤ 1 := by
            have h3 : 0 ≤ η x ∧ η x ≤ 1 := hη_bounds x
            exact abs_le.mpr ⟨by linarith, by linarith⟩
          have h4 : |φ x| ≤ 1 := hφ_bound x
          have h_nonneg2 : 0 ≤ |φ x| := abs_nonneg _
          have h5 : |η x| * |φ x| ≤ 1 * |φ x| := mul_le_mul_of_nonneg_right h2 h_nonneg2
          have h6 : 1 * |φ x| ≤ 1 := by
            simpa using h4
          linarith
        -- ∫ f · φ = ∫ ∂_i u_k · ψ
        have h_eq1 : ∫ x, f x * φ x = ∫ x, (fderiv ℝ (u k) x (EuclideanSpace.single i 1)) * ψ x := by
          apply integral_congr_ae
          filter_upwards with x
          simp [f, ψ] <;> ring
        -- IBP
        have h_ibp : ∫ x, (fderiv ℝ (u k) x (EuclideanSpace.single i 1)) * ψ x =
            -∫ x, (u k) x * (fderiv ℝ ψ x (EuclideanSpace.single i 1)) :=
          integration_by_parts_compact ((h_u_smooth k).of_le (by norm_num)) hψ_smooth hψ_support i
        -- Convolution adjoint
        let h_diff : E n → ℝ := fun y => fderiv ℝ ψ y (EuclideanSpace.single i 1)
        have hχ_meas : Measurable χ := measurable_const.indicator hS
        have hχ_bdd : ∀ x, |χ x| ≤ 1 := by
          intro x
          by_cases h : x ∈ S <;> simp [χ, h] <;> norm_num
        have hh_diff_cont : Continuous h_diff := by
          have h : Continuous (fderiv ℝ ψ) := hψ_smooth.continuous_fderiv (by norm_num)
          have h_eval : Continuous (fun (L : E n →L[ℝ] ℝ) => L (EuclideanSpace.single i 1)) := by
            let eval_at_v : (E n →L[ℝ] ℝ) →L[ℝ] ℝ :=
              { toFun := fun L => L (EuclideanSpace.single i 1)
                map_add' := fun L1 L2 => rfl
                map_smul' := fun c L => rfl }
            exact eval_at_v.continuous
          exact h_eval.comp h
        have hh_diff_support : HasCompactSupport h_diff :=
          hψ_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
        have h_adj : ∫ x, (u k) x * h_diff x =
            ∫ y, χ y * (convolution ρ_k h_diff (ContinuousLinearMap.lsmul ℝ ℝ) volume y) := by
          rw [h_u_conv]
          exact convolution_adjoint_symm hρ_cont hρ_support hρ_even hχ_meas hχ_bdd hh_diff_cont hh_diff_support
        -- Derivative commute
        let Φ_k : E n → ℝ := convolution ρ_k ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume
        have h_deriv_comm : ∀ y, convolution ρ_k h_diff (ContinuousLinearMap.lsmul ℝ ℝ) volume y =
            fderiv ℝ Φ_k y (EuclideanSpace.single i 1) := by
          intro y
          exact (convolution_deriv_commute hρ_smooth hρ_support hψ_smooth hψ_support i y).symm
        have h_adj2 : ∫ y, χ y * (convolution ρ_k h_diff (ContinuousLinearMap.lsmul ℝ ℝ) volume y) =
            ∫ y, χ y * (fderiv ℝ Φ_k y (EuclideanSpace.single i 1)) := by
          apply integral_congr_ae
          filter_upwards with y
          rw [h_deriv_comm y]
        -- So ∫ u_k · ∂_i ψ = ∫ χ · ∂_i Φ_k
        have h_final_conv : ∫ x, (u k) x * h_diff x =
            ∫ y, χ y * (fderiv ℝ Φ_k y (EuclideanSpace.single i 1)) := by
          rw [h_adj, h_adj2]
        -- Support Φ_k ⊆ Ω
        have h_support_Phi : Function.support Φ_k ⊆ Ω := by
          have h1 : Function.support Φ_k ⊆ Set.image2 (· + ·) (Function.support ρ_k) (Function.support ψ) :=
            support_convolution_bound hρ_support hψ_support
          have h2 : Function.support ρ_k ⊆ Metric.ball (0 : E n) ε_k := by
            have h_eq : Function.support ρ_k = Metric.ball (0 : E n) ε_k :=
              (Mollification.mollifier ε_k hε_k_pos).support_normed_eq
            rw [h_eq]
          have h3 : Set.image2 (· + ·) (Function.support ρ_k) (Function.support ψ) ⊆
              Set.image2 (· + ·) (Metric.ball (0 : E n) ε_k) D := by
            apply Set.image2_subset
            · exact h2
            · exact hψ_sub
          have h4 : Set.image2 (· + ·) (Metric.ball (0 : E n) ε_k) D = Metric.thickening ε_k D := by
            ext x
            simp only [Set.mem_add, Metric.mem_thickening_iff]
            constructor
            · rintro ⟨z, hz, d, hd, rfl⟩
              exact ⟨d, hd, by simpa [dist_eq_norm] using hz⟩
            · rintro ⟨d, hd, hdist⟩
              refine ⟨x - d, ?_, d, hd, by abel_nf⟩
              simpa [dist_eq_norm, sub_self] using hdist
          rw [h4] at h3
          have h5 : Metric.thickening ε_k D ⊆ Metric.thickening δ D :=
            Metric.thickening_mono hε_k_ltδ.le D
          exact h1.trans (h3.trans (h5.trans hδ_thickening))
        -- Norm bound Φ_k
        have h_norm_Phi : ∀ x, |Φ_k x| ≤ 1 :=
          norm_convolution_bound hρ_nonneg hρ_int hρ_support hρ_cont hψ_smooth.continuous hψ_bound
        -- Construct test vector field
        let Ψ_fun : E n → E n := fun x => EuclideanSpace.single i (Φ_k x)
        have hΦ_smooth : ContDiff ℝ ∞ Φ_k :=
          hρ_support.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
            hρ_smooth hψ_smooth.continuous.locallyIntegrable
        let single_i_lm : ℝ →ₗ[ℝ] E n :=
          { toFun := EuclideanSpace.single i
            map_add' := fun a b => by
              ext j
              simp [EuclideanSpace.single_apply]
              <;> split_ifs <;> simp [add_comm] <;> ring
            map_smul' := fun c a => by
              ext j
              simp [EuclideanSpace.single_apply, smul_eq_mul]
              <;> split_ifs <;> ring }
        let single_i : ℝ →L[ℝ] E n :=
          single_i_lm.mkContinuous 1 (by
            intro x
            simp [single_i_lm, EuclideanSpace.norm_single]
            <;> exact le_refl _)
        have h_eq : Ψ_fun = single_i ∘ Φ_k := by
          funext x
          rfl
        have hΨ_smooth : ContDiff ℝ ∞ Ψ_fun := by
          rw [h_eq]
          exact single_i.contDiff.comp hΦ_smooth
        have hΨ_compact : HasCompactSupport Ψ_fun := by
          have h1 : Function.support Ψ_fun ⊆ Function.support Φ_k := by
            intro x hx
            have h2 : Ψ_fun x ≠ 0 := hx
            have h3 : Φ_k x ≠ 0 := by
              by_contra h4
              have h5 : Ψ_fun x = 0 := by simp [Ψ_fun, h4]
              exact h2 h5
            simpa [Function.mem_support] using h3
          exact hρ_support.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hψ_support |>.mono h1
        have hΨ_bound : ∀ x, ‖Ψ_fun x‖ ≤ 1 := by
          intro x
          simpa [Ψ_fun, EuclideanSpace.norm_single] using h_norm_Phi x
        have hΨ_support_sub : Function.support Ψ_fun ⊆ Ω := by
          have h1 : Function.support Ψ_fun ⊆ Function.support Φ_k := by
            intro x hx
            have h2 : Ψ_fun x ≠ 0 := hx
            have h3 : Φ_k x ≠ 0 := by
              by_contra h4
              have h5 : Ψ_fun x = 0 := by simp [Ψ_fun, h4]
              exact h2 h5
            simpa [Function.mem_support] using h3
          exact h1.trans h_support_Phi
        have h_div : divergence Ψ_fun = fun x => fderiv ℝ Φ_k x (EuclideanSpace.single i 1) := by
          funext x
          have h1 : ∀ (j : Fin n), fderiv ℝ (fun y : E n => Ψ_fun y j) x (EuclideanSpace.single j 1) =
              if j = i then fderiv ℝ Φ_k x (EuclideanSpace.single i 1) else 0 := by
            intro j
            by_cases hji : j = i
            · have h_eq1 : (fun y : E n => Ψ_fun y j) = Φ_k := by
                funext y
                simp [Ψ_fun, EuclideanSpace.single_apply, hji]
                <;> aesop
              rw [h_eq1]
              have h_goal : fderiv ℝ Φ_k x (EuclideanSpace.single j 1) = fderiv ℝ Φ_k x (EuclideanSpace.single i 1) := by
                rw [hji]
              rw [h_goal, if_pos hji]
            · have h_eq2 : (fun y : E n => Ψ_fun y j) = fun (_ : E n) => (0 : ℝ) := by
                funext y
                simp [Ψ_fun, EuclideanSpace.single_apply, hji]
                <;> aesop
              rw [h_eq2]
              simp [hji]
          have h2 : ∑ j : Fin n, (if j = i then fderiv ℝ Φ_k x (EuclideanSpace.single i 1) else 0) =
              fderiv ℝ Φ_k x (EuclideanSpace.single i 1) := by
            rw [Finset.sum_ite_eq'] <;> simp
          have h3 : ∑ j : Fin n, fderiv ℝ (fun y : E n => Ψ_fun y j) x (EuclideanSpace.single j 1) =
              ∑ j : Fin n, (if j = i then fderiv ℝ Φ_k x (EuclideanSpace.single i 1) else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            exact h1 j
          have h_sum : ∑ j : Fin n, fderiv ℝ (fun y : E n => Ψ_fun y j) x (EuclideanSpace.single j 1) =
              fderiv ℝ Φ_k x (EuclideanSpace.single i 1) := by
            rw [h3, h2]
          simpa [divergence] using h_sum
        let Ψ : TestVectorField := ⟨Ψ_fun, hΨ_smooth, hΨ_compact, hΨ_bound⟩
        let Ψ' : {Φ : TestVectorField // Function.support Φ.toFun ⊆ Ω} := ⟨Ψ, hΨ_support_sub⟩
        have h_perim_bound : ENNReal.ofReal |∫ x in S, divergence Ψ_fun x| ≤ perimeterIn S Ω :=
          le_iSup (fun (Φ : {Φ : TestVectorField // Function.support Φ.toFun ⊆ Ω}) =>
            ENNReal.ofReal |∫ x in S, divergence Φ.val.toFun x|) Ψ'
        have h_int_S : ∫ y, χ y * (fderiv ℝ Φ_k y (EuclideanSpace.single i 1)) =
            ∫ x in S, fderiv ℝ Φ_k x (EuclideanSpace.single i 1) := by
          let g := fun y : E n => fderiv ℝ Φ_k y (EuclideanSpace.single i 1)
          have h_eq1 : (fun y => χ y * g y) = Set.indicator S g := by
            funext y
            by_cases hy : y ∈ S
            · simp [χ, Set.indicator_apply, hy]
            · simp [χ, Set.indicator_apply, hy]
          rw [h_eq1, integral_indicator hS] <;> rfl
        have h_div_int : ∫ x in S, divergence Ψ_fun x = ∫ x in S, fderiv ℝ Φ_k x (EuclideanSpace.single i 1) := by
          congr with x
        have h6 : |∫ x in S, fderiv ℝ Φ_k x (EuclideanSpace.single i 1)| ≤ P := by
          have h7 : ENNReal.ofReal |∫ x in S, fderiv ℝ Φ_k x (EuclideanSpace.single i 1)| ≤ perimeterIn S Ω := by
            rw [←h_div_int]
            exact h_perim_bound
          have hP_eq : perimeterIn S Ω = ENNReal.ofReal P := by
            rw [ENNReal.ofReal_toReal hP_lt_top.ne]
          rw [hP_eq] at h7
          have h_abs_nonneg : 0 ≤ |∫ x in S, fderiv ℝ Φ_k x (EuclideanSpace.single i 1)| := by positivity
          exact (ENNReal.ofReal_le_ofReal_iff hP_nonneg).mp h7
        -- Combine
        have h9 : ∫ x, f x * φ x = -∫ y, χ y * (fderiv ℝ Φ_k y (EuclideanSpace.single i 1)) := by
          rw [h_eq1, h_ibp, h_final_conv] <;> ring
        have h10 : -(∫ x in S, fderiv ℝ Φ_k x (EuclideanSpace.single i 1)) ≥ (∫ x, |f x|) - ε' := by
          have h101 : ∫ x, f x * φ x ≥ (∫ x, |f x|) - ε' := hφ_int
          rw [h9, h_int_S] at h101
          exact h101
        have h_neg_abs : -(∫ x in S, fderiv ℝ Φ_k x (EuclideanSpace.single i 1)) ≤ |∫ x in S, fderiv ℝ Φ_k x (EuclideanSpace.single i 1)| := neg_le_abs _
        have h11 : ∫ x, |f x| ≤ |∫ x in S, fderiv ℝ Φ_k x (EuclideanSpace.single i 1)| + ε' := by linarith [h10, h_neg_abs]
        have h12 : ∫ x, |f x| ≤ P + ε' := by
          calc ∫ x, |f x| ≤ |∫ x in S, fderiv ℝ Φ_k x (EuclideanSpace.single i 1)| + ε' := h11
            _ ≤ P + ε' := by linarith [h6]
        have h13 : ε' = ((∫ x, |f x|) - P) / 2 := by rfl
        rw [h13] at h12
        linarith
      -- Convert ∫_K |∂_i u_k| ≤ ∫ |f|
      have h_f_integrable : Integrable f volume :=
        hf_cont.integrable_of_hasCompactSupport hf_support
      have h_abs_integrable : Integrable (fun x => |f x|) volume := by
        have h1 : Integrable (fun x => ‖f x‖) volume := h_f_integrable.norm
        have h2 : (fun x : E n => ‖f x‖) = (fun x : E n => |f x|) := by
          funext x
          exact Real.norm_eq_abs (f x)
        rw [h2] at h1
        exact h1
      have hK_meas : MeasurableSet K := hK_compact.measurableSet
      have h14 : ∫ x in K, |fderiv ℝ (u k) x (EuclideanSpace.single i 1)| ≤ ∫ x, |f x| := by
        have h15 : ∀ x ∈ K, |fderiv ℝ (u k) x (EuclideanSpace.single i 1)| = |f x| := by
          intro x hx
          have h16 : η x = 1 := hη_one x hx
          simp [f, h16] <;> ring
        have h17 : ∫ x in K, |fderiv ℝ (u k) x (EuclideanSpace.single i 1)| = ∫ x in K, |f x| := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [self_mem_ae_restrict hK_meas] with x hx
          exact h15 x hx
        rw [h17]
        have h_nonneg : ∀ x, 0 ≤ |f x| := fun x => abs_nonneg _
        have h_ind : ∀ x, Set.indicator K (fun x => |f x|) x ≤ |f x| := by
          intro x
          by_cases hx : x ∈ K
          · simp [Set.indicator_apply, hx]
          · simp [Set.indicator_apply, hx] <;> positivity
        have h_int_ind : Integrable (Set.indicator K (fun x => |f x|)) volume :=
          h_abs_integrable.indicator hK_meas
        have h_ae : ∀ᵐ x ∂volume, Set.indicator K (fun x => |f x|) x ≤ |f x| := by
          filter_upwards with x
          exact h_ind x
        have h : ∫ x, Set.indicator K (fun x => |f x|) x ≤ ∫ x, |f x| :=
          integral_mono_ae h_int_ind h_abs_integrable h_ae
        have h_eq : ∫ x, Set.indicator K (fun x => |f x|) x = ∫ x in K, |f x| := by
          rw [integral_indicator hK_meas] <;> rfl
        rw [h_eq] at h
        exact h
      have h18 : ∫ x in K, |fderiv ℝ (u k) x (EuclideanSpace.single i 1)| ≤ P :=
        h14.trans h_bound
      -- eLpNorm conversion
      have h_deriv_cont : Continuous (fun y : E n => fderiv ℝ (u k) y (EuclideanSpace.single i 1)) := by fun_prop
      have h_deriv_locInt : MeasureTheory.LocallyIntegrable (fun y : E n => fderiv ℝ (u k) y (EuclideanSpace.single i 1)) volume :=
        h_deriv_cont.locallyIntegrable
      have h_deriv_int_on := h_deriv_locInt.integrableOn_isCompact hK_compact
      let g := fun y : E n => fderiv ℝ (u k) y (EuclideanSpace.single i 1)
      have h_deriv_int : Integrable g (volume.restrict K) := by
        unfold Integrable
        exact h_deriv_int_on
      have h_eLpNorm : eLpNorm g (1 : NNReal) (volume.restrict K) =
          ENNReal.ofReal (∫ x in K, |g x|) := by
        have h1 : eLpNorm g (1 : NNReal) (volume.restrict K) =
            ∫⁻ x, ‖g x‖ₑ ∂(volume.restrict K) := by
          have h_eq : eLpNorm g (1 : NNReal) (volume.restrict K) = eLpNorm g (1 : ENNReal) (volume.restrict K) := by
            congr <;> norm_cast
          rw [h_eq]
          exact MeasureTheory.eLpNorm_one_eq_lintegral_enorm
        rw [h1]
        have h2 : ∫⁻ x, ‖g x‖ₑ ∂(volume.restrict K) =
            ENNReal.ofReal (∫ x in K, |g x|) := by
          have h4 : ENNReal.ofReal (∫ x, ‖g x‖ ∂(volume.restrict K)) =
              ∫⁻ x, ‖g x‖ₑ ∂(volume.restrict K) :=
            ofReal_integral_norm_eq_lintegral_enorm h_deriv_int_on
          rw [←h4]
          have h5 : ∫ x, ‖g x‖ ∂(volume.restrict K) = ∫ x in K, |g x| := by
            apply integral_congr_ae
            filter_upwards with x
            exact Real.norm_eq_abs (g x)
          rw [h5]
        exact h2
      rw [h_eLpNorm]
      have h19 : 0 ≤ ∫ x in K, |fderiv ℝ (u k) x (EuclideanSpace.single i 1)| := by positivity
      have hP_eq : perimeterIn S Ω = ENNReal.ofReal P := by
        rw [ENNReal.ofReal_toReal hP_lt_top.ne]
      rw [hP_eq]
      exact ENNReal.ofReal_le_ofReal h18
  exact ⟨N, h_main⟩

-- ============================================================================
-- Main Theorem 2: Full gradient bound
-- ============================================================================

/-- **Full mollification gradient bound.**

For the canonical mollification sequence `u_k`,
`∫_K ‖∇u_k‖ ≤ n * P(S; Ω)` for large `k`. -/
lemma mollification_gradient_bound
    {S : Set (E n)} (hS : MeasurableSet S)
    {Ω : Set (E n)} (hΩ_open : IsOpen Ω)
    {K : Set (E n)} (hK_compact : IsCompact K) (hK_sub : K ⊆ Ω) :
    ∃ (u : ℕ → E n → ℝ) (N : ℕ),
      (u = fun k => Mollification.mollificationSeq hS k) ∧
      (∀ k, ContDiff ℝ 1 (u k)) ∧
      (∀ k x, 0 ≤ u k x ∧ u k x ≤ 1) ∧
      (∀ (L : Set (E n)), IsCompact L →
        Filter.Tendsto (fun k => ∫ x in L, |u k x - Set.indicator S (fun _ => (1 : ℝ)) x|)
          Filter.atTop (nhds 0)) ∧
      ∀ k ≥ N, eLpNorm (fderiv ℝ (u k)) (1 : NNReal) (volume.restrict K) ≤
        (n : ENNReal) * perimeterIn S Ω := by
  let u : ℕ → E n → ℝ := fun k => Mollification.mollificationSeq hS k
  have h_u_smooth : ∀ k, ContDiff ℝ 1 (u k) := by
    intro k
    have h₂ := Mollification.mollify_contDiff hS (1 / (k + 2 : ℝ)) (by positivity)
    exact h₂.of_le (by norm_num)
  have h_u_bound : ∀ k x, 0 ≤ u k x ∧ u k x ≤ 1 := by
    intro k
    exact Mollification.mollify_bound hS (1 / (k + 2 : ℝ)) (by positivity)
  have h_u_l1 : ∀ (L : Set (E n)), IsCompact L →
      Filter.Tendsto (fun k => ∫ x in L, |u k x - Set.indicator S (fun _ => (1 : ℝ)) x|)
        Filter.atTop (nhds 0) := by
    intro L hL
    exact Mollification.mollify_tendsto_L1 hS hL
  -- For each i, get N_i
  have h_all : ∀ (i : Fin n), ∃ (N : ℕ), ∀ k ≥ N,
      eLpNorm (fun y => fderiv ℝ (u k) y (EuclideanSpace.single i 1))
        (1 : NNReal) (volume.restrict K) ≤ perimeterIn S Ω :=
    fun i => mollification_partial_deriv_bound hS hΩ_open hK_compact hK_sub i
  choose N hN using h_all
  let N_max : ℕ := Finset.univ.sup N
  have hN_max : ∀ (i : Fin n), N i ≤ N_max := by
    intro i
    exact Finset.le_sup (Finset.mem_univ i)
  have h_grad_all : ∀ (i : Fin n) (k : ℕ), k ≥ N_max →
      eLpNorm (fun y => fderiv ℝ (u k) y (EuclideanSpace.single i 1))
        (1 : NNReal) (volume.restrict K) ≤ perimeterIn S Ω := by
    intro i k hk
    have h1 : k ≥ N i := le_trans (hN_max i) hk
    exact hN i k h1
  -- Norm bound: ‖fderiv u x‖ ≤ ∑ i, |fderiv u x (e_i)|
  have h_main : ∀ k ≥ N_max,
      eLpNorm (fderiv ℝ (u k)) (1 : NNReal) (volume.restrict K) ≤
        (n : ENNReal) * perimeterIn S Ω := by
    intro k hk
    have h1 : ∀ x, ‖fderiv ℝ (u k) x‖ ≤ ∑ i : Fin n, |fderiv ℝ (u k) x (EuclideanSpace.single i 1)| := by
      intro x
      let l : (E n →L[ℝ] ℝ) := fderiv ℝ (u k) x
      have h_coord : ∀ (y : E n), |l y| ≤ (∑ i : Fin n, |l (EuclideanSpace.single i 1)|) * ‖y‖ := by
        intro y
        have h_y : y = ∑ i : Fin n, y i • EuclideanSpace.single i 1 := by
          let b := EuclideanSpace.basisFun (Fin n) ℝ
          have h1 : ∑ i : Fin n, b.repr y i • b i = y := b.sum_repr y
          have h2 : ∑ i : Fin n, b.repr y i • b i = ∑ i : Fin n, y i • EuclideanSpace.single i (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            have h3 : b.repr y i = y i := by simp [b]
            have h4 : b i = EuclideanSpace.single i (1 : ℝ) := by simp [b]
            rw [h3, h4]
          rw [h2] at h1
          exact h1.symm

        have h_expand : l y = ∑ i : Fin n, y i * l (EuclideanSpace.single i 1) := by
          have h1 : l y = l (∑ i : Fin n, y i • EuclideanSpace.single i 1) :=
            congr_arg l h_y
          rw [h1]
          have h_sum : l (∑ i : Fin n, y i • EuclideanSpace.single i 1) = ∑ i : Fin n, l (y i • EuclideanSpace.single i 1) := by
            have h : ∀ (s : Finset (Fin n)), l (∑ i ∈ s, y i • EuclideanSpace.single i 1) = ∑ i ∈ s, l (y i • EuclideanSpace.single i 1) := by
              intro s
              induction s using Finset.induction with
              | empty => simp
              | @insert a s ha ih =>
                rw [Finset.sum_insert ha, Finset.sum_insert ha, l.map_add, ih]
            exact h Finset.univ
          rw [h_sum]
          let coeff : Fin n → ℝ := fun i => y i
          have h_sum2 : ∑ i : Fin n, l (coeff i • EuclideanSpace.single i 1) = ∑ i : Fin n, coeff i * l (EuclideanSpace.single i 1) := by
            apply Finset.sum_congr rfl
            intro i _
            exact l.map_smul (coeff i) (EuclideanSpace.single i 1)
          exact h_sum2
        rw [h_expand]
        have h_abs : |∑ i : Fin n, y i * l (EuclideanSpace.single i 1)| ≤ ∑ i : Fin n, |y i * l (EuclideanSpace.single i 1)| :=
          Finset.abs_sum_le_sum_abs _ _
        have h_each : ∀ i ∈ Finset.univ, |y i * l (EuclideanSpace.single i 1)| ≤ ‖y‖ * |l (EuclideanSpace.single i 1)| := by
          intro i _
          have h_ci : |y i| ≤ ‖y‖ := by
            have h_inner : inner ℝ y (EuclideanSpace.single i 1) = y i := by
              rw [EuclideanSpace.inner_single_right i (1 : ℝ) y]
              <;> simp
            have h_cs : |inner ℝ y (EuclideanSpace.single i 1)| ≤ ‖y‖ * ‖(EuclideanSpace.single i 1 : E n)‖ :=
              abs_real_inner_le_norm y (EuclideanSpace.single i 1)
            have h_e1 : ‖(EuclideanSpace.single i 1 : E n)‖ = 1 := by
              rw [EuclideanSpace.norm_single] <;> norm_num
            rw [h_e1] at h_cs
            rw [← h_inner]
            <;> simpa using h_cs
          calc |y i * l (EuclideanSpace.single i 1)|
            = |y i| * |l (EuclideanSpace.single i 1)| := by rw [abs_mul]
          _ ≤ ‖y‖ * |l (EuclideanSpace.single i 1)| := by gcongr
        calc |∑ i : Fin n, y i * l (EuclideanSpace.single i 1)|
          ≤ ∑ i : Fin n, |y i * l (EuclideanSpace.single i 1)| := h_abs
        _ ≤ ∑ i : Fin n, (‖y‖ * |l (EuclideanSpace.single i 1)|) := Finset.sum_le_sum h_each
        _ = (∑ i : Fin n, |l (EuclideanSpace.single i 1)|) * ‖y‖ := by
          rw [← Finset.mul_sum, mul_comm]
      exact l.opNorm_le_bound (by positivity) h_coord
    have h2 : ∀ᵐ (x : E n) ∂(volume.restrict K),
        ‖fderiv ℝ (u k) x‖ₑ ≤ ∑ i : Fin n, ‖fderiv ℝ (u k) x (EuclideanSpace.single i 1)‖ₑ := by
      filter_upwards with x
      have h_real : ‖fderiv ℝ (u k) x‖ ≤ ∑ i : Fin n, |fderiv ℝ (u k) x (EuclideanSpace.single i 1)| := h1 x
      have h_nonneg : ∀ i, 0 ≤ |fderiv ℝ (u k) x (EuclideanSpace.single i 1)| := fun _ => abs_nonneg _
      have h_sum : ENNReal.ofReal (∑ i : Fin n, |fderiv ℝ (u k) x (EuclideanSpace.single i 1)|) =
          ∑ i : Fin n, ENNReal.ofReal |fderiv ℝ (u k) x (EuclideanSpace.single i 1)| := by
        exact ofReal_sum_of_nonneg fun i a => h_nonneg i
      have h_ofReal_le : ENNReal.ofReal ‖fderiv ℝ (u k) x‖ ≤
          ENNReal.ofReal (∑ i : Fin n, |fderiv ℝ (u k) x (EuclideanSpace.single i 1)|) := by
        exact ofReal_le_ofReal (h1 x)
      rw [h_sum] at h_ofReal_le
      have h_enorm1 : ‖fderiv ℝ (u k) x‖ₑ = ENNReal.ofReal ‖fderiv ℝ (u k) x‖ := by
        simp [enorm]
      have h_enorm2 : ∀ i, ‖fderiv ℝ (u k) x (EuclideanSpace.single i 1)‖ₑ =
          ENNReal.ofReal |fderiv ℝ (u k) x (EuclideanSpace.single i 1)| := by
        intro i
        exact Real.enorm_eq_ofReal_abs ((fderiv ℝ (u k) x) (EuclideanSpace.single i 1))
      rw [h_enorm1]
      rw [Finset.sum_congr rfl (fun i _ => h_enorm2 i)]
      exact h_ofReal_le
    have h3 : eLpNorm (fderiv ℝ (u k)) (1 : NNReal) (volume.restrict K) ≤
        ∑ i : Fin n, eLpNorm (fun y => fderiv ℝ (u k) y (EuclideanSpace.single i 1))
          (1 : NNReal) (volume.restrict K) := by
      have h4 : eLpNorm (fderiv ℝ (u k)) (1 : NNReal) (volume.restrict K) =
          ∫⁻ x, ‖fderiv ℝ (u k) x‖ₑ ∂(volume.restrict K) := by
        rw [eLpNorm_nnreal_eq_lintegral (show (1 : NNReal) ≠ 0 from by norm_num)]
        simp
      rw [h4]
      calc ∫⁻ x, ‖fderiv ℝ (u k) x‖ₑ ∂(volume.restrict K)
        ≤ ∫⁻ x, ∑ i : Fin n, ‖fderiv ℝ (u k) x (EuclideanSpace.single i 1)‖ₑ ∂(volume.restrict K) :=
          lintegral_mono_ae h2
      _ = ∑ i : Fin n, ∫⁻ x, ‖fderiv ℝ (u k) x (EuclideanSpace.single i 1)‖ₑ ∂(volume.restrict K) := by
        rw [lintegral_finset_sum]
        <;> fun_prop
      _ = ∑ i : Fin n, eLpNorm (fun y => fderiv ℝ (u k) y (EuclideanSpace.single i 1))
          (1 : NNReal) (volume.restrict K) := by
        apply Finset.sum_congr rfl
        intro i _
        have h_eLp_i : eLpNorm (fun y => (fderiv ℝ (u k) y) (EuclideanSpace.single i 1)) (1 : NNReal) (volume.restrict K) =
            ∫⁻ x, ‖(fderiv ℝ (u k) x) (EuclideanSpace.single i 1)‖ₑ ∂(volume.restrict K) := by
          rw [eLpNorm_nnreal_eq_lintegral (show (1 : NNReal) ≠ 0 from by norm_num)]
          simp
        exact h_eLp_i.symm
    have h5 : ∑ i : Fin n, eLpNorm (fun y => fderiv ℝ (u k) y (EuclideanSpace.single i 1))
          (1 : NNReal) (volume.restrict K) ≤
        ∑ i : Fin n, perimeterIn S Ω := by
      apply Finset.sum_le_sum
      intro i _
      exact h_grad_all i k hk
    have h6 : ∑ i : Fin n, perimeterIn S Ω = (n : ENNReal) * perimeterIn S Ω := by
      simp [Finset.sum_const, Finset.card_fin]
      <;> ring
    rw [h6] at h5
    exact le_trans h3 h5
  exact ⟨u, N_max, rfl, h_u_smooth, h_u_bound, h_u_l1, h_main⟩

end Geometry.Perimeter
