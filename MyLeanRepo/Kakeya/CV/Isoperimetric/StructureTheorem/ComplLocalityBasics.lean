import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterDefinition
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.CutoffFunctions
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DistributionalDerivative
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterMeasureSupport
import Mathlib.Tactic


/-!
# Complement and Locality Lemmas for Distributional Derivative

Proves four key lemmas needed for the complement side of Maggi 15.5:

1. `distributionalDerivative_compl`: D(Sᶜ) = -D(S)
2. `perimeterMeasure_compl`: perimeterMeasure Sᶜ = perimeterMeasure S
3. `distributionalDerivative_eq_on_compact`: D(S₁) = D(S₂) on compact K ⊆ open Ω when S₁ = S₂ on Ω
4. `perimeterMeasure_eq_on_compact`: perimeterMeasure S₁ = perimeterMeasure S₂ on K

## Proof route

- Complement: signed measure uniqueness from smooth test functions + component-wise argument.
- Locality: smooth cutoff η = 1 near K, supported in Ω, plus L¹ approximation.

## References
- Maggi, Sets of Finite Perimeter, Chapter 12
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff CompactlySupported

namespace Geometry.Perimeter

variable {n : ℕ}

/-- If a vector field has compact support, each component has compact support. -/
lemma hasCompactSupport_component {φ : E n → E n} (h : HasCompactSupport φ) (i : Fin n) :
    HasCompactSupport (fun x : E n => φ x i) := by
  have h1 : tsupport (fun x : E n => φ x i) ⊆ tsupport φ := by
    intro x hx
    by_contra h2
    let U : Set (E n) := (tsupport φ)ᶜ
    have hU_open : IsOpen U := isClosed_closure.isOpen_compl
    have hxU : x ∈ U := h2
    have hU_eq : ∀ y ∈ U, φ y = 0 := by
      intro y hy
      have h3 : y ∉ Function.support φ := by
        intro h4
        have h5 : y ∈ tsupport φ := subset_closure h4
        exact hy h5
      simpa [Function.mem_support] using h3
    have h6 : ∀ y ∈ U, (φ y i) = 0 := by
      intro y hy
      have h7 : φ y = 0 := hU_eq y hy
      rw [h7] <;> simp
    have h_disj : Disjoint U (Function.support (fun x : E n => φ x i)) := by
      rw [Set.disjoint_left]
      intro y hyU hys
      have h8 : φ y i = 0 := h6 y hyU
      have h9 : φ y i ≠ 0 := by simpa [Function.mem_support] using hys
      exact h9 h8
    have h_closure_disj : Disjoint U (tsupport (fun x : E n => φ x i)) :=
      h_disj.closure_right hU_open
    have h10 : x ∉ tsupport (fun x : E n => φ x i) := by
      have h11 : x ∈ U := hxU
      exact h_closure_disj.subset_compl_right h11
    exact h10 hx
  have h2 : IsCompact (tsupport φ) := h
  exact h2.of_isClosed_subset (isClosed_closure) h1

-- ============================================================================
-- Signed integral helper
-- ============================================================================

/-- Integral of a function against a signed measure (positive part minus negative part). -/
noncomputable def signedInt (μ : SignedMeasure (E n)) (f : E n → ℝ) : ℝ :=
  (∫ x, f x ∂μ.toJordanDecomposition.posPart) -
  (∫ x, f x ∂μ.toJordanDecomposition.negPart)

-- ============================================================================
-- Prerequisite: perimeterIn_compl and perimeter_compl
-- ============================================================================

/-- Complement local perimeter: `perimeterIn Sᶜ Ω = perimeterIn S Ω`. -/
lemma perimeterIn_compl {S : Set (E n)} {Ω : Set (E n)} (hS : MeasurableSet S) :
    perimeterIn Sᶜ Ω = perimeterIn S Ω := by
  unfold perimeterIn
  apply iSup_congr
  intro Φ
  let φ := Φ.val.toFun
  have hφ_smooth : ContDiff ℝ ∞ φ := Φ.val.smooth
  have hφ_support : HasCompactSupport φ := Φ.val.compact
  have hcomp_smooth : ∀ (i : Fin n), ContDiff ℝ ∞ (fun y : E n => φ y i) := by
    intro i
    have hproj : ContDiff ℝ ∞ (fun z : E n => z i) := contDiff_piLp_apply 2
    exact hproj.comp hφ_smooth
  have hcomp_support : ∀ (i : Fin n), HasCompactSupport (fun y : E n => φ y i) :=
    fun i => hasCompactSupport_component hφ_support i
  have hterm_int : ∀ (i : Fin n), Integrable (fun x : E n =>
      fderiv ℝ (fun y => φ y i) x (EuclideanSpace.single i 1)) volume := by
    intro i
    let f : E n → ℝ := fun y => φ y i
    have hfc : Continuous (fderiv ℝ f) :=
      (hcomp_smooth i).continuous_fderiv (by simp)
    let v : E n := EuclideanSpace.single i 1
    have heval : Continuous (fun L : (E n →L[ℝ] ℝ) => L v) := continuous_eval_const v
    have hcont : Continuous (fun x : E n => fderiv ℝ f x v) := heval.comp hfc
    have hsupp : HasCompactSupport (fun x : E n => fderiv ℝ f x v) :=
      (hcomp_support i).fderiv_apply (𝕜 := ℝ) v
    exact hcont.integrable_of_hasCompactSupport hsupp
  have hsum_int : ∀ (s : Finset (Fin n)),
      Integrable (fun x : E n => ∑ i ∈ s, fderiv ℝ (fun y => φ y i) x (EuclideanSpace.single i 1)) volume := by
    intro s
    exact Finset.induction_on s
      (by simpa using integrable_zero)
      (fun i s hi ih => by
        have h_sum : (fun x : E n => ∑ j ∈ insert i s, fderiv ℝ (fun y => φ y j) x (EuclideanSpace.single j 1)) =
            (fun x : E n => fderiv ℝ (fun y => φ y i) x (EuclideanSpace.single i 1)) +
            (fun x : E n => ∑ j ∈ s, fderiv ℝ (fun y => φ y j) x (EuclideanSpace.single j 1)) := by
          funext x
          rw [Finset.sum_insert hi] <;> rfl
        rw [h_sum]
        exact Integrable.add (hterm_int i) ih)
  have hdiv_int : Integrable (divergence φ) volume := by
    have h_eq : divergence φ = fun x : E n =>
        ∑ i : Fin n, fderiv ℝ (fun y => φ y i) x (EuclideanSpace.single i 1) := by
      funext x; rfl
    rw [h_eq]
    exact hsum_int Finset.univ
  have h2 : ∫ x, divergence φ x = 0 := integral_divergence_eq_zero hφ_smooth hφ_support
  have hS_int : IntegrableOn (divergence φ) S := hdiv_int.integrableOn
  have hSc_int : IntegrableOn (divergence φ) Sᶜ := hdiv_int.integrableOn
  have h5 : ∫ x in (S ∪ Sᶜ), divergence φ x =
      (∫ x in S, divergence φ x) + (∫ x in Sᶜ, divergence φ x) :=
    MeasureTheory.setIntegral_union (show Disjoint S Sᶜ from disjoint_compl_right)
      hS.compl hS_int hSc_int
  have h_univ : S ∪ Sᶜ = Set.univ := by simp
  have h6 : (∫ x in S, divergence φ x) + (∫ x in Sᶜ, divergence φ x) = 0 := by
    calc
      (∫ x in S, divergence φ x) + (∫ x in Sᶜ, divergence φ x)
        = ∫ x in (S ∪ Sᶜ), divergence φ x := h5.symm
      _ = ∫ x in (Set.univ), divergence φ x := by rw [h_univ]
      _ = ∫ x, divergence φ x := by simp
      _ = 0 := h2
  have h1 : ∫ x in Sᶜ, divergence φ x = -∫ x in S, divergence φ x := by
    have h7 : (∫ x in S, divergence φ x) + (∫ x in Sᶜ, divergence φ x) = 0 := h6
    linarith
  rw [h1] <;> rw [abs_neg]

/-- `perimeterIn S univ = perimeter S`. -/
lemma perimeterIn_univ_eq_perimeter (S : Set (E n)) :
    perimeterIn S Set.univ = perimeter S := by
  unfold perimeterIn perimeter
  apply le_antisymm
  · apply iSup_le
    intro Φ
    exact le_iSup (fun (ψ : TestVectorField) =>
      ENNReal.ofReal |∫ x in S, divergence ψ.toFun x|) Φ.val
  · apply iSup_le
    intro ψ
    have hψ_support : Function.support ψ.toFun ⊆ Set.univ := Set.subset_univ _
    let Φ : {Φ : TestVectorField // Function.support Φ.toFun ⊆ Set.univ} := ⟨ψ, hψ_support⟩
    exact le_iSup (fun (Φ' : {Φ : TestVectorField // Function.support Φ.toFun ⊆ Set.univ}) =>
      ENNReal.ofReal |∫ x in S, divergence Φ'.val.toFun x|) Φ

/-- Complement perimeter: `perimeter Sᶜ = perimeter S`. -/
lemma perimeter_compl {S : Set (E n)} (hS : MeasurableSet S) (hfin : perimeter S < ⊤) :
    perimeter Sᶜ = perimeter S := by
  have h1 : perimeter Sᶜ = perimeterIn Sᶜ Set.univ := (perimeterIn_univ_eq_perimeter Sᶜ).symm
  have h2 : perimeter S = perimeterIn S Set.univ := (perimeterIn_univ_eq_perimeter S).symm
  rw [h1, h2]
  exact perimeterIn_compl hS

-- ============================================================================
-- Prerequisite: integral of directional derivative over all space is zero
-- ============================================================================

/-- Integral of directional derivative of a smooth compactly supported function
over all space is zero. -/
lemma integral_fderiv_compact_eq_zero {f : E n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hsupp : HasCompactSupport f) (v : E n) :
    ∫ x : E n, (fderiv ℝ f x) v = 0 := by
  let φ : E n → E n := fun x => f x • v
  have hφ_smooth : ContDiff ℝ ∞ φ := by
    have h1 : ContDiff ℝ ∞ f := hf
    have h2 : ContDiff ℝ ∞ (fun (_ : E n) => v) := contDiff_const
    exact h1.smul h2
  have hφ_support : HasCompactSupport φ := by
    have h1 : Function.support φ ⊆ Function.support f := by
      intro x hx
      by_contra h2
      have h3 : f x = 0 := by simpa [Function.mem_support] using h2
      have h4 : φ x = 0 := by simp [φ, h3]
      exact hx (by simpa [Function.mem_support] using h4)
    exact HasCompactSupport.mono hsupp h1
  have hdiv : ∀ x, divergence φ x = (fderiv ℝ f x) v := by
    intro x
    have h1 : ∀ (i : Fin n), fderiv ℝ (fun y : E n => f y * v i) x (EuclideanSpace.single i 1) =
        (fderiv ℝ f x (EuclideanSpace.single i 1)) * v i := by
      intro i
      have h_eq1 : (fun y : E n => f y * v i) = (v i) • f := by
        funext y; simp [smul_eq_mul] <;> ring
      have h_diff : DifferentiableAt ℝ f x := (hf.differentiable (by norm_num)).differentiableAt
      have h_has : HasFDerivAt f (fderiv ℝ f x) x := h_diff.hasFDerivAt
      have h_has_smul : HasFDerivAt ((v i) • f) ((v i) • fderiv ℝ f x) x := h_has.const_smul (v i)
      have h_fd : fderiv ℝ (fun y : E n => f y * v i) x = (v i) • fderiv ℝ f x := by
        rw [h_eq1]
        exact h_has_smul.fderiv
      rw [h_fd] <;> simp [smul_eq_mul] <;> ring
    calc
      divergence φ x
        = ∑ i : Fin n, fderiv ℝ (fun y : E n => f y * v i) x (EuclideanSpace.single i 1) := by rfl
      _ = ∑ i : Fin n, (fderiv ℝ f x (EuclideanSpace.single i 1)) * v i := by
        apply Finset.sum_congr rfl; intro i _; exact h1 i
      _ = (fderiv ℝ f x) v := by
        have hsum : ∑ i : Fin n, (fderiv ℝ f x (EuclideanSpace.single i 1)) * v i =
            fderiv ℝ f x (∑ i : Fin n, v i • EuclideanSpace.single i (1 : ℝ)) := by
          rw [map_sum]
          <;> apply Finset.sum_congr rfl
          <;> intro i _ <;> simp [smul_eq_mul] <;> ring
        have hbasis : ∑ i : Fin n, v i • EuclideanSpace.single i (1 : ℝ) = v := by
          let b := EuclideanSpace.basisFun (Fin n) ℝ
          have h_eq_coeff : ∀ i : Fin n, b.toBasis.equivFun v i = v i := by
            intro i
            simp [b, EuclideanSpace.basisFun_toBasis]
            <;> rfl
          have h_eq_basis : ∀ i : Fin n, b.toBasis i = EuclideanSpace.single i (1 : ℝ) := by
            intro i
            simp [b, EuclideanSpace.basisFun_toBasis]
            <;> rfl
          have h : ∑ i : Fin n, b.toBasis.equivFun v i • b.toBasis i = v :=
            Module.Basis.sum_equivFun b.toBasis v
          rw [Finset.sum_congr rfl (fun i _ => by
            rw [h_eq_coeff i, h_eq_basis i])] at h
          exact h
        rw [hsum, hbasis]
  have h_eq_fun : (divergence φ) = fun x : E n => (fderiv ℝ f x) v := by
    funext x; exact hdiv x
  have h_goal : ∫ x : E n, (fderiv ℝ f x) v = 0 := by
    rw [←h_eq_fun]
    exact integral_divergence_eq_zero hφ_smooth hφ_support
  exact h_goal

-- ============================================================================
-- Prerequisite: -μ satisfies the Sᶜ formula
-- ============================================================================

/-- The negated signed measure `-μ` satisfies the distributional derivative
formula for `Sᶜ`. -/
lemma distributionalDerivative_neg_compl_formula {S : Set (E n)} (hS : MeasurableSet S)
    (hfin : perimeter S < ⊤) (i : Fin n)
    (f : E n → ℝ) (hf : ContDiff ℝ ∞ f) (hsupp : HasCompactSupport f) :
    let μ := Classical.choose (distributionalDerivative_signedMeasure S i hfin)
    (∫ x in Sᶜ, (fderiv ℝ f x) (EuclideanSpace.single i (1 : ℝ))) =
      signedInt (-μ) f := by
  let μ := Classical.choose (distributionalDerivative_signedMeasure S i hfin)
  have hμ_spec : (∀ (g : E n → ℝ) (hg : ContDiff ℝ ∞ g) (hsuppg : HasCompactSupport g),
      (∫ x in S, (fderiv ℝ g x) (EuclideanSpace.single i (1 : ℝ))) =
        signedInt μ g) ∧
      (μ.totalVariation Set.univ ≤ perimeter S) :=
    Classical.choose_spec (distributionalDerivative_signedMeasure S i hfin)
  have hμ_formula := hμ_spec.1
  let e_i : E n := EuclideanSpace.single i (1 : ℝ)
  have h_int_zero : ∫ x : E n, (fderiv ℝ f x) e_i = 0 :=
    integral_fderiv_compact_eq_zero hf hsupp e_i
  have hcont : Continuous (fun x : E n => (fderiv ℝ f x) e_i) := by
    let eval_v : (E n →L[ℝ] ℝ) →L[ℝ] ℝ :=
      { toFun := fun g => g e_i
        map_add' := by intro a b; rfl
        map_smul' := by intro c a; rfl }
    exact eval_v.continuous.comp (hf.continuous_fderiv (by norm_num))
  have hsupp' : HasCompactSupport (fun x : E n => (fderiv ℝ f x) e_i) :=
    hsupp.fderiv_apply (𝕜 := ℝ) e_i
  have h3 : Integrable (fun x : E n => (fderiv ℝ f x) e_i) volume :=
    hcont.integrable_of_hasCompactSupport hsupp'
  have h4 : (∫ x in S, (fderiv ℝ f x) e_i) + (∫ x in Sᶜ, (fderiv ℝ f x) e_i) =
      ∫ x : E n, (fderiv ℝ f x) e_i := by
    have h_union : ∫ x in (S ∪ Sᶜ), (fderiv ℝ f x) e_i =
        (∫ x in S, (fderiv ℝ f x) e_i) + (∫ x in Sᶜ, (fderiv ℝ f x) e_i) :=
      MeasureTheory.setIntegral_union (show Disjoint S Sᶜ from disjoint_compl_right)
        hS.compl h3.integrableOn h3.integrableOn
    have h_univ : S ∪ Sᶜ = Set.univ := by simp
    simpa [h_univ] using h_union.symm
  have h5 : (∫ x in Sᶜ, (fderiv ℝ f x) e_i) = -(∫ x in S, (fderiv ℝ f x) e_i) := by
    have h : (∫ x in S, (fderiv ℝ f x) e_i) + (∫ x in Sᶜ, (fderiv ℝ f x) e_i) = 0 := by
      rw [h4, h_int_zero]
    linarith
  have h6 : (∫ x in S, (fderiv ℝ f x) e_i) = signedInt μ f :=
    hμ_formula f hf hsupp
  have h_neg_int : signedInt (-μ) f = -signedInt μ f := by
    let j := μ.toJordanDecomposition
    have hneg_j : (-μ).toJordanDecomposition = -j :=
      MeasureTheory.SignedMeasure.toJordanDecomposition_neg μ
    have hpos : (-μ).toJordanDecomposition.posPart = j.negPart := by
      rw [hneg_j]
      exact MeasureTheory.JordanDecomposition.neg_posPart j
    have hneg : (-μ).toJordanDecomposition.negPart = j.posPart := by
      rw [hneg_j]
      exact MeasureTheory.JordanDecomposition.neg_negPart j
    dsimp only [signedInt]
    rw [hpos, hneg] <;> ring
  dsimp only
  rw [h5, h6, h_neg_int]

-- ============================================================================
-- Smooth approximation and measure uniqueness
-- ============================================================================

/-- Approximation: for any continuous compactly supported `f` and `ε > 0`,
there exists smooth compactly supported `g` with `‖g - f‖∞ ≤ ε`. -/
lemma smooth_approx_of_continuous_compactSupport
    {f : E n → ℝ} (hf_cont : Continuous f) (hf_supp : HasCompactSupport f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : E n → ℝ), ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x, |g x - f x| ≤ ε := by
  have h_uniform : UniformContinuous f :=
    hf_supp.uniformContinuous_of_continuous hf_cont
  rcases h_uniform.exists_contDiff_dist_le hε with ⟨g_smooth, hg_smooth, hg_close⟩
  let K := tsupport f
  have hK_compact : IsCompact K := hf_supp
  have hK_bdd : Bornology.IsBounded K := hK_compact.isBounded
  rcases hK_bdd.subset_ball 0 with ⟨R0, hK_sub0⟩
  let R : ℝ := max R0 1 + 1
  have hR_pos : 0 < R := by positivity
  have hR0_le : R0 ≤ R := by
    have h1 : R0 ≤ max R0 1 := le_max_left R0 1
    have h2 : max R0 1 ≤ R := by simp [R] <;> linarith
    exact le_trans h1 h2
  have hK_sub : K ⊆ ball (0 : E n) R := by
    intro x hx
    have h1 : dist x 0 < R0 := hK_sub0 hx
    have h4 : dist x 0 < R := lt_of_lt_of_le h1 hR0_le
    simpa [ball] using h4
  let ψ_bump : ContDiffBump (0 : E n) := ⟨R, R + 1, hR_pos, by linarith⟩
  let h : E n → ℝ := fun x => (ψ_bump x) * (g_smooth x)
  have hψ_smooth : ContDiff ℝ ∞ (ψ_bump : E n → ℝ) := ψ_bump.contDiff
  have hh_smooth : ContDiff ℝ ∞ h := hψ_smooth.mul hg_smooth
  have hh_supp : HasCompactSupport h := ψ_bump.hasCompactSupport.mul_right
  have h_estimate : ∀ x, |h x - f x| ≤ ε := by
    intro x
    by_cases hx : x ∈ K
    · have h_in_ball : x ∈ ball (0 : E n) ψ_bump.rIn := by
        simpa [ψ_bump] using hK_sub hx
      have h_in_closed : x ∈ closedBall (0 : E n) ψ_bump.rIn :=
        ball_subset_closedBall h_in_ball
      have hψ1 : ψ_bump x = 1 := ψ_bump.one_of_mem_closedBall h_in_closed
      have h_h_eq_g : h x = g_smooth x := by
        dsimp only [h]; rw [hψ1] <;> ring
      rw [h_h_eq_g]
      have h9 : dist (g_smooth x) (f x) < ε := hg_close x
      simpa [Real.dist_eq] using le_of_lt h9
    · have h_not_supp : x ∉ Function.support f := fun h => hx (subset_closure h)
      have hf0 : f x = 0 := by simpa [Function.mem_support] using h_not_supp
      have hψ_nonneg : 0 ≤ ψ_bump x := ψ_bump.nonneg
      have hψ_le_one : ψ_bump x ≤ 1 := ψ_bump.le_one
      have hg_abs : |g_smooth x| < ε := by
        have h9 : dist (g_smooth x) (f x) < ε := hg_close x
        rw [hf0] at h9
        simpa [Real.dist_eq, sub_zero] using h9
      have h_abs : |h x| ≤ |g_smooth x| := by
        dsimp only [h]
        have h10 : |ψ_bump x * g_smooth x| = |ψ_bump x| * |g_smooth x| := by rw [abs_mul]
        rw [h10]
        have h11 : |ψ_bump x| ≤ 1 := by
          rw [abs_of_nonneg hψ_nonneg]; exact hψ_le_one
        have h12 : |ψ_bump x| * |g_smooth x| ≤ 1 * |g_smooth x| :=
          mul_le_mul_of_nonneg_right h11 (abs_nonneg _)
        simpa using h12
      rw [hf0]
      simpa using le_trans h_abs (le_of_lt hg_abs)
  exact ⟨h, hh_smooth, hh_supp, h_estimate⟩

/-- Two finite positive measures agreeing on all smooth compactly supported
functions are equal. -/
lemma measure_unique_of_smooth
    {μ ν : Measure (E n)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (ψ : E n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        ∫ x, ψ x ∂μ = ∫ x, ψ x ∂ν) :
    μ = ν := by
  have h_main : ∀ (f : C_c(E n, ℝ)), ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
    intro f
    let f_fun : E n → ℝ := f
    have hf_cont : Continuous f_fun := f.continuous
    have hf_supp : HasCompactSupport f_fun := f.hasCompactSupport'
    have h_approx : ∀ (ε : ℝ), 0 < ε → ∃ (g : E n → ℝ),
        ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x, |g x - f_fun x| ≤ ε := by
      intro ε hε
      exact smooth_approx_of_continuous_compactSupport (ε := ε) hf_cont hf_supp hε
    by_contra hne
    set δ : ℝ := |(∫ x, f_fun x ∂μ) - (∫ x, f_fun x ∂ν)| with hδ_def
    have hδ_ne_zero : (∫ x, f_fun x ∂μ) - (∫ x, f_fun x ∂ν) ≠ 0 := by
      intro h
      have h' : ∫ x, f_fun x ∂μ = ∫ x, f_fun x ∂ν := by linarith
      exact hne h'
    have hδ_pos : 0 < δ := by
      rw [hδ_def]
      exact abs_pos.mpr hδ_ne_zero
    set M : ℝ := (μ Set.univ).toReal + (ν Set.univ).toReal with hM_def
    have hM_nonneg : 0 ≤ M := by positivity
    have hM_pos : 0 < M := by
      by_contra hM0
      have hM_le : M ≤ 0 := by linarith
      have hM_eq : M = 0 := by linarith [hM_nonneg]
      have h1 : 0 ≤ (μ Set.univ).toReal := by positivity
      have h2 : 0 ≤ (ν Set.univ).toReal := by positivity
      have h3 : (μ Set.univ).toReal = 0 := by
        simp only [hM_def] at hM_eq; linarith
      have h4 : (ν Set.univ).toReal = 0 := by
        simp only [hM_def] at hM_eq; linarith
      have hμ0 : μ Set.univ = 0 := by
        simpa [ENNReal.toReal_eq_zero_iff] using h3
      have hν0 : ν Set.univ = 0 := by
        simpa [ENNReal.toReal_eq_zero_iff] using h4
      have hμ_triv : μ = 0 := by
        apply Measure.ext; intro s _
        have h5 : μ s ≤ μ Set.univ := measure_mono (subset_univ s)
        rw [hμ0] at h5; simpa using h5
      have hν_triv : ν = 0 := by
        apply Measure.ext; intro s _
        have h5 : ν s ≤ ν Set.univ := measure_mono (subset_univ s)
        rw [hν0] at h5; simpa using h5
      rw [hμ_triv, hν_triv] at hne
      simp at hne
    set ε : ℝ := δ / (2 * M + 1) with hε_def
    have hε_pos : 0 < ε := by positivity
    rcases h_approx ε hε_pos with ⟨g, hg_smooth, hg_supp, hg_close⟩
    have hg_int_μ : Integrable g μ := hg_smooth.continuous.integrable_of_hasCompactSupport hg_supp
    have hg_int_ν : Integrable g ν := hg_smooth.continuous.integrable_of_hasCompactSupport hg_supp
    have hf_int_μ : Integrable f_fun μ := hf_cont.integrable_of_hasCompactSupport hf_supp
    have hf_int_ν : Integrable f_fun ν := hf_cont.integrable_of_hasCompactSupport hf_supp
    have h_eq_smooth : ∫ x, g x ∂μ = ∫ x, g x ∂ν := h g hg_smooth hg_supp
    have h_close' : ∀ x, |f_fun x - g x| ≤ ε := by
      intro x
      have h : |g x - f_fun x| ≤ ε := hg_close x
      rw [abs_sub_comm] at h
      exact h
    have h_bound1 : |(∫ x, f_fun x ∂μ) - (∫ x, g x ∂μ)| ≤ ε * (μ Set.univ).toReal := by
      have h_abs : Integrable (fun x => |f_fun x - g x|) μ := (hf_int_μ.sub hg_int_μ).abs
      have h_const : Integrable (fun _ => ε) μ := integrable_const ε
      have h_eq : (∫ x, f_fun x ∂μ) - (∫ x, g x ∂μ) = ∫ x, (f_fun x - g x) ∂μ := by
        rw [integral_sub hf_int_μ hg_int_μ]
      rw [h_eq]
      have h2 : |∫ x, (f_fun x - g x) ∂μ| ≤ ∫ x, |f_fun x - g x| ∂μ :=
        abs_integral_le_integral_abs
      have h3 : ∫ x, |f_fun x - g x| ∂μ ≤ ∫ x, ε ∂μ :=
        integral_mono h_abs h_const (fun x => h_close' x)
      have h4 : ∫ x, ε ∂μ = ε * (μ Set.univ).toReal := by
        have h5 : ∫ x, ε ∂μ = Measure.real μ Set.univ * ε := by
          simpa [smul_eq_mul] using integral_const ε
        have h6 : Measure.real μ Set.univ = (μ Set.univ).toReal := by rfl
        rw [h5, h6] <;> ring
      rw [h4] at h3
      exact le_trans h2 h3
    have h_bound2 : |(∫ x, g x ∂ν) - (∫ x, f_fun x ∂ν)| ≤ ε * (ν Set.univ).toReal := by
      have h_abs : Integrable (fun x => |g x - f_fun x|) ν := (hg_int_ν.sub hf_int_ν).abs
      have h_const : Integrable (fun _ => ε) ν := integrable_const ε
      have h_eq : (∫ x, g x ∂ν) - (∫ x, f_fun x ∂ν) = ∫ x, (g x - f_fun x) ∂ν := by
        rw [integral_sub hg_int_ν hf_int_ν]
      rw [h_eq]
      have h2 : |∫ x, (g x - f_fun x) ∂ν| ≤ ∫ x, |g x - f_fun x| ∂ν :=
        abs_integral_le_integral_abs
      have h3 : ∫ x, |g x - f_fun x| ∂ν ≤ ∫ x, ε ∂ν :=
        integral_mono h_abs h_const (fun x => hg_close x)
      have h4 : ∫ x, ε ∂ν = ε * (ν Set.univ).toReal := by
        have h5 : ∫ x, ε ∂ν = Measure.real ν Set.univ * ε := by
          simpa [smul_eq_mul] using integral_const ε
        have h6 : Measure.real ν Set.univ = (ν Set.univ).toReal := by rfl
        rw [h5, h6] <;> ring
      rw [h4] at h3
      exact le_trans h2 h3
    set a : ℝ := (∫ x, f_fun x ∂μ) - (∫ x, g x ∂μ) with ha_def
    set b : ℝ := (∫ x, g x ∂ν) - (∫ x, f_fun x ∂ν) with hb_def
    have h_main_eq : (∫ x, f_fun x ∂μ) - (∫ x, f_fun x ∂ν) = a + b := by
      dsimp only [a, b]
      rw [h_eq_smooth] <;> ring
    have h_triangle : |a + b| ≤ |a| + |b| := by exact abs_add_le a b
    have h_la : |a| ≤ ε * (μ Set.univ).toReal := h_bound1
    have h_lb : |b| ≤ ε * (ν Set.univ).toReal := h_bound2
    have h_le : |a + b| ≤ ε * M := by
      calc
        |a + b| ≤ |a| + |b| := h_triangle
        _ ≤ ε * (μ Set.univ).toReal + ε * (ν Set.univ).toReal := add_le_add h_la h_lb
        _ = ε * M := by ring
    have h_lt : ε * M < δ := by
      rw [hε_def]
      have h5 : 0 ≤ M := hM_nonneg
      have h6 : 0 < δ := hδ_pos
      have h7 : M / (2 * M + 1) < 1 := by
        apply (div_lt_one (by positivity)).mpr
        linarith
      have h8 : δ * (M / (2 * M + 1)) < δ := by
        exact (mul_lt_iff_lt_one_right h6).mpr h7
      have h9 : δ / (2 * M + 1) * M = δ * (M / (2 * M + 1)) := by ring
      rw [h9]
      exact h8
    have h10 : |(∫ x, f_fun x ∂μ) - (∫ x, f_fun x ∂ν)| < δ := by
      rw [h_main_eq]
      exact lt_of_le_of_lt h_le h_lt
    have h11 : |(∫ x, f_fun x ∂μ) - (∫ x, f_fun x ∂ν)| = δ := by
      rw [hδ_def]
    rw [h11] at h10
    exact lt_irrefl δ h10
  exact MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported h_main

/-- Two finite signed measures agreeing on all smooth compactly supported
functions are equal. -/
lemma signedMeasure_unique_of_smooth
    {μ ν : SignedMeasure (E n)}
    (hμ_fin : μ.totalVariation Set.univ < ⊤)
    (hν_fin : ν.totalVariation Set.univ < ⊤)
    (h : ∀ (ψ : E n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        signedInt μ ψ = signedInt ν ψ) :
    μ = ν := by
  let jμ := μ.toJordanDecomposition
  let jν := ν.toJordanDecomposition
  have hμ_pos_fin : IsFiniteMeasure jμ.posPart := by
    have h1 : jμ.posPart Set.univ ≤ μ.totalVariation Set.univ := by
      simp only [SignedMeasure.totalVariation]
      exact le_add_right (le_refl _)
    have h2 : jμ.posPart Set.univ < ⊤ := lt_of_le_of_lt h1 hμ_fin
    exact jμ.posPart_finite
  have hμ_neg_fin : IsFiniteMeasure jμ.negPart := by
    have h1 : jμ.negPart Set.univ ≤ μ.totalVariation Set.univ := by
      simp only [SignedMeasure.totalVariation]
      exact le_add_left (le_refl _)
    have h2 : jμ.negPart Set.univ < ⊤ := lt_of_le_of_lt h1 hμ_fin
    exact jμ.negPart_finite
  have hν_pos_fin : IsFiniteMeasure jν.posPart := by
    have h1 : jν.posPart Set.univ ≤ ν.totalVariation Set.univ := by
      simp only [SignedMeasure.totalVariation]
      exact le_add_right (le_refl _)
    have h2 : jν.posPart Set.univ < ⊤ := lt_of_le_of_lt h1 hν_fin
    exact jν.posPart_finite
  have hν_neg_fin : IsFiniteMeasure jν.negPart := by
    have h1 : jν.negPart Set.univ ≤ ν.totalVariation Set.univ := by
      simp only [SignedMeasure.totalVariation]
      exact le_add_left (le_refl _)
    have h2 : jν.negPart Set.univ < ⊤ := lt_of_le_of_lt h1 hν_fin
    exact jν.negPart_finite
  let μ1 : Measure (E n) := jμ.posPart + jν.negPart
  let ν1 : Measure (E n) := jν.posPart + jμ.negPart
  have h_eq : ∀ (ψ : E n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x, ψ x ∂μ1 = ∫ x, ψ x ∂ν1 := by
    intro ψ hψ hsupp
    have hψ_int_pos : Integrable ψ jμ.posPart :=
      hψ.continuous.integrable_of_hasCompactSupport hsupp
    have hψ_int_neg : Integrable ψ jμ.negPart :=
      hψ.continuous.integrable_of_hasCompactSupport hsupp
    have hψ_int_vpos : Integrable ψ jν.posPart :=
      hψ.continuous.integrable_of_hasCompactSupport hsupp
    have hψ_int_vneg : Integrable ψ jν.negPart :=
      hψ.continuous.integrable_of_hasCompactSupport hsupp
    have h_signed : signedInt μ ψ = signedInt ν ψ := h ψ hψ hsupp
    dsimp only [signedInt] at h_signed
    have h1 : (∫ x, ψ x ∂jμ.posPart) + (∫ x, ψ x ∂jν.negPart) =
        (∫ x, ψ x ∂jν.posPart) + (∫ x, ψ x ∂jμ.negPart) := by linarith
    have h2 : ∫ x, ψ x ∂μ1 = (∫ x, ψ x ∂jμ.posPart) + (∫ x, ψ x ∂jν.negPart) := by
      exact integral_add_measure hψ_int_pos hψ_int_vneg
    have h3 : ∫ x, ψ x ∂ν1 = (∫ x, ψ x ∂jν.posPart) + (∫ x, ψ x ∂jμ.negPart) := by
      exact integral_add_measure hψ_int_vpos hψ_int_neg
    rw [h2, h3]
    exact h1
  have h_meas_eq : μ1 = ν1 := measure_unique_of_smooth h_eq
  apply VectorMeasure.ext
  intro A hA
  have h4 : μ1 A = ν1 A := by rw [h_meas_eq]
  have h5 : jμ.posPart A + jν.negPart A = jν.posPart A + jμ.negPart A := h4
  have hfin1 : jμ.posPart A ≠ ⊤ := measure_ne_top jμ.posPart A
  have hfin2 : jν.negPart A ≠ ⊤ := measure_ne_top jν.negPart A
  have hfin3 : jν.posPart A ≠ ⊤ := measure_ne_top jν.posPart A
  have hfin4 : jμ.negPart A ≠ ⊤ := measure_ne_top jμ.negPart A
  have h6 : (jμ.posPart A).toReal + (jν.negPart A).toReal =
      (jν.posPart A).toReal + (jμ.negPart A).toReal := by
    have h7 : (jμ.posPart A + jν.negPart A).toReal = (jν.posPart A + jμ.negPart A).toReal := by
      rw [h5]
    rw [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_add hfin3 hfin4] at h7
    exact h7
  have h7 : (jμ.posPart A).toReal - (jμ.negPart A).toReal =
      (jν.posPart A).toReal - (jν.negPart A).toReal := by linarith
  have hμ_eval : μ A = (jμ.posPart A).toReal - (jμ.negPart A).toReal := by
    have h8 : jμ.toSignedMeasure = μ :=
      SignedMeasure.toSignedMeasure_toJordanDecomposition μ
    have h9 : jμ.toSignedMeasure A = (jμ.posPart A).toReal - (jμ.negPart A).toReal := by
      rw [JordanDecomposition.toSignedMeasure]
      have h10 : (jμ.posPart.toSignedMeasure - jμ.negPart.toSignedMeasure) A =
          (jμ.posPart A).toReal - (jμ.negPart A).toReal := by
        rw [Measure.toSignedMeasure_sub_apply hA] <;> rfl
      exact h10
    rw [←h8]
    exact h9
  have hν_eval : ν A = (jν.posPart A).toReal - (jν.negPart A).toReal := by
    have h8 : jν.toSignedMeasure = ν :=
      SignedMeasure.toSignedMeasure_toJordanDecomposition ν
    have h9 : jν.toSignedMeasure A = (jν.posPart A).toReal - (jν.negPart A).toReal := by
      rw [JordanDecomposition.toSignedMeasure]
      have h10 : (jν.posPart.toSignedMeasure - jν.negPart.toSignedMeasure) A =
          (jν.posPart A).toReal - (jν.negPart A).toReal := by
        rw [Measure.toSignedMeasure_sub_apply hA] <;> rfl
      exact h10
    rw [←h8]
    exact h9
  rw [hμ_eval, hν_eval]
  exact h7

-- ============================================================================
-- Main complement results
-- ============================================================================

/-- **Complement formula**: `distributionalDerivative Sᶜ = -distributionalDerivative S`. -/
theorem distributionalDerivative_compl {S : Set (E n)} (hS : MeasurableSet S)
    (hfin : perimeter S < ⊤) :
    distributionalDerivative Sᶜ = -distributionalDerivative S := by
  have hfin_C : perimeter Sᶜ < ⊤ := by
    rw [perimeter_compl hS hfin] <;> exact hfin
  have h_main : ∀ (i : Fin n),
      (Classical.choose (distributionalDerivative_signedMeasure Sᶜ i hfin_C)) =
      -(Classical.choose (distributionalDerivative_signedMeasure S i hfin)) := by
    intro i
    let μ_S := Classical.choose (distributionalDerivative_signedMeasure S i hfin)
    let μ_Sc := Classical.choose (distributionalDerivative_signedMeasure Sᶜ i hfin_C)
    have hμ_S_spec : (∀ (g : E n → ℝ) (hg : ContDiff ℝ ∞ g) (hsuppg : HasCompactSupport g),
        (∫ x in S, (fderiv ℝ g x) (EuclideanSpace.single i (1 : ℝ))) =
          signedInt μ_S g) ∧ (μ_S.totalVariation Set.univ ≤ perimeter S) :=
      Classical.choose_spec (distributionalDerivative_signedMeasure S i hfin)
    have hμ_Sc_spec : (∀ (g : E n → ℝ) (hg : ContDiff ℝ ∞ g) (hsuppg : HasCompactSupport g),
        (∫ x in Sᶜ, (fderiv ℝ g x) (EuclideanSpace.single i (1 : ℝ))) =
          signedInt μ_Sc g) ∧ (μ_Sc.totalVariation Set.univ ≤ perimeter Sᶜ) :=
      Classical.choose_spec (distributionalDerivative_signedMeasure Sᶜ i hfin_C)
    have h1 : ∀ (g : E n → ℝ) (hg : ContDiff ℝ ∞ g) (hsuppg : HasCompactSupport g),
        signedInt μ_Sc g = signedInt (-μ_S) g := by
      intro g hg hsuppg
      have h2 : (∫ x in Sᶜ, (fderiv ℝ g x) (EuclideanSpace.single i (1 : ℝ))) =
          signedInt μ_Sc g := hμ_Sc_spec.1 g hg hsuppg
      have h3 : (∫ x in Sᶜ, (fderiv ℝ g x) (EuclideanSpace.single i (1 : ℝ))) =
          signedInt (-μ_S) g :=
        distributionalDerivative_neg_compl_formula hS hfin i g hg hsuppg
      rw [h2] at h3
      exact h3
    have hμ_S_fin : μ_S.totalVariation Set.univ < ⊤ := by
      have h4 : μ_S.totalVariation Set.univ ≤ perimeter S := hμ_S_spec.2
      exact lt_of_le_of_lt h4 hfin
    have hμ_Sc_fin : μ_Sc.totalVariation Set.univ < ⊤ := by
      have h4 : μ_Sc.totalVariation Set.univ ≤ perimeter Sᶜ := hμ_Sc_spec.2
      exact lt_of_le_of_lt h4 hfin_C
    have h_neg_fin : (-μ_S).totalVariation Set.univ < ⊤ := by
      rw [SignedMeasure.totalVariation_neg]
      exact hμ_S_fin
    exact signedMeasure_unique_of_smooth hμ_Sc_fin h_neg_fin h1
  have hS_iff : perimeter S < ⊤ := hfin
  have hSc_iff : perimeter Sᶜ < ⊤ := hfin_C
  let hom_i (i : Fin n) : ℝ →+ E n :=
    { toFun := fun r : ℝ => r • (EuclideanSpace.single i (1 : ℝ))
      map_zero' := by simp
      map_add' := by intro a b; simp [add_smul] }
  have hcont_i (i : Fin n) : Continuous (hom_i i) := by
    change Continuous (fun r : ℝ => r • EuclideanSpace.single i (1 : ℝ))
    fun_prop
  have h_unfold_S : distributionalDerivative S =
      ∑ i : Fin n, (Classical.choose (distributionalDerivative_signedMeasure S i hfin)).mapRange (hom_i i) (hcont_i i) := by
    simp [distributionalDerivative, hS_iff, hom_i]
    <;> rfl
  have h_unfold_Sc : distributionalDerivative Sᶜ =
      ∑ i : Fin n, (Classical.choose (distributionalDerivative_signedMeasure Sᶜ i hfin_C)).mapRange (hom_i i) (hcont_i i) := by
    simp [distributionalDerivative, hSc_iff, hom_i]
    <;> rfl
  rw [h_unfold_Sc, h_unfold_S]
  have h_sum : ∑ i : Fin n, (Classical.choose (distributionalDerivative_signedMeasure Sᶜ i hfin_C)).mapRange (hom_i i) (hcont_i i) =
      -∑ i : Fin n, (Classical.choose (distributionalDerivative_signedMeasure S i hfin)).mapRange (hom_i i) (hcont_i i) := by
    have h6 : ∑ i : Fin n, (Classical.choose (distributionalDerivative_signedMeasure Sᶜ i hfin_C)).mapRange (hom_i i) (hcont_i i) =
        ∑ i : Fin n, (-(Classical.choose (distributionalDerivative_signedMeasure S i hfin))).mapRange (hom_i i) (hcont_i i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [h_main i]
    rw [h6]
    have h7 : ∑ i : Fin n, (-(Classical.choose (distributionalDerivative_signedMeasure S i hfin))).mapRange (hom_i i) (hcont_i i) =
        -∑ i : Fin n, (Classical.choose (distributionalDerivative_signedMeasure S i hfin)).mapRange (hom_i i) (hcont_i i) := by
      have h8 : ∀ i : Fin n, (-(Classical.choose (distributionalDerivative_signedMeasure S i hfin))).mapRange (hom_i i) (hcont_i i) =
          -((Classical.choose (distributionalDerivative_signedMeasure S i hfin)).mapRange (hom_i i) (hcont_i i)) := by
        intro i
        let μ_i := Classical.choose (distributionalDerivative_signedMeasure S i hfin)
        have h_add : (μ_i + (-μ_i)).mapRange (hom_i i) (hcont_i i) =
            μ_i.mapRange (hom_i i) (hcont_i i) + (-μ_i).mapRange (hom_i i) (hcont_i i) :=
          VectorMeasure.mapRange_add (hcont_i i)
        have h_zero : (μ_i + (-μ_i)) = (0 : SignedMeasure (E n)) := by simp
        rw [h_zero] at h_add
        have h1 : (0 : SignedMeasure (E n)).mapRange (hom_i i) (hcont_i i) = 0 := by
          exact VectorMeasure.mapRange_zero (hcont_i i)
        rw [h1] at h_add
        have h2 : (0 : VectorMeasure (E n) (E n)) =
            μ_i.mapRange (hom_i i) (hcont_i i) + (-μ_i).mapRange (hom_i i) (hcont_i i) := h_add
        have h3 : (-μ_i).mapRange (hom_i i) (hcont_i i) =
            -μ_i.mapRange (hom_i i) (hcont_i i) := by
          have h4 : (-μ_i).mapRange (hom_i i) (hcont_i i) + μ_i.mapRange (hom_i i) (hcont_i i) = 0 := by
            rw [add_comm]
            exact h2.symm
          exact eq_neg_of_add_eq_zero_left h4
        exact h3
      have h9 : ∑ i : Fin n, (-(Classical.choose (distributionalDerivative_signedMeasure S i hfin))).mapRange (hom_i i) (hcont_i i) =
          ∑ i : Fin n, -((Classical.choose (distributionalDerivative_signedMeasure S i hfin)).mapRange (hom_i i) (hcont_i i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h8 i
      rw [h9]
      rw [Finset.sum_neg_distrib]
    exact h7
  exact h_sum

/-- **Complement formula**: `perimeterMeasure Sᶜ = perimeterMeasure S`. -/
theorem perimeterMeasure_compl {S : Set (E n)} (hS : MeasurableSet S)
    (hfin : perimeter S < ⊤) :
    perimeterMeasure Sᶜ = perimeterMeasure S := by
  rw [perimeterMeasure, perimeterMeasure]
  rw [distributionalDerivative_compl hS hfin]
  have h : ((-(distributionalDerivative S)).variation) = (distributionalDerivative S).variation :=
    VectorMeasure.variation_neg (μ := distributionalDerivative S)
  exact h

end Geometry.Perimeter
