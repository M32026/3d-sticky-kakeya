/-
# Half-Space Characterization (Maggi Proposition 15.15)

If a set F has locally finite perimeter and its Gauss-Green measure has
constant direction (Dχ_F = v · |Dχ_F|), then F is equivalent a.e. to a
half-space {z : inner(z, v) < c}.

## Key lemmas

1. `directionalVariation_zero_iff`: zero directional variation iff all
   smooth compactly supported test integrals vanish.
2. `zero_directionalVariation_translation_invariant`: zero directional
   variation implies a.e. translation invariance.
3. `halfSpace_characterization`: main theorem (assembles bridge lemmas with
   pelican's `half_space_characterization_conditional`).

## References

- Maggi, Sets of Finite Perimeter, Proposition 15.15
- AFP, Functions of BV, Theorem 3.57
-/

import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.Perimeter

variable {n : ℕ}

attribute [local instance] Classical.propDecidable

-- ============================================================================
-- Lemma 1: Zero directional variation iff all test integrals vanish
-- ============================================================================

/-- If `directionalVariation S v = 0`, then `∫_S ∂_v ψ = 0` for every
smooth compactly supported `ψ` (not just those bounded by 1). -/
lemma directionalVariation_zero_iff {S : Set (E n)} {v : E n}
    (hS : MeasurableSet S) :
    directionalVariation S v = 0 ↔
    ∀ (ψ : E n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x in S, fderiv ℝ ψ x v = 0 := by
  constructor
  · intro h ψ hψ hsupp
    by_cases hψ0 : ψ = 0
    · rw [hψ0]; simp
    · have h_bdd : ∃ (C : ℝ), 0 < C ∧ ∀ x, |ψ x| ≤ C := by
        have h1 : ∃ (C : ℝ), ∀ (x : E n), ‖ψ x‖ ≤ C :=
          hψ.continuous.bounded_above_of_compact_support hsupp
        rcases h1 with ⟨C0, hC0⟩
        let C := max C0 1
        refine ⟨C, by positivity, fun x => ?_⟩
        have h2 : ‖ψ x‖ ≤ C0 := hC0 x
        have h3 : |ψ x| = ‖ψ x‖ := by simp
        rw [h3]; exact h2.trans (le_max_left C0 1)
      rcases h_bdd with ⟨C, hC_pos, hC_bound⟩
      let φ : E n → ℝ := fun x => ψ x / C
      have hφ_smooth : ContDiff ℝ ∞ φ := hψ.div_const C
      have hφ_supp : HasCompactSupport φ := by
        have h1 : Function.support φ ⊆ Function.support ψ := by
          intro x hx
          have h5 : φ x ≠ 0 := hx
          have h6 : ψ x ≠ 0 := by
            by_contra h7
            have h8 : φ x = 0 := by simp [φ, h7]
            exact h5 h8
          exact h6
        exact hsupp.mono h1
      have hφ_bound : ∀ x, |φ x| ≤ 1 := by
        intro x
        have h4 : |φ x| = |ψ x| / C := by
          simp [φ, abs_div, abs_of_pos hC_pos] <;> ring
        rw [h4]
        have h5 : |ψ x| ≤ C := hC_bound x
        have h6 : |ψ x| / C ≤ 1 := by
          calc |ψ x| / C ≤ C / C := by gcongr
            _ = 1 := by field_simp [hC_pos.ne'] <;> ring
        exact h6
      let testφ : TestScalar :=
        { toFun := φ, smooth := hφ_smooth, compact := hφ_supp, bound := hφ_bound }
      have h7 : ENNReal.ofReal |∫ x in S, fderiv ℝ φ x v| ≤ directionalVariation S v :=
        le_iSup (fun (θ : TestScalar) => ENNReal.ofReal |∫ x in S, fderiv ℝ θ.toFun x v|) testφ
      rw [h] at h7
      have h8 : ENNReal.ofReal |∫ x in S, fderiv ℝ φ x v| = 0 := by simpa using h7
      have h9 : |∫ x in S, fderiv ℝ φ x v| = 0 := by
        simpa [ENNReal.ofReal_eq_zero] using h8
      have h10 : ∫ x in S, fderiv ℝ φ x v = 0 := by simpa [abs_eq_zero] using h9
      have h11 : ∀ x, fderiv ℝ φ x v = (1 / C) * fderiv ℝ ψ x v := by
        intro x
        have h12 : φ = fun y => (1 / C) * ψ y := by funext y; simp [φ]; ring
        rw [h12]
        have h_eq_fun : (fun y : E n => (1 / C) * ψ y) = (1 / C) • ψ := by
          funext y; simp [smul_eq_mul] <;> ring
        rw [h_eq_fun]
        have hdiff : DifferentiableAt ℝ ψ x := (hψ.differentiable (by norm_num)).differentiableAt
        have h_fd : HasFDerivAt ψ (fderiv ℝ ψ x) x := hdiff.hasFDerivAt
        have h_fd2 : HasFDerivAt ((1 / C) • ψ) ((1 / C) • fderiv ℝ ψ x) x := h_fd.const_smul (1 / C)
        have h13 : fderiv ℝ ((1 / C) • ψ) x = (1 / C) • fderiv ℝ ψ x := h_fd2.fderiv
        rw [h13] <;> simp [smul_eq_mul] <;> ring
      have h14 : ∫ x in S, fderiv ℝ φ x v = (1 / C) * ∫ x in S, fderiv ℝ ψ x v := by
        have h15 : ∀ᵐ x ∂volume.restrict S, fderiv ℝ φ x v = (1 / C) * fderiv ℝ ψ x v :=
          ae_of_all _ h11
        rw [integral_congr_ae h15, integral_const_mul]
      rw [h14] at h10
      have h16 : (1 / C) ≠ 0 := by positivity
      exact (mul_eq_zero.mp h10).resolve_left h16
  · intro h
    rw [directionalVariation]; apply iSup_eq_zero.mpr
    intro φ; have h1 := h φ.toFun φ.smooth φ.compact; simp [h1]

-- ============================================================================
-- Lemma 2: Zero directional variation implies translation invariance
-- ============================================================================

/-- `HasCompactSupport` is preserved by composition with a homeomorphism. -/
lemma hasCompactSupport_comp_homeomorph {ψ : E n → ℝ} (hsupp : HasCompactSupport ψ)
    (g : E n ≃ₜ E n) : HasCompactSupport (ψ ∘ g) := by
  have h1 : Function.support (ψ ∘ g) ⊆ g ⁻¹' tsupport ψ := by
    intro x hx
    have h2 : ψ (g x) ≠ 0 := hx
    have h3 : g x ∈ Function.support ψ := by simpa [Function.mem_support] using h2
    have h4 : g x ∈ tsupport ψ := subset_closure h3
    exact h4
  have h5 : tsupport (ψ ∘ g) ⊆ g ⁻¹' tsupport ψ :=
    closure_minimal h1 (hsupp.isClosed.preimage g.continuous)
  have hsupp' : IsCompact (tsupport ψ) := hsupp
  have h6 : IsCompact (g ⁻¹' tsupport ψ) := by
    have h_eq1 : g ⁻¹' tsupport ψ = g.symm '' tsupport ψ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx
        refine ⟨g x, hx, ?_⟩
        simp
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [h_eq1]
    exact hsupp'.image g.symm.continuous
  exact IsCompact.of_isClosed_subset h6 (isClosed_tsupport _) h5

/-- `directionalVariation` is even in the direction vector. -/
lemma directionalVariation_neg' {S : Set (E n)} {v : E n} :
    directionalVariation S (-v) = directionalVariation S v := by
  have h1 : ∀ (φ : TestScalar),
      ENNReal.ofReal |∫ x in S, (fderiv ℝ φ.toFun x) (-v)| =
      ENNReal.ofReal |∫ x in S, (fderiv ℝ φ.toFun x) v| := by
    intro φ
    have h2 : ∀ x, (fderiv ℝ φ.toFun x) (-v) = -(fderiv ℝ φ.toFun x) v := by
      intro x
      exact (fderiv ℝ φ.toFun x).map_neg v
    have h3 : ∫ x in S, (fderiv ℝ φ.toFun x) (-v) = -∫ x in S, (fderiv ℝ φ.toFun x) v := by
      have h4 : ∫ x in S, (fderiv ℝ φ.toFun x) (-v) = ∫ x in S, -(fderiv ℝ φ.toFun x) v := by
        apply integral_congr_ae; filter_upwards with x; exact h2 x
      rw [h4, integral_neg]
    rw [h3, abs_neg]
  apply iSup_congr
  intro φ; exact h1 φ

/-- FTC for `ψ(x + s•v)` as a function of `s`. -/
lemma ftc_directional (ψ : E n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (v : E n) (x : E n) (t : ℝ) :
    ψ (x + t • v) - ψ x = ∫ s in (0 : ℝ)..t, (fderiv ℝ ψ (x + s • v)) v := by
  let g : ℝ → ℝ := fun s => ψ (x + s • v)
  let g' : ℝ → ℝ := fun s => (fderiv ℝ ψ (x + s • v)) v
  have hg_diff : ∀ s, HasDerivAt g (g' s) s := by
    intro s
    have h1 : HasFDerivAt ψ (fderiv ℝ ψ (x + s • v)) (x + s • v) :=
      (hψ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    let l : ℝ →L[ℝ] E n := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
    have hl_eq : (l : ℝ → E n) = (fun s : ℝ => s • v) := by
      funext s; simp [l]
    have h_fd : HasFDerivAt (fun s : ℝ => s • v) l s := by
      rw [←hl_eq]; exact l.hasFDerivAt
    have h_apply : l 1 = v := by simp [l]
    have h21 : HasDerivAt (fun s : ℝ => s • v) v s :=
      h_fd.hasDerivAt |>.congr_deriv h_apply
    have h2 : HasDerivAt (fun s : ℝ => x + s • v) v s := h21.const_add x
    exact h1.comp_hasDerivAt s h2
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt g (g' s) s :=
    fun s _ => hg_diff s
  have h_fderiv_cont : Continuous (fun z : E n => fderiv ℝ ψ z) :=
    hψ.continuous_fderiv (by norm_num)
  have h_comp : Continuous (fun s : ℝ => x + s • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have h : Continuous (fun s : ℝ => fderiv ℝ ψ (x + s • v)) :=
    h_fderiv_cont.comp h_comp
  have h_eval : Continuous (fun (L : (E n) →L[ℝ] ℝ) => L v) :=
    continuous_eval_const v
  have hg'_cont : Continuous g' := by
    have h5 : Continuous (fun s : ℝ => (fderiv ℝ ψ (x + s • v)) v) := h_eval.comp h
    convert h5 <;> funext s <;> rfl
  have hint : IntervalIntegrable g' volume 0 t := hg'_cont.intervalIntegrable 0 t
  have h_eq : ∫ s in (0 : ℝ)..t, g' s = g t - g 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have h_goal : g t - g 0 = ψ (x + t • v) - ψ x := by
    simp [g] <;> ring
  rw [h_goal] at h_eq
  exact h_eq.symm

/-- The Fréchet derivative is zero outside the topological support. -/
lemma fderiv_zero_outside_tsupport {ψ : E n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {y : E n} (hy : y ∉ tsupport ψ) : fderiv ℝ ψ y = 0 := by
  have h1 : ∀ᶠ (z : E n) in nhds y, ψ z = 0 := by
    have h2 : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport ψ).isOpen_compl
    have h3 : ∀ᶠ (z : E n) in nhds y, z ∈ (tsupport ψ)ᶜ := h2.eventually_mem hy
    filter_upwards [h3] with z hz
    have h6 : z ∉ Function.support ψ := fun h7 => hz (subset_closure h7)
    simpa [Function.mem_support] using h6
  have h_const : HasFDerivAt (fun (_ : E n) => (0 : ℝ)) (0 : (E n) →L[ℝ] ℝ) y :=
    hasFDerivAt_const (0 : ℝ) y
  have h3 : HasFDerivAt ψ (0 : (E n) →L[ℝ] ℝ) y :=
    h_const.congr_of_eventuallyEq h1
  exact h3.fderiv

/-- Given smooth compactly supported `ψ` and `t ≥ 0`, the function
`f(s,x) = (fderiv ψ (x+s•w)) w` is integrable w.r.t. the product measure
`(volume.restrict (uIoc 0 t)).prod (volume.restrict S)`. -/
lemma directional_fubini_integrable
    {S : Set (E n)} {w : E n} (hS : MeasurableSet S)
    {ψ : E n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hsupp : HasCompactSupport ψ)
    {t : ℝ} (ht : 0 ≤ t) :
    let f : ℝ → E n → ℝ := fun s x => (fderiv ℝ ψ (x + s • w)) w
    Integrable (Function.uncurry f)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (volume.restrict S)) := by
  let f : ℝ → E n → ℝ := fun s x => (fderiv ℝ ψ (x + s • w)) w
  let μ := volume.restrict (Set.uIoc (0 : ℝ) t)
  let ν := volume.restrict S
  let K : Set (E n) := {x | ∃ s ∈ Set.Icc (0 : ℝ) t, x + s • w ∈ tsupport ψ}
  have hK_compact : IsCompact K := by
    let C : Set (E n × ℝ) := (tsupport ψ) ×ˢ (Set.Icc (0 : ℝ) t)
    have hC_compact : IsCompact C := hsupp.prod isCompact_Icc
    let F : E n × ℝ → E n := fun p => p.1 - p.2 • w
    have hF_cont : Continuous F := by fun_prop
    have hK_eq : K = F '' C := by
      ext x
      simp only [K, C, F, Set.mem_image, Set.mem_prod]
      constructor
      · rintro ⟨s, hs, hx⟩
        exact ⟨(x + s • w, s), ⟨hx, hs⟩, by simp [F] <;> abel⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.2, hp.2, by simpa [F] using hp.1⟩
    rw [hK_eq]; exact hC_compact.image hF_cont
  have h_f_zero : ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) t → ∀ (x : E n), x ∉ K → f s x = 0 := by
    intro s hs x hx
    have h6 : x + s • w ∉ tsupport ψ := by intro h7; exact hx ⟨s, hs, h7⟩
    have h7 : fderiv ℝ ψ (x + s • w) = 0 := fderiv_zero_outside_tsupport hψ h6
    simpa [f] using congr_arg (fun L : (E n) →L[ℝ] ℝ => L w) h7
  have h_uncurry_cont : Continuous (Function.uncurry f) := by
    have h_fderiv_cont : Continuous (fun z : E n => fderiv ℝ ψ z) :=
      hψ.continuous_fderiv (by norm_num)
    have h_add_cont : Continuous (fun p : ℝ × E n => p.2 + p.1 • w) := by fun_prop
    have h1 : Continuous (fun p : ℝ × E n => fderiv ℝ ψ (p.2 + p.1 • w)) :=
      h_fderiv_cont.comp h_add_cont
    have h_eval : Continuous (fun (L : (E n) →L[ℝ] ℝ) => L w) := continuous_eval_const w
    exact h_eval.comp h1
  let A : Set (ℝ × E n) := (Set.Icc (0 : ℝ) t) ×ˢ K
  have hA_compact : IsCompact A := isCompact_Icc.prod hK_compact
  have hA_meas : MeasurableSet A := hA_compact.measurableSet
  have h_int_on : IntegrableOn (Function.uncurry f) A (μ.prod ν) :=
    ContinuousOn.integrableOn_compact' hA_compact hA_meas h_uncurry_cont.continuousOn
  have h4 : μ ((Set.Icc (0 : ℝ) t)ᶜ) = 0 := by
    rw [Measure.restrict_apply (isCompact_Icc.measurableSet.compl)]
    have h5 : (Set.Icc (0 : ℝ) t)ᶜ ∩ Set.uIoc (0 : ℝ) t = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      have h6 : x ∈ Set.uIoc (0 : ℝ) t := h.2
      have h7 : x ∈ Set.uIcc (0 : ℝ) t := Set.uIoc_subset_uIcc h6
      have h8 : x ∈ Set.Icc (0 : ℝ) t := by
        have h9 : Set.uIcc (0 : ℝ) t = Set.Icc (0 : ℝ) t := by
          rw [Set.uIcc_of_le (show (0 : ℝ) ≤ t from ht)]
        rw [h9] at h7
        exact h7
      exact h.1 h8
    rw [h5]; simp
  have h_null : (μ.prod ν) ((Set.Icc (0 : ℝ) t)ᶜ ×ˢ Set.univ) = 0 := by
    rw [Measure.prod_prod] <;> simp [h4] <;> tauto
  have h_bad_subset : {p : ℝ × E n | p ∉ A ∧ Function.uncurry f p ≠ 0} ⊆
      (Set.Icc (0 : ℝ) t)ᶜ ×ˢ Set.univ := by
    intro p hp
    have h1 : p ∉ A := hp.1
    have h2 : Function.uncurry f p ≠ 0 := hp.2
    by_cases h3 : p.1 ∈ Set.Icc (0 : ℝ) t
    · have h4 : p.2 ∉ K := by intro h5; exact h1 ⟨h3, h5⟩
      have h5 : Function.uncurry f p = 0 := h_f_zero p.1 h3 p.2 h4
      exact False.elim (h2 h5)
    · exact ⟨h3, trivial⟩
  have h_null3 : (μ.prod ν) {p : ℝ × E n | p ∉ A ∧ Function.uncurry f p ≠ 0} = 0 :=
    measure_mono_null h_bad_subset h_null
  have h_ae_outside : ∀ᵐ (p : ℝ × E n) ∂(μ.prod ν), p ∉ A → Function.uncurry f p = 0 := by
    simpa [ae_iff] using h_null3
  exact h_int_on.integrable_of_ae_notMem_eq_zero h_ae_outside

/-- If all directional derivative integrals vanish in direction `w`, then
for `t ≥ 0`, `∫_S ψ(x+t•w) = ∫_S ψ(x)`. -/
lemma core_integral_translation
    {S : Set (E n)} {w : E n} (hS : MeasurableSet S)
    (h_zero : ∀ (ψ : E n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x in S, (fderiv ℝ ψ x) w = 0)
    {t : ℝ} (ht : 0 ≤ t)
    {ψ : E n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hsupp : HasCompactSupport ψ) :
    ∫ x in S, ψ (x + t • w) = ∫ x in S, ψ x := by
  let f : ℝ → E n → ℝ := fun s x => (fderiv ℝ ψ (x + s • w)) w
  have h_int := directional_fubini_integrable (w := w) hS hψ hsupp ht
  have h_fubini : ∫ s in (0 : ℝ)..t, ∫ x in S, f s x =
      ∫ x in S, ∫ s in (0 : ℝ)..t, f s x :=
    intervalIntegral_integral_swap h_int
  have h_inner_zero : ∀ s ∈ Set.uIcc (0 : ℝ) t, ∫ x in S, f s x = 0 := by
    intro s _
    let φ : E n → ℝ := fun y => ψ (y + s • w)
    have hφ_smooth : ContDiff ℝ ∞ φ := by
      have h_c : ContDiff ℝ ∞ (fun (_ : E n) => s • w) := by
        simpa using contDiff_const
      have h_add : ContDiff ℝ ∞ (fun y : E n => y + s • w) :=
        contDiff_id.add h_c
      exact hψ.comp h_add
    have hφ_supp : HasCompactSupport φ :=
      hasCompactSupport_comp_homeomorph hsupp (Homeomorph.addRight (s • w))
    have h_eq1 : ∀ x, (fderiv ℝ φ x) w = f s x := by
      intro x
      have h_fd : HasFDerivAt ψ (fderiv ℝ ψ (x + s • w)) (x + s • w) :=
        (hψ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
      have h2 : HasFDerivAt (fun y : E n => y + s • w) (ContinuousLinearMap.id ℝ (E n)) x := by
        exact (hasFDerivAt_id x).add_const (s • w)
      have h3 : HasFDerivAt φ (fderiv ℝ ψ (x + s • w)) x := h_fd.comp x h2
      have h4 : fderiv ℝ φ x = fderiv ℝ ψ (x + s • w) := h3.fderiv
      rw [h4] <;> rfl
    have h5 : ∫ x in S, (fderiv ℝ φ x) w = 0 := h_zero φ hφ_smooth hφ_supp
    have h6 : ∫ x in S, f s x = ∫ x in S, (fderiv ℝ φ x) w := by
      apply integral_congr_ae
      filter_upwards with x
      exact (h_eq1 x).symm
    rw [h6, h5]
  have h_lhs : ∫ s in (0 : ℝ)..t, ∫ x in S, f s x = 0 := by
    rw [intervalIntegral.integral_congr h_inner_zero] <;> simp
  have h_ftc : ∀ x, ψ (x + t • w) - ψ x = ∫ s in (0 : ℝ)..t, f s x :=
    fun x => ftc_directional ψ hψ w x t
  have h_int_ψ : IntegrableOn ψ S volume :=
    hψ.continuous.integrable_of_hasCompactSupport hsupp |>.integrableOn
  have h_int_ψt : IntegrableOn (fun x : E n => ψ (x + t • w)) S volume := by
    have h_cont : Continuous (fun x : E n => ψ (x + t • w)) := hψ.continuous.comp (by fun_prop)
    have h_supp2 : HasCompactSupport (fun x : E n => ψ (x + t • w)) :=
      hasCompactSupport_comp_homeomorph hsupp (Homeomorph.addRight (t • w))
    exact h_cont.integrable_of_hasCompactSupport h_supp2 |>.integrableOn
  let H : E n → ℝ := fun x => ∫ s in (0 : ℝ)..t, f s x
  let K : Set (E n) := {x | ∃ s ∈ Set.Icc (0 : ℝ) t, x + s • w ∈ tsupport ψ}
  have hK_compact : IsCompact K := by
    let C : Set (E n × ℝ) := (tsupport ψ) ×ˢ (Set.Icc (0 : ℝ) t)
    have hC_compact : IsCompact C := hsupp.prod isCompact_Icc
    let Fmap : E n × ℝ → E n := fun p => p.1 - p.2 • w
    have hF_cont : Continuous Fmap := by fun_prop
    have hK_eq : K = Fmap '' C := by
      ext x
      simp only [K, C, Fmap, Set.mem_image, Set.mem_prod]
      <;> constructor
      · rintro ⟨s, hs, hx⟩
        exact ⟨(x + s • w, s), ⟨hx, hs⟩, by simp [Fmap] <;> abel⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.2, hp.2, by simpa [Fmap] using hp.1⟩
    rw [hK_eq]; exact hC_compact.image hF_cont
  have h_f_zero_K : ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) t → ∀ (x : E n), x ∉ K → f s x = 0 := by
    intro s hs x hx
    have h6 : x + s • w ∉ tsupport ψ := by intro h7; exact hx ⟨s, hs, h7⟩
    have h7 : fderiv ℝ ψ (x + s • w) = 0 := fderiv_zero_outside_tsupport hψ h6
    simpa [f] using congr_arg (fun L : (E n) →L[ℝ] ℝ => L w) h7
  have h_uncurry_cont : Continuous (Function.uncurry f) := by
    have h_fderiv_cont : Continuous (fun z : E n => fderiv ℝ ψ z) :=
      hψ.continuous_fderiv (by norm_num)
    have h_add_cont : Continuous (fun p : ℝ × E n => p.2 + p.1 • w) := by fun_prop
    have h1 : Continuous (fun p : ℝ × E n => fderiv ℝ ψ (p.2 + p.1 • w)) :=
      h_fderiv_cont.comp h_add_cont
    have h_eval : Continuous (fun (L : (E n) →L[ℝ] ℝ) => L w) := continuous_eval_const w
    exact h_eval.comp h1
  let A : Set (ℝ × E n) := (Set.Icc (0 : ℝ) t) ×ˢ K
  have hA_compact : IsCompact A := isCompact_Icc.prod hK_compact
  let nrm : ℝ × E n → ℝ := fun p => ‖Function.uncurry f p‖
  have h_norm_cont : Continuous nrm := h_uncurry_cont.norm
  have h_image_compact : IsCompact (nrm '' A) := hA_compact.image h_norm_cont
  have h_bdd : BddAbove (nrm '' A) := h_image_compact.bddAbove
  rcases h_bdd with ⟨M, hM⟩
  let M' := max M 0
  have hM' : ∀ y ∈ nrm '' A, y ≤ M' := by
    intro y hy
    have h : y ≤ M := by exact hM (hy)
    exact le_trans h (le_max_left M 0)
  have h_bound_all : ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) t → ∀ (x : E n), ‖f s x‖ ≤ M' := by
    intro s hs x
    by_cases hx : x ∈ K
    · have h9 : nrm (s, x) ∈ nrm '' A := by
        exact ⟨(s, x), ⟨hs, hx⟩, rfl⟩
      exact hM' (nrm (s, x)) h9
    · have h7 : f s x = 0 := h_f_zero_K s hs x hx
      rw [h7]
      have h0 : (0 : ℝ) ≤ M' := le_max_right M 0
      simpa using h0
  have hH_cont : Continuous H := by
    let F : E n → ℝ → ℝ := fun x s => f s x
    have hF_meas : ∀ (x : E n), AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
      intro x
      have h_cont : Continuous (fun s : ℝ => (s, x)) := by fun_prop
      have h_comp : Continuous (fun s : ℝ => f s x) := h_uncurry_cont.comp h_cont
      exact h_comp.aestronglyMeasurable
    have h_bound2 : ∀ (x : E n), ∀ᵐ (s : ℝ) ∂volume, s ∈ Set.uIoc (0 : ℝ) t → ‖F x s‖ ≤ M' := by
      intro x; filter_upwards with s; intro hs
      have hs_uIcc : s ∈ Set.uIcc (0 : ℝ) t := Set.uIoc_subset_uIcc hs
      have h_eq : Set.uIcc (0 : ℝ) t = Set.Icc (0 : ℝ) t := Set.uIcc_of_le ht
      have hs' : s ∈ Set.Icc (0 : ℝ) t := by
        rw [h_eq] at hs_uIcc
        exact hs_uIcc
      exact h_bound_all s hs' x
    have h_bound_int : IntervalIntegrable (fun _ : ℝ => M') volume 0 t :=
      continuous_const.intervalIntegrable 0 t
    have h_cont2 : ∀ᵐ (s : ℝ) ∂volume, s ∈ Set.uIoc (0 : ℝ) t → Continuous (fun x : E n => F x s) := by
      filter_upwards with s; intro _
      have h_map : Continuous (fun x : E n => (s, x)) := by fun_prop
      exact h_uncurry_cont.comp h_map
    exact intervalIntegral.continuous_of_dominated_interval hF_meas h_bound2 h_bound_int h_cont2
  have hH_supp : HasCompactSupport H := by
    have h1 : ∀ x, x ∉ K → H x = 0 := by
      intro x hx
      have h2 : ∀ s ∈ Set.uIcc (0 : ℝ) t, f s x = 0 := by
        intro s hs
        have h3 : x + s • w ∉ tsupport ψ := by
          intro h4
          have h5 : s ∈ Set.Icc (0 : ℝ) t := by
            have h_eq : Set.uIcc (0 : ℝ) t = Set.Icc (0 : ℝ) t := Set.uIcc_of_le ht
            rw [h_eq] at hs
            exact hs
          exact hx ⟨s, h5, h4⟩
        have h4 : fderiv ℝ ψ (x + s • w) = 0 := fderiv_zero_outside_tsupport hψ h3
        simpa [f] using congr_arg (fun L : (E n) →L[ℝ] ℝ => L w) h4
      dsimp only [H]
      rw [intervalIntegral.integral_congr h2] <;> simp
    have h3 : Function.support H ⊆ K := by
      intro x hx; by_contra h4; have h5 : H x = 0 := h1 x h4; exact hx h5
    have h4 : tsupport H ⊆ K := closure_minimal h3 hK_compact.isClosed
    exact IsCompact.of_isClosed_subset hK_compact (isClosed_tsupport H) h4
  have h_int_H : IntegrableOn H S volume :=
    hH_cont.integrable_of_hasCompactSupport hH_supp |>.integrableOn
  have h_integral_eq : ∫ x in S, (ψ (x + t • w) - ψ x) = ∫ x in S, H x := by
    apply integral_congr_ae
    filter_upwards with x
    exact h_ftc x
  have h_main : ∫ x in S, H x = 0 := by
    rw [←h_fubini, h_lhs]
  have h_sub : ∫ x in S, (ψ (x + t • w) - ψ x) =
      (∫ x in S, ψ (x + t • w)) - (∫ x in S, ψ x) :=
    integral_sub h_int_ψt h_int_ψ
  have h_final : (∫ x in S, ψ (x + t • w)) - (∫ x in S, ψ x) = 0 := by
    calc
      (∫ x in S, ψ (x + t • w)) - (∫ x in S, ψ x)
        = ∫ x in S, (ψ (x + t • w) - ψ x) := h_sub.symm
      _ = ∫ x in S, H x := h_integral_eq
      _ = 0 := h_main
  exact sub_eq_zero.mp h_final

/-- If `directionalVariation S v = 0`, then `S` is a.e. invariant under
translation by `t • v` for every `t : ℝ`.

**Proof** (Maggi pp. 173-174):
For any smooth compactly supported ψ and t ≥ 0, the FTC gives
`ψ(x + t•v) - ψ(x) = ∫_0^t ∂_v ψ(x + s•v) ds`.
Integrating over S and applying Fubini (justified since the integrand is
continuous and compactly supported in x for s ∈ [0,t]):
`∫_S (ψ(x+t•v) - ψ(x)) dx = ∫_0^t ∫_S ∂_v ψ(x+s•v) dx ds`.
For each s, `φ_s(x) := ψ(x+s•v)` is smooth compactly supported, so
`∫_S ∂_v φ_s = 0` by `directionalVariation_zero_iff`. Hence the RHS is 0.
By change of variables, `∫_{S+t•v} ψ = ∫_S ψ(x+t•v) = ∫_S ψ`.
Since this holds for all test ψ, `ae_eq_of_integral_contDiff_smul_eq` gives
`χ_{S+t•v} =ᵐ χ_S`. For t < 0, apply the same argument to -v. -/
theorem zero_directionalVariation_translation_invariant
    {S : Set (E n)} {v : E n} (hS : MeasurableSet S)
    (h : directionalVariation S v = 0) :
    ∀ (t : ℝ), (translateSet S (t • v)) =ᵐ[volume] S := by
  have h_iff := directionalVariation_zero_iff (hS := hS) (v := v)
  have h_zero_v := h_iff.mp h
  have h_neg : directionalVariation S (-v) = 0 := by
    rw [directionalVariation_neg', h]
  have h_iff_neg := directionalVariation_zero_iff (hS := hS) (v := -v)
  have h_zero_neg := h_iff_neg.mp h_neg
  have h_all_t : ∀ (t : ℝ) (ψ : E n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x in S, ψ (x + t • v) = ∫ x in S, ψ x := by
    intro t ψ hψ hsupp
    by_cases ht : 0 ≤ t
    · exact core_integral_translation hS h_zero_v ht hψ hsupp
    · have ht' : 0 ≤ -t := by linarith
      have h1 := core_integral_translation hS h_zero_neg ht' hψ hsupp
      have h2 : (-t) • (-v) = t • v := by
        simp [smul_neg, neg_smul]
      simpa [h2] using h1
  have h_transl_int : ∀ (t : ℝ) (ψ : E n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x in translateSet S (t • v), ψ x = ∫ x in S, ψ x := by
    intro t ψ hψ hsupp
    let g : E n → E n := fun x => x + t • v
    have hg_cont : Continuous g := by fun_prop
    have hg_mp : MeasurePreserving g volume volume := measurePreserving_add_right volume (t • v)
    have hg_inj : Function.Injective g := by intro x y h; simpa [g] using h
    have h_meas : MeasurableEmbedding g :=
      hg_cont.measurable.measurableEmbedding hg_inj
    have h_preimage : g ⁻¹' (g '' S) = S := hg_inj.preimage_image S
    have h_eq : ∫ x in g ⁻¹' (g '' S), ψ (g x) = ∫ y in g '' S, ψ y :=
      hg_mp.setIntegral_preimage_emb h_meas ψ (g '' S)
    have h_image : translateSet S (t • v) = g '' S := by rfl
    have h_final1 : ∫ x in S, ψ (g x) = ∫ y in g '' S, ψ y := by
      rw [h_preimage] at h_eq
      exact h_eq
    have h_all_t' : ∫ x in S, ψ (g x) = ∫ x in S, ψ x := h_all_t t ψ hψ hsupp
    have h6 : ∫ y in g '' S, ψ y = ∫ x in S, ψ (g x) := h_final1.symm
    have h7 : ∫ y in g '' S, ψ y = ∫ x in S, ψ x := Eq.trans h6 h_all_t'
    rw [h_image]
    exact h7
  intro t
  let χ1 : E n → ℝ := Set.indicator (translateSet S (t • v)) (fun _ => (1 : ℝ))
  let χ2 : E n → ℝ := Set.indicator S (fun _ => (1 : ℝ))
  have hS_trans : MeasurableSet (translateSet S (t • v)) := by
    let g : E n → E n := fun x => x + t • v
    have hg_cont : Continuous g := by fun_prop
    have hg_inj : Function.Injective g := by intro x y h; simpa [g] using h
    have h_meas : MeasurableEmbedding g := hg_cont.measurable.measurableEmbedding hg_inj
    exact h_meas.measurableSet_image.mpr hS
  have h1_loc : LocallyIntegrable χ1 volume :=
    (locallyIntegrable_const (1 : ℝ)).indicator hS_trans
  have h2_loc : LocallyIntegrable χ2 volume :=
    (locallyIntegrable_const (1 : ℝ)).indicator hS
  have h_main_eq : ∀ (g : E n → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • χ1 x = ∫ x, g x • χ2 x := by
    intro g hg hgsupp
    have h3 : ∫ x, g x • χ1 x = ∫ x in translateSet S (t • v), g x := by
      have h_eq1 : ∫ x, g x • χ1 x = ∫ x, Set.indicator (translateSet S (t • v)) g x := by
        congr with x
        simp [χ1, smul_eq_mul, Set.indicator_apply]
      rw [h_eq1, integral_indicator hS_trans]
    have h4 : ∫ x, g x • χ2 x = ∫ x in S, g x := by
      have h_eq2 : ∫ x, g x • χ2 x = ∫ x, Set.indicator S g x := by
        congr with x
        simp [χ2, smul_eq_mul, Set.indicator_apply]
      rw [h_eq2, integral_indicator hS]
    rw [h3, h4]
    exact h_transl_int t g hg hgsupp
  have h_ae : ∀ᵐ x ∂volume, χ1 x = χ2 x :=
    ae_eq_of_integral_contDiff_smul_eq h1_loc h2_loc (fun g hg hgsupp => h_main_eq g hg hgsupp)
  have h_ae2 : ∀ᵐ x ∂volume, x ∈ translateSet S (t • v) ↔ x ∈ S := by
    filter_upwards [h_ae] with x hx
    have h_iff : x ∈ translateSet S (t • v) ↔ x ∈ S := by
      have h_eq : (if x ∈ translateSet S (t • v) then (1 : ℝ) else (0 : ℝ)) =
          (if x ∈ S then (1 : ℝ) else (0 : ℝ)) := by
        simpa [χ1, χ2, Set.indicator_apply] using hx
      constructor
      · intro h_in
        rw [if_pos h_in] at h_eq
        have h : (if x ∈ S then (1 : ℝ) else (0 : ℝ)) = 1 := h_eq.symm
        by_cases hS' : x ∈ S
        · exact hS'
        · rw [if_neg hS'] at h; norm_num at h
      · intro h_in
        rw [if_pos h_in] at h_eq
        have h : (if x ∈ translateSet S (t • v) then (1 : ℝ) else (0 : ℝ)) = 1 := h_eq
        by_cases hS' : x ∈ translateSet S (t • v)
        · exact hS'
        · rw [if_neg hS'] at h; norm_num at h
    exact h_iff
  have h_ae3 : ∀ᵐ x ∂volume, (x ∈ translateSet S (t • v)) = (x ∈ S) := by
    filter_upwards [h_ae2] with x hx; exact propext hx
  exact h_ae3

-- ============================================================================
-- Lemma 3: Cylinder factorization from translation invariance
-- ============================================================================

/-- If `S` is a.e. invariant under every translation in `v⊥`, then
`χ_S` factors a.e. through `inner(·, v)`: there exists a measurable
`g : ℝ → ℝ` such that `∀ᵐ x, (x ∈ S ↔ g(inner x v) = 1)`.

**Proof sketch**: Decompose `E n = ℝ•v ⊕ v⊥` via Fubini. For each
`t ∈ ℝ` and `w ∈ v⊥`, translation invariance gives `χ_S(t•v + w) = χ_S(t•v)`
a.e. in w. Define `g(t) := χ_S(t•v)`. Then Fubini shows
`χ_S(x) = g(inner x v)` a.e. -/
lemma cylinder_factorization {S : Set (E n)} {v : E n}
    (hS : MeasurableSet S) (hv_unit : ‖v‖ = 1)
    (h_transl : ∀ (w : E n), inner ℝ w v = 0 →
      ∀ (t : ℝ), (translateSet S (t • w)) =ᵐ[volume] S) :
    ∃ (g : ℝ → ℝ), Measurable g ∧
      (∀ᵐ (x : E n) ∂volume, (x ∈ S ↔ g (inner ℝ x v) = 1)) := by
  let V : Submodule ℝ (E n) :=
    { carrier := {x | inner ℝ x v = 0}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        have h : inner ℝ (x + y) v = inner ℝ x v + inner ℝ y v := inner_add_left x y v
        have h' : inner ℝ (x + y) v = 0 := by rw [h, hx, hy] <;> norm_num
        exact h'
      smul_mem' := by
        intro c x hx
        have h : inner ℝ (c • x) v = c * inner ℝ x v := inner_smul_left x v c
        have h' : inner ℝ (c • x) v = 0 := by rw [h, hx] <;> ring
        exact h' }

  -- Step 1: For each w ∈ V, χ_S(x + w) = χ_S(x) a.e.
  have h1 : ∀ (w : V), ∀ᵐ (x : E n) ∂volume, (x + (w : E n) ∈ S) ↔ (x ∈ S) := by
    intro w
    have hwV : inner ℝ (w : E n) v = 0 := w.prop
    have h2 := h_transl (w : E n) hwV (-1 : ℝ)
    have h_smul : (-1 : ℝ) • (w : E n) = -(w : E n) := by simp
    rw [h_smul] at h2
    have h3 : ∀ᵐ (x : E n), (x ∈ translateSet S (-(w : E n)) ↔ x ∈ S) := by
      have h2' : Filter.EventuallyEq (ae volume) (translateSet S (-(w : E n))) S := h2
      filter_upwards [h2'] with x hx
      exact ⟨Eq.mp hx, Eq.mpr hx⟩
    have h4 : ∀ (x : E n), x ∈ translateSet S (-(w : E n)) ↔ x + (w : E n) ∈ S := by
      intro x
      unfold translateSet
      simp only [Set.mem_image]
      constructor
      · rintro ⟨y, hy, h_eq⟩
        have h5 : x + (w : E n) = y := by
          calc x + (w : E n)
              = (y + (-(w : E n))) + (w : E n) := by rw [h_eq]
            _ = y + ((-(w : E n)) + (w : E n)) := by rw [add_assoc]
            _ = y + 0 := by simp
            _ = y := by rw [add_zero]
        rw [h5]; exact hy
      · intro hx
        have h_goal : x = (x + (w : E n)) + (-(w : E n)) := by
          calc x
              = x + 0 := by rw [add_zero]
            _ = x + ((w : E n) + (-(w : E n))) := by simp
            _ = (x + (w : E n)) + (-(w : E n)) := by rw [←add_assoc]
        exact ⟨x + (w : E n), hx, h_goal.symm⟩
    filter_upwards [h3] with x hx
    rw [h4 x] at hx
    exact hx

  -- Step 2: Exceptional set has product measure zero by Fubini
  let f_add2 : (V × E n) → E n := fun p => p.2 + (p.1 : E n)
  let f_snd2 : (V × E n) → E n := Prod.snd
  let E_set2 : Set (V × E n) := symmDiff (f_add2 ⁻¹' S) (f_snd2 ⁻¹' S)
  have h_f_add2_meas : Measurable f_add2 := by fun_prop
  have h_f_snd2_meas : Measurable f_snd2 := measurable_snd
  have hE2_meas : MeasurableSet E_set2 :=
    (h_f_add2_meas hS).symmDiff (h_f_snd2_meas hS)

  have h_forall_w : ∀ (w : V), volume {x : E n | (x + (w : E n) ∈ S) ≠ (x ∈ S)} = 0 := by
    intro w
    simpa [ae_iff] using h1 w

  have h_fibers2 : ∀ᵐ (w : V) ∂volume, volume {x : E n | (w, x) ∈ E_set2} = 0 := by
    filter_upwards with w
    have h_eq1 : ∀ (x : E n), (w, x) ∈ E_set2 ↔ (x + (w : E n) ∈ S) ≠ (x ∈ S) := by
      intro x
      simp [E_set2, f_add2, f_snd2, symmDiff] <;> tauto
    have h_set_eq : {x : E n | (w, x) ∈ E_set2} = {x : E n | (x + (w : E n) ∈ S) ≠ (x ∈ S)} := by
      ext x; exact h_eq1 x
    rw [h_set_eq]
    exact h_forall_w w

  have h_volume_eq2 : (volume : Measure (V × E n)) = volume.prod volume :=
    MeasureTheory.Measure.volume_eq_prod V (E n)
  have hE2_null : volume E_set2 = 0 := by
    rw [h_volume_eq2]
    exact (MeasureTheory.Measure.measure_prod_null hE2_meas).mpr h_fibers2

  -- Swap to E n × V order for the other Fubini direction
  let E_set : Set (E n × V) := Prod.swap ⁻¹' E_set2
  have h_volume_eq1 : (volume : Measure (E n × V)) = volume.prod volume :=
    MeasureTheory.Measure.volume_eq_prod (E n) V
  have h_swap_mp : MeasurePreserving (Prod.swap : (E n × V) → (V × E n)) volume volume := by
    rw [h_volume_eq1, h_volume_eq2]
    exact MeasureTheory.Measure.measurePreserving_swap
  have hE_null : volume E_set = 0 := by
    have h : volume E_set = volume E_set2 :=
      h_swap_mp.measure_preimage hE2_meas.nullMeasurableSet
    rw [h, hE2_null]

  -- Step 3: Fubini — for a.e. x, χ_S(x + w) = χ_S(x) for a.e. w ∈ V
  have h_fiber_eq : ∀ (x : E n), {w : V | (x + (w : E n) ∈ S) ≠ (x ∈ S)} = Prod.mk x ⁻¹' E_set := by
    intro x
    ext w
    simp [E_set, E_set2, f_add2, f_snd2, symmDiff] <;> tauto
  have h5 : ∀ᵐ (x : E n) ∂volume, volume (Prod.mk x ⁻¹' E_set) = 0 := by
    rw [h_volume_eq1] at hE_null
    exact MeasureTheory.Measure.measure_ae_null_of_prod_null hE_null
  have h4 : (fun x : E n => volume {w : V | (x + (w : E n) ∈ S) ≠ (x ∈ S)}) =ᵐ[volume] 0 := by
    have h6 : (fun x : E n => volume (Prod.mk x ⁻¹' E_set)) =ᵐ[volume] 0 := h5
    have h7 : (fun x : E n => volume {w : V | (x + (w : E n) ∈ S) ≠ (x ∈ S)}) =
             (fun x : E n => volume (Prod.mk x ⁻¹' E_set)) := by
      funext x; rw [h_fiber_eq x]
    rw [h7]; exact h6
  have h3 : ∀ᵐ (x : E n) ∂volume,
      ∀ᵐ (w : V) ∂volume, (x + (w : E n) ∈ S) ↔ (x ∈ S) := by
    have h4' : ∀ᵐ (x : E n) ∂volume, volume {w : V | (x + (w : E n) ∈ S) ≠ (x ∈ S)} = 0 := by
      simpa [Filter.EventuallyEq] using h4
    filter_upwards [h4'] with x hx
    have h_set_eq : {w : V | (x + (w : E n) ∈ S) ≠ (x ∈ S)} =
                    {w : V | ¬((x + (w : E n) ∈ S) ↔ (x ∈ S))} := by
      ext w; simp [not_iff] <;> tauto
    have h_ae : ∀ᵐ (w : V) ∂volume, (x + (w : E n) ∈ S) ↔ (x ∈ S) := by
      rw [ae_iff, ←h_set_eq]
      exact hx
    exact h_ae

  -- Step 4: Define g(s) and prove it measurable
  let f_s : ℝ → V → E n := fun s w => s • v + (w : E n)
  let A : ℝ → Set V := fun s => (f_s s) ⁻¹' S
  have h_fs_meas : ∀ s, Measurable (f_s s) := by intro s; fun_prop
  have hA_meas : ∀ s, MeasurableSet (A s) := by
    intro s; exact h_fs_meas s hS
  let E_all : Set (ℝ × V) := {p | (p.1 • v + (p.2 : E n)) ∈ S}
  have h_E_all_meas : MeasurableSet E_all := by
    have h : Measurable (fun p : ℝ × V => p.1 • v + (p.2 : E n)) := by fun_prop
    exact h hS
  let E_all_compl : Set (ℝ × V) := E_allᶜ
  have h_E_all_compl_meas : MeasurableSet E_all_compl := h_E_all_meas.compl
  have h_vol_meas : Measurable fun s : ℝ => volume (A s) :=
    measurable_measure_prodMk_left h_E_all_meas
  have h_compl_vol_meas : Measurable fun s : ℝ => volume (A s)ᶜ :=
    measurable_measure_prodMk_left h_E_all_compl_meas
  have h_pred_set : MeasurableSet {s : ℝ | volume (A s)ᶜ = 0} :=
    h_compl_vol_meas (MeasurableSet.singleton 0)
  let g : ℝ → ℝ := Set.indicator {s | volume (A s)ᶜ = 0} (fun (_ : ℝ) => (1 : ℝ))
  have h_one_meas : Measurable (fun (_ : ℝ) => (1 : ℝ)) := measurable_const
  have hg_meas : Measurable g := h_one_meas.indicator h_pred_set

  -- Step 5: For a.e. x, (x ∈ S ↔ g(inner x v) = 1)
  have h_final : ∀ᵐ (x : E n) ∂volume, (x ∈ S ↔ g (inner ℝ x v) = 1) := by
    filter_upwards [h3] with x hx
    set s : ℝ := inner ℝ x v with hs
    have h_x_decomp : x = s • v + (x - s • v) := by abel
    have h_inner : inner ℝ (x - s • v) v = 0 := by
      have h1 : inner ℝ (x - s • v) v = inner ℝ x v - inner ℝ (s • v) v := by
        rw [inner_sub_left]
      have h2 : inner ℝ (s • v) v = s * inner ℝ v v := by
        rw [inner_smul_left] <;> simp
      have h3 : inner ℝ v v = (‖v‖ : ℝ) ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K] <;> norm_cast
      have h4 : inner ℝ (s • v) v = s := by
        rw [h2, h3, hv_unit] <;> ring
      rw [h1, h4]
      have h5 : inner ℝ x v = s := by rfl
      rw [h5] <;> ring
    let u₀ : V := ⟨x - s • v, h_inner⟩
    have h5 : ∀ᵐ (w : V) ∂volume, (x + (w : E n) ∈ S) ↔ (x ∈ S) := hx

    -- Translation by u₀ on V is measure-preserving
    have h_mp : MeasurePreserving (fun w : V => w + u₀) volume volume :=
      measurePreserving_add_right volume u₀

    have h_eq1 : ∀ (w : V), x + (w : E n) = s • v + (((w + u₀ : V) : E n)) := by
      intro w
      have h_ua : (u₀ : E n) = x - s • v := by rfl
      have h_sub : ((w + u₀ : V) : E n) = (w : E n) + (u₀ : E n) := by
        exact Submodule.coe_add _ _
      calc x + (w : E n)
          = s • v + (u₀ : E n) + (w : E n) := by rw [h_x_decomp, h_ua] <;> abel
        _ = s • v + ((w : E n) + (u₀ : E n)) := by abel
        _ = s • v + (((w + u₀ : V) : E n)) := by rw [h_sub]

    let P_set : Set V := {w | (s • v + ((w : E n)) ∈ S) ↔ (x ∈ S)}
    have hP_meas : MeasurableSet P_set := by
      by_cases hxS2 : x ∈ S
      · have h_eq : P_set = A s := by ext w; simp [P_set, hxS2] <;> tauto
        rw [h_eq]; exact hA_meas s
      · have h_eq : P_set = (A s)ᶜ := by ext w; simp [P_set, hxS2] <;> tauto
        rw [h_eq]; exact (hA_meas s).compl
    let N : Set V := P_setᶜ
    have hN_meas : MeasurableSet N := hP_meas.compl

    have h8 : ∀ᵐ (w : V) ∂volume, (w + u₀) ∈ P_set := by
      filter_upwards [h5] with w hw
      have h9 : x + (w : E n) = s • v + (((w + u₀ : V) : E n)) := h_eq1 w
      rw [h9] at hw
      exact hw
    let N_preimage : Set V := (fun w : V => w + u₀) ⁻¹' N
    have hN_preimage_eq : N_preimage = {w | (w + u₀) ∉ P_set} := by
      ext w; simp [N_preimage, N] <;> rfl
    have h10 : volume N_preimage = 0 := by
      rw [hN_preimage_eq]
      simpa [ae_iff] using h8
    have h11 : volume N_preimage = volume N :=
      h_mp.measure_preimage hN_meas.nullMeasurableSet
    have h12 : volume N = 0 := by
      rw [←h11, h10]
    have h6 : ∀ᵐ (w' : V) ∂volume, w' ∈ P_set := by
      rw [ae_iff]
      exact h12

    by_cases hxS : x ∈ S
    · have h10 : ∀ᵐ (w : V) ∂volume, (s • v + (w : E n)) ∈ S := by
        filter_upwards [h6] with w hw
        exact hw.mpr hxS
      have h11 : volume (A s)ᶜ = 0 := by
        have h12 : (A s)ᶜ = {w : V | (s • v + (w : E n)) ∉ S} := by
          ext w; simp [A, f_s] <;> tauto
        rw [h12]; simpa [ae_iff] using h10
      have h13 : g s = 1 := by
        have h14 : g s = Set.indicator {s : ℝ | volume (A s)ᶜ = 0} (fun (_ : ℝ) => (1 : ℝ)) s := by rfl
        rw [h14]
        simp [Set.indicator_apply, h11]
      rw [h13] <;> simp [hxS]
    · have h10 : ∀ᵐ (w : V) ∂volume, (s • v + (w : E n)) ∉ S := by
        filter_upwards [h6] with w hw
        exact (hw.not).mpr hxS
      have h11 : volume (A s) = 0 := by
        have h12 : A s = {w : V | (s • v + (w : E n)) ∈ S} := by
          ext w; simp [A, f_s] <;> tauto
        rw [h12]; simpa [ae_iff] using h10
      have h_univ_pos : 0 < volume (Set.univ : Set V) := by
        have h : (interior (Set.univ : Set V)).Nonempty := by simp
        exact MeasureTheory.Measure.measure_pos_of_nonempty_interior volume h
      have h12 : volume (A s)ᶜ ≠ 0 := by
        by_contra h13
        have h14 : volume (A s) + volume (A s)ᶜ = volume (Set.univ : Set V) := by
          have h_union : (A s) ∪ (A s)ᶜ = Set.univ := by simp
          have h_disj : Disjoint (A s) (A s)ᶜ := disjoint_compl_right
          rw [← h_union, measure_union h_disj (hA_meas s).compl]
        rw [h11, h13] at h14
        have h15 : volume (Set.univ : Set V) = 0 := by
          have h16 : volume (Set.univ : Set V) = 0 + 0 := h14.symm
          simpa using h16
        exact h_univ_pos.ne' h15
      have h13 : g s = 0 := by
        have h14 : g s = Set.indicator {s : ℝ | volume (A s)ᶜ = 0} (fun (_ : ℝ) => (1 : ℝ)) s := by rfl
        rw [h14]
        simp [Set.indicator_apply, h12]
      rw [h13] <;> simp [hxS]

  exact ⟨g, hg_meas, h_final⟩

-- ============================================================================
-- Lemma 4: Classification of monotone {0,1}-valued functions on ℝ
-- ============================================================================

/-- A non-increasing function `g : ℝ → ℝ` taking values in `{0,1}` is
pointwise equal to `1_{(-∞, α)}` except possibly at `α`, or identically 0,
or identically 1. -/
lemma monotone_bool_function_classification
    {g : ℝ → ℝ} (_hg_meas : Measurable g)
    (hg_values : ∀ t, g t = 0 ∨ g t = 1)
    (hg_decr : ∀ s t, s ≤ t → g t ≤ g s) :
    (∃ (α : ℝ), ∀ (t : ℝ), t ≠ α →
      g t = Set.indicator (Set.Iio α) (fun _ => (1 : ℝ)) t) ∨
    (∀ t, g t = 0) ∨
    (∀ t, g t = 1) := by
  by_cases h_all_zero : (∀ t, g t = 0)
  · exact Or.inr (Or.inl h_all_zero)
  · have h_exists_one : ∃ t0, g t0 = 1 := by
      have h : ∃ t0, g t0 ≠ 0 := by
        by_contra h'; push Not at h'; exact h_all_zero h'
      rcases h with ⟨t0, hne⟩
      have h1 : g t0 = 1 := (hg_values t0).resolve_left hne
      exact ⟨t0, h1⟩
    rcases h_exists_one with ⟨t0, ht0⟩
    by_cases h_all_one : (∀ t, g t = 1)
    · exact Or.inr (Or.inr h_all_one)
    · have h_exists_zero : ∃ t1, g t1 = 0 := by
        have h : ∃ t1, g t1 ≠ 1 := by
          by_contra h'; push Not at h'; exact h_all_one h'
        rcases h with ⟨t1, hne⟩
        have h1 : g t1 = 0 := (hg_values t1).resolve_right hne
        exact ⟨t1, h1⟩
      rcases h_exists_zero with ⟨t1, ht1⟩
      have h_t0_lt_t1 : t0 < t1 := by
        by_contra h
        have h' : t1 ≤ t0 := by linarith
        have h'' : g t0 ≤ g t1 := hg_decr t1 t0 h'
        rw [ht0, ht1] at h'' <;> linarith
      let S : Set ℝ := {t | g t = 0}
      have hS_nonempty : S.Nonempty := ⟨t1, ht1⟩
      have h_t0_lower : ∀ x ∈ S, t0 ≤ x := by
        intro x hx
        have hgx : g x = 0 := hx
        by_contra h2
        have h3 : x < t0 := by linarith
        have h4 : g t0 ≤ g x := hg_decr x t0 (by linarith)
        rw [ht0, hgx] at h4 <;> linarith
      have hS_bdd_below : BddBelow S := ⟨t0, h_t0_lower⟩
      let α : ℝ := sInf S
      have hα_ge_t0 : t0 ≤ α := le_csInf hS_nonempty h_t0_lower
      have hα_le_t1 : α ≤ t1 := csInf_le hS_bdd_below (show t1 ∈ S from ht1)
      have h_below : ∀ t < α, g t = 1 := by
        intro t ht
        have h_notin : t ∉ S := by
          intro h_in
          have h : α ≤ t := csInf_le hS_bdd_below h_in
          linarith
        have h : g t ≠ 0 := by simpa [S] using h_notin
        exact (hg_values t).resolve_left h
      have h_above : ∀ t > α, g t = 0 := by
        intro t ht
        by_contra h
        have h' : g t = 1 := (hg_values t).resolve_left h
        have h_lower : ∀ s ∈ S, t ≤ s := by
          intro s hs
          by_contra h2
          have h3 : s < t := by linarith
          have h4 : g t ≤ g s := hg_decr s t (by linarith)
          rw [h', hs] at h4 <;> linarith
        have h5 : α ≥ t := le_csInf hS_nonempty h_lower
        linarith
      have h_main : ∀ t ≠ α, g t = Set.indicator (Set.Iio α) (fun _ => (1 : ℝ)) t := by
        intro t hne
        by_cases h : t < α
        · rw [h_below t h]
          simp [Set.indicator, Set.mem_Iio.mpr h]
        · have hge : α ≤ t := le_of_not_gt h
          have h' : t > α := lt_of_le_of_ne hge hne.symm
          rw [h_above t h']
          have hni : t ∉ Set.Iio α := by simpa [Set.mem_Iio] using hge
          simp [Set.indicator, hni]
      exact Or.inl ⟨α, h_main⟩

-- ============================================================================
-- Helper: non-negative test integrals imply a.e. non-negative (mollification)
-- ============================================================================

/-- If a locally integrable function has non-negative integral against every
smooth compactly supported non-negative test function, then it is non-negative a.e.

Uses mollification by `ContDiffBump` convolution: the convolution with a normed
bump is non-negative by the test-function hypothesis, and converges to the
original function a.e. as the bump support shrinks. -/
lemma ae_nonneg_of_contDiff_test {f : E n → ℝ} (hf : LocallyIntegrable f volume)
    (h : ∀ (φ : E n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, f x * φ x) :
    ∀ᵐ x ∂volume, 0 ≤ f x := by
  let ρ : ℕ → ContDiffBump (0 : E n) := fun k =>
    { rIn := 1 / (k + 2 : ℝ)
      rOut := 2 / (k + 2 : ℝ)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have h_pos : (0 : ℝ) < (k + 2 : ℝ) := by positivity
        gcongr <;> norm_num }
  have h_rOut_def : ∀ k : ℕ, (ρ k).rOut = 2 / (k + 2 : ℝ) := by intro k; rfl
  have h_rIn_def : ∀ k : ℕ, (ρ k).rIn = 1 / (k + 2 : ℝ) := by intro k; rfl
  have h_rOut : Filter.Tendsto (fun k : ℕ => (ρ k).rOut) Filter.atTop (nhds 0) := by
    rw [funext h_rOut_def]
    have h11 : Filter.Tendsto (fun k : ℕ => (k : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have h1 : Filter.Tendsto (fun k : ℕ => (k + 2 : ℝ)) Filter.atTop Filter.atTop := by
      have h_eq : (fun k : ℕ => (k + 2 : ℝ)) = fun k : ℕ => (k : ℝ) + 2 := by
        funext k; simp
      rw [h_eq]
      exact tendsto_atTop_mono (fun n => by linarith) h11
    have h2 : Filter.Tendsto (fun k : ℕ => 2 / (k + 2 : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop h1
    simpa [h_rOut_def] using h2
  have h_ratio : ∀ k : ℕ, (ρ k).rOut ≤ 2 * (ρ k).rIn := by
    intro k
    simp [h_rOut_def, h_rIn_def] <;> ring_nf <;> norm_num
  have h_ae : ∀ᵐ x₀ ∂volume,
      Filter.Tendsto (fun k =>
        MeasureTheory.convolution ((ρ k).normed volume) f
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x₀)
        Filter.atTop (nhds (f x₀)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      h_rOut (by filter_upwards with k; exact h_ratio k) hf
  have h_nonneg : ∀ (k : ℕ) (x₀ : E n),
      0 ≤ MeasureTheory.convolution ((ρ k).normed volume) f
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x₀ := by
    intro k x₀
    let g : E n → ℝ := (ρ k).normed volume
    let φ : E n → ℝ := fun y => g (x₀ - y)
    have hg_smooth : ContDiff ℝ ∞ g := (ρ k).contDiff_normed
    have hg_supp : HasCompactSupport g := (ρ k).hasCompactSupport_normed
    have hg_nonneg : ∀ y, 0 ≤ g y := fun y => (ρ k).nonneg_normed y
    have hφ_smooth : ContDiff ℝ ∞ φ := by
      have h1 : ContDiff ℝ ∞ (fun y : E n => x₀ - y) := by fun_prop
      exact hg_smooth.comp h1
    have hφ_supp : HasCompactSupport φ := by
      let K : Set (E n) := Set.preimage (fun y : E n => x₀ - y) (tsupport g)
      have h_tsupport_compact : IsCompact (tsupport g) := hg_supp
      have hK_compact : IsCompact K := by
        have h_eq : K = (fun y : E n => x₀ - y) '' (tsupport g) := by
          ext y
          simp only [K, Set.mem_preimage, Set.mem_image]
          constructor
          · intro h
            refine ⟨x₀ - y, h, ?_⟩
            simp [sub_sub] <;> abel
          · rintro ⟨z, hz, rfl⟩
            simpa [sub_sub] using hz
        rw [h_eq]
        exact h_tsupport_compact.image (by fun_prop)
      have h1 : Function.support φ ⊆ K := by
        intro y hy
        have h2 : φ y ≠ 0 := hy
        have h3 : g (x₀ - y) ≠ 0 := h2
        have h4 : x₀ - y ∈ Function.support g := h3
        have h5 : x₀ - y ∈ tsupport g := subset_closure h4
        exact h5
      have h2 : ∀ y ∉ K, φ y = 0 := by
        intro y hy
        have h3 : y ∉ Function.support φ := by
          intro h4; exact hy (h1 h4)
        simpa [Function.mem_support] using h3
      exact HasCompactSupport.intro hK_compact h2
    have hφ_nonneg : ∀ y, 0 ≤ φ y := by
      intro y; exact hg_nonneg (x₀ - y)
    have h1 : 0 ≤ ∫ y, f y * φ y := h φ hφ_smooth hφ_supp hφ_nonneg
    have h2 : MeasureTheory.convolution g f (ContinuousLinearMap.lsmul ℝ ℝ) volume x₀ =
        ∫ y, f y * φ y := by
      rw [MeasureTheory.convolution_lsmul_swap]
      apply integral_congr_ae
      filter_upwards with t
      <;> ring
    rw [h2]
    exact h1
  filter_upwards [h_ae] with x₀ hx₀
  let conv : ℕ → ℝ := fun k => MeasureTheory.convolution ((ρ k).normed volume) f
      (ContinuousLinearMap.lsmul ℝ ℝ) volume x₀
  have h3 : ∀ k : ℕ, 0 ≤ conv k := fun k => h_nonneg k x₀
  have h4 : ∀ k, -conv k ≤ (0 : ℝ) := by
    intro k; linarith [h3 k]
  have h5 : Filter.Tendsto (fun k => -conv k) Filter.atTop (nhds (-f x₀)) :=
    hx₀.neg
  have h6 : ∀ᶠ k in Filter.atTop, -conv k ≤ (0 : ℝ) := by
    filter_upwards with k
    exact h4 k
  have h7 : -f x₀ ≤ (0 : ℝ) := le_of_tendsto h5 h6
  linarith

-- ============================================================================
-- Helper: orientation implies directional monotonicity
-- ============================================================================

/-- Given the orientation condition, for every `t > 0`,
`χ_F(x+t•v) ≤ χ_F(x)` a.e. -/
lemma orientation_directional_monotone
    {F : Set (E n)} {v : E n} (hF : MeasurableSet F)
    (h_orientation : ∀ (φ : E n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x in F, fderiv ℝ φ x v)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂volume, (x + t • v ∈ F) → (x ∈ F) := by
  -- Step 1: For any non-negative smooth compactly supported ψ,
  -- ∫_F ψ(x+t•v) ≥ ∫_F ψ(x)
  have h1 : ∀ (ψ : E n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∀ x, 0 ≤ ψ x) → ∫ x in F, ψ (x + t • v) ≥ ∫ x in F, ψ x := by
    intro ψ hψ hsupp ψ_nonneg
    let f : ℝ → E n → ℝ := fun s x => (fderiv ℝ ψ (x + s • v)) v
    have h_int := directional_fubini_integrable (w := v) hF hψ hsupp (by linarith)
    have h_fubini : ∫ s in (0 : ℝ)..t, ∫ x in F, f s x =
        ∫ x in F, ∫ s in (0 : ℝ)..t, f s x :=
      intervalIntegral_integral_swap h_int
    have h_inner_nonneg : ∀ s ∈ Set.uIcc (0 : ℝ) t, 0 ≤ ∫ x in F, f s x := by
      intro s hs
      let φ : E n → ℝ := fun y => ψ (y + s • v)
      have hφ_smooth : ContDiff ℝ ∞ φ := by
        have h_c : ContDiff ℝ ∞ (fun (_ : E n) => s • v) := by simpa using contDiff_const
        have h_add : ContDiff ℝ ∞ (fun y : E n => y + s • v) := contDiff_id.add h_c
        exact hψ.comp h_add
      have hφ_supp : HasCompactSupport φ :=
        hasCompactSupport_comp_homeomorph hsupp (Homeomorph.addRight (s • v))
      have hφ_nonneg : ∀ x, 0 ≤ φ x := by
        intro x; exact ψ_nonneg (x + s • v)
      have h_eq1 : ∀ x, (fderiv ℝ φ x) v = f s x := by
        intro x
        have h_fd : HasFDerivAt ψ (fderiv ℝ ψ (x + s • v)) (x + s • v) :=
          (hψ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
        have h2 : HasFDerivAt (fun y : E n => y + s • v) (ContinuousLinearMap.id ℝ (E n)) x := by
          exact (hasFDerivAt_id x).add_const (s • v)
        have h3 : HasFDerivAt φ (fderiv ℝ ψ (x + s • v)) x := h_fd.comp x h2
        have h4 : fderiv ℝ φ x = fderiv ℝ ψ (x + s • v) := h3.fderiv
        rw [h4] <;> rfl
      have h5 : 0 ≤ ∫ x in F, (fderiv ℝ φ x) v :=
        h_orientation φ hφ_smooth hφ_supp hφ_nonneg
      have h6 : ∫ x in F, f s x = ∫ x in F, (fderiv ℝ φ x) v := by
        apply integral_congr_ae; filter_upwards with x; exact (h_eq1 x).symm
      rw [h6]; exact h5
    have hI_nonneg : 0 ≤ ∫ s in (0 : ℝ)..t, ∫ x in F, f s x := by
      rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ t by linarith)]
      apply setIntegral_nonneg (by simp)
      intro s hs
      have hs' : s ∈ Set.uIcc (0 : ℝ) t := by
        have h_pos : 0 ≤ s := le_of_lt hs.1
        have h_le : s ≤ t := hs.2
        have h0t : (0 : ℝ) ≤ t := by linarith
        simp [Set.mem_uIcc, h0t] <;> exact ⟨h_pos, h_le⟩
      exact h_inner_nonneg s hs'
    have h_ftc : ∀ x, ψ (x + t • v) - ψ x = ∫ s in (0 : ℝ)..t, f s x :=
      fun x => ftc_directional ψ hψ v x t
    have h_int_ψ : IntegrableOn ψ F volume :=
      hψ.continuous.integrable_of_hasCompactSupport hsupp |>.integrableOn
    have h_int_ψt : IntegrableOn (fun x : E n => ψ (x + t • v)) F volume := by
      have h_cont : Continuous (fun x : E n => ψ (x + t • v)) := hψ.continuous.comp (by fun_prop)
      have h_supp2 : HasCompactSupport (fun x : E n => ψ (x + t • v)) :=
        hasCompactSupport_comp_homeomorph hsupp (Homeomorph.addRight (t • v))
      exact h_cont.integrable_of_hasCompactSupport h_supp2 |>.integrableOn
    have h_integral_eq : ∫ x in F, (ψ (x + t • v) - ψ x) = ∫ x in F, ∫ s in (0 : ℝ)..t, f s x := by
      apply integral_congr_ae; filter_upwards with x; exact h_ftc x
    have h_main : 0 ≤ ∫ x in F, (ψ (x + t • v) - ψ x) := by
      rw [h_integral_eq, ←h_fubini]; exact hI_nonneg
    have h_sub : ∫ x in F, (ψ (x + t • v) - ψ x) =
        (∫ x in F, ψ (x + t • v)) - (∫ x in F, ψ x) :=
      integral_sub h_int_ψt h_int_ψ
    rw [h_sub] at h_main; linarith
  -- Step 2: Change of variables: ∫_{F+t•v} ψ ≥ ∫_F ψ
  let g : E n → E n := fun x => x + t • v
  have hg_cont : Continuous g := by fun_prop
  have hg_mp : MeasurePreserving g volume volume := measurePreserving_add_right volume (t • v)
  have hg_inj : Function.Injective g := by intro x y h; simpa [g] using h
  have h_meas : MeasurableEmbedding g := hg_cont.measurable.measurableEmbedding hg_inj
  have h_image : translateSet F (t • v) = g '' F := by rfl
  have hF_trans : MeasurableSet (translateSet F (t • v)) :=
    h_meas.measurableSet_image.mpr hF
  have h2 : ∀ (ψ : E n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∀ x, 0 ≤ ψ x) → ∫ x in translateSet F (t • v), ψ x ≥ ∫ x in F, ψ x := by
    intro ψ hψ hsupp ψ_nonneg
    have h_preimage : g ⁻¹' (g '' F) = F := hg_inj.preimage_image F
    have h_eq0 : ∫ x in g ⁻¹' (g '' F), ψ (g x) = ∫ y in g '' F, ψ y :=
      hg_mp.setIntegral_preimage_emb h_meas ψ (g '' F)
    have h_eq1 : ∫ x in F, ψ (g x) = ∫ x in g ⁻¹' (g '' F), ψ (g x) := by
      rw [h_preimage]
    have h_eq : ∫ x in F, ψ (g x) = ∫ y in g '' F, ψ y :=
      h_eq1.trans h_eq0
    have h3 : ∫ x in F, ψ (g x) ≥ ∫ x in F, ψ x := h1 ψ hψ hsupp ψ_nonneg
    rw [h_eq] at h3
    rw [←h_image] at h3; exact h3
  -- Step 3: Apply ae_nonneg_of_contDiff_test
  let χ1 : E n → ℝ := Set.indicator (translateSet F (t • v)) (fun _ => (1 : ℝ))
  let χ2 : E n → ℝ := Set.indicator F (fun _ => (1 : ℝ))
  let f_diff : E n → ℝ := χ1 - χ2
  have h1_loc : LocallyIntegrable f_diff volume := by
    have h_a : LocallyIntegrable χ1 volume := (locallyIntegrable_const (1 : ℝ)).indicator hF_trans
    have h_b : LocallyIntegrable χ2 volume := (locallyIntegrable_const (1 : ℝ)).indicator hF
    exact h_a.sub h_b
  have h_test : ∀ (φ : E n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x, f_diff x * φ x := by
    intro φ hφ hsupp φ_nonneg
    have h_eq1 : (fun x : E n => χ1 x * φ x) = Set.indicator (translateSet F (t • v)) φ := by
      funext x; simp [χ1, Set.indicator_apply] <;> ring
    have h_eq2 : (fun x : E n => χ2 x * φ x) = Set.indicator F φ := by
      funext x; simp [χ2, Set.indicator_apply] <;> ring
    have h7 : Integrable (fun x : E n => χ1 x * φ x) volume := by
      rw [h_eq1]; exact (hφ.continuous.integrable_of_hasCompactSupport hsupp).indicator hF_trans
    have h8 : Integrable (fun x : E n => χ2 x * φ x) volume := by
      rw [h_eq2]; exact (hφ.continuous.integrable_of_hasCompactSupport hsupp).indicator hF
    have h5 : ∫ x, f_diff x * φ x = ∫ x, (χ1 x - χ2 x) * φ x := by rfl
    have h9 : ∫ x, χ1 x * φ x = ∫ x in translateSet F (t • v), φ x := by
      rw [h_eq1, integral_indicator hF_trans]
    have h11 : ∫ x, χ2 x * φ x = ∫ x in F, φ x := by
      rw [h_eq2, integral_indicator hF]
    have h_eq : ∫ x, f_diff x * φ x =
        (∫ x in translateSet F (t • v), φ x) - (∫ x in F, φ x) := by
      have h_eq_fun : (fun x : E n => (χ1 x - χ2 x) * φ x) =
          (fun x : E n => χ1 x * φ x - χ2 x * φ x) := by
        funext x; ring
      have h_int_sub : ∫ x, (χ1 x - χ2 x) * φ x =
          (∫ x, χ1 x * φ x) - (∫ x, χ2 x * φ x) := by
        rw [h_eq_fun]
        exact integral_sub h7 h8
      calc
        ∫ x, f_diff x * φ x = ∫ x, (χ1 x - χ2 x) * φ x := h5
        _ = (∫ x, χ1 x * φ x) - (∫ x, χ2 x * φ x) := h_int_sub
        _ = (∫ x in translateSet F (t • v), φ x) - (∫ x, χ2 x * φ x) := by rw [h9]
        _ = (∫ x in translateSet F (t • v), φ x) - (∫ x in F, φ x) := by rw [h11]
    rw [h_eq]
    exact sub_nonneg.mpr (h2 φ hφ hsupp φ_nonneg)
  have h_ae_nonneg : ∀ᵐ x ∂volume, 0 ≤ f_diff x :=
    ae_nonneg_of_contDiff_test h1_loc h_test
  -- Step 4: f_diff ≥ 0 a.e. means χ1 ≥ χ2 a.e., i.e. F ⊆ F+t•v a.e.
  -- x ∈ F → x ∈ F+t•v → x-t•v ∈ F.
  -- Shift by +t•v: x+t•v ∈ F → x ∈ F.
  have h_ae1 : ∀ᵐ x ∂volume, (x ∈ F → x - t • v ∈ F) := by
    filter_upwards [h_ae_nonneg] with x hx
    intro hxF
    have h4 : 0 ≤ f_diff x := hx
    have h5 : χ2 x = 1 := by
      simp [χ2, Set.indicator_apply, hxF]
    have h6 : χ1 x = 1 := by
      have h7 : (0 : ℝ) ≤ χ1 x - χ2 x := h4
      rw [h5] at h7
      have h8 : χ1 x ≤ 1 := by
        simp [χ1, Set.indicator_apply]; split_ifs <;> norm_num
      linarith
    have h9 : x ∈ translateSet F (t • v) := by
      have h91 : χ1 x = 1 := h6
      have h : x ∈ translateSet F (t • v) := by
        by_cases h_case : x ∈ translateSet F (t • v)
        · exact h_case
        · have h10 : χ1 x = 0 := by
            simp [χ1, Set.indicator_apply, h_case]
            <;> rw [if_neg h_case] <;> norm_num
          rw [h10] at h91 <;> norm_num at h91
      exact h
    have h10 : ∃ (y : E n), y ∈ F ∧ y + t • v = x := by
      have h_def : translateSet F (t • v) = (fun y : E n => y + t • v) '' F := by rfl
      have h9' : x ∈ (fun y : E n => y + t • v) '' F := by
        rw [←h_def]
        exact h9
      exact h9'
    rcases h10 with ⟨y, hy, h_eq⟩
    have h11 : x - t • v = y := by rw [←h_eq]; abel
    rw [h11]; exact hy
  -- Shift the a.e. statement by +t•v using measure preservation
  let P : E n → Prop := fun y => y ∈ F → y - t • v ∈ F
  let shift : E n → E n := fun x => x + t • v
  have hshift_mp : MeasurePreserving shift volume volume := measurePreserving_add_right volume (t • v)
  have h_bad_set_eq : {x : E n | ¬P x} = {x : E n | x ∈ F ∧ x - t • v ∉ F} := by
    ext x; simp [P] <;> tauto
  have hP_meas : MeasurableSet {x : E n | ¬P x} := by
    rw [h_bad_set_eq]
    have h1 : MeasurableSet F := hF
    have h2 : MeasurableSet ((fun x : E n => x - t • v) ⁻¹' F) :=
      (continuous_id.sub continuous_const).measurable hF
    exact h1.diff h2
  have hN_null : volume {x : E n | ¬P x} = 0 := by
    rw [h_bad_set_eq]
    simpa [ae_iff] using h_ae1
  have h_preimage_eq : {x : E n | ¬P (shift x)} = shift ⁻¹' {x : E n | ¬P x} := by
    ext x; simp [shift]
  have h_goal_null : volume {x : E n | ¬P (shift x)} = 0 := by
    rw [h_preimage_eq]
    have h : volume (shift ⁻¹' {x : E n | ¬P x}) = volume {x : E n | ¬P x} :=
      hshift_mp.measure_preimage hP_meas.nullMeasurableSet
    rw [h, hN_null]
  have h_goal : ∀ᵐ x ∂volume, P (shift x) := by
    simpa [ae_iff] using h_goal_null
  simpa [P, shift] using h_goal


/-- Helper: a {0,1}-valued measurable function on ℝ that is non-increasing
a.e. (for every positive shift) is equal a.e. to an everywhere non-increasing
{0,1}-valued function. -/
lemma bool_ae_noninc_to_step {g₀ : ℝ → ℝ} (hg₀_meas : Measurable g₀)
    (hg₀_bool : ∀ s, g₀ s = 0 ∨ g₀ s = 1)
    (h_mono : ∀ (h : ℝ), 0 < h → ∀ᵐ s ∂volume, g₀ (s + h) ≤ g₀ s) :
    ∃ (g : ℝ → ℝ), Measurable g ∧ (∀ t, g t = 0 ∨ g t = 1) ∧
      (∀ s t, s ≤ t → g t ≤ g s) ∧ (g =ᵐ[volume] g₀) := by
  let A : Set ℝ := {s | g₀ s = 1}
  let B : Set ℝ := {s | g₀ s = 0}
  have hA_meas : MeasurableSet A := hg₀_meas (measurableSet_singleton 1)
  have hB_meas : MeasurableSet B := hg₀_meas (measurableSet_singleton 0)
  have h_univ : A ∪ B = Set.univ := by
    ext s
    simp only [A, B, Set.mem_union, Set.mem_univ, iff_true]
    have h : g₀ s = 0 ∨ g₀ s = 1 := hg₀_bool s
    rcases h with (h | h) <;> simp [h]
  have h_disj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro s h1 h2
    have h3 : g₀ s = 1 := h1
    have h4 : g₀ s = 0 := h2
    rw [h4] at h3; norm_num at h3

  by_cases hA_null : volume A = 0
  · -- Case: g₀ = 0 a.e.
    let g : ℝ → ℝ := fun _ => 0
    have hg_meas : Measurable g := by fun_prop
    have hg_bool : ∀ t, g t = 0 ∨ g t = 1 := by intro t; left; rfl
    have hg_decr : ∀ s t, s ≤ t → g t ≤ g s := by intro s t _; simp [g] <;> linarith
    have hg_ae : g =ᵐ[volume] g₀ := by
      have h_compl : {s : ℝ | g₀ s ≠ 0} = A := by
        ext s
        constructor
        · intro h
          have h' := hg₀_bool s
          rcases h' with (h1 | h1)
          · exfalso; exact h h1
          · exact h1
        · intro h
          have h_eq : g₀ s = 1 := by simpa [A] using h
          exact ne_of_eq_of_ne h_eq (by norm_num)
      have h : volume {s : ℝ | g₀ s ≠ 0} = 0 := by rw [h_compl]; exact hA_null
      have h_goal : ∀ᵐ s ∂volume, g s = g₀ s := by
        rw [ae_iff]
        have h_set : {s : ℝ | ¬(g s = g₀ s)} = {s : ℝ | g₀ s ≠ 0} := by
          ext s; simp [g] <;> exact ne_comm
        rw [h_set]
        exact h
      exact h_goal
    exact ⟨g, hg_meas, hg_bool, hg_decr, hg_ae⟩
  · by_cases hB_null : volume B = 0
    · -- Case: g₀ = 1 a.e.
      let g : ℝ → ℝ := fun _ => 1
      have hg_meas : Measurable g := by fun_prop
      have hg_bool : ∀ t, g t = 0 ∨ g t = 1 := by intro t; right; rfl
      have hg_decr : ∀ s t, s ≤ t → g t ≤ g s := by intro s t _; simp [g] <;> linarith
      have hg_ae : g =ᵐ[volume] g₀ := by
        have h_compl : {s : ℝ | g₀ s ≠ 1} = B := by
          ext s
          constructor
          · intro h
            have h' := hg₀_bool s
            rcases h' with (h1 | h1)
            · exact h1
            · exfalso; exact h h1
          · intro h
            have h_eq : g₀ s = 0 := by simpa [B] using h
            exact ne_of_eq_of_ne h_eq (by norm_num)
        have h : volume {s : ℝ | g₀ s ≠ 1} = 0 := by rw [h_compl]; exact hB_null
        have h_goal : ∀ᵐ s ∂volume, g s = g₀ s := by
          rw [ae_iff]
          have h_set : {s : ℝ | ¬(g s = g₀ s)} = {s : ℝ | g₀ s ≠ 1} := by
            ext s; simp [g] <;> exact ne_comm
          rw [h_set]
          exact h
        exact h_goal
      exact ⟨g, hg_meas, hg_bool, hg_decr, hg_ae⟩
    · -- Case: both A and B have positive measure
      have hA_pos : 0 < volume A := by
        have h : 0 ≤ volume A := by positivity
        exact lt_of_le_of_ne h (Ne.symm hA_null)
      have hB_pos : 0 < volume B := by
        have h : 0 ≤ volume B := by positivity
        exact lt_of_le_of_ne h (Ne.symm hB_null)

      -- Step 1: C = {(h,s) | 0 < h ∧ g₀(s+h) > g₀(s)} is null
      let C : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ g₀ (p.2 + p.1) > g₀ p.2}
      have hC_meas : MeasurableSet C := by
        have h1 : MeasurableSet {p : ℝ × ℝ | 0 < p.1} :=
          measurable_fst measurableSet_Ioi
        have h2 : Measurable (fun p : ℝ × ℝ => g₀ (p.2 + p.1)) :=
          hg₀_meas.comp (measurable_snd.add measurable_fst)
        have h3 : Measurable (fun p : ℝ × ℝ => g₀ p.2) :=
          hg₀_meas.comp measurable_snd
        have h4 : MeasurableSet {p : ℝ × ℝ | g₀ (p.2 + p.1) > g₀ p.2} :=
          measurableSet_lt h3 h2
        exact h1.inter h4
      have h_fiber_s : ∀ (h : ℝ), volume (Prod.mk h ⁻¹' C) = 0 := by
        intro h
        have h_eq : Prod.mk h ⁻¹' C = {s : ℝ | 0 < h ∧ g₀ (s + h) > g₀ s} := by
          ext s; simp [C] <;> rfl
        rw [h_eq]
        by_cases hh : 0 < h
        · have h2 : {s : ℝ | 0 < h ∧ g₀ (s + h) > g₀ s} = {s : ℝ | g₀ (s + h) > g₀ s} := by
            ext s; simp [hh] <;> tauto
          rw [h2]
          have h_ae : ∀ᵐ s ∂volume, ¬(g₀ (s + h) > g₀ s) := by
            filter_upwards [h_mono h hh] with s hs; linarith
          simpa [ae_iff] using h_ae
        · have h_empty : {s : ℝ | 0 < h ∧ g₀ (s + h) > g₀ s} = ∅ := by
            ext s; simp [hh] <;> linarith
          rw [h_empty]; simp
      have h_ae_fiber : (fun h : ℝ => volume (Prod.mk h ⁻¹' C)) =ᵐ[volume] 0 := by
        filter_upwards with h; exact h_fiber_s h
      have hC_null : volume C = 0 :=
        MeasureTheory.Measure.measure_prod_null_of_ae_null hC_meas h_ae_fiber

      -- Step 2: Swap C to get s-indexed fibers
      have h_swap_mp : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
        MeasureTheory.Measure.measurePreserving_swap (μ := volume) (ν := volume)
      let C_swap : Set (ℝ × ℝ) := Prod.swap '' C
      have hC_swap_null : volume C_swap = 0 := by
        have h1 : C_swap = Prod.swap ⁻¹' C := by
          ext ⟨a, b⟩; simp [C_swap, Prod.swap]
        rw [h1]
        have h2 : volume (Prod.swap ⁻¹' C) = volume C := h_swap_mp.measure_preimage hC_meas.nullMeasurableSet
        rw [h2]
        exact hC_null
      have hS_ae : (fun s : ℝ => volume (Prod.mk s ⁻¹' C_swap)) =ᵐ[volume] 0 :=
        MeasureTheory.Measure.measure_ae_null_of_prod_null hC_swap_null
      let S_good : Set ℝ := {s | volume (Prod.mk s ⁻¹' C_swap) = 0}
      have hS_ae' : ∀ᵐ s ∂volume, s ∈ S_good := by
        exact hS_ae
      have hS_compl_null : volume {s : ℝ | s ∉ S_good} = 0 := by
        simpa [ae_iff] using hS_ae'

      -- Step 3: For s ∈ S_good with g₀(s)=0, volume(A ∩ Ioi s) = 0
      have hS_good_prop : ∀ s ∈ S_good, g₀ s = 0 → volume (A ∩ Set.Ioi s) = 0 := by
        intro s hs hgs0
        have h1 : volume (Prod.mk s ⁻¹' C_swap) = 0 := hs
        have h_fiber_eq : Prod.mk s ⁻¹' C_swap = {h : ℝ | 0 < h ∧ g₀ (s + h) > g₀ s} := by
          ext h; simp [C_swap, C] <;> rfl
        rw [h_fiber_eq] at h1
        have h3 : {h : ℝ | 0 < h ∧ g₀ (s + h) > g₀ s} = {h : ℝ | 0 < h ∧ g₀ (s + h) = 1} := by
          ext h
          constructor
          · intro h4
            have h5 : 0 < h := h4.1
            have h6 : g₀ (s + h) > g₀ s := h4.2
            have h7 : g₀ (s + h) = 0 ∨ g₀ (s + h) = 1 := hg₀_bool (s + h)
            rw [hgs0] at h6
            rcases h7 with (h7 | h7)
            · exfalso; rw [h7] at h6; linarith
            · exact ⟨h5, h7⟩
          · intro h4
            exact ⟨h4.1, by rw [hgs0, h4.2] <;> norm_num⟩
        rw [h3] at h1
        let f : ℝ → ℝ := fun h => s + h
        have hf_eq : f = fun x : ℝ => x + s := by funext x; ring
        have hf_mp : MeasurePreserving f volume volume := by
          rw [hf_eq]; exact measurePreserving_add_right volume s
        have hf_inj : Function.Injective f := by intro x y h; simpa [f] using h
        have h4 : f '' {h : ℝ | 0 < h ∧ g₀ (s + h) = 1} = A ∩ Set.Ioi s := by
          ext t
          simp only [f, A, Set.mem_image, Set.mem_inter_iff, Set.mem_Ioi]
          constructor
          · rintro ⟨h, ⟨h_pos, h_eq⟩, rfl⟩
            have h_lt : s + h > s := by linarith
            exact ⟨h_eq, h_lt⟩
          · intro ht
            have h_pos2 : 0 < t - s := by linarith [ht.2]
            have h_eq2 : g₀ (s + (t - s)) = 1 := by
              have h_sum : s + (t - s) = t := by ring
              rw [h_sum]; exact ht.1
            exact ⟨t - s, ⟨h_pos2, h_eq2⟩, by ring⟩
        have h5 : volume (A ∩ Set.Ioi s) = volume {h : ℝ | 0 < h ∧ g₀ (s + h) = 1} := by
          have h6 : volume (f '' {h : ℝ | 0 < h ∧ g₀ (s + h) = 1}) = volume {h : ℝ | 0 < h ∧ g₀ (s + h) = 1} := by
            have h7 : MeasurableSet {h : ℝ | 0 < h ∧ g₀ (s + h) = 1} := by
              have h1 : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi
              have h2 : Measurable (fun h : ℝ => g₀ (s + h)) := hg₀_meas.comp (measurable_const.add measurable_id)
              have h3 : MeasurableSet {h : ℝ | g₀ (s + h) = 1} := h2 (measurableSet_singleton 1)
              exact h1.inter h3
            have h_img_meas : MeasurableSet (f '' {h : ℝ | 0 < h ∧ g₀ (s + h) = 1}) := by
              have h_eq : f '' {h : ℝ | 0 < h ∧ g₀ (s + h) = 1} = (fun y : ℝ => y - s) ⁻¹' {h : ℝ | 0 < h ∧ g₀ (s + h) = 1} := by
                ext y
                simp only [f, Set.mem_image, Set.mem_preimage]
                constructor
                · rintro ⟨x, hx, rfl⟩; simpa using hx
                · intro hy; refine ⟨y - s, hy, by ring⟩
              rw [h_eq]
              exact (by fun_prop : Measurable (fun y : ℝ => y - s)) h7
            have h8 : volume (f ⁻¹' (f '' {h : ℝ | 0 < h ∧ g₀ (s + h) = 1})) = volume (f '' {h : ℝ | 0 < h ∧ g₀ (s + h) = 1}) :=
              hf_mp.measure_preimage h_img_meas.nullMeasurableSet
            have h9 : f ⁻¹' (f '' {h : ℝ | 0 < h ∧ g₀ (s + h) = 1}) = {h : ℝ | 0 < h ∧ g₀ (s + h) = 1} :=
              hf_inj.preimage_image _
            rw [h9] at h8
            exact h8.symm
          rw [h4] at h6; exact h6
        rw [h5]; exact h1

      -- Step 4: D = {(h,t) | 0 < h ∧ g₀(t) > g₀(t-h)} is null
      let D : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ g₀ p.2 > g₀ (p.2 - p.1)}
      have hD_meas : MeasurableSet D := by
        have h_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi
        have h1 : MeasurableSet {p : ℝ × ℝ | 0 < p.1} := measurable_fst h_Ioi
        have h2 : Measurable (fun p : ℝ × ℝ => g₀ p.2) := hg₀_meas.comp measurable_snd
        have h3 : Measurable (fun p : ℝ × ℝ => g₀ (p.2 - p.1)) := hg₀_meas.comp (measurable_snd.sub measurable_fst)
        have h4 : MeasurableSet {p : ℝ × ℝ | g₀ p.2 > g₀ (p.2 - p.1)} := measurableSet_lt h3 h2
        exact h1.inter h4
      have h_fiber_t : ∀ (h : ℝ), volume (Prod.mk h ⁻¹' D) = 0 := by
        intro h
        have h_eq : Prod.mk h ⁻¹' D = {t : ℝ | 0 < h ∧ g₀ t > g₀ (t - h)} := by
          ext t; simp [D] <;> rfl
        rw [h_eq]
        by_cases hh : 0 < h
        · have h2 : {t : ℝ | 0 < h ∧ g₀ t > g₀ (t - h)} = {t : ℝ | g₀ t > g₀ (t - h)} := by
            ext t; simp [hh] <;> tauto
          rw [h2]
          let f : ℝ → ℝ := fun s => s + h
          have hf_mp : MeasurePreserving f volume volume := measurePreserving_add_right volume h
          have hf_inj : Function.Injective f := by intro x y h; simpa [f] using h
          have h_orig_null : volume {s : ℝ | g₀ (s + h) > g₀ s} = 0 := by
            have h_ae : ∀ᵐ s ∂volume, ¬(g₀ (s + h) > g₀ s) := by
              filter_upwards [h_mono h hh] with s hs; linarith
            simpa [ae_iff] using h_ae
          have h3 : f '' {s : ℝ | g₀ (s + h) > g₀ s} = {t : ℝ | g₀ t > g₀ (t - h)} := by
            ext t
            simp only [f, Set.mem_image]
            constructor
            · rintro ⟨s, hs, rfl⟩; simpa using hs
            · intro ht; refine ⟨t - h, by simpa [f] using ht, by ring⟩
          have h4 : volume {t : ℝ | g₀ t > g₀ (t - h)} = volume {s : ℝ | g₀ (s + h) > g₀ s} := by
            have h5 : volume (f '' {s : ℝ | g₀ (s + h) > g₀ s}) = volume {s : ℝ | g₀ (s + h) > g₀ s} := by
              have h6 : MeasurableSet {s : ℝ | g₀ (s + h) > g₀ s} := by
                have h1 : Measurable (fun s : ℝ => g₀ (s + h)) := hg₀_meas.comp (measurable_id.add measurable_const)
                have h2 : Measurable (fun s : ℝ => g₀ s) := hg₀_meas
                exact measurableSet_lt h2 h1
              have h_img_meas2 : MeasurableSet (f '' {s : ℝ | g₀ (s + h) > g₀ s}) := by
                have h_eq : f '' {s : ℝ | g₀ (s + h) > g₀ s} = (fun t : ℝ => t - h) ⁻¹' {s : ℝ | g₀ (s + h) > g₀ s} := by
                  ext t
                  simp only [f, Set.mem_image, Set.mem_preimage]
                  constructor
                  · rintro ⟨x, hx, rfl⟩; simpa using hx
                  · intro hy; refine ⟨t - h, hy, by ring⟩
                rw [h_eq]
                exact (by fun_prop : Measurable (fun t : ℝ => t - h)) h6
              have h7 : volume (f ⁻¹' (f '' {s : ℝ | g₀ (s + h) > g₀ s})) = volume (f '' {s : ℝ | g₀ (s + h) > g₀ s}) :=
                hf_mp.measure_preimage h_img_meas2.nullMeasurableSet
              have h8 : f ⁻¹' (f '' {s : ℝ | g₀ (s + h) > g₀ s}) = {s : ℝ | g₀ (s + h) > g₀ s} :=
                hf_inj.preimage_image _
              rw [h8] at h7; exact h7.symm
            rw [h3] at h5; exact h5
          rw [h4]; exact h_orig_null
        · have h_empty : {t : ℝ | 0 < h ∧ g₀ t > g₀ (t - h)} = ∅ := by
            ext t; simp [hh] <;> linarith
          rw [h_empty]; simp
      have h_ae_fiber_d : (fun h : ℝ => volume (Prod.mk h ⁻¹' D)) =ᵐ[volume] 0 := by
        filter_upwards with h; exact h_fiber_t h
      have hD_null : volume D = 0 :=
        MeasureTheory.Measure.measure_prod_null_of_ae_null hD_meas h_ae_fiber_d

      -- Step 5: Swap D to get t-indexed fibers → T_good
      let D_swap : Set (ℝ × ℝ) := Prod.swap '' D
      have hD_swap_null : volume D_swap = 0 := by
        have h1 : D_swap = Prod.swap ⁻¹' D := by
          ext ⟨a, b⟩; simp [D_swap, Prod.swap]
        rw [h1]
        have h_swap_mp2 : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
          MeasureTheory.Measure.measurePreserving_swap (μ := volume) (ν := volume)
        have h2 : volume (Prod.swap ⁻¹' D) = volume D := h_swap_mp2.measure_preimage hD_meas.nullMeasurableSet
        rw [h2]
        exact hD_null
      have hT_ae : (fun t : ℝ => volume (Prod.mk t ⁻¹' D_swap)) =ᵐ[volume] 0 :=
        MeasureTheory.Measure.measure_ae_null_of_prod_null hD_swap_null
      let T_good : Set ℝ := {t | volume (Prod.mk t ⁻¹' D_swap) = 0}
      have hT_ae' : ∀ᵐ t ∂volume, t ∈ T_good := hT_ae
      have hT_compl_null : volume {t : ℝ | t ∉ T_good} = 0 := by
        simpa [ae_iff] using hT_ae'

      -- Step 6: For t ∈ T_good with g₀(t)=1, volume(B ∩ Iio t) = 0
      have hT_good_prop : ∀ t ∈ T_good, g₀ t = 1 → volume (B ∩ Set.Iio t) = 0 := by
        intro t ht hgt1
        have h1 : volume (Prod.mk t ⁻¹' D_swap) = 0 := ht
        have h_fiber_eq : Prod.mk t ⁻¹' D_swap = {h : ℝ | 0 < h ∧ g₀ t > g₀ (t - h)} := by
          ext h; simp [D_swap, D] <;> rfl
        rw [h_fiber_eq] at h1
        have h3 : {h : ℝ | 0 < h ∧ g₀ t > g₀ (t - h)} = {h : ℝ | 0 < h ∧ g₀ (t - h) = 0} := by
          ext h
          constructor
          · intro h4
            have h5 : g₀ t > g₀ (t - h) := h4.2
            have h6 : g₀ (t - h) = 0 ∨ g₀ (t - h) = 1 := hg₀_bool (t - h)
            rw [hgt1] at h5
            rcases h6 with (h6 | h6)
            · exact ⟨h4.1, h6⟩
            · exfalso
              have h1 : g₀ t = 1 := hgt1
              have h2 : g₀ (t - h) = 1 := h6
              linarith [h5, h1, h2]
          · intro h4
            exact ⟨h4.1, by rw [hgt1, h4.2] <;> norm_num⟩
        rw [h3] at h1
        let f : ℝ → ℝ := fun h => t - h
        have hf_mp : MeasurePreserving f volume volume := by
          have h1 : MeasurePreserving (fun x : ℝ => -x) volume volume := Measure.measurePreserving_neg volume
          have h2 : MeasurePreserving (fun x : ℝ => t + x) volume volume := measurePreserving_add_left volume t
          have h3 : MeasurePreserving ((fun x : ℝ => t + x) ∘ (fun x : ℝ => -x)) volume volume := h2.comp h1
          have h4 : ((fun x : ℝ => t + x) ∘ (fun x : ℝ => -x)) = f := by
            funext x; simp [f]; ring
          exact h4 ▸ h3
        have hf_inj : Function.Injective f := by intro x y h; simpa [f] using h
        have h4 : f '' {h : ℝ | 0 < h ∧ g₀ (t - h) = 0} = B ∩ Set.Iio t := by
          ext s
          simp only [f, B, Set.mem_image, Set.mem_inter_iff, Set.mem_Iio]
          constructor
          · rintro ⟨h, hh, rfl⟩
            have h_lt : t - h < t := by linarith [hh.1]
            exact ⟨hh.2, h_lt⟩
          · intro ht
            have hgs0 : g₀ s = 0 := by simpa [B] using ht.1
            have hst : s < t := ht.2
            have hpos : 0 < t - s := by linarith
            have heq : g₀ (t - (t - s)) = 0 := by simpa using hgs0
            refine ⟨t - s, ⟨hpos, heq⟩, by ring⟩
        have h5 : volume (B ∩ Set.Iio t) = volume {h : ℝ | 0 < h ∧ g₀ (t - h) = 0} := by
          have h6 : volume (f '' {h : ℝ | 0 < h ∧ g₀ (t - h) = 0}) = volume {h : ℝ | 0 < h ∧ g₀ (t - h) = 0} := by
            have h7 : MeasurableSet {h : ℝ | 0 < h ∧ g₀ (t - h) = 0} := by
              have h_meas1 : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi
              have h_meas2 : MeasurableSet {h : ℝ | g₀ (t - h) = 0} :=
                (hg₀_meas.comp (measurable_const.sub measurable_id)) (measurableSet_singleton 0)
              exact h_meas1.inter h_meas2
            have h_img_meas3 : MeasurableSet (f '' {h : ℝ | 0 < h ∧ g₀ (t - h) = 0}) := by
              have h_eq : f '' {h : ℝ | 0 < h ∧ g₀ (t - h) = 0} = f ⁻¹' {h : ℝ | 0 < h ∧ g₀ (t - h) = 0} := by
                ext y
                simp only [f, Set.mem_image, Set.mem_preimage]
                constructor
                · rintro ⟨x, hx, rfl⟩; simpa using hx
                · intro hy; refine ⟨t - y, hy, by ring⟩
              rw [h_eq]
              exact (by fun_prop : Measurable f) h7
            have h8 : volume (f ⁻¹' (f '' {h : ℝ | 0 < h ∧ g₀ (t - h) = 0})) = volume (f '' {h : ℝ | 0 < h ∧ g₀ (t - h) = 0}) :=
              hf_mp.measure_preimage h_img_meas3.nullMeasurableSet
            have h9 : f ⁻¹' (f '' {h : ℝ | 0 < h ∧ g₀ (t - h) = 0}) = {h : ℝ | 0 < h ∧ g₀ (t - h) = 0} :=
              hf_inj.preimage_image _
            rw [h9] at h8; exact h8.symm
          rw [h4] at h6; exact h6
        rw [h5]; exact h1

      -- Step 7: Define Z, prove nonempty and bounded below
      let Z : Set ℝ := {t | volume (A ∩ Set.Ioi t) = 0}
      have hZ_nonempty : Z.Nonempty := by
        have h1 : volume (B ∩ S_good) = volume B := by
          have h2 : B ⊆ (B ∩ S_good) ∪ {s : ℝ | s ∉ S_good} := by
            intro x hx; by_cases h3 : x ∈ S_good <;> simp [h3] <;> tauto
          have h3 : volume B ≤ volume (B ∩ S_good) + volume {s : ℝ | s ∉ S_good} := by
            calc volume B
              ≤ volume ((B ∩ S_good) ∪ {s : ℝ | s ∉ S_good}) := measure_mono h2
              _ ≤ volume (B ∩ S_good) + volume {s : ℝ | s ∉ S_good} := measure_union_le _ _
          rw [hS_compl_null] at h3
          have h3' : volume B ≤ volume (B ∩ S_good) := by simpa [add_zero] using h3
          have h4 : (B ∩ S_good) ⊆ B := by simp
          exact le_antisymm (measure_mono h4) h3'
        have h4 : 0 < volume (B ∩ S_good) := by rw [h1]; exact hB_pos
        have h5 : (B ∩ S_good).Nonempty := by
          by_contra h6
          have h7 : (B ∩ S_good) = ∅ := Set.not_nonempty_iff_eq_empty.mp h6
          rw [h7] at h4
          simpa using h4
        rcases h5 with ⟨s, hsB, hsS⟩
        have hgs0 : g₀ s = 0 := hsB
        exact ⟨s, hS_good_prop s hsS hgs0⟩
      have hZ_bdd_below : BddBelow Z := by
        have h1 : volume (A ∩ T_good) = volume A := by
          have h2 : A ⊆ (A ∩ T_good) ∪ {t : ℝ | t ∉ T_good} := by
            intro x hx; by_cases h3 : x ∈ T_good <;> simp [h3] <;> tauto
          have h3 : volume A ≤ volume (A ∩ T_good) + volume {t : ℝ | t ∉ T_good} := by
            calc volume A
              ≤ volume ((A ∩ T_good) ∪ {t : ℝ | t ∉ T_good}) := measure_mono h2
              _ ≤ volume (A ∩ T_good) + volume {t : ℝ | t ∉ T_good} := measure_union_le _ _
          rw [hT_compl_null] at h3
          have h3' : volume A ≤ volume (A ∩ T_good) := by simpa [add_zero] using h3
          have h4 : (A ∩ T_good) ⊆ A := by simp
          exact le_antisymm (measure_mono h4) h3'
        have h4 : 0 < volume (A ∩ T_good) := by rw [h1]; exact hA_pos
        have h5 : (A ∩ T_good).Nonempty := by
          by_contra h6
          have h7 : (A ∩ T_good) = ∅ := Set.not_nonempty_iff_eq_empty.mp h6
          rw [h7] at h4
          simpa using h4
        rcases h5 with ⟨a, haA, haT⟩
        have hga1 : g₀ a = 1 := haA
        have h6 : volume (B ∩ Set.Iio a) = 0 := hT_good_prop a haT hga1
        refine ⟨a, fun z hz => ?_⟩
        by_contra hlt
        have h7 : z < a := by linarith
        have h8 : volume (A ∩ Set.Ioc z a) = 0 := by
          have h_sub : A ∩ Set.Ioc z a ⊆ A ∩ Set.Ioi z := by
            intro x hx
            have hxA : x ∈ A := hx.1
            have h_lt : z < x := hx.2.1
            exact ⟨hxA, h_lt⟩
          exact measure_mono_null h_sub hz
        have h9 : volume (B ∩ Set.Ioc z a) = 0 := by
          have h_sub : B ∩ Set.Ioc z a ⊆ (B ∩ Set.Iio a) ∪ {a} := by
            intro x hx
            have hxB : x ∈ B := hx.1
            have h_x2 : x ≤ a := hx.2.2
            by_cases h : x < a
            · exact Or.inl ⟨hxB, h⟩
            · have h_le : a ≤ x := by linarith
              have h' : x = a := le_antisymm h_x2 h_le
              exact Or.inr h'
          have h10 : volume ((B ∩ Set.Iio a) ∪ {a}) = 0 := by
            have h11 : volume (B ∩ Set.Iio a) = 0 := h6
            have h12 : volume ({a} : Set ℝ) = 0 := by simp
            have h13 : volume ((B ∩ Set.Iio a) ∪ {a}) ≤ volume (B ∩ Set.Iio a) + volume ({a} : Set ℝ) := measure_union_le _ _
            rw [h11, h12] at h13
            simpa using h13
          exact measure_mono_null h_sub h10
        have h10 : Set.Ioc z a ⊆ (A ∩ Set.Ioc z a) ∪ (B ∩ Set.Ioc z a) := by
          intro x hx
          have h11 : x ∈ A ∪ B := by rw [h_univ]; trivial
          rcases h11 with (h11 | h11) <;> simp [h11, hx] <;> tauto
        have h12 : volume (Set.Ioc z a) = 0 := by
          have h13 : volume (Set.Ioc z a) ≤ volume ((A ∩ Set.Ioc z a) ∪ (B ∩ Set.Ioc z a)) := measure_mono h10
          have h14 : volume ((A ∩ Set.Ioc z a) ∪ (B ∩ Set.Ioc z a)) ≤
              volume (A ∩ Set.Ioc z a) + volume (B ∩ Set.Ioc z a) := measure_union_le _ _
          have h15 : volume (A ∩ Set.Ioc z a) + volume (B ∩ Set.Ioc z a) = 0 := by
            rw [h8, h9]; simp
          have h16 : volume (Set.Ioc z a) ≤ 0 := le_trans h13 (le_trans h14 (le_of_eq h15))
          exact le_zero_iff.mp h16
        have h15 : 0 < volume (Set.Ioc z a) := by
          rw [Real.volume_Ioc]
          apply ENNReal.ofReal_pos.mpr
          linarith
        rw [h12] at h15; exact h15.false.elim

      -- Step 8: Define α and g
      let α : ℝ := sInf Z
      let g : ℝ → ℝ := fun s => if s < α then 1 else 0
      have hg_meas : Measurable g := by
        have h1 : MeasurableSet {s : ℝ | s < α} := measurableSet_lt measurable_id measurable_const
        have h2 : g = Set.indicator {s : ℝ | s < α} (fun _ => (1 : ℝ)) := by
          funext s
          by_cases h : s < α <;> simp [g, h, Set.indicator_apply] <;> norm_num
        rw [h2]
        exact measurable_const.indicator h1
      have hg_bool : ∀ t, g t = 0 ∨ g t = 1 := by
        intro t; by_cases h : t < α <;> simp [g, h] <;> tauto
      have hg_decr : ∀ s t, s ≤ t → g t ≤ g s := by
        intro s t hst
        by_cases h : t < α
        · have h' : s < α := by linarith
          have h1 : g t = 1 := by simp [g, h]
          have h2 : g s = 1 := by simp [g, h']
          rw [h1, h2] <;> norm_num
        · have h1 : g t = 0 := by simp [g, h]
          rw [h1]
          have h2 : 0 ≤ g s := by
            have h3 : g s = 0 ∨ g s = 1 := hg_bool s
            rcases h3 with (h3 | h3) <;> rw [h3] <;> norm_num
          exact h2

      -- Step 9: Z is upward closed and t > α implies t ∈ Z
      have hZ_upward : ∀ t u, t ∈ Z → t ≤ u → u ∈ Z := by
        intro t u ht htu
        have h1 : A ∩ Set.Ioi u ⊆ A ∩ Set.Ioi t := by
          intro x hx
          have hxA : x ∈ A := hx.1
          have h_ux : u < x := hx.2
          have h_tx : t < x := lt_of_le_of_lt htu h_ux
          exact ⟨hxA, h_tx⟩
        exact measure_mono_null h1 ht
      have hZ_above_alpha : ∀ t, α < t → t ∈ Z := by
        intro t ht
        have h1 : ∃ z ∈ Z, z < t := by
          by_contra h2
          push Not at h2
          have h3 : ∀ z ∈ Z, t ≤ z := h2
          have h4 : t ≤ α := le_csInf hZ_nonempty h3
          linarith
        rcases h1 with ⟨z, hz, hzt⟩
        exact hZ_upward z t hz (by linarith)

      -- Step 10: g₀ = 0 a.e. on Ioi α
      have h_A_Ioi_alpha_null : volume (A ∩ Set.Ioi α) = 0 := by
        have h1 : A ∩ Set.Ioi α = ⋃ k : ℕ, A ∩ Set.Ioi (α + 1 / (k + 1 : ℝ)) := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion]
          constructor
          · intro hx
            have h2 : α < x := hx.2
            obtain ⟨k, hk⟩ : ∃ k : ℕ, α + 1 / (k + 1 : ℝ) < x := by
              have h3 : ∃ k : ℕ, 1 / (k + 1 : ℝ) < x - α := exists_nat_one_div_lt (by linarith)
              rcases h3 with ⟨k, hk⟩
              have h4 : α + 1 / (k + 1 : ℝ) < x := by linarith
              exact ⟨k, h4⟩
            exact ⟨k, hx.1, hk⟩
          · rintro ⟨k, hx1, hx2⟩
            have h_pos : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
            have h_alpha_lt : α < α + 1 / (k + 1 : ℝ) := by linarith
            have h5 : α < x := lt_trans h_alpha_lt hx2
            exact ⟨hx1, h5⟩
        rw [h1]
        apply measure_iUnion_null
        intro k
        have h2 : α < α + 1 / (k + 1 : ℝ) := by
          have h3 : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
          linarith
        exact hZ_above_alpha (α + 1 / (k + 1 : ℝ)) h2

      -- Step 11: g₀ = 1 a.e. on Iio α
      have h_B_Iio_alpha_null : volume (B ∩ Set.Iio α) = 0 := by
        by_contra h
        have hpos : 0 < volume (B ∩ Set.Iio α) := by
          have h_nonneg : 0 ≤ volume (B ∩ Set.Iio α) := by positivity
          exact lt_of_le_of_ne h_nonneg (Ne.symm h)
        have h1 : volume ((B ∩ Set.Iio α) ∩ S_good) = volume (B ∩ Set.Iio α) := by
          have h2 : (B ∩ Set.Iio α) ⊆ ((B ∩ Set.Iio α) ∩ S_good) ∪ {s : ℝ | s ∉ S_good} := by
            intro x hx; by_cases h3 : x ∈ S_good <;> simp [h3] <;> tauto
          have h3 : volume (B ∩ Set.Iio α) ≤ volume ((B ∩ Set.Iio α) ∩ S_good) + volume {s : ℝ | s ∉ S_good} := by
            calc volume (B ∩ Set.Iio α)
              ≤ volume (((B ∩ Set.Iio α) ∩ S_good) ∪ {s : ℝ | s ∉ S_good}) := measure_mono h2
              _ ≤ volume ((B ∩ Set.Iio α) ∩ S_good) + volume {s : ℝ | s ∉ S_good} := measure_union_le _ _
          rw [hS_compl_null] at h3
          have h3' : volume (B ∩ Set.Iio α) ≤ volume ((B ∩ Set.Iio α) ∩ S_good) := by simpa [add_zero] using h3
          have h4 : ((B ∩ Set.Iio α) ∩ S_good) ⊆ (B ∩ Set.Iio α) := by
            intro x hx; exact hx.1
          exact le_antisymm (measure_mono h4) h3'
        have h4 : 0 < volume ((B ∩ Set.Iio α) ∩ S_good) := by
          rw [h1]; exact hpos
        have h5 : ((B ∩ Set.Iio α) ∩ S_good).Nonempty := by
          by_contra h6
          have h7 : ((B ∩ Set.Iio α) ∩ S_good) = ∅ := Set.not_nonempty_iff_eq_empty.mp h6
          rw [h7] at h4
          simpa using h4
        rcases h5 with ⟨b, hbB, hbS⟩
        have hb_lt_alpha : b < α := hbB.2
        have hgb0 : g₀ b = 0 := by simpa [B] using hbB.1
        have hb_in_Z : b ∈ Z := hS_good_prop b hbS hgb0
        have h6 : α ≤ b := csInf_le hZ_bdd_below hb_in_Z
        linarith

      -- Step 12: g = g₀ a.e.
      have h_singleton_null : ∀ᵐ s ∂volume, s ≠ α := by
        have h : volume ({α} : Set ℝ) = 0 := by simp
        simpa [ae_iff] using h
      have h1 : ∀ᵐ s ∂volume, s ∉ A ∩ Set.Ioi α := by
        rw [ae_iff]
        have h_eq : {s : ℝ | ¬(s ∉ A ∩ Set.Ioi α)} = A ∩ Set.Ioi α := by ext x; simp
        rw [h_eq]
        exact h_A_Ioi_alpha_null
      have h2 : ∀ᵐ s ∂volume, s ∉ B ∩ Set.Iio α := by
        rw [ae_iff]
        have h_eq : {s : ℝ | ¬(s ∉ B ∩ Set.Iio α)} = B ∩ Set.Iio α := by ext x; simp
        rw [h_eq]
        exact h_B_Iio_alpha_null
      have hg_ae : g =ᵐ[volume] g₀ := by
        filter_upwards [h1, h2, h_singleton_null] with s hs1 hs2 hs3
        by_cases h3 : s < α
        · have h4 : s ∉ B := by simpa [Set.mem_inter_iff, h3] using hs2
          have h5 : g₀ s = 1 := by
            have h6 : g₀ s = 0 ∨ g₀ s = 1 := hg₀_bool s
            rcases h6 with (h6 | h6)
            · exfalso; exact h4 h6
            · exact h6
          simp [g, h3, h5]
        · have h4 : α < s := by
            have h_le : α ≤ s := le_of_not_gt h3
            by_contra h5
            have h_le2 : s ≤ α := le_of_not_gt h5
            have h_eq : s = α := le_antisymm h_le2 h_le
            exact hs3 h_eq
          have h5 : s ∉ A := by simpa [Set.mem_inter_iff, h4] using hs1
          have h6 : g₀ s = 0 := by
            have h7 : g₀ s = 0 ∨ g₀ s = 1 := hg₀_bool s
            rcases h7 with (h7 | h7)
            · exact h7
            · exfalso; exact h5 h7
          have hgs : g s = 0 := by
            have h7 : ¬(s < α) := h3
            simp [g, h7]
          rw [hgs, h6]
      exact ⟨g, hg_meas, hg_bool, hg_decr, hg_ae⟩

/-- Linear map that replaces the `i₀`-th coordinate with `inner(·, v)`.

This is an invertible shear transformation when `v i₀ ≠ 0`. -/
noncomputable def innerCoordLinearMap {n : ℕ} (v : E n) (i₀ : Fin n) : E n →ₗ[ℝ] E n :=
  let e : E n ≃ₗ[ℝ] (Fin n → ℝ) := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  let h : E n → E n := fun x => e.symm (Function.update (e x) i₀ (inner ℝ x v))
  { toFun := h
    map_add' := by
      intro x y
      apply e.injective
      have h_eq1 : ∀ (z : E n), e (h z) = Function.update (e z) i₀ (inner ℝ z v) := by
        intro z; exact e.apply_symm_apply _
      rw [h_eq1 (x + y), e.map_add (h x) (h y), h_eq1 x, h_eq1 y]
      ext i
      by_cases hi : i = i₀
      · subst hi
        simp [Function.update_apply, inner_add_left] <;> ring
      · simp [Function.update_apply, hi] <;> ring
    map_smul' := by
      intro c x
      apply e.injective
      ext i
      by_cases hi : i = i₀
      · subst hi
        simp [h, e.apply_symm_apply, Function.update_apply, inner_smul_left] <;> ring
      · simp [h, e.apply_symm_apply, Function.update_apply, hi] <;> ring }

/-- The coordinate-replacement linear map is invertible when `v i₀ ≠ 0`. -/
lemma innerCoordLinearMap_det_ne_zero {n : ℕ} {v : E n} {i₀ : Fin n} (hi₀_nz : v i₀ ≠ 0) :
    LinearMap.det (innerCoordLinearMap v i₀) ≠ 0 := by
  let T := innerCoordLinearMap v i₀
  let e : E n ≃ₗ[ℝ] (Fin n → ℝ) := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  have hT_inj : Function.Injective T := by
    intro x y h
    have h_eq : e (T x) = e (T y) := by rw [h]
    have h1 : ∀ i, i ≠ i₀ → (e x) i = (e y) i := by
      intro i hi
      have h2 : (e (T x)) i = (e (T y)) i := by rw [h_eq]
      have h2x : e (T x) = Function.update (e x) i₀ (inner ℝ x v) := by rfl
      have h2y : e (T y) = Function.update (e y) i₀ (inner ℝ y v) := by rfl
      rw [h2x, h2y] at h2
      simpa [Function.update_apply, hi] using h2
    have h3 : inner ℝ x v = inner ℝ y v := by
      have h4 : (e (T x)) i₀ = (e (T y)) i₀ := by rw [h_eq]
      have h2x : e (T x) = Function.update (e x) i₀ (inner ℝ x v) := by rfl
      have h2y : e (T y) = Function.update (e y) i₀ (inner ℝ y v) := by rfl
      rw [h2x, h2y] at h4
      simpa [Function.update_apply] using h4
    have h5 : (e x) i₀ = (e y) i₀ := by
      let z := x - y
      have hz1 : inner ℝ z v = 0 := by
        have h_eq : inner ℝ z v = inner ℝ x v - inner ℝ y v := by
          have h : z = x - y := by rfl
          rw [h]
          exact inner_sub_left (x := x) (y := y) (z := v)
        rw [h_eq]
        exact sub_eq_zero.mpr h3
      have hz2 : ∀ i, i ≠ i₀ → (e z) i = 0 := by
        intro i hi
        have h : (e z) i = (e x) i - (e y) i := by
          have h' : e z = e x - e y := e.map_sub x y
          rw [h'] <;> rfl
        rw [h]
        exact sub_eq_zero.mpr (h1 i hi)
      have h_inner_sum : inner ℝ z v = ∑ i : Fin n, (e z) i * (e v) i := by
        rw [PiLp.inner_apply z v]
        apply Finset.sum_congr rfl
        intro i _
        rw [Real.inner_apply]
        <;> rfl
      rw [h_inner_sum] at hz1
      have h_in : i₀ ∈ (Finset.univ : Finset (Fin n)) := by simp
      have h9 : ∑ i : Fin n, (e z) i * (e v) i = (e z) i₀ * (e v) i₀ := by
        rw [Finset.sum_eq_single_of_mem i₀ h_in]
        intro j _ hj
        rw [hz2 j hj, zero_mul]
      rw [h9] at hz1
      have h10 : (e v) i₀ ≠ 0 := by simpa [e] using hi₀_nz
      have h11 : (e z) i₀ = 0 := (mul_eq_zero.mp hz1).resolve_right h10
      have h12 : (e z) i₀ = (e x) i₀ - (e y) i₀ := by
        have h13 : e z = e x - e y := e.map_sub x y
        rw [h13] <;> rfl
      rw [h12] at h11
      exact sub_eq_zero.mp h11
    ext i; by_cases h : i = i₀
    · rw [h]; exact h5
    · exact h1 i h
  have h_surj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hT_inj
  let e' : E n ≃ₗ[ℝ] E n := LinearEquiv.ofBijective T ⟨hT_inj, h_surj⟩
  have h_det_main : LinearMap.det (e' : E n →ₗ[ℝ] E n) ≠ 0 := by
    have h_eq : LinearMap.det (e' : E n →ₗ[ℝ] E n) = ↑(LinearEquiv.det e') := by
      simp [LinearEquiv.det]
      <;> rfl
    rw [h_eq]
    exact Units.ne_zero _
  exact h_det_main

/-- Coordinate slice nullity: `volume {y | y i₀ ∈ M} = 0 ↔ volume M = 0`. -/
lemma coordinate_slice_null {n : ℕ} (i₀ : Fin n) {M : Set ℝ} (hM : MeasurableSet M) :
    volume {y : E n | y i₀ ∈ M} = 0 ↔ volume M = 0 := by
  let e : E n ≃ᵐ (Fin n → ℝ) := (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm
  have he_mp : MeasurePreserving e volume volume := by
    convert EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (ι := Fin n) <;>
      try { exact rfl } <;>
      try { apply Subsingleton.elim }
  have h_eval : Measurable (fun y : E n => y i₀) :=
    (PiLp.continuous_apply 2 _ i₀).measurable
  have hS_meas : MeasurableSet {y : E n | y i₀ ∈ M} := h_eval hM
  have h_image_eq : e '' {y : E n | y i₀ ∈ M} = {z : Fin n → ℝ | z i₀ ∈ M} := by
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      have h9 : (e.symm z) i₀ = z i₀ := by
        have h10 : e (e.symm z) = z := e.apply_symm_apply z
        exact congr_fun h10 i₀
      rw [h9]; exact hz
  have h_vol_eq : volume {y : E n | y i₀ ∈ M} = volume {z : Fin n → ℝ | z i₀ ∈ M} := by
    have h_image_meas : MeasurableSet (e '' {y : E n | y i₀ ∈ M}) := by
      have h_eq : e '' {y : E n | y i₀ ∈ M} = e.symm ⁻¹' {y : E n | y i₀ ∈ M} := by
        ext z
        simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨x, hx, rfl⟩
          have h : e.symm (e x) = x := e.left_inv x
          rw [h]; exact hx
        · intro hz
          refine ⟨e.symm z, hz, e.apply_symm_apply z⟩
      rw [h_eq]
      exact e.symm.measurable hS_meas
    have h_pre : volume (e ⁻¹' (e '' {y : E n | y i₀ ∈ M})) = volume (e '' {y : E n | y i₀ ∈ M}) :=
      he_mp.measure_preimage h_image_meas.nullMeasurableSet
    have h_eq : e ⁻¹' (e '' {y : E n | y i₀ ∈ M}) = {y : E n | y i₀ ∈ M} := e.preimage_image _
    rw [h_eq] at h_pre
    have h : volume (e '' {y : E n | y i₀ ∈ M}) = volume {y : E n | y i₀ ∈ M} := h_pre.symm
    rw [h_image_eq] at h
    exact h.symm
  rw [h_vol_eq]
  constructor
  · -- Forward: if the pi-slice is null, then M is null
    intro h
    by_contra hM_pos
    have hM_pos' : 0 < volume M := by
      have h_nonneg : 0 ≤ volume M := by positivity
      have h_ne : (0 : ENNReal) ≠ volume M := by
        intro h_eq
        exact hM_pos h_eq.symm
      exact lt_of_le_of_ne h_nonneg h_ne
    let s : Fin n → Set ℝ := fun i => if h : i = i₀ then M else Set.Icc (-1 : ℝ) 1
    let B_pi : Set (Fin n → ℝ) := Set.univ.pi s
    have hB_sub : B_pi ⊆ {z : Fin n → ℝ | z i₀ ∈ M} := by
      intro z hz
      have h1 : z i₀ ∈ M := by
        simpa [B_pi, s, Set.mem_pi] using hz i₀
      exact h1
    have hs_meas : ∀ i, MeasurableSet (s i) := by
      intro i; by_cases h : i = i₀
      · subst h; simpa [s] using hM
      · simp [s, h, measurableSet_Icc]
    have hB_pi_meas : MeasurableSet B_pi :=
      MeasurableSet.pi Set.countable_univ (fun i _ => hs_meas i)
    have h_formula : volume B_pi = ∏ i : Fin n, volume (s i) :=
      MeasureTheory.volume_pi_pi s
    have hB_pos : 0 < volume B_pi := by
      rw [h_formula]
      have h_ne_zero : (∏ i : Fin n, volume (s i)) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro i _
        by_cases h : i = i₀
        · subst h; simpa [s] using hM_pos
        · simp [s, h] <;> norm_num
      have h_nonneg : 0 ≤ (∏ i : Fin n, volume (s i)) := by positivity
      have h_ne' : (0 : ENNReal) ≠ (∏ i : Fin n, volume (s i)) := by
        intro h_eq
        exact h_ne_zero h_eq.symm
      exact lt_of_le_of_ne h_nonneg h_ne'
    have h4 : volume B_pi ≤ volume {z : Fin n → ℝ | z i₀ ∈ M} := measure_mono hB_sub
    rw [h] at h4
    exact not_le.mpr hB_pos h4
  · -- Backward: if M is null, then the pi-slice is null
    intro hM_null
    let proj : (Fin n → ℝ) → ℝ := fun z => z i₀
    have h_set : {z : Fin n → ℝ | z i₀ ∈ M} = proj ⁻¹' M := by ext z; simp [proj]
    rw [h_set]
    have h_main : volume (proj ⁻¹' M) = 0 := by
      have h_vol : (volume : Measure (Fin n → ℝ)) = Measure.pi (fun (_ : Fin n) => volume) := by
        exact MeasureTheory.volume_pi
      rw [h_vol]
      exact MeasureTheory.Measure.pi_eval_preimage_null (fun (_ : Fin n) => volume) hM_null
    exact h_main

/-- Pushforward lemma: for a nonzero vector v, the set
`{x : E n | inner x v ∈ N}` has volume zero iff `N` has volume zero. -/
lemma inner_pushforward_null {n : ℕ} {v : E n} (hv_unit : ‖v‖ = 1) (hn_pos : 0 < n)
    {N : Set ℝ} (hN : MeasurableSet N) :
    volume {x : E n | inner ℝ x v ∈ N} = 0 ↔ volume N = 0 := by
  have h_exists : ∃ (i₀ : Fin n), v i₀ ≠ 0 := by
    by_contra h'; push Not at h'
    have h1 : v = 0 := by ext i; exact h' i
    rw [h1] at hv_unit; simp at hv_unit <;> linarith
  rcases h_exists with ⟨i₀, hi₀_nz⟩
  let T : E n →ₗ[ℝ] E n := innerCoordLinearMap v i₀
  have h_det : LinearMap.det T ≠ 0 := innerCoordLinearMap_det_ne_zero hi₀_nz
  have hT_map : Measure.map T volume = ENNReal.ofReal |(LinearMap.det T)⁻¹| • volume :=
    MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar volume h_det
  have hT_null : ∀ (S : Set (E n)), MeasurableSet S →
      (volume (T ⁻¹' S) = 0 ↔ volume S = 0) := by
    intro S hS
    have h1 : volume (T ⁻¹' S) = (Measure.map T volume) S := by
      have hT_cont : Continuous T := by continuity
      exact (Measure.map_apply hT_cont.measurable hS).symm
    rw [h1, hT_map]
    have hc_ne_zero : ENNReal.ofReal |(LinearMap.det T)⁻¹| ≠ 0 := by
      have h_pos : 0 < |(LinearMap.det T)⁻¹| := abs_pos.mpr (inv_ne_zero h_det)
      have hc_pos : 0 < ENNReal.ofReal |(LinearMap.det T)⁻¹| := by positivity
      exact hc_pos.ne'
    have h_main : (ENNReal.ofReal |(LinearMap.det T)⁻¹| • volume) S = 0 ↔ volume S = 0 := by
      have h_smul : (ENNReal.ofReal |(LinearMap.det T)⁻¹| • volume) S = ENNReal.ofReal |(LinearMap.det T)⁻¹| * volume S := by
        have h : ∀ (c : ENNReal) (μ : Measure (E n)) (T : Set (E n)), (c • μ) T = c * μ T := by
          intro c μ T
          rw [Measure.coe_smul c μ]
          <;> rfl
        exact h (ENNReal.ofReal |(LinearMap.det T)⁻¹|) volume S
      rw [h_smul]
      constructor
      · intro h
        have h_disj : ENNReal.ofReal |(LinearMap.det T)⁻¹| = 0 ∨ volume S = 0 := by
          simpa [mul_eq_zero] using h
        exact h_disj.resolve_left hc_ne_zero
      · intro h
        rw [h]
        simp
    exact h_main
  let S : Set (E n) := {y | y i₀ ∈ N}
  let e : E n ≃ₗ[ℝ] (Fin n → ℝ) := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  have h_eval_cont : Continuous (fun y : E n => y i₀) := by fun_prop
  have h_eval_meas : Measurable (fun y : E n => y i₀) := h_eval_cont.measurable
  have hS_meas : MeasurableSet S := h_eval_meas hN
  have h_key : ∀ (x : E n), (T x) i₀ = inner ℝ x v := by
    intro x
    have h : e (T x) = Function.update (e x) i₀ (inner ℝ x v) := by rfl
    have h2 : (e (T x)) i₀ = (T x) i₀ := by rfl
    rw [← h2, h]
    simp [Function.update_apply]
  have h_eq1 : T ⁻¹' S = {x : E n | inner ℝ x v ∈ N} := by
    ext x
    simp only [S, Set.mem_preimage, Set.mem_setOf_eq]
    rw [h_key x]
  calc volume {x : E n | inner ℝ x v ∈ N} = 0
    ↔ volume (T ⁻¹' S) = 0 := by rw [h_eq1]
    _ ↔ volume S = 0 := hT_null S hS_meas
    _ ↔ volume N = 0 := coordinate_slice_null i₀ hN

/-- **From orientation to monotone factorization** [GMT input].

Given a measurable set `F` that:
1. is a cylinder over the `v`-direction (`h_transl`), and
2. has non-negative ν-directional distributional derivative on non-negative test
   functions (`h_orientation`),

there exists a measurable, `{0,1}`-valued, non-increasing function `g : ℝ → ℝ`
such that `χ_F(x) = g(inner(x,v))` a.e.

**Proof sketch:**
1. `cylinder_factorization` gives a measurable `g₀` with `χ_F(x) = g₀(inner(x,v))` a.e.
2. Modify `g₀` on a null set to be `{0,1}`-valued everywhere.
3. By Fubini, `h_orientation` reduces to: for all non-negative smooth compactly
   supported `φ : ℝ → ℝ`, `∫ g₀(t) · φ'(t) dt ≥ 0`.
4. Mollify: `g₀,ε := g₀ * ρ_ε`. Then `g₀,ε'(x) = -∫ g₀(t) · (ρ_ε(x-·))'(t) dt ≤ 0`
   by the orientation condition (since `ρ_ε(x-·) ≥ 0`).
5. Thus each `g₀,ε` is non-increasing. Since `g₀,ε → g₀` a.e., `g₀` is equal a.e.
   to a non-increasing function `g`.
6. Redefine `g` on a null set to make it everywhere non-increasing and `{0,1}`-valued.

This is the key step where the **orientation** (sign of the distributional
derivative) converts a general cylinder into a **monotone** cylinder (half-space). -/
lemma orientation_to_monotone_factorization
    {F : Set (E n)} {v : E n} (hF : MeasurableSet F) (hv_unit : ‖v‖ = 1)
    (h_transl : ∀ (w : E n), inner ℝ w v = 0 →
      ∀ (t : ℝ), translateSet F (t • w) =ᵐ[volume] F)
    (h_orientation : ∀ (φ : E n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x in F, fderiv ℝ φ x v) :
    ∃ (g : ℝ → ℝ), Measurable g ∧
      (∀ t, g t = 0 ∨ g t = 1) ∧
      (∀ s t, s ≤ t → g t ≤ g s) ∧
      (∀ᵐ (x : E n) ∂volume, (x ∈ F ↔ g (inner ℝ x v) = 1)) := by
  -- Step 1: Cylinder factorization
  rcases cylinder_factorization hF hv_unit h_transl with ⟨g₀, hg₀_meas, h_factor⟩
  -- Step 2: Make g₁ everywhere {0,1}-valued
  let g₁ : ℝ → ℝ := fun s => if g₀ s = 1 then 1 else 0
  have h_pred_meas : MeasurableSet {s : ℝ | g₀ s = 1} := hg₀_meas (MeasurableSet.singleton 1)
  have hg₁_meas : Measurable g₁ := by
    have h_eq : g₁ = Set.indicator {s : ℝ | g₀ s = 1} (fun _ => (1 : ℝ)) := by
      funext s
      by_cases h : g₀ s = 1 <;> simp [g₁, Set.indicator_apply, h] <;> ring
    rw [h_eq]
    exact (measurable_const : Measurable (fun _ => (1 : ℝ))).indicator h_pred_meas
  have hg₁_bool : ∀ s, g₁ s = 0 ∨ g₁ s = 1 := by
    intro s; by_cases h : g₀ s = 1 <;> simp [g₁, h] <;> tauto
  have h_factor1 : ∀ᵐ (x : E n) ∂volume, (x ∈ F ↔ g₁ (inner ℝ x v) = 1) := by
    filter_upwards [h_factor] with x hx
    simpa [g₁] using hx
  -- Step 3: Directional monotonicity on E n
  have h_n_pos : 0 < n := by
    by_contra h
    have h' : n = 0 := by omega
    have hv0 : v = 0 := by
      ext i
      exfalso
      haveI : IsEmpty (Fin n) := by rw [h']; infer_instance
      exact isEmptyElim i
    rw [hv0] at hv_unit
    simp at hv_unit <;> linarith
  have h_dir_mono : ∀ (t : ℝ), 0 < t → ∀ᵐ (x : E n) ∂volume, (x + t • v ∈ F) → (x ∈ F) :=
    fun t ht => orientation_directional_monotone hF h_orientation ht
  have h_en_mono : ∀ (t : ℝ), 0 < t → ∀ᵐ (x : E n) ∂volume, g₁ (inner ℝ x v + t) ≤ g₁ (inner ℝ x v) := by
    intro t ht
    have h1 : ∀ᵐ (x : E n), (x + t • v ∈ F) → (x ∈ F) := h_dir_mono t ht
    have h2 : ∀ᵐ (x : E n), (x ∈ F ↔ g₁ (inner ℝ x v) = 1) := h_factor1
    let shift : E n → E n := fun x => x + t • v
    have hshift_mp : MeasurePreserving shift volume volume := measurePreserving_add_right volume (t • v)
    have h1_meas : MeasurableSet (F : Set (E n)) := hF
    have h2_meas : MeasurableSet {y : E n | g₁ (inner ℝ y v) = 1} := by
      have h_inner_cont : Continuous (fun y : E n => inner ℝ y v) := by fun_prop
      have h_inner_meas : Measurable (fun y : E n => inner ℝ y v) := h_inner_cont.measurable
      have h : Measurable (fun y : E n => g₁ (inner ℝ y v)) := hg₁_meas.comp h_inner_meas
      exact h (MeasurableSet.singleton 1)
    have hBad_meas : MeasurableSet {y : E n | ¬(y ∈ F ↔ g₁ (inner ℝ y v) = 1)} := by
      have h3 : MeasurableSet {y : E n | (y ∈ F ↔ g₁ (inner ℝ y v) = 1)} := h1_meas.iff h2_meas
      exact h3.compl
    have h3 : ∀ᵐ (x : E n), (shift x ∈ F ↔ g₁ (inner ℝ (shift x) v) = 1) := by
      have h6 : volume (shift ⁻¹' {y : E n | ¬(y ∈ F ↔ g₁ (inner ℝ y v) = 1)}) = 0 := by
        rw [hshift_mp.measure_preimage hBad_meas.nullMeasurableSet]
        simpa [ae_iff] using h2
      simpa [ae_iff] using h6
    filter_upwards [h1, h2, h3] with x h1x h2x h3x
    have h4 : inner ℝ (x + t • v) v = inner ℝ x v + t := by
      simp [inner_add_left, inner_smul_left, hv_unit] <;> ring
    by_cases h5 : g₁ (inner ℝ x v + t) = 1
    · have h7 : x + t • v ∈ F := h3x.mpr (by rw [h4] <;> exact h5)
      have h8 : x ∈ F := h1x h7
      have h9 : g₁ (inner ℝ x v) = 1 := h2x.mp h8
      rw [h5, h9] <;> norm_num
    · have h6 : g₁ (inner ℝ x v + t) = 0 := by
        have h7 : g₁ (inner ℝ x v + t) = 0 ∨ g₁ (inner ℝ x v + t) = 1 := hg₁_bool _
        rcases h7 with (h7 | h7) <;> tauto
      have h10 : 0 ≤ g₁ (inner ℝ x v) := by
        have h11 : g₁ (inner ℝ x v) = 0 ∨ g₁ (inner ℝ x v) = 1 := hg₁_bool _
        rcases h11 with (h11 | h11) <;> rw [h11] <;> norm_num
      rw [h6] <;> exact h10
  -- Step 4: Pushforward to 1D
  have h_push : ∀ (P : ℝ → Prop), MeasurableSet {s | P s} →
      (∀ᵐ (x : E n) ∂volume, P (inner ℝ x v)) → (∀ᵐ (s : ℝ) ∂volume, P s) := by
    intro P hP h
    let N : Set ℝ := {s | ¬P s}
    have hN_meas : MeasurableSet N := hP.compl
    have h1 : volume {x : E n | inner ℝ x v ∈ N} = 0 := by simpa [ae_iff, N] using h
    have h2 : volume N = 0 := (inner_pushforward_null hv_unit h_n_pos hN_meas).mp h1
    simpa [N, ae_iff] using h2
  have h_push' : ∀ (P : ℝ → Prop), MeasurableSet {s | P s} →
      (∀ᵐ (s : ℝ) ∂volume, P s) → (∀ᵐ (x : E n) ∂volume, P (inner ℝ x v)) := by
    intro P hP h
    let N : Set ℝ := {s | ¬P s}
    have hN_meas : MeasurableSet N := hP.compl
    have h1 : volume N = 0 := by simpa [ae_iff, N] using h
    have h2 : volume {x : E n | inner ℝ x v ∈ N} = 0 := (inner_pushforward_null hv_unit h_n_pos hN_meas).mpr h1
    simpa [ae_iff, N] using h2
  have h_real_mono : ∀ (t : ℝ), 0 < t → ∀ᵐ (s : ℝ) ∂volume, g₁ (s + t) ≤ g₁ s := by
    intro t ht
    let P : ℝ → Prop := fun s => g₁ (s + t) ≤ g₁ s
    have h1 : Measurable (fun s : ℝ => g₁ (s + t)) := hg₁_meas.comp (measurable_id.add measurable_const)
    have hP_meas : MeasurableSet {s | P s} :=
      h1.stronglyMeasurable.measurableSet_le hg₁_meas.stronglyMeasurable
    have h : ∀ᵐ (x : E n), P (inner ℝ x v) := h_en_mono t ht
    exact h_push P hP_meas h
  -- Step 5: Apply regularization lemma
  rcases bool_ae_noninc_to_step hg₁_meas hg₁_bool h_real_mono with ⟨g, hg_meas, hg_bool, hg_decr, hg_ae⟩
  -- Step 6: Transfer factorization
  let Q : ℝ → Prop := fun s => g s = g₁ s
  have hQ_meas : MeasurableSet {s | Q s} :=
    hg_meas.stronglyMeasurable.measurableSet_eq_fun hg₁_meas.stronglyMeasurable
  have hQ_ae : ∀ᵐ (s : ℝ), Q s := by
    exact hg_ae
  have h_transfer : ∀ᵐ (x : E n), g (inner ℝ x v) = g₁ (inner ℝ x v) :=
    h_push' Q hQ_meas hQ_ae
  have h_final : ∀ᵐ (x : E n) ∂volume, (x ∈ F ↔ g (inner ℝ x v) = 1) := by
    filter_upwards [h_factor1, h_transfer] with x hx1 hx2
    rw [hx2]
    exact hx1
  exact ⟨g, hg_meas, hg_bool, hg_decr, h_final⟩

-- ============================================================================
-- Lemma 5: Half-space characterization with monotone factorization
-- ============================================================================

/-- **Half-space characterization** (Maggi Proposition 15.15, conditional form).

If `χ_F(x) = g(inner(x,v))` a.e. for a non-increasing `g : ℝ → {0,1}`,
then `F` is a.e. a half-space, or a.e. empty, or a.e. full.

The monotonicity hypothesis is the key ingredient that distinguishes this
from the false statement "translation invariance + density ⇒ half-space".
In the GMT setting, monotonicity follows from `Dχ_F = v · |Dχ_F|` via
mollification (Maggi Prop 15.15, steps 1-5). -/
theorem halfSpace_characterization
    {n : ℕ} {F : Set (E n)} (hF : MeasurableSet F)
    {v : E n} (hv : ‖v‖ = 1)
    (g : ℝ → ℝ) (hg_meas : Measurable g)
    (hg_values : ∀ t, g t = 0 ∨ g t = 1)
    (hg_decr : ∀ s t, s ≤ t → g t ≤ g s)
    (h_factor : ∀ᵐ (x : E n) ∂volume, (x ∈ F ↔ g (inner ℝ x v) = 1)) :
    (∃ (α : ℝ), ∀ᵐ (z : E n) ∂volume, (z ∈ F ↔ inner ℝ z v < α)) ∨
    (∀ᵐ (z : E n) ∂volume, z ∉ F) ∨
    (∀ᵐ (z : E n) ∂volume, z ∈ F) := by
  have h_class := monotone_bool_function_classification hg_meas hg_values hg_decr
  rcases h_class with (h_case | h_zero | h_one)
  · rcases h_case with ⟨α, hg_pointwise⟩
    let f : (E n) →L[ℝ] ℝ :=
      { toFun := fun x => inner ℝ x v
        map_add' := fun x y => inner_add_left x y v
        map_smul' := fun c x => by simp [inner_smul_left]
        cont := continuous_id.inner continuous_const }
    have hv' : v ≠ 0 := by
      intro h; rw [h] at hv; simp at hv <;> linarith
    have hf_surj : Function.Surjective f := by
      intro r
      let c : ℝ := r / ‖v‖ ^ 2
      use c • v
      have h4 : f (c • v) = c * f v := by exact f.map_smul c v
      rw [h4]
      have h5 : f v = ‖v‖ ^ 2 := by simp [f, inner_self_eq_norm_sq_to_K]
      rw [h5]
      have h6 : ‖v‖ ^ 2 ≠ 0 := by
        have h7 : 0 < ‖v‖ := by rw [hv] <;> norm_num
        positivity
      have h_goal : c * ‖v‖ ^ 2 = r := by dsimp only [c]; field_simp [h6] <;> ring
      exact h_goal
    let K : Submodule ℝ (E n) := f.toLinearMap.ker
    have hK_proper : K ≠ ⊤ := by
      intro h
      have h1 : v ∈ K := by rw [h] <;> simp
      have h2 : f v = 0 := by
        have h3 : f.toLinearMap v = 0 := h1
        simpa using h3
      have h4 : f v = ‖v‖ ^ 2 := by simp [f, inner_self_eq_norm_sq_to_K]
      rw [h4] at h2
      have h5 : ‖v‖ ^ 2 = 0 := by linarith
      have h6 : ‖v‖ = 0 := by nlinarith
      rw [h6] at hv <;> linarith
    obtain ⟨p, hp⟩ := hf_surj α
    let H : AffineSubspace ℝ (E n) := AffineSubspace.mk' p K
    have hH_eq : (H : Set (E n)) = {z : E n | inner ℝ z v = α} := by
      ext z
      have h_iff : z ∈ (H : Set (E n)) ↔ z - p ∈ K := by
        have h_def : (H : Set (E n)) = {q | q + -p ∈ K} := by rfl
        rw [h_def]; simp [sub_eq_add_neg] <;> rfl
      rw [h_iff]
      have h2 : (z - p ∈ K) ↔ f (z - p) = 0 := by simp [K] <;> rfl
      rw [h2]
      have h3 : f (z - p) = f z - f p := by rw [f.map_sub z p] <;> rfl
      rw [h3, hp] <;> simp [f, sub_eq_zero]
    have hH_ne_top : H ≠ ⊤ := by
      intro h
      have h_all : ∀ (x : E n), x ∈ (H : Set (E n)) := by rw [h] <;> simp
      have hK_top : K = ⊤ := by
        apply Submodule.eq_top_iff'.mpr
        intro x
        have h4 : x + p ∈ (H : Set (E n)) := h_all (x + p)
        have h5 : (x + p) - p ∈ K := by
          have h_iff : ∀ (q : E n), q ∈ (H : Set (E n)) ↔ q - p ∈ K := by
            intro q
            have h_def : (H : Set (E n)) = {q | q + -p ∈ K} := by rfl
            rw [h_def]; simp [sub_eq_add_neg] <;> rfl
          exact (h_iff (x + p)).mp h4
        have h6 : (x + p) - p = x := by simp
        rw [h6] at h5; exact h5
      exact hK_proper hK_top
    have h_hyperplane_null : volume (H : Set (E n)) = 0 :=
      MeasureTheory.Measure.addHaar_affineSubspace volume H hH_ne_top
    have h_ae_ne : ∀ᵐ (z : E n) ∂volume, inner ℝ z v ≠ α := by
      rw [hH_eq] at h_hyperplane_null
      simpa [ae_iff] using h_hyperplane_null
    have h_main : ∀ᵐ (z : E n) ∂volume, (z ∈ F ↔ inner ℝ z v < α) := by
      filter_upwards [h_factor, h_ae_ne] with z hz_f hz_ne
      have h1 : (z ∈ F ↔ g (inner ℝ z v) = 1) := hz_f
      have h2 : g (inner ℝ z v) = Set.indicator (Set.Iio α) (fun _ => (1 : ℝ)) (inner ℝ z v) :=
        hg_pointwise (inner ℝ z v) hz_ne
      rw [h1, h2]; simp [Set.indicator, Set.mem_Iio] <;> tauto
    exact Or.inl ⟨α, h_main⟩
  · have h_main : ∀ᵐ (z : E n) ∂volume, z ∉ F := by
      filter_upwards [h_factor] with z hz_f
      have h1 : (z ∈ F ↔ g (inner ℝ z v) = 1) := hz_f
      have h2 : g (inner ℝ z v) = 0 := h_zero (inner ℝ z v)
      rw [h1, h2] <;> simp
    exact Or.inr (Or.inl h_main)
  · have h_main : ∀ᵐ (z : E n) ∂volume, z ∈ F := by
      filter_upwards [h_factor] with z hz_f
      have h1 : (z ∈ F ↔ g (inner ℝ z v) = 1) := hz_f
      have h2 : g (inner ℝ z v) = 1 := h_one (inner ℝ z v)
      rw [h1, h2] <;> simp
    exact Or.inr (Or.inr h_main)

/- NOTE: `halfspace_threshold_from_density` is temporarily disabled due to
   multiple build errors. It will be restored in a separate file. -/

end Geometry.Perimeter
