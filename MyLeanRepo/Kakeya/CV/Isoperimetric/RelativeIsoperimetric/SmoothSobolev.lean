import MyLeanRepo.Kakeya.CV.Isoperimetric.RelativeIsoperimetric.Cutoff
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.Mollification
import Mathlib.Tactic


/-!
# Weak Relative Isoperimetric Inequality via Gagliardo–Nirenberg–Sobolev

Proves the weak relative isoperimetric inequality:
  `|E ∩ B(x₀,r)|^{(n-1)/n} ≤ C(n)·(P(E;B(x₀,2r)) + (1/r)·|E ∩ B(x₀,2r)|)`

## Route

1. **Sobolev inequality** (Mathlib): `‖v‖_{n/(n-1)} ≤ C·‖∇v‖₁` for smooth compactly supported v.
2. **Cutoff**: Apply to v = φ·u where φ = 1 on B_r, 0 outside B_{2r}, ‖∇φ‖ ≤ C/r.
3. **Product rule**: `∇v = φ·∇u + u·∇φ`, split into gradient + zero-order terms.

## Main results

- `smooth_weak_relative_isoperimetric`: inequality for smooth bounded functions
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ}

/-! ### Holder conjugate exponent -/

/-- The Sobolev conjugate exponent p = n/(n-1). -/
noncomputable def sobolevP (n : ℕ) : NNReal := (n : NNReal).conjExponent

lemma sobolevP_pos (hn : 2 ≤ n) : 0 < sobolevP n := by
  have h1 : 1 < (n : NNReal) := by exact_mod_cast hn
  have h_hp : NNReal.HolderConjugate (n : NNReal) ((n : NNReal).conjExponent) :=
    NNReal.HolderConjugate.conjExponent h1
  have h_pos : 0 < ((n : NNReal).conjExponent : ℝ) := h_hp.coe.symm.pos
  exact_mod_cast h_pos

lemma sobolevP_holderConjugate (hn : 2 ≤ n) :
    NNReal.HolderConjugate (Module.finrank ℝ (E n)) (sobolevP n) := by
  have h1 : 1 < (n : NNReal) := by exact_mod_cast hn
  have h2 : Module.finrank ℝ (E n) = n := by simp
  rw [h2]
  exact NNReal.HolderConjugate.conjExponent h1

/-! ### Smooth weak relative isoperimetric inequality -/

/-- **Smooth weak relative isoperimetric inequality**.

For smooth `u : ℝⁿ → ℝ` with `0 ≤ u ≤ 1`,
`‖u‖_{L^{n/(n-1)}(B_r)} ≤ C(n)·(‖∇u‖_{L¹(B_{2r})} + (1/r)·‖u‖_{L¹(B_{2r})})`. -/
lemma smooth_weak_relative_isoperimetric
    {u : E n → ℝ} (hu : ContDiff ℝ 1 u)
    (h_bound : ∀ x, 0 ≤ u x ∧ u x ≤ 1)
    {x₀ : E n} {r : ℝ} (hr : 0 < r) (hn : 2 ≤ n) :
    eLpNorm u (sobolevP n) (volume.restrict (ball x₀ r)) ≤
    relIsoConst n * (eLpNorm (fderiv ℝ u) 1 (volume.restrict (ball x₀ (2 * r))) +
      ENNReal.ofReal (1 / r) * eLpNorm u 1 (volume.restrict (ball x₀ (2 * r)))) := by
  rcases exists_cutoff x₀ hr with ⟨φ, C_φ, hC_φ_nonneg, hC_φ_eq, hφ_smooth, hφ_one, hφ_zero, hφ_bounds, hφ_fderiv⟩
  let v : E n → ℝ := fun y => φ y * u y
  have hv_smooth : ContDiff ℝ 1 v := hφ_smooth.mul hu
  have hφ_support : Function.support φ ⊆ closedBall x₀ (2 * r) := by
    intro x hx
    have h3 : φ x ≠ 0 := hx
    by_contra h4
    have h5 : x ∉ ball x₀ (2 * r) := by
      intro hball
      have h6 : x ∈ closedBall x₀ (2 * r) := by
        simpa [closedBall, mem_closedBall, mem_ball] using le_of_lt hball
      exact h4 h6
    have h6 : φ x = 0 := hφ_zero x h5
    exact h3 h6
  have hv_support : HasCompactSupport v := by
    have h1 : Function.support v ⊆ Function.support φ := by
      intro x hx
      have hmul : φ x * u x ≠ 0 := hx
      have hφ : φ x ≠ 0 := (mul_ne_zero_iff.mp hmul).1
      exact hφ
    have hts_closed : IsClosed (tsupport φ) := isClosed_tsupport φ
    have hts_sub : tsupport φ ⊆ closedBall x₀ (2 * r) := closure_minimal hφ_support isClosed_closedBall
    have h2 : IsCompact (tsupport φ) := IsCompact.of_isClosed_subset (isCompact_closedBall x₀ (2 * r)) hts_closed hts_sub
    have h3 : HasCompactSupport φ := h2
    exact h3.mono h1
  let p : NNReal := sobolevP n
  have hp := sobolevP_holderConjugate hn
  have hp_pos' : p ≠ 0 := (sobolevP_pos hn).ne'
  let C_S : ENNReal :=
    (↑(MeasureTheory.eLpNormLESNormFDerivOneConst (E := E n) volume (p : ℝ)) : ENNReal)
  have h_sobolev : eLpNorm v p volume ≤ C_S * eLpNorm (fderiv ℝ v) 1 volume :=
    MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one (μ := volume) hv_smooth hv_support hp
  have h_left : eLpNorm u p (volume.restrict (ball x₀ r)) ≤ eLpNorm v p volume := by
    have h1 : ∀ᵐ y ∂volume.restrict (ball x₀ r), v y = u y := by
      filter_upwards [self_mem_ae_restrict isOpen_ball.measurableSet] with y hy
      have h2 : φ y = 1 := hφ_one y hy
      simp [v, h2]
    have h4 : eLpNorm v p (volume.restrict (ball x₀ r)) = eLpNorm u p (volume.restrict (ball x₀ r)) := by
      apply eLpNorm_congr_ae
      exact h1
    have h5 : eLpNorm v p (volume.restrict (ball x₀ r)) ≤ eLpNorm v p volume :=
      eLpNorm_mono_measure v Measure.restrict_le_self
    rw [h4] at h5
    exact h5
  let f1 : E n → E n →L[ℝ] ℝ := fun y => φ y • fderiv ℝ u y
  let f2 : E n → E n →L[ℝ] ℝ := fun y => u y • fderiv ℝ φ y
  have h_fderiv_v : ∀ y, fderiv ℝ v y = f1 y + f2 y := by
    intro y
    have h_diff_φ : DifferentiableAt ℝ φ y := hφ_smooth.differentiable (by norm_num) |>.differentiableAt
    have h_diff_u : DifferentiableAt ℝ u y := (hu.differentiable (by norm_num)).differentiableAt
    exact fderiv_mul h_diff_φ h_diff_u
  have h_cont1 : Continuous f1 := by
    have h_c1 : Continuous φ := hφ_smooth.continuous
    have h_c2 : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
    exact h_c1.smul h_c2
  have h_cont2 : Continuous f2 := by
    have h_c1 : Continuous u := hu.continuous
    have h_c2 : Continuous (fderiv ℝ φ) := hφ_smooth.continuous_fderiv (by norm_num)
    exact h_c1.smul h_c2
  have h_tri : eLpNorm (fderiv ℝ v) 1 volume ≤ eLpNorm f1 1 volume + eLpNorm f2 1 volume := by
    have h_eq : eLpNorm (fderiv ℝ v) 1 volume = eLpNorm (fun y => f1 y + f2 y) 1 volume := by
      apply eLpNorm_congr_ae
      filter_upwards with y
      rw [h_fderiv_v y] <;> rfl
    rw [h_eq]
    have h1 : eLpNorm (fun y => f1 y + f2 y) 1 volume = ∫⁻ y, ‖f1 y + f2 y‖ₑ :=
      eLpNorm_one_eq
    have h2 : eLpNorm f1 1 volume = ∫⁻ y, ‖f1 y‖ₑ := eLpNorm_one_eq
    have h3 : eLpNorm f2 1 volume = ∫⁻ y, ‖f2 y‖ₑ := eLpNorm_one_eq
    rw [h1, h2, h3]
    have h4 : Measurable (fun y : E n => ‖f1 y‖ₑ) := h_cont1.measurable.enorm
    have h5 : Measurable (fun y : E n => ‖f2 y‖ₑ) := h_cont2.measurable.enorm
    have h6 : ∫⁻ y, ‖f1 y + f2 y‖ₑ ≤ ∫⁻ y, (‖f1 y‖ₑ + ‖f2 y‖ₑ) :=
      lintegral_mono (fun y => enorm_add_le (f1 y) (f2 y))
    have h7 : ∫⁻ y, (‖f1 y‖ₑ + ‖f2 y‖ₑ) = (∫⁻ y, ‖f1 y‖ₑ) + (∫⁻ y, ‖f2 y‖ₑ) :=
      MeasureTheory.lintegral_add_left h4 _
    rw [h7] at h6
    exact h6
  have h_term1 : eLpNorm f1 1 volume ≤
      eLpNorm (fderiv ℝ u) 1 (volume.restrict (ball x₀ (2 * r))) :=
    eLpNorm_scalar_mult_bound hφ_bounds hφ_zero
  have h_term2 : eLpNorm f2 1 volume ≤
      ENNReal.ofReal (C_φ / r) * eLpNorm u 1 (volume.restrict (ball x₀ (2 * r))) :=
    eLpNorm_weighted_fderiv_cutoff_bound hu.continuous.measurable hn hr C_φ hC_φ_nonneg
      hφ_smooth hφ_zero hφ_fderiv
  have h_right : eLpNorm (fderiv ℝ v) 1 volume ≤
      eLpNorm (fderiv ℝ u) 1 (volume.restrict (ball x₀ (2 * r))) +
      ENNReal.ofReal (C_φ / r) * eLpNorm u 1 (volume.restrict (ball x₀ (2 * r))) := by
    calc eLpNorm (fderiv ℝ v) 1 volume
      ≤ eLpNorm f1 1 volume + eLpNorm f2 1 volume := h_tri
    _ ≤ eLpNorm (fderiv ℝ u) 1 (volume.restrict (ball x₀ (2 * r))) +
          ENNReal.ofReal (C_φ / r) * eLpNorm u 1 (volume.restrict (ball x₀ (2 * r))) :=
      add_le_add h_term1 h_term2
  set A : ENNReal := eLpNorm (fderiv ℝ u) (1 : ENNReal) (volume.restrict (ball x₀ (2 * r))) with hA
  set B : ENNReal := eLpNorm (u : E n → ℝ) (1 : ENNReal) (volume.restrict (ball x₀ (2 * r))) with hB
  have h_p_eq : sobolevP n = (n : NNReal) / ((n : NNReal) - 1) := by
    rw [sobolevP, NNReal.conjExponent]
  have h_base : baseRelIsoConst n = C_S * ENNReal.ofReal (max (standardCutoffBound n) 1) := by
    rw [baseRelIsoConst, dif_pos hn]
    <;> simp [C_S, h_p_eq] <;> rfl
  have hCSM : C_S * ENNReal.ofReal (max (standardCutoffBound n) 1) ≤ relIsoConst n := by
    have hn1 : (1 : ENNReal) ≤ (n : ENNReal) := by exact_mod_cast (show 1 ≤ n from by omega)
    rw [relIsoConst, h_base]
    have h : C_S * ENNReal.ofReal (max (standardCutoffBound n) 1) ≤
        (n : ENNReal) * (C_S * ENNReal.ofReal (max (standardCutoffBound n) 1)) := by
      calc C_S * ENNReal.ofReal (max (standardCutoffBound n) 1)
        = (1 : ENNReal) * (C_S * ENNReal.ofReal (max (standardCutoffBound n) 1)) := by simp
      _ ≤ (n : ENNReal) * (C_S * ENNReal.ofReal (max (standardCutoffBound n) 1)) := by
        gcongr
    exact h
  have h_final : C_S * (A + ENNReal.ofReal (C_φ / r) * B) ≤
      relIsoConst n * (A + ENNReal.ofReal (1 / r) * B) :=
    relIsoConst_match n hn C_S C_φ hC_φ_eq hCSM r hr A B
  calc eLpNorm u p (volume.restrict (ball x₀ r))
    ≤ eLpNorm v p volume := h_left
  _ ≤ C_S * eLpNorm (fderiv ℝ v) 1 volume := h_sobolev
  _ ≤ C_S * (A + ENNReal.ofReal (C_φ / r) * B) :=
      mul_le_mul_left' h_right C_S
  _ ≤ relIsoConst n * (A + ENNReal.ofReal (1 / r) * B) := h_final

end Geometry
