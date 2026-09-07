/-
# Directional Variation of Blow-Up Vanishes

At a true reduced boundary point `x` with normal `ν`, for every direction `w`
orthogonal to `ν`, the local directional variation of the blow-ups tends to
zero:

```
directionalVariationIn (blowUp U x r) w K → 0  as r → 0⁺
```

for every compact set `K`.

## Proof route

1. **Scaling**: The local directional variation scales as
   `directionalVariationIn (blowUp U x r) w K = r^{1-n} · directionalVariationIn U w (x + r·K)`
   (up to monotonicity in K).

2. **Measure bound**: `directionalVariationIn U w Ω ≤ ρ(Ω)` where
   `ρ = perimeterMeasure U.withDensity (fun y => |inner(w, ν(y))|)`.

3. **Besicovitch differentiation**: At `μ`-a.e. `x`,
   `ρ(closedBall x r) / μ(closedBall x r) → |inner(w, ν(x))| = 0`.

4. **Upper density bound**: `μ(closedBall x r) ≤ C · r^{n-1}` for small `r`.

5. **Combine**: `r^{1-n} · ρ(closedBall x (rR)) ≤ ε(r) · C · R^{n-1} → 0`.

## Dependencies

- `DirectionalVariationLemmas.lean`: scaling of directional variation
- `DistributionalDerivative.lean`: `distributionalDerivative`, `perimeterMeasure`
- `TrueReducedBoundary.lean`: polar decomposition, `trueReducedBoundary`
- `perimeter_density_upper_bound`: upper density bound (not yet formalized)

## References

- Maggi, *Sets of Finite Perimeter*, Theorem 15.5, Step 3
- Ambrosio-Fusco-Pallara, *Functions of BV*, Theorem 3.59
-/

import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.DirectionalVariationLemmas
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DistributionalDerivative
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.TrueReducedBoundary
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DirectionalVariationScaling
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpScaling
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.M4DirectionalUpgrade
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.RBCEasyLemmas
import Mathlib.Tactic

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

variable {n : ℕ}

open Perimeter

-- ============================================================================
-- Step 3: Directional variation bounded by weighted perimeter measure
-- ============================================================================

/-- **Scalar directional measure**: `μ_w(A) := inner ℝ w (Dχ_U A)`. -/
noncomputable def scalarDirectionalMeasure (U : Set (E n)) (w : E n) :
    VectorMeasure (E n) ℝ :=
  (distributionalDerivative U).mapRange (innerBilinear w) (innerBilinear w).continuous

/-- The scalar directional measure has density `inner(w, measureTheoreticNormal U)`
w.r.t. the perimeter measure. -/
lemma scalarDirectionalMeasure_withDensity (U : Set (E n)) (hU : MeasurableSet U)
    (hfin : perimeter U < ⊤) (w : E n) :
    scalarDirectionalMeasure U w =
      (perimeterMeasure U).withDensityᵥ (fun x => inner ℝ w (measureTheoreticNormal U x)) := by
  let D := distributionalDerivative U
  let μ := perimeterMeasure U
  let f := measureTheoreticNormal U
  have h_decomp : D = μ.withDensityᵥ f :=
    (measureTheoreticNormal_withDensity (hfin := hfin)).2
  have h_int_f : Integrable f μ :=
    (measureTheoreticNormal_withDensity (hfin := hfin)).1
  let g : E n → ℝ := fun x => inner ℝ w (f x)
  have h_int_g : Integrable g μ :=
    (innerBilinear w).integrable_comp h_int_f

  ext1 A hA
  have h1 : scalarDirectionalMeasure U w A = inner ℝ w (D A) := by rfl
  rw [h1, h_decomp]
  have h2 : (μ.withDensityᵥ f) A = ∫ x in A, f x ∂μ :=
    withDensityᵥ_apply h_int_f hA
  rw [h2]
  have h3 : inner ℝ w (∫ x in A, f x ∂μ) = ∫ x in A, inner ℝ w (f x) ∂μ := by
    exact (innerBilinear w).integral_comp_comm (μ := μ.restrict A) h_int_f.integrableOn |>.symm
  rw [h3]
  have h4 : (μ.withDensityᵥ g) A = ∫ x in A, g x ∂μ :=
    withDensityᵥ_apply h_int_g hA
  rw [h4]

/-- **Directional variation is bounded by the weighted perimeter measure.**

For any set `Ω`,
`directionalVariationIn U w Ω ≤ ∫_Ω |inner(w, ν(y))| d(perimeterMeasure U)`,
where `ν = measureTheoreticNormal U`.

This follows from the polar decomposition of the distributional derivative
and the integral representation of directional variation. -/
lemma directionalVariationIn_le_weighted_perimeter
    {U : Set (E n)} (hU : MeasurableSet U) (hfin : perimeter U < ⊤)
    (w : E n) {Ω : Set (E n)} (hΩ : MeasurableSet Ω) :
    directionalVariationIn U w Ω ≤
      (perimeterMeasure U).withDensity
        (fun y : E n => ENNReal.ofReal |inner ℝ w (measureTheoreticNormal U y)|) Ω := by
  let D := distributionalDerivative U
  let μ := perimeterMeasure U
  let f := measureTheoreticNormal U
  let μ_w := scalarDirectionalMeasure U w
  let g : E n → ℝ := fun x => inner ℝ w (f x)

  have hμ_w_eq : μ_w = μ.withDensityᵥ g :=
    scalarDirectionalMeasure_withDensity U hU hfin w

  have h_int_f : Integrable f μ :=
    (measureTheoreticNormal_withDensity (hfin := hfin)).1
  have h_int_g : Integrable g μ :=
    (innerBilinear w).integrable_comp h_int_f

  have h_var_le : μ_w.variation ≤ μ.withDensity (fun x => ENNReal.ofReal |g x|) := by
    rw [hμ_w_eq]
    have h_main := withDensityᵥ_variation_le h_int_g
    have h_eq : μ.withDensity (fun x => ENNReal.ofReal ‖g x‖) = μ.withDensity (fun x => ENNReal.ofReal |g x|) := by
      congr with y <;> simp [Real.norm_eq_abs]
    rw [h_eq] at h_main
    exact h_main

  apply iSup_le
  intro φ
  let ψ_vec : E n → E n := fun x => φ.val.toFun x • w
  have hψ_smooth : ContDiff ℝ ∞ ψ_vec := φ.val.smooth.smul_const w
  have hψ_supp : HasCompactSupport ψ_vec := by
    have h : Function.support ψ_vec ⊆ Function.support φ.val.toFun := by
      intro x hx
      simp only [Function.mem_support, ψ_vec] at hx ⊢
      by_contra h2
      have h3 : φ.val.toFun x = 0 := by simpa [Function.mem_support] using h2
      rw [h3] at hx <;> simp at hx
    exact φ.val.compact.mono h

  have h_eq1 : ∫ x in U, fderiv ℝ φ.val.toFun x w =
      ∫ᵛ x, ψ_vec x ∂[innerBilinear; D] := by
    have h : ∫ᵛ x, ψ_vec x ∂[innerBilinear; D] = ∫ x in U, divergence ψ_vec x :=
      distributionalDerivative_integral_formula U hfin ψ_vec hψ_smooth hψ_supp
    have hdiv : divergence ψ_vec = fun x => fderiv ℝ φ.val.toFun x w :=
      divergence_smul_const φ.val.smooth
    rw [h, hdiv] <;> rfl

  let L : ℝ →L[ℝ] E n :=
    { toFun := fun c => c • w
      map_add' := by intro a b; simp [add_smul] <;> ring
      map_smul' := by intro c a; simp [smul_smul] <;> ring }
  let T1 := D.transpose innerBilinear
  let flipLSMul : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.lsmul ℝ ℝ).flip
  let T2 := μ_w.transpose flipLSMul

  have hT2 : ∀ (s : Set (E n)) (c : ℝ), T2 s c = c * μ_w s := by
    intro s c
    have h1 : T2 s = flipLSMul.flip (μ_w s) := by
      simp [T2, VectorMeasure.transpose, VectorMeasure.mapRange_apply]
      <;> rfl
    have h2 : T2 s c = flipLSMul c (μ_w s) := by
      rw [h1]
      <;> simp [ContinuousLinearMap.flip_apply]
      <;> rfl
    rw [h2]
    have h3 : flipLSMul c (μ_w s) = c * μ_w s := by
      simp [flipLSMul, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply] <;> ring
    exact h3

  have h_comp : ∀ (s : Set (E n)), (T1 s).comp L = T2 s := by
    intro s
    apply ContinuousLinearMap.ext
    intro c
    have h1 : (T1 s).comp L c = innerBilinear (c • w) (D s) := by rfl
    have h2 : T2 s c = (ContinuousLinearMap.lsmul ℝ ℝ) c (μ_w s) := by
      have h21 : T2 s c = c * μ_w s := hT2 s c
      rw [h21]
      simp [ContinuousLinearMap.lsmul_apply] <;> ring
    rw [h1, h2]
    have h3 : innerBilinear (c • w) (D s) = c * innerBilinear w (D s) := by
      simp [innerBilinear_apply, inner_smul_left] <;> ring
    have h4 : μ_w s = innerBilinear w (D s) := by rfl
    rw [h3, h4]
    simp [ContinuousLinearMap.lsmul_apply] <;> ring

  have h_dom1 : DominatedFinMeasAdditive D.variation T1 ‖(innerBilinear : (E n) →L[ℝ] (E n) →L[ℝ] ℝ)‖ :=
    dominatedFinMeasAdditive_cbmApplyMeasure D (innerBilinear : (E n) →L[ℝ] (E n) →L[ℝ] ℝ)
  have h_dom2 : DominatedFinMeasAdditive D.variation T2 ‖w‖ := by
    refine ⟨fun s t hs ht hμs hμt hdisj => ?_, fun s hs hsf => ?_⟩
    · have h_add : T2 (s ∪ t) = T2 s + T2 t := by
        apply ContinuousLinearMap.ext
        intro c
        have hμ : μ_w (s ∪ t) = μ_w s + μ_w t :=
          VectorMeasure.of_union hdisj hs ht
        have h1 : T2 (s ∪ t) c = c * μ_w (s ∪ t) := hT2 (s ∪ t) c
        have h2 : (T2 s + T2 t) c = T2 s c + T2 t c := by
          simp [add_apply]
        rw [h1, h2]
        have h3 : T2 s c = c * μ_w s := hT2 s c
        have h4 : T2 t c = c * μ_w t := hT2 t c
        simp [h3, h4, hμ, mul_add] <;> ring
      exact h_add
    · have h_norm : ‖T2 s‖ = |μ_w s| := by
        have h_apply : ∀ (c : ℝ), T2 s c = c * μ_w s := by intro c; exact hT2 s c
        have h_le : ‖T2 s‖ ≤ |μ_w s| := by
          have hC : 0 ≤ |μ_w s| := abs_nonneg _
          have h_bound : ∀ (c : ℝ), ‖T2 s c‖ ≤ |μ_w s| * ‖c‖ := by
            intro c
            have h : |T2 s c| = |c| * |μ_w s| := by
              rw [h_apply c, abs_mul]
            have h' : ‖T2 s c‖ = |c| * |μ_w s| := by
              simpa [Real.norm_eq_abs] using h
            rw [h']
            have h_norm_c : ‖c‖ = |c| := by simp [Real.norm_eq_abs]
            rw [h_norm_c]
            exact (mul_comm _ _).le
          exact (T2 s).opNorm_le_bound hC h_bound
        have h_ge : |μ_w s| ≤ ‖T2 s‖ := by
          have h : ‖T2 s (1 : ℝ)‖ ≤ ‖T2 s‖ * ‖(1 : ℝ)‖ :=
            ContinuousLinearMap.le_opNorm (T2 s) (1 : ℝ)
          simpa [h_apply 1, norm_one] using h
        exact le_antisymm h_le h_ge
      calc ‖T2 s‖
        = |μ_w s| := h_norm
      _ ≤ ‖w‖ * ‖D s‖ := by
          have h : |μ_w s| ≤ ‖w‖ * ‖D s‖ := by
            have h5 : μ_w s = inner ℝ w (D s) := by rfl
            rw [h5]
            exact abs_real_inner_le_norm w (D s)
          exact h
      _ ≤ ‖w‖ * (D.variation s).toReal := by
          apply mul_le_mul_of_nonneg_left
          · have h_v : ‖D s‖ₑ ≤ D.variation s :=
              VectorMeasure.enorm_measure_le_variation D s
            have h_eq : ‖D s‖ₑ = ENNReal.ofReal ‖D s‖ := by
              simp
            rw [h_eq] at h_v
            have h_ne : ENNReal.ofReal ‖D s‖ ≠ ⊤ := ENNReal.ofReal_ne_top
            have h_fin_univ : D.variation Set.univ < ⊤ := by
              have h_eq2 : perimeter U = D.variation Set.univ := perimeter_eq_variation U hfin
              rw [←h_eq2]; exact hfin
            have hD_ne : D.variation s ≠ ⊤ :=
              ((measure_mono (subset_univ _)).trans_lt h_fin_univ).ne
            have h_result : (ENNReal.ofReal ‖D s‖).toReal ≤ (D.variation s).toReal :=
              (ENNReal.toReal_le_toReal h_ne hD_ne).mpr h_v
            have h_toReal : (ENNReal.ofReal ‖D s‖).toReal = ‖D s‖ :=
              ENNReal.toReal_ofReal (norm_nonneg _)
            rw [h_toReal] at h_result
            exact h_result
          · positivity
  have h_dom2' : DominatedFinMeasAdditive μ_w.variation T2 1 := by
    refine ⟨fun s t hs ht hμs hμt hdisj => ?_, fun s hs hsf => ?_⟩
    · have h_add : T2 (s ∪ t) = T2 s + T2 t := by
        apply ContinuousLinearMap.ext
        intro c
        have hμ : μ_w (s ∪ t) = μ_w s + μ_w t :=
          VectorMeasure.of_union hdisj hs ht
        have h1 : T2 (s ∪ t) c = c * μ_w (s ∪ t) := hT2 (s ∪ t) c
        have h2 : (T2 s + T2 t) c = T2 s c + T2 t c := by
          simp [add_apply]
        rw [h1, h2]
        have h3 : T2 s c = c * μ_w s := hT2 s c
        have h4 : T2 t c = c * μ_w t := hT2 t c
        simp [h3, h4, hμ, mul_add] <;> ring
      exact h_add
    · have h_norm : ‖T2 s‖ = |μ_w s| := by
        have h_apply : ∀ (c : ℝ), T2 s c = c * μ_w s := by intro c; exact hT2 s c
        have h_le : ‖T2 s‖ ≤ |μ_w s| := by
          have hC : 0 ≤ |μ_w s| := abs_nonneg _
          have h_bound : ∀ (c : ℝ), ‖T2 s c‖ ≤ |μ_w s| * ‖c‖ := by
            intro c
            have h : |T2 s c| = |c| * |μ_w s| := by
              rw [h_apply c, abs_mul]
            have h' : ‖T2 s c‖ = |c| * |μ_w s| := by
              simpa [Real.norm_eq_abs] using h
            rw [h']
            have h_norm_c : ‖c‖ = |c| := by simp [Real.norm_eq_abs]
            rw [h_norm_c]
            exact (mul_comm _ _).le
          exact (T2 s).opNorm_le_bound hC h_bound
        have h_ge : |μ_w s| ≤ ‖T2 s‖ := by
          have h : ‖T2 s (1 : ℝ)‖ ≤ ‖T2 s‖ * ‖(1 : ℝ)‖ :=
            ContinuousLinearMap.le_opNorm (T2 s) (1 : ℝ)
          simpa [h_apply 1, norm_one] using h
        exact le_antisymm h_le h_ge
      calc ‖T2 s‖
        = |μ_w s| := h_norm
      _ ≤ (μ_w.variation s).toReal := by
          have h_v : ‖μ_w s‖ₑ ≤ μ_w.variation s :=
            VectorMeasure.enorm_measure_le_variation μ_w s
          have h_eq : ‖μ_w s‖ₑ = ENNReal.ofReal |μ_w s| :=
            Real.enorm_eq_ofReal_abs (μ_w s)
          rw [h_eq] at h_v
          have h_ne : ENNReal.ofReal |μ_w s| ≠ ⊤ := ENNReal.ofReal_ne_top
          have hμw_ne : μ_w.variation s ≠ ⊤ := by
            have h1 : μ_w.variation Set.univ ≤ μ.withDensity (fun x => ENNReal.ofReal |g x|) Set.univ := h_var_le Set.univ
            have h3 : HasFiniteIntegral g μ := h_int_g.hasFiniteIntegral
            have h4 : (fun x : E n => ENNReal.ofReal |g x|) = fun x : E n => ‖g x‖ₑ := by
              funext y
              have h5 : ‖g y‖ₑ = ENNReal.ofReal |g y| := Real.enorm_eq_ofReal_abs (g y)
              rw [h5]
            have h2 : μ.withDensity (fun x => ENNReal.ofReal |g x|) Set.univ < ⊤ := by
              rw [h4]
              have h_eq : μ.withDensity (fun x : E n => ‖g x‖ₑ) Set.univ = ∫⁻ x, ‖g x‖ₑ ∂μ := by
                rw [withDensity_apply _ MeasurableSet.univ]
                <;> simp
              rw [h_eq]
              have h3' : ∫⁻ x, ‖g x‖ₑ ∂μ < ⊤ :=
                (MeasureTheory.hasFiniteIntegral_iff_enorm).mp h3
              exact h3'
            have h5 : μ_w.variation Set.univ < ⊤ := h1.trans_lt h2
            exact ((measure_mono (subset_univ _)).trans_lt h5).ne
          have h_result : (ENNReal.ofReal |μ_w s|).toReal ≤ (μ_w.variation s).toReal :=
            (ENNReal.toReal_le_toReal h_ne hμw_ne).mpr h_v
          have h_toReal : (ENNReal.ofReal |μ_w s|).toReal = |μ_w s| :=
            ENNReal.toReal_ofReal (abs_nonneg _)
          rw [h_toReal] at h_result
          exact h_result
      _ ≤ (1 : ℝ) * (μ_w.variation s).toReal := by simp

  haveI : IsFiniteMeasure D.variation := by
    have h_eq : D.variation Set.univ = perimeter U := (perimeter_eq_variation U hfin).symm
    have h1 : D.variation Set.univ < ⊤ := by
      rw [h_eq]
      exact hfin
    exact ⟨h1⟩
  have hφ_int : Integrable φ.val.toFun D.variation :=
    φ.val.smooth.continuous.integrable_of_hasCompactSupport (μ := D.variation) φ.val.compact

  have h_comp' : (fun s => T1 s ∘SL L) = T2 := by
    funext s
    exact h_comp s
  let hT_comp : DominatedFinMeasAdditive D.variation (fun s => (T1 s).comp L) (‖(innerBilinear : (E n) →L[ℝ] (E n) →L[ℝ] ℝ)‖ * ‖L‖) := by
    refine ⟨fun s t hs ht hμs hμt hdisj => ?_, fun s hs hsf => ?_⟩
    · have h9 := h_dom1.1 s t hs ht hμs hμt hdisj
      simpa using congr_arg (fun g : (E n) →L[ℝ] ℝ => g.comp L) h9
    · have h10 : ‖T1 s‖ ≤ ‖(innerBilinear : (E n) →L[ℝ] (E n) →L[ℝ] ℝ)‖ * D.variation.real s := h_dom1.2 s hs hsf
      calc ‖(T1 s).comp L‖
        ≤ ‖T1 s‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖(innerBilinear : (E n) →L[ℝ] (E n) →L[ℝ] ℝ)‖ * D.variation.real s) * ‖L‖ := by gcongr
      _ = (‖(innerBilinear : (E n) →L[ℝ] (E n) →L[ℝ] ℝ)‖ * ‖L‖) * D.variation.real s := by ring
  have h_eq2 : setToFun D.variation T2 h_dom2 φ.val.toFun =
      setToFun D.variation T1 h_dom1 (fun x => L (φ.val.toFun x)) := by
    have h_tmp := setToFun_comp_clm h_dom1 L φ.val.toFun hφ_int
    have h_switch : setToFun D.variation (fun s => (T1 s).comp L) hT_comp φ.val.toFun =
        setToFun D.variation T2 h_dom2 φ.val.toFun :=
      setToFun_congr_left' hT_comp h_dom2 (fun s _ _ => h_comp s) φ.val.toFun
    exact h_switch.symm.trans h_tmp

  have h_le : μ_w.variation ≤ ENNReal.ofReal ‖w‖ • D.variation := by
    apply Measure.le_iff.mpr
    intro s hs
    have h_bound_enorm : ∀ (E : Set (E n)), MeasurableSet E →
        ‖μ_w E‖ₑ ≤ ENNReal.ofReal ‖w‖ * D.variation E := by
      intro E hE
      have h1 : μ_w E = inner ℝ w (D E) := by rfl
      rw [h1]
      have h2 : ‖inner ℝ w (D E)‖ₑ ≤ ‖w‖ₑ * ‖D E‖ₑ := by
        have h_cs : |inner ℝ w (D E)| ≤ ‖w‖ * ‖D E‖ := by
          have h : ‖inner ℝ w (D E)‖ ≤ ‖w‖ * ‖D E‖ := norm_inner_le_norm w (D E)
          rwa [Real.norm_eq_abs] at h
        have h_en1 : ‖inner ℝ w (D E)‖ₑ = ENNReal.ofReal |inner ℝ w (D E)| :=
          Real.enorm_eq_ofReal_abs (inner ℝ w (D E))
        have h_en2 : ‖w‖ₑ = ENNReal.ofReal ‖w‖ := Eq.symm (ofReal_norm w)
        have h_en3 : ‖D E‖ₑ = ENNReal.ofReal ‖D E‖ := Eq.symm (ofReal_norm (D E))
        rw [h_en1, h_en2, h_en3]
        rw [← ENNReal.ofReal_mul (norm_nonneg w)]
        exact ENNReal.ofReal_le_ofReal h_cs
      have h3 : ‖D E‖ₑ ≤ D.variation E := VectorMeasure.enorm_measure_le_variation D E
      have h4 : ‖w‖ₑ = ENNReal.ofReal ‖w‖ := Eq.symm (ofReal_norm w)
      rw [h4] at h2
      calc ‖inner ℝ w (D E)‖ₑ
        ≤ ENNReal.ofReal ‖w‖ * ‖D E‖ₑ := h2
      _ ≤ ENNReal.ofReal ‖w‖ * D.variation E := by gcongr
    have h_bound_enorm' : ∀ (E : Set (E n)), MeasurableSet E → E ⊆ s →
        ‖μ_w E‖ₑ ≤ (ENNReal.ofReal ‖w‖ • D.variation) E := by
      intro E hE _
      have h := h_bound_enorm E hE
      simpa [smul_eq_mul] using h
    exact VectorMeasure.variation_apply_le_of_forall_enorm_le hs h_bound_enorm'
  have h_eq3 : setToFun D.variation T2 h_dom2 φ.val.toFun =
      setToFun μ_w.variation T2 h_dom2' φ.val.toFun :=
    setToFun_congr_measure_of_integrable (ENNReal.ofReal ‖w‖)
      ENNReal.ofReal_ne_top h_le h_dom2 h_dom2' φ.val.toFun hφ_int

  have h_main_eq : ∫ᵛ x, ψ_vec x ∂[innerBilinear; D] =
      ∫ᵛ x, φ.val.toFun x ∂<•μ_w := by
    have h5 : ∫ᵛ x, ψ_vec x ∂[innerBilinear; D] =
        setToFun D.variation T1 h_dom1 (fun x => L (φ.val.toFun x)) := by rfl
    rw [h5, ←h_eq2, h_eq3]
    <;> rfl

  rw [h_eq1, h_main_eq]

  haveI : IsFiniteMeasure μ_w.variation := by
    have h1 : μ_w.variation Set.univ ≤ ENNReal.ofReal ‖w‖ * D.variation Set.univ := h_le Set.univ
    have h2 : D.variation Set.univ < ⊤ := measure_lt_top D.variation Set.univ
    have h3 : μ_w.variation Set.univ < ⊤ :=
      h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2)
    exact ⟨h3⟩

  have hφ_int' : Integrable φ.val.toFun μ_w.variation :=
    φ.val.smooth.continuous.integrable_of_hasCompactSupport (μ := μ_w.variation) φ.val.compact
  have h_bound : |∫ᵛ x, φ.val.toFun x ∂<•μ_w| ≤ (μ_w.variation Ω).toReal := by
    have h6 : ‖∫ᵛ x, φ.val.toFun x ∂<•μ_w‖ ≤
        ∫ x, |φ.val.toFun x| ∂μ_w.variation := by
      have h_eq_int : (∫ᵛ x, φ.val.toFun x ∂<•μ_w) =
          setToFun μ_w.variation T2 h_dom2' φ.val.toFun := by rfl
      rw [h_eq_int]
      have h61 := norm_setToFun_le h_dom2' hφ_int' (by norm_num)
      have h62 : ‖hφ_int'.toL1 φ.val.toFun‖ = ∫ x, |φ.val.toFun x| ∂μ_w.variation := by
        have h_eq1 : ‖hφ_int'.toL1 φ.val.toFun‖ = ∫ x, ‖φ.val.toFun x‖ ∂μ_w.variation :=
          MeasureTheory.L1.norm_of_fun_eq_integral_norm hφ_int'
        rw [h_eq1]
        have h_abs : (fun x : E n => ‖φ.val.toFun x‖) = fun x : E n => |φ.val.toFun x| := by
          funext x
          exact Real.norm_eq_abs (φ.val.toFun x)
        rw [h_abs]
      rw [h62] at h61
      simpa using h61
    have h7 : ∫ x, |φ.val.toFun x| ∂μ_w.variation ≤ (μ_w.variation Ω).toReal := by
      have h8 : ∀ᵐ x ∂μ_w.variation, |φ.val.toFun x| ≤ Set.indicator Ω (fun _ => (1 : ℝ)) x := by
        filter_upwards with x
        by_cases hx : x ∈ Ω
        · have hb : |φ.val.toFun x| ≤ 1 := φ.val.bound x
          simpa [hx, abs_nonneg] using hb
        · have h9 : φ.val.toFun x = 0 := by
            by_contra h10
            have h11 : x ∈ Function.support φ.val.toFun := by
              simpa [Function.mem_support] using h10
            exact hx (φ.property h11)
          simp [hx, h9]
      have h9 : Integrable (fun x => |φ.val.toFun x|) μ_w.variation := by
        have h10 : Integrable φ.val.toFun μ_w.variation :=
          φ.val.smooth.continuous.integrable_of_hasCompactSupport (μ := μ_w.variation) φ.val.compact
        have h_and := h10.norm
        refine ⟨h_and.1, h_and.2⟩
      have h10 : Integrable (Set.indicator Ω (fun _ => (1 : ℝ))) μ_w.variation := by
        have h101 : Integrable (fun _ : E n => (1 : ℝ)) μ_w.variation := integrable_const (1 : ℝ)
        exact h101.indicator hΩ
      have h11 : ∫ x, |φ.val.toFun x| ∂μ_w.variation ≤
          ∫ x, Set.indicator Ω (fun _ => (1 : ℝ)) x ∂μ_w.variation :=
        integral_mono_ae h9 h10 h8
      have h12 : ∫ x, Set.indicator Ω (fun _ => (1 : ℝ)) x ∂μ_w.variation =
          (μ_w.variation Ω).toReal := by
        rw [integral_indicator hΩ]
        <;> simp
        <;> rfl
      rw [h12] at h11
      exact h11
    rw [Real.norm_eq_abs] at h6
    exact h6.trans h7

  have h9 : ENNReal.ofReal |∫ᵛ x, φ.val.toFun x ∂<•μ_w| ≤ μ_w.variation Ω := by
    have h10 : 0 ≤ |∫ᵛ x, φ.val.toFun x ∂<•μ_w| := abs_nonneg _
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_lt_top μ_w.variation Ω).ne]
    <;> exact h_bound

  exact h9.trans (h_var_le Ω)

-- ============================================================================
-- Step 4: Main theorem — directional variation of blow-up vanishes
-- ============================================================================

/-- **Directional variation of blow-up vanishes at reduced boundary.**

At a true reduced boundary point `x` with normal `ν = measureTheoreticNormal U x`,
for every direction `w` orthogonal to `ν` and every compact set `K`,
the local directional variation of the blow-ups tends to zero as `r → 0⁺`.

This uses:
- Besicovitch differentiation theorem
- Upper density bound for perimeter measure (conditional)
-/
theorem directionalVariation_blowUp_vanishing
    {U : Set (E n)} (hU : MeasurableSet U) (hfin : perimeter U < ⊤)
    (x : E n) (hx : x ∈ trueReducedBoundary U)
    (hn : 2 ≤ n)
    (w : E n) (hw : inner ℝ w (measureTheoreticNormal U x) = 0)
    (K : Set (E n)) (hK : IsCompact K)
    -- Upper density bound hypothesis (to be removed once proved)
    (h_upper_density : ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterMeasure U (closedBall x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)))
    -- Lebesgue differentiation for |inner(w, ν_U)| at x, limit is 0 because w ⟂ ν_U(x)
    (h_abs_lebesgue : Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, |inner ℝ w (measureTheoreticNormal U y)| ∂(perimeterMeasure U)) /
          (perimeterMeasure U (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Tendsto (fun r : ℝ => directionalVariationIn (blowUp U x r) w K)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let μ := perimeterMeasure U
  let f := measureTheoreticNormal U
  let g : E n → ℝ := fun y => |inner ℝ w (f y)|
  let ρ := μ.withDensity (fun y : E n => ENNReal.ofReal (g y))

  have hg_nonneg : ∀ y, 0 ≤ g y := by intro y; exact abs_nonneg _
  have h_int_f : Integrable f μ :=
    (measureTheoreticNormal_withDensity (hfin := hfin)).1
  have h_int_g : Integrable g μ := by
    have h1 : Integrable (fun y => inner ℝ w (f y)) μ := (innerBilinear w).integrable_comp h_int_f
    have h_and := h1.norm
    exact ⟨h_and.1, h_and.2⟩

  have hgx : g x = 0 := by
    simpa [g] using hw

  rcases hK.isBounded.subset_ball_lt 0 (0 : E n) with ⟨R, hR_pos, hKR⟩
  have hR_nonneg : 0 ≤ R := by linarith
  have h1n : 1 ≤ n := by linarith

  rcases h_upper_density with ⟨C, r0, hC_pos, hr0_pos, h_upper⟩

  -- Step 2 + Step 3 bound
  have h_bound : ∀ (r : ℝ), 0 < r →
      directionalVariationIn (blowUp U x r) w K ≤
        ENNReal.ofReal ((1 / r) ^ (n - 1)) * ρ (closedBall x (r * R)) := by
    intro r hr
    have h_step2 : directionalVariationIn (blowUp U x r) w K ≤
        ENNReal.ofReal ((1 / r) ^ (n - 1)) *
          directionalVariationIn U w (closedBall x (r * R)) :=
      directionalVariationIn_blowUp_bound hU hr hR_nonneg h1n w K (hKR.trans ball_subset_closedBall)
    have h_step3 : directionalVariationIn U w (closedBall x (r * R)) ≤
        ρ (closedBall x (r * R)) :=
      directionalVariationIn_le_weighted_perimeter hU hfin w (hΩ := isClosed_closedBall.measurableSet)
    calc directionalVariationIn (blowUp U x r) w K
      ≤ ENNReal.ofReal ((1 / r) ^ (n - 1)) *
          directionalVariationIn U w (closedBall x (r * R)) := h_step2
    _ ≤ ENNReal.ofReal ((1 / r) ^ (n - 1)) * ρ (closedBall x (r * R)) :=
        mul_le_mul_left' h_step3 _

  -- ρ(closedBall x s) = ENNReal.ofReal (∫ g) since g is integrable and non-negative
  have hρ_eq : ∀ (s : Set (E n)), MeasurableSet s →
      ρ s = ENNReal.ofReal (∫ y in s, g y ∂μ) := by
    intro s hs
    have h5 : ρ s = ∫⁻ y in s, ENNReal.ofReal (g y) ∂μ := by
      rw [withDensity_apply _ hs] <;> rfl
    rw [h5]
    have h6 : ∫⁻ y in s, ENNReal.ofReal (g y) ∂μ =
        ENNReal.ofReal (∫ y in s, g y ∂μ) := by
      have h7 : ∀ᵐ y ∂μ.restrict s, 0 ≤ g y := by
        filter_upwards with y; exact hg_nonneg y
      have h8 : AEStronglyMeasurable g (μ.restrict s) :=
        h_int_g.integrableOn.aestronglyMeasurable
      have h9 : (∫⁻ y in s, ENNReal.ofReal (g y) ∂μ).toReal = ∫ y in s, g y ∂μ :=
        (integral_eq_lintegral_of_nonneg_ae h7 h8).symm
      have h_fin : (∫⁻ y in s, ENNReal.ofReal (g y) ∂μ) ≠ ⊤ := by
        have h1 : HasFiniteIntegral g (μ.restrict s) := h_int_g.integrableOn.hasFiniteIntegral
        have h_eq : (∫⁻ y in s, ENNReal.ofReal |g y| ∂μ) = ∫⁻ y in s, ‖g y‖ₑ ∂μ := by
          apply lintegral_congr; intro y
          have h4 : ‖g y‖ₑ = ENNReal.ofReal (‖g y‖) := by
            rw [Real.enorm_eq_ofReal_abs (g y), Real.norm_eq_abs]
          rw [h4, Real.norm_eq_abs]
        have h2 : ∫⁻ y in s, ENNReal.ofReal |g y| ∂μ < ⊤ := by
          rw [h_eq]; exact h1
        have h3 : ∀ᵐ y ∂μ.restrict s, ENNReal.ofReal |g y| = ENNReal.ofReal (g y) := by
          filter_upwards with y
          rw [abs_of_nonneg (hg_nonneg y)]
        have h4 : ∫⁻ y in s, ENNReal.ofReal (g y) ∂μ < ⊤ := by
          rw [lintegral_congr_ae h3] at h2
          exact h2
        exact h4.ne
      rw [← h9, ENNReal.ofReal_toReal h_fin]
    exact h6

  -- Lebesgue differentiation for g = |inner(w, ν_U)|, limit is 0
  have h_leb_g : Tendsto (fun r : ℝ =>
      (∫ y in closedBall x r, g y ∂μ) / (μ (closedBall x r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [g, f] using h_abs_lebesgue

  -- μ(closedBall x r) > 0 for r > 0 by trueReducedBoundary
  have hμ_pos : ∀ (r : ℝ), 0 < r → 0 < μ (ball x r) := by
    intro r hr
    exact hx.1 r hr
  have hμ_closed_pos : ∀ (r : ℝ), 0 < r → 0 < μ (closedBall x r) := by
    intro r hr
    have h : ball x r ⊆ closedBall x r := ball_subset_closedBall
    have h' : μ (ball x r) ≤ μ (closedBall x r) := measure_mono h
    exact (hμ_pos r hr).trans_le h'

  -- Main convergence: (1/r)^(n-1) * ρ(closedBall x (r*R)) → 0
  -- For any ε > 0, eventually:
  --   (1/r)^(n-1) * ρ(closedBall x (rR))
  --     ≤ (1/r)^(n-1) * ε * μ(closedBall x (rR))
  --     ≤ (1/r)^(n-1) * ε * ENNReal.ofReal (C * (rR)^(n-1))
  --     = ε * ENNReal.ofReal (C * R^(n-1))

  have h_final : ∀ (ε : ℝ), 0 < ε → ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      ENNReal.ofReal ((1 / r) ^ (n - 1)) * ρ (closedBall x (r * R)) ≤
        ENNReal.ofReal (ε * C * R ^ (n - 1)) := by
    intro ε hε
    have h_cont_all : Continuous (fun r : ℝ => r * R) := by fun_prop
    have h_maps : Set.MapsTo (fun r : ℝ => r * R) (Set.Ioi 0) (Set.Ioi 0) :=
      fun x hx => mul_pos hx hR_pos
    have h2 : Tendsto (fun r : ℝ => r * R) (nhds 0) (nhds 0) := by
      have h3 := h_cont_all.tendsto 0
      have h4 : (0 : ℝ) * R = 0 := by ring
      rw [h4] at h3
      exact h3
    have h_scale : Tendsto (fun r : ℝ => r * R)
        (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
      have h_tendsto_nhds : Tendsto (fun r : ℝ => r * R) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        h2.mono_left nhdsWithin_le_nhds
      have h_eventually : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0), (r * R) ∈ Set.Ioi 0 := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact mul_pos hr hR_pos
      rw [tendsto_nhdsWithin_iff]
      exact ⟨h_tendsto_nhds, h_eventually⟩
    have h_tend : Tendsto (fun r : ℝ =>
        (∫ y in closedBall x (r * R), g y ∂μ) / (μ (closedBall x (r * R))).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      h_leb_g.comp h_scale
    have h_small : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
        (∫ y in closedBall x (r * R), g y ∂μ) ≤
          ε * (μ (closedBall x (r * R))).toReal := by
      have h_event : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
          (∫ y in closedBall x (r * R), g y ∂μ) / (μ (closedBall x (r * R))).toReal < ε :=
        h_tend (Iio_mem_nhds hε)
      filter_upwards [h_event, self_mem_nhdsWithin] with r hr hr_pos
      have hμfin_univ : μ Set.univ < ⊤ := by
        have h_eq : μ Set.univ = perimeter U :=
          (perimeter_eq_variation U hfin).symm
        rw [h_eq]
        exact hfin
      have hμfin : μ (closedBall x (r * R)) < ⊤ :=
        (measure_mono (subset_univ _)).trans_lt hμfin_univ
      have hμpos : 0 < μ (closedBall x (r * R)) :=
        hμ_closed_pos (r * R) (mul_pos hr_pos hR_pos)
      have h_pos : 0 < (μ (closedBall x (r * R))).toReal := by
        rw [ENNReal.toReal_pos_iff]
        exact ⟨hμpos, hμfin⟩
      have h_div : (∫ y in closedBall x (r * R), g y ∂μ) =
          ((∫ y in closedBall x (r * R), g y ∂μ) / (μ (closedBall x (r * R))).toReal) * (μ (closedBall x (r * R))).toReal := by
        rw [div_mul_cancel₀ _ h_pos.ne']
      have h : (∫ y in closedBall x (r * R), g y ∂μ) < ε * (μ (closedBall x (r * R))).toReal := by
        rw [h_div]
        gcongr
      exact h.le
    have h_r0 : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0), r * R < r0 := by
      have h : Tendsto (fun r : ℝ => r * R) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        h2.mono_left nhdsWithin_le_nhds
      exact h (Iio_mem_nhds hr0_pos)
    filter_upwards [h_small, h_r0, self_mem_nhdsWithin] with r hr_small hr_r0 hr_pos
    have hrR_pos : 0 < r * R := mul_pos hr_pos hR_pos
    have hρ : ρ (closedBall x (r * R)) =
        ENNReal.ofReal (∫ y in closedBall x (r * R), g y ∂μ) :=
      hρ_eq (closedBall x (r * R)) isClosed_closedBall.measurableSet
    have h11 : 0 ≤ (∫ y in closedBall x (r * R), g y ∂μ) :=
      integral_nonneg (fun y => hg_nonneg y)
    have h12 : ENNReal.ofReal (∫ y in closedBall x (r * R), g y ∂μ) ≤
        ENNReal.ofReal (ε * (μ (closedBall x (r * R))).toReal) :=
      ENNReal.ofReal_le_ofReal hr_small
    have h13 : μ (closedBall x (r * R)) ≤ ENNReal.ofReal (C * (r * R) ^ (n - 1)) :=
      h_upper (r * R) hrR_pos hr_r0
    have h13_ne : μ (closedBall x (r * R)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top h13
    have h13' : (μ (closedBall x (r * R))).toReal ≤ C * (r * R) ^ (n - 1) := by
      have h14 : (μ (closedBall x (r * R))).toReal ≤ (ENNReal.ofReal (C * (r * R) ^ (n - 1))).toReal :=
        (ENNReal.toReal_le_toReal h13_ne ENNReal.ofReal_ne_top).mpr h13
      have h15 : (ENNReal.ofReal (C * (r * R) ^ (n - 1))).toReal = C * (r * R) ^ (n - 1) := by
        rw [ENNReal.toReal_ofReal] <;> positivity
      rw [h15] at h14
      exact h14
    calc
      ENNReal.ofReal ((1 / r) ^ (n - 1)) * ρ (closedBall x (r * R))
        = ENNReal.ofReal ((1 / r) ^ (n - 1)) *
            ENNReal.ofReal (∫ y in closedBall x (r * R), g y ∂μ) := by rw [hρ]
      _ ≤ ENNReal.ofReal ((1 / r) ^ (n - 1)) *
            ENNReal.ofReal (ε * (μ (closedBall x (r * R))).toReal) :=
          mul_le_mul_left' h12 _
      _ = ENNReal.ofReal (((1 / r) ^ (n - 1)) * (ε * (μ (closedBall x (r * R))).toReal)) := by
          have hr_pos' : 0 < r := hr_pos
          have h_pos1 : 0 ≤ (1 / r) ^ (n - 1) := pow_nonneg (by positivity) (n - 1)
          exact (ENNReal.ofReal_mul h_pos1).symm
      _ ≤ ENNReal.ofReal (((1 / r) ^ (n - 1)) * ε * (C * (r * R) ^ (n - 1))) := by
          have h_pos1 : 0 ≤ (1 / r) ^ (n - 1) := by
            apply pow_nonneg
            exact one_div_nonneg.mpr hr_pos.le
          have h_pos_factor : 0 ≤ (1 / r) ^ (n - 1) * ε := mul_nonneg h_pos1 hε.le
          have h_ineq : ((1 / r) ^ (n - 1)) * ε * (μ (closedBall x (r * R))).toReal ≤
              ((1 / r) ^ (n - 1)) * ε * (C * (r * R) ^ (n - 1)) := by
            gcongr
          have h_ineq' : (1 / r) ^ (n - 1) * (ε * (μ (closedBall x (r * R))).toReal) ≤
              (1 / r) ^ (n - 1) * ε * (C * (r * R) ^ (n - 1)) := by
            have h_assoc : (1 / r) ^ (n - 1) * (ε * (μ (closedBall x (r * R))).toReal) =
                (1 / r) ^ (n - 1) * ε * (μ (closedBall x (r * R))).toReal := by ring
            rw [h_assoc]
            exact h_ineq
          exact ENNReal.ofReal_le_ofReal h_ineq'
      _ = ENNReal.ofReal (ε * C * R ^ (n - 1)) := by
          congr 1
          have hpow : (1 / r) ^ (n - 1) * (r * R) ^ (n - 1) = R ^ (n - 1) := by
            have h : (1 / r) ^ (n - 1) * (r * R) ^ (n - 1) = ((1 / r) * (r * R)) ^ (n - 1) := by
              rw [← mul_pow]
            rw [h]
            have h2 : (1 / r) * (r * R) = R := by
              have hr_ne : r ≠ 0 := hr_pos.ne'
              field_simp [hr_ne] <;> ring
            rw [h2]
          calc
            (1 / r) ^ (n - 1) * ε * (C * (r * R) ^ (n - 1))
              = ε * C * ((1 / r) ^ (n - 1) * (r * R) ^ (n - 1)) := by ring
            _ = ε * C * R ^ (n - 1) := by rw [hpow]

  have h_tendsto_zero : Tendsto (fun r : ℝ =>
      ENNReal.ofReal ((1 / r) ^ (n - 1)) * ρ (closedBall x (r * R)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h_main : ∀ (ε : ℝ), 0 < ε → ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
        ENNReal.ofReal ((1 / r) ^ (n - 1)) * ρ (closedBall x (r * R)) < ENNReal.ofReal ε := by
      intro ε hε
      set δ : ℝ := ε / (2 * (C * R ^ (n - 1))) with hδ_def
      have hδ_pos : 0 < δ := by
        have hpos : 0 < C * R ^ (n - 1) := by positivity
        positivity
      have h := h_final δ hδ_pos
      have hδ_calc : δ * C * R ^ (n - 1) = ε / 2 := by
        dsimp only [δ]
        have hpos' : 0 < C * R ^ (n - 1) := by positivity
        field_simp [hpos'.ne'] <;> ring
      filter_upwards [h] with r hr
      have h_calc : ENNReal.ofReal (δ * C * R ^ (n - 1)) = ENNReal.ofReal (ε / 2) := by
        rw [hδ_calc]
      rw [h_calc] at hr
      have hlt : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε := by
        have h1 : ε / 2 < ε := by linarith
        have h2 : 0 ≤ ε / 2 := by linarith
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h2).mpr h1
      exact hr.trans_lt hlt
    have h_basis : (nhds (0 : ENNReal)).HasBasis (fun a : ENNReal => 0 < a) (fun a => Set.Iio a) :=
      ENNReal.nhds_zero_basis
    rw [h_basis.tendsto_right_iff]
    intro a ha
    by_cases htop : a = ⊤
    · have hfin_rho : ∀ r, ρ (closedBall x (r * R)) < ⊤ := by
        intro r
        have h1 : ρ (closedBall x (r * R)) ≤ ρ Set.univ := by
          exact measure_mono (μ := ρ) (subset_univ _)
        have h2 : ρ Set.univ = ENNReal.ofReal (∫ y, g y ∂μ) := by
          have h21 := hρ_eq Set.univ MeasurableSet.univ
          have h22 : (∫ y in Set.univ, g y ∂μ) = (∫ y, g y ∂μ) := by simp
          rw [h21, h22]
        rw [h2] at h1
        exact h1.trans_lt ENNReal.ofReal_lt_top
      have h_all : ∀ (r : ℝ), ENNReal.ofReal ((1 / r) ^ (n - 1)) * ρ (closedBall x (r * R)) < ⊤ := by
        intro r
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin_rho r)
      have h_goal : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
          ENNReal.ofReal ((1 / r) ^ (n - 1)) * ρ (closedBall x (r * R)) < a := by
        rw [htop]
        filter_upwards with r
        exact h_all r
      exact h_goal
    · rcases ENNReal.lt_iff_exists_real_btwn.mp ha with ⟨ε', hε'_nonneg, hε'_ofReal_pos, hε'_lt⟩
      have hε'_pos : 0 < ε' := by
        have h : 0 < ENNReal.ofReal ε' := hε'_ofReal_pos
        rwa [ENNReal.ofReal_pos] at h
      have h := h_main ε' hε'_pos
      filter_upwards [h] with r hr
      exact hr.trans hε'_lt

  have h_zero_ev : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      (0 : ENNReal) ≤ directionalVariationIn (blowUp U x r) w K := by
    filter_upwards with r
    <;> positivity
  have h_bound_ev : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      directionalVariationIn (blowUp U x r) w K ≤
        ENNReal.ofReal ((1 / r) ^ (n - 1)) * ρ (closedBall x (r * R)) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact h_bound r hr
  exact Filter.Tendsto.squeeze' tendsto_const_nhds h_tendsto_zero h_zero_ev h_bound_ev

-- ============================================================================
-- Assembly: directional variation vanishing at true reduced boundary points
-- ============================================================================

/-- **Assemble directional variation vanishing at true reduced boundary points**.

Given a finite-perimeter set `U` and the a.e. upper density condition for
`perimeterMeasure`, there exists a `perimeterMeasure`-null set `N` such that
for every `x ∈ trueReducedBoundary U \ N`, every `w ⟂ measureTheoreticNormal U x`,
and every compact `K`, the directional variation of the blow-ups tends to zero:

`directionalVariationIn (blowUp U x r) w K → 0` as `r → 0⁺`.

This combines:
- a.e. upper density bound (hypothesis, supplied by `perimeter_density_upper_bound`)
- `abs_inner_lebesgue_diff_ae` (a.e. Lebesgue differentiation)
- `upper_bound_perimeterMeasure_from_perimeterIn` (ball → closedBall conversion)
- `directionalVariation_blowUp_vanishing` (main vanishing theorem)

Note: `h_upper_ae` uses `perimeterIn U (ball x r)`, converted internally to
`perimeterMeasure U (closedBall x r)`.
-/
theorem directional_vanishing_at_trb
    {U : Set (E n)} (hU_meas : MeasurableSet U)
    (hfin : perimeter U < ⊤) (hn : 2 ≤ n)
    (h_upper_ae : ∀ᵐ (x : E n) ∂(perimeterMeasure U),
      ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterIn U (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1))) :
    ∃ (N : Set (E n)), MeasurableSet N ∧ perimeterMeasure U N = 0 ∧
      ∀ x ∈ trueReducedBoundary U \ N,
        ∀ (w : E n), inner ℝ w (measureTheoreticNormal U x) = 0 →
          ∀ (K : Set (E n)), IsCompact K →
            Filter.Tendsto (fun r : ℝ => directionalVariationIn (blowUp U x r) w K)
              (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let μ := perimeterMeasure U
  let ν := measureTheoreticNormal U

  -- Absolute inner product Lebesgue differentiation holds a.e. wrt μ
  have h_abs_ae : ∀ᵐ (x : E n) ∂μ,
      ∀ (w : E n),
        Filter.Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, |inner ℝ w (ν y)| ∂μ) / (μ (closedBall x r)).toReal)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (|inner ℝ w (ν x)|)) :=
    abs_inner_lebesgue_diff_ae hfin

  -- Intersection of two full-measure sets
  have h_both_ae : ∀ᵐ (x : E n) ∂μ,
      (∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterIn U (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1))) ∧
      (∀ (w : E n),
        Filter.Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, |inner ℝ w (ν y)| ∂μ) / (μ (closedBall x r)).toReal)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (|inner ℝ w (ν x)|))) :=
    h_upper_ae.and h_abs_ae

  -- Extract a measurable null set outside which both conditions hold
  let P : E n → Prop := fun x =>
      (∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterIn U (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1))) ∧
      (∀ (w : E n),
        Filter.Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, |inner ℝ w (ν y)| ∂μ) / (μ (closedBall x r)).toReal)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (|inner ℝ w (ν x)|)))
  have h_both_ae : ∀ᵐ (x : E n) ∂μ, P x := h_upper_ae.and h_abs_ae
  let Bad : Set (E n) := {x | ¬P x}
  have hBad_null : μ Bad = 0 := (ae_iff).mp h_both_ae
  rcases MeasureTheory.exists_measurable_superset μ Bad with ⟨N, hBad_sub_N, hN_meas, hN_eq⟩
  have hN_null : μ N = 0 := by rw [hN_eq, hBad_null]

  refine ⟨N, hN_meas, hN_null, ?_⟩
  intro x hx
  have hx_trb : x ∈ trueReducedBoundary U := hx.1
  have hx_notN : x ∉ N := hx.2
  have hx_notBad : x ∉ Bad := fun h => hx_notN (hBad_sub_N h)
  have hx_both : P x := by simpa [Bad] using hx_notBad
  rcases hx_both with ⟨h_upper, h_abs⟩

  -- Convert perimeterIn upper bound to perimeterMeasure upper bound
  rcases h_upper with ⟨C, r0, hC_pos, hr0_pos, h_bound⟩
  have h_upper' : ∃ (C' : ℝ) (r0' : ℝ), 0 < C' ∧ 0 < r0' ∧
      ∀ r, 0 < r → r < r0' →
        μ (closedBall x r) ≤ ENNReal.ofReal (C' * r ^ (n - 1)) :=
    upper_bound_perimeterMeasure_from_perimeterIn hfin hC_pos hr0_pos h_bound hn

  intro w hw K hK
  have h_abs0 : Filter.Tendsto (fun r : ℝ =>
      (∫ y in closedBall x r, |inner ℝ w (ν y)| ∂μ) / (μ (closedBall x r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h1 := h_abs w
    have h2 : |inner ℝ w (ν x)| = 0 := by
      rw [hw] <;> simp
    rw [h2] at h1
    exact h1
  exact directionalVariation_blowUp_vanishing hU_meas hfin x hx_trb hn w hw K hK h_upper' h_abs0

end Geometry.StructureTheorem
