import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterDefinition
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.CutoffFunctions
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DistributionalDerivative
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.TrueReducedBoundary
import Mathlib.Tactic

/-!
# Perimeter Density Lower Bound

At a reduced boundary point, the volume of `S ∩ B(x,r)` and its complement
are bounded below by `c * r^n` for small `r`.

## Proof route (Gauss-Green cutoff)

1. Let `μ = perimeterMeasure S`, `ν_U = measureTheoreticNormal S`,
   `g(y) = inner(ν, ν_U(y))`.
2. Conditional: perimeter measure lower density `μ(B(x,r)) ≥ c₁ * r^(n-1)`.
3. Conditional: perimeter measure upper density `μ(B(x,r)) ≤ C₁ * r^(n-1)`.
4. Conditional: scalar comparability `∫_{B(x,r)} g dμ ≥ (1/2) μ(B(x,r))`
   (follows from Besicovitch differentiation at good points).
5. Take `η = radialCutoff x (r/2) (ε*r)` with `ε` small.
6. Gauss-Green: `∫ η * g dμ = ∫_S fderiv η ν`.
7. LHS ≥ `μ(closedBall x (r/2)) - μ(closedBall x (r/2 + ε*r))` ≥ `K * r^(n-1)`.
8. RHS ≤ `(C_grad / (ε*r)) * volume(S ∩ ball x r)`.
9. Combine: `volume(S ∩ ball x r) ≥ c' * r^n`.
10. Exterior bound by applying the same argument to `Sᶜ` with normal `-ν`.

## Whiteprint
Node `perimeter_density_lower_bound`.
-/


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

open Perimeter

variable {n : ℕ}

-- ============================================================================
-- Helper: integral against a real-density signed measure
-- ============================================================================

/-- For real-valued vector measures and functions, `∂•` and `∂<•` agree since
multiplication in `ℝ` is commutative. -/
lemma integral_smul_eq_flip {X : Type*} [MeasurableSpace X] {ν : VectorMeasure X ℝ}
    {η : X → ℝ} : ∫ᵛ x, η x ∂•ν = ∫ᵛ x, η x ∂<•ν := by
  have h_B : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ)) =
      (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    ext
    simp [mul_comm]
  exact congr_arg (fun (B : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ)) => ∫ᵛ x, η x ∂[B; ν]) h_B

/-- Integral against `μ.withDensityᵥ g` equals the product integral against `μ`. -/
lemma integral_withDensityᵥ_real {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {g : X → ℝ} (hg : Integrable g μ)
    (hg_bdd : ∀ᵐ x ∂μ, |g x| ≤ 1) {η : X → ℝ}
    (hη : Integrable η μ) :
    ∫ᵛ x, η x ∂•(μ.withDensityᵥ g) = ∫ x, η x * g x ∂μ := by
  let g_pos : X → ℝ := fun x => max (g x) 0
  let g_neg : X → ℝ := fun x => max (-g x) 0
  let f_pos : X → ENNReal := fun x => ENNReal.ofReal (g x)
  let f_neg : X → ENNReal := fun x => ENNReal.ofReal (-g x)
  let μpos := μ.withDensity f_pos
  let μneg := μ.withDensity f_neg

  have hg_pos_int : Integrable g_pos μ := hg.pos_part
  have hg_neg_int : Integrable g_neg μ := hg.neg.pos_part

  have hg_ae : AEMeasurable g μ := hg.1.aemeasurable
  have hf_pos_meas : AEMeasurable f_pos μ := AEMeasurable.ennreal_ofReal hg_ae
  have hg_neg_ae : AEMeasurable (fun x => -g x) μ := by
    rcases hg_ae with ⟨g', hg'_meas, hgg'⟩
    refine' ⟨fun x => -g' x, hg'_meas.neg, _⟩
    filter_upwards [hgg'] with x hx
    rw [hx]
  have hf_neg_meas : AEMeasurable f_neg μ := AEMeasurable.ennreal_ofReal hg_neg_ae

  have h_pos_le_one : ∀ᵐ x ∂μ, f_pos x ≤ 1 := by
    filter_upwards [hg_bdd] with x hx
    have h5 : g x ≤ 1 := by linarith [le_abs_self (g x)]
    exact ENNReal.ofReal_le_one.mpr h5
  have h_neg_le_one : ∀ᵐ x ∂μ, f_neg x ≤ 1 := by
    filter_upwards [hg_bdd] with x hx
    have h5 : -g x ≤ 1 := by linarith [neg_le_abs (g x)]
    exact ENNReal.ofReal_le_one.mpr h5

  have hf_pos_lt_top : ∫⁻ x, f_pos x ∂μ ≠ ⊤ := by
    have h1 : ∫⁻ x, f_pos x ∂μ ≤ ∫⁻ x, (1 : ENNReal) ∂μ := lintegral_mono_ae h_pos_le_one
    have h2 : ∫⁻ x, (1 : ENNReal) ∂μ = μ Set.univ := by simp
    rw [h2] at h1
    have h_fin : μ Set.univ < ⊤ := MeasureTheory.measure_lt_top μ Set.univ
    exact h1.trans_lt h_fin |>.ne
  have hf_neg_lt_top : ∫⁻ x, f_neg x ∂μ ≠ ⊤ := by
    have h1 : ∫⁻ x, f_neg x ∂μ ≤ ∫⁻ x, (1 : ENNReal) ∂μ := lintegral_mono_ae h_neg_le_one
    have h2 : ∫⁻ x, (1 : ENNReal) ∂μ = μ Set.univ := by simp
    rw [h2] at h1
    have h_fin : μ Set.univ < ⊤ := MeasureTheory.measure_lt_top μ Set.univ
    exact h1.trans_lt h_fin |>.ne

  have h_density_pos_le : μpos ≤ μ := by
    have h1 : μpos ≤ μ.withDensity (fun _ => 1) := withDensity_mono h_pos_le_one
    have h2 : μ.withDensity (fun _ => 1) = μ := by simp
    rw [h2] at h1
    exact h1
  have h_density_neg_le : μneg ≤ μ := by
    have h1 : μneg ≤ μ.withDensity (fun _ => 1) := withDensity_mono h_neg_le_one
    have h2 : μ.withDensity (fun _ => 1) = μ := by simp
    rw [h2] at h1
    exact h1

  haveI : IsFiniteMeasure μpos := isFiniteMeasure_withDensity hf_pos_lt_top
  haveI : IsFiniteMeasure μneg := isFiniteMeasure_withDensity hf_neg_lt_top

  have hη_pos : Integrable η μpos := hη.mono_measure h_density_pos_le
  have hη_neg : Integrable η μneg := hη.mono_measure h_density_neg_le

  have h_decomp : μ.withDensityᵥ g = μpos.toSignedMeasure - μneg.toSignedMeasure :=
    withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hg

  have h_var_pos : μpos.toSignedMeasure.variation = μpos := Measure.variation_toSignedMeasure
  have h_var_neg : μneg.toSignedMeasure.variation = μneg := Measure.variation_toSignedMeasure
  have hvm_pos : μpos.toSignedMeasure.Integrable η := by
    show Integrable η μpos.toSignedMeasure.variation
    rw [h_var_pos]
    exact hη_pos
  have hvm_neg : μneg.toSignedMeasure.Integrable η := by
    show Integrable η μneg.toSignedMeasure.variation
    rw [h_var_neg]
    exact hη_neg

  have h_toReal_pos : ∀ x, (f_pos x).toReal = g_pos x := by
    intro x
    simp [f_pos, g_pos] <;> norm_cast <;> linarith
  have h_toReal_neg : ∀ x, (f_neg x).toReal = g_neg x := by
    intro x
    simp [f_neg, g_neg] <;> norm_cast <;> linarith

  have hg_pos_bdd : ∀ᵐ x ∂μ, g_pos x ≤ 1 := by
    filter_upwards [hg_bdd] with x hx
    have h1 : g_pos x ≤ |g x| := by
      dsimp only [g_pos]
      exact max_le (le_abs_self (g x)) (abs_nonneg (g x))
    linarith
  have h_mul_pos : Integrable (fun x : X => η x * g_pos x) μ := by
    have h : ∀ᵐ x ∂μ, |η x * g_pos x| ≤ |η x| := by
      filter_upwards [hg_pos_bdd] with x hx
      have h6 : 0 ≤ g_pos x := by positivity
      calc |η x * g_pos x| = |η x| * |g_pos x| := by rw [abs_mul]
        _ = |η x| * g_pos x := by rw [abs_of_nonneg h6]
        _ ≤ |η x| * 1 := by gcongr
        _ = |η x| := by ring
    have hprod_am : AEStronglyMeasurable (fun x : X => η x * g_pos x) μ :=
      hη.aestronglyMeasurable.mul hg_pos_int.aestronglyMeasurable
    exact Integrable.mono hη hprod_am h
  have hg_neg_bdd : ∀ᵐ x ∂μ, g_neg x ≤ 1 := by
    filter_upwards [hg_bdd] with x hx
    have h1 : g_neg x ≤ |g x| := by
      dsimp only [g_neg]
      exact max_le (neg_le_abs (g x)) (abs_nonneg (g x))
    linarith
  have h_mul_neg : Integrable (fun x : X => η x * g_neg x) μ := by
    have h : ∀ᵐ x ∂μ, |η x * g_neg x| ≤ |η x| := by
      filter_upwards [hg_neg_bdd] with x hx
      have h6 : 0 ≤ g_neg x := by positivity
      calc |η x * g_neg x| = |η x| * |g_neg x| := by rw [abs_mul]
        _ = |η x| * g_neg x := by rw [abs_of_nonneg h6]
        _ ≤ |η x| * 1 := by gcongr
        _ = |η x| := by ring
    have hprod_am : AEStronglyMeasurable (fun x : X => η x * g_neg x) μ :=
      hη.aestronglyMeasurable.mul hg_neg_int.aestronglyMeasurable
    exact Integrable.mono hη hprod_am h

  have h_main1 : ∫ᵛ x, η x ∂•(μ.withDensityᵥ g) = ∫ᵛ x, η x ∂<•(μ.withDensityᵥ g) :=
    integral_smul_eq_flip
  rw [h_main1, h_decomp]
  rw [VectorMeasure.integral_sub_vectorMeasure hvm_pos hvm_neg]
  have h_pos_int : ∫ᵛ x, η x ∂<•μpos.toSignedMeasure = ∫ x, η x ∂μpos :=
    VectorMeasure.integral_toSignedMeasure (μ := μpos)
  have h_neg_int : ∫ᵛ x, η x ∂<•μneg.toSignedMeasure = ∫ x, η x ∂μneg :=
    VectorMeasure.integral_toSignedMeasure (μ := μneg)
  rw [h_pos_int, h_neg_int]
  have h_pos2 : ∫ x, η x ∂μpos = ∫ x, (f_pos x).toReal * η x ∂μ :=
    integral_withDensity_eq_integral_toReal_smul₀ hf_pos_meas
      (by filter_upwards with x; exact ENNReal.ofReal_lt_top) η
  have h_neg2 : ∫ x, η x ∂μneg = ∫ x, (f_neg x).toReal * η x ∂μ :=
    integral_withDensity_eq_integral_toReal_smul₀ hf_neg_meas
      (by filter_upwards with x; exact ENNReal.ofReal_lt_top) η
  rw [h_pos2, h_neg2]
  have h_eq_pos : (fun x : X => (f_pos x).toReal * η x) = fun x : X => η x * g_pos x := by
    funext x
    rw [h_toReal_pos x] <;> ring
  have h_eq_neg : (fun x : X => (f_neg x).toReal * η x) = fun x : X => η x * g_neg x := by
    funext x
    rw [h_toReal_neg x] <;> ring
  rw [h_eq_pos, h_eq_neg]
  have h_sub : (∫ x, η x * g_pos x ∂μ) - (∫ x, η x * g_neg x ∂μ) =
      ∫ x, (η x * g_pos x - η x * g_neg x) ∂μ := by
    exact (integral_sub h_mul_pos h_mul_neg).symm
  rw [h_sub]
  congr with x
  have h4 : g_pos x - g_neg x = g x := by
    dsimp only [g_pos, g_neg]
    cases' le_total 0 (g x) with h h
    · simp [g_pos, g_neg, h] <;> linarith
    · simp [g_pos, g_neg, h] <;> linarith
  have h6 : η x * g_pos x - η x * g_neg x = η x * g x := by
    rw [←mul_sub, h4] <;> ring
  exact h6

/-- **Vector measure integral identity**: for `η` integrable w.r.t. `perimeterMeasure S`,
`∫ᵛ (η•ν) ∂[innerBilinear; D] = ∫ η * inner(ν, ν_U) dμ`. -/
lemma vector_integral_withNormal
    {S : Set (E n)} (hfin : perimeter S < ⊤)
    {ν : E n} (hν_unit : ‖ν‖ = 1)
    {η : E n → ℝ}
    (hη : Integrable η (perimeterMeasure S)) :
    ∫ᵛ y, η y • ν ∂[innerBilinear; distributionalDerivative S] =
    ∫ y, η y * inner ℝ ν (measureTheoreticNormal S y) ∂(perimeterMeasure S) := by
  let D := distributionalDerivative S
  let μ := perimeterMeasure S
  let ν_U := measureTheoreticNormal S
  let B := innerBilinear (n := n)
  let g : E n → ℝ := fun y => inner ℝ ν (ν_U y)
  rcases measureTheoreticNormal_withDensity hfin with ⟨h_int, h_main1⟩
  let ρ : VectorMeasure (E n) ℝ := D.mapRange (B.flip ν) (B.flip ν).continuous
  have hg_int : Integrable g μ := by
    have h1 : Integrable (fun y => inner ℝ (ν_U y) ν) μ := h_int.inner_const ν
    have h2 : g = fun y => inner ℝ (ν_U y) ν := by
      funext y; exact real_inner_comm _ _
    rw [h2]; exact h1
  have hρ_eq : ρ = μ.withDensityᵥ g := by
    ext A hA
    have h1 : ρ A = inner ℝ (D A) ν := by rfl
    have h2 : inner ℝ (D A) ν = inner ℝ ν (D A) := real_inner_comm _ _
    have hD_eq : D = μ.withDensityᵥ ν_U := h_main1
    have h3 : D A = ∫ y in A, ν_U y ∂μ := by
      rw [hD_eq]
      exact withDensityᵥ_apply h_int hA
    rw [h1, h2, h3]
    let l : E n →L[ℝ] ℝ :=
      { toFun := fun z => inner ℝ ν z
        map_add' := by simp [inner_add_right]
        map_smul' := by simp [inner_smul_right] <;> ring }
    have h4 : l (∫ y in A, ν_U y ∂μ) = ∫ y in A, l (ν_U y) ∂μ := by
      have h5 : ∫ y in A, inner ℝ ν (ν_U y) ∂μ = inner ℝ ν (∫ y in A, ν_U y ∂μ) :=
        integral_inner (h_int.integrableOn) ν
      simpa [l] using h5.symm
    have h5 : (μ.withDensityᵥ g) A = ∫ y in A, g y ∂μ := withDensityᵥ_apply hg_int hA
    simpa [l, g, h5] using h4
  let L : ℝ →L[ℝ] E n := (ContinuousLinearMap.lsmul ℝ ℝ).flip ν
  let F : Set (E n) → (ℝ →L[ℝ] ℝ) := fun s => ((D.transpose B) s).comp L
  let G : VectorMeasure (E n) (ℝ →L[ℝ] ℝ) := ρ.transpose (ContinuousLinearMap.lsmul ℝ ℝ)
  have h_transpose_eq : ∀ (A : Set (E n)), F A = G A := by
    intro A
    ext
    have hρA : ρ A = inner ℝ ν (D A) := by
      have h51 : ρ A = inner ℝ (D A) ν := by rfl
      rw [h51, real_inner_comm]
    simp [F, G, L, VectorMeasure.transpose, VectorMeasure.mapRange_apply,
      B, innerBilinear_apply, ContinuousLinearMap.coe_comp, hρA]
    <;> ring
  have h_set_eq : F = G := by
    funext s; exact h_transpose_eq s
  have hρ_var_le : ρ.variation ≤ (‖ν‖₊ : ENNReal) • D.variation := by
    have h : ∀ (A : Set (E n)), MeasurableSet A → ‖ρ A‖ₑ ≤ (‖ν‖₊ : ENNReal) * D.variation A := by
      intro A hA
      have h51 : ρ A = inner ℝ (D A) ν := by rfl
      have h5 : ρ A = inner ℝ ν (D A) := by
        rw [h51, real_inner_comm]
      rw [h5]
      have h6 : ‖inner ℝ ν (D A)‖ₑ ≤ (‖ν‖₊ : ENNReal) * ‖D A‖ₑ := by
        have h_cs : ‖inner ℝ ν (D A)‖ ≤ ‖ν‖ * ‖D A‖ := norm_inner_le_norm ν (D A)
        have h_enorm : ‖inner ℝ ν (D A)‖ₑ = ENNReal.ofReal ‖inner ℝ ν (D A)‖ := by
          rw [Real.enorm_eq_ofReal_abs (inner ℝ ν (D A))]
          have h_abs : |inner ℝ ν (D A)| = ‖inner ℝ ν (D A)‖ := by
            rw [←Real.norm_eq_abs]
          rw [h_abs]
        rw [h_enorm]
        have h7 : (‖ν‖₊ : ENNReal) = ENNReal.ofReal ‖ν‖ := by
          have h71 : (‖ν‖₊ : ℝ) = ‖ν‖ := by
            simp [nnnorm]
          have h72 : (‖ν‖₊ : ENNReal) = ENNReal.ofReal (‖ν‖₊ : ℝ) := by
            simp [nnnorm] <;> norm_cast
          rw [h72, h71]
        have h8 : ‖D A‖ₑ = ENNReal.ofReal ‖D A‖ := by
          have h81 : ‖D A‖ₑ = (‖D A‖₊ : ENNReal) := by rfl
          rw [h81]
          have h82 : (‖D A‖₊ : ENNReal) = ENNReal.ofReal ‖D A‖ := by
            simp [nnnorm] <;> norm_cast
          rw [h82]
        rw [h7, h8]
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal h_cs
      have h7 : ‖D A‖ₑ ≤ D.variation A := VectorMeasure.enorm_measure_le_variation D A
      calc
        ‖inner ℝ ν (D A)‖ₑ ≤ (‖ν‖₊ : ENNReal) * ‖D A‖ₑ := h6
        _ ≤ (‖ν‖₊ : ENNReal) * D.variation A := by gcongr
    exact VectorMeasure.variation_le_of_forall_enorm_le h
  have hD_var_eq : D.variation = μ := by
    dsimp only [D, μ, perimeterMeasure] <;> rfl
  have hν_nnreal_one : (‖ν‖₊ : ENNReal) = 1 := by
    have h1 : ‖ν‖₊ = 1 := by
      apply NNReal.coe_injective
      have h2 : (‖ν‖₊ : ℝ) = ‖ν‖ := by
        simp [nnnorm]
      rw [h2, hν_unit] <;> norm_num
    rw [h1] <;> norm_num
  have hρ_var_le' : ρ.variation ≤ μ := by
    rw [hν_nnreal_one] at hρ_var_le
    rw [hD_var_eq] at hρ_var_le
    simpa using hρ_var_le
  have hηρ : Integrable η ρ.variation := hη.mono_measure hρ_var_le'
  have h_dom1 : DominatedFinMeasAdditive D.variation F (‖B‖ * ‖L‖) := by
    let hT := dominatedFinMeasAdditive_cbmApplyMeasure D B
    refine ⟨fun s t hs ht hμs hμt hdisj => ?_, fun s hs hsf => ?_⟩
    · have h9 : (D.transpose B) (s ∪ t) = (D.transpose B) s + (D.transpose B) t :=
        hT.1 s t hs ht hμs hμt hdisj
      simpa [F, Function.comp] using congr_arg (fun g : (E n) →L[ℝ] ℝ => g.comp L) h9
    · have h10 : ‖(D.transpose B) s‖ ≤ ‖B‖ * D.variation.real s := hT.2 s hs hsf
      calc ‖F s‖
        ≤ ‖(D.transpose B) s‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖B‖ * D.variation.real s) * ‖L‖ := by gcongr
      _ = (‖B‖ * ‖L‖) * D.variation.real s := by ring
  have h_main_eq : ∫ᵛ y, η y • ν ∂[B; D] = setToFun D.variation F h_dom1 η := by
    exact (setToFun_comp_clm (dominatedFinMeasAdditive_cbmApplyMeasure D B) L η hη).symm
  have h_dom2 : DominatedFinMeasAdditive D.variation G (‖B‖ * ‖L‖) := by
    convert h_dom1 using 2
    exact h_set_eq.symm
  have h_congr_left : setToFun D.variation F h_dom1 η = setToFun D.variation G h_dom2 η :=
    setToFun_congr_left h_dom1 h_dom2 h_set_eq η
  have h_congr_meas : setToFun D.variation G h_dom2 η =
      setToFun ρ.variation G (dominatedFinMeasAdditive_cbmApplyMeasure ρ (ContinuousLinearMap.lsmul ℝ ℝ)) η :=
    setToFun_congr_measure_of_integrable (‖ν‖₊ : ENNReal) (by simp) hρ_var_le
      h_dom2 (dominatedFinMeasAdditive_cbmApplyMeasure ρ (ContinuousLinearMap.lsmul ℝ ℝ)) η hη
  have hν_norm : ∀ᵐ y ∂μ, ‖ν_U y‖ = 1 := norm_measureTheoreticNormal_eq_one hfin
  have hg_bdd : ∀ᵐ y ∂μ, |g y| ≤ 1 := by
    filter_upwards [hν_norm] with y hy
    have h : |g y| ≤ ‖ν‖ * ‖ν_U y‖ := by
      exact abs_real_inner_le_norm ν (ν_U y)
    rw [hν_unit, hy] at h
    <;> norm_num at h ⊢ <;> exact h
  have hμ_fin : μ Set.univ < ⊤ := by
    have h : μ Set.univ = perimeter S := by
      simpa [μ, perimeterMeasure] using (perimeter_eq_variation S hfin).symm
    rw [h]; exact hfin
  letI : IsFiniteMeasure μ := ⟨hμ_fin⟩
  have h_final : ∫ᵛ y, η y ∂•ρ = ∫ y, η y * g y ∂μ := by
    rw [hρ_eq]
    exact integral_withDensityᵥ_real hg_int hg_bdd hη
  calc
    ∫ᵛ y, η y • ν ∂[B; D]
      = setToFun D.variation F h_dom1 η := h_main_eq
    _ = setToFun D.variation G h_dom2 η := h_congr_left
    _ = setToFun ρ.variation G (dominatedFinMeasAdditive_cbmApplyMeasure ρ (ContinuousLinearMap.lsmul ℝ ℝ)) η := h_congr_meas
    _ = ∫ᵛ y, η y ∂•ρ := by rfl
    _ = ∫ y, η y * g y ∂μ := h_final

/-- **Gauss-Green scalar identity**: for a smooth compactly supported scalar
test function `η` and a fixed direction `ν`,

`∫_S fderiv η ν = ∫ η * inner(ν, ν_U) dμ`

where `μ = perimeterMeasure S` and `ν_U = measureTheoreticNormal S`.

This follows from the distributional derivative integral formula combined with
the polar decomposition `Dχ_S = μ.withDensityᵥ ν_U`. -/
lemma gauss_green_scalar_identity
    {S : Set (E n)} (hS : MeasurableSet S) (hfin : perimeter S < ⊤)
    {ν : E n} (hν_unit : ‖ν‖ = 1)
    {η : E n → ℝ}
    (hη_smooth : ContDiff ℝ ∞ η) (hη_supp : HasCompactSupport η) :
    ∫ y in S, fderiv ℝ η y ν =
    ∫ y, η y * inner ℝ ν (measureTheoreticNormal S y) ∂(perimeterMeasure S) := by
  let D := distributionalDerivative S
  let μ := perimeterMeasure S
  let ν_U := measureTheoreticNormal S
  let φ : E n → E n := fun y => η y • ν

  have hφ_smooth : ContDiff ℝ ∞ φ := hη_smooth.smul_const ν
  have hφ_supp : HasCompactSupport φ := by
    have h1 : Function.support φ ⊆ Function.support η := by
      intro y hy
      by_contra h2
      have h3 : η y = 0 := by simpa [Function.mem_support] using h2
      have h4 : φ y = 0 := by
        simp [φ, h3]
      exact Function.mem_support.mp hy h4
    have h2 : tsupport φ ⊆ tsupport η := closure_mono h1
    have h3 : IsCompact (tsupport η) := hη_supp.isCompact
    have h4 : IsCompact (tsupport φ) := h3.of_isClosed_subset isClosed_closure h2
    exact h4

  have h_div : divergence φ = fun y => fderiv ℝ η y ν :=
    divergence_smul_const hη_smooth
  have h1 : ∫ᵛ y, φ y ∂[innerBilinear; D] = ∫ y in S, fderiv ℝ η y ν := by
    rw [distributionalDerivative_integral_formula S hfin φ hφ_smooth hφ_supp]
    exact congr_arg (fun f : E n → ℝ => ∫ y in S, f y) h_div

  have hμ_fin : μ Set.univ < ⊤ := by
    have h : μ Set.univ = perimeter S := by
      simpa [μ, perimeterMeasure] using (perimeter_eq_variation S hfin).symm
    rw [h]; exact hfin
  letI : IsFiniteMeasure μ := ⟨hμ_fin⟩
  have hη_cont : Continuous η := hη_smooth.continuous
  have hη : Integrable η μ := hη_smooth.continuous.integrable_of_hasCompactSupport hη_supp
  have h_main : ∫ᵛ y, φ y ∂[innerBilinear; D] =
      ∫ y, η y * inner ℝ ν (ν_U y) ∂μ :=
    vector_integral_withNormal hfin hν_unit hη

  rw [←h1, h_main]

-- ============================================================================
-- Layer cake helpers
-- ============================================================================

/-- Every superlevel set `{radialCutoff x r_inner L ≥ t}` for `t ∈ (0,1]`
is a closed ball centered at `x` with radius in `[r_inner, r_inner + L)`. -/
lemma radialCutoff_superlevel_is_closedBall {n : ℕ} {x : E n} {r_inner L : ℝ}
    (hr_inner_pos : 0 < r_inner) (hL_pos : 0 < L)
    {t : ℝ} (ht_pos : 0 < t) (ht_le_one : t ≤ 1) :
    ∃ (d : ℝ), r_inner ≤ d ∧ d < r_inner + L ∧
      {y : E n | (radialCutoff x r_inner L) y ≥ t} = closedBall x d := by
  let f : ℝ → ℝ := fun d => smoothStep ((d - r_inner) / L)
  have hL_ne : L ≠ 0 := hL_pos.ne'
  have hf_cont : Continuous f :=
    smoothStep_contDiff.continuous.comp ((continuous_id.sub continuous_const).div continuous_const (fun _ => hL_ne))
  have hf_antitone : Antitone f := by
    intro d1 d2 h
    apply smoothStep_antitone
    have h5 : (d1 - r_inner) / L ≤ (d2 - r_inner) / L := by
      gcongr
    exact h5
  let A := {d : ℝ | f d ≥ t}
  have hA_closed : IsClosed A := isClosed_Ici.preimage hf_cont
  have hA_nonempty : A.Nonempty := by
    refine ⟨r_inner, ?_⟩
    have h : f r_inner = 1 := by
      simp [f, smoothStep_one_of_nonpos] <;> norm_num
    have h' : f r_inner ≥ t := by
      rw [h] <;> linarith
    exact h'
  have hA_bdd : BddAbove A := by
    refine ⟨r_inner + L, fun d hd => ?_⟩
    by_contra h2
    have h3 : d > r_inner + L := by linarith
    have h41 : d - r_inner > L := by linarith
    have h4 : (d - r_inner) / L > 1 := by
      have h42 : (d - r_inner) / L > L / L := by gcongr
      have h43 : L / L = 1 := by
        field_simp [hL_ne]
      rw [h43] at h42
      exact h42
    have h5 : f d = 0 := by
      have h51 : (d - r_inner) / L ≥ 1 := by linarith
      have h : f d = smoothStep ((d - r_inner) / L) := by simp [f]
      rw [h, smoothStep_zero_of_one_le h51]
    have h6 : f d ≥ t := hd
    rw [h5] at h6
    linarith [ht_pos]
  let d_t := sSup A
  have h_d_t_in_A : d_t ∈ A := hA_closed.csSup_mem hA_nonempty hA_bdd
  have hA_eq : A = Set.Iic d_t := by
    ext d
    simp only [Set.mem_Iic]
    constructor
    · intro hd; exact le_csSup hA_bdd hd
    · intro hle
      have h : f d ≥ f d_t := hf_antitone hle
      have h2 : f d_t ≥ t := h_d_t_in_A
      have h3 : f d ≥ t := by linarith
      exact h3
  have h_d_t_lower : r_inner ≤ d_t := by
    have h' : f r_inner = 1 := by
      simp [f, smoothStep_one_of_nonpos] <;> norm_num
    have h_in : r_inner ∈ A := by
      have h'' : f r_inner ≥ t := by rw [h'] <;> linarith
      exact h''
    exact le_csSup hA_bdd h_in
  have h_d_t_upper : d_t < r_inner + L := by
    have h_f_at : f (r_inner + L) = 0 := by
      have h10 : ((r_inner + L) - r_inner) / L = 1 := by
        have h9 : (r_inner + L) - r_inner = L := by ring
        rw [h9, div_self hL_ne]
      have h11 : f (r_inner + L) = smoothStep (((r_inner + L) - r_inner) / L) := by
        simp [f]
      rw [h11, h10]
      exact smoothStep_zero_of_one_le (by norm_num)
    have h_notin : r_inner + L ∉ A := by
      intro h
      have h10 : f (r_inner + L) ≥ t := h
      rw [h_f_at] at h10
      linarith
    have h : ¬(r_inner + L ≤ d_t) := by
      intro hle
      have h' : r_inner + L ∈ A := hA_eq.symm ▸ hle
      exact h_notin h'
    linarith
  have h_iff : ∀ (z : ℝ), f z ≥ t ↔ z ≤ d_t := by
    intro z
    have h1 : f z ≥ t ↔ z ∈ A := Iff.rfl
    rw [h1, hA_eq]
    simp [Set.mem_Iic]
  have h_main : {y : E n | (radialCutoff x r_inner L) y ≥ t} = closedBall x d_t := by
    ext y
    have h6 : (radialCutoff x r_inner L) y = f (dist y x) := by rfl
    simp only [Set.mem_setOf_eq, mem_closedBall, h6]
    exact h_iff (dist y x)
  exact ⟨d_t, h_d_t_lower, h_d_t_upper, h_main⟩

/-- **Layer cake weighted bound**: if `0 ≤ η ≤ 1` and for every superlevel set
`{η ≥ t}` we have `∫_{{η≥t}} g dμ ≥ (1/2) μ({{η≥t}})`, then
`∫ η * g dμ ≥ (1/2) ∫ η dμ`. -/
lemma layer_cake_weighted_bound {{α : Type*}} {{m : MeasurableSpace α}} {{μ : Measure α}}
    [IsFiniteMeasure μ] {{η g : α → ℝ}}
    (hη_meas : Measurable η) (hg_int : Integrable g μ) (hg_meas : Measurable g)
    (hη_nonneg : 0 ≤ η) (hη_le_one : η ≤ 1)
    (h_scalar : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∫ x in {y | η y ≥ t}, g x ∂μ ≥ (1 / 2 : ℝ) * (μ {y | η y ≥ t}).toReal) :
    ∫ x, η x * g x ∂μ ≥ (1 / 2 : ℝ) * ∫ x, η x ∂μ := by
  let I := Set.Ioc (0 : ℝ) 1
  let ν := MeasureTheory.volume.restrict I
  let H : α × ℝ → ℝ := fun p => g p.1 * (if η p.1 ≥ p.2 then (1 : ℝ) else 0)

  have hI_fin : ν Set.univ < ⊤ := by
    simp [ν, I, Real.volume_Ioc] <;> norm_num
  haveI : IsFiniteMeasure ν := ⟨hI_fin⟩
  haveI : SFinite ν := by infer_instance

  have h1_meas : Measurable (fun p : α × ℝ => η p.1) := hη_meas.comp measurable_fst
  have h2_meas : Measurable (fun p : α × ℝ => p.2) := measurable_snd
  have h_set_meas : MeasurableSet {p : α × ℝ | η p.1 ≥ p.2} :=
    measurableSet_le h2_meas h1_meas
  have h_ind_meas : Measurable (fun p : α × ℝ => if η p.1 ≥ p.2 then (1 : ℝ) else 0) :=
    measurable_const.indicator h_set_meas
  have hH_meas : Measurable H :=
    (hg_meas.comp measurable_fst).mul h_ind_meas

  have hH_bound : ∀ p : α × ℝ, |H p| ≤ |g p.1| := by
    intro ⟨x, t⟩
    have h : |(if η x ≥ t then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs <;> norm_num
    calc |g x * (if η x ≥ t then (1 : ℝ) else 0)|
      = |g x| * |(if η x ≥ t then (1 : ℝ) else 0)| := by rw [abs_mul]
    _ ≤ |g x| * 1 := by gcongr
    _ = |g x| := by ring

  have hH_enorm_bound : ∀ p : α × ℝ, ‖H p‖ₑ ≤ ‖g p.1‖ₑ := by
    intro p
    have h : |H p| ≤ |g p.1| := hH_bound p
    exact enorm_le_iff_norm_le.mpr h

  have hgm : Measurable (fun p : α × ℝ => ‖g p.1‖ₑ) :=
    (hg_meas.comp measurable_fst).enorm
  have hgm_x : Measurable (fun x : α => ‖g x‖ₑ) := hg_meas.enorm
  have h2 : ∫⁻ p, ‖g p.1‖ₑ ∂(μ.prod ν) = (ν Set.univ) * ∫⁻ x, ‖g x‖ₑ ∂μ := by
    let f : α × ℝ → ENNReal := fun p => ‖g p.1‖ₑ
    have h21 : ∫⁻ p, f p ∂(μ.prod ν) =
        ∫⁻ x, ∫⁻ (t : ℝ), ‖g x‖ₑ ∂ν ∂μ := by
      have h_eq1 : ∫⁻ p, f p ∂(μ.prod ν) = ∫⁻ x, ∫⁻ t, f (x, t) ∂ν ∂μ :=
        (MeasureTheory.lintegral_lintegral (f := Function.curry f) hgm.aemeasurable).symm
      rw [h_eq1]
    rw [h21]
    have h3 : ∀ x, ∫⁻ (t : ℝ), ‖g x‖ₑ ∂ν = (ν Set.univ) * ‖g x‖ₑ := by
      intro x
      simp [lintegral_const] <;> ring
    have h4 : ∫⁻ x, ∫⁻ (t : ℝ), ‖g x‖ₑ ∂ν ∂μ = ∫⁻ x, (ν Set.univ) * ‖g x‖ₑ ∂μ := by
      congr with x; exact h3 x
    rw [h4, MeasureTheory.lintegral_const_mul (ν Set.univ) (hf := hgm_x)]
  have h3 : ∫⁻ x, ‖g x‖ₑ ∂μ < ⊤ := hg_int.2
  have h4 : (ν Set.univ) * ∫⁻ x, ‖g x‖ₑ ∂μ < ⊤ := by
    have hν_fin : ν Set.univ < ⊤ := hI_fin
    exact mul_lt_top hν_fin h3
  have h1_lintegral : ∫⁻ p, ‖H p‖ₑ ∂(μ.prod ν) ≤ ∫⁻ p, ‖g p.1‖ₑ ∂(μ.prod ν) := by
    gcongr with p
    exact hH_enorm_bound p
  have h5 : ∫⁻ p, ‖H p‖ₑ ∂(μ.prod ν) < ⊤ := h1_lintegral.trans_lt (by rwa [h2])
  have hH_int : Integrable H (μ.prod ν) :=
    ⟨hH_meas.aestronglyMeasurable, h5⟩

  have h1 : ∀ (x : α), η x = ∫ t in I, (if η x ≥ t then (1 : ℝ) else 0) := by
    intro x
    have hηx_nonneg : 0 ≤ η x := hη_nonneg x
    have hηx_le_one : η x ≤ 1 := hη_le_one x
    by_cases h_pos : 0 < η x
    · have h_set_eq : I ∩ {t : ℝ | η x ≥ t} = Set.Ioc (0 : ℝ) (η x) := by
        ext t
        simp only [I, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ioc]
        constructor
        · rintro ⟨⟨h1, _h2⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩
          have h3 : t ≤ 1 := by linarith [hηx_le_one]
          exact ⟨⟨h1, h3⟩, by linarith⟩
      have h_meas_set : MeasurableSet (Set.Ioc (0 : ℝ) (η x)) := measurableSet_Ioc
      have h_ind : (fun t : ℝ => (if η x ≥ t then (1 : ℝ) else 0)) =ᵐ[ν]
          Set.indicator (Set.Ioc (0 : ℝ) (η x)) (fun (_ : ℝ) => (1 : ℝ)) := by
        have hI : ∀ᵐ t ∂ν, t ∈ I := ae_restrict_mem measurableSet_Ioc
        filter_upwards [hI] with t ht
        have h_iff : η x ≥ t ↔ t ∈ Set.Ioc (0 : ℝ) (η x) := by
          simp only [Set.mem_Ioc]
          constructor
          · intro h; exact ⟨ht.1, h⟩
          · intro h; exact h.2
        rw [Set.indicator_apply]
        split_ifs <;> tauto
      have h_int_ind : ∫ t in I, (if η x ≥ t then (1 : ℝ) else 0) =
          ∫ t in I, Set.indicator (Set.Ioc (0 : ℝ) (η x)) (fun (_ : ℝ) => (1 : ℝ)) t :=
        integral_congr_ae h_ind
      rw [h_int_ind]
      have h_sub : Set.Ioc (0 : ℝ) (η x) ⊆ I := by
        intro t ht; exact ⟨ht.1, le_trans ht.2 hηx_le_one⟩
      have h9 : ∫ t in I, Set.indicator (Set.Ioc (0 : ℝ) (η x)) (fun (_ : ℝ) => (1 : ℝ)) t =
          ∫ t in Set.Ioc (0 : ℝ) (η x), (1 : ℝ) := by
        rw [setIntegral_indicator h_meas_set]
        have h_inter : I ∩ Set.Ioc (0 : ℝ) (η x) = Set.Ioc (0 : ℝ) (η x) :=
          Set.inter_eq_right.mpr h_sub
        rw [h_inter]
      rw [h9]
      have h10 : ∫ t in Set.Ioc (0 : ℝ) (η x), (1 : ℝ) = volume.real (Set.Ioc (0 : ℝ) (η x)) := by
        exact MeasureTheory.setIntegral_one_eq_measureReal (μ := volume)
      rw [h10]
      have hvol : volume.real (Set.Ioc (0 : ℝ) (η x)) = η x := by
        have h11 : volume.real (Set.Ioc (0 : ℝ) (η x)) = (volume (Set.Ioc (0 : ℝ) (η x))).toReal := by
          exact Measure.real_def volume (Ioc 0 (η x))
        rw [h11]
        rw [Real.volume_Ioc] <;> simp [hηx_nonneg] <;> linarith
      rw [hvol]
    · have h_zero : η x = 0 := by linarith
      have h_ae : (fun t : ℝ => (if η x ≥ t then (1 : ℝ) else 0)) =ᵐ[ν] 0 := by
        have hI : ∀ᵐ t ∂ν, t ∈ I := ae_restrict_mem measurableSet_Ioc
        filter_upwards [hI] with t ht
        have h_t_pos : 0 < t := ht.1
        have h_not : ¬(η x ≥ t) := by
          rw [h_zero] <;> linarith
        rw [if_neg h_not] <;> norm_num
      have h_int : ∫ t in I, (if η x ≥ t then (1 : ℝ) else 0) = 0 :=
        integral_eq_zero_of_ae h_ae
      rw [h_int, h_zero]

  let f_curried : α → ℝ → ℝ := fun x t => g x * (if η x ≥ t then 1 else 0)
  have h_f_uncurry : Function.uncurry f_curried = H := by
    funext p
    cases p with
    | mk x t =>
      simp [f_curried, H]
      <;> ring

  have h_fubini : ∫ x, (∫ t in I, f_curried x t) ∂μ =
      ∫ t in I, (∫ x, f_curried x t ∂μ) := by
    have hH_int' : Integrable (Function.uncurry f_curried) (μ.prod ν) := by
      rw [h_f_uncurry]
      exact hH_int
    exact MeasureTheory.integral_integral_swap hH_int'

  have h2 : ∫ x, η x * g x ∂μ = ∫ t in I, ∫ x in {y | η y ≥ t}, g x ∂μ := by
    have h3 : ∫ x, η x * g x ∂μ =
        ∫ x, (∫ t in I, (if η x ≥ t then (1 : ℝ) else 0)) * g x ∂μ := by
      congr with x
      exact congr_arg (fun y : ℝ => y * g x) (h1 x)
    rw [h3]
    have h4 : ∀ x, (∫ t in I, (if η x ≥ t then (1 : ℝ) else 0)) * g x =
        ∫ t in I, g x * (if η x ≥ t then (1 : ℝ) else 0) := by
      intro x
      have h5 : g x * ∫ t in I, (if η x ≥ t then (1 : ℝ) else 0) =
          ∫ t in I, g x * (if η x ≥ t then (1 : ℝ) else 0) := by
        rw [← integral_const_mul (g x)]
      have h6 : (∫ t in I, (if η x ≥ t then (1 : ℝ) else 0)) * g x =
          g x * ∫ t in I, (if η x ≥ t then (1 : ℝ) else 0) := by ring
      rw [h6, h5]
    have h5 : ∫ x, (∫ t in I, (if η x ≥ t then (1 : ℝ) else 0)) * g x ∂μ =
        ∫ x, (∫ t in I, g x * (if η x ≥ t then (1 : ℝ) else 0)) ∂μ := by
      congr with x; exact h4 x
    rw [h5, h_fubini]
    have h7 : ∀ t, ∫ x, g x * (if η x ≥ t then (1 : ℝ) else 0) ∂μ =
        ∫ x in {y | η y ≥ t}, g x ∂μ := by
      intro t
      have h8 : (fun x => g x * (if η x ≥ t then (1 : ℝ) else 0)) =
          Set.indicator {y | η y ≥ t} g := by
        funext x
        simp [Set.indicator_apply] <;> split_ifs <;> ring
      rw [h8]
      have h_set_meas' : NullMeasurableSet {y | η y ≥ t} μ :=
        (hη_meas measurableSet_Ici).nullMeasurableSet
      exact MeasureTheory.integral_indicator₀ h_set_meas'
    congr with t; exact h7 t

  let H2 : α × ℝ → ℝ := fun p => (if η p.1 ≥ p.2 then (1 : ℝ) else 0)
  have hH2_meas : Measurable H2 :=
    measurable_const.indicator h_set_meas
  have hH2_int : Integrable H2 (μ.prod ν) := by
    have h1 : ∀ p, |H2 p| ≤ 1 := by
      intro ⟨x, t⟩
      dsimp only [H2]
      split_ifs <;> norm_num
    have h2 : ∫⁻ p, ‖H2 p‖ₑ ∂(μ.prod ν) ≤ ∫⁻ p, (1 : ENNReal) ∂(μ.prod ν) := by
      apply lintegral_mono
      intro p
      have h3 : |H2 p| ≤ 1 := h1 p
      have h4 : ‖H2 p‖ₑ ≤ (1 : ENNReal) := by
        have h5 : ‖H2 p‖ₑ = ENNReal.ofReal |H2 p| := Real.enorm_eq_ofReal_abs (H2 p)
        rw [h5]
        exact ENNReal.ofReal_le_one.mpr h3
      exact h4
    have h3 : ∫⁻ p, (1 : ENNReal) ∂(μ.prod ν) = (μ.prod ν) Set.univ := by simp
    have h4 : (μ.prod ν) Set.univ < ⊤ := by
      have h5 : (μ.prod ν) Set.univ = μ Set.univ * ν Set.univ := by
        have h6 : (μ.prod ν) Set.univ = ν Set.univ * μ Set.univ := by
          rw [Measure.prod_apply] <;> simp
        rw [h6, mul_comm]
      rw [h5]
      have hμ_fin : μ Set.univ < ⊤ := by (expose_names; exact (isFiniteMeasure_iff μ).mp inst)
      have hν_fin : ν Set.univ < ⊤ := hI_fin
      exact mul_lt_top hμ_fin hν_fin
    have h5 : ∫⁻ p, ‖H2 p‖ₑ ∂(μ.prod ν) < ⊤ := h2.trans_lt (by rwa [h3])
    exact ⟨hH2_meas.aestronglyMeasurable, h5⟩

  have h_fubini2 : ∫ x, (∫ t in I, (if η x ≥ t then (1 : ℝ) else 0)) ∂μ =
      ∫ t in I, (∫ x, (if η x ≥ t then (1 : ℝ) else 0) ∂μ) := by
    have h_eq1 : ∀ x, (∫ t in I, (if η x ≥ t then (1 : ℝ) else 0)) = ∫ t, H2 (x, t) ∂ν := by
      intro x; rfl
    have h_eq2 : ∀ t, (∫ x, (if η x ≥ t then (1 : ℝ) else 0) ∂μ) = ∫ x, H2 (x, t) ∂μ := by
      intro t; rfl
    calc
      ∫ x, (∫ t in I, (if η x ≥ t then (1 : ℝ) else 0)) ∂μ
        = ∫ x, ∫ t, H2 (x, t) ∂ν ∂μ := by rfl
      _ = ∫ t, ∫ x, H2 (x, t) ∂μ ∂ν := MeasureTheory.integral_integral_swap hH2_int
      _ = ∫ t in I, (∫ x, (if η x ≥ t then (1 : ℝ) else 0) ∂μ) := by rfl

  have h3 : ∫ x, η x ∂μ = ∫ t in I, (μ {y | η y ≥ t}).toReal := by
    have h4 : ∫ x, η x ∂μ = ∫ x, (∫ t in I, (if η x ≥ t then (1 : ℝ) else 0)) ∂μ := by
      congr with x; exact h1 x
    rw [h4, h_fubini2]
    have h6 : ∀ t, ∫ x, (if η x ≥ t then (1 : ℝ) else 0) ∂μ = (μ {y | η y ≥ t}).toReal := by
      intro t
      have h_set_meas' : MeasurableSet {y : α | η y ≥ t} := hη_meas measurableSet_Ici
      have h7 : (fun x : α => (if η x ≥ t then (1 : ℝ) else 0)) =
          Set.indicator {y | η y ≥ t} (fun (_ : α) => (1 : ℝ)) := by
        funext x
        simp [Set.indicator_apply] <;> split_ifs <;> ring
      rw [h7, integral_indicator h_set_meas']
      have h9 : ∫ x in {y | η y ≥ t}, (1 : ℝ) ∂μ = μ.real {y | η y ≥ t} :=
        MeasureTheory.setIntegral_one_eq_measureReal (μ := μ)
      rw [h9]
      have h10 : μ.real {y | η y ≥ t} = (μ {y | η y ≥ t}).toReal := by exact Measure.real_def μ {y | η y ≥ t}
      rw [h10]
    have h8 : (fun t : ℝ => ∫ x, (if η x ≥ t then (1 : ℝ) else 0) ∂μ) =
        (fun t : ℝ => (μ {y | η y ≥ t}).toReal) := by
      funext t; exact h6 t
    rw [h8]

  have h_int1 : Integrable (fun t : ℝ => ∫ x in {y | η y ≥ t}, g x ∂μ) ν := by
    have h : Integrable (fun t : ℝ => ∫ x, H (x, t) ∂μ) ν := hH_int.integral_prod_right
    have h_eq : (fun t : ℝ => ∫ x, H (x, t) ∂μ) = (fun t : ℝ => ∫ x in {y | η y ≥ t}, g x ∂μ) := by
      funext t
      have h9 : ∫ x, H (x, t) ∂μ = ∫ x, g x * (if η x ≥ t then (1 : ℝ) else 0) ∂μ := by
        rfl
      rw [h9]
      have h_set_meas' : MeasurableSet {y : α | η y ≥ t} := hη_meas measurableSet_Ici
      have h10 : (fun x : α => g x * (if η x ≥ t then (1 : ℝ) else 0)) = Set.indicator {y | η y ≥ t} g := by
        funext x
        simp [Set.indicator_apply] <;> split_ifs <;> ring
      rw [h10, integral_indicator h_set_meas']
    rw [h_eq] at h
    exact h

  have h_mono : Antitone (fun t : ℝ => μ {y | η y ≥ t}) := by
    intro t1 t2 hle
    have h_sub : {y | η y ≥ t2} ⊆ {y | η y ≥ t1} := by
      intro y hy
      have h9 : η y ≥ t2 := hy
      have h10 : η y ≥ t1 := by linarith
      exact h10
    exact measure_mono h_sub
  have h_meas1 : Measurable (fun t : ℝ => μ {y | η y ≥ t}) := h_mono.measurable
  have h_meas_t : Measurable (fun t : ℝ => (μ {y | η y ≥ t}).toReal) :=
    ENNReal.measurable_toReal.comp h_meas1

  have h_int2 : Integrable (fun t : ℝ => (1 / 2 : ℝ) * (μ {y | η y ≥ t}).toReal) ν := by
    have h_bound : ∀ t, |(1 / 2 : ℝ) * (μ {y | η y ≥ t}).toReal| ≤ (1 / 2 : ℝ) * (μ Set.univ).toReal := by
      intro t
      have h5 : 0 ≤ (μ {y | η y ≥ t}).toReal := by positivity
      have h_univ_ne_top : μ Set.univ ≠ ⊤ := by
        have h2 : μ Set.univ < ⊤ := by (expose_names; exact (isFiniteMeasure_iff μ).mp inst)
        exact h2.ne
      have h6 : (μ {y | η y ≥ t}).toReal ≤ (μ Set.univ).toReal :=
        ENNReal.toReal_mono h_univ_ne_top (measure_mono (Set.subset_univ _))
      rw [abs_of_nonneg (by positivity)] <;> gcongr
    have h_const_int : Integrable (fun t : ℝ => (1 / 2 : ℝ) * (μ Set.univ).toReal) ν :=
      integrable_const _
    have h_main_asm : AEStronglyMeasurable (fun t : ℝ => (1 / 2 : ℝ) * (μ {y | η y ≥ t}).toReal) ν :=
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ => (1 / 2 : ℝ)) ν).mul h_meas_t.aestronglyMeasurable
    have h_bound_ae : ∀ᵐ (t : ℝ) ∂ν, ‖(1 / 2 : ℝ) * (μ {y | η y ≥ t}).toReal‖ ≤ ‖(1 / 2 : ℝ) * (μ Set.univ).toReal‖ := by
      filter_upwards with t
      have h5 : 0 ≤ (μ {y | η y ≥ t}).toReal := by positivity
      have h_univ_ne_top2 : μ Set.univ ≠ ⊤ := by
        have h2 : μ Set.univ < ⊤ := by (expose_names; exact (isFiniteMeasure_iff μ).mp inst)
        exact h2.ne
      have h6 : (μ {y | η y ≥ t}).toReal ≤ (μ Set.univ).toReal :=
        ENNReal.toReal_mono h_univ_ne_top2 (measure_mono (Set.subset_univ _))
      have h7 : 0 ≤ (1 / 2 : ℝ) := by norm_num
      have h9 : ‖(1 / 2 : ℝ) * (μ {y | η y ≥ t}).toReal‖ = (1 / 2 : ℝ) * (μ {y | η y ≥ t}).toReal := by
        rw [Real.norm_eq_abs, abs_of_nonneg] <;> positivity
      have h10 : ‖(1 / 2 : ℝ) * (μ Set.univ).toReal‖ = (1 / 2 : ℝ) * (μ Set.univ).toReal := by
        rw [Real.norm_eq_abs, abs_of_nonneg] <;> positivity
      rw [h9, h10]
      exact mul_le_mul_of_nonneg_left h6 h7
    exact Integrable.mono h_const_int h_main_asm h_bound_ae

  have h_mem : ∀ᵐ (t : ℝ) ∂ν, t ∈ I := MeasureTheory.ae_restrict_mem measurableSet_Ioc
  have h_ae : ∀ᵐ (t : ℝ) ∂ν, (∫ x in {y | η y ≥ t}, g x ∂μ) ≥ (1 / 2 : ℝ) * (μ {y | η y ≥ t}).toReal := by
    filter_upwards [h_mem] with t ht
    exact h_scalar t ht

  calc
    ∫ x, η x * g x ∂μ
      = ∫ t in I, ∫ x in {y | η y ≥ t}, g x ∂μ := h2
    _ ≥ ∫ t in I, (1 / 2 : ℝ) * (μ {y | η y ≥ t}).toReal := by
      have h_ae' : ∀ᵐ (t : ℝ) ∂ν, (1 / 2 : ℝ) * (μ {y | η y ≥ t}).toReal ≤ (∫ x in {y | η y ≥ t}, g x ∂μ) := by
        filter_upwards [h_ae] with t ht; exact ht
      exact integral_mono_ae h_int2 h_int1 h_ae'
    _ = (1 / 2 : ℝ) * ∫ t in I, (μ {y | η y ≥ t}).toReal := by
      rw [integral_const_mul] <;> ring
    _ = (1 / 2 : ℝ) * ∫ x, η x ∂μ := by rw [h3]

/-- **Interior volume lower bound** via Gauss-Green cutoff + layer cake. -/
lemma interior_volume_lower_bound
    {S : Set (E n)} (hS : MeasurableSet S) (hfin : perimeter S < ⊤)
    {x : E n} {ν : E n} (hν_unit : ‖ν‖ = 1)
    (hν_normal : measureTheoreticNormal S x = ν)
    (c_lower C_upper : ℝ) (hc_lower : 0 < c_lower) (hC_upper : 0 < C_upper)
    (R_lower R_upper R_scalar : ℝ)
    (hR_lower : 0 < R_lower) (hR_upper : 0 < R_upper) (hR_scalar : 0 < R_scalar)
    (hμ_lower : ∀ r, 0 < r → r < R_lower →
      (perimeterMeasure S (closedBall x r)).toReal ≥ c_lower * r ^ (n - 1))
    (hμ_upper : ∀ r, 0 < r → r < R_upper →
      (perimeterMeasure S (closedBall x r)).toReal ≤ C_upper * r ^ (n - 1))
    (h_scalar : ∀ r, 0 < r → r < R_scalar →
      (∫ y in closedBall x r, inner ℝ ν (measureTheoreticNormal S y) ∂(perimeterMeasure S)) ≥
      (1 / 2 : ℝ) * (perimeterMeasure S (closedBall x r)).toReal)
    (hn : 2 ≤ n) :
    ∃ (c : ℝ) (R : ℝ), 0 < c ∧ 0 < R ∧
      ∀ r, 0 < r → r < R →
        volume (S ∩ ball x r) ≥ ENNReal.ofReal (c * r ^ n) := by
  let μ := perimeterMeasure S
  let g := fun y : E n => inner ℝ ν (measureTheoreticNormal S y)
  let C_grad := smoothStepDerivBound

  have hC_grad_nonneg : 0 ≤ C_grad := smoothStepDerivBound_nonneg
  have hC_grad_pos : 0 < C_grad := by
    by_contra h
    have h0' : C_grad ≤ 0 := by linarith
    have h0 : C_grad = 0 := by linarith [hC_grad_nonneg]
    have h1 : ∀ t : ℝ, |deriv smoothStep t| ≤ 0 := fun t => smoothStep_deriv_bound.trans (le_of_eq h0)
    have h2 : ∀ t : ℝ, deriv smoothStep t = 0 := by
      intro t
      have h3 : |deriv smoothStep t| ≤ 0 := h1 t
      have h4 : 0 ≤ |deriv smoothStep t| := abs_nonneg _
      have h5 : |deriv smoothStep t| = 0 := by linarith
      exact abs_eq_zero.mp h5
    have h_const : smoothStep 1 = smoothStep 0 := by
      have h_cont : ContinuousOn smoothStep (Set.Icc (0 : ℝ) 1) :=
        smoothStep_contDiff.continuous.continuousOn
      have h_diff : DifferentiableOn ℝ smoothStep (Set.Ioo (0 : ℝ) 1) :=
        (smoothStep_contDiff.differentiable (by norm_num)).differentiableOn
      have h_mvt : ∃ c ∈ Set.Ioo (0 : ℝ) 1,
          deriv smoothStep c = (smoothStep 1 - smoothStep 0) / (1 - 0) :=
        exists_deriv_eq_slope smoothStep (by norm_num) h_cont h_diff
      rcases h_mvt with ⟨c, _, h_eq⟩
      have h5 : deriv smoothStep c = 0 := h2 c
      rw [h5] at h_eq
      have h6 : (smoothStep 1 - smoothStep 0) / (1 - 0) = 0 := h_eq.symm
      have h7 : smoothStep 1 - smoothStep 0 = 0 := by
        simpa using h6
      linarith
    have h5 : smoothStep 1 = smoothStep 0 := h_const
    have h6 : smoothStep 0 = 1 := smoothStep_one_of_nonpos (by norm_num)
    have h7 : smoothStep 1 = 0 := smoothStep_zero_of_one_le (by norm_num)
    rw [h6, h7] at h5 <;> norm_num at h5

  -- Fixed fractions: r_inner = r/2, L = r/3, so r_inner + L = 5r/6 < r
  let r_inner_frac : ℝ := 1 / 2
  let L_frac : ℝ := 1 / 3
  let K : ℝ := (1 / 2 : ℝ) * c_lower
  have hK_pos : 0 < K := by positivity
  let c : ℝ := K * r_inner_frac ^ (n - 1) * L_frac / C_grad
  have hc_pos : 0 < c := by positivity

  let R : ℝ := min R_lower R_scalar
  have hR_pos : 0 < R := by positivity

  refine ⟨c, R, hc_pos, hR_pos, ?_⟩

  intro r hr_pos hr_lt

  have hr_lt_lower : r < R_lower := by linarith [min_le_left R_lower R_scalar]
  have hr_lt_scalar : r < R_scalar := by linarith [min_le_right R_lower R_scalar]

  set r_inner : ℝ := r_inner_frac * r with hr_inner_def
  set L : ℝ := L_frac * r with hL_def
  have hr_inner_pos : 0 < r_inner := by positivity
  have hL_pos : 0 < L := by positivity
  have hr_inner_lt_lower : r_inner < R_lower := by
    have h : r_inner < r := by
      rw [hr_inner_def]
      have hpos : 0 < r := hr_pos
      dsimp only [r_inner_frac]
      linarith
    linarith [hr_lt_lower]
  have h_sum_lt_scalar : r_inner + L < R_scalar := by
    have h : r_inner + L < r := by
      rw [hr_inner_def, hL_def]
      have hpos : 0 < r := hr_pos
      dsimp only [r_inner_frac, L_frac]
      linarith
    linarith [hr_lt_scalar]

  let η := radialCutoff x r_inner L

  have hη_smooth : ContDiff ℝ ∞ η := by
    simpa [η] using radialCutoff_contDiff hr_inner_pos hL_pos
  have hη_supp : HasCompactSupport η := by
    have h1' : ∀ y, y ∉ closedBall x (r_inner + L) → η y = 0 := by
      intro y hy
      have h3 : y ∉ ball x (r_inner + L) := by
        have h4 : dist y x > r_inner + L := by
          simpa [closedBall, mem_closedBall] using hy
        simpa [ball, mem_ball, not_lt] using le_of_lt h4
      exact radialCutoff_zero_of_not_mem_ball hr_inner_pos hL_pos h3
    have h2 : IsCompact (closedBall x (r_inner + L)) := isCompact_closedBall x (r_inner + L)
    exact HasCompactSupport.intro h2 h1'
  have hη_meas : Measurable η := hη_smooth.continuous.measurable

  have h_smoothStep_bound : ∀ t : ℝ, 0 ≤ smoothStep t ∧ smoothStep t ≤ 1 := by
    intro t
    by_cases h1 : t ≤ 0
    · rw [smoothStep_one_of_nonpos h1] <;> norm_num
    · have h1' : 0 < t := by linarith
      by_cases h2 : 1 ≤ t
      · rw [smoothStep_zero_of_one_le h2] <;> norm_num
      · have h3 : 0 < t ∧ t < 1 := ⟨h1', by linarith⟩
        have h4 : smoothStep t ≤ smoothStep 0 := smoothStep_antitone (by linarith)
        have h5 : smoothStep 1 ≤ smoothStep t := smoothStep_antitone (by linarith)
        have h6 : smoothStep 0 = 1 := smoothStep_one_of_nonpos (by norm_num)
        have h7 : smoothStep 1 = 0 := smoothStep_zero_of_one_le (by norm_num)
        constructor <;> linarith

  have hη_nonneg : 0 ≤ η := by
    intro y
    have h : 0 ≤ smoothStep ((dist y x - r_inner) / L) := (h_smoothStep_bound _).1
    exact h

  have hη_le_one : η ≤ 1 := by
    intro y
    have h : smoothStep ((dist y x - r_inner) / L) ≤ 1 := (h_smoothStep_bound _).2
    exact h

  have hη_one : ∀ y ∈ closedBall x r_inner, η y = 1 :=
    fun y hy => radialCutoff_one_of_mem_closedBall hr_inner_pos hL_pos hy

  have hη_zero : ∀ y ∉ ball x (r_inner + L), η y = 0 :=
    fun y hy => radialCutoff_zero_of_not_mem_ball hr_inner_pos hL_pos hy

  -- Superlevel sets are closed balls with radius in [r_inner, r_inner + L)
  have h_superlevel : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ (d : ℝ), r_inner ≤ d ∧ d < r_inner + L ∧
        {y : E n | η y ≥ t} = closedBall x d := by
    intro t ht
    exact radialCutoff_superlevel_is_closedBall hr_inner_pos hL_pos ht.1 ht.2

  -- Scalar comparability on every superlevel set
  have h_scalar_superlevel : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∫ y in {y | η y ≥ t}, g y ∂μ ≥ (1 / 2 : ℝ) * (μ {y | η y ≥ t}).toReal := by
    intro t ht
    rcases h_superlevel t ht with ⟨d, hd_lower, hd_upper, h_eq⟩
    have hd_pos : 0 < d := by linarith
    have hd_lt_scalar : d < R_scalar := by linarith
    rw [h_eq]
    exact h_scalar d hd_pos hd_lt_scalar

  have hμ_fin : μ Set.univ < ⊤ := by
    have h : μ Set.univ = perimeter S := by
      simpa [μ, perimeterMeasure] using (perimeter_eq_variation S hfin).symm
    rw [h]; exact hfin
  letI : IsFiniteMeasure μ := ⟨hμ_fin⟩

  have h_norm_int : Integrable (measureTheoreticNormal S) μ :=
    (measureTheoreticNormal_withDensity hfin).1
  have hg_int : Integrable g μ := by
    have h1 : Integrable (fun y => inner ℝ (measureTheoreticNormal S y) ν) μ :=
      h_norm_int.inner_const ν
    have h2 : g = fun y => inner ℝ (measureTheoreticNormal S y) ν := by
      funext y; exact real_inner_comm _ _
    rw [h2]; exact h1
  have hg_meas : Measurable g := by
    have h1 : Measurable (measureTheoreticNormal S) := measureTheoreticNormal_measurable hfin
    have h2 : Measurable (fun y => inner ℝ ν (measureTheoreticNormal S y)) := by fun_prop
    simpa [g] using h2

  -- Layer cake bound: ∫ η*g dμ ≥ (1/2) ∫ η dμ
  have h_layer : ∫ y, η y * g y ∂μ ≥ (1 / 2 : ℝ) * ∫ y, η y ∂μ :=
    layer_cake_weighted_bound hη_meas hg_int hg_meas hη_nonneg hη_le_one h_scalar_superlevel

  -- ∫ η dμ ≥ μ(closedBall x r_inner) since η = 1 there and η ≥ 0
  have hη_int : Integrable η μ := hη_smooth.continuous.integrable_of_hasCompactSupport hη_supp
  have h_int_η : ∫ y, η y ∂μ ≥ (μ (closedBall x r_inner)).toReal := by
    have h1 : ∫ y, η y ∂μ ≥ ∫ y in closedBall x r_inner, η y ∂μ :=
      setIntegral_le_integral hη_int (Eventually.of_forall hη_nonneg)
    have h4 : ∀ y ∈ closedBall x r_inner, η y = 1 := hη_one
    have h5 : ∫ y in closedBall x r_inner, η y ∂μ = ∫ y in closedBall x r_inner, (1 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with y hy
      exact h4 y hy
    have h3 : ∫ y in closedBall x r_inner, η y ∂μ = (μ (closedBall x r_inner)).toReal := by
      rw [h5]
      have h4 : ∫ y in closedBall x r_inner, (1 : ℝ) ∂μ = (μ (closedBall x r_inner)).toReal := by
        rw [MeasureTheory.setIntegral_const (1 : ℝ)]
        <;> simp [Measure.real]
      exact h4
    linarith

  have hμ_lower_inner : (μ (closedBall x r_inner)).toReal ≥ c_lower * r_inner ^ (n - 1) :=
    hμ_lower r_inner hr_inner_pos hr_inner_lt_lower

  have h_lower_bound : ∫ y, η y * g y ∂μ ≥ K * r_inner ^ (n - 1) := by
    calc
      ∫ y, η y * g y ∂μ
        ≥ (1 / 2 : ℝ) * ∫ y, η y ∂μ := h_layer
      _ ≥ (1 / 2 : ℝ) * (μ (closedBall x r_inner)).toReal := by gcongr
      _ ≥ (1 / 2 : ℝ) * (c_lower * r_inner ^ (n - 1)) := by
        exact mul_le_mul_of_nonneg_left hμ_lower_inner (by norm_num)
      _ = K * r_inner ^ (n - 1) := by
        simp [K] <;> ring

  -- Gauss-Green
  have h_gg : ∫ y in S, fderiv ℝ η y ν = ∫ y, η y * g y ∂μ :=
    gauss_green_scalar_identity hS hfin hν_unit hη_smooth hη_supp

  -- Gradient bound
  have h_grad_bound : ∀ y, ‖fderiv ℝ η y‖ ≤ C_grad / L := by
    intro y
    by_cases hy : y = x
    · rw [hy]
      have h_loc : ∀ᶠ (z : E n) in nhds x, η z = 1 := by
        have h5 : ball x r_inner ∈ nhds x := ball_mem_nhds x hr_inner_pos
        filter_upwards [h5] with z hz
        have h6 : z ∈ closedBall x r_inner := by
          have h7 : dist z x < r_inner := by simpa [ball] using hz
          simpa [closedBall, mem_closedBall] using le_of_lt h7
        exact radialCutoff_one_of_mem_closedBall hr_inner_pos hL_pos h6
      have hfd : HasFDerivAt η (0 : E n →L[ℝ] ℝ) x :=
        HasFDerivAt.congr_of_eventuallyEq (hasFDerivAt_const (1 : ℝ) x) h_loc
      have h_pos : 0 ≤ C_grad / L := by
        have h1 : 0 ≤ C_grad := hC_grad_nonneg
        have h2 : 0 < L := hL_pos
        exact div_nonneg h1 (by linarith)
      rw [hfd.fderiv]
      <;> simpa using h_pos
    · exact radialCutoff_fderiv_bound hr_inner_pos hL_pos hy

  have hA_sub_ball : closedBall x (r_inner + L) ⊆ ball x r := by
    intro y hy
    have h : dist y x ≤ r_inner + L := by simpa [closedBall] using hy
    have h2 : r_inner + L < r := by
      rw [hr_inner_def, hL_def]
      dsimp only [r_inner_frac, L_frac]
      have hpos : 0 < r := hr_pos
      linarith
    simpa [ball] using h.trans_lt h2

  have h_deriv_zero : ∀ y, y ∉ ball x r → fderiv ℝ η y ν = 0 := by
    intro y hy
    have h_r_lt : r_inner + L < r := by
      rw [hr_inner_def, hL_def]
      have h : (1 / 2 : ℝ) * r + (1 / 3 : ℝ) * r < r := by
        have hpos : 0 < r := hr_pos
        linarith
      exact h
    have h_dist : r_inner + L < dist y x := by
      have h1 : r ≤ dist y x := by simpa [ball, not_lt] using hy
      calc r_inner + L < r := h_r_lt
        _ ≤ dist y x := h1
    have h4 : ∀ᶠ (z : E n) in nhds y, η z = 0 := by
      have h5 : ball y (dist y x - (r_inner + L)) ∈ nhds y := ball_mem_nhds y (by linarith)
      filter_upwards [h5] with z hz
      have h6 : dist z y < dist y x - (r_inner + L) := by simpa [ball] using hz
      have h7 : dist y x ≤ dist z y + dist z x := by
        have h : dist y x ≤ dist y z + dist z x := dist_triangle y z x
        rw [dist_comm y z] at h
        exact h
      have h7' : dist z x ≥ dist y x - dist z y := by linarith
      have h8 : r_inner + L < dist z x := by linarith
      have h9 : z ∉ ball x (r_inner + L) := by simpa [ball, not_lt] using le_of_lt h8
      exact radialCutoff_zero_of_not_mem_ball hr_inner_pos hL_pos h9
    have h10 : HasFDerivAt η (0 : E n →L[ℝ] ℝ) y :=
      HasFDerivAt.congr_of_eventuallyEq (hasFDerivAt_const (0 : ℝ) y) h4
    have h11 : fderiv ℝ η y = 0 := h10.fderiv
    rw [h11] <;> simp

  have h_ball_meas : MeasurableSet (ball x r) := isOpen_ball.measurableSet
  have hS_ball_meas : MeasurableSet (S ∩ ball x r) := hS.inter h_ball_meas

  have h_upper_bound : |∫ y in S, fderiv ℝ η y ν| ≤ (C_grad / L) * (volume (S ∩ ball x r)).toReal := by
    have h1 : |∫ y in S, fderiv ℝ η y ν| ≤ ∫ y in S, |fderiv ℝ η y ν| :=
      abs_integral_le_integral_abs
    have h2 : ∀ y, |fderiv ℝ η y ν| ≤ C_grad / L := by
      intro y
      have h3 : |fderiv ℝ η y ν| ≤ ‖fderiv ℝ η y‖ * ‖ν‖ := (fderiv ℝ η y).le_opNorm ν
      have h4 : ‖fderiv ℝ η y‖ * ‖ν‖ = ‖fderiv ℝ η y‖ := by
        rw [hν_unit] <;> ring
      rw [h4] at h3
      exact le_trans h3 (h_grad_bound y)
    have h_eq : ∫ y in S, |fderiv ℝ η y ν| = ∫ y in S ∩ ball x r, |fderiv ℝ η y ν| := by
      let f := fun y : E n => |fderiv ℝ η y ν|
      have h_decomp : S = (S ∩ ball x r) ∪ (S \ ball x r) := by
        ext y; simp [and_or_left] <;> tauto
      have h_disj : Disjoint (S ∩ ball x r) (S \ ball x r) := by
        rw [Set.disjoint_left]
        intro y h1 h2
        exact h2.2 h1.2
      have hS_diff_meas : MeasurableSet (S \ ball x r) := hS.diff h_ball_meas
      have h_int_ball : IntegrableOn f (S ∩ ball x r) :=
        directionalDerivative_integrable (S := S ∩ ball x r) hη_smooth hη_supp ν |>.abs
      have h_int_diff : IntegrableOn f (S \ ball x r) :=
        directionalDerivative_integrable (S := S \ ball x r) hη_smooth hη_supp ν |>.abs
      have h_eq_on : ∀ (y : E n), y ∈ (S \ ball x r) → f y = 0 := by
        intro y hy
        have h2 : y ∉ ball x r := hy.2
        have h3 : fderiv ℝ η y ν = 0 := h_deriv_zero y h2
        have h4 : f y = |fderiv ℝ η y ν| := by rfl
        rw [h4, h3] <;> simp
      have h4_ae : ∀ᵐ (y : E n) ∂volume.restrict (S \ ball x r), f y = 0 := by
        filter_upwards [ae_restrict_mem hS_diff_meas] with y hy
        exact h_eq_on y hy
      have h_zero : ∫ y in S \ ball x r, f y = 0 := by
        rw [integral_congr_ae h4_ae] <;> simp
      have h_union_int : ∫ y in (S ∩ ball x r) ∪ (S \ ball x r), f y =
          (∫ y in (S ∩ ball x r), f y) + (∫ y in (S \ ball x r), f y) :=
        MeasureTheory.setIntegral_union h_disj hS_diff_meas h_int_ball h_int_diff
      have h_main : ∫ y in S, f y = ∫ y in (S ∩ ball x r), f y := by
        have h5 : S = (S ∩ ball x r) ∪ (S \ ball x r) := h_decomp
        have h_meas : volume.restrict S = volume.restrict ((S ∩ ball x r) ∪ (S \ ball x r)) :=
          congr_arg volume.restrict h5
        have h6 : ∫ y in S, f y = ∫ y in (S ∩ ball x r) ∪ (S \ ball x r), f y := by
          exact congr_arg (fun m : Measure (E n) => ∫ y, f y ∂m) h_meas
        rw [h6, h_union_int, h_zero] <;> simp
      exact h_main
    have h4 : ∫ y in S ∩ ball x r, |fderiv ℝ η y ν| ≤ ∫ y in S ∩ ball x r, (C_grad / L : ℝ) := by
      have h_int1 : IntegrableOn (fun y => |fderiv ℝ η y ν|) (S ∩ ball x r) := by
        exact directionalDerivative_integrable (S := S ∩ ball x r) hη_smooth hη_supp ν |>.abs
      have h_int2 : IntegrableOn (fun y : E n => (C_grad / L : ℝ)) (S ∩ ball x r) :=
        integrableOn_const
      exact setIntegral_mono_on h_int1 h_int2 hS_ball_meas (fun y _ => h2 y)
    have h_combined : ∫ y in S, |fderiv ℝ η y ν| ≤ ∫ y in S ∩ ball x r, (C_grad / L : ℝ) := by
      rw [h_eq]
      exact h4
    have h5 : ∫ y in S ∩ ball x r, (C_grad / L : ℝ) =
        (C_grad / L) * (volume (S ∩ ball x r)).toReal := by
      have h : ∫ y in S ∩ ball x r, (C_grad / L : ℝ) =
          (volume (S ∩ ball x r)).toReal * (C_grad / L) := by
        rw [MeasureTheory.setIntegral_const (C_grad / L : ℝ)]
        <;> simp [Measure.real]
      rw [h]
      <;> ring
    calc |∫ y in S, fderiv ℝ η y ν|
      ≤ ∫ y in S, |fderiv ℝ η y ν| := h1
    _ ≤ ∫ y in S ∩ ball x r, (C_grad / L : ℝ) := h_combined
    _ = (C_grad / L) * (volume (S ∩ ball x r)).toReal := h5

  have h_main : (volume (S ∩ ball x r)).toReal ≥ c * r ^ n := by
    have h3 : ∫ y, η y * g y ∂μ = ∫ y in S, fderiv ℝ η y ν := h_gg.symm
    rw [h3] at h_lower_bound
    have h4 : (C_grad / L) * (volume (S ∩ ball x r)).toReal ≥ K * r_inner ^ (n - 1) := by
      calc (C_grad / L) * (volume (S ∩ ball x r)).toReal
        ≥ |∫ y in S, fderiv ℝ η y ν| := h_upper_bound
      _ ≥ ∫ y in S, fderiv ℝ η y ν := by exact le_abs_self _
      _ ≥ K * r_inner ^ (n - 1) := h_lower_bound
    have h5 : (volume (S ∩ ball x r)).toReal ≥
        (K * r_inner ^ (n - 1)) / (C_grad / L) := by
      have h6 : 0 < C_grad / L := div_pos hC_grad_pos hL_pos
      have h7 : 0 ≤ (volume (S ∩ ball x r)).toReal := by positivity
      have h8 : (C_grad / L) * (volume (S ∩ ball x r)).toReal ≥ K * r_inner ^ (n - 1) := h4
      have h9 : (volume (S ∩ ball x r)).toReal =
          ((C_grad / L) * (volume (S ∩ ball x r)).toReal) / (C_grad / L) := by
        have h10 : (C_grad / L) * (volume (S ∩ ball x r)).toReal / (C_grad / L) = (volume (S ∩ ball x r)).toReal := by
          field_simp [h6.ne'] <;> ring
        exact h10.symm
      rw [h9]
      gcongr
    have h7 : (K * r_inner ^ (n - 1)) / (C_grad / L) = c * r ^ n := by
      have h1 : r_inner = r_inner_frac * r := hr_inner_def
      have h2 : L = L_frac * r := hL_def
      have h3 : c = K * r_inner_frac ^ (n - 1) * L_frac / C_grad := by rfl
      have h4 : C_grad ≠ 0 := hC_grad_pos.ne'
      have hL_ne : L ≠ 0 := hL_pos.ne'
      have h8 : n ≥ 1 := by linarith
      have h9 : r ^ (n - 1) * r = r ^ n := by
        have h10 : (n - 1) + 1 = n := by omega
        have h11 : r ^ (n - 1) * r = r ^ ((n - 1) + 1) := by rw [pow_succ]
        rw [h11, h10]
      have h10 : (K * r_inner ^ (n - 1)) / (C_grad / L) = K * r_inner ^ (n - 1) * L / C_grad := by
        field_simp [h4, hL_ne] <;> ring
      rw [h10, h1, h2, h3]
      rw [mul_pow]
      have h11 : K * (r_inner_frac ^ (n - 1) * r ^ (n - 1)) * (L_frac * r) / C_grad =
          (K * r_inner_frac ^ (n - 1) * L_frac / C_grad) * r ^ n := by
        have h12 : K * (r_inner_frac ^ (n - 1) * r ^ (n - 1)) * (L_frac * r) =
            K * r_inner_frac ^ (n - 1) * L_frac * (r ^ (n - 1) * r) := by ring
        rw [h12, h9] <;> ring
      exact h11
    rw [h7] at h5
    exact h5

  have h_vol : volume (S ∩ ball x r) ≠ ⊤ := by
    have h : volume (S ∩ ball x r) ≤ volume (ball x r) := measure_mono fun x hx => hx.2
    have h_ball_lt_top : volume (ball x r) < ⊤ := MeasureTheory.measure_ball_lt_top
    exact h.trans_lt h_ball_lt_top |>.ne

  rw [← ENNReal.ofReal_toReal h_vol]
  exact ENNReal.ofReal_le_ofReal h_main

/-- For a smooth compactly supported function, the integral of its directional
derivative over all of `ℝⁿ` is zero.

Proof: difference quotients `(η(y + t•ν) - η(y))/t` converge pointwise to
`fderiv ℝ η y ν`, are dominated by an integrable function (Lipschitz bound +
compact support), and each has integral zero by translation invariance of
Lebesgue measure. -/
lemma integral_directionalDeriv_univ_eq_zero {n : ℕ} {η : E n → ℝ} {ν : E n}
    (hη_smooth : ContDiff ℝ ∞ η) (hη_supp : HasCompactSupport η) :
    ∫ y, fderiv ℝ η y ν = 0 := by
  by_cases hν : ν = 0
  · simp [hν]
  · let g : E n → (E n →L[ℝ] ℝ) := fderiv ℝ η
    have hg_cont : Continuous g := hη_smooth.continuous_fderiv (by norm_num)
    have h_diff : Differentiable ℝ η := hη_smooth.differentiable (by norm_num)

    -- g = fderiv η has compact support (contained in tsupport η)
    have hg_supp : HasCompactSupport g := by
      have h1 : Function.support g ⊆ tsupport η := by
        intro x hx
        by_contra h2
        have h3 : η =ᶠ[nhds x] 0 := by
          have h4 : IsOpen (tsupport η)ᶜ := isClosed_closure.isOpen_compl
          exact Filter.eventually_of_mem (IsOpen.mem_nhds h4 h2) (fun y hy => by
            have h5 : y ∉ Function.support η := fun h6 => hy (subset_closure h6)
            simpa [Function.mem_support] using h5)
        have h4 : HasFDerivAt η (0 : E n →L[ℝ] ℝ) x :=
          HasFDerivAt.congr_of_eventuallyEq (hasFDerivAt_const (0 : ℝ) x) h3
        have h5 : g x = 0 := by simpa [g] using h4.fderiv
        exact hx h5
      have h2 : closure (Function.support g) ⊆ tsupport η := closure_minimal h1 isClosed_closure
      exact hη_supp.of_isClosed_subset isClosed_closure h2

    -- Bound C on ‖g‖ everywhere
    have hC : ∃ (C : ℝ), 0 ≤ C ∧ ∀ y, ‖g y‖ ≤ C := by
      let K := tsupport g
      have hK : IsCompact K := hg_supp
      have h4 : BddAbove (Set.image (fun y => ‖g y‖) K) :=
        hK.bddAbove_image (continuous_norm.comp hg_cont).continuousOn
      rcases h4 with ⟨C0, hC0⟩
      let C := max C0 0
      refine ⟨C, by positivity, fun y => ?_⟩
      by_cases hy : y ∈ K
      · exact le_trans (hC0 ⟨y, hy, rfl⟩) (le_max_left _ _)
      · have h6 : g y = 0 := by
          have h7 : y ∉ Function.support g := fun h8 => hy (subset_closure h8)
          simpa [Function.mem_support] using h7
        rw [h6]
        have h7 : 0 ≤ C := by positivity
        simpa using h7

    rcases hC with ⟨C, hC_nonneg, hC_bound⟩
    let B : ℝ := C * ‖ν‖

    -- η is C-Lipschitz
    have h_lip : ∀ (x y : E n), |η x - η y| ≤ C * ‖x - y‖ := by
      intro x y
      have h : ‖η y - η x‖ ≤ C * ‖y - x‖ :=
        Convex.norm_image_sub_le_of_norm_fderiv_le
          (fun z _ => h_diff.differentiableAt) (fun z _ => hC_bound z) convex_univ trivial trivial
      have h2 : ‖η x - η y‖ ≤ C * ‖x - y‖ := by
        have h3 : ‖η x - η y‖ = ‖η y - η x‖ := by rw [norm_sub_rev]
        rw [h3]
        have h4 : ‖y - x‖ = ‖x - y‖ := by rw [norm_sub_rev]
        rw [h4] at h
        exact h
      have h5 : |η x - η y| = ‖η x - η y‖ := by
        simp [Real.norm_eq_abs]
      rw [h5]
      exact h2

    let K := tsupport η
    let K' : Set (E n) := Set.image2 (· + ·) K (closedBall (0 : E n) ‖ν‖)
    have hK_compact : IsCompact K := hη_supp.isCompact
    have hK'_eq : K' = (fun p : E n × E n => p.1 + p.2) '' (K ×ˢ closedBall (0 : E n) ‖ν‖) := by
      ext z
      simp only [K', Set.image2, Set.mem_image, Set.mem_prod]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
    have hK'_compact : IsCompact K' := by
      rw [hK'_eq]
      exact (hK_compact.prod (isCompact_closedBall _ _)).image continuous_add
    have hK'_meas : MeasurableSet K' := hK'_compact.measurableSet
    have hK'_fin : volume K' ≠ ⊤ := hK'_compact.measure_lt_top.ne

    -- Difference quotient support ⊆ K' for 0 < |t| ≤ 1
    have h_supp : ∀ (t : ℝ), 0 < |t| → |t| ≤ 1 →
        Function.support (fun y : E n => (η (y + t • ν) - η y) / t) ⊆ K' := by
      intro t hpos hle y hy
      have hne : (η (y + t • ν) - η y) / t ≠ 0 := hy
      have hne2 : η (y + t • ν) ≠ η y := by
        intro h; apply hne; rw [h]; simp
      by_cases h1 : η (y + t • ν) ≠ 0
      · have h2 : y + t • ν ∈ K := subset_closure h1
        have h3 : y = (y + t • ν) + (-t) • ν := by
          have h4 : (y + t • ν) + (-t) • ν = y + (t • ν + (-t) • ν) := by abel
          rw [h4]
          have h5 : t • ν + (-t) • ν = (t + -t) • ν := by rw [←add_smul]
          rw [h5]
          have h6 : t + -t = 0 := by ring
          rw [h6, zero_smul, add_zero]
        rw [h3]
        have h4 : (-t) • ν ∈ closedBall (0 : E n) ‖ν‖ := by
          have h5 : ‖(-t) • ν‖ = |t| * ‖ν‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_neg]
          have h6 : ‖(-t) • ν‖ ≤ ‖ν‖ := by
            rw [h5]
            have h7 : |t| * ‖ν‖ ≤ 1 * ‖ν‖ := by gcongr <;> positivity
            simpa using h7
          simpa [mem_closedBall, dist_zero_right] using h6
        exact Set.mem_image2.mpr ⟨y + t • ν, h2, (-t) • ν, h4, by abel⟩
      · have h5 : η y ≠ 0 := by
          by_contra h6
          have h7 : η (y + t • ν) = 0 := by tauto
          rw [h7, h6] at hne2 <;> tauto
        have h6 : y ∈ K := subset_closure h5
        have h7 : (0 : E n) ∈ closedBall (0 : E n) ‖ν‖ := by
          simp [mem_closedBall] <;> positivity
        exact Set.mem_image2.mpr ⟨y, h6, (0 : E n), h7, by simp⟩

    -- Dominating function D = B * 1_{K'}
    let D : E n → ℝ := fun y => B * Set.indicator K' (1 : E n → ℝ) y
    have hD_int : Integrable D volume := by
      have h1 : Integrable (Set.indicator K' (1 : E n → ℝ)) volume := by
        rw [integrable_indicator_iff hK'_meas]
        exact MeasureTheory.integrableOn_const (hs := hK'_fin)
      exact h1.const_mul B

    -- Sequence t_k = 1/(k+2)
    let t_seq : ℕ → ℝ := fun k => (1 : ℝ) / (k + 2)
    have ht_seq_pos : ∀ k, 0 < t_seq k := by intro k; positivity
    have ht_seq_lim : Filter.Tendsto t_seq Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun k : ℕ => ((k : ℝ) + 2)) Filter.atTop Filter.atTop := by
        apply Filter.tendsto_atTop_atTop.mpr
        intro b
        refine ⟨Nat.ceil b, fun n hn => ?_⟩
        have h_ceil : b ≤ (Nat.ceil b : ℝ) := Nat.le_ceil b
        have h_n_ge : (Nat.ceil b : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have h : (n : ℝ) ≥ b := by linarith
        linarith
      have h2 : Filter.Tendsto (fun k : ℕ => (((k : ℝ) + 2)⁻¹)) Filter.atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp h1
      simpa [t_seq] using h2
    have ht_seq_le_one : ∀ k, |t_seq k| ≤ 1 := by
      intro k
      have h : 0 < t_seq k := ht_seq_pos k
      have h2 : t_seq k ≤ 1 := by
        dsimp only [t_seq]
        have h3 : (k : ℝ) + 2 ≥ 1 := by
          have h4 : 0 ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
          linarith
        exact (div_le_one (by positivity)).mpr h3
      rw [abs_of_pos h]; exact h2

    let Q : ℕ → (E n → ℝ) := fun k y => (η (y + t_seq k • ν) - η y) / t_seq k
    let f : E n → ℝ := fun y => fderiv ℝ η y ν

    -- Pointwise bound |Q k y| ≤ D y
    have h_bound : ∀ k y, |Q k y| ≤ D y := by
      intro k y
      by_cases hys : y ∈ K'
      · have h1_raw : |η (y + t_seq k • ν) - η y| ≤ C * ‖(y + t_seq k • ν) - y‖ := h_lip (y + t_seq k • ν) y
        have h1_simp : (y + t_seq k • ν) - y = t_seq k • ν := by abel
        have h1 : |η (y + t_seq k • ν) - η y| ≤ C * ‖(t_seq k • ν)‖ := by
          rw [h1_simp] at h1_raw
          exact h1_raw
        have h1' : C * ‖(t_seq k • ν)‖ = |t_seq k| * B := by
          have h2 : ‖(t_seq k • ν)‖ = |t_seq k| * ‖ν‖ := by
            rw [norm_smul, Real.norm_eq_abs]
          rw [h2]
          simp [B] <;> ring
        have h2 : abs (Q k y) ≤ B := by
          dsimp only [Q]
          calc
            abs ((η (y + t_seq k • ν) - η y) / t_seq k)
              = abs (η (y + t_seq k • ν) - η y) / abs (t_seq k) := by rw [abs_div]
            _ ≤ (C * ‖(t_seq k • ν)‖) / abs (t_seq k) := by gcongr
            _ = (abs (t_seq k) * B) / abs (t_seq k) := by rw [h1']
            _ = B := by
              have h3 : abs (t_seq k) ≠ 0 := by
                have h4 : t_seq k ≠ 0 := (ht_seq_pos k).ne'
                have h5 : 0 < abs (t_seq k) := abs_pos.mpr h4
                exact h5.ne'
              field_simp [h3] <;> ring
        have h4 : D y = B := by
          simp [D, hys, Set.indicator_apply] <;> ring
        rw [h4]; exact h2
      · have h5 : Q k y = 0 := by
          have h6 : y ∉ Function.support (Q k) := by
            intro h7
            have h8 : y ∈ K' := h_supp (t_seq k)
              (by have h : t_seq k ≠ 0 := (ht_seq_pos k).ne'; exact abs_pos.mpr h)
              (ht_seq_le_one k) h7
            exact hys h8
          simpa [Function.mem_support] using h6
        have h7 : D y = 0 := by simp [D, hys, Set.indicator_apply]
        rw [h5, h7] <;> simp

    -- Q k is integrable (continuous + compact support)
    have hQ_int : ∀ k, Integrable (Q k) volume := by
      intro k
      have h_cont : Continuous (Q k) := by fun_prop
      have h_supp' : HasCompactSupport (Q k) :=
        let supp := Function.support (Q k)
        have h1 : supp ⊆ K' := h_supp (t_seq k) (by have h : t_seq k ≠ 0 := (ht_seq_pos k).ne'; exact abs_pos.mpr h) (ht_seq_le_one k)
        have h2 : closure supp ⊆ K' := closure_minimal h1 hK'_compact.isClosed
        hK'_compact.of_isClosed_subset isClosed_closure h2
      exact h_cont.integrable_of_hasCompactSupport h_supp'

    -- Pointwise convergence Q k y → f y
    have h_conv : ∀ y, Filter.Tendsto (fun k : ℕ => Q k y) Filter.atTop (nhds (f y)) := by
      intro y
      dsimp only [Q, f]
      have hfd : HasFDerivAt η (fderiv ℝ η y) y := h_diff.differentiableAt.hasFDerivAt
      have h1 : HasDerivAt (fun t : ℝ => t • ν) ν 0 := by
        have h : HasDerivAt (fun t : ℝ => t • ν) ((1 : ℝ) • ν) 0 := (hasDerivAt_id (0 : ℝ)).smul_const ν
        simpa using h
      have h_inner : HasDerivAt (fun t : ℝ => y + t • ν) ν 0 := h1.const_add y
      have h_y : y + (0 : ℝ) • ν = y := by simp
      have hfd' : HasFDerivAt η (fderiv ℝ η y) (y + (0 : ℝ) • ν) := by
        rw [h_y]
        exact hfd
      have h : HasDerivAt (fun t : ℝ => η (y + t • ν)) (fderiv ℝ η y ν) 0 :=
        hfd'.comp_hasDerivAt 0 h_inner
      have h_tendsto_slope : Filter.Tendsto (fun t : ℝ => (η (y + t • ν) - η y) / t) (nhdsWithin 0 {0}ᶜ) (nhds (fderiv ℝ η y ν)) := by
        convert h.tendsto_slope using 1
        funext t
        simp [slope]
        <;> ring
      have ht_seq_punctured : Filter.Tendsto t_seq Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨ht_seq_lim, Filter.Eventually.of_forall (fun k => (ht_seq_pos k).ne')⟩
      exact h_tendsto_slope.comp ht_seq_punctured

    -- DCT
    have h_dct : Filter.Tendsto (fun k : ℕ => ∫ y, Q k y) Filter.atTop (nhds (∫ y, f y)) :=
      MeasureTheory.tendsto_integral_of_dominated_convergence D
        (fun k => (hQ_int k).aestronglyMeasurable) hD_int
        (fun k => Filter.Eventually.of_forall (h_bound k))
        (Filter.Eventually.of_forall h_conv)

    -- Each integral ∫ Q k = 0 by translation invariance
    have h_zero : ∀ k, ∫ y, Q k y = 0 := by
      intro k
      have hη_int : Integrable η volume := hη_smooth.continuous.integrable_of_hasCompactSupport hη_supp
      have h_trans : ∫ y, η (y + t_seq k • ν) = ∫ y, η y := by
        let τ : E n → E n := fun y => y + t_seq k • ν
        have hmp : MeasurePreserving τ volume := by exact measurePreserving_add_right volume (t_seq k • ν)
        have h_eq : ∫ y, η (τ y) = ∫ z, η z := by exact integral_add_right_eq_self η (t_seq k • ν)
        exact h_eq
      dsimp only [Q]
      have hη_trans_int : Integrable (fun y : E n => η (y + t_seq k • ν)) volume := by
        let τ : E n → E n := fun y => y + t_seq k • ν
        have hmp : MeasurePreserving τ volume := by exact measurePreserving_add_right volume (t_seq k • ν)
        have h : Integrable (η ∘ τ) volume := by exact MeasurePreserving.integrable_comp_of_integrable hmp hη_int
        simpa [Function.comp_def] using h
      have hdiv : (fun y : E n => (η (y + t_seq k • ν) - η y) / t_seq k) =
          fun y : E n => (t_seq k)⁻¹ * (η (y + t_seq k • ν) - η y) := by
        funext y
        field_simp [(ht_seq_pos k).ne']
        <;> ring
      have h2 : ∫ y, (η (y + t_seq k • ν) - η y) =
          (∫ y, η (y + t_seq k • ν)) - (∫ y, η y) :=
        integral_sub hη_trans_int hη_int
      have h : ∫ y, (η (y + t_seq k • ν) - η y) / t_seq k =
          (t_seq k)⁻¹ * ((∫ y, η (y + t_seq k • ν)) - (∫ y, η y)) := by
        rw [hdiv, integral_const_mul, h2] <;> ring
      rw [h, h_trans] <;> ring

    have h_lim_zero : Filter.Tendsto (fun k : ℕ => ∫ y, Q k y) Filter.atTop (nhds 0) := by
      simpa [h_zero] using tendsto_const_nhds

    exact tendsto_nhds_unique h_dct h_lim_zero

/-- **Scalar comparability at almost every boundary point**.

For `perimeterMeasure U`-a.e. `x`, there exists `r0 > 0` such that for all
`0 < r < r0`,
`∫_{closedBall x r} inner(ν_U(x), ν_U(y)) dμ ≥ (1/2) * μ(closedBall x r).toReal`.

Proof: By Besicovitch differentiation, the average of `ν_U` over closed balls
converges to `ν_U(x)` for `μ`-a.e. `x`. Taking the inner product with `ν_U(x)`
(a continuous operation) gives convergence of the scalar average to
`inner(ν_U(x), ν_U(x)) = ‖ν_U(x)‖² = 1`. Hence for small `r` the average
exceeds `1/2`. -/
lemma scalar_comparability_ae
    {U : Set (E n)} (h_perim_finite : perimeter U < ⊤) :
    ∀ᵐ (x : E n) ∂(perimeterMeasure U),
      ∃ (r0 : ℝ), 0 < r0 ∧ ∀ (r : ℝ), 0 < r → r < r0 →
        (∫ y in closedBall x r, inner ℝ (measureTheoreticNormal U x) (measureTheoreticNormal U y) ∂(perimeterMeasure U)) ≥
        (1 / 2 : ℝ) * (perimeterMeasure U (closedBall x r)).toReal := by
  let μ := perimeterMeasure U
  let ν_U := measureTheoreticNormal U

  have hμ_fin : μ Set.univ < ⊤ := by
    rw [← perimeter_eq_variation U h_perim_finite] <;> exact h_perim_finite
  letI : IsFiniteMeasure μ := ⟨hμ_fin⟩

  have hν_norm : ∀ᵐ y ∂μ, ‖ν_U y‖ = 1 := norm_measureTheoreticNormal_eq_one h_perim_finite
  have hν_integrable : Integrable ν_U μ := by
    refine' ⟨(measureTheoreticNormal_measurable h_perim_finite).aestronglyMeasurable, _⟩
    have h2 : HasFiniteIntegral ν_U μ := by
      have h3 : ∀ᵐ y ∂μ, ‖ν_U y‖ ≤ 1 := by
        filter_upwards [hν_norm] with y hy <;> rw [hy] <;> norm_num
      exact HasFiniteIntegral.of_bounded (C := 1) h3
    exact h2
  have hν_int : LocallyIntegrable ν_U μ := hν_integrable.locallyIntegrable

  let v : VitaliFamily μ := Besicovitch.vitaliFamily μ

  have h_avg : ∀ᵐ (x : E n) ∂μ,
      Filter.Tendsto (fun r : ℝ => ⨍ y in closedBall x r, ν_U y ∂μ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (ν_U x)) := by
    have h1 : ∀ᵐ (x : E n) ∂μ,
        Filter.Tendsto (fun a : Set (E n) => ⨍ y in a, ν_U y ∂μ)
          (v.filterAt x) (nhds (ν_U x)) :=
      VitaliFamily.ae_tendsto_average v hν_int
    filter_upwards [h1] with x hx
    have h2 : Filter.Tendsto (fun r : ℝ => closedBall x r) (nhdsWithin 0 (Set.Ioi 0)) (v.filterAt x) :=
      Besicovitch.tendsto_filterAt μ x
    exact hx.comp h2

  have h_comm : ∀ (x : E n) (s : Set (E n)),
      inner ℝ (ν_U x) (⨍ y in s, ν_U y ∂μ) =
      ⨍ y in s, inner ℝ (ν_U x) (ν_U y) ∂μ := by
    intro x s
    let l : E n →L[ℝ] ℝ :=
      { toFun := fun z => inner ℝ (ν_U x) z
        map_add' := by simp [inner_add_right]
        map_smul' := by simp [inner_smul_right] <;> ring }
    have h_avg_eq : (⨍ y in s, ν_U y ∂μ) = (μ s).toReal⁻¹ • (∫ y in s, ν_U y ∂μ) := by
      rw [MeasureTheory.average_eq]
      have h_restrict : (μ.restrict s).real Set.univ = (μ s).toReal := by
        have h : (μ.restrict s) Set.univ = μ s := by
          simp [Measure.restrict_apply]
        exact congr_arg ENNReal.toReal h
      rw [h_restrict] <;> rfl
    rw [h_avg_eq]
    have h5 : inner ℝ (ν_U x) ((μ s).toReal⁻¹ • (∫ y in s, ν_U y ∂μ)) =
        (μ s).toReal⁻¹ * inner ℝ (ν_U x) (∫ y in s, ν_U y ∂μ) := by
      rw [inner_smul_right] <;> ring
    rw [h5]
    have h6 : inner ℝ (ν_U x) (∫ y in s, ν_U y ∂μ) = ∫ y in s, inner ℝ (ν_U x) (ν_U y) ∂μ := by
      exact (integral_inner hν_integrable.integrableOn (ν_U x)).symm
    rw [h6]
    have h7 : (μ s).toReal⁻¹ * (∫ y in s, inner ℝ (ν_U x) (ν_U y) ∂μ) =
        ⨍ y in s, inner ℝ (ν_U x) (ν_U y) ∂μ := by
      rw [MeasureTheory.average_eq]
      have h_restrict : (μ.restrict s).real Set.univ = (μ s).toReal := by
        have h : (μ.restrict s) Set.univ = μ s := by
          simp [Measure.restrict_apply]
        exact congr_arg ENNReal.toReal h
      rw [h_restrict] <;> ring
    exact h7

  filter_upwards [h_avg, hν_norm] with x hx_avg hx_norm

  have hx1 : Filter.Tendsto (fun r : ℝ => inner ℝ (ν_U x) (⨍ y in closedBall x r, ν_U y ∂μ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (inner ℝ (ν_U x) (ν_U x))) :=
    (continuous_const.inner continuous_id).tendsto (ν_U x) |>.comp hx_avg

  have h_inner_avg : (fun r : ℝ => inner ℝ (ν_U x) (⨍ y in closedBall x r, ν_U y ∂μ)) =
      fun r : ℝ => ⨍ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ := by
    funext r
    exact h_comm x (closedBall x r)

  rw [h_inner_avg] at hx1

  have h_norm2 : inner ℝ (ν_U x) (ν_U x) = 1 := by
    have h : inner ℝ (ν_U x) (ν_U x) = ‖ν_U x‖ ^ 2 := inner_self_eq_norm_sq_to_K (ν_U x)
    rw [h, hx_norm] <;> norm_num

  rw [h_norm2] at hx1

  have h_eventually : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      (⨍ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) > 1 / 2 :=
    hx1 (Ioi_mem_nhds (by norm_num))

  rcases mem_nhdsWithin.mp h_eventually with ⟨U, hU_open, h0_U, hU_sub⟩

  have h_ball : ∃ (r0 : ℝ), 0 < r0 ∧ ball (0 : ℝ) r0 ⊆ U :=
    Metric.isOpen_iff.mp hU_open 0 h0_U
  rcases h_ball with ⟨r0, hr0_pos, hball_sub⟩

  refine ⟨r0, hr0_pos, fun r hr_pos hr_lt => ?_⟩

  have h_r_in_U : r ∈ U := by
    have h : dist (r : ℝ) 0 < r0 := by
      have h' : dist (r : ℝ) 0 = |r| := by
        simp [dist_eq_norm, Real.norm_eq_abs]
      rw [h']
      have h'' : |r| = r := abs_of_pos hr_pos
      rw [h'']
      exact hr_lt
    exact hball_sub h

  have h_r_in : r ∈ U ∩ Set.Ioi (0 : ℝ) := ⟨h_r_in_U, hr_pos⟩

  have h3 : (⨍ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) > 1 / 2 :=
    hU_sub h_r_in

  have h4 : (⨍ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) =
      (∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) / (μ (closedBall x r)).toReal := by
    have h_avg : (⨍ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) =
        (μ (closedBall x r)).toReal⁻¹ * (∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) := by
      rw [MeasureTheory.average_eq]
      have h_restrict : (μ.restrict (closedBall x r)).real Set.univ = (μ (closedBall x r)).toReal := by
        have h : (μ.restrict (closedBall x r)) Set.univ = μ (closedBall x r) := by
          simp [Measure.restrict_apply]
        exact congr_arg ENNReal.toReal h
      rw [h_restrict]
      <;> rfl
    rw [h_avg]
    field_simp <;> ring

  rw [h4] at h3

  by_cases h5 : (μ (closedBall x r)).toReal = 0
  · have h_div_zero : (∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) / (μ (closedBall x r)).toReal = 0 := by
      rw [h5] <;> simp
    rw [h_div_zero] at h3
    norm_num at h3
  · have h6 : 0 < (μ (closedBall x r)).toReal := by
      have h7 : 0 ≤ (μ (closedBall x r)).toReal := by positivity
      exact h7.lt_of_ne (Ne.symm h5)
    have h8 : (∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) ≥
        (1 / 2 : ℝ) * (μ (closedBall x r)).toReal := by
      have h9 : ((∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) / (μ (closedBall x r)).toReal) * (μ (closedBall x r)).toReal =
          (∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) := by
        field_simp [h5] <;> ring
      have h10 : ((∫ y in closedBall x r, inner ℝ (ν_U x) (ν_U y) ∂μ) / (μ (closedBall x r)).toReal) * (μ (closedBall x r)).toReal ≥
          (1 / 2 : ℝ) * (μ (closedBall x r)).toReal := by
        gcongr
      rw [h9] at h10
      exact h10
    exact h8

/-- **Scalar comparability property** at a point `x`.

There exists `r0 > 0` such that for all `0 < r < r0`, the integral of
`inner(ν_U(x), ν_U(y))` over `closedBall x r` is at least half the
perimeter measure of the ball. -/
def scalarComparabilityProperty (U : Set (E n)) (x : E n) : Prop :=
  ∃ (r0 : ℝ), 0 < r0 ∧ ∀ (r : ℝ), 0 < r → r < r0 →
    (∫ y in closedBall x r, inner ℝ (measureTheoreticNormal U x) (measureTheoreticNormal U y) ∂(perimeterMeasure U)) ≥
    (1 / 2 : ℝ) * (perimeterMeasure U (closedBall x r)).toReal

/-- **Good set** for scalar comparability. -/
def scalarComparabilityGoodSet (U : Set (E n)) : Set (E n) :=
  {x | scalarComparabilityProperty U x}

/-- **Full-measure bridge**: the set of points where scalar comparability
holds has full perimeter measure (its complement has measure 0).

This is a direct restatement of `scalar_comparability_ae`. -/
lemma scalar_comparability_goodSet_fullMeasure
    {U : Set (E n)} (hfin : perimeter U < ⊤) :
    perimeterMeasure U ((scalarComparabilityGoodSet U)ᶜ) = 0 := by
  have h_ae : ∀ᵐ (x : E n) ∂(perimeterMeasure U), scalarComparabilityProperty U x :=
    scalar_comparability_ae hfin
  exact h_ae

/-- **Perimeter density lower bound** (Gauss-Green cutoff approach).

At a reduced boundary point `x` with normal `ν`, conditional on perimeter measure
density bounds and Besicovitch differentiation, both `volume(S ∩ B(x,r))` and
`volume(B(x,r) \\ S)` are bounded below by `c * r^n` for small `r`. -/
theorem perimeter_density_lower_bound
    {S : Set (E n)} (hS : MeasurableSet S) (hfin : perimeter S < ⊤)
    {x : E n} {ν : E n} (hν_unit : ‖ν‖ = 1)
    (hν_normal : measureTheoreticNormal S x = ν)
    -- Conditional: perimeter measure lower density
    (hμ_lower : ∃ (c : ℝ) (R : ℝ), 0 < c ∧ 0 < R ∧
        ∀ r, 0 < r → r < R →
          (perimeterMeasure S (closedBall x r)).toReal ≥ c * r ^ (n - 1))
    -- Conditional: perimeter measure upper density
    (hμ_upper : ∃ (C : ℝ) (R : ℝ), 0 < C ∧ 0 < R ∧
        ∀ r, 0 < r → r < R →
          (perimeterMeasure S (closedBall x r)).toReal ≤ C * r ^ (n - 1))
    -- Conditional: scalar directional measure comparability at x
    (h_scalar : ∃ (R : ℝ), 0 < R ∧
        ∀ r, 0 < r → r < R →
          (∫ y in closedBall x r, inner ℝ ν (measureTheoreticNormal S y) ∂(perimeterMeasure S)) ≥
          (1 / 2 : ℝ) * (perimeterMeasure S (closedBall x r)).toReal)
    (hn : 2 ≤ n) :
    ∃ (c : ℝ) (R : ℝ), 0 < c ∧ 0 < R ∧
      ∀ r, 0 < r → r < R →
        volume (S ∩ ball x r) ≥ ENNReal.ofReal (c * r ^ n) ∧
        volume ((ball x r) \ S) ≥ ENNReal.ofReal (c * r ^ n) := by
  rcases hμ_lower with ⟨c_lower, R_lower, hc_lower, hR_lower, hμ_lower'⟩
  rcases hμ_upper with ⟨C_upper, R_upper, hC_upper, hR_upper, hμ_upper'⟩
  rcases h_scalar with ⟨R_scalar, hR_scalar, h_scalar'⟩

  have h_interior := interior_volume_lower_bound hS hfin hν_unit hν_normal
    c_lower C_upper hc_lower hC_upper
    R_lower R_upper R_scalar hR_lower hR_upper hR_scalar
    hμ_lower' hμ_upper' h_scalar' hn

  rcases h_interior with ⟨c_int, R_int, hc_int_pos, hR_int_pos, h_int⟩

  -- Exterior bound: same η and lower bound, then use ∫_{ℝⁿ} fderiv η ν = 0
  let C_grad := smoothStepDerivBound
  have hC_grad_pos : 0 < C_grad := by
    by_contra h
    have h0 : C_grad = 0 := by linarith [smoothStepDerivBound_nonneg]
    have h1 : ∀ t : ℝ, |deriv smoothStep t| ≤ C_grad := fun t => smoothStep_deriv_bound
    have h2 : ∀ t : ℝ, deriv smoothStep t = 0 := by
      intro t
      have h3 : |deriv smoothStep t| ≤ 0 := by rw [h0] at h1; exact h1 t
      have h4 : 0 ≤ |deriv smoothStep t| := abs_nonneg _
      have h5 : |deriv smoothStep t| = 0 := le_antisymm h3 h4
      exact abs_eq_zero.mp h5
    have h_cd : ContDiff ℝ ∞ smoothStep := by
      exact smoothStep_contDiff
    have h_cont : ContinuousOn smoothStep (Set.Icc (0 : ℝ) 1) :=
      h_cd.continuous.continuousOn
    have h_diff : DifferentiableOn ℝ smoothStep (Set.Ioo (0 : ℝ) 1) :=
      (h_cd.differentiable (by norm_num)).differentiableOn
    have h_mvt : ∃ c ∈ Set.Ioo (0 : ℝ) 1,
        deriv smoothStep c = (smoothStep 1 - smoothStep 0) / (1 - 0) :=
      exists_deriv_eq_slope smoothStep (hab := by norm_num) (hfc := h_cont) (hfd := h_diff)
    rcases h_mvt with ⟨c, _, h_eq⟩
    have h5 : deriv smoothStep c = 0 := h2 c
    rw [h5] at h_eq
    have h6 : (smoothStep 1 - smoothStep 0) / (1 - 0) = 0 := h_eq.symm
    have h7 : smoothStep 1 - smoothStep 0 = 0 := by
      have h10 : (1 : ℝ) - 0 = 1 := by norm_num
      rw [h10] at h6
      simpa using h6
    have h8 : smoothStep 1 = smoothStep 0 := by linarith
    have h9 : smoothStep 0 = 1 := smoothStep_one_of_nonpos (by norm_num)
    have h10 : smoothStep 1 = 0 := smoothStep_zero_of_one_le (by norm_num)
    rw [h9, h10] at h8 <;> norm_num at h8
  let K : ℝ := (1 / 2 : ℝ) * c_lower
  let c_ext : ℝ := K * (1 / 2 : ℝ) ^ (n - 1) * (1 / 3 : ℝ) / C_grad
  have hc_ext_pos : 0 < c_ext := by positivity
  have h_exterior_main : ∃ (c : ℝ) (R : ℝ), 0 < c ∧ 0 < R ∧
      ∀ r, 0 < r → r < R →
        volume ((ball x r) \ S) ≥ ENNReal.ofReal (c * r ^ n) := by
    let R_ext : ℝ := min R_int (min R_lower R_scalar)
    have hR_ext_pos : 0 < R_ext := by positivity
    refine ⟨c_ext, R_ext, hc_ext_pos, hR_ext_pos, ?_⟩
    intro r hr_pos hr_lt
    have hr_lt_int : r < R_int := by
      exact lt_of_lt_of_le hr_lt (min_le_left R_int (min R_lower R_scalar))
    have hr_lt_lower' : r < R_lower := by
      have h : r < min R_lower R_scalar :=
        lt_of_lt_of_le hr_lt (min_le_right R_int (min R_lower R_scalar))
      exact lt_of_lt_of_le h (min_le_left R_lower R_scalar)
    have hr_lt_scalar : r < R_scalar := by
      have h : r < min R_lower R_scalar :=
        lt_of_lt_of_le hr_lt (min_le_right R_int (min R_lower R_scalar))
      exact lt_of_lt_of_le h (min_le_right R_lower R_scalar)

    set r_inner : ℝ := (1 / 2 : ℝ) * r with hr_inner_def
    set L : ℝ := (1 / 3 : ℝ) * r with hL_def
    have hr_inner_pos : 0 < r_inner := by positivity
    have hL_pos : 0 < L := by positivity
    have hr_inner_lt_lower : r_inner < R_lower := by
      rw [hr_inner_def]
      have h : (1 / 2 : ℝ) * r < r := by
        have hpos : 0 < r := hr_pos
        have h6 : (1 / 2 : ℝ) < 1 := by norm_num
        nlinarith
      linarith
    have h_sum_lt_scalar : r_inner + L < R_scalar := by
      rw [hr_inner_def, hL_def]
      have h : (1 / 2 : ℝ) * r + (1 / 3 : ℝ) * r < r := by
        have hpos : 0 < r := hr_pos
        have h6 : (1 / 2 : ℝ) + (1 / 3 : ℝ) < 1 := by norm_num
        nlinarith
      linarith

    let η := radialCutoff x r_inner L
    let μ := perimeterMeasure S
    let g := fun y : E n => inner ℝ ν (measureTheoreticNormal S y)

    have hη_smooth : ContDiff ℝ ∞ η := by
      simpa [η] using radialCutoff_contDiff hr_inner_pos hL_pos
    have hη_supp : HasCompactSupport η := by
      have h1' : ∀ y, y ∉ closedBall x (r_inner + L) → η y = 0 := by
        intro y hy
        have h3 : y ∉ ball x (r_inner + L) := by
          have h4 : dist y x > r_inner + L := by
            simpa [closedBall, mem_closedBall] using hy
          simpa [ball, mem_ball, not_lt] using le_of_lt h4
        exact radialCutoff_zero_of_not_mem_ball hr_inner_pos hL_pos h3
      have h2 : IsCompact (closedBall x (r_inner + L)) := isCompact_closedBall x (r_inner + L)
      exact HasCompactSupport.intro h2 h1'
    have hη_meas : Measurable η := hη_smooth.continuous.measurable

    have h_smoothStep_bound : ∀ t : ℝ, 0 ≤ smoothStep t ∧ smoothStep t ≤ 1 := by
      intro t
      by_cases h1 : t ≤ 0
      · rw [smoothStep_one_of_nonpos h1] <;> norm_num
      · have h1' : 0 < t := by linarith
        by_cases h2 : 1 ≤ t
        · rw [smoothStep_zero_of_one_le h2] <;> norm_num
        · have h3 : 0 < t ∧ t < 1 := ⟨h1', by linarith⟩
          have h4 : smoothStep t ≤ smoothStep 0 := smoothStep_antitone (by linarith)
          have h5 : smoothStep 1 ≤ smoothStep t := smoothStep_antitone (by linarith)
          have h6 : smoothStep 0 = 1 := smoothStep_one_of_nonpos (by norm_num)
          have h7 : smoothStep 1 = 0 := smoothStep_zero_of_one_le (by norm_num)
          constructor <;> linarith

    have hη_nonneg : 0 ≤ η := by
      intro y
      have h : 0 ≤ smoothStep ((dist y x - r_inner) / L) := (h_smoothStep_bound _).1
      exact h
    have hη_le_one : η ≤ 1 := by
      intro y
      have h : smoothStep ((dist y x - r_inner) / L) ≤ 1 := (h_smoothStep_bound _).2
      exact h
    have hη_one : ∀ y ∈ closedBall x r_inner, η y = 1 :=
      fun y hy => radialCutoff_one_of_mem_closedBall hr_inner_pos hL_pos hy

    have h_superlevel : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
        ∃ (d : ℝ), r_inner ≤ d ∧ d < r_inner + L ∧
          {y : E n | η y ≥ t} = closedBall x d := by
      intro t ht
      exact radialCutoff_superlevel_is_closedBall hr_inner_pos hL_pos ht.1 ht.2

    have h_scalar_superlevel : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
        ∫ y in {y | η y ≥ t}, g y ∂μ ≥ (1 / 2 : ℝ) * (μ {y | η y ≥ t}).toReal := by
      intro t ht
      rcases h_superlevel t ht with ⟨d, hd_lower, hd_upper, h_eq⟩
      have hd_pos : 0 < d := by linarith
      have hd_lt_scalar : d < R_scalar := by linarith
      rw [h_eq]; exact h_scalar' d hd_pos hd_lt_scalar

    have hμ_fin : μ Set.univ < ⊤ := by
      have h : μ Set.univ = perimeter S := by
        simpa [μ, perimeterMeasure] using (perimeter_eq_variation S hfin).symm
      rw [h]; exact hfin
    letI : IsFiniteMeasure μ := ⟨hμ_fin⟩

    have h_all := measureTheoreticNormal_withDensity hfin
    have h_norm_int : Integrable (measureTheoreticNormal S) μ := h_all.1
    let l : E n →L[ℝ] ℝ :=
      { toFun := fun z => inner ℝ z ν
        map_add' := by simp [inner_add_left]
        map_smul' := by simp [inner_smul_left] <;> ring }
    have h1 : Integrable (fun y => l (measureTheoreticNormal S y)) μ :=
      l.integrable_comp h_norm_int
    have h2 : g = fun y => inner ℝ (measureTheoreticNormal S y) ν := by
      funext y
      have hgy : g y = inner ℝ ν (measureTheoreticNormal S y) := by rfl
      rw [hgy]
      exact (real_inner_comm ν (measureTheoreticNormal S y)).symm
    have hg_int : Integrable g μ := by
      have h3 : (fun y => l (measureTheoreticNormal S y)) = (fun y => inner ℝ (measureTheoreticNormal S y) ν) := by
        funext y; rfl
      rw [h2]
      rw [←h3]
      exact h1
    have hg_meas : Measurable g := by
      have h1 : Measurable (measureTheoreticNormal S) := measureTheoreticNormal_measurable hfin
      have h2 : Measurable (fun y => inner ℝ ν (measureTheoreticNormal S y)) := by fun_prop
      simpa [g] using h2

    have h_layer : ∫ y, η y * g y ∂μ ≥ (1 / 2 : ℝ) * ∫ y, η y ∂μ :=
      layer_cake_weighted_bound hη_meas hg_int hg_meas hη_nonneg hη_le_one h_scalar_superlevel

    have hη_int : Integrable η μ := hη_smooth.continuous.integrable_of_hasCompactSupport hη_supp
    have h_int_η : ∫ y, η y ∂μ ≥ (μ (closedBall x r_inner)).toReal := by
      have h1 : ∫ y, η y ∂μ ≥ ∫ y in closedBall x r_inner, η y ∂μ :=
        setIntegral_le_integral hη_int (Eventually.of_forall hη_nonneg)
      have h4 : ∀ y ∈ closedBall x r_inner, η y = 1 := hη_one
      have h5 : ∫ y in closedBall x r_inner, η y ∂μ = ∫ y in closedBall x r_inner, (1 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with y hy
        exact h4 y hy
      have h3 : ∫ y in closedBall x r_inner, η y ∂μ = (μ (closedBall x r_inner)).toReal := by
        rw [h5]
        have h4 : ∫ y in closedBall x r_inner, (1 : ℝ) ∂μ = (μ (closedBall x r_inner)).toReal := by
          rw [MeasureTheory.setIntegral_const (1 : ℝ)]
          <;> simp [Measure.real]
        exact h4
      linarith

    have h_lower_bound : ∫ y, η y * g y ∂μ ≥ K * r_inner ^ (n - 1) := by
      calc
        ∫ y, η y * g y ∂μ
          ≥ (1 / 2 : ℝ) * ∫ y, η y ∂μ := h_layer
        _ ≥ (1 / 2 : ℝ) * (μ (closedBall x r_inner)).toReal := by gcongr
        _ ≥ (1 / 2 : ℝ) * (c_lower * r_inner ^ (n - 1)) := by
          exact mul_le_mul_of_nonneg_left (hμ_lower' r_inner hr_inner_pos hr_inner_lt_lower) (by norm_num)
        _ = K * r_inner ^ (n - 1) := by ring

    have h_gg : ∫ y in S, fderiv ℝ η y ν = ∫ y, η y * g y ∂μ :=
      gauss_green_scalar_identity hS hfin hν_unit hη_smooth hη_supp

    have h_total_zero : ∫ y, fderiv ℝ η y ν = 0 :=
      integral_directionalDeriv_univ_eq_zero hη_smooth hη_supp

    have h_split : ∫ y, fderiv ℝ η y ν =
        (∫ y in S, fderiv ℝ η y ν) + (∫ y in Sᶜ, fderiv ℝ η y ν) := by
      have h_int : Integrable (fderiv ℝ η · ν) volume := by
        have h_int' : Integrable (fderiv ℝ η · ν) (volume.restrict Set.univ) :=
          directionalDerivative_integrable (S := Set.univ) hη_smooth hη_supp ν
        simpa using h_int'
      have h_int_on_S : IntegrableOn (fderiv ℝ η · ν) S := h_int.integrableOn
      have h_int_on_Sc : IntegrableOn (fderiv ℝ η · ν) Sᶜ := h_int.integrableOn
      have h_union : ∫ y in (S ∪ Sᶜ : Set (E n)), fderiv ℝ η y ν =
          (∫ y in S, fderiv ℝ η y ν) + (∫ y in Sᶜ, fderiv ℝ η y ν) :=
        MeasureTheory.setIntegral_union disjoint_compl_right hS.compl h_int_on_S h_int_on_Sc
      have h_univ : (S ∪ Sᶜ : Set (E n)) = Set.univ := by simp
      rw [h_univ] at h_union
      simpa using h_union

    have h_exterior_eq : ∫ y in Sᶜ, fderiv ℝ η y ν = -∫ y in S, fderiv ℝ η y ν := by
      have h_eq : (∫ y in S, fderiv ℝ η y ν) + (∫ y in Sᶜ, fderiv ℝ η y ν) = 0 := by
        rw [←h_split, h_total_zero]
      have h_eq' : (∫ y in Sᶜ, fderiv ℝ η y ν) + (∫ y in S, fderiv ℝ η y ν) = 0 := by
        rw [add_comm] at h_eq
        exact h_eq
      exact eq_neg_of_add_eq_zero_left h_eq'

    have h_grad_bound : ∀ y, ‖fderiv ℝ η y‖ ≤ C_grad / L := by
      intro y
      by_cases hy : y = x
      · rw [hy]
        have h_loc : ∀ᶠ (z : E n) in nhds x, η z = 1 := by
          have h5 : ball x r_inner ∈ nhds x := ball_mem_nhds x hr_inner_pos
          filter_upwards [h5] with z hz
          have h6 : z ∈ closedBall x r_inner := by
            have h7 : dist z x < r_inner := by simpa [ball] using hz
            simpa [closedBall, mem_closedBall] using le_of_lt h7
          exact radialCutoff_one_of_mem_closedBall hr_inner_pos hL_pos h6
        have hfd : HasFDerivAt η (0 : E n →L[ℝ] ℝ) x :=
          HasFDerivAt.congr_of_eventuallyEq (hasFDerivAt_const (1 : ℝ) x) h_loc
        have h_pos : 0 ≤ C_grad / L := by
          have h1 : 0 ≤ C_grad := smoothStepDerivBound_nonneg
          have h2 : 0 < L := hL_pos
          exact div_nonneg h1 (by linarith)
        rw [hfd.fderiv]
        <;> simpa using h_pos
      · exact radialCutoff_fderiv_bound hr_inner_pos hL_pos hy

    have h_deriv_zero : ∀ y, y ∉ ball x r → fderiv ℝ η y ν = 0 := by
      intro y hy
      have h_r_lt : r_inner + L < r := by
        rw [hr_inner_def, hL_def]
        have h : (1 / 2 : ℝ) * r + (1 / 3 : ℝ) * r < r := by
          have hpos : 0 < r := hr_pos
          have h : (1 / 2 : ℝ) + (1 / 3 : ℝ) < 1 := by norm_num
          nlinarith
        exact h
      have h_dist : r_inner + L < dist y x := by
        have h1 : r ≤ dist y x := by
          simpa [ball, mem_ball, not_lt] using hy
        calc r_inner + L < r := h_r_lt
          _ ≤ dist y x := h1
      have h4 : ∀ᶠ (z : E n) in nhds y, η z = 0 := by
        have h5 : ball y (dist y x - (r_inner + L)) ∈ nhds y := ball_mem_nhds y (by linarith)
        filter_upwards [h5] with z hz
        have h6 : dist z y < dist y x - (r_inner + L) := by simpa [ball] using hz
        have h7 : dist y x ≤ dist z y + dist z x := by
          have h : dist y x ≤ dist y z + dist z x := dist_triangle y z x
          rw [dist_comm y z] at h
          exact h
        have h7' : dist z x ≥ dist y x - dist z y := by linarith
        have h8 : r_inner + L < dist z x := by linarith
        have h9 : z ∉ ball x (r_inner + L) := by simpa [ball, not_lt] using le_of_lt h8
        exact radialCutoff_zero_of_not_mem_ball hr_inner_pos hL_pos h9
      have h10 : HasFDerivAt η (0 : E n →L[ℝ] ℝ) y :=
        HasFDerivAt.congr_of_eventuallyEq (hasFDerivAt_const (0 : ℝ) y) h4
      have h11 : fderiv ℝ η y = 0 := h10.fderiv
      rw [h11] <;> simp

    have h_ball_meas : MeasurableSet (ball x r) := isOpen_ball.measurableSet
    have hScompl_ball_meas : MeasurableSet (Sᶜ ∩ ball x r) := hS.compl.inter h_ball_meas

    have h_exterior_abs : K * r_inner ^ (n - 1) ≤ |∫ y in Sᶜ, fderiv ℝ η y ν| := by
      rw [h_exterior_eq, abs_neg]
      have h : K * r_inner ^ (n - 1) ≤ ∫ y in S, fderiv ℝ η y ν := by
        rw [h_gg] <;> exact h_lower_bound
      exact h.trans (le_abs_self _)

    have h_upper_bound_ext : |∫ y in Sᶜ, fderiv ℝ η y ν| ≤
        (C_grad / L) * (volume (Sᶜ ∩ ball x r)).toReal := by
      have h1 : |∫ y in Sᶜ, fderiv ℝ η y ν| ≤ ∫ y in Sᶜ, |fderiv ℝ η y ν| :=
        abs_integral_le_integral_abs
      have h2 : ∀ y, |fderiv ℝ η y ν| ≤ C_grad / L := by
        intro y
        have h3 : |fderiv ℝ η y ν| ≤ ‖fderiv ℝ η y‖ * ‖ν‖ :=
          (fderiv ℝ η y).le_opNorm ν
        calc |fderiv ℝ η y ν|
          ≤ ‖fderiv ℝ η y‖ * ‖ν‖ := h3
        _ = ‖fderiv ℝ η y‖ * 1 := by rw [hν_unit]
        _ = ‖fderiv ℝ η y‖ := by ring
        _ ≤ C_grad / L := h_grad_bound y
      have h_eq : ∫ y in Sᶜ, |fderiv ℝ η y ν| = ∫ y in Sᶜ ∩ ball x r, |fderiv ℝ η y ν| := by
        have h_decomp : Sᶜ = (Sᶜ ∩ ball x r) ∪ (Sᶜ \ ball x r) := by
          ext y; simp [and_or_left] <;> tauto
        have h_rhs_simp : ((Sᶜ ∩ ball x r) ∪ (Sᶜ \ ball x r)) ∩ ball x r = Sᶜ ∩ ball x r := by
          ext y; simp [and_or_left] <;> tauto
        rw [h_decomp, h_rhs_simp]
        have h_disj : Disjoint (Sᶜ ∩ ball x r) (Sᶜ \ ball x r) := by
          rw [Set.disjoint_left]
          intro y h1 h2
          exact h2.2 h1.2
        have h_int_ball : IntegrableOn (fun y => |fderiv ℝ η y ν|) (Sᶜ ∩ ball x r) :=
          directionalDerivative_integrable (S := Sᶜ ∩ ball x r) hη_smooth hη_supp ν |>.abs
        have h_int_diff : IntegrableOn (fun y => |fderiv ℝ η y ν|) (Sᶜ \ ball x r) :=
          directionalDerivative_integrable (S := Sᶜ \ ball x r) hη_smooth hη_supp ν |>.abs
        rw [MeasureTheory.setIntegral_union h_disj (hS.compl.diff h_ball_meas) h_int_ball h_int_diff]
        have h_zero : ∫ y in Sᶜ \ ball x r, |fderiv ℝ η y ν| = 0 := by
          apply setIntegral_eq_zero_of_ae_eq_zero
          filter_upwards with y hy
          have h10 : y ∉ ball x r := hy.2
          have h11 : fderiv ℝ η y ν = 0 := h_deriv_zero y h10
          rw [h11] <;> simp
        rw [h_zero, add_zero]
      have h4 : ∫ y in Sᶜ ∩ ball x r, |fderiv ℝ η y ν| ≤ ∫ y in Sᶜ ∩ ball x r, (C_grad / L : ℝ) := by
        have h_int1 : IntegrableOn (fun y => |fderiv ℝ η y ν|) (Sᶜ ∩ ball x r) := by
          exact directionalDerivative_integrable (S := Sᶜ ∩ ball x r) hη_smooth hη_supp ν |>.abs
        have h_int2 : IntegrableOn (fun y : E n => (C_grad / L : ℝ)) (Sᶜ ∩ ball x r) :=
          integrableOn_const
        have h_meas : MeasurableSet (Sᶜ ∩ ball x r) := hS.compl.inter h_ball_meas
        exact setIntegral_mono_on h_int1 h_int2 h_meas fun x _ => h2 x
      have h_combined : ∫ y in Sᶜ, |fderiv ℝ η y ν| ≤ ∫ y in Sᶜ ∩ ball x r, (C_grad / L : ℝ) := by
        rw [h_eq]
        exact h4
      have h5 : ∫ y in Sᶜ ∩ ball x r, (C_grad / L : ℝ) =
          (C_grad / L) * (volume (Sᶜ ∩ ball x r)).toReal := by
        have h : ∫ y in Sᶜ ∩ ball x r, (C_grad / L : ℝ) =
            (volume (Sᶜ ∩ ball x r)).toReal * (C_grad / L) := by
          rw [MeasureTheory.setIntegral_const (C_grad / L : ℝ)]
          <;> simp [Measure.real]
        rw [h]
        <;> ring
      calc |∫ y in Sᶜ, fderiv ℝ η y ν|
        ≤ ∫ y in Sᶜ, |fderiv ℝ η y ν| := h1
      _ ≤ ∫ y in Sᶜ ∩ ball x r, (C_grad / L : ℝ) := h_combined
      _ = (C_grad / L) * (volume (Sᶜ ∩ ball x r)).toReal := h5

    have h_main : (volume ((ball x r) \ S)).toReal ≥ c_ext * r ^ n := by
      have h_set_eq : Sᶜ ∩ ball x r = (ball x r) \ S := by
        ext y; simp <;> tauto
      rw [h_set_eq] at h_upper_bound_ext
      have h6 : (C_grad / L) * (volume ((ball x r) \ S)).toReal ≥ K * r_inner ^ (n - 1) :=
        le_trans h_exterior_abs h_upper_bound_ext
      have h7 : (volume ((ball x r) \ S)).toReal ≥ (K * r_inner ^ (n - 1)) / (C_grad / L) := by
        have h8 : 0 < C_grad / L := by positivity
        have h9 : 0 ≤ (volume ((ball x r) \ S)).toReal := by positivity
        have h10 : (C_grad / L) * (volume ((ball x r) \ S)).toReal ≥ K * r_inner ^ (n - 1) := h6
        have h11 : (volume ((ball x r) \ S)).toReal = ((C_grad / L) * (volume ((ball x r) \ S)).toReal) / (C_grad / L) := by
          field_simp [(ne_of_gt h8)] <;> ring
        rw [h11]
        gcongr
      have h9 : (K * r_inner ^ (n - 1)) / (C_grad / L) = c_ext * r ^ n := by
        have hC_grad_pos' : 0 < C_grad := by
          have h_nonneg : 0 ≤ C_grad := smoothStepDerivBound_nonneg
          by_contra h
          have h0' : C_grad ≤ 0 := by linarith
          have h0 : C_grad = 0 := by linarith [h_nonneg]
          have h1 : c_ext = 0 := by
            have h2 : c_ext = K * (1 / 2 : ℝ) ^ (n - 1) * (1 / 3 : ℝ) / C_grad := by rfl
            rw [h2, h0] <;> simp
          rw [h1] at hc_ext_pos <;> linarith
        have h1 : r_inner = (1 / 2 : ℝ) * r := hr_inner_def
        have h2 : L = (1 / 3 : ℝ) * r := hL_def
        have h3 : c_ext = K * (1 / 2 : ℝ) ^ (n - 1) * (1 / 3 : ℝ) / C_grad := by rfl
        have h4 : C_grad ≠ 0 := hC_grad_pos'.ne'
        have hL_ne : L ≠ 0 := hL_pos.ne'
        have h8 : n ≥ 1 := by linarith
        have h9 : r ^ (n - 1) * r = r ^ n := by
          have h10 : (n - 1) + 1 = n := by omega
          have h11 : r ^ (n - 1) * r = r ^ ((n - 1) + 1) := by rw [pow_succ]
          rw [h11, h10]
        have h10 : (K * r_inner ^ (n - 1)) / (C_grad / L) = K * r_inner ^ (n - 1) * L / C_grad := by
          field_simp [h4, hL_ne] <;> ring
        rw [h10, h1, h2, h3]
        rw [mul_pow]
        have h11 : K * ((1 / 2 : ℝ) ^ (n - 1) * r ^ (n - 1)) * ((1 / 3 : ℝ) * r) / C_grad =
            (K * (1 / 2 : ℝ) ^ (n - 1) * (1 / 3 : ℝ) / C_grad) * r ^ n := by
          have h12 : K * ((1 / 2 : ℝ) ^ (n - 1) * r ^ (n - 1)) * ((1 / 3 : ℝ) * r) =
              K * (1 / 2 : ℝ) ^ (n - 1) * (1 / 3 : ℝ) * (r ^ (n - 1) * r) := by ring
          rw [h12, h9] <;> ring
        exact h11
      rw [h9] at h7
      exact h7

    have h_vol : volume ((ball x r) \ S) ≠ ⊤ := by
      have h : volume ((ball x r) \ S) ≤ volume (ball x r) := measure_mono (by simp)
      have h_ball_lt_top : volume (ball x r) < ⊤ := MeasureTheory.measure_ball_lt_top
      exact h.trans_lt h_ball_lt_top |>.ne
    rw [← ENNReal.ofReal_toReal h_vol]
    exact ENNReal.ofReal_le_ofReal h_main

  rcases h_exterior_main with ⟨c_ext, R_ext, hc_ext_pos, hR_ext_pos, h_ext⟩

  let c := min c_int c_ext
  let R := min R_int R_ext
  have hc_pos : 0 < c := by positivity
  have hR_pos : 0 < R := by positivity

  refine ⟨c, R, hc_pos, hR_pos, ?_⟩
  intro r hr_pos hr_lt

  have hr_lt_int : r < R_int := by linarith [min_le_left R_int R_ext]
  have hr_lt_ext : r < R_ext := by linarith [min_le_right R_int R_ext]

  have h1 := h_int r hr_pos hr_lt_int
  have h2 := h_ext r hr_pos hr_lt_ext

  have hc_int : c ≤ c_int := min_le_left _ _
  have hc_ext : c ≤ c_ext := min_le_right _ _
  have h3 : ENNReal.ofReal (c * r ^ n) ≤ ENNReal.ofReal (c_int * r ^ n) := by
    gcongr
    <;> linarith
  have h4 : ENNReal.ofReal (c * r ^ n) ≤ ENNReal.ofReal (c_ext * r ^ n) := by
    gcongr
    <;> linarith
  exact ⟨le_trans h3 h1, le_trans h4 h2⟩

end Geometry.StructureTheorem
