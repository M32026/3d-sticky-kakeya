import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingJacobian
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CenteredFullFiberCWA
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound

/-!
# Pullback factor and source power bound for the pure WZ2 refinement

Provides the three fields of `PureWZ2FullFiberAssertionDRefinementData` related
to the pullback from the rescaled target space back to the original source:

1. `pullbackFactor` and its positivity/finiteness
2. `target_union_pullback`: volume inequality via affine Jacobian
3. `source_power_le_assertion_rhs`: algebraic power bound using cardinality,
   tube volume, and scale separation

## Main results

- `pullbackFactor`, `pullback_factor_pos`, `pullback_factor_ne_top`
- `target_union_pullback_from_john_image`
- `source_power_full_packing`
- `source_power_generalized`

-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

private lemma realRpowENN_mul_sourcePower
    {delta a b : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta a * Kakeya.realRpowENN delta b =
      Kakeya.realRpowENN delta (a + b) := by
  simp only [Kakeya.realRpowENN]
  have hreal :
      Real.rpow delta a * Real.rpow delta b =
        Real.rpow delta (a + b) :=
    (Real.rpow_add hdelta a b).symm
  have hnonneg : 0 ≤ Real.rpow delta a :=
    Real.rpow_nonneg hdelta.le a
  rw [← ENNReal.ofReal_mul hnonneg, hreal]

private lemma realRpowENN_rpow_sourcePower
    {delta : ℝ} (hdelta : 0 < delta) (a b : ℝ) :
    ENNReal.rpow (Kakeya.realRpowENN delta a) b =
      Kakeya.realRpowENN delta (a * b) := by
  simp only [Kakeya.realRpowENN]
  calc
    ENNReal.rpow (ENNReal.ofReal (Real.rpow delta a)) b =
        ENNReal.ofReal (Real.rpow (Real.rpow delta a) b) :=
      ENNReal.ofReal_rpow_of_pos
        (Real.rpow_pos_of_pos hdelta a)
    _ = ENNReal.ofReal (Real.rpow delta (a * b)) := by
      congr 1
      exact (Real.rpow_mul hdelta.le a b).symm

private lemma assertionD_normalization_eq_sourcePower
    (N V : ENNReal)
    (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hV0 : V ≠ 0) (hVtop : V ≠ ⊤) :
    N * V *
        ENNReal.rpow
          (N * ENNReal.rpow V (1 / 2)) (-(1 / 2)) =
      ENNReal.rpow N (1 / 2) * ENNReal.rpow V (3 / 4) := by
  have hNhalf0 : ENNReal.rpow N (1 / 2) ≠ 0 :=
    (ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hN0) hNtop).ne'
  have hNhalfTop : ENNReal.rpow N (1 / 2) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hNtop
  have hVquarter0 : ENNReal.rpow V (1 / 4) ≠ 0 :=
    (ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hV0) hVtop).ne'
  have hVquarterTop : ENNReal.rpow V (1 / 4) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVtop
  have hN :
      N =
        ENNReal.rpow N (1 / 2) * ENNReal.rpow N (1 / 2) := by
    calc
      N = ENNReal.rpow N 1 := (ENNReal.rpow_one N).symm
      _ = ENNReal.rpow N ((1 / 2) + (1 / 2)) := by norm_num
      _ =
          ENNReal.rpow N (1 / 2) *
            ENNReal.rpow N (1 / 2) :=
        ENNReal.rpow_add (x := N) (1 / 2) (1 / 2)
          hN0 hNtop
  have hV :
      V =
        ENNReal.rpow V (1 / 4) * ENNReal.rpow V (3 / 4) := by
    calc
      V = ENNReal.rpow V 1 := (ENNReal.rpow_one V).symm
      _ = ENNReal.rpow V ((1 / 4) + (3 / 4)) := by norm_num
      _ =
          ENNReal.rpow V (1 / 4) *
            ENNReal.rpow V (3 / 4) :=
        ENNReal.rpow_add (x := V) (1 / 4) (3 / 4)
          hV0 hVtop
  have hVsqrtQuarter :
      ENNReal.rpow (ENNReal.rpow V (1 / 2)) (1 / 2) =
        ENNReal.rpow V (1 / 4) := by
    calc
      ENNReal.rpow (ENNReal.rpow V (1 / 2)) (1 / 2) =
          ENNReal.rpow V ((1 / 2) * (1 / 2)) :=
        (ENNReal.rpow_mul V (1 / 2) (1 / 2)).symm
      _ = ENNReal.rpow V (1 / 4) := by norm_num
  have hdenom :
      ENNReal.rpow
          (N * ENNReal.rpow V (1 / 2)) (1 / 2) =
        ENNReal.rpow N (1 / 2) *
          ENNReal.rpow V (1 / 4) := by
    calc
      ENNReal.rpow
          (N * ENNReal.rpow V (1 / 2)) (1 / 2) =
          ENNReal.rpow N (1 / 2) *
            ENNReal.rpow
              (ENNReal.rpow V (1 / 2)) (1 / 2) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ =
          ENNReal.rpow N (1 / 2) *
            ENNReal.rpow V (1 / 4) := by
        rw [hVsqrtQuarter]
  have hneg :
      ENNReal.rpow
          (N * ENNReal.rpow V (1 / 2)) (-(1 / 2)) =
        (ENNReal.rpow
          (N * ENNReal.rpow V (1 / 2)) (1 / 2))⁻¹ :=
    ENNReal.rpow_neg _ _
  let A := ENNReal.rpow N (1 / 2)
  let B := ENNReal.rpow V (1 / 4)
  let D := ENNReal.rpow V (3 / 4)
  have hAB0 : A * B ≠ 0 := mul_ne_zero hNhalf0 hVquarter0
  have hABtop : A * B ≠ ⊤ :=
    ENNReal.mul_ne_top hNhalfTop hVquarterTop
  have hNV : N * V = (A * A) * (B * D) := by
    rw [hN, hV]
  rw [hneg, hdenom]
  change N * V * (A * B)⁻¹ = A * D
  rw [hNV]
  calc
    (A * A) * (B * D) * (A * B)⁻¹ =
        (A * D) * ((A * B) * (A * B)⁻¹) := by
      ring
    _ = A * D := by
      rw [ENNReal.mul_inv_cancel hAB0 hABtop, mul_one]

/--
The pullback factor is the inverse determinant of the literal WZ
rescaling: `1000000 * rho^2`.
-/
def pullbackFactor (rho : ℝ) : ENNReal :=
  ENNReal.ofReal (1000000 * rho ^ 2)

/-- The pullback factor is positive when `rho > 0`. -/
lemma pullback_factor_pos {rho : ℝ} (hrho : 0 < rho) :
    0 < pullbackFactor rho := by
  have h : 0 < 1000000 * rho ^ 2 := by positivity
  exact ENNReal.ofReal_pos.mpr h

/-- The pullback factor is finite (always, since it's ofReal). -/
lemma pullback_factor_ne_top {rho : ℝ} :
    pullbackFactor rho ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/--
Core pullback volume inequality.

Given an affine equivalence `f` and sets `sourceSet`, `targetSet` with
`targetSet ⊆ f '' sourceSet`, we have
`(1/|det f.linear|) * volume targetSet ≤ volume sourceSet`.

Specialized to the literal WZ rescaling, this gives
`pullbackFactor rho * volume targetSet ≤ volume sourceSet`.
-/
lemma affine_equiv_pullback_volume
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    {sourceSet targetSet : Set Point3}
    (h_subset : targetSet ⊆
        (wz2PaperLiteralUnitRescalingAffineEquiv anchor hrho) '' sourceSet) :
    pullbackFactor rho * volume targetSet ≤ volume sourceSet := by
  let f := wz2PaperLiteralUnitRescalingAffineEquiv anchor hrho
  have h_inj : Function.Injective f := f.injective
  have h_preimage_subset : f ⁻¹' targetSet ⊆ sourceSet := by
    intro x hx
    have h_fx : f x ∈ targetSet := hx
    have h_in_image : f x ∈ f '' sourceSet := h_subset h_fx
    rcases h_in_image with ⟨y, hy, h_eq⟩
    have h_xy : x = y := h_inj h_eq.symm
    rw [h_xy]
    exact hy
  have h_vol_preimage : volume (f ⁻¹' targetSet) ≤ volume sourceSet :=
    measure_mono h_preimage_subset
  have h_surj : Function.Surjective f := f.surjective
  have h_image : f '' (f ⁻¹' targetSet) = targetSet :=
    Set.image_preimage_eq_iff.mpr (fun y _ => h_surj y)
  have h_vol_target : volume targetSet =
      ENNReal.ofReal |LinearMap.det (f.linear : Point3 →ₗ[ℝ] Point3)| *
        volume (f ⁻¹' targetSet) := by
    have h := wz2PaperAffineEquiv_volume_image_eq f (f ⁻¹' targetSet)
    rw [h_image] at h
    exact h
  set det_val : ℝ := |LinearMap.det (f.linear : Point3 →ₗ[ℝ] Point3)| with hdet_val
  have h_det : det_val = 1 / (1000000 * rho ^ 2) := by
    have h := wz2PaperLiteralUnitRescalingAffineEquiv_abs_det anchor hrho
    have h' : det_val = (1 / 100 : ℝ) ^ 3 * (1 / rho) ^ 2 := by
      exact_mod_cast h
    rw [h']
    field_simp [hrho.ne'] <;> ring
  have h_pos : 0 < det_val := by
    rw [h_det] <;> positivity
  have h_mul1 : pullbackFactor rho * ENNReal.ofReal det_val = 1 := by
    have h1 : pullbackFactor rho = ENNReal.ofReal (1000000 * rho ^ 2) := rfl
    rw [h1, h_det]
    have h_pos2 : 0 < 1000000 * rho ^ 2 := by positivity
    rw [←ENNReal.ofReal_mul h_pos2.le]
    have h3 : (1000000 * rho ^ 2) * (1 / (1000000 * rho ^ 2)) = 1 := by
      field_simp [hrho.ne']
    rw [h3] <;> norm_num
  calc
    pullbackFactor rho * volume targetSet
      = pullbackFactor rho *
          (ENNReal.ofReal det_val * volume (f ⁻¹' targetSet)) := by
        rw [h_vol_target]
    _ = (pullbackFactor rho * ENNReal.ofReal det_val) * volume (f ⁻¹' targetSet) := by
        ring
    _ = 1 * volume (f ⁻¹' targetSet) := by rw [h_mul1]
    _ = volume (f ⁻¹' targetSet) := by ring
    _ ≤ volume sourceSet := h_vol_preimage

/-- Pullback volume for the centered literal rescaling used by the complete
strict-fiber frontend. -/
lemma centered_affine_equiv_pullback_volume
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    {sourceSet targetSet : Set Point3}
    (h_subset : targetSet ⊆
        (wz2PaperCenteredLiteralRescalingAffineEquiv
          anchor hrho) '' sourceSet) :
    pullbackFactor rho * volume targetSet ≤ volume sourceSet := by
  let f :=
    wz2PaperCenteredLiteralRescalingAffineEquiv anchor hrho
  have h_preimage_subset : f ⁻¹' targetSet ⊆ sourceSet := by
    intro point hpoint
    rcases h_subset hpoint with ⟨sourcePoint, hsourcePoint, heq⟩
    exact f.injective heq.symm ▸ hsourcePoint
  have h_image : f '' (f ⁻¹' targetSet) = targetSet :=
    Set.image_preimage_eq_iff.mpr fun point _ => f.surjective point
  have hvolume :
      volume targetSet =
        ENNReal.ofReal
            |LinearMap.det
              (f.linear : Point3 →ₗ[ℝ] Point3)| *
          volume (f ⁻¹' targetSet) := by
    have h :=
      wz2PaperAffineEquiv_volume_image_eq
        f (f ⁻¹' targetSet)
    rw [h_image] at h
    exact h
  have hdet :
      |LinearMap.det
          (f.linear : Point3 →ₗ[ℝ] Point3)| =
        1 / (1000000 * rho ^ 2) := by
    change
      |LinearMap.det
          ((wz2PaperLiteralUnitRescalingAffineEquiv
            anchor hrho).linear : Point3 →ₗ[ℝ] Point3)| =
        _
    rw [wz2PaperLiteralUnitRescalingAffineEquiv_abs_det
      anchor hrho]
    field_simp [hrho.ne']
    ring
  have hcancel :
      pullbackFactor rho *
          ENNReal.ofReal
            |LinearMap.det
              (f.linear : Point3 →ₗ[ℝ] Point3)| =
        1 := by
    rw [hdet]
    change
      ENNReal.ofReal (1000000 * rho ^ 2) *
          ENNReal.ofReal (1 / (1000000 * rho ^ 2)) =
        1
    rw [← ENNReal.ofReal_mul (by positivity)]
    have hreal :
        (1000000 * rho ^ 2) *
            (1 / (1000000 * rho ^ 2)) =
          1 := by
      field_simp [hrho.ne']
    rw [hreal]
    norm_num
  calc
    pullbackFactor rho * volume targetSet =
        pullbackFactor rho *
          (ENNReal.ofReal
              |LinearMap.det
                (f.linear : Point3 →ₗ[ℝ] Point3)| *
            volume (f ⁻¹' targetSet)) := by
      rw [hvolume]
    _ =
        (pullbackFactor rho *
            ENNReal.ofReal
              |LinearMap.det
                (f.linear : Point3 →ₗ[ℝ] Point3)|) *
          volume (f ⁻¹' targetSet) := by ring
    _ = volume (f ⁻¹' targetSet) := by rw [hcancel, one_mul]
    _ ≤ volume sourceSet := measure_mono h_preimage_subset

/--
Concrete version using the refinement data's `target_union_subset_john_image`.

If `coordinateChange` is the standard
`wz2PaperJohnToLiteralCoordinateChange`, then
`coordinateChange '' (normalization.map '' shading.union) = literalMap '' shading.union`,
so the subset hypothesis reduces to `target ⊆ literalMap '' source`.
-/
lemma target_union_pullback_from_john_image
    {rho : ℝ} {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (normalization : WZ2PaperAssouadUnitRescalingData anchor)
    {sourceSet targetSet : Set Point3}
    (h_subset : targetSet ⊆
        (wz2PaperJohnToLiteralCoordinateChange hrho normalization) ''
          (normalization.map '' sourceSet)) :
    pullbackFactor rho * volume targetSet ≤ volume sourceSet := by
  have h_image_eq :
      (wz2PaperJohnToLiteralCoordinateChange hrho normalization) ''
        (normalization.map '' sourceSet) =
      (wz2PaperLiteralUnitRescalingAffineEquiv anchor hrho) '' sourceSet := by
    have h := wz2PaperJohnToLiteralCoordinateChange_image hrho normalization sourceSet
    simpa [wz2PaperLiteralUnitRescalingAffineEquiv_apply] using h
  have h_subset' : targetSet ⊆
      (wz2PaperLiteralUnitRescalingAffineEquiv anchor hrho) '' sourceSet := by
    rw [h_image_eq] at h_subset
    exact h_subset
  exact affine_equiv_pullback_volume anchor hrho h_subset'

/-- For `0 < x ≤ 1`, `x^z ≤ x^y` when `y ≤ z` (antitone in exponent). -/
lemma rpow_antitone_of_base_le_one {x y z : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (h : y ≤ z) :
    x ^ z ≤ x ^ y := by
  have hlog : Real.log x ≤ 0 := by
    apply Real.log_nonpos <;> linarith
  have hmul : z * Real.log x ≤ y * Real.log x := by nlinarith
  have h1 : x ^ z = Real.exp (z * Real.log x) := by
    rw [Real.rpow_def_of_pos hx] <;> ring_nf
  have h2 : x ^ y = Real.exp (y * Real.log x) := by
    rw [Real.rpow_def_of_pos hx] <;> ring_nf
  rw [h1, h2]
  exact Real.exp_le_exp.mpr hmul

/-- Power lower bound: `t^(1/2+a+p/2) ≤ t^a * N^(1/2) * V^(3/4)` from `N ≥ t^(-2+p)`, `V ≥ t^2`. -/
lemma power_lower_from_card_vol_generalized
    {t a p : ℝ} (ht : 0 < t) (N V : ENNReal)
    (hN : Kakeya.realRpowENN t (-2 + p) ≤ N)
    (hV : Kakeya.realRpowENN t 2 ≤ V) :
    Kakeya.realRpowENN t (1 / 2 + a + p / 2) ≤
      Kakeya.realRpowENN t a * (ENNReal.rpow N (1 / 2) * ENNReal.rpow V (3 / 4)) := by
  set e : ℝ := 1 / 2 + a + p / 2 with he_def
  have h_mul1 : (-2 + p) * (1 / 2 : ℝ) = (-2 + p) / 2 := by ring
  have h1 : Kakeya.realRpowENN t ((-2 + p) / 2) ≤ ENNReal.rpow N (1 / 2) := by
    have h_eq : Kakeya.realRpowENN t ((-2 + p) / 2) =
        ENNReal.rpow (Kakeya.realRpowENN t (-2 + p)) (1 / 2) := by
      rw [←h_mul1]
      exact
        (realRpowENN_rpow_sourcePower
          ht (-2 + p) (1 / 2)).symm
    rw [h_eq]
    exact ENNReal.rpow_le_rpow hN (by norm_num)
  have h_mul2 : (2 : ℝ) * (3 / 4 : ℝ) = 3 / 2 := by norm_num
  have h2 : Kakeya.realRpowENN t (3 / 2) ≤ ENNReal.rpow V (3 / 4) := by
    have h_eq : Kakeya.realRpowENN t (3 / 2) =
        ENNReal.rpow (Kakeya.realRpowENN t 2) (3 / 4) := by
      rw [←h_mul2]
      exact
        (realRpowENN_rpow_sourcePower
          ht (2 : ℝ) (3 / 4)).symm
    rw [h_eq]
    exact ENNReal.rpow_le_rpow hV (by norm_num)
  have h_exp : e = a + (((-2 + p) / 2) + 3 / 2) := by
    simp [he_def] <;> ring
  rw [h_exp]
  have h_mul0 : Kakeya.realRpowENN t (a + (((-2 + p) / 2) + 3 / 2)) =
      Kakeya.realRpowENN t a * Kakeya.realRpowENN t (((-2 + p) / 2) + 3 / 2) := by
    rw [realRpowENN_mul_sourcePower ht]
  rw [h_mul0]
  have h_mul1' : Kakeya.realRpowENN t (((-2 + p) / 2) + 3 / 2) =
      Kakeya.realRpowENN t ((-2 + p) / 2) * Kakeya.realRpowENN t (3 / 2) := by
    rw [realRpowENN_mul_sourcePower ht]
  rw [h_mul1']
  gcongr

/-- Real cross-scale identity for generalized exponent. -/
lemma cross_scale_real_generalized
    {δ ρ a p : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    (1000000 * ρ ^ 2) * ((δ / ρ) ^ (1 / 2 + a + p / 2)) =
      (1000000 : ℝ) * δ ^ (1 / 2 + a + p / 2) * ρ ^ (3 / 2 - a - p / 2) := by
  set e : ℝ := 1 / 2 + a + p / 2 with he
  have h1 : (δ / ρ) ^ e = δ ^ e / ρ ^ e := Real.div_rpow (by linarith) (by linarith) e
  have h2 : 2 - e = 3 / 2 - a - p / 2 := by simp [he] <;> ring
  have h_pos : 0 < ρ ^ e := Real.rpow_pos_of_pos hρ e
  have h_eq2 : ρ ^ ((2 - e) + e) = ρ ^ (2 - e) * ρ ^ e := Real.rpow_add (by linarith) (2 - e) e
  have h_sum : (2 - e) + e = (2 : ℝ) := by ring
  have h_eq_real : ρ ^ (2 : ℝ) = ρ ^ (2 - e) * ρ ^ e := by
    have h : ρ ^ ((2 - e) + e) = ρ ^ (2 : ℝ) := by rw [h_sum]
    rw [h] at h_eq2
    exact h_eq2
  have h_cast : ρ ^ (2 : ℕ) = ρ ^ (2 : ℝ) := by simp
  have h_eq : ρ ^ 2 = ρ ^ (2 - e) * ρ ^ e := by
    rw [h_cast]; exact h_eq_real
  have hρdiv : ρ ^ 2 / ρ ^ e = ρ ^ (2 - e) := by
    rw [div_eq_iff h_pos.ne']; exact h_eq
  calc
    (1000000 * ρ ^ 2) * ((δ / ρ) ^ e)
      = (1000000 * ρ ^ 2) * (δ ^ e / ρ ^ e) := by rw [h1]
    _ = (1000000 : ℝ) * δ ^ e * (ρ ^ 2 / ρ ^ e) := by ring
    _ = (1000000 : ℝ) * δ ^ e * ρ ^ (2 - e) := by rw [hρdiv]
    _ = (1000000 : ℝ) * δ ^ e * ρ ^ (3 / 2 - a - p / 2) := by rw [h2]

/-- ENNReal cross-scale identity for generalized exponent. -/
lemma cross_scale_ennreal_generalized
    {δ ρ a p : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    ENNReal.ofReal (1000000 * ρ ^ 2) * Kakeya.realRpowENN (δ / ρ) (1 / 2 + a + p / 2) =
      ENNReal.ofReal (1000000 : ℝ) * Kakeya.realRpowENN δ (1 / 2 + a + p / 2) *
        ENNReal.rpow (ENNReal.ofReal ρ) (3 / 2 - a - p / 2) := by
  set e : ℝ := 1 / 2 + a + p / 2 with he
  have h_real := cross_scale_real_generalized hδ hρ (a := a) (p := p)
  have h_left : ENNReal.ofReal (1000000 * ρ ^ 2) * Kakeya.realRpowENN (δ / ρ) e =
      ENNReal.ofReal ((1000000 * ρ ^ 2) * ((δ / ρ) ^ e)) := by
    have h : ENNReal.ofReal (1000000 * ρ ^ 2) * ENNReal.ofReal ((δ / ρ) ^ e) =
        ENNReal.ofReal ((1000000 * ρ ^ 2) * ((δ / ρ) ^ e)) := by
      rw [←ENNReal.ofReal_mul (by positivity)]
    simpa [Kakeya.realRpowENN] using h
  have hρpow : ENNReal.rpow (ENNReal.ofReal ρ) (3 / 2 - a - p / 2) =
      ENNReal.ofReal (ρ ^ (3 / 2 - a - p / 2)) := by
    simp [ENNReal.ofReal_rpow_of_pos hρ]
  have h_right : ENNReal.ofReal (1000000 : ℝ) * Kakeya.realRpowENN δ e *
        ENNReal.rpow (ENNReal.ofReal ρ) (3 / 2 - a - p / 2) =
      ENNReal.ofReal ((1000000 : ℝ) * δ ^ e * ρ ^ (3 / 2 - a - p / 2)) := by
    rw [hρpow]
    have h : ENNReal.ofReal (1000000 : ℝ) * ENNReal.ofReal (δ ^ e) * ENNReal.ofReal (ρ ^ (3 / 2 - a - p / 2)) =
        ENNReal.ofReal ((1000000 : ℝ) * δ ^ e * ρ ^ (3 / 2 - a - p / 2)) := by
      rw [←ENNReal.ofReal_mul (by positivity), ←ENNReal.ofReal_mul (by positivity)]
    simpa [Kakeya.realRpowENN] using h
  rw [h_left, h_right]
  exact congr_arg ENNReal.ofReal h_real

/-- Generalized source power with packing exponent p.

Assumes `N ≥ t^(-2+p)` and `V ≥ t^2`. Requires `b - a - p/2 > 0`,
`3/2 - a - p/2 > 0`, scale separation `ρ ≥ δ^c` with
`c < (b-a-p/2)/(3/2-a-p/2)`, and constant absorption
`δ^d ≤ 10^6*κ` where `d = (b-a-p/2) - c*(3/2-a-p/2) > 0`. -/
lemma source_power_generalized
    {δ ρ a b κ p : ℝ}
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) (hρ : 0 < ρ)
    (ha_pos : 0 < a) (ha_lt_b : a < b)
    (hb_pos : 0 < b) (hb_lt_three_halves : b < 3 / 2)
    (hp_nonneg : 0 ≤ p)
    (h_exp_pos : 0 < b - a - p / 2)
    (h_denom_pos : 0 < 3 / 2 - a - p / 2)
    (hκ : 0 < κ)
    (N V : ENNReal)
    (hN : Kakeya.realRpowENN (δ / ρ) (-2 + p) ≤ N)
    (hV : Kakeya.realRpowENN (δ / ρ) 2 ≤ V)
    (hN0 : N ≠ 0) (hNtop : N ≠ ⊤) (hV0 : V ≠ 0) (hVtop : V ≠ ⊤)
    (c : ℝ)
    (h_c_nonneg : 0 ≤ c)
    (h_c_bound : c < (b - a - p / 2) / (3 / 2 - a - p / 2))
    (h_scale_real : ρ ≥ δ ^ c)
    (h_absorb : Kakeya.realRpowENN δ ((b - a - p / 2) - c * (3 / 2 - a - p / 2)) ≤
        ENNReal.ofReal (1000000 * κ)) :
    Kakeya.realRpowENN δ (1 / 2 + b) ≤
      ENNReal.ofReal (1000000 * ρ ^ 2) *
        (ENNReal.ofReal κ * Kakeya.realRpowENN (δ / ρ) a *
          N * V * ENNReal.rpow (N * ENNReal.rpow V (1 / 2)) (-(1 / 2 : ℝ))) := by
  set t : ℝ := δ / ρ with ht_def
  have ht_pos : 0 < t := by positivity
  set e : ℝ := 1 / 2 + a + p / 2 with he_def
  set d : ℝ := (b - a - p / 2) - c * (3 / 2 - a - p / 2) with hd_def
  have hd_pos : 0 < d := by
    rw [hd_def]
    have h2 : c * (3 / 2 - a - p / 2) < b - a - p / 2 := by
      have h21 : c * (3 / 2 - a - p / 2) < ((b - a - p / 2) / (3 / 2 - a - p / 2)) * (3 / 2 - a - p / 2) := by
        exact mul_lt_mul_of_pos_right h_c_bound h_denom_pos
      have h22 : ((b - a - p / 2) / (3 / 2 - a - p / 2)) * (3 / 2 - a - p / 2) = b - a - p / 2 := by
        rw [div_mul_cancel₀ (b - a - p / 2) h_denom_pos.ne']
      rw [h22] at h21
      exact h21
    linarith
  have h_tail :=
    assertionD_normalization_eq_sourcePower
      N V hN0 hNtop hV0 hVtop
  have h_power := power_lower_from_card_vol_generalized (t := t) (a := a) (p := p) ht_pos N V hN hV
  have h_cross := cross_scale_ennreal_generalized hδ hρ (a := a) (p := p)
  have hδc_pos : 0 ≤ δ ^ c := by positivity
  have h_scale : δ ^ c ≤ ρ := h_scale_real
  have h3 : ρ ^ (3 / 2 - a - p / 2) ≥ (δ ^ c) ^ (3 / 2 - a - p / 2) := by
    exact Real.rpow_le_rpow hδc_pos h_scale (by linarith)
  have h4 : (δ ^ c) ^ (3 / 2 - a - p / 2) = δ ^ (c * (3 / 2 - a - p / 2)) := by
    rw [←Real.rpow_mul (by linarith)] <;> ring
  have hρpow_real : ρ ^ (3 / 2 - a - p / 2) ≥ δ ^ (c * (3 / 2 - a - p / 2)) := by
    rw [h4] at h3; exact h3
  have hρpow_enn : ENNReal.rpow (ENNReal.ofReal ρ) (3 / 2 - a - p / 2) ≥
      Kakeya.realRpowENN δ (c * (3 / 2 - a - p / 2)) := by
    have h5 : ENNReal.rpow (ENNReal.ofReal ρ) (3 / 2 - a - p / 2) =
        ENNReal.ofReal (ρ ^ (3 / 2 - a - p / 2)) := by
      simp [ENNReal.ofReal_rpow_of_pos hρ]
    have h6 : Kakeya.realRpowENN δ (c * (3 / 2 - a - p / 2)) =
        ENNReal.ofReal (δ ^ (c * (3 / 2 - a - p / 2))) := by
      simp [Kakeya.realRpowENN]
    rw [h5, h6]
    have h_cast : ENNReal.ofReal (δ ^ (c * (3 / 2 - a - p / 2))) ≤ ENNReal.ofReal (ρ ^ (3 / 2 - a - p / 2)) := by
      exact ENNReal.ofReal_le_ofReal hρpow_real
    exact h_cast
  have h_sum_exp : (1 / 2 + b : ℝ) = e + c * (3 / 2 - a - p / 2) + d := by
    simp [he_def, hd_def] <;> ring
  have h_final : Kakeya.realRpowENN δ (1 / 2 + b) ≤
      ENNReal.ofReal (1000000 : ℝ) * Kakeya.realRpowENN δ e *
        ENNReal.rpow (ENNReal.ofReal ρ) (3 / 2 - a - p / 2) * ENNReal.ofReal κ := by
    have h_split : Kakeya.realRpowENN δ (1 / 2 + b) =
        Kakeya.realRpowENN δ e * Kakeya.realRpowENN δ (c * (3 / 2 - a - p / 2)) *
        Kakeya.realRpowENN δ d := by
      rw [h_sum_exp, realRpowENN_mul_sourcePower hδ,
        realRpowENN_mul_sourcePower hδ] <;> ring
    rw [h_split]
    have h7 : Kakeya.realRpowENN δ (c * (3 / 2 - a - p / 2)) ≤
        ENNReal.rpow (ENNReal.ofReal ρ) (3 / 2 - a - p / 2) := hρpow_enn
    have h8 : Kakeya.realRpowENN δ d ≤ ENNReal.ofReal (1000000 * κ) := h_absorb
    calc
      Kakeya.realRpowENN δ e * Kakeya.realRpowENN δ (c * (3 / 2 - a - p / 2)) * Kakeya.realRpowENN δ d
        ≤ Kakeya.realRpowENN δ e * ENNReal.rpow (ENNReal.ofReal ρ) (3 / 2 - a - p / 2) *
            ENNReal.ofReal (1000000 * κ) := by gcongr
      _ = ENNReal.ofReal (1000000 : ℝ) * Kakeya.realRpowENN δ e *
            ENNReal.rpow (ENNReal.ofReal ρ) (3 / 2 - a - p / 2) * ENNReal.ofReal κ := by
          have h9 : ENNReal.ofReal (1000000 * κ) =
              ENNReal.ofReal (1000000 : ℝ) * ENNReal.ofReal κ := by
            rw [←ENNReal.ofReal_mul (by positivity)] <;> ring
          rw [h9] <;> ring
  have h_main : ENNReal.ofReal (1000000 * ρ ^ 2) *
        (ENNReal.ofReal κ * Kakeya.realRpowENN t a *
          (ENNReal.rpow N (1 / 2) * ENNReal.rpow V (3 / 4))) ≥
      Kakeya.realRpowENN δ (1 / 2 + b) := by
    calc
      ENNReal.ofReal (1000000 * ρ ^ 2) *
          (ENNReal.ofReal κ * Kakeya.realRpowENN t a *
            (ENNReal.rpow N (1 / 2) * ENNReal.rpow V (3 / 4)))
        ≥ ENNReal.ofReal (1000000 * ρ ^ 2) *
            (ENNReal.ofReal κ * Kakeya.realRpowENN t e) := by
          have h9 : ENNReal.ofReal κ * Kakeya.realRpowENN t e ≤
              ENNReal.ofReal κ * (Kakeya.realRpowENN t a *
                (ENNReal.rpow N (1 / 2) * ENNReal.rpow V (3 / 4))) := by
            exact mul_le_mul_right h_power _
          have h_comm : ENNReal.ofReal κ * (Kakeya.realRpowENN t a *
                (ENNReal.rpow N (1 / 2) * ENNReal.rpow V (3 / 4))) =
              ENNReal.ofReal κ * Kakeya.realRpowENN t a *
                (ENNReal.rpow N (1 / 2) * ENNReal.rpow V (3 / 4)) := by ring
          rw [h_comm] at h9
          exact mul_le_mul_right h9 _
      _ = ENNReal.ofReal κ *
            (ENNReal.ofReal (1000000 * ρ ^ 2) * Kakeya.realRpowENN t e) := by ring
      _ = ENNReal.ofReal κ *
            (ENNReal.ofReal (1000000 : ℝ) * Kakeya.realRpowENN δ e *
              ENNReal.rpow (ENNReal.ofReal ρ) (3 / 2 - a - p / 2)) := by
            rw [h_cross] <;> ring
      _ = ENNReal.ofReal (1000000 : ℝ) * Kakeya.realRpowENN δ e *
            ENNReal.rpow (ENNReal.ofReal ρ) (3 / 2 - a - p / 2) * ENNReal.ofReal κ := by ring
      _ ≥ Kakeya.realRpowENN δ (1 / 2 + b) := h_final
  have h_inner : (ENNReal.ofReal κ * Kakeya.realRpowENN t a *
        N * V * ENNReal.rpow (N * ENNReal.rpow V (1 / 2)) (-(1 / 2 : ℝ))) =
      ENNReal.ofReal κ * Kakeya.realRpowENN t a *
        (ENNReal.rpow N (1 / 2) * ENNReal.rpow V (3 / 4)) := by
    have h_assoc : (ENNReal.ofReal κ * Kakeya.realRpowENN t a *
          N * V * ENNReal.rpow (N * ENNReal.rpow V (1 / 2)) (-(1 / 2 : ℝ))) =
        ENNReal.ofReal κ * Kakeya.realRpowENN t a *
          (N * V * ENNReal.rpow (N * ENNReal.rpow V (1 / 2)) (-(1 / 2 : ℝ))) := by ring
    rw [h_assoc, h_tail] <;> ring
  rw [h_inner]
  exact h_main

/-- Source power with full packing (`N ≥ t^(-2)`). Covers ALL `a < b` when `b < 3/2`. -/
lemma source_power_full_packing
    {δ ρ a b κ : ℝ}
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) (hρ : 0 < ρ)
    (ha_pos : 0 < a) (ha_lt_b : a < b)
    (hb_pos : 0 < b) (hb_lt_three_halves : b < 3 / 2)
    (hκ : 0 < κ)
    (N V : ENNReal)
    (hN : Kakeya.realRpowENN (δ / ρ) (-2) ≤ N)
    (hV : Kakeya.realRpowENN (δ / ρ) 2 ≤ V)
    (hN0 : N ≠ 0) (hNtop : N ≠ ⊤) (hV0 : V ≠ 0) (hVtop : V ≠ ⊤)
    (c : ℝ)
    (h_c_nonneg : 0 ≤ c)
    (h_c_bound : c < (b - a) / (3 / 2 - a))
    (h_scale_real : ρ ≥ δ ^ c)
    (h_absorb : Kakeya.realRpowENN δ ((b - a) - c * (3 / 2 - a)) ≤
        ENNReal.ofReal (1000000 * κ)) :
    Kakeya.realRpowENN δ (1 / 2 + b) ≤
      ENNReal.ofReal (1000000 * ρ ^ 2) *
        (ENNReal.ofReal κ * Kakeya.realRpowENN (δ / ρ) a *
          N * V * ENNReal.rpow (N * ENNReal.rpow V (1 / 2)) (-(1 / 2 : ℝ))) := by
  have h_exp_pos : 0 < b - a := by linarith
  have h_denom_pos : 0 < 3 / 2 - a := by linarith
  have h_exp_pos' : 0 < b - a - (0 : ℝ) / 2 := by simpa using h_exp_pos
  have h_denom_pos' : 0 < 3 / 2 - a - (0 : ℝ) / 2 := by simpa using h_denom_pos
  have hN' : Kakeya.realRpowENN (δ / ρ) (-2 + (0 : ℝ)) ≤ N := by simpa using hN
  have h_absorb' : Kakeya.realRpowENN δ ((b - a - (0 : ℝ) / 2) - c * (3 / 2 - a - (0 : ℝ) / 2)) ≤
      ENNReal.ofReal (1000000 * κ) := by simpa using h_absorb
  have h_c_bound' : c < (b - a - (0 : ℝ) / 2) / (3 / 2 - a - (0 : ℝ) / 2) := by simpa using h_c_bound
  exact source_power_generalized (p := 0)
    hδ hδ_one hρ ha_pos ha_lt_b hb_pos hb_lt_three_halves
    (by norm_num)
    h_exp_pos' h_denom_pos'
    hκ N V hN' hV
    hN0 hNtop hV0 hVtop
    c h_c_nonneg h_c_bound'
    h_scale_real h_absorb'

end Kakeya.Assouad

end
