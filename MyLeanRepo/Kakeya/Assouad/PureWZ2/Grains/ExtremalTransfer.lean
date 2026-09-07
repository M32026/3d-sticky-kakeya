import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WeakenLoss
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CroppedExtremal
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLinePackingCardinality
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Transfer extremal/CWA properties to a pruned subshading

When weak planiness + cap+cell produces a pruned subshading retaining
`1/K` of the original mass, we transfer the extremal configuration to
the new shading by starting with a stronger extremal at `loss1 < loss2`.

## Mass loss budget

The pruning pipeline has two stages:
1. Weak planiness: retains ≥ 1/8 of mass.
2. Cap+cell separation: retains ≥ 1/(16 · capCount) of the remaining mass.

Total retention: `1 / (8 · 16 · capCount) = 1 / (128 · capCount)`.
Set `K = 128 · capCount` (or any larger constant) in the general lemma.

## Slack condition

Given `K`, we need `K · δ^loss2 ≤ δ^loss1`, equivalently
`(1/δ)^(loss2 - loss1) ≥ K`. For any fixed `K` and `loss2 > 0`,
choose `loss1 > 0` small enough and `δ` small enough.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/-- Generalized transfer: mass retention factor `K⁻¹`.

The slack condition `K * δ^loss2 ≤ δ^loss1` ensures the dense
condition survives the mass loss. For the weak planiness + cap+cell
pipeline, set `K = 128 * capCount` (or larger). -/
lemma transfer_cropped_extremal_to_subshading
    {sigma loss1 loss2 delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading1 shading2 : WZ1PaperTubeShading family}
    (K : ENNReal)
    (hK_pos : 0 < K)
    (hK_ne_top : K ≠ ⊤)
    (extremal1 : WZ2PaperCroppedIsExtremal sigma loss1 family shading1)
    (hsub : PaperIsSubshading shading2 shading1)
    (hmass : K⁻¹ * shading1.mass ≤ shading2.mass)
    (hcubical : WZ1PaperIsCubicalShading shading2)
    (hloss_le : loss1 ≤ loss2)
    (hslack : K * Kakeya.realRpowENN delta loss2 ≤ Kakeya.realRpowENN delta loss1)
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (hloss2_pos : 0 < loss2) :
    WZ2PaperCroppedIsExtremal sigma loss2 family shading2 := by
  have hC1_le_C2 : Kakeya.realRpowENN delta (-loss1) ≤ Kakeya.realRpowENN delta (-loss2) := by
    simp only [Kakeya.realRpowENN]
    have h_exp : -loss2 ≤ -loss1 := by linarith
    have h : Real.rpow delta (-loss1) ≤ Real.rpow delta (-loss2) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one h_exp
    exact ENNReal.ofReal_le_ofReal h
  have hC2_finite : WZ2PaperFiniteErrorConstant (Kakeya.realRpowENN delta (-loss2)) := by
    have h8 : Real.rpow delta (-loss2) ≥ 1 := by
      have h10 : Real.rpow delta 0 ≤ Real.rpow delta (-loss2) :=
        Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one (show -loss2 ≤ 0 by linarith)
      simpa using h10
    have h7 : (1 : ENNReal) ≤ Kakeya.realRpowENN delta (-loss2) := by
      have h71 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
      rw [h71]
      exact ENNReal.ofReal_le_ofReal h8
    have h9 : Kakeya.realRpowENN delta (-loss2) ≠ ⊤ := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
    exact ⟨h7, h9⟩
  have h_union_sub : shading2.union ⊆ shading1.union := by
    intro p hp
    rcases hp with ⟨i, hi⟩
    exact ⟨i, hsub i hi⟩
  have h_vol2 : volume shading2.union ≤ volume shading1.union :=
    measure_mono h_union_sub
  have h_vol3 : volume shading1.union ≤ Kakeya.realRpowENN delta (sigma - loss1) :=
    extremal1.volume_upper
  have h_vol4 : Kakeya.realRpowENN delta (sigma - loss1) ≤ Kakeya.realRpowENN delta (sigma - loss2) := by
    simp only [Kakeya.realRpowENN]
    have h_exp : sigma - loss2 ≤ sigma - loss1 := by linarith
    have h : Real.rpow delta (sigma - loss1) ≤ Real.rpow delta (sigma - loss2) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one h_exp
    exact ENNReal.ofReal_le_ofReal h
  have hK_inv_mul : K⁻¹ * K = 1 :=
    ENNReal.inv_mul_cancel hK_pos.ne' hK_ne_top
  have h_dense2 : shading2.IsLambdaDense (Kakeya.realRpowENN delta loss2) := by
    have h1 : Kakeya.realRpowENN delta loss1 * (wz1PaperBodyFamily family).mass ≤ shading1.mass :=
      extremal1.dense
    have h2 : K⁻¹ * Kakeya.realRpowENN delta loss1 * (wz1PaperBodyFamily family).mass ≤ shading2.mass := by
      calc
        K⁻¹ * Kakeya.realRpowENN delta loss1 * (wz1PaperBodyFamily family).mass
          = K⁻¹ * (Kakeya.realRpowENN delta loss1 * (wz1PaperBodyFamily family).mass) := by ring
        _ ≤ K⁻¹ * shading1.mass := by gcongr
        _ ≤ shading2.mass := hmass
    have h3 : Kakeya.realRpowENN delta loss2 ≤ K⁻¹ * Kakeya.realRpowENN delta loss1 := by
      have h4 : K * Kakeya.realRpowENN delta loss2 ≤ Kakeya.realRpowENN delta loss1 := hslack
      have h5 : K⁻¹ * (K * Kakeya.realRpowENN delta loss2) = Kakeya.realRpowENN delta loss2 := by
        calc
          K⁻¹ * (K * Kakeya.realRpowENN delta loss2)
            = (K⁻¹ * K) * Kakeya.realRpowENN delta loss2 := by rw [mul_assoc]
          _ = (1 : ENNReal) * Kakeya.realRpowENN delta loss2 := by rw [hK_inv_mul]
          _ = Kakeya.realRpowENN delta loss2 := by simp
      have h7 : K⁻¹ * (K * Kakeya.realRpowENN delta loss2) ≤
          K⁻¹ * Kakeya.realRpowENN delta loss1 := by gcongr
      rw [h5] at h7
      exact h7
    have h3mass : Kakeya.realRpowENN delta loss2 * (wz1PaperBodyFamily family).mass ≤
        K⁻¹ * Kakeya.realRpowENN delta loss1 * (wz1PaperBodyFamily family).mass := by
      gcongr
    exact le_trans h3mass h2
  exact
    { delta_pos := extremal1.delta_pos
      delta_le_one := extremal1.delta_le_one
      nonempty := extremal1.nonempty
      cwa_nearby_scales := weaken_cwa_nearby_scales extremal1.cwa_nearby_scales hC1_le_C2 hC2_finite
      cubical := hcubical
      dense := h_dense2
      volume_upper := le_trans (le_trans h_vol2 h_vol3) h_vol4 }

/-- The slack condition `K * δ^loss2 ≤ δ^loss1` is achievable by choosing δ small.

If `0 < loss1 < loss2`, `K ≥ 1`, and `δ ≤ K_real^(-1/(loss2-loss1))`,
then `K * δ^loss2 ≤ δ^loss1`. -/
lemma extremal_transfer_slack_achievable
    {K : ENNReal} {delta loss1 loss2 : ℝ}
    (hK_ne_top : K ≠ ⊤)
    (hK_one : (1 : ENNReal) ≤ K)
    (hloss1_pos : 0 < loss1)
    (hloss1_lt_loss2 : loss1 < loss2)
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (hdelta_small : delta ≤ (ENNReal.toReal K)^(-1 / (loss2 - loss1))) :
    K * Kakeya.realRpowENN delta loss2 ≤ Kakeya.realRpowENN delta loss1 := by
  let K_real : ℝ := ENNReal.toReal K
  have hK_real_one : 1 ≤ K_real := by
    have h1 : (1 : ENNReal) ≤ K := hK_one
    have h2 : ENNReal.toReal (1 : ENNReal) ≤ ENNReal.toReal K := by
      exact ENNReal.toReal_mono hK_ne_top h1
    simpa using h2
  have hK_real_pos : 0 < K_real := by linarith
  set gap : ℝ := loss2 - loss1 with hgap_def
  have hgap_pos : 0 < gap := by linarith
  set base : ℝ := Real.rpow K_real (-1 / gap) with hbase_def
  have hbase_pos : 0 < base := Real.rpow_pos_of_pos hK_real_pos _
  have h1 : Real.rpow delta gap ≤ Real.rpow base gap :=
    Real.rpow_le_rpow (by linarith) hdelta_small (by linarith)
  have h4 : Real.rpow base gap = K_real⁻¹ := by
    have h51 : base = Real.rpow K_real (-1 / gap) := by simp [hbase_def]
    have h5 : Real.rpow base gap = Real.rpow K_real ((-1 / gap) * gap) := by
      rw [h51]
      exact (Real.rpow_mul hK_real_pos.le (-1 / gap) gap).symm
    rw [h5]
    have h6 : (-1 / gap) * gap = -1 := by
      field_simp [hgap_pos.ne'] <;> ring
    rw [h6]
    have h7 : Real.rpow K_real (-1 : ℝ) = K_real⁻¹ := by
      simpa [Real.rpow_neg hK_real_pos.le] using rfl
    exact h7
  have h1' : Real.rpow delta gap ≤ K_real⁻¹ := by
    rw [h4] at h1
    exact h1
  have h7 : Real.rpow delta loss2 = Real.rpow delta loss1 * Real.rpow delta gap := by
    have hsum : loss1 + gap = loss2 := by
      simp [hgap_def] <;> ring
    have h : Real.rpow delta (loss1 + gap) = Real.rpow delta loss1 * Real.rpow delta gap :=
      Real.rpow_add hdelta_pos loss1 gap
    rw [hsum] at h
    exact h
  have h8 : K_real * Real.rpow delta gap ≤ 1 := by
    calc K_real * Real.rpow delta gap
      ≤ K_real * K_real⁻¹ := mul_le_mul_of_nonneg_left h1' hK_real_pos.le
    _ = 1 := by
      field_simp [hK_real_pos.ne'] <;> ring
  have h9 : 0 ≤ Real.rpow delta loss1 := Real.rpow_nonneg hdelta_pos.le _
  have h_main : K_real * Real.rpow delta loss2 ≤ Real.rpow delta loss1 := by
    rw [h7]
    have h10 : K_real * (Real.rpow delta loss1 * Real.rpow delta gap) =
        Real.rpow delta loss1 * (K_real * Real.rpow delta gap) := by ring
    rw [h10]
    have h11 : Real.rpow delta loss1 * (K_real * Real.rpow delta gap) ≤ Real.rpow delta loss1 * 1 :=
      mul_le_mul_of_nonneg_left h8 h9
    have h12 : Real.rpow delta loss1 * 1 = Real.rpow delta loss1 := by ring
    rw [h12] at h11
    exact h11
  have hK_coe : (K : ENNReal) = ENNReal.ofReal K_real := by
    rw [ENNReal.ofReal_toReal] <;> exact hK_ne_top
  have h_goal : ENNReal.ofReal K_real * Kakeya.realRpowENN delta loss2 ≤
      Kakeya.realRpowENN delta loss1 := by
    simp only [Kakeya.realRpowENN]
    have h11 : ENNReal.ofReal K_real * ENNReal.ofReal (Real.rpow delta loss2) =
        ENNReal.ofReal (K_real * Real.rpow delta loss2) := by
      rw [← ENNReal.ofReal_mul hK_real_pos.le]
    rw [h11]
    exact ENNReal.ofReal_le_ofReal h_main
  rw [hK_coe]
  exact h_goal

/-- **Polylog retention with constant factor absorbs ε gap in extremality**.

For any `ε = loss2 - loss1 > 0` and any `C > 0`, there exists `δ₀ > 0` such that
for all `δ ≤ δ₀`: if `shading1` is extremal at `loss1` and `shading2` is a
subshading with mass retention `≥ 1 / (C · log(1/δ))`, then `shading2` is
extremal at `loss2`.

This relaxes the constant `1/8` retention requirement to polylog retention
with arbitrary constant overhead (e.g., `1/(16·log)` from combined stages).
The key real-analysis fact is `log x = o(x^ε)` as `x → ∞`, so
`C · log(1/δ) · δ^ε ≤ 1` for sufficiently small `δ`. -/
lemma transfer_extremal_polylog_retention
    {sigma loss1 loss2 : ℝ}
    (C : ℝ)
    (hC_pos : 0 < C)
    (hε : 0 < loss2 - loss1)
    (hloss1_pos : 0 < loss1)
    (hloss2_pos : 0 < loss2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ δ₀ →
      ∀ {family : Kakeya.Streamlined.TubeFamily delta}
        {shading1 shading2 : WZ1PaperTubeShading family},
        WZ2PaperCroppedIsExtremal sigma loss1 family shading1 →
        PaperIsSubshading shading2 shading1 →
        shading1.mass / ENNReal.ofReal (C * Real.log (1 / delta)) ≤ shading2.mass →
        WZ1PaperIsCubicalShading shading2 →
        WZ2PaperCroppedIsExtremal sigma loss2 family shading2 := by
  -- Step 1: real analysis — C · log x ≤ x^ε for large x (since log x = o(x^ε))
  have h_main : ∃ X : ℝ, 0 < X ∧ ∀ x, x ≥ X → C * Real.log x ≤ x ^ (loss2 - loss1) := by
    have h_littleO := isLittleO_log_rpow_atTop hε
    have h_invC_pos : 0 < 1 / C := by positivity
    have h_bigO : Asymptotics.IsBigOWith (1 / C) Filter.atTop Real.log
        (fun x : ℝ => x ^ (loss2 - loss1)) :=
      (Asymptotics.isLittleO_iff_forall_isBigOWith.mp h_littleO) h_invC_pos
    rcases Filter.mem_atTop_sets.mp h_bigO.bound with ⟨X, hX⟩
    let X' := max X 1
    have hX'_pos : 0 < X' := by positivity
    have hX'_one : 1 ≤ X' := le_max_right _ _
    refine ⟨X', hX'_pos, ?_⟩
    intro x hx
    have h4 : x ≥ X := by have h5 : X ≤ X' := le_max_left _ _; linarith
    have h6 : ‖Real.log x‖ ≤ (1 / C) * ‖x ^ (loss2 - loss1)‖ := hX x h4
    have h7 : 1 ≤ x := by linarith
    have h8 : 0 ≤ Real.log x := Real.log_nonneg h7
    have h9 : 0 < x ^ (loss2 - loss1) := Real.rpow_pos_of_pos (by linarith) _
    have h10 : ‖Real.log x‖ = Real.log x := by
      rw [Real.norm_eq_abs, abs_of_nonneg h8]
    have h11 : ‖x ^ (loss2 - loss1)‖ = x ^ (loss2 - loss1) := by
      rw [Real.norm_eq_abs, abs_of_pos h9]
    rw [h10, h11] at h6
    have h12 : Real.log x ≤ (1 / C) * x ^ (loss2 - loss1) := h6
    have h13 : C * Real.log x ≤ x ^ (loss2 - loss1) := by
      calc C * Real.log x
          ≤ C * ((1 / C) * x ^ (loss2 - loss1)) := by gcongr
        _ = x ^ (loss2 - loss1) := by
          field_simp [hC_pos.ne'] <;> ring
    exact h13
  rcases h_main with ⟨X, hX_pos, hX⟩
  let δ₀ := min (1 / X) (1 / 2)
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le_one : δ₀ ≤ 1 := by
    have h : δ₀ ≤ 1 / 2 := min_le_right _ _
    linarith
  have hδ₀_lt_one : δ₀ < 1 := by
    have h : δ₀ ≤ 1 / 2 := min_le_right _ _
    linarith
  refine ⟨δ₀, hδ₀_pos, hδ₀_le_one, ?_⟩
  intro delta hdelta_pos hdelta_le family shading1 shading2 extremal1 hsub hmass hcubical
  have h1 : 1 < 1 / delta := by
    have h2 : delta < 1 := by linarith [hδ₀_lt_one]
    field_simp [hdelta_pos.ne'] <;> linarith
  have hlog_pos : 0 < Real.log (1 / delta) := Real.log_pos h1
  have hClog_pos : 0 < C * Real.log (1 / delta) := mul_pos hC_pos hlog_pos
  let K : ENNReal := ENNReal.ofReal (C * Real.log (1 / delta))
  have hK_pos : 0 < K := by
    exact ENNReal.ofReal_pos.mpr hClog_pos
  have hK_ne_top : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have h2 : 1 / delta ≥ X := by
    have h3 : delta ≤ 1 / X := by
      have h4 : delta ≤ δ₀ := hdelta_le
      have h5 : δ₀ ≤ 1 / X := min_le_left _ _
      linarith
    calc 1 / delta ≥ 1 / (1 / X) := by gcongr
      _ = X := by field_simp [hX_pos.ne'] <;> ring
  have h_log_bound : C * Real.log (1 / delta) ≤ (1 / delta) ^ (loss2 - loss1) := hX (1 / delta) h2
  have h_slack_real : C * Real.log (1 / delta) * delta ^ (loss2 - loss1) ≤ 1 := by
    have h_pos1 : 0 ≤ 1 / delta := by positivity
    have h_pos2 : 0 ≤ delta := by linarith
    have h_prod : (1 / delta) ^ (loss2 - loss1) * delta ^ (loss2 - loss1) = 1 := by
      have h : (1 / delta) ^ (loss2 - loss1) * delta ^ (loss2 - loss1) =
          ((1 / delta) * delta) ^ (loss2 - loss1) := by
        rw [← Real.mul_rpow h_pos1 h_pos2]
      rw [h]
      have h2 : (1 / delta) * delta = 1 := by field_simp [hdelta_pos.ne']
      rw [h2]
      simp
    calc C * Real.log (1 / delta) * delta ^ (loss2 - loss1)
        ≤ (1 / delta) ^ (loss2 - loss1) * delta ^ (loss2 - loss1) := by gcongr
      _ = 1 := h_prod
  have h_slack : K * Kakeya.realRpowENN delta loss2 ≤ Kakeya.realRpowENN delta loss1 := by
    simp only [K, Kakeya.realRpowENN]
    rw [← ENNReal.ofReal_mul (show 0 ≤ C * Real.log (1 / delta) by linarith [hClog_pos])]
    apply ENNReal.ofReal_le_ofReal
    have h5 : C * Real.log (1 / delta) * delta ^ loss2 ≤ delta ^ loss1 := by
      have h_rpow : delta ^ (loss2 - loss1) * delta ^ loss1 = delta ^ loss2 := by
        have h : delta ^ ((loss2 - loss1) + loss1) = delta ^ (loss2 - loss1) * delta ^ loss1 :=
          Real.rpow_add hdelta_pos (loss2 - loss1) loss1
        have hsum : (loss2 - loss1) + loss1 = loss2 := by ring
        rw [hsum] at h
        exact h.symm
      have h6 : C * Real.log (1 / delta) * delta ^ loss2 =
          (C * Real.log (1 / delta) * delta ^ (loss2 - loss1)) * delta ^ loss1 := by
        rw [h_rpow.symm] <;> ring
      rw [h6]
      have h7 : 0 ≤ delta ^ loss1 := by positivity
      nlinarith
    exact h5
  have hmass' : K⁻¹ * shading1.mass ≤ shading2.mass := by
    have h_eq : K⁻¹ * shading1.mass = shading1.mass / K := by
      rw [div_eq_mul_inv] <;> ring
    rw [h_eq]
    exact hmass
  exact transfer_cropped_extremal_to_subshading
    K hK_pos hK_ne_top extremal1 hsub hmass' hcubical
    (by linarith) h_slack hdelta_pos (by linarith) hloss2_pos

/-- **Generalized polylog retention: absorbs `(log(1/δ))^n` with constant factor**.

For any `ε = loss2 - loss1 > 0`, `n : ℕ`, and `C > 0`, there exists `δ₀ > 0`
such that for all `δ ≤ δ₀`: if `shading1` is extremal at `loss1` and
`shading2` is a subshading with mass retention `≥ 1 / (C · (log(1/δ))^n)`,
then `shading2` is extremal at `loss2`.

This handles the sticky refinement fraction `(1/log)^logExponent` plus
additional constant overhead from the assembly pipeline.
Key fact: `(log x)^n = o(x^ε)` as `x → ∞`. -/
lemma transfer_extremal_polylog_retention_general
    {sigma loss1 loss2 : ℝ}
    (logExponent : ℕ)
    (C : ℝ)
    (hC_pos : 0 < C)
    (hε : 0 < loss2 - loss1)
    (hloss1_pos : 0 < loss1)
    (hloss2_pos : 0 < loss2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ δ₀ →
      ∀ {family : Kakeya.Streamlined.TubeFamily delta}
        {shading1 shading2 : WZ1PaperTubeShading family},
        WZ2PaperCroppedIsExtremal sigma loss1 family shading1 →
        PaperIsSubshading shading2 shading1 →
        shading1.mass / ENNReal.ofReal (C * (Real.log (1 / delta))^logExponent) ≤ shading2.mass →
        WZ1PaperIsCubicalShading shading2 →
        WZ2PaperCroppedIsExtremal sigma loss2 family shading2 := by
  -- Step 1: real analysis — C · (log x)^n ≤ x^ε for large x
  have h_main : ∃ X : ℝ, 0 < X ∧ ∀ x, x ≥ X →
      C * (Real.log x)^logExponent ≤ x ^ (loss2 - loss1) := by
    have h_littleO : (fun x : ℝ => Real.rpow (Real.log x) (logExponent : ℝ)) =o[Filter.atTop]
        (fun x : ℝ => x ^ (loss2 - loss1)) :=
      isLittleO_log_rpow_rpow_atTop (r := (logExponent : ℝ)) (s := loss2 - loss1) hε
    have h_invC_pos : 0 < 1 / C := by positivity
    have h_bigO : Asymptotics.IsBigOWith (1 / C) Filter.atTop
        (fun x : ℝ => Real.rpow (Real.log x) (logExponent : ℝ))
        (fun x : ℝ => x ^ (loss2 - loss1)) :=
      (Asymptotics.isLittleO_iff_forall_isBigOWith.mp h_littleO) h_invC_pos
    rcases Filter.mem_atTop_sets.mp h_bigO.bound with ⟨X, hX⟩
    let X' := max X 1
    have hX'_pos : 0 < X' := by positivity
    have hX'_one : 1 ≤ X' := le_max_right _ _
    refine ⟨X', hX'_pos, ?_⟩
    intro x hx
    have h4 : x ≥ X := by have h5 : X ≤ X' := le_max_left _ _; linarith
    have h6 : ‖Real.rpow (Real.log x) (logExponent : ℝ)‖ ≤ (1 / C) * ‖x ^ (loss2 - loss1)‖ := hX x h4
    have h7 : 1 ≤ x := by linarith
    have h8 : 0 ≤ Real.log x := Real.log_nonneg h7
    have h9 : 0 ≤ Real.rpow (Real.log x) (logExponent : ℝ) := Real.rpow_nonneg h8 _
    have h10 : 0 < x ^ (loss2 - loss1) := Real.rpow_pos_of_pos (by linarith) _
    have h11 : ‖Real.rpow (Real.log x) (logExponent : ℝ)‖ = Real.rpow (Real.log x) (logExponent : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg h9]
    have h12 : ‖x ^ (loss2 - loss1)‖ = x ^ (loss2 - loss1) := by
      rw [Real.norm_eq_abs, abs_of_pos h10]
    rw [h11, h12] at h6
    have h13 : Real.rpow (Real.log x) (logExponent : ℝ) ≤ (1 / C) * x ^ (loss2 - loss1) := h6
    have h14 : Real.rpow (Real.log x) (logExponent : ℝ) = (Real.log x)^logExponent := by simp
    rw [h14] at h13
    have h15 : C * (Real.log x)^logExponent ≤ x ^ (loss2 - loss1) := by
      calc C * (Real.log x)^logExponent
          ≤ C * ((1 / C) * x ^ (loss2 - loss1)) := by gcongr
        _ = x ^ (loss2 - loss1) := by
          field_simp [hC_pos.ne'] <;> ring
    exact h15
  rcases h_main with ⟨X, hX_pos, hX⟩
  let δ₀ := min (1 / X) (1 / 2)
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le_one : δ₀ ≤ 1 := by
    have h : δ₀ ≤ 1 / 2 := min_le_right _ _
    linarith
  have hδ₀_lt_one : δ₀ < 1 := by
    have h : δ₀ ≤ 1 / 2 := min_le_right _ _
    linarith
  refine ⟨δ₀, hδ₀_pos, hδ₀_le_one, ?_⟩
  intro delta hdelta_pos hdelta_le family shading1 shading2 extremal1 hsub hmass hcubical
  have h1 : 1 < 1 / delta := by
    have h2 : delta < 1 := by linarith [hδ₀_lt_one]
    field_simp [hdelta_pos.ne'] <;> linarith
  have hlog_pos : 0 < Real.log (1 / delta) := Real.log_pos h1
  have hlog_pow_pos : 0 < (Real.log (1 / delta))^logExponent := by positivity
  have hClog_pow_pos : 0 < C * (Real.log (1 / delta))^logExponent := mul_pos hC_pos hlog_pow_pos
  let K : ENNReal := ENNReal.ofReal (C * (Real.log (1 / delta))^logExponent)
  have hK_pos : 0 < K := ENNReal.ofReal_pos.mpr hClog_pow_pos
  have hK_ne_top : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have h2 : 1 / delta ≥ X := by
    have h3 : delta ≤ 1 / X := by
      have h4 : delta ≤ δ₀ := hdelta_le
      have h5 : δ₀ ≤ 1 / X := min_le_left _ _
      linarith
    calc 1 / delta ≥ 1 / (1 / X) := by gcongr
      _ = X := by field_simp [hX_pos.ne'] <;> ring
  have h_log_bound : C * (Real.log (1 / delta))^logExponent ≤ (1 / delta) ^ (loss2 - loss1) :=
    hX (1 / delta) h2
  have h_slack_real : C * (Real.log (1 / delta))^logExponent * delta ^ (loss2 - loss1) ≤ 1 := by
    have h_pos1 : 0 ≤ 1 / delta := by positivity
    have h_pos2 : 0 ≤ delta := by linarith
    have h_prod : (1 / delta) ^ (loss2 - loss1) * delta ^ (loss2 - loss1) = 1 := by
      have h : (1 / delta) ^ (loss2 - loss1) * delta ^ (loss2 - loss1) =
          ((1 / delta) * delta) ^ (loss2 - loss1) := by
        rw [← Real.mul_rpow h_pos1 h_pos2]
      rw [h]
      have h2 : (1 / delta) * delta = 1 := by field_simp [hdelta_pos.ne']
      rw [h2]
      simp
    calc C * (Real.log (1 / delta))^logExponent * delta ^ (loss2 - loss1)
        ≤ (1 / delta) ^ (loss2 - loss1) * delta ^ (loss2 - loss1) := by gcongr
      _ = 1 := h_prod
  have h_slack : K * Kakeya.realRpowENN delta loss2 ≤ Kakeya.realRpowENN delta loss1 := by
    simp only [K, Kakeya.realRpowENN]
    rw [← ENNReal.ofReal_mul (show 0 ≤ C * (Real.log (1 / delta))^logExponent by linarith [hClog_pow_pos])]
    apply ENNReal.ofReal_le_ofReal
    have h5 : C * (Real.log (1 / delta))^logExponent * delta ^ loss2 ≤ delta ^ loss1 := by
      have h_rpow : delta ^ (loss2 - loss1) * delta ^ loss1 = delta ^ loss2 := by
        have h : delta ^ ((loss2 - loss1) + loss1) = delta ^ (loss2 - loss1) * delta ^ loss1 :=
          Real.rpow_add hdelta_pos (loss2 - loss1) loss1
        have hsum : (loss2 - loss1) + loss1 = loss2 := by ring
        rw [hsum] at h
        exact h.symm
      have h6 : C * (Real.log (1 / delta))^logExponent * delta ^ loss2 =
          (C * (Real.log (1 / delta))^logExponent * delta ^ (loss2 - loss1)) * delta ^ loss1 := by
        rw [h_rpow.symm] <;> ring
      rw [h6]
      have h7 : 0 ≤ delta ^ loss1 := by positivity
      nlinarith
    exact h5
  have hmass' : K⁻¹ * shading1.mass ≤ shading2.mass := by
    have h_eq : K⁻¹ * shading1.mass = shading1.mass / K := by
      rw [div_eq_mul_inv] <;> ring
    rw [h_eq]
    exact hmass
  exact transfer_cropped_extremal_to_subshading
    K hK_pos hK_ne_top extremal1 hsub hmass' hcubical
    (by linarith) h_slack hdelta_pos (by linarith) hloss2_pos

/-- **Paper pipeline mass retention in logarithmic form**.

The constant-multiplicity refinement retains `1/(log₂ N + 1)` and the
plane-map wiring retains `1/(16 · capCount)`, so the total retention is
`1/((16 · capCount) · (log₂ N + 1))`.

Using `paper_log_card_bound`, we convert `log₂ N + 1 = O(log(1/δ))`,
giving retention `1/(C · log(1/δ))` for an explicit constant `C`.

This is exactly the form required by `transfer_extremal_polylog_retention`
with `logExponent = 1`. -/
lemma paper_pipeline_mass_retention_log
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S_fiber S_cm S_final : WZ1PaperTubeShading F}
    (hed : WZ1PaperIsEssentiallyDistinct F)
    (hline : WZ1PaperIsLineClass F)
    (hdelta_pos : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (h_nonempty : 0 < F.card)
    (capCount : ℕ)
    (hcap_pos : 0 < capCount)
    (hmass_cm :
      S_fiber.mass ≤
        ((Nat.log 2 F.card + 1 : ℕ) : ENNReal) * S_cm.mass)
    (hmass_final :
      S_cm.mass ≤
        (16 : ENNReal) * (capCount : ENNReal) * S_final.mass)
    (hlog_small : 1 ≤ Real.log (1 / delta)) :
    ∃ (C : ℝ), 0 < C ∧
      S_fiber.mass / ENNReal.ofReal (C * Real.log (1 / delta)) ≤
        S_final.mass := by
  let C_log : ℝ := (5 + 5 * Real.log 163) / Real.log 2 + 1
  let C : ℝ := 16 * (capCount : ℝ) * C_log
  have hC_log_pos : 0 < C_log := by positivity
  have hC_pos : 0 < C := by positivity
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (Nat.log 2 F.card + 1 : ℝ) ≤ C_log * Real.log (1 / delta) := by
    have h := paper_log_card_bound hed hline hdelta_pos hdelta_one h_nonempty
    set x : ℝ := Real.log (1 / delta) with hx_def
    have hx_one : 1 ≤ x := hlog_small
    have hB_pos : 0 ≤ 5 * Real.log 163 / Real.log 2 + 1 := by positivity
    have h_diff : (5 * Real.log 163 / Real.log 2 + 1) * (x - 1) ≥ 0 :=
      mul_nonneg hB_pos (by linarith)
    have h3 : C_log * x ≥
        (5 / Real.log 2) * x + (5 * Real.log 163 / Real.log 2 + 1) := by
      have h4 : C_log * x - ((5 / Real.log 2) * x + (5 * Real.log 163 / Real.log 2 + 1)) =
          (5 * Real.log 163 / Real.log 2 + 1) * (x - 1) := by
        simp [C_log] <;> ring
      linarith
    exact le_trans h h3
  have h3 : 16 * (capCount : ℝ) * ((Nat.log 2 F.card + 1 : ℝ)) ≤
      C * Real.log (1 / delta) := by
    calc
      16 * (capCount : ℝ) * ((Nat.log 2 F.card + 1 : ℝ))
        ≤ 16 * (capCount : ℝ) * (C_log * Real.log (1 / delta)) := by gcongr
      _ = C * Real.log (1 / delta) := by
        simp [C] <;> ring
  let L : ENNReal := ((Nat.log 2 F.card + 1 : ℕ) : ENNReal)
  have h4 : (16 : ENNReal) * (capCount : ENNReal) * L ≤
      ENNReal.ofReal (C * Real.log (1 / delta)) := by
    have h5 : ((16 : ENNReal) * (capCount : ENNReal) * L) =
        ENNReal.ofReal (16 * (capCount : ℝ) * ((Nat.log 2 F.card + 1 : ℝ))) := by
      simp [L, ENNReal.ofReal_mul]
      <;> norm_cast
    rw [h5]
    exact ENNReal.ofReal_le_ofReal h3
  have h6 : S_fiber.mass ≤
      (16 : ENNReal) * (capCount : ENNReal) * L * S_final.mass := by
    calc
      S_fiber.mass
        ≤ L * S_cm.mass := hmass_cm
      _ ≤ L * ((16 : ENNReal) * (capCount : ENNReal) * S_final.mass) := by gcongr
      _ = (16 : ENNReal) * (capCount : ENNReal) * L * S_final.mass := by ring
  let D : ENNReal := (16 : ENNReal) * (capCount : ENNReal) * L
  have hL_pos : 0 < L := by
    have h : 0 < Nat.log 2 F.card + 1 := by omega
    simpa [L] using ENNReal.coe_pos.mpr h
  have hD_pos : 0 < D := by
    have h1 : (0 : ENNReal) < (16 : ENNReal) := by norm_num
    have h2 : (0 : ENNReal) < (capCount : ENNReal) := by exact_mod_cast hcap_pos
    have h3 : (0 : ENNReal) < L := hL_pos
    positivity
  have hD_ne_top : D ≠ ⊤ := by
    simp [D, ENNReal.mul_eq_top]
    <;> tauto
  have h_cancel : D * D⁻¹ = 1 := ENNReal.mul_inv_cancel hD_pos.ne' hD_ne_top
  have h7 : S_fiber.mass / D ≤ S_final.mass := by
    calc
      S_fiber.mass / D
        = S_fiber.mass * D⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (D * S_final.mass) * D⁻¹ := by gcongr
      _ = S_final.mass * (D * D⁻¹) := by ring
      _ = S_final.mass * 1 := by rw [h_cancel]
      _ = S_final.mass := by ring
  have h11 : S_fiber.mass / ENNReal.ofReal (C * Real.log (1 / delta)) ≤
      S_fiber.mass / D := by
    have h_inv : (ENNReal.ofReal (C * Real.log (1 / delta)))⁻¹ ≤ D⁻¹ := by
      rw [ENNReal.inv_le_inv]
      exact h4
    calc
      S_fiber.mass / ENNReal.ofReal (C * Real.log (1 / delta))
        = S_fiber.mass * (ENNReal.ofReal (C * Real.log (1 / delta)))⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ S_fiber.mass * D⁻¹ := by gcongr
      _ = S_fiber.mass / D := by rw [div_eq_mul_inv]
  exact ⟨C, hC_pos, le_trans h11 h7⟩

/-- **Full extremality transfer through the paper pruning pipeline**.

Combines `paper_pipeline_mass_retention_log` with
`transfer_extremal_polylog_retention_general` (logExponent = 1).

Given a fiber shading extremal at `loss1`, a constant-multiplicity intermediate
shading, and a final pruned shading with the standard plane-map wiring mass
retention, produces a `δ₀` such that for `delta ≤ δ₀`, the final shading is
extremal at `loss2`.

This is the single entry point for Strategy3Main's gap 5. -/
lemma transfer_extremal_through_paper_pipeline
    {sigma loss1 loss2 delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S_fiber S_cm S_final : WZ1PaperTubeShading F}
    (hed : WZ1PaperIsEssentiallyDistinct F)
    (hline : WZ1PaperIsLineClass F)
    (hdelta_pos : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (h_nonempty : F.Nonempty)
    (capCount : ℕ)
    (hcap_pos : 0 < capCount)
    (hextremal : WZ2PaperCroppedIsExtremal sigma loss1 F S_fiber)
    (hsub : PaperIsSubshading S_final S_fiber)
    (hcubical : WZ1PaperIsCubicalShading S_final)
    (hmass_cm :
      S_fiber.mass ≤
        ((Nat.log 2 F.card + 1 : ℕ) : ENNReal) * S_cm.mass)
    (hmass_final :
      S_cm.mass ≤
        (16 : ENNReal) * (capCount : ENNReal) * S_final.mass)
    (hlog_small : 1 ≤ Real.log (1 / delta))
    (hε : 0 < loss2 - loss1)
    (hloss1_pos : 0 < loss1)
    (hloss2_pos : 0 < loss2) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      (delta ≤ δ₀ → WZ2PaperCroppedIsExtremal sigma loss2 F S_final) := by
  rcases paper_pipeline_mass_retention_log
      hed hline hdelta_pos hdelta_one h_nonempty capCount hcap_pos
      hmass_cm hmass_final hlog_small
    with ⟨C, hC_pos, hmass⟩
  rcases transfer_extremal_polylog_retention_general
      (1 : ℕ) C hC_pos hε hloss1_pos hloss2_pos
    with ⟨δ₀, hδ₀_pos, hδ₀_le_one, htransfer⟩
  have hmass' : S_fiber.mass / ENNReal.ofReal (C * (Real.log (1 / delta))^1) ≤ S_final.mass := by
    have h_eq : C * (Real.log (1 / delta))^1 = C * Real.log (1 / delta) := by
      simp [pow_one]
    rw [h_eq]
    exact hmass
  refine ⟨δ₀, hδ₀_pos, hδ₀_le_one, fun hdelta_le => ?_⟩
  exact htransfer delta hdelta_pos hdelta_le hextremal hsub hmass' hcubical

/-- **Paper pipeline mass retention without essentially-distinct assumption**.

Uses the trivial fact that for a fixed finite family with `N` tubes,
`log₂ N + 1` is a constant, and for `δ ≤ 1/e` we have `log(1/δ) ≥ 1`, so
`(16·capCount)·(log₂ N + 1) ≤ (16·capCount)·(log₂ N + 1)·log(1/δ)`.

This avoids the `hed` requirement of `paper_pipeline_mass_retention_log`. -/
lemma paper_pipeline_mass_retention_no_hed
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S_fiber S_cm S_final : WZ1PaperTubeShading F}
    (hdelta_pos : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (h_nonempty : 0 < F.card)
    (capCount : ℕ)
    (hcap_pos : 0 < capCount)
    (hmass_cm :
      S_fiber.mass ≤
        ((Nat.log 2 F.card + 1 : ℕ) : ENNReal) * S_cm.mass)
    (hmass_final :
      S_cm.mass ≤
        (16 : ENNReal) * (capCount : ENNReal) * S_final.mass)
    (hlog_small : 1 ≤ Real.log (1 / delta)) :
    ∃ (C : ℝ), 0 < C ∧
      S_fiber.mass / ENNReal.ofReal (C * Real.log (1 / delta)) ≤
        S_final.mass := by
  let N_log : ℕ := Nat.log 2 F.card + 1
  let C : ℝ := 16 * (capCount : ℝ) * (N_log : ℝ)
  have hC_pos : 0 < C := by positivity
  have h1 : S_fiber.mass ≤
      (16 : ENNReal) * (capCount : ENNReal) * ((N_log : ENNReal)) * S_final.mass := by
    calc
      S_fiber.mass
        ≤ ((N_log : ENNReal)) * S_cm.mass := hmass_cm
      _ ≤ ((N_log : ENNReal)) * ((16 : ENNReal) * (capCount : ENNReal) * S_final.mass) := by gcongr
      _ = (16 : ENNReal) * (capCount : ENNReal) * ((N_log : ENNReal)) * S_final.mass := by ring
  let D : ENNReal := (16 : ENNReal) * (capCount : ENNReal) * (N_log : ENNReal)
  have hD_pos : 0 < D := by positivity
  have hD_ne_top : D ≠ ⊤ := by simp [D, ENNReal.mul_eq_top] <;> tauto
  have h2 : S_fiber.mass / D ≤ S_final.mass := by
    calc
      S_fiber.mass / D
        = S_fiber.mass * D⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (D * S_final.mass) * D⁻¹ := by gcongr
      _ = S_final.mass * (D * D⁻¹) := by ring
      _ = S_final.mass * 1 := by rw [ENNReal.mul_inv_cancel hD_pos.ne' hD_ne_top]
      _ = S_final.mass := by ring
  have h3 : D ≤ ENNReal.ofReal (C * Real.log (1 / delta)) := by
    have h4 : D = ENNReal.ofReal C := by
      have hC_eq : C = ENNReal.toReal D := by
        simp [D, C, ENNReal.toReal_mul, hD_ne_top] <;> norm_cast <;> ring
      rw [hC_eq]
      exact Eq.symm (ENNReal.ofReal_toReal hD_ne_top)
    rw [h4]
    have h5 : C ≤ C * Real.log (1 / delta) := by
      have h6 : 1 ≤ Real.log (1 / delta) := hlog_small
      have h7 : 0 ≤ C := by positivity
      nlinarith
    exact ENNReal.ofReal_le_ofReal h5
  have h4 : S_fiber.mass / ENNReal.ofReal (C * Real.log (1 / delta)) ≤
      S_fiber.mass / D := by
    have h5 : (ENNReal.ofReal (C * Real.log (1 / delta)))⁻¹ ≤ D⁻¹ := by
      rw [ENNReal.inv_le_inv] <;> exact h3
    calc
      S_fiber.mass / ENNReal.ofReal (C * Real.log (1 / delta))
        = S_fiber.mass * (ENNReal.ofReal (C * Real.log (1 / delta)))⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ S_fiber.mass * D⁻¹ := by gcongr
      _ = S_fiber.mass / D := by rw [div_eq_mul_inv]
  exact ⟨C, hC_pos, le_trans h4 h2⟩

/-- **Generalized paper pipeline mass retention (no `hed` required)**.

Like `paper_pipeline_mass_retention_no_hed`, but accepts an arbitrary `factor`
for the constant-multiplicity retention. Use `factor = 2` for
`high_multiplicity_dyadic_band` (retention `1/(2*(log₂N+1))`). -/
lemma paper_pipeline_mass_retention_no_hed_general
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S_fiber S_cm S_final : WZ1PaperTubeShading F}
    (factor : ℕ)
    (hfactor_pos : 0 < factor)
    (hdelta_pos : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (h_nonempty : 0 < F.card)
    (capCount : ℕ)
    (hcap_pos : 0 < capCount)
    (hmass_cm :
      S_fiber.mass ≤
        ((factor : ENNReal) * ((Nat.log 2 F.card + 1 : ℕ) : ENNReal)) * S_cm.mass)
    (hmass_final :
      S_cm.mass ≤
        (16 : ENNReal) * (capCount : ENNReal) * S_final.mass)
    (hlog_small : 1 ≤ Real.log (1 / delta)) :
    ∃ (C : ℝ), 0 < C ∧
      S_fiber.mass / ENNReal.ofReal (C * Real.log (1 / delta)) ≤
        S_final.mass := by
  let N_log : ℕ := Nat.log 2 F.card + 1
  let C : ℝ := 16 * (capCount : ℝ) * (factor : ℝ) * (N_log : ℝ)
  have hC_pos : 0 < C := by positivity
  let D : ENNReal := (16 : ENNReal) * (capCount : ENNReal) * (factor : ENNReal) * (N_log : ENNReal)
  have hD_pos : 0 < D := by positivity
  have hD_ne_top : D ≠ ⊤ := by simp [D, ENNReal.mul_eq_top] <;> tauto
  have h1 : S_fiber.mass ≤ D * S_final.mass := by
    calc
      S_fiber.mass
        ≤ ((factor : ENNReal) * (N_log : ENNReal)) * S_cm.mass := hmass_cm
      _ ≤ ((factor : ENNReal) * (N_log : ENNReal)) *
            ((16 : ENNReal) * (capCount : ENNReal) * S_final.mass) := by gcongr
      _ = D * S_final.mass := by ring
  have h2 : S_fiber.mass / D ≤ S_final.mass := by
    calc
      S_fiber.mass / D
        = S_fiber.mass * D⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (D * S_final.mass) * D⁻¹ := by gcongr
      _ = S_final.mass * (D * D⁻¹) := by ring
      _ = S_final.mass * 1 := by rw [ENNReal.mul_inv_cancel hD_pos.ne' hD_ne_top]
      _ = S_final.mass := by ring
  have h3 : D ≤ ENNReal.ofReal (C * Real.log (1 / delta)) := by
    have h4 : D = ENNReal.ofReal C := by
      have hC_eq : C = ENNReal.toReal D := by
        simp [D, C, ENNReal.toReal_mul, hD_ne_top] <;> norm_cast <;> ring
      rw [hC_eq]
      exact Eq.symm (ENNReal.ofReal_toReal hD_ne_top)
    rw [h4]
    have h5 : C ≤ C * Real.log (1 / delta) := by
      have h6 : 1 ≤ Real.log (1 / delta) := hlog_small
      have h7 : 0 ≤ C := by positivity
      nlinarith
    exact ENNReal.ofReal_le_ofReal h5
  have h4 : S_fiber.mass / ENNReal.ofReal (C * Real.log (1 / delta)) ≤
      S_fiber.mass / D := by
    have h5 : (ENNReal.ofReal (C * Real.log (1 / delta)))⁻¹ ≤ D⁻¹ := by
      rw [ENNReal.inv_le_inv] <;> exact h3
    calc
      S_fiber.mass / ENNReal.ofReal (C * Real.log (1 / delta))
        = S_fiber.mass * (ENNReal.ofReal (C * Real.log (1 / delta)))⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ S_fiber.mass * D⁻¹ := by gcongr
      _ = S_fiber.mass / D := by rw [div_eq_mul_inv]
  exact ⟨C, hC_pos, le_trans h4 h2⟩

/-- **Full extremality transfer through paper pipeline (no `hed` required)**.

Like `transfer_extremal_through_paper_pipeline`, but uses
`paper_pipeline_mass_retention_no_hed` instead of requiring essentially distinct.
This is the recommended entry point for Strategy3Main integration. -/
lemma transfer_extremal_through_paper_pipeline_no_hed
    {sigma loss1 loss2 delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S_fiber S_cm S_final : WZ1PaperTubeShading F}
    (hdelta_pos : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (h_nonempty : F.Nonempty)
    (capCount : ℕ)
    (hcap_pos : 0 < capCount)
    (hextremal : WZ2PaperCroppedIsExtremal sigma loss1 F S_fiber)
    (hsub : PaperIsSubshading S_final S_fiber)
    (hcubical : WZ1PaperIsCubicalShading S_final)
    (hmass_cm :
      S_fiber.mass ≤
        ((Nat.log 2 F.card + 1 : ℕ) : ENNReal) * S_cm.mass)
    (hmass_final :
      S_cm.mass ≤
        (16 : ENNReal) * (capCount : ENNReal) * S_final.mass)
    (hlog_small : 1 ≤ Real.log (1 / delta))
    (hε : 0 < loss2 - loss1)
    (hloss1_pos : 0 < loss1)
    (hloss2_pos : 0 < loss2) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      (delta ≤ δ₀ → WZ2PaperCroppedIsExtremal sigma loss2 F S_final) := by
  rcases paper_pipeline_mass_retention_no_hed
      hdelta_pos hdelta_one h_nonempty capCount hcap_pos
      hmass_cm hmass_final hlog_small
    with ⟨C, hC_pos, hmass⟩
  rcases transfer_extremal_polylog_retention_general
      (1 : ℕ) C hC_pos hε hloss1_pos hloss2_pos
    with ⟨δ₀, hδ₀_pos, hδ₀_le_one, htransfer⟩
  have hmass' : S_fiber.mass / ENNReal.ofReal (C * (Real.log (1 / delta))^1) ≤ S_final.mass := by
    have h_eq : C * (Real.log (1 / delta))^1 = C * Real.log (1 / delta) := by simp [pow_one]
    rw [h_eq]
    exact hmass
  refine ⟨δ₀, hδ₀_pos, hδ₀_le_one, fun hdelta_le => ?_⟩
  exact htransfer delta hdelta_pos hdelta_le hextremal hsub hmass' hcubical

/-- **Full extremality transfer through paper pipeline, generalized (no `hed`)**.

Like `transfer_extremal_through_paper_pipeline_no_hed`, but accepts an arbitrary
`factor` for the constant-multiplicity retention. Use `factor = 2` for
`high_multiplicity_dyadic_band`. -/
lemma transfer_extremal_through_paper_pipeline_no_hed_general
    {sigma loss1 loss2 delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S_fiber S_cm S_final : WZ1PaperTubeShading F}
    (factor : ℕ)
    (hfactor_pos : 0 < factor)
    (hdelta_pos : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (h_nonempty : F.Nonempty)
    (capCount : ℕ)
    (hcap_pos : 0 < capCount)
    (hextremal : WZ2PaperCroppedIsExtremal sigma loss1 F S_fiber)
    (hsub : PaperIsSubshading S_final S_fiber)
    (hcubical : WZ1PaperIsCubicalShading S_final)
    (hmass_cm :
      S_fiber.mass ≤
        ((factor : ENNReal) * ((Nat.log 2 F.card + 1 : ℕ) : ENNReal)) * S_cm.mass)
    (hmass_final :
      S_cm.mass ≤
        (16 : ENNReal) * (capCount : ENNReal) * S_final.mass)
    (hlog_small : 1 ≤ Real.log (1 / delta))
    (hε : 0 < loss2 - loss1)
    (hloss1_pos : 0 < loss1)
    (hloss2_pos : 0 < loss2) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      (delta ≤ δ₀ → WZ2PaperCroppedIsExtremal sigma loss2 F S_final) := by
  rcases paper_pipeline_mass_retention_no_hed_general
      factor hfactor_pos hdelta_pos hdelta_one h_nonempty capCount hcap_pos
      hmass_cm hmass_final hlog_small
    with ⟨C, hC_pos, hmass⟩
  rcases transfer_extremal_polylog_retention_general
      (1 : ℕ) C hC_pos hε hloss1_pos hloss2_pos
    with ⟨δ₀, hδ₀_pos, hδ₀_le_one, htransfer⟩
  have hmass' : S_fiber.mass / ENNReal.ofReal (C * (Real.log (1 / delta))^1) ≤ S_final.mass := by
    have h_eq : C * (Real.log (1 / delta))^1 = C * Real.log (1 / delta) := by simp [pow_one]
    rw [h_eq]
    exact hmass
  refine ⟨δ₀, hδ₀_pos, hδ₀_le_one, fun hdelta_le => ?_⟩
  exact htransfer delta hdelta_pos hdelta_le hextremal hsub hmass' hcubical

/-- **Combined-bound mass retention (no `hed` required)**.

Converts a single combined pipeline mass bound of the form
`S_fiber.mass ≤ K * (log₂ N + 1) * capCount * S_final.mass`
into the logarithmic form `S_fiber.mass / (C * log(1/δ)) ≤ S_final.mass`.

This is the right entry point when the pipeline (e.g.
`fiber_weak_planiness_to_lipschitz_map`) returns a single combined retention
bound rather than separate band and wiring bounds. -/
lemma paper_pipeline_mass_retention_combined
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S_fiber S_final : WZ1PaperTubeShading F}
    (K : ℕ)
    (hK_pos : 0 < K)
    (hdelta_pos : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (h_nonempty : 0 < F.card)
    (capCount : ℕ)
    (hcap_pos : 0 < capCount)
    (hmass :
      S_fiber.mass ≤
        (K : ENNReal) * ((Nat.log 2 F.card + 1 : ℕ) : ENNReal) *
        (capCount : ENNReal) * S_final.mass)
    (hlog_small : 1 ≤ Real.log (1 / delta)) :
    ∃ (C : ℝ), 0 < C ∧
      S_fiber.mass / ENNReal.ofReal (C * Real.log (1 / delta)) ≤
        S_final.mass := by
  let N_log : ℕ := Nat.log 2 F.card + 1
  let C : ℝ := (K : ℝ) * (capCount : ℝ) * (N_log : ℝ)
  have hC_pos : 0 < C := by positivity
  let D : ENNReal := (K : ENNReal) * (N_log : ENNReal) * (capCount : ENNReal)
  have hD_pos : 0 < D := by positivity
  have hD_ne_top : D ≠ ⊤ := by simp [D, ENNReal.mul_eq_top] <;> tauto
  have h1 : S_fiber.mass ≤ D * S_final.mass := by
    have h_eq : D * S_final.mass =
        (K : ENNReal) * (N_log : ENNReal) * (capCount : ENNReal) * S_final.mass := by
      simp [D] <;> ring
    rw [h_eq]
    exact hmass
  have h2 : S_fiber.mass / D ≤ S_final.mass := by
    calc
      S_fiber.mass / D
        = S_fiber.mass * D⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (D * S_final.mass) * D⁻¹ := by gcongr
      _ = S_final.mass * (D * D⁻¹) := by ring
      _ = S_final.mass * 1 := by rw [ENNReal.mul_inv_cancel hD_pos.ne' hD_ne_top]
      _ = S_final.mass := by ring
  have h3 : D ≤ ENNReal.ofReal (C * Real.log (1 / delta)) := by
    have h4 : D = ENNReal.ofReal C := by
      have hC_eq : C = ENNReal.toReal D := by
        simp [D, C, ENNReal.toReal_mul, hD_ne_top] <;> norm_cast <;> ring
      rw [hC_eq]
      exact Eq.symm (ENNReal.ofReal_toReal hD_ne_top)
    rw [h4]
    have h5 : C ≤ C * Real.log (1 / delta) := by
      have h6 : 1 ≤ Real.log (1 / delta) := hlog_small
      have h7 : 0 ≤ C := by positivity
      nlinarith
    exact ENNReal.ofReal_le_ofReal h5
  have h4 : S_fiber.mass / ENNReal.ofReal (C * Real.log (1 / delta)) ≤
      S_fiber.mass / D := by
    have h5 : (ENNReal.ofReal (C * Real.log (1 / delta)))⁻¹ ≤ D⁻¹ := by
      rw [ENNReal.inv_le_inv] <;> exact h3
    calc
      S_fiber.mass / ENNReal.ofReal (C * Real.log (1 / delta))
        = S_fiber.mass * (ENNReal.ofReal (C * Real.log (1 / delta)))⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ S_fiber.mass * D⁻¹ := by gcongr
      _ = S_fiber.mass / D := by rw [div_eq_mul_inv]
  exact ⟨C, hC_pos, le_trans h4 h2⟩

/-- **Full extremality transfer through combined-bound pipeline (no `hed`)**.

Takes a single combined mass retention bound from
`fiber_weak_planiness_to_lipschitz_map` (or similar) and transfers extremality
from `loss1` to `loss2`.

This is the recommended entry point for Strategy3Main integration when the
pipeline returns a single combined bound:
`S_fiber.mass ≤ K * (log₂ N + 1) * capCount * S_final.mass`.

For `fiber_weak_planiness_to_lipschitz_map`, use `K = 32`
(since `2 * 16 = 32`). -/
lemma transfer_extremal_through_combined_pipeline
    {sigma loss1 loss2 delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S_fiber S_final : WZ1PaperTubeShading F}
    (K : ℕ)
    (hK_pos : 0 < K)
    (hdelta_pos : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (h_nonempty : F.Nonempty)
    (capCount : ℕ)
    (hcap_pos : 0 < capCount)
    (hextremal : WZ2PaperCroppedIsExtremal sigma loss1 F S_fiber)
    (hsub : PaperIsSubshading S_final S_fiber)
    (hcubical : WZ1PaperIsCubicalShading S_final)
    (hmass :
      S_fiber.mass ≤
        (K : ENNReal) * ((Nat.log 2 F.card + 1 : ℕ) : ENNReal) *
        (capCount : ENNReal) * S_final.mass)
    (hlog_small : 1 ≤ Real.log (1 / delta))
    (hε : 0 < loss2 - loss1)
    (hloss1_pos : 0 < loss1)
    (hloss2_pos : 0 < loss2) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      (delta ≤ δ₀ → WZ2PaperCroppedIsExtremal sigma loss2 F S_final) := by
  rcases paper_pipeline_mass_retention_combined
      K hK_pos hdelta_pos hdelta_one h_nonempty capCount hcap_pos hmass hlog_small
    with ⟨C, hC_pos, hmass_log⟩
  rcases transfer_extremal_polylog_retention_general
      (1 : ℕ) C hC_pos hε hloss1_pos hloss2_pos
    with ⟨δ₀, hδ₀_pos, hδ₀_le_one, htransfer⟩
  have hmass' : S_fiber.mass / ENNReal.ofReal (C * (Real.log (1 / delta))^1) ≤ S_final.mass := by
    have h_eq : C * (Real.log (1 / delta))^1 = C * Real.log (1 / delta) := by simp [pow_one]
    rw [h_eq]
    exact hmass_log
  refine ⟨δ₀, hδ₀_pos, hδ₀_le_one, fun hdelta_le => ?_⟩
  exact htransfer delta hdelta_pos hdelta_le hextremal hsub hmass' hcubical

end Kakeya.Assouad

end
