import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44BadPairStatements
import Mathlib.Tactic

/-!
# ENNReal arithmetic helpers for WZ1 Lemma 44 assembly

Conversion and power identities for combining the three case bounds.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- `realRpowENN x y * realRpowENN x z = realRpowENN x (y + z)` for `x > 0`. -/
lemma lemma44_realRpowENN_mul {x y z : ℝ} (hx : 0 < x) :
    Kakeya.realRpowENN x y * Kakeya.realRpowENN x z =
    Kakeya.realRpowENN x (y + z) := by
  simp only [Kakeya.realRpowENN]
  have h1 : 0 ≤ Real.rpow x y := Real.rpow_nonneg (by linarith) _
  have h2 : 0 ≤ Real.rpow x z := Real.rpow_nonneg (by linarith) _
  have h_mul : ENNReal.ofReal (Real.rpow x y) * ENNReal.ofReal (Real.rpow x z) =
      ENNReal.ofReal (Real.rpow x y * Real.rpow x z) :=
    (ENNReal.ofReal_mul h1).symm
  rw [h_mul]
  have h3 : Real.rpow x y * Real.rpow x z = Real.rpow x (y + z) :=
    (Real.rpow_add hx y z).symm
  rw [h3]

/-- `realRpowENN (x * y) z = realRpowENN x z * realRpowENN y z` for `x, y > 0`. -/
lemma realRpowENN_ofReal_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℝ) :
    Kakeya.realRpowENN (x * y) z =
    Kakeya.realRpowENN x z * Kakeya.realRpowENN y z := by
  simp only [Kakeya.realRpowENN]
  have hxy_pos : 0 < x * y := mul_pos hx hy
  have h1 : Real.rpow (x * y) z = Real.rpow x z * Real.rpow y z :=
    Real.mul_rpow (by linarith) (by linarith)
  rw [h1]
  have h2 : 0 ≤ Real.rpow x z := Real.rpow_nonneg (by linarith) _
  have h3 : 0 ≤ Real.rpow y z := Real.rpow_nonneg (by linarith) _
  have h4 : ENNReal.ofReal (Real.rpow x z * Real.rpow y z) =
      ENNReal.ofReal (Real.rpow x z) * ENNReal.ofReal (Real.rpow y z) :=
    ENNReal.ofReal_mul h2
  exact h4

/-- Convert `ENNReal.ofReal a ≤ ENNReal.ofReal b` to `a ≤ b`. -/
lemma ENNReal_bound_to_real {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ENNReal.ofReal a ≤ ENNReal.ofReal b) : a ≤ b := by
  have h' : ENNReal.ofReal a ≤ ENNReal.ofReal b := h
  rw [ENNReal.ofReal_le_ofReal_iff hb] at h'
  exact h'

/--
Case 3 ENNReal bound: the product of Frostman constant, strip-intersection radius,
and `M²` is bounded by `delta^(4*alpha)`, using the arithmetic premise.

Requires `D * s = delta^(2*lambda + 4*alpha + 4*alpha/zeta)`.
-/
lemma case3_ENNReal_bound
    {delta lambda zeta alpha scale K D s : ℝ}
    (hdelta : 0 < delta) (hlambda : 0 < lambda) (hzeta : 0 < zeta)
    (halpha : 0 < alpha) (hscale : 0 < scale) (hK : 0 < K)
    (hD : 0 < D) (hs : 0 < s)
    (hDs : D * s = Real.rpow delta (2 * lambda + 4 * alpha + 4 * alpha / zeta))
    {M : ℕ}
    (hM : (M : ℝ) ≤ 20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ)))
    (hprem3 : (312000 : ℝ) / K ^ 4 *
        Real.rpow delta (-(3 * lambda + 4 * alpha + 4 * alpha / zeta)) ≤
        Real.rpow delta (4 * alpha)) :
    (Kakeya.realRpowENN delta (-lambda) *
     Kakeya.realRpowENN (60 * (13 * scale) / (D * s)) 1 *
     (M : ENNReal) * (M : ENNReal)) ≤
    Kakeya.realRpowENN delta (4 * alpha) := by
  have h_rpow12_pos : 0 < Real.rpow scale (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hscale _
  have hK2_pos : 0 < K ^ 2 := by positivity
  have h_bound_val_pos : 0 ≤ 20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ)) := by positivity
  have hM_ENNReal : (M : ENNReal) ≤ ENNReal.ofReal (20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))) := by
    have h1 : (M : ENNReal) = ENNReal.ofReal (M : ℝ) := by
      simp
    rw [h1]
    exact ENNReal.ofReal_le_ofReal hM
  have hM2_ENNReal : (M : ENNReal) * (M : ENNReal) ≤
      ENNReal.ofReal ((20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))) ^ 2) := by
    calc
      (M : ENNReal) * (M : ENNReal)
        ≤ ENNReal.ofReal (20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))) *
            ENNReal.ofReal (20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))) := by
          gcongr
      _ = ENNReal.ofReal ((20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))) ^ 2) := by
          rw [← ENNReal.ofReal_mul h_bound_val_pos]
          <;> congr 1 <;> ring
  set R : ℝ := 60 * (13 * scale) / (D * s) with hR_def
  have hR_nonneg : 0 ≤ R := by positivity
  have hCF_nonneg : 0 ≤ Real.rpow delta (-lambda) := Real.rpow_nonneg (by linarith) _
  have hM2_real : (20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))) ^ 2 =
      400 / (K ^ 4 * scale) := by
    have h1 : Real.rpow scale (1 / 2 : ℝ) ^ 2 = scale := by
      have h2 : Real.rpow scale (1 / 2 : ℝ) * Real.rpow scale (1 / 2 : ℝ) =
          Real.rpow scale ((1 / 2 : ℝ) + (1 / 2 : ℝ)) :=
        (Real.rpow_add hscale _ _).symm
      have h4 : Real.rpow scale 1 = scale := Real.rpow_one scale
      calc
        Real.rpow scale (1 / 2 : ℝ) ^ 2
          = Real.rpow scale (1 / 2 : ℝ) * Real.rpow scale (1 / 2 : ℝ) := by ring
        _ = Real.rpow scale ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := h2
        _ = Real.rpow scale 1 := by norm_num
        _ = scale := h4
    have h_denom_pos : 0 < K ^ 2 * Real.rpow scale (1 / 2 : ℝ) := by positivity
    have h_main : (20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))) ^ 2 =
        400 / ((K ^ 2 * Real.rpow scale (1 / 2 : ℝ)) ^ 2) := by
      rw [div_pow] <;> norm_num
    rw [h_main]
    have h5 : (K ^ 2 * Real.rpow scale (1 / 2 : ℝ)) ^ 2 = K ^ 4 * scale := by
      rw [mul_pow, h1] <;> ring
    rw [h5]
  have h_product_real : Real.rpow delta (-lambda) * R *
      ((20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))) ^ 2) =
      (312000 : ℝ) / K ^ 4 * Real.rpow delta (-(3 * lambda + 4 * alpha + 4 * alpha / zeta)) := by
    rw [hM2_real, hR_def]
    set E : ℝ := Real.rpow delta (2 * lambda + 4 * alpha + 4 * alpha / zeta) with hE_def
    set a : ℝ := -(3 * lambda + 4 * alpha + 4 * alpha / zeta) with ha_def
    have hE_pos : 0 < E := Real.rpow_pos_of_pos hdelta _
    have h_sum : a + (2 * lambda + 4 * alpha + 4 * alpha / zeta) = -lambda := by
      simp [ha_def] <;> ring
    have h_mul : Real.rpow delta a * E = Real.rpow delta (-lambda) := by
      have hE2 : E = Real.rpow delta (2 * lambda + 4 * alpha + 4 * alpha / zeta) := hE_def
      rw [hE2]
      have h_add : Real.rpow delta a * Real.rpow delta (2 * lambda + 4 * alpha + 4 * alpha / zeta) =
          Real.rpow delta (a + (2 * lambda + 4 * alpha + 4 * alpha / zeta)) :=
        (Real.rpow_add hdelta a (2 * lambda + 4 * alpha + 4 * alpha / zeta)).symm
      rw [h_add, h_sum]
    have h_rpow_div : Real.rpow delta (-lambda) / E = Real.rpow delta a := by
      have h' : Real.rpow delta a = Real.rpow delta (-lambda) / E := by
        exact (eq_div_iff hE_pos.ne').mpr h_mul
      exact h'.symm
    have h_scale_cancel : 60 * (13 * scale) * (400 / (K ^ 4 * scale)) =
        (312000 : ℝ) / K ^ 4 := by
      have hK4_pos : 0 < K ^ 4 := by positivity
      field_simp [hscale.ne', hK4_pos.ne'] <;> ring
    calc
      Real.rpow delta (-lambda) * (60 * (13 * scale) / (D * s)) * (400 / (K ^ 4 * scale))
        = Real.rpow delta (-lambda) * (60 * (13 * scale) / E) * (400 / (K ^ 4 * scale)) := by
          rw [hDs]
      _ = (Real.rpow delta (-lambda) / E) * (60 * (13 * scale) * (400 / (K ^ 4 * scale))) := by ring
      _ = (Real.rpow delta (-lambda) / E) * ((312000 : ℝ) / K ^ 4) := by rw [h_scale_cancel]
      _ = (312000 : ℝ) / K ^ 4 * (Real.rpow delta (-lambda) / E) := by ring
      _ = (312000 : ℝ) / K ^ 4 * Real.rpow delta a := by rw [h_rpow_div]
      _ = (312000 : ℝ) / K ^ 4 * Real.rpow delta (-(3 * lambda + 4 * alpha + 4 * alpha / zeta)) := by
        rw [show a = -(3 * lambda + 4 * alpha + 4 * alpha / zeta) from ha_def]
  have h_main : (Kakeya.realRpowENN delta (-lambda) *
      Kakeya.realRpowENN R 1 * (M : ENNReal) * (M : ENNReal)) ≤
      ENNReal.ofReal (Real.rpow delta (-lambda) * R *
        ((20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))) ^ 2)) := by
    calc
      (Kakeya.realRpowENN delta (-lambda) * Kakeya.realRpowENN R 1 *
          (M : ENNReal) * (M : ENNReal))
        = (Kakeya.realRpowENN delta (-lambda) * Kakeya.realRpowENN R 1) *
            ((M : ENNReal) * (M : ENNReal)) := by ring
      _ ≤ (ENNReal.ofReal (Real.rpow delta (-lambda)) * ENNReal.ofReal R) *
            ENNReal.ofReal ((20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))) ^ 2) := by
          gcongr
          <;> simpa [Kakeya.realRpowENN, Real.rpow_one] using hM2_ENNReal
      _ = ENNReal.ofReal (Real.rpow delta (-lambda) * R *
            ((20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))) ^ 2)) := by
          have h_pos1 : 0 ≤ Real.rpow delta (-lambda) := Real.rpow_nonneg (by linarith) _
          have h_pos2 : 0 ≤ R := by positivity
          have h_pos3 : 0 ≤ (20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))) ^ 2 := by positivity
          rw [← ENNReal.ofReal_mul h_pos1, ← ENNReal.ofReal_mul (mul_nonneg h_pos1 h_pos2)]
          <;> rfl
  rw [h_product_real] at h_main
  have h_final : ENNReal.ofReal ((312000 : ℝ) / K ^ 4 *
      Real.rpow delta (-(3 * lambda + 4 * alpha + 4 * alpha / zeta))) ≤
      Kakeya.realRpowENN delta (4 * alpha) := by
    simp only [Kakeya.realRpowENN]
    have h4alpha_pos : 0 ≤ Real.rpow delta (4 * alpha) := Real.rpow_nonneg (by linarith) _
    exact (ENNReal.ofReal_le_ofReal_iff h4alpha_pos).mpr hprem3
  exact h_main.trans h_final

end Kakeya.Assouad
