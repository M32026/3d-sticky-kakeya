import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Subunit.AsymptoticHelper

/-!
# Helper lemmas for the hard homogeneous hairbrush power assembly

General ENNReal/rpow algebra helpers used in
`hairbrush_homogeneous_hard_power`.

Includes:
* cross-division from a product inequality;
* constant absorption into a strict δ-exponent gap;
* normalization of `ofReal (δ^2)`;
* radius-to-density power conversion;
* layer-density to hair-density power conversion.
-/

namespace Kakeya.Assouad

/-- From `A * C ≤ B * D`, cross-divide to get `A / B ≤ D / C`. -/
lemma ennreal_cross_div {A B C D : ENNReal}
    (hB0 : B ≠ 0) (hBtop : B ≠ ⊤)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (h : A * C ≤ B * D) : A / B ≤ D / C := by
  have h1 : (A * C) / C ≤ (B * D) / C := by gcongr
  have h2 : (A * C) / C = A := ENNReal.mul_div_cancel_right hC0 hCtop
  rw [h2] at h1
  have h4 : (B * D) / C = (D / C) * B := by
    simp [div_eq_mul_inv, mul_assoc, mul_comm]
  rw [h4] at h1
  rw [ENNReal.div_le_iff hB0 hBtop]
  exact h1

/-- Absorb a positive real constant into a strict δ-exponent gap.

    Given `C * δ^e ≤ 1` with `C > 0`, conclude
    `ofReal C * realRpowENN δ (a + e) ≤ realRpowENN δ a`. -/
lemma ennreal_const_absorb {C : ℝ} (hCpos : 0 < C) {δ a e : ℝ} (hδ : 0 < δ)
    (h : C * Real.rpow δ e ≤ 1) :
    ENNReal.ofReal C * Kakeya.realRpowENN δ (a + e) ≤ Kakeya.realRpowENN δ a := by
  have hC : 0 ≤ C := by linarith
  have h1 : ENNReal.ofReal C * Kakeya.realRpowENN δ (a + e) =
      ENNReal.ofReal (C * Real.rpow δ (a + e)) :=
    Subunit.coe_realRpowENN_eq_ofReal hC hδ
  rw [h1]
  have h2 : C * Real.rpow δ (a + e) = Real.rpow δ a * (C * Real.rpow δ e) := by
    have h3 : Real.rpow δ (a + e) = Real.rpow δ a * Real.rpow δ e :=
      Real.rpow_add hδ a e
    rw [h3]
    ring
  rw [h2]
  have h4 : 0 ≤ Real.rpow δ a := Real.rpow_nonneg hδ.le a
  have h5 : Real.rpow δ a * (C * Real.rpow δ e) ≤ Real.rpow δ a :=
    mul_le_of_le_one_right h4 h
  exact ENNReal.ofReal_mono h5

/-- `ofReal (δ^2) = realRpowENN δ 2` for `δ > 0`. -/
lemma ofReal_delta_sq_eq {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (δ ^ 2) = Kakeya.realRpowENN δ 2 := by
  simp only [Kakeya.realRpowENN]
  have h : Real.rpow δ 2 = δ ^ 2 := by
    have h2 : Real.rpow δ 2 = Real.rpow δ 1 * Real.rpow δ 1 := by
      convert Real.rpow_add hδ 1 1 using 1 <;> norm_num
    have h3 : Real.rpow δ 1 = δ := Real.rpow_one δ
    rw [h2, h3]
    ring
  rw [h]

/-- Real fact: `(x⁻¹)^r = (x^r)⁻¹` for `x > 0`, `r : ℝ`. -/
private lemma real_inv_rpow {x : ℝ} (hx : 0 < x) (r : ℝ) :
    (x⁻¹) ^ r = (x ^ r)⁻¹ := by
  have h1 : x⁻¹ = x ^ (-1 : ℝ) := by
    have h2 : x ^ (-1 : ℝ) = (x ^ (1 : ℝ))⁻¹ := Real.rpow_neg hx.le 1
    simpa using h2.symm
  rw [h1]
  have h3 : (x ^ (-1 : ℝ)) ^ r = x ^ ((-1 : ℝ) * r) :=
    (Real.rpow_mul hx.le (-1 : ℝ) r).symm
  rw [h3]
  have h4 : (-1 : ℝ) * r = -r := by ring
  rw [h4]
  exact Real.rpow_neg hx.le r

/-- Convert `hairDensity ≤ 100 * radius^(1-zeta)` into
    `radius^(1+3*zeta) ≥ hairDensity^p_zeta / 100^p_zeta`. -/
lemma radius_power_to_density_power {zeta radius : ℝ} {hairDensity : ENNReal}
    (hzeta_pos : 0 < zeta) (hzeta_lt_one : zeta < 1)
    (hradius_pos : 0 < radius)
    (h : hairDensity ≤ ENNReal.ofReal 100 * ENNReal.ofReal (Real.rpow radius (1 - zeta))) :
    let p := (1 + 3 * zeta) / (1 - zeta)
    ENNReal.ofReal (Real.rpow radius (1 + 3 * zeta)) ≥
      hairDensity ^ p / (ENNReal.ofReal 100 ^ p) := by
  set p : ℝ := (1 + 3 * zeta) / (1 - zeta) with hp_def
  have h1minuszeta_pos : 0 < 1 - zeta := by linarith
  have hp_pos : 0 < p := by
    rw [hp_def]
    apply div_pos <;> linarith
  have hp_nonneg : 0 ≤ p := by linarith
  have hp_identity : (1 - zeta) * p = 1 + 3 * zeta := by
    rw [hp_def]
    field_simp [h1minuszeta_pos.ne']
  set R : ENNReal := ENNReal.ofReal (Real.rpow radius (1 - zeta)) with hR_def
  set C : ENNReal := ENNReal.ofReal 100 with hC_def
  have hrpow_pos : 0 < Real.rpow radius (1 - zeta) := Real.rpow_pos_of_pos hradius_pos (1 - zeta)
  have hC0 : C ≠ 0 := by
    rw [hC_def]
    simp
  have hCtop : C ≠ ⊤ := by
    rw [hC_def]
    exact ENNReal.ofReal_ne_top
  have hCp0 : C ^ p ≠ 0 := by
    intro hz
    rw [ENNReal.rpow_eq_zero_iff] at hz
    tauto
  have hCptop : C ^ p ≠ ⊤ := by
    intro hz
    rw [ENNReal.rpow_eq_top_iff] at hz
    tauto
  have h1 : hairDensity ≤ C * R := h
  have h2 : hairDensity ^ p ≤ (C * R) ^ p := ENNReal.rpow_le_rpow h1 hp_nonneg
  have h3 : (C * R) ^ p = C ^ p * R ^ p := ENNReal.mul_rpow_of_nonneg C R hp_nonneg
  have h4 : R ^ p = ENNReal.ofReal (Real.rpow radius (1 + 3 * zeta)) := by
    rw [hR_def, ENNReal.ofReal_rpow_of_pos hrpow_pos]
    apply congr_arg (fun x : ℝ => ENNReal.ofReal x)
    have h_mul : Real.rpow (Real.rpow radius (1 - zeta)) p = Real.rpow radius ((1 - zeta) * p) :=
      (Real.rpow_mul hradius_pos.le (1 - zeta) p).symm
    exact h_mul.trans (by rw [hp_identity])
  rw [h3, h4] at h2
  set X : ENNReal := ENNReal.ofReal (Real.rpow radius (1 + 3 * zeta)) with hX_def
  have h_cancel : C ^ p * X * (C ^ p)⁻¹ = X := by
    have h_comm : C ^ p * X * (C ^ p)⁻¹ = X * (C ^ p * (C ^ p)⁻¹) := by
      calc C ^ p * X * (C ^ p)⁻¹
        = (C ^ p * X) * (C ^ p)⁻¹ := by rw [mul_assoc]
      _ = (X * C ^ p) * (C ^ p)⁻¹ := by rw [mul_comm (C ^ p) X]
      _ = X * (C ^ p * (C ^ p)⁻¹) := by rw [mul_assoc]
    rw [h_comm, ENNReal.mul_inv_cancel hCp0 hCptop]
    simp
  have h5 : hairDensity ^ p / C ^ p ≤ X := by
    calc hairDensity ^ p / C ^ p
      ≤ (C ^ p * X) / C ^ p := by gcongr
    _ = C ^ p * X * (C ^ p)⁻¹ := by rw [div_eq_mul_inv]
    _ = X := h_cancel
  exact h5

/-- From `layerDensity / 2 ≤ hairDensity`, deduce
    `hairDensity^(2+p) ≥ layerDensity^(2+p) / 2^(2+p)`. -/
lemma hairDensity_power_from_layer {layerDensity hairDensity : ENNReal}
    (p : ℝ) (hp_nonneg : 0 ≤ p)
    (h : layerDensity / 2 ≤ hairDensity) :
    hairDensity ^ (2 + p) ≥ layerDensity ^ (2 + p) / (2 ^ (2 + p)) := by
  have h2p_nonneg : 0 ≤ (2 + p : ℝ) := by linarith
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h2p_real_pos : (0 : ℝ) < (2 : ℝ) ^ (2 + p) := by positivity
  have h2_eq : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_cast
  have h_inv_real : ((2 : ℝ)⁻¹) ^ (2 + p) = ((2 : ℝ) ^ (2 + p))⁻¹ :=
    real_inv_rpow h2_pos (2 + p)
  have h2inv_ennreal : (2 : ENNReal)⁻¹ = ENNReal.ofReal ((2 : ℝ)⁻¹) := by
    rw [h2_eq, ENNReal.ofReal_inv_of_pos h2_pos]
  have h_two_rpow : (2 : ENNReal) ^ (2 + p) = ENNReal.ofReal ((2 : ℝ) ^ (2 + p)) := by
    rw [h2_eq, ENNReal.ofReal_rpow_of_pos h2_pos]
  have h_goal : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (2 + p)) =
      (ENNReal.ofReal ((2 : ℝ) ^ (2 + p)))⁻¹ := by
    have h_step1 : (2 : ℝ)⁻¹ ^ (2 + p) = ((2 : ℝ) ^ (2 + p))⁻¹ := h_inv_real
    have h_step2 : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (2 + p)) =
        ENNReal.ofReal (((2 : ℝ) ^ (2 + p))⁻¹) := by
      rw [h_step1]
    rw [h_step2, ENNReal.ofReal_inv_of_pos h2p_real_pos]
  have h_inv_rpow : ((2 : ENNReal)⁻¹) ^ (2 + p) = ((2 : ENNReal) ^ (2 + p))⁻¹ := by
    rw [h2inv_ennreal, ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
    rw [h_two_rpow]
    exact h_goal
  have h_distrib : (layerDensity / (2 : ENNReal)) ^ (2 + p) =
      layerDensity ^ (2 + p) / ((2 : ENNReal) ^ (2 + p)) := by
    simp only [div_eq_mul_inv]
    rw [ENNReal.mul_rpow_of_nonneg layerDensity ((2 : ENNReal)⁻¹) h2p_nonneg, h_inv_rpow]
  have h_rpow : (layerDensity / (2 : ENNReal)) ^ (2 + p) ≤ hairDensity ^ (2 + p) :=
    ENNReal.rpow_le_rpow h h2p_nonneg
  rw [h_distrib] at h_rpow
  exact h_rpow

/-!
### ENNReal-to-Real conversion helpers

These wrappers simplify converting ENNReal inequalities and operations
to Real, which is useful for the final constant-absorption step.
-/

/-- Convert `A ≤ B` in ENNReal to `A.toReal ≤ B.toReal`. -/
lemma toReal_le_of_ennreal_le {A B : ENNReal} (hAtop : A ≠ ⊤) (hBtop : B ≠ ⊤)
    (h : A ≤ B) : A.toReal ≤ B.toReal :=
  (ENNReal.toReal_le_toReal hAtop hBtop).mpr h

/-- `(A * B).toReal = A.toReal * B.toReal` when both are finite. -/
lemma toReal_mul {A B : ENNReal} (hAtop : A ≠ ⊤) (hBtop : B ≠ ⊤) :
    (A * B).toReal = A.toReal * B.toReal :=
  ENNReal.toReal_mul

/-- `(A / B).toReal = A.toReal / B.toReal` when both are nonzero and finite. -/
lemma toReal_div {A B : ENNReal} (hA0 : A ≠ 0) (hAtop : A ≠ ⊤)
    (hB0 : B ≠ 0) (hBtop : B ≠ ⊤) :
    (A / B).toReal = A.toReal / B.toReal := by
  have h1 : (A / B).toReal = (A * B⁻¹).toReal := by rfl
  rw [h1, ENNReal.toReal_mul]
  have h2 : (B⁻¹).toReal = (B.toReal)⁻¹ := by
    rw [ENNReal.toReal_inv]
    <;> simp [hB0, hBtop]
  rw [h2]
  <;> field_simp

/-- `(A ^ p).toReal = A.toReal ^ p` for nonzero finite `A`. -/
lemma toReal_rpow {A : ENNReal} (hA0 : A ≠ 0) (hAtop : A ≠ ⊤) (p : ℝ) :
    (A ^ p).toReal = A.toReal ^ p :=
  (ENNReal.toReal_rpow A p).symm

/-- `(realRpowENN δ x).toReal = Real.rpow δ x` for `δ > 0`. -/
lemma toReal_realRpowENN {δ x : ℝ} (hδ : 0 < δ) :
    (Kakeya.realRpowENN δ x).toReal = Real.rpow δ x :=
  Subunit.realRpowENN_toReal hδ

/-- `(ENNReal.ofReal x).toReal = x` for `x ≥ 0`. -/
lemma toReal_ofReal {x : ℝ} (hx : 0 ≤ x) :
    (ENNReal.ofReal x).toReal = x :=
  ENNReal.toReal_ofReal hx

end Kakeya.Assouad
