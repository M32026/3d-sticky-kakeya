import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.ExponentArithmetic

/-!
# Rpow arithmetic helpers for ENNReal

Lemmas for arithmetic with `Kakeya.realRpowENN` values.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- `δ^a / δ^b = δ^(a-b)` in ENNReal. -/
lemma rpow_enn_div {delta a b : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta a / Kakeya.realRpowENN delta b =
    Kakeya.realRpowENN delta (a - b) := by
  have h_pos : ∀ (x : ℝ), 0 < Real.rpow delta x := fun x => Real.rpow_pos_of_pos hdelta x
  have h_ne_top : ∀ (x : ℝ), Kakeya.realRpowENN delta x ≠ ⊤ := by
    intro x; simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
  have h_ne_zero : ∀ (x : ℝ), Kakeya.realRpowENN delta x ≠ 0 := by
    intro x
    have h : 0 < Kakeya.realRpowENN delta x := by
      simpa [Kakeya.realRpowENN] using ENNReal.ofReal_pos.mpr (h_pos x)
    exact h.ne'
  have h_left_top : Kakeya.realRpowENN delta a / Kakeya.realRpowENN delta b ≠ ⊤ :=
    ENNReal.div_ne_top (h_ne_top a) (h_ne_zero b)
  have h_right_top : Kakeya.realRpowENN delta (a - b) ≠ ⊤ := h_ne_top (a - b)
  apply (ENNReal.toReal_eq_toReal_iff' h_left_top h_right_top).mp
  have htr : ∀ (x : ℝ), ENNReal.toReal (Kakeya.realRpowENN delta x) = Real.rpow delta x := by
    intro x
    rw [Kakeya.realRpowENN, ENNReal.toReal_ofReal (h_pos x).le]
  rw [ENNReal.toReal_div, htr a, htr b, htr (a - b)]
  have h_goal : Real.rpow delta a / Real.rpow delta b = Real.rpow delta (a - b) := by
    have h := Real.rpow_sub hdelta a b
    simpa using h.symm
  exact h_goal

/-- `δ^(a+b) = δ^a * δ^b` in ENNReal. -/
lemma rpow_enn_add {delta a b : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta (a + b) =
    Kakeya.realRpowENN delta a * Kakeya.realRpowENN delta b := by
  have h_pos : ∀ (x : ℝ), 0 < Real.rpow delta x := fun x => Real.rpow_pos_of_pos hdelta x
  have h_ne_top : ∀ (x : ℝ), Kakeya.realRpowENN delta x ≠ ⊤ := by
    intro x; simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
  have h_left_top : Kakeya.realRpowENN delta (a + b) ≠ ⊤ := h_ne_top (a + b)
  have h_right_top : Kakeya.realRpowENN delta a * Kakeya.realRpowENN delta b ≠ ⊤ :=
    ENNReal.mul_ne_top (h_ne_top a) (h_ne_top b)
  apply (ENNReal.toReal_eq_toReal_iff' h_left_top h_right_top).mp
  have htr : ∀ (x : ℝ), ENNReal.toReal (Kakeya.realRpowENN delta x) = Real.rpow delta x := by
    intro x
    rw [Kakeya.realRpowENN, ENNReal.toReal_ofReal (h_pos x).le]
  rw [htr (a + b), ENNReal.toReal_mul, htr a, htr b]
  have h_goal : Real.rpow delta (a + b) = Real.rpow delta a * Real.rpow delta b := by
    have h := Real.rpow_add hdelta a b
    simpa using h
  exact h_goal

/-- `(δ^a)⁻¹ = δ^(-a)` in ENNReal. -/
lemma rpow_enn_inv {delta a : ℝ} (hdelta : 0 < delta) :
    (Kakeya.realRpowENN delta a)⁻¹ = Kakeya.realRpowENN delta (-a) := by
  have h1 : (Kakeya.realRpowENN delta a)⁻¹ = 1 / Kakeya.realRpowENN delta a := by
    simp [one_div]
  rw [h1]
  have h2 : (1 : ENNReal) = Kakeya.realRpowENN delta 0 := by
    simp [Kakeya.realRpowENN] <;> norm_num
  rw [h2]
  have h3 : Kakeya.realRpowENN delta 0 / Kakeya.realRpowENN delta a =
      Kakeya.realRpowENN delta (-a) := by
    have h4 := rpow_enn_div hdelta (a := 0) (b := a)
    have h5 : (0 : ℝ) - a = -a := by ring
    rw [h5] at h4
    exact h4
  exact h3

/--
`δ^a / (c * δ^b) = c⁻¹ * δ^(a-b)` in ENNReal, for `c > 0` real.
-/
lemma rpow_enn_div_scale {delta a b : ℝ} {c : ℝ} (hc : 0 < c) (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta a / ((ENNReal.ofReal c) * Kakeya.realRpowENN delta b) =
    (ENNReal.ofReal c)⁻¹ * Kakeya.realRpowENN delta (a - b) := by
  have h_pos : ∀ (x : ℝ), 0 < Real.rpow delta x := fun x => Real.rpow_pos_of_pos hdelta x
  have h_ne_top : ∀ (x : ℝ), Kakeya.realRpowENN delta x ≠ ⊤ := by
    intro x; simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
  have h_ne_zero : ∀ (x : ℝ), Kakeya.realRpowENN delta x ≠ 0 := by
    intro x
    have h : 0 < Kakeya.realRpowENN delta x := by
      simpa [Kakeya.realRpowENN] using ENNReal.ofReal_pos.mpr (h_pos x)
    exact h.ne'
  have hc_enn_pos : 0 < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hc
  have hc_ne_zero : (ENNReal.ofReal c) ≠ 0 := hc_enn_pos.ne'
  have hc_ne_top : (ENNReal.ofReal c) ≠ ⊤ := by simp
  have h_mul_inv : ((ENNReal.ofReal c) * Kakeya.realRpowENN delta b)⁻¹ =
      (ENNReal.ofReal c)⁻¹ * (Kakeya.realRpowENN delta b)⁻¹ := by
    apply ENNReal.mul_inv
    · exact Or.inl hc_ne_zero
    · exact Or.inl hc_ne_top
  calc
    Kakeya.realRpowENN delta a / ((ENNReal.ofReal c) * Kakeya.realRpowENN delta b)
      = (Kakeya.realRpowENN delta a) * (((ENNReal.ofReal c) * Kakeya.realRpowENN delta b)⁻¹) := by
        simp [div_eq_mul_inv] <;> ring
    _ = (Kakeya.realRpowENN delta a) * ((ENNReal.ofReal c)⁻¹ * (Kakeya.realRpowENN delta b)⁻¹) := by
        rw [h_mul_inv]
    _ = (ENNReal.ofReal c)⁻¹ * (Kakeya.realRpowENN delta a / Kakeya.realRpowENN delta b) := by
        simp [div_eq_mul_inv] <;> ring
    _ = (ENNReal.ofReal c)⁻¹ * Kakeya.realRpowENN delta (a - b) := by
        rw [rpow_enn_div hdelta]

/--
`δ^a / (c * δ^b) = c⁻¹ * δ^(a-b)` for a positive finite `ENNReal`
coefficient.
-/
lemma rpow_enn_div_ennreal_scale
    {delta a b : ℝ} {c : ENNReal}
    (hc_pos : 0 < c) (hc_top : c ≠ ⊤)
    (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta a /
        (c * Kakeya.realRpowENN delta b) =
      c⁻¹ * Kakeya.realRpowENN delta (a - b) := by
  have h_mul_inv :
      (c * Kakeya.realRpowENN delta b)⁻¹ =
        c⁻¹ * (Kakeya.realRpowENN delta b)⁻¹ := by
    apply ENNReal.mul_inv
    · exact Or.inl hc_pos.ne'
    · exact Or.inl hc_top
  calc
    Kakeya.realRpowENN delta a /
          (c * Kakeya.realRpowENN delta b)
        = Kakeya.realRpowENN delta a *
            (c * Kakeya.realRpowENN delta b)⁻¹ := by
          simp [div_eq_mul_inv]
    _ = Kakeya.realRpowENN delta a *
          (c⁻¹ * (Kakeya.realRpowENN delta b)⁻¹) := by
        rw [h_mul_inv]
    _ = c⁻¹ *
          (Kakeya.realRpowENN delta a /
            Kakeya.realRpowENN delta b) := by
        simp [div_eq_mul_inv, mul_assoc, mul_comm,
          mul_left_comm]
    _ = c⁻¹ * Kakeya.realRpowENN delta (a - b) := by
        rw [rpow_enn_div hdelta]

end Kakeya.Assouad
