import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Katz-Tao to Frostman conversion helpers

Helper lemmas for the WZ1 final reduction (Theorem 22 → Theorem 22').
Converts cardinality-gated Katz-Tao non-concentration to Frostman
non-concentration, and establishes the small-product vacuous-B bound.
-/

noncomputable section

open Classical Kakeya.Assouad DiscreteSet

namespace Kakeya.Assouad

/--
A Katz-Tao set in the unit ball has cardinality at most `C / δ`.
Evaluate the Katz-Tao bound at `x = 0`, `r = 1`.
-/
lemma katz_tao_card_upper_bound {A : DiscreteSet 2} {delta C : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) (_hC : 0 ≤ C)
    (hA_kt : A.IsKatzTao delta 1 (ENNReal.ofReal C))
    (hA_unit : A.IsInUnitBall) :
    A.enncard ≤ ENNReal.ofReal C / ENNReal.ofReal delta := by
  have h_filter : (A.filter fun y : Point 2 => dist y 0 ≤ 1) = A := by
    apply Finset.filter_true_of_mem
    intro y hy
    exact hA_unit y hy
  have h1 : A.ballCount 0 1 = A.enncard := by
    unfold DiscreteSet.ballCount DiscreteSet.enncard
    rw [h_filter]
  have h2 : A.ballCount 0 1 ≤
      ENNReal.ofReal C * Kakeya.realRpowENN (1 / delta) 1 :=
    hA_kt 0 1 hdelta_one (by norm_num)
  rw [h1] at h2
  have h3 : Kakeya.realRpowENN (1 / delta) 1 = ENNReal.ofReal (1 / delta) := by
    simp [Kakeya.realRpowENN]
  rw [h3] at h2
  have h4 : ENNReal.ofReal (1 / delta) = (ENNReal.ofReal delta)⁻¹ := by
    have h5 : (1 / delta : ℝ) = delta⁻¹ := by
      field_simp [hdelta.ne']
    rw [h5]
    exact ENNReal.ofReal_inv_of_pos hdelta
  rw [h4] at h2
  simpa [div_eq_mul_inv] using h2

/--
Convert Katz-Tao to Frostman when the cardinality is large enough.
`C_kt / δ ≤ C_fr * |A|` is the exact gate.
-/
lemma katz_tao_to_frostman_of_card {A : DiscreteSet 2} {delta : ℝ}
    {C_kt C_fr : ENNReal}
    (hdelta : 0 < delta)
    (hA_kt : A.IsKatzTao delta 1 C_kt)
    (h_card : C_kt / ENNReal.ofReal delta ≤ C_fr * A.enncard) :
    A.IsFrostman delta 1 C_fr := by
  intro x r hδr hr1
  have h_r_nonneg : 0 ≤ r := by linarith
  have h1 : A.ballCount x r ≤ C_kt * Kakeya.realRpowENN (r / delta) 1 :=
    hA_kt x r hδr hr1
  have h2 : Kakeya.realRpowENN (r / delta) 1 = ENNReal.ofReal (r / delta) := by
    simp [Kakeya.realRpowENN]
  rw [h2] at h1
  have h_div : ENNReal.ofReal (r / delta) =
      ENNReal.ofReal r / ENNReal.ofReal delta := by
    have h_eq : (r / delta : ℝ) = r * delta⁻¹ := by
      field_simp [hdelta.ne']
    rw [h_eq]
    have h6 : ENNReal.ofReal (r * delta⁻¹) =
        ENNReal.ofReal r * ENNReal.ofReal (delta⁻¹) := by
      rw [ENNReal.ofReal_mul] ; positivity
    rw [h6, ENNReal.ofReal_inv_of_pos hdelta]
    simp [div_eq_mul_inv]
  rw [h_div] at h1
  have h4 : C_kt * (ENNReal.ofReal r / ENNReal.ofReal delta) =
      (C_kt / ENNReal.ofReal delta) * ENNReal.ofReal r := by
    simp [div_eq_mul_inv] ; ring
  rw [h4] at h1
  have h5 : (C_kt / ENNReal.ofReal delta) * ENNReal.ofReal r ≤
      (C_fr * A.enncard) * ENNReal.ofReal r := by
    gcongr
  have h7 : Kakeya.realRpowENN r 1 = ENNReal.ofReal r := by
    simp [Kakeya.realRpowENN]
  have h6 : (C_fr * A.enncard) * ENNReal.ofReal r =
      C_fr * Kakeya.realRpowENN r 1 * A.enncard := by
    rw [h7]
    simp [mul_assoc] ; ring
  rw [h6] at h5
  exact h1.trans h5

/--
If `|F| · |G₁| · |G₂| < δ^(η-3)`, then no `H` supported on `F × G₁ × G₂`
can satisfy `|H| ≥ δ^(η-3)`. This makes Alternative B vacuously true.
-/
lemma small_product_vacuous_b {F G1 G2 : DiscreteSet 2} {delta eta : ℝ}
    (h_small : F.enncard * G1.enncard * G2.enncard <
        Kakeya.realRpowENN delta (eta - 3)) :
    ∀ (H : Finset (Point2 × Point2 × Point2)),
      (∀ h ∈ H, h.1 ∈ F ∧ h.2.1 ∈ G1 ∧ h.2.2 ∈ G2) →
      Kakeya.realRpowENN delta (eta - 3) ≤ (H.card : ENNReal) → False := by
  intro H h_support h_threshold
  have h_inj : H ⊆ F ×ˢ G1 ×ˢ G2 := by
    intro p hp
    have h := h_support p hp
    simp only [Finset.mem_product] at * ; tauto
  have h_card_nat : H.card ≤ F.card * G1.card * G2.card := by
    have h : H.card ≤ (F ×ˢ G1 ×ˢ G2).card := Finset.card_le_card h_inj
    have h2 : (F ×ˢ G1 ×ˢ G2).card = F.card * G1.card * G2.card := by
      simp [Finset.card_product] ; ring
    rw [h2] at h
    exact h
  have h_card : (H.card : ENNReal) ≤ F.enncard * G1.enncard * G2.enncard := by
    have h9 : (H.card : ENNReal) ≤ ↑(F.card * G1.card * G2.card) := by
      exact_mod_cast h_card_nat
    have h10 : (↑(F.card * G1.card * G2.card) : ENNReal) =
        F.enncard * G1.enncard * G2.enncard := by
      simp [DiscreteSet.enncard]
    rw [h10] at h9
    exact h9
  have h_contra : (H.card : ENNReal) < Kakeya.realRpowENN delta (eta - 3) :=
    h_card.trans_lt h_small
  exact not_le.mpr h_contra h_threshold

/-- Multiplication law for `realRpowENN`: `δ^a * δ^b = δ^(a+b)`. -/
private lemma realRpowENN_mul {delta a b : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta a * Kakeya.realRpowENN delta b =
    Kakeya.realRpowENN delta (a + b) := by
  simp only [Kakeya.realRpowENN]
  have h_pos1 : 0 ≤ Real.rpow delta a := Real.rpow_nonneg (by linarith) _
  have h_pos2 : 0 ≤ Real.rpow delta b := Real.rpow_nonneg (by linarith) _
  have h_nonneg : 0 ≤ delta := by linarith
  have h_rpow : Real.rpow delta a * Real.rpow delta b = Real.rpow delta (a + b) := by
    have h : Real.rpow delta (a + b) = Real.rpow delta a * Real.rpow delta b :=
      Real.rpow_add hdelta a b
    exact h.symm
  have h_mul : ENNReal.ofReal (Real.rpow delta a) * ENNReal.ofReal (Real.rpow delta b) =
      ENNReal.ofReal (Real.rpow delta a * Real.rpow delta b) := by
    rw [ENNReal.ofReal_mul] ; positivity
  have h_goal : ENNReal.ofReal (Real.rpow delta a * Real.rpow delta b) =
      ENNReal.ofReal (Real.rpow delta (a + b)) :=
    congr_arg ENNReal.ofReal h_rpow
  exact h_mul.trans h_goal

/-- Inverse law for `realRpowENN`: `(δ^a)⁻¹ = δ^(-a)`. -/
private lemma realRpowENN_inv {delta a : ℝ} (hdelta : 0 < delta) :
    (Kakeya.realRpowENN delta a)⁻¹ = Kakeya.realRpowENN delta (-a) := by
  simp only [Kakeya.realRpowENN]
  have h_pos : 0 < Real.rpow delta a := Real.rpow_pos_of_pos hdelta a
  have h : (ENNReal.ofReal (Real.rpow delta a))⁻¹ =
      ENNReal.ofReal ((Real.rpow delta a)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos h_pos]
  rw [h]
  have h2 : (Real.rpow delta a)⁻¹ = Real.rpow delta (-a) :=
    (Real.rpow_neg (by linarith) a).symm
  rw [h2]

/-- Division law for `realRpowENN`: `δ^a / δ^b = δ^(a-b)`. -/
private lemma realRpowENN_div {delta a b : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta a / Kakeya.realRpowENN delta b =
    Kakeya.realRpowENN delta (a - b) := by
  have h_div : Kakeya.realRpowENN delta a / Kakeya.realRpowENN delta b =
      Kakeya.realRpowENN delta a * (Kakeya.realRpowENN delta b)⁻¹ := by
    simp [div_eq_mul_inv]
  have h_exp : a + -b = a - b := by ring
  rw [h_div, realRpowENN_inv hdelta, realRpowENN_mul hdelta,
    congr_arg (Kakeya.realRpowENN delta) h_exp]

/--
Paper-specific conversion: Katz-Tao with constant `δ^(-η)` and cardinality
at least `δ^(-1+4η)` implies Frostman with constant `δ^(-5η)`.

This is the exact arithmetic from the WZ1 Theorem 22 → 22' reduction.
-/
lemma katz_tao_to_frostman_pow {A : DiscreteSet 2} {delta eta : ℝ}
    (hdelta : 0 < delta) (_hdelta_one : delta ≤ 1) (_heta : 0 < eta)
    (hA_kt : A.IsKatzTao delta 1 (Kakeya.realRpowENN delta (-eta)))
    (_hA_unit : A.IsInUnitBall)
    (h_large : Kakeya.realRpowENN delta (-1 + 4 * eta) ≤ A.enncard) :
    A.IsFrostman delta 1 (Kakeya.realRpowENN delta (-5 * eta)) := by
  set C_kt : ENNReal := Kakeya.realRpowENN delta (-eta) with hC_kt
  set C_fr : ENNReal := Kakeya.realRpowENN delta (-5 * eta) with hC_fr
  have hdelta_rpow : ENNReal.ofReal delta = Kakeya.realRpowENN delta 1 := by
    simp [Kakeya.realRpowENN, Real.rpow_one]
  have h1 : C_kt / ENNReal.ofReal delta =
      Kakeya.realRpowENN delta (-eta - 1) := by
    rw [hdelta_rpow]
    exact realRpowENN_div hdelta
  have h2 : C_fr * Kakeya.realRpowENN delta (-1 + 4 * eta) =
      Kakeya.realRpowENN delta (-eta - 1) := by
    have h : C_fr * Kakeya.realRpowENN delta (-1 + 4 * eta) =
        Kakeya.realRpowENN delta ((-5 * eta) + (-1 + 4 * eta)) :=
      realRpowENN_mul hdelta
    have h_exp : (-5 * eta) + (-1 + 4 * eta) = -eta - 1 := by ring
    rw [h, congr_arg (Kakeya.realRpowENN delta) h_exp]
  have h_gate : C_kt / ENNReal.ofReal delta ≤ C_fr * A.enncard := by
    rw [h1]
    calc
      Kakeya.realRpowENN delta (-eta - 1)
        = C_fr * Kakeya.realRpowENN delta (-1 + 4 * eta) := h2.symm
      _ ≤ C_fr * A.enncard := by gcongr
  exact katz_tao_to_frostman_of_card hdelta hA_kt h_gate

/--
From a large product `|F| * |G1| * |G2| ≥ δ^{η-3}` and individual upper bounds
`|F|, |G1|, |G2| ≤ δ^{-1-η}`, deduce each set has cardinality at least `δ^{-1+4η}`.

This is the cardinality gate needed for KatzTao→Frostman conversion.
-/
lemma card_lower_from_product
    {delta eta : ℝ} {F G1 G2 : DiscreteSet 2}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) (heta : 0 < eta)
    (hF_upper : F.enncard ≤ Kakeya.realRpowENN delta (-1 - eta))
    (hG1_upper : G1.enncard ≤ Kakeya.realRpowENN delta (-1 - eta))
    (hG2_upper : G2.enncard ≤ Kakeya.realRpowENN delta (-1 - eta))
    (h_product_large : Kakeya.realRpowENN delta (eta - 3) ≤ F.enncard * G1.enncard * G2.enncard) :
    Kakeya.realRpowENN delta (-1 + 4 * eta) ≤ F.enncard ∧
    Kakeya.realRpowENN delta (-1 + 4 * eta) ≤ G1.enncard ∧
    Kakeya.realRpowENN delta (-1 + 4 * eta) ≤ G2.enncard := by
  set U := Kakeya.realRpowENN delta (-1 - eta) with hU_def
  have hU_pos : U ≠ 0 := by
    simp [hU_def, Kakeya.realRpowENN] <;> positivity
  have hU_ne_top : U ≠ ⊤ := by
    simp [hU_def, Kakeya.realRpowENN]
  have h_prod_U : U * U = Kakeya.realRpowENN delta (-2 - 2 * eta) := by
    simp only [hU_def]
    have h := @realRpowENN_mul delta (-1 - eta) (-1 - eta) hdelta
    have h_exp : (-1 - eta) + (-1 - eta) = -2 - 2 * eta := by ring
    rw [h, congr_arg (Kakeya.realRpowENN delta) h_exp]
  have h_exp_le : (3 * eta - 1 : ℝ) ≤ -1 + 4 * eta := by linarith
  have h_rpow_mon : Kakeya.realRpowENN delta (-1 + 4 * eta) ≤ Kakeya.realRpowENN delta (3 * eta - 1) := by
    simp only [Kakeya.realRpowENN]
    have h : Real.rpow delta (-1 + 4 * eta) ≤ Real.rpow delta (3 * eta - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one h_exp_le
    exact ENNReal.ofReal_le_ofReal h
  have h_div : Kakeya.realRpowENN delta (eta - 3) / (U * U) = Kakeya.realRpowENN delta (3 * eta - 1) := by
    rw [h_prod_U]
    have h := @realRpowENN_div delta (eta - 3) (-2 - 2 * eta) hdelta
    have h_exp : (eta - 3) - (-2 - 2 * eta) = 3 * eta - 1 := by ring
    rw [h, congr_arg (Kakeya.realRpowENN delta) h_exp]
  have hG1G2_pos : (G1.enncard * G2.enncard) ≠ 0 := by
    by_contra h
    have h0 : F.enncard * G1.enncard * G2.enncard = 0 := by
      have h_comm : F.enncard * G1.enncard * G2.enncard = F.enncard * (G1.enncard * G2.enncard) := by ring
      rw [h_comm, h, mul_zero]
    have h_pos : (0 : ENNReal) < Kakeya.realRpowENN delta (eta - 3) := by
      simp [Kakeya.realRpowENN] <;> positivity
    rw [h0] at h_product_large
    exact not_le.mpr h_pos h_product_large
  have hG1G2_ne_top : (G1.enncard * G2.enncard) ≠ ⊤ := by
    have h1 : G1.enncard ≠ ⊤ := by
      exact Ne.symm (not_eq_of_beq_eq_false rfl)
    have h2 : G2.enncard ≠ ⊤ := by
      exact Ne.symm (not_eq_of_beq_eq_false rfl)
    exact ENNReal.mul_ne_top h1 h2
  have hF_lower : Kakeya.realRpowENN delta (3 * eta - 1) ≤ F.enncard := by
    have h1 : Kakeya.realRpowENN delta (eta - 3) ≤ F.enncard * (G1.enncard * G2.enncard) := by
      simpa [mul_assoc] using h_product_large
    have h2 : Kakeya.realRpowENN delta (eta - 3) / (G1.enncard * G2.enncard) ≤ F.enncard := by
      rw [ENNReal.div_le_iff hG1G2_pos hG1G2_ne_top]
      exact h1
    have h3 : Kakeya.realRpowENN delta (eta - 3) / (U * U) ≤
        Kakeya.realRpowENN delta (eta - 3) / (G1.enncard * G2.enncard) := by
      gcongr
    rw [h_div] at h3
    exact h3.trans h2
  have hG1_lower : Kakeya.realRpowENN delta (3 * eta - 1) ≤ G1.enncard := by
    have h1 : Kakeya.realRpowENN delta (eta - 3) ≤ G1.enncard * (F.enncard * G2.enncard) := by
      have h_comm : F.enncard * G1.enncard * G2.enncard = G1.enncard * (F.enncard * G2.enncard) := by ring
      rw [h_comm] at h_product_large
      exact h_product_large
    have hFG2_pos : (F.enncard * G2.enncard) ≠ 0 := by
      by_contra h
      have h0 : F.enncard * G1.enncard * G2.enncard = 0 := by
        have h_comm : F.enncard * G1.enncard * G2.enncard = G1.enncard * (F.enncard * G2.enncard) := by ring
        rw [h_comm, h, mul_zero]
      have h_pos : (0 : ENNReal) < Kakeya.realRpowENN delta (eta - 3) := by
        simp [Kakeya.realRpowENN] <;> positivity
      rw [h0] at h_product_large
      exact not_le.mpr h_pos h_product_large
    have hFG2_ne_top : (F.enncard * G2.enncard) ≠ ⊤ := by
      have h1 : F.enncard ≠ ⊤ := by
        exact Ne.symm (not_eq_of_beq_eq_false rfl)
      have h2 : G2.enncard ≠ ⊤ := by
        exact Ne.symm (not_eq_of_beq_eq_false rfl)
      exact ENNReal.mul_ne_top h1 h2
    have h2 : Kakeya.realRpowENN delta (eta - 3) / (F.enncard * G2.enncard) ≤ G1.enncard := by
      rw [ENNReal.div_le_iff hFG2_pos hFG2_ne_top]
      exact h1
    have h3 : Kakeya.realRpowENN delta (eta - 3) / (U * U) ≤
        Kakeya.realRpowENN delta (eta - 3) / (F.enncard * G2.enncard) := by
      gcongr
    rw [h_div] at h3
    exact h3.trans h2
  have hG2_lower : Kakeya.realRpowENN delta (3 * eta - 1) ≤ G2.enncard := by
    have h1 : Kakeya.realRpowENN delta (eta - 3) ≤ G2.enncard * (F.enncard * G1.enncard) := by
      have h_comm : F.enncard * G1.enncard * G2.enncard = G2.enncard * (F.enncard * G1.enncard) := by ring
      rw [h_comm] at h_product_large
      exact h_product_large
    have hFG1_pos : (F.enncard * G1.enncard) ≠ 0 := by
      by_contra h
      have h0 : F.enncard * G1.enncard * G2.enncard = 0 := by
        rw [h, zero_mul]
      have h_pos : (0 : ENNReal) < Kakeya.realRpowENN delta (eta - 3) := by
        simp [Kakeya.realRpowENN] <;> positivity
      rw [h0] at h_product_large
      exact not_le.mpr h_pos h_product_large
    have hFG1_ne_top : (F.enncard * G1.enncard) ≠ ⊤ := by
      have h1 : F.enncard ≠ ⊤ := by
        simp [DiscreteSet.enncard]
      have h2 : G1.enncard ≠ ⊤ := by
        simp [DiscreteSet.enncard]
      exact ENNReal.mul_ne_top h1 h2
    have h2 : Kakeya.realRpowENN delta (eta - 3) / (F.enncard * G1.enncard) ≤ G2.enncard := by
      rw [ENNReal.div_le_iff hFG1_pos hFG1_ne_top]
      exact h1
    have h3 : Kakeya.realRpowENN delta (eta - 3) / (U * U) ≤
        Kakeya.realRpowENN delta (eta - 3) / (F.enncard * G1.enncard) := by
      gcongr
    rw [h_div] at h3
    exact h3.trans h2
  exact ⟨h_rpow_mon.trans hF_lower, h_rpow_mon.trans hG1_lower, h_rpow_mon.trans hG2_lower⟩

end Kakeya.Assouad
