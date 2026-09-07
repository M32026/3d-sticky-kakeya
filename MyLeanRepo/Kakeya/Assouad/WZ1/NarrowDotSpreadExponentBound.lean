import MyLeanRepo.Kakeya.AssertionD
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponent comparison lemma for narrow dot-spread cardinality bound
-/

namespace Kakeya.Assouad

lemma narrow_dot_spread_exponent_bound_strong_input
    {delta epsilon eta workingLambda width : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon < 1)
    (heta : 0 < eta) (hworkingLambda_pos : 0 < workingLambda)
    (hworkingLambda : workingLambda ≤ epsilon / 100)
    (hetaCap : eta ≤ epsilon / 20)
    (_hwidth_pos : 0 < width)
    (hnarrow : width ≤ Real.rpow delta (1 - epsilon / 10))
    (hsmall : (240000 : ℝ) * Real.rpow delta (37 / 50) ≤ 1)
    (M : ℝ) (hM : M ≥ Real.rpow delta (eta + workingLambda - 1 + epsilon / 10) / 30000)
    (D : ℝ) (hD : 0 ≤ D) (hD_le : D ≤ 8 * width) :
    Kakeya.realRpowENN (max D (Real.rpow delta (1 - eta)) / delta) (1 - epsilon)
      ≤ ENNReal.ofReal M := by
  have hM_nonneg : 0 ≤ M := by
    have h_pos : 0 ≤ Real.rpow delta (eta + workingLambda - 1 + epsilon / 10) :=
      Real.rpow_nonneg hdelta.le _
    have h : 0 ≤ Real.rpow delta (eta + workingLambda - 1 + epsilon / 10) / 30000 := by
      apply div_nonneg h_pos <;> norm_num
    exact le_trans h hM

  set X : ℝ := max D (Real.rpow delta (1 - eta)) / delta with hX_def
  have hX_pos : 0 < X := by
    have h1 : 0 < Real.rpow delta (1 - eta) := Real.rpow_pos_of_pos hdelta _
    have h2 : 0 < max D (Real.rpow delta (1 - eta)) := by positivity
    exact div_pos h2 hdelta

  have h_one_minus_eps : 0 < 1 - epsilon := by linarith

  have h_rpow_div : ∀ (a : ℝ), Real.rpow delta a / delta = Real.rpow delta (a - 1) := by
    intro a
    have h1 : Real.rpow delta (a - 1) = Real.rpow delta a / Real.rpow delta 1 :=
      Real.rpow_sub hdelta a 1
    have h2 : Real.rpow delta 1 = delta := by simp
    rw [h2] at h1
    exact h1.symm

  have h_rpow_rpow : ∀ (a b : ℝ), Real.rpow (Real.rpow delta a) b =
      Real.rpow delta (a * b) := by
    intro a b
    have h1 : Real.rpow delta (a * b) = Real.rpow (Real.rpow delta a) b :=
      Real.rpow_mul hdelta.le a b
    exact h1.symm

  have h_rpow_add : ∀ (a b : ℝ), Real.rpow delta (a + b) =
      Real.rpow delta a * Real.rpow delta b := by
    intro a b
    exact Real.rpow_add hdelta a b

  have h_big1 : Real.rpow delta (-37 / 50) ≥ 240000 := by
    have h_pos : 0 < Real.rpow delta (37 / 50) := Real.rpow_pos_of_pos hdelta _
    have h9 : Real.rpow delta (37 / 50) ≤ 1 / 240000 := by
      have h10 : (240000 : ℝ) * Real.rpow delta (37 / 50) ≤ 1 := hsmall
      calc
        Real.rpow delta (37 / 50) =
            ((240000 : ℝ) * Real.rpow delta (37 / 50)) / 240000 := by ring
        _ ≤ 1 / 240000 := by gcongr
    have h_inv : Real.rpow delta (-(37 / 50 : ℝ)) =
        (Real.rpow delta (37 / 50))⁻¹ :=
      Real.rpow_neg hdelta.le (37 / 50)
    have h_eq : Real.rpow delta (-37 / 50) =
        (Real.rpow delta (37 / 50))⁻¹ := by
      convert h_inv using 1 <;> norm_num
    rw [h_eq]
    have h12 : (Real.rpow delta (37 / 50))⁻¹ ≥ 240000 := by
      calc
        (Real.rpow delta (37 / 50))⁻¹ ≥ (1 / 240000 : ℝ)⁻¹ := by gcongr
        _ = 240000 := by norm_num
    exact h12

  have h_big2 : Real.rpow delta (-79 / 100) ≥ 30000 := by
    have h1 : (-79 / 100 : ℝ) ≤ (-37 / 50 : ℝ) := by norm_num
    have h2 : Real.rpow delta (-79 / 100) ≥ Real.rpow delta (-37 / 50) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne h1
    linarith [h_big1]

  have h_main_real : Real.rpow X (1 - epsilon) ≤ M := by
    by_cases h_case : D ≥ Real.rpow delta (1 - eta)
    · have hmax : max D (Real.rpow delta (1 - eta)) = D := by
        rw [max_eq_left] <;> linarith
      have hX_eq : X = D / delta := by
        rw [hX_def, hmax]
      rw [hX_eq]

      have hD_div_le : D / delta ≤ 8 * Real.rpow delta (-epsilon / 10) := by
        calc
          D / delta ≤ (8 * width) / delta := by gcongr
          _ = 8 * (width / delta) := by ring
          _ ≤ 8 * (Real.rpow delta (1 - epsilon / 10) / delta) := by gcongr
          _ = 8 * Real.rpow delta (-epsilon / 10) := by
            rw [h_rpow_div (1 - epsilon / 10)] <;> ring

      have h_pos_arg : 0 ≤ D / delta := by positivity
      have hX_le : Real.rpow (D / delta) (1 - epsilon) ≤
          Real.rpow (8 * Real.rpow delta (-epsilon / 10)) (1 - epsilon) := by
        apply Real.rpow_le_rpow h_pos_arg
        <;> linarith

      have h_pos1 : 0 < (8 : ℝ) := by norm_num
      have h_pos2 : 0 < Real.rpow delta (-epsilon / 10) :=
        Real.rpow_pos_of_pos hdelta _
      have h_mul_rpow :
          Real.rpow (8 * Real.rpow delta (-epsilon / 10)) (1 - epsilon) =
            (8 : ℝ) ^ (1 - epsilon) *
              Real.rpow (Real.rpow delta (-epsilon / 10)) (1 - epsilon) := by
        exact Real.mul_rpow (by norm_num) (by positivity)
      rw [h_mul_rpow] at hX_le

      have h4 :
          Real.rpow (Real.rpow delta (-epsilon / 10)) (1 - epsilon) =
            Real.rpow delta (-epsilon * (1 - epsilon) / 10) := by
        rw [h_rpow_rpow (-epsilon / 10) (1 - epsilon)] <;> ring
      rw [h4] at hX_le

      have h_exp1 :
          eta + workingLambda - 1 + epsilon / 5 - epsilon ^ 2 / 10 ≤
            -37 / 50 := by
        have h_eps2 : 0 ≤ epsilon ^ 2 / 10 := by positivity
        have h1 :
            eta + workingLambda - 1 + epsilon / 5 - epsilon ^ 2 / 10 ≤
              epsilon / 20 + epsilon / 100 - 1 + epsilon / 5 := by
          linarith [hetaCap, hworkingLambda, h_eps2]
        have h2 :
            epsilon / 20 + epsilon / 100 - 1 + epsilon / 5 ≤ -37 / 50 := by
          have h3 : epsilon ≤ 1 := by linarith
          linarith
        linarith

      have h_rpow1 :
          Real.rpow delta
              (eta + workingLambda - 1 + epsilon / 5 - epsilon ^ 2 / 10) ≥
            Real.rpow delta (-37 / 50) :=
        Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne h_exp1

      have h8_le : (8 : ℝ) ^ (1 - epsilon) ≤ 8 := by
        have h1 : 1 - epsilon ≤ 1 := by linarith
        have h2 : (1 : ℝ) ≤ 8 := by norm_num
        have h3 : (8 : ℝ) ^ (1 - epsilon) ≤ (8 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h2 h1
        simpa using h3

      have h_key :
          (30000 : ℝ) * (8 : ℝ) ^ (1 - epsilon) ≤
            Real.rpow delta
              (eta + workingLambda - 1 + epsilon / 5 - epsilon ^ 2 / 10) := by
        calc
          (30000 : ℝ) * (8 : ℝ) ^ (1 - epsilon)
              ≤ (30000 : ℝ) * 8 := by gcongr
          _ = 240000 := by norm_num
          _ ≤ Real.rpow delta (-37 / 50) := h_big1
          _ ≤ Real.rpow delta
              (eta + workingLambda - 1 + epsilon / 5 - epsilon ^ 2 / 10) :=
            h_rpow1

      set E1 := eta + workingLambda - 1 + epsilon / 5 - epsilon ^ 2 / 10
        with hE1_def
      set c1 := -epsilon * (1 - epsilon) / 10 with hc1_def
      have h_sum1 : E1 + c1 = eta + workingLambda - 1 + epsilon / 10 := by
        simp [hE1_def, hc1_def] <;> ring

      have h_pos_c1 : 0 < Real.rpow delta c1 := Real.rpow_pos_of_pos hdelta _
      have h_ineq1 :
          (30000 : ℝ) *
              ((8 : ℝ) ^ (1 - epsilon) * Real.rpow delta c1) ≤
            Real.rpow delta (eta + workingLambda - 1 + epsilon / 10) := by
        calc
          (30000 : ℝ) *
                ((8 : ℝ) ^ (1 - epsilon) * Real.rpow delta c1) =
              ((30000 : ℝ) * (8 : ℝ) ^ (1 - epsilon)) *
                Real.rpow delta c1 := by ring
          _ ≤ Real.rpow delta E1 * Real.rpow delta c1 := by gcongr
          _ = Real.rpow delta (E1 + c1) := by rw [h_rpow_add E1 c1]
          _ = Real.rpow delta (eta + workingLambda - 1 + epsilon / 10) := by
            rw [h_sum1]

      have h_final1 :
          (8 : ℝ) ^ (1 - epsilon) * Real.rpow delta c1 ≤
            Real.rpow delta (eta + workingLambda - 1 + epsilon / 10) /
              30000 := by
        calc
          (8 : ℝ) ^ (1 - epsilon) * Real.rpow delta c1 =
              ((30000 : ℝ) *
                ((8 : ℝ) ^ (1 - epsilon) * Real.rpow delta c1)) /
                30000 := by ring
          _ ≤ Real.rpow delta (eta + workingLambda - 1 + epsilon / 10) /
                30000 := by gcongr

      have h_goal :
          Real.rpow (D / delta) (1 - epsilon) ≤
            (8 : ℝ) ^ (1 - epsilon) * Real.rpow delta c1 := by
        simpa [hc1_def] using hX_le

      calc
        Real.rpow (D / delta) (1 - epsilon)
            ≤ (8 : ℝ) ^ (1 - epsilon) * Real.rpow delta c1 := h_goal
        _ ≤ Real.rpow delta (eta + workingLambda - 1 + epsilon / 10) /
              30000 := h_final1
        _ ≤ M := hM

    · have hmax :
          max D (Real.rpow delta (1 - eta)) =
            Real.rpow delta (1 - eta) := by
        rw [max_eq_right] <;> linarith
      have hX_eq : X = Real.rpow delta (-eta) := by
        rw [hX_def, hmax]
        rw [h_rpow_div (1 - eta)] <;> ring
      rw [hX_eq]

      have h_rpow_neg :
          Real.rpow (Real.rpow delta (-eta)) (1 - epsilon) =
            Real.rpow delta (-eta * (1 - epsilon)) := by
        rw [h_rpow_rpow (-eta) (1 - epsilon)]
      rw [h_rpow_neg]

      have h_exp2 :
          2 * eta + workingLambda - 1 + epsilon / 10 - eta * epsilon ≤
            -79 / 100 := by
        have h_eta_eps : 0 ≤ eta * epsilon := by positivity
        have h1 :
            2 * eta + workingLambda - 1 + epsilon / 10 - eta * epsilon ≤
              2 * eta + workingLambda - 1 + epsilon / 10 := by linarith
        have h2 : 2 * eta ≤ epsilon / 10 := by linarith [hetaCap]
        have h3 :
            2 * eta + workingLambda - 1 + epsilon / 10 ≤
              epsilon / 10 + epsilon / 100 - 1 + epsilon / 10 := by
          linarith [hworkingLambda]
        have h4 :
            epsilon / 10 + epsilon / 100 - 1 + epsilon / 10 ≤
              -79 / 100 := by
          have h5 : epsilon ≤ 1 := by linarith
          linarith
        linarith

      have h_rpow2 :
          Real.rpow delta
              (2 * eta + workingLambda - 1 + epsilon / 10 - eta * epsilon) ≥
            Real.rpow delta (-79 / 100) :=
        Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne h_exp2

      set E2 := 2 * eta + workingLambda - 1 + epsilon / 10 - eta * epsilon
        with hE2_def
      set c2 := -eta * (1 - epsilon) with hc2_def
      have h_sum2 : E2 + c2 = eta + workingLambda - 1 + epsilon / 10 := by
        simp [hE2_def, hc2_def] <;> ring

      have h_key2 : (30000 : ℝ) ≤ Real.rpow delta E2 := by
        calc
          (30000 : ℝ) ≤ Real.rpow delta (-79 / 100) := h_big2
          _ ≤ Real.rpow delta E2 := h_rpow2

      have h_nonneg_c2 : 0 ≤ Real.rpow delta c2 :=
        Real.rpow_nonneg hdelta.le c2
      have h_ineq2 :
          (30000 : ℝ) * Real.rpow delta c2 ≤
            Real.rpow delta (eta + workingLambda - 1 + epsilon / 10) := by
        calc
          (30000 : ℝ) * Real.rpow delta c2
              ≤ Real.rpow delta E2 * Real.rpow delta c2 := by gcongr
          _ = Real.rpow delta (E2 + c2) := by rw [h_rpow_add E2 c2]
          _ = Real.rpow delta (eta + workingLambda - 1 + epsilon / 10) := by
            rw [h_sum2]

      have h_final2 :
          Real.rpow delta c2 ≤
            Real.rpow delta (eta + workingLambda - 1 + epsilon / 10) /
              30000 := by
        calc
          Real.rpow delta c2 =
              ((30000 : ℝ) * Real.rpow delta c2) / 30000 := by ring
          _ ≤ Real.rpow delta (eta + workingLambda - 1 + epsilon / 10) /
                30000 := by gcongr

      simpa [hc2_def] using h_final2.trans hM

  have h_nonneg' : 0 ≤ Real.rpow X (1 - epsilon) :=
    Real.rpow_nonneg hX_pos.le _
  have h_final :
      ENNReal.ofReal (Real.rpow X (1 - epsilon)) ≤ ENNReal.ofReal M :=
    ENNReal.ofReal_le_ofReal h_main_real
  simpa [Kakeya.realRpowENN, hX_def] using h_final

lemma narrow_dot_spread_exponent_bound
    {delta epsilon eta workingLambda width : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon < 1)
    (heta : 0 < eta)
    (hworkingLambda : workingLambda ≤ epsilon / 100)
    (hetaCap : eta ≤ epsilon / 20)
    (hnarrow : width ≤ Real.rpow delta (1 - epsilon / 10))
    (hsmall :
      (1200000 : ℝ) *
          Real.rpow delta (7 * epsilon / 10) ≤ 1)
    (M : ℝ)
    (hM :
      Real.rpow delta
          (eta + workingLambda - 9 * epsilon / 10) /
          147456 ≤
        M)
    (D : ℝ) (_hD : 0 ≤ D) (hD_le : D ≤ 8 * width) :
    Kakeya.realRpowENN
        (max D (Real.rpow delta (1 - eta)) / delta)
        (1 - epsilon) ≤
      ENNReal.ofReal M := by
  have hM_nonneg : 0 ≤ M := by
    exact
      (div_nonneg (Real.rpow_nonneg hdelta.le _) (by norm_num)).trans hM
  set A : ℝ :=
    eta + workingLambda - 9 * epsilon / 10 with hA_def
  set X : ℝ :=
    max D (Real.rpow delta (1 - eta)) / delta with hX_def
  have hX_pos : 0 < X := by
    have hmax : 0 < max D (Real.rpow delta (1 - eta)) :=
      lt_max_of_lt_right (Real.rpow_pos_of_pos hdelta _)
    exact div_pos hmax hdelta
  have honeMinus : 0 < 1 - epsilon := by
    linarith
  have hpowEight : (8 : ℝ) ^ (1 - epsilon) ≤ 8 := by
    have hbase : (1 : ℝ) ≤ 8 := by norm_num
    have hexponent : 1 - epsilon ≤ 1 := by linarith
    simpa using
      Real.rpow_le_rpow_of_exponent_le hbase hexponent
  have hconstant :
      (147456 : ℝ) * (8 : ℝ) ^ (1 - epsilon) ≤
        1200000 := by
    calc
      (147456 : ℝ) * (8 : ℝ) ^ (1 - epsilon)
          ≤ 147456 * 8 := by gcongr
      _ ≤ 1200000 := by norm_num
  have h_rpow_div (exponent : ℝ) :
      Real.rpow delta exponent / delta =
        Real.rpow delta (exponent - 1) := by
    have h := Real.rpow_sub hdelta exponent 1
    simpa using h.symm
  have h_main_real : Real.rpow X (1 - epsilon) ≤ M := by
    by_cases hcase :
        D ≥ Real.rpow delta (1 - eta)
    · have hmax :
          max D (Real.rpow delta (1 - eta)) = D :=
        max_eq_left hcase
      have hX : X = D / delta := by
        rw [hX_def, hmax]
      have hratio :
          D / delta ≤
            8 * Real.rpow delta (-epsilon / 10) := by
        calc
          D / delta ≤ (8 * width) / delta := by gcongr
          _ ≤
              (8 * Real.rpow delta (1 - epsilon / 10)) /
                delta := by gcongr
          _ =
              8 *
                (Real.rpow delta (1 - epsilon / 10) /
                  delta) := by ring
          _ = 8 * Real.rpow delta (-epsilon / 10) := by
            rw [h_rpow_div (1 - epsilon / 10)]
            ring_nf
      have hpower :
          Real.rpow X (1 - epsilon) ≤
            Real.rpow
              (8 * Real.rpow delta (-epsilon / 10))
              (1 - epsilon) := by
        apply Real.rpow_le_rpow hX_pos.le
        · simpa [hX] using hratio
        · exact honeMinus.le
      have hmul :
          Real.rpow
              (8 * Real.rpow delta (-epsilon / 10))
              (1 - epsilon) =
            Real.rpow 8 (1 - epsilon) *
              Real.rpow delta
                ((-epsilon / 10) * (1 - epsilon)) := by
        calc
          Real.rpow
              (8 * Real.rpow delta (-epsilon / 10))
              (1 - epsilon) =
            Real.rpow 8 (1 - epsilon) *
              Real.rpow
                (Real.rpow delta (-epsilon / 10))
                (1 - epsilon) := by
              exact
                Real.mul_rpow
                  (by norm_num)
                  (Real.rpow_nonneg hdelta.le _)
          _ =
            Real.rpow 8 (1 - epsilon) *
              Real.rpow delta
                ((-epsilon / 10) * (1 - epsilon)) := by
              have hinner :
                  Real.rpow
                      (Real.rpow delta (-epsilon / 10))
                      (1 - epsilon) =
                    Real.rpow delta
                      ((-epsilon / 10) * (1 - epsilon)) :=
                (Real.rpow_mul hdelta.le
                  (-epsilon / 10) (1 - epsilon)).symm
              rw [hinner]
      rw [hmul] at hpower
      set B : ℝ :=
        (-epsilon / 10) * (1 - epsilon) with hB_def
      have hgap : 7 * epsilon / 10 ≤ B - A := by
        dsimp only [B, A]
        nlinarith
      have hgapPower :
          Real.rpow delta (B - A) ≤
            Real.rpow delta (7 * epsilon / 10) :=
        Real.rpow_le_rpow_of_exponent_ge
          hdelta hdeltaOne hgap
      have hgap_nonneg :
          0 ≤ Real.rpow delta (B - A) :=
        Real.rpow_nonneg hdelta.le _
      have hconstantGap :
          (147456 : ℝ) * Real.rpow 8 (1 - epsilon) *
              Real.rpow delta (B - A) ≤
            1 := by
        calc
          (147456 : ℝ) * Real.rpow 8 (1 - epsilon) *
                Real.rpow delta (B - A)
              ≤ 1200000 *
                Real.rpow delta (7 * epsilon / 10) :=
            mul_le_mul hconstant hgapPower
              hgap_nonneg (by positivity)
          _ ≤ 1 := hsmall
      have hApos : 0 < Real.rpow delta A :=
        Real.rpow_pos_of_pos hdelta _
      have hBA :
          Real.rpow delta B =
            Real.rpow delta A *
              Real.rpow delta (B - A) := by
        calc
          Real.rpow delta B =
              Real.rpow delta (A + (B - A)) := by
            congr 1
            ring
          _ =
              Real.rpow delta A *
                Real.rpow delta (B - A) :=
            Real.rpow_add hdelta A (B - A)
      have hscaled :
          Real.rpow 8 (1 - epsilon) *
              Real.rpow delta B ≤
            Real.rpow delta A / 147456 := by
        rw [hBA]
        apply
          (le_div_iff₀
            (by norm_num : (0 : ℝ) < 147456)).2
        calc
          Real.rpow 8 (1 - epsilon) *
                (Real.rpow delta A *
                  Real.rpow delta (B - A)) *
                147456 =
              Real.rpow delta A *
                ((147456 : ℝ) * Real.rpow 8 (1 - epsilon) *
                  Real.rpow delta (B - A)) := by ring
          _ ≤ Real.rpow delta A * 1 := by gcongr
          _ = Real.rpow delta A := by ring
      calc
        Real.rpow X (1 - epsilon)
            ≤ Real.rpow 8 (1 - epsilon) *
                Real.rpow delta B := by
          simpa [B] using hpower
        _ ≤ Real.rpow delta A / 147456 := hscaled
        _ ≤ M := by simpa [A] using hM
    · have hmax :
          max D (Real.rpow delta (1 - eta)) =
            Real.rpow delta (1 - eta) :=
        max_eq_right (le_of_not_ge hcase)
      have hX :
          X = Real.rpow delta (-eta) := by
        rw [hX_def, hmax, h_rpow_div (1 - eta)]
        ring_nf
      set B : ℝ := -eta * (1 - epsilon) with hB_def
      have hpower :
          Real.rpow X (1 - epsilon) =
            Real.rpow delta B := by
        rw [hX]
        simpa [B] using
          (Real.rpow_mul hdelta.le
            (-eta) (1 - epsilon)).symm
      have hgap : 7 * epsilon / 10 ≤ B - A := by
        dsimp only [B, A]
        nlinarith
      have hgapPower :
          Real.rpow delta (B - A) ≤
            Real.rpow delta (7 * epsilon / 10) :=
        Real.rpow_le_rpow_of_exponent_ge
          hdelta hdeltaOne hgap
      have hgap_nonneg :
          0 ≤ Real.rpow delta (B - A) :=
        Real.rpow_nonneg hdelta.le _
      have hconstantGap :
          (147456 : ℝ) * Real.rpow delta (B - A) ≤ 1 := by
        calc
          (147456 : ℝ) * Real.rpow delta (B - A)
              ≤ 1200000 *
                Real.rpow delta (7 * epsilon / 10) :=
            mul_le_mul (by norm_num) hgapPower
              hgap_nonneg (by norm_num)
          _ ≤ 1 := hsmall
      have hBA :
          Real.rpow delta B =
            Real.rpow delta A *
              Real.rpow delta (B - A) := by
        calc
          Real.rpow delta B =
              Real.rpow delta (A + (B - A)) := by
            congr 1
            ring
          _ =
              Real.rpow delta A *
                Real.rpow delta (B - A) :=
            Real.rpow_add hdelta A (B - A)
      have hscaled :
          Real.rpow delta B ≤
            Real.rpow delta A / 147456 := by
        rw [hBA]
        apply
          (le_div_iff₀
            (by norm_num : (0 : ℝ) < 147456)).2
        have hA_nonneg : 0 ≤ Real.rpow delta A :=
          Real.rpow_nonneg hdelta.le _
        calc
          Real.rpow delta A * Real.rpow delta (B - A) *
                147456 =
              Real.rpow delta A *
                ((147456 : ℝ) * Real.rpow delta (B - A)) := by
            ring
          _ ≤ Real.rpow delta A * 1 :=
            mul_le_mul_of_nonneg_left hconstantGap hA_nonneg
          _ = Real.rpow delta A := by ring
      rw [hpower]
      exact hscaled.trans (by simpa [A] using hM)
  have hfinal :
      ENNReal.ofReal (Real.rpow X (1 - epsilon)) ≤
        ENNReal.ofReal M :=
    ENNReal.ofReal_le_ofReal h_main_real
  simpa [Kakeya.realRpowENN, X] using hfinal

end Kakeya.Assouad
