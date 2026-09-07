import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Subunit.AsymptoticHelper

/-!
# Local robust-hairbrush numerical closure

Pure algebra from (B.28) and the incidence identity (B.13) to (B.29).
Multiply the supplied hard hairbrush lower bound by the supplied incidence
upper identity, cancel the finite positive multiplicity, and take square
roots by squaring the goal.  Polynomial losses in both constants and the
density lower bound are explicit inputs.

No geometric object is constructed in this target.

## Proof outline

Let `δE x := Kakeya.realRpowENN δ x`, `θ := ENNReal.ofReal theta`, and
`E2 := hairbrushExponent + 2 + 2*constantLoss + densityExponent*(densityPower+1)`.

1. Multiply the hard bound and incidence identity, cancel `mu`:
   `δE(hairbrushExponent+2) * hairbrushConstant * θ * density^(densityPower+1) * N
     ≤ incidenceUpper * V * V`.
2. Lower-bound `hairbrushConstant ≥ δE constantLoss` and
   `density^(densityPower+1) ≥ δE(densityExponent*(densityPower+1))`.
3. Upper-bound `incidenceUpper ≤ δE(-constantLoss)`.
4. Obtain `δE E2 * θ * N ≤ V * V`.
5. Square the goal `G := δE(3/2+outputLoss) * sqrt(theta) * N^(1/2)`:
   `G*G = δE(3+2*outputLoss) * θ * N`.
6. Since `E2/2 < 3/2+outputLoss` and `0 < δ ≤ 1`, we have
   `δE(3+2*outputLoss) ≤ δE E2`, so `G*G ≤ V*V`.
7. Monotonicity of `ENNReal.rpow` with positive exponent gives `G ≤ V`.

Choose `delta₀ = 1/1000`; no further shrinking is needed.
-/

namespace Kakeya.Assouad

theorem hairbrush_local_numerical_closure :
    HairbrushLocalNumericalClosureStatement := by
  intro densityExponent hairbrushExponent densityPower constantLoss outputLoss
    hde hdp hhe hcl hmain
  use 1 / 1000
  constructor
  · norm_num
  constructor
  · norm_num
  intro δ hδ hδ₀ theta htheta htheta1 N mu hN0 hNtop hmu0 hmutop density V hd0 hdt hVtop h_density
    incidenceUpper hairbrushConstant hIU0 hIUtop hHC0 hHCtop h_incidenceUpper h_hairbrushConstant
    h_hard h_incidence

  set δE := fun x : ℝ => Kakeya.realRpowENN δ x with hδE_def
  set θ : ENNReal := ENNReal.ofReal theta with hθ_def
  set E2 : ℝ := hairbrushExponent + 2 + densityExponent * (densityPower + 1) + 2 * constantLoss
    with hE2_def
  set G : ENNReal := δE (3 / 2 + outputLoss) * ENNReal.ofReal (Real.sqrt theta) *
                     ENNReal.rpow N (1 / 2) with hG_def

  have hδ1 : δ ≤ 1 := by linarith
  have hE2_le : E2 ≤ 3 + 2 * outputLoss := by
    simp only [hE2_def] at *; linarith

  -- δE (3 + 2 * outputLoss) ≤ δE E2  (since δ ≤ 1 and E2 ≤ 3+2*outputLoss)
  have h_exp_cmp : δE (3 + 2 * outputLoss) ≤ δE E2 := by
    rw [Subunit.realRpowENN_le_iff hδ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hE2_le

  -- ENNReal.ofReal (δ ^ 2) = δE 2
  have hδ2 : ENNReal.ofReal (δ ^ 2) = δE 2 := by
    simp [hδE_def, Kakeya.realRpowENN]

  -- density^densityPower * density = density^(densityPower + 1)
  have h_dens_pow : ENNReal.rpow density densityPower * density =
                    ENNReal.rpow density (densityPower + 1) := by
    have h_add : ENNReal.rpow density (densityPower + 1) =
                 ENNReal.rpow density densityPower * ENNReal.rpow density 1 :=
      ENNReal.rpow_add (y := densityPower) (z := 1) hd0 hdt
    have h1 : ENNReal.rpow density 1 = density := by simp
    rw [h_add, h1]

  -- Step 1: Multiply hard and incidence inequalities
  have h1 : (δE hairbrushExponent * hairbrushConstant * θ *
             ENNReal.rpow density densityPower * mu) *
            (density * N * ENNReal.ofReal (δ ^ 2)) ≤
            V * (incidenceUpper * mu * V) :=
    mul_le_mul' h_hard h_incidence

  rw [hδ2] at h1

  -- Rearrange LHS
  have h_lhs : (δE hairbrushExponent * hairbrushConstant * θ *
                ENNReal.rpow density densityPower * mu) *
               (density * N * δE 2) =
               δE (hairbrushExponent + 2) * hairbrushConstant * θ *
               ENNReal.rpow density (densityPower + 1) * mu * N := by
    calc
      _ = δE hairbrushExponent * δE 2 * hairbrushConstant * θ *
            (ENNReal.rpow density densityPower * density) * mu * N := by ac_rfl
      _ = δE (hairbrushExponent + 2) * hairbrushConstant * θ *
            ENNReal.rpow density (densityPower + 1) * mu * N := by
          rw [Subunit.realRpowENN_mul hδ, h_dens_pow]

  -- Rearrange RHS
  have h_rhs : V * (incidenceUpper * mu * V) = incidenceUpper * mu * (V * V) := by
    ac_rfl

  rw [h_lhs, h_rhs] at h1

  -- Step 2: Cancel mu
  set A : ENNReal := δE (hairbrushExponent + 2) * hairbrushConstant *
                     ENNReal.rpow density (densityPower + 1) * θ * N with hA_def
  set B : ENNReal := incidenceUpper * (V * V) with hB_def

  have h2 : A * mu ≤ B * mu := by
    simpa [hA_def, hB_def, mul_assoc, mul_comm, mul_left_comm] using h1

  have h3 : A ≤ B := by
    have h4 : (A * mu) * mu⁻¹ ≤ (B * mu) * mu⁻¹ := by gcongr
    have h5 : (A * mu) * mu⁻¹ = A := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hmu0 hmutop, mul_one]
    have h6 : (B * mu) * mu⁻¹ = B := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hmu0 hmutop, mul_one]
    rw [h5, h6] at h4
    exact h4

  -- Step 3: Lower bound density^(densityPower+1)
  have hdp1_nonneg : 0 ≤ densityPower + 1 := by linarith
  have h_dens_pow_lb : δE (densityExponent * (densityPower + 1)) ≤
                       ENNReal.rpow density (densityPower + 1) := by
    have h1 : δE densityExponent ≤ density := h_density
    have h2 : ENNReal.rpow (δE densityExponent) (densityPower + 1) ≤
              ENNReal.rpow density (densityPower + 1) :=
      ENNReal.rpow_le_rpow h1 hdp1_nonneg
    have h3 : ENNReal.rpow (δE densityExponent) (densityPower + 1) =
              δE (densityExponent * (densityPower + 1)) := by
      simp [hδE_def, Kakeya.realRpowENN,
            ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hδ densityExponent)]
      rw [Real.rpow_mul (show 0 ≤ δ by linarith)]
    rw [h3] at h2
    exact h2

  -- Step 4: Build lower bound A_lb and show A_lb ≤ A
  set A_lb : ENNReal := δE (hairbrushExponent + 2 + constantLoss +
                            densityExponent * (densityPower + 1)) * θ * N with hA_lb_def

  have hA_lb_le_A : A_lb ≤ A := by
    simp only [hA_def, hA_lb_def]
    have h_expand : δE (hairbrushExponent + 2 + constantLoss +
                        densityExponent * (densityPower + 1)) =
                    δE (hairbrushExponent + 2) * δE constantLoss *
                    δE (densityExponent * (densityPower + 1)) := by
      rw [Subunit.realRpowENN_mul hδ, Subunit.realRpowENN_mul hδ]
    rw [h_expand]
    gcongr

  -- Step 5: Upper bound B
  have hB_ub : B ≤ δE (-constantLoss) * (V * V) := by
    simp only [hB_def]
    have h : incidenceUpper * (V * V) ≤ δE (-constantLoss) * (V * V) := by
      apply mul_le_mul'
      · exact h_incidenceUpper
      · exact le_refl _
    exact h

  -- Step 6: Combine and multiply by δE constantLoss
  have h5 : A_lb ≤ δE (-constantLoss) * (V * V) := by
    calc A_lb ≤ A := hA_lb_le_A
         _ ≤ B := h3
         _ ≤ δE (-constantLoss) * (V * V) := hB_ub

  have h6 : A_lb * δE constantLoss ≤
            (δE (-constantLoss) * (V * V)) * δE constantLoss := by gcongr

  have h_delta_sum : hairbrushExponent + 2 + constantLoss +
                     densityExponent * (densityPower + 1) + constantLoss = E2 := by
    simp only [hE2_def]; ring

  have h7 : A_lb * δE constantLoss = δE E2 * θ * N := by
    simp only [hA_lb_def]
    have h_rearr : (δE (hairbrushExponent + 2 + constantLoss +
                        densityExponent * (densityPower + 1)) * θ * N) * δE constantLoss =
                   (δE (hairbrushExponent + 2 + constantLoss +
                        densityExponent * (densityPower + 1)) * δE constantLoss) * θ * N := by
      ac_rfl
    rw [h_rearr, Subunit.realRpowENN_mul hδ, h_delta_sum]

  have h_delta_inv : δE (-constantLoss) * δE constantLoss = 1 := by
    rw [Subunit.realRpowENN_mul hδ]
    have h10 : -constantLoss + constantLoss = 0 := by ring
    rw [h10]
    simp [Kakeya.realRpowENN, Real.rpow_zero]

  have h8 : (δE (-constantLoss) * (V * V)) * δE constantLoss = V * V := by
    calc
      _ = δE (-constantLoss) * δE constantLoss * (V * V) := by ac_rfl
      _ = 1 * (V * V) := by rw [h_delta_inv]
      _ = V * V := by simp

  rw [h7, h8] at h6

  -- Now h6 : δE E2 * θ * N ≤ V * V

  -- Step 7: Compute G * G
  have hθ_sqrt : ENNReal.ofReal (Real.sqrt theta) * ENNReal.ofReal (Real.sqrt theta) = θ := by
    have hpos : 0 ≤ Real.sqrt theta := by positivity
    have h1 : ENNReal.ofReal (Real.sqrt theta) * ENNReal.ofReal (Real.sqrt theta) =
              ENNReal.ofReal ((Real.sqrt theta) * (Real.sqrt theta)) := by
      rw [← ENNReal.ofReal_mul hpos]
    rw [h1]
    have h2 : (Real.sqrt theta) * (Real.sqrt theta) = theta := by
      rw [Real.mul_self_sqrt (by linarith)]
    rw [h2, hθ_def]

  have hN_sqrt : ENNReal.rpow N (1 / 2) * ENNReal.rpow N (1 / 2) = N := by
    have h1 : ENNReal.rpow N ((1 / 2 : ℝ) + (1 / 2 : ℝ)) =
              ENNReal.rpow N (1 / 2) * ENNReal.rpow N (1 / 2) :=
      ENNReal.rpow_add (y := (1 / 2 : ℝ)) (z := (1 / 2 : ℝ)) hN0 hNtop
    have h2 : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
    have h3 : ENNReal.rpow N 1 = N := by simp
    rw [h2] at h1
    rw [h3] at h1
    exact h1.symm

  have hG2 : G * G = δE (3 + 2 * outputLoss) * θ * N := by
    simp only [hG_def]
    calc
      _ = (δE (3 / 2 + outputLoss) * δE (3 / 2 + outputLoss)) *
          (ENNReal.ofReal (Real.sqrt theta) * ENNReal.ofReal (Real.sqrt theta)) *
          (ENNReal.rpow N (1 / 2) * ENNReal.rpow N (1 / 2)) := by ac_rfl
      _ = δE (3 + 2 * outputLoss) * θ * N := by
            have h_exp : (3 / 2 + outputLoss) + (3 / 2 + outputLoss) = 3 + 2 * outputLoss := by ring
            rw [Subunit.realRpowENN_mul hδ, h_exp, hθ_sqrt, hN_sqrt]

  -- Step 8: G * G ≤ V * V
  have h9 : G * G ≤ V * V := by
    calc G * G = δE (3 + 2 * outputLoss) * θ * N := hG2
         _ ≤ δE E2 * θ * N := by gcongr
         _ ≤ V * V := h6

  -- Step 9: G ≤ V  (from G^2 ≤ V^2, since rpow with positive exponent reflects order)
  have h10 : G ≤ V := by
    have h11 : G ^ (2 : ℝ) ≤ V ^ (2 : ℝ) := by
      have h12 : G ^ (2 : ℝ) = G * G := by
        rw [ENNReal.rpow_two]; simp [pow_two]
      have h13 : V ^ (2 : ℝ) = V * V := by
        rw [ENNReal.rpow_two]; simp [pow_two]
      rw [h12, h13]; exact h9
    exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp h11

  exact h10

end Kakeya.Assouad
