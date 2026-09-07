import MyLeanRepo.Kakeya.Cinematic.Section5.GlobalizationInputs
import MyLeanRepo.Kakeya.Cinematic.Targets.WZ2Input.ConstantAbsorption

/-!
# Absorb endpoint stubs into the final level-set loss

This is the arithmetic and measure-theoretic endpoint step in the
globalization following PYZ Lemma 39.
-/

namespace Kakeya.Cinematic

theorem horizontal_stub_level_set_absorption :
    HorizontalStubLevelSetAbsorptionStatement := by
  intro h_graph h_stub
  intro C_KT lambda L epsilon hC_KT hlambda hL hepsilon
  set C_total : ℝ := 4 * (1 + L) * lambda^2 * Real.rpow C_KT (3 / 2 : ℝ) with hC_total_def
  have hC_total_nonneg : 0 ≤ C_total := by
    have h1 : 0 ≤ 1 + L := by linarith
    have h2 : 0 ≤ Real.rpow C_KT (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    positivity
  set β : ℝ := 1 / 2 + epsilon with hβ_def
  have hβ_pos : 0 < β := by linarith
  rcases constant_absorption C_total β hC_total_nonneg hβ_pos with
    ⟨δ_absorb, hδ_absorb_pos, hδ_absorb⟩
  set delta₀ : ℝ := min δ_absorb (1 / lambda) with hdelta₀_def
  have hdelta₀_pos : 0 < delta₀ := by
    have h1 : 0 < δ_absorb := hδ_absorb_pos
    have h2 : 0 < 1 / lambda := by positivity
    positivity
  have hdelta₀_le : delta₀ ≤ 1 / lambda := min_le_right _ _
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le, ?_⟩
  intro delta hdelta hdelta₀ F mu E a b hKT hmu_pos hE_nonempty hE_meas hab hsub hlen hderiv hE_sub hmult
  have hdelta_absorb : delta ≤ δ_absorb := le_trans hdelta₀ (min_le_left _ _)
  set rho : ℝ := lambda * delta with hrho_def
  have hrho_pos : 0 < rho := by positivity
  have h_stub_bound : ENNReal.ofReal (mu : ℝ) * MeasureTheory.volume E ≤
      ENNReal.ofReal (2 * (1 + L) * rho * (b - a) * (F.card : ℝ)) :=
    h_stub h_graph (delta := rho) (L := L) (a := a) (b := b) (mu := mu) (E := E)
      hrho_pos hab hsub hderiv hmu_pos hE_meas hE_sub hmult
  set X : ℝ := 2 * (1 + L) * rho * (b - a) * (F.card : ℝ) with hX_def
  have hX_nonneg : 0 ≤ X := by
    have h1 : 0 ≤ 1 + L := by linarith
    have h2 : 0 ≤ b - a := by linarith
    positivity
  have h_card_bound : (F.card : ℝ) ≤ C_KT / delta := hKT.1
  set C : ℝ := 4 * (1 + L) * lambda^2 * C_KT with hC_def
  have hC_nonneg : 0 ≤ C := by
    have h1 : 0 ≤ 1 + L := by linarith
    have h2 : 0 ≤ C_KT := by linarith
    positivity
  have hX_eq1 : X = 2 * (1 + L) * (lambda * delta) * (b - a) * (F.card : ℝ) := by
    rw [hX_def, hrho_def] <;> ring
  have hX_le : X ≤ C * delta := by
    rw [hX_eq1]
    have h1 : 2 * (1 + L) * (lambda * delta) * (b - a) * (F.card : ℝ) ≤
        2 * (1 + L) * (lambda * delta) * (2 * lambda * delta) * (C_KT / delta) := by
      gcongr <;> linarith
    have h2 : 2 * (1 + L) * (lambda * delta) * (2 * lambda * delta) *
        (C_KT / delta) = C * delta := by
      rw [hC_def]
      field_simp [hdelta.ne'] <;> ring
    linarith
  rcases hE_nonempty with ⟨p, hp⟩
  have h_mult_p : (mu : ℝ) ≤ multiplicity F rho p := hmult p hp
  have h_multiplicity_le_card : multiplicity F rho p ≤ (F.card : ℝ) := by
    have h_eq : multiplicity F rho p =
        ∑ f ∈ F.toFinset, (graphNeighborhood f rho).indicator (fun _ => (1 : ℝ)) p := by
      rfl
    rw [h_eq]
    have h5 : ∀ f ∈ F.toFinset,
        (graphNeighborhood f rho).indicator (fun _ => (1 : ℝ)) p ≤ 1 := by
      intro f _
      by_cases h : p ∈ graphNeighborhood f rho
      · simp [h] <;> norm_num
      · simp [h] <;> norm_num
    have h6 : ∑ f ∈ F.toFinset,
        (graphNeighborhood f rho).indicator (fun _ => (1 : ℝ)) p ≤
        ∑ _f ∈ F.toFinset, (1 : ℝ) := Finset.sum_le_sum h5
    have h7 : (∑ _f ∈ F.toFinset, (1 : ℝ)) = (F.toFinset.card : ℝ) := by simp
    have h8 : F.toFinset.card = F.card := by
      have h9 : F.toFinset = F.finite.toFinset := by
        simp [FiniteFunctionFamily.toFinset]
      rw [h9]
      have h10 : F.finite.toFinset.card = F.carrier.ncard :=
        (Set.ncard_eq_toFinset_card F.carrier F.finite).symm
      rw [h10]
      rfl
    rw [h7, h8] at h6
    exact h6
  have hmu_le_card : (mu : ℝ) ≤ (F.card : ℝ) :=
    le_trans h_mult_p h_multiplicity_le_card
  have hmu_pos' : 0 < (mu : ℝ) := by exact_mod_cast hmu_pos
  have hmu_le_CKTDelta : (mu : ℝ) ≤ C_KT / delta :=
    le_trans hmu_le_card h_card_bound
  have hCKT_pos : 0 < C_KT := by linarith
  have h_absorb : C_total ≤ Real.rpow delta (-β) :=
    hδ_absorb delta hdelta hdelta_absorb
  have h_delta_pos' : 0 < delta := hdelta
  have h_mu_sqrt_le : Real.rpow (mu : ℝ) (1 / 2 : ℝ) ≤
      Real.rpow (C_KT / delta) (1 / 2 : ℝ) := by
    apply Real.rpow_le_rpow <;> linarith
  have h_rpow_div2 : Real.rpow (C_KT / delta) (1 / 2 : ℝ) =
      Real.rpow C_KT (1 / 2 : ℝ) / Real.rpow delta (1 / 2 : ℝ) := by
    have h1 : Real.rpow (C_KT / delta) (1 / 2 : ℝ) = Real.sqrt (C_KT / delta) :=
      (Real.sqrt_eq_rpow (C_KT / delta)).symm
    have h2 : Real.sqrt (C_KT / delta) = Real.sqrt C_KT / Real.sqrt delta :=
      Real.sqrt_div (show 0 ≤ C_KT by linarith) delta
    have h3 : Real.sqrt C_KT = Real.rpow C_KT (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow C_KT
    have h4 : Real.sqrt delta = Real.rpow delta (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow delta
    rw [h1, h2, h3, h4]
  have h_rpow_neg12 : Real.rpow delta (-1 / 2 : ℝ) =
      (Real.rpow delta (1 / 2 : ℝ))⁻¹ := by
    have h_nonneg : 0 ≤ delta := le_of_lt hdelta
    have h : Real.rpow delta (-(1 / 2 : ℝ)) =
        (Real.rpow delta (1 / 2 : ℝ))⁻¹ :=
      Real.rpow_neg h_nonneg (1 / 2 : ℝ)
    have h2 : (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) := by norm_num
    rw [h2] at h
    exact h
  have h_rpow_div3 : Real.rpow (C_KT / delta) (1 / 2 : ℝ) =
      Real.rpow C_KT (1 / 2 : ℝ) * Real.rpow delta (-1 / 2 : ℝ) := by
    rw [h_rpow_div2, h_rpow_neg12] <;> ring
  have h_rpow_add1 : Real.rpow delta (1 + epsilon) *
      Real.rpow delta (-1 / 2 : ℝ) = Real.rpow delta β := by
    have h : Real.rpow delta ((1 + epsilon) + (-1 / 2 : ℝ)) =
        Real.rpow delta (1 + epsilon) * Real.rpow delta (-1 / 2 : ℝ) :=
      Real.rpow_add hdelta _ _
    have h2 : (1 + epsilon) + (-1 / 2 : ℝ) = β := by
      simp [hβ_def] <;> ring
    rw [h2] at h
    exact h.symm
  have h_rpow_CKt32 : Real.rpow C_KT (3 / 2 : ℝ) =
      Real.rpow C_KT (1 / 2 : ℝ) * C_KT := by
    have h : Real.rpow C_KT ((1 / 2 : ℝ) + 1) =
        Real.rpow C_KT (1 / 2 : ℝ) * Real.rpow C_KT 1 :=
      Real.rpow_add (by linarith) _ _
    have h2 : Real.rpow C_KT 1 = C_KT := Real.rpow_one C_KT
    rw [h2] at h
    have h3 : (1 / 2 : ℝ) + 1 = (3 / 2 : ℝ) := by norm_num
    rw [h3] at h
    exact h
  have h_main : C * Real.rpow delta (1 + epsilon) *
      Real.rpow (mu : ℝ) (1 / 2 : ℝ) ≤ 1 := by
    have h_step1 : C * Real.rpow delta (1 + epsilon) *
        Real.rpow (mu : ℝ) (1 / 2 : ℝ) ≤
        C * Real.rpow delta (1 + epsilon) *
          Real.rpow (C_KT / delta) (1 / 2 : ℝ) := by
      have h_pos : 0 ≤ C * Real.rpow delta (1 + epsilon) :=
        mul_nonneg hC_nonneg (Real.rpow_nonneg (le_of_lt hdelta) _)
      exact mul_le_mul_of_nonneg_left h_mu_sqrt_le h_pos
    have h_step2 : C * Real.rpow delta (1 + epsilon) *
        Real.rpow (C_KT / delta) (1 / 2 : ℝ) =
        C * Real.rpow C_KT (1 / 2 : ℝ) * Real.rpow delta β := by
      rw [h_rpow_div3]
      have h_assoc : C * Real.rpow delta (1 + epsilon) *
          (Real.rpow C_KT (1 / 2 : ℝ) * Real.rpow delta (-1 / 2 : ℝ)) =
          C * Real.rpow C_KT (1 / 2 : ℝ) *
            (Real.rpow delta (1 + epsilon) * Real.rpow delta (-1 / 2 : ℝ)) := by
        ring
      rw [h_assoc, h_rpow_add1] <;> ring
    have h_step3 : C * Real.rpow C_KT (1 / 2 : ℝ) *
        Real.rpow delta β = C_total * Real.rpow delta β := by
      simp only [hC_total_def, hC_def, h_rpow_CKt32] <;> ring
    have h_step4 : C_total * Real.rpow delta β ≤ 1 := by
      have h6 : C_total * Real.rpow delta β ≤
          Real.rpow delta (-β) * Real.rpow delta β := by
        gcongr <;> exact Real.rpow_nonneg (by positivity) _
      have h7 : Real.rpow delta (-β) * Real.rpow delta β = 1 := by
        have h8 : Real.rpow delta ((-β) + β) =
            Real.rpow delta (-β) * Real.rpow delta β :=
          Real.rpow_add hdelta _ _
        have h9 : (-β) + β = 0 := by ring
        rw [h9] at h8
        have h10 : Real.rpow delta 0 = 1 := Real.rpow_zero delta
        rw [h10] at h8
        exact h8.symm
      rw [h7] at h6
      exact h6
    calc
      C * Real.rpow delta (1 + epsilon) * Real.rpow (mu : ℝ) (1 / 2 : ℝ)
          ≤ C * Real.rpow delta (1 + epsilon) *
              Real.rpow (C_KT / delta) (1 / 2 : ℝ) := h_step1
      _ = C * Real.rpow C_KT (1 / 2 : ℝ) * Real.rpow delta β := h_step2
      _ = C_total * Real.rpow delta β := h_step3
      _ ≤ 1 := h_step4
  have h_delta_rpow : Real.rpow delta (1 + epsilon) =
      delta * Real.rpow delta epsilon := by
    have h : Real.rpow delta (1 + epsilon) =
        Real.rpow delta 1 * Real.rpow delta epsilon :=
      Real.rpow_add hdelta 1 epsilon
    have h1 : Real.rpow delta 1 = delta := Real.rpow_one delta
    rw [h, h1]
  have h_step1 : C * Real.rpow delta (1 + epsilon) ≤
      Real.rpow (mu : ℝ) (-1 / 2 : ℝ) := by
    have h_pos_sqrt : 0 < Real.rpow (mu : ℝ) (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hmu_pos' _
    have h : C * Real.rpow delta (1 + epsilon) *
        Real.rpow (mu : ℝ) (1 / 2 : ℝ) ≤ 1 := h_main
    have h9 : C * Real.rpow delta (1 + epsilon) ≤
        (Real.rpow (mu : ℝ) (1 / 2 : ℝ))⁻¹ := by
      have h10 : C * Real.rpow delta (1 + epsilon) =
          (C * Real.rpow delta (1 + epsilon) *
              Real.rpow (mu : ℝ) (1 / 2 : ℝ)) /
            Real.rpow (mu : ℝ) (1 / 2 : ℝ) := by
        field_simp [h_pos_sqrt.ne'] <;> ring
      rw [h10]
      have h11 : (C * Real.rpow delta (1 + epsilon) *
          Real.rpow (mu : ℝ) (1 / 2 : ℝ)) /
            Real.rpow (mu : ℝ) (1 / 2 : ℝ) ≤
          (1 : ℝ) / Real.rpow (mu : ℝ) (1 / 2 : ℝ) := by
        apply div_le_div_of_nonneg_right h
        exact le_of_lt h_pos_sqrt
      simpa using h11
    have h10 : (Real.rpow (mu : ℝ) (1 / 2 : ℝ))⁻¹ =
        Real.rpow (mu : ℝ) (-1 / 2 : ℝ) := by
      have h_nonneg : 0 ≤ (mu : ℝ) := by positivity
      have h_neg : Real.rpow (mu : ℝ) (-(1 / 2 : ℝ)) =
          (Real.rpow (mu : ℝ) (1 / 2 : ℝ))⁻¹ :=
        Real.rpow_neg h_nonneg (1 / 2 : ℝ)
      have h2 : (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) := by norm_num
      rw [h2] at h_neg
      exact h_neg.symm
    rw [h10] at h9
    exact h9
  have h_step2 : C * delta ≤
      Real.rpow delta (-epsilon) * Real.rpow (mu : ℝ) (-1 / 2 : ℝ) := by
    have h_pos_eps : 0 < Real.rpow delta epsilon :=
      Real.rpow_pos_of_pos hdelta _
    have h11 : C * Real.rpow delta (1 + epsilon) ≤
        Real.rpow (mu : ℝ) (-1 / 2 : ℝ) := h_step1
    rw [h_delta_rpow] at h11
    have h12 : C * (delta * Real.rpow delta epsilon) ≤
        Real.rpow (mu : ℝ) (-1 / 2 : ℝ) := h11
    have h13 : C * delta ≤
        Real.rpow (mu : ℝ) (-1 / 2 : ℝ) / Real.rpow delta epsilon := by
      have h14 : C * delta =
          (C * (delta * Real.rpow delta epsilon)) / Real.rpow delta epsilon := by
        field_simp [h_pos_eps.ne'] <;> ring
      rw [h14]
      gcongr
    have h15 : Real.rpow delta (-epsilon) =
        (Real.rpow delta epsilon)⁻¹ := by
      simpa using Real.rpow_neg (by linarith) epsilon
    have h16 : Real.rpow (mu : ℝ) (-1 / 2 : ℝ) /
        Real.rpow delta epsilon =
        Real.rpow delta (-epsilon) * Real.rpow (mu : ℝ) (-1 / 2 : ℝ) := by
      rw [h15] <;> ring
    rw [h16] at h13
    exact h13
  have h_step3 : C * delta / (mu : ℝ) ≤
      Real.rpow delta (-epsilon) * Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
    have h15 : C * delta ≤
        Real.rpow delta (-epsilon) * Real.rpow (mu : ℝ) (-1 / 2 : ℝ) := h_step2
    have h16 : C * delta / (mu : ℝ) ≤
        (Real.rpow delta (-epsilon) * Real.rpow (mu : ℝ) (-1 / 2 : ℝ)) /
          (mu : ℝ) := by
      gcongr
    have h17 : Real.rpow (mu : ℝ) (-3 / 2 : ℝ) =
        Real.rpow (mu : ℝ) (-1 / 2 : ℝ) / (mu : ℝ) := by
      have h_nonneg : 0 ≤ (mu : ℝ) := by positivity
      have h_add : Real.rpow (mu : ℝ) ((-1 / 2 : ℝ) + (-1 : ℝ)) =
          Real.rpow (mu : ℝ) (-1 / 2 : ℝ) * Real.rpow (mu : ℝ) (-1 : ℝ) :=
        Real.rpow_add hmu_pos' (-1 / 2 : ℝ) (-1 : ℝ)
      have h_sum : (-1 / 2 : ℝ) + (-1 : ℝ) = (-3 / 2 : ℝ) := by norm_num
      rw [h_sum] at h_add
      have h_neg1 : Real.rpow (mu : ℝ) (-1 : ℝ) = (mu : ℝ)⁻¹ := by
        have h : Real.rpow (mu : ℝ) (-1 : ℝ) =
            (Real.rpow (mu : ℝ) 1)⁻¹ :=
          Real.rpow_neg h_nonneg 1
        have h2 : Real.rpow (mu : ℝ) 1 = (mu : ℝ) :=
          Real.rpow_one (mu : ℝ)
        exact h.trans (congr_arg Inv.inv h2)
      rw [h_add, h_neg1] <;> ring
    have h22 : (Real.rpow delta (-epsilon) *
        Real.rpow (mu : ℝ) (-1 / 2 : ℝ)) / (mu : ℝ) =
        Real.rpow delta (-epsilon) * Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
      rw [h17] <;> ring
    rw [h22] at h16
    exact h16
  have hX_div_le : X / (mu : ℝ) ≤
      Real.rpow delta (-epsilon) * Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
    have h1 : X / (mu : ℝ) ≤ C * delta / (mu : ℝ) := by gcongr
    exact h1.trans h_step3
  have hX_eq : X = (mu : ℝ) * (X / (mu : ℝ)) := by
    field_simp [hmu_pos'.ne'] <;> ring
  rw [hX_eq] at h_stub_bound
  have h_ofReal_mul : ENNReal.ofReal ((mu : ℝ) * (X / (mu : ℝ))) =
      ENNReal.ofReal (mu : ℝ) * ENNReal.ofReal (X / (mu : ℝ)) := by
    rw [ENNReal.ofReal_mul] <;> positivity
  rw [h_ofReal_mul] at h_stub_bound
  set a : ENNReal := ENNReal.ofReal (mu : ℝ) with ha_def
  have ha_ne_zero : a ≠ 0 := by
    rw [ha_def]
    exact ENNReal.ofReal_ne_zero_iff.mpr hmu_pos'
  have ha_ne_top : a ≠ ⊤ := by
    simp [ha_def]
  have h_inv_mul : a⁻¹ * a = 1 := by
    rw [ENNReal.inv_mul_cancel ha_ne_zero ha_ne_top]
  have h_cancel1 : a⁻¹ * (a * MeasureTheory.volume E) ≤
      a⁻¹ * (a * ENNReal.ofReal (X / (mu : ℝ))) := by
    gcongr
  have h_cancel2 : a⁻¹ * (a * MeasureTheory.volume E) =
      MeasureTheory.volume E := by
    rw [← mul_assoc, h_inv_mul, one_mul]
  have h_cancel3 : a⁻¹ * (a * ENNReal.ofReal (X / (mu : ℝ))) =
      ENNReal.ofReal (X / (mu : ℝ)) := by
    rw [← mul_assoc, h_inv_mul, one_mul]
  rw [h_cancel2, h_cancel3] at h_cancel1
  have h_volume_le : MeasureTheory.volume E ≤ ENNReal.ofReal (X / (mu : ℝ)) :=
    h_cancel1
  have h_target_nonneg : 0 ≤
      Real.rpow delta (-epsilon) * Real.rpow (mu : ℝ) (-3 / 2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (le_of_lt hdelta) _)
      (Real.rpow_nonneg (le_of_lt hmu_pos') _)
  exact h_volume_le.trans (ENNReal.ofReal_le_ofReal hX_div_le)

end Kakeya.Cinematic
