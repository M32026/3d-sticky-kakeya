import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridParameterSelectionHelpers

/-!
# Large-base terminal-grid parameters

Choose the grid base after `eta`, then choose a terminal level at each small
scale.  The local-child branching loss costs one power of `delta^(-eta)` and
the remaining atomization logarithm costs the second.
-/

namespace Kakeya.Assouad

theorem projected_fiber_grid_parameter_selection :
    ProjectedFiberGridParameterSelectionStatement := by
  intro eta heta
  rcases exists_large_base eta heta with
    ⟨base, hbase_ge3, hC_le⟩
  let C_nat : ℕ := 2 * (Nat.log 2 ((base + 1) ^ 2) + 1)
  let C_real : ℝ := C_nat
  have hC_real_pos : 0 < C_real := by positivity
  have hbase_pos : 0 < (base : ℝ) := by positivity
  have hbase_nonneg : 0 ≤ (base : ℝ) := by linarith
  have hbase1 : 1 < (base : ℝ) := by
    exact_mod_cast (show 1 < base from by omega)
  have hlog_base_pos : 0 < Real.log (base : ℝ) :=
    Real.log_pos hbase1
  have hC_le' : C_real ≤ (base : ℝ) ^ eta := by
    simpa [C_real, C_nat] using hC_le

  let C1 : ℝ := (Real.log 2 + 2 * Real.log 107) / Real.log 2
  let B : ℝ := 2 * Real.log (base : ℝ) / Real.log 2
  let K_atom : ℝ := 2 * C1 + 2 + 2 * B
  let K_log : ℝ := 1 + 1 / Real.log (base : ℝ)
  let K : ℝ := K_atom * K_log
  let K' : ℝ := K * (2 * C_real)
  have hK_pos : 0 < K := by positivity
  have hK'_pos : 0 < K' := by positivity
  have hB_nonneg : 0 ≤ B := by positivity
  have hC1_nonneg : 0 ≤ C1 := by positivity

  rcases exists_delta_log_absorbed
      (n := 1) K' hK'_pos heta (by norm_num) with
    ⟨δ₀, hδ₀_pos, hδ₀_le1, h_absorb⟩
  let δ₀' : ℝ := min δ₀ (1 / 2)
  have hδ₀'_pos : 0 < δ₀' := by positivity
  have hδ₀'_lt1 : δ₀' < 1 := by
    have h : δ₀' ≤ 1 / 2 := min_le_right _ _
    linarith
  have h_absorb' : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀' →
      K' * (1 + Real.log δ⁻¹) ≤ Real.rpow δ (-eta) := by
    intro δ hδ hδ_le
    have h : δ ≤ δ₀ := hδ_le.trans (min_le_left _ _)
    have h' := h_absorb δ hδ h
    simpa using h'

  refine ⟨base, hbase_ge3, δ₀', hδ₀'_pos, hδ₀'_lt1, ?_⟩
  intro δ hδ hδ_le

  have hδ_lt1 : δ < 1 := hδ_le.trans_lt hδ₀'_lt1
  rcases exists_levels_mesh base hbase_ge3 δ hδ hδ_lt1 with
    ⟨levels, hmesh1, hmesh2⟩

  have h_base_pow_le : (base : ℝ) ^ levels ≤ δ⁻¹ := by
    have hpos : 0 < (base ^ levels : ℝ) := by positivity
    have h2 : (base ^ levels : ℝ) ≤ δ⁻¹ := by
      calc
        (base ^ levels : ℝ)
            = (((base ^ levels : ℝ)⁻¹)⁻¹) := by
              field_simp [hpos.ne'] <;> ring
        _ ≤ δ⁻¹ := by gcongr
    exact h2

  have hC_pow_le :
      C_real ^ levels ≤ Real.rpow δ (-eta) := by
    have h1 : C_real ≤ (base : ℝ) ^ eta := hC_le'
    have h2 :
        C_real ^ levels ≤ ((base : ℝ) ^ eta) ^ levels := by
      gcongr <;> linarith
    have h3 :
        ((base : ℝ) ^ eta) ^ levels =
          (base : ℝ) ^ (eta * (levels : ℝ)) := by
      have h31 :
          ((base : ℝ) ^ eta) ^ (levels : ℝ) =
            (base : ℝ) ^ (eta * (levels : ℝ)) := by
        rw [← Real.rpow_mul hbase_nonneg] <;> ring
      have h32 :
          ((base : ℝ) ^ eta) ^ levels =
            ((base : ℝ) ^ eta) ^ (levels : ℝ) := by
        rw [Real.rpow_natCast]
      rw [h32, h31]
    rw [h3] at h2
    have h4 :
        (base : ℝ) ^ (eta * (levels : ℝ)) =
          (base : ℝ) ^ ((levels : ℝ) * eta) := by
      ring_nf
    rw [h4] at h2
    have h51 :
        (base : ℝ) ^ ((levels : ℝ) * eta) =
          ((base : ℝ) ^ (levels : ℝ)) ^ eta := by
      rw [Real.rpow_mul hbase_nonneg] <;> ring
    have h52 :
        (base : ℝ) ^ (levels : ℝ) = (base : ℝ) ^ levels := by
      rw [Real.rpow_natCast]
    have h5 :
        (base : ℝ) ^ ((levels : ℝ) * eta) =
          ((base : ℝ) ^ levels) ^ eta := by
      rw [h51, h52]
    rw [h5] at h2
    have h6 :
        ((base : ℝ) ^ levels) ^ eta ≤ (δ⁻¹) ^ eta :=
      Real.rpow_le_rpow (by positivity) h_base_pow_le
        (by linarith)
    have h7 : (δ⁻¹) ^ eta = Real.rpow δ (-eta) :=
      Eq.symm (Real.rpow_neg_eq_inv_rpow δ eta)
    rw [h7] at h6
    exact h2.trans h6
  have hC_pow_succ_le :
      C_real ^ (levels + 1) ≤
        C_real * Real.rpow δ (-eta) := by
    have h :
        C_real ^ (levels + 1) = C_real * C_real ^ levels := by
      simp [pow_succ] <;> ring
    rw [h]
    exact mul_le_mul_of_nonneg_left hC_pow_le (by linarith)

  have hOS_eq1 :
      projectedFiberOSLoss base levels =
        (2 : ENNReal) * (↑(C_nat ^ (levels + 1)) : ENNReal) := by
    unfold projectedFiberOSLoss
    <;> congr
    <;> simp [C_nat]
    <;> norm_cast
  have h_cast :
      (↑(C_nat ^ (levels + 1)) : ENNReal) =
        ENNReal.ofReal (C_real ^ (levels + 1)) := by
    have h1 :
        (↑(C_nat ^ (levels + 1)) : ENNReal) =
          ENNReal.ofReal (↑(C_nat ^ (levels + 1)) : ℝ) := by
      simp
    rw [h1]
    have h2 :
        (↑(C_nat ^ (levels + 1)) : ℝ) =
          C_real ^ (levels + 1) := by
      simp [C_real, Nat.cast_pow] <;> norm_cast
    rw [h2]
  have hOS_bound :
      projectedFiberOSLoss base levels ≤
        ENNReal.ofReal (2 * C_real) *
          Kakeya.realRpowENN δ (-eta) := by
    rw [hOS_eq1, h_cast]
    have h :
        ENNReal.ofReal (C_real ^ (levels + 1)) ≤
          ENNReal.ofReal (C_real * Real.rpow δ (-eta)) :=
      ENNReal.ofReal_mono hC_pow_succ_le
    have h2 :
        ENNReal.ofReal (C_real * Real.rpow δ (-eta)) =
          ENNReal.ofReal C_real *
            Kakeya.realRpowENN δ (-eta) := by
      rw [ENNReal.ofReal_mul (by linarith)] <;> rfl
    have h' :
        ENNReal.ofReal (C_real ^ (levels + 1)) ≤
          ENNReal.ofReal C_real *
            Kakeya.realRpowENN δ (-eta) := by
      rw [← h2]
      exact h
    have h_assoc :
        (2 : ENNReal) *
              (ENNReal.ofReal C_real *
                Kakeya.realRpowENN δ (-eta)) =
            ((2 : ENNReal) * ENNReal.ofReal C_real) *
              Kakeya.realRpowENN δ (-eta) := by
      ring
    have h4 :
        (2 : ENNReal) * ENNReal.ofReal C_real =
          ENNReal.ofReal (2 * C_real) := by
      simp
    calc
      (2 : ENNReal) *
            ENNReal.ofReal (C_real ^ (levels + 1))
          ≤ (2 : ENNReal) *
              (ENNReal.ofReal C_real *
                Kakeya.realRpowENN δ (-eta)) :=
        mul_le_mul_of_nonneg_left h' (by positivity)
      _ = ((2 : ENNReal) * ENNReal.ofReal C_real) *
            Kakeya.realRpowENN δ (-eta) := h_assoc
      _ = ENNReal.ofReal (2 * C_real) *
            Kakeya.realRpowENN δ (-eta) := by rw [h4]

  let indexBound : ℕ := section7GridIndexBound base levels
  let s1 : Finset ℤ :=
    Finset.Icc (-(indexBound : ℤ)) (indexBound : ℤ)
  let s2 : Finset (ℤ × ℤ) := s1.product s1
  let card : ℕ :=
    (boundedPlanarGridCenters base levels indexBound).card
  have h_s1_nonempty : s1.Nonempty := by
    dsimp only [s1, indexBound, section7GridIndexBound]
    refine ⟨0, ?_⟩
    simp only [Finset.mem_Icc] <;> omega
  have h_s2_nonempty : s2.Nonempty :=
    Finset.Nonempty.product h_s1_nonempty h_s1_nonempty
  have hcard_pos : 0 < card := by
    have h1 :
        (boundedPlanarGridCenters base levels indexBound).Nonempty := by
      dsimp only [boundedPlanarGridCenters]
      exact Finset.Nonempty.image h_s2_nonempty _
    exact Finset.card_pos.mpr h1
  have hcard_le :
      card ≤ (104 * base ^ levels + 3) ^ 2 :=
    boundedPlanarGridCenters_card_le base levels hbase_ge3
  have h104_le :
      104 * base ^ levels + 3 ≤ 107 * base ^ levels := by
    have h : base ^ levels ≥ 1 := by
      apply Nat.one_le_pow <;> omega
    omega
  have hcard_le2 :
      2 * card ≤ 2 * (107 * base ^ levels) ^ 2 := by
    calc
      2 * card ≤ 2 * (104 * base ^ levels + 3) ^ 2 := by
        gcongr
      _ ≤ 2 * (107 * base ^ levels) ^ 2 := by gcongr
  have h_natlog_mon :
      Nat.log 2 (2 * card) ≤
        Nat.log 2 (2 * (107 * base ^ levels) ^ 2) :=
    Nat.log_mono_right hcard_le2
  have h_log_bound :
      (Nat.log 2 (2 * card) : ℝ) ≤
        C1 + B * (levels : ℝ) := by
    let N : ℕ := 2 * (107 * base ^ levels) ^ 2
    have hN_pos : 0 < N := by positivity
    have h1 :
        (Nat.log 2 (2 * card) : ℝ) ≤
          (Nat.log 2 N : ℝ) := by
      exact_mod_cast h_natlog_mon
    have h2 :
        (Nat.log 2 N : ℝ) ≤
          Real.log (N : ℝ) / Real.log 2 :=
      nat_log_le_real_log N hN_pos
    have h3 :
        (N : ℝ) = 2 * (107 * (base : ℝ) ^ levels) ^ 2 := by
      simp [N, Nat.cast_pow] <;> ring
    have h4 :
        Real.log (N : ℝ) =
          Real.log 2 + 2 * Real.log 107 +
            2 * (levels : ℝ) * Real.log (base : ℝ) := by
      rw [h3]
      have h5 :
          Real.log (2 * (107 * (base : ℝ) ^ levels) ^ 2) =
            Real.log 2 +
              Real.log ((107 * (base : ℝ) ^ levels) ^ 2) := by
        rw [Real.log_mul (by positivity) (by positivity)] <;> ring
      rw [h5]
      have h6 :
          Real.log ((107 * (base : ℝ) ^ levels) ^ 2) =
            2 * Real.log (107 * (base : ℝ) ^ levels) := by
        rw [Real.log_pow] <;> ring
      rw [h6]
      have h7 :
          Real.log (107 * (base : ℝ) ^ levels) =
            Real.log 107 +
              (levels : ℝ) * Real.log (base : ℝ) := by
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_pow] <;> ring
      rw [h7] <;> ring
    calc
      (Nat.log 2 (2 * card) : ℝ)
          ≤ (Nat.log 2 N : ℝ) := h1
      _ ≤ Real.log (N : ℝ) / Real.log 2 := h2
      _ = (Real.log 2 + 2 * Real.log 107 +
            2 * (levels : ℝ) * Real.log (base : ℝ)) /
            Real.log 2 := by rw [h4]
      _ = C1 + B * (levels : ℝ) := by
        simp only [C1, B] <;> ring

  have h_atom_real :
      (2 * (Nat.log 2 (2 * card) + 1) : ℝ) ≤
        K_atom * ((levels : ℝ) + 1) := by
    have h :
        (2 * (Nat.log 2 (2 * card) + 1) : ℝ) ≤
          2 * (C1 + B * (levels : ℝ) + 1) := by
      gcongr <;> linarith
    have h2 :
        2 * (C1 + B * (levels : ℝ) + 1) ≤
          K_atom * ((levels : ℝ) + 1) := by
      simp only [K_atom]
      have h3 : 0 ≤ (levels : ℝ) := by positivity
      nlinarith [mul_nonneg h3 hB_nonneg,
        mul_nonneg h3 hC1_nonneg]
    exact h.trans h2

  have h_levels_bound :
      (levels : ℝ) ≤
        Real.log (δ⁻¹) / Real.log (base : ℝ) := by
    have h41 :
        Real.log ((base : ℝ) ^ levels) ≤ Real.log (δ⁻¹) := by
      apply Real.log_le_log
      · positivity
      · exact h_base_pow_le
    have h42 :
        Real.log ((base : ℝ) ^ levels) =
          (levels : ℝ) * Real.log (base : ℝ) := by
      rw [Real.log_pow] <;> ring
    rw [h42] at h41
    have h43 : 0 < Real.log (base : ℝ) := hlog_base_pos
    have h44 :
        (levels : ℝ) * Real.log (base : ℝ) ≤ Real.log (δ⁻¹) :=
      h41
    have h45 :
        (levels : ℝ) =
          ((levels : ℝ) * Real.log (base : ℝ)) /
            Real.log (base : ℝ) := by
      field_simp [h43.ne'] <;> ring
    calc
      (levels : ℝ) =
          ((levels : ℝ) * Real.log (base : ℝ)) /
            Real.log (base : ℝ) := h45
      _ ≤ Real.log (δ⁻¹) / Real.log (base : ℝ) := by gcongr

  have h_logδ_nonneg : 0 ≤ Real.log δ⁻¹ := by
    have h6 : δ⁻¹ ≥ 1 := by
      have h7 : δ ≤ 1 := by linarith
      have h8 : δ⁻¹ ≥ (1 : ℝ)⁻¹ := by gcongr
      have h9 : (1 : ℝ)⁻¹ = 1 := by norm_num
      linarith
    exact Real.log_nonneg h6

  have h_levels_log :
      (levels : ℝ) + 1 ≤
        K_log * (1 + Real.log δ⁻¹) := by
    have h5 :
        (levels : ℝ) ≤
          Real.log (δ⁻¹) / Real.log (base : ℝ) :=
      h_levels_bound
    have h6 : 0 ≤ Real.log δ⁻¹ := h_logδ_nonneg
    have h7 : 0 < Real.log (base : ℝ) := hlog_base_pos
    have h8 :
        (levels : ℝ) ≤
          (1 + Real.log δ⁻¹) / Real.log (base : ℝ) := by
      calc
        (levels : ℝ)
            ≤ Real.log δ⁻¹ / Real.log (base : ℝ) := h5
        _ ≤ (1 + Real.log δ⁻¹) / Real.log (base : ℝ) := by
          gcongr
          linarith
    have h9 :
        (levels : ℝ) + 1 ≤
          (1 + Real.log δ⁻¹) / Real.log (base : ℝ) +
            (1 + Real.log δ⁻¹) := by
      linarith
    have h10 :
        (1 + Real.log δ⁻¹) / Real.log (base : ℝ) +
            (1 + Real.log δ⁻¹) =
          K_log * (1 + Real.log δ⁻¹) := by
      simp only [K_log]
      field_simp [h7.ne'] <;> ring
    rw [h10] at h9
    exact h9

  have h_atom_log :
      (2 * (Nat.log 2 (2 * card) + 1) : ℝ) ≤
        K * (1 + Real.log δ⁻¹) := by
    calc
      (2 * (Nat.log 2 (2 * card) + 1) : ℝ)
          ≤ K_atom * ((levels : ℝ) + 1) := h_atom_real
      _ ≤ K_atom * (K_log * (1 + Real.log δ⁻¹)) := by
        gcongr
      _ = K * (1 + Real.log δ⁻¹) := by
        simp only [K] <;> ring

  have h_cast2 :
      ∀ (n : ℕ), (↑n : ENNReal) = ENNReal.ofReal (↑n : ℝ) := by
    intro n
    simp
  have h_atom_bound :
      projectedFiberAtomizationLoss base levels indexBound ≤
        ENNReal.ofReal (K * (1 + Real.log δ⁻¹)) := by
    unfold projectedFiberAtomizationLoss
    rw [h_cast2
      (2 * (Nat.log 2
        (2 * (boundedPlanarGridCenters
          base levels indexBound).card) + 1))]
    have h_card_eq :
        (boundedPlanarGridCenters base levels indexBound).card =
          card := by
      simp [card]
    rw [h_card_eq]
    have h_cast_eq :
        (↑(2 * (Nat.log 2 (2 * card) + 1)) : ℝ) =
          2 * (↑(Nat.log 2 (2 * card)) + 1) := by
      norm_cast <;> ring
    rw [h_cast_eq]
    exact ENNReal.ofReal_mono h_atom_log

  have h_absorb_δ :
      K' * (1 + Real.log δ⁻¹) ≤ Real.rpow δ (-eta) :=
    h_absorb' δ hδ hδ_le
  have hlog_nonneg : 0 ≤ Real.log δ⁻¹ := h_logδ_nonneg
  have h_nonneg1 : 0 ≤ K * (1 + Real.log δ⁻¹) := by
    have h : 0 ≤ 1 + Real.log δ⁻¹ := by linarith
    exact mul_nonneg (by positivity) h
  have h_nonneg2 : 0 ≤ 2 * C_real := by
    linarith [hC_real_pos]

  have h_main :
      projectedFiberAtomizationLoss base levels indexBound *
          projectedFiberOSLoss base levels ≤
        Kakeya.realRpowENN δ (-2 * eta) := by
    calc
      projectedFiberAtomizationLoss base levels indexBound *
            projectedFiberOSLoss base levels
          ≤ ENNReal.ofReal (K * (1 + Real.log δ⁻¹)) *
              (ENNReal.ofReal (2 * C_real) *
                Kakeya.realRpowENN δ (-eta)) := by
            gcongr
      _ = ENNReal.ofReal
            (K * (2 * C_real) * (1 + Real.log δ⁻¹)) *
              Kakeya.realRpowENN δ (-eta) := by
        have h_combine :
            ENNReal.ofReal (K * (1 + Real.log δ⁻¹)) *
                ENNReal.ofReal (2 * C_real) =
              ENNReal.ofReal
                (K * (2 * C_real) * (1 + Real.log δ⁻¹)) := by
          rw [← ENNReal.ofReal_mul h_nonneg1]
          have h :
              K * (1 + Real.log δ⁻¹) * (2 * C_real) =
                K * (2 * C_real) * (1 + Real.log δ⁻¹) := by
            ring
          rw [h] <;> rfl
        have h_assoc :
            ENNReal.ofReal (K * (1 + Real.log δ⁻¹)) *
                (ENNReal.ofReal (2 * C_real) *
                  Kakeya.realRpowENN δ (-eta)) =
              (ENNReal.ofReal (K * (1 + Real.log δ⁻¹)) *
                ENNReal.ofReal (2 * C_real)) *
                  Kakeya.realRpowENN δ (-eta) := by
          ring
        rw [h_assoc, h_combine]
      _ ≤ ENNReal.ofReal (Real.rpow δ (-eta)) *
            Kakeya.realRpowENN δ (-eta) := by
        gcongr <;> exact ENNReal.ofReal_mono h_absorb_δ
      _ = Kakeya.realRpowENN δ (-eta) *
            Kakeya.realRpowENN δ (-eta) := by rfl
      _ = Kakeya.realRpowENN δ (-2 * eta) := by
        have h_rpow :
            Real.rpow δ (-eta) * Real.rpow δ (-eta) =
              Real.rpow δ (-2 * eta) := by
          calc
            Real.rpow δ (-eta) * Real.rpow δ (-eta)
                = Real.rpow δ ((-eta) + (-eta)) :=
                  (Real.rpow_add hδ (-eta) (-eta)).symm
            _ = Real.rpow δ (-2 * eta) := by
              rw [show (-eta) + (-eta) = -2 * eta by ring]
        have h_nonneg_rpow :
            0 ≤ Real.rpow δ (-eta) :=
          Real.rpow_nonneg hδ.le (-eta)
        simp only [Kakeya.realRpowENN]
        have h_combine2 :
            ENNReal.ofReal (Real.rpow δ (-eta)) *
                ENNReal.ofReal (Real.rpow δ (-eta)) =
              ENNReal.ofReal
                (Real.rpow δ (-eta) * Real.rpow δ (-eta)) := by
          rw [← ENNReal.ofReal_mul h_nonneg_rpow]
        rw [h_combine2, h_rpow]

  exact ⟨levels, hmesh1, hmesh2, h_main⟩

end Kakeya.Assouad
