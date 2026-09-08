import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.NonDistinctDilatedContainment

/-!
# Strong non-distinctness implies quantitative dilated containment

This is the parameterized overlap version of
`non_distinct_dilated_containment`.

If two equal-radius tubes overlap in more than a `1 / K` fraction of one tube
volume, then one is contained in a homothetic dilation of the other with
factor linear in `K`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined.GeometricLemmas

/--
Quantitative containment from `K`-strong non-distinctness.

The midpoint bound is the one supplied by a coarse cover of a unit-ball fine
family.  The dilation factor `1000 * K` is deliberately explicit for the
subsequent packing estimate.
-/
def StrongNonDistinctDilatedContainmentStatement : Prop :=
  ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
    ∀ T₁ T₂ : Kakeya.DeltaTube rho,
      ‖tubeMidpoint T₁‖ ≤ 3 →
      ‖tubeMidpoint T₂‖ ≤ 3 →
    ∀ K : ℝ, 2 ≤ K →
      volume (T₁.carrier ∩ T₂.carrier) >
          T₁.volume / ENNReal.ofReal K →
        T₁.carrier ⊆ dilatedTubeCarrier (1000 * K) T₂

/--
Quantitative containment from `K`-strong non-distinctness.

Adapts `non_distinct_local_geometry`: the overlap threshold `V/K` yields
a Rogers--Shephard bound `64·K·V`, a direction bound `(176/3)·K·π·ρ`, and
containment in the `1000·K` dilation.
-/
lemma strong_non_distinct_dilated_containment_lemma
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (T1 T2 : Kakeya.DeltaTube ρ)
    (h_m1 : ‖tubeMidpoint T1‖ ≤ 3) (h_m2 : ‖tubeMidpoint T2‖ ≤ 3)
    {K : ℝ} (hK : 2 ≤ K)
    (h_overlap : volume (T1.carrier ∩ T2.carrier) >
        T1.volume / ENNReal.ofReal K) :
    T1.carrier ⊆ dilatedTubeCarrier (1000 * K) T2 := by
  let canonical : Kakeya.DeltaTube ρ :=
    { base := 0
      direction := EuclideanSpace.single (0 : Fin 3) 1
      direction_unit := by simp [EuclideanSpace.norm_eq] <;> norm_num }
  let V := Kakeya.deltaTubeVolume ρ
  have h_vol1 : T1.volume = V := by
    have h : T1.volume = canonical.volume := tube_volume_eq T1 canonical
    rw [h]; rfl
  have h_vol2 : T2.volume = V := by
    have h : T2.volume = canonical.volume := tube_volume_eq T2 canonical
    rw [h]; rfl
  have hV_pos : 0 < V := by
    have h_lower : V ≥ ENNReal.ofReal (Real.pi * ρ ^ 2 + (4 / 3 : ℝ) * Real.pi * ρ ^ 3) :=
      capsule_volume_lower ρ hρ
    have h_pos : 0 < Real.pi * ρ ^ 2 + (4 / 3 : ℝ) * Real.pi * ρ ^ 3 := by positivity
    have h_ennreal_pos : 0 < ENNReal.ofReal (Real.pi * ρ ^ 2 + (4 / 3 : ℝ) * Real.pi * ρ ^ 3) :=
      ENNReal.ofReal_pos.mpr h_pos
    exact lt_of_lt_of_le h_ennreal_pos h_lower
  have hV_finite : V ≠ ⊤ := by
    have h_upper : V ≤ ENNReal.ofReal (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3) :=
      capsule_upper_bound_instantiation ρ hρ
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_upper
  let eK : ENNReal := ENNReal.ofReal K
  have hK_pos : 0 < K := by linarith
  have heK_pos : 0 < eK := ENNReal.ofReal_pos.mpr hK_pos
  have heK_ne_zero : eK ≠ 0 := heK_pos.ne'
  have heK_ne_top : eK ≠ ⊤ := ENNReal.ofReal_ne_top
  have hK_mul_inv : eK * eK⁻¹ = 1 := ENNReal.mul_inv_cancel heK_ne_zero heK_ne_top
  have h_overlap' : volume (T1.carrier ∩ T2.carrier) > V * eK⁻¹ := by
    have h_div : T1.volume / eK = T1.volume * eK⁻¹ := by
      have h1 : T1.volume / eK = eK⁻¹ * T1.volume := ENNReal.div_eq_inv_mul
      rw [h1, mul_comm]
    rw [h_div, h_vol1] at h_overlap
    exact h_overlap
  have heK_inv_ne_zero : eK⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr heK_ne_top
  have h_inter_pos : 0 < volume (T1.carrier ∩ T2.carrier) := by
    have h : (0 : ENNReal) < V * eK⁻¹ := by
      exact ENNReal.mul_pos hV_pos.ne' heK_inv_ne_zero
    exact lt_trans h h_overlap'
  have h_inter_nonempty : (T1.carrier ∩ T2.carrier).Nonempty := by
    by_contra h
    have h' : T1.carrier ∩ T2.carrier = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h
    rw [h'] at h_inter_pos
    simp at h_inter_pos <;> exact h_inter_pos
  have h_inter_ne_zero : volume (T1.carrier ∩ T2.carrier) ≠ 0 := h_inter_pos.ne'
  have h_inter_ne_top : volume (T1.carrier ∩ T2.carrier) ≠ ⊤ := by
    have h_sub : T1.carrier ∩ T2.carrier ⊆ T1.carrier := by simp
    have h6 : volume (T1.carrier ∩ T2.carrier) ≤ volume T1.carrier := measure_mono h_sub
    have h7 : volume T1.carrier = T1.volume := by rfl
    rw [h7] at h6
    intro h_top
    rw [h_top] at h6
    have h8 : T1.volume = ⊤ := by simpa using h6
    rw [h_vol1] at h8
    exact hV_finite h8
  have hK_conv : Convex ℝ T1.carrier := deltaTube_carrier_convex T1
  have hL_conv : Convex ℝ T2.carrier := deltaTube_carrier_convex T2
  have h_rs1 : volume (minkowskiDiff T1.carrier T2.carrier) * volume (T1.carrier ∩ T2.carrier) ≤
      64 * T1.volume * T2.volume := rogers_shephard_general hK_conv hL_conv
  have h_rs2 : 64 * T1.volume * T2.volume = 64 * V * V := by
    rw [h_vol1, h_vol2] <;> ring
  rw [h_rs2] at h_rs1
  have h12 : (eK * V) * (V * eK⁻¹) = (eK * eK⁻¹) * (V * V) := by ac_rfl
  have h9 : (64 * eK * V) * (V * eK⁻¹) = (64 : ENNReal) * (eK * eK⁻¹) * (V * V) := by
    have h10 : (64 * eK * V) * (V * eK⁻¹) = 64 * ((eK * V) * (V * eK⁻¹)) := by
      simp [mul_assoc]
    rw [h10, h12]
    <;> simp [mul_assoc]
  have h_factor : (64 * eK * V) * (V * eK⁻¹) = 64 * V * V := by
    have h13 : (64 : ENNReal) * (eK * eK⁻¹) * (V * V) = 64 * V * V := by
      rw [hK_mul_inv]
      <;> simp [mul_one, mul_assoc]
    exact Eq.trans h9 h13
  have h4 : V * eK⁻¹ ≤ volume (T1.carrier ∩ T2.carrier) := le_of_lt h_overlap'
  have h5 : (64 * eK * V) * (V * eK⁻¹) ≤ (64 * eK * V) * volume (T1.carrier ∩ T2.carrier) := by
    gcongr
  have h3 : volume (minkowskiDiff T1.carrier T2.carrier) * volume (T1.carrier ∩ T2.carrier) ≤
      (64 * eK * V) * volume (T1.carrier ∩ T2.carrier) := by
    calc volume (minkowskiDiff T1.carrier T2.carrier) * volume (T1.carrier ∩ T2.carrier)
      ≤ 64 * V * V := h_rs1
    _ = (64 * eK * V) * (V * eK⁻¹) := h_factor.symm
    _ ≤ (64 * eK * V) * volume (T1.carrier ∩ T2.carrier) := h5
  have h_cancel : (volume (minkowskiDiff T1.carrier T2.carrier) * volume (T1.carrier ∩ T2.carrier)) /
      volume (T1.carrier ∩ T2.carrier) = volume (minkowskiDiff T1.carrier T2.carrier) := by
    simp [div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel h_inter_ne_zero h_inter_ne_top]
  have h_result : (volume (minkowskiDiff T1.carrier T2.carrier) * volume (T1.carrier ∩ T2.carrier)) /
      volume (T1.carrier ∩ T2.carrier) ≤ 64 * eK * V := ENNReal.div_le_of_le_mul h3
  rw [h_cancel] at h_result
  let d1 := T1.direction
  let d2 := T2.direction
  have hd1 : ‖d1‖ = 1 := T1.direction_unit
  have hd2 : ‖d2‖ = 1 := T2.direction_unit
  have h_lower : ENNReal.ofReal (4 * ρ * ‖cross d1 d2‖) ≤
      volume (minkowskiDiff T1.carrier T2.carrier) :=
    minkowski_diff_volume_lower hρ hd1 hd2 T1.carrier T2.carrier (by rfl) (by rfl)
  have h_capsule : V ≤ ENNReal.ofReal (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3) :=
    capsule_upper_bound_instantiation ρ hρ
  have h_comb : ENNReal.ofReal (4 * ρ * ‖cross d1 d2‖) ≤ 64 * eK * V :=
    le_trans h_lower h_result
  have h_cross_nonneg : 0 ≤ 4 * ρ * ‖cross d1 d2‖ := by positivity
  have h_V_nonneg : 0 ≤ Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3 := by positivity
  have h_real_ineq : 4 * ρ * ‖cross d1 d2‖ ≤
      64 * K * (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3) := by
    have h1 : ENNReal.ofReal (4 * ρ * ‖cross d1 d2‖) ≤
        ENNReal.ofReal (64 * K * (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3)) := by
      calc ENNReal.ofReal (4 * ρ * ‖cross d1 d2‖)
        ≤ 64 * eK * V := h_comb
      _ ≤ 64 * eK * ENNReal.ofReal (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3) := by
        gcongr <;> exact h_capsule
      _ = ENNReal.ofReal (64 * K * (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3)) := by
        have h64 : (64 : ENNReal) = ENNReal.ofReal (64 : ℝ) := by simp
        rw [h64]
        have h_mul1 : ENNReal.ofReal (64 : ℝ) * eK = ENNReal.ofReal (64 * K) := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)] <;> rfl
        rw [h_mul1]
        have h_pos2 : 0 ≤ 64 * K := by positivity
        rw [← ENNReal.ofReal_mul h_pos2] <;> rfl
    have h_b_nonneg : 0 ≤ 64 * K * (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3) := by positivity
    exact (ENNReal.ofReal_le_ofReal_iff h_b_nonneg).mp h1
  have h_cross_bound : ‖cross d1 d2‖ ≤ (176 : ℝ) / 3 * K * Real.pi * ρ := by
    have h_pos : 0 < ρ := hρ
    have h : 4 * ρ * ‖cross d1 d2‖ ≤
        64 * K * (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3) := h_real_ineq
    have h4pos : 0 < 4 * ρ := by positivity
    have h2 : ‖cross d1 d2‖ ≤ 16 * K * Real.pi * ρ + (128 : ℝ) / 3 * K * Real.pi * ρ ^ 2 := by
      have h_div1 : (4 * ρ * ‖cross d1 d2‖) / (4 * ρ) = ‖cross d1 d2‖ := by
        field_simp [h4pos.ne'] <;> ring
      have h_div3 : (64 * K * (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3)) / (4 * ρ) =
          16 * K * Real.pi * ρ + (128 : ℝ) / 3 * K * Real.pi * ρ ^ 2 := by
        field_simp [h4pos.ne'] <;> ring
      calc ‖cross d1 d2‖
        = (4 * ρ * ‖cross d1 d2‖) / (4 * ρ) := h_div1.symm
      _ ≤ (64 * K * (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3)) / (4 * ρ) := by gcongr
      _ = 16 * K * Real.pi * ρ + (128 : ℝ) / 3 * K * Real.pi * ρ ^ 2 := h_div3
    have h3 : 16 * K * Real.pi * ρ + (128 : ℝ) / 3 * K * Real.pi * ρ ^ 2 ≤
        (176 : ℝ) / 3 * K * Real.pi * ρ := by
      have h4 : ρ ^ 2 ≤ ρ := by nlinarith
      nlinarith [Real.pi_pos, hK]
    linarith
  set m1 := tubeMidpoint T1 with hm1
  set m2 := tubeMidpoint T2 with hm2
  have h_perp_dir : ‖d1 - inner ℝ d1 d2 • d2‖ = ‖cross d1 d2‖ :=
    perp_norm_eq_cross d1 d2 hd2
  have h_trans_mid : ‖(m1 - m2) - inner ℝ (m1 - m2) d2 • d2‖ ≤
      2 * ρ + (1 / 2 : ℝ) * ‖d1 - inner ℝ d1 d2 • d2‖ :=
    transverse_midpoint_bound_of_intersection hρ T1 T2 h_inter_nonempty
  have h_trans :
      ‖(m1 - m2) - inner ℝ (m1 - m2) d2 • d2‖ +
      (1 / 2 : ℝ) * ‖d1 - inner ℝ d1 d2 • d2‖ ≤ (1000 * K - 1) * ρ := by
    calc
      ‖(m1 - m2) - inner ℝ (m1 - m2) d2 • d2‖ +
          (1 / 2 : ℝ) * ‖d1 - inner ℝ d1 d2 • d2‖
        ≤ (2 * ρ + (1 / 2 : ℝ) * ‖d1 - inner ℝ d1 d2 • d2‖) +
            (1 / 2 : ℝ) * ‖d1 - inner ℝ d1 d2 • d2‖ := by gcongr
      _ = 2 * ρ + ‖d1 - inner ℝ d1 d2 • d2‖ := by ring
      _ = 2 * ρ + ‖cross d1 d2‖ := by rw [h_perp_dir]
      _ ≤ 2 * ρ + (176 : ℝ) / 3 * K * Real.pi * ρ := by gcongr
      _ ≤ (1000 * K - 1) * ρ := by
        have hpi : Real.pi ≤ 4 := Real.pi_le_four
        have hpi_pos : 0 < Real.pi := Real.pi_pos
        have hK_pos : 0 < K := by linarith
        have h1 : (176 : ℝ) / 3 * K * Real.pi ≤ (704 : ℝ) / 3 * K := by
          calc (176 : ℝ) / 3 * K * Real.pi
            = (176 : ℝ) / 3 * Real.pi * K := by ring
          _ ≤ (176 : ℝ) / 3 * 4 * K := by gcongr
          _ = (704 : ℝ) / 3 * K := by ring
        have h2 : 2 + (704 : ℝ) / 3 * K ≤ 1000 * K - 1 := by
          nlinarith
        have h3 : 2 * ρ + (176 : ℝ) / 3 * K * Real.pi * ρ ≤ (1000 * K - 1) * ρ := by
          have h4 : 2 * ρ + (176 : ℝ) / 3 * K * Real.pi * ρ ≤
              (2 + (704 : ℝ) / 3 * K) * ρ := by
            have h5 : (176 : ℝ) / 3 * K * Real.pi * ρ ≤ (704 : ℝ) / 3 * K * ρ := by
              gcongr
            nlinarith
          have h6 : (2 + (704 : ℝ) / 3 * K) * ρ ≤ (1000 * K - 1) * ρ := by
            gcongr <;> linarith
          linarith
        exact h3
  have hA : 4 * (3 : ℝ) + 1 ≤ 1000 * K := by
    nlinarith
  exact tube_contained_in_dilated_transverse_general
    hρ hρ1 (1000 * K) (3 : ℝ) hA (by norm_num) T1 T2 h_m1 h_m2 h_trans

/-- Quantitative containment from the frozen strong-overlap statement. -/
theorem strong_non_distinct_dilated_containment :
    StrongNonDistinctDilatedContainmentStatement := by
  intro rho hrho hrho1 T1 T2 h_m1 h_m2 K hK h_overlap
  exact strong_non_distinct_dilated_containment_lemma
    hrho hrho1 T1 T2 h_m1 h_m2 (hK := hK) h_overlap

end Kakeya.Streamlined.GeometricLemmas
