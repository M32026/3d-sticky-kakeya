import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.FrostmanFiberSize

/-!
# Frostman count for balanced slab groups

This is the cardinality and coarse-count algebra in (B.36)--(B.41).

Use exact incidence-mass retention and balanced average density to lower-bound
`q*M`, use the Frostman slab estimate to upper-bound `M`, and cancel to obtain
the lower bound for `theta*q`.

Do not perform geometric grouping or invoke the local hairbrush estimate.
-/

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

theorem hairbrush_balanced_frostman_count :
    HairbrushBalancedFrostmanCountStatement := by
  intro inputExponent balanceLoss frostmanExponent totalLoss coarseLoss
    h_inputExponent_pos h_balanceLoss_pos h_frostmanExponent_nonneg
    h_loss1 h_loss2

  let a : ℝ := totalLoss - (inputExponent + balanceLoss)
  have ha_pos : 0 < a := by linarith
  let b : ℝ := coarseLoss - (totalLoss + frostmanExponent)
  have hb_pos : 0 < b := by linarith

  let threshold1 : ℝ := Real.rpow (1 / 4) (1 / a)
  let threshold2 : ℝ := Real.rpow (1 / 600) (1 / b)
  let delta₀ : ℝ := min (1 / 1000) (min threshold1 threshold2)

  have hthreshold1_pos : 0 < threshold1 := by
    dsimp only [threshold1]
    exact Real.rpow_pos_of_pos (by norm_num) (1 / a)
  have hthreshold2_pos : 0 < threshold2 := by
    dsimp only [threshold2]
    exact Real.rpow_pos_of_pos (by norm_num) (1 / b)
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_le : delta₀ ≤ 1 / 1000 := min_le_left _ _

  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le, ?_⟩
  intro δ hδ hδle

  have hδ_le1 : δ ≤ 1 / 1000 := by linarith
  have hδ_pos : 0 < δ := hδ
  have hδ_le_one : δ ≤ 1 := by linarith

  have hδ_le_threshold1 : δ ≤ threshold1 := by
    have h : δ ≤ delta₀ := hδle
    have h2 : delta₀ ≤ threshold1 := by
      simp [delta₀] <;> exact min_le_right _ _
    linarith
  have hδ_le_threshold2 : δ ≤ threshold2 := by
    have h : δ ≤ delta₀ := hδle
    have h2 : delta₀ ≤ threshold2 := by
      simp [delta₀] <;> exact (min_le_right _ _).trans (min_le_right _ _)
    linarith

  -- δ^a ≤ 1/4
  have h_absorb1 : Real.rpow δ a ≤ 1 / 4 := by
    calc
      Real.rpow δ a ≤ Real.rpow threshold1 a := Real.rpow_le_rpow (by linarith) (by linarith) ha_pos.le
      _ = Real.rpow (Real.rpow (1 / 4) (1 / a)) a := by rfl
      _ = (1 / 4) := by
        have h_base1 : (0 : ℝ) ≤ 1 / 4 := by norm_num
        have h_rpow : Real.rpow (Real.rpow (1 / 4) (1 / a)) a = Real.rpow (1 / 4) ((1 / a) * a) :=
          (Real.rpow_mul h_base1 (1 / a) a).symm
        rw [h_rpow]
        have h : (1 / a) * a = 1 := by field_simp [ha_pos.ne'] <;> ring
        rw [h]
        norm_num

  -- δ^b ≤ 1/600
  have h_absorb2 : Real.rpow δ b ≤ 1 / 600 := by
    calc
      Real.rpow δ b ≤ Real.rpow threshold2 b := Real.rpow_le_rpow (by linarith) (by linarith) hb_pos.le
      _ = Real.rpow (Real.rpow (1 / 600) (1 / b)) b := by rfl
      _ = (1 / 600) := by
        have h_base2 : (0 : ℝ) ≤ 1 / 600 := by norm_num
        have h_rpow : Real.rpow (Real.rpow (1 / 600) (1 / b)) b = Real.rpow (1 / 600) ((1 / b) * b) :=
          (Real.rpow_mul h_base2 (1 / b) b).symm
        rw [h_rpow]
        have h : (1 / b) * b = 1 := by field_simp [hb_pos.ne'] <;> ring
        rw [h]
        norm_num

  -- 4 * δ^totalLoss ≤ δ^(inputExponent + balanceLoss)
  have h_const1 : 4 * Real.rpow δ totalLoss ≤ Real.rpow δ (inputExponent + balanceLoss) := by
    have h1 : Real.rpow δ (inputExponent + balanceLoss) = Real.rpow δ totalLoss * Real.rpow δ (-a) := by
      have h2 : inputExponent + balanceLoss = totalLoss + (-a) := by
        simp [a] <;> ring
      rw [h2]
      exact Real.rpow_add hδ_pos totalLoss (-a)
    rw [h1]
    have h3 : Real.rpow δ (-a) = (Real.rpow δ a)⁻¹ := Real.rpow_neg hδ_pos.le a
    rw [h3]
    have h4 : Real.rpow δ a ≤ 1 / 4 := h_absorb1
    have h5 : 0 < Real.rpow δ a := Real.rpow_pos_of_pos hδ_pos a
    have h6 : (Real.rpow δ a)⁻¹ ≥ 4 := by
      have h7 : 0 < Real.rpow δ a := h5
      have h8 : Real.rpow δ a ≤ 1 / 4 := h4
      have h9 : (Real.rpow δ a)⁻¹ ≥ (1 / 4 : ℝ)⁻¹ := by
        have h10 : 1 / (Real.rpow δ a) ≥ 1 / (1 / 4 : ℝ) := one_div_le_one_div_of_le (by positivity) h8
        simpa [one_div] using h10
      norm_num at h9
      exact h9
    have h8 : 0 < Real.rpow δ totalLoss := Real.rpow_pos_of_pos hδ_pos totalLoss
    nlinarith

  -- 600 * δ^coarseLoss ≤ δ^(totalLoss + frostmanExponent)
  have h_const2 : 600 * Real.rpow δ coarseLoss ≤ Real.rpow δ (totalLoss + frostmanExponent) := by
    have h1 : Real.rpow δ (totalLoss + frostmanExponent) = Real.rpow δ coarseLoss * Real.rpow δ (-b) := by
      have h2 : totalLoss + frostmanExponent = coarseLoss + (-b) := by
        simp [b] <;> ring
      rw [h2]
      exact Real.rpow_add hδ_pos coarseLoss (-b)
    rw [h1]
    have h3 : Real.rpow δ (-b) = (Real.rpow δ b)⁻¹ := Real.rpow_neg hδ_pos.le b
    rw [h3]
    have h4 : Real.rpow δ b ≤ 1 / 600 := h_absorb2
    have h5 : 0 < Real.rpow δ b := Real.rpow_pos_of_pos hδ_pos b
    have h6 : (Real.rpow δ b)⁻¹ ≥ 600 := by
      have h7 : 0 < Real.rpow δ b := h5
      have h8 : Real.rpow δ b ≤ 1 / 600 := h4
      have h9 : (Real.rpow δ b)⁻¹ ≥ (1 / 600 : ℝ)⁻¹ := by
        have h10 : 1 / (Real.rpow δ b) ≥ 1 / (1 / 600 : ℝ) := one_div_le_one_div_of_le (by positivity) h8
        simpa [one_div] using h10
      norm_num at h9
      exact h9
    have h8 : 0 < Real.rpow δ coarseLoss := Real.rpow_pos_of_pos hδ_pos coarseLoss
    nlinarith

  intro eta stopLoss densityFloor F Y hF_nonempty hFrost angular hAgg grouping balanced

  let V : ENNReal := Kakeya.deltaTubeVolume δ
  let q : ℕ := balanced.selectedCount
  let M : ℕ := balanced.typicalCard
  let D : ENNReal := balanced.typicalDensity
  let N : ENNReal := F.enncard
  let R : ℝ := angular.capRadius
  let θ : ℝ := angular.theta

  have hV_pos : 0 < V := (tube_volume_scaling.2.1 δ hδ hδ_le_one).1
  have hV_ne_zero : V ≠ 0 := hV_pos.ne'
  have hV_ne_top : V ≠ ⊤ := (tube_volume_scaling.2.1 δ hδ hδ_le_one).2
  have hN_pos : 0 < N := by
    simpa [N, Kakeya.TubeFamily.enncard] using hF_nonempty.card_pos
  have hN_ne_zero : N ≠ 0 := hN_pos.ne'
  have hN_ne_top : N ≠ ⊤ := by simp [N, Kakeya.TubeFamily.enncard]
  have hθ_pos : 0 < θ := by linarith [angular.delta_le_theta]
  have hR_pos : 0 < R := by linarith [angular.theta_le_capRadius]
  have hq_pos : 0 < q := balanced.selectedCount_pos
  have hM_pos : 0 < M := balanced.typicalCard_pos
  have hD_ne_zero : D ≠ 0 := balanced.typicalDensity_pos
  have hD_ne_top : D ≠ ⊤ := balanced.typicalDensity_ne_top

  -- Key lemma: shading mass ≤ family.enncard * V
  have h_shading_mass_le : ∀ (j : Fin grouping.groupCount),
      (grouping.shading j).mass ≤ (grouping.family j).enncard * V := by
    intro j
    let G := grouping.family j
    let Z := grouping.shading j
    have h1 : Z.mass ≤ ∑ T ∈ G, T.volume := by
      have h2 : Z.mass = ∑ T ∈ G, MeasureTheory.volume (Z.carrier T) := by rfl
      rw [h2]
      apply Finset.sum_le_sum
      intro T hT
      have h3 : Z.carrier T ⊆ T.carrier := Z.subset_tube hT
      exact MeasureTheory.measure_mono h3
    have h4 : ∀ T ∈ G, T.volume = V := by
      intro T _
      exact tube_volume_scaling.1 δ T
    have h5 : ∑ T ∈ G, T.volume = G.enncard * V := by
      have h6 : ∑ T ∈ G, T.volume = ∑ T ∈ G, V := by
        apply Finset.sum_congr rfl
        intro T hT
        exact h4 T hT
      rw [h6]
      simp [Kakeya.TubeFamily.enncard, Finset.sum_const]
      <;> ring
    rw [h5] at h1
    exact h1

  -- Pick a selected index
  let j0 : Fin q := ⟨0, hq_pos⟩
  let k0 : Fin grouping.groupCount := balanced.select j0

  -- D ≤ 1
  have hD_le_one : D ≤ 1 := by
    have h1 : D * (grouping.family k0).enncard * V ≤ (grouping.shading k0).mass :=
      balanced.density_lower j0
    have h2 : (grouping.shading k0).mass ≤ (grouping.family k0).enncard * V :=
      h_shading_mass_le k0
    let X := (grouping.family k0).enncard * V
    have hX_ne_zero : X ≠ 0 := by
      have h4 : (grouping.family k0).enncard ≠ 0 := by
        simpa [Kakeya.TubeFamily.enncard] using (grouping.family_nonempty k0).card_pos.ne'
      exact mul_ne_zero h4 hV_ne_zero
    have hX_ne_top : X ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by simp [Kakeya.TubeFamily.enncard]) hV_ne_top
    have h3 : D * X ≤ X := by simpa [X, mul_assoc] using h1.trans h2
    have h4 : D * X ≤ 1 * X := by simpa using h3
    exact (ENNReal.mul_le_mul_iff_left hX_ne_zero hX_ne_top).mp h4

  -- 1. typical_card_upper
  have h_typical_card_upper : (M : ENNReal) ≤
      ENNReal.ofReal (100 * Real.rpow δ (-frostmanExponent) * R) * N := by
    let S := grouping.slab k0
    have h_containment : ∀ T ∈ grouping.family k0, T.carrier ⊆ S.carrier :=
      grouping.slab_containment k0
    have h1 : (grouping.family k0).enncard ≤ F.containedCount S.carrier := by
      have h_filter : grouping.family k0 ⊆ F.filter fun T => T.carrier ⊆ S.carrier := by
        intro T hT
        exact Finset.mem_filter.mpr ⟨grouping.family_subset k0 hT, h_containment T hT⟩
      have h_card : (grouping.family k0).card ≤ (F.filter fun T => T.carrier ⊆ S.carrier).card :=
        Finset.card_le_card h_filter
      simpa [Kakeya.TubeFamily.enncard, Kakeya.TubeFamily.containedCount] using by exact_mod_cast h_card
    have hFrost' := hFrost S
    have h_vol : MeasureTheory.volume S.carrier ≤ ENNReal.ofReal (100 * R) := grouping.slab_volume k0
    have h4 : F.containedCount S.carrier ≤
        ENNReal.ofReal (Real.rpow δ (-frostmanExponent)) * MeasureTheory.volume S.carrier * N := hFrost'
    have h5 : F.containedCount S.carrier ≤
        ENNReal.ofReal (Real.rpow δ (-frostmanExponent)) * ENNReal.ofReal (100 * R) * N := by
      calc F.containedCount S.carrier
        ≤ ENNReal.ofReal (Real.rpow δ (-frostmanExponent)) * MeasureTheory.volume S.carrier * N := h4
      _ ≤ ENNReal.ofReal (Real.rpow δ (-frostmanExponent)) * ENNReal.ofReal (100 * R) * N := by gcongr
    have h6 : (M : ENNReal) ≤ (grouping.family k0).enncard := by
      have h7 : M ≤ (grouping.family k0).card := balanced.card_lower j0
      have h8 : (M : ENNReal) ≤ ((grouping.family k0).card : ENNReal) := by exact_mod_cast h7
      simpa [Kakeya.TubeFamily.enncard] using h8
    have h_pos1 : 0 ≤ Real.rpow δ (-frostmanExponent) := Real.rpow_nonneg hδ_pos.le _
    have h_pos2 : 0 ≤ 100 * R := by positivity
    have h_mul : ENNReal.ofReal (Real.rpow δ (-frostmanExponent)) * ENNReal.ofReal (100 * R) =
        ENNReal.ofReal (Real.rpow δ (-frostmanExponent) * (100 * R)) := by
      exact Eq.symm (ENNReal.ofReal_mul h_pos1)
    have h_comm : Real.rpow δ (-frostmanExponent) * (100 * R) = 100 * Real.rpow δ (-frostmanExponent) * R := by ring
    rw [h_mul, h_comm] at h5
    exact h6.trans (h1.trans h5)

  -- 2. selected_cardinality_lower
  have h_agg : Kakeya.realRpowENN δ inputExponent * N * V ≤ angular.shading.mass := hAgg

  have h_retention : Kakeya.realRpowENN δ balanceLoss * angular.shading.mass ≤
      ∑ j : Fin q, (grouping.shading (balanced.select j)).mass := balanced.mass_retention

  have h_rpow_add1 : Kakeya.realRpowENN δ balanceLoss * Kakeya.realRpowENN δ inputExponent =
      Kakeya.realRpowENN δ (inputExponent + balanceLoss) := by
    have h_nonneg1 : 0 ≤ Real.rpow δ balanceLoss := Real.rpow_nonneg hδ_pos.le _
    have h_nonneg2 : 0 ≤ Real.rpow δ inputExponent := Real.rpow_nonneg hδ_pos.le _
    have h_mul : ENNReal.ofReal (Real.rpow δ balanceLoss) * ENNReal.ofReal (Real.rpow δ inputExponent) =
        ENNReal.ofReal (Real.rpow δ balanceLoss * Real.rpow δ inputExponent) := by
      rw [← ENNReal.ofReal_mul h_nonneg1]
    have h_add : Real.rpow δ balanceLoss * Real.rpow δ inputExponent =
        Real.rpow δ (balanceLoss + inputExponent) := by
      exact (Real.rpow_add hδ_pos balanceLoss inputExponent).symm
    have h_comm : balanceLoss + inputExponent = inputExponent + balanceLoss := by ring
    simp only [Kakeya.realRpowENN]
    rw [h_mul, h_add, h_comm]

  have h_eq1 : Kakeya.realRpowENN δ (inputExponent + balanceLoss) * N * V =
      Kakeya.realRpowENN δ balanceLoss * (Kakeya.realRpowENN δ inputExponent * N * V) := by
    rw [h_rpow_add1.symm]
    ring
  have h_sum_lower : Kakeya.realRpowENN δ (inputExponent + balanceLoss) * N * V ≤
      ∑ j : Fin q, (grouping.shading (balanced.select j)).mass := by
    calc Kakeya.realRpowENN δ (inputExponent + balanceLoss) * N * V
      = Kakeya.realRpowENN δ balanceLoss * (Kakeya.realRpowENN δ inputExponent * N * V) := h_eq1
    _ ≤ Kakeya.realRpowENN δ balanceLoss * angular.shading.mass := by gcongr
    _ ≤ ∑ j : Fin q, (grouping.shading (balanced.select j)).mass := h_retention

  have h_each_upper : ∀ j : Fin q,
      (grouping.shading (balanced.select j)).mass ≤ 4 * D * (M : ENNReal) * V := by
    intro j
    let k := balanced.select j
    have h_card : (grouping.family k).enncard ≤ 2 * (M : ENNReal) := by
      have h1 : (grouping.family k).card < 2 * M := balanced.card_upper j
      have h2 : (grouping.family k).card ≤ 2 * M := le_of_lt h1
      have h3 : ((grouping.family k).card : ENNReal) ≤ ((2 * M : ℕ) : ENNReal) := by exact_mod_cast h2
      have h4 : ((2 * M : ℕ) : ENNReal) = 2 * (M : ENNReal) := by
        simp [Nat.cast_mul] <;> norm_num
      rw [h4] at h3
      simpa [Kakeya.TubeFamily.enncard] using h3
    have h_density : (grouping.shading k).mass < 2 * D * (grouping.family k).enncard * V :=
      balanced.density_upper j
    have h5 : (grouping.shading k).mass ≤ 2 * D * (2 * (M : ENNReal)) * V :=
      le_trans (le_of_lt h_density) (by gcongr)
    have h6 : 2 * D * (2 * (M : ENNReal)) * V = 4 * D * (M : ENNReal) * V := by
      simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
    rw [h6] at h5
    exact h5

  have h_sum_upper : ∑ j : Fin q, (grouping.shading (balanced.select j)).mass ≤
      (q : ENNReal) * (4 * D * (M : ENNReal) * V) := by
    calc ∑ j : Fin q, (grouping.shading (balanced.select j)).mass
      ≤ ∑ j : Fin q, 4 * D * (M : ENNReal) * V := Finset.sum_le_sum fun j _ => h_each_upper j
    _ = (q : ENNReal) * (4 * D * (M : ENNReal) * V) := by
      simp [Finset.sum_const] <;> ring

  have h9 : Kakeya.realRpowENN δ (inputExponent + balanceLoss) * N ≤ 4 * D * (q : ENNReal) * (M : ENNReal) := by
    have h10 : Kakeya.realRpowENN δ (inputExponent + balanceLoss) * N * V ≤
        (q : ENNReal) * (4 * D * (M : ENNReal) * V) := h_sum_lower.trans h_sum_upper
    have h11 : (q : ENNReal) * (4 * D * (M : ENNReal) * V) =
        (4 * D * (q : ENNReal) * (M : ENNReal)) * V := by
      simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
    rw [h11] at h10
    exact (ENNReal.mul_le_mul_iff_left hV_ne_zero hV_ne_top).mp h10

  have h10 : Kakeya.realRpowENN δ (inputExponent + balanceLoss) * N ≤ 4 * (q : ENNReal) * (M : ENNReal) := by
    calc Kakeya.realRpowENN δ (inputExponent + balanceLoss) * N
      ≤ 4 * D * (q : ENNReal) * (M : ENNReal) := h9
    _ ≤ 4 * (1 : ENNReal) * (q : ENNReal) * (M : ENNReal) := by
      gcongr
      <;> exact hD_le_one
    _ = 4 * (q : ENNReal) * (M : ENNReal) := by simp

  have h_const1_enn : 4 * Kakeya.realRpowENN δ totalLoss ≤ Kakeya.realRpowENN δ (inputExponent + balanceLoss) := by
    have h : 4 * Real.rpow δ totalLoss ≤ Real.rpow δ (inputExponent + balanceLoss) := h_const1
    have h' : ENNReal.ofReal (4 * Real.rpow δ totalLoss) ≤ ENNReal.ofReal (Real.rpow δ (inputExponent + balanceLoss)) :=
      ENNReal.ofReal_mono h
    have h'' : ENNReal.ofReal (4 * Real.rpow δ totalLoss) = 4 * Kakeya.realRpowENN δ totalLoss := by
      simp [Kakeya.realRpowENN, ← ENNReal.ofReal_mul (by positivity)]
      <;> norm_num
    rw [h''] at h'
    exact h'

  have h12 : 4 * Kakeya.realRpowENN δ totalLoss * N ≤ 4 * (q : ENNReal) * (M : ENNReal) := by
    calc 4 * Kakeya.realRpowENN δ totalLoss * N
      ≤ Kakeya.realRpowENN δ (inputExponent + balanceLoss) * N := by gcongr
    _ ≤ 4 * (q : ENNReal) * (M : ENNReal) := h10

  have h_selected_cardinality_lower : Kakeya.realRpowENN δ totalLoss * N ≤ (q : ENNReal) * (M : ENNReal) := by
    have h13a : 4 * Kakeya.realRpowENN δ totalLoss * N = 4 * (Kakeya.realRpowENN δ totalLoss * N) := by ring
    have h13b : 4 * (q : ENNReal) * (M : ENNReal) = 4 * ((q : ENNReal) * (M : ENNReal)) := by ring
    have h13 : 4 * (Kakeya.realRpowENN δ totalLoss * N) ≤ 4 * ((q : ENNReal) * (M : ENNReal)) := by
      rw [h13a, h13b] at h12
      exact h12
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h13

  -- 3. coarse_count_lower
  have h14 : Kakeya.realRpowENN δ totalLoss * N ≤ (q : ENNReal) * (M : ENNReal) := h_selected_cardinality_lower
  have h15 : (M : ENNReal) ≤ ENNReal.ofReal (100 * Real.rpow δ (-frostmanExponent) * R) * N := h_typical_card_upper

  have h16 : Kakeya.realRpowENN δ totalLoss * N ≤
      (q : ENNReal) * (ENNReal.ofReal (100 * Real.rpow δ (-frostmanExponent) * R) * N) := by
    calc Kakeya.realRpowENN δ totalLoss * N
      ≤ (q : ENNReal) * (M : ENNReal) := h14
    _ ≤ (q : ENNReal) * (ENNReal.ofReal (100 * Real.rpow δ (-frostmanExponent) * R) * N) := by gcongr

  have h17 : Kakeya.realRpowENN δ totalLoss ≤
      (q : ENNReal) * ENNReal.ofReal (100 * Real.rpow δ (-frostmanExponent) * R) := by
    have h18 : (q : ENNReal) * (ENNReal.ofReal (100 * Real.rpow δ (-frostmanExponent) * R) * N) =
        ((q : ENNReal) * ENNReal.ofReal (100 * Real.rpow δ (-frostmanExponent) * R)) * N := by
      simp [mul_assoc] <;> ring
    rw [h18] at h16
    exact (ENNReal.mul_le_mul_iff_left hN_ne_zero hN_ne_top).mp h16

  have h_rpow_mul2 : Kakeya.realRpowENN δ (-frostmanExponent) * Kakeya.realRpowENN δ frostmanExponent = 1 := by
    have h_nonneg1 : 0 ≤ Real.rpow δ (-frostmanExponent) := Real.rpow_nonneg hδ_pos.le _
    have h_nonneg2 : 0 ≤ Real.rpow δ frostmanExponent := Real.rpow_nonneg hδ_pos.le _
    have h_mul : ENNReal.ofReal (Real.rpow δ (-frostmanExponent)) * ENNReal.ofReal (Real.rpow δ frostmanExponent) =
        ENNReal.ofReal (Real.rpow δ (-frostmanExponent) * Real.rpow δ frostmanExponent) := by
      rw [← ENNReal.ofReal_mul h_nonneg1]
    have h_add : Real.rpow δ (-frostmanExponent) * Real.rpow δ frostmanExponent =
        Real.rpow δ ((-frostmanExponent) + frostmanExponent) := by
      exact (Real.rpow_add hδ_pos (-frostmanExponent) frostmanExponent).symm
    have h_zero : (-frostmanExponent) + frostmanExponent = 0 := by ring
    simp only [Kakeya.realRpowENN]
    rw [h_mul, h_add, h_zero]
    simp

  have h19 : Kakeya.realRpowENN δ (totalLoss + frostmanExponent) ≤
      (q : ENNReal) * ENNReal.ofReal (100 * R) := by
    have h20 : Kakeya.realRpowENN δ totalLoss * Kakeya.realRpowENN δ frostmanExponent ≤
        (q : ENNReal) * ENNReal.ofReal (100 * Real.rpow δ (-frostmanExponent) * R) * Kakeya.realRpowENN δ frostmanExponent := by
      gcongr
    have h21 : Kakeya.realRpowENN δ totalLoss * Kakeya.realRpowENN δ frostmanExponent =
        Kakeya.realRpowENN δ (totalLoss + frostmanExponent) := by
      have h_nonneg1 : 0 ≤ Real.rpow δ totalLoss := Real.rpow_nonneg hδ_pos.le _
      have h_nonneg2 : 0 ≤ Real.rpow δ frostmanExponent := Real.rpow_nonneg hδ_pos.le _
      have h_mul : ENNReal.ofReal (Real.rpow δ totalLoss) * ENNReal.ofReal (Real.rpow δ frostmanExponent) =
          ENNReal.ofReal (Real.rpow δ totalLoss * Real.rpow δ frostmanExponent) := by
        rw [← ENNReal.ofReal_mul h_nonneg1]
      have h_add : Real.rpow δ totalLoss * Real.rpow δ frostmanExponent =
          Real.rpow δ (totalLoss + frostmanExponent) := by
        exact (Real.rpow_add hδ_pos totalLoss frostmanExponent).symm
      simp only [Kakeya.realRpowENN]
      rw [h_mul, h_add]
    have h_pos1 : 0 ≤ Real.rpow δ (-frostmanExponent) := Real.rpow_nonneg hδ_pos.le _
    have h_pos2 : 0 ≤ 100 * R := by positivity
    have h_real : 100 * Real.rpow δ (-frostmanExponent) * R = Real.rpow δ (-frostmanExponent) * (100 * R) := by ring
    have h22 : ENNReal.ofReal (100 * Real.rpow δ (-frostmanExponent) * R) =
        ENNReal.ofReal (100 * R) * Kakeya.realRpowENN δ (-frostmanExponent) := by
      rw [h_real]
      have h : ENNReal.ofReal (Real.rpow δ (-frostmanExponent) * (100 * R)) =
          ENNReal.ofReal (Real.rpow δ (-frostmanExponent)) * ENNReal.ofReal (100 * R) := by
        rw [← ENNReal.ofReal_mul h_pos1]
      rw [h]
      simp [Kakeya.realRpowENN, mul_comm]
      <;> abel
    rw [h21, h22] at h20
    have h23 : (q : ENNReal) * (ENNReal.ofReal (100 * R) * Kakeya.realRpowENN δ (-frostmanExponent)) * Kakeya.realRpowENN δ frostmanExponent =
        (q : ENNReal) * ENNReal.ofReal (100 * R) := by
      have h_assoc : (q : ENNReal) * (ENNReal.ofReal (100 * R) * Kakeya.realRpowENN δ (-frostmanExponent)) * Kakeya.realRpowENN δ frostmanExponent =
          (q : ENNReal) * (ENNReal.ofReal (100 * R) * (Kakeya.realRpowENN δ (-frostmanExponent) * Kakeya.realRpowENN δ frostmanExponent)) := by
        calc (q : ENNReal) * (ENNReal.ofReal (100 * R) * Kakeya.realRpowENN δ (-frostmanExponent)) * Kakeya.realRpowENN δ frostmanExponent
          = (q : ENNReal) * ((ENNReal.ofReal (100 * R) * Kakeya.realRpowENN δ (-frostmanExponent)) * Kakeya.realRpowENN δ frostmanExponent) := by rw [mul_assoc]
        _ = (q : ENNReal) * (ENNReal.ofReal (100 * R) * (Kakeya.realRpowENN δ (-frostmanExponent) * Kakeya.realRpowENN δ frostmanExponent)) := by
          rw [mul_assoc (ENNReal.ofReal (100 * R))]
      rw [h_assoc, h_rpow_mul2]
      <;> simp
    rw [h23] at h20
    exact h20

  have hR_le : R ≤ 6 * θ := angular.capRadius_le_six_theta
  have h23 : 100 * R ≤ 600 * θ := by linarith
  have h24 : ENNReal.ofReal (100 * R) ≤ ENNReal.ofReal (600 * θ) := ENNReal.ofReal_mono h23

  have h25 : Kakeya.realRpowENN δ (totalLoss + frostmanExponent) ≤
      (q : ENNReal) * ENNReal.ofReal (600 * θ) := by
    calc Kakeya.realRpowENN δ (totalLoss + frostmanExponent)
      ≤ (q : ENNReal) * ENNReal.ofReal (100 * R) := h19
    _ ≤ (q : ENNReal) * ENNReal.ofReal (600 * θ) := by gcongr

  have h_posθ : 0 ≤ θ := by linarith
  have h26 : ENNReal.ofReal (600 * θ) = 600 * ENNReal.ofReal θ := by
    simp [← ENNReal.ofReal_mul h_posθ] <;> norm_num

  rw [h26] at h25
  have h25' : Kakeya.realRpowENN δ (totalLoss + frostmanExponent) ≤ 600 * ENNReal.ofReal θ * (q : ENNReal) := by
    have h_comm : (q : ENNReal) * (600 * ENNReal.ofReal θ) = 600 * ENNReal.ofReal θ * (q : ENNReal) := by
      simp [mul_assoc, mul_comm]
      <;> ring
    rw [h_comm] at h25
    exact h25

  have h_const2_enn : 600 * Kakeya.realRpowENN δ coarseLoss ≤ Kakeya.realRpowENN δ (totalLoss + frostmanExponent) := by
    have h : 600 * Real.rpow δ coarseLoss ≤ Real.rpow δ (totalLoss + frostmanExponent) := h_const2
    have h' : ENNReal.ofReal (600 * Real.rpow δ coarseLoss) ≤ ENNReal.ofReal (Real.rpow δ (totalLoss + frostmanExponent)) :=
      ENNReal.ofReal_mono h
    have h'' : ENNReal.ofReal (600 * Real.rpow δ coarseLoss) = 600 * Kakeya.realRpowENN δ coarseLoss := by
      simp [Kakeya.realRpowENN, ← ENNReal.ofReal_mul (by positivity)]
      <;> norm_num
    rw [h''] at h'
    exact h'

  have h27 : 600 * Kakeya.realRpowENN δ coarseLoss ≤ 600 * ENNReal.ofReal θ * (q : ENNReal) := by
    calc 600 * Kakeya.realRpowENN δ coarseLoss
      ≤ Kakeya.realRpowENN δ (totalLoss + frostmanExponent) := h_const2_enn
    _ ≤ 600 * ENNReal.ofReal θ * (q : ENNReal) := h25'

  have h_coarse_count_lower : Kakeya.realRpowENN δ coarseLoss ≤ ENNReal.ofReal θ * (q : ENNReal) := by
    have h27' : 600 * Kakeya.realRpowENN δ coarseLoss ≤ 600 * (ENNReal.ofReal θ * (q : ENNReal)) := by
      have h_assoc : 600 * ENNReal.ofReal θ * (q : ENNReal) = 600 * (ENNReal.ofReal θ * (q : ENNReal)) := by
        simp [mul_assoc]
      rw [h_assoc] at h27
      exact h27
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h27'

  exact ⟨h_typical_card_upper, h_selected_cardinality_lower, h_coarse_count_lower⟩

end Kakeya.Assouad
