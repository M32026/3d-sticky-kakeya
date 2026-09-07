module

/-
  TFullUpperBound: cardinality bound for a5FullFineFamily.

  Proves |T_full| ≤ Δ^{-(4s+3ε)} using the fine-failure/source-family route.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AssemblyNumericalHypotheses
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.TFullUpperBound

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.AssemblyNumerical

lemma t_full_upper_bound
    {Δ δ_n δ s u ε εA ρ_T : ℝ}
    {T_source : Finset FineTube}
    (hΔ_pos : 0 < Δ)
    (hδ_n_pos : 0 < δ_n)
    (hδ_pos : 0 < δ)
    (hδ_n_eq2 : δ_n = Δ ^ 2)
    (hδ_le_δ_n : δ ≤ δ_n)
    (hδ_n_le_4δ : δ_n ≤ 4 * δ)
    (hεA_pos : 0 < εA)
    (hεA_le_50 : εA ≤ ε / 50)
    (hρ_T_nonneg : 0 ≤ ρ_T)
    (hρ_T_le_20 : ρ_T ≤ ε / 20)
    (hs_pos : 0 < s)
    (h_num_bounds : AssemblyNumericalBounds Δ s u ε)
    (T_original allTubes : Set AffineLine)
    (hT_original_sub_allTubes : T_original ⊆ allTubes)
    (h_fine_failure : ¬ ENNReal.ofReal (Real.rpow δ (-(2 * s + εA))) ≤
        (Metric.externalCoveringNumber δ.toNNReal allTubes : ENNReal))
    (hT_source_bound : (T_source.card : ENNReal) ≤
        ENNReal.ofReal (Real.rpow δ_n (-ρ_T)) *
        (Metric.externalCoveringNumber δ_n.toNNReal T_original : ENNReal))
  : ∀ (a4 : A4_Output_v2 Δ δ_n s u ε T_source),
      (a5FullFineFamily Δ δ_n s u ε a4.Qset a4.perSquare).card ≤
        Real.rpow Δ (-(4 * s + 3 * ε)) := by
  intro a4

  -- Step 1: T_full ⊆ T_source
  have h_sub : (a5FullFineFamily Δ δ_n s u ε a4.Qset a4.perSquare) ⊆ T_source :=
    a4.hT_full_subset_source
  have h_card_le : (a5FullFineFamily Δ δ_n s u ε a4.Qset a4.perSquare).card ≤ T_source.card :=
    Finset.card_le_card h_sub

  -- Step 2: toNNReal monotonicity
  have h1_toNNReal : δ.toNNReal ≤ δ_n.toNNReal := by
    have hδ_nonneg : 0 ≤ δ := by linarith
    have hδn_nonneg : 0 ≤ δ_n := by linarith
    have h : δ ≤ δ_n := hδ_le_δ_n
    exact Real.toNNReal_mono h

  -- Step 3: Scale + subset monotonicity
  have hNcover_chain : (Metric.externalCoveringNumber δ_n.toNNReal T_original : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal allTubes : ENNReal) := by
    have h_scale : (Metric.externalCoveringNumber δ_n.toNNReal T_original : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal T_original : ENNReal) := by
      have h : Metric.externalCoveringNumber δ_n.toNNReal T_original ≤ Metric.externalCoveringNumber δ.toNNReal T_original :=
        Metric.externalCoveringNumber_anti h1_toNNReal
      simpa using h
    have h_subset : (Metric.externalCoveringNumber δ.toNNReal T_original : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal allTubes : ENNReal) := by
      have h : Metric.externalCoveringNumber δ.toNNReal T_original ≤ Metric.externalCoveringNumber δ.toNNReal allTubes :=
        Metric.externalCoveringNumber_mono_set hT_original_sub_allTubes
      simpa using h
    exact le_trans h_scale h_subset

  -- Step 4: Fine failure
  have hNcover_lt : (Metric.externalCoveringNumber δ_n.toNNReal T_original : ENNReal) <
      ENNReal.ofReal (Real.rpow δ (-(2 * s + εA))) :=
    lt_of_le_of_lt hNcover_chain (lt_of_not_ge h_fine_failure)

  -- Step 5: Combine source bound
  have h_pos1 : 0 ≤ Real.rpow δ_n (-ρ_T) := Real.rpow_nonneg hδ_n_pos.le _
  have h_ofReal_pos : 0 < ENNReal.ofReal (Real.rpow δ_n (-ρ_T)) := by
    apply ENNReal.ofReal_pos.mpr
    exact Real.rpow_pos_of_pos hδ_n_pos _
  have h_source_lt : (T_source.card : ENNReal) <
      ENNReal.ofReal (Real.rpow δ_n (-ρ_T)) *
      ENNReal.ofReal (Real.rpow δ (-(2 * s + εA))) := by
    calc (T_source.card : ENNReal)
      ≤ ENNReal.ofReal (Real.rpow δ_n (-ρ_T)) *
          (Metric.externalCoveringNumber δ_n.toNNReal T_original : ENNReal) := hT_source_bound
    _ < ENNReal.ofReal (Real.rpow δ_n (-ρ_T)) *
          ENNReal.ofReal (Real.rpow δ (-(2 * s + εA))) := by
        have h_a_ne_zero : ENNReal.ofReal (Real.rpow δ_n (-ρ_T)) ≠ 0 := h_ofReal_pos.ne'
        have h_a_ne_top : ENNReal.ofReal (Real.rpow δ_n (-ρ_T)) ≠ ⊤ := by
          simp [h_ofReal_pos] <;> positivity
        exact ENNReal.mul_lt_mul_right h_a_ne_zero h_a_ne_top hNcover_lt

  -- Step 6: Product of ofReal
  have h_pos2 : 0 ≤ Real.rpow δ (-(2 * s + εA)) := Real.rpow_nonneg hδ_pos.le _
  have h_mul_real : Real.rpow δ_n (-ρ_T) * Real.rpow δ (-(2 * s + εA)) ≥ 0 :=
    mul_nonneg h_pos1 h_pos2
  have h_ofReal_mul : ENNReal.ofReal (Real.rpow δ_n (-ρ_T)) *
      ENNReal.ofReal (Real.rpow δ (-(2 * s + εA))) =
      ENNReal.ofReal (Real.rpow δ_n (-ρ_T) * Real.rpow δ (-(2 * s + εA))) := by
    have h : ENNReal.ofReal (Real.rpow δ_n (-ρ_T) * Real.rpow δ (-(2 * s + εA))) =
        ENNReal.ofReal (Real.rpow δ_n (-ρ_T)) * ENNReal.ofReal (Real.rpow δ (-(2 * s + εA))) := by
      exact ENNReal.ofReal_mul h_pos1
    exact h.symm

  -- Step 7: Convert to Real inequality
  have h_card_eq : (T_source.card : ENNReal) = ENNReal.ofReal (T_source.card : ℝ) := by
    simp
  rw [h_card_eq] at h_source_lt
  rw [h_ofReal_mul] at h_source_lt
  have h_real_lt : (T_source.card : ℝ) <
      Real.rpow δ_n (-ρ_T) * Real.rpow δ (-(2 * s + εA)) := by
    have h_pos3a : 0 < Real.rpow δ_n (-ρ_T) := Real.rpow_pos_of_pos hδ_n_pos _
    have h_pos3b : 0 < Real.rpow δ (-(2 * s + εA)) := Real.rpow_pos_of_pos hδ_pos _
    have h_pos3 : 0 < Real.rpow δ_n (-ρ_T) * Real.rpow δ (-(2 * s + εA)) :=
      mul_pos h_pos3a h_pos3b
    have h_iff : ENNReal.ofReal (T_source.card : ℝ) <
        ENNReal.ofReal (Real.rpow δ_n (-ρ_T) * Real.rpow δ (-(2 * s + εA))) ↔
        (T_source.card : ℝ) < Real.rpow δ_n (-ρ_T) * Real.rpow δ (-(2 * s + εA)) :=
      ENNReal.ofReal_lt_ofReal_iff h_pos3
    exact h_iff.mp h_source_lt

  -- Step 8: Factor-4 conversion: δ^{-(2s+εA)} ≤ 4^{2s+εA} · δ_n^{-(2s+εA)}
  set a : ℝ := 2 * s + εA with ha_def
  have ha_pos : 0 < a := by linarith
  have hδ_ge : δ ≥ δ_n / 4 := by linarith
  have hδ_n4_pos : 0 < δ_n / 4 := by positivity

  have h_rpow1 : Real.rpow δ (-a) ≤ Real.rpow (δ_n / 4) (-a) :=
    Real.rpow_le_rpow_of_nonpos hδ_n4_pos hδ_ge (by linarith)

  have h_rpow2 : Real.rpow (δ_n / 4) (-a) =
      (4 : ℝ)^a * Real.rpow δ_n (-a) := by
    have hpos1 : 0 < Real.rpow δ_n a := Real.rpow_pos_of_pos hδ_n_pos _
    have hpos2 : 0 < Real.rpow (4 : ℝ) a := Real.rpow_pos_of_pos (by norm_num) _
    have h1 : Real.rpow (δ_n / 4) a = Real.rpow δ_n a / Real.rpow (4 : ℝ) a := by
      have hdiv : ∀ (z : ℝ), Real.rpow ((δ_n) / 4) z =
          Real.rpow δ_n z / Real.rpow (4 : ℝ) z := by
        intro z
        have h := Real.div_rpow (show (0 : ℝ) ≤ δ_n by linarith) (show (0 : ℝ) ≤ 4 by norm_num) z
        simpa using h
      exact hdiv a
    have h2 : Real.rpow (δ_n / 4) (-a) = (Real.rpow (δ_n / 4) a)⁻¹ :=
      Real.rpow_neg (by positivity) _
    rw [h2, h1]
    have h3 : (Real.rpow δ_n a / Real.rpow (4 : ℝ) a)⁻¹ =
        Real.rpow (4 : ℝ) a / Real.rpow δ_n a := by
      field_simp [hpos1.ne', hpos2.ne']
    rw [h3]
    have h4 : Real.rpow (4 : ℝ) a / Real.rpow δ_n a =
        (4 : ℝ)^a * Real.rpow δ_n (-a) := by
      have h5 : Real.rpow δ_n (-a) = (Real.rpow δ_n a)⁻¹ := Real.rpow_neg (by positivity) _
      have h6 : Real.rpow (4 : ℝ) a / Real.rpow δ_n a =
          Real.rpow (4 : ℝ) a * (Real.rpow δ_n a)⁻¹ := by
        field_simp [hpos1.ne'] <;> ring
      rw [h6, h5]
      <;> rfl
    exact h4

  have h10 : Real.rpow δ (-a) ≤ (4 : ℝ)^a * Real.rpow δ_n (-a) := by
    calc Real.rpow δ (-a)
      ≤ Real.rpow (δ_n / 4) (-a) := h_rpow1
    _ = (4 : ℝ)^a * Real.rpow δ_n (-a) := h_rpow2

  -- Step 9: Combine
  have h14 : (T_source.card : ℝ) <
      (4 : ℝ)^a * Real.rpow δ_n (-(a + ρ_T)) := by
    have h15 : Real.rpow δ_n (-ρ_T) * Real.rpow δ (-a) ≤
        Real.rpow δ_n (-ρ_T) * ((4 : ℝ)^a * Real.rpow δ_n (-a)) := by
      gcongr
      <;> exact h10
    have h17 : Real.rpow δ_n (-ρ_T) * Real.rpow δ_n (-a) =
        Real.rpow δ_n (-(a + ρ_T)) := by
      have h_add : Real.rpow δ_n (-ρ_T) * Real.rpow δ_n (-a) =
          Real.rpow δ_n ((-ρ_T) + (-a)) :=
        (Real.rpow_add hδ_n_pos _ _).symm
      rw [h_add] <;> ring_nf
    have h16 : Real.rpow δ_n (-ρ_T) * ((4 : ℝ)^a * Real.rpow δ_n (-a)) =
        (4 : ℝ)^a * Real.rpow δ_n (-(a + ρ_T)) := by
      have h_assoc : Real.rpow δ_n (-ρ_T) * ((4 : ℝ)^a * Real.rpow δ_n (-a)) =
          (4 : ℝ)^a * (Real.rpow δ_n (-ρ_T) * Real.rpow δ_n (-a)) := by ring
      rw [h_assoc, h17]
      <;> ring
    calc (T_source.card : ℝ)
      < Real.rpow δ_n (-ρ_T) * Real.rpow δ (-a) := h_real_lt
    _ ≤ (4 : ℝ)^a * Real.rpow δ_n (-(a + ρ_T)) := by
        rw [h16] at h15 <;> exact h15

  -- Step 10: δ_n = Δ²
  have h18 : Real.rpow δ_n (-(a + ρ_T)) =
      Real.rpow Δ (-(2 * a + 2 * ρ_T)) := by
    rw [hδ_n_eq2]
    have h_d2 : (Δ ^ 2 : ℝ) = Real.rpow Δ 2 := by
      simp [Real.rpow_two]
    rw [h_d2]
    have h19 : Real.rpow (Real.rpow Δ 2) (-(a + ρ_T)) =
        Real.rpow Δ (2 * (-(a + ρ_T))) := by
      have h20 := Real.rpow_mul hΔ_pos.le 2 (-(a + ρ_T))
      exact h20.symm
    rw [h19] <;> ring_nf

  rw [h18] at h14

  -- Step 11: Numerical absorption
  have hεA_nonneg : 0 ≤ εA := by linarith
  have h_absorb : (4 : ℝ)^a ≤
      Real.rpow Δ (-(3 * ε - 2 * εA - 2 * ρ_T)) :=
    h_num_bounds.h_absorb_4s3ε εA ρ_T hεA_nonneg hεA_le_50 hρ_T_nonneg hρ_T_le_20

  have h_rpow_nonneg : 0 ≤ Real.rpow Δ (-(2 * a + 2 * ρ_T)) :=
    Real.rpow_nonneg hΔ_pos.le _

  have h_final : (4 : ℝ)^a * Real.rpow Δ (-(2 * a + 2 * ρ_T)) ≤
      Real.rpow Δ (-(4 * s + 3 * ε)) := by
    have h21 : Real.rpow Δ (-(3 * ε - 2 * εA - 2 * ρ_T)) *
        Real.rpow Δ (-(2 * a + 2 * ρ_T)) =
        Real.rpow Δ (-(4 * s + 3 * ε)) := by
      have h_add : Real.rpow Δ (-(3 * ε - 2 * εA - 2 * ρ_T)) *
          Real.rpow Δ (-(2 * a + 2 * ρ_T)) =
          Real.rpow Δ ((-(3 * ε - 2 * εA - 2 * ρ_T)) + (-(2 * a + 2 * ρ_T))) :=
        (Real.rpow_add hΔ_pos _ _).symm
      rw [h_add]
      have h_exp : (-(3 * ε - 2 * εA - 2 * ρ_T)) + (-(2 * a + 2 * ρ_T)) = -(4 * s + 3 * ε) := by
        simp only [ha_def] <;> ring
      rw [h_exp]
    have h_mul_le : (4 : ℝ)^a * Real.rpow Δ (-(2 * a + 2 * ρ_T)) ≤
        Real.rpow Δ (-(3 * ε - 2 * εA - 2 * ρ_T)) * Real.rpow Δ (-(2 * a + 2 * ρ_T)) :=
      mul_le_mul_of_nonneg_right h_absorb h_rpow_nonneg
    rw [h21] at h_mul_le
    exact h_mul_le

  have h_card_le' : (T_source.card : ℝ) ≤ Real.rpow Δ (-(4 * s + 3 * ε)) :=
    le_of_lt (lt_of_lt_of_le h14 h_final)

  have h_main : ((a5FullFineFamily Δ δ_n s u ε a4.Qset a4.perSquare).card : ℝ) ≤
      (T_source.card : ℝ) := by
    exact_mod_cast h_card_le

  exact_mod_cast le_trans h_main h_card_le'

end DirecretisedFurstenbergEstimate.FrontEndLemmas.TFullUpperBound
