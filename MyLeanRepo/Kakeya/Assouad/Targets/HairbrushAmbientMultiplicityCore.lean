import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Hairbrush.MultiplicityPruning
import MyLeanRepo.Kakeya.Assouad.Hairbrush.OverlapLemmas
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.LogAbsorption

/-!
# Main proof skeleton for hairbrush ambient multiplicity core

Implements (B.11)--(B.15): dyadic multiplicity pigeonhole, layer density
definition, and individual-density dyadic pigeonhole for hair selection.
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

namespace Kakeya.Assouad

-- ============================================================================
-- nat_log_absorbed helper (copied from LogHelpers.lean)
-- ============================================================================

private lemma nat_ceil_le_add_one {x : ℝ} (hx : 0 ≤ x) :
    (Nat.ceil x : ℝ) ≤ x + 1 := by
  by_cases hx0 : x = 0
  · rw [hx0]; norm_num
  · have hx_ne : x ≠ 0 := hx0
    have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx_ne)
    let n : ℕ := Nat.ceil x
    have hn_pos : 0 < n := by
      by_contra h
      have h' : n = 0 := by omega
      have h_le : x ≤ (n : ℝ) := Nat.le_ceil x
      have h_zero : (n : ℝ) = 0 := by exact_mod_cast h'
      rw [h_zero] at h_le; linarith
    have h5 : x ≤ (n : ℝ) := Nat.le_ceil x
    by_contra h2
    have h3 : (n : ℝ) > x + 1 := by linarith
    have h6 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := Nat.cast_pred hn_pos
    have h8 : x ≤ ((n - 1 : ℕ) : ℝ) := by rw [h6]; linarith
    have h9 : Nat.ceil x ≤ n - 1 := by rw [Nat.ceil_le]; exact h8
    have h10 : n ≤ n - 1 := by simpa [n] using h9
    omega

private lemma nat_log_absorbed (C : ℝ) (hC : 0 < C) (eps : ℝ) (heps : 0 < eps) :
    ∃ δ₀, 0 < δ₀ ∧ δ₀ ≤ Real.exp (-1) ∧ ∀ δ, 0 < δ → δ ≤ δ₀ →
      (Nat.ceil (C * Real.log (1/δ)) + 1 : ℝ) ≤ Real.rpow δ (-eps) := by
  have h_main := exists_delta_log_absorbed (C + 2) (by linarith) (hB := heps) (n := 1) (by norm_num)
  rcases h_main with ⟨δ₁, hδ₁_pos, hδ₁_le1, hδ₁⟩
  let δ₂ : ℝ := Real.exp (-1)
  have hδ₂_pos : 0 < δ₂ := by positivity
  let δ₀ : ℝ := min δ₁ δ₂
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le_exp : δ₀ ≤ Real.exp (-1) := by
    have h3 : δ₀ ≤ δ₂ := min_le_right _ _
    exact h3
  refine ⟨δ₀, hδ₀_pos, hδ₀_le_exp, ?_⟩
  intro δ hδ hδ_le
  have hδ_le1 : δ ≤ δ₁ := hδ_le.trans (min_le_left _ _)
  have hδ_le2 : δ ≤ δ₂ := hδ_le.trans (min_le_right _ _)
  have h_log_ge1 : 1 ≤ Real.log (1/δ) := by
    have h4 : (1/δ) ≥ (Real.exp (-1))⁻¹ := by
      dsimp only [δ₂] at hδ_le2
      have h5 : 0 < δ := hδ
      have h6 : δ ≤ Real.exp (-1) := hδ_le2
      have h7 : (1/δ) ≥ 1 / Real.exp (-1) := by gcongr
      simpa using h7
    have h5 : (Real.exp (-1))⁻¹ = Real.exp 1 := by rw [← Real.exp_neg]; simp
    rw [h5] at h4
    have h6 : Real.log (Real.exp 1) ≤ Real.log (1/δ) := Real.log_le_log (by positivity) h4
    simpa using h6
  set x : ℝ := C * Real.log (1/δ) with hx_def
  have hx_nonneg : 0 ≤ x := by positivity
  have h_ceil : (Nat.ceil x : ℝ) ≤ x + 1 := nat_ceil_le_add_one hx_nonneg
  have h1 : (Nat.ceil x + 1 : ℝ) ≤ x + 2 := by linarith
  have h_log_eq : Real.log (1/δ) = Real.log δ⁻¹ := by field_simp
  have h2 : x + 2 ≤ (C + 2) * (1 + Real.log δ⁻¹) := by
    rw [hx_def, h_log_eq]
    have h3 : 1 ≤ Real.log δ⁻¹ := by rw [←h_log_eq]; exact h_log_ge1
    calc
      C * Real.log δ⁻¹ + 2
        ≤ C * Real.log δ⁻¹ + 2 * Real.log δ⁻¹ := by gcongr; linarith
      _ = (C + 2) * Real.log δ⁻¹ := by ring
      _ ≤ (C + 2) * (1 + Real.log δ⁻¹) := by gcongr; linarith
  have h4 : (C + 2) * (1 + Real.log δ⁻¹) ^ 1 ≤ Real.rpow δ (-eps) := hδ₁ δ hδ hδ_le1
  have h5 : (C + 2) * (1 + Real.log δ⁻¹) ^ 1 = (C + 2) * (1 + Real.log δ⁻¹) := by simp
  rw [h5] at h4
  exact le_trans h1 (le_trans h2 h4)

-- ============================================================================
-- Helper lemmas
-- ============================================================================

private lemma two_pow_J_d_gt_one {δ : ℝ} (hδ : 0 < δ) (hδ_le_exp : δ ≤ Real.exp (-1))
    {e : ℝ} (he_pos : 0 < e)
    {J : ℕ} (hJ : (J : ℝ) = Nat.ceil ((e + 1) / Real.log 2 * Real.log (1/δ)))
    {layerDensity : ENNReal} (hld_ne_top : layerDensity ≠ ⊤)
    (hld_lower : Kakeya.realRpowENN δ e ≤ layerDensity) :
    (1 : ENNReal) < (2^(J+1) : ENNReal) * (layerDensity / 2) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1δ_ge1 : 1 ≤ Real.log (1/δ) := by
    have h4 : (1/δ) ≥ Real.exp 1 := by
      have h5 : 0 < δ := hδ
      have h6 : δ ≤ Real.exp (-1) := hδ_le_exp
      have h7 : (1/δ) ≥ 1 / Real.exp (-1) := by gcongr
      have h8 : (1 / Real.exp (-1)) = Real.exp 1 := by
        have h9 : Real.exp (-1) = (Real.exp 1)⁻¹ := by simp [Real.exp_neg]
        rw [h9] <;> field_simp
      rw [h8] at h7; exact h7
    have h9 : Real.log (Real.exp 1) ≤ Real.log (1/δ) := Real.log_le_log (by positivity) h4
    simpa using h9
  have hlog1δ_pos : 0 < Real.log (1/δ) := by linarith
  have hJ_ge : (J : ℝ) ≥ (e + 1) / Real.log 2 * Real.log (1/δ) := by
    rw [hJ]; exact Nat.le_ceil _
  have h1 : (J : ℝ) * Real.log 2 ≥ (e + 1) * Real.log (1/δ) := by
    calc
      (J : ℝ) * Real.log 2
        ≥ (((e + 1) / Real.log 2 * Real.log (1/δ)) * Real.log 2) := by gcongr
      _ = (e + 1) * Real.log (1/δ) := by field_simp [hlog2_pos.ne'] <;> ring
  have h2 : (J : ℝ) * Real.log 2 > e * Real.log (1/δ) := by
    have h3 : (e + 1) * Real.log (1/δ) > e * Real.log (1/δ) := by
      have h4 : 0 < Real.log (1/δ) := hlog1δ_pos
      have h5 : (e + 1) * Real.log (1/δ) = e * Real.log (1/δ) + Real.log (1/δ) := by ring
      rw [h5] <;> linarith
    linarith
  have h_pos1 : 0 < (2^J : ℝ) := by positivity
  have h_pos2 : 0 < Real.rpow δ (-e) := Real.rpow_pos_of_pos hδ _
  have h_log_a : Real.log ((2^J : ℝ)) = (J : ℝ) * Real.log 2 := by
    simp [Real.log_pow] <;> ring
  have h_log_b : Real.log (Real.rpow δ (-e)) = e * Real.log (1/δ) := by
    have h1 : Real.log (Real.rpow δ (-e)) = (-e) * Real.log δ := Real.log_rpow hδ _
    rw [h1]
    have h2 : Real.log (1/δ) = -Real.log δ := by
      rw [Real.log_div (by norm_num) hδ.ne'] <;> simp
    rw [h2] <;> ring
  have h_log_cmp : Real.log ((2^J : ℝ)) > Real.log (Real.rpow δ (-e)) := by
    rw [h_log_a, h_log_b]; exact h2
  have h_gt : (2^J : ℝ) > Real.rpow δ (-e) :=
    (Real.log_lt_log_iff h_pos2 h_pos1).mp h_log_cmp
  have h_inv : Real.rpow δ (-e) = (Real.rpow δ e)⁻¹ := Real.rpow_neg hδ.le e
  have hpos_e : 0 < Real.rpow δ e := Real.rpow_pos_of_pos hδ _
  have h_real_gt : (2^J : ℝ) * Real.rpow δ e > 1 := by
    rw [h_inv] at h_gt
    field_simp [hpos_e.ne'] at h_gt ⊢ <;> linarith
  have hld_real_lower : Real.rpow δ e ≤ layerDensity.toReal := by
    have h1 : Kakeya.realRpowENN δ e ≤ layerDensity := hld_lower
    have h2 : (Kakeya.realRpowENN δ e).toReal ≤ layerDensity.toReal := by
      exact ENNReal.toReal_le_toReal (by simp [Kakeya.realRpowENN]) hld_ne_top |>.mpr h1
    have h3 : (Kakeya.realRpowENN δ e).toReal = Real.rpow δ e := by
      have hpos : 0 ≤ Real.rpow δ e := Real.rpow_nonneg hδ.le e
      have h4 : Kakeya.realRpowENN δ e = ENNReal.ofReal (Real.rpow δ e) := by
        simp [Kakeya.realRpowENN]
      rw [h4]; exact ENNReal.toReal_ofReal hpos
    rw [h3] at h2; exact h2
  have h4 : (2^(J+1) : ℝ) * (layerDensity.toReal / 2) > 1 := by
    have h5 : (2^(J+1) : ℝ) = 2 * (2^J : ℝ) := by simp [pow_succ] <;> ring
    rw [h5]
    have h6 : 2 * (2^J : ℝ) * (layerDensity.toReal / 2) = (2^J : ℝ) * layerDensity.toReal := by ring
    rw [h6]
    have h7 : (2^J : ℝ) * layerDensity.toReal ≥ (2^J : ℝ) * Real.rpow δ e := by gcongr
    have h8 : (2^J : ℝ) * Real.rpow δ e > 1 := h_real_gt
    linarith
  have h9 : (1 : ENNReal) < (2^(J+1) : ENNReal) * (layerDensity / 2) := by
    have h10 : ((2^(J+1) : ENNReal) * (layerDensity / 2)).toReal =
        (2^(J+1) : ℝ) * (layerDensity.toReal / 2) := by
      simp [ENNReal.toReal_mul, ENNReal.toReal_div] <;> ring
    have h11 : (1 : ENNReal).toReal < ((2^(J+1) : ENNReal) * (layerDensity / 2)).toReal := by
      rw [h10] <;> simpa using h4
    have h_ne_top1 : (1 : ENNReal) ≠ ⊤ := by simp
    have h_ne_top2 : ((2^(J+1) : ENNReal) * (layerDensity / 2)) ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · have h1 : (2^(J+1) : ENNReal) ≠ ⊤ := by simp
        exact h1
      · exact ENNReal.div_ne_top hld_ne_top (by norm_num)
    exact (ENNReal.toReal_lt_toReal h_ne_top1 h_ne_top2).mp h11
  exact h9

private lemma pigeonhole_average {α : Type*} {s : Finset α} {f : α → ENNReal} {j : α}
    (hj : j ∈ s) (hmax : ∀ i ∈ s, f i ≤ f j) :
    (∑ i ∈ s, f i) / (s.card : ENNReal) ≤ f j := by
  have h_card_pos : 0 < s.card := Finset.card_pos.mpr ⟨j, hj⟩
  have h1 : ∑ i ∈ s, f i ≤ (s.card : ENNReal) * f j := by
    have h2 : ∑ i ∈ s, f i ≤ ∑ i ∈ s, f j := by
      apply Finset.sum_le_sum; intro i hi; exact hmax i hi
    have h3 : ∑ i ∈ s, f j = (s.card : ENNReal) * f j := by
      rw [Finset.sum_const] <;> ring
    rw [h3] at h2; exact h2
  have h4 : (∑ i ∈ s, f i) / (s.card : ENNReal) ≤ ((s.card : ENNReal) * f j) / (s.card : ENNReal) := by gcongr
  have h5 : ((s.card : ENNReal) * f j) / (s.card : ENNReal) = f j := by
    have h6 : (s.card : ENNReal) ≠ 0 := by exact_mod_cast h_card_pos.ne'
    have h7 : (s.card : ENNReal) ≠ ⊤ := by exact ENNReal.natCast_ne_top s.card
    have h8 : ((s.card : ENNReal) * f j) * (s.card : ENNReal)⁻¹ = f j := by
      have h9 : ((s.card : ENNReal) * f j) * (s.card : ENNReal)⁻¹ =
          (s.card : ENNReal) * ((s.card : ENNReal)⁻¹ * f j) := by ring
      rw [h9]
      have h10 : (s.card : ENNReal)⁻¹ * f j = f j * (s.card : ENNReal)⁻¹ := by ring
      rw [h10]
      have h11 : (s.card : ENNReal) * (f j * (s.card : ENNReal)⁻¹) =
          f j * ((s.card : ENNReal) * (s.card : ENNReal)⁻¹) := by ring
      rw [h11, ENNReal.mul_inv_cancel h6 h7] <;> ring
    simpa [div_eq_mul_inv] using h8
  rw [h5] at h4; exact h4

private lemma low_mass_bound {δ : ℝ} {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    {d V : ENNReal} :
    ∑ T ∈ (F.filter (fun T => volume (Y.carrier T) < d * V)), volume (Y.carrier T) ≤ d * F.enncard * V := by
  let lowMassTubes := F.filter (fun T => volume (Y.carrier T) < d * V)
  have h1 : ∀ T ∈ lowMassTubes, volume (Y.carrier T) ≤ d * V := by
    intro T hT
    have h2 : volume (Y.carrier T) < d * V := (Finset.mem_filter.mp hT).2
    exact h2.le
  have h3 : ∑ T ∈ lowMassTubes, volume (Y.carrier T) ≤ ∑ T ∈ lowMassTubes, d * V := by
    apply Finset.sum_le_sum; intro T hT; exact h1 T hT
  have h4 : ∑ T ∈ lowMassTubes, d * V = (lowMassTubes.card : ENNReal) * (d * V) := by
    rw [Finset.sum_const] <;> simp <;> ring
  rw [h4] at h3
  have h51 : lowMassTubes.card ≤ F.card := Finset.card_le_card (Finset.filter_subset _ _)
  have h5 : (lowMassTubes.card : ENNReal) ≤ F.enncard := by
    have h52 : F.enncard = (F.card : ENNReal) := by simp [Kakeya.TubeFamily.enncard]
    rw [h52]; exact_mod_cast h51
  have h6 : (lowMassTubes.card : ENNReal) * (d * V) ≤ F.enncard * (d * V) := by gcongr
  have h7 : F.enncard * (d * V) = d * F.enncard * V := by
    rw [mul_comm F.enncard (d * V)] <;> simp [mul_assoc] <;> ring
  calc
    ∑ T ∈ lowMassTubes, volume (Y.carrier T)
      ≤ (lowMassTubes.card : ENNReal) * (d * V) := h3
    _ ≤ F.enncard * (d * V) := h6
    _ = d * F.enncard * V := h7

private lemma high_mass_bound {a b c : ENNReal} (h_sum : a + b = c) (h_low : a ≤ c / 2)
    (hc : c ≠ ⊤) : c / 2 ≤ b := by
  have h2 : c / 2 + c / 2 = c := by simpa [two_mul] using ENNReal.add_halves c
  by_cases h4 : b < c / 2
  · have h6 : c / 2 ≠ ⊤ := by
      intro h7
      have h8 : c = ⊤ := by
        rw [← h2, h7] <;> simp
      exact hc h8
    have h5 : a + b < c / 2 + c / 2 := by
      have h7 : c / 2 ≠ ⊤ := h6
      have h8 : a + b ≤ c / 2 + b := by gcongr
      have h9 : c / 2 + b < c / 2 + c / 2 := by
        by_contra h10
        have h11 : c / 2 + c / 2 ≤ c / 2 + b := le_of_not_gt h10
        have h12 : c / 2 ≤ b :=
          (ENNReal.add_le_add_iff_left h6).mp h11
        have h13 : b < b := h4.trans_le h12
        exact h13.false
      exact h8.trans_lt h9
    rw [h2] at h5; rw [h_sum] at h5; exact False.elim (h5.false)
  · exact le_of_not_gt h4

private lemma ennreal_mul_cancel_right {a b v : ENNReal} (hv0 : v ≠ 0) (hvt : v ≠ ⊤)
    (h : a * v ≤ b * v) : a ≤ b := by
  have h1 : a * v * v⁻¹ ≤ b * v * v⁻¹ := by gcongr
  have h2 : a * v * v⁻¹ = a := by
    rw [mul_assoc, ENNReal.mul_inv_cancel hv0 hvt] <;> ring
  have h3 : b * v * v⁻¹ = b := by
    rw [mul_assoc, ENNReal.mul_inv_cancel hv0 hvt] <;> ring
  rw [h2, h3] at h1; exact h1

private lemma retention_bound {δ hairLoss : ℝ} {layerDensity hairDensity F_enncard hairs_enncard V band_mass : ENNReal}
    {J : ℕ}
    (hband_lower : (layerDensity / 2) * F_enncard * V / (J + 1 : ENNReal) ≤ band_mass)
    (hband_upper : band_mass ≤ 2 * hairDensity * hairs_enncard * V)
    (hJ : 4 * (J + 1 : ENNReal) ≤ Kakeya.realRpowENN δ (-hairLoss))
    (hδ_pos : 0 < δ)
    (hV_ne_zero : V ≠ 0) (hV_ne_top : V ≠ ⊤)
    (hlayerDensity_ne_top : layerDensity ≠ ⊤) :
    Kakeya.realRpowENN δ hairLoss * layerDensity * F_enncard ≤ hairDensity * hairs_enncard := by
  set d : ENNReal := layerDensity / 2 with hd_def
  set J' : ENNReal := (J + 1 : ENNReal) with hJ'_def
  have hJ'_pos : J' ≠ 0 := by simp [hJ'_def] <;> positivity
  have hJ'_top : J' ≠ ⊤ := by simp [hJ'_def] <;> exact ENNReal.natCast_ne_top (J + 1)
  have h1 : d * F_enncard * V / J' ≤ 2 * hairDensity * hairs_enncard * V :=
    hband_lower.trans hband_upper
  have h21 : d * F_enncard * V / J' = (d * F_enncard / J') * V := by
    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] <;> ring
  rw [h21] at h1
  have h2 : d * F_enncard / J' ≤ 2 * hairDensity * hairs_enncard :=
    ennreal_mul_cancel_right hV_ne_zero hV_ne_top h1
  have h3 : d * F_enncard ≤ 2 * hairDensity * hairs_enncard * J' := by
    have h31 : (d * F_enncard / J') * J' ≤ (2 * hairDensity * hairs_enncard) * J' := by gcongr
    have h32 : (d * F_enncard / J') * J' = d * F_enncard := by
      have h : (d * F_enncard / J') * J' = d * F_enncard * (J'⁻¹ * J') := by
        simp [div_eq_mul_inv, mul_assoc] <;> ring
      rw [h]
      have hcancel : J'⁻¹ * J' = 1 :=
        ENNReal.inv_mul_cancel hJ'_pos hJ'_top
      rw [hcancel] <;> ring
    rw [h32] at h31; exact h31
  have h41 : 2 * d = layerDensity := by
    rw [hd_def, two_mul]; exact ENNReal.add_halves layerDensity
  have h4 : layerDensity * F_enncard ≤ 4 * hairDensity * hairs_enncard * J' := by
    have h42 : 2 * (d * F_enncard) = layerDensity * F_enncard := by
      rw [← mul_assoc, h41] <;> ring
    have h43 : 2 * (d * F_enncard) ≤ 2 * (2 * hairDensity * hairs_enncard * J') := by gcongr
    rw [h42] at h43
    have h44 : 2 * (2 * hairDensity * hairs_enncard * J') = 4 * hairDensity * hairs_enncard * J' := by ring
    rw [h44] at h43; exact h43
  have h_rpow_pos : Kakeya.realRpowENN δ hairLoss ≠ 0 := by
    simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hδ_pos] <;> positivity
  have h_rpow_top : Kakeya.realRpowENN δ hairLoss ≠ ⊤ := by
    simp [Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top
  have h_rpow_inv : (Kakeya.realRpowENN δ hairLoss)⁻¹ = Kakeya.realRpowENN δ (-hairLoss) := by
    have hpos : 0 < Real.rpow δ hairLoss := Real.rpow_pos_of_pos hδ_pos hairLoss
    have h1 : (ENNReal.ofReal (Real.rpow δ hairLoss))⁻¹ = ENNReal.ofReal ((Real.rpow δ hairLoss)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos hpos]
    have h2 : (Real.rpow δ hairLoss)⁻¹ = Real.rpow δ (-hairLoss) := by
      have hdef : ∀ (y : ℝ), (δ : ℝ) ^ y = Real.exp (Real.log δ * y) :=
        fun y => Real.rpow_def_of_pos hδ_pos y
      have h_a : (δ : ℝ) ^ hairLoss = Real.exp (Real.log δ * hairLoss) := hdef hairLoss
      have h_b : (δ : ℝ) ^ (-hairLoss) = Real.exp (Real.log δ * (-hairLoss)) := hdef (-hairLoss)
      have h_main : ((δ : ℝ) ^ hairLoss)⁻¹ = (δ : ℝ) ^ (-hairLoss) := by
        rw [h_a, h_b]; rw [← Real.exp_neg] <;> ring
      simpa using h_main
    have h_main : (ENNReal.ofReal (Real.rpow δ hairLoss))⁻¹ = ENNReal.ofReal (Real.rpow δ (-hairLoss)) := by
      rw [h1] <;> congr 1 <;> exact h2
    exact h_main
  have h5 : Kakeya.realRpowENN δ hairLoss * (4 * J') ≤ 1 := by
    have h51 : 4 * J' ≤ (Kakeya.realRpowENN δ hairLoss)⁻¹ := by
      rw [h_rpow_inv] <;> exact hJ
    have h : Kakeya.realRpowENN δ hairLoss * (4 * J') ≤ Kakeya.realRpowENN δ hairLoss * (Kakeya.realRpowENN δ hairLoss)⁻¹ := by gcongr
    rw [ENNReal.mul_inv_cancel h_rpow_pos h_rpow_top] at h; exact h
  have h6 : Kakeya.realRpowENN δ hairLoss * layerDensity * F_enncard ≤
           Kakeya.realRpowENN δ hairLoss * (4 * hairDensity * hairs_enncard * J') := by
    have h61 : Kakeya.realRpowENN δ hairLoss * layerDensity * F_enncard =
             Kakeya.realRpowENN δ hairLoss * (layerDensity * F_enncard) := by ring
    rw [h61]; gcongr
  have h7 : Kakeya.realRpowENN δ hairLoss * (4 * hairDensity * hairs_enncard * J') =
           (Kakeya.realRpowENN δ hairLoss * (4 * J')) * hairDensity * hairs_enncard := by
    simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
  rw [h7] at h6
  have h8 : (Kakeya.realRpowENN δ hairLoss * (4 * J')) * hairDensity * hairs_enncard ≤
           1 * hairDensity * hairs_enncard := by gcongr
  have h9 : 1 * hairDensity * hairs_enncard = hairDensity * hairs_enncard := by ring
  rw [h9] at h8; exact h6.trans h8

private lemma dyadic_interval_cover {x d V : ENNReal} {J : ℕ}
    (hd_pos : d ≠ 0) (hV_pos : V ≠ 0)
    (hlow : d * V ≤ x) (hhigh : x < (2^(J+1) : ENNReal) * d * V) :
    ∃ j ∈ Finset.range (J + 1), (2^j : ENNReal) * d * V ≤ x ∧ x < (2^(j+1) : ENNReal) * d * V := by
  let P : ℕ → Prop := fun j => x < (2^(j+1) : ENNReal) * d * V
  have hP_J : P J := hhigh
  have hP_nonempty : ∃ j, P j := ⟨J, hP_J⟩
  let j : ℕ := Nat.find hP_nonempty
  have hjP : P j := Nat.find_spec hP_nonempty
  have hj_le : j ≤ J := Nat.find_min' hP_nonempty hP_J
  have hj_range : j ∈ Finset.range (J + 1) := by simp only [Finset.mem_range] <;> omega
  have h_lower : (2^j : ENNReal) * d * V ≤ x := by
    by_cases h_j0 : j = 0
    · rw [h_j0] <;> simpa using hlow
    · have h_jpos : 0 < j := by omega
      have h_jminus : j - 1 < j := by omega
      have h_not : ¬ P (j - 1) :=
        Nat.find_min hP_nonempty h_jminus
      have h_eq1 : (j - 1) + 1 = j := by omega
      have h_not' : ¬(x < (2^j : ENNReal) * d * V) := by
        have h_expand : P (j - 1) ↔ x < (2^j : ENNReal) * d * V := by
          simp [P, h_eq1] <;> rfl
        exact h_expand.not.mp h_not
      exact le_of_not_gt h_not'
  exact ⟨j, hj_range, h_lower, hjP⟩

private lemma four_times_J_bound {C' C_dens x bound : ℝ} {J : ℕ}
    (hC'_pos : 0 < C')
    (hJ : (J : ℝ) = Nat.ceil (C' * x))
    (hC_dens : C_dens = 4 * C' + 10)
    (hx1 : 1 ≤ x)
    (h_abs : (Nat.ceil (C_dens * x) + 1 : ℝ) ≤ bound) :
    4 * (J + 1 : ℝ) ≤ bound := by
  have h_nonneg : 0 ≤ C' * x := by positivity
  have h_ceil_lt : (Nat.ceil (C' * x) : ℝ) < C' * x + 1 := Nat.ceil_lt_add_one h_nonneg
  have h_ceil_le : (Nat.ceil (C' * x) : ℝ) ≤ C' * x + 1 := h_ceil_lt.le
  have h1 : (J : ℝ) ≤ C' * x + 1 := by rw [hJ]; exact h_ceil_le
  have h2 : 4 * (J + 1 : ℝ) ≤ 4 * C' * x + 8 := by
    calc
      4 * (J + 1 : ℝ) = 4 * (J : ℝ) + 4 := by simp [mul_add] <;> ring
      _ ≤ 4 * (C' * x + 1) + 4 := by gcongr
      _ = 4 * C' * x + 8 := by ring
  have h3 : 4 * C' * x + 8 ≤ C_dens * x + 1 := by
    rw [hC_dens]
    have h4 : 8 ≤ 10 * x + 1 := by linarith
    linarith
  have h5 : C_dens * x + 1 ≤ (Nat.ceil (C_dens * x) + 1 : ℝ) := by
    have h6 : C_dens * x ≤ (Nat.ceil (C_dens * x) : ℝ) := Nat.le_ceil _
    linarith
  calc
    4 * (J + 1 : ℝ) ≤ 4 * C' * x + 8 := h2
    _ ≤ C_dens * x + 1 := h3
    _ ≤ (Nat.ceil (C_dens * x) + 1 : ℝ) := h5
    _ ≤ bound := h_abs

private lemma max_band_nonempty {α : Type*} {s : Finset α} {f : α → ENNReal} {j : α}
    (hj : j ∈ s) (hmax : ∀ i ∈ s, f i ≤ f j) (hpos : 0 < ∑ i ∈ s, f i) :
    0 < f j := by
  by_contra h
  have h0 : f j = 0 := by simpa using h
  have h1 : ∀ i ∈ s, f i = 0 := by
    intro i hi
    have h2 : f i ≤ f j := hmax i hi
    rw [h0] at h2; simpa using h2
  have h3 : ∑ i ∈ s, f i = 0 := by
    rw [Finset.sum_congr rfl h1] <;> simp
  rw [h3] at hpos; simpa using hpos

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem hairbrush_ambient_multiplicity_core :
    HairbrushAmbientMultiplicityCoreStatement := by
  intro inputExponent cardExponent layerLoss hairLoss
        h_input_pos h_card_pos h_layer_pos h_hair_pos
  -- --------------------------------------------------------------------------
  -- Choose delta₀ combining both log-absorption requirements
  -- --------------------------------------------------------------------------
  let C_mult : ℝ := cardExponent / Real.log 2 + 1
  have hC_mult_pos : 0 < C_mult := by positivity
  let C_dens : ℝ := 4 * (inputExponent + layerLoss + 1) / Real.log 2 + 10
  have hC_dens_pos : 0 < C_dens := by positivity
  rcases nat_log_absorbed C_mult hC_mult_pos layerLoss h_layer_pos with
    ⟨δ₁, hδ₁_pos, hδ₁_le_exp, h_abs_mult⟩
  rcases nat_log_absorbed C_dens hC_dens_pos hairLoss h_hair_pos with
    ⟨δ₂, hδ₂_pos, hδ₂_le_exp, h_abs_dens⟩
  let δ₀ : ℝ := min δ₁ δ₂
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le1 : δ₀ ≤ 1 := by
    have h : δ₀ ≤ δ₁ := min_le_left _ _
    have h2 : δ₁ ≤ 1 := by
      have h3 : δ₁ ≤ Real.exp (-1) := hδ₁_le_exp
      have h4 : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
      linarith
    exact h.trans h2
  refine ⟨δ₀, hδ₀_pos, hδ₀_le1, ?_⟩
  intro δ hδ hδ₀ F Y hF_nonempty hF_card hY_dense
  -- --------------------------------------------------------------------------
  -- Common setup
  -- --------------------------------------------------------------------------
  let V : ENNReal := Kakeya.deltaTubeVolume δ
  have hδ_le1 : δ ≤ 1 := hδ₀.trans hδ₀_le1
  have hδ_le_exp : δ ≤ Real.exp (-1) := by
    have h : δ ≤ δ₁ := hδ₀.trans (min_le_left _ _)
    exact h.trans hδ₁_le_exp
  have hlog1δ_ge1 : 1 ≤ Real.log (1/δ) := by
    have h4 : (1/δ) ≥ Real.exp 1 := by
      have h5 : 0 < δ := hδ
      have h6 : δ ≤ Real.exp (-1) := hδ_le_exp
      have h7 : (1/δ) ≥ 1 / Real.exp (-1) := by gcongr
      have h8 : (1 / Real.exp (-1)) = Real.exp 1 := by
        have h9 : Real.exp (-1) = (Real.exp 1)⁻¹ := by simp [Real.exp_neg]
        rw [h9] <;> field_simp
      rw [h8] at h7; exact h7
    have h9 : Real.log (Real.exp 1) ≤ Real.log (1/δ) := Real.log_le_log (by positivity) h4
    simpa using h9
  have hV_both : 0 < V ∧ V ≠ ⊤ := tube_volume_scaling.2.1 δ hδ hδ_le1
  have hV_pos : 0 < V := hV_both.1
  have hV_ne_top : V ≠ ⊤ := hV_both.2
  have hV_ne_zero : V ≠ 0 := hV_pos.ne'
  have hF_enncard_pos : 0 < F.enncard := by
    simpa [Kakeya.TubeFamily.enncard] using hF_nonempty
  have hF_enncard_ne_top : F.enncard ≠ ⊤ := by
    exact ENNReal.natCast_ne_top F.card
  have hY_mass_pos : 0 < Y.mass := by
    have h : Kakeya.realRpowENN δ inputExponent * F.enncard * V ≤ Y.mass := hY_dense
    have hpos : 0 < Kakeya.realRpowENN δ inputExponent * F.enncard * V := by
      have h1 : 0 < Kakeya.realRpowENN δ inputExponent := by
        simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hδ]
        <;> positivity
      positivity
    exact hpos.trans_le h
  have hY_mass_ne_top : Y.mass ≠ ⊤ := by
    have h : Y.mass ≤ ∑ T ∈ F, T.volume := by
      apply Finset.sum_le_sum
      intro T hT
      exact MeasureTheory.measure_mono (Y.subset_tube hT)
    have h2 : ∑ T ∈ F, T.volume = F.enncard * V := by
      have h3 : ∀ T ∈ F, T.volume = V := fun T _ => tube_volume_scaling.1 δ T
      rw [Finset.sum_congr rfl h3, Finset.sum_const]
      <;> simp [Kakeya.TubeFamily.enncard]
      <;> ring
    rw [h2] at h
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hF_enncard_ne_top hV_ne_top) h
  -- --------------------------------------------------------------------------
  -- Step 1: Multiplicity pigeonhole
  -- --------------------------------------------------------------------------
  let K : ℕ := Nat.log 2 F.card
  have hK_lt : F.card < (2 : ℕ)^(K+1) := Nat.lt_pow_succ_log_self (by norm_num) F.card
  have hK_le : (K + 1 : ℝ) ≤ Real.rpow δ (-layerLoss) := by
    have hδ_le1 : δ ≤ δ₁ := hδ₀.trans (min_le_left _ _)
    have hδ_le_exp : δ ≤ Real.exp (-1) := hδ_le1.trans hδ₁_le_exp
    have hlog1δ_ge1 : 1 ≤ Real.log (1/δ) := by
      have h4 : (1/δ) ≥ Real.exp 1 := by
        have h5 : 0 < δ := hδ
        have h6 : δ ≤ Real.exp (-1) := hδ_le_exp
        have h7 : (1/δ) ≥ 1 / Real.exp (-1) := by gcongr
        have h8 : (1 / Real.exp (-1)) = Real.exp 1 := by
          have h9 : Real.exp (-1) = (Real.exp 1)⁻¹ := by simp [Real.exp_neg]
          rw [h9] <;> field_simp
        rw [h8] at h7; exact h7
      have h9 : Real.log (Real.exp 1) ≤ Real.log (1/δ) := Real.log_le_log (by positivity) h4
      simpa using h9
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hF_card_real : (F.card : ℝ) ≤ Real.rpow δ (-cardExponent) := by
      have h1 : (F.card : ENNReal) ≤ Kakeya.realRpowENN δ (-cardExponent) := hF_card
      have h2 : (F.card : ENNReal).toReal ≤ (Kakeya.realRpowENN δ (-cardExponent)).toReal :=
        ENNReal.toReal_le_toReal (by simp) (by simp [Kakeya.realRpowENN]) |>.mpr h1
      have h3 : (F.card : ENNReal).toReal = (F.card : ℝ) := by simp
      have h4 : (Kakeya.realRpowENN δ (-cardExponent)).toReal = Real.rpow δ (-cardExponent) := by
        have hpos : 0 ≤ Real.rpow δ (-cardExponent) := Real.rpow_nonneg hδ.le _
        have h5 : Kakeya.realRpowENN δ (-cardExponent) = ENNReal.ofReal (Real.rpow δ (-cardExponent)) := by
          simp [Kakeya.realRpowENN]
        rw [h5]; exact ENNReal.toReal_ofReal hpos
      rw [h3, h4] at h2; exact h2
    have h_pow_le : (2 : ℝ)^K ≤ (F.card : ℝ) := by
      have hF_card_pos : F.card ≠ 0 := by
        simpa [Finset.nonempty_iff_ne_empty] using hF_nonempty
      have h : (2 : ℕ)^K ≤ F.card := Nat.pow_log_le_self 2 (hx := hF_card_pos)
      exact_mod_cast h
    have h_log1 : (K : ℝ) * Real.log 2 ≤ Real.log (F.card : ℝ) := by
      have h : Real.log ((2 : ℝ)^K) ≤ Real.log (F.card : ℝ) := Real.log_le_log (by positivity) h_pow_le
      have h2 : Real.log ((2 : ℝ)^K) = (K : ℝ) * Real.log 2 := by
        simp [Real.log_pow] <;> ring
      rw [h2] at h; exact h
    have h_log2 : Real.log (F.card : ℝ) ≤ cardExponent * Real.log (1/δ) := by
      have h3 : Real.log (F.card : ℝ) ≤ Real.log (Real.rpow δ (-cardExponent)) :=
        Real.log_le_log (by positivity) hF_card_real
      have h4 : Real.log (Real.rpow δ (-cardExponent)) = (-cardExponent) * Real.log δ :=
        Real.log_rpow hδ _
      have h5 : Real.log (1/δ) = -Real.log δ := by
        rw [Real.log_div (by norm_num) hδ.ne'] <;> simp
      have h6 : Real.log (F.card : ℝ) ≤ (-cardExponent) * Real.log δ := le_trans h3 (by rw [h4])
      rw [h5] at *; linarith
    have hK_log : (K : ℝ) ≤ cardExponent * Real.log (1/δ) / Real.log 2 := by
      have h6 : (K : ℝ) * Real.log 2 ≤ cardExponent * Real.log (1/δ) := le_trans h_log1 h_log2
      have h7 : 0 < Real.log 2 := hlog2_pos
      calc
        (K : ℝ) = ((K : ℝ) * Real.log 2) / Real.log 2 := by field_simp [h7.ne'] <;> ring
        _ ≤ (cardExponent * Real.log (1/δ)) / Real.log 2 := by gcongr
    have hK1 : (K + 1 : ℝ) ≤ C_mult * Real.log (1/δ) := by
      dsimp only [C_mult]
      have h8 : (K + 1 : ℝ) = (K : ℝ) + 1 := by simp
      rw [h8]
      have h9 : 1 ≤ Real.log (1/δ) := hlog1δ_ge1
      have h10 : (K : ℝ) + 1 ≤ cardExponent * Real.log (1/δ) / Real.log 2 + Real.log (1/δ) := by linarith
      have h11 : cardExponent * Real.log (1/δ) / Real.log 2 + Real.log (1/δ) =
          (cardExponent / Real.log 2 + 1) * Real.log (1/δ) := by ring
      rw [h11] at h10; exact h10
    have h12 : C_mult * Real.log (1/δ) ≤ (Nat.ceil (C_mult * Real.log (1/δ)) : ℝ) := Nat.le_ceil _
    have h13 : (K + 1 : ℝ) ≤ (Nat.ceil (C_mult * Real.log (1/δ)) : ℝ) := le_trans hK1 h12
    have h14 : (Nat.ceil (C_mult * Real.log (1/δ)) + 1 : ℝ) ≤ Real.rpow δ (-layerLoss) :=
      h_abs_mult δ hδ hδ_le1
    have h15 : (K + 1 : ℝ) ≤ (Nat.ceil (C_mult * Real.log (1/δ)) + 1 : ℝ) := by
      have h16 : (Nat.ceil (C_mult * Real.log (1/δ)) : ℝ) ≤ (Nat.ceil (C_mult * Real.log (1/δ)) + 1 : ℝ) := by simp
      exact le_trans h13 h16
    exact le_trans h15 h14
  rcases core_dyadic_pigeonhole Y hK_lt hY_mass_pos hY_mass_ne_top with
    ⟨k, hk_range, hband_mass⟩
  let mu : ℕ := (2 : ℕ)^k
  have hmu2 : 2 * mu = (2 : ℕ)^(k+1) := by
    simp [mu, pow_succ] <;> ring
  let support : Set Point3 := coreDyadicBand Y k
  let layer : Kakeya.Shading F := coreRestrictToBand Y mu (2 * mu)
  have hsupport_meas : MeasurableSet support := measurableSet_coreDyadicBand Y k
  have hband_set_eq : {x : Point3 | mu ≤ coreShadedMultiplicity Y x ∧ coreShadedMultiplicity Y x < 2 * mu} = support := by
    ext x
    simp [support, coreDyadicBand, mu, hmu2]
    <;> omega
  have hlayer_eq : ∀ T ∈ F, layer.carrier T = Y.carrier T ∩ support := by
    intro T _
    have h : layer.carrier T = Y.carrier T ∩ {x : Point3 | mu ≤ coreShadedMultiplicity Y x ∧ coreShadedMultiplicity Y x < 2 * mu} := by
      simp [layer, coreRestrictToBand]
      <;> rfl
    rw [h, hband_set_eq]
  have hmu_pos : 0 < mu := by positivity
  classical
  have hmult_bounds : ∀ x ∈ layer.union,
      mu ≤ (F.filter fun T => x ∈ layer.carrier T).card ∧
      (F.filter fun T => x ∈ layer.carrier T).card < 2 * mu := by
    intro x hx
    have hx_support : x ∈ support := by
      rcases hx with ⟨T, hT, hxT⟩
      have h_eq : layer.carrier T = Y.carrier T ∩ support := hlayer_eq T hT
      rw [h_eq] at hxT
      exact hxT.2
    have h_filter_eq : (F.filter fun T => x ∈ layer.carrier T) =
        (F.filter fun T => x ∈ Y.carrier T) := by
      ext T
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hT, h_in⟩
        have h_eq : layer.carrier T = Y.carrier T ∩ support := hlayer_eq T hT
        rw [h_eq] at h_in
        exact ⟨hT, h_in.1⟩
      · rintro ⟨hT, h_in⟩
        have h_eq : layer.carrier T = Y.carrier T ∩ support := hlayer_eq T hT
        rw [h_eq]
        exact ⟨hT, ⟨h_in, hx_support⟩⟩
    have h1 : mu ≤ coreShadedMultiplicity Y x := hx_support.1
    have h2 : coreShadedMultiplicity Y x < 2 * mu := by
      have h3 : coreShadedMultiplicity Y x < (2 : ℕ)^(k+1) := hx_support.2
      rw [hmu2] at * <;> exact h3
    rw [h_filter_eq]
    exact ⟨h1, h2⟩
  have hlayer_mass_eq : layer.mass = ∑ T ∈ F, volume (Y.carrier T ∩ support) := by
    have h : layer.mass = ∑ T ∈ F, volume (layer.carrier T) := by rfl
    rw [h]
    apply Finset.sum_congr rfl
    intro T hT
    rw [hlayer_eq T hT]
  have h_total_eq : coreTotalMass Y = Y.mass := by rfl
  have hlayer_mass_lower1 : Y.mass / (K + 1 : ENNReal) ≤ layer.mass := by
    have h : coreTotalMass Y / (K + 1 : ENNReal) ≤ ∑ T ∈ F, volume (Y.carrier T ∩ support) := by
      rw [h_total_eq] at hband_mass
      exact hband_mass
    rw [hlayer_mass_eq]
    exact h
  have hlayer_mass_ne_top : layer.mass ≠ ⊤ := by
    have h : layer.mass ≤ Y.mass := by
      apply Finset.sum_le_sum
      intro T hT
      exact MeasureTheory.measure_mono (Set.inter_subset_left)
    exact ne_top_of_le_ne_top hY_mass_ne_top h
  -- --------------------------------------------------------------------------
  -- Step 2: Define layerDensity and prove properties
  -- --------------------------------------------------------------------------
  let layerDensity : ENNReal := layer.mass / (F.enncard * V)
  have hdenom_ne_zero : F.enncard * V ≠ 0 := mul_ne_zero hF_enncard_pos.ne' hV_ne_zero
  have hdenom_ne_top : F.enncard * V ≠ ⊤ := ENNReal.mul_ne_top hF_enncard_ne_top hV_ne_top
  have hlayerDensity_pos : layerDensity ≠ 0 := by
    have h1 : 0 < layer.mass := by
      have h2 : 0 < Y.mass / (K + 1 : ENNReal) := by
        apply ENNReal.div_pos hY_mass_pos.ne'
        <;> simp
      exact h2.trans_le hlayer_mass_lower1
    exact ENNReal.div_pos h1.ne' hdenom_ne_top |>.ne'
  have hlayerDensity_ne_top : layerDensity ≠ ⊤ := by
    exact ENNReal.div_ne_top hlayer_mass_ne_top hdenom_ne_zero
  have hlayerDensity_mass : layerDensity * F.enncard * V = layer.mass := by
    have hdiv : layerDensity = layer.mass * (F.enncard * V)⁻¹ := by
      simp [layerDensity, div_eq_mul_inv]
    have h : layerDensity * (F.enncard * V) = layer.mass := by
      rw [hdiv]
      calc
        layer.mass * (F.enncard * V)⁻¹ * (F.enncard * V)
          = layer.mass * ((F.enncard * V)⁻¹ * (F.enncard * V)) := by rw [mul_assoc]
        _ = layer.mass * 1 := by rw [ENNReal.inv_mul_cancel hdenom_ne_zero hdenom_ne_top]
        _ = layer.mass := by ring
    simpa [mul_assoc] using h
  have hinput_retention : Kakeya.realRpowENN δ (inputExponent + layerLoss) ≤ layerDensity := by
    have hK_le_enn : (K + 1 : ENNReal) ≤ Kakeya.realRpowENN δ (-layerLoss) := by
      have hpos : 0 ≤ Real.rpow δ (-layerLoss) := (Real.rpow_pos_of_pos hδ _).le
      have h1 : (K + 1 : ENNReal) = ENNReal.ofReal ((K + 1 : ℝ)) := by norm_cast
      have h2 : Kakeya.realRpowENN δ (-layerLoss) = ENNReal.ofReal (Real.rpow δ (-layerLoss)) := by
        simp [Kakeya.realRpowENN]
      rw [h1, h2]
      exact (ENNReal.ofReal_le_ofReal_iff hpos).mpr hK_le
    have hpos_rpow : 0 < Real.rpow δ (-layerLoss) := Real.rpow_pos_of_pos hδ _
    have hpos2 : 0 < Real.rpow δ layerLoss := Real.rpow_pos_of_pos hδ _
    have h_rpow_inv : (Kakeya.realRpowENN δ (-layerLoss))⁻¹ = Kakeya.realRpowENN δ layerLoss := by
      have hdef : Kakeya.realRpowENN δ (-layerLoss) = ENNReal.ofReal (Real.rpow δ (-layerLoss)) := by
        simp [Kakeya.realRpowENN]
      rw [hdef]
      have hpos : 0 < Real.rpow δ (-layerLoss) := Real.rpow_pos_of_pos hδ _
      have h1 : (ENNReal.ofReal (Real.rpow δ (-layerLoss)))⁻¹ = ENNReal.ofReal ((Real.rpow δ (-layerLoss))⁻¹) :=
        (ENNReal.ofReal_inv_of_pos hpos).symm
      rw [h1]
      have h2 : (Real.rpow δ (-layerLoss))⁻¹ = Real.rpow δ layerLoss := by
        have h3 : Real.rpow δ (-layerLoss) = (Real.rpow δ layerLoss)⁻¹ := Real.rpow_neg hδ.le layerLoss
        rw [h3]
        have h4 : 0 < Real.rpow δ layerLoss := Real.rpow_pos_of_pos hδ _
        have h5 : ((Real.rpow δ layerLoss)⁻¹)⁻¹ = Real.rpow δ layerLoss := by
          field_simp [h4.ne'] <;> ring
        exact h5
      rw [h2]
      <;> simp [Kakeya.realRpowENN]
    have h_layerLoss_le : Kakeya.realRpowENN δ layerLoss ≤ (K + 1 : ENNReal)⁻¹ := by
      rw [←h_rpow_inv]
      exact ENNReal.inv_le_inv.mpr hK_le_enn
    have hpos1 : 0 ≤ Real.rpow δ inputExponent := Real.rpow_nonneg hδ.le _
    have h_rpow_add : Kakeya.realRpowENN δ (inputExponent + layerLoss) =
        Kakeya.realRpowENN δ inputExponent * Kakeya.realRpowENN δ layerLoss := by
      have h1 : Real.rpow δ (inputExponent + layerLoss) = Real.rpow δ inputExponent * Real.rpow δ layerLoss :=
        Real.rpow_add hδ inputExponent layerLoss
      have hpos2 : 0 ≤ Real.rpow δ layerLoss := Real.rpow_nonneg hδ.le _
      calc
        Kakeya.realRpowENN δ (inputExponent + layerLoss)
          = ENNReal.ofReal (Real.rpow δ (inputExponent + layerLoss)) := by simp [Kakeya.realRpowENN]
        _ = ENNReal.ofReal (Real.rpow δ inputExponent * Real.rpow δ layerLoss) := by rw [h1]
        _ = ENNReal.ofReal (Real.rpow δ inputExponent) * ENNReal.ofReal (Real.rpow δ layerLoss) := by
          exact ENNReal.ofReal_mul hpos1
        _ = Kakeya.realRpowENN δ inputExponent * Kakeya.realRpowENN δ layerLoss := by
          simp [Kakeya.realRpowENN]
    have h_goal : Kakeya.realRpowENN δ (inputExponent + layerLoss) * (F.enncard * V) ≤ layer.mass := by
      calc
        Kakeya.realRpowENN δ (inputExponent + layerLoss) * (F.enncard * V)
          = (Kakeya.realRpowENN δ inputExponent * Kakeya.realRpowENN δ layerLoss) * (F.enncard * V) := by
            rw [h_rpow_add] <;> ring
        _ ≤ (Kakeya.realRpowENN δ inputExponent * (K + 1 : ENNReal)⁻¹) * (F.enncard * V) := by gcongr
        _ = (Kakeya.realRpowENN δ inputExponent * F.enncard * V) / (K + 1 : ENNReal) := by
          simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] <;> ring
        _ ≤ Y.mass / (K + 1 : ENNReal) := ENNReal.div_le_div_right hY_dense (K + 1 : ENNReal)
        _ ≤ layer.mass := hlayer_mass_lower1
    have h_final : Kakeya.realRpowENN δ (inputExponent + layerLoss) ≤ layer.mass / (F.enncard * V) := by
      set X := Kakeya.realRpowENN δ (inputExponent + layerLoss) with hX
      set B := F.enncard * V with hB
      have hB0 : B ≠ 0 := hdenom_ne_zero
      have hBtop : B ≠ ⊤ := hdenom_ne_top
      have h_XB : X * B / B = X := by
        have h : X * B / B = X * B * B⁻¹ := by
          simp [div_eq_mul_inv] <;> ring
        rw [h]
        have h2 : X * B * B⁻¹ = X * (B * B⁻¹) := by ring
        rw [h2, ENNReal.mul_inv_cancel hB0 hBtop] <;> ring
      calc
        X = X * B / B := h_XB.symm
        _ ≤ layer.mass / B := ENNReal.div_le_div_right h_goal B
    simpa [layerDensity] using h_final
  have hlayer_mass_lower : layerDensity * F.enncard * V ≤ layer.mass := by
    rw [hlayerDensity_mass]
  have hlayer_mass_upper : layer.mass ≤ 2 * layerDensity * F.enncard * V := by
    have h : 2 * layerDensity * F.enncard * V = 2 * layer.mass := by
      calc
        2 * layerDensity * F.enncard * V
          = 2 * (layerDensity * F.enncard * V) := by ring
        _ = 2 * layer.mass := by rw [hlayerDensity_mass]
    have hgoal : layer.mass ≤ 2 * layer.mass := by
      have h2 : layer.mass ≤ layer.mass + layer.mass := le_self_add
      have h3 : 2 * layer.mass = layer.mass + layer.mass := by
        rw [two_mul]
      rw [h3]
      exact h2
    rw [h]
    exact hgoal
  -- --------------------------------------------------------------------------
  -- Step 3: Individual density pigeonhole for hairs
  -- --------------------------------------------------------------------------
  let d : ENNReal := layerDensity / 2
  have hd_pos : d ≠ 0 := by
    simp [d, hlayerDensity_pos] <;> tauto
  have hd_le_layer : d ≤ layerDensity := by
    simp [d] <;> exact ENNReal.half_le_self
  -- Number of density bands
  let J : ℕ := Nat.ceil ((inputExponent + layerLoss + 1) / Real.log 2 * Real.log (1/δ))
  have hJ_bound : (J + 1 : ℝ) ≤ Real.rpow δ (-hairLoss) := by
    have hδ_le2 : δ ≤ δ₂ := hδ₀.trans (min_le_right _ _)
    have hδ_le_exp : δ ≤ Real.exp (-1) := hδ_le2.trans hδ₂_le_exp
    have hlog1δ_ge1 : 1 ≤ Real.log (1/δ) := by
      have h4 : (1/δ) ≥ Real.exp 1 := by
        have h5 : 0 < δ := hδ
        have h6 : δ ≤ Real.exp (-1) := hδ_le_exp
        have h7 : (1/δ) ≥ 1 / Real.exp (-1) := by gcongr
        have h8 : (1 / Real.exp (-1)) = Real.exp 1 := by
          have h9 : Real.exp (-1) = (Real.exp 1)⁻¹ := by simp [Real.exp_neg]
          rw [h9] <;> field_simp
        rw [h8] at h7; exact h7
      have h9 : Real.log (Real.exp 1) ≤ Real.log (1/δ) := Real.log_le_log (by positivity) h4
      simpa using h9
    set C' := (inputExponent + layerLoss + 1) / Real.log 2 with hC'_def
    have hC'_pos : 0 < C' := by positivity
    have hJ_def : (J : ℝ) = Nat.ceil (C' * Real.log (1/δ)) := by rfl
    have h_nonneg : 0 ≤ C' * Real.log (1/δ) := by positivity
    have h_ceil_le : (J : ℝ) ≤ C' * Real.log (1/δ) + 1 := by
      rw [hJ_def]; exact (Nat.ceil_lt_add_one h_nonneg).le
    have h1 : (J + 1 : ℝ) ≤ C_dens * Real.log (1/δ) + 1 := by
      have hC_dens_def : C_dens = 4 * C' + 10 := by
        dsimp only [C_dens, C'] <;> ring
      have h2 : (J + 1 : ℝ) = (J : ℝ) + 1 := by simp
      rw [h2]
      have h3 : (J : ℝ) + 1 ≤ C' * Real.log (1/δ) + 2 := by linarith
      rw [hC_dens_def]
      set x := Real.log (1/δ) with hx_def
      have hx1 : 1 ≤ x := hlog1δ_ge1
      nlinarith
    have h5 : C_dens * Real.log (1/δ) + 1 ≤ (Nat.ceil (C_dens * Real.log (1/δ)) + 1 : ℝ) := by
      have h6 : C_dens * Real.log (1/δ) ≤ (Nat.ceil (C_dens * Real.log (1/δ)) : ℝ) := Nat.le_ceil _
      linarith
    have h6 : (Nat.ceil (C_dens * Real.log (1/δ)) + 1 : ℝ) ≤ Real.rpow δ (-hairLoss) :=
      h_abs_dens δ hδ hδ_le2
    linarith
  -- Define density bands
  let densityBand (j : ℕ) : Kakeya.TubeFamily δ :=
    F.filter (fun T => (2^j : ENNReal) * d * V ≤ volume (layer.carrier T) ∧
                        volume (layer.carrier T) < (2^(j+1) : ENNReal) * d * V)
  have hbands_cover_high_density :
    ∀ T ∈ F, d * V ≤ volume (layer.carrier T) →
      ∃ j ∈ Finset.range (J + 1), T ∈ densityBand j := by
    intro T hT hlow
    have h_e_pos : 0 < inputExponent + layerLoss := by linarith
    have h_gt_one : (1 : ENNReal) < (2^(J+1) : ENNReal) * d := by
      have h : (1 : ENNReal) < (2^(J+1) : ENNReal) * (layerDensity / 2) :=
        two_pow_J_d_gt_one hδ hδ_le_exp h_e_pos
          (by simp [J] <;> rfl) hlayerDensity_ne_top hinput_retention
      simpa [d] using h
    have hvol_le : volume (layer.carrier T) ≤ T.volume :=
      MeasureTheory.measure_mono (layer.subset_tube hT)
    have hTvol : T.volume = V := tube_volume_scaling.1 δ T
    have h_upper : volume (layer.carrier T) < (2^(J+1) : ENNReal) * d * V := by
      calc
        volume (layer.carrier T) ≤ T.volume := hvol_le
        _ = V := hTvol
        _ = (1 : ENNReal) * V := by ring
        _ < (2^(J+1) : ENNReal) * d * V := by gcongr
    rcases dyadic_interval_cover hd_pos hV_ne_zero hlow h_upper with ⟨j, hj_range, h_lower, h_strict⟩
    refine ⟨j, hj_range, ?_⟩
    simp only [densityBand, Finset.mem_filter]
    exact ⟨hT, h_lower, h_strict⟩
  -- Low density tubes contribute at most half the mass
  let lowMassTubes : Kakeya.TubeFamily δ :=
    F.filter (fun T => volume (layer.carrier T) < d * V)
  have hlow_mass : ∑ T ∈ lowMassTubes, volume (layer.carrier T) ≤ layer.mass / 2 := by
    have h1 : ∑ T ∈ lowMassTubes, volume (layer.carrier T) ≤ d * F.enncard * V :=
      low_mass_bound (Y := layer)
    have h2 : d * F.enncard * V = layer.mass / 2 := by
      have h3 : d = layerDensity / 2 := by rfl
      rw [h3]
      have hdiv : (layerDensity / 2) = layerDensity * (2 : ENNReal)⁻¹ := by
        simp [div_eq_mul_inv]
      have h4 : (layerDensity / 2) * F.enncard * V = (layerDensity * F.enncard * V) / 2 := by
        rw [hdiv]
        have h5 : layerDensity * (2 : ENNReal)⁻¹ * F.enncard * V =
            (layerDensity * F.enncard * V) * (2 : ENNReal)⁻¹ := by ring
        rw [h5]
        <;> simp [div_eq_mul_inv] <;> ring
      rw [h4, hlayerDensity_mass]
    rw [h2] at h1
    exact h1
  have high_mass : layer.mass / 2 ≤ ∑ j ∈ Finset.range (J + 1),
      ∑ T ∈ densityBand j, volume (layer.carrier T) := by
    let highMassTubes : Kakeya.TubeFamily δ :=
      F.filter (fun T => d * V ≤ volume (layer.carrier T))
    let bandMass (j : ℕ) : ENNReal := ∑ T ∈ densityBand j, volume (layer.carrier T)
    have h_partition : F = lowMassTubes ∪ highMassTubes := by
      ext T
      simp only [lowMassTubes, highMassTubes, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hT
        by_cases h' : volume (layer.carrier T) < d * V
        · exact Or.inl ⟨hT, h'⟩
        · have h'' : d * V ≤ volume (layer.carrier T) := le_of_not_gt h'
          exact Or.inr ⟨hT, h''⟩
      · rintro (h | h)
        · exact h.1
        · exact h.1
    have h_disjoint : Disjoint lowMassTubes highMassTubes := by
      rw [Finset.disjoint_left]
      intro T h1 h2
      have h1' : volume (layer.carrier T) < d * V := (Finset.mem_filter.mp h1).2
      have h2' : d * V ≤ volume (layer.carrier T) := (Finset.mem_filter.mp h2).2
      have h_cont : volume (layer.carrier T) < volume (layer.carrier T) := h1'.trans_le h2'
      exact False.elim (lt_irrefl (volume (layer.carrier T)) h_cont)
    have h_bands_disjoint : ∀ j1 ∈ Finset.range (J + 1), ∀ j2 ∈ Finset.range (J + 1),
        j1 ≠ j2 → Disjoint (densityBand j1) (densityBand j2) := by
      intro j1 hj1 j2 hj2 hne
      by_cases h : j1 < j2
      · rw [Finset.disjoint_left]
        intro T hT1 hT2
        have h1 : volume (layer.carrier T) < (2^(j1+1) : ENNReal) * d * V :=
          (Finset.mem_filter.mp hT1).2.2
        have h2 : (2^j2 : ENNReal) * d * V ≤ volume (layer.carrier T) :=
          (Finset.mem_filter.mp hT2).2.1
        have h3 : j1 + 1 ≤ j2 := by omega
        have h4 : (2^(j1+1) : ENNReal) ≤ (2^j2 : ENNReal) := by
          gcongr <;> norm_num
        have h5 : (2^(j1+1) : ENNReal) * d * V ≤ (2^j2 : ENNReal) * d * V := by gcongr
        have h6 : (2^(j1+1) : ENNReal) * d * V ≤ volume (layer.carrier T) := h5.trans h2
        have h_cont : volume (layer.carrier T) < volume (layer.carrier T) := h1.trans_le h6
        exact False.elim (lt_irrefl (volume (layer.carrier T)) h_cont)
      · have h' : j2 < j1 := by omega
        have h_disj' : Disjoint (densityBand j2) (densityBand j1) := by
          rw [Finset.disjoint_left]
          intro T hT2 hT1
          have h1 : volume (layer.carrier T) < (2^(j2+1) : ENNReal) * d * V :=
            (Finset.mem_filter.mp hT2).2.2
          have h2 : (2^j1 : ENNReal) * d * V ≤ volume (layer.carrier T) :=
            (Finset.mem_filter.mp hT1).2.1
          have h3 : j2 + 1 ≤ j1 := by omega
          have h4 : (2^(j2+1) : ENNReal) ≤ (2^j1 : ENNReal) := by
            gcongr <;> norm_num
          have h5 : (2^(j2+1) : ENNReal) * d * V ≤ (2^j1 : ENNReal) * d * V := by gcongr
          have h6 : (2^(j2+1) : ENNReal) * d * V ≤ volume (layer.carrier T) := h5.trans h2
          have h_cont : volume (layer.carrier T) < volume (layer.carrier T) := h1.trans_le h6
          exact False.elim (lt_irrefl (volume (layer.carrier T)) h_cont)
        exact h_disj'.symm
    have h_eq : highMassTubes = Finset.biUnion (Finset.range (J + 1)) densityBand := by
      ext T
      simp only [highMassTubes, Finset.mem_filter, Finset.mem_biUnion]
      constructor
      · rintro ⟨hT, hge⟩
        rcases hbands_cover_high_density T hT hge with ⟨j, hj, hmem⟩
        exact ⟨j, hj, hmem⟩
      · rintro ⟨j, hj, hT⟩
        have hge : (2^j : ENNReal) * d * V ≤ volume (layer.carrier T) :=
          (Finset.mem_filter.mp hT).2.1
        have h11 : 1 ≤ (2 : ℕ)^j := by
          apply Nat.one_le_pow <;> norm_num
        have h1 : (1 : ENNReal) ≤ (2^j : ENNReal) := by exact_mod_cast h11
        have h2 : d * V ≤ (2^j : ENNReal) * d * V := by
          have h21 : (1 : ENNReal) ≤ (2^j : ENNReal) := by exact_mod_cast h11
          have h : (d * V) * (1 : ENNReal) ≤ (d * V) * (2^j : ENNReal) :=
            mul_le_mul_left' h21 (d * V)
          have h_rhs : (d * V) * (2^j : ENNReal) = (2^j : ENNReal) * d * V := by
            simp [mul_comm, mul_assoc, mul_left_comm]
          rw [h_rhs] at h
          simpa [mul_one] using h
        exact ⟨(Finset.mem_filter.mp hT).1, h2.trans hge⟩
    have h_sum1 : ∑ T ∈ F, volume (layer.carrier T) =
        (∑ T ∈ lowMassTubes, volume (layer.carrier T)) +
        (∑ T ∈ highMassTubes, volume (layer.carrier T)) := by
      have h9 : ∑ T ∈ (lowMassTubes ∪ highMassTubes), volume (layer.carrier T) =
          (∑ T ∈ lowMassTubes, volume (layer.carrier T)) +
          (∑ T ∈ highMassTubes, volume (layer.carrier T)) :=
        Finset.sum_union h_disjoint
      have h10 : ∑ T ∈ F, volume (layer.carrier T) =
          ∑ T ∈ (lowMassTubes ∪ highMassTubes), volume (layer.carrier T) := by
        apply Finset.sum_congr h_partition
        intro T _
        rfl
      rw [h10, h9]
    have h_sum2 : ∑ T ∈ highMassTubes, volume (layer.carrier T) =
        ∑ j ∈ Finset.range (J + 1), bandMass j := by
      have h9 : ∑ T ∈ highMassTubes, volume (layer.carrier T) =
          ∑ T ∈ (Finset.biUnion (Finset.range (J + 1)) densityBand), volume (layer.carrier T) := by
        rw [h_eq]
      rw [h9]
      exact Finset.sum_biUnion (fun j _ j' _ hne => h_bands_disjoint j ‹_› j' ‹_› hne)
    have h_total : layer.mass =
        (∑ T ∈ lowMassTubes, volume (layer.carrier T)) +
        (∑ j ∈ Finset.range (J + 1), bandMass j) := by
      have h_layer_def : layer.mass = ∑ T ∈ F, volume (layer.carrier T) := by rfl
      calc
        layer.mass = ∑ T ∈ F, volume (layer.carrier T) := h_layer_def
        _ = (∑ T ∈ lowMassTubes, volume (layer.carrier T)) +
            (∑ T ∈ highMassTubes, volume (layer.carrier T)) := h_sum1
        _ = (∑ T ∈ lowMassTubes, volume (layer.carrier T)) +
            (∑ j ∈ Finset.range (J + 1), bandMass j) := by rw [h_sum2]
    exact high_mass_bound h_total.symm hlow_mass hlayer_mass_ne_top
  -- Pick max-mass band
  have h_exists_max : ∃ j ∈ Finset.range (J + 1),
      ∀ l ∈ Finset.range (J + 1),
        (∑ T ∈ densityBand l, volume (layer.carrier T)) ≤
        (∑ T ∈ densityBand j, volume (layer.carrier T)) := by
    exact Finset.exists_max_image (Finset.range (J + 1))
      (fun j => ∑ T ∈ densityBand j, volume (layer.carrier T))
      (by simp)
  rcases h_exists_max with ⟨j, hj_range, hj_max⟩
  let hairs : Kakeya.TubeFamily δ := densityBand j
  have hhairs_subset : hairs ⊆ F := Finset.filter_subset _ _
  have hhairs_nonempty : hairs.Nonempty := by
    let bandMass (j : ℕ) : ENNReal := ∑ T ∈ densityBand j, volume (layer.carrier T)
    have h_pos : 0 < ∑ j ∈ Finset.range (J + 1), bandMass j := by
      have h1 : layer.mass / 2 ≤ ∑ j ∈ Finset.range (J + 1), bandMass j := high_mass
      have h21 : layer.mass ≠ 0 := by
        have h_pos : 0 < layer.mass := by
          have h2 : 0 < Y.mass / (K + 1 : ENNReal) := by
            apply ENNReal.div_pos hY_mass_pos.ne' <;> simp
          exact h2.trans_le hlayer_mass_lower1
        exact h_pos.ne'
      have h22 : (2 : ENNReal) ≠ ⊤ := by simp
      have h2 : 0 < layer.mass / 2 := ENNReal.div_pos h21 h22
      exact h2.trans_le h1
    have h3 : 0 < bandMass j := max_band_nonempty hj_range hj_max h_pos
    by_contra h4
    have h5 : hairs = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using h4
    have h6 : bandMass j = 0 := by
      have h7 : bandMass j = ∑ T ∈ hairs, volume (layer.carrier T) := by rfl
      rw [h7, h5] <;> simp
    rw [h6] at h3
    simpa using h3
  let hairDensity : ENNReal := (2^j : ENNReal) * d
  have hhairDensity_pos : hairDensity ≠ 0 := by
    simp [hairDensity, d, hd_pos] <;> tauto
  have hhairDensity_ne_top : hairDensity ≠ ⊤ := by
    have h1 : (2^j : ENNReal) ≠ ⊤ := by simp
    have h2 : d ≠ ⊤ := by
      have hdiv : d = layerDensity / 2 := by rfl
      rw [hdiv]
      exact ENNReal.div_ne_top hlayerDensity_ne_top (by norm_num)
    exact ENNReal.mul_ne_top h1 h2
  have hlayer_density_le_hair : layerDensity / 2 ≤ hairDensity := by
    have hj1 : (1 : ENNReal) ≤ (2^j : ENNReal) := by
      exact_mod_cast Nat.one_le_pow j 2 (by norm_num)
    calc
      layerDensity / 2
        = d := by simp [d]
      _ = (1 : ENNReal) * d := by ring
      _ ≤ (2^j : ENNReal) * d := by gcongr
      _ = hairDensity := by simp [hairDensity]
  let hairShading : Kakeya.Shading hairs := coreRestrictFamily layer hhairs_subset
  have hhair_shading_eq : ∀ T ∈ hairs, hairShading.carrier T = layer.carrier T := by
    intro T _
    rfl
  have hper_hair_lower : ∀ T ∈ hairs,
      hairDensity * T.volume ≤ volume (hairShading.carrier T) := by
    intro T hT
    have hvol : T.volume = V := tube_volume_scaling.1 δ T
    have h1 : (2^j : ENNReal) * d * V ≤ volume (layer.carrier T) :=
      (Finset.mem_filter.mp hT).2.1
    have h3 : volume (hairShading.carrier T) = volume (layer.carrier T) := by
      simp [hairShading, coreRestrictFamily]
    have h4 : hairDensity * T.volume = (2^j : ENNReal) * d * V := by
      have h5 : hairDensity = (2^j : ENNReal) * d := by rfl
      rw [h5, hvol] <;> ring
    rw [h4, h3]
    exact h1
  have hper_hair_upper : ∀ T ∈ hairs,
      volume (hairShading.carrier T) ≤ 2 * hairDensity * T.volume := by
    intro T hT
    have hvol : T.volume = V := tube_volume_scaling.1 δ T
    have h2 : volume (layer.carrier T) < (2^(j+1) : ENNReal) * d * V :=
      (Finset.mem_filter.mp hT).2.2
    have h3 : volume (hairShading.carrier T) = volume (layer.carrier T) := by
      simp [hairShading, coreRestrictFamily]
    have h4 : 2 * hairDensity * T.volume = (2^(j+1) : ENNReal) * d * V := by
      have h5 : hairDensity = (2^j : ENNReal) * d := by rfl
      rw [h5, hvol]
      <;> simp [pow_succ] <;> ring
    rw [h3, h4]
    exact h2.le
  have hretention : Kakeya.realRpowENN δ hairLoss * layerDensity * F.enncard ≤
      hairDensity * hairs.enncard := by
    let bandMass (j : ℕ) : ENNReal := ∑ T ∈ densityBand j, volume (layer.carrier T)
    let C' : ℝ := (inputExponent + layerLoss + 1) / Real.log 2
    have hC'_pos : 0 < C' := by positivity
    have hJ' : (J : ℝ) = Nat.ceil (C' * Real.log (1/δ)) := by rfl
    have hC_dens_eq : C_dens = 4 * C' + 10 := by
      simp [C_dens, C'] <;> ring
    have h_abs' : (Nat.ceil (C_dens * Real.log (1/δ)) + 1 : ℝ) ≤ Real.rpow δ (-hairLoss) :=
      h_abs_dens δ hδ (hδ₀.trans (min_le_right _ _))
    have hJ4 : 4 * (J + 1 : ℝ) ≤ Real.rpow δ (-hairLoss) :=
      four_times_J_bound hC'_pos hJ' hC_dens_eq hlog1δ_ge1 h_abs'
    have hJ4_enn : 4 * (J + 1 : ENNReal) ≤ Kakeya.realRpowENN δ (-hairLoss) := by
      have h_eq1 : ENNReal.ofReal (4 * (J + 1 : ℝ)) = 4 * (J + 1 : ENNReal) := by
        simp <;> norm_cast
      have hpos : 0 ≤ Real.rpow δ (-hairLoss) := (Real.rpow_pos_of_pos hδ _).le
      have h : ENNReal.ofReal (4 * (J + 1 : ℝ)) ≤ ENNReal.ofReal (Real.rpow δ (-hairLoss)) :=
        (ENNReal.ofReal_le_ofReal_iff hpos).mpr hJ4
      rw [h_eq1] at h
      simpa [Kakeya.realRpowENN] using h
    have h_avg : (∑ j ∈ Finset.range (J + 1), bandMass j) / (J + 1 : ENNReal) ≤ bandMass j := by
      have h1 : ∑ l ∈ Finset.range (J + 1), bandMass l ≤ ∑ l ∈ Finset.range (J + 1), bandMass j :=
        Finset.sum_le_sum (fun l hl => hj_max l hl)
      have h2 : ∑ l ∈ Finset.range (J + 1), bandMass j = (J + 1 : ENNReal) * bandMass j := by
        rw [Finset.sum_const] <;> simp [Kakeya.TubeFamily.enncard] <;> ring
      have h3 : ∑ l ∈ Finset.range (J + 1), bandMass l ≤ (J + 1 : ENNReal) * bandMass j := h1.trans_eq h2
      have h4 : (J + 1 : ENNReal) ≠ 0 := by simp <;> positivity
      have h5 : (J + 1 : ENNReal) ≠ ⊤ := by simp <;> exact ENNReal.natCast_ne_top (J + 1)
      have h6 : (∑ l ∈ Finset.range (J + 1), bandMass l) / (J + 1 : ENNReal) ≤
          ((J + 1 : ENNReal) * bandMass j) / (J + 1 : ENNReal) := ENNReal.div_le_div_right h3 _
      have h7 : ((J + 1 : ENNReal) * bandMass j) / (J + 1 : ENNReal) = bandMass j := by
        have h_comm : (J + 1 : ENNReal) * bandMass j = bandMass j * (J + 1 : ENNReal) := mul_comm _ _
        rw [h_comm]
        exact ENNReal.mul_div_cancel_right h4 h5
      rw [h7] at h6
      exact h6
    have h_d_mass : d * F.enncard * V = layer.mass / 2 := by
      have h3 : d = layerDensity / 2 := by rfl
      rw [h3]
      have h4 : (layerDensity / 2) * F.enncard * V = (layerDensity * F.enncard * V) / 2 := by
        have h_div : ∀ (x : ENNReal), x / 2 = x * (2 : ENNReal)⁻¹ := by
          intro x; simp [div_eq_mul_inv]
        rw [h_div (layerDensity * F.enncard * V), h_div layerDensity]
        ring
      rw [h4, hlayerDensity_mass]
    have hband_lower : (layerDensity / 2) * F.enncard * V / (J + 1 : ENNReal) ≤ bandMass j := by
      have h5 : (layerDensity / 2) * F.enncard * V = d * F.enncard * V := by simp [d]
      rw [h5]
      have h7 : d * F.enncard * V = layer.mass / 2 := h_d_mass
      have h8 : d * F.enncard * V ≤ ∑ j ∈ Finset.range (J + 1), bandMass j := by
        rw [h7]; exact high_mass
      have h6 : d * F.enncard * V / (J + 1 : ENNReal) ≤
          (∑ j ∈ Finset.range (J + 1), bandMass j) / (J + 1 : ENNReal) := by
        gcongr
      exact h6.trans h_avg
    have hband_upper : bandMass j ≤ 2 * hairDensity * hairs.enncard * V := by
      have h1 : ∀ T ∈ hairs, volume (layer.carrier T) ≤ 2 * hairDensity * V := by
        intro T hT
        have h2 : volume (layer.carrier T) < (2^(j+1) : ENNReal) * d * V :=
          (Finset.mem_filter.mp hT).2.2
        have h3 : (2^(j+1) : ENNReal) * d * V = 2 * hairDensity * V := by
          have h4 : hairDensity = (2^j : ENNReal) * d := by rfl
          rw [h4] <;> simp [pow_succ] <;> ring
        rw [h3] at h2
        exact h2.le
      have h4 : ∑ T ∈ hairs, volume (layer.carrier T) ≤ ∑ T ∈ hairs, (2 * hairDensity * V) := by
        apply Finset.sum_le_sum; intro T hT; exact h1 T hT
      have h5 : ∑ T ∈ hairs, (2 * hairDensity * V) = 2 * hairDensity * hairs.enncard * V := by
        rw [Finset.sum_const] <;> simp [Kakeya.TubeFamily.enncard] <;> ring
      rw [h5] at h4
      exact h4
    exact retention_bound hband_lower hband_upper hJ4_enn hδ hV_ne_zero hV_ne_top hlayerDensity_ne_top
  -- --------------------------------------------------------------------------
  -- Package the result
  -- --------------------------------------------------------------------------
  refine ⟨support, hsupport_meas, layer, hlayer_eq, mu, hmu_pos, ?_, ?_,
    layerDensity, hlayerDensity_pos, hlayerDensity_ne_top, hinput_retention,
    hlayer_mass_lower, hlayer_mass_upper, hairs, hhairs_subset, hhairs_nonempty,
    hairShading, hhair_shading_eq, hairDensity, hhairDensity_pos, hhairDensity_ne_top,
    hlayer_density_le_hair, hper_hair_lower, hper_hair_upper, hretention⟩
  · exact fun x hx => (hmult_bounds x hx).1
  · exact fun x hx => (hmult_bounds x hx).2

end Kakeya.Assouad
