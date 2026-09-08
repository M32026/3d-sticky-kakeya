/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.CylinderApprox
public import Kakeya.Tube.IntersectionVolume
public import Kakeya.ConvexBody
public import Kakeya.Tube.Basic
public import Kakeya.Tube.CardEssentiallyDistinct

/-!
# Nearly parallel tubes

If two tubes are not essentially distinct, then their directions are close (modulo
antipodal identification) and their midpoints have close perpendicular and parallel
components.  The main theorems are `notED_implies_direction_close` and
`notED_implies_all_close`.
-/

@[expose] public section

open MeasureTheory
open Topology
open Tube

namespace Kakeya

noncomputable section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/- not-ED ⇒ modulo antipodal -/
theorem notED_implies_direction_close (hn : 1 < Module.finrank ℝ E) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ {δ : NNReal} (_ : 0 < δ) (_ : δ ≤ 1)
        (T₁ T₂ : Tube δ E),
        ¬ IsEssentiallyDistinct T₁.carrier T₂.carrier →
        min ‖T₁.direction - T₂.direction‖
            ‖T₁.direction + T₂.direction‖ ≤ C₀ * (δ : ℝ) := by
  obtain ⟨C_ang, hC_ang_pos, hC_ang_bound⟩ := Tube.volume_inter_le_of_angle hn
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by omega : 0 < Module.finrank ℝ E)
  set c_n : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hc_n_def
  have hc_n_pos : 0 < c_n := by
    rw [hc_n_def]; exact NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  have hc_n_bound : ∀ (δ : NNReal), 0 < δ → ∀ T : Tube δ E,
      c_n * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤ volume.real T.carrier := by
    intro δ _ T
    have h := Tube.le_volume (δ := δ) T
    have hreal := ENNReal.toReal_mono T.isCompact.measure_lt_top.ne h
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, ENNReal.coe_toReal] at hreal
    exact hreal
  set C₀ : ℝ := max 1 (2 * C_ang / c_n) with hC₀_def
  have hC₀_pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC₀_ge_one : 1 ≤ C₀ := le_max_left _ _
  have hC₀_ge_ratio : 2 * C_ang / c_n ≤ C₀ := le_max_right _ _
  refine ⟨C₀, hC₀_pos, ?_⟩
  intro δ hδ hδ1 T₁ T₂ h_notED
  have hδr : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hδ1r : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  set θ : ℝ := min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖ with hθ_def
  by_contra hθ_gt
  push Not at hθ_gt
  -- hθ_gt : C₀ * δ < θ
  have hθ_gt_δ : (δ : ℝ) < θ := by nlinarith
  have hθ_pos : 0 < θ := lt_trans hδr hθ_gt_δ
  -- Apply hC_ang_bound
  have h_inter : volume.real (T₁.carrier ∩ T₂.carrier) ≤
      C_ang * (δ : ℝ) ^ (Module.finrank ℝ E - 1) *
        min 1 ((δ : ℝ) / max θ (δ : ℝ)) := hC_ang_bound hδ hδ1 T₁ T₂
  -- max θ δ = θ
  have hmax : max θ (δ : ℝ) = θ := max_eq_left hθ_gt_δ.le
  rw [hmax] at h_inter
  -- min 1 (δ/θ) ≤ δ/θ
  have h_min_le : min (1 : ℝ) ((δ : ℝ) / θ) ≤ (δ : ℝ) / θ := min_le_right _ _
  have h_δθ_nonneg : 0 ≤ (δ : ℝ) / θ := div_nonneg hδr.le hθ_pos.le
  -- δ/θ < 1/C₀
  have h_δθ_lt : (δ : ℝ) / θ < 1 / C₀ := by
    rw [div_lt_div_iff₀ hθ_pos hC₀_pos]
    have : C₀ * (δ : ℝ) < θ := hθ_gt
    linarith
  -- Bound vol(T₁∩T₂)
  set n := Module.finrank ℝ E
  have hδpow_pos : 0 < (δ : ℝ) ^ (n - 1) := pow_pos hδr _
  have hδpow_nonneg : 0 ≤ (δ : ℝ) ^ (n - 1) := hδpow_pos.le
  have hC_ang_δpow_nonneg : 0 ≤ C_ang * (δ : ℝ) ^ (n - 1) :=
    mul_nonneg hC_ang_pos.le hδpow_nonneg
  have h_inter2 : volume.real (T₁.carrier ∩ T₂.carrier) ≤
      C_ang * (δ : ℝ) ^ (n - 1) * ((δ : ℝ) / θ) := by
    calc volume.real (T₁.carrier ∩ T₂.carrier)
        ≤ C_ang * (δ : ℝ) ^ (n - 1) * min 1 ((δ : ℝ) / θ) := h_inter
      _ ≤ C_ang * (δ : ℝ) ^ (n - 1) * ((δ : ℝ) / θ) :=
          mul_le_mul_of_nonneg_left h_min_le hC_ang_δpow_nonneg
  -- C_ang * (δ/θ) ≤ c_n / 2
  have h_C_ang_div_le : C_ang * ((δ : ℝ) / θ) ≤ c_n / 2 := by
    have h1 : C_ang * ((δ : ℝ) / θ) < C_ang * (1 / C₀) :=
      mul_lt_mul_of_pos_left h_δθ_lt hC_ang_pos
    have h2 : C_ang * (1 / C₀) ≤ c_n / 2 := by
      rw [mul_one_div]
      rw [div_le_div_iff₀ hC₀_pos (by norm_num : (0:ℝ) < 2)]
      -- 2 * C_ang ≤ c_n * C₀
      have hcc : 2 * C_ang ≤ c_n * C₀ := by
        have := hC₀_ge_ratio
        rw [div_le_iff₀ hc_n_pos] at this
        linarith
      linarith
    linarith
  -- vol(T₁∩T₂) ≤ (c_n/2) * δ^(n-1)
  have h_inter3 : volume.real (T₁.carrier ∩ T₂.carrier) ≤
      (c_n / 2) * (δ : ℝ) ^ (n - 1) := by
    calc volume.real (T₁.carrier ∩ T₂.carrier)
        ≤ C_ang * (δ : ℝ) ^ (n - 1) * ((δ : ℝ) / θ) := h_inter2
      _ = (C_ang * ((δ : ℝ) / θ)) * (δ : ℝ) ^ (n - 1) := by ring
      _ ≤ (c_n / 2) * (δ : ℝ) ^ (n - 1) :=
          mul_le_mul_of_nonneg_right h_C_ang_div_le hδpow_nonneg
  -- Lower bound on vol(T_i)
  have h_T1_lb : c_n * (δ : ℝ) ^ (n - 1) ≤ volume.real T₁.carrier := hc_n_bound δ hδ T₁
  have h_max_lb : c_n * (δ : ℝ) ^ (n - 1) ≤
      max (volume.real T₁.carrier) (volume.real T₂.carrier) :=
    le_trans h_T1_lb (le_max_left _ _)
  -- Now show ED holds, contradiction.
  apply h_notED
  -- Convert to ENNReal form of IsEssentiallyDistinct.
  have hT1_fin : volume T₁.carrier ≠ ⊤ := T₁.isCompact.measure_lt_top.ne
  have hT2_fin : volume T₂.carrier ≠ ⊤ := T₂.isCompact.measure_lt_top.ne
  have hinter_fin : volume (T₁.carrier ∩ T₂.carrier) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt T₁.isCompact.measure_lt_top).ne
  have hmax_ne : max (volume T₁.carrier) (volume T₂.carrier) ≠ ⊤ := by
    rw [ne_eq, max_eq_top, not_or]; exact ⟨hT1_fin, hT2_fin⟩
  have hRHS_ne : (1 / 2 : ENNReal) * max (volume T₁.carrier) (volume T₂.carrier) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num : (1 / 2 : ENNReal) ≠ ⊤) hmax_ne
  have h_ed_real : volume.real (T₁.carrier ∩ T₂.carrier) ≤
      (1/2 : ℝ) * max (volume.real T₁.carrier) (volume.real T₂.carrier) := by
    calc volume.real (T₁.carrier ∩ T₂.carrier)
        ≤ (c_n / 2) * (δ : ℝ) ^ (n - 1) := h_inter3
      _ = (1/2) * (c_n * (δ : ℝ) ^ (n - 1)) := by ring
      _ ≤ (1/2) * max (volume.real T₁.carrier) (volume.real T₂.carrier) :=
          mul_le_mul_of_nonneg_left h_max_lb (by norm_num)
  change volume (T₁.carrier ∩ T₂.carrier) ≤
    (1 / 2 : ENNReal) * max (volume T₁.carrier) (volume T₂.carrier)
  rw [← ENNReal.ofReal_toReal hinter_fin, ← ENNReal.ofReal_toReal hRHS_ne]
  apply ENNReal.ofReal_le_ofReal
  change volume.real (T₁.carrier ∩ T₂.carrier) ≤
    ((1 / 2 : ENNReal) * max (volume T₁.carrier) (volume T₂.carrier)).toReal
  rw [ENNReal.toReal_mul, show ((1 / 2 : ENNReal).toReal : ℝ) = 1 / 2 by simp]
  have hmax_to : (max (volume T₁.carrier) (volume T₂.carrier)).toReal =
      max (volume T₁.carrier).toReal (volume T₂.carrier).toReal := by
    rcases le_total (volume T₁.carrier) (volume T₂.carrier) with hle | hle
    · rw [max_eq_right hle, max_eq_right (ENNReal.toReal_mono hT2_fin hle)]
    · rw [max_eq_left hle, max_eq_left (ENNReal.toReal_mono hT1_fin hle)]
  rw [hmax_to]
  exact h_ed_real

theorem notED_implies_all_close (hn : 1 < Module.finrank ℝ E) :
    ∃ (C_dir C_perp C_long : ℝ), 0 < C_dir ∧ 0 < C_perp ∧ 0 < C_long ∧
      ∀ {δ : NNReal} (_ : 0 < δ) (_ : δ ≤ 1)
        (T₁ T₀ : Tube δ E),
        ¬ IsEssentiallyDistinct T₁.carrier T₀.carrier →
        min ‖T₁.direction - T₀.direction‖
            ‖T₁.direction + T₀.direction‖ ≤ C_dir * (δ : ℝ) ∧
        (∃ (ε : ℝ), (ε = 1 ∨ ε = -1) ∧
          ‖T₁.midpoint - T₀.midpoint -
            (inner ℝ (T₁.midpoint - T₀.midpoint) (ε • T₀.direction)) •
              (ε • T₀.direction)‖ ≤ C_perp * (δ : ℝ) ∧
          |inner ℝ (T₁.midpoint - T₀.midpoint) (ε • T₀.direction)| ≤ C_long) := by
  obtain ⟨C_dir, hC_dir_pos, hC_dir_bound⟩ := notED_implies_direction_close hn
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by omega : 0 < Module.finrank ℝ E)
  set c_n : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hc_n_def
  have hc_n_pos : 0 < c_n := by
    rw [hc_n_def]; exact NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  have hc_n_bound : ∀ (δ : NNReal), 0 < δ → ∀ T : Tube δ E,
      c_n * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤ volume.real T.carrier := by
    intro δ _ T
    have h := Tube.le_volume (δ := δ) T
    have hreal := ENNReal.toReal_mono T.isCompact.measure_lt_top.ne h
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, ENNReal.coe_toReal] at hreal
    exact hreal
  refine ⟨C_dir, 2 + C_dir / 2, 3, hC_dir_pos, by linarith, by norm_num, ?_⟩
  intro δ hδ hδ1 T₁ T₀ h_notED
  have hδr : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hδ1r : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  -- Direction close bound
  have h_dir : min ‖T₁.direction - T₀.direction‖
      ‖T₁.direction + T₀.direction‖ ≤ C_dir * (δ : ℝ) :=
    hC_dir_bound hδ hδ1 T₁ T₀ h_notED
  refine ⟨h_dir, ?_⟩
  -- Set notation
  have hu_norm0 : ‖T₀.direction‖ = 1 := by
    have := T₀.dist_eq_one
    rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
  have hv_norm0 : ‖T₁.direction‖ = 1 := by
    have := T₁.dist_eq_one
    rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
  set u : E := T₀.direction with hu_def
  have hu_norm : ‖u‖ = 1 := hu_norm0
  set v : E := T₁.direction with hv_def
  have hv_norm : ‖v‖ = 1 := hv_norm0
  have h_inner_u_u : inner ℝ u u = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hu_norm]; ring
  set w : E := T₁.midpoint - T₀.midpoint with hw_def
  -- Choose ε ∈ {1, -1}: 1 if ‖v - u‖ ≤ ‖v + u‖, otherwise -1.
  have h_eps_exists : ∃ (ε : ℝ), (ε = 1 ∨ ε = -1) ∧ ‖v - ε • u‖ ≤ C_dir * (δ : ℝ) := by
    by_cases hcase : ‖v - u‖ ≤ ‖v + u‖
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [one_smul]
      have := h_dir
      rw [min_eq_left hcase] at this
      exact this
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [neg_smul, one_smul, sub_neg_eq_add]
      push Not at hcase
      have := h_dir
      rw [min_eq_right hcase.le] at this
      exact this
  obtain ⟨ε, hε, hε_bound⟩ := h_eps_exists
  have hε_sq : ε * ε = 1 := by rcases hε with h | h <;> (subst h; ring)
  have hε_abs : |ε| = 1 := by rcases hε with h | h <;> (subst h; simp)
  -- Convert h_notED from ENNReal form to ℝ form so the rest of the proof can use it.
  have hT1_fin : volume T₁.carrier ≠ ⊤ := T₁.isCompact.measure_lt_top.ne
  have hT0_fin : volume T₀.carrier ≠ ⊤ := T₀.isCompact.measure_lt_top.ne
  have hinter_fin : volume (T₁.carrier ∩ T₀.carrier) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt T₁.isCompact.measure_lt_top).ne
  have hmax_ne : max (volume T₁.carrier) (volume T₀.carrier) ≠ ⊤ := by
    rw [ne_eq, max_eq_top, not_or]; exact ⟨hT1_fin, hT0_fin⟩
  have hRHS_ne : (1 / 2 : ENNReal) * max (volume T₁.carrier) (volume T₀.carrier) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num : (1 / 2 : ENNReal) ≠ ⊤) hmax_ne
  have h_notED_real : ¬ volume.real (T₁.carrier ∩ T₀.carrier) ≤
      (1/2 : ℝ) * max (volume.real T₁.carrier) (volume.real T₀.carrier) := by
    intro h_le
    apply h_notED
    change volume (T₁.carrier ∩ T₀.carrier) ≤
      (1 / 2 : ENNReal) * max (volume T₁.carrier) (volume T₀.carrier)
    rw [← ENNReal.ofReal_toReal hinter_fin, ← ENNReal.ofReal_toReal hRHS_ne]
    apply ENNReal.ofReal_le_ofReal
    change volume.real (T₁.carrier ∩ T₀.carrier) ≤
      ((1 / 2 : ENNReal) * max (volume T₁.carrier) (volume T₀.carrier)).toReal
    rw [ENNReal.toReal_mul, show ((1 / 2 : ENNReal).toReal : ℝ) = 1 / 2 by simp]
    have hmax_to : (max (volume T₁.carrier) (volume T₀.carrier)).toReal =
        max (volume T₁.carrier).toReal (volume T₀.carrier).toReal := by
      rcases le_total (volume T₁.carrier) (volume T₀.carrier) with hle | hle
      · rw [max_eq_right hle, max_eq_right (ENNReal.toReal_mono hT0_fin hle)]
      · rw [max_eq_left hle, max_eq_left (ENNReal.toReal_mono hT1_fin hle)]
    rw [hmax_to]
    exact h_le
  -- Extract a point p ∈ T₁ ∩ T₀ using positive volume.
  have h_vol_pos : 0 < volume.real (T₁.carrier ∩ T₀.carrier) := by
    set n := Module.finrank ℝ E
    have h_T0_lb : c_n * (δ : ℝ) ^ (n - 1) ≤ volume.real T₀.carrier := hc_n_bound δ hδ T₀
    have hpow_pos : 0 < c_n * (δ : ℝ) ^ (n - 1) := mul_pos hc_n_pos (pow_pos hδr _)
    have h_T0_pos : 0 < volume.real T₀.carrier := lt_of_lt_of_le hpow_pos h_T0_lb
    have h_max_pos : 0 < max (volume.real T₁.carrier) (volume.real T₀.carrier) :=
      lt_max_of_lt_right h_T0_pos
    have : (1/2 : ℝ) * max (volume.real T₁.carrier) (volume.real T₀.carrier)
        < volume.real (T₁.carrier ∩ T₀.carrier) := by
      linarith [not_le.mp h_notED_real]
    have h2 : 0 < (1/2 : ℝ) * max (volume.real T₁.carrier) (volume.real T₀.carrier) := by
      positivity
    linarith
  have h_nonempty : (T₁.carrier ∩ T₀.carrier).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at h_vol_pos
    simp at h_vol_pos
  obtain ⟨p, hp1, hp0⟩ := h_nonempty
  -- Unpack p ∈ T₀ to get z₀ ∈ segment, dist p z₀ ≤ δ.
  rw [T₀.carrier_eq, Set.mem_iUnion₂] at hp0
  obtain ⟨z₀, hz₀_seg, hp_z₀⟩ := hp0
  obtain ⟨a₀, b₀, ha₀, hb₀, hab₀, hz₀_eq⟩ := hz₀_seg
  set s₀ : ℝ := b₀ - 1/2 with hs₀_def
  have hs₀_abs : |s₀| ≤ 1/2 := by rw [hs₀_def]; rw [abs_le]; constructor <;> linarith
  have hz₀_alt : z₀ = T₀.midpoint + s₀ • u := by
    have ha₀_eq : a₀ = 1 - b₀ := by linarith
    rw [← hz₀_eq, hu_def, Tube.midpoint]
    change a₀ • T₀.x + b₀ • T₀.y = (1/2 : ℝ) • (T₀.x + T₀.y) + s₀ • (T₀.y - T₀.x)
    rw [smul_add, smul_sub, ha₀_eq, hs₀_def]
    match_scalars <;> ring
  -- Unpack p ∈ T₁ to get z₁ ∈ segment, dist p z₁ ≤ δ.
  rw [T₁.carrier_eq, Set.mem_iUnion₂] at hp1
  obtain ⟨z₁, hz₁_seg, hp_z₁⟩ := hp1
  obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hz₁_eq⟩ := hz₁_seg
  set s₁ : ℝ := b₁ - 1/2 with hs₁_def
  have hs₁_abs : |s₁| ≤ 1/2 := by rw [hs₁_def]; rw [abs_le]; constructor <;> linarith
  have hz₁_alt : z₁ = T₁.midpoint + s₁ • v := by
    have ha₁_eq : a₁ = 1 - b₁ := by linarith
    rw [← hz₁_eq, hv_def, Tube.midpoint]
    change a₁ • T₁.x + b₁ • T₁.y = (1/2 : ℝ) • (T₁.x + T₁.y) + s₁ • (T₁.y - T₁.x)
    rw [smul_add, smul_sub, ha₁_eq, hs₁_def]
    match_scalars <;> ring
  have hp_z₀_norm : ‖p - z₀‖ ≤ (δ : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hp_z₀
    exact hp_z₀
  have hp_z₁_norm : ‖p - z₁‖ ≤ (δ : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hp_z₁
    exact hp_z₁
  set I_w : ℝ := inner ℝ w u with hI_w_def
  have h_inner_eps : inner ℝ w (ε • u) = ε * I_w := by
    rw [inner_smul_right, hI_w_def]
  have h_proj_term : (inner ℝ w (ε • u)) • (ε • u) = I_w • u := by
    rw [h_inner_eps]
    rw [show (ε * I_w) • (ε • u) = (ε * ε * I_w) • u from by
      rw [smul_smul]; congr 1; ring]
    rw [hε_sq, one_mul]
  have h_inn_pz0_abs : |inner ℝ (p - z₀) u| ≤ (δ : ℝ) := by
    calc |inner ℝ (p - z₀) u|
        ≤ ‖p - z₀‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ ≤ (δ : ℝ) * 1 := by gcongr; rw [hu_norm]
      _ = (δ : ℝ) := by ring
  have h_inn_pz1_abs : |inner ℝ (p - z₁) u| ≤ (δ : ℝ) := by
    calc |inner ℝ (p - z₁) u|
        ≤ ‖p - z₁‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ ≤ (δ : ℝ) * 1 := by gcongr; rw [hu_norm]
      _ = (δ : ℝ) := by ring
  have h_inn_p_T0 : inner ℝ (p - T₀.midpoint) u
      = inner ℝ (p - z₀) u + s₀ := by
    have hp_split : p - T₀.midpoint = (p - z₀) + s₀ • u := by
      rw [hz₀_alt]; abel
    rw [hp_split, inner_add_left, inner_smul_left, h_inner_u_u]
    simp
  have h_inn_p_T0_abs : |inner ℝ (p - T₀.midpoint) u| ≤ (δ : ℝ) + 1/2 := by
    rw [h_inn_p_T0]
    calc |inner ℝ (p - z₀) u + s₀|
        ≤ |inner ℝ (p - z₀) u| + |s₀| := abs_add_le _ _
      _ ≤ (δ : ℝ) + 1/2 := by linarith
  have h_inn_p_T1 : inner ℝ (p - T₁.midpoint) u
      = inner ℝ (p - z₁) u + s₁ * inner ℝ v u := by
    have hp_split : p - T₁.midpoint = (p - z₁) + s₁ • v := by
      rw [hz₁_alt]; abel
    rw [hp_split, inner_add_left, inner_smul_left]
    simp
  have h_vu_abs : |inner ℝ v u| ≤ 1 := by
    calc |inner ℝ v u|
        ≤ ‖v‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [hv_norm, hu_norm]; ring
  have h_inn_p_T1_abs : |inner ℝ (p - T₁.midpoint) u| ≤ (δ : ℝ) + 1/2 := by
    rw [h_inn_p_T1]
    have h2 : |s₁ * inner ℝ v u| ≤ 1/2 := by
      rw [abs_mul]
      calc |s₁| * |inner ℝ v u|
          ≤ (1/2) * 1 := by gcongr
        _ = 1/2 := by ring
    calc |inner ℝ (p - z₁) u + s₁ * inner ℝ v u|
        ≤ |inner ℝ (p - z₁) u| + |s₁ * inner ℝ v u| := abs_add_le _ _
      _ ≤ (δ : ℝ) + 1/2 := by linarith
  have hI_w_eq : I_w = inner ℝ (p - T₀.midpoint) u - inner ℝ (p - T₁.midpoint) u := by
    rw [hI_w_def, hw_def]
    have heq : T₁.midpoint - T₀.midpoint = (p - T₀.midpoint) - (p - T₁.midpoint) := by abel
    rw [heq, inner_sub_left]
  have hI_w_abs : |I_w| ≤ 3 := by
    rw [hI_w_eq]
    calc |inner ℝ (p - T₀.midpoint) u - inner ℝ (p - T₁.midpoint) u|
        ≤ |inner ℝ (p - T₀.midpoint) u| + |inner ℝ (p - T₁.midpoint) u| := abs_sub _ _
      _ ≤ ((δ : ℝ) + 1/2) + ((δ : ℝ) + 1/2) := by linarith
      _ ≤ 3 := by linarith
  have h_long : |inner ℝ w (ε • u)| ≤ 3 := by
    rw [h_inner_eps, abs_mul, hε_abs, one_mul]
    exact hI_w_abs
  -- Perpendicular bound.
  have norm_perp_le : ∀ (a : E), ‖a - (inner ℝ a u) • u‖ ≤ ‖a‖ := by
    intro a
    have hsq : ‖a - (inner ℝ a u) • u‖ ^ 2 = ‖a‖ ^ 2 - (inner ℝ a u) ^ 2 := by
      rw [norm_sub_sq_real]
      rw [inner_smul_right]
      rw [norm_smul, Real.norm_eq_abs, hu_norm, mul_one, sq_abs]
      ring
    have hsq_le : ‖a - (inner ℝ a u) • u‖ ^ 2 ≤ ‖a‖ ^ 2 := by
      rw [hsq]
      linarith [sq_nonneg (inner ℝ a u)]
    exact abs_le_of_sq_le_sq' hsq_le (norm_nonneg _) |>.2
  set q₀ : E := (p - T₀.midpoint) - (inner ℝ (p - T₀.midpoint) u) • u with hq₀_def
  set q₁ : E := (p - T₁.midpoint) - (inner ℝ (p - T₁.midpoint) u) • u with hq₁_def
  have h_w_minus : w - I_w • u = q₀ - q₁ := by
    rw [hq₀_def, hq₁_def, hw_def, hI_w_eq, sub_smul]
    abel
  have hq₀_norm : ‖q₀‖ ≤ (δ : ℝ) := by
    have hp_split : p - T₀.midpoint = (p - z₀) + s₀ • u := by
      rw [hz₀_alt]; abel
    have hq₀_eq : q₀ = (p - z₀) - (inner ℝ (p - z₀) u) • u := by
      rw [hq₀_def, hp_split, inner_add_left, inner_smul_left, h_inner_u_u]
      change p - z₀ + s₀ • u - (inner ℝ (p - z₀) u + (starRingEnd ℝ) s₀ * 1) • u
          = p - z₀ - inner ℝ (p - z₀) u • u
      rw [RCLike.conj_to_real]
      module
    rw [hq₀_eq]
    exact (norm_perp_le _).trans hp_z₀_norm
  have hq₁_norm : ‖q₁‖ ≤ (1 + C_dir / 2) * (δ : ℝ) := by
    have hp_split : p - T₁.midpoint = (p - z₁) + s₁ • v := by
      rw [hz₁_alt]; abel
    have hq₁_eq : q₁ = ((p - z₁) - (inner ℝ (p - z₁) u) • u)
        + s₁ • (v - (inner ℝ v u) • u) := by
      rw [hq₁_def, hp_split, inner_add_left, inner_smul_left]
      change p - z₁ + s₁ • v - (inner ℝ (p - z₁) u + (starRingEnd ℝ) s₁ * inner ℝ v u) • u
          = (p - z₁ - inner ℝ (p - z₁) u • u) + s₁ • (v - inner ℝ v u • u)
      rw [RCLike.conj_to_real]
      module
    have h_perp_v : ‖v - (inner ℝ v u) • u‖ ≤ C_dir * (δ : ℝ) := by
      have h_inn_v_eps_u : inner ℝ (ε • u) u = ε := by
        rw [inner_smul_left, h_inner_u_u, RCLike.conj_to_real, mul_one]
      have h_inn_sub : inner ℝ (v - ε • u) u = inner ℝ v u - ε := by
        rw [inner_sub_left, h_inn_v_eps_u]
      have h_eq : v - (inner ℝ v u) • u =
          (v - ε • u) - (inner ℝ (v - ε • u) u) • u := by
        rw [h_inn_sub, sub_smul]
        abel
      rw [h_eq]
      exact (norm_perp_le _).trans hε_bound
    have h1 : ‖(p - z₁) - (inner ℝ (p - z₁) u) • u‖ ≤ (δ : ℝ) :=
      (norm_perp_le _).trans hp_z₁_norm
    have h2 : ‖s₁ • (v - (inner ℝ v u) • u)‖ ≤ (1/2) * (C_dir * (δ : ℝ)) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hs₁_abs h_perp_v (norm_nonneg _) (by norm_num)
    calc ‖q₁‖
        = ‖((p - z₁) - (inner ℝ (p - z₁) u) • u) + s₁ • (v - (inner ℝ v u) • u)‖ := by rw [hq₁_eq]
      _ ≤ ‖(p - z₁) - (inner ℝ (p - z₁) u) • u‖ + ‖s₁ • (v - (inner ℝ v u) • u)‖ :=
          norm_add_le _ _
      _ ≤ (δ : ℝ) + (1/2) * (C_dir * (δ : ℝ)) := add_le_add h1 h2
      _ = (1 + C_dir / 2) * (δ : ℝ) := by ring
  have h_perp : ‖w - I_w • u‖ ≤ (2 + C_dir / 2) * (δ : ℝ) := by
    rw [h_w_minus]
    calc ‖q₀ - q₁‖
        ≤ ‖q₀‖ + ‖q₁‖ := norm_sub_le _ _
      _ ≤ (δ : ℝ) + (1 + C_dir / 2) * (δ : ℝ) := by linarith
      _ = (2 + C_dir / 2) * (δ : ℝ) := by ring
  refine ⟨ε, hε, ?_, h_long⟩
  change ‖T₁.midpoint - T₀.midpoint -
      (inner ℝ (T₁.midpoint - T₀.midpoint) (ε • u)) • (ε • u)‖ ≤ (2 + C_dir / 2) * (δ : ℝ)
  rw [show T₁.midpoint - T₀.midpoint = w from rfl, h_proj_term]
  exact h_perp

end
end Kakeya
