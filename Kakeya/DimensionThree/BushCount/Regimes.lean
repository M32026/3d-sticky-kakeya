/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Geo_notEDbound.EssDistBound
public import Kakeya.Mathlib.FinsetFiber
public import Kakeya.Mathlib.Topology.SphereNet
public import Kakeya.Tube.CommonPoint

/-!
# The two regimes of the bush bound

The geometric heart of the bush bound `Kakeya.bushCount_exists`: for `δ` below the threshold
of the packing bound the tubes through a point are grouped into direction classes, and above
that threshold the crude packing bound already suffices. Both regimes bound
`|s| * δ ^ 2` by an absolute constant, and `Kakeya/DimensionThree/BushCount.lean` combines
them.
-/

@[expose] public section

namespace Kakeya

/-- Small-`δ` regime of the bush bound. Below a threshold `δ₀` supplied by
`Kakeya.packing_card_le_of_features`, the number of pairwise essentially distinct `δ`-tubes
through a point `x` is at most `K * δ ^ (-2)`.

The unit directions of the tubes are grouped by a `δ`-net `Θ` of the unit sphere, of which
`Metric.exists_finset_sphere_net` provides at most `192 * δ ^ (-2)` elements in dimension
`3`; each class contains at most `C_small` tubes by the packing bound, whose features are
supplied by `Kakeya.bushFeatures`. -/
lemma bushCount.exists_bound_small :
    ∃ (δ₀ : ℝ) (K : ℕ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type*} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ δ₀ →
        ∀ (s : Finset ι) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))),
          (s : Set ι).Pairwise
            (fun i j ↦ IsEssentiallyDistinct (T i).carrier (T j).carrier) →
          ∀ x : EuclideanSpace ℝ (Fin 3), (∀ i ∈ s, x ∈ (T i).carrier) →
            (s.card : ℝ) * (δ : ℝ) ^ (2 : ℕ) ≤ (K : ℝ) := by
  classical
  have hn : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 :=
      finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)
    rw [hfinrank]
    norm_num
  have hn2 : 2 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 :=
      finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)
    rw [hfinrank]
    norm_num
  obtain ⟨δ₀, C_small, hδ₀_pos, hδ₀_le1, hC_pos, hpack⟩ :=
    packing_card_le_of_features (E := EuclideanSpace ℝ (Fin 3)) hn 2 6 3
      (by norm_num) (by norm_num) (by norm_num)
  refine ⟨δ₀, 192 * C_small, hδ₀_pos, hδ₀_le1, ?_⟩
  intro ι δ hδ hδ_le s T hED x hx
  by_cases hs : s.Nonempty
  · have hδ_le1 : (δ : ℝ) ≤ 1 := hδ_le.trans hδ₀_le1
    have hδ_pos_real : 0 < (δ : ℝ) := by exact_mod_cast hδ
    obtain ⟨Θ, hΘ_unit, hΘ_card, hΘ_cover⟩ :=
      Metric.exists_finset_sphere_net (E := EuclideanSpace ℝ (Fin 3)) hn2 hδ_pos_real hδ_le1
    -- classification of tube directions into classes Θ
    choose cls hcls_mem hcls_dist using fun i : ι => hΘ_cover ((T i).direction) (T i).norm_direction
    have hcls_mem_s (i : ι) (hi : i ∈ s) : cls i ∈ Θ := hcls_mem i
    have hcls_norm_dist (i : ι) (hi : i ∈ s) : ‖(T i).direction - cls i‖ ≤ (δ : ℝ) := by
      have hdist := hcls_dist i
      rw [dist_eq_norm] at hdist
      exact hdist
    -- fibre bound
    have hfiber : ∀ w ∈ Θ, (s.filter fun i => cls i = w).card ≤ C_small := by
      intro w hw
      by_cases hfib_nonempty : (s.filter fun i => cls i = w).Nonempty
      · obtain ⟨i₀, hi₀⟩ := hfib_nonempty
        have hi₀_s : i₀ ∈ s := (Finset.mem_filter.mp hi₀).1
        have h_cls_i₀ : cls i₀ = w := (Finset.mem_filter.mp hi₀).2
        have hfib_x : ∀ i ∈ (s.filter fun i => cls i = w), x ∈ (T i).carrier := by
          intro i hi
          exact hx i ((Finset.mem_filter.mp hi).1)
        have hfib_hu : ∀ i ∈ (s.filter fun i => cls i = w), ‖(T i).direction - w‖ ≤ (δ : ℝ) := by
          intro i hi
          have hi_s : i ∈ s := (Finset.mem_filter.mp hi).1
          have h_cls_i : cls i = w := (Finset.mem_filter.mp hi).2
          have hnorm := hcls_norm_dist i hi_s
          rw [h_cls_i] at hnorm
          exact hnorm
        have hfib_features : ∀ i ∈ (s.filter fun i => cls i = w), ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
            ‖ε • (T i).direction - (T i₀).direction‖ ≤ 2 * (δ : ℝ) ∧
            ‖((T i).midpoint - (T i₀).midpoint) -
              (inner ℝ ((T i).midpoint - (T i₀).midpoint) (T i₀).direction) • (T i₀).direction‖
              ≤ 6 * (δ : ℝ) ∧
            |inner ℝ ((T i).midpoint - (T i₀).midpoint) (T i₀).direction| ≤ 3 :=
          bushFeatures hδ_le1 (s.filter fun i => cls i = w) T x w hi₀ hfib_x hfib_hu
        have hpairwise : ((s.filter fun i => cls i = w) : Set ι).Pairwise
            (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) :=
          hED.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
        have hcard_fib :=
          hpack hδ hδ_le (s.filter fun i => cls i = w) T (T i₀) hpairwise hfib_features
        exact hcard_fib
      · have hcard0 : (s.filter fun i => cls i = w).card = 0 :=
          Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hfib_nonempty)
        have hpos : 0 ≤ C_small := Nat.zero_le _
        rw [hcard0]
        exact hpos
    have hcard : s.card ≤ Θ.card * C_small :=
      Finset.card_le_mul_of_fiber_card_le s Θ cls (fun i hi => hcls_mem i) C_small hfiber
    have hfinrank3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 :=
      finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)
    have hΘ_card_real : (Θ.card : ℝ) * ((δ : ℝ) ^ (2 : ℕ)) ≤ 192 := by
      have h_card_expr :
          (Θ.card : ℝ) * ((δ : ℝ) ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1)) ≤
          Metric.sphereSeparatedCount.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := hΘ_card
      rw [hfinrank3] at h_card_expr
      have : Metric.sphereSeparatedCount.C 3 = 192 := by
        unfold Metric.sphereSeparatedCount.C
        norm_num
      rw [this] at h_card_expr
      have h_sub : (3 : ℕ) - 1 = (2 : ℕ) := by norm_num
      rw [h_sub] at h_card_expr
      -- Now we have (Θ.card : ℝ) * (δ : ℝ) ^ (2 : ℕ) ≤ 192
      exact h_card_expr
    have h_nonneg_sq : 0 ≤ (δ : ℝ) ^ (2 : ℕ) := by positivity
    have h_nonneg_card : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
    calc
      (s.card : ℝ) * (δ : ℝ) ^ (2 : ℕ) ≤ ((Θ.card * C_small : ℕ) : ℝ) * (δ : ℝ) ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) h_nonneg_sq
      _ = ((Θ.card : ℝ) * (δ : ℝ) ^ (2 : ℕ)) * (C_small : ℝ) := by
        push_cast
        ring
      _ ≤ (192 : ℝ) * (C_small : ℝ) := by
        exact mul_le_mul_of_nonneg_right hΘ_card_real (Nat.cast_nonneg C_small)
      _ = ((192 * C_small : ℕ) : ℝ) := by
        push_cast
        ring
  · have h_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hcard0 : s.card = 0 := by simp [h_empty]
    have hcard0_real : (s.card : ℝ) = 0 := by exact_mod_cast hcard0
    calc
      (s.card : ℝ) * (δ : ℝ) ^ (2 : ℕ) = 0 := by
        rw [hcard0_real, zero_mul]
      _ ≤ ((192 * C_small : ℕ) : ℝ) := by positivity

/-- Large-`δ` regime of the bush bound. Above any positive threshold `δ₀` the crude packing
bound `Kakeya.packing_card_le_of_features_large` already bounds the number of pairwise
essentially distinct `δ`-tubes through a point by a constant, and `δ ^ 2 ≤ 1`. -/
lemma bushCount.exists_bound_large {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ K : ℕ,
      ∀ {ι : Type*} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 → δ₀ < (δ : ℝ) →
        ∀ (s : Finset ι) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))),
          (s : Set ι).Pairwise
            (fun i j ↦ IsEssentiallyDistinct (T i).carrier (T j).carrier) →
          ∀ x : EuclideanSpace ℝ (Fin 3), (∀ i ∈ s, x ∈ (T i).carrier) →
            (s.card : ℝ) * (δ : ℝ) ^ (2 : ℕ) ≤ (K : ℝ) := by
  have hn : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 :=
      finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)
    rw [hfinrank]
    norm_num
  have hCmid : (0 : ℝ) ≤ 3 := by norm_num
  obtain ⟨C_large, _, hpack⟩ :=
    packing_card_le_of_features_large (E := EuclideanSpace ℝ (Fin 3)) hn (3 : ℝ) hCmid δ₀ hδ₀
  refine ⟨C_large, ?_⟩
  intro ι δ hδ hδ1 hδ_gt s T h_pairwise x hx_mem
  by_cases hs : s.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hs
    let T₀ := T i₀
    have h_midpoint_bd : ∀ i ∈ s, ‖(T i).midpoint - T₀.midpoint‖ ≤ 3 := by
      intro i hi
      have h_norm := norm_midpoint_sub_le_of_common_mem (hx_mem i hi) (hx_mem i₀ hi₀)
      have h_bound : 1 + 2 * (δ : ℝ) ≤ 3 := by nlinarith
      nlinarith
    have h_card_nat : s.card ≤ C_large :=
      hpack hδ hδ1 hδ_gt s T T₀ h_pairwise h_midpoint_bd
    have h_card_real : (s.card : ℝ) ≤ (C_large : ℝ) := Nat.cast_le.mpr h_card_nat
    have hδ_sq_le_one : (δ : ℝ) ^ (2 : ℕ) ≤ 1 := by
      have hδ_nonneg : 0 ≤ (δ : ℝ) := NNReal.coe_nonneg _
      exact pow_le_one₀ hδ_nonneg hδ1
    have h_nonneg_card : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
    calc
      (s.card : ℝ) * (δ : ℝ) ^ (2 : ℕ) ≤ (s.card : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hδ_sq_le_one h_nonneg_card
      _ = (s.card : ℝ) := by ring
      _ ≤ (C_large : ℝ) := h_card_real
  · have h_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hcard0 : s.card = 0 := by simp [h_empty]
    have hcard0_real : (s.card : ℝ) = 0 := by exact_mod_cast hcard0
    calc
      (s.card : ℝ) * (δ : ℝ) ^ (2 : ℕ) = 0 := by
        rw [hcard0_real, zero_mul]
      _ ≤ (C_large : ℝ) := Nat.cast_nonneg _

end Kakeya
