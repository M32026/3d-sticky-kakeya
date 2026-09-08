/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Real

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Finite nets in Euclidean spaces

Dimension-dependent finite nets for the unit sphere and bounded Euclidean balls.

* `exists_sphere_net` — a finite ε-net on the unit sphere `S^(n-1)`
  with cardinality `≤ C_dir(E) · ε^(-(n-1))`.

* `exists_ball_net` — a finite ε-net for the closed ball
  `B(0, 5/2)` of cardinality `≤ C_pos(E) · ε^(-n)`, contained in `B(0, 3)`.
-/

@[expose] public section

open MeasureTheory Metric

namespace Kakeya

namespace EuclideanNet

variable
  (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The unit ball volume of `E`, real-valued, is positive. -/
private lemma volume_real_unitBall_pos :
    0 < volume.real (Metric.closedBall (0 : E) 1) := by
  have hpos : 0 < volume (Metric.ball (0 : E) 1) :=
    Metric.measure_ball_pos volume 0 one_pos
  have hfin : volume (Metric.closedBall (0 : E) 1) < ⊤ :=
    MeasureTheory.measure_closedBall_lt_top
  have hfin' : volume (Metric.ball (0 : E) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin.ne (measure_mono ball_subset_closedBall)
  have h2 : 0 < volume.real (Metric.ball (0 : E) 1) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hpos.ne' hfin'
  have h1 : volume.real (Metric.ball (0 : E) 1) ≤ volume.real (Metric.closedBall (0 : E) 1) :=
    measureReal_mono ball_subset_closedBall hfin.ne
  linarith

/-- Volume of closed ball of radius `r` in finite-dim `E` (real-valued). -/
private lemma volume_real_closedBall_eq (r : ℝ) (hr : 0 ≤ r) :
    volume.real (Metric.closedBall (0 : E) r) =
      r ^ Module.finrank ℝ E * volume.real (Metric.closedBall (0 : E) 1) :=
  MeasureTheory.Measure.addHaar_real_closedBall' volume 0 hr

/-- Algebraic bound: `(1+ε/2)^n - (1-ε/2)^n ≤ n · ε · (3/2)^(n-1)` for `0 < ε ≤ 1`. -/
private lemma pow_shell_diff_le (n : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (1 + ε/2)^n - (1 - ε/2)^n ≤ (n : ℝ) * ε * (3/2)^(n-1) := by
  have h_outer_nn : (0:ℝ) ≤ 1 + ε/2 := by linarith
  have h_inner_nn : (0:ℝ) ≤ 1 - ε/2 := by linarith
  have h := abs_pow_sub_pow_le (a := 1 + ε/2) (b := 1 - ε/2) (n := n)
  have h_diff : (1 + ε/2) - (1 - ε/2) = ε := by ring
  have h_max : max |1 + ε/2| |1 - ε/2| ≤ 3/2 := by
    rw [abs_of_nonneg h_outer_nn, abs_of_nonneg h_inner_nn]
    apply max_le <;> linarith
  have h_diff_nn : (1+ε/2)^n - (1-ε/2)^n ≥ 0 := by
    apply sub_nonneg.mpr
    apply pow_le_pow_left₀ h_inner_nn
    linarith
  have h_abs : |(1+ε/2)^n - (1-ε/2)^n| = (1+ε/2)^n - (1-ε/2)^n :=
    abs_of_nonneg h_diff_nn
  rw [h_abs] at h
  have h_abs_diff : |(1 + ε/2) - (1 - ε/2)| = ε := by
    rw [h_diff]; exact abs_of_pos hε
  rw [h_abs_diff] at h
  calc (1+ε/2)^n - (1-ε/2)^n
      ≤ ε * n * max |1 + ε/2| |1 - ε/2| ^ (n - 1) := h
    _ ≤ ε * n * (3/2) ^ (n - 1) := by gcongr
    _ = (n : ℝ) * ε * (3/2) ^ (n - 1) := by ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] in
/-- Each ball of radius `ε/2` around a unit vector lies in the closed ball of
radius `1 + ε/2`. -/
private lemma ball_unit_subset_outerBall
    (ε : ℝ) (_hε : 0 < ε) (_hε1 : ε ≤ 1) (u : E) (hu : ‖u‖ = 1) :
    Metric.ball u (ε/2) ⊆ Metric.closedBall (0 : E) (1 + ε/2) := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖x‖ = ‖u + (x - u)‖ := by rw [add_sub_cancel]
    _ ≤ ‖u‖ + ‖x - u‖ := norm_add_le _ _
    _ = 1 + ‖x - u‖ := by rw [hu]
    _ ≤ 1 + ε/2 := by linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] in
/-- Each ball of radius `ε/2` around a unit vector is disjoint from the open
ball of radius `1 - ε/2`. -/
private lemma ball_unit_disjoint_innerBall
    (ε : ℝ) (_hε : 0 < ε) (_hε1 : ε ≤ 1) (u : E) (hu : ‖u‖ = 1) :
    Disjoint (Metric.ball u (ε/2)) (Metric.ball (0 : E) (1 - ε/2)) := by
  apply Metric.ball_disjoint_ball
  rw [dist_zero_right, hu]
  linarith

/-- The dimensional cardinality constant for `exists_sphere_net`. -/
noncomputable def sphereNetConstant : ℝ :=
  (Module.finrank ℝ E : ℝ) * (3 / 2) ^ (Module.finrank ℝ E - 1) *
    2 ^ Module.finrank ℝ E + 1

omit [MeasurableSpace E] [BorelSpace E] in
/-- The sphere-net cardinality constant is positive. -/
lemma sphereNetConstant_pos [Nontrivial E] : 0 < sphereNetConstant E := by
  unfold sphereNetConstant
  have hn : 0 < Module.finrank ℝ E := Module.finrank_pos
  positivity

/-- **Brick 1.** Finite ε-net on the unit sphere `S^(n-1) ⊂ E`.

For every `ε ∈ (0, 1]` there is a finite set `U` of unit vectors of
cardinality at most `C_dir(E) · ε^(-(n-1))` such that every unit vector
of `E` lies within distance `ε` of some `u ∈ U`. The constant `C_dir(E)`
depends only on the dimension.

Strategy: take a maximal ε-separated subset `U` of the unit sphere. By
volume comparison the open balls `B(u, ε/2)` are pairwise disjoint and
all lie in the annular shell `B̄(0, 1+ε/2) \ B(0, 1-ε/2)`, giving the
cardinality bound. Maximality forces the covering property. -/
lemma exists_sphere_net
    [Nontrivial E] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ U : Finset E,
      (∀ u ∈ U, ‖u‖ = 1) ∧
      (U.card : ℝ) ≤ sphereNetConstant E *
        ε ^ (-((Module.finrank ℝ E : ℝ) - 1)) ∧
      ∀ u : E, ‖u‖ = 1 → ∃ u' ∈ U, ‖u' - u‖ ≤ ε := by
  classical
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  have hn : 0 < Module.finrank ℝ E := Module.finrank_pos
  set n := Module.finrank ℝ E with hn_def
  set v₁ : ℝ := volume.real (Metric.closedBall (0 : E) 1) with hv₁_def
  have hv₁_pos : 0 < v₁ := volume_real_unitBall_pos E
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ge1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  change ∃ U : Finset E,
    (∀ u ∈ U, ‖u‖ = 1) ∧
    (U.card : ℝ) ≤ ((n : ℝ) * (3 / 2) ^ (n - 1) * 2 ^ n + 1) *
      ε ^ (-((n : ℝ) - 1)) ∧
    ∀ u : E, ‖u‖ = 1 → ∃ u' ∈ U, ‖u' - u‖ ≤ ε
  set P : ℕ → Prop := fun k => ∃ s : Finset E,
    s.card = k ∧ (∀ u ∈ s, ‖u‖ = 1) ∧
      ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ε ≤ ‖u - v‖
  have hP0 : P 0 := ⟨∅, by simp, by simp, by simp⟩
  have hvol_closedBall : ∀ (x : E) (r : ℝ), 0 ≤ r →
      volume.real (Metric.closedBall x r) = r ^ n * v₁ := by
    intro x r hr
    have h_trans : volume.real (Metric.closedBall x r) =
                   volume.real (Metric.closedBall (0 : E) r) := by
      rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
      congr 1
      exact MeasureTheory.Measure.addHaar_closedBall_center volume x r
    rw [h_trans, volume_real_closedBall_eq E r hr]
  have key_bound : ∀ k, P k → (k : ℝ) ≤ (n : ℝ) * (3/2) ^ (n - 1) * 2 ^ n *
                                          ε ^ (-((n : ℝ) - 1)) := by
    intro k hPk
    obtain ⟨s, hs_card, hs_unit, hs_sep⟩ := hPk
    have hε2_nn : 0 ≤ ε/2 := by linarith
    have hball_disj : (s : Set E).PairwiseDisjoint
        (fun u : E => Metric.ball u (ε/2)) := by
      intro u hu v hv huv
      apply Metric.ball_disjoint_ball
      have : ε ≤ ‖u - v‖ := hs_sep u hu v hv huv
      rw [dist_eq_norm]
      linarith
    have hball_meas : ∀ u : E, MeasurableSet (Metric.ball u (ε/2)) := fun u =>
      Metric.isOpen_ball.measurableSet
    have hvol_openBall : ∀ x : E, volume.real (Metric.ball x (ε/2)) =
        (ε/2) ^ n * v₁ := by
      intro x
      have : volume.real (Metric.ball x (ε/2)) =
             volume.real (Metric.closedBall x (ε/2)) := by
        rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
        congr 1
        exact (MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball volume x (ε/2)).symm
      rw [this, hvol_closedBall x (ε/2) hε2_nn]
    set shell : Set E := Metric.closedBall (0 : E) (1 + ε/2) \
                          Metric.ball (0 : E) (1 - ε/2) with hshell_def
    have hUnion_sub_shell :
        (⋃ u ∈ s, Metric.ball u (ε/2)) ⊆ shell := by
      intro x hx
      simp only [Set.mem_iUnion, exists_prop] at hx
      obtain ⟨u, hu, hxu⟩ := hx
      have hsub := ball_unit_subset_outerBall E ε hε hε1 u (hs_unit u hu) hxu
      have hdisj := ball_unit_disjoint_innerBall E ε hε hε1 u (hs_unit u hu)
      exact ⟨hsub, Set.disjoint_left.mp hdisj hxu⟩
    have hshell_fin : volume shell < ⊤ := by
      apply lt_of_le_of_lt (measure_mono (Set.sdiff_subset (s := _) (t := _)))
      exact MeasureTheory.measure_closedBall_lt_top
    have houter_nn : (0:ℝ) ≤ 1 + ε/2 := by linarith
    have hinner_nn : (0:ℝ) ≤ 1 - ε/2 := by linarith
    have hsub_oo : Metric.ball (0 : E) (1 - ε/2) ⊆ Metric.closedBall (0 : E) (1 + ε/2) := by
      intro x hx
      rw [Metric.mem_ball, dist_zero_right] at hx
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    have hfin_outer : volume (Metric.closedBall (0 : E) (1 + ε/2)) < ⊤ :=
      MeasureTheory.measure_closedBall_lt_top
    have hfin_inner_ne : volume (Metric.ball (0 : E) (1 - ε/2)) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin_outer.ne (measure_mono hsub_oo)
    have hdisj_shell_inner : Disjoint shell (Metric.ball (0 : E) (1 - ε/2)) :=
      Set.disjoint_sdiff_left
    have hball_inner_meas : MeasurableSet (Metric.ball (0 : E) (1 - ε/2)) :=
      Metric.isOpen_ball.measurableSet
    have hUnion : shell ∪ Metric.ball (0 : E) (1 - ε/2) =
        Metric.closedBall (0 : E) (1 + ε/2) := by
      rw [hshell_def, Set.sdiff_union_self, Set.union_eq_left.mpr hsub_oo]
    have hadd : volume.real shell + volume.real (Metric.ball (0 : E) (1 - ε/2)) =
        volume.real (Metric.closedBall (0 : E) (1 + ε/2)) := by
      have hreal_union :
          volume.real (shell ∪ Metric.ball (0 : E) (1 - ε/2)) =
            volume.real shell + volume.real (Metric.ball (0 : E) (1 - ε/2)) := by
        rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
            MeasureTheory.measureReal_def,
            MeasureTheory.measure_union hdisj_shell_inner hball_inner_meas]
        rw [ENNReal.toReal_add]
        · exact lt_of_le_of_lt (measure_mono Set.subset_union_left)
            (by rw [hUnion]; exact hfin_outer) |>.ne
        · exact hfin_inner_ne
      rw [← hreal_union, hUnion]
    have hinner_real : volume.real (Metric.ball (0 : E) (1 - ε/2)) =
        (1 - ε/2)^n * v₁ := by
      have h_eq : volume.real (Metric.ball (0 : E) (1 - ε/2)) =
                   volume.real (Metric.closedBall (0 : E) (1 - ε/2)) := by
        rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
        congr 1
        exact (MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball volume 0 (1 - ε/2)).symm
      rw [h_eq, hvol_closedBall 0 _ hinner_nn]
    have houter_real : volume.real (Metric.closedBall (0 : E) (1 + ε/2)) =
        (1 + ε/2)^n * v₁ := hvol_closedBall 0 _ houter_nn
    have hshell_eq : volume.real shell =
        ((1 + ε/2)^n - (1 - ε/2)^n) * v₁ := by
      have h2 := hadd
      rw [hinner_real, houter_real] at h2
      linarith
    have hshell_vol_le : volume.real shell ≤
        ((n : ℝ) * ε * (3/2)^(n - 1)) * v₁ := by
      rw [hshell_eq]
      have hdiff_le : (1 + ε/2)^n - (1 - ε/2)^n ≤ (n : ℝ) * ε * (3/2) ^ (n - 1) :=
        pow_shell_diff_le n ε hε hε1
      exact mul_le_mul_of_nonneg_right hdiff_le hv₁_pos.le
    have hsum_ball_vol :
        ∑ u ∈ s, volume.real (Metric.ball u (ε/2)) ≤ volume.real shell := by
      have hUnion_le : volume (⋃ u ∈ s, Metric.ball u (ε/2)) ≤ volume shell :=
        measure_mono hUnion_sub_shell
      have hUnion_fin : volume (⋃ u ∈ s, Metric.ball u (ε/2)) ≠ ⊤ :=
        ne_top_of_le_ne_top hshell_fin.ne hUnion_le
      have h_eq_ennreal :
          volume (⋃ u ∈ s, Metric.ball u (ε/2)) = ∑ u ∈ s, volume (Metric.ball u (ε/2)) :=
        MeasureTheory.measure_biUnion_finset hball_disj (fun u _ => hball_meas u)
      have h_sum_eq : ∑ u ∈ s, volume.real (Metric.ball u (ε/2)) =
                       volume.real (⋃ u ∈ s, Metric.ball u (ε/2)) := by
        rw [MeasureTheory.measureReal_def, h_eq_ennreal]
        rw [ENNReal.toReal_sum]
        · rfl
        · intro u hu
          have hsub_one : Metric.ball u (ε/2) ⊆ ⋃ v ∈ s, Metric.ball v (ε/2) := by
            intro x hx
            exact Set.mem_iUnion₂.mpr ⟨u, hu, hx⟩
          exact ne_top_of_le_ne_top hUnion_fin (measure_mono hsub_one)
      rw [h_sum_eq]
      exact MeasureTheory.measureReal_mono hUnion_sub_shell hshell_fin.ne
    have hsum_eq : ∑ u ∈ s, volume.real (Metric.ball u (ε/2)) =
                   (s.card : ℝ) * ((ε/2) ^ n * v₁) := by
      simp_rw [hvol_openBall]
      rw [Finset.sum_const]
      ring
    have hsum_le : (s.card : ℝ) * ((ε/2)^n * v₁) ≤ ((n : ℝ) * ε * (3/2)^(n-1)) * v₁ := by
      calc (s.card : ℝ) * ((ε/2)^n * v₁) = _ := hsum_eq.symm
        _ ≤ volume.real shell := hsum_ball_vol
        _ ≤ _ := hshell_vol_le
    have hsum_le' : (s.card : ℝ) * (ε/2)^n ≤ (n : ℝ) * ε * (3/2)^(n-1) := by
      have h1 : (s.card : ℝ) * ((ε/2)^n * v₁) = ((s.card : ℝ) * (ε/2)^n) * v₁ := by ring
      rw [h1] at hsum_le
      exact le_of_mul_le_mul_right hsum_le hv₁_pos
    rw [hs_card] at hsum_le'
    have hε_pos_pow_n : 0 < (ε/2)^n := by positivity
    have h_card_bound : (k : ℝ) ≤ (n : ℝ) * ε * (3/2)^(n-1) / (ε/2)^n :=
      (le_div_iff₀ hε_pos_pow_n).mpr hsum_le'
    have h_eps2_pow : (ε/2)^n = ε^n / 2^n := by rw [div_pow]
    have h_div_eq : (n : ℝ) * ε * (3/2)^(n-1) / (ε/2)^n =
                     (n : ℝ) * (3/2)^(n-1) * 2^n * ε^(-((n : ℝ) - 1)) := by
      rw [h_eps2_pow]
      have h_rpow : ε ^ (-((n : ℝ) - 1)) = ε / ε^n := by
        rw [Real.rpow_neg hε.le]
        rw [show ((n : ℝ) - 1) = (n : ℝ) + (-1 : ℝ) by ring]
        rw [Real.rpow_add hε, Real.rpow_natCast, Real.rpow_neg_one]
        field_simp
      rw [h_rpow]
      field_simp
    rw [h_div_eq] at h_card_bound
    exact h_card_bound
  set Mreal : ℝ := (n : ℝ) * (3/2) ^ (n - 1) * 2 ^ n * ε ^ (-((n : ℝ) - 1)) with hMreal_def
  set M : ℕ := ⌈Mreal⌉₊ with hM_def
  have hM_ge : Mreal ≤ M := Nat.le_ceil _
  have hP_bound : ∀ k, P k → k ≤ M := fun k hPk => by
    have hk_real : (k : ℝ) ≤ Mreal := key_bound k hPk
    have : (k : ℝ) ≤ (M : ℝ) := le_trans hk_real hM_ge
    exact_mod_cast this
  set kmax : ℕ := Nat.findGreatest P M with hkmax_def
  have hkmax_P : P kmax := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  obtain ⟨U, hU_card, hU_unit, hU_sep⟩ := hkmax_P
  refine ⟨U, hU_unit, ?_, ?_⟩
  · have h1 : (U.card : ℝ) ≤ Mreal := by
      rw [hU_card]; exact key_bound kmax ⟨U, hU_card, hU_unit, hU_sep⟩
    have h2 : Mreal ≤ ((n : ℝ) * (3/2) ^ (n - 1) * 2 ^ n + 1) *
                ε ^ (-((n : ℝ) - 1)) := by
      rw [hMreal_def, add_mul, one_mul]
      have : 0 ≤ ε ^ (-((n : ℝ) - 1)) := Real.rpow_nonneg hε.le _
      linarith
    linarith
  · intro u hu
    by_contra h_neg
    push Not at h_neg
    have hu_notin : u ∉ U := by
      intro hu_mem
      have := h_neg u hu_mem
      have heq : ‖u - u‖ = 0 := by simp
      linarith
    have hu_sep : ∀ u' ∈ U, ε ≤ ‖u' - u‖ := fun u' hu' =>
      le_of_lt (h_neg u' hu')
    let U' : Finset E := insert u U
    have hU'_card : U'.card = kmax + 1 := by
      change (insert u U).card = kmax + 1
      rw [Finset.card_insert_of_notMem hu_notin, hU_card]
    have hU'_unit : ∀ v ∈ U', ‖v‖ = 1 := by
      intro v hv
      have hv' : v ∈ insert u U := hv
      rcases Finset.mem_insert.mp hv' with rfl | hv'
      · exact hu
      · exact hU_unit v hv'
    have hU'_sep : ∀ v ∈ U', ∀ w ∈ U', v ≠ w → ε ≤ ‖v - w‖ := by
      intro v hv w hw hvw
      have hv' : v = u ∨ v ∈ U := Finset.mem_insert.mp hv
      have hw' : w = u ∨ w ∈ U := Finset.mem_insert.mp hw
      rcases hv' with hv_eq | hv_in
      · rcases hw' with hw_eq | hw_in
        · exact absurd (hv_eq.trans hw_eq.symm) hvw
        · subst hv_eq
          have := hu_sep w hw_in
          rw [norm_sub_rev]; exact this
      · rcases hw' with hw_eq | hw_in
        · subst hw_eq
          exact hu_sep v hv_in
        · exact hU_sep v hv_in w hw_in hvw
    have hP_succ : P (kmax + 1) := ⟨U', hU'_card, hU'_unit, hU'_sep⟩
    have hbd : kmax + 1 ≤ M := hP_bound (kmax + 1) hP_succ
    have := Nat.findGreatest_is_greatest (P := P) (n := M)
              (k := kmax + 1) (by omega) hbd hP_succ
    omega

/-- The dimensional cardinality constant for `exists_ball_net`. -/
noncomputable def ballNetConstant : ℝ :=
  (9 * (Module.finrank ℝ E : ℝ) + 5) ^ Module.finrank ℝ E + 1

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The bounded-ball net cardinality constant is positive. -/
lemma ballNetConstant_pos [Nontrivial E] : 0 < ballNetConstant E := by
  unfold ballNetConstant
  positivity

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Brick 2.** Finite ε-net for the closed ball `B(0, 5/2)` of `E`.

For every `ε ∈ (0, 1]` there is a finite set `P ⊆ B(0, 3)` of
cardinality at most `C_pos(E) · ε^(-n)` such that every point of
`B(0, 5/2)` lies within distance `ε` of some `p ∈ P`. The constant
`C_pos(E)` depends only on the dimension.

Sketch: pick an orthonormal basis `e : OrthonormalBasis (Fin n) ℝ E`,
let `δ' := ε / √n`, and form the grid `P := { ∑_k (δ' · k_i) e_i : k ∈
ℤ^n ∩ [-3/δ', 3/δ']^n }`. By `Fintype.piFinset` over `Finset.Icc`, this
has cardinality `≤ (6/δ' + 1)^n ≤ C_pos · ε^(-n)`. The covering
property follows from `‖m - m'‖ ≤ √n · δ' = ε` via the `Pi.norm_le_iff`
componentwise bound. -/
lemma exists_ball_net
    [Nontrivial E] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ P : Finset E,
      (P.card : ℝ) ≤ ballNetConstant E *
        ε ^ (-(Module.finrank ℝ E : ℝ)) ∧
      (∀ p ∈ P, p ∈ Metric.closedBall (0 : E) 3) ∧
      ∀ m : E, m ∈ Metric.closedBall (0 : E) (5 / 2) →
        ∃ m' ∈ P, ‖m - m'‖ ≤ ε := by
  classical
  set n := Module.finrank ℝ E
  have hn : 0 < n := Module.finrank_pos
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  haveI : NeZero n := ⟨by omega⟩
  set e := stdOrthonormalBasis ℝ E
  change ∃ P : Finset E,
    (P.card : ℝ) ≤ ((9 * (n : ℝ) + 5) ^ n + 1) * ε ^ (-(n : ℝ)) ∧
    (∀ p ∈ P, p ∈ Metric.closedBall (0 : E) 3) ∧
    ∀ m : E, m ∈ Metric.closedBall (0 : E) (5 / 2) →
      ∃ m' ∈ P, ‖m - m'‖ ≤ ε
  set sn : ℝ := Real.sqrt n with hsn_def
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn_pos : 0 < sn := Real.sqrt_pos.mpr hn_pos
  have hsn_sq : sn ^ 2 = n := by rw [hsn_def]; exact Real.sq_sqrt hn_pos.le
  have hsn_ge_one : 1 ≤ sn := by
    rw [hsn_def]
    calc 1 = Real.sqrt 1 := by rw [Real.sqrt_one]
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hn1
  set δ' : ℝ := ε / sn with hδ'_def
  have hδ'_pos : 0 < δ' := div_pos hε hsn_pos
  have hδ'_le : δ' ≤ 1 := by
    rw [hδ'_def]; exact div_le_one_of_le₀ (by linarith) hsn_pos.le
  set Kr : ℝ := (5/2 : ℝ) / δ' + 1 with hKr_def
  set K : ℕ := ⌈Kr⌉₊ with hK_def
  have hKr_pos : 0 < Kr := by rw [hKr_def]; positivity
  have hK_ge : Kr ≤ K := Nat.le_ceil _
  have hK_lt : (K : ℝ) ≤ Kr + 1 := (Nat.ceil_lt_add_one hKr_pos.le).le
  set B : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ) with hB_def
  set CodB : Finset (Fin n → ℤ) := Fintype.piFinset (fun _ : Fin n => B) with hCodB_def
  let φ : (Fin n → ℤ) → E := fun k => ∑ i, ((k i : ℝ) * δ') • e i
  set Pfull : Finset E := CodB.image φ with hPfull_def
  set P : Finset E := Pfull.filter (fun p => p ∈ Metric.closedBall (0 : E) 3) with hP_def
  refine ⟨P, ?_, ?_, ?_⟩
  · have hP_le_full : (P.card : ℝ) ≤ (Pfull.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hPfull_le : (Pfull.card : ℝ) ≤ (CodB.card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    have hB_card : B.card = 2 * K + 1 := by simp [B, Int.card_Icc]; omega
    have hCodB_card : (CodB.card : ℝ) = ((2 * K + 1 : ℕ) : ℝ) ^ n := by
      simp [CodB, Fintype.card_piFinset, hB_card, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
    have h2K1 : ((2 * K + 1 : ℕ) : ℝ) ≤ (9 * (n : ℝ) + 5) / ε := by
      have hsn_le : sn ≤ n := by
        rw [hsn_def]
        calc Real.sqrt n ≤ Real.sqrt (n * n) :=
              Real.sqrt_le_sqrt (by nlinarith [hn1])
          _ = n := by rw [Real.sqrt_mul_self hn_pos.le]
      have hKr_val : Kr = (5/2 : ℝ) / δ' + 1 := hKr_def
      calc ((2 * K + 1 : ℕ) : ℝ)
          = 2 * (K : ℝ) + 1 := by push_cast; ring
        _ ≤ 2 * (Kr + 1) + 1 := by linarith
        _ = 5 / δ' + 5 := by rw [hKr_val]; ring
        _ = 5 * sn / ε + 5 := by rw [hδ'_def]; field_simp
        _ ≤ 5 * n / ε + 5 := by
            have h : 5 * sn / ε ≤ 5 * n / ε := by
              apply div_le_div_of_nonneg_right _ hε.le
              linarith
            linarith
        _ ≤ 5 * n / ε + 5 / ε := by
            have h : (5 : ℝ) ≤ 5 / ε := by rw [le_div_iff₀ hε]; linarith
            linarith
        _ = (5 * (n : ℝ) + 5) / ε := by ring
        _ ≤ (9 * (n : ℝ) + 5) / ε := by
            apply div_le_div_of_nonneg_right _ hε.le
            linarith
    calc (P.card : ℝ) ≤ (Pfull.card : ℝ) := hP_le_full
      _ ≤ (CodB.card : ℝ) := hPfull_le
      _ = ((2 * K + 1 : ℕ) : ℝ) ^ n := hCodB_card
      _ ≤ ((9 * (n : ℝ) + 5) / ε) ^ n := by
          apply pow_le_pow_left₀ (Nat.cast_nonneg _) h2K1
      _ = (9 * (n : ℝ) + 5) ^ n / ε ^ n := by rw [div_pow]
      _ = (9 * (n : ℝ) + 5) ^ n * ε ^ (-(n : ℝ)) := by
          rw [Real.rpow_neg hε.le, Real.rpow_natCast, ← div_eq_mul_inv]
      _ ≤ ((9 * (n : ℝ) + 5) ^ n + 1) * ε ^ (-(n : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hε.le _)
          linarith
  · intro p hp
    rw [hP_def, Finset.mem_filter] at hp
    exact hp.2
  · intro m hm
    simp only [Metric.mem_closedBall, dist_zero_right] at hm
    let cfun : Fin n → ℝ := fun i => inner ℝ (e i) m
    let kfun : Fin n → ℤ := fun i => ⌊cfun i / δ' + 1/2⌋
    let dfun : Fin n → ℝ := fun i => (kfun i : ℝ) * δ'
    have hk_round : ∀ i, |cfun i - dfun i| ≤ δ' / 2 := fun i => by
      have h1 : (kfun i : ℝ) ≤ cfun i / δ' + 1/2 := Int.floor_le _
      have h2 : cfun i / δ' + 1/2 < kfun i + 1 := Int.lt_floor_add_one _
      have hh1 : (kfun i : ℝ) - 1/2 ≤ cfun i / δ' := by linarith
      have hh2 : cfun i / δ' ≤ (kfun i : ℝ) + 1/2 := by linarith
      have key1 : dfun i - δ'/2 ≤ cfun i := by
        have hmul := mul_le_mul_of_nonneg_right hh1 hδ'_pos.le
        rw [div_mul_cancel₀ _ hδ'_pos.ne', sub_mul] at hmul
        simp only [dfun]; linarith
      have key2 : cfun i ≤ dfun i + δ'/2 := by
        have hmul := mul_le_mul_of_nonneg_right hh2 hδ'_pos.le
        rw [div_mul_cancel₀ _ hδ'_pos.ne', add_mul] at hmul
        simp only [dfun]; linarith
      rw [abs_le]; constructor <;> linarith
    set m' : E := φ kfun with hm'_def
    have hm_eq : m = ∑ i, cfun i • e i := by
      conv_lhs => rw [← e.sum_repr m]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [cfun, e.repr_apply_apply]
    have hm'_eq : m' = ∑ i, dfun i • e i := by
      simp only [hm'_def, φ, dfun]
    have hdiff_eq : m - m' = ∑ i, (cfun i - dfun i) • e i := by
      rw [hm_eq, hm'_eq, ← Finset.sum_sub_distrib]
      congr 1; ext i; rw [← sub_smul]
    have hPyth : ∀ a : Fin n → ℝ, ‖∑ i, a i • e i‖ ^ 2 = ∑ i, (a i) ^ 2 := by
      intro a
      rw [← @real_inner_self_eq_norm_sq]
      rw [e.orthonormal.inner_sum a a Finset.univ]
      congr 1; ext i
      simp [sq]
    have hnorm_diff_sq : ‖m - m'‖ ^ 2 = ∑ i, (cfun i - dfun i) ^ 2 := by
      rw [hdiff_eq, hPyth]
    have hbound : ∀ i, (cfun i - dfun i) ^ 2 ≤ (δ' / 2) ^ 2 := fun i => by
      have habs : |cfun i - dfun i| ≤ δ' / 2 := hk_round i
      have : (cfun i - dfun i) ^ 2 = |cfun i - dfun i| ^ 2 := (sq_abs _).symm
      rw [this]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hsum_le : ∑ i, (cfun i - dfun i) ^ 2 ≤ (n : ℝ) * (δ' / 2) ^ 2 := by
      calc ∑ i, (cfun i - dfun i) ^ 2 ≤ ∑ _i : Fin n, (δ' / 2) ^ 2 :=
            Finset.sum_le_sum fun i _ => hbound i
        _ = (n : ℝ) * (δ' / 2) ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hnorm_diff_sq_le : ‖m - m'‖ ^ 2 ≤ (ε / 2) ^ 2 := by
      rw [hnorm_diff_sq]
      calc ∑ i, (cfun i - dfun i) ^ 2 ≤ (n : ℝ) * (δ' / 2) ^ 2 := hsum_le
        _ = (n : ℝ) * δ' ^ 2 / 4 := by ring
        _ = (n : ℝ) * (ε / sn) ^ 2 / 4 := by rw [hδ'_def]
        _ = (n : ℝ) * ε ^ 2 / sn ^ 2 / 4 := by ring
        _ = (n : ℝ) * ε ^ 2 / n / 4 := by rw [hsn_sq]
        _ = ε ^ 2 / 4 := by field_simp
        _ = (ε / 2) ^ 2 := by ring
    have hnorm_diff : ‖m - m'‖ ≤ ε / 2 := by
      have hε2_nn : 0 ≤ ε / 2 := by linarith
      have : ‖m - m'‖ * ‖m - m'‖ ≤ (ε/2) * (ε/2) := by
        have h1 : ‖m - m'‖ * ‖m - m'‖ = ‖m - m'‖ ^ 2 := by ring
        have h2 : (ε/2) * (ε/2) = (ε/2) ^ 2 := by ring
        rw [h1, h2]; exact hnorm_diff_sq_le
      exact nonneg_le_nonneg_of_sq_le_sq hε2_nn this
    have hm'_norm : ‖m'‖ ≤ 3 := by
      calc ‖m'‖ = ‖m - (m - m')‖ := by congr 1; abel
        _ ≤ ‖m‖ + ‖m - m'‖ := norm_sub_le _ _
        _ ≤ 5/2 + ε/2 := by linarith
        _ ≤ 3 := by linarith
    have hk_in_B : ∀ i, kfun i ∈ B := fun i => by
      rw [hB_def, Finset.mem_Icc]
      have h_inner_le : |cfun i| ≤ ‖m‖ := by
        have : |cfun i| ≤ ‖e i‖ * ‖m‖ := abs_real_inner_le_norm _ _
        rw [e.norm_eq_one, one_mul] at this
        exact this
      have h1 : (kfun i : ℝ) ≤ cfun i / δ' + 1/2 := Int.floor_le _
      have h2 : cfun i / δ' + 1/2 < kfun i + 1 := Int.lt_floor_add_one _
      have h3 : (kfun i : ℝ) - 1/2 ≤ cfun i / δ' := by linarith
      have h4 : cfun i / δ' ≤ (kfun i : ℝ) + 1/2 := by linarith
      have h_c_bd : |cfun i / δ'| ≤ (5/2)/δ' := by
        rw [abs_div, abs_of_pos hδ'_pos]
        apply div_le_div_of_nonneg_right _ hδ'_pos.le
        linarith [h_inner_le, hm]
      have h_kfun_bd : |(kfun i : ℝ)| ≤ (5/2)/δ' + 1/2 := by
        rcases abs_le.mp h_c_bd with ⟨hc1, hc2⟩
        rw [abs_le]; constructor <;> linarith
      have h_kfun_le_K : |(kfun i : ℝ)| ≤ K := by
        calc |(kfun i : ℝ)| ≤ (5/2)/δ' + 1/2 := h_kfun_bd
          _ = Kr - 1/2 := by rw [hKr_def]; ring
          _ ≤ K - 1/2 := by linarith
          _ ≤ K := by linarith
      rcases abs_le.mp h_kfun_le_K with ⟨hh1, hh2⟩
      constructor
      · exact_mod_cast hh1
      · exact_mod_cast hh2
    have hk_in_CodB : kfun ∈ CodB := by
      rw [hCodB_def]
      exact Fintype.mem_piFinset.mpr hk_in_B
    have hm'_in_Pfull : m' ∈ Pfull := by
      rw [hPfull_def, Finset.mem_image]
      exact ⟨kfun, hk_in_CodB, rfl⟩
    have hm'_in_P : m' ∈ P := by
      rw [hP_def, Finset.mem_filter]
      exact ⟨hm'_in_Pfull, by
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact hm'_norm⟩
    refine ⟨m', hm'_in_P, ?_⟩
    linarith [hnorm_diff]

end EuclideanNet

end Kakeya
