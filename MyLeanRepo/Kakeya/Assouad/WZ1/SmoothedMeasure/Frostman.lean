import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedMeasure.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Thickening

/-!
# All-scale Frostman bound for smoothed measures

Given a discrete `(δ,s,C)`-Frostman set with `0 < s ≤ 2`, smoothing with
radius `ρ = δ/2` yields `ν(B(x,r)) ≤ max(C·2^s, ρ^{-s}) · r^s`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

/-- ENNReal division identity: (ofReal a)⁻¹ * ofReal b = ofReal (b/a) for a > 0. -/
private lemma ofReal_div {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    (ENNReal.ofReal a)⁻¹ * ENNReal.ofReal b = ENNReal.ofReal (b / a) := by
  have ha' : 0 ≤ a := by linarith
  have h1 : ENNReal.ofReal (b / a) * ENNReal.ofReal a = ENNReal.ofReal b := by
    have h2 : ENNReal.ofReal ((b / a) * a) = ENNReal.ofReal (b / a) * ENNReal.ofReal a :=
      ENNReal.ofReal_mul (show 0 ≤ b / a by positivity)
    have h3 : (b / a) * a = b := by field_simp [ha.ne'] <;> ring
    rw [h3] at h2
    exact h2.symm
  have h4 : ENNReal.ofReal a ≠ 0 := by positivity
  have h5 : ENNReal.ofReal a ≠ ⊤ := by simp
  have h_comm : ENNReal.ofReal (b / a) * ENNReal.ofReal a = ENNReal.ofReal a * ENNReal.ofReal (b / a) := mul_comm _ _
  have h6 : (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal (b / a) * ENNReal.ofReal a) = ENNReal.ofReal (b / a) := by
    rw [h_comm, ← mul_assoc, ENNReal.inv_mul_cancel h4 h5, one_mul]
  rw [h1] at h6
  exact h6

/-- Volume of 2D ball as ofReal(π * r²). -/
private lemma volume_ball_fin_two' {x : Point2} {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball x r) = ENNReal.ofReal (Real.pi * r^2) := by
  rw [EuclideanSpace.volume_ball_fin_two x r]
  have h1 : ENNReal.ofReal r ^ 2 = ENNReal.ofReal (r^2) := by
    have h11 : ENNReal.ofReal r ^ 2 = ENNReal.ofReal r * ENNReal.ofReal r := by rw [pow_two]
    have h12 : ENNReal.ofReal (r * r) = ENNReal.ofReal r * ENNReal.ofReal r :=
      @ENNReal.ofReal_mul r r hr
    have h13 : ENNReal.ofReal (r * r) = ENNReal.ofReal (r^2) := by
      congr 1 <;> ring
    rw [h11, ←h12, h13]
  rw [h1]
  have h2 : ENNReal.ofReal (r^2) * ENNReal.ofReal Real.pi = ENNReal.ofReal (r^2 * Real.pi) := by
    have h21 : ENNReal.ofReal ((r^2) * Real.pi) = ENNReal.ofReal (r^2) * ENNReal.ofReal Real.pi :=
      @ENNReal.ofReal_mul (r^2) Real.pi (show 0 ≤ r^2 by positivity)
    exact h21.symm
  rw [h2]
  have h3 : ENNReal.ofReal (r^2 * Real.pi) = ENNReal.ofReal (Real.pi * r^2) := by
    have h4 : r^2 * Real.pi = Real.pi * r^2 := by ring
    rw [h4]
  exact h3

/-- If balls B(z,r) and B(0,ρ) are disjoint, σ(B(z,r)) = 0. -/
private lemma ballUniformMeasure_ball_zero
    {ρ : ℝ} (hρ : 0 < ρ) {z : Point2} {r : ℝ} (hr : 0 < r)
    (h_disj : r + ρ ≤ dist z 0) :
    (ballUniformMeasure ρ hρ : Measure Point2) (Metric.ball z r) = 0 := by
  set Vρ := volume (Metric.ball (0 : Point2) ρ) with hVρ
  have hs : MeasurableSet (Metric.ball z r) := Metric.isOpen_ball.measurableSet
  have h_empty : (Metric.ball z r ∩ Metric.ball (0 : Point2) ρ) = ∅ := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro h
    have h1 : dist y z < r := by simpa [Metric.mem_ball] using h.1
    have h1' : dist z y < r := by rwa [dist_comm] at h1
    have h2 : dist y (0 : Point2) < ρ := by simpa [Metric.mem_ball] using h.2
    have h3 : dist z 0 ≤ dist z y + dist y 0 := dist_triangle z y 0
    have h4 : dist z 0 < r + ρ := by linarith [dist_comm z y]
    linarith
  have h_def : (ballUniformMeasure ρ hρ : Measure Point2) (Metric.ball z r) =
      Vρ⁻¹ * volume (Metric.ball z r ∩ Metric.ball (0 : Point2) ρ) := by
    have h_unfold : (ballUniformMeasure ρ hρ : Measure Point2) =
        Vρ⁻¹ • volume.restrict (Metric.ball (0 : Point2) ρ) := by rfl
    rw [h_unfold, MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply (ht := hs)]
    <;> rfl
  rw [h_def, h_empty]
  <;> simp

/-- σ(B(x,r)) ≤ r²/ρ² in ENNReal. -/
private lemma ballUniformMeasure_area_bound
    {ρ : ℝ} (hρ : 0 < ρ) {x : Point2} {r : ℝ} (hr : 0 < r) :
    (ballUniformMeasure ρ hρ : Measure Point2) (Metric.ball x r) ≤
      ENNReal.ofReal (r^2 / ρ^2) := by
  set Vρ := volume (Metric.ball (0 : Point2) ρ) with hVρ
  have hVρ_pos : 0 < Vρ := by rw [hVρ, volume_ball_fin_two' (by linarith)] <;> positivity
  have hVρ_ne_zero : Vρ ≠ 0 := hVρ_pos.ne'
  have hVρ_ne_top : Vρ ≠ ⊤ := by
    rw [hVρ, volume_ball_fin_two' (by linarith)] <;> simp [ENNReal.ofReal_ne_top]
  have hs : MeasurableSet (Metric.ball x r) := Metric.isOpen_ball.measurableSet
  have h_def : (ballUniformMeasure ρ hρ : Measure Point2) =
      Vρ⁻¹ • volume.restrict (Metric.ball (0 : Point2) ρ) := by rfl
  have h_formula : (ballUniformMeasure ρ hρ : Measure Point2) (Metric.ball x r) =
      Vρ⁻¹ * volume (Metric.ball x r ∩ Metric.ball (0 : Point2) ρ) := by
    rw [h_def, MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply (ht := hs)] <;> rfl
  rw [h_formula]
  have h_volρ : Vρ = ENNReal.ofReal (Real.pi * ρ^2) := by
    rw [hVρ, volume_ball_fin_two' (by linarith)]
  have h_volr : volume (Metric.ball x r) = ENNReal.ofReal (Real.pi * r^2) :=
    volume_ball_fin_two' (by linarith)
  have h_sub : (Metric.ball x r ∩ Metric.ball (0 : Point2) ρ) ⊆ Metric.ball x r := by
    intro y hy; exact hy.1
  have h_mono : volume (Metric.ball x r ∩ Metric.ball (0 : Point2) ρ) ≤ volume (Metric.ball x r) := by
    exact @MeasureTheory.measure_mono Point2 (Measure Point2) _ _ volume (Metric.ball x r ∩ Metric.ball (0 : Point2) ρ) (Metric.ball x r) h_sub
  calc Vρ⁻¹ * volume (Metric.ball x r ∩ Metric.ball (0 : Point2) ρ)
      ≤ Vρ⁻¹ * volume (Metric.ball x r) := by gcongr
    _ = (ENNReal.ofReal (Real.pi * ρ^2))⁻¹ * ENNReal.ofReal (Real.pi * r^2) := by rw [h_volρ, h_volr]
    _ = ENNReal.ofReal ((Real.pi * r^2) / (Real.pi * ρ^2)) := ofReal_div (by positivity) (by positivity)
    _ = ENNReal.ofReal (r^2 / ρ^2) := by
      apply congr_arg ENNReal.ofReal
      field_simp [hρ.ne'] <;> ring

/--
All-scale Frostman bound for the smoothed measure.

Given a discrete `(δ,s,C)`-Frostman set with `0 < s ≤ 2`, smoothing with
radius `ρ = δ/2` yields `ν(B(x,r)) ≤ max(C·2^s, ρ^{-s}) · r^s`.
-/
lemma smoothMeasure_frostman
    {A : DiscreteSet 2} {δ C s : ℝ} (hne : A.Nonempty)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C) (hs_pos : 0 < s) (hs2 : s ≤ 2)
    (hFrost : A.IsFrostman δ s (ENNReal.ofReal C))
    {x : Point2} {r : ℝ} (hr : 0 < r) :
    (smoothMeasure A hne (δ / 2) (by positivity) : Measure Point2) (Metric.ball x r) ≤
      ENNReal.ofReal (max (C * (2:ℝ)^s) ((δ / 2)^(-s)) * r^s) := by
  let ρ := δ / 2
  have hρ : 0 < ρ := by positivity
  let σ := ballUniformMeasure ρ hρ
  let ν := smoothMeasure A hne ρ hρ
  set C' : ℝ := max (C * (2:ℝ)^s) (ρ^(-s)) with hC'_def
  have hC'_nonneg : 0 ≤ C' := by positivity
  have h_pos : 0 ≤ C' * r^s := by positivity
  have h_ball_meas : MeasurableSet (Metric.ball x r) := Metric.isOpen_ball.measurableSet
  have h_main : (ν : Measure Point2) (Metric.ball x r) =
      (A.card : ENNReal)⁻¹ * ∑ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r) := by
    rw [smoothMeasure_apply h_ball_meas]
    apply congr_arg (fun y => (A.card : ENNReal)⁻¹ * y)
    apply Finset.sum_congr rfl
    intro a _
    have h_set : {y : Point2 | a + y ∈ Metric.ball x r} = Metric.ball (x - a) r := by
      ext y; simp [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg] <;> abel
    rw [h_set]
  rw [h_main]
  by_cases h_large : ρ ≤ r
  · -- r ≥ ρ
    have hρeq : ρ = δ / 2 := by rfl
    have hδr : δ ≤ r + ρ := by rw [hρeq]; linarith
    by_cases h_small : r + ρ ≤ 1
    · let S := A.filter (fun a : Point2 => dist x a < r + ρ)
      have h1 : ∑ a ∈ S, (σ : Measure Point2) (Metric.ball (x - a) r) = ∑ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r) := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro a ha hna
        have h_inA : a ∈ A := ha
        have h_not : ¬(dist x a < r + ρ) := by
          simpa [S, Finset.mem_filter, h_inA] using hna
        have h' : r + ρ ≤ dist x a := by linarith
        have h_eq : dist (x - a) 0 = dist x a := by
          simp [dist_eq_norm, sub_eq_add_neg] <;> abel
        have h_dist : r + ρ ≤ dist (x - a) 0 := by
          rw [h_eq]; exact h'
        exact ballUniformMeasure_ball_zero hρ hr h_dist
      rw [←h1]
      have h2 : ∑ a ∈ S, (σ : Measure Point2) (Metric.ball (x - a) r) ≤ (S.card : ENNReal) := by
        have h3 : ∀ a ∈ S, (σ : Measure Point2) (Metric.ball (x - a) r) ≤ 1 := by
          intro a _
          have h4 : (σ : Measure Point2) (Metric.ball (x - a) r) ≤ (σ : Measure Point2) Set.univ :=
            @MeasureTheory.measure_mono Point2 (Measure Point2) _ _ (σ : Measure Point2) (Metric.ball (x - a) r) Set.univ (Set.subset_univ _)
          simpa using h4
        have h_sum1 : ∑ a ∈ S, (σ : Measure Point2) (Metric.ball (x - a) r) ≤ ∑ a ∈ S, (1 : ENNReal) :=
          Finset.sum_le_sum (fun i _ => h3 i ‹_›)
        have h_sum2 : ∑ a ∈ S, (1 : ENNReal) = (S.card : ENNReal) := by simp
        rw [h_sum2] at h_sum1
        exact h_sum1
      have hS_sub : S ⊆ A.filter (fun a => dist x a ≤ r + ρ) := by
        intro a ha; have h4 : a ∈ A ∧ dist x a < r + ρ := by simpa [S, Finset.mem_filter] using ha
        simp only [Finset.mem_filter] at *; exact ⟨h4.1, by linarith⟩
      have h4 : (S.card : ENNReal) ≤ A.ballCount x (r + ρ) := by
        have h5 : S.card ≤ (A.filter (fun a => dist x a ≤ r + ρ)).card := Finset.card_le_card hS_sub
        have h_filter_eq : A.filter (fun y : Point2 => dist y x ≤ r + ρ) = A.filter (fun a : Point2 => dist x a ≤ r + ρ) := by
          apply Finset.ext; intro y; simp [dist_comm]
        have h6 : A.ballCount x (r + ρ) = ((A.filter (fun a => dist x a ≤ r + ρ)).card : ENNReal) := by
          simp [DiscreteSet.ballCount, h_filter_eq] <;> rfl
        rw [h6]
        exact_mod_cast h5
      have h4' : ∑ a ∈ S, (σ : Measure Point2) (Metric.ball (x - a) r) ≤ A.ballCount x (r + ρ) :=
        h2.trans h4
      have h5 : (A.card : ENNReal)⁻¹ * ∑ a ∈ S, (σ : Measure Point2) (Metric.ball (x - a) r) ≤ (A.card : ENNReal)⁻¹ * A.ballCount x (r + ρ) := by
        exact mul_le_mul_of_nonneg_left h4' (by positivity)
      have h_frost2 : A.ballCount x (r + ρ) ≤ ENNReal.ofReal C * Kakeya.realRpowENN (r + ρ) s * A.enncard :=
        hFrost x (r + ρ) hδr h_small
      have h_enncard : A.enncard = (A.card : ENNReal) := by simp [DiscreteSet.enncard]
      have h6 : (A.card : ENNReal)⁻¹ * A.ballCount x (r + ρ) ≤ ENNReal.ofReal C * Kakeya.realRpowENN (r + ρ) s := by
        rw [h_enncard] at h_frost2
        set b := ENNReal.ofReal C * Kakeya.realRpowENN (r + ρ) s with hb
        have hpos : (A.card : ENNReal) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
        have htop : (A.card : ENNReal) ≠ ⊤ := by simp
        have h7 : (A.card : ENNReal)⁻¹ * A.ballCount x (r + ρ) ≤ (A.card : ENNReal)⁻¹ * (b * (A.card : ENNReal)) := by gcongr
        have h8 : (A.card : ENNReal)⁻¹ * (b * (A.card : ENNReal)) = b := by
          have h_comm : b * (A.card : ENNReal) = (A.card : ENNReal) * b := by ring
          rw [h_comm, ← mul_assoc, ENNReal.inv_mul_cancel hpos htop, one_mul]
        rw [h8] at h7
        exact h7
      have h_nonneg : 0 ≤ r + ρ := by linarith
      have h_rpow : Kakeya.realRpowENN (r + ρ) s = ENNReal.ofReal (Real.rpow (r + ρ) s) := by
        unfold Kakeya.realRpowENN <;> rfl
      have h_rpow2 : Real.rpow (r + ρ) s = (r + ρ)^s := by rfl
      have h_rpow3 : Kakeya.realRpowENN (r + ρ) s = ENNReal.ofReal ((r + ρ)^s) := by
        rw [h_rpow, h_rpow2]
      rw [h_rpow3] at h6
      have h_ineq : (r + ρ)^s ≤ (2 * r)^s := by
        have h9 : 0 ≤ r + ρ := by linarith
        have h10 : r + ρ ≤ 2 * r := by linarith
        exact Real.rpow_le_rpow h9 h10 hs_pos.le
      have h11 : ENNReal.ofReal C * ENNReal.ofReal ((r + ρ)^s) ≤ ENNReal.ofReal (C * (2 * r)^s) := by
        have h12 : ENNReal.ofReal C * ENNReal.ofReal ((r + ρ)^s) = ENNReal.ofReal (C * (r + ρ)^s) := by
          exact (@ENNReal.ofReal_mul C ((r + ρ)^s) hC).symm
        rw [h12]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h_ineq hC)
      have h13 : C * (2 * r)^s = C * (2:ℝ)^s * r^s := by
        have h14 : (2 * r)^s = (2:ℝ)^s * r^s := by
          rw [Real.mul_rpow (by norm_num) (by linarith)] <;> ring
        rw [h14] <;> ring
      have h15 : C * (2:ℝ)^s ≤ C' := by dsimp only [C']; exact le_max_left _ _
      have h16 : ENNReal.ofReal (C * (2 * r)^s) ≤ ENNReal.ofReal (C' * r^s) := by
        rw [h13]; exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h15 (by positivity))
      have h17 : (A.card : ENNReal)⁻¹ * ∑ a ∈ S, (σ : Measure Point2) (Metric.ball (x - a) r) ≤ ENNReal.ofReal (C' * r^s) :=
        h5.trans (h6.trans (h11.trans h16))
      exact h17
    · -- r + ρ > 1
      have h_goal : (A.card : ENNReal)⁻¹ * ∑ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r) ≤ 1 := by
        have h_eq : (A.card : ENNReal)⁻¹ * ∑ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r) = (ν : Measure Point2) (Metric.ball x r) := by rw [←h_main]
        rw [h_eq]
        have h : (ν : Measure Point2) (Metric.ball x r) ≤ (ν : Measure Point2) Set.univ :=
          @MeasureTheory.measure_mono Point2 (Measure Point2) _ _ (ν : Measure Point2) (Metric.ball x r) Set.univ (Set.subset_univ _)
        simpa using h
      have h12 : 1 ≤ C' * r^s := by
        have h13 : C' ≥ ρ^(-s) := by dsimp only [C']; exact le_max_right _ _
        have h14 : 0 < ρ := hρ
        have h15 : 0 ≤ r := by linarith
        have h16 : ρ ≤ r := h_large
        have h17 : 1 ≤ r / ρ := by
          have h171 : ρ ≤ r := h_large
          have h172 : 0 < ρ := h14
          calc
            1 = ρ / ρ := by field_simp [h172.ne']
            _ ≤ r / ρ := by gcongr
        have h18 : 1 ≤ (r / ρ)^s := Real.one_le_rpow h17 hs_pos.le
        have h19 : (r / ρ)^s = r^s / ρ^s := by
          rw [Real.div_rpow (by linarith) (by linarith)] <;> rfl
        have h20 : r^s / ρ^s = ρ^(-s) * r^s := by
          have h21 : ρ^(-s) = 1 / ρ^s := by rw [Real.rpow_neg (by linarith)] <;> field_simp
          rw [h21] <;> ring
        have h22 : 1 ≤ ρ^(-s) * r^s := by rw [←h20, ←h19]; exact h18
        exact h22.trans (mul_le_mul_of_nonneg_right h13 (by positivity))
      have h14 : (1 : ENNReal) ≤ ENNReal.ofReal (C' * r^s) := by simpa [ENNReal.ofReal_le_ofReal_iff] using h12
      exact h_goal.trans h14
  · -- r < ρ
    have h_small : r < ρ := by linarith
    have h_bound : ∀ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r) ≤ ENNReal.ofReal (r^2 / ρ^2) := by
      intro a _; exact ballUniformMeasure_area_bound hρ hr
    have h_sum : ∑ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r) ≤ (A.card : ENNReal) * ENNReal.ofReal (r^2 / ρ^2) := by
      have h : ∑ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r) ≤ ∑ a ∈ A, ENNReal.ofReal (r^2 / ρ^2) := Finset.sum_le_sum h_bound
      have h_eq : ∑ a ∈ A, ENNReal.ofReal (r^2 / ρ^2) = (A.card : ENNReal) * ENNReal.ofReal (r^2 / ρ^2) := by
        simp [Finset.sum_const] <;> ring
      rw [h_eq] at h
      exact h
    have hpos : (A.card : ENNReal) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
    have htop : (A.card : ENNReal) ≠ ⊤ := by simp
    have h6 : (A.card : ENNReal)⁻¹ * ∑ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r) ≤ ENNReal.ofReal (r^2 / ρ^2) := by
      calc (A.card : ENNReal)⁻¹ * ∑ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r)
          ≤ (A.card : ENNReal)⁻¹ * ((A.card : ENNReal) * ENNReal.ofReal (r^2 / ρ^2)) := by gcongr
        _ = ENNReal.ofReal (r^2 / ρ^2) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hpos htop, one_mul]
    have h7 : r^2 / ρ^2 ≤ C' * r^s := by
      dsimp only [C', ρ]
      have h8 : 0 < r / ρ := by positivity
      have h9 : r / ρ < 1 := by apply (div_lt_one hρ).mpr; linarith
      have h10 : (r / ρ)^(2 : ℝ) ≤ (r / ρ)^s := Real.rpow_le_rpow_of_exponent_ge h8 h9.le hs2
      have h11 : (r / ρ)^(2 : ℝ) = r^2 / ρ^2 := by
        simp [Real.rpow_two] <;> field_simp [hρ.ne'] <;> ring
      have h12 : (r / ρ)^s = r^s / ρ^s := by
        rw [Real.div_rpow (by linarith) (by linarith)] <;> rfl
      rw [h11, h12] at h10
      have h13 : ρ^(-s) ≤ C' := by dsimp only [C']; exact le_max_right _ _
      have h14 : r^s / ρ^s = ρ^(-s) * r^s := by
        have h15 : ρ^(-s) = 1 / ρ^s := by rw [Real.rpow_neg (by linarith)] <;> field_simp
        rw [h15] <;> ring
      rw [h14] at h10
      exact h10.trans (mul_le_mul_of_nonneg_right h13 (by positivity))
    have h8 : ENNReal.ofReal (r^2 / ρ^2) ≤ ENNReal.ofReal (C' * r^s) := ENNReal.ofReal_le_ofReal h7
    exact h6.trans h8

end Kakeya.Assouad
