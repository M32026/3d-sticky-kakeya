module

/-
  ConcentratedContradiction.lean

  Core contradiction lemma for the concentrated case.

  Given a family of tubes through y, direction-separated by r/ξ,
  each with mass ≥ r^(σ+4η) in the annulus A(y,ξ,2ξ),
  and enough tubes, derive a contradiction with Frostman's bound.

  Whiteprint node: concentrated-case
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.BoundedOverlap

@[expose] public section

open MeasureTheory Metric Set Finset

noncomputable section

namespace RadialBootstrapping

/-- Core contradiction for concentrated case. -/
lemma concentrated_core_contradiction
    {ν : Measure Point} [IsProbabilityMeasure ν]
    (r η σ ξ C m : ℝ)
    (hr : 0 < r) (hη : 0 < η) (hσ : 0 ≤ σ)
    (hξ : 0 < ξ) (hC : 0 ≤ C) (hm : 0 < m)
    (y : Point)
    (T_y : Finset Line2)
    -- All tubes pass through y
    (h_through_y : ∀ L ∈ T_y, y ∈ tube r L)
    -- Direction separation
    (h_sep : ∀ L1 ∈ T_y, ∀ L2 ∈ T_y, L1 ≠ L2 → lineDirDist L1 L2 ≥ r / ξ)
    -- Smallness condition for bounded overlap
    (h_small : 2 * r / ξ ≤ 1)
    -- Each tube has mass m in annulus
    (h_mass : ∀ L ∈ T_y, ν (Metric.ball y (2 * ξ) \ Metric.ball y ξ ∩ tube r L) ≥ ENNReal.ofReal m)
    -- Frostman bound
    (hFrostman : ν (Metric.ball y (2 * ξ)) ≤ ENNReal.ofReal (C * (2 * ξ)))
    -- Tube count lower bound: |T_y| * m > 26 * C * ξ
    (h_count : (T_y.card : ℝ) * m > 26 * C * ξ) :
    False := by
  classical
  let A : Line2 → Set Point := fun L =>
    Metric.ball y (2 * ξ) \ Metric.ball y ξ ∩ tube r L

  have hA_meas : ∀ L ∈ T_y, MeasurableSet (A L) := by
    intro L _
    exact (measurableSet_ball).diff (measurableSet_ball) |>.inter (Metric.isOpen_thickening.measurableSet)

  have hA_sub_ball : ∀ L ∈ T_y, A L ⊆ Metric.ball y (2 * ξ) := by
    intro L _
    have h : A L = (Metric.ball y (2 * ξ) \ Metric.ball y ξ) ∩ tube r L := by rfl
    rw [h]
    exact Set.inter_subset_left.trans Set.diff_subset

  -- Bounded overlap: for any z with dist(y,z) ≥ ξ, at most 13 tubes contain z in tube(r, L)
  have h_overlap : ∀ (z : Point), ξ ≤ dist y z →
      (T_y.filter (fun L => z ∈ tube r L)).card ≤ 13 := by
    intro z hz
    let r' := r / 2
    have hr' : 0 < r' := by
      dsimp only [r']
      exact half_pos hr
    have h_sep' : ∀ L1 ∈ T_y, ∀ L2 ∈ T_y, L1 ≠ L2 → lineDirDist L1 L2 ≥ r' / ξ := by
      intro L1 hL1 L2 hL2 hne
      have h : lineDirDist L1 L2 ≥ r / ξ := h_sep L1 hL1 L2 hL2 hne
      have h2 : r' / ξ = r / (2 * ξ) := by
        dsimp only [r']
        <;> ring
      rw [h2]
      have h3 : r / ξ ≥ r / (2 * ξ) := by
        apply div_le_div_of_nonneg_left hr.le
        <;> linarith
      exact le_trans h3 h
    have h_small' : 4 * r' / ξ ≤ 1 := by
      dsimp only [r']
      have h4 : 4 * (r / 2) / ξ = 2 * r / ξ := by ring
      rw [h4]
      exact h_small
    have h_eq_tube : ∀ (L : Line2), tube (2 * r') L = tube r L := by
      intro L
      have h4 : 2 * r' = r := by simp [r'] <;> ring
      rw [h4]
    have h_through_y' : ∀ L ∈ T_y, y ∈ tube (2 * r') L := by
      intro L hL
      rw [h_eq_tube L]
      exact h_through_y L hL
    let S := T_y.filter (fun L => z ∈ tube (2 * r') L ∧ y ∈ tube (2 * r') L)
    have hS_eq : S = T_y.filter (fun L => z ∈ tube r L) := by
      ext L
      simp only [S, Finset.mem_filter, h_eq_tube L]
      <;> constructor <;> intro h <;> aesop <;> tauto
    have h_main : S.card ≤ 13 :=
      bounded_overlap_pair (hr := hr') (hξ := hξ) (h_sep := h_sep')
        (x := z) (y := y) (hxy := by rwa [dist_comm]) (h_small := h_small')
    rw [hS_eq] at h_main
    exact h_main

  -- Each z in annulus is in at most 13 sets A L
  have h_pointwise_overlap : ∀ z ∈ Metric.ball y (2 * ξ) \ Metric.ball y ξ,
      (T_y.filter (fun L => z ∈ A L)).card ≤ 13 := by
    intro z hz
    have hz_ann : ξ ≤ dist y z := by
      have h1 : z ∉ Metric.ball y ξ := hz.2
      have h2 : ¬ dist y z < ξ := by
        intro h5
        have h6 : dist z y < ξ := by
          rw [dist_comm] at h5
          exact h5
        exact h1 (by simpa [Metric.mem_ball] using h6)
      by_contra h3
      have h4 : dist y z < ξ := by linarith
      exact h2 h4
    have h2 : ∀ L ∈ T_y, z ∈ A L → z ∈ tube r L := by
      intro L _ hzA
      exact hzA.2
    have h4 : (T_y.filter (fun L => z ∈ A L)) ⊆ T_y.filter (fun L => z ∈ tube r L) := by
      intro L hL
      have h5 : L ∈ T_y := (Finset.mem_filter.mp hL).1
      exact Finset.mem_filter.mpr ⟨h5, h2 L h5 (Finset.mem_filter.mp hL).2⟩
    have h5 := h_overlap z hz_ann
    exact le_trans (Finset.card_le_card h4) h5

  -- Sum of measures ≤ 13 * measure of ball, using pointwise bounded overlap
  have h_sum_le : ∑ L ∈ T_y, ν (A L) ≤ 13 * ν (Metric.ball y (2 * ξ)) := by
    have h_meas : ∀ L ∈ T_y, MeasurableSet (A L) := hA_meas
    let f : Point → ENNReal := fun z => ∑ L ∈ T_y, Set.indicator (A L) (fun _ => (1 : ENNReal)) z
    have h1 : ∑ L ∈ T_y, ν (A L) = ∫⁻ z, f z ∂ν := by
      have h_eq : ∀ L ∈ T_y, ν (A L) = ∫⁻ z, Set.indicator (A L) (fun _ => (1 : ENNReal)) z ∂ν := by
        intro L hL
        rw [MeasureTheory.lintegral_indicator (h_meas L hL)]
        <;> simp
      have h_ind_meas : ∀ L ∈ T_y, Measurable (Set.indicator (A L) (fun _ => (1 : ENNReal))) := by
        intro L hL
        exact (measurable_const : Measurable (fun _ : Point => (1 : ENNReal))).indicator (h_meas L hL)
      calc
        ∑ L ∈ T_y, ν (A L) = ∑ L ∈ T_y, ∫⁻ z, Set.indicator (A L) (fun _ => (1 : ENNReal)) z ∂ν := by
          apply Finset.sum_congr rfl; intro L hL; exact h_eq L hL
        _ = ∫⁻ z, ∑ L ∈ T_y, Set.indicator (A L) (fun _ => (1 : ENNReal)) z ∂ν := by
          rw [MeasureTheory.lintegral_finsetSum T_y h_ind_meas]
        _ = ∫⁻ z, f z ∂ν := by rfl
    rw [h1]
    have h_bound : ∀ z, f z ≤ 13 * Set.indicator (Metric.ball y (2 * ξ)) (fun _ => (1 : ENNReal)) z := by
      intro z
      by_cases hz : z ∈ Metric.ball y (2 * ξ)
      · -- z in ball
        by_cases hz2 : z ∈ Metric.ball y ξ
        · -- z in inner ball: A L doesn't contain z (since A L excludes inner ball)
          have h3 : ∀ L ∈ T_y, Set.indicator (A L) (fun _ => (1 : ENNReal)) z = 0 := by
            intro L _
            have h4 : z ∉ A L := by
              intro h5
              have h6 : z ∉ Metric.ball y ξ := h5.1.2
              exact h6 hz2
            simp [Set.indicator_apply, h4]
          have h5 : f z = 0 := by
            dsimp only [f]
            rw [Finset.sum_eq_zero]
            exact h3
          rw [h5]
          <;> simp [hz] <;> positivity
        · -- z in annulus
          have hz' : z ∈ Metric.ball y (2 * ξ) \ Metric.ball y ξ := ⟨hz, hz2⟩
          have h4 : (T_y.filter (fun L => z ∈ A L)).card ≤ 13 := h_pointwise_overlap z hz'
          have h5 : f z = ↑((T_y.filter (fun L => z ∈ A L)).card) := by
            dsimp only [f]
            have h_ind : ∑ L ∈ T_y, Set.indicator (A L) (fun _ => (1 : ENNReal)) z =
                ∑ L ∈ T_y, (if z ∈ A L then (1 : ENNReal) else 0) := by
              apply Finset.sum_congr rfl
              intro L _
              simp [Set.indicator_apply] <;> split_ifs <;> simp
            rw [h_ind]
            rw [Finset.sum_ite]
            <;> simp <;> norm_cast
          rw [h5]
          simp [hz]
          <;> exact_mod_cast h4
      · -- z outside ball: indicator is 0
        have h3 : Set.indicator (Metric.ball y (2 * ξ)) (fun _ => (1 : ENNReal)) z = 0 := by
          simp [hz]
        have h4 : f z = 0 := by
          simp [f, hz, Set.indicator_apply, hA_sub_ball]
          <;> tauto
        rw [h3, h4] <;> simp
    have h6 : ∫⁻ z, f z ∂ν ≤ ∫⁻ z, 13 * Set.indicator (Metric.ball y (2 * ξ)) (fun _ => (1 : ENNReal)) z ∂ν :=
      lintegral_mono h_bound
    have h7 : ∫⁻ z, 13 * Set.indicator (Metric.ball y (2 * ξ)) (fun _ => (1 : ENNReal)) z ∂ν =
        13 * ν (Metric.ball y (2 * ξ)) := by
      have h_int : ∫⁻ z, Set.indicator (Metric.ball y (2 * ξ)) (fun _ => (1 : ENNReal)) z ∂ν =
          ν (Metric.ball y (2 * ξ)) := by
        rw [MeasureTheory.lintegral_indicator measurableSet_ball]
        <;> simp
      have h_meas_ind : Measurable (Set.indicator (Metric.ball y (2 * ξ)) (fun _ => (1 : ENNReal))) := by
        apply Measurable.indicator (by fun_prop) measurableSet_ball
      have h_mul : ∫⁻ z, 13 * Set.indicator (Metric.ball y (2 * ξ)) (fun _ => (1 : ENNReal)) z ∂ν =
          13 * ∫⁻ z, Set.indicator (Metric.ball y (2 * ξ)) (fun _ => (1 : ENNReal)) z ∂ν :=
        MeasureTheory.lintegral_const_mul (13 : ENNReal) h_meas_ind
      rw [h_mul, h_int] <;> ring
    calc
      ∫⁻ z, f z ∂ν ≤ ∫⁻ z, 13 * Set.indicator (Metric.ball y (2 * ξ)) (fun _ => (1 : ENNReal)) z ∂ν := h6
      _ = 13 * ν (Metric.ball y (2 * ξ)) := h7

  -- Sum of measures ≥ |T_y| * m
  have h_sum_ge : ∑ L ∈ T_y, ν (A L) ≥ (T_y.card : ENNReal) * ENNReal.ofReal m := by
    have h : ∀ L ∈ T_y, ν (A L) ≥ ENNReal.ofReal m := h_mass
    calc
      ∑ L ∈ T_y, ν (A L) ≥ ∑ L ∈ T_y, ENNReal.ofReal m := Finset.sum_le_sum h
      _ = (T_y.card : ENNReal) * ENNReal.ofReal m := by
        simp [Finset.sum_const] <;> ring

  -- Combine
  have h_final : (T_y.card : ENNReal) * ENNReal.ofReal m ≤ 13 * ν (Metric.ball y (2 * ξ)) := by
    calc
      (T_y.card : ENNReal) * ENNReal.ofReal m ≤ ∑ L ∈ T_y, ν (A L) := h_sum_ge
      _ ≤ 13 * ν (Metric.ball y (2 * ξ)) := h_sum_le

  have h_final2 : (T_y.card : ENNReal) * ENNReal.ofReal m ≤ 13 * ENNReal.ofReal (C * (2 * ξ)) := by
    calc
      (T_y.card : ENNReal) * ENNReal.ofReal m ≤ 13 * ν (Metric.ball y (2 * ξ)) := h_final
      _ ≤ 13 * ENNReal.ofReal (C * (2 * ξ)) := by gcongr
  have h_final' : (T_y.card : ℝ) * m ≤ 26 * C * ξ := by
    have h2 : (T_y.card : ENNReal) * ENNReal.ofReal m = ENNReal.ofReal ((T_y.card : ℝ) * m) := by
      have h_nat : (T_y.card : ENNReal) = ENNReal.ofReal (T_y.card : ℝ) := by simp
      rw [h_nat]
      have h_mul : ENNReal.ofReal ((T_y.card : ℝ) * m) =
          ENNReal.ofReal (T_y.card : ℝ) * ENNReal.ofReal m :=
        ENNReal.ofReal_mul (hp := by positivity)
      exact h_mul.symm
    have h3 : 13 * ENNReal.ofReal (C * (2 * ξ)) = ENNReal.ofReal (26 * C * ξ) := by
      have h4 : (13 : ENNReal) = ENNReal.ofReal (13 : ℝ) := by simp
      rw [h4]
      have h5 : ENNReal.ofReal (13 : ℝ) * ENNReal.ofReal (C * (2 * ξ)) =
          ENNReal.ofReal (13 * (C * (2 * ξ))) :=
        (ENNReal.ofReal_mul (hp := by norm_num)).symm
      rw [h5]
      have h6 : 13 * (C * (2 * ξ)) = 26 * C * ξ := by ring
      rw [h6]
    have h4 : ENNReal.ofReal ((T_y.card : ℝ) * m) ≤ ENNReal.ofReal (26 * C * ξ) := by
      calc
        ENNReal.ofReal ((T_y.card : ℝ) * m) = (T_y.card : ENNReal) * ENNReal.ofReal m := h2.symm
        _ ≤ 13 * ENNReal.ofReal (C * (2 * ξ)) := h_final2
        _ = ENNReal.ofReal (26 * C * ξ) := h3
    have h5 : ENNReal.ofReal ((T_y.card : ℝ) * m) ≤ ENNReal.ofReal (26 * C * ξ) ↔
        (T_y.card : ℝ) * m ≤ 26 * C * ξ := by
      exact ENNReal.ofReal_le_ofReal_iff (show 0 ≤ 26 * C * ξ from by positivity)
    exact h5.mp h4
  linarith [h_count]

end RadialBootstrapping
