import MyLeanRepo.Kakeya.CV.GeometricMeasure.GraphAreaLocalComparison
import MyLeanRepo.Kakeya.CV.GeometricMeasure.GraphPullbackMeasureAbsoluteContinuity
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

private lemma real_lower_squeeze {l a : ℝ} (ha : 0 ≤ a)
    (h : ∀ (c : ℝ), 0 < c → c < 1 → l ≥ c ^ 2 * a) : l ≥ a := by
  have h_l_nonneg : 0 ≤ l := by
    have h2 := h (1 / 2 : ℝ) (by norm_num) (by norm_num)
    have h3 : (1 / 2 : ℝ) ^ 2 * a ≥ 0 := by positivity
    linarith
  by_contra h'
  have h_lt : l < a := by
    simpa [not_le] using h'
  have ha_pos : 0 < a := by
    by_cases h : a = 0
    · rw [h] at h_lt <;> linarith
    · linarith
  set c : ℝ := Real.sqrt ((l + a) / (2 * a)) with hc_def
  have h0 : 0 < (l + a) / (2 * a) := by positivity
  have h1 : (l + a) / (2 * a) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hc1 : 0 < c := Real.sqrt_pos.mpr h0
  have hc2 : c < 1 := by
    have h9 : c ^ 2 < 1 := by
      rw [Real.sq_sqrt (by positivity)] <;> exact h1
    have h10 : 0 ≤ c := Real.sqrt_nonneg _
    nlinarith
  have hc3 : c ^ 2 = (l + a) / (2 * a) :=
    Real.sq_sqrt (by positivity)
  have h4 : c ^ 2 * a = (l + a) / 2 := by
    rw [hc3]
    field_simp [ha_pos.ne'] <;> ring
  have h5 : c ^ 2 * a > l := by
    rw [h4] <;> linarith
  have h6 := h c hc1 hc2
  linarith

private lemma real_upper_squeeze {l a : ℝ} (ha : 0 ≤ a) (hl : 0 ≤ l)
    (h : ∀ (c : ℝ), 1 < c → l ≤ c ^ 2 * a) : l ≤ a := by
  by_contra h'
  have h_gt : a < l := by
    simpa [not_le] using h'
  by_cases ha0 : a = 0
  · have h9 := h 2 (by norm_num)
    rw [ha0] at h9 <;> linarith
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    set c : ℝ := Real.sqrt ((a + l) / (2 * a)) with hc_def
    have h0 : 0 < (a + l) / (2 * a) := by positivity
    have h1 : 1 < (a + l) / (2 * a) := by
      apply (one_lt_div (by positivity)).mpr
      linarith
    have hc1 : 1 < c := by
      have h9 : 1 < c ^ 2 := by
        rw [Real.sq_sqrt (by positivity)] <;> exact h1
      have h10 : 0 ≤ c := Real.sqrt_nonneg _
      nlinarith
    have hc3 : c ^ 2 = (a + l) / (2 * a) :=
      Real.sq_sqrt (by positivity)
    have h4 : c ^ 2 * a = (a + l) / 2 := by
      rw [hc3]
      field_simp [ha_pos.ne'] <;> ring
    have h5 : c ^ 2 * a < l := by
      rw [h4] <;> linarith
    have h6 := h c hc1
    linarith

/-- The Radon--Nikodym derivative of the graph pullback measure equals the
tangent-plane area factor almost everywhere. -/
lemma graphPullbackMeasure_rnDeriv
    (g : R2 → ℝ) (hg : ContDiff ℝ 1 g) :
    ∀ᵐ (x : R2) ∂volume,
      (graphPullbackMeasure g).rnDeriv volume x = areaFactor g x := by
  let ρ : Measure R2 := graphPullbackMeasure g
  have h_ac : ρ ≪ volume := graphPullbackMeasure_absolutelyContinuous g hg
  haveI : IsLocallyFiniteMeasure ρ :=
    graphPullbackMeasure_isLocallyFinite g hg
  have h_besicovitch : ∀ᵐ (x : R2) ∂volume,
      Filter.Tendsto
        (fun r : ℝ => ρ (closedBall x r) / volume (closedBall x r))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (ρ.rnDeriv volume x)) :=
    Besicovitch.ae_tendsto_rnDeriv ρ volume
  have h_area_finite : ∀ (x : R2), areaFactor g x ≠ ⊤ := by
    intro x
    exact ENNReal.mul_ne_top planeConstant_ne_top ENNReal.ofReal_ne_top
  have h_rn_finite :
      ∀ᵐ (x : R2) ∂volume, ρ.rnDeriv volume x ≠ ⊤ := by
    have h : ∀ᵐ (x : R2) ∂volume, ρ.rnDeriv volume x < ⊤ :=
      ρ.rnDeriv_lt_top volume
    filter_upwards [h] with x hx
    exact hx.ne
  filter_upwards [h_besicovitch, h_rn_finite] with
    x h_tendsto h_rn_ne_top
  set L : ENNReal := ρ.rnDeriv volume x with hL_def
  set a : ENNReal := areaFactor g x with ha_def
  have ha_ne_top : a ≠ ⊤ := h_area_finite x
  have hL_ne_top : L ≠ ⊤ := h_rn_ne_top
  have h_squeeze_lower : ∀ (c : ℝ), 0 < c → c < 1 →
      L ≥ (ENNReal.ofReal c) ^ 2 * a := by
    intro c hc_pos hc_lt_one
    let ε := 1 - c
    have hε_pos : 0 < ε := by linarith
    have hε_lt_one : ε < 1 := by linarith
    have h1 : (1 - ε : ℝ) = c := by linarith
    rcases local_area_comparison isOpen_univ (Set.mem_univ x)
      hg.contDiffOn ε hε_pos hε_lt_one with
      ⟨r0, hr0_pos, h_comp⟩
    have h_event : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
        (ENNReal.ofReal c) ^ 2 * a ≤
          ρ (closedBall x r) / volume (closedBall x r) := by
      have h_nhds :
          ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0), r < r0 :=
        Filter.Eventually.filter_mono inf_le_left
          (Iio_mem_nhds hr0_pos)
      filter_upwards [h_nhds, self_mem_nhdsWithin] with r hr_lt hr_pos'
      have hr_pos'' : 0 < r := hr_pos'
      have h_sub : closedBall x r ⊆ ball x r0 := by
        intro y hy
        have h5 : dist y x ≤ r := hy
        have h6 : dist y x < r0 := by linarith
        exact h6
      have h_ball_meas : MeasurableSet (closedBall x r) :=
        isClosed_closedBall.measurableSet
      have h_bounds := h_comp (closedBall x r) h_ball_meas h_sub
      have hvol_pos : 0 < volume (closedBall x r) :=
        Metric.measure_closedBall_pos volume x hr_pos''
      have hvol_ne : volume (closedBall x r) ≠ ⊤ :=
        (isCompact_closedBall x r).measure_ne_top
      have hρ_eq :
          ρ (closedBall x r) =
            μH[2] (graphMap g '' (closedBall x r)) :=
        graphPullbackMeasure_apply hg.continuous h_ball_meas
      have h10 :
          μH[2] (graphMap g '' (closedBall x r)) ≥
            (ENNReal.ofReal c) ^ 2 * a * volume (closedBall x r) := by
        simpa [h1, ha_def] using h_bounds.1
      have h12 : volume (closedBall x r) ≠ 0 := hvol_pos.ne'
      have h13 :
          ρ (closedBall x r) / volume (closedBall x r) ≥
            ((ENNReal.ofReal c) ^ 2 * a * volume (closedBall x r)) /
              volume (closedBall x r) :=
        ENNReal.div_le_div (by rw [hρ_eq] <;> exact h10) le_rfl
      have h14 :
          ((ENNReal.ofReal c) ^ 2 * a * volume (closedBall x r)) /
              volume (closedBall x r) =
            (ENNReal.ofReal c) ^ 2 * a :=
        ENNReal.mul_div_cancel_right h12 hvol_ne
      rw [h14] at h13
      exact h13
    exact ge_of_tendsto h_tendsto h_event
  have h_squeeze_upper_small : ∀ (c : ℝ), 1 < c → c < 2 →
      L ≤ (ENNReal.ofReal c) ^ 2 * a := by
    intro c hc_gt_one hc_lt_two
    let ε := c - 1
    have hε_pos : 0 < ε := by linarith
    have hε_lt_one : ε < 1 := by linarith
    have h1 : (1 + ε : ℝ) = c := by linarith
    rcases local_area_comparison isOpen_univ (Set.mem_univ x)
      hg.contDiffOn ε hε_pos hε_lt_one with
      ⟨r0, hr0_pos, h_comp⟩
    have h_event : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
        ρ (closedBall x r) / volume (closedBall x r) ≤
          (ENNReal.ofReal c) ^ 2 * a := by
      have h_nhds :
          ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0), r < r0 :=
        Filter.Eventually.filter_mono inf_le_left
          (Iio_mem_nhds hr0_pos)
      filter_upwards [h_nhds, self_mem_nhdsWithin] with r hr_lt hr_pos'
      have hr_pos'' : 0 < r := hr_pos'
      have h_sub : closedBall x r ⊆ ball x r0 := by
        intro y hy
        have h5 : dist y x ≤ r := hy
        have h6 : dist y x < r0 := by linarith
        exact h6
      have h_ball_meas : MeasurableSet (closedBall x r) :=
        isClosed_closedBall.measurableSet
      have h_bounds := h_comp (closedBall x r) h_ball_meas h_sub
      have hvol_pos : 0 < volume (closedBall x r) :=
        Metric.measure_closedBall_pos volume x hr_pos''
      have hvol_ne : volume (closedBall x r) ≠ ⊤ :=
        (isCompact_closedBall x r).measure_ne_top
      have hρ_eq :
          ρ (closedBall x r) =
            μH[2] (graphMap g '' (closedBall x r)) :=
        graphPullbackMeasure_apply hg.continuous h_ball_meas
      have h10 :
          μH[2] (graphMap g '' (closedBall x r)) ≤
            (ENNReal.ofReal c) ^ 2 * a * volume (closedBall x r) := by
        simpa [h1, ha_def] using h_bounds.2
      have h12 : volume (closedBall x r) ≠ 0 := hvol_pos.ne'
      have h13 :
          ρ (closedBall x r) / volume (closedBall x r) ≤
            ((ENNReal.ofReal c) ^ 2 * a * volume (closedBall x r)) /
              volume (closedBall x r) :=
        ENNReal.div_le_div (by rw [hρ_eq] <;> exact h10) le_rfl
      have h14 :
          ((ENNReal.ofReal c) ^ 2 * a * volume (closedBall x r)) /
              volume (closedBall x r) =
            (ENNReal.ofReal c) ^ 2 * a :=
        ENNReal.mul_div_cancel_right h12 hvol_ne
      rw [h14] at h13
      exact h13
    exact le_of_tendsto h_tendsto h_event
  have h_squeeze_upper : ∀ (c : ℝ), 1 < c →
      L ≤ (ENNReal.ofReal c) ^ 2 * a := by
    intro c hc
    let d : ℝ := min c (3 / 2)
    have hd1 : 1 < d := by
      dsimp only [d]
      exact lt_min hc (by norm_num)
    have hd2 : d < 2 := by
      exact lt_of_le_of_lt (min_le_right c (3 / 2)) (by norm_num)
    have hdc : d ≤ c := min_le_left _ _
    have hof : ENNReal.ofReal d ≤ ENNReal.ofReal c :=
      ENNReal.ofReal_le_ofReal hdc
    have hpow :
        (ENNReal.ofReal d) ^ 2 ≤ (ENNReal.ofReal c) ^ 2 :=
      pow_le_pow_left₀ bot_le hof 2
    exact (h_squeeze_upper_small d hd1 hd2).trans
      (mul_le_mul_right' hpow a)
  have h_lower_real : ∀ (c : ℝ), 0 < c → c < 1 →
      L.toReal ≥ c ^ 2 * a.toReal := by
    intro c hc1 hc2
    have h := h_squeeze_lower c hc1 hc2
    have h9 :
        ((ENNReal.ofReal c) ^ 2 * a).toReal =
          c ^ 2 * a.toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hc1.le]
    have hprod_ne_top : (ENNReal.ofReal c) ^ 2 * a ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) ha_ne_top
    have hreal :
        ((ENNReal.ofReal c) ^ 2 * a).toReal ≤ L.toReal :=
      (ENNReal.toReal_le_toReal hprod_ne_top hL_ne_top).mpr h
    rw [h9] at hreal
    exact hreal
  have h_upper_real : ∀ (c : ℝ), 1 < c →
      L.toReal ≤ c ^ 2 * a.toReal := by
    intro c hc
    have h := h_squeeze_upper c hc
    have h9 :
        ((ENNReal.ofReal c) ^ 2 * a).toReal =
          c ^ 2 * a.toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (le_trans zero_le_one hc.le)]
    have hprod_ne_top : (ENNReal.ofReal c) ^ 2 * a ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) ha_ne_top
    have hreal :
        L.toReal ≤ ((ENNReal.ofReal c) ^ 2 * a).toReal :=
      (ENNReal.toReal_le_toReal hL_ne_top hprod_ne_top).mpr h
    rw [h9] at hreal
    exact hreal
  have ha_nonneg : 0 ≤ a.toReal := by positivity
  have hL_nonneg : 0 ≤ L.toReal := by positivity
  have h_lower_final : L.toReal ≥ a.toReal :=
    real_lower_squeeze ha_nonneg h_lower_real
  have h_upper_final : L.toReal ≤ a.toReal :=
    real_upper_squeeze ha_nonneg hL_nonneg h_upper_real
  have h_eq : L.toReal = a.toReal := by linarith
  exact (ENNReal.toReal_eq_toReal_iff' hL_ne_top ha_ne_top).mp h_eq

end Kakeya.CV
