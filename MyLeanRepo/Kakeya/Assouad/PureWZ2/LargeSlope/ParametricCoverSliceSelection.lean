import MyLeanRepo.Kakeya.Assouad.LargeSlope.CoverSliceSelection

/-!
# Parametric cover-slice selection

This is the quantitative Markov form needed before the common-slice Fubini
step.  A larger threshold factor makes the exceptional y-set proportionally
smaller.
-/

noncomputable section

open MeasureTheory Set Metric Finset

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/--
For radius `W` and finite positive threshold factor `K`, the bad set of
heights meeting more than `K * W * #centers` vertical windows has measure at
most `2 / K`.
-/
theorem exists_parametric_cover_slice_good_set
    {W : ℝ} (hW_pos : 0 < W)
    {K : ENNReal} (hK_zero : K ≠ 0) (hK_top : K ≠ ⊤)
    (coverCenters : Finset Point3) :
    ∃ good : Set ℝ,
      MeasurableSet good ∧
      good ⊆ Set.Icc (-1 : ℝ) 1 ∧
      volume (Set.Icc (-1 : ℝ) 1 \ good) ≤ 2 / K ∧
      ∀ y ∈ good,
        ((coverCenters.filter
          (fun center => |center (1 : Fin 3) - y| ≤ W)).card : ENNReal) ≤
          K * ENNReal.ofReal W *
            (coverCenters.card : ENNReal) := by
  let numberOfCenters := coverCenters.card
  by_cases hnumber : numberOfCenters = 0
  · have hempty : coverCenters = ∅ := Finset.card_eq_zero.mp hnumber
    refine ⟨Set.Icc (-1 : ℝ) 1, measurableSet_Icc, Set.Subset.rfl, ?_, ?_⟩
    · simp
    · intro y _
      rw [hempty]
      simp
  · have hnumber_pos : 0 < numberOfCenters := Nat.pos_of_ne_zero hnumber
    let interval : Set ℝ := Set.Icc (-1) 1
    let window (center : Point3) : Set ℝ :=
      Set.Icc (center 1 - W) (center 1 + W)
    let indicator (center : Point3) : ℝ → ENNReal :=
      fun y => if y ∈ window center then 1 else 0
    let count : ℝ → ENNReal := fun y =>
      ∑ center ∈ coverCenters, indicator center y
    have hwindow :
        ∀ center : Point3,
          {y : ℝ | |center 1 - y| ≤ W} = window center := by
      intro center
      ext y
      simp only [Set.mem_setOf_eq, window, Set.mem_Icc]
      rw [abs_le]
      constructor <;> intro h <;> constructor <;> linarith
    have hindicator :
        ∀ center : Point3,
          indicator center =
            (window center).indicator (1 : ℝ → ENNReal) := by
      intro center
      funext y
      simp [indicator, Set.indicator_apply]
    have hcount_card :
        ∀ y, count y =
          ((coverCenters.filter
            (fun center => |center 1 - y| ≤ W)).card : ENNReal) := by
      intro y
      have hterm :
          ∀ center ∈ coverCenters,
            indicator center y =
              if |center 1 - y| ≤ W then (1 : ENNReal) else 0 := by
        intro center _
        have hmem :
            y ∈ window center ↔ |center 1 - y| ≤ W := by
          have hset := hwindow center
          rw [← hset]
          rfl
        simp [indicator, hmem]
      rw [show count y =
          ∑ center ∈ coverCenters,
            if |center 1 - y| ≤ W then (1 : ENNReal) else 0 by
        apply Finset.sum_congr rfl
        exact hterm]
      rw [Finset.sum_ite]
      simp [Finset.sum_const]
    have hindicator_measurable :
        ∀ center ∈ coverCenters, Measurable (indicator center) := by
      intro center _
      rw [hindicator center]
      exact Measurable.indicator measurable_const measurableSet_Icc
    have hcount_measurable : Measurable count := by
      apply Finset.measurable_sum
      exact hindicator_measurable
    have hintegral_indicator :
        ∀ center ∈ coverCenters,
          ∫⁻ y in interval, indicator center y ≤
            ENNReal.ofReal (2 * W) := by
      intro center _
      have heq :
          ∫⁻ y in interval, indicator center y =
            volume (window center ∩ interval) := by
        rw [hindicator center]
        have hone :
            ∫⁻ y : ℝ,
                (window center).indicator (1 : ℝ → ENNReal) y
                  ∂(volume.restrict interval) =
              (volume.restrict interval) (window center) :=
          lintegral_indicator_one measurableSet_Icc
        rw [hone]
        rw [Measure.restrict_apply measurableSet_Icc]
      calc
        ∫⁻ y in interval, indicator center y
            = volume (window center ∩ interval) := heq
        _ ≤ volume (window center) := measure_mono Set.inter_subset_left
        _ = ENNReal.ofReal (2 * W) := by
          dsimp [window]
          rw [Real.volume_Icc]
          congr 1
          ring
    let total : ENNReal :=
      ENNReal.ofReal W * (numberOfCenters : ENNReal)
    have htotal_zero : total ≠ 0 := by
      have hW_enn : ENNReal.ofReal W ≠ 0 := by
        exact (ENNReal.ofReal_pos.mpr hW_pos).ne'
      have hnumber_enn : (numberOfCenters : ENNReal) ≠ 0 := by
        exact_mod_cast hnumber_pos.ne'
      exact mul_ne_zero hW_enn hnumber_enn
    have htotal_top : total ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
    have hintegral_count :
        ∫⁻ y in interval, count y ≤ 2 * total := by
      have hsum :
          ∫⁻ y in interval, count y =
            ∑ center ∈ coverCenters,
              ∫⁻ y in interval, indicator center y := by
        rw [lintegral_finsetSum _ hindicator_measurable]
      rw [hsum]
      calc
        ∑ center ∈ coverCenters,
              ∫⁻ y in interval, indicator center y
            ≤ ∑ _center ∈ coverCenters,
                ENNReal.ofReal (2 * W) :=
          Finset.sum_le_sum hintegral_indicator
        _ = 2 * total := by
          have htwo :
              ENNReal.ofReal (2 * W) =
                2 * ENNReal.ofReal W := by
            rw [show (2 * W : ℝ) = (2 : ℝ) * W by ring,
              ENNReal.ofReal_mul (by norm_num)]
            simp
          rw [htwo]
          simp [total, numberOfCenters, Finset.sum_const]
          ring
    let threshold : ENNReal := K * total
    let bad : Set ℝ := {y ∈ interval | threshold ≤ count y}
    have hbad_measurable : MeasurableSet bad :=
      measurableSet_Icc.inter (hcount_measurable measurableSet_Ici)
    have hge_inter :
        {y : ℝ | threshold ≤ count y} ∩ interval = bad := by
      ext y
      simp [bad]
      tauto
    have hmarkov_raw :
        threshold * (volume.restrict interval)
            {y : ℝ | threshold ≤ count y} ≤
          ∫⁻ y in interval, count y :=
      MeasureTheory.mul_meas_ge_le_lintegral₀
        hcount_measurable.aemeasurable threshold
    have hrestricted :
        (volume.restrict interval)
            {y : ℝ | threshold ≤ count y} = volume bad := by
      have hset_measurable :
          MeasurableSet {y : ℝ | threshold ≤ count y} :=
        hcount_measurable measurableSet_Ici
      calc
        (volume.restrict interval) {y : ℝ | threshold ≤ count y}
            = volume ({y : ℝ | threshold ≤ count y} ∩ interval) := by
              rw [Measure.restrict_apply hset_measurable]
        _ = volume bad := by rw [hge_inter]
    have hmarkov : threshold * volume bad ≤ 2 * total := by
      rw [hrestricted] at hmarkov_raw
      exact hmarkov_raw.trans hintegral_count
    have hcancel : K * volume bad ≤ 2 := by
      have hrewrite :
          total * (K * volume bad) ≤ total * 2 := by
        simpa [threshold, mul_assoc, mul_comm, mul_left_comm] using hmarkov
      exact
        (ENNReal.mul_le_mul_iff_right htotal_zero htotal_top).mp
          (by simpa [mul_comm] using hrewrite)
    have hbad_volume : volume bad ≤ 2 / K := by
      apply (ENNReal.le_div_iff_mul_le
        (Or.inl hK_zero) (Or.inl hK_top)).mpr
      simpa [mul_comm] using hcancel
    let good : Set ℝ := interval \ bad
    have hgood_measurable : MeasurableSet good :=
      measurableSet_Icc.diff hbad_measurable
    refine ⟨good, hgood_measurable, ?_, ?_, ?_⟩
    · intro y hy
      exact hy.1
    · have hdiff : interval \ good = bad := by
        ext y
        simp [good, bad]
      rw [hdiff]
      exact hbad_volume
    · intro y hy
      have hnot_bad : y ∉ bad := hy.2
      have hlt : count y < threshold := by
        by_contra h
        exact hnot_bad ⟨hy.1, le_of_not_gt h⟩
      have hle : count y ≤ threshold := le_of_lt hlt
      simpa [hcount_card y, threshold, total, numberOfCenters, mul_assoc] using hle

end Kakeya.Assouad

end
