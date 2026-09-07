import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.RotatedHorizontalCoordinates
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ParametricCoverSliceSelection

/-!
# Cover-slice selection in a rotated horizontal frame

The paper carrier lies in the axis box `[-1,1]^3`.  After a horizontal
rotation its new y-coordinate lies in `[-sqrt 2,sqrt 2]`, hence safely in
`[-2,2]`.  Markov's window-count argument is unchanged except that the
ambient interval has length four.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric Finset

attribute [local instance] Classical.propDecidable

/-- Parametric Markov selection on the interval `[-2,2]`. -/
theorem exists_parametric_cover_slice_good_set_two
    {W : ℝ} (hWPos : 0 < W)
    {K : ENNReal} (hKZero : K ≠ 0) (hKTop : K ≠ ⊤)
    (coverCenters : Finset Point3) :
    ∃ good : Set ℝ,
      MeasurableSet good ∧
      good ⊆ Set.Icc (-2 : ℝ) 2 ∧
      volume (Set.Icc (-2 : ℝ) 2 \ good) ≤ 2 / K ∧
      ∀ y ∈ good,
        ((coverCenters.filter fun center =>
          |center (1 : Fin 3) - y| ≤ W).card : ENNReal) ≤
          K * ENNReal.ofReal W * (coverCenters.card : ENNReal) := by
  let numberOfCenters := coverCenters.card
  by_cases hnumber : numberOfCenters = 0
  · have hempty : coverCenters = ∅ := Finset.card_eq_zero.mp hnumber
    refine ⟨Set.Icc (-2 : ℝ) 2, measurableSet_Icc, Set.Subset.rfl, ?_, ?_⟩
    · simp
    · intro y _
      rw [hempty]
      simp
  · have hnumberPos : 0 < numberOfCenters := Nat.pos_of_ne_zero hnumber
    let interval : Set ℝ := Set.Icc (-2) 2
    let window (center : Point3) : Set ℝ :=
      Set.Icc (center 1 - W) (center 1 + W)
    let indicator (center : Point3) : ℝ → ENNReal :=
      fun y => if y ∈ window center then 1 else 0
    let count : ℝ → ENNReal := fun y =>
      ∑ center ∈ coverCenters, indicator center y
    have hwindow : ∀ center : Point3,
        {y : ℝ | |center 1 - y| ≤ W} = window center := by
      intro center
      ext y
      simp only [Set.mem_setOf_eq, window, Set.mem_Icc]
      rw [abs_le]
      constructor <;> intro h <;> constructor <;> linarith
    have hindicator : ∀ center : Point3, indicator center =
        (window center).indicator (1 : ℝ → ENNReal) := by
      intro center
      funext y
      simp [indicator, Set.indicator_apply]
    have hcountCard : ∀ y, count y =
        ((coverCenters.filter fun center =>
          |center 1 - y| ≤ W).card : ENNReal) := by
      intro y
      rw [show count y = ∑ center ∈ coverCenters,
          if |center 1 - y| ≤ W then (1 : ENNReal) else 0 by
        apply Finset.sum_congr rfl
        intro center _
        have hmem : y ∈ window center ↔ |center 1 - y| ≤ W := by
          rw [← hwindow center]
          rfl
        simp [indicator, hmem]]
      rw [Finset.sum_ite]
      simp [Finset.sum_const]
    have hindicatorMeasurable : ∀ center ∈ coverCenters,
        Measurable (indicator center) := by
      intro center _
      rw [hindicator center]
      exact Measurable.indicator measurable_const measurableSet_Icc
    have hcountMeasurable : Measurable count := by
      apply Finset.measurable_sum
      exact hindicatorMeasurable
    have hintegralIndicator : ∀ center ∈ coverCenters,
        ∫⁻ y in interval, indicator center y ≤ ENNReal.ofReal (2 * W) := by
      intro center _
      have heq : ∫⁻ y in interval, indicator center y =
          volume (window center ∩ interval) := by
        rw [hindicator center]
        rw [lintegral_indicator_one measurableSet_Icc]
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
    have htotalZero : total ≠ 0 := by
      exact mul_ne_zero (ENNReal.ofReal_pos.mpr hWPos).ne'
        (by exact_mod_cast hnumberPos.ne')
    have htotalTop : total ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
    have hintegralCount : ∫⁻ y in interval, count y ≤ 2 * total := by
      rw [lintegral_finsetSum _ hindicatorMeasurable]
      calc
        ∑ center ∈ coverCenters, ∫⁻ y in interval, indicator center y
          ≤ ∑ _center ∈ coverCenters, ENNReal.ofReal (2 * W) :=
            Finset.sum_le_sum hintegralIndicator
        _ = 2 * total := by
          have htwo : ENNReal.ofReal (2 * W) =
              2 * ENNReal.ofReal W := by
            rw [show (2 * W : ℝ) = (2 : ℝ) * W by ring,
              ENNReal.ofReal_mul (by norm_num)]
            simp
          rw [htwo]
          simp [total, numberOfCenters, Finset.sum_const]
          ring
    let threshold := K * total
    let bad : Set ℝ := {y ∈ interval | threshold ≤ count y}
    have hbadMeasurable : MeasurableSet bad :=
      measurableSet_Icc.inter (hcountMeasurable measurableSet_Ici)
    have hgeInter : {y : ℝ | threshold ≤ count y} ∩ interval = bad := by
      ext y
      simp [bad]
      tauto
    have hgeMeasurable : MeasurableSet {y : ℝ | threshold ≤ count y} :=
      hcountMeasurable measurableSet_Ici
    have hrestricted : (volume.restrict interval)
        {y : ℝ | threshold ≤ count y} = volume bad := by
      calc
        (volume.restrict interval) {y : ℝ | threshold ≤ count y}
          = volume ({y : ℝ | threshold ≤ count y} ∩ interval) := by
            exact Measure.restrict_apply hgeMeasurable
        _ = volume bad := by rw [hgeInter]
    have hmarkovRaw := MeasureTheory.mul_meas_ge_le_lintegral₀
      hcountMeasurable.aemeasurable threshold
      (μ := volume.restrict interval)
    have hmarkov : threshold * volume bad ≤ 2 * total := by
      rw [hrestricted] at hmarkovRaw
      exact hmarkovRaw.trans hintegralCount
    have hcancel : K * volume bad ≤ 2 := by
      have hrewrite : total * (K * volume bad) ≤ total * 2 := by
        simpa [threshold, mul_assoc, mul_comm, mul_left_comm] using hmarkov
      exact (ENNReal.mul_le_mul_iff_right htotalZero htotalTop).mp
        (by simpa [mul_comm] using hrewrite)
    have hbadVolume : volume bad ≤ 2 / K := by
      apply (ENNReal.le_div_iff_mul_le
        (Or.inl hKZero) (Or.inl hKTop)).mpr
      simpa [mul_comm] using hcancel
    let good := interval \ bad
    refine ⟨good, measurableSet_Icc.diff hbadMeasurable, ?_, ?_, ?_⟩
    · exact fun _ h => h.1
    · have hdiff : interval \ good = bad := by
        ext y
        simp [good, bad]
      rwa [hdiff]
    · intro y hy
      have hnotBad : y ∉ bad := hy.2
      have hle : count y ≤ threshold := by
        exact le_of_lt (lt_of_not_ge fun h => hnotBad ⟨hy.1, h⟩)
      simpa [hcountCard y, threshold, total, numberOfCenters, mul_assoc]
        using hle

/-- Transport a ball cover through the fixed horizontal rotation. -/
theorem pureWZ2_rotate_ball_cover
    {E : Set Point3} {r : ℝ} {N : ENNReal}
    (frameSlope : ℝ) (hcover : CanCoverByBalls E r N) :
    CanCoverByBalls (pureWZ2HorizontalRotation frameSlope '' E) r N := by
  rcases hcover with ⟨centers, hcard, hcenters⟩
  let rotation := pureWZ2HorizontalRotation frameSlope
  let embedding : Point3 ↪ Point3 :=
    ⟨rotation, rotation.injective⟩
  refine ⟨centers.map embedding, ?_, ?_⟩
  · simpa [embedding] using hcard
  · intro point hpoint
    rcases hpoint with ⟨source, hsource, rfl⟩
    rcases hcenters source hsource with ⟨center, hcenter, hball⟩
    refine ⟨rotation center, Finset.mem_map.mpr
      ⟨center, hcenter, rfl⟩, ?_⟩
    have hdist := rotation.isometry.dist_eq source center
    simpa [Metric.mem_closedBall] using hdist ▸ hball

end Kakeya.Assouad

end
