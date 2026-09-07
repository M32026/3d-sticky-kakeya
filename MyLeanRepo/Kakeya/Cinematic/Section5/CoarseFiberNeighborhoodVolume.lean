import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseFiberCarrierContainmentInputs
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Volume of a coarse-fiber real neighborhood
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Cinematic

lemma measurableSet_coarseFiberRealNeighborhood
    {Delta T C_out : ℝ}
    (R : CurvilinearRectangle Delta T) :
    MeasurableSet (coarseFiberRealNeighborhood R C_out) := by
  let f : ℝ → ℝ := R.function.extension
  let interval : Set ℝ :=
    Set.Icc
      (R.interval.midpoint - C_out * R.interval.length)
      (R.interval.midpoint + C_out * R.interval.length)
  have hf_measurable : Measurable f :=
    R.function.extension_contDiff.continuous.measurable
  have hnorm_measurable :
      Measurable (fun p : ℝ × ℝ => |p.2 - f p.1|) :=
    continuous_abs.measurable.comp
      (measurable_snd.sub (hf_measurable.comp measurable_fst))
  have hset :
      coarseFiberRealNeighborhood R C_out =
        (interval ×ˢ (Set.univ : Set ℝ)) ∩
          {p : ℝ × ℝ | |p.2 - f p.1| ≤ C_out * Delta} := by
    ext p
    simp only [coarseFiberRealNeighborhood, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true,
      interval, f, Set.mem_Icc]
    constructor
    · rintro ⟨hmid, hvertical⟩
      exact ⟨⟨by linarith [(abs_le.mp hmid).1],
        by linarith [(abs_le.mp hmid).2]⟩, hvertical⟩
    · rintro ⟨⟨hleft, hright⟩, hvertical⟩
      exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, hvertical⟩
  rw [hset]
  exact (measurableSet_Icc.prod MeasurableSet.univ).inter
    (hnorm_measurable measurableSet_Iic)

lemma volume_coarseFiberRealNeighborhood
    {Delta T C_out : ℝ}
    (R : CurvilinearRectangle Delta T)
    (hC_out : 0 ≤ C_out)
    (hradius : 0 ≤ C_out * Delta) :
    volume (coarseFiberRealNeighborhood R C_out) =
      ENNReal.ofReal
        (4 * C_out ^ 2 * Delta * R.interval.length) := by
  let f : ℝ → ℝ := R.function.extension
  let interval : Set ℝ :=
    Set.Icc
      (R.interval.midpoint - C_out * R.interval.length)
      (R.interval.midpoint + C_out * R.interval.length)
  let radius : ℝ := C_out * Delta
  have hmeasurable :
      MeasurableSet (coarseFiberRealNeighborhood R C_out) :=
    measurableSet_coarseFiberRealNeighborhood R
  have hslice : ∀ x : ℝ,
      volume
          {y : ℝ |
            (x, y) ∈ coarseFiberRealNeighborhood R C_out} =
        Set.indicator interval
          (fun _ : ℝ => ENNReal.ofReal (2 * radius)) x := by
    intro x
    by_cases hx : x ∈ interval
    · have hset :
          {y : ℝ |
            (x, y) ∈ coarseFiberRealNeighborhood R C_out} =
            Set.Icc (f x - radius) (f x + radius) := by
        ext y
        simp only [coarseFiberRealNeighborhood, Set.mem_setOf_eq,
          Set.mem_Icc, f, radius]
        have hx' :
            |x - R.interval.midpoint| ≤
              C_out * R.interval.length := by
          exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
        constructor
        · rintro ⟨_, hy⟩
          exact ⟨by linarith [(abs_le.mp hy).1],
            by linarith [(abs_le.mp hy).2]⟩
        · rintro ⟨hleft, hright⟩
          exact ⟨hx', abs_le.mpr ⟨by linarith, by linarith⟩⟩
      rw [hset, Real.volume_Icc]
      have hlength :
          ENNReal.ofReal ((f x + radius) - (f x - radius)) =
            ENNReal.ofReal (2 * radius) := by
        congr 1
        ring
      rw [hlength]
      simp [hx]
    · have hset :
          {y : ℝ |
            (x, y) ∈ coarseFiberRealNeighborhood R C_out} = ∅ := by
        ext y
        simp only [coarseFiberRealNeighborhood, Set.mem_setOf_eq,
          Set.mem_empty_iff_false, iff_false]
        intro hy
        apply hx
        exact ⟨by linarith [(abs_le.mp hy.1).1],
          by linarith [(abs_le.mp hy.1).2]⟩
      rw [hset]
      simp [hx]
  have hslice_function :
      (fun x : ℝ =>
        volume
          {y : ℝ |
            (x, y) ∈ coarseFiberRealNeighborhood R C_out}) =
        Set.indicator interval
          (fun _ : ℝ => ENNReal.ofReal (2 * radius)) := by
    funext x
    exact hslice x
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  have hfubini :
      (volume.prod volume)
          (coarseFiberRealNeighborhood R C_out) =
        ∫⁻ x : ℝ,
          volume
            {y : ℝ |
              (x, y) ∈ coarseFiberRealNeighborhood R C_out}
          ∂volume :=
    MeasureTheory.Measure.prod_apply hmeasurable
  rw [hfubini, hslice_function]
  have hintegral :
      (∫⁻ x : ℝ,
        Set.indicator interval
          (fun _ : ℝ => ENNReal.ofReal (2 * radius)) x ∂volume) =
        ENNReal.ofReal (2 * radius) * volume interval :=
    lintegral_indicator_const_comp measurable_id measurableSet_Icc
      (ENNReal.ofReal (2 * radius))
  rw [hintegral, Real.volume_Icc]
  have hlength :
      (R.interval.midpoint + C_out * R.interval.length) -
          (R.interval.midpoint - C_out * R.interval.length) =
        2 * C_out * R.interval.length := by
    ring
  rw [hlength]
  have hradius' : 0 ≤ 2 * radius := by
    dsimp only [radius]
    exact mul_nonneg (by norm_num) hradius
  have hlength_nonneg :
      0 ≤ 2 * C_out * R.interval.length := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) hC_out)
      R.interval.length_nonneg
  rw [← ENNReal.ofReal_mul hradius']
  congr 1
  dsimp only [radius]
  ring

end Kakeya.Cinematic
