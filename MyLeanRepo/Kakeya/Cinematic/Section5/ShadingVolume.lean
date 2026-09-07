import MyLeanRepo.Kakeya.Cinematic.Section5.FineShadings
import MyLeanRepo.Kakeya.Cinematic.Geometry
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Fine-shading volume bounds

This module bounds one enlarged fine shading by the real-coordinate carrier
of its enlarged rectangle, then sums the bound over a finite family.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Cinematic

def CurvilinearRectangle.realCarrier {delta t : ℝ}
    (R : CurvilinearRectangle delta t) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc R.interval.left R.interval.right ∧
    |p.2 - R.function.extension p.1| ≤ delta}

lemma CurvilinearRectangle.measurableSet_realCarrier {delta t : ℝ}
    (R : CurvilinearRectangle delta t) :
    MeasurableSet R.realCarrier := by
  let f : ℝ → ℝ := R.function.extension
  let interval : Set ℝ := Set.Icc R.interval.left R.interval.right
  have hf_measurable : Measurable f :=
    R.function.extension_contDiff.continuous.measurable
  have hnorm_measurable :
      Measurable (fun p : ℝ × ℝ => |p.2 - f p.1|) :=
    continuous_abs.measurable.comp
      (measurable_snd.sub (hf_measurable.comp measurable_fst))
  have hcarrier :
      R.realCarrier =
        (interval ×ˢ (Set.univ : Set ℝ)) ∩
          {p : ℝ × ℝ | |p.2 - f p.1| ≤ delta} := by
    ext p
    simp [CurvilinearRectangle.realCarrier, interval, f]
  rw [hcarrier]
  exact (measurableSet_Icc.prod MeasurableSet.univ).inter
    (hnorm_measurable measurableSet_Iic)

lemma ParameterInterval.eq_of_midpoint_length
    (I J : ParameterInterval)
    (hmid : I.midpoint = J.midpoint)
    (hlen : I.length = J.length) : I = J := by
  have hleft : I.left = J.left := by
    simp [ParameterInterval.midpoint, ParameterInterval.length] at hmid hlen ⊢
    linarith
  have hright : I.right = J.right := by
    simp [ParameterInterval.midpoint, ParameterInterval.length] at hmid hlen ⊢
    linarith
  cases I
  cases J
  simp_all

lemma CurvilinearRectangle.volume_realCarrier {delta t : ℝ}
    (R : CurvilinearRectangle delta t) (hdelta : 0 ≤ delta) :
    volume R.realCarrier =
      ENNReal.ofReal (2 * delta * R.interval.length) := by
  let f : ℝ → ℝ := R.function.extension
  let interval : Set ℝ := Set.Icc R.interval.left R.interval.right
  have hcarrier_measurable : MeasurableSet R.realCarrier :=
    R.measurableSet_realCarrier
  have hslice : ∀ x : ℝ,
      volume {y : ℝ | (x, y) ∈ R.realCarrier} =
        Set.indicator interval
          (fun _ : ℝ => ENNReal.ofReal (2 * delta)) x := by
    intro x
    by_cases hx : x ∈ interval
    · have hset :
          {y : ℝ | (x, y) ∈ R.realCarrier} =
            Set.Icc (f x - delta) (f x + delta) := by
        ext y
        simp only [CurvilinearRectangle.realCarrier, Set.mem_setOf_eq,
          Set.mem_Icc, f]
        constructor
        · intro hy
          exact ⟨by linarith [(abs_le.mp hy.2).1],
            by linarith [(abs_le.mp hy.2).2]⟩
        · rintro ⟨hleft, hright⟩
          exact ⟨hx, abs_le.mpr ⟨by linarith, by linarith⟩⟩
      rw [hset, Real.volume_Icc]
      have hlength :
          ENNReal.ofReal ((f x + delta) - (f x - delta)) =
            ENNReal.ofReal (2 * delta) := by
        congr 1
        ring
      rw [hlength]
      simp [hx]
    · have hset :
          {y : ℝ | (x, y) ∈ R.realCarrier} = ∅ := by
        ext y
        simp only [CurvilinearRectangle.realCarrier, Set.mem_setOf_eq,
          Set.mem_empty_iff_false, iff_false]
        intro hy
        exact hx hy.1
      rw [hset]
      simp [hx]
  have hslice_function :
      (fun x : ℝ => volume {y : ℝ | (x, y) ∈ R.realCarrier}) =
        Set.indicator interval
          (fun _ : ℝ => ENNReal.ofReal (2 * delta)) := by
    funext x
    exact hslice x
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  have hfubini :
      (volume.prod volume) R.realCarrier =
        ∫⁻ x : ℝ, volume {y : ℝ | (x, y) ∈ R.realCarrier} ∂volume :=
    MeasureTheory.Measure.prod_apply hcarrier_measurable
  rw [hfubini, hslice_function]
  have hintegral :
      (∫⁻ x : ℝ,
        Set.indicator interval
          (fun _ : ℝ => ENNReal.ofReal (2 * delta)) x ∂volume) =
        ENNReal.ofReal (2 * delta) * volume interval :=
    lintegral_indicator_const_comp measurable_id measurableSet_Icc
      (ENNReal.ofReal (2 * delta))
  rw [hintegral]
  have hinterval_volume :
      volume interval = ENNReal.ofReal R.interval.length := by
    rw [Real.volume_Icc]
    rfl
  rw [hinterval_volume]
  have hnonnegative : 0 ≤ 2 * delta := by positivity
  rw [← ENNReal.ofReal_mul hnonnegative]

lemma fineOuterShading_subset_realCarrier
    {family : Set C2Function} {E₂ : Set (ℝ × ℝ)}
    {K delta t Delta C_R C_s : ℝ}
    (data : FineRectangleAssignmentData family E₂ K delta t Delta C_R)
    (R : CurvilinearRectangle delta (C_R * t * Delta / delta))
    (U : CurvilinearRectangle
      (C_s * delta) (C_R * t * Delta / delta))
    (hU_function : U.function = R.function)
    (hU_midpoint : U.interval.midpoint = R.interval.midpoint) :
    fineOuterShading data C_s R ⊆ U.realCarrier := by
  intro p hp
  rcases hp with
    ⟨hpE, _, U', hU'_function, hU'_midpoint, _, hpoint⟩
  have hU'_length : U'.interval.length = U.interval.length := by
    rw [U'.interval_length, U.interval_length]
  have hU'_midpoint' :
      U'.interval.midpoint = U.interval.midpoint := by
    rw [hU'_midpoint, hU_midpoint]
  have hinterval :
      U'.interval = U.interval :=
    ParameterInterval.eq_of_midpoint_length U'.interval U.interval
      hU'_midpoint' hU'_length
  have hfunction : U'.function = U.function := by
    rw [hU'_function, hU_function]
  have hcarrier : U'.carrier = U.carrier := by
    change
      verticalNeighborhoodOn U'.function (C_s * delta) U'.interval =
        verticalNeighborhoodOn U.function (C_s * delta) U.interval
    rw [hfunction, hinterval]
  rw [hcarrier] at hpoint
  have hpoint_pair :
      (((data.point ⟨p, hpE⟩).1 : ℝ),
        (data.point ⟨p, hpE⟩).2) = p :=
    data.point_coe ⟨p, hpE⟩
  have hpoint_first :
      ((data.point ⟨p, hpE⟩).1 : ℝ) = p.1 :=
    congrArg Prod.fst hpoint_pair
  have hpoint_second :
      (data.point ⟨p, hpE⟩).2 = p.2 :=
    congrArg Prod.snd hpoint_pair
  have hhorizontal :
      p.1 ∈ Set.Icc U.interval.left U.interval.right := by
    have hmem :
        ((data.point ⟨p, hpE⟩).1 : ℝ) ∈
          Set.Icc U.interval.left U.interval.right :=
      hpoint.1
    simpa only [hpoint_first] using hmem
  have hvertical :
      |p.2 - U.function.extension p.1| ≤ C_s * delta := by
    simpa only [← hpoint_first, ← hpoint_second,
      C2Function.extension_eq_value] using hpoint.2
  exact ⟨hhorizontal, hvertical⟩

lemma fineOuterShading_volume_le
    {family : Set C2Function} {E₂ : Set (ℝ × ℝ)}
    {K delta t Delta C_R C_s : ℝ}
    (hdelta : 0 < delta)
    (hC_s : 0 ≤ C_s)
    (data : FineRectangleAssignmentData family E₂ K delta t Delta C_R)
    (R : CurvilinearRectangle delta (C_R * t * Delta / delta))
    (U : CurvilinearRectangle
      (C_s * delta) (C_R * t * Delta / delta))
    (hU_function : U.function = R.function)
    (hU_midpoint : U.interval.midpoint = R.interval.midpoint) :
    volume (fineOuterShading data C_s R) ≤
      ENNReal.ofReal
        (2 * C_s * delta *
          Real.sqrt
            (C_s * delta / (C_R * t * Delta / delta))) := by
  have hscaled_nonnegative : 0 ≤ C_s * delta := by positivity
  have hsubset :
      fineOuterShading data C_s R ⊆ U.realCarrier :=
    fineOuterShading_subset_realCarrier
      data R U hU_function hU_midpoint
  calc
    volume (fineOuterShading data C_s R)
        ≤ volume U.realCarrier :=
      measure_mono hsubset
    _ = ENNReal.ofReal
          (2 * (C_s * delta) * U.interval.length) :=
      U.volume_realCarrier hscaled_nonnegative
    _ = ENNReal.ofReal
          (2 * (C_s * delta) *
            Real.sqrt
              (C_s * delta / (C_R * t * Delta / delta))) := by
      rw [U.interval_length]
    _ = ENNReal.ofReal
          (2 * C_s * delta *
            Real.sqrt
              (C_s * delta / (C_R * t * Delta / delta))) := by
      congr 1
      ring

lemma fineOuterShading_union_volume_le
    {family : Set C2Function} {E₂ : Set (ℝ × ℝ)}
    {K delta t Delta C_R C_s : ℝ}
    (hdelta : 0 < delta)
    (hC_s : 0 ≤ C_s)
    (data : FineRectangleAssignmentData family E₂ K delta t Delta C_R)
    (R : RectangleFamily delta (C_R * t * Delta / delta))
    (U_enlarged : Fin R.card →
      CurvilinearRectangle
        (C_s * delta) (C_R * t * Delta / delta))
    (hU_function : ∀ i,
      (U_enlarged i).function = (R.rectangle i).function)
    (hU_midpoint : ∀ i,
      (U_enlarged i).interval.midpoint =
        (R.rectangle i).interval.midpoint) :
    volume
        (⋃ i : Fin R.card,
          fineOuterShading data C_s (R.rectangle i)) ≤
      (R.card : ENNReal) *
        ENNReal.ofReal
          (2 * C_s * delta *
            Real.sqrt
              (C_s * delta / (C_R * t * Delta / delta))) := by
  let area : ENNReal :=
    ENNReal.ofReal
      (2 * C_s * delta *
        Real.sqrt
          (C_s * delta / (C_R * t * Delta / delta)))
  have heach : ∀ i : Fin R.card,
      volume (fineOuterShading data C_s (R.rectangle i)) ≤ area := by
    intro i
    exact fineOuterShading_volume_le
      hdelta hC_s data (R.rectangle i) (U_enlarged i)
      (hU_function i) (hU_midpoint i)
  calc
    volume
        (⋃ i : Fin R.card,
          fineOuterShading data C_s (R.rectangle i))
        ≤ ∑' i : Fin R.card,
            volume (fineOuterShading data C_s (R.rectangle i)) :=
      measure_iUnion_le _
    _ = ∑ i : Fin R.card,
          volume (fineOuterShading data C_s (R.rectangle i)) := by
      rw [tsum_fintype]
    _ ≤ ∑ _i : Fin R.card, area := by
      exact Finset.sum_le_sum fun i _ => heach i
    _ = (R.card : ENNReal) * area := by
      simp [Finset.sum_const]

end Kakeya.Cinematic
