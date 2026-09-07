import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FullGrainThreshold
import MyLeanRepo.Kakeya.Assouad.WZ1.MaximalSeparated
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26IntervalPacking
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma18GoodLineIntervalCover

/-!
# Line-hit full grains for Proposition 6.3

Starting from one cellwise full-grain/Fubini certificate, select a maximal
`2 * rho`-separated finite subset of the actual shaded parameters on its good
line.  The selected parameters cover the line set, while their width-`rho`
scalar slabs are pairwise disjoint.  This gives the multiplicative volume
ledger used in the paper's line-hit-grain selection.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

namespace Proposition63FullGrainFubiniCellData

variable {E : Set Point3} {normal : Point3}
  {rho diameter lineVolume : ℝ} {retainedVolume threshold : ENNReal}

/-- Actual parameters where the selected line meets the good set. -/
def lineParameters
    (data : Proposition63FullGrainFubiniCellData E normal rho diameter
      lineVolume retainedVolume threshold) : Set ℝ :=
  {parameter | data.anchor + parameter • normal ∈ data.good}

theorem lineParameters_measurable
    (data : Proposition63FullGrainFubiniCellData E normal rho diameter
      lineVolume retainedVolume threshold) :
    MeasurableSet data.lineParameters := by
  exact data.good_measurable.preimage (by fun_prop)

theorem lineParameters_volume_lower
    (data : Proposition63FullGrainFubiniCellData E normal rho diameter
      lineVolume retainedVolume threshold) :
    ENNReal.ofReal (lineVolume / (4 * diameter ^ 2)) ≤
      volume data.lineParameters :=
  data.line_volume

theorem lineParameters_subset_interval
    (data : Proposition63FullGrainFubiniCellData E normal rho diameter
      lineVolume retainedVolume threshold)
    (hnormal : ‖normal‖ = 1) :
    data.lineParameters ⊆ Set.Icc (-2 * diameter) (2 * diameter) := by
  intro parameter hparameter
  have hpointBall := data.good_ball hparameter
  have hanchorBall := data.good_ball data.anchor_mem
  have hdistance : dist (data.anchor + parameter • normal) data.anchor ≤
      2 * diameter := by
    calc
      dist (data.anchor + parameter • normal) data.anchor ≤
          dist (data.anchor + parameter • normal) data.center +
            dist data.center data.anchor := dist_triangle _ _ _
      _ ≤ diameter + diameter := by
        gcongr
        · exact hpointBall
        · simpa [dist_comm] using hanchorBall
      _ = 2 * diameter := by ring
  have habs : |parameter| ≤ 2 * diameter := by
    have hdifference :
        data.anchor + parameter • normal - data.anchor =
          parameter • normal := by module
    rw [dist_eq_norm, hdifference, norm_smul, Real.norm_eq_abs, hnormal, mul_one]
      at hdistance
    exact hdistance
  exact ⟨by linarith [abs_le.mp habs |>.1],
    by linarith [abs_le.mp habs |>.2]⟩

/-- A finite separated set of actual good-line parameters, together with its
covering and the two volume inequalities needed for line-hit summation. -/
structure LineHitData
    (data : Proposition63FullGrainFubiniCellData E normal rho diameter
      lineVolume retainedVolume threshold) where
  parameters : Finset ℝ
  parameters_mem : (parameters : Set ℝ) ⊆ data.lineParameters
  parameters_separated :
    ∀ first ∈ parameters, ∀ second ∈ parameters, first ≠ second →
      2 * rho < dist first second
  parameters_cover :
    data.lineParameters ⊆
      ⋃ parameter ∈ parameters, Metric.closedBall parameter (2 * rho)

namespace LineHitData

variable
    (data : Proposition63FullGrainFubiniCellData E normal rho diameter
      lineVolume retainedVolume threshold)

/-- Union of all full scalar grains whose levels are represented by the
selected actual parameters of the good line. -/
def region
    (hit : LineHitData data) : Set Point3 :=
  ⋃ parameter ∈ hit.parameters,
    data.good ∩ {point |
      |inner ℝ point normal -
        inner ℝ (data.anchor + parameter • normal) normal| ≤ rho}

theorem region_measurable
    (hit : LineHitData data) : MeasurableSet hit.region := by
  apply MeasurableSet.biUnion
    (Finset.finite_toSet hit.parameters).countable
  intro parameter _
  exact data.good_measurable.inter <|
    measurableSet_le (by fun_prop) measurable_const

theorem region_subset_good
    (hit : LineHitData data) : hit.region ⊆ data.good := by
  rintro point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨parameter, _, hpointGrain⟩
  exact hpointGrain.1

theorem parameters_volume_cover
    (hit : LineHitData data) (hrho : 0 < rho) :
    volume data.lineParameters ≤
      (hit.parameters.card : ENNReal) * ENNReal.ofReal (4 * rho) := by
  calc
    volume data.lineParameters ≤
        volume (⋃ parameter ∈ hit.parameters,
          Metric.closedBall parameter (2 * rho)) :=
      measure_mono hit.parameters_cover
    _ ≤ ∑ parameter ∈ hit.parameters,
          volume (Metric.closedBall parameter (2 * rho)) :=
      measure_biUnion_finset_le hit.parameters _
    _ = ∑ _parameter ∈ hit.parameters, ENNReal.ofReal (4 * rho) := by
      apply Finset.sum_congr rfl
      intro parameter _
      rw [Real.volume_closedBall]
      congr 1
      ring
    _ = (hit.parameters.card : ENNReal) * ENNReal.ofReal (4 * rho) := by
      simp [Finset.sum_const]

theorem region_volume_lower
    (hit : LineHitData data) :
    (hit.parameters.card : ENNReal) * threshold ≤ volume hit.region := by
  let grain : ℝ → Set Point3 := fun parameter =>
    data.good ∩ {point |
      |inner ℝ point normal -
        inner ℝ (data.anchor + parameter • normal) normal| ≤ rho}
  have hgrainMeasurable : ∀ parameter ∈ hit.parameters,
      MeasurableSet (grain parameter) := by
    intro parameter _
    exact data.good_measurable.inter <|
      measurableSet_le (by fun_prop) measurable_const
  have hgrainDisjoint : Set.PairwiseDisjoint (↑hit.parameters) grain := by
    intro first hfirst second hsecond hne
    change Disjoint (grain first) (grain second)
    rw [Set.disjoint_left]
    intro point hpointFirst hpointSecond
    have hfirstProjection :
        |inner ℝ point normal -
          inner ℝ (data.anchor + first • normal) normal| ≤ rho :=
      hpointFirst.2
    have hsecondProjection :
        |inner ℝ point normal -
          inner ℝ (data.anchor + second • normal) normal| ≤ rho :=
      hpointSecond.2
    have hprojection (parameter : ℝ) :
        inner ℝ (data.anchor + parameter • normal) normal =
          inner ℝ data.anchor normal + parameter := by
      rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
        data.normal_unit]
      norm_num
    have hdistance : dist first second ≤ 2 * rho := by
      rw [Real.dist_eq]
      rw [hprojection first] at hfirstProjection
      rw [hprojection second] at hsecondProjection
      calc
        |first - second| =
            |(inner ℝ point normal - (inner ℝ data.anchor normal + second)) -
              (inner ℝ point normal - (inner ℝ data.anchor normal + first))| := by
                congr 1 <;> ring
        _ ≤ |inner ℝ point normal - (inner ℝ data.anchor normal + second)| +
            |inner ℝ point normal - (inner ℝ data.anchor normal + first)| :=
          abs_sub _ _
        _ ≤ rho + rho := by gcongr
        _ = 2 * rho := by ring
    exact (not_le_of_gt
      (hit.parameters_separated first hfirst second hsecond hne)) hdistance
  have hsum :
      (hit.parameters.card : ENNReal) * threshold ≤
        ∑ parameter ∈ hit.parameters, volume (grain parameter) := by
    calc
      (hit.parameters.card : ENNReal) * threshold =
          ∑ _parameter ∈ hit.parameters, threshold := by
            simp [Finset.sum_const]
      _ ≤ ∑ parameter ∈ hit.parameters, volume (grain parameter) :=
        Finset.sum_le_sum fun parameter hparameter => by
          exact data.full_grain parameter
            (hit.parameters_mem hparameter)
  have hunion :
      volume hit.region =
        ∑ parameter ∈ hit.parameters, volume (grain parameter) := by
    exact measure_biUnion_finset hgrainDisjoint hgrainMeasurable
  rw [hunion]
  exact hsum

theorem line_volume_mul_threshold_le
    (hit : LineHitData data) (hrho : 0 < rho) :
    ENNReal.ofReal (lineVolume / (4 * diameter ^ 2)) * threshold ≤
      ENNReal.ofReal (4 * rho) * volume hit.region := by
  calc
    ENNReal.ofReal (lineVolume / (4 * diameter ^ 2)) * threshold
        ≤ volume data.lineParameters * threshold :=
      mul_le_mul_right' data.lineParameters_volume_lower threshold
    _ ≤ ((hit.parameters.card : ENNReal) * ENNReal.ofReal (4 * rho)) *
          threshold :=
      mul_le_mul_right' (parameters_volume_cover data hit hrho) threshold
    _ = ENNReal.ofReal (4 * rho) *
          ((hit.parameters.card : ENNReal) * threshold) := by ac_rfl
    _ ≤ ENNReal.ofReal (4 * rho) * volume hit.region :=
      mul_le_mul_left' hit.region_volume_lower _

/-- Interval covering of one selected line-hit region from point-centered
covering bounds at actual points of the good line.  This is the metric core
of the Lemma 4.10-to-4.11 passage and is independent of any tube structure. -/
theorem region_interval_covering
    (hit : LineHitData data)
    {tau : ℝ} (hrho : 0 < rho) (htau : 0 < tau)
    (hrhoTau : rho ≤ tau)
    (bound : ENNReal)
    (hlocal : ∀ parameter ∈ data.lineParameters,
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        (scalarProjection normal
          (E ∩ Metric.closedBall
            (data.anchor + parameter • normal) tau))) : ENNReal) ≤
        bound) :
    ∀ intervalCenter : ℝ,
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        (scalarProjection normal hit.region ∩
          Metric.closedBall intervalCenter tau)) : ENNReal) ≤
        4 * (9 * bound) := by
  intro intervalCenter
  let offset := inner ℝ data.anchor normal
  let intervalParameters : Set ℝ :=
    data.lineParameters ∩
      Metric.closedBall (intervalCenter - offset) (2 * tau)
  have hintervalSubset : intervalParameters ⊆
      Metric.closedBall (intervalCenter - offset) (2 * tau) :=
    Set.inter_subset_right
  rcases Kakeya.Assouad.real_subset_self_centered_cover
      htau (by positivity : 0 < 2 * tau) hintervalSubset with
    ⟨selected, hselectedParameters, hselectedCard, hselectedCover⟩
  have hcardNine : (selected.card : ENNReal) ≤ 9 := by
    have hceil : Nat.ceil (4 * (2 * tau) / tau) = 8 := by
      have htauNe : tau ≠ 0 := htau.ne'
      have hratio : 4 * (2 * tau) / tau = (8 : ℝ) := by
        field_simp [htauNe]
        ring
      rw [hratio]
      norm_num
    rw [hceil] at hselectedCard
    norm_num at hselectedCard ⊢
    exact hselectedCard
  let linePoint : ℝ → Point3 := fun parameter =>
    data.anchor + parameter • normal
  let localProjection : ℝ → Set ℝ := fun parameter =>
    scalarProjection normal
      (E ∩ Metric.closedBall (linePoint parameter) tau)
  let sourceSet : Set ℝ :=
    ⋃ parameter ∈ selected, localProjection parameter
  have hlocalCover : ∀ parameter ∈ selected,
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        (localProjection parameter)) : ENNReal) ≤ bound := by
    intro parameter hparameter
    exact hlocal parameter (hselectedParameters hparameter).1
  have hsourceCover :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho) sourceSet) :
          ENNReal) ≤ 9 * bound := by
    have hunion := Kakeya.Assouad.externalCoveringNumber_biUnion_le_card
      (ε := Real.toNNReal rho) (s := selected)
      (A := localProjection) hlocalCover
    exact hunion.trans <| by gcongr
  have htargetSubset :
      scalarProjection normal hit.region ∩
          Metric.closedBall intervalCenter tau ⊆
        Metric.cthickening rho sourceSet := by
    intro value hvalue
    rcases hvalue.1 with ⟨point, hpointRegion, rfl⟩
    rcases Set.mem_iUnion₂.mp hpointRegion with
      ⟨parameter, hparameterSelected, hpointGrain⟩
    have hparameterLine : parameter ∈ data.lineParameters :=
      hit.parameters_mem hparameterSelected
    have hparameterInterval : parameter ∈
        Metric.closedBall (intervalCenter - offset) (2 * tau) := by
      have hvalueInterval := hvalue.2
      rw [Metric.mem_closedBall, Real.dist_eq] at hvalueInterval ⊢
      have hprojection :
          inner ℝ (linePoint parameter) normal = offset + parameter := by
        dsimp only [linePoint, offset]
        rw [inner_add_left, real_inner_smul_left,
          real_inner_self_eq_norm_sq, data.normal_unit]
        norm_num
      have hgrain := hpointGrain.2
      rw [hprojection] at hgrain
      have htriangle :
          |parameter - (intervalCenter - offset)| ≤
            |(offset + parameter) - inner ℝ point normal| +
              |inner ℝ point normal - intervalCenter| := by
        calc
          |parameter - (intervalCenter - offset)| =
              |((offset + parameter) - inner ℝ point normal) +
                (inner ℝ point normal - intervalCenter)| := by ring_nf
          _ ≤ |(offset + parameter) - inner ℝ point normal| +
                |inner ℝ point normal - intervalCenter| := abs_add_le _ _
      calc
        |parameter - (intervalCenter - offset)| ≤
            |(offset + parameter) - inner ℝ point normal| +
              |inner ℝ point normal - intervalCenter| := htriangle
        _ ≤ rho + tau := by
          exact add_le_add (by simpa [abs_sub_comm] using hgrain)
            hvalueInterval
        _ ≤ 2 * tau := by linarith
    have hparameterIn : parameter ∈ intervalParameters :=
      ⟨hparameterLine, hparameterInterval⟩
    rcases Set.mem_iUnion₂.mp (hselectedCover hparameterIn) with
      ⟨selectedParameter, hselectedParameter, hparameterBall⟩
    have hselectedLine : selectedParameter ∈ data.lineParameters :=
      (hselectedParameters hselectedParameter).1
    have hlineBall : linePoint parameter ∈
        Metric.closedBall (linePoint selectedParameter) tau := by
      have hparameterDistance : dist parameter selectedParameter ≤ tau :=
        hparameterBall
      change dist
        (Kakeya.Assouad.wz1Lemma18LinePoint data.anchor normal parameter)
        (Kakeya.Assouad.wz1Lemma18LinePoint data.anchor normal
          selectedParameter) ≤ tau
      rw [Kakeya.Assouad.wz1Lemma18LinePoint_dist data.anchor normal
        parameter selectedParameter data.normal_unit]
      exact hparameterDistance
    let sourceValue := inner ℝ (linePoint parameter) normal
    have hsourceValue : sourceValue ∈ sourceSet := by
      exact Set.mem_iUnion₂.mpr
        ⟨selectedParameter, hselectedParameter,
          ⟨linePoint parameter,
            ⟨data.good_subset hparameterLine, hlineBall⟩, rfl⟩⟩
    have hdistance : dist (inner ℝ point normal) sourceValue ≤ rho := by
      rw [Real.dist_eq]
      simpa [sourceValue, linePoint] using hpointGrain.2
    exact Metric.mem_cthickening_of_dist_le
      (inner ℝ point normal) sourceValue rho sourceSet hsourceValue hdistance
  have hthick := Kakeya.Assouad.externalCoveringNumber_of_subset_cthickening
    hrho hrho htargetSubset hsourceCover
  have hfactor : (2 * Nat.ceil (rho / rho) + 2 : ENNReal) = 4 := by
    have hrhoNe : rho ≠ 0 := hrho.ne'
    have hratio : rho / rho = (1 : ℝ) := by field_simp [hrhoNe]
    rw [hratio]
    norm_num
  simpa only [hfactor] using hthick

end LineHitData

/-- Select the finite separated set of actual line parameters used by the
line-hit-grain argument. -/
theorem exists_lineHitData
    (data : Proposition63FullGrainFubiniCellData E normal rho diameter
      lineVolume retainedVolume threshold)
    (hnormal : ‖normal‖ = 1) (hrho : 0 < rho) (hdiameter : 0 < diameter) :
    Nonempty data.LineHitData := by
  let bound : ℕ := Nat.ceil ((4 * diameter) / (2 * rho) + 1)
  have hfiniteBound : ∀ parameters : Finset ℝ,
      (∀ parameter ∈ parameters, parameter ∈ data.lineParameters) →
      (∀ first ∈ parameters, ∀ second ∈ parameters, first ≠ second →
        2 * rho < dist first second) →
      parameters.card ≤ bound := by
    intro parameters hparameters hseparated
    have hinterval := data.lineParameters_subset_interval hnormal
    have hreal : (parameters.card : ℝ) ≤
        ((2 * diameter) - (-2 * diameter)) / (2 * rho) + 1 :=
      Kakeya.Assouad.real_separated_card_bound (by positivity) (by linarith)
        (fun first hfirst second hsecond hne => by
          simpa [Real.dist_eq] using
            (hseparated first hfirst second hsecond hne).le)
        (fun parameter hparameter =>
          (hinterval (hparameters parameter hparameter)).1)
        (fun parameter hparameter =>
          (hinterval (hparameters parameter hparameter)).2)
    have hreal' : (parameters.card : ℝ) ≤
        (4 * diameter) / (2 * rho) + 1 := by
      convert hreal using 1 <;> ring
    have hceil : (4 * diameter) / (2 * rho) + 1 ≤ (bound : ℝ) :=
      Nat.le_ceil _
    exact_mod_cast hreal'.trans hceil
  rcases Kakeya.Assouad.exists_maximal_separated
      (fun parameter => parameter ∈ data.lineParameters)
      (fun first second => 2 * rho < dist first second)
      (fun {first second} h => by simpa [dist_comm] using h)
      bound hfiniteBound with
    ⟨parameters, hparameters, hseparated, hcover⟩
  have hcover' : data.lineParameters ⊆
      ⋃ parameter ∈ parameters, Metric.closedBall parameter (2 * rho) := by
    intro parameter hparameter
    rcases hcover parameter hparameter with
      ⟨selected, hselected, hequal | hnotSeparated⟩
    · subst parameter
      exact Set.mem_iUnion₂.mpr
        ⟨selected, hselected, by simpa using hrho.le⟩
    · exact Set.mem_iUnion₂.mpr
        ⟨selected, hselected, by
          exact Metric.mem_closedBall.mpr (le_of_not_gt hnotSeparated)⟩
  exact ⟨{
    parameters := parameters
    parameters_mem := hparameters
    parameters_separated := hseparated
    parameters_cover := hcover'
  }⟩

end Proposition63FullGrainFubiniCellData

end Kakeya.Assouad.PureWZ2

end
