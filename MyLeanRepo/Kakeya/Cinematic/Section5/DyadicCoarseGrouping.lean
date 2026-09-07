import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseGroupingSetup
import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicFineAssignmentData

/-!
# Coarse grouping from pointwise dyadic two-ends data

This wrapper feeds the pointwise distance and tangency bounds stored in
`DyadicFineAssignmentData` into the closed coarse-grouping construction.
No common exact fiber or common exact center is assumed.
-/

noncomputable section

namespace Kakeya.Cinematic

lemma coarse_grouping_setup_of_dyadic_data
    (hCoarseGrouping : CoarseRectangleGroupingStatement)
    (hFineToCoarseCentral : FineToCoarseCentralStatement)
    (hSubfamilySelection : RectangleSubfamilySelectionStatement)
    (hFineTangencyLift : FineTangencyLiftToCoarseStatement)
    (hComparableCoarseTan : ComparableCoarseTangencyStatement)
    (hTangencyGeom : TangencyGeometryCompletionStatement)
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K D delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (hK : 1 ≤ K)
    (hD : 1 ≤ D)
    (hdelta : 0 < delta)
    (hC_R : 0 < C_R)
    (hC_R_large : 9216 * K^2 ≤ C_R)
    (hAdmissible :
      IsAdmissibleComparisonScale DeltaRep (C_R * tRep) 100)
    (hfamily : IsCinematicFamily family K D)
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)
    (fine : RectangleFamily
      delta (C_R * tRep * DeltaRep / delta))
    (hfine_nonempty : fine.Nonempty)
    (source : Fin fine.card → E)
    (hfine_eq_source :
      ∀ i, fine.rectangle i = data.assignment.rectangle (source i))
    (hfine_centers : fine.CentersIn family)
    (hfine_central :
      fine.IsOverCentralQuarterOf data.interval) :
    ∃ (coarseData : CoarseRectangleGroupingData
          family E K data.interval delta tRep DeltaRep C_R
          data.assignment fine)
      (tangency : ℝ),
      5 ≤ tangency ∧
      (∀ j, ∀ f ∈
          (coarseTangentFamily coarseData
            (fun i => data.assignment.fiber (source i)) j).carrier,
        (coarseData.coarse.rectangle j).IsLambdaTangent f tangency) ∧
      ∀ j, (coarseData.fiber j).card ≤ fine.card := by
  let H : Fin fine.card → FiniteFunctionFamily :=
    fun i => data.assignment.fiber (source i)
  have hH_sub : ∀ i, (H i).carrier ⊆ family := by
    intro i
    exact data.assignment.fiber_subset (source i)
  have hH_tangent :
      ∀ i, ∀ f ∈ (H i).carrier,
        (fine.rectangle i).IsLambdaTangent f 5 := by
    intro i f hf
    rw [hfine_eq_source i]
    exact data.assignment.fiber_tangent (source i) f hf
  have hH_dist :
      ∀ i, ∀ f ∈ (H i).carrier,
        c2Distance f (fine.rectangle i).function ≤ 6 * tRep := by
    intro i f hf
    rw [hfine_eq_source i, data.assignment.rectangle_function]
    exact data.fiber_dist_le_six_representative
      hdelta (source i) f hf
  have hH_tangency :
      ∀ i, ∀ f ∈ (H i).carrier,
        tangencyParameterOn data.interval f
          (fine.rectangle i).function ≤ DeltaRep := by
    intro i f hf
    rw [hfine_eq_source i, data.assignment.rectangle_function]
    exact data.fiber_tangency_le_representative
      (source i) f hf
  have hI : data.interval.IsControlled K := by
    rw [← data.assignment_interval]
    exact data.assignment.intervalControlled
  rcases coarse_grouping_setup
      hCoarseGrouping hFineToCoarseCentral hSubfamilySelection
      hFineTangencyLift hComparableCoarseTan hTangencyGeom
      hK hD hdelta data.delta_le_DeltaRep data.DeltaRep_le_tRep
      data.tRep_pos hC_R hC_R_large
      hAdmissible hfamily hI data.assignment_interval
      fine hfine_nonempty source hfine_eq_source
      hfine_centers hfine_central H hH_sub hH_tangent
      hH_dist hH_tangency with
    ⟨coarseData, tangency, htangency, hcoarse, hfiber⟩
  exact ⟨coarseData, tangency, htangency, hcoarse, hfiber⟩

/--
Feed a transported fine assignment into coarse grouping while reusing the
pointwise distance and tangency certificates stored in the original dyadic
data. This is the bridge used after fine-shading cover enlarges `C_R` without
changing the interval, centers, or fibers.
-/
lemma coarse_grouping_setup_of_transported_dyadic_data_at_tangency
    (hCoarseGrouping : CoarseRectangleGroupingStatement)
    (hFineToCoarseCentral : FineToCoarseCentralStatement)
    (hSubfamilySelection : RectangleSubfamilySelectionStatement)
    (hFineTangencyLift : FineTangencyLiftToCoarseStatement)
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K D delta diameter epsilon eta tRep DeltaRep C_R₀ C_R tangency : ℝ}
    (hK : 1 ≤ K)
    (hD : 1 ≤ D)
    (htangency : 5 ≤ tangency)
    (hCompTan : ComparableCoarseTangencyAt K D 100 tangency)
    (hdelta : 0 < delta)
    (hC_R : 0 < C_R)
    (hC_R_large : 9216 * K ^ 2 ≤ C_R)
    (h100_le_C_R : 100 ≤ C_R)
    (hfamily : IsCinematicFamily family K D)
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
    (pointData :
      FineRectangleAssignmentData
        family E K delta tRep DeltaRep C_R)
    (hpointData_I : pointData.interval = data.interval)
    (hpointData_center :
      ∀ p, pointData.center p = data.assignment.center p)
    (hpointData_fiber :
      ∀ p, pointData.fiber p = data.assignment.fiber p)
    (fine : RectangleFamily
      delta (C_R * tRep * DeltaRep / delta))
    (hfine_nonempty : fine.Nonempty)
    (source : Fin fine.card → E)
    (hfine_eq_source :
      ∀ i, fine.rectangle i = pointData.rectangle (source i))
    (hfine_centers : fine.CentersIn family)
    (hfine_central :
      fine.IsOverCentralQuarterOf pointData.interval) :
    ∃ coarseData : CoarseRectangleGroupingData
        family E K data.interval delta tRep DeltaRep C_R pointData fine,
      (∀ j, ∀ f ∈
          (coarseTangentFamily coarseData
            (fun i => pointData.fiber (source i)) j).carrier,
        (coarseData.coarse.rectangle j).IsLambdaTangent f tangency) ∧
      ∀ j, (coarseData.fiber j).card ≤ fine.card := by
  let H : Fin fine.card → FiniteFunctionFamily :=
    fun i => pointData.fiber (source i)
  have hH_sub : ∀ i, (H i).carrier ⊆ family := by
    intro i
    exact pointData.fiber_subset (source i)
  have hH_tangent :
      ∀ i, ∀ f ∈ (H i).carrier,
        (fine.rectangle i).IsLambdaTangent f 5 := by
    intro i f hf
    rw [hfine_eq_source i]
    exact pointData.fiber_tangent (source i) f hf
  have hH_dist :
      ∀ i, ∀ f ∈ (H i).carrier,
        c2Distance f (fine.rectangle i).function ≤ 6 * tRep := by
    intro i f hf
    have hf_old :
        f ∈ (data.assignment.fiber (source i)).carrier := by
      rw [← hpointData_fiber (source i)]
      exact hf
    rw [hfine_eq_source i, pointData.rectangle_function,
      hpointData_center (source i)]
    exact data.fiber_dist_le_six_representative
      hdelta (source i) f hf_old
  have hH_tangency :
      ∀ i, ∀ f ∈ (H i).carrier,
        tangencyParameterOn data.interval f
          (fine.rectangle i).function ≤ DeltaRep := by
    intro i f hf
    have hf_old :
        f ∈ (data.assignment.fiber (source i)).carrier := by
      rw [← hpointData_fiber (source i)]
      exact hf
    rw [hfine_eq_source i, pointData.rectangle_function,
      hpointData_center (source i)]
    exact data.fiber_tangency_le_representative
      (source i) f hf_old
  have hI : data.interval.IsControlled K := by
    rw [← data.assignment_interval]
    exact data.assignment.intervalControlled
  have hAdmissible :
      IsAdmissibleComparisonScale DeltaRep (C_R * tRep) 100 := by
    constructor
    · norm_num
    · calc
        100 * DeltaRep ≤ 100 * tRep :=
          mul_le_mul_of_nonneg_left
            data.DeltaRep_le_tRep (by norm_num)
        _ ≤ C_R * tRep :=
          mul_le_mul_of_nonneg_right
            h100_le_C_R data.tRep_pos.le
  have hfine_central' :
      fine.IsOverCentralQuarterOf data.interval := by
    rw [← hpointData_I]
    exact hfine_central
  exact coarse_grouping_setup_at_tangency
    hCoarseGrouping hFineToCoarseCentral hSubfamilySelection
    hFineTangencyLift hK hD htangency hCompTan
    hdelta data.delta_le_DeltaRep data.DeltaRep_le_tRep
    data.tRep_pos hC_R hC_R_large hAdmissible hfamily hI
    hpointData_I fine hfine_nonempty source hfine_eq_source
    hfine_centers hfine_central' H hH_sub hH_tangent
    hH_dist hH_tangency

lemma coarse_grouping_setup_of_transported_dyadic_data
    (hCoarseGrouping : CoarseRectangleGroupingStatement)
    (hFineToCoarseCentral : FineToCoarseCentralStatement)
    (hSubfamilySelection : RectangleSubfamilySelectionStatement)
    (hFineTangencyLift : FineTangencyLiftToCoarseStatement)
    (hComparableCoarseTan : ComparableCoarseTangencyStatement)
    (hTangencyGeom : TangencyGeometryCompletionStatement)
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K D delta diameter epsilon eta tRep DeltaRep C_R₀ C_R : ℝ}
    (hK : 1 ≤ K)
    (hD : 1 ≤ D)
    (hdelta : 0 < delta)
    (hC_R : 0 < C_R)
    (hC_R_large : 9216 * K ^ 2 ≤ C_R)
    (h100_le_C_R : 100 ≤ C_R)
    (hfamily : IsCinematicFamily family K D)
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
    (pointData :
      FineRectangleAssignmentData
        family E K delta tRep DeltaRep C_R)
    (hpointData_I : pointData.interval = data.interval)
    (hpointData_center :
      ∀ p, pointData.center p = data.assignment.center p)
    (hpointData_fiber :
      ∀ p, pointData.fiber p = data.assignment.fiber p)
    (fine : RectangleFamily
      delta (C_R * tRep * DeltaRep / delta))
    (hfine_nonempty : fine.Nonempty)
    (source : Fin fine.card → E)
    (hfine_eq_source :
      ∀ i, fine.rectangle i = pointData.rectangle (source i))
    (hfine_centers : fine.CentersIn family)
    (hfine_central :
      fine.IsOverCentralQuarterOf pointData.interval) :
    ∃ (coarseData : CoarseRectangleGroupingData
          family E K data.interval delta tRep DeltaRep C_R
          pointData fine)
      (tangency : ℝ),
      5 ≤ tangency ∧
      (∀ j, ∀ f ∈
          (coarseTangentFamily coarseData
            (fun i => pointData.fiber (source i)) j).carrier,
        (coarseData.coarse.rectangle j).IsLambdaTangent f tangency) ∧
      ∀ j, (coarseData.fiber j).card ≤ fine.card := by
  rcases hComparableCoarseTan hTangencyGeom
      K D 100 hK hD (by norm_num) with
    ⟨tangency, htangency, hCompTan⟩
  rcases coarse_grouping_setup_of_transported_dyadic_data_at_tangency
      hCoarseGrouping hFineToCoarseCentral hSubfamilySelection
      hFineTangencyLift hK hD htangency hCompTan
      hdelta hC_R hC_R_large h100_le_C_R hfamily data
      pointData hpointData_I hpointData_center hpointData_fiber
      fine hfine_nonempty source hfine_eq_source
      hfine_centers hfine_central with
    ⟨coarseData, hcoarse, hfiber⟩
  exact ⟨coarseData, tangency, htangency, hcoarse, hfiber⟩

end Kakeya.Cinematic
