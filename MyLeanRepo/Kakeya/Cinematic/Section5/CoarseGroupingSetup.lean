import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ShiftedTangency
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulAssemblyInputs

attribute [local instance] Classical.propDecidable

/-!
# Coarse grouping and tangent fibers

This module constructs the coarse grouping of a selected fine rectangle
family and transfers each rectangle-dependent tangent family to its coarse
parent at one uniform tangency constant.
-/

namespace Kakeya.Cinematic

/-- The union of the fine tangent families assigned to one coarse parent. -/
def coarseTangentFamily
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (H : Fin fine.card → FiniteFunctionFamily)
    (j : Fin data.coarse.card) : FiniteFunctionFamily :=
  { carrier :=
      (Finset.biUnion (data.fiber j) fun i => (H i).toFinset :
        Finset C2Function)
    finite := Set.toFinite _ }

/-- Construct a coarse rectangle grouping and transfer all fine tangent
families to their coarse parents. -/
lemma coarse_grouping_setup_at_tangency
    (hCoarseGrouping : CoarseRectangleGroupingStatement)
    (hFineToCoarseCentral : FineToCoarseCentralStatement)
    (hSubfamilySelection : RectangleSubfamilySelectionStatement)
    (hFineTangencyLift : FineTangencyLiftToCoarseStatement)
    {K D delta t Delta C_R tangency : ℝ}
    (hK : 1 ≤ K)
    (hD : 1 ≤ D)
    (htangency : 5 ≤ tangency)
    (hCompTan : ComparableCoarseTangencyAt K D 100 tangency)
    (hdelta_pos : 0 < delta)
    (hdelta_le_Delta : delta ≤ Delta)
    (hDelta_le_t : Delta ≤ t)
    (ht_pos : 0 < t)
    (hC_R_pos : 0 < C_R)
    (hC_R_large : 9216 * K ^ 2 ≤ C_R)
    (hAdmissibleComp :
      IsAdmissibleComparisonScale Delta (C_R * t) 100)
    {family : Set C2Function}
    (hfamily : IsCinematicFamily family K D)
    {I : ParameterInterval}
    (hI : I.IsControlled K)
    {E₂ : Set (ℝ × ℝ)}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    (hpointData_I : pointData.interval = I)
    (fine : RectangleFamily delta (C_R * t * Delta / delta))
    (hfine_nonempty : fine.Nonempty)
    (source : Fin fine.card → E₂)
    (hfine_eq_source :
      ∀ i, fine.rectangle i = pointData.rectangle (source i))
    (hfine_centers : fine.CentersIn family)
    (hfine_central : fine.IsOverCentralQuarterOf I)
    (H : Fin fine.card → FiniteFunctionFamily)
    (hH_sub : ∀ i, (H i).carrier ⊆ family)
    (hH_tangent5 : ∀ i, ∀ f ∈ (H i).carrier,
      (fine.rectangle i).IsLambdaTangent f 5)
    (hH_dist : ∀ i, ∀ f ∈ (H i).carrier,
      c2Distance f (fine.rectangle i).function ≤ 6 * t)
    (hH_tang_param : ∀ i, ∀ f ∈ (H i).carrier,
      tangencyParameterOn I f (fine.rectangle i).function ≤ Delta) :
    ∃ data : CoarseRectangleGroupingData
        family E₂ K I delta t Delta C_R pointData fine,
      (∀ j, ∀ f ∈ (coarseTangentFamily data H j).carrier,
        (data.coarse.rectangle j).IsLambdaTangent f tangency) ∧
      ∀ j, (data.fiber j).card ≤ fine.card := by
  obtain ⟨data⟩ :=
    hCoarseGrouping hFineToCoarseCentral hSubfamilySelection
      (K := K) (delta := delta) (t := t) (Delta := Delta)
      (C_R := C_R) hK hdelta_pos hdelta_le_Delta hDelta_le_t
      ht_pos hC_R_pos hC_R_large hI pointData hpointData_I fine
      hfine_nonempty source hfine_eq_source hfine_centers
  have h_tangency :
      ∀ j, ∀ f ∈ (coarseTangentFamily data H j).carrier,
        (data.coarse.rectangle j).IsLambdaTangent f tangency := by
    intro j f hf
    have h_exists :
        ∃ i ∈ data.fiber j, f ∈ (H i).carrier := by
      have hf' :
          f ∈ Finset.biUnion (data.fiber j) (fun i => (H i).toFinset) := by
        simpa [coarseTangentFamily] using hf
      rcases Finset.mem_biUnion.mp hf' with ⟨i, hi, hfi⟩
      exact ⟨i, hi, by
        simpa [FiniteFunctionFamily.toFinset] using hfi⟩
    rcases h_exists with ⟨i, hi, hfi⟩
    have hparent : data.parent i = j := by
      simpa [CoarseRectangleGroupingData.fiber] using hi
    let center := (fine.rectangle i).function
    have h_enlarged_tangent :
        (data.enlarged i).IsLambdaTangent f 5 :=
      hFineTangencyLift hK hD hdelta_pos hdelta_le_Delta
        hDelta_le_t ht_pos hC_R_pos hC_R_large
        hfamily hI (R := fine.rectangle i) (S := data.enlarged i)
        (hfine_central i) (data.enlarged_function i)
        (data.enlarged_midpoint i) (data.fine_subset_enlarged i)
        (f := f) (k := center) rfl (hfine_centers i)
        (hH_sub i hfi) (hH_dist i f hfi)
        (hH_tang_param i f hfi) (hH_tangent5 i f hfi)
    rcases data.parent_relation i with heq | hcomp
    · rw [hparent] at heq
      have h_up :
          (data.enlarged i).IsLambdaTangent f tangency :=
        h_enlarged_tangent.mono
          (lt_of_lt_of_le hdelta_pos hdelta_le_Delta).le
          (by linarith)
      simpa [heq] using h_up
    · rw [hparent] at hcomp
      have hC_R_ge_one : 1 ≤ C_R := by
        nlinarith [sq_nonneg K]
      have hDelta_le_CRt : Delta ≤ C_R * t := by
        calc
          Delta ≤ t := hDelta_le_t
          _ = 1 * t := by ring
          _ ≤ C_R * t := by gcongr
      exact hCompTan hfamily hI
        (lt_of_lt_of_le hdelta_pos hdelta_le_Delta)
        hDelta_le_CRt hAdmissibleComp
        (R := data.enlarged i) (S := data.coarse.rectangle j)
        (by simpa [data.enlarged_function i] using hfine_centers i)
        (data.coarse_centers j) (data.enlarged_central i)
        (data.coarse_central j) hcomp (f := f) (hH_sub i hfi)
        h_enlarged_tangent
  have h_fiber_bound :
      ∀ j, (data.fiber j).card ≤ fine.card := by
    intro j
    calc
      (data.fiber j).card ≤
          (Finset.univ : Finset (Fin fine.card)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = fine.card := Finset.card_fin fine.card
  exact ⟨data, h_tangency, h_fiber_bound⟩

lemma coarse_grouping_setup
    (hCoarseGrouping : CoarseRectangleGroupingStatement)
    (hFineToCoarseCentral : FineToCoarseCentralStatement)
    (hSubfamilySelection : RectangleSubfamilySelectionStatement)
    (hFineTangencyLift : FineTangencyLiftToCoarseStatement)
    (hComparableCoarseTan : ComparableCoarseTangencyStatement)
    (hTangencyGeom : TangencyGeometryCompletionStatement)
    {K D delta t Delta C_R : ℝ}
    (hK : 1 ≤ K)
    (hD : 1 ≤ D)
    (hdelta_pos : 0 < delta)
    (hdelta_le_Delta : delta ≤ Delta)
    (hDelta_le_t : Delta ≤ t)
    (ht_pos : 0 < t)
    (hC_R_pos : 0 < C_R)
    (hC_R_large : 9216 * K ^ 2 ≤ C_R)
    (hAdmissibleComp :
      IsAdmissibleComparisonScale Delta (C_R * t) 100)
    {family : Set C2Function}
    (hfamily : IsCinematicFamily family K D)
    {I : ParameterInterval}
    (hI : I.IsControlled K)
    {E₂ : Set (ℝ × ℝ)}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    (hpointData_I : pointData.interval = I)
    (fine : RectangleFamily delta (C_R * t * Delta / delta))
    (hfine_nonempty : fine.Nonempty)
    (source : Fin fine.card → E₂)
    (hfine_eq_source :
      ∀ i, fine.rectangle i = pointData.rectangle (source i))
    (hfine_centers : fine.CentersIn family)
    (hfine_central : fine.IsOverCentralQuarterOf I)
    (H : Fin fine.card → FiniteFunctionFamily)
    (hH_sub : ∀ i, (H i).carrier ⊆ family)
    (hH_tangent5 : ∀ i, ∀ f ∈ (H i).carrier,
      (fine.rectangle i).IsLambdaTangent f 5)
    (hH_dist : ∀ i, ∀ f ∈ (H i).carrier,
      c2Distance f (fine.rectangle i).function ≤ 6 * t)
    (hH_tang_param : ∀ i, ∀ f ∈ (H i).carrier,
      tangencyParameterOn I f (fine.rectangle i).function ≤ Delta) :
    ∃ (data : CoarseRectangleGroupingData
          family E₂ K I delta t Delta C_R pointData fine)
      (tangency : ℝ),
      5 ≤ tangency ∧
      (∀ j, ∀ f ∈ (coarseTangentFamily data H j).carrier,
        (data.coarse.rectangle j).IsLambdaTangent f tangency) ∧
      ∀ j, (data.fiber j).card ≤ fine.card := by
  obtain ⟨tangency, htangency_ge5, hCompTan⟩ :=
    hComparableCoarseTan hTangencyGeom K D 100 hK hD (by norm_num)
  rcases coarse_grouping_setup_at_tangency
      hCoarseGrouping hFineToCoarseCentral hSubfamilySelection
      hFineTangencyLift hK hD htangency_ge5 hCompTan
      hdelta_pos hdelta_le_Delta hDelta_le_t ht_pos
      hC_R_pos hC_R_large hAdmissibleComp hfamily hI
      hpointData_I fine hfine_nonempty source hfine_eq_source
      hfine_centers hfine_central H hH_sub hH_tangent5
      hH_dist hH_tang_param with
    ⟨data, h_tangency, h_fiber_bound⟩
  exact
    ⟨data, tangency, htangency_ge5,
      h_tangency, h_fiber_bound⟩

end Kakeya.Cinematic
