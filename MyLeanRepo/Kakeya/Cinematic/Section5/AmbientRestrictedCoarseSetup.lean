import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedCoarseSetupInputs

/-!
# Coarse grouping inside one fixed ambient bin
-/

namespace Kakeya.Cinematic

theorem ambient_restricted_coarse_setup_at_tangency
    (hCoarseGrouping : CoarseRectangleGroupingStatement)
    (hFineToCoarseCentral : FineToCoarseCentralStatement)
    (hSubfamilySelection : RectangleSubfamilySelectionStatement)
    (hFineTangencyLift : FineTangencyLiftToCoarseStatement)
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K D delta diameter epsilon eta tRep DeltaRep C_R₀ tangency : ℝ}
    (htangency : 5 ≤ tangency)
    (hCompTan : ComparableCoarseTangencyAt K D 100 tangency)
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
    (center : C2Function)
    (hE : MeasurableSet E)
    {C_R C_count C_shading C_volume : ℝ}
    (setup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume)
    (hK : 1 ≤ K)
    (hD : 1 ≤ D)
    (hdelta : 0 < delta)
    (hC_R_large : 9216 * K ^ 2 ≤ C_R)
    (h100_le_C_R : 100 ≤ C_R)
    (hfamily : IsCinematicFamily family K D) :
    ∃ coarseSetup : AmbientRestrictedCoarseSetupData
        data center hE setup,
      coarseSetup.tangency = tangency := by
  have hC_R : 0 < C_R := by linarith
  let arData := ambientRestrictedData data center hE
  have hpointData_I :
      setup.pointData.interval = arData.interval := by
    rw [setup.pointData_interval, arData.assignment_interval]
  rcases coarse_grouping_setup_of_transported_dyadic_data_at_tangency
      hCoarseGrouping hFineToCoarseCentral hSubfamilySelection
      hFineTangencyLift hK hD htangency hCompTan
      hdelta hC_R hC_R_large h100_le_C_R hfamily
      arData setup.pointData hpointData_I
      setup.pointData_center setup.pointData_fiber
      setup.fine setup.fine_nonempty setup.source
      setup.fine_source setup.fine_centers setup.fine_central with
    ⟨coarseData, hcoarse, hfiber⟩
  refine
    ⟨{ coarseData := coarseData
       tangency := tangency
       tangency_ge_five := htangency
       coarse_tangent := hcoarse
       coarse_fiber_card := hfiber }, rfl⟩

theorem ambient_restricted_coarse_setup :
    AmbientRestrictedCoarseSetupStatement := by
  intro hCoarseGrouping hFineToCoarseCentral hSubfamilySelection
    hFineTangencyLift hComparableCoarseTan hTangencyGeom
    family E K D delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_count C_shading C_volume setup
    hK hD hdelta hC_R_large h100_le_C_R hfamily
  rcases hComparableCoarseTan hTangencyGeom
      K D 100 hK hD (by norm_num) with
    ⟨tangency, htangency, hCompTan⟩
  rcases ambient_restricted_coarse_setup_at_tangency
      hCoarseGrouping hFineToCoarseCentral hSubfamilySelection
      hFineTangencyLift htangency hCompTan
      data center hE setup hK hD hdelta hC_R_large
      h100_le_C_R hfamily with
    ⟨coarseSetup, _⟩
  exact ⟨coarseSetup⟩

end Kakeya.Cinematic
