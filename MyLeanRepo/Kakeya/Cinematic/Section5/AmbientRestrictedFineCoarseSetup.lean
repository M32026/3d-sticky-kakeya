import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedCoarseSetup
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedFSVSetupInputs

/-!
# Fine and coarse setup inside one fixed ambient bin

Compose the two closed dependent setup steps so broad callers do not elaborate
their nested existential packages inline.
-/

namespace Kakeya.Cinematic

theorem ambient_restricted_fine_coarse_setup_uniform_tangency
    (hFSV : FineShadingCoverVolumeStatement)
    (hCentered : CenteredRectangleEnlargementStatement)
    (hShading : FineShadingComparisonStatement)
    (hMaximal : MaximalFineRectangleSelectionStatement)
    (hCount : PolynomialScaleCoarseRectangleCountStatement)
    (hComparable : ComparableRectanglesStatement)
    (hTransitivity : ComparabilityTransitivityStatement)
    (hGeometry : AmbientRestrictedFSVGeometryStatement)
    (hCoarseGrouping : CoarseRectangleGroupingStatement)
    (hFineToCoarseCentral : FineToCoarseCentralStatement)
    (hSubfamilySelection : RectangleSubfamilySelectionStatement)
    (hFineTangencyLift : FineTangencyLiftToCoarseStatement)
    (hComparableCoarseTan : ComparableCoarseTangencyStatement)
    (hTangencyGeometry : TangencyGeometryCompletionStatement)
    (K D T C_R₀ : ℝ)
    (hK : 1 ≤ K) (hD : 1 ≤ D) (hT : 1 ≤ T)
    (hC_R₀ : 0 < C_R₀) :
    ∃ tangency C_R C_count C_shading C_volume : ℝ,
      5 ≤ tangency ∧
      C_R₀ ≤ C_R ∧
      100 ≤ C_R ∧
      0 < C_count ∧
      100 ≤ C_shading ∧
      100 ≤ C_volume ∧
      ∃ delta₀ : ℝ,
        0 < delta₀ ∧
        delta₀ ≤ 1 ∧
        ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
          {delta diameter epsilon eta tRep DeltaRep : ℝ},
          ∀ (data : DyadicFineAssignmentData
              family E K delta diameter epsilon eta
                tRep DeltaRep C_R₀)
            (center : C2Function)
            (hfamily : IsCinematicFamily family K D)
            (hE : MeasurableSet E),
            (ambientRestrictedSet data center).Nonempty →
            0 < delta →
            delta ≤ delta₀ →
            tRep ≤ T →
            9216 * K ^ 2 ≤ C_R →
            ∃ fineSetup : AmbientRestrictedFSVSetupData
                data center hE C_R C_count C_shading C_volume,
              ∃ coarseSetup : AmbientRestrictedCoarseSetupData
                  data center hE fineSetup,
                coarseSetup.tangency = tangency := by
  rcases hComparableCoarseTan hTangencyGeometry
      K D 100 hK hD (by norm_num) with
    ⟨tangency, htangency, hCompTan⟩
  rcases hFSV hCentered hShading hMaximal hCount
      hComparable hTransitivity K D T C_R₀ hK hD hT hC_R₀ with
    ⟨C_R, C_count, C_shading, C_volume,
      hC_R₀_le, hC_R_large, hC_count,
      hC_shading, hC_volume,
      delta₀, hdelta₀, hdelta₀_one, hmain⟩
  refine
    ⟨tangency, C_R, C_count, C_shading, C_volume,
      htangency, hC_R₀_le, hC_R_large, hC_count,
      hC_shading, hC_volume,
      delta₀, hdelta₀, hdelta₀_one, ?_⟩
  intro family E delta diameter epsilon eta tRep DeltaRep
    data center hfamily hE hbin hdelta hdelta₀ htRep hC_R
  let E₂ := ambientRestrictedSet data center
  let data₀ := (ambientRestrictedData data center hE).assignment
  rcases hmain hfamily hbin hdelta hdelta₀
      data.delta_le_DeltaRep data.DeltaRep_le_tRep htRep data₀ with
    ⟨pointData, hpointData_interval, hpointData_center,
      hpointData_fiber, fine, source, hfine_nonempty,
      hfine_source, hfine_centers, hfine_central,
      hfine_incomparable, hfine_card, enlarged,
      henlarged_function, henlarged_midpoint,
      hbin_cover, hbin_volume⟩
  have hC_R_one : 1 ≤ C_R := by linarith
  have hfixed :=
    hGeometry (data := data) hdelta center hE pointData
      hpointData_fiber hC_R_one
  let fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume :=
    { pointData := pointData
      fine := fine
      source := source
      enlarged := enlarged
      pointData_interval := hpointData_interval
      pointData_center := hpointData_center
      pointData_fiber := hpointData_fiber
      fine_nonempty := hfine_nonempty
      fine_source := hfine_source
      fine_centers := hfine_centers
      fine_central := hfine_central
      fine_incomparable := hfine_incomparable
      fine_card := hfine_card
      enlarged_function := henlarged_function
      enlarged_midpoint := henlarged_midpoint
      bin_cover := hbin_cover
      bin_volume := hbin_volume
      point_fiber_ambient := hfixed.1
      fixed_ambient_diameter := hfixed.2 }
  rcases ambient_restricted_coarse_setup_at_tangency
      hCoarseGrouping hFineToCoarseCentral hSubfamilySelection
      hFineTangencyLift htangency hCompTan
      data center hE fineSetup hK hD hdelta hC_R hC_R_large
      hfamily with
    ⟨coarseSetup, hcoarseTangency⟩
  exact ⟨fineSetup, coarseSetup, hcoarseTangency⟩

theorem ambient_restricted_fine_coarse_setup
    (hFSV : FineShadingCoverVolumeStatement)
    (hCentered : CenteredRectangleEnlargementStatement)
    (hShading : FineShadingComparisonStatement)
    (hMaximal : MaximalFineRectangleSelectionStatement)
    (hCount : PolynomialScaleCoarseRectangleCountStatement)
    (hComparable : ComparableRectanglesStatement)
    (hTransitivity : ComparabilityTransitivityStatement)
    (hGeometry : AmbientRestrictedFSVGeometryStatement)
    (hCoarseGrouping : CoarseRectangleGroupingStatement)
    (hFineToCoarseCentral : FineToCoarseCentralStatement)
    (hSubfamilySelection : RectangleSubfamilySelectionStatement)
    (hFineTangencyLift : FineTangencyLiftToCoarseStatement)
    (hComparableCoarseTan : ComparableCoarseTangencyStatement)
    (hTangencyGeometry : TangencyGeometryCompletionStatement)
    (K D T C_R₀ : ℝ)
    (hK : 1 ≤ K) (hD : 1 ≤ D) (hT : 1 ≤ T)
    (hC_R₀ : 0 < C_R₀) :
    ∃ C_R C_count C_shading C_volume : ℝ,
      C_R₀ ≤ C_R ∧
      100 ≤ C_R ∧
      0 < C_count ∧
      100 ≤ C_shading ∧
      100 ≤ C_volume ∧
      ∃ delta₀ : ℝ,
        0 < delta₀ ∧
        delta₀ ≤ 1 ∧
        ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
          {delta diameter epsilon eta tRep DeltaRep : ℝ},
          ∀ (data : DyadicFineAssignmentData
              family E K delta diameter epsilon eta
                tRep DeltaRep C_R₀)
            (center : C2Function)
            (hfamily : IsCinematicFamily family K D)
            (hE : MeasurableSet E),
            (ambientRestrictedSet data center).Nonempty →
            0 < delta →
            delta ≤ delta₀ →
            tRep ≤ T →
            9216 * K ^ 2 ≤ C_R →
            ∃ fineSetup : AmbientRestrictedFSVSetupData
                data center hE C_R C_count C_shading C_volume,
              Nonempty
                (AmbientRestrictedCoarseSetupData
                  data center hE fineSetup) := by
  rcases hFSV hCentered hShading hMaximal hCount
      hComparable hTransitivity K D T C_R₀ hK hD hT hC_R₀ with
    ⟨C_R, C_count, C_shading, C_volume,
      hC_R₀_le, hC_R_large, hC_count,
      hC_shading, hC_volume,
      delta₀, hdelta₀, hdelta₀_one, hmain⟩
  refine
    ⟨C_R, C_count, C_shading, C_volume,
      hC_R₀_le, hC_R_large, hC_count,
      hC_shading, hC_volume,
      delta₀, hdelta₀, hdelta₀_one, ?_⟩
  intro family E delta diameter epsilon eta tRep DeltaRep
    data center hfamily hE hbin hdelta hdelta₀ htRep hC_R
  let E₂ := ambientRestrictedSet data center
  let data₀ := (ambientRestrictedData data center hE).assignment
  rcases hmain hfamily hbin hdelta hdelta₀
      data.delta_le_DeltaRep data.DeltaRep_le_tRep htRep data₀ with
    ⟨pointData, hpointData_interval, hpointData_center,
      hpointData_fiber, fine, source, hfine_nonempty,
      hfine_source, hfine_centers, hfine_central,
      hfine_incomparable, hfine_card, enlarged,
      henlarged_function, henlarged_midpoint,
      hbin_cover, hbin_volume⟩
  have hC_R_one : 1 ≤ C_R := by
    linarith
  have hfixed :=
    hGeometry (data := data) hdelta center hE pointData
      hpointData_fiber hC_R_one
  let fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume :=
    { pointData := pointData
      fine := fine
      source := source
      enlarged := enlarged
      pointData_interval := hpointData_interval
      pointData_center := hpointData_center
      pointData_fiber := hpointData_fiber
      fine_nonempty := hfine_nonempty
      fine_source := hfine_source
      fine_centers := hfine_centers
      fine_central := hfine_central
      fine_incomparable := hfine_incomparable
      fine_card := hfine_card
      enlarged_function := henlarged_function
      enlarged_midpoint := henlarged_midpoint
      bin_cover := hbin_cover
      bin_volume := hbin_volume
      point_fiber_ambient := hfixed.1
      fixed_ambient_diameter := hfixed.2 }
  exact
    ⟨fineSetup,
      ambient_restricted_coarse_setup
        hCoarseGrouping hFineToCoarseCentral hSubfamilySelection
        hFineTangencyLift hComparableCoarseTan hTangencyGeometry
        data center hE fineSetup
        hK hD hdelta hC_R hC_R_large hfamily⟩

end Kakeya.Cinematic
