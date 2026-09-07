import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedFSVSetupInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicCoarseGrouping

/-!
# Coarse grouping inside one fixed ambient bin

Consume the fine-shading package produced after ambient restriction and run
the transported dyadic coarse-grouping bridge.  The result keeps the exact
fine family, source map, pointwise fibers, and fixed ambient geometry from the
preceding package.
-/

namespace Kakeya.Cinematic

structure AmbientRestrictedCoarseSetupData
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
    (center : C2Function)
    (hE : MeasurableSet E)
    {C_R C_count C_shading C_volume : ℝ}
    (setup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume) where
  coarseData : CoarseRectangleGroupingData
    family (ambientRestrictedSet data center) K
      (ambientRestrictedData data center hE).interval
      delta tRep DeltaRep C_R setup.pointData setup.fine
  tangency : ℝ
  tangency_ge_five : 5 ≤ tangency
  coarse_tangent :
    ∀ j, ∀ f ∈
        (coarseTangentFamily coarseData
          (fun i => setup.pointData.fiber (setup.source i)) j).carrier,
      (coarseData.coarse.rectangle j).IsLambdaTangent f tangency
  coarse_fiber_card :
    ∀ j, (coarseData.fiber j).card ≤ setup.fine.card

def AmbientRestrictedCoarseSetupStatement : Prop :=
  CoarseRectangleGroupingStatement →
    FineToCoarseCentralStatement →
    RectangleSubfamilySelectionStatement →
    FineTangencyLiftToCoarseStatement →
    ComparableCoarseTangencyStatement →
    TangencyGeometryCompletionStatement →
    ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
      {K D delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ},
      ∀ (data : DyadicFineAssignmentData
          family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
        (center : C2Function)
        (hE : MeasurableSet E)
        {C_R C_count C_shading C_volume : ℝ}
        (setup : AmbientRestrictedFSVSetupData
          data center hE C_R C_count C_shading C_volume),
        1 ≤ K →
        1 ≤ D →
        0 < delta →
        9216 * K ^ 2 ≤ C_R →
        100 ≤ C_R →
        IsCinematicFamily family K D →
        Nonempty
          (AmbientRestrictedCoarseSetupData
            data center hE setup)

end Kakeya.Cinematic
