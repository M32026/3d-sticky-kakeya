import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedFSVGeometryInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.FineShadingCoverVolumeInputs

/-!
# Fine-shading setup inside one fixed ambient bin

The paper first restricts the dyadic pointwise data to one ambient bin and
only then runs the fine-shading cover.  This package retains every FSV witness
and immediately records that the transported pointwise fibers remain inside
the same fixed ambient family.
-/

open MeasureTheory

namespace Kakeya.Cinematic

structure AmbientRestrictedFSVSetupData
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
    (center : C2Function)
    (hE : MeasurableSet E)
    (C_R C_count C_shading C_volume : ℝ) where
  pointData : FineRectangleAssignmentData
    family (ambientRestrictedSet data center)
      K delta tRep DeltaRep C_R
  fine : RectangleFamily delta (C_R * tRep * DeltaRep / delta)
  source : Fin fine.card → ambientRestrictedSet data center
  enlarged : Fin fine.card →
    CurvilinearRectangle
      (C_shading * delta) (C_R * tRep * DeltaRep / delta)
  pointData_interval :
    pointData.interval =
      (ambientRestrictedData data center hE).assignment.interval
  pointData_center : ∀ p,
    pointData.center p =
      (ambientRestrictedData data center hE).assignment.center p
  pointData_fiber : ∀ p,
    pointData.fiber p =
      (ambientRestrictedData data center hE).assignment.fiber p
  fine_nonempty : fine.Nonempty
  fine_source : ∀ i, fine.rectangle i = pointData.rectangle (source i)
  fine_centers : fine.CentersIn family
  fine_central : fine.IsOverCentralQuarterOf pointData.interval
  fine_incomparable : fine.IsPairwiseIncomparable family 100
  fine_card :
    (fine.card : ℝ) ≤ Real.rpow delta (-C_count)
  enlarged_function : ∀ i,
    (enlarged i).function = (fine.rectangle i).function
  enlarged_midpoint : ∀ i,
    (enlarged i).interval.midpoint =
      (fine.rectangle i).interval.midpoint
  bin_cover :
    ambientRestrictedSet data center ⊆
      ⋃ i, (enlarged i).realCarrier
  bin_volume :
    volume (ambientRestrictedSet data center) ≤
      (fine.card : ENNReal) *
        ENNReal.ofReal
          (2 * C_volume * delta ^ 2 /
            Real.sqrt (C_R * tRep * DeltaRep))
  point_fiber_ambient : ∀ p,
    (pointData.fiber p).carrier ⊆
      (data.ambientSource.cluster center (3 * tRep)).carrier
  fixed_ambient_diameter :
    ∀ f ∈ (data.ambientSource.cluster center (3 * tRep)).carrier,
      ∀ g ∈ (data.ambientSource.cluster center (3 * tRep)).carrier,
        dist f g ≤ 6 * (C_R * tRep)

def AmbientRestrictedFSVSetupStatement : Prop :=
  FineShadingCoverVolumeStatement →
    AmbientRestrictedFSVGeometryStatement →
    ∀ K D T C_R₀ : ℝ,
      1 ≤ K →
      1 ≤ D →
      1 ≤ T →
      0 < C_R₀ →
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
              (center : C2Function),
              ∀ (hfamily : IsCinematicFamily family K D)
                (hE : MeasurableSet E),
              (ambientRestrictedSet data center).Nonempty →
              0 < delta →
              delta ≤ delta₀ →
              tRep ≤ T →
              Nonempty
                (AmbientRestrictedFSVSetupData
                  data center hE
                    C_R C_count C_shading C_volume)

end Kakeya.Cinematic
