import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeOutputCertificate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCriticalFloorSelection
import MyLeanRepo.Kakeya.Assouad.PropStickyOrdinaryToCroppedShading

/-!
# Ordinary critical witness for the exact V4 final coarse shading

The pure critical floor applies to ordinary unit-segment shadings, whereas
the V4 final coarse shading is carried by cropped full-line paper tubes.  The
record below isolates the exact non-circular bridge needed at this point: an
ordinary pure shading whose union is contained in the already constructed
final coarse shaded union.

No final multiplicity estimate or extremality conclusion is included in the
witness.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/--
An ordinary pure critical-floor witness for the exact final coarse shading of
one rich four-degree output.

The ordinary family may use different unit-segment representatives.  The
last field is the exact comparison that transfers the pure critical lower
bound to the fixed V4 coarse shading.
-/
structure Prop62V4FinalCoarseCriticalWitness
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambientCover : PureWZ2Section6Cover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {densityConstant outputParentConstant sourceFiberConstant : ENNReal}
    {input : PureWZ2Prop62PacketCellInput ambientCover sourceShading}
    (output :
      PureWZ2Prop62FourDegreeOutputCertificate
        input densityConstant outputParentConstant sourceFiberConstant)
    (loss : ℝ) where
  ordinaryFamily : Kakeya.Streamlined.TubeFamily rho
  ordinaryShading :
    Kakeya.Streamlined.TubeShading ordinaryFamily
  ordinary_nonempty : ordinaryFamily.Nonempty
  ordinary_cwa :
    WZ2PaperPureCWAAtNearbyScales ordinaryFamily
      (Kakeya.realRpowENN rho (-loss))
  ordinary_dense :
    ordinaryShading.IsLambdaDense
      (Kakeya.realRpowENN rho loss)
  ordinary_union_subset :
    ordinaryShading.union ⊆ output.coarseShading.union

namespace Prop62V4FinalCoarseCriticalWitness

variable
    {delta rho sigma floorLoss structuralBudget : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambientCover : PureWZ2Section6Cover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {densityConstant outputParentConstant sourceFiberConstant : ENNReal}
    {input : PureWZ2Prop62PacketCellInput ambientCover sourceShading}
    {output :
      PureWZ2Prop62FourDegreeOutputCertificate
        input densityConstant outputParentConstant sourceFiberConstant}

/--
Apply the ordinary pure critical floor and transfer its lower bound to the
exact final cropped coarse shading.
-/
theorem volume_floor
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss structuralBudget)
    (witness :
      Prop62V4FinalCoarseCriticalWitness
        output critical.structuralLoss)
    (rho_le : rho ≤ critical.delta₀) :
    Kakeya.realRpowENN rho (sigma + floorLoss) ≤
      volume output.coarseShading.union := by
  exact
    (critical.volume_floor rho input.rho_pos rho_le
      (Prop62V4FinalCoarseCriticalWitness.ordinaryFamily witness)
      (Prop62V4FinalCoarseCriticalWitness.ordinary_nonempty witness)
      (Prop62V4FinalCoarseCriticalWitness.ordinaryShading witness)
      (Prop62V4FinalCoarseCriticalWitness.ordinary_cwa witness)
      (Prop62V4FinalCoarseCriticalWitness.ordinary_dense witness)).trans
        (measure_mono
          (Prop62V4FinalCoarseCriticalWitness.ordinary_union_subset witness))

end Prop62V4FinalCoarseCriticalWitness

namespace PureWZ2Prop62FourDegreeOutputCertificate

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambientCover : PureWZ2Section6Cover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {densityConstant outputParentConstant sourceFiberConstant : ENNReal}
    {input : PureWZ2Prop62PacketCellInput ambientCover sourceShading}
    (output :
      PureWZ2Prop62FourDegreeOutputCertificate
        input densityConstant outputParentConstant sourceFiberConstant)

/--
The canonical same-family ordinary trace obtained by intersecting each final
coarse cropped carrier with its ordinary unit-segment carrier.
-/
noncomputable def finalCoarseOrdinaryTrace :
    Kakeya.Streamlined.TubeShading output.coarse.family :=
  wz2PaperCroppedShadingToOrdinary output.coarseShading

/-- The canonical ordinary trace lies in the exact final coarse shaded union. -/
theorem finalCoarseOrdinaryTrace_union_subset :
    output.finalCoarseOrdinaryTrace.union ⊆
      output.coarseShading.union :=
  wz2PaperCroppedShadingToOrdinary_union_subset output.coarseShading

/-- The exact final coarse family is nonempty. -/
theorem finalCoarse_nonempty :
    output.coarse.family.Nonempty := by
  let sourceIndex : Fin output.refinement.selected.family.card :=
    ⟨0, output.refined_nonempty⟩
  exact
    Nat.zero_lt_of_lt
      (output.cover.toWZ1PaperTubeCover.parent sourceIndex).isLt

/--
The only additional input needed when the ordinary witness uses the same
final coarse family is density of the canonical ordinary trace.  Pure nearby
CWA is already retained by the rich four-degree certificate.
-/
noncomputable def finalCoarseCriticalWitnessOfTraceDense
    (loss : ℝ)
    (constant_le :
      outputParentConstant ≤
        Kakeya.realRpowENN rho (-loss))
    (trace_dense :
      output.finalCoarseOrdinaryTrace.IsLambdaDense
        (Kakeya.realRpowENN rho loss)) :
    Prop62V4FinalCoarseCriticalWitness output loss where
  ordinaryFamily := output.coarse.family
  ordinaryShading := output.finalCoarseOrdinaryTrace
  ordinary_nonempty := output.finalCoarse_nonempty
  ordinary_cwa :=
    output.parent_cwa.mono constant_le
      (by simp [Kakeya.realRpowENN])
  ordinary_dense := trace_dense
  ordinary_union_subset :=
    output.finalCoarseOrdinaryTrace_union_subset

/--
Same-family specialization: once density of the canonical ordinary trace is
proved, the pure critical floor gives the exact V4 final coarse volume floor.
-/
theorem finalCoarseVolumeFloorOfTraceDense
    {sigma floorLoss structuralBudget : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss structuralBudget)
    (rho_le : rho ≤ critical.delta₀)
    (constant_le :
      outputParentConstant ≤
        Kakeya.realRpowENN rho (-critical.structuralLoss))
    (trace_dense :
      output.finalCoarseOrdinaryTrace.IsLambdaDense
        (Kakeya.realRpowENN rho critical.structuralLoss)) :
    Kakeya.realRpowENN rho (sigma + floorLoss) ≤
      volume output.coarseShading.union :=
  Prop62V4FinalCoarseCriticalWitness.volume_floor
    critical
    (output.finalCoarseCriticalWitnessOfTraceDense
      critical.structuralLoss constant_le trace_dense)
    rho_le

end PureWZ2Prop62FourDegreeOutputCertificate

end Kakeya.Assouad

end
