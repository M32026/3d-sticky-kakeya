import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyPostDeletionStructure
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper
import MyLeanRepo.Kakeya.Assouad.WZ1.MultiplicityBounds

/-!
# Pure critical coarse multiplicity cap

This module isolates the part of the coarse-cap argument after the critical
union-volume floor.  The scalar theorem uses only that floor, the lower half
of one dyadic multiplicity band, a total shaded-mass upper bound, and one
explicit absorption inequality.  In particular, it does not pass through the
historical cropped CWA interface.

The final theorem applies the scalar argument to the exact post-deletion
coarse family and shading.  All inequalities remain attached to that same
dependent object.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/--
The volume-floor part of the coarse multiplicity argument.

The factor two converting the lower dyadic endpoint `2^level` to the public
cap `2^(level+1)` is included in `constantAbsorption`; no second dyadic loss
is introduced.
-/
theorem pureWZ2_coarse_cap_from_volume_floor_and_mass_upper
    {scale sigma floorLoss outputLoss : ℝ}
    (scalePos : 0 < scale)
    {bodyFamily : Kakeya.Streamlined.BodyFamily}
    (shading : Kakeya.Streamlined.Shading bodyFamily)
    (cardinality massConstant : ENNReal)
    (level : ℕ)
    (volumeFloor :
      Kakeya.realRpowENN scale (sigma + floorLoss) ≤
        volume shading.union)
    (massUpper :
      shading.mass ≤
        massConstant * Kakeya.realRpowENN scale 2 * cardinality)
    (bandLower :
      ∀ point ∈ shading.union,
        (2 ^ level : ENNReal) ≤
          (shading.pointMultiplicity point : ENNReal))
    (constantAbsorption :
      2 * massConstant ≤
        Kakeya.realRpowENN scale (-(outputLoss - floorLoss))) :
    (2 ^ (level + 1) : ENNReal) ≤
      Kakeya.realRpowENN scale (2 - sigma - outputLoss) *
        cardinality := by
  let multiplicity : ENNReal := 2 ^ level
  have floorMass :
      multiplicity *
          Kakeya.realRpowENN scale (sigma + floorLoss) ≤
        shading.mass := by
    calc
      multiplicity *
            Kakeya.realRpowENN scale (sigma + floorLoss) ≤
          multiplicity * volume shading.union := by
        gcongr
      _ ≤ shading.mass :=
        multiplicity_floor_le_mass <| by
          intro point pointMem
          simpa only [multiplicity] using bandLower point pointMem
  have scaledMass :
      ((2 : ENNReal) * multiplicity) *
          Kakeya.realRpowENN scale (sigma + floorLoss) ≤
        (2 * massConstant) *
          Kakeya.realRpowENN scale 2 * cardinality := by
    calc
      ((2 : ENNReal) * multiplicity) *
            Kakeya.realRpowENN scale (sigma + floorLoss) =
          2 *
            (multiplicity *
              Kakeya.realRpowENN scale (sigma + floorLoss)) := by
        ring
      _ ≤ 2 * shading.mass :=
        mul_le_mul_left' floorMass 2
      _ ≤
          2 *
            (massConstant *
              Kakeya.realRpowENN scale 2 * cardinality) :=
        mul_le_mul_left' massUpper 2
      _ =
          (2 * massConstant) *
            Kakeya.realRpowENN scale 2 * cardinality := by
        ring
  have absorbed :
      ((2 : ENNReal) * multiplicity) *
          Kakeya.realRpowENN scale (sigma + floorLoss) ≤
        Kakeya.realRpowENN scale
            (2 + floorLoss - outputLoss) *
          cardinality := by
    calc
      ((2 : ENNReal) * multiplicity) *
            Kakeya.realRpowENN scale (sigma + floorLoss) ≤
          (2 * massConstant) *
            Kakeya.realRpowENN scale 2 * cardinality :=
        scaledMass
      _ ≤
          Kakeya.realRpowENN scale (-(outputLoss - floorLoss)) *
            Kakeya.realRpowENN scale 2 * cardinality := by
        gcongr
      _ =
          Kakeya.realRpowENN scale
              (2 + floorLoss - outputLoss) *
            cardinality := by
        rw [realRpowENN_mul' scalePos]
        congr 1
        ring
  have factorization :
      Kakeya.realRpowENN scale (2 + floorLoss - outputLoss) =
        Kakeya.realRpowENN scale (sigma + floorLoss) *
          Kakeya.realRpowENN scale (2 - sigma - outputLoss) := by
    rw [realRpowENN_mul' scalePos]
    congr 1
    ring
  have floorFactor_ne_zero :
      Kakeya.realRpowENN scale (sigma + floorLoss) ≠ 0 := by
    simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos scalePos]
  have floorFactor_ne_top :
      Kakeya.realRpowENN scale (sigma + floorLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have capStrong :
      (2 : ENNReal) * multiplicity ≤
        Kakeya.realRpowENN scale (2 - sigma - outputLoss) *
          cardinality := by
    have withFloorFactor :
        Kakeya.realRpowENN scale (sigma + floorLoss) *
            ((2 : ENNReal) * multiplicity) ≤
          Kakeya.realRpowENN scale (sigma + floorLoss) *
            (Kakeya.realRpowENN scale (2 - sigma - outputLoss) *
              cardinality) := by
      calc
        Kakeya.realRpowENN scale (sigma + floorLoss) *
              ((2 : ENNReal) * multiplicity) =
            ((2 : ENNReal) * multiplicity) *
              Kakeya.realRpowENN scale (sigma + floorLoss) := by
          ring
        _ ≤
            Kakeya.realRpowENN scale
                (2 + floorLoss - outputLoss) *
              cardinality :=
          absorbed
        _ =
            (Kakeya.realRpowENN scale (sigma + floorLoss) *
              Kakeya.realRpowENN scale (2 - sigma - outputLoss)) *
              cardinality := by
          rw [← factorization]
        _ =
            Kakeya.realRpowENN scale (sigma + floorLoss) *
              (Kakeya.realRpowENN scale (2 - sigma - outputLoss) *
                cardinality) := by
          ring
    exact
      (ENNReal.mul_le_mul_iff_right
        floorFactor_ne_zero floorFactor_ne_top).mp withFloorFactor
  calc
    (2 ^ (level + 1) : ENNReal) =
        (2 : ENNReal) * multiplicity := by
      simp [multiplicity, pow_succ, mul_comm]
    _ ≤
        Kakeya.realRpowENN scale (2 - sigma - outputLoss) *
          cardinality :=
      capStrong

/--
Specialize the scalar argument to paper tube carriers, whose aggregate mass
has the closed quadratic upper bound.
-/
theorem pureWZ2_paper_coarse_cap_from_volume_floor
    {scale sigma floorLoss outputLoss : ℝ}
    (scalePos : 0 < scale)
    (scaleSmall : scale ≤ 1 / 24)
    {family : Kakeya.Streamlined.TubeFamily scale}
    (shading : WZ1PaperTubeShading family)
    (lineClass : WZ1PaperIsLineClass family)
    (level : ℕ)
    (volumeFloor :
      Kakeya.realRpowENN scale (sigma + floorLoss) ≤
        volume shading.union)
    (bandLower :
      ∀ point ∈ shading.union,
        (2 ^ level : ENNReal) ≤
          (shading.pointMultiplicity point : ENNReal))
    (constantAbsorption :
      2 * (55296 * Kakeya.deltaTubeVolume 1) ≤
        Kakeya.realRpowENN scale (-(outputLoss - floorLoss))) :
    (2 ^ (level + 1) : ENNReal) ≤
      Kakeya.realRpowENN scale (2 - sigma - outputLoss) *
        family.enncard := by
  apply
    pureWZ2_coarse_cap_from_volume_floor_and_mass_upper
      scalePos shading family.enncard
        (55296 * Kakeya.deltaTubeVolume 1) level
      volumeFloor
  · exact
      wz2_paper_shading_mass_upper
        scalePos scaleSmall lineClass shading
  · exact bandLower
  · exact constantAbsorption

namespace PureWZ2SameFamilyPositiveParentDeletionData

variable
    {delta sigma outputLoss floorLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {support : PureWZ2PositiveCallerSupportData quotient}
    {coordinateCount : ℕ}
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled}
    {scaleSeparation : 18 * delta ≤ callerRequested.1}
    {balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation}
    {deletionExponent : ℕ}
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent)

/--
The H5 coarse cap for the exact same-family post-deletion shading, starting
from a pure critical volume lower bound on that same shading.
-/
theorem coarse_cap_upper_from_pure_volume_floor
    (rhoSmall : callerRequested.1 ≤ 1 / 24)
    (volumeFloor :
      Kakeya.realRpowENN callerRequested.1 (sigma + floorLoss) ≤
        volume data.finalCoarseShading.union)
    (constantAbsorption :
      2 * (55296 * Kakeya.deltaTubeVolume 1) ≤
        Kakeya.realRpowENN callerRequested.1
          (-(outputLoss - floorLoss))) :
    (2 ^
        (balancing.balanced.finalData.producer.coarseBand.level + 1) :
      ENNReal) ≤
      Kakeya.realRpowENN callerRequested.1
          (2 - sigma - outputLoss) *
        data.selectedCoarse.family.enncard := by
  exact
    pureWZ2_paper_coarse_cap_from_volume_floor
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      rhoSmall data.finalCoarseShading
      data.section6Cover.coarse_line_class
      balancing.balanced.finalData.producer.coarseBand.level
      volumeFloor
      (fun point pointMem =>
        (data.post.bands.coarse_band point pointMem).1)
      constantAbsorption

end PureWZ2SameFamilyPositiveParentDeletionData

end Kakeya.Assouad

end
