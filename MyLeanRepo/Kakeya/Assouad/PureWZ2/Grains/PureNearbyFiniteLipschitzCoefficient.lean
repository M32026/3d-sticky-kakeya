import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureNearbyFiniteVariation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteScaleLipschitzBridge

/-!
# Quantitative finite pure-nearby Lipschitz coordination

The historical wrapper fixed the terminal Lipschitz constant to one.  The
underlying finite-scale bridge is already quantitative.  This module exposes
that coefficient while keeping the identical parent-pair refinements and mass
account.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Coordinate one genuine cellwise weak plane map through finitely many pure
nearby covers and obtain an arbitrary positive Lipschitz constant. -/
theorem paper_pure_nearby_cwa_fixed_plane_map_finite_lipschitz_coefficient
    {delta incidence coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hcwa : WZ2PaperPureCWAAtNearbyScales fine C)
    (source : WZ1PaperTubeShading fine)
    (hfineNonempty : fine.Nonempty)
    (hline : WZ1PaperIsLineClass fine)
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (planeMap : PaperWZ1WeakPlaneMapData source incidence)
    (hplaneCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second)
    (fineMultiplicity : ℕ)
    (hFineMultiplicity : ∀ point ∈ source.union,
      fineMultiplicity ≤ source.pointMultiplicity point)
    (N : ℕ)
    (requested : ℕ → WZ2PaperRequestedScale delta)
    (spatialScale variationScale : ℕ → ℝ)
    (kappa : ℕ → ℝ)
    (densityPower : ℕ → ENNReal)
    (hclose : ∀ k, k < N → ∀ point ∈ source.union, ∀ index,
      point ∈ source.carrier index →
      2 * paperCloseDirectionCount source point index (kappa k) ≤
        fineMultiplicity)
    (hdensity : ∀ k, k < N →
      densityPower k * fine.enncard ≤ (fineMultiplicity : ENNReal))
    (hincidenceNonnegative : 0 ≤ incidence)
    (hactualSmall : ∀ k, k < N →
      (hcwa.chosenNearby (requested k)).rho < 1 / 8)
    (hkappa : ∀ k, k < N →
      8 * (hcwa.chosenNearby (requested k)).rho < kappa k)
    (K : ℕ → ℕ)
    (hK : ∀ k, k < N → 0 < K k)
    (hspatialPositive : ∀ k, k < N → 0 < spatialScale k)
    (hvariationPositive : ∀ k, k < N → 0 < variationScale k)
    (hspatialAligned : ∀ k, k < N →
      spatialScale k = (K k : ℝ) * delta)
    (hdelta : 0 < delta)
    (hcoefficient : 0 < coefficient)
    (hcovers : ∀ d : ℝ, delta < d → d ≤ 4 →
      coefficient * d < 2 →
      ∃ k, k < N ∧ d ≤ spatialScale k ∧
        variationScale k ≤ coefficient * d) :
    ∃ (final : WZ1PaperTubeShading fine)
      (finalPlaneMap : PaperWZ1WeakPlaneMapData final incidence),
      PaperIsSubshading final source ∧
      finalPlaneMap.planeMap = planeMap.planeMap ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point = source.pointMultiplicity point) ∧
      LipschitzWith (Real.toNNReal coefficient)
        (fun point : {point : Point3 // point ∈ final.union} =>
          finalPlaneMap.planeMap point) ∧
      (∏ k ∈ Finset.range N, densityPower k ^ 2) * source.mass ≤
        (∏ k ∈ Finset.range N,
          27 * (2 *
            (wz1OrientationCapCount
              (10 *
                  (incidence +
                    4 * (hcwa.chosenNearby (requested k)).rho) /
                (kappa k -
                  8 * (hcwa.chosenNearby (requested k)).rho))
              (variationScale k) : ENNReal))) *
          27 * final.mass := by
  rcases paper_pure_nearby_cwa_fixed_plane_map_finite_nested_variation
      hcwa source hfineNonempty hline hsourceCubical planeMap hplaneCell
      fineMultiplicity hFineMultiplicity N requested spatialScale
      variationScale kappa densityPower hclose hdensity
      hincidenceNonnegative hactualSmall hkappa K hK hspatialPositive
      hvariationPositive hspatialAligned with
    ⟨coordinated, hcoordinatedSub, hcoordinatedCubical,
      hcoordinatedMultiplicity, hvariation, hcoordinatedMass⟩
  let coordinatedPlaneMap :=
    PureWZ2.paperWeakPlaneMapRestrict planeMap hcoordinatedSub
  have hcoordinatedCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      coordinatedPlaneMap.planeMap first =
        coordinatedPlaneMap.planeMap second := hplaneCell
  rcases PureWZ2.paper_finite_scale_variation_to_lipschitz
      hdelta hcoefficient hcoordinatedCubical coordinatedPlaneMap
      hcoordinatedCell N spatialScale variationScale hvariation
      (fun first hfirst second hsecond =>
        PureWZ2.paper_shading_union_dist_le_four coordinated
          hfirst hsecond) hcovers with
    ⟨final, finalPlaneMap, hfinalSubCoordinated, hfinalPlaneMap,
      hfinalCubical, hfinalMultiplicityCoordinated, hresidueMass,
      hfinalLipschitz⟩
  have hfinalSub : PaperIsSubshading final source := fun index =>
    (hfinalSubCoordinated index).trans (hcoordinatedSub index)
  have hfinalMultiplicity : ∀ point ∈ final.union,
      final.pointMultiplicity point = source.pointMultiplicity point := by
    intro point hpoint
    have hpointCoordinated : point ∈ coordinated.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hfinalSubCoordinated index hindex⟩
    exact (hfinalMultiplicityCoordinated point hpoint).trans
      (hcoordinatedMultiplicity point hpointCoordinated)
  have hfinalMass :
      (∏ k ∈ Finset.range N, densityPower k ^ 2) * source.mass ≤
        (∏ k ∈ Finset.range N,
          27 * (2 *
            (wz1OrientationCapCount
              (10 *
                  (incidence +
                    4 * (hcwa.chosenNearby (requested k)).rho) /
                (kappa k -
                  8 * (hcwa.chosenNearby (requested k)).rho))
              (variationScale k) : ENNReal))) *
          27 * final.mass := by
    calc
      (∏ k ∈ Finset.range N, densityPower k ^ 2) * source.mass ≤
          (∏ k ∈ Finset.range N,
            27 * (2 *
              (wz1OrientationCapCount
                (10 *
                    (incidence +
                      4 * (hcwa.chosenNearby (requested k)).rho) /
                  (kappa k -
                    8 * (hcwa.chosenNearby (requested k)).rho))
                (variationScale k) : ENNReal))) *
            coordinated.mass := hcoordinatedMass
      _ ≤ (∏ k ∈ Finset.range N,
            27 * (2 *
              (wz1OrientationCapCount
                (10 *
                    (incidence +
                      4 * (hcwa.chosenNearby (requested k)).rho) /
                  (kappa k -
                    8 * (hcwa.chosenNearby (requested k)).rho))
                (variationScale k) : ENNReal))) *
            (27 * final.mass) := by gcongr
      _ = (∏ k ∈ Finset.range N,
            27 * (2 *
              (wz1OrientationCapCount
                (10 *
                    (incidence +
                      4 * (hcwa.chosenNearby (requested k)).rho) /
                  (kappa k -
                    8 * (hcwa.chosenNearby (requested k)).rho))
                (variationScale k) : ENNReal))) *
            27 * final.mass := by ring
  exact ⟨final, finalPlaneMap, hfinalSub, hfinalPlaneMap, hfinalCubical,
    hfinalMultiplicity, hfinalLipschitz, hfinalMass⟩

end Kakeya.Assouad

end
