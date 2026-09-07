import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureFiniteNestedVariation

/-!
# Finite variation schedule from pure nearby-scale CWA

For each requested, integer-aligned spatial scale, pure CWA supplies an actual
nearby cover.  The requested scale controls the spatial grid, while the actual
cover radius controls the carrier-direction error.  This module chooses those
witnesses and feeds them to the finite nested variation theorem without
identifying the two scales.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The canonical chosen nearby witness at one requested scale. -/
noncomputable def WZ2PaperPureCWAAtNearbyScales.chosenNearby
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hcwa : WZ2PaperPureCWAAtNearbyScales fine C)
    (requested : WZ2PaperRequestedScale delta) :
    WZ2PaperPureNearbyScaleCoverData fine requested C :=
  Classical.choice (hcwa.2.2.2 requested)

/-- Choose finitely many nearby pure covers and run the fixed-map variation
iteration.  No exact-scale replacement of a nearby witness is made. -/
theorem paper_pure_nearby_cwa_fixed_plane_map_finite_nested_variation
    {delta incidence : ℝ}
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
      spatialScale k = (K k : ℝ) * delta) :
    ∃ final : WZ1PaperTubeShading fine,
      PaperIsSubshading final source ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point = source.pointMultiplicity point) ∧
      (∀ k, k < N → ∀ point ∈ final.union, ∀ other ∈ final.union,
        dist point other ≤ spatialScale k →
          dist (planeMap.planeMap point)
            (planeMap.planeMap other) ≤ variationScale k) ∧
      (∏ k ∈ Finset.range N, densityPower k ^ 2) * source.mass ≤
        (∏ k ∈ Finset.range N,
          27 * (2 *
            (wz1OrientationCapCount
              (10 *
                  (incidence +
                    4 * (hcwa.chosenNearby (requested k)).rho) /
                (kappa k -
                  8 * (hcwa.chosenNearby (requested k)).rho))
              (variationScale k) : ENNReal))) * final.mass := by
  let nearby (k : ℕ) :
      WZ2PaperPureNearbyScaleCoverData fine (requested k) C :=
    hcwa.chosenNearby (requested k)
  exact paper_pure_fixed_plane_map_finite_nested_variation
    source hfineNonempty hline hsourceCubical planeMap hplaneCell
    fineMultiplicity hFineMultiplicity N
    (fun k => (nearby k).rho) spatialScale variationScale kappa
    (fun k => (nearby k).scaleData.coarse)
    (fun k => (nearby k).scaleData.cover) densityPower hclose hdensity
    hincidenceNonnegative
    (fun k _ => (nearby k).scaleData.rho_pos)
    (fun k hk => hactualSmall k hk) hspatialPositive hvariationPositive
    (fun k hk => hkappa k hk) K hK hspatialAligned

end Kakeya.Assouad

end
