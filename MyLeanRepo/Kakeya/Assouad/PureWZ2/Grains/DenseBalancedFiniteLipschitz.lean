import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighMultiplicityBalancedDichotomy
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DenseLocalizedFiniteLipschitz
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WeakLipschitzPlaneMapRefinement

/-!
# Finite Lipschitz coordination of the dense direction branch
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Localize a dense high-multiplicity branch to incidence `eta` and
coordinate the resulting genuine plane map through finitely many pure nearby
covers. -/
theorem dense_balanced_weak_finite_lipschitz_coefficient
    {delta kappa eta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambient source : WZ1PaperTubeShading family}
    {densityPower nearbyConstant : ENNReal}
    (hcwa : WZ2PaperPureCWAAtNearbyScales family nearbyConstant)
    (hfamily : family.Nonempty)
    (hline : WZ1PaperIsLineClass family)
    (hsourceSub : PaperIsSubshading source ambient)
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (center : Point3 → Fin family.card)
    (hcenterMeasurable : Measurable center)
    (hcenterCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      center first = center second)
    (hcluster : ∀ index point, point ∈ source.carrier index →
      ‖wz1Cross (family.tube (center point)).direction
        (family.tube index).direction‖ < kappa)
    (hdensity : ∀ point ∈ source.union,
      (densityPower / 48) * family.enncard ≤
        2 * (source.pointMultiplicity point : ENNReal))
    (hsourceMass :
      (densityPower / 48) * ((1 / 4 : ENNReal) * ambient.mass) ≤
        2 * source.mass)
    (N : ℕ)
    (requested : ℕ → WZ2PaperRequestedScale delta)
    (spatialScale variationScale : ℕ → ℝ)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (hdelta : 0 < delta)
    (heta : 0 < eta)
    (hetaHalf : eta ≤ 1 / 2)
    (hcoefficient : 0 < coefficient)
    (hactualSmall : ∀ coordinate, coordinate < N →
      (hcwa.chosenNearby (requested coordinate)).rho < 1 / 8)
    (hspatialPositive : ∀ coordinate, coordinate < N →
      0 < spatialScale coordinate)
    (hvariationPositive : ∀ coordinate, coordinate < N →
      0 < variationScale coordinate)
    (K : ℕ → ℕ)
    (hK : ∀ coordinate, coordinate < N → 0 < K coordinate)
    (hspatialAligned : ∀ coordinate, coordinate < N →
      spatialScale coordinate = (K coordinate : ℝ) * delta)
    (hcovers : ∀ d : ℝ, delta < d → d ≤ 4 → coefficient * d < 2 →
      ∃ coordinate, coordinate < N ∧ d ≤ spatialScale coordinate ∧
        variationScale coordinate ≤ coefficient * d) :
    Nonempty (QuantitativeWeakLipschitzPlaneMapRefinement ambient eta
      (Real.toNNReal coefficient)
      ((∏ coordinate ∈ Finset.range N, (densityPower / 48)) *
        (densityPower / 48) * (1 / 4))
      (2 *
        (denseLocalDirectionLabelCount kappa eta : ENNReal) *
        (∏ coordinate ∈ Finset.range N,
          (localPlaneMapCapCount
            (8 * eta +
              16 * (hcwa.chosenNearby (requested coordinate)).rho)
            (variationScale coordinate) : ENNReal) *
            27 *
              (2 *
                (denseLocalDirectionLabelCount kappa eta : ENNReal))) *
        27)) := by
  rcases paper_pure_dense_localized_finite_lipschitz_coefficient
      hcwa source hfamily hline hsourceCubical center hcenterMeasurable
      hcenterCell hcluster (fun _ => 2) (fun _ => densityPower / 48)
      N requested spatialScale variationScale
      (by
        intro coordinate _ point hpoint
        exact hdensity point hpoint)
      hkappaNonnegative hkappaHalf hdelta heta hetaHalf hcoefficient hactualSmall
      hspatialPositive hvariationPositive K hK hspatialAligned hcovers with
    ⟨localized, final, localCenter, planeMap, hlocalizedSub, hfinalSub,
      _hlocalizedCubical, hfinalCubical, _hmultiplicity, hfinalCellwise,
      hfinalLipschitz, hfinalMass⟩
  have hfinalAmbient : PaperIsSubshading final ambient := fun index =>
    (hfinalSub index).trans <|
      (hlocalizedSub index).trans (hsourceSub index)
  let productDensity : ENNReal :=
    ∏ coordinate ∈ Finset.range N, densityPower / 48
  let localCount : ENNReal :=
    denseLocalDirectionLabelCount kappa eta
  let productCost : ENNReal :=
    ∏ coordinate ∈ Finset.range N,
      (localPlaneMapCapCount
        (8 * eta + 16 * (hcwa.chosenNearby (requested coordinate)).rho)
        (variationScale coordinate) : ENNReal) *
        27 * (2 * localCount)
  have hmass :
      (productDensity * (densityPower / 48) * (1 / 4)) *
          ambient.mass ≤
        (2 * localCount * productCost * 27) * final.mass := by
    have hscaled := mul_le_mul_left' hsourceMass productDensity
    calc
      (productDensity * (densityPower / 48) * (1 / 4)) *
          ambient.mass =
          productDensity *
            ((densityPower / 48) * ((1 / 4 : ENNReal) * ambient.mass)) := by
        ring
      _ ≤ productDensity * (2 * source.mass) := hscaled
      _ = 2 * (productDensity * source.mass) := by ring
      _ ≤ 2 *
          (localCount * productCost * 27 * final.mass) := by
        exact mul_le_mul_left'
          (by simpa [productDensity, localCount, productCost] using hfinalMass) _
      _ = (2 * localCount * productCost * 27) * final.mass := by ring
  exact ⟨{
    shading := final
    subshading := hfinalAmbient
    cubical := hfinalCubical
    planeMap := planeMap
    planeMap_cellwise := hfinalCellwise
    lipschitz := hfinalLipschitz
    mass_retention := by
      simpa [productDensity, localCount, productCost] using hmass
  }⟩

end Kakeya.Assouad.PureWZ2

end
