import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SparseRelativeBandPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SparseVariableQFiniteLipschitz
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SparseRelativeBandCVPackage
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WeakLipschitzPlaneMapRefinement

/-!
# Finite Lipschitz coordination of a relative-band sparse branch

All combinatorial and multiplicity hypotheses are discharged from
`SparseRelativeBandPreparationData`.  The only analytic input left explicit is
the CV broad-mass absorption inequality.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Coordinate the variable-`Q` weak plane map from a prepared sparse branch. -/
theorem sparse_relative_band_weak_finite_lipschitz_coefficient
    {delta kappa tau coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambient : WZ1PaperTubeShading family}
    {densityPower nearbyConstant cvConstant : ENNReal}
    (hcwa : WZ2PaperPureCWAAtNearbyScales family nearbyConstant)
    (hfamily : family.Nonempty)
    (hline : WZ1PaperIsLineClass family)
    (prepared : SparseRelativeBandPreparationData
      (kappa := kappa) ambient densityPower)
    (hCV : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ prepared.shading.union →
      ∀ (L : ENNReal),
        (∀ point ∈ E,
          L ≤ (paperShadingTrilinearMultiplicity
            prepared.shading point) ^ (1 / 2 : ℝ)) →
        L * volume E ≤
          cvConstant *
            (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
              (3 / 2 : ℝ))
    (hdelta : 0 < delta)
    (htau : 0 < tau)
    (hkappa : 0 < kappa)
    (hcoefficient : 0 < coefficient)
    (habsorb :
      let Q : ℕ := prepared.multiplicity ^ 3 / 4
      (2 : ENNReal) * (2 * prepared.multiplicity : ℕ) * cvConstant *
          (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : ℝ) ≤
        (((Q : ENNReal) * ENNReal.ofReal tau) ^
          (1 / 2 : ℝ)) * prepared.shading.mass)
    (N : ℕ)
    (requested : ℕ → WZ2PaperRequestedScale delta)
    (spatialScale variationScale : ℕ → ℝ)
    (hactualSmall : ∀ coordinate, coordinate < N →
      (hcwa.chosenNearby (requested coordinate)).rho < 1 / 8)
    (hparentKappa : ∀ coordinate, coordinate < N →
      8 * (hcwa.chosenNearby (requested coordinate)).rho < kappa)
    (K : ℕ → ℕ)
    (hK : ∀ coordinate, coordinate < N → 0 < K coordinate)
    (hspatialPositive : ∀ coordinate, coordinate < N →
      0 < spatialScale coordinate)
    (hvariationPositive : ∀ coordinate, coordinate < N →
      0 < variationScale coordinate)
    (hspatialAligned : ∀ coordinate, coordinate < N →
      spatialScale coordinate = (K coordinate : ℝ) * delta)
    (hcovers : ∀ d : ℝ, delta < d → d ≤ 4 → coefficient * d < 2 →
      ∃ coordinate, coordinate < N ∧ d ≤ spatialScale coordinate ∧
        variationScale coordinate ≤ coefficient * d) :
    ∃ (final : WZ1PaperTubeShading family)
      (planeMap : PaperWZ1WeakPlaneMapData final (tau / kappa)),
      PaperIsSubshading final ambient ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
            wz1PaperGridIndex delta second →
          planeMap.planeMap first = planeMap.planeMap second) ∧
      LipschitzWith (Real.toNNReal coefficient)
        (fun point : {point : Point3 // point ∈ final.union} =>
          planeMap.planeMap point) ∧
      (1 / 32 : ENNReal) *
          (∏ coordinate ∈ Finset.range N,
            (densityPower / 24) ^ 2) * ambient.mass ≤
        (prepared.bandCount : ENNReal) *
          ((∏ coordinate ∈ Finset.range N,
            27 * (2 *
              (wz1OrientationCapCount
                (10 *
                    (tau / kappa +
                      4 * (hcwa.chosenNearby
                        (requested coordinate)).rho) /
                  (kappa -
                    8 * (hcwa.chosenNearby
                      (requested coordinate)).rho))
                (variationScale coordinate) : ENNReal))) *
            27 * final.mass) := by
  let M := prepared.multiplicity
  let R := prepared.closeThreshold
  let Q := M ^ 3 / 4
  have hM : 0 < M := by
    rw [show M = 2 ^ prepared.level by
      exact prepared.multiplicity_eq]
    positivity
  have hQpos : 0 < Q := by
    dsimp only [Q]
    have hcube : 4 ≤ M ^ 3 := by
      have hMR : 12 * R ≤ M := prepared.combinatorial_budget
      have hR : 0 < R := prepared.closeThreshold_pos
      have htwo : 2 ≤ M := by omega
      calc
        4 ≤ 2 ^ 3 := by norm_num
        _ ≤ M ^ 3 := Nat.pow_le_pow_left htwo 3
    exact Nat.div_pos hcube (by norm_num)
  have hQ : 4 * Q ≤ M ^ 3 := by
    dsimp only [Q]
    exact Nat.mul_div_le (M ^ 3) 4
  have hmultiplicityUpper : ∀ point ∈ prepared.shading.union,
      (prepared.shading.pointMultiplicity point : ENNReal) ≤
        (2 * M : ℕ) := by
    intro point hpoint
    exact_mod_cast (prepared.multiplicity_upper point hpoint).le
  have hdensity : ∀ coordinate, coordinate < N →
      (densityPower / 24) * family.enncard ≤ (2 * R : ℕ) := by
    intro _ _
    exact prepared.coordination_density
  rcases paper_pure_sparse_variable_q_weak_finite_lipschitz_coefficient
      hcwa prepared.shading hfamily hline prepared.cubical
      M Q R prepared.multiplicity_lower hQpos hQ
      prepared.combinatorial_budget prepared.close_count hCV
      hmultiplicityUpper hdelta htau hkappa hcoefficient (by
        simpa [Q, M] using habsorb)
      (fun _ => densityPower / 24) N requested spatialScale variationScale
      hdensity hactualSmall hparentKappa K hK hspatialPositive
      hvariationPositive hspatialAligned hcovers with
    ⟨narrow, selected, final, planeMap, hnarrowSub, hselectedSub,
      hfinalSub, _hselectedCubical, hfinalCubical, _hfinalMultiplicity,
      hfinalCellwise, hfinalLipschitz, hfinalMass⟩
  have hfinalAmbient : PaperIsSubshading final ambient := fun index =>
    (hfinalSub index).trans <|
      (hselectedSub index).trans <|
        (hnarrowSub index).trans <|
          (prepared.subshading index).trans
            (prepared.source_subshading index)
  let productDensity : ENNReal :=
    ∏ coordinate ∈ Finset.range N, (densityPower / 24) ^ 2
  let productCost : ENNReal :=
    ∏ coordinate ∈ Finset.range N,
      27 * (2 *
        (wz1OrientationCapCount
          (10 *
              (tau / kappa +
                4 * (hcwa.chosenNearby (requested coordinate)).rho) /
            (kappa -
              8 * (hcwa.chosenNearby (requested coordinate)).rho))
          (variationScale coordinate) : ENNReal))
  have hmass : (1 / 32 : ENNReal) * productDensity * ambient.mass ≤
      (prepared.bandCount : ENNReal) *
        (productCost * 27 * final.mass) := by
    have hscaled := mul_le_mul_left' prepared.mass_retention
      ((1 / 8 : ENNReal) * productDensity)
    have hleft : (1 / 32 : ENNReal) * productDensity * ambient.mass =
        (1 / 8 : ENNReal) * productDensity *
          ((1 / 4 : ENNReal) * ambient.mass) := by
      have hcoefficient : (1 / 32 : ENNReal) =
          (1 / 8 : ENNReal) * (1 / 4 : ENNReal) := by
        simp only [one_div]
        have hmul : (8 : ENNReal) * 4 = 32 := by norm_num
        have hinv : ((8 : ENNReal) * 4)⁻¹ =
            (8 : ENNReal)⁻¹ * (4 : ENNReal)⁻¹ := by
          rw [ENNReal.mul_inv] <;> norm_num
        rw [hmul] at hinv
        exact hinv
      rw [hcoefficient]
      ring
    rw [← hleft] at hscaled
    calc
      (1 / 32 : ENNReal) * productDensity * ambient.mass ≤
          (1 / 8 : ENNReal) * productDensity *
            ((prepared.bandCount : ENNReal) * prepared.shading.mass) :=
        hscaled
      _ = (prepared.bandCount : ENNReal) *
          ((1 / 8 : ENNReal) * productDensity *
            prepared.shading.mass) := by ring
      _ ≤ (prepared.bandCount : ENNReal) *
          (productCost * 27 * final.mass) := by
        exact mul_le_mul_left'
          (by simpa [productDensity, productCost] using hfinalMass) _
  exact ⟨final, planeMap, hfinalAmbient, hfinalCubical,
    hfinalCellwise, hfinalLipschitz,
    by simpa [productDensity, productCost] using hmass⟩

/-- Consume the uniform CV package and expose the sparse branch through the
same quantitative weak-refinement interface as the dense branch. -/
theorem sparse_relative_band_packaged_weak_finite_lipschitz_coefficient
    {delta sigma loss kappa coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambient : WZ1PaperTubeShading family}
    {nearbyConstant : ENNReal}
    (hcwa : WZ2PaperPureCWAAtNearbyScales family nearbyConstant)
    (hfamily : family.Nonempty)
    (hline : WZ1PaperIsLineClass family)
    (prepared : SparseRelativeBandPreparationData
      (kappa := kappa) ambient
      (Kakeya.realRpowENN delta (2 - sigma + 3 * loss)))
    (package : SparseRelativeBandCVPackage ambient prepared)
    (hdelta : 0 < delta)
    (hkappa : 0 < kappa)
    (hcoefficient : 0 < coefficient)
    (N : ℕ)
    (requested : ℕ → WZ2PaperRequestedScale delta)
    (spatialScale variationScale : ℕ → ℝ)
    (hactualSmall : ∀ coordinate, coordinate < N →
      (hcwa.chosenNearby (requested coordinate)).rho < 1 / 8)
    (hparentKappa : ∀ coordinate, coordinate < N →
      8 * (hcwa.chosenNearby (requested coordinate)).rho < kappa)
    (K : ℕ → ℕ)
    (hK : ∀ coordinate, coordinate < N → 0 < K coordinate)
    (hspatialPositive : ∀ coordinate, coordinate < N →
      0 < spatialScale coordinate)
    (hvariationPositive : ∀ coordinate, coordinate < N →
      0 < variationScale coordinate)
    (hspatialAligned : ∀ coordinate, coordinate < N →
      spatialScale coordinate = (K coordinate : ℝ) * delta)
    (hcovers : ∀ d : ℝ, delta < d → d ≤ 4 → coefficient * d < 2 →
      ∃ coordinate, coordinate < N ∧ d ≤ spatialScale coordinate ∧
        variationScale coordinate ≤ coefficient * d) :
    Nonempty (QuantitativeWeakLipschitzPlaneMapRefinement ambient
      (package.tau / kappa)
      (Real.toNNReal coefficient)
      ((1 / 32 : ENNReal) *
        (∏ coordinate ∈ Finset.range N,
          (Kakeya.realRpowENN delta (2 - sigma + 3 * loss) / 24) ^ 2))
      ((prepared.bandCount : ENNReal) *
        ((∏ coordinate ∈ Finset.range N,
          27 * (2 *
            (wz1OrientationCapCount
              (10 *
                  (package.tau / kappa +
                    4 * (hcwa.chosenNearby
                      (requested coordinate)).rho) /
                (kappa -
                  8 * (hcwa.chosenNearby
                    (requested coordinate)).rho))
              (variationScale coordinate) : ENNReal))) *
          27))) := by
  rcases sparse_relative_band_weak_finite_lipschitz_coefficient
      hcwa hfamily hline prepared package.cv hdelta package.tau_pos hkappa
      hcoefficient package.absorb N requested spatialScale variationScale hactualSmall
      hparentKappa K hK hspatialPositive hvariationPositive
      hspatialAligned hcovers with
    ⟨final, planeMap, hfinalSub, hfinalCubical,
      hfinalCellwise, hfinalLipschitz, hfinalMass⟩
  exact ⟨{
    shading := final
    subshading := hfinalSub
    cubical := hfinalCubical
    planeMap := planeMap
    planeMap_cellwise := hfinalCellwise
    lipschitz := hfinalLipschitz
    mass_retention := by
      simpa [mul_assoc] using hfinalMass
  }⟩

end Kakeya.Assouad.PureWZ2

end
