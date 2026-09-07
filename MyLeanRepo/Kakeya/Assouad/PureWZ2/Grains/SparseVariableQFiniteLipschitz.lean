import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseWeakPlaniness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SparseQ1PlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureNearbyFiniteLipschitzCoefficient
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperBroadMassBudget

/-!
# Variable-Q sparse planiness and finite-scale coordination

Unlike the special `Q = 1` route, this is the quantitative sparse branch
needed by the paper.  The broad threshold `Q` is allowed to pay the
multilinear Kakeya term.  High point multiplicity supplies the independent
combinatorial budgets `4 Q ≤ m^3` and `12 R ≤ m`.

The cellwise weak-planiness selector is followed by the existing finite
nearby-cover coordination.  The final map remains on the original tube
family, is `1`-Lipschitz, and has incidence exactly `delta` when
`tau / kappa = delta`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

theorem paper_pure_sparse_variable_q_weak_finite_lipschitz_coefficient
    {delta tau kappa coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {nearbyConstant cvConstant multiplicityUpper : ENNReal}
    (hcwa : WZ2PaperPureCWAAtNearbyScales fine nearbyConstant)
    (source : WZ1PaperTubeShading fine)
    (hfineNonempty : fine.Nonempty)
    (hline : WZ1PaperIsLineClass fine)
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (m Q R : ℕ)
    (hmultiplicity : ∀ point ∈ source.union,
      m ≤ source.pointMultiplicity point)
    (hQpos : 0 < Q)
    (hQ : 4 * Q ≤ m ^ 3)
    (hR : 12 * R ≤ m)
    (hclose : ∀ point ∈ source.union, ∀ index,
      point ∈ source.carrier index →
      paperCloseDirectionCount source point index kappa < R)
    (hCV : ∀ (E : Set Point3), MeasurableSet E → E ⊆ source.union →
      ∀ (L : ENNReal),
        (∀ point ∈ E,
          L ≤ (paperShadingTrilinearMultiplicity source point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          cvConstant *
            (ENNReal.ofReal (delta ^ 2) * fine.enncard) ^
              (3 / 2 : ℝ))
    (hmultiplicityUpper : ∀ point ∈ source.union,
      (source.pointMultiplicity point : ENNReal) ≤ multiplicityUpper)
    (hdelta : 0 < delta)
    (htau : 0 < tau)
    (hkappa : 0 < kappa)
    (hcoefficient : 0 < coefficient)
    (habsorb :
      (2 : ENNReal) * multiplicityUpper * cvConstant *
          (ENNReal.ofReal (delta ^ 2) * fine.enncard) ^
            (3 / 2 : ℝ) ≤
        (((Q : ENNReal) * ENNReal.ofReal tau) ^
          (1 / 2 : ℝ)) * source.mass)
    (densityPower : ℕ → ENNReal)
    (N : ℕ)
    (requested : ℕ → WZ2PaperRequestedScale delta)
    (spatialScale variationScale : ℕ → ℝ)
    (hdensity : ∀ k, k < N →
      densityPower k * fine.enncard ≤ (2 * R : ℕ))
    (hactualSmall : ∀ k, k < N →
      (hcwa.chosenNearby (requested k)).rho < 1 / 8)
    (hparentKappa : ∀ k, k < N →
      8 * (hcwa.chosenNearby (requested k)).rho < kappa)
    (K : ℕ → ℕ)
    (hK : ∀ k, k < N → 0 < K k)
    (hspatialPositive : ∀ k, k < N → 0 < spatialScale k)
    (hvariationPositive : ∀ k, k < N → 0 < variationScale k)
    (hspatialAligned : ∀ k, k < N →
      spatialScale k = (K k : ℝ) * delta)
    (hcovers : ∀ d : ℝ, delta < d → d ≤ 4 → coefficient * d < 2 →
      ∃ k, k < N ∧ d ≤ spatialScale k ∧
        variationScale k ≤ coefficient * d) :
    ∃ (narrow selected final : WZ1PaperTubeShading fine)
      (finalPlaneMap : PaperWZ1WeakPlaneMapData final (tau / kappa)),
      PaperIsSubshading narrow source ∧
      PaperIsSubshading selected narrow ∧
      PaperIsSubshading final selected ∧
      WZ1PaperIsCubicalShading selected ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point = selected.pointMultiplicity point) ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
            wz1PaperGridIndex delta second →
          finalPlaneMap.planeMap first = finalPlaneMap.planeMap second) ∧
      LipschitzWith (Real.toNNReal coefficient)
        (fun point : {point : Point3 // point ∈ final.union} =>
          finalPlaneMap.planeMap point) ∧
      (1 / 8 : ENNReal) *
          (∏ k ∈ Finset.range N, densityPower k ^ 2) * source.mass ≤
        (∏ k ∈ Finset.range N,
          27 * (2 *
            (wz1OrientationCapCount
              (10 *
                  (tau / kappa +
                    4 * (hcwa.chosenNearby (requested k)).rho) /
                (kappa -
                  8 * (hcwa.chosenNearby (requested k)).rho))
              (variationScale k) : ENNReal))) *
          27 * final.mass := by
  have hbroadSmall :
      2 * (∫⁻ point in paperCountedBroadSet source tau Q,
        (source.pointMultiplicity point : ENNReal)) ≤ source.mass :=
    paper_broad_mass_budget_main cvConstant hCV multiplicityUpper
      hmultiplicityUpper Q tau hQpos htau habsorb
  have hbroadMeasurable :
      MeasurableSet (paperCountedBroadSet source tau Q) :=
    paperCountedBroadSet_measurable source tau Q
  rcases paper_narrow_pruning hbroadMeasurable hbroadSmall with
    ⟨narrowData⟩
  let narrow := narrowData.shading
  have hnarrowClose : ∀ point ∈ narrow.union, ∀ index,
      point ∈ narrow.carrier index →
      paperCloseDirectionCount narrow point index kappa < R := by
    intro point hpoint index hindex
    have hpointSource : point ∈ source.union :=
      ⟨index, narrowData.subshading index hindex⟩
    have hmono : paperCloseDirectionCount narrow point index kappa ≤
        paperCloseDirectionCount source point index kappa := by
      unfold paperCloseDirectionCount
      apply Finset.card_le_card
      intro other hother
      simp only [Finset.mem_filter] at hother ⊢
      exact ⟨hother.1, narrowData.subshading other hother.2.1,
        hother.2.2⟩
    exact hmono.trans_lt
      (hclose point hpointSource index
        (narrowData.subshading index hindex))
  have hnarrowMultiplicity : ∀ point ∈ narrow.union,
      narrow.pointMultiplicity point = source.pointMultiplicity point :=
    fun point hpoint => paper_narrow_pointMultiplicity_eq narrowData hpoint
  have hnarrowBudget : ∀ point ∈ narrow.union,
      let mu := narrow.pointMultiplicity point
      4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3 := by
    intro point hpoint
    have hm : m ≤ narrow.pointMultiplicity point := by
      rw [hnarrowMultiplicity point hpoint]
      have hpointSource : point ∈ source.union := by
        rcases hpoint with ⟨index, hindex⟩
        exact ⟨index, narrowData.subshading index hindex⟩
      exact hmultiplicity point hpointSource
    exact wz1_good_triple_budget m Q R
      (narrow.pointMultiplicity point) hm hQ hR
  rcases paper_cellwise_weak_planiness_from_narrow
      hdelta hkappa hfineNonempty hsourceCubical narrowData
      hnarrowClose hnarrowBudget with
    ⟨selected, _selection, planeMap, hselectedSub, hselectedCubical,
      hplaneCell, _hselectionCell, _hplaneSelection,
      hnarrowMultiplicityUpper, hselectedMass⟩
  have hselectedMultiplicityLower : ∀ point ∈ selected.union,
      2 * R ≤ selected.pointMultiplicity point := by
    intro point hpoint
    have hpointNarrow : point ∈ narrow.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hselectedSub index hindex⟩
    have hmNarrow : m ≤ narrow.pointMultiplicity point := by
      rw [hnarrowMultiplicity point hpointNarrow]
      have hpointSource : point ∈ source.union := by
        rcases hpointNarrow with ⟨index, hindex⟩
        exact ⟨index, narrowData.subshading index hindex⟩
      exact hmultiplicity point hpointSource
    have hfour : narrow.pointMultiplicity point ≤
        4 * selected.pointMultiplicity point :=
      hnarrowMultiplicityUpper point hpointNarrow
    omega
  have hselectedClose : ∀ k, k < N → ∀ point ∈ selected.union,
      ∀ index, point ∈ selected.carrier index →
        2 * paperCloseDirectionCount selected point index kappa ≤ 2 * R := by
    intro k _ point hpoint index hindex
    have hpointSource : point ∈ source.union := by
      exact ⟨index, narrowData.subshading index
        (hselectedSub index hindex)⟩
    have hmono : paperCloseDirectionCount selected point index kappa ≤
        paperCloseDirectionCount source point index kappa := by
      unfold paperCloseDirectionCount
      apply Finset.card_le_card
      intro other hother
      simp only [Finset.mem_filter] at hother ⊢
      exact ⟨hother.1, narrowData.subshading other
        (hselectedSub other hother.2.1), hother.2.2⟩
    have hstrict := hclose point hpointSource index
      (narrowData.subshading index (hselectedSub index hindex))
    omega
  have hincidenceNonnegative : 0 ≤ tau / kappa :=
    div_nonneg htau.le hkappa.le
  rcases paper_pure_nearby_cwa_fixed_plane_map_finite_lipschitz_coefficient
      hcwa selected hfineNonempty hline hselectedCubical
      planeMap hplaneCell (2 * R) hselectedMultiplicityLower
      N requested spatialScale variationScale (fun _ => kappa)
      densityPower hselectedClose hdensity hincidenceNonnegative
      hactualSmall hparentKappa K hK hspatialPositive
      hvariationPositive hspatialAligned hdelta hcoefficient hcovers with
    ⟨final, finalPlaneMapRaw, hfinalSub, hfinalPlaneMap, hfinalCubical,
      hfinalMultiplicity, hfinalLipschitzRaw, hfinalMass⟩
  have hfinalCell : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        finalPlaneMapRaw.planeMap first =
          finalPlaneMapRaw.planeMap second := by
    intro first second hgrid
    rw [hfinalPlaneMap]
    exact hplaneCell first second hgrid
  have hcoefficient :
      (1 / 4 : ENNReal) * (1 / 2 : ENNReal) = 1 / 8 := by
    simp only [one_div]
    have hmul : (4 : ENNReal) * 2 = 8 := by norm_num
    have hinv : ((4 : ENNReal) * 2)⁻¹ =
        (4 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ := by
      rw [ENNReal.mul_inv] <;> norm_num
    rw [hmul] at hinv
    exact hinv.symm
  have hbaseMass : (1 / 8 : ENNReal) * source.mass ≤ selected.mass := by
    calc
      (1 / 8 : ENNReal) * source.mass =
          (1 / 4 : ENNReal) * ((1 / 2 : ENNReal) * source.mass) := by
            rw [← mul_assoc, hcoefficient]
      _ ≤ (1 / 4 : ENNReal) * narrow.mass := by
        exact mul_le_mul_left' narrowData.mass_lower _
      _ ≤ selected.mass := hselectedMass
  have hmass :
      (1 / 8 : ENNReal) *
          (∏ k ∈ Finset.range N, densityPower k ^ 2) * source.mass ≤
        (∏ k ∈ Finset.range N,
          27 * (2 *
            (wz1OrientationCapCount
              (10 *
                  (tau / kappa +
                    4 * (hcwa.chosenNearby (requested k)).rho) /
                (kappa -
                  8 * (hcwa.chosenNearby (requested k)).rho))
              (variationScale k) : ENNReal))) *
          27 * final.mass := by
    calc
      (1 / 8 : ENNReal) *
          (∏ k ∈ Finset.range N, densityPower k ^ 2) * source.mass =
          (∏ k ∈ Finset.range N, densityPower k ^ 2) *
            ((1 / 8 : ENNReal) * source.mass) := by ring
      _ ≤ (∏ k ∈ Finset.range N, densityPower k ^ 2) *
          selected.mass := by gcongr
      _ ≤ (∏ k ∈ Finset.range N,
          27 * (2 *
            (wz1OrientationCapCount
              (10 *
                  (tau / kappa +
                    4 * (hcwa.chosenNearby (requested k)).rho) /
                (kappa -
                  8 * (hcwa.chosenNearby (requested k)).rho))
              (variationScale k) : ENNReal))) *
          27 * final.mass := hfinalMass
  exact ⟨narrow, selected, final, finalPlaneMapRaw, narrowData.subshading,
    hselectedSub, hfinalSub, hselectedCubical, hfinalCubical,
    hfinalMultiplicity, hfinalCell, hfinalLipschitzRaw, hmass⟩

/-- The historical Lip-1 sparse wrapper, now a specialization of the
quantitative terminal bridge. -/
theorem paper_pure_sparse_variable_q_weak_finite_lipschitz
    {delta tau kappa : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {nearbyConstant cvConstant multiplicityUpper : ENNReal}
    (hcwa : WZ2PaperPureCWAAtNearbyScales fine nearbyConstant)
    (source : WZ1PaperTubeShading fine)
    (hfineNonempty : fine.Nonempty)
    (hline : WZ1PaperIsLineClass fine)
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (m Q R : ℕ)
    (hmultiplicity : ∀ point ∈ source.union,
      m ≤ source.pointMultiplicity point)
    (hQpos : 0 < Q)
    (hQ : 4 * Q ≤ m ^ 3)
    (hR : 12 * R ≤ m)
    (hclose : ∀ point ∈ source.union, ∀ index,
      point ∈ source.carrier index →
      paperCloseDirectionCount source point index kappa < R)
    (hCV : ∀ (E : Set Point3), MeasurableSet E → E ⊆ source.union →
      ∀ (L : ENNReal),
        (∀ point ∈ E,
          L ≤ (paperShadingTrilinearMultiplicity source point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          cvConstant *
            (ENNReal.ofReal (delta ^ 2) * fine.enncard) ^
              (3 / 2 : ℝ))
    (hmultiplicityUpper : ∀ point ∈ source.union,
      (source.pointMultiplicity point : ENNReal) ≤ multiplicityUpper)
    (hdelta : 0 < delta)
    (htau : 0 < tau)
    (hkappa : 0 < kappa)
    (habsorb :
      (2 : ENNReal) * multiplicityUpper * cvConstant *
          (ENNReal.ofReal (delta ^ 2) * fine.enncard) ^
            (3 / 2 : ℝ) ≤
        (((Q : ENNReal) * ENNReal.ofReal tau) ^
          (1 / 2 : ℝ)) * source.mass)
    (densityPower : ℕ → ENNReal)
    (N : ℕ)
    (requested : ℕ → WZ2PaperRequestedScale delta)
    (spatialScale variationScale : ℕ → ℝ)
    (hdensity : ∀ k, k < N →
      densityPower k * fine.enncard ≤ (2 * R : ℕ))
    (hactualSmall : ∀ k, k < N →
      (hcwa.chosenNearby (requested k)).rho < 1 / 8)
    (hparentKappa : ∀ k, k < N →
      8 * (hcwa.chosenNearby (requested k)).rho < kappa)
    (K : ℕ → ℕ)
    (hK : ∀ k, k < N → 0 < K k)
    (hspatialPositive : ∀ k, k < N → 0 < spatialScale k)
    (hvariationPositive : ∀ k, k < N → 0 < variationScale k)
    (hspatialAligned : ∀ k, k < N →
      spatialScale k = (K k : ℝ) * delta)
    (hcovers : ∀ d : ℝ, delta < d → d < 2 →
      ∃ k, k < N ∧ d ≤ spatialScale k ∧ variationScale k ≤ d) :
    ∃ (narrow selected final : WZ1PaperTubeShading fine)
      (finalPlaneMap : PaperWZ1WeakPlaneMapData final (tau / kappa)),
      PaperIsSubshading narrow source ∧
      PaperIsSubshading selected narrow ∧
      PaperIsSubshading final selected ∧
      WZ1PaperIsCubicalShading selected ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point = selected.pointMultiplicity point) ∧
      LipschitzWith 1
        (fun point : {point : Point3 // point ∈ final.union} =>
          finalPlaneMap.planeMap point) ∧
      (1 / 8 : ENNReal) *
          (∏ k ∈ Finset.range N, densityPower k ^ 2) * source.mass ≤
        (∏ k ∈ Finset.range N,
          27 * (2 *
            (wz1OrientationCapCount
              (10 *
                  (tau / kappa +
                    4 * (hcwa.chosenNearby (requested k)).rho) /
                (kappa -
                  8 * (hcwa.chosenNearby (requested k)).rho))
              (variationScale k) : ENNReal))) *
          27 * final.mass := by
  rcases paper_pure_sparse_variable_q_weak_finite_lipschitz_coefficient
      (coefficient := (1 : ℝ)) hcwa source hfineNonempty hline
      hsourceCubical m Q R hmultiplicity hQpos hQ hR hclose hCV
      hmultiplicityUpper hdelta htau hkappa (by norm_num) habsorb
      densityPower N requested spatialScale variationScale hdensity
      hactualSmall hparentKappa K hK hspatialPositive hvariationPositive
      hspatialAligned (by
        intro d hdeltaD _ hunit
        have hdTwo : d < 2 := by simpa using hunit
        rcases hcovers d hdeltaD hdTwo with ⟨k, hk, hd, hvariation⟩
        exact ⟨k, hk, hd, by simpa using hvariation⟩) with
    ⟨narrow, selected, final, planeMap, hnarrowSub, hselectedSub,
      hfinalSub, hselectedCubical, hfinalCubical, hmultiplicityFinal,
      _hcell, hlipschitz, hmass⟩
  exact ⟨narrow, selected, final, planeMap, hnarrowSub, hselectedSub,
    hfinalSub, hselectedCubical, hfinalCubical, hmultiplicityFinal,
    by simpa using hlipschitz, hmass⟩

end Kakeya.Assouad.PureWZ2

end
