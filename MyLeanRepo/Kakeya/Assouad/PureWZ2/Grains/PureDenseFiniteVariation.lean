import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureDenseParentVariation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureFiniteNestedVariation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureNearbyFiniteVariation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteScaleLipschitzBridge

/-!
# Finite dense-cluster variation through pure covers

The dense branch uses one fixed, genuine stable-normal plane map. At every
requested spatial scale, a pure strict-carrier cover selects one parent per
cell. The resulting restrictions are nested, preserve the active tube set at
surviving points, and retain all earlier variation estimates.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Iterate the asymmetric dense-parent variation estimate through finitely
many pure covers. -/
theorem paper_pure_dense_parent_finite_nested_variation
    {delta kappa : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading fine)
    (hfineNonempty : fine.Nonempty)
    (hline : WZ1PaperIsLineClass fine)
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (center : Point3 → Fin fine.card)
    (hcenterMeasurable : Measurable center)
    (hcenterCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      center first = center second)
    (hcluster : ∀ index point, point ∈ source.carrier index →
      ‖wz1Cross (fine.tube (center point)).direction
        (fine.tube index).direction‖ ≤ kappa)
    (multiplicityCoefficient densityPower : ℕ → ENNReal)
    (N : ℕ)
    (parentRadius spatialScale variationScale : ℕ → ℝ)
    (coarse : ∀ k, Kakeya.Streamlined.TubeFamily (parentRadius k))
    (cover : ∀ k, WZ2PaperPurePartitioningCover fine (coarse k))
    (hdensityPoint : ∀ k, k < N → ∀ point ∈ source.union,
      densityPower k * fine.enncard ≤
        multiplicityCoefficient k *
          (source.pointMultiplicity point : ENNReal))
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (hparentRadius : ∀ k, k < N → 0 < parentRadius k)
    (hparentRadiusSmall : ∀ k, k < N → parentRadius k < 1 / 8)
    (hspatialScale : ∀ k, k < N → 0 < spatialScale k)
    (hvariationScale : ∀ k, k < N → 0 < variationScale k)
    (K : ℕ → ℕ)
    (hK : ∀ k, k < N → 0 < K k)
    (hspatialScaleAligned : ∀ k, k < N →
      spatialScale k = (K k : ℝ) * delta) :
    ∃ (planeMap : PaperWZ1WeakPlaneMapData source kappa)
      (final : WZ1PaperTubeShading fine),
      (∀ point, planeMap.planeMap point =
        stableVerticalNormal
          (wz1PaperDirection (fine.tube (center point)))) ∧
      PaperIsSubshading final source ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point = source.pointMultiplicity point) ∧
      (∀ k, k < N → ∀ point ∈ final.union, ∀ other ∈ final.union,
        dist point other ≤ spatialScale k →
          dist (planeMap.planeMap point)
            (planeMap.planeMap other) ≤ variationScale k) ∧
      (∏ k ∈ Finset.range N, densityPower k) * source.mass ≤
        (∏ k ∈ Finset.range N,
          (localPlaneMapCapCount
            (8 * kappa + 16 * parentRadius k) (variationScale k) : ENNReal) *
            27 * multiplicityCoefficient k) * final.mass := by
  let planeMap : PaperWZ1WeakPlaneMapData source kappa :=
    { planeMap := fun point =>
        stableVerticalNormal
          (wz1PaperDirection (fine.tube (center point)))
      measurable := by
        have hfinite : Measurable fun index : Fin fine.card =>
            stableVerticalNormal
              (wz1PaperDirection (fine.tube index)) :=
          measurable_of_finite _
        exact hfinite.comp hcenterMeasurable
      unit := by
        intro point _
        apply stableVerticalNormal_unit
        exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
          (paper_direction_cross_axis_lower (hline (center point)))
      incidence := by
        intro index point hpoint
        have hcenterCross : 0 < ‖wz1Cross
            (wz1PaperDirection (fine.tube (center point)))
            verticalNormalAxis‖ :=
          (by norm_num : (0 : ℝ) < 1 / 2).trans_le
            (paper_direction_cross_axis_lower (hline (center point)))
        have hpaperCross : ‖wz1Cross
            (wz1PaperDirection (fine.tube (center point)))
            (wz1PaperDirection (fine.tube index))‖ ≤ kappa := by
          rw [← raw_cross_norm_eq_paper_cross_norm]
          exact hcluster index point hpoint
        rw [abs_inner_raw_eq_paperDirection]
        exact (stableVerticalNormal_incidence
          (wz1PaperDirection (fine.tube (center point)))
          (wz1PaperDirection (fine.tube index))
          (wz1PaperDirection_norm _) (wz1PaperDirection_norm _)
          hcenterCross).trans hpaperCross }
  let rightFactor : ℕ → ENNReal := fun k =>
    (localPlaneMapCapCount
      (8 * kappa + 16 * parentRadius k) (variationScale k) : ENNReal) *
      27 * multiplicityCoefficient k
  have hiteration :
      ∃ final : WZ1PaperTubeShading fine,
        PaperIsSubshading final source ∧
        WZ1PaperIsCubicalShading final ∧
        (∀ point ∈ final.union,
          final.pointMultiplicity point = source.pointMultiplicity point) ∧
        (∀ k, k < N → ∀ point ∈ final.union, ∀ other ∈ final.union,
          dist point other ≤ spatialScale k →
            dist (planeMap.planeMap point)
              (planeMap.planeMap other) ≤ variationScale k) ∧
        (∏ k ∈ Finset.range N, densityPower k) * source.mass ≤
          (∏ k ∈ Finset.range N, rightFactor k) * final.mass := by
    apply paper_finite_nested_asymmetric_variation_iteration
      source hsourceCubical planeMap.planeMap N spatialScale variationScale
        densityPower rightFactor
    intro k hk current hcurrentSub hcurrentCubical hcurrentMultiplicity
    have hcurrentDensity : ∀ point ∈ current.union,
        densityPower k * fine.enncard ≤
          multiplicityCoefficient k *
            (current.pointMultiplicity point : ENNReal) := by
      intro point hpoint
      have hpointSource : point ∈ source.union := by
        rcases hpoint with ⟨index, hindex⟩
        exact ⟨index, hcurrentSub index hindex⟩
      rw [hcurrentMultiplicity point hpoint]
      exact hdensityPoint k hk point hpointSource
    have hcurrentCluster : ∀ index point,
        point ∈ current.carrier index →
        ‖wz1Cross (fine.tube (center point)).direction
          (fine.tube index).direction‖ ≤ kappa := by
      intro index point hpoint
      exact hcluster index point (hcurrentSub index hpoint)
    rcases paper_pure_dense_parent_nearby_asymmetric_variation
        (cover k) hfineNonempty hline hcurrentCubical center
        hcenterMeasurable hcenterCell hcurrentCluster
        (multiplicityCoefficient k) (densityPower k) hcurrentDensity
        hkappaNonnegative hkappaHalf (hparentRadius k hk)
        (hparentRadiusSmall k hk) (hspatialScale k hk)
        (hvariationScale k hk) (K k) (hK k hk)
        (hspatialScaleAligned k hk) with
      ⟨stepPlaneMap, next, hstepPlaneMap, hnextSub, hnextCubical,
        hnextVariation, hnextMultiplicity, hnextMass⟩
    have hnextVariation' : ∀ point ∈ next.union, ∀ other ∈ next.union,
        dist point other ≤ spatialScale k →
          dist (planeMap.planeMap point)
            (planeMap.planeMap other) ≤ variationScale k := by
      intro point hpoint other hother hdist
      have hvariation :=
        hnextVariation point hpoint other hother hdist
      rw [hstepPlaneMap point, hstepPlaneMap other] at hvariation
      simpa [planeMap] using hvariation
    exact ⟨next, hnextSub, hnextCubical, hnextMultiplicity,
      hnextVariation', hnextMass⟩
  rcases hiteration with
    ⟨final, hfinalSub, hfinalCubical, hfinalMultiplicity,
      hfinalVariation, hfinalMass⟩
  exact ⟨planeMap, final, (fun _ => rfl), hfinalSub, hfinalCubical,
    hfinalMultiplicity, hfinalVariation, hfinalMass⟩

/-- Choose the finitely many actual pure nearby covers and finish the dense
branch with a genuine quantitatively Lipschitz stable-normal plane map. -/
theorem paper_pure_nearby_cwa_dense_finite_lipschitz_coefficient
    {delta kappa coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hcwa : WZ2PaperPureCWAAtNearbyScales fine C)
    (source : WZ1PaperTubeShading fine)
    (hfineNonempty : fine.Nonempty)
    (hline : WZ1PaperIsLineClass fine)
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (center : Point3 → Fin fine.card)
    (hcenterMeasurable : Measurable center)
    (hcenterCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      center first = center second)
    (hcluster : ∀ index point, point ∈ source.carrier index →
      ‖wz1Cross (fine.tube (center point)).direction
        (fine.tube index).direction‖ ≤ kappa)
    (multiplicityCoefficient densityPower : ℕ → ENNReal)
    (N : ℕ)
    (requested : ℕ → WZ2PaperRequestedScale delta)
    (spatialScale variationScale : ℕ → ℝ)
    (hdensityPoint : ∀ k, k < N → ∀ point ∈ source.union,
      densityPower k * fine.enncard ≤
        multiplicityCoefficient k *
          (source.pointMultiplicity point : ENNReal))
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (hactualSmall : ∀ k, k < N →
      (hcwa.chosenNearby (requested k)).rho < 1 / 8)
    (hspatialScale : ∀ k, k < N → 0 < spatialScale k)
    (hvariationScale : ∀ k, k < N → 0 < variationScale k)
    (K : ℕ → ℕ)
    (hK : ∀ k, k < N → 0 < K k)
    (hspatialScaleAligned : ∀ k, k < N →
      spatialScale k = (K k : ℝ) * delta)
    (hdelta : 0 < delta)
    (hcoefficient : 0 < coefficient)
    (hcovers : ∀ d : ℝ, delta < d → d ≤ 4 → coefficient * d < 2 →
      ∃ k, k < N ∧ d ≤ spatialScale k ∧
        variationScale k ≤ coefficient * d) :
    ∃ (final : WZ1PaperTubeShading fine)
      (finalPlaneMap : PaperWZ1WeakPlaneMapData final kappa),
      PaperIsSubshading final source ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point = source.pointMultiplicity point) ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
            wz1PaperGridIndex delta second →
          finalPlaneMap.planeMap first = finalPlaneMap.planeMap second) ∧
      LipschitzWith (Real.toNNReal coefficient)
        (fun point : {point : Point3 // point ∈ final.union} =>
          finalPlaneMap.planeMap point) ∧
      (∏ k ∈ Finset.range N, densityPower k) * source.mass ≤
        (∏ k ∈ Finset.range N,
          (localPlaneMapCapCount
            (8 * kappa + 16 * (hcwa.chosenNearby (requested k)).rho)
              (variationScale k) : ENNReal) *
            27 * multiplicityCoefficient k) * 27 * final.mass := by
  let nearby (k : ℕ) :
      WZ2PaperPureNearbyScaleCoverData fine (requested k) C :=
    hcwa.chosenNearby (requested k)
  rcases paper_pure_dense_parent_finite_nested_variation
      source hfineNonempty hline hsourceCubical center hcenterMeasurable
      hcenterCell hcluster multiplicityCoefficient densityPower N
      (fun k => (nearby k).rho) spatialScale variationScale
      (fun k => (nearby k).scaleData.coarse)
      (fun k => (nearby k).scaleData.cover) hdensityPoint
      hkappaNonnegative hkappaHalf
      (fun k _ => (nearby k).scaleData.rho_pos) hactualSmall
      hspatialScale hvariationScale K hK hspatialScaleAligned with
    ⟨planeMap, coordinated, hplaneMap, hcoordinatedSub, hcoordinatedCubical,
      hcoordinatedMultiplicity, hcoordinatedVariation,
      hcoordinatedMass⟩
  let coordinatedPlaneMap :=
    paperWeakPlaneMapRestrict planeMap hcoordinatedSub
  have hplaneCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      coordinatedPlaneMap.planeMap first =
        coordinatedPlaneMap.planeMap second := by
    intro first second hgrid
    change planeMap.planeMap first = planeMap.planeMap second
    rw [hplaneMap first, hplaneMap second]
    exact congrArg
      (fun index : Fin fine.card =>
        stableVerticalNormal
          (wz1PaperDirection (fine.tube index)))
      (hcenterCell first second hgrid)
  rcases paper_finite_scale_variation_to_lipschitz
      hdelta hcoefficient hcoordinatedCubical coordinatedPlaneMap hplaneCell
      N spatialScale variationScale hcoordinatedVariation
      (fun first hfirst second hsecond =>
        paper_shading_union_dist_le_four coordinated hfirst hsecond)
      hcovers with
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
  have hfinalCell : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        finalPlaneMap.planeMap first = finalPlaneMap.planeMap second := by
    intro first second hgrid
    rw [hfinalPlaneMap]
    exact hplaneCell first second hgrid
  have hfinalMass :
      (∏ k ∈ Finset.range N, densityPower k) * source.mass ≤
        (∏ k ∈ Finset.range N,
          (localPlaneMapCapCount
            (8 * kappa + 16 * (hcwa.chosenNearby (requested k)).rho)
              (variationScale k) : ENNReal) *
            27 * multiplicityCoefficient k) * 27 * final.mass := by
    calc
      (∏ k ∈ Finset.range N, densityPower k) * source.mass ≤
          (∏ k ∈ Finset.range N,
            (localPlaneMapCapCount
              (8 * kappa + 16 * (hcwa.chosenNearby (requested k)).rho)
                (variationScale k) : ENNReal) *
              27 * multiplicityCoefficient k) * coordinated.mass :=
        hcoordinatedMass
      _ ≤ (∏ k ∈ Finset.range N,
            (localPlaneMapCapCount
              (8 * kappa + 16 * (hcwa.chosenNearby (requested k)).rho)
                (variationScale k) : ENNReal) *
              27 * multiplicityCoefficient k) * (27 * final.mass) := by
        gcongr
      _ = (∏ k ∈ Finset.range N,
            (localPlaneMapCapCount
              (8 * kappa + 16 * (hcwa.chosenNearby (requested k)).rho)
                (variationScale k) : ENNReal) *
              27 * multiplicityCoefficient k) * 27 * final.mass := by ring
  exact ⟨final, finalPlaneMap, hfinalSub, hfinalCubical,
    hfinalMultiplicity, hfinalCell, hfinalLipschitz, hfinalMass⟩

/-- The historical Lip-1 dense wrapper, now a specialization of the
quantitative terminal bridge. -/
theorem paper_pure_nearby_cwa_dense_finite_lipschitz
    {delta kappa : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hcwa : WZ2PaperPureCWAAtNearbyScales fine C)
    (source : WZ1PaperTubeShading fine)
    (hfineNonempty : fine.Nonempty)
    (hline : WZ1PaperIsLineClass fine)
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (center : Point3 → Fin fine.card)
    (hcenterMeasurable : Measurable center)
    (hcenterCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      center first = center second)
    (hcluster : ∀ index point, point ∈ source.carrier index →
      ‖wz1Cross (fine.tube (center point)).direction
        (fine.tube index).direction‖ ≤ kappa)
    (multiplicityCoefficient densityPower : ℕ → ENNReal)
    (N : ℕ)
    (requested : ℕ → WZ2PaperRequestedScale delta)
    (spatialScale variationScale : ℕ → ℝ)
    (hdensityPoint : ∀ k, k < N → ∀ point ∈ source.union,
      densityPower k * fine.enncard ≤
        multiplicityCoefficient k *
          (source.pointMultiplicity point : ENNReal))
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (hactualSmall : ∀ k, k < N →
      (hcwa.chosenNearby (requested k)).rho < 1 / 8)
    (hspatialScale : ∀ k, k < N → 0 < spatialScale k)
    (hvariationScale : ∀ k, k < N → 0 < variationScale k)
    (K : ℕ → ℕ)
    (hK : ∀ k, k < N → 0 < K k)
    (hspatialScaleAligned : ∀ k, k < N →
      spatialScale k = (K k : ℝ) * delta)
    (hdelta : 0 < delta)
    (hcovers : ∀ d : ℝ, delta < d → d < 2 →
      ∃ k, k < N ∧ d ≤ spatialScale k ∧ variationScale k ≤ d) :
    ∃ (final : WZ1PaperTubeShading fine)
      (finalPlaneMap : PaperWZ1WeakPlaneMapData final kappa),
      PaperIsSubshading final source ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point = source.pointMultiplicity point) ∧
      LipschitzWith 1
        (fun point : {point : Point3 // point ∈ final.union} =>
          finalPlaneMap.planeMap point) ∧
      (∏ k ∈ Finset.range N, densityPower k) * source.mass ≤
        (∏ k ∈ Finset.range N,
          (localPlaneMapCapCount
            (8 * kappa + 16 * (hcwa.chosenNearby (requested k)).rho)
              (variationScale k) : ENNReal) *
            27 * multiplicityCoefficient k) * 27 * final.mass := by
  rcases paper_pure_nearby_cwa_dense_finite_lipschitz_coefficient
      (coefficient := (1 : ℝ)) hcwa source hfineNonempty hline
      hsourceCubical center hcenterMeasurable hcenterCell hcluster
      multiplicityCoefficient densityPower N requested spatialScale
      variationScale hdensityPoint hkappaNonnegative hkappaHalf
      hactualSmall hspatialScale hvariationScale K hK
      hspatialScaleAligned hdelta (by norm_num) (by
        intro d hdeltaD _ hunit
        have hdTwo : d < 2 := by simpa using hunit
        rcases hcovers d hdeltaD hdTwo with ⟨k, hk, hd, hvariation⟩
        exact ⟨k, hk, hd, by simpa using hvariation⟩) with
    ⟨final, planeMap, hsub, hcubical, hmultiplicity, _hcell,
      hlipschitz, hmass⟩
  exact ⟨final, planeMap, hsub, hcubical, hmultiplicity,
    by simpa using hlipschitz, hmass⟩

end Kakeya.Assouad.PureWZ2

end
