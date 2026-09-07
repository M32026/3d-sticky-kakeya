import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureAmplifiedOneScaleVariation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiplicityPreservingVariation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteNestedVariationIteration

/-!
# Fixed-map finite iteration through pure covers

Multiplicity-preserving common spatial restrictions keep the active tube
indices unchanged at every surviving point.  Thus the pure one-scale theorem
can be applied successively to one fixed plane map and one fixed source
shading, while all previous variation estimates survive.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Finite nested variation bookkeeping with separate spatial and plane-map
scales. -/
theorem paper_finite_nested_asymmetric_variation_iteration
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading F)
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (planeMap : Point3 → Point3)
    (N : ℕ)
    (spatialScale variationScale : ℕ → ℝ)
    (leftFactor rightFactor : ℕ → ENNReal)
    (step : ∀ k, k < N → ∀ current : WZ1PaperTubeShading F,
      PaperIsSubshading current source →
      WZ1PaperIsCubicalShading current →
      (∀ p ∈ current.union,
        current.pointMultiplicity p = source.pointMultiplicity p) →
      ∃ next : WZ1PaperTubeShading F,
        PaperIsSubshading next current ∧
        WZ1PaperIsCubicalShading next ∧
        (∀ p ∈ next.union,
          next.pointMultiplicity p = current.pointMultiplicity p) ∧
        (∀ p ∈ next.union, ∀ q ∈ next.union,
          dist p q ≤ spatialScale k →
            dist (planeMap p) (planeMap q) ≤ variationScale k) ∧
        leftFactor k * current.mass ≤ rightFactor k * next.mass) :
    ∃ final : WZ1PaperTubeShading F,
      PaperIsSubshading final source ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ p ∈ final.union,
        final.pointMultiplicity p = source.pointMultiplicity p) ∧
      (∀ k, k < N → ∀ p ∈ final.union, ∀ q ∈ final.union,
        dist p q ≤ spatialScale k →
          dist (planeMap p) (planeMap q) ≤ variationScale k) ∧
      (∏ k ∈ Finset.range N, leftFactor k) * source.mass ≤
        (∏ k ∈ Finset.range N, rightFactor k) * final.mass := by
  let P : ℕ → Prop := fun m =>
    ∃ current : WZ1PaperTubeShading F,
      PaperIsSubshading current source ∧
      WZ1PaperIsCubicalShading current ∧
      (∀ p ∈ current.union,
        current.pointMultiplicity p = source.pointMultiplicity p) ∧
      (∀ k, k < m → k < N → ∀ p ∈ current.union, ∀ q ∈ current.union,
        dist p q ≤ spatialScale k →
          dist (planeMap p) (planeMap q) ≤ variationScale k) ∧
      (∏ k ∈ Finset.range m, leftFactor k) * source.mass ≤
        (∏ k ∈ Finset.range m, rightFactor k) * current.mass
  have hbase : P 0 := by
    refine ⟨source, fun _ => Set.Subset.rfl, hsourceCubical, ?_, ?_, ?_⟩
    · intro p _
      rfl
    · intro k hk
      omega
    · simp
  have hnext : ∀ m, m < N → P m → P (m + 1) := by
    intro m hm hPm
    rcases hPm with
      ⟨current, hcurrentSub, hcurrentCubical, hcurrentMultiplicity,
        hcurrentVariation, hcurrentMass⟩
    rcases step m hm current hcurrentSub hcurrentCubical
        hcurrentMultiplicity with
      ⟨next, hnextSub, hnextCubical, hnextMultiplicityCurrent,
        hnextVariation, hnextMass⟩
    have hnextSubSource : PaperIsSubshading next source := fun index =>
      (hnextSub index).trans (hcurrentSub index)
    have hnextMultiplicity : ∀ p ∈ next.union,
        next.pointMultiplicity p = source.pointMultiplicity p := by
      intro p hp
      have hpCurrent : p ∈ current.union := by
        rcases hp with ⟨index, hindex⟩
        exact ⟨index, hnextSub index hindex⟩
      exact (hnextMultiplicityCurrent p hp).trans
        (hcurrentMultiplicity p hpCurrent)
    have hvariation : ∀ k, k < m + 1 → k < N →
        ∀ p ∈ next.union, ∀ q ∈ next.union,
          dist p q ≤ spatialScale k →
            dist (planeMap p) (planeMap q) ≤ variationScale k := by
      intro k hk hNk p hp q hq hpq
      by_cases hkm : k = m
      · subst hkm
        exact hnextVariation p hp q hq hpq
      · have hkOld : k < m := by omega
        have hpCurrent : p ∈ current.union := by
          rcases hp with ⟨index, hindex⟩
          exact ⟨index, hnextSub index hindex⟩
        have hqCurrent : q ∈ current.union := by
          rcases hq with ⟨index, hindex⟩
          exact ⟨index, hnextSub index hindex⟩
        exact hcurrentVariation k hkOld hNk p hpCurrent q hqCurrent hpq
    have hmass :
        (∏ k ∈ Finset.range (m + 1), leftFactor k) * source.mass ≤
          (∏ k ∈ Finset.range (m + 1), rightFactor k) * next.mass := by
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      calc
        ((∏ k ∈ Finset.range m, leftFactor k) * leftFactor m) *
            source.mass =
          leftFactor m *
            ((∏ k ∈ Finset.range m, leftFactor k) * source.mass) := by ring
        _ ≤ leftFactor m *
            ((∏ k ∈ Finset.range m, rightFactor k) * current.mass) := by
          gcongr
        _ = (∏ k ∈ Finset.range m, rightFactor k) *
            (leftFactor m * current.mass) := by ring
        _ ≤ (∏ k ∈ Finset.range m, rightFactor k) *
            (rightFactor m * next.mass) := by gcongr
        _ = ((∏ k ∈ Finset.range m, rightFactor k) * rightFactor m) *
            next.mass := by ring
    exact ⟨next, hnextSubSource, hnextCubical, hnextMultiplicity,
      hvariation, hmass⟩
  have hinduction : ∀ m, m ≤ N → P m := by
    intro m hm
    induction m with
    | zero => exact hbase
    | succ m ih => exact hnext m (by omega) (ih (by omega))
  rcases hinduction N le_rfl with
    ⟨final, hfinalSub, hfinalCubical, hfinalMultiplicity,
      hfinalVariation, hfinalMass⟩
  exact ⟨final, hfinalSub, hfinalCubical, hfinalMultiplicity,
    (fun k hk => hfinalVariation k hk hk), hfinalMass⟩

/-- Apply one pure-cover variation step to a current multiplicity-preserving
subshading of the fixed source. -/
theorem paper_pure_fixed_plane_map_one_scale_variation
    {delta parentRadius spatialScale variationScale kappa incidence : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily parentRadius}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    {source current : WZ1PaperTubeShading fine}
    (hfineNonempty : fine.Nonempty)
    (hline : WZ1PaperIsLineClass fine)
    (planeMap : PaperWZ1WeakPlaneMapData source incidence)
    (hplaneCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second)
    (hcurrentSub : PaperIsSubshading current source)
    (hcurrentCubical : WZ1PaperIsCubicalShading current)
    (hcurrentMultiplicity : ∀ point ∈ current.union,
      current.pointMultiplicity point = source.pointMultiplicity point)
    (fineMultiplicity : ℕ)
    (hFineMultiplicity : ∀ point ∈ source.union,
      fineMultiplicity ≤ source.pointMultiplicity point)
    (hclose : ∀ point ∈ source.union, ∀ index,
      point ∈ source.carrier index →
      2 * paperCloseDirectionCount source point index kappa ≤
        fineMultiplicity)
    (densityPower : ENNReal)
    (hdensity : densityPower * fine.enncard ≤
      (fineMultiplicity : ENNReal))
    (hincidenceNonnegative : 0 ≤ incidence)
    (hparentRadius : 0 < parentRadius)
    (hparentRadiusSmall : parentRadius < 1 / 8)
    (hspatialScale : 0 < spatialScale)
    (hvariationScale : 0 < variationScale)
    (hkappa : 8 * parentRadius < kappa)
    (K : ℕ) (hK : 0 < K)
    (hspatialScaleAligned : spatialScale = (K : ℝ) * delta) :
    ∃ next : WZ1PaperTubeShading fine,
      PaperIsSubshading next current ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = current.pointMultiplicity point) ∧
      (∀ point ∈ next.union, ∀ other ∈ next.union,
        dist point other ≤ spatialScale →
          dist (planeMap.planeMap point)
            (planeMap.planeMap other) ≤ variationScale) ∧
      densityPower ^ 2 * current.mass ≤
        27 * (2 *
          (wz1OrientationCapCount
            (10 * (incidence + 4 * parentRadius) /
              (kappa - 8 * parentRadius)) variationScale :
              ENNReal)) * next.mass := by
  let currentPlaneMap :=
    PureWZ2.paperWeakPlaneMapRestrict planeMap hcurrentSub
  have hcurrentFineMultiplicity : ∀ point ∈ current.union,
      fineMultiplicity ≤ current.pointMultiplicity point := by
    intro point hpoint
    have hpointSource : point ∈ source.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hcurrentSub index hindex⟩
    rw [hcurrentMultiplicity point hpoint]
    exact hFineMultiplicity point hpointSource
  have hcurrentClose : ∀ point ∈ current.union, ∀ index,
      point ∈ current.carrier index →
      2 * paperCloseDirectionCount current point index kappa ≤
        fineMultiplicity := by
    intro point hpoint index hindex
    rw [PureWZ2.paper_closeDirectionCount_eq_of_subshading_of_multiplicity_eq
      hcurrentSub hpoint (hcurrentMultiplicity point hpoint) index]
    have hpointSource : point ∈ source.union :=
      ⟨index, hcurrentSub index hindex⟩
    exact hclose point hpointSource index (hcurrentSub index hindex)
  rcases paper_pure_amplified_one_scale_nearby_variation_cancel_cardinality
      cover hfineNonempty hline hcurrentCubical currentPlaneMap hplaneCell
      fineMultiplicity hcurrentFineMultiplicity hcurrentClose densityPower
      hdensity hincidenceNonnegative hparentRadius hparentRadiusSmall
      hspatialScale hvariationScale hkappa K hK hspatialScaleAligned with
    ⟨next, hnextSub, hnextCubical, hvariation, hnextMultiplicity, hmass⟩
  exact ⟨next, hnextSub, hnextCubical, hnextMultiplicity, hvariation, hmass⟩

/-- Lemma 16 bookkeeping specialized to a finite list of pure nearby-scale
covers.  All scale variation estimates refer to the original plane map. -/
theorem paper_pure_fixed_plane_map_finite_nested_variation
    {delta incidence : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
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
    (parentScale spatialScale variationScale kappa : ℕ → ℝ)
    (coarse : ∀ k, Kakeya.Streamlined.TubeFamily (parentScale k))
    (cover : ∀ k, WZ2PaperPurePartitioningCover fine (coarse k))
    (densityPower : ℕ → ENNReal)
    (hclose : ∀ k, k < N → ∀ point ∈ source.union, ∀ index,
      point ∈ source.carrier index →
      2 * paperCloseDirectionCount source point index (kappa k) ≤
        fineMultiplicity)
    (hdensity : ∀ k, k < N →
      densityPower k * fine.enncard ≤ (fineMultiplicity : ENNReal))
    (hincidenceNonnegative : 0 ≤ incidence)
    (hparentScalePositive : ∀ k, k < N → 0 < parentScale k)
    (hparentScaleSmall : ∀ k, k < N → parentScale k < 1 / 8)
    (hspatialScalePositive : ∀ k, k < N → 0 < spatialScale k)
    (hvariationScalePositive : ∀ k, k < N → 0 < variationScale k)
    (hkappa : ∀ k, k < N → 8 * parentScale k < kappa k)
    (K : ℕ → ℕ)
    (hK : ∀ k, k < N → 0 < K k)
    (hspatialScaleAligned : ∀ k, k < N →
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
              (10 * (incidence + 4 * parentScale k) /
                (kappa k - 8 * parentScale k)) (variationScale k) :
                  ENNReal))) *
          final.mass := by
  let rightFactor : ℕ → ENNReal := fun k =>
    27 * (2 *
      (wz1OrientationCapCount
        (10 * (incidence + 4 * parentScale k) /
          (kappa k - 8 * parentScale k)) (variationScale k) : ENNReal))
  apply paper_finite_nested_asymmetric_variation_iteration
    source hsourceCubical planeMap.planeMap N spatialScale variationScale
      (fun k => densityPower k ^ 2) rightFactor
  intro k hk current hcurrentSub hcurrentCubical hcurrentMultiplicity
  exact paper_pure_fixed_plane_map_one_scale_variation
    (cover k) hfineNonempty hline planeMap hplaneCell hcurrentSub
    hcurrentCubical hcurrentMultiplicity fineMultiplicity hFineMultiplicity
    (hclose k hk) (densityPower k) (hdensity k hk)
    hincidenceNonnegative (hparentScalePositive k hk)
    (hparentScaleSmall k hk) (hspatialScalePositive k hk)
    (hvariationScalePositive k hk) (hkappa k hk)
    (K k) (hK k hk) (hspatialScaleAligned k hk)

end Kakeya.Assouad

end
