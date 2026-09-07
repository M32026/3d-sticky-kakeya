import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DenseLocalDirectionRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureDenseFiniteVariation

/-!
# Dense local caps followed by finite nearby-scale coordination

The dense branch first restricts, independently in every fine spatial cell,
to one direction cap of diameter `eta`.  Its stable vertical normal therefore
has incidence at most `eta`.  The existing pure nearby-cover iteration then
coordinates that same plane map at finitely many spatial scales and produces
a genuinely `1`-Lipschitz final restriction.

All losses are explicit.  In particular, this construction stays on the
original tube family and does not use isotropic rediscretization or a
constant plane map.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Localize a dense direction cluster to incidence `eta`, then coordinate
the resulting stable-normal map through finitely many pure nearby covers. -/
theorem paper_pure_dense_localized_finite_lipschitz_coefficient
    {delta kappa eta coefficient : ℝ}
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
        (fine.tube index).direction‖ < kappa)
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
    (hdelta : 0 < delta)
    (heta : 0 < eta)
    (hetaHalf : eta ≤ 1 / 2)
    (hcoefficient : 0 < coefficient)
    (hactualSmall : ∀ k, k < N →
      (hcwa.chosenNearby (requested k)).rho < 1 / 8)
    (hspatialScale : ∀ k, k < N → 0 < spatialScale k)
    (hvariationScale : ∀ k, k < N → 0 < variationScale k)
    (K : ℕ → ℕ)
    (hK : ∀ k, k < N → 0 < K k)
    (hspatialScaleAligned : ∀ k, k < N →
      spatialScale k = (K k : ℝ) * delta)
    (hcovers : ∀ d : ℝ, delta < d → d ≤ 4 → coefficient * d < 2 →
      ∃ k, k < N ∧ d ≤ spatialScale k ∧
        variationScale k ≤ coefficient * d) :
    ∃ (localized final : WZ1PaperTubeShading fine)
      (localCenter : Point3 → Fin fine.card)
      (finalPlaneMap : PaperWZ1WeakPlaneMapData final eta),
      PaperIsSubshading localized source ∧
      PaperIsSubshading final localized ∧
      WZ1PaperIsCubicalShading localized ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        source.pointMultiplicity point ≤
          denseLocalDirectionLabelCount kappa eta *
            final.pointMultiplicity point) ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
            wz1PaperGridIndex delta second →
          finalPlaneMap.planeMap first = finalPlaneMap.planeMap second) ∧
      LipschitzWith (Real.toNNReal coefficient)
        (fun point : {point : Point3 // point ∈ final.union} =>
          finalPlaneMap.planeMap point) ∧
      (∏ k ∈ Finset.range N, densityPower k) * source.mass ≤
        (denseLocalDirectionLabelCount kappa eta : ENNReal) *
          (∏ k ∈ Finset.range N,
            (localPlaneMapCapCount
              (8 * eta +
                16 * (hcwa.chosenNearby (requested k)).rho)
              (variationScale k) : ENNReal) *
              27 *
                (multiplicityCoefficient k *
                  (denseLocalDirectionLabelCount kappa eta : ENNReal))) *
          27 * final.mass := by
  rcases paper_dense_local_direction_refinement
      hdelta heta hkappaNonnegative hkappaHalf hline hsourceCubical
      center hcenterMeasurable hcenterCell hcluster with
    ⟨localized, localCenter, hlocalizedSub, hlocalizedCubical,
      hlocalCenterMeasurable, hlocalCenterCell, hlocalCenterMem,
      hlocalDirections, hlocalMultiplicity, hlocalMass⟩
  let localCount : ENNReal :=
    (denseLocalDirectionLabelCount kappa eta : ENNReal)
  have hlocalCluster : ∀ index point,
      point ∈ localized.carrier index →
      ‖wz1Cross (fine.tube (localCenter point)).direction
        (fine.tube index).direction‖ ≤ eta := by
    intro index point hpoint
    have hpointUnion : point ∈ localized.union := ⟨index, hpoint⟩
    have hdirection := hlocalDirections point hpointUnion
      (localCenter point) index (hlocalCenterMem point hpointUnion) hpoint
    have hcrossPaper : ‖wz1Cross
        (wz1PaperDirection (fine.tube (localCenter point)))
        (wz1PaperDirection (fine.tube index))‖ ≤ eta := by
      let u := wz1PaperDirection (fine.tube (localCenter point))
      let v := wz1PaperDirection (fine.tube index)
      have heq : wz1Cross u v = wz1Cross (u - v) v := by
        have hdecomp : u = (u - v) + v := by abel
        rw [hdecomp, wz1Cross_add_left]
        simp [wz1Cross]
      rw [heq]
      exact (wz1Cross_norm_le (u - v) v).trans <| by
        rw [wz1PaperDirection_norm, mul_one]
        exact hdirection
    rw [raw_cross_norm_eq_paper_cross_norm]
    exact hcrossPaper
  have hlocalizedDensity : ∀ k, k < N →
      ∀ point ∈ localized.union,
        densityPower k * fine.enncard ≤
          (multiplicityCoefficient k * localCount) *
            (localized.pointMultiplicity point : ENNReal) := by
    intro k hk point hpoint
    have hpointSource : point ∈ source.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hlocalizedSub index hindex⟩
    have hmultNat := hlocalMultiplicity point hpointSource
    have hmultENN : (source.pointMultiplicity point : ENNReal) ≤
        localCount * (localized.pointMultiplicity point : ENNReal) := by
      have hcast : (source.pointMultiplicity point : ENNReal) ≤
          ((denseLocalDirectionLabelCount kappa eta *
            localized.pointMultiplicity point : ℕ) : ENNReal) := by
        exact_mod_cast hmultNat
      simpa [localCount, Nat.cast_mul] using hcast
    calc
      densityPower k * fine.enncard ≤
          multiplicityCoefficient k *
            (source.pointMultiplicity point : ENNReal) :=
        hdensityPoint k hk point hpointSource
      _ ≤ multiplicityCoefficient k *
          (localCount *
            (localized.pointMultiplicity point : ENNReal)) := by gcongr
      _ = (multiplicityCoefficient k * localCount) *
          (localized.pointMultiplicity point : ENNReal) := by ring
  rcases paper_pure_nearby_cwa_dense_finite_lipschitz_coefficient
      hcwa localized hfineNonempty hline hlocalizedCubical
      localCenter hlocalCenterMeasurable hlocalCenterCell hlocalCluster
      (fun k => multiplicityCoefficient k * localCount) densityPower N
      requested spatialScale variationScale hlocalizedDensity
      heta.le hetaHalf hactualSmall hspatialScale hvariationScale
      K hK hspatialScaleAligned hdelta hcoefficient hcovers with
    ⟨final, finalPlaneMap, hfinalSub, hfinalCubical,
      hfinalMultiplicity, hfinalCellwise, hfinalLipschitz, hfinalMass⟩
  have hsourceMultiplicity : ∀ point ∈ final.union,
      source.pointMultiplicity point ≤
        denseLocalDirectionLabelCount kappa eta *
          final.pointMultiplicity point := by
    intro point hpoint
    have hpointLocalized : point ∈ localized.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hfinalSub index hindex⟩
    have hsource := hlocalMultiplicity point <| by
      rcases hpointLocalized with ⟨index, hindex⟩
      exact ⟨index, hlocalizedSub index hindex⟩
    rw [← hfinalMultiplicity point hpoint] at hsource
    exact hsource
  have hmass :
      (∏ k ∈ Finset.range N, densityPower k) * source.mass ≤
        localCount *
          (∏ k ∈ Finset.range N,
            (localPlaneMapCapCount
              (8 * eta +
                16 * (hcwa.chosenNearby (requested k)).rho)
              (variationScale k) : ENNReal) *
              27 * (multiplicityCoefficient k * localCount)) *
          27 * final.mass := by
    calc
      (∏ k ∈ Finset.range N, densityPower k) * source.mass ≤
          (∏ k ∈ Finset.range N, densityPower k) *
            (localCount * localized.mass) := by gcongr
      _ = localCount *
          ((∏ k ∈ Finset.range N, densityPower k) *
            localized.mass) := by ring
      _ ≤ localCount *
          ((∏ k ∈ Finset.range N,
            (localPlaneMapCapCount
              (8 * eta +
                16 * (hcwa.chosenNearby (requested k)).rho)
              (variationScale k) : ENNReal) *
              27 * (multiplicityCoefficient k * localCount)) *
            27 * final.mass) := by gcongr
      _ = localCount *
          (∏ k ∈ Finset.range N,
            (localPlaneMapCapCount
              (8 * eta +
                16 * (hcwa.chosenNearby (requested k)).rho)
              (variationScale k) : ENNReal) *
              27 * (multiplicityCoefficient k * localCount)) *
          27 * final.mass := by ring
  exact ⟨localized, final, localCenter, finalPlaneMap, hlocalizedSub,
    hfinalSub, hlocalizedCubical, hfinalCubical, hsourceMultiplicity,
    hfinalCellwise, hfinalLipschitz, by simpa [localCount] using hmass⟩

end Kakeya.Assouad.PureWZ2

end
