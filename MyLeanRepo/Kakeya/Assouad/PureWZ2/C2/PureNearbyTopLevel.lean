import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingJacobian
import MyLeanRepo.Kakeya.Assouad.PropStickyOrdinaryToCroppedShading
import MyLeanRepo.Kakeya.Assouad.Hairbrush.HomogeneousTwoEndsHelpers

/-!
# Top-level CWA from pure nearby-scale CWA

This is the top-scale specialization of the public pure Definition 2.12
condition used in the Proposition 6.4 mild-rescaling cleanup.  Requesting
scale one returns an actual scale at least one; the outer-John determinant
bound therefore gives a uniform factor four.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- A positive-radius tube carrier is contained in its centered dilation by
two. -/
private theorem pureWZ2Proposition64_tubeCarrier_self_dilated
    {rho : ℝ} (hrho : 0 < rho) (tube : Kakeya.DeltaTube rho) :
    tube.carrier ⊆ wz2PaperCenteredDilatedCarrier 2 tube := by
  have hconvex : Convex ℝ tube.carrier :=
    wz2_paper_ordinary_tube_carrier_convex tube
  let center := wz2PaperTubeMidpoint tube
  have hcenter : center ∈ tube.carrier := by
    have hsegment : center ∈ Kakeya.unitSegment tube.base tube.direction := by
      refine ⟨1 / 2, by norm_num, ?_⟩
      simp [center, wz2PaperTubeMidpoint]
    exact Metric.mem_cthickening_of_dist_le center center rho
      (Kakeya.unitSegment tube.base tube.direction) hsegment
      (by simp [hrho.le])
  intro point hpoint
  let midpoint : Point3 := (1 / 2 : ℝ) • point + (1 / 2 : ℝ) • center
  have hmidpoint : midpoint ∈ tube.carrier :=
    hconvex hpoint hcenter (by norm_num) (by norm_num) (by norm_num)
  refine ⟨midpoint, hmidpoint, ?_⟩
  simp [midpoint, AffineMap.homothety_apply]
  module

/-- The strict full fibers of a pure partitioning cover partition every
filtered subset of the fine index set. -/
private theorem pureWZ2Proposition64_fullFibers_partition
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (hrho : 0 < rho)
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (predicate : Fin fine.card → Prop) [DecidablePred predicate] :
    (Finset.univ.filter predicate).card =
      ∑ parent : Fin coarse.card,
        ((wz2PaperOrdinaryFullFiberIndices fine coarse parent).filter
          predicate).card := by
  let fiber := fun parent : Fin coarse.card =>
    wz2PaperOrdinaryFullFiberIndices fine coarse parent
  have hdisjoint : ∀ first second : Fin coarse.card, first ≠ second →
      Disjoint (fiber first) (fiber second) := by
    intro first second hne
    apply Disjoint.mono
      (fun index hindex => by
        rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
        exact ((mem_wz2PaperOrdinaryFullFiberIndices_iff first index).mp
          hindex).trans
            (pureWZ2Proposition64_tubeCarrier_self_dilated hrho _))
      (fun index hindex => by
        rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
        exact ((mem_wz2PaperOrdinaryFullFiberIndices_iff second index).mp
          hindex).trans
            (pureWZ2Proposition64_tubeCarrier_self_dilated hrho _))
      (cover.doubled_fibers_disjoint first second hne)
  have hfilteredDisjoint : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin coarse.card)))
      (fun parent => (fiber parent).filter predicate) := by
    intro first _ second _ hne
    exact Disjoint.mono (Finset.filter_subset _ _)
      (Finset.filter_subset _ _) (hdisjoint first second hne)
  have hunion : Finset.univ.filter predicate =
      Finset.biUnion (Finset.univ : Finset (Fin coarse.card))
        (fun parent => (fiber parent).filter predicate) := by
    ext index
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro hpredicate
      rcases cover.covers index with ⟨parent, hparent⟩
      exact ⟨parent, hparent, hpredicate⟩
    · rintro ⟨_parent, _hparent, hpredicate⟩
      exact hpredicate
  rw [hunion, Finset.card_biUnion hfilteredDisjoint]

/-- Transfer normalized CWA from one actual-John full fiber back to the
original fiber. -/
private theorem pureWZ2Proposition64_fullFiberTopLevelCWA
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (normalization : WZ2PaperAssouadUnitRescalingData (coarse.tube parent))
    (hrhoOne : 1 ≤ rho)
    {C : ENNReal}
    (hcwa : WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := fine) (coarse := coarse) parent normalization) C)
    (convexSet : Set Point3) (hconvex : Convex ℝ convexSet) :
    (((wz2PaperOrdinaryFullFiberIndices fine coarse parent).filter
      fun index => (fine.tube index).carrier ⊆ convexSet).card : ENNReal) ≤
      4 * C * volume convexSet *
        ((wz2PaperOrdinaryFullFiberIndices fine coarse parent).card :
          ENNReal) := by
  let normalizedFamily := wz2PaperPureUnitRescaledFullFiberBodyFamily
    (fine := fine) (coarse := coarse) parent normalization
  let indexEquiv := wz2PaperOrdinaryFullFiberIndexEquiv
    (fine := fine) (coarse := coarse) parent
  let imageSet := normalization.map '' convexSet
  have himageConvex : Convex ℝ imageSet :=
    hconvex.affine_image normalization.map.toAffineMap
  let normalizedContained := normalizedFamily.containedIndices imageSet
  let sourceContained :=
    (wz2PaperOrdinaryFullFiberIndices fine coarse parent).filter
      fun index => (fine.tube index).carrier ⊆ convexSet
  have hcontainment : ∀ target : Fin normalizedFamily.card,
      (normalizedFamily.body target).carrier ⊆ imageSet ↔
        (fine.tube (indexEquiv target).1).carrier ⊆ convexSet := by
    intro target
    change normalization.map ''
        (fine.tube (indexEquiv target).1).carrier ⊆
          normalization.map '' convexSet ↔ _
    exact Set.image_subset_image_iff normalization.map.injective
  have himage : Finset.image (fun target => (indexEquiv target).1)
      normalizedContained = sourceContained := by
    ext source
    constructor
    · intro hsource
      rcases Finset.mem_image.mp hsource with ⟨target, htarget, rfl⟩
      have htarget' : (normalizedFamily.body target).carrier ⊆ imageSet :=
        (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mp htarget
      exact Finset.mem_filter.mpr
        ⟨(indexEquiv target).2, (hcontainment target).mp htarget'⟩
    · intro hsource
      rcases Finset.mem_filter.mp hsource with ⟨hsource, hcarrier⟩
      let target := indexEquiv.symm ⟨source, hsource⟩
      apply Finset.mem_image.mpr
      refine ⟨target, ?_, ?_⟩
      · apply (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mpr
        apply (hcontainment target).mpr
        simpa [target] using hcarrier
      · simp [target]
  have hcount : normalizedFamily.containedCount imageSet =
      (sourceContained.card : ENNReal) := by
    change (normalizedContained.card : ENNReal) = _
    rw [← himage]
    exact_mod_cast (Finset.card_image_of_injective normalizedContained
      (fun _ _ h => indexEquiv.injective (Subtype.ext h))).symm
  let john := normalization.parent_convex_body.outerJohnEllipsoidMap
  have hjohn : rho ^ 2 / 4 ≤
      |LinearMap.det (john : Point3 →ₗ[ℝ] Point3)| :=
    wz2Paper_outerJohn_abs_det_lower (coarse.tube parent) (by linarith)
  have hjohnPos : 0 < |LinearMap.det (john : Point3 →ₗ[ℝ] Point3)| := by
    exact lt_of_lt_of_le (by positivity : 0 < rho ^ 2 / 4) hjohn
  have hdet :
      |LinearMap.det (normalization.map.linear : Point3 →ₗ[ℝ] Point3)| ≤ 4 := by
    rw [show normalization.map.linear = john.symm by rfl,
      LinearEquiv.det_coe_symm, abs_inv]
    have hinverse : |LinearMap.det (john : Point3 →ₗ[ℝ] Point3)|⁻¹ ≤
        (rho ^ 2 / 4)⁻¹ :=
      (inv_le_inv₀ hjohnPos (by positivity)).2 hjohn
    calc
      |LinearMap.det (john : Point3 →ₗ[ℝ] Point3)|⁻¹ ≤
          (rho ^ 2 / 4)⁻¹ := hinverse
      _ = 4 / rho ^ 2 := by field_simp
      _ ≤ 4 := by
        exact (div_le_iff₀ (by positivity : 0 < rho ^ 2)).2 (by nlinarith)
  have hvolume : volume imageSet ≤ 4 * volume convexSet := by
    rw [show volume imageSet = ENNReal.ofReal
        |LinearMap.det (normalization.map.linear : Point3 →ₗ[ℝ] Point3)| *
          volume convexSet by
      exact wz2PaperAffineEquiv_volume_image_eq normalization.map convexSet]
    gcongr
    simpa using ENNReal.ofReal_mono hdet
  rw [← hcount]
  have hcard : normalizedFamily.enncard =
      ((wz2PaperOrdinaryFullFiberIndices fine coarse parent).card :
        ENNReal) := by
    rfl
  rw [← hcard]
  calc
    normalizedFamily.containedCount imageSet ≤
        C * volume imageSet * normalizedFamily.enncard :=
      hcwa imageSet himageConvex
    _ ≤ C * (4 * volume convexSet) * normalizedFamily.enncard := by
      gcongr
    _ = 4 * C * volume convexSet * normalizedFamily.enncard := by ring

/-- Public pure nearby-CWA implies a top-level ordinary-carrier CWA bound,
with one fixed factor four. -/
theorem pureWZ2Proposition64_pureNearby_topLevelOrdinary
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hdeltaOne : delta ≤ 1)
    (hnearby : WZ2PaperPureCWAAtNearbyScales family C) :
    WZ2PaperBodyConvexWolffBound family.toBodyFamily (4 * C) := by
  let requested : WZ2PaperRequestedScale delta :=
    ⟨1, hdeltaOne, by norm_num⟩
  rcases hnearby.2.2.2 requested with ⟨nearby⟩
  let scaleData := nearby.scaleData
  let coarse := scaleData.coarse
  let cover := scaleData.cover
  intro convexSet hconvex
  let predicate : Fin family.card → Prop := fun index =>
    (family.tube index).carrier ⊆ convexSet
  have hfiber : ∀ parent : Fin coarse.card,
      (((wz2PaperOrdinaryFullFiberIndices family coarse parent).filter
        predicate).card : ENNReal) ≤
      (4 * C * volume convexSet) *
        ((wz2PaperOrdinaryFullFiberIndices family coarse parent).card :
          ENNReal) := by
    intro parent
    rcases scaleData.rescaledFiber parent with ⟨fiber⟩
    simpa [predicate, mul_assoc] using
      pureWZ2Proposition64_fullFiberTopLevelCWA parent
        fiber.normalization nearby.requested_le fiber.convex_wolff
        convexSet hconvex
  have hpartition := pureWZ2Proposition64_fullFibers_partition
    scaleData.rho_pos cover predicate
  have hpartitionAll := pureWZ2Proposition64_fullFibers_partition
    scaleData.rho_pos cover (fun _ => True)
  have hcard : ∑ parent : Fin coarse.card,
      (wz2PaperOrdinaryFullFiberIndices family coarse parent).card =
        family.card := by
    simpa using hpartitionAll.symm
  change ((Finset.univ.filter predicate).card : ENNReal) ≤
    4 * C * volume convexSet * family.enncard
  rw [hpartition, Nat.cast_sum]
  calc
    ∑ parent : Fin coarse.card,
        (((wz2PaperOrdinaryFullFiberIndices family coarse parent).filter
          predicate).card : ENNReal) ≤
      ∑ parent : Fin coarse.card,
        (4 * C * volume convexSet) *
          ((wz2PaperOrdinaryFullFiberIndices family coarse parent).card :
            ENNReal) := Finset.sum_le_sum fun parent _ => hfiber parent
    _ = (4 * C * volume convexSet) *
        (∑ parent : Fin coarse.card,
          ((wz2PaperOrdinaryFullFiberIndices family coarse parent).card :
            ENNReal)) := by rw [Finset.mul_sum]
    _ = 4 * C * volume convexSet * family.enncard := by
      rw [← Nat.cast_sum, hcard]
      simp [Kakeya.Streamlined.TubeFamily.enncard]


/-- For a line-class tube whose ordinary segment is centered at its
height-zero point, the whole ordinary carrier lies in the literal cropped
paper carrier. -/
theorem pureWZ2Proposition64_centeredOrdinaryCarrier_subset_cropped
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 10)
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube)
    (hcentered : wz2PaperTubeMidpoint tube = wz1TubeAxisZeroPoint tube) :
    tube.carrier ⊆ wz1PaperTubeCarrier tube := by
  intro point hpoint
  constructor
  · exact Metric.cthickening_mono (by linarith : delta ≤ 6 * delta)
      (tubeAxisLine tube)
      (Metric.cthickening_subset_of_subset delta
        (wz2_paper_unitSegment_subset_axisLine tube) hpoint)
  · have hpointMidpoint := tube_subset_midpoint_closedBall hdelta tube hpoint
    have hdistance : dist point (wz2PaperTubeMidpoint tube) ≤ 1 / 2 + delta := by
      simpa [Metric.mem_closedBall, wz2PaperTubeMidpoint] using hpointMidpoint
    have hmidpointCoordinate : ∀ coordinate : Fin 3,
        |wz2PaperTubeMidpoint tube coordinate| ≤ 1 / 3 := by
      intro coordinate
      rw [hcentered]
      by_cases hzero : coordinate = (0 : Fin 3)
      · simpa [hzero] using hline.2.1
      by_cases hone : coordinate = (1 : Fin 3)
      · simpa [hone] using hline.2.2
      · have htwo : coordinate = (2 : Fin 3) := by
          apply Fin.ext
          omega
        rw [htwo, wz1TubeAxisZeroPoint_coord_two tube hline.vertical]
        norm_num
    have hpointCoordinate : ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
      intro coordinate
      have hcoordinateDistance :
          |point coordinate - wz2PaperTubeMidpoint tube coordinate| ≤
            dist point (wz2PaperTubeMidpoint tube) := by
        simpa [Real.dist_eq] using
          PiLp.dist_apply_le point (wz2PaperTubeMidpoint tube) coordinate
      calc
        |point coordinate| =
            |(point coordinate - wz2PaperTubeMidpoint tube coordinate) +
              wz2PaperTubeMidpoint tube coordinate| := by ring_nf
        _ ≤ |point coordinate - wz2PaperTubeMidpoint tube coordinate| +
              |wz2PaperTubeMidpoint tube coordinate| := abs_add_le _ _
        _ ≤ (1 / 2 + delta) + 1 / 3 :=
          add_le_add (hcoordinateDistance.trans hdistance)
            (hmidpointCoordinate coordinate)
        _ ≤ 1 := by linarith
    simpa [Kakeya.Streamlined.axisBox] using
      ⟨hpointCoordinate 0, hpointCoordinate 1, hpointCoordinate 2⟩

/-- Convert the ordinary-carrier top-level estimate to the cropped paper
carrier convention for localized line-class families. -/
theorem pureWZ2Proposition64_pureNearby_topLevel
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 10)
    (hline : WZ1PaperIsLineClass family)
    (hcentered : ∀ index, wz2PaperTubeMidpoint (family.tube index) =
      wz1TubeAxisZeroPoint (family.tube index))
    (hnearby : WZ2PaperPureCWAAtNearbyScales family C) :
    WZ2PaperConvexWolffBound family (4 * C) := by
  have ordinary := pureWZ2Proposition64_pureNearby_topLevelOrdinary
    (hdeltaSmall.trans (by norm_num)) hnearby
  intro convexSet hconvex
  have hindices :
      (Finset.univ.filter fun index : Fin family.card =>
        wz1PaperTubeCarrier (family.tube index) ⊆ convexSet) ⊆
      (Finset.univ.filter fun index : Fin family.card =>
        (family.tube index).carrier ⊆ convexSet) := by
    intro index hindex
    have hcropped := (Finset.mem_filter.mp hindex).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ index,
        (pureWZ2Proposition64_centeredOrdinaryCarrier_subset_cropped
          hdelta hdeltaSmall (family.tube index) (hline index)
          (hcentered index)).trans hcropped⟩
  have hcount :
      (wz1PaperBodyFamily family).containedCount convexSet ≤
        family.toBodyFamily.containedCount convexSet := by
    change
      ((Finset.univ.filter fun index : Fin family.card =>
        wz1PaperTubeCarrier (family.tube index) ⊆ convexSet).card :
          ENNReal) ≤
      ((Finset.univ.filter fun index : Fin family.card =>
        (family.tube index).carrier ⊆ convexSet).card : ENNReal)
    exact_mod_cast Finset.card_le_card hindices
  exact hcount.trans (ordinary convexSet hconvex)

end Kakeya.Assouad

end
