import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSpatialPropertyThreePullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SubfamilyGrainConfigurationExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.NormalizedCardinalityFloor
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume

/-!
# Property-Three mass retention on a dyadic source shading

If the ambient source shading has point multiplicity in `[m,2m)`, the
Property-Three common hull recovers the ambient multiplicity `m` at every
surviving point.  The selected sticky refinement has multiplicity at most
`2m`.  These two factors cancel.  Consequently the pullback pays only the
coarse multiplicity cap and the sticky polylogarithmic retention, not a
cardinality bound for the entire selected fine family.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/-- A sticky selected refinement cannot have larger point multiplicity than
its ambient source shading. -/
lemma sticky_refined_pointMultiplicity_le_source
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (point : Point3) :
    sticky.refined.pointMultiplicity point ≤
      sourceShading.pointMultiplicity point := by
  let selectedIndices : Finset (Fin sticky.selected.family.card) :=
    Finset.univ.filter fun index =>
      point ∈ sticky.refined.carrier index
  let sourceIndices : Finset (Fin source.card) :=
    Finset.univ.filter fun index =>
      point ∈ sourceShading.carrier index
  have himage :
      Finset.image sticky.selected.embedding selectedIndices ⊆
        sourceIndices := by
    intro sourceIndex hsourceIndex
    rcases Finset.mem_image.mp hsourceIndex with
      ⟨selectedIndex, hselectedIndex, rfl⟩
    have hpoint : point ∈ sticky.refined.carrier selectedIndex :=
      (Finset.mem_filter.mp hselectedIndex).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, sticky.subshading selectedIndex hpoint⟩
  have hcard :
      (Finset.image sticky.selected.embedding selectedIndices).card =
        selectedIndices.card := by
    exact Finset.card_image_of_injective _
      sticky.selected.embedding.injective
  have hle := Finset.card_le_card himage
  change selectedIndices.card ≤ sourceIndices.card
  rw [← hcard]
  exact hle

/-- The sharp common-hull loss for an incoming shading which is already in a
single dyadic point-multiplicity band.  Compared with the generic loss, the
fine-family cardinality cancels and only one coarse multiplicity cap remains. -/
def propertyThreeDyadicCommonHullMassLoss
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent) : ENNReal :=
  (4 * stickyCoarseMultiplicityCap sticky) *
    (wz2PaperPureRefinementFraction delta logExponent)⁻¹

lemma propertyThreeDyadicCommonHullMassLoss_pos_ne_top
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    0 < propertyThreeDyadicCommonHullMassLoss sticky ∧
      propertyThreeDyadicCommonHullMassLoss sticky ≠ ⊤ := by
  have hcoarsePos : 0 < stickyCoarseMultiplicityCap sticky := by
    unfold stickyCoarseMultiplicityCap
    apply ENNReal.mul_pos
    · exact (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos sticky.coarse_extremal.delta_pos _)).ne'
    · have hcard : (sticky.coarse.card : ENNReal) ≠ 0 := by
        exact_mod_cast sticky.coarse_extremal.nonempty.ne'
      simpa [Kakeya.Streamlined.TubeFamily.enncard] using hcard
  have hcoarseTop : stickyCoarseMultiplicityCap sticky ≠ ⊤ := by
    unfold stickyCoarseMultiplicityCap
    exact ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
      (by simp [Kakeya.Streamlined.TubeFamily.enncard])
  have hfraction := pure_refinement_fraction_pos_ne_top
    hdelta hdeltaOne logExponent
  unfold propertyThreeDyadicCommonHullMassLoss
  exact ⟨ENNReal.mul_pos
      (ENNReal.mul_pos (by norm_num) hcoarsePos.ne').ne'
      (ENNReal.inv_ne_zero.mpr hfraction.2),
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hcoarseTop)
      (ENNReal.inv_ne_top.mpr hfraction.1.ne')⟩

/-- If the coarse shading also lies in a genuine multiplicity band, its lower
and upper multiplicities cancel in the Property-Three cell count.  The
pullback therefore loses only the band's regularity, rather than its absolute
multiplicity cap. -/
lemma propertyThreeFinePullback_volume_lower_of_coarse_band
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse)
    (hsub : PaperIsSubshading propertyThree sticky.croppedCoarseShading)
    (hcubical : WZ1PaperIsCubicalShading propertyThree)
    (hhalf : (1 / 2 : ENNReal) * sticky.croppedCoarseShading.mass ≤
      propertyThree.mass)
    (coarseMultiplicity regularity : ENNReal)
    (hcoarseMultiplicityPos : 0 < coarseMultiplicity)
    (hcoarseMultiplicityTop : coarseMultiplicity ≠ ⊤)
    (hregularityPos : 0 < regularity)
    (hregularityTop : regularity ≠ ⊤)
    (hcoarseLower : ∀ point ∈ sticky.croppedCoarseShading.union,
      coarseMultiplicity ≤
        sticky.croppedCoarseShading.pointMultiplicity point)
    (hcoarseUpper : ∀ point ∈ sticky.croppedCoarseShading.union,
      (sticky.croppedCoarseShading.pointMultiplicity point : ENNReal) ≤
        regularity * coarseMultiplicity) :
    (2 * regularity : ENNReal)⁻¹ * volume sticky.refined.union ≤
      volume
        (propertyThreeFinePullbackShading sticky.cover sticky.refined
          propertyThree).union := by
  let active : ENNReal := sticky.balanced.activeCells.card
  let good : ENNReal :=
    (propertyThreeGoodCells sticky.balanced propertyThree).card
  let cubeVolume : ENNReal :=
    volume (wz1PaperGridCube rho.1 (0, 0, 0))
  have hrho : 0 < rho.1 := sticky.coarse_extremal.delta_pos
  have hpropertyMassUpper :
      propertyThree.mass ≤
        (regularity * coarseMultiplicity) * (good * cubeVolume) := by
    calc
      propertyThree.mass ≤
          (regularity * coarseMultiplicity) * volume propertyThree.union :=
        mass_le_of_pointMultiplicity_le (fun point hpoint => by
          have hnat := paperSubshading_pointMultiplicity_le
            propertyThree sticky.croppedCoarseShading hsub point
          have henn :
              (propertyThree.pointMultiplicity point : ENNReal) ≤
                (sticky.croppedCoarseShading.pointMultiplicity point :
                  ENNReal) := by exact_mod_cast hnat
          have hpointCoarse : point ∈ sticky.croppedCoarseShading.union := by
            rcases hpoint with ⟨index, hpointIndex⟩
            exact ⟨index, hsub index hpointIndex⟩
          exact henn.trans (hcoarseUpper point hpointCoarse))
      _ = (regularity * coarseMultiplicity) * (good * cubeVolume) := by
        rw [propertyThree_volume_eq_goodCells
          sticky.balanced hsub hcubical hrho]
  have hcoarseMassLower :
      coarseMultiplicity * volume sticky.croppedCoarseShading.union ≤
        sticky.croppedCoarseShading.mass :=
    multiplicity_floor_le_mass hcoarseLower
  have hactiveWithCube :
      ((1 / 2 : ENNReal) * coarseMultiplicity * active) * cubeVolume ≤
        ((regularity * coarseMultiplicity) * good) * cubeVolume := by
    calc
      ((1 / 2 : ENNReal) * coarseMultiplicity * active) * cubeVolume =
          (1 / 2 : ENNReal) *
            (coarseMultiplicity *
              volume sticky.croppedCoarseShading.union) := by
        dsimp only [active, cubeVolume]
        rw [balanced_cover_coarse_volume sticky.balanced hrho]
        ring
      _ ≤ (1 / 2 : ENNReal) * sticky.croppedCoarseShading.mass := by
        gcongr
      _ ≤ propertyThree.mass := hhalf
      _ ≤ (regularity * coarseMultiplicity) * (good * cubeVolume) :=
        hpropertyMassUpper
      _ = ((regularity * coarseMultiplicity) * good) * cubeVolume := by ring
  have hcubeZero : cubeVolume ≠ 0 :=
    (wz1PaperGridCube_volume_pos hrho (0, 0, 0)).ne'
  have hcubeTop : cubeVolume ≠ ⊤ :=
    wz1PaperGridCube_volume_ne_top hrho (0, 0, 0)
  have hactiveCount :
      (1 / 2 : ENNReal) * coarseMultiplicity * active ≤
        (regularity * coarseMultiplicity) * good :=
    (ENNReal.mul_le_mul_iff_right hcubeZero hcubeTop).mp <| by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hactiveWithCube
  have hregularCount :
      (1 / 2 : ENNReal) * active ≤ regularity * good := by
    apply (ENNReal.mul_le_mul_iff_left hcoarseMultiplicityPos.ne'
      hcoarseMultiplicityTop).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hactiveCount
  have hrefinedVolume :
      volume sticky.refined.union = active * sticky.balanced.cellMass := by
    simpa [active] using
      balanced_cover_fine_union_volume sticky.balanced hrho
  have hpullbackVolume :
      volume
          (propertyThreeFinePullbackShading sticky.cover sticky.refined
            propertyThree).union =
        good * sticky.balanced.cellMass := by
    simpa [good] using
      propertyThreeFinePullback_volume_eq_goodCells sticky.balanced hsub
  rw [hrefinedVolume, hpullbackVolume]
  have hinverse : (2 * regularity : ENNReal)⁻¹ =
      (2 : ENNReal)⁻¹ * regularity⁻¹ :=
    ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inr hregularityPos.ne')
  calc
    (2 * regularity : ENNReal)⁻¹ *
          (active * sticky.balanced.cellMass) =
        regularity⁻¹ * ((1 / 2 : ENNReal) * active) *
          sticky.balanced.cellMass := by
      rw [hinverse]
      simp only [one_div]
      ring
    _ ≤ regularity⁻¹ * (regularity * good) *
        sticky.balanced.cellMass := by gcongr
    _ = good * sticky.balanced.cellMass := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel
        hregularityPos.ne' hregularityTop]
      simp

/-- The complete two-band cancellation.  The fine multiplicity cancels when
passing from shaded mass to spatial volume and back, while the coarse
multiplicity cancels in the active-cell count.  Only the coarse band
regularity and the sticky refinement fraction remain. -/
lemma ambientPropertyThreeCommonHull_source_mass_lower_of_two_bands
    {delta sigma outputLoss : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    (ambientShading : WZ1PaperTubeShading ambient)
    (selected : Kakeya.Streamlined.TubeSubfamily ambient)
    {sourceShading : WZ1PaperTubeShading selected.family}
    (hsourceSub : PaperIsSubshading sourceShading
      (restrictPaperShading selected ambientShading))
    {rho : WZ2PaperRequestedScale delta}
    {logExponent fineMultiplicity : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse)
    (hsub : PaperIsSubshading propertyThree sticky.croppedCoarseShading)
    (hcubical : WZ1PaperIsCubicalShading propertyThree)
    (hhalf : (1 / 2 : ENNReal) * sticky.croppedCoarseShading.mass ≤
      propertyThree.mass)
    (coarseMultiplicity regularity : ENNReal)
    (hcoarseMultiplicityPos : 0 < coarseMultiplicity)
    (hcoarseMultiplicityTop : coarseMultiplicity ≠ ⊤)
    (hregularityPos : 0 < regularity)
    (hregularityTop : regularity ≠ ⊤)
    (hcoarseLower : ∀ point ∈ sticky.croppedCoarseShading.union,
      coarseMultiplicity ≤
        sticky.croppedCoarseShading.pointMultiplicity point)
    (hcoarseUpper : ∀ point ∈ sticky.croppedCoarseShading.union,
      (sticky.croppedCoarseShading.pointMultiplicity point : ENNReal) ≤
        regularity * coarseMultiplicity)
    (hsourceLower : ∀ point ∈ ambientShading.union,
      fineMultiplicity ≤ ambientShading.pointMultiplicity point)
    (hsourceUpper : ∀ point ∈ ambientShading.union,
      (ambientShading.pointMultiplicity point : ENNReal) <
        2 * (fineMultiplicity : ENNReal)) :
    ((4 * regularity) *
        (wz2PaperPureRefinementFraction delta logExponent)⁻¹)⁻¹ *
        sourceShading.mass ≤
      (paperCommonSpatialHull ambientShading
        (extendShading selected
          (ambientPropertyThreeCommonHull sticky propertyThree))).mass := by
  have hvolume := propertyThreeFinePullback_volume_lower_of_coarse_band
    sticky propertyThree hsub hcubical hhalf coarseMultiplicity regularity
    hcoarseMultiplicityPos hcoarseMultiplicityTop hregularityPos
    hregularityTop hcoarseLower hcoarseUpper
  have hrefinedUpper : ∀ point ∈ sticky.refined.union,
      (sticky.refined.pointMultiplicity point : ENNReal) <
        2 * (fineMultiplicity : ENNReal) := by
    intro point hpoint
    have hsourcePoint : point ∈ sourceShading.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨sticky.selected.embedding index,
        sticky.subshading index hindex⟩
    have hrestrictedPoint : point ∈
        (restrictPaperShading selected ambientShading).union := by
      rcases hsourcePoint with ⟨index, hindex⟩
      exact ⟨index, hsourceSub index hindex⟩
    have hambientPoint : point ∈ ambientShading.union := by
      rcases hrestrictedPoint with ⟨index, hindex⟩
      exact ⟨selected.embedding index, hindex⟩
    have hrefinedSource :=
      sticky_refined_pointMultiplicity_le_source sticky point
    have hsourceRestricted := paperSubshading_pointMultiplicity_le
      sourceShading (restrictPaperShading selected ambientShading)
      hsourceSub point
    have hrestrictedAmbient := restrictPaperShading_pointMultiplicity_le
      selected ambientShading point
    have hleNat := hrefinedSource.trans
      (hsourceRestricted.trans hrestrictedAmbient)
    have hleENN :
        (sticky.refined.pointMultiplicity point : ENNReal) ≤
          (ambientShading.pointMultiplicity point : ENNReal) := by
      exact_mod_cast hleNat
    exact hleENN.trans_lt (hsourceUpper point hambientPoint)
  have hrefinedMass : sticky.refined.mass ≤
      (2 * fineMultiplicity : ENNReal) * volume sticky.refined.union := by
    apply mass_le_of_pointMultiplicity_le
    intro point hpoint
    exact (hrefinedUpper point hpoint).le
  have htargetMultiplicity : ∀ point ∈
      (paperCommonSpatialHull ambientShading
        (extendShading selected
          (ambientPropertyThreeCommonHull sticky propertyThree))).union,
      fineMultiplicity ≤
        (paperCommonSpatialHull ambientShading
          (extendShading selected
            (ambientPropertyThreeCommonHull sticky propertyThree))).pointMultiplicity
              point := by
    intro point hpoint
    rw [paperCommonSpatialHull_pointMultiplicity_eq ambientShading
      (extendShading selected
        (ambientPropertyThreeCommonHull sticky propertyThree)) point hpoint]
    have hambientPoint : point ∈ ambientShading.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hindex.1⟩
    exact hsourceLower point hambientPoint
  have htargetMass : (fineMultiplicity : ENNReal) *
      volume (paperCommonSpatialHull ambientShading
        (extendShading selected
          (ambientPropertyThreeCommonHull sticky propertyThree))).union ≤
        (paperCommonSpatialHull ambientShading
          (extendShading selected
            (ambientPropertyThreeCommonHull sticky propertyThree))).mass := by
    exact multiplicity_floor_le_mass (fun point hpoint => by
      exact_mod_cast htargetMultiplicity point hpoint)
  have htargetVolume :
      volume (paperCommonSpatialHull ambientShading
        (extendShading selected
          (ambientPropertyThreeCommonHull sticky propertyThree))).union =
        volume
          (propertyThreeFinePullbackShading sticky.cover sticky.refined
            propertyThree).union := by
    rw [paperCommonSpatialHull_union]
    · rw [extendShading_union, ambientPropertyThreeCommonHull_union]
    · intro ambientIndex point hpoint
      by_cases himage : ∃ selectedIndex,
          selected.embedding selectedIndex = ambientIndex
      · rcases himage with ⟨selectedIndex, rfl⟩
        rw [extendShading_carrier_mem] at hpoint
        exact hsourceSub selectedIndex <|
          ambientPropertyThreeCommonHull_subshading
            sticky propertyThree selectedIndex hpoint
      · rw [extendShading_carrier_empty himage] at hpoint
        exact False.elim hpoint
  have hrefinedToTarget :
      (4 * regularity : ENNReal)⁻¹ * sticky.refined.mass ≤
        (paperCommonSpatialHull ambientShading
          (extendShading selected
            (ambientPropertyThreeCommonHull sticky propertyThree))).mass := by
    calc
      (4 * regularity : ENNReal)⁻¹ * sticky.refined.mass ≤
          (4 * regularity : ENNReal)⁻¹ *
            ((2 * fineMultiplicity : ENNReal) *
              volume sticky.refined.union) := by gcongr
      _ = (fineMultiplicity : ENNReal) *
          ((2 * regularity : ENNReal)⁻¹ *
            volume sticky.refined.union) := by
        have hinverse : (4 * regularity : ENNReal)⁻¹ =
            (4 : ENNReal)⁻¹ * regularity⁻¹ :=
          ENNReal.mul_inv (Or.inl (by norm_num))
            (Or.inr hregularityPos.ne')
        rw [hinverse]
        have hfourTwo : (4 : ENNReal)⁻¹ * 2 = 2⁻¹ := by
          have hfour : (4 : ENNReal)⁻¹ =
              ENNReal.ofReal (1 / 4 : ℝ) := by simp
          have htwo : (2 : ENNReal)⁻¹ =
              ENNReal.ofReal (1 / 2 : ℝ) := by simp
          rw [hfour, htwo, show (2 : ENNReal) =
            ENNReal.ofReal (2 : ℝ) by norm_num]
          rw [← ENNReal.ofReal_mul (by norm_num)]
          norm_num
        have htwoInverse : (2 * regularity : ENNReal)⁻¹ =
            (2 : ENNReal)⁻¹ * regularity⁻¹ :=
          ENNReal.mul_inv (Or.inl (by norm_num))
            (Or.inr hregularityPos.ne')
        rw [htwoInverse]
        rw [show
          (4 : ENNReal)⁻¹ * regularity⁻¹ *
              (2 * (fineMultiplicity : ENNReal) *
                volume sticky.refined.union) =
            ((4 : ENNReal)⁻¹ * 2) * (fineMultiplicity : ENNReal) *
              regularity⁻¹ * volume sticky.refined.union by ring, hfourTwo]
        ring
      _ ≤ (fineMultiplicity : ENNReal) *
          volume
            (propertyThreeFinePullbackShading sticky.cover sticky.refined
              propertyThree).union := by gcongr
      _ = (fineMultiplicity : ENNReal) *
          volume (paperCommonSpatialHull ambientShading
            (extendShading selected
              (ambientPropertyThreeCommonHull sticky propertyThree))).union :=
        by rw [htargetVolume]
      _ ≤ (paperCommonSpatialHull ambientShading
          (extendShading selected
            (ambientPropertyThreeCommonHull sticky propertyThree))).mass :=
        htargetMass
  have hinverse :
      ((4 * regularity) *
          (wz2PaperPureRefinementFraction delta logExponent)⁻¹)⁻¹ =
        (4 * regularity : ENNReal)⁻¹ *
          wz2PaperPureRefinementFraction delta logExponent := by
    rw [ENNReal.mul_inv
      (Or.inl (mul_ne_zero (by norm_num) hregularityPos.ne'))
      (Or.inl (ENNReal.mul_ne_top (by norm_num) hregularityTop)), inv_inv]
  rw [hinverse]
  calc
    (4 * regularity : ENNReal)⁻¹ *
          wz2PaperPureRefinementFraction delta logExponent *
            sourceShading.mass =
        (4 * regularity : ENNReal)⁻¹ *
          (wz2PaperPureRefinementFraction delta logExponent *
            sourceShading.mass) := by ring
    _ ≤
        (4 * regularity : ENNReal)⁻¹ * sticky.refined.mass := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        (mul_le_mul_right sticky.retained_mass
          (4 * regularity : ENNReal)⁻¹)
    _ ≤ (paperCommonSpatialHull ambientShading
        (extendShading selected
          (ambientPropertyThreeCommonHull sticky propertyThree))).mass :=
      hrefinedToTarget

/-- On a dyadic-multiplicity source shading, the honest Property-Three common
hull loses only one coarse multiplicity cap.  In particular, no upper bound
on the cardinality of the selected fine family occurs. -/
theorem ambientPropertyThreeCommonHull_source_mass_lower_of_dyadic
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent multiplicity : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse)
    (_hdelta : 0 < delta)
    (hsub : PaperIsSubshading
      propertyThree sticky.croppedCoarseShading)
    (hcubical : WZ1PaperIsCubicalShading propertyThree)
    (hhalf :
      (1 / 2 : ENNReal) * sticky.croppedCoarseShading.mass ≤
        propertyThree.mass)
    (hsourceLower : ∀ point ∈ sourceShading.union,
      multiplicity ≤ sourceShading.pointMultiplicity point)
    (hsourceUpper : ∀ point ∈ sourceShading.union,
      sourceShading.pointMultiplicity point < 2 * multiplicity) :
    ((4 * stickyCoarseMultiplicityCap sticky : ENNReal)⁻¹) *
        (wz2PaperPureRefinementFraction delta logExponent *
          sourceShading.mass) ≤
      (ambientPropertyThreeCommonHull sticky propertyThree).mass := by
  let coarseCap : ENNReal := stickyCoarseMultiplicityCap sticky
  let active : ENNReal := sticky.balanced.activeCells.card
  let good : ENNReal :=
    (propertyThreeGoodCells sticky.balanced propertyThree).card
  let cubeVolume : ENNReal :=
    volume (wz1PaperGridCube rho.1 (0, 0, 0))
  let cellMass : ENNReal := sticky.balanced.cellMass
  have hrho : 0 < rho.1 := sticky.coarse_extremal.delta_pos
  have hcoarseCapZero : coarseCap ≠ 0 := by
    dsimp only [coarseCap, stickyCoarseMultiplicityCap]
    apply mul_ne_zero
    · exact (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hrho (2 - sigma - outputLoss))).ne'
    · have hcoarseNonempty : sticky.coarse.Nonempty := by
        let sourceIndex : Fin sticky.selected.family.card :=
          ⟨0, sticky.selected_nonempty⟩
        rcases sticky.cover.covers sourceIndex with ⟨parent, _⟩
        exact Nat.zero_lt_of_lt parent.isLt
      simpa [Kakeya.Streamlined.TubeFamily.enncard] using
        hcoarseNonempty.ne'
  have hcoarseCapTop : coarseCap ≠ ⊤ := by
    dsimp only [coarseCap, stickyCoarseMultiplicityCap]
    exact ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
      (by simp [Kakeya.Streamlined.TubeFamily.enncard])
  have hpropertyMassUpper :
      propertyThree.mass ≤ coarseCap * (good * cubeVolume) := by
    calc
      propertyThree.mass ≤ coarseCap * volume propertyThree.union :=
        mass_le_of_pointMultiplicity_le (fun point hpoint => by
          have hnat := paperSubshading_pointMultiplicity_le
            propertyThree sticky.croppedCoarseShading hsub point
          have henn :
              (propertyThree.pointMultiplicity point : ENNReal) ≤
                (sticky.croppedCoarseShading.pointMultiplicity point :
                  ENNReal) := by
            exact_mod_cast hnat
          exact henn.trans (sticky.coarse_multiplicity_upper point))
      _ = coarseCap * (good * cubeVolume) := by
        rw [propertyThree_volume_eq_goodCells
          sticky.balanced hsub hcubical hrho]
  have hactiveWithCube :
      ((1 / 2 : ENNReal) * active) * cubeVolume ≤
        (coarseCap * good) * cubeVolume := by
    calc
      ((1 / 2 : ENNReal) * active) * cubeVolume =
          (1 / 2 : ENNReal) *
            volume sticky.croppedCoarseShading.union := by
        dsimp only [active, cubeVolume]
        rw [balanced_cover_coarse_volume sticky.balanced hrho]
        ring
      _ ≤ (1 / 2 : ENNReal) *
          sticky.croppedCoarseShading.mass := by
        gcongr
        simpa using multiplicity_floor_le_mass
          (one_le_pointMultiplicity_on_union
            sticky.croppedCoarseShading)
      _ ≤ propertyThree.mass := hhalf
      _ ≤ coarseCap * (good * cubeVolume) := hpropertyMassUpper
      _ = (coarseCap * good) * cubeVolume := by ring
  have hcubeZero : cubeVolume ≠ 0 := by
    exact (wz1PaperGridCube_volume_pos hrho (0, 0, 0)).ne'
  have hcubeTop : cubeVolume ≠ ⊤ := by
    exact wz1PaperGridCube_volume_ne_top hrho (0, 0, 0)
  have hactiveCount :
      (1 / 2 : ENNReal) * active ≤ coarseCap * good :=
    (ENNReal.mul_le_mul_iff_right hcubeZero hcubeTop).mp <| by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hactiveWithCube
  have hgoodCount :
      coarseCap⁻¹ * ((1 / 2 : ENNReal) * active) ≤ good := by
    calc
      coarseCap⁻¹ * ((1 / 2 : ENNReal) * active) ≤
          coarseCap⁻¹ * (coarseCap * good) := by gcongr
      _ = good := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcoarseCapZero
          hcoarseCapTop, one_mul]
  have hrefinedVolume :
      volume sticky.refined.union = active * cellMass := by
    simpa [active, cellMass] using
      balanced_cover_fine_union_volume sticky.balanced hrho
  have hpullbackVolume :
      volume
          (propertyThreeFinePullbackShading sticky.cover sticky.refined
            propertyThree).union =
        good * cellMass := by
    simpa [good, cellMass] using
      propertyThreeFinePullback_volume_eq_goodCells
        sticky.balanced hsub
  have hvolumeRetention :
      (1 / 2 : ENNReal) * coarseCap⁻¹ *
          volume sticky.refined.union ≤
        volume
          (propertyThreeFinePullbackShading sticky.cover sticky.refined
            propertyThree).union := by
    rw [hrefinedVolume, hpullbackVolume]
    calc
      (1 / 2 : ENNReal) * coarseCap⁻¹ * (active * cellMass) =
          (coarseCap⁻¹ * ((1 / 2 : ENNReal) * active)) *
            cellMass := by ring
      _ ≤ good * cellMass := by gcongr
  have hrefinedUpper : ∀ point ∈ sticky.refined.union,
      sticky.refined.pointMultiplicity point < 2 * multiplicity := by
    intro point hpoint
    have hsourcePoint : point ∈ sourceShading.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨sticky.selected.embedding index,
        sticky.subshading index hindex⟩
    exact (sticky_refined_pointMultiplicity_le_source sticky point).trans_lt
      (hsourceUpper point hsourcePoint)
  have hrefinedMass :
      sticky.refined.mass ≤ (2 * multiplicity : ENNReal) *
        volume sticky.refined.union := by
    apply mass_le_of_pointMultiplicity_le
    intro point hpoint
    exact_mod_cast (hrefinedUpper point hpoint).le
  have htargetMultiplicity : ∀ point ∈
      (ambientPropertyThreeCommonHull sticky propertyThree).union,
      multiplicity ≤
        (ambientPropertyThreeCommonHull sticky propertyThree).pointMultiplicity
          point := by
    intro point hpoint
    rw [ambientPropertyThreeCommonHull_pointMultiplicity_eq
      sticky propertyThree point hpoint]
    have hsourcePoint : point ∈ sourceShading.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index,
        ambientPropertyThreeCommonHull_subshading
          sticky propertyThree index hindex⟩
    exact hsourceLower point hsourcePoint
  have htargetMass :
      (multiplicity : ENNReal) *
          volume (ambientPropertyThreeCommonHull sticky propertyThree).union ≤
        (ambientPropertyThreeCommonHull sticky propertyThree).mass := by
    exact multiplicity_floor_le_mass (fun point hpoint => by
      exact_mod_cast htargetMultiplicity point hpoint)
  have htargetVolume :
      volume (ambientPropertyThreeCommonHull sticky propertyThree).union =
        volume
          (propertyThreeFinePullbackShading sticky.cover sticky.refined
            propertyThree).union := by
    rw [ambientPropertyThreeCommonHull_union sticky propertyThree]
  have hrefinedToTarget :
      ((4 * coarseCap : ENNReal)⁻¹) * sticky.refined.mass ≤
        (ambientPropertyThreeCommonHull sticky propertyThree).mass := by
    calc
      ((4 * coarseCap : ENNReal)⁻¹) * sticky.refined.mass ≤
          ((4 * coarseCap : ENNReal)⁻¹) *
            ((2 * multiplicity : ENNReal) *
              volume sticky.refined.union) := by gcongr
      _ = (multiplicity : ENNReal) *
          ((1 / 2 : ENNReal) * coarseCap⁻¹ *
            volume sticky.refined.union) := by
        rw [ENNReal.mul_inv (Or.inr hcoarseCapTop)
          (Or.inr hcoarseCapZero)]
        have hfourTwo : (4 : ENNReal)⁻¹ * 2 = 2⁻¹ := by
          have hfour : (4 : ENNReal)⁻¹ =
              ENNReal.ofReal (1 / 4 : ℝ) := by
            simp
          have htwo : (2 : ENNReal)⁻¹ =
              ENNReal.ofReal (1 / 2 : ℝ) := by
            simp
          rw [hfour, htwo, show (2 : ENNReal) =
            ENNReal.ofReal (2 : ℝ) by norm_num]
          rw [← ENNReal.ofReal_mul (by norm_num)]
          norm_num
        rw [show
          4⁻¹ * coarseCap⁻¹ * (2 * (multiplicity : ENNReal) *
              volume sticky.refined.union) =
            (4⁻¹ * 2) *
              (multiplicity : ENNReal) * coarseCap⁻¹ *
                volume sticky.refined.union by ring, hfourTwo]
        simp only [one_div]
        ring
      _ ≤ (multiplicity : ENNReal) *
          volume
            (propertyThreeFinePullbackShading sticky.cover sticky.refined
              propertyThree).union := by gcongr
      _ = (multiplicity : ENNReal) *
          volume (ambientPropertyThreeCommonHull sticky propertyThree).union := by
        rw [htargetVolume]
      _ ≤ (ambientPropertyThreeCommonHull sticky propertyThree).mass :=
        htargetMass
  calc
    ((4 * stickyCoarseMultiplicityCap sticky : ENNReal)⁻¹) *
        (wz2PaperPureRefinementFraction delta logExponent *
          sourceShading.mass) =
        ((4 * coarseCap : ENNReal)⁻¹) *
          (wz2PaperPureRefinementFraction delta logExponent *
            sourceShading.mass) := by rfl
    _ ≤ ((4 * coarseCap : ENNReal)⁻¹) * sticky.refined.mass := by
      gcongr
      exact sticky.retained_mass
    _ ≤ (ambientPropertyThreeCommonHull sticky propertyThree).mass :=
      hrefinedToTarget

/-- Repackage the sharp dyadic common-hull estimate in the inverse-loss form
consumed by the extremality-restoration theorem. -/
lemma propertyThreeDyadicCommonHullMassLoss_inv_mul_source_mass_le
    {delta sigma outputLoss tau epsilon₁ epsilon₃ : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent multiplicity : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hsourceLower : ∀ point ∈ sourceShading.union,
      multiplicity ≤ sourceShading.pointMultiplicity point)
    (hsourceUpper : ∀ point ∈ sourceShading.union,
      sourceShading.pointMultiplicity point < 2 * multiplicity) :
    (propertyThreeDyadicCommonHullMassLoss sticky)⁻¹ *
        sourceShading.mass ≤
      (ambientPropertyThreeCommonHull sticky propP.propertyThree).mass := by
  have hfraction := pure_refinement_fraction_pos_ne_top
    hdelta hdeltaOne logExponent
  have hcoarsePos : 0 < stickyCoarseMultiplicityCap sticky := by
    unfold stickyCoarseMultiplicityCap
    apply ENNReal.mul_pos
    · exact (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos sticky.coarse_extremal.delta_pos _)).ne'
    · have hcard : (sticky.coarse.card : ENNReal) ≠ 0 := by
        exact_mod_cast sticky.coarse_extremal.nonempty.ne'
      simpa [Kakeya.Streamlined.TubeFamily.enncard] using hcard
  have hcoarseTop : stickyCoarseMultiplicityCap sticky ≠ ⊤ := by
    unfold stickyCoarseMultiplicityCap
    exact ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
      (by simp [Kakeya.Streamlined.TubeFamily.enncard])
  have raw := ambientPropertyThreeCommonHull_source_mass_lower_of_dyadic
    sticky propP.propertyThree hdelta
    (fun index => (propP.propertyThree_sub index).trans
      (propP.propertyOne_sub index))
    propP.propertyThree_cubical propP.propertyThree_mass
    hsourceLower hsourceUpper
  have hrewrite :
      (propertyThreeDyadicCommonHullMassLoss sticky)⁻¹ =
        (4 * stickyCoarseMultiplicityCap sticky)⁻¹ *
          wz2PaperPureRefinementFraction delta logExponent := by
    unfold propertyThreeDyadicCommonHullMassLoss
    rw [ENNReal.mul_inv
      (Or.inl (mul_ne_zero (by norm_num) hcoarsePos.ne'))
      (Or.inl (ENNReal.mul_ne_top (by norm_num) hcoarseTop)), inv_inv]
  rw [hrewrite]
  simpa only [mul_assoc] using raw

/-- Zero-extend the selected-family Property-Three output and restore every
ambient tube membership on its surviving spatial union.  This is the correct
common hull after an ordinary re-entry has selected a genuine tube
subfamily. -/
noncomputable def ambientSubfamilyPropertyThreeCommonHull
    {delta sigma outputLoss : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    (ambientShading : WZ1PaperTubeShading ambient)
    (selected : Kakeya.Streamlined.TubeSubfamily ambient)
    {sourceShading : WZ1PaperTubeShading selected.family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse) :
    WZ1PaperTubeShading ambient :=
  paperCommonSpatialHull ambientShading
    (extendShading selected
      (ambientPropertyThreeCommonHull sticky propertyThree))

lemma ambientSubfamilyPropertyThreeCommonHull_subshading
    {delta sigma outputLoss : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambient}
    {selected : Kakeya.Streamlined.TubeSubfamily ambient}
    {sourceShading : WZ1PaperTubeShading selected.family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse) :
    PaperIsSubshading
      (ambientSubfamilyPropertyThreeCommonHull ambientShading selected sticky
        propertyThree) ambientShading :=
  paperCommonSpatialHull_subshading _ _

lemma ambientSubfamilyPropertyThreeCommonHull_cubical
    {delta sigma outputLoss : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambient}
    (selected : Kakeya.Streamlined.TubeSubfamily ambient)
    {sourceShading : WZ1PaperTubeShading selected.family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse)
    (hambientCubical : WZ1PaperIsCubicalShading ambientShading)
    (hinnerCubical : WZ1PaperIsCubicalShading
      (ambientPropertyThreeCommonHull sticky propertyThree)) :
    WZ1PaperIsCubicalShading
      (ambientSubfamilyPropertyThreeCommonHull ambientShading selected sticky
        propertyThree) :=
  paperCommonSpatialHull_cubical hambientCubical
    (extendShading_cubical selected hinnerCubical)

lemma ambientSubfamilyPropertyThreeCommonHull_union
    {delta sigma outputLoss : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambient}
    (selected : Kakeya.Streamlined.TubeSubfamily ambient)
    {sourceShading : WZ1PaperTubeShading selected.family}
    (hsourceSub : PaperIsSubshading sourceShading
      (restrictPaperShading selected ambientShading))
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse) :
    (ambientSubfamilyPropertyThreeCommonHull ambientShading selected sticky
        propertyThree).union =
      (propertyThreeFinePullbackShading sticky.cover sticky.refined
        propertyThree).union := by
  have hselectedSub : PaperIsSubshading
      (ambientPropertyThreeCommonHull sticky propertyThree)
      (restrictPaperShading selected ambientShading) :=
    fun index point hpoint =>
      hsourceSub index
        (ambientPropertyThreeCommonHull_subshading sticky propertyThree index
          hpoint)
  have hextendedSub : PaperIsSubshading
      (extendShading selected
        (ambientPropertyThreeCommonHull sticky propertyThree))
      ambientShading :=
    extendShading_subshading selected hselectedSub
  rw [ambientSubfamilyPropertyThreeCommonHull,
    paperCommonSpatialHull_union hextendedSub,
    extendShading_union, ambientPropertyThreeCommonHull_union]

/-- Paper AD on the selected-family pullback transports to the ambient
common hull because zero-extension and the outer hull preserve its union. -/
lemma ambientSubfamilyPropertyThreeCommonHull_ad
    {delta sigma outputLoss queryScale alpha : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambient}
    (selected : Kakeya.Streamlined.TubeSubfamily ambient)
    {sourceShading : WZ1PaperTubeShading selected.family}
    (hsourceSub : PaperIsSubshading sourceShading
      (restrictPaperShading selected ambientShading))
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse)
    (plane center : Point3) (C : ENNReal)
    (hAD : PureWZ2PaperADSet1
      (scalarProjection plane
        ((propertyThreeFinePullbackShading sticky.cover sticky.refined
            propertyThree).union ∩
          Metric.closedBall center (Real.sqrt queryScale)))
      queryScale alpha C) :
    PureWZ2PaperADSet1
      (scalarProjection plane
        ((ambientSubfamilyPropertyThreeCommonHull ambientShading selected
            sticky propertyThree).union ∩
          Metric.closedBall center (Real.sqrt queryScale)))
      queryScale alpha C := by
  rw [ambientSubfamilyPropertyThreeCommonHull_union selected hsourceSub
    sticky propertyThree]
  exact hAD

/-- The outer common hull restores the complete ambient multiplicity at each
surviving point. -/
lemma ambientSubfamilyPropertyThreeCommonHull_pointMultiplicity_eq
    {delta sigma outputLoss : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    (ambientShading : WZ1PaperTubeShading ambient)
    (selected : Kakeya.Streamlined.TubeSubfamily ambient)
    {sourceShading : WZ1PaperTubeShading selected.family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse) :
    ∀ point ∈
        (ambientSubfamilyPropertyThreeCommonHull ambientShading selected sticky
          propertyThree).union,
      (ambientSubfamilyPropertyThreeCommonHull ambientShading selected sticky
          propertyThree).pointMultiplicity point =
        ambientShading.pointMultiplicity point :=
  paperCommonSpatialHull_pointMultiplicity_eq _ _

/-- The selected-family pullback uses the dyadic upper bound, while the outer
common hull uses the ambient dyadic lower bound.  This is the cancellation
needed after ordinary re-entry has selected a tube subfamily. -/
theorem ambientSubfamilyPropertyThreeCommonHull_source_mass_lower_of_dyadic
    {delta sigma outputLoss : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambient}
    (selected : Kakeya.Streamlined.TubeSubfamily ambient)
    {sourceShading : WZ1PaperTubeShading selected.family}
    (hsourceSub : PaperIsSubshading sourceShading
      (restrictPaperShading selected ambientShading))
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ} {multiplicity : ENNReal}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse)
    (_hdelta : 0 < delta)
    (hsub : PaperIsSubshading
      propertyThree sticky.croppedCoarseShading)
    (hcubical : WZ1PaperIsCubicalShading propertyThree)
    (hhalf :
      (1 / 2 : ENNReal) * sticky.croppedCoarseShading.mass ≤
        propertyThree.mass)
    (hambientLower : ∀ point ∈ ambientShading.union,
      multiplicity ≤ ambientShading.pointMultiplicity point)
    (hambientUpper : ∀ point ∈ ambientShading.union,
      ambientShading.pointMultiplicity point < 2 * multiplicity) :
    ((4 * stickyCoarseMultiplicityCap sticky : ENNReal)⁻¹) *
        (wz2PaperPureRefinementFraction delta logExponent *
          sourceShading.mass) ≤
      (ambientSubfamilyPropertyThreeCommonHull ambientShading selected sticky
        propertyThree).mass := by
  let coarseCap : ENNReal := stickyCoarseMultiplicityCap sticky
  let active : ENNReal := sticky.balanced.activeCells.card
  let good : ENNReal :=
    (propertyThreeGoodCells sticky.balanced propertyThree).card
  let cubeVolume : ENNReal :=
    volume (wz1PaperGridCube rho.1 (0, 0, 0))
  have hrho : 0 < rho.1 := sticky.coarse_extremal.delta_pos
  have hcoarseCapZero : coarseCap ≠ 0 := by
    dsimp only [coarseCap, stickyCoarseMultiplicityCap]
    apply mul_ne_zero
    · exact (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hrho (2 - sigma - outputLoss))).ne'
    · have hcoarseNonempty : sticky.coarse.Nonempty := by
        let sourceIndex : Fin sticky.selected.family.card :=
          ⟨0, sticky.selected_nonempty⟩
        rcases sticky.cover.covers sourceIndex with ⟨parent, _⟩
        exact Nat.zero_lt_of_lt parent.isLt
      simpa [Kakeya.Streamlined.TubeFamily.enncard] using
        hcoarseNonempty.ne'
  have hcoarseCapTop : coarseCap ≠ ⊤ := by
    dsimp only [coarseCap, stickyCoarseMultiplicityCap]
    exact ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
      (by simp [Kakeya.Streamlined.TubeFamily.enncard])
  have hpropertyMassUpper :
      propertyThree.mass ≤ coarseCap * (good * cubeVolume) := by
    calc
      propertyThree.mass ≤ coarseCap * volume propertyThree.union :=
        mass_le_of_pointMultiplicity_le (fun point hpoint => by
          have hnat := paperSubshading_pointMultiplicity_le
            propertyThree sticky.croppedCoarseShading hsub point
          have henn :
              (propertyThree.pointMultiplicity point : ENNReal) ≤
                (sticky.croppedCoarseShading.pointMultiplicity point :
                  ENNReal) := by exact_mod_cast hnat
          exact henn.trans (sticky.coarse_multiplicity_upper point))
      _ = coarseCap * (good * cubeVolume) := by
        rw [propertyThree_volume_eq_goodCells
          sticky.balanced hsub hcubical hrho]
  have hactiveWithCube :
      ((1 / 2 : ENNReal) * active) * cubeVolume ≤
        (coarseCap * good) * cubeVolume := by
    calc
      ((1 / 2 : ENNReal) * active) * cubeVolume =
          (1 / 2 : ENNReal) *
            volume sticky.croppedCoarseShading.union := by
        dsimp only [active, cubeVolume]
        rw [balanced_cover_coarse_volume sticky.balanced hrho]
        ring
      _ ≤ (1 / 2 : ENNReal) * sticky.croppedCoarseShading.mass := by
        gcongr
        simpa using multiplicity_floor_le_mass
          (one_le_pointMultiplicity_on_union
            sticky.croppedCoarseShading)
      _ ≤ propertyThree.mass := hhalf
      _ ≤ coarseCap * (good * cubeVolume) := hpropertyMassUpper
      _ = (coarseCap * good) * cubeVolume := by ring
  have hcubeZero : cubeVolume ≠ 0 :=
    (wz1PaperGridCube_volume_pos hrho (0, 0, 0)).ne'
  have hcubeTop : cubeVolume ≠ ⊤ :=
    wz1PaperGridCube_volume_ne_top hrho (0, 0, 0)
  have hgoodCount :
      coarseCap⁻¹ * ((1 / 2 : ENNReal) * active) ≤ good := by
    have hactiveCount :
        (1 / 2 : ENNReal) * active ≤ coarseCap * good :=
      (ENNReal.mul_le_mul_iff_right hcubeZero hcubeTop).mp <| by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hactiveWithCube
    calc
      coarseCap⁻¹ * ((1 / 2 : ENNReal) * active) ≤
          coarseCap⁻¹ * (coarseCap * good) := by gcongr
      _ = good := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcoarseCapZero
          hcoarseCapTop, one_mul]
  have hrefinedVolume :
      volume sticky.refined.union = active * sticky.balanced.cellMass := by
    simpa [active] using
      balanced_cover_fine_union_volume sticky.balanced hrho
  have hpullbackVolume :
      volume
          (propertyThreeFinePullbackShading sticky.cover sticky.refined
            propertyThree).union =
        good * sticky.balanced.cellMass := by
    simpa [good] using
      propertyThreeFinePullback_volume_eq_goodCells
        sticky.balanced hsub
  have hvolumeRetention :
      (1 / 2 : ENNReal) * coarseCap⁻¹ *
          volume sticky.refined.union ≤
        volume
          (propertyThreeFinePullbackShading sticky.cover sticky.refined
            propertyThree).union := by
    rw [hrefinedVolume, hpullbackVolume]
    calc
      (1 / 2 : ENNReal) * coarseCap⁻¹ *
            (active * sticky.balanced.cellMass) =
          (coarseCap⁻¹ * ((1 / 2 : ENNReal) * active)) *
            sticky.balanced.cellMass := by ring
      _ ≤ good * sticky.balanced.cellMass := by gcongr
  have hrefinedUpper : ∀ point ∈ sticky.refined.union,
      sticky.refined.pointMultiplicity point < 2 * multiplicity := by
    intro point hpoint
    have hsourcePoint : point ∈ sourceShading.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨sticky.selected.embedding index,
        sticky.subshading index hindex⟩
    have hrestrictedPoint : point ∈
        (restrictPaperShading selected ambientShading).union := by
      rcases hsourcePoint with ⟨index, hindex⟩
      exact ⟨index, hsourceSub index hindex⟩
    have hambientPoint : point ∈ ambientShading.union := by
      rcases hrestrictedPoint with ⟨index, hindex⟩
      exact ⟨selected.embedding index, hindex⟩
    have hrefinedSource :=
      sticky_refined_pointMultiplicity_le_source sticky point
    have hsourceRestricted := paperSubshading_pointMultiplicity_le
      sourceShading (restrictPaperShading selected ambientShading)
      hsourceSub point
    have hrestrictedAmbient := restrictPaperShading_pointMultiplicity_le
      selected ambientShading point
    have hleNat := hrefinedSource.trans
      (hsourceRestricted.trans hrestrictedAmbient)
    have hleENN :
        (sticky.refined.pointMultiplicity point : ENNReal) ≤
          (ambientShading.pointMultiplicity point : ENNReal) := by
      exact_mod_cast hleNat
    exact hleENN.trans_lt (hambientUpper point hambientPoint)
  have hrefinedMass :
      sticky.refined.mass ≤ (2 * multiplicity : ENNReal) *
        volume sticky.refined.union := by
    apply mass_le_of_pointMultiplicity_le
    intro point hpoint
    exact_mod_cast (hrefinedUpper point hpoint).le
  let target := ambientSubfamilyPropertyThreeCommonHull
    ambientShading selected sticky propertyThree
  have htargetMultiplicity : ∀ point ∈ target.union,
      multiplicity ≤ target.pointMultiplicity point := by
    intro point hpoint
    rw [ambientSubfamilyPropertyThreeCommonHull_pointMultiplicity_eq
      ambientShading selected sticky propertyThree point hpoint]
    have hambientPoint : point ∈ ambientShading.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index,
        ambientSubfamilyPropertyThreeCommonHull_subshading sticky
          propertyThree index hindex⟩
    exact hambientLower point hambientPoint
  have htargetMass : (multiplicity : ENNReal) * volume target.union ≤
      target.mass :=
    multiplicity_floor_le_mass htargetMultiplicity
  have htargetVolume : target.union =
      (propertyThreeFinePullbackShading sticky.cover sticky.refined
        propertyThree).union := by
    exact ambientSubfamilyPropertyThreeCommonHull_union selected hsourceSub
      sticky propertyThree
  have hrefinedToTarget :
      ((4 * coarseCap : ENNReal)⁻¹) * sticky.refined.mass ≤ target.mass := by
    calc
      ((4 * coarseCap : ENNReal)⁻¹) * sticky.refined.mass ≤
          ((4 * coarseCap : ENNReal)⁻¹) *
            ((2 * multiplicity : ENNReal) *
              volume sticky.refined.union) := by gcongr
      _ = (multiplicity : ENNReal) *
          ((1 / 2 : ENNReal) * coarseCap⁻¹ *
            volume sticky.refined.union) := by
        rw [ENNReal.mul_inv (Or.inr hcoarseCapTop)
          (Or.inr hcoarseCapZero)]
        have hfourTwo : (4 : ENNReal)⁻¹ * 2 = 2⁻¹ := by
          have hfour : (4 : ENNReal)⁻¹ =
              ENNReal.ofReal (1 / 4 : ℝ) := by
            simp
          have htwo : (2 : ENNReal)⁻¹ =
              ENNReal.ofReal (1 / 2 : ℝ) := by
            simp
          rw [hfour, htwo, show (2 : ENNReal) =
            ENNReal.ofReal (2 : ℝ) by norm_num]
          rw [← ENNReal.ofReal_mul (by norm_num)]
          norm_num
        rw [show
          4⁻¹ * coarseCap⁻¹ * (2 * (multiplicity : ENNReal) *
              volume sticky.refined.union) =
            (4⁻¹ * 2) * (multiplicity : ENNReal) * coarseCap⁻¹ *
              volume sticky.refined.union by ring, hfourTwo]
        simp only [one_div]
        ring
      _ ≤ (multiplicity : ENNReal) *
          volume
            (propertyThreeFinePullbackShading sticky.cover sticky.refined
              propertyThree).union := by gcongr
      _ = (multiplicity : ENNReal) * volume target.union := by
        rw [htargetVolume]
      _ ≤ target.mass := htargetMass
  calc
    ((4 * stickyCoarseMultiplicityCap sticky : ENNReal)⁻¹) *
        (wz2PaperPureRefinementFraction delta logExponent *
          sourceShading.mass) =
        ((4 * coarseCap : ENNReal)⁻¹) *
          (wz2PaperPureRefinementFraction delta logExponent *
            sourceShading.mass) := by rfl
    _ ≤ ((4 * coarseCap : ENNReal)⁻¹) * sticky.refined.mass := by
      gcongr
      exact sticky.retained_mass
    _ ≤ target.mass := hrefinedToTarget

/-- Inverse-loss form of the selected-source/ambient-dyadic cancellation. -/
lemma ambientSubfamilyPropertyThreeCommonHull_mass_loss
    {delta sigma outputLoss tau epsilon₁ epsilon₃ : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambient}
    (selected : Kakeya.Streamlined.TubeSubfamily ambient)
    {sourceShading : WZ1PaperTubeShading selected.family}
    (hsourceSub : PaperIsSubshading sourceShading
      (restrictPaperShading selected ambientShading))
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ} {multiplicity : ENNReal}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hambientLower : ∀ point ∈ ambientShading.union,
      multiplicity ≤ ambientShading.pointMultiplicity point)
    (hambientUpper : ∀ point ∈ ambientShading.union,
      ambientShading.pointMultiplicity point < 2 * multiplicity) :
    (propertyThreeDyadicCommonHullMassLoss sticky)⁻¹ *
        sourceShading.mass ≤
      (ambientSubfamilyPropertyThreeCommonHull ambientShading selected sticky
        propP.propertyThree).mass := by
  have hfraction := pure_refinement_fraction_pos_ne_top
    hdelta hdeltaOne logExponent
  have hcoarsePos : 0 < stickyCoarseMultiplicityCap sticky := by
    unfold stickyCoarseMultiplicityCap
    apply ENNReal.mul_pos
    · exact (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos sticky.coarse_extremal.delta_pos _)).ne'
    · have hcard : (sticky.coarse.card : ENNReal) ≠ 0 := by
        exact_mod_cast sticky.coarse_extremal.nonempty.ne'
      simpa [Kakeya.Streamlined.TubeFamily.enncard] using hcard
  have hcoarseTop : stickyCoarseMultiplicityCap sticky ≠ ⊤ := by
    unfold stickyCoarseMultiplicityCap
    exact ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
      (by simp [Kakeya.Streamlined.TubeFamily.enncard])
  have raw :=
    ambientSubfamilyPropertyThreeCommonHull_source_mass_lower_of_dyadic
      selected hsourceSub sticky propP.propertyThree hdelta
      (fun index => (propP.propertyThree_sub index).trans
        (propP.propertyOne_sub index))
      propP.propertyThree_cubical propP.propertyThree_mass
      hambientLower hambientUpper
  have hrewrite :
      (propertyThreeDyadicCommonHullMassLoss sticky)⁻¹ =
        (4 * stickyCoarseMultiplicityCap sticky)⁻¹ *
          wz2PaperPureRefinementFraction delta logExponent := by
    unfold propertyThreeDyadicCommonHullMassLoss
    rw [ENNReal.mul_inv
      (Or.inl (mul_ne_zero (by norm_num) hcoarsePos.ne'))
      (Or.inl (ENNReal.mul_ne_top (by norm_num) hcoarseTop)), inv_inv]
  rw [hrewrite]
  simpa only [mul_assoc] using raw

end Kakeya.Assouad.PureWZ2

end
