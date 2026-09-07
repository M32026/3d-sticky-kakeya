import MyLeanRepo.Kakeya.Assouad.PureWZ2.CenteredStrictFiberBounds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GenericMultiplicityScalarNormalization
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingJacobian

/-!
# Cardinality lower bound directly from pure Definition 2.12

Request the top scale `1`.  One complete strict fiber is nonempty, and its
actual outer-John body family satisfies normalized Convex-Wolff counting.
Because the actual parent radius is at least one, every normalized source
`delta`-tube body has volume at most `48 * delta^2`.  Counting one body then
gives the required cardinality product for the entire source family.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem pureWZ2_pure_cwa_top_cardinality_product
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (familyNonempty : family.Nonempty)
    {C : ENNReal}
    (cwa : WZ2PaperPureCWAAtNearbyScales family C) :
    (1 : ENNReal) ≤
      ((48 : ENNReal) * C) *
        Kakeya.realRpowENN delta 2 *
        family.enncard := by
  let requested : WZ2PaperRequestedScale delta :=
    ⟨1, hdeltaOne, le_rfl⟩
  rcases cwa.2.2.2 requested with ⟨nearby⟩
  let scaleData := nearby.scaleData
  let source : Fin family.card := ⟨0, familyNonempty⟩
  let parent : Fin scaleData.coarse.card :=
    scaleData.cover.parent source
  have sourceMem :
      source ∈
        wz2PaperOrdinaryFullFiberIndices
          family scaleData.coarse parent :=
    scaleData.cover.parent_mem_fullFiber source
  let sourceMember :
      wz2PaperOrdinaryFullFiberIndices
        family scaleData.coarse parent :=
    ⟨source, sourceMem⟩
  let bodyIndex :
      Fin
        (wz2PaperOrdinaryFullFiberIndices
          family scaleData.coarse parent).card :=
    (wz2PaperOrdinaryFullFiberIndexEquiv parent).symm
      sourceMember
  let fiber :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := family) (coarse := scaleData.coarse)
        parent C :=
    Classical.choice (scaleData.rescaledFiber parent)
  let bodies :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := family) (coarse := scaleData.coarse)
      parent fiber.normalization
  have sourceIndexEq :
      ((wz2PaperOrdinaryFullFiberIndexEquiv parent)
        bodyIndex).1 = source := by
    exact congrArg Subtype.val <|
      (wz2PaperOrdinaryFullFiberIndexEquiv parent)
        |>.apply_symm_apply sourceMember
  have bodyCarrierEq :
      (bodies.body bodyIndex).carrier =
        fiber.normalization.map ''
          (family.tube source).carrier := by
    change
      fiber.normalization.map ''
          (family.tube
            ((wz2PaperOrdinaryFullFiberIndexEquiv parent)
              bodyIndex).1).carrier =
        fiber.normalization.map ''
          (family.tube source).carrier
    rw [sourceIndexEq]
  have bodyConvex :
      Convex ℝ (bodies.body bodyIndex).carrier := by
    rw [bodyCarrierEq]
    exact
      Convex.affine_image fiber.normalization.map.toAffineMap
        (wz2_paper_ordinary_tube_carrier_convex
          (family.tube source))
  have bodyMember :
      bodyIndex ∈
        bodies.containedIndices
          (bodies.body bodyIndex).carrier := by
    exact
      Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
        Set.Subset.rfl
  have bodyCount :
      (1 : ENNReal) ≤
        bodies.containedCount
          (bodies.body bodyIndex).carrier := by
    change
      (1 : ENNReal) ≤
        ((bodies.containedIndices
          (bodies.body bodyIndex).carrier).card : ENNReal)
    exact_mod_cast
      Finset.one_le_card.mpr ⟨bodyIndex, bodyMember⟩
  have actualOne : 1 ≤ nearby.rho := by
    simpa [requested] using nearby.requested_le
  let detENN : ENNReal :=
    ENNReal.ofReal
      |LinearMap.det
        (fiber.normalization.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)|
  have detQuarter :
      (1 / 4 : ℝ) ≤
        |LinearMap.det
          (fiber.normalization.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| := by
    calc
      (1 / 4 : ℝ) ≤ nearby.rho ^ 2 / 4 := by
        nlinarith
      _ ≤
          |LinearMap.det
            (fiber.normalization.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)| :=
        wz2Paper_outerJohn_abs_det_lower
          (scaleData.coarse.tube parent) scaleData.rho_pos
  have detQuarterENN :
      ENNReal.ofReal (1 / 4 : ℝ) ≤ detENN := by
    exact ENNReal.ofReal_mono detQuarter
  have detInvUpper : detENN⁻¹ ≤ 4 := by
    have quarterEq :
        ENNReal.ofReal (1 / 4 : ℝ) = (4 : ENNReal)⁻¹ := by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4)]
      norm_num
    calc
      detENN⁻¹ ≤
          (ENNReal.ofReal (1 / 4 : ℝ))⁻¹ :=
        ENNReal.inv_le_inv' detQuarterENN
      _ = 4 := by rw [quarterEq, inv_inv]
  have mapDet :
      ENNReal.ofReal
          |LinearMap.det
            (fiber.normalization.map.linear :
              Point3 →ₗ[ℝ] Point3)| =
        detENN⁻¹ := by
    have linearEq :
        fiber.normalization.map.linear =
          (fiber.normalization.parent_convex_body
            |>.outerJohnEllipsoidMap).symm := rfl
    rw [linearEq, LinearEquiv.det_coe_symm, abs_inv,
      ENNReal.ofReal_inv_of_pos]
    let johnMap :=
      fiber.normalization.parent_convex_body.outerJohnEllipsoidMap
    exact
      abs_pos.mpr
        (LinearEquiv.isUnit_det' johnMap).ne_zero
  have sourceVolume :
      volume (family.tube source).carrier =
        Kakeya.deltaTubeVolume delta :=
    tube_volume_scaling.1 delta (family.tube source)
  have bodyVolume :
      volume (bodies.body bodyIndex).carrier ≤
        (48 : ENNReal) *
          Kakeya.realRpowENN delta 2 := by
    rw [bodyCarrierEq,
      wz2PaperAffineEquiv_volume_image_eq,
      mapDet, sourceVolume]
    calc
      detENN⁻¹ * Kakeya.deltaTubeVolume delta ≤
          (4 : ENNReal) *
            Kakeya.deltaTubeVolume delta := by
        gcongr
      _ ≤
          (4 : ENNReal) *
            ((12 : ENNReal) *
              Kakeya.realRpowENN delta 2) := by
        gcongr
        exact
          pure_wz2_deltaTubeVolume_upper_twelve
            hdelta hdeltaOne
      _ =
          (48 : ENNReal) *
            Kakeya.realRpowENN delta 2 := by ring
  have bodyCardinality :
      bodies.enncard ≤ family.enncard := by
    change
      ((wz2PaperOrdinaryFullFiberIndices
          family scaleData.coarse parent).card : ENNReal) ≤
        (family.card : ENNReal)
    exact_mod_cast
      (show
        (wz2PaperOrdinaryFullFiberIndices
          family scaleData.coarse parent).card ≤ family.card by
        simpa using
          Finset.card_le_univ
            (wz2PaperOrdinaryFullFiberIndices
              family scaleData.coarse parent))
  calc
    (1 : ENNReal) ≤
        bodies.containedCount
          (bodies.body bodyIndex).carrier :=
      bodyCount
    _ ≤
        C * volume (bodies.body bodyIndex).carrier *
          bodies.enncard :=
      fiber.convex_wolff
        (bodies.body bodyIndex).carrier bodyConvex
    _ ≤
        C *
            ((48 : ENNReal) *
              Kakeya.realRpowENN delta 2) *
          family.enncard := by
      gcongr
    _ =
        ((48 : ENNReal) * C) *
          Kakeya.realRpowENN delta 2 *
          family.enncard := by ring

theorem pureWZ2_pure_cwa_cardinality_lower
    {delta strongLoss : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (familyNonempty : family.Nonempty)
    {C : ENNReal}
    (cwa : WZ2PaperPureCWAAtNearbyScales family C)
    (absorption :
      (48 : ENNReal) * C ≤
        Kakeya.realRpowENN delta (-2 * strongLoss)) :
    Kakeya.realRpowENN delta (-2 + 2 * strongLoss) ≤
      family.enncard := by
  have product :=
    pureWZ2_pure_cwa_top_cardinality_product
      hdelta hdeltaOne familyNonempty cwa
  have absorbed :
      (1 : ENNReal) ≤
        Kakeya.realRpowENN delta (2 - 2 * strongLoss) *
          family.enncard := by
    calc
      (1 : ENNReal) ≤
          ((48 : ENNReal) * C) *
            Kakeya.realRpowENN delta 2 *
            family.enncard :=
        product
      _ ≤
          Kakeya.realRpowENN delta (-2 * strongLoss) *
            Kakeya.realRpowENN delta 2 *
            family.enncard := by
        gcongr
      _ =
          Kakeya.realRpowENN delta (2 - 2 * strongLoss) *
            family.enncard := by
        rw [← realRpowENN_add hdelta]
        congr 1
        ring
  exact
    pureWZ2_cardinality_lower_of_power_product
      hdelta absorbed

end Kakeya.Assouad

end
