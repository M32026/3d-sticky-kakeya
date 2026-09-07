import MyLeanRepo.Kakeya.Assouad.PureWZ2.CompleteFiberActualScale
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnCWATransport

/-!
# Canonical John transport between nested same-axis parents

If an ordinary parent radius is enlarged from `actual` to `coarser`, the
canonical outer-John coordinate change loses at most
`81 * (coarser / actual)^2` in volume.  The physical fine bodies are unchanged,
so this transports complete-fiber Body CWA directly.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Canonical coordinate change from an actual parent John chart to a coarser
same-axis parent John chart. -/
noncomputable def wz2PaperSameAxisJohnCoordinateChange
    {actual coarser : ℝ}
    {actualParent : Kakeya.DeltaTube actual}
    (actualJohn : WZ2PaperAssouadUnitRescalingData actualParent)
    (coarserJohn :
      WZ2PaperAssouadUnitRescalingData
        (sameAxisTube (rho := coarser) actualParent)) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  actualJohn.map.symm.trans coarserJohn.map

@[simp]
theorem wz2PaperSameAxisJohnCoordinateChange_apply_map
    {actual coarser : ℝ}
    {actualParent : Kakeya.DeltaTube actual}
    (actualJohn : WZ2PaperAssouadUnitRescalingData actualParent)
    (coarserJohn :
      WZ2PaperAssouadUnitRescalingData
        (sameAxisTube (rho := coarser) actualParent))
    (point : Point3) :
    wz2PaperSameAxisJohnCoordinateChange actualJohn coarserJohn
        (actualJohn.map point) =
      coarserJohn.map point := by
  simp [wz2PaperSameAxisJohnCoordinateChange, AffineEquiv.trans_apply]

theorem wz2PaperSameAxisJohnCoordinateChange_image
    {actual coarser : ℝ}
    {actualParent : Kakeya.DeltaTube actual}
    (actualJohn : WZ2PaperAssouadUnitRescalingData actualParent)
    (coarserJohn :
      WZ2PaperAssouadUnitRescalingData
        (sameAxisTube (rho := coarser) actualParent))
    (source : Set Point3) :
    wz2PaperSameAxisJohnCoordinateChange actualJohn coarserJohn ''
        (actualJohn.map '' source) =
      coarserJohn.map '' source := by
  ext point
  constructor
  · rintro ⟨actualPoint, ⟨sourcePoint, sourceMem, rfl⟩, rfl⟩
    exact
      ⟨sourcePoint, sourceMem,
        (wz2PaperSameAxisJohnCoordinateChange_apply_map
          actualJohn coarserJohn sourcePoint).symm⟩
  · rintro ⟨sourcePoint, sourceMem, rfl⟩
    exact
      ⟨actualJohn.map sourcePoint,
        ⟨sourcePoint, sourceMem, rfl⟩,
        wz2PaperSameAxisJohnCoordinateChange_apply_map
          actualJohn coarserJohn sourcePoint⟩

private theorem sameAxis_outerJohn_det_ratio
    {actual coarser : ℝ}
    (actualPos : 0 < actual)
    (coarserPos : 0 < coarser)
    (actualLeCoarser : actual ≤ coarser)
    (coarserLeOne : coarser ≤ 1)
    {actualParent : Kakeya.DeltaTube actual}
    (actualJohn : WZ2PaperAssouadUnitRescalingData actualParent)
    (coarserJohn :
      WZ2PaperAssouadUnitRescalingData
        (sameAxisTube (rho := coarser) actualParent)) :
    |LinearMap.det
        (coarserJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)| ≤
      (81 * (coarser / actual) ^ 2) *
        |LinearMap.det
          (actualJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| := by
  let unitBallVolume : ENNReal :=
    volume (Metric.closedBall (0 : Point3) 1)
  have unitBallPos : 0 < unitBallVolume :=
    Metric.measure_closedBall_pos volume (0 : Point3) (by norm_num)
  have unitBallTop : unitBallVolume ≠ ⊤ :=
    (ProperSpace.isCompact_closedBall (0 : Point3) 1).measure_ne_top
  have actualCarrier :
      actualParent.carrier ⊆
        actualJohn.parent_convex_body.outerJohnEllipsoid :=
    actualJohn.parent_convex_body.outerJohnEllipsoid_spec.1
  have tubeRatio :
      volume
          (sameAxisTube (rho := coarser) actualParent).carrier ≤
        3 * Kakeya.realRpowENN coarser 2 *
            (Kakeya.realRpowENN actual 2)⁻¹ *
          volume actualParent.carrier := by
    change
      (sameAxisTube (rho := coarser) actualParent).volume ≤
        3 * Kakeya.realRpowENN coarser 2 *
            (Kakeya.realRpowENN actual 2)⁻¹ *
          actualParent.volume
    rw [tube_volume_scaling.1 coarser
        (sameAxisTube (rho := coarser) actualParent),
      tube_volume_scaling.1 actual actualParent]
    exact
      deltaTubeVolume_ratio_bound_cylinder
        actualPos actualLeCoarser coarserLeOne
  have ellipsoidVolume :
      volume coarserJohn.parent_convex_body.outerJohnEllipsoid ≤
        (81 : ENNReal) *
          (Kakeya.realRpowENN coarser 2 *
            (Kakeya.realRpowENN actual 2)⁻¹) *
          volume actualJohn.parent_convex_body.outerJohnEllipsoid := by
    calc
      volume coarserJohn.parent_convex_body.outerJohnEllipsoid ≤
          (27 : ENNReal) *
            volume
              (sameAxisTube (rho := coarser) actualParent).carrier :=
        coarserJohn.outerJohn_volume_le_twentySeven
      _ ≤
          (27 : ENNReal) *
            (3 * Kakeya.realRpowENN coarser 2 *
                (Kakeya.realRpowENN actual 2)⁻¹ *
              volume actualParent.carrier) := by
        gcongr
      _ ≤
          (27 : ENNReal) *
            (3 * Kakeya.realRpowENN coarser 2 *
                (Kakeya.realRpowENN actual 2)⁻¹ *
              volume
                actualJohn.parent_convex_body.outerJohnEllipsoid) := by
        gcongr
      _ =
          (81 : ENNReal) *
            (Kakeya.realRpowENN coarser 2 *
              (Kakeya.realRpowENN actual 2)⁻¹) *
            volume
              actualJohn.parent_convex_body.outerJohnEllipsoid := by
        ring
  have scaleRatio :
      Kakeya.realRpowENN coarser 2 *
          (Kakeya.realRpowENN actual 2)⁻¹ =
        ENNReal.ofReal ((coarser / actual) ^ 2) := by
    rw [show
      Kakeya.realRpowENN coarser 2 =
        ENNReal.ofReal (coarser ^ 2) by
          simp [Kakeya.realRpowENN, Real.rpow_two]]
    rw [show
      Kakeya.realRpowENN actual 2 =
        ENNReal.ofReal (actual ^ 2) by
          simp [Kakeya.realRpowENN, Real.rpow_two]]
    rw [← ENNReal.ofReal_inv_of_pos (sq_pos_of_pos actualPos)]
    rw [← ENNReal.ofReal_mul (sq_nonneg coarser)]
    congr 1
    field_simp [actualPos.ne']
  have targetVolume :
      volume coarserJohn.parent_convex_body.outerJohnEllipsoid =
        ENNReal.ofReal
            |LinearMap.det
              (coarserJohn.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)| *
          unitBallVolume :=
    JohnEllipsoid.volume_ellipsoid_eq
      coarserJohn.parent_convex_body.outerJohnEllipsoidCenter
      coarserJohn.parent_convex_body.outerJohnEllipsoidMap
  have sourceVolume :
      volume actualJohn.parent_convex_body.outerJohnEllipsoid =
        ENNReal.ofReal
            |LinearMap.det
              (actualJohn.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)| *
          unitBallVolume :=
    JohnEllipsoid.volume_ellipsoid_eq
      actualJohn.parent_convex_body.outerJohnEllipsoidCenter
      actualJohn.parent_convex_body.outerJohnEllipsoidMap
  rw [targetVolume, sourceVolume, scaleRatio] at ellipsoidVolume
  have coefficient :
      (81 : ENNReal) *
          ENNReal.ofReal ((coarser / actual) ^ 2) =
        ENNReal.ofReal (81 * (coarser / actual) ^ 2) := by
    rw [← ENNReal.ofReal_ofNat (n := 81),
      ← ENNReal.ofReal_mul (by norm_num)]
  rw [coefficient] at ellipsoidVolume
  have rearranged :
      ENNReal.ofReal (81 * (coarser / actual) ^ 2) *
            (ENNReal.ofReal
                |LinearMap.det
                  (actualJohn.parent_convex_body.outerJohnEllipsoidMap :
                    Point3 →ₗ[ℝ] Point3)| *
              unitBallVolume) =
        (ENNReal.ofReal (81 * (coarser / actual) ^ 2) *
            ENNReal.ofReal
              |LinearMap.det
                (actualJohn.parent_convex_body.outerJohnEllipsoidMap :
                  Point3 →ₗ[ℝ] Point3)|) *
          unitBallVolume := by
    ring
  rw [rearranged] at ellipsoidVolume
  have detENN :
      ENNReal.ofReal
          |LinearMap.det
            (coarserJohn.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)| ≤
        ENNReal.ofReal (81 * (coarser / actual) ^ 2) *
          ENNReal.ofReal
            |LinearMap.det
              (actualJohn.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)| :=
    (ENNReal.mul_le_mul_iff_left
      unitBallPos.ne' unitBallTop).1 ellipsoidVolume
  rw [← ENNReal.ofReal_mul (by positivity)] at detENN
  exact
    (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (by positivity) (abs_nonneg _))).1 detENN

/-- The inverse John coordinate change loses at most the quadratic
same-axis radius ratio. -/
theorem wz2PaperSameAxisJohnCoordinateChange_inverse_volume
    {actual coarser : ℝ}
    (actualPos : 0 < actual)
    (coarserPos : 0 < coarser)
    (actualLeCoarser : actual ≤ coarser)
    (coarserLeOne : coarser ≤ 1)
    {actualParent : Kakeya.DeltaTube actual}
    (actualJohn : WZ2PaperAssouadUnitRescalingData actualParent)
    (coarserJohn :
      WZ2PaperAssouadUnitRescalingData
        (sameAxisTube (rho := coarser) actualParent))
    (targetSet : Set Point3) :
    volume
        ((wz2PaperSameAxisJohnCoordinateChange
          actualJohn coarserJohn).symm '' targetSet) ≤
      ENNReal.ofReal (81 * (coarser / actual) ^ 2) *
        volume targetSet := by
  let coordinateChange :=
    wz2PaperSameAxisJohnCoordinateChange actualJohn coarserJohn
  rw [wz2PaperAffineEquiv_volume_image_eq]
  have targetDet :=
    sameAxis_outerJohn_det_ratio
      actualPos coarserPos actualLeCoarser coarserLeOne
      actualJohn coarserJohn
  have sourceDetPos :
      0 <
        |LinearMap.det
          (actualJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr
      (LinearEquiv.isUnit_det'
        actualJohn.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have targetDetPos :
      0 <
        |LinearMap.det
          (coarserJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr
      (LinearEquiv.isUnit_det'
        coarserJohn.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have coordinateDet :
      (81 * (coarser / actual) ^ 2)⁻¹ ≤
        |LinearMap.det
          (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| := by
    change
      (81 * (coarser / actual) ^ 2)⁻¹ ≤
        |LinearMap.det
          ((actualJohn.map.symm.linear.trans
            coarserJohn.map.linear : Point3 ≃ₗ[ℝ] Point3) :
            Point3 →ₗ[ℝ] Point3)|
    rw [show
      ((actualJohn.map.symm.linear.trans
        coarserJohn.map.linear : Point3 ≃ₗ[ℝ] Point3) :
          Point3 →ₗ[ℝ] Point3) =
        (coarserJohn.map.linear : Point3 →ₗ[ℝ] Point3).comp
          (actualJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3) by
            ext point
            rfl,
      LinearMap.det_comp, abs_mul]
    have sourceLinear :
        (actualJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
          actualJohn.parent_convex_body.outerJohnEllipsoidMap := rfl
    have targetLinear :
        (coarserJohn.map.linear : Point3 →ₗ[ℝ] Point3) =
          coarserJohn.parent_convex_body.outerJohnEllipsoidMap.symm := rfl
    rw [sourceLinear, targetLinear,
      LinearEquiv.det_coe_symm, abs_inv]
    rw [mul_comm
      |LinearMap.det
        (coarserJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)|⁻¹]
    change
      (81 * (coarser / actual) ^ 2)⁻¹ ≤
        |LinearMap.det
          (actualJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| /
          |LinearMap.det
            (coarserJohn.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)|
    apply (le_div_iff₀ targetDetPos).2
    calc
      (81 * (coarser / actual) ^ 2)⁻¹ *
            |LinearMap.det
              (coarserJohn.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)| ≤
          (81 * (coarser / actual) ^ 2)⁻¹ *
            ((81 * (coarser / actual) ^ 2) *
              |LinearMap.det
                (actualJohn.parent_convex_body.outerJohnEllipsoidMap :
                  Point3 →ₗ[ℝ] Point3)|) := by
        gcongr
      _ =
          |LinearMap.det
            (actualJohn.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)| := by
        have coefficientPos :
            0 < 81 * (coarser / actual) ^ 2 := by positivity
        field_simp [coefficientPos.ne']
  have coordinateDetPos :
      0 <
        |LinearMap.det
          (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr
      (LinearEquiv.isUnit_det' coordinateChange.linear).ne_zero
  have inverseDet :
      |LinearMap.det
          (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
        81 * (coarser / actual) ^ 2 := by
    have symmLinear :
        coordinateChange.symm.linear =
          coordinateChange.linear.symm := rfl
    rw [symmLinear, LinearEquiv.det_coe_symm, abs_inv]
    apply (inv_le_iff_one_le_mul₀ coordinateDetPos).2
    have coefficientPos :
        0 < 81 * (coarser / actual) ^ 2 := by positivity
    calc
      (1 : ℝ) =
          (81 * (coarser / actual) ^ 2) *
            (81 * (coarser / actual) ^ 2)⁻¹ := by
        field_simp [coefficientPos.ne']
      _ ≤
          (81 * (coarser / actual) ^ 2) *
            |LinearMap.det
              (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| :=
        mul_le_mul_of_nonneg_left coordinateDet coefficientPos.le
  exact
    mul_le_mul_right'
      (ENNReal.ofReal_mono inverseDet)
      (volume targetSet)

/-- Transport complete-fiber Body CWA from an actual parent to a nested
same-axis coarser parent. -/
theorem wz2PaperBodyConvexWolffBound_of_sameAxisJohnTransport
    {actual coarser : ℝ}
    (actualPos : 0 < actual)
    (coarserPos : 0 < coarser)
    (actualLeCoarser : actual ≤ coarser)
    (coarserLeOne : coarser ≤ 1)
    {actualParent : Kakeya.DeltaTube actual}
    (actualJohn : WZ2PaperAssouadUnitRescalingData actualParent)
    (coarserJohn :
      WZ2PaperAssouadUnitRescalingData
        (sameAxisTube (rho := coarser) actualParent))
    {source target : Kakeya.Streamlined.BodyFamily}
    {C : ENNReal}
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (sourcePhysical targetPhysical :
      Fin target.card → Set Point3)
    (source_carrier :
      ∀ index,
        (source.body (indexEquiv index)).carrier =
          actualJohn.map '' sourcePhysical index)
    (target_carrier :
      ∀ index,
        (target.body index).carrier =
          coarserJohn.map '' targetPhysical index)
    (physical_subset :
      ∀ index, sourcePhysical index ⊆ targetPhysical index)
    (sourceCWA : WZ2PaperBodyConvexWolffBound source C) :
    WZ2PaperBodyConvexWolffBound target
      (ENNReal.ofReal (81 * (coarser / actual) ^ 2) * C) := by
  apply
    wz2PaperBodyConvexWolffBound_of_affineTransport
      (wz2PaperSameAxisJohnCoordinateChange actualJohn coarserJohn)
      indexEquiv
  · intro targetIndex
    rw [source_carrier, target_carrier,
      wz2PaperSameAxisJohnCoordinateChange_image]
    exact Set.image_mono (physical_subset targetIndex)
  · intro targetSet
    exact
      wz2PaperSameAxisJohnCoordinateChange_inverse_volume
        actualPos coarserPos actualLeCoarser coarserLeOne
        actualJohn coarserJohn targetSet
  · exact sourceCWA

/--
The complete selected actual fiber has a coarser singleton same-axis scale
witness.  Its CWA loss is exactly the quadratic same-axis John ratio.
-/
noncomputable def pureWZ2_completeFiber_coarserScale
    {delta actual coarser : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualC outputC : ENNReal}
    (actualScale : WZ2PaperPureScaleCoverData fine actual actualC)
    (parent : Fin actualScale.coarse.card)
    (actualLeCoarser : actual ≤ coarser)
    (coarserPos : 0 < coarser)
    (coarserLeOne : coarser ≤ 1)
    (outputOne : 1 ≤ outputC)
    (constantAbsorption :
      ENNReal.ofReal (81 * (coarser / actual) ^ 2) * actualC ≤
        outputC) :
    WZ2PaperPureScaleCoverData
      (PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
        actualScale.cover
        ({parent} : Finset (Fin actualScale.coarse.card))
        (Finset.singleton_nonempty parent)).selectedFine.family
      coarser outputC := by
  let complete :=
    PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
      actualScale.cover
      ({parent} : Finset (Fin actualScale.coarse.card))
      (Finset.singleton_nonempty parent)
  let coarse : Kakeya.Streamlined.TubeFamily coarser :=
    {
      card := 1
      tube := fun _ =>
        sameAxisTube (rho := coarser)
          (actualScale.coarse.tube parent)
    }
  let actualJohn :=
    Classical.choice (actualScale.rescaledFiber parent)
  let coarserJohn :=
    WZ2PaperAssouadUnitRescalingData.ofTube
      (coarse.tube 0) coarserPos
  let sourceBody :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := fine) (coarse := actualScale.coarse)
      parent actualJohn.normalization
  let targetBody :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := complete.selectedFine.family)
      (coarse := coarse) 0 coarserJohn
  have indicesEq :
      complete.selectedFineIndices =
        wz2PaperOrdinaryFullFiberIndices
          fine actualScale.coarse parent :=
    pureWZ2_singletonComplete_selectedFineIndices
      actualScale.cover actualScale.rho_pos.le parent
  let targetFiber :=
    wz2PaperOrdinaryFullFiberIndices
      complete.selectedFine.family coarse 0
  let sourceFiber :=
    wz2PaperOrdinaryFullFiberIndices
      fine actualScale.coarse parent
  have targetFull : targetFiber = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro index
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    exact
      (pureWZ2_singletonComplete_tube_subset_parent
        actualScale.cover actualScale.rho_pos.le parent index).trans
        (sameAxisTube_carrier_mono
          actualLeCoarser (actualScale.coarse.tube parent))
  let targetToSource :
      {target : Fin complete.selectedFine.family.card //
        target ∈ targetFiber} →
        {source : Fin fine.card // source ∈ sourceFiber} :=
    fun target =>
      ⟨complete.selectedFine.embedding target.1, by
        dsimp only [sourceFiber]
        rw [← indicesEq]
        exact complete.selectedFine_embedding_mem target.1⟩
  have targetToSourceInjective :
      Function.Injective targetToSource := by
    intro first second equality
    apply Subtype.ext
    apply complete.selectedFine.embedding.injective
    exact
      congrArg
        (fun source :
          {source : Fin fine.card // source ∈ sourceFiber} =>
            source.1)
        equality
  have targetToSourceSurjective :
      Function.Surjective targetToSource := by
    intro source
    have sourceSelected :
        source.1 ∈ complete.selectedFineIndices := by
      rw [indicesEq]
      exact source.2
    rcases
        complete.selectedFine_ambient_surjective
          source.1 sourceSelected
      with ⟨selectedSource, selectedSourceEq⟩
    have selectedTarget : selectedSource ∈ targetFiber := by
      rw [targetFull]
      simp
    refine ⟨⟨selectedSource, selectedTarget⟩, ?_⟩
    apply Subtype.ext
    exact selectedSourceEq
  let subtypeEquiv :
      {target : Fin complete.selectedFine.family.card //
        target ∈ targetFiber} ≃
        {source : Fin fine.card // source ∈ sourceFiber} :=
    Equiv.ofBijective targetToSource
      ⟨targetToSourceInjective, targetToSourceSurjective⟩
  let targetFiberEquiv :=
    wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := complete.selectedFine.family)
      (coarse := coarse) 0
  let sourceFiberEquiv :=
    wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := fine) (coarse := actualScale.coarse) parent
  let indexEquiv :
      Fin targetBody.card ≃ Fin sourceBody.card :=
    (targetFiberEquiv.trans subtypeEquiv).trans
      sourceFiberEquiv.symm
  have indexValue :
      ∀ targetIndex,
        complete.selectedFine.embedding
            ((wz2PaperOrdinaryFullFiberIndexEquiv
              (fine := complete.selectedFine.family)
              (coarse := coarse) 0) targetIndex).1 =
          ((wz2PaperOrdinaryFullFiberIndexEquiv
            (fine := fine) (coarse := actualScale.coarse)
            parent) (indexEquiv targetIndex)).1 := by
    intro targetIndex
    let targetSource := targetFiberEquiv targetIndex
    have sourceRoundTrip :=
      sourceFiberEquiv.apply_symm_apply (subtypeEquiv targetSource)
    change
      complete.selectedFine.embedding targetSource.1 =
        (sourceFiberEquiv (sourceFiberEquiv.symm
          (subtypeEquiv targetSource))).1
    rw [sourceRoundTrip]
    rfl
  have transported :
      WZ2PaperBodyConvexWolffBound targetBody
        (ENNReal.ofReal (81 * (coarser / actual) ^ 2) * actualC) := by
    apply
      wz2PaperBodyConvexWolffBound_of_sameAxisJohnTransport
        actualScale.rho_pos coarserPos actualLeCoarser coarserLeOne
        actualJohn.normalization coarserJohn indexEquiv
        (fun index =>
          (fine.tube
            ((wz2PaperOrdinaryFullFiberIndexEquiv
              (fine := fine) (coarse := actualScale.coarse)
              parent) (indexEquiv index)).1).carrier)
        (fun index =>
          (complete.selectedFine.family.tube
            ((wz2PaperOrdinaryFullFiberIndexEquiv
              (fine := complete.selectedFine.family)
              (coarse := coarse) 0) index).1).carrier)
    · intro index
      rfl
    · intro index
      rfl
    · intro index
      rw [complete.selectedFine.tube_eq, indexValue index]
    · exact actualJohn.convex_wolff
  have targetFiberCWA :
      WZ2PaperBodyConvexWolffBound targetBody outputC :=
    fun convexSet convex =>
      (transported convexSet convex).trans <| by
        gcongr
  exact
    pureWZ2_completeFiber_coarserScale_of_fiberCWA
      actualScale parent actualLeCoarser coarserPos outputOne
      targetFiberCWA

end Kakeya.Assouad

end
