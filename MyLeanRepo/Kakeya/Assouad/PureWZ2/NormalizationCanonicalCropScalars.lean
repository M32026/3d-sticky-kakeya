import MyLeanRepo.Kakeya.Assouad.PureWZ2.ExtremalSpatialCellLocalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationLocalizedPureProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BodyCWAFiberwiseAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ScaleChoice
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnCWATransport
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingJacobian
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Streamlined.Targets.StickyImpliesGeneral

/-!
# Canonical crop scalars after rigid normalization

This module isolates the quantitative content of the canonical dense crop
from the rigid-frame and all-scale-CWA transport.

The existing universal scalar producer quantifies over every structural
normalization output.  Spatial localization alone therefore cannot prove it:
it controls only the structural output built from that localization.  The
interface below records the three non-formal quantitative comparisons that
are actually needed:

* comparison of the cropped paper-body mass with the localized ordinary-body
  mass;
* retention of ordinary shaded mass by the canonical dense crop; and
* expansion of the canonical cropped union relative to the framed ordinary
  union.

The two remaining fields are scalar absorptions.  From these inputs, density
and the volume upper bound are derived rather than postulated.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem tubeShading_union_measurable
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading family) :
    MeasurableSet shading.union := by
  have unionEq :
      shading.union =
        ⋃ index : Fin family.card, shading.carrier index := by
    ext point
    constructor
    · rintro ⟨index, pointMem⟩
      exact Set.mem_iUnion.mpr ⟨index, pointMem⟩
    · intro pointMem
      rcases Set.mem_iUnion.mp pointMem with ⟨index, indexMem⟩
      exact ⟨index, indexMem⟩
  rw [unionEq]
  exact MeasurableSet.iUnion shading.measurable_carrier

private theorem canonicalCrop_realRpowENN_add
    {delta first second : ℝ}
    (deltaPos : 0 < delta) :
    Kakeya.realRpowENN delta (first + second) =
      Kakeya.realRpowENN delta first *
        Kakeya.realRpowENN delta second := by
  simp only [Kakeya.realRpowENN]
  have powerIdentity :
      Real.rpow delta (first + second) =
        Real.rpow delta first * Real.rpow delta second :=
    Real.rpow_add deltaPos first second
  rw [powerIdentity]
  exact ENNReal.ofReal_mul (Real.rpow_nonneg deltaPos.le first)

/--
Quantitative bounds on one canonical dense crop.

The factors are exposed separately so that geometric crop estimates and
small-scale power absorption can be proved independently.
-/
structure PureWZ2CanonicalCropQuantitativeBounds
    {sigma sourceLoss inputLoss outputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    (data :
      PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData
        (outputLoss := outputLoss) source localized 0) where
  bodyFactor : ENNReal
  cropMassFactor : ENNReal
  volumeFactor : ENNReal
  paper_body_mass_upper :
    (wz1PaperBodyFamily data.croppedFamily).mass ≤
      bodyFactor * localized.family.toBodyFamily.mass
  crop_mass_retention :
    cropMassFactor * data.ordinaryRefined.mass ≤
      data.canonicalCroppedShading.mass
  density_absorption :
    Kakeya.realRpowENN delta (outputLoss - inputLoss) *
        bodyFactor ≤
      cropMassFactor
  union_volume_expansion :
    volume data.canonicalCroppedShading.union ≤
      volumeFactor *
        volume (data.frame '' data.ordinaryRefined.union)
  volume_absorption :
    volumeFactor *
        Kakeya.realRpowENN delta (sigma - inputLoss) ≤
      Kakeya.realRpowENN delta (sigma - outputLoss)

namespace PureWZ2CanonicalCropQuantitativeBounds

variable
    {sigma sourceLoss inputLoss outputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {data :
      PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData
        (outputLoss := outputLoss) source localized 0}

/--
The quantitative crop bounds imply the two canonical scalar fields.
-/
theorem toCanonicalScalars
    (bounds : PureWZ2CanonicalCropQuantitativeBounds data) :
    PureWZ2CroppedCriticalNormalizationCanonicalScalars data := by
  have retainedMass :
      localized.shading.mass ≤ data.ordinaryRefined.mass := by
    simpa [wz2PaperPureRefinementFraction] using data.retained_mass
  have ordinaryDense :
      Kakeya.realRpowENN delta inputLoss *
          localized.family.toBodyFamily.mass ≤
        data.ordinaryRefined.mass :=
    localized.extremal.dense.trans retainedMass
  have dense :
      data.canonicalCroppedShading.IsLambdaDense
        (Kakeya.realRpowENN delta outputLoss) := by
    change
      Kakeya.realRpowENN delta outputLoss *
          (wz1PaperBodyFamily data.croppedFamily).mass ≤
        data.canonicalCroppedShading.mass
    calc
      Kakeya.realRpowENN delta outputLoss *
            (wz1PaperBodyFamily data.croppedFamily).mass =
          (Kakeya.realRpowENN delta (outputLoss - inputLoss) *
              Kakeya.realRpowENN delta inputLoss) *
            (wz1PaperBodyFamily data.croppedFamily).mass := by
        rw [← canonicalCrop_realRpowENN_add
          localized.extremal.delta_pos]
        congr 2
        ring
      _ ≤
          (Kakeya.realRpowENN delta (outputLoss - inputLoss) *
              Kakeya.realRpowENN delta inputLoss) *
            (bounds.bodyFactor *
              localized.family.toBodyFamily.mass) := by
        gcongr
        exact bounds.paper_body_mass_upper
      _ =
          (Kakeya.realRpowENN delta (outputLoss - inputLoss) *
              bounds.bodyFactor) *
            (Kakeya.realRpowENN delta inputLoss *
              localized.family.toBodyFamily.mass) := by
        ring
      _ ≤ bounds.cropMassFactor * data.ordinaryRefined.mass := by
        gcongr
        exact bounds.density_absorption
      _ ≤ data.canonicalCroppedShading.mass :=
        bounds.crop_mass_retention
  have ordinaryUnionSubset :
      data.ordinaryRefined.union ⊆ localized.shading.union := by
    rintro point ⟨index, pointMem⟩
    exact
      ⟨data.selected.embedding index,
        data.ordinary_subshading index pointMem⟩
  have framedOrdinaryVolume :
      volume (data.frame '' data.ordinaryRefined.union) =
        volume data.ordinaryRefined.union :=
    Kakeya.Streamlined.AffineIsometryEquiv.volume_image
      data.frame data.ordinaryRefined.union
        (tubeShading_union_measurable data.ordinaryRefined)
  have volumeUpper :
      volume data.canonicalCroppedShading.union ≤
        Kakeya.realRpowENN delta (sigma - outputLoss) := by
    calc
      volume data.canonicalCroppedShading.union ≤
          bounds.volumeFactor *
            volume (data.frame '' data.ordinaryRefined.union) :=
        bounds.union_volume_expansion
      _ = bounds.volumeFactor *
            volume data.ordinaryRefined.union := by
        rw [framedOrdinaryVolume]
      _ ≤ bounds.volumeFactor *
            volume localized.shading.union := by
        gcongr
      _ ≤ bounds.volumeFactor *
            Kakeya.realRpowENN delta (sigma - inputLoss) := by
        gcongr
        exact localized.extremal.volume_upper
      _ ≤ Kakeya.realRpowENN delta (sigma - outputLoss) :=
        bounds.volume_absorption
  exact
    {
      dense := dense
      volume_upper := volumeUpper
    }

end PureWZ2CanonicalCropQuantitativeBounds

/--
Uniform producer of the geometric crop bounds at normalization exponent zero.
-/
def PureWZ2CanonicalCropQuantitativeBoundsProducerAtZero : Prop :=
  ∀ {sigma sourceLoss inputLoss outputLoss delta : ℝ},
    ∀ {source :
        PureWZ2ExtremalConfiguration sigma sourceLoss delta},
      ∀ {localized :
          PureWZ2ExtremalConfiguration sigma inputLoss delta},
        ∀ data :
            PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData
              (outputLoss := outputLoss) source localized 0,
          Nonempty (PureWZ2CanonicalCropQuantitativeBounds data)

/--
The geometric crop-bound producer closes the existing universal scalar
producer at exponent zero.
-/
theorem pureWZ2_canonicalScalarsProducerAtZero_of_quantitativeBounds
    (bounds :
      PureWZ2CanonicalCropQuantitativeBoundsProducerAtZero) :
    PureWZ2CroppedCriticalNormalizationCanonicalScalarsProducerAt 0 := by
  intro sigma sourceLoss inputLoss outputLoss delta
    source localized data
  rcases bounds data with ⟨certificate⟩
  exact certificate.toCanonicalScalars

/-! ## Top-level CWA directly from the pure nearby-scale API -/

private theorem pureWZ2CanonicalCrop_john_map_volume_upper
    {rho : ℝ}
    {parent : Kakeya.DeltaTube rho}
    (rhoPos : 0 < rho)
    (normalization :
      WZ2PaperAssouadUnitRescalingData parent)
    (source : Set Point3) :
    volume (normalization.map '' source) ≤
      ENNReal.ofReal (4 / rho ^ 2) * volume source := by
  have normalizationEq :
      normalization =
        WZ2PaperAssouadUnitRescalingData.ofTube parent rhoPos :=
    normalization.unique _
  subst normalization
  rw [wz2PaperAffineEquiv_volume_image_eq]
  gcongr
  change
    |LinearMap.det
      (((wz2_paper_ordinary_tube_isConvexBody
          parent rhoPos).outerJohnEllipsoidMap.symm :
        Point3 ≃ₗ[ℝ] Point3) : Point3 →ₗ[ℝ] Point3)| ≤
      4 / rho ^ 2
  rw [LinearEquiv.det_coe_symm, abs_inv]
  have determinantLower :=
    wz2Paper_outerJohn_abs_det_lower parent rhoPos
  have lowerPos : 0 < rho ^ 2 / 4 := by positivity
  have determinantPos :
      0 <
        |LinearMap.det
          ((wz2_paper_ordinary_tube_isConvexBody
            parent rhoPos).outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| :=
    lt_of_lt_of_le lowerPos determinantLower
  calc
    |LinearMap.det
        ((wz2_paper_ordinary_tube_isConvexBody
          parent rhoPos).outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)|⁻¹ ≤
        (rho ^ 2 / 4)⁻¹ :=
      (inv_le_inv₀ determinantPos lowerPos).2 determinantLower
    _ = 4 / rho ^ 2 := by
      field_simp [rhoPos.ne']

private theorem pureWZ2CanonicalCrop_pureFiberPhysicalCWA
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (rhoPos : 0 < rho)
    {sourceConstant outputConstant : ENNReal}
    (fiber :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := coarse)
        parent sourceConstant)
    (absorb :
      ENNReal.ofReal (4 / rho ^ 2) * sourceConstant ≤
        outputConstant) :
    WZ2PaperBodyConvexWolffBound
      (Kakeya.Streamlined.TubeSubfamily.fromFinset fine
        (wz2PaperOrdinaryFullFiberIndices
          fine coarse parent)).family.toBodyFamily
      outputConstant := by
  let source :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := fine) (coarse := coarse)
      parent fiber.normalization
  let selected :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset fine
      (wz2PaperOrdinaryFullFiberIndices
        fine coarse parent)
  let target := selected.family.toBodyFamily
  have cardEq : target.card = source.card := by
    rfl
  let indexEquiv : Fin target.card ≃ Fin source.card :=
    Fin.castOrderIso cardEq
  have carrierContainment :
      ∀ targetIndex,
        fiber.normalization.map.symm ''
            (source.body (indexEquiv targetIndex)).carrier ⊆
          (target.body targetIndex).carrier := by
    intro targetIndex point pointMem
    rcases pointMem with ⟨johnPoint, johnPointMem, rfl⟩
    change
      fiber.normalization.map.symm johnPoint ∈
        (selected.family.tube targetIndex).carrier
    change
      johnPoint ∈ fiber.normalization.map ''
        (fine.tube
          ((wz2PaperOrdinaryFullFiberIndexEquiv parent)
            (indexEquiv targetIndex))).carrier at johnPointMem
    rcases johnPointMem with
      ⟨physicalPoint, physicalPointMem, rfl⟩
    have indexEq :
        ((wz2PaperOrdinaryFullFiberIndexEquiv parent)
          (indexEquiv targetIndex)).1 =
          selected.embedding targetIndex := by
      rfl
    rw [indexEq] at physicalPointMem
    simp only [fiber.normalization.map.symm_apply_apply]
    rw [selected.tube_eq]
    exact physicalPointMem
  have raw :
      WZ2PaperBodyConvexWolffBound target
        (ENNReal.ofReal (4 / rho ^ 2) * sourceConstant) := by
    apply
      wz2PaperBodyConvexWolffBound_of_affineTransport
        fiber.normalization.map.symm
        indexEquiv carrierContainment
    · intro targetSet
      exact
        pureWZ2CanonicalCrop_john_map_volume_upper
          rhoPos fiber.normalization targetSet
    · exact fiber.convex_wolff
  intro convexSet convex
  exact (raw convexSet convex).trans (by gcongr)

private theorem pureWZ2CanonicalCrop_pureFiberParentCWA
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (rhoPos : 0 < rho)
    (parent : Fin coarse.card)
    {sourceConstant outputConstant : ENNReal}
    (fiber :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := coarse)
        parent sourceConstant)
    (absorb :
      ENNReal.ofReal (4 / rho ^ 2) * sourceConstant ≤
        outputConstant) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperBodyParentFiber
        fine.toBodyFamily cover.parent parent)
      outputConstant := by
  let selected :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset fine
      (wz2PaperOrdinaryFullFiberIndices
        fine coarse parent)
  let source := selected.family.toBodyFamily
  let target :=
    wz2PaperBodyParentFiber
      fine.toBodyFamily cover.parent parent
  have sourceCWA :
      WZ2PaperBodyConvexWolffBound
        source outputConstant :=
    pureWZ2CanonicalCrop_pureFiberPhysicalCWA
      parent rhoPos fiber absorb
  let sourceIndices :=
    wz2PaperOrdinaryFullFiberIndices
      fine coarse parent
  let targetIndices :=
    Finset.univ.filter fun index : Fin fine.card =>
      cover.parent index = parent
  have indicesEq : sourceIndices = targetIndices := by
    ext index
    change
      index ∈
          wz2PaperOrdinaryFullFiberIndices
            fine coarse parent ↔
        index ∈ Finset.univ.filter fun source =>
          cover.parent source = parent
    simpa using
      cover.mem_fullFiber_iff_parent_eq
        rhoPos.le parent index
  let fiberEquiv : sourceIndices ≃ targetIndices :=
    {
      toFun := fun sourceIndex =>
        ⟨sourceIndex.1, by
          rw [← indicesEq]
          exact sourceIndex.2⟩
      invFun := fun targetIndex =>
        ⟨targetIndex.1, by
          rw [indicesEq]
          exact targetIndex.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }
  let indexEquiv : Fin target.card ≃ Fin source.card :=
    (targetIndices.orderIsoOfFin rfl).toEquiv |>.trans
      (fiberEquiv.symm.trans
        (sourceIndices.orderIsoOfFin rfl).symm.toEquiv)
  have transported :
      WZ2PaperBodyConvexWolffBound
        target (1 * outputConstant) := by
    apply
      wz2PaperBodyConvexWolffBound_of_affineTransport
        (AffineEquiv.refl ℝ Point3) indexEquiv
    · intro targetIndex point pointMem
      rcases pointMem with
        ⟨sourcePoint, sourcePointMem, rfl⟩
      simp only [AffineEquiv.refl_apply]
      change
        sourcePoint ∈
          (fine.tube
            (targetIndices.orderEmbOfFin
              rfl targetIndex)).carrier
      change
        sourcePoint ∈
          (source.body
            (indexEquiv targetIndex)).carrier at sourcePointMem
      have ambientEq :
          selected.embedding (indexEquiv targetIndex) =
            targetIndices.orderEmbOfFin rfl targetIndex := by
        let targetMember : targetIndices :=
          targetIndices.orderIsoOfFin rfl targetIndex
        let sourceMember : sourceIndices :=
          fiberEquiv.symm targetMember
        have sourceRoundTrip :=
          (sourceIndices.orderIsoOfFin rfl)
            |>.apply_symm_apply sourceMember
        change
          ((sourceIndices.orderIsoOfFin rfl)
              ((sourceIndices.orderIsoOfFin rfl).symm
                sourceMember)).1 =
            targetMember.1
        rw [sourceRoundTrip]
        rfl
      change
        sourcePoint ∈
          (selected.family.tube
            (indexEquiv targetIndex)).carrier at sourcePointMem
      rw [selected.tube_eq, ambientEq] at sourcePointMem
      exact sourcePointMem
    · intro targetSet
      simp
    · exact sourceCWA
  simpa using transported

/--
Direct recovery of ordinary top-level CWA from the pure nearby-scale API.

The requested scale is `delta ^ inputLoss`, not `1`.  The nearby factor then
forces the actual scale below `1`, exactly as in
`pure_wz2_scale_and_nearby_generalized`.
-/
theorem pureWZ2_pureNearby_to_ordinaryTopCWA
    {delta inputLoss outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (inputLossPos : 0 < inputLoss)
    (inputLossLeOne : inputLoss ≤ 1)
    (deltaLeOne : delta ≤ 1)
    (familyNonempty : family.Nonempty)
    (pureCWA :
      WZ2PaperPureCWAAtNearbyScales family
        (Kakeya.realRpowENN delta (-inputLoss)))
    (absorb :
      ∀ rho : ℝ,
        0 < rho →
        delta ≤ rho →
        rho ≤ 1 →
        Real.rpow delta inputLoss ≤ rho →
        ENNReal.ofReal (4 / rho ^ 2) *
            Kakeya.realRpowENN delta (-inputLoss) ≤
          Kakeya.realRpowENN delta (-outputLoss)) :
    WZ2PaperBodyConvexWolffBound family.toBodyFamily
      (Kakeya.realRpowENN delta (-outputLoss)) := by
  have deltaPos : 0 < delta := pureCWA.1
  rcases
      pure_wz2_scale_and_nearby_generalized
        deltaPos deltaLeOne
        inputLossPos le_rfl inputLossLeOne
        rfl pureCWA with
    ⟨requested, nearby, _rhoLtOne, rhoLeOne,
      _deltaDivRho, requestedRho, rhoPos⟩
  have deltaRho : delta ≤ nearby.rho :=
    requested.2.1.trans nearby.requested_le
  have coarseCardPos :
      0 < nearby.scaleData.coarse.card := by
    let source : Fin family.card :=
      ⟨0, familyNonempty⟩
    rcases nearby.scaleData.cover.covers source with
      ⟨parent, _sourceMem⟩
    exact Nat.zero_lt_of_lt parent.2
  apply
    wz2PaperBodyConvexWolffBound_of_parent_fibers
      (parentCount := nearby.scaleData.coarse.card)
      coarseCardPos nearby.scaleData.cover.parent
  intro parent
  let fiber :=
    Classical.choice
      (nearby.scaleData.rescaledFiber parent)
  exact
    pureWZ2CanonicalCrop_pureFiberParentCWA
      nearby.scaleData.cover rhoPos parent fiber
      (absorb nearby.rho rhoPos deltaRho rhoLeOne requestedRho)

/--
The fixed John pullback loss is absorbed once
`3 * inputLoss < outputLoss`.
-/
theorem exists_pureWZ2_pureNearby_topCWA_absorption
    {inputLoss outputLoss : ℝ}
    (gap : 3 * inputLoss < outputLoss) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ delta rho : ℝ,
        0 < delta →
        delta ≤ delta₀ →
        0 < rho →
        delta ≤ rho →
        rho ≤ 1 →
        Real.rpow delta inputLoss ≤ rho →
          ENNReal.ofReal (4 / rho ^ 2) *
              Kakeya.realRpowENN delta (-inputLoss) ≤
            Kakeya.realRpowENN delta (-outputLoss) := by
  have gapPos : 0 < outputLoss - 3 * inputLoss := by
    linarith
  rcases
      exists_delta_realRpowENN_bound
        (4 : ENNReal) (by norm_num) gapPos with
    ⟨delta₀, delta₀Pos, delta₀LeOne, constantAbsorption⟩
  refine
    ⟨delta₀, delta₀Pos, delta₀LeOne, ?_⟩
  intro delta rho deltaPos deltaLe rhoPos
    _deltaRho _rhoLeOne requestedRho
  have inverseRho :
      ENNReal.ofReal (1 / rho ^ 2) ≤
        Kakeya.realRpowENN delta (-2 * inputLoss) := by
    have requestedENN :
        Kakeya.realRpowENN delta inputLoss ≤
          ENNReal.ofReal rho :=
      ENNReal.ofReal_mono requestedRho
    have inverseENN :
        (ENNReal.ofReal rho)⁻¹ ≤
          (Kakeya.realRpowENN delta inputLoss)⁻¹ :=
      ENNReal.inv_le_inv' requestedENN
    have inverseSquared :
        ((ENNReal.ofReal rho)⁻¹) ^ 2 ≤
          ((Kakeya.realRpowENN delta inputLoss)⁻¹) ^ 2 :=
      pow_le_pow_left' inverseENN 2
    calc
      ENNReal.ofReal (1 / rho ^ 2) =
          ((ENNReal.ofReal rho)⁻¹) ^ 2 := by
        rw [show 1 / rho ^ 2 = (rho⁻¹) ^ 2 by ring,
          ENNReal.ofReal_pow (inv_nonneg.mpr rhoPos.le),
          ENNReal.ofReal_inv_of_pos rhoPos]
      _ ≤
          ((Kakeya.realRpowENN delta inputLoss)⁻¹) ^ 2 :=
        inverseSquared
      _ =
          Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta (-inputLoss) := by
        rw [pure_wz2_realRpowENN_inv deltaPos]
        ring
      _ =
          Kakeya.realRpowENN delta (-2 * inputLoss) := by
        rw [← Kakeya.Streamlined.realRpowENN_add deltaPos]
        congr 1
        ring
  have fourOverRho :
      ENNReal.ofReal (4 / rho ^ 2) ≤
        (4 : ENNReal) *
          Kakeya.realRpowENN delta (-2 * inputLoss) := by
    rw [show 4 / rho ^ 2 = 4 * (1 / rho ^ 2) by ring,
      ENNReal.ofReal_mul (by norm_num)]
    norm_num
    gcongr
    simpa [one_div] using inverseRho
  have constantBound :
      (4 : ENNReal) ≤
        Kakeya.realRpowENN delta
          (-(outputLoss - 3 * inputLoss)) :=
    constantAbsorption delta deltaPos deltaLe
  calc
    ENNReal.ofReal (4 / rho ^ 2) *
          Kakeya.realRpowENN delta (-inputLoss) ≤
        ((4 : ENNReal) *
          Kakeya.realRpowENN delta (-2 * inputLoss)) *
          Kakeya.realRpowENN delta (-inputLoss) := by
      gcongr
    _ =
        (4 : ENNReal) *
          Kakeya.realRpowENN delta (-3 * inputLoss) := by
      calc
        (4 : ENNReal) *
              Kakeya.realRpowENN delta (-2 * inputLoss) *
              Kakeya.realRpowENN delta (-inputLoss) =
            4 *
              (Kakeya.realRpowENN delta (-2 * inputLoss) *
                Kakeya.realRpowENN delta (-inputLoss)) := by
          ring
        _ =
            4 *
              Kakeya.realRpowENN delta
                ((-2 * inputLoss) + (-inputLoss)) := by
          rw [Kakeya.Streamlined.realRpowENN_add deltaPos]
        _ =
            4 *
              Kakeya.realRpowENN delta (-3 * inputLoss) := by
          congr 2
          ring
    _ ≤
        Kakeya.realRpowENN delta
            (-(outputLoss - 3 * inputLoss)) *
          Kakeya.realRpowENN delta (-3 * inputLoss) := by
      gcongr
    _ = Kakeya.realRpowENN delta (-outputLoss) := by
      rw [← Kakeya.Streamlined.realRpowENN_add deltaPos]
      congr 1
      ring

/-! ## The common canonical rigid frame -/

/-- The translation-to-center followed by the Householder rotation to `e₃`. -/
noncomputable def pureWZ2CanonicalRigidFrame
    (center direction : Point3)
    (directionUnit : ‖direction‖ = 1) :
    Point3 ≃ᵃⁱ[ℝ] Point3 :=
  let rotation := householderToE3 direction directionUnit
  AffineIsometryEquiv.mk'
    (fun point : Point3 => rotation (point - center))
    rotation center (by simp)

@[simp]
theorem pureWZ2CanonicalRigidFrame_center
    (center direction : Point3)
    (directionUnit : ‖direction‖ = 1) :
    pureWZ2CanonicalRigidFrame
      center direction directionUnit center = 0 := by
  simp [pureWZ2CanonicalRigidFrame]

@[simp]
theorem pureWZ2CanonicalRigidFrame_direction
    (center direction : Point3)
    (directionUnit : ‖direction‖ = 1) :
    (pureWZ2CanonicalRigidFrame
      center direction directionUnit).linearIsometryEquiv direction =
        e3 := by
  exact householderToE3_sends_d_to_e3 direction directionUnit

/-- Transport one ordinary tube through the common rigid frame. -/
noncomputable def pureWZ2RigidImageTube
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta) :
    Kakeya.DeltaTube delta where
  base := frame tube.base
  direction := frame.linearIsometryEquiv tube.direction
  direction_unit := by
    rw [frame.linearIsometryEquiv.norm_map, tube.direction_unit]

private theorem pureWZ2RigidFrame_map_add
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (center vector : Point3) :
    frame (center + vector) =
      frame center + frame.linearIsometryEquiv vector := by
  have mapped := frame.map_vadd center vector
  simpa [vadd_eq_add, add_comm] using mapped

/-- The transported tube carrier is exactly the common rigid image. -/
theorem pureWZ2RigidImageTube_carrier
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta) :
    (pureWZ2RigidImageTube frame tube).carrier =
      frame '' tube.carrier := by
  have segmentImage :
      frame '' Kakeya.unitSegment tube.base tube.direction =
        Kakeya.unitSegment
          (frame tube.base)
          (frame.linearIsometryEquiv tube.direction) := by
    ext point
    simp only [Kakeya.unitSegment, Set.mem_image]
    constructor
    · rintro ⟨sourcePoint, ⟨parameter, parameterMem, rfl⟩, rfl⟩
      refine ⟨parameter, parameterMem, ?_⟩
      rw [pureWZ2RigidFrame_map_add,
        frame.linearIsometryEquiv.map_smul]
    · rintro ⟨parameter, parameterMem, rfl⟩
      refine
        ⟨tube.base + parameter • tube.direction,
          ⟨parameter, parameterMem, rfl⟩, ?_⟩
      rw [pureWZ2RigidFrame_map_add,
        frame.linearIsometryEquiv.map_smul]
  have thickeningImage :
      frame '' Metric.cthickening delta
          (Kakeya.unitSegment tube.base tube.direction) =
        Metric.cthickening delta
          (frame '' Kakeya.unitSegment
            tube.base tube.direction) := by
    simpa using
      Kakeya.Streamlined.IsometryEquiv.cthickening_image
        frame.toIsometryEquiv delta
          (Kakeya.unitSegment tube.base tube.direction)
  rw [Kakeya.DeltaTube.carrier,
    Kakeya.DeltaTube.carrier,
    thickeningImage, segmentImage]
  rfl

/-- Transport an indexed family through one common rigid frame. -/
noncomputable def pureWZ2RigidImageFamily
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta) :
    Kakeya.Streamlined.TubeFamily delta where
  card := family.card
  tube index := pureWZ2RigidImageTube frame (family.tube index)

@[simp]
theorem pureWZ2RigidImageFamily_card
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta) :
    (pureWZ2RigidImageFamily frame family).card = family.card :=
  rfl

theorem pureWZ2RigidImageFamily_carrier
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (index : Fin family.card) :
    ((pureWZ2RigidImageFamily frame family).tube index).carrier =
      frame '' (family.tube index).carrier :=
  pureWZ2RigidImageTube_carrier frame (family.tube index)

private theorem pureWZ2AffineIsometry_volume_image
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (source : Set Point3) :
    volume (frame '' source) = volume source := by
  let linear : Point3 ≃ₗᵢ[ℝ] Point3 :=
    frame.linearIsometryEquiv
  let linearEquiv : Point3 ≃ Point3 := linear.toEquiv
  let translation : Point3 := frame 0
  let translationEquiv : Point3 ≃ Point3 :=
    Equiv.addLeft translation
  have decomposition :
      frame '' source =
        translationEquiv '' (linearEquiv '' source) := by
    ext point
    simp only [Set.mem_image]
    constructor
    · rintro ⟨sourcePoint, sourcePointMem, rfl⟩
      have mapEq :
          frame sourcePoint =
            translation + linear sourcePoint := by
        have mapped :=
          pureWZ2RigidFrame_map_add
            frame 0 sourcePoint
        simpa [translation, linear, add_comm] using mapped
      exact
        ⟨linear sourcePoint,
          ⟨sourcePoint, sourcePointMem, rfl⟩,
          mapEq.symm⟩
    · rintro ⟨linearPoint, ⟨sourcePoint, sourcePointMem, rfl⟩, rfl⟩
      have mapEq :
          frame sourcePoint =
            translation + linear sourcePoint := by
        have mapped :=
          pureWZ2RigidFrame_map_add
            frame 0 sourcePoint
        simpa [translation, linear, add_comm] using mapped
      exact ⟨sourcePoint, sourcePointMem, mapEq⟩
  rw [decomposition]
  have translationPreserving :
      MeasurePreserving translationEquiv volume volume :=
    measurePreserving_add_left volume translation
  have translationSymmPreserving :
      MeasurePreserving translationEquiv.symm volume volume := by
    simpa [translationEquiv] using
      measurePreserving_add_left volume (-translation)
  have linearPreserving :
      MeasurePreserving linearEquiv volume volume :=
    LinearIsometryEquiv.measurePreserving linear
  have linearSymmPreserving :
      MeasurePreserving linearEquiv.symm volume volume :=
    LinearIsometryEquiv.measurePreserving linear.symm
  have equivVolumeImage
      {equivalence : Point3 ≃ Point3}
      (preserving :
        MeasurePreserving equivalence volume volume)
      (symmPreserving :
        MeasurePreserving equivalence.symm volume volume)
      (set : Set Point3) :
      volume (equivalence '' set) = volume set := by
    apply le_antisymm
    · have bound :=
        symmPreserving.measure_preimage_le set
      have preimageEq :
          equivalence.symm ⁻¹' set =
            equivalence '' set := by
        ext point
        constructor
        · intro pointMem
          exact
            ⟨equivalence.symm point, pointMem,
              equivalence.apply_symm_apply point⟩
        · rintro ⟨sourcePoint, sourcePointMem, rfl⟩
          simpa using sourcePointMem
      rwa [preimageEq] at bound
    · have bound :=
        preserving.measure_preimage_le
          (equivalence '' set)
      have preimageEq :
          equivalence ⁻¹' (equivalence '' set) = set := by
        ext point
        simp
      rwa [preimageEq] at bound
  rw [equivVolumeImage
    translationPreserving translationSymmPreserving]
  exact
    equivVolumeImage
      linearPreserving linearSymmPreserving source

/-- Ordinary Body CWA is invariant under the common rigid frame. -/
theorem pureWZ2RigidImageFamily_bodyCWA
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    {C : ENNReal}
    (sourceCWA :
      WZ2PaperBodyConvexWolffBound family.toBodyFamily C) :
    WZ2PaperBodyConvexWolffBound
      (pureWZ2RigidImageFamily frame family).toBodyFamily C := by
  have transported :
      WZ2PaperBodyConvexWolffBound
        (pureWZ2RigidImageFamily frame family).toBodyFamily
        (1 * C) := by
    apply
      wz2PaperBodyConvexWolffBound_of_affineTransport
        (source := family.toBodyFamily)
        (target :=
          (pureWZ2RigidImageFamily frame family).toBodyFamily)
        frame.toAffineEquiv (Equiv.refl _)
    · intro index
      change
        frame '' (family.tube index).carrier ⊆
          ((pureWZ2RigidImageFamily
            frame family).tube index).carrier
      rw [pureWZ2RigidImageFamily_carrier]
    · intro targetSet
      have volumeEq :
          volume (frame.symm '' targetSet) =
            volume targetSet :=
        pureWZ2AffineIsometry_volume_image
          frame.symm targetSet
      simpa using volumeEq.le
    · exact sourceCWA
  simpa using transported

/--
Localization provenance together with the canonical translation-rotation
frame.

`pure_cwa_transport` is the thin affine Definition-2.12 transport boundary.
`ordinary_to_paper_cwa` is the thin top-level convention-change boundary;
the ordinary top-level CWA itself is derived above from the pure nearby API.
The axial-window field remains an explicit geometric certificate: it is not
deduced from bounded support or cell containment.
-/
structure PureWZ2LocalizedCanonicalRigidFrameData
    {sigma sourceLoss inputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    (localization :
      PureWZ2SameDeltaSpatialCellLocalizationData
        source localized) where
  referenceDirection : Point3
  referenceDirection_unit : ‖referenceDirection‖ = 1
  line_class :
    WZ1PaperIsLineClass
      (pureWZ2RigidImageFamily
        (pureWZ2CanonicalRigidFrame
          localization.center referenceDirection
          referenceDirection_unit)
        localized.family)
  pure_cwa_transport :
    ∀ {C : ENNReal},
      WZ2PaperPureCWAAtNearbyScales localized.family C →
        WZ2PaperPureCWAAtNearbyScales
          (pureWZ2RigidImageFamily
            (pureWZ2CanonicalRigidFrame
              localization.center referenceDirection
              referenceDirection_unit)
            localized.family)
          C
  top_level_transport_factor : ENNReal
  top_level_transport_factor_ne_top :
    top_level_transport_factor ≠ ⊤
  ordinary_to_paper_cwa :
    ∀ {C : ENNReal},
      WZ2PaperBodyConvexWolffBound
          (pureWZ2RigidImageFamily
            (pureWZ2CanonicalRigidFrame
              localization.center referenceDirection
              referenceDirection_unit)
            localized.family).toBodyFamily
          C →
        WZ2PaperConvexWolffBound
          (pureWZ2RigidImageFamily
            (pureWZ2CanonicalRigidFrame
              localization.center referenceDirection
              referenceDirection_unit)
            localized.family)
          (top_level_transport_factor * C)
  ordinary_cell_containment :
    ∀ index (cell : ℤ × ℤ × ℤ),
      ((pureWZ2CanonicalRigidFrame
              localization.center referenceDirection
              referenceDirection_unit ''
            localized.shading.carrier index) ∩
          wz1PaperGridCube delta cell).Nonempty →
        wz1PaperGridCube delta cell ⊆
          wz1PaperTubeCarrier
            ((pureWZ2RigidImageFamily
              (pureWZ2CanonicalRigidFrame
                localization.center referenceDirection
                referenceDirection_unit)
              localized.family).tube index)
  ordinary_axial_window :
    ∀ index point,
      point ∈
          pureWZ2CanonicalRigidFrame
              localization.center referenceDirection
              referenceDirection_unit ''
            localized.shading.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8
  ordinary_bounded_base :
    HasBoundedBase
      (pureWZ2RigidImageFamily
        (pureWZ2CanonicalRigidFrame
          localization.center referenceDirection
          referenceDirection_unit)
        localized.family)
      4

namespace PureWZ2LocalizedCanonicalRigidFrameData

variable
    {sigma sourceLoss inputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {localization :
      PureWZ2SameDeltaSpatialCellLocalizationData
        source localized}
    (rigid :
      PureWZ2LocalizedCanonicalRigidFrameData localization)

/-- The one common frame selected by the wrapper. -/
noncomputable def frame : Point3 ≃ᵃⁱ[ℝ] Point3 :=
  pureWZ2CanonicalRigidFrame
    localization.center rigid.referenceDirection
      rigid.referenceDirection_unit

/-- The corresponding canonical rigid-image family. -/
noncomputable def croppedFamily :
    Kakeya.Streamlined.TubeFamily delta :=
  pureWZ2RigidImageFamily rigid.frame localized.family

@[simp]
theorem frame_center :
    rigid.frame localization.center = 0 := by
  simp [frame]

@[simp]
theorem frame_referenceDirection :
    rigid.frame.linearIsometryEquiv
        rigid.referenceDirection = e3 := by
  simp [frame]

theorem cropped_tube_eq
    (index : Fin localized.family.card) :
    rigid.croppedFamily.tube index =
      pureWZ2RigidImageTube
        rigid.frame (localized.family.tube index) :=
  rfl

theorem cropped_carrier_image_eq
    (index : Fin localized.family.card) :
    (rigid.croppedFamily.tube index).carrier =
      rigid.frame '' (localized.family.tube index).carrier :=
  pureWZ2RigidImageFamily_carrier
    rigid.frame localized.family index

/--
The canonical framed base is bounded by `3`, hence by the requested public
radius `5`.  This is the PostDeletion provenance missing from the older
structural normalization record.
-/
theorem cropped_base_norm_le_five
    (index : Fin localized.family.card) :
    ‖(rigid.croppedFamily.tube index).base‖ ≤ 5 := by
  calc
    ‖(rigid.croppedFamily.tube index).base‖ =
        dist
          (rigid.frame (localized.family.tube index).base)
          (rigid.frame localization.center) := by
      rw [rigid.frame_center, dist_zero_right]
      rfl
    _ =
        dist (localized.family.tube index).base
          localization.center :=
      rigid.frame.dist_map _ _
    _ ≤ 3 := localization.family_bases_local index
    _ ≤ 5 := by norm_num

/--
Assemble the existing source-derived structural record from the canonical
rigid frame.

The ordinary selection is the whole localized family.  Pure nearby CWA is
weakened to the output loss before the common rigid transport.
-/
noncomputable def toSourceDerivedStructuralData
    {outputLoss : ℝ}
    (inputLossLeHalf : inputLoss ≤ outputLoss / 2)
    (inputLossLe : inputLoss ≤ outputLoss)
    (perTubeDensity :
      ∀ index,
        (Kakeya.realRpowENN delta inputLoss / 2) *
              volume (localized.family.tube index).carrier ≤
          volume (localized.shading.carrier index))
    (topLevelCWA :
      WZ2PaperConvexWolffBound rigid.croppedFamily
        (Kakeya.realRpowENN delta (-outputLoss))) :
    PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData
      (outputLoss := outputLoss) source localized 0 := by
  let selected :
      Kakeya.Streamlined.TubeSubfamily localized.family :=
    {
      family := localized.family
      embedding := Equiv.toEmbedding (Equiv.refl _)
      tube_eq := fun _ => rfl
    }
  refine
    {
      input_loss_le_half := inputLossLeHalf
      selected := selected
      selected_nonempty := ?_
      ordinaryRefined := localized.shading
      ordinary_subshading := ?_
      retained_mass := ?_
      frame := rigid.frame
      croppedFamily := rigid.croppedFamily
      indexEquiv := Equiv.refl _
      ordinary_carrier_image_eq := ?_
      ordinary_per_tube := by
        intro index
        simpa [selected] using perTubeDensity index
      ordinary_axial_window := by
        intro index point pointMem
        simpa [selected, frame] using
          rigid.ordinary_axial_window index point pointMem
      line_class := ?_
      cropped_pure_cwa := ?_
      cropped_top_level_cwa := topLevelCWA
      ordinary_cell_containment := rigid.ordinary_cell_containment
      ordinary_bounded_base := rigid.ordinary_bounded_base
    }
  · simpa [selected] using localized.extremal.nonempty
  · intro index
    simp [selected]
  · simp [wz2PaperPureRefinementFraction]
  · intro index
    change
      (rigid.croppedFamily.tube index).carrier =
        rigid.frame '' (localized.family.tube index).carrier
    exact rigid.cropped_carrier_image_eq index
  · simpa [croppedFamily, frame] using rigid.line_class
  · apply rigid.pure_cwa_transport
    exact
      localized.extremal.cwa_nearby_scales.mono_loss
        localized.extremal.delta_pos
        localized.extremal.delta_le_one
        inputLossLe

@[simp]
theorem toSourceDerivedStructuralData_croppedFamily
    {outputLoss : ℝ}
    (inputLossLeHalf : inputLoss ≤ outputLoss / 2)
    (inputLossLe : inputLoss ≤ outputLoss)
    (perTubeDensity :
      ∀ index,
        (Kakeya.realRpowENN delta inputLoss / 2) *
              volume (localized.family.tube index).carrier ≤
          volume (localized.shading.carrier index))
    (topLevelCWA :
      WZ2PaperConvexWolffBound rigid.croppedFamily
        (Kakeya.realRpowENN delta (-outputLoss))) :
    (rigid.toSourceDerivedStructuralData
      inputLossLeHalf inputLossLe perTubeDensity topLevelCWA).croppedFamily =
        rigid.croppedFamily :=
  rfl

/--
The source-derived structural record retains the radius-five framed-base
bound needed by the PostDeletion witness.
-/
theorem toSourceDerivedStructuralData_cropped_base_norm_le_five
    {outputLoss : ℝ}
    (inputLossLeHalf : inputLoss ≤ outputLoss / 2)
    (inputLossLe : inputLoss ≤ outputLoss)
    (perTubeDensity :
      ∀ index,
        (Kakeya.realRpowENN delta inputLoss / 2) *
              volume (localized.family.tube index).carrier ≤
          volume (localized.shading.carrier index))
    (topLevelCWA :
      WZ2PaperConvexWolffBound rigid.croppedFamily
        (Kakeya.realRpowENN delta (-outputLoss)))
    (index :
      Fin
        (rigid.toSourceDerivedStructuralData
          inputLossLeHalf inputLossLe
          perTubeDensity topLevelCWA).croppedFamily.card) :
    ‖((rigid.toSourceDerivedStructuralData
        inputLossLeHalf inputLossLe
        perTubeDensity topLevelCWA).croppedFamily.tube index).base‖ ≤
      5 := by
  exact rigid.cropped_base_norm_le_five index

end PureWZ2LocalizedCanonicalRigidFrameData

/-!
The remaining conditions are concentrated in two producer interfaces.

The rigid producer owns the direction-cone/fixed-line-class theorem and the
two affine transport statements.  The crop leaf owns only quantitative
canonical-crop retention/expansion, not the desired `dense` or
`volume_upper` conclusions themselves.
-/

def PureWZ2LocalizedCanonicalRigidFrameProducer : Prop :=
  ∃ topLevelTransportFactor : ENNReal,
    topLevelTransportFactor ≠ ⊤ ∧
    ∀ {sigma sourceLoss inputLoss delta : ℝ},
      ∀ {source :
          PureWZ2ExtremalConfiguration sigma sourceLoss delta},
        ∀ {localized :
            PureWZ2ExtremalConfiguration sigma inputLoss delta},
          ∀ localization :
              PureWZ2SameDeltaSpatialCellLocalizationData
                source localized,
            Nonempty
              {rigid :
                PureWZ2LocalizedCanonicalRigidFrameData
                  localization //
                rigid.top_level_transport_factor =
                  topLevelTransportFactor}

def PureWZ2LocalizedCanonicalCropQuantitativeLeaf : Prop :=
  ∀ {sigma sourceLoss inputLoss outputLoss delta : ℝ},
    ∀ {source :
        PureWZ2ExtremalConfiguration sigma sourceLoss delta},
      ∀ {localized :
          PureWZ2ExtremalConfiguration sigma inputLoss delta},
        ∀ {localization :
            PureWZ2SameDeltaSpatialCellLocalizationData
              source localized},
          ∀ rigid :
              PureWZ2LocalizedCanonicalRigidFrameData
                localization,
            ∀ inputLossLeHalf : inputLoss ≤ outputLoss / 2,
              ∀ inputLossLe : inputLoss ≤ outputLoss,
              ∀ topLevelCWA :
                  WZ2PaperConvexWolffBound
                    rigid.croppedFamily
                    (Kakeya.realRpowENN delta (-outputLoss)),
                Nonempty
                  (PureWZ2CanonicalCropQuantitativeBounds
                    (rigid.toSourceDerivedStructuralData
                      inputLossLeHalf inputLossLe
                      localization.ordinary_per_tube topLevelCWA))

/-- The normalization input loss leaves room for all fixed CWA losses. -/
def pureWZ2CanonicalNormalizationInputLoss
    (outputLoss : ℝ) : ℝ :=
  min (outputLoss / 8) (1 / 2)

private theorem pureWZ2CanonicalNormalizationInputLoss_pos
    {outputLoss : ℝ}
    (outputLossPos : 0 < outputLoss) :
    0 < pureWZ2CanonicalNormalizationInputLoss outputLoss := by
  exact lt_min (by positivity) (by norm_num)

private theorem pureWZ2CanonicalNormalizationInputLoss_le
    {outputLoss : ℝ}
    (outputLossPos : 0 < outputLoss) :
    pureWZ2CanonicalNormalizationInputLoss outputLoss ≤
      outputLoss := by
  calc
    pureWZ2CanonicalNormalizationInputLoss outputLoss ≤
        outputLoss / 8 :=
      min_le_left _ _
    _ ≤ outputLoss := by linarith

private theorem pureWZ2CanonicalNormalizationInputLoss_le_half
    {outputLoss : ℝ}
    (outputLossPos : 0 < outputLoss) :
    pureWZ2CanonicalNormalizationInputLoss outputLoss ≤
      outputLoss / 2 := by
  calc
    pureWZ2CanonicalNormalizationInputLoss outputLoss ≤
        outputLoss / 8 :=
      min_le_left _ _
    _ ≤ outputLoss / 2 := by linarith

private theorem pureWZ2CanonicalNormalizationInputLoss_le_one
    (outputLoss : ℝ) :
    pureWZ2CanonicalNormalizationInputLoss outputLoss ≤ 1 := by
  calc
    pureWZ2CanonicalNormalizationInputLoss outputLoss ≤
        (1 / 2 : ℝ) :=
      min_le_right _ _
    _ ≤ 1 := by norm_num

private theorem pureWZ2CanonicalNormalizationInputLoss_gap
    {outputLoss : ℝ}
    (outputLossPos : 0 < outputLoss) :
    3 * pureWZ2CanonicalNormalizationInputLoss outputLoss <
      outputLoss := by
  have inputUpper :
      pureWZ2CanonicalNormalizationInputLoss outputLoss ≤
        outputLoss / 8 :=
    min_le_left _ _
  linarith

private theorem pureWZ2CanonicalNormalizationInputLoss_half_gap
    {outputLoss : ℝ}
    (outputLossPos : 0 < outputLoss) :
    3 * pureWZ2CanonicalNormalizationInputLoss outputLoss <
      outputLoss / 2 := by
  have inputUpper :
      pureWZ2CanonicalNormalizationInputLoss outputLoss ≤
        outputLoss / 8 :=
    min_le_left _ _
  linarith

private theorem
    exists_pureWZ2_topLevelTransportFactor_absorption
    (transportFactor : ENNReal)
    (transportFactorFinite : transportFactor ≠ ⊤)
    {outputLoss : ℝ}
    (outputLossPos : 0 < outputLoss) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ delta : ℝ,
        0 < delta →
        delta ≤ delta₀ →
          transportFactor *
              Kakeya.realRpowENN delta (-(outputLoss / 2)) ≤
            Kakeya.realRpowENN delta (-outputLoss) := by
  rcases
      exists_delta_realRpowENN_bound
        transportFactor transportFactorFinite
        (show 0 < outputLoss / 2 by positivity) with
    ⟨delta₀, delta₀Pos, delta₀LeOne, factorBound⟩
  refine ⟨delta₀, delta₀Pos, delta₀LeOne, ?_⟩
  intro delta deltaPos deltaLe
  calc
    transportFactor *
          Kakeya.realRpowENN delta (-(outputLoss / 2)) ≤
        Kakeya.realRpowENN delta (-(outputLoss / 2)) *
          Kakeya.realRpowENN delta (-(outputLoss / 2)) := by
      gcongr
      exact factorBound delta deltaPos deltaLe
    _ = Kakeya.realRpowENN delta (-outputLoss) := by
      rw [← Kakeya.Streamlined.realRpowENN_add deltaPos]
      congr 1
      ring

/--
The same-delta spatial localization producer, the canonical rigid-frame
producer, and the quantitative crop leaf close the source-derived
normalization leaf at exponent zero.

The ordinary top-level CWA is derived from pure nearby CWA by requesting
`rho₀ = delta ^ inputLoss`.  Only the final ordinary-to-paper convention
transport remains in the rigid-frame interface.
-/
theorem
    pureWZ2_cropped_critical_normalization_sourceDerivedLeaf_of_spatialRigidCrop
    (spatial :
      PureWZ2SameDeltaSpatialCellExtremalProducer)
    (rigidProducer :
      PureWZ2LocalizedCanonicalRigidFrameProducer)
    (cropLeaf :
      PureWZ2LocalizedCanonicalCropQuantitativeLeaf) :
    PureWZ2CroppedCriticalNormalizationSourceDerivedLeafAt 0 := by
  rcases rigidProducer with
    ⟨topLevelTransportFactor,
      topLevelTransportFactorFinite, produceRigid⟩
  intro sigma outputLoss outputLossPos
  let inputLoss :=
    pureWZ2CanonicalNormalizationInputLoss outputLoss
  have inputLossPos : 0 < inputLoss :=
    pureWZ2CanonicalNormalizationInputLoss_pos outputLossPos
  have inputLossLe : inputLoss ≤ outputLoss :=
    pureWZ2CanonicalNormalizationInputLoss_le outputLossPos
  have inputLossLeHalf : inputLoss ≤ outputLoss / 2 :=
    pureWZ2CanonicalNormalizationInputLoss_le_half outputLossPos
  have inputLossLeOne : inputLoss ≤ 1 :=
    pureWZ2CanonicalNormalizationInputLoss_le_one outputLoss
  have halfLossGap : 3 * inputLoss < outputLoss / 2 :=
    pureWZ2CanonicalNormalizationInputLoss_half_gap outputLossPos
  rcases spatial sigma inputLoss inputLossPos with
    ⟨sourceLoss, spatialDelta₀,
      sourceLossPos, _sourceLossLe,
      spatialDelta₀Pos, _spatialDelta₀LeOne,
      localize⟩
  rcases
      exists_pureWZ2_pureNearby_topCWA_absorption
        halfLossGap with
    ⟨cwaDelta₀, cwaDelta₀Pos, _cwaDelta₀LeOne,
      cwaAbsorption⟩
  rcases
      exists_pureWZ2_topLevelTransportFactor_absorption
        topLevelTransportFactor
        topLevelTransportFactorFinite
        outputLossPos with
    ⟨paperDelta₀, paperDelta₀Pos, _paperDelta₀LeOne,
      paperAbsorption⟩
  let delta₁ := min spatialDelta₀ (min cwaDelta₀ paperDelta₀)
  have delta₁Pos : 0 < delta₁ :=
    lt_min spatialDelta₀Pos
      (lt_min cwaDelta₀Pos paperDelta₀Pos)
  refine
    ⟨sourceLoss, inputLoss, delta₁,
      sourceLossPos, inputLossPos, inputLossLeHalf,
      delta₁Pos, ?_⟩
  intro delta deltaPos deltaLe source
  have deltaSpatial : delta ≤ spatialDelta₀ :=
    deltaLe.trans (min_le_left _ _)
  have deltaCWA : delta ≤ cwaDelta₀ :=
    deltaLe.trans
      ((min_le_right spatialDelta₀
        (min cwaDelta₀ paperDelta₀)).trans
          (min_le_left cwaDelta₀ paperDelta₀))
  have deltaPaper : delta ≤ paperDelta₀ :=
    deltaLe.trans
      ((min_le_right spatialDelta₀
        (min cwaDelta₀ paperDelta₀)).trans
          (min_le_right cwaDelta₀ paperDelta₀))
  rcases localize delta deltaPos deltaSpatial source with
    ⟨localized, ⟨localization⟩⟩
  rcases produceRigid localization with
    ⟨⟨rigid, rigidTransportFactor⟩⟩
  have localizedOrdinaryTop :
      WZ2PaperBodyConvexWolffBound
        localized.family.toBodyFamily
        (Kakeya.realRpowENN delta (-(outputLoss / 2))) := by
    apply
      pureWZ2_pureNearby_to_ordinaryTopCWA
        inputLossPos inputLossLeOne
        localized.extremal.delta_le_one
        localized.extremal.nonempty
        localized.extremal.cwa_nearby_scales
    intro rho rhoPos deltaRho rhoLeOne requestedRho
    exact
      cwaAbsorption delta rho
        deltaPos deltaCWA rhoPos
        deltaRho rhoLeOne requestedRho
  have croppedOrdinaryTop :
      WZ2PaperBodyConvexWolffBound
        rigid.croppedFamily.toBodyFamily
        (Kakeya.realRpowENN delta (-(outputLoss / 2))) :=
    pureWZ2RigidImageFamily_bodyCWA
      rigid.frame localized.family localizedOrdinaryTop
  have croppedTopRaw :
      WZ2PaperConvexWolffBound
        rigid.croppedFamily
        (rigid.top_level_transport_factor *
          Kakeya.realRpowENN delta (-(outputLoss / 2))) :=
    rigid.ordinary_to_paper_cwa croppedOrdinaryTop
  have croppedTop :
      WZ2PaperConvexWolffBound
        rigid.croppedFamily
        (Kakeya.realRpowENN delta (-outputLoss)) :=
    fun convexSet convex =>
      (croppedTopRaw convexSet convex).trans <| by
        gcongr
        rw [rigidTransportFactor]
        exact paperAbsorption delta deltaPos deltaPaper
  let data :=
    rigid.toSourceDerivedStructuralData
      inputLossLeHalf inputLossLe
      localization.ordinary_per_tube croppedTop
  rcases cropLeaf rigid inputLossLeHalf inputLossLe croppedTop with
    ⟨quantitative⟩
  exact
    ⟨localized,
      ⟨data.toSourceLeaves
        quantitative.toCanonicalScalars⟩⟩

/--
Consequently the same three inputs close the frozen critical normalization
theorem at exponent zero.
-/
theorem
    pureWZ2_cropped_critical_normalization_of_spatialRigidCanonicalCrop
    (spatial :
      PureWZ2SameDeltaSpatialCellExtremalProducer)
    (rigidProducer :
      PureWZ2LocalizedCanonicalRigidFrameProducer)
    (cropLeaf :
      PureWZ2LocalizedCanonicalCropQuantitativeLeaf) :
    PureWZ2CroppedCriticalNormalizationAt 0 :=
  pureWZ2_cropped_critical_normalization_of_sourceDerivedLeaf
    0
    (pureWZ2_cropped_critical_normalization_sourceDerivedLeaf_of_spatialRigidCrop
      spatial rigidProducer cropLeaf)

end Kakeya.Assouad

end
