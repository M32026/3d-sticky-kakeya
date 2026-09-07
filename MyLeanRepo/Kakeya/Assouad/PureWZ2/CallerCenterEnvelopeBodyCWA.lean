import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerCenterNearbyCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BodyCWASubfamilyTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CanonicalJohnBodyVolumeFloor
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureQuotientEnvelopeBodyCWA
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureFiberRestriction

/-!
# Actual-John CWA for one caller-center envelope fiber

Fix one scheduled raw parent and one monochromatic caller full fiber over its
factor-`19` envelope.  Each caller has an injectively chosen ambient center
source in the raw complete fiber.

The proof has four exact steps:

1. transport the complete raw fiber from its John chart to the envelope John
   chart;
2. restrict to the injective center-source subfamily, paying an explicit
   ambient/selected fiber-cardinality ratio;
3. identify this subfamily with the caller indices in the public strict
   envelope fiber;
4. enlarge each center-source body to its caller body.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem callerCenterEnvelopeFullFiber_convexWolff
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {scheduledRequested : WZ2PaperRequestedScale delta}
    {scheduled :
      WZ2PaperPureNearbyScaleCoverData
        fine scheduledRequested ambientConstant}
    {callerBase :
      WZ2PaperPureTubeSubfamily quotient.callerCoarse}
    {Color : Type*}
    {coloring :
      PureWZ2CallerCenterEnvelopeColoringData
        quotient scheduled callerBase Color}
    {selected :
      WZ2PaperPureTubeSubfamily callerBase.family}
    (data :
      PureWZ2CallerCenterMonochromaticEnvelopeCoverData
        coloring selected)
    (parent : Fin data.selectedCoarse.family.card)
    (envelopeNormalization :
      WZ2PaperAssouadUnitRescalingData
        (data.selectedCoarse.family.tube parent))
    (fiberRatio : ENNReal)
    (fiberRatioBound :
      wz2PaperOrdinaryFullFiberCount
          fine scheduled.scaleData.coarse
          (data.selectedCoarse.embedding parent) ≤
        fiberRatio *
          wz2PaperOrdinaryFullFiberCount
            selected.family data.selectedCoarse.family parent) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := selected.family)
        (coarse := data.selectedCoarse.family)
        parent envelopeNormalization)
      (fiberRatio * ((185193 : ENNReal) * ambientConstant)) := by
  let ambientParent : Fin scheduled.scaleData.coarse.card :=
    data.selectedCoarse.embedding parent
  let actualFiber :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine)
        (coarse := scheduled.scaleData.coarse)
        ambientParent ambientConstant :=
    Classical.choice
      (scheduled.scaleData.rescaledFiber ambientParent)
  have parentTubeEq :
      data.selectedCoarse.family.tube parent =
        wz2PaperOrdinaryEnvelope
          (scheduled.scaleData.coarse.tube ambientParent) := by
    rw [data.selectedCoarse.tube_eq]
    rfl
  let canonicalEnvelopeNormalization :
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope
          (scheduled.scaleData.coarse.tube ambientParent)) :=
    parentTubeEq ▸ envelopeNormalization
  have normalizationMapEq :
      canonicalEnvelopeNormalization.map =
        envelopeNormalization.map := by
    apply AffineEquiv.ext
    intro point
    simp only [WZ2PaperAssouadUnitRescalingData.map]
    congr <;> exact parentTubeEq.symm
  let ambientActualBodies :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := fine)
      (coarse := scheduled.scaleData.coarse)
      ambientParent actualFiber.normalization
  let transportedBodies :=
    wz2PaperPureQuotientEnvelopeTransportedBodyFamily
      ambientParent actualFiber canonicalEnvelopeNormalization
  let transportIndexEquiv :
      Fin transportedBodies.card ≃
        Fin ambientActualBodies.card :=
    Equiv.refl _
  have transportedCWA :
      WZ2PaperBodyConvexWolffBound
        transportedBodies ((185193 : ENNReal) * ambientConstant) := by
    apply
      wz2PaperBodyConvexWolffBound_of_ordinaryEnvelopeJohnTransport
        (source := ambientActualBodies)
        (target := transportedBodies)
        scheduled.scaleData.rho_pos
        (scheduled.scaleData.coarse.tube ambientParent)
        actualFiber.normalization
        canonicalEnvelopeNormalization
        transportIndexEquiv
    · intro targetIndex
      change
        wz2PaperOrdinaryEnvelopeJohnCoordinateChange
              actualFiber.normalization canonicalEnvelopeNormalization ''
            (actualFiber.normalization.map ''
              (fine.tube
                ((wz2PaperOrdinaryFullFiberIndexEquiv ambientParent)
                  (transportIndexEquiv targetIndex)).1).carrier) ⊆
          canonicalEnvelopeNormalization.map ''
            (fine.tube
              ((wz2PaperOrdinaryFullFiberIndexEquiv ambientParent)
                targetIndex).1).carrier
      rintro _ ⟨johnPoint, ⟨physicalPoint, hphysicalPoint, rfl⟩, rfl⟩
      refine ⟨physicalPoint, ?_, ?_⟩
      · have hindex :
            transportIndexEquiv targetIndex = targetIndex := rfl
        rw [hindex] at hphysicalPoint
        exact hphysicalPoint
      · exact
          (wz2PaperOrdinaryEnvelopeJohnCoordinateChange_apply_map
            actualFiber.normalization canonicalEnvelopeNormalization
            physicalPoint).symm
    · exact actualFiber.convex_wolff
  let targetFiberEquiv :=
    wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := selected.family)
      (coarse := data.selectedCoarse.family)
      parent
  let ambientFiberEquiv :=
    wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := fine)
      (coarse := scheduled.scaleData.coarse)
      ambientParent
  let centerSource :
      Fin selected.family.card → Fin fine.card :=
    fun callerIndex =>
      quotient.representative
        (quotient.net.centerEmbedding
          (quotient.callerCenter
            (callerBase.embedding
              (selected.embedding callerIndex))))
  have centerSourceInjective :
      Function.Injective centerSource := by
    intro first second heq
    apply selected.embedding.injective
    apply callerBase.embedding.injective
    exact quotient.callerCenterSource_injective heq
  have centerSourceMem :
      ∀ targetIndex,
        centerSource (targetFiberEquiv targetIndex).1 ∈
          wz2PaperOrdinaryFullFiberIndices
            fine scheduled.scaleData.coarse ambientParent := by
    intro targetIndex
    let callerIndex := (targetFiberEquiv targetIndex).1
    have callerMem :
        callerIndex ∈
          wz2PaperOrdinaryFullFiberIndices
            selected.family data.selectedCoarse.family parent :=
      (targetFiberEquiv targetIndex).2
    have ownerEq :
        pureWZ2CallerCenterScheduledOwner
            quotient scheduled
            (callerBase.embedding
              (selected.embedding callerIndex)) =
          ambientParent := by
      rw [data.fullFiberIndices_eq_owner parent] at callerMem
      exact (Finset.mem_filter.mp callerMem).2
    have scheduledParent :
        scheduled.scaleData.cover.parent
            (centerSource callerIndex) =
          ambientParent := by
      exact ownerEq
    exact
      (scheduled.scaleData.cover.mem_fullFiber_iff_parent_eq
        scheduled.scaleData.rho_pos.le
        ambientParent
        (centerSource callerIndex)).mpr scheduledParent
  let sourceBodyIndex :
      Fin
          (wz2PaperPureUnitRescaledFullFiberBodyFamily
            (fine := selected.family)
            (coarse := data.selectedCoarse.family)
            parent envelopeNormalization).card →
        Fin transportedBodies.card :=
    fun targetIndex =>
      ambientFiberEquiv.symm
        ⟨centerSource (targetFiberEquiv targetIndex).1,
          centerSourceMem targetIndex⟩
  have sourceBodyIndexInjective :
      Function.Injective sourceBodyIndex := by
    intro first second heq
    apply targetFiberEquiv.injective
    apply Subtype.ext
    apply centerSourceInjective
    have hambient :=
      congrArg
        (fun sourceIndex : Fin transportedBodies.card =>
          (ambientFiberEquiv sourceIndex).1)
        heq
    simpa [sourceBodyIndex] using hambient
  let centerBodies : Kakeya.Streamlined.Subfamily transportedBodies :=
    {
      family :=
        {
          card :=
            (wz2PaperPureUnitRescaledFullFiberBodyFamily
              (fine := selected.family)
              (coarse := data.selectedCoarse.family)
              parent envelopeNormalization).card
          body := fun targetIndex =>
            transportedBodies.body (sourceBodyIndex targetIndex)
        }
      embedding :=
        {
          toFun := sourceBodyIndex
          inj' := sourceBodyIndexInjective
        }
      carrier_eq := fun _ => rfl
    }
  have centerBodiesCWA :
      WZ2PaperBodyConvexWolffBound
        centerBodies.family
        (fiberRatio * ((185193 : ENNReal) * ambientConstant)) := by
    apply
      transportedCWA.subfamily_of_cardinality
        centerBodies
    change
      wz2PaperOrdinaryFullFiberCount
          fine scheduled.scaleData.coarse ambientParent ≤
        fiberRatio *
          wz2PaperOrdinaryFullFiberCount
            selected.family data.selectedCoarse.family parent
    exact fiberRatioBound
  let targetBodies :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := selected.family)
      (coarse := data.selectedCoarse.family)
      parent envelopeNormalization
  apply
    WZ2PaperBodyConvexWolffBound.of_pointwise_subset
      (source := centerBodies.family)
      (target := targetBodies)
      rfl
  · intro targetIndex
    let callerIndex := (targetFiberEquiv targetIndex).1
    have hcenter :
        (fine.tube (centerSource callerIndex)).carrier ⊆
          (selected.family.tube callerIndex).carrier := by
      rw [selected.tube_eq, callerBase.tube_eq]
      exact
        quotient.callerCenterSource_carrier_subset
          (callerBase.embedding
            (selected.embedding callerIndex))
    change
      canonicalEnvelopeNormalization.map ''
          (fine.tube
            ((ambientFiberEquiv
              (sourceBodyIndex targetIndex)).1)).carrier ⊆
        envelopeNormalization.map ''
          (selected.family.tube
            (targetFiberEquiv targetIndex).1).carrier
    have hsource :
        (ambientFiberEquiv
          (sourceBodyIndex targetIndex)).1 =
            centerSource callerIndex := by
      simp [sourceBodyIndex, callerIndex]
    rw [hsource, normalizationMapEq]
    exact Set.image_mono hcenter
  · exact centerBodiesCWA

/--
Assemble one scheduled caller-center envelope scale from the exact
monochromatic cover, selected strict-fiber uniformity, and a uniform
ambient-to-selected fiber ratio.
-/
noncomputable def callerCenterMonochromaticEnvelopeScaleData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {scheduledRequested : WZ2PaperRequestedScale delta}
    {scheduled :
      WZ2PaperPureNearbyScaleCoverData
        fine scheduledRequested ambientConstant}
    {callerBase :
      WZ2PaperPureTubeSubfamily quotient.callerCoarse}
    {Color : Type*}
    {coloring :
      PureWZ2CallerCenterEnvelopeColoringData
        quotient scheduled callerBase Color}
    {selected :
      WZ2PaperPureTubeSubfamily callerBase.family}
    (data :
      PureWZ2CallerCenterMonochromaticEnvelopeCoverData
        coloring selected)
    (coverConstant fiberRatio : ENNReal)
    (fullFiberUniform :
      WZ2PaperPureFullFibersAreCUniform
        selected.family data.selectedCoarse.family coverConstant)
    (fiberRatioBound :
      ∀ parent : Fin data.selectedCoarse.family.card,
        wz2PaperOrdinaryFullFiberCount
            fine scheduled.scaleData.coarse
            (data.selectedCoarse.embedding parent) ≤
          fiberRatio *
            wz2PaperOrdinaryFullFiberCount
              selected.family data.selectedCoarse.family parent) :
    WZ2PaperPureScaleCoverData
      selected.family (19 * scheduled.rho)
      (max coverConstant
        (fiberRatio * ((185193 : ENNReal) * ambientConstant))) := by
  let normalization :
      ∀ parent : Fin data.selectedCoarse.family.card,
        WZ2PaperAssouadUnitRescalingData
          (data.selectedCoarse.family.tube parent) :=
    fun parent =>
      WZ2PaperAssouadUnitRescalingData.ofTube
        (data.selectedCoarse.family.tube parent)
        (mul_pos (by norm_num) scheduled.scaleData.rho_pos)
  exact
    data.toPureScaleData
      coverConstant
      (fiberRatio * ((185193 : ENNReal) * ambientConstant))
      fullFiberUniform normalization
      (fun parent =>
        callerCenterEnvelopeFullFiber_convexWolff
          data parent (normalization parent)
          fiberRatio (fiberRatioBound parent))

/--
Preferred one-scale assembly.  The canonical John bodies of the selected
caller full fiber satisfy CWA directly from their physical volume ratio, so
no ambient-to-center fiber ratio is needed.
-/
noncomputable def callerCenterMonochromaticEnvelopeScaleDataOfVolume
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {scheduledRequested : WZ2PaperRequestedScale delta}
    {scheduled :
      WZ2PaperPureNearbyScaleCoverData
        fine scheduledRequested ambientConstant}
    {callerBase :
      WZ2PaperPureTubeSubfamily quotient.callerCoarse}
    {Color : Type*}
    {coloring :
      PureWZ2CallerCenterEnvelopeColoringData
        quotient scheduled callerBase Color}
    {selected :
      WZ2PaperPureTubeSubfamily callerBase.family}
    (data :
      PureWZ2CallerCenterMonochromaticEnvelopeCoverData
        coloring selected)
    (coverConstant : ENNReal)
    (fullFiberUniform :
      WZ2PaperPureFullFibersAreCUniform
        selected.family data.selectedCoarse.family coverConstant) :
    let bodyConstant :=
      (27 : ENNReal) *
        (Kakeya.deltaTubeVolume (19 * scheduled.rho)) *
        (Kakeya.deltaTubeVolume callerRequested.1)⁻¹
    WZ2PaperPureScaleCoverData
      selected.family (19 * scheduled.rho)
      (max coverConstant bodyConstant) := by
  let bodyConstant :=
    (27 : ENNReal) *
      (Kakeya.deltaTubeVolume (19 * scheduled.rho)) *
      (Kakeya.deltaTubeVolume callerRequested.1)⁻¹
  let normalization :
      ∀ parent : Fin data.selectedCoarse.family.card,
        WZ2PaperAssouadUnitRescalingData
          (data.selectedCoarse.family.tube parent) :=
    fun parent =>
      WZ2PaperAssouadUnitRescalingData.ofTube
        (data.selectedCoarse.family.tube parent)
        (mul_pos (by norm_num) scheduled.scaleData.rho_pos)
  apply
    data.toPureScaleData
      coverConstant bodyConstant
      fullFiberUniform normalization
  intro parent
  have hparentVolume :
      volume (data.selectedCoarse.family.tube parent).carrier =
        Kakeya.deltaTubeVolume (19 * scheduled.rho) := by
    let canonical : Kakeya.DeltaTube (19 * scheduled.rho) :=
      {
        base := 0
        direction := EuclideanSpace.single (0 : Fin 3) 1
        direction_unit := by simp
      }
    have hvolume :=
      Kakeya.Streamlined.tube_volume_eq
        (data.selectedCoarse.family.tube parent) canonical
    calc
      volume (data.selectedCoarse.family.tube parent).carrier =
          (data.selectedCoarse.family.tube parent).volume := rfl
      _ = canonical.volume := hvolume
      _ = Kakeya.deltaTubeVolume (19 * scheduled.rho) := rfl
  have raw :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily_convexWolff_volumeRatio
      (fine := selected.family)
      (coarse := data.selectedCoarse.family)
      parent
      (scheduled.scaleData.delta_pos.trans_le
        callerRequested.2.1)
      (mul_pos (by norm_num) scheduled.scaleData.rho_pos)
      (normalization parent)
  simpa [bodyConstant, hparentVolume] using raw

end Kakeya.Assouad

end
