import MyLeanRepo.Kakeya.Assouad.PureWZ2.BoundedPaperCarrierImageContainment
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LiteralExactImageOrdinaryShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CriticalMultiplicityInputs
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricFiberRescaling
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescaledShading

/-!
# Bounded-base critical witnesses on exact V4 final fibers

This is the normalization-free sibling of the final-fiber witness route.
It keeps the canonical complete final fiber fixed, transports the inherited
bounded-base certificate through its stored same-family provenance, and uses
the exact literal affine image of the supplied final-fiber shading.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Same-family provenance, restated here so this bounded-base route does not
import the normalization-trace witness module. -/
structure Prop62V4BoundedFinalFiberSameFamilyData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (parent : Fin coarse.card)
    {sourceConstant : ENNReal}
    (rescaling :
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant) where
  indexEquiv :
    Fin (wz2PaperFullFiberSubfamily fine coarse parent).family.card ≃
      Fin rescaling.sourceFamily.card
  tube_eq : ∀ index,
    (wz2PaperFullFiberSubfamily fine coarse parent).family.tube index =
      rescaling.sourceFamily.tube (indexEquiv index)

namespace PureWZ2Prop62MetricFiberRescalingInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {parent : Fin coarse.card}
    {sourceConstant : ENNReal}
    (rescaling :
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant)

noncomputable def boundedFinalFiberSameFamily :
    Prop62V4BoundedFinalFiberSameFamilyData cover parent rescaling := by
  let indices := wz2PaperFullFiberIndices fine coarse parent
  let fiber := wz2PaperFullFiberSubfamily fine coarse parent
  let fiberEnum : Fin fiber.family.card ≃ indices :=
    (indices.orderIsoOfFin rfl).toEquiv
  let sameIndices : indices ≃ rescaling.sourceIndices :=
    { toFun := fun index =>
        ⟨index.1, by
          rw [rescaling.sourceIndices_eq]
          exact index.2⟩
      invFun := fun index =>
        ⟨index.1, by
          change index.1 ∈ wz2PaperFullFiberIndices fine coarse parent
          rw [← rescaling.sourceIndices_eq]
          exact index.2⟩
      left_inv := fun _ => by ext; rfl
      right_inv := fun _ => by ext; rfl }
  let indexEquiv :=
    fiberEnum.trans (sameIndices.trans rescaling.sourceEquiv.symm)
  refine { indexEquiv := indexEquiv, tube_eq := ?_ }
  intro index
  rw [fiber.tube_eq, rescaling.source_tube_eq]
  congr 2
  let member := sameIndices (fiberEnum index)
  have roundTrip :
      rescaling.sourceEquiv (rescaling.sourceEquiv.symm member) = member :=
    rescaling.sourceEquiv.apply_symm_apply member
  change (fiberEnum index).1 =
    (rescaling.sourceEquiv (rescaling.sourceEquiv.symm member)).1
  rw [roundTrip]
  rfl

end PureWZ2Prop62MetricFiberRescalingInput

namespace Prop62V4BoundedFinalFiberSameFamilyData

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {parent : Fin coarse.card}
    {sourceConstant : ENNReal}
    {rescaling :
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant}
    (sameFamily :
      Prop62V4BoundedFinalFiberSameFamilyData
        cover parent rescaling)

noncomputable def publicReindex :
    PureWZ2Prop62PublicRescalingReindexData
      (wz2PaperFullFiberSubfamily fine coarse parent).family
      (coarse.tube parent) rescaling.rho_pos rescaling.rho_le_one
      (cover.fine_line_class.subfamily
        (wz2PaperFullFiberSubfamily fine coarse parent))
      (cover.coarse_line_class parent)
      (fun index => by
        rw [(wz2PaperFullFiberSubfamily fine coarse parent).tube_eq]
        exact
          (mem_wz2PaperFullFiberIndices_iff
            parent
            ((wz2PaperFullFiberSubfamily fine coarse parent).embedding index)).mp <|
            Finset.orderEmbOfFin_mem
              (wz2PaperFullFiberIndices fine coarse parent) rfl index)
      sourceConstant where
  ambientFine := fine
  ambientCoarse := coarse
  ambientCover := cover
  ambientParent := parent
  anchor_eq := rfl
  input := rescaling
  indexEquiv := sameFamily.indexEquiv
  tube_eq := sameFamily.tube_eq

end Prop62V4BoundedFinalFiberSameFamilyData

namespace Prop62V4BoundedFinalFiber

variable
    {delta rho structuralLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {parent : Fin coarse.card}
    {sourceConstant : ENNReal}
    (rescaling :
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant)

/-- The paper-literal family on the exact, complete final fiber. -/
noncomputable def literal :
    WZ2PaperLiteralUnitRescaledFamilyData
      (wz2PaperFullFiberSubfamily fine coarse parent).family
      (coarse.tube parent) rescaling.rho_pos :=
  wz2PaperLiteralOrdinaryRescaledFamilyLiteralData
    rescaling.rho_pos rescaling.rho_le_one
    (wz2PaperFullFiberSubfamily fine coarse parent).family
    (coarse.tube parent)
    (cover.fine_line_class.subfamily
      (wz2PaperFullFiberSubfamily fine coarse parent))
    (cover.coarse_line_class parent)
    (fun index => by
      rw [(wz2PaperFullFiberSubfamily fine coarse parent).tube_eq]
      exact
        (mem_wz2PaperFullFiberIndices_iff
          parent
          ((wz2PaperFullFiberSubfamily fine coarse parent).embedding index)).mp <|
          Finset.orderEmbOfFin_mem
            (wz2PaperFullFiberIndices fine coarse parent) rfl index)

/-- The standard cubical literal target for the unchanged final-fiber shading. -/
noncomputable def literalShading
    (sourceShading :
      WZ1PaperTubeShading
        (wz2PaperFullFiberSubfamily fine coarse parent).family) :
    WZ2PaperLiteralUnitRescaledShadingData
      (literal rescaling) sourceShading :=
  Classical.choice <|
    wz2_paper_literal_unit_rescaled_shading
      wz2_paper_literal_image_carrier
      rescaling.delta_pos rescaling.rho_pos rescaling.rho_le_one
      (by
        calc
          delta / rho ≤ 1 / 100 := by
            rw [div_le_iff₀ rescaling.rho_pos]
            nlinarith [rescaling.scale_separation]
          _ ≤ 1 / 24 := by norm_num)
      (cover.fine_line_class.subfamily
        (wz2PaperFullFiberSubfamily fine coarse parent))
      (cover.coarse_line_class parent)
      (fun index => by
        rw [(wz2PaperFullFiberSubfamily fine coarse parent).tube_eq]
        exact
          (mem_wz2PaperFullFiberIndices_iff
            parent
            ((wz2PaperFullFiberSubfamily fine coarse parent).embedding index)).mp <|
            Finset.orderEmbOfFin_mem
              (wz2PaperFullFiberIndices fine coarse parent) rfl index)
      (literal rescaling) sourceShading

/--
The smallest generic bounded-base constructor.  Its only quantitative data
are the packet mass retained on the exact final fiber and the scalar
absorptions needed to convert that mass into density after rescaling.
-/
noncomputable def witness
    (sourceShading :
      WZ1PaperTubeShading
        (wz2PaperFullFiberSubfamily fine coarse parent).family)
    (boundedBase : HasBoundedBase rescaling.sourceFamily 4)
    (packetDensity : ENNReal)
    (packetMassLower :
      packetDensity *
          (wz2PaperFullFiberSubfamily fine coarse parent).family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        sourceShading.mass)
    (cwaAbsorption :
      (81000000 : ENNReal) * sourceConstant ≤
        Kakeya.realRpowENN (delta / rho) (-structuralLoss))
    (densityAbsorption :
      Kakeya.realRpowENN (delta / rho) structuralLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * packetDensity) :
    PureWZ2Prop62CriticalRescaledFiberFloorWitness
      (loss := structuralLoss) sourceShading (coarse.tube parent)
      rescaling.rho_pos := by
  let fiber := wz2PaperFullFiberSubfamily fine coarse parent
  let sameFamily := rescaling.boundedFinalFiberSameFamily
  let publicReindex := sameFamily.publicReindex
  let certificate := publicReindex.targetCertificate
  let literalData := literal rescaling
  let targetShading := literalShading rescaling sourceShading
  let ratio := delta / rho
  let jacobian : ENNReal :=
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
      ENNReal.ofReal ((1 / rho : ℝ) ^ 2)
  have ratioLeOne : ratio ≤ 1 := by
    rw [show ratio = delta / rho by rfl]
    have deltaLeRho : delta ≤ rho := by
      nlinarith [rescaling.scale_separation, rescaling.delta_pos]
    exact (div_le_one rescaling.rho_pos).mpr deltaLeRho
  have imageSubsetPublic :
      ∀ publicIndex,
        wz2PaperLiteralUnitRescalingMap (coarse.tube parent) rescaling.rho_pos ''
            sourceShading.carrier
              (literalData.sourceIndex
                (certificate.section6Index.symm publicIndex)) ⊆
          (certificate.publicFamily.tube publicIndex).carrier := by
    intro publicIndex
    let sourceIndex :=
      literalData.sourceIndex
        (certificate.section6Index.symm publicIndex)
    have sourceLine : WZ1PaperTubeInLineClass (fiber.family.tube sourceIndex) :=
      cover.fine_line_class.subfamily fiber sourceIndex
    have sourceBase : ‖(fiber.family.tube sourceIndex).base‖ ≤ 4 := by
      rw [sameFamily.tube_eq sourceIndex]
      exact boundedBase (sameFamily.indexEquiv sourceIndex)
    have sourceCovered :
        WZ1PaperTubeCovers (fiber.family.tube sourceIndex)
          (coarse.tube parent) := by
      rw [fiber.tube_eq]
      exact
        (mem_wz2PaperFullFiberIndices_iff
          parent (fiber.embedding sourceIndex)).mp <|
          Finset.orderEmbOfFin_mem
            (wz2PaperFullFiberIndices fine coarse parent) rfl sourceIndex
    have carrierSubset :
        sourceShading.carrier sourceIndex ⊆
          wz1PaperTubeCarrier (fiber.family.tube sourceIndex) :=
      sourceShading.subset_body sourceIndex
    have contained :=
      wz2PaperLiteral_image_paperCarrier_subset_ordinary_of_boundedBase
        rescaling.delta_pos (fiber.family.tube sourceIndex)
        (coarse.tube parent) rescaling.rho_pos rescaling.rho_le_one
        (by
          rw [div_le_iff₀ rescaling.rho_pos]
          nlinarith [rescaling.scale_separation, rescaling.delta_pos])
        sourceLine sourceBase sourceCovered
    intro imagePoint imageMem
    have imageInOrdinary := contained (Set.image_mono carrierSubset imageMem)
    change imagePoint ∈
      (wz2PaperLiteralOrdinaryRescaledTube
        (fiber.family.tube sourceIndex) (coarse.tube parent)
        rescaling.rho_pos).carrier
    simpa [certificate, publicReindex, literalData, sourceIndex] using imageInOrdinary
  have publicCWA :
      WZ2PaperPureCWAAtNearbyScales certificate.publicFamily
        (Kakeya.realRpowENN ratio (-structuralLoss)) := by
    have inherited := publicReindex.publicPureCWA
    exact inherited.mono cwaAbsorption (by simp [Kakeya.realRpowENN])
  have bodyMassUpper :
      certificate.publicFamily.toBodyFamily.mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN ratio 2 * fiber.family.enncard := by
    have targetCard :
        literalData.targetFamily.enncard = fiber.family.enncard := by
      have cardEq : literalData.targetFamily.card = fiber.family.card := by
        simpa using Fintype.card_congr <|
          Equiv.ofBijective
            literalData.sourceIndex literalData.sourceIndex_bijective
      exact congrArg (fun cardinality : ℕ => (cardinality : ENNReal)) cardEq
    have publicCard :
        certificate.publicFamily.enncard = fiber.family.enncard := by
      calc
        certificate.publicFamily.enncard = literalData.targetFamily.enncard :=
          certificate.publicFamily_enncard_eq
        _ = fiber.family.enncard := targetCard
    have tubeVolumeUpper :
        Kakeya.deltaTubeVolume ratio ≤
          24 * Kakeya.realRpowENN ratio 2 *
            Kakeya.deltaTubeVolume 1 := by
      have fiberNonempty : fiber.family.Nonempty := by
        change 0 < (wz2PaperFullFiberIndices fine coarse parent).card
        apply Finset.card_pos.mpr
        rcases cover.parent_hit parent with ⟨index, covered⟩
        exact ⟨index,
          (mem_wz2PaperFullFiberIndices_iff parent index).mpr covered⟩
      let index : Fin fiber.family.card := ⟨0, fiberNonempty⟩
      have upper :=
        tube_volume_scaling.2.2 ratio (div_pos rescaling.delta_pos rescaling.rho_pos)
          ratioLeOne
          (certificate.publicFamily.tube
            (certificate.section6Index
              (literalData.sourceIndex_bijective.surjective index).choose))
      rwa [tube_volume_scaling.1 ratio
        (certificate.publicFamily.tube
          (certificate.section6Index
            (literalData.sourceIndex_bijective.surjective index).choose))] at upper
    rw [tubeFamily_mass_eq_nominal]
    change
      certificate.publicFamily.enncard *
          Kakeya.deltaTubeVolume ratio ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN ratio 2 * fiber.family.enncard
    rw [publicCard]
    calc
      fiber.family.enncard * Kakeya.deltaTubeVolume ratio ≤
          fiber.family.enncard *
            (24 * Kakeya.realRpowENN ratio 2 *
              Kakeya.deltaTubeVolume 1) := by gcongr
      _ ≤ fiber.family.enncard *
            (55296 * Kakeya.realRpowENN ratio 2 *
              Kakeya.deltaTubeVolume 1) := by
          gcongr
          norm_num
      _ = (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN ratio 2 * fiber.family.enncard := by ring
  have scaleIdentity :
      ENNReal.ofReal ((1 / rho : ℝ) ^ 2) *
          Kakeya.realRpowENN delta 2 =
        Kakeya.realRpowENN ratio 2 := by
    simp only [ratio, Kakeya.realRpowENN]
    have deltaTwo : Real.rpow delta 2 = delta ^ 2 :=
      Real.rpow_two delta
    have ratioTwo :
        Real.rpow (delta / rho) 2 = (delta / rho) ^ 2 :=
      Real.rpow_two (delta / rho)
    rw [deltaTwo, ratioTwo]
    rw [← ENNReal.ofReal_mul (sq_nonneg (1 / rho))]
    congr 1
    field_simp [rescaling.rho_pos.ne']
  have massLower :
      Kakeya.realRpowENN ratio structuralLoss *
          certificate.publicFamily.toBodyFamily.mass ≤
        jacobian * sourceShading.mass := by
    calc
      Kakeya.realRpowENN ratio structuralLoss *
            certificate.publicFamily.toBodyFamily.mass ≤
          Kakeya.realRpowENN ratio structuralLoss *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN ratio 2 * fiber.family.enncard) := by
          gcongr
      _ = (Kakeya.realRpowENN ratio structuralLoss *
            (55296 * Kakeya.deltaTubeVolume 1)) *
            (Kakeya.realRpowENN ratio 2 * fiber.family.enncard) := by ring
      _ ≤ (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * packetDensity) *
            (Kakeya.realRpowENN ratio 2 * fiber.family.enncard) := by
          gcongr
      _ = jacobian *
            (packetDensity * fiber.family.enncard *
              Kakeya.realRpowENN delta 2) := by
          rw [← scaleIdentity]
          ring
      _ ≤ jacobian * sourceShading.mass := by gcongr
  have ordinaryDense :
      (certificate.literalExactCroppedImageShading
        sourceShading imageSubsetPublic).IsLambdaDense
          (Kakeya.realRpowENN ratio structuralLoss) :=
    certificate.literalExactCroppedImageShading_dense_of_mass
      sourceShading imageSubsetPublic massLower
  exact
    { familyData := literalData
      literalShading := targetShading
      ordinaryFamily := certificate.publicFamily
      ordinaryShading :=
        certificate.literalExactCroppedImageShading
          sourceShading imageSubsetPublic
      ordinary_nonempty := by
        apply certificate.publicFamily_nonempty
        have fiberNonempty : fiber.family.Nonempty := by
          change 0 < (wz2PaperFullFiberIndices fine coarse parent).card
          apply Finset.card_pos.mpr
          rcases cover.parent_hit parent with ⟨index, covered⟩
          exact ⟨index,
            (mem_wz2PaperFullFiberIndices_iff parent index).mpr covered⟩
        have cardEq : literalData.targetFamily.card = fiber.family.card := by
          simpa using Fintype.card_congr <|
            Equiv.ofBijective
              literalData.sourceIndex literalData.sourceIndex_bijective
        change 0 < literalData.targetFamily.card
        rw [cardEq]
        exact fiberNonempty
      ordinary_cwa := publicCWA
      ordinary_dense := ordinaryDense
      ordinary_union_subset_target :=
        certificate.literalExactCroppedImageShading_union_subset
          sourceShading imageSubsetPublic targetShading }

end Prop62V4BoundedFinalFiber

end Kakeya.Assouad

end
