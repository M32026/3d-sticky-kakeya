import MyLeanRepo.Kakeya.Assouad.PureWZ2.LiteralExactImageOrdinaryShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationFinalOrdinaryTrace
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CriticalMultiplicityInputs
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperFinalV4CoarseFiberDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4PureRefinementComposition
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4PureScalarInputs
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescaledShading

/-!
# Non-circular critical witnesses for the exact V4 final fibers

The final four-degree certificate retains a complete-fiber rescaling input,
but the critical multiplicity argument needs an ordinary dense shading whose
union lies in the corresponding literal target shading.  This module obtains
that ordinary shading from the frozen normalization trace.

No final-fiber extremal output is used.  The only quantitative assumptions of
the generic constructor are:

* absorption of the inherited pure-CWA constant at the chosen structural
  loss;
* one exact Jacobian-scaled mass lower bound for the ordinary trace.

The finite equivalence and tube equalities identifying the rescaling input
with the exact final full fiber are constructed from the provenance already
stored in `PureWZ2Prop62MetricFiberRescalingInput`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2CroppedCriticalNormalizationData

variable
    {sigma sourceLoss normalizationLoss delta rho : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent)
    (selected :
      Kakeya.Streamlined.TubeSubfamily normalized.croppedFamily)
    (finalShading : WZ1PaperTubeShading selected.family)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (cover : PureWZ2Section6Cover selected.family coarse)
    (parent : Fin coarse.card)

/-- The exact complete final fiber, indexed as a subfamily of the final
selected family. -/
noncomputable def criticalFinalFiber :
    Kakeya.Streamlined.TubeSubfamily selected.family :=
  wz2PaperFullFiberSubfamily selected.family coarse parent

/-- The exact complete final fiber, now embedded all the way back into the
normalized cropped family. -/
noncomputable def criticalFinalFiberInNormalized :
    Kakeya.Streamlined.TubeSubfamily normalized.croppedFamily :=
  selected.comp
    (criticalFinalFiber
      (normalized := normalized) selected coarse parent)

/-- The final four-degree shading restricted to the exact complete fiber. -/
noncomputable def criticalFinalFiberShading :
    WZ1PaperTubeShading
      (criticalFinalFiber
        (normalized := normalized) selected coarse parent).family :=
  restrictPaperShading
    (criticalFinalFiber
      (normalized := normalized) selected coarse parent)
    finalShading

/-- The ordinary normalization trace on the same exact final-fiber indices. -/
noncomputable def criticalFinalFiberOrdinaryTrace :
    Kakeya.Streamlined.TubeShading
      (criticalFinalFiber
        (normalized := normalized) selected coarse parent).family :=
  normalized.finalOrdinaryTrace
    (criticalFinalFiberInNormalized
      (normalized := normalized) selected coarse parent)
    (criticalFinalFiberShading
      (normalized := normalized) selected finalShading coarse parent)

@[simp] theorem criticalFinalFiberInNormalized_embedding
    (index :
      Fin
        (criticalFinalFiber
          (normalized := normalized) selected coarse parent).family.card) :
    (criticalFinalFiberInNormalized
      (normalized := normalized) selected coarse parent).embedding index =
        selected.embedding
          ((criticalFinalFiber
            (normalized := normalized) selected coarse parent).embedding index) :=
  rfl

@[simp] theorem criticalFinalFiberShading_carrier
    (index :
      Fin
        (criticalFinalFiber
          (normalized := normalized) selected coarse parent).family.card) :
    (criticalFinalFiberShading
      (normalized := normalized) selected finalShading coarse parent).carrier index =
        finalShading.carrier
          ((criticalFinalFiber
            (normalized := normalized) selected coarse parent).embedding index) :=
  rfl

theorem criticalFinalFiberOrdinaryTrace_subset
    (index :
      Fin
        (criticalFinalFiber
          (normalized := normalized) selected coarse parent).family.card) :
    (criticalFinalFiberOrdinaryTrace
        (normalized := normalized)
        selected finalShading coarse parent).carrier index ⊆
      (criticalFinalFiberShading
        (normalized := normalized)
        selected finalShading coarse parent).carrier index := by
  intro point pointMem
  exact pointMem.2

end PureWZ2CroppedCriticalNormalizationData

/--
The same-family certificate between the exact final full fiber and the source
family stored by its inherited metric-fiber rescaling input.

These are the two provenance facts needed to transport pure CWA without
selecting a new fiber.
-/
structure Prop62V4FinalFiberSameFamilyData
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
  tube_eq :
    ∀ index,
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

/--
Recover the exact final-fiber equivalence from the `sourceIndices`,
`sourceEquiv`, and `source_tube_eq` fields of the stored rescaling input.
-/
noncomputable def finalFiberSameFamily :
    Prop62V4FinalFiberSameFamilyData cover parent rescaling := by
  let indices := wz2PaperFullFiberIndices fine coarse parent
  let fiber := wz2PaperFullFiberSubfamily fine coarse parent
  let fiberEnum : Fin fiber.family.card ≃ indices :=
    (indices.orderIsoOfFin rfl).toEquiv
  let sameIndices : indices ≃ rescaling.sourceIndices :=
    {
      toFun := fun index =>
        ⟨index.1, by
          rw [rescaling.sourceIndices_eq]
          exact index.2⟩
      invFun := fun index =>
        ⟨index.1, by
          change index.1 ∈
            wz2PaperFullFiberIndices fine coarse parent
          rw [← rescaling.sourceIndices_eq]
          exact index.2⟩
      left_inv := fun _ => by ext; rfl
      right_inv := fun _ => by ext; rfl
    }
  let indexEquiv :=
    fiberEnum.trans (sameIndices.trans rescaling.sourceEquiv.symm)
  refine
    {
      indexEquiv := indexEquiv
      tube_eq := ?_
    }
  intro index
  rw [fiber.tube_eq, rescaling.source_tube_eq]
  congr 2
  let member := sameIndices (fiberEnum index)
  have roundTrip :
      rescaling.sourceEquiv
          (rescaling.sourceEquiv.symm member) =
        member :=
    rescaling.sourceEquiv.apply_symm_apply member
  change (fiberEnum index).1 =
    (rescaling.sourceEquiv
      (rescaling.sourceEquiv.symm member)).1
  rw [roundTrip]
  rfl

end PureWZ2Prop62MetricFiberRescalingInput

namespace Prop62V4FinalFiberSameFamilyData

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
      Prop62V4FinalFiberSameFamilyData
        cover parent rescaling)

/-- Reindex the inherited rescaling witness onto the exact final full fiber. -/
noncomputable def publicReindex :
    PureWZ2Prop62PublicRescalingReindexData
      (wz2PaperFullFiberSubfamily fine coarse parent).family
      (coarse.tube parent) rescaling.rho_pos rescaling.rho_le_one
      (cover.fine_line_class.subfamily
        (wz2PaperFullFiberSubfamily fine coarse parent))
      (cover.coarse_line_class parent)
      (fun index => by
        rw [(wz2PaperFullFiberSubfamily
          fine coarse parent).tube_eq]
        exact
          (mem_wz2PaperFullFiberIndices_iff
            parent
            ((wz2PaperFullFiberSubfamily
              fine coarse parent).embedding index)).mp <|
            Finset.orderEmbOfFin_mem
              (wz2PaperFullFiberIndices fine coarse parent)
              rfl index)
      sourceConstant where
  ambientFine := fine
  ambientCoarse := coarse
  ambientCover := cover
  ambientParent := parent
  anchor_eq := rfl
  input := rescaling
  indexEquiv := sameFamily.indexEquiv
  tube_eq := sameFamily.tube_eq

end Prop62V4FinalFiberSameFamilyData

namespace PureWZ2CroppedCriticalNormalizationData

variable
    {sigma sourceLoss normalizationLoss delta rho structuralLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent)
    (selected :
      Kakeya.Streamlined.TubeSubfamily normalized.croppedFamily)
    (finalShading : WZ1PaperTubeShading selected.family)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (cover : PureWZ2Section6Cover selected.family coarse)
    (parent : Fin coarse.card)
    {sourceConstant : ENNReal}
    (rescaling :
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant)

/-- The canonical literal family on the exact final full fiber. -/
noncomputable def criticalFinalFiberLiteral :
    WZ2PaperLiteralUnitRescaledFamilyData
      (criticalFinalFiber
        (normalized := normalized) selected coarse parent).family
      (coarse.tube parent) rescaling.rho_pos :=
  wz2PaperLiteralOrdinaryRescaledFamilyLiteralData
    rescaling.rho_pos rescaling.rho_le_one
    (criticalFinalFiber
      (normalized := normalized) selected coarse parent).family
    (coarse.tube parent)
    (cover.fine_line_class.subfamily
      (criticalFinalFiber
        (normalized := normalized) selected coarse parent))
    (cover.coarse_line_class parent)
    (fun index => by
      rw [(criticalFinalFiber
        (normalized := normalized) selected coarse parent).tube_eq]
      exact
        (mem_wz2PaperFullFiberIndices_iff
          parent
          ((criticalFinalFiber
            (normalized := normalized) selected coarse parent).embedding index)).mp <|
          Finset.orderEmbOfFin_mem
            (wz2PaperFullFiberIndices selected.family coarse parent)
            rfl index)

/-- The canonical cubical literal shading of the exact final full fiber. -/
noncomputable def criticalFinalFiberLiteralShading :
    WZ2PaperLiteralUnitRescaledShadingData
      (normalized.criticalFinalFiberLiteral
        selected coarse cover parent rescaling)
      (criticalFinalFiberShading
        (normalized := normalized)
        selected finalShading coarse parent) :=
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
        (criticalFinalFiber
          (normalized := normalized) selected coarse parent))
      (cover.coarse_line_class parent)
      (fun index => by
        rw [(criticalFinalFiber
          (normalized := normalized) selected coarse parent).tube_eq]
        exact
          (mem_wz2PaperFullFiberIndices_iff
            parent
            ((criticalFinalFiber
              (normalized := normalized) selected coarse parent).embedding index)).mp <|
            Finset.orderEmbOfFin_mem
              (wz2PaperFullFiberIndices selected.family coarse parent)
              rfl index)
      (normalized.criticalFinalFiberLiteral
        selected coarse cover parent rescaling)
      (criticalFinalFiberShading
        (normalized := normalized)
        selected finalShading coarse parent)

/-- The exact rescaling certificate obtained by reindexing, not reselecting,
the metric-fiber witness stored by the four-degree output. -/
noncomputable def criticalFinalFiberRescalingCertificate :
    WZ2PaperAssouadToLiteralRescalingCertificate
      rescaling.rho_pos
      (WZ2PaperAssouadUnitRescalingData.ofTube
        (coarse.tube parent) rescaling.rho_pos)
      (normalized.criticalFinalFiberLiteral
        selected coarse cover parent rescaling)
      4000000 := by
  let sameFamily := rescaling.finalFiberSameFamily
  exact sameFamily.publicReindex.targetCertificate

/--
The public ordinary family obtained from the exact final complete fiber has
the standard quadratic body-mass upper bound.  The cardinality is unchanged:
the rescaling and public recentering only reindex the same exact fiber.
-/
theorem criticalFinalFiber_public_body_mass_upper
    (ratioLeOne : delta / rho ≤ 1) :
    (normalized.criticalFinalFiberRescalingCertificate
      selected coarse cover parent rescaling
      ).publicFamily.toBodyFamily.mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (delta / rho) 2 *
          (criticalFinalFiber
            (normalized := normalized) selected coarse parent
            ).family.enncard := by
  let fiber :=
    criticalFinalFiber
      (normalized := normalized) selected coarse parent
  let literal :=
    normalized.criticalFinalFiberLiteral
      selected coarse cover parent rescaling
  let certificate :=
    normalized.criticalFinalFiberRescalingCertificate
      selected coarse cover parent rescaling
  have targetCard :
      literal.targetFamily.enncard = fiber.family.enncard := by
    have cardEq :
        literal.targetFamily.card = fiber.family.card := by
      simpa using
        Fintype.card_congr <|
          Equiv.ofBijective
            literal.sourceIndex literal.sourceIndex_bijective
    exact congrArg (fun cardinality : ℕ => (cardinality : ENNReal)) cardEq
  have publicCard :
      certificate.publicFamily.enncard = fiber.family.enncard := by
    calc
      certificate.publicFamily.enncard =
          literal.targetFamily.enncard :=
        certificate.publicFamily_enncard_eq
      _ = fiber.family.enncard := targetCard
  have tubeVolumeUpper :
      Kakeya.deltaTubeVolume (delta / rho) ≤
        24 * Kakeya.realRpowENN (delta / rho) 2 *
          Kakeya.deltaTubeVolume 1 := by
    have fiberNonempty : fiber.family.Nonempty := by
      change
        0 <
          (wz2PaperFullFiberIndices
            selected.family coarse parent).card
      apply Finset.card_pos.mpr
      rcases cover.parent_hit parent with ⟨index, covered⟩
      exact
        ⟨index,
          (mem_wz2PaperFullFiberIndices_iff
            parent index).mpr covered⟩
    let index : Fin fiber.family.card := ⟨0, fiberNonempty⟩
    have upper :=
      tube_volume_scaling.2.2
        (delta / rho) (div_pos rescaling.delta_pos rescaling.rho_pos)
        ratioLeOne
        (certificate.publicFamily.tube
          (certificate.section6Index
            (literal.sourceIndex_bijective.surjective index).choose))
    rwa [tube_volume_scaling.1
      (delta / rho)
      (certificate.publicFamily.tube
        (certificate.section6Index
          (literal.sourceIndex_bijective.surjective index).choose))] at upper
  rw [tubeFamily_mass_eq_nominal]
  change
    certificate.publicFamily.enncard *
        Kakeya.deltaTubeVolume (delta / rho) ≤
      (55296 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN (delta / rho) 2 *
        fiber.family.enncard
  rw [publicCard]
  calc
    fiber.family.enncard * Kakeya.deltaTubeVolume (delta / rho) ≤
        fiber.family.enncard *
          (24 * Kakeya.realRpowENN (delta / rho) 2 *
            Kakeya.deltaTubeVolume 1) := by
      gcongr
    _ ≤
        fiber.family.enncard *
          (55296 * Kakeya.realRpowENN (delta / rho) 2 *
            Kakeya.deltaTubeVolume 1) := by
      gcongr
      norm_num
    _ =
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (delta / rho) 2 *
          fiber.family.enncard := by
      ring

/--
Minimal scalar premises for the non-circular final-fiber critical witness.

`cwa_absorption` weakens the CWA already stored by the rescaling input.
`trace_mass` is exactly the density inequality for the affine image of the
normalization trace; no final extremality conclusion occurs in either field.
-/
structure CriticalFinalFiberScalarInputs : Prop where
  cwa_absorption :
    (81000000 : ENNReal) * sourceConstant ≤
      Kakeya.realRpowENN (delta / rho) (-structuralLoss)
  trace_mass :
    Kakeya.realRpowENN (delta / rho) structuralLoss *
          (normalized.criticalFinalFiberRescalingCertificate
            selected coarse cover parent rescaling
            ).publicFamily.toBodyFamily.mass ≤
      (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / rho : ℝ) ^ 2)) *
        (criticalFinalFiberOrdinaryTrace
          (normalized := normalized)
          selected finalShading coarse parent).mass

/--
Build the two final-fiber scalar inputs from the exact packet-mass lower bound
and the synchronized normalization trace.  This is the complete quantitative
bridge; no density of the final ordinary trace is assumed.
-/
theorem criticalFinalFiberScalarInputs_of_packet_mass
    (hdelta : 0 < delta)
    (ratioLeOne : delta / rho ≤ 1)
    (finalCubical : WZ1PaperIsCubicalShading finalShading)
    (finalSubset :
      ∀ index,
        finalShading.carrier index ⊆
          normalized.croppedRefined.carrier
            (selected.embedding index))
    (packetDensity : ENNReal)
    (packetMassLower :
      packetDensity *
            (criticalFinalFiber
              (normalized := normalized) selected coarse parent
              ).family.enncard *
            Kakeya.realRpowENN delta 2 ≤
        (criticalFinalFiberShading
          (normalized := normalized)
          selected finalShading coarse parent).mass)
    (cwaAbsorption :
      (81000000 : ENNReal) * sourceConstant ≤
        Kakeya.realRpowENN (delta / rho) (-structuralLoss))
    (traceDensityAbsorption :
      Kakeya.realRpowENN (delta / rho) structuralLoss *
            (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          (100 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta sourceLoss / 2) *
          packetDensity) :
    normalized.CriticalFinalFiberScalarInputs
      (structuralLoss := structuralLoss)
      selected finalShading coarse cover parent rescaling := by
  refine
    {
      cwa_absorption := cwaAbsorption
      trace_mass := ?_
    }
  let fiber :=
    criticalFinalFiber
      (normalized := normalized) selected coarse parent
  let fiberInNormalized :=
    criticalFinalFiberInNormalized
      (normalized := normalized) selected coarse parent
  let fiberShading :=
    criticalFinalFiberShading
      (normalized := normalized)
      selected finalShading coarse parent
  let ordinaryTrace :=
    criticalFinalFiberOrdinaryTrace
      (normalized := normalized)
      selected finalShading coarse parent
  let certificate :=
    normalized.criticalFinalFiberRescalingCertificate
      selected coarse cover parent rescaling
  have bodyMassUpper :
      certificate.publicFamily.toBodyFamily.mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (delta / rho) 2 *
          fiber.family.enncard := by
    exact
      normalized.criticalFinalFiber_public_body_mass_upper
        selected coarse cover parent rescaling ratioLeOne
  have scaleIdentity :
      ENNReal.ofReal ((1 / rho : ℝ) ^ 2) *
          Kakeya.realRpowENN delta 2 =
        Kakeya.realRpowENN (delta / rho) 2 := by
    simp only [Kakeya.realRpowENN]
    have deltaTwo : Real.rpow delta 2 = delta ^ 2 :=
      Real.rpow_two delta
    have ratioTwo :
        Real.rpow (delta / rho) 2 =
          (delta / rho) ^ 2 :=
      Real.rpow_two (delta / rho)
    rw [deltaTwo, ratioTwo]
    rw [← ENNReal.ofReal_mul (sq_nonneg (1 / rho))]
    congr 1
    field_simp [rescaling.rho_pos.ne']
  have fiberCubical : WZ1PaperIsCubicalShading fiberShading := by
    exact
      restrictPaperShading_cubical fiber finalCubical
  have fiberSubset :
      ∀ index,
        fiberShading.carrier index ⊆
          normalized.croppedRefined.carrier
            (fiberInNormalized.embedding index) := by
    intro index
    exact finalSubset (fiber.embedding index)
  have traceLower :
      (100 : ENNReal)⁻¹ *
            (Kakeya.realRpowENN delta sourceLoss / 2) *
            fiberShading.mass ≤
        ordinaryTrace.mass := by
    exact
      normalized.finalOrdinaryTrace_mass_lower_normalized
        fiberInNormalized fiberShading hdelta fiberCubical fiberSubset
  calc
    Kakeya.realRpowENN (delta / rho) structuralLoss *
          certificate.publicFamily.toBodyFamily.mass ≤
        Kakeya.realRpowENN (delta / rho) structuralLoss *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN (delta / rho) 2 *
            fiber.family.enncard) := by
      gcongr
    _ =
        (Kakeya.realRpowENN (delta / rho) structuralLoss *
          (55296 * Kakeya.deltaTubeVolume 1)) *
          (Kakeya.realRpowENN (delta / rho) 2 *
            fiber.family.enncard) := by
      ring
    _ ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          (100 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta sourceLoss / 2) *
          packetDensity) *
          (Kakeya.realRpowENN (delta / rho) 2 *
            fiber.family.enncard) := by
      gcongr
    _ =
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / rho : ℝ) ^ 2)) *
          ((100 : ENNReal)⁻¹ *
            (Kakeya.realRpowENN delta sourceLoss / 2) *
            (packetDensity * fiber.family.enncard *
              Kakeya.realRpowENN delta 2)) := by
      rw [← scaleIdentity]
      ring
    _ ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / rho : ℝ) ^ 2)) *
          ((100 : ENNReal)⁻¹ *
            (Kakeya.realRpowENN delta sourceLoss / 2) *
            fiberShading.mass) := by
      gcongr
    _ ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / rho : ℝ) ^ 2)) *
          ordinaryTrace.mass := by
      gcongr

/--
Construct the exact final-fiber critical-floor witness directly from the
normalization trace and the inherited rescaling provenance.

This is deliberately weaker than a completed rescaled extremal output and
therefore cannot be circularly justified by the final fiber conclusion.
-/
noncomputable def criticalFinalFiberFloorWitness
    (scalar :
      normalized.CriticalFinalFiberScalarInputs
        (structuralLoss := structuralLoss)
        selected finalShading coarse cover parent rescaling) :
    PureWZ2Prop62CriticalRescaledFiberFloorWitness
      (loss := structuralLoss)
      (criticalFinalFiberShading
        (normalized := normalized)
        selected finalShading coarse parent)
      (coarse.tube parent) rescaling.rho_pos := by
  let sameFamily := rescaling.finalFiberSameFamily
  let publicReindex := sameFamily.publicReindex
  let certificate :=
    normalized.criticalFinalFiberRescalingCertificate
      selected coarse cover parent rescaling
  let ordinaryTrace :=
    criticalFinalFiberOrdinaryTrace
      (normalized := normalized)
      selected finalShading coarse parent
  let literalShading :=
    normalized.criticalFinalFiberLiteralShading
      selected finalShading coarse cover parent rescaling
  have publicCWA :
      WZ2PaperPureCWAAtNearbyScales certificate.publicFamily
        (Kakeya.realRpowENN (delta / rho) (-structuralLoss)) := by
    have inherited := publicReindex.publicPureCWA
    exact inherited.mono scalar.cwa_absorption
      (by simp [Kakeya.realRpowENN])
  have ordinaryDense :
      (certificate.literalExactImageShading ordinaryTrace).IsLambdaDense
        (Kakeya.realRpowENN (delta / rho) structuralLoss) :=
    certificate.literalExactImageShading_dense_of_mass
      ordinaryTrace scalar.trace_mass
  exact
    {
      familyData :=
        normalized.criticalFinalFiberLiteral
          selected coarse cover parent rescaling
      literalShading := literalShading
      ordinaryFamily := certificate.publicFamily
      ordinaryShading :=
        certificate.literalExactImageShading ordinaryTrace
      ordinary_nonempty := by
        apply certificate.publicFamily_nonempty
        let fiber :=
          criticalFinalFiber
            (normalized := normalized) selected coarse parent
        have fiberNonempty : fiber.family.Nonempty := by
          change
            0 <
              (wz2PaperFullFiberIndices
                selected.family coarse parent).card
          apply Finset.card_pos.mpr
          rcases cover.parent_hit parent with
            ⟨index, covered⟩
          exact
            ⟨index,
              (mem_wz2PaperFullFiberIndices_iff
                parent index).mpr covered⟩
        have cardEq :
            (criticalFinalFiberLiteral
              (normalized := normalized)
              selected coarse cover parent rescaling).targetFamily.card =
              fiber.family.card := by
          simpa using
            Fintype.card_congr <|
              Equiv.ofBijective
                (criticalFinalFiberLiteral
                  (normalized := normalized)
                  selected coarse cover parent rescaling).sourceIndex
                (criticalFinalFiberLiteral
                  (normalized := normalized)
                  selected coarse cover parent rescaling
                  ).sourceIndex_bijective
        change
          0 <
            (criticalFinalFiberLiteral
              (normalized := normalized)
              selected coarse cover parent rescaling).targetFamily.card
        rw [cardEq]
        exact fiberNonempty
      ordinary_cwa := publicCWA
      ordinary_dense := ordinaryDense
      ordinary_union_subset_target :=
        certificate.literalExactImageShading_union_subset
          ordinaryTrace
          (criticalFinalFiberShading
            (normalized := normalized)
            selected finalShading coarse parent)
          (criticalFinalFiberOrdinaryTrace_subset
            (normalized := normalized)
            selected finalShading coarse parent)
          literalShading
    }

end PureWZ2CroppedCriticalNormalizationData

namespace Prop62PaperAudit.V4.Prop62V4RichCertificateCompanionData

variable
    {delta sigma sourceLoss normalizationLoss structuralLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent}
    {rho : WZ2PaperRequestedScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {metricCertificate :
      PureWZ2Prop62MetricParentsV4Certificate
        normalized.croppedRefined rho fineParentDistanceConstant
          parentConstant fiberConstant}
    {eta : ℝ}
    {packetDensityExponent cwaLossExponent polylogExponent : ℕ}
    (rich :
      Prop62PaperAudit.V4.Prop62V4RichCertificateCompanionData
        (eta := eta)
        (packetDensityExponent := packetDensityExponent)
        (cwaLossExponent := cwaLossExponent)
        (polylogExponent := polylogExponent)
        normalized.final_extremal.delta_pos
        (Prop62PaperAudit.V4.prop62V4MetricCompanionOfCertificate
          normalized metricCertificate))

/--
The direct rich-companion specialization.  The family, shading, cover, and
rescaling input are exactly the fields of `rich.outputCertificate`; only the
two scalar inequalities remain for the caller.
-/
noncomputable def finalFiberCriticalWitness
    (parent : Fin rich.outputCertificate.coarse.family.card)
    (scalar :
      normalized.CriticalFinalFiberScalarInputs
        (structuralLoss := structuralLoss)
        rich.composedSelected rich.composedShading
        rich.outputCertificate.coarse.family
        rich.outputCertificate.cover parent
        (rich.outputCertificate.rescaled_fiber_input parent)) :
    PureWZ2Prop62CriticalRescaledFiberFloorWitness
      (loss := structuralLoss)
      (restrictPaperShading
        (wz2PaperFullFiberSubfamily
          rich.outputCertificate.refinement.selected.family
          rich.outputCertificate.coarse.family parent)
        rich.outputCertificate.refinement.refined)
      (rich.outputCertificate.coarse.family.tube parent)
      (rich.outputCertificate.rescaled_fiber_input parent).rho_pos :=
  normalized.criticalFinalFiberFloorWitness
    rich.composedSelected rich.composedShading
    rich.outputCertificate.coarse.family
    rich.outputCertificate.cover parent
    (rich.outputCertificate.rescaled_fiber_input parent)
    scalar

/-- Parentwise packaging in exactly the shape consumed by the critical
multiplicity input record. -/
theorem finalFiberCriticalWitnesses
    (scalar :
      ∀ parent : Fin rich.outputCertificate.coarse.family.card,
        normalized.CriticalFinalFiberScalarInputs
          (structuralLoss := structuralLoss)
          rich.composedSelected rich.composedShading
          rich.outputCertificate.coarse.family
          rich.outputCertificate.cover parent
          (rich.outputCertificate.rescaled_fiber_input parent)) :
    ∀ parent : Fin rich.outputCertificate.coarse.family.card,
      Nonempty
        (PureWZ2Prop62CriticalRescaledFiberFloorWitness
          (loss := structuralLoss)
          (restrictPaperShading
            (wz2PaperFullFiberSubfamily
              rich.outputCertificate.refinement.selected.family
              rich.outputCertificate.coarse.family parent)
            rich.outputCertificate.refinement.refined)
          (rich.outputCertificate.coarse.family.tube parent)
          (rich.outputCertificate.rescaled_fiber_input parent).rho_pos) :=
  fun parent =>
    ⟨rich.finalFiberCriticalWitness parent (scalar parent)⟩

end Prop62PaperAudit.V4.Prop62V4RichCertificateCompanionData

namespace Prop62PaperAudit.V4.Prop62V4RichCertificateCompanionData

variable
    {delta sigma sourceLoss normalizationLoss structuralLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent}
    {rho : WZ2PaperRequestedScale delta}
    {hdelta : 0 < delta}
    {preparation :
      Prop62PaperAudit.V4.FixedGridPreparationData
        (rho := rho.1) normalized.croppedRefined hdelta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {metricCertificate :
      PureWZ2Prop62MetricParentsV4Certificate
        preparation.cleanup.refined rho fineParentDistanceConstant
          parentConstant fiberConstant}
    {eta : ℝ}
    {packetDensityExponent cwaLossExponent polylogExponent : ℕ}
    (rich :
      Prop62PaperAudit.V4.Prop62V4RichCertificateCompanionData
        (eta := eta)
        (packetDensityExponent := packetDensityExponent)
        (cwaLossExponent := cwaLossExponent)
        (polylogExponent := polylogExponent)
        hdelta
        (Prop62PaperAudit.V4.prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate))

/--
The fixed-grid rich-companion specialization used by the current V4 route.
The exact `1 + 10 + 50` selected family, final shading, final parent, cover,
and stored rescaling input are passed unchanged to the generic constructor.
-/
noncomputable def fixedGridFinalFiberCriticalWitness
    (parent : Fin rich.outputCertificate.coarse.family.card)
    (scalar :
      PureWZ2CroppedCriticalNormalizationData.CriticalFinalFiberScalarInputs
        (structuralLoss := structuralLoss)
        normalized
        rich.fixedGridComposedSelected rich.fixedGridComposedShading
        rich.outputCertificate.coarse.family
        rich.outputCertificate.cover parent
        (rich.outputCertificate.rescaled_fiber_input parent)) :
    PureWZ2Prop62CriticalRescaledFiberFloorWitness
      (loss := structuralLoss)
      (restrictPaperShading
        (wz2PaperFullFiberSubfamily
          rich.outputCertificate.refinement.selected.family
          rich.outputCertificate.coarse.family parent)
        rich.outputCertificate.refinement.refined)
      (rich.outputCertificate.coarse.family.tube parent)
      (rich.outputCertificate.rescaled_fiber_input parent).rho_pos :=
  normalized.criticalFinalFiberFloorWitness
    rich.fixedGridComposedSelected rich.fixedGridComposedShading
    rich.outputCertificate.coarse.family
    rich.outputCertificate.cover parent
    (rich.outputCertificate.rescaled_fiber_input parent)
    scalar

/-- Parentwise fixed-grid packaging in the exact shape consumed by the
critical multiplicity input record. -/
theorem fixedGridFinalFiberCriticalWitnesses
    (scalar :
      ∀ parent : Fin rich.outputCertificate.coarse.family.card,
        PureWZ2CroppedCriticalNormalizationData.CriticalFinalFiberScalarInputs
          (structuralLoss := structuralLoss)
          normalized
          rich.fixedGridComposedSelected rich.fixedGridComposedShading
          rich.outputCertificate.coarse.family
          rich.outputCertificate.cover parent
          (rich.outputCertificate.rescaled_fiber_input parent)) :
    ∀ parent : Fin rich.outputCertificate.coarse.family.card,
      Nonempty
        (PureWZ2Prop62CriticalRescaledFiberFloorWitness
          (loss := structuralLoss)
          (restrictPaperShading
            (wz2PaperFullFiberSubfamily
              rich.outputCertificate.refinement.selected.family
              rich.outputCertificate.coarse.family parent)
            rich.outputCertificate.refinement.refined)
          (rich.outputCertificate.coarse.family.tube parent)
          (rich.outputCertificate.rescaled_fiber_input parent).rho_pos) :=
  fun parent =>
    ⟨rich.fixedGridFinalFiberCriticalWitness parent (scalar parent)⟩

namespace FixedGridPureScalar

variable
    {cwaPower : ℕ}
    {sigma outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss}
    (scalar :
      Prop62V4PureScalarInputs
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss routing)
    (deltaLe : delta ≤ scalar.delta₀)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho.1)
    (sourceLoss_le :
      sourceLoss ≤ routing.numerics.hierarchy.sourceLoss)
    (eta_eq : eta = routing.numerics.hierarchy.stableLoss)

include eta_eq

/--
The exact packet-density ledger on one final complete fiber, in the form
needed by the normalization-trace bridge.
-/
theorem packet_mass_lower
    (parent : Fin rich.outputCertificate.coarse.family.card) :
    ((2 : ENNReal)⁻¹ *
          Kakeya.realRpowENN delta
            ((packetDensityExponent : ℝ) *
              routing.numerics.hierarchy.stableLoss)) *
          (PureWZ2CroppedCriticalNormalizationData.criticalFinalFiber
            (normalized := normalized)
            rich.fixedGridComposedSelected
            rich.outputCertificate.coarse.family parent).family.enncard *
          Kakeya.realRpowENN delta 2 ≤
      (PureWZ2CroppedCriticalNormalizationData.criticalFinalFiberShading
        (normalized := normalized)
        rich.fixedGridComposedSelected rich.fixedGridComposedShading
        rich.outputCertificate.coarse.family parent).mass := by
  have exactFiberCardUpper :
      (PureWZ2CroppedCriticalNormalizationData.criticalFinalFiber
        (normalized := normalized)
        rich.fixedGridComposedSelected
        rich.outputCertificate.coarse.family parent).family.enncard ≤
        (2 * rich.outputCertificate.fiberFloor : ℕ) := by
    change
      (wz2PaperFullFiberCount
        rich.outputCertificate.refinement.selected.family
        rich.outputCertificate.coarse.family parent : ENNReal) ≤
          (2 * rich.outputCertificate.fiberFloor : ℕ)
    exact_mod_cast
      (rich.outputCertificate.fiber_cardinality parent).2.le
  calc
    ((2 : ENNReal)⁻¹ *
          Kakeya.realRpowENN delta
            ((packetDensityExponent : ℝ) *
              routing.numerics.hierarchy.stableLoss)) *
          (PureWZ2CroppedCriticalNormalizationData.criticalFinalFiber
            (normalized := normalized)
            rich.fixedGridComposedSelected
            rich.outputCertificate.coarse.family parent).family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        ((2 : ENNReal)⁻¹ *
          Kakeya.realRpowENN delta
            ((packetDensityExponent : ℝ) *
              routing.numerics.hierarchy.stableLoss)) *
          (2 * rich.outputCertificate.fiberFloor : ℕ) *
          Kakeya.realRpowENN delta 2 := by
      gcongr
    _ =
        Kakeya.realRpowENN delta
            ((packetDensityExponent : ℝ) *
              routing.numerics.hierarchy.stableLoss) *
          (rich.outputCertificate.fiberFloor : ENNReal) *
          Kakeya.realRpowENN delta 2 := by
      calc
        _ =
            ((2 : ENNReal)⁻¹ * 2) *
              (Kakeya.realRpowENN delta
                  ((packetDensityExponent : ℝ) *
                    routing.numerics.hierarchy.stableLoss) *
                (rich.outputCertificate.fiberFloor : ENNReal) *
                Kakeya.realRpowENN delta 2) := by
          simp only [Nat.cast_mul]
          norm_num only [Nat.cast_ofNat]
          ac_rfl
        _ = _ := by
          rw [ENNReal.inv_mul_cancel] <;> norm_num
    _ ≤
        (restrictPaperShading
          (wz2PaperFullFiberSubfamily
            rich.outputCertificate.refinement.selected.family
            rich.outputCertificate.coarse.family parent)
          rich.outputCertificate.refinement.refined).mass := by
      simpa [eta_eq] using rich.outputCertificate.packet_density parent

include scalar deltaLe rhoLower sourceLoss_le

/--
All scalar premises for the exact final-fiber critical witness are automatic
at the common V4 threshold.
-/
theorem critical_inputs
    (parent : Fin rich.outputCertificate.coarse.family.card) :
    PureWZ2CroppedCriticalNormalizationData.CriticalFinalFiberScalarInputs
      (structuralLoss := routing.critical.structuralLoss)
      normalized
      rich.fixedGridComposedSelected rich.fixedGridComposedShading
      rich.outputCertificate.coarse.family
      rich.outputCertificate.cover parent
      (rich.outputCertificate.rescaled_fiber_input parent) := by
  have ratioLeOne : delta / rho.1 ≤ 1 :=
    (scalar.ratio_small hdelta deltaLe
      metricCertificate.rho_pos rhoLower).trans (by norm_num)
  have cwaAbsorption :
      (81000000 : ENNReal) * (fiberConstant / 81000000) ≤
        Kakeya.realRpowENN (delta / rho.1)
          (-routing.critical.structuralLoss) := by
    calc
      (81000000 : ENNReal) * (fiberConstant / 81000000) ≤
          fiberConstant :=
        (ENNReal.mul_div_cancel (by norm_num) (by norm_num)).le
      _ ≤
          Kakeya.realRpowENN delta
            (-(cwaLossExponent : ℝ) *
              routing.numerics.hierarchy.stableLoss) :=
        by simpa [eta_eq] using
          rich.fourDegree.receipt.fiberConstant_le
      _ ≤
          Kakeya.realRpowENN (delta / rho.1)
            (-routing.critical.structuralLoss) :=
        scalar.fiber_cwa hdelta deltaLe
          metricCertificate.rho_pos rhoLower
  exact
    normalized.criticalFinalFiberScalarInputs_of_packet_mass
      rich.fixedGridComposedSelected rich.fixedGridComposedShading
      rich.outputCertificate.coarse.family
      rich.outputCertificate.cover parent
      (rich.outputCertificate.rescaled_fiber_input parent)
      hdelta ratioLeOne rich.fixedGridComposed_cubical
      rich.fixedGridComposed_subshading
      ((2 : ENNReal)⁻¹ *
        Kakeya.realRpowENN delta
          ((packetDensityExponent : ℝ) *
            routing.numerics.hierarchy.stableLoss))
      (packet_mass_lower rich eta_eq parent)
      cwaAbsorption
      (by
        have hierarchyTrace :=
          scalar.fiber_trace_density hdelta deltaLe
            metricCertificate.rho_pos rhoLower
        have deltaLeOne : delta ≤ 1 :=
          deltaLe.trans <|
            scalar.delta₀_le_one_hundred.trans (by norm_num)
        have sourcePowerLe :
            Kakeya.realRpowENN delta
                routing.numerics.hierarchy.sourceLoss ≤
              Kakeya.realRpowENN delta sourceLoss :=
          pure_wz2_rpowENN_antitone
            hdelta deltaLeOne sourceLoss_le
        calc
          Kakeya.realRpowENN (delta / rho.1)
                routing.critical.structuralLoss *
              (55296 * Kakeya.deltaTubeVolume 1) ≤
              ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
                (100 : ENNReal)⁻¹ *
                (Kakeya.realRpowENN delta
                    routing.numerics.hierarchy.sourceLoss / 2) *
                ((2 : ENNReal)⁻¹ *
                  Kakeya.realRpowENN delta
                    ((packetDensityExponent : ℝ) *
                      routing.numerics.hierarchy.stableLoss)) :=
            hierarchyTrace
          _ ≤
              ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
                (100 : ENNReal)⁻¹ *
                (Kakeya.realRpowENN delta sourceLoss / 2) *
                ((2 : ENNReal)⁻¹ *
                  Kakeya.realRpowENN delta
                    ((packetDensityExponent : ℝ) *
                      routing.numerics.hierarchy.stableLoss)) := by
            gcongr)

/-- The exact final complete fibers now carry pure critical-floor witnesses
without any caller-supplied geometric hypothesis. -/
theorem critical_witnesses :
    ∀ parent : Fin rich.outputCertificate.coarse.family.card,
      Nonempty
        (PureWZ2Prop62CriticalRescaledFiberFloorWitness
          (loss := routing.critical.structuralLoss)
          (restrictPaperShading
            (wz2PaperFullFiberSubfamily
              rich.outputCertificate.refinement.selected.family
              rich.outputCertificate.coarse.family parent)
            rich.outputCertificate.refinement.refined)
          (rich.outputCertificate.coarse.family.tube parent)
          (rich.outputCertificate.rescaled_fiber_input parent).rho_pos) :=
  rich.fixedGridFinalFiberCriticalWitnesses fun parent =>
    critical_inputs rich scalar deltaLe rhoLower sourceLoss_le eta_eq parent

end FixedGridPureScalar

end Prop62PaperAudit.V4.Prop62V4RichCertificateCompanionData

end Kakeya.Assouad

end
