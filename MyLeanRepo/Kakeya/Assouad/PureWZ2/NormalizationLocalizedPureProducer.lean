import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationSourceDerivedProducer

/-!
# Localized pure producer for cropped critical normalization

The literal Definition 2.12 witness at one requested scale supplies an actual
nearby scale, complete strict fibers, and actual outer-John body CWA on each
fiber.  The centered/full-fiber machinery transports that one body CWA to a
common centered chart.  It does not by itself make the centered fiber an
all-scale `WZ2PaperPureIsExtremal` configuration.

The missing step is simultaneous localization and schedule regularization:
one must retain a localized subfamily and subshading while recovering
`WZ2PaperPureCWAAtNearbyScales` for every requested scale.  Moreover, the
historical nearby top-level theorem has the older line-class nearby API as
input.  In that older API the actual top-scale witness still satisfies
`rho ≤ 1`, so requesting scale `1` forces `rho = 1`.  Literal
`WZ2PaperPureNearbyScaleCoverData` deliberately has no type-level
`rho ≤ 1`; its actual witness for requested scale `1` may be larger than
`1`.  Consequently the literal pure nearby field does not currently imply
`WZ2PaperConvexWolffBound`.

This module records the thinnest conditional producer at that boundary.
It takes normalization exponent zero and uses the identity selection and
identity rigid frame.  Thus its only new input is a localized genuine pure
extremizer already in the fixed line class, together with the top-level CWA
on that same family.  The all-scale cropped pure CWA is then obtained by loss
weakening from `localized.extremal`; it is not replaced by a one-layer body
CWA.

The canonical cropped density and volume remain outside this module, in the
scalar producer.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Every pure extremal source supplies the literal actual-nearby witness at one
requested scale, and every parent of that witness has a nonempty complete
strict fiber.

This is the exact one-layer endpoint before all-scale-preserving
localization: after selecting or recentering one such fiber, Definition 2.12
does not automatically supply nearby witnesses for the new family at the
other requested scales.
-/
theorem PureWZ2ExtremalConfiguration.literalActualNearby_completeFibers
    {sigma loss delta : ℝ}
    (source : PureWZ2ExtremalConfiguration sigma loss delta)
    (requested : WZ2PaperRequestedScale delta) :
    ∃ nearby :
        WZ2PaperPureNearbyScaleCoverData
          source.family requested
          (Kakeya.realRpowENN delta (-loss)),
      ∀ parent : Fin nearby.scaleData.coarse.card,
        (wz2PaperOrdinaryFullFiberIndices
          source.family nearby.scaleData.coarse parent).Nonempty := by
  rcases
      source.extremal.cwa_nearby_scales.2.2.2 requested
    with
    ⟨nearby⟩
  refine ⟨nearby, ?_⟩
  exact
    nearby.scaleData.cover.fullFiber_nonempty_of_uniform
      source.extremal.nonempty
      nearby.scaleData.full_fiber_uniform

/--
The exact residual output of all-scale-preserving localization.

The type of `localized` already requires `WZ2PaperPureIsExtremal`; hence its
`cwa_nearby_scales` field quantifies over every requested scale.  The
additional fields record the geometric, density, and top-level CWA facts not
encoded by pure extremality.
-/
structure PureWZ2LocalizedAllScaleInput
    {sigma sourceLoss inputLoss outputLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta) : Prop where
  output_loss_pos : 0 < outputLoss
  line_class : WZ1PaperIsLineClass localized.family
  top_level_cwa :
    WZ2PaperConvexWolffBound
      localized.family
      (Kakeya.realRpowENN delta (-outputLoss))
  ordinary_cell_containment :
    ∀ index (cell : ℤ × ℤ × ℤ),
      (localized.shading.carrier index ∩
          wz1PaperGridCube delta cell).Nonempty →
        wz1PaperGridCube delta cell ⊆
          wz1PaperTubeCarrier (localized.family.tube index)
  ordinary_per_tube :
    ∀ index,
      (Kakeya.realRpowENN delta inputLoss / 2) *
            MeasureTheory.volume
              (localized.family.tube index).carrier ≤
        MeasureTheory.volume (localized.shading.carrier index)
  ordinary_axial_window :
    ∀ index point,
      point ∈
          (AffineIsometryEquiv.refl ℝ Point3) ''
            localized.shading.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8
  ordinary_bounded_base :
    HasBoundedBase localized.family 4

namespace PureWZ2LocalizedAllScaleInput

variable
    {sigma sourceLoss inputLoss outputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}

/--
All structural normalization fields follow from the residual input at
normalization exponent zero.

The ordinary selection is the whole localized family, the rigid frame is the
identity, and the cropped family is the same indexed family.  In particular,
the frame is common to every tube and the fixed line-class field is preserved
literally.
-/
noncomputable def toSourceDerivedStructuralData
    (data :
      PureWZ2LocalizedAllScaleInput
        (outputLoss := outputLoss)
        source localized)
    (inputLossLe : inputLoss ≤ outputLoss / 2) :
    PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralData
      (outputLoss := outputLoss)
      source localized 0 := by
  let selected : Kakeya.Streamlined.TubeSubfamily localized.family :=
    {
      family := localized.family
      embedding := Equiv.toEmbedding (Equiv.refl _)
      tube_eq := fun _ => rfl
    }
  refine
    {
      input_loss_le_half := inputLossLe
      selected := selected
      selected_nonempty := ?_
      ordinaryRefined := localized.shading
      ordinary_subshading := ?_
      retained_mass := ?_
      frame := AffineIsometryEquiv.refl ℝ Point3
      croppedFamily := localized.family
      indexEquiv := Equiv.refl _
      ordinary_carrier_image_eq := ?_
      ordinary_per_tube := by
        intro index
        simpa [selected] using data.ordinary_per_tube index
      ordinary_axial_window := by
        intro index point pointMem
        simpa [selected] using
          data.ordinary_axial_window index point pointMem
      line_class := data.line_class
      cropped_pure_cwa := ?_
      cropped_top_level_cwa := data.top_level_cwa
      ordinary_cell_containment := ?_
      ordinary_bounded_base := data.ordinary_bounded_base
    }
  · simpa [selected] using localized.extremal.nonempty
  · intro index
    simpa [selected]
  · simp [wz2PaperPureRefinementFraction]
  · intro index
    simp [selected]
  · exact
      localized.extremal.cwa_nearby_scales.mono_loss
        localized.extremal.delta_pos
        localized.extremal.delta_le_one
        (by linarith [data.output_loss_pos])
  · intro index cell cellMeets
    rcases cellMeets with ⟨point, pointSource, pointCell⟩
    rcases pointSource with ⟨sourcePoint, sourcePointMem, sourcePointEq⟩
    have sourcePointEq' : sourcePoint = point := by
      simpa using sourcePointEq
    subst sourcePoint
    simpa using
      data.ordinary_cell_containment index cell
        ⟨point, sourcePointMem, pointCell⟩

end PureWZ2LocalizedAllScaleInput

/--
Quantifier-correct producer for the genuinely missing localized pure input.

The threshold is fixed before the source extremizer.  A proof may choose a
literal actual-nearby witness from `source.extremal.cwa_nearby_scales`, retain
complete strict fibers, use the centered/full-fiber machinery, and run the
finite schedule regularizer.  Its output must nevertheless be the all-scale
record above.  The one actual witness and its centered body CWA close only one
schedule layer; they do not supply the `∀ requested` field of
`localized.extremal.cwa_nearby_scales`.
-/
def PureWZ2LocalizedAllScaleProducer : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < outputLoss →
      ∃ sourceLoss inputLoss delta₁ : ℝ,
        0 < sourceLoss ∧
        0 < inputLoss ∧
        inputLoss ≤ outputLoss / 2 ∧
        0 < delta₁ ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₁ →
          ∀ source :
              PureWZ2ExtremalConfiguration
                sigma sourceLoss delta,
            ∃ localized :
                PureWZ2ExtremalConfiguration
                  sigma inputLoss delta,
              Nonempty
                (PureWZ2LocalizedAllScaleInput
                  (outputLoss := outputLoss)
                  source localized)

/--
The localized all-scale producer closes the structural producer required by
the existing source-derived normalization split, with exponent zero.
-/
theorem
    pureWZ2_cropped_critical_normalization_sourceDerivedStructural_of_localizedPure
    (localizedPure :
      PureWZ2LocalizedAllScaleProducer) :
    PureWZ2CroppedCriticalNormalizationSourceDerivedStructuralProducerAt
      0 := by
  intro sigma outputLoss outputLossPos
  rcases localizedPure sigma outputLoss outputLossPos with
    ⟨sourceLoss, inputLoss, delta₁,
      sourceLossPos, inputLossPos, inputLossLe,
      delta₁Pos, produce⟩
  refine
    ⟨sourceLoss, inputLoss, delta₁,
      sourceLossPos, inputLossPos, inputLossLe,
      delta₁Pos, ?_⟩
  intro delta deltaPos deltaLe source
  rcases produce delta deltaPos deltaLe source with
    ⟨localized, ⟨data⟩⟩
  exact
    ⟨localized,
      ⟨data.toSourceDerivedStructuralData inputLossLe⟩⟩

/--
Combining the localized all-scale producer with the existing canonical
cropped scalar producer closes the frozen normalization theorem.
-/
theorem pureWZ2_cropped_critical_normalization_of_localizedPureProducer
    (localizedPure :
      PureWZ2LocalizedAllScaleProducer)
    (canonicalScalars :
      PureWZ2CroppedCriticalNormalizationCanonicalScalarsProducerAt
        0) :
    PureWZ2CroppedCriticalNormalizationAt 0 :=
  pureWZ2_cropped_critical_normalization_of_sourceDerivedProducers
    0
    (pureWZ2_cropped_critical_normalization_sourceDerivedStructural_of_localizedPure
      localizedPure)
    canonicalScalars

end Kakeya.Assouad

end
