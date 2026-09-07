import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CroppedExtremal
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CoverSynchronization
import MyLeanRepo.Kakeya.Assouad.PropStickyStatements

/-!
# Synchronized public and internal Section 6 structure

The existing Section 6 proof body may continue to consume the historical
line-distance certificate.  This package requires the same family and shading
to carry the public pure Definition 2.12 extremality simultaneously.
-/

noncomputable section

namespace Kakeya.Assouad

/--
One extremal configuration with both the public pure structural semantics and
the internal WZ line-cover certificate.
-/
structure WZ2PaperSection6InternalExtremal
    {delta : ℝ}
    (sigma loss : ℝ)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading family) : Prop where
  paperData : WZ2PaperCroppedIsExtremal sigma loss family shading
  internalData : WZ2PaperIsExtremal sigma loss family shading

/--
The stronger exact-scale source certificate used by the existing preparation
mainline, synchronized with the public pure nearby-scale hypothesis.
-/
structure WZ2PaperSection6ExactSource
    {delta : ℝ}
    (sigma loss : ℝ)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading family) : Prop where
  public_cwa :
    WZ2PaperPureCWAAtNearbyScales family
      (Kakeya.realRpowENN delta (-loss))
  internalData :
    WZ2PaperExactScaleExtremal sigma loss family shading
  exactScaleSynchronization :
    ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
      let scaleData :=
        Classical.choice
          (internalData.cwa_exact_scales.2.2.2 rho)
      WZ2PaperPureInternalCoverSynchronization
        family scaleData.coarse scaleData.cover

namespace WZ2PaperSection6InternalExtremal

/-- Forget the internal certificate and expose the public extremal pair. -/
theorem toPublic
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data :
      WZ2PaperSection6InternalExtremal
        sigma loss family shading) :
    WZ2PaperCroppedIsExtremal sigma loss family shading :=
  data.paperData

/-- Existing Section 6 code consumes only this projection. -/
theorem toInternal
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data :
      WZ2PaperSection6InternalExtremal
        sigma loss family shading) :
    WZ2PaperIsExtremal sigma loss family shading :=
  data.internalData

end WZ2PaperSection6InternalExtremal

namespace WZ2PaperSection6ExactSource

/-- Existing preparation modules consume only the historical exact source. -/
theorem toInternal
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data :
      WZ2PaperSection6ExactSource
        sigma loss family shading) :
    WZ2PaperExactScaleExtremal sigma loss family shading :=
  data.internalData

/-- The exact-scale cover selected by the historical preparation code. -/
noncomputable def canonicalScaleData
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data :
      WZ2PaperSection6ExactSource
        sigma loss family shading)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) :
    WZ2PaperScaleCoverData family rho
      (Kakeya.realRpowENN delta (-loss)) :=
  Classical.choice
    (data.internalData.cwa_exact_scales.2.2.2 rho)

/-- The canonical exact-scale choice carries public/internal provenance. -/
theorem canonicalScaleSynchronization
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data :
      WZ2PaperSection6ExactSource
        sigma loss family shading)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) :
    WZ2PaperPureInternalCoverSynchronization
      family (data.canonicalScaleData rho).coarse
      (data.canonicalScaleData rho).cover := by
  simpa [canonicalScaleData] using
    data.exactScaleSynchronization rho

/-- Restrict one explicitly synchronized exact-scale witness to a selected
fine family and its hit parents. -/
noncomputable def restrictExactScaleToHitParents
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data :
      WZ2PaperSection6ExactSource
        sigma loss family shading)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    WZ2PaperPureInternalCoverSynchronization
      selected.family
      ((data.canonicalScaleData rho).cover.hitParentSubfamily selected).family
      ((data.canonicalScaleData rho).cover.restrictToHitParents selected) :=
  (data.canonicalScaleSynchronization rho).restrictToHitParents
    (data.internalData.delta_pos.le.trans rho.2.1) selected

end WZ2PaperSection6ExactSource

/--
The model-conversion and strictification theorem needed to enter the existing
Section 6 mainline from public pure data.

The output may refine and cubicalize the shading, but must retain its public
pure CWA and provide the historical exact line certificate only as an internal
proof device.
-/
def WZ2PaperPureToSection6ExactSourceStatement : Prop :=
  ∃ logExponent : ℕ,
  ∀ sigma outputLoss : ℝ,
    0 < sigma → sigma < 1 →
    0 < outputLoss →
    HasWZ2PaperCroppedCriticalVolumeFloor sigma →
      ∃ inputLoss delta₀ : ℝ,
        0 < inputLoss ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ source : Kakeya.Streamlined.TubeFamily delta,
            ∀ shading : Kakeya.Streamlined.TubeShading source,
              ∀ publicExtremal :
                  WZ2PaperPureIsExtremal
                    sigma inputLoss source shading,
                source.IsInUnitBall →
                  ∃ selected : Kakeya.Streamlined.TubeSubfamily source,
                    ∃ cropped :
                        WZ1PaperTubeShading selected.family,
                      (∀ index,
                        cropped.carrier index ⊆
                          shading.carrier (selected.embedding index)) ∧
                      wz2PaperPureRefinementFraction delta logExponent *
                          shading.mass ≤
                        cropped.mass ∧
                      Nonempty
                        (WZ2PaperSection6ExactSource
                          sigma inputLoss selected.family cropped)

end Kakeya.Assouad

end
