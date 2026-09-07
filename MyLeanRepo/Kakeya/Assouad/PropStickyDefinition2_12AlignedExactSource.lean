import MyLeanRepo.Kakeya.Assouad.PropStickySection6InternalCertificate
import MyLeanRepo.Kakeya.Assouad.PropStickyCallerRootedSynchronizedSchedule

/-!
# Exact-scale source with aligned complete pure witnesses

The historical Section 6 preparation chooses one internal exact-scale witness
at every admissible scale.  Cover synchronization alone remembers only its
ordinary parent relation.  The literal `multiScaleWolffLem` additionally needs
the complete pure scale data, especially the canonical outer-John CWA of every
strict full fiber.

This is an internal stronger certificate.  It is not claimed to follow from
the public nearby-scale Definition 2.12 predicate.
-/

noncomputable section

namespace Kakeya.Assouad

/-- A selected tube subfamily preserves the ambient unit-ball support. -/
theorem wz2PaperTubeSubfamily_isInUnitBall
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (hfamily : family.IsInUnitBall) :
    selected.family.IsInUnitBall := by
  intro index
  rw [selected.tube_eq]
  exact hfamily (selected.embedding index)

/--
One pure exact-scale lift aligned with the canonical historical exact-scale
choice.

The pure witness uses the same scale and definitionally the same coarse
family.  Its parent-map-free cover is exactly the public cover stored by the
existing synchronization certificate.
-/
structure WZ2PaperAlignedPureExactScaleData
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (sourceData :
      WZ2PaperSection6ExactSource
        sigma loss family shading)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) where
  pureScale :
    WZ2PaperPureScaleCoverData
      family rho.1
      (Kakeya.realRpowENN delta (-loss))
  coarse_eq :
    pureScale.coarse =
      (sourceData.canonicalScaleData rho).coarse
  cover_eq :
    HEq pureScale.cover
      (sourceData.canonicalScaleSynchronization rho).publicCover

/--
The existing exact source plus one aligned complete pure scale witness at
every canonical internal exact scale.
-/
structure WZ2PaperAlignedPureExactSource
    {delta : ℝ}
    (sigma loss : ℝ)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading family) : Prop where
  unit_ball : family.IsInUnitBall
  sourceData :
    WZ2PaperSection6ExactSource
      sigma loss family shading
  pureScale :
    ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
      Nonempty
        (WZ2PaperAlignedPureExactScaleData
          sourceData rho)

namespace WZ2PaperAlignedPureExactSource

/-- Forget the complete pure lifts and enter the existing Section 6 mainline. -/
theorem toSection6ExactSource
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data :
      WZ2PaperAlignedPureExactSource
        sigma loss family shading) :
    WZ2PaperSection6ExactSource
      sigma loss family shading :=
  data.sourceData

/-- The aligned pure witness at one canonical exact scale. -/
noncomputable def canonicalPureScaleData
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data :
      WZ2PaperAlignedPureExactSource
        sigma loss family shading)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) :
    WZ2PaperAlignedPureExactScaleData data.sourceData rho :=
  Classical.choice (data.pureScale rho)

end WZ2PaperAlignedPureExactSource

/--
Transport complete pure exact-scale data to every coordinate of the canonical
caller-rooted schedule.

The schedule now records that each entry is the canonical historical choice
at its displayed scale.  The enhanced source supplies the pure witness aligned
with exactly that canonical choice.
-/
structure WZ2PaperAlignedPureScheduleScaleData
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {outputConstant : ENNReal}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {aligned :
      WZ2PaperAlignedPureExactSource
        sigma loss family shading}
    (schedule :
      WZ2PaperCallerRootedSynchronizedScheduleData
        (Kakeya.realRpowENN delta (-loss))
        outputConstant caller
        aligned.sourceData.internalData.cwa_exact_scales)
    (coordinate : Fin schedule.nestedSchedule.scaleCount) where
  pureScale :
    WZ2PaperPureScaleCoverData
      family (schedule.nestedSchedule.scale coordinate).1
      (Kakeya.realRpowENN delta (-loss))
  coarse_eq :
    pureScale.coarse =
      (schedule.nestedSchedule.scaleData coordinate).coarse
  cover_eq :
    HEq pureScale.cover
      (schedule.coordinateSynchronization
        (fun rho =>
          aligned.sourceData.canonicalScaleSynchronization rho)
        coordinate).publicCover

namespace WZ2PaperAlignedPureExactSource

/-- Choose the aligned complete pure witness at one schedule coordinate. -/
noncomputable def scheduleScaleData
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {outputConstant : ENNReal}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    (aligned :
      WZ2PaperAlignedPureExactSource
        sigma loss family shading)
    (schedule :
      WZ2PaperCallerRootedSynchronizedScheduleData
        (Kakeya.realRpowENN delta (-loss))
        outputConstant caller
        aligned.sourceData.internalData.cwa_exact_scales)
    (coordinate : Fin schedule.nestedSchedule.scaleCount) :
    WZ2PaperAlignedPureScheduleScaleData
      (aligned := aligned) schedule coordinate := by
  let rho := schedule.nestedSchedule.scale coordinate
  let canonical :=
    aligned.canonicalPureScaleData rho
  have hhistorical :
      schedule.nestedSchedule.scaleData coordinate =
        aligned.sourceData.canonicalScaleData rho :=
    eq_of_heq (schedule.canonical_scaleData_eq coordinate)
  have hcanonicalCoarse :
      canonical.pureScale.coarse =
        (aligned.sourceData.canonicalScaleData rho).coarse :=
    canonical.coarse_eq
  have hcoarse :
      (schedule.nestedSchedule.scaleData coordinate).coarse =
        (aligned.sourceData.canonicalScaleData rho).coarse :=
    congrArg (fun data => data.coarse) hhistorical
  refine
    {
      pureScale := canonical.pureScale
      coarse_eq := ?_
      cover_eq := ?_
    }
  · exact hcanonicalCoarse.trans hcoarse.symm
  · have hsync :
        HEq
          (schedule.coordinateSynchronization
            (fun rho =>
              aligned.sourceData.canonicalScaleSynchronization rho)
            coordinate).publicCover
          (aligned.sourceData.canonicalScaleSynchronization rho).publicCover := by
      apply proof_irrel_heq
    exact canonical.cover_eq.trans hsync.symm

end WZ2PaperAlignedPureExactSource

/--
The strengthened entry theorem needed by the literal multiscale proof.

This deliberately refines the existing
`WZ2PaperPureToSection6ExactSourceStatement`; it does not weaken the public
Definition 2.12 predicate.
-/
def WZ2PaperPureToAlignedExactSourceStatement : Prop :=
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
                        (WZ2PaperAlignedPureExactSource
                          sigma inputLoss selected.family cropped)

end Kakeya.Assouad

end
