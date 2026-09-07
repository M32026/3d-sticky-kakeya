import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CroppedExtremal
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingBridge
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageAssemblyStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPureToCroppedPreparationStatements

/-!
# Correct public output of WZ2 `prop: sticky`

The structural output uses the pure Assouad Definition 2.12 cover.  The
cropped WZ cover is retained only as an internal certificate connecting the
existing balancing proof to the public full fibers.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
WZ anisotropic rescaling of one complete final full fiber.

The source fiber is the ordinary strict full fiber.  The global preparation
certificate proves that it is also the cropped strict full fiber and the
internal assigned fiber.

The WZ target family and cubical shading are retained for Section 6.  Public
extremality is stated on a separate ordinary target family connected to the
actual outer-John affine images by an explicit rescaling certificate.  Thus
the WZ target's axis data is never used as a substitute for public carrier
geometry.
-/
structure WZ2PaperPureRescaledFullFiberOutput
    {delta rho sigma loss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading fine)
    (parentTube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) where
  familyData :
    WZ2PaperLiteralUnitRescaledFamilyData
      fine parentTube hrho
  literalShading :
    WZ2PaperLiteralUnitRescaledShadingData
      familyData sourceShading
  jacobianConstant : ENNReal
  jacobianConstant_one : 1 ≤ jacobianConstant
  jacobianConstant_finite : jacobianConstant ≠ ⊤
  rescalingCertificate :
    WZ2PaperAssouadToLiteralRescalingCertificate
      hrho
      (WZ2PaperAssouadUnitRescalingData.ofTube
        parentTube hrho)
      familyData jacobianConstant
  extremal :
    WZ2PaperCroppedIsExtremal
      sigma loss
      rescalingCertificate.publicFamily
      (rescalingCertificate.publicShading
        literalShading.targetShading)
  source_cardinality_eq :
    rescalingCertificate.publicFamily.enncard =
      fine.enncard

/-! Balanced-cover compatibility on the same cropped shaded sets used by the
internal proof.  The parent map is the unique map derived from the public
geometric cover. -/
structure WZ2PaperPureBalancedCoverData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse) : Prop where
  point_compatibility :
    ∀ source point,
      point ∈ fineShading.carrier source →
        point ∈
          coarseShading.carrier (cover.parent source)

/-- The four paper conclusions on one final configuration. -/
structure WZ2PaperPurePropStickyData
    {delta sigma loss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading source)
    (rho : WZ2PaperRequestedScale delta)
    (logExponent : ℕ) where
  strongLoss : ℝ
  strongLoss_pos : 0 < strongLoss
  strongLoss_budget : 3 * strongLoss ≤ loss
  selected : Kakeya.Streamlined.TubeSubfamily source
  refined : WZ1PaperTubeShading selected.family
  refinement_subshading :
    ∀ index,
      refined.carrier index ⊆
        sourceShading.carrier (selected.embedding index)
  retained_mass :
    wz2PaperPureRefinementFraction delta logExponent *
        sourceShading.mass ≤
      refined.mass
  refined_cubical :
    WZ1PaperIsCubicalShading refined
  coarse : Kakeya.Streamlined.TubeFamily rho.1
  cover :
    WZ2PaperPurePartitioningCover
      selected.family coarse
  full_fiber_uniform :
    WZ2PaperPureFullFibersAreCUniform
      selected.family coarse
      (Kakeya.realRpowENN rho.1 (-strongLoss))
  coarseShading :
    WZ1PaperTubeShading coarse
  balanced :
    WZ2PaperPureBalancedCoverData
      cover refined coarseShading
  coarse_extremal_strong :
    WZ2PaperCroppedIsExtremal
      sigma strongLoss coarse coarseShading
  coarse_extremal :
    WZ2PaperCroppedIsExtremal
      sigma loss coarse coarseShading
  rescaledFiber :
    ∀ parent : Fin coarse.card,
      Nonempty
        (WZ2PaperPureRescaledFullFiberOutput
          (sigma := sigma) (loss := loss)
          (restrictPaperShading
            (Kakeya.Streamlined.TubeSubfamily.fromFinset selected.family
              (wz2PaperOrdinaryFullFiberIndices
                selected.family coarse parent))
            refined)
          (coarse.tube parent) coarse_extremal.delta_pos)
  coarse_multiplicity_upper :
    ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN rho.1 (2 - sigma - loss) *
          coarse.enncard
  fiber_multiplicity_upper :
    ∀ parent point,
      (((wz2PaperOrdinaryFullFiberIndices
          selected.family coarse parent).filter
          fun source =>
            point ∈ refined.carrier source).card :
          ENNReal) ≤
        Kakeya.realRpowENN (delta / rho.1)
            (2 - sigma - loss) *
          wz2PaperOrdinaryFullFiberCount
            selected.family coarse parent

/-! Public `prop: sticky` statement after the paper's explicit switch to the
cropped WZ shading convention.  Its CWA fields remain the pure Definition 2.12
predicate. -/
def WZ2PaperPurePropStickyStatement : Prop :=
  ∃ logExponent : ℕ,
  ∀ sigma : ℝ,
    0 < sigma → sigma < 1 →
    HasWZ2PaperCroppedCriticalVolumeFloor sigma →
      ∀ outputLoss : ℝ, 0 < outputLoss →
        ∃ inputLoss delta₀ : ℝ,
          0 < inputLoss ∧
          0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ source : Kakeya.Streamlined.TubeFamily delta,
              ∀ sourceShading :
                  WZ1PaperTubeShading source,
                WZ2PaperCroppedIsExtremal
                    sigma inputLoss source sourceShading →
                  ∀ rho : WZ2PaperRequestedScale delta,
                    Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                    rho.1 ≤ Real.rpow delta outputLoss →
                      Nonempty
                        (WZ2PaperPurePropStickyData
                          (sigma := sigma) (loss := outputLoss)
                          sourceShading rho logExponent)

end Kakeya.Assouad

end
