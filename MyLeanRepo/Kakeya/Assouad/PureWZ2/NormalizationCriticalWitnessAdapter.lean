import MyLeanRepo.Kakeya.Assouad.PureWZ2.CriticalRescaledFiberWitness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationFinalOrdinaryTrace

/-!
# Critical witness from a normalized final ordinary trace

Once a final cropped fiber has an ordinary trace, the remaining interface to
Node 2's pure critical floor is a single aggregate density inequality after
literal unit rescaling.  This module packages that last mechanical step.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace WZ2PaperPureRescaledFullFiberOutput

/--
Attach a critical witness to a final cropped fiber using the ordinary trace
of the frozen normalization.
-/
noncomputable def withNormalizationFinalOrdinaryTrace
    {sigma inputLoss normalizationLoss delta rho loss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent)
    (selected :
      Kakeya.Streamlined.TubeSubfamily normalized.croppedFamily)
    (finalShading : WZ1PaperTubeShading selected.family)
    (parentTube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (output :
      WZ2PaperPureRescaledFullFiberOutput
        (sigma := sigma) (loss := loss)
        finalShading parentTube hrho)
    (ordinaryDense :
      (output.rescalingCertificate.literalExactImageShading
        (normalized.finalOrdinaryTrace
          selected finalShading)).IsLambdaDense
            (Kakeya.realRpowENN (delta / rho) loss)) :
    PureWZ2CriticalRescaledFiberWitness
      (sigma := sigma) (loss := loss)
      finalShading parentTube hrho :=
  output.withOrdinaryExactImage
    (normalized.finalOrdinaryTrace selected finalShading)
    (by
      intro index point pointMem
      exact pointMem.2)
    ordinaryDense

/--
The same adapter with the exact literal-Jacobian mass inequality exposed as
its only quantitative premise.
-/
noncomputable def withNormalizationFinalOrdinaryTraceOfMass
    {sigma inputLoss normalizationLoss delta rho loss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent)
    (selected :
      Kakeya.Streamlined.TubeSubfamily normalized.croppedFamily)
    (finalShading : WZ1PaperTubeShading selected.family)
    (parentTube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (output :
      WZ2PaperPureRescaledFullFiberOutput
        (sigma := sigma) (loss := loss)
        finalShading parentTube hrho)
    (massLower :
      Kakeya.realRpowENN (delta / rho) loss *
            output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho : ℝ) ^ 2)) *
          (normalized.finalOrdinaryTrace
            selected finalShading).mass) :
    PureWZ2CriticalRescaledFiberWitness
      (sigma := sigma) (loss := loss)
      finalShading parentTube hrho :=
  output.withNormalizationFinalOrdinaryTrace
    normalized selected finalShading parentTube hrho
    (output.rescalingCertificate.literalExactImageShading_dense_of_mass
      (normalized.finalOrdinaryTrace selected finalShading)
      massLower)

/--
Produce the same witness from a synchronized per-tube ordinary density and
one scalar lower bound for the concrete final cropped mass.
-/
noncomputable def withNormalizationFinalOrdinaryTraceOfPerTube
    {sigma inputLoss normalizationLoss delta rho loss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent)
    (selected :
      Kakeya.Streamlined.TubeSubfamily normalized.croppedFamily)
    (finalShading : WZ1PaperTubeShading selected.family)
    (parentTube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (output :
      WZ2PaperPureRescaledFullFiberOutput
        (sigma := sigma) (loss := loss)
        finalShading parentTube hrho)
    (finalCubical : WZ1PaperIsCubicalShading finalShading)
    (finalSubset :
      ∀ index,
        finalShading.carrier index ⊆
          normalized.croppedRefined.carrier
            (selected.embedding index))
    (density : ENNReal)
    (ordinaryPerTube :
      ∀ index : Fin selected.family.card,
        density *
            volume
              (normalized.croppedFamily.tube
                (selected.embedding index)).carrier ≤
          volume
            (normalized.frame ''
              normalized.ordinaryRefined.carrier
                (PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
                  normalized selected index)))
    (scalar :
      Kakeya.realRpowENN (delta / rho) loss *
            output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho : ℝ) ^ 2)) *
          ((100 : ENNReal)⁻¹ * density * finalShading.mass)) :
    PureWZ2CriticalRescaledFiberWitness
      (sigma := sigma) (loss := loss)
      finalShading parentTube hrho := by
  apply
    output.withNormalizationFinalOrdinaryTraceOfMass
      normalized selected finalShading parentTube hrho
  exact scalar.trans <| by
    gcongr
    exact
      normalized.finalOrdinaryTrace_mass_lower
        selected finalShading source.extremal.delta_pos
        finalCubical finalSubset density ordinaryPerTube

end WZ2PaperPureRescaledFullFiberOutput

end Kakeya.Assouad

end
