import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingExtractionAbsorption

/-!
# Frostman interval certificate for Lemma 7.10

The selected suffix has uniform exact branching at every integer grid level.
The scaled-tree argument converts this into the target-dimensional Frostman
certificate after normalizing the selected cell.
-/

noncomputable section

namespace Kakeya.Assouad

/--
The analytic certificate consumed by `ParameterLocalSpacingCandidateData`;
the geometric block fields and provenance are supplied by
`ParameterSpacingSelectedCellData`.
-/
def ParameterSpacingIntervalCertificateStatement : Prop :=
  ∀ epsilon : ℝ,
    0 < epsilon →
    epsilon < 1 / 10 →
    ∀ base : ℕ,
      3 ≤ base →
      (2 * (Nat.log 2 ((base + 1) ^ 3) + 1) : ℝ) ≤
        Real.rpow (base : ℝ) (epsilon ^ 2 / 1000) →
      ∃ delta₀ : ℝ,
        0 < delta₀ ∧ delta₀ < 1 ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              ∀ C lambda : ENNReal,
                ∀ clustered :
                    TubeParameterClusterFrostmanData
                      F Y C lambda delta,
                  ∀ profile :
                      ParameterSpacingProfileAssemblyData
                        (epsilon := epsilon) clustered,
                    profile.tree.base = base →
                    ∀ selectedCell :
                        ParameterSpacingSelectedCellData profile,
                      let fineScale :=
                        normalizedParameterBlockFineScale
                          delta selectedCell.blockScale
                      let normalized :=
                        normalizedParameterBlock
                          selectedCell.points selectedCell.center
                            selectedCell.blockScale
                      normalized.IsFrostman
                        fineScale
                        (1 - epsilon ^ 2)
                        (Kakeya.realRpowENN
                          fineScale (-12 * epsilon ^ 2)) ∧
                        Kakeya.realRpowENN
                            fineScale
                            (-(1 - epsilon ^ 2)) ≤
                          Kakeya.realRpowENN fineScale
                              (-12 * epsilon ^ 2) *
                            normalized.enncard ∧
                        weightedFrostmanToKatzTaoConstant
                              (1 - epsilon ^ 2) *
                            ENNReal.ofReal
                              (1 + Real.log fineScale⁻¹) *
                            Kakeya.realRpowENN fineScale
                              (7 * epsilon ^ 2) ≤
                          100000

end Kakeya.Assouad
