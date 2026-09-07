import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DyadicDirectionDichotomy
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SelectedCardinalityCancellation
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import Mathlib.Tactic

/-!
# Density power carried by a retained dyadic branch

An extremal paper shading has aggregate mass at least
`delta^(loss+2) * #family`.  If a branch retains the source mass up to a
factor `A` and has point multiplicity below `2m`, its mass is at most
`2m * delta^(sigma-loss)`.  Hence, after absorbing `2A`, the dyadic
multiplicity `m` dominates a fixed scale power times the family cardinality.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- Quantitative lower bound for the multiplicity of any retained dyadic
branch.  All logarithmic or geometric selection costs remain in the explicit
coefficient `massLoss`; `habsorb` is the only small-scale bookkeeping input. -/
lemma dyadic_branch_multiplicity_density
    {delta sigma loss densityLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source selected : WZ1PaperTubeShading family}
    {multiplicity : ℕ}
    {massLoss : ENNReal}
    (extremal :
      WZ2PaperCroppedIsExtremal sigma loss family source)
    (hline : WZ1PaperIsLineClass family)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hsub : PaperIsSubshading selected source)
    (hmass : source.mass ≤ massLoss * selected.mass)
    (hmultiplicity : ∀ point ∈ selected.union,
      selected.pointMultiplicity point < 2 * multiplicity)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * loss)
    (habsorb :
      (2 * massLoss) * Kakeya.realRpowENN delta loss ≤ 1) :
    Kakeya.realRpowENN delta densityLoss * family.enncard ≤
      (multiplicity : ENNReal) := by
  have hdelta : 0 < delta := extremal.delta_pos
  have hambient :
      Kakeya.realRpowENN delta (loss + 2) * family.enncard ≤
        source.mass := by
    let all :=
      Kakeya.Streamlined.TubeSubfamily.fromFinset family Finset.univ
    have hall := selected_cardinality_cancellation extremal hline all
      hdeltaSmall
    have hcard : all.family.enncard = family.enncard := by
      simp [all, Kakeya.Streamlined.TubeSubfamily.fromFinset,
        Kakeya.Streamlined.TubeFamily.enncard]
    rwa [hcard] at hall
  have hselectedMass :
      selected.mass ≤ (2 * multiplicity : ENNReal) * volume selected.union := by
    apply mass_le_of_pointMultiplicity_le
    intro point hpoint
    exact_mod_cast (hmultiplicity point hpoint).le
  have hselectedVolume :
      volume selected.union ≤ Kakeya.realRpowENN delta (sigma - loss) := by
    have hunion : selected.union ⊆ source.union := by
      rintro point ⟨index, hpoint⟩
      exact ⟨index, hsub index hpoint⟩
    exact (measure_mono hunion).trans extremal.volume_upper
  have hraw :
      Kakeya.realRpowENN delta (loss + 2) * family.enncard ≤
        (2 * massLoss) * (multiplicity : ENNReal) *
          Kakeya.realRpowENN delta (sigma - loss) := by
    calc
      Kakeya.realRpowENN delta (loss + 2) * family.enncard
          ≤ source.mass := hambient
      _ ≤ massLoss * selected.mass := hmass
      _ ≤ massLoss *
          ((2 * multiplicity : ENNReal) * volume selected.union) := by
            gcongr
      _ ≤ massLoss *
          ((2 * multiplicity : ENNReal) *
            Kakeya.realRpowENN delta (sigma - loss)) := by
            gcongr
      _ = (2 * massLoss) * (multiplicity : ENNReal) *
          Kakeya.realRpowENN delta (sigma - loss) := by ring
  let volumePower := Kakeya.realRpowENN delta (sigma - loss)
  have hvolumeZero : volumePower ≠ 0 := by
    simp [volumePower, Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
  have hvolumeTop : volumePower ≠ ⊤ := by
    simp [volumePower, Kakeya.realRpowENN]
  have hcancelVolume :
      Kakeya.realRpowENN delta (2 - sigma + 2 * loss) *
          family.enncard ≤
        (2 * massLoss) * (multiplicity : ENNReal) := by
    have hfactor :
        Kakeya.realRpowENN delta (loss + 2) =
          Kakeya.realRpowENN delta (2 - sigma + 2 * loss) *
            volumePower := by
      rw [show loss + 2 =
          (2 - sigma + 2 * loss) + (sigma - loss) by ring,
        Kakeya.Assouad.realRpowENN_add hdelta]
    rw [hfactor] at hraw
    have hraw' :
        volumePower *
            (Kakeya.realRpowENN delta (2 - sigma + 2 * loss) *
              family.enncard) ≤
          volumePower *
            ((2 * massLoss) * (multiplicity : ENNReal)) := by
      simpa [volumePower, mul_assoc, mul_left_comm, mul_comm] using hraw
    have hraw'' :
        (Kakeya.realRpowENN delta (2 - sigma + 2 * loss) *
            family.enncard) * volumePower ≤
          ((2 * massLoss) * (multiplicity : ENNReal)) * volumePower := by
      simpa [mul_comm] using hraw'
    exact (ENNReal.mul_le_mul_iff_left hvolumeZero hvolumeTop).mp hraw''
  have hscaled := mul_le_mul_left' hcancelVolume
    (Kakeya.realRpowENN delta loss)
  have hexponent :
      Kakeya.realRpowENN delta loss *
          Kakeya.realRpowENN delta (2 - sigma + 2 * loss) =
        Kakeya.realRpowENN delta densityLoss := by
    rw [← Kakeya.Assouad.realRpowENN_add hdelta, hdensityLoss]
    congr 1
    ring
  calc
    Kakeya.realRpowENN delta densityLoss * family.enncard =
        Kakeya.realRpowENN delta loss *
          (Kakeya.realRpowENN delta (2 - sigma + 2 * loss) *
            family.enncard) := by rw [← hexponent]; ring
    _ ≤ Kakeya.realRpowENN delta loss *
          ((2 * massLoss) * (multiplicity : ENNReal)) := hscaled
    _ = ((2 * massLoss) * Kakeya.realRpowENN delta loss) *
          (multiplicity : ENNReal) := by ring
    _ ≤ 1 * (multiplicity : ENNReal) := by gcongr
    _ = (multiplicity : ENNReal) := by simp

end Kakeya.Assouad.PureWZ2

end
