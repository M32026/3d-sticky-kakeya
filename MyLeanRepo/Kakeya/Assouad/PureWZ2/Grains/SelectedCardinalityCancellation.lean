import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierVolumeLower
import MyLeanRepo.Kakeya.Assouad.TubeVolumeRatio
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Selected-family cardinality cancellation

The full-fiber multiplicity cap in one sticky output carries the cardinality
of the selected fine family.  This factor is not independent: density of the
source shading and the uniform `delta^2` lower volume of a paper tube imply
that `delta^(loss+2) * #selected` is bounded by the source shaded mass.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory ENNReal

/-- An indexed tube subfamily has no more indices than its ambient family. -/
lemma tubeSubfamily_enncard_le
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily source) :
    selected.family.enncard ≤ source.enncard := by
  have hcard : selected.family.card ≤ source.card := by
    have hinj : Function.Injective selected.embedding :=
      selected.embedding.injective
    simpa using Fintype.card_le_of_injective selected.embedding hinj
  simpa [Kakeya.Streamlined.TubeFamily.enncard] using hcard

/-- A line-class paper body family has mass at least
`delta^2 * #family`. -/
lemma paperBodyFamily_mass_lower_rpow_two
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hline : WZ1PaperIsLineClass family) :
    Kakeya.realRpowENN delta 2 * family.enncard ≤
      (wz1PaperBodyFamily family).mass := by
  have hpi_one : (1 : ℝ) ≤ Real.pi :=
    (by linarith [Real.pi_gt_three])
  have hrpow_le_volume : Kakeya.realRpowENN delta 2 ≤
      Kakeya.deltaTubeVolume delta := by
    calc
      Kakeya.realRpowENN delta 2 = ENNReal.ofReal (delta ^ 2) := by
        simp [Kakeya.realRpowENN, Real.rpow_two]
      _ ≤ ENNReal.ofReal (Real.pi * delta ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [sq_nonneg delta]
      _ ≤ Kakeya.deltaTubeVolume delta :=
        deltaTubeVolume_lower_pi hdelta
  calc
    Kakeya.realRpowENN delta 2 * family.enncard ≤
        Kakeya.deltaTubeVolume delta * family.enncard := by gcongr
    _ = ∑ _index : Fin family.card, Kakeya.deltaTubeVolume delta := by
      simp [Kakeya.Streamlined.TubeFamily.enncard, mul_comm]
    _ ≤ ∑ index : Fin family.card,
        volume (wz1PaperTubeCarrier (family.tube index)) := by
      apply Finset.sum_le_sum
      intro index _
      exact wz2PaperTubeCarrier_volume_lower
        hdelta hdeltaSmall (family.tube index) (hline index)
    _ = (wz1PaperBodyFamily family).mass := rfl

/-- Density cancels the cardinality of every selected tube subfamily. -/
lemma selected_cardinality_cancellation
    {delta sigma loss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    (extremal :
      WZ2PaperCroppedIsExtremal sigma loss source sourceShading)
    (hline : WZ1PaperIsLineClass source)
    (selected : Kakeya.Streamlined.TubeSubfamily source)
    (hdeltaSmall : delta ≤ 1 / 12) :
    Kakeya.realRpowENN delta (loss + 2) * selected.family.enncard ≤
      sourceShading.mass := by
  have hdelta : 0 < delta := extremal.delta_pos
  have hbody : Kakeya.realRpowENN delta 2 * source.enncard ≤
      (wz1PaperBodyFamily source).mass :=
    paperBodyFamily_mass_lower_rpow_two hdelta hdeltaSmall hline
  have hselected : Kakeya.realRpowENN delta 2 * selected.family.enncard ≤
      Kakeya.realRpowENN delta 2 * source.enncard := by
    gcongr
    exact tubeSubfamily_enncard_le selected
  have hdense := extremal.dense
  calc
    Kakeya.realRpowENN delta (loss + 2) * selected.family.enncard =
        Kakeya.realRpowENN delta loss *
          (Kakeya.realRpowENN delta 2 * selected.family.enncard) := by
      rw [Kakeya.Assouad.realRpowENN_add hdelta loss 2]
      ring
    _ ≤ Kakeya.realRpowENN delta loss *
        (Kakeya.realRpowENN delta 2 * source.enncard) := by gcongr
    _ ≤ Kakeya.realRpowENN delta loss *
        (wz1PaperBodyFamily source).mass := by gcongr
    _ ≤ sourceShading.mass := hdense

end Kakeya.Assouad.PureWZ2

end
