import MyLeanRepo.Kakeya.Streamlined.RhoTubeMultiplicity.PerTubeDensity
import MyLeanRepo.Kakeya.Streamlined.RhoTubeMultiplicity.DilatedExactInducedThickenedFiberMass.Proof
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeRadius

/-!
# Per-tube density inside an actual dilated parent

The strict tube-density theorem is applied only to the same-axis
radius-`rho` enlargement of the fine tube.  Its full halo is then compressed
into the actual dilated parent by the rolling-body halo estimate.
-/

noncomputable section

open MeasureTheory Metric

namespace Kakeya.Streamlined

/--
If a fine `delta`-tube lies in an actual dilated `rho`-tube parent, then the
part of its shaded `rho`-halo inside that parent controls the usual per-tube
density lower bound.  The factor `1728` is the rolling-body halo loss.
-/
lemma dilated_per_tube_density
    {delta rho A : ℝ}
    (hdelta : 0 < delta) (hdelta_rho : delta ≤ rho) (hrho_one : rho ≤ 1)
    (hA : 1 ≤ A)
    (fine : Kakeya.DeltaTube delta) (parent : Kakeya.DeltaTube rho)
    (hcontained : fine.carrier ⊆ dilatedTubeCarrier A parent)
    (E : Set Point3) (hE_meas : MeasurableSet E)
    (hE_sub : E ⊆ fine.carrier) :
    ENNReal.ofReal (1 / 100 : ℝ) * volume E /
          Kakeya.deltaTubeVolume delta * parent.volume ≤
      1728 *
        volume
          (dilatedTubeCarrier A parent ∩ Metric.cthickening rho E) := by
  have hrho : 0 < rho := hdelta.trans_le hdelta_rho
  let widened := GeometricLemmas.withRadius rho fine
  have hfine_widened : fine.carrier ⊆ widened.carrier :=
    GeometricLemmas.carrier_subset_withRadius hdelta_rho fine
  have hdensity :
      ENNReal.ofReal (1 / 100 : ℝ) * volume E /
            Kakeya.deltaTubeVolume delta * widened.volume ≤
        volume (widened.carrier ∩ Metric.cthickening rho E) :=
    per_tube_density hdelta hrho hdelta_rho hrho_one
      fine widened hfine_widened E hE_meas hE_sub
  have hwidened_volume : widened.volume = parent.volume :=
    tube_volume_eq widened parent
  have hinter_full :
      volume (widened.carrier ∩ Metric.cthickening rho E) ≤
        volume (Metric.cthickening rho E) :=
    measure_mono Set.inter_subset_right
  have hE_parent : E ⊆ dilatedTubeCarrier A parent :=
    hE_sub.trans hcontained
  have hhalo :
      volume (Metric.cthickening rho E) ≤
        1728 *
          volume
            (dilatedTubeCarrier A parent ∩ Metric.cthickening rho E) :=
    dilated_tube_halo_volume_bound hrho hA parent E hE_parent
  rw [hwidened_volume] at hdensity
  exact hdensity.trans (hinter_full.trans hhalo)

/--
The same estimate with the reciprocal `1 / 100` cleared.  This is the form
used by the finite fiber-summing argument.
-/
lemma dilated_per_tube_density_scaled
    {delta rho A : ℝ}
    (hdelta : 0 < delta) (hdelta_rho : delta ≤ rho) (hrho_one : rho ≤ 1)
    (hA : 1 ≤ A)
    (fine : Kakeya.DeltaTube delta) (parent : Kakeya.DeltaTube rho)
    (hcontained : fine.carrier ⊆ dilatedTubeCarrier A parent)
    (E : Set Point3) (hE_meas : MeasurableSet E)
    (hE_sub : E ⊆ fine.carrier) :
    parent.volume / Kakeya.deltaTubeVolume delta * volume E ≤
      172800 *
        volume
          (dilatedTubeCarrier A parent ∩ Metric.cthickening rho E) := by
  have h := dilated_per_tube_density
    hdelta hdelta_rho hrho_one hA fine parent hcontained E hE_meas hE_sub
  let c100 : ENNReal := ENNReal.ofReal (100 : ℝ)
  let c1_100 : ENNReal := ENNReal.ofReal (1 / 100 : ℝ)
  have hconstants : c100 * c1_100 = 1 := by
    dsimp only [c100, c1_100]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 100)]
    norm_num
  have hmul := mul_le_mul_left' h c100
  calc
    parent.volume / Kakeya.deltaTubeVolume delta * volume E
        = c100 *
            (c1_100 * volume E / Kakeya.deltaTubeVolume delta *
              parent.volume) := by
          rw [show c100 *
              (c1_100 * volume E / Kakeya.deltaTubeVolume delta *
                parent.volume) =
              (c100 * c1_100) *
                (parent.volume / Kakeya.deltaTubeVolume delta *
                  volume E) by
            simp only [div_eq_mul_inv]
            ring,
            hconstants, one_mul]
    _ ≤ c100 *
          (1728 *
            volume
              (dilatedTubeCarrier A parent ∩
                Metric.cthickening rho E)) := hmul
    _ = 172800 *
          volume
            (dilatedTubeCarrier A parent ∩
              Metric.cthickening rho E) := by
        dsimp only [c100]
        norm_num
        ring

end Kakeya.Streamlined
