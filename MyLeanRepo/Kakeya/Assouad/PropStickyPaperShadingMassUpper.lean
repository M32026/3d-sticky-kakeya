import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpperStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperAxisCoreVolume

/-!
# Aggregate mass upper bound for a paper shading

Sum the closed quadratic carrier-volume bound over the indexed family.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

theorem wz2_paper_shading_mass_upper :
    WZ2PaperShadingMassUpperStatement := by
  intro scale hscale hscale_le family hline shading
  let C : ENNReal :=
    55296 * Kakeya.deltaTubeVolume 1 * Kakeya.realRpowENN scale 2
  have hgeometry : WZ2PaperTubeCarrierGeometryStatement :=
    wz2_paper_tube_carrier_geometry
  have h_per_tube : ∀ i : Fin family.card,
      volume (shading.carrier i) ≤ C := by
    intro i
    have hsub : shading.carrier i ⊆ wz1PaperTubeCarrier (family.tube i) :=
      shading.subset_body i
    have hvol : volume (wz1PaperTubeCarrier (family.tube i)) ≤ C :=
      (wz2PaperTubeCarrier_convex_and_volume_quadratic hgeometry hscale hscale_le
        (family.tube i) (hline i)).2
    exact (measure_mono hsub).trans hvol
  have h_sum : shading.mass ≤ ∑ i : Fin family.card, C := by
    calc
      shading.mass
        = ∑ i : Fin family.card, volume (shading.carrier i) := rfl
      _ ≤ ∑ i : Fin family.card, C :=
        Finset.sum_le_sum fun i _ => h_per_tube i
  have h_const_sum :
      (∑ i : Fin family.card, C) = (family.card : ENNReal) * C := by
    simp [Finset.sum_const]
  rw [h_const_sum] at h_sum
  have h_enncard : (family.card : ENNReal) = family.enncard := by
    rfl
  rw [h_enncard] at h_sum
  simpa [C, mul_comm, mul_assoc] using h_sum

end Kakeya.Assouad

end
