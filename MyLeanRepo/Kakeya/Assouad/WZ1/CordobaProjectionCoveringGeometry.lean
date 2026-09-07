import MyLeanRepo.Kakeya.Assouad.WZ1.CubeCountGeometry

/-!
# Córdoba projection covering geometry

This module exposes the slab-volume covering lemma in the form used by the
root-relative Córdoba argument: the projected target set need only be
contained in the projection of the measurable ambient set.
-/

namespace Kakeya.Assouad

open MeasureTheory Metric

/--
Covering number bound when the target projection is a subset of the projection
of the set carrying the slab-volume estimates.
-/
lemma covering_number_from_slab_volumes_subset
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {E : Set ℝ} {S : Set X} {W rho V_total V_min : ℝ}
    (proj : X → ℝ)
    (hrho_pos : 0 < rho) (hW_pos : 0 < W) (hVmin_pos : 0 < V_min)
    (hS_meas : MeasurableSet S)
    (hproj_meas : Measurable proj)
    (_hE : E ⊆ proj '' S)
    (h_slab :
      ∀ t ∈ E,
        μ (S ∩ {x | |proj x - t| ≤ W}) ≥
          ENNReal.ofReal V_min)
    (h_total : μ S ≤ ENNReal.ofReal V_total)
    (h_disjoint :
      ∀ t t', |t - t'| > 2 * W →
        Disjoint {x | |proj x - t| ≤ W}
          {x | |proj x - t'| ≤ W}) :
    (↑(externalCoveringNumber (Real.toNNReal rho) E) : ENNReal) ≤
      ENNReal.ofReal
        ((V_total / V_min) * (2 * W / rho + 2)) := by
  exact covering_number_from_slab_volumes_of_slab_bounds
    proj hrho_pos hW_pos hVmin_pos hS_meas hproj_meas
    h_slab h_total h_disjoint

end Kakeya.Assouad
