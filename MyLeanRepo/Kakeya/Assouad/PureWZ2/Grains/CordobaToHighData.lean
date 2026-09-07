import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SlabExtension
import Mathlib.Tactic

/-!
# Córdoba-to-HighData wiring helper

Takes a Córdoba slab volume lower bound on a subset of projection values,
extends it to the full projection via `extend_slab_bounds`, and applies
`slab_to_ad` to produce `PureWZ2LocalADHighData`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/-- Wire Córdoba slab bound + extension + slab_to_ad into HighData. -/
def cordoba_to_high_data
    {delta' rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta'}
    {shading : WZ1PaperTubeShading family}
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (C : ENNReal)
    (q : Point3)
    (hq : q ∈ shading.union)
    (v : Point3)
    (hv_unit : ‖v‖ = 1)
    (S : Set Point3)
    (hS_meas : MeasurableSet S)
    (W0 V_min V_total : ℝ)
    (hW0_pos : 0 < W0)
    (hVmin_pos : 0 < V_min)
    (hV_total_pos : 0 < V_total)
    (hV_total : volume S ≤ ENNReal.ofReal V_total)
    (P : Set ℝ)
    (h_slab_P : ∀ t ∈ P,
        volume (S ∩ {x | |inner ℝ x v - t| ≤ W0}) ≥ ENNReal.ofReal V_min)
    (h_cover : ∀ t ∈ scalarProjection v S, ∃ t' ∈ P, |t - t'| ≤ W0)
    (h_arithmetic :
        ENNReal.ofReal ((V_total / V_min) * (2 * (2 * W0) / rho + 2)) ≤ C)
    (h_dir : v = planeMap ⟨q, hq⟩)
    (h_contain : shading.union ∩ Metric.closedBall q (Real.sqrt rho) ⊆ S) :
    PureWZ2LocalADHighData planeMap C rho q hq := by
  let W : ℝ := 2 * W0
  have hW_pos : 0 < W := by positivity
  have h_slab_full : ∀ t ∈ scalarProjection v S,
      volume (S ∩ {x | |inner ℝ x v - t| ≤ W}) ≥ ENNReal.ofReal V_min :=
    PureWZ2.extend_slab_bounds hS_meas hW0_pos hVmin_pos h_slab_P h_cover
  exact
    { v := v
      hv_unit := hv_unit
      S := S
      hS_meas := hS_meas
      W := W
      V_min := V_min
      V_total := V_total
      hW_pos := hW_pos
      hVmin_pos := hVmin_pos
      hV_total_pos := hV_total_pos
      hV_total := hV_total
      h_slab := h_slab_full
      h_arithmetic := h_arithmetic
      h_dir := h_dir
      h_contain := h_contain }

end Kakeya.Assouad

end
