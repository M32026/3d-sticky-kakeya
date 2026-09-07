import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.RefinementInfrastructure

/-!
# Convert one-scale locally-linear output back into a source package

This enables dependent iteration of the one-scale producer: after each scale,
the output shading is repackaged as a `WZ1PlaninessGraininessPackage` at the
weaker output loss, so the next scale can consume it.
-/

namespace Kakeya.Assouad

namespace WZ1LocallyLinearOneScaleData

/--
Convert a one-scale locally-linear output into a `WZ1PlaninessGraininessPackage`
at the weaker `outputLoss`.

The key reconstruction is the local grains: the one-scale data guarantees
`planeMap_eq` but not a bounded `lipschitzConstant`.  We reuse the source's
bounded Lipschitz constant, which is valid because the plane map is identical
and the output shading is a subshading of the source shading.
-/
def toPlaninessGraininessPackage
    {sigma inputLoss outputLoss delta : ℝ}
    {source : WZ1PlaninessGraininessPackage sigma inputLoss delta}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (data : WZ1LocallyLinearOneScaleData source outputLoss rho)
    (hinputLoss_le_outputLoss : inputLoss ≤ outputLoss)
    (hdelta_pos : 0 < delta)
    (hdelta_one : delta ≤ 1) :
    WZ1PlaninessGraininessPackage sigma outputLoss delta := by
  have h_power_weak :
      Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-outputLoss) := by
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one
    linarith
  have h_union_subset : data.shading.union ⊆ source.shading.union :=
    IsSubshading.union_subset data.subshading
  have h_planeMap_eq :
      source.local_grains.planeMap = data.local_grains.planeMap :=
    data.planeMap_eq.symm
  have h_lipschitz_restricted :
      LipschitzOnWith source.local_grains.lipschitzConstant
        data.local_grains.planeMap data.shading.union := by
    have h1 : LipschitzOnWith source.local_grains.lipschitzConstant
        source.local_grains.planeMap data.shading.union :=
      source.local_grains.lipschitz.mono h_union_subset
    exact h_planeMap_eq ▸ h1
  let reconstructedLocalGrains :
      WZ1LocalGrainData data.shading sigma source.constant := {
    planeMap := data.local_grains.planeMap
    measurable := data.local_grains.measurable
    lipschitzConstant := source.local_grains.lipschitzConstant
    lipschitz := h_lipschitz_restricted
    unit := data.local_grains.unit
    incidence := data.local_grains.incidence
    local_ad := data.local_grains.local_ad
  }
  let reconstructedGlobalGrains :
      WZ1LipschitzGlobalGrainData
        data.shading sigma source.constant := {
    slope := source.global_grains.slope
    lipschitzConstant := source.global_grains.lipschitzConstant
    lipschitz := source.global_grains.lipschitz
    global_slab_ad := data.global_slab_ad
  }
  exact {
    family := source.family
    uniform := source.uniform
    shading := data.shading
    vertical_chart := source.vertical_chart
    constant := source.constant
    extremal := data.extremal
    constant_one := source.constant_one
    constant_ne_top := source.constant_ne_top
    constant_bound :=
      source.constant_bound.trans h_power_weak
    global_grains := reconstructedGlobalGrains
    local_grains := reconstructedLocalGrains
    slope_lipschitz_bound :=
      source.slope_lipschitz_bound.trans h_power_weak
    slope_one_lipschitz :=
      source.slope_one_lipschitz
    slope_bound := source.slope_bound
    planeMap_vertical_bound := by
      intro p hp
      change |data.local_grains.planeMap p (2 : Fin 3)| ≤ 1 / 2
      rw [data.planeMap_eq]
      exact
        source.planeMap_vertical_bound p
          (data.subshading.union_subset hp)
    planeMap_lipschitz_bound :=
      source.planeMap_lipschitz_bound.trans h_power_weak
    planeMap_one_lipschitz := by
      have h :=
        source.planeMap_one_lipschitz.mono h_union_subset
      rw [h_planeMap_eq] at h
      simpa [reconstructedLocalGrains] using h
  }

end WZ1LocallyLinearOneScaleData

end Kakeya.Assouad
