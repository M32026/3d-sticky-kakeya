import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredHierarchyHelpers

/-!
# Shading restriction to height intervals

Wrappers that combine `restrictShadingToHeights` with the property-transfer
lemmas from `AnchoredHierarchyHelpers`.
-/

noncomputable section

namespace Kakeya.Assouad

namespace WZ1LocallyLinearOneScale

/-- Restrict a shading to points whose z-coordinate lies in a measurable set. -/
def restrictShadingToHeights
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (Z : Set ℝ) (hZ : MeasurableSet Z) :
    Kakeya.Streamlined.TubeShading F :=
  { carrier := fun i => Y.carrier i ∩ {p | p (2 : Fin 3) ∈ Z}
    measurable_carrier := fun i =>
      (Y.measurable_carrier i).inter
        (by
          let f : Point3 → ℝ := fun p => p (2 : Fin 3)
          have h_cont : Continuous f :=
            PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)
          exact h_cont.measurable hZ)
    subset_body := fun i =>
      Set.inter_subset_left.trans (Y.subset_body i) }

/-- The restricted shading is a subshading of the original. -/
lemma restrictShadingToHeights_subshading
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (Z : Set ℝ) (hZ : MeasurableSet Z) :
    IsSubshading (restrictShadingToHeights Y Z hZ) Y := by
  intro i
  exact Set.inter_subset_left

/--
Transfer local grains from a source shading to its height-restricted
subshading, keeping the same constant.
-/
def transferLocalGrainsToHeightRestriction
    {delta sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {Z : Set ℝ} {hZ : MeasurableSet Z}
    {C : ENNReal}
    (localGrains : WZ1LocalGrainData Y sigma C) :
    WZ1LocalGrainData
      (restrictShadingToHeights Y Z hZ) sigma C :=
  restrictAndWeakenLocalGrains
    (restrictShadingToHeights_subshading Y Z hZ)
    (by rfl)
    localGrains

/--
Transfer global slab AD from a source shading to its height-restricted
subshading, keeping the same constant.
-/
lemma transferGlobalSlabADToHeightRestriction
    {delta sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {Z : Set ℝ} {hZ : MeasurableSet Z}
    {slope : ℝ → ℝ} {C : ENNReal}
    (h : HasGlobalSlabAD Y slope sigma C) :
    HasGlobalSlabAD
      (restrictShadingToHeights Y Z hZ) slope sigma C :=
  restrictAndWeakenGlobalSlabAD
    (restrictShadingToHeights_subshading Y Z hZ)
    (by rfl)
    h

/--
Weaken extremality from `inputLoss` to `outputLoss` when
`inputLoss ≤ outputLoss`.
-/
lemma weakenExtremality
    {delta sigma inputLoss outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    (h : WZ1ExtremalPair sigma inputLoss F U Y)
    (h_le : inputLoss ≤ outputLoss) :
    WZ1ExtremalPair sigma outputLoss F U Y :=
  WZ1ExtremalPair.mono_epsilon h h_le

end WZ1LocallyLinearOneScale

end Kakeya.Assouad
