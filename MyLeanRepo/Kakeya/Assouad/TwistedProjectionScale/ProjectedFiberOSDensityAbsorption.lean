import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSDensityAbsorptionStatement

/-!
# Density absorption after projected-fiber OS uniformization

Compose the band, terminal atomization, and weighted OS mass losses, then
absorb their exact product into the final same-family density.
-/

namespace Kakeya.Assouad

theorem projected_fiber_os_density_absorption :
    ProjectedFiberOSDensityAbsorptionStatement := by
  intro delta eta hdelta hdelta_one heta F Y hY_dense hY_slab f threshold
    levelCount bandData base levels indexBound atomized uniform h_loss
  let S := uniform.shading
  let FM := F.toBodyFamily
  have h1 :
      Y.mass ≤
        projectedFiberBandLoss levelCount * bandData.shading.mass :=
    bandData.mass_retention
  have h2 :
      bandData.shading.mass ≤
        projectedFiberAtomizationLoss base levels indexBound *
          projectedFiberOSLoss base levels * S.mass :=
    uniform.total_mass_retention
  have h3 :
      Y.mass ≤
        projectedFiberTotalLoss levelCount base levels indexBound *
          S.mass := by
    calc
      Y.mass
          ≤ projectedFiberBandLoss levelCount *
              bandData.shading.mass := h1
      _ ≤ projectedFiberBandLoss levelCount *
            (projectedFiberAtomizationLoss base levels indexBound *
              projectedFiberOSLoss base levels * S.mass) := by
          gcongr
      _ = projectedFiberTotalLoss
            levelCount base levels indexBound * S.mass := by
          simp [projectedFiberTotalLoss, mul_assoc]
  have h4 :
      Y.mass ≤
        Kakeya.realRpowENN delta (-3 * eta) * S.mass := by
    calc
      Y.mass
          ≤ projectedFiberTotalLoss
              levelCount base levels indexBound * S.mass := h3
      _ ≤ Kakeya.realRpowENN delta (-3 * eta) * S.mass := by
          gcongr
  have h5 :
      Kakeya.realRpowENN delta eta * FM.mass ≤ Y.mass :=
    hY_dense
  have h6 :
      Kakeya.realRpowENN delta eta * FM.mass ≤
        Kakeya.realRpowENN delta (-3 * eta) * S.mass :=
    h5.trans h4
  set c := Kakeya.realRpowENN delta (3 * eta) with hc_def
  have h7 :
      c * (Kakeya.realRpowENN delta eta * FM.mass) ≤
        c * (Kakeya.realRpowENN delta (-3 * eta) * S.mass) := by
    gcongr
  have h8 :
      c * Kakeya.realRpowENN delta eta =
        Kakeya.realRpowENN delta (4 * eta) := by
    rw [← realRpowENN_add hdelta (3 * eta) eta]
    ring_nf
  have h9 :
      c * Kakeya.realRpowENN delta (-3 * eta) = 1 := by
    have h10 :
        c * Kakeya.realRpowENN delta (-3 * eta) =
          Kakeya.realRpowENN delta ((3 * eta) + (-3 * eta)) :=
      (realRpowENN_add hdelta (3 * eta) (-3 * eta)).symm
    rw [h10]
    have h11 : (3 * eta) + (-3 * eta) = 0 := by ring
    rw [h11]
    simp [Kakeya.realRpowENN]
  have h12 :
      c * (Kakeya.realRpowENN delta eta * FM.mass) =
        Kakeya.realRpowENN delta (4 * eta) * FM.mass := by
    have h121 :
        c * (Kakeya.realRpowENN delta eta * FM.mass) =
          (c * Kakeya.realRpowENN delta eta) * FM.mass := by
      exact Eq.symm
        (mul_assoc c (Kakeya.realRpowENN delta eta) FM.mass)
    rw [h121, h8]
  have h13 :
      c * (Kakeya.realRpowENN delta (-3 * eta) * S.mass) =
        S.mass := by
    have h131 :
        c * (Kakeya.realRpowENN delta (-3 * eta) * S.mass) =
          (c * Kakeya.realRpowENN delta (-3 * eta)) * S.mass := by
      exact Eq.symm
        (mul_assoc c
          (Kakeya.realRpowENN delta (-3 * eta)) S.mass)
    rw [h131, h9, one_mul]
  have h_density :
      S.IsLambdaDense
        (Kakeya.realRpowENN delta (4 * eta)) := by
    rw [h12, h13] at h7
    exact h7
  have h_sub1 : IsSubshading S atomized.shading :=
    uniform.subshading
  have h_sub2 :
      IsSubshading atomized.shading bandData.shading :=
    atomized.subshading
  have h_sub3 : IsSubshading bandData.shading Y :=
    bandData.subshading
  have h_sub : IsSubshading S Y := by
    intro i
    exact (h_sub1 i).trans ((h_sub2 i).trans (h_sub3 i))
  have h_slab : S.union ⊆ horizontalSlab 0 1 := by
    have h10 : S.union ⊆ Y.union :=
      IsSubshading.union_subset h_sub
    exact h10.trans hY_slab
  have h_twisted :
      twistedUnion S f ⊆ uniform.retainedBand :=
    uniform.twisted_subset
  refine' ⟨_⟩
  exact
    { globalShading := S
      globalShading_eq := rfl
      subshading := h_sub
      density := h_density
      slab := h_slab
      twisted_subset := h_twisted }

end Kakeya.Assouad
