import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GlobalProjectionHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PlaneMapDirectionBounds

import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADTransport
namespace Kakeya.Assouad

lemma single_ball_global_ad
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (localGrains : PureWZ2LocalGrainData shading sigma C)
    (z : ℝ)
    (p : {point : Point3 // point ∈ shading.union})
    (E : Set Point3)
    (hE_height : ∀ x ∈ E, inner ℝ x e3 = z)
    (hE_sub : E ⊆ shading.union ∩ Metric.closedBall (p : Point3) (Real.sqrt delta))
    (hv2 : |(localGrains.planeMap p) (2 : Fin 3)| ≤ 1 / 10)
    (hv0 : 1 / 3 ≤ |(localGrains.planeMap p) (0 : Fin 3)|)
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (hsigma_pos : 0 < sigma)
    (hsigma_one : sigma < 1) :
    PureWZ2PaperADSet1
      (scalarProjection (globalGrainDirection
        ((localGrains.planeMap p) 1 / (localGrains.planeMap p) 0)) E)
      delta (1 - sigma) (100 * C) := by
  let v : Point3 := localGrains.planeMap p
  have hv_unit : ‖v‖ = 1 := localGrains.planeMap_unit p
  let B : Set Point3 := shading.union ∩ Metric.closedBall (p : Point3) (Real.sqrt delta)
  have h_local_ad : PureWZ2PaperADSet1 (scalarProjection v B) delta (1 - sigma) C :=
    localGrains.local_ad delta (le_refl delta) hdelta_le_one p
  have h_proj_sub : scalarProjection v E ⊆ scalarProjection v B := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, hE_sub hx, rfl⟩
  have h_ad_E : PureWZ2PaperADSet1 (scalarProjection v E) delta (1 - sigma) C :=
    PureWZ2PaperADSet1.mono_set h_local_ad h_proj_sub
  exact PureWZ2PaperADSet1.transfer_to_global_direction
    (z := z) (hE_height := hE_height) (hv_unit := hv_unit)
    (hv2 := hv2) (hv0 := hv0) (hAD := h_ad_E) (hdelta_le_one := hdelta_le_one)

end Kakeya.Assouad
