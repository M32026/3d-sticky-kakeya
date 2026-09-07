import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationCWATransport.Basic
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationCWATransport.John
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationCWATransport.Fiber

/-!
# Pure CWA transport through rigid isometries

Given an affine isometry `e` and two tube families whose carriers are
related by `e`, transport the pure Definition 2.12 nearby-scale CWA.

## Submodules

- `Basic`: image constructions, geometric and cover transport
- `John`: John ellipsoid transport through affine isometries
- `Fiber`: unit-rescaled full fiber data transport
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

variable (e : Point3 ≃ᵃⁱ[ℝ] Point3)

/-! ### Cover data transport -/

/-- Transport pure scale cover data through an isometry. -/
def scaleCoverData_image
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ} {rho : ℝ} {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData F rho C) :
    WZ2PaperPureScaleCoverData (imageTubeFamily e F) rho C :=
  let G' := imageTubeFamily e data.coarse
  { delta_pos := data.delta_pos
    rho_pos := data.rho_pos
    coarse := G'
    cover := purePartitioningCover_image e data.cover
    full_fiber_uniform := fullFiberUniform_image e data.full_fiber_uniform
    rescaledFiber := fun parent =>
      Nonempty.map
        (fun (d : WZ2PaperPureUnitRescaledFullFiberData (fine := F) (coarse := data.coarse) parent C) =>
          unitRescaledFiber_image (δ := δ) (ρ := rho) (F := F) (G := data.coarse) (C := C)
            e data.rho_pos parent d)
        (data.rescaledFiber parent) }

/-- Transport nearby scale cover data through an isometry. -/
def nearbyScaleCoverData_image
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {rho₀ : WZ2PaperRequestedScale δ} {C : ENNReal}
    (data : WZ2PaperPureNearbyScaleCoverData F rho₀ C) :
    WZ2PaperPureNearbyScaleCoverData (imageTubeFamily e F) rho₀ C :=
  { rho := data.rho
    requested_le := data.requested_le
    within_factor := data.within_factor
    scaleData := scaleCoverData_image e data.scaleData }

/-! ### Main theorem -/

/-- Pure Definition 2.12 nearby-scale CWA transports through rigid isometries. -/
theorem pureCWAAtNearbyScales_image
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ} {C : ENNReal}
    (h : WZ2PaperPureCWAAtNearbyScales F C) :
    WZ2PaperPureCWAAtNearbyScales (imageTubeFamily e F) C :=
  ⟨h.1, h.2.1, essentialDistinct_image e h.2.2.1,
    fun rho₀ =>
      have hne : Nonempty (WZ2PaperPureNearbyScaleCoverData F rho₀ C) := h.2.2.2 rho₀
      ⟨nearbyScaleCoverData_image e (Classical.choice hne)⟩⟩

end Kakeya.Assouad

end
