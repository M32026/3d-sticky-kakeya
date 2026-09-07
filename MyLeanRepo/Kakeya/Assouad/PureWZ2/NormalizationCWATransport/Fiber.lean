import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationCWATransport.Fiber.Index
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationCWATransport.Fiber.Body

/-!
# Fiber data transport through affine isometries

Transports `WZ2PaperPureUnitRescaledFullFiberData` through an affine isometry.

## Submodules

- `Fiber.Index`: index equivalence and matching
- `Fiber.Body`: composition chain, body carrier transport, inverse volume bound
-/

noncomputable section

open MeasureTheory JohnEllipsoid

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

variable (e : Point3 ≃ᵃⁱ[ℝ] Point3)

/-- Transport unit-rescaled full fiber data through an isometry. -/
theorem unitRescaledFiber_image
    {δ ρ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {G : Kakeya.Streamlined.TubeFamily ρ} {C : ENNReal}
    (hrho : 0 < ρ) (parent : Fin G.card)
    (fiberData : WZ2PaperPureUnitRescaledFullFiberData
        (fine := F) (coarse := G) parent C) :
    WZ2PaperPureUnitRescaledFullFiberData
        (fine := imageTubeFamily e F) (coarse := imageTubeFamily e G) parent C := by
  let F' := imageTubeFamily e F
  let G' := imageTubeFamily e G
  let normalization := fiberData.normalization
  let normalization' : WZ2PaperAssouadUnitRescalingData (G'.tube parent) :=
    WZ2PaperAssouadUnitRescalingData.ofTube (G'.tube parent) hrho
  let sourceBodies :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := F) (coarse := G) parent normalization
  let targetBodies :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := F') (coarse := G') parent normalization'
  let e' := affineIsometryToEquiv e
  let φ : Point3 ≃ᵃ[ℝ] Point3 :=
    normalization.map.symm.trans (e'.trans normalization'.map)
  let indexEquiv : Fin (wz2PaperOrdinaryFullFiberIndices F' G' parent).card ≃
      Fin (wz2PaperOrdinaryFullFiberIndices F G parent).card :=
    unitRescaledFiber_indexEquiv (F := F) (G := G) e parent
  have hvol : volume normalization'.parent_convex_body.outerJohnEllipsoid =
      volume normalization.parent_convex_body.outerJohnEllipsoid :=
    unitRescaledFiber_volume_eq e normalization normalization'
  have hphi_comp : φ ∘ normalization.map = normalization'.map ∘ e :=
    unitRescaledFiber_compChain e normalization normalization'
  have hcarrier : ∀ (j : Fin (wz2PaperOrdinaryFullFiberIndices F' G' parent).card),
      φ '' (sourceBodies.body (indexEquiv j)).carrier ⊆
      (targetBodies.body j).carrier := by
    intro j
    have h_eq := unitRescaledFiber_bodyCarrier e parent normalization normalization' φ hphi_comp j
    rw [h_eq]
  have h_phi_lin : φ.linear =
      (normalization.map.symm.linear).trans
        ((affineIsometryToEquiv e).linear.trans normalization'.map.linear) := by
    simp [φ, e'] <;> rfl
  have hdet : |LinearMap.det (φ.linear : Point3 →ₗ[ℝ] Point3)| = 1 := by
    rw [h_phi_lin]
    exact unitRescaledFiber_phi_det_one e normalization normalization' hvol
  have hinvvol : ∀ (targetSet : Set Point3),
      volume (φ.symm '' targetSet) ≤ (1 : ENNReal) * volume targetSet :=
    fun targetSet => unitRescaledFiber_invVol φ hdet targetSet
  have hbound := wz2PaperBodyConvexWolffBound_of_affineTransport
    (source := sourceBodies) (target := targetBodies)
    φ indexEquiv hcarrier hinvvol fiberData.convex_wolff
  exact ⟨normalization', by simpa [one_mul] using hbound⟩

end Kakeya.Assouad

end
