import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationCWATransport.John
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationCWATransport.Fiber.Index

/-!
# Fiber body transport through affine isometries

Composition chain, body carrier transport, index matching, and inverse volume bound.
-/

noncomputable section

open MeasureTheory JohnEllipsoid

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

variable (e : Point3 ≃ᵃⁱ[ℝ] Point3)

/-- The composition chain: φ ∘ normalization.map = normalization'.map ∘ e. -/
lemma unitRescaledFiber_compChain
    {ρ : ℝ} {G : Kakeya.Streamlined.TubeFamily ρ} {parent : Fin G.card}
    (normalization : WZ2PaperAssouadUnitRescalingData (G.tube parent))
    (normalization' : WZ2PaperAssouadUnitRescalingData ((imageTubeFamily e G).tube parent)) :
    ((normalization.map.symm.trans ((affineIsometryToEquiv e).trans normalization'.map)) ∘ normalization.map) =
    (normalization'.map ∘ e) := by
  funext x
  simp [AffineEquiv.trans_apply, affineIsometryToEquiv_apply e]
  <;> rfl

/-- The index equivalence commutes with the canonical full-fiber index ordering. -/
lemma unitRescaledFiber_indexMatch
    {δ ρ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {G : Kakeya.Streamlined.TubeFamily ρ}
    (parent : Fin G.card)
    (j : Fin (wz2PaperOrdinaryFullFiberIndices (imageTubeFamily e F) (imageTubeFamily e G) parent).card) :
    ((wz2PaperOrdinaryFullFiberIndexEquiv (fine := F) (coarse := G) parent)
        (unitRescaledFiber_indexEquiv e parent j)).1 =
    ((wz2PaperOrdinaryFullFiberIndexEquiv (fine := imageTubeFamily e F) (coarse := imageTubeFamily e G) parent)
        j).1 := by
  dsimp only [unitRescaledFiber_indexEquiv, wz2PaperOrdinaryFullFiberIndexEquiv]
  let S' := wz2PaperOrdinaryFullFiberIndices (imageTubeFamily e F) (imageTubeFamily e G) parent
  let S := wz2PaperOrdinaryFullFiberIndices F G parent
  have hS : S' = S := fullFiberIndices_image e parent
  have h_main : ∀ (s t : Finset (Fin F.card)) (h : t = s) (k : Fin t.card),
      (s.orderIsoOfFin rfl (Equiv.cast (congr_arg Fin (congr_arg Finset.card h)) k)).1 =
      (t.orderIsoOfFin rfl k).1 := by
    intro s t h k
    subst h
    <;> simp [Equiv.cast]
    <;> rfl
  exact h_main S S' hS j

/-- Transport body carriers through the affine equivalence. -/
lemma unitRescaledFiber_bodyCarrier
    {δ ρ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {G : Kakeya.Streamlined.TubeFamily ρ}
    (parent : Fin G.card)
    (normalization : WZ2PaperAssouadUnitRescalingData (G.tube parent))
    (normalization' : WZ2PaperAssouadUnitRescalingData ((imageTubeFamily e G).tube parent))
    (φ : Point3 ≃ᵃ[ℝ] Point3)
    (hphi_comp : φ ∘ normalization.map = normalization'.map ∘ e)
    (j : Fin (wz2PaperOrdinaryFullFiberIndices (imageTubeFamily e F) (imageTubeFamily e G) parent).card) :
    φ '' ((wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := F) (coarse := G) parent normalization).body
        (unitRescaledFiber_indexEquiv e parent j)).carrier =
    ((wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := imageTubeFamily e F) (coarse := imageTubeFamily e G) parent normalization').body
        j).carrier := by
  let F' := imageTubeFamily e F
  let G' := imageTubeFamily e G
  let sourceBodies :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily (fine := F) (coarse := G) parent normalization
  let targetBodies :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily (fine := F') (coarse := G') parent normalization'
  let srcIdx := (wz2PaperOrdinaryFullFiberIndexEquiv (fine := F) (coarse := G) parent)
                  (unitRescaledFiber_indexEquiv e parent j)
  let tgtIdx := (wz2PaperOrdinaryFullFiberIndexEquiv (fine := F') (coarse := G') parent) j
  have h_idx : srcIdx.1 = tgtIdx.1 := unitRescaledFiber_indexMatch e parent j
  have h_chain : ∀ (s : Set Point3),
      φ '' (normalization.map '' s) = normalization'.map '' (e '' s) := by
    intro s
    have h1 : φ '' (normalization.map '' s) = (φ ∘ normalization.map) '' s :=
      Set.image_image φ normalization.map s
    rw [h1, hphi_comp]
    exact (Set.image_image normalization'.map e s).symm
  have h_src : (sourceBodies.body (unitRescaledFiber_indexEquiv e parent j)).carrier =
      normalization.map '' (F.tube srcIdx.1).carrier := by
    rfl
  have h_tgt : (targetBodies.body j).carrier =
      normalization'.map '' (F'.tube tgtIdx.1).carrier := by
    rfl
  rw [h_src, h_tgt]
  rw [h_chain ((F.tube srcIdx.1).carrier)]
  have h1 : e '' (F.tube srcIdx.1).carrier = (F'.tube srcIdx.1).carrier :=
    (imageTubeFamily_carrier e F srcIdx.1).symm
  rw [h1]
  <;> congr <;> exact h_idx

/-- Inverse volume bound: if φ has determinant 1, then φ.symm preserves volume. -/
lemma unitRescaledFiber_invVol
    (φ : Point3 ≃ᵃ[ℝ] Point3)
    (hdet : |LinearMap.det (φ.linear : Point3 →ₗ[ℝ] Point3)| = 1)
    (targetSet : Set Point3) :
    volume (φ.symm '' targetSet) ≤ (1 : ENNReal) * volume targetSet := by
  have hvol_eq : volume (φ.symm '' targetSet) =
      ENNReal.ofReal |LinearMap.det (φ.symm.linear : Point3 →ₗ[ℝ] Point3)| * volume targetSet :=
    volume_affineEquiv_image (f := φ.symm) targetSet
  rw [hvol_eq]
  have hsymmdet : |LinearMap.det (φ.symm.linear : Point3 →ₗ[ℝ] Point3)| = 1 := by
    have h1 : φ.symm.linear = φ.linear.symm := by ext x; simp
    rw [h1]
    have h2 : LinearMap.det (φ.linear.symm : Point3 →ₗ[ℝ] Point3) =
        (LinearMap.det (φ.linear : Point3 →ₗ[ℝ] Point3))⁻¹ :=
      LinearEquiv.det_coe_symm φ.linear
    rw [h2, abs_inv, hdet] <;> norm_num
  rw [hsymmdet]
  <;> simp [one_mul]
  <;> rfl

end Kakeya.Assouad

end
