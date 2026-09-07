import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationCWATransport.Basic

/-!
# Fiber index transport through affine isometries

Index equivalence for full fiber transport.

The matching lemma `unitRescaledFiber_indexMatch` lives in `Body.lean`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

variable (e : Point3 ≃ᵃⁱ[ℝ] Point3)

/-- Construct the index equivalence between source and target full fiber index sets. -/
def unitRescaledFiber_indexEquiv
    {δ ρ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {G : Kakeya.Streamlined.TubeFamily ρ}
    (parent : Fin G.card) :
    Fin (wz2PaperOrdinaryFullFiberIndices (imageTubeFamily e F) (imageTubeFamily e G) parent).card ≃
    Fin (wz2PaperOrdinaryFullFiberIndices F G parent).card :=
  have hS := fullFiberIndices_image e parent
  have hfindices : _ := congr_arg Finset.card hS
  Equiv.cast (congr_arg Fin hfindices)

end Kakeya.Assouad

end
