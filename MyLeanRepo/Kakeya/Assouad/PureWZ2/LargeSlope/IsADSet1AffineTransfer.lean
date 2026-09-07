import MyLeanRepo.Kakeya.Assouad.WZ1.ADAffineThickeningTransport
import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# IsADSet1 affine transfer

Transfer an `IsADSet1` bound under a uniformly nondegenerate affine map
`t ↦ a*t + b` with `1/4 ≤ |a| ≤ 4`. The base scale is preserved and the
constant blows up by a factor of 10.

This is a thin wrapper around `IsADSet1.affine_image_covering` that also
repackages the covering bound into a full `IsADSet1` instance. It lives in
a separate file to isolate the expensive elaboration of the underlying
covering-number lemma.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Transfer an `IsADSet1` under an affine map, producing a new `IsADSet1`
with constant `10 * C`. -/
lemma IsADSet1.affine_transfer
    {E : Set ℝ} {delta alpha a b : ℝ} {C : ENNReal}
    (hE : IsADSet1 E delta alpha C)
    (ha1 : 1/4 ≤ |a|) (ha2 : |a| ≤ 4)
    (E' : Set ℝ) (h_eq : E' = (fun u : ℝ => a * u + b) '' E)
    (h_bounded : E' ⊆ Set.Icc (-4 : ℝ) 4) :
    IsADSet1 E' delta alpha (10 * C) := by
  have h_cover := IsADSet1.affine_image_covering (a := a) (b := b) hE ha1 ha2
  rcases hE with ⟨hδ, hα, hα1, hC, hE_bounded, hcover⟩
  have hC10_one : (1 : ENNReal) ≤ 10 * C := by
    have h1 : (1 : ENNReal) ≤ C := hC
    have h2 : (1 : ENNReal) ≤ (10 : ENNReal) := by norm_num
    have h3 : (1 : ENNReal) * (1 : ENNReal) ≤ (10 : ENNReal) * C := mul_le_mul' h2 h1
    simpa using h3
  refine' ⟨hδ, hα, hα1, hC10_one, h_bounded, _⟩
  intro rho hrho hdelta_rho hrho_one x r hrho_r hr_one
  have h := h_cover rho hrho hdelta_rho hrho_one x r hrho_r hr_one
  have h_set : E' ∩ Metric.closedBall x r = ((fun u : ℝ => a * u + b) '' E) ∩ Metric.closedBall x r := by
    rw [h_eq]
  rw [h_set]
  exact h

end Kakeya.Assouad
