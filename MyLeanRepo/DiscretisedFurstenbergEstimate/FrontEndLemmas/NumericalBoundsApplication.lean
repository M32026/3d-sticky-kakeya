module

/-
  FrontEndLemmas.NumericalBoundsApplication

  Helper lemma to apply ParameterSelectionNumericalHypotheses without
  unfolding the huge irreducible type inside the dense front_end_composition
  proof context.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction.ParameterSelection
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction

noncomputable section

set_option allowUnsafeReducibility true
attribute [local reducible] ParameterSelectionNumericalHypotheses

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas

/-- Apply ParameterSelectionNumericalHypotheses to get the numerical bounds data.
    Extracted to a separate module to avoid OOM from unfolding the huge irreducible
    type inside the dense front_end_composition proof context. -/
def apply_numerical_hypotheses
    {s t ε η_upper η_axiom δ₀_axiom A δ₀ Δ δ K_pack M : ℝ}
    (h_num_bounds : ParameterSelectionNumericalHypotheses s t ε η_upper η_axiom δ₀_axiom A δ₀)
    (hΔ_pos : 0 < Δ) (hΔ_lt_δ₀ : Δ < δ₀) (hδ_pos : 0 < δ) (hδ_eq : δ = Δ^2)
    (hK_pos : 0 < K_pack) (hK_bound : K_pack ≤ Real.rpow Δ (-2 * ε) / 6)
    (hM_pos : 0 < M) (hM_lower : M / 2 ≥ Real.rpow Δ (-2 * s + 2 * ε))
    (hM_upper : M ≤ Real.rpow Δ (-2 * s - ε)) :=
  h_num_bounds Δ δ K_pack M hΔ_pos hΔ_lt_δ₀ hδ_pos hδ_eq
    hK_pos hK_bound hM_pos hM_lower hM_upper

end DirecretisedFurstenbergEstimate.FrontEndLemmas
