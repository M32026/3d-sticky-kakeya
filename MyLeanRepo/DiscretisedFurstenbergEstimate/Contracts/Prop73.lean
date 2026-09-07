module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.BoundedStatement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CombiningInductionWithBound

@[expose] public section

open scoped ENNReal NNReal

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

/-- OS Proposition 7.3, bounded-consumer form. Given `UniformIncidenceData`,
    produces a uniform combining induction with explicit C' upper bound. -/
theorem prop73_main
    (s : ℝ)
    (hs : 0 < s)
    (hs1 : s < 1) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ t ε_inc : ℝ,
        s < t →
        t < 2 →
        0 < ε_inc →
        CombiningInductionUniform_with_data_bounded
          s t ε_inc K := by
  exact combining_induction_uniform_with_data_bounded s hs hs1

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
