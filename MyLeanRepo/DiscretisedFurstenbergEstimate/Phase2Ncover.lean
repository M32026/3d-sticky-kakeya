module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Phase2

/-- Covering number at scale `δ`, as `ENNReal`. -/
def Ncover {X : Type*} [PseudoMetricSpace X] (δ : ℝ) (P : Set X) : ENNReal :=
  Metric.externalCoveringNumber δ.toNNReal P

end DirecretisedFurstenbergEstimate.Phase2

end
