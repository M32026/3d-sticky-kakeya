module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

abbrev Ncover {X : Type*} [PseudoMetricSpace X] (δ : ℝ) (E : Set X) : ENNReal :=
  Metric.externalCoveringNumber δ.toNNReal E

end DirecretisedFurstenbergEstimate.Section9

end
