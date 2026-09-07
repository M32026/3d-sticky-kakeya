import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointTransverseBudgetStatements

/-!
# Assemble the transverse endpoint leaf from one source-strip budget
-/

namespace Kakeya.Assouad

open scoped ENNReal

theorem wz1_wide_coarse_endpoint_transverse_budget_assembly :
    WZ1WideCoarseEndpointTransverseBudgetAssemblyStatement := by
  intro hBudget
  intro epsilon parameters hepsilon hepsilonOne
  rcases hBudget epsilon parameters hepsilon hepsilonOne with
    ⟨etaCap, hetaCap, hBudgetAt⟩
  refine ⟨etaCap, hetaCap, ?_⟩
  intro eta heta hetaSmall
  rcases hBudgetAt eta heta hetaSmall with
    ⟨delta₀, hdelta₀, hdelta₀One, hBudgetMain⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta F G₁ G₂ ambient active H
    hdelta hdeltaSmall data input normal hnormal hcoefficient
    level radius hradius hradiusOne
  have hbudget :
      WZ1WideCoarseEndpointSourceBudget
        (ambient := ambient) (active := active)
        parameters input normal level radius := by
    simpa [WZ1WideCoarseEndpointTransverseSourceBudget] using
      hBudgetMain hdelta hdeltaSmall data input
        normal hnormal hcoefficient level radius
        hradius hradiusOne
  exact
    wideCoarseEndpoint_sourceBudget_normalBound
      hdelta normal hnormal level radius hradius hbudget

end Kakeya.Assouad
