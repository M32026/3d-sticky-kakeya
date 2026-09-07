import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointAxialBudgetStatements

/-!
# Assemble the axial endpoint leaf from four exact source-strip budgets
-/

namespace Kakeya.Assouad

theorem wz1_wide_coarse_endpoint_axial_budget_assembly :
    WZ1WideCoarseEndpointAxialBudgetAssemblyStatement := by
  intro hProjectiveFrostman hProjectiveRaw
    hSmallCoefficient hDenominator
  intro epsilon parameters hepsilon hepsilonOne
  rcases hProjectiveFrostman epsilon parameters hepsilon hepsilonOne with
    ⟨etaProjectiveFrostman, hetaProjectiveFrostman,
      hProjectiveFrostmanAt⟩
  rcases hProjectiveRaw epsilon parameters hepsilon hepsilonOne with
    ⟨etaProjectiveRaw, hetaProjectiveRaw, hProjectiveRawAt⟩
  rcases hSmallCoefficient epsilon parameters hepsilon hepsilonOne with
    ⟨etaSmallCoefficient, hetaSmallCoefficient, hSmallCoefficientAt⟩
  rcases hDenominator epsilon parameters hepsilon hepsilonOne with
    ⟨etaDenominator, hetaDenominator, hDenominatorAt⟩
  let etaCap :=
    min etaProjectiveFrostman
      (min etaProjectiveRaw
        (min etaSmallCoefficient etaDenominator))
  have hetaCap : 0 < etaCap := by
    simp [etaCap, hetaProjectiveFrostman, hetaProjectiveRaw,
      hetaSmallCoefficient, hetaDenominator]
  refine ⟨etaCap, hetaCap, ?_⟩
  intro eta heta hetaSmall
  have hetaProjectiveFrostmanSmall :
      eta ≤ etaProjectiveFrostman :=
    hetaSmall.trans (min_le_left _ _)
  have hetaProjectiveRawSmall : eta ≤ etaProjectiveRaw :=
    hetaSmall.trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hetaSmallCoefficientSmall : eta ≤ etaSmallCoefficient :=
    hetaSmall.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hetaDenominatorSmall : eta ≤ etaDenominator :=
    hetaSmall.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  rcases
      hProjectiveFrostmanAt eta heta hetaProjectiveFrostmanSmall with
    ⟨deltaProjectiveFrostman, hdeltaProjectiveFrostman,
      hdeltaProjectiveFrostmanOne, hProjectiveFrostmanMain⟩
  rcases hProjectiveRawAt eta heta hetaProjectiveRawSmall with
    ⟨deltaProjectiveRaw, hdeltaProjectiveRaw,
      hdeltaProjectiveRawOne, hProjectiveRawMain⟩
  rcases
      hSmallCoefficientAt eta heta hetaSmallCoefficientSmall with
    ⟨deltaSmallCoefficient, hdeltaSmallCoefficient,
      hdeltaSmallCoefficientOne, hSmallCoefficientMain⟩
  rcases hDenominatorAt eta heta hetaDenominatorSmall with
    ⟨deltaDenominator, hdeltaDenominator,
      hdeltaDenominatorOne, hDenominatorMain⟩
  let delta₀ :=
    min deltaProjectiveFrostman
      (min deltaProjectiveRaw
        (min deltaSmallCoefficient deltaDenominator))
  have hdelta₀ : 0 < delta₀ := by
    simp [delta₀, hdeltaProjectiveFrostman, hdeltaProjectiveRaw,
      hdeltaSmallCoefficient, hdeltaDenominator]
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans hdeltaProjectiveFrostmanOne
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta F G₁ G₂ ambient active H
    hdelta hdeltaSmall data input normal hnormal haxial
    level radius hradius hradiusOne
  have hdeltaProjectiveFrostmanSmall :
      delta ≤ deltaProjectiveFrostman :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaProjectiveRawSmall : delta ≤ deltaProjectiveRaw :=
    hdeltaSmall.trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaSmallCoefficientSmall :
      delta ≤ deltaSmallCoefficient :=
    hdeltaSmall.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hdeltaDenominatorSmall : delta ≤ deltaDenominator :=
    hdeltaSmall.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  by_cases hprojective :
      WZ1WideCoarseEndpointAxialProjectiveBranch
        data.direction normal data.width
  · by_cases hsmallWidth :
        WZ1WideCoarseEndpointAxialProjectiveSmallWidth
          parameters data
    · have hbudget :=
        hProjectiveFrostmanMain hdelta hdeltaProjectiveFrostmanSmall
          data input normal hnormal haxial hprojective hsmallWidth
          level radius hradius hradiusOne
      exact
        wideCoarseEndpoint_sourceBudget_normalBound
          hdelta normal hnormal level radius hradius hbudget
    · have hbudget :=
        hProjectiveRawMain hdelta hdeltaProjectiveRawSmall
          data input normal hnormal haxial hprojective hsmallWidth
          level radius hradius hradiusOne
      exact
        wideCoarseEndpoint_sourceBudget_normalBound
          hdelta normal hnormal level radius hradius hbudget
  · by_cases hsmallCoefficient :
        WZ1WideCoarseEndpointAxialSmallCoefficient
          parameters data normal
    · have hbudget :=
        hSmallCoefficientMain hdelta hdeltaSmallCoefficientSmall
          data input normal hnormal haxial hprojective
          hsmallCoefficient level radius hradius hradiusOne
      exact
        wideCoarseEndpoint_sourceBudget_normalBound
          hdelta normal hnormal level radius hradius hbudget
    · have hbudget :=
        hDenominatorMain hdelta hdeltaDenominatorSmall
          data input normal hnormal haxial hprojective
          hsmallCoefficient level radius hradius hradiusOne
      exact
        wideCoarseEndpoint_sourceBudget_normalBound
          hdelta normal hnormal level radius hradius hbudget

end Kakeya.Assouad
