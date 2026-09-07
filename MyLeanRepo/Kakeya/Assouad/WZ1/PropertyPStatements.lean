import MyLeanRepo.Kakeya.Assouad.WZ1.RescaledFiberStatements

/-!
# Property-(P) consequences

Property (P) is selected after Proposition 5 has supplied one concrete
unit-rescaled extremal fiber.  It is therefore carried by
`WZ1PropertyPRescaledFiberData`, not by the raw Proposition 5 fiber.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Property (P) supplies a nearby point of the distinguished shading. -/
lemma WZ1PropertyPRescaledFiberData.nearby_distinguished
    {delta sigma inputLoss baseOutputLoss propertyOutputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := inputLoss) U Y rho}
    {parent : Fin (U.coarse rho).card}
    {hrho : 0 < rho.1}
    {base :
      WZ1UnitRescaledFiberData
        (inputLoss := inputLoss) (outputLoss := baseOutputLoss)
        balanced parent hrho}
    (selected :
      WZ1PropertyPRescaledFiberData
        (propertyOutputLoss := propertyOutputLoss) base) :
    ∀ p ∈ selected.fiber.sourceShading.union,
      ∃ q ∈ selected.fiber.sourceShading.carrier
          selected.fiber.distinguished,
        dist p q ≤ 2 * rho.1 := by
  intro p hp
  rcases selected.propertyP p hp with ⟨q, hq, hcell⟩
  exact
    ⟨q, hq,
      grid_cell_diameter
        (lt_of_lt_of_le balanced.refined_extremal.1 rho.2.1)
        hcell⟩

end Kakeya.Assouad
