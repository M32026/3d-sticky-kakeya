import MyLeanRepo.Kakeya.Assouad.PropStickyPaperExactBalancingMassRetentionStatements

/-!
# Paper refinement after exact balancing

Boundary pruning and exact whole-cell balancing both restrict all tube
shadings by one global union of literal `delta`-cells.  Once the boundary
loss and the finite cell-count loss are absorbed, their final shading is a
genuine paper refinement on the same tube family.
-/

noncomputable section

namespace Kakeya.Assouad

def wz2PaperPostBalancingLoss
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {multiplicityCap : ENNReal}
    (pruning :
      WZ2PaperBoundaryCellPruningData
        (rho := rho) shading hdelta multiplicityCap) : ENNReal :=
  let availableCellCount :=
    ∑ coarseCell ∈ pruning.coarseCells,
      (pruning.availableFineCells coarseCell).card
  (8 : ENNReal) *
    ((Nat.log 2 availableCellCount + 1 : ℕ) : ENNReal)

structure WZ2PaperPostBalancingRefinementData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (multiplicityCap : ENNReal)
    (pruning :
      WZ2PaperBoundaryCellPruningData
        (rho := rho) shading hdelta multiplicityCap)
    (balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) pruning.pruned pruning.coarseCells
        pruning.availableFineCells)
    (multiplicityLevel logExponent : ℕ) where
  massData :
    WZ2PaperExactBalancingMassRetentionData
      shading hdelta multiplicityCap pruning balancing
      multiplicityLevel
  source_mass_le :
    shading.mass ≤
      wz2PaperPostBalancingLoss pruning *
        balancing.refined.mass
  retained_mass :
    wz1PaperRefinementFraction delta logExponent *
        shading.mass ≤
      balancing.refined.mass

namespace WZ2PaperPostBalancingRefinementData

noncomputable def toRefinement
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {multiplicityCap : ENNReal}
    {pruning :
      WZ2PaperBoundaryCellPruningData
        (rho := rho) shading hdelta multiplicityCap}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) pruning.pruned pruning.coarseCells
        pruning.availableFineCells}
    {multiplicityLevel logExponent : ℕ}
    (data :
      WZ2PaperPostBalancingRefinementData
        shading hdelta multiplicityCap pruning balancing
        multiplicityLevel logExponent) :
    WZ1PaperRefinement shading logExponent where
  selected :=
    { family := fine
      embedding := Equiv.toEmbedding (Equiv.refl (Fin fine.card))
      tube_eq := fun _ => rfl }
  refined := balancing.refined
  subshading := fun index => by
    exact
      (balancing.refined_subshading index).trans
        (pruning.pruned_subshading index)
  retained_mass := data.retained_mass

end WZ2PaperPostBalancingRefinementData

def WZ2PaperPostBalancingRefinementStatement : Prop :=
  WZ2PaperExactBalancingMassRetentionStatement →
  ∀ {delta rho : ℝ},
    ∀ (hdelta : 0 < delta),
      ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
        ∀ (shading : WZ1PaperTubeShading fine),
          ∀ (multiplicityLevel : ℕ),
            (∀ point ∈ shading.union,
              (2 ^ multiplicityLevel : ENNReal) ≤
                  (shading.pointMultiplicity point : ENNReal) ∧
                (shading.pointMultiplicity point : ENNReal) <
                  (2 ^ (multiplicityLevel + 1) : ENNReal)) →
            ∀ (multiplicityCap : ENNReal),
              ∀ (pruning :
                  WZ2PaperBoundaryCellPruningData
                    (rho := rho) shading hdelta multiplicityCap),
                ∀ (balancing :
                    WZ2PaperExactCellBalancingData
                      (rho := rho) pruning.pruned
                      pruning.coarseCells
                      pruning.availableFineCells),
                  multiplicityCap *
                        ENNReal.ofReal (1000 * delta / rho) ≤
                      pruning.pruned.mass →
                  ∀ (logExponent : ℕ),
                    wz1PaperRefinementFraction delta logExponent *
                          wz2PaperPostBalancingLoss pruning ≤
                        1 →
                    Nonempty
                      (WZ2PaperPostBalancingRefinementData
                        shading hdelta multiplicityCap pruning
                        balancing multiplicityLevel logExponent)

end Kakeya.Assouad

end
