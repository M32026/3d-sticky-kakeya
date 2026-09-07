import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64CriticalFloorAssembly

/-!
# Quantitative Proposition 6.4 producer boundaries

These construction-private statements retain the terminal multiplicity and
indexed-mass receipts needed by the critical-floor assembly.  In particular,
they do not factor through the provenance-erasing plain hierarchy or vertical
producer statements in `Node05ConditionalAssembly`.

The existing plain `PureWZ2MixedHierarchyConstructionData` has no quantitative
terminal receipt, so it cannot be adapted to the hierarchy boundary below.
A genuine `PureWZ2QuantitativeMixedRawHierarchyData` can instead be normalized
by `PureWZ2QuantitativeMixedRawHierarchyData.toQuantitativeNormalizedHierarchyOutput`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Construction-private Lemma-8 producer retaining the quantitative
hierarchy receipt consumed by the critical-floor assembly.

The requested final-scale threshold precedes the source-scale threshold,
exactly as in the frozen plain producer API.
-/
def PureWZ2QuantitativeVerticalRediscretizationProducerStatement : Prop :=
  ∀ sigma workLoss outputLoss targetDelta₀ : ℝ,
    0 < workLoss → 0 < outputLoss → 0 < targetDelta₀ →
      ∃ sourceDelta₀ : ℝ, 0 < sourceDelta₀ ∧
        ∀ sourceDelta : ℝ,
          0 < sourceDelta → sourceDelta ≤ sourceDelta₀ →
            ∀ quantitativeOutput :
                PureWZ2QuantitativeNormalizedHierarchyOutput
                  sigma workLoss sourceDelta,
              ∃ finalDelta : ℝ,
                0 < finalDelta ∧ finalDelta ≤ targetDelta₀ ∧
                  Nonempty
                    (PureWZ2VerticalRediscretizationData
                      quantitativeOutput.normalized.prepared.normalized
                        finalDelta outputLoss)

/-- Construction-private hierarchy producer whose output still contains the
terminal multiplicity and indexed-mass receipts.  This is the narrow open
boundary required by the quantitative Proposition 6.4 route; a plain
`PureWZ2BudgetedHierarchyOutput` is deliberately insufficient.
-/
def PureWZ2QuantitativeNormalizedHierarchyFromCriticalStatement : Prop :=
  PureWZ2PropStickyCapability →
    PureWZ2PaperADBridgeStatement →
      PureWZ2GrainsFromCriticalStatement →
        ∀ sigma : ℝ,
          PureWZ2CriticalPackage sigma →
            ∀ workLoss sourceDelta₀ : ℝ,
              0 < workLoss → 0 < sourceDelta₀ →
                ∃ sourceDelta : ℝ,
                  0 < sourceDelta ∧ sourceDelta ≤ sourceDelta₀ ∧
                    Nonempty
                      (PureWZ2QuantitativeNormalizedHierarchyOutput
                        sigma workLoss sourceDelta)

/-- The two quantitative construction-private producers imply the unchanged
paper-facing Node-5 statement without passing through either plain producer
boundary.
-/
theorem pureWZ2_c2_grains_of_quantitative_producers
    (hierarchyProducer :
      PureWZ2QuantitativeNormalizedHierarchyFromCriticalStatement)
    (verticalProducer :
      PureWZ2QuantitativeVerticalRediscretizationProducerStatement) :
    PureWZ2C2GrainsStatement := by
  intro subunit criticalExtraction propSticky grains
  have propStickyOutput :=
    propSticky subunit criticalExtraction
  rcases propStickyOutput with ⟨propStickyCapability⟩
  have grainsOutput :=
    grains subunit criticalExtraction propSticky
  have hierarchyFromCritical :=
    hierarchyProducer
      propStickyCapability grainsOutput.1 grainsOutput.2
  intro sigma critical outputLoss targetDelta₀
    houtputLoss htargetDelta₀
  let workLoss : ℝ := outputLoss / 2
  have hworkLoss : 0 < workLoss := by
    dsimp only [workLoss]
    positivity
  rcases verticalProducer sigma workLoss outputLoss targetDelta₀
      hworkLoss houtputLoss htargetDelta₀ with
    ⟨sourceDelta₀, hsourceDelta₀, verticalAt⟩
  rcases hierarchyFromCritical sigma critical workLoss sourceDelta₀
      hworkLoss hsourceDelta₀ with
    ⟨sourceDelta, hsourceDelta, hsourceSmall, quantitativeOutput⟩
  rcases quantitativeOutput with ⟨quantitativeOutput⟩
  rcases verticalAt sourceDelta hsourceDelta hsourceSmall quantitativeOutput with
    ⟨finalDelta, hfinalDelta, hfinalSmall, final⟩
  rcases final with ⟨final⟩
  exact
    ⟨finalDelta, hfinalDelta, hfinalSmall,
      ⟨final.toC2GrainConfiguration⟩⟩

end Kakeya.Assouad

end
