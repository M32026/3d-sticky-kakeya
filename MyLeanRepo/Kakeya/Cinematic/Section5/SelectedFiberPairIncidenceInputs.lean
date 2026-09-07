import MyLeanRepo.Kakeya.Cinematic.Section5.ProductScalePairIncidenceInputs

/-!
# Pair incidence for selected fine-rectangle fibers

This is the finite Lemmas 45--46 assembly for arbitrary selected function
fibers `G'(R)`.  Each selected fiber supplies many good ordered pairs, while
the product-scale fixed-pair theorem bounds the number of fine rectangles
containing one pair.  The ambient function support is explicit and need only
contain the selected fibers.
-/

namespace Kakeya.Cinematic

def SelectedFiberPairIncidenceStatement : Prop :=
  ProductScaleFixedPairIncidenceStatement →
    TangencyGeometryCompletionStatement →
    FinePairIncidenceBoundStatement →
    PairIncidenceCountingStatement →
    ∀ K D : ℝ,
      1 ≤ K →
      1 ≤ D →
      ∃ C_inc : ℝ, 0 < C_inc ∧
        ∀ {delta t metricLower tangencyLower Cc : ℝ},
          0 < delta →
          0 < t →
          0 < metricLower →
          0 < tangencyLower →
          10 * delta ≤ metricLower / (6 * K) →
          100 ≤ Cc →
          Cc * delta ≤ t →
          ∀ {family : Set C2Function},
            IsCinematicFamily family K D →
            ∀ {I : ParameterInterval},
              I.IsControlled K →
              ∀ (R : RectangleFamily delta t),
                R.IsOverCentralQuarterOf I →
                R.IsPairwiseIncomparable family Cc →
                ∀ (ambient : FiniteFunctionFamily),
                  ambient.carrier ⊆ family →
                  ∀ selectedFiber : Fin R.card → Finset C2Function,
                    (∀ i,
                      (selectedFiber i : Set C2Function) ⊆
                        ambient.carrier) →
                    (∀ i, ∀ function ∈ selectedFiber i,
                      (R.rectangle i).IsLambdaTangent function 5) →
                    ∀ q : ℕ,
                      0 < q →
                      (∀ i, q ≤ (selectedFiber i).card) →
                      (∀ i,
                        (selectedFiber i).card ^ 2 ≤
                          3 * (((selectedFiber i).product
                            (selectedFiber i)).filter fun pair =>
                              metricLower <
                                  c2Distance pair.2 pair.1 ∧
                                tangencyLower ≤
                                  tangencyParameterOn I
                                    pair.2 pair.1 + delta).card) →
                      (R.card : ℝ) * (q : ℝ) ^ 2 ≤
                        3 * (ambient.card : ℝ) ^ 2 *
                          (C_inc *
                              Real.sqrt
                                (delta * t /
                                  (metricLower * tangencyLower)) +
                            1)

end Kakeya.Cinematic
