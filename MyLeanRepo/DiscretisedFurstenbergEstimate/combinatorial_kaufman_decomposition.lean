module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.MainAssembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.TubeNull
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.ProcessIntervalsResult
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Combinatorial Kaufman decomposition

This is the real-variable kernel of OS Lemma 8.4 and Proposition 8.1.
It is deliberately stated before any dyadic-set dictionary is applied.

The output intervals are macroscopic, have disjoint interiors, cover all but
`O(ε)` of the logarithmic scale interval, and retain the required total slope.
Each retained block is either regular with slope at least `s`, or merely
superlinear with slope exactly `s`.
-/

noncomputable section

/--
Quantitative interval decomposition used to choose the structured scales.

The constants `A` and `τ` are selected before `m` and `f`.  This quantifier
order is essential: allowing `τ` to depend on `f` would not give a bounded
number of scale blocks.
-/
theorem combinatorial_kaufman_decomposition
    (s t : ℝ)
    (hs : 0 < s) (hst : s < t) (ht : t ≤ 2) :
    ∃ A : ℝ, A = 1 + 6 / (t - s) ∧
      ∀ ε : ℝ, 0 < ε → A * ε < t - s →
        ∃ τ : ℝ, 0 < τ ∧ τ ≤ ε ∧
          ∀ (m : ℝ) (f : ℝ → ℝ),
            0 < m →
            LipschitzOnWith 2 f (Set.Icc 0 m) →
            MonotoneOn f (Set.Icc 0 m) →
            f 0 = 0 →
            (∀ x ∈ Set.Icc 0 m, t * x - ε * m ≤ f x) →
            ∃ (n : ℕ) (I : Fin n → ℝ × ℝ),
              0 < n ∧
              PairwiseInteriorDisjoint I ∧
              (∀ i,
                0 ≤ (I i).1 ∧
                (I i).1 < (I i).2 ∧
                (I i).2 ≤ m ∧
                τ * m ≤ (I i).2 - (I i).1) ∧
              (1 - A * ε) * m ≤
                ∑ i, ((I i).2 - (I i).1) ∧
              (t - A * ε) * m ≤
                ∑ i,
                  ((I i).2 - (I i).1) *
                    chordSlope f (I i).1 (I i).2 ∧
              (∀ i,
                (EpsilonLinear f (A * ε) (I i).1 (I i).2 ∧
                    s ≤ chordSlope f (I i).1 (I i).2 ∧
                    chordSlope f (I i).1 (I i).2 ≤ 2) ∨
                (EpsilonSuperlinear f (A * ε) (I i).1 (I i).2 ∧
                    chordSlope f (I i).1 (I i).2 = s)) := by
  exact CombinatorialKaufman.MainAssembly.combinatorial_kaufman_assembly
    s t hs hst ht
    CombinatorialKaufman.TubeNull.tubeNull_result
    CombinatorialKaufman.ProcessIntervalsResult.processIntervals_result
