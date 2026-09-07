import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FirstCrossing

/-!
# A suffix with uniformly large average branching dimension

Paper Lemma 7.10 merges adjacent scale intervals until their dimensions are
increasing.  The downstream argument only uses one consequence: there is an
early scale after which every initial suffix has average dimension at least a
fixed target.

For a finite profile this follows by choosing the last minimum of the
cumulative excess over the target dimension.  This formulation avoids
formalizing an irrelevant concrete merge algorithm while preserving exactly
the paper invariant used by the local Frostman argument.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Weighted branching accumulated strictly before the scale `j`. -/
def suffixProfileCumulative
    {N : ℕ}
    (a : Fin (N + 1) → ℝ)
    (t : Fin N → ℝ)
    (j : Fin (N + 1)) : ℝ :=
  ∑ i : Fin N,
    if i.val < j.val then
      t i * (a i.succ - a i.castSucc)
    else 0

/--
Select an early level after which every finite suffix has average branching
dimension at least `d`.

The strict gap condition ensures that the selected level lies before
normalized scale `1 - epsilon²`.  The suffix inequality is the exact input
needed to prove the normalized Frostman bound for the selected grid cell.
-/
def SuffixBranchingProfileStatement : Prop :=
  ∀ N : ℕ,
    0 < N →
      ∀ n d epsilon avgLow : ℝ,
        0 ≤ d →
        d < n →
        0 < epsilon →
        epsilon < 1 →
        (n - d) * epsilon ^ 2 < avgLow - d →
          ∀ a : Fin (N + 1) → ℝ,
            ∀ t : Fin N → ℝ,
              a 0 = 0 →
              a (Fin.last N) = 1 →
              (∀ i : Fin N, a i.castSucc < a i.succ) →
              (∀ i : Fin N, 0 ≤ t i ∧ t i ≤ n) →
              avgLow ≤
                ∑ i : Fin N,
                  t i * (a i.succ - a i.castSucc) →
                ∃ k : Fin N,
                  a k.castSucc < 1 - epsilon ^ 2 ∧
                    suffixProfileCumulative a t k.castSucc ≤
                      d * a k.castSucc ∧
                    ∀ j : Fin (N + 1),
                      k.val ≤ j.val →
                        d * (a j - a k.castSucc) ≤
                          suffixProfileCumulative a t j -
                            suffixProfileCumulative a t k.castSucc

end Kakeya.Assouad
