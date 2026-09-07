import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SuffixBranchingProfileStatement

/-!
# A large suffix after a prescribed initial scale

The paper's scale decomposition starts at a small positive normalized scale,
not at zero.  This variant selects the cumulative-excess minimum only among
levels at or after a prescribed starting level.
-/

noncomputable section

namespace Kakeya.Assouad

def SuffixBranchingProfileFromStatement : Prop :=
  ∀ N : ℕ,
    0 < N →
      ∀ n d epsilon avgLow : ℝ,
        0 ≤ d →
        d < n →
        0 < epsilon →
        epsilon < 1 →
        ∀ a : Fin (N + 1) → ℝ,
          ∀ t : Fin N → ℝ,
            a 0 = 0 →
            a (Fin.last N) = 1 →
            (∀ i : Fin N,
              a i.castSucc < a i.succ) →
            (∀ i : Fin N, 0 ≤ t i ∧ t i ≤ n) →
            avgLow ≤
              ∑ i : Fin N,
                t i *
                  (a i.succ - a i.castSucc) →
            ∀ start : Fin N,
              (n - d) *
                  (epsilon ^ 2 +
                    a start.castSucc) <
                avgLow - d →
              ∃ k : Fin N,
                start.val ≤ k.val ∧
                a k.castSucc <
                  1 - epsilon ^ 2 ∧
                suffixProfileCumulative
                    a t k.castSucc ≤
                  d * a k.castSucc +
                    (n - d) *
                      a start.castSucc ∧
                ∀ j : Fin (N + 1),
                  k.val ≤ j.val →
                    d *
                        (a j -
                          a k.castSucc) ≤
                      suffixProfileCumulative a t j -
                        suffixProfileCumulative
                          a t k.castSucc

end Kakeya.Assouad
