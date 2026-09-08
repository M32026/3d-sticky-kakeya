import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.MultiscaleShifts

/-!
# Prefix groups for composed multiscale shifts

A composed translation is indexed by one choice at each level.  At any cut,
indices with the same prefix must form equal-size groups, while each total
shift splits into a group-dependent prefix sum and an index-dependent suffix
sum.  The suffix norm is bounded by the corresponding tail of the radius
budget.

This is the finite product bookkeeping needed before constructing
group-shared covers.  It is independent of the geometric choice of scales,
copy counts, or shift distributions.
-/

noncomputable section

open BigOperators

namespace Kakeya.Streamlined.RandomTranslation

/--
Every cut of a positive finite product of copy indices admits balanced prefix
groups and a compatible prefix/suffix decomposition of the composed shifts.

Two total-copy indices have the same group exactly when all choices strictly
before the cut agree.  Consequently every group has the same positive
cardinality.  The cumulative shift depends only on the group, while the
residual shift contains the levels at or after the cut and is bounded by the
tail radius sum.
-/
def HierarchicalPrefixGroupingStatement : Prop :=
  ∀ {M : ℕ},
    ∀ J : Fin M → ℕ,
      (∀ k, 0 < J k) →
      ∀ radius : Fin M → ℝ,
        (∀ k, 0 ≤ radius k) →
        ∀ shiftAt :
          (k : Fin M) → Fin (J k) → Point3,
          (∀ k j, ‖shiftAt k j‖ ≤ radius k) →
          ∀ cut : Fin (M + 1),
            ∃ (groupCount : ℕ)
              (group : Fin (multiscaleTotalJ J) → Fin groupCount)
              (cumulative : Fin groupCount → Point3)
              (residual : Fin (multiscaleTotalJ J) → Point3),
              0 < groupCount ∧
              Function.Surjective group ∧
              (∀ g h,
                (Finset.univ.filter fun i => group i = g).card =
                  (Finset.univ.filter fun i => group i = h).card) ∧
              (∀ g,
                0 <
                  (Finset.univ.filter fun i => group i = g).card) ∧
              (∀ i j,
                group i = group j ↔
                  ∀ k : Fin M, k.val < cut.val →
                    (finPiFinEquiv.symm i) k =
                      (finPiFinEquiv.symm j) k) ∧
              (∀ i,
                multiscaleShiftFun shiftAt i =
                  cumulative (group i) + residual i) ∧
              ∀ i,
                ‖residual i‖ ≤
                  ∑ k ∈
                    (Finset.univ.filter
                      fun k : Fin M => cut.val ≤ k.val),
                    radius k

end Kakeya.Streamlined.RandomTranslation
