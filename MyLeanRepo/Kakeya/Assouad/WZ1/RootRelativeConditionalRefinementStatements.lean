import MyLeanRepo.Kakeya.Assouad.WZ1.RootRelativeCoverRelations

/-!
# Finite-schedule root-relative regularization

This is the first replacement boundary for the retired recursive
`WZ1BalancedCoverCoreStatement`.

For a prescribed finite WZ1 scale schedule and recursion depth, it keeps one
same-family subshading of the original root family.  Parent identities always
come from the original `UniformTubeStructure`; all nonempty cells cut out by
at most `depth + 1` of those independent parent coordinates are balanced.
No `UniformTubeStructure (U.coarse rho)` is constructed.
-/

namespace Kakeya.Assouad

/--
Simultaneously regularize all root-parent coordinate cells needed by a fixed
finite WZ1 scale schedule.

The power `2 * depth` records the two conditional-cardinality comparisons
used at each recursive split.  The schedule and depth are chosen before the
small-scale threshold.
-/
def WZ1RootRelativeConditionalRefinementStatement : Prop :=
  ∀ sigma sourceLoss : ℝ, 0 < sourceLoss →
    ∀ depth : ℕ, 1 ≤ depth →
      ∀ scaleCount : ℕ, 0 < scaleCount →
        ∀ epsilon : ℝ, 0 < epsilon →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ F : Kakeya.Streamlined.TubeFamily delta,
              ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                ∀ Y : Kakeya.Streamlined.TubeShading F,
                  WZ1ExtremalPair sigma sourceLoss F U Y →
                  ∀ schedule :
                      Fin scaleCount →
                        Kakeya.Streamlined.AdmissibleScale delta,
                    ∃ refined :
                        Kakeya.Streamlined.TubeShading F,
                      IsSubshading refined Y ∧
                      0 < refined.mass ∧
                      Kakeya.realRpowENN delta epsilon * Y.mass ≤
                        refined.mass ∧
                      ∃ C : ENNReal,
                        1 ≤ C ∧
                        C ≠ ⊤ ∧
                        C ^ (2 * depth) ≤
                          Kakeya.realRpowENN delta (-epsilon) ∧
                        WZ1RootScheduledConditionalUniformity
                          depth U refined schedule C

end Kakeya.Assouad
