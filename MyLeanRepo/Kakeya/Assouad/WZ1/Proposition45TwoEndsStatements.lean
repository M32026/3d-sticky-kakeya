import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements

/-!
# Two-ends statement boundary for WZ1 Proposition 8.9
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- Raw strip nonconcentration produced by the paper's Lemma 8.10. -/
def WZ1RawStripNonconcentration
    (delta zeta width : ℝ) (set : DiscreteSet 2) : Prop :=
  ∀ normal : Point2, ‖normal‖ = 1 →
    ∀ level radius : ℝ, delta ≤ radius →
      ((set.filter fun point =>
          |inner ℝ point normal - level| ≤ radius).card : ENNReal) ≤
        ENNReal.ofReal
            ((Real.rpow width zeta)⁻¹ *
              Real.rpow radius zeta) *
          set.enncard

/--
Raw strip nonconcentration after a quantitative active-vertex restriction.
The extra constant records the loss in (8.30).
-/
def WZ1WeightedRawStripNonconcentration
    (delta zeta width : ℝ) (constant : ENNReal)
    (set : DiscreteSet 2) : Prop :=
  ∀ normal : Point2, ‖normal‖ = 1 →
    ∀ level radius : ℝ, delta ≤ radius →
      ((set.filter fun point =>
          |inner ℝ point normal - level| ≤ radius).card : ENNReal) ≤
        constant *
          ENNReal.ofReal
            ((Real.rpow width zeta)⁻¹ *
              Real.rpow radius zeta) *
          set.enncard

end Kakeya.Assouad
