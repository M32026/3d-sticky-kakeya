import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.LensEndpointLocalization
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.GraphLensFromZeros
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.CurvatureSign
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.PerturbationPreservation

/-!
# Directional graph-lens existence input

This is the independent PYZ Lemma 37 leaf used by the robust bipartite
tangency reduction.  It constructs a graph lens after shifting one of two
well-separated functions upward or downward, and localizes both endpoints.
-/

namespace Kakeya.Cinematic

def DirectionalLensExistenceStatement : Prop :=
  ∀ {K tangency delta t : ℝ},
    1 ≤ K →
    5 ≤ tangency →
    0 < delta →
    0 < t →
    delta ≤ t →
    tangency ^ 50 * delta ≤ t / (1000 * K ^ 4) →
    ∀ {family : Set C2Function},
      HasCinematicCurvature family K →
      ∀ {w b : C2Function},
        w ≠ b →
        w ∈ family →
        b ∈ family →
        2 * t ≤ c2Distance w b →
        ∀ (R : CurvilinearRectangle delta t),
          R.IsLambdaTangent w tangency →
          R.IsLambdaTangent b tangency →
          ∀ (I : ParameterInterval),
            I.IsControlled K →
            R.interval.carrier ⊆ I.centeredCarrier (1 / 4) →
            ∀ epsilon : ℝ,
              (2 * tangency + 2) * delta < epsilon →
              epsilon ≤ 25 * tangency ^ 10 * delta →
              ∀ shift0_w shift0_b : ℝ,
                |shift0_w| ≤ delta →
                |shift0_b| ≤ delta →
                let d := c2Distance w b
                let V := 25 * tangency ^ 10 + 2 * tangency + 2
                let curvature := d / (6 * K * t)
                let E :=
                  2 * (2 * V + d / t) / curvature +
                    Real.sqrt (2 * V / curvature)
                (∃ L : GraphLens,
                    L.left ∈ I.carrier ∧
                    L.right ∈ I.carrier ∧
                    (L.left : ℝ) ∈
                      Set.Icc
                        (R.interval.left - E * Real.sqrt (delta / t))
                        (R.interval.right + E * Real.sqrt (delta / t)) ∧
                    (L.right : ℝ) ∈
                      Set.Icc
                        (R.interval.left - E * Real.sqrt (delta / t))
                        (R.interval.right + E * Real.sqrt (delta / t)) ∧
                    L.f =
                      w.verticalTranslate (epsilon + shift0_w) ∧
                    L.g = b.verticalTranslate shift0_b) ∨
                  (∃ L : GraphLens,
                    L.left ∈ I.carrier ∧
                    L.right ∈ I.carrier ∧
                    (L.left : ℝ) ∈
                      Set.Icc
                        (R.interval.left - E * Real.sqrt (delta / t))
                        (R.interval.right + E * Real.sqrt (delta / t)) ∧
                    (L.right : ℝ) ∈
                      Set.Icc
                        (R.interval.left - E * Real.sqrt (delta / t))
                        (R.interval.right + E * Real.sqrt (delta / t)) ∧
                    L.f =
                      w.verticalTranslate (-epsilon + shift0_w) ∧
                    L.g = b.verticalTranslate shift0_b)

end Kakeya.Cinematic
