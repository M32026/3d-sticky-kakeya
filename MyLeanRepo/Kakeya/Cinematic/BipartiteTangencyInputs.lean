import MyLeanRepo.Kakeya.Cinematic.Statements
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Lenses

/-!
# Explicit inputs for PYZ Proposition 26

These propositions separate the Marcus--Tardos lens-counting core from the
random-sampling and scale-reduction step that upgrades the restricted
bipartite estimate to the full statement.
-/

namespace Kakeya.Cinematic

/-- The finite perturbation statement used to remove improper tangencies. -/
def FiniteTangencyPerturbationStatement : Prop :=
  ∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
    ∀ family : Set C2Function,
      IsCinematicFamily family K D →
      ∀ I : ParameterInterval, I.IsControlled K →
        ∀ F : FiniteFunctionFamily, F.carrier ⊆ family →
          ∀ epsilon : ℝ, 0 < epsilon →
            ∃ shift : C2Function → ℝ,
              (∀ f ∈ F.carrier, |shift f| ≤ epsilon) ∧
              F.HasNoExactTangenciesOn I shift

/--
Build the restricted, well-separated bipartite tangency theorem from the
non-overlapping graph-lens bound and the required cinematic geometry.
-/
def BipartiteTangencyCoreFromGraphLensesStatement : Prop :=
  GraphLensBoundStatement →
    TwoZerosStatement →
    TangencyGeometryCompletionStatement →
    CommonTangentRectangleStatement →
    ComparableRectanglesStatement →
    RectanglePackingStatement →
    FiniteTangencyPerturbationStatement →
    BipartiteTangencyCoreStatement

/--
Build the unit-multiplicity tangency-dilation-stable theorem from graph
lenses.

This leaf contains the actual lens-existence, perturbation, non-overlap, and
Marcus--Tardos argument.
-/
def BipartiteTangencyRobustUnitCoreFromGraphLensesStatement : Prop :=
  GraphLensBoundStatement →
    TwoZerosStatement →
    TangencyGeometryCompletionStatement →
    CommonTangentRectangleRobustStatement →
    ComparableRectanglesStatement →
    RectanglePackingStatement →
    FiniteTangencyPerturbationStatement →
    BipartiteTangencyRobustUnitCoreStatement

/--
Upgrade the unit-multiplicity robust lens bound to arbitrary `mu,nu` by
two-sided finite sampling.
-/
def BipartiteTangencyRobustCoreFromUnitStatement : Prop :=
  BipartiteTangencyRobustUnitCoreStatement →
    BipartiteTangencyRobustCoreStatement

/--
The scale and incomparability reductions from the tangency-dilation-stable
restricted theorem to full PYZ Proposition 26.
-/
def BipartiteTangencyReductionStatement : Prop :=
  PolynomialRectangleRefinementStatement →
    CommonTangentRectangleRobustStatement →
    BipartiteTangencyRobustCoreStatement →
    BipartiteTangencyStatement

/--
The full bipartite tangency estimate with an arbitrary fixed tangency
dilation. Both the separation loss `A` and the tangency dilation are kept
polynomially explicit.
-/
def BipartiteTangencyRobustFullStatement : Prop :=
  ∀ K : ℝ, 1 ≤ K →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ tangency : ℝ, 5 ≤ tangency →
        ∀ family : Set C2Function,
          HasCinematicCurvature family K →
          ∀ I : ParameterInterval, I.IsControlled K →
            ∀ A delta t : ℝ,
              1 ≤ A → 0 < delta → 0 < t →
              delta ≤ t → t ≤ 1 → delta ≤ A * t →
              ∀ W B : FiniteFunctionFamily,
                W.carrier ⊆ family →
                B.carrier ⊆ family →
                (∀ ⦃f⦄, f ∈ W.carrier ∨ f ∈ B.carrier →
                  ∀ ⦃g⦄, g ∈ W.carrier ∨ g ∈ B.carrier →
                    dist f g ≤ 6 * t) →
                W.AreSeparated B (t / A) →
                ∀ R : RectangleFamily delta t,
                  R.CentersIn family →
                  R.IsOverCentralQuarterOf I →
                  R.IsPairwiseIncomparable family 100 →
                  R.Nonempty →
                  ∀ mu nu : ℕ, 0 < mu → 0 < nu →
                    (∀ i,
                      mu ≤ RectangleFamily.tangentCount
                        (R.rectangle i) W tangency ∧
                      nu ≤ RectangleFamily.tangentCount
                        (R.rectangle i) B tangency) →
                    (R.card : ℝ) ≤
                      C * Real.rpow tangency C * Real.rpow A C *
                        Real.rpow
                            (RectangleFamily.bipartiteNormalizedCount
                              W B mu nu)
                            (3 / 2 : ℝ) *
                          Real.log
                            (RectangleFamily.bipartiteNormalizedCount
                              W B mu nu)

end Kakeya.Cinematic
