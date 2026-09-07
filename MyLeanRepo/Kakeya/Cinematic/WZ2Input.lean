import MyLeanRepo.Kakeya.Cinematic.Statements
import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.PolynomialScaleCoarseCountInputs
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Cinematic input consumed by WZ2

This is the normalized form of WZ1 Theorem 7.2 recalled in Section 7 of WZ2.
It is intentionally separate from the more general PYZ Theorem 1.7: the full
paper theorem is the reusable source result, while `WZ2CinematicInput` is the
stable interface consumed by the Assouad workstream.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Cinematic

/--
The special cinematic maximal estimate used by WZ2.

WZ2 first extracts a one-dimensional Katz--Tao set and maps it into a
cinematic family through a fixed bi-Lipschitz parametrization. The constants
`C_KT` and `lambda` absorb the resulting fixed non-concentration and graph
neighborhood dilation factors. The final loss `epsilon` is independent of
those fixed constants.
-/
def WZ2CinematicInput : Prop :=
  ∀ K D C_KT lambda : ℝ,
    1 ≤ K → 1 ≤ D → 1 ≤ C_KT → 1 ≤ lambda →
    ∀ family : Set C2Function,
      IsCinematicFamily family K D →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧
          delta₀ ≤ 1 / lambda ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ F : FiniteFunctionFamily,
              F.carrier ⊆ family →
              F.IsDeltaSeparated delta →
              F.HasKatzTaoBound delta C_KT →
              eLpNorm (multiplicity F (lambda * delta)) (3 / 2 : ENNReal)
                  MeasureTheory.volume ≤
                ENNReal.ofReal (Real.rpow delta (-epsilon))

/--
The local integral form of the WZ2 cinematic estimate.

The estimate is uniform over vertical unit strips. This is the genuine
paper-level core; the passage to the global `L^(3/2)` norm uses only bounded
support, strip covering, and absorption of a family-dependent constant.
-/
def WZ2LocalIntegralInput : Prop :=
  ∀ K D C_KT lambda : ℝ,
    1 ≤ K → 1 ≤ D → 1 ≤ C_KT → 1 ≤ lambda →
    ∀ family : Set C2Function,
      IsCinematicFamily family K D →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧
          delta₀ ≤ 1 / lambda ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ F : FiniteFunctionFamily,
              F.carrier ⊆ family →
              F.IsDeltaSeparated delta →
              F.HasKatzTaoBound delta C_KT →
              ∀ c : ℝ,
                (∫ p in (Set.Icc 0 1 ×ˢ Set.Icc c (c + 1)),
                  Real.rpow (multiplicity F (lambda * delta) p)
                    (3 / 2 : ℝ)) ≤
                  Real.rpow delta (-epsilon)

/--
Uniform dyadic level-set estimate containing the geometric content of PYZ
Section 5.

The passage from this estimate to `WZ2LocalIntegralInput` is purely analytic:
dyadic multiplicity selection, restricted weak type, and logarithmic
absorption.
-/
def WZ2LocalLevelSetInput : Prop :=
  ∀ K D C_KT lambda : ℝ,
    1 ≤ K → 1 ≤ D → 1 ≤ C_KT → 1 ≤ lambda →
    ∀ family : Set C2Function,
      IsCinematicFamily family K D →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧
          delta₀ ≤ 1 / lambda ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ F : FiniteFunctionFamily,
              F.carrier ⊆ family →
              F.IsDeltaSeparated delta →
              F.HasKatzTaoBound delta C_KT →
              ∀ c : ℝ,
                ∀ mu : ℕ, 0 < mu →
                  ∀ E₀ : Set (ℝ × ℝ),
                    MeasurableSet E₀ →
                    E₀ ⊆ Set.Icc 0 1 ×ˢ Set.Icc c (c + 1) →
                    (∀ p ∈ E₀,
                      (mu : ℝ) ≤ multiplicity F (lambda * delta) p ∧
                        multiplicity F (lambda * delta) p < 2 * mu) →
                    volume E₀ ≤
                      ENNReal.ofReal
                        (Real.rpow delta (-epsilon) *
                          Real.rpow (mu : ℝ) (-3 / 2 : ℝ))

/--
The short-curve level-set estimate corresponding to PYZ Lemma 39.

The substantive Section 5 geometry is applied only where the horizontal
coordinate lies in the centered sixteenth of one fixed controlled interval.
The passage from this statement to `WZ2LocalLevelSetInput` is a separate
finite-interval restriction/globalization argument.
-/
def WZ2ShortCurveLevelSetInput : Prop :=
  ∀ K D C_KT lambda : ℝ,
    1 ≤ K → 1 ≤ D → 1 ≤ C_KT → 1 ≤ lambda →
    ∀ family : Set C2Function,
      IsCinematicFamily family K D →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧
          delta₀ ≤ 1 / lambda ∧
          ∀ I : ParameterInterval, I.IsControlled K →
            ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
              ∀ F : FiniteFunctionFamily,
                F.carrier ⊆ family →
                F.IsDeltaSeparated delta →
                F.HasKatzTaoBound delta C_KT →
                ∀ c : ℝ,
                  ∀ mu : ℕ, 0 < mu →
                    ∀ E₀ : Set (ℝ × ℝ),
                      MeasurableSet E₀ →
                      E₀ ⊆
                        I.realCenteredCarrier (1 / 16) ×ˢ
                          Set.Icc c (c + 1) →
                      (∀ p ∈ E₀,
                        (mu : ℝ) ≤ multiplicity F (lambda * delta) p ∧
                          multiplicity F (lambda * delta) p < 2 * mu) →
                      volume E₀ ≤
                        ENNReal.ofReal
                          (Real.rpow delta (-epsilon) *
                            Real.rpow (mu : ℝ) (-3 / 2 : ℝ))

/--
Paper inputs for the substantive Section 5 level-set geometry.

This proposition contains the shading, fine/coarse rectangle, bilinear
incidence, and bipartite-extraction work. It is intentionally separate from
the already-proved analytic level-set-to-integral reduction.
-/
def WZ2LocalLevelSetFromPaperInputsStatement : Prop :=
  FineToCoarseContainmentStatement →
    FineTangencyLiftToCoarseStatement →
    SeparatedTangentBallPairStatement →
    SharedTangentBallPairPigeonholeStatement →
    TangencyGeometryCompletionStatement →
    ComparableRectanglesStatement →
    RectanglePackingStatement →
    ComparabilityTransitivityStatement →
    PolynomialScaleCoarseRectangleCountStatement →
    RectangleSubfamilySelectionStatement →
    RectangleRefinementStatement →
    BipartiteTangencyStatement →
    TwoEndsSelectionStatement →
    TangencyTwoEndsSelectionStatement →
    FineRectangleAssignmentStatement →
    GoodPairCountingStatement →
    PairIncidenceCountingStatement →
    WZ2LocalLevelSetInput

/-- Assemble the local integral once the Section 5 level-set core is known. -/
def WZ2LocalIntegralFromPaperInputsStatement : Prop :=
  WZ2LocalLevelSetInput →
    MultiplicityLevelSelectionStatement →
    RestrictedWeakTypeReductionStatement →
    WZ2LocalIntegralInput

end Kakeya.Cinematic
