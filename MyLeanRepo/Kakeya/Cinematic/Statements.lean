import MyLeanRepo.Kakeya.Cinematic.Geometry

/-!
# Frozen statements for the PYZ cinematic proof

This module contains propositions only. It has no proof placeholders and does
not import any target theorem. Leaf targets import this file and
receive earlier mathematical results as ordinary hypotheses, so proof issues
can run independently.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Cinematic

def PreliminaryDichotomyStatement : Prop :=
  ∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
    ∀ family : Set C2Function,
      IsCinematicFamily family K D →
      ∀ I : ParameterInterval, I.IsShort K →
        ∀ f ∈ family, ∀ g ∈ family,
          ((∀ x ∈ I.carrier,
              |f x - g x| < (3 * K)⁻¹ * c2Distance f g) ∨
            (∀ x ∈ I.carrier,
              (6 * K)⁻¹ * c2Distance f g ≤ |f x - g x|)) ∧
          ((∀ x ∈ I.carrier,
              |f.firstDeriv x - g.firstDeriv x| <
                (3 * K)⁻¹ * c2Distance f g) ∨
            (∀ x ∈ I.carrier,
              (6 * K)⁻¹ * c2Distance f g ≤
                |f.firstDeriv x - g.firstDeriv x|)) ∧
          (((∀ x ∈ I.carrier,
              |f x - g x| < (3 * K)⁻¹ * c2Distance f g) ∧
            (∀ x ∈ I.carrier,
              |f.firstDeriv x - g.firstDeriv x| <
                (3 * K)⁻¹ * c2Distance f g)) →
            ∀ x ∈ I.carrier,
              (6 * K)⁻¹ * c2Distance f g ≤
                |f.secondDeriv x - g.secondDeriv x|)

def TwoZerosStatement : Prop :=
  ∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
    ∀ family : Set C2Function,
      IsCinematicFamily family K D →
      ∀ I : ParameterInterval, I.IsShort K →
        ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
          ∀ x₁ x₂ x₃ : UnitPoint,
            x₁ ∈ I.carrier → x₂ ∈ I.carrier → x₃ ∈ I.carrier →
            (x₁ : ℝ) < x₂ → (x₂ : ℝ) < x₃ →
            f x₁ = g x₁ → f x₂ = g x₂ → f x₃ = g x₃ →
            False

def TangencySublevelDiameterStatement : Prop :=
  ∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
    ∃ C : ℝ, 0 < C ∧
      ∀ family : Set C2Function,
        IsCinematicFamily family K D →
        ∀ I : ParameterInterval, I.IsShort K →
          ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
            ∀ delta : ℝ, 0 < delta →
              delta ≤ c2Distance f g / (6 * K) →
              ∀ x ∈ tangencySublevelSetOn I f g delta,
                ∀ y ∈ tangencySublevelSetOn I f g delta,
                  |(x : ℝ) - y| ≤
                    C * Real.sqrt
                      ((tangencyParameterOn I f g + delta) /
                        c2Distance f g)

def CommonTangentRectangleStatement : Prop :=
  ∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
    ∃ C : ℝ, 0 < C ∧
      ∀ family : Set C2Function,
        IsCinematicFamily family K D →
        ∀ I : ParameterInterval, I.IsControlled K →
          ∀ delta t : ℝ, 0 < delta → delta ≤ t → t ≤ 1 →
            ∀ R : CurvilinearRectangle delta t,
              R.function ∈ family →
              R.IsOverCentralQuarterOf I →
              ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
                R.IsLambdaTangent f 5 →
                R.IsLambdaTangent g 5 →
                (tangencyParameterOn I f g + delta) *
                    c2Distance f g ≤
                  C * delta * t

/--
The polynomially uniform form of PYZ Lemma 17 for an arbitrary tangency
constant.

The fixed-`5` statement is sufficient inside the normalized core, but the
scale change in Lemma 28 turns `5`-tangency into `O(A)`-tangency.  The
dependence on that dilation must therefore remain explicit.
-/
def CommonTangentRectangleRobustStatement : Prop :=
  ∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ tangency : ℝ, 1 ≤ tangency →
        ∀ family : Set C2Function,
          IsCinematicFamily family K D →
          ∀ I : ParameterInterval, I.IsControlled K →
            ∀ delta t : ℝ, 0 < delta → delta ≤ t → t ≤ 1 →
              ∀ R : CurvilinearRectangle delta t,
                R.function ∈ family →
                R.IsOverCentralQuarterOf I →
                ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
                  R.IsLambdaTangent f tangency →
                  R.IsLambdaTangent g tangency →
                  (tangencyParameterOn I f g + delta) *
                      c2Distance f g ≤
                    C * Real.rpow tangency C * delta * t

def ComparableRectanglesStatement : Prop :=
  ∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
    ∃ C : ℝ, 0 < C ∧
      ∀ family : Set C2Function,
        IsCinematicFamily family K D →
        ∀ I : ParameterInterval, I.IsControlled K →
          ∀ delta t lambda : ℝ,
            0 < delta → delta ≤ t → 1 ≤ lambda →
            ∀ R S : CurvilinearRectangle delta t,
              R.function ∈ family → S.function ∈ family →
              R.IsOverCentralQuarterOf I →
              S.IsOverCentralQuarterOf I →
              R.AreLambdaComparable S family lambda →
              max R.interval.right S.interval.right -
                  min R.interval.left S.interval.left ≤
                Real.sqrt (lambda * delta / t) ∧
              ∀ x ∈ R.intervalHullCarrier S,
                |R.function x - S.function x| ≤
                  C * Real.rpow lambda 3 * delta

def RectanglePackingStatement : Prop :=
  ∀ K : ℝ, 1 ≤ K →
    ∃ C : ℝ, 0 < C ∧
      ∀ family : Set C2Function,
        HasCinematicCurvature family K →
        ∀ I : ParameterInterval, I.IsShort K →
          ∀ delta t lambda : ℝ,
            0 < delta → delta ≤ t → t ≤ 1 → 100 ≤ lambda →
            ∀ center : C2Function,
              ∀ R : RectangleFamily delta t,
                R.CentersIn family →
                R.IsOverCentralQuarterOf I →
                R.IsPairwiseIncomparable family 100 →
                (∀ i,
                  c2Distance center (R.rectangle i).function ≤ 3 * t) →
                ∀ U : CurvilinearRectangle (lambda * delta) t,
                  (∀ i, (R.rectangle i).carrier ⊆ U.carrier) →
                  (R.card : ℝ) ≤
                    C * Real.rpow lambda (5 / 2 : ℝ)

def BipartiteTangencyStatement : Prop :=
  ∀ K : ℝ, 1 ≤ K →
    ∃ C : ℝ, 0 < C ∧
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
                    mu ≤ RectangleFamily.tangentCount (R.rectangle i) W 5 ∧
                    nu ≤ RectangleFamily.tangentCount (R.rectangle i) B 5) →
                  (R.card : ℝ) ≤
                    C * Real.rpow A C *
                      Real.rpow
                          (RectangleFamily.bipartiteNormalizedCount W B mu nu)
                          (3 / 2 : ℝ) *
                        Real.log
                          (RectangleFamily.bipartiteNormalizedCount W B mu nu)

/-- Basic correctness properties of centered interval scaling. -/
def IntervalScalingStatement : Prop :=
  (∀ I : ParameterInterval, ∀ q r : ℝ,
      0 ≤ q → q ≤ r →
        I.centeredCarrier q ⊆ I.centeredCarrier r) ∧
  (∀ I : ParameterInterval,
      I.centeredCarrier 1 = I.carrier) ∧
  (∀ I : ParameterInterval, ∀ q : ℝ, 0 ≤ q →
      ∀ x ∈ I.centeredCarrier q,
        ∀ y ∈ I.centeredCarrier q,
          |(x : ℝ) - y| ≤ q * I.length)

/-- Attainment and closedness properties behind the tangency parameter API. -/
def TangencyApiStatement : Prop :=
  ∀ I : ParameterInterval, ∀ f g : C2Function,
    0 ≤ tangencyParameterOn I f g ∧
    (∃ x ∈ I.centeredCarrier (1 / 2),
      tangencyParameterOn I f g =
        |f x - g x| + |f.firstDeriv x - g.firstDeriv x|) ∧
    ∀ delta : ℝ, IsClosed (tangencySublevelSetOn I f g delta)

/-- PYZ Corollary 21 with a uniform output comparability constant. -/
def ComparabilityTransitivityStatement : Prop :=
  ∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
    ∀ lambda₁ lambda₂ : ℝ, 1 ≤ lambda₁ → 1 ≤ lambda₂ →
      ∃ lambda₃ : ℝ, 1 ≤ lambda₃ ∧
        ∀ family : Set C2Function,
          IsCinematicFamily family K D →
          ∀ I : ParameterInterval, I.IsControlled K →
            ∀ delta t : ℝ, 0 < delta → delta ≤ t →
              IsAdmissibleComparisonScale delta t lambda₃ →
              ∀ R₁ R₂ R₃ : CurvilinearRectangle delta t,
                R₁.function ∈ family →
                R₂.function ∈ family →
                R₃.function ∈ family →
                R₁.IsOverCentralQuarterOf I →
                R₂.IsOverCentralQuarterOf I →
                R₃.IsOverCentralQuarterOf I →
                R₁.AreLambdaComparable R₂ family lambda₁ →
                R₂.AreLambdaComparable R₃ family lambda₂ →
                R₁.AreLambdaComparable R₃ family lambda₃

/-- PYZ Lemma 25: a coarse polynomial bound from doubling. -/
def CoarseRectangleCountStatement : Prop :=
  ∀ D : ℝ, 1 ≤ D →
    ∃ C : ℝ, 0 < C ∧
      ∀ K : ℝ, 1 ≤ K →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ t lambda : ℝ,
              delta ≤ t → t ≤ 1 → 100 ≤ lambda →
              IsAdmissibleComparisonScale delta t lambda →
              ∀ family : Set C2Function,
                IsCinematicFamily family K D →
                ∀ I : ParameterInterval, I.IsShort K →
                  ∀ R : RectangleFamily delta t,
                    R.CentersIn family →
                    R.IsOverCentralQuarterOf I →
                    R.IsPairwiseIncomparable family lambda →
                    (R.card : ℝ) ≤ Real.rpow delta (-C)

/-- Finite greedy existence of a maximal incomparable rectangle subfamily. -/
def RectangleSubfamilySelectionStatement : Prop :=
  ∀ delta t : ℝ, ∀ family : Set C2Function,
    ∀ C : ℝ, 100 ≤ C →
      ∀ R : RectangleFamily delta t,
        R.CentersIn family →
        ∃ S : RectangleSubfamily R,
          S.family.CentersIn family ∧
          S.family.IsPairwiseIncomparable family C ∧
          ∀ i : Fin R.card,
            ∃ j : Fin S.card,
              i = S.embedding j ∨
                (R.rectangle i).AreLambdaComparable
                  (S.family.rectangle j) family C

/-- Remaining geometric content of PYZ Lemma 16 plus Lemma 18. -/
def TangencyGeometryCompletionStatement : Prop :=
  ∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
    ∃ C : ℝ, 0 < C ∧
      ∀ family : Set C2Function,
        IsCinematicFamily family K D →
        ∀ I : ParameterInterval, I.IsControlled K →
          ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
            ∀ delta : ℝ, 0 < delta →
              delta ≤ c2Distance f g / (6 * K) →
              let scale :=
                Real.sqrt
                  ((tangencyParameterOn I f g + delta) *
                    c2Distance f g)
              (∃ pieces : IntervalFamily,
                pieces.card ≤ 2 ∧
                tangencySublevelSetOn I f g delta = pieces.union ∧
                pieces.AllLengthsLE (C * delta / scale) ∧
                ∀ x ∈ tangencySublevelSetOn I f g (delta / 2),
                  ∃ j : Fin pieces.card,
                    x ∈ (pieces.interval j).carrier ∧
                    delta ≤ C * scale * (pieces.interval j).length) ∧
              ∀ J : ParameterInterval,
                J.carrier ⊆ I.centeredCarrier (1 / 4) →
                (∀ x ∈ J.carrier, |f x - g x| ≤ delta) →
                ∀ lambda : ℝ, 1 ≤ lambda →
                  ∀ x ∈ I.carrier,
                    x ∈ J.centeredCarrier lambda →
                    |f x - g x| ≤ C * lambda^2 * delta

/-- PYZ Lemma 16(2b)--(2c), separated from interval propagation. -/
def TangencySublevelStructureStatement : Prop :=
  ∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
    ∃ C : ℝ, 0 < C ∧
      ∀ family : Set C2Function,
        IsCinematicFamily family K D →
        ∀ I : ParameterInterval, I.IsControlled K →
          ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
            ∀ delta : ℝ, 0 < delta →
              delta ≤ c2Distance f g / (6 * K) →
              let scale :=
                Real.sqrt
                  ((tangencyParameterOn I f g + delta) *
                    c2Distance f g)
              ∃ pieces : IntervalFamily,
                pieces.card ≤ 2 ∧
                tangencySublevelSetOn I f g delta = pieces.union ∧
                pieces.AllLengthsLE (C * delta / scale) ∧
                ∀ x ∈ tangencySublevelSetOn I f g (delta / 2),
                  ∃ j : Fin pieces.card,
                    x ∈ (pieces.interval j).carrier ∧
                    delta ≤ C * scale * (pieces.interval j).length

/--
The strictly convex/concave branch of PYZ Lemma 16(2b)--(2c).

All preliminary dichotomy, diameter, and calculus facts are explicit
hypotheses so this long real-analysis branch can be proved independently.
-/
def ConvexTangencySublevelCaseStatement : Prop :=
  ∀ K Cdiam : ℝ, 1 ≤ K → 0 < Cdiam →
    ∃ C : ℝ, 0 < C ∧
      ∀ I : ParameterInterval,
        I.IsControlled K →
        ∀ f g : C2Function, f ≠ g →
          ∀ delta : ℝ, 0 < delta →
            delta ≤ c2Distance f g / (6 * K) →
            (∀ x ∈ I.carrier,
              |f x - g x| < (3 * K)⁻¹ * c2Distance f g) →
            (∀ x ∈ I.carrier,
              |f.firstDeriv x - g.firstDeriv x| <
                (3 * K)⁻¹ * c2Distance f g) →
            (∀ x ∈ I.carrier,
              (6 * K)⁻¹ * c2Distance f g ≤
                |f.secondDeriv x - g.secondDeriv x|) →
            let E := tangencySublevelSetOn I f g delta
            let Ehalf := tangencySublevelSetOn I f g (delta / 2)
            (∀ x ∈ E, ∀ y ∈ E,
              |(x : ℝ) - y| ≤
                Cdiam * Real.sqrt
                  ((tangencyParameterOn I f g + delta) /
                    c2Distance f g)) →
            ∃ pieces : IntervalFamily,
              pieces.card ≤ 2 ∧
              E = pieces.union ∧
              pieces.AllLengthsLE
                (C * delta /
                  Real.sqrt
                    ((tangencyParameterOn I f g + delta) *
                      c2Distance f g)) ∧
              ∀ x ∈ Ehalf,
                ∃ j : Fin pieces.card,
                  x ∈ (pieces.interval j).carrier ∧
                  delta ≤ C *
                    Real.sqrt
                      ((tangencyParameterOn I f g + delta) *
                        c2Distance f g) *
                    (pieces.interval j).length

/-- Assemble all branches of Lemma 16(2b)--(2c) from the convex core. -/
def TangencySublevelStructureFromConvexStatement : Prop :=
  TangencyApiStatement →
    IntervalScalingStatement →
    TangencySublevelDiameterStatement →
    ConvexTangencySublevelCaseStatement →
    TangencySublevelStructureStatement

/-- PYZ Lemma 18, separated from sublevel decomposition. -/
def TangencyIntervalExtensionStatement : Prop :=
  ∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
    ∃ C : ℝ, 0 < C ∧
      ∀ family : Set C2Function,
        IsCinematicFamily family K D →
        ∀ I : ParameterInterval, I.IsControlled K →
          ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
            ∀ delta : ℝ, 0 < delta →
              delta ≤ c2Distance f g / (6 * K) →
              ∀ J : ParameterInterval,
                J.carrier ⊆ I.centeredCarrier (1 / 4) →
                (∀ x ∈ J.carrier, |f x - g x| ≤ delta) →
                ∀ lambda : ℝ, 1 ≤ lambda →
                  ∀ x ∈ I.carrier,
                    x ∈ J.centeredCarrier lambda →
                    |f x - g x| ≤ C * lambda^2 * delta

/-- Reassemble the original combined geometry package. -/
def TangencyGeometryAssemblyStatement : Prop :=
  TangencySublevelStructureStatement →
    TangencyIntervalExtensionStatement →
      TangencyGeometryCompletionStatement

/-- PYZ Lemmas 22 and 24: shrinking and large incomparable refinement. -/
def RectangleRefinementStatement : Prop :=
  (∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
    ∀ c : ℝ, 0 < c → c < 1 →
      ∃ C : ℝ, 100 ≤ C ∧
        ∀ family : Set C2Function,
          IsCinematicFamily family K D →
          ∀ I : ParameterInterval, I.IsControlled K →
            ∀ delta t : ℝ, 0 < delta → delta ≤ t → t ≤ 1 →
              IsAdmissibleComparisonScale delta t C →
              ∀ R S R' S' : CurvilinearRectangle delta t,
                R.function ∈ family → S.function ∈ family →
                R.IsOverCentralQuarterOf I →
                S.IsOverCentralQuarterOf I →
                R'.IsCenteredShrinkOf R c →
                S'.IsCenteredShrinkOf S c →
                R.AreLambdaIncomparable S family C →
                R'.AreLambdaIncomparable S' family 100) ∧
  (∀ K : ℝ, 1 ≤ K →
    ∀ C : ℝ, 100 ≤ C →
      ∃ retention : ℝ, 0 < retention ∧ retention ≤ 1 ∧
        ∀ family : Set C2Function,
          HasCinematicCurvature family K →
          ∀ I : ParameterInterval, I.IsControlled K →
            ∀ delta t : ℝ, 0 < delta → delta ≤ t → t ≤ 1 →
              IsAdmissibleComparisonScale delta t C →
              ∀ center : C2Function,
                ∀ R : RectangleFamily delta t,
                  R.CentersIn family →
                  R.IsOverCentralQuarterOf I →
                  R.IsPairwiseIncomparable family 100 →
                  (∀ i,
                    c2Distance center (R.rectangle i).function ≤ 3 * t) →
                  ∃ S : RectangleSubfamily R,
                    S.family.IsPairwiseIncomparable family C ∧
                    retention * (R.card : ℝ) ≤ (S.card : ℝ))

/--
The quantitative form of PYZ Lemma 24.

The proof of Lemma 24 uses Lemmas 20 and 23, whose losses are polynomial in
the requested comparison constant.  Recording that dependence is necessary
when the comparison constant itself grows with the tangency dilation in
Lemma 28.
-/
def PolynomialRectangleRefinementStatement : Prop :=
  ∀ K : ℝ, 1 ≤ K →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ comparison : ℝ, 100 ≤ comparison →
        ∀ family : Set C2Function,
          HasCinematicCurvature family K →
          ∀ I : ParameterInterval, I.IsControlled K →
            ∀ delta t : ℝ, 0 < delta → delta ≤ t →
              IsAdmissibleComparisonScale delta t comparison →
              ∀ center : C2Function,
                ∀ R : RectangleFamily delta t,
                  R.CentersIn family →
                  R.IsOverCentralQuarterOf I →
                  R.IsPairwiseIncomparable family 100 →
                  (∀ i,
                    c2Distance center (R.rectangle i).function ≤
                      comparison * t) →
                  ∃ S : RectangleSubfamily R,
                    S.family.IsPairwiseIncomparable family comparison ∧
                    (R.card : ℝ) ≤
                      C * Real.rpow comparison C * (S.card : ℝ)

/-- The restricted regime used as the core of PYZ Proposition 26. -/
def BipartiteTangencyCoreStatement : Prop :=
  ∀ K : ℝ, 1 ≤ K →
    ∃ c₂ Cc C : ℝ,
      0 < c₂ ∧ 100 ≤ Cc ∧ 0 < C ∧
      ∀ family : Set C2Function,
        HasCinematicCurvature family K →
        ∀ I : ParameterInterval, I.IsControlled K →
          ∀ delta t : ℝ, 0 < delta → 0 < t →
            delta ≤ t → t ≤ 1 →
            delta ≤ c₂ * t / 2 →
            IsAdmissibleComparisonScale delta t Cc →
            ∀ W B : FiniteFunctionFamily,
              W.carrier ⊆ family →
              B.carrier ⊆ family →
              W.AreSeparated B (2 * t) →
              ∀ R : RectangleFamily delta t,
                R.CentersIn family →
                R.IsOverCentralQuarterOf I →
                R.IsPairwiseIncomparable family Cc →
                R.Nonempty →
                ∀ mu nu : ℕ, 0 < mu → 0 < nu →
                  (∀ i,
                    mu ≤ RectangleFamily.tangentCount (R.rectangle i) W 5 ∧
                    nu ≤ RectangleFamily.tangentCount (R.rectangle i) B 5) →
                  (R.card : ℝ) ≤
                    C *
                      Real.rpow
                          (RectangleFamily.bipartiteNormalizedCount W B mu nu)
                          (3 / 2 : ℝ) *
                        Real.log
                          (RectangleFamily.bipartiteNormalizedCount W B mu nu)

/--
The tangency-dilation-stable restricted regime behind PYZ Lemma 28.

Shrinking a `(delta,t)` rectangle to the scale
`(delta / (2 * A), t / (2 * A))` preserves its parameter interval and turns
`t / A` separation into `2 * (t / (2 * A))` separation.  Its tangency
constant, however, grows from `5` to `10 * A`.  The restricted theorem must
therefore be polynomially uniform in that tangency constant; the fixed-`5`
core above is not by itself a sufficient black-box premise for the
separation reduction.
-/
def BipartiteTangencyRobustCoreStatement : Prop :=
  ∀ K : ℝ, 1 ≤ K →
    ∃ c₂ C : ℝ,
      0 < c₂ ∧ 100 ≤ C ∧
      ∀ tangency : ℝ, 5 ≤ tangency →
        ∀ family : Set C2Function,
          HasCinematicCurvature family K →
          ∀ I : ParameterInterval, I.IsControlled K →
            ∀ delta t : ℝ, 0 < delta → 0 < t →
              delta ≤ t → t ≤ 1 →
              Real.rpow tangency C * delta ≤ c₂ * t / 2 →
              IsAdmissibleComparisonScale delta t
                (C * Real.rpow tangency C) →
              ∀ W B : FiniteFunctionFamily,
                W.carrier ⊆ family →
                B.carrier ⊆ family →
                W.AreSeparated B (2 * t) →
                ∀ R : RectangleFamily delta t,
                  R.CentersIn family →
                  R.IsOverCentralQuarterOf I →
                  R.IsPairwiseIncomparable family
                    (C * Real.rpow tangency C) →
                  R.Nonempty →
                  ∀ mu nu : ℕ, 0 < mu → 0 < nu →
                    (∀ i,
                      mu ≤
                        RectangleFamily.tangentCount
                          (R.rectangle i) W tangency ∧
                      nu ≤
                        RectangleFamily.tangentCount
                          (R.rectangle i) B tangency) →
                    (R.card : ℝ) ≤
                      C * Real.rpow tangency C *
                        Real.rpow
                            (RectangleFamily.bipartiteNormalizedCount
                              W B mu nu)
                            (3 / 2 : ℝ) *
                          Real.log
                            (RectangleFamily.bipartiteNormalizedCount
                              W B mu nu)

/--
The `mu = nu = 1` geometric core of the robust separated theorem.

This is the direct graph-lens counting statement.  The passage from this
unit-multiplicity estimate to `BipartiteTangencyRobustCoreStatement` is the
finite two-sided sampling argument and is kept as a separate leaf.
-/
def BipartiteTangencyRobustUnitCoreStatement : Prop :=
  ∀ K : ℝ, 1 ≤ K →
    ∃ c₂ C : ℝ,
      0 < c₂ ∧ 100 ≤ C ∧
      ∀ tangency : ℝ, 5 ≤ tangency →
        ∀ family : Set C2Function,
          HasCinematicCurvature family K →
          ∀ I : ParameterInterval, I.IsControlled K →
            ∀ delta t : ℝ, 0 < delta → 0 < t →
              delta ≤ t → t ≤ 1 →
              Real.rpow tangency C * delta ≤ c₂ * t / 2 →
              IsAdmissibleComparisonScale delta t
                (C * Real.rpow tangency C) →
              ∀ W B : FiniteFunctionFamily,
                W.carrier ⊆ family →
                B.carrier ⊆ family →
                W.AreSeparated B (2 * t) →
                ∀ R : RectangleFamily delta t,
                  R.CentersIn family →
                  R.IsOverCentralQuarterOf I →
                  R.IsPairwiseIncomparable family
                    (C * Real.rpow tangency C) →
                  R.Nonempty →
                  (∀ i,
                    1 ≤
                      RectangleFamily.tangentCount
                        (R.rectangle i) W tangency ∧
                    1 ≤
                      RectangleFamily.tangentCount
                        (R.rectangle i) B tangency) →
                  (R.card : ℝ) ≤
                    C * Real.rpow tangency C *
                      Real.rpow
                          (RectangleFamily.bipartiteNormalizedCount
                            W B 1 1)
                          (3 / 2 : ℝ) *
                        Real.log
                          (RectangleFamily.bipartiteNormalizedCount
                            W B 1 1)

/-- Section 4 perturbation and reduction package. -/
def Section4PerturbationAndReductionsStatement : Prop :=
  (∀ f g : C2Function, ∀ c : ℝ,
      c2Distance (f.verticalTranslate c) (g.verticalTranslate c) =
          c2Distance f g ∧
        ∀ x : UnitPoint,
          jetGap (f.verticalTranslate c) (g.verticalTranslate c) x =
            jetGap f g x) ∧
  (∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
    ∀ family : Set C2Function,
      IsCinematicFamily family K D →
      ∀ I : ParameterInterval, I.IsControlled K →
        ∀ F : FiniteFunctionFamily, F.carrier ⊆ family →
          ∀ epsilon : ℝ, 0 < epsilon →
            ∃ shift : C2Function → ℝ,
              (∀ f ∈ F.carrier, |shift f| ≤ epsilon) ∧
              F.HasNoExactTangenciesOn I shift) ∧
  (PolynomialRectangleRefinementStatement →
    CommonTangentRectangleRobustStatement →
    BipartiteTangencyRobustCoreStatement →
      BipartiteTangencyStatement)

/--
Finite metric two-ends selection used in Section 5.

The diameter hypothesis is inherited in the paper from `F ⊆ family` and the
cinematic-family bound `diameter family ≤ K`. It is explicit here because the
lemma is stated for an abstract finite metric family.
-/
def TwoEndsSelectionStatement : Prop :=
  ∀ epsilon delta K : ℝ,
    0 < epsilon → 0 < delta → delta ≤ K →
      ∀ F : FiniteFunctionFamily, F.carrier.Nonempty → F.DiameterLE K →
        ∃ t : ℝ, ∃ center : C2Function,
          ∃ G : FiniteFunctionFamily,
            delta ≤ t ∧ t ≤ K ∧
            G.carrier ⊆ F.carrier ∩ c2Ball center t ∧
            Real.rpow (t / K) epsilon * (F.card : ℝ) ≤
              (G.card : ℝ) ∧
            ∀ g : C2Function, ∀ lambda : ℝ,
              delta / t < lambda → lambda < 1 →
                (((G.carrier ∩ c2Ball g (lambda * t)).ncard : ℝ) ≤
                  4 * Real.rpow (2 * lambda) epsilon * (G.card : ℝ))

/-- Dyadic multiplicity selection used to create the first shading. -/
def MultiplicityLevelSelectionStatement : Prop :=
  ∀ delta : ℝ, 0 < delta →
    ∀ F : FiniteFunctionFamily,
      ∀ E : Set (ℝ × ℝ), MeasurableSet E →
        MeasureTheory.volume E < ⊤ →
        let total :=
          ∫ p in E, Real.rpow (multiplicity F delta p) (3 / 2 : ℝ)
        total = 0 ∨
          ∃ mu : ℕ, 0 < mu ∧
            ∃ E₀ : Set (ℝ × ℝ),
              MeasurableSet E₀ ∧ E₀ ⊆ E ∧
              (∀ p ∈ E₀,
                mu ≤ multiplicity F delta p ∧
                  multiplicity F delta p < 2 * mu) ∧
              total ≤
                ((Nat.log2 (F.card + 1) + 1 : ℕ) : ℝ) *
                  ∫ p in E₀,
                    Real.rpow (multiplicity F delta p) (3 / 2 : ℝ)

/-- Section 5 two-ends and initial multiplicity/shading setup. -/
def Section5TwoEndsSetupStatement : Prop :=
  TwoEndsSelectionStatement ∧ MultiplicityLevelSelectionStatement

/--
Finite counting form of the good-pair selection in PYZ Lemma 45.

For every first coordinate, each of two bad sets occupies at most one third
of `S`; hence at least one third of all ordered pairs avoid both bad sets.
-/
def GoodPairCountingStatement : Prop :=
  ∀ (α : Type) [DecidableEq α],
    ∀ S : Finset α, ∀ bad₁ bad₂ : α → Finset α,
      (∀ g ∈ S, 3 * (S ∩ bad₁ g).card ≤ S.card) →
      (∀ g ∈ S, 3 * (S ∩ bad₂ g).card ≤ S.card) →
      S.card ^ 2 ≤
        3 * ((S.product S).filter
          (fun pair => pair.2 ∉ bad₁ pair.1 ∧ pair.2 ∉ bad₂ pair.1)).card

/--
Finite incidence double-counting used after PYZ Lemmas 45 and 46.

If every rectangle contributes at least `q` admissible pairs and every pair
belongs to at most `L` rectangles, then the total number of rectangle-pair
incidences is bounded in the two expected ways.
-/
def PairIncidenceCountingStatement : Prop :=
  ∀ (ρ σ : Type) [DecidableEq ρ] [DecidableEq σ],
    ∀ rectangles : Finset ρ, ∀ pairs : Finset σ,
      ∀ incidence : ρ → Finset σ, ∀ q L : ℕ,
        (∀ R ∈ rectangles, q ≤ (pairs ∩ incidence R).card) →
        (∀ p ∈ pairs,
          (rectangles.filter (fun R => p ∈ incidence R)).card ≤ L) →
        rectangles.card * q ≤ pairs.card * L

/--
Second two-ends selection from PYZ Section 5, now for the tangency parameter.

The explicit upper bound `T` is supplied by the first two-ends localization.
In the paper one may safely take `T = 12 * t` with the present normalization.
-/
def TangencyTwoEndsSelectionStatement : Prop :=
  ∀ eta delta T : ℝ,
    0 < eta → 0 < delta → delta ≤ T →
      ∀ I : ParameterInterval,
        ∀ F : FiniteFunctionFamily,
          F.carrier.Nonempty →
          (∀ ⦃f⦄, f ∈ F.carrier →
            ∀ ⦃g⦄, g ∈ F.carrier →
              0 ≤ tangencyParameterOn I f g ∧
                tangencyParameterOn I f g ≤ T) →
          ∃ Delta : ℝ, ∃ k : C2Function,
            ∃ G : FiniteFunctionFamily,
              delta ≤ Delta ∧
              Delta ≤ T ∧
              k ∈ F.carrier ∧
              G.carrier =
                F.carrier ∩
                  {f | tangencyParameterOn I f k ≤ Delta} ∧
              Real.rpow (Delta / T) eta * (F.card : ℝ) ≤
                2 * (G.card : ℝ) ∧
              ∀ g ∈ F.carrier,
                ∀ lambda : ℝ,
                  delta / Delta < lambda →
                  lambda < 1 →
                  (((F.carrier ∩
                        {f | tangencyParameterOn I f g ≤
                          lambda * Delta}).ncard : ℕ) : ℝ) ≤
                    2 * Real.rpow lambda eta * (G.card : ℝ)

/--
Restricted weak-type reduction preceding the two-ends argument in PYZ
Section 5.

Once every dyadic multiplicity level has the expected `mu⁻³/²` measure
bound, the full `3/2`-power integral is controlled up to the logarithmic
number of levels.
-/
def RestrictedWeakTypeReductionStatement : Prop :=
  MultiplicityLevelSelectionStatement →
    ∃ C_rw : ℝ, 0 < C_rw ∧
      ∀ delta B : ℝ, 0 < delta → 0 ≤ B →
        ∀ F : FiniteFunctionFamily,
          ∀ E : Set (ℝ × ℝ),
            MeasurableSet E →
            MeasureTheory.volume E < ⊤ →
            (∀ mu : ℕ, 0 < mu →
              ∀ E₀ : Set (ℝ × ℝ),
                MeasurableSet E₀ →
                E₀ ⊆ E →
                (∀ p ∈ E₀,
                  (mu : ℝ) ≤ multiplicity F delta p ∧
                    multiplicity F delta p < 2 * mu) →
                MeasureTheory.volume E₀ ≤
                  ENNReal.ofReal
                    (B * Real.rpow (mu : ℝ) (-3 / 2 : ℝ))) →
            (∫ p in E,
                Real.rpow (multiplicity F delta p) (3 / 2 : ℝ)) ≤
              C_rw *
                (((Nat.log2 (F.card + 1) + 1 : ℕ) : ℝ)) * B

/-- PYZ Lemma 41: assign a common tangent fine rectangle to one fiber. -/
def FineRectangleAssignmentStatement : Prop :=
  ∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
    ∃ C_R : ℝ, 9216 * K^2 ≤ C_R ∧
      ∀ family : Set C2Function,
        IsCinematicFamily family K D →
        ∀ I : ParameterInterval, I.IsControlled K →
          ∀ delta t Delta : ℝ,
            0 < delta → delta ≤ Delta → Delta ≤ t →
            let t' := C_R * t * Delta / delta
            ∀ p : UnitPoint × ℝ,
              p.1 ∈ I.centeredCarrier (1 / 8) →
              ∀ k ∈ family, |p.2 - k p.1| ≤ delta →
                ∀ G : FiniteFunctionFamily,
                  G.carrier ⊆ family →
                  (∀ f ∈ G.carrier,
                    c2Distance f k ≤ 6 * t ∧
                    tangencyParameterOn I f k ≤ Delta ∧
                    |p.2 - f p.1| ≤ delta) →
                  ∃ R : CurvilinearRectangle delta t',
                    R.function = k ∧
                    R.interval.midpoint = (p.1 : ℝ) ∧
                    p ∈ R.carrier ∧
                    R.IsOverCentralQuarterOf I ∧
                    ∀ f ∈ G.carrier, R.IsLambdaTangent f 5

/--
The original raw PYZ Theorem 1.7 API.

This proposition is retained as the formally disproved historical interface.
It chooses `δ₀` before the concrete family without fixing an absolute `C²`
normalization; `theorem1_7_uniformity_not` proves its negation.
-/
def Theorem1_7Statement : Prop :=
  ∀ D : ℝ, 1 ≤ D →
    ∃ C : ℝ, 0 < C ∧
      ∀ K : ℝ, 1 ≤ K →
        ∀ ε : ℝ, 0 < ε →
          ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
            ∀ α ζ : ℝ, 0 < α → α ≤ ζ → ζ ≤ 1 →
              ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
                ∀ family : Set C2Function,
                  IsCinematicFamily family K D →
                  ∀ E : Set (ℝ × ℝ),
                    IsQuasiProduct E δ α α (Real.rpow δ (-ε)) →
                    ∀ F : FiniteFunctionFamily,
                      F.carrier ⊆ family →
                      HasFrostmanBound F δ ε ζ →
                      (∫ p in E,
                        Real.rpow (multiplicity F δ p) (3 / 2 : ℝ)) ≤
                          Real.rpow δ
                            (2 - α / 2 - ζ / 2 - C * ε) *
                            (F.card : ℝ)

/--
Application-faithful repaired PYZ Theorem 1.7 for a uniformly bounded subset
of `C²([0,1])`.

The absolute jet bound `M` is fixed before the small-scale threshold. This
is an explicit correction to the literal theorem statement, which says the
threshold depends only on `D`, `K`, and `ε`. It matches the paper application,
where
`sup_{f ∈ 𝓕} ‖f‖_{C²(I)} ≤ ‖γ‖_{C²(I)}`, and excludes the singleton
high-frequency counterexample to `Theorem1_7Statement`.
-/
def Theorem1_7UniformC2Statement : Prop :=
  ∀ D : ℝ, 1 ≤ D →
    ∃ C : ℝ, 0 < C ∧
      ∀ K : ℝ, 1 ≤ K →
        ∀ M : ℝ, 0 ≤ M →
          ∀ ε : ℝ, 0 < ε →
            ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
              ∀ α ζ : ℝ, 0 < α → α ≤ ζ → ζ ≤ 1 →
                ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
                  ∀ family : Set C2Function,
                    IsCinematicFamily family K D →
                    HasUniformC2Bound family M →
                    ∀ E : Set (ℝ × ℝ),
                      IsQuasiProduct E δ α α (Real.rpow δ (-ε)) →
                      ∀ F : FiniteFunctionFamily,
                        F.carrier ⊆ family →
                        HasFrostmanBound F δ ε ζ →
                        (∫ p in E,
                          Real.rpow (multiplicity F δ p) (3 / 2 : ℝ)) ≤
                            Real.rpow δ
                              (2 - α / 2 - ζ / 2 - C * ε) *
                              (F.card : ℝ)

end Kakeya.Cinematic
