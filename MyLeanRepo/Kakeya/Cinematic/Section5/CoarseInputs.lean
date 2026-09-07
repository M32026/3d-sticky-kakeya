import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseGrouping

/-!
# Coarse rectangle grouping input
-/

namespace Kakeya.Cinematic

/--
Construct and group the centered coarse dilations of one selected fine
rectangle family.
-/
def CoarseRectangleGroupingStatement : Prop :=
  FineToCoarseCentralStatement →
    RectangleSubfamilySelectionStatement →
      ∀ {K delta t Delta C_R : ℝ},
        1 ≤ K →
        0 < delta →
        delta ≤ Delta →
        Delta ≤ t →
        0 < t →
        0 < C_R →
        9216 * K^2 ≤ C_R →
        ∀ {family : Set C2Function} {E₂ : Set (ℝ × ℝ)}
          {I : ParameterInterval},
          I.IsControlled K →
          ∀ (pointData :
            FineRectangleAssignmentData
              family E₂ K delta t Delta C_R),
            pointData.interval = I →
            ∀ (fine : RectangleFamily
              delta (C_R * t * Delta / delta)),
              fine.Nonempty →
              ∀ (source : Fin fine.card → E₂),
                (∀ i, fine.rectangle i =
                  pointData.rectangle (source i)) →
                fine.CentersIn family →
                Nonempty
                  (CoarseRectangleGroupingData
                    family E₂ K I delta t Delta C_R pointData fine)

/--
Tangency transfer from one coarse rectangle to a comparable coarse parent.
The output tangency constant is fixed after `K`, `D`, and the comparison
constant are fixed; it is not incorrectly asserted to remain equal to `5`.
-/
def ComparableCoarseTangencyAt
    (K D comparison tangency : ℝ) : Prop :=
  ∀ {family : Set C2Function},
    IsCinematicFamily family K D →
    ∀ {I : ParameterInterval},
      I.IsControlled K →
      ∀ {delta t : ℝ},
        0 < delta →
        delta ≤ t →
        IsAdmissibleComparisonScale delta t comparison →
        ∀ {R S : CurvilinearRectangle delta t},
          R.function ∈ family →
          S.function ∈ family →
          R.IsOverCentralQuarterOf I →
          S.IsOverCentralQuarterOf I →
          R.AreLambdaComparable S family comparison →
          ∀ {f : C2Function},
            f ∈ family →
            R.IsLambdaTangent f 5 →
            S.IsLambdaTangent f tangency

def ComparableCoarseTangencyStatement : Prop :=
  TangencyGeometryCompletionStatement →
    ∀ K D comparison : ℝ,
      1 ≤ K →
      1 ≤ D →
      100 ≤ comparison →
      ∃ tangency : ℝ, 5 ≤ tangency ∧
        ∀ {family : Set C2Function},
          IsCinematicFamily family K D →
          ∀ {I : ParameterInterval},
            I.IsControlled K →
            ∀ {delta t : ℝ},
              0 < delta →
              delta ≤ t →
              IsAdmissibleComparisonScale delta t comparison →
              ∀ {R S : CurvilinearRectangle delta t},
                R.function ∈ family →
                S.function ∈ family →
                R.IsOverCentralQuarterOf I →
                S.IsOverCentralQuarterOf I →
                R.AreLambdaComparable S family comparison →
                ∀ {f : C2Function},
                  f ∈ family →
                  R.IsLambdaTangent f 5 →
                  S.IsLambdaTangent f tangency

end Kakeya.Cinematic
