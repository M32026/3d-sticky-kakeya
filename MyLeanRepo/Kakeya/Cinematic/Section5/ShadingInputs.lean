import MyLeanRepo.Kakeya.Cinematic.Section5.FineShadings

/-!
# Fine-shading comparison input
-/

namespace Kakeya.Cinematic

/--
PYZ Lemma 42. Comparable fine rectangles have nested inner and enlarged
shadings after one fixed polynomial enlargement.
-/
def FineShadingComparisonStatement : Prop :=
  ComparableRectanglesStatement →
    ComparabilityTransitivityStatement →
      ∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
        ∃ C_s : ℝ, 100 ≤ C_s ∧
          ∀ {family : Set C2Function},
            IsCinematicFamily family K D →
            ∀ {E₂ : Set (ℝ × ℝ)}
              {delta t Delta C_R : ℝ},
              0 < delta →
              delta ≤ Delta →
              Delta ≤ t →
              0 < t →
              0 < C_R →
              let tFine := C_R * t * Delta / delta
              IsAdmissibleComparisonScale delta tFine C_s →
              ∀ (data :
                FineRectangleAssignmentData
                  family E₂ K delta t Delta C_R),
                Real.sqrt (C_s * delta / tFine) ≤
                  data.interval.length / 8 →
                ∀ R R' : CurvilinearRectangle delta tFine,
                  R.function ∈ family →
                  R'.function ∈ family →
                  R.IsOverCentralQuarterOf data.interval →
                  R'.IsOverCentralQuarterOf data.interval →
                  |R.interval.midpoint - data.interval.midpoint| ≤
                    data.interval.length / 16 →
                  |R'.interval.midpoint - data.interval.midpoint| ≤
                    data.interval.length / 16 →
                  R.AreLambdaComparable R' family 100 →
                  fineInnerShading data R' ⊆
                    fineOuterShading data C_s R

/--
The maximal-incomparable selection core of PYZ Lemma 43. The selected
rectangles retain source points in `E₂`, are pairwise 100-incomparable, and
every point-indexed fine rectangle is either selected or comparable to one
selected rectangle.
-/
def MaximalFineRectangleSelectionStatement : Prop :=
  ∀ {K delta t Delta C_R : ℝ},
    let tFine := C_R * t * Delta / delta
    ∀ {family : Set C2Function} {E₂ : Set (ℝ × ℝ)},
      E₂.Nonempty →
      ∀ (data :
        FineRectangleAssignmentData
          family E₂ K delta t Delta C_R),
        ∀ N : ℕ,
          (∀ S : RectangleFamily delta tFine,
            (∃ source : Fin S.card → E₂,
              ∀ i, S.rectangle i = data.rectangle (source i)) →
            S.IsPairwiseIncomparable family 100 →
            S.card ≤ N) →
          ∃ R : RectangleFamily delta tFine,
            ∃ source : Fin R.card → E₂,
              R.Nonempty ∧
              (∀ i, R.rectangle i = data.rectangle (source i)) ∧
              R.CentersIn family ∧
              R.IsOverCentralQuarterOf data.interval ∧
              R.IsPairwiseIncomparable family 100 ∧
              (∀ p : E₂, ∃ i : Fin R.card,
                data.rectangle p = R.rectangle i ∨
                  (data.rectangle p).AreLambdaComparable
                    (R.rectangle i) family 100)

/--
Outer shadings of a sufficiently incomparable fine rectangle family are
pairwise disjoint.
-/
def FineShadingDisjointnessStatement : Prop :=
  ComparabilityTransitivityStatement →
    ∀ K D C_s : ℝ,
      1 ≤ K →
      1 ≤ D →
      1 ≤ C_s →
      ∃ C_out : ℝ, 100 ≤ C_out ∧
        ∀ {family : Set C2Function} {E₂ : Set (ℝ × ℝ)}
          {delta t Delta C_R : ℝ},
          IsCinematicFamily family K D →
          0 < delta →
          let tFine := C_R * t * Delta / delta
          delta ≤ tFine →
          IsAdmissibleComparisonScale delta tFine C_out →
          ∀ (data :
            FineRectangleAssignmentData
              family E₂ K delta t Delta C_R),
            ∀ R : RectangleFamily delta tFine,
              R.CentersIn family →
              R.IsOverCentralQuarterOf data.interval →
              R.IsPairwiseIncomparable family C_out →
              Set.PairwiseDisjoint
                (Set.univ : Set (Fin R.card))
                (fun i => fineOuterShading data C_s (R.rectangle i))

end Kakeya.Cinematic
