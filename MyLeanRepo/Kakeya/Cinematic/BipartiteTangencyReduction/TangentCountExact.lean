import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ClusterDefinitions

/-!
# Exact tangent counts

If every member of a finite function family is tangent to one rectangle, its
tangent count is exactly the family cardinality.  The same applies to every
metric cluster of that family.
-/

namespace Kakeya.Cinematic

namespace RectangleFamily

lemma tangentCount_eq_card_of_all_tangent
    {delta t tangency : ℝ}
    (rectangle : CurvilinearRectangle delta t)
    (functions : FiniteFunctionFamily)
    (hall : ∀ function ∈ functions.carrier,
      rectangle.IsLambdaTangent function tangency) :
    tangentCount rectangle functions tangency = functions.card := by
  classical
  unfold tangentCount
  have hfilter :
      functions.toFinset.filter
          (fun function => rectangle.IsLambdaTangent function tangency) =
        functions.toFinset := by
    apply Finset.filter_eq_self.mpr
    intro function hfunction
    exact hall function <| by
      simpa [FiniteFunctionFamily.toFinset] using hfunction
  rw [hfilter]
  exact Set.ncard_eq_toFinset_card functions.carrier functions.finite |>.symm

lemma tangentCount_cluster_eq_card_of_all_tangent
    {delta t tangency radius : ℝ}
    (rectangle : CurvilinearRectangle delta t)
    (functions : FiniteFunctionFamily)
    (center : C2Function)
    (hall : ∀ function ∈ functions.carrier,
      rectangle.IsLambdaTangent function tangency) :
    tangentCount rectangle (functions.cluster center radius) tangency =
      (functions.cluster center radius).card := by
  apply tangentCount_eq_card_of_all_tangent
  intro function hfunction
  exact hall function hfunction.1

end RectangleFamily

end Kakeya.Cinematic
