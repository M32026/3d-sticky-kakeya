import MyLeanRepo.Kakeya.Cinematic.Section5.FineShadings

/-!
# Fine-to-coarse rectangle grouping data
-/

namespace Kakeya.Cinematic

/--
The finite grouping obtained after coarsening the selected fine rectangles
and choosing a maximal incomparable coarse subfamily.
-/
structure CoarseRectangleGroupingData
    (family : Set C2Function)
    (E₂ : Set (ℝ × ℝ)) (K : ℝ) (I : ParameterInterval)
    (delta t Delta C_R : ℝ)
    (pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R)
    (fine : RectangleFamily delta (C_R * t * Delta / delta)) where
  source : Fin fine.card → E₂
  fine_eq_source : ∀ i, fine.rectangle i = pointData.rectangle (source i)
  enlarged : Fin fine.card → CurvilinearRectangle Delta (C_R * t)
  enlarged_function : ∀ i,
    (enlarged i).function = (fine.rectangle i).function
  enlarged_midpoint : ∀ i,
    (enlarged i).interval.midpoint =
      (fine.rectangle i).interval.midpoint
  fine_subset_enlarged : ∀ i,
    (fine.rectangle i).carrier ⊆ (enlarged i).carrier
  enlarged_central : ∀ i,
    (enlarged i).IsOverCentralQuarterOf I
  coarse : RectangleFamily Delta (C_R * t)
  coarse_nonempty : coarse.Nonempty
  coarse_centers : coarse.CentersIn family
  coarse_central : coarse.IsOverCentralQuarterOf I
  coarse_incomparable :
    coarse.IsPairwiseIncomparable family 100
  representative : Fin coarse.card ↪ Fin fine.card
  coarse_eq_enlarged : ∀ j,
    coarse.rectangle j = enlarged (representative j)
  parent : Fin fine.card → Fin coarse.card
  parent_representative : ∀ j, parent (representative j) = j
  parent_relation : ∀ i,
    enlarged i = coarse.rectangle (parent i) ∨
      (enlarged i).AreLambdaComparable
        (coarse.rectangle (parent i)) family 100

/-- Fine rectangle indices assigned to one coarse parent. -/
def CoarseRectangleGroupingData.fiber
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (j : Fin data.coarse.card) : Finset (Fin fine.card) :=
  Finset.univ.filter fun i => data.parent i = j

lemma CoarseRectangleGroupingData.sum_fiber_card
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine) :
    ∑ j : Fin data.coarse.card, (data.fiber j).card = fine.card := by
  have hmaps :
      ((Finset.univ : Finset (Fin fine.card)) : Set (Fin fine.card)).MapsTo
        data.parent (Finset.univ : Finset (Fin data.coarse.card)) := by
    intro i _
    exact Finset.mem_univ (data.parent i)
  simpa [CoarseRectangleGroupingData.fiber] using
    (Finset.card_eq_sum_card_fiberwise hmaps).symm

lemma CoarseRectangleGroupingData.fine_card_le_coarse_card_mul
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    {M : ℕ} (hM : ∀ j, (data.fiber j).card ≤ M) :
    fine.card ≤ data.coarse.card * M := by
  rw [← data.sum_fiber_card]
  calc
    ∑ j : Fin data.coarse.card, (data.fiber j).card
        ≤ ∑ _j : Fin data.coarse.card, M :=
      Finset.sum_le_sum fun j _ => hM j
    _ = data.coarse.card * M := by
      simp [Finset.sum_const]

lemma CoarseRectangleGroupingData.fine_card_le_coarse_card_mul_real
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    {M : ℝ} (hM : ∀ j, ((data.fiber j).card : ℝ) ≤ M) :
    (fine.card : ℝ) ≤ (data.coarse.card : ℝ) * M := by
  have hsum :
      (fine.card : ℝ) =
        ∑ j : Fin data.coarse.card, ((data.fiber j).card : ℝ) := by
    exact_mod_cast data.sum_fiber_card.symm
  rw [hsum]
  calc
    ∑ j : Fin data.coarse.card, ((data.fiber j).card : ℝ)
        ≤ ∑ _j : Fin data.coarse.card, M :=
      Finset.sum_le_sum fun j _ => hM j
    _ = (data.coarse.card : ℝ) * M := by
      simp [Finset.sum_const]

lemma CoarseRectangleGroupingData.sum_selected_parent_card
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (selected : Finset (Fin fine.card)) :
    ∑ j : Fin data.coarse.card,
        (selected.filter fun i => data.parent i = j).card =
      selected.card := by
  have hmaps :
      (selected : Set (Fin fine.card)).MapsTo data.parent
        (Finset.univ : Finset (Fin data.coarse.card)) := by
    intro i _
    exact Finset.mem_univ (data.parent i)
  simpa using (Finset.card_eq_sum_card_fiberwise hmaps).symm

lemma CoarseRectangleGroupingData.selected_card_le_coarse_card_mul_real
    {family : Set C2Function}
    {E₂ : Set (ℝ × ℝ)} {K : ℝ}
    {I : ParameterInterval}
    {delta t Delta C_R : ℝ}
    {pointData :
      FineRectangleAssignmentData family E₂ K delta t Delta C_R}
    {fine : RectangleFamily delta (C_R * t * Delta / delta)}
    (data : CoarseRectangleGroupingData
      family E₂ K I delta t Delta C_R pointData fine)
    (selected : Finset (Fin fine.card))
    {M : ℝ}
    (hM : ∀ j,
      ((selected.filter fun i => data.parent i = j).card : ℝ) ≤ M) :
    (selected.card : ℝ) ≤ (data.coarse.card : ℝ) * M := by
  have hsum :
      (selected.card : ℝ) =
        ∑ j : Fin data.coarse.card,
          ((selected.filter fun i => data.parent i = j).card : ℝ) := by
    exact_mod_cast (data.sum_selected_parent_card selected).symm
  rw [hsum]
  calc
    ∑ j : Fin data.coarse.card,
        ((selected.filter fun i => data.parent i = j).card : ℝ)
        ≤ ∑ _j : Fin data.coarse.card, M :=
      Finset.sum_le_sum fun j _ => hM j
    _ = (data.coarse.card : ℝ) * M := by
      simp [Finset.sum_const]

end Kakeya.Cinematic
