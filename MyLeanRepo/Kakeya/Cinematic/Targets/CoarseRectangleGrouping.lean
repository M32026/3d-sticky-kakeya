import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseInputs

/-!
# Group centered coarse dilations
-/

namespace Kakeya.Cinematic

theorem coarse_rectangle_grouping :
    CoarseRectangleGroupingStatement := by
  dsimp only [CoarseRectangleGroupingStatement]
  intro hFineToCoarse hSubfamily K delta t Delta C_R hK hdelta
    hdeltaDelta hDeltaT ht hCR hCRlarge family E₂ I hI pointData
    hpointDataInterval fine hfine source hsource hcenters
  classical
  have hEnlargement :
      ∀ i : Fin fine.card,
        ∃ S : CurvilinearRectangle Delta (C_R * t),
          S.function = (fine.rectangle i).function ∧
          S.interval.midpoint = (fine.rectangle i).interval.midpoint ∧
          (fine.rectangle i).carrier ⊆ S.carrier ∧
          S.IsOverCentralQuarterOf I := by
    intro i
    apply hFineToCoarse hK hdelta hdeltaDelta hDeltaT ht hCR hCRlarge hI
    · simpa [hpointDataInterval, hsource i] using
        pointData.rectangle_central (source i)
    · simpa [hpointDataInterval, hsource i] using
        pointData.rectangle_midpoint_central (source i)
  choose enlarged enlarged_function enlarged_midpoint fine_subset_enlarged
    enlarged_central using hEnlargement
  let enlargedFamily : RectangleFamily Delta (C_R * t) := {
    card := fine.card
    rectangle := enlarged
  }
  have hEnlargedCenters : enlargedFamily.CentersIn family := by
    intro i
    change (enlarged i).function ∈ family
    rw [enlarged_function i]
    exact hcenters i
  obtain ⟨selected, selected_centers, selected_incomparable, selected_cover⟩ :=
    hSubfamily Delta (C_R * t) family 100 (by norm_num)
      enlargedFamily hEnlargedCenters
  have selected_nonempty : selected.family.Nonempty := by
    rcases selected_cover ⟨0, hfine⟩ with ⟨j, -⟩
    exact Nat.zero_lt_of_lt j.isLt
  let parent : Fin fine.card → Fin selected.card := fun i =>
    if h : ∃ j, i = selected.embedding j then
      Classical.choose h
    else
      Classical.choose (selected_cover i)
  have parent_representative :
      ∀ j, parent (selected.embedding j) = j := by
    intro j
    have hrep : ∃ k, selected.embedding j = selected.embedding k :=
      ⟨j, rfl⟩
    simp only [parent, dif_pos hrep]
    apply selected.embedding.injective
    exact (Classical.choose_spec hrep).symm
  have parent_relation :
      ∀ i,
        enlarged i = selected.family.rectangle (parent i) ∨
          (enlarged i).AreLambdaComparable
            (selected.family.rectangle (parent i)) family 100 := by
    intro i
    by_cases hrep : ∃ j, i = selected.embedding j
    · left
      simpa [parent, hrep, enlargedFamily, RectangleSubfamily.family] using
        congrArg enlarged (Classical.choose_spec hrep)
    · rcases Classical.choose_spec (selected_cover i) with heq | hcomparable
      · left
        simpa [parent, hrep, enlargedFamily, RectangleSubfamily.family] using
          congrArg enlarged heq
      · right
        simpa [parent, hrep, enlargedFamily, RectangleSubfamily.family] using
          hcomparable
  refine ⟨{
    source := source
    fine_eq_source := hsource
    enlarged := enlarged
    enlarged_function := enlarged_function
    enlarged_midpoint := enlarged_midpoint
    fine_subset_enlarged := fine_subset_enlarged
    enlarged_central := enlarged_central
    coarse := selected.family
    coarse_nonempty := selected_nonempty
    coarse_centers := selected_centers
    coarse_central := fun j => enlarged_central (selected.embedding j)
    coarse_incomparable := selected_incomparable
    representative := selected.embedding
    coarse_eq_enlarged := fun _ => rfl
    parent := parent
    parent_representative := parent_representative
    parent_relation := parent_relation
  }⟩

end Kakeya.Cinematic
