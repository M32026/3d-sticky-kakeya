import MyLeanRepo.Kakeya.Assouad.Statements

/-!
# Reindex a selected finite set of tube indices

This packages a `Finset (Fin F.card)` as an actual `TubeFamily`, preserving
the selected tube structures exactly.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The tube family obtained by enumerating exactly the selected indices. -/
def selectedTubeFamily {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (selected : Finset (Fin F.card)) :
    Kakeya.Streamlined.TubeFamily delta where
  card := selected.card
  tube j := F.tube ↑(selected.equivFin.symm j)

lemma selectedTubeFamily_tube {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (selected : Finset (Fin F.card))
    (j : Fin selected.card) :
    (selectedTubeFamily F selected).tube j =
      F.tube ↑(selected.equivFin.symm j) := rfl

lemma selectedTubeFamily_isEssentiallyDistinct {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (selected : Finset (Fin F.card))
    (hdistinct :
      ∀ i ∈ selected, ∀ j ∈ selected, i ≠ j →
        (F.tube i).EssentiallyDistinct (F.tube j)) :
    (selectedTubeFamily F selected).IsEssentiallyDistinct := by
  intro i j hij
  have hi_mem : (↑(selected.equivFin.symm i) : Fin F.card) ∈ selected :=
    Finset.coe_mem _
  have hj_mem : (↑(selected.equivFin.symm j) : Fin F.card) ∈ selected :=
    Finset.coe_mem _
  have hindex :
      (↑(selected.equivFin.symm i) : Fin F.card) ≠
        ↑(selected.equivFin.symm j) := by
    intro h
    apply hij
    exact selected.equivFin.symm.injective (Subtype.ext h)
  exact hdistinct _ hi_mem _ hj_mem hindex

lemma selectedTubeFamily_isInVerticalChart {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (selected : Finset (Fin F.card))
    (hvertical : IsInVerticalChart F) :
    IsInVerticalChart (selectedTubeFamily F selected) := by
  intro j
  exact hvertical ↑(selected.equivFin.symm j)

lemma selectedTubeFamily_hasBoundedBase {delta R : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (selected : Finset (Fin F.card))
    (hbase : HasBoundedBase F R) :
    HasBoundedBase (selectedTubeFamily F selected) R := by
  intro j
  exact hbase ↑(selected.equivFin.symm j)

/-- Reindex an existing shading along the selected tube indices. -/
def selectedTubeShading {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (selected : Finset (Fin F.card)) :
    Kakeya.Streamlined.TubeShading (selectedTubeFamily F selected) where
  carrier j := Y.carrier (selected.equivFin.symm j).1
  measurable_carrier j :=
    Y.measurable_carrier (selected.equivFin.symm j).1
  subset_body j := by
    change
      Y.carrier (selected.equivFin.symm j).1 ⊆
        (F.tube (selected.equivFin.symm j).1).carrier
    exact Y.subset_body (selected.equivFin.symm j).1

lemma selectedTubeShading_carrier {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (selected : Finset (Fin F.card))
    (j : Fin selected.card) :
    (selectedTubeShading Y selected).carrier j =
      Y.carrier (selected.equivFin.symm j).1 := rfl

lemma selectedTubeShading_union_subset {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (selected : Finset (Fin F.card)) :
    (selectedTubeShading Y selected).union ⊆ Y.union := by
  intro p hp
  rcases hp with ⟨j, hj⟩
  exact ⟨(selected.equivFin.symm j).1, hj⟩

lemma selectedTubeShading_mass {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (selected : Finset (Fin F.card)) :
    (selectedTubeShading Y selected).mass =
      ∑ i ∈ selected, MeasureTheory.volume (Y.carrier i) := by
  classical
  let e := selected.equivFin
  calc
    (selectedTubeShading Y selected).mass =
        ∑ j : Fin selected.card,
          MeasureTheory.volume
            (Y.carrier (e.symm j).1) := rfl
    _ = ∑ i : selected,
          MeasureTheory.volume (Y.carrier i.1) := by
        exact Equiv.sum_comp (M := ENNReal) e.symm
          (fun i : selected =>
            MeasureTheory.volume (Y.carrier i.1))
    _ = ∑ i ∈ selected,
          MeasureTheory.volume (Y.carrier i) := by
        simpa using
          (Finset.sum_attach selected
            (fun i => MeasureTheory.volume (Y.carrier i)))

/-- Nominal body mass of a selected tube family is the selected volume sum. -/
lemma selectedTubeFamily_mass {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (selected : Finset (Fin F.card)) :
    (selectedTubeFamily F selected).toBodyFamily.mass =
      ∑ i ∈ selected, (F.tube i).volume := by
  classical
  let e := selected.equivFin
  calc
    (selectedTubeFamily F selected).toBodyFamily.mass =
        ∑ j : Fin selected.card,
          (F.tube (e.symm j).1).volume := rfl
    _ = ∑ i : selected, (F.tube i.1).volume := by
      exact Equiv.sum_comp (M := ENNReal) e.symm
        (fun i : selected => (F.tube i.1).volume)
    _ = ∑ i ∈ selected, (F.tube i).volume := by
      simpa using
        (Finset.sum_attach selected
          (fun i => (F.tube i).volume))

/-- Selecting tube indices cannot increase nominal body mass. -/
lemma selectedTubeFamily_mass_le {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (selected : Finset (Fin F.card)) :
    (selectedTubeFamily F selected).toBodyFamily.mass ≤
      F.toBodyFamily.mass := by
  rw [selectedTubeFamily_mass]
  change
    (∑ i ∈ selected, (F.tube i).volume) ≤
      ∑ i : Fin F.card, (F.tube i).volume
  exact Finset.sum_le_univ_sum_of_nonneg
    (f := fun i : Fin F.card => (F.tube i).volume)
    (fun _ => bot_le)

/--
Choose one selected representative for every original tube index.

Selected indices represent themselves.  Every other index is paired with a
selected tube with which it fails essential distinctness.
-/
lemma exists_selected_representative
    {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (selected : Finset (Fin F.card))
    (hmax :
      ∀ i : Fin F.card,
        i ∈ selected ∨
          ∃ j ∈ selected,
            ¬(F.tube i).EssentiallyDistinct (F.tube j)) :
    ∃ parent : Fin F.card → Fin selected.card,
      (∀ i, i ∈ selected →
        (selected.equivFin.symm (parent i)).1 = i) ∧
      (∀ i, i ∉ selected →
        ¬(F.tube i).EssentiallyDistinct
          (F.tube (selected.equivFin.symm (parent i)).1)) ∧
      Function.Surjective parent := by
  classical
  let representativeSubtype :
      ∀ i : Fin F.card, selected :=
    fun i =>
      if hi : i ∈ selected then
        ⟨i, hi⟩
      else
        ⟨Classical.choose (Or.resolve_left (hmax i) hi),
          (Classical.choose_spec (Or.resolve_left (hmax i) hi)).1⟩
  let parent : Fin F.card → Fin selected.card :=
    fun i => selected.equivFin (representativeSubtype i)
  have hself :
      ∀ i, i ∈ selected →
        (selected.equivFin.symm (parent i)).1 = i := by
    intro i hi
    simp [parent, representativeSubtype, hi]
  have hconflict :
      ∀ i, i ∉ selected →
        ¬(F.tube i).EssentiallyDistinct
          (F.tube (selected.equivFin.symm (parent i)).1) := by
    intro i hi
    have hspec :=
      (Classical.choose_spec (Or.resolve_left (hmax i) hi)).2
    simpa [parent, representativeSubtype, hi] using hspec
  have hsurj : Function.Surjective parent := by
    intro j
    let chosen : selected := selected.equivFin.symm j
    refine ⟨chosen.1, ?_⟩
    change selected.equivFin (representativeSubtype chosen.1) = j
    have hrep : representativeSubtype chosen.1 = chosen := by
      apply Subtype.ext
      simp [representativeSubtype, chosen]
    rw [hrep]
    exact selected.equivFin.apply_symm_apply j
  exact ⟨parent, hself, hconflict, hsurj⟩

end Kakeya.Assouad
