import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslatedCopiesBasic
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslateTubeGeometry
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# Shadings on translated-copy subfamilies

For a subfamily of an explicit indexed union of translated copies, transport
the original shading along the copy and original-family indices. The resulting
shaded union has volume at most the number of copies times the original shaded
union volume.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined.RandomTranslation

/--
The exact translated restriction of `Y` to a subfamily of `translatedCopies`.
-/
def translatedSubfamilyShading
    {δ : ℝ} {F : TubeFamily δ} {J : ℕ} {shift : Fin J → Point3}
    (S : TubeSubfamily (translatedCopies F J shift))
    (Y : TubeShading F) : TubeShading S.family where
  carrier i :=
    let p : Fin J × Fin F.card := finProdFinEquiv.symm (S.embedding i)
    translateSet (Y.carrier p.2) (shift p.1)
  measurable_carrier i := by
    let p : Fin J × Fin F.card := finProdFinEquiv.symm (S.embedding i)
    exact measurableSet_translateSet (Y.measurable_carrier p.2) (shift p.1)
  subset_body i := by
    let p : Fin J × Fin F.card := finProdFinEquiv.symm (S.embedding i)
    have hY : Y.carrier p.2 ⊆ (F.tube p.2).carrier :=
      Y.subset_body p.2
    have himage :
        translateSet (Y.carrier p.2) (shift p.1) ⊆
          translateSet (F.tube p.2).carrier (shift p.1) :=
      Set.image_mono hY
    have hcarrier :
        translateSet (F.tube p.2).carrier (shift p.1) =
          (translateTube (F.tube p.2) (shift p.1)).carrier :=
      (translateTube_carrier (F.tube p.2) (shift p.1)).symm
    change
      translateSet (Y.carrier p.2) (shift p.1) ⊆
        (S.family.tube i).carrier
    rw [S.tube_eq i]
    have htube :
        (translatedCopies F J shift).tube (S.embedding i) =
          translateTube (F.tube p.2) (shift p.1) := by
      rfl
    rw [htube, ← hcarrier]
    exact himage

@[simp] lemma translatedSubfamilyShading_carrier
    {δ : ℝ} {F : TubeFamily δ} {J : ℕ} {shift : Fin J → Point3}
    (S : TubeSubfamily (translatedCopies F J shift))
    (Y : TubeShading F) (i : Fin S.family.card) :
    (translatedSubfamilyShading S Y).carrier i =
      let p : Fin J × Fin F.card :=
        finProdFinEquiv.symm (S.embedding i)
      translateSet (Y.carrier p.2) (shift p.1) := rfl

/--
Translation preserves the mass of each selected shaded piece.
-/
lemma translatedSubfamilyShading_mass
    {δ : ℝ} {F : TubeFamily δ} {J : ℕ} {shift : Fin J → Point3}
    (S : TubeSubfamily (translatedCopies F J shift))
    (Y : TubeShading F) :
    (translatedSubfamilyShading S Y).mass =
      ∑ i : Fin S.family.card,
        let p : Fin J × Fin F.card :=
          finProdFinEquiv.symm (S.embedding i)
        volume (Y.carrier p.2) := by
  apply Finset.sum_congr rfl
  intro i _
  let p : Fin J × Fin F.card :=
    finProdFinEquiv.symm (S.embedding i)
  change volume (translateSet (Y.carrier p.2) (shift p.1)) =
    volume (Y.carrier p.2)
  exact volume_translateSet (Y.measurable_carrier p.2) (shift p.1)

/--
The translated subfamily shading is contained in the union of all translated
copies of the original shaded union.
-/
lemma translatedSubfamilyShading_union_subset
    {δ : ℝ} {F : TubeFamily δ} {J : ℕ} {shift : Fin J → Point3}
    (S : TubeSubfamily (translatedCopies F J shift))
    (Y : TubeShading F) :
    (translatedSubfamilyShading S Y).union ⊆
      ⋃ j : Fin J, translateSet Y.union (shift j) := by
  intro x hx
  rcases hx with ⟨i, hxi⟩
  let p : Fin J × Fin F.card := finProdFinEquiv.symm (S.embedding i)
  have hsource : ∃ k : Fin F.card, x ∈ translateSet (Y.carrier k) (shift p.1) :=
    ⟨p.2, hxi⟩
  have hp : x ∈ translateSet Y.union (shift p.1) := by
    rcases hsource with ⟨k, y, hy, rfl⟩
    exact ⟨y, ⟨k, hy⟩, rfl⟩
  exact Set.mem_iUnion.mpr ⟨p.1, hp⟩

/--
The shaded union of a translated subfamily has volume at most `J` times the
volume of the original shaded union.
-/
lemma translatedSubfamilyShading_union_volume_le
    {δ : ℝ} {F : TubeFamily δ} {J : ℕ} {shift : Fin J → Point3}
    (S : TubeSubfamily (translatedCopies F J shift))
    (Y : TubeShading F) :
    volume (translatedSubfamilyShading S Y).union ≤
      (J : ENNReal) * volume Y.union := by
  have hsub := translatedSubfamilyShading_union_subset S Y
  have h_union :
      volume (⋃ j : Fin J, translateSet Y.union (shift j)) ≤
        ∑ j : Fin J, volume (translateSet Y.union (shift j)) := by
    simpa using
      (measure_biUnion_finset_le
        (μ := volume) (Finset.univ : Finset (Fin J))
        (fun j => translateSet Y.union (shift j)))
  have hY_union_meas : MeasurableSet Y.union := by
    have h_union_eq :
        Y.union = ⋃ i : Fin F.card, Y.carrier i := by
      ext x
      constructor
      · intro hx
        change ∃ i : Fin F.card, x ∈ Y.carrier i at hx
        exact Set.mem_iUnion.mpr hx
      · intro hx
        change ∃ i : Fin F.card, x ∈ Y.carrier i
        exact Set.mem_iUnion.mp hx
    rw [h_union_eq]
    exact MeasurableSet.iUnion (fun i => Y.measurable_carrier i)
  have h_translate :
      ∀ j : Fin J, volume (translateSet Y.union (shift j)) = volume Y.union :=
    fun j => volume_translateSet hY_union_meas (shift j)
  calc
    volume (translatedSubfamilyShading S Y).union
        ≤ volume (⋃ j : Fin J, translateSet Y.union (shift j)) :=
      measure_mono hsub
    _ ≤ ∑ j : Fin J, volume (translateSet Y.union (shift j)) := h_union
    _ = ∑ _j : Fin J, volume Y.union := by
      apply Finset.sum_congr rfl
      intro j _
      exact h_translate j
    _ = (J : ENNReal) * volume Y.union := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]

end Kakeya.Streamlined.RandomTranslation
