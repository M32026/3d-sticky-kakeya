import MyLeanRepo.Kakeya.Streamlined.DividingScales.FrostmanInequalities
import MyLeanRepo.Kakeya.Streamlined.MaximalDensityFactoring.SubfamilyHelpers

/-!
# Body-subfamily invariance under ambient reindexing

Two body subfamilies with the same ambient index image differ only by a finite
reindexing.  Their contained masses, densities, and Frostman constants are
therefore equal.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace Subfamily

/-- Identity body subfamily. -/
def identity (F : BodyFamily) : Subfamily F where
  family := F
  embedding := Function.Embedding.refl _
  carrier_eq := fun _ => rfl

/-- Same ambient image gives the same image of contained indices. -/
lemma containedIndices_image_eq_of_image_eq
    {F : BodyFamily}
    (S T : Subfamily F)
    (himage :
      Finset.image S.embedding Finset.univ =
        Finset.image T.embedding Finset.univ)
    (K : Set Point3) :
    Finset.image S.embedding (S.family.containedIndices K) =
      Finset.image T.embedding (T.family.containedIndices K) := by
  classical
  ext ambient
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨i, hi, hiambient⟩
    have hiK : (F.body ambient).carrier ⊆ K := by
      have hselected :=
        (BodyFamily.mem_containedIndices_iff.mp hi)
      rw [S.carrier_eq i, hiambient] at hselected
      exact hselected
    have hambient :
        ambient ∈ Finset.image T.embedding Finset.univ := by
      rw [← himage]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hiambient⟩
    rcases Finset.mem_image.mp hambient with
      ⟨j, _hj, hjambient⟩
    refine Finset.mem_image.mpr ⟨j, ?_, hjambient⟩
    rw [BodyFamily.mem_containedIndices_iff, T.carrier_eq j, hjambient]
    exact hiK
  · intro h
    rcases Finset.mem_image.mp h with ⟨j, hj, hjambient⟩
    have hjK : (F.body ambient).carrier ⊆ K := by
      have hselected :=
        (BodyFamily.mem_containedIndices_iff.mp hj)
      rw [T.carrier_eq j, hjambient] at hselected
      exact hselected
    have hambient :
        ambient ∈ Finset.image S.embedding Finset.univ := by
      rw [himage]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hjambient⟩
    rcases Finset.mem_image.mp hambient with
      ⟨i, _hi, hiambient⟩
    refine Finset.mem_image.mpr ⟨i, ?_, hiambient⟩
    rw [BodyFamily.mem_containedIndices_iff, S.carrier_eq i, hiambient]
    exact hjK

/-- Contained mass of a body subfamily as an ambient-index sum. -/
lemma containedMass_eq_ambient_sum
    {F : BodyFamily}
    (S : Subfamily F)
    (K : Set Point3) :
    S.family.containedMass K =
      ∑ i ∈ Finset.image S.embedding
          (S.family.containedIndices K),
        (F.body i).volume := by
  classical
  have hsum :
      ∑ j ∈ S.family.containedIndices K,
          (S.family.body j).volume =
        ∑ j ∈ S.family.containedIndices K,
          (F.body (S.embedding j)).volume := by
    apply Finset.sum_congr rfl
    intro j _
    simp [Body.volume, S.carrier_eq j]
  rw [BodyFamily.containedMass, hsum]
  rw [Finset.sum_image]
  exact fun i _ j _ hij => S.embedding.injective hij

/-- Same ambient image gives equal contained mass. -/
lemma containedMass_eq_of_image_eq
    {F : BodyFamily}
    (S T : Subfamily F)
    (himage :
      Finset.image S.embedding Finset.univ =
        Finset.image T.embedding Finset.univ)
    (K : Set Point3) :
    S.family.containedMass K = T.family.containedMass K := by
  rw [S.containedMass_eq_ambient_sum K,
    T.containedMass_eq_ambient_sum K,
    S.containedIndices_image_eq_of_image_eq T himage K]

/-- Same ambient image gives equal density. -/
lemma density_eq_of_image_eq
    {F : BodyFamily}
    (S T : Subfamily F)
    (himage :
      Finset.image S.embedding Finset.univ =
        Finset.image T.embedding Finset.univ)
    (K : Set Point3) :
    S.family.density K = T.family.density K := by
  dsimp only [BodyFamily.density]
  rw [S.containedMass_eq_of_image_eq T himage K]

/-- Same ambient image gives equal maximal convex-set density. -/
lemma deltaMax_eq_of_image_eq
    {F : BodyFamily}
    (S T : Subfamily F)
    (himage :
      Finset.image S.embedding Finset.univ =
        Finset.image T.embedding Finset.univ) :
    S.family.deltaMax = T.family.deltaMax := by
  have hdensity :
      ∀ K : Set Point3, S.family.density K = T.family.density K :=
    S.density_eq_of_image_eq T himage
  unfold BodyFamily.deltaMax
  congr 1
  ext value
  constructor
  · rintro ⟨K, hK, rfl⟩
    exact ⟨K, hK, hdensity K⟩
  · rintro ⟨K, hK, rfl⟩
    exact ⟨K, hK, (hdensity K).symm⟩

/-- Same ambient image gives equal Frostman constant. -/
lemma frostmanConstantIn_eq_of_image_eq
    {F : BodyFamily}
    (S T : Subfamily F)
    (himage :
      Finset.image S.embedding Finset.univ =
        Finset.image T.embedding Finset.univ)
    (V : Set Point3) :
    S.family.frostmanConstantIn V = T.family.frostmanConstantIn V := by
  have hdensity :
      ∀ K : Set Point3, S.family.density K = T.family.density K :=
    S.density_eq_of_image_eq T himage
  unfold BodyFamily.frostmanConstantIn
  congr 1
  ext value
  constructor
  · rintro ⟨K, hK, hKV, rfl⟩
    refine ⟨K, hK, hKV, ?_⟩
    rw [hdensity K, hdensity V]
  · rintro ⟨K, hK, hKV, rfl⟩
    refine ⟨K, hK, hKV, ?_⟩
    rw [hdensity K, hdensity V]

end Subfamily

end Kakeya.Streamlined
