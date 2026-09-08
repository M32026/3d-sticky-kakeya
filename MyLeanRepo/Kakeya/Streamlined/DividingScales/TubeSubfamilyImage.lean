import MyLeanRepo.Kakeya.Streamlined.DividingScales.FullFiberRestriction

/-!
# Tube-subfamily invariance under ambient reindexing

Two tube subfamilies with the same image of ambient indices differ only by a
finite reindexing.  Their contained masses, densities, and Frostman constants
inside every common reference set are therefore equal.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace TubeSubfamily

variable {rho : ℝ} {G : TubeFamily rho}

/-- Same ambient index image gives the same image of contained indices. -/
lemma indicesIn_image_eq_of_image_eq
    (S T : TubeSubfamily G)
    (himage :
      Finset.image S.embedding Finset.univ =
        Finset.image T.embedding Finset.univ)
    (K : Set Point3) :
    Finset.image S.embedding (S.family.indicesIn K) =
      Finset.image T.embedding (T.family.indicesIn K) := by
  classical
  ext ambient
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨i, hi, hiambient⟩
    have hiK :
        (G.tube ambient).carrier ⊆ K := by
      have hselected :
          (S.family.tube i).carrier ⊆ K :=
        (S.family.mem_indicesIn_iff K i).mp hi
      rw [S.tube_eq i, hiambient] at hselected
      exact hselected
    have hambient :
        ambient ∈ Finset.image T.embedding Finset.univ := by
      rw [← himage]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hiambient⟩
    rcases Finset.mem_image.mp hambient with
      ⟨j, _hj, hjambient⟩
    refine Finset.mem_image.mpr ⟨j, ?_, hjambient⟩
    rw [T.family.mem_indicesIn_iff K j, T.tube_eq j, hjambient]
    exact hiK
  · intro h
    rcases Finset.mem_image.mp h with ⟨j, hj, hjambient⟩
    have hjK :
        (G.tube ambient).carrier ⊆ K := by
      have hselected :
          (T.family.tube j).carrier ⊆ K :=
        (T.family.mem_indicesIn_iff K j).mp hj
      rw [T.tube_eq j, hjambient] at hselected
      exact hselected
    have hambient :
        ambient ∈ Finset.image S.embedding Finset.univ := by
      rw [himage]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hjambient⟩
    rcases Finset.mem_image.mp hambient with
      ⟨i, _hi, hiambient⟩
    refine Finset.mem_image.mpr ⟨i, ?_, hiambient⟩
    rw [S.family.mem_indicesIn_iff K i, S.tube_eq i, hiambient]
    exact hjK

/-- Same ambient index image gives equal contained mass in every set. -/
lemma containedMass_eq_of_image_eq
    (S T : TubeSubfamily G)
    (himage :
      Finset.image S.embedding Finset.univ =
        Finset.image T.embedding Finset.univ)
    (K : Set Point3) :
    S.family.toBodyFamily.containedMass K =
      T.family.toBodyFamily.containedMass K := by
  rw [S.containedMass_eq_ambient_sum K,
    T.containedMass_eq_ambient_sum K,
    S.indicesIn_image_eq_of_image_eq T himage K]

/-- Same ambient index image gives equal density in every set. -/
lemma density_eq_of_image_eq
    (S T : TubeSubfamily G)
    (himage :
      Finset.image S.embedding Finset.univ =
        Finset.image T.embedding Finset.univ)
    (K : Set Point3) :
    S.family.toBodyFamily.density K =
      T.family.toBodyFamily.density K := by
  dsimp only [BodyFamily.density]
  rw [S.containedMass_eq_of_image_eq T himage K]

/-- Same ambient index image gives equal Frostman constant in every set. -/
lemma frostmanConstantIn_eq_of_image_eq
    (S T : TubeSubfamily G)
    (himage :
      Finset.image S.embedding Finset.univ =
        Finset.image T.embedding Finset.univ)
    (V : Set Point3) :
    S.family.toBodyFamily.frostmanConstantIn V =
      T.family.toBodyFamily.frostmanConstantIn V := by
  have hdensity :
      ∀ K : Set Point3,
        S.family.toBodyFamily.density K =
          T.family.toBodyFamily.density K :=
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

end TubeSubfamily

end Kakeya.Streamlined
