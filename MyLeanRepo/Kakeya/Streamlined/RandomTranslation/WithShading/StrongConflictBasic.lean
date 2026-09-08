import MyLeanRepo.Kakeya.Streamlined.Estimates

/-!
# Dependency-light strong-conflict profiles

These are the finite strong-conflict quantities shared by the historical
strict recursion and the native assigned-profile recursion.  They depend only
on indexed tube families and weights; no cover or uniform structure occurs.
-/

noncomputable section

open BigOperators MeasureTheory
open Kakeya.Streamlined

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/-- Count of `K`-strong conflicts for one tube in an equal-radius family. -/
def tubeConflictDegreeStrong
    {delta : ℝ}
    (family : TubeFamily delta)
    (volumeScale K : ENNReal)
    (index : Fin family.card) : ℕ :=
  (Finset.univ.filter fun other =>
    other ≠ index ∧
      volume
        ((family.tube index).carrier ∩
          (family.tube other).carrier) >
        volumeScale / K).card

/-- Total ordered `K`-strong conflict degree. -/
def tubeTotalStrongConflictDegree
    {delta : ℝ}
    (family : TubeFamily delta)
    (K : ENNReal) : ℕ :=
  ∑ index : Fin family.card,
    tubeConflictDegreeStrong
      family (Kakeya.deltaTubeVolume delta) K index

/-- Shading-weighted total ordered `K`-strong conflict degree. -/
def weightedTotalStrongConflict
    {delta : ℝ} {family : TubeFamily delta}
    (shading : TubeShading family)
    (K : ENNReal) : ENNReal :=
  ∑ index : Fin family.card,
    volume (shading.carrier index) *
      (tubeConflictDegreeStrong
        family (Kakeya.deltaTubeVolume delta) K index : ENNReal)

/-- Strong conflict degree weighted by an arbitrary finite weight. -/
def weightedTotalStrongConflictBy
    {scale : ℝ}
    (family : TubeFamily scale)
    (weight : Fin family.card → ENNReal)
    (K : ENNReal) : ENNReal :=
  ∑ index : Fin family.card,
    weight index *
      (tubeConflictDegreeStrong
        family (Kakeya.deltaTubeVolume scale) K index : ENNReal)

/-- Total arbitrary weight on a finite tube family. -/
def tubeFamilyWeight
    {scale : ℝ}
    (family : TubeFamily scale)
    (weight : Fin family.card → ENNReal) : ENNReal :=
  ∑ index : Fin family.card, weight index

/-- A pointwise strong-degree bound controls every arbitrary-weight total. -/
lemma weightedTotalStrongConflictBy_le_of_pointwise
    {scale : ℝ}
    (family : TubeFamily scale)
    (weight : Fin family.card → ENNReal)
    (K : ENNReal)
    (bound : ℕ)
    (hdegree :
      ∀ index,
        tubeConflictDegreeStrong
          family (Kakeya.deltaTubeVolume scale) K index ≤ bound) :
    weightedTotalStrongConflictBy family weight K ≤
      (bound : ENNReal) * tubeFamilyWeight family weight := by
  dsimp only [weightedTotalStrongConflictBy, tubeFamilyWeight]
  calc
    (∑ index : Fin family.card,
        weight index *
          (tubeConflictDegreeStrong
            family (Kakeya.deltaTubeVolume scale) K index : ENNReal))
        ≤ ∑ index : Fin family.card,
            weight index * (bound : ENNReal) := by
          apply Finset.sum_le_sum
          intro index _
          gcongr
          exact_mod_cast hdegree index
    _ = (bound : ENNReal) *
          ∑ index : Fin family.card, weight index := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      rw [mul_comm]

/-- Every pointwise strong-conflict set is bounded by the ambient cardinality. -/
lemma tubeConflictDegreeStrong_le_card
    {delta : ℝ}
    (family : TubeFamily delta)
    (volumeScale K : ENNReal)
    (index : Fin family.card) :
    tubeConflictDegreeStrong family volumeScale K index ≤ family.card := by
  dsimp only [tubeConflictDegreeStrong]
  simpa using
    Finset.card_le_card
      (Finset.filter_subset
        (fun other : Fin family.card =>
          other ≠ index ∧
            volume
              ((family.tube index).carrier ∩
                (family.tube other).carrier) >
              volumeScale / K)
        Finset.univ)

/-- Trivial finite bound for the total strong-conflict degree. -/
lemma tubeTotalStrongConflictDegree_le_card
    {delta : ℝ}
    (family : TubeFamily delta)
    (K : ENNReal) :
    tubeTotalStrongConflictDegree family K ≤
      family.card * family.card := by
  dsimp only [tubeTotalStrongConflictDegree]
  calc
    (∑ index : Fin family.card,
        tubeConflictDegreeStrong
          family (Kakeya.deltaTubeVolume delta) K index)
        ≤ ∑ _index : Fin family.card, family.card := by
          exact Finset.sum_le_sum fun index _ =>
            tubeConflictDegreeStrong_le_card
              family (Kakeya.deltaTubeVolume delta) K index
    _ = family.card * family.card := by
      simp [Finset.sum_const]

/-- Trivial finite bound for the shading-weighted strong-conflict total. -/
lemma weightedTotalStrongConflict_le_card
    {delta : ℝ}
    (family : TubeFamily delta)
    (shading : TubeShading family)
    (K : ENNReal) :
    weightedTotalStrongConflict shading K ≤
      (family.card : ENNReal) * shading.mass := by
  dsimp only [weightedTotalStrongConflict, Shading.mass]
  calc
    (∑ index : Fin family.card,
        volume (shading.carrier index) *
          (tubeConflictDegreeStrong
            family (Kakeya.deltaTubeVolume delta) K index : ENNReal))
        ≤ ∑ index : Fin family.card,
            volume (shading.carrier index) *
              (family.card : ENNReal) := by
          apply Finset.sum_le_sum
          intro index _
          gcongr
          exact_mod_cast
            tubeConflictDegreeStrong_le_card
              family (Kakeya.deltaTubeVolume delta) K index
    _ = (family.card : ENNReal) *
          ∑ index : Fin family.card,
            volume (shading.carrier index) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      rw [mul_comm]

end Kakeya.Streamlined.RandomTranslation.WithShading

end
