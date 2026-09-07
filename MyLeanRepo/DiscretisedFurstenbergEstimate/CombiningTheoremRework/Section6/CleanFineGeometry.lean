module

/-
  Clean Fine Geometry Lemmas

  Extracts simple geometric lemmas from Prop73/InductiveStepBridge.lean
  without any Prop73 dependencies.

  Contains:
  - fine_point_set_homothety_image: union of fine square sets equals
    homothety image of union of original square sets.

  Dependencies: CombiningTheorem (homothetyS), FormatConversionLemmas
  (squareHomothety_toSet), DyadicTubes, Mathlib

  Whiteprint node: section6 / clean_fine_geometry
  Status: CLEAN EXTRACT
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicConversion
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DiscretisedFurstenbergEstimate.InductionConfigurations
open DirecretisedFurstenbergEstimate.FormatConversion.M5

/-- The point set of a fine config is the homothety image of the thinned
    point set within the coarse square Q.

    Given P_thin : Finset (DyadicSquare n) with all squares contained in Q,
    the union of (squareHomothety hnm Q p).toSet for p ∈ P_thin equals
    homothetyS (dyadicDelta m) Q.i Q.j '' (⋃ p ∈ P_thin, p.toSet). -/
lemma fine_point_set_homothety_image_clean
    {n m : ℕ} (hnm : m ≤ n) (Q : DyadicSquare m)
    (P_thin : Finset (DyadicSquare n))
    (h_contained : ∀ p ∈ P_thin, squareContained hnm p Q) :
    (⋃ p ∈ P_thin, ((squareHomothety hnm Q p).toSet : Set EuclideanPlane)) =
    homothetyS (dyadicDelta m) Q.i Q.j ''
      (⋃ p ∈ P_thin, (p.toSet : Set EuclideanPlane)) := by
  have h_eq1 : (⋃ p ∈ P_thin, ((squareHomothety hnm Q p).toSet : Set EuclideanPlane)) =
      ⋃ p ∈ P_thin, (homothetyS (dyadicDelta m) Q.i Q.j '' p.toSet) := by
    ext x
    simp only [Set.mem_iUnion₂]
    <;> constructor <;> rintro ⟨p, hp, hxp⟩ <;> refine ⟨p, hp, ?_⟩
    · exact (squareHomothety_toSet hnm Q p).symm ▸ hxp
    · exact (squareHomothety_toSet hnm Q p) ▸ hxp
  rw [h_eq1]
  have h_eq2 : (⋃ p ∈ P_thin, (homothetyS (dyadicDelta m) Q.i Q.j '' p.toSet)) =
      homothetyS (dyadicDelta m) Q.i Q.j '' (⋃ p ∈ P_thin, (p.toSet : Set EuclideanPlane)) := by
    ext x
    simp only [Set.mem_iUnion₂, Set.mem_image]
    constructor
    · rintro ⟨p, hp, y, hyp, rfl⟩
      exact ⟨y, ⟨p, hp, hyp⟩, rfl⟩
    · rintro ⟨y, ⟨p, hp, hyp⟩, rfl⟩
      exact ⟨p, hp, y, hyp, rfl⟩
  exact h_eq2

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
