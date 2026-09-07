import MyLeanRepo.Kakeya.Cinematic.Perturbation.FiniteAvoidance
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Epsilon avoidance for directional shifts

Given finite W and B families, find a polynomial-size epsilon that avoids
creating exact tangencies between shifted W and B functions.

The bad set for a pair `(f, g)` is the set of vertical shift differences that
would create an exact tangency.  Each bad set has measure zero (Sard), and a
finite union of translated null sets is still null.  Therefore any interval of
positive length contains an epsilon that avoids all bad values.
-/

namespace Kakeya.Cinematic

open MeasureTheory

/-- badSet is symmetric under swapping functions and negation. -/
lemma badSet_symm (f g : C2Function) (I : ParameterInterval) :
    badSet g f I = Neg.neg '' (badSet f g I) := by
  ext r
  simp only [badSet, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨x, hx, hderiv, rfl⟩
    refine ⟨g x - f x, ?_, by ring⟩
    exact ⟨x, hx, hderiv.symm, by ring⟩
  · rintro ⟨y, ⟨x, hx, hderiv, rfl⟩, rfl⟩
    exact ⟨x, hx, hderiv.symm, by ring⟩

/-- The set of upward epsilon values creating tangencies has measure zero. -/
lemma badUnion_up_measure_zero
    {W B : FiniteFunctionFamily} {I : ParameterInterval}
    (shift0 : C2Function → ℝ) :
    volume {epsilon : ℝ | ∃ p ∈ (W.toFinset ×ˢ B.toFinset),
      (shift0 p.1 - shift0 p.2) + epsilon ∈ badSet p.1 p.2 I} = 0 := by
  let S : Finset (C2Function × C2Function) := W.toFinset ×ˢ B.toFinset
  have h_main : ∀ (p : C2Function × C2Function), p ∈ S →
      volume ((fun x : ℝ => x - (shift0 p.1 - shift0 p.2)) '' (badSet p.1 p.2 I)) = 0 := by
    intro p _
    have h_null : volume (badSet p.1 p.2 I) = 0 := badSet_measure_zero p.1 p.2 I
    let c : ℝ := shift0 p.1 - shift0 p.2
    have h_eq : (fun x : ℝ => x - c) '' (badSet p.1 p.2 I) =
        (fun y : ℝ => y + c) ⁻¹' (badSet p.1 p.2 I) := by
      ext y; simp [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, h_y⟩
        have h : y + c = x := by linarith
        exact h ▸ hx
      · intro hx
        refine ⟨y + c, hx, ?_⟩
        ring
    rw [h_eq]
    have h_mp : MeasurePreserving (fun y : ℝ => y + c) := measurePreserving_add_right volume c
    exact h_mp.preimage_null h_null
  have h_union : volume (⋃ p ∈ (S : Set (C2Function × C2Function)),
      (fun x : ℝ => x - (shift0 p.1 - shift0 p.2)) '' (badSet p.1 p.2 I)) = 0 := by
    exact (measure_biUnion_null_iff S.countable_toSet).mpr h_main
  have h_set_eq : {epsilon : ℝ | ∃ p ∈ S, (shift0 p.1 - shift0 p.2) + epsilon ∈ badSet p.1 p.2 I} =
      ⋃ p ∈ (S : Set (C2Function × C2Function)),
        (fun x : ℝ => x - (shift0 p.1 - shift0 p.2)) '' (badSet p.1 p.2 I) := by
    ext epsilon
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨p, hp, h_in⟩
      refine ⟨p, hp, (shift0 p.1 - shift0 p.2) + epsilon, h_in, ?_⟩
      ring
    · rintro ⟨p, hp, y, hy, rfl⟩
      exact ⟨p, hp, by simpa using hy⟩
  rw [h_set_eq]
  exact h_union

/-- The set of downward epsilon values creating tangencies has measure zero. -/
lemma badUnion_down_measure_zero
    {W B : FiniteFunctionFamily} {I : ParameterInterval}
    (shift0 : C2Function → ℝ) :
    volume {epsilon : ℝ | ∃ p ∈ (W.toFinset ×ˢ B.toFinset),
      (shift0 p.1 - shift0 p.2) - epsilon ∈ badSet p.1 p.2 I} = 0 := by
  let S : Finset (C2Function × C2Function) := W.toFinset ×ˢ B.toFinset
  have h_main : ∀ (p : C2Function × C2Function), p ∈ S →
      volume ((fun x : ℝ => (shift0 p.1 - shift0 p.2) - x) '' (badSet p.1 p.2 I)) = 0 := by
    intro p _
    let c : ℝ := shift0 p.1 - shift0 p.2
    -- Use badSet_symm: -badSet f g = badSet g f
    -- Then {c - r | r ∈ badSet f g} = {c + r | r ∈ badSet g f}, a translation
    have h_eq1 : (fun x : ℝ => c - x) '' (badSet p.1 p.2 I) =
        (fun x : ℝ => c + x) '' (badSet p.2 p.1 I) := by
      ext y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨r, hr, rfl⟩
        refine ⟨-r, ?_, by ring⟩
        have h_symm : badSet p.2 p.1 I = Neg.neg '' (badSet p.1 p.2 I) := badSet_symm p.1 p.2 I
        rw [h_symm]
        exact ⟨r, hr, by ring⟩
      · rintro ⟨r, hr, rfl⟩
        have h_symm2 : badSet p.1 p.2 I = Neg.neg '' (badSet p.2 p.1 I) := badSet_symm p.2 p.1 I
        refine ⟨-r, ?_, by ring⟩
        rw [h_symm2]
        exact ⟨r, hr, by ring⟩
    rw [h_eq1]
    have h_null : volume (badSet p.2 p.1 I) = 0 := badSet_measure_zero p.2 p.1 I
    have h_image_eq : (fun x : ℝ => c + x) '' (badSet p.2 p.1 I) =
        (fun y : ℝ => y - c) ⁻¹' (badSet p.2 p.1 I) := by
      ext z
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have h : c + x - c = x := by ring
        rw [h]; exact hx
      · intro hz
        refine ⟨z - c, hz, by ring⟩
    rw [h_image_eq]
    have h_mp_inv : MeasurePreserving (fun y : ℝ => y - c) := measurePreserving_add_right volume (-c)
    exact h_mp_inv.preimage_null h_null
  have h_union : volume (⋃ p ∈ (S : Set (C2Function × C2Function)),
      (fun x : ℝ => (shift0 p.1 - shift0 p.2) - x) '' (badSet p.1 p.2 I)) = 0 := by
    exact (measure_biUnion_null_iff S.countable_toSet).mpr h_main
  have h_set_eq : {epsilon : ℝ | ∃ p ∈ S, (shift0 p.1 - shift0 p.2) - epsilon ∈ badSet p.1 p.2 I} =
      ⋃ p ∈ (S : Set (C2Function × C2Function)),
        (fun x : ℝ => (shift0 p.1 - shift0 p.2) - x) '' (badSet p.1 p.2 I) := by
    ext epsilon
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨p, hp, h_in⟩
      refine ⟨p, hp, (shift0 p.1 - shift0 p.2) - epsilon, h_in, ?_⟩
      ring
    · rintro ⟨p, hp, y, hy, rfl⟩
      exact ⟨p, hp, by simpa using hy⟩
  rw [h_set_eq]
  exact h_union

/-- A nonempty open interval cannot be contained in a null set. -/
lemma exists_real_notin_null_set {a b : ℝ} (hab : a < b) {S : Set ℝ}
    (hS : volume S = 0) :
    ∃ (x : ℝ), a < x ∧ x < b ∧ x ∉ S := by
  have h_pos : 0 < volume (Set.Ioo a b) := by
    simpa [Real.volume_Ioo, hab] using by linarith
  have h_not_sub : ¬ (Set.Ioo a b ⊆ S) := by
    intro h_sub
    have h1 : volume (Set.Ioo a b) ≤ volume S := measure_mono h_sub
    rw [hS] at h1
    exact not_le.mpr h_pos h1
  have h_exists : ∃ (x : ℝ), x ∈ Set.Ioo a b ∧ x ∉ S :=
    Set.not_subset.mp h_not_sub
  rcases h_exists with ⟨x, hx, hxn⟩
  exact ⟨x, hx.1, hx.2, hxn⟩

end Kakeya.Cinematic
