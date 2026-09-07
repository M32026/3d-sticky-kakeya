import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeReversal

/-!
# Four-segment signed axis cover

Four geometric unit segments cover both signed parameter ranges produced by
the representative-axis alignment lemma.  The leftmost segment is stored with
reversed orientation to keep every basepoint within one unit of the
representative base.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Every signed axis point with parameter in `[-1,2]` belongs to one of four
consecutive unit segments covering the oriented axis range `[-2,2]`.
-/
lemma signed_axis_point_mem_four_segments
    (base direction : Point3)
    {sign r : ℝ} (hsign : sign = 1 ∨ sign = -1)
    (hr : r ∈ Set.Icc (-1 : ℝ) 2) :
    base + r • (sign • direction) ∈
      Kakeya.unitSegment (base - direction) (-direction) ∪
      Kakeya.unitSegment (base - direction) direction ∪
      Kakeya.unitSegment base direction ∪
      Kakeya.unitSegment (base + direction) direction := by
  rcases hsign with (rfl | rfl)
  · have hpoint :
        base + r • ((1 : ℝ) • direction) =
          base + r • direction := by simp
    rw [hpoint]
    by_cases h0 : r ≤ 0
    · have hp : r + 1 ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> linarith [hr.1]
      exact Or.inl (Or.inl (Or.inr ⟨r + 1, hp, by module⟩))
    · by_cases h1 : r ≤ 1
      · have hp : r ∈ Set.Icc (0 : ℝ) 1 := by
          constructor <;> linarith
        exact Or.inl (Or.inr ⟨r, hp, rfl⟩)
      · have hp : r - 1 ∈ Set.Icc (0 : ℝ) 1 := by
          constructor <;> linarith [hr.2]
        exact Or.inr ⟨r - 1, hp, by module⟩
  · have hneg : (-1 : ℝ) • direction = -direction := by simp
    rw [hneg]
    let q : ℝ := -r
    have hpoint :
        base + r • (-direction) = base + q • direction := by
      dsimp only [q]
      module
    rw [hpoint]
    have hq : q ∈ Set.Icc (-2 : ℝ) 1 := by
      dsimp only [q]
      constructor <;> linarith [hr.1, hr.2]
    by_cases hm1 : q ≤ -1
    · have hp : -1 - q ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> linarith [hq.1]
      exact Or.inl (Or.inl (Or.inl ⟨-1 - q, hp, by module⟩))
    · by_cases h0 : q ≤ 0
      · have hp : q + 1 ∈ Set.Icc (0 : ℝ) 1 := by
          constructor <;> linarith
        exact Or.inl (Or.inl (Or.inr ⟨q + 1, hp, by module⟩))
      · have hp : q ∈ Set.Icc (0 : ℝ) 1 := by
          constructor <;> linarith [hq.2]
        exact Or.inl (Or.inr ⟨q, hp, rfl⟩)

/--
Orientation-aware form of `signed_axis_point_mem_four_segments`.

Reversing the direction also shifts the stored base to `base + direction`.
After that shift, a reversed parameter `r` becomes the forward parameter
`1 - r`, which remains in `[-1,2]`.
-/
lemma oriented_anchor_axis_point_mem_four_segments
    (base direction anchor : Point3)
    {sign r : ℝ}
    (horient :
      sign = 1 ∧ anchor = base ∨
        sign = -1 ∧ anchor = base + direction)
    (hr : r ∈ Set.Icc (-1 : ℝ) 2) :
    anchor + r • (sign • direction) ∈
      Kakeya.unitSegment (base - direction) (-direction) ∪
      Kakeya.unitSegment (base - direction) direction ∪
      Kakeya.unitSegment base direction ∪
      Kakeya.unitSegment (base + direction) direction := by
  rcases horient with ⟨hsign, hanchor⟩ | ⟨hsign, hanchor⟩
  · subst sign
    subst anchor
    exact signed_axis_point_mem_four_segments
      base direction (Or.inl rfl) hr
  · subst sign
    subst anchor
    let q : ℝ := 1 - r
    have hq : q ∈ Set.Icc (-1 : ℝ) 2 := by
      dsimp only [q]
      constructor <;> linarith [hr.1, hr.2]
    have hpoint :
        (base + direction) + r • ((-1 : ℝ) • direction) =
          base + q • ((1 : ℝ) • direction) := by
      dsimp only [q]
      module
    rw [hpoint]
    exact signed_axis_point_mem_four_segments
      base direction (Or.inl rfl) hq

/--
The repaired orientation-aware anchor always maps to the forward parameter
range `[-1,2]`, so three fixed forward unit segments suffice.
-/
lemma oriented_anchor_axis_point_mem_three_segments
    (base direction anchor : Point3)
    {sign r : ℝ}
    (horient :
      sign = 1 ∧ anchor = base ∨
        sign = -1 ∧ anchor = base + direction)
    (hr : r ∈ Set.Icc (-1 : ℝ) 2) :
    anchor + r • (sign • direction) ∈
      Kakeya.unitSegment (base - direction) direction ∪
      Kakeya.unitSegment base direction ∪
      Kakeya.unitSegment (base + direction) direction := by
  have hforward :
      ∃ q ∈ Set.Icc (-1 : ℝ) 2,
        anchor + r • (sign • direction) =
          base + q • direction := by
    rcases horient with ⟨hsign, hanchor⟩ | ⟨hsign, hanchor⟩
    · subst sign
      subst anchor
      exact ⟨r, hr, by simp⟩
    · subst sign
      subst anchor
      refine ⟨1 - r, ⟨by linarith [hr.2], by linarith [hr.1]⟩, ?_⟩
      module
  rcases hforward with ⟨q, hq, hpoint⟩
  rw [hpoint]
  by_cases h0 : q ≤ 0
  · have hp : q + 1 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hq.1]
    exact Or.inl (Or.inl ⟨q + 1, hp, by module⟩)
  · by_cases h1 : q ≤ 1
    · have hp : q ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> linarith
      exact Or.inl (Or.inr ⟨q, hp, rfl⟩)
    · have hp : q - 1 ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> linarith [hq.2]
      exact Or.inr ⟨q - 1, hp, by module⟩

end Kakeya.Assouad
