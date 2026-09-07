import MyLeanRepo.Kakeya.Cinematic.Geometry

/-!
# Property transfer for rectangle subfamilies

Simple lemmas that transfer `CentersIn`, `IsOverCentralQuarterOf`, and
`Nonempty` from a `RectangleFamily` to a `RectangleSubfamily`.
-/

namespace Kakeya.Cinematic

namespace RectangleSubfamily

/-- The `CentersIn` property transfers to any subfamily. -/
lemma centersIn_transfer {δ t : ℝ} {R : RectangleFamily δ t}
    (S : RectangleSubfamily R) {family : Set C2Function}
    (h : R.CentersIn family) : S.family.CentersIn family := by
  intro i
  exact h (S.embedding i)

/-- The `IsOverCentralQuarterOf` property transfers to any subfamily. -/
lemma overCentralQuarter_transfer {δ t : ℝ} {R : RectangleFamily δ t}
    (S : RectangleSubfamily R) {I : ParameterInterval}
    (h : R.IsOverCentralQuarterOf I) :
    S.family.IsOverCentralQuarterOf I := by
  intro i
  exact h (S.embedding i)

/--
If `R` is nonempty and its cardinality is bounded by a positive multiple of
the subfamily cardinality, then the subfamily is nonempty.
-/
lemma nonempty_transfer {δ t : ℝ} {R : RectangleFamily δ t}
    (S : RectangleSubfamily R) (hR : R.Nonempty)
    {C : ℝ} (_hC : 0 < C)
    (hbound : (R.card : ℝ) ≤ C * (S.card : ℝ)) :
    S.family.Nonempty := by
  have hRpos : 0 < (R.card : ℝ) := by exact_mod_cast hR
  by_contra h
  have hS0 : S.family.card = 0 := by
    simpa [RectangleFamily.Nonempty] using h
  have hS_card : S.card = 0 := by
    have h_eq : S.family.card = S.card := by rfl
    rw [h_eq] at hS0
    exact hS0
  rw [hS_card] at hbound
  have h_cont : (R.card : ℝ) ≤ 0 := by simpa using hbound
  linarith

end RectangleSubfamily

end Kakeya.Cinematic
