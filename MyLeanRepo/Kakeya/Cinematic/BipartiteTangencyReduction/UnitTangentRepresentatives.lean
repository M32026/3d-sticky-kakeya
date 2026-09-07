import MyLeanRepo.Kakeya.Cinematic.Geometry

/-!
# Unit tangent representatives

Choose one tangent function from each color for every rectangle in the
unit-multiplicity robust bipartite reduction.
-/

namespace Kakeya.Cinematic

lemma exists_tangent_representative
    {delta t tangency : ℝ}
    (rectangle : CurvilinearRectangle delta t)
    (functions : FiniteFunctionFamily)
    (hcount : 1 ≤ RectangleFamily.tangentCount rectangle functions tangency) :
    ∃ function : C2Function,
      function ∈ functions.carrier ∧
        rectangle.IsLambdaTangent function tangency := by
  classical
  let tangentFunctions :=
    functions.toFinset.filter fun function =>
      rectangle.IsLambdaTangent function tangency
  have hcard :
      tangentFunctions.card =
        RectangleFamily.tangentCount rectangle functions tangency := by
    rfl
  have hnonempty : tangentFunctions.Nonempty := by
    apply Finset.card_pos.mp
    rw [hcard]
    omega
  obtain ⟨function, hfunction⟩ := hnonempty
  have hfiltered := Finset.mem_filter.mp hfunction
  exact ⟨function,
    by simpa [FiniteFunctionFamily.toFinset] using hfiltered.1,
    hfiltered.2⟩

lemma exists_unit_tangent_representatives
    {delta t tangency : ℝ}
    (rectangles : RectangleFamily delta t)
    (white black : FiniteFunctionFamily)
    (hcounts : ∀ i,
      1 ≤ RectangleFamily.tangentCount
          (rectangles.rectangle i) white tangency ∧
        1 ≤ RectangleFamily.tangentCount
          (rectangles.rectangle i) black tangency) :
    ∃ whiteRepresentative blackRepresentative :
        Fin rectangles.card → C2Function,
      (∀ i,
        whiteRepresentative i ∈ white.carrier ∧
          (rectangles.rectangle i).IsLambdaTangent
            (whiteRepresentative i) tangency) ∧
      (∀ i,
        blackRepresentative i ∈ black.carrier ∧
          (rectangles.rectangle i).IsLambdaTangent
            (blackRepresentative i) tangency) := by
  choose whiteRepresentative hwhite using
    fun i => exists_tangent_representative
      (rectangles.rectangle i) white (hcounts i).1
  choose blackRepresentative hblack using
    fun i => exists_tangent_representative
      (rectangles.rectangle i) black (hcounts i).2
  exact ⟨whiteRepresentative, blackRepresentative, hwhite, hblack⟩

end Kakeya.Cinematic
