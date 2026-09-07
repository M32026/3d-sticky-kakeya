import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Point-dependent fine rectangles and their shadings

These definitions retain the point-dependent center function and tangent
fiber produced by the two two-ends reductions in PYZ Section 5.
-/

noncomputable section

namespace Kakeya.Cinematic

/--
The output after dyadic pigeonholing has fixed common scales `t` and `Delta`.
Every point of `E₂` then carries its own center function, tangent fiber, and
fine rectangle at those common scales.
-/
structure FineRectangleAssignmentData
    (family : Set C2Function) (E₂ : Set (ℝ × ℝ))
    (K delta t Delta C_R : ℝ) where
  interval : ParameterInterval
  intervalControlled : interval.IsControlled K
  point : E₂ → UnitPoint × ℝ
  point_coe : ∀ p : E₂,
    (((point p).1 : ℝ), (point p).2) = p
  center : E₂ → C2Function
  center_mem : ∀ p, center p ∈ family
  fiber : E₂ → FiniteFunctionFamily
  fiber_subset : ∀ p, (fiber p).carrier ⊆ family
  rectangle : E₂ →
    CurvilinearRectangle delta (C_R * t * Delta / delta)
  rectangle_function : ∀ p, (rectangle p).function = center p
  rectangle_midpoint : ∀ p, (rectangle p).interval.midpoint = p.1.1
  rectangle_midpoint_central : ∀ p,
    |(rectangle p).interval.midpoint - interval.midpoint| ≤
      interval.length / 16
  point_mem_rectangle : ∀ p, point p ∈ (rectangle p).carrier
  rectangle_central : ∀ p,
    (rectangle p).IsOverCentralQuarterOf interval
  fiber_tangent : ∀ p, ∀ f ∈ (fiber p).carrier,
    (rectangle p).IsLambdaTangent f 5

/-- The inner shading `Y₂'(R)` from PYZ Section 5. -/
def fineInnerShading
    {family : Set C2Function} {E₂ : Set (ℝ × ℝ)}
    {K delta t Delta C_R : ℝ}
    (data : FineRectangleAssignmentData family E₂ K delta t Delta C_R)
    (R : CurvilinearRectangle delta (C_R * t * Delta / delta)) :
    Set (ℝ × ℝ) :=
  {p | ∃ hp : p ∈ E₂,
    (data.rectangle ⟨p, hp⟩).AreLambdaComparable R family 100 ∧
    data.point ⟨p, hp⟩ ∈ R.carrier}

/-- The enlarged shading `Y₂(R)` from PYZ Section 5. -/
def fineOuterShading
    {family : Set C2Function} {E₂ : Set (ℝ × ℝ)}
    {K delta t Delta C_R : ℝ}
    (data : FineRectangleAssignmentData family E₂ K delta t Delta C_R)
    (C_s : ℝ)
    (R : CurvilinearRectangle delta (C_R * t * Delta / delta)) :
    Set (ℝ × ℝ) :=
  {p | ∃ hp : p ∈ E₂,
    (data.rectangle ⟨p, hp⟩).AreLambdaComparable R family C_s ∧
    ∃ U : CurvilinearRectangle
        (C_s * delta) (C_R * t * Delta / delta),
      U.function = R.function ∧
      U.interval.midpoint = R.interval.midpoint ∧
      R.carrier ⊆ U.carrier ∧
      data.point ⟨p, hp⟩ ∈ U.carrier}

end Kakeya.Cinematic
