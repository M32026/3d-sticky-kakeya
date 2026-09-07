import MyLeanRepo.Kakeya.Cinematic.Section5.PointwiseRectangleShorteningInputs

/-!
# Shorten pointwise rectangles to a common scale

Given point-indexed fine rectangles at individual exact scales, apply
`rectangle_shortening` to each one to produce rectangles at the common upper
scale. All containment, midpoint, and tangency certificates are preserved.
-/

namespace Kakeya.Cinematic

theorem pointwise_rectangle_shortening :
    PointwiseRectangleShorteningStatement := by
  intro hRS
  intro family E K delta t Delta C_R I hI point hpoint center hcenter
        fiber hfiber exactScale hdelta hcommon hexact_pos hexact_le
        rectangle hfunc hmid hmidcentral hpointmem hcentral htangent
  let h₂ : ℝ := C_R * t * Delta / delta
  have hh₂ : 0 < h₂ := hcommon
  let S : E → CurvilinearRectangle delta h₂ := fun p =>
    Classical.choose
      (hRS (h₁ := exactScale p) (h₂ := h₂) hdelta
        (hexact_pos p) hh₂ (hexact_le p) (rectangle p))
  have hS_spec : ∀ (p : E),
      (S p).function = (rectangle p).function ∧
      (S p).interval.midpoint = (rectangle p).interval.midpoint ∧
      (S p).interval.carrier ⊆ (rectangle p).interval.carrier ∧
      (S p).carrier ⊆ (rectangle p).carrier ∧
      (∀ (q : UnitPoint × ℝ), q ∈ (rectangle p).carrier →
        (q.1 : ℝ) = (rectangle p).interval.midpoint → q ∈ (S p).carrier) ∧
      (∀ (J : ParameterInterval),
        (rectangle p).IsOverCentralQuarterOf J →
        (S p).IsOverCentralQuarterOf J) ∧
      ∀ (f : C2Function) (lambda : ℝ),
        (rectangle p).IsLambdaTangent f lambda →
        (S p).IsLambdaTangent f lambda := by
    intro p
    exact Classical.choose_spec
      (hRS (h₁ := exactScale p) (h₂ := h₂) hdelta
        (hexact_pos p) hh₂ (hexact_le p) (rectangle p))
  have h_main : ∃ (data : FineRectangleAssignmentData family E K delta t Delta C_R),
      data.interval = I ∧
      (∀ p : E, data.center p = center p) ∧
      ∀ p : E, data.fiber p = fiber p := by
    refine' ⟨{
      interval := I,
      intervalControlled := hI,
      point := point,
      point_coe := hpoint,
      center := center,
      center_mem := hcenter,
      fiber := fiber,
      fiber_subset := hfiber,
      rectangle := S,
      rectangle_function := by
        intro p
        rcases hS_spec p with ⟨hfunc', _, _, _, _, _, _⟩
        rw [hfunc', hfunc p],
      rectangle_midpoint := by
        intro p
        rcases hS_spec p with ⟨_, hmid', _, _, _, _, _⟩
        rw [hmid', hmid p],
      rectangle_midpoint_central := by
        intro p
        rcases hS_spec p with ⟨_, hmid', _, _, _, _, _⟩
        rw [hmid']
        exact hmidcentral p,
      point_mem_rectangle := by
        intro p
        rcases hS_spec p with ⟨_, _, _, _, hpreserve, _, _⟩
        have h1 : ((point p).1 : ℝ) = (rectangle p).interval.midpoint := by
          have h2 : ((point p).1 : ℝ) = (p : ℝ × ℝ).1 :=
            congrArg Prod.fst (hpoint p)
          rw [h2, hmid p]
        exact hpreserve (point p) (hpointmem p) h1,
      rectangle_central := by
        intro p
        rcases hS_spec p with ⟨_, _, _, _, _, hcentral', _⟩
        exact hcentral' I (hcentral p),
      fiber_tangent := by
        intro p f hf
        rcases hS_spec p with ⟨_, _, _, _, _, _, htangent'⟩
        exact htangent' f 5 (htangent p f hf)
    }, rfl, fun _ => rfl, fun _ => rfl⟩
  exact h_main

end Kakeya.Cinematic
