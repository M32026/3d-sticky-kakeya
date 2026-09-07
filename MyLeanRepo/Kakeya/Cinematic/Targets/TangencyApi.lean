import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# Tangency parameter API validation

This target validates the minimum-attainment and closed-sublevel properties
required before formalizing the remaining parts of PYZ Lemma 16.
-/

namespace Kakeya.Cinematic

theorem tangency_api : TangencyApiStatement := by
  intro I f g
  let h : UnitPoint → ℝ := fun x =>
    |f x - g x| + |f.firstDeriv x - g.firstDeriv x|
  have h_cont : Continuous h :=
    (f.value.continuous.sub g.value.continuous).abs.add
      (f.firstDeriv.continuous.sub g.firstDeriv.continuous).abs
  let S := I.centeredCarrier (1 / 2)

  -- The midpoint of I, as a UnitPoint
  have h_mid_in_interval : I.midpoint ∈ unitInterval := by
    simp only [unitInterval, Set.mem_Icc, ParameterInterval.midpoint]
    constructor <;> linarith [I.left_mem.1, I.left_mem.2, I.right_mem.1, I.right_mem.2, I.left_le_right]
  let x_mid : UnitPoint := ⟨I.midpoint, h_mid_in_interval⟩

  -- x_mid belongs to I.carrier
  have h_x_mid_in_carrier : x_mid ∈ I.carrier := by
    simp only [ParameterInterval.carrier, Set.mem_setOf_eq]
    constructor
    · simp [x_mid, ParameterInterval.midpoint]
      linarith [I.left_le_right]
    · simp [x_mid, ParameterInterval.midpoint]
      linarith [I.left_le_right]

  -- x_mid belongs to S
  have h_x_mid_in_S : x_mid ∈ S := by
    simp only [S, ParameterInterval.centeredCarrier, Set.mem_setOf_eq]
    simp [x_mid, ParameterInterval.midpoint]
    linarith [I.length_nonneg]

  have hS_nonempty : S.Nonempty := ⟨x_mid, h_x_mid_in_S⟩

  -- S is closed
  have hS_closed : IsClosed S := by
    simp only [S, ParameterInterval.centeredCarrier, Set.mem_setOf_eq]
    exact isClosed_le (continuous_subtype_val.sub continuous_const).abs continuous_const

  -- S is compact (closed subset of compact UnitPoint)
  have hS_compact : IsCompact S := hS_closed.isCompact

  -- The set in the sInf definition is h '' S
  have h_set_eq : {r : ℝ | ∃ x ∈ S, r = h x} = h '' S := by
    ext r
    simp [Set.mem_image]
    aesop

  -- Part 1: nonnegativity
  have h1 : 0 ≤ tangencyParameterOn I f g := by
    have h_bdd : ∀ r ∈ h '' S, 0 ≤ r := by
      intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [tangencyParameterOn, h_set_eq]
    exact le_csInf (hS_nonempty.image h) h_bdd

  -- Part 2: attainment
  have h2 : ∃ x ∈ S, tangencyParameterOn I f g = h x := by
    rcases hS_compact.exists_isMinOn hS_nonempty h_cont.continuousOn with ⟨x0, hx0, hx0_min⟩
    have h_min_in : h x0 ∈ h '' S := ⟨x0, hx0, rfl⟩
    have h_min_le : ∀ y ∈ h '' S, h x0 ≤ y := by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact hx0_min hx
    have h_bdd_below : BddBelow (h '' S) := ⟨0, fun r hr => by
      rcases hr with ⟨x, _, rfl⟩
      exact add_nonneg (abs_nonneg _) (abs_nonneg _)⟩
    have h_sInf_eq : sInf (h '' S) = h x0 := by
      have h1 : sInf (h '' S) ≤ h x0 := csInf_le h_bdd_below h_min_in
      have h2 : h x0 ≤ sInf (h '' S) := le_csInf (hS_nonempty.image h) h_min_le
      linarith
    refine ⟨x0, hx0, ?_⟩
    rw [tangencyParameterOn, h_set_eq, h_sInf_eq]

  -- Part 3: closedness of sublevel sets
  have h3 : ∀ delta : ℝ, IsClosed (tangencySublevelSetOn I f g delta) := by
    intro delta
    have h_q4_closed : IsClosed (I.centeredCarrier (1 / 4)) := by
      simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq]
      exact isClosed_le (continuous_subtype_val.sub continuous_const).abs continuous_const
    have h_c : Continuous (fun x : UnitPoint => |f x - g x|) :=
      (f.value.continuous.sub g.value.continuous).abs
    have h_abs_closed : IsClosed {x : UnitPoint | |f x - g x| ≤ delta} :=
      isClosed_Iic.preimage h_c
    have h_set_eq2 : tangencySublevelSetOn I f g delta =
        I.centeredCarrier (1 / 4) ∩ {x : UnitPoint | |f x - g x| ≤ delta} := by
      ext x
      simp [tangencySublevelSetOn]
    rw [h_set_eq2]
    exact h_q4_closed.inter h_abs_closed

  exact ⟨h1, h2, h3⟩

end Kakeya.Cinematic
