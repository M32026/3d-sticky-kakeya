import MyLeanRepo.Kakeya.Cinematic.Section5.LocalAssembly.Infrastructure

/-!
# Tangency bounds for the local cinematic assembly

The first two-ends selection localizes a finite family to a `C²` ball of
radius `t`. This module turns that metric localization into the uniform
tangency-parameter upper bound needed by the second two-ends selection.
-/

noncomputable section

open Set

namespace Kakeya.Cinematic

lemma localAssembly_tangencyParameterOn_nonneg
    (I : ParameterInterval) (f g : C2Function) :
    0 ≤ tangencyParameterOn I f g := by
  let value : UnitPoint → ℝ := fun x =>
    |f x - g x| + |f.firstDeriv x - g.firstDeriv x|
  let S : Set UnitPoint := I.centeredCarrier (1 / 2)
  have hmid_mem : I.midpoint ∈ unitInterval := by
    simp only [unitInterval, Set.mem_Icc, ParameterInterval.midpoint]
    constructor <;>
      linarith [I.left_mem.1, I.left_mem.2, I.right_mem.1,
        I.right_mem.2, I.left_le_right]
  let midpoint : UnitPoint := ⟨I.midpoint, hmid_mem⟩
  have hmidS : midpoint ∈ S := by
    rw [show S = I.centeredCarrier (1 / 2) by rfl]
    simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq,
      midpoint, Subtype.coe_mk, sub_self, abs_zero]
    have hlength := I.length_nonneg
    positivity
  have hS_nonempty : S.Nonempty := ⟨midpoint, hmidS⟩
  have hnonneg : ∀ r ∈ value '' S, 0 ≤ r := by
    intro r hr
    rcases hr with ⟨x, _, rfl⟩
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hset :
      {r : ℝ |
        ∃ x ∈ I.centeredCarrier (1 / 2),
          r = |f x - g x| + |f.firstDeriv x - g.firstDeriv x|} =
        value '' S := by
    ext r
    simp [value, S, Set.mem_image]
    aesop
  rw [tangencyParameterOn, hset]
  exact le_csInf (hS_nonempty.image value) hnonneg

lemma localAssembly_tangencyParameterOn_le
    (I : ParameterInterval) (f g : C2Function) :
    tangencyParameterOn I f g ≤ 2 * c2Distance f g := by
  let value : UnitPoint → ℝ := fun x =>
    |f x - g x| + |f.firstDeriv x - g.firstDeriv x|
  let S : Set UnitPoint := I.centeredCarrier (1 / 2)
  have hmid_mem : I.midpoint ∈ unitInterval := by
    simp only [unitInterval, Set.mem_Icc, ParameterInterval.midpoint]
    constructor <;>
      linarith [I.left_mem.1, I.left_mem.2, I.right_mem.1,
        I.right_mem.2, I.left_le_right]
  let midpoint : UnitPoint := ⟨I.midpoint, hmid_mem⟩
  have hmidS : midpoint ∈ S := by
    rw [show S = I.centeredCarrier (1 / 2) by rfl]
    simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq,
      midpoint, Subtype.coe_mk, sub_self, abs_zero]
    have hlength := I.length_nonneg
    positivity
  have hvalue_mem : value midpoint ∈ value '' S :=
    ⟨midpoint, hmidS, rfl⟩
  have hbdd : BddBelow (value '' S) := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨x, _, rfl⟩
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsInf : sInf (value '' S) ≤ value midpoint :=
    csInf_le hbdd hvalue_mem
  have hvalue :
      value midpoint ≤ 2 * c2Distance f g := by
    dsimp only [value]
    have h0 := abs_value_sub_le_c2Distance f g midpoint
    have h1 := abs_firstDeriv_sub_le_c2Distance f g midpoint
    linarith
  have hset :
      {r : ℝ |
        ∃ x ∈ I.centeredCarrier (1 / 2),
          r = |f x - g x| + |f.firstDeriv x - g.firstDeriv x|} =
        value '' S := by
    ext r
    simp [value, S, Set.mem_image]
    aesop
  rw [tangencyParameterOn, hset]
  exact hsInf.trans hvalue

lemma localAssembly_dist_le_two_mul_of_mem_ball
    {center f g : C2Function} {t : ℝ}
    (hf : f ∈ c2Ball center t) (hg : g ∈ c2Ball center t) :
    dist f g ≤ 2 * t := by
  have hfc : dist f center ≤ t := by
    simpa [c2Distance_eq_dist] using (mem_c2Ball.mp hf)
  have hgc : dist g center ≤ t := by
    simpa [c2Distance_eq_dist] using (mem_c2Ball.mp hg)
  calc
    dist f g ≤ dist f center + dist center g := dist_triangle _ _ _
    _ = dist f center + dist g center := by rw [dist_comm center g]
    _ ≤ 2 * t := by linarith

lemma localAssembly_tangencyParameterOn_le_four_mul
    {I : ParameterInterval} {center f g : C2Function} {t : ℝ}
    (hf : f ∈ c2Ball center t) (hg : g ∈ c2Ball center t) :
    tangencyParameterOn I f g ≤ 4 * t := by
  calc
    tangencyParameterOn I f g ≤ 2 * c2Distance f g :=
      localAssembly_tangencyParameterOn_le I f g
    _ = 2 * dist f g := by rfl
    _ ≤ 2 * (2 * t) := by
      gcongr
      exact localAssembly_dist_le_two_mul_of_mem_ball hf hg
    _ = 4 * t := by ring

lemma localAssembly_tangency_bounds_of_localized
    {I : ParameterInterval} {center : C2Function} {t : ℝ}
    {G : FiniteFunctionFamily}
    (hG : G.carrier ⊆ c2Ball center t) :
    ∀ ⦃f⦄, f ∈ G.carrier →
      ∀ ⦃g⦄, g ∈ G.carrier →
        0 ≤ tangencyParameterOn I f g ∧
          tangencyParameterOn I f g ≤ 4 * t := by
  intro f hf g hg
  exact
    ⟨localAssembly_tangencyParameterOn_nonneg I f g,
      localAssembly_tangencyParameterOn_le_four_mul
        (hG hf) (hG hg)⟩

end Kakeya.Cinematic
