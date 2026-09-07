module

/-
  Energy bound from common-tube intersection counts.

  Pure combinatorial lemma: if the number of tubes containing both x and y
  is bounded by C_T * dist(x,y)^{-s}, then the total (t-s)-energy over all
  tube fibers is bounded by C_T * (t-energy of Q).

  Whiteprint node: Phase2 / EnergyBoundFromCommonTubes
  Dependencies: CommonTubeEnergyExtraction (definitions)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Phase2

/-- Double-counting identity: sum over tube fibers equals sum over pairs
    weighted by common-tube count. -/
lemma fiber_pair_sum_rearrangement
    {X Tube : Type*} [DecidableEq X] [DecidableEq Tube]
    (Q : Finset X) (𝒯 : Finset Tube)
    (fiber : Tube → Finset X)
    (hfiber : ∀ T ∈ 𝒯, fiber T ⊆ Q)
    (g : X → X → ℝ) :
    ∑ T ∈ 𝒯, ∑ x ∈ fiber T, ∑ y ∈ (fiber T).erase x, g x y =
    ∑ x ∈ Q, ∑ y ∈ Q.erase x,
      ((𝒯.filter (fun T => x ∈ fiber T ∧ y ∈ fiber T)).card : ℝ) * g x y := by
  let h : Tube → X → X → ℝ := fun T x y =>
    if x ∈ fiber T ∧ y ∈ fiber T ∧ x ≠ y then g x y else 0

  have h1 : ∀ (T : Tube), T ∈ 𝒯 →
      ∑ x ∈ fiber T, ∑ y ∈ (fiber T).erase x, g x y =
      ∑ x ∈ Q, ∑ y ∈ Q, h T x y := by
    intro T hT
    have hFT : fiber T ⊆ Q := hfiber T hT
    have h_inner : ∀ (x : X), x ∈ fiber T →
        ∑ y ∈ (fiber T).erase x, g x y = ∑ y ∈ Q, h T x y := by
      intro x hx
      have h_sub : (fiber T).erase x ⊆ Q := by
        intro y hy
        exact hFT ((Finset.mem_erase.mp hy).2)
      have h_eq1 : ∑ y ∈ (fiber T).erase x, g x y =
          ∑ y ∈ (fiber T).erase x, h T x y := by
        apply Finset.sum_congr rfl
        intro y hy
        have h4 : y ∈ fiber T := (Finset.mem_erase.mp hy).2
        have h5 : y ≠ x := (Finset.mem_erase.mp hy).1
        have h6 : x ≠ y := Ne.symm h5
        simp [h, h4, h6, hx]
      have h_ext : ∑ y ∈ (fiber T).erase x, h T x y = ∑ y ∈ Q, h T x y := by
        apply Finset.sum_subset h_sub
        intro y hyQ hy_not
        have h7 : y ∉ (fiber T).erase x := hy_not
        have h8 : h T x y = 0 := by
          unfold h
          have h9 : ¬(x ∈ fiber T ∧ y ∈ fiber T ∧ x ≠ y) := by
            intro h10
            have h11 : y ∈ (fiber T).erase x := by
              exact Finset.mem_erase.mpr ⟨Ne.symm h10.2.2, h10.2.1⟩
            exact h7 h11
          rw [if_neg h9]
        exact h8
      rw [h_eq1, h_ext]
    have h2 : ∑ x ∈ fiber T, ∑ y ∈ (fiber T).erase x, g x y =
        ∑ x ∈ fiber T, ∑ y ∈ Q, h T x y := by
      apply Finset.sum_congr rfl
      intro x hx
      exact h_inner x hx
    have h_outer : ∑ x ∈ fiber T, ∑ y ∈ Q, h T x y =
        ∑ x ∈ Q, ∑ y ∈ Q, h T x y := by
      apply Finset.sum_subset hFT
      intro x hxQ hx_not
      have h4 : x ∉ fiber T := hx_not
      have h5 : ∑ y ∈ Q, h T x y = 0 := by
        apply Finset.sum_eq_zero
        intro y _
        unfold h
        have h6 : ¬(x ∈ fiber T ∧ y ∈ fiber T ∧ x ≠ y) := by
          intro h7
          exact h4 h7.1
        rw [if_neg h6]
      exact h5
    rw [h2, h_outer]

  have h_main1 : ∑ T ∈ 𝒯, ∑ x ∈ fiber T, ∑ y ∈ (fiber T).erase x, g x y =
      ∑ T ∈ 𝒯, ∑ x ∈ Q, ∑ y ∈ Q, h T x y := by
    apply Finset.sum_congr rfl
    intro T hT
    exact h1 T hT

  have h_comm : ∑ T ∈ 𝒯, ∑ x ∈ Q, ∑ y ∈ Q, h T x y =
      ∑ x ∈ Q, ∑ y ∈ Q, ∑ T ∈ 𝒯, h T x y := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    <;> rfl

  rw [h_main1, h_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have h4 : ∑ y ∈ Q, ∑ T ∈ 𝒯, h T x y =
      ∑ y ∈ Q.erase x, ∑ T ∈ 𝒯, h T x y := by
    have h5 : x ∈ Q := hx
    have h6 : ∑ T ∈ 𝒯, h T x x = 0 := by
      apply Finset.sum_eq_zero
      intro T _
      unfold h
      have h7 : ¬(x ∈ fiber T ∧ x ∈ fiber T ∧ x ≠ x) := by
        intro h8
        exact h8.2.2 rfl
      rw [if_neg h7]
    have h9 : insert x (Q.erase x) = Q := Finset.insert_erase h5
    have h10 : ∑ y ∈ Q, (∑ T ∈ 𝒯, h T x y) =
        ∑ T ∈ 𝒯, h T x x + ∑ y ∈ Q.erase x, (∑ T ∈ 𝒯, h T x y) := by
      have h11 : ∑ y ∈ insert x (Q.erase x), (∑ T ∈ 𝒯, h T x y) =
          ∑ T ∈ 𝒯, h T x x + ∑ y ∈ Q.erase x, (∑ T ∈ 𝒯, h T x y) := by
        rw [Finset.sum_insert (by simp)]
        <;> ring
      rw [h9] at h11
      exact h11
    have h8 : ∑ y ∈ Q, (∑ T ∈ 𝒯, h T x y) =
        ∑ y ∈ Q.erase x, (∑ T ∈ 𝒯, h T x y) + ∑ T ∈ 𝒯, h T x x := by
      rw [h10] <;> ring
    rw [h8, h6] <;> ring
  rw [h4]
  apply Finset.sum_congr rfl
  intro y hy
  have h_y_ne_x : y ≠ x := (Finset.mem_erase.mp hy).1
  have h_x_ne_y : x ≠ y := Ne.symm h_y_ne_x
  have h5 : ∑ T ∈ 𝒯, h T x y =
      ((𝒯.filter (fun T => x ∈ fiber T ∧ y ∈ fiber T)).card : ℝ) * g x y := by
    have h6 : ∀ T ∈ 𝒯, h T x y =
        if x ∈ fiber T ∧ y ∈ fiber T then g x y else 0 := by
      intro T _
      simp only [h]
      have h7 : x ≠ y := h_x_ne_y
      simp [h7]
      <;> aesop
    rw [Finset.sum_congr rfl h6]
    rw [Finset.sum_ite]
    simp [Finset.sum_const, mul_comm]
    <;> ring
  exact h5

/-- **Total energy bound from common-tube intersection counts.**

    If for every pair x ≠ y in Q, the number of tubes containing both
    is at most C_T * dist(x,y)^{-s}, then:

    Σ_{T ∈ 𝒯} pairEnergy (t-s) (fiber T) ≤ C_T * pairEnergy t Q
-/
lemma energy_bound_from_common_tubes
    {X Tube : Type*} [MetricSpace X] [DecidableEq X] [DecidableEq Tube]
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s ≤ t)
    {C_T : ℝ} (hCT_pos : 0 ≤ C_T)
    (Q : Finset X) (𝒯 : Finset Tube)
    (fiber : Tube → Finset X)
    (hfiber : ∀ T ∈ 𝒯, fiber T ⊆ Q)
    (h_common : ∀ (x : X) (hx : x ∈ Q) (y : X) (hy : y ∈ Q),
      x ≠ y →
        ((𝒯.filter (fun T => x ∈ fiber T ∧ y ∈ fiber T)).card : ℝ) ≤
          C_T * Real.rpow (dist x y) (-s)) :
    ∑ T ∈ 𝒯, pairEnergy (t - s) (fiber T) ≤
      C_T * pairEnergy t Q := by
  set u := t - s with hu_def
  have h_u_nonneg : 0 ≤ u := by linarith
  have h_su : s + u = t := by linarith

  have h1 : ∑ T ∈ 𝒯, pairEnergy u (fiber T) =
      ∑ x ∈ Q, ∑ y ∈ Q.erase x,
        ((𝒯.filter (fun T => x ∈ fiber T ∧ y ∈ fiber T)).card : ℝ) *
        Real.rpow (dist x y) (-u) :=
    fiber_pair_sum_rearrangement Q 𝒯 fiber hfiber
      (fun x y => Real.rpow (dist x y) (-u))

  rw [h1]
  have h2 : ∀ x ∈ Q, ∀ y ∈ Q.erase x,
      ((𝒯.filter (fun T => x ∈ fiber T ∧ y ∈ fiber T)).card : ℝ) *
        Real.rpow (dist x y) (-u) ≤
      C_T * Real.rpow (dist x y) (-s) * Real.rpow (dist x y) (-u) := by
    intro x hx y hy
    have h_y_ne_x : y ≠ x := (Finset.mem_erase.mp hy).1
    have h_y_in_Q : y ∈ Q := (Finset.mem_erase.mp hy).2
    have h_x_ne_y : x ≠ y := Ne.symm h_y_ne_x
    have h4 : ((𝒯.filter (fun T => x ∈ fiber T ∧ y ∈ fiber T)).card : ℝ) ≤
        C_T * Real.rpow (dist x y) (-s) := h_common x hx y h_y_in_Q h_x_ne_y
    have h5 : 0 ≤ Real.rpow (dist x y) (-u) := Real.rpow_nonneg dist_nonneg _
    nlinarith
  have h3 : ∑ x ∈ Q, ∑ y ∈ Q.erase x,
      ((𝒯.filter (fun T => x ∈ fiber T ∧ y ∈ fiber T)).card : ℝ) *
        Real.rpow (dist x y) (-u) ≤
      ∑ x ∈ Q, ∑ y ∈ Q.erase x,
        C_T * Real.rpow (dist x y) (-s) * Real.rpow (dist x y) (-u) := by
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro y hy
    exact h2 x hx y hy
  have h_rpow : ∀ (x y : X), x ≠ y →
      Real.rpow (dist x y) (-s) * Real.rpow (dist x y) (-u) =
      Real.rpow (dist x y) (-(s + u)) := by
    intro x y hxy
    have h_pos : 0 < dist x y := dist_pos.mpr hxy
    have h : Real.rpow (dist x y) ((-s) + (-u)) =
        Real.rpow (dist x y) (-s) * Real.rpow (dist x y) (-u) :=
      Real.rpow_add h_pos (-s) (-u)
    have h2 : (-s) + (-u) = -(s + u) := by ring
    rw [h2] at h
    exact h.symm
  calc
    ∑ x ∈ Q, ∑ y ∈ Q.erase x, _ ≤
      ∑ x ∈ Q, ∑ y ∈ Q.erase x,
        C_T * Real.rpow (dist x y) (-s) * Real.rpow (dist x y) (-u) := h3
    _ = C_T * ∑ x ∈ Q, ∑ y ∈ Q.erase x,
          Real.rpow (dist x y) (-(s + u)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      have h_y_ne_x : y ≠ x := (Finset.mem_erase.mp hy).1
      have h_x_ne_y : x ≠ y := Ne.symm h_y_ne_x
      have h9 : Real.rpow (dist x y) (-s) * Real.rpow (dist x y) (-u) =
          Real.rpow (dist x y) (-(s + u)) := h_rpow x y h_x_ne_y
      have h_eq : C_T * Real.rpow (dist x y) (-s) * Real.rpow (dist x y) (-u) =
          C_T * Real.rpow (dist x y) (-(s + u)) := by
        calc
          C_T * Real.rpow (dist x y) (-s) * Real.rpow (dist x y) (-u)
            = C_T * (Real.rpow (dist x y) (-s) * Real.rpow (dist x y) (-u)) := by ring
          _ = C_T * Real.rpow (dist x y) (-(s + u)) := by rw [h9]
      exact h_eq
    _ = C_T * pairEnergy t Q := by
      rw [show s + u = t from by linarith]
      <;> rfl

end DirecretisedFurstenbergEstimate.Phase2
