module

/-
  Covering number equality under bi-Lipschitz homothety.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section


noncomputable section

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MultiscaleDecomposition

namespace DirecretisedFurstenbergEstimate.MultiscaleDecomposition

/-- Covering number equality under a bi-Lipschitz map τ with scale L
    and inverse scale Da, where L * Da = 1. -/
lemma covering_number_equality
    {X : Type*} [PseudoMetricSpace X] {A : Set X}
    {τ τ_inv : X → X} {L Da : ℝ}
    (hL_pos : 0 < L) (hDa_pos : 0 < Da)
    (hL_Da : L * Da = 1)
    (h_lip : LipschitzWith L.toNNReal τ)
    (h_lip_inv : LipschitzWith Da.toNNReal τ_inv)
    (h_left_inv : ∀ x, τ_inv (τ x) = x)
    (ε : NNReal) :
    Metric.externalCoveringNumber (L.toNNReal * ε) (τ '' A) =
      Metric.externalCoveringNumber ε A := by
  have h_image_inv : τ_inv '' (τ '' A) = A := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, h_eq⟩
      have h_z : τ_inv (τ x) = z := h_eq
      have h_x_eq : z = x := by
        rw [h_left_inv x] at h_z
        exact h_z.symm
      rw [h_x_eq]
      exact hx
    · intro hz
      exact ⟨τ z, ⟨z, hz, rfl⟩, h_left_inv z⟩
  have h_forward : Metric.externalCoveringNumber (L.toNNReal * ε) (τ '' A) ≤
      Metric.externalCoveringNumber ε A := by
    exact DiscretisedFurstenbergEstimate.CoveringUtils.externalCoveringNumber_image_lipschitz
      (f := τ) (K := L.toNNReal) (ε := ε) (A := A) h_lip
  have h_mul : (L.toNNReal * ε) * Da.toNNReal = ε := by
    apply NNReal.eq
    have hL_nn : (L.toNNReal : ℝ) = L := by simp [hL_pos.le]
    have hDa_nn : ((Da.toNNReal : ℝ)) = Da := by simp [hDa_pos.le]
    have h_coe : (((L.toNNReal * ε) * Da.toNNReal : NNReal) : ℝ) =
        ((L.toNNReal : ℝ) * (ε : ℝ) * (Da.toNNReal : ℝ)) := by
      rw [NNReal.coe_mul, NNReal.coe_mul] <;> ring
    rw [h_coe, hL_nn, hDa_nn]
    have h_final : L * (ε : ℝ) * Da = (ε : ℝ) := by
      have h : L * Da = 1 := hL_Da
      calc L * (ε : ℝ) * Da
        = (L * Da) * (ε : ℝ) := by ring
      _ = 1 * (ε : ℝ) := by rw [h]
      _ = (ε : ℝ) := by ring
    exact h_final
  have h_comm : Da.toNNReal * (L.toNNReal * ε) = (L.toNNReal * ε) * Da.toNNReal := by
    apply mul_comm
  have h_backward : Metric.externalCoveringNumber ε A ≤
      Metric.externalCoveringNumber (L.toNNReal * ε) (τ '' A) := by
    have h : Metric.externalCoveringNumber (Da.toNNReal * (L.toNNReal * ε)) (τ_inv '' (τ '' A)) ≤
        Metric.externalCoveringNumber (L.toNNReal * ε) (τ '' A) :=
      DiscretisedFurstenbergEstimate.CoveringUtils.externalCoveringNumber_image_lipschitz
        (f := τ_inv) (K := Da.toNNReal) (ε := L.toNNReal * ε) (A := τ '' A) h_lip_inv
    rw [h_comm] at h
    rw [h_mul] at h
    rw [h_image_inv] at h
    exact h
  exact le_antisymm h_forward h_backward

end DirecretisedFurstenbergEstimate.MultiscaleDecomposition
