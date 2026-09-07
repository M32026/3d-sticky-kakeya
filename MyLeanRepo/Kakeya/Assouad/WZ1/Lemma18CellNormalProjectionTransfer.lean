import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma18CellNormalProjectionTransferStatements
import MyLeanRepo.Kakeya.Assouad.LargeSlope.ExternalCoveringNumberIsometry

/-!
# WZ1 Lemma 18: transfer projection to the square-root cell normal

Prove the metric projection-transfer leaf without selecting good lines,
constructing grains, or asserting the final interval estimate.
-/

namespace Kakeya.Assouad

theorem wz1_lemma18_cell_normal_projection_transfer :
    WZ1Lemma18CellNormalProjectionTransferStatement := by
  intro rho tau K hrho htau htau_rho hK E planeMap localCenter cellCenter hdist hlip
  let n1 := planeMap cellCenter
  let n2 := planeMap localCenter
  let localPiece := E ∩ Metric.closedBall localCenter tau
  let C1 := wz1CenteredScalarProjection localCenter n1 localPiece
  let C2 := wz1CenteredScalarProjection localCenter n2 localPiece

  have h_epsilon_pos : 0 < 2 * K * rho := by positivity

  -- Step 1: Centered containment C1 ⊆ cthickening (2 * K * rho) C2
  have h_containment : C1 ⊆ Metric.cthickening (2 * K * rho) C2 := by
    intro y1 hy1
    rcases hy1 with ⟨x, hx, rfl⟩
    have hx_local : x ∈ localPiece := hx
    have hx_ball : x ∈ Metric.closedBall localCenter tau := hx_local.2
    have hdist_x : dist x localCenter ≤ tau := hx_ball
    let y2 := inner ℝ (x - localCenter) n2
    have hy2 : y2 ∈ C2 := ⟨x, hx_local, rfl⟩
    have h_norm1 : ‖n1 - n2‖ = ‖n2 - n1‖ := by
      have h : n1 - n2 = -(n2 - n1) := by abel
      rw [h]
      rw [norm_neg]
    have h4 : ‖n1 - n2‖ ≤ K * dist localCenter cellCenter := by
      rw [h_norm1]
      simpa [n1, n2, dist_eq_norm] using hlip
    have h5 : ‖n1 - n2‖ ≤ 2 * K * Real.sqrt rho := by
      calc
        ‖n1 - n2‖ ≤ K * dist localCenter cellCenter := h4
        _ ≤ K * (2 * Real.sqrt rho) := by gcongr
        _ = 2 * K * Real.sqrt rho := by ring
    have h3 : ‖x - localCenter‖ ≤ tau := by
      simpa [dist_eq_norm] using hdist_x
    have h_cs : |inner ℝ (x - localCenter) (n1 - n2)| ≤
        ‖x - localCenter‖ * ‖n1 - n2‖ :=
      abs_real_inner_le_norm (x - localCenter) (n1 - n2)
    have h_diff : inner ℝ (x - localCenter) n1 - y2 =
        inner ℝ (x - localCenter) (n1 - n2) := by
      simp [y2, inner_sub_right]
    have h6 : |inner ℝ (x - localCenter) n1 - y2| ≤
        tau * (2 * K * Real.sqrt rho) := by
      rw [h_diff]
      calc
        |inner ℝ (x - localCenter) (n1 - n2)|
          ≤ ‖x - localCenter‖ * ‖n1 - n2‖ := h_cs
        _ ≤ tau * ‖n1 - n2‖ := by gcongr
        _ ≤ tau * (2 * K * Real.sqrt rho) := by gcongr
    have hsqrt_sq : Real.sqrt rho * Real.sqrt rho = rho :=
      Real.mul_self_sqrt (by linarith)
    have h7 : tau * (2 * K * Real.sqrt rho) ≤ 2 * K * rho := by
      have h8 : tau * Real.sqrt rho ≤ rho := by
        calc
          tau * Real.sqrt rho
            ≤ (Real.sqrt rho) * Real.sqrt rho := by gcongr
          _ = rho := hsqrt_sq
      calc
        tau * (2 * K * Real.sqrt rho)
          = 2 * K * (tau * Real.sqrt rho) := by ring
        _ ≤ 2 * K * rho := by gcongr
    have h9 : |inner ℝ (x - localCenter) n1 - y2| ≤ 2 * K * rho :=
      h6.trans h7
    have h10 : dist (inner ℝ (x - localCenter) n1) y2 ≤ 2 * K * rho := by
      simpa [Real.dist_eq] using h9
    exact Metric.mem_cthickening_of_dist_le
      (inner ℝ (x - localCenter) n1) y2 (2 * K * rho) C2 hy2 h10

  -- Step 2: Covering number transfer for centered projections
  have h_centered_bound :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho) C1) : ENNReal) ≤
      (2 * Nat.ceil ((2 * K * rho) / rho) + 2 : ENNReal) *
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho) C2) : ENNReal) :=
    externalCoveringNumber_of_subset_cthickening
      hrho h_epsilon_pos h_containment le_rfl

  -- Step 3: Translation invariance
  have h_trans1 : C1 = (fun t : ℝ => t - inner ℝ localCenter n1) ''
      scalarProjection n1 localPiece := by
    ext y
    simp only [C1, wz1CenteredScalarProjection, scalarProjection,
      Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨inner ℝ x n1, ⟨x, hx, rfl⟩, ?_⟩
      have h : inner ℝ (x - localCenter) n1 =
          inner ℝ x n1 - inner ℝ localCenter n1 := by
        rw [inner_sub_left]
      exact h.symm
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      have h : inner ℝ (x - localCenter) n1 =
          inner ℝ x n1 - inner ℝ localCenter n1 := by
        rw [inner_sub_left]
      exact h
  have h_trans2 : C2 = (fun t : ℝ => t - inner ℝ localCenter n2) ''
      scalarProjection n2 localPiece := by
    ext y
    simp only [C2, wz1CenteredScalarProjection, scalarProjection,
      Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨inner ℝ x n2, ⟨x, hx, rfl⟩, ?_⟩
      have h : inner ℝ (x - localCenter) n2 =
          inner ℝ x n2 - inner ℝ localCenter n2 := by
        rw [inner_sub_left]
      exact h.symm
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      have h : inner ℝ (x - localCenter) n2 =
          inner ℝ x n2 - inner ℝ localCenter n2 := by
        rw [inner_sub_left]
      exact h

  have h_cover1 : Metric.externalCoveringNumber (Real.toNNReal rho) C1 =
      Metric.externalCoveringNumber (Real.toNNReal rho)
        (scalarProjection n1 localPiece) := by
    rw [h_trans1]
    exact translation_externalCoveringNumber (inner ℝ localCenter n1)
      (scalarProjection n1 localPiece) (Real.toNNReal rho)
  have h_cover2 : Metric.externalCoveringNumber (Real.toNNReal rho) C2 =
      Metric.externalCoveringNumber (Real.toNNReal rho)
        (scalarProjection n2 localPiece) := by
    rw [h_trans2]
    exact translation_externalCoveringNumber (inner ℝ localCenter n2)
      (scalarProjection n2 localPiece) (Real.toNNReal rho)

  have h_final :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
          (scalarProjection n1 localPiece)) : ENNReal) ≤
      (2 * Nat.ceil ((2 * K * rho) / rho) + 2 : ENNReal) *
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
          (scalarProjection n2 localPiece)) : ENNReal) := by
    have h1 : (↑(Metric.externalCoveringNumber (Real.toNNReal rho) C1) : ENNReal) =
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
          (scalarProjection n1 localPiece)) : ENNReal) := by
      exact_mod_cast h_cover1
    have h2 : (↑(Metric.externalCoveringNumber (Real.toNNReal rho) C2) : ENNReal) =
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
          (scalarProjection n2 localPiece)) : ENNReal) := by
      exact_mod_cast h_cover2
    rw [h1, h2] at h_centered_bound
    exact h_centered_bound
  exact ⟨h_containment, by simpa [n1, n2] using h_final⟩

end Kakeya.Assouad
