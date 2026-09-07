import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridAtomizationHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.Section7ProjectionRectangleGridCoverStatement

/-!
# Finite terminal-grid cover of the Section 7 projection rectangle

Every point in the normalized projection rectangle is contained in the grid
atom represented by the center with the same floor index.
-/

namespace Kakeya.Assouad

private lemma floor_in_Icc {x : ℝ} {n N : ℕ} {C : ℝ}
    (hn : 0 < n) (hC : |x| ≤ C) (hN : C * (n : ℝ) ≤ (N : ℝ)) :
    ⌊x * (n : ℝ)⌋ ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  have h1 : -C ≤ x := by linarith [abs_le.mp hC]
  have h2 : x ≤ C := by linarith [abs_le.mp hC]
  have h3 : x * (n : ℝ) ≤ C * (n : ℝ) := by gcongr
  have h4 : -C * (n : ℝ) ≤ x * (n : ℝ) := by gcongr
  have h_upper : ⌊x * (n : ℝ)⌋ ≤ (N : ℤ) := by
    have h5 : (⌊x * (n : ℝ)⌋ : ℝ) ≤ x * (n : ℝ) := Int.floor_le _
    have h6 : (⌊x * (n : ℝ)⌋ : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast h6
  have hN2 : -(N : ℝ) ≤ -C * (n : ℝ) := by linarith
  let k : ℤ := -(N : ℤ)
  have h5 : (k : ℝ) ≤ x * (n : ℝ) := by
    simpa [k] using hN2.trans h4
  have h_lower : k ≤ ⌊x * (n : ℝ)⌋ := Int.le_floor.mpr h5
  have h10 : (-(N : ℤ)) ≤ ⌊x * (n : ℝ)⌋ := by
    simpa [k] using h_lower
  exact Finset.mem_Icc.mpr ⟨h10, h_upper⟩

theorem section7_projection_rectangle_grid_cover :
    Section7ProjectionRectangleGridCoverStatement := by
  intro base levels hbase band hband q hq
  have hrect : q ∈ section7ProjectionRectangle := hband hq
  have h1 : |q 0| ≤ 51 := hrect.1
  have h2 : |q 1| ≤ 1 := hrect.2
  set idx : ℤ × ℤ := planarGridIndex base levels q with hidx_def
  set N : ℕ := section7GridIndexBound base levels with hN_def
  set n : ℕ := base ^ levels with hn_def
  have hN_pos : 0 < n := by positivity
  have hN1' : (51 : ℝ) * (n : ℝ) ≤ (N : ℝ) := by
    simp only [hN_def, section7GridIndexBound, hn_def]
    norm_cast
    linarith
  have hN2' : (1 : ℝ) * (n : ℝ) ≤ (N : ℝ) := by
    simp only [hN_def, section7GridIndexBound, hn_def]
    norm_cast
    linarith
  have h_idx1 : idx.1 ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    have h_eq : idx.1 = ⌊q 0 * (n : ℝ)⌋ := by
      simp [idx, planarGridIndex, hn_def, Nat.cast_pow]
    rw [h_eq]
    exact floor_in_Icc hN_pos h1 hN1'
  have h_idx2 : idx.2 ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    have h_eq : idx.2 = ⌊q 1 * (n : ℝ)⌋ := by
      simp [idx, planarGridIndex, hn_def, Nat.cast_pow]
    rw [h_eq]
    exact floor_in_Icc hN_pos h2 hN2'
  have h_idx_in : idx ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).product
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
    exact Finset.mem_product.mpr ⟨h_idx1, h_idx2⟩
  set center : Point2 := planarGridCenter base levels idx with hcenter_def
  have h_center_in : center ∈ boundedPlanarGridCenters base levels N := by
    rw [boundedPlanarGridCenters]
    exact Finset.mem_image.mpr ⟨idx, h_idx_in, rfl⟩
  have h_index_eq :
      planarGridIndex base levels q =
        planarGridIndex base levels center := by
    have h : planarGridIndex base levels center = idx :=
      planarGridIndex_center_eq base levels idx hbase
    exact h.symm
  have h_q_in_atom :
      q ∈ projectedFiberGridAtom band base levels center := by
    simp only [projectedFiberGridAtom, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    exact ⟨hq, h_index_eq⟩
  simp only [finiteAtomUnion, Set.mem_iUnion]
  exact ⟨center, h_center_in, h_q_in_atom⟩

end Kakeya.Assouad
