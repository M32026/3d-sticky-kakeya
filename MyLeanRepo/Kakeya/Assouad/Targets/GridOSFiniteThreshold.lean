import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSFiniteStepScheduleStatements

/-! WZ2 Section 7: choose one common positive threshold from finitely many. -/

namespace Kakeya.Assouad

theorem grid_os_finite_threshold :
    GridOSFiniteThresholdStatement := by
  intro steps threshold hpos
  let s : Finset ℝ := Finset.image threshold Finset.univ
  have h_nonempty : s.Nonempty := by
    refine ⟨threshold 0, ?_⟩
    exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩
  let common : ℝ := Finset.min' s h_nonempty
  have h_common_in : common ∈ s := Finset.min'_mem s h_nonempty
  have h_common_pos : 0 < common := by
    rcases Finset.mem_image.mp h_common_in with ⟨i, _, h_eq⟩
    have h : 0 < threshold i := hpos i
    rwa [h_eq] at h
  have h_common_le : ∀ index, common ≤ threshold index := by
    intro index
    have h : threshold index ∈ s := by
      exact Finset.mem_image.mpr ⟨index, by simp, rfl⟩
    exact Finset.min'_le s (threshold index) h
  exact ⟨common, h_common_pos, h_common_le⟩

end Kakeya.Assouad
