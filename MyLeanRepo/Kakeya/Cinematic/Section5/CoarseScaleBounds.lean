import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedCoarseSetupInputs

/-!
# Helper lemmas for coarse scale bounds

Extracts `DeltaRep ≤ C_R * tRep` from the coarse rectangle geometry.
-/

namespace Kakeya.Cinematic

/-- Any parameter interval has length at most 1. -/
lemma ParameterInterval.length_le_one (I : ParameterInterval) : I.length ≤ 1 := by
  have h1 : 0 ≤ I.left := I.left_mem.1
  have h2 : I.right ≤ 1 := I.right_mem.2
  have h3 : I.length = I.right - I.left := by rfl
  rw [h3]
  linarith

/-- The coarse rectangle first parameter `DeltaRep` is at most its second
parameter `C_R * tRep`, because every coarse rectangle interval fits in `[0,1]`. -/
lemma coarse_DeltaRep_le_C_R_tRep
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    {data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀}
    {center : C2Function}
    {hE : MeasurableSet E}
    {C_R C_count C_shading C_volume : ℝ}
    {setup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume}
    (coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE setup)
    (h_C_R_tRep_pos : 0 < C_R * tRep) :
    DeltaRep ≤ C_R * tRep := by
  have h_nonempty : coarseSetup.coarseData.coarse.Nonempty :=
    coarseSetup.coarseData.coarse_nonempty
  rcases Fin.pos_iff_nonempty.mp h_nonempty with ⟨j⟩
  let R := coarseSetup.coarseData.coarse.rectangle j
  have h1 : R.interval.length ≤ 1 := R.interval.length_le_one
  have h2 : R.interval.length = Real.sqrt (DeltaRep / (C_R * tRep)) :=
    R.interval_length
  rw [h2] at h1
  by_cases hDelta : DeltaRep ≤ 0
  · linarith
  · have hDelta_pos : 0 < DeltaRep := by linarith
    have hratio_pos : 0 < DeltaRep / (C_R * tRep) := by positivity
    have hsqrt_nonneg : 0 ≤ Real.sqrt (DeltaRep / (C_R * tRep)) :=
      Real.sqrt_nonneg _
    have hsqrt_le_one : Real.sqrt (DeltaRep / (C_R * tRep)) ≤ 1 := h1
    have hsq_le_one : (Real.sqrt (DeltaRep / (C_R * tRep))) ^ 2 ≤ 1 := by
      have h : (Real.sqrt (DeltaRep / (C_R * tRep))) ^ 2 ≤ 1 ^ 2 := by
        gcongr
      simpa using h
    have hsq : (Real.sqrt (DeltaRep / (C_R * tRep))) ^ 2 =
        DeltaRep / (C_R * tRep) :=
      Real.sq_sqrt (by positivity)
    rw [hsq] at hsq_le_one
    have h6 : DeltaRep / (C_R * tRep) ≤ 1 := hsq_le_one
    have h7 : DeltaRep ≤ C_R * tRep := by
      calc
        DeltaRep = (DeltaRep / (C_R * tRep)) * (C_R * tRep) := by
          rw [div_mul_cancel₀ DeltaRep h_C_R_tRep_pos.ne']
        _ ≤ 1 * (C_R * tRep) := by gcongr
        _ = C_R * tRep := by ring
    exact h7

end Kakeya.Cinematic
