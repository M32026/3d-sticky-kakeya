module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.ProcessIntervals
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.MainAssembly
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# ProcessIntervalsResult wrapper

Converts the core `process_intervals` induction to the `ProcessIntervalsResult`
interface required by `MainAssembly`.

This lives in a separate file because `MainAssembly` imports `ProcessIntervals`,
so `ProcessIntervals` cannot import `MainAssembly` back.

Whiteprint node: `process_intervals`
Depends on: `tube_null`, `extend_merge`
-/


noncomputable section

open CombinatorialKaufman.ProcessIntervals
open CombinatorialKaufman

namespace CombinatorialKaufman.ProcessIntervalsResult

/-- Wrapper converting `process_intervals` to the `ProcessIntervalsResult` interface. -/
lemma processIntervals_result : CombinatorialKaufman.MainAssembly.ProcessIntervalsResult := by
  intro f s t m δ ε' τ0 hs hst ht hδ_pos hδ_lt_one hm hτ0_pos hε'_pos
    h_cont hLip h_f0 h_lower L h_sort h_disj h_lin h_min h_bound h_gap
  have h_len : ∀ p ∈ L, p.1 < p.2 := fun p hp => (h_bound p hp).2.2
  have hL_in : ∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ m := fun p hp =>
    let h := h_bound p hp; ⟨h.1, h.2.1⟩
  have h_totalLen_le_m : totalLength L ≤ m :=
    intervalList_sum_length_le_zero (by linarith) h_len h_sort h_disj hL_in
  have hSD : SortedDisjoint L := sortedDisjoint_of_byLeft_disjoint h_sort h_disj h_len
  have hL_bound' : ∀ I ∈ L, 0 ≤ I.1 ∧ I.2 ≤ m := fun I hI =>
    let h := h_bound I hI; ⟨h.1, h.2.1⟩
  have h_main_result := process_intervals f s t δ ε' τ0 m hs hst ht hδ_pos hδ_lt_one
    hε'_pos hτ0_pos (by linarith) h_cont hLip h_f0 h_lower
    m (by linarith) L hSD h_lin hL_bound' h_min
  rcases h_main_result with ⟨J, hJ_SD, hJ_good, hJ_bound, hJ_min, hJ_len⟩
  have hJ_byLeft_disj := byLeft_disjoint_of_sortedDisjoint hJ_SD
  have hJ_sort' : SortedByLeft J := hJ_byLeft_disj.1
  have hJ_disj' : PairwiseInteriorDisjointList J := hJ_byLeft_disj.2
  have hJ_len' : ∀ p ∈ J, p.2 - p.1 ≥ δ * τ0 * m := hJ_min
  have hJ_bound' : ∀ p ∈ J, 0 ≤ p.1 ∧ p.2 ≤ m ∧ p.1 < p.2 := fun p hp =>
    ⟨(hJ_bound p hp).1, (hJ_bound p hp).2, hJ_SD.2 p hp⟩
  have hJ_good' : ∀ p ∈ J,
      (EpsilonLinear f (2*δ) p.1 p.2 ∧ s ≤ chordSlope f p.1 p.2) ∨
      (EpsilonSuperlinear f (2*δ) p.1 p.2 ∧ chordSlope f p.1 p.2 = s) := by
    intro p hp
    rcases hJ_good p hp with (h | h)
    · exact Or.inl ⟨h.1, h.2.1⟩
    · exact Or.inr h
  have h_ts_pos : 0 < t - s := by linarith
  have h_gap' : m - totalLength J ≤ (δ + δ^2 + ε'/(t-s)) * m := by
    have h1 : totalLength J ≥ (1 - δ) * totalLength L - ε' * m / (t - s) := hJ_len
    have h2 : m - totalLength J ≤ m - ((1 - δ) * totalLength L - ε' * m / (t - s)) := by
      gcongr
    have h3 : m - ((1 - δ) * totalLength L - ε' * m / (t - s)) =
        (m - totalLength L) + δ * totalLength L + ε' * m / (t - s) := by ring
    rw [h3] at h2
    have h4 : (m - totalLength L) + δ * totalLength L + ε' * m / (t - s) ≤
        (δ + δ^2 + ε'/(t-s)) * m := by
      have h5 : m - totalLength L ≤ δ^2 * m := h_gap
      have h6 : δ * totalLength L ≤ δ * m := by gcongr
      have h7 : ε' * m / (t - s) = (ε'/(t-s)) * m := by
        field_simp [h_ts_pos.ne'] <;> ring
      rw [h7]
      linarith
    linarith
  exact ⟨J, hJ_good', hJ_len', hJ_bound', hJ_sort', hJ_disj', h_gap'⟩

end CombinatorialKaufman.ProcessIntervalsResult

end
