module

/-
  Contract B2: Theorem 6.1 → UniformIncidenceData adapter.

  Frozen facade signature. Converts the uniform regular incidence estimate
  into the exact-scale UniformIncidenceData package consumed by Prop73.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Contracts.Theorem61
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformIncidenceData
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CarrierTransfer
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.CarrierTransfer

theorem theorem6_1_uniform_data (s t : ℝ) (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2) :
    ∃ ε_inc : ℝ, ε_inc < 1 ∧ Nonempty (UniformIncidenceData s t ε_inc) := by
  rcases theorem6_1_main s t hs hs1 hst ht2 with ⟨εA, hεA_lt_one, h_main⟩
  have hεA_pos : 0 < εA := h_main.1
  rcases h_main.2.2 with ⟨δR_thin, hδR_thin_pos, hδR_thin_one, h_body⟩
  set ε_inc : ℝ := εA / 2 with hε_inc_def
  have hε_inc_pos : 0 < ε_inc := by linarith
  have hε_inc_lt : ε_inc < εA := by linarith
  have hε_inc_lt_one : ε_inc < 1 := by linarith
  set C_tube : ℝ := 381790 * (176 : ℝ) ^ s with hC_tube_def
  have hC_tube_pos : 0 < C_tube := by
    rw [hC_tube_def]
    have h1 : (0 : ℝ) < (176 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    positivity
  have hC_tube_ge : (361 : ℝ) ≤ C_tube := by
    rw [hC_tube_def]
    have h1 : (1 : ℝ) ≤ (176 : ℝ) ^ s := by
      have h2 : (0 : ℝ) ≤ s := by linarith
      have h3 : (176 : ℝ) ^ s ≥ (176 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
      simpa using h3
    nlinarith
  have hC_tube_eq : C_tube = 381790 * (176 : ℝ) ^ s := by
    rw [hC_tube_def] <;> rfl
  have hs' : 0 ≤ s := by linarith
  rcases uniform_wide_transfer_uniform_all_j
      (hεA_pos := hεA_pos) (hε_inc_pos := hε_inc_pos) (hε_inc_lt := hε_inc_lt)
      (hs := hs') (hs1 := hs1) (hC_tube_eq := hC_tube_eq)
      (hC_tube_pos := hC_tube_pos) (hC_tube_ge := hC_tube_ge)
      (δR_thin := δR_thin) (hδR_thin_pos := hδR_thin_pos) (h_body := h_body)
    with ⟨δR, hδR_pos, hδR_one, h_transfer⟩
  let data : UniformIncidenceData s t ε_inc :=
    { δR := δR
      hδR_pos := hδR_pos
      hδR_one := hδR_one
      h_body := h_transfer
      hε_inc_pos := hε_inc_pos }
  exact ⟨ε_inc, hε_inc_lt_one, ⟨data⟩⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
