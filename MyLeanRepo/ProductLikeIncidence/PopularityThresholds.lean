module

/-
# Popularity Threshold Proof

Correct proof that the Phase0 V3 popularity constant `c_phase0` is large enough
to support the threefold recursive selection with `c_sel = c_phase0 / 2`.

Key insight: use `C ≤ δ^(-eta_target)` (not just `C_work ≤ δ^(-eta_work)`).
Since `eta_target = eta_work/2`, we get:
  c_phase0 = δ^eta_target / (7 * C_work^2)
           ≥ δ^(3*eta_target) / (7 * 35^2)
           = δ^(1.5*eta_work) / constant

And since rho_sel ≈ 2.01*eta_work > 1.5*eta_work, for small δ:
  δ^rho_sel ≤ c_phase0 / 4   (selection retention condition)
  δ^rho_sel ≤ c_phase0 / 16  (Kaufman/neighborhood margin)
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV3
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

namespace ProductLikeIncidence.ProductReduction

/-- The Phase0 V3 popularity constant. -/
def cPhase0 (δ eta_target C_work : ℝ) : ℝ :=
  δ ^ eta_target / (7 * C_work ^ 2)

/-- Lower bound on c_phase0 from the target-scale absorption bound.

    Given `C ≤ δ^(-eta_target)` and `C_work = 35*C`, we have:
    `c_phase0 ≥ δ^(3*eta_target) / (7 * 35^2)`. -/
lemma cPhase0_lower_bound
    {δ eta_target C C_work : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hη_target_pos : 0 < eta_target)
    (hC_pos : 0 < C)
    (hC_le_target : C ≤ δ ^ (-eta_target))
    (hC_work_eq : C_work = 35 * C) :
    cPhase0 δ eta_target C_work ≥ δ ^ (3 * eta_target) / (7 * 35 ^ 2) := by
  have h1 : C_work ^ 2 = (35 : ℝ) ^ 2 * C ^ 2 := by
    rw [hC_work_eq]; ring
  have h2 : C ^ 2 ≤ (δ ^ (-eta_target)) ^ 2 := by
    have h21 : 0 ≤ C := by linarith
    gcongr
  have h3 : (δ ^ (-eta_target)) ^ 2 = δ ^ (-2 * eta_target) := by
    have h31 : (δ ^ (-eta_target)) ^ 2 = δ ^ (-eta_target) * δ ^ (-eta_target) := by ring
    rw [h31, ← Real.rpow_add hδ_pos] <;> ring_nf
  have hC_work_pos : 0 < C_work := by
    rw [hC_work_eq] <;> positivity
  have h4 : C_work ^ 2 ≤ (35 : ℝ) ^ 2 * δ ^ (-2 * eta_target) := by
    calc C_work ^ 2
      = (35 : ℝ) ^ 2 * C ^ 2 := h1
    _ ≤ (35 : ℝ) ^ 2 * (δ ^ (-eta_target)) ^ 2 := by gcongr
    _ = (35 : ℝ) ^ 2 * δ ^ (-2 * eta_target) := by rw [h3]
  have h5 : 0 < 7 * C_work ^ 2 := by positivity
  have h6 : δ ^ eta_target / (7 * C_work ^ 2) ≥
      δ ^ eta_target / (7 * ((35 : ℝ) ^ 2 * δ ^ (-2 * eta_target))) := by
    gcongr
    <;> positivity
  have h7 : δ ^ eta_target / (7 * ((35 : ℝ) ^ 2 * δ ^ (-2 * eta_target))) =
      δ ^ (3 * eta_target) / (7 * (35 : ℝ) ^ 2) := by
    have h8 : 0 < δ ^ (-2 * eta_target) := by positivity
    field_simp [h8.ne']
    <;> rw [← Real.rpow_add hδ_pos] <;> ring_nf
  rw [h7] at h6
  exact h6

/-- Sufficient small-δ condition for selection retention.

    If `δ^(rho_sel - 3*eta_target) ≤ 1/(4*7*35^2)`, then
    `δ^rho_sel ≤ c_phase0 / 4 = c_sel / 2`. -/
lemma selection_retention_condition
    {δ eta_target rho_sel C_work : ℝ}
    (hδ_pos : 0 < δ)
    (hη_target_pos : 0 < eta_target)
    (hC_work_pos : 0 < C_work)
    (h_exponent_pos : 0 < rho_sel - 3 * eta_target)
    (h_small : δ ^ (rho_sel - 3 * eta_target) ≤ 1 / (4 * 7 * 35 ^ 2))
    (h_lower : cPhase0 δ eta_target C_work ≥ δ ^ (3 * eta_target) / (7 * 35 ^ 2)) :
    δ ^ rho_sel ≤ cPhase0 δ eta_target C_work / 4 := by
  have h1 : δ ^ rho_sel = δ ^ (3 * eta_target) * δ ^ (rho_sel - 3 * eta_target) := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf
  rw [h1]
  have h2 : δ ^ (3 * eta_target) * δ ^ (rho_sel - 3 * eta_target) ≤
      δ ^ (3 * eta_target) * (1 / (4 * 7 * 35 ^ 2)) := by
    gcongr
    <;> positivity
  have h3 : δ ^ (3 * eta_target) * (1 / (4 * 7 * 35 ^ 2)) =
      (δ ^ (3 * eta_target) / (7 * 35 ^ 2)) / 4 := by ring
  rw [h3] at h2
  exact le_trans h2 (by linarith [h_lower])

/-- Sufficient small-δ condition for Kaufman/neighborhood mass margin.

    If `δ^(rho_sel - 3*eta_target) ≤ 1/(16*7*35^2)`, then
    `δ^rho_sel ≤ c_phase0 / 16 = c_sel / 8`. -/
lemma kaufman_mass_condition
    {δ eta_target rho_sel C_work : ℝ}
    (hδ_pos : 0 < δ)
    (hη_target_pos : 0 < eta_target)
    (hC_work_pos : 0 < C_work)
    (h_exponent_pos : 0 < rho_sel - 3 * eta_target)
    (h_small : δ ^ (rho_sel - 3 * eta_target) ≤ 1 / (16 * 7 * 35 ^ 2))
    (h_lower : cPhase0 δ eta_target C_work ≥ δ ^ (3 * eta_target) / (7 * 35 ^ 2)) :
    δ ^ rho_sel ≤ cPhase0 δ eta_target C_work / 16 := by
  have h1 : δ ^ rho_sel = δ ^ (3 * eta_target) * δ ^ (rho_sel - 3 * eta_target) := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf
  rw [h1]
  have h2 : δ ^ (3 * eta_target) * δ ^ (rho_sel - 3 * eta_target) ≤
      δ ^ (3 * eta_target) * (1 / (16 * 7 * 35 ^ 2)) := by
    gcongr
    <;> positivity
  have h3 : δ ^ (3 * eta_target) * (1 / (16 * 7 * 35 ^ 2)) =
      (δ ^ (3 * eta_target) / (7 * 35 ^ 2)) / 16 := by ring
  rw [h3] at h2
  exact le_trans h2 (by linarith [h_lower])

/-- The exponent gap is positive: `rho_sel > 3 * eta_target` when
    `eta_target = eta_work / 2` and `rho_sel = 2*eta_work + qAbsorb eta_work`. -/
lemma exponent_gap_positive
    {eta_work eta_target rho_sel : ℝ}
    (hη_work_pos : 0 < eta_work)
    (h_eta_target : eta_target = eta_work / 2)
    (h_rho_sel : rho_sel = 2 * eta_work + qAbsorb eta_work) :
    0 < rho_sel - 3 * eta_target := by
  rw [h_rho_sel, h_eta_target]
  simp only [qAbsorb]
  <;> linarith

/-- Combined popularity threshold: for sufficiently small δ, both the
    selection retention and Kaufman mass conditions hold.

    The outer δ₀ absorbs the constants `1/(4*7*35^2)` and `1/(16*7*35^2)`
    using the positive exponent gap `rho_sel - 3*eta_target`. -/
lemma popularity_threshold_combined
    {δ eta_work eta_target C C_work rho_sel : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hη_work_pos : 0 < eta_work)
    (h_eta_target : eta_target = eta_work / 2)
    (hC_pos : 0 < C)
    (hC_le_target : C ≤ δ ^ (-eta_target))
    (hC_work_eq : C_work = 35 * C)
    (h_rho_sel : rho_sel = 2 * eta_work + qAbsorb eta_work)
    (h_small_retention : δ ^ (rho_sel - 3 * eta_target) ≤ 1 / (4 * 7 * 35 ^ 2))
    (h_small_mass : δ ^ (rho_sel - 3 * eta_target) ≤ 1 / (16 * 7 * 35 ^ 2)) :
    let c_sel := cPhase0 δ eta_target C_work / 2
    δ ^ rho_sel ≤ c_sel / 2 ∧
    δ ^ rho_sel ≤ c_sel / 8 := by
  dsimp only
  have h_gap : 0 < rho_sel - 3 * eta_target :=
    exponent_gap_positive hη_work_pos h_eta_target h_rho_sel
  have hC_work_pos : 0 < C_work := by
    rw [hC_work_eq] <;> positivity
  have h_lower : cPhase0 δ eta_target C_work ≥ δ ^ (3 * eta_target) / (7 * 35 ^ 2) :=
    cPhase0_lower_bound hδ_pos hδ_lt_one (by linarith) hC_pos hC_le_target hC_work_eq
  have h_ret : δ ^ rho_sel ≤ cPhase0 δ eta_target C_work / 4 :=
    selection_retention_condition hδ_pos (by linarith) hC_work_pos h_gap h_small_retention h_lower
  have h_mass : δ ^ rho_sel ≤ cPhase0 δ eta_target C_work / 16 :=
    kaufman_mass_condition hδ_pos (by linarith) hC_work_pos h_gap h_small_mass h_lower
  have h_goal1 : δ ^ rho_sel ≤ (cPhase0 δ eta_target C_work / 2) / 2 := by
    have h_eq : (cPhase0 δ eta_target C_work / 2) / 2 = cPhase0 δ eta_target C_work / 4 := by ring
    rw [h_eq]; exact h_ret
  have h_goal2 : δ ^ rho_sel ≤ (cPhase0 δ eta_target C_work / 2) / 8 := by
    have h_eq : (cPhase0 δ eta_target C_work / 2) / 8 = cPhase0 δ eta_target C_work / 16 := by ring
    rw [h_eq]; exact h_mass
  exact ⟨h_goal1, h_goal2⟩

end ProductLikeIncidence.ProductReduction
