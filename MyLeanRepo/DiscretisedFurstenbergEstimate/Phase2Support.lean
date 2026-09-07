module

/-
  Phase2Support.lean

  Supporting bridge lemmas for Phase2Assembly.

  Provides:
  1. energy_total_to_pair_energy: convert per_tube_energy_general sum to
     pairEnergy sum over fibers
  2. incidence_double_count: double counting identity for fibers
  3. heavy_square_selection: extract heavy squares from separated point set
  4. common_tube_bound: intersection bound for tube families (skeleton)

  Whiteprint node: Phase2 / Phase2Support
  Dependencies: HeavySquaresBridge, CommonTubeEnergyExtraction
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquareRefinement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.Phase2

open DirecretisedFurstenbergEstimate.Lagoon

local notation "Plane" => EuclideanPlane

def squareIndex (Δ : ℝ) (p : Plane) : ℤ × ℤ :=
  (⌊p 0 / Δ⌋, ⌊p 1 / Δ⌋)

/-- A point belongs to the square indexed by `squareIndex Δ p`. -/
lemma point_in_own_square {Δ : ℝ} (hΔ_pos : 0 < Δ) (p : Plane) :
    p ∈ squareSet Δ (squareIndex Δ p) := by
  have h1 : Δ * (⌊p 0 / Δ⌋ : ℝ) ≤ p 0 := by
    have h : (⌊p 0 / Δ⌋ : ℝ) ≤ p 0 / Δ := Int.floor_le (p 0 / Δ)
    have h' : Δ * (⌊p 0 / Δ⌋ : ℝ) ≤ Δ * (p 0 / Δ) := by gcongr
    have h'' : Δ * (p 0 / Δ) = p 0 := by
      field_simp [hΔ_pos.ne'] <;> ring
    linarith
  have h2 : p 0 < Δ * ((⌊p 0 / Δ⌋ : ℝ) + 1) := by
    have h : p 0 / Δ < (⌊p 0 / Δ⌋ : ℝ) + 1 := Int.lt_floor_add_one (p 0 / Δ)
    have h' : Δ * (p 0 / Δ) < Δ * ((⌊p 0 / Δ⌋ : ℝ) + 1) := by gcongr
    have h'' : Δ * (p 0 / Δ) = p 0 := by
      field_simp [hΔ_pos.ne'] <;> ring
    linarith
  have h3 : Δ * (⌊p 1 / Δ⌋ : ℝ) ≤ p 1 := by
    have h : (⌊p 1 / Δ⌋ : ℝ) ≤ p 1 / Δ := Int.floor_le (p 1 / Δ)
    have h' : Δ * (⌊p 1 / Δ⌋ : ℝ) ≤ Δ * (p 1 / Δ) := by gcongr
    have h'' : Δ * (p 1 / Δ) = p 1 := by
      field_simp [hΔ_pos.ne'] <;> ring
    linarith
  have h4 : p 1 < Δ * ((⌊p 1 / Δ⌋ : ℝ) + 1) := by
    have h : p 1 / Δ < (⌊p 1 / Δ⌋ : ℝ) + 1 := Int.lt_floor_add_one (p 1 / Δ)
    have h' : Δ * (p 1 / Δ) < Δ * ((⌊p 1 / Δ⌋ : ℝ) + 1) := by gcongr
    have h'' : Δ * (p 1 / Δ) = p 1 := by
      field_simp [hΔ_pos.ne'] <;> ring
    linarith
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

/-- If p ∈ squareSet Δ Q, then squareIndex Δ p = Q. -/
lemma squareIndex_unique {Δ : ℝ} (hΔ_pos : 0 < Δ) (p : Plane) (Q : ℤ × ℤ)
    (hp : p ∈ squareSet Δ Q) : squareIndex Δ p = Q := by
  have hx1 : Δ * (Q.1 : ℝ) ≤ p 0 := hp.1.1
  have hx2 : p 0 < Δ * ((Q.1 : ℝ) + 1) := hp.1.2
  have hq1 : (Q.1 : ℝ) ≤ p 0 / Δ := by
    have h : Δ * (Q.1 : ℝ) ≤ p 0 := hx1
    have h' : (Q.1 : ℝ) ≤ p 0 / Δ := by
      calc (Q.1 : ℝ)
        = (Δ * (Q.1 : ℝ)) / Δ := by field_simp [hΔ_pos.ne'] <;> ring
      _ ≤ p 0 / Δ := by gcongr
    exact h'
  have hq2 : p 0 / Δ < (Q.1 : ℝ) + 1 := by
    have h : p 0 < Δ * ((Q.1 : ℝ) + 1) := hx2
    have h' : p 0 / Δ < (Δ * ((Q.1 : ℝ) + 1)) / Δ := by gcongr
    have h'' : (Δ * ((Q.1 : ℝ) + 1)) / Δ = (Q.1 : ℝ) + 1 := by
      field_simp [hΔ_pos.ne'] <;> ring
    rw [h''] at h'
    exact h'
  have hfloor1 : ⌊p 0 / Δ⌋ = Q.1 := by
    rw [Int.floor_eq_iff]
    exact ⟨hq1, hq2⟩
  have hy1 : Δ * (Q.2 : ℝ) ≤ p 1 := hp.2.1
  have hy2 : p 1 < Δ * ((Q.2 : ℝ) + 1) := hp.2.2
  have hq3 : (Q.2 : ℝ) ≤ p 1 / Δ := by
    have h : Δ * (Q.2 : ℝ) ≤ p 1 := hy1
    have h' : (Q.2 : ℝ) ≤ p 1 / Δ := by
      calc (Q.2 : ℝ)
        = (Δ * (Q.2 : ℝ)) / Δ := by field_simp [hΔ_pos.ne'] <;> ring
      _ ≤ p 1 / Δ := by gcongr
    exact h'
  have hq4 : p 1 / Δ < (Q.2 : ℝ) + 1 := by
    have h : p 1 < Δ * ((Q.2 : ℝ) + 1) := hy2
    have h' : p 1 / Δ < (Δ * ((Q.2 : ℝ) + 1)) / Δ := by gcongr
    have h'' : (Δ * ((Q.2 : ℝ) + 1)) / Δ = (Q.2 : ℝ) + 1 := by
      field_simp [hΔ_pos.ne'] <;> ring
    rw [h''] at h'
    exact h'
  have hfloor2 : ⌊p 1 / Δ⌋ = Q.2 := by
    rw [Int.floor_eq_iff]
    exact ⟨hq3, hq4⟩
  ext <;> simp [squareIndex, hfloor1, hfloor2] <;> tauto

end DirecretisedFurstenbergEstimate.Phase2
