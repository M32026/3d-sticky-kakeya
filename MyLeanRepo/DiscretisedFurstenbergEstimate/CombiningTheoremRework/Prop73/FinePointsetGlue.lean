module

/-
  FinePointsetGlue — Point-set identification lemma for fine config construction.

  Given a NiceConfiguration whose P₀ corresponds to an index finset S'',
  prove config.pointSet = setFromIndices (dyadicDelta n) S''.

  This is the key identification needed to connect the tail uniformisation
  consumer output (which works with setFromIndices) to the CombiningConfig
  (which works with config.pointSet).

  Whiteprint node: combining_theorem_rework / fine_pointset_glue
  Status: In progress.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.InductiveStepBridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BasicUniformization
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.BasicUniformization

variable {n : ℕ}

local instance : DecidableEq (DyadicSquare n) := Classical.decEq (DyadicSquare n)

/-- Helper: DyadicSquare.toSet equals dyadicSquare at the same scale. -/
lemma dyadicSquare_toSet_eq (p : DyadicSquare n) :
    (p.toSet : Set Plane) =
      CombiningTheorem.dyadicSquare (dyadicDelta n) p.i p.j := by
  ext x
  simp [DyadicSquare.toSet, CombiningTheorem.dyadicSquare, Set.mem_Ico]
  <;> aesop

/-- Point-set identification: if config.P₀ is the image of S'' under
    indicesToMainSquare, then config.pointSet equals setFromIndices.

    This connects the consumer's index-set output to the CombiningConfig's
    point set field. -/
lemma fine_pointset_from_indices
    {s C : ℝ} {M : ℕ}
    (config : CombiningTheorem.NiceConfiguration n s C M)
    (S'' : Finset (ℤ × ℤ))
    (hP0_eq : config.P₀ = S''.image (indicesToMainSquare (n := n))) :
    config.pointSet = setFromIndices (dyadicDelta n) S'' := by
  have h1 : ∀ (p : DyadicSquare n), (p.toSet : Set Plane) =
        CombiningTheorem.dyadicSquare (dyadicDelta n) p.i p.j :=
    dyadicSquare_toSet_eq
  ext x
  simp only [CombiningTheorem.NiceConfiguration.pointSet, Set.mem_iUnion,
    setFromIndices, Finset.mem_coe]
  constructor
  · rintro ⟨p, hp, hx⟩
    have h2 : p ∈ S''.image (indicesToMainSquare (n := n)) := by
      rw [hP0_eq] at hp <;> exact hp
    rcases Finset.mem_image.mp h2 with ⟨idx, hidx, rfl⟩
    refine ⟨idx, hidx, ?_⟩
    rw [h1 (indicesToMainSquare idx)] at hx
    exact hx
  · rintro ⟨idx, hidx, hx⟩
    let p : DyadicSquare n := indicesToMainSquare idx
    have hp : p ∈ config.P₀ := by
      rw [hP0_eq]
      exact Finset.mem_image.mpr ⟨idx, hidx, rfl⟩
    refine ⟨p, hp, ?_⟩
    rw [h1 p]
    exact hx

/-- Construct the index finset corresponding to a config's P₀. -/
def indicesFromConfig {s C : ℝ} {M : ℕ}
    (config : CombiningTheorem.NiceConfiguration n s C M) : Finset (ℤ × ℤ) :=
  config.P₀.image (fun p : DyadicSquare n => (p.i, p.j))

/-- The index finset from a config satisfies the unit-square bounds if the
    config's squares are within the unit square. -/
lemma indicesFromConfig_unit
    {s C : ℝ} {M : ℕ}
    (config : CombiningTheorem.NiceConfiguration n s C M)
    (h_unit : ∀ (p : DyadicSquare n), p ∈ config.P₀ →
      0 ≤ p.i ∧ 0 ≤ p.j ∧ p.i < (2 : ℤ)^n ∧ p.j < (2 : ℤ)^n) :
    ∀ idx ∈ indicesFromConfig config,
      0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^n ∧ idx.2 < (2 : ℤ)^n := by
  intro idx hidx
  have h : ∃ (p : DyadicSquare n), p ∈ config.P₀ ∧ (p.i, p.j) = idx := by
    simpa [indicesFromConfig, Finset.mem_image] using hidx
  rcases h with ⟨p, hp, h_eq⟩
  have h_i : p.i = idx.1 := by simp [Prod.ext_iff] at h_eq <;> tauto
  have h_j : p.j = idx.2 := by simp [Prod.ext_iff] at h_eq <;> tauto
  have h_result := h_unit p hp
  rw [h_i, h_j] at *
  <;> exact h_result

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
