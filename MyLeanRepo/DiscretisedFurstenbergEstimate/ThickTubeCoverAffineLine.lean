module

/-
  Thick tube cover for AffineLine (OS Proposition 2).

  Genuine proof using affineLine_packing_bound from PackingBound.lean.
  Reuses pigeonhole lemmas from ThickTubeCover.lean.

  Given tube families T(p) that are (δ,s,C₁)-sets of AffineLines with
  uniform cardinality ~M, find a refinement P' ⊆ P and a Δ-separated
  cover C' that is itself a (Δ,s,C₂)-set with uniform incidence lower bound.
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-! ARCHIVED: MATHEMATICALLY INVALID FOR THE TARGET PROOF. DO NOT IMPORT.

Fundamentally depends on ThickTubeCover (pigeonhole lemmas).
The main thick_tube_cover_euclidean theorem uses singleton witnesses.
See .scratch/operator/TEAM_CORRECTION_AND_PROOF_ROUTE.md. -/


noncomputable section

open scoped ENNReal NNReal
open DirecretisedFurstenbergEstimate

namespace DirecretisedFurstenbergEstimate

variable {α : Type*} [DecidableEq α]

abbrev K_pack : ℕ := MainAppendix.affineLine_packing_constant

-- ============================================================================
-- General separation predicate
-- ============================================================================

/-- A set is ε-separated if distinct points are at distance ≥ ε. -/
def Separated' (ε : ℝ) {X : Type*} [PseudoMetricSpace X] (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε ≤ dist x y

-- ============================================================================
-- K_pack positivity
-- ============================================================================

lemma K_pack_pos : 0 < K_pack := by
  have h_affine_nonempty : Nonempty AffineLine := by
    let p : EuclideanPlane := 0
    let v : EuclideanPlane := EuclideanSpace.single 0 1
    let ℓ : AffineSubspace ℝ EuclideanPlane := AffineSubspace.mk' p (ℝ ∙ v)
    have hv_ne_zero : v ≠ 0 := by
      intro h
      have h4 : v 0 = 0 := by rw [h] <;> simp
      have h5 : v 0 = 1 := by
        simp [v]
        <;> norm_num
      rw [h5] at h4 <;> norm_num at h4
    have h_finrank : Module.finrank ℝ ℓ.direction = 1 := by
      have h1 : ℓ.direction = ℝ ∙ v := by
        simp [ℓ]
      rw [h1]
      exact finrank_span_singleton hv_ne_zero
    exact ⟨⟨ℓ, h_finrank⟩⟩
  let z : AffineLine := Classical.choice h_affine_nonempty
  let S : Set AffineLine := {z}
  have hS_sep : Set.Pairwise S (fun x y => (1 : ℝ) ≤ dist x y) := by
    intro x hx y hy hne
    have hx' : x = z := by simpa [S] using hx
    have hy' : y = z := by simpa [S] using hy
    rw [hx', hy'] at hne
    <;> tauto
  have hS_sub : S ⊆ Metric.closedBall z (2 * (1 : ℝ)) := by
    intro x hx
    have hx' : x = z := by simpa [S] using hx
    rw [hx']
    <;> simp [dist_self] <;> linarith
  by_contra h
  have h0 : K_pack = 0 := by omega
  have h_bound := MainAppendix.affineLine_packing_bound (1 : ℝ) (by norm_num) hS_sep z hS_sub
  have hK_eq : (K_pack : ENat) = 0 := by exact_mod_cast h0
  rw [hK_eq] at h_bound
  have h2 : S.encard ≤ (0 : ENat) := h_bound.2
  have h3 : S.encard = 1 := by
    simp [S, Set.encard_singleton]
  rw [h3] at h2
  <;> norm_num at h2

end DirecretisedFurstenbergEstimate

end
