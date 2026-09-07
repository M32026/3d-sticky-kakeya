module

public import MyLeanRepo.InductionOnScales.UniformFibers
public import MyLeanRepo.InductionOnScales.Homothety
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# TQ_local Construction

Construct local fine tube collections TQ_local(Q) and cardinality estimates
using the UniformFibers infrastructure.

Given coarse tubes with uniform fiber sizes [NΔ, 2*NΔ):
- form80: |fineTubes| ≥ |coarseTubes| * NΔ
- form71: |TQ_local(Q)| ≤ |localFamily(Q)| * 2 * NΔ ≤ MΔ * 2 * NΔ

## Whiteprint node
Helper for CoarsePhase TQ_local step.
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales.CoarsePhase

/-- Construct TQ_local and cardinality estimates using uniform fibers.

Given:
- `fineTubes`: global set of fine tubes (e.g. config.tubes)
- `coarseTubes`: selected coarse tubes with uniform fiber sizes
- `NΔ`: lower fiber bound (each U ∈ coarseTubes has NΔ ≤ fiberSize < 2*NΔ)
- `localFamily Q`: per-Q coarse tube families, subsets of coarseTubes, size ≤ MΔ

Output:
- `TQ_local Q`: fine tubes contained in some U ∈ localFamily Q
- `form80`: |fineTubes| ≥ |coarseTubes| * NΔ
- `form71`: |TQ_local Q| ≤ MΔ * 2 * NΔ

Note: The factor of 2 in form71 comes from the dyadic band [NΔ, 2*NΔ).
This factor is absorbed into the global K in the main theorem. -/
lemma construct_TQ_local_uniform
    {n m : ℕ} (hnm : m ≤ n)
    {α : Type*} [DecidableEq α]
    (fineTubes : Finset (DyadicTube n))
    (coarseTubes : Finset (DyadicTube m))
    (NΔ : ℕ)
    (h_lower : ∀ U ∈ coarseTubes, NΔ ≤ fiberSize hnm fineTubes U)
    (h_upper : ∀ U ∈ coarseTubes, fiberSize hnm fineTubes U < 2 * NΔ)
    (MΔ : ℕ) (hMΔ : 0 < MΔ)
    (Qs : Finset α)
    (localFamily : α → Finset (DyadicTube m))
    (h_local_sub : ∀ x ∈ Qs, localFamily x ⊆ coarseTubes)
    (h_local_size : ∀ x ∈ Qs, (localFamily x).card ≤ MΔ) :
    ∃ (TQ_local : α → Finset (DyadicTube n)),
      (fineTubes.card : ℝ) ≥ (coarseTubes.card : ℝ) * (NΔ : ℝ) ∧
      (∀ x ∈ Qs, (TQ_local x).card ≤ (MΔ : ℝ) * (2 * NΔ : ℝ)) ∧
      (∀ x ∈ Qs, TQ_local x = (localFamily x).biUnion
        (fun U => fineTubes.filter (fun T => T.toSet ⊆ U.toSet))) := by
  let TQ_local : α → Finset (DyadicTube n) := fun x =>
    (localFamily x).biUnion (fun U => fineTubes.filter (fun T => T.toSet ⊆ U.toSet))
  have h_form80 : (fineTubes.card : ℝ) ≥ (coarseTubes.card : ℝ) * (NΔ : ℝ) :=
    form80_bound hnm fineTubes coarseTubes NΔ h_lower
  have h_form71 : ∀ x ∈ Qs, (TQ_local x).card ≤ (MΔ : ℝ) * (2 * NΔ : ℝ) := by
    intro x hx
    have h1 : (localFamily x).card ≤ MΔ := h_local_size x hx
    have h2 : ∀ U ∈ localFamily x, fiberSize hnm fineTubes U < 2 * NΔ := by
      intro U hU
      have h3 : U ∈ coarseTubes := h_local_sub x hx hU
      exact h_upper U h3
    have h_eq : TQ_local x = (localFamily x).biUnion
        (fun U => fineTubes.filter (fun T => T.toSet ⊆ U.toSet)) := by rfl
    rw [h_eq]
    have h5 := form71_bound hnm fineTubes (localFamily x) MΔ h1 NΔ h2
    have h6 : MΔ * 2 * NΔ = MΔ * (2 * NΔ) := by ring
    rw [h6] at h5
    exact_mod_cast h5
  have h_eq : ∀ x ∈ Qs, TQ_local x = (localFamily x).biUnion
      (fun U => fineTubes.filter (fun T => T.toSet ⊆ U.toSet)) := by
    intro x _
    rfl
  exact ⟨TQ_local, h_form80, h_form71, h_eq⟩

/-- Variant: absorb the factor of 2 into N_Δ by setting N_Δ = 2 * NΔ.

This gives |TQ_local| ≤ MΔ * N_Δ exactly, but the lower bound becomes
|fineTubes| ≥ |coarseTubes| * N_Δ / 2. Use this when the factor of 2
can be absorbed elsewhere (e.g. into K). -/
lemma construct_TQ_local_absorbed
    {n m : ℕ} (hnm : m ≤ n)
    {α : Type*} [DecidableEq α]
    (fineTubes : Finset (DyadicTube n))
    (coarseTubes : Finset (DyadicTube m))
    (NΔ : ℕ) (hNΔ_pos : 0 < NΔ)
    (h_lower : ∀ U ∈ coarseTubes, NΔ ≤ fiberSize hnm fineTubes U)
    (h_upper : ∀ U ∈ coarseTubes, fiberSize hnm fineTubes U < 2 * NΔ)
    (MΔ : ℕ) (hMΔ : 0 < MΔ)
    (Qs : Finset α)
    (localFamily : α → Finset (DyadicTube m))
    (h_local_sub : ∀ x ∈ Qs, localFamily x ⊆ coarseTubes)
    (h_local_size : ∀ x ∈ Qs, (localFamily x).card ≤ MΔ) :
    ∃ (N_Δ : ℝ) (hN_Δ : 0 ≤ N_Δ)
      (TQ_local : α → Finset (DyadicTube n)),
      (fineTubes.card : ℝ) ≥ (coarseTubes.card : ℝ) * N_Δ / 2 ∧
      (∀ x ∈ Qs, (TQ_local x).card ≤ (MΔ : ℝ) * N_Δ) := by
  let N_Δ : ℝ := 2 * (NΔ : ℝ)
  have hN_Δ_nonneg : 0 ≤ N_Δ := by positivity
  rcases construct_TQ_local_uniform hnm fineTubes coarseTubes NΔ h_lower h_upper
      MΔ hMΔ Qs localFamily h_local_sub h_local_size
    with ⟨TQ_local, h_form80, h_form71, _⟩
  have h_lower' : (fineTubes.card : ℝ) ≥ (coarseTubes.card : ℝ) * N_Δ / 2 := by
    have h1 : (fineTubes.card : ℝ) ≥ (coarseTubes.card : ℝ) * (NΔ : ℝ) := h_form80
    have h2 : (coarseTubes.card : ℝ) * N_Δ / 2 = (coarseTubes.card : ℝ) * (NΔ : ℝ) := by
      dsimp only [N_Δ] <;> ring
    rw [h2]
    exact h1
  have h_upper' : ∀ x ∈ Qs, (TQ_local x).card ≤ (MΔ : ℝ) * N_Δ := by
    intro x hx
    have h3 : (TQ_local x).card ≤ (MΔ : ℝ) * (2 * (NΔ : ℝ)) := h_form71 x hx
    have h4 : (MΔ : ℝ) * N_Δ = (MΔ : ℝ) * (2 * (NΔ : ℝ)) := by
      dsimp only [N_Δ] <;> ring
    rw [h4]
    exact h3
  exact ⟨N_Δ, hN_Δ_nonneg, TQ_local, h_lower', h_upper'⟩

end CoarsePhase

end InductionOnScales
