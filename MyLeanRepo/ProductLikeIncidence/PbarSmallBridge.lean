module

/-
# Pbar Small Upper Bound Bridge

Derives `hPbar_small : Nplane δ Pbar_param < δ^{-(2s+η)}` from the Phase0 construction.

## Key insight

Since `Pbar_param = ⋃₀ Tbar` and `Tbar` is a family of dyadic δ-cubes:
- Every δ-cube meeting `⋃₀ Tbar` must equal one of the Tbar cubes
  (dyadic cubes at the same scale are disjoint or equal)
- Therefore `Nplane δ (⋃₀ Tbar) = Tbar.encard`

Since `Tbar ⊆ T ⊆ dyadicCubesMeeting δ (⋃ Pz z)`:
- `Tbar.encard ≤ dyadicCoveringNumber δ (⋃ Pz z)`
- `hP_small` gives `dyadicCoveringNumber δ (⋃ Pz z) < δ^{-(2s+η)}`
- Therefore `Nplane δ Pbar_param < δ^{-(2s+η)}`

## Lemmas

1. `covering_le_cube_family`: `Nplane δ (⋃₀ Tbar) ≤ Tbar.encard`
2. `cube_family_covering_eq`: `Nplane δ (⋃₀ Tbar) = Tbar.encard`
3. `pbar_small_bridge`: derives `hPbar_small` from `hP_small` + subset relations

## Dependencies
- `MyLeanRepo.CoreDefinitions`
- `MyLeanRepo.ProductLikeBasic`
- `MyLeanRepo.ProjectionBasic`
- `MyLeanRepo.ProductLikeIncidence.Phase0.ProjectionBoundComplete`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.Phase0.ProjectionBoundComplete
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set ENNReal Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- Two dyadic δ-cubes that share a point are equal. -/
lemma dyadic_cubes_share_point_eq
    {δ : ℝ} (hδ_pos : 0 < δ)
    {kQ kT : Fin 2 → ℤ}
    {p : EuclideanSpace ℝ (Fin 2)}
    (hpQ : p ∈ dyadicCube δ kQ)
    (hpT : p ∈ dyadicCube δ kT) :
    dyadicCube δ kQ = dyadicCube δ kT := by
  have h_kQ_eq_kT : kQ = kT := by
    ext i
    have h1 : p i ∈ Set.Ico (δ * (kQ i : ℝ)) (δ * ((kQ i : ℝ) + 1)) := hpQ i
    have h2 : p i ∈ Set.Ico (δ * (kT i : ℝ)) (δ * ((kT i : ℝ) + 1)) := hpT i
    have h3 : (kQ i : ℝ) = (kT i : ℝ) := by
      simp only [Set.mem_Ico] at h1 h2
      by_cases h : (kQ i : ℝ) < (kT i : ℝ)
      · -- kQ < kT, so kQ + 1 ≤ kT
        have h4 : (kQ i : ℝ) + 1 ≤ (kT i : ℝ) := by exact_mod_cast Int.add_one_le_of_lt (by exact_mod_cast h)
        have h5 : p i < δ * (kT i : ℝ) := by
          calc p i < δ * ((kQ i : ℝ) + 1) := h1.2
               _ ≤ δ * (kT i : ℝ) := by gcongr
        linarith
      · by_cases h' : (kT i : ℝ) < (kQ i : ℝ)
        · -- kT < kQ, so kT + 1 ≤ kQ
          have h4 : (kT i : ℝ) + 1 ≤ (kQ i : ℝ) := by exact_mod_cast Int.add_one_le_of_lt (by exact_mod_cast h')
          have h5 : p i < δ * (kQ i : ℝ) := by
            calc p i < δ * ((kT i : ℝ) + 1) := h2.2
                 _ ≤ δ * (kQ i : ℝ) := by gcongr
          linarith
        · have h'' : (kQ i : ℝ) = (kT i : ℝ) := by linarith
          exact h''
    exact_mod_cast h3
  rw [h_kQ_eq_kT]

/-- **Reverse direction of cube_family_le_covering**: if `Tbar` is a family of
dyadic δ-cubes, then any δ-cube meeting `⋃₀ Tbar` must be one of the Tbar cubes.
Hence `Nplane δ (⋃₀ Tbar) ≤ Tbar.encard`. -/
lemma covering_le_cube_family
    {δ : ℝ} (hδ_pos : 0 < δ)
    {Tbar : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hTbar_sub : Tbar ⊆ dyadicCubes 2 δ)
    (hTbar_finite : Tbar.Finite) :
    ENat.toENNReal (dyadicCoveringNumber δ (⋃₀ Tbar)) ≤
      ENat.toENNReal Tbar.encard := by
  have h1 : dyadicCubesMeeting δ (⋃₀ Tbar) ⊆ Tbar := by
    intro Q hQ
    have hQ_cube : Q ∈ dyadicCubes 2 δ := hQ.1
    have hQ_meet : (Q ∩ ⋃₀ Tbar).Nonempty := hQ.2
    rcases hQ_meet with ⟨p, hpQ, hp_union⟩
    rcases hp_union with ⟨T, hT_in_Tbar, hpT⟩
    have hT_cube : T ∈ dyadicCubes 2 δ := hTbar_sub hT_in_Tbar
    rcases hQ_cube with ⟨kQ, hQ_eq⟩
    rcases hT_cube with ⟨kT, hT_eq⟩
    have hpQ' : p ∈ dyadicCube δ kQ := by
      rw [← hQ_eq]; exact hpQ
    have hpT' : p ∈ dyadicCube δ kT := by
      rw [← hT_eq]; exact hpT
    have h_cubes_eq : dyadicCube δ kQ = dyadicCube δ kT :=
      dyadic_cubes_share_point_eq hδ_pos hpQ' hpT'
    have hQ_eq_T : Q = T := by
      calc Q = dyadicCube δ kQ := hQ_eq
           _ = dyadicCube δ kT := h_cubes_eq
           _ = T := hT_eq.symm
    exact hQ_eq_T ▸ hT_in_Tbar
  have h2 : (dyadicCubesMeeting δ (⋃₀ Tbar)).Finite := by
    exact Set.Finite.subset hTbar_finite h1
  have h3 : ENat.toENNReal (dyadicCoveringNumber δ (⋃₀ Tbar)) ≤
      ENat.toENNReal Tbar.encard := by
    have h4 : (dyadicCoveringNumber δ (⋃₀ Tbar)) = (dyadicCubesMeeting δ (⋃₀ Tbar)).encard := by
      rfl
    rw [h4]
    exact_mod_cast Set.encard_mono h1
  exact h3

/-- **Equality**: for a family Tbar of dyadic δ-cubes,
`Nplane δ (⋃₀ Tbar) = Tbar.encard`. -/
lemma cube_family_covering_eq
    {δ : ℝ} (hδ_pos : 0 < δ)
    {Tbar : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hTbar_sub : Tbar ⊆ dyadicCubes 2 δ)
    (hTbar_finite : Tbar.Finite) :
    ENat.toENNReal (dyadicCoveringNumber δ (⋃₀ Tbar)) =
      ENat.toENNReal Tbar.encard := by
  have h_le1 : ENat.toENNReal Tbar.encard ≤
      ENat.toENNReal (dyadicCoveringNumber δ (⋃₀ Tbar)) :=
    cube_family_le_covering hδ_pos hTbar_sub hTbar_finite
  have h_le2 : ENat.toENNReal (dyadicCoveringNumber δ (⋃₀ Tbar)) ≤
      ENat.toENNReal Tbar.encard :=
    covering_le_cube_family hδ_pos hTbar_sub hTbar_finite
  exact le_antisymm h_le2 h_le1

/-- **Pbar small upper bound bridge**: derives `Nplane δ Pbar_param < δ^{-(2s+η)}`
from the Phase0 union covering bound.

Given:
- `Pbar_param = ⋃₀ Tbar`
- `Tbar ⊆ dyadicCubes 2 δ`
- `Tbar.Finite`
- `Tbar ⊆ dyadicCubesMeeting δ A` (Tbar cubes meet the union A)
- `hP_small : Nplane δ A < δ^{-(2s+η)}`

Conclude:
- `Nplane δ Pbar_param < δ^{-(2s+η)}` -/
lemma pbar_small_bridge
    {δ s η : ℝ}
    (hδ_pos : 0 < δ)
    {Pbar_param : Set (EuclideanSpace ℝ (Fin 2))}
    {Tbar : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hPbar_eq_sUnion : Pbar_param = ⋃₀ Tbar)
    (hTbar_sub_cubes : Tbar ⊆ dyadicCubes 2 δ)
    (hTbar_finite : Tbar.Finite)
    (hTbar_sub_meeting : Tbar ⊆ dyadicCubesMeeting δ A)
    (hP_small : ENat.toENNReal (dyadicCoveringNumber δ A) <
        ENNReal.ofReal (δ ^ (-(2 * s + η)))) :
    ENat.toENNReal (dyadicCoveringNumber δ Pbar_param) <
      ENNReal.ofReal (δ ^ (-(2 * s + η))) := by
  have h_eq : ENat.toENNReal (dyadicCoveringNumber δ Pbar_param) =
      ENat.toENNReal Tbar.encard := by
    rw [hPbar_eq_sUnion]
    exact cube_family_covering_eq hδ_pos hTbar_sub_cubes hTbar_finite
  have h_le : ENat.toENNReal Tbar.encard ≤
      ENat.toENNReal (dyadicCoveringNumber δ A) := by
    have h3 : Tbar ⊆ dyadicCubesMeeting δ A := hTbar_sub_meeting
    have h4 : ENat.toENNReal Tbar.encard ≤
        ENat.toENNReal (dyadicCubesMeeting δ A).encard := by
      exact_mod_cast Set.encard_mono h3
    have h5 : (dyadicCoveringNumber δ A) = (dyadicCubesMeeting δ A).encard := by rfl
    rw [h5] at *
    exact h4
  rw [h_eq]
  exact lt_of_le_of_lt h_le hP_small

end ProductLikeIncidence.ProductReduction
