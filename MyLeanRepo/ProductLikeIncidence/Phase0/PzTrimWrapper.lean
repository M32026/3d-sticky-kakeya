module

/-
# Pz_trim Wrapper

Packages `approximate_cube_trimming` with `delta_sc_set_intersection_with_cube_union`
to produce a size-controlled, regularity-preserving trimmed parameter set `Pz_trim`.

Given a (δ,s,C)-set Pz in an approximate-incidence strip, and a target size M with
C⁻¹·δ^{-s} ≤ M ≤ |Pz|_δ, produce Pz_trim ⊆ Pz such that:
- Pz_trim is a (δ,s,35·C)-set
- Pz_trim stays in the same approximate-incidence strip
- M/2 ≤ |Pz_trim|_δ ≤ 2M+1

## Whiteprint node
`pz_trim_wrapper`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProductLikeIncidence.ProductLikeProof
public import MyLeanRepo.ProductLikeIncidence.Phase0.CubeUnion
public import MyLeanRepo.ProductLikeIncidence.Phase0.ApproximateCubeTrimming
public import MyLeanRepo.ProductLikeIncidence.Phase0.PzTrimHelpers
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Bornology ENNReal Finset Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- **Pz_trim wrapper**: trim a (δ,s,C)-set Pz in an approximate-incidence strip
to controlled size while preserving (δ,s)-regularity with constant 35·C.

Given target size M satisfying C⁻¹·δ^{-s} ≤ M ≤ |Pz|_δ, produces Pz_trim ⊆ Pz with
M/2 ≤ |Pz_trim|_δ ≤ 2M+1 and IsDeltaSCSet δ s (35*C) Pz_trim. -/
lemma pz_trim_wrapper
    {δ s C M : ℝ}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales) (hδ_le_one : δ ≤ 1)
    (hs_pos : 0 < s) (hs_lt_one : s < 1) (hC_ge1 : 1 ≤ C)
    (hM_pos : 0 < M) (hM_lower : C⁻¹ * δ ^ (-s) ≤ M)
    {x y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    {Pz : Set (EuclideanSpace ℝ (Fin 2))}
    (hPz_delta : IsDeltaSCSet δ s C Pz)
    (hPz_strip : ∀ p ∈ Pz, |p 0 * y + p 1 - x| ≤ 2 * δ)
    (hM_le : ENNReal.ofReal M ≤ ENat.toENNReal (dyadicCoveringNumber δ Pz)) :
    ∃ (Pz_trim : Set (EuclideanSpace ℝ (Fin 2)))
      (A' : Finset (Set (EuclideanSpace ℝ (Fin 2)))),
      Pz_trim = Pz ∩ ⋃₀ (A' : Set _) ∧
      Pz_trim ⊆ Pz ∧
      IsDeltaSCSet δ s (35 * C) Pz_trim ∧
      (∀ p ∈ Pz_trim, |p 0 * y + p 1 - x| ≤ 2 * δ) ∧
      ENNReal.ofReal (M / 2) ≤ ENat.toENNReal (dyadicCoveringNumber δ Pz_trim) ∧
      ENat.toENNReal (dyadicCoveringNumber δ Pz_trim) ≤ ENNReal.ofReal (2 * M + 1) := by
  let A_set : Set (Set (EuclideanSpace ℝ (Fin 2))) := dyadicCubesMeeting δ Pz
  have hPz_bdd : Bornology.IsBounded Pz := hPz_delta.1
  have hA_set_finite : A_set.Finite :=
    ProductLikeIncidence.dyadicCubesMeeting_finite hδ hPz_bdd
  let A : Finset (Set (EuclideanSpace ℝ (Fin 2))) := hA_set_finite.toFinset
  have hA_coe : (A : Set _) = A_set := hA_set_finite.coe_toFinset

  have hA_cubes : ∀ Q ∈ A, Q ∈ dyadicCubes 2 δ := by
    intro Q hQ
    have hQ' : Q ∈ A_set := by
      rw [←hA_coe] <;> exact hQ
    exact hQ'.1

  have hA_meet : ∀ Q ∈ A, (Q ∩ Pz).Nonempty := by
    intro Q hQ
    have hQ' : Q ∈ A_set := by
      rw [←hA_coe] <;> exact hQ
    exact hQ'.2

  have hA_strip : ∀ Q ∈ A, ∃ p ∈ Q, |p 0 * y + p 1 - x| ≤ 2 * δ := by
    intro Q hQ
    have hQ_meet : (Q ∩ Pz).Nonempty := hA_meet Q hQ
    rcases hQ_meet with ⟨p, hpQ, hpPz⟩
    exact ⟨p, hpQ, hPz_strip p hpPz⟩

  let A_set' : Set (Set (EuclideanSpace ℝ (Fin 2))) := (A : Set _)
  have hA_set'_eq : A_set' = A_set := by
    exact hA_coe
  have h_union_eq : Set.sUnion A_set' = cubeUnion δ Pz := by
    rw [hA_set'_eq]
    rfl
  have hA_regular : IsDeltaSCSet δ s C (Set.sUnion A_set') := by
    rw [h_union_eq]
    exact cube_union_preserves_delta_set hδ hδ_dyadic hPz_delta

  have hA_card_eq : ENat.toENNReal (dyadicCoveringNumber δ Pz) =
      ENat.toENNReal A.card := by
    have h1 : dyadicCoveringNumber δ Pz = A_set.encard := by rfl
    rw [h1]
    have h2 : A_set.encard = ↑A.card := by
      rw [←hA_coe]
      exact encard_coe_eq_coe_finsetCard A
    rw [h2]

  have hM_le' : ENNReal.ofReal M ≤ ENat.toENNReal A.card := by
    rw [←hA_card_eq]
    exact hM_le

  rcases approximate_cube_trimming
      hδ hδ_dyadic hδ_le_one hs_pos hs_lt_one hC_ge1 hM_pos hM_lower
      (x := x) (y := y) hy0 hy1 (A := A)
      hA_cubes hA_meet hA_strip hA_regular hM_le'
    with ⟨A', hA'_sub, h_size_lower, h_size_upper, hA'_regular, hA'_meet⟩

  let A'_set : Set (Set (EuclideanSpace ℝ (Fin 2))) := (A' : Set _)
  let U' : Set (EuclideanSpace ℝ (Fin 2)) := Set.sUnion A'_set
  let Pz_trim : Set (EuclideanSpace ℝ (Fin 2)) := Pz ∩ U'

  have hPz_trim_sub : Pz_trim ⊆ Pz := by
    simp only [Pz_trim]
    exact Set.inter_subset_left

  have hA'_cubes : ∀ Q ∈ A', Q ∈ dyadicCubes 2 δ := by
    intro Q hQ
    have hQ_in_A : Q ∈ A := hA'_sub hQ
    exact hA_cubes Q hQ_in_A

  have hPz_trim_delta : IsDeltaSCSet δ s (35 * C) Pz_trim :=
    delta_sc_set_intersection_with_cube_union A' hA'_cubes hA'_meet hA'_regular

  have hPz_trim_strip : ∀ p ∈ Pz_trim, |p 0 * y + p 1 - x| ≤ 2 * δ := by
    intro p hp
    have hpPz : p ∈ Pz := hp.1
    exact hPz_strip p hpPz

  have h_cover_eq : dyadicCoveringNumber δ Pz_trim = ↑A'.card := by
    have h1 : dyadicCubesMeeting δ Pz_trim = (A' : Set _) :=
      cubes_meeting_P_intersection_eq hδ A' hA'_cubes hA'_meet
    dsimp only [dyadicCoveringNumber]
    rw [h1]
    exact encard_coe_eq_coe_finsetCard A'

  have h_size_lower' : ENNReal.ofReal (M / 2) ≤
      ENat.toENNReal (dyadicCoveringNumber δ Pz_trim) := by
    rw [h_cover_eq]
    exact h_size_lower

  have h_size_upper' : ENat.toENNReal (dyadicCoveringNumber δ Pz_trim) ≤
      ENNReal.ofReal (2 * M + 1) := by
    rw [h_cover_eq]
    exact h_size_upper

  exact ⟨Pz_trim, A', rfl, hPz_trim_sub, hPz_trim_delta, hPz_trim_strip,
    h_size_lower', h_size_upper'⟩

end ProductLikeIncidence.ProductReduction
