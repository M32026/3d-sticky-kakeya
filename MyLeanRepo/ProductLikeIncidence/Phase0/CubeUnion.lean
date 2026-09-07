module

/-
# Phase 0 Conversion — Point Sets to Tube Families

Converts (δ,s,C)-sets of parameter points to tube families whose
parameter sets are also (δ,s,C)-sets, by taking the union of dyadic
cubes meeting the point set.

## Key lemma
`cube_union_preserves_delta_set`: If S is a (δ,s,C)-set, then
U = ⋃₀(dyadicCubesMeeting δ S) is also a (δ,s,C)-set.

## Whiteprint node
`phase0_conversion`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Bornology Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- The union of all dyadic δ-cubes meeting a set S. -/
def cubeUnion {d : ℕ} (δ : ℝ) (S : Set (EuclideanSpace ℝ (Fin d))) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃₀ (dyadicCubesMeeting δ S)

/-- For dyadic scales δ ≤ r, r is an integer multiple of δ. -/
lemma dyadic_scale_multiple {δ r : ℝ}
    (hδ : δ ∈ dyadicScales) (hr : r ∈ dyadicScales) (hδ_le_r : δ ≤ r) :
    ∃ (N : ℕ), r = (N : ℝ) * δ := by
  rcases hδ with ⟨n, rfl⟩
  rcases hr with ⟨m, rfl⟩
  have hnm : m ≤ n := by
    by_contra h
    have h' : n < m := by omega
    have : (2 : ℝ) ^ (-(n : ℤ)) > (2 : ℝ) ^ (-(m : ℤ)) := by
      gcongr <;> norm_num
    linarith
  let N : ℕ := 2 ^ (n - m)
  have h_exp : ((n - m : ℕ) : ℤ) + (-(n : ℤ)) = (-(m : ℤ)) := by omega
  have h_final : (2 : ℝ) ^ ((n - m : ℕ) : ℤ) * (2 : ℝ) ^ (-(n : ℤ)) =
      (2 : ℝ) ^ (-(m : ℤ)) := by
    rw [← zpow_add₀ (by norm_num), h_exp]
  refine' ⟨N, _⟩
  have h_N : (N : ℝ) = (2 : ℝ) ^ ((n - m : ℕ) : ℤ) := by
    simp [N]
  rw [h_N]
  exact h_final.symm

/-- Every point lies in the dyadic cube with floor coordinates. -/
lemma point_in_cubeContaining {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ dyadicCube δ (fun i : Fin d => Int.floor (x i / δ)) := by
  intro i
  have h1 : (Int.floor (x i / δ) : ℝ) ≤ x i / δ := Int.floor_le (x i / δ)
  have h2 : x i / δ < (Int.floor (x i / δ) : ℝ) + 1 := Int.lt_floor_add_one (x i / δ)
  have h3 : δ * (Int.floor (x i / δ) : ℝ) ≤ x i := by
    calc δ * (Int.floor (x i / δ) : ℝ) ≤ δ * (x i / δ) := by gcongr
      _ = x i := by field_simp [hδ.ne'] <;> ring
  have h4 : x i < δ * ((Int.floor (x i / δ) : ℝ) + 1) := by
    calc x i = δ * (x i / δ) := by field_simp [hδ.ne'] <;> ring
      _ < δ * ((Int.floor (x i / δ) : ℝ) + 1) := by gcongr
  exact ⟨h3, h4⟩

/-- Distinct dyadic δ-cubes are disjoint. -/
lemma dyadic_cube_disjoint_or_equal {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {k1 k2 : Fin d → ℤ}
    (h : (dyadicCube δ k1 ∩ dyadicCube δ k2).Nonempty) : k1 = k2 := by
  rcases h with ⟨x, hx1, hx2⟩
  have h_i : ∀ i : Fin d, k1 i = k2 i := by
    intro i
    have h1 : x i ∈ Set.Ico (δ * (k1 i : ℝ)) (δ * ((k1 i : ℝ) + 1)) := hx1 i
    have h2 : x i ∈ Set.Ico (δ * (k2 i : ℝ)) (δ * ((k2 i : ℝ) + 1)) := hx2 i
    by_cases h : k1 i < k2 i
    · have h' : (k1 i : ℝ) + 1 ≤ (k2 i : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h
      have h4 : x i < δ * ((k1 i : ℝ) + 1) := h1.2
      have h5 : δ * (k2 i : ℝ) ≤ x i := h2.1
      have h6 : δ * ((k1 i : ℝ) + 1) ≤ δ * (k2 i : ℝ) := by gcongr
      linarith
    · by_cases h' : k2 i < k1 i
      · have h'' : (k2 i : ℝ) + 1 ≤ (k1 i : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h'
        have h4 : x i < δ * ((k2 i : ℝ) + 1) := h2.2
        have h5 : δ * (k1 i : ℝ) ≤ x i := h1.1
        have h6 : δ * ((k2 i : ℝ) + 1) ≤ δ * (k1 i : ℝ) := by gcongr
        linarith
      · have h_eq : k1 i = k2 i := by omega
        exact h_eq
  funext i
  exact h_i i

/-- A dyadic δ-cube intersecting an r-cube (r = N*δ, r > 0) is contained in it. -/
lemma dyadicCubeContainment {d : ℕ} {δ r : ℝ} {k : Fin d → ℤ} {j : Fin d → ℤ}
    (hδ : 0 < δ) (hr_pos : 0 < r) (hN : ∃ (N : ℕ), r = (N : ℝ) * δ)
    (h_inter : (dyadicCube δ k ∩ dyadicCube r j).Nonempty) :
    dyadicCube δ k ⊆ dyadicCube r j := by
  rcases hN with ⟨N, hN⟩
  rcases h_inter with ⟨p, hpδ, hpr⟩
  have hN_pos : 0 < N := by
    by_contra h
    have hN0 : N = 0 := by omega
    rw [hN0] at hN
    have : r = 0 := by simpa using hN
    linarith
  intro q hq
  intro i
  have hpr_i : p i ∈ Set.Ico (r * (j i : ℝ)) (r * ((j i : ℝ) + 1)) := hpr i
  have hpr1 : r * (j i : ℝ) ≤ p i := hpr_i.1
  have hpr2 : p i < r * ((j i : ℝ) + 1) := hpr_i.2
  have hp_div1 : (k i : ℝ) ≤ p i / δ := by
    have h1 : δ * (k i : ℝ) ≤ p i := (hpδ i).1
    calc (k i : ℝ) = (δ * (k i : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
      _ ≤ p i / δ := by gcongr
  have hp_div2 : p i / δ < (k i : ℝ) + 1 := by
    have h2 : p i < δ * ((k i : ℝ) + 1) := (hpδ i).2
    calc p i / δ < (δ * ((k i : ℝ) + 1)) / δ := by gcongr
      _ = (k i : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
  have hpr_div1 : ((N : ℤ) : ℝ) * (j i : ℝ) ≤ p i / δ := by
    have h_eq : r * (j i : ℝ) = ((N : ℤ) : ℝ) * δ * (j i : ℝ) := by
      rw [hN] <;> norm_cast <;> ring
    rw [h_eq] at hpr1
    calc ((N : ℤ) : ℝ) * (j i : ℝ) = (((N : ℤ) : ℝ) * δ * (j i : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
      _ ≤ p i / δ := by gcongr
  have hpr_div2 : p i / δ < ((N : ℤ) : ℝ) * ((j i : ℝ) + 1) := by
    have h_eq : r * ((j i : ℝ) + 1) = ((N : ℤ) : ℝ) * δ * ((j i : ℝ) + 1) := by
      rw [hN] <;> norm_cast <;> ring
    rw [h_eq] at hpr2
    calc p i / δ < (((N : ℤ) : ℝ) * δ * ((j i : ℝ) + 1)) / δ := by gcongr
      _ = ((N : ℤ) : ℝ) * ((j i : ℝ) + 1) := by field_simp [hδ.ne'] <;> ring
  have h_bound1 : (N : ℤ) * (j i) ≤ (k i) := by
    have h1 : ((N : ℤ) : ℝ) * (j i : ℝ) < (k i : ℝ) + 1 := by
      calc ((N : ℤ) : ℝ) * (j i : ℝ) ≤ p i / δ := hpr_div1
        _ < (k i : ℝ) + 1 := hp_div2
    have h2 : (N : ℤ) * (j i) < (k i) + 1 := by exact_mod_cast h1
    omega
  have h_bound2 : (k i) + 1 ≤ (N : ℤ) * ((j i) + 1) := by
    have h1 : (k i : ℝ) < ((N : ℤ) : ℝ) * ((j i : ℝ) + 1) := by
      calc (k i : ℝ) ≤ p i / δ := hp_div1
        _ < ((N : ℤ) : ℝ) * ((j i : ℝ) + 1) := hpr_div2
    have h2 : (k i) < (N : ℤ) * ((j i) + 1) := by exact_mod_cast h1
    omega
  have h71 : ((N : ℤ) : ℝ) * (j i : ℝ) ≤ (k i : ℝ) := by exact_mod_cast h_bound1
  have h_lower : r * (j i : ℝ) ≤ q i := by
    have h5 : r * (j i : ℝ) = ((N : ℤ) : ℝ) * δ * (j i : ℝ) := by
      rw [hN] <;> norm_cast <;> ring
    rw [h5]
    have h6 : ((N : ℤ) : ℝ) * δ * (j i : ℝ) ≤ δ * (k i : ℝ) := by
      nlinarith [h71, hδ]
    have hq1 : δ * (k i : ℝ) ≤ q i := (hq i).1
    linarith
  have h72 : (k i : ℝ) + 1 ≤ ((N : ℤ) : ℝ) * ((j i : ℝ) + 1) := by exact_mod_cast h_bound2
  have h_upper : q i < r * ((j i : ℝ) + 1) := by
    have h5 : r * ((j i : ℝ) + 1) = ((N : ℤ) : ℝ) * δ * ((j i : ℝ) + 1) := by
      rw [hN] <;> norm_cast <;> ring
    rw [h5]
    have h6 : δ * ((k i : ℝ) + 1) ≤ ((N : ℤ) : ℝ) * δ * ((j i : ℝ) + 1) := by
      nlinarith [h72, hδ]
    have hq2 : q i < δ * ((k i : ℝ) + 1) := (hq i).2
    linarith
  exact ⟨h_lower, h_upper⟩

/-- If S is a (δ,s,C)-set, then the union of dyadic cubes meeting S
is also a (δ,s,C)-set. -/
lemma cube_union_preserves_delta_set
    {δ s C : ℝ} {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hδ_pos : 0 < δ)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hS : IsDeltaSCSet δ s C S) :
    IsDeltaSCSet δ s C (cubeUnion δ S) := by
  let U := cubeUnion δ S
  have hS_bdd : IsBounded S := hS.1
  have hS_nonempty : S.Nonempty := hS.2.1
  have h1_d : 1 ≤ 2 := by norm_num
  have hS_delta : ∀ ⦃r : ℝ⦄ ⦃Q : Set (EuclideanSpace ℝ (Fin 2))⦄,
      r ∈ dyadicScales → Q ∈ dyadicCubes 2 r → δ ≤ r → r ≤ 1 →
        ENat.toENNReal (dyadicCoveringNumber δ (S ∩ Q)) ≤
          ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber δ S) *
            ENNReal.ofReal (r ^ s) := hS.2.2.2.2.2.2.2.2

  -- U is bounded: finite sUnion of bounded cubes
  have h_finite_cubes : (dyadicCubesMeeting δ S).Finite :=
    dyadicCubesMeeting_finite hδ_pos hS_bdd
  have h_all_bounded : ∀ Q ∈ dyadicCubesMeeting δ S, IsBounded Q := by
    intro Q hQ
    rcases hQ.1 with ⟨k, rfl⟩
    exact dyadicCube_bounded
  have hU_bdd : IsBounded U :=
    (Bornology.isBounded_sUnion h_finite_cubes).mpr h_all_bounded

  -- U is nonempty
  have hU_nonempty : U.Nonempty := by
    rcases hS_nonempty with ⟨x, hx⟩
    let k : Fin 2 → ℤ := fun i => Int.floor (x i / δ)
    have h_x_in_cube : x ∈ dyadicCube δ k := point_in_cubeContaining hδ_pos x
    have h_cube_meets_S : (dyadicCube δ k ∩ S).Nonempty := ⟨x, h_x_in_cube, hx⟩
    have h_cube_in : dyadicCube δ k ∈ dyadicCubesMeeting δ S :=
      ⟨⟨k, rfl⟩, h_cube_meets_S⟩
    exact ⟨x, Set.mem_sUnion.mpr ⟨dyadicCube δ k, h_cube_in, h_x_in_cube⟩⟩

  -- Cubes meeting U = cubes meeting S
  have h_cubes_eq : dyadicCubesMeeting δ U = dyadicCubesMeeting δ S := by
    ext Q
    simp only [dyadicCubesMeeting, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hQ_cube, ⟨x, hxQ, hxU⟩⟩
      rcases Set.mem_sUnion.mp hxU with ⟨Q', hQ'_in, hxQ'⟩
      rcases hQ_cube with ⟨k, rfl⟩
      rcases hQ'_in.1 with ⟨k', rfl⟩
      have h_disj : k = k' := dyadic_cube_disjoint_or_equal hδ_pos ⟨x, hxQ, hxQ'⟩
      rw [h_disj] at *
      exact hQ'_in
    · rintro ⟨hQ_cube, ⟨x, hxQ, hxS⟩⟩
      have hQ_in : Q ∈ dyadicCubesMeeting δ S := ⟨hQ_cube, ⟨x, hxQ, hxS⟩⟩
      have hxU : x ∈ U := Set.mem_sUnion.mpr ⟨Q, hQ_in, hxQ⟩
      exact ⟨hQ_cube, ⟨x, hxQ, hxU⟩⟩

  -- For any dyadic r-cube Q (r≥δ), cubes meeting U∩Q = cubes meeting S∩Q
  have h_inter_eq : ∀ (r : ℝ), r ∈ dyadicScales →
      ∀ (Q : Set (EuclideanSpace ℝ (Fin 2))), Q ∈ dyadicCubes 2 r → δ ≤ r → r ≤ 1 →
        dyadicCubesMeeting δ (U ∩ Q) = dyadicCubesMeeting δ (S ∩ Q) := by
    intro r hr Q hQ hδ_le_r hr_le_one
    rcases hQ with ⟨j, rfl⟩
    have hN : ∃ (N : ℕ), r = (N : ℝ) * δ := dyadic_scale_multiple hδ_dyadic hr hδ_le_r
    ext Q'
    simp only [dyadicCubesMeeting, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hQ'_cube, ⟨x, hxQ', hxUQ⟩⟩
      rcases hQ'_cube with ⟨k, rfl⟩
      have hxU : x ∈ U := hxUQ.1
      have hxQ : x ∈ dyadicCube r j := hxUQ.2
      rcases Set.mem_sUnion.mp hxU with ⟨Q'', hQ''_in, hxQ''⟩
      rcases hQ''_in with ⟨hQ''_cube, ⟨y, hyQ'', hyS⟩⟩
      rcases hQ''_cube with ⟨k', rfl⟩
      have h_disj : k = k' := dyadic_cube_disjoint_or_equal hδ_pos ⟨x, hxQ', hxQ''⟩
      have hr_pos : 0 < r := dyadicScales_pos hr
      have h_k'_in_r : dyadicCube δ k' ⊆ dyadicCube r j :=
        dyadicCubeContainment hδ_pos hr_pos hN ⟨x, hxQ'', hxQ⟩
      have h_y_in_Q' : y ∈ dyadicCube δ k' := hyQ''
      have h_y_in_Q : y ∈ dyadicCube r j := h_k'_in_r h_y_in_Q'
      have h_y_in_S : y ∈ S := hyS
      have h_k_eq : k' = k := h_disj.symm
      have h_y_in_Qk : y ∈ dyadicCube δ k := by
        rw [h_k_eq] at h_y_in_Q'; exact h_y_in_Q'
      exact ⟨⟨k, rfl⟩, ⟨y, h_y_in_Qk, ⟨h_y_in_S, h_y_in_Q⟩⟩⟩
    · rintro ⟨hQ'_cube, ⟨x, hxQ', hxSQ⟩⟩
      rcases hQ'_cube with ⟨k, rfl⟩
      have hxS : x ∈ S := hxSQ.1
      have hxQ : x ∈ dyadicCube r j := hxSQ.2
      have hQ'_in : dyadicCube δ k ∈ dyadicCubesMeeting δ S :=
        ⟨⟨k, rfl⟩, ⟨x, hxQ', hxS⟩⟩
      have hxU : x ∈ U := Set.mem_sUnion.mpr ⟨dyadicCube δ k, hQ'_in, hxQ'⟩
      have hr_pos2 : 0 < r := dyadicScales_pos hr
      have h_k_in_r : dyadicCube δ k ⊆ dyadicCube r j :=
        dyadicCubeContainment hδ_pos hr_pos2 hN ⟨x, hxQ', hxQ⟩
      have hx_in_UQ : x ∈ U ∩ dyadicCube r j := ⟨hxU, hxQ⟩
      exact ⟨⟨k, rfl⟩, ⟨x, hxQ', hx_in_UQ⟩⟩

  refine' ⟨hU_bdd, hU_nonempty, h1_d, hδ_dyadic, hδ_pos, hS.2.2.2.2.2.1, hS.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.1, _⟩
  intro r Q hr hQ_cube hδ_le_r hr_le_one
  have h_cover_U : ENat.toENNReal (dyadicCoveringNumber δ U) =
      ENat.toENNReal (dyadicCoveringNumber δ S) := by
    simp only [dyadicCoveringNumber, h_cubes_eq]
  have h_cover_inter : ENat.toENNReal (dyadicCoveringNumber δ (U ∩ Q)) =
      ENat.toENNReal (dyadicCoveringNumber δ (S ∩ Q)) := by
    simp only [dyadicCoveringNumber, h_inter_eq r hr Q hQ_cube hδ_le_r hr_le_one]
  rw [h_cover_inter, h_cover_U]
  exact hS_delta hr hQ_cube hδ_le_r hr_le_one

/-- Covering number is preserved by taking the cube union. -/
lemma cubeUnion_coveringNumber_eq {d : ℕ} {δ : ℝ} {S : Set (EuclideanSpace ℝ (Fin d))}
    (hδ_pos : 0 < δ) :
    ENat.toENNReal (dyadicCoveringNumber δ (cubeUnion δ S)) =
      ENat.toENNReal (dyadicCoveringNumber δ S) := by
  have h_cubes_eq : dyadicCubesMeeting δ (cubeUnion δ S) = dyadicCubesMeeting δ S := by
    ext Q
    simp only [dyadicCubesMeeting, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hQ_cube, ⟨x, hxQ, hxU⟩⟩
      rcases Set.mem_sUnion.mp hxU with ⟨Q', hQ'_in, hxQ'⟩
      rcases hQ_cube with ⟨k, rfl⟩
      rcases hQ'_in.1 with ⟨k', rfl⟩
      have h_disj : k = k' := dyadic_cube_disjoint_or_equal hδ_pos ⟨x, hxQ, hxQ'⟩
      rw [h_disj] at *
      exact hQ'_in
    · rintro ⟨hQ_cube, ⟨x, hxQ, hxS⟩⟩
      have hQ_in : Q ∈ dyadicCubesMeeting δ S := ⟨hQ_cube, ⟨x, hxQ, hxS⟩⟩
      have hxU : x ∈ cubeUnion δ S := Set.mem_sUnion.mpr ⟨Q, hQ_in, hxQ⟩
      exact ⟨hQ_cube, ⟨x, hxQ, hxU⟩⟩
  simp only [dyadicCoveringNumber, h_cubes_eq]

/-- Cube union is monotone with respect to set inclusion. -/
lemma cubeUnion_mono {d : ℕ} {δ : ℝ} {A B : Set (EuclideanSpace ℝ (Fin d))}
    (h : A ⊆ B) : cubeUnion δ A ⊆ cubeUnion δ B := by
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨Q, hQ_in, hxQ⟩
  have hQ_meets_B : (Q ∩ B).Nonempty := by
    rcases hQ_in.2 with ⟨y, hyQ, hyA⟩
    exact ⟨y, hyQ, h hyA⟩
  have hQ_in_B : Q ∈ dyadicCubesMeeting δ B := ⟨hQ_in.1, hQ_meets_B⟩
  exact Set.mem_sUnion.mpr ⟨Q, hQ_in_B, hxQ⟩

/-- Dyadic covering number is monotone with respect to set inclusion. -/
lemma coveringNumber_mono {d : ℕ} {δ : ℝ} {A B : Set (EuclideanSpace ℝ (Fin d))}
    (h : A ⊆ B) :
    ENat.toENNReal (dyadicCoveringNumber δ A) ≤
      ENat.toENNReal (dyadicCoveringNumber δ B) := by
  have h1 : dyadicCubesMeeting δ A ⊆ dyadicCubesMeeting δ B := by
    intro Q hQ
    rcases hQ.2 with ⟨y, hyQ, hyA⟩
    exact ⟨hQ.1, ⟨y, hyQ, h hyA⟩⟩
  have h2 : (dyadicCoveringNumber δ A) ≤ (dyadicCoveringNumber δ B) :=
    Set.encard_mono h1
  exact_mod_cast h2

end ProductLikeIncidence.ProductReduction
