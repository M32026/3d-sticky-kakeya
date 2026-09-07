module

/-
# Pz Trim Helpers

Helpers for constructing `Pz_trim = Pz ∩ ⋃₀ A'` and proving it retains the
(δ,s,C)-set property.

## Main lemmas

1. `cubes_meeting_P_intersection_eq`: `dyadicCubesMeeting δ (P ∩ ⋃₀ A') = A'`
   when every cube in A' meets P.

2. `cubes_meeting_P_intersection_rcube_eq`: for an r-cube Q,
   `dyadicCubesMeeting δ ((P ∩ ⋃₀ A') ∩ Q) = {C ∈ A' | C ⊆ Q}`.

3. `delta_sc_set_intersection_with_cube_union`: if `⋃₀ A'` is a (δ,s,C)-set
   and every cube in A' meets P, then `P ∩ ⋃₀ A'` is also a (δ,s,C)-set.

## Whiteprint node
`pelican_pz_trim_helpers`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.ProductLikeProof

@[expose] public section

noncomputable section

open Set

attribute [local instance] Classical.propDecidable

/-- If two δ-dyadic cubes have nonempty intersection, they are equal. -/
private lemma dyadicCube_eq_of_intersect' {δ : ℝ} {d : ℕ} (hδ : 0 < δ)
    {k j : Fin d → ℤ}
    (h : (dyadicCube δ k ∩ dyadicCube δ j).Nonempty) :
    dyadicCube δ k = dyadicCube δ j := by
  rcases h with ⟨p, hp1, hp2⟩
  have hkj : k = j := by
    funext i
    set x : ℝ := p i / δ with hx_def
    have hx : δ * x = p i := by
      simp only [hx_def]
      field_simp [hδ.ne'] <;> ring
    have h1 : (k i : ℝ) ≤ x := by
      have h11 : δ * (k i : ℝ) ≤ p i := (hp1 i).1
      rw [←hx] at h11
      nlinarith
    have h2 : x < (k i : ℝ) + 1 := by
      have h21 : p i < δ * ((k i : ℝ) + 1) := (hp1 i).2
      rw [←hx] at h21
      nlinarith
    have h3 : (j i : ℝ) ≤ x := by
      have h31 : δ * (j i : ℝ) ≤ p i := (hp2 i).1
      rw [←hx] at h31
      nlinarith
    have h4 : x < (j i : ℝ) + 1 := by
      have h41 : p i < δ * ((j i : ℝ) + 1) := (hp2 i).2
      rw [←hx] at h41
      nlinarith
    by_cases h5 : k i < j i
    · have h6 : (k i : ℝ) + 1 ≤ (j i : ℝ) := by exact_mod_cast (Int.add_one_le_of_lt h5)
      linarith
    · by_cases h7 : j i < k i
      · have h8 : (j i : ℝ) + 1 ≤ (k i : ℝ) := by exact_mod_cast (Int.add_one_le_of_lt h7)
        linarith
      · have h9 : k i = j i := by omega
        exact h9
  rw [hkj]

/-- A dyadic cube at positive scale is nonempty. -/
private lemma dyadicCube_nonempty' {δ : ℝ} {d : ℕ} (hδ : 0 < δ)
    {k : Fin d → ℤ} : (dyadicCube δ k).Nonempty := by
  let f : Fin d → ℝ := fun i => δ * (k i : ℝ)
  let p : EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 _).symm f
  have hpf : ∀ i, p i ∈ Set.Ico (δ * (k i : ℝ)) (δ * ((k i : ℝ) + 1)) := by
    intro i
    simp only [p, WithLp.equiv_symm_apply]
    constructor <;> linarith [hδ]
  exact ⟨p, hpf⟩

/-- If A' is a finite family of δ-dyadic cubes, every cube in A' meets P,
then the δ-dyadic cubes meeting `P ∩ ⋃₀ A'` are exactly A'. -/
lemma cubes_meeting_P_intersection_eq {δ : ℝ} {d : ℕ} (hδ : 0 < δ)
    (A' : Finset (Set (EuclideanSpace ℝ (Fin d))))
    (hA'_cubes : ∀ Q ∈ A', Q ∈ dyadicCubes d δ)
    {P : Set (EuclideanSpace ℝ (Fin d))}
    (hA'_meet_P : ∀ Q ∈ A', (Q ∩ P).Nonempty) :
    dyadicCubesMeeting (d := d) δ (P ∩ ⋃₀ (A' : Set (Set (EuclideanSpace ℝ (Fin d))))) =
      (A' : Set (Set (EuclideanSpace ℝ (Fin d)))) := by
  let U : Set (EuclideanSpace ℝ (Fin d)) := ⋃₀ (A' : Set (Set (EuclideanSpace ℝ (Fin d))))
  ext Q
  simp only [dyadicCubesMeeting, mem_setOf_eq, Finset.mem_coe]
  constructor
  · rintro ⟨hQ_dyadic, h_meet⟩
    rcases h_meet with ⟨p, hpQ, ⟨hpP, hpU⟩⟩
    rcases hpU with ⟨Cube, hCube_in, hpCube⟩
    have hCube_dyadic : Cube ∈ dyadicCubes d δ := hA'_cubes Cube hCube_in
    rcases hQ_dyadic with ⟨k, hk⟩
    rcases hCube_dyadic with ⟨j, hj⟩
    have hpc_k : p ∈ dyadicCube δ k := by rw [←hk]; exact hpQ
    have hpc_j : p ∈ dyadicCube δ j := by rw [←hj]; exact hpCube
    have h_eq : dyadicCube δ k = dyadicCube δ j :=
      dyadicCube_eq_of_intersect' hδ ⟨p, hpc_k, hpc_j⟩
    have hQ_eq_Cube : Q = Cube := by
      calc Q = dyadicCube δ k := hk
        _ = dyadicCube δ j := h_eq
        _ = Cube := hj.symm
    rw [hQ_eq_Cube]
    exact hCube_in
  · intro hQ_in
    have hQ_dyadic : Q ∈ dyadicCubes d δ := hA'_cubes Q hQ_in
    have hQ_meet_P : (Q ∩ P).Nonempty := hA'_meet_P Q hQ_in
    rcases hQ_meet_P with ⟨p, hpQ, hpP⟩
    have hpU : p ∈ U := ⟨Q, hQ_in, hpQ⟩
    have h_meet : (Q ∩ (P ∩ U)).Nonempty := ⟨p, hpQ, ⟨hpP, hpU⟩⟩
    exact ⟨hQ_dyadic, h_meet⟩

/-- If A' is a finite family of δ-dyadic cubes, every cube in A' meets P,
and Q is an r-dyadic cube with δ ≤ r, then the δ-dyadic cubes meeting
`(P ∩ ⋃₀ A') ∩ Q` are exactly those in A' that are contained in Q. -/
lemma cubes_meeting_P_intersection_rcube_eq {δ r : ℝ} {d : ℕ}
    (hδ : 0 < δ) (hδ_le_r : δ ≤ r)
    (hδ_dyadic : δ ∈ dyadicScales) (hr_dyadic : r ∈ dyadicScales)
    (A' : Finset (Set (EuclideanSpace ℝ (Fin d))))
    (hA'_cubes : ∀ C ∈ A', C ∈ dyadicCubes d δ)
    {P : Set (EuclideanSpace ℝ (Fin d))}
    (hA'_meet_P : ∀ C ∈ A', (C ∩ P).Nonempty)
    {Q : Set (EuclideanSpace ℝ (Fin d))}
    (hQ : Q ∈ dyadicCubes d r) :
    dyadicCubesMeeting (d := d) δ ((P ∩ ⋃₀ (A' : Set (Set (EuclideanSpace ℝ (Fin d))))) ∩ Q) =
      ((A'.filter (fun C => C ⊆ Q)) : Set (Set (EuclideanSpace ℝ (Fin d)))) := by
  let U : Set (EuclideanSpace ℝ (Fin d)) := ⋃₀ (A' : Set (Set (EuclideanSpace ℝ (Fin d))))
  ext Cube
  simp only [dyadicCubesMeeting, mem_setOf_eq]
  constructor
  · rintro ⟨hCube_dyadic, h_meet⟩
    rcases h_meet with ⟨p, hpCube, ⟨⟨hpP, hpU⟩, hpQ⟩⟩
    rcases hpU with ⟨Cube', hCube'_in, hpCube'⟩
    have hCube'_dyadic : Cube' ∈ dyadicCubes d δ := hA'_cubes Cube' hCube'_in
    rcases hCube_dyadic with ⟨k, hk⟩
    rcases hCube'_dyadic with ⟨j, hj⟩
    have hpc_k : p ∈ dyadicCube δ k := by rw [←hk]; exact hpCube
    have hpc_j : p ∈ dyadicCube δ j := by rw [←hj]; exact hpCube'
    have h_eq : dyadicCube δ k = dyadicCube δ j :=
      dyadicCube_eq_of_intersect' hδ ⟨p, hpc_k, hpc_j⟩
    have hCube_eq_Cube' : Cube = Cube' := by
      calc Cube = dyadicCube δ k := hk
        _ = dyadicCube δ j := h_eq
        _ = Cube' := hj.symm
    have hCube_in_A' : Cube ∈ A' := by
      rw [hCube_eq_Cube']; exact hCube'_in
    have hCube_sub_Q : Cube ⊆ Q := by
      rcases hQ with ⟨jQ, hQ_eq⟩
      have h_meet_Q : (dyadicCube δ j ∩ dyadicCube r jQ).Nonempty := by
        rw [←hj, ←hQ_eq]
        exact ⟨p, hpCube', hpQ⟩
      have h_nest : dyadicCube δ j ⊆ dyadicCube r jQ :=
        ProductLikeIncidence.dyadicCube_nesting hδ hδ_le_r hδ_dyadic hr_dyadic j jQ h_meet_Q
      rw [hCube_eq_Cube', hj, hQ_eq]
      exact h_nest
    have h_goal : Cube ∈ (A'.filter (fun C' => C' ⊆ Q) : Set _) := by
      simp only [Finset.mem_coe, Finset.mem_filter]
      exact ⟨hCube_in_A', hCube_sub_Q⟩
    exact h_goal
  · intro h
    have h' : Cube ∈ A' ∧ Cube ⊆ Q := by
      simpa [Finset.mem_coe, Finset.mem_filter] using h
    have hCube_in_A' : Cube ∈ A' := h'.1
    have hCube_sub_Q : Cube ⊆ Q := h'.2
    have hCube_dyadic : Cube ∈ dyadicCubes d δ := hA'_cubes Cube hCube_in_A'
    have hCube_meet_P : (Cube ∩ P).Nonempty := hA'_meet_P Cube hCube_in_A'
    rcases hCube_meet_P with ⟨p, hpCube, hpP⟩
    have hpU : p ∈ U := ⟨Cube, hCube_in_A', hpCube⟩
    have hpQ : p ∈ Q := hCube_sub_Q hpCube
    have h_meet : (Cube ∩ ((P ∩ U) ∩ Q)).Nonempty := ⟨p, hpCube, ⟨⟨hpP, hpU⟩, hpQ⟩⟩
    exact ⟨hCube_dyadic, h_meet⟩

/-- If `⋃₀ A'` is a (δ,s,C)-set and every cube in A' meets P, then
`P ∩ ⋃₀ A'` is also a (δ,s,C)-set. -/
lemma delta_sc_set_intersection_with_cube_union {δ s C : ℝ} {d : ℕ}
    (A' : Finset (Set (EuclideanSpace ℝ (Fin d))))
    (hA'_cubes : ∀ Q ∈ A', Q ∈ dyadicCubes d δ)
    {P : Set (EuclideanSpace ℝ (Fin d))}
    (hA'_meet_P : ∀ Q ∈ A', (Q ∩ P).Nonempty)
    (hS1_regular : IsDeltaSCSet δ s C (⋃₀ (A' : Set (Set (EuclideanSpace ℝ (Fin d)))))) :
    IsDeltaSCSet δ s C (P ∩ ⋃₀ (A' : Set (Set (EuclideanSpace ℝ (Fin d))))) := by
  let U : Set (EuclideanSpace ℝ (Fin d)) := ⋃₀ (A' : Set (Set (EuclideanSpace ℝ (Fin d))))
  let S2 := P ∩ U
  have h1_bdd : Bornology.IsBounded U := hS1_regular.1
  have h1_nonempty : U.Nonempty := hS1_regular.2.1
  have h_d_ge1 : 1 ≤ d := hS1_regular.2.2.1
  have hδ_dyadic : δ ∈ dyadicScales := hS1_regular.2.2.2.1
  have hδ_pos : 0 < δ := hS1_regular.2.2.2.2.1
  have hs_nonneg : 0 ≤ s := hS1_regular.2.2.2.2.2.1
  have hs_le_d : s ≤ (d : ℝ) := hS1_regular.2.2.2.2.2.2.1
  have hC_pos : 0 < C := hS1_regular.2.2.2.2.2.2.2.1
  have h1_reg : ∀ (r : ℝ) (Q : Set (EuclideanSpace ℝ (Fin d))),
      r ∈ dyadicScales → Q ∈ dyadicCubes d r → δ ≤ r → r ≤ 1 →
        ENat.toENNReal (dyadicCoveringNumber (d := d) δ (U ∩ Q)) ≤
          ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber (d := d) δ U) *
            ENNReal.ofReal (r ^ s) := hS1_regular.2.2.2.2.2.2.2.2
  have h2_bdd : Bornology.IsBounded S2 := by
    have h_sub : S2 ⊆ U := inter_subset_right
    exact Bornology.IsBounded.subset h1_bdd h_sub
  have h2_nonempty : S2.Nonempty := by
    have hA'_nonempty : A'.Nonempty := by
      by_contra h
      have h_empty : A' = ∅ := by simpa using h
      have hU_empty : U = ∅ := by
        simp [U, h_empty]
      rw [hU_empty] at h1_nonempty
      simp at h1_nonempty
    rcases hA'_nonempty with ⟨Q, hQ_in⟩
    have hQ_meet_P : (Q ∩ P).Nonempty := hA'_meet_P Q hQ_in
    rcases hQ_meet_P with ⟨p, hpQ, hpP⟩
    have hpU : p ∈ U := ⟨Q, hQ_in, hpQ⟩
    exact ⟨p, hpP, hpU⟩
  have hA'_nonempty' : A'.Nonempty := by
      by_contra h
      have h_empty : A' = ∅ := by simpa using h
      have hU_empty : U = ∅ := by
        simp [U, h_empty]
      rw [hU_empty] at h1_nonempty
      simp at h1_nonempty
  have hA'_meet_univ : ∀ Q ∈ A', (Q ∩ (Set.univ : Set (EuclideanSpace ℝ (Fin d)))).Nonempty := by
    intro Q hQ
    have hQ_dyadic : Q ∈ dyadicCubes d δ := hA'_cubes Q hQ
    rcases hQ_dyadic with ⟨k, rfl⟩
    simpa using dyadicCube_nonempty' hδ_pos
  have h_cover_S2 : dyadicCoveringNumber (d := d) δ S2 =
        dyadicCoveringNumber (d := d) δ U := by
    have h_eq1 : dyadicCubesMeeting (d := d) δ S2 = (A' : Set _) :=
      cubes_meeting_P_intersection_eq hδ_pos A' hA'_cubes hA'_meet_P
    have h_eq2_raw : dyadicCubesMeeting (d := d) δ ((Set.univ : Set _) ∩ U) = (A' : Set _) :=
      cubes_meeting_P_intersection_eq hδ_pos A' hA'_cubes hA'_meet_univ
    have h_univ_inter : (Set.univ : Set (EuclideanSpace ℝ (Fin d))) ∩ U = U := by simp
    have h_eq2 : dyadicCubesMeeting (d := d) δ U = (A' : Set _) := by
      rw [←h_univ_inter]; exact h_eq2_raw
    rw [dyadicCoveringNumber, dyadicCoveringNumber, h_eq1, h_eq2]
  have h2_reg : ∀ (r : ℝ) (Q : Set (EuclideanSpace ℝ (Fin d))),
      r ∈ dyadicScales → Q ∈ dyadicCubes d r → δ ≤ r → r ≤ 1 →
        ENat.toENNReal (dyadicCoveringNumber (d := d) δ (S2 ∩ Q)) ≤
          ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber (d := d) δ S2) *
            ENNReal.ofReal (r ^ s) := by
    intro r Q hr_dyadic' hQ_dyadic hδ_le_r hr_le_one
    have h_eq3 : dyadicCubesMeeting (d := d) δ (S2 ∩ Q) =
          ((A'.filter (fun C => C ⊆ Q)) : Set _) :=
      cubes_meeting_P_intersection_rcube_eq hδ_pos hδ_le_r hδ_dyadic hr_dyadic'
        A' hA'_cubes hA'_meet_P hQ_dyadic
    have h_eq4_raw : dyadicCubesMeeting (d := d) δ (((Set.univ : Set _) ∩ U) ∩ Q) =
          ((A'.filter (fun C => C ⊆ Q)) : Set _) :=
      cubes_meeting_P_intersection_rcube_eq hδ_pos hδ_le_r hδ_dyadic hr_dyadic'
        A' hA'_cubes hA'_meet_univ hQ_dyadic
    have h_univ_inter2 : ((Set.univ : Set (EuclideanSpace ℝ (Fin d))) ∩ U) ∩ Q = U ∩ Q := by simp
    have h_eq4 : dyadicCubesMeeting (d := d) δ (U ∩ Q) =
          ((A'.filter (fun C => C ⊆ Q)) : Set _) := by
      rw [←h_univ_inter2]; exact h_eq4_raw
    have h_cover_inter : dyadicCoveringNumber (d := d) δ (S2 ∩ Q) =
          dyadicCoveringNumber (d := d) δ (U ∩ Q) := by
      rw [dyadicCoveringNumber, dyadicCoveringNumber, h_eq3, h_eq4]
    rw [h_cover_inter, h_cover_S2]
    exact h1_reg r Q hr_dyadic' hQ_dyadic hδ_le_r hr_le_one
  exact ⟨h2_bdd, h2_nonempty, h_d_ge1, hδ_dyadic, hδ_pos, hs_nonneg, hs_le_d, hC_pos, h2_reg⟩
