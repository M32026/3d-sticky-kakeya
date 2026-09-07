module

/-
# Covering Number to Finset Bridge

Convert between `Nreal δ A` (ENNReal covering number) and finite subsets
of A with one point per δ-cube.

## Forward
If `Nreal δ A ≥ ENNReal.ofReal L` and A is bounded, construct a finite
`A_fin ⊆ A` with one point per δ-cube, such that `A_fin.card ≥ L`.

## Reverse
If `A_fin ⊆ A` has one point per δ-cube (distinct points lie in distinct
dyadic cubes), then `Nreal δ A ≥ A_fin.card`.

## Whiteprint node
`robust_projection/CoveringToFinset`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.Compat
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory Set ENNReal Finset Classical

namespace robust_projection

/-- Dyadic cubes at the same scale are disjoint. -/
lemma dyadic_cubes_disjoint {d : ℕ} {r : ℝ} (hr : 0 < r)
    {k1 k2 : Fin d → ℤ} (h : k1 ≠ k2) :
    Disjoint (dyadicCube r k1) (dyadicCube r k2) := by
  have hi : ∃ i : Fin d, k1 i ≠ k2 i := by
    by_contra h'
    push Not at h'
    have h'' : k1 = k2 := by funext i; exact h' i
    exact h h''
  rcases hi with ⟨i, hne⟩
  have h_cases : k1 i < k2 i ∨ k2 i < k1 i := by omega
  rcases h_cases with (h_lt | h_lt')
  · have h3 : (k2 i : ℝ) ≥ (k1 i : ℝ) + 1 := by exact_mod_cast (by linarith)
    simp only [dyadicCube, Set.disjoint_left, Set.mem_setOf_eq]
    intro x hx1 hx2
    have h1 : x i ∈ Set.Ico (r * (k1 i : ℝ)) (r * ((k1 i : ℝ) + 1)) := hx1 i
    have h2 : x i ∈ Set.Ico (r * (k2 i : ℝ)) (r * ((k2 i : ℝ) + 1)) := hx2 i
    have h4 : r * ((k1 i : ℝ) + 1) ≤ r * (k2 i : ℝ) := by gcongr
    have h5 : x i < r * ((k1 i : ℝ) + 1) := h1.2
    have h6 : r * (k2 i : ℝ) ≤ x i := h2.1
    have h7 : r * ((k1 i : ℝ) + 1) ≤ r * (k2 i : ℝ) := h4
    linarith
  · have h3 : (k1 i : ℝ) ≥ (k2 i : ℝ) + 1 := by exact_mod_cast (by linarith)
    simp only [dyadicCube, Set.disjoint_left, Set.mem_setOf_eq]
    intro x hx1 hx2
    have h1 : x i ∈ Set.Ico (r * (k1 i : ℝ)) (r * ((k1 i : ℝ) + 1)) := hx1 i
    have h2 : x i ∈ Set.Ico (r * (k2 i : ℝ)) (r * ((k2 i : ℝ) + 1)) := hx2 i
    have h4 : r * ((k2 i : ℝ) + 1) ≤ r * (k1 i : ℝ) := by gcongr
    have h5 : x i < r * ((k2 i : ℝ) + 1) := h2.2
    have h6 : r * (k1 i : ℝ) ≤ x i := h1.1
    linarith

/-- The unique dyadic cube containing a real number. -/
def cubeOf (δ : ℝ) (x : ℝ) : Set (EuclideanSpace ℝ (Fin 1)) :=
  dyadicCube δ (fun _ : Fin 1 => Int.floor (x / δ))

/-- A real number's 1D copy lies in its cube. -/
lemma mem_cubeOf {δ : ℝ} (hδ_pos : 0 < δ) (x : ℝ) :
    realLineCopy {x} ⊆ cubeOf δ x := by
  intro p hp
  have hpx : p 0 = x := by
    simpa [realLineCopy] using hp
  simp only [cubeOf, dyadicCube, Set.mem_setOf_eq]
  intro i
  have h_i : i = 0 := by
    fin_cases i <;> rfl
  rw [h_i, hpx]
  have h1 : (Int.floor (x / δ) : ℝ) ≤ x / δ := Int.floor_le _
  have h2 : x / δ < (Int.floor (x / δ) : ℝ) + 1 := Int.lt_floor_add_one _
  constructor
  · calc δ * (Int.floor (x / δ) : ℝ) ≤ δ * (x / δ) := by gcongr
      _ = x := by field_simp [hδ_pos.ne'] <;> ring
  · calc x = δ * (x / δ) := by field_simp [hδ_pos.ne'] <;> ring
      _ < δ * ((Int.floor (x / δ) : ℝ) + 1) := by gcongr

/-- If x is in the 1D projection of dyadic cube k, then cubeOf δ x equals that cube. -/
lemma cubeOf_eq {δ : ℝ} (hδ_pos : 0 < δ) {x : ℝ} {k : Fin 1 → ℤ}
    (h : x ∈ Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 : ℝ) + 1))) :
    cubeOf δ x = dyadicCube δ k := by
  have h2 : (k 0 : ℝ) ≤ x / δ := by
    calc (k 0 : ℝ)
      = δ * (k 0 : ℝ) / δ := by field_simp [hδ_pos.ne'] <;> ring
    _ ≤ x / δ := by gcongr <;> exact h.1
  have h3 : x / δ < (k 0 : ℝ) + 1 := by
    calc x / δ
      < δ * ((k 0 : ℝ) + 1) / δ := by gcongr <;> exact h.2
    _ = (k 0 : ℝ) + 1 := by field_simp [hδ_pos.ne'] <;> ring
  have h4 : Int.floor (x / δ) = k 0 := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num <;> linarith
  have h5 : (fun _ : Fin 1 => Int.floor (x / δ)) = k := by
    funext i
    fin_cases i
    exact h4
  have h6 : cubeOf δ x = dyadicCube δ (fun _ : Fin 1 => Int.floor (x / δ)) := by
    rfl
  rw [h6, h5]

/-- Forward: extract a finset with one point per δ-cube from a covering bound. -/
lemma finset_from_covering {δ : ℝ} (hδ_pos : 0 < δ)
    {A : Set ℝ} (hA_bdd : Bornology.IsBounded A)
    {L : ℝ} (hL : Nreal δ A ≥ ENNReal.ofReal L) :
    ∃ (A_fin : Finset ℝ), (A_fin : Set ℝ) ⊆ A ∧
      Set.InjOn (cubeOf δ) (A_fin : Set ℝ) ∧
      (A_fin.card : ℝ) ≥ L := by
  by_cases hL_neg : L < 0
  · -- L < 0: empty finset works
    refine ⟨∅, by simp, ?_, ?_⟩
    · simp
    · simp <;> linarith
  · -- L ≥ 0
    have hL_nonneg : 0 ≤ L := by linarith
    let A1 := realLineCopy A
    have hA1_bdd : Bornology.IsBounded A1 := by
      have h_exists : ∃ (R : ℝ), ∀ (x : ℝ), x ∈ A → dist x 0 ≤ R := by exact Bornology.IsBounded.subset_closedBall hA_bdd 0
      rcases h_exists with ⟨R, hR⟩
      have h_main : ∀ (p : EuclideanSpace ℝ (Fin 1)), p ∈ A1 → dist p 0 ≤ R := by
        intro p hp
        have h_p0 : p 0 ∈ A := by
          change p ∈ realLineCopy A at hp
          simpa [realLineCopy] using hp
        have h_norm : ‖p‖ = |p 0| := by
          have h1 : ‖p‖ = Real.sqrt (‖p 0‖ ^ 2) := by
            simp [EuclideanSpace.norm_eq, Finset.sum_singleton]
            <;> norm_num
          have h2 : Real.sqrt (‖p 0‖ ^ 2) = ‖p 0‖ := Real.sqrt_sq (norm_nonneg (p 0))
          have h3 : ‖p 0‖ = |p 0| := by simp
          rw [h1, h2, h3]
        have h_dist : dist p 0 = ‖p‖ := by simp [dist_eq_norm]
        rw [h_dist, h_norm]
        have h4 : dist (p 0) 0 ≤ R := hR (p 0) h_p0
        have h5 : dist (p 0) 0 = |p 0| := by
          simp [dist_eq_norm]
        rw [h5] at h4
        exact h4
      exact ProductLikeIncidence.productLikeRealLineCopy_bounded hA_bdd
    have h_fin : (dyadicCubesMeeting δ A1).Finite := by
      exact ProductLikeIncidence.dyadicCubesMeeting_finite hδ_pos hA1_bdd
    let cubes_fin : Finset (Set (EuclideanSpace ℝ (Fin 1))) := h_fin.toFinset
    have hQs_coe : (cubes_fin : Set (Set (EuclideanSpace ℝ (Fin 1)))) =
        dyadicCubesMeeting δ A1 := by
      simp [cubes_fin, Set.Finite.coe_toFinset]

    -- Choose one point per cube
    let choose_point (Q : Set (EuclideanSpace ℝ (Fin 1))) :
        EuclideanSpace ℝ (Fin 1) :=
      if hQ : Q ∈ cubes_fin then
        Classical.choose (show (Q ∩ A1).Nonempty from by
          have hQ_in : Q ∈ dyadicCubesMeeting δ A1 := by
            rw [←hQs_coe] <;> exact hQ
          exact hQ_in.2)
      else
        (0 : EuclideanSpace ℝ (Fin 1))

    have hchoose_in : ∀ Q ∈ cubes_fin, choose_point Q ∈ Q ∩ A1 := by
      intro Q hQ
      have h_choose : choose_point Q = Classical.choose (show (Q ∩ A1).Nonempty from by
          have hQ_in : Q ∈ dyadicCubesMeeting δ A1 := by
            rw [←hQs_coe] <;> exact hQ
          exact hQ_in.2) := by
        simp [choose_point, hQ]
      rw [h_choose]
      exact Classical.choose_spec _

    -- Chosen points are distinct because cubes are disjoint
    have h_inj : Set.InjOn choose_point (cubes_fin : Set _) := by
      intro Q1 hQ1 Q2 hQ2 h_eq
      by_contra hne_Q
      have hQ1' : Q1 ∈ dyadicCubesMeeting δ A1 := by
        rw [←hQs_coe] <;> exact hQ1
      have hQ2' : Q2 ∈ dyadicCubesMeeting δ A1 := by
        rw [←hQs_coe] <;> exact hQ2
      rcases hQ1'.1 with ⟨k1, hk1⟩
      rcases hQ2'.1 with ⟨k2, hk2⟩
      have hne_k : k1 ≠ k2 := by
        intro h_eq_k
        have h_eq_Q : Q1 = Q2 := by
          rw [hk1, hk2, h_eq_k]
        exact hne_Q h_eq_Q
      have h_disj : Disjoint (dyadicCube δ k1) (dyadicCube δ k2) :=
        dyadic_cubes_disjoint hδ_pos hne_k
      have hp1_orig : choose_point Q1 ∈ Q1 := (hchoose_in Q1 hQ1).1
      have hp2_orig : choose_point Q2 ∈ Q2 := (hchoose_in Q2 hQ2).1
      have h1_set : Q1 = dyadicCube δ k1 := hk1
      have h2_set : Q2 = dyadicCube δ k2 := hk2
      have h1_fn : choose_point Q1 = choose_point (dyadicCube δ k1) := by rw [h1_set]
      have h2_fn : choose_point Q2 = choose_point (dyadicCube δ k2) := by rw [h2_set]
      have hp1_cube : choose_point Q1 ∈ dyadicCube δ k1 := by
        rw [h1_set] at hp1_orig
        rw [h1_fn]
        exact hp1_orig
      have hp2_cube : choose_point Q2 ∈ dyadicCube δ k2 := by
        rw [h2_set] at hp2_orig
        rw [h2_fn]
        exact hp2_orig
      have h_eq' : choose_point Q1 = choose_point Q2 := h_eq
      have hp2_in_k1 : choose_point Q2 ∈ dyadicCube δ k1 := by
        rw [←h_eq']
        exact hp1_cube
      have h_contra : choose_point Q2 ∉ dyadicCube δ k2 :=
        Set.disjoint_left.mp h_disj hp2_in_k1
      exact h_contra hp2_cube

    let points_1D : Finset (EuclideanSpace ℝ (Fin 1)) :=
      Finset.image choose_point cubes_fin

    have h_points_card : points_1D.card = cubes_fin.card :=
      Finset.card_image_of_injOn h_inj

    have h_points_sub_A1 : (points_1D : Set _) ⊆ A1 := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
      exact (hchoose_in Q hQ).2

    -- Map to ℝ
    let A_fin : Finset ℝ := Finset.image (fun p : EuclideanSpace ℝ (Fin 1) => p 0) points_1D

    have hA_fin_sub : (A_fin : Set ℝ) ⊆ A := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
      have h_p_in_A1 : p ∈ A1 := h_points_sub_A1 hp
      have h_p_in_A1 : p ∈ A1 := h_points_sub_A1 hp
      exact h_p_in_A1

    -- p ↦ p 0 is injective on EuclideanSpace ℝ (Fin 1)
    have h_eval_inj : Function.Injective (fun p : EuclideanSpace ℝ (Fin 1) => p 0) := by
      intro p q h
      ext i
      have hi : i = 0 := by fin_cases i <;> rfl
      rw [hi]
      exact h
    have hA_fin_card : A_fin.card = points_1D.card :=
      Finset.card_image_of_injective _ h_eval_inj

    have hNreal_eq : Nreal δ A = (cubes_fin.card : ENNReal) := by
      let S : Set (Set (EuclideanSpace ℝ (Fin 1))) := ↑cubes_fin
      have h3 : (dyadicCubesMeeting δ A1).encard = S.encard := by
        apply congr_arg Set.encard hQs_coe.symm
      have h4 : S.encard = ↑(cubes_fin.card) := by
        have h_S : S = ↑cubes_fin := by rfl
        rw [h_S]
        exact encard_coe_eq_coe_finsetCard cubes_fin
      have h1 : (dyadicCubesMeeting δ A1).encard = ↑(cubes_fin.card) := by
        calc (dyadicCubesMeeting δ A1).encard
          = S.encard := h3
        _ = ↑(cubes_fin.card) := h4
      have h_goal : ENat.toENNReal (dyadicCubesMeeting δ A1).encard = (cubes_fin.card : ENNReal) := by
        rw [h1]
        <;> norm_cast
      simpa [Nreal, dyadicCoveringNumber, A1] using h_goal

    have h_card_ineq : (cubes_fin.card : ENNReal) ≥ ENNReal.ofReal L := by
      rw [←hNreal_eq]
      exact hL

    have h_final : (cubes_fin.card : ℝ) ≥ L := by
      have hL_ne_top : ENNReal.ofReal L ≠ ⊤ := by simp
      have hcard_ne_top : (cubes_fin.card : ENNReal) ≠ ⊤ := by simp
      have h_toReal : (ENNReal.ofReal L).toReal ≤ ((cubes_fin.card : ENNReal)).toReal :=
        (ENNReal.toReal_le_toReal hL_ne_top hcard_ne_top).mpr h_card_ineq
      have h1 : (ENNReal.ofReal L).toReal = L := by
        rw [ENNReal.toReal_ofReal (by linarith)]
      have h2 : ((cubes_fin.card : ENNReal)).toReal = (cubes_fin.card : ℝ) := by simp
      rw [h1, h2] at h_toReal
      exact h_toReal

    have h_one_per_cube : Set.InjOn (cubeOf δ) (A_fin : Set ℝ) := by
      intro x hx y hy h_eq
      rcases Finset.mem_image.mp hx with ⟨px, hpx, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨py, hpy, rfl⟩
      rcases Finset.mem_image.mp hpx with ⟨Qx, hQx, rfl⟩
      rcases Finset.mem_image.mp hpy with ⟨Qy, hQy, rfl⟩
      have hQx' : Qx ∈ dyadicCubesMeeting δ A1 := by
        rw [←hQs_coe] <;> exact hQx
      have hQy' : Qy ∈ dyadicCubesMeeting δ A1 := by
        rw [←hQs_coe] <;> exact hQy
      rcases hQx'.1 with ⟨kx, hkx⟩
      rcases hQy'.1 with ⟨ky, hky⟩
      have hpx_in : (choose_point Qx) 0 ∈ Set.Ico (δ * (kx 0 : ℝ)) (δ * ((kx 0 : ℝ) + 1)) := by
        have h : choose_point Qx ∈ Qx := (hchoose_in Qx hQx).1
        have h_fn : choose_point Qx = choose_point (dyadicCube δ kx) := by rw [hkx]
        have h' : choose_point (dyadicCube δ kx) ∈ dyadicCube δ kx := by
          rw [hkx] at h
          exact h
        rw [h_fn]
        exact h' 0
      have hpy_in : (choose_point Qy) 0 ∈ Set.Ico (δ * (ky 0 : ℝ)) (δ * ((ky 0 : ℝ) + 1)) := by
        have h : choose_point Qy ∈ Qy := (hchoose_in Qy hQy).1
        have h_fn : choose_point Qy = choose_point (dyadicCube δ ky) := by rw [hky]
        have h' : choose_point (dyadicCube δ ky) ∈ dyadicCube δ ky := by
          rw [hky] at h
          exact h
        rw [h_fn]
        exact h' 0
      have h_cube_x : cubeOf δ ((choose_point Qx) 0) = Qx := by
        have h_eq : cubeOf δ ((choose_point Qx) 0) = dyadicCube δ kx := cubeOf_eq hδ_pos hpx_in
        rw [h_eq, hkx.symm]
      have h_cube_y : cubeOf δ ((choose_point Qy) 0) = Qy := by
        have h_eq : cubeOf δ ((choose_point Qy) 0) = dyadicCube δ ky := cubeOf_eq hδ_pos hpy_in
        rw [h_eq, hky.symm]
      have h_Qx_eq_Qy : Qx = Qy := by
        rw [←h_cube_x, ←h_cube_y]
        exact h_eq
      have h_points_eq : choose_point Qx = choose_point Qy := by
        rw [h_Qx_eq_Qy]
      exact congr_arg (fun p : EuclideanSpace ℝ (Fin 1) => p 0) h_points_eq

    refine ⟨A_fin, hA_fin_sub, h_one_per_cube, ?_⟩
    rw [hA_fin_card, h_points_card]
    exact h_final

/-- Reverse: a finset with one point per δ-cube gives a covering lower bound. -/
lemma covering_from_finset {δ : ℝ} (hδ_pos : 0 < δ)
    {A : Set ℝ} {A_fin : Finset ℝ}
    (hA_fin_sub : (A_fin : Set ℝ) ⊆ A)
    (h_one_per_cube : Set.InjOn (cubeOf δ) (A_fin : Set ℝ)) :
    Nreal δ A ≥ (A_fin.card : ENNReal) := by
  let A1 := realLineCopy A
  -- For each x ∈ A_fin, cubeOf δ x is a dyadic cube meeting A
  let cubes_of : Finset (Set (EuclideanSpace ℝ (Fin 1))) :=
    Finset.image (cubeOf δ) A_fin

  have h_cubes_meet : ∀ Q ∈ cubes_of, Q ∈ dyadicCubesMeeting δ A1 := by
    intro Q hQ
    rcases Finset.mem_image.mp hQ with ⟨x, hx, rfl⟩
    have hx_A : x ∈ A := hA_fin_sub hx
    have h1 : cubeOf δ x ∈ dyadicCubes 1 δ := by
      refine ⟨fun _ : Fin 1 => Int.floor (x / δ), rfl⟩
    have h2 : (cubeOf δ x ∩ A1).Nonempty := by
      let f : Fin 1 → ℝ := fun (_ : Fin 1) => x
      let p : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 (Fin 1 → ℝ)).symm f
      have hp0 : p 0 = x := by
        have h_apply : ((WithLp.equiv 2 (Fin 1 → ℝ)).symm f) 0 = f 0 := by
          rfl
        rw [h_apply]
        <;> rfl
      have hp_cube : p ∈ cubeOf δ x := by
        have hp_in_line : p ∈ realLineCopy {x} := by
          simp [realLineCopy, hp0]
        exact mem_cubeOf hδ_pos x hp_in_line
      have hp_A1 : p ∈ A1 := by
        have h_p0_A : p 0 ∈ A := by
          rw [hp0] <;> exact hx_A
        have h : p ∈ realLineCopy A := by
          simpa [realLineCopy] using h_p0_A
        exact h
      exact ⟨p, hp_cube, hp_A1⟩
    exact ⟨h1, h2⟩

  have h_inj : Set.InjOn (cubeOf δ) (A_fin : Set ℝ) := h_one_per_cube
  have h_card_image : cubes_of.card = A_fin.card :=
    Finset.card_image_of_injOn h_inj

  have h_sub : (cubes_of : Set _) ⊆ dyadicCubesMeeting δ A1 := by
    intro Q hQ
    exact h_cubes_meet Q hQ
  have h_encard_coe : (↑cubes_of : Set (Set (EuclideanSpace ℝ (Fin 1)))).encard = ↑(cubes_of.card) := by
    simp
  have h_encard_le : ↑(cubes_of.card) ≤ (dyadicCubesMeeting δ A1).encard := by
    rw [←h_encard_coe]
    exact Set.encard_mono h_sub
  have h_card_le : (cubes_of.card : ENNReal) ≤ Nreal δ A := by
    simpa [Nreal, dyadicCoveringNumber] using ENat.toENNReal_mono h_encard_le
  calc Nreal δ A
    ≥ (cubes_of.card : ENNReal) := h_card_le
  _ = (A_fin.card : ENNReal) := by rw [h_card_image]

end robust_projection
