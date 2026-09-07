module

/-
# Cube-Family T_y Aggregation

Phase 0 aggregation over cube families (without Appendix strip restriction).

Given, for each x ∈ X_y, a family Cz(x,y) of dyadic δ-cubes in parameter space
such that:
- Each union ⋃₀ Cz(x,y) is a (δ,s,C)-set
- Approximate incidence: each cube contains p with |x - (p0*y+p1)| ≤ 2δ
- Overlap: each cube appears in at most Kov families
- Size: each family has ≤ C·δ^{-s} cubes

Then the global union ⋃₀ (⋃_{x∈X_y} Cz(x,y)) is a (δ,2s,7·Kov·C⁴)-set.

This removes the `Pz ⊂ appendixParameterStrip` premise by working directly
with dyadic parameter cubes instead of Appendix-A tubes.

## Whiteprint node
`phase0_cube_family_aggregation`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.ProductLikeProof
public import MyLeanRepo.ProductLikeIncidence.Phase0.CubeUnion
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open ProductLikeIncidence ENNReal Set Bornology Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- For a family C of distinct dyadic δ-cubes, the δ-covering number of their
union equals the cardinality of C. -/
lemma cubeFamilyCoveringEqCard {δ : ℝ} (hδ : 0 < δ)
    {C : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hC : C ⊆ dyadicCubes 2 δ) :
    dyadicCoveringNumber δ (⋃₀ C) = C.encard := by
  have h1 : dyadicCubesMeeting δ (⋃₀ C) = C := by
    ext Q
    simp only [dyadicCubesMeeting, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hQ_dyadic, hQ_meet⟩
      rcases hQ_meet with ⟨p, hpQ, hpC⟩
      rcases hpC with ⟨Q', hQ'_in_C, hpQ'⟩
      have hQ'_dyadic : Q' ∈ dyadicCubes 2 δ := hC hQ'_in_C
      have h_inter : (Q ∩ Q').Nonempty := ⟨p, hpQ, hpQ'⟩
      rcases hQ_dyadic with ⟨k, hk⟩
      rcases hQ'_dyadic with ⟨k', hk'⟩
      have h_inter2 : (dyadicCube δ k ∩ dyadicCube δ k').Nonempty := by
        rw [←hk, ←hk']
        exact h_inter
      have h_k_eq : k = k' := dyadic_cube_disjoint_or_equal hδ h_inter2
      have hQ_eq : Q = Q' := by
        rw [hk, hk', h_k_eq]
      rw [hQ_eq]
      exact hQ'_in_C
    · intro hQ_in_C
      have hQ_dyadic : Q ∈ dyadicCubes 2 δ := hC hQ_in_C
      have hQ_nonempty : Q.Nonempty := by
        rcases hQ_dyadic with ⟨k, rfl⟩
        let p : EuclideanSpace ℝ (Fin 2) :=
          (WithLp.equiv 2 (Fin 2 → ℝ)).symm fun i => δ * (k i : ℝ)
        have hp : p ∈ dyadicCube δ k := by
          intro i
          have hpi : p i = δ * (k i : ℝ) := by simp [p]
          rw [hpi]
          have h1 : δ * (k i : ℝ) ≤ δ * (k i : ℝ) := by rfl
          have h2 : δ * (k i : ℝ) < δ * ((k i : ℝ) + 1) := by
            have h3 : 0 < δ := hδ
            have h4 : (k i : ℝ) < (k i : ℝ) + 1 := by linarith
            exact mul_lt_mul_of_pos_left h4 h3
          exact ⟨h1, h2⟩
        exact ⟨p, hp⟩
      rcases hQ_nonempty with ⟨p, hpQ⟩
      have hQ_meet : (Q ∩ ⋃₀ C).Nonempty :=
        ⟨p, hpQ, ⟨Q, hQ_in_C, hpQ⟩⟩
      exact ⟨hQ_dyadic, hQ_meet⟩
  have h2 : dyadicCoveringNumber δ (⋃₀ C) = (dyadicCubesMeeting δ (⋃₀ C)).encard := by rfl
  rw [h2, h1]

/-- Cube-family version of `T_y_is_delta_2s_set_approx`.

Works directly with dyadic parameter cubes instead of Appendix-A tubes,
removing the `Pz ⊂ appendixParameterStrip` premise.

Given for each x ∈ X_y a family Cz x of dyadic δ-cubes such that:
- Each union ⋃₀ Cz x is a (δ,s,C)-set
- Approximate incidence: each cube Q ∈ Cz x contains p with |x - (p0*y+p1)| ≤ 2δ
- Overlap: each cube appears in at most Kov families
- Size: each family has ≤ C·δ^{-s} cubes

Then the global union ⋃₀ (⋃_{x∈X_y} Cz x) is a (δ,2s,7·Kov·C⁴)-set. -/
lemma cube_family_T_y_is_delta_2s_set {δ s C : ℝ} {Kov : ℕ} {y : ℝ} {X_y : Set ℝ}
    {Cz : ℝ → Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hs_nonneg : 0 ≤ s) (hs_le_one : s ≤ 1) (hC_pos : 0 < C)
    (hKov_pos : 1 ≤ Kov)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hX_grid : X_y ⊆ productLikeIntegerGrid δ)
    (hX_set : IsProductLikeRealDeltaSCSet δ s C X_y)
    (hCz_sub : ∀ x ∈ X_y, Cz x ⊆ dyadicCubes 2 δ)
    (hP_x_delta : ∀ x ∈ X_y, IsDeltaSCSet (d := 2) δ s C (⋃₀ (Cz x)))
    (h_approx : ∀ x ∈ X_y, ∀ Q ∈ Cz x,
      ∃ p ∈ Q, |x - (p 0 * y + p 1)| ≤ 2 * δ)
    (h_bounded_overlap : ∀ (Q : Set (EuclideanSpace ℝ (Fin 2))),
      Q ∈ (⋃ x ∈ X_y, Cz x) →
      let S := {x ∈ X_y | Q ∈ Cz x}
      S.Finite ∧ S.encard ≤ Kov)
    (h_card : ∀ x ∈ X_y,
      ENat.toENNReal (Cz x).encard ≤ ENNReal.ofReal (C * δ^(-s))) :
    IsDeltaSCSet (d := 2) δ (2 * s) (7 * (Kov : ℝ) * C^4)
      (⋃₀ (⋃ x ∈ X_y, Cz x)) := by
  classical
  let U : Set (Set (EuclideanSpace ℝ (Fin 2))) := ⋃ x ∈ X_y, Cz x
  let P_U : Set (EuclideanSpace ℝ (Fin 2)) := ⋃₀ U
  let P_x : ℝ → Set (EuclideanSpace ℝ (Fin 2)) := fun x => ⋃₀ (Cz x)
  have hU_sub : U ⊆ dyadicCubes 2 δ := by
    intro Q hQ
    rcases Set.mem_iUnion₂.mp hQ with ⟨x, hx, hQx⟩
    exact hCz_sub x hx hQx
  have hX_bdd_real : Bornology.IsBounded X_y := by
    have h1 : Bornology.IsBounded (productLikeRealLineCopy X_y) := hX_set.1
    let f_proj : EuclideanSpace ℝ (Fin 1) → ℝ := fun p => p 0
    have h_lip : LipschitzWith 1 f_proj := by
      apply LipschitzWith.mk_one
      intro x y
      have h1 : |(x - y) 0| ≤ ‖x - y‖ := PiLp.norm_apply_le (x - y) 0
      have h2 : (x - y) 0 = x 0 - y 0 := by simp
      have h3 : dist (f_proj x) (f_proj y) = |x 0 - y 0| := by
        dsimp only [f_proj]; rw [Real.dist_eq] <;> rfl
      have h4 : dist x y = ‖x - y‖ := dist_eq_norm x y
      rw [h3, h4, ←h2]; exact h1
    have h2 : Bornology.IsBounded (f_proj '' productLikeRealLineCopy X_y) :=
      h_lip.isBounded_image h1
    have h3 : (fun (p : EuclideanSpace ℝ (Fin 1)) => p 0) '' productLikeRealLineCopy X_y = X_y := by
      ext x
      simp only [Set.mem_image, productLikeRealLineCopy, Set.mem_setOf_eq]
      constructor
      · rintro ⟨p, hp, rfl⟩
        have h5 : p 0 ∈ X_y := by simpa [productLikeRealLineCopy, realLineCopy] using hp
        exact h5
      · intro hx
        let f : Fin 1 → ℝ := fun _ => x
        let p : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 (Fin 1 → ℝ)).symm f
        have hp2 : p 0 = x := by
          have h_eq : (WithLp.equiv 2 (Fin 1 → ℝ)) p = f :=
            (WithLp.equiv 2 (Fin 1 → ℝ)).apply_symm_apply f
          have h4 : ((WithLp.equiv 2 (Fin 1 → ℝ)) p) 0 = p 0 := by rfl
          rw [← h4, h_eq] <;> simp [f]
        have h5 : p 0 ∈ X_y := by rw [hp2]; exact hx
        have hp1 : p ∈ productLikeRealLineCopy X_y := by
          simpa [productLikeRealLineCopy, realLineCopy] using h5
        exact ⟨p, hp1, hp2⟩
    rw [h3] at h2; exact h2
  have hX_nonempty : X_y.Nonempty := by
    have h1 : (productLikeRealLineCopy X_y).Nonempty := hX_set.2.1
    rcases h1 with ⟨p, hp⟩
    exact ⟨p 0, hp⟩
  have hX_fin : X_y.Finite := finite_bounded_grid_subset hδ hX_grid hX_bdd_real
  have hCz_fin : ∀ x ∈ X_y, (Cz x).Finite := by
    intro x hx
    have h3 : dyadicCoveringNumber δ (P_x x) < ⊤ :=
      dyadicCoveringNumber_lt_top hδ (hP_x_delta x hx).1
    have h4 : dyadicCoveringNumber δ (P_x x) = (Cz x).encard :=
      cubeFamilyCoveringEqCard hδ (hCz_sub x hx)
    rw [h4] at h3
    exact Set.encard_lt_top_iff.mp h3
  have hU_fin : U.Finite := Set.Finite.biUnion hX_fin hCz_fin
  have hP_U_card : dyadicCoveringNumber δ P_U = U.encard :=
    cubeFamilyCoveringEqCard hδ hU_sub
  let X_finset : Finset ℝ := hX_fin.toFinset
  have hP_U_bdd : Bornology.IsBounded P_U := by
    have h1 : P_U = ⋃ x ∈ X_y, P_x x := by
      ext z
      simp only [P_U, P_x, U, Set.mem_sUnion, Set.mem_iUnion]
      constructor
      · rintro ⟨Q, ⟨x, hx, hQx⟩, hzQ⟩
        exact ⟨x, hx, ⟨Q, hQx, hzQ⟩⟩
      · rintro ⟨x, hx, Q, hQx, hzQ⟩
        exact ⟨Q, ⟨x, hx, hQx⟩, hzQ⟩
    rw [h1]
    have h2 : ∀ (x : ℝ), x ∈ X_y → Bornology.IsBounded (P_x x) := by
      intro x hx
      exact (hP_x_delta x hx).1
    have h3 : Bornology.IsBounded (⋃ x ∈ X_y, P_x x) := by
      let S : Set (Set (EuclideanSpace ℝ (Fin 2))) := P_x '' X_y
      have hS_fin : S.Finite := Set.Finite.image _ hX_fin
      have h_eq : (⋃ x ∈ X_y, P_x x) = ⋃₀ S := by
        ext z
        simp only [S, Set.mem_iUnion, Set.mem_sUnion, Set.mem_image]
        constructor
        · rintro ⟨x, hx, hz⟩
          exact ⟨P_x x, ⟨x, hx, rfl⟩, hz⟩
        · rintro ⟨T, ⟨x, hx, rfl⟩, hz⟩
          exact ⟨x, hx, hz⟩
      rw [h_eq]
      rw [Bornology.isBounded_sUnion hS_fin]
      intro T hT
      rcases hT with ⟨x, hx, rfl⟩
      exact h2 x hx
    exact h3
  have hP_U_nonempty : P_U.Nonempty := by
    rcases hX_nonempty with ⟨x, hx⟩
    have h1 : (P_x x).Nonempty := (hP_x_delta x hx).2.1
    rcases h1 with ⟨p, hp⟩
    have h2 : p ∈ P_U := by
      have h3 : P_U = ⋃ x ∈ X_y, P_x x := by
        ext z
        simp only [P_U, P_x, U, Set.mem_sUnion, Set.mem_iUnion]
        constructor
        · rintro ⟨Q, ⟨x, hx, hQx⟩, hzQ⟩
          exact ⟨x, hx, ⟨Q, hQx, hzQ⟩⟩
        · rintro ⟨x, hx, Q, hQx, hzQ⟩
          exact ⟨Q, ⟨x, hx, hQx⟩, hzQ⟩
      rw [h3]
      exact Set.mem_iUnion₂.mpr ⟨x, hx, hp⟩
    exact ⟨p, h2⟩
  let Cz_finset (x : ℝ) : Finset (Set (EuclideanSpace ℝ (Fin 2))) :=
    if h : x ∈ X_y then (hCz_fin x h).toFinset else ∅
  let U_finset : Finset (Set (EuclideanSpace ℝ (Fin 2))) :=
    X_finset.biUnion Cz_finset
  have hU_finset_eq : (U_finset : Set _) = U := by
    ext Q
    simp only [U_finset, U, Cz_finset, X_finset, Finset.mem_coe, Finset.mem_biUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, hQ⟩
      have hx' : x ∈ X_y := by simpa [X_finset] using hx
      have hQ' : Q ∈ Cz x := by simpa [Cz_finset, hx'] using hQ
      exact ⟨x, hx', hQ'⟩
    · rintro ⟨x, hx, hQ⟩
      refine ⟨x, by simpa [X_finset] using hx, ?_⟩
      simpa [Cz_finset, hx] using hQ
  have hX_lower : ENat.toENNReal X_y.encard ≥ ENNReal.ofReal (δ^(-s) / C) := by
    have h1 := deltaSCSet_card_lower_bound hX_set
    rw [realLineCoveringEqCard hδ hX_grid] at h1
    exact h1
  have hCz_lower : ∀ x ∈ X_y, ENat.toENNReal (Cz x).encard ≥ ENNReal.ofReal (δ^(-s) / C) := by
    intro x hx
    have h1 := deltaSCSet_card_lower_bound (hP_x_delta x hx)
    rw [cubeFamilyCoveringEqCard hδ (hCz_sub x hx)] at h1
    exact h1
  let I_inc : Finset (ℝ × Set (EuclideanSpace ℝ (Fin 2))) :=
    X_finset.biUnion (fun x => ({x} : Finset ℝ) ×ˢ Cz_finset x)
  have hI_card : I_inc.card = ∑ x ∈ X_finset, (Cz_finset x).card := by
    rw [Finset.card_biUnion]
    · simp [I_inc, Finset.card_product, Finset.card_singleton]
    · intro a _ b _ hab
      apply Finset.disjoint_left.mpr
      intro p hp1 hp2
      have h1 : p.1 ∈ ({a} : Finset ℝ) := (Finset.mem_product.mp hp1).1
      have h1' : p.1 = a := by simpa using h1
      have h2 : p.1 ∈ ({b} : Finset ℝ) := (Finset.mem_product.mp hp2).1
      have h2' : p.1 = b := by simpa using h2
      rw [h1'] at h2'; exact hab h2'
  have h_img : I_inc.image (fun p : ℝ × Set (EuclideanSpace ℝ (Fin 2)) => p.2) = U_finset := by
    ext Q
    simp only [Finset.mem_image, I_inc, Finset.mem_biUnion, U_finset]
    constructor
    · rintro ⟨p, ⟨x, hx, hp⟩, rfl⟩
      have hQ : p.2 ∈ Cz_finset x := (Finset.mem_product.mp hp).2
      exact ⟨x, hx, hQ⟩
    · rintro ⟨x, hx, hQ⟩
      have h_mem : (x, Q) ∈ ({x} : Finset ℝ) ×ˢ Cz_finset x := by
        simp [hQ]
      exact ⟨(x, Q), ⟨x, hx, h_mem⟩, rfl⟩
  have hI_le : I_inc.card ≤ Kov * U_finset.card := by
    have h_disj : ∀ Q1 ∈ U_finset, ∀ Q2 ∈ U_finset, Q1 ≠ Q2 →
        Disjoint (I_inc.filter (fun p => p.2 = Q1)) (I_inc.filter (fun p => p.2 = Q2)) := by
      intro Q1 _ Q2 _ hne
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 : p.2 = Q1 := (Finset.mem_filter.mp hp1).2
      have h2 : p.2 = Q2 := (Finset.mem_filter.mp hp2).2
      rw [h1] at h2
      exact hne h2
    have h_union : I_inc = U_finset.biUnion (fun Q => I_inc.filter (fun p => p.2 = Q)) := by
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hp
        have hQ : p.2 ∈ U_finset := by
          rw [← h_img]
          exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
        exact ⟨p.2, hQ, hp, rfl⟩
      · rintro ⟨Q, hQ, hp, _⟩
        exact hp
    have h_sum : I_inc.card = ∑ Q ∈ U_finset, (I_inc.filter (fun p => p.2 = Q)).card := by
      have h_card : (U_finset.biUnion (fun Q => I_inc.filter (fun p => p.2 = Q))).card =
          ∑ Q ∈ U_finset, (I_inc.filter (fun p => p.2 = Q)).card :=
        Finset.card_biUnion h_disj
      exact (congr_arg Finset.card h_union).trans h_card
    rw [h_sum]
    have h_each : ∀ Q ∈ U_finset, (I_inc.filter (fun p => p.2 = Q)).card ≤ Kov := by
      intro Q hQ
      let S : Set ℝ := {x ∈ X_y | Q ∈ Cz x}
      have hS_fin : S.Finite := hX_fin.subset (fun x hx => hx.1)
      let S' : Finset ℝ := hS_fin.toFinset
      have hQ_in_U : Q ∈ U := by
        rw [← hU_finset_eq]; exact hQ
      have hS_encard : S.encard ≤ Kov := (h_bounded_overlap Q hQ_in_U).2
      have hS'_card : S'.card ≤ Kov := by
        have h_eq : (S' : Set ℝ) = S := by simp [S']
        have h : S.encard = ↑S'.card := by
          rw [← h_eq]
          exact encard_coe_eq_coe_finsetCard S'
        rw [h] at hS_encard
        exact_mod_cast hS_encard
      let fiber_img : Finset (ℝ × Set (EuclideanSpace ℝ (Fin 2))) :=
        S'.image (fun x => (x, Q))
      have h_fiber_eq : I_inc.filter (fun p => p.2 = Q) = fiber_img := by
        ext p
        simp only [Finset.mem_filter, fiber_img, Finset.mem_image]
        constructor
        · rintro ⟨hp, h_eq⟩
          rcases Finset.mem_biUnion.mp hp with ⟨x', hx', h6'⟩
          have h_eq1 : p.1 = x' := by
            have h : p.1 ∈ ({x'} : Finset ℝ) := (Finset.mem_product.mp h6').1
            simpa using h
          have h8 : x' ∈ X_y := by simpa [X_finset] using hx'
          have h9 : p.2 ∈ Cz_finset x' := (Finset.mem_product.mp h6').2
          have h9' : Q ∈ Cz_finset x' := by rw [← h_eq]; exact h9
          have h10 : x' ∈ S' := by
            have h101 : x' ∈ S := by
              simp only [S, Set.mem_setOf_eq]
              exact ⟨h8, by simpa [Cz_finset, h8] using h9'⟩
            simpa [S'] using h101
          have h11 : (x', Q) = p := by
            ext <;> simp [h_eq1, h_eq]
          exact ⟨x', h10, h11⟩
        · rintro ⟨x, hx, rfl⟩
          have hxS : x ∈ S := by simpa [S'] using hx
          have hxX : x ∈ X_y := hxS.1
          have hQ' : Q ∈ Cz x := hxS.2
          have h11 : Q ∈ Cz_finset x := by simpa [Cz_finset, hxX] using hQ'
          have h_prod : (x, Q) ∈ ({x} : Finset ℝ) ×ˢ Cz_finset x := by
            simp [h11]
          have h' : x ∈ X_finset := by simpa [X_finset] using hxX
          have h12 : (x, Q) ∈ I_inc := by
            simp only [I_inc, Finset.mem_biUnion]
            exact ⟨x, h', h_prod⟩
          exact ⟨h12, rfl⟩
      rw [h_fiber_eq]
      have h_inj : Function.Injective (fun x : ℝ => (x, Q)) := by
        intro x y h; simpa using h
      have h_card : fiber_img.card = S'.card := by
        have h_eq : fiber_img = S'.image (fun x : ℝ => (x, Q)) := by rfl
        rw [h_eq]
        exact Finset.card_image_of_injective S' h_inj
      rw [h_card]
      exact hS'_card
    have h_sum3 : ∑ Q ∈ U_finset, (I_inc.filter (fun p => p.2 = Q)).card ≤ ∑ Q ∈ U_finset, Kov :=
      Finset.sum_le_sum h_each
    have h_final : ∑ Q ∈ U_finset, (I_inc.filter (fun p => p.2 = Q)).card ≤ Kov * U_finset.card := by
      have h : ∑ Q ∈ U_finset, (I_inc.filter (fun p => p.2 = Q)).card ≤ ∑ Q ∈ U_finset, (Kov : ℕ) := h_sum3
      have h2 : ∑ Q ∈ U_finset, (Kov : ℕ) = Kov * U_finset.card := by
        rw [Finset.sum_const] <;> ring
      linarith
    exact h_final
  have h_sum_lower : ((∑ x ∈ X_finset, (Cz_finset x).card : ℝ)) ≥
      (X_finset.card : ℝ) * (δ^(-s) / C) := by
    have h_each2 : ∀ x ∈ X_finset, ((Cz_finset x).card : ℝ) ≥ (δ^(-s) / C) := by
      intro x hx
      have hx' : x ∈ X_y := by simpa [X_finset] using hx
      have h_coe : (Cz_finset x : Set _) = Cz x := by
        have hif : Cz_finset x = (hCz_fin x hx').toFinset := by
          unfold Cz_finset
          rw [dif_pos hx']
        rw [hif]
        exact Set.Finite.coe_toFinset (hCz_fin x hx')
      have h_encard : (Cz x).encard = ↑(Cz_finset x).card := by
        have h9 : (Cz x).encard = (↑(Cz_finset x) : Set (Set (EuclideanSpace ℝ (Fin 2)))).encard := by
          rw [← h_coe]
        rw [h9]
        exact Set.encard_coe_eq_coe_finsetCard (Cz_finset x)
      have h4 : ENat.toENNReal (Cz x).encard = (↑(Cz_finset x).card : ENNReal) := by
        rw [h_encard] <;> simp
      have h5 : (↑(Cz_finset x).card : ENNReal) ≥ ENNReal.ofReal (δ^(-s) / C) := by
        rw [← h4]
        exact hCz_lower x hx'
      have h_pos_card : 0 ≤ ((Cz_finset x).card : ℝ) := Nat.cast_nonneg _
      have h_coe' : (↑(Cz_finset x).card : ENNReal) = ENNReal.ofReal ((Cz_finset x).card : ℝ) :=
        (ENNReal.ofReal_natCast (Cz_finset x).card).symm
      have h6 : ENNReal.ofReal (δ^(-s) / C) ≤ ENNReal.ofReal ((Cz_finset x).card : ℝ) := by
        have h7 : ENNReal.ofReal ((Cz_finset x).card : ℝ) = (↑(Cz_finset x).card : ENNReal) := h_coe'.symm
        rw [h7]
        exact h5
      have h_pos_ds : 0 ≤ δ ^ (-s) := Real.rpow_nonneg (by linarith) _
      have h_pos : 0 ≤ δ ^ (-s) / C := by
        exact div_nonneg h_pos_ds (by linarith)
      exact (ENNReal.ofReal_le_ofReal_iff h_pos_card).mp h6
    have h : ((∑ x ∈ X_finset, (Cz_finset x).card : ℝ)) ≥ ∑ x ∈ X_finset, (δ^(-s) / C) :=
      Finset.sum_le_sum h_each2
    rw [Finset.sum_const] at h
    simpa using h
  have h_double_count : (Kov : ENNReal) * ENat.toENNReal U.encard ≥
      ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s) / C) := by
    have h1 : (I_inc.card : ℝ) ≤ (Kov : ℝ) * (U_finset.card : ℝ) := by exact_mod_cast hI_le
    have h2 : (I_inc.card : ℝ) = ∑ x ∈ X_finset, ((Cz_finset x).card : ℝ) := by
      rw [hI_card, Nat.cast_sum]
    have h_sum_lower2 : (I_inc.card : ℝ) ≥ (X_finset.card : ℝ) * (δ^(-s) / C) := by
      rw [h2]
      exact h_sum_lower
    have h3 : (X_finset.card : ℝ) * (δ^(-s) / C) ≤ (Kov : ℝ) * (U_finset.card : ℝ) := by
      linarith [h_sum_lower2, h1]
    have hX_eq : ENat.toENNReal X_y.encard = (↑X_finset.card : ENNReal) := by
      have h' : (↑X_finset : Set ℝ) = X_y := hX_fin.coe_toFinset
      have h : X_y.encard = ↑X_finset.card := by
        rw [← h']
        exact Set.encard_coe_eq_coe_finsetCard X_finset
      exact_mod_cast h
    have hU_eq : ENat.toENNReal U.encard = (↑U_finset.card : ENNReal) := by
      have h' : (↑U_finset : Set _) = U := hU_finset_eq
      have h : U.encard = ↑U_finset.card := by
        rw [← h']
        exact Set.encard_coe_eq_coe_finsetCard U_finset
      exact_mod_cast h
    rw [hX_eq, hU_eq]
    have h_pos3 : 0 ≤ (X_finset.card : ℝ) * (δ^(-s) / C) := by positivity
    have h3' : ENNReal.ofReal ((X_finset.card : ℝ) * (δ^(-s) / C)) ≤
        ENNReal.ofReal ((Kov : ℝ) * (U_finset.card : ℝ)) := ENNReal.ofReal_le_ofReal h3
    have h5 : ENNReal.ofReal ((X_finset.card : ℝ) * (δ^(-s) / C)) =
        (↑X_finset.card : ENNReal) * ENNReal.ofReal (δ^(-s) / C) := by
      have h_pos1 : 0 ≤ (X_finset.card : ℝ) := by positivity
      have h_pos2 : 0 ≤ δ^(-s) / C := by positivity
      have h_coe : (↑X_finset.card : ENNReal) = ENNReal.ofReal (X_finset.card : ℝ) := by norm_cast
      have h_mul : ENNReal.ofReal ((X_finset.card : ℝ) * (δ^(-s) / C)) =
          ENNReal.ofReal (X_finset.card : ℝ) * ENNReal.ofReal (δ^(-s) / C) :=
        ENNReal.ofReal_mul h_pos1
      calc
        ENNReal.ofReal ((X_finset.card : ℝ) * (δ^(-s) / C))
          = ENNReal.ofReal (X_finset.card : ℝ) * ENNReal.ofReal (δ^(-s) / C) := h_mul
        _ = (↑X_finset.card : ENNReal) * ENNReal.ofReal (δ^(-s) / C) := by rw [h_coe]
    have h6 : ENNReal.ofReal ((Kov : ℝ) * (U_finset.card : ℝ)) =
        (Kov : ENNReal) * (↑U_finset.card : ENNReal) := by
      have h_pos1 : 0 ≤ (Kov : ℝ) := by positivity
      have h_pos2 : 0 ≤ (U_finset.card : ℝ) := by positivity
      have h_coe : (↑U_finset.card : ENNReal) = ENNReal.ofReal (U_finset.card : ℝ) := by norm_cast
      have h_mul : ENNReal.ofReal ((Kov : ℝ) * (U_finset.card : ℝ)) =
          ENNReal.ofReal (Kov : ℝ) * ENNReal.ofReal (U_finset.card : ℝ) :=
        ENNReal.ofReal_mul h_pos1
      have h_coe3 : (Kov : ENNReal) = ENNReal.ofReal (Kov : ℝ) := by norm_cast
      calc
        ENNReal.ofReal ((Kov : ℝ) * (U_finset.card : ℝ))
          = ENNReal.ofReal (Kov : ℝ) * ENNReal.ofReal (U_finset.card : ℝ) := h_mul
        _ = (Kov : ENNReal) * (↑U_finset.card : ENNReal) := by
            rw [h_coe3, h_coe] <;> ring
    rw [h5, h6] at h3'
    exact h3'
  have h_main_bound : ∀ (r : ℝ) (Q : Set (EuclideanSpace ℝ (Fin 2))),
      r ∈ dyadicScales → Q ∈ dyadicCubes 2 r → δ ≤ r → r ≤ 1 →
      ENat.toENNReal (dyadicCoveringNumber δ (P_U ∩ Q)) ≤
        ENNReal.ofReal (7 * (Kov : ℝ) * C^4) * ENat.toENNReal (dyadicCoveringNumber δ P_U) *
          ENNReal.ofReal (r ^ (2 * s)) := by
    intro r Q hr_dyadic hQ_dyadic hδ_le_r hr_le_one
    rcases hQ_dyadic with ⟨k, hk⟩
    have hQ_eq : Q = dyadicCube r k := hk
    let lo : ℝ := r * (k 0 : ℝ) * y + r * (k 1 : ℝ)
    let hi : ℝ := r * ((k 0 : ℝ) + 1) * y + r * ((k 1 : ℝ) + 1)
    let lo' : ℝ := lo - 2 * δ
    let hi' : ℝ := hi + 2 * δ
    let I_real : Set ℝ := Set.Icc lo' hi'
    have hr_pos : 0 < r := dyadicScales_pos hr_dyadic
    have h_len : hi' - lo' ≤ 6 * r := by
      dsimp only [lo', hi', lo, hi]
      have h_y : y ≤ 1 := hy1
      have hδ_le_r2 : 2 * δ ≤ 2 * r := by gcongr
      nlinarith
    have hN : ∃ (N : ℕ), r = (N : ℝ) * δ := dyadicScales_ratio_nat hδ_dyadic hr_dyadic hδ_le_r
    have h_proj : ∀ (x : ℝ), x ∈ X_y → (P_x x ∩ Q).Nonempty → x ∈ I_real := by
      intro x hx hnonempty
      rcases hnonempty with ⟨p, hpP, hpQ⟩
      have h_exists_Q0 : ∃ (Q0 : Set (EuclideanSpace ℝ (Fin 2))), Q0 ∈ Cz x ∧ p ∈ Q0 := by
        simpa [P_x, Set.mem_sUnion] using hpP
      rcases h_exists_Q0 with ⟨Q0, hQ0_in, hp_in_Q0⟩
      have hQ0_dyadic : Q0 ∈ dyadicCubes 2 δ := hCz_sub x hx hQ0_in
      rcases hQ0_dyadic with ⟨kQ, hQ0_eq⟩
      have h_inter : (Q0 ∩ Q).Nonempty := ⟨p, hp_in_Q0, hpQ⟩
      have h_inter2 : (dyadicCube δ kQ ∩ dyadicCube r k).Nonempty := by
        rw [← hQ0_eq, ← hQ_eq]
        exact h_inter
      have hr_pos : 0 < r := dyadicScales_pos hr_dyadic
      have h_contain1 : dyadicCube δ kQ ⊆ dyadicCube r k := dyadicCubeContainment hδ hr_pos hN h_inter2
      have h_contain : Q0 ⊆ Q := by
        rw [hQ0_eq, hQ_eq]
        exact h_contain1
      rcases h_approx x hx Q0 hQ0_in with ⟨p', hp'_in_Q0, h_ineq⟩
      have h_p'_in_Q : p' ∈ Q := h_contain hp'_in_Q0
      have h_p'_in_cube : p' ∈ dyadicCube r k := by
        rw [← hQ_eq]; exact h_p'_in_Q
      have h1 : lo ≤ p' 0 * y + p' 1 := by
        have h11 : r * (k 0 : ℝ) ≤ p' 0 := (h_p'_in_cube 0).1
        have h12 : r * (k 1 : ℝ) ≤ p' 1 := (h_p'_in_cube 1).1
        dsimp only [lo]
        nlinarith [hy0]
      have h2 : p' 0 * y + p' 1 ≤ hi := by
        have h21 : p' 0 < r * ((k 0 : ℝ) + 1) := (h_p'_in_cube 0).2
        have h22 : p' 1 < r * ((k 1 : ℝ) + 1) := (h_p'_in_cube 1).2
        dsimp only [hi]
        nlinarith [hy0, hy1]
      have h3 : |x - (p' 0 * y + p' 1)| ≤ 2 * δ := h_ineq
      have h4 : x ≥ p' 0 * y + p' 1 - 2 * δ := by
        linarith [abs_le.mp h3]
      have h5 : x ≤ p' 0 * y + p' 1 + 2 * δ := by
        linarith [abs_le.mp h3]
      have h6 : x ≥ lo' := by dsimp only [lo']; linarith
      have h7 : x ≤ hi' := by dsimp only [hi']; linarith
      exact ⟨h6, h7⟩
    let k_lo : ℤ := ⌊lo' / r⌋
    let k_hi : ℤ := ⌊hi' / r⌋
    let Kint : Finset ℤ := Finset.Icc k_lo k_hi
    have hK_card : Kint.card ≤ 7 := by
      have h1 : k_hi - k_lo ≤ 6 := by
        by_contra h
        have h' : k_hi - k_lo ≥ 7 := by linarith
        have h2 : (k_hi : ℝ) ≥ (k_lo : ℝ) + 7 := by
          have h21 : (k_hi - k_lo : ℝ) ≥ 7 := by exact_mod_cast h'
          linarith
        have h3 : hi' / r ≥ (k_hi : ℝ) := Int.floor_le (hi' / r)
        have h4 : lo' / r < (k_lo : ℝ) + 1 := Int.lt_floor_add_one (lo' / r)
        have h5 : hi' / r - lo' / r > 6 := by linarith
        have h6 : hi' / r - lo' / r ≤ 6 := by
          have h7 : hi' - lo' ≤ 6 * r := h_len
          have h8 : (hi' - lo') / r ≤ 6 := by
            have h81 : (hi' - lo') / r ≤ (6 * r) / r := by gcongr
            have h82 : (6 * r) / r = 6 := by field_simp [hr_pos.ne'] <;> ring
            rw [h82] at h81
            exact h81
          have h9 : (hi' - lo') / r = hi' / r - lo' / r := by ring
          linarith
        linarith
      simp [Kint, Finset.Icc_eq_empty_of_lt]
      <;> omega
    let J (k' : ℤ) : Set ℝ := Set.Ico (r * (k' : ℝ)) (r * ((k' : ℝ) + 1))
    have h_cover_I : I_real ⊆ ⋃ k' ∈ Kint, J k' := by
      intro x hx
      have h_x_in : lo' ≤ x ∧ x ≤ hi' := hx
      let k' : ℤ := ⌊x / r⌋
      have h_k'_in_K : k' ∈ Kint := by
        have h1 : k_lo ≤ k' := by
          have h2 : lo' ≤ x := h_x_in.1
          have h3 : lo' / r ≤ x / r := by gcongr
          have h4 : ⌊lo' / r⌋ ≤ ⌊x / r⌋ := Int.floor_mono h3
          exact h4
        have h2 : k' ≤ k_hi := by
          have h3 : x ≤ hi' := h_x_in.2
          have h4 : x / r ≤ hi' / r := by gcongr
          have h5 : ⌊x / r⌋ ≤ ⌊hi' / r⌋ := Int.floor_mono h4
          exact h5
        exact Finset.mem_Icc.mpr ⟨h1, h2⟩
      have h_x_in_J : x ∈ J k' := by
        dsimp only [J]
        have h1 : r * (k' : ℝ) ≤ x := by
          have h2 : (k' : ℝ) ≤ x / r := Int.floor_le (x / r)
          have h3 : r * (k' : ℝ) ≤ r * (x / r) := by gcongr
          have h4 : r * (x / r) = x := by field_simp [hr_pos.ne'] <;> ring
          rw [h4] at h3; exact h3
        have h5 : x < r * ((k' : ℝ) + 1) := by
          have h6 : x / r < (k' : ℝ) + 1 := Int.lt_floor_add_one (x / r)
          have h7 : r * (x / r) < r * ((k' : ℝ) + 1) := by gcongr
          have h8 : r * (x / r) = x := by field_simp [hr_pos.ne'] <;> ring
          rw [h8] at h7; exact h7
        exact ⟨h1, h5⟩
      exact Set.mem_iUnion₂.mpr ⟨k', h_k'_in_K, h_x_in_J⟩
    let S_set : Set ℝ := X_y ∩ I_real
    have hS_fin : S_set.Finite := hX_fin.subset (fun x hx => hx.1)
    let S_finset : Finset ℝ := hS_fin.toFinset
    have hS_eq : (S_finset : Set ℝ) = S_set := by simp [S_finset, S_set]
    have h_empty : ∀ x ∈ X_y, x ∉ I_real → P_x x ∩ Q = ∅ := by
      intro x hx hnx
      by_contra h
      have h' : (P_x x ∩ Q).Nonempty := Set.nonempty_iff_ne_empty.mpr h
      exact hnx (h_proj x hx h')
    have h_interval_bound : ∀ k' ∈ Kint,
        ENat.toENNReal (X_y ∩ J k').encard ≤
          ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s) := by
      intro k' _
      let Q1 : Set (EuclideanSpace ℝ (Fin 1)) := dyadicCube r (fun _ => k')
      have hQ1_dyadic : Q1 ∈ dyadicCubes 1 r := ⟨(fun _ => k'), rfl⟩
      have hX_delta : IsDeltaSCSet (d := 1) δ s C (productLikeRealLineCopy X_y) := hX_set
      have h_main := hX_delta.2.2.2.2.2.2.2.2 hr_dyadic hQ1_dyadic hδ_le_r hr_le_one
      have h_eq1 : productLikeRealLineCopy X_y ∩ Q1 = productLikeRealLineCopy (X_y ∩ J k') := by
        ext p
        simp only [productLikeRealLineCopy, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨h1, h2⟩
          have h3 : p 0 ∈ J k' := by
            simpa [Q1, J] using h2 0
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩
          have h3 : p ∈ Q1 := by
            simpa [dyadicCube, Q1, J] using h2
          exact ⟨h1, h3⟩
      rw [h_eq1] at h_main
      have h_card : dyadicCoveringNumber δ (productLikeRealLineCopy (X_y ∩ J k')) = (X_y ∩ J k').encard :=
        realLineCoveringEqCard hδ (fun x hx => hX_grid hx.1)
      rw [h_card] at h_main
      have h_X_card : dyadicCoveringNumber δ (productLikeRealLineCopy X_y) = X_y.encard :=
        realLineCoveringEqCard hδ hX_grid
      rw [h_X_card] at h_main
      exact h_main
    have h1_PU : P_U = ⋃ x ∈ X_y, P_x x := by
      ext z
      simp only [P_U, P_x, U, Set.mem_sUnion, Set.mem_iUnion]
      constructor
      · rintro ⟨Q, ⟨x, hx, hQx⟩, hzQ⟩
        exact ⟨x, hx, ⟨Q, hQx, hzQ⟩⟩
      · rintro ⟨x, hx, Q, hQx, hzQ⟩
        exact ⟨Q, ⟨x, hx, hQx⟩, hzQ⟩
    have h_union_eq : P_U ∩ Q = ⋃ x ∈ S_finset, P_x x ∩ Q := by
      rw [h1_PU]
      ext p
      simp only [Set.mem_inter_iff, Set.mem_iUnion]
      constructor
      · rintro ⟨h2, h3⟩
        rcases h2 with ⟨x, hx, hp⟩
        have h4 : x ∈ S_set := by
          have h5 : (P_x x ∩ Q).Nonempty := ⟨p, hp, h3⟩
          exact ⟨hx, h_proj x hx h5⟩
        have h6 : x ∈ S_finset := by
          have h7 : x ∈ (S_finset : Set ℝ) := by rw [hS_eq]; exact h4
          exact_mod_cast h7
        exact ⟨x, h6, hp, h3⟩
      · rintro ⟨x, hx, hp, hQ⟩
        have h7 : x ∈ S_set := by
          have h8 : x ∈ (S_finset : Set ℝ) := hx
          rw [hS_eq] at h8
          exact h8
        have h8 : x ∈ X_y := h7.1
        exact ⟨⟨x, h8, hp⟩, hQ⟩
    have h_bdd : ∀ x ∈ S_finset, Bornology.IsBounded (P_x x ∩ Q) := by
      intro x hx
      have hxS : x ∈ S_set := by
        have h : x ∈ (S_finset : Set ℝ) := hx
        rw [hS_eq] at h
        exact h
      have hx' : x ∈ X_y := hxS.1
      have h_bdd_Px : Bornology.IsBounded (P_x x) := (hP_x_delta x hx').1
      have h_sub : (P_x x ∩ Q) ⊆ (P_x x) := by
        intro z hz
        exact hz.1
      have h : Bornology.IsBounded (P_x x ∩ Q) :=
        Bornology.IsBounded.subset h_bdd_Px h_sub
      exact h
    have h_cover_union : ENat.toENNReal (dyadicCoveringNumber δ (P_U ∩ Q)) ≤
        ∑ x ∈ S_finset, ENat.toENNReal (dyadicCoveringNumber δ (P_x x ∩ Q)) := by
      rw [h_union_eq]
      exact dyadicCoveringNumber_iUnion_le S_finset (fun x => P_x x ∩ Q) h_bdd hδ
    have h_per_x : ∀ x ∈ S_finset, ENat.toENNReal (dyadicCoveringNumber δ (P_x x ∩ Q)) ≤
        ENNReal.ofReal (C^2 * δ^(-s) * r^s) := by
      intro x hx
      have hxS : x ∈ S_set := by
        have h : x ∈ (S_finset : Set ℝ) := hx
        rw [hS_eq] at h
        exact h
      have hx' : x ∈ X_y := hxS.1
      let Q2 : Set (EuclideanSpace ℝ (Fin 2)) := Q
      have hT_delta : IsDeltaSCSet (d := 2) δ s C (P_x x) := hP_x_delta x hx'
      have hT_cover : ∀ ⦃r' : ℝ⦄ ⦃Q' : Set (EuclideanSpace ℝ (Fin 2))⦄,
          r' ∈ dyadicScales → Q' ∈ dyadicCubes 2 r' → δ ≤ r' → r' ≤ 1 →
          ENat.toENNReal (dyadicCoveringNumber δ (P_x x ∩ Q')) ≤
            ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber δ (P_x x)) *
              ENNReal.ofReal (r' ^ s) := hT_delta.2.2.2.2.2.2.2.2
      have hQ_dyadic2 : Q ∈ dyadicCubes 2 r := by
        rw [hQ_eq]
        exact ⟨k, rfl⟩
      have h_main2 := hT_cover hr_dyadic hQ_dyadic2 hδ_le_r hr_le_one
      have h_card1 : dyadicCoveringNumber δ (P_x x) = (Cz x).encard :=
        cubeFamilyCoveringEqCard hδ (hCz_sub x hx')
      rw [h_card1] at h_main2
      have h_upper : ENat.toENNReal (Cz x).encard ≤ ENNReal.ofReal (C * δ^(-s)) := h_card x hx'
      calc
        ENat.toENNReal (dyadicCoveringNumber δ (P_x x ∩ Q2))
          ≤ ENNReal.ofReal C * ENat.toENNReal (Cz x).encard * ENNReal.ofReal (r ^ s) := h_main2
        _ ≤ ENNReal.ofReal C * ENNReal.ofReal (C * δ^(-s)) * ENNReal.ofReal (r ^ s) := by gcongr
        _ = ENNReal.ofReal (C^2 * δ^(-s) * r^s) := by
          have h_posC : 0 ≤ C := by positivity
          have h_posd : 0 ≤ δ^(-s) := by positivity
          have h_posr : 0 ≤ r ^ s := by positivity
          have h1 : ENNReal.ofReal (C * δ^(-s)) = ENNReal.ofReal C * ENNReal.ofReal (δ^(-s)) := by
            rw [ENNReal.ofReal_mul h_posC]
          rw [h1]
          have h_posC2 : 0 ≤ C^2 := by positivity
          have h_mul1 : ENNReal.ofReal (C^2 * δ^(-s) * r^s) =
              ENNReal.ofReal (C^2) * ENNReal.ofReal (δ^(-s)) * ENNReal.ofReal (r^s) := by
            rw [ENNReal.ofReal_mul (show 0 ≤ C^2 * δ^(-s) by positivity),
                ENNReal.ofReal_mul h_posC2] <;> ring
          have h_C2 : ENNReal.ofReal (C^2) = ENNReal.ofReal C * ENNReal.ofReal C := by
            rw [← ENNReal.ofReal_mul h_posC] <;> ring_nf
          rw [h_mul1, h_C2] <;> ring
    have h_sum_bound : ∑ x ∈ S_finset, ENat.toENNReal (dyadicCoveringNumber δ (P_x x ∩ Q)) ≤
        ENNReal.ofReal (C^2 * δ^(-s) * r^s) * ENat.toENNReal S_finset.card := by
      have h : ∑ x ∈ S_finset, ENat.toENNReal (dyadicCoveringNumber δ (P_x x ∩ Q)) ≤
          ∑ x ∈ S_finset, ENNReal.ofReal (C^2 * δ^(-s) * r^s) :=
        Finset.sum_le_sum h_per_x
      have h' : ∑ x ∈ S_finset, ENNReal.ofReal (C^2 * δ^(-s) * r^s) =
          ENNReal.ofReal (C^2 * δ^(-s) * r^s) * ENat.toENNReal S_finset.card := by
        have h1 : ∑ x ∈ S_finset, ENNReal.ofReal (C^2 * δ^(-s) * r^s) =
            (↑S_finset.card : ENNReal) * ENNReal.ofReal (C^2 * δ^(-s) * r^s) := by
          rw [Finset.sum_const]
          <;> simp [mul_comm]
        have h2 : ENat.toENNReal S_finset.card = (↑S_finset.card : ENNReal) := by simp
        calc
          ∑ x ∈ S_finset, ENNReal.ofReal (C^2 * δ^(-s) * r^s)
            = (↑S_finset.card : ENNReal) * ENNReal.ofReal (C^2 * δ^(-s) * r^s) := h1
          _ = ENNReal.ofReal (C^2 * δ^(-s) * r^s) * (↑S_finset.card : ENNReal) := mul_comm _ _
          _ = ENNReal.ofReal (C^2 * δ^(-s) * r^s) * ENat.toENNReal S_finset.card := by rw [h2]
      rw [h'] at h
      exact h
    have hS_card_bound : ENat.toENNReal S_finset.card ≤
        ENNReal.ofReal 7 * ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s) := by
      have hS_sub : S_set ⊆ ⋃ k' ∈ Kint, X_y ∩ J k' := by
        intro x hx
        have h_x_in_I : x ∈ I_real := hx.2
        have h4 : x ∈ ⋃ k' ∈ Kint, J k' := h_cover_I h_x_in_I
        rcases Set.mem_iUnion₂.mp h4 with ⟨k', hk', hxJ⟩
        exact Set.mem_iUnion₂.mpr ⟨k', hk', ⟨hx.1, hxJ⟩⟩
      let XJ_finset (k' : ℤ) : Finset ℝ :=
        (hX_fin.subset (show X_y ∩ J k' ⊆ X_y from fun x hx => hx.1)).toFinset
      have hXJ_eq : ∀ k' : ℤ, (XJ_finset k' : Set ℝ) = X_y ∩ J k' := by
        intro k'
        exact (hX_fin.subset (show X_y ∩ J k' ⊆ X_y from fun x hx => hx.1)).coe_toFinset
      have h4 : S_finset ⊆ Kint.biUnion XJ_finset := by
        intro x hx
        have h5 : x ∈ S_set := by
          have h6 : x ∈ (S_finset : Set ℝ) := hx
          rw [hS_eq] at h6
          exact h6
        have h6 : x ∈ ⋃ k' ∈ Kint, X_y ∩ J k' := hS_sub h5
        rcases Set.mem_iUnion₂.mp h6 with ⟨k', hk', hxJ⟩
        have h7 : x ∈ XJ_finset k' := by
          simpa [XJ_finset] using hxJ
        exact Finset.mem_biUnion.mpr ⟨k', hk', h7⟩
      have h5 : S_finset.card ≤ (Kint.biUnion XJ_finset).card := Finset.card_le_card h4
      have h6 : (Kint.biUnion XJ_finset).card ≤ ∑ k' ∈ Kint, (XJ_finset k').card := Finset.card_biUnion_le
      have h2 : (S_finset.card : ℕ) ≤ ∑ k' ∈ Kint, (XJ_finset k').card := by linarith
      have h3 : ENat.toENNReal S_finset.card ≤ ∑ k' ∈ Kint, ENat.toENNReal (XJ_finset k').card := by
        have h31 : (S_finset.card : ENNReal) ≤ ∑ k' ∈ Kint, ((XJ_finset k').card : ENNReal) := by
          exact_mod_cast h2
        simpa using h31
      have h4 : ∑ k' ∈ Kint, ENat.toENNReal (XJ_finset k').card ≤
          ∑ k' ∈ Kint, (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) :=
        Finset.sum_le_sum (fun k' hk' => by
          have h_eq : ENat.toENNReal (XJ_finset k').card = ENat.toENNReal (X_y ∩ J k').encard := by
            have h1 : ENat.toENNReal (XJ_finset k').card = ENat.toENNReal ((XJ_finset k' : Set ℝ)).encard := by
              simp
            rw [h1]
            have h2 : (XJ_finset k' : Set ℝ) = X_y ∩ J k' := hXJ_eq k'
            rw [h2]
          rw [h_eq]
          exact h_interval_bound k' hk')
      have h_sum_eq : ∑ k' ∈ Kint, (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) =
          ENNReal.ofReal (Kint.card : ℝ) * (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) := by
        have h1 : ∑ k' ∈ Kint, (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) =
            (↑Kint.card : ENNReal) * (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) := by
          rw [Finset.sum_const]
          <;> exact nsmul_eq_mul Kint.card (ENNReal.ofReal C * ↑X_y.encard * ENNReal.ofReal (r ^ s))
        have h2 : (↑Kint.card : ENNReal) = ENNReal.ofReal (Kint.card : ℝ) := by norm_cast
        rw [h1, h2]
      have h5 : ENat.toENNReal S_finset.card ≤
          ENNReal.ofReal (Kint.card : ℝ) * (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) := by
        calc
          ENat.toENNReal S_finset.card
            ≤ ∑ k' ∈ Kint, ENat.toENNReal (XJ_finset k').card := h3
          _ ≤ ∑ k' ∈ Kint, (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) := h4
          _ = ENNReal.ofReal (Kint.card : ℝ) * (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) := h_sum_eq
      have h6 : ENNReal.ofReal (Kint.card : ℝ) ≤ ENNReal.ofReal 7 := by
        exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hK_card)
      calc
        ENat.toENNReal S_finset.card
          ≤ ENNReal.ofReal (Kint.card : ℝ) * (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) := h5
        _ ≤ ENNReal.ofReal 7 * (ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) := by gcongr
        _ = ENNReal.ofReal 7 * ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s) := by ring
    calc
      ENat.toENNReal (dyadicCoveringNumber δ (P_U ∩ Q))
        ≤ ∑ x ∈ S_finset, ENat.toENNReal (dyadicCoveringNumber δ (P_x x ∩ Q)) := h_cover_union
      _ ≤ ENNReal.ofReal (C^2 * δ^(-s) * r^s) * ENat.toENNReal S_finset.card := h_sum_bound
      _ ≤ ENNReal.ofReal (C^2 * δ^(-s) * r^s) *
            (ENNReal.ofReal 7 * ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) := by
          gcongr
      _ = ENNReal.ofReal (7 * C^3) * ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s)) * ENNReal.ofReal (r ^ (2 * s)) := by
          have h_posC : 0 ≤ C := by positivity
          have h_posC2 : 0 ≤ C^2 := by positivity
          have h_posd : 0 ≤ δ^(-s) := by positivity
          have h_posr : 0 ≤ r ^ s := by positivity
          have h_pos3 : 0 ≤ (7 : ℝ) := by positivity
          have h1 : ENNReal.ofReal (C^2 * δ^(-s) * r^s) =
              ENNReal.ofReal (C^2) * ENNReal.ofReal (δ^(-s)) * ENNReal.ofReal (r^s) := by
            have h1a : ENNReal.ofReal (C^2 * δ^(-s) * r^s) =
                ENNReal.ofReal (C^2 * δ^(-s)) * ENNReal.ofReal (r^s) :=
              ENNReal.ofReal_mul (by positivity : 0 ≤ C^2 * δ^(-s))
            have h1b : ENNReal.ofReal (C^2 * δ^(-s)) =
                ENNReal.ofReal (C^2) * ENNReal.ofReal (δ^(-s)) :=
              ENNReal.ofReal_mul h_posC2
            rw [h1a, h1b] <;> ring
          have h2 : ENNReal.ofReal (r ^ s) * ENNReal.ofReal (r ^ s) = ENNReal.ofReal (r ^ (2 * s)) := by
            have h2a : ENNReal.ofReal (r ^ s) * ENNReal.ofReal (r ^ s) = ENNReal.ofReal ((r ^ s) * (r ^ s)) :=
              (ENNReal.ofReal_mul h_posr).symm
            rw [h2a]
            have h2b : (r ^ s) * (r ^ s) = r ^ (2 * s) := by
              have h : (r ^ s) * (r ^ s) = r ^ (s + s) := by
                rw [← Real.rpow_add (by positivity)]
              rw [h]
              have h2 : s + s = 2 * s := by ring
              rw [h2]
            rw [h2b]
          have h3 : ENNReal.ofReal (C^2) * (ENNReal.ofReal 7 * ENNReal.ofReal C) = ENNReal.ofReal (7 * C^3) := by
            have h3a : ENNReal.ofReal 7 * ENNReal.ofReal C = ENNReal.ofReal (7 * C) :=
              (ENNReal.ofReal_mul h_pos3).symm
            have h3b : ENNReal.ofReal (C^2) * ENNReal.ofReal (7 * C) = ENNReal.ofReal (C^2 * (7 * C)) :=
              (ENNReal.ofReal_mul h_posC2).symm
            rw [h3a, h3b]
            have h3c : C^2 * (7 * C) = 7 * C^3 := by ring
            rw [h3c]
          have h4 : ENNReal.ofReal (C^2 * δ^(-s) * r^s) *
                (ENNReal.ofReal 7 * ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) =
              ENNReal.ofReal (7 * C^3) * ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s)) * ENNReal.ofReal (r ^ (2 * s)) := by
            rw [h1]
            have h5 : (ENNReal.ofReal (C^2) * ENNReal.ofReal (δ^(-s)) * ENNReal.ofReal (r^s)) *
                  (ENNReal.ofReal 7 * ENNReal.ofReal C * ENat.toENNReal X_y.encard * ENNReal.ofReal (r ^ s)) =
                (ENNReal.ofReal (C^2) * (ENNReal.ofReal 7 * ENNReal.ofReal C)) *
                  ENNReal.ofReal (δ^(-s)) * ENat.toENNReal X_y.encard *
                  (ENNReal.ofReal (r ^ s) * ENNReal.ofReal (r ^ s)) := by ring
            rw [h5, h3, h2] <;> ring
          exact h4
      _ ≤ ENNReal.ofReal (7 * (Kov : ℝ) * C^4) * ENat.toENNReal (dyadicCoveringNumber δ P_U) * ENNReal.ofReal (r ^ (2 * s)) := by
          have h9 : ENNReal.ofReal (δ^(-s)) = ENNReal.ofReal C * ENNReal.ofReal (δ^(-s) / C) := by
            have h_posC : 0 ≤ C := by positivity
            have h9a : C * (δ^(-s) / C) = δ^(-s) := by
              field_simp [hC_pos.ne'] <;> ring
            have h9b : ENNReal.ofReal C * ENNReal.ofReal (δ^(-s) / C) = ENNReal.ofReal (C * (δ^(-s) / C)) :=
              (ENNReal.ofReal_mul h_posC).symm
            rw [h9b, h9a]
          have h7 : ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s)) ≤
              (Kov : ENNReal) * ENNReal.ofReal C * ENat.toENNReal U.encard := by
            rw [h9]
            have h10 : ENat.toENNReal X_y.encard * (ENNReal.ofReal C * ENNReal.ofReal (δ^(-s) / C)) =
                ENNReal.ofReal C * (ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s) / C)) := by ring
            rw [h10]
            have h11 : ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s) / C) ≤
                (Kov : ENNReal) * ENat.toENNReal U.encard := h_double_count
            have h12 : ENNReal.ofReal C * (ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s) / C)) ≤
                ENNReal.ofReal C * ((Kov : ENNReal) * ENat.toENNReal U.encard) :=
              mul_le_mul_of_nonneg_left h11 (by positivity)
            have h13 : ENNReal.ofReal C * ((Kov : ENNReal) * ENat.toENNReal U.encard) =
                (Kov : ENNReal) * ENNReal.ofReal C * ENat.toENNReal U.encard := by ring
            rw [h13] at h12
            exact h12
          have h_goal : ENNReal.ofReal (7 * C^3) * (ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s))) ≤
              ENNReal.ofReal (7 * (Kov : ℝ) * C^4) * ENat.toENNReal U.encard := by
            have h91 : ENNReal.ofReal (7 * C^3) * (ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s))) ≤
                ENNReal.ofReal (7 * C^3) * ((Kov : ENNReal) * ENNReal.ofReal C * ENat.toENNReal U.encard) :=
              mul_le_mul_of_nonneg_left h7 (by positivity)
            have h10 : ENNReal.ofReal (7 * C^3) * ((Kov : ENNReal) * ENNReal.ofReal C * ENat.toENNReal U.encard) =
                ENNReal.ofReal (7 * (Kov : ℝ) * C^4) * ENat.toENNReal U.encard := by
              have hK_coe : (Kov : ENNReal) = ENNReal.ofReal (Kov : ℝ) := by norm_cast
              rw [hK_coe]
              have h_assoc : ENNReal.ofReal (7 * C^3) * (ENNReal.ofReal (Kov : ℝ) * ENNReal.ofReal C * ENat.toENNReal U.encard) =
                  (ENNReal.ofReal (7 * C^3) * (ENNReal.ofReal (Kov : ℝ) * ENNReal.ofReal C)) * ENat.toENNReal U.encard := by ring
              rw [h_assoc]
              have h_mul : ENNReal.ofReal (7 * C^3) * (ENNReal.ofReal (Kov : ℝ) * ENNReal.ofReal C) =
                  ENNReal.ofReal (7 * (Kov : ℝ) * C^4) := by
                have h1 : ENNReal.ofReal (Kov : ℝ) * ENNReal.ofReal C = ENNReal.ofReal ((Kov : ℝ) * C) :=
                  (ENNReal.ofReal_mul (by positivity)).symm
                rw [h1]
                have h2 : ENNReal.ofReal (7 * C^3) * ENNReal.ofReal ((Kov : ℝ) * C) =
                    ENNReal.ofReal ((7 * C^3) * ((Kov : ℝ) * C)) :=
                  (ENNReal.ofReal_mul (by positivity)).symm
                rw [h2]
                have h3 : (7 * C^3) * ((Kov : ℝ) * C) = 7 * (Kov : ℝ) * C^4 := by ring
                rw [h3]
              rw [h_mul]
            exact le_trans h91 (le_of_eq h10)
          have h12 : ENNReal.ofReal (7 * C^3) * ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s)) * ENNReal.ofReal (r ^ (2 * s)) =
              (ENNReal.ofReal (7 * C^3) * (ENat.toENNReal X_y.encard * ENNReal.ofReal (δ^(-s)))) * ENNReal.ofReal (r ^ (2 * s)) := by ring
          rw [h12]
          have h13 : ENNReal.ofReal (7 * (Kov : ℝ) * C^4) * ENat.toENNReal U.encard =
              ENNReal.ofReal (7 * (Kov : ℝ) * C^4) * ENat.toENNReal (dyadicCoveringNumber δ P_U) := by
            rw [hP_U_card]
          rw [h13] at h_goal
          exact mul_le_mul_of_nonneg_right h_goal (by positivity)
  have h_s_nonneg2 : 0 ≤ 2 * s := by linarith [hs_nonneg]
  have h_s_le_two : 2 * s ≤ 2 := by linarith [hs_le_one]
  exact ⟨hP_U_bdd, hP_U_nonempty, by norm_num, hδ_dyadic, hδ, h_s_nonneg2, h_s_le_two, by positivity, h_main_bound⟩

end ProductLikeIncidence.ProductReduction
