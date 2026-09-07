module

/-
# Basic Utilities

Generic utility lemmas extracted from the monolithic IncidenceToRingProof.

## Main results

1. `image_bounded_of_lipschitz` — image of bounded set under Lipschitz map is bounded
2. `rounded_projection_bound` — Nδ(rounded projection) ≤ 3·Nδ(raw projection)
3. `dyadicCubesMeeting_sUnion` — δ-cubes meeting union of δ-cube family = family itself

## Proof route

- `image_bounded_of_lipschitz`: thin wrapper around `LipschitzWith.isBounded_image`
- `rounded_projection_bound`:
  1. Raw projection B is bounded (coordinate projection is 1-Lipschitz)
  2. Rounded projection R is within δ/2 of B pointwise
  3. Apply `thickening_covering_factor` with M=1 to get factor 3
  4. Convert from `dyadicCoveringNumber` (`ℕ∞`) to `Nreal` (`ENNReal`)
  5. Apply monotonicity for S1 ⊆ R
- `dyadicCubesMeeting_sUnion`: forward direction uses disjointness of distinct
  dyadic cubes; reverse uses nonemptiness of dyadic cubes and subset inclusion

## Dependencies

- `MyLeanRepo.CoreDefinitions` — dyadic definitions, `Nreal`, `productLikeRealLineCopy`
- `MyLeanRepo.SetDiscretizationBridge` — `thickening_covering_factor`
- `MyLeanRepo.RoundingWrapper` — `Nreal_mono_local`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.SetDiscretizationBridge
public import MyLeanRepo.RoundingWrapper
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Bornology ENNReal Classical

namespace ProductLikeIncidence.ProductReduction

/-- Image of a bounded set under a Lipschitz map is bounded. -/
lemma image_bounded_of_lipschitz {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {s : Set α} {f : α → β} {C : ℝ}
    (hs : IsBounded s) (hC_nonneg : 0 ≤ C)
    (hlip : ∀ x y, dist (f x) (f y) ≤ C * dist x y) :
    IsBounded (f '' s) := by
  let K : NNReal := ⟨C, hC_nonneg⟩
  have h_lip : LipschitzWith K f := LipschitzWith.of_dist_le_mul hlip
  exact h_lip.isBounded_image hs

/-- Rounded projection bound: if every point of S1 is within δ/2 of a point in
    the raw projection, then the dyadic covering number of S1 is at most
    3 times the covering number of the raw projection. -/
lemma rounded_projection_bound {δ : ℝ} (hδ_pos : 0 < δ)
    {E : Set (EuclideanSpace ℝ (Fin 2))}
    {S1 : Set ℝ}
    (round : ℝ → ℝ)
    (h_round_near : ∀ x, |round x - x| ≤ δ / 2)
    (hS1_sub_img : S1 ⊆ Set.image (fun p : EuclideanSpace ℝ (Fin 2) => round (p 0)) E)
    (hE_bounded : IsBounded E) :
    Nreal δ S1 ≤ 3 * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0) E) := by
  let B : Set ℝ := Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0) E
  let R : Set ℝ := Set.image (fun p : EuclideanSpace ℝ (Fin 2) => round (p 0)) E
  have hB_bdd : IsBounded B := by
    have h_coord_le_norm : ∀ (x : EuclideanSpace ℝ (Fin 2)), |x 0| ≤ ‖x‖ := by
      intro x
      have h1 : ‖x‖ ^ 2 = ∑ i : Fin 2, (x i) ^ 2 := EuclideanSpace.real_norm_sq_eq x
      have h2 : (x 0) ^ 2 ≤ ∑ i : Fin 2, (x i) ^ 2 := by
        rw [Fin.sum_univ_two]
        exact le_add_of_nonneg_right (sq_nonneg _)
      have h3 : (x 0) ^ 2 ≤ ‖x‖ ^ 2 := by
        rw [h1] at *; exact h2
      have h4 : |x 0| ≤ ‖x‖ := by
        nlinarith [abs_nonneg (x 0), norm_nonneg x, sq_abs (x 0)]
      exact h4
    have h_proj_dist : ∀ (p q : EuclideanSpace ℝ (Fin 2)),
        dist (p 0) (q 0) ≤ dist p q := by
      intro p q
      have h1 : dist (p 0) (q 0) = |p 0 - q 0| := by simp [Real.dist_eq]
      rw [h1]
      have h5 : |(p - q) 0| ≤ ‖p - q‖ := h_coord_le_norm (p - q)
      have h6 : (p - q) 0 = p 0 - q 0 := by simp
      rw [h6] at h5
      have h7 : ‖p - q‖ = dist p q := by simp [dist_eq_norm]
      rw [h7] at h5
      exact h5
    have h_proj_dist1 : ∀ (x y : EuclideanSpace ℝ (Fin 2)),
        dist (x 0) (y 0) ≤ (1 : ℝ) * dist x y := by
      intro x y
      have h := h_proj_dist x y
      simpa using h
    exact image_bounded_of_lipschitz hE_bounded (show (0 : ℝ) ≤ 1 from by norm_num) h_proj_dist1
  have h_close : ∀ (p : ℝ), p ∈ R → ∃ (q : ℝ), q ∈ B ∧ |p - q| ≤ (↑(1 : ℕ) : ℝ) * δ := by
    intro p hp
    rcases hp with ⟨e, heE, rfl⟩
    let x : ℝ := e 0
    have hx_B : x ∈ B := ⟨e, heE, rfl⟩
    have h_dist : |round x - x| ≤ δ / 2 := h_round_near x
    have hδ2 : δ / 2 ≤ (↑(1 : ℕ) : ℝ) * δ := by
      simp
      linarith
    exact ⟨x, hx_B, le_trans h_dist hδ2⟩
  have h_main : dyadicCoveringNumber δ (productLikeRealLineCopy R) ≤
      (2 * (1 : ℕ) + 1) * dyadicCoveringNumber δ (productLikeRealLineCopy B) :=
    SetDiscretizationBridge.thickening_covering_factor (M := 1) hδ_pos hB_bdd h_close
  have h_realLine : ∀ (A : Set ℝ), productLikeRealLineCopy A = realLineCopy A := by
    intro A; rfl
  rw [h_realLine R, h_realLine B] at h_main
  have h_toENNReal : ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy R)) ≤
      ENat.toENNReal ((2 * (1 : ℕ) + 1) * dyadicCoveringNumber δ (realLineCopy B)) := by
    have h_mono' : Monotone ENat.toENNReal := by
      intro a b h
      exact ENat.toENNReal_le.mpr h
    exact h_mono' h_main
  have h_mul : ENat.toENNReal ((2 * (1 : ℕ) + 1) * dyadicCoveringNumber δ (realLineCopy B)) =
      ENat.toENNReal (2 * (1 : ℕ) + 1) * ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy B)) := by
    rw [ENat.toENNReal_mul]
  rw [h_mul] at h_toENNReal
  have h_coeff2 : ENat.toENNReal (2 * (1 : ℕ) + 1) = (3 : ENNReal) := by
    norm_cast
  rw [h_coeff2] at h_toENNReal
  have hR_goal : Nreal δ R ≤ (3 : ENNReal) * Nreal δ B := by
    dsimp only [Nreal]
    exact h_toENNReal
  have hS1_sub_R : S1 ⊆ R := hS1_sub_img
  have h_mono : Nreal δ S1 ≤ Nreal δ R := robust_projection_main.Nreal_mono_local hS1_sub_R
  have h_final : Nreal δ S1 ≤ (3 : ENNReal) * Nreal δ B := le_trans h_mono hR_goal
  simpa [B] using h_final

/-- For a family C of δ-dyadic cubes, the δ-cubes meeting their union are exactly C. -/
lemma dyadicCubesMeeting_sUnion {d : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    {C : Set (Set (EuclideanSpace ℝ (Fin d)))}
    (hC : C ⊆ dyadicCubes d δ) :
    dyadicCubesMeeting δ (⋃₀ C) = C := by
  ext Q
  simp only [dyadicCubesMeeting, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hQ_dyadic, ⟨x, hxQ, hxU⟩⟩
    rcases hxU with ⟨Q', hQ'_in_C, hxQ'⟩
    rcases hC hQ'_in_C with ⟨k', rfl⟩
    rcases hQ_dyadic with ⟨k, rfl⟩
    have hk : k = k' := by
      by_contra hne
      have h_coord : ∃ (i : Fin d), k i ≠ k' i := by
        by_contra h
        push Not at h
        have h' : k = k' := by
          funext i
          exact h i
        exact hne h'
      rcases h_coord with ⟨i, hne_i⟩
      have h1 : x i ∈ Set.Ico (δ * (k i : ℝ)) (δ * ((k i : ℝ) + 1)) := hxQ i
      have h2 : x i ∈ Set.Ico (δ * (k' i : ℝ)) (δ * ((k' i : ℝ) + 1)) := hxQ' i
      have h_ne' : (k i : ℝ) ≠ (k' i : ℝ) := by exact_mod_cast hne_i
      have h_cases : (k i : ℝ) < (k' i : ℝ) ∨ (k' i : ℝ) < (k i : ℝ) :=
        lt_or_gt_of_ne h_ne'
      rcases h_cases with (h_lt | h_lt')
      · -- k i < k' i
        have h3 : (k i : ℤ) < (k' i : ℤ) := by exact_mod_cast h_lt
        have h4 : (k i : ℝ) + 1 ≤ (k' i : ℝ) := by
          have h5 : (k i : ℤ) + 1 ≤ (k' i : ℤ) := Int.add_one_le_of_lt h3
          exact_mod_cast h5
        have h6 : δ * ((k i : ℝ) + 1) ≤ δ * (k' i : ℝ) := by gcongr
        have h7 : x i < δ * ((k i : ℝ) + 1) := h1.2
        have h8 : δ * (k' i : ℝ) ≤ x i := h2.1
        linarith
      · -- k' i < k i
        have h3 : (k' i : ℤ) < (k i : ℤ) := by exact_mod_cast h_lt'
        have h4 : (k' i : ℝ) + 1 ≤ (k i : ℝ) := by
          have h5 : (k' i : ℤ) + 1 ≤ (k i : ℤ) := Int.add_one_le_of_lt h3
          exact_mod_cast h5
        have h6 : δ * ((k' i : ℝ) + 1) ≤ δ * (k i : ℝ) := by gcongr
        have h7 : x i < δ * ((k' i : ℝ) + 1) := h2.2
        have h8 : δ * (k i : ℝ) ≤ x i := h1.1
        linarith
    rw [hk] at *
    exact hQ'_in_C
  · intro hQ_in_C
    have hQ_dyadic : Q ∈ dyadicCubes d δ := hC hQ_in_C
    have hQ_sub : Q ⊆ ⋃₀ C := Set.subset_sUnion_of_mem hQ_in_C
    have h_nonempty : Q.Nonempty := by
      rcases hQ_dyadic with ⟨k, rfl⟩
      let p : EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 (Fin d → ℝ)).symm fun i => δ * (k i : ℝ)
      have hp : p ∈ dyadicCube δ k := by
        intro i
        simp only [p, Set.mem_Ico, WithLp.equiv_symm_apply]
        <;> constructor <;> simp [hδ_pos] <;> norm_cast <;> linarith
      exact ⟨p, hp⟩
    have h_meet : (Q ∩ ⋃₀ C).Nonempty := by
      have h_eq : Q ∩ ⋃₀ C = Q := by
        apply Set.inter_eq_left.mpr
        exact hQ_sub
      rw [h_eq]
      exact h_nonempty
    exact ⟨hQ_dyadic, h_meet⟩

end ProductLikeIncidence.ProductReduction
