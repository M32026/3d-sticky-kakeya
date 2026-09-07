module

/-
# Translation Bounds for Resolution A

Covering number bounds under translation, needed for graph normalization:
1. 1D projection: Nδ(π_y(T_y')) ≤ 2·Nδ(π_y(T_y))
2. 2D parameter set: Nδ(Pbar_param') ≤ 4·Nδ(Pbar_param)

## Whiteprint node
`translation_bounds_resolution_a`
-/

public import MyLeanRepo.ProductLikeIncidence.DeltaSetTranslation
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.TwoSidedBigCap
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set ENNReal Bornology Classical

namespace ProductLikeIncidence

/-- **1D projection translation bound**.

If `T_y'` is a 2D translation of `T_y` by vector `v`, then the 1D
projection `π_y(T_y')` is a real translation of `π_y(T_y)`, so its
dyadic covering number increases by at most a factor of 2. -/
lemma raw_proj_translation_bound
    {δ y : ℝ} (hδ : 0 < δ)
    {T_y T_y' : Set (EuclideanSpace ℝ (Fin 2))}
    (v : EuclideanSpace ℝ (Fin 2))
    (hT' : T_y' = (fun p => p + v) '' T_y)
    (hT_bdd : IsBounded T_y) :
    Nreal δ (Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) T_y') ≤
    2 * Nreal δ (Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) T_y) := by
  let π_y : EuclideanSpace ℝ (Fin 2) → ℝ := fun q => q 0 * y + q 1
  let a : ℝ := v 0 * y + v 1
  have h_eq : Set.image π_y T_y' = ProductReduction.translateSet a (Set.image π_y T_y) := by
    rw [hT']
    ext z
    simp only [Set.mem_image, ProductReduction.translateSet]
    constructor
    · rintro ⟨p', ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨π_y p, ⟨p, hp, rfl⟩, by simp [π_y, a] <;> ring⟩
    · rintro ⟨w, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p + v, ⟨p, hp, rfl⟩, by simp [π_y, a] <;> ring⟩
  rw [h_eq]
  let π_y_clm : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    { toFun := π_y
      map_add' := by intro a b; simp [π_y] <;> ring
      map_smul' := by intro c a; simp [π_y] <;> ring }
  have h_lipschitz : LipschitzWith ‖π_y_clm‖₊ π_y := π_y_clm.lipschitz
  have h_img_bdd : IsBounded (π_y '' T_y) := h_lipschitz.isBounded_image hT_bdd
  have h_eq2 : (Set.image π_y T_y) = (π_y '' T_y) := by rfl
  rw [h_eq2]
  exact nreal_translate_real_le_two hδ h_img_bdd a

/-- **2D translation covering bound**.

A translation of a bounded 2D set by an arbitrary vector `v` increases the
dyadic covering number by at most a factor of 4 (two adjacent cubes in each
of the two coordinates). -/
lemma dyadic_cover_translate2d_le_four
    {δ : ℝ} (hδ : 0 < δ)
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    (v : EuclideanSpace ℝ (Fin 2))
    (_hP_bdd : IsBounded P) :
    dyadicCoveringNumber δ ((fun p : EuclideanSpace ℝ (Fin 2) => p + v) '' P) ≤
    4 * dyadicCoveringNumber δ P := by
  let P' := (fun p : EuclideanSpace ℝ (Fin 2) => p + v) '' P
  let q : Fin 2 → ℤ := fun i => Int.floor (v i / δ)
  have hq1 : ∀ i, (q i : ℝ) ≤ v i / δ := fun i => Int.floor_le (v i / δ)
  have hq2 : ∀ i, v i / δ < (q i : ℝ) + 1 := fun i => Int.lt_floor_add_one (v i / δ)
  let r : Fin 2 → ℝ := fun i => v i - δ * (q i : ℝ)
  have hr1 : ∀ i, 0 ≤ r i := by
    intro i
    dsimp only [r]
    have h : δ * (q i : ℝ) ≤ v i := by
      have h' : (q i : ℝ) ≤ v i / δ := hq1 i
      calc δ * (q i : ℝ) ≤ δ * (v i / δ) := by gcongr
        _ = v i := by field_simp [hδ.ne']
    linarith
  have hr2 : ∀ i, r i < δ := by
    intro i
    dsimp only [r]
    have h : v i < δ * ((q i : ℝ) + 1) := by
      have h' : v i / δ < (q i : ℝ) + 1 := hq2 i
      calc v i = δ * (v i / δ) := by field_simp [hδ.ne']
        _ < δ * ((q i : ℝ) + 1) := by gcongr
    linarith

  let ε0 : Fin 2 → ℤ := 0
  let ε1 : Fin 2 → ℤ := fun i => if i = 0 then 1 else 0
  let ε2 : Fin 2 → ℤ := fun i => if i = 1 then 1 else 0
  let ε3 : Fin 2 → ℤ := fun _ => 1
  let shifts : Finset (Fin 2 → ℤ) := {ε0, ε1, ε2, ε3}

  let idxP : Set (Fin 2 → ℤ) := {k | (dyadicCube δ k ∩ P).Nonempty}
  let idxP' : Set (Fin 2 → ℤ) := {l | (dyadicCube δ l ∩ P').Nonempty}

  have h_inj : Function.Injective (dyadicCube (d := 2) δ) :=
    TwoSidedBigCap.dyadicCube_injective hδ

  have h_image1 : (dyadicCube δ '' idxP) = dyadicCubesMeeting (d := 2) δ P := by
    ext Q
    simp only [idxP, Set.mem_image, dyadicCubesMeeting, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, rfl⟩, hk⟩
    · rintro ⟨hQ, hk⟩
      rcases hQ with ⟨k, rfl⟩
      exact ⟨k, hk, rfl⟩

  have h_image2 : (dyadicCube δ '' idxP') = dyadicCubesMeeting (d := 2) δ P' := by
    ext Q
    simp only [idxP', Set.mem_image, dyadicCubesMeeting, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, rfl⟩, hk⟩
    · rintro ⟨hQ, hk⟩
      rcases hQ with ⟨k, rfl⟩
      exact ⟨k, hk, rfl⟩

  have h_injOn1 : Set.InjOn (dyadicCube δ) idxP := fun x _ y _ h => h_inj h
  have h_encard1 : (dyadicCube δ '' idxP).encard = idxP.encard := Set.InjOn.encard_image h_injOn1
  have h_cov_eq_P : dyadicCoveringNumber δ P = idxP.encard := by
    rw [dyadicCoveringNumber, ← h_image1]
    exact h_encard1

  have h_injOn2 : Set.InjOn (dyadicCube δ) idxP' := fun x _ y _ h => h_inj h
  have h_encard2 : (dyadicCube δ '' idxP').encard = idxP'.encard := Set.InjOn.encard_image h_injOn2
  have h_cov_eq_P' : dyadicCoveringNumber δ P' = idxP'.encard := by
    rw [dyadicCoveringNumber, ← h_image2]
    exact h_encard2

  have h_main : idxP' ⊆ ⋃ ε ∈ (shifts : Set (Fin 2 → ℤ)),
      (fun k : Fin 2 → ℤ => k + q + ε) '' idxP := by
    intro l hl
    simp only [idxP', Set.mem_setOf_eq] at hl
    rcases hl with ⟨p', hp'Q, hp'P'⟩
    rcases hp'P' with ⟨p, hpP, rfl⟩
    let k : Fin 2 → ℤ := fun i => Int.floor (p i / δ)
    have hk1 : ∀ i, δ * (k i : ℝ) ≤ p i := by
      intro i
      have h : (k i : ℝ) ≤ p i / δ := Int.floor_le (p i / δ)
      calc δ * (k i : ℝ) ≤ δ * (p i / δ) := by gcongr
        _ = p i := by field_simp [hδ.ne']
    have hk2 : ∀ i, p i < δ * ((k i : ℝ) + 1) := by
      intro i
      have h : p i / δ < (k i : ℝ) + 1 := Int.lt_floor_add_one (p i / δ)
      calc p i = δ * (p i / δ) := by field_simp [hδ.ne']
        _ < δ * ((k i : ℝ) + 1) := by gcongr
    have h_k_in_idxP : k ∈ idxP := by
      simp only [idxP, Set.mem_setOf_eq]
      exact ⟨p, fun i => ⟨hk1 i, hk2 i⟩, hpP⟩
    have h_lower : ∀ i, k i ≤ l i - q i := by
      intro i
      have h1 : (p + v) i < δ * ((l i : ℝ) + 1) := (hp'Q i).2
      have h2 : (p + v) i = p i + v i := by rfl
      rw [h2] at h1
      have h3 : p i + v i < δ * ((l i : ℝ) + 1) := h1
      have h4 : δ * (k i : ℝ) ≤ p i := hk1 i
      have h5 : v i = δ * (q i : ℝ) + r i := by simp [r] <;> ring
      rw [h5] at h3
      have h_real : (k i : ℝ) < (l i : ℝ) - (q i : ℝ) + 1 := by nlinarith [hδ, hr1 i]
      have h_int : k i < l i - q i + 1 := by exact_mod_cast h_real
      omega
    have h_upper : ∀ i, l i - q i ≤ k i + 1 := by
      intro i
      have h1 : δ * (l i : ℝ) ≤ (p + v) i := (hp'Q i).1
      have h2 : (p + v) i = p i + v i := by rfl
      rw [h2] at h1
      have h3 : δ * (l i : ℝ) ≤ p i + v i := h1
      have h4 : p i < δ * ((k i : ℝ) + 1) := hk2 i
      have h5 : v i = δ * (q i : ℝ) + r i := by simp [r] <;> ring
      rw [h5] at h3
      have h_real : (l i : ℝ) - (q i : ℝ) < (k i : ℝ) + 2 := by nlinarith [hδ, hr2 i]
      have h_int : l i - q i < k i + 2 := by exact_mod_cast h_real
      omega
    let ε : Fin 2 → ℤ := fun i => l i - q i - k i
    have hε01 : ∀ i, ε i = 0 ∨ ε i = 1 := by
      intro i
      have h1 : k i ≤ l i - q i := h_lower i
      have h2 : l i - q i ≤ k i + 1 := h_upper i
      have h3 : ε i = l i - q i - k i := by rfl
      rw [h3]
      omega
    have hε_in_shifts : ε ∈ shifts := by
      have h0 : ε 0 = 0 ∨ ε 0 = 1 := hε01 0
      have h1 : ε 1 = 0 ∨ ε 1 = 1 := hε01 1
      rcases h0 with (h0 | h0) <;> rcases h1 with (h1 | h1)
      · -- (0,0) → ε0
        have hε_eq : ε = ε0 := by
          ext i; fin_cases i <;> simp [ε0, h0, h1]
        rw [hε_eq]; simp [shifts]
      · -- (0,1) → ε2
        have hε_eq : ε = ε2 := by
          ext i; fin_cases i <;> simp [ε2, h0, h1]
        rw [hε_eq]; simp [shifts]
      · -- (1,0) → ε1
        have hε_eq : ε = ε1 := by
          ext i; fin_cases i <;> simp [ε1, h0, h1]
        rw [hε_eq]; simp [shifts]
      · -- (1,1) → ε3
        have hε_eq : ε = ε3 := by
          ext i; fin_cases i <;> simp [ε3, h0, h1]
        rw [hε_eq]; simp [shifts]
    have h_eq : l = k + q + ε := by
      ext i
      simp [ε] <;> ring
    simp only [Set.mem_iUnion]
    exact ⟨ε, hε_in_shifts, k, h_k_in_idxP, h_eq.symm⟩

  have h_shift_inj : ∀ ε ∈ (shifts : Set (Fin 2 → ℤ)),
      Function.Injective (fun k : Fin 2 → ℤ => k + q + ε) := by
    intro ε _ a b h
    simpa using h
  have h_encard_le : idxP'.encard ≤ 4 * idxP.encard := by
    calc idxP'.encard
      ≤ (⋃ ε ∈ (shifts : Set (Fin 2 → ℤ)), (fun k : Fin 2 → ℤ => k + q + ε) '' idxP).encard :=
        Set.encard_mono h_main
    _ ≤ ∑ ε ∈ shifts, ((fun k : Fin 2 → ℤ => k + q + ε) '' idxP).encard := by
      exact Finset.set_encard_biUnion_le shifts (fun ε => (fun k : Fin 2 → ℤ => k + q + ε) '' idxP)
    _ = ∑ ε ∈ shifts, idxP.encard := by
      apply Finset.sum_congr rfl
      intro ε hε
      exact Set.InjOn.encard_image (fun x _ y _ h => h_shift_inj ε hε h)
    _ = 4 * idxP.encard := by
      have h_card : shifts.card = 4 := by decide
      rw [Finset.sum_const, h_card] <;> ring
  rw [h_cov_eq_P', h_cov_eq_P]
  exact h_encard_le

end ProductLikeIncidence
