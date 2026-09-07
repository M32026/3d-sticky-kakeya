module

/-
# Discretized Bourgain covering inequality — complete proof

Direct cube-to-cube mapping with bounded fibers (constant 16).
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.Compat
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped Pointwise
open ProductLikeIncidence

namespace bourgain_projection_theorem

/-! ## Helper: bounded fibers counting -/

lemma finset_card_le_mul_of_bounded_fibers {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Finset α} {t : Finset β} (f : α → β)
    (h1 : ∀ x ∈ s, f x ∈ t) {C : ℕ}
    (h2 : ∀ y ∈ t, (s.filter (fun x => f x = y)).card ≤ C) :
    s.card ≤ C * t.card := by
  have h_union : s = t.biUnion (fun y => s.filter (fun x => f x = y)) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hx; exact ⟨f x, h1 x hx, hx, rfl⟩
    · rintro ⟨y, hy, hx, rfl⟩; exact hx
  rw [h_union]
  have h_disj : ∀ y1 ∈ t, ∀ y2 ∈ t, y1 ≠ y2 →
      Disjoint (s.filter (fun x => f x = y1)) (s.filter (fun x => f x = y2)) := by
    intro y1 _ y2 _ hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h3 : f x = y1 := (Finset.mem_filter.mp hx1).2
    have h4 : f x = y2 := (Finset.mem_filter.mp hx2).2
    exact hne (h3.symm.trans h4)
  rw [Finset.card_biUnion h_disj]
  have h : ∑ y ∈ t, (s.filter (fun x => f x = y)).card ≤ ∑ y ∈ t, C :=
    Finset.sum_le_sum (fun y hy => h2 y hy)
  have h' : ∑ y ∈ t, C = C * t.card := by
    simp [Finset.sum_const] <;> ring
  rw [h'] at h
  exact h

/-! ## Cube indices intersecting an interval -/

/-- Number of δ-dyadic cubes intersecting an interval of length ≤ 3δ is at most 4. -/
lemma cubes_meeting_interval_le4 {δ : ℝ} (hδ : 0 < δ) {a b : ℝ} (h_len : b - a ≤ 3 * δ) :
    Set.encard {k : ℤ | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ Set.Ico a b).Nonempty} ≤ 4 := by
  have h1 : {k : ℤ | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ Set.Ico a b).Nonempty} ⊆
      {k : ℤ | a / δ - 1 < (k : ℝ) ∧ (k : ℝ) < b / δ} := by
    intro k hk
    rcases hk with ⟨x, hx_cube, hx_int⟩
    have h2 : δ * (k : ℝ) ≤ x := hx_cube.1
    have h3 : x < δ * ((k : ℝ) + 1) := hx_cube.2
    have h4 : a ≤ x := hx_int.1
    have h5 : x < b := hx_int.2
    have h6 : a / δ - 1 < (k : ℝ) := by
      have h61 : a < δ * ((k : ℝ) + 1) := by linarith
      have h62 : a / δ < (k : ℝ) + 1 := by
        calc a / δ < (δ * ((k : ℝ) + 1)) / δ := by gcongr
          _ = (k : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
      linarith
    have h7 : (k : ℝ) < b / δ := by
      have h71 : δ * (k : ℝ) < b := by linarith
      calc (k : ℝ) = (δ * (k : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
        _ < b / δ := by gcongr
    exact ⟨h6, h7⟩
  have h2 : (b / δ) - (a / δ - 1) ≤ 4 := by
    have h3 : (b / δ) - (a / δ - 1) = (b - a) / δ + 1 := by ring
    rw [h3]
    have h4 : (b - a) / δ ≤ 3 := by
      calc (b - a) / δ ≤ (3 * δ) / δ := by gcongr
        _ = 3 := by field_simp [hδ.ne'] <;> ring
    linarith
  have h3 : Set.encard {k : ℤ | a / δ - 1 < (k : ℝ) ∧ (k : ℝ) < b / δ} ≤ 4 := by
    let m : ℤ := Int.floor (a / δ - 1) + 1
    let M : ℤ := Int.ceil (b / δ)
    let S : Finset ℤ := Finset.Ico m M
    have hS1 : {k : ℤ | a / δ - 1 < (k : ℝ) ∧ (k : ℝ) < b / δ} ⊆ (S : Set ℤ) := by
      intro k hk
      rcases hk with ⟨hk1, hk2⟩
      have h4 : m ≤ k := by
        have h5 : (Int.floor (a / δ - 1) : ℝ) < (k : ℝ) := by
          have h6 : (Int.floor (a / δ - 1) : ℝ) ≤ a / δ - 1 := Int.floor_le (a / δ - 1)
          linarith [hk1]
        have h7 : Int.floor (a / δ - 1) < k := by exact_mod_cast h5
        simpa [m] using Int.add_one_le_iff.mpr h7
      have h7 : k < M := by
        have h8 : (k : ℝ) < (Int.ceil (b / δ) : ℝ) := by
          have h9 : (b / δ) ≤ (Int.ceil (b / δ) : ℝ) := Int.le_ceil _
          linarith [hk2]
        exact_mod_cast h8
      exact Finset.mem_Ico.mpr ⟨h4, h7⟩
    have h_bound : (M : ℝ) - (m : ℝ) < 5 := by
      have h5 : (M : ℝ) < b / δ + 1 := Int.ceil_lt_add_one _
      have h_floor_raw : a / δ - 1 < (Int.floor (a / δ - 1) : ℝ) + 1 := Int.lt_floor_add_one (a / δ - 1)
      have h61 : (Int.floor (a / δ - 1) : ℝ) + 1 > a / δ - 1 := by exact h_floor_raw
      have h6 : (m : ℝ) > a / δ - 1 := by
        have h_eq : (m : ℝ) = (Int.floor (a / δ - 1) : ℝ) + 1 := by
          simp [m] <;> norm_cast
        rw [h_eq]
        exact h61
      linarith
    have hS2 : S.card ≤ 4 := by
      by_cases h10 : m ≤ M
      · have h11 : S.card = (M - m).toNat := by exact Int.card_Ico m M
        rw [h11]
        have h12 : M - m < 5 := by exact_mod_cast h_bound
        have h13 : (M - m).toNat ≤ 4 := by
          apply Int.toNat_le.mpr
          omega
        exact h13
      · have h12 : M ≤ m := by omega
        have h11 : S = ∅ := by exact Finset.Ico_eq_empty_of_le h12
        rw [h11] <;> simp
    have h4 : Set.encard _ ≤ (S : Set ℤ).encard := Set.encard_mono hS1
    have h5 : (S : Set ℤ).encard = S.card := by simp
    rw [h5] at h4
    exact h4.trans (by exact_mod_cast hS2)
  exact Set.encard_mono h1 |>.trans h3

/-- Number of δ-dyadic cubes intersecting an interval of length ≤ δ is at most 2. -/
lemma cubes_meeting_interval_le2 {δ : ℝ} (hδ : 0 < δ) {a b : ℝ} (h_len : b - a ≤ δ) :
    Set.encard {k : ℤ | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ Set.Ico a b).Nonempty} ≤ 2 := by
  have h1 : {k : ℤ | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ Set.Ico a b).Nonempty} ⊆
      {k : ℤ | a / δ - 1 < (k : ℝ) ∧ (k : ℝ) < b / δ} := by
    intro k hk
    rcases hk with ⟨x, hx_cube, hx_int⟩
    have h2 : δ * (k : ℝ) ≤ x := hx_cube.1
    have h3 : x < δ * ((k : ℝ) + 1) := hx_cube.2
    have h4 : a ≤ x := hx_int.1
    have h5 : x < b := hx_int.2
    have h6 : a / δ - 1 < (k : ℝ) := by
      have h61 : a < δ * ((k : ℝ) + 1) := by linarith
      have h62 : a / δ < (k : ℝ) + 1 := by
        calc a / δ < (δ * ((k : ℝ) + 1)) / δ := by gcongr
          _ = (k : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
      linarith
    have h7 : (k : ℝ) < b / δ := by
      have h71 : δ * (k : ℝ) < b := by linarith
      calc (k : ℝ) = (δ * (k : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
        _ < b / δ := by gcongr
    exact ⟨h6, h7⟩
  have h2 : (b / δ) - (a / δ - 1) ≤ 2 := by
    have h3 : (b / δ) - (a / δ - 1) = (b - a) / δ + 1 := by ring
    rw [h3]
    have h4 : (b - a) / δ ≤ 1 := by
      calc (b - a) / δ ≤ δ / δ := by gcongr
        _ = 1 := by field_simp [hδ.ne'] <;> ring
    linarith
  have h3 : Set.encard {k : ℤ | a / δ - 1 < (k : ℝ) ∧ (k : ℝ) < b / δ} ≤ 2 := by
    let m : ℤ := Int.floor (a / δ - 1) + 1
    let M : ℤ := Int.ceil (b / δ)
    let S : Finset ℤ := Finset.Ico m M
    have hS1 : {k : ℤ | a / δ - 1 < (k : ℝ) ∧ (k : ℝ) < b / δ} ⊆ (S : Set ℤ) := by
      intro k hk
      rcases hk with ⟨hk1, hk2⟩
      have h4 : m ≤ k := by
        have h5 : (Int.floor (a / δ - 1) : ℝ) < (k : ℝ) := by
          have h6 : (Int.floor (a / δ - 1) : ℝ) ≤ a / δ - 1 := Int.floor_le (a / δ - 1)
          linarith [hk1]
        have h7 : Int.floor (a / δ - 1) < k := by exact_mod_cast h5
        simpa [m] using Int.add_one_le_iff.mpr h7
      have h7 : k < M := by
        have h8 : (k : ℝ) < (Int.ceil (b / δ) : ℝ) := by
          have h9 : (b / δ) ≤ (Int.ceil (b / δ) : ℝ) := Int.le_ceil _
          linarith [hk2]
        exact_mod_cast h8
      exact Finset.mem_Ico.mpr ⟨h4, h7⟩
    have h_bound : (M : ℝ) - (m : ℝ) < 3 := by
      have h5 : (M : ℝ) < b / δ + 1 := Int.ceil_lt_add_one _
      have h_floor_raw : a / δ - 1 < (Int.floor (a / δ - 1) : ℝ) + 1 := Int.lt_floor_add_one (a / δ - 1)
      have h61 : (Int.floor (a / δ - 1) : ℝ) + 1 > a / δ - 1 := by exact h_floor_raw
      have h6 : (m : ℝ) > a / δ - 1 := by
        have h_eq : (m : ℝ) = (Int.floor (a / δ - 1) : ℝ) + 1 := by
          simp [m] <;> norm_cast
        rw [h_eq]
        exact h61
      linarith
    have hS2 : S.card ≤ 2 := by
      by_cases h10 : m ≤ M
      · have h11 : S.card = (M - m).toNat := by exact Int.card_Ico m M
        rw [h11]
        have h12 : M - m < 3 := by exact_mod_cast h_bound
        have h13 : (M - m).toNat ≤ 2 := by
          apply Int.toNat_le.mpr
          omega
        exact h13
      · have h12 : M ≤ m := by omega
        have h11 : S = ∅ := by exact Finset.Ico_eq_empty_of_le h12
        rw [h11] <;> simp
    have h4 : Set.encard _ ≤ (S : Set ℤ).encard := Set.encard_mono hS1
    have h5 : (S : Set ℤ).encard = S.card := by simp
    rw [h5] at h4
    exact h4.trans (by exact_mod_cast hS2)
  exact Set.encard_mono h1 |>.trans h3

/-! ## Index set bijection with covering numbers -/

/-- The cube map k ↦ dyadicCube δ k is injective. -/
lemma dyadicCube_map_injective {d : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    Function.Injective (fun (k : Fin d → ℤ) => dyadicCube δ k) := by
  intro k1 k2 h
  have h' : dyadicCube δ k1 = dyadicCube δ k2 := by simpa using h
  have h_nonempty : (dyadicCube δ k1).Nonempty := dyadicCube_nonempty hδ k1
  rcases h_nonempty with ⟨x, hx1⟩
  have hx2 : x ∈ dyadicCube δ k2 := by
    exact h' ▸ hx1
  have h1 : ∀ i, k1 i = k2 i := by
    intro i
    have h21 : δ * (k1 i : ℝ) ≤ x i := (hx1 i).1
    have h22 : x i < δ * ((k1 i : ℝ) + 1) := (hx1 i).2
    have h23 : δ * (k2 i : ℝ) ≤ x i := (hx2 i).1
    have h24 : x i < δ * ((k2 i : ℝ) + 1) := (hx2 i).2
    have h3 : (k1 i : ℝ) < (k2 i : ℝ) + 1 := by nlinarith
    have h4 : (k2 i : ℝ) < (k1 i : ℝ) + 1 := by nlinarith
    have h5 : k1 i ≤ k2 i := by
      by_contra h5
      have h6 : k1 i ≥ k2 i + 1 := by omega
      have h7 : (k1 i : ℝ) ≥ (k2 i : ℝ) + 1 := by exact_mod_cast h6
      linarith
    have h6 : k2 i ≤ k1 i := by
      by_contra h6
      have h7 : k2 i ≥ k1 i + 1 := by omega
      have h8 : (k2 i : ℝ) ≥ (k1 i : ℝ) + 1 := by exact_mod_cast h7
      linarith
    exact le_antisymm h5 h6
  exact funext h1

/-- For a bounded set A, the index set {k | cube k meets A} is finite
and has encard equal to the dyadic covering number. -/
lemma dyadic_index_set_finite_and_encard {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {A : Set (EuclideanSpace ℝ (Fin d))} (hA : Bornology.IsBounded A) :
    let I : Set (Fin d → ℤ) := {k | (dyadicCube δ k ∩ A).Nonempty}
    I.Finite ∧ I.encard = dyadicCoveringNumber δ A := by
  let I : Set (Fin d → ℤ) := {k | (dyadicCube δ k ∩ A).Nonempty}
  let g : (Fin d → ℤ) → Set (EuclideanSpace ℝ (Fin d)) := fun k => dyadicCube δ k
  have h_g_inj : Function.Injective g := dyadicCube_map_injective hδ
  have h_image : g '' I = dyadicCubesMeeting δ A := by
    ext Q
    simp only [Set.mem_image, dyadicCubesMeeting, dyadicCubes]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, rfl⟩, hk⟩
    · rintro ⟨hQ1, hQ2⟩
      rcases hQ1 with ⟨k, rfl⟩
      exact ⟨k, hQ2, rfl⟩
  have hfin_cubes : (dyadicCubesMeeting δ A).Finite := dyadicCubesMeeting_finite hδ hA
  have h1 : I = g ⁻¹' (dyadicCubesMeeting δ A) := by
    ext k
    simp only [I, Set.mem_preimage, Set.mem_setOf_eq, g, dyadicCubesMeeting, dyadicCubes]
    <;> simp
  have hcard : (g '' I).encard = I.encard := Function.Injective.encard_image h_g_inj I
  have hfin_image : (g '' I).Finite := by
    rw [h_image]
    exact hfin_cubes
  have h_lt_top : I.encard < ⊤ := by
    have h : (g '' I).encard < ⊤ := hfin_image.encard_lt_top
    rw [hcard] at h
    exact h
  have hfin_I : I.Finite := by
    have h' : I.encard < ⊤ := h_lt_top
    exact Set.encard_lt_top_iff.mp h_lt_top
  have h_main : I.encard = dyadicCoveringNumber δ A := by
    have h_eq : (g '' I).encard = (dyadicCubesMeeting δ A).encard := by rw [h_image]
    have h : I.encard = (g '' I).encard := hcard.symm
    rw [h, h_eq]
    <;> rfl
  exact ⟨hfin_I, h_main⟩

/-- For a bounded real set S, the integer index set is finite and has encard
equal to the dyadic covering number of the 1D copy. -/
lemma real_index_set_finite_and_encard {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS : Bornology.IsBounded S) :
    let I : Set ℤ := {k | ∃ z ∈ S, δ * (k : ℝ) ≤ z ∧ z < δ * ((k : ℝ) + 1)}
    I.Finite ∧ I.encard = dyadicCoveringNumber δ (_root_.productLikeRealLineCopy S) := by
  let I : Set ℤ := {k | ∃ z ∈ S, δ * (k : ℝ) ≤ z ∧ z < δ * ((k : ℝ) + 1)}
  let g1 : ℤ → (Fin 1 → ℤ) := fun k => fun _ => k
  have h_g1_inj : Function.Injective g1 := by
    intro k1 k2 h
    have h' := congr_fun h 0
    simpa [g1] using h'
  let I' : Set (Fin 1 → ℤ) := g1 '' I
  have h_I'_eq : I' = {k' : Fin 1 → ℤ | (dyadicCube δ k' ∩ _root_.productLikeRealLineCopy S).Nonempty} := by
    ext k'
    simp only [I', Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rcases hk with ⟨z, hzS, hz1, hz2⟩
      let e1 : EuclideanSpace ℝ (Fin 1) ≃ (Fin 1 → ℝ) := EuclideanSpace.equiv (Fin 1) ℝ
      let x : EuclideanSpace ℝ (Fin 1) := e1.symm (fun _ => z)
      have h1 : e1 x = (fun _ : Fin 1 => z) := e1.apply_symm_apply _
      have hx1 : x ∈ _root_.productLikeRealLineCopy S := by
        have h2 : (e1 x) 0 ∈ S := by rw [h1] <;> exact hzS
        have h3 : x 0 ∈ S := h2
        simpa [_root_.productLikeRealLineCopy, realLineCopy] using h3
      have hx2 : x ∈ dyadicCube δ (g1 k) := by
        intro i
        have h3 : (e1 x) i ∈ Set.Ico (δ * ((g1 k i) : ℝ)) (δ * (((g1 k i) : ℝ) + 1)) := by
          rw [h1] <;> fin_cases i <;> simp [g1, hz1, hz2] <;> exact ⟨hz1, hz2⟩
        simpa [dyadicCube, e1] using h3
      exact ⟨x, hx2, hx1⟩
    · rintro ⟨x, hx_cube, hx_S⟩
      let z := x 0
      have hzS : z ∈ S := by
        simpa [_root_.productLikeRealLineCopy, realLineCopy, z] using hx_S
      have hz1 : δ * ((k' 0) : ℝ) ≤ z := (hx_cube 0).1
      have hz2 : z < δ * (((k' 0) : ℝ) + 1) := (hx_cube 0).2
      have h_k' : g1 (k' 0) = k' := by
        funext i; simp [g1] <;> fin_cases i <;> rfl
      exact ⟨k' 0, ⟨z, hzS, hz1, hz2⟩, h_k'⟩
  have hS' : Bornology.IsBounded (_root_.productLikeRealLineCopy S) :=
    productLikeRealLineCopy_bounded hS
  have h_main := dyadic_index_set_finite_and_encard hδ hS'
  have hfin_I' : I'.Finite := by
    rw [h_I'_eq]; exact h_main.1
  have hcard_I' : I'.encard = dyadicCoveringNumber δ (_root_.productLikeRealLineCopy S) := by
    rw [h_I'_eq]; exact h_main.2
  have h1 : I = g1 ⁻¹' I' := by
    ext k
    simp only [I', Set.mem_preimage, Set.mem_image, g1]
    <;> constructor
    · intro hk
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k', hk', h_eq⟩
      have h_k_eq : k' = k := by
        have h := congr_fun h_eq 0
        simpa [g1] using h
      rw [h_k_eq] at hk'
      exact hk'
  have hcard_I : (g1 '' I).encard = I.encard := Function.Injective.encard_image h_g1_inj I
  have hfin_image : (g1 '' I).Finite := by
    have h2 : g1 '' I = I' := by rfl
    rw [h2]
    exact hfin_I'
  have h_lt_top : I.encard < ⊤ := by
    have h : (g1 '' I).encard < ⊤ := hfin_image.encard_lt_top
    rw [hcard_I] at h
    exact h
  have hfin_I : I.Finite := by
    have h' : I.encard < ⊤ := h_lt_top
    exact Set.encard_lt_top_iff.mp h_lt_top
  have hcard_I2 : I.encard = I'.encard := by
    have h : (g1 '' I).encard = I.encard := hcard_I
    have h2 : g1 '' I = I' := by rfl
    rw [h2] at h
    exact h.symm
  exact ⟨hfin_I, hcard_I2.trans hcard_I'⟩

/-- `δ * ⌊x/δ⌋ ≤ x` for `δ > 0`. -/
lemma floor_mul_le {δ x : ℝ} (hδ : 0 < δ) : δ * (Int.floor (x / δ) : ℝ) ≤ x := by
  have h : (Int.floor (x / δ) : ℝ) ≤ x / δ := Int.floor_le (x / δ)
  have h2 : δ * (Int.floor (x / δ) : ℝ) ≤ δ * (x / δ) := by gcongr
  have h3 : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
  rw [h3] at h2
  exact h2

/-- `x < δ * (⌊x/δ⌋ + 1)` for `δ > 0`. -/
lemma lt_floor_add_one_mul {δ x : ℝ} (hδ : 0 < δ) : x < δ * ((Int.floor (x / δ) : ℝ) + 1) := by
  have h : x / δ < (Int.floor (x / δ) : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
  have h2 : δ * (x / δ) < δ * ((Int.floor (x / δ) : ℝ) + 1) := by gcongr
  have h3 : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
  rw [h3] at h2
  exact h2

/-! ## Main discretized theorem -/

/--
Discretized Bourgain covering inequality with constant 16 (≤ 81).
-/
theorem discretized_bourgain_averaging16 {δ x : ℝ} (hδ : 0 < δ)
    {A B1 B2 : Set ℝ} {B : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : Bornology.IsBounded A) (hB1 : Bornology.IsBounded B1)
    (hB2 : Bornology.IsBounded B2) (hB : Bornology.IsBounded B)
    (hB_sub : ∀ p ∈ B, p 0 ∈ B1 ∧ p 1 ∈ B2)
    (hA_sub : A ⊆ B1) (hx : |x| ≤ 1) :
    ENat.toENNReal (dyadicCoveringNumber δ
      (_root_.productLikeRealLineCopy (Set.image2 (fun a1 a2 => a1 + x * a2) A A))) *
    ENat.toENNReal (dyadicCoveringNumber δ B) ≤
    16 * ENat.toENNReal (dyadicCoveringNumber δ
      (_root_.productLikeRealLineCopy (Set.image2 (· - ·) B1 A))) *
    ENat.toENNReal (dyadicCoveringNumber δ
      (_root_.productLikeRealLineCopy (Set.image2 (· - ·) B2 A))) *
    ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D x B)) := by
  -- Boundedness of derived sets
  have h_lipschitz_add : LipschitzWith 2 (fun p : ℝ × ℝ => p.1 + x * p.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    have h1 : |p.1 + x * p.2 - (q.1 + x * q.2)| ≤ |p.1 - q.1| + |p.2 - q.2| := by
      calc |p.1 + x * p.2 - (q.1 + x * q.2)|
          ≤ |p.1 - q.1| + |x * (p.2 - q.2)| := by
            rw [show p.1 + x * p.2 - (q.1 + x * q.2) = (p.1 - q.1) + x * (p.2 - q.2) by ring]
            exact abs_add_le (p.1 - q.1) (x * (p.2 - q.2))
        _ ≤ |p.1 - q.1| + |x| * |p.2 - q.2| := by rw [abs_mul]
        _ ≤ |p.1 - q.1| + |p.2 - q.2| := by
            have h' : |x| * |p.2 - q.2| ≤ |p.2 - q.2| := by
              have hpos : 0 ≤ |p.2 - q.2| := abs_nonneg _
              nlinarith [hx]
            linarith
    have hdist : dist (p.1 + x * p.2) (q.1 + x * q.2) = |p.1 + x * p.2 - (q.1 + x * q.2)| := by
      rw [Real.dist_eq] <;> rfl
    have hsum : |p.1 - q.1| + |p.2 - q.2| ≤ 2 * dist p q := by
      have hmax : dist p q = max (dist p.1 q.1) (dist p.2 q.2) := by rfl
      have ha : |p.1 - q.1| = dist p.1 q.1 := by rw [Real.dist_eq] <;> rfl
      have hb : |p.2 - q.2| = dist p.2 q.2 := by rw [Real.dist_eq] <;> rfl
      rw [hmax, ha, hb]
      have h10 : dist p.1 q.1 ≤ max (dist p.1 q.1) (dist p.2 q.2) := le_max_left _ _
      have h11 : dist p.2 q.2 ≤ max (dist p.1 q.1) (dist p.2 q.2) := le_max_right _ _
      linarith
    rw [hdist]
    exact h1.trans hsum
  have h_lipschitz_sub : LipschitzWith 2 (fun p : ℝ × ℝ => p.1 - p.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    have h1 : |p.1 - p.2 - (q.1 - q.2)| ≤ |p.1 - q.1| + |p.2 - q.2| := by
      have h2 : p.1 - p.2 - (q.1 - q.2) = (p.1 - q.1) - (p.2 - q.2) := by ring
      rw [h2]
      exact abs_sub (p.1 - q.1) (p.2 - q.2)
    have hdist : dist (p.1 - p.2) (q.1 - q.2) = |p.1 - p.2 - (q.1 - q.2)| := by
      rw [Real.dist_eq] <;> rfl
    have hsum : |p.1 - q.1| + |p.2 - q.2| ≤ 2 * dist p q := by
      have hmax : dist p q = max (dist p.1 q.1) (dist p.2 q.2) := by rfl
      have ha : |p.1 - q.1| = dist p.1 q.1 := by rw [Real.dist_eq] <;> rfl
      have hb : |p.2 - q.2| = dist p.2 q.2 := by rw [Real.dist_eq] <;> rfl
      rw [hmax, ha, hb]
      have h10 : dist p.1 q.1 ≤ max (dist p.1 q.1) (dist p.2 q.2) := le_max_left _ _
      have h11 : dist p.2 q.2 ≤ max (dist p.1 q.1) (dist p.2 q.2) := le_max_right _ _
      linarith
    rw [hdist]
    exact h1.trans hsum
  have hAxA_bounded : Bornology.IsBounded (Set.image2 (fun a1 a2 : ℝ => a1 + x * a2) A A) := by
    have h_eq : Set.image2 (fun a1 a2 : ℝ => a1 + x * a2) A A = (fun p : ℝ × ℝ => p.1 + x * p.2) '' (A ×ˢ A) := by
      ext z; simp [Set.image2] <;> aesop
    rw [h_eq]
    exact h_lipschitz_add.isBounded_image (hA.prod hA)
  have hB1A_bounded : Bornology.IsBounded (Set.image2 (· - ·) B1 A) := by
    have h_eq : Set.image2 (· - ·) B1 A = (fun p : ℝ × ℝ => p.1 - p.2) '' (B1 ×ˢ A) := by
      ext z; simp [Set.image2] <;> aesop
    rw [h_eq]
    exact h_lipschitz_sub.isBounded_image (hB1.prod hA)
  have hB2A_bounded : Bornology.IsBounded (Set.image2 (· - ·) B2 A) := by
    have h_eq : Set.image2 (· - ·) B2 A = (fun p : ℝ × ℝ => p.1 - p.2) '' (B2 ×ˢ A) := by
      ext z; simp [Set.image2] <;> aesop
    rw [h_eq]
    exact h_lipschitz_sub.isBounded_image (hB2.prod hA)
  have hpi_bounded : Bornology.IsBounded (projectionSet x B) := projectionSet.bounded x hB

  -- Index sets
  let I_AxA : Set ℤ := {k | ∃ z ∈ Set.image2 (fun a1 a2 => a1 + x * a2) A A,
      δ * (k : ℝ) ≤ z ∧ z < δ * ((k : ℝ) + 1)}
  let I_B1A : Set ℤ := {k | ∃ w ∈ Set.image2 (· - ·) B1 A,
      δ * (k : ℝ) ≤ w ∧ w < δ * ((k : ℝ) + 1)}
  let I_B2A : Set ℤ := {k | ∃ w ∈ Set.image2 (· - ·) B2 A,
      δ * (k : ℝ) ≤ w ∧ w < δ * ((k : ℝ) + 1)}
  let I_pi : Set ℤ := {k | ∃ w ∈ projectionSet x B,
      δ * (k : ℝ) ≤ w ∧ w < δ * ((k : ℝ) + 1)}
  let I_B : Set (Fin 2 → ℤ) := {k | (dyadicCube δ k ∩ B).Nonempty}

  -- Finiteness and cardinality equality
  have ⟨hfin_AxA, hcard_AxA⟩ := real_index_set_finite_and_encard hδ hAxA_bounded
  have ⟨hfin_B1A, hcard_B1A⟩ := real_index_set_finite_and_encard hδ hB1A_bounded
  have ⟨hfin_B2A, hcard_B2A⟩ := real_index_set_finite_and_encard hδ hB2A_bounded
  have ⟨hfin_pi, hcard_pi⟩ := real_index_set_finite_and_encard hδ hpi_bounded
  have ⟨hfin_B, hcard_B⟩ := dyadic_index_set_finite_and_encard hδ hB

  -- Convert to finsets
  let s_AxA := hfin_AxA.toFinset
  let s_B1A := hfin_B1A.toFinset
  let s_B2A := hfin_B2A.toFinset
  let s_pi := hfin_pi.toFinset
  let s_B := hfin_B.toFinset

  have hs_AxA : (s_AxA : Set ℤ) = I_AxA := hfin_AxA.coe_toFinset
  have hs_B1A : (s_B1A : Set ℤ) = I_B1A := hfin_B1A.coe_toFinset
  have hs_B2A : (s_B2A : Set ℤ) = I_B2A := hfin_B2A.coe_toFinset
  have hs_pi : (s_pi : Set ℤ) = I_pi := hfin_pi.coe_toFinset
  have hs_B : (s_B : Set (Fin 2 → ℤ)) = I_B := hfin_B.coe_toFinset

  -- Choose points for A+x·A cubes
  have h_choice_AxA : ∀ (k : ℤ), k ∈ I_AxA →
      ∃ (a1 a2 : ℝ), a1 ∈ A ∧ a2 ∈ A ∧
        δ * (k : ℝ) ≤ a1 + x * a2 ∧ a1 + x * a2 < δ * ((k : ℝ) + 1) := by
    intro k hk
    rcases hk with ⟨z, hz, hz1, hz2⟩
    rcases Set.mem_image2.mp hz with ⟨a1, ha1, a2, ha2, rfl⟩
    exact ⟨a1, a2, ha1, ha2, hz1, hz2⟩
  classical
  let h_packed : ∀ (k : ℤ), ∃ (pr : ℝ × ℝ),
      (k ∈ I_AxA → pr.1 ∈ A ∧ pr.2 ∈ A ∧ δ * (k : ℝ) ≤ pr.1 + x * pr.2 ∧ pr.1 + x * pr.2 < δ * ((k : ℝ) + 1)) := by
    intro k
    by_cases hk : k ∈ I_AxA
    · rcases h_choice_AxA k hk with ⟨a1, a2, ha1, ha2, hz1, hz2⟩
      refine ⟨(a1, a2), fun _ => ⟨ha1, ha2, hz1, hz2⟩⟩
    · exact ⟨(0, 0), by tauto⟩
  choose data hdata using h_packed
  let a1 : ℤ → ℝ := fun k => (data k).1
  let a2 : ℤ → ℝ := fun k => (data k).2
  have ha1 : ∀ k, k ∈ I_AxA → a1 k ∈ A := fun k hk => (hdata k hk).1
  have ha2 : ∀ k, k ∈ I_AxA → a2 k ∈ A := fun k hk => (hdata k hk).2.1
  have hz1 : ∀ k, k ∈ I_AxA → δ * (k : ℝ) ≤ a1 k + x * a2 k := fun k hk => (hdata k hk).2.2.1
  have hz2 : ∀ k, k ∈ I_AxA → a1 k + x * a2 k < δ * ((k : ℝ) + 1) := fun k hk => (hdata k hk).2.2.2

  -- Choose points for B cubes
  have h_choice_B : ∀ (k' : Fin 2 → ℤ), k' ∈ I_B →
      ∃ (p : EuclideanSpace ℝ (Fin 2)), p ∈ B ∧
        ∀ i, δ * (k' i : ℝ) ≤ p i ∧ p i < δ * ((k' i : ℝ) + 1) := by
    intro k' hk
    rcases hk with ⟨p, hp_cube, hp_B⟩
    exact ⟨p, hp_B, hp_cube⟩
  let h_packed_B : ∀ (k' : Fin 2 → ℤ), ∃ (p : EuclideanSpace ℝ (Fin 2)),
      (k' ∈ I_B → p ∈ B ∧ ∀ i, δ * (k' i : ℝ) ≤ p i ∧ p i < δ * ((k' i : ℝ) + 1)) := by
    intro k'
    by_cases hk : k' ∈ I_B
    · rcases h_choice_B k' hk with ⟨p, hpB, hpk⟩
      refine ⟨p, fun _ => ⟨hpB, hpk⟩⟩
    · exact ⟨0, by tauto⟩
  choose p hpdata using h_packed_B
  have hp : ∀ k', k' ∈ I_B → p k' ∈ B := fun k' hk => (hpdata k' hk).1
  have hpk : ∀ k', k' ∈ I_B → ∀ i, δ * (k' i : ℝ) ≤ p k' i ∧ p k' i < δ * ((k' i : ℝ) + 1) := fun k' hk => (hpdata k' hk).2

  -- The cube-mapping f
  let f : ℤ × (Fin 2 → ℤ) → ℤ × ℤ × ℤ := fun q =>
    (Int.floor (((p q.2) 0 - a2 q.1) / δ),
     Int.floor (((p q.2) 1 - a1 q.1) / δ),
     Int.floor ((x * (p q.2) 0 + (p q.2) 1) / δ))

  -- Image containment
  have h_image : ∀ (q : ℤ × (Fin 2 → ℤ)), q.1 ∈ s_AxA → q.2 ∈ s_B →
      f q ∈ s_B1A ×ˢ s_B2A ×ˢ s_pi := by
    rintro ⟨k, k'⟩ hk hk'
    have hk_I : k ∈ I_AxA := by have h : k ∈ (s_AxA : Set ℤ) := hk; rw [hs_AxA] at h; exact h
    have hk'_I : k' ∈ I_B := by have h : k' ∈ (s_B : Set (Fin 2 → ℤ)) := hk'; rw [hs_B] at h; exact h
    set b0 := (p k') 0 with hb0_def
    set b1 := (p k') 1 with hb1_def
    have hb0 : b0 ∈ B1 := (hB_sub (p k') (hp k' hk'_I)).1
    have hb1 : b1 ∈ B2 := (hB_sub (p k') (hp k' hk'_I)).2
    have h1 : b0 - a2 k ∈ Set.image2 (· - ·) B1 A := by
      exact ⟨b0, hb0, a2 k, ha2 k hk_I, by ring⟩
    have h2 : b1 - a1 k ∈ Set.image2 (· - ·) B2 A := by
      exact ⟨b1, hb1, a1 k, ha1 k hk_I, by ring⟩
    have h3 : x * b0 + b1 ∈ projectionSet x B := by
      refine ⟨p k', hp k' hk'_I, ?_⟩
      simp [hb0_def, hb1_def] <;> ring
    let u1 := Int.floor (((b0 - a2 k) / δ))
    let u2 := Int.floor (((b1 - a1 k) / δ))
    let u3 := Int.floor ((x * b0 + b1) / δ)
    have hu1 : u1 ∈ I_B1A := ⟨b0 - a2 k, h1, floor_mul_le hδ, lt_floor_add_one_mul hδ⟩
    have hu2 : u2 ∈ I_B2A := ⟨b1 - a1 k, h2, floor_mul_le hδ, lt_floor_add_one_mul hδ⟩
    have hu3 : u3 ∈ I_pi := ⟨x * b0 + b1, h3, floor_mul_le hδ, lt_floor_add_one_mul hδ⟩
    have hu1s : u1 ∈ s_B1A := by
      have h : u1 ∈ (s_B1A : Set ℤ) := by
        simpa [hs_B1A] using hu1
      exact Finset.mem_coe.mp h
    have hu2s : u2 ∈ s_B2A := by
      have h : u2 ∈ (s_B2A : Set ℤ) := by
        simpa [hs_B2A] using hu2
      exact Finset.mem_coe.mp h
    have hu3s : u3 ∈ s_pi := by
      have h : u3 ∈ (s_pi : Set ℤ) := by
        simpa [hs_pi] using hu3
      exact Finset.mem_coe.mp h
    simp only [f, Finset.mem_product]
    exact ⟨hu1s, hu2s, hu3s⟩

  -- Fiber bound: at most 16 preimages per output triple
  have h_fiber : ∀ (y : ℤ × ℤ × ℤ),
      ((s_AxA ×ˢ s_B).filter (fun q => f q = y)).card ≤ 16 := by
    rintro ⟨u, v, w⟩
    let F := (s_AxA ×ˢ s_B).filter (fun q => f q = (u, v, w))
    let g : ℤ × (Fin 2 → ℤ) → ℤ := fun q => q.1
    let K : Finset ℤ := F.image g

    -- Step 1: |K| ≤ 4
    have h_K_le4 : K.card ≤ 4 := by
      let c : ℝ := δ * ((w : ℝ) + 1 / 2) - x * δ * ((u : ℝ) + 1 / 2) - δ * ((v : ℝ) + 1 / 2)
      let L : ℝ := c - 3 * δ / 2
      let U : ℝ := c + 3 * δ / 2
      have h_k_in_set : ∀ k ∈ K, k ∈ {k : ℤ | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ Set.Ico L U).Nonempty} := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨q, hqF, rfl⟩
        have hqF' : q ∈ (s_AxA ×ˢ s_B) ∧ f q = (u, v, w) := Finset.mem_filter.mp hqF
        have hq1 : q.1 ∈ s_AxA := (Finset.mem_product.mp hqF'.1).1
        have hq2 : q.2 ∈ s_B := (Finset.mem_product.mp hqF'.1).2
        have h_eq : f q = (u, v, w) := hqF'.2
        set k := q.1 with hk_def
        set k' := q.2 with hk'_def
        have hk_I : k ∈ I_AxA := by have h : k ∈ (s_AxA : Set ℤ) := hq1; rw [hs_AxA] at h; exact h
        have h_eq1 : Int.floor (((p k') 0 - a2 k) / δ) = u := by
          simpa [f] using congr_arg (fun x : ℤ × ℤ × ℤ => x.1) h_eq
        have h_eq2 : Int.floor (((p k') 1 - a1 k) / δ) = v := by
          simpa [f] using congr_arg (fun x : ℤ × ℤ × ℤ => x.2.1) h_eq
        have h_eq3 : Int.floor ((x * (p k') 0 + (p k') 1) / δ) = w := by
          simpa [f] using congr_arg (fun x : ℤ × ℤ × ℤ => x.2.2) h_eq
        set b0 := (p k') 0 with hb0_def
        set b1 := (p k') 1 with hb1_def
        set z := a1 k + x * a2 k with hz_def
        have h_z1 : δ * (k : ℝ) ≤ z := hz1 k hk_I
        have h_z2 : z < δ * ((k : ℝ) + 1) := hz2 k hk_I
        have h_t1 : δ * (w : ℝ) ≤ x * b0 + b1 := by
          have h : δ * (Int.floor ((x * b0 + b1) / δ) : ℝ) ≤ x * b0 + b1 := floor_mul_le hδ
          rw [h_eq3] at h; exact h
        have h_t2 : x * b0 + b1 < δ * ((w : ℝ) + 1) := by
          have h : x * b0 + b1 < δ * ((Int.floor ((x * b0 + b1) / δ) : ℝ) + 1) := lt_floor_add_one_mul hδ
          rw [h_eq3] at h; exact h
        have h_s1 : δ * (u : ℝ) ≤ b0 - a2 k := by
          have h : δ * (Int.floor (((b0 - a2 k) / δ)) : ℝ) ≤ b0 - a2 k := floor_mul_le hδ
          rw [h_eq1] at h; exact h
        have h_s2 : b0 - a2 k < δ * ((u : ℝ) + 1) := by
          have h : b0 - a2 k < δ * ((Int.floor (((b0 - a2 k) / δ)) : ℝ) + 1) := lt_floor_add_one_mul hδ
          rw [h_eq1] at h; exact h
        have h_s3 : δ * (v : ℝ) ≤ b1 - a1 k := by
          have h : δ * (Int.floor (((b1 - a1 k) / δ)) : ℝ) ≤ b1 - a1 k := floor_mul_le hδ
          rw [h_eq2] at h; exact h
        have h_s4 : b1 - a1 k < δ * ((v : ℝ) + 1) := by
          have h : b1 - a1 k < δ * ((Int.floor (((b1 - a1 k) / δ)) : ℝ) + 1) := lt_floor_add_one_mul hδ
          rw [h_eq2] at h; exact h
        have h_z_eq : z = (x * b0 + b1) - x * (b0 - a2 k) - (b1 - a1 k) := by
          simp [hz_def] <;> ring
        have h_lo : L < z := by
          rw [h_z_eq]; simp only [L, c]
          rcases abs_cases x with (hxn | hxp) <;> nlinarith
        have h_hi : z < U := by
          rw [h_z_eq]; simp only [U, c]
          rcases abs_cases x with (hxn | hxp) <;> nlinarith
        exact ⟨z, ⟨h_z1, h_z2⟩, ⟨le_of_lt h_lo, h_hi⟩⟩
      have h_UL : U - L ≤ 3 * δ := by
        dsimp only [U, L, c]
        <;> linarith
      have h_set_le4 : Set.encard {k : ℤ | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ Set.Ico L U).Nonempty} ≤ 4 :=
        cubes_meeting_interval_le4 hδ h_UL
      have hK_sub : (K : Set ℤ) ⊆ {k : ℤ | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ Set.Ico L U).Nonempty} :=
        by intro k hk; exact h_k_in_set k hk
      have h : (K : Set ℤ).encard ≤ Set.encard {k : ℤ | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ Set.Ico L U).Nonempty} :=
        Set.encard_mono hK_sub
      have h' : (K : Set ℤ).encard = ↑K.card := by simp
      rw [h'] at h
      exact_mod_cast (h.trans h_set_le4)

    -- Step 2: for each k ∈ K, the k-fiber has size ≤ 4
    have h_kfiber_le4 : ∀ k ∈ K, (F.filter (fun q => q.1 = k)).card ≤ 4 := by
      intro k hk
      have h_k_in_AxA : k ∈ s_AxA := by
        rcases Finset.mem_image.mp hk with ⟨q, hqF, rfl⟩
        have hqF' : q ∈ (s_AxA ×ˢ s_B) ∧ f q = (u, v, w) := Finset.mem_filter.mp hqF
        exact (Finset.mem_product.mp hqF'.1).1
      have hk_I : k ∈ I_AxA := by have h : k ∈ (s_AxA : Set ℤ) := h_k_in_AxA; rw [hs_AxA] at h; exact h
      let S0 : Set ℤ := {k0 | (Set.Ico (δ * (k0 : ℝ)) (δ * ((k0 : ℝ) + 1)) ∩
          Set.Ico (a2 k + δ * (u : ℝ)) (a2 k + δ * ((u : ℝ) + 1))).Nonempty}
      let S1 : Set ℤ := {k1 | (Set.Ico (δ * (k1 : ℝ)) (δ * ((k1 : ℝ) + 1)) ∩
          Set.Ico (a1 k + δ * (v : ℝ)) (a1 k + δ * ((v : ℝ) + 1))).Nonempty}
      have hS0_len : (a2 k + δ * ((u : ℝ) + 1)) - (a2 k + δ * (u : ℝ)) ≤ δ := by linarith
      have hS1_len : (a1 k + δ * ((v : ℝ) + 1)) - (a1 k + δ * (v : ℝ)) ≤ δ := by linarith
      have hS0_le2 : Set.encard S0 ≤ 2 := cubes_meeting_interval_le2 hδ hS0_len
      have hS1_le2 : Set.encard S1 ≤ 2 := cubes_meeting_interval_le2 hδ hS1_len
      have hS0_finite : S0.Finite := Set.finite_of_encard_le_coe hS0_le2
      have hS1_finite : S1.Finite := Set.finite_of_encard_le_coe hS1_le2
      let f0 := hS0_finite.toFinset
      let f1 := hS1_finite.toFinset
      have hf0_card : f0.card ≤ 2 := by
        have h : (f0 : Set ℤ) = S0 := hS0_finite.coe_toFinset
        have h_eq : (f0.card : ENat) = Set.encard (f0 : Set ℤ) := by exact Eq.symm (Set.encard_coe_eq_coe_finsetCard f0)
        have h' : (f0.card : ENat) ≤ 2 := by rw [h_eq, h]; exact hS0_le2
        exact_mod_cast h'
      have hf1_card : f1.card ≤ 2 := by
        have h : (f1 : Set ℤ) = S1 := hS1_finite.coe_toFinset
        have h_eq : (f1.card : ENat) = Set.encard (f1 : Set ℤ) := by exact Eq.symm (Set.encard_coe_eq_coe_finsetCard f1)
        have h' : (f1.card : ENat) ≤ 2 := by rw [h_eq, h]; exact hS1_le2
        exact_mod_cast h'
      let e : (Fin 2 → ℤ) ≃ ℤ × ℤ :=
        { toFun := fun k' => (k' 0, k' 1)
          invFun := fun p => fun i => if i = 0 then p.1 else p.2
          left_inv := by intro k'; funext i; fin_cases i <;> simp
          right_inv := by intro p; simp }
      let possible_k' : Finset (Fin 2 → ℤ) := (f0 ×ˢ f1).image e.symm
      have h_possible_card : possible_k'.card ≤ 4 := by
        have h : possible_k'.card = (f0 ×ˢ f1).card := by
          apply Finset.card_image_of_injective; exact e.symm.injective
        rw [h, Finset.card_product] <;> nlinarith
      let F_k : Finset (Fin 2 → ℤ) := s_B.filter (fun k' => f (k, k') = (u, v, w))
      have h_Fk_subset : F_k ⊆ possible_k' := by
        intro k' hk'
        have h_k'_in_B : k' ∈ s_B := (Finset.mem_filter.mp hk').1
        have h_eq : f (k, k') = (u, v, w) := (Finset.mem_filter.mp hk').2
        have h_k'_I : k' ∈ I_B := by have h : k' ∈ (s_B : Set (Fin 2 → ℤ)) := h_k'_in_B; rw [hs_B] at h; exact h
        have h_eq1 : Int.floor (((p k') 0 - a2 k) / δ) = u := by
          simpa [f] using congr_arg (fun x : ℤ × ℤ × ℤ => x.1) h_eq
        have h_eq2 : Int.floor (((p k') 1 - a1 k) / δ) = v := by
          simpa [f] using congr_arg (fun x : ℤ × ℤ × ℤ => x.2.1) h_eq
        set b0 := (p k') 0 with hb0_def
        set b1 := (p k') 1 with hb1_def
        have h_b0_in : b0 ∈ Set.Ico (a2 k + δ * (u : ℝ)) (a2 k + δ * ((u : ℝ) + 1)) := by
          have h1 : δ * (u : ℝ) ≤ b0 - a2 k := by
            have h : δ * (Int.floor (((b0 - a2 k) / δ)) : ℝ) ≤ b0 - a2 k := floor_mul_le hδ
            rw [h_eq1] at h; exact h
          have h2 : b0 - a2 k < δ * ((u : ℝ) + 1) := by
            have h : b0 - a2 k < δ * ((Int.floor (((b0 - a2 k) / δ)) : ℝ) + 1) := lt_floor_add_one_mul hδ
            rw [h_eq1] at h; exact h
          exact ⟨by linarith, by linarith⟩
        have h_b1_in : b1 ∈ Set.Ico (a1 k + δ * (v : ℝ)) (a1 k + δ * ((v : ℝ) + 1)) := by
          have h1 : δ * (v : ℝ) ≤ b1 - a1 k := by
            have h : δ * (Int.floor (((b1 - a1 k) / δ)) : ℝ) ≤ b1 - a1 k := floor_mul_le hδ
            rw [h_eq2] at h; exact h
          have h2 : b1 - a1 k < δ * ((v : ℝ) + 1) := by
            have h : b1 - a1 k < δ * ((Int.floor (((b1 - a1 k) / δ)) : ℝ) + 1) := lt_floor_add_one_mul hδ
            rw [h_eq2] at h; exact h
          exact ⟨by linarith, by linarith⟩
        have h_k'0_in_S0 : k' 0 ∈ S0 := by
          exact ⟨b0, hpk k' h_k'_I 0, h_b0_in⟩
        have h_k'1_in_S1 : k' 1 ∈ S1 := by
          exact ⟨b1, hpk k' h_k'_I 1, h_b1_in⟩
        have h_e : e k' ∈ f0 ×ˢ f1 := by
          simp only [e, Finset.mem_product]
          exact ⟨by simpa [f0, hS0_finite.coe_toFinset] using h_k'0_in_S0,
                     by simpa [f1, hS1_finite.coe_toFinset] using h_k'1_in_S1⟩
        exact Finset.mem_image.mpr ⟨e k', h_e, by simp⟩
      have h_filter_eq : (F.filter (fun q => q.1 = k)) = ({k} : Finset ℤ) ×ˢ F_k := by
        ext ⟨k1, k'⟩
        simp only [F, F_k, Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨⟨hk1, hk'⟩, h_eq⟩, rfl⟩
          exact ⟨rfl, hk', h_eq⟩
        · rintro ⟨h_k1_eq, hk', h_eq⟩
          have h_k1_eq' : k1 = k := by simpa using h_k1_eq
          have h_k1_in_AxA : k1 ∈ s_AxA := by rw [h_k1_eq']; exact h_k_in_AxA
          have h_eq' : f (k1, k') = (u, v, w) := by rw [h_k1_eq']; exact h_eq
          have h4 : (k1 ∈ s_AxA ∧ k' ∈ s_B) ∧ f (k1, k') = (u, v, w) := ⟨⟨h_k1_in_AxA, hk'⟩, h_eq'⟩
          exact ⟨h4, by simpa using h_k1_eq⟩
      rw [h_filter_eq]
      have h_card : (({k} : Finset ℤ) ×ˢ F_k).card = F_k.card := by
        rw [Finset.card_product, Finset.card_singleton] <;> ring
      rw [h_card]
      exact (Finset.card_le_card h_Fk_subset).trans h_possible_card

    -- Step 3: |F| ≤ 4 * |K| ≤ 16
    have h_main_count : F.card ≤ 4 * K.card :=
      finset_card_le_mul_of_bounded_fibers g
        (fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩)
        (fun k hk => h_kfiber_le4 k hk)
    have h_final : F.card ≤ 16 := by
      calc F.card ≤ 4 * K.card := h_main_count
        _ ≤ 4 * 4 := by gcongr
        _ = 16 := by norm_num
    exact h_final

  -- Counting
  let t := s_B1A ×ˢ s_B2A ×ˢ s_pi
  have h1 : ∀ q ∈ (s_AxA ×ˢ s_B), f q ∈ t := by
    intro q hq
    have hq1 : q.1 ∈ s_AxA := (Finset.mem_product.mp hq).1
    have hq2 : q.2 ∈ s_B := (Finset.mem_product.mp hq).2
    exact h_image q hq1 hq2
  have h_fiber' : ∀ y ∈ t, ((s_AxA ×ˢ s_B).filter (fun q => f q = y)).card ≤ 16 := by
    intro y _
    exact h_fiber y
  have h_main : (s_AxA ×ˢ s_B).card ≤ 16 * t.card :=
    finset_card_le_mul_of_bounded_fibers f h1 h_fiber'
  have h_card_prod1 : (s_AxA ×ˢ s_B).card = s_AxA.card * s_B.card := by
    simp [Finset.card_product] <;> ring
  have h_card_prod2 : t.card = s_B1A.card * s_B2A.card * s_pi.card := by
    simp [t, Finset.card_product] <;> ring
  rw [h_card_prod1, h_card_prod2] at h_main

  -- Convert to ENNReal
  have h_enn : (↑(s_AxA.card * s_B.card) : ENNReal) ≤
      (↑(16 * s_B1A.card * s_B2A.card * s_pi.card) : ENNReal) := by
    have h_main' : s_AxA.card * s_B.card ≤ 16 * s_B1A.card * s_B2A.card * s_pi.card := by
      have h : 16 * (s_B1A.card * s_B2A.card * s_pi.card) = 16 * s_B1A.card * s_B2A.card * s_pi.card := by ring
      rw [h] at h_main
      exact h_main
    exact_mod_cast h_main'
  have h_mul1 : (↑(s_AxA.card * s_B.card) : ENNReal) =
      (↑s_AxA.card : ENNReal) * (↑s_B.card : ENNReal) := by
    simp [Nat.cast_mul]
  have h_mul2 : (↑(16 * s_B1A.card * s_B2A.card * s_pi.card) : ENNReal) =
      16 * (↑s_B1A.card : ENNReal) * (↑s_B2A.card : ENNReal) * (↑s_pi.card : ENNReal) := by
    simp [Nat.cast_mul] <;> ring
  rw [h_mul1, h_mul2] at h_enn

  -- Relate finset cards to covering numbers
  have h_card_eq : ∀ {α : Type _} (s : Finset α) (I : Set α) (hs : (s : Set α) = I),
      (I.encard : ENNReal) = (↑s.card : ENNReal) := by
    intro α s I hs
    have h_eq1 : I.encard = (s : Set α).encard := by rw [hs.symm]
    have h_eq2 : (s : Set α).encard = ↑s.card := by
      exact Set.encard_coe_eq_coe_finsetCard s
    have h_eq3 : I.encard = ↑s.card := by rw [h_eq1, h_eq2]
    exact congr_arg (fun x : ℕ∞ => (x : ENNReal)) h_eq3
  have h_to_enn_AxA : (↑s_AxA.card : ENNReal) = ENat.toENNReal (dyadicCoveringNumber (d := 1) δ
        (_root_.productLikeRealLineCopy (Set.image2 (fun a1 a2 => a1 + x * a2) A A))) := by
    have h : (I_AxA.encard : ENNReal) = (↑s_AxA.card : ENNReal) := h_card_eq s_AxA I_AxA hs_AxA
    have h2 : I_AxA.encard = dyadicCoveringNumber (d := 1) δ
          (_root_.productLikeRealLineCopy (Set.image2 (fun a1 a2 => a1 + x * a2) A A)) := hcard_AxA
    rw [←h2]
    exact h.symm
  have h_to_enn_B : (↑s_B.card : ENNReal) = ENat.toENNReal (dyadicCoveringNumber δ B) := by
    have h := h_card_eq s_B I_B hs_B
    have h2 : (I_B.encard : ENNReal) = ENat.toENNReal (dyadicCoveringNumber δ B) :=
      congr_arg ENat.toENNReal hcard_B
    exact h.symm.trans h2
  have h_to_enn_B1A : (↑s_B1A.card : ENNReal) = ENat.toENNReal (dyadicCoveringNumber δ
        (_root_.productLikeRealLineCopy (Set.image2 (· - ·) B1 A))) := by
    have h := h_card_eq s_B1A I_B1A hs_B1A
    have h2 : (I_B1A.encard : ENNReal) = ENat.toENNReal (dyadicCoveringNumber δ
          (_root_.productLikeRealLineCopy (Set.image2 (· - ·) B1 A))) :=
      congr_arg ENat.toENNReal hcard_B1A
    exact h.symm.trans h2
  have h_to_enn_B2A : (↑s_B2A.card : ENNReal) = ENat.toENNReal (dyadicCoveringNumber δ
        (_root_.productLikeRealLineCopy (Set.image2 (· - ·) B2 A))) := by
    have h := h_card_eq s_B2A I_B2A hs_B2A
    have h2 : (I_B2A.encard : ENNReal) = ENat.toENNReal (dyadicCoveringNumber δ
          (_root_.productLikeRealLineCopy (Set.image2 (· - ·) B2 A))) :=
      congr_arg ENat.toENNReal hcard_B2A
    exact h.symm.trans h2
  have h_to_enn_pi : (↑s_pi.card : ENNReal) = ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D x B)) := by
    have h := h_card_eq s_pi I_pi hs_pi
    have h2 : (I_pi.encard : ENNReal) = ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D x B)) := by
      have h3 : projectionSet1D x B = _root_.productLikeRealLineCopy (projectionSet x B) := by rfl
      rw [h3]
      exact congr_arg ENat.toENNReal hcard_pi
    exact h.symm.trans h2

  rw [h_to_enn_AxA, h_to_enn_B, h_to_enn_B1A, h_to_enn_B2A, h_to_enn_pi] at h_enn
  exact h_enn

end bourgain_projection_theorem
