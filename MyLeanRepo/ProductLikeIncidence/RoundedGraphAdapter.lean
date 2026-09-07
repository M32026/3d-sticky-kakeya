module

/-
# Rounded Graph Adapter

Bridge from threefold-selected E3' (already projectively normalized)
to the dense rounded graph Gamma ⊆ S1 × S2 required by BSG.

The projective map G does NOT occur here — E3' is already the projected set.

## Key results

- `rounded_graph_adapter`: Given E3' with density c_dense * N(S1) * N(S2) ≤ Nplane(E3'),
  produces Gamma ⊆ S1 × S2 with:
  - Density: Nplane(Gamma) ≥ (c_dense/4) * N(S1) * N(S2) [factor 4 from 2D rounding]
  - Sumset: N(thirdProj(Gamma)) ≤ 3 * N(thirdProj(E3')) [factor 3 from 1D δ-neighborhood]

## Whiteprint node

`rounded_graph_adapter`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProductLikeSetBasics
public import MyLeanRepo.CubeIndexSet
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set ENNReal Bornology

noncomputable section

namespace ProductLikeIncidence

/-- Cube index of a point in 2D. -/
def cubeIndexOfPoint (δ : ℝ) (p : EuclideanSpace ℝ (Fin 2)) : Fin 2 → ℤ :=
  fun i => Int.floor (p i / δ)

lemma cubeIndexOfPoint_mem {δ : ℝ} (hδ : 0 < δ) (p : EuclideanSpace ℝ (Fin 2)) :
    p ∈ dyadicCube δ (cubeIndexOfPoint δ p) := by
  intro i
  have h1 : δ * ((Int.floor (p i / δ) : ℝ)) ≤ p i := by
    have h2 : (Int.floor (p i / δ) : ℝ) ≤ p i / δ := Int.floor_le (p i / δ)
    have h3 : δ * (Int.floor (p i / δ) : ℝ) ≤ δ * (p i / δ) := by gcongr
    have h4 : δ * (p i / δ) = p i := by field_simp [hδ.ne']
    linarith
  have h2 : p i < δ * ((Int.floor (p i / δ) : ℝ) + 1) := by
    have h3 : p i / δ < (Int.floor (p i / δ) : ℝ) + 1 := Int.lt_floor_add_one (p i / δ)
    have h4 : δ * (p i / δ) < δ * ((Int.floor (p i / δ) : ℝ) + 1) := by gcongr
    have h5 : δ * (p i / δ) = p i := by field_simp [hδ.ne']
    linarith
  exact ⟨h1, h2⟩

/-- If x is within δ/2 of grid point δ*a, then floor(x/δ) is a-1 or a. -/
lemma floor_near_grid {δ : ℝ} (hδ : 0 < δ) {x : ℝ} {a : ℤ}
    (h : |x - δ * (a : ℝ)| ≤ δ / 2) :
    Int.floor (x / δ) = a - 1 ∨ Int.floor (x / δ) = a := by
  have hne : δ ≠ 0 := hδ.ne'
  have h2 : -(δ / 2) ≤ x - δ * (a : ℝ) := (abs_le.mp h).1
  have h3 : x - δ * (a : ℝ) ≤ δ / 2 := (abs_le.mp h).2
  have h1 : (a : ℝ) - 1 / 2 ≤ x / δ := by
    have h4 : δ * ((a : ℝ) - 1 / 2) ≤ x := by
      have h5 : δ * ((a : ℝ) - 1 / 2) = δ * (a : ℝ) - δ / 2 := by ring
      rw [h5]
      linarith
    calc (a : ℝ) - 1 / 2
      = (δ * ((a : ℝ) - 1 / 2)) / δ := by field_simp [hne] <;> ring
    _ ≤ x / δ := by gcongr
  have h2' : x / δ ≤ (a : ℝ) + 1 / 2 := by
    have h4 : x ≤ δ * ((a : ℝ) + 1 / 2) := by
      have h5 : δ * ((a : ℝ) + 1 / 2) = δ * (a : ℝ) + δ / 2 := by ring
      rw [h5]
      linarith
    calc x / δ
      ≤ (δ * ((a : ℝ) + 1 / 2)) / δ := by gcongr
    _ = (a : ℝ) + 1 / 2 := by field_simp [hne] <;> ring
  let k := Int.floor (x / δ)
  have hk1 : (k : ℝ) ≤ x / δ := Int.floor_le (x / δ)
  have hk2 : x / δ < (k : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
  have h5 : (k : ℝ) ≤ (a : ℝ) + 1 / 2 := by linarith
  have h6 : k ≤ a := by
    by_contra h
    have h7 : a + 1 ≤ k := by omega
    have h8 : (a : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h7
    linarith
  have h8 : (a : ℝ) - 3 / 2 < (k : ℝ) := by linarith
  have h9 : a - 1 ≤ k := by
    by_contra h
    have h10 : k ≤ a - 2 := by omega
    have h11 : (k : ℝ) ≤ (a : ℝ) - 2 := by exact_mod_cast h10
    linarith
  omega

/-- The map k ↦ dyadicCube δ k is injective in 2D. -/
lemma dyadicCube2_injective {δ : ℝ} (hδ : 0 < δ) :
    Function.Injective (fun (k : Fin 2 → ℤ) => dyadicCube δ k) := by
  intro k1 k2 h
  funext i
  let p : EuclideanSpace ℝ (Fin 2) :=
    (WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun j => δ * (k1 j))
  have hp_i : p i = δ * (k1 i) := by simp [p]
  have hp_in_cube1 : p ∈ dyadicCube δ k1 := by
    intro j
    have h_left : δ * (k1 j : ℝ) ≤ p j := by simp [p] <;> linarith
    have h_right : p j < δ * ((k1 j : ℝ) + 1) := by simp [p] <;> linarith [hδ]
    exact ⟨h_left, h_right⟩
  have h' : dyadicCube δ k1 = dyadicCube δ k2 := by simpa using h
  have hp_in_cube2 : p ∈ dyadicCube δ k2 := by
    have h_rw : p ∈ dyadicCube δ k1 := hp_in_cube1
    rw [h'] at h_rw
    exact h_rw
  have h4 : p i ∈ Set.Ico (δ * (k2 i : ℝ)) (δ * ((k2 i : ℝ) + 1)) := hp_in_cube2 i
  have h5 : δ * (k2 i : ℝ) ≤ p i := h4.1
  have h6 : p i < δ * ((k2 i : ℝ) + 1) := h4.2
  rw [hp_i] at h5 h6
  have h7 : (k2 i : ℝ) ≤ (k1 i : ℝ) := by
    have h72 : (δ * (k2 i : ℝ)) / δ ≤ (δ * (k1 i : ℝ)) / δ := by gcongr
    have h73 : (δ * (k2 i : ℝ)) / δ = (k2 i : ℝ) := by field_simp [hδ.ne']
    have h74 : (δ * (k1 i : ℝ)) / δ = (k1 i : ℝ) := by field_simp [hδ.ne']
    rw [h73, h74] at h72
    exact h72
  have h8 : (k1 i : ℝ) < (k2 i : ℝ) + 1 := by
    have h82 : (δ * (k1 i : ℝ)) / δ < (δ * ((k2 i : ℝ) + 1)) / δ := by gcongr
    have h83 : (δ * (k1 i : ℝ)) / δ = (k1 i : ℝ) := by field_simp [hδ.ne']
    have h84 : (δ * ((k2 i : ℝ) + 1)) / δ = (k2 i : ℝ) + 1 := by field_simp [hδ.ne']
    rw [h83, h84] at h82
    exact h82
  have h9 : k2 i ≤ k1 i := by exact_mod_cast h7
  have h10 : k1 i ≤ k2 i := by
    have h11 : k1 i < k2 i + 1 := by exact_mod_cast h8
    omega
  exact le_antisymm h10 h9

/-- For a finite 2D set A, covering number = number of distinct cube indices. -/
lemma finite_covering2_eq_card {δ : ℝ} (hδ : 0 < δ) {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : A.Finite) :
    ENat.toENNReal (dyadicCoveringNumber δ A) =
      ↑(hA.toFinset.image (cubeIndexOfPoint δ)).card := by
  let Af := hA.toFinset
  let g := cubeIndexOfPoint δ
  let f : (Fin 2 → ℤ) → Set (EuclideanSpace ℝ (Fin 2)) := fun k => dyadicCube δ k
  have hAf : (Af : Set _) = A := hA.coe_toFinset
  have h_inj : Function.Injective f := dyadicCube2_injective hδ

  have h1 : dyadicCubesMeeting δ A = f '' (g '' A) := by
    ext Q
    simp only [dyadicCubesMeeting, dyadicCubes, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨k, rfl⟩, ⟨p, hpQ, hpA⟩⟩
      have hgk : g p = k := by
        funext i
        have hpi : p i ∈ Set.Ico (δ * (k i : ℝ)) (δ * ((k i : ℝ) + 1)) := hpQ i
        have h_floor : Int.floor (p i / δ) = k i := by
          rw [Int.floor_eq_iff]
          constructor
          · have h_le : (k i : ℝ) ≤ p i / δ := by
              have h : δ * (k i : ℝ) ≤ p i := hpi.1
              calc (k i : ℝ) = (δ * (k i : ℝ)) / δ := by field_simp [hδ.ne']
                _ ≤ p i / δ := by gcongr
            exact_mod_cast h_le
          · have h_lt : p i / δ < (k i : ℝ) + 1 := by
              have h : p i < δ * ((k i : ℝ) + 1) := hpi.2
              calc p i / δ < (δ * ((k i : ℝ) + 1)) / δ := by gcongr
                _ = (k i : ℝ) + 1 := by field_simp [hδ.ne']
            exact_mod_cast h_lt
        simpa [g, cubeIndexOfPoint] using h_floor
      exact ⟨k, ⟨p, hpA, hgk⟩, rfl⟩
    · intro h
      rcases h with ⟨k, ⟨p, hpA, hgk⟩, rfl⟩
      have hQ1 : dyadicCube δ k ∈ dyadicCubes 2 δ := ⟨k, rfl⟩
      have hQ2 : p ∈ dyadicCube δ k := by
        rw [←hgk]
        exact cubeIndexOfPoint_mem hδ p
      exact ⟨hQ1, p, hQ2, hpA⟩

  have h_finite_idx : (g '' A).Finite := hA.image g
  let IdxFinset := Af.image g
  have h_idx_coe : (IdxFinset : Set (Fin 2 → ℤ)) = g '' A := by
    ext x
    simp only [IdxFinset, Finset.mem_coe, Finset.mem_image, Set.mem_image, hAf]
    <;> aesop

  have h_finite_cubes : (dyadicCubesMeeting δ A).Finite := by
    have h2 : (f '' (g '' A)).Finite := h_finite_idx.image f
    rwa [h1]

  let CubesFinset := h_finite_cubes.toFinset
  have h_cubes_coe : (CubesFinset : Set _) = dyadicCubesMeeting δ A :=
    h_finite_cubes.coe_toFinset

  have h_eq : CubesFinset = IdxFinset.image f := by
    apply Finset.coe_inj.mp
    ext Q
    simp only [Finset.mem_coe, Finset.mem_image, h_cubes_coe, h1, h_idx_coe, Set.mem_image]
    <;> aesop

  have h_card : CubesFinset.card = IdxFinset.card := by
    rw [h_eq]
    apply Finset.card_image_of_injective
    exact h_inj

  have h_encard : (dyadicCubesMeeting δ A).encard = ↑CubesFinset.card := by
    rw [← h_cubes_coe]
    exact Set.encard_coe_eq_coe_finsetCard CubesFinset

  rw [dyadicCoveringNumber, h_encard, h_card]
  <;> rfl

/-- Nreal is monotone in the set argument. -/
lemma Nreal_mono' {δ : ℝ} {A B : Set ℝ} (h : A ⊆ B) :
    Nreal δ A ≤ Nreal δ B := by
  dsimp only [Nreal]
  apply ENat.toENNReal_mono
  apply Set.encard_mono
  intro Q hQ
  have hRL : realLineCopy A ⊆ realLineCopy B := by
    intro x hx
    simpa [realLineCopy] using h (by simpa [realLineCopy] using hx)
  exact ⟨hQ.1, hQ.2.mono (Set.inter_subset_inter_right _ hRL)⟩

/-- **1D δ-neighborhood covering bound.**

If every point of `B` is within distance `δ` of some point of `A`, then
the δ-dyadic covering number of `B` is at most `3` times that of `A`. -/
lemma neighborhood_covering_bound {δ : ℝ} (hδ_pos : 0 < δ)
    {A B : Set ℝ} (h_near : ∀ b ∈ B, ∃ a ∈ A, |b - a| ≤ δ) :
    Nreal δ B ≤ 3 * Nreal δ A := by
  let idxA : Set ℤ := {k | ∃ x ∈ A, x ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1))}
  let idxB : Set ℤ := {k | ∃ x ∈ B, x ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1))}
  let cubeMap (k : ℤ) : Set (EuclideanSpace ℝ (Fin 1)) := dyadicCube δ (fun _ => k)

  have h_cubeMap_inj : Function.Injective cubeMap := by
    intro k l h
    let y : ℝ := δ * (k : ℝ)
    let x : EuclideanSpace ℝ (Fin 1) :=
      (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ => y)
    have h_y_def : x 0 = y := by simp [x] <;> rfl
    have hx : x ∈ cubeMap k := by
      intro i
      have h_i0 : i = 0 := Fin.fin_one_eq_zero i
      rw [h_i0, h_y_def]
      exact ⟨by linarith, by linarith [hδ_pos]⟩
    have hxk : δ * (k : ℝ) ≤ x 0 := (hx 0).1
    have hxk2 : x 0 < δ * ((k : ℝ) + 1) := (hx 0).2
    have hxl : δ * (l : ℝ) ≤ x 0 := by rw [h] at hx; exact (hx 0).1
    have hxl2 : x 0 < δ * ((l : ℝ) + 1) := by rw [h] at hx; exact (hx 0).2
    have h_k_le_l : k ≤ l := by
      by_contra h'
      have h_lt_k : l < k := by omega
      have h9 : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (show l + 1 ≤ k from by omega)
      have h10 : δ * ((l : ℝ) + 1) ≤ δ * (k : ℝ) := by gcongr
      linarith
    have h_l_le_k : l ≤ k := by
      by_contra h'
      have h_lt_l : k < l := by omega
      have h9 : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast (show k + 1 ≤ l from by omega)
      have h10 : δ * ((k : ℝ) + 1) ≤ δ * (l : ℝ) := by gcongr
      linarith
    omega

  have h_imageA : dyadicCubesMeeting δ (realLineCopy A) = cubeMap '' idxA := by
    apply Set.Subset.antisymm
    · intro Q hQ
      have hQ1 : Q ∈ dyadicCubes 1 δ := hQ.1
      have hQ2 : (Q ∩ realLineCopy A).Nonempty := hQ.2
      rcases hQ1 with ⟨kf, rfl⟩
      let k0 : ℤ := kf 0
      rcases hQ2 with ⟨x, hxQ, hxA⟩
      have h_y : x 0 ∈ A := by simpa [realLineCopy] using hxA
      have h_Ico : x 0 ∈ Set.Ico (δ * (k0 : ℝ)) (δ * ((k0 : ℝ) + 1)) := by
        simpa [dyadicCube] using hxQ
      have h_k_in : k0 ∈ idxA := ⟨x 0, h_y, h_Ico⟩
      have h_kf_eq : kf = fun _ => k0 := by
        funext j
        have h_j0 : j = 0 := Fin.fin_one_eq_zero j
        rw [h_j0] <;> simp [k0]
      have h_eq : cubeMap k0 = dyadicCube δ kf := by
        rw [h_kf_eq] <;> rfl
      exact ⟨k0, h_k_in, h_eq⟩
    · intro Q hQ
      have h_main : ∃ k, k ∈ idxA ∧ cubeMap k = Q := by simpa [Set.mem_image] using hQ
      rcases h_main with ⟨k, hk, hQ⟩
      have h_k_def : ∃ y ∈ A, y ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := hk
      rcases h_k_def with ⟨y, hyA, hyIco⟩
      let x : EuclideanSpace ℝ (Fin 1) :=
        (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ => y)
      have hx1 : x ∈ realLineCopy A := by simpa [realLineCopy, x] using hyA
      have hx2 : x ∈ cubeMap k := by
        intro i
        have h_i0 : i = 0 := Fin.fin_one_eq_zero i
        rw [h_i0]
        have h_eq : x 0 = y := by simp [x] <;> rfl
        rw [h_eq]
        exact hyIco
      let kf : Fin 1 → ℤ := fun _ => k
      have hQ1 : cubeMap k ∈ dyadicCubes 1 δ := ⟨kf, rfl⟩
      have h_goal : cubeMap k ∈ dyadicCubesMeeting δ (realLineCopy A) := ⟨hQ1, ⟨x, hx2, hx1⟩⟩
      exact hQ ▸ h_goal

  have h_imageB : dyadicCubesMeeting δ (realLineCopy B) = cubeMap '' idxB := by
    apply Set.Subset.antisymm
    · intro Q hQ
      have hQ1 : Q ∈ dyadicCubes 1 δ := hQ.1
      have hQ2 : (Q ∩ realLineCopy B).Nonempty := hQ.2
      rcases hQ1 with ⟨kf, rfl⟩
      let k0 : ℤ := kf 0
      rcases hQ2 with ⟨x, hxQ, hxB⟩
      have h_y : x 0 ∈ B := by simpa [realLineCopy] using hxB
      have h_Ico : x 0 ∈ Set.Ico (δ * (k0 : ℝ)) (δ * ((k0 : ℝ) + 1)) := by
        simpa [dyadicCube] using hxQ
      have h_k_in : k0 ∈ idxB := ⟨x 0, h_y, h_Ico⟩
      have h_kf_eq : kf = fun _ => k0 := by
        funext j
        have h_j0 : j = 0 := Fin.fin_one_eq_zero j
        rw [h_j0] <;> simp [k0]
      have h_eq : cubeMap k0 = dyadicCube δ kf := by
        rw [h_kf_eq] <;> rfl
      exact ⟨k0, h_k_in, h_eq⟩
    · intro Q hQ
      have h_main : ∃ k, k ∈ idxB ∧ cubeMap k = Q := by simpa [Set.mem_image] using hQ
      rcases h_main with ⟨k, hk, hQ⟩
      have h_k_def : ∃ y ∈ B, y ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := hk
      rcases h_k_def with ⟨y, hyB, hyIco⟩
      let x : EuclideanSpace ℝ (Fin 1) :=
        (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ => y)
      have hx1 : x ∈ realLineCopy B := by simpa [realLineCopy, x] using hyB
      have hx2 : x ∈ cubeMap k := by
        intro i
        have h_i0 : i = 0 := Fin.fin_one_eq_zero i
        rw [h_i0]
        have h_eq : x 0 = y := by simp [x] <;> rfl
        rw [h_eq]
        exact hyIco
      let kf : Fin 1 → ℤ := fun _ => k
      have hQ1 : cubeMap k ∈ dyadicCubes 1 δ := ⟨kf, rfl⟩
      have h_goal : cubeMap k ∈ dyadicCubesMeeting δ (realLineCopy B) := ⟨hQ1, ⟨x, hx2, hx1⟩⟩
      exact hQ ▸ h_goal

  have hA_eq : Nreal δ A = ENat.toENNReal idxA.encard := by
    dsimp only [Nreal, dyadicCoveringNumber]
    rw [h_imageA, h_cubeMap_inj.encard_image] <;> rfl
  have hB_eq : Nreal δ B = ENat.toENNReal idxB.encard := by
    dsimp only [Nreal, dyadicCoveringNumber]
    rw [h_imageB, h_cubeMap_inj.encard_image] <;> rfl

  -- Key inclusion: idxB ⊆ idxA ∪ (idxA + 1) ∪ (idxA - 1)
  have h_incl : idxB ⊆ idxA ∪ (idxA.image (· + 1)) ∪ (idxA.image (· - 1)) := by
    intro j hj
    rcases hj with ⟨b, hb, hb_cube⟩
    rcases h_near b hb with ⟨a, ha, hdist⟩
    have h1 : b - δ ≤ a := by linarith [abs_le.mp hdist]
    have h2 : a ≤ b + δ := by linarith [abs_le.mp hdist]
    have ha1 : δ * ((j : ℝ) - 1) ≤ a := by linarith [hb_cube.1]
    have ha2 : a < δ * ((j : ℝ) + 2) := by linarith [hb_cube.2]
    by_cases h3 : a < δ * (j : ℝ)
    · have h4 : (j - 1 : ℤ) ∈ idxA := by
        refine ⟨a, ha, ?_⟩
        have h1 : δ * ↑(j - 1) ≤ a := by
          have h2 : (δ * ↑(j - 1) : ℝ) = δ * ((j : ℝ) - 1) := by simp [sub_eq_add_neg] <;> ring
          rw [h2]
          exact ha1
        have h3' : a < δ * (↑(j - 1) + 1) := by
          have h4 : δ * (↑(j - 1) + 1) = δ * (j : ℝ) := by simp [sub_eq_add_neg] <;> ring
          rw [h4]
          exact h3
        exact ⟨h1, h3'⟩
      have h5 : j ∈ idxA.image (· + 1) := ⟨j - 1, h4, by simp⟩
      exact Or.inl (Or.inr h5)
    · have h3' : δ * (j : ℝ) ≤ a := by linarith
      by_cases h4 : a < δ * ((j : ℝ) + 1)
      · have h5 : j ∈ idxA := ⟨a, ha, ⟨h3', h4⟩⟩
        exact Or.inl (Or.inl h5)
      · have h4' : δ * ((j : ℝ) + 1) ≤ a := by linarith
        have h5 : (j + 1 : ℤ) ∈ idxA := by
          refine ⟨a, ha, ?_⟩
          have h1 : δ * ↑(j + 1) ≤ a := by
            have h2 : (δ * ↑(j + 1) : ℝ) = δ * ((j : ℝ) + 1) := by simp <;> ring
            rw [h2]
            exact h4'
          have h3 : a < δ * (↑(j + 1) + 1) := by
            have h5 : (↑(j + 1) : ℝ) + 1 = (j : ℝ) + 2 := by
              have h51 : (↑(j + 1) : ℝ) = (j : ℝ) + 1 := by simp
              rw [h51] <;> ring
            have h6 : δ * (↑(j + 1) + 1) = δ * ((j : ℝ) + 2) := by rw [h5]
            rw [h6]
            exact ha2
          exact ⟨h1, h3⟩
        have h6 : j ∈ idxA.image (· - 1) := ⟨j + 1, h5, by simp⟩
        exact Or.inr h6

  let S2 := idxA.image (· + 1)
  let S3 := idxA.image (· - 1)
  have h_inj1 : Set.InjOn (· + 1) idxA := by intro x _ y _ h; linarith
  have h_inj3 : Set.InjOn (· - 1) idxA := by intro x _ y _ h; linarith
  have h_eq2 : S2.encard = idxA.encard := h_inj1.encard_image
  have h_eq3 : S3.encard = idxA.encard := h_inj3.encard_image

  have h_union_bound : (idxA ∪ S2 ∪ S3).encard ≤ idxA.encard + idxA.encard + idxA.encard := by
    calc (idxA ∪ S2 ∪ S3).encard
        ≤ (idxA ∪ S2).encard + S3.encard := Set.encard_union_le _ _
    _ ≤ idxA.encard + S2.encard + S3.encard := by
          have h : (idxA ∪ S2).encard ≤ idxA.encard + S2.encard := Set.encard_union_le _ _
          exact add_le_add h (le_refl _)
    _ = idxA.encard + idxA.encard + idxA.encard := by rw [h_eq2, h_eq3] <;> rfl

  have h_card : idxB.encard ≤ idxA.encard + idxA.encard + idxA.encard :=
    le_trans (Set.encard_mono h_incl) h_union_bound

  rw [hB_eq, hA_eq]
  have h5 : ENat.toENNReal idxB.encard ≤ ENat.toENNReal (idxA.encard + idxA.encard + idxA.encard) :=
    ENat.toENNReal_mono h_card
  have h6 : ENat.toENNReal (idxA.encard + idxA.encard + idxA.encard) =
      ENat.toENNReal idxA.encard + ENat.toENNReal idxA.encard + ENat.toENNReal idxA.encard := by
    simp [ENat.toENNReal_add] <;> rfl
  rw [h6] at h5
  have h7 : ENat.toENNReal idxA.encard + ENat.toENNReal idxA.encard + ENat.toENNReal idxA.encard =
      3 * ENat.toENNReal idxA.encard := by
    have h8 : ∀ (x : ENNReal), x + x + x = 3 * x := by
      intro x
      calc x + x + x
        = 1 * x + 1 * x + 1 * x := by simp
      _ = (1 + 1 + 1 : ENNReal) * x := by rw [add_mul, add_mul]
      _ = 3 * x := by norm_num
    exact h8 _
  rw [h7] at h5
  exact h5

/-- The rounding map in 2D: round each coordinate. -/
def roundingMap2 (round : ℝ → ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm
    (fun i => if i = 0 then round (p 0) else round (p 1))

/-- **Rounded graph adapter.**

Given a finite set E3' ⊆ Pbar with density bound
`c_dense * N(S1) * N(S2) ≤ Nplane(E3')`, and a rounding function mapping each
coordinate to the δ-grid within δ/2, produces a rounded graph Gamma ⊆ S1 × S2
with:
- Density: `Nplane(Gamma) ≥ (c_dense/4) * N(S1) * N(S2)`
- Sumset: `N(thirdProj(Gamma)) ≤ 3 * N(thirdProj(E3'))`
- Third projection bound inherited from E3'. -/
lemma rounded_graph_adapter
    {δ L η : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_dyadic : δ ∈ dyadicScales)
    {E3' Pbar : Set (EuclideanSpace ℝ (Fin 2))}
    (hE3'_sub : E3' ⊆ Pbar)
    (hE3'_finite : E3'.Finite)
    (hPbar_bounded : IsBounded Pbar)
    {S1 S2 : Set ℝ}
    (hS1_grid : S1 ⊆ productLikeIntegerGrid δ)
    (hS2_grid : S2 ⊆ productLikeIntegerGrid δ)
    (round : ℝ → ℝ)
    (hround_grid : ∀ x, round x ∈ productLikeIntegerGrid δ)
    (hround_near : ∀ x, |x - round x| ≤ δ / 2)
    (hS1_contains : ∀ p ∈ E3', round (p 0) ∈ S1)
    (hS2_contains : ∀ p ∈ E3', round (p 1) ∈ S2)
    (c_dense : ENNReal)
    (h_density : c_dense * Nreal δ S1 * Nreal δ S2 ≤
      ENat.toENNReal (dyadicCoveringNumber δ E3'))
    (h_third_proj : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) E3') ≤
      ENNReal.ofReal (δ ^ (-(L * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal))) :
    ∃ (Gamma : Set (EuclideanSpace ℝ (Fin 2))),
      (∀ p ∈ Gamma, p 0 ∈ S1 ∧ p 1 ∈ S2) ∧
      (∀ p ∈ Gamma, ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ)) ∧
      ENat.toENNReal (dyadicCoveringNumber δ Gamma) ≥
        (c_dense / 4) * Nreal δ S1 * Nreal δ S2 ∧
      Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma) ≤
        3 * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) E3') ∧
      Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma) ≤
        3 * (ENNReal.ofReal (δ ^ (-(L * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal))) ∧
      (∀ g ∈ Gamma, ∃ z ∈ E3', g 0 = round (z 0) ∧ g 1 = round (z 1)) := by
  let f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    roundingMap2 round
  let Gamma : Set (EuclideanSpace ℝ (Fin 2)) := f '' E3'
  let g := cubeIndexOfPoint δ

  have hGamma_sub : ∀ q ∈ Gamma, q 0 ∈ S1 ∧ q 1 ∈ S2 := by
    intro q hq
    rcases hq with ⟨p, hp, rfl⟩
    exact ⟨hS1_contains p hp, hS2_contains p hp⟩

  have h_eval0 : ∀ p, (f p) 0 = round (p 0) := by
    intro p; simp [f, roundingMap2]
  have h_eval1 : ∀ p, (f p) 1 = round (p 1) := by
    intro p; simp [f, roundingMap2]

  have hGamma_grid : ∀ q ∈ Gamma, ∀ i : Fin 2, ∃ k : ℤ, q i = δ * (k : ℝ) := by
    intro q hq i
    rcases hq with ⟨p, hp, rfl⟩
    fin_cases i
    · exact hround_grid (p 0)
    · exact hround_grid (p 1)

  have hG_rounded_finite : Gamma.Finite := hE3'_finite.image f
  let E3'f : Finset (EuclideanSpace ℝ (Fin 2)) := hE3'_finite.toFinset
  let Gammaf : Finset (EuclideanSpace ℝ (Fin 2)) := hG_rounded_finite.toFinset
  have hE3'f_coe : (E3'f : Set _) = E3' := hE3'_finite.coe_toFinset
  have hGammaf_coe : (Gammaf : Set _) = Gamma := hG_rounded_finite.coe_toFinset

  -- g is injective on Gamma because Gamma points are grid points
  have h_g_inj_Gamma : Set.InjOn g Gamma := by
    intro q1 hq1 q2 hq2 h_eq
    have h_all : ∀ i, q1 i = q2 i := by
      intro i
      have h1 : ∃ (k : ℤ), q1 i = δ * (k : ℝ) := hGamma_grid q1 hq1 i
      have h2 : ∃ (k : ℤ), q2 i = δ * (k : ℝ) := hGamma_grid q2 hq2 i
      rcases h1 with ⟨k1, hk1⟩
      rcases h2 with ⟨k2, hk2⟩
      have hne : δ ≠ 0 := hδ_pos.ne'
      have h3 : g q1 i = k1 := by
        simp [g, cubeIndexOfPoint]
        have h_eq : q1 i / δ = (k1 : ℝ) := by
          rw [hk1] <;> field_simp [hne]
        rw [h_eq] <;> simp
      have h4 : g q2 i = k2 := by
        simp [g, cubeIndexOfPoint]
        have h_eq : q2 i / δ = (k2 : ℝ) := by
          rw [hk2] <;> field_simp [hne]
        rw [h_eq] <;> simp
      have h5 : g q1 i = g q2 i := congr_fun h_eq i
      rw [h3, h4] at h5
      have h6 : k1 = k2 := h5
      rw [hk1, hk2, h6]
    ext i
    exact h_all i

  have h_Gamma_cubes : (Gammaf.image g).card = Gammaf.card :=
    Finset.card_image_of_injOn (by simpa [hGammaf_coe] using h_g_inj_Gamma)

  -- For each q ∈ Gamma, the g-values of its preimage have size ≤ 4
  have h_fiber_bound : ∀ (q : EuclideanSpace ℝ (Fin 2)),
      ((E3'f.filter (fun p => f p = q)).image g).card ≤ 4 := by
    intro q
    by_cases hq : q ∈ Gammaf
    · -- q is a grid point
      have hq' : q ∈ Gamma := by
        have h : q ∈ (Gammaf : Set _) := hq
        rw [hGammaf_coe] at h
        exact h
      have hgrid0 : ∃ (k : ℤ), q 0 = δ * (k : ℝ) := hGamma_grid q hq' 0
      have hgrid1 : ∃ (k : ℤ), q 1 = δ * (k : ℝ) := hGamma_grid q hq' 1
      rcases hgrid0 with ⟨k0, hk0⟩
      rcases hgrid1 with ⟨k1, hk1⟩
      let Idx0 : Finset ℤ := {k0 - 1, k0}
      let Idx1 : Finset ℤ := {k1 - 1, k1}
      let S : Finset (Fin 2 → ℤ) :=
        Idx0.product Idx1 |>.image (fun p : ℤ × ℤ => fun i => if i = 0 then p.1 else p.2)
      have hS_card : S.card ≤ 4 := by
        have h : S.card ≤ (Idx0.product Idx1).card := Finset.card_image_le
        have h2 : (Idx0.product Idx1).card = Idx0.card * Idx1.card := Finset.card_product _ _
        rw [h2] at h
        simp [Idx0, Idx1] at h ⊢ <;> omega
      have h_sub : (E3'f.filter (fun p => f p = q)).image g ⊆ S := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
        have hpe : p ∈ E3' := by
          have h : p ∈ (E3'f : Set _) := (Finset.mem_filter.mp hp).1
          rw [hE3'f_coe] at h
          exact h
        have hfe : f p = q := (Finset.mem_filter.mp hp).2
        have h_near0 : |p 0 - δ * (k0 : ℝ)| ≤ δ / 2 := by
          have h_round_eq : round (p 0) = δ * (k0 : ℝ) := by
            have h1 : (f p) 0 = round (p 0) := h_eval0 p
            have h2 : (f p) 0 = q 0 := by rw [hfe]
            have h3 : round (p 0) = q 0 := h1.symm.trans h2
            rw [h3, hk0]
          have h : |p 0 - round (p 0)| ≤ δ / 2 := hround_near (p 0)
          rw [h_round_eq] at h
          exact h
        have h_near1 : |p 1 - δ * (k1 : ℝ)| ≤ δ / 2 := by
          have h_round_eq : round (p 1) = δ * (k1 : ℝ) := by
            have h1 : (f p) 1 = round (p 1) := h_eval1 p
            have h2 : (f p) 1 = q 1 := by rw [hfe]
            have h3 : round (p 1) = q 1 := h1.symm.trans h2
            rw [h3, hk1]
          have h : |p 1 - round (p 1)| ≤ δ / 2 := hround_near (p 1)
          rw [h_round_eq] at h
          exact h
        have h0 : g p 0 = k0 - 1 ∨ g p 0 = k0 := floor_near_grid hδ_pos h_near0
        have h1 : g p 1 = k1 - 1 ∨ g p 1 = k1 := floor_near_grid hδ_pos h_near1
        have h_in_S : g p ∈ S := by
          simp only [S, Finset.mem_image, Finset.mem_product]
          rcases h0 with (h0 | h0) <;> rcases h1 with (h1 | h1) <;>
            exact ⟨(g p 0, g p 1), by simp [Idx0, Idx1, h0, h1], by funext i; fin_cases i <;> simp [h0, h1]⟩
        exact h_in_S
      exact le_trans (Finset.card_le_card h_sub) hS_card
    · -- q not in Gammaf, preimage is empty
      have h_notin : q ∉ Gamma := by
        intro h
        have h' : q ∈ (Gammaf : Set _) := by
          rw [hGammaf_coe] <;> exact h
        exact hq h'
      have h_empty : E3'f.filter (fun p => f p = q) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro p hp
        intro h_eq
        have hpe' : p ∈ E3' := by
          rw [←hE3'f_coe] <;> exact hp
        have hq' : q ∈ Gamma := ⟨p, hpe', h_eq⟩
        exact h_notin hq'
      rw [h_empty]
      <;> simp

  -- E3'f.image g = Gammaf.biUnion (fun q => (E3'f.filter (fun p => f p = q)).image g)
  have h_union : E3'f.image g =
      Gammaf.biUnion (fun q => (E3'f.filter (fun p => f p = q)).image g) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_biUnion]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hpe : p ∈ E3' := by
        have h' : p ∈ (E3'f : Set _) := hp
        rw [hE3'f_coe] at h'
        exact h'
      have h : f p ∈ Gamma := ⟨p, hpe, rfl⟩
      have hfp : f p ∈ Gammaf := by
        have h' : f p ∈ (Gammaf : Set _) := by
          rw [hGammaf_coe]
          exact h
        exact h'
      have h_filter : p ∈ E3'f.filter (fun p' => f p' = f p) :=
        Finset.mem_filter.mpr ⟨hp, rfl⟩
      exact ⟨f p, hfp, ⟨p, h_filter, rfl⟩⟩
    · rintro ⟨q, hq, ⟨p, hp_filter, rfl⟩⟩
      have hp' : p ∈ E3'f := (Finset.mem_filter.mp hp_filter).1
      exact ⟨p, hp', rfl⟩

  have h_K_E3_le : (E3'f.image g).card ≤ 4 * (Gammaf.image g).card := by
    rw [h_union]
    calc (Gammaf.biUnion (fun q => (E3'f.filter (fun p => f p = q)).image g)).card
        ≤ ∑ q ∈ Gammaf, ((E3'f.filter (fun p => f p = q)).image g).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ Gammaf, 4 := by
        apply Finset.sum_le_sum
        intro q _
        exact h_fiber_bound q
      _ = 4 * Gammaf.card := by
        rw [Finset.sum_const] <;> ring
      _ = 4 * (Gammaf.image g).card := by rw [h_Gamma_cubes]

  have h_cover_E3 : ENat.toENNReal (dyadicCoveringNumber δ E3') =
      ↑(E3'f.image g).card := finite_covering2_eq_card hδ_pos hE3'_finite
  have h_cover_Gamma : ENat.toENNReal (dyadicCoveringNumber δ Gamma) =
      ↑(Gammaf.image g).card := finite_covering2_eq_card hδ_pos hG_rounded_finite

  have h_density4 : ENat.toENNReal (dyadicCoveringNumber δ E3') ≤
      4 * ENat.toENNReal (dyadicCoveringNumber δ Gamma) := by
    rw [h_cover_E3, h_cover_Gamma]
    exact_mod_cast h_K_E3_le

  have h_main_density : ENat.toENNReal (dyadicCoveringNumber δ Gamma) ≥
      (c_dense / 4) * Nreal δ S1 * Nreal δ S2 := by
    have h : c_dense * Nreal δ S1 * Nreal δ S2 ≤
        4 * ENat.toENNReal (dyadicCoveringNumber δ Gamma) :=
      le_trans h_density h_density4
    have h4 : (c_dense / 4) * Nreal δ S1 * Nreal δ S2 =
        (c_dense * Nreal δ S1 * Nreal δ S2) / 4 := by
      have h9 : ∀ (a b c : ENNReal), (a / 4) * b * c = (a * b * c) / 4 := by
        intro a b c
        have h10 : (a / 4) * b * c = a * (4 : ENNReal)⁻¹ * b * c := by rfl
        have h11 : (a * b * c) / 4 = a * b * c * (4 : ENNReal)⁻¹ := by rfl
        rw [h10, h11]
        simp [mul_assoc, mul_comm, mul_left_comm]
      exact h9 c_dense (Nreal δ S1) (Nreal δ S2)
    calc (c_dense / 4) * Nreal δ S1 * Nreal δ S2
      = (c_dense * Nreal δ S1 * Nreal δ S2) / 4 := h4
    _ ≤ (4 * ENat.toENNReal (dyadicCoveringNumber δ Gamma)) / 4 := by gcongr
    _ = ENat.toENNReal (dyadicCoveringNumber δ Gamma) := by
      have h_ne : (4 : ENNReal) ≠ 0 := by norm_num
      have h_top : (4 : ENNReal) ≠ ⊤ := by norm_num
      have h_comm : (4 * ENat.toENNReal (dyadicCoveringNumber δ Gamma)) / 4 =
          (ENat.toENNReal (dyadicCoveringNumber δ Gamma) * 4) / 4 := by
        rw [mul_comm (4 : ENNReal)]
      rw [h_comm]
      exact ENNReal.mul_div_cancel_right h_ne h_top

  -- Sumset bound using neighborhood_covering_bound
  let thirdProjE3' := Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) E3'
  let sumsetGamma := Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma

  have h_sumset_near : ∀ w ∈ sumsetGamma, ∃ z ∈ thirdProjE3', |w - z| ≤ δ := by
    intro w hw
    rcases hw with ⟨q, hq, rfl⟩
    have h_q_in : q ∈ f '' E3' := by simpa [Gamma] using hq
    rcases h_q_in with ⟨p, hpE3', hfe⟩
    let z : ℝ := p 0 + p 1
    have hz : z ∈ thirdProjE3' := ⟨p, hpE3', rfl⟩
    have hq0 : q 0 = round (p 0) := by
      have h1 : (f p) 0 = q 0 := by rw [hfe]
      exact h1.symm.trans (h_eval0 p)
    have hq1 : q 1 = round (p 1) := by
      have h1 : (f p) 1 = q 1 := by rw [hfe]
      exact h1.symm.trans (h_eval1 p)
    have h1 : |(q 0 + q 1) - z| ≤ δ := by
      have h2 : |q 0 - p 0| ≤ δ / 2 := by
        have h_near : |p 0 - round (p 0)| ≤ δ / 2 := hround_near (p 0)
        have h_eq : q 0 - p 0 = -(p 0 - round (p 0)) := by
          rw [hq0] <;> ring
        rw [h_eq, abs_neg]
        exact h_near
      have h3 : |q 1 - p 1| ≤ δ / 2 := by
        have h_near : |p 1 - round (p 1)| ≤ δ / 2 := hround_near (p 1)
        have h_eq : q 1 - p 1 = -(p 1 - round (p 1)) := by
          rw [hq1] <;> ring
        rw [h_eq, abs_neg]
        exact h_near
      calc |(q 0 + q 1) - z|
        = |(q 0 - p 0) + (q 1 - p 1)| := by simp [z] <;> ring_nf
      _ ≤ |q 0 - p 0| + |q 1 - p 1| := by exact abs_add_le (q.ofLp 0 - p.ofLp 0) (q.ofLp 1 - p.ofLp 1)
      _ ≤ δ / 2 + δ / 2 := by linarith
      _ = δ := by ring
    exact ⟨z, hz, h1⟩

  have h_sumset3 : Nreal δ sumsetGamma ≤ 3 * Nreal δ thirdProjE3' :=
    neighborhood_covering_bound hδ_pos h_sumset_near

  have h_final_sum : Nreal δ sumsetGamma ≤
      3 * (ENNReal.ofReal (δ ^ (-(L * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal))) := by
    calc Nreal δ sumsetGamma
        ≤ 3 * Nreal δ thirdProjE3' := h_sumset3
      _ ≤ 3 * (ENNReal.ofReal (δ ^ (-(L * η))) *
            ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal))) := by
          exact mul_le_mul_of_nonneg_left h_third_proj (by positivity)

  have hGamma_witness : ∀ g ∈ Gamma, ∃ z ∈ E3', g 0 = round (z 0) ∧ g 1 = round (z 1) := by
    intro g hg
    rcases hg with ⟨z, hz, rfl⟩
    exact ⟨z, hz, h_eval0 z, h_eval1 z⟩

  exact ⟨Gamma, hGamma_sub, hGamma_grid, h_main_density, h_sumset3, h_final_sum, hGamma_witness⟩

end ProductLikeIncidence
