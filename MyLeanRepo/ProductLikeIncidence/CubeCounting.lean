module

/-
# Cube Counting Lemma — Product lower bound from occupancy and rounding

Formalizes the geometric argument: if every δ-cube contains ≤ M_G points,
and rounding maps each point to within δ/2 of a grid point in S1×S2,
then N(S1)*N(S2) ≥ |E3''| / (4*M_G).

The factor 4 arises because a δ/2-ball around a grid point intersects
at most 2 δ-cubes per dimension (4 in 2D).

## Whiteprint node
Helper for absolute size lower bounds in incidence-to-ring contradiction.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProductLikeSetBasics
public import MyLeanRepo.ProductLikeIncidence.GridSeparatedCard
public import MyLeanRepo.OSWPrelude

@[expose] public section


noncomputable section

open Set ENNReal Bornology MeasureTheory Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-! ## Geometric cube-counting lemma -/

/-- **Coordinate-wise cube index bound**: If a point `p` lies in the δ-cube
indexed by `k` and satisfies `|p0 - δ*a| ≤ δ/2` and `|p1 - δ*b| ≤ δ/2`,
then `k 0 ∈ {a-1, a}` and `k 1 ∈ {b-1, b}`. Thus at most 4 cubes can
intersect a coordinate-wise δ/2-neighborhood of a grid point. -/
lemma cube_index_near_grid_coord
    {δ : ℝ} (hδ_pos : 0 < δ)
    {a b : ℤ} {g : EuclideanSpace ℝ (Fin 2)}
    (hga : g 0 = δ * (a : ℝ)) (hgb : g 1 = δ * (b : ℝ))
    {p : EuclideanSpace ℝ (Fin 2)}
    (h_coord0 : |p 0 - g 0| ≤ δ / 2)
    (h_coord1 : |p 1 - g 1| ≤ δ / 2)
    {k : Fin 2 → ℤ}
    (hk0 : p 0 ∈ Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 : ℝ) + 1)))
    (hk1 : p 1 ∈ Set.Ico (δ * (k 1 : ℝ)) (δ * ((k 1 : ℝ) + 1))) :
    (k 0 = a - 1 ∨ k 0 = a) ∧ (k 1 = b - 1 ∨ k 1 = b) := by
  have h_k0 : k 0 = a - 1 ∨ k 0 = a := by
    rw [hga] at h_coord0
    have h1 : δ * (k 0 : ℝ) ≤ p 0 := hk0.1
    have h2 : p 0 < δ * ((k 0 : ℝ) + 1) := hk0.2
    have h3 : p 0 ≤ δ * (a : ℝ) + δ / 2 := by
      have h4 : p 0 - δ * (a : ℝ) ≤ δ / 2 := (abs_le.mp h_coord0).2
      linarith
    have h4 : δ * (a : ℝ) - δ / 2 ≤ p 0 := by
      have h5 : -(δ / 2) ≤ p 0 - δ * (a : ℝ) := (abs_le.mp h_coord0).1
      linarith
    have h5 : (k 0 : ℝ) ≤ (a : ℝ) + 1 / 2 := by
      calc (k 0 : ℝ)
        = (δ * (k 0 : ℝ)) / δ := by field_simp [hδ_pos.ne'] <;> ring
      _ ≤ (p 0) / δ := by gcongr
      _ ≤ (δ * (a : ℝ) + δ / 2) / δ := by gcongr
      _ = (a : ℝ) + 1 / 2 := by field_simp [hδ_pos.ne'] <;> ring
    have h6 : (a : ℝ) - 3 / 2 < (k 0 : ℝ) := by
      calc (a : ℝ) - 3 / 2
        = (δ * (a : ℝ) - δ / 2) / δ - 1 := by field_simp [hδ_pos.ne'] <;> ring
      _ ≤ (p 0) / δ - 1 := by gcongr
      _ < (δ * ((k 0 : ℝ) + 1)) / δ - 1 := by gcongr
      _ = (k 0 : ℝ) := by field_simp [hδ_pos.ne'] <;> ring
    have h7 : k 0 ≤ a := by
      by_contra h7
      have h8 : k 0 ≥ a + 1 := by linarith
      have h9 : (k 0 : ℝ) ≥ (a : ℝ) + 1 := by exact_mod_cast h8
      linarith
    have h10 : k 0 ≥ a - 1 := by
      by_contra h10
      have h11 : k 0 ≤ a - 2 := by linarith
      have h12 : (k 0 : ℝ) ≤ (a : ℝ) - 2 := by exact_mod_cast h11
      linarith
    omega
  have h_k1 : k 1 = b - 1 ∨ k 1 = b := by
    rw [hgb] at h_coord1
    have h1 : δ * (k 1 : ℝ) ≤ p 1 := hk1.1
    have h2 : p 1 < δ * ((k 1 : ℝ) + 1) := hk1.2
    have h3 : p 1 ≤ δ * (b : ℝ) + δ / 2 := by
      have h4 : p 1 - δ * (b : ℝ) ≤ δ / 2 := (abs_le.mp h_coord1).2
      linarith
    have h4 : δ * (b : ℝ) - δ / 2 ≤ p 1 := by
      have h5 : -(δ / 2) ≤ p 1 - δ * (b : ℝ) := (abs_le.mp h_coord1).1
      linarith
    have h5 : (k 1 : ℝ) ≤ (b : ℝ) + 1 / 2 := by
      calc (k 1 : ℝ)
        = (δ * (k 1 : ℝ)) / δ := by field_simp [hδ_pos.ne'] <;> ring
      _ ≤ (p 1) / δ := by gcongr
      _ ≤ (δ * (b : ℝ) + δ / 2) / δ := by gcongr
      _ = (b : ℝ) + 1 / 2 := by field_simp [hδ_pos.ne'] <;> ring
    have h6 : (b : ℝ) - 3 / 2 < (k 1 : ℝ) := by
      calc (b : ℝ) - 3 / 2
        = (δ * (b : ℝ) - δ / 2) / δ - 1 := by field_simp [hδ_pos.ne'] <;> ring
      _ ≤ (p 1) / δ - 1 := by gcongr
      _ < (δ * ((k 1 : ℝ) + 1)) / δ - 1 := by gcongr
      _ = (k 1 : ℝ) := by field_simp [hδ_pos.ne'] <;> ring
    have h7 : k 1 ≤ b := by
      by_contra h7
      have h8 : k 1 ≥ b + 1 := by linarith
      have h9 : (k 1 : ℝ) ≥ (b : ℝ) + 1 := by exact_mod_cast h8
      linarith
    have h10 : k 1 ≥ b - 1 := by
      by_contra h10
      have h11 : k 1 ≤ b - 2 := by linarith
      have h12 : (k 1 : ℝ) ≤ (b : ℝ) - 2 := by exact_mod_cast h11
      linarith
    omega
  exact ⟨h_k0, h_k1⟩

/-- **Cube index bound**: If a point `p` lies in the δ-cube indexed by `k`
and is within δ/2 (Euclidean distance) of grid point `(δ*a, δ*b)`, then
`k 0 ∈ {a-1, a}` and `k 1 ∈ {b-1, b}`.

Derives the coordinate-wise bounds from the Euclidean distance bound and
calls `cube_index_near_grid_coord`. -/
lemma cube_index_near_grid
    {δ : ℝ} (hδ_pos : 0 < δ)
    {a b : ℤ} {g : EuclideanSpace ℝ (Fin 2)}
    (hga : g 0 = δ * (a : ℝ)) (hgb : g 1 = δ * (b : ℝ))
    {p : EuclideanSpace ℝ (Fin 2)} (h_dist : dist p g ≤ δ / 2)
    {k : Fin 2 → ℤ}
    (hk0 : p 0 ∈ Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 : ℝ) + 1)))
    (hk1 : p 1 ∈ Set.Ico (δ * (k 1 : ℝ)) (δ * ((k 1 : ℝ) + 1))) :
    (k 0 = a - 1 ∨ k 0 = a) ∧ (k 1 = b - 1 ∨ k 1 = b) := by
  have h_coord0 : |p 0 - g 0| ≤ δ / 2 := by
    have h : |p 0 - g 0| ≤ dist p g := PiLp.norm_apply_le (p - g) 0
    linarith
  have h_coord1 : |p 1 - g 1| ≤ δ / 2 := by
    have h : |p 1 - g 1| ≤ dist p g := PiLp.norm_apply_le (p - g) 1
    linarith
  exact cube_index_near_grid_coord hδ_pos hga hgb h_coord0 h_coord1 hk0 hk1

/-- **Cube index function**: Maps a point to the index of the unique
half-open δ-cube containing it. -/
def cubeIndex (δ : ℝ) (p : EuclideanSpace ℝ (Fin 2)) : Fin 2 → ℤ :=
  fun i => Int.floor (p i / δ)

/-- A point lies in the δ-cube indexed by `cubeIndex δ p`. -/
lemma point_in_cubeIndex_cube
    {δ : ℝ} (hδ_pos : 0 < δ) (p : EuclideanSpace ℝ (Fin 2)) :
    p ∈ dyadicCube δ (cubeIndex δ p) := by
  intro i
  have h1 : (cubeIndex δ p i : ℝ) ≤ p i / δ := Int.floor_le (p i / δ)
  have h2 : p i / δ < (cubeIndex δ p i : ℝ) + 1 := Int.lt_floor_add_one (p i / δ)
  have h3 : δ * (cubeIndex δ p i : ℝ) ≤ p i := by
    calc δ * (cubeIndex δ p i : ℝ)
      ≤ δ * (p i / δ) := by gcongr
    _ = p i := by field_simp [hδ_pos.ne'] <;> ring
  have h4 : p i < δ * ((cubeIndex δ p i : ℝ) + 1) := by
    calc p i
      = δ * (p i / δ) := by field_simp [hδ_pos.ne'] <;> ring
    _ < δ * ((cubeIndex δ p i : ℝ) + 1) := by gcongr
  exact ⟨h3, h4⟩

/-- **Product lower bound from occupancy and rounding**.

If every δ-cube contains at most `M_G` points of `E3''`, and rounding
maps each point to within δ/2 of a grid point in `S1 × S2`, then:
  `N(S1) * N(S2) ≥ |E3''| / (4 * M_G)` -/
lemma product_lower_from_occupancy
    {δ : ℝ} (hδ_pos : 0 < δ)
    {E3'' : Set (EuclideanSpace ℝ (Fin 2))}
    {S1 S2 : Set ℝ}
    {M_G : ENNReal}
    (hE3''_finite : E3''.Finite)
    (hS1_finite : S1.Finite) (hS2_finite : S2.Finite)
    (hS1_grid : ∀ x ∈ S1, x ∈ productLikeIntegerGrid δ)
    (hS2_grid : ∀ x ∈ S2, x ∈ productLikeIntegerGrid δ)
    (hS1_sep : ∀ x ∈ S1, ∀ y ∈ S1, x ≠ y → |x - y| ≥ δ)
    (hS2_sep : ∀ x ∈ S2, ∀ y ∈ S2, x ≠ y → |x - y| ≥ δ)
    (h_occupancy : ∀ Q ∈ dyadicCubes 2 δ,
        ENat.toENNReal (E3'' ∩ Q).encard ≤ M_G)
    (round : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (h_round_near : ∀ p, dist p (round p) ≤ δ / 2)
    (h_round_image : ∀ p ∈ E3'', (round p) 0 ∈ S1 ∧ (round p) 1 ∈ S2) :
    Nreal δ S1 * Nreal δ S2 ≥
      ENat.toENNReal E3''.encard / (4 * M_G) := by
  let E_fin := hE3''_finite.toFinset
  let S1_fin := hS1_finite.toFinset
  let S2_fin := hS2_finite.toFinset
  have hE_coe : (E_fin : Set _) = E3'' := hE3''_finite.coe_toFinset
  have hS1_coe : (S1_fin : Set _) = S1 := hS1_finite.coe_toFinset
  have hS2_coe : (S2_fin : Set _) = S2 := hS2_finite.coe_toFinset

  have hN1 : Nreal δ S1 = ENat.toENNReal S1.encard := by
    have h1 : Nreal δ S1 = ENNReal.ofReal (S1.ncard : ℝ) :=
      grid_separated_nreal_eq_card1d hδ_pos hS1_finite hS1_grid hS1_sep
    have h2 : ENNReal.ofReal (S1.ncard : ℝ) = ENat.toENNReal S1.encard := by
      have h_ncard : S1.ncard = S1_fin.card := by rw [←hS1_coe] <;> simp
      have h_encard : S1.encard = ↑S1_fin.card := by rw [←hS1_coe] <;> simp
      rw [h_ncard, h_encard] <;> simp <;> norm_cast
    rw [h1, h2]
  have hN2 : Nreal δ S2 = ENat.toENNReal S2.encard := by
    have h1 : Nreal δ S2 = ENNReal.ofReal (S2.ncard : ℝ) :=
      grid_separated_nreal_eq_card1d hδ_pos hS2_finite hS2_grid hS2_sep
    have h2 : ENNReal.ofReal (S2.ncard : ℝ) = ENat.toENNReal S2.encard := by
      have h_ncard : S2.ncard = S2_fin.card := by rw [←hS2_coe] <;> simp
      have h_encard : S2.encard = ↑S2_fin.card := by rw [←hS2_coe] <;> simp
      rw [h_ncard, h_encard] <;> simp <;> norm_cast
    rw [h1, h2]
  rw [hN1, hN2]

  let fiber (g : EuclideanSpace ℝ (Fin 2)) : Finset (EuclideanSpace ℝ (Fin 2)) :=
    E_fin.filter (fun p => round p = g)
  let S_prod : Finset (EuclideanSpace ℝ (Fin 2)) := E_fin.image round

  have h_g_in_product : ∀ g ∈ S_prod, g 0 ∈ S1 ∧ g 1 ∈ S2 := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨p, hp, rfl⟩
    have hpe : p ∈ E3'' := by rw [←hE_coe] <;> exact hp
    exact h_round_image p hpe

  -- Key fiber bound: |fiber g| ≤ 4 * M_G
  have h_fiber_bound : ∀ g ∈ S_prod,
      (↑(fiber g).card : ENNReal) ≤ 4 * M_G := by
    intro g hg
    have hg0 : g 0 ∈ S1 := (h_g_in_product g hg).1
    have hg1 : g 1 ∈ S2 := (h_g_in_product g hg).2
    obtain ⟨a, ha⟩ := hS1_grid (g 0) hg0
    obtain ⟨b, hb⟩ := hS2_grid (g 1) hg1
    let C_g : Finset (Fin 2 → ℤ) := (fiber g).image (cubeIndex δ)
    have hCg_le_4 : C_g.card ≤ 4 := by
      let idx0 : Finset ℤ := {a - 1, a}
      let idx1 : Finset ℤ := {b - 1, b}
      let allowed : Finset (Fin 2 → ℤ) :=
        (Finset.product idx0 idx1).image (fun p : ℤ × ℤ =>
          fun i : Fin 2 => if i = 0 then p.1 else p.2)
      have h_sub : C_g ⊆ allowed := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
        have hpe : p ∈ E_fin := (Finset.mem_filter.mp hp).1
        have h_eq : round p = g := (Finset.mem_filter.mp hp).2
        have h_dist : dist p g ≤ δ / 2 := by
          have h' : dist p (round p) ≤ δ / 2 := h_round_near p
          rw [h_eq] at h'; exact h'
        have h_in_cube : p ∈ dyadicCube δ (cubeIndex δ p) :=
          point_in_cubeIndex_cube hδ_pos p
        have h_bound := cube_index_near_grid hδ_pos ha hb h_dist
          (h_in_cube 0) (h_in_cube 1)
        have h_k0 : cubeIndex δ p 0 = a - 1 ∨ cubeIndex δ p 0 = a := h_bound.1
        have h_k1 : cubeIndex δ p 1 = b - 1 ∨ cubeIndex δ p 1 = b := h_bound.2
        let p' : ℤ × ℤ := (cubeIndex δ p 0, cubeIndex δ p 1)
        have hp'_in : p' ∈ Finset.product idx0 idx1 := by
          simp [p', idx0, idx1, h_k0, h_k1] <;> tauto
        have h_final : cubeIndex δ p ∈ allowed := by
          apply Finset.mem_image.mpr
          refine ⟨p', hp'_in, ?_⟩
          funext i; fin_cases i <;> simp [p'] <;> rfl
        exact h_final
      have h_card : allowed.card ≤ 4 := by
        have h : allowed.card ≤ (Finset.product idx0 idx1).card := by exact Finset.card_image_le
        have hcp : (Finset.product idx0 idx1).card = idx0.card * idx1.card := Finset.card_product idx0 idx1
        rw [hcp] at h
        simpa [idx0, idx1] using h
      exact le_trans (Finset.card_le_card h_sub) h_card
    let A (k : Fin 2 → ℤ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
      (hE3''_finite.subset (Set.inter_subset_left (s := E3'') (t := dyadicCube δ k))).toFinset
    have hA_eq : ∀ k, (A k : Set _) = E3'' ∩ dyadicCube δ k := by
      intro k; simp [A]
    have h_fiber_sub : fiber g ⊆ C_g.biUnion A := by
      intro p hp
      have hpf : p ∈ fiber g := hp
      have hpe : p ∈ E_fin := (Finset.mem_filter.mp hpf).1
      have hpe' : p ∈ E3'' := by rw [←hE_coe] <;> exact hpe
      let k := cubeIndex δ p
      have hk : k ∈ C_g := Finset.mem_image.mpr ⟨p, hpf, rfl⟩
      have h_in_cube : p ∈ dyadicCube δ k := point_in_cubeIndex_cube hδ_pos p
      have h_in_A : p ∈ A k := by
        simpa [A, hA_eq] using ⟨hpe', h_in_cube⟩
      exact Finset.mem_biUnion.mpr ⟨k, hk, h_in_A⟩
    have h_card_le : (fiber g).card ≤ ∑ k ∈ C_g, (A k).card := by
      calc (fiber g).card
        ≤ (C_g.biUnion A).card := Finset.card_le_card h_fiber_sub
      _ ≤ ∑ k ∈ C_g, (A k).card := by exact Finset.card_biUnion_le
    have h_main : (↑(fiber g).card : ENNReal) ≤ ∑ k ∈ C_g, (↑(A k).card : ENNReal) := by
      exact_mod_cast h_card_le
    have h_each : ∀ k ∈ C_g, (↑(A k).card : ENNReal) ≤ M_G := by
      intro k _
      have hQ : dyadicCube δ k ∈ dyadicCubes 2 δ := ⟨k, rfl⟩
      have h_occ : ENat.toENNReal (E3'' ∩ dyadicCube δ k).encard ≤ M_G :=
        h_occupancy (dyadicCube δ k) hQ
      have h_eq : (↑(A k).card : ENNReal) = ENat.toENNReal (E3'' ∩ dyadicCube δ k).encard := by
        have h9 : (A k : Set _) = E3'' ∩ dyadicCube δ k := hA_eq k
        have h10 : (E3'' ∩ dyadicCube δ k).encard = ↑(A k).card := by
          rw [←h9]
          <;> simp
        simp [h10]
      rw [h_eq]; exact h_occ
    have h_sum_le : ∑ k ∈ C_g, (↑(A k).card : ENNReal) ≤ ∑ k ∈ C_g, M_G :=
      Finset.sum_le_sum h_each
    have h_sum_MG : ∑ k ∈ C_g, M_G = (↑C_g.card : ENNReal) * M_G := by
      simp [Finset.sum_const] <;> ring
    have h_final : (↑C_g.card : ENNReal) * M_G ≤ 4 * M_G := by
      have h : (↑C_g.card : ENNReal) ≤ 4 := by exact_mod_cast hCg_le_4
      exact mul_le_mul_of_nonneg_right h (by positivity)
    calc (↑(fiber g).card : ENNReal)
      ≤ ∑ k ∈ C_g, (↑(A k).card : ENNReal) := h_main
    _ ≤ ∑ k ∈ C_g, M_G := h_sum_le
    _ = (↑C_g.card : ENNReal) * M_G := h_sum_MG
    _ ≤ 4 * M_G := h_final

  let toPair : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun g => (g 0, g 1)
  have h_toPair_inj : Function.Injective toPair := by
    intro g1 g2 h
    ext i
    fin_cases i <;> simp [toPair, Prod.ext_iff] at h ⊢ <;> tauto
  have h_image_sub : S_prod.image toPair ⊆ S1_fin ×ˢ S2_fin := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨g, hg, rfl⟩
    have h1 : g 0 ∈ S1 := (h_g_in_product g hg).1
    have h2 : g 1 ∈ S2 := (h_g_in_product g hg).2
    have h3 : g 0 ∈ S1_fin := by
      have h31 : g 0 ∈ (S1_fin : Set _) := by
        rw [hS1_coe]
        exact h1
      exact h31
    have h4 : g 1 ∈ S2_fin := by
      have h41 : g 1 ∈ (S2_fin : Set _) := by
        rw [hS2_coe]
        exact h2
      exact h41
    exact Finset.mem_product.mpr ⟨h3, h4⟩
  have hS_prod_card : S_prod.card ≤ S1_fin.card * S2_fin.card := by
    have h1 : S_prod.card = (S_prod.image toPair).card := by
      simp [Finset.card_image_of_injective, h_toPair_inj]
    rw [h1]
    have h2 : (S_prod.image toPair).card ≤ (S1_fin ×ˢ S2_fin).card :=
      Finset.card_le_card h_image_sub
    rw [Finset.card_product] at h2
    exact h2

  have h_disj : ∀ g1 ∈ S_prod, ∀ g2 ∈ S_prod,
      g1 ≠ g2 → Disjoint (fiber g1) (fiber g2) := by
    intro g1 _ g2 _ hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h5 : round x = g1 := (Finset.mem_filter.mp hx1).2
    have h6 : round x = g2 := (Finset.mem_filter.mp hx2).2
    have h7 : g1 = g2 := by
      calc g1 = round x := h5.symm
           _ = g2 := h6
    exact False.elim (hne h7)
  have h_union : E_fin = S_prod.biUnion fiber := by
    ext p
    simp only [Finset.mem_biUnion]
    constructor
    · intro hp
      have hg : round p ∈ S_prod := Finset.mem_image.mpr ⟨p, hp, rfl⟩
      exact ⟨round p, hg, by simp [fiber, hp]⟩
    · rintro ⟨g, _, hpg⟩
      exact (Finset.mem_filter.mp hpg).1
  have h_card_sum : E_fin.card = ∑ g ∈ S_prod, (fiber g).card := by
    rw [h_union, Finset.card_biUnion h_disj]
  have h_encard_sum : ENat.toENNReal E3''.encard =
      ∑ g ∈ S_prod, (↑(fiber g).card : ENNReal) := by
    have h1 : E3''.encard = ↑E_fin.card := by rw [←hE_coe] <;> simp
    have h2 : ENat.toENNReal E3''.encard = (↑E_fin.card : ENNReal) := by
      rw [h1] <;> simp
    have h3 : (↑E_fin.card : ENNReal) = ∑ g ∈ S_prod, (↑(fiber g).card : ENNReal) := by
      rw [h_card_sum] <;> simp [Finset.sum_apply] <;> norm_cast
    rw [h2, h3]
  have h_sum_bound : ENat.toENNReal E3''.encard ≤
      (↑S_prod.card : ENNReal) * (4 * M_G) := by
    rw [h_encard_sum]
    have h_sum_le : ∑ g ∈ S_prod, (↑(fiber g).card : ENNReal) ≤
        ∑ g ∈ S_prod, (4 * M_G) := Finset.sum_le_sum h_fiber_bound
    have h_sum_eq : ∑ g ∈ S_prod, (4 * M_G) = (↑S_prod.card : ENNReal) * (4 * M_G) := by
      simp [Finset.sum_const] <;> ring
    exact le_trans h_sum_le (le_of_eq h_sum_eq)
  have h_final : ENat.toENNReal E3''.encard ≤
      4 * M_G * (ENat.toENNReal S1.encard * ENat.toENNReal S2.encard) := by
    have h1 : ENat.toENNReal E3''.encard ≤ (↑S_prod.card : ENNReal) * (4 * M_G) := h_sum_bound
    have h2 : (↑S_prod.card : ENNReal) * (4 * M_G) ≤
        (↑(S1_fin.card * S2_fin.card) : ENNReal) * (4 * M_G) := by
      gcongr <;> exact_mod_cast hS_prod_card
    have h3 : (↑(S1_fin.card * S2_fin.card) : ENNReal) =
        ENat.toENNReal S1.encard * ENat.toENNReal S2.encard := by
      have h4 : S1.encard = ↑S1_fin.card := by rw [←hS1_coe] <;> simp
      have h5 : S2.encard = ↑S2_fin.card := by rw [←hS2_coe] <;> simp
      rw [h4, h5] <;> simp [mul_comm] <;> norm_cast
    have h4 : (↑(S1_fin.card * S2_fin.card) : ENNReal) * (4 * M_G) =
        (ENat.toENNReal S1.encard * ENat.toENNReal S2.encard) * (4 * M_G) := by
      rw [h3]
    have h5 : (ENat.toENNReal S1.encard * ENat.toENNReal S2.encard) * (4 * M_G) =
        4 * M_G * (ENat.toENNReal S1.encard * ENat.toENNReal S2.encard) := by
      ring
    rw [h4, h5] at h2
    exact le_trans h1 h2
  by_cases h : (4 * M_G) = 0
  · have hE_eq_zero : ENat.toENNReal E3''.encard = 0 := by
      have h' : ENat.toENNReal E3''.encard ≤ (4 * M_G) * (ENat.toENNReal S1.encard * ENat.toENNReal S2.encard) := h_final
      rw [h] at h'
      simp at h' ⊢ <;> exact h'
    rw [hE_eq_zero]
    <;> simp
  · by_cases h_top : (4 * M_G) = ⊤
    · rw [h_top]
      <;> simp
    · have h_iff : ENat.toENNReal E3''.encard / (4 * M_G) ≤
          ENat.toENNReal S1.encard * ENat.toENNReal S2.encard ↔
        ENat.toENNReal E3''.encard ≤
          (4 * M_G) * (ENat.toENNReal S1.encard * ENat.toENNReal S2.encard) :=
        ENNReal.div_le_iff' h h_top
      exact h_iff.mpr h_final

/-- **Coordinate-wise product lower bound from occupancy and rounding**.

Like `product_lower_from_occupancy`, but takes a 1D rounding function
`round_fun : ℝ → ℝ` with coordinate-wise bound `|z - round_fun z| ≤ δ/2`
instead of a 2D rounding with Euclidean `dist ≤ δ/2`.

The cube-counting argument only needs coordinate-wise bounds, so the
conclusion is identical: `N(S1) * N(S2) ≥ |E3''| / (4 * M_G)`. -/
lemma product_lower_from_occupancy_coord
    {δ : ℝ} (hδ_pos : 0 < δ)
    {E3'' : Set (EuclideanSpace ℝ (Fin 2))}
    {S1 S2 : Set ℝ}
    {M_G : ENNReal}
    (hE3''_finite : E3''.Finite)
    (hS1_finite : S1.Finite) (hS2_finite : S2.Finite)
    (hS1_grid : ∀ x ∈ S1, x ∈ productLikeIntegerGrid δ)
    (hS2_grid : ∀ x ∈ S2, x ∈ productLikeIntegerGrid δ)
    (hS1_sep : ∀ x ∈ S1, ∀ y ∈ S1, x ≠ y → |x - y| ≥ δ)
    (hS2_sep : ∀ x ∈ S2, ∀ y ∈ S2, x ≠ y → |x - y| ≥ δ)
    (h_occupancy : ∀ Q ∈ dyadicCubes 2 δ,
        ENat.toENNReal (E3'' ∩ Q).encard ≤ M_G)
    (round_fun : ℝ → ℝ)
    (h_round_near : ∀ z, |z - round_fun z| ≤ δ / 2)
    (h_round_image : ∀ p ∈ E3'', round_fun (p 0) ∈ S1 ∧ round_fun (p 1) ∈ S2) :
    Nreal δ S1 * Nreal δ S2 ≥
      ENat.toENNReal E3''.encard / (4 * M_G) := by
  let round2 : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun p => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun i => round_fun (p i))
  have h_round2_coord : ∀ p i, |p i - round2 p i| ≤ δ / 2 := by
    intro p i; exact h_round_near (p i)
  let E_fin := hE3''_finite.toFinset
  let S1_fin := hS1_finite.toFinset
  let S2_fin := hS2_finite.toFinset
  have hE_coe : (E_fin : Set _) = E3'' := hE3''_finite.coe_toFinset
  have hS1_coe : (S1_fin : Set _) = S1 := hS1_finite.coe_toFinset
  have hS2_coe : (S2_fin : Set _) = S2 := hS2_finite.coe_toFinset
  have hN1 : Nreal δ S1 = ENat.toENNReal S1.encard := by
    have h1 : Nreal δ S1 = ENNReal.ofReal (S1.ncard : ℝ) :=
      grid_separated_nreal_eq_card1d hδ_pos hS1_finite hS1_grid hS1_sep
    have h2 : ENNReal.ofReal (S1.ncard : ℝ) = ENat.toENNReal S1.encard := by
      have h_ncard : S1.ncard = S1_fin.card := by rw [←hS1_coe] <;> simp
      have h_encard : S1.encard = ↑S1_fin.card := by rw [←hS1_coe] <;> simp
      rw [h_ncard, h_encard] <;> simp <;> norm_cast
    rw [h1, h2]
  have hN2 : Nreal δ S2 = ENat.toENNReal S2.encard := by
    have h1 : Nreal δ S2 = ENNReal.ofReal (S2.ncard : ℝ) :=
      grid_separated_nreal_eq_card1d hδ_pos hS2_finite hS2_grid hS2_sep
    have h2 : ENNReal.ofReal (S2.ncard : ℝ) = ENat.toENNReal S2.encard := by
      have h_ncard : S2.ncard = S2_fin.card := by rw [←hS2_coe] <;> simp
      have h_encard : S2.encard = ↑S2_fin.card := by rw [←hS2_coe] <;> simp
      rw [h_ncard, h_encard] <;> simp <;> norm_cast
    rw [h1, h2]
  rw [hN1, hN2]
  let fiber (g : EuclideanSpace ℝ (Fin 2)) : Finset (EuclideanSpace ℝ (Fin 2)) :=
    E_fin.filter (fun p => round2 p = g)
  let S_prod : Finset (EuclideanSpace ℝ (Fin 2)) := E_fin.image round2
  have h_g_in_product : ∀ g ∈ S_prod, g 0 ∈ S1 ∧ g 1 ∈ S2 := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨p, hp, rfl⟩
    have hpe : p ∈ E3'' := by rw [←hE_coe] <;> exact hp
    exact h_round_image p hpe
  have h_fiber_bound : ∀ g ∈ S_prod,
      (↑(fiber g).card : ENNReal) ≤ 4 * M_G := by
    intro g hg
    have hg0 : g 0 ∈ S1 := (h_g_in_product g hg).1
    have hg1 : g 1 ∈ S2 := (h_g_in_product g hg).2
    obtain ⟨a, ha⟩ := hS1_grid (g 0) hg0
    obtain ⟨b, hb⟩ := hS2_grid (g 1) hg1
    let C_g : Finset (Fin 2 → ℤ) := (fiber g).image (cubeIndex δ)
    have hCg_le_4 : C_g.card ≤ 4 := by
      let idx0 : Finset ℤ := {a - 1, a}
      let idx1 : Finset ℤ := {b - 1, b}
      let allowed : Finset (Fin 2 → ℤ) :=
        (Finset.product idx0 idx1).image (fun p : ℤ × ℤ =>
          fun i : Fin 2 => if i = 0 then p.1 else p.2)
      have h_sub : C_g ⊆ allowed := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
        have hpe : p ∈ E_fin := (Finset.mem_filter.mp hp).1
        have h_eq : round2 p = g := (Finset.mem_filter.mp hp).2
        have h_coord0 : |p 0 - g 0| ≤ δ / 2 := by
          have h := h_round2_coord p 0; rw [h_eq] at h; exact h
        have h_coord1 : |p 1 - g 1| ≤ δ / 2 := by
          have h := h_round2_coord p 1; rw [h_eq] at h; exact h
        have h_in_cube : p ∈ dyadicCube δ (cubeIndex δ p) :=
          point_in_cubeIndex_cube hδ_pos p
        have h_bound := cube_index_near_grid_coord hδ_pos ha hb h_coord0 h_coord1
          (h_in_cube 0) (h_in_cube 1)
        have h_k0 : cubeIndex δ p 0 = a - 1 ∨ cubeIndex δ p 0 = a := h_bound.1
        have h_k1 : cubeIndex δ p 1 = b - 1 ∨ cubeIndex δ p 1 = b := h_bound.2
        let p' : ℤ × ℤ := (cubeIndex δ p 0, cubeIndex δ p 1)
        have hp'_in : p' ∈ Finset.product idx0 idx1 := by
          simp [p', idx0, idx1, h_k0, h_k1] <;> tauto
        have h_final : cubeIndex δ p ∈ allowed := by
          apply Finset.mem_image.mpr
          refine ⟨p', hp'_in, ?_⟩
          funext i; fin_cases i <;> simp [p'] <;> rfl
        exact h_final
      have h_card : allowed.card ≤ 4 := by
        have h : allowed.card ≤ (Finset.product idx0 idx1).card := by exact Finset.card_image_le
        have hcp : (Finset.product idx0 idx1).card = idx0.card * idx1.card := Finset.card_product idx0 idx1
        rw [hcp] at h
        simpa [idx0, idx1] using h
      exact le_trans (Finset.card_le_card h_sub) h_card
    let A (k : Fin 2 → ℤ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
      (hE3''_finite.subset (Set.inter_subset_left (s := E3'') (t := dyadicCube δ k))).toFinset
    have hA_eq : ∀ k, (A k : Set _) = E3'' ∩ dyadicCube δ k := by
      intro k; simp [A]
    have h_fiber_sub : fiber g ⊆ C_g.biUnion A := by
      intro p hp
      have hpf : p ∈ fiber g := hp
      have hpe : p ∈ E_fin := (Finset.mem_filter.mp hpf).1
      have hpe' : p ∈ E3'' := by rw [←hE_coe] <;> exact hpe
      let k := cubeIndex δ p
      have hk : k ∈ C_g := Finset.mem_image.mpr ⟨p, hpf, rfl⟩
      have h_in_cube : p ∈ dyadicCube δ k := point_in_cubeIndex_cube hδ_pos p
      have h_in_A : p ∈ A k := by
        simpa [A, hA_eq] using ⟨hpe', h_in_cube⟩
      exact Finset.mem_biUnion.mpr ⟨k, hk, h_in_A⟩
    have h_card_le : (fiber g).card ≤ ∑ k ∈ C_g, (A k).card := by
      calc (fiber g).card
        ≤ (C_g.biUnion A).card := Finset.card_le_card h_fiber_sub
      _ ≤ ∑ k ∈ C_g, (A k).card := by exact Finset.card_biUnion_le
    have h_main : (↑(fiber g).card : ENNReal) ≤ ∑ k ∈ C_g, (↑(A k).card : ENNReal) := by
      exact_mod_cast h_card_le
    have h_each : ∀ k ∈ C_g, (↑(A k).card : ENNReal) ≤ M_G := by
      intro k _
      have hQ : dyadicCube δ k ∈ dyadicCubes 2 δ := ⟨k, rfl⟩
      have h_occ : ENat.toENNReal (E3'' ∩ dyadicCube δ k).encard ≤ M_G :=
        h_occupancy (dyadicCube δ k) hQ
      have h_eq : (↑(A k).card : ENNReal) = ENat.toENNReal (E3'' ∩ dyadicCube δ k).encard := by
        have h9 : (A k : Set _) = E3'' ∩ dyadicCube δ k := hA_eq k
        have h10 : (E3'' ∩ dyadicCube δ k).encard = ↑(A k).card := by
          rw [←h9] <;> simp
        simp [h10]
      rw [h_eq]; exact h_occ
    have h_sum_le : ∑ k ∈ C_g, (↑(A k).card : ENNReal) ≤ ∑ k ∈ C_g, M_G :=
      Finset.sum_le_sum h_each
    have h_sum_MG : ∑ k ∈ C_g, M_G = (↑C_g.card : ENNReal) * M_G := by
      simp [Finset.sum_const] <;> ring
    have h_final : (↑C_g.card : ENNReal) * M_G ≤ 4 * M_G := by
      have h : (↑C_g.card : ENNReal) ≤ 4 := by exact_mod_cast hCg_le_4
      exact mul_le_mul_of_nonneg_right h (by positivity)
    calc (↑(fiber g).card : ENNReal)
      ≤ ∑ k ∈ C_g, (↑(A k).card : ENNReal) := h_main
    _ ≤ ∑ k ∈ C_g, M_G := h_sum_le
    _ = (↑C_g.card : ENNReal) * M_G := h_sum_MG
    _ ≤ 4 * M_G := h_final
  let toPair : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun g => (g 0, g 1)
  have h_toPair_inj : Function.Injective toPair := by
    intro g1 g2 h
    ext i
    fin_cases i <;> simp [toPair, Prod.ext_iff] at h ⊢ <;> tauto
  have h_image_sub : S_prod.image toPair ⊆ S1_fin ×ˢ S2_fin := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨g, hg, rfl⟩
    have h1 : g 0 ∈ S1 := (h_g_in_product g hg).1
    have h2 : g 1 ∈ S2 := (h_g_in_product g hg).2
    have h3 : g 0 ∈ S1_fin := by
      have h31 : g 0 ∈ (S1_fin : Set _) := by rw [hS1_coe]; exact h1
      exact h31
    have h4 : g 1 ∈ S2_fin := by
      have h41 : g 1 ∈ (S2_fin : Set _) := by rw [hS2_coe]; exact h2
      exact h41
    exact Finset.mem_product.mpr ⟨h3, h4⟩
  have hS_prod_card : S_prod.card ≤ S1_fin.card * S2_fin.card := by
    have h1 : S_prod.card = (S_prod.image toPair).card := by
      simp [Finset.card_image_of_injective, h_toPair_inj]
    rw [h1]
    have h2 : (S_prod.image toPair).card ≤ (S1_fin ×ˢ S2_fin).card :=
      Finset.card_le_card h_image_sub
    rw [Finset.card_product] at h2
    exact h2
  have h_disj : ∀ g1 ∈ S_prod, ∀ g2 ∈ S_prod,
      g1 ≠ g2 → Disjoint (fiber g1) (fiber g2) := by
    intro g1 _ g2 _ hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h5 : round2 x = g1 := (Finset.mem_filter.mp hx1).2
    have h6 : round2 x = g2 := (Finset.mem_filter.mp hx2).2
    have h7 : g1 = g2 := by
      calc g1 = round2 x := h5.symm
           _ = g2 := h6
    exact False.elim (hne h7)
  have h_union : E_fin = S_prod.biUnion fiber := by
    ext p
    simp only [Finset.mem_biUnion]
    constructor
    · intro hp
      have hg : round2 p ∈ S_prod := Finset.mem_image.mpr ⟨p, hp, rfl⟩
      exact ⟨round2 p, hg, by simp [fiber, hp]⟩
    · rintro ⟨g, _, hpg⟩
      exact (Finset.mem_filter.mp hpg).1
  have h_card_sum : E_fin.card = ∑ g ∈ S_prod, (fiber g).card := by
    rw [h_union, Finset.card_biUnion h_disj]
  have h_encard_sum : ENat.toENNReal E3''.encard =
      ∑ g ∈ S_prod, (↑(fiber g).card : ENNReal) := by
    have h1 : E3''.encard = ↑E_fin.card := by rw [←hE_coe] <;> simp
    have h2 : ENat.toENNReal E3''.encard = (↑E_fin.card : ENNReal) := by
      rw [h1] <;> simp
    have h3 : (↑E_fin.card : ENNReal) = ∑ g ∈ S_prod, (↑(fiber g).card : ENNReal) := by
      rw [h_card_sum] <;> simp [Finset.sum_apply] <;> norm_cast
    rw [h2, h3]
  have h_sum_bound : ENat.toENNReal E3''.encard ≤
      (↑S_prod.card : ENNReal) * (4 * M_G) := by
    rw [h_encard_sum]
    have h_sum_le : ∑ g ∈ S_prod, (↑(fiber g).card : ENNReal) ≤
        ∑ g ∈ S_prod, (4 * M_G) := Finset.sum_le_sum h_fiber_bound
    have h_sum_eq : ∑ g ∈ S_prod, (4 * M_G) = (↑S_prod.card : ENNReal) * (4 * M_G) := by
      simp [Finset.sum_const] <;> ring
    exact le_trans h_sum_le (le_of_eq h_sum_eq)
  have h_final : ENat.toENNReal E3''.encard ≤
      4 * M_G * (ENat.toENNReal S1.encard * ENat.toENNReal S2.encard) := by
    have h1 : ENat.toENNReal E3''.encard ≤ (↑S_prod.card : ENNReal) * (4 * M_G) := h_sum_bound
    have h2 : (↑S_prod.card : ENNReal) * (4 * M_G) ≤
        (↑(S1_fin.card * S2_fin.card) : ENNReal) * (4 * M_G) := by
      gcongr <;> exact_mod_cast hS_prod_card
    have h3 : (↑(S1_fin.card * S2_fin.card) : ENNReal) =
        ENat.toENNReal S1.encard * ENat.toENNReal S2.encard := by
      have h4 : S1.encard = ↑S1_fin.card := by rw [←hS1_coe] <;> simp
      have h5 : S2.encard = ↑S2_fin.card := by rw [←hS2_coe] <;> simp
      rw [h4, h5] <;> simp [mul_comm] <;> norm_cast
    have h4 : (↑(S1_fin.card * S2_fin.card) : ENNReal) * (4 * M_G) =
        (ENat.toENNReal S1.encard * ENat.toENNReal S2.encard) * (4 * M_G) := by
      rw [h3]
    have h5 : (ENat.toENNReal S1.encard * ENat.toENNReal S2.encard) * (4 * M_G) =
        4 * M_G * (ENat.toENNReal S1.encard * ENat.toENNReal S2.encard) := by
      ring
    rw [h4, h5] at h2
    exact le_trans h1 h2
  by_cases h : (4 * M_G) = 0
  · have hE_eq_zero : ENat.toENNReal E3''.encard = 0 := by
      have h' : ENat.toENNReal E3''.encard ≤ (4 * M_G) * (ENat.toENNReal S1.encard * ENat.toENNReal S2.encard) := h_final
      rw [h] at h'
      simp at h' ⊢ <;> exact h'
    rw [hE_eq_zero] <;> simp
  · by_cases h_top : (4 * M_G) = ⊤
    · rw [h_top] <;> simp
    · have h_iff : ENat.toENNReal E3''.encard / (4 * M_G) ≤
          ENat.toENNReal S1.encard * ENat.toENNReal S2.encard ↔
        ENat.toENNReal E3''.encard ≤
          (4 * M_G) * (ENat.toENNReal S1.encard * ENat.toENNReal S2.encard) :=
        ENNReal.div_le_iff' h h_top
      exact h_iff.mpr h_final

end ProductLikeIncidence.ProductReduction
