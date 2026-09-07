module

/-
# Bounded Occupancy from Lipschitz Map

Derives bounded occupancy M_G for the image of a representative set
under a lower-Lipschitz projective map.

## Main results

- `unique_per_cube_from_with_card`: Bridge from the uniqueness output of
  `regular_set_has_bounded_energy_with_card` to per-cube encard ≤ 1.

- `bounded_occupancy_from_lipschitz`: If E has at most one point per δ-cube
  and G is lower Lipschitz on E, then G '' E has bounded occupancy:
  each δ-cube contains at most M_G = (2*L*√2 + 6)^2 points.

- `M_G_power_absorption`: If L ≤ δ^(-q_L), then M_G ≤ δ^(-q_G)
  for any q_G > 2*q_L, for sufficiently small δ.

## Whiteprint node
`bounded_occupancy`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProductLikeIncidence.RoundedGraphAdapter
public import MyLeanRepo.ProductLikeIncidence.PbarPrimeConstruction
public import MyLeanRepo.EnergyTransfer
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set ENNReal Bornology

namespace ProductLikeIncidence

/-- Coordinate difference bounded by distance. -/
private lemma coord_diff_le_dist {p q : EuclideanSpace ℝ (Fin 2)} {i : Fin 2} :
    |p i - q i| ≤ dist p q := by
  have h1 : |(p - q) i| ≤ ‖p - q‖ := Defect36.abs_coord_le_norm (p - q) i
  have h2 : (p - q) i = p i - q i := by simp
  rw [h2] at h1
  rw [dist_eq_norm]
  exact h1

/-- A δ-cube has diameter ≤ δ * √2. -/
private lemma dyadicCube_diam {δ : ℝ} (hδ_pos : 0 < δ) {k : Fin 2 → ℤ}
    {x y : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ dyadicCube δ k) (hy : y ∈ dyadicCube δ k) :
    dist x y ≤ δ * Real.sqrt 2 := by
  have h1 : ∀ i : Fin 2, |x i - y i| < δ := by
    intro i
    have hx' : x i ∈ Set.Ico (δ * (k i : ℝ)) (δ * ((k i : ℝ) + 1)) := hx i
    have hy' : y i ∈ Set.Ico (δ * (k i : ℝ)) (δ * ((k i : ℝ) + 1)) := hy i
    rw [Set.mem_Ico] at hx' hy'
    have h3 : x i - y i < δ := by linarith
    have h4 : -(δ : ℝ) < x i - y i := by linarith
    rw [abs_lt] <;> constructor <;> linarith
  have h2 : (x 0 - y 0)^2 + (x 1 - y 1)^2 ≤ 2 * δ^2 := by
    have h4 : |x 0 - y 0| ≤ δ := by linarith [h1 0]
    have h5 : |x 1 - y 1| ≤ δ := by linarith [h1 1]
    have h6 : (x 0 - y 0)^2 ≤ δ^2 := by
      have h61 : (x 0 - y 0)^2 = |x 0 - y 0|^2 := by rw [sq_abs]
      rw [h61]; gcongr <;> linarith
    have h7 : (x 1 - y 1)^2 ≤ δ^2 := by
      have h71 : (x 1 - y 1)^2 = |x 1 - y 1|^2 := by rw [sq_abs]
      rw [h71]; gcongr <;> linarith
    nlinarith
  have h_norm2 : ‖x - y‖ ^ 2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
    have h : ‖x - y‖ = Real.sqrt ((x 0 - y 0)^2 + (x 1 - y 1)^2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
      <;> ring
    rw [h]
    rw [Real.sq_sqrt (by positivity)]
  have h_main : ‖x - y‖ ≤ δ * Real.sqrt 2 := by
    have h9 : ‖x - y‖ ^ 2 ≤ (δ * Real.sqrt 2)^2 := by
      rw [h_norm2]
      have h10 : (δ * Real.sqrt 2)^2 = 2 * δ^2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      rw [h10]; exact h2
    have h11 : 0 ≤ ‖x - y‖ := norm_nonneg _
    have h12 : 0 ≤ δ * Real.sqrt 2 := by positivity
    nlinarith
  rw [dist_eq_norm]; exact h_main

/-- **Bridge:** uniqueness from `regular_set_has_bounded_energy_with_card`
    gives per-cube encard ≤ 1. -/
lemma unique_per_cube_from_with_card
    {δ : ℝ} {P : Set (EuclideanSpace ℝ (Fin 2))}
    {E : Finset (EuclideanSpace ℝ (Fin 2))}
    (hE_sub_P : (E : Set _) ⊆ P)
    (h_unique : ∀ Q ∈ dyadicCubesMeeting δ P,
      ∃! p, p ∈ E ∧ p ∈ Q ∩ P) :
    ∀ (Q : Set (EuclideanSpace ℝ (Fin 2))),
      Q ∈ dyadicCubes 2 δ → ((E : Set _) ∩ Q).encard ≤ 1 := by
  intro Q hQ
  by_cases h_meet : ((E : Set _) ∩ Q).Nonempty
  · have hQ_meet_P : Q ∈ dyadicCubesMeeting δ P := by
      have h1 : Q ∈ dyadicCubes 2 δ := hQ
      rcases h_meet with ⟨p, hpE, hpQ⟩
      have h2 : p ∈ P := hE_sub_P hpE
      exact ⟨h1, ⟨p, hpQ, h2⟩⟩
    rcases h_unique Q hQ_meet_P with ⟨p0, ⟨hp0_E, hp0_Q, hp0_P⟩, h_uniq⟩
    have h_sub : ((E : Set _) ∩ Q) ⊆ {p0} := by
      intro p hp
      have h_p_E : p ∈ E := hp.1
      have h_p_Q : p ∈ Q := hp.2
      have h_p_P : p ∈ P := hE_sub_P h_p_E
      have h : p ∈ E ∧ p ∈ Q ∩ P := ⟨h_p_E, ⟨h_p_Q, h_p_P⟩⟩
      have h_eq : p = p0 := h_uniq p h
      rw [h_eq]; simp
    have h_encard : ((E : Set _) ∩ Q).encard ≤ ({p0} : Set _).encard :=
      Set.encard_mono h_sub
    simpa using h_encard
  · have h_empty : (E : Set _) ∩ Q = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h_meet
    rw [h_empty]; simp

/-- **Bounded occupancy from lower Lipschitz bound.**

If E has at most one point per δ-cube and G satisfies
`dist x y ≤ L * dist (G x) (G y)` on E, then every δ-cube contains
at most `(2*L*√2 + 6)^2` points of G '' E. -/
lemma bounded_occupancy_from_lipschitz
    {δ : ℝ} (hδ_pos : 0 < δ)
    {L : ℝ} (hL_pos : 0 < L)
    {E : Set (EuclideanSpace ℝ (Fin 2))}
    (hE_finite : E.Finite)
    (h_unique : ∀ (Q : Set (EuclideanSpace ℝ (Fin 2))),
      Q ∈ dyadicCubes 2 δ → (E ∩ Q).encard ≤ 1)
    {G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hG_lip : ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ L * dist (G x) (G y)) :
    ∀ (Q_img : Set (EuclideanSpace ℝ (Fin 2))),
      Q_img ∈ dyadicCubes 2 δ →
      ENat.toENNReal ((G '' E) ∩ Q_img).encard ≤
        ENNReal.ofReal ((2 * L * Real.sqrt 2 + 6) ^ 2) := by
  intro Q_img hQ_img
  rcases hQ_img with ⟨k, hk⟩
  subst hk
  let D := L * (δ * Real.sqrt 2)
  have hD_pos : 0 ≤ D := by positivity

  let E_pre := E ∩ {p | G p ∈ dyadicCube δ k}
  have hE_pre_sub : E_pre ⊆ E := by intro x hx; exact hx.1
  have hE_pre_finite : E_pre.Finite := hE_finite.subset hE_pre_sub

  have h_preimage_diam : ∀ x ∈ E_pre, ∀ y ∈ E_pre, dist x y ≤ D := by
    intro x hx y hy
    have h : dist x y ≤ L * dist (G x) (G y) := hG_lip x hx.1 y hy.1
    have h2 : dist (G x) (G y) ≤ δ * Real.sqrt 2 := dyadicCube_diam hδ_pos hx.2 hy.2
    calc dist x y
      ≤ L * dist (G x) (G y) := h
      _ ≤ L * (δ * Real.sqrt 2) := by gcongr
      _ = D := by ring

  by_cases h_empty : E_pre = ∅
  · have h : (G '' E) ∩ dyadicCube δ k = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_empty_iff_false, iff_false]
      intro h
      rcases h with ⟨⟨x, hx, rfl⟩, hzQ⟩
      have h_x_in_pre : x ∈ E_pre := ⟨hx, hzQ⟩
      rw [h_empty] at h_x_in_pre
      simpa using h_x_in_pre
    rw [h]; simp
  · have h_nonempty : E_pre.Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty
    rcases h_nonempty with ⟨p0, hp0⟩
    have h_center : ∀ p ∈ E_pre, dist p p0 ≤ D := by
      intro p hp; exact h_preimage_diam p hp p0 hp0

    -- Bounds: p0_i - D ≤ p_i ≤ p0_i + D
    have h1a : ∀ p ∈ E_pre, p0 0 - D ≤ p 0 := by
      intro p hp
      have h2 : |p 0 - p0 0| ≤ D := le_trans coord_diff_le_dist (h_center p hp)
      have h3 : -D ≤ p 0 - p0 0 := (abs_le.mp h2).1
      linarith
    have h1b : ∀ p ∈ E_pre, p 0 ≤ p0 0 + D := by
      intro p hp
      have h2 : |p 0 - p0 0| ≤ D := le_trans coord_diff_le_dist (h_center p hp)
      have h3 : p 0 - p0 0 ≤ D := (abs_le.mp h2).2
      linarith
    have h1c : ∀ p ∈ E_pre, p0 1 - D ≤ p 1 := by
      intro p hp
      have h2 : |p 1 - p0 1| ≤ D := le_trans coord_diff_le_dist (h_center p hp)
      have h3 : -D ≤ p 1 - p0 1 := (abs_le.mp h2).1
      linarith
    have h1d : ∀ p ∈ E_pre, p 1 ≤ p0 1 + D := by
      intro p hp
      have h2 : |p 1 - p0 1| ≤ D := le_trans coord_diff_le_dist (h_center p hp)
      have h3 : p 1 - p0 1 ≤ D := (abs_le.mp h2).2
      linarith

    -- Number of δ-cubes meeting E_pre ≤ (2D/δ + 6)^2
    -- The square has side 2D, so call bounded_square_cube_count with D' := 2*D
    let D' := 2 * D
    have hD'_pos : 0 ≤ D' := by positivity
    have h1b' : ∀ p ∈ E_pre, p 0 ≤ (p0 0 - D) + D' := by
      intro p hp
      have h : p 0 ≤ p0 0 + D := h1b p hp
      have h_eq : (p0 0 - D) + D' = p0 0 + D := by
        dsimp only [D'] <;> ring
      rw [h_eq]; exact h
    have h1d' : ∀ p ∈ E_pre, p 1 ≤ (p0 1 - D) + D' := by
      intro p hp
      have h : p 1 ≤ p0 1 + D := h1d p hp
      have h_eq : (p0 1 - D) + D' = p0 1 + D := by
        dsimp only [D'] <;> ring
      rw [h_eq]; exact h
    have h_cube_bound : ENat.toENNReal (dyadicCubesMeeting δ E_pre).encard ≤
        ENNReal.ofReal ((D' / δ + 6) ^ 2) :=
      (Defect36.bounded_square_cube_count hδ_pos hD'_pos
        (a := p0 0 - D) (b := p0 1 - D)
        h1a h1b' h1c h1d').2

    have h_fin_cubes : (dyadicCubesMeeting δ E_pre).Finite :=
      ProductLikeIncidence.dyadicCubesMeeting_finite hδ_pos
        hE_pre_finite.isBounded

    -- Cardinality bound: E_pre.encard ≤ number of cubes meeting E_pre
    -- because each cube contains at most 1 point of E (hence of E_pre).
    let E_pre_fin := hE_pre_finite.toFinset
    let Cubes_fin := h_fin_cubes.toFinset
    let f : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2)) :=
      fun p => dyadicCube δ (cubeIndexOfPoint δ p)

    have hE_pre_fin_coe : (E_pre_fin : Set _) = E_pre := hE_pre_finite.coe_toFinset
    have hCubes_fin_coe : (Cubes_fin : Set _) = dyadicCubesMeeting δ E_pre :=
      h_fin_cubes.coe_toFinset

    have h_f_mem : ∀ p, p ∈ f p := fun p => cubeIndexOfPoint_mem hδ_pos p

    have h_f_in_cubes : ∀ p ∈ E_pre_fin, f p ∈ Cubes_fin := by
      intro p hp
      have h_p_in_Epre : p ∈ E_pre := by
        rw [← hE_pre_fin_coe]; exact hp
      have h1 : f p ∈ dyadicCubes 2 δ := ⟨cubeIndexOfPoint δ p, rfl⟩
      have h2 : (f p ∩ E_pre).Nonempty := ⟨p, h_f_mem p, h_p_in_Epre⟩
      have h3 : f p ∈ dyadicCubesMeeting δ E_pre := ⟨h1, h2⟩
      have h4 : f p ∈ (Cubes_fin : Set _) := by
        rw [hCubes_fin_coe]
        exact h3
      exact h4

    have h_per_cube_le1 : ∀ Q ∈ dyadicCubes 2 δ, (E_pre ∩ Q).encard ≤ 1 := by
      intro Q hQ
      have h1 : (E_pre ∩ Q).encard ≤ (E ∩ Q).encard :=
        Set.encard_mono (by intro x hx; exact ⟨hE_pre_sub hx.1, hx.2⟩)
      exact le_trans h1 (h_unique Q hQ)

    have h_f_inj : Set.InjOn f (E_pre_fin : Set _) := by
      intro x hx y hy h_eq
      have hx_in : x ∈ f x := h_f_mem x
      have hy_in : y ∈ f y := h_f_mem y
      have hy_in' : y ∈ f x := h_eq.symm ▸ hy_in
      have h_x_in_pre : x ∈ E_pre := by rw [← hE_pre_fin_coe]; exact hx
      have h_y_in_pre : y ∈ E_pre := by rw [← hE_pre_fin_coe]; exact hy
      have hQ_cube : f x ∈ dyadicCubes 2 δ := ⟨cubeIndexOfPoint δ x, rfl⟩
      have h_encard_le1 : (E_pre ∩ f x).encard ≤ 1 := h_per_cube_le1 (f x) hQ_cube
      by_cases hxy : x = y
      · exact hxy
      · have h_sub : ({x, y} : Set _) ⊆ E_pre ∩ f x := by
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with (rfl | rfl) <;> tauto
        have h4 : Set.encard ({x, y} : Set _) ≤ Set.encard (E_pre ∩ f x) :=
          Set.encard_mono h_sub
        have h5 : Set.encard ({x, y} : Set _) = 2 := by
          rw [Set.encard_pair hxy] <;> norm_num
        rw [h5] at h4
        have h_cont : (2 : ENat) ≤ (1 : ENat) := le_trans h4 h_encard_le1
        simpa using h_cont

    let Img_fin := E_pre_fin.image f
    have h_img_sub : Img_fin ⊆ Cubes_fin := by
      intro Q hQ
      rcases Finset.mem_image.mp hQ with ⟨p, hp, rfl⟩
      exact h_f_in_cubes p hp
    have h_card_img : Img_fin.card = E_pre_fin.card :=
      Finset.card_image_of_injOn h_f_inj
    have h_card_le : E_pre_fin.card ≤ Cubes_fin.card := by
      calc E_pre_fin.card = Img_fin.card := h_card_img.symm
        _ ≤ Cubes_fin.card := Finset.card_le_card h_img_sub

    have h_encard_le : ENat.toENNReal E_pre.encard ≤
        ENat.toENNReal (dyadicCubesMeeting δ E_pre).encard := by
      have h1 : E_pre.encard = ↑E_pre_fin.card := by
        rw [← Set.encard_coe_eq_coe_finsetCard E_pre_fin, hE_pre_fin_coe]
      have h2 : (dyadicCubesMeeting δ E_pre).encard = ↑Cubes_fin.card := by
        rw [← Set.encard_coe_eq_coe_finsetCard Cubes_fin, hCubes_fin_coe]
      rw [h1, h2]
      exact_mod_cast h_card_le

    have h_img_eq : (G '' E) ∩ dyadicCube δ k = G '' E_pre := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_image, E_pre]
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, hzQ⟩; exact ⟨x, ⟨hx, hzQ⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hzQ⟩, rfl⟩; exact ⟨⟨x, hx, rfl⟩, hzQ⟩
    rw [h_img_eq]

    have h_inj : Set.InjOn G E_pre := by
      intro x hx y hy h_eq
      have h : dist x y ≤ L * dist (G x) (G y) := hG_lip x hx.1 y hy.1
      have h7 : dist (G x) (G y) = 0 := by
        rw [h_eq] <;> exact dist_self _
      rw [h7] at h
      have h5 : dist x y ≤ 0 := by simpa using h
      have h6 : dist x y = 0 := by
        have h_nonneg : 0 ≤ dist x y := dist_nonneg
        linarith
      exact dist_eq_zero.mp h6

    let Img_G := E_pre_fin.image G
    have hImgG_coe : (Img_G : Set _) = G '' E_pre := by
      ext z
      simp [Img_G, E_pre_fin, hE_pre_fin_coe] <;> aesop
    have h_inj' : Set.InjOn G (E_pre_fin : Set _) := by
      rw [hE_pre_fin_coe]
      exact h_inj
    have h_card_eq_G : Img_G.card = E_pre_fin.card :=
      Finset.card_image_of_injOn h_inj'
    have h_card_imgG : ENat.toENNReal (G '' E_pre).encard = ENat.toENNReal E_pre.encard := by
      have h1 : (G '' E_pre).encard = (↑Img_G : Set (EuclideanSpace ℝ (Fin 2))).encard := by
        rw [hImgG_coe]
      have h2 : (↑Img_G : Set (EuclideanSpace ℝ (Fin 2))).encard = ↑Img_G.card :=
        Set.encard_coe_eq_coe_finsetCard Img_G
      have h3 : E_pre.encard = (↑E_pre_fin : Set (EuclideanSpace ℝ (Fin 2))).encard := by
        rw [hE_pre_fin_coe]
      have h4 : (↑E_pre_fin : Set (EuclideanSpace ℝ (Fin 2))).encard = ↑E_pre_fin.card :=
        Set.encard_coe_eq_coe_finsetCard E_pre_fin
      have h6 : (G '' E_pre).encard = E_pre.encard := by
        calc (G '' E_pre).encard
          = (↑Img_G : Set (EuclideanSpace ℝ (Fin 2))).encard := h1
        _ = ↑Img_G.card := h2
        _ = ↑E_pre_fin.card := by rw [h_card_eq_G]
        _ = (↑E_pre_fin : Set (EuclideanSpace ℝ (Fin 2))).encard := h4.symm
        _ = E_pre.encard := h3.symm
      exact_mod_cast h6
    rw [h_card_imgG]

    have hD'_over_δ : D' / δ = 2 * L * Real.sqrt 2 := by
      dsimp only [D', D]
      field_simp [hδ_pos.ne'] <;> ring
    rw [hD'_over_δ] at h_cube_bound
    exact le_trans h_encard_le h_cube_bound

/-- **Power absorption for M_G.**

If `q_G > 2 * q_L`, there exists `δ₀ > 0` such that for all `0 < δ ≤ δ₀`,
if `0 ≤ L ≤ δ^(-q_L)`, then `M_G = (2*L*√2 + 6)^2 ≤ δ^(-q_G)`.

The additive constant 6 and multiplicative factor `2√2` are absorbed
into the slack `q_G - 2*q_L > 0` for sufficiently small δ. -/
lemma M_G_power_absorption {q_L q_G : ℝ}
    (hq_L_pos : 0 < q_L) (hqG_gt : q_G > 2 * q_L) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < 1 → δ ≤ δ₀ →
      ∀ L, 0 ≤ L → L ≤ δ ^ (-q_L) →
        (2 * L * Real.sqrt 2 + 6) ^ 2 ≤ δ ^ (-q_G) := by
  let ε := q_G - 2 * q_L
  have hε_pos : 0 < ε := by linarith
  let C : ℝ := (2 * Real.sqrt 2 + 1) ^ 2
  have hC_pos : 0 < C := by positivity
  let δ₁ : ℝ := (1 / 6 : ℝ) ^ (1 / q_L)
  let δ₂ : ℝ := C ^ (-1 / ε)
  let δ₀ : ℝ := min δ₁ δ₂
  have hδ₁_pos : 0 < δ₁ := by positivity
  have hδ₂_pos : 0 < δ₂ := by positivity
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine' ⟨δ₀, hδ₀_pos, _⟩
  intro δ hδ_pos hδ_lt_one hδ_leδ₀ L hL_nonneg hL
  have hδ_leδ₁ : δ ≤ δ₁ := le_trans hδ_leδ₀ (min_le_left _ _)
  have hδ_leδ₂ : δ ≤ δ₂ := le_trans hδ_leδ₀ (min_le_right _ _)

  -- Step 1: 6 ≤ δ^(-q_L) since δ ≤ (1/6)^(1/q_L)
  have h6 : 6 ≤ δ ^ (-q_L) := by
    have h1 : δ ^ q_L ≤ 1 / 6 := by
      have h2 : δ ≤ (1 / 6 : ℝ) ^ (1 / q_L) := hδ_leδ₁
      have h3 : δ ^ q_L ≤ ((1 / 6 : ℝ) ^ (1 / q_L)) ^ q_L := by gcongr
      have h4 : ((1 / 6 : ℝ) ^ (1 / q_L)) ^ q_L = 1 / 6 := by
        rw [← Real.rpow_mul (show (0 : ℝ) ≤ 1 / 6 by norm_num)]
        <;> field_simp [hq_L_pos.ne'] <;> ring
      rw [h4] at h3; exact h3
    have h5 : δ ^ (-q_L) = (δ ^ q_L)⁻¹ := by
      rw [Real.rpow_neg (by linarith)] <;> ring
    rw [h5]
    have h6pos : 0 < δ ^ q_L := by positivity
    field_simp [h6pos.ne'] <;> nlinarith

  -- Step 2: 2*L*√2 + 6 ≤ (2*√2+1) * δ^(-q_L)
  have h_bound1 : 2 * L * Real.sqrt 2 + 6 ≤ (2 * Real.sqrt 2 + 1) * δ ^ (-q_L) := by
    have h7 : 2 * L * Real.sqrt 2 ≤ 2 * Real.sqrt 2 * δ ^ (-q_L) := by
      have h71 : 0 ≤ 2 * Real.sqrt 2 := by positivity
      nlinarith [hL]
    linarith

  -- Step 3: M_G ≤ C * δ^(-2*q_L)
  have h_bound2 : (2 * L * Real.sqrt 2 + 6) ^ 2 ≤ C * δ ^ (-2 * q_L) := by
    have h8 : 0 ≤ 2 * L * Real.sqrt 2 + 6 := by positivity
    have h9 : 0 ≤ (2 * Real.sqrt 2 + 1) * δ ^ (-q_L) := by positivity
    have h10 : (2 * L * Real.sqrt 2 + 6) ^ 2 ≤ ((2 * Real.sqrt 2 + 1) * δ ^ (-q_L)) ^ 2 := by
      gcongr
    have h11 : ((2 * Real.sqrt 2 + 1) * δ ^ (-q_L)) ^ 2 = C * δ ^ (-2 * q_L) := by
      have h12 : (δ ^ (-q_L)) ^ 2 = δ ^ (-2 * q_L) := by
        have h121 : (δ ^ (-q_L)) ^ 2 = (δ ^ (-q_L)) * (δ ^ (-q_L)) := by ring
        rw [h121]
        have h122 : (δ ^ (-q_L)) * (δ ^ (-q_L)) = δ ^ (-2 * q_L) := by
          rw [← Real.rpow_add (by linarith)] <;> ring_nf
        exact h122
      simp only [C]
      ring_nf at * <;> rw [h12] <;> ring
    rw [h11] at h10; exact h10

  -- Step 4: C ≤ δ^(-ε) since δ ≤ C^(-1/ε)
  have hC_le : C ≤ δ ^ (-ε) := by
    have h1 : δ ^ ε ≤ C⁻¹ := by
      have h2 : δ ≤ C ^ (-1 / ε) := hδ_leδ₂
      have h3 : δ ^ ε ≤ (C ^ (-1 / ε)) ^ ε := by gcongr
      have h41 : C ^ ((-1 / ε) * ε) = (C ^ (-1 / ε)) ^ ε :=
        Real.rpow_mul (show 0 ≤ C by positivity) (-1 / ε) ε
      have h41' : (C ^ (-1 / ε)) ^ ε = C ^ ((-1 / ε) * ε) := h41.symm
      have h42 : (-1 / ε) * ε = -1 := by
        field_simp [hε_pos.ne'] <;> ring
      have h43 : C ^ (-1 : ℝ) = C⁻¹ := by
        rw [Real.rpow_neg (show 0 ≤ C by positivity)]
        <;> simp
      have h4 : (C ^ (-1 / ε)) ^ ε = C⁻¹ := by
        calc (C ^ (-1 / ε)) ^ ε
          = C ^ ((-1 / ε) * ε) := h41'
        _ = C ^ (-1 : ℝ) := by rw [h42]
        _ = C⁻¹ := h43
      rw [h4] at h3; exact h3
    have h5 : δ ^ (-ε) = (δ ^ ε)⁻¹ := by
      rw [Real.rpow_neg (by linarith)] <;> ring
    rw [h5]
    have h6pos : 0 < δ ^ ε := by positivity
    have h7pos : 0 < C := hC_pos
    have h9 : (C⁻¹)⁻¹ ≤ (δ ^ ε)⁻¹ := by
      gcongr
      <;> linarith
    simpa using h9

  -- Step 5: C * δ^(-2*q_L) ≤ δ^(-ε) * δ^(-2*q_L) = δ^(-q_G)
  have h13 : δ ^ (-q_G) = δ ^ (-ε) * δ ^ (-2 * q_L) := by
    have h14 : -q_G = -ε + -2 * q_L := by simp [ε] <;> ring
    rw [h14]
    rw [← Real.rpow_add (by linarith)] <;> ring
  rw [h13]
  have h15 : 0 ≤ δ ^ (-2 * q_L) := by positivity
  have h16 : C * δ ^ (-2 * q_L) ≤ δ ^ (-ε) * δ ^ (-2 * q_L) := by
    gcongr
    <;> linarith
  exact le_trans h_bound2 h16

/-- Occupancy bound for the image of a per-cube-unique set under a map
    whose inverse is L-Lipschitz.

    Thin wrapper around `bounded_occupancy_from_lipschitz` that derives
    the lower-Lipschitz condition for F from the upper-Lipschitz
    condition on F_inv. -/
lemma occupancy_from_inv_lipschitz
    {δ L : ℝ}
    (hδ_pos : 0 < δ)
    (hL_pos : 0 < L)
    {E3 : Set (EuclideanSpace ℝ (Fin 2))}
    (hE3_finite : E3.Finite)
    {F F_inv : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hF_left_inv : ∀ p ∈ E3, F_inv (F p) = p)
    (hF_inv_lip : ∀ u v, dist (F_inv u) (F_inv v) ≤ L * dist u v)
    (h_per_cube : ∀ (Q : Set (EuclideanSpace ℝ (Fin 2))),
      Q ∈ dyadicCubes 2 δ → (E3 ∩ Q).encard ≤ 1)
    {E3'' : Set (EuclideanSpace ℝ (Fin 2))}
    (hE3''_sub : E3'' ⊆ F '' E3) :
    ∀ (Q : Set (EuclideanSpace ℝ (Fin 2))),
      Q ∈ dyadicCubes 2 δ →
      ENat.toENNReal (E3'' ∩ Q).encard ≤
        ENNReal.ofReal ((2 * L * Real.sqrt 2 + 6) ^ 2) := by
  have hF_lower_lip : ∀ x ∈ E3, ∀ y ∈ E3,
      dist x y ≤ L * dist (F x) (F y) := by
    intro x hx y hy
    have h1 : dist (F_inv (F x)) (F_inv (F y)) ≤ L * dist (F x) (F y) :=
      hF_inv_lip (F x) (F y)
    have h2 : F_inv (F x) = x := hF_left_inv x hx
    have h3 : F_inv (F y) = y := hF_left_inv y hy
    rw [h2, h3] at h1
    exact h1
  have h_main := bounded_occupancy_from_lipschitz
    (hδ_pos := hδ_pos) (hL_pos := hL_pos)
    (hE_finite := hE3_finite) (h_unique := h_per_cube)
    (hG_lip := hF_lower_lip)
  intro Q hQ
  have h_sub : E3'' ∩ Q ⊆ (F '' E3) ∩ Q := by
    intro p hp
    exact ⟨hE3''_sub hp.1, hp.2⟩
  have h4 : ENat.toENNReal (E3'' ∩ Q).encard ≤
      ENat.toENNReal ((F '' E3) ∩ Q).encard := by
    gcongr
  exact le_trans h4 (h_main Q hQ)

end ProductLikeIncidence
