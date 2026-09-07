module

/-
# Product Density from Threefold Selection (Corrected v7)

Bounded occupancy M_G converts cardinality to covering number.
Finite fiber decomposition, proper ENNReal division.
-/

public import MyLeanRepo.ProductLikeIncidence.RoundedGraphAdapter
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set ENNReal

noncomputable section

namespace ProductLikeIncidence

/-- Bounded occupancy to covering number: card(A) ≤ M * Nplane(A). -/
lemma bounded_occupancy_to_covering
    {δ : ℝ} (hδ_pos : 0 < δ)
    {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA_finite : A.Finite)
    {M : ENNReal}
    (h_occ : ∀ (Q : Set (EuclideanSpace ℝ (Fin 2))),
      Q ∈ dyadicCubes 2 δ → ENat.toENNReal (A ∩ Q).encard ≤ M) :
    ENat.toENNReal A.encard ≤ M * ENat.toENNReal (dyadicCoveringNumber δ A) := by
  let Af := hA_finite.toFinset
  let g := cubeIndexOfPoint δ
  let IdxFinset := Af.image g
  have hAf : (Af : Set _) = A := hA_finite.coe_toFinset

  have h_partition : Af.card = ∑ k ∈ IdxFinset, (Af.filter (fun x => g x = k)).card :=
    Finset.card_eq_sum_card_image g Af

  have h_fiber_le : ∀ k ∈ IdxFinset,
      (↑((Af.filter (fun x => g x = k)).card) : ENNReal) ≤ M := by
    intro k hk
    have hQ_dyadic : (dyadicCube δ k) ∈ dyadicCubes 2 δ := ⟨k, rfl⟩
    have h_subAQ : A ∩ (dyadicCube δ k) ⊆ A := by
      intro x hx; exact hx.1
    have h_inter_fin : (A ∩ (dyadicCube δ k)).Finite := Set.Finite.subset hA_finite h_subAQ
    let Qfin := h_inter_fin.toFinset
    have hQfin_coe : (Qfin : Set _) = A ∩ (dyadicCube δ k) := h_inter_fin.coe_toFinset
    have h_subset : (Af.filter (fun x => g x = k)) ⊆ Qfin := by
      intro x hx
      have h_x_in_Af : x ∈ Af := (Finset.mem_filter.mp hx).1
      have h_gx : g x = k := (Finset.mem_filter.mp hx).2
      have h_x_in_A : x ∈ A := by rw [←hAf]; exact h_x_in_Af
      have h_x_in_Q : x ∈ (dyadicCube δ (g x)) := cubeIndexOfPoint_mem hδ_pos x
      have h_x_in_Q' : x ∈ (dyadicCube δ k) := by rw [h_gx] at h_x_in_Q; exact h_x_in_Q
      have h_x_in_inter : x ∈ A ∩ (dyadicCube δ k) := ⟨h_x_in_A, h_x_in_Q'⟩
      have h_goal : x ∈ Qfin := by
        have h9 : x ∈ (Qfin : Set _) := by rw [hQfin_coe]; exact h_x_in_inter
        simpa using h9
      exact h_goal
    have h_card_le : (Af.filter (fun x => g x = k)).card ≤ Qfin.card :=
      Finset.card_le_card h_subset
    have h_encard_le : ENat.toENNReal (A ∩ (dyadicCube δ k)).encard ≤ M := h_occ (dyadicCube δ k) hQ_dyadic
    let QfinSet : Set (EuclideanSpace ℝ (Fin 2)) := ↑Qfin
    have h71 : QfinSet.encard = ↑Qfin.card := Set.encard_coe_eq_coe_finsetCard Qfin
    have h7 : ENat.toENNReal QfinSet.encard = (↑Qfin.card : ENNReal) := by
      rw [h71] <;> norm_cast
    have h_eq : ENat.toENNReal (A ∩ (dyadicCube δ k)).encard = ↑Qfin.card := by
      have h10 : ENat.toENNReal (A ∩ (dyadicCube δ k)).encard = ENat.toENNReal QfinSet.encard := by
        congr; exact hQfin_coe.symm
      rw [h10, h7]
    rw [h_eq] at h_encard_le
    have h_cast : (↑((Af.filter (fun x => g x = k)).card) : ENNReal) ≤ ↑Qfin.card := by
      exact_mod_cast h_card_le
    exact le_trans h_cast h_encard_le

  have h_sum_le : (↑Af.card : ENNReal) ≤ M * ↑IdxFinset.card := by
    have h1 : (↑Af.card : ENNReal) = ∑ k ∈ IdxFinset, (↑((Af.filter (fun x => g x = k)).card) : ENNReal) := by
      exact_mod_cast h_partition
    rw [h1]
    have h2 : ∑ k ∈ IdxFinset, (↑((Af.filter (fun x => g x = k)).card) : ENNReal) ≤ ∑ k ∈ IdxFinset, M := by
      apply Finset.sum_le_sum; intro k hk; exact h_fiber_le k hk
    have h3 : ∑ k ∈ IdxFinset, M = ↑IdxFinset.card * M := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h4 : ↑IdxFinset.card * M = M * ↑IdxFinset.card := by rw [mul_comm]
    rw [h3, h4] at h2
    exact h2

  have h_cover_eq : ENat.toENNReal (dyadicCoveringNumber δ A) = ↑IdxFinset.card :=
    finite_covering2_eq_card hδ_pos hA_finite

  have h_A_card : ENat.toENNReal A.encard = ↑Af.card := by
    let AfSet : Set (EuclideanSpace ℝ (Fin 2)) := ↑Af
    have h51 : AfSet.encard = ↑Af.card := Set.encard_coe_eq_coe_finsetCard Af
    have h5 : ENat.toENNReal AfSet.encard = (↑Af.card : ENNReal) := by
      rw [h51] <;> norm_cast
    have h6 : ENat.toENNReal A.encard = ENat.toENNReal AfSet.encard := by
      congr; exact hAf.symm
    rw [h6]; exact h5

  rw [h_A_card, h_cover_eq]; exact h_sum_le

/-- Product density from threefold selection with bounded occupancy. -/
lemma product_density_from_threefold
    {δ ε η : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hε_pos : 0 < ε) (hη_pos : 0 < η)
    {E E3 : Set (EuclideanSpace ℝ (Fin 2))}
    (hE3_finite : E3.Finite)
    {M_G C1 C2 : ENNReal}
    (hM_G_pos : M_G ≠ 0) (hM_G_top : M_G ≠ ⊤)
    (hC1_pos : C1 ≠ 0) (hC1_top : C1 ≠ ⊤)
    (hC2_pos : C2 ≠ 0) (hC2_top : C2 ≠ ⊤)
    (h_occupancy : ∀ (Q : Set (EuclideanSpace ℝ (Fin 2))),
      Q ∈ dyadicCubes 2 δ → ENat.toENNReal (E3 ∩ Q).encard ≤ M_G)
    (hE3_size : ENat.toENNReal E3.encard ≥
      ENNReal.ofReal (δ ^ (3 * ε)) * ENat.toENNReal (dyadicCoveringNumber δ E))
    (h_proj_x : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0) E3) ≤
      ENNReal.ofReal (δ ^ (-η)) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ E)).toReal)))
    (h_proj_y : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 1) E3) ≤
      ENNReal.ofReal (δ ^ (-η)) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ E)).toReal)))
    (round : ℝ → ℝ)
    {S1 S2 : Set ℝ}
    (hS1_bound : Nreal δ S1 ≤ C1 * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0) E3))
    (hS2_bound : Nreal δ S2 ≤ C2 * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 1) E3))
    (hS1_capture : ENat.toENNReal (E3 ∩ {p : EuclideanSpace ℝ (Fin 2) | round (p 0) ∈ S1}).encard ≥
      (3 / 4 : ENNReal) * ENat.toENNReal E3.encard)
    (hS2_capture : ENat.toENNReal (E3 ∩ {p : EuclideanSpace ℝ (Fin 2) | round (p 1) ∈ S2}).encard ≥
      (3 / 4 : ENNReal) * ENat.toENNReal E3.encard) :
    let E' := E3 ∩ {p : EuclideanSpace ℝ (Fin 2) | round (p 0) ∈ S1} ∩
      {p : EuclideanSpace ℝ (Fin 2) | round (p 1) ∈ S2}
    ENat.toENNReal (dyadicCoveringNumber δ E') ≥
      (1 / 2 : ENNReal) / M_G / C1 / C2 *
      ENNReal.ofReal (δ ^ (3 * ε + 2 * η)) *
        Nreal δ S1 * Nreal δ S2 := by
  let T1 := E3 ∩ {p : EuclideanSpace ℝ (Fin 2) | round (p 0) ∈ S1}
  let T2 := E3 ∩ {p : EuclideanSpace ℝ (Fin 2) | round (p 1) ∈ S2}
  let E' := T1 ∩ T2
  let N_E : ENNReal := ENat.toENNReal (dyadicCoveringNumber δ E)
  let N3 : ENNReal := ENat.toENNReal E3.encard

  have hT1_sub : T1 ⊆ E3 := by intro x hx; exact hx.1
  have hT2_sub : T2 ⊆ E3 := by intro x hx; exact hx.1
  have hE'_sub : E' ⊆ E3 := by intro x hx; exact hT1_sub hx.1

  have hT1_fin : T1.Finite := Set.Finite.subset hE3_finite hT1_sub
  have hT2_fin : T2.Finite := Set.Finite.subset hE3_finite hT2_sub
  have hE'_fin : E'.Finite := Set.Finite.subset hE3_finite hE'_sub

  let E3f := hE3_finite.toFinset
  let T1f := hT1_fin.toFinset
  let T2f := hT2_fin.toFinset
  let E'f := hE'_fin.toFinset

  have hE3f_coe : (E3f : Set (EuclideanSpace ℝ (Fin 2))) = E3 := hE3_finite.coe_toFinset
  have hT1f_coe : (T1f : Set (EuclideanSpace ℝ (Fin 2))) = T1 := hT1_fin.coe_toFinset
  have hT2f_coe : (T2f : Set (EuclideanSpace ℝ (Fin 2))) = T2 := hT2_fin.coe_toFinset
  have hE'f_coe : (E'f : Set (EuclideanSpace ℝ (Fin 2))) = E' := hE'_fin.coe_toFinset

  have hE'f_eq : E'f = T1f ∩ T2f := by
    apply Finset.coe_injective
    rw [Finset.coe_inter, hE'f_coe, hT1f_coe, hT2f_coe] <;> rfl

  have h_card_eq : ∀ (X : Set (EuclideanSpace ℝ (Fin 2))) (Xf : Finset (EuclideanSpace ℝ (Fin 2)))
      (h : (Xf : Set (EuclideanSpace ℝ (Fin 2))) = X),
      ENat.toENNReal X.encard = (↑Xf.card : ENNReal) := by
    intro X Xf h
    have h1 : ENat.toENNReal X.encard = ENat.toENNReal (↑Xf : Set (EuclideanSpace ℝ (Fin 2))).encard := by
      congr 1; exact congr_arg Set.encard h.symm
    rw [h1]
    have h2 : (↑Xf : Set (EuclideanSpace ℝ (Fin 2))).encard = ↑Xf.card :=
      Set.encard_coe_eq_coe_finsetCard Xf
    rw [h2] <;> simp

  have hT1_card : ENat.toENNReal T1.encard = (↑T1f.card : ENNReal) := h_card_eq T1 T1f hT1f_coe
  have hE3_card : ENat.toENNReal E3.encard = (↑E3f.card : ENNReal) := h_card_eq E3 E3f hE3f_coe
  have hT2_card : ENat.toENNReal T2.encard = (↑T2f.card : ENNReal) := h_card_eq T2 T2f hT2f_coe
  have hE'_card : ENat.toENNReal E'.encard = (↑E'f.card : ENNReal) := h_card_eq E' E'f hE'f_coe

  have h4_ne_zero : (4 : ENNReal) ≠ 0 := by simp
  have h4_ne_top : (4 : ENNReal) ≠ ⊤ := by simp
  have h11 : (4 : ENNReal) * (3 / 4 : ENNReal) = (3 : ENNReal) :=
    ENNReal.mul_div_cancel h4_ne_zero h4_ne_top

  have h1_cap_nat : 3 * E3f.card ≤ 4 * T1f.card := by
    have h_orig : ENat.toENNReal T1.encard ≥ (3 / 4 : ENNReal) * ENat.toENNReal E3.encard := hS1_capture
    rw [hT1_card, hE3_card] at h_orig
    have h' : (3 : ENNReal) * ↑E3f.card ≤ (4 : ENNReal) * ↑T1f.card := by
      calc (3 : ENNReal) * ↑E3f.card
        = (4 * (3 / 4 : ENNReal)) * ↑E3f.card := by rw [h11]
      _ = 4 * ((3 / 4 : ENNReal) * ↑E3f.card) := by rw [mul_assoc]
      _ ≤ 4 * ↑T1f.card := by gcongr
    exact_mod_cast h'

  have h2_cap_nat : 3 * E3f.card ≤ 4 * T2f.card := by
    have h_orig : ENat.toENNReal T2.encard ≥ (3 / 4 : ENNReal) * ENat.toENNReal E3.encard := hS2_capture
    rw [hT2_card, hE3_card] at h_orig
    have h' : (3 : ENNReal) * ↑E3f.card ≤ (4 : ENNReal) * ↑T2f.card := by
      calc (3 : ENNReal) * ↑E3f.card
        = (4 * (3 / 4 : ENNReal)) * ↑E3f.card := by rw [h11]
      _ = 4 * ((3 / 4 : ENNReal) * ↑E3f.card) := by rw [mul_assoc]
      _ ≤ 4 * ↑T2f.card := by gcongr
    exact_mod_cast h'

  have hT1f_sub_E3f : T1f ⊆ E3f := by
    intro x hx
    have h : x ∈ (T1f : Set _) := hx
    have h' : x ∈ T1 := by rw [hT1f_coe] at h; exact h
    have h'' : x ∈ E3 := hT1_sub h'
    have h3 : x ∈ (E3f : Set _) := by rw [hE3f_coe]; exact h''
    exact h3
  have hT2f_sub_E3f : T2f ⊆ E3f := by
    intro x hx
    have h : x ∈ (T2f : Set _) := hx
    have h' : x ∈ T2 := by rw [hT2f_coe] at h; exact h
    have h'' : x ∈ E3 := hT2_sub h'
    have h3 : x ∈ (E3f : Set _) := by rw [hE3f_coe]; exact h''
    exact h3
  have hE'f_sub_E3f : E'f ⊆ E3f := by
    intro x hx
    have h : x ∈ (E'f : Set _) := hx
    have h' : x ∈ E' := by rw [hE'f_coe] at h; exact h
    have h'' : x ∈ E3 := hE'_sub h'
    have h3 : x ∈ (E3f : Set _) := by rw [hE3f_coe]; exact h''
    exact h3

  have h_card : E'f.card * 2 ≥ E3f.card := by
    have h2 : (E3f \ E'f).card ≤ (E3f \ T1f).card + (E3f \ T2f).card := by
      have h3 : E3f \ E'f ⊆ (E3f \ T1f) ∪ (E3f \ T2f) := by
        simp only [Finset.subset_iff, Finset.mem_sdiff, Finset.mem_union, hE'f_eq]
        intro x hx
        have h4 : x ∈ E3f := hx.1
        have h5 : x ∉ T1f ∩ T2f := hx.2
        have h6 : x ∉ T1f ∨ x ∉ T2f := by
          by_contra h7; push Not at h7; exact h5 (Finset.mem_inter.mpr h7)
        rcases h6 with (h6 | h6)
        · exact Or.inl ⟨h4, h6⟩
        · exact Or.inr ⟨h4, h6⟩
      calc (E3f \ E'f).card
          ≤ ((E3f \ T1f) ∪ (E3f \ T2f)).card := Finset.card_le_card h3
      _ ≤ (E3f \ T1f).card + (E3f \ T2f).card := Finset.card_union_le _ _
    have h_eq1 : (E3f \ T1f).card + T1f.card = E3f.card := Finset.card_sdiff_add_card_eq_card hT1f_sub_E3f
    have h_eq2 : (E3f \ T2f).card + T2f.card = E3f.card := Finset.card_sdiff_add_card_eq_card hT2f_sub_E3f
    have h_eq3 : (E3f \ E'f).card + E'f.card = E3f.card := Finset.card_sdiff_add_card_eq_card hE'f_sub_E3f
    omega

  have h2_ne_zero : (2 : ENNReal) ≠ 0 := by simp
  have h2_ne_top : (2 : ENNReal) ≠ ⊤ := by simp

  have hE'_card_lower : ENat.toENNReal E'.encard ≥ N3 / 2 := by
    have h6 : (E'f.card : ENNReal) * 2 ≥ (E3f.card : ENNReal) := by exact_mod_cast h_card
    have h_div : (E'f.card : ENNReal) * 2 / 2 = (E'f.card : ENNReal) :=
      ENNReal.mul_div_cancel_right h2_ne_zero h2_ne_top
    have h7 : (E'f.card : ENNReal) ≥ (E3f.card : ENNReal) / 2 := by
      calc (E'f.card : ENNReal)
          = (E'f.card : ENNReal) * 2 / 2 := h_div.symm
      _ ≥ (E3f.card : ENNReal) / 2 := by gcongr
    have hN3 : N3 = (↑E3f.card : ENNReal) := hE3_card
    rw [hE'_card, hN3]; exact h7

  have h_occ_E' : ∀ (Q : Set (EuclideanSpace ℝ (Fin 2))),
      Q ∈ dyadicCubes 2 δ → ENat.toENNReal (E' ∩ Q).encard ≤ M_G := by
    intro Q hQ
    have h_sub : E' ∩ Q ⊆ E3 ∩ Q := by intro x hx; exact ⟨hE'_sub hx.1, hx.2⟩
    have h1 : (E' ∩ Q).encard ≤ (E3 ∩ Q).encard := Set.encard_mono h_sub
    have h2 : ENat.toENNReal (E' ∩ Q).encard ≤ ENat.toENNReal (E3 ∩ Q).encard := by gcongr
    exact le_trans h2 (h_occupancy Q hQ)

  have h_occ_bound : ENat.toENNReal E'.encard ≤
      M_G * ENat.toENNReal (dyadicCoveringNumber δ E') :=
    bounded_occupancy_to_covering hδ_pos hE'_fin h_occ_E'

  have h_Nplane_lower : ENat.toENNReal (dyadicCoveringNumber δ E') ≥
      ENat.toENNReal E'.encard / M_G := by
    calc ENat.toENNReal E'.encard / M_G
        ≤ (M_G * ENat.toENNReal (dyadicCoveringNumber δ E')) / M_G := by gcongr
    _ = ENat.toENNReal (dyadicCoveringNumber δ E') := by
      rw [mul_comm]; exact ENNReal.mul_div_cancel_right hM_G_pos hM_G_top

  have hS1_le : Nreal δ S1 ≤ C1 *
      ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (Real.sqrt (N_E.toReal)) := by
    calc Nreal δ S1
      ≤ C1 * Nreal δ (Set.image (fun p => p 0) E3) := hS1_bound
    _ ≤ C1 * (ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (Real.sqrt (N_E.toReal))) := by gcongr
    _ = C1 * ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (Real.sqrt (N_E.toReal)) := by rw [mul_assoc]

  have hS2_le : Nreal δ S2 ≤ C2 *
      ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (Real.sqrt (N_E.toReal)) := by
    calc Nreal δ S2
      ≤ C2 * Nreal δ (Set.image (fun p => p 1) E3) := hS2_bound
    _ ≤ C2 * (ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (Real.sqrt (N_E.toReal))) := by gcongr
    _ = C2 * ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (Real.sqrt (N_E.toReal)) := by rw [mul_assoc]

  have hN3_top : N3 ≠ ⊤ := by
    have h_encard : E3.encard = ↑E3f.card := by
      rw [←hE3f_coe]
      exact Set.encard_coe_eq_coe_finsetCard E3f
    have h : N3 = (↑E3f.card : ENNReal) := by
      simp only [N3, h_encard] <;> norm_cast
    rw [h]
    <;> simp
  have hN_E_top : N_E ≠ ⊤ := by
    by_contra h
    have h_pos : 0 < δ ^ (3 * ε) := by positivity
    have h1 : ENNReal.ofReal (δ ^ (3 * ε)) * N_E = ⊤ := by
      rw [h]
      have h_pos2 : 0 < δ ^ (3 * ε) := by positivity
      have h_ne_zero : ENNReal.ofReal (δ ^ (3 * ε)) ≠ 0 := (ENNReal.ofReal_pos.mpr h_pos2).ne'
      exact mul_top h_ne_zero
    have h2 : N3 ≥ ENNReal.ofReal (δ ^ (3 * ε)) * N_E := hE3_size
    rw [h1] at h2
    have h3 : N3 = ⊤ := top_le_iff.mp h2
    exact hN3_top h3

  have h_nonneg : 0 ≤ N_E.toReal := by positivity
  have h_sqrt_sq : Real.sqrt (N_E.toReal) * Real.sqrt (N_E.toReal) = N_E.toReal := by
    have h1 : Real.sqrt (N_E.toReal) * Real.sqrt (N_E.toReal) = Real.sqrt ((N_E.toReal) ^ 2) := by
      rw [← Real.sqrt_mul h_nonneg] <;> ring_nf
    rw [h1, Real.sqrt_sq_eq_abs, abs_of_nonneg h_nonneg]

  have h_exp1 : δ ^ (-η) * δ ^ (-η) = δ ^ (-2 * η) := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf
  have h5 : ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (δ ^ (-η)) =
      ENNReal.ofReal (δ ^ (-2 * η)) := by
    rw [← ENNReal.ofReal_mul (by positivity), h_exp1]
  have h6 : ENNReal.ofReal (Real.sqrt (N_E.toReal)) * ENNReal.ofReal (Real.sqrt (N_E.toReal)) = N_E := by
    rw [← ENNReal.ofReal_mul (by positivity), h_sqrt_sq]
    exact ENNReal.ofReal_toReal hN_E_top

  have h_prod_le : Nreal δ S1 * Nreal δ S2 ≤
      C1 * C2 * ENNReal.ofReal (δ ^ (-2 * η)) * N_E := by
    calc Nreal δ S1 * Nreal δ S2
      ≤ (C1 * ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (Real.sqrt (N_E.toReal))) *
          (C2 * ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (Real.sqrt (N_E.toReal))) := by gcongr
    _ = C1 * C2 * (ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (δ ^ (-η))) *
          (ENNReal.ofReal (Real.sqrt (N_E.toReal)) * ENNReal.ofReal (Real.sqrt (N_E.toReal))) := by
      simp [mul_assoc, mul_comm, mul_left_comm] <;> rfl
    _ = C1 * C2 * ENNReal.ofReal (δ ^ (-2 * η)) * N_E := by
      rw [h5, h6] <;> simp [mul_assoc]

  let K := ENNReal.ofReal (δ ^ (2 * η)) / C1 / C2

  have hK_pos : K ≠ 0 := by
    simp only [K, div_eq_mul_inv]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      · exact ENNReal.inv_ne_zero.mpr hC1_top
    · exact ENNReal.inv_ne_zero.mpr hC2_top

  have h_sum2 : 2 * η + (-2 * η) = 0 := by ring
  have h_exp2 : δ ^ (2 * η) * δ ^ (-2 * η) = 1 := by
    have h : δ ^ (2 * η) * δ ^ (-2 * η) = δ ^ (2 * η + (-2 * η)) := by rw [← Real.rpow_add hδ_pos]
    rw [h, h_sum2] <;> simp
  have h2 : ENNReal.ofReal (δ ^ (2 * η)) * ENNReal.ofReal (δ ^ (-2 * η)) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), h_exp2] <;> rw [ENNReal.ofReal_one]
  have h_c1 : C1⁻¹ * C1 = 1 := by
    rw [mul_comm]; exact ENNReal.mul_inv_cancel hC1_pos hC1_top
  have h_c2 : C2⁻¹ * C2 = 1 := by
    rw [mul_comm]; exact ENNReal.mul_inv_cancel hC2_pos hC2_top

  have hK_cancel : K * (C1 * C2 * ENNReal.ofReal (δ ^ (-2 * η))) = 1 := by
    simp only [K, div_eq_mul_inv]
    set a := ENNReal.ofReal (δ ^ (2 * η)) with ha
    set b := ENNReal.ofReal (δ ^ (-2 * η)) with hb
    have h4 : (a * C1⁻¹ * C2⁻¹) * (C1 * C2 * b) = a * b := by
      have h5 : (a * C1⁻¹ * C2⁻¹) * (C1 * C2 * b) = a * (C1⁻¹ * C1) * (C2⁻¹ * C2) * b := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> rfl
      rw [h5, h_c1, h_c2] <;> simp [mul_assoc]
    rw [h4, h2]

  have h_NE_lower : N_E ≥ K * Nreal δ S1 * Nreal δ S2 := by
    have h : K * (Nreal δ S1 * Nreal δ S2) ≤ K * (C1 * C2 * ENNReal.ofReal (δ ^ (-2 * η)) * N_E) := by
      gcongr
    have h' : K * (C1 * C2 * ENNReal.ofReal (δ ^ (-2 * η)) * N_E) = N_E := by
      rw [← mul_assoc, hK_cancel, one_mul]
    rw [h'] at h
    have h_assoc : K * Nreal δ S1 * Nreal δ S2 = K * (Nreal δ S1 * Nreal δ S2) := by rw [mul_assoc]
    rw [h_assoc]; exact h

  have hE'_eq : E' = E3 ∩ {p : EuclideanSpace ℝ (Fin 2) | round (p 0) ∈ S1} ∩
      {p : EuclideanSpace ℝ (Fin 2) | round (p 1) ∈ S2} := by
    ext x; simp [E', T1, T2] <;> tauto

  have h_exp3 : δ ^ (3 * ε) * δ ^ (2 * η) = δ ^ (3 * ε + 2 * η) := by
    rw [← Real.rpow_add hδ_pos]
  have h_mul3 : ENNReal.ofReal (δ ^ (3 * ε)) * ENNReal.ofReal (δ ^ (2 * η)) =
      ENNReal.ofReal (δ ^ (3 * ε + 2 * η)) := by
    rw [← ENNReal.ofReal_mul (by positivity), h_exp3]

  have h_main : ENat.toENNReal (dyadicCoveringNumber δ E') ≥
      (1 / 2 : ENNReal) / M_G / C1 / C2 *
      ENNReal.ofReal (δ ^ (3 * ε + 2 * η)) *
        Nreal δ S1 * Nreal δ S2 := by
    set a := ENNReal.ofReal (δ ^ (3 * ε)) with ha
    set b := ENNReal.ofReal (δ ^ (2 * η)) with hb
    set c := ENNReal.ofReal (δ ^ (3 * ε + 2 * η)) with hc
    set d := Nreal δ S1 * Nreal δ S2 with hd
    have h_ab : a * b = c := h_mul3
    calc ENat.toENNReal (dyadicCoveringNumber δ E')
        ≥ ENat.toENNReal E'.encard / M_G := h_Nplane_lower
    _ ≥ (N3 / 2) / M_G := by gcongr
    _ ≥ ((a * N_E) / 2) / M_G := by gcongr
    _ = (1 / 2 : ENNReal) / M_G * a * N_E := by
      simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    _ ≥ (1 / 2 : ENNReal) / M_G * a * (K * d) := by
      have h_assoc : K * d = K * Nreal δ S1 * Nreal δ S2 := by
        simp [d, mul_assoc]
      have h : (1 / 2 : ENNReal) / M_G * a * N_E ≥ (1 / 2 : ENNReal) / M_G * a * (K * Nreal δ S1 * Nreal δ S2) := by
        gcongr
      rw [h_assoc]; exact h
    _ = (1 / 2 : ENNReal) / M_G / C1 / C2 * c * Nreal δ S1 * Nreal δ S2 := by
      have h_step1 : (1 / 2 : ENNReal) / M_G * a * (K * d) =
          (1 / 2 : ENNReal) / M_G * (a * K) * d := by
        simp only [mul_assoc]
      have h_aK : a * K = c / C1 / C2 := by
        simp only [K, div_eq_mul_inv]
        have h_assoc : a * (b * C1⁻¹ * C2⁻¹) = (a * b) * C1⁻¹ * C2⁻¹ := by
          simp [mul_assoc]
        rw [h_assoc, h_ab]
      rw [h_step1, h_aK, hd]
      simp only [div_eq_mul_inv]
      simp [mul_assoc, mul_comm, mul_left_comm]

  rw [hE'_eq] at h_main
  exact h_main

end ProductLikeIncidence
