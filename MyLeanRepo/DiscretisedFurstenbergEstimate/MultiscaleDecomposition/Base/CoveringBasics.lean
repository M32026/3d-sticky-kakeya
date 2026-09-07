module

/-
Copyright (c) 2024 The Discretised Furstenberg Estimate Team.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raven Team
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.Core

@[expose] public section

noncomputable section

namespace DirecretisedFurstenbergEstimate

namespace MultiscaleDecomposition

/-! # Basic covering number lemmas

This module contains foundational covering number results:
- `externalCoveringNumber_iUnion_le`: finite union subadditivity
- `ball_dyadic_squares_bound`: ball intersects at most 9 side-r squares
- `single_ball_covers_dyadicSquare`: one ball covers a side-r square
- `refine_cover_by_squares`: refinement from scale Δ^k to Δ^(k+1)
- `exists_finite_cover_le`: extract finite cover from finite bound
- `ball_dyadic_squares_bound_4`: ball intersects at most 4 side-L squares when r ≤ L/2
- `four_balls_cover_square`: 4 balls cover a side-L square when r ≥ L√2/4
-/

-- ======================================================================
-- Covering number product lemmas
-- ======================================================================

/-- Finite union subadditivity for external covering numbers. -/
lemma externalCoveringNumber_iUnion_le {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} [Fintype ι] {ε : NNReal} {A : ι → Set X} :
    Metric.externalCoveringNumber ε (⋃ i, A i) ≤
      ∑ i : ι, Metric.externalCoveringNumber ε (A i) := by
  have h_min : ∀ i : ι, ∃ (C_i : Set X), Metric.IsCover ε (A i) C_i ∧
      C_i.encard = Metric.externalCoveringNumber ε (A i) := by
    intro i
    let S : Set (Set X) := {C | Metric.IsCover ε (A i) C}
    have hS_nonempty : S.Nonempty := by
      refine ⟨Set.univ, ?_⟩
      dsimp only [S, Metric.IsCover]
      intro x _
      exact ⟨x, by simp, by simp [Metric.mem_closedBall]⟩
    letI : Nonempty {C : Set X // C ∈ S} := by
      exact hS_nonempty.to_subtype
    let f : {C : Set X // C ∈ S} → ENat := fun C => C.val.encard
    have h_exists : ∃ (x : {C : Set X // C ∈ S}), f x = iInf f :=
      ENat.exists_eq_iInf f
    rcases h_exists with ⟨C, hC⟩
    have hC_prop : Metric.IsCover ε (A i) C.val := C.property
    have h_eq : iInf f = Metric.externalCoveringNumber ε (A i) := by
      simp [f, S, Metric.externalCoveringNumber, iInf_subtype]
      <;> aesop
    have h_final : C.val.encard = Metric.externalCoveringNumber ε (A i) := by
      have h1 : f C = C.val.encard := by rfl
      rw [h1] at hC
      exact hC.trans h_eq
    exact ⟨C.val, hC_prop, h_final⟩
  choose C hC1 hC2 using h_min
  have h_union_cover : Metric.IsCover ε (⋃ i : ι, A i) (⋃ i : ι, C i) := by
    apply Metric.IsCover.of_subset_iUnion_closedBall
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    have h1 : x ∈ ⋃ c ∈ (C i), Metric.closedBall c ε :=
      (hC1 i).subset_iUnion_closedBall hi
    rcases Set.mem_iUnion₂.mp h1 with ⟨c, hc, hxc⟩
    have hc2 : c ∈ (⋃ j : ι, C j) := Set.mem_iUnion.mpr ⟨i, hc⟩
    exact Set.mem_iUnion₂.mpr ⟨c, hc2, hxc⟩
  have h_encard : (⋃ i : ι, C i).encard ≤ ∑ i : ι, (C i).encard := by
    have h_eq_union : (⋃ i : ι, C i) = (⋃ i ∈ Finset.univ, C i) := by
      ext x; simp
    rw [h_eq_union]
    exact Finset.set_encard_biUnion_le Finset.univ C
  have h_main : Metric.externalCoveringNumber ε (⋃ i : ι, A i) ≤ (⋃ i : ι, C i).encard :=
    Metric.IsCover.externalCoveringNumber_le_encard h_union_cover
  calc Metric.externalCoveringNumber ε (⋃ i : ι, A i)
    ≤ (⋃ i : ι, C i).encard := h_main
  _ ≤ ∑ i : ι, (C i).encard := h_encard
  _ = ∑ i : ι, Metric.externalCoveringNumber ε (A i) := by
    congr with i
    exact hC2 i

/-- A ball of radius r intersects at most 9 dyadic squares of side r in R². -/
lemma ball_dyadic_squares_bound (r : ℝ) (hr : 0 < r) (x : EuclideanPlane) :
    ∃ (S : Finset (ℤ × ℤ)),
      (∀ (i j : ℤ), (Metric.closedBall x r ∩ dyadicSquare r i j).Nonempty → (i, j) ∈ S) ∧
      S.card ≤ 9 := by
  let k0 : ℤ := ⌊x 0 / r⌋
  let l0 : ℤ := ⌊x 1 / r⌋
  let S : Finset (ℤ × ℤ) :=
    (Finset.Icc (k0 - 1) (k0 + 1)) ×ˢ (Finset.Icc (l0 - 1) (l0 + 1))
  have h_le1 : (k0 - 1 : ℤ) ≤ (k0 + 1 : ℤ) := by omega
  have h_le2 : (l0 - 1 : ℤ) ≤ (l0 + 1 : ℤ) := by omega
  have h_card1 : (Finset.Icc (k0 - 1) (k0 + 1)).card ≤ 3 := by
    let T : Finset ℤ := {k0 - 1, k0, k0 + 1}
    have h_sub : Finset.Icc (k0 - 1) (k0 + 1) ⊆ T := by
      intro z hz
      simp only [Finset.mem_Icc] at hz
      simp [T, Finset.mem_insert, Finset.mem_singleton] <;> omega
    have hT_card : T.card ≤ 3 := by
      dsimp only [T]
      exact Finset.card_le_three
    exact (Finset.card_le_card h_sub).trans hT_card
  have h_card2 : (Finset.Icc (l0 - 1) (l0 + 1)).card ≤ 3 := by
    let T : Finset ℤ := {l0 - 1, l0, l0 + 1}
    have h_sub : Finset.Icc (l0 - 1) (l0 + 1) ⊆ T := by
      intro z hz
      simp only [Finset.mem_Icc] at hz
      simp [T, Finset.mem_insert, Finset.mem_singleton] <;> omega
    have hT_card : T.card ≤ 3 := by
      dsimp only [T]
      exact Finset.card_le_three
    exact (Finset.card_le_card h_sub).trans hT_card
  have hS_card : S.card ≤ 9 := by
    have h : S.card = (Finset.Icc (k0 - 1) (k0 + 1)).card * (Finset.Icc (l0 - 1) (l0 + 1)).card := by
      rw [Finset.card_product]
    rw [h]
    have h_mul : (Finset.Icc (k0 - 1) (k0 + 1)).card * (Finset.Icc (l0 - 1) (l0 + 1)).card ≤ 3 * 3 := by
      apply mul_le_mul h_card1 h_card2
      <;> positivity
    linarith
  have h_coord_le_norm : ∀ (p : EuclideanPlane) (c : Fin 2),
      |p c - x c| ≤ dist p x := by
    intro p c
    let y : EuclideanPlane := p - x
    let e : EuclideanPlane := EuclideanSpace.single c 1
    have h_cs : |inner ℝ y e| ≤ ‖y‖ * ‖e‖ := by
      exact abs_real_inner_le_norm y e
    have h_norm1 : ‖e‖ = 1 := by
      simp [e, EuclideanSpace.norm_single]
    have h_inner : inner ℝ y e = y c := by
      rw [EuclideanSpace.inner_single_right c 1 y]
      <;> simp
    have h4 : |y c| ≤ ‖y‖ := by
      have h5 : |inner ℝ y e| ≤ ‖y‖ := by
        rw [h_norm1] at h_cs
        <;> simpa using h_cs
      rw [h_inner] at h5
      exact h5
    simpa [dist_eq_norm, y] using h4
  have h_index_bounds : ∀ (c : Fin 2) (idx : ℤ) (p : EuclideanPlane),
      p ∈ Metric.closedBall x r →
      p c ∈ Set.Ico (idx * r) ((idx + 1) * r) →
      ⌊x c / r⌋ - 1 ≤ idx ∧ idx ≤ ⌊x c / r⌋ + 1 := by
    intro c idx p hp hcoord
    let q0 : ℤ := ⌊x c / r⌋
    have h_cb : |p c - x c| ≤ r := by
      have h : |p c - x c| ≤ dist p x := h_coord_le_norm p c
      have h2 : dist p x ≤ r := hp
      linarith
    have h1 : idx * r ≤ p c := hcoord.1
    have h2 : p c < (idx + 1) * r := hcoord.2
    have h3 : p c ≤ x c + r := by linarith [abs_le.mp h_cb]
    have h4 : x c - r ≤ p c := by linarith [abs_le.mp h_cb]
    have h5 : idx ≤ q0 + 1 := by
      have h6 : idx * r ≤ x c + r := by linarith
      have h7 : (idx : ℝ) ≤ x c / r + 1 := by
        calc (idx : ℝ)
          = (idx * r) / r := by field_simp [hr.ne'] <;> ring
        _ ≤ (x c + r) / r := by gcongr
        _ = x c / r + 1 := by
          field_simp [hr.ne'] <;> ring
      have h8 : x c / r < (q0 + 1 : ℝ) := Int.lt_floor_add_one (x c / r)
      have h9 : (idx : ℝ) < (q0 + 2 : ℝ) := by linarith
      have h10 : idx < q0 + 2 := by exact_mod_cast h9
      omega
    have h9 : q0 - 1 ≤ idx := by
      have h10 : x c - r < (idx + 1) * r := by linarith
      have h11 : x c / r - 1 < (idx + 1 : ℝ) := by
        calc x c / r - 1
          = (x c - r) / r := by field_simp [hr.ne'] <;> ring
        _ < ((idx + 1) * r) / r := by gcongr
        _ = (idx + 1 : ℝ) := by field_simp [hr.ne'] <;> ring
      have h12 : (q0 : ℝ) ≤ x c / r := Int.floor_le (x c / r)
      have h13 : (q0 - 1 : ℝ) < (idx + 1 : ℝ) := by linarith
      have h14 : q0 - 1 < idx + 1 := by exact_mod_cast h13
      omega
    exact ⟨h9, h5⟩
  refine ⟨S, ?_, hS_card⟩
  intro i j h
  rcases h with ⟨p, hp_ball, hp_square⟩
  have h_i_bounds := h_index_bounds 0 i p hp_ball hp_square.1
  have h_j_bounds := h_index_bounds 1 j p hp_ball hp_square.2
  have h_i_in : i ∈ Finset.Icc (k0 - 1) (k0 + 1) := by
    simp only [Finset.mem_Icc] <;> omega
  have h_j_in : j ∈ Finset.Icc (l0 - 1) (l0 + 1) := by
    simp only [Finset.mem_Icc] <;> omega
  exact Finset.mem_product.mpr ⟨h_i_in, h_j_in⟩

/-- A single ball of radius r covers a dyadic square of side r. -/
lemma single_ball_covers_dyadicSquare (r : ℝ) (hr : 0 < r) (a b : ℤ) :
    ∃ (x : EuclideanPlane), dyadicSquare r a b ⊆ Metric.closedBall x r := by
  let center : EuclideanPlane :=
    WithLp.toLp 2 fun k : Fin 2 =>
      if k = 0 then (a : ℝ) * r + r / 2 else (b : ℝ) * r + r / 2
  refine ⟨center, ?_⟩
  intro p hp
  have hc0 : center 0 = (a : ℝ) * r + r / 2 := by simp [center] <;> ring
  have hc1 : center 1 = (b : ℝ) * r + r / 2 := by simp [center] <;> ring
  have h3 : |p 0 - center 0| ≤ r / 2 := by
    rw [hc0]
    have h4 : p 0 ∈ Set.Ico ((a : ℝ) * r) (((a : ℝ) + 1) * r) := hp.1
    have h5 : (a : ℝ) * r ≤ p 0 := h4.1
    have h6 : p 0 < ((a : ℝ) + 1) * r := h4.2
    rw [abs_le]
    constructor <;> linarith
  have h4 : |p 1 - center 1| ≤ r / 2 := by
    rw [hc1]
    have h5 : p 1 ∈ Set.Ico ((b : ℝ) * r) (((b : ℝ) + 1) * r) := hp.2
    have h6 : (b : ℝ) * r ≤ p 1 := h5.1
    have h7 : p 1 < ((b : ℝ) + 1) * r := h5.2
    rw [abs_le]
    constructor <;> linarith
  let y : EuclideanPlane := p - center
  have h5 : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := by
    have h6 : ‖y‖ ^ 2 = ∑ i : Fin 2, (y i) ^ 2 := EuclideanSpace.real_norm_sq_eq y
    rw [h6]
    <;> simp [Fin.sum_univ_two]
    <;> ring
  have h7 : ‖y‖ ≤ r := by
    have h8 : ‖y‖ ^ 2 ≤ r ^ 2 := by
      rw [h5]
      have h91 : (y 0) ^ 2 ≤ (r / 2) ^ 2 := by
        have h10 : |y 0| ≤ r / 2 := by simpa [y] using h3
        have h11 : (y 0) ^ 2 = |y 0| ^ 2 := by rw [sq_abs]
        rw [h11]
        gcongr
      have h92 : (y 1) ^ 2 ≤ (r / 2) ^ 2 := by
        have h12 : |y 1| ≤ r / 2 := by simpa [y] using h4
        have h13 : (y 1) ^ 2 = |y 1| ^ 2 := by rw [sq_abs]
        rw [h13]
        gcongr
      nlinarith
    have h10 : 0 ≤ ‖y‖ := by positivity
    nlinarith
  simpa [Metric.mem_closedBall, dist_eq_norm, y] using h7

/-- Helper: coercion from ENat to ENNReal is monotone. -/
lemma enat_to_ennreal_mono {a b : ENat} (h : a ≤ b) :
    (a : ENNReal) ≤ (b : ENNReal) := by
  cases a with
  | top =>
    cases b with
    | top => simp
    | coe _ => exfalso; simp at h <;> contradiction
  | coe a' =>
    cases b with
    | top => simp
    | coe b' =>
      have h2 : a' ≤ b' := by exact_mod_cast h
      simp [h2] <;> norm_cast

/-- Refinement: given a finite cover at scale Δ^k, bound the covering number at
    scale Δ^(k+1) using uniformity and the 9-squares bound. -/
lemma refine_cover_by_squares {P : Set EuclideanPlane} {k m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsUniform P m Δ N) (hk : k < m)
    (A : Set EuclideanPlane) (hA : A ⊆ P)
    (C : Finset EuclideanPlane) (hC : Metric.IsCover (Δ^k).toNNReal A C) :
    Metric.externalCoveringNumber (Δ^(k+1)).toNNReal A ≤
      (C.card : ENNReal) * 9 * (N k : ENNReal) := by
  have hΔ : 0 < Δ := h_uniform.1
  have hΔk : 0 < Δ^k := by positivity
  let squares (c : EuclideanPlane) : Finset (ℤ × ℤ) :=
    Classical.choose (ball_dyadic_squares_bound (Δ^k) hΔk c)
  have h_squares_prop (c : EuclideanPlane) :
    (∀ (i j : ℤ), (Metric.closedBall c (Δ^k) ∩ dyadicSquare (Δ^k) i j).Nonempty → (i, j) ∈ squares c) ∧
    (squares c).card ≤ 9 :=
    Classical.choose_spec (ball_dyadic_squares_bound (Δ^k) hΔk c)
  let inj : (ℤ × ℤ) → EuclideanPlane × (ℤ × ℤ) := fun p => (Classical.arbitrary EuclideanPlane, p)
  let f_inj (c : EuclideanPlane) : Function.Injective (fun p : ℤ × ℤ => (c, p)) := by
    intro p1 p2 h
    exact congr_arg Prod.snd h
  let idx : Finset (EuclideanPlane × (ℤ × ℤ)) :=
    C.biUnion fun c => (squares c).map ⟨fun p : ℤ × ℤ => (c, p), f_inj c⟩
  let Q (p : EuclideanPlane × (ℤ × ℤ)) : Set EuclideanPlane :=
    dyadicSquare (Δ^k) p.2.1 p.2.2
  letI : Fintype {p : EuclideanPlane × (ℤ × ℤ) // p ∈ idx} := by exact idx.fintypeCoeSort
  let A' (i : {p // p ∈ idx}) : Set EuclideanPlane := P ∩ Q i.val
  let U : Set EuclideanPlane := ⋃ (i : {p // p ∈ idx}), A' i
  have h_cover : A ⊆ U := by
    intro x hx
    have h2 : x ∈ P := hA hx
    have h_sub : A ⊆ ⋃ c ∈ C, Metric.closedBall c (Δ^k).toNNReal :=
      hC.subset_iUnion_closedBall
    have h4 : x ∈ ⋃ c ∈ C, Metric.closedBall c (Δ^k).toNNReal := h_sub hx
    have h5 : ∃ (c : EuclideanPlane), c ∈ C ∧ x ∈ Metric.closedBall c (Δ^k).toNNReal := by
      simpa [Set.mem_iUnion] using h4
    rcases h5 with ⟨c, hcC, hcBall⟩
    have hcBall' : dist x c ≤ Δ^k := by
      have h6 : x ∈ Metric.closedBall c (Δ^k).toNNReal := hcBall
      have h7 : dist x c ≤ ↑(Δ^k).toNNReal := by
        simpa [Metric.mem_closedBall] using h6
      have h8 : (↑(Δ^k).toNNReal : ℝ) = Δ^k := by
        simp [hΔk]
        <;> linarith
      rw [h8] at h7
      exact h7
    let a : ℤ := ⌊x 0 / (Δ^k)⌋
    let b : ℤ := ⌊x 1 / (Δ^k)⌋
    have h_x_in_square : x ∈ dyadicSquare (Δ^k) a b := by
      have h_floor1 : (a : ℝ) ≤ x 0 / (Δ^k) := Int.floor_le (x 0 / (Δ^k))
      have h_floor2 : x 0 / (Δ^k) < (a + 1 : ℝ) := Int.lt_floor_add_one (x 0 / (Δ^k))
      have h_left1 : (a : ℝ) * (Δ^k) ≤ x 0 := by
        calc (a : ℝ) * (Δ^k)
          ≤ (x 0 / (Δ^k)) * (Δ^k) := by gcongr
        _ = x 0 := by field_simp [hΔk.ne'] <;> ring
      have h_right1 : x 0 < ((a : ℝ) + 1) * (Δ^k) := by
        calc x 0
          = (x 0 / (Δ^k)) * (Δ^k) := by field_simp [hΔk.ne'] <;> ring
        _ < ((a : ℝ) + 1) * (Δ^k) := by gcongr
      have h_floor3 : (b : ℝ) ≤ x 1 / (Δ^k) := Int.floor_le (x 1 / (Δ^k))
      have h_floor4 : x 1 / (Δ^k) < (b + 1 : ℝ) := Int.lt_floor_add_one (x 1 / (Δ^k))
      have h_left2 : (b : ℝ) * (Δ^k) ≤ x 1 := by
        calc (b : ℝ) * (Δ^k)
          ≤ (x 1 / (Δ^k)) * (Δ^k) := by gcongr
        _ = x 1 := by field_simp [hΔk.ne'] <;> ring
      have h_right2 : x 1 < ((b : ℝ) + 1) * (Δ^k) := by
        calc x 1
          = (x 1 / (Δ^k)) * (Δ^k) := by field_simp [hΔk.ne'] <;> ring
        _ < ((b : ℝ) + 1) * (Δ^k) := by gcongr
      exact ⟨⟨h_left1, h_right1⟩, ⟨h_left2, h_right2⟩⟩
    have h_intersect : (Metric.closedBall c (Δ^k) ∩ dyadicSquare (Δ^k) a b).Nonempty :=
      ⟨x, by simpa [Metric.mem_closedBall] using hcBall', h_x_in_square⟩
    have h_in_squares : (a, b) ∈ squares c := (h_squares_prop c).1 a b h_intersect
    let p_val : EuclideanPlane × (ℤ × ℤ) := ⟨c, ⟨a, b⟩⟩
    have h_in_idx : p_val ∈ idx := by
      have h_in_map : p_val ∈ (squares c).map ⟨fun p : ℤ × ℤ => (c, p), fun p1 p2 h => by simp_all⟩ :=
        Finset.mem_map.mpr ⟨(a, b), h_in_squares, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨c, hcC, h_in_map⟩
    let i : {p // p ∈ idx} := ⟨p_val, h_in_idx⟩
    have hxi : x ∈ A' i := ⟨h2, h_x_in_square⟩
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩
  have h_each_enat : ∀ p ∈ idx, Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p) ≤ ↑(N k) := by
    intro p hp
    by_cases hne : (P ∩ Q p).Nonempty
    · have hne' := hne
      rcases hne with ⟨x, hxP, hxQ⟩
      let a := p.2.1
      let b := p.2.2
      have hQ_eq : Q p = dyadicSquare (Δ^k) a b := by rfl
      have h_unif : (Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p) : ENNReal) = (↑(N k) : ENNReal) :=
        h_uniform.2.2.2.2 k hk a b hne'
      have h_ne_top : Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p) ≠ ⊤ := by
        intro h
        rw [h] at h_unif
        simp at h_unif
      have h_exists : ∃ (m : ℕ), Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p) = ↑m := by
        have h : ∃ (m : ℕ), (↑m : ENat) = Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p) :=
          ENat.ne_top_iff_exists.mp h_ne_top
        rcases h with ⟨m, hm⟩
        exact ⟨m, hm.symm⟩
      rcases h_exists with ⟨m, hm⟩
      have h_eq : (m : ENNReal) = (↑(N k) : ENNReal) := by
        rw [hm] at h_unif
        exact h_unif
      have h_mn : m = N k := by exact_mod_cast h_eq
      have h : Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p) = ↑(N k) := by
        rw [hm, h_mn]
      rw [h] <;> simp
    · have h_empty : P ∩ Q p = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using hne
      rw [h_empty] <;> simp
  have h_union_enat : Metric.externalCoveringNumber (Δ^(k+1)).toNNReal U ≤
      ∑ p ∈ idx, Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p) := by
    have h_main2 : Metric.externalCoveringNumber (Δ^(k+1)).toNNReal U ≤
        ∑ (i : {p // p ∈ idx}), Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (A' i) :=
      externalCoveringNumber_iUnion_le (ε := (Δ^(k+1)).toNNReal) (A := A')
    have h_main3 : Metric.externalCoveringNumber (Δ^(k+1)).toNNReal U ≤
        ∑ p ∈ idx, Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p) := by
      have h2 : ∑ (i : {p // p ∈ idx}), Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (A' i) =
          ∑ (i : {p // p ∈ idx}), Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q i.val) := by
        apply Finset.sum_congr rfl
        intro i _
        rfl
      have h3 : ∑ (i : {p // p ∈ idx}), Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q i.val) =
          ∑ p ∈ idx, Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p) := by
        let f : EuclideanPlane × (ℤ × ℤ) → ENat := fun p =>
          Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p)
        exact Finset.sum_attach idx f
      calc Metric.externalCoveringNumber (Δ^(k+1)).toNNReal U
        ≤ ∑ (i : {p // p ∈ idx}), Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (A' i) := h_main2
      _ = ∑ (i : {p // p ∈ idx}), Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q i.val) := h2
      _ = ∑ p ∈ idx, Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p) := h3
    exact h_main3
  have h_idx_card : idx.card ≤ C.card * 9 := by
    calc idx.card
      ≤ ∑ c ∈ C, ((squares c).map ⟨fun p : ℤ × ℤ => (c, p), f_inj c⟩).card := Finset.card_biUnion_le
    _ = ∑ c ∈ C, (squares c).card := by
      apply Finset.sum_congr rfl; intro c _; rw [Finset.card_map] <;> simp
    _ ≤ ∑ c ∈ C, 9 := by apply Finset.sum_le_sum; intro c _; exact (h_squares_prop c).2
    _ = C.card * 9 := by rw [Finset.sum_const] <;> ring
  have h_final_enat : Metric.externalCoveringNumber (Δ^(k+1)).toNNReal A ≤ ↑(C.card * 9 * N k) := by
    calc Metric.externalCoveringNumber (Δ^(k+1)).toNNReal A
      ≤ Metric.externalCoveringNumber (Δ^(k+1)).toNNReal U :=
        Metric.externalCoveringNumber_mono_set h_cover
    _ ≤ ∑ p ∈ idx, Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p) := h_union_enat
    _ ≤ ∑ p ∈ idx, ↑(N k) := by
        apply Finset.sum_le_sum; intro p hp; exact h_each_enat p hp
    _ = ↑(idx.card) * ↑(N k) := by
        rw [Finset.sum_const] <;> ring
    _ ≤ ↑(C.card * 9) * ↑(N k) := by
        gcongr <;> exact h_idx_card
    _ = ↑(C.card * 9 * N k) := by
        simp [mul_assoc] <;> ring
  have h_final : (Metric.externalCoveringNumber (Δ^(k+1)).toNNReal A : ENNReal) ≤
      (C.card : ENNReal) * 9 * (N k : ENNReal) := by
    have h1 : (Metric.externalCoveringNumber (Δ^(k+1)).toNNReal A : ENNReal) ≤ (↑(C.card * 9 * N k) : ENNReal) :=
      enat_to_ennreal_mono h_final_enat
    have h2 : (↑(C.card * 9 * N k) : ENNReal) = (C.card : ENNReal) * 9 * (N k : ENNReal) := by
      simp [mul_assoc] <;> ring
    rw [h2] at h1
    exact h1
  exact h_final

/-- Extract a finite cover from a finite upper bound on the external covering number. -/
lemma exists_finite_cover_le {X : Type*} [PseudoMetricSpace X] {ε : NNReal} {A : Set X} {M : ENNReal}
    (h : Metric.externalCoveringNumber ε A ≤ M) (hM : M ≠ ⊤) :
    ∃ (C : Finset X), Metric.IsCover ε A C ∧ (C.card : ENNReal) ≤ M := by
  have h_ne_top : Metric.externalCoveringNumber ε A ≠ ⊤ := by
    intro h10
    have h11 : M = ⊤ := by
      have h12 : (Metric.externalCoveringNumber ε A : ENNReal) = ⊤ := by
        simpa using h10
      rw [h12] at h
      simpa using h
    exact hM h11
  let S : Set (Set X) := {C | Metric.IsCover ε A C}
  have hS_nonempty : S.Nonempty := by
    refine ⟨Set.univ, ?_⟩
    dsimp only [S, Metric.IsCover]
    intro x _
    exact ⟨x, by simp, by simp [Metric.mem_closedBall]⟩
  letI : Nonempty {C : Set X // C ∈ S} := hS_nonempty.to_subtype
  let f : {C : Set X // C ∈ S} → ENat := fun C => C.val.encard
  have h_exists : ∃ (x : {C : Set X // C ∈ S}), f x = iInf f := ENat.exists_eq_iInf f
  rcases h_exists with ⟨C, hC⟩
  have hC_cover : Metric.IsCover ε A C.val := C.property
  have hC_eq : C.val.encard = Metric.externalCoveringNumber ε A := by
    have h_eq : iInf f = Metric.externalCoveringNumber ε A := by
      simp [f, S, Metric.externalCoveringNumber, iInf_subtype] <;> aesop
    rw [h_eq] at hC
    exact hC
  have hC_fin : C.val.Finite := by
    by_contra h
    have h' : C.val.encard = ⊤ := by
      rw [Set.encard_eq_top_iff]
      exact h
    have h'' : Metric.externalCoveringNumber ε A = ⊤ := by
      rw [←hC_eq]
      exact h'
    exact h_ne_top h''
  let C' : Finset X := hC_fin.toFinset
  have h1 : (C' : Set X) = C.val := by
    have h_coe : ↑(hC_fin.toFinset) = C.val := Set.Finite.coe_toFinset hC_fin
    exact h_coe
  refine ⟨C', ?_, ?_⟩
  · have hcover : Metric.IsCover ε A (C' : Set X) := by
      rw [h1]
      exact hC_cover
    exact hcover
  · have h2 : (C'.card : ENNReal) = C.val.encard := by
      have h3 : (C' : Set X) = C.val := h1
      rw [←h3] <;> simp
    rw [h2, hC_eq]
    exact h

/-- Coordinate bound in Euclidean plane: |x c - y c| ≤ dist x y. -/
lemma euclidean_coord_bound (x y : EuclideanPlane) (c : Fin 2) : |x c - y c| ≤ dist x y := by
  let z : EuclideanPlane := x - y
  have h1 : ‖z‖ ^ 2 = ∑ i : Fin 2, (z i)^2 := EuclideanSpace.real_norm_sq_eq z
  have h3 : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ (z i)^2 := fun i _ => sq_nonneg (z i)
  have h2 : (z c)^2 ≤ ‖z‖^2 := by
    rw [h1]
    exact Finset.single_le_sum h3 (Finset.mem_univ c)
  have h4 : |z c| ≤ ‖z‖ := by
    have h5 : (z c)^2 ≤ ‖z‖^2 := h2
    have h6 : |z c|^2 = (z c)^2 := by rw [sq_abs]
    have h7 : |z c|^2 ≤ ‖z‖^2 := by rw [h6] <;> exact h5
    exact le_of_sq_le_sq h7 (norm_nonneg z)
  have h7 : ‖z‖ = dist x y := by
    simp [dist_eq_norm, z]
  rw [h7] at h4
  exact h4

/-- 1D: an interval of length 2r ≤ L intersects at most 2 dyadic intervals of length L. -/
lemma one_d_interval_bound (L r : ℝ) (hL : 0 < L) (hle : r ≤ L / 2)
    (x p : ℝ) (h : |p - x| ≤ r) (i : ℤ)
    (hi : p ∈ Set.Ico (i * L) ((i + 1) * L)) :
    i ∈ (if x - r ≥ (⌊x / L⌋ : ℝ) * L
          then ({⌊x / L⌋, ⌊x / L⌋ + 1} : Finset ℤ)
          else ({⌊x / L⌋ - 1, ⌊x / L⌋} : Finset ℤ)) := by
  let q : ℤ := ⌊x / L⌋
  have hq1 : (q : ℝ) * L ≤ x := by
    have h1 : (q : ℝ) ≤ x / L := Int.floor_le (x / L)
    have h2 : (q : ℝ) * L ≤ (x / L) * L := by gcongr
    have h3 : (x / L) * L = x := by field_simp [hL.ne'] <;> ring
    rw [h3] at h2; exact h2
  have hq2 : x < (q + 1 : ℝ) * L := by
    have h1 : x / L < (q + 1 : ℝ) := Int.lt_floor_add_one (x / L)
    have h2 : x = (x / L) * L := by field_simp [hL.ne'] <;> ring
    rw [h2]; gcongr
  have h_left : x - r ≤ p := by linarith [abs_le.mp h]
  have h_right : p ≤ x + r := by linarith [abs_le.mp h]
  have hpi1 : (i : ℝ) * L ≤ p := hi.1
  have hpi2 : p < ((i + 1 : ℝ) * L) := hi.2
  have h_broad1 : i ≤ q + 1 := by
    have h1 : (i : ℝ) * L ≤ x + r := by linarith
    have h2 : (i : ℝ) ≤ x / L + r / L := by
      calc (i : ℝ) = ((i : ℝ) * L) / L := by field_simp [hL.ne'] <;> ring
        _ ≤ (x + r) / L := by gcongr
        _ = x / L + r / L := by ring
    have h3 : r / L ≤ 1 / 2 := by
      have h4 : r ≤ L / 2 := hle
      calc r / L ≤ (L / 2) / L := by gcongr
        _ = 1 / 2 := by field_simp [hL.ne'] <;> ring
    have h4 : x / L < (q + 1 : ℝ) := by
      have h5 : x < (q + 1 : ℝ) * L := hq2
      have h6 : x / L < ((q + 1 : ℝ) * L) / L := by gcongr
      have h7 : ((q + 1 : ℝ) * L) / L = (q + 1 : ℝ) := by field_simp [hL.ne'] <;> ring
      rw [h7] at h6; exact h6
    have h5 : (i : ℝ) < (q + 1 : ℝ) + 1 / 2 := by linarith
    have h6 : (i : ℝ) < (q + 2 : ℝ) := by linarith
    have h7 : i < q + 2 := by exact_mod_cast h6
    omega
  have h_broad2 : q - 1 ≤ i := by
    have h1 : x - r < ((i + 1 : ℝ) * L) := by linarith
    have h2 : x / L - r / L < (i + 1 : ℝ) := by
      calc x / L - r / L = (x - r) / L := by ring
        _ < (((i + 1 : ℝ) * L)) / L := by gcongr
        _ = (i + 1 : ℝ) := by field_simp [hL.ne'] <;> ring
    have h3 : (q : ℝ) ≤ x / L := by
      have h4 : (q : ℝ) * L ≤ x := hq1
      calc (q : ℝ) = ((q : ℝ) * L) / L := by field_simp [hL.ne'] <;> ring
        _ ≤ x / L := by gcongr
    have h4 : r / L ≤ 1 / 2 := by
      have h5 : r ≤ L / 2 := hle
      calc r / L ≤ (L / 2) / L := by gcongr
        _ = 1 / 2 := by field_simp [hL.ne'] <;> ring
    have h5 : (q - 1 : ℝ) < (i + 1 : ℝ) := by linarith
    have h6 : q - 1 < i + 1 := by exact_mod_cast h5
    omega
  split_ifs with hcase
  · have h10 : i ≠ q - 1 := by
      intro h11
      have h_i1 : i + 1 = q := by omega
      have h_eq : ((i + 1 : ℝ)) = (q : ℝ) := by exact_mod_cast h_i1
      have h12 : p < (q : ℝ) * L := by
        have h13 : p < ((i + 1 : ℝ) * L) := hi.2
        rw [h_eq] at h13
        exact h13
      linarith
    have h13 : i = q ∨ i = q + 1 := by omega
    rcases h13 with (h_i | h_i)
    · rw [h_i]; simp [Finset.mem_insert, Finset.mem_singleton, hcase] <;> tauto
    · rw [h_i]; simp [Finset.mem_insert, Finset.mem_singleton, hcase] <;> tauto
  · have h10 : i ≠ q + 1 := by
      intro h11
      have h_eq : (i : ℝ) = (q + 1 : ℝ) := by exact_mod_cast h11
      have h12 : p ≥ ((q + 1 : ℝ) * L) := by
        have h13 : (i : ℝ) * L ≤ p := hi.1
        rw [h_eq] at h13
        exact h13
      have h13 : x + r ≥ ((q + 1 : ℝ) * L) := by linarith
      have h14 : 2 * r > L := by linarith [hq1]
      have h15 : 2 * r ≤ L := by linarith [hle]
      linarith
    have h13 : i = q - 1 ∨ i = q := by omega
    rcases h13 with (h_i | h_i)
    · rw [h_i]; simp [Finset.mem_insert, Finset.mem_singleton, hcase] <;> tauto
    · rw [h_i]; simp [Finset.mem_insert, Finset.mem_singleton, hcase] <;> tauto

/-- A ball of radius r ≤ L/2 intersects at most 4 dyadic squares of side L in R². -/
lemma ball_dyadic_squares_bound_4 (L r : ℝ) (hL : 0 < L) (hr : 0 < r) (hle : r ≤ L / 2)
    (x : EuclideanPlane) :
    ∃ (S : Finset (ℤ × ℤ)),
      (∀ (i j : ℤ), (Metric.closedBall x r ∩ dyadicSquare L i j).Nonempty → (i, j) ∈ S) ∧
      S.card ≤ 4 := by
  let I0 : Finset ℤ :=
    if x 0 - r ≥ (⌊x 0 / L⌋ : ℝ) * L then
      ({⌊x 0 / L⌋, ⌊x 0 / L⌋ + 1} : Finset ℤ)
    else
      ({⌊x 0 / L⌋ - 1, ⌊x 0 / L⌋} : Finset ℤ)
  let I1 : Finset ℤ :=
    if x 1 - r ≥ (⌊x 1 / L⌋ : ℝ) * L then
      ({⌊x 1 / L⌋, ⌊x 1 / L⌋ + 1} : Finset ℤ)
    else
      ({⌊x 1 / L⌋ - 1, ⌊x 1 / L⌋} : Finset ℤ)
  let S : Finset (ℤ × ℤ) := I0 ×ˢ I1
  have hI02 : I0.card = 2 := by
    dsimp only [I0]; split_ifs <;> simp [Finset.mem_insert, Finset.mem_singleton] <;> omega
  have hI12 : I1.card = 2 := by
    dsimp only [I1]; split_ifs <;> simp [Finset.mem_insert, Finset.mem_singleton] <;> omega
  have hS_card : S.card ≤ 4 := by
    have h : S.card = I0.card * I1.card := Finset.card_product ..
    rw [h, hI02, hI12] <;> norm_num
  have h_main : ∀ (i j : ℤ), (Metric.closedBall x r ∩ dyadicSquare L i j).Nonempty → (i, j) ∈ S := by
    intro i j h
    rcases h with ⟨p, hp_ball, hp_square⟩
    have h_cb0 : |p 0 - x 0| ≤ r := by
      have h1 : |p 0 - x 0| ≤ dist p x := euclidean_coord_bound p x 0
      have h2 : dist p x ≤ r := hp_ball
      linarith
    have h_cb1 : |p 1 - x 1| ≤ r := by
      have h1 : |p 1 - x 1| ≤ dist p x := euclidean_coord_bound p x 1
      have h2 : dist p x ≤ r := hp_ball
      linarith
    have h_i_in : i ∈ I0 := one_d_interval_bound L r hL hle (x 0) (p 0) h_cb0 i hp_square.1
    have h_j_in : j ∈ I1 := one_d_interval_bound L r hL hle (x 1) (p 1) h_cb1 j hp_square.2
    exact Finset.mem_product.mpr ⟨h_i_in, h_j_in⟩
  exact ⟨S, h_main, hS_card⟩

/-- A square of side L can be covered by 4 balls of radius r when r ≥ L * Real.sqrt 2 / 4. -/
lemma four_balls_cover_square (L r : ℝ) (hL : 0 < L) (hr : 0 < r)
    (h : r ≥ L * Real.sqrt 2 / 4) (a b : ℤ) :
    ∃ (c : Finset EuclideanPlane), (dyadicSquare L a b) ⊆ ⋃ x ∈ c, Metric.closedBall x r ∧ c.card ≤ 4 := by
  let c1 : EuclideanPlane :=
    WithLp.toLp 2 fun k : Fin 2 =>
      if k = 0 then (a : ℝ) * L + L / 4 else (b : ℝ) * L + L / 4
  let c2 : EuclideanPlane :=
    WithLp.toLp 2 fun k : Fin 2 =>
      if k = 0 then (a : ℝ) * L + 3 * L / 4 else (b : ℝ) * L + L / 4
  let c3 : EuclideanPlane :=
    WithLp.toLp 2 fun k : Fin 2 =>
      if k = 0 then (a : ℝ) * L + L / 4 else (b : ℝ) * L + 3 * L / 4
  let c4 : EuclideanPlane :=
    WithLp.toLp 2 fun k : Fin 2 =>
      if k = 0 then (a : ℝ) * L + 3 * L / 4 else (b : ℝ) * L + 3 * L / 4
  let c : Finset EuclideanPlane := {c1, c2, c3, c4}
  have hc_card : c.card ≤ 4 := by
    simp [c] <;> exact Finset.card_le_four
  have hcover : dyadicSquare L a b ⊆ ⋃ x ∈ c, Metric.closedBall x r := by
    intro p hp
    have h0 : p 0 ∈ Set.Ico ((a : ℝ) * L) (((a : ℝ) + 1) * L) := hp.1
    have h1 : p 1 ∈ Set.Ico ((b : ℝ) * L) (((b : ℝ) + 1) * L) := hp.2
    set dx : ℝ := p 0 - (a : ℝ) * L with hdx_def
    set dy : ℝ := p 1 - (b : ℝ) * L with hdy_def
    have hdx1 : 0 ≤ dx := by linarith [h0.1]
    have hdx2 : dx < L := by linarith [h0.2]
    have hdy1 : 0 ≤ dy := by linarith [h1.1]
    have hdy2 : dy < L := by linarith [h1.2]
    set cx : ℝ := if dx ≤ L / 2 then L / 4 else 3 * L / 4 with hcx_def
    set cy : ℝ := if dy ≤ L / 2 then L / 4 else 3 * L / 4 with hcy_def
    set center' : EuclideanPlane :=
      WithLp.toLp 2 fun k : Fin 2 =>
        if k = 0 then (a : ℝ) * L + cx else (b : ℝ) * L + cy with hcenter'_def
    have hcenter_in : center' ∈ c := by
      simp [c, center', cx, cy] <;> split_ifs <;> tauto
    have hdx_cx : |dx - cx| ≤ L / 4 := by
      by_cases hcase : dx ≤ L / 2
      · have hcx_eq : cx = L / 4 := by
          rw [hcx_def, if_pos hcase]
        rw [hcx_eq]
        have h1 : -L / 4 ≤ dx - L / 4 := by linarith
        have h2 : dx - L / 4 ≤ L / 4 := by linarith
        rw [abs_le] <;> constructor <;> linarith
      · have hcx_eq : cx = 3 * L / 4 := by
          rw [hcx_def, if_neg hcase]
        rw [hcx_eq]
        have h1 : -L / 4 ≤ dx - 3 * L / 4 := by linarith
        have h2 : dx - 3 * L / 4 ≤ L / 4 := by linarith
        rw [abs_le] <;> constructor <;> linarith
    have hdy_cy : |dy - cy| ≤ L / 4 := by
      by_cases hcase : dy ≤ L / 2
      · have hcy_eq : cy = L / 4 := by
          rw [hcy_def, if_pos hcase]
        rw [hcy_eq]
        have h1 : -L / 4 ≤ dy - L / 4 := by linarith
        have h2 : dy - L / 4 ≤ L / 4 := by linarith
        rw [abs_le] <;> constructor <;> linarith
      · have hcy_eq : cy = 3 * L / 4 := by
          rw [hcy_def, if_neg hcase]
        rw [hcy_eq]
        have h1 : -L / 4 ≤ dy - 3 * L / 4 := by linarith
        have h2 : dy - 3 * L / 4 ≤ L / 4 := by linarith
        rw [abs_le] <;> constructor <;> linarith
    set y : EuclideanPlane := p - center' with hy_def
    have hy0 : y 0 = dx - cx := by
      simp [hy_def, hcenter'_def, hdx_def] <;> ring
    have hy1 : y 1 = dy - cy := by
      simp [hy_def, hcenter'_def, hdy_def] <;> ring
    have h4 : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := by
      have h5 : ‖y‖ ^ 2 = ∑ i : Fin 2, (y i) ^ 2 := EuclideanSpace.real_norm_sq_eq y
      rw [h5] <;> simp [Fin.sum_univ_two] <;> ring
    have h61 : |y 0| ≤ L / 4 := by rw [hy0] <;> exact hdx_cx
    have h62 : |y 1| ≤ L / 4 := by rw [hy1] <;> exact hdy_cy
    have h6 : (y 0) ^ 2 ≤ (L / 4) ^ 2 := by
      have h : (y 0) ^ 2 = |y 0| ^ 2 := by rw [sq_abs]
      rw [h]; gcongr
    have h8 : (y 1) ^ 2 ≤ (L / 4) ^ 2 := by
      have h : (y 1) ^ 2 = |y 1| ^ 2 := by rw [sq_abs]
      rw [h]; gcongr
    have h10 : ‖y‖ ^ 2 ≤ (L * Real.sqrt 2 / 4) ^ 2 := by
      rw [h4]
      have h11 : (L * Real.sqrt 2 / 4) ^ 2 = 2 * (L / 4) ^ 2 := by
        have h12 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        calc (L * Real.sqrt 2 / 4) ^ 2
          = L^2 * (Real.sqrt 2)^2 / 16 := by ring
        _ = L^2 * 2 / 16 := by rw [h12] <;> ring
        _ = 2 * (L / 4) ^ 2 := by ring
      rw [h11] <;> nlinarith
    have h_pos : 0 ≤ L * Real.sqrt 2 / 4 := by positivity
    have h13 : ‖y‖ ≤ L * Real.sqrt 2 / 4 := by
      exact le_of_sq_le_sq h10 h_pos
    have h14 : ‖y‖ ≤ r := by
      calc ‖y‖ ≤ L * Real.sqrt 2 / 4 := h13
        _ ≤ r := h
    have hdist : dist p center' ≤ r := by
      simpa [dist_eq_norm, hy_def] using h14
    exact Set.mem_iUnion₂.mpr ⟨center', hcenter_in, hdist⟩
  exact ⟨c, hcover, hc_card⟩

end MultiscaleDecomposition

end DirecretisedFurstenbergEstimate

end
