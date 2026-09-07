module

/-
# Piece 2: Local IsRealDeltaSet Transfer

Transfers the (δ,s,C)-set property from a grid set S to its rounding
preimage A_cells = Rδ⁻¹(S).

## Main result

`local_delta_set_transfer`: If S ⊆ δℤ is a (δ,s,C)-set, then
A_cells is a (δ,s,6*C)-set.

## Proof sketch

For any dyadic cube Q of side r:
1. Rδ(A_cells ∩ Q) ⊆ S ∩ Q⁺ where Q⁺ is Q enlarged by δ/2
2. Q⁺ is covered by 3 dyadic cubes of side r (Q_left, Q, Q_right)
3. Nδ(A_cells ∩ Q) ≤ 2·|S ∩ Q⁺| ≤ 2·Σ|S ∩ Q_i|
4. |S ∩ Q_i| = Nδ(S ∩ Q_i) ≤ C·Nδ(S)·r^s (δ-set property)
5. Nδ(A_cells) ≥ |S| = Nδ(S)
6. Thus Nδ(A_cells ∩ Q) ≤ 6·C·Nδ(A_cells)·r^s
-/

public import MyLeanRepo.RoundingWrapper
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.Energy.AverageProjectionEnergy
public import MyLeanRepo.MultiSetPR
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Metric Classical

namespace robust_projection_main

/-- For A ⊆ δℤ, each grid point lies in a distinct δ-dyadic cube, so
|A| ≤ Nδ(A). In fact Nδ(A) = |A|. -/
lemma grid_set_card_le_Ndelta {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA_grid : A ⊆ productLikeIntegerGrid δ) :
    ENat.toENNReal A.encard ≤ Nreal δ A := by
  choose n hn using fun (y : ℝ) (hy : y ∈ A) => hA_grid hy
  let n' : ℝ → ℤ := fun y => if h : y ∈ A then n y h else 0
  let f : ℝ → Set (EuclideanSpace ℝ (Fin 1)) := fun y =>
    dyadicCube δ (fun (_ : Fin 1) => n' y)
  let pt : ℝ → EuclideanSpace ℝ (Fin 1) := fun y =>
    (WithLp.equiv 2 _).symm (fun _ => y)
  have hpt_eval : ∀ (y : ℝ), (pt y) 0 = y := by
    intro y; simp [pt]
  have hn'_eq : ∀ (y : ℝ) (hy : y ∈ A), n' y = n y hy := by
    intro y hy; simp [n', hy]
  have h_y_eq : ∀ (y : ℝ) (hy : y ∈ A), y = δ * (n' y : ℝ) := by
    intro y hy; rw [hn'_eq y hy]; exact hn y hy

  have h_meets : ∀ y ∈ A, f y ∈ dyadicCubesMeeting δ (realLineCopy A) := by
    intro y hy
    have h1 : f y ∈ dyadicCubes 1 δ := by exact ⟨_, rfl⟩
    have h2 : (f y ∩ realLineCopy A).Nonempty := by
      use pt y
      constructor
      · intro i; fin_cases i
        have h_y : y = δ * (n' y : ℝ) := h_y_eq y hy
        have h_goal : y ∈ Set.Ico (δ * (n' y : ℝ)) (δ * ((n' y : ℝ) + 1)) := by
          have h_left : δ * (n' y : ℝ) ≤ y := le_of_eq h_y.symm
          have h_right : y < δ * ((n' y : ℝ) + 1) := by
            calc y = δ * (n' y : ℝ) := h_y
              _ < δ * ((n' y : ℝ) + 1) := mul_lt_mul_of_pos_left (by linarith) hδ
          exact ⟨h_left, h_right⟩
        simpa [pt, f] using h_goal
      · simp only [realLineCopy, Set.mem_setOf_eq]
        have h3 : (pt y) 0 ∈ A := by rw [hpt_eval y]; exact hy
        exact h3
    exact ⟨h1, h2⟩

  have h_cube_inj : ∀ (a b : ℤ),
      dyadicCube δ (fun (_ : Fin 1) => a) = dyadicCube δ (fun (_ : Fin 1) => b) → a = b := by
    intro a b h_eq
    let p : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 _).symm (fun _ => δ * (a : ℝ))
    have hp_eval : p 0 = δ * (a : ℝ) := by simp [p]
    have h3 : p ∈ dyadicCube δ (fun (_ : Fin 1) => a) := by
      intro i; fin_cases i
      have h_goal : δ * (a : ℝ) ∈ Set.Ico (δ * (a : ℝ)) (δ * ((a : ℝ) + 1)) := by
        exact ⟨le_refl _, mul_lt_mul_of_pos_left (by linarith) hδ⟩
      simpa [p, dyadicCube] using h_goal
    have h4 : p ∈ dyadicCube δ (fun (_ : Fin 1) => b) := by exact h_eq ▸ h3
    have h5 : p 0 ∈ Set.Ico (δ * (b : ℝ)) (δ * ((b : ℝ) + 1)) := h4 0
    have h6 : δ * (b : ℝ) ≤ p 0 := h5.1
    have h7 : p 0 < δ * ((b : ℝ) + 1) := h5.2
    rw [hp_eval] at h6 h7
    have h8 : (b : ℝ) ≤ (a : ℝ) := by
      have h_div : δ * (b : ℝ) / δ ≤ δ * (a : ℝ) / δ := by gcongr
      have h1 : δ * (b : ℝ) / δ = (b : ℝ) := by field_simp [hδ.ne'] <;> ring
      have h2 : δ * (a : ℝ) / δ = (a : ℝ) := by field_simp [hδ.ne'] <;> ring
      rw [h1, h2] at h_div
      exact h_div
    have h9 : (a : ℝ) < (b : ℝ) + 1 := by
      have h_div : δ * (a : ℝ) / δ < δ * ((b : ℝ) + 1) / δ := by gcongr
      have h1 : δ * (a : ℝ) / δ = (a : ℝ) := by field_simp [hδ.ne'] <;> ring
      have h2 : δ * ((b : ℝ) + 1) / δ = (b : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
      rw [h1, h2] at h_div
      exact h_div
    have h10 : ⌊(a : ℝ)⌋ = b := by
      rw [Int.floor_eq_iff]; exact ⟨h8, h9⟩
    have h11 : ⌊(a : ℝ)⌋ = a := by simp
    rw [h11] at h10; exact h10

  have h_inj : Set.InjOn f A := by
    intro y hy z hz h_eq
    have h_k_eq : n' y = n' z := h_cube_inj (n' y) (n' z) h_eq
    have h_yy : y = δ * (n' y : ℝ) := h_y_eq y hy
    have h_zz : z = δ * (n' z : ℝ) := h_y_eq z hz
    rw [h_yy, h_zz, h_k_eq]

  have h_image_subset : f '' A ⊆ dyadicCubesMeeting δ (realLineCopy A) := by
    intro Q hQ; rcases hQ with ⟨y, hy, rfl⟩; exact h_meets y hy
  have h_encard_eq : (f '' A).encard = A.encard := h_inj.encard_image
  have h_encard_le : (f '' A).encard ≤ (dyadicCubesMeeting δ (realLineCopy A)).encard :=
    Set.encard_mono h_image_subset
  have h_final : A.encard ≤ (dyadicCubesMeeting δ (realLineCopy A)).encard := by
    rw [←h_encard_eq]; exact h_encard_le
  have h_goal : ENat.toENNReal A.encard ≤
      ENat.toENNReal (dyadicCubesMeeting δ (realLineCopy A)).encard := by
    exact ENat.toENNReal_le.mpr h_final
  simpa [Nreal, dyadicCoveringNumber] using h_goal

/-- Rounding fixes grid points. -/
lemma roundToDeltaGrid_fixes_grid {δ : ℝ} (hδ : 0 < δ) {y : ℝ}
    (hy : y ∈ productLikeIntegerGrid δ) : roundToDeltaGrid δ y = y := by
  rcases hy with ⟨n, rfl⟩
  dsimp only [roundToDeltaGrid]
  have h7 : (δ * (n : ℝ)) / δ = (n : ℝ) := by field_simp [hδ.ne'] <;> ring
  rw [h7]
  have h8 : round (n : ℝ) = (n : ℤ) := by simp
  rw [h8] <;> norm_cast

/-- Enlarged interval Q⁺ is covered by 3 side-r intervals. -/
lemma enlarged_interval_cover {δ r : ℝ} (hδ : 0 < δ) (hδ_le_r : δ ≤ r) (k : ℤ) :
    Set.Ico (r * (k : ℝ) - δ / 2) (r * ((k : ℝ) + 1) + δ / 2) ⊆
      Set.Ico (r * ((k - 1 : ℤ) : ℝ)) (r * (k : ℝ)) ∪
      (Set.Ico (r * (k : ℝ)) (r * ((k : ℝ) + 1)) ∪
       Set.Ico (r * ((k + 1 : ℤ) : ℝ)) (r * ((k + 2 : ℤ) : ℝ))) := by
  intro x hx
  have hlo : r * (k : ℝ) - δ / 2 ≤ x := hx.1
  have hhi : x < r * ((k : ℝ) + 1) + δ / 2 := hx.2
  have hr_pos : 0 < r := by linarith
  have hδ2 : δ / 2 ≤ r / 2 := by linarith
  by_cases h1 : x < r * (k : ℝ)
  · -- x ∈ I_left
    have h_lo2 : r * ((k - 1 : ℤ) : ℝ) ≤ x := by
      simp [sub_mul] at hlo ⊢ <;> linarith
    exact Or.inl ⟨h_lo2, h1⟩
  · -- x ≥ r*k
    have h1' : r * (k : ℝ) ≤ x := by linarith
    by_cases h2 : x < r * ((k : ℝ) + 1)
    · -- x ∈ I_Q
      exact Or.inr (Or.inl ⟨h1', h2⟩)
    · -- x ∈ I_right
      have h_hi2 : x < r * ((k + 2 : ℤ) : ℝ) := by
        simp [add_mul] at hhi ⊢ <;> linarith
      have h_lo3 : r * ((k + 1 : ℤ) : ℝ) ≤ x := by
        have h_eq : r * ((k + 1 : ℤ) : ℝ) = r * ((k : ℝ) + 1) := by
          simp [add_assoc] <;> norm_cast
        rw [h_eq]
        linarith
      exact Or.inr (Or.inr ⟨h_lo3, h_hi2⟩)

/-- **Piece 2 main theorem**: Transfer IsRealDeltaSet from grid set S to
its rounding preimage A_cells = Rδ⁻¹(S).

If S ⊆ δℤ is a (δ,s,C)-set, then A_cells is a (δ,s,6*C)-set. -/
lemma local_delta_set_transfer {δ s C : ℝ} (hδ : 0 < δ)
    {S : Set ℝ} (hS_grid : S ⊆ productLikeIntegerGrid δ)
    (hS_delta : IsRealDeltaSet δ s C S) :
    IsRealDeltaSet δ s ((6 : ℝ) * C) (roundToDeltaGrid δ ⁻¹' S) := by
  let A_cells := (roundToDeltaGrid δ ⁻¹' S)
  rcases hS_delta with ⟨hS_bdd, hS_nonempty, _, hδ_scale, hδ_pos, hs_nonneg, hs_le_one, hC_pos, h_cover⟩

  -- S ⊆ A_cells
  have hS_sub_A : S ⊆ A_cells := by
    intro y hy
    have h6 : roundToDeltaGrid δ y = y := roundToDeltaGrid_fixes_grid hδ (hS_grid hy)
    have h7 : roundToDeltaGrid δ y ∈ S := by rw [h6]; exact hy
    exact h7

  -- Boundedness: if realLineCopy S bounded, then realLineCopy A_cells bounded
  have hA_bdd : Bornology.IsBounded (realLineCopy A_cells) := by
    rcases (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin 1))).mp hS_bdd
      with ⟨r, hR⟩
    have hR' : ∀ (q : EuclideanSpace ℝ (Fin 1)), q ∈ realLineCopy A_cells →
        dist q (0 : EuclideanSpace ℝ (Fin 1)) ≤ r + δ / 2 := by
      intro q hq
      have hq0 : q 0 ∈ A_cells := by simpa [realLineCopy] using hq
      have h1 : roundToDeltaGrid δ (q 0) ∈ S := by simpa [A_cells, Set.mem_preimage] using hq0
      let p : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 _).symm (fun _ => roundToDeltaGrid δ (q 0))
      have hp0 : p 0 = roundToDeltaGrid δ (q 0) := by simp [p]
      have hp_in : p ∈ realLineCopy S := by
        have h : p 0 ∈ S := by rw [hp0]; exact h1
        simpa [realLineCopy] using h
      have h2 : p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) r := hR hp_in
      have h2' : dist p 0 ≤ r := h2
      have h_dist1 : dist q p = |q 0 - p 0| := by
        simp [EuclideanSpace.dist_eq, p, Fin.sum_univ_one] <;> rfl
      have h3 : dist q p ≤ δ / 2 := by
        rw [h_dist1, hp0]
        exact abs_sub_roundToDeltaGrid hδ (q 0)
      have h4 : dist q 0 ≤ dist q p + dist p 0 := dist_triangle q p 0
      calc dist q 0 ≤ dist q p + dist p 0 := h4
        _ ≤ δ / 2 + r := by linarith
        _ = r + δ / 2 := by ring
    have h_sub : realLineCopy A_cells ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) (r + δ / 2) := by
      intro q hq
      exact hR' q hq
    exact (Metric.isBounded_iff_subset_closedBall _).mpr ⟨_, h_sub⟩

  -- Nonemptiness
  have hA_nonempty : (realLineCopy A_cells).Nonempty := by
    rcases hS_nonempty with ⟨p, hp⟩
    have h_y_in_S : p 0 ∈ S := by simpa [realLineCopy] using hp
    have h_y_in_A : p 0 ∈ A_cells := hS_sub_A h_y_in_S
    exact ⟨p, by simpa [realLineCopy] using h_y_in_A⟩

  -- Nδ(S) ≤ Nδ(A_cells)
  have hNS_le_NA : Nreal δ S ≤ Nreal δ A_cells := Nreal_mono_local hS_sub_A

  -- Main covering bound
  have hA_cover : ∀ (r : ℝ) (Q : Set (EuclideanSpace ℝ (Fin 1))),
      r ∈ dyadicScales → Q ∈ dyadicCubes 1 r → δ ≤ r → r ≤ 1 →
        ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A_cells ∩ Q)) ≤
          ENNReal.ofReal ((6 : ℝ) * C) *
            ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A_cells)) *
              ENNReal.ofReal (r ^ s) := by
    intro r Q hr_scale hQ hδ_le_r hr_le_one
    rcases hQ with ⟨k, rfl⟩
    let k0 : ℤ := k 0
    let I_Q : Set ℝ := Set.Ico (r * (k0 : ℝ)) (r * ((k0 : ℝ) + 1))
    let I_plus : Set ℝ := Set.Ico (r * (k0 : ℝ) - δ / 2) (r * ((k0 : ℝ) + 1) + δ / 2)
    let I_left : Set ℝ := Set.Ico (r * ((k0 - 1 : ℤ) : ℝ)) (r * (k0 : ℝ))
    let I_right : Set ℝ := Set.Ico (r * ((k0 + 1 : ℤ) : ℝ)) (r * ((k0 + 2 : ℤ) : ℝ))

    -- realLineCopy A_cells ∩ dyadicCube r k = realLineCopy (A_cells ∩ I_Q)
    have h_eq1 : realLineCopy A_cells ∩ dyadicCube r k = realLineCopy (A_cells ∩ I_Q) := by
      ext x
      simp [realLineCopy, dyadicCube, I_Q] <;> tauto

    -- A_cells ∩ I_Q ⊆ Rδ⁻¹(S ∩ I_plus)
    have h1 : A_cells ∩ I_Q ⊆ roundToDeltaGrid δ ⁻¹' (S ∩ I_plus) := by
      intro x hx
      have h3 : roundToDeltaGrid δ x ∈ S := by simpa [A_cells, Set.mem_preimage] using hx.1
      have h4 : |x - roundToDeltaGrid δ x| ≤ δ / 2 := abs_sub_roundToDeltaGrid hδ x
      have h5 : roundToDeltaGrid δ x ∈ I_plus := by
        rcases hx.2 with ⟨h21, h22⟩
        have h6 : |x - roundToDeltaGrid δ x| ≤ δ / 2 := h4
        have h7 : -(δ / 2) ≤ x - roundToDeltaGrid δ x := (abs_le.mp h6).1
        have h8 : x - roundToDeltaGrid δ x ≤ δ / 2 := (abs_le.mp h6).2
        simp only [I_plus, Set.mem_Ico]
        constructor <;> linarith
      exact ⟨h3, h5⟩

    -- I_plus ⊆ I_left ∪ (I_Q ∪ I_right)
    have h2 : I_plus ⊆ I_left ∪ (I_Q ∪ I_right) := enlarged_interval_cover hδ hδ_le_r k0

    -- Nδ(A_cells ∩ I_Q) ≤ 2 * |S ∩ I_plus|
    have h3 : Nreal δ (A_cells ∩ I_Q) ≤ 2 * ENat.toENNReal (S ∩ I_plus).encard := by
      have h31 : Nreal δ (A_cells ∩ I_Q) ≤ Nreal δ (roundToDeltaGrid δ ⁻¹' (S ∩ I_plus)) :=
        Nreal_mono_local h1
      have h32 : Nreal δ (roundToDeltaGrid δ ⁻¹' (S ∩ I_plus)) ≤ 2 * ENat.toENNReal (S ∩ I_plus).encard :=
        grid_preimage_covering_bound hδ (show (S ∩ I_plus) ⊆ productLikeIntegerGrid δ from
          fun x hx => hS_grid hx.1)
      exact le_trans h31 h32

    -- S ∩ I_plus ⊆ (S ∩ I_left) ∪ (S ∩ I_Q) ∪ (S ∩ I_right)
    have h41 : S ∩ I_plus ⊆ (S ∩ I_left) ∪ ((S ∩ I_Q) ∪ (S ∩ I_right)) := by
      intro x hx
      have h5 : x ∈ I_plus := hx.2
      have hS : x ∈ S := hx.1
      have h6 : x ∈ I_left ∪ (I_Q ∪ I_right) := h2 h5
      rcases h6 with (h6 | h6)
      · exact Or.inl ⟨hS, h6⟩
      · rcases h6 with (h6 | h6)
        · exact Or.inr (Or.inl ⟨hS, h6⟩)
        · exact Or.inr (Or.inr ⟨hS, h6⟩)

    -- |S ∩ I_plus| ≤ |S ∩ I_left| + |S ∩ I_Q| + |S ∩ I_right|
    have h4 : ENat.toENNReal (S ∩ I_plus).encard ≤
        ENat.toENNReal (S ∩ I_left).encard +
        ENat.toENNReal (S ∩ I_Q).encard +
        ENat.toENNReal (S ∩ I_right).encard := by
      have h42 : (S ∩ I_plus).encard ≤ ((S ∩ I_left) ∪ ((S ∩ I_Q) ∪ (S ∩ I_right))).encard :=
        Set.encard_mono h41
      have h43 : ((S ∩ I_left) ∪ ((S ∩ I_Q) ∪ (S ∩ I_right))).encard ≤
          (S ∩ I_left).encard + ((S ∩ I_Q) ∪ (S ∩ I_right)).encard := Set.encard_union_le _ _
      have h44 : ((S ∩ I_Q) ∪ (S ∩ I_right)).encard ≤
          (S ∩ I_Q).encard + (S ∩ I_right).encard := Set.encard_union_le _ _
      have h45 : ((S ∩ I_left) ∪ ((S ∩ I_Q) ∪ (S ∩ I_right))).encard ≤
          (S ∩ I_left).encard + (S ∩ I_Q).encard + (S ∩ I_right).encard := by
        calc _ ≤ (S ∩ I_left).encard + ((S ∩ I_Q) ∪ (S ∩ I_right)).encard := h43
          _ ≤ (S ∩ I_left).encard + ((S ∩ I_Q).encard + (S ∩ I_right).encard) := by gcongr
          _ = (S ∩ I_left).encard + (S ∩ I_Q).encard + (S ∩ I_right).encard := by ring
      exact_mod_cast le_trans h42 h45

    -- Helper: for a given interval I_i and cube Q_i, |S ∩ I_i| ≤ C * Nδ(S) * r^s
    let X := ENNReal.ofReal C * Nreal δ S * ENNReal.ofReal (r ^ s)
    have h_bound : ∀ (I_i : Set ℝ) (Q_i : Set (EuclideanSpace ℝ (Fin 1))),
        Q_i ∈ dyadicCubes 1 r →
          realLineCopy S ∩ Q_i = realLineCopy (S ∩ I_i) →
          ENat.toENNReal (S ∩ I_i).encard ≤ X := by
      intro I_i Q_i hQi h_eq
      have h51 : Nreal δ (S ∩ I_i) ≤ X := by
        have h := h_cover hr_scale hQi hδ_le_r hr_le_one
        rw [h_eq] at h
        exact h
      have h52 : S ∩ I_i ⊆ productLikeIntegerGrid δ := by
        intro x hx; exact hS_grid hx.1
      have h53 : ENat.toENNReal (S ∩ I_i).encard ≤ Nreal δ (S ∩ I_i) :=
        grid_set_card_le_Ndelta hδ h52
      exact le_trans h53 h51

    let Q_left := dyadicCube r (fun (_ : Fin 1) => k0 - 1)
    let Q_right := dyadicCube r (fun (_ : Fin 1) => k0 + 1)

    -- General equality lemma
    have h_eq_general : ∀ (n : ℤ), realLineCopy S ∩ dyadicCube r (fun (_ : Fin 1) => n) =
        realLineCopy (S ∩ Set.Ico (r * (n : ℝ)) (r * ((n : ℝ) + 1))) := by
      intro n
      ext y
      simp [realLineCopy, dyadicCube, Set.mem_inter_iff]
      <;> rfl

    -- Interval equalities (coercion simplification)
    have h_I_left_eq : I_left = Set.Ico (r * ((k0 - 1 : ℤ) : ℝ)) (r * (((k0 - 1 : ℤ) : ℝ) + 1)) := by
      congr 1 <;> simp [sub_add] <;> norm_cast <;> ring
    have h_I_Q_eq : I_Q = Set.Ico (r * (k0 : ℝ)) (r * ((k0 : ℝ) + 1)) := by rfl
    have h_I_right_eq : I_right = Set.Ico (r * ((k0 + 1 : ℤ) : ℝ)) (r * (((k0 + 1 : ℤ) : ℝ) + 1)) := by
      congr 1 <;> simp [add_assoc] <;> norm_cast <;> ring

    have h_eq_left : realLineCopy S ∩ Q_left = realLineCopy (S ∩ I_left) := by
      rw [h_I_left_eq]
      exact h_eq_general (k0 - 1)
    have h_k_eq : k = (fun (_ : Fin 1) => k0) := by
      funext i; fin_cases i <;> rfl
    have h_eq_Q : realLineCopy S ∩ dyadicCube r k = realLineCopy (S ∩ I_Q) := by
      rw [h_k_eq, h_I_Q_eq]
      exact h_eq_general k0
    have h_eq_right : realLineCopy S ∩ Q_right = realLineCopy (S ∩ I_right) := by
      rw [h_I_right_eq]
      exact h_eq_general (k0 + 1)

    have h5_left : ENat.toENNReal (S ∩ I_left).encard ≤ X :=
      h_bound I_left Q_left ⟨_, rfl⟩ h_eq_left
    have h5_Q : ENat.toENNReal (S ∩ I_Q).encard ≤ X :=
      h_bound I_Q (dyadicCube r k) ⟨_, rfl⟩ h_eq_Q
    have h5_right : ENat.toENNReal (S ∩ I_right).encard ≤ X :=
      h_bound I_right Q_right ⟨_, rfl⟩ h_eq_right

    have h5_sum : ENat.toENNReal (S ∩ I_left).encard +
        ENat.toENNReal (S ∩ I_Q).encard +
        ENat.toENNReal (S ∩ I_right).encard ≤ 3 * X := by
      calc _ ≤ X + X + X := by gcongr <;> tauto
        _ = 3 * X := by ring

    have h6 : Nreal δ (A_cells ∩ I_Q) ≤ 2 * (3 * X) := by
      calc Nreal δ (A_cells ∩ I_Q)
        ≤ 2 * ENat.toENNReal (S ∩ I_plus).encard := h3
      _ ≤ 2 * (ENat.toENNReal (S ∩ I_left).encard +
              ENat.toENNReal (S ∩ I_Q).encard +
              ENat.toENNReal (S ∩ I_right).encard) := by gcongr
      _ ≤ 2 * (3 * X) := by gcongr

    have h7 : 2 * (3 * X) ≤ ENNReal.ofReal ((6 : ℝ) * C) * Nreal δ A_cells * ENNReal.ofReal (r ^ s) := by
      have h8 : 2 * (3 * X) = 6 * X := by ring
      rw [h8]
      have h9 : 6 * X = ENNReal.ofReal ((6 : ℝ) * C) * Nreal δ S * ENNReal.ofReal (r ^ s) := by
        simp only [X]
        have h10 : (6 : ENNReal) = ENNReal.ofReal (6 : ℝ) := by norm_cast
        rw [h10]
        have h11 : ENNReal.ofReal (6 : ℝ) * (ENNReal.ofReal C * Nreal δ S * ENNReal.ofReal (r ^ s)) =
            (ENNReal.ofReal (6 : ℝ) * ENNReal.ofReal C) * Nreal δ S * ENNReal.ofReal (r ^ s) := by ring
        rw [h11]
        have h12 : ENNReal.ofReal (6 : ℝ) * ENNReal.ofReal C = ENNReal.ofReal ((6 : ℝ) * C) := by
          rw [← ENNReal.ofReal_mul] <;> norm_num
        rw [h12] <;> ring
      rw [h9]
      gcongr
      <;> exact hNS_le_NA

    rw [h_eq1]
    have h_final : Nreal δ (A_cells ∩ I_Q) ≤ ENNReal.ofReal ((6 : ℝ) * C) * Nreal δ A_cells * ENNReal.ofReal (r ^ s) :=
      le_trans h6 h7
    simpa [Nreal, dyadicCoveringNumber] using h_final

  exact ⟨hA_bdd, hA_nonempty, by norm_num, hδ_scale, hδ_pos, hs_nonneg, hs_le_one, by positivity, hA_cover⟩

end robust_projection_main
