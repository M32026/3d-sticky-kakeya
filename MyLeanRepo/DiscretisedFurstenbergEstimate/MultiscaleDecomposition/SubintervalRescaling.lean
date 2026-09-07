module

/-
  Generalized rescaling lemma for uniform sets.

  Given a uniform set P and a dyadic square at scale Δ^a, the rescaled set
  is uniform with shifted parameters.

  Whiteprint node: multiscale_decomp
  Dependencies: LinearToRegular, SquareCorrespondence, SquareContainment, CoveringNumberEquality
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.LinearToRegular
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.SquareCorrespondence
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.SquareContainment
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.CoveringNumberEquality
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section


noncomputable section

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MultiscaleDecomposition

namespace DirecretisedFurstenbergEstimate.MultiscaleDecomposition

/-- Generalization of `uniform_rescaled_one_square` to arbitrary starting scale `a`.

If `P` is `(m, Δ, N)`-uniform and `Q` is a nonempty dyadic `Δ^a`-square,
then the rescaled set `homothetyS (Δ^a) i j '' (P ∩ Q)` is
`(b-a, Δ, N')`-uniform where `N' k = N (a + k)`. -/
lemma uniform_rescaled_square
    {P : Set EuclideanPlane} {m a b : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsUniform P m Δ N)
    (ha : a < b) (hab : b ≤ m)
    {n : ℕ} (hn_pos : 0 < n)
    (h1 : (1 : ℝ) = (n : ℝ) * Δ)
    (i j : ℤ) (hQ : (P ∩ dyadicSquare (Δ ^ a) i j).Nonempty) :
    IsUniform (homothetyS (Δ ^ a) i j '' (P ∩ dyadicSquare (Δ ^ a) i j))
      (b - a) Δ (fun k => N (a + k)) := by
  let v : EuclideanPlane :=
    WithLp.toLp (2 : ENNReal) (fun k : Fin 2 =>
      if k = 0 then (i : ℝ) * (Δ ^ a) else (j : ℝ) * (Δ ^ a))
  let L : ℝ := 1 / (Δ ^ a)
  let τ : EuclideanPlane → EuclideanPlane := fun x => L • (x - v)
  let τ_inv : EuclideanPlane → EuclideanPlane := fun y => (Δ ^ a : ℝ) • y + v
  have hΔ_pos : 0 < Δ := h_uniform.1
  have hΔ1 : Δ < 1 := h_uniform.2.1
  have hΔa_pos : 0 < Δ ^ a := by positivity
  have hL_pos : 0 < L := by positivity
  have hL_Da : L * (Δ ^ a) = 1 := by
    dsimp only [L]
    field_simp [hΔa_pos.ne'] <;> ring
  have hτ_eq : homothetyS (Δ ^ a) i j = τ := by
    funext x
    simp [homothetyS, τ, v]
    <;> ext k <;> fin_cases k <;> simp [L] <;> ring
  have hτ_inv1 : ∀ x, τ_inv (τ x) = x := by
    intro x
    have h : τ_inv (τ x) = (Δ ^ a : ℝ) • (L • (x - v)) + v := by
      rfl
    rw [h]
    have h2 : (Δ ^ a : ℝ) • (L • (x - v)) = ((Δ ^ a : ℝ) * L) • (x - v) := by
      rw [smul_smul]
    rw [h2]
    have h3 : (Δ ^ a : ℝ) * L = 1 := by
      rw [mul_comm] <;> exact hL_Da
    rw [h3]
    simp
    <;> abel
  have h_inj : Function.Injective τ := by
    intro x y h
    have h' : τ_inv (τ x) = τ_inv (τ y) := by rw [h]
    simpa [hτ_inv1] using h'
  have h_lip : LipschitzWith L.toNNReal τ := by
    refine' LipschitzWith.of_dist_le_mul _
    intro x y
    have h_sub : τ x - τ y = L • (x - y) := by
      simp [τ, smul_sub] <;> abel
    have h : dist (τ x) (τ y) = ‖L • (x - y)‖ := by
      rw [dist_eq_norm, h_sub]
    rw [h, norm_smul]
    have h_abs : ‖L‖ = L := by
      simp [Real.norm_eq_abs, abs_of_pos hL_pos]
    rw [h_abs]
    have h_coe : (L.toNNReal : ℝ) = L := by simp [hL_pos.le]
    rw [h_coe]
    <;> simp [dist_eq_norm]
  have h_lip_inv : LipschitzWith ((Δ ^ a).toNNReal) τ_inv := by
    refine' LipschitzWith.of_dist_le_mul _
    intro x y
    have h_sub : τ_inv x - τ_inv y = (Δ ^ a : ℝ) • (x - y) := by
      simp [τ_inv, smul_sub] <;> abel
    have h : dist (τ_inv x) (τ_inv y) = ‖(Δ ^ a : ℝ) • (x - y)‖ := by
      rw [dist_eq_norm, h_sub]
    rw [h, norm_smul]
    have h_abs : ‖(Δ ^ a : ℝ)‖ = Δ ^ a := by
      rw [Real.norm_eq_abs, abs_of_pos hΔa_pos]
    rw [h_abs]
    have h_coe : (((Δ ^ a).toNNReal : ℝ)) = Δ ^ a := by simp [hΔa_pos.le]
    rw [h_coe]
    <;> simp [dist_eq_norm]
  let Q := dyadicSquare (Δ ^ a) i j
  let P' := homothetyS (Δ ^ a) i j '' (P ∩ Q)
  have hP'_eq : P' = τ '' (P ∩ Q) := by
    congr <;> exact hτ_eq
  have hP'_nonempty : P'.Nonempty := by
    rcases hQ with ⟨x, hxP, hxQ⟩
    exact ⟨homothetyS (Δ ^ a) i j x, ⟨x, ⟨hxP, hxQ⟩, rfl⟩⟩
  have hN_pos : ∀ k < b - a, N (a + k) ≥ 1 := by
    intro k hk
    have h2 : a + k < m := by omega
    exact h_uniform.2.2.2.1 (a + k) h2
  refine' ⟨hΔ_pos, hΔ1, hP'_nonempty, hN_pos, _⟩
  intro k hk a' b' hR'
  let R' := dyadicSquare (Δ ^ k) a' b'
  have hR'_nonempty : (P' ∩ R').Nonempty := hR'
  rcases hR'_nonempty with ⟨y, hyP', hyR'⟩
  rcases hyP' with ⟨x, hxPQ, rfl⟩
  have hxQ : x ∈ Q := hxPQ.2
  have hxP : x ∈ P := hxPQ.1
  let c : ℤ := i * (n ^ k) + a'
  let d : ℤ := j * (n ^ k) + b'
  let R := dyadicSquare (Δ ^ (a + k)) c d
  have h_x_in_R : x ∈ R := by
    have h_sq_img := rescaled_square_image (a := a) (k := k) hn_pos h1 i j a' b'
    have h_τx_in_R' : τ x ∈ R' := hyR'
    have h : τ x ∈ τ '' R := by
      rw [h_sq_img]
      exact h_τx_in_R'
    rcases h with ⟨w, hwR, h_eq⟩
    have h_weq : w = x := h_inj h_eq
    rw [h_weq] at hwR
    exact hwR
  have hR_nonempty : (P ∩ R).Nonempty := ⟨x, hxP, h_x_in_R⟩
  have h_contain : R ⊆ Q := by
    by_cases h_k : k = 0
    · -- k = 0 case: R and Q are at same scale, must be equal
      subst h_k
      have hc : c = i := by
        have h_lt1 : (c : ℝ) * Δ ^ a < (i + 1 : ℝ) * Δ ^ a := by
          have h : (c : ℝ) * Δ ^ a ≤ x 0 := h_x_in_R.1.1
          have h2 : x 0 < (i + 1 : ℝ) * Δ ^ a := hxQ.1.2
          linarith
        have h_lt2 : (i : ℝ) * Δ ^ a < (c + 1 : ℝ) * Δ ^ a := by
          have h : (i : ℝ) * Δ ^ a ≤ x 0 := hxQ.1.1
          have h2 : x 0 < (c + 1 : ℝ) * Δ ^ a := h_x_in_R.1.2
          linarith
        have h_pos : 0 < Δ ^ a := hΔa_pos
        have h1 : (c : ℝ) < (i + 1 : ℝ) := by
          calc (c : ℝ)
            = ((c : ℝ) * Δ ^ a) / (Δ ^ a) := by field_simp [h_pos.ne'] <;> ring
          _ < (((i + 1 : ℝ) * Δ ^ a) / (Δ ^ a)) := by gcongr
          _ = (i + 1 : ℝ) := by field_simp [h_pos.ne'] <;> ring
        have h2 : (i : ℝ) < (c + 1 : ℝ) := by
          calc (i : ℝ)
            = ((i : ℝ) * Δ ^ a) / (Δ ^ a) := by field_simp [h_pos.ne'] <;> ring
          _ < (((c + 1 : ℝ) * Δ ^ a) / (Δ ^ a)) := by gcongr
          _ = (c + 1 : ℝ) := by field_simp [h_pos.ne'] <;> ring
        have h1' : c < i + 1 := by exact_mod_cast h1
        have h2' : i < c + 1 := by exact_mod_cast h2
        omega
      have hd : d = j := by
        have h_lt1 : (d : ℝ) * Δ ^ a < (j + 1 : ℝ) * Δ ^ a := by
          have h : (d : ℝ) * Δ ^ a ≤ x 1 := h_x_in_R.2.1
          have h2 : x 1 < (j + 1 : ℝ) * Δ ^ a := hxQ.2.2
          linarith
        have h_lt2 : (j : ℝ) * Δ ^ a < (d + 1 : ℝ) * Δ ^ a := by
          have h : (j : ℝ) * Δ ^ a ≤ x 1 := hxQ.2.1
          have h2 : x 1 < (d + 1 : ℝ) * Δ ^ a := h_x_in_R.2.2
          linarith
        have h_pos : 0 < Δ ^ a := hΔa_pos
        have h1 : (d : ℝ) < (j + 1 : ℝ) := by
          calc (d : ℝ)
            = ((d : ℝ) * Δ ^ a) / (Δ ^ a) := by field_simp [h_pos.ne'] <;> ring
          _ < (((j + 1 : ℝ) * Δ ^ a) / (Δ ^ a)) := by gcongr
          _ = (j + 1 : ℝ) := by field_simp [h_pos.ne'] <;> ring
        have h2 : (j : ℝ) < (d + 1 : ℝ) := by
          calc (j : ℝ)
            = ((j : ℝ) * Δ ^ a) / (Δ ^ a) := by field_simp [h_pos.ne'] <;> ring
          _ < (((d + 1 : ℝ) * Δ ^ a) / (Δ ^ a)) := by gcongr
          _ = (d + 1 : ℝ) := by field_simp [h_pos.ne'] <;> ring
        have h1' : d < j + 1 := by exact_mod_cast h1
        have h2' : j < d + 1 := by exact_mod_cast h2
        omega
      intro z hz
      simp only [R, dyadicSquare] at hz
      have h5 : Δ ^ (a + 0) = Δ ^ a := by simp
      rw [h5] at hz
      have h6' : z 0 ∈ Set.Ico ((i : ℝ) * Δ ^ a) ((i + 1 : ℝ) * Δ ^ a) := by
        simpa [hc] using hz.1
      have h7' : z 1 ∈ Set.Ico ((j : ℝ) * Δ ^ a) ((j + 1 : ℝ) * Δ ^ a) := by
        simpa [hd] using hz.2
      simp only [Q, dyadicSquare]
      exact ⟨h6', h7'⟩
    · -- k > 0 case: use dyadic_square_containment lemma
      have h_k_pos : 0 < k := Nat.pos_of_ne_zero h_k
      have h_int1 : Set.Nonempty (Set.Ico ((c : ℝ) * Δ ^ (a + k)) ((c + 1 : ℝ) * Δ ^ (a + k)) ∩
          Set.Ico ((i : ℝ) * (Δ ^ a)) (((i + 1 : ℝ) * (Δ ^ a)))) :=
        ⟨x 0, h_x_in_R.1, hxQ.1⟩
      have h_int2 : Set.Nonempty (Set.Ico ((d : ℝ) * Δ ^ (a + k)) ((d + 1 : ℝ) * Δ ^ (a + k)) ∩
          Set.Ico ((j : ℝ) * (Δ ^ a)) (((j + 1 : ℝ) * (Δ ^ a)))) :=
        ⟨x 1, h_x_in_R.2, hxQ.2⟩
      exact dyadic_square_containment hn_pos h1 i j c d h_k_pos h_int1 h_int2
  have h_sq_img : τ '' R = R' := rescaled_square_image (a := a) (k := k) hn_pos h1 i j a' b'
  have h_R_inter_Q : R ∩ Q = R := by
    exact Set.inter_eq_left.mpr h_contain
  have h_set_eq : P' ∩ R' = τ '' (P ∩ R) := by
    have h1 : P' ∩ R' = (τ '' (P ∩ Q)) ∩ (τ '' R) := by
      rw [hP'_eq, h_sq_img]
    rw [h1]
    have h21 : τ '' (P ∩ Q) = (τ '' P) ∩ (τ '' Q) := by
      rw [Set.image_inter h_inj]
    have h22 : τ '' ((P ∩ Q) ∩ R) = (τ '' (P ∩ Q)) ∩ (τ '' R) := by
      rw [Set.image_inter h_inj]
    have h2 : (τ '' (P ∩ Q)) ∩ (τ '' R) = τ '' ((P ∩ Q) ∩ R) := by
      rw [←h22]
    rw [h2]
    have h3 : (P ∩ Q) ∩ R = P ∩ R := by
      ext z
      simp [h_R_inter_Q]
      <;> tauto
    rw [h3]
  let ε : NNReal := (Δ ^ (a + k + 1)).toNNReal
  have hε_pos : 0 < Δ ^ (a + k + 1) := by positivity
  have hε_eq : (ε : ℝ) = Δ ^ (a + k + 1) := by
    simp [ε, hε_pos.le] <;> linarith
  have h_scale_eq : (Δ ^ (k + 1) : ℝ) = L * (Δ ^ (a + k + 1) : ℝ) := by
    dsimp only [L]
    rw [pow_add]
    field_simp [hΔa_pos.ne'] <;> ring
  have h_nnreal_eq : (Δ ^ (k + 1)).toNNReal = L.toNNReal * ε := by
    apply NNReal.eq
    have h_left : (((Δ ^ (k + 1)).toNNReal : ℝ)) = Δ ^ (k + 1) := by
      have h_pos : 0 < Δ ^ (k + 1) := by positivity
      simp [h_pos.le]
    have h_right : ((L.toNNReal * ε : NNReal) : ℝ) = (L.toNNReal : ℝ) * (ε : ℝ) := by
      rw [NNReal.coe_mul]
    rw [h_left, h_right]
    have h_coe_L : (L.toNNReal : ℝ) = L := by simp [hL_pos.le]
    rw [h_coe_L, hε_eq]
    exact h_scale_eq
  have h_cover_eq : Metric.externalCoveringNumber (L.toNNReal * ε) (τ '' (P ∩ R)) =
      Metric.externalCoveringNumber ε (P ∩ R) :=
    covering_number_equality
      (hL_pos := hL_pos) (hDa_pos := hΔa_pos) (hL_Da := hL_Da)
      (h_lip := h_lip) (h_lip_inv := h_lip_inv)
      (h_left_inv := hτ_inv1) (ε := ε)
  have h_main : (Metric.externalCoveringNumber (Δ ^ (k + 1)).toNNReal (P' ∩ R') : ENNReal) =
      (Metric.externalCoveringNumber (Δ ^ (a + k + 1)).toNNReal (P ∩ R) : ENNReal) := by
    have h4 : P' ∩ R' = τ '' (P ∩ R) := h_set_eq
    rw [h4, h_nnreal_eq]
    have h5 : (ε : NNReal) = (Δ ^ (a + k + 1)).toNNReal := by
      rfl
    rw [h5]
    exact_mod_cast h_cover_eq
  rw [h_main]
  have h2 : a + k < m := by omega
  exact h_uniform.2.2.2.2 (a + k) h2 c d hR_nonempty

/-- Dyadic version: if `P` is dyadic-uniform and `Q` is a nonempty dyadic `Δ^a`-square,
    then the rescaled set is dyadic-uniform with shifted parameters. -/
lemma uniform_rescaled_square_dyadic
    {P : Set EuclideanPlane} {m a b : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N)
    (ha : a < b) (hab : b ≤ m)
    {n : ℕ} (hn_pos : 0 < n)
    (h1 : (1 : ℝ) = (n : ℝ) * Δ)
    (i j : ℤ) (hQ : (P ∩ dyadicSquare (Δ ^ a) i j).Nonempty) :
    IsDyadicUniform (homothetyS (Δ ^ a) i j '' (P ∩ dyadicSquare (Δ ^ a) i j))
      (b - a) Δ (fun k => N (a + k)) := by
  let v : EuclideanPlane :=
    WithLp.toLp (2 : ENNReal) (fun k : Fin 2 =>
      if k = 0 then (i : ℝ) * (Δ ^ a) else (j : ℝ) * (Δ ^ a))
  let L : ℝ := 1 / (Δ ^ a)
  let τ : EuclideanPlane → EuclideanPlane := fun x => L • (x - v)
  let τ_inv : EuclideanPlane → EuclideanPlane := fun y => (Δ ^ a : ℝ) • y + v
  have hΔ_pos : 0 < Δ := h_uniform.1
  have hΔ1 : Δ < 1 := h_uniform.2.1
  have hΔa_pos : 0 < Δ ^ a := by positivity
  have hL_pos : 0 < L := by positivity
  have hL_Da : L * (Δ ^ a) = 1 := by
    dsimp only [L]
    field_simp [hΔa_pos.ne'] <;> ring
  have hτ_eq : homothetyS (Δ ^ a) i j = τ := by
    funext x
    simp [homothetyS, τ, v]
    <;> ext k <;> fin_cases k <;> simp [L] <;> ring
  have hτ_inv1 : ∀ x, τ_inv (τ x) = x := by
    intro x
    have h : τ_inv (τ x) = (Δ ^ a : ℝ) • (L • (x - v)) + v := by rfl
    rw [h]
    have h2 : (Δ ^ a : ℝ) • (L • (x - v)) = ((Δ ^ a : ℝ) * L) • (x - v) := by rw [smul_smul]
    rw [h2]
    have h3 : (Δ ^ a : ℝ) * L = 1 := by rw [mul_comm] <;> exact hL_Da
    rw [h3] <;> simp <;> abel
  have h_inj : Function.Injective τ := by
    intro x y h
    have h' : τ_inv (τ x) = τ_inv (τ y) := by rw [h]
    simpa [hτ_inv1] using h'
  let Q := dyadicSquare (Δ ^ a) i j
  let P' := homothetyS (Δ ^ a) i j '' (P ∩ Q)
  have hP'_eq : P' = τ '' (P ∩ Q) := by
    congr <;> exact hτ_eq
  have hP'_nonempty : P'.Nonempty := by
    rcases hQ with ⟨x, hxP, hxQ⟩
    exact ⟨homothetyS (Δ ^ a) i j x, ⟨x, ⟨hxP, hxQ⟩, rfl⟩⟩
  have hN_pos : ∀ k < b - a, N (a + k) ≥ 1 := by
    intro k hk
    have h2 : a + k < m := by omega
    exact h_uniform.2.2.2.1 (a + k) h2
  refine' ⟨hΔ_pos, hΔ1, hP'_nonempty, hN_pos, _⟩
  intro k hk a' b' hR'
  let R' := dyadicSquare (Δ ^ k) a' b'
  have hR'_nonempty : (P' ∩ R').Nonempty := hR'
  rcases hR'_nonempty with ⟨y, hyP', hyR'⟩
  rcases hyP' with ⟨x, hxPQ, rfl⟩
  have hxQ : x ∈ Q := hxPQ.2
  have hxP : x ∈ P := hxPQ.1
  let c : ℤ := i * (n ^ k) + a'
  let d : ℤ := j * (n ^ k) + b'
  let R := dyadicSquare (Δ ^ (a + k)) c d
  have h_x_in_R : x ∈ R := by
    have h_sq_img := rescaled_square_image (a := a) (k := k) hn_pos h1 i j a' b'
    have h_τx_in_R' : τ x ∈ R' := hyR'
    have h : τ x ∈ τ '' R := by rw [h_sq_img]; exact h_τx_in_R'
    rcases h with ⟨w, hwR, h_eq⟩
    have h_weq : w = x := h_inj h_eq
    rw [h_weq] at hwR
    exact hwR
  have hR_nonempty : (P ∩ R).Nonempty := ⟨x, hxP, h_x_in_R⟩
  have h_contain : R ⊆ Q := by
    by_cases h_k : k = 0
    · subst h_k
      have hc : c = i := by
        have h_lt1 : (c : ℝ) * Δ ^ a < (i + 1 : ℝ) * Δ ^ a := by
          have h : (c : ℝ) * Δ ^ a ≤ x 0 := h_x_in_R.1.1
          have h2 : x 0 < (i + 1 : ℝ) * Δ ^ a := hxQ.1.2
          linarith
        have h_lt2 : (i : ℝ) * Δ ^ a < (c + 1 : ℝ) * Δ ^ a := by
          have h : (i : ℝ) * Δ ^ a ≤ x 0 := hxQ.1.1
          have h2 : x 0 < (c + 1 : ℝ) * Δ ^ a := h_x_in_R.1.2
          linarith
        have h_pos : 0 < Δ ^ a := hΔa_pos
        have h1 : (c : ℝ) < (i + 1 : ℝ) := by
          calc (c : ℝ) = ((c : ℝ) * Δ ^ a) / (Δ ^ a) := by field_simp [h_pos.ne'] <;> ring
            _ < (((i + 1 : ℝ) * Δ ^ a) / (Δ ^ a)) := by gcongr
            _ = (i + 1 : ℝ) := by field_simp [h_pos.ne'] <;> ring
        have h2 : (i : ℝ) < (c + 1 : ℝ) := by
          calc (i : ℝ) = ((i : ℝ) * Δ ^ a) / (Δ ^ a) := by field_simp [h_pos.ne'] <;> ring
            _ < (((c + 1 : ℝ) * Δ ^ a) / (Δ ^ a)) := by gcongr
            _ = (c + 1 : ℝ) := by field_simp [h_pos.ne'] <;> ring
        have h1' : c < i + 1 := by exact_mod_cast h1
        have h2' : i < c + 1 := by exact_mod_cast h2
        omega
      have hd : d = j := by
        have h_lt1 : (d : ℝ) * Δ ^ a < (j + 1 : ℝ) * Δ ^ a := by
          have h : (d : ℝ) * Δ ^ a ≤ x 1 := h_x_in_R.2.1
          have h2 : x 1 < (j + 1 : ℝ) * Δ ^ a := hxQ.2.2
          linarith
        have h_lt2 : (j : ℝ) * Δ ^ a < (d + 1 : ℝ) * Δ ^ a := by
          have h : (j : ℝ) * Δ ^ a ≤ x 1 := hxQ.2.1
          have h2 : x 1 < (d + 1 : ℝ) * Δ ^ a := h_x_in_R.2.2
          linarith
        have h_pos : 0 < Δ ^ a := hΔa_pos
        have h1 : (d : ℝ) < (j + 1 : ℝ) := by
          calc (d : ℝ) = ((d : ℝ) * Δ ^ a) / (Δ ^ a) := by field_simp [h_pos.ne'] <;> ring
            _ < (((j + 1 : ℝ) * Δ ^ a) / (Δ ^ a)) := by gcongr
            _ = (j + 1 : ℝ) := by field_simp [h_pos.ne'] <;> ring
        have h2 : (j : ℝ) < (d + 1 : ℝ) := by
          calc (j : ℝ) = ((j : ℝ) * Δ ^ a) / (Δ ^ a) := by field_simp [h_pos.ne'] <;> ring
            _ < (((d + 1 : ℝ) * Δ ^ a) / (Δ ^ a)) := by gcongr
            _ = (d + 1 : ℝ) := by field_simp [h_pos.ne'] <;> ring
        have h1' : d < j + 1 := by exact_mod_cast h1
        have h2' : j < d + 1 := by exact_mod_cast h2
        omega
      intro z hz
      simp only [R, dyadicSquare] at hz
      have h5 : Δ ^ (a + 0) = Δ ^ a := by simp
      rw [h5] at hz
      have h6' : z 0 ∈ Set.Ico ((i : ℝ) * Δ ^ a) ((i + 1 : ℝ) * Δ ^ a) := by simpa [hc] using hz.1
      have h7' : z 1 ∈ Set.Ico ((j : ℝ) * Δ ^ a) ((j + 1 : ℝ) * Δ ^ a) := by simpa [hd] using hz.2
      simp only [Q, dyadicSquare]
      exact ⟨h6', h7'⟩
    · have h_k_pos : 0 < k := Nat.pos_of_ne_zero h_k
      have h_int1 : Set.Nonempty (Set.Ico ((c : ℝ) * Δ ^ (a + k)) ((c + 1 : ℝ) * Δ ^ (a + k)) ∩
          Set.Ico ((i : ℝ) * (Δ ^ a)) (((i + 1 : ℝ) * (Δ ^ a)))) :=
        ⟨x 0, h_x_in_R.1, hxQ.1⟩
      have h_int2 : Set.Nonempty (Set.Ico ((d : ℝ) * Δ ^ (a + k)) ((d + 1 : ℝ) * Δ ^ (a + k)) ∩
          Set.Ico ((j : ℝ) * (Δ ^ a)) (((j + 1 : ℝ) * (Δ ^ a)))) :=
        ⟨x 1, h_x_in_R.2, hxQ.2⟩
      exact dyadic_square_containment hn_pos h1 i j c d h_k_pos h_int1 h_int2
  have h_PR_eq : P ∩ R = (P ∩ Q) ∩ R := by
    ext z
    simp only [Set.mem_inter_iff]
    constructor
    · intro ⟨hzP, hzR⟩
      have hzQ : z ∈ Q := h_contain hzR
      exact ⟨⟨hzP, hzQ⟩, hzR⟩
    · intro ⟨⟨hzP, _⟩, hzR⟩
      exact ⟨hzP, hzR⟩
  -- Key: τ gives a bijection between fine square indices
  let f_idx : ℤ × ℤ → ℤ × ℤ := fun p =>
    (p.1 - i * (n ^ (k + 1)), p.2 - j * (n ^ (k + 1)))
  have h_f_inj : Function.Injective f_idx := by
    intro p1 p2 h
    have h1 : (p1.1 : ℤ) - i * (n ^ (k + 1)) = (p2.1 : ℤ) - i * (n ^ (k + 1)) := by
      exact congr_arg Prod.fst h
    have h2 : (p1.2 : ℤ) - j * (n ^ (k + 1)) = (p2.2 : ℤ) - j * (n ^ (k + 1)) := by
      exact congr_arg Prod.snd h
    have h3 : p1.1 = p2.1 := by linarith
    have h4 : p1.2 = p2.2 := by linarith
    exact Prod.ext h3 h4
  have h_f_surj : Function.Surjective f_idx := by
    intro q
    refine' ⟨(q.1 + i * (n ^ (k + 1)), q.2 + j * (n ^ (k + 1))), _⟩
    simp [f_idx, Prod.ext_iff] <;> ring
  have h_f_bij : Function.Bijective f_idx := ⟨h_f_inj, h_f_surj⟩
  have h_sq_img_fine : ∀ (p : ℤ × ℤ),
      τ '' dyadicSquare (Δ ^ (a + k + 1)) p.1 p.2 =
      dyadicSquare (Δ ^ (k + 1)) (f_idx p).1 (f_idx p).2 := by
    intro p
    let a'' := f_idx p
    have h_eq1 : i * (n ^ (k + 1)) + a''.1 = p.1 := by
      simp [a'', f_idx] <;> ring
    have h_eq2 : j * (n ^ (k + 1)) + a''.2 = p.2 := by
      simp [a'', f_idx] <;> ring
    have h_pow : a + (k + 1) = a + k + 1 := by omega
    have h := rescaled_square_image (a := a) (k := k + 1) hn_pos h1 i j a''.1 a''.2
    have h_c : (i * (n ^ (k + 1)) + a''.1 : ℤ) = p.1 := by simp [a'', f_idx] <;> ring
    have h_d : (j * (n ^ (k + 1)) + a''.2 : ℤ) = p.2 := by simp [a'', f_idx] <;> ring
    have h_goal : τ '' dyadicSquare (Δ ^ (a + k + 1)) p.1 p.2 =
        dyadicSquare (Δ ^ (k + 1)) (f_idx p).1 (f_idx p).2 := by
      simpa [τ, L, v, h_pow, h_c, h_d] using h
    exact h_goal
  have h_equiv : ∀ (p : ℤ × ℤ),
      ((P ∩ R) ∩ dyadicSquare (Δ ^ (a + k + 1)) p.1 p.2).Nonempty ↔
      ((P' ∩ R') ∩ dyadicSquare (Δ ^ (k + 1)) (f_idx p).1 (f_idx p).2).Nonempty := by
    intro p
    have h_set_eq1 : (P ∩ R) ∩ dyadicSquare (Δ ^ (a + k + 1)) p.1 p.2 =
        (P ∩ Q) ∩ R ∩ dyadicSquare (Δ ^ (a + k + 1)) p.1 p.2 := by
      rw [h_PR_eq] <;> rfl
    have h_img_inter : (τ '' (P ∩ Q)) ∩ (τ '' R) = τ '' ((P ∩ Q) ∩ R) := by
      exact (Set.image_inter h_inj (s := P ∩ Q) (t := R)).symm
    have h_set_eq2 : P' ∩ R' = τ '' ((P ∩ Q) ∩ R) := by
      have h1 : P' ∩ R' = (τ '' (P ∩ Q)) ∩ (τ '' R) := by
        rw [hP'_eq, rescaled_square_image (a := a) (k := k) hn_pos h1 i j a' b']
      rw [h1, h_img_inter]
    constructor
    · rintro ⟨z, hz1, hz2⟩
      have hz3 : z ∈ (P ∩ Q) ∩ R := by
        have hz4 : z ∈ P ∩ R := hz1
        rw [h_PR_eq] at hz4
        exact hz4
      have hzR : z ∈ R := hz3.2
      have h_τR_eq : τ '' R = R' := rescaled_square_image (a := a) (k := k) hn_pos h1 i j a' b'
      have h_τz_in_R' : τ z ∈ R' := by
        have h : τ z ∈ τ '' R := ⟨z, hzR, rfl⟩
        rw [h_τR_eq] at h
        exact h
      have h_τz_in_fine : τ z ∈ dyadicSquare (Δ ^ (k + 1)) (f_idx p).1 (f_idx p).2 := by
        rw [←h_sq_img_fine p]
        exact ⟨z, hz2, rfl⟩
      have h_τz_in_P' : τ z ∈ P' := by
        rw [hP'_eq]; exact ⟨z, hz3.1, rfl⟩
      exact ⟨τ z, ⟨h_τz_in_P', h_τz_in_R'⟩, h_τz_in_fine⟩
    · rintro ⟨w, hw1, hw2⟩
      have h_wP' : w ∈ P' := hw1.1
      have h_wR' : w ∈ R' := hw1.2
      rcases h_wP' with ⟨z, hzPQ, hz_eq⟩
      have hzR : z ∈ R := by
        have h_τR_eq : τ '' R = R' := rescaled_square_image (a := a) (k := k) hn_pos h1 i j a' b'
        have h5 : w ∈ τ '' R := by
          rw [h_τR_eq]
          exact h_wR'
        rcases h5 with ⟨z', hz'R, h_eq⟩
        have h_eq3 : τ z' = τ z := by
          calc τ z' = w := h_eq
            _ = τ z := hz_eq.symm
        have h_eq2 : z' = z := h_inj h_eq3
        rw [h_eq2] at hz'R
        exact hz'R
      have hz_fine : z ∈ dyadicSquare (Δ ^ (a + k + 1)) p.1 p.2 := by
        have h6 : τ z ∈ dyadicSquare (Δ ^ (k + 1)) (f_idx p).1 (f_idx p).2 := by
          have h7 : w = τ z := hz_eq.symm
          rw [h7] at hw2
          exact hw2
        have h7 : τ z ∈ τ '' dyadicSquare (Δ ^ (a + k + 1)) p.1 p.2 := by
          rw [h_sq_img_fine p]
          exact h6
        rcases h7 with ⟨z', hz'fine, h_eq⟩
        have h_eq2 : z' = z := h_inj h_eq
        rw [h_eq2] at hz'fine
        exact hz'fine
      have hz1 : z ∈ P ∩ R := by
        rw [h_PR_eq]; exact ⟨hzPQ, hzR⟩
      exact ⟨z, hz1, hz_fine⟩
  let S_orig : Set (ℤ × ℤ) := {p | ((P ∩ R) ∩ dyadicSquare (Δ ^ (a + k + 1)) p.1 p.2).Nonempty}
  let S_resc : Set (ℤ × ℤ) := {q | ((P' ∩ R') ∩ dyadicSquare (Δ ^ (k + 1)) q.1 q.2).Nonempty}
  have h_image : f_idx '' S_orig = S_resc := by
    ext q
    simp only [Set.mem_image, S_resc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (h_equiv p).mp hp
    · intro hq
      let p : ℤ × ℤ := (q.1 + i * (n ^ (k + 1)), q.2 + j * (n ^ (k + 1)))
      have hfp : f_idx p = q := by
        simp [p, f_idx] <;> omega
      have hq' : ((P' ∩ R') ∩ dyadicSquare (Δ ^ (k + 1)) (f_idx p).1 (f_idx p).2).Nonempty := by
        have h : (f_idx p).1 = q.1 ∧ (f_idx p).2 = q.2 := by
          simp [hfp, Prod.ext_iff] <;> omega
        rw [h.1, h.2]
        exact hq
      have hp : p ∈ S_orig := (h_equiv p).mpr hq'
      exact ⟨p, hp, hfp⟩
  have h_count_orig : (dyadicSquareCount (Δ ^ (a + k + 1)) (P ∩ R) : ENNReal) =
      (↑(N (a + k)) : ENNReal) := by
    have h2 : a + k < m := by omega
    exact h_uniform.2.2.2.2 (a + k) h2 c d hR_nonempty
  have h_count_orig_enat : dyadicSquareCount (Δ ^ (a + k + 1)) (P ∩ R) = ↑(N (a + k)) := by
    exact_mod_cast h_count_orig
  have hS_finite : S_orig.Finite := Set.finite_of_encard_eq_coe (by
    rw [show S_orig.encard = dyadicSquareCount (Δ ^ (a + k + 1)) (P ∩ R) from rfl,
      h_count_orig_enat])
  have h_encard : (f_idx '' S_orig).encard = S_orig.encard := by
    exact Function.Injective.encard_image h_f_inj S_orig
  have h_S_orig : S_orig.encard = dyadicSquareCount (Δ ^ (a + k + 1)) (P ∩ R) := by rfl
  have h_S_resc : S_resc.encard = dyadicSquareCount (Δ ^ (k + 1)) (P' ∩ R') := by rfl
  have h_final : dyadicSquareCount (Δ ^ (k + 1)) (P' ∩ R') = ↑(N (a + k)) := by
    calc dyadicSquareCount (Δ ^ (k + 1)) (P' ∩ R')
      = S_resc.encard := by rfl
    _ = (f_idx '' S_orig).encard := by rw [h_image]
    _ = S_orig.encard := h_encard
    _ = dyadicSquareCount (Δ ^ (a + k + 1)) (P ∩ R) := by rfl
    _ = ↑(N (a + k)) := h_count_orig_enat
  exact_mod_cast h_final

end DirecretisedFurstenbergEstimate.MultiscaleDecomposition
