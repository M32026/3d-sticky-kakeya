module

/-
  Dyadic uniformity definition and bridge lemmas.

  Source-faithful to OS Definition 950: uniformity is defined using dyadic
  square counts, not metric ball covering numbers.

  Key result: `IsDyadicUniform` implies the same metric covering upper bound
  (9^j * ∏ N(i)) as the old `IsUniform`, because one ball of radius r covers
  a dyadic square of side r.
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.CoveringBasics

@[expose] public section

noncomputable section

namespace DirecretisedFurstenbergEstimate
namespace MultiscaleDecomposition

/-! # Dyadic square count -/

/-- Number of dyadic δ-squares intersecting A, as ENat.
    For bounded A this is finite. -/
def dyadicSquareCount (δ : ℝ) (A : Set EuclideanPlane) : ENat :=
  Set.encard {p : ℤ × ℤ | (A ∩ dyadicSquare δ p.1 p.2).Nonempty}

/-! # Dyadic uniformity -/

/-- `P` is `(Δ^i)_{i=0}^{m-1}`-dyadic-uniform if there is a sequence `N` such
    that for every `i < m` and every dyadic `Δ^i`-square `Q` intersecting `P`,
    the number of `Δ^(i+1)`-dyadic squares intersecting `P ∩ Q` equals `N i`.
    This matches OS Definition 950, where `|P ∩ Q|_{Δ_j}` counts dyadic squares. -/
def IsDyadicUniform (P : Set EuclideanPlane) (m : ℕ) (Δ : ℝ) (N : ℕ → ℕ) : Prop :=
  0 < Δ ∧ Δ < 1 ∧ P.Nonempty ∧
  (∀ i < m, N i ≥ 1) ∧
  ∀ (i : ℕ), i < m → ∀ (a b : ℤ),
    (P ∩ dyadicSquare (Δ ^ i) a b).Nonempty →
    (dyadicSquareCount (Δ ^ (i + 1)) (P ∩ dyadicSquare (Δ ^ i) a b) : ENNReal) =
      (↑(N i) : ENNReal)

/-! # Bridge: dyadic square count → metric covering upper bound -/

/-- If `dyadicSquareCount δ A = ↑N`, then the metric covering number at scale
    δ is at most N (one ball per dyadic square, since a ball of radius δ
    covers a dyadic square of side δ). -/
lemma metricCovering_le_of_dyadicSquareCount_eq {δ : ℝ} (hδ : 0 < δ)
    {A : Set EuclideanPlane} {N : ℕ}
    (h : dyadicSquareCount δ A = ↑N) :
    Metric.externalCoveringNumber δ.toNNReal A ≤ ↑N := by
  let S_set : Set (ℤ × ℤ) := {p | (A ∩ dyadicSquare δ p.1 p.2).Nonempty}
  have h' : S_set.encard = ↑N := by
    simpa [dyadicSquareCount] using h
  have hS_finite : S_set.Finite := Set.finite_of_encard_eq_coe h'
  let S : Finset (ℤ × ℤ) := hS_finite.toFinset
  have hS_mem : ∀ (p : ℤ × ℤ), p ∈ S ↔ (A ∩ dyadicSquare δ p.1 p.2).Nonempty := by
    intro p; simp [S, hS_finite.mem_toFinset] <;> rfl
  have hS_card : S.card = N := by
    have h2 : S.card = S_set.ncard := by exact Eq.symm (Set.ncard_eq_toFinset_card S_set hS_finite)
    have h3 : (S_set.ncard : ENat) = ↑N := by
      have h41 : S_set.encard = ↑N := h'
      letI : Fintype S_set := hS_finite.fintype
      have h42 : (S_set.ncard : ENat) = S_set.encard := by
        exact Set.coe_ncard_eq_encard S_set
      rw [h42, h41]
    have h5 : S_set.ncard = N := by
      exact_mod_cast h3
    rw [h2, h5]
  let centers : Finset EuclideanPlane :=
    S.image (fun p => Classical.choose (single_ball_covers_dyadicSquare δ hδ p.1 p.2))
  have hcover : A ⊆ ⋃ (c : EuclideanPlane) (_ : c ∈ centers), Metric.closedBall c δ.toNNReal := by
    intro x hx
    let a : ℤ := ⌊x 0 / δ⌋
    let b : ℤ := ⌊x 1 / δ⌋
    have h_x_in_square : x ∈ dyadicSquare δ a b := by
      have h_floor1 : (a : ℝ) ≤ x 0 / δ := Int.floor_le (x 0 / δ)
      have h_floor2 : x 0 / δ < (a + 1 : ℝ) := Int.lt_floor_add_one (x 0 / δ)
      have h_left1 : (a : ℝ) * δ ≤ x 0 := by
        calc (a : ℝ) * δ ≤ (x 0 / δ) * δ := by gcongr
          _ = x 0 := by field_simp [hδ.ne'] <;> ring
      have h_right1 : x 0 < ((a : ℝ) + 1) * δ := by
        calc x 0 = (x 0 / δ) * δ := by field_simp [hδ.ne'] <;> ring
          _ < ((a : ℝ) + 1) * δ := by gcongr
      have h_floor3 : (b : ℝ) ≤ x 1 / δ := Int.floor_le (x 1 / δ)
      have h_floor4 : x 1 / δ < (b + 1 : ℝ) := Int.lt_floor_add_one (x 1 / δ)
      have h_left2 : (b : ℝ) * δ ≤ x 1 := by
        calc (b : ℝ) * δ ≤ (x 1 / δ) * δ := by gcongr
          _ = x 1 := by field_simp [hδ.ne'] <;> ring
      have h_right2 : x 1 < ((b : ℝ) + 1) * δ := by
        calc x 1 = (x 1 / δ) * δ := by field_simp [hδ.ne'] <;> ring
          _ < ((b : ℝ) + 1) * δ := by gcongr
      exact ⟨⟨h_left1, h_right1⟩, ⟨h_left2, h_right2⟩⟩
    have h_intersect : (A ∩ dyadicSquare δ a b).Nonempty := ⟨x, hx, h_x_in_square⟩
    have h_in_S : (a, b) ∈ S := (hS_mem (a, b)).mpr h_intersect
    let c := Classical.choose (single_ball_covers_dyadicSquare δ hδ a b)
    have hc_in : c ∈ centers := Finset.mem_image.mpr ⟨(a, b), h_in_S, rfl⟩
    have hball : dyadicSquare δ a b ⊆ Metric.closedBall c δ :=
      Classical.choose_spec (single_ball_covers_dyadicSquare δ hδ a b)
    have h_x_in_ball : x ∈ Metric.closedBall c δ.toNNReal := by
      have hball' : x ∈ Metric.closedBall c δ := hball h_x_in_square
      have h_eq : Metric.closedBall c δ = Metric.closedBall c δ.toNNReal := by
        ext y; simp [Metric.mem_closedBall, show 0 ≤ δ by linarith] <;> rfl
      rw [h_eq] at hball'
      exact hball'
    have h_goal : x ∈ ⋃ (c : EuclideanPlane) (_ : c ∈ centers), Metric.closedBall c δ.toNNReal := by
      simp only [Set.mem_iUnion]
      exact ⟨c, hc_in, h_x_in_ball⟩
    exact h_goal
  have h_is_cover : Metric.IsCover δ.toNNReal A centers := by
    rw [Metric.isCover_iff_subset_iUnion_closedBall]
    exact hcover
  have h1 : Metric.externalCoveringNumber δ.toNNReal A ≤ (↑centers : Set EuclideanPlane).encard :=
    Metric.IsCover.externalCoveringNumber_le_encard h_is_cover
  have h1' : (↑centers : Set EuclideanPlane).encard = ↑centers.card := by simp
  rw [h1'] at h1
  have h2 : (↑centers.card : ENat) ≤ (↑N : ENat) := by
    have h3 : centers.card ≤ S.card := Finset.card_image_le
    rw [hS_card] at h3
    exact_mod_cast h3
  exact le_trans h1 h2

/-! # Single-step refinement for dyadic uniformity -/

/-- Given a cover at scale Δ^k, bound covering at Δ^(k+1) by C.card * 9 * N(k). -/
lemma dyadicRefine_cover_by_squares {P : Set EuclideanPlane} {k m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N) (hk : k < m)
    (A : Set EuclideanPlane) (hA : A ⊆ P)
    (C : Finset EuclideanPlane) (hC : Metric.IsCover (Δ^k).toNNReal A C) :
    (Metric.externalCoveringNumber (Δ^(k+1)).toNNReal A : ENNReal) ≤
      (C.card : ENNReal) * 9 * (N k : ENNReal) := by
  have hΔ : 0 < Δ := h_uniform.1
  have hΔk : 0 < Δ^k := by positivity
  have hΔk1 : 0 < Δ^(k+1) := by positivity
  let squares (c : EuclideanPlane) : Finset (ℤ × ℤ) :=
    Classical.choose (ball_dyadic_squares_bound (Δ^k) hΔk c)
  have h_squares_prop (c : EuclideanPlane) :
    (∀ (i j : ℤ), (Metric.closedBall c (Δ^k) ∩ dyadicSquare (Δ^k) i j).Nonempty → (i, j) ∈ squares c) ∧
    (squares c).card ≤ 9 :=
    Classical.choose_spec (ball_dyadic_squares_bound (Δ^k) hΔk c)
  let f_inj (c : EuclideanPlane) : Function.Injective (fun p : ℤ × ℤ => (c, p)) := by
    intro p1 p2 h; exact congr_arg Prod.snd h
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
        simp [hΔk] <;> linarith
      rw [h8] at h7; exact h7
    let a : ℤ := ⌊x 0 / (Δ^k)⌋
    let b : ℤ := ⌊x 1 / (Δ^k)⌋
    have h_x_in_square : x ∈ dyadicSquare (Δ^k) a b := by
      have h_floor1 : (a : ℝ) ≤ x 0 / (Δ^k) := Int.floor_le (x 0 / (Δ^k))
      have h_floor2 : x 0 / (Δ^k) < (a + 1 : ℝ) := Int.lt_floor_add_one (x 0 / (Δ^k))
      have h_left1 : (a : ℝ) * (Δ^k) ≤ x 0 := by
        calc (a : ℝ) * (Δ^k) ≤ (x 0 / (Δ^k)) * (Δ^k) := by gcongr
          _ = x 0 := by field_simp [hΔk.ne'] <;> ring
      have h_right1 : x 0 < ((a : ℝ) + 1) * (Δ^k) := by
        calc x 0 = (x 0 / (Δ^k)) * (Δ^k) := by field_simp [hΔk.ne'] <;> ring
          _ < ((a : ℝ) + 1) * (Δ^k) := by gcongr
      have h_floor3 : (b : ℝ) ≤ x 1 / (Δ^k) := Int.floor_le (x 1 / (Δ^k))
      have h_floor4 : x 1 / (Δ^k) < (b + 1 : ℝ) := Int.lt_floor_add_one (x 1 / (Δ^k))
      have h_left2 : (b : ℝ) * (Δ^k) ≤ x 1 := by
        calc (b : ℝ) * (Δ^k) ≤ (x 1 / (Δ^k)) * (Δ^k) := by gcongr
          _ = x 1 := by field_simp [hΔk.ne'] <;> ring
      have h_right2 : x 1 < ((b : ℝ) + 1) * (Δ^k) := by
        calc x 1 = (x 1 / (Δ^k)) * (Δ^k) := by field_simp [hΔk.ne'] <;> ring
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
  have h_each_enat : ∀ p ∈ idx,
      Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p) ≤ ↑(N k) := by
    intro p hp
    by_cases hne : (P ∩ Q p).Nonempty
    · let a := p.2.1
      let b := p.2.2
      have h_unif_enreal : (dyadicSquareCount (Δ^(k+1)) (P ∩ Q p) : ENNReal) = (↑(N k) : ENNReal) :=
        h_uniform.2.2.2.2 k hk a b hne
      have h_unif_enat : dyadicSquareCount (Δ^(k+1)) (P ∩ Q p) = ↑(N k) := by
        exact_mod_cast h_unif_enreal
      exact metricCovering_le_of_dyadicSquareCount_eq hΔk1 h_unif_enat
    · have h_empty : P ∩ Q p = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using hne
      rw [h_empty] <;> simp
  have h_union_enat : Metric.externalCoveringNumber (Δ^(k+1)).toNNReal U ≤
      ∑ p ∈ idx, Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p) := by
    have h_main2 : Metric.externalCoveringNumber (Δ^(k+1)).toNNReal U ≤
        ∑ (i : {p // p ∈ idx}), Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (A' i) :=
      externalCoveringNumber_iUnion_le (ε := (Δ^(k+1)).toNNReal) (A := A')
    have h2 : ∑ (i : {p // p ∈ idx}), Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (A' i) =
        ∑ (i : {p // p ∈ idx}), Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q i.val) := by
      apply Finset.sum_congr rfl; intro i _; rfl
    have h3 : ∑ (i : {p // p ∈ idx}), Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q i.val) =
        ∑ p ∈ idx, Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p) := by
      let f : EuclideanPlane × (ℤ × ℤ) → ENat := fun p =>
        Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p)
      exact Finset.sum_attach idx f
    rw [h2, h3] at h_main2
    exact h_main2
  have h_idx_card : idx.card ≤ C.card * 9 := by
    calc idx.card
      ≤ ∑ c ∈ C, ((squares c).map ⟨fun p : ℤ × ℤ => (c, p), f_inj c⟩).card := Finset.card_biUnion_le
    _ = ∑ c ∈ C, (squares c).card := by
      apply Finset.sum_congr rfl; intro c _; rw [Finset.card_map] <;> simp
    _ ≤ ∑ c ∈ C, 9 := by apply Finset.sum_le_sum; intro c _; exact (h_squares_prop c).2
    _ = C.card * 9 := by rw [Finset.sum_const] <;> ring
  have h_final_enat : Metric.externalCoveringNumber (Δ^(k+1)).toNNReal A ≤
      ↑(C.card * 9 * N k) := by
    calc Metric.externalCoveringNumber (Δ^(k+1)).toNNReal A
      ≤ Metric.externalCoveringNumber (Δ^(k+1)).toNNReal U :=
        Metric.externalCoveringNumber_mono_set h_cover
    _ ≤ ∑ p ∈ idx, Metric.externalCoveringNumber (Δ^(k+1)).toNNReal (P ∩ Q p) := h_union_enat
    _ ≤ ∑ p ∈ idx, ↑(N k) := by
        apply Finset.sum_le_sum; intro p hp; exact h_each_enat p hp
    _ = ↑(idx.card * N k) := by
        rw [Finset.sum_const]
        <;> simp [mul_comm]
        <;> norm_cast
    _ ≤ ↑(C.card * 9 * N k) := by
        gcongr <;> exact h_idx_card
  have h_final : (Metric.externalCoveringNumber (Δ^(k+1)).toNNReal A : ENNReal) ≤
      (C.card : ENNReal) * 9 * (N k : ENNReal) := by
    have h1 : (Metric.externalCoveringNumber (Δ^(k+1)).toNNReal A : ENNReal) ≤
        (↑(C.card * 9 * N k) : ENNReal) := enat_to_ennreal_mono h_final_enat
    have h2 : (↑(C.card * 9 * N k) : ENNReal) = (C.card : ENNReal) * 9 * (N k : ENNReal) := by
      simp [mul_assoc] <;> ring
    rw [h2] at h1
    exact h1
  exact h_final

/-- Upper bound: metric covering number of P ∩ Q at scale Δ^m
    ≤ 9^(m-j) * ∏ N(i). -/
lemma dyadicCovering_product_upper {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N) {j : ℕ} (hj : j ≤ m)
    (a b : ℤ) (hQ : (P ∩ dyadicSquare (Δ ^ j) a b).Nonempty) :
    (Metric.externalCoveringNumber (Δ ^ m).toNNReal
       (P ∩ dyadicSquare (Δ ^ j) a b) : ENNReal) ≤
      (9 : ENNReal) ^ (m - j) * ∏ i ∈ Finset.range (m - j), (↑(N (j + i)) : ENNReal) := by
  let P_j := P ∩ dyadicSquare (Δ ^ j) a b
  have hΔ : 0 < Δ := h_uniform.1
  have hΔ_pos : ∀ k : ℕ, 0 < Δ ^ k := by intro k; exact pow_pos hΔ k
  have h_main : ∀ (k : ℕ), j + k ≤ m →
      (Metric.externalCoveringNumber (Δ ^ (j + k)).toNNReal P_j : ENNReal) ≤
        (9 : ENNReal) ^ k * ∏ i ∈ Finset.range k, (↑(N (j + i)) : ENNReal) := by
    intro k hk
    induction k with
    | zero =>
      have h1 : ∃ (x : EuclideanPlane), dyadicSquare (Δ ^ j) a b ⊆ Metric.closedBall x (Δ ^ j) :=
        single_ball_covers_dyadicSquare (Δ ^ j) (hΔ_pos j) a b
      rcases h1 with ⟨x, hx⟩
      have h2 : P_j ⊆ Metric.closedBall x (Δ ^ j) :=
        Set.Subset.trans (show P_j ⊆ dyadicSquare (Δ ^ j) a b from Set.inter_subset_right) hx
      have h2' : P_j ⊆ Metric.closedBall x (Δ ^ j).toNNReal := by
        have h_eq : Metric.closedBall x (Δ ^ j) = Metric.closedBall x (Δ ^ j).toNNReal := by
          ext y; simp [Metric.mem_closedBall, show 0 ≤ Δ ^ j by linarith [hΔ_pos j]] <;> rfl
        rw [h_eq] at h2
        exact h2
      have h3 : Metric.IsCover (Δ ^ j).toNNReal P_j ({x} : Set EuclideanPlane) := by
        rw [Metric.isCover_iff_subset_iUnion_closedBall]
        simpa using h2'
      have h4 : Metric.externalCoveringNumber (Δ ^ j).toNNReal P_j ≤ ({x} : Set EuclideanPlane).encard :=
        Metric.IsCover.externalCoveringNumber_le_encard h3
      have h5 : ({x} : Set EuclideanPlane).encard = 1 := by simp
      rw [h5] at h4
      have h6 : (Metric.externalCoveringNumber (Δ ^ j).toNNReal P_j : ENNReal) ≤ (1 : ENNReal) := by
        exact_mod_cast h4
      simpa using h6
    | succ k ih =>
      have h_jk_lt_m : j + k < m := by omega
      let M : ENNReal := (9 : ENNReal) ^ k * ∏ i ∈ Finset.range k, (↑(N (j + i)) : ENNReal)
      have hM_fin : M ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · have h9 : (9 : ENNReal) ^ k ≠ ⊤ := by simp
          exact h9
        · apply ENNReal.prod_ne_top; intro i _; simp
      have h_ih' : (Metric.externalCoveringNumber (Δ ^ (j + k)).toNNReal P_j : ENNReal) ≤ M := ih (by omega)
      rcases exists_finite_cover_le h_ih' hM_fin with ⟨C, hC_cover, hC_card⟩
      have h_refine := dyadicRefine_cover_by_squares h_uniform h_jk_lt_m P_j (Set.inter_subset_left) C hC_cover
      calc (Metric.externalCoveringNumber (Δ ^ (j + k + 1)).toNNReal P_j : ENNReal)
        ≤ (C.card : ENNReal) * 9 * (N (j + k) : ENNReal) := h_refine
      _ ≤ M * 9 * (N (j + k) : ENNReal) := by gcongr <;> assumption
      _ = (9 : ENNReal) ^ (k + 1) * ∏ i ∈ Finset.range (k + 1), (↑(N (j + i)) : ENNReal) := by
          simp [M, Finset.prod_range_succ, pow_succ, mul_assoc] <;> ring
  have h_final := h_main (m - j) (by omega)
  have h_eq : j + (m - j) = m := by omega
  rw [h_eq] at h_final
  exact h_final

/-- Upper bound on covering number of P ∩ scale-1 square. -/
lemma dyadicCovering_upper_per_square {P : Set EuclideanPlane} {m j : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N) (hj : j ≤ m) (a b : ℤ) :
    (Metric.externalCoveringNumber (Δ ^ j).toNNReal
       (P ∩ dyadicSquare (1 : ℝ) a b) : ENNReal) ≤
      (9 : ENNReal) ^ j * ∏ i ∈ Finset.range j, (↑(N i) : ENNReal) := by
  by_cases hQ : (P ∩ dyadicSquare (1 : ℝ) a b).Nonempty
  · have h_uniform_j : IsDyadicUniform P j Δ N :=
      ⟨h_uniform.1, h_uniform.2.1, h_uniform.2.2.1,
       fun i hi => h_uniform.2.2.2.1 i (by linarith),
       fun i hi => h_uniform.2.2.2.2 i (by linarith)⟩
    have h_delta0 : (Δ ^ 0 : ℝ) = 1 := by simp
    have hQ' : (P ∩ dyadicSquare (Δ ^ 0) a b).Nonempty := by
      rw [h_delta0] at *; exact hQ
    have h_main := dyadicCovering_product_upper h_uniform_j (j := 0) (by omega) a b hQ'
    simpa [h_delta0] using h_main
  · have h_empty : P ∩ dyadicSquare (1 : ℝ) a b = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using hQ
    rw [h_empty]; simp

end MultiscaleDecomposition
end DirecretisedFurstenbergEstimate

end
