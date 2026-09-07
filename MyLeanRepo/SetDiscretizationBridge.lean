module

/-
# Set Discretization Bridge

Converts an arbitrary bounded set A into a union A_delta of half-open
δ-dyadic intervals meeting A. This supplies the exact volume identity
needed by the Strong Ring theorem.

## Main results

- `discretizeSet δ A`: union of δ-dyadic intervals meeting A
- `volume_discretizeSet`: `volume(A_delta) = δ * Nreal(δ,A)`
- `coveringNumber_discretizeSet`: `Nreal(δ,A_delta) = Nreal(δ,A)`
- `deltaSet_transfer`: delta-set non-concentration transfers with factor 3
- `sumset_coveringNumber_discretize`: sumset covering numbers comparable
-/

public import MyLeanRepo.CoefficientRounding
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set ENNReal Classical Bornology MeasureTheory

namespace SetDiscretizationBridge

open ProductLikeIncidence (cubeIndexSet coveringNumber_eq_cubeIndexSet
  thickening_covering_factor5 mk1)

/-- Discretize A: union of all half-open δ-dyadic intervals meeting A. -/
def discretizeSet (δ : ℝ) (A : Set ℝ) : Set ℝ :=
  ⋃ k ∈ cubeIndexSet δ A, Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1))

/-- Generalized thickening factor: if S' is pointwise within M*δ of S,
then δ-covering number of S' is at most (2M+1) times that of S. -/
lemma thickening_covering_factor {δ : ℝ} (hδ : 0 < δ) {M : ℕ}
    {S S' : Set ℝ} (hS_bdd : IsBounded S)
    (h_close : ∀ p ∈ S', ∃ q ∈ S, |p - q| ≤ (M : ℝ) * δ) :
    dyadicCoveringNumber δ (productLikeRealLineCopy S') ≤
      (2 * M + 1) * dyadicCoveringNumber δ (productLikeRealLineCopy S) := by
  by_cases hS_empty : S = ∅
  · have hS'_empty : S' = ∅ := by
      by_contra h
      have hne : S'.Nonempty := Set.nonempty_iff_ne_empty.mpr h
      rcases hne with ⟨p, hp⟩
      rcases h_close p hp with ⟨q, hqS, _⟩
      rw [hS_empty] at hqS
      exact hqS
    rw [hS_empty, hS'_empty]
    <;> simp [productLikeRealLineCopy, dyadicCoveringNumber, dyadicCubesMeeting]
    <;> exact le_mul_of_one_le_left (by simp) (by norm_num)
  · let idxS := cubeIndexSet δ S
    let idxS' := cubeIndexSet δ S'
    have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS_empty
    rcases hS_nonempty with ⟨a0, ha0⟩
    have hS_bdd' : ∃ (R : ℝ), ∀ (x : ℝ), x ∈ S → ∀ (y : ℝ), y ∈ S → dist x y ≤ R :=
      Metric.isBounded_iff.mp hS_bdd
    rcases hS_bdd' with ⟨M0, hM0⟩
    have hM' : ∀ x ∈ S, |x| ≤ M0 + |a0| := by
      intro x hx
      have h1 : dist x a0 ≤ M0 := hM0 x hx a0 ha0
      have h2 : |x - a0| ≤ M0 := by simpa [Real.dist_eq] using h1
      have h_tri : |x| ≤ |x - a0| + |a0| := by
        have h : |(x - a0) + a0| ≤ |x - a0| + |a0| := abs_add_le (x - a0) a0
        have h_eq : (x - a0) + a0 = x := by ring
        rw [h_eq] at h
        exact h
      linarith
    let R := M0 + |a0|
    have h_idxS_finite : Set.Finite idxS := by
      have h1 : ∀ k ∈ idxS, -R / δ - 2 ≤ (k : ℝ) ∧ (k : ℝ) ≤ R / δ + 1 := by
        intro k hk
        rcases hk with ⟨p, ⟨hp1, hp2⟩, hpS⟩
        have h_p_bdd : |p| ≤ R := hM' p hpS
        have h2 : -R ≤ p := (abs_le.mp h_p_bdd).1
        have h3 : p ≤ R := (abs_le.mp h_p_bdd).2
        constructor
        · have h4 : -R < δ * ((k : ℝ) + 1) := by linarith
          have h5 : -R / δ < (k : ℝ) + 1 := by
            have h6 : (-R) / δ < (δ * ((k : ℝ) + 1)) / δ := by
              apply div_lt_div_of_pos_right h4 hδ
            simpa [hδ.ne'] using h6
          linarith
        · have h4 : δ * (k : ℝ) ≤ R := by linarith
          have h5 : (k : ℝ) ≤ R / δ := by
            have h6 : (δ * (k : ℝ)) / δ ≤ R / δ := by
              apply div_le_div_of_nonneg_right h4 (by linarith)
            simpa [hδ.ne'] using h6
          linarith
      have h4 : idxS ⊆ Set.Icc (Int.ceil (-R / δ - 2)) (Int.floor (R / δ + 1)) := by
        intro k hk
        have h5 := h1 k hk
        have h6 : k ≤ Int.floor (R / δ + 1) := by
          apply Int.le_floor.mpr
          exact h5.2
        have h7 : Int.ceil (-R / δ - 2) ≤ k := by
          apply Int.ceil_le.mpr
          exact h5.1
        exact ⟨h7, h6⟩
      exact Set.Finite.subset (Set.finite_Icc _ _) h4
    have h_main : idxS' ⊆ ⋃ m ∈ idxS, (Finset.Icc (m - M) (m + M) : Set ℤ) := by
      intro k hk
      rcases hk with ⟨p, ⟨hp1, hp2⟩, hpS'⟩
      rcases h_close p hpS' with ⟨q, hqS, hdist⟩
      let m : ℤ := Int.floor (q / δ)
      have hm1 : δ * (m : ℝ) ≤ q := by
        have h : (m : ℝ) ≤ q / δ := Int.floor_le (q / δ)
        have h2 : δ * (m : ℝ) ≤ δ * (q / δ) := by gcongr
        have h3 : δ * (q / δ) = q := by field_simp [hδ.ne'] <;> ring
        rw [h3] at h2; exact h2
      have hm2 : q < δ * ((m : ℝ) + 1) := by
        have h : q / δ < (m : ℝ) + 1 := Int.lt_floor_add_one (q / δ)
        have h2 : δ * (q / δ) < δ * ((m : ℝ) + 1) := by gcongr
        have h3 : δ * (q / δ) = q := by field_simp [hδ.ne'] <;> ring
        rw [h3] at h2; exact h2
      have hm_in_idxS : m ∈ idxS := by
        simp only [idxS, cubeIndexSet, Set.mem_setOf_eq]
        exact ⟨q, ⟨hm1, hm2⟩, hqS⟩
      have h_k_le : k ≤ m + (M : ℤ) := by
        have h : p - q ≤ (M : ℝ) * δ := by
          have h' : |p - q| ≤ (M : ℝ) * δ := hdist
          exact (abs_le.mp h').2
        have h'' : p < δ * ((m : ℝ) + 1) + (M : ℝ) * δ := by linarith
        have h4 : (k : ℝ) < (m : ℝ) + 1 + (M : ℝ) := by nlinarith
        have h_eq : (m : ℝ) + 1 + (M : ℝ) = ↑(m + (M : ℤ) + 1) := by
          simp [Nat.cast_add, Int.cast_add] <;> ring
        have h5 : (k : ℝ) < ↑(m + (M : ℤ) + 1) := by
          rw [h_eq] at h4
          exact h4
        have h6 : k < m + (M : ℤ) + 1 := by exact_mod_cast h5
        omega
      have h_k_ge : m - (M : ℤ) ≤ k := by
        have h : q - p ≤ (M : ℝ) * δ := by
          have h' : |p - q| ≤ (M : ℝ) * δ := hdist
          have h'' : |q - p| ≤ (M : ℝ) * δ := by
            rw [show q - p = -(p - q) by ring]
            rw [abs_neg] <;> exact h'
          exact (abs_le.mp h'').2
        have h'' : q < δ * ((k : ℝ) + 1) + (M : ℝ) * δ := by linarith
        have h4 : (m : ℝ) < (k : ℝ) + 1 + (M : ℝ) := by nlinarith
        have h_eq : (k : ℝ) + 1 + (M : ℝ) = ↑(k + (M : ℤ) + 1) := by
          simp [Nat.cast_add, Int.cast_add] <;> ring
        have h5 : (m : ℝ) < ↑(k + (M : ℤ) + 1) := by
          rw [h_eq] at h4
          exact h4
        have h6 : m < k + (M : ℤ) + 1 := by exact_mod_cast h5
        omega
      have h_k_range : k ∈ (Finset.Icc (m - (M : ℤ)) (m + (M : ℤ)) : Set ℤ) := by
        simp only [Finset.mem_Icc, Finset.mem_coe]
        exact ⟨h_k_ge, h_k_le⟩
      exact Set.mem_iUnion₂.mpr ⟨m, hm_in_idxS, h_k_range⟩
    have h5 : (idxS').encard ≤ (⋃ m ∈ idxS, (Finset.Icc (m - M) (m + M) : Set ℤ)).encard :=
      Set.encard_mono h_main
    let idxS_fin : Finset ℤ := h_idxS_finite.toFinset
    let U : Finset ℤ := idxS_fin.biUnion (fun m => Finset.Icc (m - M) (m + M))
    have hU : (U : Set ℤ) = (⋃ m ∈ idxS, (Finset.Icc (m - M) (m + M) : Set ℤ)) := by
      ext z
      simp [U, idxS_fin, Set.Finite.mem_toFinset] <;> aesop
    have h7 : Set.Finite (⋃ m ∈ idxS, (Finset.Icc (m - M) (m + M) : Set ℤ)) := by
      rw [← hU]
      exact U.finite_toSet
    have h8 : U.card ≤ ∑ m ∈ idxS_fin, (Finset.Icc (m - M) (m + M)).card :=
      Finset.card_biUnion_le
    have h9 : ∀ m : ℤ, (Finset.Icc (m - M) (m + M)).card = 2 * M + 1 := by
      intro m
      simp [Finset.Icc_eq_empty_of_lt]
      <;> omega
    have h10 : U.card ≤ (2 * M + 1) * idxS_fin.card := by
      calc U.card
        ≤ ∑ m ∈ idxS_fin, (Finset.Icc (m - M) (m + M)).card := h8
      _ = ∑ m ∈ idxS_fin, (2 * M + 1) := by
        apply Finset.sum_congr rfl
        intro m _
        exact h9 m
      _ = (2 * M + 1) * idxS_fin.card := by
        rw [Finset.sum_const] <;> ring
    have h13 : (⋃ m ∈ idxS, (Finset.Icc (m - M) (m + M) : Set ℤ)).encard = ↑U.card := by
      have h_eq : (⋃ m ∈ idxS, (Finset.Icc (m - M) (m + M) : Set ℤ)) = (U : Set ℤ) := hU.symm
      rw [h_eq]
      simp
    have h14 : idxS.encard = ↑idxS_fin.card := by
      have h_eq : idxS = (idxS_fin : Set ℤ) := by
        ext y
        simp [idxS_fin, Set.Finite.mem_toFinset] <;> tauto
      rw [h_eq]
      simp
    have h6 : (⋃ m ∈ idxS, (Finset.Icc (m - M) (m + M) : Set ℤ)).encard ≤
        (2 * M + 1) * idxS.encard := by
      rw [h13, h14]
      exact_mod_cast h10
    have h10' : (idxS').encard ≤ (2 * M + 1) * idxS.encard := le_trans h5 h6
    have h11 : dyadicCoveringNumber δ (productLikeRealLineCopy S') = (idxS').encard :=
      coveringNumber_eq_cubeIndexSet hδ
    have h12 : dyadicCoveringNumber δ (productLikeRealLineCopy S) = (idxS).encard :=
      coveringNumber_eq_cubeIndexSet hδ
    rw [h11, h12]
    exact h10'

/-- The δ-dyadic intervals are pairwise disjoint. -/
lemma dyadic_intervals_disjoint {δ : ℝ} (hδ : 0 < δ) {k1 k2 : ℤ}
    (h : k1 ≠ k2) :
    Disjoint (Set.Ico (δ * (k1 : ℝ)) (δ * ((k1 : ℝ) + 1)))
      (Set.Ico (δ * (k2 : ℝ)) (δ * ((k2 : ℝ) + 1))) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have h1 : δ * (k1 : ℝ) ≤ x := hx1.1
  have h2 : x < δ * ((k1 : ℝ) + 1) := hx1.2
  have h3 : δ * (k2 : ℝ) ≤ x := hx2.1
  have h4 : x < δ * ((k2 : ℝ) + 1) := hx2.2
  have h5 : (k1 : ℝ) < (k2 : ℝ) + 1 := by nlinarith
  have h6 : (k2 : ℝ) < (k1 : ℝ) + 1 := by nlinarith
  have h7 : k1 < k2 + 1 := by exact_mod_cast h5
  have h8 : k2 < k1 + 1 := by exact_mod_cast h6
  have h9 : k1 = k2 := by omega
  exact h h9

/-- `cubeIndexSet δ A` is finite when A is bounded. -/
lemma cubeIndexSet_finite {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA_bdd : IsBounded A) : Set.Finite (cubeIndexSet δ A) := by
  by_cases hA_empty : A = ∅
  · rw [hA_empty]
    have h : cubeIndexSet δ ∅ = ∅ := by
      ext k
      simp [cubeIndexSet]
    rw [h]
    exact Set.finite_empty
  · have hA_nonempty : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA_empty
    rcases hA_nonempty with ⟨a0, ha0⟩
    have hA_bdd' : ∃ (M : ℝ), ∀ (x : ℝ), x ∈ A → ∀ (y : ℝ), y ∈ A → dist x y ≤ M :=
      Metric.isBounded_iff.mp hA_bdd
    rcases hA_bdd' with ⟨M, hM⟩
    have hM' : ∀ x ∈ A, |x| ≤ M + |a0| := by
      intro x hx
      have h1 : dist x a0 ≤ M := hM x hx a0 ha0
      have h2 : |x - a0| ≤ M := by simpa [Real.dist_eq] using h1
      have h_tri : |x| ≤ |x - a0| + |a0| := by
        have h : |(x - a0) + a0| ≤ |x - a0| + |a0| := abs_add_le (x - a0) a0
        have h_eq : (x - a0) + a0 = x := by ring
        rw [h_eq] at h
        exact h
      linarith
    let R := M + |a0|
    have h1 : ∀ k ∈ cubeIndexSet δ A, -R / δ - 2 ≤ (k : ℝ) ∧ (k : ℝ) ≤ R / δ + 1 := by
      intro k hk
      rcases hk with ⟨p, ⟨hp1, hp2⟩, hpS⟩
      have h_p_bdd : |p| ≤ R := hM' p hpS
      have h2 : -R ≤ p := (abs_le.mp h_p_bdd).1
      have h3 : p ≤ R := (abs_le.mp h_p_bdd).2
      constructor
      · have h4 : -R < δ * ((k : ℝ) + 1) := by linarith
        have h5 : -R / δ < (k : ℝ) + 1 := by
          have h6 : (-R) / δ < (δ * ((k : ℝ) + 1)) / δ := by
            apply div_lt_div_of_pos_right h4 hδ
          simpa [hδ.ne'] using h6
        linarith
      · have h4 : δ * (k : ℝ) ≤ R := by linarith
        have h5 : (k : ℝ) ≤ R / δ := by
          have h6 : (δ * (k : ℝ)) / δ ≤ R / δ := by
            apply div_le_div_of_nonneg_right h4 (by linarith)
          simpa [hδ.ne'] using h6
        linarith
    have h4 : cubeIndexSet δ A ⊆ Set.Icc (Int.ceil (-R / δ - 2)) (Int.floor (R / δ + 1)) := by
      intro k hk
      have h5 := h1 k hk
      have h6 : k ≤ Int.floor (R / δ + 1) := by
        apply Int.le_floor.mpr
        exact h5.2
      have h7 : Int.ceil (-R / δ - 2) ≤ k := by
        apply Int.ceil_le.mpr
        exact h5.1
      exact ⟨h7, h6⟩
    exact Set.Finite.subset (Set.finite_Icc _ _) h4

/-- Volume of discretized set: `volume(A_delta) = δ * Nreal(δ,A)`. -/
lemma volume_discretizeSet {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA_bdd : IsBounded A) :
    volume (discretizeSet δ A) = ENNReal.ofReal δ * Nreal δ A := by
  let idxS := cubeIndexSet δ A
  have h_idxS_finite : Set.Finite idxS := cubeIndexSet_finite hδ hA_bdd
  let idxS_fin : Finset ℤ := h_idxS_finite.toFinset
  have h_disj : ∀ k1 ∈ idxS, ∀ k2 ∈ idxS, k1 ≠ k2 →
      Disjoint (Set.Ico (δ * (k1 : ℝ)) (δ * ((k1 : ℝ) + 1)))
        (Set.Ico (δ * (k2 : ℝ)) (δ * ((k2 : ℝ) + 1))) := by
    intro k1 _ k2 _ hne
    exact dyadic_intervals_disjoint hδ hne
  have h_vol : ∀ k : ℤ, volume (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1))) = ENNReal.ofReal δ := by
    intro k
    have h_diff : (δ * ((k : ℝ) + 1)) - δ * (k : ℝ) = δ := by ring
    rw [Real.volume_Ico, h_diff]
    <;> norm_num
  have h_main : volume (discretizeSet δ A) =
      ∑ k ∈ idxS_fin, volume (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1))) := by
    have h_eq : discretizeSet δ A = ⋃ k ∈ idxS_fin, Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := by
      simp [discretizeSet, idxS_fin, Set.Finite.mem_toFinset] <;> rfl
    rw [h_eq]
    have h : volume (⋃ k ∈ idxS_fin, Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1))) =
        ∑ k ∈ idxS_fin, volume (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1))) := by
      have h_disj' : (↑idxS_fin : Set ℤ).PairwiseDisjoint (fun k : ℤ => Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1))) := by
        intro i _ j _ hne
        exact dyadic_intervals_disjoint hδ hne
      have h_meas : ∀ k ∈ idxS_fin, MeasurableSet (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1))) := by
        intro k _
        exact measurableSet_Ico
      exact MeasureTheory.measure_biUnion_finset h_disj' h_meas
    exact h
  rw [h_main]
  have h_sum : ∑ k ∈ idxS_fin, volume (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1))) =
      ENNReal.ofReal δ * ↑idxS_fin.card := by
    rw [Finset.sum_congr rfl (fun k _ => h_vol k)]
    rw [Finset.sum_const]
    <;> ring
  rw [h_sum]
  have h_line_copy_eq : realLineCopy A = productLikeRealLineCopy A := by rfl
  have h1 : dyadicCoveringNumber δ (realLineCopy A) = idxS.encard := by
    rw [h_line_copy_eq]
    exact coveringNumber_eq_cubeIndexSet hδ
  have h2 : idxS.encard = ↑idxS_fin.card := by
    have h_eq : idxS = (idxS_fin : Set ℤ) := by
      ext y
      simp [idxS_fin, Set.Finite.mem_toFinset]
      <;> tauto
    rw [h_eq]
    simp
  have h_Nreal : Nreal δ A = ↑idxS_fin.card := by
    simp only [Nreal, h1, h2]
    <;> rfl
  rw [h_Nreal]
  <;> ring

/-- Covering number equality: `Nreal(δ,A_delta) = Nreal(δ,A)`. -/
lemma coveringNumber_discretizeSet {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ} :
    cubeIndexSet δ (discretizeSet δ A) = cubeIndexSet δ A := by
  ext k
  simp only [cubeIndexSet, Set.mem_setOf_eq]
  constructor
  · -- If interval k meets A_delta, it meets A
    rintro ⟨x, hxI, hxAδ⟩
    have h_x_in_union : x ∈ discretizeSet δ A := hxAδ
    rcases Set.mem_iUnion₂.mp h_x_in_union with ⟨j, hj, hxj⟩
    have h_x_in_Ij : x ∈ Set.Ico (δ * (j : ℝ)) (δ * ((j : ℝ) + 1)) := hxj
    have h_k_eq_j : k = j := by
      by_contra hne
      have h_disj := dyadic_intervals_disjoint hδ hne
      have h_contra : x ∉ Set.Ico (δ * (j : ℝ)) (δ * ((j : ℝ) + 1)) :=
        (Set.disjoint_left.mp h_disj) hxI
      exact h_contra h_x_in_Ij
    rw [h_k_eq_j] at *
    exact hj
  · -- If interval k meets A, it meets A_delta (since interval ⊆ A_delta)
    rintro ⟨x, hxI, hxA⟩
    have h_k_in : k ∈ cubeIndexSet δ A := by
      simp only [cubeIndexSet, Set.mem_setOf_eq]
      exact ⟨x, hxI, hxA⟩
    have h_x_in_Aδ : x ∈ discretizeSet δ A := by
      apply Set.mem_iUnion₂.mpr
      exact ⟨k, h_k_in, hxI⟩
    exact ⟨x, hxI, h_x_in_Aδ⟩

/-- Every point of A_delta is within δ of some point of A. -/
lemma discretizeSet_close {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ} {x : ℝ}
    (hx : x ∈ discretizeSet δ A) : ∃ y ∈ A, |x - y| < δ := by
  rcases Set.mem_iUnion₂.mp hx with ⟨k, hk, hxI⟩
  rcases hk with ⟨y, hyI, hyA⟩
  have h1 : x ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := hxI
  have h2 : y ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := hyI
  have h3 : |x - y| < δ := by
    rw [abs_sub_lt_iff]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  exact ⟨y, hyA, h3⟩

/-- Sumsets covering number comparability:
Nδ(A_delta + x*A_delta) ≤ (2M+1) * Nδ(A + x*A) when |x|+1 ≤ M. -/
lemma sumset_coveringNumber_discretize {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA : A ⊆ Set.Icc 1 2) {x : ℝ} {M : ℕ} (hM : (1 + |x| : ℝ) ≤ (M : ℝ)) :
    dyadicCoveringNumber δ (productLikeRealLineCopy
      (Set.image2 (fun a b => a + x * b) (discretizeSet δ A) (discretizeSet δ A))) ≤
    (2 * M + 1) * dyadicCoveringNumber δ (productLikeRealLineCopy
      (Set.image2 (fun a b => a + x * b) A A)) := by
  let S := Set.image2 (fun a b => a + x * b) A A
  let S' := Set.image2 (fun a b => a + x * b) (discretizeSet δ A) (discretizeSet δ A)
  have hA_bdd : IsBounded A := by
    have h : IsBounded (Set.Icc (1 : ℝ) 2) := Metric.isBounded_Icc 1 2
    exact IsBounded.subset h hA
  have hS_bdd : IsBounded S := by
    let B : ℝ := 2 + 2 * |x|
    have h1 : S ⊆ Set.Icc (-B) B := by
      intro z hz
      rcases hz with ⟨a, ha, b, hb, rfl⟩
      have ha1 : 1 ≤ a := (hA ha).1
      have ha2 : a ≤ 2 := (hA ha).2
      have hb1 : 1 ≤ b := (hA hb).1
      have hb2 : b ≤ 2 := (hA hb).2
      have ha_abs : |a| ≤ 2 := by
        have h : |a| = a := abs_of_pos (by linarith)
        rw [h] <;> linarith
      have hb_abs : |b| ≤ 2 := by
        have h : |b| = b := abs_of_pos (by linarith)
        rw [h] <;> linarith
      have h_tri : |a + x * b| ≤ |a| + |x * b| := abs_add_le a (x * b)
      have h_abs : |a + x * b| ≤ B := by
        calc |a + x * b|
          ≤ |a| + |x * b| := h_tri
        _ = |a| + |x| * |b| := by rw [abs_mul]
        _ ≤ 2 + |x| * 2 := by gcongr <;> linarith
        _ = B := by simp [B] <;> ring
      have h_lower : -B ≤ a + x * b := by linarith [abs_le.mp h_abs]
      have h_upper : a + x * b ≤ B := by linarith [abs_le.mp h_abs]
      exact ⟨h_lower, h_upper⟩
    have h2 : IsBounded (Set.Icc (-B) B) := Metric.isBounded_Icc (-B) B
    exact IsBounded.subset h2 h1
  have h_close : ∀ p ∈ S', ∃ q ∈ S, |p - q| ≤ (M : ℝ) * δ := by
    intro p hp
    rcases hp with ⟨aδ, haδ, bδ, hbδ, rfl⟩
    rcases discretizeSet_close hδ haδ with ⟨a, haA, hca⟩
    rcases discretizeSet_close hδ hbδ with ⟨b, hbA, hcb⟩
    let q : ℝ := a + x * b
    have hq : q ∈ S := ⟨a, haA, b, hbA, rfl⟩
    have h_dist : |(aδ + x * bδ) - q| ≤ (M : ℝ) * δ := by
      have h1 : |(aδ + x * bδ) - (a + x * b)| ≤ |aδ - a| + |x| * |bδ - b| := by
        calc |(aδ + x * bδ) - (a + x * b)|
          = |(aδ - a) + x * (bδ - b)| := by ring_nf
        _ ≤ |aδ - a| + |x * (bδ - b)| := abs_add_le _ _
        _ = |aδ - a| + |x| * |bδ - b| := by rw [abs_mul]
      have h2 : |aδ - a| < δ := hca
      have h3 : |bδ - b| < δ := hcb
      have h4 : |aδ - a| + |x| * |bδ - b| ≤ (1 + |x|) * δ := by
        have h5 : |aδ - a| ≤ δ := by linarith
        have h6 : |x| * |bδ - b| ≤ |x| * δ := by
          gcongr
          <;> linarith
        linarith
      have h7 : |(aδ + x * bδ) - q| ≤ (1 + |x|) * δ := by linarith
      have h8 : (1 + |x|) * δ ≤ (M : ℝ) * δ := by
        gcongr <;> linarith
      linarith
    exact ⟨q, hq, h_dist⟩
  exact thickening_covering_factor hδ hS_bdd h_close

/-- Real dyadic interval of side r with integer index m. -/
def realDyadicCube (r : ℝ) (m : ℤ) : Set ℝ :=
  Set.Ico (r * (m : ℝ)) (r * ((m : ℝ) + 1))

/-- cubeIndexSet distributes over union. -/
lemma cubeIndexSet_union {δ : ℝ} {S1 S2 : Set ℝ} :
    cubeIndexSet δ (S1 ∪ S2) = cubeIndexSet δ S1 ∪ cubeIndexSet δ S2 := by
  ext k
  simp [cubeIndexSet, Set.inter_union_distrib_left]
  <;> tauto

/-- Key containment for delta-set transfer: δ-intervals meeting
`(discretizeSet δ A) ∩ I` also meet `A ∩ I` enlarged by δ. -/
lemma transfer_key_containment {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hδ_le_r : δ ≤ r)
    {A : Set ℝ} {m : ℤ} :
    cubeIndexSet δ ((discretizeSet δ A) ∩ realDyadicCube r m) ⊆
      cubeIndexSet δ (A ∩ Set.Ico (r * (m : ℝ) - δ) (r * ((m : ℝ) + 1) + δ)) := by
  intro k hk
  rcases hk with ⟨x, hxJ, ⟨hxAδ, hxI⟩⟩
  rcases Set.mem_iUnion₂.mp hxAδ with ⟨l, hl, hxIl⟩
  have h_k_eq_l : k = l := by
    by_contra hne
    have h_disj := dyadic_intervals_disjoint hδ hne
    have h_contra : x ∉ Set.Ico (δ * (l : ℝ)) (δ * ((l : ℝ) + 1)) :=
      (Set.disjoint_left.mp h_disj) hxJ
    exact h_contra hxIl
  subst h_k_eq_l
  rcases hl with ⟨y, hyJ, hyA⟩
  have h_y_in_enlarged : y ∈ Set.Ico (r * (m : ℝ) - δ) (r * ((m : ℝ) + 1) + δ) := by
    have h1 : δ * (k : ℝ) ≤ y := hyJ.1
    have h2 : y < δ * ((k : ℝ) + 1) := hyJ.2
    have h3 : r * (m : ℝ) ≤ x := hxI.1
    have h4 : x < r * ((m : ℝ) + 1) := hxI.2
    have h5 : δ * (k : ℝ) ≤ x := hxJ.1
    have h6 : x < δ * ((k : ℝ) + 1) := hxJ.2
    constructor <;> linarith
  exact ⟨y, hyJ, ⟨hyA, h_y_in_enlarged⟩⟩

/-- The enlarged interval is contained in 3 adjacent dyadic cubes. -/
lemma enlarged_contained_in_three {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hδ_le_r : δ ≤ r)
    {m : ℤ} :
    Set.Ico (r * (m : ℝ) - δ) (r * ((m : ℝ) + 1) + δ) ⊆
      realDyadicCube r (m - 1) ∪ realDyadicCube r m ∪ realDyadicCube r (m + 1) := by
  intro x hx
  have h1 : r * (m : ℝ) - δ ≤ x := hx.1
  have h2 : x < r * ((m : ℝ) + 1) + δ := hx.2
  have h3 : r * ((m : ℝ) - 1) ≤ x := by linarith
  have h4 : x < r * ((m : ℝ) + 2) := by linarith
  by_cases h8 : x < r * (m : ℝ)
  · have h_left : x ∈ realDyadicCube r (m - 1) := by
      simpa [realDyadicCube, Int.cast_sub] using ⟨h3, h8⟩
    simp [h_left]
  · by_cases h9 : x < r * ((m : ℝ) + 1)
    · have h_mid : x ∈ realDyadicCube r m := by
        simpa [realDyadicCube] using ⟨by linarith, h9⟩
      simp [h_mid]
    · have h9' : r * ((m : ℝ) + 1) ≤ x := by linarith
      have h_lower : r * ((m + 1 : ℤ) : ℝ) ≤ x := by
        have h_eq : r * ((m + 1 : ℤ) : ℝ) = r * ((m : ℝ) + 1) := by norm_cast <;> ring
        rw [h_eq]
        exact h9'
      have h_upper : x < r * (((m + 1 : ℤ) : ℝ) + 1) := by
        have h_eq : r * (((m + 1 : ℤ) : ℝ) + 1) = r * ((m : ℝ) + 2) := by norm_cast <;> ring_nf
        rw [h_eq]
        exact h4
      have h_right : x ∈ realDyadicCube r (m + 1) := ⟨h_lower, h_upper⟩
      simp [h_right]

/-- A is contained in its discretization. -/
lemma subset_discretizeSet {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ} :
    A ⊆ discretizeSet δ A := by
  intro x hx
  let k : ℤ := Int.floor (x / δ)
  have h1 : δ * (k : ℝ) ≤ x := by
    have h : (k : ℝ) ≤ x / δ := Int.floor_le (x / δ)
    have h2 : δ * (k : ℝ) ≤ δ * (x / δ) := by gcongr
    have h3 : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
    rw [h3] at h2; exact h2
  have h2 : x < δ * ((k : ℝ) + 1) := by
    have h : x / δ < (k : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
    have h2 : δ * (x / δ) < δ * ((k : ℝ) + 1) := by gcongr
    have h3 : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
    rw [h3] at h2; exact h2
  have hk : k ∈ cubeIndexSet δ A := by
    simp only [cubeIndexSet, Set.mem_setOf_eq]
    exact ⟨x, ⟨h1, h2⟩, hx⟩
  exact Set.mem_iUnion₂.mpr ⟨k, hk, ⟨h1, h2⟩⟩

/-- A_delta is bounded if A is bounded. -/
lemma discretizeSet_bounded {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA_bdd : IsBounded A) : IsBounded (discretizeSet δ A) := by
  have h1 : Set.Finite (cubeIndexSet δ A) := cubeIndexSet_finite hδ hA_bdd
  let idxS_fin : Finset ℤ := h1.toFinset
  have h2 : ∀ k ∈ idxS_fin, IsBounded (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1))) := by
    intro k _
    exact Metric.isBounded_Ico (δ * ↑k) (δ * (↑k + 1))
  have h3 : IsBounded (⋃ k ∈ idxS_fin, Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1))) := by
    exact (isBounded_biUnion_finset idxS_fin).mpr h2
  have h4 : discretizeSet δ A = ⋃ k ∈ idxS_fin, Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := by
    simp [discretizeSet, idxS_fin, Set.Finite.mem_toFinset] <;> rfl
  rw [h4]
  exact h3

/-- Helper: Euclidean dyadic cube corresponds to real dyadic interval. -/
lemma euclidean_cube_eq_real {r : ℝ} {m : ℤ} :
    dyadicCube r (fun (_ : Fin 1) => m) = productLikeRealLineCopy (realDyadicCube r m) := by
  ext x
  simp only [dyadicCube, realDyadicCube, productLikeRealLineCopy, Set.mem_setOf_eq, Set.mem_Ico]
  <;> aesop

/-- Helper: intersection commutes with productLikeRealLineCopy. -/
lemma lineCopy_inter {S T : Set ℝ} :
    productLikeRealLineCopy S ∩ productLikeRealLineCopy T = productLikeRealLineCopy (S ∩ T) := by
  ext x
  simp only [productLikeRealLineCopy, Set.mem_inter_iff, Set.mem_setOf_eq]
  <;> aesop

/-- Boundedness transfers between A and its real-line copy. -/
lemma realLineCopy_bounded_iff {A : Set ℝ} :
    IsBounded (productLikeRealLineCopy A) ↔ IsBounded A := by
  let g : EuclideanSpace ℝ (Fin 1) → ℝ := fun x => x 0
  let f : ℝ → EuclideanSpace ℝ (Fin 1) := mk1
  have h_g : LipschitzWith 1 g := by
    intro x y
    have h1 : |x 0 - y 0| ≤ ‖x - y‖ := by
      have h2 : |x 0 - y 0| ^ 2 ≤ ∑ i : Fin 1, |(x - y) i| ^ 2 := by
        simp [Finset.sum_singleton] <;> exact le_refl _
      have h3 : |x 0 - y 0| ≤ Real.sqrt (∑ i : Fin 1, |(x - y) i| ^ 2) :=
        Real.le_sqrt_of_sq_le h2
      simpa [EuclideanSpace.norm_eq] using h3
    have h4 : dist (g x) (g y) ≤ dist x y := by
      simpa [g, dist_eq_norm, Real.dist_eq] using h1
    have h5 : edist (g x) (g y) ≤ (1 : ENNReal) * edist x y := by
      rw [one_mul]
      exact PiLp.edist_apply_le x y 0
    exact h5
  have h_f : LipschitzWith 1 f := by
    intro x y
    have h_eq1 : ‖mk1 x - mk1 y‖ = Real.sqrt ((x - y) ^ 2) := by
      simp [mk1, EuclideanSpace.norm_eq, Finset.sum_singleton] <;> ring
    have h_eq : ‖mk1 x - mk1 y‖ = |x - y| := by
      rw [h_eq1]
      have h_sq : Real.sqrt ((x - y) ^ 2) = |x - y| := by
        exact Real.sqrt_sq_eq_abs (x - y)
      exact h_sq
    have h4 : dist (f x) (f y) ≤ dist x y := by
      simpa [f, dist_eq_norm, Real.dist_eq] using le_of_eq h_eq
    have h6 : edist (f x) (f y) = ENNReal.ofReal (dist (f x) (f y)) := by
      exact edist_dist (f x) (f y)
    have h7 : edist x y = ENNReal.ofReal (dist x y) := by exact edist_dist x y
    have h5 : edist (f x) (f y) ≤ (1 : ENNReal) * edist x y := by
      rw [one_mul, h6, h7]
      exact ENNReal.ofReal_le_ofReal h4
    exact h5
  have h_eq1 : g '' (productLikeRealLineCopy A) = A := by
    ext y
    simp only [g, productLikeRealLineCopy, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy
      refine ⟨mk1 y, hy, rfl⟩
  have h_eq2 : f '' A = productLikeRealLineCopy A := by
    ext x
    simp only [f, productLikeRealLineCopy, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have h4 : (mk1 a) 0 = a := by simp [mk1] <;> rfl
      have h5 : (mk1 a) 0 ∈ A := by rw [h4]; exact ha
      exact h5
    · intro hx
      refine ⟨x 0, hx, ?_⟩
      ext i
      fin_cases i <;> rfl
  constructor
  · intro h
    have h' : IsBounded (g '' (productLikeRealLineCopy A)) := h_g.isBounded_image h
    rw [h_eq1] at h'; exact h'
  · intro h
    have h' : IsBounded (f '' A) := h_f.isBounded_image h
    rw [h_eq2] at h'; exact h'

/-- Nonemptiness transfers between A and its real-line copy. -/
lemma realLineCopy_nonempty_iff {A : Set ℝ} :
    (productLikeRealLineCopy A).Nonempty ↔ A.Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    have h : x 0 ∈ A := by
      simp only [productLikeRealLineCopy, Set.mem_setOf_eq] at hx; exact hx
    exact ⟨x 0, h⟩
  · rintro ⟨a, ha⟩
    have h : mk1 a ∈ productLikeRealLineCopy A := by
      simp only [productLikeRealLineCopy, Set.mem_setOf_eq] <;> exact ha
    exact ⟨mk1 a, h⟩

/-- Monotonicity of cube index set. -/
lemma cubeIndexSet_mono {δ : ℝ} {S T : Set ℝ} (h : S ⊆ T) :
    cubeIndexSet δ S ⊆ cubeIndexSet δ T := by
  intro k hk
  simp only [cubeIndexSet, Set.mem_setOf_eq] at hk ⊢
  rcases hk with ⟨x, hx1, hx2⟩
  exact ⟨x, hx1, h hx2⟩

/-- Full delta-set transfer: if A is a (δ,κ,C)-set, then A_delta is a (δ,κ,3C)-set. -/
theorem deltaSet_transfer {δ κ C : ℝ} {A : Set ℝ}
    (hA : IsProductLikeRealDeltaSCSet δ κ C A) :
    IsProductLikeRealDeltaSCSet δ κ (3 * C) (discretizeSet δ A) := by
  rcases hA with ⟨hA_bdd, hA_nonempty, h_d1, hδ_dyadic, hδ_pos, hκ_nonneg, hκ_le_one, hC_pos, hA_bound⟩
  have hA_bdd' : IsBounded A := realLineCopy_bounded_iff.mp hA_bdd
  have hA_nonempty' : A.Nonempty := realLineCopy_nonempty_iff.mp hA_nonempty
  have hA_delta_bdd' : IsBounded (discretizeSet δ A) := discretizeSet_bounded hδ_pos hA_bdd'
  have hA_delta_bdd : IsBounded (productLikeRealLineCopy (discretizeSet δ A)) :=
    realLineCopy_bounded_iff.mpr hA_delta_bdd'
  have hA_delta_nonempty' : (discretizeSet δ A).Nonempty :=
    hA_nonempty'.mono (subset_discretizeSet hδ_pos)
  have hA_delta_nonempty : (productLikeRealLineCopy (discretizeSet δ A)).Nonempty :=
    realLineCopy_nonempty_iff.mpr hA_delta_nonempty'
  refine' ⟨hA_delta_bdd, hA_delta_nonempty, h_d1, hδ_dyadic, hδ_pos, hκ_nonneg, hκ_le_one, by positivity, _⟩
  intro r Q hr_dyadic hQ_dyadic hδ_le_r hr_le_one
  rcases hQ_dyadic with ⟨k_fn, hQ⟩
  let m : ℤ := k_fn 0
  have h_k_fn : k_fn = fun (_ : Fin 1) => m := by
    funext i
    fin_cases i <;> rfl
  have hQ_eq : Q = dyadicCube r (fun (_ : Fin 1) => m) := by
    rw [hQ, h_k_fn]
  rw [hQ_eq]
  have hr_pos : 0 < r := by linarith
  set enlarged : Set ℝ := Set.Ico (r * (m : ℝ) - δ) (r * ((m : ℝ) + 1) + δ) with henlarged
  let idxL := cubeIndexSet δ (A ∩ realDyadicCube r (m - 1))
  let idxM := cubeIndexSet δ (A ∩ realDyadicCube r m)
  let idxR := cubeIndexSet δ (A ∩ realDyadicCube r (m + 1))
  let X := ENNReal.ofReal C * ENat.toENNReal (cubeIndexSet δ A).encard * ENNReal.ofReal (r ^ κ)
  have h_main1 : productLikeRealLineCopy (discretizeSet δ A) ∩ dyadicCube r (fun (_ : Fin 1) => m) =
      productLikeRealLineCopy ((discretizeSet δ A) ∩ realDyadicCube r m) := by
    rw [euclidean_cube_eq_real, lineCopy_inter]
  have h_idx_contain : cubeIndexSet δ ((discretizeSet δ A) ∩ realDyadicCube r m) ⊆
      cubeIndexSet δ (A ∩ enlarged) :=
    transfer_key_containment hδ_pos hr_pos hδ_le_r
  have h_idx_union : cubeIndexSet δ (A ∩ enlarged) ⊆ idxL ∪ idxM ∪ idxR := by
    intro k hk
    simp only [cubeIndexSet, Set.mem_setOf_eq] at hk
    rcases hk with ⟨x, hxIco, ⟨hxA, hxE⟩⟩
    have h_xinE' : x ∈ Set.Ico (r * (m : ℝ) - δ) (r * ((m : ℝ) + 1) + δ) := by
      rw [←henlarged]
      exact hxE
    have h1 : r * (m : ℝ) - δ ≤ x := h_xinE'.1
    have h2 : x < r * ((m : ℝ) + 1) + δ := h_xinE'.2
    have h3 : r * ((m : ℝ) - 1) ≤ x := by linarith
    have h4 : x < r * ((m : ℝ) + 2) := by linarith
    by_cases h8 : x < r * (m : ℝ)
    · have h_left : x ∈ realDyadicCube r (m - 1) := by
        simpa [realDyadicCube, Int.cast_sub] using ⟨h3, h8⟩
      have h_goalL : k ∈ idxL := by
        exact ⟨x, hxIco, ⟨hxA, h_left⟩⟩
      exact Or.inl (Or.inl h_goalL)
    · by_cases h9 : x < r * ((m : ℝ) + 1)
      · have h_mid : x ∈ realDyadicCube r m := by
          simpa [realDyadicCube] using ⟨by linarith, h9⟩
        have h_goalM : k ∈ idxM := by
          exact ⟨x, hxIco, ⟨hxA, h_mid⟩⟩
        exact Or.inl (Or.inr h_goalM)
      · have h9' : r * ((m : ℝ) + 1) ≤ x := by linarith
        have h_lower : r * (((m + 1 : ℤ) : ℝ)) ≤ x := by
          have h_eq : r * ((m + 1 : ℤ) : ℝ) = r * ((m : ℝ) + 1) := by norm_cast <;> ring
          rw [h_eq]; exact h9'
        have h_upper : x < r * (((m + 1 : ℤ) : ℝ) + 1) := by
          have h_eq : r * (((m + 1 : ℤ) : ℝ) + 1) = r * ((m : ℝ) + 2) := by norm_cast <;> ring_nf
          rw [h_eq]; exact h4
        have h_right : x ∈ realDyadicCube r (m + 1) := ⟨h_lower, h_upper⟩
        have h_goalR : k ∈ idxR := by
          exact ⟨x, hxIco, ⟨hxA, h_right⟩⟩
        exact Or.inr h_goalR
  have h_cube_finite : Set.Finite (cubeIndexSet δ A) := cubeIndexSet_finite hδ_pos hA_bdd'
  have h_subL : idxL ⊆ cubeIndexSet δ A := by
    have h : (A ∩ realDyadicCube r (m - 1)) ⊆ A := by intro z hz; exact hz.1
    exact cubeIndexSet_mono h
  have h_subM : idxM ⊆ cubeIndexSet δ A := by
    have h : (A ∩ realDyadicCube r m) ⊆ A := by intro z hz; exact hz.1
    exact cubeIndexSet_mono h
  have h_subR : idxR ⊆ cubeIndexSet δ A := by
    have h : (A ∩ realDyadicCube r (m + 1)) ⊆ A := by intro z hz; exact hz.1
    exact cubeIndexSet_mono h
  have h_finL : Set.Finite idxL := Finite.subset h_cube_finite h_subL
  have h_finM : Set.Finite idxM := Finite.subset h_cube_finite h_subM
  have h_finR : Set.Finite idxR := Finite.subset h_cube_finite h_subR
  have h_encard_union : ENat.toENNReal (idxL ∪ idxM ∪ idxR).encard ≤
      ENat.toENNReal idxL.encard + ENat.toENNReal idxM.encard + ENat.toENNReal idxR.encard := by
    have h1 : (idxL ∪ idxM).encard ≤ idxL.encard + idxM.encard :=
      encard_union_le idxL idxM
    have h2 : ((idxL ∪ idxM) ∪ idxR).encard ≤ (idxL ∪ idxM).encard + idxR.encard :=
      encard_union_le (idxL ∪ idxM) idxR
    have h_union : (idxL ∪ idxM ∪ idxR).encard ≤ idxL.encard + idxM.encard + idxR.encard := by
      calc (idxL ∪ idxM ∪ idxR).encard
        = ((idxL ∪ idxM) ∪ idxR).encard := by rfl
      _ ≤ (idxL ∪ idxM).encard + idxR.encard := h2
      _ ≤ idxL.encard + idxM.encard + idxR.encard := by
        exact add_le_add h1 le_rfl
    exact_mod_cast h_union
  have h_covA : dyadicCoveringNumber δ (productLikeRealLineCopy A) = (cubeIndexSet δ A).encard :=
    coveringNumber_eq_cubeIndexSet hδ_pos
  have h_boundL : ENat.toENNReal idxL.encard ≤ X := by
    have hQ' : (dyadicCube r (fun (_ : Fin 1) => m - 1)) ∈ dyadicCubes 1 r := ⟨_, rfl⟩
    have h := hA_bound hr_dyadic hQ' hδ_le_r hr_le_one
    have h_int : productLikeRealLineCopy A ∩ dyadicCube r (fun (_ : Fin 1) => m - 1) =
        productLikeRealLineCopy (A ∩ realDyadicCube r (m - 1)) := by
      rw [euclidean_cube_eq_real, lineCopy_inter]
    rw [h_int] at h
    have h_cov : dyadicCoveringNumber δ (productLikeRealLineCopy (A ∩ realDyadicCube r (m - 1))) = idxL.encard :=
      coveringNumber_eq_cubeIndexSet hδ_pos
    rw [h_cov, h_covA] at h
    exact h
  have h_boundM : ENat.toENNReal idxM.encard ≤ X := by
    have hQ' : (dyadicCube r (fun (_ : Fin 1) => m)) ∈ dyadicCubes 1 r := ⟨_, rfl⟩
    have h := hA_bound hr_dyadic hQ' hδ_le_r hr_le_one
    have h_int : productLikeRealLineCopy A ∩ dyadicCube r (fun (_ : Fin 1) => m) =
        productLikeRealLineCopy (A ∩ realDyadicCube r m) := by
      rw [euclidean_cube_eq_real, lineCopy_inter]
    rw [h_int] at h
    have h_cov : dyadicCoveringNumber δ (productLikeRealLineCopy (A ∩ realDyadicCube r m)) = idxM.encard :=
      coveringNumber_eq_cubeIndexSet hδ_pos
    rw [h_cov, h_covA] at h
    exact h
  have h_boundR : ENat.toENNReal idxR.encard ≤ X := by
    have hQ' : (dyadicCube r (fun (_ : Fin 1) => m + 1)) ∈ dyadicCubes 1 r := ⟨_, rfl⟩
    have h := hA_bound hr_dyadic hQ' hδ_le_r hr_le_one
    have h_int : productLikeRealLineCopy A ∩ dyadicCube r (fun (_ : Fin 1) => m + 1) =
        productLikeRealLineCopy (A ∩ realDyadicCube r (m + 1)) := by
      rw [euclidean_cube_eq_real, lineCopy_inter]
    rw [h_int] at h
    have h_cov : dyadicCoveringNumber δ (productLikeRealLineCopy (A ∩ realDyadicCube r (m + 1))) = idxR.encard :=
      coveringNumber_eq_cubeIndexSet hδ_pos
    rw [h_cov, h_covA] at h
    exact h
  have h_sum : ENat.toENNReal idxL.encard + ENat.toENNReal idxM.encard + ENat.toENNReal idxR.encard ≤ 3 * X := by
    calc ENat.toENNReal idxL.encard + ENat.toENNReal idxM.encard + ENat.toENNReal idxR.encard
      ≤ X + X + X := by gcongr <;> linarith
    _ = 3 * X := by ring
  have h_final : ENat.toENNReal (cubeIndexSet δ ((discretizeSet δ A) ∩ realDyadicCube r m)).encard ≤ 3 * X := by
    calc ENat.toENNReal (cubeIndexSet δ ((discretizeSet δ A) ∩ realDyadicCube r m)).encard
      ≤ ENat.toENNReal (cubeIndexSet δ (A ∩ enlarged)).encard :=
        ENat.toENNReal_mono (Set.encard_mono h_idx_contain)
    _ ≤ ENat.toENNReal (idxL ∪ idxM ∪ idxR).encard :=
        ENat.toENNReal_mono (Set.encard_mono h_idx_union)
    _ ≤ ENat.toENNReal idxL.encard + ENat.toENNReal idxM.encard + ENat.toENNReal idxR.encard := h_encard_union
    _ ≤ 3 * X := h_sum
  have h_goal : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (discretizeSet δ A) ∩ dyadicCube r (fun (_ : Fin 1) => m))) ≤
      ENNReal.ofReal (3 * C) * ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (discretizeSet δ A))) * ENNReal.ofReal (r ^ κ) := by
    rw [h_main1]
    have h_cov1 : dyadicCoveringNumber δ (productLikeRealLineCopy ((discretizeSet δ A) ∩ realDyadicCube r m)) =
        (cubeIndexSet δ ((discretizeSet δ A) ∩ realDyadicCube r m)).encard :=
      coveringNumber_eq_cubeIndexSet hδ_pos
    have h_cov2 : dyadicCoveringNumber δ (productLikeRealLineCopy (discretizeSet δ A)) =
        (cubeIndexSet δ (discretizeSet δ A)).encard := coveringNumber_eq_cubeIndexSet hδ_pos
    have h_cov3 : (cubeIndexSet δ (discretizeSet δ A)).encard = (cubeIndexSet δ A).encard :=
      congr_arg Set.encard (coveringNumber_discretizeSet hδ_pos)
    rw [h_cov1, h_cov2, h_cov3]
    have h_final2 : 3 * X = ENNReal.ofReal (3 * C) * ENat.toENNReal (cubeIndexSet δ A).encard * ENNReal.ofReal (r ^ κ) := by
      simp [X, mul_assoc] <;> ring
    rw [←h_final2]
    exact h_final
  exact h_goal

end SetDiscretizationBridge
