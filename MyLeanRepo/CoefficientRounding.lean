module

/-
# Coefficient Rounding Lemma

If x and x' are within δ of each other, and A ⊆ [1,2], then the
δ-covering numbers of A + x·A and A + x'·A are comparable up to an
absolute constant factor (5).

## Main result

`coefficient_rounding`: `Nreal δ (A + x'·A) ≤ 5 * Nreal δ (A + x·A)`
when `|x - x'| ≤ δ` and `A ⊆ [1,2]`.
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeSetBasics
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set ENNReal Classical Bornology

namespace ProductLikeIncidence

/-- Construct a 1D EuclideanSpace point from a real number. -/
def mk1 (r : ℝ) : EuclideanSpace ℝ (Fin 1) :=
  (WithLp.equiv 2 (Fin 1 → ℝ)).symm fun (_ : Fin 1) => r

/-- Index set of δ-dyadic intervals meeting a real set S. -/
def cubeIndexSet (δ : ℝ) (S : Set ℝ) : Set ℤ :=
  {k | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ S).Nonempty}

/-- The δ-covering number of a real set equals the encard of its cube index set. -/
lemma coveringNumber_eq_cubeIndexSet {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ} :
    dyadicCoveringNumber δ (productLikeRealLineCopy S) = (cubeIndexSet δ S).encard := by
  let f : ℤ → Set (EuclideanSpace ℝ (Fin 1)) :=
    fun k => dyadicCube δ (fun (_ : Fin 1) => k)
  have h1 : dyadicCubesMeeting δ (productLikeRealLineCopy S) = f '' (cubeIndexSet δ S) := by
    ext Q
    simp only [dyadicCubesMeeting, Set.mem_setOf_eq, Set.mem_image, cubeIndexSet]
    constructor
    · rintro ⟨hQ_dyadic, ⟨x, hxQ, hxS⟩⟩
      rcases hQ_dyadic with ⟨k_fn, hk_eq⟩
      let k : ℤ := k_fn 0
      have h_k_fn : k_fn = fun (_ : Fin 1) => k := by
        funext i
        fin_cases i <;> rfl
      rw [h_k_fn] at hk_eq
      have h_k_in : k ∈ cubeIndexSet δ S := by
        simp only [cubeIndexSet, Set.mem_setOf_eq]
        refine ⟨x 0, ?_, hxS⟩
        rw [hk_eq] at hxQ
        exact hxQ 0
      exact ⟨k, h_k_in, hk_eq.symm⟩
    · rintro ⟨k, hk, rfl⟩
      have hQ_dyadic : f k ∈ dyadicCubes 1 δ := ⟨_, rfl⟩
      rcases hk with ⟨p, hpI, hpS⟩
      let x : EuclideanSpace ℝ (Fin 1) := mk1 p
      have hxQ : x ∈ f k := by
        simp only [f, dyadicCube, Set.mem_setOf_eq, x, mk1]
        intro i
        fin_cases i
        simpa using hpI
      have hxS : x ∈ productLikeRealLineCopy S := by
        simp only [productLikeRealLineCopy]
        exact hpS
      exact ⟨hQ_dyadic, ⟨x, hxQ, hxS⟩⟩
  have h_inj : Function.Injective f := by
    intro k1 k2 h
    let p : EuclideanSpace ℝ (Fin 1) := mk1 (δ * (k1 : ℝ))
    have h_p1 : p ∈ f k1 := by
      simp only [f, dyadicCube, Set.mem_setOf_eq]
      intro i
      have h_pi : p i = δ * (k1 : ℝ) := by
        simp [p, mk1] <;> rfl
      rw [h_pi]
      exact ⟨by linarith, by linarith⟩
    rw [h] at h_p1
    have h_p2 : p ∈ f k2 := h_p1
    simp only [f, dyadicCube, Set.mem_setOf_eq, p, mk1] at h_p2
    have h3 := h_p2 0
    simp at h3
    have h4 : (k2 : ℝ) ≤ (k1 : ℝ) := by
      have h41 : δ * (k2 : ℝ) ≤ δ * (k1 : ℝ) := h3.1
      nlinarith
    have h5 : (k1 : ℝ) < (k2 : ℝ) + 1 := by
      have h51 : δ * (k1 : ℝ) < δ * ((k2 : ℝ) + 1) := h3.2
      nlinarith
    have h6 : k1 ≥ k2 := by exact_mod_cast h4
    have h7 : k1 ≤ k2 := by
      by_contra h8
      have h9 : k1 ≥ k2 + 1 := by omega
      have h10 : (k1 : ℝ) ≥ (k2 : ℝ) + 1 := by exact_mod_cast h9
      linarith
    omega
  rw [dyadicCoveringNumber, h1]
  rw [Function.Injective.encard_image h_inj]
  <;> rfl

/-- If S' is pointwise within 2δ of S, then the δ-covering number of S' is
at most 5 times that of S. -/
lemma thickening_covering_factor5 {δ : ℝ} (hδ : 0 < δ)
    {S S' : Set ℝ} (hS_bdd : IsBounded S)
    (h_close : ∀ p ∈ S', ∃ q ∈ S, |p - q| ≤ 2 * δ) :
    dyadicCoveringNumber δ (productLikeRealLineCopy S') ≤
      5 * dyadicCoveringNumber δ (productLikeRealLineCopy S) := by
  by_cases hS_empty : S = ∅
  · -- S empty implies S' empty
    have hS'_empty : S' = ∅ := by
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
    have hS_bdd' : ∃ (M : ℝ), ∀ (x : ℝ), x ∈ S → ∀ (y : ℝ), y ∈ S → dist x y ≤ M :=
      Metric.isBounded_iff.mp hS_bdd
    rcases hS_bdd' with ⟨M, hM⟩
    have hM' : ∀ x ∈ S, |x| ≤ M + |a0| := by
      intro x hx
      have h1 : dist x a0 ≤ M := hM x hx a0 ha0
      have h2 : |x - a0| ≤ M := by simpa [Real.dist_eq] using h1
      have h_tri : |x| ≤ |x - a0| + |a0| := by
        have h : |(x - a0) + a0| ≤ |x - a0| + |a0| := abs_add_le (x - a0) a0
        have h_eq : (x - a0) + a0 = x := by ring
        rw [h_eq] at h
        exact h
      calc |x| ≤ |x - a0| + |a0| := h_tri
        _ ≤ M + |a0| := by linarith
    let R := M + |a0|
    have h_idxS_finite : Set.Finite idxS := by
      have h1 : ∀ k ∈ idxS, -R / δ - 2 ≤ (k : ℝ) ∧ (k : ℝ) ≤ R / δ + 1 := by
        intro k hk
        rcases hk with ⟨p, ⟨hp1, hp2⟩, hpS⟩
        have h_p_bdd : |p| ≤ R := hM' p hpS
        have h2 : -R ≤ p := (abs_le.mp h_p_bdd).1
        have h3 : p ≤ R := (abs_le.mp h_p_bdd).2
        constructor
        · -- Lower bound: -R/δ - 2 ≤ k
          have h4 : -R < δ * ((k : ℝ) + 1) := by linarith
          have h5 : -R / δ < (k : ℝ) + 1 := by
            have h6 : (-R) / δ < (δ * ((k : ℝ) + 1)) / δ := by
              apply div_lt_div_of_pos_right h4 hδ
            simpa [hδ.ne'] using h6
          linarith
        · -- Upper bound: k ≤ R/δ + 1
          have h4 : δ * (k : ℝ) ≤ R := by linarith
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
    have h_main : idxS' ⊆ ⋃ m ∈ idxS, (Finset.Icc (m - 2) (m + 2) : Set ℤ) := by
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
      have h_k_le_m2 : k ≤ m + 2 := by
        have h : p - q ≤ 2 * δ := by
          have h' : |p - q| ≤ 2 * δ := hdist
          exact (abs_le.mp h').2
        have h'' : p < δ * ((m : ℝ) + 3) := by linarith
        have h4 : (k : ℝ) < (m : ℝ) + 3 := by nlinarith
        have h5 : k < m + 3 := by exact_mod_cast h4
        omega
      have h_k_ge_m2 : m - 2 ≤ k := by
        have h : q - p ≤ 2 * δ := by
          have h' : |p - q| ≤ 2 * δ := hdist
          have h'' : |q - p| ≤ 2 * δ := by
            rw [show q - p = -(p - q) by ring]
            rw [abs_neg] <;> exact h'
          exact (abs_le.mp h'').2
        have h'' : q < δ * ((k : ℝ) + 3) := by linarith
        have h4 : (m : ℝ) < (k : ℝ) + 3 := by nlinarith
        have h5 : m < k + 3 := by exact_mod_cast h4
        omega
      have h_k_range : k ∈ (Finset.Icc (m - 2) (m + 2) : Set ℤ) := by
        simp only [Finset.mem_Icc, Finset.mem_coe]
        exact ⟨h_k_ge_m2, h_k_le_m2⟩
      exact Set.mem_iUnion₂.mpr ⟨m, hm_in_idxS, h_k_range⟩
    have h5 : (idxS').encard ≤ (⋃ m ∈ idxS, (Finset.Icc (m - 2) (m + 2) : Set ℤ)).encard :=
      Set.encard_mono h_main
    have h6 : (⋃ m ∈ idxS, (Finset.Icc (m - 2) (m + 2) : Set ℤ)).encard ≤
        5 * idxS.encard := by
      let idxS_fin : Finset ℤ := h_idxS_finite.toFinset
      let U : Finset ℤ := idxS_fin.biUnion (fun m => Finset.Icc (m - 2) (m + 2))
      have hU : (U : Set ℤ) = (⋃ m ∈ idxS, (Finset.Icc (m - 2) (m + 2) : Set ℤ)) := by
        ext z
        simp [U, idxS_fin, Set.Finite.mem_toFinset]
        <;> aesop
      have h7 : Set.Finite (⋃ m ∈ idxS, (Finset.Icc (m - 2) (m + 2) : Set ℤ)) := by
        rw [← hU]
        exact U.finite_toSet
      have h8 : U.card ≤ ∑ m ∈ idxS_fin, (Finset.Icc (m - 2) (m + 2)).card :=
        Finset.card_biUnion_le
      have h9 : ∀ m : ℤ, (Finset.Icc (m - 2) (m + 2)).card = 5 := by
        intro m
        simp [Finset.Icc_eq_empty_of_lt]
        <;> omega
      have h10 : U.card ≤ 5 * idxS_fin.card := by
        calc U.card
          ≤ ∑ m ∈ idxS_fin, (Finset.Icc (m - 2) (m + 2)).card := h8
        _ = ∑ m ∈ idxS_fin, 5 := by
          apply Finset.sum_congr rfl
          intro m _
          exact h9 m
        _ = 5 * idxS_fin.card := by
          rw [Finset.sum_const] <;> ring
      have h13 : (⋃ m ∈ idxS, (Finset.Icc (m - 2) (m + 2) : Set ℤ)).encard = ↑U.card := by
        have h_eq : (⋃ m ∈ idxS, (Finset.Icc (m - 2) (m + 2) : Set ℤ)) = (U : Set ℤ) := hU.symm
        rw [h_eq]
        simp
      have h14 : idxS.encard = ↑idxS_fin.card := by
        have h_eq : idxS = (idxS_fin : Set ℤ) := by
          ext y
          simp [idxS_fin, Set.Finite.mem_toFinset]
          <;> tauto
        rw [h_eq]
        simp
      rw [h13, h14]
      exact_mod_cast h10
    have h10 : (idxS').encard ≤ 5 * idxS.encard := le_trans h5 h6
    have h11 : dyadicCoveringNumber δ (productLikeRealLineCopy S') = (idxS').encard :=
      coveringNumber_eq_cubeIndexSet hδ
    have h12 : dyadicCoveringNumber δ (productLikeRealLineCopy S) = (idxS).encard :=
      coveringNumber_eq_cubeIndexSet hδ
    rw [h11, h12]
    exact h10

/-- **Coefficient rounding lemma.**

If `A ⊆ [1,2]` and `|x - x'| ≤ δ`, then the δ-covering number of
`A + x'·A` is at most 5 times that of `A + x·A`.

This allows rounding a coefficient `x'` from the thickened measure support
back to a grid coefficient `x` while losing only an absolute factor. -/
lemma coefficient_rounding {δ : ℝ} (hδ : 0 < δ)
    {A : Set ℝ} (hA : A ⊆ Set.Icc 1 2)
    {x x' : ℝ} (h_close : |x - x'| ≤ δ) :
    dyadicCoveringNumber δ (productLikeRealLineCopy
      (Set.image2 (fun a b => a + x' * b) A A)) ≤
    5 * dyadicCoveringNumber δ (productLikeRealLineCopy
      (Set.image2 (fun a b => a + x * b) A A)) := by
  let S := Set.image2 (fun a b => a + x * b) A A
  let S' := Set.image2 (fun a b => a + x' * b) A A
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
      have h_tri : |a + x * b| ≤ |a| + |x * b| := by
        have h5 : -( |a| + |x * b|) ≤ a + x * b := by
          have h51 : -|a| ≤ a := neg_abs_le a
          have h52 : -|x * b| ≤ x * b := neg_abs_le (x * b)
          linarith
        have h6 : a + x * b ≤ |a| + |x * b| := by
          have h61 : a ≤ |a| := le_abs_self a
          have h62 : x * b ≤ |x * b| := le_abs_self (x * b)
          linarith
        exact abs_le.mpr ⟨h5, h6⟩
      have h_abs : |a + x * b| ≤ B := by
        calc |a + x * b|
          ≤ |a| + |x * b| := h_tri
        _ = |a| + |x| * |b| := by rw [abs_mul]
        _ ≤ 2 + |x| * 2 := by
          have h3 : |x| * |b| ≤ |x| * 2 := by gcongr <;> linarith
          linarith
        _ = B := by simp [B] <;> ring
      have h_lower : -B ≤ a + x * b := by linarith [abs_le.mp h_abs]
      have h_upper : a + x * b ≤ B := by linarith [abs_le.mp h_abs]
      exact ⟨h_lower, h_upper⟩
    have h2 : IsBounded (Set.Icc (-B) B) := Metric.isBounded_Icc (-B) B
    exact IsBounded.subset h2 h1
  have h_close' : ∀ p ∈ S', ∃ q ∈ S, |p - q| ≤ 2 * δ := by
    intro p hp
    rcases hp with ⟨a, ha, b, hb, rfl⟩
    refine ⟨a + x * b, ⟨a, ha, b, hb, rfl⟩, ?_⟩
    have h1 : |(a + x' * b) - (a + x * b)| = |x' - x| * |b| := by
      have h2 : (a + x' * b) - (a + x * b) = (x' - x) * b := by ring
      rw [h2, abs_mul]
    rw [h1]
    have h3 : 1 ≤ b := (hA hb).1
    have h4 : b ≤ 2 := (hA hb).2
    have h5 : |b| = b := abs_of_pos (by linarith)
    rw [h5]
    have h_abs : |x' - x| ≤ δ := by
      rw [abs_sub_comm]
      exact h_close
    have h6 : |x' - x| * b ≤ 2 * δ := by
      calc |x' - x| * b
          ≤ δ * b := mul_le_mul_of_nonneg_right h_abs (by linarith)
        _ ≤ δ * 2 := by gcongr <;> linarith
        _ = 2 * δ := by ring
    exact h6
  exact thickening_covering_factor5 hδ hS_bdd h_close'

/-- Version using `Nreal`. -/
lemma coefficient_rounding_Nreal {δ : ℝ} (hδ : 0 < δ)
    {A : Set ℝ} (hA : A ⊆ Set.Icc 1 2)
    {x x' : ℝ} (h_close : |x - x'| ≤ δ) :
    Nreal δ (Set.image2 (fun a b => a + x' * b) A A) ≤
    5 * Nreal δ (Set.image2 (fun a b => a + x * b) A A) := by
  have h := coefficient_rounding hδ hA h_close
  have h' : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (fun a b => a + x' * b) A A))) ≤
      ENat.toENNReal (5 * dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (fun a b => a + x * b) A A))) :=
    ENat.toENNReal_mono h
  have h_mul : ENat.toENNReal (5 * dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (fun a b => a + x * b) A A))) =
      5 * ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (fun a b => a + x * b) A A))) := by
    simp [mul_comm]
    <;> rfl
  rw [h_mul] at h'
  simpa [Nreal] using h'

end ProductLikeIncidence
