module

/-
# Covering Number ↔ Measure Translation (SUPPORT FOR STEP 3-5)

Correct statements for the arbitrary-dimensional Marstrand extraction.

## Key finding

Paper's measure bound `|x₁A + ... + x_mA| ≳ δ^(εm)` translates to
`Nδ(x₁A + ... + x_mA) ≳ δ^(-1+εm)`, NOT `δ^(εm)`.

Reason: each δ-dyadic cube in 1D has volume δ, so
`volume(S) ≤ Nδ(S) · δ`, hence `Nδ(S) ≥ volume(S) / δ`.

## Paper reference

simpleBourgain.tex lines 594-605.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.DiscretizedPluennecke
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Classical

namespace WeakTwoEndsSumProduct

/-- **Covering number lower bound from measure**.

For any bounded set S ⊂ ℝ, `volume(S) ≤ δ · Nδ(S)`.

This is the key translation: the paper's Lebesgue measure bound
`|Σ x_iA| ≳ δ^(εm)` becomes `Nδ(Σ x_iA) ≳ δ^(-1+εm)`. -/
lemma covering_number_ge_measure_div_delta {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS_bdd : Bornology.IsBounded S) :
    volume S ≤ ENNReal.ofReal δ * Nreal δ S := by
  let I : ℤ → Set ℝ := fun k => Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1))
  let K : Set ℤ := ProductLikeIncidence.realCubeIndexSet δ S

  -- Intervals I(k) for k ∈ K cover S
  have h_cover : S ⊆ ⋃ k ∈ K, I k := by
    intro x hx
    let k : ℤ := ⌊x / δ⌋
    have h4 : δ * (k : ℝ) ≤ x := by
      have h5 : (k : ℝ) ≤ x / δ := Int.floor_le (x / δ)
      have h6 : δ * (k : ℝ) ≤ δ * (x / δ) := by gcongr
      have h7 : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
      linarith
    have h7 : x < δ * ((k : ℝ) + 1) := by
      have h8 : x / δ < (k : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
      have h9 : δ * (x / δ) < δ * ((k : ℝ) + 1) := by gcongr
      have h10 : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
      linarith
    have hk_in_I : x ∈ I k := ⟨h4, h7⟩
    have h_k_in_K : k ∈ K := by
      simp only [K, ProductLikeIncidence.realCubeIndexSet]
      exact ⟨x, hk_in_I, hx⟩
    exact Set.mem_iUnion₂.mpr ⟨k, h_k_in_K, hk_in_I⟩

  -- K is finite (hence countable)
  have hK_finite : K.Finite := ProductLikeIncidence.realCubeIndexSet_finite hδ hS_bdd
  have hK_count : Set.Countable K := hK_finite.countable

  -- Each interval is measurable and has volume δ
  have h_meas : ∀ k ∈ K, MeasurableSet (I k) := by
    intro k _
    exact measurableSet_Ico
  have h_vol : ∀ k ∈ K, volume (I k) = ENNReal.ofReal δ := by
    intro k _
    rw [Real.volume_Ico]
    have h : δ * ((k : ℝ) + 1) - δ * (k : ℝ) = δ := by ring
    rw [h]

  -- Countable subadditivity
  have h_subadd : volume (⋃ k ∈ K, I k) ≤ ∑' (p : {k // k ∈ K}), volume (I p) :=
    measure_biUnion_le volume hK_count I

  have h_tsum : ∑' (p : {k // k ∈ K}), volume (I p) =
      (ENat.card {k // k ∈ K} : ENNReal) * ENNReal.ofReal δ := by
    have h3 : ∑' (p : {k // k ∈ K}), volume (I p) = ∑' (p : {k // k ∈ K}), ENNReal.ofReal δ := by
      apply tsum_congr
      intro p
      exact h_vol p p.prop
    rw [h3]
    exact ENNReal.tsum_const (ENNReal.ofReal δ)

  have h_encard_eq : (ENat.card {k // k ∈ K} : ENNReal) = (K.encard : ENNReal) := by
    have h : ENat.card {k // k ∈ K} = K.encard := ENat.card_coe_set_eq K
    rw [h]

  have h_main : ∑' (p : {k // k ∈ K}), volume (I p) = (K.encard : ENNReal) * ENNReal.ofReal δ := by
    rw [h_tsum, h_encard_eq]

  have h5 : volume S ≤ volume (⋃ k ∈ K, I k) := measure_mono h_cover

  have h7 : volume S ≤ (K.encard : ENNReal) * ENNReal.ofReal δ := by
    calc volume S
      ≤ volume (⋃ k ∈ K, I k) := h5
    _ ≤ ∑' (p : {k // k ∈ K}), volume (I p) := h_subadd
    _ = (K.encard : ENNReal) * ENNReal.ofReal δ := h_main

  -- Relate K.encard to Nreal δ S using existing lemma
  have h_line_eq : realLineCopy S = productLikeRealLineCopy S := by
    ext x
    simp [realLineCopy, productLikeRealLineCopy]
  have h_card : Nreal δ S = (K.encard : ENNReal) := by
    have h10 : Nreal δ S = ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (realLineCopy S)) := by rfl
    rw [h10, h_line_eq]
    have h11 : dyadicCoveringNumber (d := 1) δ (productLikeRealLineCopy S) = K.encard :=
      ProductLikeIncidence.realCoveringNumber_eq_card hδ hS_bdd
    exact congr_arg ENat.toENNReal h11

  have h_comm : (K.encard : ENNReal) * ENNReal.ofReal δ = ENNReal.ofReal δ * Nreal δ S := by
    rw [h_card]
    <;> exact mul_comm _ _
  rw [h_comm] at h7
  exact h7

/-- **Corollary: measure lower bound → covering lower bound**.

If `volume(S) ≥ c · δ^α` with `c ≥ 0`, then
`Nδ(S) ≥ c · δ^(α-1)`.

Set `α = εm` to get `Nδ(Σ x_iA) ≥ c · δ^(-1+εm)`. -/
lemma measure_lower_to_covering_lower {δ c α : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c)
    {S : Set ℝ} (hS_bdd : Bornology.IsBounded S)
    (h_vol : ENNReal.ofReal c * ENNReal.ofReal (δ ^ α) ≤ volume S) :
    ENNReal.ofReal c * ENNReal.ofReal (δ ^ (α - 1)) ≤ Nreal δ S := by
  have h1 : volume S ≤ ENNReal.ofReal δ * Nreal δ S :=
    covering_number_ge_measure_div_delta hδ hS_bdd
  have h2 : ENNReal.ofReal c * ENNReal.ofReal (δ ^ α) ≤
      ENNReal.ofReal δ * Nreal δ S := le_trans h_vol h1
  have h4 : δ ^ α = δ * δ ^ (α - 1) := by
    have h41 : α = 1 + (α - 1) := by ring
    rw [h41]
    rw [Real.rpow_add hδ]
    <;> simp
  have h51 : ENNReal.ofReal δ * ENNReal.ofReal (δ ^ (α - 1)) =
      ENNReal.ofReal (δ * δ ^ (α - 1)) := by
    rw [ENNReal.ofReal_mul (by positivity)] <;> rfl
  have h5 : ENNReal.ofReal δ * (ENNReal.ofReal c * ENNReal.ofReal (δ ^ (α - 1))) =
      ENNReal.ofReal c * ENNReal.ofReal (δ ^ α) := by
    have h52 : ENNReal.ofReal δ * (ENNReal.ofReal c * ENNReal.ofReal (δ ^ (α - 1))) =
        ENNReal.ofReal c * (ENNReal.ofReal δ * ENNReal.ofReal (δ ^ (α - 1))) := by
      simp [mul_left_comm]
    rw [h52, h51, h4]
  have hδ_ne_zero : ENNReal.ofReal δ ≠ 0 := by positivity
  have hδ_ne_top : ENNReal.ofReal δ ≠ ⊤ := ENNReal.ofReal_ne_top
  have h7 : ENNReal.ofReal δ * (ENNReal.ofReal c * ENNReal.ofReal (δ ^ (α - 1))) ≤
      ENNReal.ofReal δ * Nreal δ S := by
    rw [h5] <;> exact h2
  have h10 : (ENNReal.ofReal c * ENNReal.ofReal (δ ^ (α - 1))) ≤ Nreal δ S :=
    (ENNReal.mul_le_mul_iff_right hδ_ne_zero hδ_ne_top).mp h7
  exact h10

/-- **Volume of δ-neighborhood ≤ 3δ · Nδ(S)**.

For any S ⊂ ℝ, the open δ-neighborhood `{t | ∃ x ∈ S, |t - x| < δ}` has
Lebesgue measure at most `3δ · Nδ(S)`.

This is the key lemma for extracting covering-number lower bounds from
Marstrand's projection theorem: the projection's δ-neighborhood has large
volume, hence the projection itself has large covering number. -/
lemma neighborhood_volume_le_covering {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ} :
    volume {t | ∃ x ∈ S, |t - x| < δ} ≤ 3 * ENNReal.ofReal δ * Nreal δ S := by
  let I : ℤ → Set ℝ := fun k => Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1))
  let K : Set ℤ := {k | (I k ∩ S).Nonempty}
  let J : ℤ → Set ℝ := fun k => Set.Ico (δ * ((k : ℝ) - 1)) (δ * ((k : ℝ) + 2))

  -- δ-neighborhood ⊆ ⋃_{k ∈ K} J k
  have h_contain : {t | ∃ x ∈ S, |t - x| < δ} ⊆ ⋃ k ∈ K, J k := by
    intro t ht
    rcases ht with ⟨x, hxS, hxt⟩
    let k : ℤ := ⌊x / δ⌋
    have hxI : x ∈ I k := by
      have h1 : δ * (k : ℝ) ≤ x := by
        have h2 : (k : ℝ) ≤ x / δ := Int.floor_le (x / δ)
        have h3 : δ * (k : ℝ) ≤ δ * (x / δ) := by gcongr
        have h4 : δ * (x / δ) = x := by field_simp [hδ.ne']
        linarith
      have h5 : x < δ * ((k : ℝ) + 1) := by
        have h6 : x / δ < (k : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
        have h7 : δ * (x / δ) < δ * ((k : ℝ) + 1) := by gcongr
        have h8 : δ * (x / δ) = x := by field_simp [hδ.ne']
        linarith
      exact ⟨h1, h5⟩
    have hk : k ∈ K := by
      simp only [K, Set.mem_setOf_eq]
      exact ⟨x, hxI, hxS⟩
    have h_tJ : t ∈ J k := by
      simp only [J, Set.mem_Ico]
      have h9 : δ * ((k : ℝ) - 1) ≤ t := by linarith [abs_lt.mp hxt, hxI.1]
      have h10 : t < δ * ((k : ℝ) + 2) := by linarith [abs_lt.mp hxt, hxI.2]
      exact ⟨h9, h10⟩
    exact Set.mem_iUnion₂.mpr ⟨k, hk, h_tJ⟩

  have hK_count : Set.Countable K :=
    Set.Countable.mono (show K ⊆ (Set.univ : Set ℤ) from fun _ _ => trivial) Set.countable_univ

  have h_vol_J : ∀ k : ℤ, volume (J k) = 3 * ENNReal.ofReal δ := by
    intro k
    rw [Real.volume_Ico]
    have h : δ * ((k : ℝ) + 2) - δ * ((k : ℝ) - 1) = 3 * δ := by ring
    rw [h]
    have h2 : ENNReal.ofReal (3 * δ) = 3 * ENNReal.ofReal δ := by
      rw [ENNReal.ofReal_mul (by positivity)]
      <;> norm_num
    exact h2

  have h_sub : volume (⋃ k ∈ K, J k) ≤ ∑' (p : {k // k ∈ K}), volume (J p) :=
    measure_biUnion_le volume hK_count J

  have h_tsum : ∑' (p : {k // k ∈ K}), volume (J p) =
      (K.encard : ENNReal) * (3 * ENNReal.ofReal δ) := by
    have h1 : ∑' (p : {k // k ∈ K}), volume (J p) =
        ∑' (p : {k // k ∈ K}), 3 * ENNReal.ofReal δ := by
      apply tsum_congr
      intro p
      exact h_vol_J p
    rw [h1]
    rw [ENNReal.tsum_const (3 * ENNReal.ofReal δ)]
    have h_encard_eq : (ENat.card {k // k ∈ K} : ENNReal) = (K.encard : ENNReal) := by
      have h : ENat.card {k // k ∈ K} = K.encard := ENat.card_coe_set_eq K
      rw [h]
    rw [h_encard_eq]

  -- Injection K → dyadic cubes meeting S: k ↦ dyadicCube δ (fun _ => k)
  let f : ℤ → Set (EuclideanSpace ℝ (Fin 1)) := fun k => dyadicCube δ (fun _ => k)
  let mkPoint (y : ℝ) : EuclideanSpace ℝ (Fin 1) :=
    (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ => y)

  have h_f_inj : Set.InjOn f K := by
    intro k1 _ k2 _ h
    let z1 := mkPoint (δ * (k1 : ℝ))
    have hz1 : z1 ∈ f k1 := by
      have h : ∀ i : Fin 1, z1 i ∈ Set.Ico (δ * (k1 : ℝ)) (δ * ((k1 : ℝ) + 1)) := by
        intro i
        have h9 : z1 i = δ * (k1 : ℝ) := by
          simp [mkPoint]
          <;> rfl
        rw [h9] <;> constructor <;> linarith
      simpa [f, dyadicCube] using h
    have hz1' : z1 ∈ f k2 := by rw [h] at hz1; exact hz1
    have h4 : z1 0 ∈ Set.Ico (δ * (k2 : ℝ)) (δ * ((k2 : ℝ) + 1)) := by
      have h5 : ∀ i : Fin 1, z1 i ∈ Set.Ico (δ * (k2 : ℝ)) (δ * ((k2 : ℝ) + 1)) := by
        simpa [f, dyadicCube] using hz1'
      exact h5 0
    have h_z1 : z1 0 = δ * (k1 : ℝ) := by simp [mkPoint] <;> rfl
    rw [h_z1] at h4
    have h5 : (k2 : ℝ) ≤ (k1 : ℝ) := by
      have h51 : δ * (k2 : ℝ) ≤ δ * (k1 : ℝ) := h4.1
      have h52 : (δ * (k2 : ℝ)) / δ ≤ (δ * (k1 : ℝ)) / δ := by gcongr
      have h53 : (δ * (k2 : ℝ)) / δ = (k2 : ℝ) := by field_simp [hδ.ne']
      have h54 : (δ * (k1 : ℝ)) / δ = (k1 : ℝ) := by field_simp [hδ.ne']
      rw [h53, h54] at h52; exact h52
    have h6 : (k1 : ℝ) < (k2 : ℝ) + 1 := by
      have h61 : δ * (k1 : ℝ) < δ * ((k2 : ℝ) + 1) := h4.2
      have h62 : (δ * (k1 : ℝ)) / δ < (δ * ((k2 : ℝ) + 1)) / δ := by gcongr
      have h63 : (δ * (k1 : ℝ)) / δ = (k1 : ℝ) := by field_simp [hδ.ne']
      have h64 : (δ * ((k2 : ℝ) + 1)) / δ = (k2 : ℝ) + 1 := by field_simp [hδ.ne']
      rw [h63, h64] at h62; exact h62
    have h7 : k2 ≤ k1 := by exact_mod_cast h5
    have h8 : k1 < k2 + 1 := by exact_mod_cast h6
    omega

  have h_image_subset : f '' K ⊆ dyadicCubesMeeting (d := 1) δ (realLineCopy S) := by
    intro Q hQ
    rcases hQ with ⟨k, hk, rfl⟩
    rcases hk with ⟨x, hxI, hxS⟩
    let z := mkPoint x
    have hz1 : z ∈ f k := by
      have h : ∀ i : Fin 1, z i ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := by
        intro i
        have h9 : z i = x := by simp [mkPoint] <;> rfl
        rw [h9]; exact hxI
      simpa [f, dyadicCube] using h
    have hz2 : z ∈ realLineCopy S := by
      have h_z0 : z 0 = x := by simp [mkPoint] <;> rfl
      have h : z 0 ∈ S := by rw [h_z0]; exact hxS
      simpa [realLineCopy] using h
    have h_meets : (f k ∩ realLineCopy S).Nonempty := ⟨z, hz1, hz2⟩
    exact ⟨⟨(fun _ => k), rfl⟩, h_meets⟩

  have h_encard_le : (K.encard : ENNReal) ≤ Nreal δ S := by
    have h1 : (f '' K).encard ≤ (dyadicCubesMeeting (d := 1) δ (realLineCopy S)).encard :=
      Set.encard_mono h_image_subset
    have h2 : (f '' K).encard = K.encard := h_f_inj.encard_image
    have h3 : Nreal δ S = ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (realLineCopy S)) := by rfl
    rw [h3]
    have h4 : (K.encard : ENNReal) ≤ ENat.toENNReal (dyadicCubesMeeting (d := 1) δ (realLineCopy S)).encard := by
      rw [←h2]
      exact_mod_cast h1
    exact h4

  calc volume {t | ∃ x ∈ S, |t - x| < δ}
    ≤ volume (⋃ k ∈ K, J k) := measure_mono h_contain
  _ ≤ ∑' (p : {k // k ∈ K}), volume (J p) := h_sub
  _ = (K.encard : ENNReal) * (3 * ENNReal.ofReal δ) := h_tsum
  _ = 3 * ENNReal.ofReal δ * (K.encard : ENNReal) := by ring
  _ ≤ 3 * ENNReal.ofReal δ * Nreal δ S := by
    exact mul_le_mul_of_nonneg_left h_encard_le (by positivity)

end WeakTwoEndsSumProduct
