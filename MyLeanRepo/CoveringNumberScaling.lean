module

/-
# Covering Number Scaling and Comparison Lemmas

Elementary dyadic covering-number inequalities for the strong-ring proof.

## Main results

- `Nreal_scaling`: exact equality `N(δ, t·A) = N(δ/t, A)`
- `Nreal_scale_up_upper`: `N(δ, c·A) ≤ (⌈c⌉+1)·N(δ, A)` for `c ≥ 1`
- `Nreal_coarsening`: `N(δ, A) ≥ (r₀/3)·N(δ·r₀, A)` for `0 < r₀ ≤ 1`
- `Nreal_refinement_upper`: `N(Δ, A) ≤ (⌈Δ/δ⌉+1)·N(δ, A)` for `Δ ≥ δ`
- `Nreal_scale_down_bounds`: two-sided bounds for `N(δ, w·A)` when `0 < w ≤ 1`
- `Nreal_difference_set`: `N(δ, A-A) ≤ 3·N(δ, A)^2`

## Proof route

1. `Nreal_scaling`: direct bijection of cube index sets.
2. `Nreal_scale_up_upper`: fiber-counting — each δ-cube index of A accounts for
   at most `⌈c⌉+1` indices of c·A.
3. `Nreal_refinement_upper`: each δ-cube meets at most 2 Δ-cubes (Δ ≥ δ), so
   `N(Δ,A) ≤ 2·N(δ,A) ≤ (⌈Δ/δ⌉+1)·N(δ,A)`.
4. `Nreal_coarsening`: from scale-up with `c = 1/r₀` plus scaling equality.
5. `Nreal_scale_down_bounds`: combine scaling with coarsening (lower) and
   refinement (upper).
6. `Nreal_difference_set`: fiber-counting — each pair of cube indices accounts
   for at most 3 difference indices.

## Whiteprint

Node: `covering_number_scaling`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.Compat
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Classical Bornology

namespace WeakTwoEndsSumProduct

/-! ### Helper lemmas -/

/-- Boundedness is preserved under scaling of a real set. -/
lemma scaleSet_bounded {t : ℝ} {A : Set ℝ} (hA : IsBounded A) :
    IsBounded (scaleSet t A) := by
  have h_abs_nonneg : 0 ≤ |t| := abs_nonneg t
  have h_lip : LipschitzWith (Real.toNNReal (|t|)) (fun x : ℝ => t * x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h1 : dist (t * x) (t * y) = |t| * dist x y := by
      simp only [Real.dist_eq]
      have h2 : t * x - t * y = t * (x - y) := by ring
      rw [h2, abs_mul]
      <;> rfl
    rw [h1]
    have h3 : (Real.toNNReal (|t|) : ℝ) = |t| := by
      simp [Real.toNNReal_of_nonneg h_abs_nonneg]
      <;> norm_cast
    rw [h3] <;> exact le_refl _
  exact h_lip.isBounded_image hA

/-- General fiber-counting bound: if `f : S → T` has fibers of size at most `B`,
    then `|S| ≤ B * |T|`. -/
lemma finset_card_le_mul_of_bounded_fibers {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset α} {T : Finset β} {f : α → β} {B : ℕ}
    (h_f : ∀ x ∈ S, f x ∈ T)
    (h_fiber : ∀ y ∈ T, (S.filter (fun x => f x = y)).card ≤ B) :
    S.card ≤ B * T.card := by
  have h1 : S = Finset.biUnion T (fun y => S.filter (fun x => f x = y)) := by
    ext z
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hz
      exact ⟨f z, h_f z hz, hz, rfl⟩
    · rintro ⟨y, _, hz, _⟩
      exact hz
  rw [h1]
  calc (Finset.biUnion T (fun y => S.filter (fun x => f x = y))).card
    ≤ ∑ y ∈ T, (S.filter (fun x => f x = y)).card := Finset.card_biUnion_le
  _ ≤ ∑ y ∈ T, B := Finset.sum_le_sum (fun y hy => h_fiber y hy)
  _ = B * T.card := by simp [Finset.sum_const] <;> ring

/-- Integer count in `(c*k - 1, c*(k+1))` is at most `Nat.ceil c + 1`. -/
lemma int_count_scale_fiber {c : ℝ} (hc : 1 ≤ c) (k : ℤ) (S : Finset ℤ)
    (hS : ∀ m ∈ S, c * (k : ℝ) - 1 < (m : ℝ) ∧ (m : ℝ) < c * ((k : ℝ) + 1)) :
    S.card ≤ Nat.ceil c + 1 := by
  let base : ℤ := Int.floor (c * (k : ℝ))
  let g : ℤ → ℕ := fun m => (m - base).toNat
  have h_frac : c * (k : ℝ) - (Int.floor (c * (k : ℝ)) : ℝ) < 1 := by
    have h : c * (k : ℝ) < (Int.floor (c * (k : ℝ)) : ℝ) + 1 := Int.lt_floor_add_one (c * (k : ℝ))
    linarith
  have h_base_le : ∀ m ∈ S, base ≤ m := by
    intro m hm
    have h2 : (Int.floor (c * (k : ℝ)) : ℝ) < (m : ℝ) + 1 := by
      have h3 : c * (k : ℝ) - 1 < (m : ℝ) := (hS m hm).1
      have h4 : (Int.floor (c * (k : ℝ)) : ℝ) ≤ c * (k : ℝ) := Int.floor_le _
      linarith
    have h5 : Int.floor (c * (k : ℝ)) < m + 1 := by exact_mod_cast h2
    linarith
  have h_g_eq : ∀ m ∈ S, (g m : ℤ) = m - base := by
    intro m hm
    have h10 : 0 ≤ m - base := by linarith [h_base_le m hm]
    dsimp only [g]
    rw [Int.toNat_of_nonneg h10]
    <;> norm_cast
  have h_lt : ∀ m ∈ S, g m < Nat.ceil c + 1 := by
    intro m hm
    have h2 : (m : ℝ) < c * ((k : ℝ) + 1) := (hS m hm).2
    have h3 : (Int.floor (c * (k : ℝ)) : ℝ) ≤ c * (k : ℝ) := Int.floor_le _
    have h4 : ((m - base : ℤ) : ℝ) < c + 1 := by
      dsimp only [base]
      have h51 : (m : ℝ) < c * (k : ℝ) + c := by
        have h52 : c * ((k : ℝ) + 1) = c * (k : ℝ) + c := by ring
        rw [h52] at h2
        exact h2
      have h53 : (Int.floor (c * (k : ℝ)) : ℝ) ≤ c * (k : ℝ) := h3
      have h54 : c * (k : ℝ) - (Int.floor (c * (k : ℝ)) : ℝ) < 1 := h_frac
      have h55 : ((m - Int.floor (c * (k : ℝ)) : ℤ) : ℝ) = (m : ℝ) - (Int.floor (c * (k : ℝ)) : ℝ) := by
        simp
      rw [h55]
      linarith
    have h6 : (g m : ℝ) = ((m - base : ℤ) : ℝ) := by
      have h7 : (g m : ℤ) = m - base := h_g_eq m hm
      exact_mod_cast h7
    have h8 : (Nat.ceil c : ℝ) ≥ c := Nat.le_ceil c
    have h9 : (c + 1 : ℝ) ≤ ((Nat.ceil c + 1 : ℕ) : ℝ) := by
      have h10 : (Nat.ceil c : ℝ) ≥ c := h8
      have h11 : ((Nat.ceil c + 1 : ℕ) : ℝ) = (Nat.ceil c : ℝ) + 1 := by
        simp <;> norm_cast
      rw [h11] <;> linarith
    have h12 : (g m : ℝ) < ((Nat.ceil c + 1 : ℕ) : ℝ) := by
      rw [h6]
      exact lt_of_lt_of_le h4 h9
    exact_mod_cast h12
  have h_inj : Set.InjOn g (S : Set ℤ) := by
    intro m1 hm1 m2 hm2 h
    have h10 : (g m1 : ℤ) = m1 - base := h_g_eq m1 hm1
    have h11 : (g m2 : ℤ) = m2 - base := h_g_eq m2 hm2
    have h12 : (g m1 : ℤ) = (g m2 : ℤ) := by exact_mod_cast h
    rw [h10, h11] at h12
    <;> linarith
  have h_image : S.image g ⊆ Finset.range (Nat.ceil c + 1) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨m, hm, rfl⟩
    exact Finset.mem_range.mpr (h_lt m hm)
  have h13 : S.card = (S.image g).card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h14 : (Finset.range (Nat.ceil c + 1)).card = Nat.ceil c + 1 := Finset.card_range _
  rw [h13]
  have h15 : (S.image g).card ≤ (Finset.range (Nat.ceil c + 1)).card := Finset.card_le_card h_image
  rw [h14] at h15
  exact h15

/-- At most 2 integers lie in an open interval of length at most 2. -/
lemma int_count_in_short_interval {a b : ℝ} (h_len : b - a ≤ 2) (S : Finset ℤ)
    (hS : ∀ m ∈ S, a < (m : ℝ) ∧ (m : ℝ) < b) : S.card ≤ 2 := by
  let base : ℤ := Int.floor a + 1
  have h_base_le : ∀ m ∈ S, base ≤ m := by
    intro m hm
    have h1 : a < (m : ℝ) := (hS m hm).1
    have h2 : (Int.floor a : ℝ) < (m : ℝ) := by
      have h3 : (Int.floor a : ℝ) ≤ a := Int.floor_le a
      linarith
    have h4 : Int.floor a < m := by exact_mod_cast h2
    simp only [base] <;> linarith
  let g : ℤ → ℕ := fun m => (m - base).toNat
  have h_g_eq : ∀ m ∈ S, (g m : ℤ) = m - base := by
    intro m hm
    have h10 : 0 ≤ m - base := by linarith [h_base_le m hm]
    dsimp only [g]
    rw [Int.toNat_of_nonneg h10] <;> norm_cast
  have h_frac_lt_one : a - (Int.floor a : ℝ) < 1 := by
    have h4 := Int.lt_floor_add_one a
    linarith
  have h_lt2 : ∀ m ∈ S, g m < 2 := by
    intro m hm
    have h_m_lt_b : (m : ℝ) < b := (hS m hm).2
    have h_floor_le_a : (Int.floor a : ℝ) ≤ a := Int.floor_le a
    have h1 : (m : ℝ) - (Int.floor a : ℝ) < 3 := by
      have h2 : (m : ℝ) - (Int.floor a : ℝ) < b - (Int.floor a : ℝ) := by linarith
      have h3 : b - (Int.floor a : ℝ) = (b - a) + (a - (Int.floor a : ℝ)) := by ring
      rw [h3] at h2
      have h4 : (b - a) + (a - (Int.floor a : ℝ)) < 3 := by linarith [h_len, h_frac_lt_one]
      linarith
    have h5 : ((m - base : ℤ) : ℝ) < 2 := by
      dsimp only [base]
      have h6 : ((m - (Int.floor a + 1) : ℤ) : ℝ) = (m : ℝ) - (Int.floor a : ℝ) - 1 := by
        simp <;> ring
      rw [h6]
      linarith
    have h7 : (g m : ℝ) = ((m - base : ℤ) : ℝ) := by
      have h8 : (g m : ℤ) = m - base := h_g_eq m hm
      exact_mod_cast h8
    have h9 : (g m : ℝ) < 2 := by
      rw [h7] <;> exact h5
    exact_mod_cast h9
  have h_inj : Set.InjOn g (S : Set ℤ) := by
    intro m1 hm1 m2 hm2 h
    have h10 : (g m1 : ℤ) = (g m2 : ℤ) := by exact_mod_cast h
    have h11 : (g m1 : ℤ) = m1 - base := h_g_eq m1 hm1
    have h12 : (g m2 : ℤ) = m2 - base := h_g_eq m2 hm2
    rw [h11, h12] at h10 <;> linarith
  have h_range : S.image g ⊆ ({0, 1} : Finset ℕ) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨m, hm, rfl⟩
    have h13 : g m < 2 := h_lt2 m hm
    have h14 : g m = 0 ∨ g m = 1 := by omega
    rcases h14 with (h14 | h14)
    · rw [h14] <;> simp
    · rw [h14] <;> simp
  have h15 : S.card = (S.image g).card := by
    rw [Finset.card_image_of_injOn h_inj]
  rw [h15]
  have h16 : (S.image g).card ≤ ({0, 1} : Finset ℕ).card := Finset.card_le_card h_range
  have h17 : ({0, 1} : Finset ℕ).card = 2 := by decide
  rw [h17] at h16
  exact h16

/-- For `x > 0`, `(Nat.ceil x : ℝ) < x + 1`. -/
lemma nat_ceil_lt_add_one {x : ℝ} (hx : 0 < x) : (Nat.ceil x : ℝ) < x + 1 := by
  have h_n_pos : 0 < Nat.ceil x := Nat.ceil_pos.mpr hx
  have h2 : ((Nat.ceil x - 1 : ℕ) : ℝ) < x := by
    by_contra h3
    have h4 : x ≤ ((Nat.ceil x - 1 : ℕ) : ℝ) := by linarith
    have h5 : Nat.ceil x ≤ Nat.ceil x - 1 := Nat.ceil_le.mpr h4
    omega
  have h6 : ((Nat.ceil x - 1 : ℕ) : ℝ) = (Nat.ceil x : ℝ) - 1 := by
    simp [h_n_pos] <;> omega
  rw [h6] at h2
  linarith

/-! ### Exact scaling -/

/-- `N(δ, t·A) = N(δ/t, A)` for `t > 0`. -/
lemma Nreal_scaling {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t)
    {A : Set ℝ} (hA : IsBounded A) :
    Nreal δ (scaleSet t A) = Nreal (δ / t) A := by
  let Iδt := ProductLikeIncidence.realCubeIndexSet δ (scaleSet t A)
  let Idt := ProductLikeIncidence.realCubeIndexSet (δ / t) A
  have h_eq : Iδt = Idt := by
    ext k
    have h1 : k ∈ Iδt ↔ ∃ (y : ℝ), (δ * (k : ℝ) ≤ y ∧ y < δ * ((k : ℝ) + 1)) ∧ y ∈ scaleSet t A := by
      have h_main : k ∈ Iδt ↔ ∃ (x : ℝ), x ∈ scaleSet t A ∧ δ * (k : ℝ) ≤ x ∧ x < δ * ((k : ℝ) + 1) :=
        ProductLikeIncidence.realCubeIndexSet_mem_iff
      rw [h_main]
      apply exists_congr; intro y; tauto
    have h2 : k ∈ Idt ↔ ∃ (x : ℝ), ((δ / t) * (k : ℝ) ≤ x ∧ x < (δ / t) * ((k : ℝ) + 1)) ∧ x ∈ A := by
      have h_main : k ∈ Idt ↔ ∃ (x : ℝ), x ∈ A ∧ (δ / t) * (k : ℝ) ≤ x ∧ x < (δ / t) * ((k : ℝ) + 1) :=
        ProductLikeIncidence.realCubeIndexSet_mem_iff
      rw [h_main]
      apply exists_congr; intro x; tauto
    rw [h1, h2]
    constructor
    · rintro ⟨y, ⟨h1, h2⟩, ⟨x, hxA, rfl⟩⟩
      refine ⟨x, ⟨?_, ?_⟩, hxA⟩
      · calc (δ / t) * (k : ℝ) = (δ * (k : ℝ)) / t := by field_simp [ht.ne'] <;> ring
          _ ≤ (t * x) / t := by gcongr
          _ = x := by field_simp [ht.ne'] <;> ring
      · calc x = (t * x) / t := by field_simp [ht.ne'] <;> ring
          _ < (δ * ((k : ℝ) + 1)) / t := by gcongr
          _ = (δ / t) * ((k : ℝ) + 1) := by field_simp [ht.ne'] <;> ring
    · rintro ⟨x, ⟨h1, h2⟩, hxA⟩
      refine ⟨t * x, ⟨?_, ?_⟩, ⟨x, hxA, rfl⟩⟩
      · calc δ * (k : ℝ) = t * ((δ / t) * (k : ℝ)) := by field_simp [ht.ne'] <;> ring
          _ ≤ t * x := by gcongr
      · calc t * x < t * ((δ / t) * ((k : ℝ) + 1)) := by gcongr
          _ = δ * ((k : ℝ) + 1) := by field_simp [ht.ne'] <;> ring
  have h_bdd1 : IsBounded (scaleSet t A) := scaleSet_bounded hA
  have h_eq1 : Nreal δ (scaleSet t A) = (Iδt.encard : ENNReal) := by
    have h := ProductLikeIncidence.realCoveringNumber_eq_card_ennreal hδ h_bdd1
    have h' : Nreal δ (scaleSet t A) =
        ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (scaleSet t A))) := by rfl
    rw [h']
    exact h
  have h_eq2 : Nreal (δ / t) A = (Idt.encard : ENNReal) := by
    have h := ProductLikeIncidence.realCoveringNumber_eq_card_ennreal (div_pos hδ ht) hA
    have h' : Nreal (δ / t) A =
        ENat.toENNReal (dyadicCoveringNumber (δ / t) (productLikeRealLineCopy A)) := by rfl
    rw [h']
    exact h
  rw [h_eq1, h_eq2, h_eq]

/-! ### Scale-up upper bound -/

/-- `N(δ, c·A) ≤ (⌈c⌉+1)·N(δ, A)` for `c ≥ 1`. -/
lemma Nreal_scale_up_upper {δ c : ℝ} (hδ : 0 < δ) (hc : 1 ≤ c)
    {A : Set ℝ} (hA : IsBounded A) :
    Nreal δ (scaleSet c A) ≤ (Nat.ceil c + 1 : ENNReal) * Nreal δ A := by
  let I_cA := ProductLikeIncidence.realCubeIndexSet δ (scaleSet c A)
  let I_A := ProductLikeIncidence.realCubeIndexSet δ A
  have h_fin_cA : I_cA.Finite := ProductLikeIncidence.realCubeIndexSet_finite hδ (scaleSet_bounded hA)
  have h_fin_A : I_A.Finite := ProductLikeIncidence.realCubeIndexSet_finite hδ hA
  let K_cA : Finset ℤ := h_fin_cA.toFinset
  let K_A : Finset ℤ := h_fin_A.toFinset
  have hK_cA : (K_cA : Set ℤ) = I_cA := Set.Finite.coe_toFinset h_fin_cA
  have hK_A : (K_A : Set ℤ) = I_A := Set.Finite.coe_toFinset h_fin_A
  have h_exists : ∀ (m : ℤ), m ∈ I_cA → ∃ (x : ℝ), x ∈ A ∧ δ * (m : ℝ) ≤ c * x ∧ c * x < δ * ((m : ℝ) + 1) := by
    intro m hm
    have h_mem := ProductLikeIncidence.realCubeIndexSet_mem_iff.mp hm
    rcases h_mem with ⟨y, hyS, h1, h2⟩
    rcases hyS with ⟨x, hxA, rfl⟩
    exact ⟨x, hxA, h1, h2⟩
  let x : ℤ → ℝ := fun m => if h : m ∈ I_cA then Classical.choose (h_exists m h) else 0
  let k : ℤ → ℤ := fun m => Int.floor (x m / δ)
  have h_x_prop : ∀ m ∈ I_cA, x m ∈ A ∧ δ * (m : ℝ) ≤ c * (x m) ∧ c * (x m) < δ * ((m : ℝ) + 1) := by
    intro m hm
    have h' := Classical.choose_spec (h_exists m hm)
    have h_x_def : x m = Classical.choose (h_exists m hm) := by
      simp [x, dif_pos hm]
    rw [h_x_def]
    exact h'
  have h_k_in_A : ∀ m ∈ K_cA, k m ∈ K_A := by
    intro m hm
    have hm' : m ∈ I_cA := by rw [←hK_cA] <;> exact hm
    have hxp := h_x_prop m hm'
    have h1 : δ * (k m : ℝ) ≤ x m := by
      dsimp only [k]
      have h2 : (k m : ℝ) ≤ x m / δ := Int.floor_le (x m / δ)
      have h3 : δ * (k m : ℝ) ≤ δ * (x m / δ) := by gcongr
      have h4 : δ * (x m / δ) = x m := by field_simp [hδ.ne'] <;> ring
      rw [h4] at h3 <;> exact h3
    have h2 : x m < δ * ((k m : ℝ) + 1) := by
      dsimp only [k]
      have h3 : x m / δ < (k m : ℝ) + 1 := Int.lt_floor_add_one (x m / δ)
      have h4 : δ * (x m / δ) < δ * ((k m : ℝ) + 1) := by gcongr
      have h5 : δ * (x m / δ) = x m := by field_simp [hδ.ne'] <;> ring
      rw [h5] at h4 <;> exact h4
    have h6 : k m ∈ I_A := ProductLikeIncidence.realCubeIndexSet_mem_iff.mpr
      ⟨x m, hxp.1, h1, h2⟩
    have h7 : k m ∈ K_A := by
      have h8 : k m ∈ (K_A : Set ℤ) := by
        rw [hK_A]
        exact h6
      exact h8
    exact h7
  have h_fiber : ∀ j ∈ K_A, (K_cA.filter (fun m => k m = j)).card ≤ Nat.ceil c + 1 := by
    intro j hj
    let S := K_cA.filter (fun m => k m = j)
    have hS : ∀ m ∈ S, c * (j : ℝ) - 1 < (m : ℝ) ∧ (m : ℝ) < c * ((j : ℝ) + 1) := by
      intro m hm
      have h_m_in_cA : m ∈ I_cA := by
        have h : m ∈ K_cA := (Finset.mem_filter.mp hm).1
        rw [←hK_cA] <;> exact h
      have h_k_eq : k m = j := (Finset.mem_filter.mp hm).2
      have hxp := h_x_prop m h_m_in_cA
      have h1 : δ * (j : ℝ) ≤ x m := by
        have h2 : δ * (k m : ℝ) ≤ x m := by
          dsimp only [k]
          have h3 : (k m : ℝ) ≤ x m / δ := Int.floor_le (x m / δ)
          have h4 : δ * (k m : ℝ) ≤ δ * (x m / δ) := by gcongr
          have h5 : δ * (x m / δ) = x m := by field_simp [hδ.ne'] <;> ring
          rw [h5] at h4 <;> exact h4
        rw [h_k_eq] at h2 <;> exact h2
      have h2 : x m < δ * ((j : ℝ) + 1) := by
        have h3 : x m < δ * ((k m : ℝ) + 1) := by
          dsimp only [k]
          have h4 : x m / δ < (k m : ℝ) + 1 := Int.lt_floor_add_one (x m / δ)
          have h5 : δ * (x m / δ) < δ * ((k m : ℝ) + 1) := by gcongr
          have h6 : δ * (x m / δ) = x m := by field_simp [hδ.ne'] <;> ring
          rw [h6] at h5 <;> exact h5
        rw [h_k_eq] at h3 <;> exact h3
      have h3 : δ * (m : ℝ) ≤ c * (x m) := hxp.2.1
      have h4 : c * (x m) < δ * ((m : ℝ) + 1) := hxp.2.2
      constructor
      · -- c * j - 1 < m
        have h_pos : 0 < δ := hδ
        have h_c_nonneg : 0 ≤ c := by linarith
        nlinarith
      · -- m < c * (j + 1)
        have h_pos : 0 < δ := hδ
        have h_c_nonneg : 0 ≤ c := by linarith
        nlinarith
    exact int_count_scale_fiber hc j S hS
  have h_main_card : K_cA.card ≤ (Nat.ceil c + 1) * K_A.card :=
    finset_card_le_mul_of_bounded_fibers h_k_in_A h_fiber
  have h_enc_cA : (I_cA.encard : ENNReal) = ↑K_cA.card := by
    exact_mod_cast Set.Finite.encard_eq_coe_toFinset_card h_fin_cA
  have h_enc_A : (I_A.encard : ENNReal) = ↑K_A.card := by
    exact_mod_cast Set.Finite.encard_eq_coe_toFinset_card h_fin_A
  have h_bdd_cA : IsBounded (scaleSet c A) := scaleSet_bounded hA
  have h1 : Nreal δ (scaleSet c A) = (I_cA.encard : ENNReal) := by
    have h := ProductLikeIncidence.realCoveringNumber_eq_card_ennreal hδ h_bdd_cA
    have h' : Nreal δ (scaleSet c A) =
        ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (scaleSet c A))) := by rfl
    rw [h'] <;> exact h
  have h2 : Nreal δ A = (I_A.encard : ENNReal) := by
    have h := ProductLikeIncidence.realCoveringNumber_eq_card_ennreal hδ hA
    have h' : Nreal δ A =
        ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A)) := by rfl
    rw [h'] <;> exact h
  rw [h1, h2, h_enc_cA, h_enc_A]
  exact_mod_cast h_main_card

/-! ### Refinement upper bound -/

/-- Upper bound for coarser scale: `N(Δ, A) ≤ (⌈Δ/δ⌉+1)·N(δ, A)` when `Δ ≥ δ > 0`. -/
lemma Nreal_refinement_upper {δ Δ : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ) (h_le : δ ≤ Δ)
    {A : Set ℝ} (hA : IsBounded A) :
    Nreal Δ A ≤ (Nat.ceil (Δ / δ) + 1 : ENNReal) * Nreal δ A := by
  let I_Δ := ProductLikeIncidence.realCubeIndexSet Δ A
  let I_δ := ProductLikeIncidence.realCubeIndexSet δ A
  have h_fin_Δ : I_Δ.Finite := ProductLikeIncidence.realCubeIndexSet_finite hΔ hA
  have h_fin_δ : I_δ.Finite := ProductLikeIncidence.realCubeIndexSet_finite hδ hA
  let K_Δ : Finset ℤ := h_fin_Δ.toFinset
  let K_δ : Finset ℤ := h_fin_δ.toFinset
  have hK_Δ : (K_Δ : Set ℤ) = I_Δ := Set.Finite.coe_toFinset h_fin_Δ
  have hK_δ : (K_δ : Set ℤ) = I_δ := Set.Finite.coe_toFinset h_fin_δ
  have h_exists : ∀ (m : ℤ), m ∈ I_Δ → ∃ (x : ℝ), x ∈ A ∧ Δ * (m : ℝ) ≤ x ∧ x < Δ * ((m : ℝ) + 1) := by
    intro m hm
    rcases hm with ⟨x, hx⟩
    exact ⟨x, hx.2, hx.1.1, hx.1.2⟩
  let x : ℤ → ℝ := fun m => if h : m ∈ I_Δ then Classical.choose (h_exists m h) else 0
  let k : ℤ → ℤ := fun m => Int.floor (x m / δ)
  have h_x_prop : ∀ m ∈ I_Δ, x m ∈ A ∧ Δ * (m : ℝ) ≤ x m ∧ x m < Δ * ((m : ℝ) + 1) := by
    intro m hm
    have h' := Classical.choose_spec (h_exists m hm)
    have h_x_def : x m = Classical.choose (h_exists m hm) := by
      simp [x, dif_pos hm]
    rw [h_x_def] <;> exact h'
  have h_k_in_δ : ∀ m ∈ K_Δ, k m ∈ K_δ := by
    intro m hm
    have hm' : m ∈ I_Δ := by rw [←hK_Δ] <;> exact hm
    have hxp := h_x_prop m hm'
    have h1 : δ * (k m : ℝ) ≤ x m := by
      dsimp only [k]
      have h2 : (k m : ℝ) ≤ x m / δ := Int.floor_le (x m / δ)
      have h3 : δ * (k m : ℝ) ≤ δ * (x m / δ) := by gcongr
      have h4 : δ * (x m / δ) = x m := by field_simp [hδ.ne'] <;> ring
      rw [h4] at h3 <;> exact h3
    have h2 : x m < δ * ((k m : ℝ) + 1) := by
      dsimp only [k]
      have h3 : x m / δ < (k m : ℝ) + 1 := Int.lt_floor_add_one (x m / δ)
      have h4 : δ * (x m / δ) < δ * ((k m : ℝ) + 1) := by gcongr
      have h5 : δ * (x m / δ) = x m := by field_simp [hδ.ne'] <;> ring
      rw [h5] at h4 <;> exact h4
    have h6 : k m ∈ I_δ := ProductLikeIncidence.realCubeIndexSet_mem_iff.mpr
      ⟨x m, hxp.1, h1, h2⟩
    have h7 : k m ∈ (K_δ : Set ℤ) := by rw [hK_δ] <;> exact h6
    exact h7
  let c : ℝ := Δ / δ
  have hc : 1 ≤ c := by
    have h' : 0 < δ := hδ
    have h'' : δ / δ ≤ Δ / δ := by gcongr
    have h1 : δ / δ = 1 := by field_simp [h'.ne'] <;> ring
    rw [h1] at h'' <;> exact h''
  have h_c_pos : 0 < c := by positivity
  have h_fiber2 : ∀ j ∈ K_δ, (K_Δ.filter (fun m => k m = j)).card ≤ 2 := by
    intro j hj
    let S := K_Δ.filter (fun m => k m = j)
    have hS : ∀ m ∈ S, (j : ℝ) / c - 1 < (m : ℝ) ∧ (m : ℝ) < ((j : ℝ) + 1) / c := by
      intro m hm
      have h_m_in : m ∈ I_Δ := by
        have h : m ∈ K_Δ := (Finset.mem_filter.mp hm).1
        rw [←hK_Δ] <;> exact h
      have h_k_eq : k m = j := (Finset.mem_filter.mp hm).2
      have hxp := h_x_prop m h_m_in
      have h1 : δ * (j : ℝ) ≤ x m := by
        have h2 : δ * (k m : ℝ) ≤ x m := by
          dsimp only [k]; have h3 : (k m : ℝ) ≤ x m / δ := Int.floor_le (x m / δ)
          have h4 : δ * (k m : ℝ) ≤ δ * (x m / δ) := by gcongr
          have h5 : δ * (x m / δ) = x m := by field_simp [hδ.ne'] <;> ring
          rw [h5] at h4 <;> exact h4
        rw [h_k_eq] at h2 <;> exact h2
      have h2 : x m < δ * ((j : ℝ) + 1) := by
        have h3 : x m < δ * ((k m : ℝ) + 1) := by
          dsimp only [k]; have h4 : x m / δ < (k m : ℝ) + 1 := Int.lt_floor_add_one (x m / δ)
          have h5 : δ * (x m / δ) < δ * ((k m : ℝ) + 1) := by gcongr
          have h6 : δ * (x m / δ) = x m := by field_simp [hδ.ne'] <;> ring
          rw [h6] at h5 <;> exact h5
        rw [h_k_eq] at h3 <;> exact h3
      have h3 : Δ * (m : ℝ) ≤ x m := hxp.2.1
      have h4 : x m < Δ * ((m : ℝ) + 1) := hxp.2.2
      have h5 : (m : ℝ) < ((j : ℝ) + 1) / c := by
        have h6 : Δ * (m : ℝ) < δ * ((j : ℝ) + 1) := by linarith
        have h_eq : Δ = c * δ := by
          dsimp only [c]; field_simp [hδ.ne'] <;> ring
        rw [h_eq] at h6
        have h9 : c * (m : ℝ) < (j : ℝ) + 1 := by
          have h10 : c * δ * (m : ℝ) < δ * ((j : ℝ) + 1) := h6
          have h11 : 0 < δ := hδ
          nlinarith
        calc (m : ℝ)
          = (c * (m : ℝ)) / c := by field_simp [h_c_pos.ne'] <;> ring
        _ < ((j : ℝ) + 1) / c := by gcongr
      have h6 : (j : ℝ) / c - 1 < (m : ℝ) := by
        have h7 : δ * (j : ℝ) < Δ * ((m : ℝ) + 1) := by linarith
        have h_eq : Δ = c * δ := by
          dsimp only [c]; field_simp [hδ.ne'] <;> ring
        rw [h_eq] at h7
        have h9 : (j : ℝ) < c * ((m : ℝ) + 1) := by
          have h10 : δ * (j : ℝ) < c * δ * ((m : ℝ) + 1) := h7
          have h11 : 0 < δ := hδ
          nlinarith
        have h12 : (j : ℝ) / c < (m : ℝ) + 1 := by
          calc (j : ℝ) / c
            < (c * ((m : ℝ) + 1)) / c := by gcongr
          _ = (m : ℝ) + 1 := by field_simp [h_c_pos.ne'] <;> ring
        linarith
      exact ⟨h6, h5⟩
    have h_len : (((j : ℝ) + 1) / c) - ((j : ℝ) / c - 1) ≤ 2 := by
      have h9 : 1 / c ≤ 1 := by
        have h10 : 1 ≤ c := hc
        have h11 : 0 < c := h_c_pos
        calc 1 / c ≤ 1 / 1 := by gcongr
          _ = 1 := by norm_num
      have h10 : (((j : ℝ) + 1) / c) - ((j : ℝ) / c - 1) = 1 / c + 1 := by
        field_simp [h_c_pos.ne'] <;> ring
      rw [h10] <;> linarith
    exact int_count_in_short_interval h_len S hS
  have h_main_card : K_Δ.card ≤ 2 * K_δ.card :=
    finset_card_le_mul_of_bounded_fibers h_k_in_δ h_fiber2
  have h_factor2 : (2 : ENNReal) ≤ (Nat.ceil c + 1 : ENNReal) := by
    have h21 : 1 ≤ c := hc
    have h22 : 1 ≤ Nat.ceil c := by
      have h23 : (1 : ℝ) ≤ c := h21
      exact Nat.one_le_ceil_iff.mpr h_c_pos
    have h24 : 2 ≤ Nat.ceil c + 1 := by linarith
    exact_mod_cast h24
  have h_enc_Δ : (I_Δ.encard : ENNReal) = ↑K_Δ.card := by
    exact_mod_cast Set.Finite.encard_eq_coe_toFinset_card h_fin_Δ
  have h_enc_δ : (I_δ.encard : ENNReal) = ↑K_δ.card := by
    exact_mod_cast Set.Finite.encard_eq_coe_toFinset_card h_fin_δ
  have h1 : Nreal Δ A = (I_Δ.encard : ENNReal) := by
    have h := ProductLikeIncidence.realCoveringNumber_eq_card_ennreal hΔ hA
    have h' : Nreal Δ A =
        ENat.toENNReal (dyadicCoveringNumber Δ (productLikeRealLineCopy A)) := by rfl
    rw [h'] <;> exact h
  have h2 : Nreal δ A = (I_δ.encard : ENNReal) := by
    have h := ProductLikeIncidence.realCoveringNumber_eq_card_ennreal hδ hA
    have h' : Nreal δ A =
        ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A)) := by rfl
    rw [h'] <;> exact h
  rw [h1, h2, h_enc_Δ, h_enc_δ]
  calc (↑K_Δ.card : ENNReal)
    ≤ (2 : ENNReal) * (↑K_δ.card : ENNReal) := by exact_mod_cast h_main_card
  _ ≤ (Nat.ceil c + 1 : ENNReal) * (↑K_δ.card : ENNReal) := by gcongr

/-- Tight 1D refining bound: `N(Δ, A) ≤ 2 * N(δ, A)` when `0 < δ ≤ Δ`. -/
lemma Nreal_refining {δ Δ : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ) (h_le : δ ≤ Δ)
    {A : Set ℝ} (hA : IsBounded A) :
    Nreal Δ A ≤ 2 * Nreal δ A := by
  let I_Δ := ProductLikeIncidence.realCubeIndexSet Δ A
  let I_δ := ProductLikeIncidence.realCubeIndexSet δ A
  have h_fin_Δ : I_Δ.Finite := ProductLikeIncidence.realCubeIndexSet_finite hΔ hA
  have h_fin_δ : I_δ.Finite := ProductLikeIncidence.realCubeIndexSet_finite hδ hA
  let K_Δ : Finset ℤ := h_fin_Δ.toFinset
  let K_δ : Finset ℤ := h_fin_δ.toFinset
  have hK_Δ : (K_Δ : Set ℤ) = I_Δ := Set.Finite.coe_toFinset h_fin_Δ
  have hK_δ : (K_δ : Set ℤ) = I_δ := Set.Finite.coe_toFinset h_fin_δ
  have h_exists : ∀ (m : ℤ), m ∈ I_Δ → ∃ (x : ℝ), x ∈ A ∧ Δ * (m : ℝ) ≤ x ∧ x < Δ * ((m : ℝ) + 1) := by
    intro m hm
    exact ProductLikeIncidence.realCubeIndexSet_mem_iff.mp hm
  let x : ℤ → ℝ := fun m => if h : m ∈ I_Δ then Classical.choose (h_exists m h) else 0
  let k : ℤ → ℤ := fun m => Int.floor (x m / δ)
  have h_x_prop : ∀ m ∈ I_Δ, x m ∈ A ∧ Δ * (m : ℝ) ≤ x m ∧ x m < Δ * ((m : ℝ) + 1) := by
    intro m hm
    have h' := Classical.choose_spec (h_exists m hm)
    have h_x_def : x m = Classical.choose (h_exists m hm) := by simp [x, dif_pos hm]
    rw [h_x_def] <;> exact h'
  have h_k_in_δ : ∀ m ∈ K_Δ, k m ∈ K_δ := by
    intro m hm
    have hm' : m ∈ I_Δ := by rw [←hK_Δ] <;> exact hm
    have hxp := h_x_prop m hm'
    have h1 : δ * (k m : ℝ) ≤ x m := by
      dsimp only [k]; have h2 : (k m : ℝ) ≤ x m / δ := Int.floor_le (x m / δ)
      have h3 : δ * (k m : ℝ) ≤ δ * (x m / δ) := by gcongr
      have h4 : δ * (x m / δ) = x m := by field_simp [hδ.ne'] <;> ring
      rw [h4] at h3 <;> exact h3
    have h2 : x m < δ * ((k m : ℝ) + 1) := by
      dsimp only [k]; have h3 : x m / δ < (k m : ℝ) + 1 := Int.lt_floor_add_one (x m / δ)
      have h4 : δ * (x m / δ) < δ * ((k m : ℝ) + 1) := by gcongr
      have h5 : δ * (x m / δ) = x m := by field_simp [hδ.ne'] <;> ring
      rw [h5] at h4 <;> exact h4
    have h6 : k m ∈ I_δ := ProductLikeIncidence.realCubeIndexSet_mem_iff.mpr
      ⟨x m, hxp.1, h1, h2⟩
    have h7 : k m ∈ (K_δ : Set ℤ) := by rw [hK_δ] <;> exact h6
    exact h7
  let c : ℝ := Δ / δ
  have hc : 1 ≤ c := by
    have h' : 0 < δ := hδ
    have h'' : δ / δ ≤ Δ / δ := by gcongr
    have h1 : δ / δ = 1 := by field_simp [h'.ne'] <;> ring
    rw [h1] at h'' <;> exact h''
  have h_c_pos : 0 < c := by positivity
  have h_fiber2 : ∀ j ∈ K_δ, (K_Δ.filter (fun m => k m = j)).card ≤ 2 := by
    intro j hj
    let S := K_Δ.filter (fun m => k m = j)
    have hS : ∀ m ∈ S, (j : ℝ) / c - 1 < (m : ℝ) ∧ (m : ℝ) < ((j : ℝ) + 1) / c := by
      intro m hm
      have h_m_in : m ∈ I_Δ := by
        have h : m ∈ K_Δ := (Finset.mem_filter.mp hm).1
        rw [←hK_Δ] <;> exact h
      have h_k_eq : k m = j := (Finset.mem_filter.mp hm).2
      have hxp := h_x_prop m h_m_in
      have h1 : δ * (j : ℝ) ≤ x m := by
        have h2 : δ * (k m : ℝ) ≤ x m := by
          dsimp only [k]; have h3 : (k m : ℝ) ≤ x m / δ := Int.floor_le (x m / δ)
          have h4 : δ * (k m : ℝ) ≤ δ * (x m / δ) := by gcongr
          have h5 : δ * (x m / δ) = x m := by field_simp [hδ.ne'] <;> ring
          rw [h5] at h4 <;> exact h4
        rw [h_k_eq] at h2 <;> exact h2
      have h2 : x m < δ * ((j : ℝ) + 1) := by
        have h3 : x m < δ * ((k m : ℝ) + 1) := by
          dsimp only [k]; have h4 : x m / δ < (k m : ℝ) + 1 := Int.lt_floor_add_one (x m / δ)
          have h5 : δ * (x m / δ) < δ * ((k m : ℝ) + 1) := by gcongr
          have h6 : δ * (x m / δ) = x m := by field_simp [hδ.ne'] <;> ring
          rw [h6] at h5 <;> exact h5
        rw [h_k_eq] at h3 <;> exact h3
      have h3 : Δ * (m : ℝ) ≤ x m := hxp.2.1
      have h4 : x m < Δ * ((m : ℝ) + 1) := hxp.2.2
      have h5 : (m : ℝ) < ((j : ℝ) + 1) / c := by
        have h6 : Δ * (m : ℝ) < δ * ((j : ℝ) + 1) := by linarith
        have h_eq : Δ = c * δ := by dsimp only [c]; field_simp [hδ.ne'] <;> ring
        rw [h_eq] at h6
        have h9 : c * (m : ℝ) < (j : ℝ) + 1 := by
          have h10 : c * δ * (m : ℝ) < δ * ((j : ℝ) + 1) := h6
          have h11 : 0 < δ := hδ
          nlinarith
        calc (m : ℝ)
          = (c * (m : ℝ)) / c := by field_simp [h_c_pos.ne'] <;> ring
        _ < ((j : ℝ) + 1) / c := by gcongr
      have h6 : (j : ℝ) / c - 1 < (m : ℝ) := by
        have h7 : δ * (j : ℝ) < Δ * ((m : ℝ) + 1) := by linarith
        have h_eq : Δ = c * δ := by dsimp only [c]; field_simp [hδ.ne'] <;> ring
        rw [h_eq] at h7
        have h9 : (j : ℝ) < c * ((m : ℝ) + 1) := by
          have h10 : δ * (j : ℝ) < c * δ * ((m : ℝ) + 1) := h7
          have h11 : 0 < δ := hδ
          nlinarith
        have h12 : (j : ℝ) / c < (m : ℝ) + 1 := by
          calc (j : ℝ) / c
            < (c * ((m : ℝ) + 1)) / c := by gcongr
          _ = (m : ℝ) + 1 := by field_simp [h_c_pos.ne'] <;> ring
        linarith
      exact ⟨h6, h5⟩
    have h_len : (((j : ℝ) + 1) / c) - ((j : ℝ) / c - 1) ≤ 2 := by
      have h9 : 1 / c ≤ 1 := by
        have h10 : 1 ≤ c := hc
        have h11 : 0 < c := h_c_pos
        calc 1 / c ≤ 1 / 1 := by gcongr
          _ = 1 := by norm_num
      have h10 : (((j : ℝ) + 1) / c) - ((j : ℝ) / c - 1) = 1 / c + 1 := by
        field_simp [h_c_pos.ne'] <;> ring
      rw [h10] <;> linarith
    exact int_count_in_short_interval h_len S hS
  have h_main_card : K_Δ.card ≤ 2 * K_δ.card :=
    finset_card_le_mul_of_bounded_fibers h_k_in_δ h_fiber2
  have h_enc_Δ : (I_Δ.encard : ENNReal) = ↑K_Δ.card := by
    exact_mod_cast Set.Finite.encard_eq_coe_toFinset_card h_fin_Δ
  have h_enc_δ : (I_δ.encard : ENNReal) = ↑K_δ.card := by
    exact_mod_cast Set.Finite.encard_eq_coe_toFinset_card h_fin_δ
  have h1 : Nreal Δ A = (I_Δ.encard : ENNReal) := by
    have h := ProductLikeIncidence.realCoveringNumber_eq_card_ennreal hΔ hA
    have h' : Nreal Δ A = ENat.toENNReal (dyadicCoveringNumber Δ (productLikeRealLineCopy A)) := by rfl
    rw [h'] <;> exact h
  have h2 : Nreal δ A = (I_δ.encard : ENNReal) := by
    have h := ProductLikeIncidence.realCoveringNumber_eq_card_ennreal hδ hA
    have h' : Nreal δ A = ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A)) := by rfl
    rw [h'] <;> exact h
  rw [h1, h2, h_enc_Δ, h_enc_δ]
  exact_mod_cast h_main_card

/-! ### Coarsening lower bound -/

/-- `N(δ, A) ≥ (r₀/3)·N(δ·r₀, A)` for `0 < r₀ ≤ 1`. -/
lemma Nreal_coarsening {δ r₀ : ℝ} (hδ : 0 < δ) (hr₀_pos : 0 < r₀) (hr₀_le_one : r₀ ≤ 1)
    {A : Set ℝ} (hA : IsBounded A) :
    ENNReal.ofReal (r₀ / 3) * Nreal (δ * r₀) A ≤ Nreal δ A := by
  let c : ℝ := 1 / r₀
  have hc : 1 ≤ c := by
    have h1 : 0 < r₀ := hr₀_pos
    have h2 : r₀ ≤ 1 := hr₀_le_one
    have h3 : 1 / r₀ ≥ 1 := by
      calc 1 / r₀ ≥ 1 / 1 := by gcongr
        _ = 1 := by norm_num
    exact h3
  have h_scaling : Nreal δ (scaleSet c A) = Nreal (δ * r₀) A := by
    have h1 : Nreal δ (scaleSet c A) = Nreal (δ / c) A := Nreal_scaling hδ (by positivity) hA
    have h2 : δ / c = δ * r₀ := by
      dsimp only [c]
      field_simp [hr₀_pos.ne'] <;> ring
    rw [h1, h2]
  have h_upper : Nreal δ (scaleSet c A) ≤ (Nat.ceil c + 1 : ENNReal) * Nreal δ A :=
    Nreal_scale_up_upper hδ hc hA
  rw [h_scaling] at h_upper
  have h_real_bound : (Nat.ceil c + 1 : ℝ) ≤ 3 / r₀ := by
    dsimp only [c]
    have h_pos : 0 < 1 / r₀ := by positivity
    have h1 : (Nat.ceil (1 / r₀) : ℝ) < 1 / r₀ + 1 := nat_ceil_lt_add_one h_pos
    have h4 : (Nat.ceil (1 / r₀) + 1 : ℝ) < 1 / r₀ + 2 := by linarith
    have h5 : (2 : ℝ) ≤ 2 / r₀ := by
      have h6 : 0 < r₀ := hr₀_pos
      have h7 : r₀ ≤ 1 := hr₀_le_one
      calc (2 : ℝ)
        = 2 / 1 := by norm_num
      _ ≤ 2 / r₀ := by gcongr
    have h6 : 1 / r₀ + 2 ≤ 3 / r₀ := by
      have h7 : (2 : ℝ) ≤ 2 / r₀ := h5
      have h8 : 1 / r₀ + 2 ≤ 1 / r₀ + 2 / r₀ := by linarith
      have h9 : 1 / r₀ + 2 / r₀ = 3 / r₀ := by
        field_simp [hr₀_pos.ne'] <;> ring
      linarith
    have h10 : (Nat.ceil (1 / r₀) + 1 : ℝ) ≤ 3 / r₀ := by linarith
    exact h10
  have h3 : (Nat.ceil c + 1 : ENNReal) ≤ ENNReal.ofReal (3 / r₀) := by
    have h_eq : (Nat.ceil c + 1 : ENNReal) = ENNReal.ofReal ((Nat.ceil c + 1 : ℝ)) := by
      norm_cast
    rw [h_eq]
    exact ENNReal.ofReal_le_ofReal h_real_bound
  have h4 : Nreal (δ * r₀) A ≤ ENNReal.ofReal (3 / r₀) * Nreal δ A := by
    calc Nreal (δ * r₀) A
      ≤ (Nat.ceil c + 1 : ENNReal) * Nreal δ A := h_upper
    _ ≤ ENNReal.ofReal (3 / r₀) * Nreal δ A := by gcongr
  have h5 : ENNReal.ofReal (r₀ / 3) * ENNReal.ofReal (3 / r₀) = 1 := by
    have h6 : 0 ≤ r₀ / 3 := by positivity
    have h7 : 0 ≤ 3 / r₀ := by positivity
    rw [← ENNReal.ofReal_mul h6]
    have h8 : (r₀ / 3) * (3 / r₀) = 1 := by
      field_simp [hr₀_pos.ne'] <;> ring
    rw [h8] <;> simp
  calc ENNReal.ofReal (r₀ / 3) * Nreal (δ * r₀) A
    ≤ ENNReal.ofReal (r₀ / 3) * (ENNReal.ofReal (3 / r₀) * Nreal δ A) := by gcongr
  _ = (ENNReal.ofReal (r₀ / 3) * ENNReal.ofReal (3 / r₀)) * Nreal δ A := by ring
  _ = 1 * Nreal δ A := by rw [h5]
  _ = Nreal δ A := by ring

/-! ### Two-sided bounds for scaling down -/

/-- Two-sided bounds for `N(δ, w·A)` when `0 < w ≤ 1`.

Lower bound: `N(δ, w·A) ≥ (w/3)·N(δ, A)` (via coarsening).
Upper bound: `N(δ, w·A) ≤ (⌈1/w⌉+1)·N(δ, A)` (via refinement). -/
lemma Nreal_scale_down_bounds {δ w : ℝ} (hδ : 0 < δ) (hw_pos : 0 < w)
    (hw_le_one : w ≤ 1) {A : Set ℝ} (hA : IsBounded A) :
    ENNReal.ofReal (w / 3) * Nreal δ A ≤ Nreal δ (scaleSet w A) ∧
    Nreal δ (scaleSet w A) ≤ (Nat.ceil (1 / w) + 1 : ENNReal) * Nreal δ A := by
  have h_scaling : Nreal δ (scaleSet w A) = Nreal (δ / w) A :=
    Nreal_scaling hδ hw_pos hA
  constructor
  · -- Lower bound via coarsening
    rw [h_scaling]
    have h_coarse : Nreal (δ / w) A ≥ ENNReal.ofReal (w / 3) * Nreal ((δ / w) * w) A :=
      Nreal_coarsening (div_pos hδ hw_pos) hw_pos hw_le_one hA
    have h3 : (δ / w) * w = δ := by
      field_simp [hw_pos.ne'] <;> ring
    rw [h3] at h_coarse
    exact h_coarse
  · -- Upper bound via refinement
    rw [h_scaling]
    have h4 : δ ≤ δ / w := by
      have h5 : 0 < w := hw_pos
      have h6 : w ≤ 1 := hw_le_one
      calc δ = δ / 1 := by field_simp
        _ ≤ δ / w := by gcongr
    have h5 : δ / w / δ = 1 / w := by
      field_simp [hδ.ne', hw_pos.ne'] <;> ring
    have h_bound := Nreal_refinement_upper hδ (div_pos hδ hw_pos) h4 hA
    rwa [h5] at h_bound

/-! ### Difference set bound -/

/-- `N(δ, A-A) ≤ 3·N(δ, A)^2`. -/
lemma Nreal_difference_set {δ : ℝ} (hδ : 0 < δ)
    {A : Set ℝ} (hA : IsBounded A) :
    Nreal δ (Set.image2 (· - ·) A A) ≤ 3 * (Nreal δ A)^2 := by
  let I_diff := ProductLikeIncidence.realCubeIndexSet δ (Set.image2 (· - ·) A A)
  let I_A := ProductLikeIncidence.realCubeIndexSet δ A
  have h_bdd_diff : IsBounded (Set.image2 (· - ·) A A) := hA.sub hA
  have h_fin_diff : I_diff.Finite := ProductLikeIncidence.realCubeIndexSet_finite hδ h_bdd_diff
  have h_fin_A : I_A.Finite := ProductLikeIncidence.realCubeIndexSet_finite hδ hA
  let K_diff : Finset ℤ := h_fin_diff.toFinset
  let K_A : Finset ℤ := h_fin_A.toFinset
  have hK_diff : (K_diff : Set ℤ) = I_diff := Set.Finite.coe_toFinset h_fin_diff
  have hK_A : (K_A : Set ℤ) = I_A := Set.Finite.coe_toFinset h_fin_A
  have h_exists : ∀ (m : ℤ), m ∈ I_diff → ∃ (x y : ℝ), x ∈ A ∧ y ∈ A ∧ δ * (m : ℝ) ≤ x - y ∧ x - y < δ * ((m : ℝ) + 1) := by
    intro m hm
    have h_mem := ProductLikeIncidence.realCubeIndexSet_mem_iff.mp hm
    rcases h_mem with ⟨w, hw_img, h1, h2⟩
    rcases hw_img with ⟨x, hxA, y, hyA, rfl⟩
    exact ⟨x, y, hxA, hyA, h1, h2⟩
  let xy : ℤ → ℝ × ℝ := fun m => if h : m ∈ I_diff then
    (Classical.choose (h_exists m h), Classical.choose (Classical.choose_spec (h_exists m h)))
  else (0, 0)
  let i : ℤ → ℤ := fun m => Int.floor ((xy m).1 / δ)
  let j : ℤ → ℤ := fun m => Int.floor ((xy m).2 / δ)
  let f : ℤ → ℤ × ℤ := fun m => (i m, j m)
  have h_xy_prop : ∀ m ∈ I_diff, (xy m).1 ∈ A ∧ (xy m).2 ∈ A ∧ δ * (m : ℝ) ≤ (xy m).1 - (xy m).2 ∧ (xy m).1 - (xy m).2 < δ * ((m : ℝ) + 1) := by
    intro m hm
    have hxy_def : xy m = (Classical.choose (h_exists m hm), Classical.choose (Classical.choose_spec (h_exists m hm))) := by
      simp [xy, dif_pos hm]
    rw [hxy_def]
    exact Classical.choose_spec (Classical.choose_spec (h_exists m hm))
  have h_i_bounds : ∀ m ∈ I_diff, δ * (i m : ℝ) ≤ (xy m).1 ∧ (xy m).1 < δ * ((i m : ℝ) + 1) := by
    intro m hm
    have h1 : δ * (i m : ℝ) ≤ (xy m).1 := by
      dsimp only [i]
      have h2 : (i m : ℝ) ≤ (xy m).1 / δ := Int.floor_le ((xy m).1 / δ)
      have h3 : δ * (i m : ℝ) ≤ δ * ((xy m).1 / δ) := by gcongr
      have h4 : δ * ((xy m).1 / δ) = (xy m).1 := by field_simp [hδ.ne'] <;> ring
      rw [h4] at h3 <;> exact h3
    have h2 : (xy m).1 < δ * ((i m : ℝ) + 1) := by
      dsimp only [i]
      have h3 : (xy m).1 / δ < (i m : ℝ) + 1 := Int.lt_floor_add_one ((xy m).1 / δ)
      have h4 : δ * ((xy m).1 / δ) < δ * ((i m : ℝ) + 1) := by gcongr
      have h5 : δ * ((xy m).1 / δ) = (xy m).1 := by field_simp [hδ.ne'] <;> ring
      rw [h5] at h4 <;> exact h4
    exact ⟨h1, h2⟩
  have h_j_bounds : ∀ m ∈ I_diff, δ * (j m : ℝ) ≤ (xy m).2 ∧ (xy m).2 < δ * ((j m : ℝ) + 1) := by
    intro m hm
    have h1 : δ * (j m : ℝ) ≤ (xy m).2 := by
      dsimp only [j]
      have h2 : (j m : ℝ) ≤ (xy m).2 / δ := Int.floor_le ((xy m).2 / δ)
      have h3 : δ * (j m : ℝ) ≤ δ * ((xy m).2 / δ) := by gcongr
      have h4 : δ * ((xy m).2 / δ) = (xy m).2 := by field_simp [hδ.ne'] <;> ring
      rw [h4] at h3 <;> exact h3
    have h2 : (xy m).2 < δ * ((j m : ℝ) + 1) := by
      dsimp only [j]
      have h3 : (xy m).2 / δ < (j m : ℝ) + 1 := Int.lt_floor_add_one ((xy m).2 / δ)
      have h4 : δ * ((xy m).2 / δ) < δ * ((j m : ℝ) + 1) := by gcongr
      have h5 : δ * ((xy m).2 / δ) = (xy m).2 := by field_simp [hδ.ne'] <;> ring
      rw [h5] at h4 <;> exact h4
    exact ⟨h1, h2⟩
  have h_f_in : ∀ m ∈ K_diff, f m ∈ K_A ×ˢ K_A := by
    intro m hm
    have hm' : m ∈ I_diff := by
      have h : m ∈ (K_diff : Set ℤ) := hm
      rw [hK_diff] at h <;> exact h
    have hxp := h_xy_prop m hm'
    have hib := h_i_bounds m hm'
    have hjb := h_j_bounds m hm'
    have h_i_in : i m ∈ I_A := by
      dsimp only [I_A, ProductLikeIncidence.realCubeIndexSet]
      exact ⟨(xy m).1, ⟨hib, hxp.1⟩⟩
    have h_j_in : j m ∈ I_A := by
      dsimp only [I_A, ProductLikeIncidence.realCubeIndexSet]
      exact ⟨(xy m).2, ⟨hjb, hxp.2.1⟩⟩
    have h_i_in' : i m ∈ K_A := by
      have h : i m ∈ (K_A : Set ℤ) := by rw [hK_A] <;> exact h_i_in
      exact h
    have h_j_in' : j m ∈ K_A := by
      have h : j m ∈ (K_A : Set ℤ) := by rw [hK_A] <;> exact h_j_in
      exact h
    exact Finset.mem_product.mpr ⟨h_i_in', h_j_in'⟩
  have h_fiber3 : ∀ (p : ℤ × ℤ), p ∈ K_A ×ˢ K_A → (K_diff.filter (fun m => f m = p)).card ≤ 3 := by
    intro p hp
    let S := K_diff.filter (fun m => f m = p)
    have hS : ∀ m ∈ S, p.1 - p.2 - 1 ≤ m ∧ m ≤ p.1 - p.2 + 1 := by
      intro m hm
      have h_m_in : m ∈ I_diff := by
        have h : m ∈ K_diff := (Finset.mem_filter.mp hm).1
        have h' : m ∈ (K_diff : Set ℤ) := h
        rw [hK_diff] at h' <;> exact h'
      have h_f_eq : f m = p := (Finset.mem_filter.mp hm).2
      have hxp := h_xy_prop m h_m_in
      have h_i_eq : i m = p.1 := (Prod.ext_iff.mp h_f_eq).1
      have h_j_eq : j m = p.2 := (Prod.ext_iff.mp h_f_eq).2
      have hib := h_i_bounds m h_m_in
      have hjb := h_j_bounds m h_m_in
      have h1 : δ * (p.1 : ℝ) ≤ (xy m).1 := by rw [←h_i_eq] <;> exact hib.1
      have h2 : (xy m).1 < δ * ((p.1 : ℝ) + 1) := by rw [←h_i_eq] <;> exact hib.2
      have h3 : δ * (p.2 : ℝ) ≤ (xy m).2 := by rw [←h_j_eq] <;> exact hjb.1
      have h4 : (xy m).2 < δ * ((p.2 : ℝ) + 1) := by rw [←h_j_eq] <;> exact hjb.2
      have h5 : δ * (m : ℝ) ≤ (xy m).1 - (xy m).2 := hxp.2.2.1
      have h6 : (xy m).1 - (xy m).2 < δ * ((m : ℝ) + 1) := hxp.2.2.2
      constructor
      · -- p.1 - p.2 - 1 ≤ m
        have h7 : δ * ((p.1 : ℝ) - (p.2 : ℝ) - 1) < (xy m).1 - (xy m).2 := by nlinarith
        have h8 : (p.1 : ℝ) - (p.2 : ℝ) - 1 < (m : ℝ) + 1 := by nlinarith
        exact Int.le_of_lt_add_one (by exact_mod_cast h8)
      · -- m ≤ p.1 - p.2 + 1
        have h7 : (xy m).1 - (xy m).2 < δ * ((p.1 : ℝ) - (p.2 : ℝ) + 1) := by nlinarith
        have h8 : (m : ℝ) < (p.1 : ℝ) - (p.2 : ℝ) + 1 := by nlinarith
        have h9 : m ≤ p.1 - p.2 := Int.le_of_lt_add_one (by exact_mod_cast h8)
        linarith
    have h_sub : S ⊆ Finset.Icc (p.1 - p.2 - 1) (p.1 - p.2 + 1) := by
      intro m hm
      exact Finset.mem_Icc.mpr (hS m hm)
    have h_card : S.card ≤ (Finset.Icc (p.1 - p.2 - 1) (p.1 - p.2 + 1)).card := Finset.card_le_card h_sub
    have h_Icc_card : (Finset.Icc (p.1 - p.2 - 1) (p.1 - p.2 + 1)).card = 3 := by
      let a := p.1 - p.2 - 1
      have h_shift : p.1 - p.2 + 1 = a + 2 := by omega
      have h_eq : Finset.Icc a (a + 2) = Finset.image (fun k : ℕ => a + (k : ℤ)) (Finset.range 3) := by
        ext z
        simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨h1, h2⟩
          have h3 : 0 ≤ z - a := by linarith
          have h4 : z - a ≤ 2 := by linarith
          let k : ℕ := (z - a).toNat
          have hk : (k : ℤ) = z - a := by
            simp [k, Int.toNat_of_nonneg h3]
          have h5 : k < 3 := by omega
          exact ⟨k, h5, by linarith⟩
        · rintro ⟨k, hk, rfl⟩
          have h6 : (k : ℤ) < 3 := by exact_mod_cast hk
          have h7 : (k : ℤ) ≥ 0 := by exact_mod_cast Nat.zero_le k
          constructor <;> linarith
      have h_target : Finset.Icc (p.1 - p.2 - 1) (p.1 - p.2 + 1) = Finset.Icc a (a + 2) := by
        congr <;> omega
      rw [h_target, h_eq]
      have h_inj : Set.InjOn (fun k : ℕ => a + (k : ℤ)) (Finset.range 3) := by
        intro k1 _ k2 _ h
        simpa using h
      rw [Finset.card_image_of_injOn h_inj, Finset.card_range] <;> norm_num
    rw [h_Icc_card] at h_card
    exact h_card
  have h_main_card : K_diff.card ≤ 3 * (K_A.card)^2 := by
    have h := finset_card_le_mul_of_bounded_fibers h_f_in h_fiber3
    have h_prod_card : (K_A ×ˢ K_A).card = K_A.card * K_A.card := by
      rw [Finset.card_product] <;> ring
    rw [h_prod_card] at h
    <;> ring_nf at h ⊢ <;> exact h
  have h_enc_diff : (I_diff.encard : ENNReal) = ↑K_diff.card := by
    exact_mod_cast Set.Finite.encard_eq_coe_toFinset_card h_fin_diff
  have h_enc_A : (I_A.encard : ENNReal) = ↑K_A.card := by
    exact_mod_cast Set.Finite.encard_eq_coe_toFinset_card h_fin_A
  have h1 : Nreal δ (Set.image2 (· - ·) A A) = (I_diff.encard : ENNReal) := by
    have h := ProductLikeIncidence.realCoveringNumber_eq_card_ennreal hδ h_bdd_diff
    have h' : Nreal δ (Set.image2 (· - ·) A A) =
        ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (· - ·) A A))) := by rfl
    rw [h'] <;> exact h
  have h2 : Nreal δ A = (I_A.encard : ENNReal) := by
    have h := ProductLikeIncidence.realCoveringNumber_eq_card_ennreal hδ hA
    have h' : Nreal δ A =
        ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A)) := by rfl
    rw [h'] <;> exact h
  rw [h1, h2, h_enc_diff, h_enc_A]
  exact_mod_cast h_main_card

end WeakTwoEndsSumProduct
