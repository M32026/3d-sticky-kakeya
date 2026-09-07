module

/-
# Iterative Weight Elimination Theorem

Given the one-step Expansion Lemma (Lemma 3.2), iterate it n-1 times
to eliminate all but one weight, concluding positive volume of a set
of the form N·A^(N) - N·A^(N).
-/

public import MyLeanRepo.ExpansionLemma
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Metric
open scoped BigOperators Pointwise

namespace WeakTwoEndsSumProduct

/-! ## Local aliases for ExpansionLemma.iteratedSumset recursion -/

lemma iteratedSumset_zero {T : Set ℝ} : ExpansionLemma.iteratedSumset T 0 = {0} := by
  simp [ExpansionLemma.iteratedSumset]

lemma iteratedSumset_succ {T : Set ℝ} {n : ℕ} :
    ExpansionLemma.iteratedSumset T (n + 1) = Set.image2 (· + ·) T (ExpansionLemma.iteratedSumset T n) := by
  simp [ExpansionLemma.iteratedSumset]

/-! ## Basic properties -/

lemma iteratedSumset_one {T : Set ℝ} :
    ExpansionLemma.iteratedSumset T 1 = T := by
  ext x
  simp [ExpansionLemma.iteratedSumset, iteratedSumset_zero]
  <;> aesop

lemma productSet_one {A : Set ℝ} :
    ExpansionLemma.productSet A 1 = A := by
  ext x
  simp only [ExpansionLemma.productSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨f, hf, rfl⟩
    have h : ∏ i : Fin 1, f i = f 0 := by simp
    rw [h]; exact hf 0
  · intro hx
    refine ⟨fun _ => x, fun _ => hx, ?_⟩
    simp

lemma iteratedSumset_mono {S T : Set ℝ} {N : ℕ} (h : S ⊆ T) :
    ExpansionLemma.iteratedSumset S N ⊆ ExpansionLemma.iteratedSumset T N := by
  induction N with
  | zero => simp [ExpansionLemma.iteratedSumset]
  | succ N ih =>
    rw [iteratedSumset_succ, iteratedSumset_succ]
    intro z hz
    rcases hz with ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, h ha, b, ih hb, rfl⟩

lemma iteratedDifference_subset' {S T : Set ℝ} {N : ℕ} (h : S ⊆ T) :
    ExpansionLemma.iteratedDifference S N ⊆ ExpansionLemma.iteratedDifference T N := by
  have h1 : ExpansionLemma.iteratedSumset S N ⊆ ExpansionLemma.iteratedSumset T N :=
    iteratedSumset_mono (N := N) h
  intro z hz
  rcases hz with ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, h1 ha, b, h1 hb, rfl⟩

/-! ## iteratedSumset_add -/

lemma iteratedSumset_add {T : Set ℝ} {P Q : ℕ} {x y : ℝ}
    (hx : x ∈ ExpansionLemma.iteratedSumset T P)
    (hy : y ∈ ExpansionLemma.iteratedSumset T Q) :
    x + y ∈ ExpansionLemma.iteratedSumset T (P + Q) := by
  have h_main : ∀ (Q : ℕ), ∀ (P : ℕ) (x y : ℝ),
      x ∈ ExpansionLemma.iteratedSumset T P →
      y ∈ ExpansionLemma.iteratedSumset T Q →
      x + y ∈ ExpansionLemma.iteratedSumset T (P + Q) := by
    intro Q
    induction Q with
    | zero =>
      intro P x y hx hy
      have hy_eq : y = 0 := by simpa [ExpansionLemma.iteratedSumset] using hy
      rw [hy_eq, add_zero]
      simpa using hx
    | succ Q ih =>
      intro P x y hx hy
      rw [iteratedSumset_succ] at hy
      rcases hy with ⟨a, ha, y', hy', h_eq⟩
      have h_eq' : a + y' = y := by simpa using h_eq
      have h1 : x + a ∈ ExpansionLemma.iteratedSumset T (P + 1) := by
        rw [iteratedSumset_succ]
        exact ⟨a, ha, x, hx, by ring⟩
      have h2 := ih (P + 1) (x + a) y' h1 hy'
      have h3 : (P + 1) + Q = P + (Q + 1) := by ring
      rw [h3] at h2
      have h4 : (x + a) + y' = x + y := by
        rw [← h_eq'] <;> ring
      rw [h4] at h2
      exact h2
  exact h_main Q P x y hx hy

/-! ## Multiplication lemmas -/

lemma mul_left_iteratedSumset {B : Set ℝ} {b : ℝ} {M : ℕ} {x : ℝ}
    (hb : b ∈ B) (hx : x ∈ ExpansionLemma.iteratedSumset B M) :
    b * x ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet B 2) M := by
  have h_main : ∀ (M : ℕ) (y : ℝ), y ∈ ExpansionLemma.iteratedSumset B M →
      b * y ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet B 2) M := by
    intro M
    induction M with
    | zero =>
      intro y hy
      have hy_eq : y = 0 := by simpa [ExpansionLemma.iteratedSumset] using hy
      rw [hy_eq, mul_zero]
      simp [ExpansionLemma.iteratedSumset]
    | succ M ih =>
      intro y hy
      rw [iteratedSumset_succ] at hy
      rcases hy with ⟨a, ha, y', hy', h_eq⟩
      have h_eq' : a + y' = y := by simpa using h_eq
      have h1 : b * a ∈ ExpansionLemma.productSet B 2 := by
        refine ⟨fun i : Fin 2 => if i = 0 then b else a, ?_, ?_⟩
        · intro i; fin_cases i <;> simp [ha, hb]
        · simp [Fin.prod_univ_two]
      have h2 : b * y' ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet B 2) M := ih y' hy'
      have h_goal : b * y = b * a + b * y' := by
        rw [← h_eq'] <;> ring
      rw [h_goal, iteratedSumset_succ]
      exact ⟨b * a, h1, b * y', h2, by ring⟩
  exact h_main M x hx

lemma product_of_iteratedSumsets {B : Set ℝ} {M N : ℕ} {u w : ℝ}
    (hu : u ∈ ExpansionLemma.iteratedSumset B M)
    (hw : w ∈ ExpansionLemma.iteratedSumset B N) :
    u * w ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet B 2) (M * N) := by
  have h_main : ∀ (N : ℕ) (z : ℝ), z ∈ ExpansionLemma.iteratedSumset B N →
      u * z ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet B 2) (M * N) := by
    intro N
    induction N with
    | zero =>
      intro z hz
      have hz_eq : z = 0 := by simpa [ExpansionLemma.iteratedSumset] using hz
      rw [hz_eq, mul_zero]
      simp [ExpansionLemma.iteratedSumset]
    | succ N ih =>
      intro z hz
      rw [iteratedSumset_succ] at hz
      rcases hz with ⟨b, hb, z', hz', h_eq⟩
      have h_eq' : b + z' = z := by simpa using h_eq
      have h1 : u * b ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet B 2) M := by
        have h_comm : u * b = b * u := by ring
        rw [h_comm]
        exact mul_left_iteratedSumset hb hu
      have h2 : u * z' ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet B 2) (M * N) := ih z' hz'
      have h_goal : u * z = u * b + u * z' := by
        rw [← h_eq'] <;> ring
      rw [h_goal]
      have h3 := iteratedSumset_add h1 h2
      have h4 : M + M * N = M * (N + 1) := by ring
      rw [h4] at h3
      exact h3
  exact h_main N w hw

/-! ## Product-of-sums expansion -/

lemma product_sum_expansion (B : Set ℝ) (M : ℕ) :
    ExpansionLemma.productSet (ExpansionLemma.iteratedDifference B M) 2 ⊆
    ExpansionLemma.iteratedDifference (ExpansionLemma.productSet B 2) (2 * M * M) := by
  intro z hz
  rcases hz with ⟨f, hf, h_z_eq⟩
  rcases hf 0 with ⟨u, hu, v, hv, hx_eq⟩
  rcases hf 1 with ⟨w, hw, z', hz', hy_eq⟩
  have h1 : u * w ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet B 2) (M * M) :=
    product_of_iteratedSumsets hu hw
  have h2 : v * z' ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet B 2) (M * M) :=
    product_of_iteratedSumsets hv hz'
  have h3 : u * z' ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet B 2) (M * M) :=
    product_of_iteratedSumsets hu hz'
  have h4 : v * w ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet B 2) (M * M) :=
    product_of_iteratedSumsets hv hw
  have h_pos : u * w + v * z' ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet B 2) (2 * M * M) := by
    have h5 := iteratedSumset_add h1 h2
    have h6 : M * M + M * M = 2 * M * M := by ring
    rw [h6] at h5; exact h5
  have h_neg : u * z' + v * w ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet B 2) (2 * M * M) := by
    have h5 := iteratedSumset_add h3 h4
    have h6 : M * M + M * M = 2 * M * M := by ring
    rw [h6] at h5; exact h5
  have h_f0 : f 0 = u - v := hx_eq.symm
  have h_f1 : f 1 = w - z' := hy_eq.symm
  have h_prod : ∏ i : Fin 2, f i = f 0 * f 1 := by simp [Fin.prod_univ_two]
  have h_z : z = (u - v) * (w - z') := by
    calc z = ∏ i : Fin 2, f i := h_z_eq
       _ = f 0 * f 1 := h_prod
       _ = (u - v) * (w - z') := by rw [h_f0, h_f1]
  have h_final : (u - v) * (w - z') = (u * w + v * z') - (u * z' + v * w) := by ring
  rw [h_z, h_final]
  exact ⟨u * w + v * z', h_pos, u * z' + v * w, h_neg, rfl⟩

/-- Product of two iterated sumsets lies in iterated sumset of pointwise products. -/
lemma mul_iteratedSumsets {S T : Set ℝ} {P Q : ℕ} {a b : ℝ}
    (ha : a ∈ ExpansionLemma.iteratedSumset S P)
    (hb : b ∈ ExpansionLemma.iteratedSumset T Q) :
    a * b ∈ ExpansionLemma.iteratedSumset (Set.image2 (· * ·) S T) (P * Q) := by
  have h1 : ∀ (Q' : ℕ) (b : ℝ), b ∈ ExpansionLemma.iteratedSumset T Q' →
      ∀ (s : ℝ), s ∈ S →
      s * b ∈ ExpansionLemma.iteratedSumset (Set.image2 (· * ·) S T) Q' := by
    intro Q'
    induction Q' with
    | zero =>
      intro b hb s hs
      have hb0 : b = 0 := by simpa [ExpansionLemma.iteratedSumset] using hb
      have h : s * b = 0 := by rw [hb0]; ring
      rw [h]
      simp [ExpansionLemma.iteratedSumset]
    | succ Q' ih2 =>
      intro b hb s hs
      rw [iteratedSumset_succ] at hb
      rcases hb with ⟨t, ht, b', hb', h_eq2⟩
      have h_eq2' : t + b' = b := by simpa using h_eq2
      have h_st : s * t ∈ Set.image2 (· * ·) S T := ⟨s, hs, t, ht, rfl⟩
      have h_ih : s * b' ∈ ExpansionLemma.iteratedSumset (Set.image2 (· * ·) S T) Q' := ih2 b' hb' s hs
      have h_goal : s * b = s * t + s * b' := by rw [← h_eq2'] <;> ring
      rw [h_goal, iteratedSumset_succ]
      exact ⟨s * t, h_st, s * b', h_ih, by ring⟩
  have h_main : ∀ (P : ℕ), ∀ (a : ℝ), a ∈ ExpansionLemma.iteratedSumset S P →
      ∀ (b : ℝ), b ∈ ExpansionLemma.iteratedSumset T Q →
      a * b ∈ ExpansionLemma.iteratedSumset (Set.image2 (· * ·) S T) (P * Q) := by
    intro P
    induction P with
    | zero =>
      intro a ha b hb
      have ha0 : a = 0 := by simpa [ExpansionLemma.iteratedSumset] using ha
      have h : a * b = 0 := by rw [ha0]; ring
      rw [h]
      simp [ExpansionLemma.iteratedSumset]
    | succ P ih =>
      intro a ha b hb
      rw [iteratedSumset_succ] at ha
      rcases ha with ⟨s, hs, a', ha', h_eq⟩
      have h_eq' : s + a' = a := by simpa using h_eq
      have h_sb : s * b ∈ ExpansionLemma.iteratedSumset (Set.image2 (· * ·) S T) Q := h1 Q b hb s hs
      have h2 : a' * b ∈ ExpansionLemma.iteratedSumset (Set.image2 (· * ·) S T) (P * Q) := ih a' ha' b hb
      have h3 : a * b = s * b + a' * b := by rw [← h_eq'] <;> ring
      rw [h3]
      have h4 := iteratedSumset_add h_sb h2
      have h5 : Q + P * Q = (P + 1) * Q := by ring
      rw [h5] at h4
      exact h4
  exact h_main P a ha b hb

/-- Product of d iterated sumsets of T lies in iterated sumset of productSet T d. -/
lemma product_of_d_iteratedSumsets {T : Set ℝ} {d N : ℕ} {f : Fin d → ℝ}
    (hf : ∀ i, f i ∈ ExpansionLemma.iteratedSumset T N) :
    ∏ i : Fin d, f i ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet T d) (N ^ d) := by
  induction d with
  | zero =>
    simp [ExpansionLemma.iteratedSumset, ExpansionLemma.productSet]
  | succ d ih =>
    have h_prod : ∏ i : Fin (d + 1), f i = (f 0) * ∏ i : Fin d, f (Fin.succ i) := by
      rw [Fin.prod_univ_succ]
      <;> rfl
    rw [h_prod]
    have h1 : f 0 ∈ ExpansionLemma.iteratedSumset T N := hf 0
    have h2 : (∏ i : Fin d, f (Fin.succ i)) ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet T d) (N ^ d) :=
      ih (fun i => hf (Fin.succ i))
    have h3 := mul_iteratedSumsets h1 h2
    have h4 : Set.image2 (· * ·) T (ExpansionLemma.productSet T d) ⊆ ExpansionLemma.productSet T (d + 1) := by
      intro z hz
      rcases hz with ⟨t, ht, p, hp, rfl⟩
      rcases hp with ⟨g, hg, rfl⟩
      let h_arr : Fin (d + 1) → ℝ := fun i => if h : i = 0 then t else g (i.pred h)
      have hh : ∀ i, h_arr i ∈ T := by
        intro i
        by_cases h2 : i = 0
        · have h_eq : h_arr i = t := by simp [h_arr, h2]
          rw [h_eq]; exact ht
        · have h_eq : h_arr i = g (i.pred h2) := by simp [h_arr, h2]
          rw [h_eq]; exact hg (i.pred h2)
      have h_prod : ∏ i : Fin (d + 1), h_arr i = t * ∏ i : Fin d, g i := by
        rw [Fin.prod_univ_succ] <;> simp [h_arr] <;> rfl
      exact ⟨h_arr, hh, h_prod.symm⟩
    have h5 : (f 0) * (∏ i : Fin d, f (Fin.succ i)) ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet T (d + 1)) (N * N ^ d) :=
      iteratedSumset_mono (N := N * N ^ d) h4 h3
    have h6 : N * N ^ d = N ^ (d + 1) := by ring
    rw [h6] at h5
    exact h5

/-- Padding: iteratedDifference T N ⊆ iteratedDifference T (N + N) without Nonempty assumption. -/
lemma iteratedDifference_double {T : Set ℝ} {N : ℕ} :
    ExpansionLemma.iteratedDifference T N ⊆ ExpansionLemma.iteratedDifference T (N + N) := by
  by_cases h : (ExpansionLemma.iteratedSumset T N).Nonempty
  · rcases h with ⟨c, hc⟩
    intro x hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    have ha' : a + c ∈ ExpansionLemma.iteratedSumset T (N + N) := iteratedSumset_add ha hc
    have hb' : b + c ∈ ExpansionLemma.iteratedSumset T (N + N) := iteratedSumset_add hb hc
    have h_eq : (a + c) - (b + c) = a - b := by ring
    exact ⟨a + c, ha', b + c, hb', h_eq⟩
  · have h_empty' : ExpansionLemma.iteratedSumset T N = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h_empty : ExpansionLemma.iteratedDifference T N = ∅ := by
      rw [ExpansionLemma.iteratedDifference, h_empty'] <;> simp
    rw [h_empty] <;> intro x hx <;> simp at hx

/-- Generalized product-of-differences expansion. -/
lemma product_sum_expansion_gen (T : Set ℝ) (N d : ℕ) (hd : 0 < d) :
    ExpansionLemma.productSet (ExpansionLemma.iteratedDifference T N) d ⊆
    ExpansionLemma.iteratedDifference (ExpansionLemma.productSet T d) (2 ^ d * N ^ d) := by
  have h_main : ∀ (d : ℕ), 0 < d →
      ExpansionLemma.productSet (ExpansionLemma.iteratedDifference T N) d ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet T d) (2 ^ d * N ^ d) := by
    intro d hd
    induction d with
    | zero => exfalso; linarith
    | succ d ih =>
      intro z hz
      by_cases h_d0 : d = 0
      · -- d+1 = 1
        have h_d_eq : d = 0 := h_d0
        have h1 : ExpansionLemma.productSet (ExpansionLemma.iteratedDifference T N) (d + 1) = ExpansionLemma.iteratedDifference T N := by
          rw [h_d_eq]; simp [productSet_one]
        rw [h1] at hz
        have h2 : ExpansionLemma.productSet T (d + 1) = T := by
          rw [h_d_eq]; simp [productSet_one]
        have h_exp : N + N = (2 ^ 1 * N ^ 1) := by
          simp [pow_one, two_mul] <;> ring
        have h_pad : z ∈ ExpansionLemma.iteratedDifference T (N + N) := iteratedDifference_double hz
        rw [h_exp] at h_pad
        have h_goal_exp : 2 ^ (d + 1) * N ^ (d + 1) = 2 ^ 1 * N ^ 1 := by
          rw [h_d_eq]
        rw [h2, h_goal_exp]
        exact h_pad
      · -- d ≥ 1
        have h_d_pos : 0 < d := by omega
        rcases hz with ⟨f, hf, rfl⟩
        let x : ℝ := f 0
        let g : Fin d → ℝ := fun i => f (Fin.succ i)
        have hx : x ∈ ExpansionLemma.iteratedDifference T N := hf 0
        have hg : ∀ i, g i ∈ ExpansionLemma.iteratedDifference T N := fun i => hf (Fin.succ i)
        have h_prod : ∏ i : Fin (d + 1), f i = x * ∏ i : Fin d, g i := by
          rw [Fin.prod_univ_succ] <;> rfl
        rw [h_prod]
        rcases hx with ⟨ux, hux, vx, hvx, hx_eq⟩
        have h_x_eq : x = ux - vx := hx_eq.symm
        rw [h_x_eq]
        have h_y_in : (∏ i : Fin d, g i) ∈ ExpansionLemma.productSet (ExpansionLemma.iteratedDifference T N) d := by
          exact ⟨g, hg, rfl⟩
        rcases ih h_d_pos h_y_in with ⟨uy, huy, vy, hvy, hy_eq⟩
        have h_y_eq : (∏ i : Fin d, g i) = uy - vy := hy_eq.symm
        rw [h_y_eq]
        have h4 : Set.image2 (· * ·) T (ExpansionLemma.productSet T d) ⊆ ExpansionLemma.productSet T (d + 1) := by
          intro z hz
          rcases hz with ⟨t, ht, p, hp, rfl⟩
          rcases hp with ⟨q, hq, rfl⟩
          let h_arr2 : Fin (d + 1) → ℝ := fun i => if h : i = 0 then t else q (i.pred h)
          have hh2 : ∀ i, h_arr2 i ∈ T := by
            intro i
            by_cases h2 : i = 0
            · have h_eq : h_arr2 i = t := by simp [h_arr2, h2]
              rw [h_eq]; exact ht
            · have h_eq : h_arr2 i = q (i.pred h2) := by simp [h_arr2, h2]
              rw [h_eq]; exact hq (i.pred h2)
          have h_prod2 : ∏ i : Fin (d + 1), h_arr2 i = t * ∏ i : Fin d, q i := by
            rw [Fin.prod_univ_succ] <;> simp [h_arr2] <;> rfl
          exact ⟨h_arr2, hh2, h_prod2.symm⟩
        have h_ux_uy : ux * uy ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet T (d + 1)) (N * (2 ^ d * N ^ d)) := by
          have h := mul_iteratedSumsets hux huy
          exact iteratedSumset_mono (N := N * (2 ^ d * N ^ d)) h4 h
        have h_vx_vy : vx * vy ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet T (d + 1)) (N * (2 ^ d * N ^ d)) := by
          have h := mul_iteratedSumsets hvx hvy
          exact iteratedSumset_mono (N := N * (2 ^ d * N ^ d)) h4 h
        have h_ux_vy : ux * vy ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet T (d + 1)) (N * (2 ^ d * N ^ d)) := by
          have h := mul_iteratedSumsets hux hvy
          exact iteratedSumset_mono (N := N * (2 ^ d * N ^ d)) h4 h
        have h_vx_uy : vx * uy ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet T (d + 1)) (N * (2 ^ d * N ^ d)) := by
          have h := mul_iteratedSumsets hvx huy
          exact iteratedSumset_mono (N := N * (2 ^ d * N ^ d)) h4 h
        have h_sum_exp : N * (2 ^ d * N ^ d) + N * (2 ^ d * N ^ d) = 2 * (N * (2 ^ d * N ^ d)) := by ring
        have h_pos : ux * uy + vx * vy ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet T (d + 1)) (2 * (N * (2 ^ d * N ^ d))) := by
          have h := iteratedSumset_add h_ux_uy h_vx_vy
          rw [h_sum_exp] at h
          exact h
        have h_neg : ux * vy + vx * uy ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet T (d + 1)) (2 * (N * (2 ^ d * N ^ d))) := by
          have h := iteratedSumset_add h_ux_vy h_vx_uy
          rw [h_sum_exp] at h
          exact h
        have h_final : (ux - vx) * (uy - vy) = (ux * uy + vx * vy) - (ux * vy + vx * uy) := by ring
        rw [h_final]
        have h_eq : 2 * (N * (2 ^ d * N ^ d)) = 2 ^ (d + 1) * N ^ (d + 1) := by ring
        rw [h_eq] at h_pos h_neg
        exact ⟨ux * uy + vx * vy, h_pos, ux * vy + vx * uy, h_neg, rfl⟩
  exact h_main d hd

/-! ## ProductSet nesting -/

lemma productSet_productSet_contain (A : Set ℝ) (d : ℕ) :
    ExpansionLemma.productSet (ExpansionLemma.productSet A d) 2 ⊆
    ExpansionLemma.productSet A (d + d) := by
  intro z hz
  rcases hz with ⟨f, hf, h_z_eq⟩
  rcases hf 0 with ⟨a, ha, h_a_eq⟩
  rcases hf 1 with ⟨b, hb, h_b_eq⟩
  let g : Fin (d + d) → ℝ := fun i =>
    if h : i.val < d then a ⟨i.val, h⟩ else b ⟨i.val - d, by omega⟩
  have hg : ∀ i, g i ∈ A := by
    intro i
    by_cases h : i.val < d
    · have h' : g i = a ⟨i.val, h⟩ := by
        simp only [g, dif_pos h]
      rw [h']; exact ha ⟨i.val, h⟩
    · have h' : g i = b ⟨i.val - d, by omega⟩ := by
        simp only [g, dif_neg h]
      rw [h']; exact hb ⟨i.val - d, by omega⟩
  have h1 : ∀ (i : Fin d), g (Fin.castAdd d i) = a i := by
    intro i
    have h_val : (Fin.castAdd d i).val = i.val := by exact Fin.val_castAdd d i
    have h_lt : (Fin.castAdd d i).val < d := by rw [h_val]; exact i.is_lt
    have h_goal : g (Fin.castAdd d i) = a ⟨(Fin.castAdd d i).val, h_lt⟩ := by
      dsimp only [g]; rw [dif_pos h_lt]
    have h_fin : (⟨(Fin.castAdd d i).val, h_lt⟩ : Fin d) = i := by
      apply Fin.ext; rw [h_val]
    rw [h_goal, h_fin]
  have h2 : ∀ (i : Fin d), g (Fin.natAdd d i) = b i := by
    intro i
    have h_val : (Fin.natAdd d i).val = d + i.val := by exact Fin.val_natAdd d i
    have h_nlt : ¬(Fin.natAdd d i).val < d := by rw [h_val]; omega
    have h_goal : g (Fin.natAdd d i) = b ⟨(Fin.natAdd d i).val - d, by omega⟩ := by
      dsimp only [g]; rw [dif_neg h_nlt]
    have h_sub : (Fin.natAdd d i).val - d = i.val := by
      rw [h_val] <;> omega
    have h_fin : (⟨(Fin.natAdd d i).val - d, by omega⟩ : Fin d) = i := by
      apply Fin.ext
      simpa using h_sub
    rw [h_goal, h_fin]
  have h_split : ∏ i : Fin (d + d), g i =
      (∏ i : Fin d, g (Fin.castAdd d i)) * (∏ i : Fin d, g (Fin.natAdd d i)) :=
    Fin.prod_univ_add g
  have h_eq : ∏ i : Fin (d + d), g i = (∏ i : Fin d, a i) * (∏ i : Fin d, b i) := by
    rw [h_split]
    have h1' : ∏ i : Fin d, g (Fin.castAdd d i) = ∏ i : Fin d, a i := by
      apply Finset.prod_congr rfl; intro x _; exact h1 x
    have h2' : ∏ i : Fin d, g (Fin.natAdd d i) = ∏ i : Fin d, b i := by
      apply Finset.prod_congr rfl; intro x _; exact h2 x
    rw [h1', h2']
  have h_prod : ∏ i : Fin 2, f i = f 0 * f 1 := by simp [Fin.prod_univ_two]
  have h_z : z = (∏ i : Fin d, a i) * (∏ i : Fin d, b i) := by
    calc z = ∏ i : Fin 2, f i := h_z_eq
       _ = f 0 * f 1 := h_prod
       _ = (∏ i : Fin d, a i) * (∏ i : Fin d, b i) := by rw [h_a_eq, h_b_eq]
  rw [h_z]
  exact ⟨g, hg, h_eq.symm⟩

/-! ## Containment lemmas -/

lemma sumset_subset_difference {S T : Set ℝ} {P N : ℕ}
    (h : S ⊆ ExpansionLemma.iteratedDifference T P) :
    ExpansionLemma.iteratedSumset S N ⊆
    ExpansionLemma.iteratedDifference T (N * P) := by
  have h_ind : ∀ (N : ℕ),
      ExpansionLemma.iteratedSumset S N ⊆ ExpansionLemma.iteratedDifference T (N * P) := by
    intro N
    induction N with
    | zero =>
      intro x hx
      have hx0 : x = 0 := by simpa [ExpansionLemma.iteratedSumset] using hx
      rw [hx0]
      simp [ExpansionLemma.iteratedDifference, ExpansionLemma.iteratedSumset]
    | succ N ih =>
      intro z hz
      rw [iteratedSumset_succ] at hz
      rcases hz with ⟨s, hs, x', hx', h_eq⟩
      have h_eq' : s + x' = z := by simpa using h_eq
      rcases h hs with ⟨a_s, ha_s, b_s, hb_s, h_s_eq⟩
      rcases ih hx' with ⟨a_x, ha_x, b_x, hb_x, h_x_eq⟩
      have h_s_eq' : a_s - b_s = s := by simpa using h_s_eq
      have h_x_eq' : a_x - b_x = x' := by simpa using h_x_eq
      have h1 : a_s + a_x ∈ ExpansionLemma.iteratedSumset T (P + N * P) :=
        iteratedSumset_add ha_s ha_x
      have h2 : b_s + b_x ∈ ExpansionLemma.iteratedSumset T (P + N * P) :=
        iteratedSumset_add hb_s hb_x
      have h3 : P + N * P = (N + 1) * P := by ring
      rw [h3] at h1 h2
      have h4 : z = (a_s + a_x) - (b_s + b_x) := by
        rw [← h_eq', ← h_s_eq', ← h_x_eq'] <;> ring
      rw [h4]
      exact ⟨a_s + a_x, h1, b_s + b_x, h2, rfl⟩
  exact h_ind N

lemma iteratedDifference_of_subset_difference {S T : Set ℝ} {P N : ℕ}
    (h : S ⊆ ExpansionLemma.iteratedDifference T P) :
    ExpansionLemma.iteratedDifference S N ⊆
    ExpansionLemma.iteratedDifference T (2 * N * P) := by
  intro z hz
  rcases hz with ⟨x, hx, y, hy, h_z_eq⟩
  have h_z_eq' : x - y = z := by simpa using h_z_eq
  have hx' : x ∈ ExpansionLemma.iteratedDifference T (N * P) :=
    sumset_subset_difference h hx
  have hy' : y ∈ ExpansionLemma.iteratedDifference T (N * P) :=
    sumset_subset_difference h hy
  rcases hx' with ⟨a, ha, b, hb, h_x_eq⟩
  rcases hy' with ⟨c, hc, d, hd, h_y_eq⟩
  have h_x_eq' : a - b = x := by simpa using h_x_eq
  have h_y_eq' : c - d = y := by simpa using h_y_eq
  have h1 : a + d ∈ ExpansionLemma.iteratedSumset T (N * P + N * P) :=
    iteratedSumset_add ha hd
  have h2 : b + c ∈ ExpansionLemma.iteratedSumset T (N * P + N * P) :=
    iteratedSumset_add hb hc
  have h3 : N * P + N * P = 2 * N * P := by ring
  rw [h3] at h1 h2
  have h4 : z = (a + d) - (b + c) := by
    rw [← h_z_eq', ← h_x_eq', ← h_y_eq'] <;> ring
  rw [h4]
  exact ⟨a + d, h1, b + c, h2, rfl⟩

lemma iterated_containment (A B : Set ℝ) (d M N : ℕ)
    (h_contain : B ⊆ ExpansionLemma.iteratedDifference
      (ExpansionLemma.productSet A d) M) :
    ∃ (M' : ℕ),
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet B 2) N ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (2 * d)) M' := by
  let T := ExpansionLemma.productSet A d
  have h1 : ExpansionLemma.productSet B 2 ⊆
      ExpansionLemma.productSet (ExpansionLemma.iteratedDifference T M) 2 := by
    intro z hz
    rcases hz with ⟨f, hf, rfl⟩
    refine ⟨f, fun i => h_contain (hf i), rfl⟩
  have h2 := product_sum_expansion T M
  have h31 := productSet_productSet_contain A d
  have h_dd : d + d = 2 * d := by ring
  have h32 : ExpansionLemma.productSet A (d + d) = ExpansionLemma.productSet A (2 * d) := by
    congr 1 <;> ring
  have h3 : ExpansionLemma.productSet T 2 ⊆ ExpansionLemma.productSet A (2 * d) := by
    rw [h32] at h31
    exact h31
  have h4 : ExpansionLemma.productSet B 2 ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (2 * d)) (2 * M * M) := by
    intro z hz
    have h5 : z ∈ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet T 2) (2 * M * M) :=
      Set.Subset.trans h1 h2 hz
    rcases h5 with ⟨u, hu, v, hv, rfl⟩
    have h6 : u ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A (2 * d)) (2 * M * M) :=
      iteratedSumset_mono h3 hu
    have h7 : v ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A (2 * d)) (2 * M * M) :=
      iteratedSumset_mono h3 hv
    exact ⟨u, h6, v, h7, rfl⟩
  refine ⟨2 * N * (2 * M * M), ?_⟩
  exact iteratedDifference_of_subset_difference h4

/-- Generalized ProductSet nesting: productSet(productSet A d_A) d_B ⊆ productSet A (d_B * d_A). -/
lemma productSet_productSet_contain_gen (A : Set ℝ) (d_A d_B : ℕ) :
    ExpansionLemma.productSet (ExpansionLemma.productSet A d_A) d_B ⊆
    ExpansionLemma.productSet A (d_B * d_A) := by
  induction d_B with
  | zero =>
    intro z hz
    have h1 : ExpansionLemma.productSet (ExpansionLemma.productSet A d_A) 0 = {1} := by
      ext y; simp [ExpansionLemma.productSet]
    have h2 : ExpansionLemma.productSet A (0 * d_A) = {1} := by
      have h0 : 0 * d_A = 0 := by ring
      rw [h0]
      ext y
      simp [ExpansionLemma.productSet, Fin.prod_const]
      <;> constructor <;> intro h <;> tauto
    rw [h1] at hz
    rw [h2]
    exact hz
  | succ d_B ih =>
    intro z hz
    rcases hz with ⟨f, hf, h_eq⟩
    have h1 : f 0 ∈ ExpansionLemma.productSet A d_A := hf 0
    have h2 : (∏ i : Fin d_B, f (Fin.succ i)) ∈ ExpansionLemma.productSet (ExpansionLemma.productSet A d_A) d_B := by
      exact ⟨fun i => f (Fin.succ i), fun i => hf (Fin.succ i), rfl⟩
    rcases ih h2 with ⟨g, hg, h_eq2⟩
    rcases h1 with ⟨a, ha, h_eq1⟩
    let K := d_A + d_B * d_A
    let h_arr : Fin K → ℝ := fun i =>
      if h_lt : i.val < d_A then a ⟨i.val, h_lt⟩ else g ⟨i.val - d_A, by omega⟩
    have hh : ∀ i, h_arr i ∈ A := by
      intro i
      by_cases h_lt : i.val < d_A
      · have h' : h_arr i = a ⟨i.val, h_lt⟩ := by
          simp only [h_arr, dif_pos h_lt]
        rw [h']; exact ha ⟨i.val, h_lt⟩
      · have h' : h_arr i = g ⟨i.val - d_A, by omega⟩ := by
          simp only [h_arr, dif_neg h_lt]
        rw [h']; exact hg ⟨i.val - d_A, by omega⟩
    have h3 : ∀ (i : Fin d_A), h_arr (Fin.castAdd (d_B * d_A) i) = a i := by
      intro i
      have h_val : (Fin.castAdd (d_B * d_A) i).val = i.val := by exact Fin.val_castAdd (d_B * d_A) i
      have h_lt : (Fin.castAdd (d_B * d_A) i).val < d_A := by rw [h_val]; exact i.is_lt
      have h_goal : h_arr (Fin.castAdd (d_B * d_A) i) = a ⟨(Fin.castAdd (d_B * d_A) i).val, h_lt⟩ := by
        simp only [h_arr, dif_pos h_lt]
      rw [h_goal]
      have h_fin : (⟨(Fin.castAdd (d_B * d_A) i).val, h_lt⟩ : Fin d_A) = i := by
        apply Fin.ext; rw [h_val]
      rw [h_fin]
    have h4 : ∀ (i : Fin (d_B * d_A)), h_arr (Fin.natAdd d_A i) = g i := by
      intro i
      have h_val : (Fin.natAdd d_A i).val = d_A + i.val := by exact Fin.val_natAdd d_A i
      have h_nlt : ¬(Fin.natAdd d_A i).val < d_A := by rw [h_val]; omega
      have h_goal : h_arr (Fin.natAdd d_A i) = g ⟨(Fin.natAdd d_A i).val - d_A, by omega⟩ := by
        simp only [h_arr, dif_neg h_nlt]
      rw [h_goal]
      have h_sub : (Fin.natAdd d_A i).val - d_A = i.val := by rw [h_val] <;> omega
      have h_fin : (⟨(Fin.natAdd d_A i).val - d_A, by omega⟩ : Fin (d_B * d_A)) = i := by
        apply Fin.ext; simpa using h_sub
      rw [h_fin]
    have h_split : ∏ i : Fin K, h_arr i =
        (∏ i : Fin d_A, h_arr (Fin.castAdd (d_B * d_A) i)) * (∏ i : Fin (d_B * d_A), h_arr (Fin.natAdd d_A i)) :=
      Fin.prod_univ_add h_arr
    have h5 : ∏ i : Fin K, h_arr i = (∏ i : Fin d_A, a i) * (∏ i : Fin (d_B * d_A), g i) := by
      rw [h_split]
      have h51 : ∏ i : Fin d_A, h_arr (Fin.castAdd (d_B * d_A) i) = ∏ i : Fin d_A, a i := by
        apply Finset.prod_congr rfl; intro x _; exact h3 x
      have h52 : ∏ i : Fin (d_B * d_A), h_arr (Fin.natAdd d_A i) = ∏ i : Fin (d_B * d_A), g i := by
        apply Finset.prod_congr rfl; intro x _; exact h4 x
      rw [h51, h52]
    have h6 : ∏ i : Fin (d_B + 1), f i = (∏ i : Fin d_A, a i) * (∏ i : Fin (d_B * d_A), g i) := by
      rw [Fin.prod_univ_succ, h_eq1, h_eq2] <;> ring
    have h7 : K = (d_B + 1) * d_A := by
      dsimp only [K]; ring
    have h9 : ∏ i : Fin K, h_arr i = z := by
      calc
        ∏ i : Fin K, h_arr i
          = (∏ i : Fin d_A, a i) * (∏ i : Fin (d_B * d_A), g i) := h5
        _ = ∏ i : Fin (d_B + 1), f i := h6.symm
        _ = z := h_eq.symm
    have h_goal : z ∈ ExpansionLemma.productSet A K := ⟨h_arr, hh, h9.symm⟩
    have h8 : ExpansionLemma.productSet A K = ExpansionLemma.productSet A ((d_B + 1) * d_A) := by
      congr 1 <;> ring
    rw [h8] at h_goal
    exact h_goal

/-- Generalized iterated containment with arbitrary product exponent on B. -/
lemma iterated_containment_gen (A B : Set ℝ) (d_A M_A d_B N : ℕ) (hd_B : 0 < d_B)
    (h_contain : B ⊆ ExpansionLemma.iteratedDifference
      (ExpansionLemma.productSet A d_A) M_A) :
    ∃ (M' : ℕ),
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet B d_B) N ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (d_B * d_A)) M' := by
  let T := ExpansionLemma.productSet A d_A
  have h1 : ExpansionLemma.productSet B d_B ⊆
      ExpansionLemma.productSet (ExpansionLemma.iteratedDifference T M_A) d_B := by
    intro z hz
    rcases hz with ⟨f, hf, rfl⟩
    refine ⟨f, fun i => h_contain (hf i), rfl⟩
  let K := 2 ^ d_B * M_A ^ d_B
  have h2 := product_sum_expansion_gen T M_A d_B hd_B
  have h3 := productSet_productSet_contain_gen A d_A d_B
  have h4 : ExpansionLemma.productSet T d_B ⊆ ExpansionLemma.productSet A (d_B * d_A) := h3
  have h5 : ExpansionLemma.productSet B d_B ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (d_B * d_A)) K := by
    intro z hz
    have h6 : z ∈ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet T d_B) K :=
      Set.Subset.trans h1 h2 hz
    rcases h6 with ⟨u, hu, v, hv, rfl⟩
    have h7 : u ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A (d_B * d_A)) K :=
      iteratedSumset_mono (N := K) h4 hu
    have h8 : v ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A (d_B * d_A)) K :=
      iteratedSumset_mono (N := K) h4 hv
    exact ⟨u, h7, v, h8, rfl⟩
  refine ⟨2 * N * K, ?_⟩
  exact iteratedDifference_of_subset_difference h5

/-- Explicit version of `iterated_containment_gen` with the bound `M'` given
as `2 * N * (2 ^ d_B * M_A ^ d_B)`. -/
lemma iterated_containment_gen_explicit (A B : Set ℝ) (d_A M_A d_B N : ℕ) (hd_B : 0 < d_B)
    (h_contain : B ⊆ ExpansionLemma.iteratedDifference
      (ExpansionLemma.productSet A d_A) M_A) :
    ExpansionLemma.iteratedDifference (ExpansionLemma.productSet B d_B) N ⊆
    ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (d_B * d_A))
      (2 * N * (2 ^ d_B * M_A ^ d_B)) := by
  let T := ExpansionLemma.productSet A d_A
  let K := 2 ^ d_B * M_A ^ d_B
  have h1 : ExpansionLemma.productSet B d_B ⊆
      ExpansionLemma.productSet (ExpansionLemma.iteratedDifference T M_A) d_B := by
    intro z hz
    rcases hz with ⟨f, hf, rfl⟩
    refine ⟨f, fun i => h_contain (hf i), rfl⟩
  have h2 := product_sum_expansion_gen T M_A d_B hd_B
  have h3 := productSet_productSet_contain_gen A d_A d_B
  have h4 : ExpansionLemma.productSet T d_B ⊆ ExpansionLemma.productSet A (d_B * d_A) := h3
  have h5 : ExpansionLemma.productSet B d_B ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (d_B * d_A)) K := by
    intro z hz
    have h6 : z ∈ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet T d_B) K :=
      Set.Subset.trans h1 h2 hz
    rcases h6 with ⟨u, hu, v, hv, rfl⟩
    have h7 : u ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A (d_B * d_A)) K :=
      iteratedSumset_mono (N := K) h4 hu
    have h8 : v ∈ ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A (d_B * d_A)) K :=
      iteratedSumset_mono (N := K) h4 hv
    exact ⟨u, h7, v, h8, rfl⟩
  exact iteratedDifference_of_subset_difference h5

/-! ## Volume and diameter -/

lemma diam_pos_of_pos_vol {B : Set ℝ} (hB : IsCompact B)
    (hvol : 0 < MeasureTheory.volume B) : 0 < diam B := by
  by_contra h
  have h0 : diam B ≤ 0 := le_of_not_gt h
  have h1 : diam B = 0 := le_antisymm h0 diam_nonneg
  have hB_nonempty : B.Nonempty := by
    by_contra h2
    rw [Set.not_nonempty_iff_eq_empty.mp h2] at hvol
    simp at hvol
  rcases hB_nonempty with ⟨x, hx⟩
  have hB_single : B = {x} := by
    have h_sub : B ⊆ {x} := by
      intro y hy
      have h2 : dist y x ≤ diam B := dist_le_diam_of_mem hB.isBounded hy hx
      rw [h1] at h2
      have h4 : dist y x = 0 := by linarith [show 0 ≤ dist y x from dist_nonneg]
      have h5 : y = x := by simpa [dist_eq_zero] using h4
      simpa using h5
    exact Set.Subset.antisymm h_sub (Set.singleton_subset_iff.mpr hx)
  rw [hB_single] at hvol
  simp at hvol

lemma volume_dilation {c : ℝ} (hc : c ≠ 0) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasureTheory.volume ((fun b : ℝ => c * b) '' B) =
      ENNReal.ofReal |c| * MeasureTheory.volume B := by
  let g : ℝ → ℝ := fun x => c⁻¹ * x
  have h_image_eq_preimage : (fun b : ℝ => c * b) '' B = g ⁻¹' B := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage, g]
    constructor
    · rintro ⟨b, hb, rfl⟩
      have h : c⁻¹ * (c * b) = b := by field_simp [hc] <;> ring
      rw [h] <;> exact hb
    · intro hgy
      refine ⟨c⁻¹ * y, hgy, ?_⟩
      field_simp [hc] <;> ring
  rw [h_image_eq_preimage]
  have hc_inv : c⁻¹ ≠ 0 := inv_ne_zero hc
  have h_main := Real.volume_preimage_mul_left hc_inv B
  have h_abs : |(c⁻¹)⁻¹| = |c| := by
    have h1 : (c⁻¹)⁻¹ = c := by field_simp [hc]
    rw [h1]
  rw [h_abs] at h_main
  exact h_main

/-! ## scaledSumset helpers -/

lemma scaledSumset_card_one_contain {ι : Type*} [Fintype ι] (h_card : Fintype.card ι = 1)
    {v : ι → ℝ} {A : Set ℝ} :
    ∃ (i₀ : ι), ExpansionLemma.scaledSumset v A ⊆ (fun x : ℝ => v i₀ * x) '' A := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let i₀ : ι := Classical.arbitrary ι
  have h_subsingleton : Subsingleton ι := by
    have h : Fintype.card ι ≤ 1 := by omega
    exact Fintype.card_le_one_iff_subsingleton.mp h
  have h_unique : ∀ (j : ι), j = i₀ := fun j => Subsingleton.elim j i₀
  have h_contain : ExpansionLemma.scaledSumset v A ⊆ (fun x : ℝ => v i₀ * x) '' A := by
    intro z hz
    rcases hz with ⟨a, ha, rfl⟩
    have h_sum : ∑ i : ι, v i * a i = v i₀ * a i₀ := by
      have h_eq : ∀ (i : ι), v i * a i = v i₀ * a i₀ := by
        intro i
        have h_i : i = i₀ := h_unique i
        rw [h_i]
      have h2 : ∑ i : ι, v i * a i = ∑ i : ι, v i₀ * a i₀ := by
        apply Finset.sum_congr rfl
        intro i _
        exact h_eq i
      rw [h2]
      have h3 : ∑ i : ι, v i₀ * a i₀ = Fintype.card ι * (v i₀ * a i₀) := by
        rw [Finset.sum_const, Finset.card_univ] <;> ring
      rw [h3, h_card] <;> ring
    rw [h_sum]
    exact ⟨a i₀, ha i₀, rfl⟩
  exact ⟨i₀, h_contain⟩

lemma scaledSumset_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') {v : ι' → ℝ} {A : Set ℝ} :
    ExpansionLemma.scaledSumset (v ∘ e) A = ExpansionLemma.scaledSumset v A := by
  ext x
  simp only [ExpansionLemma.scaledSumset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨fun i' => a (e.symm i'), fun i' => ha (e.symm i'), ?_⟩
    have h_sum : ∑ i : ι, (v ∘ e) i * a i = ∑ i' : ι', v i' * a (e.symm i') := by
      exact Fintype.sum_equiv e
        (fun i : ι => (v ∘ e) i * a i)
        (fun i' : ι' => v i' * a (e.symm i'))
        (by intro i; simp [Function.comp_apply])
    exact h_sum
  · rintro ⟨b, hb, rfl⟩
    refine ⟨fun i => b (e i), fun i => hb (e i), ?_⟩
    have h_sum : ∑ i : ι, (v ∘ e) i * b (e i) = ∑ i' : ι', v i' * b i' := by
      exact Fintype.sum_equiv e
        (fun i : ι => (v ∘ e) i * b (e i))
        (fun i' : ι' => v i' * b i')
        (by intro i; simp [Function.comp_apply])
    exact h_sum.symm

/-! ## Padding lemmas -/

lemma iteratedDifference_pad_sum {S : Set ℝ} {M N : ℕ}
    (hS : S.Nonempty) (h : M ≤ N) :
    ExpansionLemma.iteratedDifference S M ⊆
    ExpansionLemma.iteratedDifference S N := by
  have h_step : ∀ K : ℕ, ExpansionLemma.iteratedDifference S K ⊆
      ExpansionLemma.iteratedDifference S (K + 1) := by
    intro K z hz
    rcases hz with ⟨u, hu, v, hv, h_z_eq⟩
    have h_z_eq' : u - v = z := by simpa using h_z_eq
    rcases hS with ⟨s, hs⟩
    have h1 : u + s ∈ ExpansionLemma.iteratedSumset S (K + 1) := by
      rw [iteratedSumset_succ]
      exact ⟨s, hs, u, hu, by ring⟩
    have h2 : v + s ∈ ExpansionLemma.iteratedSumset S (K + 1) := by
      rw [iteratedSumset_succ]
      exact ⟨s, hs, v, hv, by ring⟩
    have h3 : z = (u + s) - (v + s) := by
      rw [← h_z_eq'] <;> ring
    rw [h3]
    exact ⟨u + s, h1, v + s, h2, rfl⟩
  induction' h with K h ih
  · exact Subset.refl _
  · exact Set.Subset.trans ih (h_step K)

lemma smul_iteratedSumset {S T : Set ℝ} {c : ℝ} {N : ℕ}
    (h : (fun x => c * x) '' S ⊆ T) :
    (fun x => c * x) '' ExpansionLemma.iteratedSumset S N ⊆
    ExpansionLemma.iteratedSumset T N := by
  have h_main : ∀ (N : ℕ),
      (fun x : ℝ => c * x) '' ExpansionLemma.iteratedSumset S N ⊆
      ExpansionLemma.iteratedSumset T N := by
    intro N
    induction N with
    | zero =>
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have hx0 : x = 0 := by simpa [ExpansionLemma.iteratedSumset] using hx
      simpa [hx0, ExpansionLemma.iteratedSumset] using by simp
    | succ N ih =>
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      rw [iteratedSumset_succ] at hw
      rcases hw with ⟨s, hs, x', hx', h_eq⟩
      have h_eq' : s + x' = w := by simpa using h_eq
      have h_goal : c * w = c * s + c * x' := by
        rw [← h_eq'] <;> ring
      simpa [h_goal, iteratedSumset_succ] using
        ⟨c * s, h ⟨s, hs, rfl⟩, c * x', ih ⟨x', hx', rfl⟩, by ring⟩
  exact h_main N

lemma productSet_pad {A : Set ℝ} {d N : ℕ} (a : ℝ) (ha : a ∈ A) (h : d ≤ N) :
    (fun x : ℝ => a ^ (N - d) * x) '' ExpansionLemma.productSet A d ⊆
    ExpansionLemma.productSet A N := by
  have h_main : ∀ (k : ℕ), (fun x : ℝ => a ^ k * x) '' ExpansionLemma.productSet A d ⊆
      ExpansionLemma.productSet A (d + k) := by
    intro k
    induction k with
    | zero =>
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      simpa using hx
    | succ k ih =>
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have h1 : a ^ k * x ∈ ExpansionLemma.productSet A (d + k) := ih ⟨x, hx, rfl⟩
      rcases h1 with ⟨f, hf, h_eq⟩
      let g : Fin (d + k + 1) → ℝ := fun i =>
        if h2 : i = 0 then a else f (i.pred h2)
      have hg : ∀ i, g i ∈ A := by
        intro i
        by_cases h2 : i = 0
        · rw [h2]; simp [g, ha]
        · simp [g, h2, hf]
      have h_eq2 : ∏ i : Fin (d + k + 1), g i = a * ∏ i : Fin (d + k), f i := by
        rw [Fin.prod_univ_succ]
        have h5 : g 0 = a := by simp [g]
        rw [h5]
        apply congr_arg (fun x => a * x)
        apply Finset.prod_congr rfl
        intro j _
        have h6 : g (Fin.succ j) = f j := by
          simp [g, Fin.succ_ne_zero]
          <;> rfl
        exact h6
      have h_final : a ^ (k + 1) * x = ∏ i : Fin (d + k + 1), g i := by
        calc a ^ (k + 1) * x = a * (a ^ k * x) := by ring
                        _ = a * ∏ i : Fin (d + k), f i := by rw [h_eq]
                        _ = ∏ i : Fin (d + k + 1), g i := h_eq2.symm
      exact ⟨g, hg, h_final⟩
  have h4 : (fun x : ℝ => a ^ (N - d) * x) '' ExpansionLemma.productSet A d ⊆
      ExpansionLemma.productSet A (d + (N - d)) := h_main (N - d)
  have h5 : d + (N - d) = N := by omega
  have h6 : ExpansionLemma.productSet A (d + (N - d)) = ExpansionLemma.productSet A N := by
    rw [h5]
  rw [h6] at h4
  exact h4

lemma iteratedDifference_pad_product {A : Set ℝ} {d M N : ℕ}
    (a : ℝ) (ha : a ∈ A) (h : d ≤ N) :
    (fun x : ℝ => a ^ (N - d) * x) ''
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A d) M ⊆
    ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) M := by
  let c : ℝ := a ^ (N - d)
  have h1 : (fun x : ℝ => c * x) '' ExpansionLemma.productSet A d ⊆
      ExpansionLemma.productSet A N := productSet_pad a ha h
  have h2 : (fun x : ℝ => c * x) '' ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A d) M ⊆
      ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A N) M :=
    smul_iteratedSumset h1
  intro z hz
  rcases hz with ⟨w, hw, rfl⟩
  rcases hw with ⟨u, hu, v, hv, h_w_eq⟩
  have h3 : c * u - c * v = c * w := by
    have h_w_eq' : u - v = w := by simpa using h_w_eq
    rw [← h_w_eq'] <;> ring
  simpa [c] using ⟨c * u, h2 ⟨u, hu, rfl⟩, c * v, h2 ⟨v, hv, rfl⟩, h3⟩

lemma exists_nonzero_of_diam_pos {A : Set ℝ} (hA : IsCompact A)
    (hA_nonempty : A.Nonempty) (h_diam : 0 < diam A) :
    ∃ (a : ℝ), a ∈ A ∧ a ≠ 0 := by
  by_contra h
  push Not at h
  have hA_sub : A ⊆ {0} := by
    intro x hx
    have h4 : x = 0 := h x hx
    simpa using h4
  have h_diam_zero : diam A = 0 := by
    have h5 : A ⊆ {0} := hA_sub
    have h6 : diam A ≤ diam ({0} : Set ℝ) := diam_mono h5 (by simp)
    have h7 : diam ({0} : Set ℝ) = 0 := by simp
    have h8 : diam A ≤ 0 := by linarith
    have h9 : 0 ≤ diam A := diam_nonneg
    linarith
  linarith

lemma iteratedSumset_nonempty {S : Set ℝ} (hS : S.Nonempty) {N : ℕ} :
    (ExpansionLemma.iteratedSumset S N).Nonempty := by
  induction N with
  | zero => simp [ExpansionLemma.iteratedSumset]
  | succ N ih =>
    rcases hS with ⟨s, hs⟩
    rcases ih with ⟨x, hx⟩
    exact ⟨s + x, by rw [iteratedSumset_succ]; exact ⟨s, hs, x, hx, by ring⟩⟩

lemma productSet_nonempty {A : Set ℝ} (hA : A.Nonempty) {n : ℕ} :
    (ExpansionLemma.productSet A n).Nonempty := by
  rcases hA with ⟨a, ha⟩
  refine ⟨a ^ n, ?_⟩
  refine ⟨fun _ => a, fun _ => ha, ?_⟩
  simp

/-! ## Compactness -/

lemma productSet_compact {A : Set ℝ} (hA : IsCompact A) {n : ℕ} :
    IsCompact (ExpansionLemma.productSet A n) := by
  have h1 : ExpansionLemma.productSet A n =
      (fun (f : Fin n → ℝ) => ∏ i, f i) '' ExpansionLemma.cartesianPower A n := by
    ext x
    simp [ExpansionLemma.productSet, ExpansionLemma.cartesianPower, Set.mem_univ_pi]
    <;> aesop
  rw [h1]
  have h2 : IsCompact (ExpansionLemma.cartesianPower A n) := by
    rw [ExpansionLemma.cartesianPower]
    simpa using isCompact_univ_pi (fun _ => hA)
  exact h2.image (by fun_prop)

lemma iteratedSumset_compact {S : Set ℝ} (hS : IsCompact S) {N : ℕ} :
    IsCompact (ExpansionLemma.iteratedSumset S N) := by
  induction N with
  | zero => simp [ExpansionLemma.iteratedSumset] <;> exact isCompact_singleton
  | succ N ih =>
    rw [iteratedSumset_succ]
    have h_prod : IsCompact (S ×ˢ ExpansionLemma.iteratedSumset S N) := hS.prod ih
    have h_cont : Continuous (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop
    have h_eq : Set.image2 (· + ·) S (ExpansionLemma.iteratedSumset S N) =
        (fun p : ℝ × ℝ => p.1 + p.2) '' (S ×ˢ ExpansionLemma.iteratedSumset S N) := by
      ext z; simp [Set.image2, Set.mem_prod]
      <;> aesop
    rw [h_eq]
    exact h_prod.image h_cont

lemma iteratedDifference_compact {S : Set ℝ} (hS : IsCompact S) {N : ℕ} :
    IsCompact (ExpansionLemma.iteratedDifference S N) := by
  have h1 : IsCompact (ExpansionLemma.iteratedSumset S N) := iteratedSumset_compact hS
  have h_prod : IsCompact (ExpansionLemma.iteratedSumset S N ×ˢ ExpansionLemma.iteratedSumset S N) := h1.prod h1
  have h_cont : Continuous (fun p : ℝ × ℝ => p.1 - p.2) := by fun_prop
  have h_eq : ExpansionLemma.iteratedDifference S N =
      (fun p : ℝ × ℝ => p.1 - p.2) '' (ExpansionLemma.iteratedSumset S N ×ˢ ExpansionLemma.iteratedSumset S N) := by
    ext z; simp [ExpansionLemma.iteratedDifference, Set.image2, Set.mem_prod] <;> aesop
  rw [h_eq]
  exact h_prod.image h_cont

/-! ## Main induction -/

lemma iterative_weight_elimination_induction
    (h_expansion : ∀ {m : ℕ} {B : Set ℝ} {w : Fin m → ℝ},
      IsCompact B → B.Nonempty → 2 ≤ m →
      (∀ i, w i ∈ Set.Icc (1 / 2 : ℝ) 1) →
      0 < volume (ExpansionLemma.scaledSumset w B) →
      ∃ (N : ℕ), 0 < N ∧ ∃ (j : Fin m),
        volume (ExpansionLemma.scaledSumsetExcept w j
          (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet B 2) N)) ≥
        ENNReal.ofReal (diam B) * volume (ExpansionLemma.scaledSumset w B)) :
    ∀ (n : ℕ), ∀ (ι : Type) [Fintype ι], Fintype.card ι = n →
    ∀ (A : Set ℝ), IsCompact A → A.Nonempty → 0 < diam A →
    ∀ (v : ι → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) →
    0 < volume (ExpansionLemma.scaledSumset v A) →
    ∃ (d M : ℕ), 0 < d ∧ 0 < volume (ExpansionLemma.iteratedDifference
      (ExpansionLemma.productSet A d) M) := by
  have h_main : ∀ (k : ℕ), ∀ (ι : Type) [Fintype ι], Fintype.card ι = k →
      ∀ (A : Set ℝ), IsCompact A → A.Nonempty → 0 < diam A →
      ∀ (v : ι → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) →
      0 < volume (ExpansionLemma.scaledSumset v A) →
      ∃ (d M : ℕ), 0 < d ∧ 0 < volume (ExpansionLemma.iteratedDifference
        (ExpansionLemma.productSet A d) M) := by
    intro k
    induction k with
    | zero =>
    intro ι _ h_card A hA hA_nonempty h_diam v hv hvol
    exfalso
    have h_empty : IsEmpty ι := by
      rw [Fintype.card_eq_zero_iff] at h_card; exact h_card
    have h_ss : ExpansionLemma.scaledSumset v A = {0} := by
      ext x
      simp [ExpansionLemma.scaledSumset, Finset.sum_eq_zero]
      <;> aesop
    rw [h_ss] at hvol
    simp at hvol
    | succ k ih =>
    intro ι _ h_card A hA hA_nonempty h_diam v hv hvol
    by_cases h_k : k = 0
    · -- Base case: k+1 = 1
      subst h_k
      rcases scaledSumset_card_one_contain h_card with ⟨i₀, h_ss⟩
      rcases hA_nonempty with ⟨a0, ha0⟩
      have h_vol_image : 0 < volume ((fun x : ℝ => v i₀ * x) '' A) :=
        lt_of_lt_of_le hvol (measure_mono h_ss)
      have hvi₀ : v i₀ ∈ Set.Icc (1 / 2 : ℝ) 1 := hv i₀
      have h_v_ne_zero : v i₀ ≠ 0 := by
        have h : 1 / 2 ≤ v i₀ := hvi₀.1; linarith
      have h_vol_A : 0 < volume A := by
        have h_eq : volume ((fun x : ℝ => v i₀ * x) '' A) =
            ENNReal.ofReal |v i₀| * volume A :=
          volume_dilation h_v_ne_zero hA.measurableSet
        rw [h_eq] at h_vol_image
        have h_abs_pos : 0 < ENNReal.ofReal |v i₀| := by
          apply ENNReal.ofReal_pos.mpr; exact abs_pos.mpr h_v_ne_zero
        exact (ENNReal.mul_pos_iff.mp h_vol_image).2
      have h_vol_diff : 0 < volume (Set.image2 (· - ·) A A) := by
        have h_sub : (fun x : ℝ => x - a0) '' A ⊆ Set.image2 (· - ·) A A := by
          intro z hz
          rcases hz with ⟨x, hx, rfl⟩
          exact ⟨x, hx, a0, ha0, rfl⟩
        have h_vol_trans : 0 < volume ((fun x : ℝ => x - a0) '' A) := by
          have h1 : (fun x : ℝ => x - a0) '' A = (fun x : ℝ => x + a0) ⁻¹' A := by
            ext y
            simp only [Set.mem_image, Set.mem_preimage]
            constructor
            · rintro ⟨x, hx, rfl⟩
              have h : (x - a0) + a0 = x := by ring
              rw [h]; exact hx
            · intro hy
              refine ⟨y + a0, hy, ?_⟩
              ring
          have hmp : MeasurePreserving (fun x : ℝ => x + a0) := by exact measurePreserving_add_right volume a0
          have h_eq : volume ((fun x : ℝ => x - a0) '' A) = volume A := by
            rw [h1]
            exact hmp.measure_preimage hA.measurableSet.nullMeasurableSet
          rw [h_eq]; exact h_vol_A
        exact lt_of_lt_of_le h_vol_trans (measure_mono h_sub)
      have h5 : ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 1) 1 =
          Set.image2 (· - ·) A A := by
        have h51 : ExpansionLemma.productSet A 1 = A := productSet_one
        have h52 : ExpansionLemma.iteratedSumset A 1 = A := iteratedSumset_one
        simp [ExpansionLemma.iteratedDifference, h51, h52]
        <;> rfl
      refine ⟨1, 1, by norm_num, ?_⟩
      rw [h5]
      exact h_vol_diff
    · -- Inductive step
      have h_k_pos : 1 ≤ k := by omega
      let m := k + 1
      have hm2 : 2 ≤ m := by omega
      have h_card_eq : Fintype.card (Fin m) = Fintype.card ι := by
        simpa [m, Fintype.card_fin] using h_card.symm
      let e : Fin m ≃ ι := Fintype.equivOfCardEq h_card_eq
      let w : Fin m → ℝ := v ∘ e
      have hw : ∀ i : Fin m, w i ∈ Set.Icc (1 / 2 : ℝ) 1 := fun i => hv (e i)
      have h_ss_eq : ExpansionLemma.scaledSumset w A = ExpansionLemma.scaledSumset v A :=
        scaledSumset_equiv e
      have hvol' : 0 < volume (ExpansionLemma.scaledSumset w A) := by
        rw [h_ss_eq]; exact hvol
      rcases h_expansion (m := m) (B := A) (w := w) hA hA_nonempty hm2 hw hvol' with ⟨N₀, hN₀_pos, j, h_vol_B⟩
      let B₁ := ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N₀
      let ι' := {i : Fin m // i ≠ j}
      let v' : ι' → ℝ := fun i => w i
      have h_card' : Fintype.card ι' = k := by
        have h1 : Fintype.card ι' = Fintype.card (Fin m) - Fintype.card {i : Fin m // i = j} :=
          Fintype.card_subtype_compl (fun i : Fin m => i = j)
        have h2 : Fintype.card {i : Fin m // i = j} = 1 := by simp
        rw [h1, h2]
        <;> simp [m, Fintype.card_fin] <;> omega
      have h_vol' : 0 < volume (ExpansionLemma.scaledSumset v' B₁) := by
        have h_def : ExpansionLemma.scaledSumset v' B₁ =
            ExpansionLemma.scaledSumsetExcept w j B₁ := by rfl
        rw [h_def]
        have h_pos : 0 < ENNReal.ofReal (diam A) * volume (ExpansionLemma.scaledSumset w A) := by
          have h1 : 0 < ENNReal.ofReal (diam A) := ENNReal.ofReal_pos.mpr h_diam
          exact ENNReal.mul_pos h1.ne' hvol'.ne'
        exact lt_of_lt_of_le h_pos h_vol_B
      have hB1_compact : IsCompact B₁ :=
        iteratedDifference_compact (productSet_compact hA)
      have hB1_nonempty : B₁.Nonempty := by
        have h1 : (ExpansionLemma.productSet A 2).Nonempty := productSet_nonempty hA_nonempty
        have h2 : (ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A 2) N₀).Nonempty :=
          iteratedSumset_nonempty h1
        rcases h2 with ⟨u, hu⟩
        exact ⟨u - u, u, hu, u, hu, by ring⟩
      have hB1_diam_pos : 0 < diam B₁ := by
        by_contra h
        have h0 : diam B₁ ≤ 0 := le_of_not_gt h
        have h1 : diam B₁ = 0 := le_antisymm h0 diam_nonneg
        rcases hB1_nonempty with ⟨x, hx⟩
        have hB1_single : B₁ = {x} := by
          have h_sub : B₁ ⊆ {x} := by
            intro y hy
            have h2 : dist y x ≤ diam B₁ := dist_le_diam_of_mem hB1_compact.isBounded hy hx
            rw [h1] at h2
            have h4 : dist y x = 0 := by linarith [show 0 ≤ dist y x from dist_nonneg]
            have h5 : y = x := by simpa [dist_eq_zero] using h4
            simpa using h5
          exact Set.Subset.antisymm h_sub (Set.singleton_subset_iff.mpr hx)
        have h_ss_singleton : ExpansionLemma.scaledSumset v' B₁ = {∑ i : ι', v' i * x} := by
          rw [hB1_single]
          ext z
          simp only [ExpansionLemma.scaledSumset, Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · rintro ⟨a, ha, rfl⟩
            have h_all : ∀ i, a i = x := by
              intro i; have h6 : a i ∈ ({x} : Set ℝ) := ha i; simpa using h6
            have h7 : ∑ i : ι', v' i * a i = ∑ i : ι', v' i * x := by
              apply Finset.sum_congr rfl; intro i _; rw [h_all i]
            rw [h7]
          · intro hz
            refine ⟨fun _ => x, fun _ => by simp, ?_⟩
            rw [hz]
        rw [h_ss_singleton] at h_vol'
        have h_contra : volume ({∑ i : ι', v' i * x} : Set ℝ) = 0 := by simp
        rw [h_contra] at h_vol'
        simpa using h_vol'
      rcases ih ι' h_card' B₁ hB1_compact hB1_nonempty hB1_diam_pos v' (fun i => hw i) h_vol' with ⟨d, M, hd_pos, h_vol_dM⟩
      have h_contain : B₁ ⊆ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N₀ :=
        Subset.refl B₁
      rcases iterated_containment_gen A B₁ 2 N₀ d M hd_pos h_contain with ⟨M', h_contain'⟩
      have h_comm : d * 2 = 2 * d := by ring
      have h_vol_final : 0 < volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (2 * d)) M') := by
        have h9 : ExpansionLemma.productSet A (d * 2) = ExpansionLemma.productSet A (2 * d) := by congr 1 <;> ring
        have h10 : ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (d * 2)) M' ⊆ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (2 * d)) M' := by
          rw [h9]
        exact lt_of_lt_of_le h_vol_dM (measure_mono (Set.Subset.trans h_contain' h10))
      exact ⟨2 * d, M', by omega, h_vol_final⟩
  exact h_main

/-! ## Main theorem -/

lemma iterative_weight_elimination_main
    {A : Set ℝ} (hA : IsCompact A) (hA_nonempty : A.Nonempty)
    (hA_diam_pos : 0 < diam A)
    {n : ℕ} (hn : 1 ≤ n)
    {v : Fin n → ℝ} (hv : ∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hvol_pos : 0 < volume (ExpansionLemma.scaledSumset v A))
    (h_expansion : ∀ {m : ℕ} {B : Set ℝ} {w : Fin m → ℝ},
      IsCompact B → B.Nonempty → 2 ≤ m →
      (∀ i, w i ∈ Set.Icc (1 / 2 : ℝ) 1) →
      0 < volume (ExpansionLemma.scaledSumset w B) →
      ∃ (N : ℕ), 0 < N ∧ ∃ (j : Fin m),
        volume (ExpansionLemma.scaledSumsetExcept w j
          (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet B 2) N)) ≥
        ENNReal.ofReal (diam B) * volume (ExpansionLemma.scaledSumset w B)) :
    ∃ (N : ℕ), 0 < volume (ExpansionLemma.iteratedDifference
      (ExpansionLemma.productSet A N) N) := by
  have h_ind := iterative_weight_elimination_induction h_expansion n
  rcases h_ind (Fin n) (by simp) A hA hA_nonempty hA_diam_pos v hv hvol_pos with ⟨d, M, hd_pos, h_vol_dM⟩
  rcases exists_nonzero_of_diam_pos hA hA_nonempty hA_diam_pos with ⟨a, ha, ha_ne_zero⟩
  let N := max d M
  have hd : d ≤ N := le_max_left d M
  have hM : M ≤ N := le_max_right d M
  let c : ℝ := a ^ (N - d)
  have hc_ne_zero : c ≠ 0 := by
    simp [c, ha_ne_zero] <;> positivity
  have h_meas : MeasurableSet (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A d) M) :=
    (iteratedDifference_compact (productSet_compact hA)).measurableSet
  have h_sub1 : (fun x : ℝ => c * x) '' ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A d) M ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) M :=
    iteratedDifference_pad_product a ha hd
  have h_vol_image : 0 < volume ((fun x : ℝ => c * x) '' ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A d) M) := by
    have h_eq : volume ((fun x : ℝ => c * x) '' ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A d) M) =
        ENNReal.ofReal |c| * volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A d) M) :=
      volume_dilation hc_ne_zero h_meas
    rw [h_eq]
    have h_abs_pos : 0 < ENNReal.ofReal |c| := by
      apply ENNReal.ofReal_pos.mpr; exact abs_pos.mpr hc_ne_zero
    exact ENNReal.mul_pos h_abs_pos.ne' h_vol_dM.ne'
  have h1 : 0 < volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) M) :=
    lt_of_lt_of_le h_vol_image (measure_mono h_sub1)
  have h_nonempty : (ExpansionLemma.productSet A N).Nonempty := by
    rcases hA_nonempty with ⟨x, hx⟩
    refine ⟨x ^ N, ?_⟩
    refine ⟨fun _ => x, by simp [hx], by simp⟩
  have h2 : ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) M ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) N :=
    iteratedDifference_pad_sum h_nonempty hM
  have h3 : 0 < volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) N) :=
    lt_of_lt_of_le h1 (measure_mono h2)
  exact ⟨N, h3⟩

theorem iterative_weight_elimination
    {A : Set ℝ} (hA : IsCompact A) (hA_nonempty : A.Nonempty)
    (hA_diam_pos : 0 < diam A)
    {n : ℕ} (hn : 1 ≤ n)
    {v : Fin n → ℝ} (hv : ∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hvol_pos : 0 < volume (ExpansionLemma.scaledSumset v A))
    (h_expansion : ∀ {m : ℕ} {B : Set ℝ} {w : Fin m → ℝ},
      IsCompact B → B.Nonempty → 2 ≤ m →
      (∀ i, w i ∈ Set.Icc (1 / 2 : ℝ) 1) →
      0 < volume (ExpansionLemma.scaledSumset w B) →
      ∃ (N : ℕ), 0 < N ∧ ∃ (j : Fin m),
        volume (ExpansionLemma.scaledSumsetExcept w j
          (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet B 2) N)) ≥
        ENNReal.ofReal (diam B) * volume (ExpansionLemma.scaledSumset w B)) :
    ∃ (N : ℕ), 0 < volume (ExpansionLemma.iteratedDifference
      (ExpansionLemma.productSet A N) N) :=
  iterative_weight_elimination_main hA hA_nonempty hA_diam_pos hn hv hvol_pos h_expansion

theorem iterative_weight_elimination_quantitative
    {A : Set ℝ} (hA : IsCompact A) (hA_nonempty : A.Nonempty)
    (hA_diam_pos : 0 < diam A)
    {n : ℕ} (hn : 1 ≤ n)
    {v : Fin n → ℝ} (hv : ∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hvol_pos : 0 < volume (ExpansionLemma.scaledSumset v A))
    (h_expansion : ∀ {m : ℕ} {B : Set ℝ} {w : Fin m → ℝ},
      IsCompact B → B.Nonempty → 2 ≤ m →
      (∀ i, w i ∈ Set.Icc (1 / 2 : ℝ) 1) →
      0 < volume (ExpansionLemma.scaledSumset w B) →
      ∃ (N : ℕ), 0 < N ∧ ∃ (j : Fin m),
        volume (ExpansionLemma.scaledSumsetExcept w j
          (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet B 2) N)) ≥
        ENNReal.ofReal (diam B) * volume (ExpansionLemma.scaledSumset w B)) :
    ∃ (N : ℕ) (c : ℝ), 0 < c ∧
      ENNReal.ofReal c ≤ volume (ExpansionLemma.iteratedDifference
        (ExpansionLemma.productSet A N) N) := by
  have h_main := iterative_weight_elimination hA hA_nonempty hA_diam_pos hn hv hvol_pos h_expansion
  rcases h_main with ⟨N, hN_pos⟩
  let V := volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) N)
  have hV_pos : 0 < V := hN_pos
  have h_exists_c : ∃ (c : ℝ), 0 < c ∧ ENNReal.ofReal c ≤ V := by
    by_cases h_top : V = ⊤
    · refine ⟨1, by norm_num, ?_⟩
      rw [h_top] <;> simp
    · have h_lt_top : V < ⊤ := by
        rw [lt_top_iff_ne_top] <;> exact h_top
      have hV_ne_zero : V ≠ 0 := hV_pos.ne'
      have h5 : ENNReal.toReal V ≠ 0 := by
        intro h6
        have h7 : V = 0 ∨ V = ⊤ := by
          rw [ENNReal.toReal_eq_zero_iff] at h6; exact h6
        rcases h7 with (h7 | h7)
        · exact hV_ne_zero h7
        · exact h_top h7
      have hV_real_pos : 0 < ENNReal.toReal V := by
        have h_nonneg : 0 ≤ ENNReal.toReal V := by positivity
        exact lt_of_le_of_ne h_nonneg h5.symm
      let c : ℝ := ENNReal.toReal V / 2
      have hc_pos : 0 < c := half_pos hV_real_pos
      have h_le : ENNReal.ofReal c ≤ V := by
        have h1 : c ≤ ENNReal.toReal V := by dsimp only [c] <;> linarith
        have h2 : ENNReal.ofReal c ≤ ENNReal.ofReal (ENNReal.toReal V) := ENNReal.ofReal_le_ofReal h1
        have h3 : ENNReal.ofReal (ENNReal.toReal V) = V := ENNReal.ofReal_toReal h_top
        rw [h3] at h2; exact h2
      exact ⟨c, hc_pos, h_le⟩
  rcases h_exists_c with ⟨c, hc_pos, hc_le⟩
  exact ⟨N, c, hc_pos, hc_le⟩

/-! ## Uniform quantitative elimination

Given a fixed `N_max` for the one-step expansion lemma and a uniform initial
volume lower bound `V_min`, produce a single `N` and positive constant `c_X`
(depending only on `N_max`, `n`, and `V_min`) such that for **all** compact
nonempty `A` with positive diameter and all weights in `[1/2,1]`, the iterated
difference set has volume at least `c_X`. -/

/-- Volume lower-bound recurrence during iterative weight elimination.
At the step with `m` remaining weights, the bound transforms as
`V ↦ V^2 / (2 * m)`: the diameter lower bound is `V / (2 * m)`, and the
expansion lemma multiplies the volume by the diameter. -/
def finalVolume (V : ℝ) : ℕ → ℝ
  | 0 => V
  | 1 => V
  | k + 2 => finalVolume (V^2 / (2 * ((k + 2 : ℕ) : ℝ))) (k + 1)

/-- The recurrence step: `finalVolume V m = finalVolume (V^2 / (2*m)) (m-1)` for `m ≥ 2`. -/
lemma finalVolume_step {V : ℝ} {m : ℕ} (hm : 2 ≤ m) :
    finalVolume V m = finalVolume (V^2 / (2 * (m : ℝ))) (m - 1) := by
  cases m with
  | zero => omega
  | succ m' =>
    cases m' with
    | zero => omega
    | succ _ =>
      simp [finalVolume] <;> ring_nf

/-- `finalVolume V n > 0` whenever `V > 0`. -/
lemma finalVolume_pos : ∀ (n : ℕ) (V : ℝ), 0 < V → 0 < finalVolume V n
  | 0, V, hV => by simpa [finalVolume] using hV
  | 1, V, hV => by simpa [finalVolume] using hV
  | k + 2, V, hV =>
    have h_pos2 : 0 < V^2 / (2 * ((k + 2 : ℕ) : ℝ)) := by positivity
    finalVolume_pos (k + 1) (V^2 / (2 * ((k + 2 : ℕ) : ℝ))) h_pos2

/-- Diameter lower bound from a scaled-sumset volume lower bound.
If `volume(scaledSumset v A) ≥ V` and all `v_i ∈ [1/2,1]`, then `diam A ≥ V / (2*n)`. -/
lemma scaledSumset_diam_lower {n : ℕ} {v : Fin n → ℝ} {A : Set ℝ} {V : ℝ}
    (hA : IsCompact A) (hA_nonempty : A.Nonempty)
    (hv : ∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hV : ENNReal.ofReal V ≤ volume (ExpansionLemma.scaledSumset v A))
    (hV_pos : 0 < V) (hn_pos : 0 < n) :
    V / (2 * (n : ℝ)) ≤ diam A := by
  rcases hA_nonempty with ⟨a0, ha0⟩
  have h1 : ExpansionLemma.scaledSumset v A ⊆
      Set.Icc ((∑ i : Fin n, v i) * a0 - (n : ℝ) * diam A)
        ((∑ i : Fin n, v i) * a0 + (n : ℝ) * diam A) := by
    intro x hx
    rcases hx with ⟨a, ha, rfl⟩
    have h2 : ∀ i : Fin n, |a i - a0| ≤ diam A := fun i =>
      dist_le_diam_of_mem hA.isBounded (ha i) ha0
    have h3 : |∑ i : Fin n, v i * (a i - a0)| ≤ (n : ℝ) * diam A := by
      have h_abs_sum : |∑ i : Fin n, v i * (a i - a0)| ≤ ∑ i : Fin n, |v i * (a i - a0)| :=
        Finset.abs_sum_le_sum_abs (f := fun i : Fin n => v i * (a i - a0)) (s := Finset.univ)
      have h_eq_abs : ∑ i : Fin n, |v i * (a i - a0)| = ∑ i : Fin n, v i * |a i - a0| := by
        apply Finset.sum_congr rfl; intro i _
        have hvi_nonneg : 0 ≤ v i := by have h := (hv i).1; linarith
        rw [abs_mul, abs_of_nonneg hvi_nonneg]
      have h_abs2 : |∑ i : Fin n, v i * (a i - a0)| ≤ ∑ i : Fin n, v i * |a i - a0| := by
        rw [h_eq_abs] at h_abs_sum; exact h_abs_sum
      have h_le : ∑ i : Fin n, v i * |a i - a0| ≤ ∑ i : Fin n, v i * diam A := by
        apply Finset.sum_le_sum; intro i _
        have hvi_nonneg : 0 ≤ v i := by have h := (hv i).1; linarith
        exact mul_le_mul_of_nonneg_left (h2 i) hvi_nonneg
      have h_sum_v : (∑ i : Fin n, v i) * diam A = ∑ i : Fin n, v i * diam A := by
        rw [Finset.sum_mul] <;> rfl
      have h_sum_le : ∑ i : Fin n, v i ≤ (n : ℝ) := by
        have h5 : ∀ i : Fin n, v i ≤ 1 := fun i => (hv i).2
        have h6 : ∑ i : Fin n, v i ≤ ∑ i : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum; intro i _; exact h5 i
        simpa using h6
      calc |∑ i : Fin n, v i * (a i - a0)|
        ≤ ∑ i : Fin n, v i * |a i - a0| := h_abs2
      _ ≤ ∑ i : Fin n, v i * diam A := h_le
      _ = (∑ i : Fin n, v i) * diam A := h_sum_v.symm
      _ ≤ (n : ℝ) * diam A := by gcongr <;> exact diam_nonneg
    have h_sum : ∑ i, v i * a i - (∑ i, v i) * a0 = ∑ i, v i * (a i - a0) := by
      have h41 : (∑ i, v i) * a0 = ∑ i, v i * a0 := by rw [Finset.sum_mul]
      have h : ∑ i, v i * a i - (∑ i, v i) * a0 = ∑ i, v i * a i - ∑ i, v i * a0 := by rw [h41]
      rw [h, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    have h4 : |∑ i, v i * a i - (∑ i, v i) * a0| ≤ (n : ℝ) * diam A := by
      rw [h_sum]; exact h3
    have h5 : -(n : ℝ) * diam A ≤ ∑ i, v i * a i - (∑ i, v i) * a0 := by
      have h51 := (abs_le.mp h4).1
      simpa [mul_neg] using h51
    have h6 : ∑ i, v i * a i - (∑ i, v i) * a0 ≤ (n : ℝ) * diam A := by
      exact (abs_le.mp h4).2
    exact ⟨by linarith, by linarith⟩
  have h_vol : volume (ExpansionLemma.scaledSumset v A) ≤
      ENNReal.ofReal (2 * (n : ℝ) * diam A) := by
    have h6 : volume (Set.Icc ((∑ i : Fin n, v i) * a0 - (n : ℝ) * diam A)
          ((∑ i : Fin n, v i) * a0 + (n : ℝ) * diam A)) =
        ENNReal.ofReal (2 * (n : ℝ) * diam A) := by
      rw [Real.volume_Icc] <;> ring_nf
    have h7 : volume (ExpansionLemma.scaledSumset v A) ≤ volume (Set.Icc _ _) :=
      measure_mono h1
    rw [h6] at h7; exact h7
  have h8 : ENNReal.ofReal V ≤ ENNReal.ofReal (2 * (n : ℝ) * diam A) := le_trans hV h_vol
  have h9 : V ≤ 2 * (n : ℝ) * diam A :=
    ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mp h8
  have h10 : 0 < 2 * (n : ℝ) := by positivity
  calc V / (2 * (n : ℝ))
    ≤ (2 * (n : ℝ) * diam A) / (2 * (n : ℝ)) := by gcongr
  _ = diam A := by field_simp [h10.ne'] <;> ring

/-- Given compact nonempty `A` with positive diameter, there exists `a ∈ A`
with `|a| ≥ diam A / 4`. -/
lemma exists_large_abs_of_diam_pos {A : Set ℝ} (hA : IsCompact A)
    (hA_nonempty : A.Nonempty) (h_diam : 0 < diam A) :
    ∃ (a : ℝ), a ∈ A ∧ diam A / 4 ≤ |a| := by
  have h1 : ∃ (x y : ℝ), x ∈ A ∧ y ∈ A ∧ diam A / 2 < dist x y := by
    by_contra h
    have h2 : ∀ (x : ℝ), x ∈ A → ∀ (y : ℝ), y ∈ A → dist x y ≤ diam A / 2 := by
      intro x hx y hy
      have h4 : ¬(diam A / 2 < dist x y) := by
        intro h5; exact h ⟨x, y, hx, hy, h5⟩
      exact le_of_not_gt h4
    have h3 : diam A ≤ diam A / 2 :=
      Metric.diam_le_of_forall_dist_le_of_nonempty hA_nonempty h2
    linarith
  rcases h1 with ⟨x, y, hx, hy, hdist⟩
  have h3 : |x - y| = dist x y := by simp [dist_eq_norm]
  have h4 : |x| + |y| ≥ |x - y| := by exact abs_sub x y
  have h5 : |x| + |y| > diam A / 2 := by
    rw [h3] at h4; linarith
  by_cases h6 : diam A / 4 ≤ |x|
  · exact ⟨x, hx, h6⟩
  · have h7 : diam A / 4 ≤ |y| := by linarith
    exact ⟨y, hy, h7⟩

/-- **Quantitative uniform induction**.

Given a fixed `N_max` for the one-step uniform expansion lemma, and `k` weights,
there exist `d, M` (depending only on `k` and `N_max`) such that for any
initial volume bound `V > 0`, any compact nonempty `A` with positive diameter,
and any weights `v_i ∈ [1/2,1]`, if `volume(scaledSumset v A) ≥ V`, then
`volume(iteratedDifference (productSet A d) M) ≥ finalVolume V k`. -/
lemma iterative_weight_elimination_quantitative_induction
    (N_max : ℕ) (hN_max_pos : 0 < N_max)
    (h_expansion_uniform : ∀ {m : ℕ} {B : Set ℝ} {w : Fin m → ℝ},
      IsCompact B → B.Nonempty → 2 ≤ m →
      (∀ i, w i ∈ Set.Icc (1 / 2 : ℝ) 1) →
      0 < volume (ExpansionLemma.scaledSumset w B) →
      ∃ (j : Fin m),
        volume (ExpansionLemma.scaledSumsetExcept w j
          (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet B 2) N_max)) ≥
        ENNReal.ofReal (diam B) * volume (ExpansionLemma.scaledSumset w B)) :
    ∀ (k : ℕ), 1 ≤ k → ∃ (d M : ℕ), 0 < d ∧
      ∀ (V : ℝ), 0 < V →
      ∀ (ι : Type) [Fintype ι], Fintype.card ι = k →
      ∀ (A : Set ℝ), IsCompact A → A.Nonempty → 0 < diam A →
      ∀ (v : ι → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) →
      volume (ExpansionLemma.scaledSumset v A) ≥ ENNReal.ofReal V →
      volume (ExpansionLemma.iteratedDifference
        (ExpansionLemma.productSet A d) M) ≥ ENNReal.ofReal (finalVolume V k) := by
  have h_main : ∀ (k : ℕ), 1 ≤ k → ∃ (d M : ℕ), 0 < d ∧
      ∀ (V : ℝ), 0 < V →
      ∀ (ι : Type) [Fintype ι], Fintype.card ι = k →
      ∀ (A : Set ℝ), IsCompact A → A.Nonempty → 0 < diam A →
      ∀ (v : ι → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) →
      volume (ExpansionLemma.scaledSumset v A) ≥ ENNReal.ofReal V →
      volume (ExpansionLemma.iteratedDifference
        (ExpansionLemma.productSet A d) M) ≥ ENNReal.ofReal (finalVolume V k) := by
    intro k hk
    induction k with
    | zero => exfalso; linarith
    | succ k ih =>
      by_cases h_k : k = 0
      · -- Base case: k + 1 = 1
        subst h_k
        refine ⟨1, 1, by norm_num, ?_⟩
        intro V hV ι _ h_card A hA hA_nonempty h_diam v hv hvol
        rcases scaledSumset_card_one_contain h_card with ⟨i₀, h_ss⟩
        rcases hA_nonempty with ⟨a0, ha0⟩
        have h_vol_image : volume ((fun x : ℝ => v i₀ * x) '' A) ≥ ENNReal.ofReal V :=
          le_trans hvol (measure_mono h_ss)
        have hvi₀ : v i₀ ∈ Set.Icc (1 / 2 : ℝ) 1 := hv i₀
        have h_v_ne_zero : v i₀ ≠ 0 := by
          have h : 1 / 2 ≤ v i₀ := hvi₀.1; linarith
        have h_v_le_one : v i₀ ≤ 1 := hvi₀.2
        have h_vol_A : volume A ≥ ENNReal.ofReal V := by
          have h_eq : volume ((fun x : ℝ => v i₀ * x) '' A) =
              ENNReal.ofReal |v i₀| * volume A :=
            volume_dilation h_v_ne_zero hA.measurableSet
          rw [h_eq] at h_vol_image
          have h_v_nonneg : 0 ≤ v i₀ := by have h := hvi₀.1; linarith
          have h_abs_le_one : |v i₀| ≤ 1 := by
            rw [abs_of_nonneg h_v_nonneg] <;> exact h_v_le_one
          have h10 : ENNReal.ofReal |v i₀| ≤ 1 := by
            have h101 : ENNReal.ofReal |v i₀| ≤ ENNReal.ofReal (1 : ℝ) :=
              (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mpr h_abs_le_one
            simpa using h101
          have h11 : ENNReal.ofReal V ≤ ENNReal.ofReal |v i₀| * volume A := h_vol_image
          have h12 : ENNReal.ofReal |v i₀| * volume A ≤ volume A := by
            have h13 : ENNReal.ofReal |v i₀| * volume A ≤ 1 * volume A := by
              gcongr <;> exact h10
            simpa using h13
          exact le_trans h11 h12
        have h_vol_diff : volume (Set.image2 (· - ·) A A) ≥ ENNReal.ofReal V := by
          have h_sub : (fun x : ℝ => x - a0) '' A ⊆ Set.image2 (· - ·) A A := by
            intro z hz
            rcases hz with ⟨x, hx, rfl⟩
            exact ⟨x, hx, a0, ha0, rfl⟩
          have h_vol_trans : volume ((fun x : ℝ => x - a0) '' A) = volume A := by
            have h1 : (fun x : ℝ => x - a0) '' A = (fun x : ℝ => x + a0) ⁻¹' A := by
              ext y
              simp only [Set.mem_image, Set.mem_preimage]
              constructor
              · rintro ⟨x, hx, rfl⟩
                have h : (x - a0) + a0 = x := by ring
                rw [h]; exact hx
              · intro hy
                refine ⟨y + a0, hy, by ring⟩
            have hmp : MeasurePreserving (fun x : ℝ => x + a0) := by exact measurePreserving_add_right volume a0
            rw [h1]
            exact hmp.measure_preimage hA.measurableSet.nullMeasurableSet
          have h_vol4 : volume ((fun x : ℝ => x - a0) '' A) ≥ ENNReal.ofReal V := by
            rw [h_vol_trans]; exact h_vol_A
          exact le_trans h_vol4 (measure_mono h_sub)
        have h5 : ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 1) 1 =
            Set.image2 (· - ·) A A := by
          have h51 : ExpansionLemma.productSet A 1 = A := productSet_one
          have h52 : ExpansionLemma.iteratedSumset A 1 = A := iteratedSumset_one
          simp [ExpansionLemma.iteratedDifference, h51, h52]
        rw [h5]
        simpa [finalVolume] using h_vol_diff
      · -- Inductive step: k ≥ 1
        have h_k_pos : 1 ≤ k := by omega
        rcases ih h_k_pos with ⟨d, M, hd_pos, h_ih⟩
        let d' := 2 * d
        let M' := 2 * M * (2 ^ d * N_max ^ d)
        refine ⟨d', M', by omega, ?_⟩
        intro V hV ι _ h_card A hA hA_nonempty h_diam v hv hvol
        let m := k + 1
        have hm2 : 2 ≤ m := by omega
        have h_card_eq : Fintype.card (Fin m) = Fintype.card ι := by
          simpa [m, Fintype.card_fin] using h_card.symm
        let e : Fin m ≃ ι := Fintype.equivOfCardEq h_card_eq
        let w : Fin m → ℝ := v ∘ e
        have hw : ∀ i : Fin m, w i ∈ Set.Icc (1 / 2 : ℝ) 1 := fun i => hv (e i)
        have h_ss_eq : ExpansionLemma.scaledSumset w A = ExpansionLemma.scaledSumset v A :=
          scaledSumset_equiv e
        have hvol' : volume (ExpansionLemma.scaledSumset w A) ≥ ENNReal.ofReal V := by
          rw [h_ss_eq]; exact hvol
        have hvol_pos' : 0 < volume (ExpansionLemma.scaledSumset w A) :=
          lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hV) hvol'
        rcases h_expansion_uniform (m := m) (B := A) (w := w) hA hA_nonempty hm2 hw hvol_pos' with ⟨j, h_vol_B⟩
        let B₁ := ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N_max
        let ι' := {i : Fin m // i ≠ j}
        let v' : ι' → ℝ := fun i => w i
        have h_card' : Fintype.card ι' = k := by
          have h1 : Fintype.card ι' = Fintype.card (Fin m) - Fintype.card {i : Fin m // i = j} :=
            Fintype.card_subtype_compl (fun i : Fin m => i = j)
          have h2 : Fintype.card {i : Fin m // i = j} = 1 := by simp
          rw [h1, h2]
          simp [m, Fintype.card_fin] <;> omega
        have h_diam_lower : V / (2 * (m : ℝ)) ≤ diam A :=
          scaledSumset_diam_lower hA hA_nonempty hw hvol' hV (by omega)
        let V' := V^2 / (2 * (m : ℝ))
        have hV'_pos : 0 < V' := by positivity
        have h_vol'_quant : volume (ExpansionLemma.scaledSumset v' B₁) ≥ ENNReal.ofReal V' := by
          have h_def : ExpansionLemma.scaledSumset v' B₁ =
              ExpansionLemma.scaledSumsetExcept w j B₁ := by rfl
          rw [h_def]
          have h1 : ENNReal.ofReal (diam A) * volume (ExpansionLemma.scaledSumset w A) ≥
              ENNReal.ofReal V' := by
            have h2 : ENNReal.ofReal (diam A) ≥ ENNReal.ofReal (V / (2 * (m : ℝ))) := by
              gcongr
            have h3 : ENNReal.ofReal (diam A) * volume (ExpansionLemma.scaledSumset w A) ≥
                ENNReal.ofReal (V / (2 * (m : ℝ))) * ENNReal.ofReal V := by
              gcongr
            have h_pos1 : 0 ≤ V / (2 * (m : ℝ)) := by positivity
            have h4 : ENNReal.ofReal (V / (2 * (m : ℝ))) * ENNReal.ofReal V =
                ENNReal.ofReal V' := by
              have h_eq1 : ENNReal.ofReal (V / (2 * (m : ℝ))) * ENNReal.ofReal V =
                  ENNReal.ofReal ((V / (2 * (m : ℝ))) * V) := by
                rw [← ENNReal.ofReal_mul (p := V / (2 * (m : ℝ))) (q := V) h_pos1]
              have h_eq2 : (V / (2 * (m : ℝ))) * V = V' := by
                simp [V'] <;> ring
              rw [h_eq1, h_eq2]
            rw [h4] at h3
            exact h3
          exact le_trans h1 h_vol_B
        have hB1_compact : IsCompact B₁ :=
          iteratedDifference_compact (productSet_compact hA)
        have hB1_nonempty : B₁.Nonempty := by
          have h1 : (ExpansionLemma.productSet A 2).Nonempty := productSet_nonempty hA_nonempty
          have h2 : (ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A 2) N_max).Nonempty :=
            iteratedSumset_nonempty h1
          rcases h2 with ⟨u, hu⟩
          exact ⟨u - u, u, hu, u, hu, by ring⟩
        have hB1_diam_pos : 0 < diam B₁ := by
          by_contra h
          have h0 : diam B₁ ≤ 0 := le_of_not_gt h
          have h1 : diam B₁ = 0 := le_antisymm h0 diam_nonneg
          rcases hB1_nonempty with ⟨x, hx⟩
          have hB1_single : B₁ = {x} := by
            have h_sub : B₁ ⊆ {x} := by
              intro y hy
              have h2 : dist y x ≤ diam B₁ := dist_le_diam_of_mem hB1_compact.isBounded hy hx
              rw [h1] at h2
              have h4 : dist y x = 0 := by linarith [show 0 ≤ dist y x from dist_nonneg]
              have h5 : y = x := by simpa [dist_eq_zero] using h4
              simpa using h5
            exact Set.Subset.antisymm h_sub (Set.singleton_subset_iff.mpr hx)
          have h_ss_singleton : ExpansionLemma.scaledSumset v' B₁ = {∑ i : ι', v' i * x} := by
            rw [hB1_single]
            ext z
            simp only [ExpansionLemma.scaledSumset, Set.mem_setOf_eq, Set.mem_singleton_iff]
            constructor
            · rintro ⟨a, ha, rfl⟩
              have h_all : ∀ i, a i = x := by
                intro i; have h6 : a i ∈ ({x} : Set ℝ) := ha i; simpa using h6
              have h7 : ∑ i : ι', v' i * a i = ∑ i : ι', v' i * x := by
                apply Finset.sum_congr rfl; intro i _; rw [h_all i]
              rw [h7]
            · intro hz
              refine ⟨fun _ => x, fun _ => by simp, ?_⟩
              rw [hz]
          rw [h_ss_singleton] at h_vol'_quant
          have h_contra : volume ({∑ i : ι', v' i * x} : Set ℝ) = 0 := by simp
          rw [h_contra] at h_vol'_quant
          have h_pos : 0 < ENNReal.ofReal V' := ENNReal.ofReal_pos.mpr hV'_pos
          exact False.elim (not_le.mpr h_pos h_vol'_quant)
        have h_final_rec : finalVolume V m = finalVolume V' k := by
          have h_step := finalVolume_step (V := V) (m := m) hm2
          simpa [V', m] using h_step
        have h_ih_B1 : volume (ExpansionLemma.iteratedDifference
            (ExpansionLemma.productSet B₁ d) M) ≥ ENNReal.ofReal (finalVolume V' k) :=
          h_ih V' hV'_pos ι' h_card' B₁ hB1_compact hB1_nonempty hB1_diam_pos v' (fun i => hw i) h_vol'_quant
        have h_contain' : ExpansionLemma.iteratedDifference (ExpansionLemma.productSet B₁ d) M ⊆
            ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (d * 2)) M' :=
          iterated_containment_gen_explicit A B₁ 2 N_max d M hd_pos (Subset.refl B₁)
        have h_vol_final : volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A d') M') ≥
            ENNReal.ofReal (finalVolume V m) := by
          have h9 : d' = d * 2 := by ring
          rw [h9] at *
          have h10 : volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (d * 2)) M') ≥
              ENNReal.ofReal (finalVolume V' k) :=
            le_trans h_ih_B1 (measure_mono h_contain')
          rw [h_final_rec]
          exact h10
        exact h_vol_final
  exact h_main

/-- **Quantitative uniform iterative weight elimination**.

Given a fixed `N_max` for the one-step uniform expansion lemma, a number of
weights `n`, and a uniform initial volume lower bound `V_min`, there exists a
single `N` and a positive constant `c_X` (both depending only on `N_max`, `n`,
and `V_min`) such that for **all** compact nonempty `A` with positive diameter
and all weights `v_i ∈ [1/2,1]`, if `volume(scaledSumset v A) ≥ V_min`, then
`volume(iteratedDifference (productSet A N) N) ≥ c_X`.

This supplies the `h_uniform_elim` hypothesis of `expansion_theorem_uniform`. -/
theorem iterative_weight_elimination_quantitative_uniform
    (N_max : ℕ) (hN_max_pos : 0 < N_max)
    (h_expansion_uniform : ∀ {m : ℕ} {B : Set ℝ} {w : Fin m → ℝ},
      IsCompact B → B.Nonempty → 2 ≤ m →
      (∀ i, w i ∈ Set.Icc (1 / 2 : ℝ) 1) →
      0 < volume (ExpansionLemma.scaledSumset w B) →
      ∃ (j : Fin m),
        volume (ExpansionLemma.scaledSumsetExcept w j
          (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet B 2) N_max)) ≥
        ENNReal.ofReal (diam B) * volume (ExpansionLemma.scaledSumset w B))
    {n : ℕ} (hn : 1 ≤ n) (V_min : ℝ) (hV_min_pos : 0 < V_min) :
    ∃ (N : ℕ) (c_X : ℝ), 0 < c_X ∧
      ∀ (A : Set ℝ), IsCompact A → A.Nonempty → 0 < diam A →
      ∀ (v : Fin n → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) →
      volume (ExpansionLemma.scaledSumset v A) ≥ ENNReal.ofReal V_min →
      volume (ExpansionLemma.iteratedDifference
        (ExpansionLemma.productSet A N) N) ≥ ENNReal.ofReal c_X := by
  have h_ind := iterative_weight_elimination_quantitative_induction N_max hN_max_pos h_expansion_uniform
  rcases h_ind n hn with ⟨d, M, hd_pos, h_main⟩
  let N := max d M
  have hd : d ≤ N := le_max_left d M
  have hM : M ≤ N := le_max_right d M
  let c_base : ℝ := V_min / (8 * (n : ℝ))
  have hc_base_pos : 0 < c_base := by positivity
  let c_X : ℝ := c_base ^ (N - d) * finalVolume V_min n
  have hcX_pos : 0 < c_X := by
    have h1 : 0 < c_base ^ (N - d) := by positivity
    have h2 : 0 < finalVolume V_min n := finalVolume_pos n V_min hV_min_pos
    positivity
  refine ⟨N, c_X, hcX_pos, ?_⟩
  intro A hA hA_nonempty h_diam v hv hvol
  have h_vol_dM : volume (ExpansionLemma.iteratedDifference
      (ExpansionLemma.productSet A d) M) ≥ ENNReal.ofReal (finalVolume V_min n) :=
    h_main V_min hV_min_pos (Fin n) (by simp) A hA hA_nonempty h_diam v hv hvol
  rcases exists_large_abs_of_diam_pos hA hA_nonempty h_diam with ⟨a, ha, h_abs_a⟩
  have h_diam_lower : V_min / (2 * (n : ℝ)) ≤ diam A :=
    scaledSumset_diam_lower hA hA_nonempty hv hvol hV_min_pos (by linarith)
  have h_abs_a_lower : c_base ≤ |a| := by
    have h1 : (V_min / (2 * (n : ℝ))) / 4 ≤ diam A / 4 := by gcongr
    have h2 : (V_min / (2 * (n : ℝ))) / 4 = V_min / (8 * (n : ℝ)) := by ring
    rw [h2] at h1
    exact le_trans h1 h_abs_a
  let c : ℝ := a ^ (N - d)
  have hc_ne_zero : c ≠ 0 := by
    have ha_ne_zero : a ≠ 0 := by
      have h_pos_abs : 0 < |a| := lt_of_lt_of_le hc_base_pos h_abs_a_lower
      exact abs_ne_zero.mp h_pos_abs.ne'
    simp [c, ha_ne_zero] <;> positivity
  have h_abs_c : |c| ≥ c_base ^ (N - d) := by
    have h1 : |c| = |a| ^ (N - d) := by
      simp [c, abs_pow]
    rw [h1]
    gcongr <;> linarith
  let S := ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A d) M
  have hS_meas : MeasurableSet S :=
    (iteratedDifference_compact (productSet_compact hA)).measurableSet
  have h_sub1 : (fun x : ℝ => c * x) '' S ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) M :=
    iteratedDifference_pad_product a ha hd
  have h_vol_image : volume ((fun x : ℝ => c * x) '' S) =
      ENNReal.ofReal |c| * volume S :=
    volume_dilation hc_ne_zero hS_meas
  have h_vol_image_lower : volume ((fun x : ℝ => c * x) '' S) ≥
      ENNReal.ofReal (c_base ^ (N - d) * finalVolume V_min n) := by
    rw [h_vol_image]
    have h1 : ENNReal.ofReal |c| * volume S ≥
        ENNReal.ofReal (c_base ^ (N - d)) * ENNReal.ofReal (finalVolume V_min n) := by
      have h1a : ENNReal.ofReal |c| ≥ ENNReal.ofReal (c_base ^ (N - d)) :=
        (ENNReal.ofReal_le_ofReal_iff (by positivity)).mpr h_abs_c
      have h1b : volume S ≥ ENNReal.ofReal (finalVolume V_min n) := h_vol_dM
      exact mul_le_mul' h1a h1b
    have h2 : ENNReal.ofReal (c_base ^ (N - d)) * ENNReal.ofReal (finalVolume V_min n) =
        ENNReal.ofReal (c_base ^ (N - d) * finalVolume V_min n) := by
      rw [← ENNReal.ofReal_mul (p := c_base ^ (N - d)) (q := finalVolume V_min n)] <;> positivity
    rw [h2] at h1
    exact h1
  have h1 : volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) M) ≥
      ENNReal.ofReal c_X := by
    have h3 : volume ((fun x : ℝ => c * x) '' S) ≤
        volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) M) :=
      measure_mono h_sub1
    simpa [c_X] using le_trans h_vol_image_lower h3
  have h_nonempty : (ExpansionLemma.productSet A N).Nonempty :=
    productSet_nonempty hA_nonempty
  have h2 : ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) M ⊆
      ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A N) N :=
    iteratedDifference_pad_sum h_nonempty hM
  exact le_trans h1 (measure_mono h2)

end WeakTwoEndsSumProduct
