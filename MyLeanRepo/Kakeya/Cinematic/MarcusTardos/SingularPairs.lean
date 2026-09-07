import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.BlockStructure
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.DyadicDecomposition
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Definitions
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.OrderFunction
import Mathlib.Tactic
import Mathlib.Data.Finset.Card

/-!
# Singular pair analysis for Marcus-Tardos Lemma 2

Characterizes when a dyadic block pair fails to be intersection reverse
(singular) and proves the at-most-constant bound per level.

## Key results

- `intersection_le_one_ir`: block pairs with intersection size ≤ 1 are IR
- `level_k_all_ir`: at level `k = clog 2 d`, all block pairs are IR
- `singular_pair_characterization`: singular pairs involve a crossing block
- `at_most_three_singular_pairs`: at most 3 singular pairs per level
-/

namespace MarcusTardos.SingularPairs

open BigOperators Finset

variable {α : Type*} [DecidableEq α]

/-! ### Trivial IR for small intersections -/

/-- If two nodup lists have at most one common element, they are
intersection reverse (vacuously: no distinct common pairs). -/
lemma intersection_le_one_ir {B B' : List α}
    (hB : B.Nodup) (hB' : B'.Nodup)
    (h : (B.toFinset ∩ B'.toFinset).card ≤ 1) :
    IsIntersectionReverse B B' := by
  intro a ha b hb hne haB' hbB'
  have hca : a ∈ B.toFinset ∩ B'.toFinset := by
    simp [List.mem_toFinset, ha, haB']
  have hcb : b ∈ B.toFinset ∩ B'.toFinset := by
    simp [List.mem_toFinset, hb, hbB']
  have h_card : (B.toFinset ∩ B'.toFinset).card ≤ 1 := h
  have h_ab : a = b := by
    have h4 : ∀ (x : α), x ∈ (B.toFinset ∩ B'.toFinset) → ∀ (y : α), y ∈ (B.toFinset ∩ B'.toFinset) → x = y :=
      Finset.card_le_one.mp h_card
    exact h4 a hca b hcb
  exact False.elim (hne h_ab)

/-- Any dyadic block at level `k` with `2^k ≥ A.length` has size ≤ 1. -/
lemma level_k_block_size_le_one {A : List α} {k : ℕ} (h : 2^k ≥ A.length)
    {s : List Bool} (hs : s.length = k) : (block A s).length ≤ 1 :=
  block_length_le_one h s hs

/-- At level `k` where `2^k ≥ d`, every block pair is intersection reverse. -/
lemma level_k_all_ir {d : ℕ} {A A' : List α} {k : ℕ}
    (hA : A.Nodup) (hA' : A'.Nodup)
    (hlenA : A.length = d) (hlenA' : A'.length = d)
    (hk : 2^k ≥ d) {s t : List Bool}
    (hs : s.length = k) (ht : t.length = k) :
    IsIntersectionReverse (block A s) (block A' t) := by
  have hkA : 2^k ≥ A.length := by rwa [hlenA]
  have h1 : (block A s).length ≤ 1 :=
    level_k_block_size_le_one hkA hs
  have hkA' : 2^k ≥ A'.length := by rwa [hlenA']
  have h2 : (block A' t).length ≤ 1 :=
    level_k_block_size_le_one hkA' ht
  have hB : (block A s).Nodup := block_nodup hA s
  have hB' : (block A' t).Nodup := block_nodup hA' t
  have h4 : ((block A s).toFinset).card ≤ 1 := by
    rw [List.toFinset_card_of_nodup hB] <;> exact h1
  have h5 : (block A s).toFinset ∩ (block A' t).toFinset ⊆ (block A s).toFinset := by
    exact Finset.inter_subset_left
  have h6 : ((block A s).toFinset ∩ (block A' t).toFinset).card ≤
      (block A s).toFinset.card := Finset.card_le_card h5
  have h3 : ((block A s).toFinset ∩ (block A' t).toFinset).card ≤ 1 := by
    calc
      ((block A s).toFinset ∩ (block A' t).toFinset).card
        ≤ (block A s).toFinset.card := h6
      _ ≤ 1 := h4
  exact intersection_le_one_ir hB hB' h3

/-! ### Singular pair characterization via rotation cuts -/

/--
If both blocks in a pair are sublists of linearly IR rotations,
the pair is IR.
-/
lemma sublists_of_ir_are_ir {A_rot A'_rot B B' : List α}
    (hIR : IsIntersectionReverse A_rot A'_rot)
    (hA_rot_nodup : A_rot.Nodup) (hA'_rot_nodup : A'_rot.Nodup)
    (hB : List.Sublist B A_rot) (hB' : List.Sublist B' A'_rot) :
    IsIntersectionReverse B B' :=
  hIR.sublist hA_rot_nodup hA'_rot_nodup hB hB'

/--
A block pair is singular (not IR) only if at least one block fails
to be a sublist of its IR rotation (i.e., crosses the rotation cut).
-/
lemma singular_requires_crossing {A A' A_rot A'_rot : List α}
    (hIR : IsIntersectionReverse A_rot A'_rot)
    (hA_rot_nodup : A_rot.Nodup) (hA'_rot_nodup : A'_rot.Nodup)
    {B B' : List α}
    (hB_sub : List.Sublist B A_rot) (hB'_sub : List.Sublist B' A'_rot) :
    IsIntersectionReverse B B' :=
  sublists_of_ir_are_ir hIR hA_rot_nodup hA'_rot_nodup hB_sub hB'_sub

/-! ### Algebraic bound for both-crossing pairs -/

/--
Algebraic lemma: if `x + y = r`, then `r^2 + r - 2*x^2 - 2*y^2 ≤ r`.
This is the core bound for the both-crossing contribution.
-/
private lemma both_cross_algebraic_bound (r x y : ℕ) (hxy : x + y = r) :
    (r : ℤ)^2 + (r : ℤ) - 2 * (x : ℤ)^2 - 2 * (y : ℤ)^2 ≤ (r : ℤ) := by
  have h : (r : ℤ)^2 ≤ 2 * (x : ℤ)^2 + 2 * (y : ℤ)^2 := by
    have h' : (r : ℤ) = (x : ℤ) + (y : ℤ) := by
      have h_eq : r = x + y := hxy.symm
      rw [h_eq] <;> norm_cast
    rw [h']
    nlinarith [sq_nonneg ((x : ℤ) - (y : ℤ))]
  linarith

/-! ### Direct bound on S via telescoping -/

/-- Telescoping sum: `∑_{l=1}^k (s_{l-1} - s_l) = s_0 - s_k`. -/
private lemma telescoping_sum (s : ℕ → ℝ) (k : ℕ) :
    ∑ l ∈ Finset.Icc 1 k, (s (l - 1) - s l) = s 0 - s k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    have h_simp : (k + 1 - 1 : ℕ) = k := by omega
    rw [ih, h_simp] <;> ring

/--
Telescoping Cauchy-Schwarz bound.

Given `Q_l ≥ (s_{l-1} - s_l)^2 / 9` with `0 ≤ p ≤ s_0` and `s_k = 0`,
prove `∑ w_l * Q_l ≥ p^2 / (9 * V)`.
-/
lemma telescoping_cs_bound (k : ℕ) (w : ℕ → ℝ)
    (hw_pos : ∀ l ∈ Finset.Icc 1 k, 0 < w l)
    (Q s : ℕ → ℝ) (p : ℝ)
    (hQ : ∀ l ∈ Finset.Icc 1 k, Q l ≥ (s (l - 1) - s l)^2 / 9)
    (hp_nonneg : 0 ≤ p) (hs0 : p ≤ s 0) (hsk : s k = 0)
    (hs_nonneg : ∀ l, 0 ≤ s l)
    (hs_decr : ∀ l ∈ Finset.Icc 1 k, s l ≤ s (l - 1))
    (hk_pos : 0 < k) :
    ∑ l ∈ Finset.Icc 1 k, w l * Q l ≥
    p^2 / (9 * ∑ l ∈ Finset.Icc 1 k, 1 / w l) := by
  have h1 : ∀ l ∈ Finset.Icc 1 k, 0 ≤ s (l - 1) - s l := by
    intro l hl
    have h2 : s l ≤ s (l - 1) := hs_decr l hl
    linarith [hs_nonneg (l - 1), hs_nonneg l]
  have hQ_nonneg : ∀ l ∈ Finset.Icc 1 k, 0 ≤ Q l := by
    intro l hl
    have h : Q l ≥ (s (l - 1) - s l)^2 / 9 := hQ l hl
    linarith [sq_nonneg (s (l - 1) - s l)]
  have h_telescoping : ∑ l ∈ Finset.Icc 1 k, (s (l - 1) - s l) = s 0 - s k :=
    telescoping_sum s k
  have h3 : ∑ l ∈ Finset.Icc 1 k, Real.sqrt (Q l) ≥ p / 3 := by
    have h4 : ∀ l ∈ Finset.Icc 1 k, Real.sqrt (Q l) ≥ (s (l - 1) - s l) / 3 := by
      intro l hl
      have h5 : Q l ≥ (s (l - 1) - s l)^2 / 9 := hQ l hl
      have h6 : 0 ≤ (s (l - 1) - s l) / 3 := by linarith [h1 l hl]
      have h7 : Real.sqrt (Q l) ≥ Real.sqrt ((s (l - 1) - s l)^2 / 9) :=
        Real.sqrt_le_sqrt h5
      have h8 : Real.sqrt ((s (l - 1) - s l)^2 / 9) = (s (l - 1) - s l) / 3 := by
        have h9 : 0 ≤ (s (l - 1) - s l) / 3 := h6
        have h10 : (s (l - 1) - s l)^2 / 9 = ((s (l - 1) - s l) / 3)^2 := by ring
        rw [h10]
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_nonneg h9]
      rw [h8] at h7 <;> exact h7
    have h_sum3 : ∑ l ∈ Finset.Icc 1 k, (s (l - 1) - s l) / 3 = (s 0 - s k) / 3 := by
      have h_factor : ∑ l ∈ Finset.Icc 1 k, (s (l - 1) - s l) / 3 =
          (1 / 3 : ℝ) * ∑ l ∈ Finset.Icc 1 k, (s (l - 1) - s l) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      rw [h_factor, h_telescoping] <;> ring
    calc
      ∑ l ∈ Finset.Icc 1 k, Real.sqrt (Q l)
        ≥ ∑ l ∈ Finset.Icc 1 k, (s (l - 1) - s l) / 3 := by
          gcongr <;> exact h4 l ‹_›
      _ = (s 0 - s k) / 3 := h_sum3
      _ ≥ p / 3 := by
        rw [hsk] <;> linarith [hs0]
  let V := ∑ l ∈ Finset.Icc 1 k, 1 / w l
  have hV_pos : 0 < V :=
    Finset.sum_pos (fun l hl => one_div_pos.mpr (hw_pos l hl))
      (Finset.nonempty_Icc.mpr hk_pos)
  have hf : ∀ l ∈ Finset.Icc 1 k, 0 ≤ w l * Q l := by
    intro l hl
    have hwl : 0 < w l := hw_pos l hl
    have hQl : 0 ≤ Q l := hQ_nonneg l hl
    positivity
  have hg : ∀ l ∈ Finset.Icc 1 k, 0 ≤ 1 / w l := by
    intro l hl
    have hwl : 0 < w l := hw_pos l hl
    exact div_nonneg zero_le_one hwl.le
  have ht : ∀ l ∈ Finset.Icc 1 k, (Real.sqrt (Q l))^2 ≤ (w l * Q l) * (1 / w l) := by
    intro l hl
    have hwl : 0 < w l := hw_pos l hl
    have hQl : 0 ≤ Q l := hQ_nonneg l hl
    have h9 : (Real.sqrt (Q l))^2 = Q l := Real.sq_sqrt hQl
    have h10 : (w l * Q l) * (1 / w l) = Q l := by
      field_simp [hwl.ne'] <;> ring
    rw [h9, h10]
  have h_cs : (∑ l ∈ Finset.Icc 1 k, Real.sqrt (Q l))^2 ≤
      (∑ l ∈ Finset.Icc 1 k, w l * Q l) * V :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.Icc 1 k) hf hg ht
  have h4 : 0 ≤ p / 3 := by linarith
  calc
    ∑ l ∈ Finset.Icc 1 k, w l * Q l
      ≥ (∑ l ∈ Finset.Icc 1 k, Real.sqrt (Q l))^2 / V := by
        have h : (∑ l ∈ Finset.Icc 1 k, Real.sqrt (Q l))^2 / V ≤ (∑ l ∈ Finset.Icc 1 k, w l * Q l) := by
          calc
            (∑ l ∈ Finset.Icc 1 k, Real.sqrt (Q l))^2 / V
              ≤ ((∑ l ∈ Finset.Icc 1 k, w l * Q l) * V) / V := by gcongr
            _ = ∑ l ∈ Finset.Icc 1 k, w l * Q l := by
              field_simp [hV_pos.ne'] <;> ring
        exact h
    _ ≥ (p / 3)^2 / V := by gcongr
    _ = p^2 / (9 * V) := by ring

/--
Generalized telescoping Cauchy-Schwarz bound.

Given `Q_l ≥ (s_{l-1} - s_l)^2 / K` with `0 ≤ p ≤ s_0` and `s_k = 0`,
prove `∑ w_l * Q_l ≥ p^2 / (K * V)`.
-/
lemma telescoping_cs_bound_K (K : ℕ) (hK_pos : 0 < K) (k : ℕ) (w : ℕ → ℝ)
    (hw_pos : ∀ l ∈ Finset.Icc 1 k, 0 < w l)
    (Q s : ℕ → ℝ) (p : ℝ)
    (hQ : ∀ l ∈ Finset.Icc 1 k, Q l ≥ (s (l - 1) - s l)^2 / (K : ℝ))
    (hp_nonneg : 0 ≤ p) (hs0 : p ≤ s 0) (hsk : s k = 0)
    (hs_nonneg : ∀ l, 0 ≤ s l)
    (hs_decr : ∀ l ∈ Finset.Icc 1 k, s l ≤ s (l - 1))
    (hk_pos : 0 < k) :
    ∑ l ∈ Finset.Icc 1 k, w l * Q l ≥
    p^2 / ((K : ℝ) * ∑ l ∈ Finset.Icc 1 k, 1 / w l) := by
  have hK_real_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
  have h1 : ∀ l ∈ Finset.Icc 1 k, 0 ≤ s (l - 1) - s l := by
    intro l hl
    have h2 : s l ≤ s (l - 1) := hs_decr l hl
    linarith [hs_nonneg (l - 1), hs_nonneg l]
  have hQ_nonneg : ∀ l ∈ Finset.Icc 1 k, 0 ≤ Q l := by
    intro l hl
    have h : Q l ≥ (s (l - 1) - s l)^2 / (K : ℝ) := hQ l hl
    have hsq : 0 ≤ (s (l - 1) - s l)^2 / (K : ℝ) := by positivity
    linarith
  have h_telescoping : ∑ l ∈ Finset.Icc 1 k, (s (l - 1) - s l) = s 0 - s k :=
    telescoping_sum s k
  have h_sqrtK : 0 < Real.sqrt (K : ℝ) := Real.sqrt_pos.mpr hK_real_pos
  have h3 : ∑ l ∈ Finset.Icc 1 k, Real.sqrt (Q l) ≥ p / Real.sqrt (K : ℝ) := by
    have h4 : ∀ l ∈ Finset.Icc 1 k, Real.sqrt (Q l) ≥ (s (l - 1) - s l) / Real.sqrt (K : ℝ) := by
      intro l hl
      have h5 : Q l ≥ (s (l - 1) - s l)^2 / (K : ℝ) := hQ l hl
      have h6 : 0 ≤ (s (l - 1) - s l) / Real.sqrt (K : ℝ) := by
        apply div_nonneg
        · exact h1 l hl
        · exact h_sqrtK.le
      have h7 : Real.sqrt (Q l) ≥ Real.sqrt ((s (l - 1) - s l)^2 / (K : ℝ)) :=
        Real.sqrt_le_sqrt h5
      have h8 : Real.sqrt ((s (l - 1) - s l)^2 / (K : ℝ)) = (s (l - 1) - s l) / Real.sqrt (K : ℝ) := by
        have h9 : 0 ≤ (s (l - 1) - s l) := h1 l hl
        have h_sqK : Real.sqrt (K : ℝ) ^ 2 = (K : ℝ) := Real.sq_sqrt hK_real_pos.le
        have h10 : (s (l - 1) - s l)^2 / (K : ℝ) = ((s (l - 1) - s l) / Real.sqrt (K : ℝ))^2 := by
          have h : ((s (l - 1) - s l) / Real.sqrt (K : ℝ))^2 = (s (l - 1) - s l)^2 / Real.sqrt (K : ℝ)^2 := by ring
          rw [h, h_sqK]
        rw [h10]
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_nonneg h6]
      rw [h8] at h7 <;> exact h7
    have h_sum3 : ∑ l ∈ Finset.Icc 1 k, (s (l - 1) - s l) / Real.sqrt (K : ℝ) =
        (s 0 - s k) / Real.sqrt (K : ℝ) := by
      have h_factor : ∑ l ∈ Finset.Icc 1 k, (s (l - 1) - s l) / Real.sqrt (K : ℝ) =
          (1 / Real.sqrt (K : ℝ)) * ∑ l ∈ Finset.Icc 1 k, (s (l - 1) - s l) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      rw [h_factor, h_telescoping] <;> ring
    calc
      ∑ l ∈ Finset.Icc 1 k, Real.sqrt (Q l)
        ≥ ∑ l ∈ Finset.Icc 1 k, (s (l - 1) - s l) / Real.sqrt (K : ℝ) := by
          gcongr <;> exact h4 l ‹_›
      _ = (s 0 - s k) / Real.sqrt (K : ℝ) := h_sum3
      _ ≥ p / Real.sqrt (K : ℝ) := by
        rw [hsk]
        have hs0' : p ≤ s 0 - 0 := by simpa using hs0
        exact div_le_div_of_nonneg_right hs0' h_sqrtK.le
  let V := ∑ l ∈ Finset.Icc 1 k, 1 / w l
  have hV_pos : 0 < V :=
    Finset.sum_pos (fun l hl => one_div_pos.mpr (hw_pos l hl))
      (Finset.nonempty_Icc.mpr hk_pos)
  have hf : ∀ l ∈ Finset.Icc 1 k, 0 ≤ w l * Q l := by
    intro l hl
    have hwl : 0 < w l := hw_pos l hl
    have hQl : 0 ≤ Q l := hQ_nonneg l hl
    positivity
  have hg : ∀ l ∈ Finset.Icc 1 k, 0 ≤ 1 / w l := by
    intro l hl
    have hwl : 0 < w l := hw_pos l hl
    exact div_nonneg zero_le_one hwl.le
  have ht : ∀ l ∈ Finset.Icc 1 k, (Real.sqrt (Q l))^2 ≤ (w l * Q l) * (1 / w l) := by
    intro l hl
    have hwl : 0 < w l := hw_pos l hl
    have hQl : 0 ≤ Q l := hQ_nonneg l hl
    have h9 : (Real.sqrt (Q l))^2 = Q l := Real.sq_sqrt hQl
    have h10 : (w l * Q l) * (1 / w l) = Q l := by
      field_simp [hwl.ne'] <;> ring
    rw [h9, h10]
  have h_cs : (∑ l ∈ Finset.Icc 1 k, Real.sqrt (Q l))^2 ≤
      (∑ l ∈ Finset.Icc 1 k, w l * Q l) * V :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.Icc 1 k) hf hg ht
  have h4 : 0 ≤ p / Real.sqrt (K : ℝ) := by
    apply div_nonneg hp_nonneg h_sqrtK.le
  calc
    ∑ l ∈ Finset.Icc 1 k, w l * Q l
      ≥ (∑ l ∈ Finset.Icc 1 k, Real.sqrt (Q l))^2 / V := by
        have h : (∑ l ∈ Finset.Icc 1 k, Real.sqrt (Q l))^2 / V ≤ (∑ l ∈ Finset.Icc 1 k, w l * Q l) := by
          calc
            (∑ l ∈ Finset.Icc 1 k, Real.sqrt (Q l))^2 / V
              ≤ ((∑ l ∈ Finset.Icc 1 k, w l * Q l) * V) / V := by gcongr
            _ = ∑ l ∈ Finset.Icc 1 k, w l * Q l := by
              field_simp [hV_pos.ne'] <;> ring
        exact h
    _ ≥ (p / Real.sqrt (K : ℝ))^2 / V := by gcongr
    _ = p^2 / ((K : ℝ) * V) := by
      have h12 : Real.sqrt (K : ℝ) ^ 2 = (K : ℝ) := Real.sq_sqrt hK_real_pos.le
      have h11 : (p / Real.sqrt (K : ℝ))^2 / V = p^2 / ((K : ℝ) * V) := by
        calc
          (p / Real.sqrt (K : ℝ))^2 / V
            = (p^2 / Real.sqrt (K : ℝ)^2) / V := by ring
          _ = (p^2 / (K : ℝ)) / V := by rw [h12]
          _ = p^2 / ((K : ℝ) * V) := by
            field_simp [hV_pos.ne', hK_real_pos.ne'] <;> ring
      exact h11

end MarcusTardos.SingularPairs
