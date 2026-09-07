import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.DyadicDecomposition
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.OrderFunction
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.WeightedLowerBound
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Concrete block sum and diagonal bound

Instantiates the abstract `G` function from `WeightedLowerBound` with
concrete dyadic blocks and proves the diagonal bound assumption.

## Key results

- `G`: concrete block sum `∑_{|s|=l} orderFun(block(A, s), a, b)`
- `diagonal_bound_concrete`: `∑_{a≠b} (G A l a b)^2 ≤ d² / 2^l`
-/

namespace MarcusTardos.ConcreteBlockSum

open BigOperators Finset

variable {α : Type*} [DecidableEq α]

/-- Concrete block sum: `G A l a b = ∑_{|s|=l} orderFun(block(A, s), a, b)`. -/
noncomputable def G (A : List α) (l : ℕ) (a b : α) : ℝ :=
  ∑ s ∈ binaryStrings l, (orderFun (block A s) a b : ℝ)

/-! ### Unique block property -/

/-- Each element of a nodup list belongs to at most one block at each level. -/
lemma unique_block {A : List α} (hA : A.Nodup) {a : α} {l : ℕ}
    {s t : List Bool} (hs : s ∈ binaryStrings l) (ht : t ∈ binaryStrings l)
    (has : a ∈ block A s) (hat : a ∈ block A t) : s = t := by
  have hsl : s.length = l := binaryStrings_mem.mp hs
  have htl : t.length = l := binaryStrings_mem.mp ht
  by_contra hne
  have h_disj : Disjoint (block A s : Multiset α) (block A t) :=
    block_disjoint hA (by omega) hne
  have h1 : a ∈ (block A s : Multiset α) := by exact_mod_cast has
  have h2 : a ∈ (block A t : Multiset α) := by exact_mod_cast hat
  exact Multiset.disjoint_left.mp h_disj h1 h2

/-! ### Sum of orderFun squares -/

/-- For a nodup list `B` whose elements are in `alphabet`, the sum of
squares of `orderFun` over distinct ordered pairs equals `|B|(|B|-1)`. -/
lemma sum_orderFun_sq {B : List α} (hB : B.Nodup) {alphabet : Finset α}
    (halph : ∀ x ∈ B, x ∈ alphabet) :
    ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, (orderFun B a b : ℝ)^2 =
    (B.length : ℝ) * ((B.length : ℝ) - 1) := by
  have h1 : ∀ a ∈ alphabet, (∑ b ∈ alphabet.erase a, (orderFun B a b : ℝ)^2) =
      if a ∈ B then ((B.length : ℝ) - 1) else 0 := by
    intro a ha
    by_cases h_aB : a ∈ B
    · -- a ∈ B
      have h2 : ∀ b ∈ alphabet.erase a, (orderFun B a b : ℝ)^2 =
          if b ∈ B then 1 else 0 := by
        intro b hb
        have hba : b ≠ a := by
          simp only [Finset.mem_erase] at hb <;> tauto
        by_cases h_bB : b ∈ B
        · have h3 : (orderFun B a b)^2 = 1 := orderFun_sq_eq_one h_aB h_bB hba.symm
          have h4 : (orderFun B a b : ℝ)^2 = 1 := by exact_mod_cast h3
          rw [h4]
          simp [h_bB]
        · have h4 : orderFun B a b = 0 := by
            rw [orderFun_eq_zero_iff] <;> tauto
          have h5 : (orderFun B a b : ℝ)^2 = 0 := by
            rw [h4] <;> norm_num
          rw [h5]
          simp [h_bB]
      have h_sum : ∑ b ∈ alphabet.erase a, (orderFun B a b : ℝ)^2 =
          ∑ b ∈ alphabet.erase a, (if b ∈ B then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl h2
      rw [h_sum]
      have h3 : ∑ b ∈ alphabet.erase a, (if b ∈ B then (1 : ℝ) else 0) =
          ((B.toFinset.erase a).card : ℝ) := by
        have h4 : ∑ b ∈ alphabet.erase a, (if b ∈ B then (1 : ℝ) else 0) =
            ((alphabet.erase a).filter (fun b => b ∈ B)).card := by
          rw [Finset.sum_ite] <;> simp
        rw [h4]
        have h5 : (alphabet.erase a).filter (fun b => b ∈ B) = B.toFinset.erase a := by
          apply Finset.ext
          intro x
          simp only [Finset.mem_filter, Finset.mem_erase, List.mem_toFinset]
          constructor
          · rintro ⟨⟨hne, hxa⟩, hxB⟩
            exact ⟨hne, hxB⟩
          · rintro ⟨hne, hxB⟩
            exact ⟨⟨hne, halph x hxB⟩, hxB⟩
        rw [h5] <;> rfl
      rw [h3]
      have h6 : (B.toFinset.erase a).card = B.length - 1 := by
        have h7 : B.toFinset.card = B.length := List.toFinset_card_of_nodup hB
        have h8 : a ∈ B.toFinset := by simpa [List.mem_toFinset] using h_aB
        rw [Finset.card_erase_of_mem h8, h7] <;> omega
      rw [h6]
      have h9 : ((B.length - 1 : ℕ) : ℝ) = (B.length : ℝ) - 1 := by
        have h10 : 0 < B.length := by
          cases B with
          | nil => contradiction
          | cons _ _ => simp
        rw [Nat.cast_sub h10] <;> norm_num
      rw [h9]
      have h11 : (if a ∈ B then (B.length : ℝ) - 1 else (0 : ℝ)) = (B.length : ℝ) - 1 := by
        rw [if_pos h_aB]
      exact h11.symm
    · -- a ∉ B
      have h2 : ∀ b ∈ alphabet.erase a, (orderFun B a b : ℝ)^2 = 0 := by
        intro b _
        have h3 : orderFun B a b = 0 := by
          rw [orderFun_eq_zero_iff] <;> tauto
        rw [h3] <;> norm_num
      have h_sum : ∑ b ∈ alphabet.erase a, (orderFun B a b : ℝ)^2 = 0 := by
        rw [Finset.sum_congr rfl h2] <;> simp
      rw [h_sum]
      simp [h_aB]
  calc
    ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, (orderFun B a b : ℝ)^2
      = ∑ a ∈ alphabet, (if a ∈ B then ((B.length : ℝ) - 1) else 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact h1 a ha
    _ = ∑ a ∈ B.toFinset, ((B.length : ℝ) - 1) := by
      have h3 : ∑ a ∈ alphabet, (if a ∈ B then (B.length : ℝ) - 1 else 0) =
          ∑ a ∈ alphabet.filter (fun a => a ∈ B), ((B.length : ℝ) - 1) := by
        rw [Finset.sum_ite] <;> simp
      rw [h3]
      have h4 : alphabet.filter (fun a => a ∈ B) = B.toFinset := by
        apply Finset.ext
        intro x
        simp only [Finset.mem_filter, List.mem_toFinset]
        constructor
        · rintro ⟨_, hx⟩
          exact hx
        · intro hx
          exact ⟨halph x hx, hx⟩
      rw [h4]
    _ = (B.toFinset.card : ℝ) * ((B.length : ℝ) - 1) := by
      rw [Finset.sum_const] <;> ring
    _ = (B.length : ℝ) * ((B.length : ℝ) - 1) := by
      have h5 : B.toFinset.card = B.length := List.toFinset_card_of_nodup hB
      rw [h5] <;> ring

/-! ### Square of G equals sum of squares -/

/-- If at most one term in a finite sum is nonzero, the square of the sum
equals the sum of squares. -/
private lemma sq_sum_at_most_one_nonzero {β : Type*} [DecidableEq β] {s : Finset β} {f : β → ℝ}
    (h : ∀ x y, x ∈ s → y ∈ s → f x ≠ 0 → f y ≠ 0 → x = y) :
    (∑ x ∈ s, f x)^2 = ∑ x ∈ s, (f x)^2 := by
  by_cases h_exists : ∃ x ∈ s, f x ≠ 0
  · rcases h_exists with ⟨x0, hx0, hnz⟩
    have h_unique : ∀ y ∈ s, f y ≠ 0 → y = x0 := by
      intro y hy hny
      exact h y x0 hy hx0 hny hnz
    have h_sum : ∑ z ∈ s, f z = f x0 := by
      rw [Finset.sum_eq_single_of_mem x0 hx0]
      intro y hy hne
      have hfy : f y = 0 := by
        by_contra h'
        exact hne (h_unique y hy h')
      exact hfy
    have h_sum_sq : ∑ z ∈ s, (f z)^2 = (f x0)^2 := by
      rw [Finset.sum_eq_single_of_mem x0 hx0]
      intro y hy hne
      have hfy : f y = 0 := by
        by_contra h'
        exact hne (h_unique y hy h')
      rw [hfy] <;> ring
    rw [h_sum, h_sum_sq]
  · have h_all_zero : ∀ x ∈ s, f x = 0 := by
      intro x hx
      by_contra h'
      exact h_exists ⟨x, hx, h'⟩
    have h_sum : ∑ x ∈ s, f x = 0 := by
      rw [Finset.sum_congr rfl h_all_zero] <;> simp
    have h_sum_sq : ∑ x ∈ s, (f x)^2 = 0 := by
      rw [Finset.sum_congr rfl (fun x hx => by rw [h_all_zero x hx])] <;> simp
    rw [h_sum, h_sum_sq] <;> ring

/-- For concrete `G`, the square equals the sum of squares because at most
one block contains both `a` and `b`. -/
lemma G_sq_eq_sum_sq {A : List α} (hA : A.Nodup) {l : ℕ} {a b : α} :
    (G A l a b)^2 = ∑ s ∈ binaryStrings l, (orderFun (block A s) a b : ℝ)^2 := by
  let f : List Bool → ℝ := fun s => (orderFun (block A s) a b : ℝ)
  have h_at_most_one : ∀ (s t : List Bool), s ∈ binaryStrings l → t ∈ binaryStrings l →
      f s ≠ 0 → f t ≠ 0 → s = t := by
    intro s t hs ht hfs hft
    have has : a ∈ block A s := by
      have h : f s ≠ 0 := hfs
      dsimp only [f] at h
      have h' : (orderFun (block A s) a b : ℝ) ≠ 0 := h
      have h'' : orderFun (block A s) a b ≠ 0 := by exact_mod_cast h'
      have h_contra : a ∈ block A s ∧ b ∈ block A s := by
        by_contra h3
        have h4 : orderFun (block A s) a b = 0 := by
          rw [orderFun_eq_zero_iff] <;> tauto
        exact h'' h4
      exact h_contra.1
    have hat : a ∈ block A t := by
      have h : f t ≠ 0 := hft
      dsimp only [f] at h
      have h' : (orderFun (block A t) a b : ℝ) ≠ 0 := h
      have h'' : orderFun (block A t) a b ≠ 0 := by exact_mod_cast h'
      have h_contra : a ∈ block A t ∧ b ∈ block A t := by
        by_contra h3
        have h4 : orderFun (block A t) a b = 0 := by
          rw [orderFun_eq_zero_iff] <;> tauto
        exact h'' h4
      exact h_contra.1
    exact unique_block hA hs ht has hat
  exact sq_sum_at_most_one_nonzero h_at_most_one

/-! ### Diagonal bound -/

/-- The diagonal bound for concrete `G`:
`∑_{a,b≠a} (G A l a b)^2 ≤ d² / 2^l`. -/
lemma diagonal_bound_concrete {A : List α} (hA : A.Nodup) (d : ℕ) (hlen : A.length = d)
    {alphabet : Finset α} (halph : ∀ x ∈ A, x ∈ alphabet) (l : ℕ) :
    ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, (G A l a b)^2 ≤ (d : ℝ)^2 / (2 : ℝ)^l := by
  have h2 : ∀ a ∈ alphabet, ∀ b ∈ alphabet.erase a,
      (G A l a b)^2 = ∑ s ∈ binaryStrings l, (orderFun (block A s) a b : ℝ)^2 := by
    intro a _ b _
    exact G_sq_eq_sum_sq hA
  have h1 : ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, (G A l a b)^2 =
      ∑ s ∈ binaryStrings l, ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
        (orderFun (block A s) a b : ℝ)^2 := by
    have h_step1 : ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, (G A l a b)^2 =
        ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, ∑ s ∈ binaryStrings l,
          (orderFun (block A s) a b : ℝ)^2 := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact h2 a ha b hb
    rw [h_step1]
    have h_comm1 : ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, ∑ s ∈ binaryStrings l,
          (orderFun (block A s) a b : ℝ)^2 =
        ∑ a ∈ alphabet, ∑ s ∈ binaryStrings l, ∑ b ∈ alphabet.erase a,
          (orderFun (block A s) a b : ℝ)^2 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    rw [h_comm1]
    have h_comm2 : ∑ a ∈ alphabet, ∑ s ∈ binaryStrings l, ∑ b ∈ alphabet.erase a,
          (orderFun (block A s) a b : ℝ)^2 =
        ∑ s ∈ binaryStrings l, ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
          (orderFun (block A s) a b : ℝ)^2 := by
      rw [Finset.sum_comm]
    exact h_comm2
  rw [h1]
  have h3 : ∀ s ∈ binaryStrings l, ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
      (orderFun (block A s) a b : ℝ)^2 =
      ((block A s).length : ℝ) * (((block A s).length : ℝ) - 1) := by
    intro s _
    have hB : (block A s).Nodup := block_nodup hA s
    have hB_alph : ∀ x ∈ block A s, x ∈ alphabet := by
      intro x hx
      have h_sub : x ∈ A := (block_sublist A s).subset hx
      exact halph x h_sub
    exact sum_orderFun_sq hB hB_alph
  rw [Finset.sum_congr rfl h3]
  let k_s : List Bool → ℝ := fun s => (block A s).length
  have h_sum_nat : ∑ s ∈ binaryStrings l, (block A s).length = A.length :=
    sum_block_lengths A l
  have h_sum : ∑ s ∈ binaryStrings l, k_s s = (d : ℝ) := by
    dsimp only [k_s]
    have h : ∑ s ∈ binaryStrings l, (block A s).length = d := by
      rw [h_sum_nat, hlen]
    exact_mod_cast h
  have h_max : ∀ s ∈ binaryStrings l, k_s s ≤ (d : ℝ) / (2 : ℝ)^l + 1 := by
    intro s hs
    have h5 : (block A s).length ≤ A.length / 2^s.length + 1 := block_length_le A s
    have h6 : s.length = l := binaryStrings_mem.mp hs
    rw [h6] at h5
    have h7 : ((block A s).length : ℝ) ≤ ↑(A.length / 2^l) + 1 := by exact_mod_cast h5
    have h_pos2 : 0 < (2 : ℝ)^l := by positivity
    have h8 : (↑(A.length / 2^l) : ℝ) ≤ (A.length : ℝ) / (2 : ℝ)^l := by
      have h9 : (A.length / 2^l : ℕ) * (2^l) ≤ A.length := Nat.div_mul_le_self A.length (2^l)
      have h10 : ((A.length / 2^l : ℕ) : ℝ) * ((2 : ℝ)^l) ≤ (A.length : ℝ) := by exact_mod_cast h9
      calc
        (↑(A.length / 2^l) : ℝ)
          = ((↑(A.length / 2^l) : ℝ) * ((2 : ℝ)^l)) / ((2 : ℝ)^l) := by field_simp [h_pos2.ne'] <;> ring
        _ ≤ (A.length : ℝ) / ((2 : ℝ)^l) := by gcongr
    rw [hlen] at *
    <;> linarith
  have h9 : ∑ s ∈ binaryStrings l, (k_s s)^2 ≤
      ((d : ℝ) / (2 : ℝ)^l + 1) * ∑ s ∈ binaryStrings l, k_s s := by
    calc
      ∑ s ∈ binaryStrings l, (k_s s)^2
        ≤ ∑ s ∈ binaryStrings l, ((d : ℝ) / (2 : ℝ)^l + 1) * (k_s s) := by
          apply Finset.sum_le_sum
          intro s hs
          have h10 : (k_s s)^2 ≤ ((d : ℝ) / (2 : ℝ)^l + 1) * (k_s s) := by
            have h11 : 0 ≤ k_s s := by positivity
            nlinarith [h_max s hs]
          exact h10
      _ = ((d : ℝ) / (2 : ℝ)^l + 1) * ∑ s ∈ binaryStrings l, k_s s := by
        rw [Finset.mul_sum]
  have h_final : ∑ s ∈ binaryStrings l, (k_s s) * ((k_s s) - 1) ≤ (d : ℝ)^2 / (2 : ℝ)^l := by
    have h10 : ∑ s ∈ binaryStrings l, (k_s s) * ((k_s s) - 1) =
        ∑ s ∈ binaryStrings l, (k_s s)^2 - ∑ s ∈ binaryStrings l, k_s s := by
      have h11 : ∀ s ∈ binaryStrings l, (k_s s) * ((k_s s) - 1) = (k_s s)^2 - k_s s := by
        intro s _
        ring
      rw [Finset.sum_congr rfl h11, Finset.sum_sub_distrib]
    rw [h10]
    rw [h_sum] at h9
    have h12 : ∑ s ∈ binaryStrings l, (k_s s)^2 - ∑ s ∈ binaryStrings l, k_s s ≤
        (d : ℝ)^2 / (2 : ℝ)^l := by
      rw [h_sum]
      have h13 : ∑ s ∈ binaryStrings l, (k_s s)^2 - (d : ℝ) ≤
          ((d : ℝ) / (2 : ℝ)^l + 1) * (d : ℝ) - (d : ℝ) := by
        exact sub_le_sub h9 (le_refl (d : ℝ))
      have h14 : ((d : ℝ) / (2 : ℝ)^l + 1) * (d : ℝ) - (d : ℝ) = (d : ℝ)^2 / (2 : ℝ)^l := by ring
      rw [h14] at h13
      exact h13
    exact h12
  exact h_final

end MarcusTardos.ConcreteBlockSum
