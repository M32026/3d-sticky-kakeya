import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.BlockStructure
import Mathlib.Tactic
import Mathlib.Data.Finset.Card

/-!
# Cut point argument for Block Lemma
-/

namespace MarcusTardos.CutPoint

variable {α : Type*} [DecidableEq α]

/-- Concatenate B 0, B 1, ..., B (k-1). -/
def joinRange (k : ℕ) (B : ℕ → List α) : List α :=
  match k with
  | 0 => []
  | k' + 1 => B 0 ++ joinRange k' (fun i => B (i + 1))

omit [DecidableEq α] in
lemma joinRange_succ (k : ℕ) (B : ℕ → List α) :
    joinRange (k + 1) B = B 0 ++ joinRange k (fun i => B (i + 1)) := by
  simp [joinRange]

omit [DecidableEq α] in
private lemma drop_append_le {l1 l2 : List α} {n : ℕ} (h : n ≤ l1.length) :
    List.drop n (l1 ++ l2) = List.drop n l1 ++ l2 := by
  induction l1 generalizing n with
  | nil =>
    have h_n0 : n = 0 := by simpa using h
    rw [h_n0] <;> simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n' =>
      have h' : n' ≤ xs.length := by simp [List.length] at h <;> omega
      simp [List.drop_cons, ih h'] <;> rfl

omit [DecidableEq α] in
private lemma drop_append_gt {l1 l2 : List α} {n : ℕ} (h : l1.length < n) :
    List.drop n (l1 ++ l2) = List.drop (n - l1.length) l2 := by
  induction l1 generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp at h <;> omega
    | succ n' =>
      have h' : xs.length < n' := by simp [List.length] at h <;> omega
      simp [List.drop_cons, ih h'] <;> rfl

omit [DecidableEq α] in
private lemma take_append_le {l1 l2 : List α} {n : ℕ} (h : l1.length ≤ n) :
    List.take n (l1 ++ l2) = l1 ++ List.take (n - l1.length) l2 := by
  induction l1 generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp at h <;> omega
    | succ n' =>
      have h' : xs.length ≤ n' := by simp [List.length] at h <;> omega
      simp [List.take_cons, ih h'] <;> rfl

/-- If n ≤ i*L, block i is a sublist of drop n. -/
lemma block_sublist_drop (L : ℕ) :
    ∀ (k : ℕ) (B : ℕ → List α), (∀ i < k, (B i).length = L) →
    ∀ (i n : ℕ), i < k → n ≤ i * L →
    List.Sublist (B i) (List.drop n (joinRange k B)) := by
  intro k
  induction k with
  | zero =>
    intro B _ i n hi _
    exfalso; omega
  | succ k ih =>
    intro B h_len i n hi hn
    by_cases h_i : i = 0
    · subst h_i
      have h_n0 : n = 0 := by omega
      rw [h_n0, joinRange_succ]
      exact List.sublist_append_left _ _
    · have h_i_pos : 0 < i := by omega
      rw [joinRange_succ (B := B)]
      have h6 : (B 0).length = L := h_len 0 (by omega)
      by_cases h_nL : n ≤ (B 0).length
      · rw [drop_append_le h_nL]
        have h_i_minus : i - 1 < k := by omega
        have h_ih1 := ih (fun j => B (j + 1)) (fun j hj => h_len (j + 1) (by omega)) (i - 1) 0 h_i_minus (by simp)
        have h_i_eq : i - 1 + 1 = i := by omega
        have h_ih2 : List.Sublist (B i) (joinRange k (fun j => B (j + 1))) := by
          simpa [h_i_eq] using h_ih1
        exact h_ih2.trans (List.sublist_append_right _ _)
      · have h_ngtL : (B 0).length < n := by omega
        rw [drop_append_gt h_ngtL]
        have h8 : n - (B 0).length = n - L := by rw [h6] <;> omega
        have h_i_minus : i - 1 < k := by omega
        have h_n_minus : n - L ≤ (i - 1) * L := by
          have h_iL : i * L = (i - 1) * L + L := by
            cases i with
            | zero => contradiction
            | succ i' => simp [Nat.mul_succ] <;> ring
          omega
        have h_ih1 := ih (fun j => B (j + 1)) (fun j hj => h_len (j + 1) (by omega)) (i - 1) (n - L) h_i_minus h_n_minus
        have h_i_eq : i - 1 + 1 = i := by omega
        have h_ih2 : List.Sublist (B i) (List.drop (n - L) (joinRange k (fun j => B (j + 1)))) :=
          h_i_eq ▸ h_ih1
        rw [h8]
        exact h_ih2

/-- If (i+1)*L ≤ n, block i is a sublist of take n. -/
lemma block_sublist_take (L : ℕ) :
    ∀ (k : ℕ) (B : ℕ → List α), (∀ i < k, (B i).length = L) →
    ∀ (i n : ℕ), i < k → (i + 1) * L ≤ n →
    List.Sublist (B i) (List.take n (joinRange k B)) := by
  intro k
  induction k with
  | zero =>
    intro B _ i n hi _
    exfalso; omega
  | succ k ih =>
    intro B h_len i n hi hbound
    by_cases h_i : i = 0
    · subst h_i
      rw [joinRange_succ]
      have h6 : (B 0).length = L := h_len 0 (by omega)
      have hL : L ≤ n := by
        have h : (0 + 1) * L ≤ n := hbound
        simpa [Nat.mul_one] using h
      have h7 : (B 0).length ≤ n := by
        rw [h6]; exact hL
      rw [take_append_le h7]
      exact List.sublist_append_left _ _
    · have h_i_pos : 0 < i := by omega
      rw [joinRange_succ (B := B)]
      have h6 : (B 0).length = L := h_len 0 (by omega)
      have hL : L ≤ n := by
        have h : (i + 1) * L ≤ n := hbound
        have h' : L ≤ (i + 1) * L := by
          have h'' : 0 < i + 1 := by omega
          nlinarith
        exact h'.trans h
      have h7 : (B 0).length ≤ n := by
        rw [h6]; exact hL
      rw [take_append_le h7]
      have h_i_minus : i - 1 < k := by omega
      have h_i_eq : i - 1 + 1 = i := by omega
      have h_n_minus : (i - 1 + 1) * L ≤ n - L := by
        rw [h_i_eq]
        have h_bound' : (i + 1) * L ≤ n := hbound
        have h_iL : (i + 1) * L = i * L + L := by
          cases i with
          | zero => contradiction
          | succ i' =>
            simp [Nat.mul_succ, add_assoc] <;> ring
        rw [h_iL] at h_bound'
        omega
      have h_ih1 := ih (fun j => B (j + 1)) (fun j hj => h_len (j + 1) (by omega)) (i - 1) (n - L) h_i_minus h_n_minus
      have h_ih2 : List.Sublist (B i) (List.take (n - L) (joinRange k (fun j => B (j + 1)))) :=
        h_i_eq ▸ h_ih1
      have h8 : n - (B 0).length = n - L := by rw [h6] <;> omega
      have h_ih3 : List.Sublist (B i) (List.take (n - (B 0).length) (joinRange k (fun j => B (j + 1)))) := by
        rw [h8]; exact h_ih2
      exact h_ih3.trans (List.sublist_append_right _ _)

/-- A partition of A into k consecutive blocks each of length L. -/
structure IsConsecutivePartition (A : List α) (k L : ℕ) (B : ℕ → List α) : Prop where
  concat : A = joinRange k B
  equal_length : ∀ i < k, (B i).length = L
  positive : 0 < k

/-- Block i crosses cut at n iff i*L < n < (i+1)*L. -/
def CrossesCut (L i n : ℕ) : Prop :=
  i * L < n ∧ n < (i + 1) * L

/-- At most one index crosses. -/
lemma at_most_one_crossing_index (L n : ℕ) (hL_pos : 0 < L) :
    ∀ i j : ℕ, CrossesCut L i n → CrossesCut L j n → i = j := by
  intro i j hi hj
  have h1 : i * L < n := hi.1
  have h2 : n < (i + 1) * L := hi.2
  have h3 : j * L < n := hj.1
  have h4 : n < (j + 1) * L := hj.2
  by_cases h : i ≤ j
  · have h5 : j * L < (i + 1) * L := by linarith
    have h7 : j < i + 1 := by nlinarith
    omega
  · have h' : j < i := by omega
    have h5 : i * L < (j + 1) * L := by linarith
    have h7 : i < j + 1 := by nlinarith
    omega

/-- If block i does not cross, it is a sublist of the rotation. -/
lemma noncrossing_block_sublist {A : List α} {k L : ℕ} {B : ℕ → List α}
    (hpart : IsConsecutivePartition A k L B) {i n : ℕ} (hi : i < k)
    (hn : n ≤ A.length) (h_no_cross : ¬CrossesCut L i n) :
    List.Sublist (B i) (A.drop n ++ A.take n) := by
  by_cases h1 : n ≤ i * L
  · have h_sub : List.Sublist (B i) (List.drop n A) := by
      rw [hpart.concat]
      exact block_sublist_drop L k B hpart.equal_length i n hi h1
    exact h_sub.trans (List.sublist_append_left _ _)
  · have h1' : i * L < n := by omega
    have h2 : (i + 1) * L ≤ n := by
      by_contra h3
      have h4 : n < (i + 1) * L := by omega
      exact h_no_cross ⟨h1', h4⟩
    have h_sub : List.Sublist (B i) (List.take n A) := by
      rw [hpart.concat]
      exact block_sublist_take L k B hpart.equal_length i n hi h2
    exact h_sub.trans (List.sublist_append_right _ _)

/-- At most one block fails to be a sublist of the rotation. -/
lemma at_most_one_not_sublist {A : List α} {k L : ℕ} {B : ℕ → List α}
    (hpart : IsConsecutivePartition A k L B)
    (n : ℕ) (hn : n ≤ A.length) (hL_pos : 0 < L) :
    ∀ (i j : ℕ), i < k → j < k →
      ¬ List.Sublist (B i) (A.drop n ++ A.take n) →
      ¬ List.Sublist (B j) (A.drop n ++ A.take n) →
      i = j := by
  intro i j hi hj h_not1 h_not2
  have h_cross_i : CrossesCut L i n := by
    by_contra h
    exact h_not1 (noncrossing_block_sublist (hpart := hpart) (hi := hi) (hn := hn) (h_no_cross := h))
  have h_cross_j : CrossesCut L j n := by
    by_contra h
    exact h_not2 (noncrossing_block_sublist (hpart := hpart) (hi := hj) (hn := hn) (h_no_cross := h))
  exact at_most_one_crossing_index L n hL_pos i j h_cross_i h_cross_j

/-- Non-crossing block pairs are IR. -/
lemma noncrossing_pair_IR {A A' A_rot A'_rot : List α}
    (hIR : IsIntersectionReverse A_rot A'_rot)
    (hA_rot_nodup : A_rot.Nodup) (hA'_rot_nodup : A'_rot.Nodup)
    {B B' : List α}
    (hB_sub : List.Sublist B A_rot) (hB'_sub : List.Sublist B' A'_rot) :
    IsIntersectionReverse B B' :=
  hIR.sublist hA_rot_nodup hA'_rot_nodup hB_sub hB'_sub

end MarcusTardos.CutPoint
