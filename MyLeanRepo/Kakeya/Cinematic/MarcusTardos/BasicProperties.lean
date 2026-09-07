import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Definitions
import Mathlib.Data.List.Rotate

/-!
# Basic properties of Marcus-Tardos definitions

This module proves foundational lemmas for `posOf`, `IsIntersectionReverse`,
`IsRotation`, and `IsCyclicIntersectionReverse`.

## Whiteprint node
- `BasicProperties`
-/

namespace MarcusTardos

variable {α : Type*} [DecidableEq α]

/-! ### posOf -/

/-- If `a ∈ A`, then `posOf a A` is a valid index. -/
lemma posOf_lt_length {a : α} {A : List α} (h : a ∈ A) : posOf a A < A.length := by
  induction A with
  | nil => contradiction
  | cons x xs ih =>
    simp only [posOf]
    by_cases hx : x = a
    · simp [hx, Nat.zero_lt_succ]
    · have h' : a ∈ xs := by
        simp only [List.mem_cons] at h <;> tauto
      have h'' : posOf a xs < xs.length := ih h'
      simp only [hx, ↓reduceIte, List.length_cons]
      have h3 : 1 + posOf a xs = posOf a xs + 1 := by omega
      rw [h3]
      exact Nat.add_lt_add_right h'' 1

/-- If `a ∉ A`, then `posOf a A = A.length`. -/
lemma posOf_eq_length {a : α} {A : List α} (h : a ∉ A) : posOf a A = A.length := by
  induction A with
  | nil => simp [posOf]
  | cons x xs ih =>
    have h' : a ∉ xs := by simp [List.mem_cons] at h <;> tauto
    have hx : x ≠ a := by simp [List.mem_cons] at h <;> tauto
    simp only [posOf, hx, ↓reduceIte, List.length_cons]
    rw [ih h'] <;> omega

/-- `posOf` is injective on elements of a list. -/
lemma posOf_inj {a b : α} {A : List α} (ha : a ∈ A) (hb : b ∈ A)
    (h : posOf a A = posOf b A) : a = b := by
  induction A with
  | nil => contradiction
  | cons x xs ih =>
    by_cases hxa : x = a
    · have h1 : posOf a (x :: xs) = 0 := by
        simp [posOf, hxa]
      rw [h1] at h
      by_cases hxb : x = b
      · exact hxa.symm.trans hxb
      · have h2 : posOf b (x :: xs) = 1 + posOf b xs := by
          simp [posOf, hxb]
        rw [h2] at h
        omega
    · by_cases hxb : x = b
      · have h1 : posOf a (x :: xs) = 1 + posOf a xs := by
          simp [posOf, hxa]
        have h2 : posOf b (x :: xs) = 0 := by
          simp [posOf, hxb]
        rw [h1, h2] at h
        omega
      · have h1 : posOf a (x :: xs) = 1 + posOf a xs := by
          simp [posOf, hxa]
        have h2 : posOf b (x :: xs) = 1 + posOf b xs := by
          simp [posOf, hxb]
        rw [h1, h2] at h
        have h3 : posOf a xs = posOf b xs := by
          exact Nat.add_left_cancel h
        have ha' : a ∈ xs := by simp [List.mem_cons] at ha <;> tauto
        have hb' : b ∈ xs := by simp [List.mem_cons] at hb <;> tauto
        exact ih ha' hb' h3

/-! ### IsRotation -/

private lemma drop_eq_nil_of_le {A : List α} {n : ℕ} (h : A.length ≤ n) :
    A.drop n = [] := by
  have h5 : ∀ (l : List α) (k : ℕ), l.length ≤ k → l.drop k = [] := by
    intro l
    induction l with
    | nil => intro k hk; simp
    | cons x xs ih =>
      intro k hk
      cases k with
      | zero => simp [List.length] at hk <;> omega
      | succ k' =>
        have hk' : xs.length ≤ k' := by simp [List.length] at hk <;> omega
        simpa [List.drop] using ih k' hk'
  exact h5 A n h

private lemma take_eq_self_of_le {A : List α} {n : ℕ} (h : A.length ≤ n) :
    A.take n = A := by
  have h5 : ∀ (l : List α) (k : ℕ), l.length ≤ k → l.take k = l := by
    intro l
    induction l with
    | nil => intro k hk; simp
    | cons x xs ih =>
      intro k hk
      cases k with
      | zero => simp [List.length] at hk <;> omega
      | succ k' =>
        have hk' : xs.length ≤ k' := by simp [List.length] at hk <;> omega
        simpa [List.take] using ih k' hk'
  exact h5 A n h

/-- Our `IsRotation` is equivalent to Mathlib's `List.IsRotated`. -/
lemma isRotation_iff_isRotated {A B : List α} :
    IsRotation A B ↔ List.IsRotated A B := by
  constructor
  · rintro ⟨n, hn⟩
    by_cases h : n ≤ A.length
    · refine' ⟨n, _⟩
      have h1 : A.rotate n = A.drop n ++ A.take n := by
        rw [List.rotate_eq_rotate', List.rotate'_eq_drop_append_take h]
      rw [h1, hn]
    · have h' : A.length ≤ n := by omega
      have h2 : A.drop n ++ A.take n = A := by
        rw [drop_eq_nil_of_le h', take_eq_self_of_le h'] <;> simp
      have hB : B = A := hn.trans h2
      exact hB ▸ List.IsRotated.refl A
  · rintro ⟨n, hn⟩
    by_cases hlen : A.length = 0
    · have hA : A = [] := List.eq_nil_iff_length_eq_zero.mpr hlen
      have hB : B = [] := by
        rw [hA] at hn <;> simpa using hn
      rw [hA, hB]
      exact ⟨0, by simp⟩
    · let m := n % A.length
      have hmod : A.rotate m = A.rotate n := by rw [List.rotate_mod]
      have hpos : 0 < A.length := by omega
      have hle : m ≤ A.length := (Nat.mod_lt n hpos).le
      have h1 : A.rotate m = A.drop m ++ A.take m := by
        rw [List.rotate_eq_rotate', List.rotate'_eq_drop_append_take hle]
      refine' ⟨m, _⟩
      rw [← h1, hmod, hn]

/-- `IsRotation` preserves list length. -/
lemma IsRotation.length_eq {A B : List α} (h : IsRotation A B) : A.length = B.length := by
  rw [isRotation_iff_isRotated] at h
  exact h.perm.length_eq

/-- `IsRotation` preserves the nodup property. -/
lemma IsRotation.nodup_iff {A B : List α} (h : IsRotation A B) : A.Nodup ↔ B.Nodup := by
  rw [isRotation_iff_isRotated] at h
  exact h.nodup_iff

/-- `IsRotation` preserves membership. -/
lemma IsRotation.mem_iff {A B : List α} (h : IsRotation A B) {x : α} : x ∈ A ↔ x ∈ B := by
  rw [isRotation_iff_isRotated] at h
  exact h.mem_iff

/-- `IsRotation` is reflexive. -/
lemma IsRotation.refl (A : List α) : IsRotation A A :=
  ⟨0, by simp⟩

/-- `IsRotation` is symmetric. -/
lemma IsRotation.symm {A B : List α} (h : IsRotation A B) : IsRotation B A := by
  rw [isRotation_iff_isRotated] at h ⊢
  exact h.symm

/-- `IsRotation` is transitive. -/
lemma IsRotation.trans {A B C : List α} (h1 : IsRotation A B) (h2 : IsRotation B C) :
    IsRotation A C := by
  rw [isRotation_iff_isRotated] at h1 h2 ⊢
  exact h1.trans h2

/-! ### IsIntersectionReverse -/

/-- `IsIntersectionReverse` is symmetric. -/
lemma IsIntersectionReverse.symm {A B : List α} (h : IsIntersectionReverse A B) :
    IsIntersectionReverse B A := by
  intro x hx y hy hxy hxA hyA
  have h' := h y hyA x hxA (Ne.symm hxy) hy hx
  exact h'.symm

/-- If the left list has length at most 1, `IsIntersectionReverse` holds vacuously. -/
lemma IsIntersectionReverse_of_left_length_le_one {A B : List α} (h : A.length ≤ 1) :
    IsIntersectionReverse A B := by
  cases A with
  | nil =>
    intro a ha; contradiction
  | cons x xs =>
    have hxs : xs = [] := by
      simp [List.length] at h <;> omega
    rw [hxs]
    intro a ha b hb hne
    have ha' : a = x := by simpa using ha
    have hb' : b = x := by simpa using hb
    rw [ha', hb'] at hne <;> contradiction

/-- If the right list has length at most 1, `IsIntersectionReverse` holds vacuously. -/
lemma IsIntersectionReverse_of_right_length_le_one {A B : List α} (h : B.length ≤ 1) :
    IsIntersectionReverse A B := by
  intro a ha b hb hne h_aB h_bB
  cases B with
  | nil => contradiction
  | cons x xs =>
    have hxs : xs = [] := by
      simp [List.length] at h <;> omega
    have h1 : a = x := by
      rw [hxs] at h_aB <;> simpa using h_aB
    have h2 : b = x := by
      rw [hxs] at h_bB <;> simpa using h_bB
    rw [h1, h2] at hne <;> contradiction

/-! ### IsCyclicIntersectionReverse -/

/-- `IsCyclicIntersectionReverse` is symmetric. -/
lemma IsCyclicIntersectionReverse.symm {A B : List α}
    (h : IsCyclicIntersectionReverse A B) :
    IsCyclicIntersectionReverse B A := by
  rcases h with ⟨A', B', hA, hB, hIR⟩
  refine' ⟨B', A', hB, hA, hIR.symm⟩

end MarcusTardos
