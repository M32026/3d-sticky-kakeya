import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.GraphLensBridge.ChordOrder

/-!
# A list criterion for cyclic intersection reversal

Two nodup cyclic lists are intersection reverse once no three common symbols
have the same positive cyclic order.  The proof cuts the first list at a
common pivot and the second immediately after the same pivot.
-/

namespace Kakeya.Cinematic.GraphLensBridge

open MarcusTardos

variable {α : Type*} [DecidableEq α]

theorem posOf_eq_idxOf (a : α) (list : List α) :
    posOf a list = list.idxOf a := by
  induction list with
  | nil => rfl
  | cons head tail ih =>
      simp only [posOf, List.idxOf_cons]
      split_ifs with h
      · subst head
        simp
      · simp [beq_false_of_ne h, ih, Nat.add_comm]

theorem idxOf_rotate (list : List α) (hnodup : list.Nodup)
    (a : α) (ha : a ∈ list) (k : ℕ) (hk : k < list.length) :
    (list.rotate k).idxOf a =
      (list.idxOf a + list.length - k) % list.length := by
  let position := (list.idxOf a + list.length - k) % list.length
  have hlength : 0 < list.length := lt_of_le_of_lt (Nat.zero_le k) hk
  have hposition : position < list.length := Nat.mod_lt _ hlength
  have hpositionRotate : position < (list.rotate k).length := by
    simpa using hposition
  have hidx : list.idxOf a < list.length :=
    List.idxOf_lt_length_of_mem ha
  have harith : (position + k) % list.length = list.idxOf a := by
    dsimp [position]
    by_cases hki : k ≤ list.idxOf a
    · have hsub :
          list.idxOf a + list.length - k =
            list.idxOf a - k + list.length := by
        omega
      rw [hsub, Nat.add_mod_right]
      have hsmall : list.idxOf a - k < list.length := by omega
      rw [Nat.mod_eq_of_lt hsmall]
      have hcancel : list.idxOf a - k + k = list.idxOf a :=
        Nat.sub_add_cancel hki
      rw [hcancel, Nat.mod_eq_of_lt hidx]
    · have hik : list.idxOf a < k := Nat.lt_of_not_ge hki
      have hsub : list.idxOf a + list.length - k < list.length := by
        omega
      rw [Nat.mod_eq_of_lt hsub]
      have hsum :
          list.idxOf a + list.length - k + k =
            list.idxOf a + list.length := by
        omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hidx]
  have hgetRaw :=
    List.get_rotate list k ⟨position, hpositionRotate⟩
  have hright :
      list.get ⟨(position + k) % list.length,
        Nat.mod_lt _ (by positivity)⟩ = a := by
    have hbase := List.idxOf_get hidx
    convert hbase using 1 <;> simp [harith]
  have hget :
      (list.rotate k).get ⟨position, hpositionRotate⟩ = a :=
    hgetRaw.trans hright
  have hrotateNodup : (list.rotate k).Nodup :=
    List.nodup_rotate.mpr hnodup
  have hpos := List.get_idxOf hrotateNodup ⟨position, hpositionRotate⟩
  rw [hget] at hpos
  exact hpos

private theorem cyclicLT_swap
    {n p a b : ℕ} (hp : p < n) (ha : a < n) (hb : b < n)
    (hpa : p ≠ a) (hpb : p ≠ b) (hab : a ≠ b) :
    CyclicLT p a b ↔ ¬CyclicLT p b a := by
  unfold CyclicLT
  omega

private theorem at_order_nat {n p a b : ℕ}
    (hp : p < n) (ha : a < n) (hb : b < n)
    (hpa : p ≠ a) (hpb : p ≠ b) :
    (a + n - p) % n < (b + n - p) % n ↔
      CyclicLT p a b := by
  by_cases hpaLe : p ≤ a
  · have haEq : a + n - p = a - p + n := by omega
    rw [haEq, Nat.add_mod_right]
    have haSmall : a - p < n := by omega
    rw [Nat.mod_eq_of_lt haSmall]
    by_cases hpbLe : p ≤ b
    · have hbEq : b + n - p = b - p + n := by omega
      rw [hbEq, Nat.add_mod_right]
      have hbSmall : b - p < n := by omega
      rw [Nat.mod_eq_of_lt hbSmall]
      unfold CyclicLT
      omega
    · have hbp : b < p := Nat.lt_of_not_ge hpbLe
      have hbSmall : b + n - p < n := by omega
      rw [Nat.mod_eq_of_lt hbSmall]
      unfold CyclicLT
      omega
  · have hap : a < p := Nat.lt_of_not_ge hpaLe
    have haSmall : a + n - p < n := by omega
    rw [Nat.mod_eq_of_lt haSmall]
    by_cases hpbLe : p ≤ b
    · have hbEq : b + n - p = b - p + n := by omega
      rw [hbEq, Nat.add_mod_right]
      have hbSmall : b - p < n := by omega
      rw [Nat.mod_eq_of_lt hbSmall]
      unfold CyclicLT
      omega
    · have hbp : b < p := Nat.lt_of_not_ge hpbLe
      have hbSmall : b + n - p < n := by omega
      rw [Nat.mod_eq_of_lt hbSmall]
      unfold CyclicLT
      omega

private theorem after_order_nat {n p a b : ℕ}
    (hp : p < n) (ha : a < n) (hb : b < n)
    (hpa : p ≠ a) (hpb : p ≠ b) :
    (a + n - (p + 1)) % n < (b + n - (p + 1)) % n ↔
      CyclicLT p a b := by
  by_cases hpaLt : p < a
  · have haEq : a + n - (p + 1) = a - (p + 1) + n := by omega
    rw [haEq, Nat.add_mod_right]
    have haSmall : a - (p + 1) < n := by omega
    rw [Nat.mod_eq_of_lt haSmall]
    by_cases hpbLt : p < b
    · have hbEq : b + n - (p + 1) = b - (p + 1) + n := by omega
      rw [hbEq, Nat.add_mod_right]
      have hbSmall : b - (p + 1) < n := by omega
      rw [Nat.mod_eq_of_lt hbSmall]
      unfold CyclicLT
      omega
    · have hbp : b < p := by omega
      have hbSmall : b + n - (p + 1) < n := by omega
      rw [Nat.mod_eq_of_lt hbSmall]
      unfold CyclicLT
      omega
  · have hap : a < p := by omega
    have haSmall : a + n - (p + 1) < n := by omega
    rw [Nat.mod_eq_of_lt haSmall]
    by_cases hpbLt : p < b
    · have hbEq : b + n - (p + 1) = b - (p + 1) + n := by omega
      rw [hbEq, Nat.add_mod_right]
      have hbSmall : b - (p + 1) < n := by omega
      rw [Nat.mod_eq_of_lt hbSmall]
      unfold CyclicLT
      omega
    · have hbp : b < p := by omega
      have hbSmall : b + n - (p + 1) < n := by omega
      rw [Nat.mod_eq_of_lt hbSmall]
      unfold CyclicLT
      omega

private theorem rotate_at_order
    (list : List α) (hnodup : list.Nodup)
    {pivot a b : α} (hpivot : pivot ∈ list)
    (ha : a ∈ list) (hb : b ∈ list)
    (hpa : pivot ≠ a) (hpb : pivot ≠ b) :
    (list.rotate (list.idxOf pivot)).idxOf a <
        (list.rotate (list.idxOf pivot)).idxOf b ↔
      CyclicLT (list.idxOf pivot) (list.idxOf a) (list.idxOf b) := by
  have hpivotIdx : list.idxOf pivot < list.length :=
    List.idxOf_lt_length_of_mem hpivot
  have haIdx : list.idxOf a < list.length :=
    List.idxOf_lt_length_of_mem ha
  have hbIdx : list.idxOf b < list.length :=
    List.idxOf_lt_length_of_mem hb
  have hpaIdx : list.idxOf pivot ≠ list.idxOf a := by
    intro h
    exact hpa ((List.idxOf_inj hpivot).mp h)
  have hpbIdx : list.idxOf pivot ≠ list.idxOf b := by
    intro h
    exact hpb ((List.idxOf_inj hpivot).mp h)
  rw [idxOf_rotate list hnodup a ha _ hpivotIdx,
    idxOf_rotate list hnodup b hb _ hpivotIdx]
  exact at_order_nat hpivotIdx haIdx hbIdx hpaIdx hpbIdx

private theorem rotate_after_order
    (list : List α) (hnodup : list.Nodup)
    {pivot a b : α} (hpivot : pivot ∈ list)
    (ha : a ∈ list) (hb : b ∈ list)
    (hpa : pivot ≠ a) (hpb : pivot ≠ b) :
    (list.rotate (list.idxOf pivot + 1)).idxOf a <
        (list.rotate (list.idxOf pivot + 1)).idxOf b ↔
      CyclicLT (list.idxOf pivot) (list.idxOf a) (list.idxOf b) := by
  have hpivotIdx : list.idxOf pivot < list.length :=
    List.idxOf_lt_length_of_mem hpivot
  have hk : list.idxOf pivot + 1 ≤ list.length := Nat.succ_le_of_lt hpivotIdx
  by_cases hkEq : list.idxOf pivot + 1 = list.length
  · rw [hkEq, List.rotate_length]
    have haIdx : list.idxOf a < list.length :=
      List.idxOf_lt_length_of_mem ha
    have hbIdx : list.idxOf b < list.length :=
      List.idxOf_lt_length_of_mem hb
    have hpaIdx : list.idxOf pivot ≠ list.idxOf a := by
      intro h
      exact hpa ((List.idxOf_inj hpivot).mp h)
    have hpbIdx : list.idxOf pivot ≠ list.idxOf b := by
      intro h
      exact hpb ((List.idxOf_inj hpivot).mp h)
    unfold CyclicLT
    omega
  · have hkLt : list.idxOf pivot + 1 < list.length :=
      lt_of_le_of_ne hk hkEq
    have haIdx : list.idxOf a < list.length :=
      List.idxOf_lt_length_of_mem ha
    have hbIdx : list.idxOf b < list.length :=
      List.idxOf_lt_length_of_mem hb
    have hpaIdx : list.idxOf pivot ≠ list.idxOf a := by
      intro h
      exact hpa ((List.idxOf_inj hpivot).mp h)
    have hpbIdx : list.idxOf pivot ≠ list.idxOf b := by
      intro h
      exact hpb ((List.idxOf_inj hpivot).mp h)
    rw [idxOf_rotate list hnodup a ha _ hkLt,
      idxOf_rotate list hnodup b hb _ hkLt]
    exact after_order_nat hpivotIdx haIdx hbIdx hpaIdx hpbIdx

private theorem pivot_first
    (list : List α) (hnodup : list.Nodup)
    {pivot : α} (hpivot : pivot ∈ list) :
    (list.rotate (list.idxOf pivot)).idxOf pivot = 0 := by
  have hpivotIdx : list.idxOf pivot < list.length :=
    List.idxOf_lt_length_of_mem hpivot
  rw [idxOf_rotate list hnodup pivot hpivot _ hpivotIdx]
  have hlength : 0 < list.length := Nat.zero_lt_of_lt hpivotIdx
  have hvalue :
      list.idxOf pivot + list.length - list.idxOf pivot = list.length := by
    omega
  rw [hvalue, Nat.mod_self]

private theorem pivot_last
    (list : List α) (hnodup : list.Nodup)
    {pivot : α} (hpivot : pivot ∈ list) :
    (list.rotate (list.idxOf pivot + 1)).idxOf pivot =
      list.length - 1 := by
  have hpivotIdx : list.idxOf pivot < list.length :=
    List.idxOf_lt_length_of_mem hpivot
  have hk : list.idxOf pivot + 1 ≤ list.length := Nat.succ_le_of_lt hpivotIdx
  by_cases hkEq : list.idxOf pivot + 1 = list.length
  · rw [hkEq, List.rotate_length]
    omega
  · have hkLt : list.idxOf pivot + 1 < list.length :=
      lt_of_le_of_ne hk hkEq
    rw [idxOf_rotate list hnodup pivot hpivot _ hkLt]
    have hlength : 0 < list.length := Nat.zero_lt_of_lt hpivotIdx
    have hvalue :
        list.idxOf pivot + list.length - (list.idxOf pivot + 1) =
          list.length - 1 := by
      omega
    rw [hvalue, Nat.mod_eq_of_lt]
    omega

/--
If no ordered triple of common symbols has the same cyclic orientation, then
the two cyclic lists are intersection reverse.
-/
theorem cyclicIntersectionReverse_of_no_common_cyclic_triple
    (first second : List α) (hfirst : first.Nodup)
    (hsecond : second.Nodup)
    (hno :
      ∀ pivot a b,
        pivot ∈ first → pivot ∈ second →
        a ∈ first → a ∈ second →
        b ∈ first → b ∈ second →
        pivot ≠ a → pivot ≠ b → a ≠ b →
        CyclicLT (first.idxOf pivot) (first.idxOf a) (first.idxOf b) →
        ¬CyclicLT (second.idxOf pivot) (second.idxOf a) (second.idxOf b)) :
    IsCyclicIntersectionReverse first second := by
  classical
  by_cases hcommon : ∃ pivot, pivot ∈ first ∧ pivot ∈ second
  · rcases hcommon with ⟨pivot, hpivotFirst, hpivotSecond⟩
    let first' := first.rotate (first.idxOf pivot)
    let second' := second.rotate (second.idxOf pivot + 1)
    refine ⟨first', second', ?_, ?_, ?_⟩
    · refine ⟨first.idxOf pivot, ?_⟩
      exact List.rotate_eq_drop_append_take
        (List.idxOf_lt_length_of_mem hpivotFirst).le
    · refine ⟨second.idxOf pivot + 1, ?_⟩
      exact List.rotate_eq_drop_append_take
        (Nat.succ_le_of_lt (List.idxOf_lt_length_of_mem hpivotSecond))
    · intro a haFirst' b hbFirst' hab haSecond' hbSecond'
      have haFirst : a ∈ first := List.mem_rotate.mp haFirst'
      have hbFirst : b ∈ first := List.mem_rotate.mp hbFirst'
      have haSecond : a ∈ second := List.mem_rotate.mp haSecond'
      have hbSecond : b ∈ second := List.mem_rotate.mp hbSecond'
      rw [posOf_eq_idxOf, posOf_eq_idxOf, posOf_eq_idxOf, posOf_eq_idxOf]
      by_cases hap : a = pivot
      · subst a
        have hfirstPivot := pivot_first first hfirst hpivotFirst
        have hsecondPivot := pivot_last second hsecond hpivotSecond
        have hbFirstIdx :
            (first.rotate (first.idxOf pivot)).idxOf b <
              first.length := by
          rw [← List.length_rotate first (first.idxOf pivot)]
          exact List.idxOf_lt_length_of_mem hbFirst'
        have hbSecondIdx :
            (second.rotate (second.idxOf pivot + 1)).idxOf b <
              second.length := by
          rw [← List.length_rotate second (second.idxOf pivot + 1)]
          exact List.idxOf_lt_length_of_mem hbSecond'
        have hpivotFirst' :
            pivot ∈ first.rotate (first.idxOf pivot) :=
          List.mem_rotate.mpr hpivotFirst
        have hpivotSecond' :
            pivot ∈ second.rotate (second.idxOf pivot + 1) :=
          List.mem_rotate.mpr hpivotSecond
        have hfirstNe :
            (first.rotate (first.idxOf pivot)).idxOf b ≠
              (first.rotate (first.idxOf pivot)).idxOf pivot := by
          intro h
          exact hab ((List.idxOf_inj hpivotFirst').mp h.symm)
        have hsecondNe :
            (second.rotate (second.idxOf pivot + 1)).idxOf b ≠
              (second.rotate (second.idxOf pivot + 1)).idxOf pivot := by
          intro h
          exact hab ((List.idxOf_inj hpivotSecond').mp h.symm)
        simp only [first', second']
        rw [hfirstPivot, hsecondPivot]
        constructor <;> intro
        · omega
        · omega
      · by_cases hbp : b = pivot
        · subst b
          have hfirstPivot := pivot_first first hfirst hpivotFirst
          have hsecondPivot := pivot_last second hsecond hpivotSecond
          have haFirstIdx :
              (first.rotate (first.idxOf pivot)).idxOf a <
                first.length := by
            rw [← List.length_rotate first (first.idxOf pivot)]
            exact List.idxOf_lt_length_of_mem haFirst'
          have haSecondIdx :
              (second.rotate (second.idxOf pivot + 1)).idxOf a <
                second.length := by
            rw [← List.length_rotate second (second.idxOf pivot + 1)]
            exact List.idxOf_lt_length_of_mem haSecond'
          have hpivotFirst' :
              pivot ∈ first.rotate (first.idxOf pivot) :=
            List.mem_rotate.mpr hpivotFirst
          have hpivotSecond' :
              pivot ∈ second.rotate (second.idxOf pivot + 1) :=
            List.mem_rotate.mpr hpivotSecond
          have hfirstNe :
              (first.rotate (first.idxOf pivot)).idxOf a ≠
                (first.rotate (first.idxOf pivot)).idxOf pivot := by
            intro h
            exact hab ((List.idxOf_inj haFirst').mp h)
          have hsecondNe :
              (second.rotate (second.idxOf pivot + 1)).idxOf a ≠
                (second.rotate (second.idxOf pivot + 1)).idxOf pivot := by
            intro h
            exact hab ((List.idxOf_inj haSecond').mp h)
          simp only [first', second']
          rw [hfirstPivot, hsecondPivot]
          constructor <;> intro
          · omega
          · omega
        · have hfirstOrder :=
            rotate_at_order first hfirst hpivotFirst haFirst hbFirst
              (Ne.symm hap) (Ne.symm hbp)
          have hsecondOrder :=
            rotate_after_order second hsecond hpivotSecond hbSecond haSecond
              (Ne.symm hbp) (Ne.symm hap)
          have hfirstIdx : first.idxOf a ≠ first.idxOf b := by
            intro h
            exact hab ((List.idxOf_inj haFirst).mp h)
          have hsecondSwap :=
            cyclicLT_swap
              (List.idxOf_lt_length_of_mem hpivotSecond)
              (List.idxOf_lt_length_of_mem haSecond)
              (List.idxOf_lt_length_of_mem hbSecond)
              (by
                intro h
                exact (Ne.symm hap) ((List.idxOf_inj hpivotSecond).mp h))
              (by
                intro h
                exact (Ne.symm hbp) ((List.idxOf_inj hpivotSecond).mp h))
              (by
                intro h
                exact hab ((List.idxOf_inj haSecond).mp h))
          simp only [first', second']
          rw [hfirstOrder, hsecondOrder]
          constructor
          · intro hcyclicFirst
            have hnoSecond :=
              hno pivot a b hpivotFirst hpivotSecond
                haFirst haSecond hbFirst hbSecond
                (Ne.symm hap) (Ne.symm hbp) hab hcyclicFirst
            by_contra hnotSecondSwap
            exact hnoSecond (hsecondSwap.mpr hnotSecondSwap)
          · intro hcyclicSecondSwap
            by_contra hnotFirst
            have hfirstSwap :=
              cyclicLT_swap
                (List.idxOf_lt_length_of_mem hpivotFirst)
                (List.idxOf_lt_length_of_mem haFirst)
                (List.idxOf_lt_length_of_mem hbFirst)
                (by
                  intro h
                  exact (Ne.symm hap) ((List.idxOf_inj hpivotFirst).mp h))
                (by
                  intro h
                  exact (Ne.symm hbp) ((List.idxOf_inj hpivotFirst).mp h))
                hfirstIdx
            have hcyclicFirstSwap :
                CyclicLT (first.idxOf pivot) (first.idxOf b) (first.idxOf a) := by
              by_contra hnotSwap
              exact hnotFirst (hfirstSwap.mpr hnotSwap)
            exact (hno pivot b a hpivotFirst hpivotSecond
              hbFirst hbSecond haFirst haSecond
              (Ne.symm hbp) (Ne.symm hap) (Ne.symm hab)
              hcyclicFirstSwap) hcyclicSecondSwap
  · refine ⟨first, second, ⟨0, by simp⟩, ⟨0, by simp⟩, ?_⟩
    intro a haFirst b _ _ haSecond _
    exact False.elim (hcommon ⟨a, haFirst, haSecond⟩)

end Kakeya.Cinematic.GraphLensBridge
