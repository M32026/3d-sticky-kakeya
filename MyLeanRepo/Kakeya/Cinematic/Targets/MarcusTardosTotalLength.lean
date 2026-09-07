import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Statements

/-!
# Marcus--Tardos varying-length corollary

This target formalizes the dyadic pruning argument from Theorem 1 to
Corollary 6 while receiving the equal-length theorem as an ordinary input.
-/

namespace MarcusTardos

private lemma posOf_filter_lt_iff
    {α : Type*} [DecidableEq α] (p : α → Bool) {a b : α} (hab : a ≠ b)
    (ha : p a = true) (hb : p b = true) (L : List α) :
    posOf a (L.filter p) < posOf b (L.filter p) ↔
      posOf a L < posOf b L := by
  induction L with
  | nil => simp [posOf]
  | cons x xs ih =>
      by_cases hpx : p x = true
      · rw [List.filter_cons_of_pos hpx]
        by_cases hxa : x = a
        · subst x
          simp [posOf, hab]
        · by_cases hxb : x = b
          · subst x
            simp [posOf]
          · simp [posOf, hxa, hxb, ih]
      · rw [List.filter_cons_of_neg hpx]
        have hxa : x ≠ a := by
          intro h
          subst x
          exact hpx ha
        have hxb : x ≠ b := by
          intro h
          subst x
          exact hpx hb
        simp [posOf, hxa, hxb, ih]

private lemma isIntersectionReverse_filter
    {α : Type*} [DecidableEq α] (p q : α → Bool) {A B : List α}
    (h : IsIntersectionReverse A B) :
    IsIntersectionReverse (A.filter p) (B.filter q) := by
  intro a ha b hb hab haB hbB
  have hpa : p a = true := (List.mem_filter.mp ha).2
  have hpb : p b = true := (List.mem_filter.mp hb).2
  have hqa : q a = true := (List.mem_filter.mp haB).2
  have hqb : q b = true := (List.mem_filter.mp hbB).2
  rw [posOf_filter_lt_iff p hab hpa hpb]
  rw [posOf_filter_lt_iff q hab.symm hqb hqa]
  exact h a (List.mem_of_mem_filter ha) b (List.mem_of_mem_filter hb) hab
    (List.mem_of_mem_filter haB) (List.mem_of_mem_filter hbB)

private lemma isRotation_filter
    {α : Type*} (p : α → Bool) {A B : List α} (h : IsRotation A B) :
    IsRotation (A.filter p) (B.filter p) := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨(A.take k |>.filter p).length, ?_⟩
  rw [List.filter_append]
  have hsplit : A.filter p = (A.take k).filter p ++ (A.drop k).filter p := by
    rw [← List.filter_append, List.take_append_drop]
  rw [hsplit]
  simp

private lemma isCyclicIntersectionReverse_filter
    {α : Type*} [DecidableEq α] (p q : α → Bool) {A B : List α}
    (h : IsCyclicIntersectionReverse A B) :
    IsCyclicIntersectionReverse (A.filter p) (B.filter q) := by
  obtain ⟨A', B', hA, hB, hrev⟩ := h
  exact ⟨A'.filter p, B'.filter q, isRotation_filter p hA,
    isRotation_filter q hB, isIntersectionReverse_filter p q hrev⟩

private def lengthKeys {m : ℕ} {α : Type*} (A : Fin m → List α) :
    Finset (Lex (OrderDual ℕ × Fin m)) :=
  Finset.univ.image fun i => toLex (OrderDual.toDual (A i).length, i)

private lemma lengthKeys_card {m : ℕ} {α : Type*} (A : Fin m → List α) :
    (lengthKeys A).card = m := by
  rw [lengthKeys, Finset.card_image_of_injective]
  · simp
  · intro i j h
    simpa using congrArg (fun x : Lex (OrderDual ℕ × Fin m) => (ofLex x).2) h

private def lengthKeysEquiv {m : ℕ} {α : Type*} (A : Fin m → List α) :
    (lengthKeys A : Type) ≃ Fin m where
  toFun x := (ofLex x.1).2
  invFun i := ⟨toLex (OrderDual.toDual (A i).length, i), by simp [lengthKeys]⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp x.2
    change toLex (OrderDual.toDual (A (ofLex x.1).2).length, (ofLex x.1).2) = x.1
    have hpair : (OrderDual.toDual (A i).length, i) = ofLex x.1 := by
      simpa using congrArg ofLex hi
    rw [← hpair]
    exact hi
  right_inv i := by simp

private def lengthRankEquiv {m : ℕ} {α : Type*} (A : Fin m → List α) : Fin m ≃ Fin m :=
  ((lengthKeys A).orderIsoOfFin (lengthKeys_card A)).toEquiv.trans (lengthKeysEquiv A)

private lemma lengthRankEquiv_apply_key {m : ℕ} {α : Type*} (A : Fin m → List α)
    (i : Fin m) :
    (((lengthKeys A).orderIsoOfFin (lengthKeys_card A)) i).1 =
      toLex (OrderDual.toDual (A (lengthRankEquiv A i)).length, lengthRankEquiv A i) := by
  let x := ((lengthKeys A).orderIsoOfFin (lengthKeys_card A)) i
  have hx := x.2
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hx
  have hrank : lengthRankEquiv A i = j := by
    change (ofLex x.1).2 = j
    rw [← hj]
    simp
  rw [hrank, ← hj]

private lemma lengthRankEquiv_antitone {m : ℕ} {α : Type*} (A : Fin m → List α) :
    Antitone fun i => (A (lengthRankEquiv A i)).length := by
  intro i j hij
  have hkey := ((lengthKeys A).orderIsoOfFin (lengthKeys_card A)).monotone hij
  change (((lengthKeys A).orderIsoOfFin (lengthKeys_card A)) i).1 ≤
    (((lengthKeys A).orderIsoOfFin (lengthKeys_card A)) j).1 at hkey
  rw [lengthRankEquiv_apply_key A i, lengthRankEquiv_apply_key A j] at hkey
  change toLex (OrderDual.toDual (A (lengthRankEquiv A i)).length, lengthRankEquiv A i) ≤
    toLex (OrderDual.toDual (A (lengthRankEquiv A j)).length, lengthRankEquiv A j) at hkey
  simpa using Prod.Lex.monotone_fst _ _ hkey

private lemma sqrt_four_pow (k : ℕ) :
    Real.sqrt (((4 : ℕ) ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by
  rw [Nat.cast_pow]
  norm_num only [Nat.cast_ofNat]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]
  rw [pow_mul, Real.sqrt_sq (by positivity)]

private lemma sum_pow_two_le (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1), (2 : ℝ) ^ k) ≤ 2 ^ (K + 1) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [show K.succ + 1 = (K + 1) + 1 by omega, Finset.sum_range_succ]
      rw [show (2 : ℝ) ^ (K + 1 + 1) = 2 * 2 ^ (K + 1) by ring]
      linarith

private lemma dyadic_sum_one_div_sqrt_le (m : ℕ) :
    (∑ q ∈ Finset.range m, (1 : ℝ) / Real.sqrt (q + 1 : ℕ)) ≤
      8 * Real.sqrt m := by
  by_cases hm : m = 0
  · subst m
    simp
  let K : ℕ := Nat.log 4 m
  let level : ℕ → ℕ := fun q => Nat.log 4 (q + 1)
  have hlevel (q : ℕ) (hq : q ∈ Finset.range m) : level q ∈ Finset.range (K + 1) := by
    rw [Finset.mem_range]
    apply Nat.lt_succ_of_le
    dsimp [level, K]
    apply Nat.log_monotone
    have hqm : q < m := Finset.mem_range.mp hq
    omega
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := Finset.range m) (t := Finset.range (K + 1)) (g := level) hlevel
    (fun q => (1 : ℝ) / Real.sqrt (q + 1 : ℕ))
  rw [← hfiber]
  calc
    (∑ k ∈ Finset.range (K + 1),
        ∑ q ∈ Finset.range m with level q = k,
          (1 : ℝ) / Real.sqrt (q + 1 : ℕ))
        ≤ ∑ k ∈ Finset.range (K + 1), (4 : ℝ) * 2 ^ k := by
          gcongr with k hk
          let bucket := {q ∈ Finset.range m | level q = k}
          have hbucket_card : bucket.card ≤ 4 ^ (k + 1) := by
            calc
              bucket.card ≤ (Finset.range (4 ^ (k + 1))).card := by
                apply Finset.card_le_card
                intro q hq
                rw [Finset.mem_filter] at hq
                rw [Finset.mem_range]
                have hlt : q + 1 < 4 ^ (Nat.log 4 (q + 1)).succ :=
                  Nat.lt_pow_succ_log_self (by norm_num) (q + 1)
                dsimp [level] at hq
                rw [hq.2] at hlt
                omega
              _ = 4 ^ (k + 1) := Finset.card_range _
          calc
            (∑ q ∈ Finset.range m with level q = k,
                (1 : ℝ) / Real.sqrt (q + 1 : ℕ))
                ≤ bucket.card * ((1 : ℝ) / 2 ^ k) := by
                  have hsum := Finset.sum_le_card_nsmul bucket
                    (fun q => (1 : ℝ) / Real.sqrt (q + 1 : ℕ))
                    ((1 : ℝ) / 2 ^ k) (by
                      intro q hq
                      rw [Finset.mem_filter] at hq
                      have hpow : 4 ^ k ≤ q + 1 := by
                        have := Nat.pow_log_le_self 4 (show q + 1 ≠ 0 by omega)
                        dsimp [level] at hq
                        rwa [hq.2] at this
                      have hsqrt : Real.sqrt (((4 : ℕ) ^ k : ℕ) : ℝ) ≤
                          Real.sqrt (q + 1 : ℕ) := by
                        apply Real.sqrt_le_sqrt
                        exact_mod_cast hpow
                      rw [sqrt_four_pow] at hsqrt
                      gcongr)
                  simpa [bucket, nsmul_eq_mul] using hsum
            _ ≤ ((4 : ℕ) ^ (k + 1) : ℕ) * ((1 : ℝ) / 2 ^ k) := by
                  gcongr
            _ = (4 : ℝ) * 2 ^ k := by
                  push_cast
                  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
                  field_simp
                  ring
    _ = 4 * ∑ k ∈ Finset.range (K + 1), (2 : ℝ) ^ k := by
          rw [Finset.mul_sum]
    _ ≤ 4 * 2 ^ (K + 1) := by gcongr; exact sum_pow_two_le K
    _ = 8 * 2 ^ K := by rw [pow_succ]; ring
    _ ≤ 8 * Real.sqrt m := by
          gcongr
          rw [← sqrt_four_pow K]
          apply Real.sqrt_le_sqrt
          exact_mod_cast Nat.pow_log_le_self 4 hm

theorem total_length_from_equal_length :
    TotalLengthFromEqualLengthStatement := by
  intro hEqual α inst
  obtain ⟨C, hC, hEqual⟩ := hEqual α
  refine ⟨8 * C, mul_pos (by norm_num) hC, ?_⟩
  intro m n alphabet halphabet A hNodup hmem hreverse
  by_cases hm : m = 0
  · subst m
    simp
  by_cases hn : n = 0
  · subst n
    have halphabet_empty : alphabet = ∅ := Finset.card_eq_zero.mp hn
    have hAempty : ∀ i, A i = [] := by
      intro i
      rw [List.eq_nil_iff_forall_not_mem]
      intro x hx
      have hxempty : x ∈ (∅ : Finset α) := by
        rw [← halphabet_empty]
        exact hmem i x hx
      simp at hxempty
    simp [hAempty, hn]
  let e : Fin m ≃ Fin m := lengthRankEquiv A
  let B : Fin m → List α := fun i => A (e i)
  have hB_antitone : Antitone fun i => (B i).length := by
    exact lengthRankEquiv_antitone A
  have hB_bound : ∀ q : Fin m,
      ((B q).length : ℝ) ≤
        C * (Real.sqrt n * Real.log (n + 1) +
          n / Real.sqrt (q.1 + 1 : ℕ)) := by
    intro q
    let k : ℕ := q.1 + 1
    have hk_le : k ≤ m := Nat.succ_le_iff.mpr q.2
    let embed : Fin k → Fin m := Fin.castLE hk_le
    let d : ℕ := (B q).length
    let Aq : Fin k → List α := fun r => (B (embed r)).take d
    have hd_le (r : Fin k) : d ≤ (B (embed r)).length := by
      apply hB_antitone
      apply Fin.le_iff_val_le_val.mpr
      dsimp [embed, k]
      omega
    have hAq_nodup : ∀ r, (Aq r).Nodup ∧ (Aq r).length = d := by
      intro r
      constructor
      · exact (hNodup (e (embed r))).take
      · change ((B (embed r)).take d).length = d
        rw [List.length_take, min_eq_left (hd_le r)]
    have hAq_mem : ∀ r, ∀ x ∈ Aq r, x ∈ alphabet := by
      intro r x hx
      exact hmem (e (embed r)) x (List.mem_of_mem_take hx)
    have hAq_reverse : ∀ r s, r ≠ s →
        IsCyclicIntersectionReverse (Aq r) (Aq s) := by
      intro r s hrs
      have hindex : e (embed r) ≠ e (embed s) := by
        intro h
        apply hrs
        apply Fin.castLE_injective
        exact e.injective h
      have hrev := hreverse (e (embed r)) (e (embed s)) hindex
      change IsCyclicIntersectionReverse ((B (embed r)).take d) ((B (embed s)).take d)
      rw [(hNodup (e (embed r))).take_eq_filter_mem,
        (hNodup (e (embed s))).take_eq_filter_mem]
      exact isCyclicIntersectionReverse_filter _ _ hrev
    have hd := hEqual k d n (Nat.succ_pos q.1) alphabet halphabet Aq
      hAq_nodup hAq_mem hAq_reverse
    simpa [k, d] using hd
  have hsum_reindex :
      (∑ i, (A i).length : ℕ) = ∑ i, (B i).length := by
    change (∑ i, (A i).length : ℕ) = ∑ i, (A (e i)).length
    exact (e.sum_comp fun i => (A i).length).symm
  have hsqrt_sum :
      (∑ q : Fin m, (1 : ℝ) / Real.sqrt (q.1 + 1 : ℕ)) ≤
        8 * Real.sqrt m := by
    rw [Fin.sum_univ_eq_sum_range
      (fun q : ℕ => (1 : ℝ) / Real.sqrt (q + 1 : ℕ)) m]
    exact dyadic_sum_one_div_sqrt_le m
  have hlog : 0 ≤ Real.log (n + 1) := by
    apply Real.log_nonneg
    norm_num
  have hbase : 0 ≤ Real.sqrt n * Real.log (n + 1) :=
    mul_nonneg (Real.sqrt_nonneg _) hlog
  rw [hsum_reindex]
  push_cast
  calc
    (∑ q, ((B q).length : ℝ))
        ≤ ∑ q : Fin m, C * (Real.sqrt n * Real.log (n + 1) +
            n / Real.sqrt (q.1 + 1 : ℕ)) := by
          gcongr with q
          exact hB_bound q
    _ = C * ((m : ℝ) * (Real.sqrt n * Real.log (n + 1)) +
          n * ∑ q : Fin m, (1 : ℝ) / Real.sqrt (q.1 + 1 : ℕ)) := by
        simp_rw [div_eq_mul_inv, mul_add]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [Fintype.card_fin]
        rw [← Finset.mul_sum]
        rw [← Finset.mul_sum]
        ring_nf
    _ ≤ C * ((m : ℝ) * (Real.sqrt n * Real.log (n + 1)) +
          n * (8 * Real.sqrt m)) := by
        gcongr
    _ ≤ (8 * C) * ((m : ℝ) * Real.sqrt n * Real.log (n + 1) +
          n * Real.sqrt m) := by
        have hmn : 0 ≤ (m : ℝ) * (Real.sqrt n * Real.log (n + 1)) := by positivity
        have hnroot : 0 ≤ (n : ℝ) * Real.sqrt m := by positivity
        nlinarith

end MarcusTardos
