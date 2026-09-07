module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Total slope condition

Given disjoint intervals covering all but `B*m` of `[0,m]`, prove:
`∑ (p.2 - p.1) * chordSlope(f,p.1,p.2) ≥ f m - 2*B*m`.

With the lower bound `f m ≥ t*m - ε*m`, this gives:
`∑ (p.2 - p.1) * chordSlope(f,p.1,p.2) ≥ (t - ε - 2*B)*m`.

Uses only 2-Lipschitz to bound the increase over uncovered gaps.

Whiteprint node: `total_slope`
-/

noncomputable section

open scoped BigOperators

variable {f : ℝ → ℝ} {m : ℝ}

/-- Core induction: for a sorted disjoint list of valid intervals within `[x,m]`,
the missing increase `f m - f x - ∑(f b_i - f a_i)` is at most
`2 * (missing length)`. -/
lemma total_slope_helper (f : ℝ → ℝ) (m : ℝ)
    (hlip : LipschitzOnWith 2 f (Set.Icc 0 m)) :
    ∀ (L : List (ℝ × ℝ)),
      List.Pairwise (fun p q : ℝ × ℝ => p.1 < q.1) L →
      (∀ p ∈ L, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ m) →
      (∀ p ∈ L, ∀ q ∈ L, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1) →
      ∀ (x : ℝ), 0 ≤ x → x ≤ m →
      (∀ p ∈ L, x ≤ p.1) →
      f m - f x ≤ (L.map (fun p => f p.2 - f p.1)).sum +
        2 * ((m - x) - (L.map (fun p => p.2 - p.1)).sum) := by
  intro L
  induction L with
  | nil =>
    intro _ _ _ x hx0 hxm _
    simp
    have hxin : x ∈ Set.Icc 0 m := ⟨hx0, hxm⟩
    have hmin : (m : ℝ) ∈ Set.Icc 0 m := ⟨by linarith, by linarith⟩
    have h' : dist (f m) (f x) ≤ 2 * dist m x :=
      hlip.dist_le_mul m hmin x hxin
    have h_abs : |f m - f x| ≤ 2 * |m - x| := by
      simpa [Real.dist_eq] using h'
    have h1 : f m - f x ≤ |f m - f x| := le_abs_self _
    have h2 : |m - x| = m - x := by
      rw [abs_of_nonneg] <;> linarith
    linarith
  | cons I L ih =>
    intro h_sorted h_bound h_disj x hx0 hxm h_ge
    have hI_bound : 0 ≤ I.1 ∧ I.1 < I.2 ∧ I.2 ≤ m := h_bound I (by simp)
    have hI1 : x ≤ I.1 := h_ge I (by simp)
    have hI2 : I.2 ≤ m := hI_bound.2.2
    have hI1_nonneg : 0 ≤ I.1 := hI_bound.1
    have h_decomp : (∀ (y : ℝ × ℝ), y ∈ L → I.1 < y.1) ∧
        List.Pairwise (fun p q : ℝ × ℝ => p.1 < q.1) L := by
      simpa [List.pairwise_cons] using h_sorted
    have h_pair : ∀ (y : ℝ × ℝ), y ∈ L → I.1 < y.1 := h_decomp.1
    have h_tail_sorted : List.Pairwise (fun p q : ℝ × ℝ => p.1 < q.1) L := h_decomp.2
    have h_tail_ge : ∀ p ∈ L, I.2 ≤ p.1 := by
      intro p hp
      have h_isp : I.1 < p.1 := h_pair p hp
      have h_ne : I ≠ p := by
        intro h_eq
        rw [h_eq] at h_isp <;> linarith
      have h := h_disj I (by simp) p (by simp [hp]) h_ne
      rcases h with (h | h)
      · exact h
      · have hpb : p.1 < p.2 := (h_bound p (by simp [hp])).2.1
        linarith
    have h_tail_bound : ∀ p ∈ L, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ m :=
      fun p hp => h_bound p (by simp [hp])
    have h_tail_disj : ∀ p ∈ L, ∀ q ∈ L, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1 :=
      fun p hp q hq => h_disj p (by simp [hp]) q (by simp [hq])
    have hI2_in : I.2 ∈ Set.Icc 0 m := ⟨by linarith, by linarith⟩
    have h_ih := ih h_tail_sorted h_tail_bound h_tail_disj I.2
      (by linarith) (by linarith) h_tail_ge
    have hI1_in : I.1 ∈ Set.Icc 0 m := ⟨hI1_nonneg, by linarith⟩
    have hx_in : x ∈ Set.Icc 0 m := ⟨hx0, hxm⟩
    have h1 : f I.1 - f x ≤ 2 * (I.1 - x) := by
      have h_lip' : dist (f I.1) (f x) ≤ 2 * dist I.1 x :=
        hlip.dist_le_mul I.1 hI1_in x hx_in
      have h_abs : |f I.1 - f x| ≤ 2 * |I.1 - x| := by
        simpa [Real.dist_eq] using h_lip'
      have h1 : f I.1 - f x ≤ |f I.1 - f x| := le_abs_self _
      have h2 : |I.1 - x| = I.1 - x := by
        rw [abs_of_nonneg] <;> linarith
      linarith
    calc f m - f x
      = (f I.1 - f x) + (f I.2 - f I.1) + (f m - f I.2) := by ring
    _ ≤ 2 * (I.1 - x) + (f I.2 - f I.1) +
          ((L.map (fun p => f p.2 - f p.1)).sum +
            2 * ((m - I.2) - (L.map (fun p => p.2 - p.1)).sum)) := by gcongr
    _ = ((I :: L).map (fun p => f p.2 - f p.1)).sum +
          2 * ((m - x) - ((I :: L).map (fun p => p.2 - p.1)).sum) := by
        simp [List.map_cons, List.sum_cons] <;> ring

/-- Total slope bound for a list of disjoint intervals.

If the total uncovered length is at most `B * m`, then
`∑ (length * chordSlope) ≥ f m - 2 * B * m`. -/
lemma total_slope_list (f : ℝ → ℝ) (m B : ℝ) (hm_pos : 0 < m)
    (hlip : LipschitzOnWith 2 f (Set.Icc 0 m))
    (hf0 : f 0 = 0)
    (L : List (ℝ × ℝ))
    (h_sorted : List.Pairwise (fun p q : ℝ × ℝ => p.1 < q.1) L)
    (h_bound : ∀ p ∈ L, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ m)
    (h_disj : ∀ p ∈ L, ∀ q ∈ L, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1)
    (h_coverage : m - (L.map (fun p => p.2 - p.1)).sum ≤ B * m) :
    (L.map (fun p => (p.2 - p.1) * chordSlope f p.1 p.2)).sum ≥
      f m - 2 * B * m := by
  have h_main := total_slope_helper f m hlip L h_sorted h_bound h_disj 0
    (by linarith) (by linarith) (fun p hp => (h_bound p hp).1)
  have h2 : f m - f 0 ≤ (L.map (fun p => f p.2 - f p.1)).sum +
        2 * (m - (L.map (fun p => p.2 - p.1)).sum) := by
    simpa using h_main
  have h3 : f m ≤ (L.map (fun p => f p.2 - f p.1)).sum + 2 * B * m := by
    rw [hf0] at h2
    linarith
  have h4 : ∀ (p : ℝ × ℝ), (p.2 - p.1) * chordSlope f p.1 p.2 = f p.2 - f p.1 := by
    intro p
    by_cases h : p.2 - p.1 = 0
    · have h5 : p.2 = p.1 := by linarith
      simp [h5, chordSlope] <;> ring
    · have hne : p.2 - p.1 ≠ 0 := h
      dsimp only [chordSlope]
      field_simp [hne] <;> ring
  have h_eq_map : L.map (fun p => (p.2 - p.1) * chordSlope f p.1 p.2) =
                   L.map (fun p => f p.2 - f p.1) := by
    congr with p
    exact h4 p
  rw [h_eq_map]
  linarith

/-- Total slope bound with the lower bound on `f m`.

If `f m ≥ t * m - ε * m` and uncovered length ≤ `B * m`, then
`∑ (length * chordSlope) ≥ (t - ε - 2 * B) * m`. -/
lemma total_slope_with_lower (f : ℝ → ℝ) (m t ε B : ℝ) (hm_pos : 0 < m)
    (hlip : LipschitzOnWith 2 f (Set.Icc 0 m))
    (hf0 : f 0 = 0)
    (h_lower : f m ≥ t * m - ε * m)
    (L : List (ℝ × ℝ))
    (h_sorted : List.Pairwise (fun p q : ℝ × ℝ => p.1 < q.1) L)
    (h_bound : ∀ p ∈ L, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ m)
    (h_disj : ∀ p ∈ L, ∀ q ∈ L, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1)
    (h_coverage : m - (L.map (fun p => p.2 - p.1)).sum ≤ B * m) :
    (L.map (fun p => (p.2 - p.1) * chordSlope f p.1 p.2)).sum ≥
      (t - ε - 2 * B) * m := by
  have h1 := total_slope_list f m B hm_pos hlip hf0 L h_sorted h_bound h_disj h_coverage
  linarith [h_lower]

end
