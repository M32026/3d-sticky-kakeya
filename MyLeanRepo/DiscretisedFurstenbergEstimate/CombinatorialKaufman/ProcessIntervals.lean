module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.MergingLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.IntervalUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section

set_option maxHeartbeats 500000

/-!
# ProcessIntervals induction

Core combinatorial induction for the Kaufman decomposition.
Given δ²-linear intervals from tube-null, process right-to-left.
Each output interval is either 2δ-linear with slope ≥ s, or 2δ-superlinear with slope = s.

Includes the ExtendMerge sub-lemma for chain merging.
-/

open CombinatorialKaufman.MergingLemmas
open CombinatorialKaufman
open List

namespace CombinatorialKaufman.ProcessIntervals

noncomputable section

/-! ## ExtendMerge -/

namespace ExtendMerge

lemma totalLength_nonneg {L : List (ℝ × ℝ)} (hLen : ∀ p ∈ L, p.1 < p.2) :
    0 ≤ totalLength L := by
  have h : ∀ x ∈ L.map (fun p : ℝ × ℝ => p.2 - p.1), 0 ≤ x := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨p, hp, rfl⟩
    have h' : p.1 < p.2 := hLen p hp
    linarith
  exact List.sum_nonneg h

lemma sum_between {L : List (ℝ × ℝ)} {c d : ℝ}
    (hcd : c ≤ d) (hSD : SortedDisjoint L)
    (hBound : ∀ p ∈ L, c ≤ p.1 ∧ p.2 ≤ d) :
    totalLength L ≤ d - c := by
  have h_main : ∀ (L' : List (ℝ × ℝ)), SortedDisjoint L' →
      ∀ (c' d' : ℝ), c' ≤ d' →
      (∀ p ∈ L', c' ≤ p.1 ∧ p.2 ≤ d') →
      totalLength L' ≤ d' - c' := by
    intro L'
    induction L' with
    | nil =>
        intro _ c' d' hcd' _
        simpa [totalLength] using sub_nonneg.mpr hcd'
    | cons I L'' ih =>
        intro hSD' c' d' hcd' hBound'
        have h1 : ∀ p ∈ L'', I.2 ≤ p.1 := by
          intro p hp
          have h : (I :: L'').Pairwise (fun I J => I.2 ≤ J.1) := hSD'.1
          exact (List.pairwise_cons.mp h).1 p hp
        have hL''_SD : SortedDisjoint L'' :=
          ⟨(List.pairwise_cons.mp hSD'.1).2, fun p hp => hSD'.2 p (by simp [hp])⟩
        have h2 := ih hL''_SD I.2 d' (by linarith [hBound' I (by simp)])
            (fun p hp => ⟨h1 p hp, (hBound' p (by simp [hp])).2⟩)
        have hI_len : I.1 < I.2 := hSD'.2 I (by simp)
        have h_goal : (I.2 - I.1) + totalLength L'' ≤ d' - c' := by
          calc (I.2 - I.1) + totalLength L''
            ≤ (I.2 - I.1) + (d' - I.2) := by gcongr
          _ = d' - I.1 := by ring
          _ ≤ d' - c' := by linarith [(hBound' I (by simp)).1]
        simpa [totalLength, List.map_cons, List.sum_cons] using h_goal
  exact h_main L hSD c d hcd hBound

lemma dropWhile_head_false {α : Type*} {p : α → Bool} {l : List α} {x : α} {xs : List α}
    (h : l.dropWhile p = x :: xs) : p x = false := by
  induction l with
  | nil => simp at h <;> contradiction
  | cons y ys ih =>
    by_cases hpy : p y
    · have h' : (y :: ys).dropWhile p = ys.dropWhile p := by
        simp [List.dropWhile, hpy]
      rw [h'] at h
      exact ih h
    · have hpy' : p y = false := by simpa using hpy
      have h' : (y :: ys).dropWhile p = y :: ys := by
        simp [List.dropWhile, hpy]
      rw [h'] at h
      injection h with h_y _
      exact h_y.symm ▸ hpy'

/-- Extend a pending superlinear interval [c,b] leftward through chains of
    straddling δ²-linear intervals. -/
lemma extendMerge_induction (f : ℝ → ℝ) (s m δ τ0 : ℝ)
    (hs : 0 < s) (hδ : 0 < δ) (hδ_le1 : δ ≤ 1)
    (hm_pos : 0 < m) (hτ0_pos : 0 < τ0) (hf_cont : Continuous f) :
  ∀ (n : ℕ) (R : ℝ),
    ∀ (c b : ℝ) (L : List (ℝ × ℝ)),
      L.length ≤ n →
      0 ≤ c ∧ c < b ∧ b ≤ m →
      c ≤ R → R ≤ b →
      chordSlope f c b = s →
      EpsilonSuperlinear f (2 * δ) c b →
      chordSlope f 0 c > s →
      SortedDisjoint L →
      (∀ p ∈ L, EpsilonLinear f (δ^2) p.1 p.2) →
      (∀ p ∈ L, p.2 - p.1 ≥ τ0 * m) →
      (∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ m) →
      (∀ p ∈ L, p.2 ≤ R) →
      ∃ (cstar : ℝ) (J_chain L_rem : List (ℝ × ℝ)),
        0 ≤ cstar ∧
        cstar ≤ c ∧
        chordSlope f cstar b = s ∧
        EpsilonSuperlinear f (2 * δ) cstar b ∧
        SortedDisjoint J_chain ∧
        (∀ p ∈ J_chain, EpsilonLinear f (2 * δ) p.1 p.2 ∧ s ≤ chordSlope f p.1 p.2) ∧
        (∀ p ∈ J_chain, 0 ≤ p.1 ∧ p.2 ≤ m) ∧
        (∀ p ∈ J_chain, δ * τ0 * m ≤ p.2 - p.1) ∧
        (∀ p ∈ J_chain, p.2 ≤ cstar) ∧
        (∀ p ∈ L_rem, ∀ q ∈ J_chain, p.2 ≤ q.1) ∧
        (∀ p ∈ L_rem, p.2 ≤ cstar) ∧
        L_rem.Sublist L ∧
        totalLength J_chain + (R - cstar) ≥ (1 - δ) * (totalLength L - totalLength L_rem) := by
  intro n
  induction n with
  | zero =>
      intro R c b L hlen hbound hR_ge_c hR_le_b h_slope h_super h_slope0c hSD hLin hLen hBound hL_R
      have hL_empty : L = [] := by
        have h : L.length = 0 := by omega
        exact eq_nil_iff_length_eq_zero.mpr h
      subst hL_empty
      exact ⟨c, [], [], by linarith [hbound.1], by linarith, h_slope, h_super,
        by simp [SortedDisjoint], by simp, by simp, by simp, by simp, by simp, by simp, by simp,
        by simp [totalLength] <;> linarith⟩
  | succ n ih =>
      intro R c b L hlen hbound hR_ge_c hR_le_b h_slope h_super h_slope0c hSD hLin hLen hBound hL_R
      by_cases h_empty : L = []
      · subst h_empty
        exact ⟨c, [], [], by linarith [hbound.1], by linarith, h_slope, h_super,
          by simp [SortedDisjoint], by simp, by simp, by simp, by simp, by simp, by simp, by simp,
          by simp [totalLength] <;> linarith⟩
      · let p : ℝ × ℝ → Bool := fun x => decide (x.2 ≤ c)
        let left := L.takeWhile p
        let rest := L.dropWhile p
        have h_split : L = left ++ rest := by
          have h : left ++ rest = L := by exact takeWhile_append_dropWhile
          exact h.symm
        have h_left_le_c : ∀ x ∈ left, x.2 ≤ c := by
          intro x hx
          have h₁ : p x = true := List.mem_takeWhile_imp hx
          exact of_decide_eq_true h₁
        have h_left_sublist : left.Sublist L := by exact takeWhile_sublist p
        have h_left_SD : SortedDisjoint left :=
          ⟨hSD.1.sublist h_left_sublist, fun I hI => hSD.2 I (h_left_sublist.subset hI)⟩
        by_cases h_rest_empty : rest = []
        · have h3 : totalLength L = totalLength left := by
            rw [h_split, h_rest_empty] <;> simp [totalLength]
          exact ⟨c, [], left, by linarith [hbound.1], by linarith, h_slope, h_super,
            by simp [SortedDisjoint], by simp, by simp, by simp, by simp, by simp, h_left_le_c, h_left_sublist,
            by rw [h3]; simp [totalLength] <;> linarith⟩
        · have h_rest_cons : ∃ (K : ℝ × ℝ) (rest_tail : List (ℝ × ℝ)), rest = K :: rest_tail := by
            exact ne_nil_iff_exists_cons.mp h_rest_empty
          rcases h_rest_cons with ⟨K, rest_tail, h_rest_eq⟩
          have hK_in_rest : K ∈ rest := by rw [h_rest_eq] <;> simp
          have hK_in_L : K ∈ L := by rw [h_split] <;> simp [hK_in_rest]
          have h_dropWhile_eq : L.dropWhile p = K :: rest_tail := by
            have h1 : rest = L.dropWhile p := by rfl
            rw [←h1]; exact h_rest_eq
          have h_false : p K = false := dropWhile_head_false h_dropWhile_eq
          have hK2_gt_c : K.2 > c := by
            have h : ¬(K.2 ≤ c) := by
              intro hle; have hpk : p K = true := by simp [p, hle]
              rw [hpk] at h_false <;> contradiction
            exact lt_of_not_ge h
          have hK_len_pos : 0 < K.2 - K.1 := by
            have h : K.2 - K.1 ≥ τ0 * m := hLen K hK_in_L
            have h' : 0 < τ0 * m := by positivity
            linarith
          have hK1_lt_K2 : K.1 < K.2 := by linarith
          have h_left2_le_K1 : ∀ x ∈ left, x.2 ≤ K.1 := by
            intro x hx
            rw [h_split] at hSD
            have h_cross : ∀ (a : ℝ × ℝ), a ∈ left → ∀ (b : ℝ × ℝ), b ∈ rest → (fun I J => I.2 ≤ J.1) a b :=
              (List.pairwise_append.mp hSD.1).2.2
            exact h_cross x hx K hK_in_rest
          have h_rest_sublist : rest.Sublist L := List.dropWhile_sublist p
          have h_rest_SD : SortedDisjoint rest :=
            ⟨hSD.1.sublist h_rest_sublist, fun I hI => hSD.2 I (h_rest_sublist.subset hI)⟩
          have h_rest_K2_le : ∀ x ∈ rest_tail, K.2 ≤ x.1 := by
            have h : (K :: rest_tail).Pairwise (fun I J => I.2 ≤ J.1) := by
              rw [←h_rest_eq]; exact h_rest_SD.1
            exact (List.pairwise_cons.mp h).1
          have hK1_le_all_rest : ∀ x ∈ rest, K.1 ≤ x.1 := by
            rw [h_rest_eq]
            intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with (rfl | hx)
            · linarith
            · have h : K.2 ≤ x.1 := h_rest_K2_le x hx
              linarith [hK1_lt_K2]
          have h_rest_bound : ∀ x ∈ rest, K.1 ≤ x.1 ∧ x.2 ≤ R := by
            intro x hx
            have hx_in_L : x ∈ L := by rw [h_split] <;> simp [hx]
            exact ⟨hK1_le_all_rest x hx, hL_R x hx_in_L⟩
          have h_rest_len : ∀ x ∈ rest, x.1 < x.2 := by
            intro x hx
            have hx_in_L : x ∈ L := by rw [h_split] <;> simp [hx]
            have h : x.2 - x.1 ≥ τ0 * m := hLen x hx_in_L
            have h' : 0 < τ0 * m := by positivity
            linarith
          have h_sum_rest : totalLength rest ≤ R - K.1 :=
            sum_between (by linarith [hL_R K hK_in_L, hK1_lt_K2]) h_rest_SD h_rest_bound
          have h_tl_rest_nonneg : 0 ≤ totalLength rest := totalLength_nonneg h_rest_len
          by_cases h_gap : K.1 > c
          · have h5 : (1 - δ) * totalLength rest ≤ totalLength rest := by
              have h6 : 0 ≤ totalLength rest := h_tl_rest_nonneg
              have h7 : 0 ≤ 1 - δ := by linarith
              nlinarith
            have h8 : totalLength rest ≤ R - c := by
              have h9 : totalLength rest ≤ R - K.1 := h_sum_rest
              have h10 : R - K.1 ≤ R - c := by linarith
              linarith
            have h3 : totalLength L = totalLength left + totalLength rest := by
              rw [h_split]; simp [totalLength]
            exact ⟨c, [], left, by linarith [hbound.1], by linarith, h_slope, h_super,
              by simp [SortedDisjoint], by simp, by simp, by simp, by simp, by simp, h_left_le_c, h_left_sublist,
              by rw [h3]; simpa [totalLength] using h5.trans h8⟩
          · have hK1_le_c : K.1 ≤ c := by linarith
            have hK_lin : EpsilonLinear f (δ^2) K.1 K.2 := hLin K hK_in_L
            by_cases h_small : c - K.1 ≤ δ * (K.2 - K.1)
            · have h4 : (1 - δ) * totalLength rest ≤ R - c := by
                have h5 : totalLength rest ≤ R - K.1 := h_sum_rest
                have h6 : c - K.1 ≤ δ * (K.2 - K.1) := h_small
                have h7 : K.2 - K.1 ≤ R - K.1 := by linarith [hL_R K hK_in_L]
                have h8 : c - K.1 ≤ δ * (R - K.1) := by
                  calc c - K.1 ≤ δ * (K.2 - K.1) := h6
                    _ ≤ δ * (R - K.1) := by gcongr
                have h9 : (1 - δ) * (R - K.1) ≤ R - c := by
                  have h10 : (1 - δ) * (R - K.1) = (R - K.1) - δ * (R - K.1) := by ring
                  rw [h10]; linarith
                calc (1 - δ) * totalLength rest
                  ≤ (1 - δ) * (R - K.1) := by gcongr
                _ ≤ R - c := h9
              have h3 : totalLength L = totalLength left + totalLength rest := by
                rw [h_split]; simp [totalLength]
              exact ⟨c, [], left, by linarith [hbound.1], by linarith, h_slope, h_super,
                by simp [SortedDisjoint], by simp, by simp, by simp, by simp, by simp, h_left_le_c, h_left_sublist,
                by rw [h3]; simpa [totalLength] using h4⟩
            · have h_large : c - K.1 > δ * (K.2 - K.1) := by linarith
              have hK1_lt_c : K.1 < c := by
                have h_pos : 0 < δ * (K.2 - K.1) := by positivity
                linarith
              have h_trunc_lin_raw : EpsilonLinear f (2 * δ^2 / δ) K.1 c :=
                truncated_epsilonLinear f (by positivity) hδ hK1_lt_c hK2_gt_c hK_lin h_large
              have h_eq : (2 * δ^2 / δ) = (2 * δ) := by
                field_simp [hδ.ne'] <;> ring
              have h_trunc_lin : EpsilonLinear f (2 * δ) K.1 c := by
                rw [h_eq] at h_trunc_lin_raw; exact h_trunc_lin_raw
              by_cases h_high : chordSlope f K.1 c ≥ s
              · have hc_le_m : c ≤ m := by linarith [hbound.2.2]
                have hK1_ge0 : 0 ≤ K.1 := (hBound K hK_in_L).1
                have h_min_len : δ * τ0 * m ≤ c - K.1 := by
                  have h1 : c - K.1 > δ * (K.2 - K.1) := h_large
                  have h2 : K.2 - K.1 ≥ τ0 * m := hLen K hK_in_L
                  have h3 : δ * (K.2 - K.1) ≥ δ * (τ0 * m) := by gcongr
                  have h4 : δ * (τ0 * m) = δ * τ0 * m := by ring
                  linarith
                have h4_len : totalLength [(K.1, c)] + (R - c) ≥ (1 - δ) * totalLength rest := by
                  have h5 : totalLength [(K.1, c)] = c - K.1 := by
                    simp [totalLength] <;> ring
                  rw [h5]
                  have h6 : (c - K.1) + (R - c) = R - K.1 := by ring
                  rw [h6]
                  have h7 : 0 ≤ 1 - δ := by linarith
                  have h8 : (1 - δ) * totalLength rest ≤ totalLength rest := by
                    have h9 : 0 ≤ totalLength rest := h_tl_rest_nonneg
                    nlinarith
                  linarith [h_sum_rest]
                have h3 : totalLength L = totalLength left + totalLength rest := by
                  rw [h_split]; simp [totalLength]
                have h_final : totalLength [(K.1, c)] + (R - c) ≥ (1 - δ) * (totalLength L - totalLength left) := by
                  rw [h3]
                  have h10 : totalLength left + totalLength rest - totalLength left = totalLength rest := by ring
                  rw [h10]
                  exact h4_len
                have hJ_SD : SortedDisjoint [(K.1, c)] := by
                  simp [SortedDisjoint, hK1_lt_c]
                have h_cross : ∀ p ∈ left, ∀ q ∈ [(K.1, c)], p.2 ≤ q.1 := by
                  intro p hp q hq
                  simp only [List.mem_singleton] at hq
                  rw [hq]
                  exact h_left2_le_K1 p hp
                exact ⟨c, [(K.1, c)], left, by linarith [hbound.1], by linarith, h_slope, h_super,
                  hJ_SD,
                  (by intro p hp; simp only [List.mem_singleton] at hp; rw [hp]; exact ⟨h_trunc_lin, h_high⟩),
                  (by intro p hp; simp only [List.mem_singleton] at hp; rw [hp]; exact ⟨hK1_ge0, hc_le_m⟩),
                  (by intro p hp; simp only [List.mem_singleton] at hp; rw [hp]; exact h_min_len),
                  (by simp), h_cross, h_left_le_c, h_left_sublist, h_final⟩
              · have h_low : chordSlope f K.1 c < s := by linarith
                have hK1_pos : 0 < K.1 := by
                  by_contra h
                  have h' : K.1 ≤ 0 := by linarith
                  have h'' : K.1 = 0 := by linarith [(hBound K hK_in_L).1]
                  rw [h''] at h_low; linarith
                rcases largest_chordSlope_eq f hf_cont hK1_pos hK1_lt_c h_slope0c h_low
                  with ⟨c', hc'_ge0, hc'_leK1, h_slope_c', h_mon⟩
                have hc'_lt_K1 : c' < K.1 := by
                  have h_ne : c' ≠ K.1 := by
                    intro h_eq; rw [h_eq] at h_slope_c'; linarith
                  exact lt_of_le_of_ne hc'_leK1 h_ne
                have hc'_pos : 0 < c' := by
                  by_contra h
                  have h' : c' = 0 := by linarith
                  rw [h'] at h_slope_c'; linarith
                have hc'_lt_c : c' < c := by linarith [hc'_lt_K1, hK1_lt_c]
                have h_super_c' : EpsilonSuperlinear f (2 * δ) c' c :=
                  merged_epsilonSuperlinear f (by positivity) hc'_lt_K1 hK1_lt_c
                    h_slope_c' h_low h_trunc_lin h_mon
                have h_merged_raw : EpsilonSuperlinear f (max (2 * δ) (2 * δ)) c' b ∧ chordSlope f c' b = s :=
                  merge_adjacent_epsilonSuperlinear f hc'_lt_c hbound.2.1 h_super_c' h_super
                    h_slope_c' h_slope (by positivity) (by positivity)
                have h_max : max (2 * δ) (2 * δ) = (2 * δ) := by simp
                have h_merged : EpsilonSuperlinear f (2 * δ) c' b ∧ chordSlope f c' b = s := by
                  rw [h_max] at h_merged_raw; exact h_merged_raw
                have h_slope0_c' : chordSlope f 0 c' > s :=
                  chordSlope0_gt_s_of_middle f hc'_pos hc'_lt_c h_slope0c h_slope_c'
                have h_left_len : left.length ≤ n := by
                  have h1 : left.length ≤ L.length := by exact Sublist.length_le h_left_sublist
                  have h2 : L.length = left.length + rest.length := by
                    rw [h_split] <;> simp
                  have h3 : 0 < rest.length := by
                    exact List.length_pos_iff_ne_nil.mpr h_rest_empty
                  omega
                rcases ih K.1 c' b left h_left_len ⟨hc'_ge0, by linarith, hbound.2.2⟩
                  (by linarith [hc'_leK1]) (by linarith [hK1_lt_c, hbound.2.1])
                  h_merged.2 h_merged.1 h_slope0_c'
                  h_left_SD
                  (fun x hx => hLin x (by rw [h_split] <;> simp [hx]))
                  (fun x hx => hLen x (by rw [h_split] <;> simp [hx]))
                  (fun x hx => hBound x (by rw [h_split] <;> simp [hx]))
                  h_left2_le_K1
                  with ⟨cstar, J_chain, L_rem, hcstar_nonneg, hcstar_le_c', h_slope_cstarb, h_super_cstarb,
                    hJ_SD, hJ_good, hJ_bound, hJ_min, hJ_right, h_cross, hLrem_right, hLrem_sublist, h_length⟩
                have h_cstar_le_c : cstar ≤ c := by linarith [hcstar_le_c', hc'_lt_c]
                have h_final_sublist : L_rem.Sublist L :=
                  List.Sublist.trans hLrem_sublist h_left_sublist
                have h3 : totalLength L = totalLength left + totalLength rest := by
                  rw [h_split]; simp [totalLength]
                have h4 : totalLength J_chain + (R - cstar) ≥ (1 - δ) * (totalLength L - totalLength L_rem) := by
                  have h5 : totalLength J_chain + (K.1 - cstar) ≥ (1 - δ) * (totalLength left - totalLength L_rem) := h_length
                  have h6 : totalLength rest ≤ R - K.1 := h_sum_rest
                  have h7 : 0 ≤ 1 - δ := by linarith
                  have h8 : 0 ≤ totalLength rest := h_tl_rest_nonneg
                  have h9 : (1 - δ) * totalLength rest ≤ totalLength rest := by nlinarith
                  calc totalLength J_chain + (R - cstar)
                    = totalLength J_chain + (K.1 - cstar) + (R - K.1) := by ring
                  _ ≥ (1 - δ) * (totalLength left - totalLength L_rem) + (R - K.1) := by gcongr
                  _ ≥ (1 - δ) * (totalLength left - totalLength L_rem) + totalLength rest := by gcongr
                  _ ≥ (1 - δ) * (totalLength left - totalLength L_rem) + (1 - δ) * totalLength rest := by gcongr
                  _ = (1 - δ) * (totalLength L - totalLength L_rem) := by
                    rw [h3] <;> ring
                exact ⟨cstar, J_chain, L_rem, hcstar_nonneg, h_cstar_le_c, h_slope_cstarb, h_super_cstarb,
                  hJ_SD, hJ_good, hJ_bound, hJ_min, hJ_right, h_cross, hLrem_right, h_final_sublist, h4⟩

end ExtendMerge

/-! ## ProcessIntervals -/

open ExtendMerge

/-- Convert SortedByLeft + PairwiseInteriorDisjointList to SortedDisjoint. -/
lemma sortedDisjoint_of_byLeft_disjoint {L : List (ℝ × ℝ)}
    (h_sort : SortedByLeft L)
    (h_disj : PairwiseInteriorDisjointList L)
    (h_len : ∀ p ∈ L, p.1 < p.2) :
    SortedDisjoint L := by
  have h_main : ∀ (L : List (ℝ × ℝ)), SortedByLeft L → PairwiseInteriorDisjointList L →
      (∀ p ∈ L, p.1 < p.2) → SortedDisjoint L := by
    intro L
    induction L with
    | nil =>
        intro _ _ _
        exact ⟨by simp, by simp⟩
    | cons I L ih =>
        intro h_sort h_disj h_len
        have h1 : ∀ J ∈ L, I.2 ≤ J.1 := by
          intro J hJ
          have h_I1_lt_J1 : I.1 < J.1 := (List.pairwise_cons.mp h_sort).1 J hJ
          have h_disj' : Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2) :=
            (List.pairwise_cons.mp h_disj).1 J hJ
          by_contra h
          have h_I2_gt_J1 : I.2 > J.1 := by linarith
          have h_J2_gt_J1 : J.1 < J.2 := h_len J (by simp [hJ])
          set x : ℝ := (J.1 + min I.2 J.2) / 2 with hx_def
          have h_J1_lt_min : J.1 < min I.2 J.2 := by
            apply lt_min <;> linarith
          have h_J1_lt_x : J.1 < x := by
            rw [hx_def]; linarith
          have h_x_lt_I2 : x < I.2 := by
            rw [hx_def]; have h : min I.2 J.2 ≤ I.2 := min_le_left _ _; linarith
          have h_x_lt_J2 : x < J.2 := by
            rw [hx_def]; have h : min I.2 J.2 ≤ J.2 := min_le_right _ _; linarith
          have h_I1_lt_x : I.1 < x := by linarith
          have h_x_in_Ioo : x ∈ Set.Ioo I.1 I.2 := ⟨h_I1_lt_x, h_x_lt_I2⟩
          have h_x_in_Joo : x ∈ Set.Ioo J.1 J.2 := ⟨h_J1_lt_x, h_x_lt_J2⟩
          exact Set.not_disjoint_iff.mpr ⟨x, h_x_in_Ioo, h_x_in_Joo⟩ h_disj'
        have hL_sort : SortedByLeft L := (List.pairwise_cons.mp h_sort).2
        have hL_disj : PairwiseInteriorDisjointList L := (List.pairwise_cons.mp h_disj).2
        have hL_len : ∀ p ∈ L, p.1 < p.2 := fun p hp => h_len p (by simp [hp])
        have hL_SD : SortedDisjoint L := ih hL_sort hL_disj hL_len
        exact ⟨List.pairwise_cons.mpr ⟨h1, hL_SD.1⟩, fun p hp => h_len p (by simp [hp])⟩
  exact h_main L h_sort h_disj h_len

/-- Convert SortedDisjoint to SortedByLeft + PairwiseInteriorDisjointList. -/
lemma byLeft_disjoint_of_sortedDisjoint {L : List (ℝ × ℝ)} (hSD : SortedDisjoint L) :
    SortedByLeft L ∧ PairwiseInteriorDisjointList L := by
  have h_main : ∀ (L : List (ℝ × ℝ)), SortedDisjoint L →
      SortedByLeft L ∧ PairwiseInteriorDisjointList L := by
    intro L
    induction L with
    | nil =>
        intro _
        exact ⟨by simp [SortedByLeft], by simp [PairwiseInteriorDisjointList]⟩
    | cons I L ih =>
        intro hSD
        have h1 : ∀ J ∈ L, I.2 ≤ J.1 := (List.pairwise_cons.mp hSD.1).1
        have hL_SD : SortedDisjoint L :=
          ⟨(List.pairwise_cons.mp hSD.1).2, fun p hp => hSD.2 p (by simp [hp])⟩
        have h_rest := ih hL_SD
        have h_sort : SortedByLeft (I :: L) := by
          have h2 : ∀ J ∈ L, I.1 < J.1 := by
            intro J hJ
            have h3 : I.1 < I.2 := hSD.2 I (by simp)
            have h4 : I.2 ≤ J.1 := h1 J hJ
            linarith
          exact List.pairwise_cons.mpr ⟨h2, h_rest.1⟩
        have h_disj : PairwiseInteriorDisjointList (I :: L) := by
          have h2 : ∀ J ∈ L, Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2) := by
            intro J hJ
            have h3 : I.2 ≤ J.1 := h1 J hJ
            exact Set.disjoint_left.mpr fun x hx1 hx2 => by
              have h4 : x < I.2 := hx1.2
              have h5 : J.1 < x := hx2.1
              linarith
          exact List.pairwise_cons.mpr ⟨h2, h_rest.2⟩
        exact ⟨h_sort, h_disj⟩
  exact h_main L hSD

lemma slope_le_two
    (f : ℝ → ℝ) (a b m : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hbm : b ≤ m)
    (hLip : LipschitzOnWith 2 f (Set.Icc 0 m)) :
    chordSlope f a b ≤ 2 := by
  have ha' : a ∈ Set.Icc (0 : ℝ) m := ⟨ha, by linarith⟩
  have hb' : b ∈ Set.Icc (0 : ℝ) m := ⟨by linarith, hbm⟩
  have h_edist : edist (f a) (f b) ≤ (2 : NNReal) * edist a b := hLip ha' hb'
  have h_main : dist (f a) (f b) ≤ 2 * dist a b := by
    have h1 : edist (f a) (f b) = ENNReal.ofReal (dist (f a) (f b)) := by
      simp [edist_dist]
    have h2 : (2 : NNReal) * edist a b = ENNReal.ofReal (2 * dist a b) := by
      simp [edist_dist, ENNReal.ofReal_mul] <;> norm_cast
    rw [h1, h2] at h_edist
    have h4 : 0 ≤ 2 * dist a b := by positivity
    have h5 : ENNReal.ofReal (dist (f a) (f b)) ≤ ENNReal.ofReal (2 * dist a b) := h_edist
    have h6 : dist (f a) (f b) ≤ 2 * dist a b := by exact (ENNReal.ofReal_le_ofReal_iff h4).mp h_edist
    exact h6
  have h3 : |f b - f a| ≤ 2 * (b - a) := by
    have h4 : dist (f a) (f b) = |f a - f b| := by simp [Real.dist_eq]
    have h5 : dist a b = |a - b| := by simp [Real.dist_eq]
    rw [h4, h5] at h_main
    have h6 : |a - b| = b - a := by rw [abs_of_neg] <;> linarith
    rw [h6] at h_main
    have h7 : |f a - f b| = |f b - f a| := by exact abs_sub_comm (f a) (f b)
    rw [h7] at h_main
    exact h_main
  have h4 : f b - f a ≤ 2 * (b - a) := by
    have h5 : |f b - f a| ≤ 2 * (b - a) := h3
    exact (abs_le.mp h5).2
  have h7 : 0 < b - a := by linarith
  have h8 : (f b - f a) / (b - a) ≤ 2 := by
    calc (f b - f a) / (b - a)
      ≤ (2 * (b - a)) / (b - a) := by gcongr
    _ = 2 := by field_simp [h7.ne'] <;> ring
  simpa [chordSlope] using h8

lemma totalLength_le_bound {L : List (ℝ × ℝ)} {B : ℝ}
    (hB_nonneg : 0 ≤ B)
    (hL_sort : SortedDisjoint L)
    (hL_bound : ∀ I ∈ L, 0 ≤ I.1 ∧ I.2 ≤ B) :
    totalLength L ≤ B := by
  have h_main : ∀ (L : List (ℝ × ℝ)) (x : ℝ), x ≤ B →
      SortedDisjoint L →
      (∀ I ∈ L, x ≤ I.1 ∧ I.2 ≤ B) →
      totalLength L ≤ B - x := by
    intro L
    induction L with
    | nil =>
        intro x hxB _ _
        simp [totalLength] <;> linarith
    | cons I L ih =>
        intro x hxB h_sort h_bound
        have hI1 : x ≤ I.1 := (h_bound I (by simp)).1
        have hI2 : I.2 ≤ B := (h_bound I (by simp)).2
        have h_pair : ∀ (K : ℝ × ℝ), K ∈ L → I.2 ≤ K.1 :=
          (List.pairwise_cons.mp h_sort.1).1
        have hL_sort' : SortedDisjoint L :=
          ⟨(List.pairwise_cons.mp h_sort.1).2, fun K hK => h_sort.2 K (by simp [hK])⟩
        have hL_bound' : ∀ K ∈ L, I.2 ≤ K.1 ∧ K.2 ≤ B :=
          fun K hK => ⟨h_pair K hK, (h_bound K (by simp [hK])).2⟩
        have h_ih := ih I.2 (by linarith) hL_sort' hL_bound'
        simp [totalLength, List.map_cons, List.sum_cons] at * <;> linarith
  have h := h_main L 0 hB_nonneg hL_sort (fun I hI => ⟨(hL_bound I hI).1, (hL_bound I hI).2⟩)
  simpa using h

/-- Main induction: process a list of δ²-linear intervals. -/
lemma process_intervals
    (f : ℝ → ℝ) (s t δ ε' τ0 m : ℝ)
    (hs : 0 < s) (hst : s < t) (ht : t ≤ 2)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hε'_pos : 0 < ε') (hτ0_pos : 0 < τ0)
    (hm : 0 ≤ m)
    (h_cont : Continuous f)
    (hLip : LipschitzOnWith 2 f (Set.Icc 0 m))
    (h_f0 : f 0 = 0)
    (h_lower : ∀ x ∈ Set.Icc 0 m, t * x - ε' * m ≤ f x) :
    ∀ (B : ℝ), B ≤ m →
    ∀ (L : List (ℝ × ℝ)),
      SortedDisjoint L →
      AllEpsilonLinear f (δ ^ 2) L →
      (∀ I ∈ L, 0 ≤ I.1 ∧ I.2 ≤ B) →
      (∀ I ∈ L, τ0 * m ≤ I.2 - I.1) →
      ∃ (J : List (ℝ × ℝ)),
        SortedDisjoint J ∧
        GoodIntervals f s δ J ∧
        (∀ I ∈ J, 0 ≤ I.1 ∧ I.2 ≤ B) ∧
        (∀ I ∈ J, δ * τ0 * m ≤ I.2 - I.1) ∧
        totalLength J ≥ (1 - δ) * totalLength L - ε' * m / (t - s) := by
  have h_main : ∀ (n : ℕ),
      (∀ (B : ℝ), B ≤ m → ∀ (L : List (ℝ × ℝ)), L.length = n →
        SortedDisjoint L →
        AllEpsilonLinear f (δ ^ 2) L →
        (∀ I ∈ L, 0 ≤ I.1 ∧ I.2 ≤ B) →
        (∀ I ∈ L, τ0 * m ≤ I.2 - I.1) →
        ∃ (J : List (ℝ × ℝ)),
          SortedDisjoint J ∧
          GoodIntervals f s δ J ∧
          (∀ I ∈ J, 0 ≤ I.1 ∧ I.2 ≤ B) ∧
          (∀ I ∈ J, δ * τ0 * m ≤ I.2 - I.1) ∧
          totalLength J ≥ (1 - δ) * totalLength L - ε' * m / (t - s)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B hB L hL_len hL_sort hL_lin hL_bound hL_min
      by_cases h_empty : L = []
      · subst h_empty
        have h_pos : 0 ≤ ε' * m / (t - s) := by positivity
        exact ⟨[], by simp [SortedDisjoint, GoodIntervals], by simp [GoodIntervals], by simp, by simp,
          by simp [totalLength] <;> linarith⟩
      · have h_ne : L ≠ [] := h_empty
        let I := L.getLast h_ne
        let L' := L.dropLast
        have hL'_sublist : L'.Sublist L := dropLast_sublist L
        have h_len : L'.length < L.length := by
          have h : L = L' ++ [I] := (List.dropLast_append_getLast h_ne).symm
          rw [h]; simp [L', h_ne] <;> omega
        have hL'_len : L'.length < n := by rw [hL_len] at h_len; exact h_len
        have hL'_sort : SortedDisjoint L' :=
          ⟨hL_sort.1.sublist hL'_sublist, fun I hI => hL_sort.2 I (hL'_sublist.subset hI)⟩
        have hL'_lin : AllEpsilonLinear f (δ ^ 2) L' :=
          fun K hK => hL_lin K (hL'_sublist.subset hK)
        have hL'_bound_B : ∀ K ∈ L', 0 ≤ K.1 ∧ K.2 ≤ B :=
          fun K hK => hL_bound K (hL'_sublist.subset hK)
        have hL'_min : ∀ K ∈ L', τ0 * m ≤ K.2 - K.1 :=
          fun K hK => hL_min K (hL'_sublist.subset hK)
        have hI_in : I ∈ L := getLast_mem h_ne
        have hI1 : I.1 < I.2 := hL_sort.2 I hI_in
        have hI2 : 0 ≤ I.1 := (hL_bound I hI_in).1
        have hI3 : I.2 ≤ B := (hL_bound I hI_in).2
        have hI3m : I.2 ≤ m := by linarith
        have hI4 : τ0 * m ≤ I.2 - I.1 := hL_min I hI_in
        have hI_lin : EpsilonLinear f (δ ^ 2) I.1 I.2 := hL_lin I hI_in
        have hI_lin_2δ : EpsilonLinear f (2 * δ) I.1 I.2 := by
          intro x hx
          have h9 : |f x - chordValue f I.1 I.2 x| ≤ δ ^ 2 * (I.2 - I.1) := hI_lin x hx
          have h10 : δ ^ 2 * (I.2 - I.1) ≤ 2 * δ * (I.2 - I.1) := by
            have h11 : δ ^ 2 ≤ 2 * δ := by nlinarith [hδ_lt_one]
            have h13 : 0 ≤ I.2 - I.1 := by linarith
            nlinarith
          exact le_trans h9 h10
        have h_eq : L = L' ++ [I] := (List.dropLast_append_getLast h_ne).symm
        have hL'_right : ∀ K ∈ L', K.2 ≤ I.1 := by
          rw [h_eq] at hL_sort
          have h := hL_sort.1
          have h' := (List.pairwise_append.mp h).2.2
          simpa [mem_singleton] using h'
        have hL'_bound_m : ∀ K ∈ L', 0 ≤ K.1 ∧ K.2 ≤ m :=
          fun K hK => let h := hL'_bound_B K hK; ⟨h.1, by linarith⟩
        have h_ts_pos : 0 < t - s := by linarith

        by_cases h_high : s ≤ chordSlope f I.1 I.2
        · -- Case 1: high slope
          have hB' : I.1 ≤ m := by linarith
          have hL'_bound_I1 : ∀ K ∈ L', 0 ≤ K.1 ∧ K.2 ≤ I.1 :=
            fun K hK => ⟨(hL'_bound_B K hK).1, hL'_right K hK⟩
          have h_ih := ih L'.length hL'_len I.1 hB' L' rfl hL'_sort hL'_lin hL'_bound_I1 hL'_min
          rcases h_ih with ⟨J', hJ'_sort, hJ'_good, hJ'_bound, hJ'_min, hJ'_len⟩
          let J := J' ++ [I]
          have hJ'_right_I : ∀ K ∈ J', K.2 ≤ I.1 :=
            fun K hK => (hJ'_bound K hK).2
          have h_cross : ∀ (x : ℝ × ℝ), x ∈ J' → ∀ (y : ℝ × ℝ), y ∈ [I] → (fun I J => I.2 ≤ J.1) x y := by
            intro x hx y hy
            have h_y_eq : y = I := by simpa [mem_singleton] using hy
            rw [h_y_eq]
            exact hJ'_right_I x hx
          have h_pair : (J' ++ [I]).Pairwise (fun I J => I.2 ≤ J.1) := by
            rw [List.pairwise_append]
            exact ⟨hJ'_sort.1, by simp, h_cross⟩
          have h_slope_le2 : chordSlope f I.1 I.2 ≤ 2 :=
            slope_le_two f I.1 I.2 m hI2 hI1 hI3m hLip
          have h_len1 : totalLength J = totalLength J' + (I.2 - I.1) := by
            simp [J, totalLength, map_append] <;> ring
          have h_total_L : totalLength L = totalLength L' + (I.2 - I.1) := by
            have h_eq2 : L = L' ++ [I] := h_eq
            rw [h_eq2]
            simp [totalLength, map_append] <;> ring
          exact ⟨J,
            ⟨h_pair, fun K hK => by
              simp only [J, mem_append, mem_singleton] at hK
              rcases hK with (hK | rfl)
              · exact hJ'_sort.2 K hK
              · exact hI1⟩,
            fun K hK => by
              simp only [J, mem_append, mem_singleton] at hK
              rcases hK with (hK | rfl)
              · exact hJ'_good K hK
              · exact Or.inl ⟨hI_lin_2δ, h_high, h_slope_le2⟩,
            fun K hK => by
              simp only [J, mem_append, mem_singleton] at hK
              rcases hK with (hK | rfl)
              · have hb := hJ'_bound K hK
                exact ⟨hb.1, by linarith [hI3]⟩
              · exact ⟨hI2, hI3⟩,
            fun K hK => by
              simp only [J, mem_append, mem_singleton] at hK
              rcases hK with (hK | rfl)
              · exact hJ'_min K hK
              · have h5 : δ * τ0 * m ≤ τ0 * m := by
                  have h6 : δ ≤ 1 := by linarith
                  have h7 : 0 ≤ τ0 * m := by positivity
                  nlinarith
                linarith,
            by
              rw [h_len1]
              have h : (I.2 - I.1) ≥ (1 - δ) * (I.2 - I.1) := by
                have h' : 0 ≤ I.2 - I.1 := by linarith
                nlinarith
              nlinarith [hJ'_len, h, h_total_L]⟩
        · -- Case 2: low slope
          have h_low : chordSlope f I.1 I.2 < s := by linarith
          by_cases h_small : I.2 ≤ ε' * m / (t - s)
          · -- Case 2a: small, discard
            have hL_bound2 : ∀ K ∈ L, 0 ≤ K.1 ∧ K.2 ≤ I.2 := by
              intro K hK
              have h1 : K.2 ≤ I.2 := by
                by_cases h : K = I
                · rw [h]
                · have hK' : K ∈ L' := by
                    simp only [h_eq, mem_append, mem_singleton] at hK <;> tauto
                  have h3 : ∀ (x : ℝ × ℝ), x ∈ L' → ∀ (y : ℝ × ℝ), y ∈ [I] → (fun I J => I.2 ≤ J.1) x y := by
                    rw [h_eq] at hL_sort
                    exact (List.pairwise_append.mp hL_sort.1).2.2
                  have h4 : K.2 ≤ I.1 := h3 K hK' I (by simp)
                  linarith
              exact ⟨(hL_bound K hK).1, h1⟩
            have hB_nonneg : 0 ≤ I.2 := by linarith [hI1, hI2]
            have h_total_le : totalLength L ≤ I.2 := totalLength_le_bound hB_nonneg hL_sort hL_bound2
            have h9 : totalLength L ≤ ε' * m / (t - s) := by linarith
            have h10 : 0 ≤ totalLength L := totalLength_nonneg hL_sort.2
            have h11 : 0 ≤ 1 - δ := by linarith
            have h12 : (1 - δ) * totalLength L ≤ ε' * m / (t - s) := by nlinarith
            exact ⟨[], by simp [SortedDisjoint, GoodIntervals], by simp [GoodIntervals], by simp, by simp,
              by simp [totalLength] <;> exact h12⟩
          · -- Case 2b: large low-slope
            have h_large : ε' * m / (t - s) < I.2 := by linarith
            have h_b_pos : 0 < I.2 := by
              have h_pos : 0 ≤ ε' * m / (t - s) := by positivity
              linarith
            have h_slope0 : s < chordSlope f 0 I.2 := by
              have h11 : f I.2 ≥ t * I.2 - ε' * m := h_lower I.2 ⟨by linarith, hI3m⟩
              have h12 : chordSlope f 0 I.2 = f I.2 / I.2 := by
                simp [chordSlope, h_f0] <;> ring
              have h14 : ε' * m < (t - s) * I.2 := by
                have h141 : ε' * m = (t - s) * (ε' * m / (t - s)) := by
                  field_simp [h_ts_pos.ne'] <;> ring
                rw [h141]
                exact mul_lt_mul_of_pos_left h_large h_ts_pos
              have h13 : t * I.2 - ε' * m > s * I.2 := by nlinarith
              have h15 : 0 < I.2 := h_b_pos
              have h16 : (t * I.2 - ε' * m) / I.2 > s * I.2 / I.2 := by
                apply div_lt_div_of_pos_right h13 h15
              have h17 : f I.2 / I.2 ≥ (t * I.2 - ε' * m) / I.2 := by
                have h_pos : 0 ≤ 1 / I.2 := by positivity
                have h20 : (1 / I.2) * f I.2 ≥ (1 / I.2) * (t * I.2 - ε' * m) :=
                  mul_le_mul_of_nonneg_left h11 h_pos
                calc f I.2 / I.2
                  = (1 / I.2) * f I.2 := by ring
                _ ≥ (1 / I.2) * (t * I.2 - ε' * m) := h20
                _ = (t * I.2 - ε' * m) / I.2 := by ring
              rw [h12]
              calc f I.2 / I.2
                ≥ (t * I.2 - ε' * m) / I.2 := h17
              _ > s * I.2 / I.2 := h16
              _ = s := by field_simp [h15.ne'] <;> ring
            have hI1_pos : 0 < I.1 := by
              by_contra h
              have h' : I.1 = 0 := by linarith [hI2]
              have h_contra : chordSlope f 0 I.2 < s := by
                rw [h'] at h_low; exact h_low
              linarith [h_slope0, h_contra]
            rcases largest_chordSlope_eq f h_cont hI1_pos hI1 h_slope0 h_low
              with ⟨c', hc'_ge0, hc'_le, h_slope_c', h_mono_slope⟩
            have hc'_pos : 0 < c' := by
              by_contra h
              have h' : c' = 0 := by linarith [hc'_ge0]
              rw [h'] at h_slope_c'
              linarith [h_slope0]
            have hc'_lt : c' < I.1 := by
              have h_ne : c' ≠ I.1 := by intro eq; rw [eq] at h_slope_c'; linarith
              exact lt_of_le_of_ne hc'_le h_ne
            have h_super_c' : EpsilonSuperlinear f (δ ^ 2) c' I.2 :=
              merged_epsilonSuperlinear f (by positivity) hc'_lt hI1
                h_slope_c' h_low hI_lin h_mono_slope
            have h_super_c'_2δ : EpsilonSuperlinear f (2 * δ) c' I.2 := by
              intro x hx
              have h7 : chordValue f c' I.2 x - δ ^ 2 * (I.2 - c') ≤ f x := h_super_c' x hx
              have h8 : δ ^ 2 * (I.2 - c') ≤ 2 * δ * (I.2 - c') := by
                have h9 : 0 ≤ I.2 - c' := by linarith
                have h10 : δ ^ 2 ≤ 2 * δ := by nlinarith [hδ_lt_one]
                nlinarith
              linarith
            have hc'_lt_b : c' < I.2 := by linarith [hc'_lt, hI1]
            have h_slope0c' : s < chordSlope f 0 c' :=
              chordSlope0_gt_s_of_middle f (c := c') (b := I.2) hc'_pos hc'_lt_b h_slope0 h_slope_c'
            have hL'_right_R : ∀ K ∈ L', K.2 ≤ I.1 := hL'_right
            have hL'_len_le : L'.length ≤ L.length := hL'_sublist.length_le
            have h_merge := extendMerge_induction f s m δ τ0 hs hδ_pos (by linarith) (by linarith) hτ0_pos h_cont
              L.length I.1 c' I.2 L' hL'_len_le
              ⟨hc'_ge0, by linarith, hI3m⟩
              (by linarith [hc'_le]) (by linarith [hI1, hI3m])
              h_slope_c' h_super_c'_2δ h_slope0c'
              hL'_sort hL'_lin hL'_min hL'_bound_m hL'_right_R
            rcases h_merge with ⟨cstar, J_chain, L_rem, hcstar0, hcstar_le, h_slope_star, h_super_star,
              hJ_sort, hJ_good_raw, hJ_bound, hJ_min, hJ_right, h_cross, hLrem_right, hLrem_sublist, h_len_preserve⟩
            have hLrem_len_n : L_rem.length < n := by
              have h1 : L_rem.length ≤ L'.length := hLrem_sublist.length_le
              omega
            have hLrem_min : ∀ K ∈ L_rem, τ0 * m ≤ K.2 - K.1 :=
              fun K hK => hL'_min K (hLrem_sublist.subset hK)
            have hLrem_sort : SortedDisjoint L_rem :=
              ⟨hL'_sort.1.sublist hLrem_sublist, fun K hK => hL'_sort.2 K (hLrem_sublist.subset hK)⟩
            have hLrem_lin : AllEpsilonLinear f (δ ^ 2) L_rem :=
              fun K hK => hL'_lin K (hLrem_sublist.subset hK)
            have h_cstar_lt_I2 : cstar < I.2 := by linarith [hcstar_le, hc'_lt]
            have hJ_good_chain : GoodIntervals f s δ J_chain := by
              intro p hp
              have h1 := hJ_good_raw p hp
              have h2 : chordSlope f p.1 p.2 ≤ 2 :=
                slope_le_two f p.1 p.2 m (hJ_bound p hp).1 (hJ_sort.2 p hp) (hJ_bound p hp).2 hLip
              exact Or.inl ⟨h1.1, h1.2, h2⟩
            -- Choose bound for recursion on L_rem
            by_cases hJchain_empty : J_chain = []
            · -- J_chain empty: use cstar as bound
              have hLrem_bound_cstar : ∀ K ∈ L_rem, 0 ≤ K.1 ∧ K.2 ≤ cstar := by
                intro K hK
                have h := hL'_bound_m K (hLrem_sublist.subset hK)
                exact ⟨h.1, hLrem_right K hK⟩
              have h_ih := ih L_rem.length hLrem_len_n cstar (by linarith [hcstar0, h_cstar_lt_I2]) L_rem rfl
                hLrem_sort hLrem_lin hLrem_bound_cstar hLrem_min
              rcases h_ih with ⟨J_rem, hJrem_sort, hJrem_good, hJrem_bound, hJrem_min, hJrem_len⟩
              let J := J_rem ++ [(cstar, I.2)]
              have hJrem_right_cstar : ∀ K ∈ J_rem, K.2 ≤ cstar := fun K hK => (hJrem_bound K hK).2
              have h_cross2 : ∀ (x : ℝ × ℝ), x ∈ J_rem → ∀ (y : ℝ × ℝ), y ∈ [(cstar, I.2)] → (fun I J => I.2 ≤ J.1) x y := by
                intro x hx y hy
                have h_y_eq : y = (cstar, I.2) := by simpa [mem_singleton] using hy
                rw [h_y_eq]
                exact hJrem_right_cstar x hx
              have h_pair : J.Pairwise (fun I J => I.2 ≤ J.1) := by
                simp only [J, List.pairwise_append]
                exact ⟨hJrem_sort.1, by simp, h_cross2⟩
              have hJ_SD : SortedDisjoint J :=
                ⟨h_pair, fun K hK => by
                  simp only [J, mem_append, mem_singleton] at hK
                  rcases hK with (hK | rfl)
                  · exact hJrem_sort.2 K hK
                  · exact h_cstar_lt_I2⟩
              have hJ_good : GoodIntervals f s δ J := by
                intro K hK
                simp only [J, mem_append, mem_singleton] at hK
                rcases hK with (hK | rfl)
                · exact hJrem_good K hK
                · exact Or.inr ⟨h_super_star, h_slope_star⟩
              have hJ_bound_all : ∀ K ∈ J, 0 ≤ K.1 ∧ K.2 ≤ B := by
                intro K hK
                simp only [J, mem_append, mem_singleton] at hK
                rcases hK with (hK | rfl)
                · have hb := hJrem_bound K hK
                  have hK2_le_B : K.2 ≤ B := by
                    have h1 : K.2 ≤ cstar := hb.2
                    have h2 : cstar ≤ c' := hcstar_le
                    have h3 : c' < I.1 := hc'_lt
                    have h4 : I.1 < I.2 := hI1
                    linarith [hI3]
                  exact ⟨hb.1, hK2_le_B⟩
                · exact ⟨hcstar0, hI3⟩
              have hJ_min_all : ∀ K ∈ J, δ * τ0 * m ≤ K.2 - K.1 := by
                intro K hK
                simp only [J, mem_append, mem_singleton] at hK
                rcases hK with (hK | rfl)
                · exact hJrem_min K hK
                · have h9 : cstar ≤ c' := hcstar_le
                  have h10 : I.2 - cstar ≥ I.2 - I.1 := by linarith [hc'_lt]
                  have h11 : δ * τ0 * m ≤ τ0 * m := by
                    have h12 : δ ≤ 1 := by linarith
                    have h13 : 0 ≤ τ0 * m := by positivity
                    nlinarith
                  linarith
              have h_total_J : totalLength J = totalLength J_rem + (I.2 - cstar) := by
                simp [J, totalLength, map_append] <;> ring
              have h_final_len : totalLength J ≥ (1 - δ) * totalLength L - ε' * m / (t - s) := by
                rw [h_total_J]
                have h_tl_zero : totalLength J_chain = 0 := by
                  rw [hJchain_empty]
                  simp [totalLength]
                have h_eq2 : totalLength J_rem + (I.2 - cstar) =
                    totalLength J_rem + (totalLength J_chain + (I.1 - cstar)) + (I.2 - I.1) := by
                  rw [h_tl_zero]
                  <;> ring
                rw [h_eq2]
                set E := ε' * m / (t - s) with hE_def
                have h_ih : totalLength J_rem ≥ (1 - δ) * totalLength L_rem - E := hJrem_len
                have h_merge : totalLength J_chain + (I.1 - cstar) ≥ (1 - δ) * (totalLength L' - totalLength L_rem) := h_len_preserve
                have h11 : totalLength J_rem + (totalLength J_chain + (I.1 - cstar)) ≥ (1 - δ) * totalLength L' - E := by
                  have h_a : totalLength J_rem ≥ (1 - δ) * totalLength L_rem - E := h_ih
                  have h_b : (totalLength J_chain + (I.1 - cstar)) ≥ (1 - δ) * (totalLength L' - totalLength L_rem) := h_merge
                  linarith
                have h7 : totalLength L = totalLength L' + (I.2 - I.1) := by
                  rw [h_eq]; simp [totalLength, map_append] <;> ring
                have h9 : 0 ≤ I.2 - I.1 := by linarith
                have h10 : (1 - δ) * (I.2 - I.1) ≤ I.2 - I.1 := by
                  have h101 : 0 ≤ 1 - δ := by linarith
                  have h102 : (1 - δ) ≤ 1 := by linarith
                  have h : (1 - δ) * (I.2 - I.1) ≤ 1 * (I.2 - I.1) :=
                    mul_le_mul_of_nonneg_right h102 h9
                  simpa using h
                rw [h7]
                let X := totalLength J_rem + (totalLength J_chain + (I.1 - cstar))
                let B := totalLength L'
                let Z := I.2 - I.1
                have hX : X ≥ (1 - δ) * B - E := h11
                have hZ : (1 - δ) * Z ≤ Z := h10
                have h_goal : X + Z ≥ (1 - δ) * (B + Z) - E := by
                  calc X + Z
                    ≥ ((1 - δ) * B - E) + Z := add_le_add hX (le_refl Z)
                  _ ≥ ((1 - δ) * B - E) + (1 - δ) * Z := add_le_add_right hZ ((1 - δ) * B - E)
                  _ = (1 - δ) * (B + Z) - E := by ring
                exact h_goal
              exact ⟨J, hJ_SD, hJ_good, hJ_bound_all, hJ_min_all, h_final_len⟩
            · -- J_chain non-empty
              let q0 := J_chain.head hJchain_empty
              have hq0_in : q0 ∈ J_chain := List.head_mem hJchain_empty
              let M := q0.1
              have hM_nonneg : 0 ≤ M := (hJ_bound q0 hq0_in).1
              have hM_le_m : M ≤ m := by
                have h1 : q0.1 < q0.2 := hJ_sort.2 q0 hq0_in
                have h2 : q0.2 ≤ m := (hJ_bound q0 hq0_in).2
                exact h1.le.trans h2
              have hLrem_le_M : ∀ K ∈ L_rem, K.2 ≤ M := by
                intro K hK
                exact h_cross K hK q0 hq0_in
              have hLrem_bound_M : ∀ K ∈ L_rem, 0 ≤ K.1 ∧ K.2 ≤ M := by
                intro K hK
                have h := hL'_bound_m K (hLrem_sublist.subset hK)
                exact ⟨h.1, hLrem_le_M K hK⟩
              have h_ih := ih L_rem.length hLrem_len_n M hM_le_m L_rem rfl
                hLrem_sort hLrem_lin hLrem_bound_M hLrem_min
              rcases h_ih with ⟨J_rem, hJrem_sort, hJrem_good, hJrem_bound, hJrem_min, hJrem_len⟩
              let J := J_rem ++ J_chain ++ [(cstar, I.2)]
              have h_mem : ∀ (K : ℝ × ℝ), K ∈ J → K ∈ J_rem ∨ K ∈ J_chain ∨ K = (cstar, I.2) := by
                intro K hK
                have h : K ∈ (J_rem ++ J_chain) ++ [(cstar, I.2)] := hK
                rw [List.mem_append] at h
                rcases h with (h | h)
                · rw [List.mem_append] at h
                  rcases h with (h | h)
                  · exact Or.inl h
                  · exact Or.inr (Or.inl h)
                · have h' : K = (cstar, I.2) := by simpa [List.mem_singleton] using h
                  exact Or.inr (Or.inr h')
              have hJrem_right_M : ∀ K ∈ J_rem, K.2 ≤ M := fun K hK => (hJrem_bound K hK).2
              have hJchain_eq : q0 :: J_chain.tail = J_chain := List.cons_head_tail hJchain_empty
              have h_y1_ge_M : ∀ y ∈ J_chain, M ≤ y.1 := by
                intro y hy
                by_cases h_y_eq : y = q0
                · have h_goal : M ≤ y.1 := by
                    have h_eq : y.1 = M := by
                      dsimp only [M]
                      rw [h_y_eq] <;> rfl
                    exact le_of_eq h_eq.symm
                  exact h_goal
                · have h1 : y ∈ q0 :: J_chain.tail := by
                    rw [hJchain_eq]; exact hy
                  have h2 : y = q0 ∨ y ∈ J_chain.tail := by
                    simpa [mem_cons] using h1
                  have h_y_tail : y ∈ J_chain.tail := by
                    rcases h2 with (h2 | h2)
                    · contradiction
                    · exact h2
                  have h_q0_before_y : q0.2 ≤ y.1 :=
                    hJ_sort.1.rel_head_tail h_y_tail
                  have h_q01_lt_q02 : q0.1 < q0.2 := hJ_sort.2 q0 hq0_in
                  exact le_trans h_q01_lt_q02.le h_q0_before_y
              have h_cross_rem_chain : ∀ (x : ℝ × ℝ), x ∈ J_rem → ∀ (y : ℝ × ℝ), y ∈ J_chain → (fun I J => I.2 ≤ J.1) x y := by
                intro x hx y hy
                have h_x2_le_M : x.2 ≤ M := hJrem_right_M x hx
                have h_y1_ge_M' : M ≤ y.1 := h_y1_ge_M y hy
                exact le_trans h_x2_le_M h_y1_ge_M'
              have h1 : (J_rem ++ J_chain).Pairwise (fun I J => I.2 ≤ J.1) := by
                rw [List.pairwise_append]
                exact ⟨hJrem_sort.1, hJ_sort.1, h_cross_rem_chain⟩
              have h_chain_right_cstar : ∀ K ∈ J_chain, K.2 ≤ cstar := hJ_right
              have h_cross3 : ∀ (x : ℝ × ℝ), x ∈ (J_rem ++ J_chain) → ∀ (y : ℝ × ℝ), y ∈ [(cstar, I.2)] → (fun I J => I.2 ≤ J.1) x y := by
                intro x hx y hy
                have h_y_eq : y = (cstar, I.2) := by simpa [mem_singleton] using hy
                rw [h_y_eq]
                simp only [mem_append] at hx
                rcases hx with (hx | hx)
                · have h_x2_le_M : x.2 ≤ M := hJrem_right_M x hx
                  have h_M_le_cstar : M ≤ cstar := by
                    have h : q0.2 ≤ cstar := hJ_right q0 hq0_in
                    have h2 : q0.1 < q0.2 := hJ_sort.2 q0 hq0_in
                    exact h2.le.trans h
                  exact le_trans h_x2_le_M h_M_le_cstar
                · exact h_chain_right_cstar x hx
              have h_pair : J.Pairwise (fun I J => I.2 ≤ J.1) := by
                have h5 : ((J_rem ++ J_chain) ++ [(cstar, I.2)]).Pairwise (fun I J => I.2 ≤ J.1) := by
                  rw [List.pairwise_append]
                  exact ⟨h1, by simp, h_cross3⟩
                exact h5
              have hJ_SD : SortedDisjoint J :=
                ⟨h_pair, fun K hK => by
                  have hK' := h_mem K hK
                  rcases hK' with (hK | hK | rfl)
                  · exact hJrem_sort.2 K hK
                  · exact hJ_sort.2 K hK
                  · exact h_cstar_lt_I2⟩
              have hJ_good : GoodIntervals f s δ J := by
                intro K hK
                have hK' := h_mem K hK
                rcases hK' with (hK | hK | rfl)
                · exact hJrem_good K hK
                · exact hJ_good_chain K hK
                · exact Or.inr ⟨h_super_star, h_slope_star⟩
              have hJ_bound_all : ∀ K ∈ J, 0 ≤ K.1 ∧ K.2 ≤ B := by
                intro K hK
                have hK' := h_mem K hK
                rcases hK' with (hK | hK | rfl)
                · have hb := hJrem_bound K hK
                  have hM_le_B : M ≤ B := by
                    have h1 : q0.2 ≤ cstar := hJ_right q0 hq0_in
                    have h2 : q0.1 < q0.2 := hJ_sort.2 q0 hq0_in
                    have h3 : cstar ≤ I.2 := by linarith [hcstar_le, hc'_lt, hI1]
                    linarith [hI3]
                  exact ⟨hb.1, by linarith [hb.2, hM_le_B]⟩
                · have hb := hJ_bound K hK
                  have hK2_le_B : K.2 ≤ B := by
                    have h1 : K.2 ≤ cstar := hJ_right K hK
                    have h2 : cstar ≤ I.2 := by linarith [hcstar_le, hc'_lt, hI1]
                    linarith [hI3]
                  exact ⟨hb.1, hK2_le_B⟩
                · exact ⟨hcstar0, hI3⟩
              have hJ_min_all : ∀ K ∈ J, δ * τ0 * m ≤ K.2 - K.1 := by
                intro K hK
                have hK' := h_mem K hK
                rcases hK' with (hK | hK | rfl)
                · exact hJrem_min K hK
                · exact hJ_min K hK
                · have h9 : cstar ≤ c' := hcstar_le
                  have h10 : I.2 - cstar ≥ I.2 - I.1 := by linarith [hc'_lt]
                  have h11 : δ * τ0 * m ≤ τ0 * m := by
                    have h12 : δ ≤ 1 := by linarith
                    have h13 : 0 ≤ τ0 * m := by positivity
                    nlinarith
                  linarith
              have h_total_J : totalLength J = totalLength J_rem + totalLength J_chain + (I.2 - cstar) := by
                have h : totalLength (J_rem ++ J_chain ++ [(cstar, I.2)]) = totalLength J_rem + totalLength J_chain + (I.2 - cstar) := by
                  simp [totalLength, map_append] <;> ring
                exact h
              have h_final_len : totalLength J ≥ (1 - δ) * totalLength L - ε' * m / (t - s) := by
                rw [h_total_J]
                have h_eq2 : totalLength J_rem + totalLength J_chain + (I.2 - cstar) =
                    totalLength J_rem + (totalLength J_chain + (I.1 - cstar)) + (I.2 - I.1) := by ring
                rw [h_eq2]
                set E := ε' * m / (t - s) with hE_def
                have h_ih : totalLength J_rem ≥ (1 - δ) * totalLength L_rem - E := hJrem_len
                have h_merge : totalLength J_chain + (I.1 - cstar) ≥ (1 - δ) * (totalLength L' - totalLength L_rem) := h_len_preserve
                have h11 : totalLength J_rem + (totalLength J_chain + (I.1 - cstar)) ≥ (1 - δ) * totalLength L' - E := by
                  have h_a : totalLength J_rem ≥ (1 - δ) * totalLength L_rem - E := h_ih
                  have h_b : (totalLength J_chain + (I.1 - cstar)) ≥ (1 - δ) * (totalLength L' - totalLength L_rem) := h_merge
                  linarith
                have h7 : totalLength L = totalLength L' + (I.2 - I.1) := by
                  rw [h_eq]; simp [totalLength, map_append] <;> ring
                have h9 : 0 ≤ I.2 - I.1 := by linarith
                have h10 : (1 - δ) * (I.2 - I.1) ≤ I.2 - I.1 := by
                  have h101 : 0 ≤ 1 - δ := by linarith
                  have h102 : (1 - δ) ≤ 1 := by linarith
                  have h : (1 - δ) * (I.2 - I.1) ≤ 1 * (I.2 - I.1) :=
                    mul_le_mul_of_nonneg_right h102 h9
                  simpa using h
                rw [h7]
                let X := totalLength J_rem + (totalLength J_chain + (I.1 - cstar))
                let B := totalLength L'
                let Z := I.2 - I.1
                have hX : X ≥ (1 - δ) * B - E := h11
                have hZ : (1 - δ) * Z ≤ Z := h10
                have h_goal : X + Z ≥ (1 - δ) * (B + Z) - E := by
                  calc X + Z
                    ≥ ((1 - δ) * B - E) + Z := add_le_add hX (le_refl Z)
                  _ ≥ ((1 - δ) * B - E) + (1 - δ) * Z := add_le_add_right hZ ((1 - δ) * B - E)
                  _ = (1 - δ) * (B + Z) - E := by ring
                exact h_goal
              exact ⟨J, hJ_SD, hJ_good, hJ_bound_all, hJ_min_all, h_final_len⟩
  exact fun B hB L hL_sort hL_lin hL_bound hL_min =>
    h_main L.length B hB L rfl hL_sort hL_lin hL_bound hL_min

end
end CombinatorialKaufman.ProcessIntervals
