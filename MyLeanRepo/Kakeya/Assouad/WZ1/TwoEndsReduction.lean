import MyLeanRepo.Kakeya.Assouad.WZ1.Statements

/-!
# Two-ends reduction lemma

Given a finite planar set E in the unit ball, find a strip S of half-width w ≥ δ
such that S contains a c·w^ζ fraction of E's points, and within S, E is
non-concentrated on any narrower strip (of width r ≥ δ) in any direction.

This is the discrete version of WZ1 Lemma 46 (Sticky-Kakeya paper, Section 8).
-/

namespace Kakeya.Assouad

open scoped ENNReal

lemma two_ends_reduction
    {E : DiscreteSet 2} {δ ζ : ℝ}
    (hδ : 0 < δ)
    (hδ_le_one : δ ≤ 1)
    (hζ : 0 < ζ)
    (hE_nonempty : E.Nonempty)
    (hE_ball : E.IsInUnitBall)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ (normal : Point2) (t : ℝ) (w : ℝ),
      ‖normal‖ = 1 ∧
      δ ≤ w ∧
      w ≤ 1 ∧
      (c * Real.rpow w ζ * E.card : ℝ) ≤
        (E.filter fun p => |inner ℝ p normal - t| ≤ w).card ∧
      ∀ (normal' : Point2) (t' : ℝ) (r : ℝ),
        ‖normal'‖ = 1 → δ ≤ r → r ≤ w →
        (E.filter fun p =>
          |inner ℝ p normal - t| ≤ w ∧
          |inner ℝ p normal' - t'| ≤ r).card ≤
        Real.rpow (r / w) ζ *
        (E.filter fun p => |inner ℝ p normal - t| ≤ w).card := by
  classical
  let N := E.card
  have hN_pos : 0 < N := Finset.card_pos.mpr hE_nonempty

  let K1 : Set Point2 := {v | ‖v‖ = 1}
  let K2 : Set ℝ := Set.Icc (-2 : ℝ) 2
  let K : Set (Point2 × ℝ) := K1 ×ˢ K2

  have hK1_compact : IsCompact K1 := by
    have h_eq : K1 = Metric.sphere (0 : Point2) 1 := by
      ext v
      simp [K1] <;> rfl
    rw [h_eq]
    exact isCompact_sphere (0 : Point2) 1
  have hK2_compact : IsCompact K2 := isCompact_Icc
  have hK_compact : IsCompact K := hK1_compact.prod hK2_compact

  let count (normal : Point2) (t w : ℝ) : ℕ :=
    (E.filter fun p => |inner ℝ p normal - t| ≤ w).card

  let W : Set ℝ := {w | δ ≤ w ∧ ∃ (normal : Point2) (t : ℝ),
    ‖normal‖ = 1 ∧ -2 ≤ t ∧ t ≤ 2 ∧
    (c * Real.rpow w ζ * N : ℝ) ≤ count normal t w}

  -- W is non-empty: w = 1, t = 0 works
  let normal0 : Point2 := EuclideanSpace.single 0 1
  have hnormal0 : ‖normal0‖ = 1 := by simp [normal0] <;> norm_num
  have h1_in_W : (1 : ℝ) ∈ W := by
    have h1 : ∀ p ∈ E, |inner ℝ p normal0 - (0 : ℝ)| ≤ 1 := by
      intro p hp
      have h2 : ‖p‖ ≤ 1 := by simpa [dist_eq_norm] using hE_ball p hp
      have h4 : |inner ℝ p normal0| ≤ ‖p‖ * ‖normal0‖ := abs_real_inner_le_norm p normal0
      have h5 : |inner ℝ p normal0| ≤ ‖p‖ := by rw [hnormal0] at h4; simpa using h4
      have h6 : |inner ℝ p normal0 - (0 : ℝ)| ≤ 1 := by
        have h7 : |inner ℝ p normal0 - (0 : ℝ)| = |inner ℝ p normal0| := by ring_nf
        rw [h7]; linarith
      exact h6
    have h51 : E.filter (fun p => |inner ℝ p normal0 - (0 : ℝ)| ≤ 1) = E :=
      Finset.filter_true_of_mem h1
    have h5 : count normal0 0 1 = N := by
      simp only [count]; rw [h51] <;> rfl
    have h6 : (c * Real.rpow 1 ζ * (N : ℝ)) ≤ (N : ℝ) := by
      have h7 : Real.rpow 1 ζ = 1 := by simp
      have h_eq : c * Real.rpow 1 ζ * (N : ℝ) = c * (N : ℝ) := by rw [h7] <;> ring
      rw [h_eq]; exact mul_le_of_le_one_left (by positivity) hc1
    exact ⟨hδ_le_one, normal0, 0, hnormal0, by norm_num, by norm_num, by
      rw [h5] <;> exact h6⟩

  have hW_nonempty : W.Nonempty := ⟨1, h1_in_W⟩
  have hW_bdd' : ∀ w ∈ W, δ ≤ w := fun w hw => hw.1

  let w₀ := sInf W
  have h_bdd : BddBelow W := ⟨δ, hW_bdd'⟩
  have hw₀_bdd : δ ≤ w₀ := le_csInf hW_nonempty hW_bdd'
  have hw₀_le_one : w₀ ≤ 1 := csInf_le h_bdd h1_in_W

  -- Sequence w_n ∈ W converging to w₀
  have h_seq : ∃ (w_n : ℕ → ℝ), Filter.Tendsto w_n Filter.atTop (nhds w₀) ∧ ∀ n, w_n n ∈ W :=
    let h := exists_seq_tendsto_sInf hW_nonempty ⟨δ, hW_bdd'⟩
    ⟨h.choose, h.choose_spec.2.1, h.choose_spec.2.2⟩
  rcases h_seq with ⟨w_n, h_tendsto, hwn⟩

  choose normal t hnormal ht_neg ht_pos hcount using fun n => (hwn n).2
  have hK_seq : ∀ n, (normal n, t n) ∈ K := by
    intro n; exact ⟨hnormal n, ⟨ht_neg n, ht_pos n⟩⟩

  -- Compactness gives cluster point, then convergent subsequence
  let f : ℕ → Point2 × ℝ := fun n => (normal n, t n)
  have hK_in_map : K ∈ Filter.map f Filter.atTop := by
    have h1 : f ⁻¹' K = Set.univ := by
      ext n
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      exact hK_seq n
    rw [Filter.mem_map, h1]
    exact Filter.univ_mem
  have h_map_le : Filter.map f Filter.atTop ≤ Filter.principal K := by
    intro s hs
    exact Filter.mem_of_superset hK_in_map hs
  have h_cluster : ∃ p_lim ∈ K, ClusterPt p_lim (Filter.map f Filter.atTop) :=
    hK_compact h_map_le
  rcases h_cluster with ⟨p_lim, hp_lim_in, hpt⟩
  have h_map_cluster : MapClusterPt p_lim Filter.atTop f := hpt
  obtain ⟨ψ, hψ_strict, h_conv⟩ := MapClusterPt.tendsto_subseq h_map_cluster
  let normal_lim := p_lim.1
  let t_lim := p_lim.2
  have hK_lim1 : ‖normal_lim‖ = 1 := hp_lim_in.1
  have hK_lim2 : -2 ≤ t_lim ∧ t_lim ≤ 2 := hp_lim_in.2

  -- Define S n using the subsequence ψ
  let S : ℕ → Finset Point2 := fun n =>
    E.filter fun p => |inner ℝ p (normal (ψ n)) - t (ψ n)| ≤ w_n (ψ n)
  have hS_subset : ∀ n, S n ⊆ E := fun n => Finset.filter_subset _ _
  have h_in_powerset : ∀ n, S n ∈ E.powerset := by
    intro n; exact Finset.mem_powerset.mpr (hS_subset n)

  -- Pigeonhole: find E' with infinite fiber
  have h_pigeonhole : ∃ (E' : Finset Point2), E' ∈ E.powerset ∧ Set.Infinite {n | S n = E'} := by
    by_contra h
    push Not at h
    have h3 : ∀ E' ∈ E.powerset, Set.Finite {n | S n = E'} := by
      intro E' hE'
      have h4 : ¬ Set.Infinite {n | S n = E'} := by
        have h5 := h E'
        tauto
      exact Set.not_infinite.mp h4
    have h4 : Set.Finite (⋃ E' ∈ E.powerset, {n | S n = E'}) :=
      Set.Finite.biUnion (Finset.finite_toSet _) h3
    have h5 : (⋃ E' ∈ E.powerset, {n | S n = E'}) = Set.univ := by
      ext n
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨S n, h_in_powerset n, rfl⟩
    rw [h5] at h4
    exact Set.infinite_univ h4
  rcases h_pigeonhole with ⟨E', hE'_in, hinf⟩

  -- Extract strictly increasing subsequence from infinite fiber
  have h_forall : ∀ N, ∃ n, n > N ∧ n ∈ {n | S n = E'} := by
    intro N
    by_contra h2
    push Not at h2
    have h3 : {n | S n = E'} ⊆ Set.Icc 0 N := by
      intro x hx
      have h4 : x ≤ N := by
        by_contra h5
        have h6 : x > N := by linarith
        have h7 : x ∉ {n | S n = E'} := h2 x h6
        exact h7 hx
      exact ⟨by linarith [Nat.zero_le x], h4⟩
    have h4 : Set.Finite {n | S n = E'} := Set.Finite.subset (Set.finite_Icc 0 N) h3
    exact hinf h4
  obtain ⟨φ, hφ_strict, hφ_mem⟩ := Nat.exists_strictMono_subsequence h_forall
  have hE'_eq : ∀ n, S (φ n) = E' := fun n => hφ_mem n

  have h_count_bound : ∀ n, (c * Real.rpow (w_n (ψ (φ n))) ζ * N : ℝ) ≤ (E'.card : ℝ) := by
    intro n
    have h9 := hcount (ψ (φ n))
    have h10 : count (normal (ψ (φ n))) (t (ψ (φ n))) (w_n (ψ (φ n))) = (S (φ n)).card := by
      rfl
    rw [h10, hE'_eq n] at h9
    exact h9

  have h10 : Filter.Tendsto (fun n => w_n (ψ (φ n))) Filter.atTop (nhds w₀) :=
    h_tendsto.comp (hψ_strict.tendsto_atTop.comp hφ_strict.tendsto_atTop)

  have h_pos0 : 0 < w₀ := by linarith [hw₀_bdd, hδ]
  have h_cont_rpow : ContinuousAt (fun x : ℝ => Real.rpow x ζ) w₀ := by
    apply ContinuousAt.rpow
    · exact continuousAt_id
    · exact continuousAt_const
    · exact Or.inl (ne_of_gt h_pos0)
  have h_cont1 : ContinuousAt (fun x : ℝ => c * Real.rpow x ζ * N) w₀ :=
    (h_cont_rpow.const_mul c).mul_const (N : ℝ)
  have h11 : (c * Real.rpow w₀ ζ * N : ℝ) ≤ (E'.card : ℝ) := by
    have h12 : Filter.Tendsto (fun n => c * Real.rpow (w_n (ψ (φ n))) ζ * N) Filter.atTop
        (nhds (c * Real.rpow w₀ ζ * N)) :=
      h_cont1.tendsto.comp h10
    exact le_of_tendsto h12 (Filter.Eventually.of_forall h_count_bound)

  have h13 : ∀ p ∈ E', |inner ℝ p normal_lim - t_lim| ≤ w₀ := by
    intro p hp
    have h14 : ∀ n, |inner ℝ p (normal (ψ (φ n))) - t (ψ (φ n))| ≤ w_n (ψ (φ n)) := by
      intro n
      have h15 : p ∈ S (φ n) := by rw [hE'_eq n] <;> exact hp
      simp only [S, Finset.mem_filter] at h15
      exact h15.2
    let g : Point2 × ℝ → ℝ := fun x => |inner ℝ p x.1 - x.2|
    have hg_cont : Continuous g :=
      continuous_abs.comp <|
        ((innerSL ℝ p).continuous.comp continuous_fst).sub continuous_snd
    have h16 : Filter.Tendsto (fun n : ℕ => (normal (ψ (φ n)), t (ψ (φ n))))
        Filter.atTop (nhds p_lim) :=
      h_conv.comp hφ_strict.tendsto_atTop
    have h17 : Filter.Tendsto (fun n : ℕ => g (normal (ψ (φ n)), t (ψ (φ n))))
        Filter.atTop (nhds (g p_lim)) :=
      Filter.Tendsto.comp (hg_cont.tendsto p_lim) h16
    have h18 : g p_lim = |inner ℝ p normal_lim - t_lim| := by rfl
    rw [h18] at h17
    exact le_of_tendsto_of_tendsto h17 h10 (Filter.Eventually.of_forall h14)

  have hE'_subset_E : E' ⊆ E := Finset.mem_powerset.mp hE'_in
  have h18 : E' ⊆ E.filter fun p => |inner ℝ p normal_lim - t_lim| ≤ w₀ := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨hE'_subset_E hp, h13 p hp⟩
  have h21 : (E'.card : ℝ) ≤ (count normal_lim t_lim w₀ : ℝ) := by
    exact_mod_cast Finset.card_le_card h18
  have h22 : (c * Real.rpow w₀ ζ * N : ℝ) ≤ (count normal_lim t_lim w₀ : ℝ) := by
    exact_mod_cast le_trans h11 h21

  -- w₀ ∈ W
  have hw₀_in_W : w₀ ∈ W :=
    ⟨hw₀_bdd, normal_lim, t_lim, hK_lim1, hK_lim2.1, hK_lim2.2, h22⟩
  have hw₀_min : ∀ w ∈ W, w₀ ≤ w := fun w hw => csInf_le h_bdd hw

  set normal₀ := normal_lim with hnormal₀_def
  set t₀ := t_lim with ht₀_def
  have hnormal₀ : ‖normal₀‖ = 1 := hK_lim1
  have hcount₀ : (c * Real.rpow w₀ ζ * N : ℝ) ≤ count normal₀ t₀ w₀ := h22
  have h_rpow0_pos : 0 < Real.rpow w₀ ζ := Real.rpow_pos_of_pos h_pos0 ζ
  have h_count_pos : 0 < (count normal₀ t₀ w₀ : ℝ) := by
    have h_pos : 0 < c * Real.rpow w₀ ζ * (N : ℝ) :=
      mul_pos (mul_pos hc h_rpow0_pos) (by exact_mod_cast hN_pos)
    linarith [hcount₀]

  have h_nonconc : ∀ (normal' : Point2) (t' : ℝ) (r : ℝ),
      ‖normal'‖ = 1 → δ ≤ r → r ≤ w₀ →
      (E.filter fun p =>
        |inner ℝ p normal₀ - t₀| ≤ w₀ ∧
        |inner ℝ p normal' - t'| ≤ r).card ≤
      Real.rpow (r / w₀) ζ * count normal₀ t₀ w₀ := by
    intro normal' t' r hnormal' hrδ hr_le
    by_cases h_eq : r = w₀
    · rw [h_eq]
      have h_sub : (E.filter fun p =>
          |inner ℝ p normal₀ - t₀| ≤ w₀ ∧
          |inner ℝ p normal' - t'| ≤ w₀) ⊆
          E.filter fun p => |inner ℝ p normal₀ - t₀| ≤ w₀ := by
        intro p hp
        have h2 := (Finset.mem_filter.mp hp).2
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, h2.1⟩
      have h3 : Real.rpow (w₀ / w₀) ζ = 1 := by
        have h4 : w₀ / w₀ = 1 := by field_simp [show (w₀ : ℝ) ≠ 0 by linarith]
        rw [h4] <;> simp
      rw [h3]
      simpa [mul_one] using Finset.card_le_card h_sub
    · have h_lt : r < w₀ := lt_of_le_of_ne hr_le h_eq
      by_contra h
      push Not at h
      let E'' := E.filter fun p =>
        |inner ℝ p normal₀ - t₀| ≤ w₀ ∧ |inner ℝ p normal' - t'| ≤ r
      have hE''_pos : 0 < E''.card := by
        have hr_pos : 0 < r := lt_of_lt_of_le hδ hrδ
        have hpos1 : 0 < r / w₀ := div_pos hr_pos h_pos0
        have hpos2 : 0 < Real.rpow (r / w₀) ζ := Real.rpow_pos_of_pos hpos1 ζ
        have hpos3 : 0 < (count normal₀ t₀ w₀ : ℝ) := h_count_pos
        have hpos4 : 0 < Real.rpow (r / w₀) ζ * (count normal₀ t₀ w₀ : ℝ) := mul_pos hpos2 hpos3
        have h5 : (Real.rpow (r / w₀) ζ * count normal₀ t₀ w₀ : ℝ) < (E''.card : ℝ) := by
          exact_mod_cast h
        have h6 : 0 < (E''.card : ℝ) := by linarith
        have h_ne_zero : E''.card ≠ 0 := by
          intro h
          have h10 : (E''.card : ℝ) = 0 := by
            rw [h] <;> norm_num
          rw [h10] at h6
          exact lt_irrefl 0 h6
        exact Nat.pos_of_ne_zero h_ne_zero
      have hE''_in_strip : E'' ⊆ E.filter fun p => |inner ℝ p normal' - t'| ≤ r := by
        intro p hp
        have h23 := (Finset.mem_filter.mp hp).2
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, h23.2⟩
      have h_count_r : (E''.card : ℝ) ≤ (count normal' t' r : ℝ) := by
        exact_mod_cast Finset.card_le_card hE''_in_strip
      have h_rpow : Real.rpow r ζ = Real.rpow (r / w₀) ζ * Real.rpow w₀ ζ := by
        have h_r_nonneg : 0 ≤ r := by linarith [hδ, hrδ]
        have h_pos1 : 0 ≤ r / w₀ := div_nonneg h_r_nonneg (by linarith [h_pos0])
        have h_pos2 : 0 ≤ w₀ := by linarith [h_pos0]
        have h : Real.rpow (r / w₀ * w₀) ζ = Real.rpow (r / w₀) ζ * Real.rpow w₀ ζ :=
          Real.mul_rpow h_pos1 h_pos2
        have h2 : r / w₀ * w₀ = r := by
          field_simp [show (w₀ : ℝ) ≠ 0 by linarith] <;> ring
        rw [h2] at h; exact h
      have h_eq1 : c * Real.rpow r ζ * (N : ℝ) =
          Real.rpow (r / w₀) ζ * (c * Real.rpow w₀ ζ * (N : ℝ)) := by
        rw [h_rpow] <;> ring
      have h_main : (c * Real.rpow r ζ * N : ℝ) ≤ (count normal' t' r : ℝ) := by
        rw [h_eq1]
        have h4 : Real.rpow (r / w₀) ζ * (c * Real.rpow w₀ ζ * (N : ℝ)) ≤
            Real.rpow (r / w₀) ζ * (count normal₀ t₀ w₀ : ℝ) :=
          have h_r_nonneg : 0 ≤ r := by linarith [hδ, hrδ]
          have h_w0_nonneg : 0 ≤ w₀ := by linarith [h_pos0]
          have h_div_nonneg : 0 ≤ r / w₀ := div_nonneg h_r_nonneg h_w0_nonneg
          have h_rpow2_nonneg : 0 ≤ Real.rpow (r / w₀) ζ := Real.rpow_nonneg h_div_nonneg ζ
          mul_le_mul_of_nonneg_left hcount₀ h_rpow2_nonneg
        have h5 : Real.rpow (r / w₀) ζ * (count normal₀ t₀ w₀ : ℝ) < (E''.card : ℝ) := by
          exact_mod_cast h
        linarith
      have ht'_range : -2 ≤ t' ∧ t' ≤ 2 := by
        obtain ⟨p, hp⟩ := Finset.card_pos.mp hE''_pos
        have hpin : p ∈ E'' := hp
        have h24 : |inner ℝ p normal' - t'| ≤ r := by
          have h25 := (Finset.mem_filter.mp hpin).2; exact h25.2
        have h26 : p ∈ E := (Finset.mem_filter.mp hpin).1
        have h27 : ‖p‖ ≤ 1 := by simpa [dist_eq_norm] using hE_ball p h26
        have h29 : |inner ℝ p normal'| ≤ ‖p‖ * ‖normal'‖ := abs_real_inner_le_norm p normal'
        rw [hnormal'] at h29
        have h30 : |inner ℝ p normal'| ≤ 1 := by linarith
        have h31 : |t'| ≤ |inner ℝ p normal'| + |inner ℝ p normal' - t'| := by
          calc |t'| = |inner ℝ p normal' - (inner ℝ p normal' - t')| := by ring_nf
            _ ≤ |inner ℝ p normal'| + |inner ℝ p normal' - t'| := by exact abs_sub _ _
        have h32 : |t'| ≤ 1 + r := by linarith
        have h33 : r ≤ 1 := by linarith [hw₀_le_one]
        constructor <;> linarith [abs_le.mp h32]
      have hr_in_W : r ∈ W := by
        refine ⟨hrδ, normal', t', hnormal', ht'_range.1, ht'_range.2, ?_⟩
        exact_mod_cast h_main
      have h_not_le : ¬ w₀ ≤ r := by linarith
      exact h_not_le (hw₀_min r hr_in_W)

  refine ⟨normal₀, t₀, w₀, hnormal₀, hw₀_bdd, hw₀_le_one, hcount₀, h_nonconc⟩

end Kakeya.Assouad
