module

/-
  Tube Capacity Pruning — Main theorem.

  Builds on TubeCapacityPruningCore and Bridge_SSetTransfer to prove
  dyadicTube_capacity_pruning: existence of a capacity-respecting subset
  with cardinality bounds and S-set inheritance.

  Whiteprint node: dyadic_tube_pruning
  Dependencies: TubeCapacityPruningCore, Bridge_SSetTransfer
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.TubeCapacityPruningCore
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge_SSetTransfer
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.FrontEndLemmas

open DirecretisedFurstenbergEstimate

/-! ### Main theorem -/

/-- Tube capacity pruning main theorem with explicit constants. -/
theorem dyadicTube_capacity_pruning
    {n : ℕ} {s C : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (δ_n : ℝ) (hδn_pos : 0 < δ_n) (hδn_lt_one : δ_n < 1)
    (hδn_eq : δ_n = dyadicDelta n)
    (rawTubes : Finset (DyadicTube n))
    (hraw_sset : IsDeltaSSet δ_n s C (rawTubes : Set (DyadicTube n)))
    (hraw_slope : ∀ U ∈ rawTubes, |U.slope| ≤ 3 / 2)
    (hraw_intercept : ∀ U ∈ rawTubes, |U.intercept| ≤ 3) :
    ∃ (normalized : Finset (DyadicTube n)),
      normalized ⊆ rawTubes ∧
      (normalized.card : ℝ) ≤ (28 : ℝ) * δ_n^(-s) ∧
      (normalized.card : ℝ) ≥ (1 / (C * (2 : ℝ)^(s + 1))) * δ_n^(-s) ∧
      IsDeltaSSet δ_n s ((125 : ℝ) * (2 : ℝ)^(s + 1) * C) (normalized : Set (DyadicTube n)) := by
  rcases exists_maximal_tube_capacity_respecting rawTubes hs_pos with
    ⟨S', hS'_sub, hS'_cap, hS'_max⟩
  let cover := halfCapCoverTubes s S'
  let f : SomeDyadicTube → Finset (DyadicTube n) := fun Q =>
    S'.filter (fun T => T ∈ descendantSet n Q)
  have hδ_n_pos : 0 < δ_n := hδn_pos
  have hC_pos : 0 < C := hraw_sset.2.2.1
  have hS_slope : ∀ U ∈ S', |U.slope| ≤ 3 / 2 :=
    fun U hU => hraw_slope U (hS'_sub hU)
  have hS_intercept : ∀ U ∈ S', |U.intercept| ≤ 3 :=
    fun U hU => hraw_intercept U (hS'_sub hU)
  have h_upper : (S'.card : ℝ) ≤ (28 : ℝ) * δ_n^(-s) :=
    capacity_respecting_upper_bound hS'_cap hS_slope hS_intercept δ_n hδn_pos hδn_eq
  -- Cover covers all rawTubes
  have h_covers_raw : ∀ (t : DyadicTube n), t ∈ rawTubes →
      ∃ (Q : SomeDyadicTube), Q ∈ cover ∧ t ∈ descendantSet n Q :=
    halfCapCoverTubes_covers_all hs_pos hS'_sub hS'_cap hS'_max hraw_slope hraw_intercept
  -- Helper: extract level bound from cover membership
  have h_level_le : ∀ (Q : SomeDyadicTube), Q ∈ cover → Q.level ≤ n := by
    intro Q hQ
    rcases Finset.mem_biUnion.mp hQ with ⟨A, _, hQ'⟩
    exact halfCapCoverTube_level_le hQ'
  -- Each cover element has ≥ half capacity
  have h_each_cap : ∀ (Q : SomeDyadicTube), Q ∈ cover →
      ((f Q).card : ℝ) ≥ (dyadicTubeCap n Q.level s) / 2 := by
    intro Q hQ
    have hlev : Q.level ≤ n := h_level_le Q hQ
    have h1 : f Q = tubesInCube hlev Q.tube S' := by
      ext T
      simp only [f, Finset.mem_filter, descendantSet, tubesInCube]
      rw [dif_pos hlev] <;> simp [hlev] <;> tauto
    rw [h1]
    rcases Finset.mem_biUnion.mp hQ with ⟨A, _, hQ'⟩
    exact halfCapCover_half_cap_general hQ'
  -- Descendant sets are pairwise disjoint
  have h_disj : ∀ Q1 ∈ cover, ∀ Q2 ∈ cover, Q1 ≠ Q2 → Disjoint (f Q1) (f Q2) := by
    intro Q1 hQ1 Q2 hQ2 hne
    have h : Disjoint (descendantSet n Q1) (descendantSet n Q2) :=
      halfCapCoverTubes_disjoint hQ1 hQ2 hne
    rw [Finset.disjoint_left]
    intro T hT1 hT2
    have h4 : T ∈ descendantSet n Q1 := (Finset.mem_filter.mp hT1).2
    have h5 : T ∈ descendantSet n Q2 := (Finset.mem_filter.mp hT2).2
    exact Set.disjoint_left.mp h h4 h5
  -- Cover partitions S'
  have h_cover_S' : S' = cover.biUnion f := by
    ext T
    simp only [f, Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · intro hT
      rcases h_covers_raw T (hS'_sub hT) with ⟨Q, hQ, hdesc⟩
      exact ⟨Q, hQ, hT, hdesc⟩
    · rintro ⟨Q, hQ, hT, _⟩
      exact hT
  have h_part : S'.card = ∑ Q ∈ cover, (f Q).card := by
    have h : (cover.biUnion f).card = ∑ Q ∈ cover, (f Q).card :=
      Finset.card_biUnion h_disj
    rw [h_cover_S']
    exact h
  -- Lower bound from sum of capacities
  have h_sum_lower : ∑ Q ∈ cover, ((f Q).card : ℝ) ≥
      ∑ Q ∈ cover, (dyadicTubeCap n Q.level s) / 2 :=
    Finset.sum_le_sum (fun Q hQ => h_each_cap Q hQ)
  have h_half : ∑ Q ∈ cover, (dyadicTubeCap n Q.level s) / 2 =
      (1 / 2 : ℝ) * ∑ Q ∈ cover, dyadicTubeCap n Q.level s := by
    rw [Finset.mul_sum] <;> ring_nf
  have h_lower_sum : (S'.card : ℝ) ≥
      (1 / 2 : ℝ) * ∑ Q ∈ cover, dyadicTubeCap n Q.level s := by
    rw [h_part]
    rw [h_half] at h_sum_lower
    exact_mod_cast h_sum_lower
  -- Choose center for each cover element
  have h_center_exists : ∀ (Q : SomeDyadicTube), Q ∈ cover →
      ∃ (c : DyadicTube n), c ∈ S' ∧ c ∈ descendantSet n Q := by
    intro Q hQ
    have h1 : ((f Q).card : ℝ) ≥ (dyadicTubeCap n Q.level s) / 2 := h_each_cap Q hQ
    have h3 : dyadicTubeCap n Q.level s ≥ 1 :=
      dyadicTubeCap_one_le hs_pos (h_level_le Q hQ)
    have h41 : ((f Q).card : ℝ) ≥ 1 / 2 := by linarith [h1, h3]
    have h4 : (f Q).card ≥ 1 := by
      by_contra h45
      have h46 : (f Q).card = 0 := by omega
      rw [h46] at h41
      norm_num at h41
    rcases Finset.card_pos.mp h4 with ⟨c, hc⟩
    exact ⟨c, (Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2⟩
  choose c hc1 hc2 using h_center_exists
  -- Each descendant set is in a ball
  have h_ball : ∀ (Q : SomeDyadicTube), Q ∈ cover →
      ∃ (center : DyadicTube n), descendantSet n Q ⊆ Metric.closedBall center (2 * dyadicDelta Q.level) := by
    intro Q hQ
    let center := c Q hQ
    refine' ⟨center, _⟩
    intro T hT
    have h3 : Q.level ≤ n := h_level_le Q hQ
    have h4 : dyadicTubeAncestor Q.level h3 T = Q.tube := by
      simpa [descendantSet, h3] using hT
    have h5 : dyadicTubeAncestor Q.level h3 center = Q.tube := by
      simpa [descendantSet, h3] using hc2 Q hQ
    have h6 : T.dist center < 2 * dyadicDelta Q.level :=
      same_ancestor_dist_lt h3 T center (by rw [h4, h5])
    exact h6.le
  have hr_geδ : ∀ (Q : SomeDyadicTube), Q ∈ cover → δ_n ≤ 2 * dyadicDelta Q.level := by
    intro Q hQ
    have h3 : Q.level ≤ n := h_level_le Q hQ
    have h4 : dyadicDelta Q.level ≥ dyadicDelta n := by
      have h5 : (2 : ℝ)^(Q.level) ≤ (2 : ℝ)^n := by gcongr <;> norm_num
      have h6 : 1 / (2 : ℝ)^(Q.level) ≥ 1 / (2 : ℝ)^n :=
        one_div_le_one_div_of_le (by positivity) h5
      simpa [dyadicDelta] using h6
    have h7 : dyadicDelta n = δ_n := hδn_eq.symm
    rw [h7] at h4
    linarith
  have hr_nonneg : ∀ (Q : SomeDyadicTube), Q ∈ cover → 0 ≤ 2 * dyadicDelta Q.level := by
    intro Q _
    have h : 0 < dyadicDelta Q.level := dyadicDelta_pos Q.level
    linarith
  have hcover_set : (rawTubes : Set (DyadicTube n)) ⊆ ⋃ Q ∈ cover, descendantSet n Q := by
    intro t ht
    rcases h_covers_raw t ht with ⟨Q, hQ, hdesc⟩
    exact Set.mem_iUnion₂.mpr ⟨Q, hQ, hdesc⟩
  have hP_fin : (rawTubes : Set (DyadicTube n)).Finite := by exact Finset.finite_toSet rawTubes
  -- S-set cancellation
  have h_cancel : (1 : ℝ) ≤ C * ∑ Q ∈ cover, (2 * dyadicDelta Q.level)^s :=
    sset_cover_sum_radii_bound_tubes hraw_sset hP_fin hδn_pos hs_pos
      cover (fun Q => descendantSet n Q) (fun Q => 2 * dyadicDelta Q.level)
      hcover_set hr_geδ hr_nonneg h_ball
  -- Sum conversion
  have h_sum_conv : ∑ Q ∈ cover, (2 * dyadicDelta Q.level)^s =
      (2 : ℝ)^s * (δ_n)^s * ∑ Q ∈ cover, dyadicTubeCap n Q.level s := by
    have h1 : ∀ Q ∈ cover, (2 * dyadicDelta Q.level)^s =
        (2 : ℝ)^s * (δ_n)^s * dyadicTubeCap n Q.level s := by
      intro Q hQ
      have h3 : Q.level ≤ n := h_level_le Q hQ
      have h_cap : dyadicTubeCap n Q.level s = (dyadicDelta Q.level / dyadicDelta n) ^ s := by
        simp [dyadicTubeCap]
      have hδn : dyadicDelta n = δ_n := hδn_eq.symm
      rw [h_cap, hδn]
      have h_pos1 : 0 < (2 : ℝ) := by norm_num
      have h_pos2 : 0 < dyadicDelta Q.level := dyadicDelta_pos Q.level
      have h_pos3 : 0 < δ_n := hδn_pos
      have h_eq1 : (2 * dyadicDelta Q.level)^s = (2 : ℝ)^s * (dyadicDelta Q.level)^s := by
        rw [← Real.mul_rpow (by norm_num) (by positivity)] <;> ring
      rw [h_eq1]
      have h_eq2 : (dyadicDelta Q.level)^s = (δ_n)^s * (dyadicDelta Q.level / δ_n)^s := by
        have h : (δ_n)^s * (dyadicDelta Q.level / δ_n)^s = (dyadicDelta Q.level)^s := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          <;> field_simp [h_pos3.ne'] <;> ring
        exact h.symm
      rw [h_eq2] <;> ring
    have h_sum : ∑ Q ∈ cover, (2 * dyadicDelta Q.level)^s =
        ∑ Q ∈ cover, ((2 : ℝ)^s * (δ_n)^s * dyadicTubeCap n Q.level s) :=
      Finset.sum_congr rfl h1
    rw [h_sum]
    have h_final : ∑ Q ∈ cover, ((2 : ℝ)^s * (δ_n)^s * dyadicTubeCap n Q.level s) =
        (2 : ℝ)^s * (δ_n)^s * ∑ Q ∈ cover, dyadicTubeCap n Q.level s := by
      rw [Finset.mul_sum]
      <;> rw [Finset.mul_sum] <;> ring
    exact h_final
  rw [h_sum_conv] at h_cancel
  have h_pos_prod : 0 < C * (2 : ℝ)^s * (δ_n)^s := by positivity
  have h_mul : (1 : ℝ) ≤ (C * (2 : ℝ)^s * (δ_n)^s) * ∑ Q ∈ cover, dyadicTubeCap n Q.level s := by
    simpa [mul_assoc] using h_cancel
  have h_sum_cap : ∑ Q ∈ cover, dyadicTubeCap n Q.level s ≥
      1 / (C * (2 : ℝ)^s * (δ_n)^s) := by
    have h_pos : 0 < C * (2 : ℝ)^s * (δ_n)^s := h_pos_prod
    have h_div : ((C * (2 : ℝ)^s * (δ_n)^s) * ∑ Q ∈ cover, dyadicTubeCap n Q.level s) / (C * (2 : ℝ)^s * (δ_n)^s) =
        ∑ Q ∈ cover, dyadicTubeCap n Q.level s := by
      field_simp [h_pos.ne'] <;> ring
    have h_ge : ((C * (2 : ℝ)^s * (δ_n)^s) * ∑ Q ∈ cover, dyadicTubeCap n Q.level s) / (C * (2 : ℝ)^s * (δ_n)^s) ≥
        1 / (C * (2 : ℝ)^s * (δ_n)^s) := by gcongr
    rw [h_div] at h_ge
    exact h_ge
  have h_lower : (S'.card : ℝ) ≥ (1 / (C * (2 : ℝ)^(s+1))) * (δ_n)^(-s) := by
    have h1 : (1 / 2 : ℝ) * ∑ Q ∈ cover, dyadicTubeCap n Q.level s ≥
        (1 / 2 : ℝ) * (1 / (C * (2 : ℝ)^s * (δ_n)^s)) := by gcongr
    have h2 : (1 / 2 : ℝ) * (1 / (C * (2 : ℝ)^s * (δ_n)^s)) =
        (1 / (C * (2 : ℝ)^(s+1))) * (δ_n)^(-s) := by
      have h3 : (δ_n)^(-s) = 1 / (δ_n)^s := by
        rw [Real.rpow_neg hδn_pos.le] <;> ring
      rw [h3]
      have h4 : (2 : ℝ)^(s+1) = 2 * (2 : ℝ)^s := by
        have h5 : (2 : ℝ)^(s+1) = (2 : ℝ)^s * (2 : ℝ)^1 := by
          rw [Real.rpow_add (by norm_num)] <;> ring
        rw [h5]
        have h6 : (2 : ℝ)^1 = 2 := by norm_num
        rw [h6] <;> ring
      rw [h4]
      field_simp [h_pos_prod.ne', hδn_pos.ne']
    rw [h2] at h1
    linarith [h_lower_sum]
  --! S-set property for S'
  have h_raw_nonempty : (rawTubes : Set (DyadicTube n)).Nonempty := hraw_sset.1
  have hraw_cover : ∀ (x : DyadicTube n) (r : ℝ), δ_n ≤ r →
      Metric.externalCoveringNumber (δ_n).toNNReal ((rawTubes : Set (DyadicTube n)) ∩ Metric.closedBall x r) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r)^s * Metric.externalCoveringNumber (δ_n).toNNReal (rawTubes : Set (DyadicTube n)) :=
    hraw_sset.2.2.2.2
  have hS'_nonempty : S'.Nonempty := by
    by_contra h
    have h_empty : S' = ∅ := by simpa using h
    rcases h_raw_nonempty with ⟨t, ht⟩
    rcases hS'_max t ht (by rw [h_empty] <;> simp) with ⟨j, hj, A, hanc, hsat⟩
    have h_cap1 : 1 ≤ dyadicTubeCap n j s := dyadicTubeCap_one_le hs_pos hj
    have hsat' : (tubesInCube hj A (∅ : Finset (DyadicTube n))).card = Nat.floor (dyadicTubeCap n j s) := by
      simpa [h_empty, tubesInCube] using hsat
    have h_zero : (tubesInCube hj A (∅ : Finset (DyadicTube n))).card = 0 := by
      simp [tubesInCube]
    have h_floor_pos : 0 < Nat.floor (dyadicTubeCap n j s) := by
      have h5 : 1 ≤ dyadicTubeCap n j s := h_cap1
      have h6 : (1 : ℕ) ≤ Nat.floor (dyadicTubeCap n j s) := by
        have h5' : (1 : ℝ) ≤ dyadicTubeCap n j s := by exact_mod_cast h5
        have h_pos : 0 ≤ dyadicTubeCap n j s := by linarith
        rw [Nat.le_floor_iff h_pos]
        exact_mod_cast h5'
      omega
    have h_contra : Nat.floor (dyadicTubeCap n j s) = 0 := by
      have h7 : (tubesInCube hj A (∅ : Finset (DyadicTube n))).card = Nat.floor (dyadicTubeCap n j s) := hsat'
      rw [h_zero] at h7
      exact h7.symm
    omega
  -- Lower bound on C from raw S-set diameter
  have hC_lower : C ≥ (9 : ℝ)^(-s) := by
    rcases h_raw_nonempty with ⟨x, hx⟩
    have h_diam : ∀ T ∈ rawTubes, T.dist x ≤ 9 := by
      intro T hT
      have h1 : |T.slope - x.slope| ≤ 3 := by
        have h2 : |T.slope| ≤ 3 / 2 := hraw_slope T hT
        have h3 : |x.slope| ≤ 3 / 2 := hraw_slope x hx
        calc |T.slope - x.slope| ≤ |T.slope| + |x.slope| := by exact real_abs_sub T.slope x.slope
          _ ≤ 3 / 2 + 3 / 2 := by linarith
          _ = 3 := by norm_num
      have h4 : |T.intercept - x.intercept| ≤ 6 := by
        have h5 : |T.intercept| ≤ 3 := hraw_intercept T hT
        have h6 : |x.intercept| ≤ 3 := hraw_intercept x hx
        calc |T.intercept - x.intercept| ≤ |T.intercept| + |x.intercept| := by exact real_abs_sub T.intercept x.intercept
          _ ≤ 3 + 3 := by linarith
          _ = 6 := by norm_num
      have h7 : T.dist x = |T.slope - x.slope| + |T.intercept - x.intercept| := by rfl
      rw [h7] <;> linarith
    have h_ball9 : (rawTubes : Set (DyadicTube n)) ⊆ Metric.closedBall x (9 : ℝ) := by
      intro T hT
      exact h_diam T hT
    have h9 : δ_n ≤ (9 : ℝ) := by linarith [hδn_lt_one]
    have h10 := hraw_cover x (9 : ℝ) h9
    have h11 : (rawTubes : Set (DyadicTube n)) ∩ Metric.closedBall x (9 : ℝ) = (rawTubes : Set (DyadicTube n)) := by
      rw [Set.inter_eq_left.mpr h_ball9]
    rw [h11] at h10
    let n_enat := Metric.externalCoveringNumber (δ_n).toNNReal (rawTubes : Set (DyadicTube n))
    have hn_enat_pos : 0 < n_enat := Metric.externalCoveringNumber_pos_iff.mpr ⟨x, hx⟩
    have hn_enat_lt_top : n_enat < ⊤ := by
      have h_le : n_enat ≤ (rawTubes : Set (DyadicTube n)).encard :=
        Metric.externalCoveringNumber_le_encard_self (rawTubes : Set (DyadicTube n))
      exact lt_of_le_of_lt h_le hP_fin.encard_lt_top
    let a : ENNReal := ↑n_enat
    have ha0 : a ≠ 0 := by
      intro h
      have h_coe : (↑n_enat : ENNReal) = 0 := by simpa [a] using h
      have h_n_enat_eq_zero : n_enat = 0 := by
        cases h : n_enat with
        | top =>
          have h1 : (↑n_enat : ENNReal) = (⊤ : ENNReal) := by
            rw [h] <;> simp
          rw [h1] at h_coe
          exact False.elim (ENNReal.top_ne_zero h_coe)
        | coe n =>
          have h1 : (↑n_enat : ENNReal) = (↑n : ENNReal) := by
            rw [h] <;> simp
          rw [h1] at h_coe
          have h2 : (↑n : ENNReal) = 0 := h_coe
          have h3 : n = 0 := by
            rw [Nat.cast_eq_zero] at h2
            exact h2
          rw [h3] <;> simp
      exact hn_enat_pos.ne' h_n_enat_eq_zero
    have ha_top : a ≠ ⊤ := by
      intro h
      have h9 : a = ↑n_enat := by rfl
      rw [h9] at h
      have h10 : n_enat = ⊤ := ENat.map_eq_top_iff.mp h
      exact hn_enat_lt_top.ne h10
    let b : ENNReal := ENNReal.ofReal C * (ENNReal.ofReal (9 : ℝ)) ^ s
    have h12 : a ≤ b * a := h10
    have h13 : (1 : ENNReal) ≤ b := by
      have h14 : a / a ≤ (b * a) / a := by gcongr
      have h15 : a / a = 1 := by
        have h : a * a⁻¹ = 1 := ENNReal.mul_inv_cancel ha0 ha_top
        have h2 : a / a = a * a⁻¹ := by simp [div_eq_mul_inv]
        rw [h2, h]
      have h16 : (b * a) / a = b := by
        have h : (b * a) * a⁻¹ = b := by
          calc (b * a) * a⁻¹
            = b * (a * a⁻¹) := by ring
          _ = b * 1 := by rw [ENNReal.mul_inv_cancel ha0 ha_top]
          _ = b := by ring
        have h2 : (b * a) / a = (b * a) * a⁻¹ := by simp [div_eq_mul_inv]
        rw [h2, h]
      rw [h15, h16] at h14
      exact h14
    have hb_lt_top : b ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · exact ENNReal.ofReal_ne_top
      · exact ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
    have h20 : (1 : ℝ) ≤ C * (9 : ℝ)^s := by
      have h13' : (1 : ℝ) ≤ b.toReal := by
        have h' : (1 : ENNReal).toReal ≤ b.toReal :=
          (ENNReal.toReal_le_toReal (by simp) hb_lt_top).mpr h13
        simpa using h'
      have h_b_toReal : b.toReal = C * (9 : ℝ)^s := by
        have h1 : b.toReal = (ENNReal.ofReal C).toReal * ((ENNReal.ofReal (9 : ℝ)) ^ s).toReal := by
          simp [b] <;> rfl
        rw [h1]
        have hC_nonneg : 0 ≤ C := by linarith
        have h2a : (ENNReal.ofReal C).toReal = C := by
          rw [ENNReal.toReal_ofReal hC_nonneg]
        have h2 : ((ENNReal.ofReal (9 : ℝ)) ^ s).toReal = (9 : ℝ)^s := by
          rw [← ENNReal.toReal_rpow] <;> simp
        rw [h2a, h2] <;> ring
      rw [h_b_toReal] at h13'
      exact h13'
    have h21 : (9 : ℝ)^s > 0 := by positivity
    have h22 : C ≥ 1 / (9 : ℝ)^s := by
      have h23 : C * (9 : ℝ)^s ≥ 1 := h20
      have h24 : (C * (9 : ℝ)^s) / (9 : ℝ)^s ≥ 1 / (9 : ℝ)^s := by
        apply div_le_div_of_nonneg_right h23
        positivity
      have h25 : C = (C * (9 : ℝ)^s) / (9 : ℝ)^s := by field_simp [h21.ne'] <;> ring
      rw [h25]
      exact h24
    have h24 : (9 : ℝ)^(-s) = 1 / (9 : ℝ)^s := by
      rw [Real.rpow_neg (by norm_num)] <;> ring
    rw [h24]
    exact h22
  set C' := (125 : ℝ) * (2 : ℝ)^(s + 1) * C with hC'_def
  have hC'_pos : 0 < C' := by positivity
  have hC'_gt_one : (1 : ℝ) < C' := by
    have h1 : C ≥ (9 : ℝ)^(-s) := hC_lower
    have h2 : C' ≥ (125 : ℝ) * (2 : ℝ)^(s + 1) * (9 : ℝ)^(-s) := by
      rw [hC'_def] <;> gcongr
    have h3 : (125 : ℝ) * (2 : ℝ)^(s + 1) * (9 : ℝ)^(-s) = (250 : ℝ) * ((2 : ℝ) / 9)^s := by
      have h41 : (9 : ℝ)^(-s) = ((9 : ℝ)⁻¹)^s := by
        have h_pos : (0 : ℝ) < 9 := by norm_num
        have h1 : (9 : ℝ)^(-s) = ((9 : ℝ)^s)⁻¹ := Real.rpow_neg (by positivity) s
        have h2 : ((9 : ℝ)⁻¹)^s = ((9 : ℝ)^s)⁻¹ := by
          have h3 : (9 : ℝ)⁻¹ = 1 / (9 : ℝ) := by norm_num
          rw [h3]
          have h4 : (1 / (9 : ℝ))^s = 1 / (9 : ℝ)^s := by
            rw [Real.div_rpow (by norm_num) (by positivity)] <;> norm_num
          rw [h4] <;> field_simp
        rw [h1, h2]
      have h42 : (2 : ℝ)^(s + 1) = 2 * (2 : ℝ)^s := by
        have h : (2 : ℝ)^(s + 1) = (2 : ℝ)^s * (2 : ℝ)^(1 : ℝ) :=
          Real.rpow_add (by norm_num) s 1
        have h2 : (2 : ℝ)^(1 : ℝ) = 2 := by simp
        rw [h, h2] <;> ring
      rw [h41, h42]
      have h43 : ((2 : ℝ) * (9 : ℝ)⁻¹)^s = (2 : ℝ)^s * ((9 : ℝ)⁻¹)^s := by
        rw [← Real.mul_rpow (by norm_num) (by positivity)]
      have h44 : (2 : ℝ) / 9 = (2 : ℝ) * (9 : ℝ)⁻¹ := by ring
      have h_goal : (125 : ℝ) * (2 * (2 : ℝ)^s) * ((9 : ℝ)⁻¹)^s =
          (250 : ℝ) * ((2 : ℝ) / 9)^s := by
        rw [h44, h43] <;> ring
      exact h_goal
    rw [h3] at h2
    have h6 : (2 : ℝ) / 9 < 1 := by norm_num
    have h7 : ((2 : ℝ) / 9)^s > (2 : ℝ) / 9 := by
      have h_base_pos : (0 : ℝ) < (2 : ℝ) / 9 := by norm_num
      have h : ((2 : ℝ) / 9)^(1 : ℝ) < ((2 : ℝ) / 9)^s :=
        Real.rpow_lt_rpow_of_exponent_gt (by norm_num) h6 hs_lt_one
      simpa using h
    have h8 : (250 : ℝ) * ((2 : ℝ) / 9)^s > (250 : ℝ) * ((2 : ℝ) / 9) :=
      mul_lt_mul_of_pos_left h7 (by norm_num)
    have h9 : (250 : ℝ) * ((2 : ℝ) / 9) > 1 := by norm_num
    linarith
  -- Global: card ≤ 5 * Ncover
  have h_card_cover : (S' : Set (DyadicTube n)).encard ≤
      5 * Metric.externalCoveringNumber (δ_n).toNNReal (S' : Set (DyadicTube n)) := by
    have h := DiscretisedFurstenbergEstimate.InductionOnScales.card_le_five_cover S'
    have h' : (S' : Set (DyadicTube n)).encard ≤
        5 * Metric.externalCoveringNumber (dyadicDelta n).toNNReal (S' : Set (DyadicTube n)) := h
    have hδ : (dyadicDelta n).toNNReal = (δ_n).toNNReal := by
      congr
      <;> exact hδn_eq.symm
    rw [hδ] at h'
    exact h'
  have h_encard_card : (S' : Set (DyadicTube n)).encard = ↑(S'.card) := by simp
  -- S-set proof
  have h_sset : IsDeltaSSet δ_n s C' (S' : Set (DyadicTube n)) := by
    refine' ⟨hS'_nonempty, hδn_pos, hC'_pos, by linarith, _⟩
    intro x r hr
    by_cases h_rge1 : (1 : ℝ) ≤ r
    · -- Case r ≥ 1
      have h1 : Metric.externalCoveringNumber (δ_n).toNNReal ((S' : Set (DyadicTube n)) ∩ Metric.closedBall x r) ≤
          Metric.externalCoveringNumber (δ_n).toNNReal (S' : Set (DyadicTube n)) :=
        Metric.externalCoveringNumber_mono_set (by simp)
      have hC'_one : (1 : ℝ) ≤ C' := by linarith
      have hr_s_one : (1 : ℝ) ≤ r^s := Real.one_le_rpow h_rge1 (by linarith)
      have h3 : (1 : ℝ) ≤ C' * r^s := by
        calc 1
          = 1 * 1 := by ring
        _ ≤ C' * r^s := mul_le_mul hC'_one hr_s_one (by positivity) (by positivity)
      have h2 : (1 : ENNReal) ≤ ENNReal.ofReal (C' * r^s) := by
        have h2' : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (C' * r^s) := ENNReal.ofReal_le_ofReal h3
        have h_one : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
        rw [h_one] at h2'
        exact h2'
      have h_eq_C' : ENNReal.ofReal (C' * r^s) = ENNReal.ofReal C' * (ENNReal.ofReal r)^s := by
        have h_posC' : 0 ≤ C' := by positivity
        have h_mul : ENNReal.ofReal (C' * r^s) = ENNReal.ofReal C' * ENNReal.ofReal (r^s) :=
          @ENNReal.ofReal_mul C' (r^s) h_posC'
        have h_rpow : ENNReal.ofReal (r^s) = (ENNReal.ofReal r)^s :=
          (ENNReal.ofReal_rpow_of_nonneg (x := r) (p := s) (by linarith) (by linarith)).symm
        rw [h_mul, h_rpow]
      let N : ENNReal := Metric.externalCoveringNumber (δ_n).toNNReal (S' : Set (DyadicTube n))
      have h1' : Metric.externalCoveringNumber (δ_n).toNNReal ((S' : Set (DyadicTube n)) ∩ Metric.closedBall x r) ≤
          Metric.externalCoveringNumber (δ_n).toNNReal (S' : Set (DyadicTube n)) :=
        Metric.externalCoveringNumber_mono_set (by simp)
      have h_local : (Metric.externalCoveringNumber (δ_n).toNNReal ((S' : Set (DyadicTube n)) ∩ Metric.closedBall x r) : ENNReal) ≤ N := by
        dsimp only [N]
        have h_mono : ∀ (a b : ENat), a ≤ b → (↑a : ENNReal) ≤ (↑b : ENNReal) :=
          fun a b h => by simpa using WithTop.coe_mono h
        exact h_mono _ _ h1'
      have h_main : (Metric.externalCoveringNumber (δ_n).toNNReal ((S' : Set (DyadicTube n)) ∩ Metric.closedBall x r) : ENNReal) ≤
          ENNReal.ofReal C' * (ENNReal.ofReal r)^s * N := by
        calc (Metric.externalCoveringNumber (δ_n).toNNReal ((S' : Set (DyadicTube n)) ∩ Metric.closedBall x r) : ENNReal)
          ≤ N := h_local
        _ = (1 : ENNReal) * N := by rw [one_mul]
        _ ≤ ENNReal.ofReal (C' * r^s) * N := by
          exact mul_le_mul_of_nonneg_right h2 (by simp)
        _ = ENNReal.ofReal C' * (ENNReal.ofReal r)^s * N := by rw [h_eq_C']
      exact_mod_cast h_main
    · -- Case δ_n ≤ r < 1
      have h_rlt1 : r < 1 := by linarith
      have hP : ∃ (k : ℕ), dyadicDelta k ≤ r := ⟨n, by linarith [hδn_eq]⟩
      let j := Nat.find hP
      have hj_le : dyadicDelta j ≤ r := (Nat.find_spec hP)
      have hj_min : ∀ m < j, r < dyadicDelta m := by
        intro m hm
        by_contra h
        have h' : dyadicDelta m ≤ r := by linarith
        exact Nat.find_min hP hm h'
      have hj_pos : 0 < j := by
        by_contra h
        have h0 : j = 0 := by omega
        rw [h0] at hj_le
        have h1 : dyadicDelta 0 = 1 := by simp [dyadicDelta] <;> norm_num
        rw [h1] at hj_le
        have h_cont : ¬(1 : ℝ) ≤ r := by linarith
        exact h_cont hj_le
      have h_jn : j ≤ n := by
        by_contra h
        have h2 : n < j := by omega
        have h3 : r < dyadicDelta n := hj_min n h2
        have h4 : dyadicDelta n = δ_n := hδn_eq.symm
        rw [h4] at h3
        linarith
      have h_rlt2δj : r < 2 * dyadicDelta j := by
        have h5 : j - 1 < j := by omega
        have h6 : r < dyadicDelta (j - 1) := hj_min (j - 1) h5
        have h7 : dyadicDelta (j - 1) = 2 * dyadicDelta j := by
          have h_pos : 0 < j := hj_pos
          have h_j_succ : ∃ j' : ℕ, j = j' + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
          rcases h_j_succ with ⟨j', hj_eq⟩
          rw [hj_eq]
          simp [dyadicDelta, pow_succ] <;> field_simp <;> ring
        rw [h7] at h6
        exact h6
      let tubesInBall := S'.filter (fun T => T ∈ Metric.closedBall x r)
      let cubes := tubesInBall.image (fun T => dyadicTubeAncestor j h_jn T)
      have h_cubes_ball : ∀ A ∈ cubes, ∃ (T : DyadicTube n),
          dyadicTubeAncestor j h_jn T = A ∧ T ∈ Metric.closedBall x r := by
        intro A hA
        rcases Finset.mem_image.mp hA with ⟨T, hT, rfl⟩
        exact ⟨T, rfl, (Finset.mem_filter.mp hT).2⟩
      have h_cubes_le25 : cubes.card ≤ 25 :=
        ball_cube_count_le_25 h_jn x r h_rlt2δj cubes h_cubes_ball
      have h_tubes_sub : tubesInBall ⊆ cubes.biUnion (fun A => tubesInCube h_jn A S') := by
        intro T hT
        have hT_inS' : T ∈ S' := (Finset.mem_filter.mp hT).1
        have hT_ball : T ∈ Metric.closedBall x r := (Finset.mem_filter.mp hT).2
        let A := dyadicTubeAncestor j h_jn T
        have hA_in : A ∈ cubes := by
          simp only [cubes, Finset.mem_image]
          exact ⟨T, hT, rfl⟩
        simp only [Finset.mem_biUnion]
        exact ⟨A, hA_in, by simp [tubesInCube, hT_inS'] <;> tauto⟩
      have h_cap_each : ∀ A ∈ cubes, (tubesInCube h_jn A S').card ≤ Nat.floor (dyadicTubeCap n j s) :=
        fun A _ => hS'_cap j h_jn A
      have h_card_le : tubesInBall.card ≤ cubes.card * Nat.floor (dyadicTubeCap n j s) := by
        calc tubesInBall.card
          ≤ (cubes.biUnion (fun A => tubesInCube h_jn A S')).card := Finset.card_le_card h_tubes_sub
        _ ≤ ∑ A ∈ cubes, (tubesInCube h_jn A S').card := Finset.card_biUnion_le
        _ ≤ ∑ A ∈ cubes, Nat.floor (dyadicTubeCap n j s) := Finset.sum_le_sum h_cap_each
        _ = cubes.card * Nat.floor (dyadicTubeCap n j s) := by rw [Finset.sum_const] <;> ring
      have h_cap_pos : 0 ≤ dyadicTubeCap n j s := by
        have h : 1 ≤ dyadicTubeCap n j s := dyadicTubeCap_one_le hs_pos h_jn
        linarith
      have h_floor_le : (Nat.floor (dyadicTubeCap n j s) : ℝ) ≤ dyadicTubeCap n j s :=
        Nat.floor_le h_cap_pos
      have h_cubes_nonneg : 0 ≤ (cubes.card : ℝ) := Nat.cast_nonneg _
      have h1 : (tubesInBall.card : ℝ) ≤ (cubes.card : ℝ) * (dyadicTubeCap n j s) := by
        have h_card_le' : (tubesInBall.card : ℝ) ≤ (cubes.card : ℝ) * (Nat.floor (dyadicTubeCap n j s) : ℝ) := by
          have h : (tubesInBall.card : ℝ) ≤ ↑(cubes.card * Nat.floor (dyadicTubeCap n j s)) := Nat.cast_le.mpr h_card_le
          have h2 : (↑(cubes.card * Nat.floor (dyadicTubeCap n j s)) : ℝ) = (cubes.card : ℝ) * (Nat.floor (dyadicTubeCap n j s) : ℝ) := by
            simp [Nat.cast_mul]
          rw [h2] at h
          exact h
        have h_mul : (cubes.card : ℝ) * (Nat.floor (dyadicTubeCap n j s) : ℝ) ≤ (cubes.card : ℝ) * (dyadicTubeCap n j s) :=
          mul_le_mul_of_nonneg_left h_floor_le h_cubes_nonneg
        exact le_trans h_card_le' h_mul
      have h_cap_eq : dyadicTubeCap n j s = (dyadicDelta j / dyadicDelta n) ^ s := by
        simp [dyadicTubeCap]
      have hδn : dyadicDelta n = δ_n := hδn_eq.symm
      have h1' : (tubesInBall.card : ℝ) ≤ (cubes.card : ℝ) * ((dyadicDelta j / δ_n) ^ s) := by
        rw [h_cap_eq, hδn] at h1
        exact h1
      have h2 : (cubes.card : ℝ) ≤ 25 := Nat.cast_le.mpr h_cubes_le25
      have hδj_pos : 0 < dyadicDelta j := dyadicDelta_pos j
      have h5 : 0 ≤ dyadicDelta j / δ_n := div_nonneg hδj_pos.le hδn_pos.le
      have h6 : dyadicDelta j / δ_n ≤ r / δ_n :=
        div_le_div_of_nonneg_right hj_le hδn_pos.le
      have h4 : (dyadicDelta j / δ_n)^s ≤ (r / δ_n)^s := by
        gcongr <;> linarith
      have h_pow_nonneg : 0 ≤ (dyadicDelta j / δ_n)^s := Real.rpow_nonneg h5 s
      have h2' : (cubes.card : ℝ) * ((dyadicDelta j / δ_n) ^ s) ≤ 25 * ((dyadicDelta j / δ_n) ^ s) :=
        mul_le_mul_of_nonneg_right h2 h_pow_nonneg
      have h3' : 25 * ((dyadicDelta j / δ_n) ^ s) ≤ 25 * (r / δ_n)^s :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
      have h_local_real : (tubesInBall.card : ℝ) ≤ 25 * (r / δ_n)^s := by
        calc (tubesInBall.card : ℝ)
          ≤ (cubes.card : ℝ) * ((dyadicDelta j / δ_n) ^ s) := h1'
        _ ≤ 25 * ((dyadicDelta j / δ_n) ^ s) := h2'
        _ ≤ 25 * (r / δ_n)^s := h3'
      have h_set_eq : (S' : Set (DyadicTube n)) ∩ Metric.closedBall x r = (tubesInBall : Set (DyadicTube n)) := by
        ext T
        simp [tubesInBall, Finset.mem_filter]
        <;> rfl
      have h_ncover_local : Metric.externalCoveringNumber (δ_n).toNNReal ((S' : Set (DyadicTube n)) ∩ Metric.closedBall x r) ≤
          ENNReal.ofReal (25 * (r / δ_n)^s) := by
        rw [h_set_eq]
        have h : Metric.externalCoveringNumber (δ_n).toNNReal (tubesInBall : Set (DyadicTube n)) ≤
            (tubesInBall : Set (DyadicTube n)).encard :=
          Metric.externalCoveringNumber_le_encard_self (A := (tubesInBall : Set (DyadicTube n)))
        have h_encard : (tubesInBall : Set (DyadicTube n)).encard = ↑(tubesInBall.card) := by simp
        have h_enat : Metric.externalCoveringNumber (δ_n).toNNReal (tubesInBall : Set (DyadicTube n)) ≤ ↑(tubesInBall.card) := by
          rw [h_encard] at h
          exact h
        have h_enreal : (Metric.externalCoveringNumber (δ_n).toNNReal (tubesInBall : Set (DyadicTube n)) : ENNReal) ≤ (↑(tubesInBall.card) : ENNReal) := by
          exact_mod_cast h_enat
        have h' : (↑(tubesInBall.card) : ENNReal) = ENNReal.ofReal ((tubesInBall.card : ℝ)) := by simp
        have h_final : (Metric.externalCoveringNumber (δ_n).toNNReal (tubesInBall : Set (DyadicTube n)) : ENNReal) ≤ ENNReal.ofReal ((tubesInBall.card : ℝ)) := by
          rw [h'] at h_enreal
          exact h_enreal
        exact le_trans h_final (ENNReal.ofReal_le_ofReal h_local_real)
      -- Global lower bound on Ncover(S')
      have h_ncover_lower : ENNReal.ofReal (δ_n^(-s) / (5 * C * (2 : ℝ)^(s + 1))) ≤
          Metric.externalCoveringNumber (δ_n).toNNReal (S' : Set (DyadicTube n)) := by
        let Ncover : ENNReal := Metric.externalCoveringNumber (δ_n).toNNReal (S' : Set (DyadicTube n))
        have h1_enat : (S'.card : ℕ∞) ≤ 5 * Metric.externalCoveringNumber (δ_n).toNNReal (S' : Set (DyadicTube n)) := by
          rw [h_encard_card] at h_card_cover
          exact h_card_cover
        have h1 : (↑(S'.card) : ENNReal) ≤ (5 : ENNReal) * Ncover := by
          dsimp only [Ncover]
          exact_mod_cast h1_enat
        set x : ℝ := δ_n^(-s) / (5 * C * (2 : ℝ)^(s + 1)) with hx_def
        set y : ℝ := δ_n^(-s) / (C * (2 : ℝ)^(s + 1)) with hy_def
        have h_posx : 0 ≤ x := by positivity
        have h_posy : 0 ≤ y := by positivity
        have h_arith : (5 : ℝ) * x = y := by
          simp only [hx_def, hy_def]
          field_simp [hC_pos.ne'] <;> ring
        have h_pos5 : 0 ≤ (5 : ℝ) := by norm_num
        have h_eq5 : (5 : ENNReal) * ENNReal.ofReal x = ENNReal.ofReal y := by
          have h_mul : ENNReal.ofReal ((5 : ℝ) * x) = (5 : ENNReal) * ENNReal.ofReal x := by
            have h := ENNReal.ofReal_mul (p := (5 : ℝ)) (q := x) h_pos5
            simpa using h
          have h_arith' : ENNReal.ofReal ((5 : ℝ) * x) = ENNReal.ofReal y := by rw [h_arith]
          rw [←h_mul, h_arith']
        have h_card_coe : (↑(S'.card) : ENNReal) = ENNReal.ofReal ((S'.card : ℝ)) := by simp
        have h_lower2 : ENNReal.ofReal y ≤ (↑(S'.card) : ENNReal) := by
          rw [h_card_coe]
          apply ENNReal.ofReal_le_ofReal
          have h4 : (S'.card : ℝ) ≥ (1 / (C * (2 : ℝ)^(s + 1))) * δ_n^(-s) := h_lower
          have h5 : y = (1 / (C * (2 : ℝ)^(s + 1))) * δ_n^(-s) := by
            simp only [hy_def]
            field_simp [hC_pos.ne'] <;> ring
          rw [h5]
          exact h4
        have h6 : (5 : ENNReal) * ENNReal.ofReal x ≤ (5 : ENNReal) * Ncover := by
          calc (5 : ENNReal) * ENNReal.ofReal x
            = ENNReal.ofReal y := h_eq5
          _ ≤ (↑(S'.card) : ENNReal) := h_lower2
          _ ≤ (5 : ENNReal) * Ncover := h1
        -- Cancel factor of 5 via toReal
        by_cases hN : Ncover = ⊤
        · simpa [Ncover, hN] using le_top
        · have hN_fin : Ncover ≠ ⊤ := hN
          have h5_fin : (5 : ENNReal) * Ncover ≠ ⊤ := by
            have h9 : (5 : ENNReal) ≠ ⊤ := by norm_num
            exact ENNReal.mul_ne_top h9 hN
          have h_toReal : ((5 : ENNReal) * ENNReal.ofReal x).toReal ≤ ((5 : ENNReal) * Ncover).toReal :=
            ENNReal.toReal_mono h5_fin h6
          have h_left : ((5 : ENNReal) * ENNReal.ofReal x).toReal = 5 * x := by
            rw [ENNReal.toReal_mul]
            <;> simp [h_posx] <;> ring
          have h_right : ((5 : ENNReal) * Ncover).toReal = 5 * Ncover.toReal := by
            rw [ENNReal.toReal_mul]
            <;> simp [mul_comm] <;> ring
          rw [h_left, h_right] at h_toReal
          have h_x_le : x ≤ Ncover.toReal := by linarith
          have h7 : ENNReal.ofReal x ≤ ENNReal.ofReal Ncover.toReal := ENNReal.ofReal_le_ofReal h_x_le
          have h8 : ENNReal.ofReal Ncover.toReal ≤ Ncover := ENNReal.ofReal_toReal_le
          exact le_trans h7 h8
      -- Combine
      have h_posC' : 0 ≤ C' := hC'_pos.le
      have h_posr : 0 ≤ r := le_trans hδn_pos.le hr
      have h_eq_C' : ENNReal.ofReal (C' * r^s) = ENNReal.ofReal C' * (ENNReal.ofReal r)^s := by
        have h_mul : ENNReal.ofReal (C' * r^s) = ENNReal.ofReal C' * ENNReal.ofReal (r^s) :=
          ENNReal.ofReal_mul h_posC'
        have h_rpow : ENNReal.ofReal (r^s) = (ENNReal.ofReal r)^s :=
          (ENNReal.ofReal_rpow_of_nonneg h_posr (by linarith)).symm
        rw [h_mul, h_rpow]
      have h_combine : ENNReal.ofReal (25 * (r / δ_n)^s) ≤
          ENNReal.ofReal (C' * r^s) * Metric.externalCoveringNumber (δ_n).toNNReal (S' : Set (DyadicTube n)) := by
        have h7 : ENNReal.ofReal (C' * r^s) * Metric.externalCoveringNumber (δ_n).toNNReal (S' : Set (DyadicTube n)) ≥
            ENNReal.ofReal (C' * r^s) * ENNReal.ofReal (δ_n^(-s) / (5 * C * (2 : ℝ)^(s + 1))) := by
          exact mul_le_mul_left' h_ncover_lower _
        have h_pos1 : 0 ≤ C' * r^s := mul_nonneg h_posC' (Real.rpow_nonneg h_posr s)
        have h8 : ENNReal.ofReal (C' * r^s) * ENNReal.ofReal (δ_n^(-s) / (5 * C * (2 : ℝ)^(s + 1))) =
            ENNReal.ofReal (C' * r^s * (δ_n^(-s) / (5 * C * (2 : ℝ)^(s + 1)))) := by
          rw [←ENNReal.ofReal_mul h_pos1]
        rw [h8] at h7
        have h9 : C' * r^s * (δ_n^(-s) / (5 * C * (2 : ℝ)^(s + 1))) = 25 * (r / δ_n)^s := by
          have h10 : C' = (125 : ℝ) * (2 : ℝ)^(s + 1) * C := by simp [hC'_def]
          rw [h10]
          have h11 : (r / δ_n)^s = r^s * δ_n^(-s) := by
            rw [Real.div_rpow (by linarith) (by positivity)]
            <;> rw [Real.rpow_neg hδn_pos.le] <;> ring
          rw [h11]
          field_simp [hC_pos.ne', hδn_pos.ne'] <;> ring
        rw [h9] at h7
        exact h7
      have h_combine' : ENNReal.ofReal (25 * (r / δ_n)^s) ≤
          ENNReal.ofReal C' * (ENNReal.ofReal r)^s * Metric.externalCoveringNumber (δ_n).toNNReal (S' : Set (DyadicTube n)) := by
        rw [h_eq_C'] at h_combine
        exact h_combine
      exact le_trans h_ncover_local h_combine'
  exact ⟨S', hS'_sub, h_upper, h_lower, h_sset⟩

end DiscretisedFurstenbergEstimate.FrontEndLemmas
