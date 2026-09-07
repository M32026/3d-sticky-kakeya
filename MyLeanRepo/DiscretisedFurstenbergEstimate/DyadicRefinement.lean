module

/-
  Dyadic refinement and IsDeltaSSet-to-finset conversion.

  ## Main results

  1. `dyadic_refinement`: select a subset Qset with uniform dyadic multiplicity.
  2. `deltaSSet_to_finset_ballCount`: extract a finite δ-separated subset P''
     from a (δ,t)-set P' with a finset ball-count property.

  Whiteprint: heavy_squares (refinement sub-part)
  Dependencies: HeavySquareEnergyBound
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate.Lagoon

open DirecretisedFurstenbergEstimate

/-! ### Dyadic refinement -/

/-- Monotonicity of Nat.log in the second argument. -/
lemma nat_log_mono {b n m : ℕ} (hb : 1 < b) (h : n ≤ m) :
    Nat.log b n ≤ Nat.log b m := by
  by_cases hn : n = 0
  · simp [hn]
  · have h1 : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b (by omega)
    have h2 : b ^ Nat.log b n ≤ m := by linarith
    exact Nat.log_mono_right h

/-- Dyadic pigeonhole refinement: given Q_all and point counts n(Q),
    select Qset ⊆ Q_all and m such that every Q ∈ Qset has m ≤ n(Q) < 2m,
    and the total count is bounded by K * m * |Qset|. -/
lemma dyadic_refinement {α : Type*} [DecidableEq α]
    (Q_all : Finset α) (n : α → ℕ) :
    ∃ (Qset : Finset α) (m K : ℕ),
      Qset ⊆ Q_all ∧
      (∀ Q ∈ Qset, m ≤ n Q ∧ n Q < 2 * m) ∧
      (∑ Q ∈ Q_all, n Q) ≤ K * m * Qset.card := by
  by_cases h_empty : Q_all = ∅
  · exact ⟨∅, 1, 1, by simp, by simp, by simp [h_empty]⟩
  · let max_n := Finset.sup Q_all n
    by_cases h_max : max_n = 0
    · have h_all_zero : ∀ Q ∈ Q_all, n Q = 0 := by
        intro Q hQ
        have h : n Q ≤ max_n := Finset.le_sup hQ
        rw [h_max] at h; omega
      have h_sum : ∑ Q ∈ Q_all, n Q = 0 := by
        apply Finset.sum_eq_zero; intro Q hQ; exact h_all_zero Q hQ
      exact ⟨∅, 1, 1, by simp, by simp, by rw [h_sum] <;> simp⟩
    · have h_max_pos : 0 < max_n := by omega
      let K_max := Nat.log 2 max_n + 1
      let level (k : ℕ) : Finset α :=
        Q_all.filter (fun Q => 2^k ≤ n Q ∧ n Q < 2^(k+1))
      let S (k : ℕ) : ℕ := 2^k * (level k).card
      have h_exists : ∃ k ∈ Finset.range K_max, ∀ j ∈ Finset.range K_max, S j ≤ S k :=
        Finset.exists_max_image (Finset.range K_max) S (by simp)
      rcases h_exists with ⟨k, hk_range, hk_max⟩
      let Qset := level k
      let m := 2^k
      have h1 : ∀ Q ∈ Qset, m ≤ n Q ∧ n Q < 2 * m := by
        intro Q hQ
        have h2 : 2^k ≤ n Q ∧ n Q < 2^(k+1) := (Finset.mem_filter.mp hQ).2
        have h3 : 2^(k+1) = 2 * m := by
          simp [m, pow_succ] <;> ring
        have h4 : n Q < 2 * m := by
          calc n Q < 2^(k+1) := h2.2
            _ = 2 * m := h3
        exact ⟨h2.1, h4⟩
      have hQset_sub : Qset ⊆ Q_all := by
        intro Q hQ; exact (Finset.mem_filter.mp hQ).1
      have h_cover : ∀ Q ∈ Q_all, n Q > 0 → ∃ j ∈ Finset.range K_max, Q ∈ level j := by
        intro Q hQ hpos
        let j := Nat.log 2 (n Q)
        have hj1 : 2^j ≤ n Q := by
          have h : 2 ^ Nat.log 2 (n Q) ≤ n Q := Nat.pow_log_le_self 2 (by omega)
          exact h
        have hj2 : n Q < 2^(j+1) := Nat.lt_pow_succ_log_self (by norm_num) (n Q)
        have h4 : n Q ≤ max_n := Finset.le_sup hQ
        have h5 : j ≤ Nat.log 2 max_n := nat_log_mono (by norm_num) h4
        have hj3 : j < K_max := by
          dsimp only [K_max]
          omega
        exact ⟨j, Finset.mem_range.mpr hj3, by
          simp only [level, Finset.mem_filter] <;> exact ⟨hQ, ⟨hj1, hj2⟩⟩⟩
      let Q_pos := Q_all.filter (fun Q => n Q > 0)
      have h_union : Q_pos ⊆ Finset.biUnion (Finset.range K_max) level := by
        intro Q hQ
        have hQ_in : Q ∈ Q_all := (Finset.mem_filter.mp hQ).1
        have hpos : n Q > 0 := (Finset.mem_filter.mp hQ).2
        rcases h_cover Q hQ_in hpos with ⟨j, hj_range, hj_level⟩
        exact Finset.mem_biUnion.mpr ⟨j, hj_range, hj_level⟩
      have h_sum_eq : ∑ Q ∈ Q_all, n Q = ∑ Q ∈ Q_pos, n Q := by
        have h : ∑ Q ∈ Q_all, n Q = ∑ Q ∈ Q_all, (if 0 < n Q then n Q else 0) := by
          apply Finset.sum_congr rfl
          intro Q hQ
          by_cases hpos : 0 < n Q <;> simp [hpos] <;> omega
        rw [h]
        rw [Finset.sum_filter]
        <;> rfl
      have h_disj : ∀ (j1 j2 : ℕ), j1 ≠ j2 → Disjoint (level j1) (level j2) := by
        intro j1 j2 hne
        simp only [Finset.disjoint_left]
        intro Q hq1 hq2
        have h1 : n Q < 2^(j1+1) := (Finset.mem_filter.mp hq1).2.2
        have h2 : 2^j2 ≤ n Q := (Finset.mem_filter.mp hq2).2.1
        by_cases h : j1 < j2
        · have h3 : j1 + 1 ≤ j2 := by omega
          have h4 : 2^(j1+1) ≤ 2^j2 := by gcongr <;> norm_num
          have h5 : n Q < 2^j2 := by linarith
          linarith
        · have h' : j2 < j1 := by omega
          have h5 : n Q < 2^(j2+1) := (Finset.mem_filter.mp hq2).2.2
          have h6 : 2^j1 ≤ n Q := (Finset.mem_filter.mp hq1).2.1
          have h7 : j2 + 1 ≤ j1 := by omega
          have h8 : 2^(j2+1) ≤ 2^j1 := by gcongr <;> norm_num
          have h9 : n Q < 2^j1 := by linarith
          linarith
      have h_disj' : Set.PairwiseDisjoint (Finset.range K_max : Set ℕ) level := by
        intro j1 _ j2 _ hne
        exact h_disj j1 j2 hne
      have h_sum_biUnion : ∑ j ∈ Finset.range K_max, ∑ Q ∈ level j, n Q =
          ∑ Q ∈ Finset.biUnion (Finset.range K_max) level, n Q := by
        rw [Finset.sum_biUnion h_disj']
      have h_sum2 : ∑ Q ∈ Q_pos, n Q ≤
          ∑ j ∈ Finset.range K_max, ∑ Q ∈ level j, n Q := by
        rw [h_sum_biUnion]
        exact Finset.sum_le_sum_of_subset_of_nonneg h_union (fun i _ _ => Nat.zero_le (n i))
      have h_bound : ∀ j ∈ Finset.range K_max,
          (∑ Q ∈ level j, n Q) ≤ 2 * S j := by
        intro j _
        have h : ∀ Q ∈ level j, n Q ≤ 2^(j+1) := by
          intro Q hQ
          have h' : n Q < 2^(j+1) := (Finset.mem_filter.mp hQ).2.2
          exact h'.le
        calc (∑ Q ∈ level j, n Q)
          ≤ ∑ Q ∈ level j, (2^(j+1) : ℕ) := Finset.sum_le_sum h
        _ = (level j).card * 2^(j+1) := by
          simp [Finset.sum_const] <;> ring
        _ = 2 * S j := by
          simp [S] <;> ring
      have h_main : ∑ Q ∈ Q_all, n Q ≤ ∑ j ∈ Finset.range K_max, 2 * S j := by
        rw [h_sum_eq]
        calc ∑ Q ∈ Q_pos, n Q
          ≤ ∑ j ∈ Finset.range K_max, ∑ Q ∈ level j, n Q := h_sum2
        _ ≤ ∑ j ∈ Finset.range K_max, 2 * S j :=
          Finset.sum_le_sum fun j hj => h_bound j hj
      have h_final : ∑ j ∈ Finset.range K_max, 2 * S j ≤ 2 * K_max * m * Qset.card := by
        have h : ∀ j ∈ Finset.range K_max, S j ≤ S k := fun j hj => hk_max j hj
        calc ∑ j ∈ Finset.range K_max, 2 * S j
          ≤ ∑ j ∈ Finset.range K_max, 2 * S k :=
            Finset.sum_le_sum fun j hj => by gcongr <;> exact h j hj
        _ = 2 * K_max * S k := by
          simp [Finset.sum_const, Finset.card_range] <;> ring
        _ = 2 * K_max * (m * Qset.card) := by
          have h_S_eq : S k = m * Qset.card := by
            simp [S, Qset, m] <;> ring
          rw [h_S_eq]
        _ = 2 * K_max * m * Qset.card := by ring
      exact ⟨Qset, m, 2 * K_max, hQset_sub, h1, le_trans h_main h_final⟩

/-! ### IsDeltaSSet → finset ball-count conversion -/

local notation "Plane" => EuclideanPlane

/-- Existence of a finite cover of the unit ball by 1/2-balls in EuclideanPlane. -/
lemma exists_unit_ball_cover :
    ∃ (C : Finset Plane), (Metric.closedBall (0 : Plane) 1) ⊆
      ⋃ c ∈ C, Metric.closedBall c (1 / 2 : ℝ) := by
  have h_compact : IsCompact (Metric.closedBall (0 : Plane) 1) := by exact isCompact_closedBall 0 1
  have h := Metric.exists_finite_isCover_of_isCompact
    (show (1 / 2 : ℝ≥0) ≠ 0 by norm_num) h_compact
  rcases h with ⟨N, _, hN_fin, hN_cover⟩
  let C := hN_fin.toFinset
  have h_coe : (C : Set Plane) = N := hN_fin.coe_toFinset
  refine' ⟨C, _⟩
  intro z hz
  have h_tmp : z ∈ ⋃ y ∈ N, Metric.closedBall y (1 / 2 : ℝ≥0) :=
    hN_cover.subset_iUnion_closedBall hz
  rcases Set.mem_iUnion₂.mp h_tmp with ⟨y, hy, hzy⟩
  have hyC : y ∈ (C : Set Plane) := by
    have h : y ∈ N := hy
    exact h_coe ▸ h
  exact Set.mem_iUnion₂.mpr ⟨y, hyC, by simpa using hzy⟩

/-- A finite 1/2-cover of the unit ball. -/
noncomputable def doublingCover : Finset Plane :=
  Classical.choose exists_unit_ball_cover

/-- Doubling constant for EuclideanPlane. -/
noncomputable def doublingConstant : ℕ := doublingCover.card

/-- The doubling cover covers the unit ball. -/
lemma doublingCover_cover :
    (Metric.closedBall (0 : Plane) 1) ⊆
      ⋃ c ∈ doublingCover, Metric.closedBall c (1 / 2 : ℝ) :=
  Classical.choose_spec exists_unit_ball_cover

/-- The doubling constant is positive. -/
lemma doublingConstant_pos : 0 < doublingConstant := by
  have h_ball : (Metric.closedBall (0 : Plane) 1).Nonempty := ⟨0, by simp⟩
  have h_union : (⋃ c ∈ doublingCover, Metric.closedBall c (1 / 2 : ℝ)).Nonempty :=
    h_ball.mono doublingCover_cover
  rcases h_union with ⟨z, hz⟩
  rcases Set.mem_iUnion₂.mp hz with ⟨c, hc, _⟩
  exact Finset.card_pos.mpr ⟨c, hc⟩

/-- Convert δ.toNNReal to ENNReal.ofReal δ. -/
lemma toNNReal_eq_ofReal {δ : ℝ} (hδ_nonneg : 0 ≤ δ) :
    (δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by
  have h_toNNReal : δ.toNNReal = NNReal.mk δ hδ_nonneg := by
    apply NNReal.coe_injective
    simp [hδ_nonneg]
  rw [h_toNNReal]
  exact (ENNReal.ofReal_eq_coe_nnreal hδ_nonneg).symm

/-- Any ball of radius δ can be covered by `doublingConstant` balls of radius δ/2. -/
lemma ball_cover_doubling (δ : ℝ) (hδ_pos : 0 < δ) (x : Plane) :
    ∃ (C : Finset Plane), C.card = doublingConstant ∧
      Metric.closedBall x δ ⊆ ⋃ c ∈ C, Metric.closedBall c (δ / 2) := by
  let C0 : Finset Plane := doublingCover
  let C : Finset Plane := C0.image (fun c => x + δ • c)
  have h_inj : Set.InjOn (fun c : Plane => x + δ • c) (C0 : Set Plane) := by
    intro c1 _ c2 _ h
    have h_eq : δ • c1 = δ • c2 := by simpa using h
    have h' : (1 / δ : ℝ) • (δ • c1) = (1 / δ : ℝ) • (δ • c2) := by rw [h_eq]
    have h_c1 : (1 / δ : ℝ) • (δ • c1) = c1 := by
      rw [smul_smul] <;> simp [hδ_pos.ne'] <;> ext i <;> simp [smul_eq_mul] <;> ring
    have h_c2 : (1 / δ : ℝ) • (δ • c2) = c2 := by
      rw [smul_smul] <;> simp [hδ_pos.ne'] <;> ext i <;> simp [smul_eq_mul] <;> ring
    rw [h_c1, h_c2] at h'
    exact h'
  have h_card : C.card = doublingConstant := by
    rw [Finset.card_image_of_injOn h_inj] <;> rfl
  have h_cover : Metric.closedBall x δ ⊆ ⋃ c ∈ C, Metric.closedBall c (δ / 2) := by
    intro y hy
    have h1 : dist y x ≤ δ := by simpa [Metric.mem_closedBall] using hy
    have h1' : ‖y - x‖ ≤ δ := by
      rw [dist_eq_norm] at h1; exact h1
    let z : Plane := (1 / δ : ℝ) • (y - x)
    have hz : ‖z‖ ≤ 1 := by
      have h_pos1 : 0 < (1 / δ : ℝ) := by positivity
      have h_norm : ‖z‖ = (1 / δ : ℝ) * ‖y - x‖ := by
        calc ‖z‖
          = |(1 / δ : ℝ)| * ‖y - x‖ := norm_smul (1 / δ : ℝ) (y - x)
        _ = (1 / δ : ℝ) * ‖y - x‖ := by rw [abs_of_pos h_pos1]
      rw [h_norm]
      have h : (1 / δ : ℝ) * ‖y - x‖ ≤ 1 := by
        calc (1 / δ : ℝ) * ‖y - x‖
          ≤ (1 / δ : ℝ) * δ := by gcongr
        _ = 1 := by field_simp [hδ_pos.ne'] <;> ring
      exact h
    have h2 : z ∈ Metric.closedBall (0 : Plane) 1 := by
      simpa [Metric.mem_closedBall] using hz
    have h3 : z ∈ ⋃ c ∈ C0, Metric.closedBall c (1 / 2 : ℝ) :=
      doublingCover_cover h2
    rcases Set.mem_iUnion₂.mp h3 with ⟨c, hc, h4⟩
    have h5 : dist z c ≤ 1 / 2 := by simpa [Metric.mem_closedBall] using h4
    have h5' : ‖z - c‖ ≤ 1 / 2 := by
      rw [dist_eq_norm] at h5; exact h5
    let c' : Plane := x + δ • c
    have hc' : c' ∈ C := Finset.mem_image.mpr ⟨c, hc, rfl⟩
    have h_yx : δ • z = y - x := by
      ext i
      simp [z, smul_eq_mul] <;> field_simp [hδ_pos.ne'] <;> ring
    have h6 : ‖y - c'‖ ≤ δ / 2 := by
      have h_y : y = x + δ • z := by
        have h : y - x = δ • z := h_yx.symm
        have h' : y = x + δ • z := by calc
          y = (y - x) + x := by abel
          _ = δ • z + x := by rw [h]
          _ = x + δ • z := by abel
        exact h'
      have h7 : y - c' = δ • (z - c) := by
        rw [h_y]
        simp [c', smul_sub]
        <;> abel
      rw [h7]
      have h8 : ‖δ • (z - c)‖ = δ * ‖z - c‖ := by
        have h9 : ‖δ • (z - c)‖ = |δ| * ‖z - c‖ := norm_smul δ (z - c)
        rw [h9, abs_of_pos hδ_pos]
      rw [h8]
      have h10 : δ * ‖z - c‖ ≤ δ * (1 / 2 : ℝ) := by gcongr
      have h11 : δ * (1 / 2 : ℝ) = δ / 2 := by ring
      rw [h11] at h10
      exact h10
    have h9 : dist y c' ≤ δ / 2 := by rw [dist_eq_norm]; exact h6
    exact Set.mem_iUnion₂.mpr ⟨c', hc', by simpa [Metric.mem_closedBall] using h9⟩
  exact ⟨C, h_card, h_cover⟩

/-- Existence of a minimal external cover when the external covering number is finite. -/
lemma exists_set_encard_eq_externalCoveringNumber {ε : NNReal} {A : Set Plane}
    (h : Metric.externalCoveringNumber ε A ≠ ⊤) :
    ∃ (C : Set Plane), Metric.IsCover ε A C ∧ C.Finite ∧
      C.encard = Metric.externalCoveringNumber ε A := by
  have h1 : ∃ (C' : Set Plane), Metric.IsCover ε A C' ∧ C'.Finite := by
    by_contra h2
    push Not at h2
    have h3 : Metric.externalCoveringNumber ε A = ⊤ := by
      simp [Metric.externalCoveringNumber, h2, Set.encard_eq_top_iff]
      <;> tauto
    exact h h3
  rcases h1 with ⟨C', hC'_cover, hC'_fin⟩
  letI : Nonempty { s : Set Plane // Metric.IsCover ε A s } :=
    ⟨⟨C', hC'_cover⟩⟩
  let h_exists := ENat.exists_eq_iInf
    (fun C : {s : Set Plane // Metric.IsCover ε A s} ↦ (C : Set Plane).encard)
  obtain ⟨C_sub, hC⟩ := h_exists
  let C : Set Plane := C_sub.val
  have hC_cover' : Metric.IsCover ε A C := C_sub.property
  have h_fin : C.Finite := by
    have h_lt : C.encard < ⊤ := by
      rw [hC]
      simp only [iInf_lt_top, Set.encard_lt_top_iff, Subtype.exists, exists_prop]
      exact ⟨C', hC'_cover, hC'_fin⟩
    exact Set.encard_lt_top_iff.mp h_lt
  have h_eq : C.encard = Metric.externalCoveringNumber ε A := by
    rw [hC]
    simp_rw [Metric.externalCoveringNumber, iInf_subtype]
  exact ⟨C, hC_cover', h_fin, h_eq⟩

/-- Covering number doubling: externalCoveringNumber(δ/2) A ≤ doublingConstant * externalCoveringNumber(δ) A. -/
lemma coveringNumber_doubling (δ : ℝ) (hδ_pos : 0 < δ) (A : Set Plane) :
    Metric.externalCoveringNumber (δ / 2).toNNReal A ≤
      (doublingConstant : ENat) * Metric.externalCoveringNumber δ.toNNReal A := by
  have hK_pos : 0 < doublingConstant := doublingConstant_pos
  by_cases h_top : Metric.externalCoveringNumber δ.toNNReal A = ⊤
  · rw [h_top]
    have h : (doublingConstant : ENat) * (⊤ : ENat) = ⊤ := by
      simp [hK_pos.ne']
    rw [h]
    exact le_top
  · rcases exists_set_encard_eq_externalCoveringNumber h_top with ⟨C, hC_cover, hC_fin, hC_encard⟩
    let c' := hC_fin.toFinset
    have h_coe : (c' : Set Plane) = C := hC_fin.coe_toFinset
    choose D hD_card hD_cover using fun x => ball_cover_doubling δ hδ_pos x
    let D_all : Finset Plane := c'.biUnion D
    have h_cover' : A ⊆ ⋃ x ∈ c', Metric.closedBall x δ := by
      intro a ha
      have h_tmp : a ∈ ⋃ y ∈ C, Metric.closedBall y δ.toNNReal :=
        hC_cover.subset_iUnion_closedBall ha
      rcases Set.mem_iUnion₂.mp h_tmp with ⟨y, hy, hzy⟩
      have hyC : y ∈ (c' : Set Plane) := by
        have h : y ∈ C := hy
        exact h_coe ▸ h
      have hdist : dist a y ≤ δ := by
        have h_in : a ∈ Metric.closedBall y δ.toNNReal := hzy
        have hδ_nonneg : 0 ≤ δ := by linarith
        have h_toNNReal_coe : (δ.toNNReal : ℝ) = δ := by exact Real.coe_toNNReal δ hδ_nonneg
        have h_nndist : nndist a y ≤ δ.toNNReal := by
          have h_simp : dist a y ≤ δ ∨ a = y := by
            simpa [Metric.mem_closedBall] using h_in
          rcases h_simp with (h | rfl)
          · have h4 : (nndist a y : ℝ) = dist a y := by exact coe_nndist a y
            have h5 : (nndist a y : ℝ) ≤ (δ.toNNReal : ℝ) := by
              rw [h4, h_toNNReal_coe] <;> exact h
            exact_mod_cast h5
          · simp
        have h : (nndist a y : ℝ) ≤ (δ.toNNReal : ℝ) := by exact_mod_cast h_nndist
        have h2 : (nndist a y : ℝ) = dist a y := by exact coe_nndist a y
        rw [h2, h_toNNReal_coe] at h
        exact h
      exact Set.mem_iUnion₂.mpr ⟨y, hyC, by simpa [Metric.mem_closedBall] using hdist⟩
    have hD_all_cover : A ⊆ ⋃ y ∈ D_all, Metric.closedBall y (δ / 2) := by
      intro a ha
      have h1 : ∃ x ∈ c', dist a x ≤ δ := by
        simpa [Finset.mem_biUnion] using h_cover' ha
      rcases h1 with ⟨x, hx, hdist⟩
      have h2 : a ∈ ⋃ y ∈ D x, Metric.closedBall y (δ / 2) :=
        hD_cover x (by simpa [Metric.mem_closedBall] using hdist)
      rcases Set.mem_iUnion₂.mp h2 with ⟨y, hy, h3⟩
      have h4 : y ∈ D_all := Finset.mem_biUnion.mpr ⟨x, hx, hy⟩
      exact Set.mem_iUnion₂.mpr ⟨y, h4, h3⟩
    have hD_all_isCover : Metric.IsCover (δ / 2).toNNReal A (D_all : Set Plane) := by
      intro a ha
      have h : a ∈ ⋃ y ∈ D_all, Metric.closedBall y (δ / 2) := hD_all_cover ha
      rcases Set.mem_iUnion₂.mp h with ⟨y, hy, h2⟩
      have h3 : dist a y ≤ δ / 2 := by simpa [Metric.mem_closedBall] using h2
      refine ⟨y, hy, ?_⟩
      have h4 : edist a y ≤ ((δ / 2).toNNReal : ENNReal) := by
        rw [edist_dist]
        have h5 : 0 ≤ δ / 2 := by linarith
        simpa [h5] using h3
      exact h4
    have h1 : Metric.externalCoveringNumber (δ / 2).toNNReal A ≤ (D_all : Set Plane).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hD_all_isCover
    have h_card_le : D_all.card ≤ ∑ x ∈ c', (D x).card :=
      Finset.card_biUnion_le (s := c') (t := D)
    have h2 : D_all.card ≤ doublingConstant * c'.card := by
      calc D_all.card
        ≤ ∑ x ∈ c', (D x).card := h_card_le
      _ = ∑ x ∈ c', doublingConstant := by
        apply Finset.sum_congr rfl; intro x _; exact hD_card x
      _ = doublingConstant * c'.card := by
        simp [Finset.sum_const] <;> ring
    have h3 : (D_all : Set Plane).encard ≤ (doublingConstant : ENat) * C.encard := by
      have h31 : (D_all : Set Plane).encard = (D_all.card : ENat) := by simp
      have h32 : C.encard = (c'.card : ENat) := by
        rw [← h_coe] <;> simp
      rw [h31, h32]
      exact_mod_cast h2
    have h4 : (doublingConstant : ENat) * C.encard =
        (doublingConstant : ENat) * Metric.externalCoveringNumber δ.toNNReal A := by
      rw [hC_encard]
    rw [h4] at h3
    exact le_trans h1 h3

/-- Packing bound: packingNumber(δ) A ≤ doublingConstant * externalCoveringNumber(δ) A. -/
lemma packingNumber_le_cover (δ : ℝ) (hδ_pos : 0 < δ) (A : Set Plane) :
    Metric.packingNumber δ.toNNReal A ≤
      (doublingConstant : ENat) * Metric.externalCoveringNumber δ.toNNReal A := by
  let ε2 : NNReal := (δ / 2).toNNReal
  have h_double : (2 * ε2) = δ.toNNReal := by
    apply Subtype.ext
    have h_pos2 : 0 ≤ δ / 2 := by linarith
    have h1 : (ε2 : ℝ) = δ / 2 := by
      simp [ε2, NNReal.coe_mk, h_pos2] <;> norm_cast
    have h_goal : (↑(2 * ε2) : ℝ) = (↑δ.toNNReal : ℝ) := by
      calc (↑(2 * ε2) : ℝ)
        = 2 * (ε2 : ℝ) := by simp
      _ = 2 * (δ / 2) := by rw [h1]
      _ = δ := by ring
      _ = (↑δ.toNNReal : ℝ) := by simp [hδ_pos.le] <;> norm_cast
    exact h_goal
  have h1 : Metric.packingNumber (2 * ε2) A ≤
      Metric.externalCoveringNumber ε2 A :=
    Metric.packingNumber_two_mul_le_externalCoveringNumber ε2 A
  rw [h_double] at h1
  have h2 : Metric.externalCoveringNumber ε2 A ≤
      (doublingConstant : ENat) * Metric.externalCoveringNumber δ.toNNReal A :=
    coveringNumber_doubling δ hδ_pos A
  exact le_trans h1 h2

/-- Bounded sets in EuclideanPlane have finite packing number. -/
lemma bounded_packing_finite {δ : ℝ} (hδ_pos : 0 < δ)
    {P' : Set Plane} (hP'_bounded : P' ⊆ Metric.closedBall 0 1) :
    Metric.packingNumber δ.toNNReal P' ≠ ⊤ := by
  have h_compact : IsCompact (Metric.closedBall (0 : Plane) 1) := by exact isCompact_closedBall 0 1
  have h_tb : TotallyBounded (Metric.closedBall (0 : Plane) 1) :=
    h_compact.totallyBounded
  have h_exists : ∃ (N : Set Plane), N ⊆ Metric.closedBall (0 : Plane) 1 ∧ N.Finite ∧
      Metric.IsCover δ.toNNReal (Metric.closedBall (0 : Plane) 1) N :=
    Metric.exists_finite_isCover_of_totallyBounded
      (show δ.toNNReal ≠ 0 by simp [hδ_pos]) h_tb
  rcases h_exists with ⟨N, _, hN_fin, hN_cover⟩
  let C := hN_fin.toFinset
  have h_coe : (C : Set Plane) = N := hN_fin.coe_toFinset
  have hP'_isCover : Metric.IsCover δ.toNNReal P' (C : Set Plane) := by
    have h_tmp : P' ⊆ ⋃ y ∈ N, Metric.closedBall y δ.toNNReal :=
      Set.Subset.trans hP'_bounded hN_cover.subset_iUnion_closedBall
    have h_tmp2 : P' ⊆ ⋃ y ∈ (C : Set Plane), Metric.closedBall y δ.toNNReal := by
      convert h_tmp using 2
      <;> rw [h_coe]
    exact Metric.IsCover.of_subset_iUnion_closedBall h_tmp2
  have h3 : Metric.externalCoveringNumber δ.toNNReal P' ≤ (C : Set Plane).encard :=
    Metric.IsCover.externalCoveringNumber_le_encard hP'_isCover
  have h4 : (C : Set Plane).encard = (C.card : ENat) := by simp
  rw [h4] at h3
  have h5 : Metric.externalCoveringNumber δ.toNNReal P' ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp) h3
  have h6 : Metric.packingNumber δ.toNNReal P' ≤
      (doublingConstant : ENat) * Metric.externalCoveringNumber δ.toNNReal P' :=
    packingNumber_le_cover δ hδ_pos P'
  have hK_pos : 0 < doublingConstant := doublingConstant_pos
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ↑n = Metric.externalCoveringNumber δ.toNNReal P' :=
    ENat.ne_top_iff_exists.mp h5
  have hn' : Metric.externalCoveringNumber δ.toNNReal P' = ↑n := hn.symm
  have h7 : (doublingConstant : ENat) * Metric.externalCoveringNumber δ.toNNReal P' ≠ ⊤ := by
    rw [hn']
    have h_eq : (doublingConstant : ENat) * (↑n : ENat) = ↑(doublingConstant * n) := by
      exact (ENat.coe_mul doublingConstant n).symm
    rw [h_eq]
    exact ENat.ne_top_iff_exists.mpr ⟨doublingConstant * n, rfl⟩
  exact ne_top_of_le_ne_top h7 h6

/-- Helper: convert Metric.IsSeparated (using edist) to strict dist inequality. -/
lemma isSeparated_to_dist {δ : ℝ} (hδ_pos : 0 < δ) {S : Set Plane}
    (h : Metric.IsSeparated δ.toNNReal S) :
    Set.Pairwise S (fun a b => δ < dist a b) := by
  intro a ha b hb hne
  have h_edist : (δ.toNNReal : ENNReal) < edist a b := h ha hb hne
  have h_eq : edist a b = ENNReal.ofReal (dist a b) := edist_dist a b
  rw [h_eq] at h_edist
  have hδ_nonneg : 0 ≤ δ := by linarith
  have h1 : (δ.toNNReal : ENNReal) = ENNReal.ofReal δ := toNNReal_eq_ofReal hδ_nonneg
  rw [h1] at h_edist
  have h2 : ENNReal.ofReal δ < ENNReal.ofReal (dist a b) := h_edist
  have h3 : δ < dist a b := by
    by_contra h4
    have h5 : dist a b ≤ δ := by linarith
    have h6 : ENNReal.ofReal (dist a b) ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal h5
    exact not_lt.mpr h6 h2
  exact h3

/-- Extract a finite δ-separated subset P'' from a bounded set P' such that
    P'' is a δ-cover of P'. -/
lemma finite_separated_cover {δ : ℝ} (hδ_pos : 0 < δ)
    {P' : Set Plane} (hP'_bounded : P' ⊆ Metric.closedBall 0 1) :
    ∃ (P'' : Finset Plane),
      (P'' : Set Plane) ⊆ P' ∧
      Set.Pairwise (P'' : Set Plane) (fun a b => δ < dist a b) ∧
      Metric.IsCover δ.toNNReal P' (P'' : Set Plane) := by
  have h_pack_fin : Metric.packingNumber δ.toNNReal P' ≠ ⊤ :=
    bounded_packing_finite hδ_pos hP'_bounded
  let P''_set := Metric.maximalSeparatedSet δ.toNNReal P'
  have h_sub : P''_set ⊆ P' := Metric.maximalSeparatedSet_subset
  have h_sep : Metric.IsSeparated δ.toNNReal P''_set :=
    Metric.isSeparated_maximalSeparatedSet
  have h_cover : Metric.IsCover δ.toNNReal P' P''_set :=
    Metric.isCover_maximalSeparatedSet h_pack_fin
  have h_fin : P''_set.Finite := by
    have h_encard : P''_set.encard = Metric.packingNumber δ.toNNReal P' :=
      Metric.encard_maximalSeparatedSet h_pack_fin
    have h_ne_top : P''_set.encard ≠ ⊤ := by
      rw [h_encard]; exact h_pack_fin
    exact Set.encard_ne_top_iff.mp h_ne_top
  let P'' := h_fin.toFinset
  have h_coe : (P'' : Set Plane) = P''_set := h_fin.coe_toFinset
  have h_sep' : Set.Pairwise (P'' : Set Plane) (fun a b => δ < dist a b) := by
    rw [h_coe]
    exact isSeparated_to_dist hδ_pos h_sep
  refine' ⟨P'', _⟩
  have h_coe' : (P'' : Set Plane) = P''_set := h_fin.coe_toFinset
  have h_sep'' : P''_set.Pairwise (fun a b => δ < dist a b) := by
    rw [←h_coe']
    exact h_sep'
  rw [h_coe']
  exact ⟨h_sub, h_sep'', h_cover⟩

/-- Convert IsDeltaSSet to a finset ball-count property.
    Given a (δ,t,C_P')-set P' that is bounded, extract a finite δ-separated
    subset P'' ⊆ P' such that for all x, r ≥ δ:
    |P'' ∩ B(x,r)| ≤ doublingConstant * C_P' * r^t * |P''|. -/
lemma deltaSSet_to_finset_ballCount {δ t C_P' : ℝ}
    (hδ_pos : 0 < δ) (ht_pos : 0 ≤ t) (hC_pos : 0 < C_P')
    {P' : Set Plane} (hP' : IsDeltaSSet δ t C_P' P')
    (hP'_bounded : P' ⊆ Metric.closedBall 0 1) :
    ∃ (P'' : Finset Plane),
      (P'' : Set Plane) ⊆ P' ∧
      Set.Pairwise (P'' : Set Plane) (fun a b => δ ≤ dist a b) ∧
      ∀ (x : Plane) (r : ℝ), δ ≤ r →
        ((P''.filter (fun y => dist x y ≤ r)).card : ℝ) ≤
          (doublingConstant : ℝ) * C_P' * r^t * (P''.card : ℝ) := by
  rcases hP' with ⟨_, _, _, _, hP'_ball⟩
  rcases finite_separated_cover hδ_pos hP'_bounded with ⟨P'', h_sub, h_sep, h_cover⟩
  have h_ecover_le : Metric.externalCoveringNumber δ.toNNReal P' ≤ (P'' : Set Plane).encard :=
    Metric.IsCover.externalCoveringNumber_le_encard h_cover
  have h_main : ∀ (x : Plane) (r : ℝ), δ ≤ r →
      ((P''.filter (fun y => dist x y ≤ r)).card : ENNReal) ≤
        (doublingConstant : ENNReal) * ENNReal.ofReal C_P' * (ENNReal.ofReal r) ^ t * (P''.card : ENNReal) := by
    intro x r hr
    let S := P''.filter (fun y => dist x y ≤ r)
    have hS_sep : Metric.IsSeparated δ.toNNReal (S : Set Plane) := by
      intro a ha b hb hne
      have h : δ < dist a b := h_sep (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hne
      have hδ_nonneg : 0 ≤ δ := by linarith
      have h1 : (δ.toNNReal : ENNReal) = ENNReal.ofReal δ := toNNReal_eq_ofReal hδ_nonneg
      rw [h1, edist_dist a b]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hδ_nonneg |>.mpr h
    have h1 : (S : Set Plane).encard ≤ Metric.packingNumber δ.toNNReal (S : Set Plane) :=
      Metric.IsSeparated.encard_le_packingNumber (Set.Subset.refl _) hS_sep
    have h2 : Metric.packingNumber δ.toNNReal (S : Set Plane) ≤
        (doublingConstant : ENat) * Metric.externalCoveringNumber δ.toNNReal (S : Set Plane) :=
      packingNumber_le_cover δ hδ_pos (S : Set Plane)
    have hS_sub : (S : Set Plane) ⊆ P' ∩ Metric.closedBall x r := by
      intro p hp
      have h2 : p ∈ P'' := (Finset.mem_filter.mp hp).1
      have h3 : dist x p ≤ r := (Finset.mem_filter.mp hp).2
      have h4 : p ∈ Metric.closedBall x r := by
        simpa [Metric.mem_closedBall, dist_comm] using h3
      exact ⟨h_sub h2, h4⟩
    have h3 : Metric.externalCoveringNumber δ.toNNReal (S : Set Plane) ≤
        Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x r) :=
      Metric.externalCoveringNumber_mono_set hS_sub
    have h4 : (Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C_P' * (ENNReal.ofReal r) ^ t *
          (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal) :=
      hP'_ball x r hr
    have h_ecard_S : (S : Set Plane).encard = (S.card : ENat) := by simp
    have h_ecard_P'' : (P'' : Set Plane).encard = (P''.card : ENat) := by simp
    have h_step1 : (S.card : ENNReal) ≤ (Metric.packingNumber δ.toNNReal (S : Set Plane) : ENNReal) := by
      exact_mod_cast h1
    have h_step2 : (Metric.packingNumber δ.toNNReal (S : Set Plane) : ENNReal) ≤
        ((doublingConstant : ENat) * Metric.externalCoveringNumber δ.toNNReal (S : Set Plane) : ENNReal) := by
      exact_mod_cast h2
    have h_step3 : ((doublingConstant : ENat) * Metric.externalCoveringNumber δ.toNNReal (S : Set Plane) : ENNReal) ≤
        ((doublingConstant : ENat) * Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x r) : ENNReal) := by
      gcongr
      <;> exact_mod_cast h3
    have h_step4 : ((doublingConstant : ENat) * Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x r) : ENNReal) ≤
        (doublingConstant : ENNReal) * (ENNReal.ofReal C_P' * (ENNReal.ofReal r) ^ t *
          (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal)) := by
      have h41 : (Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x r) : ENNReal) ≤
          ENNReal.ofReal C_P' * (ENNReal.ofReal r) ^ t *
            (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal) := h4
      have h_eq : ((doublingConstant : ENat) * Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x r) : ENNReal) =
          (doublingConstant : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x r) : ENNReal) := by
        simp
      rw [h_eq]
      exact mul_le_mul_left' h41 _
    have h_step5 : (doublingConstant : ENNReal) * (ENNReal.ofReal C_P' * (ENNReal.ofReal r) ^ t *
          (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal)) ≤
        (doublingConstant : ENNReal) * ENNReal.ofReal C_P' * (ENNReal.ofReal r) ^ t * (P''.card : ENNReal) := by
      have h51 : (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal) ≤ (P''.card : ENNReal) := by
        exact_mod_cast h_ecover_le
      have h : (doublingConstant : ENNReal) * (ENNReal.ofReal C_P' * (ENNReal.ofReal r) ^ t *
            (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal)) ≤
          (doublingConstant : ENNReal) * (ENNReal.ofReal C_P' * (ENNReal.ofReal r) ^ t * (P''.card : ENNReal)) := by
        gcongr
        <;> exact h51
      simpa [mul_assoc] using h
    exact le_trans (le_trans (le_trans (le_trans h_step1 h_step2) h_step3) h_step4) h_step5
  have h_sep_nonstrict : Set.Pairwise (P'' : Set Plane) (fun a b => δ ≤ dist a b) := by
    intro a ha b hb hne
    have h_strict : δ < dist a b := h_sep ha hb hne
    exact le_of_lt h_strict
  refine' ⟨P'', h_sub, h_sep_nonstrict, _⟩
  intro x r hr
  have h4 := h_main x r hr
  let RHS : ENNReal := (doublingConstant : ENNReal) * ENNReal.ofReal C_P' * (ENNReal.ofReal r) ^ t * (P''.card : ENNReal)
  have hr_pos : 0 < r := by linarith
  have hRHS_ne_top : RHS ≠ ⊤ := by
    have h1 : (doublingConstant : ENNReal) ≠ ⊤ := by simp
    have h2 : ENNReal.ofReal C_P' ≠ ⊤ := by simp
    have h3 : (ENNReal.ofReal r) ^ t ≠ ⊤ := by
      simp [hr_pos.ne', ht_pos]
      <;> norm_num
    have h4 : (P''.card : ENNReal) ≠ ⊤ := by simp
    simp only [RHS]
    have h5 := ENNReal.mul_ne_top h1 h2
    have h6 := ENNReal.mul_ne_top h5 h3
    exact ENNReal.mul_ne_top h6 h4
  have h6 : ((P''.filter (fun y => dist x y ≤ r)).card : ℝ) ≤ RHS.toReal :=
    ENNReal.toReal_mono hRHS_ne_top h4
  have hr_pos2 : 0 < r := by linarith
  have h7 : RHS.toReal = (doublingConstant : ℝ) * C_P' * r^t * (P''.card : ℝ) := by
    have h_ne1 : (doublingConstant : ENNReal) ≠ ⊤ := by simp
    have h_ne2 : ENNReal.ofReal C_P' ≠ ⊤ := by simp
    have h_ne3 : (ENNReal.ofReal r) ^ t ≠ ⊤ := by
      simp [hr_pos2.ne', ht_pos] <;> norm_num
    have h_ne4 : (P''.card : ENNReal) ≠ ⊤ := by simp
    have h_r_nonneg : 0 ≤ r := by linarith
    have h_C_nonneg : 0 ≤ C_P' := by linarith
    have h_rpow : ((ENNReal.ofReal r) ^ t).toReal = r ^ t := by
      have h_eq1 := ENNReal.toReal_rpow (ENNReal.ofReal r) t
      have h_eq2 : (ENNReal.ofReal r).toReal = r := by
        rw [ENNReal.toReal_ofReal h_r_nonneg]
      rw [h_eq2] at h_eq1
      exact h_eq1.symm
    simp only [RHS]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul]
    rw [h_rpow]
    have h_dc : (doublingConstant : ENNReal).toReal = (doublingConstant : ℝ) := by simp
    have h_C : (ENNReal.ofReal C_P').toReal = C_P' := by
      rw [ENNReal.toReal_ofReal h_C_nonneg]
    have h_card : (P''.card : ENNReal).toReal = (P''.card : ℝ) := by simp
    rw [h_dc, h_C, h_card] <;> ring
  rw [h7] at h6
  exact h6

end DirecretisedFurstenbergEstimate.Lagoon
