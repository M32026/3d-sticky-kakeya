module

/-
  Grid snapping for 1D S-sets.

  Converts a bounded (δ,s,C)-set A ⊆ [0,1] into a subset A_grid of the
  δ-grid that is a ProductLikeRealDeltaSCSet with constant C*100 and has
  covering number at least original/100.

  Whiteprint node: `grid_snap`
  Dependencies: `covering_utils`
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Translation
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open scoped ENNReal NNReal
open DirecretisedFurstenbergEstimate

namespace DiscretisedFurstenbergEstimate.GridSnap

/-! ### Bounded packing number finiteness -/

/-- Bounded set in ℝ has finite packing number at scale δ > 0. -/
lemma bounded_packing_finite {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA_bdd : Bornology.IsBounded A) :
    Metric.packingNumber δ.toNNReal A ≠ ⊤ := by
  let ε : NNReal := ⟨δ / 2, by linarith⟩
  have hε_pos' : 0 < δ / 2 := by linarith
  have hε_pos : (0 : ENNReal) < ↑ε := by exact_mod_cast hε_pos'
  have hε_coe : (ε : ℝ) = δ / 2 := by exact Real.ext_cauchy rfl
  have h2ε : 2 * ε = δ.toNNReal := by
    apply NNReal.coe_injective
    have h1 : ((2 * ε : NNReal) : ℝ) = 2 * (ε : ℝ) := by exact Real.ext_cauchy rfl
    have h3 : ((δ.toNNReal : NNReal) : ℝ) = δ := by
      rw [Real.coe_toNNReal] <;> linarith
    rw [h1, h3, hε_coe] <;> ring
  have h1 : ∃ (r : ℝ), A ⊆ Metric.ball (0 : ℝ) r := hA_bdd.subset_ball 0
  rcases h1 with ⟨r, hsub⟩
  have h2 : TotallyBounded (Metric.ball (0 : ℝ) r) := Real.totallyBounded_ball 0 r
  have hTB : TotallyBounded A := by exact TotallyBounded.subset hsub h2
  have h4 : ∀ (e : ENNReal), 0 < e → ∃ (t : Set ℝ), t.Finite ∧ A ⊆ ⋃ y ∈ t, Metric.eball y e :=
    (EMetric.totallyBounded_iff (s := A)).mp hTB
  rcases h4 (↑ε) hε_pos with ⟨t, ht_fin, hcover⟩
  have hIsCover : Metric.IsCover ε A t := by
    intro x hx
    have h6 : x ∈ ⋃ y ∈ t, Metric.eball y (↑ε) := hcover hx
    have h6' : ∃ (y : ℝ), y ∈ t ∧ edist x y < (↑ε : ENNReal) := by
      simpa [Set.mem_iUnion, Metric.mem_eball] using h6
    rcases h6' with ⟨y, hy_mem, h7⟩
    exact ⟨y, hy_mem, le_of_lt h7⟩
  have h9 : Metric.externalCoveringNumber ε A ≤ t.encard :=
    Metric.IsCover.externalCoveringNumber_le_encard hIsCover
  have h10 : t.encard < ⊤ := ht_fin.encard_lt_top
  have h11 : Metric.externalCoveringNumber ε A < ⊤ := h9.trans_lt h10
  have h12 : Metric.packingNumber (2 * ε) A ≤ Metric.externalCoveringNumber ε A :=
    Metric.packingNumber_two_mul_le_externalCoveringNumber ε A
  rw [h2ε] at h12
  have h13 : Metric.packingNumber δ.toNNReal A < ⊤ := h12.trans_lt h11
  exact h13.ne

/-! ### δ-grid set covering bounds in ℝ -/

/-- A subset of the δ-grid intersects a closed δ-ball in at most 3 points. -/
lemma grid_set_ball_at_most_3 {δ : ℝ} (hδ : 0 < δ)
    {T : Set ℝ} (hT : T ⊆ productLikeIntegerGrid δ) {x : ℝ} :
    (T ∩ Metric.closedBall x δ).Finite ∧
    (T ∩ Metric.closedBall x δ).encard ≤ 3 := by
  let S := T ∩ Metric.closedBall x δ
  have hS_grid : S ⊆ productLikeIntegerGrid δ := by
    intro y hy; exact hT hy.1
  have hS_bdd : ∀ y ∈ S, x - δ ≤ y ∧ y ≤ x + δ := by
    intro y hy
    have h : dist y x ≤ δ := (Metric.mem_closedBall).mp hy.2
    have h2 : |y - x| ≤ δ := by simpa [dist_eq_norm] using h
    exact ⟨by linarith [abs_le.mp h2], by linarith [abs_le.mp h2]⟩
  classical
  let f : ℝ → ℤ := fun y => if h : y ∈ S then (hS_grid h).choose else 0
  have h_f_def : ∀ y ∈ S, y = δ * (f y : ℝ) := by
    intro y hy
    have h_fy : f y = (hS_grid hy).choose := by
      simp [f, hy]
    rw [h_fy]
    exact (hS_grid hy).choose_spec
  have h_inj : Set.InjOn f S := by
    intro y hy z hz h_eq
    have hy_eq : y = δ * (f y : ℝ) := h_f_def y hy
    have hz_eq : z = δ * (f z : ℝ) := h_f_def z hz
    rw [hy_eq, hz_eq, h_eq]
  let k_min : ℤ := ⌊(x - δ) / δ⌋
  let k_max : ℤ := ⌊(x + δ) / δ⌋
  have h_range : ∀ y ∈ S, f y ∈ Finset.Icc k_min k_max := by
    intro y hy
    have h1 : x - δ ≤ y := (hS_bdd y hy).1
    have h2 : y ≤ x + δ := (hS_bdd y hy).2
    have h3 : y = δ * (f y : ℝ) := h_f_def y hy
    rw [h3] at h1 h2
    have h4 : (x - δ) / δ ≤ (f y : ℝ) := by
      have h41 : δ * (f y : ℝ) ≥ x - δ := h1
      have h : (x - δ) / δ ≤ (δ * (f y : ℝ)) / δ := by gcongr <;> linarith
      have h2 : (δ * (f y : ℝ)) / δ = (f y : ℝ) := by field_simp [hδ.ne'] <;> ring
      rw [h2] at h
      exact h
    have h5 : (f y : ℝ) ≤ (x + δ) / δ := by
      have h51 : δ * (f y : ℝ) ≤ x + δ := h2
      have h : (δ * (f y : ℝ)) / δ ≤ (x + δ) / δ := by gcongr <;> linarith
      have h2 : (δ * (f y : ℝ)) / δ = (f y : ℝ) := by field_simp [hδ.ne'] <;> ring
      rw [h2] at h
      exact h
    have h6 : k_min ≤ f y := by
      have h61 : (k_min : ℝ) ≤ (x - δ) / δ := Int.floor_le _
      have h63 : (k_min : ℝ) ≤ (f y : ℝ) := by linarith
      exact_mod_cast h63
    have h7 : f y ≤ k_max := by
      have h71 : (f y : ℝ) ≤ (x + δ) / δ := h5
      have h : f y ≤ ⌊(x + δ) / δ⌋ := by exact Int.le_floor.mpr h5
      exact h
    exact Finset.mem_Icc.mpr ⟨h6, h7⟩
  have h_img_fin : Set.Finite (f '' S) := by
    have h_sub : f '' S ⊆ (Finset.Icc k_min k_max : Set ℤ) := by
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      exact h_range y hy
    exact Set.Finite.subset (Finset.finite_toSet _) h_sub
  have h_encard_image : (f '' S).encard = S.encard := h_inj.encard_image
  have hS_encard : S.encard ≠ ⊤ := by
    rw [←h_encard_image]
    exact (Set.Finite.encard_lt_top h_img_fin).ne
  have hS_fin : Set.Finite S := Set.encard_ne_top_iff.mp hS_encard
  have h_floor_add : ∀ (z : ℝ) (n : ℤ), ⌊z + (n : ℝ)⌋ = ⌊z⌋ + n := by
    intro z n
    exact Int.floor_add_intCast z n
  have h_bound : k_max - k_min ≤ 2 := by
    have h4 : (x + δ) / δ = (x - δ) / δ + (2 : ℝ) := by
      field_simp [hδ.ne'] <;> ring
    have h5 : k_max = k_min + 2 := by
      calc k_max
        = ⌊(x + δ) / δ⌋ := by rfl
      _ = ⌊(x - δ) / δ + (2 : ℝ)⌋ := by rw [h4]
      _ = ⌊(x - δ) / δ⌋ + (2 : ℤ) := h_floor_add ((x - δ) / δ) 2
      _ = k_min + 2 := by rfl
    omega
  have h_card : S.encard ≤ 3 := by
    rw [←h_encard_image]
    have h : (f '' S).encard ≤ (Finset.Icc k_min k_max : Set ℤ).encard :=
      Set.encard_mono (by
        intro z hz
        rcases hz with ⟨y, hy, rfl⟩
        exact h_range y hy)
    have h2 : (Finset.Icc k_min k_max : Set ℤ).encard ≤ 3 := by
      have h3 : (Finset.Icc k_min k_max).card ≤ 3 := by
        have h41 : (k_min : ℝ) ≤ (x - δ) / δ := Int.floor_le _
        have h42 : (x + δ) / δ ≤ (k_max : ℝ) + 1 := Int.lt_floor_add_one _ |>.le
        have h43 : k_min ≤ k_max := by
          have h_mon : Monotone (fun x : ℝ => ⌊x⌋) := fun a b h => Int.floor_mono h
          have h_ineq : (x - δ) / δ ≤ (x + δ) / δ := by
            have h : (x - δ) ≤ (x + δ) := by linarith
            gcongr <;> linarith
          exact h_mon h_ineq
        have h_sub : Finset.Icc k_min k_max ⊆ Finset.Icc k_min (k_min + 2) := by
          intro z hz
          have h5 : k_min ≤ z := (Finset.mem_Icc.mp hz).1
          have h6 : z ≤ k_max := (Finset.mem_Icc.mp hz).2
          have h7 : z ≤ k_min + 2 := by omega
          exact Finset.mem_Icc.mpr ⟨h5, h7⟩
        have h_card : (Finset.Icc k_min (k_min + 2)).card = 3 := by
          have h_general : ∀ (k : ℤ), (Finset.Icc k (k + 2)).card = 3 := by
            intro k
            simp [Finset.Icc_eq_empty_of_lt]
            <;> omega
          exact h_general k_min
        have h : (Finset.Icc k_min k_max).card ≤ (Finset.Icc k_min (k_min + 2)).card :=
          Finset.card_le_card h_sub
        rw [h_card] at h
        exact h
      exact_mod_cast h3
    exact h.trans h2
  exact ⟨hS_fin, h_card⟩

/-- For a finite subset T of the δ-grid, |T| ≤ 3 * externalCoveringNumber δ T. -/
lemma grid_set_cover_bound {δ : ℝ} (hδ : 0 < δ)
    {T : Set ℝ} (hT : T ⊆ productLikeIntegerGrid δ) (hT_fin : Set.Finite T) :
    (T.encard : ENNReal) ≤ 3 * (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) := by
  by_cases h_top : Metric.externalCoveringNumber δ.toNNReal T = ⊤
  · rw [h_top] <;> simp
  · rcases DiscretisedFurstenbergEstimate.CoveringUtils.exists_external_cover_eq (lt_top_iff_ne_top.mpr h_top) with ⟨C, hC, hC_eq⟩
    by_cases hCinf : C.encard = ⊤
    · rw [hC_eq] at hCinf; rw [hCinf] <;> simp
    · have hCfin : Set.Finite C := Set.encard_ne_top_iff.mp hCinf
      let C' := hCfin.toFinset
      let T' := hT_fin.toFinset
      let S_c : ℝ → Finset ℝ := fun c =>
        (grid_set_ball_at_most_3 hδ hT (x := c)).1.toFinset
      let S_union : Finset ℝ := C'.biUnion S_c
      have h_coe_T : (T' : Set ℝ) = T := hT_fin.coe_toFinset
      have h1 : T' ⊆ S_union := by
        intro x hx
        have h_x_in_T : x ∈ T := by
          rw [←h_coe_T] <;> exact hx
        rcases hC h_x_in_T with ⟨c, hc, hedist⟩
        have hc' : c ∈ C' := by simpa [C'] using hc
        have h_edist : edist x c ≤ ↑δ.toNNReal := hedist
        have hdist : dist x c ≤ δ := by
          rw [edist_dist] at h_edist
          have h_eq : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by exact ENNReal.ofNNReal_toNNReal δ
          rw [h_eq] at h_edist
          have h_nonneg : 0 ≤ dist x c := dist_nonneg
          have h_edist' : ENNReal.ofReal (dist x c) ≤ ENNReal.ofReal δ := by
            simpa [edist_dist, h_nonneg] using h_edist
          exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h_edist'
        have h_in_Sc : x ∈ S_c c := by
          simpa [S_c] using ⟨h_x_in_T, Metric.mem_closedBall.mpr hdist⟩
        exact Finset.mem_biUnion.mpr ⟨c, hc', h_in_Sc⟩
      have h2 : T'.card ≤ S_union.card := Finset.card_le_card h1
      have h3 : S_union.card ≤ ∑ c ∈ C', (S_c c).card := Finset.card_biUnion_le
      have h4 : ∀ c ∈ C', (S_c c).card ≤ 3 := by
        intro c _
        let S_set : Set ℝ := (S_c c : Set ℝ)
        have h_set_eq : S_set = T ∩ Metric.closedBall c δ := by
          ext y
          simp [S_c, S_set]
          <;> tauto
        have h5 : (T ∩ Metric.closedBall c δ).encard ≤ 3 := (grid_set_ball_at_most_3 hδ hT (x := c)).2
        have h_fin : S_set.Finite := by
          rw [h_set_eq]
          exact (grid_set_ball_at_most_3 hδ hT (x := c)).1
        have h_encard : S_set.encard = ↑(S_c c).card := by
          have h1 : S_set.encard = ↑S_set.ncard := Set.Finite.encard_eq_coe h_fin
          have h2 : S_set.ncard = (S_c c).card := by
            simpa [S_set] using rfl
          rw [h1, h2]
        have h6 : S_set.encard ≤ 3 := by
          rw [h_set_eq]
          exact h5
        rw [h_encard] at h6
        exact_mod_cast h6
      have h_sum : (∑ c ∈ C', (S_c c).card) ≤ C'.card * 3 := by
        calc ∑ c ∈ C', (S_c c).card
          ≤ ∑ c ∈ C', 3 := Finset.sum_le_sum h4
        _ = C'.card * 3 := by simp [Finset.sum_const] <;> ring
      have h_total : T'.card ≤ 3 * C'.card := by linarith
      have hT_ncard : T.ncard = T'.card := by
        have h : T.ncard = (T' : Set ℝ).ncard := by rw [h_coe_T]
        rw [h]
        simp
      have h_encard : (T.encard : ENNReal) = ↑T'.card := by
        have h : T.encard = ↑T.ncard := Set.Finite.encard_eq_coe hT_fin
        rw [h, hT_ncard] <;> rfl
      rw [h_encard]
      have hC_ncard : C.ncard = C'.card := by
        have h_coe_C : (C' : Set ℝ) = C := hCfin.coe_toFinset
        have h : C.ncard = ((C' : Set ℝ)).ncard := by rw [h_coe_C]
        rw [h]
        simp
      have hCcard : (C.encard : ENNReal) = ↑C'.card := by
        have h9 : C.encard = ↑C.ncard := Set.Finite.encard_eq_coe hCfin
        rw [h9, hC_ncard] <;> rfl
      rw [hC_eq] at hCcard
      rw [hCcard]
      have h : (↑T'.card : ENNReal) ≤ (3 : ENNReal) * (↑C'.card : ENNReal) := by
        exact_mod_cast h_total
      exact h

/-! ### δ-separated set covering bounds in ℝ -/

/-- A δ-separated subset of ℝ intersects a closed δ-ball in at most 3 points. -/
lemma separated_set_ball_at_most_3 {δ : ℝ} (hδ : 0 < δ)
    {S : Set ℝ} (hS_sep : Metric.IsSeparated δ.toNNReal S) {x : ℝ} :
    (S ∩ Metric.closedBall x δ).Finite ∧
    (S ∩ Metric.closedBall x δ).encard ≤ 3 := by
  classical
  let B := S ∩ Metric.closedBall x δ
  let f : ℝ → ℤ := fun y => ⌊(y - (x - δ)) / δ⌋
  have h_inj : Set.InjOn f B := by
    intro y hy z hz h_eq
    by_contra hyz
    have h_yb : dist y x ≤ δ := (Metric.mem_closedBall).mp hy.2
    have h_zb : dist z x ≤ δ := (Metric.mem_closedBall).mp hz.2
    have h_y_abs : |y - x| ≤ δ := by simpa [dist_eq_norm] using h_yb
    have h_z_abs : |z - x| ≤ δ := by simpa [dist_eq_norm] using h_zb
    have h_y1 : x - δ ≤ y := by linarith [abs_le.mp h_y_abs]
    have h_y2 : y ≤ x + δ := by linarith [abs_le.mp h_y_abs]
    have h_z1 : x - δ ≤ z := by linarith [abs_le.mp h_z_abs]
    have h_z2 : z ≤ x + δ := by linarith [abs_le.mp h_z_abs]
    have h_fy_lower : (f y : ℝ) ≤ (y - (x - δ)) / δ := Int.floor_le _
    have h_fy_upper : (y - (x - δ)) / δ < (f y : ℝ) + 1 := Int.lt_floor_add_one _
    have h_fz_lower : (f z : ℝ) ≤ (z - (x - δ)) / δ := Int.floor_le _
    have h_fz_upper : (z - (x - δ)) / δ < (f z : ℝ) + 1 := Int.lt_floor_add_one _
    have h_k : f z = f y := h_eq.symm
    rw [h_k] at h_fz_lower h_fz_upper
    have h_diff : |y - z| < δ := by
      let k : ℝ := (f y : ℝ)
      have ha1 : k ≤ (y - (x - δ)) / δ := h_fy_lower
      have ha2 : (y - (x - δ)) / δ < k + 1 := h_fy_upper
      have hb1 : k ≤ (z - (x - δ)) / δ := by simpa [h_k] using h_fz_lower
      have hb2 : (z - (x - δ)) / δ < k + 1 := by simpa [h_k] using h_fz_upper
      have h_abs : |(y - (x - δ)) / δ - (z - (x - δ)) / δ| < 1 := by
        rw [abs_lt]
        constructor
        · linarith
        · linarith
      have h_eq_diff : (y - (x - δ)) / δ - (z - (x - δ)) / δ = (y - z) / δ := by ring
      rw [h_eq_diff] at h_abs
      have h5 : |(y - z) / δ| = |y - z| / δ := by
        rw [abs_div, abs_of_pos hδ]
      rw [h5] at h_abs
      calc |y - z|
        = (|y - z| / δ) * δ := by field_simp [hδ.ne'] <;> ring
      _ < 1 * δ := by gcongr <;> linarith
      _ = δ := by ring
    have h_sep_edist : (↑δ.toNNReal : ENNReal) < edist y z := hS_sep hy.1 hz.1 hyz
    have h_sep_dist : δ < dist y z := by
      have h1 : edist y z = ENNReal.ofReal (dist y z) := by rw [edist_dist]
      have h2 : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by exact ENNReal.ofNNReal_toNNReal δ
      rw [h1, h2] at h_sep_edist
      have h_iff : ENNReal.ofReal δ < ENNReal.ofReal (dist y z) ↔ δ < dist y z :=
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)
      exact h_iff.mp h_sep_edist
    have h10 : dist y z = |y - z| := by simp [dist_eq_norm]
    rw [h10] at h_sep_dist
    linarith
  let k_min : ℤ := 0
  let k_max : ℤ := 2
  have h_range : ∀ y ∈ B, f y ∈ Finset.Icc k_min k_max := by
    intro y hy
    have h_yb : dist y x ≤ δ := (Metric.mem_closedBall).mp hy.2
    have h_y_abs : |y - x| ≤ δ := by simpa [dist_eq_norm] using h_yb
    have h1 : x - δ ≤ y := by linarith [abs_le.mp h_y_abs]
    have h2 : y ≤ x + δ := by linarith [abs_le.mp h_y_abs]
    have h3 : (0 : ℝ) ≤ (y - (x - δ)) / δ := by
      apply div_nonneg <;> linarith
    have h4 : (y - (x - δ)) / δ ≤ 2 := by
      have h41 : y - (x - δ) ≤ 2 * δ := by linarith
      have h : (y - (x - δ)) / δ ≤ (2 * δ) / δ := by gcongr
      have h2 : (2 * δ) / δ = 2 := by field_simp [hδ.ne'] <;> ring
      rw [h2] at h
      exact h
    have h5 : 0 ≤ f y := by
      have h51 : ((0 : ℤ) : ℝ) ≤ (y - (x - δ)) / δ := by exact_mod_cast h3
      have h52 : (0 : ℤ) ≤ f y := Int.le_floor.mpr h51
      exact_mod_cast h52
    have h6 : f y ≤ 2 := by
      have h61 : (f y : ℝ) ≤ (y - (x - δ)) / δ := Int.floor_le _
      have h62 : (f y : ℝ) ≤ 2 := by linarith
      exact_mod_cast h62
    exact Finset.mem_Icc.mpr ⟨h5, h6⟩
  have h_img_fin : Set.Finite (f '' B) := by
    have h_sub : f '' B ⊆ (Finset.Icc k_min k_max : Set ℤ) := by
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      exact h_range y hy
    exact Set.Finite.subset (Finset.finite_toSet _) h_sub
  have h_encard_image : (f '' B).encard = B.encard := h_inj.encard_image
  have hB_encard : B.encard ≠ ⊤ := by
    rw [←h_encard_image]
    exact (Set.Finite.encard_lt_top h_img_fin).ne
  have hB_fin : Set.Finite B := Set.encard_ne_top_iff.mp hB_encard
  have h_card : B.encard ≤ 3 := by
    rw [←h_encard_image]
    have h : (f '' B).encard ≤ (Finset.Icc k_min k_max : Set ℤ).encard :=
      Set.encard_mono (by
        intro z hz
        rcases hz with ⟨y, hy, rfl⟩
        exact h_range y hy)
    have h21 : (Finset.Icc (0 : ℤ) 2).card = 3 := by decide
    have h2 : (Finset.Icc k_min k_max : Set ℤ).encard = 3 := by
      exact_mod_cast h21
    rw [h2] at h
    exact h
  exact ⟨hB_fin, h_card⟩

/-- For a δ-separated subset S ⊆ A in ℝ, |S| ≤ 3 * externalCoveringNumber δ A. -/
lemma separated_set_cover_bound {δ : ℝ} (hδ : 0 < δ)
    {S A : Set ℝ} (hS_sub : S ⊆ A) (hS_sep : Metric.IsSeparated δ.toNNReal S)
    (hA_bdd : Bornology.IsBounded A) :
    (S.encard : ENNReal) ≤ 3 * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
  have h_pack_fin : Metric.packingNumber δ.toNNReal A ≠ ⊤ := bounded_packing_finite hδ hA_bdd
  have h1 : Metric.externalCoveringNumber δ.toNNReal A ≤ Metric.coveringNumber δ.toNNReal A :=
    Metric.externalCoveringNumber_le_coveringNumber _ _
  have h2 : Metric.coveringNumber δ.toNNReal A ≤ Metric.packingNumber δ.toNNReal A :=
    Metric.coveringNumber_le_packingNumber _ _
  have h_ext_le : Metric.externalCoveringNumber δ.toNNReal A ≤ Metric.packingNumber δ.toNNReal A :=
    h1.trans h2
  have h_ext_fin : Metric.externalCoveringNumber δ.toNNReal A ≠ ⊤ := by
    by_contra h4
    have h51 : (⊤ : ℕ∞) ≤ Metric.packingNumber δ.toNNReal A := by
      simpa [h4] using h_ext_le
    have h52 : Metric.packingNumber δ.toNNReal A ≤ (⊤ : ℕ∞) := le_top
    have h5 : Metric.packingNumber δ.toNNReal A = ⊤ := le_antisymm h52 h51
    exact h_pack_fin h5
  rcases DiscretisedFurstenbergEstimate.CoveringUtils.exists_external_cover_eq (lt_top_iff_ne_top.mpr h_ext_fin) with ⟨C, hC, hC_eq⟩
  by_cases hCinf : C.encard = ⊤
  · rw [hC_eq] at hCinf; rw [hCinf] <;> simp
  · have hCfin : Set.Finite C := Set.encard_ne_top_iff.mp hCinf
    let C' := hCfin.toFinset
    have hS_fin : Set.Finite S := by
      have h1 : S.encard ≤ Metric.packingNumber δ.toNNReal A := by exact Metric.IsSeparated.encard_le_packingNumber hS_sub hS_sep
      have h2 : S.encard ≠ ⊤ := by
        by_contra h3
        have h41 : (⊤ : ℕ∞) ≤ Metric.packingNumber δ.toNNReal A := by
          simpa [h3] using h1
        have h42 : Metric.packingNumber δ.toNNReal A ≤ (⊤ : ℕ∞) := le_top
        have h4 : Metric.packingNumber δ.toNNReal A = ⊤ := le_antisymm h42 h41
        exact h_pack_fin h4
      exact Set.encard_ne_top_iff.mp h2
    let S_finset := hS_fin.toFinset
    let T_c : ℝ → Finset ℝ := fun c =>
      (separated_set_ball_at_most_3 hδ hS_sep (x := c)).1.toFinset
    let T_union : Finset ℝ := C'.biUnion T_c
    have h_coe_S : (S_finset : Set ℝ) = S := hS_fin.coe_toFinset
    have h1 : S_finset ⊆ T_union := by
      intro x hx
      have h_x_in_S : x ∈ S := by rw [←h_coe_S] <;> exact hx
      rcases hC (hS_sub h_x_in_S) with ⟨c, hc, hedist⟩
      have hc' : c ∈ C' := by simpa [C'] using hc
      have h_edist : edist x c ≤ ↑δ.toNNReal := hedist
      have hdist : dist x c ≤ δ := by
        rw [edist_dist] at h_edist
        have h_eq : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by exact ENNReal.ofNNReal_toNNReal δ
        rw [h_eq] at h_edist
        have h_edist' : ENNReal.ofReal (dist x c) ≤ ENNReal.ofReal δ := by
          simpa [edist_dist, dist_nonneg] using h_edist
        exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h_edist'
      have h_in_Tc : x ∈ T_c c := by
        simpa [T_c] using ⟨h_x_in_S, Metric.mem_closedBall.mpr hdist⟩
      exact Finset.mem_biUnion.mpr ⟨c, hc', h_in_Tc⟩
    have h2 : S_finset.card ≤ T_union.card := Finset.card_le_card h1
    have h3 : T_union.card ≤ ∑ c ∈ C', (T_c c).card := Finset.card_biUnion_le
    have h4 : ∀ c ∈ C', (T_c c).card ≤ 3 := by
      intro c _
      let T_set : Set ℝ := (T_c c : Set ℝ)
      have h_set_eq : T_set = S ∩ Metric.closedBall c δ := by
        ext y; simp [T_c, T_set] <;> tauto
      have h5 : (S ∩ Metric.closedBall c δ).encard ≤ 3 := (separated_set_ball_at_most_3 hδ hS_sep (x := c)).2
      have h_fin : T_set.Finite := by
        rw [h_set_eq]
        exact (separated_set_ball_at_most_3 hδ hS_sep (x := c)).1
      have h_encard : T_set.encard = ↑(T_c c).card := by
        have h1 : T_set.encard = ↑T_set.ncard := Set.Finite.encard_eq_coe h_fin
        have h2 : T_set.ncard = (T_c c).card := by simpa [T_set] using rfl
        rw [h1, h2]
      have h6 : T_set.encard ≤ 3 := by rw [h_set_eq]; exact h5
      rw [h_encard] at h6
      exact_mod_cast h6
    have h_sum : (∑ c ∈ C', (T_c c).card) ≤ C'.card * 3 := by
      calc ∑ c ∈ C', (T_c c).card
        ≤ ∑ c ∈ C', 3 := Finset.sum_le_sum h4
      _ = C'.card * 3 := by simp [Finset.sum_const] <;> ring
    have h_total : S_finset.card ≤ 3 * C'.card := by linarith
    have hS_ncard : S.ncard = S_finset.card := by
      have h : S.ncard = (S_finset : Set ℝ).ncard := by rw [h_coe_S]
      rw [h] <;> simp
    have h_encard : (S.encard : ENNReal) = ↑S_finset.card := by
      have h : S.encard = ↑S.ncard := Set.Finite.encard_eq_coe hS_fin
      rw [h, hS_ncard] <;> rfl
    rw [h_encard]
    have hC_ncard : C.ncard = C'.card := by
      have h_coe_C : (C' : Set ℝ) = C := hCfin.coe_toFinset
      have h : C.ncard = (C' : Set ℝ).ncard := by rw [h_coe_C]
      rw [h] <;> simp
    have hCcard : (C.encard : ENNReal) = ↑C'.card := by
      have h9 : C.encard = ↑C.ncard := Set.Finite.encard_eq_coe hCfin
      rw [h9, hC_ncard] <;> rfl
    rw [hC_eq] at hCcard
    rw [hCcard]
    have h : (↑S_finset.card : ENNReal) ≤ (3 : ENNReal) * (↑C'.card : ENNReal) := by
      exact_mod_cast h_total
    exact h

/-! ### Transfer between ℝ and EuclideanSpace ℝ (Fin 1) -/

/-- External covering number is preserved by the canonical embedding ℝ → ℝ¹. -/
lemma extCov_mk1 (ε : NNReal) (A : Set ℝ) :
    Metric.externalCoveringNumber ε (Translation.mk1 '' A) = Metric.externalCoveringNumber ε A := by
  have h_inj : Function.Injective Translation.mk1 := by
    intro x y h
    have h1 : (Translation.mk1 x) 0 = (Translation.mk1 y) 0 := by rw [h]
    simpa [Translation.mk1_apply] using h1
  have h_dist_eq : ∀ (x y : ℝ), dist (Translation.mk1 x) (Translation.mk1 y) = dist x y := by
    intro x y
    rw [Translation.dist1_eq, Translation.mk1_apply, Translation.mk1_apply]
    <;> simp [dist_eq_norm]
  have h1 : Metric.externalCoveringNumber ε (Translation.mk1 '' A) ≤ Metric.externalCoveringNumber ε A := by
    have h : ∀ (C : Set ℝ), Metric.IsCover ε A C →
        Metric.externalCoveringNumber ε (Translation.mk1 '' A) ≤ C.encard := by
      intro C hC
      have h2 : Metric.IsCover ε (Translation.mk1 '' A) (Translation.mk1 '' C) := by
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        rcases hC hx with ⟨c, hc, hdist⟩
        have h_edist : edist (Translation.mk1 x) (Translation.mk1 c) ≤ ↑ε := by
          have h_eq : edist (Translation.mk1 x) (Translation.mk1 c) = edist x c := by
            rw [edist_dist, edist_dist, h_dist_eq]
          rw [h_eq]; exact hdist
        exact ⟨Translation.mk1 c, Set.mem_image_of_mem Translation.mk1 hc, h_edist⟩
      have h3 : (Translation.mk1 '' C).encard = C.encard := h_inj.encard_image C
      calc Metric.externalCoveringNumber ε (Translation.mk1 '' A)
        ≤ (Translation.mk1 '' C).encard := Metric.IsCover.externalCoveringNumber_le_encard h2
      _ = C.encard := h3
    simpa [Metric.externalCoveringNumber, le_iInf_iff] using h
  have h2 : Metric.externalCoveringNumber ε A ≤ Metric.externalCoveringNumber ε (Translation.mk1 '' A) := by
    have h : ∀ (D : Set (EuclideanSpace ℝ (Fin 1))), Metric.IsCover ε (Translation.mk1 '' A) D →
        Metric.externalCoveringNumber ε A ≤ D.encard := by
      intro D hD
      let D' := (fun p : EuclideanSpace ℝ (Fin 1) => p 0) '' D
      have h2 : Metric.IsCover ε A D' := by
        intro x hx
        rcases hD (Set.mem_image_of_mem Translation.mk1 hx) with ⟨d, hd, hdist⟩
        let c := d 0
        have hc : c ∈ D' := ⟨d, hd, rfl⟩
        have h_edist : edist x c ≤ ↑ε := by
          have h_eq : edist x c = edist (Translation.mk1 x) d := by
            rw [edist_dist, edist_dist]
            have h_dist : dist x c = dist (Translation.mk1 x) d := by
              rw [Translation.dist1_eq]
              <;> simp [Translation.mk1_apply, c]
              <;> rfl
            rw [h_dist]
          rw [h_eq]; exact hdist
        exact ⟨c, hc, h_edist⟩
      have h_inj2 : Set.InjOn (fun p : EuclideanSpace ℝ (Fin 1) => p 0) D := by
        intro p _ q _ h
        have h4 : p 0 = q 0 := h
        have h5 : p = q := by
          ext i; fin_cases i <;> exact h4
        exact h5
      have h3 : D'.encard = D.encard := h_inj2.encard_image
      calc Metric.externalCoveringNumber ε A
        ≤ D'.encard := Metric.IsCover.externalCoveringNumber_le_encard h2
      _ = D.encard := h3
    simpa [Metric.externalCoveringNumber, le_iInf_iff] using h
  exact le_antisymm h1 h2

/-- Image of intersection with closed ball under mk1. -/
lemma ball_mk1 (A : Set ℝ) (x : ℝ) (r : ℝ) :
    Translation.mk1 '' (A ∩ Metric.closedBall x r) =
    (Translation.mk1 '' A) ∩ Metric.closedBall (Translation.mk1 x) r := by
  ext q
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    have hdist : dist (Translation.mk1 y) (Translation.mk1 x) ≤ r := by
      rw [Translation.dist1_eq, Translation.mk1_apply, Translation.mk1_apply]
      exact (Metric.mem_closedBall).mp hy2
    exact ⟨Set.mem_image_of_mem Translation.mk1 hy1, Metric.mem_closedBall.mpr hdist⟩
  · rintro ⟨⟨y, hy, rfl⟩, hq⟩
    have hdist : dist y x ≤ r := by
      have h : dist (Translation.mk1 y) (Translation.mk1 x) ≤ r := (Metric.mem_closedBall).mp hq
      rw [Translation.dist1_eq, Translation.mk1_apply, Translation.mk1_apply] at h
      exact h
    exact ⟨y, ⟨hy, Metric.mem_closedBall.mpr hdist⟩, rfl⟩

/-- productLikeRealLineCopy A = mk1 '' A. -/
lemma productLikeRealLineCopy_eq_image (A : Set ℝ) :
    productLikeRealLineCopy A = Translation.mk1 '' A := by
  ext p
  simp [productLikeRealLineCopy, Translation.mk1_apply]
  constructor
  · intro h
    refine ⟨p 0, h, ?_⟩
    ext i; fin_cases i <;> simp [Translation.mk1_apply]
  · rintro ⟨x, hx, rfl⟩
    simpa [Translation.mk1_apply] using hx

/-! ### Main grid-snapping theorem -/

/-- Snap a bounded 1D S-set to the δ-grid, obtaining a grid SC-set. -/
theorem sset_to_grid_scset {δ s C : ℝ} (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hC : 0 < C)
    {A : Set ℝ} (hA_sub : A ⊆ Set.Icc (0 : ℝ) 1)
    (hA_bdd : Bornology.IsBounded A)
    (hA_nonempty : A.Nonempty)
    (hA : IsDeltaSSet δ s C A) :
    ∃ (A_grid : Set ℝ),
      A_grid ⊆ productLikeUnitGrid δ ∧
      IsProductLikeRealDeltaSCSet δ s (C * 100) A_grid ∧
      (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal) ≥
        (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) / 100 ∧
      (∀ g ∈ A_grid, ∃ a ∈ A, |g - a| ≤ δ) := by
  classical
  -- Step 1: Maximal δ-separated subset S of A
  let S := Metric.maximalSeparatedSet δ.toNNReal A
  have hS_sub : S ⊆ A := Metric.maximalSeparatedSet_subset
  have hS_sep : Metric.IsSeparated δ.toNNReal S := Metric.isSeparated_maximalSeparatedSet
  have h_pack_fin : Metric.packingNumber δ.toNNReal A ≠ ⊤ := bounded_packing_finite hδ hA_bdd
  have hS_cover : Metric.IsCover δ.toNNReal A S := Metric.isCover_maximalSeparatedSet h_pack_fin
  have hS_encard_eq : S.encard = Metric.packingNumber δ.toNNReal A := Metric.encard_maximalSeparatedSet h_pack_fin
  have hS_fin : Set.Finite S := Set.encard_ne_top_iff.mp (by rw [hS_encard_eq]; exact h_pack_fin)
  have hS_nonempty : S.Nonempty := by
    rcases hA_nonempty with ⟨x, hx⟩
    have h3 : ({x} : Set ℝ).encard ≤ S.encard :=
      Metric.encard_le_of_isSeparated (Set.singleton_subset_iff.mpr hx)
        (by intro a ha b hb hne; exfalso; simp_all [Set.mem_singleton_iff] <;> tauto)
        h_pack_fin
    have h4 : 0 < Metric.packingNumber δ.toNNReal A := by
      have h5 : ({x} : Set ℝ).encard = 1 := by simp
      rw [h5] at h3
      rw [hS_encard_eq] at h3
      exact zero_lt_one.trans_le h3
    rw [←hS_encard_eq] at h4
    by_contra h
    have h_empty : S = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h
    rw [h_empty] at h4
    simp at h4

  -- Step 2: Snap function and A_grid
  let snap : ℝ → ℝ := fun x => δ * ⌊x / δ⌋
  let A_grid := snap '' S

  -- Step 3: snap properties
  have h_snap_lower : ∀ x : ℝ, snap x ≤ x := by
    intro x
    have h1 : ⌊x / δ⌋ ≤ x / δ := Int.floor_le _
    have h2 : δ * ⌊x / δ⌋ ≤ δ * (x / δ) := by gcongr
    have h3 : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
    linarith
  have h_snap_upper : ∀ x : ℝ, x < snap x + δ := by
    intro x
    have h1 : x / δ < ⌊x / δ⌋ + 1 := Int.lt_floor_add_one _
    have h2 : x < δ * (⌊x / δ⌋ + 1) := by
      calc x = δ * (x / δ) := by field_simp [hδ.ne'] <;> ring
           _ < δ * (⌊x / δ⌋ + 1) := by gcongr
    have h3 : δ * (⌊x / δ⌋ + 1) = snap x + δ := by ring
    linarith
  have h_snap_dist : ∀ x : ℝ, |snap x - x| < δ := by
    intro x
    have h1 : snap x ≤ x := h_snap_lower x
    have h2 : x < snap x + δ := h_snap_upper x
    rw [abs_lt] <;> constructor <;> linarith
  have h_snap_grid : ∀ x : ℝ, snap x ∈ productLikeIntegerGrid δ := by
    intro x; exact ⟨⌊x / δ⌋, by ring⟩
  have h_snap_in_unit : ∀ x ∈ Set.Icc (0 : ℝ) 1, snap x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    have h1 : 0 ≤ x := hx.1
    have h2 : x ≤ 1 := hx.2
    have h3 : 0 ≤ snap x := by
      have h4 : 0 ≤ x / δ := by positivity
      have h5 : (0 : ℤ) ≤ ⌊x / δ⌋ := by exact Int.floor_nonneg.mpr h4
      have h6 : 0 ≤ δ * ⌊x / δ⌋ := by positivity
      exact h6
    have h4 : snap x ≤ x := h_snap_lower x
    exact ⟨h3, by linarith⟩

  -- Step 4: A_grid ⊆ productLikeUnitGrid δ
  have h3 : A_grid ⊆ productLikeUnitGrid δ := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h_x_in_A : x ∈ A := hS_sub hx
    have h_x_in_Icc : x ∈ Set.Icc (0 : ℝ) 1 := hA_sub h_x_in_A
    exact ⟨h_snap_grid x, h_snap_in_unit x h_x_in_Icc⟩
  have h3_grid : A_grid ⊆ productLikeIntegerGrid δ := by
    intro y hy; exact (h3 hy).1

  -- Step 5: snap injective on S
  have h4 : Set.InjOn snap S := by
    intro x hx y hy h_eq
    by_contra hyz
    have h_snap_eq : δ * ⌊x / δ⌋ = δ * ⌊y / δ⌋ := by
      simpa [snap] using h_eq
    have h_k : ⌊x / δ⌋ = ⌊y / δ⌋ := by
      have h_snap_eq' : (δ : ℝ) * (⌊x / δ⌋ : ℝ) = (δ : ℝ) * (⌊y / δ⌋ : ℝ) := by exact_mod_cast h_snap_eq
      have h_k' : (⌊x / δ⌋ : ℝ) = (⌊y / δ⌋ : ℝ) := by
        apply mul_left_cancel₀ hδ.ne'
        exact h_snap_eq'
      exact_mod_cast h_k'
    have h_x1 : δ * ⌊x / δ⌋ ≤ x := h_snap_lower x
    have h_x2 : x < δ * ⌊x / δ⌋ + δ := h_snap_upper x
    have h_y1 : δ * ⌊y / δ⌋ ≤ y := h_snap_lower y
    have h_y2 : y < δ * ⌊y / δ⌋ + δ := h_snap_upper y
    have h_y1' : δ * ⌊x / δ⌋ ≤ y := by
      rw [h_k] at *; exact h_y1
    have h_y2' : y < δ * ⌊x / δ⌋ + δ := by
      rw [h_k] at *; exact h_y2
    have h_diff : |x - y| < δ := by
      rw [abs_lt] <;> constructor <;> linarith
    have h_sep_edist : (↑δ.toNNReal : ENNReal) < edist x y := hS_sep hx hy hyz
    have h_iff : ENNReal.ofReal δ < ENNReal.ofReal (dist x y) ↔ δ < dist x y :=
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)
    have h1 : edist x y = ENNReal.ofReal (dist x y) := by rw [edist_dist]
    have h2 : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by exact ENNReal.ofNNReal_toNNReal δ
    rw [h1, h2] at h_sep_edist
    have h_sep_dist : δ < dist x y := h_iff.mp h_sep_edist
    have h10 : dist x y = |x - y| := by simp [dist_eq_norm]
    rw [h10] at h_sep_dist
    linarith

  -- Step 6: A_grid finite and nonempty
  have hA_grid_fin : Set.Finite A_grid := hS_fin.image _
  have hA_grid_nonempty : A_grid.Nonempty := by
    rcases hS_nonempty with ⟨x, hx⟩
    exact ⟨snap x, ⟨x, hx, rfl⟩⟩

  -- Step 7: Covering number bound
  have h_encard_eq : A_grid.encard = S.encard := h4.encard_image
  have h_extA_le_S1 : Metric.externalCoveringNumber δ.toNNReal A ≤ S.encard :=
    hS_cover.externalCoveringNumber_le_encard
  have h_extA_le_S : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤ (S.encard : ENNReal) :=
    ENat.toENNReal_le.mpr h_extA_le_S1
  have h_grid_bound : (A_grid.encard : ENNReal) ≤ 3 * (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal) :=
    grid_set_cover_bound hδ h3_grid hA_grid_fin
  have h_cover_bound : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤
      3 * (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal) := by
    calc (Metric.externalCoveringNumber δ.toNNReal A : ENNReal)
      ≤ S.encard := h_extA_le_S
    _ = A_grid.encard := by rw [h_encard_eq]
    _ ≤ 3 * (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal) := h_grid_bound

  -- Step 8: S-set property of A_grid in ℝ
  have hA_grid_Sset : IsDeltaSSet δ s (18 * C) A_grid := by
    have h18C_pos : 0 < 18 * C := by positivity
    refine ⟨hA_grid_nonempty, hδ, h18C_pos, hs, ?_⟩
    intro x r hδ_le_r
    let B := A_grid ∩ Metric.closedBall x r
    let S_pre := {s ∈ S | snap s ∈ Metric.closedBall x r}
    have hB_equiv : B = snap '' S_pre := by
      ext y
      simp only [B, S_pre, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨s, hs_in_S, rfl⟩, hdist⟩
        exact ⟨s, ⟨hs_in_S, hdist⟩, rfl⟩
      · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
        exact ⟨⟨s, hs1, rfl⟩, hs2⟩
    have hB_encard : B.encard = S_pre.encard := by
      rw [hB_equiv]
      have hS_pre_sub_S : S_pre ⊆ S := fun s hs => hs.1
      exact (h4.mono hS_pre_sub_S).encard_image
    have hS_pre_sub_ball : S_pre ⊆ S ∩ Metric.closedBall x (r + δ) := by
      intro s hs
      have h_s_in_S : s ∈ S := hs.1
      have h_snap_in : snap s ∈ Metric.closedBall x r := hs.2
      have h1 : dist (snap s) x ≤ r := (Metric.mem_closedBall).mp h_snap_in
      have h2 : dist s x ≤ r + δ := by
        have h_tri : dist s x ≤ dist s (snap s) + dist (snap s) x := dist_triangle _ _ _
        have h_abs : dist s (snap s) = |s - snap s| := by simp [dist_eq_norm]
        rw [h_abs] at h_tri
        have h_lt : |snap s - s| < δ := h_snap_dist s
        have h_abs : |s - snap s| = |snap s - s| := by
          have h : s - snap s = -(snap s - s) := by ring
          rw [h, abs_neg]
        have h_le : |s - snap s| + dist (snap s) x ≤ r + δ := by
          rw [h_abs]
          have h4 : |snap s - s| + dist (snap s) x < δ + r := by linarith [h_lt, h1]
          have h5 : δ + r = r + δ := by ring
          rw [h5] at h4
          exact le_of_lt h4
        exact h_tri.trans h_le
      exact ⟨h_s_in_S, Metric.mem_closedBall.mpr h2⟩
    have hS_pre_encard_le : S_pre.encard ≤ (S ∩ Metric.closedBall x (r + δ)).encard :=
      Set.encard_mono hS_pre_sub_ball
    have hA_inter_bdd : Bornology.IsBounded (A ∩ Metric.closedBall x (r + δ)) :=
      Bornology.IsBounded.subset hA_bdd (fun z hz => hz.1)
    have hS_inter_sub_Ainter : (S ∩ Metric.closedBall x (r + δ)) ⊆ (A ∩ Metric.closedBall x (r + δ)) := by
      intro z hz
      exact ⟨hS_sub hz.1, hz.2⟩
    have hS_inter_sep : Metric.IsSeparated δ.toNNReal (S ∩ Metric.closedBall x (r + δ)) :=
      hS_sep.mono (fun z hz => hz.1)
    have h_sep_bound : ((S ∩ Metric.closedBall x (r + δ)).encard : ENNReal) ≤
        3 * (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x (r + δ)) : ENNReal) :=
      separated_set_cover_bound hδ hS_inter_sub_Ainter hS_inter_sep hA_inter_bdd
    have hA_Sset : (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x (r + δ)) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (r + δ)) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) :=
      hA.2.2.2.2 x (r + δ) (by linarith)
    have h_rpow_le : (ENNReal.ofReal (r + δ)) ^ s ≤ ENNReal.ofReal 2 * (ENNReal.ofReal r) ^ s := by
      have h1 : r + δ ≤ 2 * r := by linarith
      have h2 : ENNReal.ofReal (r + δ) ≤ ENNReal.ofReal (2 * r) := ENNReal.ofReal_le_ofReal (by linarith)
      have h3 : (ENNReal.ofReal (r + δ)) ^ s ≤ (ENNReal.ofReal (2 * r)) ^ s := by gcongr
      have h4 : ENNReal.ofReal (2 * r) = ENNReal.ofReal 2 * ENNReal.ofReal r := by
        rw [ENNReal.ofReal_mul (by norm_num)] <;> ring
      rw [h4] at h3
      have h5 : (ENNReal.ofReal 2 * ENNReal.ofReal r) ^ s =
          (ENNReal.ofReal 2) ^ s * (ENNReal.ofReal r) ^ s := by
        rw [ENNReal.mul_rpow_of_ne_top (by simp) (by simp)]
      rw [h5] at h3
      have h6 : (ENNReal.ofReal 2) ^ s ≤ ENNReal.ofReal 2 := by
        have h7 : (2 : ℝ) ^ s ≤ 2 := by
          have h8 : 0 ≤ s := hs
          have h9 : s ≤ 1 := hs1
          have h10 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
          have h11 : (2 : ℝ) ^ s ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h9
          have h12 : (2 : ℝ) ^ (1 : ℝ) = 2 := by norm_num
          rw [h12] at h11
          exact h11
        have h13 : (ENNReal.ofReal 2) ^ s = ENNReal.ofReal ((2 : ℝ) ^ s) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num) hs]
        rw [h13]
        exact ENNReal.ofReal_le_ofReal h7
      calc (ENNReal.ofReal (r + δ)) ^ s
        ≤ (ENNReal.ofReal 2) ^ s * (ENNReal.ofReal r) ^ s := h3
      _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal r) ^ s := by gcongr <;> exact h6
    have hB_fin' : Set.Finite B := hA_grid_fin.subset (show B ⊆ A_grid from by simp [B])
    have h_ext_le_encard1 : Metric.externalCoveringNumber δ.toNNReal B ≤ B.encard :=
      Metric.externalCoveringNumber_le_encard_self B
    have h_ext_le_encard : (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) ≤ (B.encard : ENNReal) :=
      ENat.toENNReal_le.mpr h_ext_le_encard1
    have h_final : (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) ≤
        ENNReal.ofReal (18 * C) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal) := by
      calc (Metric.externalCoveringNumber δ.toNNReal B : ENNReal)
        ≤ (B.encard : ENNReal) := h_ext_le_encard
      _ = (S_pre.encard : ENNReal) := by
        exact congr_arg (fun x : ENat => (x : ENNReal)) hB_encard
      _ ≤ ((S ∩ Metric.closedBall x (r + δ)).encard : ENNReal) :=
        ENat.toENNReal_le.mpr hS_pre_encard_le
      _ ≤ 3 * (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x (r + δ)) : ENNReal) := h_sep_bound
      _ ≤ 3 * (ENNReal.ofReal C * (ENNReal.ofReal (r + δ)) ^ s *
              (Metric.externalCoveringNumber δ.toNNReal A : ENNReal)) := by gcongr
      _ ≤ 3 * (ENNReal.ofReal C * (ENNReal.ofReal 2 * (ENNReal.ofReal r) ^ s) *
              (Metric.externalCoveringNumber δ.toNNReal A : ENNReal)) := by gcongr
      _ = (3 * ENNReal.ofReal C * ENNReal.ofReal 2) * (ENNReal.ofReal r) ^ s *
              (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
        ac_rfl
      _ ≤ (3 * ENNReal.ofReal C * ENNReal.ofReal 2) * (ENNReal.ofReal r) ^ s *
              (3 * (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal)) := by gcongr
      _ = ENNReal.ofReal (18 * C) * (ENNReal.ofReal r) ^ s *
              (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal) := by
        have h_const18 : (3 * ENNReal.ofReal C * ENNReal.ofReal 2) * (3 : ENNReal) = ENNReal.ofReal (18 * C) := by
          have h1 : (3 : ENNReal) = ENNReal.ofReal 3 := by norm_cast
          rw [h1]
          have h2 : ENNReal.ofReal 3 * ENNReal.ofReal C * ENNReal.ofReal 2 * ENNReal.ofReal 3 =
              ENNReal.ofReal (3 * C * 2 * 3) := by
            rw [←ENNReal.ofReal_mul (by positivity), ←ENNReal.ofReal_mul (by positivity), ←ENNReal.ofReal_mul (by positivity)]
            <;> rfl
          rw [h2]
          have h3 : (3 * C * 2 * 3 : ℝ) = 18 * C := by ring
          rw [h3]
        have h_assoc : (3 * ENNReal.ofReal C * ENNReal.ofReal 2) * (ENNReal.ofReal r) ^ s * (3 * (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal)) =
            ((3 * ENNReal.ofReal C * ENNReal.ofReal 2) * (3 : ENNReal)) * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal) := by
          ac_rfl
        rw [h_assoc, h_const18]
    exact h_final

  -- Step 9: Transfer S-set to EuclideanSpace
  let P_grid := productLikeRealLineCopy A_grid
  have hP_eq : P_grid = Translation.mk1 '' A_grid := productLikeRealLineCopy_eq_image A_grid
  have hP_grid_Sset : IsDeltaSSet δ s (18 * C) P_grid := by
    rw [hP_eq]
    have h1 : (Translation.mk1 '' A_grid).Nonempty := hA_grid_nonempty.image Translation.mk1
    refine ⟨h1, hδ, by positivity, hs, ?_⟩
    intro p r hδ_le_r
    let x : ℝ := p 0
    have h_ball : Translation.mk1 '' (A_grid ∩ Metric.closedBall x r) =
        (Translation.mk1 '' A_grid) ∩ Metric.closedBall p r := by
      have h_eq_p : p = Translation.mk1 x := by
        ext i
        fin_cases i
        · simp [Translation.mk1_apply] <;> rfl
      rw [h_eq_p]
      exact ball_mk1 A_grid x r
    have h_transfer1 : Metric.externalCoveringNumber δ.toNNReal ((Translation.mk1 '' A_grid) ∩ Metric.closedBall p r) =
        Metric.externalCoveringNumber δ.toNNReal (A_grid ∩ Metric.closedBall x r) := by
      rw [←h_ball]
      exact extCov_mk1 δ.toNNReal (A_grid ∩ Metric.closedBall x r)
    have h_transfer2 : Metric.externalCoveringNumber δ.toNNReal (Translation.mk1 '' A_grid) =
        Metric.externalCoveringNumber δ.toNNReal A_grid := extCov_mk1 δ.toNNReal A_grid
    rw [h_transfer1, h_transfer2]
    exact hA_grid_Sset.2.2.2.2 x r hδ_le_r

  -- Step 10: Translate to SC-set
  have hA_grid_bdd : Bornology.IsBounded A_grid := Set.Finite.isBounded hA_grid_fin
  have hP_bdd : Bornology.IsBounded P_grid := by
    rw [hP_eq]
    have h_mk1_dist : ∀ (x y : ℝ), dist (Translation.mk1 x) (Translation.mk1 y) = dist x y := by
      intro x y
      rw [Translation.dist1_eq]
      <;> simp [Translation.mk1_apply] <;> rfl
    have h_mk1_lip : LipschitzWith (1 : NNReal) Translation.mk1 := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [h_mk1_dist x y] <;> simp
    exact h_mk1_lip.isBounded_image hA_grid_bdd
  have hSC : IsDeltaSCSet (d := 1) δ s (3 * (18 * C)) P_grid :=
    DiscretisedFurstenbergEstimate.Translation.isDeltaSSet_to_isDeltaSCSet1 hP_grid_Sset hδ_dyadic hP_bdd hs1
  have h_const : 3 * (18 * C) ≤ C * 100 := by
    have h : 3 * (18 * C) = 54 * C := by ring
    rw [h]
    have h2 : 0 ≤ C := by linarith
    nlinarith
  have hSC' : IsDeltaSCSet (d := 1) δ s (C * 100) P_grid := by
    rcases hSC with ⟨h_bdd, h_ne, h_d, h_δdy, h_δpos, h_snonneg, h_sle, h_C1pos, h_main⟩
    have h_C2pos : 0 < C * 100 := by positivity
    refine ⟨h_bdd, h_ne, h_d, h_δdy, h_δpos, h_snonneg, h_sle, h_C2pos, ?_⟩
    intro r Q hrQ hQ hδr hr1
    have h9 := h_main hrQ hQ hδr hr1
    have h10 : ENNReal.ofReal (3 * (18 * C)) ≤ ENNReal.ofReal (C * 100) := ENNReal.ofReal_le_ofReal (by linarith)
    calc ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (P_grid ∩ Q))
      ≤ ENNReal.ofReal (3 * (18 * C)) * ENat.toENNReal (dyadicCoveringNumber (d := 1) δ P_grid) * ENNReal.ofReal (r ^ s) := h9
    _ ≤ ENNReal.ofReal (C * 100) * ENat.toENNReal (dyadicCoveringNumber (d := 1) δ P_grid) * ENNReal.ofReal (r ^ s) := by gcongr
  have h_final : IsProductLikeRealDeltaSCSet δ s (C * 100) A_grid := hSC'
  have h_cover100 : (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal) ≥
      (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) / 100 := by
    have h : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤
        3 * (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal) := h_cover_bound
    have h_div3 : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) / 3 ≤
        (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal) := by
      have h4 : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) / 3 ≤
          (3 * (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal)) / 3 := by gcongr
      have h5 : (3 * (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal)) / 3 =
          (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal) := by
        have h6 : (3 : ENNReal) ≠ 0 := by norm_num
        have h7 : (3 : ENNReal) ≠ ⊤ := by norm_num
        have h_comm : (3 * (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal)) / 3 =
            ((Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal) * 3) / 3 := by
          rw [mul_comm]
        rw [h_comm]
        exact ENNReal.mul_div_cancel_right h6 h7
      rw [h5] at h4
      exact h4
    have h2 : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) / 100 ≤
        (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) / 3 := by
      gcongr <;> norm_num
    exact h2.trans h_div3
  have h_proximity : ∀ g ∈ A_grid, ∃ a ∈ A, |g - a| ≤ δ := by
    intro g hg
    rcases hg with ⟨x, hx, rfl⟩
    have h_x_in_A : x ∈ A := hS_sub hx
    have h : |snap x - x| < δ := h_snap_dist x
    exact ⟨x, h_x_in_A, by linarith [abs_lt.mp h]⟩
  exact ⟨A_grid, h3, h_final, h_cover100, h_proximity⟩

end DiscretisedFurstenbergEstimate.GridSnap
