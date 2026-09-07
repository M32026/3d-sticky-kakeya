module

/-
  Proof of h7c covering bound for ProductPropBounded.

  Given param_union ⊆ cthickening(r, e_plane_inv '' T'_union), prove
  covering(δ', param_union) ≤ 676 * covering(δ', T'_union),
  hence covering(T'_union) ≥ covering(param_union) / 1000.
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate

noncomputable section

-- ============================================================================
-- Identification between EuclideanSpace ℝ (Fin 2) and ℝ × ℝ
-- ============================================================================

/-- Map from Euclidean 2-space to pairs. -/
def e_plane (p : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ := (p 0, p 1)

/-- Map from pairs to Euclidean 2-space. -/
def e_plane_inv (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then p.1 else p.2)

/-- e_plane ∘ e_plane_inv = id. -/
lemma e_plane_comp_inv : e_plane ∘ e_plane_inv = id := by
  funext p
  apply Prod.ext
  · simp [e_plane, e_plane_inv]
  · simp [e_plane, e_plane_inv]

/-- e_plane_inv ∘ e_plane = id. -/
lemma e_plane_inv_comp : e_plane_inv ∘ e_plane = id := by
  funext x
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [e_plane, e_plane_inv] <;> aesop

/-- e_plane (e_plane_inv p) = p. -/
lemma e_plane_left_inverse (p : ℝ × ℝ) : e_plane (e_plane_inv p) = p := by
  have h := congr_fun e_plane_comp_inv p
  exact h

/-- e_plane_inv (e_plane x) = x. -/
lemma e_plane_right_inverse (x : EuclideanSpace ℝ (Fin 2)) : e_plane_inv (e_plane x) = x := by
  have h := congr_fun e_plane_inv_comp x
  exact h

/-- Distance formula for Euclidean 2-space. -/
lemma euclidean2_dist (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y = Real.sqrt ((x 0 - y 0)^2 + (x 1 - y 1)^2) := by
  rw [PiLp.dist_eq_sum (show 0 < (2 : ENNReal).toReal by norm_num)]
  have h_toReal : (ENNReal.toReal 2 : ℝ) = 2 := by norm_num
  have h_sum : (∑ i : Fin 2, dist (x i) (y i) ^ ENNReal.toReal 2) =
      (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
    rw [h_toReal, Fin.sum_univ_two]
    have h1 : ∀ (a b : ℝ), dist a b ^ (2 : ℝ) = (a - b)^2 := by
      intro a b
      simp [Real.dist_eq, sq_abs]
      <;> ring
    rw [h1 (x 0) (y 0), h1 (x 1) (y 1)]
  rw [h_sum]
  have h_rpow : ((x 0 - y 0)^2 + (x 1 - y 1)^2 : ℝ) ^ (1 / ENNReal.toReal 2) =
      Real.sqrt ((x 0 - y 0)^2 + (x 1 - y 1)^2) := by
    rw [h_toReal]
    rw [Real.sqrt_eq_rpow]
    <;> ring
  exact h_rpow

/-- e_plane is 1-Lipschitz (Euclidean L2 → max metric). -/
lemma e_plane_one_lipschitz : LipschitzWith (1 : NNReal) e_plane := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let a := x 0 - y 0
  let b := x 1 - y 1
  have hdist : dist x y = Real.sqrt (a^2 + b^2) := euclidean2_dist x y
  have h1 : |a| ≤ dist x y := by
    rw [hdist]
    have h2 : a^2 ≤ a^2 + b^2 := by linarith [sq_nonneg b]
    have h3 : |a| ≤ Real.sqrt (a^2 + b^2) := by
      rw [abs_le]
      constructor <;> nlinarith [Real.sqrt_nonneg (a^2 + b^2), Real.sq_sqrt (show 0 ≤ a^2 + b^2 by positivity)]
    exact h3
  have h2 : |b| ≤ dist x y := by
    rw [hdist]
    have h3 : b^2 ≤ a^2 + b^2 := by linarith [sq_nonneg a]
    have h4 : |b| ≤ Real.sqrt (a^2 + b^2) := by
      rw [abs_le]
      constructor <;> nlinarith [Real.sqrt_nonneg (a^2 + b^2), Real.sq_sqrt (show 0 ≤ a^2 + b^2 by positivity)]
    exact h4
  simp [e_plane, Prod.dist_eq, max_le_iff] <;> exact ⟨h1, h2⟩

/-- e_plane_inv is sqrt(2)-Lipschitz (max metric → Euclidean L2). -/
lemma e_plane_inv_sqrt2_lipschitz :
    LipschitzWith (⟨Real.sqrt 2, by positivity⟩ : NNReal) e_plane_inv := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let dx := x.1 - y.1
  let dy := x.2 - y.2
  have h1 : dist (e_plane_inv x) (e_plane_inv y) = Real.sqrt (dx^2 + dy^2) := by
    rw [euclidean2_dist]
    have h2 : (e_plane_inv x) 0 - (e_plane_inv y) 0 = dx := by
      simp [e_plane_inv] <;> ring
    have h3 : (e_plane_inv x) 1 - (e_plane_inv y) 1 = dy := by
      simp [e_plane_inv] <;> ring
    rw [h2, h3]
  have h2 : dist x y = max (|dx|) (|dy|) := by
    simp [Prod.dist_eq] <;> rfl
  have h3 : dx^2 ≤ (dist x y)^2 := by
    rw [h2]
    have h4 : |dx| ≤ max (|dx|) (|dy|) := le_max_left _ _
    have h5 : |dx|^2 ≤ (max (|dx|) (|dy|))^2 := by gcongr
    have h6 : dx^2 = |dx|^2 := by
      rw [sq_abs]
    rw [h6]
    exact h5
  have h4 : dy^2 ≤ (dist x y)^2 := by
    rw [h2]
    have h5 : |dy| ≤ max (|dx|) (|dy|) := le_max_right _ _
    have h6 : |dy|^2 ≤ (max (|dx|) (|dy|))^2 := by gcongr
    have h7 : dy^2 = |dy|^2 := by rw [sq_abs]
    rw [h7]
    exact h6
  have h5 : Real.sqrt (dx^2 + dy^2) ≤ Real.sqrt 2 * dist x y := by
    have h6 : 0 ≤ dist x y := by positivity
    have h7 : dx^2 + dy^2 ≤ 2 * (dist x y)^2 := by linarith
    have h8 : Real.sqrt (dx^2 + dy^2) ≤ Real.sqrt (2 * (dist x y)^2) := Real.sqrt_le_sqrt h7
    have h9 : Real.sqrt (2 * (dist x y)^2) = Real.sqrt 2 * dist x y := by
      calc
        Real.sqrt (2 * (dist x y)^2)
          = Real.sqrt 2 * Real.sqrt ((dist x y)^2) := by
            rw [Real.sqrt_mul] <;> positivity
        _ = Real.sqrt 2 * dist x y := by
          rw [Real.sqrt_sq_eq_abs]
          rw [abs_of_nonneg h6]
    rw [h9] at h8
    exact h8
  rw [h1]
  exact h5

-- ============================================================================
-- Ball cover in ℝ × ℝ (max metric)
-- ============================================================================

/-- A ball of radius K*Δ in ℝ×ℝ (sup metric) can be covered by at most
    (ceil(2K)+1)^2 balls of radius Δ. -/
lemma ball_cover_prod (K Δ : ℝ) (hK_pos : 0 < K) (hΔ_pos : 0 < Δ) (x : ℝ × ℝ) :
    ∃ (C : Finset (ℝ × ℝ)),
      Metric.closedBall x (K * Δ) ⊆ ⋃ c ∈ (C : Set (ℝ × ℝ)), Metric.closedBall c Δ ∧
      C.card ≤ (Nat.ceil (2 * K) + 1)^2 := by
  let n : ℕ := Nat.ceil (2 * K) + 1
  let g : ℕ × ℕ → ℝ × ℝ := fun p =>
    (x.1 - K * Δ + (p.1 : ℝ) * Δ, x.2 - K * Δ + (p.2 : ℝ) * Δ)
  let C : Finset (ℝ × ℝ) := Finset.image g (Finset.range n ×ˢ Finset.range n)
  have h1 : C.card ≤ n^2 := by
    have h2 : C.card ≤ (Finset.range n ×ˢ Finset.range n).card := Finset.card_image_le
    have h3 : (Finset.range n ×ˢ Finset.range n).card = n * n := by
      simp [Finset.card_product] <;> ring
    rw [h3] at h2
    have h4 : n * n = n ^ 2 := by ring
    rw [h4] at h2
    exact h2
  have h_n_gt_2K : (n : ℝ) > 2 * K := by
    dsimp only [n]
    have h_cast : ((Nat.ceil (2 * K) + 1 : ℕ) : ℝ) = (Nat.ceil (2 * K) : ℝ) + 1 := by simp
    rw [h_cast]
    have h2 : (Nat.ceil (2 * K) : ℝ) ≥ 2 * K := Nat.le_ceil _
    linarith
  have h_index : ∀ (y_coord x_coord : ℝ), |y_coord - x_coord| ≤ K * Δ →
      ∃ i : ℕ, i < n ∧ |y_coord - (x_coord - K * Δ + (i : ℝ) * Δ)| ≤ Δ := by
    intro y_coord x_coord h_bound
    have h1 : y_coord - (x_coord - K * Δ) ∈ Set.Icc (0 : ℝ) (2 * K * Δ) := by
      have h11 : -K * Δ ≤ y_coord - x_coord := by
        have h := (abs_le.mp h_bound).1
        ring_nf at h ⊢ <;> exact h
      have h12 : y_coord - x_coord ≤ K * Δ := by
        have h := (abs_le.mp h_bound).2
        ring_nf at h ⊢ <;> exact h
      have h2 : 0 ≤ y_coord - (x_coord - K * Δ) := by
        have h_eq : y_coord - (x_coord - K * Δ) = y_coord - x_coord + K * Δ := by ring
        rw [h_eq] <;> linarith
      have h3 : y_coord - (x_coord - K * Δ) ≤ 2 * K * Δ := by
        have h_eq : y_coord - (x_coord - K * Δ) = y_coord - x_coord + K * Δ := by ring
        rw [h_eq] <;> linarith
      exact ⟨h2, h3⟩
    let t : ℝ := (y_coord - (x_coord - K * Δ)) / Δ
    have ht_nonneg : 0 ≤ t := by
      dsimp only [t]
      exact div_nonneg h1.1 (by linarith)
    have ht_le : t ≤ 2 * K := by
      dsimp only [t]
      have h4 : y_coord - (x_coord - K * Δ) ≤ 2 * K * Δ := h1.2
      have h5 : (y_coord - (x_coord - K * Δ)) / Δ ≤ (2 * K * Δ) / Δ := by gcongr
      have h6 : (2 * K * Δ) / Δ = 2 * K := by
        field_simp [hΔ_pos.ne'] <;> ring
      rw [h6] at h5
      exact h5
    let i : ℕ := Nat.floor t
    have hi1 : (i : ℝ) ≤ t := Nat.floor_le ht_nonneg
    have hi2 : t < (i : ℝ) + 1 := Nat.lt_floor_add_one t
    have hi3 : i < n := by
      have h7 : (i : ℝ) ≤ 2 * K := hi1.trans ht_le
      have h8 : (i : ℝ) < (n : ℝ) := by linarith [h_n_gt_2K]
      exact_mod_cast h8
    have h9 : (i : ℝ) * Δ ≤ y_coord - (x_coord - K * Δ) := by
      have h91 : (i : ℝ) ≤ t := hi1
      have h92 : (i : ℝ) * Δ ≤ t * Δ := mul_le_mul_of_nonneg_right h91 (by linarith)
      have h93 : t * Δ = y_coord - (x_coord - K * Δ) := by
        dsimp only [t]
        field_simp [hΔ_pos.ne'] <;> ring
      rw [h93] at h92
      exact h92
    have h10 : y_coord - (x_coord - K * Δ) < ((i : ℝ) + 1) * Δ := by
      have h101 : t * Δ < ((i : ℝ) + 1) * Δ := mul_lt_mul_of_pos_right hi2 hΔ_pos
      have h102 : t * Δ = y_coord - (x_coord - K * Δ) := by
        dsimp only [t]
        field_simp [hΔ_pos.ne'] <;> ring
      rw [h102] at h101
      exact h101
    have hdist : |y_coord - (x_coord - K * Δ + (i : ℝ) * Δ)| ≤ Δ := by
      rw [abs_le]
      constructor <;> linarith
    exact ⟨i, hi3, hdist⟩
  have h2 : ∀ y ∈ Metric.closedBall x (K * Δ), ∃ c ∈ C, dist y c ≤ Δ := by
    intro y hy
    have hdy : dist y x ≤ K * Δ := hy
    have hdy1 : |y.1 - x.1| ≤ K * Δ := by
      have h : dist y x = max (|y.1 - x.1|) (|y.2 - x.2|) := by
        simp [Prod.dist_eq] <;> rfl
      rw [h] at hdy
      exact le_trans (le_max_left _ _) hdy
    have hdy2 : |y.2 - x.2| ≤ K * Δ := by
      have h : dist y x = max (|y.1 - x.1|) (|y.2 - x.2|) := by
        simp [Prod.dist_eq] <;> rfl
      rw [h] at hdy
      exact le_trans (le_max_right _ _) hdy
    rcases h_index y.1 x.1 hdy1 with ⟨i, hi_lt, hi_dist⟩
    rcases h_index y.2 x.2 hdy2 with ⟨j, hj_lt, hj_dist⟩
    let c : ℝ × ℝ := g (i, j)
    have hc_in_C : c ∈ C := by
      apply Finset.mem_image.mpr
      have h_i_in : i ∈ Finset.range n := by simpa [Finset.mem_range] using hi_lt
      have h_j_in : j ∈ Finset.range n := by simpa [Finset.mem_range] using hj_lt
      exact ⟨(i, j), Finset.mem_product.mpr ⟨h_i_in, h_j_in⟩, rfl⟩
    have hdist_c : dist y c ≤ Δ := by
      simp [c, g, Prod.dist_eq]
      <;> exact ⟨hi_dist, hj_dist⟩
    exact ⟨c, hc_in_C, hdist_c⟩
  have h3 : Metric.closedBall x (K * Δ) ⊆ ⋃ c ∈ (C : Set (ℝ × ℝ)), Metric.closedBall c Δ := by
    intro y hy
    rcases h2 y hy with ⟨c, hc, hdist⟩
    exact Set.mem_iUnion₂.mpr ⟨c, hc, hdist⟩
  exact ⟨C, h3, h1⟩

-- ============================================================================
-- Doubling in Euclidean 2D
-- ============================================================================

/-- Doubling bound for Euclidean 2D: covering(ε, A) ≤ M * covering(K*ε, A)
    where M = (ceil(2*sqrt(2)*K)+1)^2. -/
lemma externalCoveringNumber_doubling_euclidean2d
    {A : Set (EuclideanSpace ℝ (Fin 2))} {K ε : ℝ}
    (hK_pos : 0 < K) (hε_pos : 0 < ε) (h : K * ε ≤ 12 * ε) :
    Metric.externalCoveringNumber ε.toNNReal A ≤
      ((Nat.ceil (2 * Real.sqrt 2 * K) + 1)^2 : ENNReal) *
      Metric.externalCoveringNumber (K * ε).toNNReal A := by
  let M : ℕ := (Nat.ceil (2 * Real.sqrt 2 * K) + 1)^2
  let ε' : ℝ := ε / Real.sqrt 2
  have hε'_pos : 0 < ε' := by positivity
  have hKε'_pos : 0 < K * ε / ε' := by positivity
  have h_radius_eq : (K * ε / ε') * ε' = K * ε := by
    dsimp only [ε']
    field_simp [hε_pos.ne'] <;> ring
  -- Key: cover Euclidean ball of radius K*ε by pulling back max-metric cover.
  have h_ball_cover : ∀ (x : EuclideanSpace ℝ (Fin 2)),
      ∃ (D : Finset (EuclideanSpace ℝ (Fin 2))),
        Metric.closedBall x (K * ε) ⊆ ⋃ d ∈ (D : Set _), Metric.closedBall d ε ∧
        D.card ≤ M := by
    intro x
    rcases ball_cover_prod (K * ε / ε') ε' hKε'_pos hε'_pos (e_plane x) with
      ⟨C, hC_cover, hC_card⟩
    let D : Finset (EuclideanSpace ℝ (Fin 2)) := Finset.image e_plane_inv C
    have hD_card : D.card ≤ C.card := Finset.card_image_le
    have h_main : Metric.closedBall x (K * ε) ⊆
        ⋃ d ∈ (D : Set _), Metric.closedBall d ε := by
      intro y hy
      have h1 : e_plane y ∈ Metric.closedBall (e_plane x) (K * ε) := by
        have h2 : dist (e_plane y) (e_plane x) ≤ (1 : ℝ) * dist y x :=
          e_plane_one_lipschitz.dist_le_mul y x
        have h3 : dist (e_plane y) (e_plane x) ≤ dist y x := by
          simpa using h2
        simpa using h3.trans hy
      have h1' : e_plane y ∈ Metric.closedBall (e_plane x) ((K * ε / ε') * ε') := by
        rw [h_radius_eq] at * <;> exact h1
      have h4 : e_plane y ∈ ⋃ c ∈ (C : Set (ℝ × ℝ)), Metric.closedBall c ε' := hC_cover h1'
      rcases Set.mem_iUnion₂.mp h4 with ⟨c, hc, hc_dist⟩
      let d := e_plane_inv c
      have hd_in_D : d ∈ D := Finset.mem_image_of_mem e_plane_inv hc
      have h3 : dist y d ≤ ε := by
        have h4 : dist (e_plane y) c ≤ ε' := hc_dist
        have h5 : dist y d ≤ Real.sqrt 2 * dist (e_plane y) c := by
          have h6 : dist (e_plane_inv (e_plane y)) (e_plane_inv c) ≤ Real.sqrt 2 * dist (e_plane y) c :=
            e_plane_inv_sqrt2_lipschitz.dist_le_mul (e_plane y) c
          have h7 : e_plane_inv (e_plane y) = y := e_plane_right_inverse y
          rw [h7] at h6
          exact h6
        have h8 : Real.sqrt 2 * ε' = ε := by
          dsimp only [ε']
          field_simp <;> ring
        calc dist y d ≤ Real.sqrt 2 * dist (e_plane y) c := h5
             _ ≤ Real.sqrt 2 * ε' := by gcongr
             _ = ε := h8
      exact Set.mem_iUnion₂.mpr ⟨d, hd_in_D, h3⟩
    have h_card : D.card ≤ M := by
      calc D.card ≤ C.card := hD_card
           _ ≤ (Nat.ceil (2 * (K * ε / ε')) + 1)^2 := hC_card
           _ = M := by
             have h_eq : K * ε / ε' = Real.sqrt 2 * K := by
               dsimp only [ε']
               field_simp <;> ring
             congr 1
             <;> rw [h_eq] <;> ring_nf
    exact ⟨D, h_main, h_card⟩
  -- Now standard doubling argument
  have h_main : ∀ (C : Set (EuclideanSpace ℝ (Fin 2))),
      Metric.IsCover (K * ε).toNNReal A C →
      Metric.externalCoveringNumber ε.toNNReal A ≤ (M : ENNReal) * C.encard := by
    intro C hC
    by_cases h_fin : C.Finite
    · let C' : Finset (EuclideanSpace ℝ (Fin 2)) := h_fin.toFinset
      have hC' : (C' : Set _) = C := h_fin.coe_toFinset
      choose D hD_cover hD_card using fun (c : EuclideanSpace ℝ (Fin 2)) =>
        h_ball_cover c
      let D_all : Finset (EuclideanSpace ℝ (Fin 2)) :=
        C'.biUnion (fun c => D c)
      have h_cover : Metric.IsCover ε.toNNReal A (D_all : Set _) := by
        have hC_sub : A ⊆ ⋃ c ∈ C, Metric.closedEBall c (K * ε).toNNReal :=
          Metric.isCover_iff_subset_iUnion_closedEBall.mp hC
        intro x hx
        have h61 : x ∈ ⋃ c ∈ C, Metric.closedEBall c (K * ε).toNNReal := hC_sub hx
        rcases Set.mem_iUnion₂.mp h61 with ⟨c, hc, hxc_edist⟩
        have hxc : dist x c ≤ K * ε := by
          have h : dist x c ≤ K * ε ∨ x = c := by
            simpa [Metric.mem_closedEBall] using hxc_edist
          rcases h with (h | rfl)
          · exact h
          · have h_pos : 0 ≤ K * ε := by positivity
            simpa [dist_self] using h_pos
        have hc' : c ∈ C' := by
          have h : c ∈ (C' : Set _) := by
            rw [hC'] <;> exact hc
          exact h
        have h_in_union : x ∈ ⋃ d ∈ (D c : Set _), Metric.closedBall d ε := hD_cover c hxc
        rcases Set.mem_iUnion₂.mp h_in_union with ⟨d, hd_in_Dc, hxd⟩
        have hdist : dist x d ≤ ε := hxd
        have hd_in_Dall : d ∈ (D_all : Set _) := by
          apply Finset.mem_biUnion.mpr
          exact ⟨c, hc', hd_in_Dc⟩
        have h_edist : edist x d ≤ ↑ε.toNNReal := by
          have hε_coe : (↑ε.toNNReal : ℝ) = ε := by
            rw [Real.coe_toNNReal']
            have h : max ε 0 = ε := by
              rw [max_eq_left] <;> linarith
            exact h
          rw [edist_le_coe, ←dist_le_coe, hε_coe]
          exact hdist
        exact ⟨d, hd_in_Dall, h_edist⟩
      have h_card : D_all.card ≤ M * C'.card := by
        calc D_all.card ≤ ∑ c ∈ C', (D c).card := Finset.card_biUnion_le
             _ ≤ ∑ c ∈ C', M := by gcongr <;> exact hD_card c
             _ = M * C'.card := by
               simp [Finset.sum_const, mul_comm]
      let D_all_set : Set (EuclideanSpace ℝ (Fin 2)) := ↑D_all
      have h9 : Metric.externalCoveringNumber ε.toNNReal A ≤ D_all_set.encard :=
        Metric.IsCover.externalCoveringNumber_le_encard h_cover
      have h10 : D_all_set.encard = ↑(D_all.card) :=
        Set.encard_coe_eq_coe_finsetCard D_all
      have h11 : C.encard = ↑(C'.card) := by
        have h12 : C = (C' : Set _) := hC'.symm
        rw [h12]
        exact Set.encard_coe_eq_coe_finsetCard C'
      have h9_enn : (Metric.externalCoveringNumber ε.toNNReal A : ENNReal) ≤ (M : ENNReal) * (C.encard : ENNReal) := by
        have h9_cast : (Metric.externalCoveringNumber ε.toNNReal A : ENNReal) ≤ (↑D_all.card : ENNReal) := by
          rw [h10] at h9
          exact_mod_cast h9
        have h_card_cast : (↑D_all.card : ENNReal) ≤ (M : ENNReal) * (↑(C'.card) : ENNReal) := by
          exact_mod_cast h_card
        have h11' : (C.encard : ENNReal) = ↑(C'.card) := by
          exact_mod_cast h11
        rw [h11']
        exact le_trans h9_cast h_card_cast
      exact h9_enn
    · have h_inf : C.encard = ⊤ := Set.encard_eq_top_iff.mpr h_fin
      have h_main_goal : (Metric.externalCoveringNumber ε.toNNReal A : ENNReal) ≤ (M : ENNReal) * (C.encard : ENNReal) := by
        rw [h_inf]
        have h_coerce : (↑(⊤ : ℕ∞) : ENNReal) = ⊤ := by simp
        rw [h_coerce]
        have h_mul_top : (M : ENNReal) * (⊤ : ENNReal) = ⊤ := by
          rw [ENNReal.mul_top (show (M : ENNReal) ≠ 0 from by positivity)]
        rw [h_mul_top]
        exact le_top
      exact_mod_cast h_main_goal
  by_cases h_top : Metric.externalCoveringNumber (K * ε).toNNReal A = ⊤
  · rw [h_top] <;> simp
  · have h_lt_top : Metric.externalCoveringNumber (K * ε).toNNReal A < ⊤ := by
      exact lt_top_iff_ne_top.mpr h_top
    rcases DiscretisedFurstenbergEstimate.CoveringUtils.exists_external_cover_eq h_lt_top with
      ⟨C, hC, h_eq⟩
    have h5 : Metric.externalCoveringNumber ε.toNNReal A ≤ (M : ENNReal) * C.encard :=
      h_main C hC
    have hM : (M : ENNReal) = ((Nat.ceil (2 * Real.sqrt 2 * K) + 1)^2 : ENNReal) := by
      simp [M] <;> rfl
    rw [hM] at h5
    rw [h_eq] at *
    <;> exact h5

-- ============================================================================
-- Main h7c covering bound
-- ============================================================================

/-- h7c: covering(T'_union) ≥ covering(param_union) / 1000.
    Assumes param_union is within distance sqrt(2)*9δ'/2 of e_plane_inv '' T'_union. -/
lemma h7c_covering_bound (δ' : ℝ) (hδ' : 0 < δ')
    (param_union : Set (EuclideanSpace ℝ (Fin 2)))
    (T'_union : Set (ℝ × ℝ))
    (h_thicken : param_union ⊆
      Metric.cthickening (Real.sqrt 2 * (9 * δ' / 2))
        (e_plane_inv '' T'_union)) :
    (Metric.externalCoveringNumber δ'.toNNReal T'_union : ENNReal) ≥
      (Metric.externalCoveringNumber δ'.toNNReal param_union : ENNReal) /
      ENNReal.ofReal (1000 : ℝ) := by
  let T_eucl := e_plane_inv '' T'_union
  let r : ℝ := Real.sqrt 2 * (9 * δ' / 2)
  let sqrt2_nn : NNReal := ⟨Real.sqrt 2, by positivity⟩
  -- Step 1: e_plane_inv is sqrt(2)-Lipschitz
  have h_einv_lip : LipschitzWith sqrt2_nn e_plane_inv :=
    e_plane_inv_sqrt2_lipschitz
  -- Step 2: covering(sqrt(2)*δ', T_eucl) ≤ covering(δ', T'_union)
  have h2 : Metric.externalCoveringNumber (sqrt2_nn * δ'.toNNReal) T_eucl ≤
      Metric.externalCoveringNumber δ'.toNNReal T'_union :=
    DiscretisedFurstenbergEstimate.CoveringUtils.externalCoveringNumber_image_lipschitz
      (hf := h_einv_lip)
  have h_scale1 : (sqrt2_nn * δ'.toNNReal : NNReal) = (Real.sqrt 2 * δ').toNNReal := by
    apply NNReal.coe_injective
    have hδ'_nonneg : 0 ≤ δ' := by linarith
    have h1 : (↑(sqrt2_nn * δ'.toNNReal) : ℝ) = (↑sqrt2_nn : ℝ) * (↑δ'.toNNReal : ℝ) := by
      simp [NNReal.coe_mul]
    have h2 : (↑δ'.toNNReal : ℝ) = δ' := by
      rw [Real.coe_toNNReal']
      have h : max δ' 0 = δ' := by rw [max_eq_left] <;> linarith
      exact h
    have h3 : (↑sqrt2_nn : ℝ) = Real.sqrt 2 := by
      dsimp only [sqrt2_nn]
      <;> rfl
    have h4 : (↑((Real.sqrt 2 * δ').toNNReal) : ℝ) = Real.sqrt 2 * δ' := by
      rw [Real.coe_toNNReal']
      have h : max (Real.sqrt 2 * δ') 0 = Real.sqrt 2 * δ' := by
        rw [max_eq_left] <;> positivity
      exact h
    calc (↑(sqrt2_nn * δ'.toNNReal) : ℝ)
        = (↑sqrt2_nn : ℝ) * (↑δ'.toNNReal : ℝ) := h1
      _ = Real.sqrt 2 * δ' := by rw [h3, h2] <;> ring
      _ = (↑((Real.sqrt 2 * δ').toNNReal) : ℝ) := h4.symm
  rw [h_scale1] at h2
  -- Step 3: Thickening with slack δ'
  let r' : ℝ := r + δ'
  let R : ℝ := r' + Real.sqrt 2 * δ'
  have h3 : Metric.externalCoveringNumber R.toNNReal param_union ≤
      Metric.externalCoveringNumber (Real.sqrt 2 * δ').toNNReal T_eucl := by
    have h_main : ∀ (C : Set (EuclideanSpace ℝ (Fin 2))),
        Metric.IsCover (Real.sqrt 2 * δ').toNNReal T_eucl C →
        Metric.externalCoveringNumber R.toNNReal param_union ≤ C.encard := by
      intro C hC
      have hC_sub : T_eucl ⊆ ⋃ c ∈ C, Metric.closedEBall c (Real.sqrt 2 * δ').toNNReal :=
        Metric.isCover_iff_subset_iUnion_closedEBall.mp hC
      have h_cover_sub : param_union ⊆ ⋃ c ∈ C, Metric.closedEBall c R.toNNReal := by
        intro x hx
        have h4 : x ∈ Metric.cthickening r T_eucl := h_thicken hx
        have h4' : Metric.infEDist x T_eucl ≤ ENNReal.ofReal r := by
          simpa using h4
        have h_strict : Metric.infEDist x T_eucl < ENNReal.ofReal r' := by
          have hr'_pos : 0 < r' := by positivity
          have h5 : ENNReal.ofReal r < ENNReal.ofReal r' := by
            rw [ENNReal.ofReal_lt_ofReal_iff hr'_pos] <;> linarith
          exact lt_of_le_of_lt h4' h5
        have h5 : ∃ y, y ∈ T_eucl ∧ edist x y < ENNReal.ofReal r' :=
          Metric.infEDist_lt_iff.mp h_strict
        rcases h5 with ⟨y, hy, hxy_edist⟩
        have hxy : dist x y < r' :=
          edist_lt_ofReal.mp hxy_edist
        have hxy_le : dist x y ≤ r' := by linarith
        have h61 : y ∈ ⋃ c ∈ C, Metric.closedEBall c (Real.sqrt 2 * δ').toNNReal := hC_sub hy
        rcases Set.mem_iUnion₂.mp h61 with ⟨c, hc, hyc⟩
        have h7 : dist y c ≤ Real.sqrt 2 * δ' := by
          have h : dist y c ≤ Real.sqrt 2 * δ' ∨ y = c := by
            simpa [Metric.mem_closedEBall] using hyc
          rcases h with (h | rfl)
          · exact h
          · have h_pos : 0 ≤ Real.sqrt 2 * δ' := by positivity
            simpa [dist_self] using h_pos
        have h6 : dist x c ≤ R := by
          calc dist x c ≤ dist x y + dist y c := dist_triangle x y c
               _ ≤ r' + Real.sqrt 2 * δ' := by linarith
        have hR_nonneg : 0 ≤ R := by positivity
        have h6_edist : edist x c ≤ ↑R.toNNReal := by
          have h_eq : (R.toNNReal : ℝ) = R := by
            simp [hR_nonneg] <;> linarith
          have h6' : dist x c ≤ (R.toNNReal : ℝ) := by
            rw [h_eq] <;> exact h6
          rw [edist_le_coe, ←dist_le_coe]
          exact h6'
        exact Set.mem_iUnion₂.mpr ⟨c, hc, h6_edist⟩
      have h_cover : Metric.IsCover R.toNNReal param_union C :=
        Metric.isCover_iff_subset_iUnion_closedEBall.mpr h_cover_sub
      exact Metric.IsCover.externalCoveringNumber_le_encard h_cover
    simpa [Metric.externalCoveringNumber] using le_iInf₂ h_main
  -- Step 4: Doubling in Euclidean 2D
  let K_dbl : ℝ := R / δ'
  have hK_dbl_pos : 0 < K_dbl := by positivity
  have hK_dbl_eq : K_dbl = Real.sqrt 2 * 11 / 2 + 1 := by
    dsimp only [K_dbl, R, r', r]
    field_simp [hδ'.ne'] <;> ring
  have h4 : K_dbl * δ' ≤ 12 * δ' := by
    rw [hK_dbl_eq]
    have h5 : Real.sqrt 2 * 11 / 2 + 1 ≤ 12 := by
      have h6 : Real.sqrt 2 ≤ 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith
    gcongr
  have h_R_eq : R = K_dbl * δ' := by
    dsimp only [K_dbl, R]
    field_simp [hδ'.ne'] <;> ring
  have h_doubling : Metric.externalCoveringNumber δ'.toNNReal param_union ≤
      ((Nat.ceil (2 * Real.sqrt 2 * K_dbl) + 1)^2 : ENNReal) *
      Metric.externalCoveringNumber R.toNNReal param_union := by
    rw [h_R_eq]
    exact externalCoveringNumber_doubling_euclidean2d (hK_pos := hK_dbl_pos) (hε_pos := hδ') h4
  -- Bound constant: 2*sqrt(2)*K_dbl = 22 + 2*sqrt(2) < 25, ceil+1 ≤ 26, square ≤ 676
  have h_const_le : (Nat.ceil (2 * Real.sqrt 2 * K_dbl) + 1)^2 ≤ 676 := by
    have h6 : 2 * Real.sqrt 2 * K_dbl ≤ 25 := by
      rw [hK_dbl_eq]
      have h7 : 2 * Real.sqrt 2 * (Real.sqrt 2 * 11 / 2 + 1) = 22 + 2 * Real.sqrt 2 := by
        calc
          2 * Real.sqrt 2 * (Real.sqrt 2 * 11 / 2 + 1)
            = 2 * (Real.sqrt 2)^2 * 11 / 2 + 2 * Real.sqrt 2 := by ring
          _ = 2 * 2 * 11 / 2 + 2 * Real.sqrt 2 := by rw [Real.sq_sqrt (by norm_num)]
          _ = 22 + 2 * Real.sqrt 2 := by norm_num
      rw [h7]
      have h8 : Real.sqrt 2 ≤ 3 / 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith
    have h8 : Nat.ceil (2 * Real.sqrt 2 * K_dbl) ≤ 25 := Nat.ceil_le.mpr h6
    have h9 : Nat.ceil (2 * Real.sqrt 2 * K_dbl) + 1 ≤ 26 := by linarith
    have h10 : (Nat.ceil (2 * Real.sqrt 2 * K_dbl) + 1)^2 ≤ 26^2 := by gcongr
    norm_num at h10 ⊢ <;> exact h10
  have h_doubling676 : Metric.externalCoveringNumber δ'.toNNReal param_union ≤
      (676 : ENNReal) * Metric.externalCoveringNumber R.toNNReal param_union := by
    calc
      Metric.externalCoveringNumber δ'.toNNReal param_union
        ≤ ((Nat.ceil (2 * Real.sqrt 2 * K_dbl) + 1)^2 : ENNReal) *
            Metric.externalCoveringNumber R.toNNReal param_union := h_doubling
      _ ≤ (676 : ENNReal) * Metric.externalCoveringNumber R.toNNReal param_union := by
          gcongr <;> exact_mod_cast h_const_le
  -- Combine
  let x := Metric.externalCoveringNumber δ'.toNNReal param_union
  let y := Metric.externalCoveringNumber δ'.toNNReal T'_union
  have h_final : x ≤ (676 : ENNReal) * y := by
    calc x ≤ (676 : ENNReal) * Metric.externalCoveringNumber R.toNNReal param_union := h_doubling676
         _ ≤ (676 : ENNReal) * Metric.externalCoveringNumber (Real.sqrt 2 * δ').toNNReal T_eucl := by
             gcongr <;> exact h3
         _ ≤ (676 : ENNReal) * y := by gcongr <;> exact h2
  have h676_le : (676 : ENNReal) ≤ ENNReal.ofReal (1000 : ℝ) := by
    norm_cast <;> norm_num
  have h_final1000 : x ≤ y * ENNReal.ofReal (1000 : ℝ) := by
    have h : x ≤ (676 : ENNReal) * y := h_final
    have h' : (676 : ENNReal) * y ≤ y * ENNReal.ofReal (1000 : ℝ) := by
      rw [mul_comm (676 : ENNReal) y]
      gcongr <;> exact h676_le
    exact le_trans h h'
  have h_goal : x / ENNReal.ofReal (1000 : ℝ) ≤ y := by
    rw [ENNReal.div_le_iff (by norm_num) (by simp)]
    exact h_final1000
  exact h_goal

end

end DirecretisedFurstenbergEstimate
