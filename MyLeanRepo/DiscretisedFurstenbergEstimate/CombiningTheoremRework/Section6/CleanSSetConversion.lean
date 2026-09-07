module

/-
  Clean S-set Conversion Lemmas

  Extracts grid packing, metric comparability, and point-set-to-finset
  S-set conversion lemmas from contaminated Prop73/ and FineNormalizedRatio.lean
  files, without any Prop73 dependencies.

  Contains (geometric constructors ep, squareCenter, dSquareCorner,
  dyadicSquare_covered_by_center are imported from CleanSquareLemmas):
  - dsquare_ball_at_most_9, grid_packing_helper, grid_packing_dsquare
  - dsquare_plane_metric_comparability, plane_grid_ball_at_most_9, corner_packing_bound
  - point_in_square_dist_to_corner
  - weaken_sset_exponent
  - fine_local_squares_bound
  - fine_pointset_sset_to_finset_sset

  Dependencies: Base, DyadicTubes, DyadicConversion, CleanSquareLemmas, Mathlib

  Whiteprint node: section6 / clean_sset_conversion
  Status: CLEAN EXTRACT
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CleanSquareLemmas
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.DyadicConversion

attribute [local instance] Classical.propDecidable

/-- At most 9 DSquares in a δ-ball (sup norm on grid corners). -/
lemma dsquare_ball_at_most_9 {m : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta m) (c : DSquare m) (S : Finset (DSquare m)) :
    (S.filter (fun q => dist q c ≤ δ)).card ≤ 9 := by
  let i0 := c.i
  let j0 := c.j
  let grid : Finset (DSquare m) :=
    (Finset.Icc (i0 - 1) (i0 + 1)).biUnion fun i =>
      (Finset.Icc (j0 - 1) (j0 + 1)).image (fun j => (⟨i, j⟩ : DSquare m))
  have h1 : S.filter (fun q => dist q c ≤ δ) ⊆ grid := by
    intro q hq
    have h2 : dist q c ≤ δ := (Finset.mem_filter.mp hq).2
    have h_def : dist q c = dist q.toPoint c.toPoint := by rfl
    have h_max : dist q.toPoint c.toPoint = max (dist q.toPoint.1 c.toPoint.1) (dist q.toPoint.2 c.toPoint.2) := by exact Prod.dist_eq
    have hδ_def : DiscretisedFurstenbergEstimate.δ m = dyadicDelta m := by
      simp [DiscretisedFurstenbergEstimate.δ, dyadicDelta, Real.rpow_neg] <;> field_simp <;> norm_cast
    have h21 : dist q.toPoint.1 c.toPoint.1 = |(q.i : ℝ) - (c.i : ℝ)| * δ := by
      have h : dist q.toPoint.1 c.toPoint.1 = |(q.i : ℝ) * dyadicDelta m - (c.i : ℝ) * dyadicDelta m| := by
        rw [Real.dist_eq]
        have h' : q.toPoint.1 = (q.i : ℝ) * DiscretisedFurstenbergEstimate.δ m := by
          simp [DSquare.toPoint] <;> rfl
        have h'' : c.toPoint.1 = (c.i : ℝ) * DiscretisedFurstenbergEstimate.δ m := by
          simp [DSquare.toPoint] <;> rfl
        rw [h', h'', hδ_def]
      rw [h]
      have h2 : (q.i : ℝ) * dyadicDelta m - (c.i : ℝ) * dyadicDelta m = ((q.i : ℝ) - (c.i : ℝ)) * δ := by
        rw [←hδ_eq] <;> ring
      rw [h2, abs_mul]
      have h3 : |((q.i : ℝ) - (c.i : ℝ))| * |δ| = |(q.i : ℝ) - (c.i : ℝ)| * δ := by
        rw [abs_of_pos hδ_pos] <;> ring
      exact h3
    have h22 : dist q.toPoint.2 c.toPoint.2 = |(q.j : ℝ) - (c.j : ℝ)| * δ := by
      have h : dist q.toPoint.2 c.toPoint.2 = |(q.j : ℝ) * dyadicDelta m - (c.j : ℝ) * dyadicDelta m| := by
        rw [Real.dist_eq]
        have h' : q.toPoint.2 = (q.j : ℝ) * DiscretisedFurstenbergEstimate.δ m := by
          simp [DSquare.toPoint] <;> rfl
        have h'' : c.toPoint.2 = (c.j : ℝ) * DiscretisedFurstenbergEstimate.δ m := by
          simp [DSquare.toPoint] <;> rfl
        rw [h', h'', hδ_def]
      rw [h]
      have h2 : (q.j : ℝ) * dyadicDelta m - (c.j : ℝ) * dyadicDelta m = ((q.j : ℝ) - (c.j : ℝ)) * δ := by
        rw [←hδ_eq] <;> ring
      rw [h2, abs_mul]
      have h3 : |((q.j : ℝ) - (c.j : ℝ))| * |δ| = |(q.j : ℝ) - (c.j : ℝ)| * δ := by
        rw [abs_of_pos hδ_pos] <;> ring
      exact h3
    have h_dist_eq : dist q c = max (|(q.i : ℝ) - (c.i : ℝ)| * δ) (|(q.j : ℝ) - (c.j : ℝ)| * δ) := by
      rw [h_def, h_max, h21, h22]
    rw [h_dist_eq] at h2
    have h7 : |(q.i : ℝ) - (c.i : ℝ)| ≤ 1 := by
      have h8 : |(q.i : ℝ) - (c.i : ℝ)| * δ ≤ max (|(q.i : ℝ) - (c.i : ℝ)| * δ) (|(q.j : ℝ) - (c.j : ℝ)| * δ) := le_max_left _ _
      have h9 : |(q.i : ℝ) - (c.i : ℝ)| * δ ≤ δ := by linarith
      nlinarith [abs_nonneg ((q.i : ℝ) - (c.i : ℝ))]
    have h9 : |(q.j : ℝ) - (c.j : ℝ)| ≤ 1 := by
      have h10 : |(q.j : ℝ) - (c.j : ℝ)| * δ ≤ max (|(q.i : ℝ) - (c.i : ℝ)| * δ) (|(q.j : ℝ) - (c.j : ℝ)| * δ) := le_max_right _ _
      have h11 : |(q.j : ℝ) - (c.j : ℝ)| * δ ≤ δ := by linarith
      nlinarith [abs_nonneg ((q.j : ℝ) - (c.j : ℝ))]
    have h14 : c.i - 1 ≤ q.i := by
      have h : (c.i : ℝ) - 1 ≤ (q.i : ℝ) := by linarith [abs_le.mp h7]
      exact_mod_cast h
    have h15 : q.i ≤ c.i + 1 := by
      have h : (q.i : ℝ) ≤ (c.i : ℝ) + 1 := by linarith [abs_le.mp h7]
      exact_mod_cast h
    have h16 : c.j - 1 ≤ q.j := by
      have h : (c.j : ℝ) - 1 ≤ (q.j : ℝ) := by linarith [abs_le.mp h9]
      exact_mod_cast h
    have h17 : q.j ≤ c.j + 1 := by
      have h : (q.j : ℝ) ≤ (c.j : ℝ) + 1 := by linarith [abs_le.mp h9]
      exact_mod_cast h
    have h18 : q.i ∈ Finset.Icc (i0 - 1) (i0 + 1) := by
      simp only [Finset.mem_Icc]; exact ⟨h14, h15⟩
    have h19 : q.j ∈ Finset.Icc (j0 - 1) (j0 + 1) := by
      simp only [Finset.mem_Icc]; exact ⟨h16, h17⟩
    exact Finset.mem_biUnion.mpr ⟨q.i, h18, Finset.mem_image.mpr ⟨q.j, h19, by cases q <;> simp <;> rfl⟩⟩
  have h_grid_card : grid.card ≤ 9 := by
    have h13 : grid.card ≤ ∑ i ∈ Finset.Icc (i0 - 1) (i0 + 1),
        ((Finset.Icc (j0 - 1) (j0 + 1)).image (fun j : ℤ => (⟨i, j⟩ : DSquare m))).card :=
      Finset.card_biUnion_le
    have h14 : ∀ i, ((Finset.Icc (j0 - 1) (j0 + 1)).image (fun j : ℤ => (⟨i, j⟩ : DSquare m))).card = 3 := by
      intro i
      have h_inj : Function.Injective (fun j : ℤ => (⟨i, j⟩ : DSquare m)) := by
        intro j1 j2 h
        simpa [DSquare.mk] using h
      rw [Finset.card_image_of_injective _ h_inj]
      simp [Finset.Icc_self]
      <;> omega
    have h15 : (Finset.Icc (i0 - 1) (i0 + 1)).card = 3 := by simp <;> omega
    calc grid.card
      ≤ ∑ i ∈ Finset.Icc (i0 - 1) (i0 + 1), _ := h13
    _ = ∑ i ∈ Finset.Icc (i0 - 1) (i0 + 1), 3 := by
        apply Finset.sum_congr rfl; intro i _; exact h14 i
    _ = 3 * 3 := by rw [Finset.sum_const, h15] <;> ring
    _ = 9 := by norm_num
  exact le_trans (Finset.card_le_card h1) h_grid_card

/-- Helper: for any finite cover C, |S| ≤ 9 * |C|. -/
lemma grid_packing_helper {m : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta m) (S : Finset (DSquare m))
    (C : Finset (DSquare m))
    (hcover : (S : Set (DSquare m)) ⊆ ⋃ c ∈ C, Metric.closedBall c δ.toNNReal) :
    S.card ≤ 9 * C.card := by
  let S_c (c : DSquare m) : Finset (DSquare m) := S.filter (fun q => dist q c ≤ δ)
  have h3 : ∀ c ∈ C, (S_c c).card ≤ 9 := by
    intro c _
    exact dsquare_ball_at_most_9 hδ_pos hδ_eq c S
  have h4 : S ⊆ C.biUnion S_c := by
    intro q hq
    have h5 : q ∈ (S : Set (DSquare m)) := hq
    have h6 : q ∈ ⋃ c ∈ C, Metric.closedBall c δ.toNNReal := hcover h5
    rcases Set.mem_iUnion₂.mp h6 with ⟨c, hc, hball⟩
    have h7 : dist q c ≤ δ := by
      have hε : (δ.toNNReal : ℝ) = δ := by
        simp [NNReal.coe_mk, hδ_pos.le] <;> linarith
      have hdist : dist q c ≤ (δ.toNNReal : ℝ) := by exact dist_le_coe.mpr hball
      rw [hε] at hdist
      exact hdist
    have h8 : q ∈ S_c c := Finset.mem_filter.mpr ⟨hq, h7⟩
    exact Finset.mem_biUnion.mpr ⟨c, hc, h8⟩
  have h5 : S.card ≤ (C.biUnion S_c).card := Finset.card_le_card h4
  have h6 : (C.biUnion S_c).card ≤ ∑ c ∈ C, (S_c c).card := Finset.card_biUnion_le
  have h7 : ∑ c ∈ C, (S_c c).card ≤ ∑ c ∈ C, 9 := by
    apply Finset.sum_le_sum; intro c hc; exact h3 c hc
  have h8 : ∑ c ∈ C, (9 : ℕ) = 9 * C.card := by
    simp [Finset.sum_const] <;> ring
  rw [h8] at h7
  exact le_trans (le_trans h5 h6) h7

/-- Grid packing: |S| ≤ 9 * Ncover(δ, S) for any finset of DSquares. -/
lemma grid_packing_dsquare {m : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta m) (S : Finset (DSquare m)) :
    (S.card : ENNReal) ≤ (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal (S : Set (DSquare m)) := by
  let ε : NNReal := δ.toNNReal
  have h_main : ∀ (C : Set (DSquare m)), Metric.IsCover ε (S : Set (DSquare m)) C →
      (S.card : ENNReal) / 9 ≤ (C.encard : ENNReal) := by
    intro C hC
    by_cases hCfin : Set.Finite C
    · let Cfin := hCfin.toFinset
      have h2 : (Cfin : Set (DSquare m)) = C := Set.Finite.coe_toFinset _
      have h3 : (S : Set (DSquare m)) ⊆ ⋃ c ∈ Cfin, Metric.closedBall c ε := by
        have h4 := hC.subset_iUnion_closedBall
        rw [←h2] at h4
        exact h4
      have h4 : S.card ≤ 9 * Cfin.card := grid_packing_helper hδ_pos hδ_eq S Cfin h3
      have h5 : (S.card : ENNReal) ≤ (9 : ENNReal) * (Cfin.card : ENNReal) := by exact_mod_cast h4
      have h6 : (C.encard : ENNReal) = (Cfin.card : ENNReal) := by
        have h7 : C.encard = (Cfin.card : ENat) := by rw [←h2]; simp
        rw [h7] <;> norm_cast
      rw [h6]
      calc (S.card : ENNReal) / 9
        ≤ ((9 : ENNReal) * (Cfin.card : ENNReal)) / 9 := by gcongr
      _ = (Cfin.card : ENNReal) := by
        have h_comm : (9 : ENNReal) * (Cfin.card : ENNReal) = (Cfin.card : ENNReal) * (9 : ENNReal) := by ring
        rw [h_comm]
        exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
    · have h6 : C.encard = ⊤ := by rw [Set.encard_eq_top_iff]; exact hCfin
      rw [h6] <;> simp
  have h4 : (S.card : ENNReal) / 9 ≤ (Metric.externalCoveringNumber ε (S : Set (DSquare m)) : ENNReal) := by
    simpa [Metric.externalCoveringNumber] using le_iInf₂ h_main
  have h5 : ((S.card : ENNReal) / 9) * 9 ≤ (Metric.externalCoveringNumber ε (S : Set (DSquare m)) : ENNReal) * 9 := by
    gcongr
  have h6 : ((S.card : ENNReal) / 9) * 9 = (S.card : ENNReal) := by
    exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
  have h7 : (S.card : ENNReal) ≤ (9 : ENNReal) * (Metric.externalCoveringNumber ε (S : Set (DSquare m)) : ENNReal) := by
    have h8 : (Metric.externalCoveringNumber ε (S : Set (DSquare m)) : ENNReal) * 9 = (9 : ENNReal) * (Metric.externalCoveringNumber ε (S : Set (DSquare m)) : ENNReal) := by ring
    rw [h8] at h5
    rw [h6] at h5
    exact h5
  exact h7

/-- Metric comparability: DSquare dist ≤ Plane corner dist ≤ √2 · DSquare dist. -/
lemma dsquare_plane_metric_comparability {m : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta m)
    (q p : DSquare m) :
    dist q p ≤ dist (dSquareCorner δ q) (dSquareCorner δ p) ∧
    dist (dSquareCorner δ q) (dSquareCorner δ p) ≤ Real.sqrt 2 * dist q p := by
  let a : ℝ := |(q.i : ℝ) - (p.i : ℝ)| * δ
  let b : ℝ := |(q.j : ℝ) - (p.j : ℝ)| * δ
  have ha_nonneg : 0 ≤ a := by positivity
  have hb_nonneg : 0 ≤ b := by positivity
  have h1 : dist q p = max a b := by
    have h_dist_def : dist q p = dist q.toPoint p.toPoint := by rfl
    rw [h_dist_def]
    have h : dist q.toPoint p.toPoint = max (dist q.toPoint.1 p.toPoint.1) (dist q.toPoint.2 p.toPoint.2) := by exact Prod.dist_eq
    rw [h]
    have h21 : dist q.toPoint.1 p.toPoint.1 = a := by
      simp [DSquare.toPoint, a, Real.dist_eq]
      have h : |(q.i : ℝ) * δ - (p.i : ℝ) * δ| = |(q.i : ℝ) - (p.i : ℝ)| * δ := by
        have h' : (q.i : ℝ) * δ - (p.i : ℝ) * δ = ((q.i : ℝ) - (p.i : ℝ)) * δ := by ring
        rw [h']
        rw [abs_mul, abs_of_pos hδ_pos] <;> ring
      have hδm : DiscretisedFurstenbergEstimate.δ m = δ := by
        have h : DiscretisedFurstenbergEstimate.δ m = dyadicDelta m := by
          simp [DiscretisedFurstenbergEstimate.δ, dyadicDelta, Real.rpow_neg] <;> field_simp <;> norm_cast
        rw [h, hδ_eq]
      rw [hδm]
      exact h
    have h22 : dist q.toPoint.2 p.toPoint.2 = b := by
      simp [DSquare.toPoint, b, Real.dist_eq]
      have h : |(q.j : ℝ) * δ - (p.j : ℝ) * δ| = |(q.j : ℝ) - (p.j : ℝ)| * δ := by
        have h' : (q.j : ℝ) * δ - (p.j : ℝ) * δ = ((q.j : ℝ) - (p.j : ℝ)) * δ := by ring
        rw [h']
        rw [abs_mul, abs_of_pos hδ_pos] <;> ring
      have hδm : DiscretisedFurstenbergEstimate.δ m = δ := by
        have h : DiscretisedFurstenbergEstimate.δ m = dyadicDelta m := by
          simp [DiscretisedFurstenbergEstimate.δ, dyadicDelta, Real.rpow_neg] <;> field_simp <;> norm_cast
        rw [h, hδ_eq]
      rw [hδm]
      exact h
    rw [h21, h22]
  have h2 : dist (dSquareCorner δ q) (dSquareCorner δ p) = Real.sqrt (a ^ 2 + b ^ 2) := by
    have h_dist : dist (dSquareCorner δ q) (dSquareCorner δ p) =
        ‖dSquareCorner δ q - dSquareCorner δ p‖ := by rw [dist_eq_norm]
    rw [h_dist]
    have h3 : ‖dSquareCorner δ q - dSquareCorner δ p‖ =
        Real.sqrt (((dSquareCorner δ q) 0 - (dSquareCorner δ p) 0) ^ 2 +
          ((dSquareCorner δ q) 1 - (dSquareCorner δ p) 1) ^ 2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring_nf
    rw [h3]
    have h4 : (dSquareCorner δ q) 0 - (dSquareCorner δ p) 0 = (q.i : ℝ) * δ - (p.i : ℝ) * δ := by
      simp [dSquareCorner, ep] <;> ring
    have h5 : (dSquareCorner δ q) 1 - (dSquareCorner δ p) 1 = (q.j : ℝ) * δ - (p.j : ℝ) * δ := by
      simp [dSquareCorner, ep] <;> ring
    rw [h4, h5]
    have h6 : ((q.i : ℝ) * δ - (p.i : ℝ) * δ) ^ 2 = a ^ 2 := by
      have h1 : (q.i : ℝ) * δ - (p.i : ℝ) * δ = ((q.i : ℝ) - (p.i : ℝ)) * δ := by ring
      have h2 : a = |(q.i : ℝ) - (p.i : ℝ)| * δ := by rfl
      rw [h1, h2]
      have h3 : ((q.i : ℝ) - (p.i : ℝ)) ^ 2 = |(q.i : ℝ) - (p.i : ℝ)| ^ 2 := by rw [sq_abs]
      have h4 : (((q.i : ℝ) - (p.i : ℝ)) * δ) ^ 2 = ((q.i : ℝ) - (p.i : ℝ)) ^ 2 * δ ^ 2 := by ring
      have h5 : (|(q.i : ℝ) - (p.i : ℝ)| * δ) ^ 2 = |(q.i : ℝ) - (p.i : ℝ)| ^ 2 * δ ^ 2 := by ring
      rw [h4, h5, h3]
    have h7 : ((q.j : ℝ) * δ - (p.j : ℝ) * δ) ^ 2 = b ^ 2 := by
      have h1 : (q.j : ℝ) * δ - (p.j : ℝ) * δ = ((q.j : ℝ) - (p.j : ℝ)) * δ := by ring
      have h2 : b = |(q.j : ℝ) - (p.j : ℝ)| * δ := by rfl
      rw [h1, h2]
      have h3 : ((q.j : ℝ) - (p.j : ℝ)) ^ 2 = |(q.j : ℝ) - (p.j : ℝ)| ^ 2 := by rw [sq_abs]
      have h4 : (((q.j : ℝ) - (p.j : ℝ)) * δ) ^ 2 = ((q.j : ℝ) - (p.j : ℝ)) ^ 2 * δ ^ 2 := by ring
      have h5 : (|(q.j : ℝ) - (p.j : ℝ)| * δ) ^ 2 = |(q.j : ℝ) - (p.j : ℝ)| ^ 2 * δ ^ 2 := by ring
      rw [h4, h5, h3]
    rw [h6, h7] <;> ring
  rw [h1, h2]
  have h_ia : a ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
    have h_pos : 0 ≤ b ^ 2 := by positivity
    have h : a ^ 2 ≤ a ^ 2 + b ^ 2 := by linarith
    have h' : 0 ≤ a := ha_nonneg
    have h4 : Real.sqrt (a ^ 2) ≤ Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_le_sqrt h
    have h5 : Real.sqrt (a ^ 2) = a := Real.sqrt_sq h'
    rw [h5] at h4
    exact h4
  have h_ib : b ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
    have h_pos : 0 ≤ a ^ 2 := by positivity
    have h : b ^ 2 ≤ a ^ 2 + b ^ 2 := by linarith
    have h' : 0 ≤ b := hb_nonneg
    have h4 : Real.sqrt (b ^ 2) ≤ Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_le_sqrt h
    have h5 : Real.sqrt (b ^ 2) = b := Real.sqrt_sq h'
    rw [h5] at h4
    exact h4
  have h_first : max a b ≤ Real.sqrt (a ^ 2 + b ^ 2) := max_le h_ia h_ib
  have h_sum : a ^ 2 + b ^ 2 ≤ 2 * (max a b) ^ 2 := by
    have h1 : a ≤ max a b := le_max_left _ _
    have h2 : b ≤ max a b := le_max_right _ _
    have h3 : a ^ 2 ≤ (max a b) ^ 2 := by gcongr
    have h4 : b ^ 2 ≤ (max a b) ^ 2 := by gcongr
    linarith
  have h_second : Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt 2 * (max a b) := by
    have h9 : Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt (2 * (max a b) ^ 2) := Real.sqrt_le_sqrt h_sum
    have h10 : 0 ≤ max a b := by positivity
    have h11 : Real.sqrt (2 * (max a b) ^ 2) = Real.sqrt 2 * (max a b) := by
      calc Real.sqrt (2 * (max a b) ^ 2)
        = Real.sqrt 2 * Real.sqrt ((max a b) ^ 2) := by rw [Real.sqrt_mul] <;> norm_num
      _ = Real.sqrt 2 * (max a b) := by rw [Real.sqrt_sq h10]
    rw [h11] at h9
    exact h9
  exact ⟨h_first, h_second⟩

/-- At most 9 DSquare corners in a Plane δ-ball. -/
lemma plane_grid_ball_at_most_9 {m : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta m) (c : EuclideanPlane) (S : Finset (DSquare m)) :
    (S.filter (fun q => dist (dSquareCorner δ q) c ≤ δ)).card ≤ 9 := by
  let i0 : ℤ := Int.floor (c 0 / δ)
  let j0 : ℤ := Int.floor (c 1 / δ)
  have h_i01 : (i0 : ℝ) ≤ c 0 / δ := Int.floor_le (c 0 / δ)
  have h_i02 : c 0 / δ < (i0 : ℝ) + 1 := Int.lt_floor_add_one (c 0 / δ)
  have h_j01 : (j0 : ℝ) ≤ c 1 / δ := Int.floor_le (c 1 / δ)
  have h_j02 : c 1 / δ < (j0 : ℝ) + 1 := Int.lt_floor_add_one (c 1 / δ)
  have h1 : ∀ q ∈ S.filter (fun q => dist (dSquareCorner δ q) c ≤ δ),
      q.i ∈ Finset.Icc (i0 - 1) (i0 + 1) ∧ q.j ∈ Finset.Icc (j0 - 1) (j0 + 1) := by
    intro q hq
    have h2 : dist (dSquareCorner δ q) c ≤ δ := (Finset.mem_filter.mp hq).2
    have h_coord0 : |(dSquareCorner δ q) 0 - c 0| ≤ dist (dSquareCorner δ q) c := by
      have h : dist (dSquareCorner δ q) c = ‖(dSquareCorner δ q) - c‖ := by rw [dist_eq_norm]
      rw [h]
      have h2 : |((dSquareCorner δ q) - c) 0| ≤ ‖(dSquareCorner δ q) - c‖ := by
        let v := (dSquareCorner δ q) - c
        have h3 : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
          have h4 : ‖v‖ ^ 2 = ∑ i : Fin 2, (v i) ^ 2 := by
            exact EuclideanSpace.real_norm_sq_eq v
          rw [h4]
          simp [Fin.sum_univ_two] <;> ring
        have h5 : |v 0| ^ 2 ≤ ‖v‖ ^ 2 := by
          rw [h3]
          have h6 : 0 ≤ (v 1) ^ 2 := by positivity
          have h7 : (v 0) ^ 2 = |v 0| ^ 2 := by rw [sq_abs]
          rw [h7]
          linarith
        have h8 : 0 ≤ |v 0| := by positivity
        have h9 : 0 ≤ ‖v‖ := by positivity
        nlinarith
      simpa using h2
    have h3 : |(q.i : ℝ) * δ - c 0| ≤ δ := by
      simpa [dSquareCorner, ep] using h_coord0.trans h2
    have h_coord1 : |(dSquareCorner δ q) 1 - c 1| ≤ dist (dSquareCorner δ q) c := by
      have h : dist (dSquareCorner δ q) c = ‖(dSquareCorner δ q) - c‖ := by rw [dist_eq_norm]
      rw [h]
      have h2 : |((dSquareCorner δ q) - c) 1| ≤ ‖(dSquareCorner δ q) - c‖ := by
        let v := (dSquareCorner δ q) - c
        have h3 : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
          have h4 : ‖v‖ ^ 2 = ∑ i : Fin 2, (v i) ^ 2 := by exact EuclideanSpace.real_norm_sq_eq v
          rw [h4]
          simp [Fin.sum_univ_two] <;> ring
        have h5 : |v 1| ^ 2 ≤ ‖v‖ ^ 2 := by
          rw [h3]
          have h6 : 0 ≤ (v 0) ^ 2 := by positivity
          have h7 : (v 1) ^ 2 = |v 1| ^ 2 := by rw [sq_abs]
          rw [h7]
          linarith
        have h8 : 0 ≤ |v 1| := by positivity
        have h9 : 0 ≤ ‖v‖ := by positivity
        nlinarith
      simpa using h2
    have h4 : |(q.j : ℝ) * δ - c 1| ≤ δ := by
      simpa [dSquareCorner, ep] using h_coord1.trans h2
    have h_eq1 : (q.i : ℝ) * δ - c 0 = ((q.i : ℝ) - c 0 / δ) * δ := by
      field_simp [hδ_pos.ne'] <;> ring
    have h_abs1 : |(q.i : ℝ) - c 0 / δ| ≤ 1 := by
      have h5 : |(q.i : ℝ) * δ - c 0| = |(q.i : ℝ) - c 0 / δ| * δ := by
        rw [h_eq1, abs_mul, abs_of_pos hδ_pos]
      have h6 : |(q.i : ℝ) - c 0 / δ| * δ ≤ δ := by
        rw [←h5]
        exact h3
      have h7 : |(q.i : ℝ) - c 0 / δ| ≤ 1 := by
        calc |(q.i : ℝ) - c 0 / δ|
          = (|(q.i : ℝ) - c 0 / δ| * δ) / δ := by field_simp [hδ_pos.ne'] <;> ring
        _ ≤ δ / δ := by gcongr
        _ = 1 := by field_simp [hδ_pos.ne']
      exact h7
    have h_eq2 : (q.j : ℝ) * δ - c 1 = ((q.j : ℝ) - c 1 / δ) * δ := by
      field_simp [hδ_pos.ne'] <;> ring
    have h_abs2 : |(q.j : ℝ) - c 1 / δ| ≤ 1 := by
      have h5 : |(q.j : ℝ) * δ - c 1| = |(q.j : ℝ) - c 1 / δ| * δ := by
        rw [h_eq2, abs_mul, abs_of_pos hδ_pos]
      have h6 : |(q.j : ℝ) - c 1 / δ| * δ ≤ δ := by
        rw [←h5]
        exact h4
      have h7 : |(q.j : ℝ) - c 1 / δ| ≤ 1 := by
        calc |(q.j : ℝ) - c 1 / δ|
          = (|(q.j : ℝ) - c 1 / δ| * δ) / δ := by field_simp [hδ_pos.ne'] <;> ring
        _ ≤ δ / δ := by gcongr
        _ = 1 := by field_simp [hδ_pos.ne']
      exact h7
    have h_parts1 : -1 ≤ (q.i : ℝ) - c 0 / δ ∧ (q.i : ℝ) - c 0 / δ ≤ 1 := abs_le.mp h_abs1
    have h_low1 : c 0 / δ - 1 ≤ (q.i : ℝ) := by linarith [h_parts1.1]
    have h_high1 : (q.i : ℝ) ≤ c 0 / δ + 1 := by linarith [h_parts1.2]
    have h_i_low : i0 - 1 ≤ q.i := by
      have h : (i0 - 1 : ℝ) ≤ (q.i : ℝ) := by linarith
      exact_mod_cast h
    have h_i_high : q.i ≤ i0 + 1 := by
      have h : (q.i : ℝ) < (i0 : ℝ) + 2 := by linarith
      by_contra h'
      have : q.i ≥ i0 + 2 := by omega
      have : (q.i : ℝ) ≥ (i0 + 2 : ℝ) := by exact_mod_cast this
      linarith
    have h_parts2 : -1 ≤ (q.j : ℝ) - c 1 / δ ∧ (q.j : ℝ) - c 1 / δ ≤ 1 := abs_le.mp h_abs2
    have h_low2 : c 1 / δ - 1 ≤ (q.j : ℝ) := by linarith [h_parts2.1]
    have h_high2 : (q.j : ℝ) ≤ c 1 / δ + 1 := by linarith [h_parts2.2]
    have h_j_low : j0 - 1 ≤ q.j := by
      have h : (j0 - 1 : ℝ) ≤ (q.j : ℝ) := by linarith
      exact_mod_cast h
    have h_j_high : q.j ≤ j0 + 1 := by
      have h : (q.j : ℝ) < (j0 : ℝ) + 2 := by linarith
      by_contra h'
      have : q.j ≥ j0 + 2 := by omega
      have : (q.j : ℝ) ≥ (j0 + 2 : ℝ) := by exact_mod_cast this
      linarith
    exact ⟨by simp [Finset.mem_Icc] <;> omega, by simp [Finset.mem_Icc] <;> omega⟩
  let grid : Finset (DSquare m) :=
    (Finset.Icc (i0 - 1) (i0 + 1)).biUnion fun i =>
      (Finset.Icc (j0 - 1) (j0 + 1)).image (fun j => (⟨i, j⟩ : DSquare m))
  have h2 : S.filter (fun q => dist (dSquareCorner δ q) c ≤ δ) ⊆ grid := by
    intro q hq
    have h3 := h1 q hq
    have h4 : q.i ∈ Finset.Icc (i0 - 1) (i0 + 1) := h3.1
    have h5 : q.j ∈ Finset.Icc (j0 - 1) (j0 + 1) := h3.2
    exact Finset.mem_biUnion.mpr ⟨q.i, h4, Finset.mem_image.mpr ⟨q.j, h5, by cases q <;> simp <;> rfl⟩⟩
  have h3 : grid.card ≤ 9 := by
    have h13 : grid.card ≤ ∑ i ∈ Finset.Icc (i0 - 1) (i0 + 1),
        ((Finset.Icc (j0 - 1) (j0 + 1)).image (fun j : ℤ => (⟨i, j⟩ : DSquare m))).card :=
      Finset.card_biUnion_le
    have h14 : ∀ i, ((Finset.Icc (j0 - 1) (j0 + 1)).image (fun j : ℤ => (⟨i, j⟩ : DSquare m))).card = 3 := by
      intro i
      have h_inj : Function.Injective (fun j : ℤ => (⟨i, j⟩ : DSquare m)) := by
        intro j1 j2 h
        simpa [DSquare.mk] using h
      rw [Finset.card_image_of_injective _ h_inj]
      simp [Finset.Icc_self] <;> omega
    have h15 : (Finset.Icc (i0 - 1) (i0 + 1)).card = 3 := by simp <;> omega
    calc grid.card
      ≤ ∑ i ∈ Finset.Icc (i0 - 1) (i0 + 1), _ := h13
    _ = ∑ i ∈ Finset.Icc (i0 - 1) (i0 + 1), 3 := by
        apply Finset.sum_congr rfl; intro i _; exact h14 i
    _ = 3 * 3 := by rw [Finset.sum_const, h15] <;> ring
    _ = 9 := by norm_num
  exact le_trans (Finset.card_le_card h2) h3

/-- Packing bound: |S| ≤ 9 * Ncover_Plane(δ, corners(S)). -/
lemma corner_packing_bound {m : ℕ} {δ : ℝ} (hδ_pos : 0 < δ) (hδ_eq : δ = dyadicDelta m)
    (S : Finset (DSquare m)) :
    (S.card : ENNReal) ≤ 9 * Metric.externalCoveringNumber δ.toNNReal
      (S.image (dSquareCorner δ) : Set EuclideanPlane) := by
  let f : DSquare m → EuclideanPlane := dSquareCorner δ
  let A : Set EuclideanPlane := (S.image f : Set EuclideanPlane)
  have h_main : ∀ (C : Set EuclideanPlane), Metric.IsCover δ.toNNReal A C →
      (S.card : ENNReal) / 9 ≤ (C.encard : ENNReal) := by
    intro C hC
    by_cases hCfin : Set.Finite C
    · let Cfin := hCfin.toFinset
      have h2 : (Cfin : Set EuclideanPlane) = C := Set.Finite.coe_toFinset _
      have h3 : A ⊆ ⋃ c ∈ (Cfin : Set EuclideanPlane), Metric.closedBall c δ.toNNReal := by
        have h4 := hC.subset_iUnion_closedBall
        rw [←h2] at h4
        exact h4
      let Q_c : EuclideanPlane → Finset (DSquare m) := fun c =>
        S.filter (fun q => dist (f q) c ≤ δ)
      have hQ_sub : S ⊆ Cfin.biUnion Q_c := by
        intro q hq
        have hqA : f q ∈ A := Finset.mem_image.mpr ⟨q, hq, rfl⟩
        have h5 : f q ∈ ⋃ c ∈ (Cfin : Set EuclideanPlane), Metric.closedBall c δ.toNNReal := h3 hqA
        rcases Set.mem_iUnion₂.mp h5 with ⟨c, hc_in, hball⟩
        have h6 : c ∈ Cfin := by exact_mod_cast hc_in
        have h7 : dist (f q) c ≤ δ := by
          have h71 : (f q) ∈ Metric.closedBall c δ.toNNReal := hball
          have h72 : dist (f q) c ≤ (δ.toNNReal : ℝ) := h71
          have h73 : (δ.toNNReal : ℝ) = δ := by
            simp [NNReal.coe_mk, hδ_pos.le] <;> linarith
          rw [h73] at h72
          exact h72
        have h8 : q ∈ Q_c c := Finset.mem_filter.mpr ⟨hq, h7⟩
        exact Finset.mem_biUnion.mpr ⟨c, h6, h8⟩
      have h4 : ∀ c ∈ Cfin, (Q_c c).card ≤ 9 := by
        intro c _
        exact plane_grid_ball_at_most_9 hδ_pos hδ_eq c S
      have h5 : S.card ≤ (Cfin.biUnion Q_c).card := Finset.card_le_card hQ_sub
      have h6 : (Cfin.biUnion Q_c).card ≤ ∑ c ∈ Cfin, (Q_c c).card := Finset.card_biUnion_le
      have h7 : ∑ c ∈ Cfin, (Q_c c).card ≤ ∑ c ∈ Cfin, 9 := by
        apply Finset.sum_le_sum
        intro i _
        exact h4 i ‹_›
      have h8 : ∑ c ∈ Cfin, (9 : ℕ) = 9 * Cfin.card := by
        rw [Finset.sum_const] <;> ring
      have h9 : S.card ≤ 9 * Cfin.card := by linarith
      have h10 : (S.card : ENNReal) ≤ (9 : ENNReal) * (Cfin.card : ENNReal) := by
        exact_mod_cast h9
      have h11 : (C.encard : ENNReal) = (Cfin.card : ENNReal) := by
        have h12 : C.encard = (Cfin.card : ENat) := by rw [←h2]; simp
        rw [h12] <;> norm_cast
      rw [h11]
      calc (S.card : ENNReal) / 9
        ≤ ((9 : ENNReal) * (Cfin.card : ENNReal)) / 9 := by gcongr
      _ = (Cfin.card : ENNReal) := by
        have h_comm : (9 : ENNReal) * (Cfin.card : ENNReal) = (Cfin.card : ENNReal) * (9 : ENNReal) := by ring
        rw [h_comm]
        exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
    · have h6 : C.encard = ⊤ := by rw [Set.encard_eq_top_iff]; exact hCfin
      rw [h6] <;> simp
  have h4 : (S.card : ENNReal) / 9 ≤ Metric.externalCoveringNumber δ.toNNReal A := by
    simpa [Metric.externalCoveringNumber] using le_iInf₂ h_main
  have h7 : (S.card : ENNReal) ≤ 9 * Metric.externalCoveringNumber δ.toNNReal A := by
    have h9 : ((S.card : ENNReal) / 9) * 9 = (S.card : ENNReal) := by
      exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
    calc (S.card : ENNReal)
      = ((S.card : ENNReal) / 9) * 9 := h9.symm
    _ ≤ Metric.externalCoveringNumber δ.toNNReal A * 9 := by gcongr
    _ = 9 * Metric.externalCoveringNumber δ.toNNReal A := by ring
  exact h7

/-- Any point in a dyadic square is within √2·δ of its lower-left corner. -/
lemma point_in_square_dist_to_corner {k : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta k) (q : DSquare k) (z : EuclideanPlane)
    (hz : z ∈ (dSquareToDyadicSquare q).toSet) :
    dist z (dSquareCorner δ q) ≤ Real.sqrt 2 * δ := by
  have h12 : 0 ≤ z 0 - (q.i : ℝ) * δ := by
    have h13 : ((dSquareToDyadicSquare q).i : ℝ) * dyadicDelta k ≤ z 0 := hz.1
    have h14 : (dSquareToDyadicSquare q).i = q.i := by simp [dSquareToDyadicSquare]
    rw [h14] at h13
    rw [←hδ_eq] at h13
    linarith
  have h13 : z 0 - (q.i : ℝ) * δ < δ := by
    have h14 : z 0 < ((dSquareToDyadicSquare q).i + 1 : ℝ) * dyadicDelta k := hz.2.1
    have h15 : (dSquareToDyadicSquare q).i = q.i := by simp [dSquareToDyadicSquare]
    rw [h15] at h14
    rw [←hδ_eq] at h14
    linarith
  have h14 : 0 ≤ z 1 - (q.j : ℝ) * δ := by
    have h15 : ((dSquareToDyadicSquare q).j : ℝ) * dyadicDelta k ≤ z 1 := hz.2.2.1
    have h16 : (dSquareToDyadicSquare q).j = q.j := by simp [dSquareToDyadicSquare]
    rw [h16] at h15
    rw [←hδ_eq] at h15
    linarith
  have h15 : z 1 - (q.j : ℝ) * δ < δ := by
    have h16 : z 1 < ((dSquareToDyadicSquare q).j + 1 : ℝ) * dyadicDelta k := hz.2.2.2
    have h17 : (dSquareToDyadicSquare q).j = q.j := by simp [dSquareToDyadicSquare]
    rw [h17] at h16
    rw [←hδ_eq] at h16
    linarith
  have h16 : (z 0 - (q.i : ℝ) * δ) ^ 2 ≤ δ ^ 2 := by nlinarith
  have h17 : (z 1 - (q.j : ℝ) * δ) ^ 2 ≤ δ ^ 2 := by nlinarith
  have h18 : dist z (dSquareCorner δ q) ^ 2 =
      (z 0 - (q.i : ℝ) * δ) ^ 2 + (z 1 - (q.j : ℝ) * δ) ^ 2 := by
    have h19 := EuclideanSpace.dist_sq_eq z (dSquareCorner δ q)
    rw [h19]
    simp [Fin.sum_univ_two, Real.dist_eq, dSquareCorner, ep] <;> ring
  have h20 : dist z (dSquareCorner δ q) ^ 2 ≤ (Real.sqrt 2 * δ) ^ 2 := by
    rw [h18]
    have h21 : (Real.sqrt 2 * δ) ^ 2 = 2 * δ ^ 2 := by
      calc (Real.sqrt 2 * δ) ^ 2 = (Real.sqrt 2) ^ 2 * δ ^ 2 := by ring
        _ = 2 * δ ^ 2 := by rw [Real.sq_sqrt (by norm_num)] <;> ring
    rw [h21]
    linarith
  have h22 : 0 ≤ dist z (dSquareCorner δ q) := by positivity
  have h23 : 0 ≤ Real.sqrt 2 * δ := by positivity
  nlinarith

/-- Weaken an S-set from exponent t to exponent s (s ≤ t).
    Increases constant to max(C,1) to handle r ≥ 1. -/
lemma weaken_sset_exponent {X : Type*} [PseudoMetricSpace X]
    {δ s t C : ℝ} {P : Set X}
    (h : IsDeltaSSet δ t C P) (hs : 0 ≤ s) (hst : s ≤ t) :
    IsDeltaSSet δ s (max C 1) P := by
  let C' := max C 1
  have hC'_pos : 0 < C' := by positivity
  have hC'_ge1 : 1 ≤ C' := le_max_right C 1
  have hδ_pos : 0 < δ := h.2.1
  have ht_nonneg : 0 ≤ t := by linarith
  refine ⟨h.1, hδ_pos, hC'_pos, hs, ?_⟩
  intro x r hr
  have hr_pos : 0 < r := by linarith [hδ_pos]
  by_cases h_r1 : r ≤ 1
  · -- Case r ≤ 1: r^t ≤ r^s
    have h1 := h.2.2.2.2 x r hr
    have h_rt : r ^ t ≤ r ^ s :=
      Real.rpow_le_rpow_of_exponent_ge hr_pos h_r1 hst
    have h4 : (ENNReal.ofReal r) ^ t ≤ (ENNReal.ofReal r) ^ s := by
      have hr_nonneg' : 0 ≤ r := by linarith
      have h5 : ENNReal.ofReal (r ^ t) = (ENNReal.ofReal r) ^ t :=
        (ENNReal.ofReal_rpow_of_nonneg hr_nonneg' ht_nonneg).symm
      have h6 : ENNReal.ofReal (r ^ s) = (ENNReal.ofReal r) ^ s :=
        (ENNReal.ofReal_rpow_of_nonneg hr_nonneg' hs).symm
      rw [←h5, ←h6]
      exact ENNReal.ofReal_le_ofReal h_rt
    have h7 : ENNReal.ofReal C ≤ ENNReal.ofReal C' :=
      ENNReal.ofReal_le_ofReal (le_max_left C 1)
    have h8 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ t ≤
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s := by gcongr
    have h9 : Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) ≤
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s *
          Metric.externalCoveringNumber δ.toNNReal P := by
      calc Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r)
        ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t *
            Metric.externalCoveringNumber δ.toNNReal P := h1
      _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s *
            Metric.externalCoveringNumber δ.toNNReal P := by gcongr
    exact h9
  · -- Case r > 1: Ncover(P ∩ B) ≤ Ncover(P) ≤ C' * r^s * Ncover(P)
    have h_r_gt1 : 1 < r := by linarith
    have h5 : (P ∩ Metric.closedBall x r) ⊆ P := by simp
    have h6 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h5
    have h71 : (1 : ENNReal) ≤ ENNReal.ofReal C' := by
      simpa using ENNReal.ofReal_le_ofReal hC'_ge1
    have h72 : (1 : ENNReal) ≤ (ENNReal.ofReal r) ^ s := by
      have h73 : (1 : ℝ) ≤ r := by linarith
      have h74 : (1 : ENNReal) ≤ ENNReal.ofReal r := by
        simpa using ENNReal.ofReal_le_ofReal h73
      have h75 : ∀ (y : ENNReal), 1 ≤ y → 1 ≤ y ^ s := by
        intro y hy
        have h : (1 : ENNReal) ^ s ≤ y ^ s := by gcongr
        simpa using h
      exact h75 (ENNReal.ofReal r) h74
    have h9 : (1 : ENNReal) ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s := by
      calc (1 : ENNReal)
        = (1 : ENNReal) * (1 : ENNReal) := by simp
      _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s := by gcongr
    have h10 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
      have h : (1 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
          (ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) :=
        mul_le_mul_right' h9 (Metric.externalCoveringNumber δ.toNNReal P : ENNReal)
      simpa using h
    exact le_trans h6 h10

/-- Local squares bound: |S| ≤ 9 * Ncover(E_local) using corner packing. -/
lemma fine_local_squares_bound
    {k : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta k)
    (S : Finset (DSquare k)) (E_local : Set EuclideanPlane)
    (h1 : ∀ q ∈ S, (dSquareToDyadicSquare q).toSet ⊆ E_local) :
    (S.card : ENNReal) ≤ 9 * Metric.externalCoveringNumber δ.toNNReal E_local := by
  let corners : Set EuclideanPlane := (S.image (dSquareCorner δ) : Set EuclideanPlane)
  have h_corners_sub : corners ⊆ E_local := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
    have h_corner_in_square : dSquareCorner δ q ∈ (dSquareToDyadicSquare q).toSet := by
      have h_i_eq : (dSquareToDyadicSquare q).i = q.i := by simp [dSquareToDyadicSquare]
      have h_j_eq : (dSquareToDyadicSquare q).j = q.j := by simp [dSquareToDyadicSquare]
      have hdk : dyadicDelta k = δ := hδ_eq.symm
      have h_x : (dSquareCorner δ q) 0 = (q.i : ℝ) * δ := by simp [dSquareCorner, ep]
      have h_y : (dSquareCorner δ q) 1 = (q.j : ℝ) * δ := by simp [dSquareCorner, ep]
      have h_main : ((dSquareToDyadicSquare q).i : ℝ) * dyadicDelta k ≤ (dSquareCorner δ q) 0 ∧
          (dSquareCorner δ q) 0 < ((dSquareToDyadicSquare q).i + 1 : ℝ) * dyadicDelta k ∧
          ((dSquareToDyadicSquare q).j : ℝ) * dyadicDelta k ≤ (dSquareCorner δ q) 1 ∧
          (dSquareCorner δ q) 1 < ((dSquareToDyadicSquare q).j + 1 : ℝ) * dyadicDelta k := by
        rw [h_i_eq, h_j_eq, hdk, h_x, h_y]
        have h_pos : 0 < δ := hδ_pos
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      have h_toSet_iff : ∀ (z : EuclideanPlane), z ∈ (dSquareToDyadicSquare q).toSet ↔
          ((dSquareToDyadicSquare q).i : ℝ) * dyadicDelta k ≤ z 0 ∧
          z 0 < ((dSquareToDyadicSquare q).i + 1 : ℝ) * dyadicDelta k ∧
          ((dSquareToDyadicSquare q).j : ℝ) * dyadicDelta k ≤ z 1 ∧
          z 1 < ((dSquareToDyadicSquare q).j + 1 : ℝ) * dyadicDelta k := by
        intro z
        simp [DyadicSquare.toSet]
        <;> rfl
      exact (h_toSet_iff (dSquareCorner δ q)).mpr h_main
    exact h1 q hq h_corner_in_square
  have h_pack : (S.card : ENNReal) ≤ 9 * Metric.externalCoveringNumber δ.toNNReal corners :=
    corner_packing_bound hδ_pos hδ_eq S
  have h_mono : Metric.externalCoveringNumber δ.toNNReal corners ≤
      Metric.externalCoveringNumber δ.toNNReal E_local :=
    Metric.externalCoveringNumber_mono_set h_corners_sub
  have h_mono' : (Metric.externalCoveringNumber δ.toNNReal corners : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal E_local : ENNReal) := by
    simpa using h_mono
  have h_pack' : (S.card : ENNReal) ≤
      (9 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal corners : ENNReal) :=
    h_pack
  calc (S.card : ENNReal)
    ≤ (9 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal corners : ENNReal) := h_pack'
  _ ≤ (9 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal E_local : ENNReal) := by
    gcongr

/-- Convert point-set S-set to finset-of-DSquares S-set.
    Constant is 81 * max(C,1) * (2√2)^s. -/
lemma fine_pointset_sset_to_finset_sset
    {k : ℕ} {s t C : ℝ}
    (P : Finset (DyadicSquare k))
    (hP_nonempty : P.Nonempty)
    (E : Set EuclideanPlane)
    (hE_eq : E = ⋃ p ∈ P, (p.toSet : Set EuclideanPlane))
    (h_sset : IsDeltaSSet (dyadicDelta k) t C E)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    IsFinsetDeltaSSet (dyadicDelta k) s
      (81 * max C 1 * (2 * Real.sqrt 2) ^ s)
      (finsetDyadicToDSquare P) := by
  let δ : ℝ := dyadicDelta k
  have hδ_pos : 0 < δ := dyadicDelta_pos k
  have hδ_eq : δ = dyadicDelta k := by rfl
  let S_dsquare := finsetDyadicToDSquare P
  let C_s := max C 1
  have hC_s_pos : 0 < C_s := by positivity
  have h_sset_s : IsDeltaSSet δ s C_s E := weaken_sset_exponent h_sset hs hst
  let C' : ℝ := 81 * C_s * (2 * Real.sqrt 2) ^ s
  have hC'_pos : 0 < C' := by positivity
  have hS_nonempty : S_dsquare.Nonempty := by
    rcases hP_nonempty with ⟨p, hp⟩
    exact ⟨dyadicSquareToDSquare p, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩

  have hP_card_eq : P.card = S_dsquare.card := by
    have h : S_dsquare.card = P.card := Finset.card_image_of_injective P (by
      intro a b h
      have h' : a.i = b.i ∧ a.j = b.j := by simpa [dyadicSquareToDSquare] using h
      have h'' : a = b := by
        cases a; cases b; simp [DSquare.mk] at h' ⊢ <;> tauto
      exact h'')
    exact h.symm

  -- Ncover(E) ≤ |P|
  have h_ncover_E : Metric.externalCoveringNumber δ.toNNReal E ≤ (P.card : ENNReal) := by
    rw [hE_eq]
    let centers : Finset EuclideanPlane := P.image (fun p => squareCenter δ p)
    have h1 : (⋃ p ∈ (P : Set (DyadicSquare k)),
          (p.toSet : Set EuclideanPlane)) ⊆
        ⋃ c ∈ (centers : Set EuclideanPlane), Metric.closedBall c δ.toNNReal := by
      intro x hx
      rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
      let c := squareCenter δ p
      have hc_in : c ∈ centers := Finset.mem_image.mpr ⟨p, hp, rfl⟩
      have hcov : x ∈ Metric.closedBall c δ := dyadicSquare_covered_by_center hδ_pos hδ_eq p hxp
      have hcov' : x ∈ Metric.closedBall c δ.toNNReal := by
        have h5 : ((δ.toNNReal : ℝ)) = δ := by simp [NNReal.coe_mk, hδ_pos.le] <;> linarith
        simpa [Metric.mem_closedBall, h5] using hcov
      exact Set.mem_iUnion₂.mpr ⟨c, hc_in, hcov'⟩
    have h_iscover : Metric.IsCover δ.toNNReal
        (⋃ p ∈ (P : Set (DyadicSquare k)),
          (p.toSet : Set EuclideanPlane))
        (centers : Set EuclideanPlane) :=
      Metric.IsCover.of_subset_iUnion_closedBall h1
    have h6_enat : Metric.externalCoveringNumber δ.toNNReal
        (⋃ p ∈ (P : Set (DyadicSquare k)),
          (p.toSet : Set EuclideanPlane)) ≤
        (centers : Set EuclideanPlane).encard :=
      h_iscover.externalCoveringNumber_le_encard
    have h7 : (centers : Set EuclideanPlane).encard = ↑centers.card := by simp
    rw [h7] at h6_enat
    have h8 : centers.card ≤ P.card := Finset.card_image_le
    have h9 : Metric.externalCoveringNumber δ.toNNReal
        (⋃ p ∈ (P : Set (DyadicSquare k)),
          (p.toSet : Set EuclideanPlane)) ≤ ↑P.card := by
      calc Metric.externalCoveringNumber δ.toNNReal _
        ≤ ↑centers.card := h6_enat
      _ ≤ ↑P.card := by exact_mod_cast h8
    exact_mod_cast h9

  -- |S_dsquare| ≤ 9 * Ncover(S_dsquare : Set DSquare)
  have h_grid : (S_dsquare.card : ENNReal) ≤
      (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal (S_dsquare : Set (DSquare k)) :=
    grid_packing_dsquare hδ_pos hδ_eq S_dsquare

  have h_inner : ∀ (p' : DSquare k) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal
        ((S_dsquare : Set (DSquare k)) ∩ Metric.closedBall p' r) : ENNReal) ≤
      ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal (S_dsquare : Set (DSquare k)) : ENNReal) := by
    intro p' r hr
    let localS : Finset (DSquare k) := S_dsquare.filter (fun q => dist q p' ≤ r)
    let x : EuclideanPlane := dSquareCorner δ p'
    let R : ℝ := Real.sqrt 2 * (r + δ)
    let E_local : Set EuclideanPlane :=
      ⋃ q ∈ (localS : Set (DSquare k)), (dSquareToDyadicSquare q).toSet
    have hR_geδ : δ ≤ R := by
      have h2 : r + δ ≥ 2 * δ := by linarith
      have h3 : Real.sqrt 2 * (r + δ) ≥ Real.sqrt 2 * (2 * δ) := by gcongr
      have h4 : Real.sqrt 2 * (2 * δ) > δ := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith
    have hR_le : R ≤ (2 * Real.sqrt 2) * r := by
      have h1 : δ ≤ r := hr
      have h2 : r + δ ≤ 2 * r := by linarith
      have h3 : Real.sqrt 2 * (r + δ) ≤ Real.sqrt 2 * (2 * r) := by gcongr
      linarith

    have hE_local_sub : E_local ⊆ E ∩ Metric.closedBall x R := by
      intro z hz
      rcases Set.mem_iUnion₂.mp hz with ⟨q, hq, hzq⟩
      have hq' : q ∈ localS := hq
      have hq_S : q ∈ S_dsquare := (Finset.mem_filter.mp hq').1
      have hq_dist : dist q p' ≤ r := (Finset.mem_filter.mp hq').2
      have hq_dy : dSquareToDyadicSquare q ∈ P := by
        rcases Finset.mem_image.mp hq_S with ⟨p_dy, hp_dy, rfl⟩
        exact hp_dy
      have hz_E : z ∈ E := by
        rw [hE_eq]
        exact Set.mem_iUnion₂.mpr ⟨dSquareToDyadicSquare q, hq_dy, hzq⟩
      have hz_ball : dist z x ≤ R := by
        have h1 : dist (dSquareCorner δ q) x ≤ Real.sqrt 2 * dist q p' :=
          (dsquare_plane_metric_comparability hδ_pos hδ_eq q p').2
        have h2 : dist z (dSquareCorner δ q) ≤ Real.sqrt 2 * δ :=
          point_in_square_dist_to_corner hδ_pos hδ_eq q z hzq
        calc dist z x
          ≤ dist z (dSquareCorner δ q) + dist (dSquareCorner δ q) x := dist_triangle _ _ _
        _ ≤ Real.sqrt 2 * δ + Real.sqrt 2 * dist q p' := by gcongr
        _ ≤ Real.sqrt 2 * δ + Real.sqrt 2 * r := by gcongr
        _ = Real.sqrt 2 * (r + δ) := by ring
      have hz_ball' : z ∈ Metric.closedBall x R := by
        simpa [Metric.mem_closedBall] using hz_ball
      exact ⟨hz_E, hz_ball'⟩

    have h1 : ∀ q ∈ localS, (dSquareToDyadicSquare q).toSet ⊆ E_local := by
      intro q hq
      intro z hz
      exact Set.mem_iUnion₂.mpr ⟨q, hq, hz⟩

    have h_local_bound : (localS.card : ENNReal) ≤
        9 * Metric.externalCoveringNumber δ.toNNReal E_local :=
      fine_local_squares_bound hδ_pos hδ_eq localS E_local h1

    have h_localS_eq : (localS : Set (DSquare k)) =
        (S_dsquare : Set (DSquare k)) ∩ Metric.closedBall p' r := by
      ext q
      simp only [localS, Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff,
        Metric.mem_closedBall]
      <;> rfl

    have h_ncover_local : (Metric.externalCoveringNumber δ.toNNReal
        ((S_dsquare : Set (DSquare k)) ∩ Metric.closedBall p' r) : ENNReal) ≤
        (localS.card : ENNReal) := by
      let hcover : Metric.IsCover δ.toNNReal (localS : Set (DSquare k)) (localS : Set (DSquare k)) :=
        Metric.IsCover.of_subset_iUnion_closedBall (by
          intro y hy
          exact Set.mem_iUnion₂.mpr ⟨y, hy, Metric.mem_closedBall_self (by positivity)⟩)
      have h2 : Metric.externalCoveringNumber δ.toNNReal (localS : Set (DSquare k)) ≤
          (localS : Set (DSquare k)).encard := hcover.externalCoveringNumber_le_encard
      have h3 : (localS : Set (DSquare k)).encard = ↑localS.card := by simp
      rw [h3] at h2
      have h4 : (Metric.externalCoveringNumber δ.toNNReal
          ((S_dsquare : Set (DSquare k)) ∩ Metric.closedBall p' r) : ENNReal) ≤
          (Metric.externalCoveringNumber δ.toNNReal (localS : Set (DSquare k)) : ENNReal) := by
        rw [h_localS_eq]
      have h5 : (Metric.externalCoveringNumber δ.toNNReal (localS : Set (DSquare k)) : ENNReal) ≤
          (localS.card : ENNReal) := by
        exact_mod_cast h2
      exact le_trans h4 h5

    have h_sset_bound : (Metric.externalCoveringNumber δ.toNNReal (E ∩ Metric.closedBall x R) : ENNReal) ≤
        ENNReal.ofReal C_s * (ENNReal.ofReal R) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal E : ENNReal) :=
      h_sset_s.2.2.2.2 x R hR_geδ

    have h_mono : (Metric.externalCoveringNumber δ.toNNReal E_local : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal (E ∩ Metric.closedBall x R) : ENNReal) := by
      have h_mono_nnreal : Metric.externalCoveringNumber δ.toNNReal E_local ≤
          Metric.externalCoveringNumber δ.toNNReal (E ∩ Metric.closedBall x R) :=
        Metric.externalCoveringNumber_mono_set hE_local_sub
      exact_mod_cast h_mono_nnreal

    have hR_pow : (ENNReal.ofReal R) ^ s ≤
        ENNReal.ofReal ((2 * Real.sqrt 2) ^ s) * (ENNReal.ofReal r) ^ s := by
      have h : (ENNReal.ofReal R) ^ s ≤ (ENNReal.ofReal ((2 * Real.sqrt 2) * r)) ^ s := by
        gcongr <;> linarith
      have h2 : (ENNReal.ofReal ((2 * Real.sqrt 2) * r)) ^ s =
          ENNReal.ofReal ((2 * Real.sqrt 2) ^ s) * (ENNReal.ofReal r) ^ s := by
        have h3 : 0 ≤ (2 * Real.sqrt 2) := by positivity
        have h4 : 0 ≤ r := by linarith
        have h5 : ENNReal.ofReal ((2 * Real.sqrt 2) * r) =
            ENNReal.ofReal (2 * Real.sqrt 2) * ENNReal.ofReal r := by
          rw [ENNReal.ofReal_mul h3]
        rw [h5]
        have h6 : (ENNReal.ofReal (2 * Real.sqrt 2) * ENNReal.ofReal r) ^ s =
            (ENNReal.ofReal (2 * Real.sqrt 2)) ^ s * (ENNReal.ofReal r) ^ s := by
          exact ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal (2 * √2)) (ENNReal.ofReal r) hs
        rw [h6]
        have h7 : (ENNReal.ofReal (2 * Real.sqrt 2)) ^ s =
            ENNReal.ofReal ((2 * Real.sqrt 2) ^ s) := by
          rw [ENNReal.ofReal_rpow_of_nonneg h3 hs]
        rw [h7] <;> rfl
      rw [h2] at h
      exact h

    have hC'_eq : ENNReal.ofReal C' =
        (81 : ENNReal) * ENNReal.ofReal C_s * ENNReal.ofReal ((2 * Real.sqrt 2) ^ s) := by
      have h_pos3 : 0 ≤ (81 : ℝ) * C_s := by positivity
      have h_pos4 : 0 ≤ (2 * Real.sqrt 2) ^ s := by positivity
      have h_pos5 : 0 ≤ (81 : ℝ) * C_s * (2 * Real.sqrt 2) ^ s := by positivity
      simp [C', ENNReal.ofReal_mul h_pos3, ENNReal.ofReal_mul h_pos5] <;> ring_nf

    calc (Metric.externalCoveringNumber δ.toNNReal
        ((S_dsquare : Set (DSquare k)) ∩ Metric.closedBall p' r) : ENNReal)
      ≤ (localS.card : ENNReal) := h_ncover_local
    _ ≤ 9 * (Metric.externalCoveringNumber δ.toNNReal E_local : ENNReal) := by
        exact_mod_cast h_local_bound
    _ ≤ 9 * (Metric.externalCoveringNumber δ.toNNReal (E ∩ Metric.closedBall x R) : ENNReal) := by
        gcongr <;> exact h_mono
    _ ≤ 9 * (ENNReal.ofReal C_s * (ENNReal.ofReal R) ^ s *
              (Metric.externalCoveringNumber δ.toNNReal E : ENNReal)) := by gcongr
    _ ≤ 9 * (ENNReal.ofReal C_s * (ENNReal.ofReal R) ^ s * (P.card : ENNReal)) := by
        gcongr <;> exact h_ncover_E
    _ = 9 * ENNReal.ofReal C_s * (ENNReal.ofReal R) ^ s * (P.card : ENNReal) := by ring
    _ = 9 * ENNReal.ofReal C_s * (ENNReal.ofReal R) ^ s * (S_dsquare.card : ENNReal) := by
        rw [hP_card_eq]
    _ ≤ 9 * ENNReal.ofReal C_s * (ENNReal.ofReal R) ^ s *
          ((9 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (S_dsquare : Set (DSquare k)) : ENNReal)) := by
        gcongr <;> exact h_grid
    _ = (81 : ENNReal) * ENNReal.ofReal C_s * (ENNReal.ofReal R) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal (S_dsquare : Set (DSquare k)) : ENNReal) := by ring
    _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal (S_dsquare : Set (DSquare k)) : ENNReal) := by
        rw [hC'_eq]
        have h_bound2 : (81 : ENNReal) * ENNReal.ofReal C_s * (ENNReal.ofReal R) ^ s ≤
            (81 : ENNReal) * ENNReal.ofReal C_s * ENNReal.ofReal ((2 * Real.sqrt 2) ^ s) * (ENNReal.ofReal r) ^ s := by
          calc (81 : ENNReal) * ENNReal.ofReal C_s * (ENNReal.ofReal R) ^ s
            ≤ (81 : ENNReal) * ENNReal.ofReal C_s *
                (ENNReal.ofReal ((2 * Real.sqrt 2) ^ s) * (ENNReal.ofReal r) ^ s) := by gcongr <;> exact hR_pow
          _ = (81 : ENNReal) * ENNReal.ofReal C_s * ENNReal.ofReal ((2 * Real.sqrt 2) ^ s) * (ENNReal.ofReal r) ^ s := by ring
        exact mul_le_mul_of_nonneg_right h_bound2 (by positivity)

  have h_result : IsDeltaSSet δ s C' (S_dsquare : Set (DSquare k)) :=
    ⟨hS_nonempty, hδ_pos, hC'_pos, hs, h_inner⟩
  exact h_result

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
