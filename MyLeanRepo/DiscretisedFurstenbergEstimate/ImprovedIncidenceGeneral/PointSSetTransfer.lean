module

/-
  Transfer S-set property from original finite point set P to dyadic square centers.

  Proof route:
  - Explicit 5×5 grid gives 25-fold doubling in Plane: any 2δ-ball covered by 25 δ-balls.
  - Backward matching: δ-cover of P ∩ B(c,r+δ) gives 2δ-cover of S ∩ B(c,r);
    subdivide to δ-cover with factor 25.
  - Forward matching: δ-cover of S gives 2δ-cover of P; subdivide to δ-cover with factor 25.
  - Chain:
      covering_δ(S ∩ B(c,r))
        ≤ 25 · covering_δ(P ∩ B(c,r+δ))
        ≤ 25 · C · (r+δ)^t · covering_δ(P)
        ≤ 25 · C · (2r)^t · 25 · covering_δ(S)
        = C · 625 · 2^t · r^t · covering_δ(S)

  Whiteprint node: point_sset_transfer
  Dependencies: DyadicBridge (dyadicSquareCenter), discretised_furstenberg_estimate (IsDeltaSSet)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicBridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate

-- ============================================================================
-- edist / dist conversion helpers
-- ============================================================================

lemma edist_to_dist {x y : Plane} {ε : ℝ} (hε : 0 ≤ ε)
    (h : edist x y ≤ ε.toNNReal) : dist x y ≤ ε := by
  have h2 : (ε.toNNReal : ENNReal) = ENNReal.ofReal ε := ENNReal.ofNNReal_toNNReal ε
  have h3 : edist x y ≤ ENNReal.ofReal ε := by
    rw [h2] at h
    exact h
  exact (edist_le_ofReal hε).mp h3

lemma dist_to_edist {x y : Plane} {ε : ℝ} (hε : 0 ≤ ε)
    (h : dist x y ≤ ε) : edist x y ≤ ε.toNNReal := by
  have h1 : ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal h
  have h2 : (ε.toNNReal : ENNReal) = ENNReal.ofReal ε := ENNReal.ofNNReal_toNNReal ε
  have h3 : edist x y = ENNReal.ofReal (dist x y) := by rw [edist_dist]
  rw [h3, h2]
  exact h1

-- ============================================================================
-- Grid-point helper for explicit doubling
-- ============================================================================

/-- A grid point x + (i*δ, j*δ). -/
noncomputable def gridPoint (x : Plane) (δ : ℝ) (ij : ℤ × ℤ) : Plane :=
  WithLp.toLp 2 fun k : Fin 2 =>
    if k = 0 then x 0 + (ij.1 : ℝ) * δ
    else x 1 + (ij.2 : ℝ) * δ

/-- For any real a with |a| ≤ 2δ, find i ∈ {-2,-1,0,1,2} with |a - i*δ| ≤ δ/2. -/
lemma nearest_grid_int (a δ : ℝ) (hδ : 0 < δ) (h : |a| ≤ 2 * δ) :
    ∃ (i : ℤ), i ∈ Finset.Icc (-2 : ℤ) 2 ∧ |a - (i : ℝ) * δ| ≤ δ / 2 := by
  have h1 : -2 * δ ≤ a := by linarith [abs_le.mp h]
  have h2 : a ≤ 2 * δ := by linarith [abs_le.mp h]
  by_cases h3 : a ≤ -3 * δ / 2
  · refine' ⟨-2, by simp [Finset.mem_Icc] <;> norm_num, _⟩
    have h4 : 0 ≤ a + 2 * δ := by linarith
    have h5 : a + 2 * δ ≤ δ / 2 := by linarith
    have h6 : |a + 2 * δ| ≤ δ / 2 := by rw [abs_of_nonneg h4] <;> linarith
    have h7 : a - ((-2 : ℤ) : ℝ) * δ = a + 2 * δ := by simp <;> ring
    rw [h7]; exact h6
  · by_cases h4 : a ≤ -δ / 2
    · refine' ⟨-1, by simp [Finset.mem_Icc] <;> norm_num, _⟩
      have h5 : |a + δ| ≤ δ / 2 := by rw [abs_le] <;> constructor <;> linarith
      have h7 : a - ((-1 : ℤ) : ℝ) * δ = a + δ := by simp <;> ring
      rw [h7]; exact h5
    · by_cases h5 : a ≤ δ / 2
      · refine' ⟨0, by simp [Finset.mem_Icc] <;> norm_num, _⟩
        have h6 : |a| ≤ δ / 2 := by rw [abs_le] <;> constructor <;> linarith
        have h7 : a - ((0 : ℤ) : ℝ) * δ = a := by simp <;> ring
        rw [h7]; exact h6
      · by_cases h6 : a ≤ 3 * δ / 2
        · refine' ⟨1, by simp [Finset.mem_Icc] <;> norm_num, _⟩
          have h7 : |a - δ| ≤ δ / 2 := by rw [abs_le] <;> constructor <;> linarith
          have h8 : a - ((1 : ℤ) : ℝ) * δ = a - δ := by simp <;> ring
          rw [h8]; exact h7
        · refine' ⟨2, by simp [Finset.mem_Icc] <;> norm_num, _⟩
          have h7 : |a - 2 * δ| ≤ δ / 2 := by rw [abs_le] <;> constructor <;> linarith
          have h8 : a - ((2 : ℤ) : ℝ) * δ = a - 2 * δ := by simp <;> ring
          rw [h8]; exact h7

/-- The 5×5 grid of points around x at spacing δ. -/
noncomputable def planeGrid (x : Plane) (δ : ℝ) : Finset Plane :=
  let idx : Finset (ℤ × ℤ) := (Finset.Icc (-2 : ℤ) 2) ×ˢ (Finset.Icc (-2 : ℤ) 2)
  Finset.image (gridPoint x δ) idx

lemma planeGrid_card (x : Plane) (δ : ℝ) : (planeGrid x δ).card ≤ 25 := by
  let idx : Finset (ℤ × ℤ) := (Finset.Icc (-2 : ℤ) 2) ×ˢ (Finset.Icc (-2 : ℤ) 2)
  have h : (planeGrid x δ).card ≤ idx.card := Finset.card_image_le
  have h2 : idx.card = 25 := by
    simp [idx, Finset.card_product] <;> decide
  rw [h2] at h
  exact h

/-- Any point within 2δ of x is within δ of some grid point. -/
lemma planeGrid_cover (x : Plane) {δ : ℝ} (hδ : 0 < δ) {z : Plane} (h : dist z x ≤ 2 * δ) :
    ∃ y ∈ planeGrid x δ, dist z y ≤ δ := by
  let u := z - x
  have h_norm : ‖u‖ ≤ 2 * δ := by simpa [dist_eq_norm] using h
  have h_norm_sq : ‖u‖ ^ 2 = (u 0)^2 + (u 1)^2 := by
    have h4 : ‖u‖ = Real.sqrt ((u 0)^2 + (u 1)^2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring
    rw [h4]
    have h5 : 0 ≤ (u 0)^2 + (u 1)^2 := by positivity
    rw [Real.sq_sqrt h5]
  have h0 : |u 0| ≤ 2 * δ := by
    have h2 : (u 0)^2 ≤ ‖u‖^2 := by rw [h_norm_sq] <;> nlinarith [sq_nonneg (u 1)]
    have h3 : 0 ≤ |u 0| := by positivity
    have h4 : 0 ≤ ‖u‖ := by positivity
    nlinarith [sq_abs (u 0)]
  have h1 : |u 1| ≤ 2 * δ := by
    have h2 : (u 1)^2 ≤ ‖u‖^2 := by rw [h_norm_sq] <;> nlinarith [sq_nonneg (u 0)]
    have h3 : 0 ≤ |u 1| := by positivity
    have h4 : 0 ≤ ‖u‖ := by positivity
    nlinarith [sq_abs (u 1)]
  rcases nearest_grid_int (u 0) δ hδ h0 with ⟨i, hi, h_i⟩
  rcases nearest_grid_int (u 1) δ hδ h1 with ⟨j, hj, h_j⟩
  let y := gridPoint x δ (i, j)
  let idx : Finset (ℤ × ℤ) := (Finset.Icc (-2 : ℤ) 2) ×ˢ (Finset.Icc (-2 : ℤ) 2)
  have hij : (i, j) ∈ idx := by
    simp [idx, Finset.mem_product, hi, hj] <;> norm_num
  have hy : y ∈ planeGrid x δ :=
    Finset.mem_image.mpr ⟨(i, j), hij, rfl⟩
  have h_eq0 : (z - y) 0 = u 0 - (i : ℝ) * δ := by
    simp [u, y, gridPoint] <;> ring
  have h_eq1 : (z - y) 1 = u 1 - (j : ℝ) * δ := by
    simp [u, y, gridPoint] <;> ring
  have h_dist0 : |(z - y) 0| ≤ δ / 2 := by
    rw [h_eq0] <;> exact h_i
  have h_dist1 : |(z - y) 1| ≤ δ / 2 := by
    rw [h_eq1] <;> exact h_j
  have h_zy_norm_sq : ‖z - y‖ ^ 2 = ((z - y) 0)^2 + ((z - y) 1)^2 := by
    have h4 : ‖z - y‖ = Real.sqrt (((z - y) 0)^2 + ((z - y) 1)^2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring
    rw [h4]
    have h5 : 0 ≤ ((z - y) 0)^2 + ((z - y) 1)^2 := by positivity
    rw [Real.sq_sqrt h5]
  have h6 : ‖z - y‖ ^ 2 ≤ δ^2 := by
    rw [h_zy_norm_sq]
    have h7 : ((z - y) 0)^2 ≤ (δ / 2)^2 := by
      have h8 : |(z - y) 0| ≤ δ / 2 := h_dist0
      nlinarith [abs_le.mp h8]
    have h9 : ((z - y) 1)^2 ≤ (δ / 2)^2 := by
      have h10 : |(z - y) 1| ≤ δ / 2 := h_dist1
      nlinarith [abs_le.mp h10]
    nlinarith
  have h10 : ‖z - y‖ ≤ δ := by
    have h11 : 0 ≤ ‖z - y‖ := by positivity
    nlinarith
  exact ⟨y, hy, by simpa [dist_eq_norm] using h10⟩

-- ============================================================================
-- Cover subdivision: 2δ-cover → δ-cover with 25× more balls
-- ============================================================================

/-- Convert a 2δ-cover of A into a δ-cover with at most 25× the cardinal. -/
lemma cover_subdivide_25 {δ : ℝ} (hδ : 0 < δ) {A : Set Plane} {C : Set Plane}
    (hC : Metric.IsCover (2 * δ).toNNReal A C) :
    ∃ (C' : Set Plane), Metric.IsCover δ.toNNReal A C' ∧ C'.encard ≤ (25 : ℕ∞) * C.encard := by
  let C' : Set Plane := {y : Plane | ∃ x ∈ C, y ∈ planeGrid x δ}
  have h_cover : Metric.IsCover δ.toNNReal A C' := by
    intro z hz
    rcases hC hz with ⟨x, hx, hball⟩
    have h_dist : dist z x ≤ 2 * δ := edist_to_dist (by linarith) hball
    rcases planeGrid_cover x hδ h_dist with ⟨y, hy_grid, h_y_dist⟩
    have hy : y ∈ C' := ⟨x, hx, hy_grid⟩
    have h_edist : edist z y ≤ δ.toNNReal := dist_to_edist (by linarith) h_y_dist
    exact ⟨y, hy, h_edist⟩
  by_cases hfin : C.Finite
  · let Cfin := hfin.toFinset
    let C'fin : Finset Plane := Cfin.biUnion (fun x => planeGrid x δ)
    have hC'fin : (C'fin : Set Plane) = C' := by
      ext y
      simp [C'fin, C', Finset.mem_biUnion]
      <;> aesop
    have h_card : C'fin.card ≤ 25 * Cfin.card := by
      calc C'fin.card
        ≤ ∑ x ∈ Cfin, (planeGrid x δ).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ Cfin, 25 := by gcongr; exact planeGrid_card _ _
      _ = 25 * Cfin.card := by simp [mul_comm]
    have h_encard : C'.encard = ↑C'fin.card := by
      have h4 : C' = (C'fin : Set Plane) := hC'fin.symm
      rw [h4]
      simp
    have h_C_encard : C.encard = ↑Cfin.card := by
      have h4 : C = (Cfin : Set Plane) := by
        exact hfin.coe_toFinset.symm
      rw [h4]
      simp
    refine' ⟨C', h_cover, _⟩
    rw [h_encard, h_C_encard]
    exact_mod_cast h_card
  · have h_top : C.encard = ⊤ := by
      exact Set.encard_eq_top_iff.mpr hfin
    refine' ⟨C', h_cover, _⟩
    rw [h_top]
    <;> simp

-- ============================================================================
-- Covering-number bound via cover conversion
-- ============================================================================

/-- If every ε-cover of B can be converted to a δ-cover of A with ≤ 25× cardinal,
    then covering_δ(A) ≤ 25 * covering_ε(B). -/
lemma covering_bound_25 {ε δ : NNReal} {A B : Set Plane}
    (h : ∀ (C : Set Plane), Metric.IsCover ε B C →
      ∃ (C' : Set Plane), Metric.IsCover δ A C' ∧ C'.encard ≤ (25 : ℕ∞) * C.encard) :
    Metric.externalCoveringNumber δ A ≤ (25 : ℕ∞) * Metric.externalCoveringNumber ε B := by
  have h_main : ∀ (C : Set Plane), ∀ (hC : Metric.IsCover ε B C),
      Metric.externalCoveringNumber δ A ≤ (25 : ℕ∞) * C.encard := by
    intro C hC
    rcases h C hC with ⟨C', hC'_cover, hC'_card⟩
    have h2 : Metric.externalCoveringNumber δ A ≤ C'.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hC'_cover
    exact le_trans h2 hC'_card
  have h_step1 : ∀ (C : Set Plane),
      Metric.externalCoveringNumber δ A ≤
        iInf (fun (hC : Metric.IsCover ε B C) => (25 : ℕ∞) * C.encard) := by
    intro C
    exact le_iInf (h_main C)
  have h_step2 : Metric.externalCoveringNumber δ A ≤
      iInf (fun (C : Set Plane) =>
        iInf (fun (hC : Metric.IsCover ε B C) => (25 : ℕ∞) * C.encard)) :=
    le_iInf h_step1
  have h_mul1 : ∀ (C : Set Plane),
      iInf (fun (hC : Metric.IsCover ε B C) => (25 : ℕ∞) * C.encard)
      = (25 : ℕ∞) * iInf (fun (hC : Metric.IsCover ε B C) => C.encard) := by
    intro C
    by_cases hC : Metric.IsCover ε B C
    · have hne : Nonempty (Metric.IsCover ε B C) := ⟨hC⟩
      simp [hne, iInf_const]
      <;> rfl
    · have h_empty : IsEmpty (Metric.IsCover ε B C) := { false := hC }
      have h_iInf_top : iInf (fun (hC : Metric.IsCover ε B C) => (25 : ℕ∞) * C.encard) = ⊤ :=
        iInf_neg hC
      have h_iInf_top2 : iInf (fun (hC : Metric.IsCover ε B C) => C.encard) = ⊤ :=
        iInf_neg hC
      rw [h_iInf_top, h_iInf_top2] <;> simp
  have h_mul2 :
      iInf (fun (C : Set Plane) =>
        iInf (fun (hC : Metric.IsCover ε B C) => (25 : ℕ∞) * C.encard))
      = iInf (fun (C : Set Plane) =>
          (25 : ℕ∞) * iInf (fun (hC : Metric.IsCover ε B C) => C.encard)) := by
    apply iInf_congr
    intro C
    exact h_mul1 C
  let f : Set Plane → ℕ∞ := fun C =>
    iInf (fun (hC : Metric.IsCover ε B C) => C.encard)
  have h_mul3 :
      iInf (fun (C : Set Plane) => (25 : ℕ∞) * f C)
      = (25 : ℕ∞) * Metric.externalCoveringNumber ε B := by
    have h_eq1 : iInf (fun (C : Set Plane) => (25 : ℕ∞) * f C) =
        (25 : ℕ∞) * iInf f :=
      (ENat.mul_iInf_of_ne (show (25 : ℕ∞) ≠ 0 from by simp)).symm
    have h_def : Metric.externalCoveringNumber ε B = iInf f := by rfl
    rw [h_eq1, h_def]
  rw [h_mul2, h_mul3] at h_step2
  exact h_step2

-- ============================================================================
-- Matching-based cover conversions
-- ============================================================================

/-- Forward matching: a δ-cover of S gives a 2δ-cover of P. -/
lemma cover_forward_match {δ : ℝ} (hδ : 0 < δ) {P S : Set Plane}
    (h_match : ∀ p ∈ P, ∃ z ∈ S, dist p z ≤ δ)
    {C : Set Plane} (hC : Metric.IsCover δ.toNNReal S C) :
    Metric.IsCover (2 * δ).toNNReal P C := by
  intro p hp
  rcases h_match p hp with ⟨z, hz, hdist⟩
  rcases hC hz with ⟨x, hx, hball⟩
  have hball_dist : dist z x ≤ δ := edist_to_dist (by linarith) hball
  have h6 : dist p x ≤ 2 * δ := by
    calc dist p x ≤ dist p z + dist z x := dist_triangle _ _ _
      _ ≤ δ + δ := by gcongr
      _ = 2 * δ := by ring
  have h_edist : edist p x ≤ (2 * δ).toNNReal := dist_to_edist (by linarith) h6
  exact ⟨x, hx, h_edist⟩

/-- Backward matching for balls: a δ-cover of P ∩ B(c,r+δ) gives a 2δ-cover of S ∩ B(c,r). -/
lemma cover_backward_match_ball {δ r : ℝ} (hδ : 0 < δ) {c : Plane} {P S : Set Plane}
    (h_match : ∀ z ∈ S, ∃ p ∈ P, dist p z ≤ δ)
    {C : Set Plane} (hC : Metric.IsCover δ.toNNReal (P ∩ Metric.closedBall c (r + δ)) C) :
    Metric.IsCover (2 * δ).toNNReal (S ∩ Metric.closedBall c r) C := by
  intro z hz
  have hzS : z ∈ S := hz.1
  have hzball : dist z c ≤ r := hz.2
  rcases h_match z hzS with ⟨p, hp, hdist⟩
  have hpc : dist p c ≤ r + δ := by
    calc dist p c ≤ dist p z + dist z c := dist_triangle _ _ _
      _ ≤ δ + r := by gcongr
      _ = r + δ := by ring
  have hp' : p ∈ P ∩ Metric.closedBall c (r + δ) := ⟨hp, hpc⟩
  rcases hC hp' with ⟨x, hx, hball⟩
  have hball_dist : dist p x ≤ δ := edist_to_dist (by linarith) hball
  have h6 : dist z x ≤ 2 * δ := by
    calc dist z x ≤ dist z p + dist p x := dist_triangle _ _ _
      _ = dist p z + dist p x := by rw [dist_comm z p]
      _ ≤ δ + δ := by gcongr
      _ = 2 * δ := by ring
  have h_edist : edist z x ≤ (2 * δ).toNNReal := dist_to_edist (by linarith) h6
  exact ⟨x, hx, h_edist⟩

-- ============================================================================
-- Main theorem: S-set transfer from points to square centers
-- ============================================================================

/-- Transfer S-set property from original finite point set P to dyadic square centers.

    If P and the set S of square centers are δ-close in Hausdorff distance
    (every point of P is within δ of a center, and every center is within δ of a point),
    then the S-set constant blows up by at most 625 · 2^t. -/
lemma sset_transfer_to_centers
    {δ t C : ℝ} {n : ℕ} {P : Set Plane} {Q : Finset (DyadicSquare n)}
    (hδ_pos : 0 < δ) (ht_nonneg : 0 ≤ t) (hC_pos : 0 < C)
    (hP_sset : IsDeltaSSet δ t C P)
    (h_match_forward : ∀ p ∈ P, ∃ q ∈ Q, dist p (dyadicSquareCenter q) ≤ δ)
    (h_match_backward : ∀ q ∈ Q, ∃ p ∈ P, dist p (dyadicSquareCenter q) ≤ δ)
    (_h_inj : Set.InjOn dyadicSquareCenter (Q : Set (DyadicSquare n))) :
    IsDeltaSSet δ t (C * 625 * 2^t) (Q.image dyadicSquareCenter : Set Plane) := by
  let S : Set Plane := (Q.image dyadicSquareCenter : Set Plane)
  have hS_fin : S.Finite := Finset.finite_toSet (Finset.image dyadicSquareCenter Q)
  have hP_nonempty : P.Nonempty := hP_sset.1
  have hS_nonempty : S.Nonempty := by
    rcases hP_nonempty with ⟨p, hp⟩
    rcases h_match_forward p hp with ⟨q, hq, _⟩
    exact ⟨dyadicSquareCenter q, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
  have h_match_forward' : ∀ p ∈ P, ∃ z ∈ S, dist p z ≤ δ := by
    intro p hp
    rcases h_match_forward p hp with ⟨q, hq, hdist⟩
    exact ⟨dyadicSquareCenter q, Finset.mem_image.mpr ⟨q, hq, rfl⟩, hdist⟩
  have h_match_backward' : ∀ z ∈ S, ∃ p ∈ P, dist p z ≤ δ := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
    rcases h_match_backward q hq with ⟨p, hp, hdist⟩
    exact ⟨p, hp, hdist⟩

  -- Step 1: covering_δ(S ∩ B(c,r)) ≤ 25 * covering_δ(P ∩ B(c,r+δ))
  have h_bound1 : ∀ (c : Plane) (r : ℝ), δ ≤ r →
      Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall c r) ≤
        (25 : ℕ∞) * Metric.externalCoveringNumber δ.toNNReal
          (P ∩ Metric.closedBall c (r + δ)) := by
    intro c r hr
    apply covering_bound_25
    intro C hC
    have h2cover : Metric.IsCover (2 * δ).toNNReal (S ∩ Metric.closedBall c r) C :=
      cover_backward_match_ball hδ_pos h_match_backward' hC
    exact cover_subdivide_25 hδ_pos h2cover

  -- Step 2: covering_δ(P) ≤ 25 * covering_δ(S)
  have h_bound2 :
      Metric.externalCoveringNumber δ.toNNReal P ≤
        (25 : ℕ∞) * Metric.externalCoveringNumber δ.toNNReal S := by
    apply covering_bound_25
    intro C hC
    have h2cover : Metric.IsCover (2 * δ).toNNReal P C :=
      cover_forward_match hδ_pos h_match_forward' hC
    exact cover_subdivide_25 hδ_pos h2cover

  -- Extract S-set property for P
  have h_sset' : ∀ (c : Plane) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall c r) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ t *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) :=
    hP_sset.2.2.2.2

  refine' ⟨hS_nonempty, hδ_pos, by positivity, ht_nonneg, _⟩
  intro c r hr

  -- Power bounds
  have hr_pos : 0 < r := by linarith
  have h_radd : r + δ ≤ 2 * r := by linarith
  have h_rpow1 : (ENNReal.ofReal (r + δ)) ^ t ≤ (ENNReal.ofReal (2 * r)) ^ t := by
    gcongr <;> linarith
  have h_rpow2 : (ENNReal.ofReal (2 * r)) ^ t =
      (ENNReal.ofReal 2) ^ t * (ENNReal.ofReal r) ^ t := by
    have h1 : (ENNReal.ofReal (2 * r)) ^ t = ENNReal.ofReal ((2 * r) ^ t) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    rw [h1]
    have h2 : (2 * r) ^ t = (2 : ℝ)^t * r^t := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [h2]
    have h3 : ENNReal.ofReal ((2 : ℝ)^t * r^t) =
        ENNReal.ofReal ((2 : ℝ)^t) * ENNReal.ofReal (r^t) := by
      rw [ENNReal.ofReal_mul (by positivity)]
    rw [h3]
    have h4 : ENNReal.ofReal ((2 : ℝ)^t) = (ENNReal.ofReal 2) ^ t := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    have h5 : ENNReal.ofReal (r^t) = (ENNReal.ofReal r) ^ t := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    rw [h4, h5]

  -- Coerce the ℕ∞ bounds to ENNReal
  have h_bound1' : (Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall c r) : ENNReal) ≤
      (25 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal
        (P ∩ Metric.closedBall c (r + δ)) : ENNReal) := by
    exact_mod_cast h_bound1 c r hr
  have h_bound2' : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
      (25 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := by
    exact_mod_cast h_bound2

  have h_sset_val : (Metric.externalCoveringNumber δ.toNNReal
          (P ∩ Metric.closedBall c (r + δ)) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (r + δ)) ^ t *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) :=
    h_sset' c (r + δ) (by linarith)

  set cov_SB := (Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall c r) : ENNReal)
  set cov_PB := (Metric.externalCoveringNumber δ.toNNReal
        (P ∩ Metric.closedBall c (r + δ)) : ENNReal)
  set cov_P := (Metric.externalCoveringNumber δ.toNNReal P : ENNReal)
  set cov_S := (Metric.externalCoveringNumber δ.toNNReal S : ENNReal)
  set C' := ENNReal.ofReal C
  set rpow_r := (ENNReal.ofReal r) ^ t
  set rpow_2 := (ENNReal.ofReal 2) ^ t

  have h_a : cov_SB ≤ (25 : ENNReal) * cov_PB := h_bound1'
  have h_b : cov_PB ≤ C' * (ENNReal.ofReal (r + δ)) ^ t * cov_P := h_sset_val
  have h_c : C' * (ENNReal.ofReal (r + δ)) ^ t * cov_P ≤ C' * (ENNReal.ofReal (2 * r)) ^ t * cov_P := by
    gcongr
    <;> exact h_rpow1
  have h_d : C' * (ENNReal.ofReal (2 * r)) ^ t * cov_P = C' * (rpow_2 * rpow_r) * cov_P := by
    rw [h_rpow2] <;> ring
  have h_e : C' * (rpow_2 * rpow_r) * cov_P ≤ C' * (rpow_2 * rpow_r) * ((25 : ENNReal) * cov_S) := by
    gcongr
  have h_f : (25 : ENNReal) * (C' * (rpow_2 * rpow_r) * ((25 : ENNReal) * cov_S)) =
      ENNReal.ofReal (C * 625 * 2^t) * rpow_r * cov_S := by
    have h_ofReal2 : rpow_2 = ENNReal.ofReal ((2 : ℝ)^t) := by
      have h_unfold : rpow_2 = (ENNReal.ofReal 2) ^ t := by simp [rpow_2]
      rw [h_unfold]
      exact ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)
    rw [h_ofReal2]
    have h_expand : ENNReal.ofReal (C * 625 * 2^t) =
        C' * (625 : ENNReal) * ENNReal.ofReal ((2 : ℝ)^t) := by
      have h1 : ENNReal.ofReal (C * 625 * 2^t) =
          C' * ENNReal.ofReal (625 : ℝ) * ENNReal.ofReal ((2 : ℝ)^t) := by
        rw [show C * 625 * 2^t = C * (625 : ℝ) * (2^t) by ring]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        <;> ring
      rw [h1] <;> norm_num
    rw [h_expand]
    simp [mul_assoc, mul_comm, mul_left_comm]
    <;> ring_nf
    <;> simp [mul_assoc, mul_comm, mul_left_comm]
  have h_main : cov_SB ≤ (25 : ENNReal) * (C' * (rpow_2 * rpow_r) * ((25 : ENNReal) * cov_S)) := by
    calc cov_SB
      ≤ (25 : ENNReal) * cov_PB := h_a
    _ ≤ (25 : ENNReal) * (C' * (ENNReal.ofReal (r + δ)) ^ t * cov_P) := by gcongr
    _ ≤ (25 : ENNReal) * (C' * (ENNReal.ofReal (2 * r)) ^ t * cov_P) := by gcongr
    _ = (25 : ENNReal) * (C' * (rpow_2 * rpow_r) * cov_P) := by rw [h_d]
    _ ≤ (25 : ENNReal) * (C' * (rpow_2 * rpow_r) * ((25 : ENNReal) * cov_S)) := by gcongr
  rw [h_f] at h_main
  exact h_main

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
