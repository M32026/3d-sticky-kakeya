module

/-
  Incidence and property transfer under snapping for Option 1.

  Provides:
  1. `iSnap_movement_lt_half`: movement < Δ/2 at scale Δ/20
  2. `iSnap_injective_on_separated`: injectivity on Δ-separated sets
  3. `iSnap_card_preservation`: cardinality preservation
  4. `snap_assignedCount_dist`: tube-to-tube distance transfer (Δ → 2Δ)
  5. `snap_near_point`: point-to-line incidence transfer (Δ → 2Δ)
  6. `iSnap_slope_bound`, `iSnap_intercept_bound`, `iSnap_v1`: property preservation

  S-set transfer is already in SnappingSSetTransfer.lean:
    `IsDeltaSSet.affineLine_snap`
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.SnappingSSetTransfer
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.SnapTransfer

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Snapping
open LemmaE
open TubesAndSlopes

attribute [local instance] Classical.propDecidable

/-- Snap scale for injectivity: Δ / 20. -/
def injectSnapScale (Δ : ℝ) : ℝ := Δ / 20

/-- Abbreviation for snap at injectivity scale. -/
def iSnap (Δ : ℝ) : AffineLine → AffineLine :=
  affineLineSnap (injectSnapScale Δ)

/-- Movement bound: dist(ℓ, iSnap Δ ℓ) < Δ/2 for 0 < Δ ≤ 1, B ≤ 2. -/
lemma iSnap_movement_lt_half {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_le_one : Δ ≤ 1)
    {ℓ : AffineLine} (h_slope : |(affineLineParams ℓ).1| ≤ 1)
    (h_intercept : |(affineLineParams ℓ).2| ≤ 2)
    (h_v1 : (getDirV ℓ) 1 ≠ 0) :
    AffineLine.dist ℓ (iSnap Δ ℓ) < Δ / 2 := by
  let ε := injectSnapScale Δ
  have hε_pos : 0 < ε := by
    dsimp only [ε]; exact div_pos hΔ_pos (by norm_num)
  have hε_eq : ε = Δ / 20 := by rfl
  have hε_le_one : ε ≤ 1 := by
    rw [hε_eq]
    have h : Δ ≤ 1 := hΔ_le_one
    have h2 : Δ / 20 ≤ 1 / 20 := by
      have h3 : (1 / 20 : ℝ) * Δ ≤ (1 / 20 : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left h (by norm_num)
      have h4 : (1 / 20 : ℝ) * Δ = Δ / 20 := by ring
      have h5 : (1 / 20 : ℝ) * 1 = 1 / 20 := by ring
      rw [h4, h5] at h3
      exact h3
    have h6 : (1 : ℝ) / 20 ≤ 1 := by norm_num
    linarith
  have h1 : AffineLine.dist ℓ (affineLineSnap ε ℓ) ≤ (3 + (2 : ℝ) + ε) * ε :=
    affineLineSnap_near ε hε_pos hε_le_one ℓ 2 (by norm_num) h_v1 h_slope h_intercept
  have h_main : (3 + (2 : ℝ) + ε) * ε < Δ / 2 := by
    rw [hε_eq]
    nlinarith
  exact lt_of_le_of_lt h1 h_main

/-- iSnap is injective on a Δ-separated set. -/
lemma iSnap_injective_on_separated {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_le_one : Δ ≤ 1)
    {S : Finset AffineLine}
    (h_separated : ∀ ℓ1 ∈ S, ∀ ℓ2 ∈ S, ℓ1 ≠ ℓ2 → Δ ≤ AffineLine.dist ℓ1 ℓ2)
    (h_slope : ∀ ℓ ∈ S, |(affineLineParams ℓ).1| ≤ 1)
    (h_intercept : ∀ ℓ ∈ S, |(affineLineParams ℓ).2| ≤ 2)
    (h_v1 : ∀ ℓ ∈ S, (getDirV ℓ) 1 ≠ 0) :
    Set.InjOn (iSnap Δ) (S : Set AffineLine) := by
  intro ℓ1 hℓ1 ℓ2 hℓ2 h_eq
  by_contra hne
  have h_sep : Δ ≤ AffineLine.dist ℓ1 ℓ2 := h_separated ℓ1 hℓ1 ℓ2 hℓ2 hne
  have h_move1 : AffineLine.dist ℓ1 (iSnap Δ ℓ1) < Δ / 2 :=
    iSnap_movement_lt_half hΔ_pos hΔ_le_one (h_slope ℓ1 hℓ1) (h_intercept ℓ1 hℓ1) (h_v1 ℓ1 hℓ1)
  have h_move2 : AffineLine.dist ℓ2 (iSnap Δ ℓ2) < Δ / 2 :=
    iSnap_movement_lt_half hΔ_pos hΔ_le_one (h_slope ℓ2 hℓ2) (h_intercept ℓ2 hℓ2) (h_v1 ℓ2 hℓ2)
  have h_snap_eq : iSnap Δ ℓ1 = iSnap Δ ℓ2 := h_eq
  have h_dist : AffineLine.dist ℓ1 ℓ2 < Δ := by
    have h_tri : AffineLine.dist ℓ1 ℓ2 ≤
        AffineLine.dist ℓ1 (iSnap Δ ℓ1) + AffineLine.dist (iSnap Δ ℓ1) ℓ2 :=
      dist_triangle ℓ1 (iSnap Δ ℓ1) ℓ2
    have h_comm : AffineLine.dist (iSnap Δ ℓ1) ℓ2 = AffineLine.dist ℓ2 (iSnap Δ ℓ1) := by
      exact Eq.symm (dist_comm ℓ2 (iSnap Δ ℓ1))
    rw [h_comm] at h_tri
    have h_move2' : AffineLine.dist ℓ2 (iSnap Δ ℓ1) < Δ / 2 := by
      have h_eq2 : iSnap Δ ℓ1 = iSnap Δ ℓ2 := h_snap_eq
      rw [h_eq2]
      exact h_move2
    linarith [h_tri, h_move1, h_move2']
  linarith

/-- Cardinality preserved under iSnap for Δ-separated finite sets. -/
lemma iSnap_card_preservation {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_le_one : Δ ≤ 1)
    {S : Finset AffineLine}
    (h_separated : ∀ ℓ1 ∈ S, ∀ ℓ2 ∈ S, ℓ1 ≠ ℓ2 → Δ ≤ AffineLine.dist ℓ1 ℓ2)
    (h_slope : ∀ ℓ ∈ S, |(affineLineParams ℓ).1| ≤ 1)
    (h_intercept : ∀ ℓ ∈ S, |(affineLineParams ℓ).2| ≤ 2)
    (h_v1 : ∀ ℓ ∈ S, (getDirV ℓ) 1 ≠ 0) :
    (Finset.image (iSnap Δ) S).card = S.card := by
  have h_inj := iSnap_injective_on_separated hΔ_pos hΔ_le_one h_separated h_slope h_intercept h_v1
  rw [Finset.card_image_of_injOn h_inj]

/-- Tube-to-tube distance transfer: if dist(T, boldT) ≤ Δ, then
    dist(T, iSnap(boldT)) ≤ 2Δ. -/
lemma snap_assignedCount_dist {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_le_one : Δ ≤ 1)
    {T boldT : AffineLine}
    (h_slope : |(affineLineParams boldT).1| ≤ 1)
    (h_intercept : |(affineLineParams boldT).2| ≤ 2)
    (h_v1 : (getDirV boldT) 1 ≠ 0)
    (h : AffineLine.dist T boldT ≤ Δ) :
    AffineLine.dist T (iSnap Δ boldT) ≤ 2 * Δ := by
  have h_move : AffineLine.dist boldT (iSnap Δ boldT) < Δ / 2 :=
    iSnap_movement_lt_half hΔ_pos hΔ_le_one h_slope h_intercept h_v1
  have h_tri : AffineLine.dist T (iSnap Δ boldT) ≤
      AffineLine.dist T boldT + AffineLine.dist boldT (iSnap Δ boldT) :=
    dist_triangle T boldT (iSnap Δ boldT)
  have h_main : AffineLine.dist T (iSnap Δ boldT) ≤ Δ + Δ / 2 := by
    calc AffineLine.dist T (iSnap Δ boldT)
      ≤ AffineLine.dist T boldT + AffineLine.dist boldT (iSnap Δ boldT) := h_tri
    _ ≤ Δ + Δ / 2 := by gcongr <;> linarith
  linarith

/-- Point-to-line incidence transfer: if p is within Δ of ℓ and ‖p‖ ≤ 1,
    then p is within 2Δ of iSnap(ℓ). -/
lemma snap_near_point {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_le_one : Δ ≤ 1)
    {ℓ : AffineLine} {p : EuclideanPlane}
    (h_slope : |(affineLineParams ℓ).1| ≤ 1)
    (h_intercept : |(affineLineParams ℓ).2| ≤ 2)
    (h_v1 : (getDirV ℓ) 1 ≠ 0)
    (hp_norm : ‖p‖ ≤ 1)
    (hp_near : p ∈ Metric.cthickening Δ (ℓ.1 : Set EuclideanPlane)) :
    p ∈ Metric.cthickening (2 * Δ) ((iSnap Δ ℓ).1 : Set EuclideanPlane) := by
  let ε := injectSnapScale Δ
  have hε_pos : 0 < ε := by dsimp only [ε]; exact div_pos hΔ_pos (by norm_num)
  let q : EuclideanPlane := EuclideanGeometry.orthogonalProjection ℓ.1 p
  have hq_in : q ∈ (ℓ.1 : Set EuclideanPlane) := EuclideanGeometry.orthogonalProjection_mem p
  have hdist_pq : dist p q ≤ Δ := by
    have h_infEDist : Metric.infEDist p (ℓ.1 : Set EuclideanPlane) ≤ ENNReal.ofReal Δ :=
      Metric.mem_cthickening_iff.mp hp_near
    have h_ne_top : Metric.infEDist p (ℓ.1 : Set EuclideanPlane) ≠ ⊤ :=
      Metric.infEDist_ne_top ℓ.nonempty
    have h_infDist : Metric.infDist p (ℓ.1 : Set EuclideanPlane) ≤ Δ := by
      have h_eq : Metric.infDist p (ℓ.1 : Set EuclideanPlane) =
          ENNReal.toReal (Metric.infEDist p (ℓ.1 : Set EuclideanPlane)) := by rfl
      rw [h_eq]
      have h5 : ENNReal.toReal (ENNReal.ofReal Δ) = Δ := by simp [hΔ_pos.le]
      have h6 : ENNReal.toReal (Metric.infEDist p (ℓ.1 : Set EuclideanPlane)) ≤
          ENNReal.toReal (ENNReal.ofReal Δ) :=
        ENNReal.toReal_le_toReal h_ne_top (by simp) |>.mpr h_infEDist
      rw [h5] at h6
      exact h6
    have h_eq2 : dist p q = Metric.infDist p (ℓ.1 : Set EuclideanPlane) :=
      EuclideanGeometry.dist_orthogonalProjection_eq_infDist ℓ.1 p
    rw [h_eq2]; exact h_infDist
  have hq_norm : ‖q‖ ≤ 1 + Δ := by
    have h_add : q = p + (q - p) := by simp [sub_add_cancel]
    rw [h_add]
    have h : ‖p + (q - p)‖ ≤ ‖p‖ + ‖q - p‖ := norm_add_le _ _
    have h2 : ‖q - p‖ = dist q p := by rw [dist_eq_norm]
    rw [h2] at h
    have h3 : dist q p = dist p q := dist_comm _ _
    rw [h3] at h
    linarith [hp_norm, hdist_pq]
  set m := (affineLineParams ℓ).1 with hm_def
  set b := (affineLineParams ℓ).2 with hb_def
  set m' := (affineLineParams (iSnap Δ ℓ)).1 with hm'_def
  set b' := (affineLineParams (iSnap Δ ℓ)).2 with hb'_def
  have h_params : affineLineParams (iSnap Δ ℓ) = (gridSnap1D ε m, gridSnap1D ε b) :=
    affineLineSnap_params ε ℓ
  have h_m'_eq : m' = gridSnap1D ε m := by simp [hm'_def, h_params]
  have h_b'_eq : b' = gridSnap1D ε b := by simp [hb'_def, h_params]
  have h_dm : |m - m'| < ε := by
    rw [h_m'_eq]; exact gridSnap1D_bound hε_pos m
  have h_db : |b - b'| < ε := by
    rw [h_b'_eq]; exact gridSnap1D_bound hε_pos b
  have hq_eq : q 0 = m * q 1 + b := affineLineParams_correct ℓ h_v1 q hq_in
  let q' : EuclideanPlane := mkPlane (m' * q 1 + b') (q 1)
  have hq'_in_line : q' ∈ (iSnap Δ ℓ).1 := by
    have h_snap_eq : iSnap Δ ℓ = makeAffineLine m' b' := by
      have h_inj : affineLineParams (iSnap Δ ℓ) = affineLineParams (makeAffineLine m' b') := by
        simp [hm'_def, hb'_def, makeAffineLine_params]
      have h_v1' : (getDirV (iSnap Δ ℓ)) 1 ≠ 0 := affineLineSnap_v1 ε ℓ
      have h_v1'' : (getDirV (makeAffineLine m' b')) 1 ≠ 0 := makeAffineLine_v1 m' b'
      exact affineLineParams_injective h_v1' h_v1'' h_inj
    rw [h_snap_eq, makeAffineLine_iff m' b' q'] <;> simp [q', mkPlane_apply0, mkPlane_apply1] <;> ring
  have hq1_abs : |q 1| ≤ ‖q‖ := coord_abs_le_norm q 1
  have h_dist_qq' : dist q q' ≤ ε * (2 + Δ) := by
    have h1 : dist q q' = |q 0 - q' 0| := by
      have h2 : q - q' = mkPlane (q 0 - q' 0) 0 := by
        ext i; fin_cases i <;> simp [q', mkPlane_apply0, mkPlane_apply1] <;> ring
      rw [dist_eq_norm, h2]
      have h3 : ‖mkPlane (q 0 - q' 0) 0‖ = |q 0 - q' 0| := by
        have h4 : ‖mkPlane (q 0 - q' 0) 0‖ ^ 2 = (q 0 - q' 0) ^ 2 := by
          simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, mkPlane_apply0, mkPlane_apply1]
          <;> ring
        have h5 : 0 ≤ ‖mkPlane (q 0 - q' 0) 0‖ := by positivity
        have h6 : 0 ≤ |q 0 - q' 0| := by positivity
        have h7 : ‖mkPlane (q 0 - q' 0) 0‖ ^ 2 = |q 0 - q' 0| ^ 2 := by
          rw [h4, sq_abs]
        nlinarith
      rw [h3]
    rw [h1]
    have h4 : q 0 - q' 0 = (m - m') * q 1 + (b - b') := by
      simp [q', hq_eq, mkPlane_apply0] <;> ring
    rw [h4]
    have h5 : |(m - m') * q 1 + (b - b')| ≤ |m - m'| * |q 1| + |b - b'| := by
      have h_abs : |(m - m') * q 1 + (b - b')| ≤ |(m - m') * q 1| + |b - b'| := by
        have h1 : -(|(m - m') * q 1| + |b - b'|) ≤ (m - m') * q 1 + (b - b') := by
          have ha : -|(m - m') * q 1| ≤ (m - m') * q 1 := (abs_le.mp (le_refl _)).1
          have hb : -|b - b'| ≤ b - b' := (abs_le.mp (le_refl _)).1
          linarith
        have h2 : (m - m') * q 1 + (b - b') ≤ |(m - m') * q 1| + |b - b'| := by
          have ha : (m - m') * q 1 ≤ |(m - m') * q 1| := (abs_le.mp (le_refl _)).2
          have hb : b - b' ≤ |b - b'| := (abs_le.mp (le_refl _)).2
          linarith
        exact abs_le.mpr ⟨h1, h2⟩
      calc |(m - m') * q 1 + (b - b')|
        ≤ |(m - m') * q 1| + |b - b'| := h_abs
      _ = |m - m'| * |q 1| + |b - b'| := by rw [abs_mul]
    have h6 : |m - m'| * |q 1| + |b - b'| ≤ ε * |q 1| + ε := by
      gcongr <;> exact (abs_lt.mp h_dm).le <;> exact (abs_lt.mp h_db).le
    have h7 : ε * |q 1| + ε ≤ ε * (1 + Δ) + ε := by
      gcongr <;> linarith [hq1_abs, hq_norm]
    linarith
  have h_dist_p_snap : dist p q' ≤ 2 * Δ := by
    calc dist p q'
      ≤ dist p q + dist q q' := dist_triangle p q q'
    _ ≤ Δ + ε * (2 + Δ) := by gcongr
    _ = Δ + ε * (2 + Δ) := by ring
    _ = Δ + (Δ / 20) * (2 + Δ) := by rw [show ε = Δ / 20 from rfl] <;> ring
    _ ≤ 2 * Δ := by nlinarith
  have h7 : Metric.infEDist p ((iSnap Δ ℓ).1 : Set EuclideanPlane) ≤ ENNReal.ofReal (dist p q') := by
    have h71 : Metric.infEDist p ((iSnap Δ ℓ).1 : Set EuclideanPlane) ≤ edist p q' :=
      Metric.infEDist_le_edist_of_mem hq'_in_line
    have h72 : edist p q' = ENNReal.ofReal (dist p q') := by
      simp [edist_dist]
    rw [h72] at h71
    exact h71
  have h8 : ENNReal.ofReal (dist p q') ≤ ENNReal.ofReal (2 * Δ) := by
    gcongr
    <;> exact h_dist_p_snap
  have h_final : Metric.infEDist p ((iSnap Δ ℓ).1 : Set EuclideanPlane) ≤ ENNReal.ofReal (2 * Δ) :=
    le_trans h7 h8
  exact Metric.mem_cthickening_iff.mpr h_final

/-- Helper: |gridSnap1D ε x| ≤ |x| + ε. -/
lemma gridSnap_abs_bound {ε x : ℝ} (hε_pos : 0 < ε) :
    |gridSnap1D ε x| ≤ |x| + ε := by
  set y := gridSnap1D ε x with hy_def
  have h2 : |x - y| < ε := gridSnap1D_bound hε_pos x
  have h3 : |y| ≤ |x| + |x - y| := by
    have h4 : y = x + (y - x) := by ring
    have h5 : ‖x + (y - x)‖ ≤ ‖x‖ + ‖y - x‖ := norm_add_le x (y - x)
    have h6 : ‖y‖ = ‖x + (y - x)‖ := by
      exact congr_arg norm h4
    have h : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
      rw [h6]
      exact h5
    have h2 : ‖y - x‖ = ‖x - y‖ := by
      have h3 : y - x = -(x - y) := by ring
      rw [h3]
      rw [norm_neg]
    rw [h2] at h
    exact h
  linarith [h2, h3]

/-- iSnap gives slope |a| ≤ 2 (safe bound). -/
lemma iSnap_slope_bound {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_le_one : Δ ≤ 1)
    {ℓ : AffineLine} (h_slope : |(affineLineParams ℓ).1| ≤ 1) :
    |(affineLineParams (iSnap Δ ℓ)).1| ≤ 2 := by
  let ε := injectSnapScale Δ
  have hε_pos : 0 < ε := by dsimp only [ε]; exact div_pos hΔ_pos (by norm_num)
  have h_params : affineLineParams (iSnap Δ ℓ) =
      (gridSnap1D ε (affineLineParams ℓ).1, gridSnap1D ε (affineLineParams ℓ).2) :=
    affineLineSnap_params ε ℓ
  have h1 : (affineLineParams (iSnap Δ ℓ)).1 = gridSnap1D ε (affineLineParams ℓ).1 := by
    simp [h_params]
  rw [h1]
  have h2 : |gridSnap1D ε (affineLineParams ℓ).1| ≤ |(affineLineParams ℓ).1| + ε :=
    gridSnap_abs_bound hε_pos
  have hε_eq : ε = Δ / 20 := by rfl
  have hε_le_one : ε ≤ 1 := by
    rw [hε_eq]
    have h : Δ ≤ 1 := hΔ_le_one
    have h2 : Δ / 20 ≤ 1 / 20 := by
      have h3 : (1 / 20 : ℝ) * Δ ≤ (1 / 20 : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left h (by norm_num)
      have h4 : (1 / 20 : ℝ) * Δ = Δ / 20 := by ring
      have h5 : (1 / 20 : ℝ) * 1 = 1 / 20 := by ring
      rw [h4, h5] at h3
      exact h3
    have h6 : (1 : ℝ) / 20 ≤ 1 := by norm_num
    linarith
  linarith [h_slope, h2, hε_le_one]

/-- iSnap gives intercept |b| ≤ 3 (safe bound). -/
lemma iSnap_intercept_bound {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_le_one : Δ ≤ 1)
    {ℓ : AffineLine} (h_intercept : |(affineLineParams ℓ).2| ≤ 2) :
    |(affineLineParams (iSnap Δ ℓ)).2| ≤ 3 := by
  let ε := injectSnapScale Δ
  have hε_pos : 0 < ε := by dsimp only [ε]; exact div_pos hΔ_pos (by norm_num)
  have h_params : affineLineParams (iSnap Δ ℓ) =
      (gridSnap1D ε (affineLineParams ℓ).1, gridSnap1D ε (affineLineParams ℓ).2) :=
    affineLineSnap_params ε ℓ
  have h1 : (affineLineParams (iSnap Δ ℓ)).2 = gridSnap1D ε (affineLineParams ℓ).2 := by
    simp [h_params]
  rw [h1]
  have h2 : |gridSnap1D ε (affineLineParams ℓ).2| ≤ |(affineLineParams ℓ).2| + ε :=
    gridSnap_abs_bound hε_pos
  have hε_eq : ε = Δ / 20 := by rfl
  have hε_le_one : ε ≤ 1 := by
    rw [hε_eq]
    have h : Δ ≤ 1 := hΔ_le_one
    have h2 : Δ / 20 ≤ 1 / 20 := by
      have h3 : (1 / 20 : ℝ) * Δ ≤ (1 / 20 : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left h (by norm_num)
      have h4 : (1 / 20 : ℝ) * Δ = Δ / 20 := by ring
      have h5 : (1 / 20 : ℝ) * 1 = 1 / 20 := by ring
      rw [h4, h5] at h3
      exact h3
    have h6 : (1 : ℝ) / 20 ≤ 1 := by norm_num
    linarith
  linarith [h_intercept, h2, hε_le_one]

/-- iSnap preserves getDirV component ≠ 0. -/
lemma iSnap_v1 {Δ : ℝ} {ℓ : AffineLine} :
    (getDirV (iSnap Δ ℓ)) 1 ≠ 0 :=
  affineLineSnap_v1 (injectSnapScale Δ) ℓ

/-- Distinct grid-snapped values differ by at least the grid scale δ. -/
lemma gridSnap1D_separation {δ : ℝ} (hδ_pos : 0 < δ) {x1 x2 : ℝ}
    (h_ne : gridSnap1D δ x1 ≠ gridSnap1D δ x2) :
    δ ≤ |gridSnap1D δ x1 - gridSnap1D δ x2| := by
  let n1 : ℤ := ⌊x1 / δ⌋
  let n2 : ℤ := ⌊x2 / δ⌋
  have h1 : gridSnap1D δ x1 = δ * (n1 : ℝ) := by rfl
  have h2 : gridSnap1D δ x2 = δ * (n2 : ℝ) := by rfl
  have h3 : n1 ≠ n2 := by
    intro h4
    have h5 : gridSnap1D δ x1 = gridSnap1D δ x2 := by
      have h6 : (n1 : ℝ) = (n2 : ℝ) := by exact_mod_cast h4
      calc gridSnap1D δ x1 = δ * (n1 : ℝ) := h1
        _ = δ * (n2 : ℝ) := by rw [h6]
        _ = gridSnap1D δ x2 := h2.symm
    exact h_ne h5
  have h4 : 1 ≤ |n1 - n2| := by
    have h41 : n1 - n2 ≠ 0 := by
      intro h
      apply h3
      linarith
    have h42 : 0 < |n1 - n2| := by
      exact abs_pos.mpr h41
    exact h42
  have h5 : (1 : ℝ) ≤ |(n1 : ℝ) - (n2 : ℝ)| := by exact_mod_cast h4
  have h_abs : |δ * ((n1 : ℝ) - (n2 : ℝ))| = δ * |(n1 : ℝ) - (n2 : ℝ)| := by
    rw [abs_mul, abs_of_pos hδ_pos]
  calc |gridSnap1D δ x1 - gridSnap1D δ x2|
    = |δ * ((n1 : ℝ) - (n2 : ℝ))| := by rw [h1, h2] <;> ring_nf
  _ = δ * |(n1 : ℝ) - (n2 : ℝ)| := h_abs
  _ ≥ δ * 1 := by gcongr
  _ = δ := by ring

/-- Generalized slope Lipschitz: |Δa| ≤ (1+M²)·dist for |a| ≤ M. -/
lemma slope_lipschitz_general {M : ℝ} (hM_nonneg : 0 ≤ M)
    (ℓ1 ℓ2 : AffineLine)
    (h1_v1 : (getDirV ℓ1) 1 ≠ 0)
    (h2_v1 : (getDirV ℓ2) 1 ≠ 0)
    (h1_slope : |(affineLineParams ℓ1).1| ≤ M)
    (h2_slope : |(affineLineParams ℓ2).1| ≤ M) :
    |(affineLineParams ℓ1).1 - (affineLineParams ℓ2).1| ≤ (1 + M^2) * AffineLine.dist ℓ1 ℓ2 := by
  let a1 := (affineLineParams ℓ1).1
  let a2 := (affineLineParams ℓ2).1
  let P1 := ℓ1.1.direction.starProjection
  let P2 := ℓ2.1.direction.starProjection
  have hP1_raw := starProjection_e2_semicircle ℓ1 h1_v1
  have hP2_raw := starProjection_e2_semicircle ℓ2 h2_v1
  have hP1_1 := hP1_raw.1
  have hP1_2 := hP1_raw.2
  have hP2_1 := hP2_raw.1
  have hP2_2 := hP2_raw.2
  have h_denom_le : (1 + a1^2) * (1 + a2^2) ≤ (1 + M^2)^2 := by
    have h1 : a1^2 ≤ M^2 := by nlinarith [abs_le.mp h1_slope]
    have h2 : a2^2 ≤ M^2 := by nlinarith [abs_le.mp h2_slope]
    have h_exp : (1 + a1^2) * (1 + a2^2) = 1 + a1^2 + a2^2 + a1^2 * a2^2 := by ring
    rw [h_exp]
    have h5 : 1 + a1^2 + a2^2 + a1^2 * a2^2 ≤ (1 + M^2)^2 := by
      have h6 : (1 + M^2)^2 = 1 + M^2 + M^2 + M^2 * M^2 := by ring
      rw [h6]
      gcongr <;> nlinarith
    exact h5
  have h_denom_pos : 0 < (1 + a1^2) * (1 + a2^2) := by positivity
  have h_norm2 : ‖(P1 - P2) e2‖ ^ 2 =
      (a1 - a2)^2 / ((1 + a1^2) * (1 + a2^2)) := by
    have h_sub : (P1 - P2) e2 = P1 e2 - P2 e2 := by rfl
    have h_image0 : ((P1 - P2) e2) 0 = a1 / (1 + a1^2) - a2 / (1 + a2^2) := by
      rw [h_sub]
      have h : (P1 e2 - P2 e2) 0 = (P1 e2) 0 - (P2 e2) 0 := by simp
      rw [h, hP1_1, hP2_1] <;> rfl
    have h_image1 : ((P1 - P2) e2) 1 = 1 / (1 + a1^2) - 1 / (1 + a2^2) := by
      rw [h_sub]
      have h : (P1 e2 - P2 e2) 1 = (P1 e2) 1 - (P2 e2) 1 := by simp
      rw [h, hP1_2, hP2_2] <;> rfl
    rw [EuclideanSpace.real_norm_sq_eq ((P1 - P2) e2), Fin.sum_univ_two, h_image0, h_image1]
    <;> exact semicircle_chord_algebraic a1 a2
  have h4 : ‖(P1 - P2) e2‖ ^ 2 ≥ (a1 - a2)^2 / (1 + M^2)^2 := by
    rw [h_norm2]
    have h_pos3 : 0 < (1 + M^2)^2 := by positivity
    have h_diff : 0 ≤ (1 + M^2)^2 - (1 + a1^2) * (1 + a2^2) := by linarith [h_denom_le]
    have h_formula : (a1 - a2)^2 / ((1 + a1^2) * (1 + a2^2)) - (a1 - a2)^2 / (1 + M^2)^2 =
        (a1 - a2)^2 * ((1 + M^2)^2 - (1 + a1^2) * (1 + a2^2)) / (((1 + a1^2) * (1 + a2^2)) * (1 + M^2)^2) := by
      field_simp [h_denom_pos.ne'] <;> ring
    have h_nonneg : 0 ≤ (a1 - a2)^2 * ((1 + M^2)^2 - (1 + a1^2) * (1 + a2^2)) / (((1 + a1^2) * (1 + a2^2)) * (1 + M^2)^2) := by
      apply div_nonneg
      · exact mul_nonneg (by positivity) h_diff
      · positivity
    linarith [h_formula, h_nonneg]
  have h6 : ‖(P1 - P2) e2‖ ≥ |a1 - a2| / (1 + M^2) := by
    have h7 : 0 ≤ ‖(P1 - P2) e2‖ := by positivity
    have h8 : 0 ≤ |a1 - a2| / (1 + M^2) := by positivity
    have h9 : (‖(P1 - P2) e2‖)^2 ≥ (|a1 - a2| / (1 + M^2))^2 := by
      calc (‖(P1 - P2) e2‖)^2
        = ‖(P1 - P2) e2‖ ^ 2 := by ring
      _ ≥ (a1 - a2)^2 / (1 + M^2)^2 := h4
      _ = (|a1 - a2| / (1 + M^2))^2 := by
        have h10 : (a1 - a2)^2 = (|a1 - a2|)^2 := by rw [sq_abs]
        rw [h10] <;> field_simp <;> ring
    nlinarith [sq_nonneg (‖(P1 - P2) e2‖ - (|a1 - a2| / (1 + M^2)))]
  have h9 : ‖(P1 - P2) e2‖ ≤ ‖P1 - P2‖ := by
    have h10 : ‖(P1 - P2) e2‖ ≤ ‖P1 - P2‖ * ‖e2‖ := ContinuousLinearMap.le_opNorm (P1 - P2) e2
    rw [e2_norm] at h10 <;> linarith
  have h10 : ‖P1 - P2‖ ≤ AffineLine.dist ℓ1 ℓ2 := by
    have h11 : AffineLine.dist ℓ1 ℓ2 = ‖P1 - P2‖ + ‖ℓ1.offset - ℓ2.offset‖ := by rfl
    rw [h11]
    exact le_add_of_nonneg_right (by positivity)
  have h_pos : 0 < 1 + M^2 := by nlinarith
  have h_first : |a1 - a2| ≤ (1 + M^2) * ‖(P1 - P2) e2‖ := by
    have h_div : |a1 - a2| / (1 + M^2) ≤ ‖(P1 - P2) e2‖ := h6
    calc |a1 - a2|
      = (1 + M^2) * (|a1 - a2| / (1 + M^2)) := by field_simp [h_pos.ne'] <;> ring
    _ ≤ (1 + M^2) * ‖(P1 - P2) e2‖ := by gcongr
  calc |a1 - a2|
    ≤ (1 + M^2) * ‖(P1 - P2) e2‖ := h_first
  _ ≤ (1 + M^2) * ‖P1 - P2‖ := by gcongr
  _ ≤ (1 + M^2) * AffineLine.dist ℓ1 ℓ2 := by gcongr

/-- By definition, b = offset 0 - a * offset 1. -/
lemma affineLineParams_b_formula (ℓ : AffineLine) (hv1 : (getDirV ℓ) 1 ≠ 0) :
    (affineLineParams ℓ).2 = ℓ.offset 0 - (affineLineParams ℓ).1 * ℓ.offset 1 := by
  have hif : (if (getDirV ℓ) 1 = 0 then (0 : ℝ) else (getDirV ℓ) 0 / (getDirV ℓ) 1)
      = (getDirV ℓ) 0 / (getDirV ℓ) 1 := by
    rw [if_neg hv1]
  have h1 : (affineLineParams ℓ).1 = (getDirV ℓ) 0 / (getDirV ℓ) 1 := by
    change (affineLineParams ℓ).1 = _
    simp [affineLineParams, hif]
    <;> rfl
  have h2 : (affineLineParams ℓ).2 =
      ℓ.offset 0 - ((getDirV ℓ) 0 / (getDirV ℓ) 1) * ℓ.offset 1 := by
    change (affineLineParams ℓ).2 = _
    simp [affineLineParams, hif]
    <;> rfl
  rw [h2, h1] <;> ring

/-- Offset norm bound: ‖offset‖ ≤ |b| (since ‖offset‖ = |b|/sqrt(1+a²) ≤ |b|). -/
lemma offset_norm_le_intercept (ℓ : AffineLine) (hv1 : (getDirV ℓ) 1 ≠ 0) :
    ‖ℓ.offset‖ ≤ |(affineLineParams ℓ).2| := by
  set a := (affineLineParams ℓ).1 with ha_def
  set b := (affineLineParams ℓ).2 with hb_def
  have h_off := offset_formula ℓ hv1
  have h_norm2 : ‖ℓ.offset‖ ^ 2 = b^2 / (1 + a^2) := by
    have h_off1 : ℓ.offset 0 = b / (1 + a^2) := h_off.1
    have h_off2 : ℓ.offset 1 = -a * b / (1 + a^2) := h_off.2
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, h_off1, h_off2]
    field_simp
    <;> ring
  have h_pos : 0 < 1 + a^2 := by positivity
  have h9 : b^2 / (1 + a^2) ≤ b^2 := by
    apply div_le_self
    · positivity
    · nlinarith
  have h10 : ‖ℓ.offset‖ ^ 2 ≤ b^2 := by
    rw [h_norm2] <;> exact h9
  have h11 : 0 ≤ ‖ℓ.offset‖ := by positivity
  have h12 : 0 ≤ |b| := by positivity
  nlinarith [sq_abs b]

/-- Quantitative separation of distinct snapped tubes: dist ≥ Δ/360.

    Uses grid spacing Δ/20, generalized slope Lipschitz (constant 5),
    and intercept Lipschitz (constant 18) for |a|≤2, ‖offset‖≤3. -/
lemma iSnap_grid_separation {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_le_one : Δ ≤ 1)
    {ℓ1 ℓ2 : AffineLine}
    (h_slope1 : |(affineLineParams ℓ1).1| ≤ 1)
    (h_intercept1 : |(affineLineParams ℓ1).2| ≤ 2)
    (h_v1 : (getDirV ℓ1) 1 ≠ 0)
    (h_slope2 : |(affineLineParams ℓ2).1| ≤ 1)
    (h_intercept2 : |(affineLineParams ℓ2).2| ≤ 2)
    (h_v2 : (getDirV ℓ2) 1 ≠ 0)
    (h_ne : iSnap Δ ℓ1 ≠ iSnap Δ ℓ2) :
    Δ / 360 ≤ AffineLine.dist (iSnap Δ ℓ1) (iSnap Δ ℓ2) := by
  set ℓ1' := iSnap Δ ℓ1 with hℓ1'_def
  set ℓ2' := iSnap Δ ℓ2 with hℓ2'_def
  set a1 := (affineLineParams ℓ1').1 with ha1_def
  set b1 := (affineLineParams ℓ1').2 with hb1_def
  set a2 := (affineLineParams ℓ2').1 with ha2_def
  set b2 := (affineLineParams ℓ2').2 with hb2_def
  set d := AffineLine.dist ℓ1' ℓ2' with hd_def
  let ε := injectSnapScale Δ
  have hε_eq : ε = Δ / 20 := by rfl
  have h_a1_bound : |a1| ≤ 2 := iSnap_slope_bound hΔ_pos hΔ_le_one h_slope1
  have h_a2_bound : |a2| ≤ 2 := iSnap_slope_bound hΔ_pos hΔ_le_one h_slope2
  have h_b1_bound : |b1| ≤ 3 := iSnap_intercept_bound hΔ_pos hΔ_le_one h_intercept1
  have h_b2_bound : |b2| ≤ 3 := iSnap_intercept_bound hΔ_pos hΔ_le_one h_intercept2
  have h_v1' : (getDirV ℓ1') 1 ≠ 0 := iSnap_v1
  have h_v2' : (getDirV ℓ2') 1 ≠ 0 := iSnap_v1
  have h_off1_norm : ‖ℓ1'.offset‖ ≤ 3 := by
    have h : ‖ℓ1'.offset‖ ≤ |b1| := offset_norm_le_intercept ℓ1' h_v1'
    linarith [h_b1_bound]
  have h_off2_norm : ‖ℓ2'.offset‖ ≤ 3 := by
    have h : ‖ℓ2'.offset‖ ≤ |b2| := offset_norm_le_intercept ℓ2' h_v2'
    linarith [h_b2_bound]
  have h_params1 : affineLineParams ℓ1' = (gridSnap1D ε (affineLineParams ℓ1).1, gridSnap1D ε (affineLineParams ℓ1).2) :=
    affineLineSnap_params ε ℓ1
  have h_params2 : affineLineParams ℓ2' = (gridSnap1D ε (affineLineParams ℓ2).1, gridSnap1D ε (affineLineParams ℓ2).2) :=
    affineLineSnap_params ε ℓ2
  have h_a1_eq : a1 = gridSnap1D ε (affineLineParams ℓ1).1 := by
    simp [ha1_def, h_params1]
  have h_b1_eq : b1 = gridSnap1D ε (affineLineParams ℓ1).2 := by
    simp [hb1_def, h_params1]
  have h_a2_eq : a2 = gridSnap1D ε (affineLineParams ℓ2).1 := by
    simp [ha2_def, h_params2]
  have h_b2_eq : b2 = gridSnap1D ε (affineLineParams ℓ2).2 := by
    simp [hb2_def, h_params2]
  have hε_pos : 0 < ε := by dsimp only [ε]; exact div_pos hΔ_pos (by norm_num)
  have h_params_ne : (a1, b1) ≠ (a2, b2) := by
    intro h
    have h' : a1 = a2 ∧ b1 = b2 := Prod.ext_iff.mp h
    have h_eq : affineLineParams ℓ1' = affineLineParams ℓ2' := by
      have h11 : (affineLineParams ℓ1') = (a1, b1) := by
        simp [ha1_def, hb1_def]
      have h12 : (affineLineParams ℓ2') = (a2, b2) := by
        simp [ha2_def, hb2_def]
      rw [h11, h12]
      exact Prod.ext h'.1 h'.2
    have h_line_eq : ℓ1' = ℓ2' := affineLineParams_injective h_v1' h_v2' h_eq
    exact h_ne h_line_eq
  have h_grid : max |a1 - a2| |b1 - b2| ≥ ε := by
    by_contra h
    have h' : max |a1 - a2| |b1 - b2| < ε := by linarith
    have h_da : |a1 - a2| < ε := by
      calc |a1 - a2| ≤ max |a1 - a2| |b1 - b2| := le_max_left _ _
      _ < ε := h'
    have h_db : |b1 - b2| < ε := by
      calc |b1 - b2| ≤ max |a1 - a2| |b1 - b2| := le_max_right _ _
      _ < ε := h'
    have h_a_eq : a1 = a2 := by
      by_contra h_neq
      have h_neq' : gridSnap1D ε (affineLineParams ℓ1).1 ≠ gridSnap1D ε (affineLineParams ℓ2).1 := by
        rw [←h_a1_eq, ←h_a2_eq]
        exact h_neq
      have h_sep : ε ≤ |a1 - a2| := by
        rw [h_a1_eq, h_a2_eq]
        exact gridSnap1D_separation hε_pos h_neq'
      linarith
    have h_b_eq : b1 = b2 := by
      by_contra h_neq
      have h_neq' : gridSnap1D ε (affineLineParams ℓ1).2 ≠ gridSnap1D ε (affineLineParams ℓ2).2 := by
        rw [←h_b1_eq, ←h_b2_eq]
        exact h_neq
      have h_sep : ε ≤ |b1 - b2| := by
        rw [h_b1_eq, h_b2_eq]
        exact gridSnap1D_separation hε_pos h_neq'
      linarith
    have h_eq : (a1, b1) = (a2, b2) := Prod.ext h_a_eq h_b_eq
    exact h_params_ne h_eq
  have h_slope_lb : |a1 - a2| ≤ 5 * d := by
    have h := slope_lipschitz_general (by norm_num) ℓ1' ℓ2' h_v1' h_v2' h_a1_bound h_a2_bound
    have h' : |(affineLineParams ℓ1').1 - (affineLineParams ℓ2').1| = |a1 - a2| := by
      simp [ha1_def, ha2_def]
    have h'' : (1 + (2 : ℝ)^2) * AffineLine.dist ℓ1' ℓ2' = 5 * d := by
      simp [hd_def] <;> norm_num
    rw [h', h''] at h
    exact h
  have h_b_formula1 : b1 = ℓ1'.offset 0 - a1 * ℓ1'.offset 1 := by
    have h := affineLineParams_b_formula ℓ1' h_v1'
    simpa [ha1_def, hb1_def] using h
  have h_b_formula2 : b2 = ℓ2'.offset 0 - a2 * ℓ2'.offset 1 := by
    have h := affineLineParams_b_formula ℓ2' h_v2'
    simpa [ha2_def, hb2_def] using h
  have h_intercept_lb : |b1 - b2| ≤ 18 * d := by
    set doff := ℓ1'.offset - ℓ2'.offset with hdoff_def
    have h_db : b1 - b2 = doff 0 - a1 * doff 1 - (a1 - a2) * ℓ2'.offset 1 := by
      simp [h_b_formula1, h_b_formula2, hdoff_def] <;> ring
    rw [h_db]
    have h_eq : doff 0 - a1 * doff 1 - (a1 - a2) * ℓ2'.offset 1 =
        doff 0 + (-a1 * doff 1) + (-(a1 - a2) * ℓ2'.offset 1) := by ring
    rw [h_eq]
    have h1 : |doff 0 + (-a1 * doff 1) + (-(a1 - a2) * ℓ2'.offset 1)| ≤
        |doff 0| + |a1| * |doff 1| + |a1 - a2| * |ℓ2'.offset 1| := by
      have h_tri1 : |doff 0 + (-a1 * doff 1) + (-(a1 - a2) * ℓ2'.offset 1)| ≤
          |doff 0 + (-a1 * doff 1)| + |-(a1 - a2) * ℓ2'.offset 1| := by
        exact abs_add_le (doff.ofLp 0 + -a1 * doff.ofLp 1) (-(a1 - a2) * ℓ2'.offset.ofLp 1)
      have h_tri2 : |doff 0 + (-a1 * doff 1)| ≤ |doff 0| + |-a1 * doff 1| := by exact abs_add_le (doff.ofLp 0) (-a1 * doff.ofLp 1)
      have h_abs1 : |-a1 * doff 1| = |a1| * |doff 1| := by
        calc |-a1 * doff 1|
          = |(-a1) * doff 1| := by rfl
        _ = |(-a1)| * |doff 1| := by rw [abs_mul]
        _ = |a1| * |doff 1| := by simp
      have h_abs2 : |-(a1 - a2) * ℓ2'.offset 1| = |a1 - a2| * |ℓ2'.offset 1| := by
        calc |-(a1 - a2) * ℓ2'.offset 1|
          = |(-(a1 - a2)) * ℓ2'.offset 1| := by rfl
        _ = |(-(a1 - a2))| * |ℓ2'.offset 1| := by rw [abs_mul]
        _ = |a1 - a2| * |ℓ2'.offset 1| := by
          have h_neg : |(-(a1 - a2))| = |a1 - a2| := abs_neg (a1 - a2)
          rw [h_neg]
      linarith
    have h2 : |doff 0| ≤ ‖doff‖ := coord_abs_le_norm doff 0
    have h3 : |doff 1| ≤ ‖doff‖ := coord_abs_le_norm doff 1
    have h4 : |ℓ2'.offset 1| ≤ ‖ℓ2'.offset‖ := coord_abs_le_norm ℓ2'.offset 1
    have h5 : ‖doff‖ ≤ d := by
      have h6 : d = ‖ℓ1'.1.direction.starProjection - ℓ2'.1.direction.starProjection‖ + ‖doff‖ := by rfl
      linarith [norm_nonneg (ℓ1'.1.direction.starProjection - ℓ2'.1.direction.starProjection)]
    calc |doff 0 + (-a1 * doff 1) + (-(a1 - a2) * ℓ2'.offset 1)|
      ≤ |doff 0| + |a1| * |doff 1| + |a1 - a2| * |ℓ2'.offset 1| := h1
    _ ≤ ‖doff‖ + 2 * ‖doff‖ + |a1 - a2| * 3 := by
      gcongr <;> linarith [h_a1_bound, h2, h3, h4, h_off2_norm]
    _ ≤ 3 * d + 5 * d * 3 := by gcongr <;> linarith [h_slope_lb, h5]
    _ = 18 * d := by ring
  have h_main : d ≥ Δ / 360 := by
    cases' le_max_iff.mp h_grid with h_da h_db
    · -- |a1 - a2| ≥ ε
      have h : ε ≤ |a1 - a2| := h_da
      rw [hε_eq] at h
      linarith [h_slope_lb]
    · -- |b1 - b2| ≥ ε
      have h : ε ≤ |b1 - b2| := h_db
      rw [hε_eq] at h
      linarith [h_intercept_lb]
  exact h_main

end DirecretisedFurstenbergEstimate.SnapTransfer
