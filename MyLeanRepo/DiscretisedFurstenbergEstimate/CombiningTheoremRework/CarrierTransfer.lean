module

/-
  Carrier transfer: thin (AffineLine identity) → wide (DyadicTube canonicalWideCarrier).

  Contains:
  1. Geometric lemmas: canonicalWideCarrier ⊆ cthickening, wide incidence → thin incidence
  2. Full transfer lemma (takes pending sub-results as explicit hypotheses)

  Operator correction (2026-08-10): Use Kcarrier = 9 consistently.
  Flow:
    1. Wide incidence at δ → center-line incidence at 4δ → 9δ
    2. Transfer point sqrt-regularity and tube S-sets from δ to 9δ
    3. Apply thin regular theorem at 9δ
    4. Ncover(9δ, center-line image) ≤ Ncover(δ, dyadic family)
    5. Absorb 9 into exponent: (9δ)^{-(2s+εA)} ≥ δ^{-(2s+ε_inc)}

  Status:
    - h_ncover_transfer: DISCHARGED (cobalt's WideCenterLine.ncover_image_le_of_incidence)
    - h_sset_scale: DISCHARGED (kestrel's Euclidean doubling 361 + indigo's sset_scale_up)
    - h_tube_sset_transfer: DISCHARGED (tube_sset_transfer_set → indigo's wide_tubeSSet_transfer_9δ)
      Requires δ ≤ (√2-1)/4 for intercept bound ≤3, and C_tube = 381790 * 176^s
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicToAffineAdapters
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge_SSetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformIncidenceData
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.WideCenterLine
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.TubeSSetAdapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DoublingProperty
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.CarrierTransfer

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.InductionOnScales
open DiscretisedFurstenbergEstimate.CombiningTheoremRework
open DyadicCardToNcover
open DirecretisedFurstenbergEstimate.RegularIncidence

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The translation vector used by canonicalWideCarrier. -/
def wideShiftV : Plane :=
  WithLp.toLp (2 : ENNReal) fun _ : Fin 2 => -1 / 2

/-- Map a DyadicTube to the affine line at the center of canonicalWideCarrier.
    Center line has slope = T.slope, intercept = T.intercept + T.slope/2 - 1/2. -/
noncomputable def wideToAffineLine {j : ℕ} (T : DyadicTube j) : AffineLine :=
  lineOfSlopeIntercept T.slope (T.slope / 2 + T.intercept - 1 / 2)

/-- A point (x, m*x + b) lies on lineOfSlopeIntercept m b. -/
lemma point_on_lineOfSlopeIntercept (m b x : ℝ) :
    TubesAndSlopes.mkPlane x (m * x + b) ∈ (lineOfSlopeIntercept m b).1 := by
  have h : TubesAndSlopes.mkPlane x (m * x + b) - TubesAndSlopes.mkPlane 0 b ∈
      Submodule.span ℝ {tubeDirV m} := by
    have h2 : TubesAndSlopes.mkPlane x (m * x + b) - TubesAndSlopes.mkPlane 0 b =
        x • tubeDirV m := by
      ext i; fin_cases i <;> simp [TubesAndSlopes.mkPlane_apply0,
        TubesAndSlopes.mkPlane_apply1, tubeDirV, smul_eq_mul] <;> ring
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  simpa [lineOfSlopeIntercept, AffineSubspace.mem_mk'] using h

/-- The canonical wide carrier is contained in a 3*δ_j-thickening of the
    corresponding affine line. -/
lemma canonicalWideCarrier_subset_cthickening {j : ℕ} (T : DyadicTube j) :
    canonicalWideCarrier j T ⊆
      Metric.cthickening (3 * dyadicDelta j) (wideToAffineLine T).1 := by
  set δ := dyadicDelta j with hδ
  set m := T.slope with hm
  set b := T.intercept with hb
  set b' := m / 2 + b - 1 / 2 with hb'
  set v := wideShiftV with hv

  intro q hq
  rcases hq with ⟨p, hp_strip, hq_eq⟩
  have hq_eq2 : q = p + v := hq_eq.symm
  have h_strip : |p 1 - m * p 0 - b| ≤ 3 * δ := hp_strip

  have hq0 : q 0 = p 0 - 1 / 2 := by
    rw [hq_eq2]
    have h : (p + v) 0 = p 0 + v 0 := by rfl
    rw [h]
    have hv0 : v 0 = -1 / 2 := by simp [v, wideShiftV] <;> norm_num
    rw [hv0] <;> ring
  have hq1 : q 1 = p 1 - 1 / 2 := by
    rw [hq_eq2]
    have h : (p + v) 1 = p 1 + v 1 := by rfl
    rw [h]
    have hv1 : v 1 = -1 / 2 := by simp [v, wideShiftV] <;> norm_num
    rw [hv1] <;> ring

  have h_residual : q 1 - m * q 0 - b' = p 1 - m * p 0 - b := by
    rw [hq0, hq1, hb'] <;> ring
  have h_abs : |q 1 - m * q 0 - b'| ≤ 3 * δ := by
    rw [h_residual] <;> exact h_strip

  let r : Plane := TubesAndSlopes.mkPlane (q 0) (m * q 0 + b')
  have hr0 : r 0 = q 0 := by simp [r, TubesAndSlopes.mkPlane_apply0]
  have hr1 : r 1 = m * q 0 + b' := by simp [r, TubesAndSlopes.mkPlane_apply1]

  have hr_on_line : r ∈ (wideToAffineLine T).1 := by
    exact point_on_lineOfSlopeIntercept m b' (q 0)

  have hdist_le : dist q r ≤ 3 * δ := by
    have h_same_x : q 0 = r 0 := hr0.symm
    have h : dist q r = |q 1 - r 1| := by
      have h_norm : ‖q - r‖ = Real.sqrt (((q - r) 0)^2 + ((q - r) 1)^2) := by
        simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring_nf
      rw [dist_eq_norm, h_norm]
      have h0 : (q - r) 0 = 0 := by simp [h_same_x]
      have h5 : Real.sqrt (((q - r) 0)^2 + ((q - r) 1)^2) = Real.sqrt (((q - r) 1)^2) := by
        rw [h0] <;> ring_nf
      rw [h5]
      have h4 : Real.sqrt (((q - r) 1)^2) = |(q - r) 1| := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h4] <;> rfl
    rw [h]
    have h7 : q 1 - r 1 = q 1 - m * q 0 - b' := by
      rw [hr1] <;> ring
    rw [h7]
    exact h_abs

  have h_edist : edist q r ≤ ENNReal.ofReal (3 * δ) := by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal hdist_le
  have h_inf : Metric.infEDist q ((wideToAffineLine T).1) ≤ ENNReal.ofReal (3 * δ) := by
    have h : Metric.infEDist q ((wideToAffineLine T).1) ≤ edist q r :=
      Metric.infEDist_le_edist_of_mem hr_on_line
    exact le_trans h h_edist
  exact Metric.mem_cthickening_iff.mpr h_inf

/-- Wide incidence at scale δ implies thin incidence at scale δ + 3*δ_j.
    Since δ = δ_j in the exact-scale application, this gives 4δ. -/
lemma wide_incidence_to_thin {j : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (T : DyadicTube j) (p : Plane)
    (h : p ∈ Metric.cthickening δ (canonicalWideCarrier j T)) :
    p ∈ Metric.cthickening (δ + 3 * dyadicDelta j) (wideToAffineLine T).1 := by
  let L : Set Plane := (wideToAffineLine T).1
  have hδj_pos : 0 < dyadicDelta j := dyadicDelta_pos j
  have h1 : canonicalWideCarrier j T ⊆ Metric.cthickening (3 * dyadicDelta j) L :=
    canonicalWideCarrier_subset_cthickening T
  have h_main : Metric.cthickening δ (canonicalWideCarrier j T) ⊆
      Metric.cthickening (δ + 3 * dyadicDelta j) L := by
    calc Metric.cthickening δ (canonicalWideCarrier j T)
      ⊆ Metric.cthickening δ (Metric.cthickening (3 * dyadicDelta j) L) :=
        Metric.cthickening_subset_of_subset δ h1
    _ ⊆ Metric.cthickening (δ + 3 * dyadicDelta j) L := by
      have hε : 0 ≤ δ := by linarith
      have h3δ : 0 ≤ (3 * dyadicDelta j) := by
        exact mul_nonneg (by norm_num) hδj_pos.le
      exact Metric.cthickening_cthickening_subset hε h3δ L
  exact h_main h

/-! ============================================================================
   S-set scale-up (from indigo) and point S-set scaling (kestrel + indigo)
   ============================================================================ -/

/-- Scale up an S-set from δ to Kδ using a doubling property.
    Copied from indigo's SSetScaleUp.lean. -/
lemma sset_scale_up {X : Type*} [PseudoMetricSpace X] {E : Set X} {δ s C K C_d : ℝ}
    (hK : 1 ≤ K) (hδ : 0 < δ) (hC_d_pos : 0 < C_d)
    (hE_bdd : Bornology.IsBounded E)
    (h_doubling : ∀ (F : Set X), Bornology.IsBounded F →
      Ncover δ F ≤ ENNReal.ofReal C_d * Ncover (K * δ) F)
    (h : IsDeltaSSet δ s C E) :
    IsDeltaSSet (K * δ) s (C * C_d) E := by
  have hKδ_pos : 0 < K * δ := by positivity
  have hδ_le_Kδ : δ ≤ K * δ := by
    calc δ = 1 * δ := by ring
      _ ≤ K * δ := by gcongr
  rcases h with ⟨hE_nonempty, hδ_pos', hC_pos, hs, hcover⟩
  refine' ⟨hE_nonempty, hKδ_pos, mul_pos hC_pos hC_d_pos, hs, _⟩
  intro x r hr
  have hδ_le_r : δ ≤ r := le_trans hδ_le_Kδ hr
  have h1 : Ncover (K * δ) (E ∩ Metric.closedBall x r) ≤
      Ncover δ (E ∩ Metric.closedBall x r) := by
    have h' : δ.toNNReal ≤ (K * δ).toNNReal := by exact Real.toNNReal_mono hδ_le_Kδ
    simpa [Ncover] using Metric.externalCoveringNumber_anti (A := E ∩ Metric.closedBall x r) h'
  have h2 : Ncover δ (E ∩ Metric.closedBall x r) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Ncover δ E :=
    hcover x r hδ_le_r
  have h3 : Ncover δ E ≤ ENNReal.ofReal C_d * Ncover (K * δ) E :=
    h_doubling E hE_bdd
  have h_main : Ncover (K * δ) (E ∩ Metric.closedBall x r) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal C_d * Ncover (K * δ) E) := by
    calc Ncover (K * δ) (E ∩ Metric.closedBall x r)
      ≤ Ncover δ (E ∩ Metric.closedBall x r) := h1
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Ncover δ E := h2
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal C_d * Ncover (K * δ) E) := by gcongr
  have h_final : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal C_d * Ncover (K * δ) E) =
      ENNReal.ofReal (C * C_d) * (ENNReal.ofReal r) ^ s * Ncover (K * δ) E := by
    have h4 : ENNReal.ofReal C * ENNReal.ofReal C_d = ENNReal.ofReal (C * C_d) := by
      rw [← ENNReal.ofReal_mul] <;> linarith
    calc ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal C_d * Ncover (K * δ) E)
      = (ENNReal.ofReal C * ENNReal.ofReal C_d) * (ENNReal.ofReal r) ^ s * Ncover (K * δ) E := by ring
    _ = ENNReal.ofReal (C * C_d) * (ENNReal.ofReal r) ^ s * Ncover (K * δ) E := by rw [h4] <;> ring
  rw [h_final] at h_main
  exact h_main

/-- Point S-set scaling from δ to 9δ using kestrel's Euclidean doubling (C_d=361)
    and indigo's sset_scale_up. -/
lemma point_sset_scale {P : Set Plane} {δ u C : ℝ} (hδ : 0 < δ)
    (hP_bdd : Bornology.IsBounded P)
    (h : IsDeltaSSet δ u C P) :
    IsDeltaSSet (9 * δ) u (C * 361) P := by
  have h_doubling' : ∀ (F : Set Plane), Bornology.IsBounded F →
      Ncover δ F ≤ ENNReal.ofReal (361 : ℝ) * Ncover (9 * δ) F := by
    intro F _
    have h_kestrel := CoveringUtils.euclidean_plane_doubling δ hδ F
    simpa [Ncover] using h_kestrel
  exact sset_scale_up (hK := by norm_num) hδ (hC_d_pos := by norm_num) hP_bdd h_doubling' h

/-! ============================================================================
   Tube S-set transfer: DyadicTube δ → wideToAffineLine image at 9δ

   Uses co-Lipschitz bound (constant 88) and packing bound at 18δ.
   ============================================================================ -/

/-- Co-Lipschitz bound for wideToAffineLine: paramDistLinf ≤ 88 * dist.

    Relates wide dist to orig dist (dist(orig) ≤ 4 * dist(wide)), then
    uses toAffineLine_co_lipschitz (constant 22): 22 * 4 = 88. -/
lemma wideToAffineLine_co_lipschitz {n : ℕ} (T1 T2 : DyadicTube n)
    (hm1 : |T1.slope| ≤ 1) (hm2 : |T2.slope| ≤ 1)
    (hb2 : |T2.intercept| ≤ 3) :
    InductionOnScales.tubeParamDistLinf T1 T2 ≤ 88 * dist (wideToAffineLine T1) (wideToAffineLine T2) := by
  set m1 := T1.slope with hm1_def
  set m2 := T2.slope with hm2_def
  set b1 := T1.intercept with hb1_def
  set b2 := T2.intercept with hb2_def
  set b1' := m1 / 2 + b1 - 1 / 2 with hb1'_def
  set b2' := m2 / 2 + b2 - 1 / 2 with hb2'_def
  set ℓ1 := wideToAffineLine T1 with hℓ1
  set ℓ2 := wideToAffineLine T2 with hℓ2
  set o1 := toAffineLine T1 with ho1
  set o2 := toAffineLine T2 with ho2

  have h_dir_same : ℓ1.1.direction.starProjection = o1.1.direction.starProjection := by
    have h1 : ℓ1.1.direction = Submodule.span ℝ {tubeDirV m1} := by
      rw [hℓ1, wideToAffineLine]; exact lineOfSlopeIntercept_direction m1 b1'
    have h2 : o1.1.direction = Submodule.span ℝ {tubeDirV m1} := by
      rw [ho1]; exact lineOfSlopeIntercept_direction m1 b1
    rw [h1, h2]
  have h_dir_same2 : ℓ2.1.direction.starProjection = o2.1.direction.starProjection := by
    have h1 : ℓ2.1.direction = Submodule.span ℝ {tubeDirV m2} := by
      rw [hℓ2, wideToAffineLine]; exact lineOfSlopeIntercept_direction m2 b2'
    have h2 : o2.1.direction = Submodule.span ℝ {tubeDirV m2} := by
      rw [ho2]; exact lineOfSlopeIntercept_direction m2 b2
    rw [h1, h2]

  have h_proj_lower : ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ ≥ |m1 - m2| / 2 := by
    have h_dir_eq1 : ℓ1.1.direction = Submodule.span ℝ {tubeDirV m1} := by
      rw [hℓ1, wideToAffineLine]; exact lineOfSlopeIntercept_direction m1 b1'
    have h_dir_eq2 : ℓ2.1.direction = Submodule.span ℝ {tubeDirV m2} := by
      rw [hℓ2, wideToAffineLine]; exact lineOfSlopeIntercept_direction m2 b2'
    rw [h_dir_eq1, h_dir_eq2]
    exact proj_lower_bound_simple m1 m2 hm1 hm2

  have h_off1_wide : ℓ1.offset = b1' • offsetVec m1 := by
    rw [hℓ1, wideToAffineLine]; exact offset_formula m1 b1'
  have h_off2_wide : ℓ2.offset = b2' • offsetVec m2 := by
    rw [hℓ2, wideToAffineLine]; exact offset_formula m2 b2'
  have h_off1_orig : o1.offset = b1 • offsetVec m1 := by
    rw [ho1]; exact offset_formula m1 b1
  have h_off2_orig : o2.offset = b2 • offsetVec m2 := by
    rw [ho2]; exact offset_formula m2 b2

  have h_db' : b1' - b2' = (b1 - b2) + (m1 - m2) / 2 := by
    simp [hb1'_def, hb2'_def] <;> ring
  have h_b2'_diff : b2' - b2 = m2 / 2 - 1 / 2 := by
    simp [hb2'_def] <;> ring
  have h_b2'_diff_bound : |b2' - b2| ≤ 1 := by
    rw [h_b2'_diff]
    have h : |m2 / 2 - 1 / 2| ≤ |m2| / 2 + 1 / 2 := by
      have h2 : |m2 / 2 - 1 / 2| ≤ |m2 / 2| + 1 / 2 := by
        have h3 : |m2 / 2 - 1 / 2| = |m2 / 2 + (-1 / 2 : ℝ)| := by ring_nf
        rw [h3]
        have h4 := abs_add_le (m2 / 2) (-1 / 2 : ℝ)
        have h5 : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num
        rw [h5] at h4; exact h4
      have h6 : |m2 / 2| = |m2| / 2 := by rw [abs_div, abs_of_pos (show (0:ℝ)<2 by norm_num)]
      rw [h6] at h2; exact h2
    linarith [hm2]

  let proj := ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection
  let wide_off := ℓ1.offset - ℓ2.offset
  let orig_off := o1.offset - o2.offset
  let extra := ((m1 - m2) / 2) • offsetVec m1 + (b2' - b2) • (offsetVec m1 - offsetVec m2)

  have h_extra_bound : ‖extra‖ ≤ (3 / 2 : ℝ) * |m1 - m2| := by
    have h1 : ‖extra‖ ≤ |m1 - m2| / 2 * ‖offsetVec m1‖ + |b2' - b2| * ‖offsetVec m1 - offsetVec m2‖ := by
      calc
        _ ≤ ‖((m1 - m2) / 2) • offsetVec m1‖ + ‖(b2' - b2) • (offsetVec m1 - offsetVec m2)‖ := norm_add_le _ _
        _ = |m1 - m2| / 2 * ‖offsetVec m1‖ + |b2' - b2| * ‖offsetVec m1 - offsetVec m2‖ := by
          simp [norm_smul, mul_comm, mul_left_comm] <;> ring
    have h2 : ‖offsetVec m1‖ ≤ 1 := by
      rw [offsetVec_norm m1]
      have h21 : 0 < Real.sqrt (1 + m1^2) := by positivity
      have h22 : (1 : ℝ) ≤ Real.sqrt (1 + m1^2) := by
        have h23 : (1 : ℝ) ≤ 1 + m1^2 := by nlinarith
        have h24 : Real.sqrt 1 ≤ Real.sqrt (1 + m1^2) := Real.sqrt_le_sqrt h23
        have h25 : Real.sqrt 1 = (1 : ℝ) := by norm_num
        rw [h25] at h24; exact h24
      have h26 : 1 / Real.sqrt (1 + m1^2) ≤ 1 := by apply (div_le_one h21).mpr; exact h22
      exact h26
    have h3 : ‖offsetVec m1 - offsetVec m2‖ ≤ |m1 - m2| := offsetVec_lipschitz m1 m2
    have h4 : |b2' - b2| ≤ 1 := h_b2'_diff_bound
    calc
      _ ≤ |m1 - m2| / 2 * ‖offsetVec m1‖ + |b2' - b2| * ‖offsetVec m1 - offsetVec m2‖ := h1
      _ ≤ |m1 - m2| / 2 * 1 + 1 * |m1 - m2| := by gcongr <;> linarith
      _ = (3 / 2 : ℝ) * |m1 - m2| := by ring

  have h_off_relation : ‖orig_off‖ ≤ ‖wide_off‖ + 3 * ‖proj‖ := by
    have h1 : wide_off - orig_off = extra := by
      rw [show wide_off = ℓ1.offset - ℓ2.offset from rfl,
          show orig_off = o1.offset - o2.offset from rfl]
      rw [h_off1_wide, h_off2_wide, h_off1_orig, h_off2_orig]
      have h_b1'_diff : b1' - b1 = m1 / 2 - 1 / 2 := by simp [hb1'_def] <;> ring
      have h_b2'_diff : b2' - b2 = m2 / 2 - 1 / 2 := by simp [hb2'_def] <;> ring
      have h_eq1 : (b1' • offsetVec m1 - b2' • offsetVec m2) - (b1 • offsetVec m1 - b2 • offsetVec m2) =
          (b1' - b1) • offsetVec m1 - (b2' - b2) • offsetVec m2 := by
        have h_a : b1' • offsetVec m1 - b1 • offsetVec m1 = (b1' - b1) • offsetVec m1 := by
          rw [←sub_smul] <;> rfl
        have h_b : b2' • offsetVec m2 - b2 • offsetVec m2 = (b2' - b2) • offsetVec m2 := by
          rw [←sub_smul] <;> rfl
        have h : (b1' • offsetVec m1 - b2' • offsetVec m2) - (b1 • offsetVec m1 - b2 • offsetVec m2) =
            (b1' • offsetVec m1 - b1 • offsetVec m1) - (b2' • offsetVec m2 - b2 • offsetVec m2) := by abel
        rw [h, h_a, h_b]
      have h_eq2 : (b1' - b1) • offsetVec m1 - (b2' - b2) • offsetVec m2 =
          ((m1 - m2) / 2 + (b2' - b2)) • offsetVec m1 - (b2' - b2) • offsetVec m2 := by
        have h : b1' - b1 = (m1 - m2) / 2 + (b2' - b2) := by
          rw [h_b1'_diff, h_b2'_diff] <;> ring
        rw [h]
      have h_eq3 : ((m1 - m2) / 2 + (b2' - b2)) • offsetVec m1 - (b2' - b2) • offsetVec m2 =
          ((m1 - m2) / 2) • offsetVec m1 + (b2' - b2) • (offsetVec m1 - offsetVec m2) := by
        rw [add_smul, smul_sub] <;> abel
      rw [h_eq1, h_eq2, h_eq3]
      <;> rfl
    have h2 : orig_off = wide_off - extra := by rw [←h1] <;> abel
    have h3 : ‖wide_off - extra‖ ≤ ‖wide_off‖ + ‖extra‖ := norm_sub_le _ _
    have h4 : |m1 - m2| ≤ 2 * ‖proj‖ := by linarith [h_proj_lower]
    have h5 : ‖orig_off‖ ≤ ‖wide_off‖ + ‖extra‖ := by
      rw [h2]; exact h3
    have h6 : ‖extra‖ ≤ (3 / 2 : ℝ) * |m1 - m2| := h_extra_bound
    linarith

  have h_dist_orig_le : dist o1 o2 ≤ 4 * dist ℓ1 ℓ2 := by
    have h_proj_eq : ‖o1.1.direction.starProjection - o2.1.direction.starProjection‖ = ‖proj‖ := by
      have h_eq1 : o1.1.direction.starProjection = ℓ1.1.direction.starProjection := h_dir_same.symm
      have h_eq2 : o2.1.direction.starProjection = ℓ2.1.direction.starProjection := h_dir_same2.symm
      rw [h_eq1, h_eq2] <;> rfl
    have h1 : dist o1 o2 = ‖proj‖ + ‖orig_off‖ := by
      simp [dist, AffineLine.dist, h_proj_eq] <;> ring
    have h2 : dist ℓ1 ℓ2 = ‖proj‖ + ‖wide_off‖ := by
      simp [dist, AffineLine.dist] <;> ring
    rw [h1, h2]
    have hwnn : 0 ≤ ‖wide_off‖ := by positivity
    have h : ‖proj‖ + ‖orig_off‖ ≤ 4 * (‖proj‖ + ‖wide_off‖) := by
      linarith [h_off_relation]
    exact h

  have h_main : InductionOnScales.tubeParamDistLinf T1 T2 ≤ 22 * dist o1 o2 :=
    DyadicToAffineAdapters.toAffineLine_co_lipschitz T1 T2 hm1 hm2 hb2
  calc
    InductionOnScales.tubeParamDistLinf T1 T2 ≤ 22 * dist o1 o2 := h_main
    _ ≤ 22 * (4 * dist ℓ1 ℓ2) := by gcongr
    _ = 88 * dist ℓ1 ℓ2 := by ring

/-- Equality between the two line-of-slope-intercept constructors. -/
lemma lineOfSlopeIntercept_eq_mkSlopeIntercept (m b : ℝ) :
    lineOfSlopeIntercept m b = AffineLine.mkSlopeIntercept m b := by
  apply Subtype.ext
  have h_p_eq : TubesAndSlopes.mkPlane 0 b = WithLp.toLp (2 : ENNReal) ![0, b] := by
    ext i; fin_cases i <;> simp [TubesAndSlopes.mkPlane] <;> norm_num
  have h_v_eq : tubeDirV m = WithLp.toLp (2 : ENNReal) ![1, m] := by
    ext i; fin_cases i <;> simp [tubeDirV, TubesAndSlopes.mkPlane] <;> norm_num
  have h_pt : TubesAndSlopes.mkPlane 0 b ∈ (lineOfSlopeIntercept m b).1 := by
    have h := point_on_lineOfSlopeIntercept m b 0
    have h_eq : m * 0 + b = b := by ring
    simpa [h_eq] using h
  have h_pt2 : TubesAndSlopes.mkPlane 0 b ∈ (AffineLine.mkSlopeIntercept m b).1 := by
    rw [h_p_eq]
    simp [AffineLine.mkSlopeIntercept]
    <;> exact AffineSubspace.mk'_mem _ _
  have h_dir : (lineOfSlopeIntercept m b).1.direction =
      (AffineLine.mkSlopeIntercept m b).1.direction := by
    have h1 : (lineOfSlopeIntercept m b).1.direction = Submodule.span ℝ {tubeDirV m} :=
      lineOfSlopeIntercept_direction m b
    have h2 : (AffineLine.mkSlopeIntercept m b).1.direction =
        Submodule.span ℝ {WithLp.toLp (2 : ENNReal) ![1, m]} := by
      simp [AffineLine.mkSlopeIntercept]
      <;> rfl
    rw [h1, h2]
    congr
    <;> exact h_v_eq
  have h_eq : (lineOfSlopeIntercept m b).1 = (AffineLine.mkSlopeIntercept m b).1 :=
    (AffineSubspace.eq_iff_direction_eq_of_mem h_pt h_pt2).mpr h_dir
  exact h_eq

/-- wideToAffineLine preserves InStandardChart.inChart.

    If T is in the standard chart (|T.slope| ≤ 1), then wideToAffineLine T
    is also in the standard chart for AffineLine. -/
lemma wideToAffineLine_inChart {j : ℕ} (T : DyadicTube j)
    (h : InStandardChart.inChart T) :
    InStandardChart.inChart (wideToAffineLine T) := by
  have hm : |T.slope| ≤ 1 := by
    have h1 : -(2 : ℝ)^j ≤ (T.a : ℝ) ∧ (T.a : ℝ) ≤ (2 : ℝ)^j := h
    have h2 : |(T.a : ℝ)| ≤ (2 : ℝ)^j := by
      have h3 : -(2 : ℝ)^j ≤ (T.a : ℝ) := h1.1
      have h5 : (T.a : ℝ) ≤ (2 : ℝ)^j := h1.2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hδ_pos : 0 < dyadicDelta j := dyadicDelta_pos j
    have h6 : |T.slope| = dyadicDelta j * |(T.a : ℝ)| := by
      have h7 : T.slope = dyadicDelta j * (T.a : ℝ) := by
        simp [DyadicTube.slope] <;> ring
      rw [h7, abs_mul]
      rw [abs_of_pos hδ_pos]
      <;> ring
    rw [h6]
    have h7 : dyadicDelta j * |(T.a : ℝ)| ≤ dyadicDelta j * (2 : ℝ)^j :=
      mul_le_mul_of_nonneg_left h2 hδ_pos.le
    have h8 : dyadicDelta j * (2 : ℝ)^j = 1 := by
      simp [dyadicDelta] <;> field_simp <;> ring
    rw [h8] at h7
    exact h7
  refine' ⟨T.slope, T.slope / 2 + T.intercept - 1 / 2, hm, _⟩
  have h_eq : AffineLine.mkSlopeIntercept T.slope (T.slope / 2 + T.intercept - 1 / 2) =
      wideToAffineLine T := by
    exact (lineOfSlopeIntercept_eq_mkSlopeIntercept T.slope (T.slope / 2 + T.intercept - 1 / 2)).symm
  exact h_eq

/-- Derive |T.slope| ≤ 1 from InStandardChart.inChart for DyadicTube. -/
lemma slope_le_one_of_inChart {j : ℕ} {T : DyadicTube j}
    (h : InStandardChart.inChart T) : |T.slope| ≤ 1 := by
  have h1 : -(2 : ℝ)^j ≤ (T.a : ℝ) ∧ (T.a : ℝ) ≤ (2 : ℝ)^j := h
  have h2 : |(T.a : ℝ)| ≤ (2 : ℝ)^j := by
    have h3 : -(2 : ℝ)^j ≤ (T.a : ℝ) := h1.1
    have h5 : (T.a : ℝ) ≤ (2 : ℝ)^j := h1.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hδ_pos : 0 < dyadicDelta j := dyadicDelta_pos j
  have h6 : |T.slope| = dyadicDelta j * |(T.a : ℝ)| := by
    have h7 : T.slope = dyadicDelta j * (T.a : ℝ) := by
      simp [DyadicTube.slope] <;> ring
    rw [h7, abs_mul, abs_of_pos hδ_pos] <;> ring
  rw [h6]
  have h7 : dyadicDelta j * |(T.a : ℝ)| ≤ dyadicDelta j * (2 : ℝ)^j :=
    mul_le_mul_of_nonneg_left h2 hδ_pos.le
  have h8 : dyadicDelta j * (2 : ℝ)^j = 1 := by
    simp [dyadicDelta] <;> field_simp <;> ring
  rw [h8] at h7
  exact h7

/-- wideToAffineLine equals cobalt's WideCenterLine.wideCenterLine. -/
lemma wideToAffineLine_eq_wideCenterLine (j : ℕ) (T : DyadicTube j) :
    wideToAffineLine T = WideCenterLine.wideCenterLine j T := by
  simp [wideToAffineLine, WideCenterLine.wideCenterLine] <;> ring_nf

/-- From incidence to a point in B(0,1) and small δ, derive |T.intercept| ≤ 3.

    Uses the offset bound: ‖wideToAffineLine.offset‖ ≤ 1 + 4δ.
    For line y = mx + b', ‖offset‖ = |b'| / √(1+m²).
    With |m| ≤ 1: |b'| ≤ (1+4δ)√2.
    Since b' = m/2 + b - 1/2: |b| ≤ (1+4δ)√2 + 1.
    For δ ≤ (√2-1)/4, this gives |b| ≤ 3. -/
lemma intercept_bound_3_from_incidence {j : ℕ} {T : DyadicTube j} {p : Plane}
    (hp : ‖p‖ ≤ 1)
    (hδ_small : dyadicDelta j ≤ (Real.sqrt 2 - 1) / 4)
    (h_inc : p ∈ Metric.cthickening (dyadicDelta j) (canonicalWideCarrier j T))
    (hm : |T.slope| ≤ 1) :
    |T.intercept| ≤ 3 := by
  set δ := dyadicDelta j with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos j
  set m := T.slope with hm_def
  set b := T.intercept with hb_def
  set b' := m / 2 + b - 1 / 2 with hb'_def
  set ℓ := wideToAffineLine T with hℓ

  have h_off_bound : ‖ℓ.offset‖ ≤ 1 + 4 * δ := by
    have h_eq : ℓ = WideCenterLine.wideCenterLine j T :=
      wideToAffineLine_eq_wideCenterLine j T
    rw [h_eq]
    exact WideCenterLine.offset_bound_from_incidence hp h_inc

  have h_off_formula : ℓ.offset = b' • offsetVec m := by
    rw [hℓ]
    exact offset_formula m b'

  have h_norm : ‖ℓ.offset‖ = |b'| / Real.sqrt (1 + m^2) := by
    rw [h_off_formula]
    have h1 : ‖b' • offsetVec m‖ = |b'| * ‖offsetVec m‖ := by
      rw [norm_smul] <;> rfl
    rw [h1, offsetVec_norm m] <;> ring

  rw [h_norm] at h_off_bound

  have h_m2 : m^2 ≤ 1 := by nlinarith [abs_le.mp hm]
  have h_sqrt_le : Real.sqrt (1 + m^2) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt (by linarith)
  have h_sqrt_pos : 0 < Real.sqrt (1 + m^2) := by positivity

  have h_b'_bound : |b'| ≤ (1 + 4 * δ) * Real.sqrt (1 + m^2) := by
    have h : |b'| / Real.sqrt (1 + m^2) ≤ 1 + 4 * δ := h_off_bound
    have h_eq2 : (|b'| / Real.sqrt (1 + m^2)) * Real.sqrt (1 + m^2) = |b'| := by
      field_simp [h_sqrt_pos.ne'] <;> ring
    calc |b'|
      = (|b'| / Real.sqrt (1 + m^2)) * Real.sqrt (1 + m^2) := h_eq2.symm
    _ ≤ (1 + 4 * δ) * Real.sqrt (1 + m^2) := by gcongr

  have h_b'_bound2 : |b'| ≤ (1 + 4 * δ) * Real.sqrt 2 := by
    calc |b'|
      ≤ (1 + 4 * δ) * Real.sqrt (1 + m^2) := h_b'_bound
    _ ≤ (1 + 4 * δ) * Real.sqrt 2 := by gcongr

  have h_b_eq : b = b' - m / 2 + 1 / 2 := by
    simp only [hb'_def] <;> ring

  have h_b_bound : |b| ≤ (1 + 4 * δ) * Real.sqrt 2 + 1 := by
    rw [h_b_eq]
    have h : |b' - m / 2 + 1 / 2| ≤ |b'| + |m / 2| + 1 / 2 := by
      have h1 : |b' - m / 2 + 1 / 2| ≤ |b'| + |m / 2 - 1 / 2| := by
        have h_alg : b' - m / 2 + 1 / 2 = b' - (m / 2 - 1 / 2) := by ring
        rw [h_alg]
        exact abs_sub b' (m / 2 - 1 / 2)
      have h2 : |m / 2 - 1 / 2| ≤ |m / 2| + 1 / 2 := by
        have h4 : m / 2 - 1 / 2 = m / 2 + (-1 / 2 : ℝ) := by ring
        rw [h4]
        have h3 : |m / 2 + (-1 / 2 : ℝ)| ≤ |m / 2| + |(-1 / 2 : ℝ)| := by exact real_abs_add (m / 2) (-1 / 2)
        have h5 : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num
        rw [h5] at h3; exact h3
      linarith
    have h5 : |m / 2| = |m| / 2 := by
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    rw [h5] at h
    linarith [hm, h_b'_bound2]

  have h_final : (1 + 4 * δ) * Real.sqrt 2 + 1 ≤ 3 := by
    have h1 : 4 * δ ≤ Real.sqrt 2 - 1 := by linarith [hδ_small]
    have h2 : 1 + 4 * δ ≤ Real.sqrt 2 := by linarith
    have h3 : (1 + 4 * δ) * Real.sqrt 2 ≤ Real.sqrt 2 * Real.sqrt 2 := by
      gcongr <;> linarith
    have h4 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      rw [← Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;> norm_num
    have h5 : (1 + 4 * δ) * Real.sqrt 2 ≤ 2 := by
      rw [h4] at h3; exact h3
    linarith

  linarith [h_b_bound, h_final]

/-- A set of DyadicTubes with bounded slope and intercept is finite.

    Since slope = T.a * δ and intercept = T.b * δ with δ > 0,
    bounded real values imply bounded integer indices. -/
lemma bounded_tubes_finite {j : ℕ} {F : Set (DyadicTube j)}
    (hm : ∀ T ∈ F, |T.slope| ≤ 1)
    (hb : ∀ T ∈ F, |T.intercept| ≤ 3) :
    Set.Finite F := by
  set δ := dyadicDelta j with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos j
  have h1 : ∀ T ∈ F, |(T.a : ℝ)| ≤ 1 / δ := by
    intro T hT
    have h2 : |T.slope| ≤ 1 := hm T hT
    have h3 : T.slope = δ * (T.a : ℝ) := by
      simp [DyadicTube.slope] <;> ring
    rw [h3] at h2
    have h4 : |δ * (T.a : ℝ)| ≤ 1 := h2
    have h5 : |δ * (T.a : ℝ)| = δ * |(T.a : ℝ)| := by
      rw [abs_mul, abs_of_pos hδ_pos] <;> ring
    rw [h5] at h4
    calc |(T.a : ℝ)|
      = (δ * |(T.a : ℝ)|) / δ := by field_simp [hδ_pos.ne'] <;> ring
    _ ≤ 1 / δ := by gcongr
  have h2 : ∀ T ∈ F, |(T.b : ℝ)| ≤ 3 / δ := by
    intro T hT
    have h3 : |T.intercept| ≤ 3 := hb T hT
    have h4 : T.intercept = δ * (T.b : ℝ) := by
      simp [DyadicTube.intercept] <;> ring
    rw [h4] at h3
    have h5 : |δ * (T.b : ℝ)| = δ * |(T.b : ℝ)| := by
      rw [abs_mul, abs_of_pos hδ_pos] <;> ring
    rw [h5] at h3
    calc |(T.b : ℝ)|
      = (δ * |(T.b : ℝ)|) / δ := by field_simp [hδ_pos.ne'] <;> ring
    _ ≤ 3 / δ := by gcongr
  let A : Finset ℤ := Finset.Icc (Int.ceil (-(1 / δ))) (Int.floor (1 / δ))
  let B : Finset ℤ := Finset.Icc (Int.ceil (-(3 / δ))) (Int.floor (3 / δ))
  have h3 : F ⊆ {T : DyadicTube j | T.a ∈ A ∧ T.b ∈ B} := by
    intro T hT
    have h4 : |(T.a : ℝ)| ≤ 1 / δ := h1 T hT
    have h5 : |(T.b : ℝ)| ≤ 3 / δ := h2 T hT
    have h6 : T.a ∈ A := by
      simp only [A, Finset.mem_Icc]
      have h7 : -(1 / δ) ≤ (T.a : ℝ) := (abs_le.mp h4).1
      have h8 : (T.a : ℝ) ≤ 1 / δ := (abs_le.mp h4).2
      constructor
      · exact_mod_cast (Int.ceil_le.mpr h7)
      · exact_mod_cast (Int.le_floor.mpr h8)
    have h9 : T.b ∈ B := by
      simp only [B, Finset.mem_Icc]
      have h10 : -(3 / δ) ≤ (T.b : ℝ) := (abs_le.mp h5).1
      have h11 : (T.b : ℝ) ≤ 3 / δ := (abs_le.mp h5).2
      constructor
      · exact_mod_cast (Int.ceil_le.mpr h10)
      · exact_mod_cast (Int.le_floor.mpr h11)
    exact ⟨h6, h9⟩
  let f : DyadicTube j → ℤ × ℤ := fun T => (T.a, T.b)
  have h_inj : Set.InjOn f F := by
    intro T1 _ T2 _ h
    have h' : T1.a = T2.a ∧ T1.b = T2.b := by simpa [f, Prod.ext_iff] using h
    cases T1 <;> cases T2 <;> simp_all (config := {decide := true}) <;> aesop
  have h4 : Set.Finite (f '' F) := by
    apply Set.Finite.subset (A ×ˢ B).finite_toSet
    rintro ⟨a, b⟩ h
    have h_mem : ∃ (T : DyadicTube j), T ∈ F ∧ f T = (a, b) := by
      simpa [Set.mem_image] using h
    rcases h_mem with ⟨T, hT, h_eq⟩
    have h_a : T.a = a := by
      simp [f] at h_eq <;> exact h_eq.1
    have h_b : T.b = b := by
      simp [f] at h_eq <;> exact h_eq.2
    have h5 := h3 hT
    have h_goal : (a, b) ∈ (A ×ˢ B) := by
      simp only [Finset.mem_product]
      exact ⟨h_a.symm ▸ h5.1, h_b.symm ▸ h5.2⟩
    exact h_goal
  have h5 : Set.Finite F := by exact Set.Finite.of_finite_image h4 h_inj
  exact h5

/-- Set-valued tube S-set transfer using the finite adapter.

    Given slope bounds, incidence to a bounded point set, and small δ,
    derives intercept bounds, proves finiteness, converts to Finset,
    and calls the finite adapter `wide_tubeSSet_transfer_9δ`. -/
lemma tube_sset_transfer_set
    {j : ℕ} {s C : ℝ} {F : Set (DyadicTube j)} {P : Set Plane}
    (hδ_small : dyadicDelta j ≤ (Real.sqrt 2 - 1) / 4)
    (hC_one : 1 ≤ C)
    (hs : 0 ≤ s) (hs_lt_one : s < 1)
    (hP : P ⊆ Metric.closedBall 0 1)
    (h_slopes : ∀ T ∈ F, |T.slope| ≤ 1)
    (h_inc : ∀ T ∈ F, ∃ p ∈ P,
      p ∈ Metric.cthickening (dyadicDelta j) (canonicalWideCarrier j T))
    (h : IsDeltaSSet (dyadicDelta j) s C F) :
    IsDeltaSSet (9 * dyadicDelta j) s
      (max 1 (10 * C) * 38179 * 176^s)
      (wideToAffineLine '' F) := by
  set δ := dyadicDelta j with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos j
  -- Derive intercept bound ≤ 3 from incidence
  have hb : ∀ T ∈ F, |T.intercept| ≤ 3 := by
    intro T hT
    rcases h_inc T hT with ⟨p, hpP, hp_inc⟩
    have hp_ball : ‖p‖ ≤ 1 := by
      have h : p ∈ Metric.closedBall (0 : Plane) 1 := hP hpP
      simpa [Metric.mem_closedBall] using h
    exact intercept_bound_3_from_incidence hp_ball hδ_small hp_inc (h_slopes T hT)
  -- Prove finiteness
  have h_fin : Set.Finite F := bounded_tubes_finite h_slopes hb
  -- Convert to Finset
  let F' : Finset (DyadicTube j) := h_fin.toFinset
  have h_coe : (F' : Set (DyadicTube j)) = F := h_fin.coe_toFinset
  -- Call finite adapter
  have h_slopes' : ∀ T ∈ F', |T.slope| ≤ 1 := by
    intro T hT
    have hT_F : T ∈ F := by
      have h : T ∈ (F' : Set (DyadicTube j)) := hT
      rw [h_coe] at h
      exact h
    exact h_slopes T hT_F
  have hb' : ∀ T ∈ F', |T.intercept| ≤ 3 := by
    intro T hT
    have hT_F : T ∈ F := by
      have h : T ∈ (F' : Set (DyadicTube j)) := hT
      rw [h_coe] at h
      exact h
    exact hb T hT_F
  have h' : IsDeltaSSet δ s C (F' : Set (DyadicTube j)) := by
    have h_eq : (F' : Set (DyadicTube j)) = F := h_coe
    rw [h_eq]
    exact h
  have h_main := wide_tubeSSet_transfer_9δ
    (hs := hs) (hs_lt_one := hs_lt_one) (hC_one := hC_one)
    (hm := h_slopes') (hb := hb') h'
  have h_final : IsDeltaSSet (9 * δ) s (max 1 (10 * C) * 38179 * 176^s)
      (wideToAffineLine '' (F' : Set (DyadicTube j))) := h_main
  have h_img_eq : wideToAffineLine '' (F' : Set (DyadicTube j)) = wideToAffineLine '' F := by
    rw [h_coe]
  rw [h_img_eq] at h_final
  exact h_final

/-! ============================================================================
   Full transfer lemma (pending sub-results are explicit hypotheses)
   ============================================================================ -/

/-- Transfer a uniform regular incidence estimate from thin AffineLine carrier
    to wide canonicalWideCarrier at a specific dyadic scale.

    Uses Kcarrier = 9 throughout.

    Tube S-set transfer is discharged internally via `tube_sset_transfer_set`,
    which requires δ ≤ (√2-1)/4 and C_tube = 381790 * 176^s.

    Remaining explicit hypotheses:
    - h_ncover_transfer: Ncover(9δ, wideToAffineLine '' F) ≤ Ncover(δ, F)
    - h_sset_scale: EuclideanPlane δ-Sset → 9δ-Sset
    - h_absorb_*: exponent absorption conditions (follow from ε_inc < εA and small δ)
-/
lemma uniform_wide_transfer_at_scale
    {s t εA ε_inc C_tube : ℝ} (j : ℕ)
    (hεA_pos : 0 < εA)
    (hε_inc_pos : 0 < ε_inc)
    (hε_inc_lt : ε_inc < εA)
    (hs : 0 ≤ s)
    (hs_lt_one : s < 1)
    (hδ_small : dyadicDelta j ≤ (Real.sqrt 2 - 1) / 4)
    (hC_tube_eq : C_tube = 381790 * (176 : ℝ) ^ s)
    (δR_thin : ℝ)
    (h_body : RegularIncidenceBody (fun ℓ : AffineLine => ℓ.1) s t εA εA δR_thin)
    (δR : ℝ)
    (hδR_pos : 0 < δR)
    (hδR_one : δR ≤ 1)
    (h_threshold : 9 * δR ≤ δR_thin)
    -- Ncover transfer via cobalt's WideCenterLine (scale-specific to dyadicDelta j)
    (h_ncover_transfer : ∀ (F : Set (DyadicTube j)) (P : Set Plane)
        (hP : P ⊆ Metric.closedBall 0 1)
        (h_inc : ∀ T ∈ F, ∃ p ∈ P, p ∈ Metric.cthickening (dyadicDelta j) (canonicalWideCarrier j T)),
        Ncover (9 * dyadicDelta j) (wideToAffineLine '' F) ≤ Ncover (dyadicDelta j) F)
    -- Point S-set scaling δ → 9δ in EuclideanPlane (discharged via kestrel + indigo)
    (h_sset_scale : ∀ (P : Set Plane) (δ u C : ℝ), 0 < δ →
        Bornology.IsBounded P →
        IsDeltaSSet δ u C P →
        IsDeltaSSet (9 * δ) u (C * 361) P)
    -- Absorption: tube S-set constant ≤ (9δ)^{-εA}
    (h_absorb_tube : ∀ δ, 0 < δ → δ ≤ δR →
        (Real.rpow δ (-ε_inc)) * C_tube ≤ Real.rpow (9 * δ) (-εA))
    -- Absorption: point S-set constant ≤ (9δ)^{-εA}
    (h_absorb_point : ∀ δ, 0 < δ → δ ≤ δR →
        (Real.rpow δ (-ε_inc)) * 361 ≤ Real.rpow (9 * δ) (-εA))
    -- Absorption: sqrt regularity bound (for any u ∈ [t,2])
    (h_absorb_sqrt : ∀ (u : ℝ), t ≤ u → u ≤ 2 → ∀ δ, 0 < δ → δ ≤ δR →
        Real.rpow δ (-(u / 2 + ε_inc)) ≤ Real.rpow (9 * δ) (-(u / 2 + εA)))
    -- Absorption: output exponent
    (h_absorb_output : ∀ δ, 0 < δ → δ ≤ δR →
        Real.rpow δ (-(2 * s + ε_inc)) ≤ Real.rpow (9 * δ) (-(2 * s + εA))) :
    dyadicDelta j ≤ δR →
    RegularIncidenceAtScale (canonicalWideCarrier j) s t ε_inc ε_inc (dyadicDelta j) := by
  intro hδj_le
  set δ : ℝ := dyadicDelta j with hδ_def
  have hδ_pos : 0 < δ := dyadicDelta_pos j
  have hδ_le : δ ≤ δR := hδj_le
  set δ' : ℝ := 9 * δ with hδ'_def
  have hδ'_pos : 0 < δ' := by positivity
  have hδ'_le : δ' ≤ δR_thin := by
    have h1 : δ' = 9 * δ := by rfl
    rw [h1]
    have h2 : 9 * δ ≤ 9 * δR := by gcongr
    exact le_trans h2 h_threshold

  intro u hu_t hu_two P hP_subset hReg tubeFamily hTubes hIncidence hChart

  -- Map tube families to AffineLine
  let tubeFamily' : (p : Plane) → p ∈ P → Set AffineLine :=
    fun p hp => wideToAffineLine '' (tubeFamily p hp)

  -- Chart preservation for the wide AffineLine family
  have hChart' : ∀ p hp, ∀ ℓ ∈ tubeFamily' p hp,
      InStandardChart.inChart ℓ := by
    intro p hp ℓ hℓ
    rcases hℓ with ⟨T, hT, rfl⟩
    exact wideToAffineLine_inChart T (hChart p hp T hT)

  -- Step 1: Transfer incidence: wide at δ → thin at δ' = 9δ
  have hIncidence' : ∀ p hp, ∀ ℓ ∈ tubeFamily' p hp,
      p ∈ Metric.cthickening δ' ((fun ℓ : AffineLine => ℓ.1) ℓ) := by
    intro p hp ℓ hℓ
    rcases hℓ with ⟨T, hT, rfl⟩
    have h_wide : p ∈ Metric.cthickening δ (canonicalWideCarrier j T) :=
      hIncidence p hp T hT
    have h4δ : p ∈ Metric.cthickening (δ + 3 * δ) (wideToAffineLine T).1 :=
      wide_incidence_to_thin hδ_pos T p h_wide
    have h_sum : δ + 3 * δ = 4 * δ := by ring
    rw [h_sum] at h4δ
    have h4δ_le_9δ : 4 * δ ≤ δ' := by
      rw [hδ'_def] <;> linarith
    exact Metric.cthickening_mono h4δ_le_9δ _ h4δ

  -- Step 2: Transfer tube S-sets: DyadicTube at δ → AffineLine at 9δ
  have hTubes' : ∀ p hp,
      IsDeltaSSet δ' s (Real.rpow δ' (-εA)) (tubeFamily' p hp) := by
    intro p hp
    have h_orig : IsDeltaSSet δ s (Real.rpow δ (-ε_inc)) (tubeFamily p hp) :=
      hTubes p hp
    set C : ℝ := Real.rpow δ (-ε_inc) with hC_def
    have hC_one : 1 ≤ C := by
      rw [hC_def]
      have hδ_le_one : δ ≤ 1 := le_trans hδ_le hδR_one
      have h : Real.rpow δ 0 ≤ Real.rpow δ (-ε_inc) :=
        Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one (by linarith)
      simpa using h
    have h_slopes : ∀ T ∈ tubeFamily p hp, |T.slope| ≤ 1 := by
      intro T hT
      exact slope_le_one_of_inChart (hChart p hp T hT)
    have h_inc : ∀ T ∈ tubeFamily p hp, ∃ p' ∈ P,
        p' ∈ Metric.cthickening δ (canonicalWideCarrier j T) := by
      intro T hT
      exact ⟨p, hp, hIncidence p hp T hT⟩
    have h_scaled0 : IsDeltaSSet δ' s
        (max 1 (10 * C) * 38179 * 176^s)
        (tubeFamily' p hp) :=
      tube_sset_transfer_set (hδ_small := hδ_small) (hC_one := hC_one)
        (hs := hs) (hs_lt_one := hs_lt_one) (hP := hP_subset)
        (h_slopes := h_slopes) (h_inc := h_inc) h_orig
    have h_max : max 1 (10 * C) = 10 * C := by
      rw [max_eq_right] <;> linarith
    have h_const_eq : (max 1 (10 * C) * 38179 * 176^s) = C * C_tube := by
      rw [h_max, hC_tube_eq] <;> ring
    rw [h_const_eq] at h_scaled0
    have h_abs : C * C_tube ≤ Real.rpow δ' (-εA) := by
      have h_eq : δ' = 9 * δ := by rfl
      rw [h_eq]
      exact h_absorb_tube δ hδ_pos hδ_le
    exact IsDeltaSSet.weaken_C h_scaled0 h_abs

  -- Step 3: Transfer point square-root regularity from δ to 9δ
  have hReg' : IsSquareRootRegular δ' u
      (Real.rpow δ' (-εA)) (Real.rpow δ' (-εA)) P := by
    -- Part A: S-set scaling
    have hP_delta : IsDeltaSSet δ u (Real.rpow δ (-ε_inc)) P :=
      hReg.to_isDeltaSSet
    have hP_bdd : Bornology.IsBounded P :=
      Metric.isBounded_closedBall.subset hP_subset
    have hP_scaled : IsDeltaSSet δ' u
        ((Real.rpow δ (-ε_inc)) * 361) P :=
      h_sset_scale P δ u (Real.rpow δ (-ε_inc)) hδ_pos hP_bdd hP_delta
    have hP_abs : (Real.rpow δ (-ε_inc)) * 361 ≤
        Real.rpow δ' (-εA) := by
      have h_eq : δ' = 9 * δ := by rfl
      rw [h_eq]
      exact h_absorb_point δ hδ_pos hδ_le
    have hP_delta' : IsDeltaSSet δ' u (Real.rpow δ' (-εA)) P :=
      IsDeltaSSet.weaken_C hP_scaled hP_abs

    -- Part B: sqrt covering bound via antitonicity
    have h_sqrt_orig : Ncover (Real.sqrt δ) P ≤
        ENNReal.ofReal (Real.rpow δ (-(u / 2 + ε_inc))) :=
      hReg.ncover_sqrt_bound_simplified hδ_pos
    have h_sqrt_le : Real.sqrt δ ≤ Real.sqrt δ' := by
      apply Real.sqrt_le_sqrt
      <;> linarith
    have h_sqrt_le' : (Real.sqrt δ).toNNReal ≤ (Real.sqrt δ').toNNReal := by
      apply Real.toNNReal_le_toNNReal
      <;> linarith
    have h_sqrt_antitone : Metric.externalCoveringNumber (Real.sqrt δ').toNNReal P ≤
        Metric.externalCoveringNumber (Real.sqrt δ).toNNReal P :=
      Metric.externalCoveringNumber_anti h_sqrt_le'
    have h_sqrt_abs : Real.rpow δ (-(u / 2 + ε_inc)) ≤
        Real.rpow δ' (-(u / 2 + εA)) := by
      have h_eq : δ' = 9 * δ := by rfl
      rw [h_eq]
      exact h_absorb_sqrt u hu_t hu_two δ hδ_pos hδ_le
    have h_rpow_eq : Real.rpow δ' (-(u / 2 + εA)) =
        Real.rpow δ' (-εA) * Real.rpow δ' (-u / 2) := by
      have h : Real.rpow δ' (-εA) * Real.rpow δ' (-u / 2) =
          Real.rpow δ' ((-εA) + (-u / 2)) :=
        (Real.rpow_add hδ'_pos (-εA) (-u / 2)).symm
      have h2 : (-εA) + (-u / 2) = -(u / 2 + εA) := by ring
      rw [h2] at h
      exact h.symm
    have hP_sqrt' : Ncover (Real.sqrt δ') P ≤
        ENNReal.ofReal (Real.rpow δ' (-εA) * Real.rpow δ' (-u / 2)) := by
      calc Ncover (Real.sqrt δ') P
        ≤ Ncover (Real.sqrt δ) P := by simpa [Ncover] using h_sqrt_antitone
      _ ≤ ENNReal.ofReal (Real.rpow δ (-(u / 2 + ε_inc))) := h_sqrt_orig
      _ ≤ ENNReal.ofReal (Real.rpow δ' (-(u / 2 + εA))) := by
        exact ENNReal.ofReal_le_ofReal h_sqrt_abs
      _ = ENNReal.ofReal (Real.rpow δ' (-εA) * Real.rpow δ' (-u / 2)) := by
        rw [h_rpow_eq]
    exact ⟨hP_delta', hP_sqrt'⟩

  -- Step 4: Apply thin estimate at scale δ' = 9δ
  have h_main : ENNReal.ofReal (Real.rpow δ' (-(2 * s + εA))) ≤
      Ncover δ' (⋃ p, ⋃ hp : p ∈ P, tubeFamily' p hp) :=
    h_body u hu_t hu_two hδ'_pos hδ'_le P hP_subset hReg'
      tubeFamily' hTubes' hIncidence' hChart'

  -- Step 5: Transfer Ncover back: Ncover(δ, original) ≥ Ncover(9δ, image)
  let allTubes : Set (DyadicTube j) := ⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp
  let allTubes' : Set AffineLine := ⋃ p, ⋃ hp : p ∈ P, tubeFamily' p hp

  have h_image_eq : wideToAffineLine '' allTubes = allTubes' := by
    ext ℓ
    simp only [allTubes, allTubes', Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨T, ⟨p, hp, T_in⟩, rfl⟩
      exact ⟨p, hp, T, T_in, rfl⟩
    · rintro ⟨p, hp, T, T_in, rfl⟩
      exact ⟨T, ⟨p, hp, T_in⟩, rfl⟩

  have h_allTubes_inc : ∀ T ∈ allTubes, ∃ p ∈ P,
      p ∈ Metric.cthickening δ (canonicalWideCarrier j T) := by
    intro T hT
    rcases Set.mem_iUnion.mp hT with ⟨p, hpT⟩
    rcases Set.mem_iUnion.mp hpT with ⟨hp, T_in⟩
    exact ⟨p, hp, hIncidence p hp T T_in⟩
  have h_transfer : Ncover δ' allTubes' ≤ Ncover δ allTubes := by
    rw [← h_image_eq]
    exact h_ncover_transfer allTubes P hP_subset h_allTubes_inc

  -- Step 6: Absorb 9 into output exponent
  have h_absorb_out : ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_inc))) ≤
      ENNReal.ofReal (Real.rpow δ' (-(2 * s + εA))) := by
    have h1 : Real.rpow δ (-(2 * s + ε_inc)) ≤
        Real.rpow δ' (-(2 * s + εA)) := by
      have h_eq : δ' = 9 * δ := by rfl
      rw [h_eq]
      exact h_absorb_output δ hδ_pos hδ_le
    exact ENNReal.ofReal_le_ofReal h1

  -- Final chain
  calc ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_inc)))
    ≤ ENNReal.ofReal (Real.rpow δ' (-(2 * s + εA))) := h_absorb_out
  _ ≤ Ncover δ' allTubes' := h_main
  _ ≤ Ncover δ allTubes := h_transfer

/-- Derive all four absorption conditions from a single uniform small-δ bound.

    Given `h_small : δ^(εA-ε_inc) ≤ 9^(-εA) / C_tube` for all `δ ≤ δR`,
    this implies tube (with constant C_tube), point (with constant 361),
    sqrt, and output absorption.

    Requires `C_tube ≥ 361` so point absorption follows from tube absorption,
    and so the sqrt/output exponent bounds hold. -/
lemma absorption_all
    {s t εA ε_inc δR C_tube : ℝ}
    (hεA_pos : 0 < εA)
    (hε_inc_pos : 0 < ε_inc)
    (hε_inc_lt : ε_inc < εA)
    (hs1 : s < 1)
    (hC_tube_pos : 0 < C_tube)
    (hC_tube_ge : (361 : ℝ) ≤ C_tube)
    (h_small : ∀ δ, 0 < δ → δ ≤ δR →
        Real.rpow δ (εA - ε_inc) ≤ (9 : ℝ) ^ (-εA) / C_tube) :
    (∀ δ, 0 < δ → δ ≤ δR →
        (Real.rpow δ (-ε_inc)) * C_tube ≤ Real.rpow (9 * δ) (-εA)) ∧
    (∀ δ, 0 < δ → δ ≤ δR →
        (Real.rpow δ (-ε_inc)) * 361 ≤ Real.rpow (9 * δ) (-εA)) ∧
    (∀ (u : ℝ), t ≤ u → u ≤ 2 → ∀ δ, 0 < δ → δ ≤ δR →
        Real.rpow δ (-(u / 2 + ε_inc)) ≤ Real.rpow (9 * δ) (-(u / 2 + εA))) ∧
    (∀ δ, 0 < δ → δ ≤ δR →
        Real.rpow δ (-(2 * s + ε_inc)) ≤ Real.rpow (9 * δ) (-(2 * s + εA))) := by
  have h9_pos : (0 : ℝ) < 9 := by norm_num
  have h9_gt_one : (1 : ℝ) < 9 := by norm_num
  have h_diff_pos : 0 < εA - ε_inc := by linarith

  -- Common: (9δ)^x = 9^x * δ^x
  have h_mul9 : ∀ (x : ℝ) (δ : ℝ), 0 < δ →
      Real.rpow (9 * δ) x = (9 : ℝ) ^ x * Real.rpow δ x := by
    intro x δ hδ
    exact Real.mul_rpow (hx := by norm_num) (hy := by linarith)

  -- Key: δ^(εA-ε_inc) * δ^(-εA) = δ^(-ε_inc)
  have h_key1 : ∀ (δ : ℝ), 0 < δ →
      Real.rpow δ (εA - ε_inc) * Real.rpow δ (-εA) = Real.rpow δ (-ε_inc) := by
    intro δ hδ
    have h : Real.rpow δ (εA - ε_inc) * Real.rpow δ (-εA) = Real.rpow δ ((εA - ε_inc) + (-εA)) :=
      (Real.rpow_add hδ (εA - ε_inc) (-εA)).symm
    have h_sum : (εA - ε_inc) + (-εA) = -ε_inc := by ring
    rw [h, h_sum]

  -- 1. Tube absorption
  have h1 : ∀ δ, 0 < δ → δ ≤ δR →
      (Real.rpow δ (-ε_inc)) * C_tube ≤ Real.rpow (9 * δ) (-εA) := by
    intro δ hδ hδR
    have hU : Real.rpow δ (εA - ε_inc) ≤ (9 : ℝ) ^ (-εA) / C_tube := h_small δ hδ hδR
    rw [h_mul9 (-εA) δ hδ]
    have h_ineq : C_tube * Real.rpow δ (εA - ε_inc) ≤ (9 : ℝ) ^ (-εA) := by
      calc C_tube * Real.rpow δ (εA - ε_inc)
        ≤ C_tube * ((9 : ℝ) ^ (-εA) / C_tube) := by gcongr
      _ = (9 : ℝ) ^ (-εA) := by
        field_simp [hC_tube_pos.ne'] <;> ring
    have h_final : (Real.rpow δ (-ε_inc)) * C_tube ≤
        (9 : ℝ) ^ (-εA) * Real.rpow δ (-εA) := by
      have h_mult : (Real.rpow δ (-ε_inc)) * C_tube =
          C_tube * Real.rpow δ (εA - ε_inc) * Real.rpow δ (-εA) := by
        rw [← h_key1 δ hδ] <;> ring
      rw [h_mult]
      have h_pos2 : 0 ≤ Real.rpow δ (-εA) := Real.rpow_nonneg hδ.le _
      gcongr <;> linarith
    exact h_final

  -- 2. Point absorption (361 ≤ C_tube)
  have h2 : ∀ δ, 0 < δ → δ ≤ δR →
      (Real.rpow δ (-ε_inc)) * 361 ≤ Real.rpow (9 * δ) (-εA) := by
    intro δ hδ hδR
    have h1δ := h1 δ hδ hδR
    have h_pos : 0 < Real.rpow δ (-ε_inc) := Real.rpow_pos_of_pos hδ _
    have h_le : (Real.rpow δ (-ε_inc)) * 361 ≤
        (Real.rpow δ (-ε_inc)) * C_tube := by
      gcongr <;> linarith
    exact le_trans h_le h1δ

  -- General pattern for sqrt/output:
  -- δ^(-y-ε_inc) ≤ (9δ)^(-y-εA) ↔ δ^(εA-ε_inc) ≤ 9^(-y-εA)
  -- We have h_small: δ^(εA-ε_inc) ≤ 9^(-εA)/C_tube
  -- Need 9^(-εA)/C_tube ≤ 9^(-y-εA), i.e. C_tube ≥ 9^y
  -- For y ≤ 2, 9^y ≤ 81 ≤ 361 ≤ C_tube.
  have h_general : ∀ (y : ℝ), y ≤ 2 → ∀ δ, 0 < δ → δ ≤ δR →
      Real.rpow δ (-(y + ε_inc)) ≤ Real.rpow (9 * δ) (-(y + εA)) := by
    intro y hy δ hδ hδR
    have hU : Real.rpow δ (εA - ε_inc) ≤ (9 : ℝ) ^ (-εA) / C_tube := h_small δ hδ hδR
    have h9y_le : (9 : ℝ) ^ y ≤ C_tube := by
      have h1 : (9 : ℝ) ^ y ≤ (9 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hy
      have h2 : (9 : ℝ) ^ (2 : ℝ) = 81 := by norm_num
      linarith
    have h_bound : (9 : ℝ) ^ (-εA) / C_tube ≤ (9 : ℝ) ^ (-(y + εA)) := by
      have h3 : (9 : ℝ) ^ (-(y + εA)) = (9 : ℝ) ^ (-εA) / (9 : ℝ) ^ y := by
        have h4 : (9 : ℝ) ^ (-y) = ((9 : ℝ) ^ y)⁻¹ := by
          have h5 : (9 : ℝ) ^ y * (9 : ℝ) ^ (-y) = 1 := by
            have h6 := Real.rpow_add h9_pos y (-y)
            have h7 : y + (-y) = 0 := by ring
            rw [h7] at h6
            have h8 : (9 : ℝ) ^ (0 : ℝ) = 1 := by simp
            rw [h8] at h6
            exact h6.symm
          field_simp [(Real.rpow_pos_of_pos h9_pos y).ne'] <;> linarith
        have h9 : (9 : ℝ) ^ (-(y + εA)) = (9 : ℝ) ^ (-εA) * (9 : ℝ) ^ (-y) := by
          have h10 := Real.rpow_add h9_pos (-εA) (-y)
          have h11 : (-εA) + (-y) = -(y + εA) := by ring
          rw [h11] at h10
          exact h10
        rw [h9, h4] <;> ring
      rw [h3]
      have h_pos : 0 < (9 : ℝ) ^ y := Real.rpow_pos_of_pos h9_pos _
      gcongr
      <;> linarith
    have hU' : Real.rpow δ (εA - ε_inc) ≤ (9 : ℝ) ^ (-(y + εA)) := le_trans hU h_bound
    have h_key : Real.rpow δ (εA - ε_inc) * Real.rpow δ (-(y + εA)) = Real.rpow δ (-(y + ε_inc)) := by
      have h := Real.rpow_add hδ (εA - ε_inc) (-(y + εA))
      have h_sum : (εA - ε_inc) + (-(y + εA)) = -(y + ε_inc) := by ring
      rw [h_sum] at h
      exact h.symm
    have h_final : Real.rpow δ (-(y + ε_inc)) ≤
        (9 : ℝ) ^ (-(y + εA)) * Real.rpow δ (-(y + εA)) := by
      have h_mult : Real.rpow δ (-(y + ε_inc)) =
          Real.rpow δ (εA - ε_inc) * Real.rpow δ (-(y + εA)) := h_key.symm
      rw [h_mult]
      have h_pos2 : 0 ≤ Real.rpow δ (-(y + εA)) := Real.rpow_nonneg hδ.le _
      gcongr <;> linarith
    have h_goal : Real.rpow (9 * δ) (-(y + εA)) =
        (9 : ℝ) ^ (-(y + εA)) * Real.rpow δ (-(y + εA)) := h_mul9 (-(y + εA)) δ hδ
    rw [h_goal]
    exact h_final

  -- 3. Sqrt absorption: y = u/2 ≤ 1 ≤ 2
  have h3 : ∀ (u : ℝ), t ≤ u → u ≤ 2 → ∀ δ, 0 < δ → δ ≤ δR →
      Real.rpow δ (-(u / 2 + ε_inc)) ≤ Real.rpow (9 * δ) (-(u / 2 + εA)) := by
    intro u hu_t hu_two δ hδ hδR
    have hy : u / 2 ≤ 2 := by linarith
    exact h_general (u / 2) hy δ hδ hδR

  -- 4. Output absorption: y = 2s < 2
  have h4 : ∀ δ, 0 < δ → δ ≤ δR →
      Real.rpow δ (-(2 * s + ε_inc)) ≤ Real.rpow (9 * δ) (-(2 * s + εA)) := by
    intro δ hδ hδR
    have hy : 2 * s ≤ 2 := by linarith [hs1]
    exact h_general (2 * s) hy δ hδ hδR

  exact ⟨h1, h2, h3, h4⟩

/-- Given εA > ε_inc > 0 and C_tube > 0, there exists δR > 0 such that
    `δ^(εA-ε_inc) ≤ 9^(-εA) / C_tube` for all `0 < δ ≤ δR`.

    Threshold: δR = (9^εA * C_tube)^(-1/(εA-ε_inc)). -/
lemma exists_absorption_deltaR
    {εA ε_inc C_tube : ℝ} (hεA_pos : 0 < εA) (hε_inc_pos : 0 < ε_inc)
    (hε_inc_lt : ε_inc < εA) (hC_tube_pos : 0 < C_tube) :
    ∃ (δR : ℝ), 0 < δR ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δR →
        Real.rpow δ (εA - ε_inc) ≤ (9 : ℝ) ^ (-εA) / C_tube := by
  set α : ℝ := εA - ε_inc with hα_def
  have hα_pos : 0 < α := by linarith
  set B : ℝ := (9 : ℝ) ^ εA * C_tube with hB_def
  have h9_pos : (0 : ℝ) < 9 := by norm_num
  have hB_pos : 0 < B := by positivity
  set δR : ℝ := Real.rpow B (-(1 / α)) with hδR_def
  have hδR_pos : 0 < δR := Real.rpow_pos_of_pos hB_pos _

  have h_rpow_mul : Real.rpow δR α = B⁻¹ := by
    have h_log1 : Real.log (Real.rpow B (-(1 / α))) = (-(1 / α)) * Real.log B :=
      Real.log_rpow hB_pos _
    have h_log2 : Real.log (Real.rpow δR α) = α * Real.log δR :=
      Real.log_rpow hδR_pos _
    have h_log3 : Real.log (Real.rpow δR α) = - Real.log B := by
      rw [h_log2, hδR_def, h_log1]
      have h_simp : α * (-(1 / α) * Real.log B) = - Real.log B := by
        have hα_ne : α ≠ 0 := hα_pos.ne'
        field_simp [hα_ne] <;> ring
      exact h_simp
    have h_log4 : Real.log (B⁻¹) = - Real.log B := by
      rw [Real.log_inv] <;> linarith
    have h_pos1 : 0 < Real.rpow δR α := Real.rpow_pos_of_pos hδR_pos _
    have h_pos2 : 0 < B⁻¹ := by positivity
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr h_pos1) (Set.mem_Ioi.mpr h_pos2)
      (by rw [h_log3, h_log4])

  have hB_inv_eq : B⁻¹ = (9 : ℝ) ^ (-εA) / C_tube := by
    dsimp only [B]
    have h9_pos' : (0 : ℝ) < 9 := by norm_num
    have h_pos : 0 < (9 : ℝ) ^ εA := Real.rpow_pos_of_pos h9_pos' _
    have h_mul : ((9 : ℝ) ^ εA * C_tube)⁻¹ = ((9 : ℝ) ^ εA)⁻¹ / C_tube := by
      field_simp [h_pos.ne', hC_tube_pos.ne'] <;> ring
    rw [h_mul]
    have h_inv : ((9 : ℝ) ^ εA)⁻¹ = (9 : ℝ) ^ (-εA) := by
      have h1 : (9 : ℝ) ^ εA * (9 : ℝ) ^ (-εA) = 1 := by
        have h2 := Real.rpow_add h9_pos' εA (-εA)
        have h3 : εA + (-εA) = 0 := by ring
        rw [h3] at h2
        have h4 : (9 : ℝ) ^ (0 : ℝ) = 1 := by simp
        rw [h4] at h2
        exact h2.symm
      field_simp [h_pos.ne'] <;> linarith
    rw [h_inv] <;> ring

  refine' ⟨δR, hδR_pos, _⟩
  intro δ hδ_pos hδ_le
  have h5 : Real.rpow δ α ≤ Real.rpow δR α :=
    Real.rpow_le_rpow hδ_pos.le hδ_le hα_pos.le
  rw [h_rpow_mul, hB_inv_eq] at h5
  exact h5

/-- Integrated transfer with all sub-conditions discharged.

    Discharges:
    - All 4 absorption conditions (via h_small + absorption_all)
    - Ncover comparison (via cobalt's WideCenterLine.ncover_image_le_of_incidence)
    - Tube S-set transfer (via tube_sset_transfer_set + indigo's finite adapter)

    Requires `dyadicDelta j ≤ 1/2` for cobalt's offset bound.
    Requires `dyadicDelta j ≤ (√2-1)/4` for intercept bound ≤3.
    Requires `C_tube = 381790 * 176^s ≥ 361` for absorption. -/
lemma uniform_wide_transfer_with_absorption
    {s t εA ε_inc C_tube : ℝ} (j : ℕ)
    (hεA_pos : 0 < εA)
    (hε_inc_pos : 0 < ε_inc)
    (hε_inc_lt : ε_inc < εA)
    (hs : 0 ≤ s)
    (hs1 : s < 1)
    (hδ_small : dyadicDelta j ≤ (Real.sqrt 2 - 1) / 4)
    (hC_tube_eq : C_tube = 381790 * (176 : ℝ) ^ s)
    (hC_tube_pos : 0 < C_tube)
    (hC_tube_ge : (361 : ℝ) ≤ C_tube)
    (δR_thin : ℝ)
    (h_body : RegularIncidenceBody (fun ℓ : AffineLine => ℓ.1) s t εA εA δR_thin)
    (δR : ℝ)
    (hδR_pos : 0 < δR)
    (hδR_one : δR ≤ 1)
    (h_threshold : 9 * δR ≤ δR_thin)
    (hδ_half : dyadicDelta j ≤ 1 / 2)
    -- Uniform small-δ bound for absorption
    (h_small : ∀ δ, 0 < δ → δ ≤ δR →
        Real.rpow δ (εA - ε_inc) ≤ (9 : ℝ) ^ (-εA) / C_tube) :
    dyadicDelta j ≤ δR →
    RegularIncidenceAtScale (canonicalWideCarrier j) s t ε_inc ε_inc (dyadicDelta j) := by
  -- Derive all 4 absorption conditions
  have h_abs := absorption_all (t := t) (hεA_pos := hεA_pos) (hε_inc_pos := hε_inc_pos)
    (hε_inc_lt := hε_inc_lt) (hs1 := hs1)
    (hC_tube_pos := hC_tube_pos) (hC_tube_ge := hC_tube_ge) (h_small := h_small)
  rcases h_abs with ⟨h_absorb_tube, h_absorb_point, h_absorb_sqrt, h_absorb_output⟩

  -- Construct Ncover transfer from cobalt's lemma
  have h_ncover_transfer : ∀ (F : Set (DyadicTube j)) (P : Set Plane)
      (hP : P ⊆ Metric.closedBall 0 1)
      (h_inc : ∀ T ∈ F, ∃ p ∈ P, p ∈ Metric.cthickening (dyadicDelta j) (canonicalWideCarrier j T)),
      Ncover (9 * dyadicDelta j) (wideToAffineLine '' F) ≤ Ncover (dyadicDelta j) F := by
    intro F P hP h_inc
    have h_eq : wideToAffineLine = WideCenterLine.wideCenterLine j := by
      funext T
      exact wideToAffineLine_eq_wideCenterLine j T
    rw [h_eq]
    exact WideCenterLine.ncover_image_le_of_incidence hP hδ_half h_inc

  -- Use the core lemma (h_sset_scale discharged via kestrel + indigo)
  intro hδj_le
  exact uniform_wide_transfer_at_scale j hεA_pos hε_inc_pos hε_inc_lt
    hs hs1 hδ_small hC_tube_eq
    δR_thin h_body δR hδR_pos hδR_one h_threshold
    h_ncover_transfer
    (fun P δ u C hδ hP_bdd h => point_sset_scale hδ hP_bdd h)
    h_absorb_tube h_absorb_point h_absorb_sqrt h_absorb_output hδj_le

/-- Full carrier transfer with automatic δR selection.

    Produces δR > 0 satisfying absorption conditions, δR ≤ 1, and 9*δR ≤ δR_thin.
    The transfer holds for any j with dyadicDelta j ≤ δR.

    Tube S-set transfer is fully discharged (requires hδ_small and C_tube = 381790 * 176^s). -/
lemma uniform_wide_transfer_auto_deltaR
    {s t εA ε_inc C_tube : ℝ} (j : ℕ)
    (hεA_pos : 0 < εA)
    (hε_inc_pos : 0 < ε_inc)
    (hε_inc_lt : ε_inc < εA)
    (hs : 0 ≤ s)
    (hs1 : s < 1)
    (hδ_small : dyadicDelta j ≤ (Real.sqrt 2 - 1) / 4)
    (hC_tube_eq : C_tube = 381790 * (176 : ℝ) ^ s)
    (hC_tube_pos : 0 < C_tube)
    (hC_tube_ge : (361 : ℝ) ≤ C_tube)
    (δR_thin : ℝ)
    (hδR_thin_pos : 0 < δR_thin)
    (h_body : RegularIncidenceBody (fun ℓ : AffineLine => ℓ.1) s t εA εA δR_thin)
    (hδ_half : dyadicDelta j ≤ 1 / 2) :
    ∃ (δR : ℝ), 0 < δR ∧ δR ≤ 1 ∧ 9 * δR ≤ δR_thin ∧
      (dyadicDelta j ≤ δR →
        RegularIncidenceAtScale (canonicalWideCarrier j) s t ε_inc ε_inc (dyadicDelta j)) := by
  rcases exists_absorption_deltaR hεA_pos hε_inc_pos hε_inc_lt hC_tube_pos
    with ⟨δR0, hδR0_pos, h_small0⟩
  let δR : ℝ := min δR0 (min 1 (δR_thin / 9))
  have hδR_pos : 0 < δR := by
    have h1 : 0 < δR0 := hδR0_pos
    have h2 : (0 : ℝ) < 1 := by norm_num
    have h3 : 0 < δR_thin / 9 := by positivity
    positivity
  have hδR_one : δR ≤ 1 := by
    have h : δR ≤ min 1 (δR_thin / 9) := min_le_right _ _
    exact le_trans h (min_le_left _ _)
  have h_threshold : 9 * δR ≤ δR_thin := by
    have h : δR ≤ min 1 (δR_thin / 9) := min_le_right _ _
    have h2 : δR ≤ δR_thin / 9 := le_trans h (min_le_right _ _)
    linarith
  have h_small : ∀ δ, 0 < δ → δ ≤ δR →
      Real.rpow δ (εA - ε_inc) ≤ (9 : ℝ) ^ (-εA) / C_tube := by
    intro δ hδ hδ_le
    have hδ_le0 : δ ≤ δR0 := le_trans hδ_le (min_le_left _ _)
    exact h_small0 δ hδ hδ_le0
  refine' ⟨δR, hδR_pos, hδR_one, h_threshold, _⟩
  exact uniform_wide_transfer_with_absorption j hεA_pos hε_inc_pos hε_inc_lt
    hs hs1 hδ_small hC_tube_eq hC_tube_pos hC_tube_ge
    δR_thin h_body δR hδR_pos hδR_one h_threshold hδ_half h_small

/-- Uniform carrier transfer for ALL scales j with dyadicDelta j ≤ δR.

    Chooses δR ≤ (√2-1)/4 so the intercept bound and tube adapter hold,
    and δR ≤ 1/2 so the cobalt offset bound holds automatically.
    Produces exactly the `h_body` field of `UniformIncidenceData`. -/
lemma uniform_wide_transfer_uniform_all_j
    {s t εA ε_inc C_tube : ℝ}
    (hεA_pos : 0 < εA)
    (hε_inc_pos : 0 < ε_inc)
    (hε_inc_lt : ε_inc < εA)
    (hs : 0 ≤ s)
    (hs1 : s < 1)
    (hC_tube_eq : C_tube = 381790 * (176 : ℝ) ^ s)
    (hC_tube_pos : 0 < C_tube)
    (hC_tube_ge : (361 : ℝ) ≤ C_tube)
    (δR_thin : ℝ)
    (hδR_thin_pos : 0 < δR_thin)
    (h_body : RegularIncidenceBody (fun ℓ : AffineLine => ℓ.1) s t εA εA δR_thin) :
    ∃ (δR : ℝ), 0 < δR ∧ δR ≤ 1 ∧
      (∀ (j : ℕ), dyadicDelta j ≤ δR →
        RegularIncidenceAtScale (canonicalWideCarrier j) s t ε_inc ε_inc (dyadicDelta j)) := by
  rcases exists_absorption_deltaR hεA_pos hε_inc_pos hε_inc_lt hC_tube_pos
    with ⟨δR0, hδR0_pos, h_small0⟩
  let δR : ℝ := min δR0 (min ((Real.sqrt 2 - 1) / 4) (min (1 / 2) (min 1 (δR_thin / 9))))
  have hδR_pos : 0 < δR := by
    have h1 : 0 < δR0 := hδR0_pos
    have h2 : (0 : ℝ) < (Real.sqrt 2 - 1) / 4 := by
      have h_sqrt2_gt_one : (1 : ℝ) < Real.sqrt 2 := by
        apply Real.lt_sqrt_of_sq_lt <;> norm_num
      linarith
    have h3 : (0 : ℝ) < 1 / 2 := by norm_num
    have h4 : (0 : ℝ) < 1 := by norm_num
    have h5 : 0 < δR_thin / 9 := by positivity
    positivity
  have hδR_one : δR ≤ 1 := by
    have h : δR ≤ min ((Real.sqrt 2 - 1) / 4) (min (1 / 2) (min 1 (δR_thin / 9))) := min_le_right _ _
    have h2 : δR ≤ min (1 / 2) (min 1 (δR_thin / 9)) := le_trans h (min_le_right _ _)
    have h3 : δR ≤ min 1 (δR_thin / 9) := le_trans h2 (min_le_right _ _)
    exact le_trans h3 (min_le_left _ _)
  have hδR_half : δR ≤ 1 / 2 := by
    have h : δR ≤ min ((Real.sqrt 2 - 1) / 4) (min (1 / 2) (min 1 (δR_thin / 9))) := min_le_right _ _
    have h2 : δR ≤ min (1 / 2) (min 1 (δR_thin / 9)) := le_trans h (min_le_right _ _)
    exact le_trans h2 (min_le_left _ _)
  have hδR_small : δR ≤ (Real.sqrt 2 - 1) / 4 := by
    have h : δR ≤ min ((Real.sqrt 2 - 1) / 4) (min (1 / 2) (min 1 (δR_thin / 9))) := min_le_right _ _
    exact le_trans h (min_le_left _ _)
  have h_threshold : 9 * δR ≤ δR_thin := by
    have h : δR ≤ min ((Real.sqrt 2 - 1) / 4) (min (1 / 2) (min 1 (δR_thin / 9))) := min_le_right _ _
    have h2 : δR ≤ min (1 / 2) (min 1 (δR_thin / 9)) := le_trans h (min_le_right _ _)
    have h3 : δR ≤ min 1 (δR_thin / 9) := le_trans h2 (min_le_right _ _)
    have h4 : δR ≤ δR_thin / 9 := le_trans h3 (min_le_right _ _)
    linarith
  have h_small : ∀ δ, 0 < δ → δ ≤ δR →
      Real.rpow δ (εA - ε_inc) ≤ (9 : ℝ) ^ (-εA) / C_tube := by
    intro δ hδ hδ_le
    have hδ_le0 : δ ≤ δR0 := le_trans hδ_le (min_le_left _ _)
    exact h_small0 δ hδ hδ_le0
  refine' ⟨δR, hδR_pos, hδR_one, _⟩
  intro j hδj_le
  have hδ_half : dyadicDelta j ≤ 1 / 2 := le_trans hδj_le hδR_half
  have hδ_small : dyadicDelta j ≤ (Real.sqrt 2 - 1) / 4 := le_trans hδj_le hδR_small
  exact uniform_wide_transfer_with_absorption j hεA_pos hε_inc_pos hε_inc_lt
    hs hs1 hδ_small hC_tube_eq hC_tube_pos hC_tube_ge
    δR_thin h_body δR hδR_pos hδR_one h_threshold hδ_half h_small hδj_le

end DirecretisedFurstenbergEstimate.CarrierTransfer

end
