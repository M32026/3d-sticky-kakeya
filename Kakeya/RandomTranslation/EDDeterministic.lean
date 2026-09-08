/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.EDChernoffNet
public import Kakeya.Tube.EDUpToMult

/-!
# Deterministic ED-multiplicity for translate families

The ED half of the `randCF` construction ([GWZ, Lemma 3.8], proved in
`Kakeya/RandomTranslation/RandCF.lean`) currently routes through a Chernoff
tail bound over the testing net of `Kakeya/RandomTranslation/EDChernoffNet.lean`.
That route is lossy: the Chernoff denominator it uses is the *pointwise* thin-box
packing cap `C_pack`, so `Kakeya.Probability.lemma_A1_case_lt` forces the
threshold `M_ED` to exceed `J · C_pack`, and the surviving cap is then
`M_dim · M_inner`, i.e. *quadratic* in `J · C_pack`.

This file records the deterministic bound that the same packing input already
gives, with no probability at all and no net:

* `Kakeya.volume_cthickening_tube_le_netVolThin` — the thin-volume bound
  `vol(cthickening (99·δ) T.carrier) ≤ netVolThinConstantM E · δ^(n-1)` for
  *every* `δ`-tube whose midpoint lies in `B(0, 2)`, not just for members of the
  net produced by `Kakeya.exists_thin_tube_net`.  This is what removes the need
  for a net on the ED side: the reference body can be taken to be the tube under
  consideration itself.

* `Kakeya.isEDUpToMult_translate_product_of_thinBox_pack` — for *any* family of
  translation vectors `v : Fin J → E` in the unit ball, the `J`-fold translate
  family `(i, j) ↦ (T i).translate (v j)` of a pairwise essentially distinct
  family in `B(0, 1)` is essentially distinct up to multiplicity `J · C_pack`.

The cap `J · C_pack` is linear in `J`, against the quadratic cap the Chernoff
route yields, and it is sharp in its `J`-dependence: taking all `v j` equal makes
the translate family `J` literal copies of a single family, so no bound below `J`
can hold for all `v`.  See the module docstring of
`Kakeya/RandomTranslation/RandCF.lean` for how the cap is consumed.
-/

@[expose] public section

open MeasureTheory Metric

namespace Kakeya

section EDDeterministic

universe u v

variable
  (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A tube whose carrier lies in `B(0, r)` has midpoint of norm at most `r`. -/
lemma norm_midpoint_le_of_carrier_subset [ProperSpace E]
    {δ : NNReal} (T : Tube δ E) {r : ℝ}
    (h : T.carrier ⊆ Metric.closedBall (0 : E) r) : ‖T.midpoint‖ ≤ r := by
  have hmid_in_seg : T.midpoint ∈ segment ℝ T.x T.y := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    simp only [Tube.midpoint, smul_add]
  have hmid_in_carrier : T.midpoint ∈ T.carrier := by
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨T.midpoint, hmid_in_seg, Metric.mem_closedBall_self δ.coe_nonneg⟩
  have hmid_ball := h hmid_in_carrier
  rw [Metric.mem_closedBall, dist_zero_right] at hmid_ball
  exact hmid_ball

/-- **Universal thin-volume bound for tubes.**

The `99·δ`-cthickening of any `δ`-tube with midpoint in `B(0, 2)` has volume at
most `netVolThinConstantM E · δ^(n-1)`.

This is the per-member volume property of `Kakeya.exists_thin_tube_net` stated
for an arbitrary tube.  Nothing about membership in a net is used: the bound
comes from `Kakeya.Tube.volume_cthickening_unit_segment_le` applied to the tube's
own unit core segment when `δ ≤ 1/100`, and from the crude bound
`vol(B(0, 200))` otherwise.

The hypothesis `δ < 1` is not removable: the `99·δ`-cthickening contains a ball
of radius `100·δ` about `T.x`, whose volume grows like `δ^n`, so the bound
`≲ δ^(n-1)` fails for large `δ`. -/
lemma volume_cthickening_tube_le_netVolThin [Nontrivial E] [ProperSpace E]
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ < 1) (T : Tube δ E) (hmid : ‖T.midpoint‖ ≤ 2) :
    volume (Metric.cthickening (99 * (δ : ℝ)) T.carrier)
      ≤ ENNReal.ofReal (netVolThinConstantM E) *
        (δ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
  classical
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδR1 : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  set n := Module.finrank ℝ E with hn_def
  have _hn : 0 < Module.finrank ℝ E := Module.finrank_pos
  -- Brick 3: volume bound on unit segments.
  set C_vol : ℝ := (Kakeya.Tube.unitSegmentCthickeningVolumeConstant E : ℝ)
    with hC_vol_def
  have hC_vol_pos : 0 < C_vol := by
    rw [hC_vol_def]
    exact NNReal.coe_pos.mpr (Kakeya.Tube.unitSegmentCthickeningVolumeConstant_pos E)
  have hvol : ∀ (x y : E), dist x y = 1 →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        volume.real (Metric.cthickening r (segment ℝ x y)) ≤
          C_vol * r ^ (Module.finrank ℝ E - 1) := by
    intro x y hxy r hr hr1
    have hr_coe : ((r.toNNReal : NNReal) : ℝ) = r := Real.coe_toNNReal r hr.le
    have hrN_le_one : r.toNNReal ≤ 1 := by
      rw [← NNReal.coe_le_coe, hr_coe]; exact hr1
    have h := Kakeya.Tube.volume_cthickening_unit_segment_le
      E x y hxy r.toNNReal hrN_le_one
    have hRHS_fin :
        (Kakeya.Tube.unitSegmentCthickeningVolumeConstant E : ENNReal) *
            (r.toNNReal : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hreal := ENNReal.toReal_mono hRHS_fin h
    simpa [Measure.real, hC_vol_def, hr_coe, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.coe_toReal] using hreal
  have hTdist : dist T.x T.y = 1 := T.dist_eq_one
  have hT_carrier_cth : T.carrier = Metric.cthickening (δ : ℝ) (segment ℝ T.x T.y) := by
    rw [T.carrier_eq]
    have hseg_closed : IsClosed (segment ℝ T.x T.y) := by
      rw [segment_eq_image']
      exact (isCompact_Icc.image (by fun_prop)).isClosed
    rw [hseg_closed.cthickening_eq_biUnion_closedBall hδR.le]
  have h99_nn : (0 : ℝ) ≤ 99 * (δ : ℝ) := by positivity
  have h_subset_cth :
      Metric.cthickening (99 * (δ : ℝ)) T.carrier ⊆
        Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y) := by
    rw [hT_carrier_cth]
    have h1 : Metric.cthickening (99 * (δ : ℝ))
          (Metric.cthickening (δ : ℝ) (segment ℝ T.x T.y)) ⊆
        Metric.cthickening (99 * (δ : ℝ) + (δ : ℝ)) (segment ℝ T.x T.y) :=
      Metric.cthickening_cthickening_subset h99_nn hδR.le _
    have h_eq : (99 * (δ : ℝ) + (δ : ℝ)) = 100 * (δ : ℝ) := by ring
    rw [h_eq] at h1; exact h1
  have hseg_compact : IsCompact (segment ℝ T.x T.y) := by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  have h_cth_fin : volume (Metric.cthickening (100 * δ) (segment ℝ T.x T.y)) ≠ ⊤ :=
    hseg_compact.cthickening.measure_lt_top.ne
  have h_meas_mono : volume.real (Metric.cthickening (99 * (δ : ℝ)) T.carrier) ≤
      volume.real (Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y)) :=
    measureReal_mono h_subset_cth h_cth_fin
  have hvol_seg_bd :
      volume.real (Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y)) ≤
        netVolThinConstantM E * (δ : ℝ) ^ (n - 1) := by
    by_cases hδ_small : (δ : ℝ) ≤ 1 / 100
    · have h100δ_pos : 0 < 100 * (δ : ℝ) := by positivity
      have h100δ_le : 100 * (δ : ℝ) ≤ 1 := by linarith
      have hvol_brick : volume.real (Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y))
          ≤ C_vol * (100 * (δ : ℝ)) ^ (n - 1) :=
        hvol T.x T.y hTdist (100 * (δ : ℝ)) h100δ_pos h100δ_le
      have h_split : (100 * (δ : ℝ)) ^ (n - 1) = 100 ^ (n - 1) * (δ : ℝ) ^ (n - 1) :=
        mul_pow _ _ _
      have h100_nn : (0 : ℝ) ≤ 100 ^ (n - 1) := by positivity
      have hδpow_nn : (0 : ℝ) ≤ (δ : ℝ) ^ (n - 1) := by positivity
      have h100_n_pow_ge : (100 : ℝ) ^ (n - 1) ≤ 100 ^ n := by
        apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 100)
        omega
      have h_C_vol_pos : 0 ≤ C_vol := hC_vol_pos.le
      have hstep1 : C_vol * (100 * (δ : ℝ)) ^ (n - 1) ≤
          C_vol * 100 ^ n * (δ : ℝ) ^ (n - 1) := by
        rw [h_split]
        calc C_vol * (100 ^ (n - 1) * (δ : ℝ) ^ (n - 1))
            = (C_vol * 100 ^ (n - 1)) * (δ : ℝ) ^ (n - 1) := by ring
          _ ≤ (C_vol * 100 ^ n) * (δ : ℝ) ^ (n - 1) := by
              apply mul_le_mul_of_nonneg_right _ hδpow_nn
              exact mul_le_mul_of_nonneg_left h100_n_pow_ge h_C_vol_pos
      have hC_vol_le : C_vol * 100 ^ n ≤ netVolThinConstantM E := by
        unfold netVolThinConstantM
        rw [dif_pos _hn]
        have h_vol_ball_nn : 0 ≤ MeasureTheory.volume.real (Metric.closedBall (0 : E) 200) *
            100 ^ Module.finrank ℝ E := by
          apply mul_nonneg MeasureTheory.measureReal_nonneg; positivity
        change C_vol * 100 ^ n ≤
          MeasureTheory.volume.real (Metric.closedBall (0 : E) 200) *
              100 ^ Module.finrank ℝ E +
            (Kakeya.Tube.unitSegmentCthickeningVolumeConstant E : ℝ) *
              100 ^ Module.finrank ℝ E + 1
        rw [← hC_vol_def]
        have hn_eq : (n : ℕ) = Module.finrank ℝ E := hn_def
        rw [hn_eq]
        linarith
      have h_C_vol_le' : C_vol * 100 ^ n * (δ : ℝ) ^ (n - 1) ≤
          netVolThinConstantM E * (δ : ℝ) ^ (n - 1) :=
        mul_le_mul_of_nonneg_right hC_vol_le hδpow_nn
      linarith
    · push Not at hδ_small
      have hseg_in_ball :
          segment ℝ T.x T.y ⊆ Metric.closedBall (T.midpoint : E) (1/2) := by
        intro z hz
        obtain ⟨a, b, ha, hb, hab, hz_eq⟩ := hz
        have h_dir_norm : ‖T.direction‖ = 1 := by
          have := T.dist_eq_one
          rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
        have hz_alt : z = T.midpoint + (b - 1/2) • T.direction := by
          rw [← hz_eq]
          simp only [Tube.midpoint, Tube.direction]
          have hab' : a = 1 - b := by linarith
          rw [hab']
          module
        rw [Metric.mem_closedBall, dist_eq_norm, hz_alt]
        have h_dist : z - T.midpoint = (b - 1/2) • T.direction := by
          rw [hz_alt]; abel
        have h_dist_norm : ‖(b - 1/2) • T.direction‖ = |b - 1/2| := by
          rw [norm_smul, h_dir_norm, mul_one, Real.norm_eq_abs]
        have h_abs : |b - 1/2| ≤ 1/2 := by
          rw [abs_le]; constructor <;> nlinarith
        have h_simp : T.midpoint + (b - 1/2) • T.direction - T.midpoint
            = (b - 1/2) • T.direction := by abel
        calc ‖T.midpoint + (b - 1/2) • T.direction - T.midpoint‖
            = ‖(b - 1/2) • T.direction‖ := by rw [h_simp]
          _ = |b - 1/2| := h_dist_norm
          _ ≤ 1/2 := h_abs
      have h_cth_in_ball :
          Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y) ⊆
            Metric.cthickening (100 * (δ : ℝ)) (Metric.closedBall (T.midpoint : E) (1/2)) :=
        Metric.cthickening_subset_of_subset _ hseg_in_ball
      have h_cth_ball :
          Metric.cthickening (100 * (δ : ℝ)) (Metric.closedBall (T.midpoint : E) (1/2))
            = Metric.closedBall T.midpoint (100 * (δ : ℝ) + 1/2) := by
          rw [cthickening_closedBall (by positivity) (by norm_num)]
      have h100δ_le : 100 * (δ : ℝ) ≤ 100 := by linarith
      have h_radius_le : (100 * (δ : ℝ) + 1/2) ≤ 100 + 1/2 := by linarith
      have h_ball_in_big :
          Metric.closedBall (T.midpoint : E) (100 * (δ : ℝ) + 1/2) ⊆
            Metric.closedBall (0 : E) 200 := by
        intro x hx
        rw [Metric.mem_closedBall] at hx ⊢
        calc dist x (0 : E)
            ≤ dist x T.midpoint + dist T.midpoint 0 := dist_triangle _ _ _
          _ ≤ (100 * (δ : ℝ) + 1/2) + ‖T.midpoint‖ := by
              rw [dist_zero_right]; linarith
          _ ≤ 100 + 1/2 + 2 := by linarith
          _ ≤ 200 := by norm_num
      have h_full_sub :
          Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y)
            ⊆ Metric.closedBall (0 : E) 200 := by
        calc Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y)
            ⊆ Metric.cthickening (100 * (δ : ℝ))
                (Metric.closedBall (T.midpoint : E) (1/2)) := h_cth_in_ball
          _ = Metric.closedBall (T.midpoint : E) (100 * (δ : ℝ) + 1/2) := h_cth_ball
          _ ⊆ Metric.closedBall (0 : E) 200 := h_ball_in_big
      have hfin : volume (Metric.closedBall (0 : E) 200) ≠ ⊤ :=
        MeasureTheory.measure_closedBall_lt_top.ne
      have h_vol_le_ball :
          volume.real (Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y)) ≤
            volume.real (Metric.closedBall (0 : E) 200) :=
        measureReal_mono h_full_sub hfin
      have h_vol_ball_nn : 0 ≤ volume.real (Metric.closedBall (0 : E) 200) :=
        MeasureTheory.measureReal_nonneg
      have hδ_inv : (1 : ℝ) / 100 < (δ : ℝ) := hδ_small
      have h100δ_ge : (100 * (δ : ℝ) : ℝ) > 1 := by linarith
      have h_pow_ge : (100 * (δ : ℝ)) ^ (n - 1) ≥ 1 := by
        apply one_le_pow₀
        linarith
      have h_pow_eq : (100 * (δ : ℝ)) ^ (n - 1) = 100 ^ (n - 1) * (δ : ℝ) ^ (n - 1) :=
        mul_pow _ _ _
      have hδpow_nn : 0 ≤ (δ : ℝ) ^ (n - 1) := by positivity
      have h100pow_nn : 0 ≤ (100 : ℝ) ^ (n - 1) := by positivity
      have h_factor :
          (1 : ℝ) ≤ 100 ^ n * (δ : ℝ) ^ (n - 1) := by
        have h_step : (100 : ℝ) ^ n * (δ : ℝ) ^ (n - 1) =
            100 * (100 ^ (n - 1) * (δ : ℝ) ^ (n - 1)) := by
          rw [show (100 : ℝ) ^ n = 100 * 100 ^ (n - 1) from by
            rw [mul_comm, ← pow_succ, Nat.sub_add_cancel _hn]]
          ring
        rw [h_step]
        have h100ge1 : (1 : ℝ) ≤ 100 := by norm_num
        have h_prod : (1 : ℝ) ≤ 100 ^ (n - 1) * (δ : ℝ) ^ (n - 1) := by
          rw [← h_pow_eq]; exact h_pow_ge
        nlinarith
      have h_main :
          volume.real (Metric.closedBall (0 : E) 200) ≤
            volume.real (Metric.closedBall (0 : E) 200) * 100 ^ n * (δ : ℝ) ^ (n - 1) := by
        have hmul : volume.real (Metric.closedBall (0 : E) 200) * 1 ≤
            volume.real (Metric.closedBall (0 : E) 200) * (100 ^ n * (δ : ℝ) ^ (n - 1)) :=
          mul_le_mul_of_nonneg_left h_factor h_vol_ball_nn
        rw [mul_one] at hmul
        calc volume.real (Metric.closedBall (0 : E) 200) ≤ _ := hmul
          _ = volume.real (Metric.closedBall (0 : E) 200) * 100 ^ n
                * (δ : ℝ) ^ (n - 1) := by ring
      have h_ball_le : volume.real (Metric.closedBall (0 : E) 200) * 100 ^ n ≤
          netVolThinConstantM E := by
        unfold netVolThinConstantM
        rw [dif_pos _hn]
        have h_other_nn : 0 ≤
            (Kakeya.Tube.unitSegmentCthickeningVolumeConstant E : ℝ) *
              100 ^ Module.finrank ℝ E := by
          apply mul_nonneg
          · exact NNReal.coe_nonneg _
          · positivity
        change volume.real (Metric.closedBall (0 : E) 200) * 100 ^ n ≤
          volume.real (Metric.closedBall (0 : E) 200) * 100 ^ Module.finrank ℝ E +
            (Kakeya.Tube.unitSegmentCthickeningVolumeConstant E : ℝ) *
              100 ^ Module.finrank ℝ E + 1
        have hn_eq : (n : ℕ) = Module.finrank ℝ E := hn_def
        rw [hn_eq]
        linarith
      calc volume.real (Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y))
          ≤ volume.real (Metric.closedBall (0 : E) 200) := h_vol_le_ball
        _ ≤ volume.real (Metric.closedBall (0 : E) 200) * 100 ^ n
              * (δ : ℝ) ^ (n - 1) := h_main
        _ ≤ netVolThinConstantM E * (δ : ℝ) ^ (n - 1) := by
            apply mul_le_mul_of_nonneg_right h_ball_le hδpow_nn
  have hreal_final :
      volume.real (Metric.cthickening (99 * (δ : ℝ)) T.carrier) ≤
        netVolThinConstantM E * (δ : ℝ) ^ (n - 1) :=
    h_meas_mono.trans hvol_seg_bd
  have hLHS_fin : volume (Metric.cthickening (99 * (δ : ℝ)) T.carrier) ≠ ⊤ :=
    ne_top_of_le_ne_top h_cth_fin (measure_mono h_subset_cth)
  have hRHS_fin : ENNReal.ofReal (netVolThinConstantM E) *
      (δ : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  refine (ENNReal.toReal_le_toReal hLHS_fin hRHS_fin).mp ?_
  simpa [Measure.real, hn_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (netVolThinConstantM_pos (E := E)).le,
    ENNReal.coe_toReal] using hreal_final

/-- **Deterministic ED-multiplicity bound for a translate family.**

Let `T : ι → Tube δ E` be a pairwise essentially distinct family of tubes in
`B(0, 1)` with volumes between `c_vol · δ^(n-1)` and `M_vol · δ^(n-1)`, and let
`C_pack` be a thin-box ED packing cap for it, i.e. for every reference tube in
`B(0, 7/2)` with thin `99·δ`-cthickening, at most `C_pack` members of the family
are `BadAgainstSet` that cthickening at density `c_vol / (2 · M_vol)` after any
single translation.

Then for **any** translation vectors `v : Fin J → E` in the closed unit ball the
`J`-fold translate family is essentially distinct up to multiplicity `J · C_pack`.

No probability is used.  The reference body for the index `p₀` is the translate
`(T p₀.1).translate (v p₀.2)` itself, whose thin-volume bound is
`Kakeya.volume_cthickening_tube_le_netVolThin`; the packing cap is then applied once per
translation index `j` and the `J` results are summed. -/
theorem isEDUpToMult_translate_product_of_thinBox_pack
    [Nontrivial E] [ProperSpace E]
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ < 1)
    {c_vol M_vol : ℝ} (hc_vol_pos : 0 < c_vol) (hM_vol_pos : 0 < M_vol)
    (C_pack : ℕ)
    {ι : Type v} (s : Finset ι) (T : ι → Tube δ E)
    (hT_ball : ∀ i, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hT_vol_lb : ∀ i ∈ s,
      c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤ volume.real (T i).carrier)
    (hT_vol_ub : ∀ i ∈ s,
      volume.real (T i).carrier ≤ M_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1))
    (hThinBox_pack : ∀ (T₀' : Tube δ E),
      T₀'.carrier ⊆ Metric.closedBall (0 : E) (7 / 2) →
      volume (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
          ≤ ENNReal.ofReal (netVolThinConstantM E) *
            (δ : ENNReal) ^ (Module.finrank ℝ E - 1) →
      ∀ v : E,
        (@Finset.filter ι
            (fun i => BadAgainstSet ((T i).translate v)
              (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
              (c_vol / (2 * M_vol)))
            (Classical.decPred _) s).card ≤ C_pack)
    {J : ℕ} (v : Fin J → E) (hv : ∀ j, ‖v j‖ ≤ 1) :
    IsEDUpToMult (s ×ˢ (Finset.univ : Finset (Fin J)))
      (fun p : ι × Fin J => ((T p.1).translate (v p.2)).carrier) (J * C_pack) := by
  classical
  set V_lb : ℝ := c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) with hV_lb_def
  set V_ub : ℝ := M_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) with hV_ub_def
  have hV_lb_pos : 0 < V_lb := by
    rw [hV_lb_def]
    exact mul_pos hc_vol_pos (pow_pos (by exact_mod_cast hδ) _)
  have hV_ub_pos : 0 < V_ub := by
    rw [hV_ub_def]
    exact mul_pos hM_vol_pos (pow_pos (by exact_mod_cast hδ) _)
  have hc_bridge_eq : c_vol / (2 * M_vol) = V_lb / (2 * V_ub) := by
    rw [hV_lb_def, hV_ub_def]
    have hM_vol_ne : M_vol ≠ 0 := ne_of_gt hM_vol_pos
    have hp_ne : (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≠ 0 :=
      pow_ne_zero _ (ne_of_gt (by exact_mod_cast hδ))
    field_simp [hM_vol_ne, hp_ne]
  intro p₀ hp₀
  have hp₀_mem : p₀.1 ∈ s ∧ p₀.2 ∈ (Finset.univ : Finset (Fin J)) :=
    Finset.mem_product.mp hp₀
  change (notEssDistinctSet (s ×ˢ (Finset.univ : Finset (Fin J)))
      (fun p : ι × Fin J => ((T p.1).translate (v p.2)).carrier)
      ((T p₀.1).translate (v p₀.2)).carrier).card ≤ J * C_pack
  set T₀' : Tube δ E := (T p₀.1).translate (v p₀.2) with hT₀'_def
  set K_thick : Set E := Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier with hK_thick_def
  have hT₀'_ball : T₀'.carrier ⊆ Metric.closedBall (0 : E) 2 := by
    intro x hx
    rw [hT₀'_def, Tube.translate_carrier] at hx
    rw [Set.mem_preimage] at hx
    have hxv : ‖-(v p₀.2) + x‖ ≤ 1 := by
      have hb := hT_ball p₀.1 hx
      rw [Metric.mem_closedBall, dist_zero_right] at hb
      exact hb
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hbnd : ‖v p₀.2 + (-(v p₀.2) + x)‖ ≤ 2 :=
      (norm_add_le _ _).trans (by linarith [hv p₀.2, hxv])
    rwa [add_neg_cancel_left] at hbnd
  have hT₀'_B72 : T₀'.carrier ⊆ Metric.closedBall (0 : E) (7 / 2) :=
    hT₀'_ball.trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hmid : ‖T₀'.midpoint‖ ≤ 2 :=
    Kakeya.norm_midpoint_le_of_carrier_subset (E := E) T₀' hT₀'_ball
  have hvol_thin : volume (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
      ≤ ENNReal.ofReal (netVolThinConstantM E) *
        (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
    Kakeya.volume_cthickening_tube_le_netVolThin (E := E) hδ hδ1 T₀' hmid
  have hvol_tr : ∀ (i : ι) (w : E), volume.real ((T i).translate w).carrier =
      volume.real (T i).carrier := by
    intro i w
    rw [Tube.translate_carrier]
    change (volume _).toReal = (volume _).toReal
    rw [MeasureTheory.measure_preimage_add]
  have h_per_index : ∀ (j : Fin J) (i : ι), i ∈ s →
      ¬ IsEssentiallyDistinct ((T i).translate (v j)).carrier T₀'.carrier →
        BadAgainstSet ((T i).translate (v j)) K_thick (c_vol / (2 * M_vol)) := by
    intro j i hi_val hnotED
    have hvol_lb_p₀ : V_lb ≤ volume.real T₀'.carrier := by
      rw [hV_lb_def, hT₀'_def, hvol_tr p₀.1 (v p₀.2)]
      exact hT_vol_lb p₀.1 hp₀_mem.1
    have hvol_ub_i : volume.real ((T i).translate (v j)).carrier ≤ V_ub := by
      rw [hV_ub_def, hvol_tr i (v j)]
      exact hT_vol_ub i hi_val
    have hvol_lb_p₀_enn : ENNReal.ofReal V_lb ≤ volume T₀'.carrier := by
      have hfin : volume T₀'.carrier ≠ ⊤ := T₀'.isCompact.measure_lt_top.ne
      calc
        ENNReal.ofReal V_lb ≤ ENNReal.ofReal (volume.real T₀'.carrier) :=
          ENNReal.ofReal_le_ofReal hvol_lb_p₀
        _ = volume T₀'.carrier := ENNReal.ofReal_toReal hfin
    have hvol_ub_i_enn : volume ((T i).translate (v j)).carrier ≤ ENNReal.ofReal V_ub := by
      have hfin : volume ((T i).translate (v j)).carrier ≠ ⊤ :=
        ((T i).translate (v j)).isCompact.measure_lt_top.ne
      calc
        volume ((T i).translate (v j)).carrier =
            ENNReal.ofReal (volume.real ((T i).translate (v j)).carrier) :=
          (ENNReal.ofReal_toReal hfin).symm
        _ ≤ ENNReal.ofReal V_ub := ENNReal.ofReal_le_ofReal hvol_ub_i
    have hTp_sub : T₀'.carrier ⊆ K_thick := by
      rw [hK_thick_def]
      exact Metric.self_subset_cthickening T₀'.carrier
    have hbridge :=
      badAgainstSet_of_notED_subset_cthickening hδ
        ((T i).translate (v j)) T₀' K_thick V_lb V_ub hV_lb_pos hV_ub_pos
        hvol_lb_p₀_enn hvol_ub_i_enn hTp_sub hnotED
    rw [← hc_bridge_eq] at hbridge
    exact hbridge
  set Sfull : Finset (ι × Fin J) :=
    ((s ×ˢ (Finset.univ : Finset (Fin J))).filter
      (fun p : ι × Fin J => BadAgainstSet
        ((T p.1).translate (v p.2))
        K_thick (c_vol / (2 * M_vol)))) with hSfull_def
  have h_sub : notEssDistinctSet (s ×ˢ (Finset.univ : Finset (Fin J)))
        (fun p : ι × Fin J => ((T p.1).translate (v p.2)).carrier)
        T₀'.carrier ⊆ Sfull := by
    intro p hp
    have hp' : p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))) ∧
        ¬ IsEssentiallyDistinct ((T p.1).translate (v p.2)).carrier T₀'.carrier := by
      unfold notEssDistinctSet at hp
      simpa using hp
    obtain ⟨hp_mem, hp_notED⟩ := hp'
    have hi_mem : p.1 ∈ s := (Finset.mem_product.mp hp_mem).1
    have h_bad : BadAgainstSet ((T p.1).translate (v p.2)) K_thick
        (c_vol / (2 * M_vol)) := by
      exact h_per_index p.2 p.1 hi_mem hp_notED
    rw [hSfull_def, Finset.mem_filter]
    exact ⟨hp_mem, h_bad⟩
  have hcard_sub :
      (notEssDistinctSet (s ×ˢ (Finset.univ : Finset (Fin J)))
        (fun p : ι × Fin J => ((T p.1).translate (v p.2)).carrier)
        T₀'.carrier).card ≤ Sfull.card := Finset.card_le_card h_sub
  let fibre : Fin J → Finset ι :=
    fun j => @Finset.filter ι
      (fun i => BadAgainstSet ((T i).translate (v j)) K_thick (c_vol / (2 * M_vol)))
      (Classical.decPred _) s
  have hSfull_card_eq : Sfull.card = ∑ j : Fin J, (fibre j).card := by
    rw [hSfull_def, Finset.card_filter, Finset.sum_product_right]
    exact Finset.sum_congr rfl (fun j _ => (Finset.card_filter _ _).symm)
  have hcard_fibre : ∀ j : Fin J, (fibre j).card ≤ C_pack := by
    intro j
    change (@Finset.filter ι
        (fun i => BadAgainstSet ((T i).translate (v j))
          K_thick (c_vol / (2 * M_vol)))
        (Classical.decPred _) s).card ≤ C_pack
    exact hThinBox_pack T₀' hT₀'_B72 hvol_thin (v j)
  have hsum_le : (∑ j : Fin J, (fibre j).card) ≤ J * C_pack := by
    calc
      (∑ j : Fin J, (fibre j).card) ≤ ∑ _j : Fin J, C_pack :=
        Finset.sum_le_sum (fun j _ => hcard_fibre j)
      _ = J * C_pack := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp
  calc
    (notEssDistinctSet (s ×ˢ (Finset.univ : Finset (Fin J)))
        (fun p : ι × Fin J => ((T p.1).translate (v p.2)).carrier) T₀'.carrier).card
        ≤ Sfull.card := hcard_sub
    _ ≤ J * C_pack := by
      rw [hSfull_card_eq]
      exact hsum_le

end EDDeterministic

end Kakeya
