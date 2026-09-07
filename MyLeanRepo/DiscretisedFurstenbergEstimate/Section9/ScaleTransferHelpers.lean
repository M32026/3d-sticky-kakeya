module

/-
  S-set transfer helpers for Section 9 Step 5.

  Transfers S-sets from normalized scale δ_norm = δ/4 to decomposition scale δ_d = Δ^m.

  Ratio bound: δ_d / δ_norm ≤ 1/Δ = 2^q (since Δ = 2^-q).
  The nearby-power selection is applied to the normalized scale δ_norm = δ/4,
  giving δ_norm ≤ δ_d ≤ (1/Δ)·δ_norm.

  Uses iterated covering doubling:
  - Plane: constant inflates by 9^q
  - AffineLine: constant inflates by Kpack^q

  Whiteprint node: section9 / scale_transfer_helpers
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.NearbyDyadicTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.AffineLineIteratedTransfer
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.NearbyDyadicTransfer
open MainAppendix

/-- Iterated covering doubling for EuclideanPlane:
    Ncover(δ, S) ≤ 9^k * Ncover(2^k · δ, S). -/
lemma plane_covering_doubling_iter (δ : ℝ) (hδ_pos : 0 < δ) (k : ℕ)
    {S : Set EuclideanPlane} :
    Metric.externalCoveringNumber δ.toNNReal S ≤
      (9 : ENNReal)^k * Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal S := by
  induction k with
  | zero => simpa using le_refl _
  | succ k ih =>
    set δ' : ℝ := ((2^k : ℕ) : ℝ) * δ with hδ'_def
    have hδ'_pos : 0 < δ' := by positivity
    have h_eq2 : 2 * δ' = ((2^(k+1) : ℕ) : ℝ) * δ := by
      simp [hδ'_def, pow_succ] <;> ring
    have h_step : Metric.externalCoveringNumber δ'.toNNReal S ≤
        (9 : ENNReal) * Metric.externalCoveringNumber (2 * δ').toNNReal S :=
      plane_covering_doubling hδ'_pos S
    calc Metric.externalCoveringNumber δ.toNNReal S
      ≤ (9 : ENNReal)^k * Metric.externalCoveringNumber δ'.toNNReal S := ih
    _ ≤ (9 : ENNReal)^k * ((9 : ENNReal) * Metric.externalCoveringNumber (2 * δ').toNNReal S) := by
      gcongr <;> exact h_step
    _ = (9 : ENNReal)^(k+1) * Metric.externalCoveringNumber (((2^(k+1) : ℕ) : ℝ) * δ).toNNReal S := by
      have h_eq3 : (2 * δ').toNNReal = (((2^(k+1) : ℕ) : ℝ) * δ).toNNReal := by
        apply NNReal.coe_injective; simp [h_eq2]
      rw [h_eq3]; simp [pow_succ] <;> ring

/-- Iterated S-set transfer for EuclideanPlane:
    if δ ≤ δ_d ≤ 2^k · δ, a (δ,s,C)-set is a (δ_d,s,C·9^k)-set. -/
lemma sset_transfer_coarser_plane_iter
    {δ δ_d s C : ℝ} {P : Set EuclideanPlane}
    (hδ_pos : 0 < δ) (hδ_d_pos : 0 < δ_d)
    (hδ_le_d : δ ≤ δ_d)
    (k : ℕ) (hδ_d_le : δ_d ≤ ((2^k : ℕ) : ℝ) * δ)
    (hs : 0 ≤ s) (hC_pos : 0 < C)
    (hP : IsDeltaSSet δ s C P) :
    IsDeltaSSet δ_d s (C * (9 : ℝ)^k) P := by
  rcases hP with ⟨hP_nonempty, _, _, hs_nonneg, h_main⟩
  have hCK_pos : 0 < C * (9 : ℝ)^k := by positivity
  have hN1 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
      (9 : ENNReal)^k * Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal P :=
    plane_covering_doubling_iter δ hδ_pos k
  have hN2 : Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal P ≤
      Metric.externalCoveringNumber δ_d.toNNReal P := by
    have h_le : ((2^k : ℕ) : ℝ) * δ ≥ δ_d := by exact_mod_cast hδ_d_le
    have h_le' : δ_d.toNNReal ≤ (((2^k : ℕ) : ℝ) * δ).toNNReal := by exact Real.toNNReal_mono hδ_d_le
    exact Metric.externalCoveringNumber_anti h_le'
  have hNcover : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
      (9 : ENNReal)^k * Metric.externalCoveringNumber δ_d.toNNReal P :=
    le_trans hN1 (by gcongr)
  refine' ⟨hP_nonempty, hδ_d_pos, hCK_pos, hs_nonneg, _⟩
  intro x r hr
  have hδ_le_r : δ ≤ r := by linarith
  have h1 : (Metric.externalCoveringNumber δ_d.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) := by
    have h_le : δ.toNNReal ≤ δ_d.toNNReal := by exact Real.toNNReal_mono hδ_le_d
    exact_mod_cast Metric.externalCoveringNumber_anti h_le
  have h2 := h_main x r hδ_le_r
  calc (Metric.externalCoveringNumber δ_d.toNNReal (P ∩ Metric.closedBall x r) : ENNReal)
    ≤ (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) := h1
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h2
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          ((9 : ENNReal)^k * Metric.externalCoveringNumber δ_d.toNNReal P) := by gcongr
    _ = ENNReal.ofReal (C * (9 : ℝ)^k) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ_d.toNNReal P) := by
      have h3 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            ((9 : ENNReal)^k * Metric.externalCoveringNumber δ_d.toNNReal P) =
          (9 : ENNReal)^k * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            Metric.externalCoveringNumber δ_d.toNNReal P := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
      rw [h3]
      have h4 : (9 : ENNReal)^k * ENNReal.ofReal C =
          ENNReal.ofReal ((9 : ℝ)^k * C) := by
        have h41 : (9 : ENNReal)^k = ENNReal.ofReal ((9 : ℝ)^k) := by simp
        rw [h41]
        have h5 : 0 ≤ (9 : ℝ)^k := by positivity
        rw [← ENNReal.ofReal_mul h5]
      rw [h4] <;> ring_nf

/-- Transfer a plane S-set from δ_norm = δ/4 to δ_d = Δ^m.

    Given δ/4 ≤ δ_d ≤ (1/Δ)·(δ/4), we have δ_d/(δ/4) ≤ 1/Δ = 2^q.
    Constant inflates by 9^q. -/
lemma sset_transfer_norm_to_dd_plane
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    {δ δ_d : ℝ} (hδ_pos : 0 < δ) (hδ_d_pos : 0 < δ_d)
    (hδ_norm_le_dd : δ / 4 ≤ δ_d)
    (hδ_d_le_ratio : δ_d ≤ (1 / Δ) * (δ / 4))
    (q : ℕ) (hΔ_eq : Δ = (1 / 2 : ℝ) ^ q)
    {t C : ℝ} (ht : 0 ≤ t) (hC_pos : 0 < C)
    {P : Set EuclideanPlane}
    (hP : IsDeltaSSet (δ / 4) t C P) :
    IsDeltaSSet δ_d t (C * (9 : ℝ)^q) P := by
  have hδ_norm_pos : 0 < δ / 4 := by positivity
  have h_ratio : δ_d ≤ ((2^q : ℕ) : ℝ) * (δ / 4) := by
    have h1 : δ_d ≤ (1 / Δ) * (δ / 4) := hδ_d_le_ratio
    have h2 : (1 / Δ) = ((2^q : ℕ) : ℝ) := by
      rw [hΔ_eq]
      have h3 : 1 / ((1 / 2 : ℝ) ^ q) = ((2^q : ℕ) : ℝ) := by
        have h4 : ((1 / 2 : ℝ) ^ q) * ((2^q : ℕ) : ℝ) = 1 := by
          have h5 : ((1 / 2 : ℝ) ^ q) = (1 : ℝ) / ((2^q : ℕ) : ℝ) := by
            simp [pow_succ] <;> field_simp <;> ring
          rw [h5] <;> field_simp <;> ring
        field_simp [h4] <;> linarith
      exact h3
    rw [h2] at h1
    exact h1
  exact sset_transfer_coarser_plane_iter
    hδ_norm_pos hδ_d_pos hδ_norm_le_dd q h_ratio ht hC_pos hP

/-- Transfer an AffineLine S-set from δ_norm = δ/4 to δ_d = Δ^m.

    Given δ/4 ≤ δ_d ≤ (1/Δ)·(δ/4), we have δ_d/(δ/4) ≤ 1/Δ = 2^q.
    Constant inflates by Kpack^q. -/
lemma sset_transfer_norm_to_dd_affineLine
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    {δ δ_d : ℝ} (hδ_pos : 0 < δ) (hδ_d_pos : 0 < δ_d)
    (hδ_norm_le_dd : δ / 4 ≤ δ_d)
    (hδ_d_le_ratio : δ_d ≤ (1 / Δ) * (δ / 4))
    (q : ℕ) (hΔ_eq : Δ = (1 / 2 : ℝ) ^ q)
    {s C : ℝ} (hs : 0 ≤ s) (hC_pos : 0 < C)
    {T : Set AffineLine}
    (hT : IsDeltaSSet (δ / 4) s C T) :
    IsDeltaSSet δ_d s (C * (affineLine_packing_constant : ℝ)^q) T := by
  have hδ_norm_pos : 0 < δ / 4 := by positivity
  have h_ratio : δ_d ≤ ((2^q : ℕ) : ℝ) * (δ / 4) := by
    have h1 : δ_d ≤ (1 / Δ) * (δ / 4) := hδ_d_le_ratio
    have h2 : (1 / Δ) = ((2^q : ℕ) : ℝ) := by
      rw [hΔ_eq]
      have h3 : 1 / ((1 / 2 : ℝ) ^ q) = ((2^q : ℕ) : ℝ) := by
        have h4 : ((1 / 2 : ℝ) ^ q) * ((2^q : ℕ) : ℝ) = 1 := by
          have h5 : ((1 / 2 : ℝ) ^ q) = (1 : ℝ) / ((2^q : ℕ) : ℝ) := by
            simp [pow_succ] <;> field_simp <;> ring
          rw [h5] <;> field_simp <;> ring
        field_simp [h4] <;> linarith
      exact h3
    rw [h2] at h1
    exact h1
  exact sset_transfer_coarser_affineLine_iter
    hδ_norm_pos hδ_d_pos hδ_norm_le_dd q h_ratio hs hC_pos hT

/-- Exact dyadic logarithm identity: for k : ℕ,
    ceil(log(1/dyadicDelta k) / log 2) = k.
    Since log(1/dyadicDelta k) = k * log 2. -/
lemma ceil_log_dyadicDelta (k : ℕ) :
    Nat.ceil (Real.log (1 / dyadicDelta k) / Real.log 2) = k := by
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_eq : Real.log (1 / dyadicDelta k) = (k : ℝ) * Real.log 2 := by
    have h1 : 1 / dyadicDelta k = (2 : ℝ)^k := by
      simp [dyadicDelta]
      <;> field_simp <;> ring
    rw [h1, Real.log_pow] <;> norm_num
  have h_div : Real.log (1 / dyadicDelta k) / Real.log 2 = (k : ℝ) := by
    rw [h_eq]
    field_simp [h_log2_pos.ne'] <;> ring
  rw [h_div]
  simp

/-- K_band at dyadic scale k equals 2*k+7.
    K_band(x) := 2 * ceil(log(1/x)/log 2) + 7. -/
lemma k_band_dyadic_eq (k : ℕ) :
    2 * Nat.ceil (Real.log (1 / dyadicDelta k) / Real.log 2) + 7 = 2 * k + 7 := by
  rw [ceil_log_dyadicDelta k] <;> ring

end DirecretisedFurstenbergEstimate.Section9

end
