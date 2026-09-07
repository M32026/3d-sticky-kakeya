module

/-
  Iterated S-set coarsening for AffineLine.

  Adapts `sset_transfer_coarser_plane_iter` (Section9Assembly.lean)
  from EuclideanPlane (doubling constant 9) to AffineLine
  (doubling constant affineLine_packing_constant).

  If `δ ≤ δ_d ≤ 2^k · δ`, a `(δ, s, C)`-set of AffineLines
  is a `(δ_d, s, C · Kpack^k)`-set.

  Whiteprint node: section9 / affine_line_iterated_transfer
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.SnappingSSetTransfer
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Snapping
open MainAppendix

/-- Iterated S-set coarsening for AffineLine:
    if `δ ≤ δ_d ≤ 2^k · δ`, a `(δ, s, C)`-set is a `(δ_d, s, C · Kpack^k)`-set. -/
lemma sset_transfer_coarser_affineLine_iter
    {δ δ_d s C : ℝ} {S : Set AffineLine}
    (hδ_pos : 0 < δ) (hδ_d_pos : 0 < δ_d)
    (hδ_le_d : δ ≤ δ_d)
    (k : ℕ) (hδ_d_le : δ_d ≤ ((2^k : ℕ) : ℝ) * δ)
    (hs : 0 ≤ s) (hC_pos : 0 < C)
    (hS : IsDeltaSSet δ s C S) :
    IsDeltaSSet δ_d s (C * (affineLine_packing_constant : ℝ)^k) S := by
  rcases hS with ⟨hS_nonempty, _, _, hs_nonneg, h_main⟩
  let Kpack : ℕ := affineLine_packing_constant
  have hK_pos : 0 < (Kpack : ℝ) := by
    exact_mod_cast affineLine_packing_constant_pos'
  have hCK_pos : 0 < C * (Kpack : ℝ)^k := by positivity
  have hN1 : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤
      (Kpack : ENNReal)^k *
        Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal S :=
    affineLine_doubling_iter δ hδ_pos k (S := S)
  have hN2 : Metric.externalCoveringNumber (((2^k : ℕ) : ℝ) * δ).toNNReal S ≤
      Metric.externalCoveringNumber δ_d.toNNReal S := by
    have h_le : ((2^k : ℕ) : ℝ) * δ ≥ δ_d := by exact_mod_cast hδ_d_le
    have h_le' : δ_d.toNNReal ≤ (((2^k : ℕ) : ℝ) * δ).toNNReal := by exact Real.toNNReal_mono hδ_d_le
    exact Metric.externalCoveringNumber_anti h_le'
  have hNcover : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤
      (Kpack : ENNReal)^k * Metric.externalCoveringNumber δ_d.toNNReal S :=
    le_trans hN1 (by gcongr)
  refine' ⟨hS_nonempty, hδ_d_pos, hCK_pos, hs_nonneg, _⟩
  intro x r hr
  have hδ_le_r : δ ≤ r := by linarith
  have h1 : (Metric.externalCoveringNumber δ_d.toNNReal (S ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall x r) : ENNReal) := by
    have h_le : δ.toNNReal ≤ δ_d.toNNReal := by exact Real.toNNReal_mono hδ_le_d
    exact_mod_cast Metric.externalCoveringNumber_anti h_le
  have h2 := h_main x r hδ_le_r
  calc (Metric.externalCoveringNumber δ_d.toNNReal (S ∩ Metric.closedBall x r) : ENNReal)
    ≤ (Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall x r) : ENNReal) := h1
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := h2
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          ((Kpack : ENNReal)^k * Metric.externalCoveringNumber δ_d.toNNReal S) := by gcongr
    _ = ENNReal.ofReal (C * (Kpack : ℝ)^k) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ_d.toNNReal S) := by
      have h3 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            ((Kpack : ENNReal)^k * Metric.externalCoveringNumber δ_d.toNNReal S) =
          (Kpack : ENNReal)^k * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            Metric.externalCoveringNumber δ_d.toNNReal S := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
      rw [h3]
      have h4 : (Kpack : ENNReal)^k * ENNReal.ofReal C =
          ENNReal.ofReal ((Kpack : ℝ)^k * C) := by
        have h41 : (Kpack : ENNReal)^k = ENNReal.ofReal ((Kpack : ℝ)^k) := by simp
        rw [h41]
        have h5 : 0 ≤ (Kpack : ℝ)^k := by positivity
        rw [← ENNReal.ofReal_mul h5]
      rw [h4] <;> ring_nf

end DirecretisedFurstenbergEstimate.Section9

end
