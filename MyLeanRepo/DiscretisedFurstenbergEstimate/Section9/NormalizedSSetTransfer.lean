module

/-
  Normalized S-set transfer helpers for Section 9 Step 5.

  Composes normalization (φ, φ_line at scale δ → δ/4) with iterated
  coarsening (δ/4 → δ_d = Δ^m) for both Plane point sets and AffineLine
  tube families.

  IMPORTANT: δ_d must be chosen near δ/4, not δ. Specifically:
    δ/4 ≤ δ_d ≤ (1/Δ) * (δ/4)

  Also transfers geometric conditions (thickening incidence, offset bounds)
  under normalization.

  Dependencies:
  - Section9/Normalization.lean
  - Section9/ScaleTransferHelpers.lean
  - Section9/LineNormalizationSSet.lean (line_normalization_sset_transfer)

  Whiteprint node: section9 / normalized_sset_transfer
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.Normalization
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.LineNormalizationSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.ScaleTransferHelpers
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal Pointwise

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

open DiscretisedFurstenbergEstimate
open MainAppendix
open Normalization (φ φ_line normalize_sset normalized_offset_bound φ_line_bilipschitz)
open LineNormalizationSSet (line_normalization_sset_transfer)

/-! ### Plane: full normalized transfer δ → δ_d -/

/-- Transfer a Plane S-set from source scale δ to decomposition scale δ_d
    via normalization (δ → δ/4) then coarsening (δ/4 → δ_d).

    Requires: δ/4 ≤ δ_d ≤ (1/Δ) * (δ/4).
    Constant: C · 4^t · 9^q. -/
lemma normalized_sset_to_dd_plane
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    {δ δ_d : ℝ} (hδ_pos : 0 < δ) (hδ_d_pos : 0 < δ_d)
    (hδ_norm_le_dd : δ / 4 ≤ δ_d)
    (hδ_d_le_ratio : δ_d ≤ (1 / Δ) * (δ / 4))
    (q : ℕ) (hΔ_eq : Δ = (1 / 2 : ℝ) ^ q)
    {t C : ℝ} (ht : 0 ≤ t) (hC_pos : 0 < C)
    {P : Set EuclideanPlane}
    (hP : IsDeltaSSet δ t C P) :
    IsDeltaSSet δ_d t (C * (4 : ℝ)^t * (9 : ℝ)^q) (φ '' P) := by
  have h1 : IsDeltaSSet (δ / 4) t (C * (4 : ℝ)^t) (φ '' P) :=
    normalize_sset hP
  have h2 : IsDeltaSSet δ_d t ((C * (4 : ℝ)^t) * (9 : ℝ)^q) (φ '' P) :=
    sset_transfer_norm_to_dd_plane
      Δ hΔ_pos hδ_pos hδ_d_pos hδ_norm_le_dd hδ_d_le_ratio q hΔ_eq ht (by positivity) h1
  have h3 : (C * (4 : ℝ)^t) * (9 : ℝ)^q = C * (4 : ℝ)^t * (9 : ℝ)^q := by ring
  rw [h3] at h2
  exact h2

/-! ### AffineLine: full normalized transfer δ → δ_d -/

/-- Transfer an AffineLine S-set from source scale δ to decomposition scale δ_d
    via normalization (δ → δ/4) then coarsening (δ/4 → δ_d).

    Requires: δ/4 ≤ δ_d ≤ (1/Δ) * (δ/4).
    Constant: C · 4^s · Kpack^3 · Kpack^q = C · 4^s · Kpack^(q+3).

    Uses normalize_sset_affineLine (granite, pending). -/
lemma normalized_sset_to_dd_affineLine
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    {δ δ_d : ℝ} (hδ_pos : 0 < δ) (hδ_d_pos : 0 < δ_d)
    (hδ_norm_le_dd : δ / 4 ≤ δ_d)
    (hδ_d_le_ratio : δ_d ≤ (1 / Δ) * (δ / 4))
    (q : ℕ) (hΔ_eq : Δ = (1 / 2 : ℝ) ^ q)
    {s C : ℝ} (hs : 0 ≤ s) (hC_pos : 0 < C)
    {T : Set AffineLine}
    (hT : IsDeltaSSet δ s C T) :
    IsDeltaSSet δ_d s
      (C * (4 : ℝ)^s * (affineLine_packing_constant : ℝ)^(q + 3))
      (φ_line '' T) := by
  -- Step 1: normalize δ → δ/4 (granite's theorem)
  have h_norm : IsDeltaSSet (δ / 4) s
      (C * (4 : ℝ)^s * (affineLine_packing_constant : ℝ)^3) (φ_line '' T) :=
    line_normalization_sset_transfer hδ_pos hs hC_pos hT
  -- Step 2: coarsen δ/4 → δ_d
  have h_const_pos : 0 < (C * (4 : ℝ)^s * (affineLine_packing_constant : ℝ)^3) := by
    have h1 : 0 < (4 : ℝ)^s := Real.rpow_pos_of_pos (by norm_num) s
    have h2 : 0 < (affineLine_packing_constant : ℝ) := by
      exact_mod_cast affineLine_packing_constant_pos
    positivity
  have h_coarsen : IsDeltaSSet δ_d s
      ((C * (4 : ℝ)^s * (affineLine_packing_constant : ℝ)^3) *
        (affineLine_packing_constant : ℝ)^q) (φ_line '' T) :=
    sset_transfer_norm_to_dd_affineLine
      Δ hΔ_pos hδ_pos hδ_d_pos hδ_norm_le_dd hδ_d_le_ratio q hΔ_eq hs h_const_pos h_norm
  have h3 : (C * (4 : ℝ)^s * (affineLine_packing_constant : ℝ)^3) *
        (affineLine_packing_constant : ℝ)^q =
      C * (4 : ℝ)^s * (affineLine_packing_constant : ℝ)^(q + 3) := by
    simp [pow_add] <;> ring
  rw [h3] at h_coarsen
  exact h_coarsen

/-! ### Geometric condition transfers -/

/-- Thickening incidence transfers under φ:
    if p ∈ cthickening(δ, ℓ.1), then φ p ∈ cthickening(δ/4, (φ_line ℓ).1). -/
lemma normalized_near_transfer {δ : ℝ} (hδ_pos : 0 < δ)
    {p : EuclideanPlane} {ℓ : AffineLine}
    (h : p ∈ Metric.cthickening δ ℓ.1) :
    φ p ∈ Metric.cthickening (δ / 4) (φ_line ℓ).1 := by
  have hc_pos : 0 < Normalization.c := Normalization.c_pos
  let c : ℝ := Normalization.c
  let s : Set EuclideanPlane := ℓ.1
  have hS_nonempty : s.Nonempty := by exact AffineLine.nonempty ℓ

  -- Exact distance scaling: dist(φ x, φ y) = c * dist(x, y)
  have h_dist_scale : ∀ (x y : EuclideanPlane), dist (φ x) (φ y) = c * dist x y := by
    intro x y
    have h_sub : φ x - φ y = c • (x - y) := by
      have h_def : ∀ z, φ z = c • z + Normalization.halfVec := by intro z; rfl
      rw [h_def x, h_def y]
      simp [smul_sub] <;> abel
    have h_norm : ‖c • (x - y)‖ = |c| * ‖x - y‖ := by
      simp [norm_smul] <;> ring
    calc
      dist (φ x) (φ y) = ‖φ x - φ y‖ := by rw [dist_eq_norm]
      _ = ‖c • (x - y)‖ := by rw [h_sub]
      _ = |c| * ‖x - y‖ := h_norm
      _ = c * ‖x - y‖ := by rw [abs_of_pos hc_pos]
      _ = c * dist x y := by rw [dist_eq_norm]

  -- Distance image scales: dist(φ p) '' (φ '' s) = {c * d | d ∈ dist p '' s}
  have h_smul_set : (fun d : ℝ => c * d) '' (dist p '' s) = c • (dist p '' s) := by
    ext z
    simp [Set.mem_image, Set.mem_smul_set]
    <;> ring
  have h_img_dist : (dist (φ p) '' (φ '' s)) = c • (dist p '' s) := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨dist p x, ⟨x, hx, rfl⟩, (h_dist_scale p x).symm⟩
    · rintro ⟨d, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨φ x, ⟨x, hx, rfl⟩, h_dist_scale p x⟩

  -- infDist scales exactly
  have h_iInf_eq : ∀ (x : EuclideanPlane) (t : Set EuclideanPlane), t.Nonempty →
      (⨅ (y : {y // y ∈ t}), dist x y) = sInf (dist x '' t) := by
    intro x t ht
    have h1 : (⨅ (y : {y // y ∈ t}), dist x y) = sInf (Set.range (fun (y : {y // y ∈ t}) => dist x y)) := by
      exact Eq.symm sInf_range
    rw [h1]
    have h2 : Set.range (fun (y : {y // y ∈ t}) => dist x y) = dist x '' t := by
      ext z
      simp [Set.ext_iff]
      <;> aesop
    rw [h2]
  have h_infDist_sInf : ∀ (x : EuclideanPlane) (t : Set EuclideanPlane), t.Nonempty →
      Metric.infDist x t = sInf (dist x '' t) := by
    intro x t ht
    rw [Metric.infDist_eq_iInf]
    exact h_iInf_eq x t ht
  have hA_nonempty : (dist p '' s).Nonempty := hS_nonempty.image _
  have h_infDist_eq : Metric.infDist (φ p) (φ '' s) = c * Metric.infDist p s := by
    rw [h_infDist_sInf (φ p) (φ '' s) (hS_nonempty.image φ),
        h_infDist_sInf p s hS_nonempty, h_img_dist]
    exact Real.sInf_smul_of_nonneg hc_pos.le (dist p '' s)

  -- Both infEDist values are finite (metric space + nonempty set)
  have h_infEDist_p_ne_top : Metric.infEDist p s ≠ ⊤ := by
    have h9 : Metric.infEDist p s ≤ ENNReal.ofReal δ := by simpa [Metric.cthickening] using h
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h9
  have h_infEDist_φ_ne_top : Metric.infEDist (φ p) (φ '' s) ≠ ⊤ := by
    rcases hS_nonempty with ⟨y, hy⟩
    have h10 : Metric.infEDist (φ p) (φ '' s) ≤ edist (φ p) (φ y) :=
      Metric.infEDist_le_edist_of_mem (Set.mem_image_of_mem φ hy)
    have h11 : edist (φ p) (φ y) ≠ ⊤ := by exact edist_ne_top (φ p) (φ y)
    exact ne_top_of_le_ne_top h11 h10

  -- Convert between infDist and infEDist
  have h_ofReal_p : ENNReal.ofReal (Metric.infDist p s) = Metric.infEDist p s := by
    rw [Metric.infDist, ENNReal.ofReal_toReal h_infEDist_p_ne_top]
  have h_ofReal_φ : ENNReal.ofReal (Metric.infDist (φ p) (φ '' s)) = Metric.infEDist (φ p) (φ '' s) := by
    rw [Metric.infDist, ENNReal.ofReal_toReal h_infEDist_φ_ne_top]

  -- Main infEDist equality
  have h_main : Metric.infEDist (φ p) (φ '' s) = ENNReal.ofReal c * Metric.infEDist p s := by
    calc
      Metric.infEDist (φ p) (φ '' s)
        = ENNReal.ofReal (Metric.infDist (φ p) (φ '' s)) := h_ofReal_φ.symm
      _ = ENNReal.ofReal (c * Metric.infDist p s) := by rw [h_infDist_eq]
      _ = ENNReal.ofReal c * ENNReal.ofReal (Metric.infDist p s) := by
        rw [ENNReal.ofReal_mul hc_pos.le]
      _ = ENNReal.ofReal c * Metric.infEDist p s := by rw [h_ofReal_p]

  -- Map φ '' s to φ_line ℓ
  have h2 : (φ '' s) = ((φ_line ℓ).1 : Set EuclideanPlane) := by rfl
  rw [h2] at h_main

  -- Final bound
  have h3 : Metric.infEDist p s ≤ ENNReal.ofReal δ := by simpa [Metric.cthickening] using h
  have h4 : ENNReal.ofReal c * Metric.infEDist p s ≤ ENNReal.ofReal c * ENNReal.ofReal δ := by gcongr
  have h5 : ENNReal.ofReal c * ENNReal.ofReal δ = ENNReal.ofReal (c * δ) := by
    rw [← ENNReal.ofReal_mul hc_pos.le]
  have h6 : c * δ = δ / 4 := by
    have h7 : c = 1 / 4 := by simp [c, Normalization.c] <;> ring
    rw [h7] <;> ring
  have h4' : ENNReal.ofReal c * Metric.infEDist p s ≤ ENNReal.ofReal (δ / 4) := by
    calc
      ENNReal.ofReal c * Metric.infEDist p s
        ≤ ENNReal.ofReal c * ENNReal.ofReal δ := h4
      _ = ENNReal.ofReal (c * δ) := h5
      _ = ENNReal.ofReal (δ / 4) := by rw [h6]
  have h_final : Metric.infEDist (φ p) (φ_line ℓ).1 ≤ ENNReal.ofReal (δ / 4) := by
    rw [h_main]
    exact h4'
  simpa [Metric.cthickening] using h_final

/-- Offset bound transfers under φ_line. -/
lemma normalized_offset_transfer {ℓ : AffineLine}
    (h : ℓ.offset ∈ Metric.closedBall (0 : EuclideanPlane) 2) :
    (φ_line ℓ).offset ∈ Metric.closedBall (0 : EuclideanPlane) 2 :=
  normalized_offset_bound h

/-- Boundedness transfers under φ_line. -/
lemma normalized_tube_bounded {T : Set AffineLine} (hT : Bornology.IsBounded T) :
    Bornology.IsBounded (φ_line '' T) := by
  rcases φ_line_bilipschitz with ⟨U, K, hU_pos, hK_pos, h_lip, _⟩
  let U' : NNReal := ⟨U, hU_pos.le⟩
  have h_lip' : LipschitzWith U' φ_line :=
    LipschitzWith.of_dist_le_mul h_lip
  exact h_lip'.isBounded_image hT

end DirecretisedFurstenbergEstimate.Section9

end
