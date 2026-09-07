module

/-
  Lemmas for h_fine_rescalable discharge in A10.

  Contains:
  - toPlane'/fromPlane' Lipschitz maps (local copies to avoid import conflict)
  - IsDeltaSSet.snap_plane: snapping transfer on EuclideanPlane
  - IsDeltaSSet.rescale_16δ_to_delta: 16δ → δ → IsRescalableDeltaSet
  - fine_tube_sset_to_dyadic_rescalable: A9 interface assembly
  - covering_prod_to_plane: covering number transfer ℝ×ℝ → EuclideanPlane
  - IsRescalableDeltaSet.prod_to_plane: rescalable transfer ℝ×ℝ → EuclideanPlane

  Whiteprint: appendix_a_alternative / a10_product_witness
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductStructureRescaling.Basics
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductStructureRescaling.CoveringScaling
public import MyLeanRepo.DiscretisedFurstenbergEstimate.SsetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductContradiction
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.A10

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA

abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- Local definitions to avoid import conflict between A9_A10_Helpers and AffineLineSSet
def toPlane' : ℝ × ℝ → EuclideanPlane := fun p =>
  EuclideanSpace.equiv (Fin 2) ℝ |>.symm (fun i => if i = 0 then p.1 else p.2)

def fromPlane' : EuclideanPlane → ℝ × ℝ := fun q => (q 0, q 1)

lemma fromPlane'_lip : LipschitzWith (1 : NNReal) fromPlane' := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h1 : dist (fromPlane' x) (fromPlane' y) = max (|x 0 - y 0|) (|x 1 - y 1|) := by
    simp [fromPlane', Prod.dist_eq] <;> rfl
  rw [h1]
  have h2 : (x 0 - y 0)^2 + (x 1 - y 1)^2 = ‖x - y‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    have h : Real.sqrt ((x 0 - y 0)^2 + (x 1 - y 1)^2)^2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
      rw [Real.sq_sqrt] <;> positivity
    simpa [Fin.sum_univ_two] using h.symm
  have h_pos1 : 0 ≤ (x 1 - y 1)^2 := by positivity
  have h41 : (x 0 - y 0)^2 ≤ (x 0 - y 0)^2 + (x 1 - y 1)^2 := le_add_of_nonneg_right h_pos1
  have h41' : (x 0 - y 0)^2 ≤ ‖x - y‖ ^ 2 := by rw [←h2] <;> exact h41
  have h_pos2 : 0 ≤ (x 0 - y 0)^2 := by positivity
  have h42 : (x 1 - y 1)^2 ≤ (x 0 - y 0)^2 + (x 1 - y 1)^2 := le_add_of_nonneg_left h_pos2
  have h42' : (x 1 - y 1)^2 ≤ ‖x - y‖ ^ 2 := by rw [←h2] <;> exact h42
  have h4 : |x 0 - y 0| ≤ ‖x - y‖ := by
    have h5 : |x 0 - y 0|^2 = (x 0 - y 0)^2 := by rw [sq_abs]
    nlinarith [norm_nonneg (x - y), h41', h5]
  have h5 : |x 1 - y 1| ≤ ‖x - y‖ := by
    have h6 : |x 1 - y 1|^2 = (x 1 - y 1)^2 := by rw [sq_abs]
    nlinarith [norm_nonneg (x - y), h42', h6]
  have h3 : max (|x 0 - y 0|) (|x 1 - y 1|) ≤ ‖x - y‖ := max_le h4 h5
  simpa [dist_eq_norm] using h3

lemma toPlane'_lip : LipschitzWith (Real.toNNReal (Real.sqrt 2)) toPlane' := by
  let K : NNReal := Real.toNNReal (Real.sqrt 2)
  have hK : (K : ℝ) = Real.sqrt 2 := by
    simp [K, Real.toNNReal_of_nonneg (show 0 ≤ Real.sqrt 2 by positivity)]
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h1 : dist (toPlane' p) (toPlane' q) = ‖toPlane' p - toPlane' q‖ := by rw [dist_eq_norm]
  rw [h1]
  have h_sub0 : (toPlane' p - toPlane' q) 0 = p.1 - q.1 := by simp [toPlane'] <;> aesop
  have h_sub1 : (toPlane' p - toPlane' q) 1 = p.2 - q.2 := by simp [toPlane'] <;> aesop
  have h2 : ‖toPlane' p - toPlane' q‖ ^ 2 = (p.1 - q.1)^2 + (p.2 - q.2)^2 := by
    have h_euclid : ‖toPlane' p - toPlane' q‖ ^ 2 =
        ((toPlane' p - toPlane' q) 0)^2 + ((toPlane' p - toPlane' q) 1)^2 := by
      rw [EuclideanSpace.norm_eq]
      have h_sqrt : Real.sqrt (((toPlane' p - toPlane' q) 0)^2 + ((toPlane' p - toPlane' q) 1)^2)^2 =
          ((toPlane' p - toPlane' q) 0)^2 + ((toPlane' p - toPlane' q) 1)^2 := by
        rw [Real.sq_sqrt] <;> positivity
      simpa [Fin.sum_univ_two] using h_sqrt
    rw [h_euclid, h_sub0, h_sub1]
  have h3 : dist p q = max (|p.1 - q.1|) (|p.2 - q.2|) := by simp [Prod.dist_eq] <;> rfl
  rw [h3]
  let M := max (|p.1 - q.1|) (|p.2 - q.2|)
  have h51 : (p.1 - q.1)^2 ≤ M^2 := by
    have h : |p.1 - q.1| ≤ M := le_max_left _ _
    have h' : (p.1 - q.1)^2 = |p.1 - q.1|^2 := by rw [sq_abs]
    rw [h']; gcongr
  have h52 : (p.2 - q.2)^2 ≤ M^2 := by
    have h : |p.2 - q.2| ≤ M := le_max_right _ _
    have h' : (p.2 - q.2)^2 = |p.2 - q.2|^2 := by rw [sq_abs]
    rw [h']; gcongr
  have h4 : (p.1 - q.1)^2 + (p.2 - q.2)^2 ≤ 2 * M^2 := by linarith
  have h9 : ‖toPlane' p - toPlane' q‖ ≤ Real.sqrt 2 * M := by
    have h10 : 0 ≤ ‖toPlane' p - toPlane' q‖ := by positivity
    have h11 : 0 ≤ Real.sqrt 2 * M := by positivity
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [hK]; exact h9

end DirecretisedFurstenbergEstimate.A10

open scoped ENNReal NNReal

/-- Snapping transfer for S-sets in EuclideanPlane. -/
lemma IsDeltaSSet.snap_plane {δ s C : ℝ} {P : Set (EuclideanSpace ℝ (Fin 2))}
    (h : IsDeltaSSet δ s C P)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : ∀ x, dist x (f x) ≤ δ / Real.sqrt 2) :
    IsDeltaSSet δ s (625 * (1 + 1 / Real.sqrt 2)^s * C) (f '' P) := by
  let P' := f '' P
  have hδ_pos : 0 < δ := h.2.1
  have hC_pos : 0 < C := h.2.2.1
  have hs : 0 ≤ s := h.2.2.2.1
  have hC'_pos : 0 < 625 * (1 + 1 / Real.sqrt 2)^s * C := by positivity
  have hP_nonempty : P.Nonempty := h.1
  have hP'_nonempty : P'.Nonempty := hP_nonempty.image f
  have hδ_toNNReal_pos : 0 < δ.toNNReal := by
    have h_eq : (δ.toNNReal : ℝ) = δ := by simp [Real.toNNReal, hδ_pos.le]
    exact Real.toNNReal_pos.mpr hδ_pos
  have hsnap' : ∀ x, dist x (f x) ≤ (δ.toNNReal : ℝ) / Real.sqrt 2 := by
    intro x
    have h_eq : (δ.toNNReal : ℝ) = δ := by simp [Real.toNNReal, hδ_pos.le]
    rw [h_eq]
    exact hf x
  have h_upper : (Metric.externalCoveringNumber δ.toNNReal P' : ℝ≥0∞) ≤
      (25 : ℝ≥0∞) * (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞) := by
    exact_mod_cast ncover_snap_upper_nat hδ_toNNReal_pos hsnap'
  have h_lower : (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞) ≤
      (25 : ℝ≥0∞) * (Metric.externalCoveringNumber δ.toNNReal P' : ℝ≥0∞) := by
    exact_mod_cast ncover_snap_lower_nat hδ_toNNReal_pos hsnap'
  refine ⟨hP'_nonempty, hδ_pos, hC'_pos, hs, fun x r hr => ?_⟩
  set r' : ℝ := r + δ / Real.sqrt 2 with hr'_def
  have hr'_ge : δ ≤ r' := by
    dsimp only [r']
    have h_pos : 0 < δ / Real.sqrt 2 := by positivity
    linarith
  have hr'_le : r' ≤ (1 + 1 / Real.sqrt 2) * r := by
    dsimp only [r']
    have h1 : δ ≤ r := hr
    have h2 : 0 ≤ r := by linarith
    have h3 : δ / Real.sqrt 2 ≤ r / Real.sqrt 2 := by gcongr
    have h4 : r + δ / Real.sqrt 2 ≤ r + r / Real.sqrt 2 := by linarith
    have h5 : r + r / Real.sqrt 2 = (1 + 1 / Real.sqrt 2) * r := by ring
    linarith
  have h_inter1 : P' ∩ Metric.closedBall x r ⊆
      f '' (P ∩ Metric.closedBall x r') :=
    snap_image_inter_subset hδ_pos hf
  have h_cover1 : (Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x r) : ℝ≥0∞) ≤
      (Metric.externalCoveringNumber δ.toNNReal (f '' (P ∩ Metric.closedBall x r')) : ℝ≥0∞) := by
    have h := Metric.externalCoveringNumber_mono_set (ε := δ.toNNReal) h_inter1
    exact_mod_cast h
  have h_cover2 : (Metric.externalCoveringNumber δ.toNNReal (f '' (P ∩ Metric.closedBall x r')) : ℝ≥0∞) ≤
      (25 : ℝ≥0∞) * (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r')) := by
    exact_mod_cast ncover_snap_upper_nat hδ_toNNReal_pos hsnap'
  have h_sset : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r') : ℝ≥0∞) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r') ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞) :=
    h.2.2.2.2 x r' hr'_ge
  have h_rpow_mono : (ENNReal.ofReal r') ^ s ≤ (ENNReal.ofReal ((1 + 1 / Real.sqrt 2) * r)) ^ s := by
    gcongr <;> linarith
  have hpos1 : 0 < 1 + 1 / Real.sqrt 2 := by positivity
  have h_expand : ENNReal.ofReal ((1 + 1 / Real.sqrt 2) * r) ^ s =
      ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s) * (ENNReal.ofReal r) ^ s := by
    have h9 : ENNReal.ofReal ((1 + 1 / Real.sqrt 2) * r) =
        ENNReal.ofReal (1 + 1 / Real.sqrt 2) * ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_mul hpos1.le] <;> ring
    rw [h9]
    have h10 : (ENNReal.ofReal (1 + 1 / Real.sqrt 2) * ENNReal.ofReal r) ^ s =
        (ENNReal.ofReal (1 + 1 / Real.sqrt 2)) ^ s * (ENNReal.ofReal r) ^ s :=
      ENNReal.mul_rpow_of_nonneg _ _ (by linarith)
    rw [h10]
    have h11 : (ENNReal.ofReal (1 + 1 / Real.sqrt 2)) ^ s =
        ENNReal.ofReal ((1 + 1 / Real.sqrt 2) ^ s) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hpos1.le (by linarith)]
    rw [h11] <;> ring
  calc
    (Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x r) : ENNReal)
      ≤ (Metric.externalCoveringNumber δ.toNNReal (f '' (P ∩ Metric.closedBall x r')) : ENNReal) := h_cover1
    _ ≤ (25 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r')) := h_cover2
    _ ≤ (25 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r') ^ s * (Metric.externalCoveringNumber δ.toNNReal P)) := by gcongr
    _ ≤ (25 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal ((1 + 1 / Real.sqrt 2) * r)) ^ s * (Metric.externalCoveringNumber δ.toNNReal P)) := by gcongr
    _ ≤ (25 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s) * (ENNReal.ofReal r) ^ s) * (Metric.externalCoveringNumber δ.toNNReal P)) := by
        rw [h_expand]
    _ ≤ (25 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s) * (ENNReal.ofReal r) ^ s) * ((25 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal P'))) := by
        gcongr <;> exact h_lower
    _ = ENNReal.ofReal (625 * (1 + 1 / Real.sqrt 2)^s * C) * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P') := by
        have h_pos1 : 0 ≤ (1 + 1 / Real.sqrt 2)^s := by positivity
        have h_pos2 : 0 ≤ C := by linarith
        have h_ofReal1 : ENNReal.ofReal (625 * (1 + 1 / Real.sqrt 2)^s * C) =
            ENNReal.ofReal (625 * (1 + 1 / Real.sqrt 2)^s) * ENNReal.ofReal C := by
          rw [← ENNReal.ofReal_mul (by positivity)]
        have h_ofReal2 : ENNReal.ofReal (625 * (1 + 1 / Real.sqrt 2)^s) =
            (625 : ENNReal) * ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s) := by
          have h_step1 : ENNReal.ofReal (625 * (1 + 1 / Real.sqrt 2)^s) =
              ENNReal.ofReal (625 : ℝ) * ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s) := by
            exact ENNReal.ofReal_mul' h_pos1
          rw [h_step1]
          have h22 : ENNReal.ofReal (625 : ℝ) = (625 : ENNReal) := by norm_cast
          rw [h22]
        have h625 : (625 : ENNReal) = (25 : ENNReal) * (25 : ENNReal) := by norm_cast
        have h_const : ENNReal.ofReal (625 * (1 + 1 / Real.sqrt 2)^s * C) =
            (25 : ENNReal) * (25 : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s) := by
          rw [h_ofReal1, h_ofReal2, h625]
          <;> simp [mul_assoc, mul_comm, mul_left_comm]
        rw [h_const]
        <;> simp [mul_assoc, mul_comm, mul_left_comm]

namespace DirecretisedFurstenbergEstimate.A10

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA hiding IsRescalableDeltaSet

/-- Weaken the constant of an IsRescalableDeltaSet. -/
lemma IsRescalableDeltaSet.mono_const {X : Type*} [PseudoMetricSpace X]
    {δ Δ s C1 C2 : ℝ} {P : Set X}
    (h : IsRescalableDeltaSet δ Δ s C1 P) (hC : C1 ≤ C2) :
    IsRescalableDeltaSet δ Δ s C2 P :=
  DirecretisedFurstenbergEstimate.ProductContradiction.IsRescalableDeltaSet.mono_const h hC

/-- Convert a (16δ)-scale S-set on ℝ×ℝ to IsRescalableDeltaSet at scale δ. -/
lemma IsDeltaSSet.rescale_16δ_to_delta {δ Δ s C : ℝ} {P : Set (ℝ × ℝ)}
    (h : IsDeltaSSet (16 * δ) s C P)
    (hδ_pos : 0 < δ) (hΔ_pos : 0 < Δ) (hδ_eq : δ = Δ^2) (hs : 0 ≤ s) :
    IsRescalableDeltaSet δ Δ s (C * 256 * (16 : ℝ)^s * Δ^s) P := by
  have h16δ_pos : 0 < 16 * δ := by positivity
  have h4δ_pos : 0 < 4 * δ := by positivity
  have h_step1 : IsDeltaSSet (4 * δ) s (C * 16 * (4 : ℝ)^s) P :=
    IsDeltaSSet.scale_down2 h4δ_pos h16δ_pos (by linarith) (by linarith) h
  have h_step2 : IsDeltaSSet δ s ((C * 16 * (4 : ℝ)^s) * 16 * (4 : ℝ)^s) P :=
    IsDeltaSSet.scale_down2 hδ_pos h4δ_pos (by linarith) (by linarith) h_step1
  have h4s : (4 : ℝ)^s * (4 : ℝ)^s = (16 : ℝ)^s := by
    have h : (4 : ℝ)^s * (4 : ℝ)^s = (4 * 4 : ℝ)^s := by
      rw [← Real.mul_rpow (by norm_num) (by norm_num)] <;> norm_num
    rw [h] <;> norm_num
  have h_const_eq : (C * 16 * (4 : ℝ)^s) * 16 * (4 : ℝ)^s = C * 256 * (16 : ℝ)^s := by
    calc
      (C * 16 * (4 : ℝ)^s) * 16 * (4 : ℝ)^s
        = C * (16 * 16) * ((4 : ℝ)^s * (4 : ℝ)^s) := by ring
      _ = C * 256 * (16 : ℝ)^s := by rw [h4s] <;> ring
  have h_step3 : IsDeltaSSet δ s (C * 256 * (16 : ℝ)^s) P := by
    rw [h_const_eq] at h_step2
    exact h_step2
  have hδ_le_Δ2 : δ ≤ Δ^2 := by rw [hδ_eq]
  exact IsDeltaSSet.to_rescalable h_step3 hδ_le_Δ2 hΔ_pos hs

/-- A9 interface assembly: FineTube S-set → IsRescalableDeltaSet on dyadic cell params. -/
lemma fine_tube_sset_to_dyadic_rescalable
    {δ Δ s C : ℝ} {cells : Set (ℤ × ℤ)}
    {tubeOfCell : (ℤ × ℤ) → AffineLine}
    (hT_sset : IsDeltaSSet δ s C (tubeOfCell '' cells))
    (h_bounds : ∀ cell ∈ cells,
      (LemmaE.getDirV (tubeOfCell cell)) 1 ≠ 0 ∧
      |(LemmaE.affineLineParams (tubeOfCell cell)).1| ≤ 1 ∧
      |(LemmaE.affineLineParams (tubeOfCell cell)).2| ≤ 3)
    (h_params_eq : ∀ cell ∈ cells,
      LemmaE.affineLineParams (tubeOfCell cell) = DirecretisedFurstenbergEstimate.AppendixA.paramsOfDyadicCell δ cell)
    (hδ_pos : 0 < δ) (hΔ_pos : 0 < Δ) (hδ_eq : δ = Δ^2) (hs : 0 ≤ s) :
    IsRescalableDeltaSet δ Δ s
      (C * (20 : ℝ)^s * 1048576 * 256 * (16 : ℝ)^s * Δ^s)
      ((fun cell => DirecretisedFurstenbergEstimate.AppendixA.paramsOfDyadicCell δ cell) '' cells) := by
  let Tubes := tubeOfCell '' cells
  have hC_pos : 0 < C := hT_sset.2.2.1
  have h_bounds' : ∀ T ∈ Tubes,
      (LemmaE.getDirV T) 1 ≠ 0 ∧
      |(LemmaE.affineLineParams T).1| ≤ 1 ∧
      |(LemmaE.affineLineParams T).2| ≤ 3 := by
    intro T hT
    rcases hT with ⟨cell, hcell, rfl⟩
    exact h_bounds cell hcell
  have h1 : IsDeltaSSet (16 * δ) s (C * (20 : ℝ)^s * 1048576)
      (LemmaE.affineLineParams '' Tubes) :=
    affineLine_bounded_slope_sset_to_params hδ_pos hs hC_pos hT_sset h_bounds'
  have h_set_eq : LemmaE.affineLineParams '' Tubes =
      (fun cell => DirecretisedFurstenbergEstimate.AppendixA.paramsOfDyadicCell δ cell) '' cells := by
    ext z
    simp only [Tubes, Set.mem_image]
    constructor
    · rintro ⟨T, ⟨cell, hcell, rfl⟩, rfl⟩
      exact ⟨cell, hcell, Eq.symm (h_params_eq cell hcell)⟩
    · rintro ⟨cell, hcell, rfl⟩
      exact ⟨tubeOfCell cell, ⟨cell, hcell, rfl⟩, h_params_eq cell hcell⟩
  rw [h_set_eq] at h1
  exact IsDeltaSSet.rescale_16δ_to_delta h1 hδ_pos hΔ_pos hδ_eq hs

/-- Covering number transfer from ℝ×ℝ (L∞) to EuclideanPlane (L2) via toPlane'. -/
lemma covering_prod_to_plane {δ : ℝ} (hδ : 0 < δ) {S : Set (ℝ × ℝ)} :
    Metric.externalCoveringNumber δ.toNNReal (toPlane' '' S) ≤
      16 * Metric.externalCoveringNumber δ.toNNReal S := by
  have hδ2_pos : 0 < δ / Real.sqrt 2 := by positivity
  have h_sqrt2_pos : 0 < Real.sqrt 2 := by positivity
  have h_scale : δ ≤ 4 * (δ / Real.sqrt 2) := by
    have h_sqrt_le_4 : Real.sqrt 2 ≤ 4 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h : δ ≤ (δ / Real.sqrt 2) * 4 := by
      calc δ
        = (δ / Real.sqrt 2) * Real.sqrt 2 := by field_simp [h_sqrt2_pos.ne'] <;> ring
      _ ≤ (δ / Real.sqrt 2) * 4 := by gcongr
    linarith
  set ε2 : NNReal := (δ / Real.sqrt 2).toNNReal with hε2_def
  have hε2_pos : 0 < ε2 := by
    have h_eq : (ε2 : ℝ) = δ / Real.sqrt 2 := by
      simp [ε2, Real.toNNReal_of_nonneg (show 0 ≤ δ / Real.sqrt 2 by positivity)]
    exact Real.toNNReal_pos.mpr hδ2_pos
  have hK_mul : (Real.toNNReal (Real.sqrt 2)) * ε2 = δ.toNNReal := by
    apply NNReal.coe_injective
    have h_nonneg1 : 0 ≤ Real.sqrt 2 := by positivity
    have h_nonneg2 : 0 ≤ δ / Real.sqrt 2 := by positivity
    have h_nonneg3 : 0 ≤ δ := by linarith
    simp [ε2, Real.toNNReal_of_nonneg h_nonneg1, Real.toNNReal_of_nonneg h_nonneg2, Real.toNNReal_of_nonneg h_nonneg3]
    <;> field_simp [h_sqrt2_pos.ne'] <;> ring
  have h1 : Metric.externalCoveringNumber δ.toNNReal (toPlane' '' S) ≤
      Metric.externalCoveringNumber ε2 S := by
    have h : ∀ (C : Set (ℝ × ℝ)), Metric.IsCover ε2 S C →
        Metric.externalCoveringNumber δ.toNNReal (toPlane' '' S) ≤ C.encard := by
      intro C hC
      have hC' : Metric.IsCover ((Real.toNNReal (Real.sqrt 2)) * ε2) (toPlane' '' S) (toPlane' '' C) :=
        Metric.IsCover.image_lipschitz hC toPlane'_lip
      rw [hK_mul] at hC'
      have h_card : (toPlane' '' C).encard ≤ C.encard := Set.encard_image_le toPlane' C
      have h_le : Metric.externalCoveringNumber δ.toNNReal (toPlane' '' S) ≤ (toPlane' '' C).encard :=
        Metric.IsCover.externalCoveringNumber_le_encard hC'
      exact le_trans h_le h_card
    simpa [Metric.externalCoveringNumber] using le_iInf₂ h
  have h2 : Metric.externalCoveringNumber ε2 S ≤
      16 * Metric.externalCoveringNumber δ.toNNReal S :=
    covering_scale_2d hδ2_pos hδ h_scale
  exact le_trans h1 h2

/-- Transfer IsRescalableDeltaSet from ℝ×ℝ to EuclideanPlane via toPlane'. -/
lemma IsRescalableDeltaSet.prod_to_plane {δ Δ s C : ℝ} {P : Set (ℝ × ℝ)}
    (h : IsRescalableDeltaSet δ Δ s C P) :
    IsRescalableDeltaSet δ Δ s (16 * C) (toPlane' '' P) := by
  let Q := toPlane' '' P
  have hδ_pos : 0 < δ := h.2.1
  have hΔ_pos : 0 < Δ := h.2.2.1
  have hC_pos : 0 < C := h.2.2.2.1
  have hs : 0 ≤ s := h.2.2.2.2.1
  have h_main : ∀ (x : ℝ × ℝ) (r : ℝ), Δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x (Δ * r)) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h.2.2.2.2.2
  have hC'_pos : 0 < 16 * C := by positivity
  have hQ_nonempty : Q.Nonempty := h.1.image toPlane'
  have h_left_inv : ∀ (y : ℝ × ℝ), fromPlane' (toPlane' y) = y := by
    intro y
    apply Prod.ext
    · simp [toPlane', fromPlane'] <;> aesop
    · simp [toPlane', fromPlane'] <;> aesop
  have h_cover_lower : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal Q : ENNReal) := by
    have h : ∀ (D : Set EuclideanPlane), Metric.IsCover δ.toNNReal Q D →
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤ (D.encard : ENNReal) := by
      intro D hD
      have hD1 : Metric.IsCover ((1 : NNReal) * δ.toNNReal) (fromPlane' '' Q) (fromPlane' '' D) :=
        Metric.IsCover.image_lipschitz hD fromPlane'_lip
      have h_img : fromPlane' '' Q = P := by
        ext z
        simp only [Set.mem_image]
        constructor
        · rintro ⟨y, hy, rfl⟩
          rcases hy with ⟨w, hw, rfl⟩
          rw [h_left_inv w]
          exact hw
        · intro hz
          exact ⟨toPlane' z, Set.mem_image_of_mem toPlane' hz, h_left_inv z⟩
      have h_one : (1 : NNReal) * δ.toNNReal = δ.toNNReal := by simp
      rw [h_one] at hD1
      rw [h_img] at hD1
      have hD' : Metric.IsCover δ.toNNReal P (fromPlane' '' D) := hD1
      have h_card : (fromPlane' '' D).encard ≤ D.encard := Set.encard_image_le fromPlane' D
      have h_le : Metric.externalCoveringNumber δ.toNNReal P ≤ (fromPlane' '' D).encard :=
        Metric.IsCover.externalCoveringNumber_le_encard hD'
      exact_mod_cast le_trans h_le h_card
    simpa [Metric.externalCoveringNumber] using le_iInf₂ h
  refine ⟨hQ_nonempty, hδ_pos, hΔ_pos, hC'_pos, hs, fun q r hr => ?_⟩
  have h_inter : Q ∩ Metric.closedBall q (Δ * r) ⊆
      toPlane' '' (P ∩ Metric.closedBall (fromPlane' q) (Δ * r)) := by
    intro p hp
    rcases hp.1 with ⟨y, hy, rfl⟩
    have hdist : dist (fromPlane' (toPlane' y)) (fromPlane' q) ≤ Δ * r := by
      have h : dist (fromPlane' (toPlane' y)) (fromPlane' q) ≤ (1 : ℝ) * dist (toPlane' y) q :=
        fromPlane'_lip.dist_le_mul (toPlane' y) q
      have h' : (1 : ℝ) * dist (toPlane' y) q = dist (toPlane' y) q := by ring
      rw [h'] at h
      have h2 : dist (toPlane' y) q ≤ Δ * r := by simpa [Metric.mem_closedBall] using hp.2
      exact le_trans h h2
    have h3 : fromPlane' (toPlane' y) = y := h_left_inv y
    rw [h3] at hdist
    exact ⟨y, ⟨hy, by simpa [Metric.mem_closedBall] using hdist⟩, rfl⟩
  set S_int := P ∩ Metric.closedBall (fromPlane' q) (Δ * r) with hS_int_def
  have h1 : (Metric.externalCoveringNumber δ.toNNReal (Q ∩ Metric.closedBall q (Δ * r)) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (toPlane' '' S_int) : ENNReal) := by
    have h_mono := Metric.externalCoveringNumber_mono_set (ε := δ.toNNReal) h_inter
    exact_mod_cast h_mono
  have h2 : (Metric.externalCoveringNumber δ.toNNReal (toPlane' '' S_int) : ENNReal) ≤
      (16 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal S_int : ENNReal) := by
    have h := covering_prod_to_plane (S := S_int) hδ_pos
    exact_mod_cast h
  have h3 : (Metric.externalCoveringNumber δ.toNNReal S_int : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) :=
    h_main (fromPlane' q) r hr
  calc
    (Metric.externalCoveringNumber δ.toNNReal (Q ∩ Metric.closedBall q (Δ * r)) : ENNReal)
      ≤ (Metric.externalCoveringNumber δ.toNNReal (toPlane' '' S_int) : ENNReal) := h1
    _ ≤ (16 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal S_int : ENNReal) := h2
    _ ≤ (16 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal)) := by gcongr
    _ ≤ (16 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal Q : ENNReal)) := by
        gcongr <;> exact h_cover_lower
    _ = ENNReal.ofReal (16 * C) * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal Q : ENNReal) := by
        have h_const : ENNReal.ofReal (16 * C) = (16 : ENNReal) * ENNReal.ofReal C := by
          have h : ENNReal.ofReal (16 * C) = ENNReal.ofReal (16 : ℝ) * ENNReal.ofReal C := by
            rw [← ENNReal.ofReal_mul (by norm_num)] <;> ring
          rw [h]
          have h2 : ENNReal.ofReal (16 : ℝ) = (16 : ENNReal) := by norm_cast
          rw [h2] <;> ring
        rw [h_const] <;> ring

/-- Convert A9 fine rescalable data to A10 h_fine_rescalable_prod and h_fine_rescalable.

    Given the bound `16 * C_fine_resc ≤ Δ^{-499ε}`, produces both the prod version
    (by weakening the constant) and the plane version (by applying prod_to_plane then
    weakening).

    Note: the plane version uses this namespace's `toPlane'`. A10_Fixed's `toPlane'`
    is definitionally equal, so the result transfers by `rfl`. -/
lemma a10_fine_rescalable_of_a9
    {Δ δ s t ε : ℝ} (a9 : A9_Output Δ δ s t ε)
    (hC_le : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0),
      16 * (a9.perSquare Q hQ).C_fine_resc ≤ Real.rpow Δ (-501 * ε))
    (hΔ_pos : 0 < Δ) (hs : 0 ≤ s) :
    (∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0) (p : EuclideanPlane)
        (hp : p ∈ (a9.perSquare Q hQ).P_norm_Q),
      IsRescalableDeltaSet δ Δ s (Real.rpow Δ (-501 * ε))
        ((fun cell => paramsOfDyadicCell δ cell) ''
          ((a9.perSquare Q hQ).fineTubes_norm p : Set (DyadicTubeCell δ)))) ∧
    (∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0) (p : EuclideanPlane)
        (hp : p ∈ (a9.perSquare Q hQ).P_norm_Q),
      IsRescalableDeltaSet δ Δ s (Real.rpow Δ (-501 * ε))
        ((fun cell => toPlane' (paramsOfDyadicCell δ cell)) ''
          ((a9.perSquare Q hQ).fineTubes_norm p : Set (DyadicTubeCell δ)))) := by
  have h_prod : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0) (p : EuclideanPlane)
      (hp : p ∈ (a9.perSquare Q hQ).P_norm_Q),
      IsRescalableDeltaSet δ Δ s (Real.rpow Δ (-501 * ε))
        ((fun cell => paramsOfDyadicCell δ cell) ''
          ((a9.perSquare Q hQ).fineTubes_norm p : Set (DyadicTubeCell δ))) := by
    intro Q hQ p hp
    let sq := a9.perSquare Q hQ
    have h1 : IsRescalableDeltaSet δ Δ s sq.C_fine_resc _ := sq.hfine_rescalable_prod p hp
    have h2 : sq.C_fine_resc ≤ Real.rpow Δ (-501 * ε) := by
      have h3 : 16 * sq.C_fine_resc ≤ Real.rpow Δ (-501 * ε) := hC_le Q hQ
      have h4 : 0 < sq.C_fine_resc := sq.hC_fine_resc_pos
      linarith
    exact IsRescalableDeltaSet.mono_const h1 h2
  have h_plane : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0) (p : EuclideanPlane)
      (hp : p ∈ (a9.perSquare Q hQ).P_norm_Q),
      IsRescalableDeltaSet δ Δ s (Real.rpow Δ (-501 * ε))
        ((fun cell => toPlane' (paramsOfDyadicCell δ cell)) ''
          ((a9.perSquare Q hQ).fineTubes_norm p : Set (DyadicTubeCell δ))) := by
    intro Q hQ p hp
    let sq := a9.perSquare Q hQ
    let S := (fun cell => paramsOfDyadicCell δ cell) ''
      (sq.fineTubes_norm p : Set (DyadicTubeCell δ))
    have h1 : IsRescalableDeltaSet δ Δ s sq.C_fine_resc S := sq.hfine_rescalable_prod p hp
    have h2 : IsRescalableDeltaSet δ Δ s (16 * sq.C_fine_resc) (toPlane' '' S) :=
      IsRescalableDeltaSet.prod_to_plane h1
    have h3 : (toPlane' '' S) =
        (fun cell => toPlane' (paramsOfDyadicCell δ cell)) ''
          (sq.fineTubes_norm p : Set (DyadicTubeCell δ)) := by
      rw [Set.image_image]
      <;> rfl
    rw [h3] at h2
    have h4 : 16 * sq.C_fine_resc ≤ Real.rpow Δ (-501 * ε) := hC_le Q hQ
    exact IsRescalableDeltaSet.mono_const h2 h4
  exact ⟨h_prod, h_plane⟩

end DirecretisedFurstenbergEstimate.A10
