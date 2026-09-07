import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SingleTubeGlobalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SingleTubeLocalAD
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierVolumeLower
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import Mathlib.Tactic

/-!
# Single-tube grain data construction

Direct construction of `PureWZ2LocalGrainData` and
`PureWZ2LipschitzGlobalGrainData` for a single-tube configuration, WITHOUT
dilation or relaxed pre-grain bounds.

## Key idea

For a single tube:
- **planeMap**: constant `horizontalPerpendicular(d)` — Lipschitz 0, incidence 0
- **local AD**: projection onto perpendicular has diameter ≤ 14δ, so C ≥ 16 suffices
- **global AD**: horizontal slice has diameter ≤ 42δ, so any projection has
  diameter ≤ 42δ, hence C ≥ 44 suffices
- **slope**: constant 0 — Lipschitz 0

These tight bounds (Lipschitz 1, incidence δ) satisfy the grain conclusion
directly, avoiding the dilation route entirely.

## Dependencies

- `SingleTubeGlobalAD.lean`: `horizontalPerpendicular`, `tube_slice_diameter_bound`
- `SingleTubeLocalAD.lean`: `tube_projection_perpendicular_diameter`,
  `bounded_diameter_ad_simple`
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set MeasureTheory Classical

attribute [local instance] Classical.propDecidable

/-- Scalar projection is monotone in the set argument. -/
private lemma scalarProjection_mono {v : Point3} {A B : Set Point3} (h : A ⊆ B) :
    scalarProjection v A ⊆ scalarProjection v B := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

/-- Construct local grain data for a shading contained in a single paper tube.

The plane map is the constant horizontal perpendicular to the tube direction.
The local AD follows from the projection diameter bound of 14δ.

Requires `C ≥ 16` to absorb the covering-number constant. -/
def single_tube_local_grain_data
    {delta sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (i : Fin F.card)
    (hdir : (F.tube i).direction 0 ≠ 0 ∨ (F.tube i).direction 1 ≠ 0)
    (hS_sub : S.union ⊆ wz1PaperTubeCarrier (F.tube i))
    (honly : ∀ (j : Fin F.card), S.carrier j ≠ ∅ → j = i)
    (hdelta_pos : 0 < delta)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    {C : ENNReal}
    (hC_ge16 : (16 : ENNReal) ≤ C)
    (hC_top : C ≠ ⊤) :
    PureWZ2LocalGrainData S sigma C :=
  let T := F.tube i
  let v := horizontalPerpendicular T.direction hdir
  let hv_spec := horizontalPerpendicular_spec T.direction hdir
  { planeMap := fun (_ : {point : Point3 // point ∈ S.union}) => v
  , planeMap_lipschitz := by
      intro x y
      simp [edist_dist]
      <;> exact zero_le _
  , planeMap_unit := fun _ => hv_spec.1
  , planeMap_incidence := by
      intro index point hpoint
      have hne : S.carrier index ≠ ∅ := by
        intro h
        rw [h] at hpoint
        exact hpoint
      have hji : index = i := honly index hne
      have hdir_eq : (F.tube index).direction = T.direction := by
        rw [hji]
        <;> rfl
      have h_inner : inner ℝ (F.tube index).direction v = 0 := by
        rw [hdir_eq]
        exact hv_spec.2.1
      rw [h_inner]
      have h0 : |(0 : ℝ)| ≤ delta := by
        simpa using hdelta_pos.le
      exact h0
  , local_ad := by
      intro rho hrho_ge hrho_le point
      let E := scalarProjection v
          (S.union ∩ Metric.closedBall (point : Point3) (Real.sqrt rho))
      have hE_sub : E ⊆ scalarProjection v (wz1PaperTubeCarrier T) :=
        scalarProjection_mono (Set.inter_subset_left.trans hS_sub)
      have h_diam : ∀ (x y : ℝ), x ∈ E → y ∈ E → |x - y| ≤ 14 * delta := by
        intro x y hx hy
        exact tube_projection_perpendicular_diameter
          hdelta_pos T v hv_spec.1 hv_spec.2.1 x y
          (hE_sub hx) (hE_sub hy)
      have hC_ge : ENNReal.ofReal (14 + 2 : ℝ) ≤ C := by
        have h1 : (14 + 2 : ℝ) = (16 : ℝ) := by norm_num
        rw [h1]
        simpa using hC_ge16
      exact bounded_diameter_ad_simple
        (14 : ℝ) (by norm_num) hdelta_pos
        (by linarith) hrho_ge
        (by linarith) (by linarith)
        hC_ge hC_top h_diam
  }

/-- Construct global grain data for a shading contained in a single paper tube.

The slope is constant 0. The global AD follows from the horizontal slice
diameter bound of 42δ.

Requires `C ≥ 44` to absorb the covering-number constant. -/
def single_tube_global_grain_data
    {delta sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (i : Fin F.card)
    (hdir_vertical : 1 / 2 ≤ |(F.tube i).direction (2 : Fin 3)|)
    (hS_sub : S.union ⊆ wz1PaperTubeCarrier (F.tube i))
    (hdelta_pos : 0 < delta)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    {C : ENNReal}
    (hC_ge44 : (44 : ENNReal) ≤ C)
    (hC_top : C ≠ ⊤) :
    PureWZ2LipschitzGlobalGrainData S sigma C :=
  let T := F.tube i
  PureWZ2LipschitzGlobalGrainData.ofRealFunction
    (fun (_ : ℝ) => 0) (by
      intro x _ y _
      simp [edist_dist]
      <;> exact zero_le _) (by
      intro z hz
      let E := scalarProjection (globalGrainDirection (0 : ℝ))
          (horizontalSlice S.union z)
      have h_slice_sub : horizontalSlice S.union z ⊆
          horizontalSlice (wz1PaperTubeCarrier T) z := by
        intro p hp
        exact ⟨hS_sub hp.1, hp.2⟩
      have hE_sub : E ⊆ scalarProjection (globalGrainDirection (0 : ℝ))
          (horizontalSlice (wz1PaperTubeCarrier T) z) :=
        scalarProjection_mono h_slice_sub
      have h_diam : ∀ (x y : ℝ), x ∈ E → y ∈ E → |x - y| ≤ 42 * delta := by
        intro x y hx hy
        rcases hE_sub hx with ⟨p, hp, rfl⟩
        rcases hE_sub hy with ⟨q, hq, rfl⟩
        have h_dist : dist p q ≤ 42 * delta :=
          tube_slice_diameter_bound hdelta_pos T hdir_vertical z p q hp hq
        have h_inner : |inner ℝ p (globalGrainDirection (0 : ℝ)) -
            inner ℝ q (globalGrainDirection (0 : ℝ))| ≤
            ‖p - q‖ * ‖globalGrainDirection (0 : ℝ)‖ := by
          have h : inner ℝ (p - q) (globalGrainDirection (0 : ℝ)) =
              inner ℝ p (globalGrainDirection (0 : ℝ)) -
              inner ℝ q (globalGrainDirection (0 : ℝ)) := by
            rw [inner_sub_left]
          rw [←h]
          exact abs_real_inner_le_norm _ _
        have h_norm_dir : ‖globalGrainDirection (0 : ℝ)‖ = 1 := by
          simp [globalGrainDirection, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
          <;> norm_num
        rw [h_norm_dir] at h_inner
        have h_norm : ‖p - q‖ = dist p q := by
          simp [dist_eq_norm]
        rw [h_norm] at h_inner
        linarith
      have hC_ge : ENNReal.ofReal (42 + 2 : ℝ) ≤ C := by
        have h1 : (42 + 2 : ℝ) = (44 : ℝ) := by norm_num
        rw [h1]
        simpa using hC_ge44
      exact bounded_diameter_ad_simple
        (42 : ℝ) (by norm_num) hdelta_pos
        hdelta_pos (by linarith)
        (by linarith) (by linarith)
        hC_ge hC_top h_diam)

/-- Density selection: if a shading is λ-dense, there exists a tube whose
individual carrier satisfies the density bound.

Proof by contradiction: if every tube falls below the density threshold,
summing over all tubes contradicts the aggregate density condition. -/
lemma exists_tube_satisfying_density
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    {lambda : ENNReal}
    (h_dense : S.IsLambdaDense lambda)
    (h_nonempty : F.Nonempty) :
    ∃ (i : Fin F.card),
      lambda * ((wz1PaperBodyFamily F).body i).volume ≤
        volume (S.carrier i) := by
  by_contra h
  push Not at h
  have h_strict : ∀ (i : Fin F.card),
      volume (S.carrier i) < lambda * ((wz1PaperBodyFamily F).body i).volume := by
    intro i
    exact h i
  have h_fin_nonempty : Nonempty (Fin F.card) := by
    exact Fin.pos_iff_nonempty.mp h_nonempty
  have h_univ_nonempty : (Finset.univ : Finset (Fin F.card)).Nonempty := by
    exact Finset.univ_nonempty
  have h_sum : ∑ i : Fin F.card, volume (S.carrier i) <
      ∑ i : Fin F.card, lambda * ((wz1PaperBodyFamily F).body i).volume :=
    ENNReal.sum_lt_sum_of_nonempty h_univ_nonempty (fun i _ => h_strict i)
  have h_mul_sum : ∑ i : Fin F.card, lambda * ((wz1PaperBodyFamily F).body i).volume =
      lambda * ∑ i : Fin F.card, ((wz1PaperBodyFamily F).body i).volume := by
    rw [Finset.mul_sum]
  rw [h_mul_sum] at h_sum
  have h_contra : (∑ i : Fin F.card, volume (S.carrier i)) <
      (∑ i : Fin F.card, volume (S.carrier i)) :=
    lt_of_lt_of_le h_sum h_dense
  exact lt_irrefl _ h_contra

/-- Top-level Convex Wolff bound for a single-tube family.

For outputLoss ≥ 2, any convex set containing the paper tube has volume
≥ 2 * δ², so `C * volume ≥ δ^(-outputLoss) * 2 * δ² = 2 * δ^(2-outputLoss) ≥ 2 ≥ 1`,
which dominates the contained count (0 or 1). -/
lemma single_tube_top_level_cwa
    {delta outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (hF_card : F.card = 1)
    (hdelta_pos : 0 < delta)
    (hdelta_small : delta ≤ 1 / 12)
    (hline : WZ1PaperIsLineClass F)
    (hloss_ge_two : 2 ≤ outputLoss) :
    WZ2PaperConvexWolffBound F
      (Kakeya.realRpowENN delta (-outputLoss)) := by
  intro convexSet hconvex
  let B := wz1PaperBodyFamily F
  have h_card1 : (Finset.univ : Finset (Fin F.card)).card = 1 := by
    simp [hF_card]
  have h_count_le_one : B.containedCount convexSet ≤ 1 := by
    have h2 : (B.containedIndices convexSet) ⊆ (Finset.univ : Finset (Fin F.card)) := Finset.subset_univ _
    have h3 : (B.containedIndices convexSet).card ≤ (Finset.univ : Finset (Fin F.card)).card := Finset.card_le_card h2
    have h4 : (Finset.univ : Finset (Fin F.card)).card = 1 := h_card1
    have h5 : (B.containedIndices convexSet).card ≤ 1 := by rw [h4] at h3; exact h3
    have h6 : B.containedCount convexSet = ((B.containedIndices convexSet).card : ENNReal) := by rfl
    rw [h6]
    exact_mod_cast h5
  by_cases h_count : B.containedCount convexSet = 0
  · rw [h_count]
    <;> simp
  · have h_n_le_one : (B.containedIndices convexSet).card ≤ 1 := by
      have h3 : (B.containedIndices convexSet) ⊆ (Finset.univ : Finset (Fin F.card)) := Finset.subset_univ _
      have h4 : (B.containedIndices convexSet).card ≤ (Finset.univ : Finset (Fin F.card)).card := Finset.card_le_card h3
      rw [h_card1] at h4
      exact h4
    have h_n_ne_zero : (B.containedIndices convexSet).card ≠ 0 := by
      intro h6
      have h7 : B.containedCount convexSet = 0 := by
        have h8 : B.containedCount convexSet = ((B.containedIndices convexSet).card : ENNReal) := by
          rfl
        rw [h8, h6] <;> simp
      exact h_count h7
    have h_n_eq_one : (B.containedIndices convexSet).card = 1 := by omega
    have h_count_eq_one : B.containedCount convexSet = 1 := by
      have h8 : B.containedCount convexSet = ((B.containedIndices convexSet).card : ENNReal) := by rfl
      rw [h8, h_n_eq_one] <;> norm_num
    have h_nonempty : (B.containedIndices convexSet).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h_empty
      have h9 : (B.containedIndices convexSet).card = 0 := by
        exact Finset.card_eq_zero.mpr h_empty
      exact h_n_ne_zero h9
    rcases h_nonempty with ⟨i, hi⟩
    have h_i_in : (B.body i).carrier ⊆ convexSet := by
      have h_mem : i ∈ B.containedIndices convexSet := hi
      rw [Streamlined.BodyFamily.mem_containedIndices_iff] at h_mem
      exact h_mem
    have h_exists : ∃ (i : Fin F.card), (B.body i).carrier ⊆ convexSet := ⟨i, h_i_in⟩
    rcases h_exists with ⟨i, hi⟩
    have h_vol : volume (B.body i).carrier ≤ volume convexSet :=
      measure_mono hi
    have hline_i : WZ1PaperTubeInLineClass (F.tube i) := hline i
    have h_lower : Kakeya.deltaTubeVolume delta ≤ volume (B.body i).carrier :=
      Kakeya.Assouad.wz2PaperTubeCarrier_volume_lower hdelta_pos hdelta_small (F.tube i) hline_i
    have h_fine_lower : ENNReal.ofReal (2 * delta^2) ≤ Kakeya.deltaTubeVolume delta :=
      Kakeya.Streamlined.tube_volume_ge_two_delta_sq delta hdelta_pos
    have h_vol_lower : ENNReal.ofReal (2 * delta^2) ≤ volume convexSet :=
      h_fine_lower.trans (h_lower.trans h_vol)
    let C := Kakeya.realRpowENN delta (-outputLoss)
    have hC_pos : 0 < C := by
      simp only [C, Kakeya.realRpowENN]
      exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta_pos _)
    have h_delta_le_one : delta ≤ 1 := by linarith
    have h_exp_nonpos : 2 - outputLoss ≤ 0 := by linarith
    have h_rpow_ge_one : (1 : ENNReal) ≤ C * ENNReal.ofReal (2 * delta^2) := by
      have h_nonneg1 : 0 ≤ Real.rpow delta (-outputLoss) := Real.rpow_nonneg (by linarith) _
      have h_nonneg2 : 0 ≤ 2 * delta^2 := by positivity
      have h_mul : Real.rpow delta (-outputLoss) * (2 * delta^2) =
          2 * Real.rpow delta (2 - outputLoss) := by
        have h4 : Real.rpow delta (-outputLoss) * delta^2 =
            Real.rpow delta (2 - outputLoss) := by
          have h41 : (delta^2 : ℝ) = Real.rpow delta 2 := by
            simp [Real.rpow_two]
          have h42 : Real.rpow delta (-outputLoss) * Real.rpow delta 2 =
              Real.rpow delta (2 - outputLoss) := by
            have h : Real.rpow delta ((-outputLoss) + 2) =
                Real.rpow delta (-outputLoss) * Real.rpow delta 2 := Real.rpow_add hdelta_pos (-outputLoss) 2
            have h43 : (-outputLoss) + 2 = 2 - outputLoss := by ring
            rw [h43] at h
            exact h.symm
          rw [h41]
          exact h42
        calc
          Real.rpow delta (-outputLoss) * (2 * delta^2)
            = 2 * (Real.rpow delta (-outputLoss) * delta^2) := by ring
          _ = 2 * Real.rpow delta (2 - outputLoss) := by rw [h4]
      have h5 : 1 ≤ 2 * Real.rpow delta (2 - outputLoss) := by
        have h6 : 1 ≤ Real.rpow delta (2 - outputLoss) :=
          Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta_pos h_delta_le_one h_exp_nonpos
        linarith
      have h7 : C * ENNReal.ofReal (2 * delta^2) =
          ENNReal.ofReal (Real.rpow delta (-outputLoss) * (2 * delta^2)) := by
        simp only [C, Kakeya.realRpowENN]
        rw [ENNReal.ofReal_mul h_nonneg1]
        <;> rfl
      rw [h7, h_mul]
      have h9 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by norm_num
      rw [h9]
      exact ENNReal.ofReal_le_ofReal h5
    have h_main : (1 : ENNReal) ≤ C * volume convexSet := by
      calc (1 : ENNReal)
        ≤ C * ENNReal.ofReal (2 * delta^2) := h_rpow_ge_one
      _ ≤ C * volume convexSet := by gcongr
    have h_enncard : F.enncard = (1 : ENNReal) := by
      have h1 : F.enncard = (F.card : ENNReal) := by
        rfl
      rw [h1, hF_card]
      <;> norm_num
    rw [h_count_eq_one, h_enncard]
    <;> simpa using h_main

end Kakeya.Assouad

end
