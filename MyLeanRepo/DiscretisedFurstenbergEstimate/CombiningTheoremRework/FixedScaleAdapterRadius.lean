module

/-
  apply_appendix_a_to_dyadic_at_radius

  Variant of apply_appendix_a_to_dyadic that takes deltaA and the already-unpacked
  Appendix A body directly, avoiding re-existentialization of deltaA.

  This is useful when deltaA is known from upstream (e.g., appendix_a_main) and
  needs to be threaded through the proof without losing its identity.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CarrierTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicToAffineAdapters
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge_SSetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.FixedScaleAdapter
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal Classical

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence
open DirecretisedFurstenbergEstimate.CarrierTransfer
open DyadicToAffineAdapters
open DyadicCardToNcover
open DiscretisedFurstenbergEstimate.InductionOnScales
open DiscretisedFurstenbergEstimate.FixedScaleAdapter

/-- Variant of `apply_appendix_a_to_dyadic` that takes `deltaA` and the
    already-unpacked Appendix A body directly.

    Instead of returning `∃ δA, ... (9δ_n ≤ δA → disjunction)`, this returns
    the disjunction directly given `h9δn_le_deltaA`.
-/
lemma apply_appendix_a_to_dyadic_at_radius
    {n m : ℕ} (hnm : m ≤ n) (h_even : n = 2 * m)
    {s t u : ℝ} (hs_pos : 0 < s) (hs_lt_one : s < 1) (hst : s < t) (hu_t : t ≤ u) (hu_two : u ≤ 2)
    {C_P K_P C_T : ℝ}
    {P : Set DirecretisedFurstenbergEstimate.EuclideanPlane}
    (hP_bdd : P ⊆ Metric.closedBall 0 1)
    (hP_regular : IsSquareRootRegular (dyadicDelta n) u C_P K_P P)
    {tubeFamily : (p : DirecretisedFurstenbergEstimate.EuclideanPlane) → p ∈ P → Finset (DyadicTube n)}
    (hTubes_sset : ∀ p hp, IsDeltaSSet (dyadicDelta n) s C_T (tubeFamily p hp : Set (DyadicTube n)))
    (h_slope_bound : ∀ p hp, ∀ T ∈ tubeFamily p hp, |T.slope| ≤ 1)
    (h_intercept_bound : ∀ p hp, ∀ T ∈ tubeFamily p hp, |T.intercept| ≤ 3)
    (hIncidence : ∀ p hp, ∀ T ∈ tubeFamily p hp,
      ∃ (Q : DyadicSquare n),
        p ∈ (Q.toSet : Set DirecretisedFurstenbergEstimate.EuclideanPlane) ∧
          (T.toSet ∩ Q.toSet).Nonempty)
    (hCT_one : 1 ≤ C_T)
    (εA : ℝ) (hεA_pos : 0 < εA)
    (deltaA : ℝ) (hδA_pos : 0 < deltaA) (hδA_one : deltaA ≤ 1)
    (h_body : ∀ (u : ℝ), t ≤ u → u ≤ 2 →
      ∀ {δ : ℝ}, 0 < δ → δ ≤ deltaA →
      ∀ (P : Set DirecretisedFurstenbergEstimate.EuclideanPlane),
        P ⊆ Metric.closedBall 0 1 →
        IsDeltaSSet δ u (Real.rpow δ (-εA)) P →
        RegularIncidence.Ncover (Real.sqrt δ) P ≤
          ENNReal.ofReal (Real.rpow δ (-(u / 2 + εA))) →
        ∀ (tubeFamily :
            (p : DirecretisedFurstenbergEstimate.EuclideanPlane) → p ∈ P → Set AffineLine),
          (∀ p hp, IsDeltaSSet δ s (Real.rpow δ (-εA)) (tubeFamily p hp)) →
          (∀ p hp, ∀ T ∈ tubeFamily p hp, p ∈ Metric.cthickening δ (T.1)) →
          let allTubes := ⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp
          ENNReal.ofReal (Real.rpow δ (-(2 * s + εA))) ≤
              RegularIncidence.Ncover δ allTubes ∨
            ENNReal.ofReal (Real.rpow δ (-(s + εA))) ≤
              RegularIncidence.Ncover (Real.sqrt δ) allTubes)
    (h_absorb_point : C_P * 361 ≤ Real.rpow (9 * dyadicDelta n) (-εA))
    (h_absorb_sqrt  : K_P * (9 : ℝ)^(u / 2) ≤ Real.rpow (9 * dyadicDelta n) (-εA))
    (h_absorb_tube  : max 1 (10 * C_T) * 628849 * 44^s ≤ Real.rpow (9 * dyadicDelta n) (-εA))
    (h9δn_le_deltaA : 9 * dyadicDelta n ≤ deltaA) :
    (ENNReal.ofReal (Real.rpow (9 * dyadicDelta n) (-(2 * s + εA))) ≤
      RegularIncidence.Ncover (9 * dyadicDelta n)
        (⋃ p, ⋃ hp : p ∈ P, toAffineLine '' (tubeFamily p hp : Set (DyadicTube n))))
    ∨
    (ENNReal.ofReal (Real.rpow (9 * dyadicDelta n) (-(s + εA))) ≤
      RegularIncidence.Ncover (Real.sqrt (9 * dyadicDelta n))
        (⋃ p, ⋃ hp : p ∈ P, toAffineLine '' (tubeFamily p hp : Set (DyadicTube n)))) := by
  set δ := dyadicDelta n with hδ_def
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  set δ' := 9 * δ with hδ'_def
  have hδ'_pos : 0 < δ' := by positivity
  have hP_bdd' : Bornology.IsBounded P := Metric.isBounded_closedBall.subset hP_bdd

  -- Step 1: Convert point S-set from δ to δ'
  have hP_delta : IsDeltaSSet δ u C_P P := hP_regular.to_isDeltaSSet
  have hP_scaled : IsDeltaSSet δ' u (C_P * 361) P :=
    point_sset_scale hδ_pos hP_bdd' hP_delta
  have hP_final : IsDeltaSSet δ' u (Real.rpow δ' (-εA)) P :=
    IsDeltaSSet.weaken_C hP_scaled h_absorb_point

  -- Step 2: Convert sqrt covering bound
  have h_sqrt_orig : RegularIncidence.Ncover (Real.sqrt δ) P ≤
      ENNReal.ofReal (K_P * Real.rpow δ (-u / 2)) := hP_regular.ncover_sqrt_le
  have hδ_leδ' : δ ≤ δ' := by linarith [hδ_pos]
  have hsqrt_le : Real.sqrt δ ≤ Real.sqrt δ' := Real.sqrt_le_sqrt hδ_leδ'
  have h_sqrt_antitone :
      RegularIncidence.Ncover (Real.sqrt δ') P ≤ RegularIncidence.Ncover (Real.sqrt δ) P := by
    have h_le : (Real.sqrt δ).toNNReal ≤ (Real.sqrt δ').toNNReal := by exact Real.toNNReal_mono hsqrt_le
    simpa [RegularIncidence.Ncover] using Metric.externalCoveringNumber_anti h_le
  have h_sqrt_eq : Real.rpow δ (-u / 2) = (9 : ℝ)^(u / 2) * Real.rpow δ' (-u / 2) := by
    have h1 : Real.rpow δ' (-u / 2) = (9 : ℝ)^(-u / 2) * Real.rpow δ (-u / 2) :=
      Real.mul_rpow (by norm_num) (by linarith)
    have h3 : (9 : ℝ)^(u / 2) * (9 : ℝ)^(-u / 2) = (1 : ℝ) := by
      have h4 : (9 : ℝ)^(u / 2) * (9 : ℝ)^(-u / 2) = (9 : ℝ)^((u / 2) + (-u / 2)) :=
        (Real.rpow_add (by norm_num) (u / 2) (-u / 2)).symm
      rw [h4]
      have h5 : (u / 2 : ℝ) + (-u / 2) = 0 := by ring
      rw [h5] <;> simp
    have h6 : Real.rpow δ (-u / 2) =
        (9 : ℝ)^(u / 2) * ((9 : ℝ)^(-u / 2) * Real.rpow δ (-u / 2)) := by
      have h7 : (9 : ℝ)^(u / 2) * (9 : ℝ)^(-u / 2) = (1 : ℝ) := h3
      have h8 : (9 : ℝ)^(u / 2) * ((9 : ℝ)^(-u / 2) * Real.rpow δ (-u / 2)) =
          ((9 : ℝ)^(u / 2) * (9 : ℝ)^(-u / 2)) * Real.rpow δ (-u / 2) := by ring
      rw [h8, h7] <;> ring
    rw [h6, ←h1] <;> ring
  have h_sqrt_final : RegularIncidence.Ncover (Real.sqrt δ') P ≤
      ENNReal.ofReal (Real.rpow δ' (-εA) * Real.rpow δ' (-u / 2)) := by
    calc RegularIncidence.Ncover (Real.sqrt δ') P
      ≤ RegularIncidence.Ncover (Real.sqrt δ) P := h_sqrt_antitone
    _ ≤ ENNReal.ofReal (K_P * Real.rpow δ (-u / 2)) := h_sqrt_orig
    _ = ENNReal.ofReal (K_P * (9 : ℝ)^(u / 2) * Real.rpow δ' (-u / 2)) := by
      rw [h_sqrt_eq] <;> ring_nf
    _ ≤ ENNReal.ofReal (Real.rpow δ' (-εA) * Real.rpow δ' (-u / 2)) := by
      have h_pos : 0 ≤ Real.rpow δ' (-u / 2) := Real.rpow_nonneg hδ'_pos.le _
      have h_le : K_P * (9 : ℝ)^(u / 2) * Real.rpow δ' (-u / 2) ≤
          Real.rpow δ' (-εA) * Real.rpow δ' (-u / 2) :=
        mul_le_mul_of_nonneg_right h_absorb_sqrt h_pos
      exact ENNReal.ofReal_le_ofReal h_le

  have hP_regular' : IsSquareRootRegular δ' u (Real.rpow δ' (-εA)) (Real.rpow δ' (-εA)) P :=
    ⟨hP_final, h_sqrt_final⟩

  -- Step 3: Convert tube S-sets from DyadicTube at δ to AffineLine at δ'
  let tubeFamily' :
      (p : DirecretisedFurstenbergEstimate.EuclideanPlane) → p ∈ P → Set AffineLine :=
    fun p hp => toAffineLine '' (tubeFamily p hp : Set (DyadicTube n))
  have hTubes' : ∀ p hp, IsDeltaSSet δ' s (Real.rpow δ' (-εA)) (tubeFamily' p hp) := by
    intro p hp
    have h_orig : IsDeltaSSet δ s C_T (tubeFamily p hp : Set (DyadicTube n)) := hTubes_sset p hp
    have hm : ∀ T ∈ tubeFamily p hp, |T.slope| ≤ 1 := h_slope_bound p hp
    have hb : ∀ T ∈ tubeFamily p hp, |T.intercept| ≤ 3 := h_intercept_bound p hp
    have h_scaled : IsDeltaSSet δ' s (max 1 (10 * C_T) * 628849 * 44^s) (tubeFamily' p hp) :=
      toAffineLine_tubeSSet_transfer_9δ hs_pos.le hs_lt_one hCT_one hm hb h_orig
    have h_abs : max 1 (10 * C_T) * 628849 * 44^s ≤ Real.rpow δ' (-εA) := h_absorb_tube
    exact IsDeltaSSet.weaken_C h_scaled h_abs

  -- Step 4: Convert incidence to 9δ
  have hInc' : ∀ p hp, ∀ ℓ ∈ tubeFamily' p hp, p ∈ Metric.cthickening δ' (ℓ.1) := by
    intro p hp ℓ hℓ
    rcases hℓ with ⟨T, hT, rfl⟩
    rcases hIncidence p hp T hT with ⟨Q, hpQ, h_intersect⟩
    have h_slope : |T.slope| ≤ 1 := h_slope_bound p hp T hT
    exact point_in_square_near_affine_line_9δ T Q p hpQ h_intersect h_slope

  -- Step 5: Apply the body directly with the provided deltaA
  have hδ'_le : δ' ≤ deltaA := by
    dsimp only [δ', δ]
    exact h9δn_le_deltaA
  have h_sqrt_rpow : Real.rpow δ' (-εA) * Real.rpow δ' (-u / 2) =
      Real.rpow δ' (-(u / 2 + εA)) := by
    have h_add : Real.rpow δ' (-εA) * Real.rpow δ' (-u / 2) =
        Real.rpow δ' ((-εA) + (-u / 2)) := (Real.rpow_add hδ'_pos _ _).symm
    rw [h_add]
    have h_sum : (-εA) + (-u / 2) = -(u / 2 + εA) := by ring
    rw [h_sum]
  have h_sqrt_bound : RegularIncidence.Ncover (Real.sqrt δ') P ≤
      ENNReal.ofReal (Real.rpow δ' (-(u / 2 + εA))) := by
    rw [←h_sqrt_rpow]
    exact h_sqrt_final
  have hsu' : t ≤ u := hu_t
  exact h_body u hsu' hu_two hδ'_pos hδ'_le P hP_bdd hP_final h_sqrt_bound
    tubeFamily' hTubes' hInc'

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
