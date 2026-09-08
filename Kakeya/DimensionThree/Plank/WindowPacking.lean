/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabAssignment
public import Kakeya.DimensionThree.Plank.ThickenedGeometry
public import Kakeya.DimensionThree.Plank.Geometry

/-!
# Window packing: how many essentially distinct planks fit in the Section 6 window

`Kakeya.plankReduction` feeds GWZ Lemma 6.11
(`Kakeya.findingTypicalAngleOfIntersection_stable_reserve`),
whose plank-count hypothesis is `(s.card : ℝ≥0) ≤ C₀ · a ^ (-Nexp)` with `C₀` and `Nexp` fixed
*before* the configuration.  Lemma 6.13 does not carry such a bound as a hypothesis; it is a
consequence of the two geometric hypotheses it does carry, namely that the family lies in the fixed
working window (`Plank.IsWindowedFamily`) and that its members are pairwise essentially distinct.
This file supplies that missing input.

The argument is the pose-packing argument already used for the fibre bound
(`Plank.ThickenedRepr.phi_packing_bound`), with the confinement coming from the window rather than
from a common containing prism:

* *Confinement.*  A plank of a windowed family has its centre in the window, so `‖cⱼ‖ ≤ 4`.  Reading
  the nine frame entries and three centre coordinates in the fixed reference frame
  `EuclideanSpace.basisFun` with the normalisations `96/a` and `48/a` confines all twelve pose
  coordinates to `K = 192/a`.
* *Separation.*  The contrapositive of `Plank.plank_not_essentiallyDistinct_of_pose_close`:
  essentially distinct planks fail one of that lemma's two closeness conditions, and both are
  implied by pose distance `≤ 1` at this normalisation since every half-width lies in `[a, 1]`.
  So `r = 1`.

`Plank.card_le_of_pose_confined_separated` then gives
`s.card ≤ (8K + 2)^12 = (1536/a + 2)^12 ≤ (1538/a)^12`, i.e. `Plank.windowPackingConst · a^(-12)`.

No lower threshold `a₀ ≤ a` is needed: the conclusion is allowed to degrade polynomially in `a⁻¹`,
which is exactly the shape Lemma 6.11 consumes.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}

/-! ## Frame comparison through a reference frame -/

/-- **Off-diagonal frame comparison through a reference frame.** For `p ≠ k` the inner product
`⟪e p, e' k⟫` vanishes when `e' = e` (orthonormality), so it is controlled by the reference-frame
coordinate differences of the two frames along the row `k`. -/
private lemma wp_abs_inner_offdiag_le_frame_diff
    (f e e' : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) {p k : Fin 3} (hpk : p ≠ k) :
    |inner ℝ (e p) (e' k)|
      ≤ ∑ m : Fin 3, |inner ℝ (e' k) (f m) - inner ℝ (e k) (f m)| := by
  have hunit : ∀ m : Fin 3, |inner ℝ (e p) (f m)| ≤ 1 := by
    intro m
    have h := abs_real_inner_le_norm (e p) (f m)
    rwa [e.norm_eq_one p, f.norm_eq_one m, mul_one] at h
  have hcomm : ∀ (u : EuclideanSpace ℝ (Fin 3)) (m : Fin 3),
      (inner ℝ u (f m) : ℝ) = inner ℝ (f m) u := fun u m => real_inner_comm (f m) u
  have hexp : (inner ℝ (e p) (e' k) : ℝ)
      = ∑ m : Fin 3, (inner ℝ (e' k) (f m) - inner ℝ (e k) (f m)) * inner ℝ (e p) (f m) := by
    simp only [sub_mul, Finset.sum_sub_distrib, hcomm (e' k), hcomm (e k)]
    rw [← inner_eq_sum_frame f (e p) (e' k), ← inner_eq_sum_frame f (e p) (e k),
      e.inner_eq_zero hpk, sub_zero]
  rw [hexp]
  calc |∑ m : Fin 3, (inner ℝ (e' k) (f m) - inner ℝ (e k) (f m)) * inner ℝ (e p) (f m)|
      ≤ ∑ m : Fin 3, |(inner ℝ (e' k) (f m) - inner ℝ (e k) (f m)) * inner ℝ (e p) (f m)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m : Fin 3, |inner ℝ (e' k) (f m) - inner ℝ (e k) (f m)| := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hunit m)

/-- **Offset comparison through a reference frame.** Any frame coordinate of a vector is bounded by
the sum of its reference-frame coordinates. -/
private lemma wp_abs_inner_offset_le_frame_sum
    (f e' : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) (k : Fin 3)
    (d : EuclideanSpace ℝ (Fin 3)) :
    |inner ℝ (e' k) d| ≤ ∑ m : Fin 3, |inner ℝ (f m) d| := by
  have hunit : ∀ m : Fin 3, |inner ℝ (e' k) (f m)| ≤ 1 := by
    intro m
    have h := abs_real_inner_le_norm (e' k) (f m)
    rwa [e'.norm_eq_one k, f.norm_eq_one m, mul_one] at h
  rw [inner_eq_sum_frame f (e' k) d]
  calc |∑ m : Fin 3, inner ℝ (f m) d * inner ℝ (e' k) (f m)|
      ≤ ∑ m : Fin 3, |inner ℝ (f m) d * inner ℝ (e' k) (f m)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m : Fin 3, |inner ℝ (f m) d| := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hunit m)

/-- Every plank half-width is at most `1`. -/
private lemma wp_width_le_one {a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1) (p : Fin 3) :
    ((![a, b, 1] p : ℝ≥0) : ℝ) ≤ 1 := by
  have ha1 : a ≤ 1 := hab.trans hb1
  fin_cases p <;> simp [ha1, hb1]

/-- Every plank half-width is at least the shortest one, `a`. -/
private lemma wp_width_ge {a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1) (k : Fin 3) :
    (a : ℝ) ≤ ((![a, b, 1] k : ℝ≥0) : ℝ) := by
  have ha1 : a ≤ 1 := hab.trans hb1
  fin_cases k <;> simp [hab, ha1]

/-- A prism contains its own centre. -/
private lemma wp_center_mem_carrier {n : ℕ}
    (P : PrismNDim n (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))) :
    P.center ∈ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  rw [P.mem_carrier_iff]
  intro k
  simp

/-! ## The window packing bound -/

/-- **The window plank-packing constant.**  At most `windowPackingConst · a ^ (-12)` pairwise
essentially distinct `a × b × 1` planks fit in the fixed Section 6 window
(`Plank.card_le_of_windowed_essentiallyDistinct`).  It is `(8K + 2)^12 ≤ (1538/a)^12` with
`K = 192/a` the pose-confinement radius and pose separation scale `1`; the `a`-dependence is carried
by the declared exponent `Plank.windowPackingExp`, so the constant itself is absolute. -/
def windowPackingConst : ℝ≥0 := 1538 ^ 12

/-- **The window plank-packing exponent**, the dimension of the pose space.  See
`Plank.windowPackingConst`. -/
def windowPackingExp : ℝ := 12

/-- The window plank-packing constant is positive. -/
theorem windowPackingConst_pos : 0 < windowPackingConst := by
  unfold windowPackingConst
  norm_num

/-- The window plank-packing exponent is nonnegative. -/
theorem windowPackingExp_nonneg : 0 ≤ windowPackingExp := by
  unfold windowPackingExp
  norm_num

/-! ## The pose map and its two inputs

The packing engine `Plank.card_le_of_pose_confined_separated` needs exactly two facts about a
twelve-coordinate reading of the family: that the coordinates are confined, and that distinct
members are separated.  Both are isolated here so that the main proof is their composition. -/

/-- The fixed reference frame in which every plank pose is read. -/
private def wpFrame : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  EuclideanSpace.basisFun (Fin 3) ℝ

/-- The twelve pose coordinates of a plank: the nine entries of its frame against the fixed
reference frame `wpFrame`, normalised by `96 / a`, together with the three reference-frame
coordinates of its centre, normalised by `48 / a`.  Both normalisations are at the *shortest*
half-width `a`, which is the scale at which `Plank.plank_not_essentiallyDistinct_of_pose_close`
gives separation in every coordinate direction. -/
private def wpPose (Q : Plank a b hab hb1) : EuclideanSpace ℝ ((Fin 3 × Fin 3) ⊕ Fin 3) :=
  WithLp.toLp 2 (Sum.elim
    (fun pq : Fin 3 × Fin 3 => (96 / (a : ℝ)) * inner ℝ (Q.basis pq.1) (wpFrame pq.2))
    (fun q : Fin 3 =>
      (48 / (a : ℝ)) * inner ℝ (wpFrame q) (Q.center -ᵥ (0 : EuclideanSpace ℝ (Fin 3)))))

/-- The nine frame coordinates of `wpPose`. -/
private lemma wpPose_inl (Q : Plank a b hab hb1) (p q : Fin 3) :
    wpPose Q (Sum.inl (p, q)) = (96 / (a : ℝ)) * inner ℝ (Q.basis p) (wpFrame q) := by
  unfold wpPose
  rfl

/-- The three centre coordinates of `wpPose`. -/
private lemma wpPose_inr (Q : Plank a b hab hb1) (q : Fin 3) :
    wpPose Q (Sum.inr q)
      = (48 / (a : ℝ)) * inner ℝ (wpFrame q) (Q.center -ᵥ (0 : EuclideanSpace ℝ (Fin 3))) := by
  unfold wpPose
  rfl

/-- **Centre confinement.**  A plank of a windowed family contains its own centre, so that centre
lies in the window and has norm at most `windowRadius = 4`. -/
private lemma wp_center_norm_le (s : Finset ι) (P : ι → Plank a b hab hb1)
    (hwin : IsWindowedFamily s P) {j : ι} (hj : j ∈ s) :
    ‖(P j).center -ᵥ (0 : EuclideanSpace ℝ (Fin 3))‖ ≤ 4 := by
  have hmem : (P j).center ∈ ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    wp_center_mem_carrier (P j).toPrismNDim
  have hsubset : ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) windowRadius :=
    hwin j hj
  have hball : (P j).center ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) windowRadius :=
    hsubset hmem
  rw [Metric.mem_closedBall] at hball
  rw [dist_eq_norm_vsub] at hball
  simpa [windowRadius] using hball

/-- **Pose confinement.**  All twelve pose coordinates of a plank whose centre is within `4` of the
origin are bounded by `192 / a`: the nine frame entries by `96 / a` (Cauchy-Schwarz for unit
vectors) and the three centre coordinates by `48 · 4 / a`. -/
private lemma wpPose_abs_le (ha0 : 0 < a) (Q : Plank a b hab hb1)
    (hc : ‖Q.center -ᵥ (0 : EuclideanSpace ℝ (Fin 3))‖ ≤ 4)
    (p : (Fin 3 × Fin 3) ⊕ Fin 3) :
    |wpPose Q p| ≤ 192 / (a : ℝ) := by
  have ha0' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  rcases p with ⟨p, q⟩ | q
  · -- Frame branch: Sum.inl (p, q)
    rw [wpPose_inl]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 96 / (a : ℝ))]
    have h1 : |inner ℝ (Q.basis p) (wpFrame q)| ≤ 1 := by
      have h := abs_real_inner_le_norm (Q.basis p) (wpFrame q)
      rwa [Q.basis.norm_eq_one p, wpFrame.norm_eq_one q, mul_one] at h
    calc
      (96 / (a : ℝ)) * |inner ℝ (Q.basis p) (wpFrame q)|
          ≤ (96 / (a : ℝ)) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 96 / (a : ℝ) := by ring
      _ ≤ 192 / (a : ℝ) := div_le_div_of_nonneg_right (by norm_num : (96 : ℝ) ≤ 192) (by
          positivity : 0 ≤ (a : ℝ))
  · -- Centre branch: Sum.inr q
    rw [wpPose_inr]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 48 / (a : ℝ))]
    have h1 : |inner ℝ (wpFrame q) (Q.center -ᵥ (0 : EuclideanSpace ℝ (Fin 3)))| ≤ 4 := by
      calc
        |inner ℝ (wpFrame q) (Q.center -ᵥ (0 : EuclideanSpace ℝ (Fin 3)))|
            ≤ ‖wpFrame q‖ * ‖Q.center -ᵥ (0 : EuclideanSpace ℝ (Fin 3))‖ :=
          abs_real_inner_le_norm _ _
        _ = 1 * ‖Q.center -ᵥ (0 : EuclideanSpace ℝ (Fin 3))‖ := by rw [wpFrame.norm_eq_one q]
        _ = ‖Q.center -ᵥ (0 : EuclideanSpace ℝ (Fin 3))‖ := by ring
        _ ≤ 4 := hc
    calc
      (48 / (a : ℝ)) * |inner ℝ (wpFrame q) (Q.center -ᵥ (0 : EuclideanSpace ℝ (Fin 3)))|
          ≤ (48 / (a : ℝ)) * 4 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 192 / (a : ℝ) := by ring

/-- **Pose separation.**  Two planks whose poses are at distance at most `1` are not essentially
distinct.  This is the contrapositive form of the separation input: each of the twelve coordinates
then differs by at most `1`, which at the normalisations `96 / a` and `48 / a` gives frame
differences `≤ a / 96` and centre differences `≤ a / 48`; expanding through the reference frame
turns these into the two anisotropic hypotheses of
`Plank.plank_not_essentiallyDistinct_of_pose_close`. -/
private lemma wp_not_essentiallyDistinct_of_wpPose_dist_le_one (ha0 : 0 < a)
    (Q Q' : Plank a b hab hb1) (hd : dist (wpPose Q) (wpPose Q') ≤ 1) :
    ¬ PrismNDim.IsEssentiallyDistinct Q.toPrismNDim Q'.toPrismNDim := by
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have ha0' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  -- Coordinatewise closeness: for every p, |wpPose Q p - wpPose Q' p| ≤ 1
  have hcoord : ∀ p : (Fin 3 × Fin 3) ⊕ Fin 3, |wpPose Q p - wpPose Q' p| ≤ 1 := by
    intro p
    have h := PiLp.dist_apply_le (wpPose Q) (wpPose Q') p
    rw [Real.dist_eq] at h
    exact h.trans hd
  -- Frame differences: for every p, q, |inner ℝ (Q.basis p) (wpFrame q) - inner ℝ (Q'.basis p)
  -- (wpFrame q)| ≤ (a : ℝ) / 96
  have hfrmdiff : ∀ p q : Fin 3,
      |inner ℝ (Q.basis p) (wpFrame q) - inner ℝ (Q'.basis p) (wpFrame q)| ≤ (a : ℝ) / 96 := by
    intro p q
    have h := hcoord (Sum.inl (p, q))
    rw [wpPose_inl Q p q, wpPose_inl Q' p q, ← mul_sub, abs_mul,
      abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 96) ha0')] at h
    rw [div_mul_eq_mul_div, div_le_one ha0'] at h
    linarith
  -- Centre differences: for every q, |inner ℝ (wpFrame q) (Q.center -ᵥ Q'.center)| ≤ (a : ℝ) / 48
  have hcendiff : ∀ q : Fin 3,
      |inner ℝ (wpFrame q) (Q.center -ᵥ Q'.center)| ≤ (a : ℝ) / 48 := by
    intro q
    have h := hcoord (Sum.inr q)
    rw [wpPose_inr Q q, wpPose_inr Q' q, ← mul_sub, ← inner_sub_right,
      show (Q.center -ᵥ (0 : EuclideanSpace ℝ (Fin 3))) - (Q'.center -ᵥ (0 : EuclideanSpace ℝ
          (Fin 3)))
        = Q.center -ᵥ Q'.center from vsub_sub_vsub_cancel_right _ _ _,
      abs_mul, abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 48) ha0')] at h
    rw [div_mul_eq_mul_div, div_le_one ha0'] at h
    linarith
  -- Apply plank_not_essentiallyDistinct_of_pose_close with the two closeness conditions
  refine plank_not_essentiallyDistinct_of_pose_close ha0 hb0 Q Q' ?_ ?_
  · intro j k hjk
    have h1 : |inner ℝ (Q.basis j) (Q'.basis k)|
        ≤ ∑ m : Fin 3, |inner ℝ (Q'.basis k) (wpFrame m) - inner ℝ (Q.basis k) (wpFrame m)| :=
      wp_abs_inner_offdiag_le_frame_diff wpFrame Q.basis Q'.basis hjk
    rw [Fin.sum_univ_three] at h1
    have e0 := hfrmdiff k 0
    have e1 := hfrmdiff k 1
    have e2 := hfrmdiff k 2
    rw [abs_sub_comm] at e0 e1 e2
    have h2 : |inner ℝ (Q.basis j) (Q'.basis k)| ≤ (a : ℝ) / 32 := by linarith
    have hwj := wp_width_le_one hab hb1 j
    have hwk := wp_width_ge hab hb1 k
    nlinarith [mul_nonneg (sub_nonneg.mpr hwj) (abs_nonneg (inner ℝ (Q.basis j) (Q'.basis k)))]
  · intro k
    have h1 := wp_abs_inner_offset_le_frame_sum wpFrame Q'.basis k (Q.center -ᵥ Q'.center)
    rw [Fin.sum_univ_three] at h1
    have e0 := hcendiff 0
    have e1 := hcendiff 1
    have e2 := hcendiff 2
    have hwk := wp_width_ge hab hb1 k
    linarith

/-- **The numeric step.**  With confinement radius `K = 192 / a` and separation scale `r = 1`, the
packing engine's bound `(2 (4K + r) / r) ^ 12 = (8K + 2) ^ 12` is at most
`windowPackingConst · a ^ (-windowPackingExp) = 1538 ^ 12 · a ^ (-12)`, using `a ≤ 1` to absorb the
additive `2` into `2 / a`. -/
private lemma wp_packing_arith (ha0 : 0 < a) (ha1 : a ≤ 1) :
    (2 * (4 * (192 / (a : ℝ)) + ((1 : ℝ≥0) : ℝ)) / ((1 : ℝ≥0) : ℝ)) ^ 12
      ≤ ((windowPackingConst * a ^ (-windowPackingExp) : ℝ≥0) : ℝ) := by
  have ha0' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have ha1' : (a : ℝ) ≤ 1 := by exact_mod_cast ha1
  have ha_ne_zero : (a : ℝ) ≠ 0 := by linarith
  -- Simplify LHS: (2 * (4*(192/a) + 1) / 1)^12 = (1536/a + 2)^12
  have hLHS : (2 * (4 * (192 / (a : ℝ)) + ((1 : ℝ≥0) : ℝ)) / ((1 : ℝ≥0) : ℝ)) ^ 12 =
      (1536 / (a : ℝ) + 2) ^ 12 := by
    push_cast
    ring
  rw [hLHS]
  -- 1536/a + 2 ≤ 1538/a, using a ≤ 1 to get 1/a ≥ 1, hence 2 ≤ 2/a
  have h_one_div_a : (1 : ℝ) ≤ 1 / (a : ℝ) := by
    rw [le_div_iff₀ ha0']
    simpa using ha1'
  have h_two_div : (2 : ℝ) ≤ 2 / (a : ℝ) := by
    calc
      (2 : ℝ) = 2 * 1 := by norm_num
      _ ≤ 2 * (1 / (a : ℝ)) := mul_le_mul_of_nonneg_left h_one_div_a (by norm_num)
      _ = 2 / (a : ℝ) := by ring
  -- 1538/a - (1536/a + 2) = 2/a - 2 = 2*(1/a - 1) ≥ 0
  have h_mid : (1536 / (a : ℝ) + 2) ≤ 1538 / (a : ℝ) := by
    calc
      (1536 / (a : ℝ) + 2) = (1538 / (a : ℝ)) - ((2 : ℝ) / (a : ℝ) - 2) := by ring
      _ ≤ (1538 / (a : ℝ)) - 0 := by
        refine sub_le_sub_left ?_ _
        have : (2 : ℝ) / (a : ℝ) - 2 = 2 * (1 / (a : ℝ) - 1) := by ring
        rw [this]
        nlinarith
      _ = 1538 / (a : ℝ) := by ring
  have h_nonneg : 0 ≤ 1536 / (a : ℝ) + 2 := by positivity
  have h_pow : (1536 / (a : ℝ) + 2) ^ 12 ≤ (1538 / (a : ℝ)) ^ 12 :=
    pow_le_pow_left₀ h_nonneg h_mid 12
  -- Unfold constants and match RHS: (1538/a)^12 = 1538^12 * (a^12)⁻¹
  unfold windowPackingConst windowPackingExp
  have h_nn : (a : ℝ≥0) ^ (-(12 : ℝ)) = ((a : ℝ≥0) ^ (12 : ℕ))⁻¹ := by
    calc
      (a : ℝ≥0) ^ (-(12 : ℝ)) = (a : ℝ≥0) ^ (-((12 : ℕ) : ℝ)) := by norm_num
      _ = ((a : ℝ≥0) ^ ((12 : ℕ) : ℝ))⁻¹ := by rw [NNReal.rpow_neg]
      _ = ((a : ℝ≥0) ^ (12 : ℕ))⁻¹ := by rw [NNReal.rpow_natCast]
  have h_arith : ((a : ℝ≥0) ^ (-(12 : ℝ)) : ℝ) = ((a : ℝ) ^ 12)⁻¹ := by
    calc
      ((a : ℝ≥0) ^ (-(12 : ℝ)) : ℝ) = (((a : ℝ≥0) ^ (12 : ℕ))⁻¹ : ℝ) := by
        simpa using congrArg (fun x : ℝ≥0 => (x : ℝ)) h_nn
      _ = (((a : ℝ≥0) ^ (12 : ℕ) : ℝ≥0) : ℝ)⁻¹ := by push_cast; rfl
      _ = ((a : ℝ) ^ 12)⁻¹ := by push_cast; rfl
  calc
    (1536 / (a : ℝ) + 2) ^ 12 ≤ (1538 / (a : ℝ)) ^ 12 := h_pow
    _ = (1538 ^ 12) * ((a : ℝ) ^ 12)⁻¹ := by
      field_simp [ha_ne_zero]
    _ = ((1538 ^ 12 : ℝ≥0) : ℝ) * ((a : ℝ) ^ 12)⁻¹ := by push_cast; rfl
    _ = ((1538 ^ 12 : ℝ≥0) : ℝ) * ((a : ℝ) ^ (-(12 : ℝ))) := by
      rw [show ((a : ℝ) ^ 12)⁻¹ = (a : ℝ) ^ (-(12 : ℝ)) from by
        calc
          ((a : ℝ) ^ 12)⁻¹ = ((a : ℝ) ^ (12 : ℝ))⁻¹ := by norm_num
          _ = (a : ℝ) ^ (-(12 : ℝ)) := by
            rw [← Real.rpow_neg (by linarith : 0 ≤ (a : ℝ)) (12 : ℝ)]]
    _ = ((1538 ^ 12 : ℝ≥0) : ℝ) * ((a ^ (-(12 : ℝ)) : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_rpow a (-(12 : ℝ))]

/-- **Window packing with explicit constants.**  A family of `a × b × 1` planks (`0 < a`) that lies
in the fixed Section 6 window and whose carriers are pairwise essentially distinct has at most
`windowPackingConst · a ^ (-windowPackingExp)` members.

This is the concrete form; `Plank.card_le_of_windowed_essentiallyDistinct` is the packaged form
whose two constants are bound before the configuration, as GWZ Lemma 6.11 requires. -/
theorem card_le_windowPackingConst
    (s : Finset ι) (P : ι → Plank a b hab hb1) (ha0 : 0 < a)
    (hwin : IsWindowedFamily s P)
    (hED : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      PrismNDim.IsEssentiallyDistinct (P i).toPrismNDim (P j).toPrismNDim) :
    (s.card : ℝ≥0) ≤ windowPackingConst * a ^ (-windowPackingExp) := by
  have ha1 : a ≤ 1 := hab.trans hb1
  have ha0' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hK0 : (0 : ℝ) ≤ 192 / (a : ℝ) := by positivity
  -- Confinement: all pose coordinates are bounded by 192 / a
  have hconf : ∀ j ∈ s, ∀ p, |wpPose (P j) p| ≤ 192 / (a : ℝ) := by
    intro j hj p
    have hcentre : ‖(P j).center -ᵥ (0 : EuclideanSpace ℝ (Fin 3))‖ ≤ 4 :=
      wp_center_norm_le s P hwin hj
    exact wpPose_abs_le ha0 (P j) hcentre p
  -- Separation: distinct planks have pose distance > 1
  have hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ((1 : ℝ≥0) : ℝ) < dist (wpPose (P i)) (wpPose (P j)) := by
    intro i hi j hj hne
    by_contra! hle
    -- hle : dist (wpPose (P i)) (wpPose (P j)) ≤ (1 : ℝ≥0) : ℝ
    push_cast at hle
    have hnotED : ¬ PrismNDim.IsEssentiallyDistinct (P i).toPrismNDim (P j).toPrismNDim :=
      wp_not_essentiallyDistinct_of_wpPose_dist_le_one ha0 (P i) (P j) hle
    exact hnotED (hED i hi j hj hne)
  -- Apply the packing engine
  have hcard : (s.card : ℝ) ≤ (2 * (4 * (192 / (a : ℝ)) + ((1 : ℝ≥0) : ℝ)) / ((1 : ℝ≥0) : ℝ)) ^
      12 :=
    card_le_of_pose_confined_separated s (fun j => wpPose (P j)) hK0 (r := 1) (by norm_num)
        hconf hsep
  -- Chain with the arithmetic bound
  have hfinal : (s.card : ℝ) ≤ ((windowPackingConst * a ^ (-windowPackingExp) : ℝ≥0) : ℝ) :=
    hcard.trans (wp_packing_arith ha0 ha1)
  -- Convert from ℝ to ℝ≥0
  have hreal : ((s.card : ℝ≥0) : ℝ) ≤ ((windowPackingConst * a ^ (-windowPackingExp) : ℝ≥0) : ℝ)
      := by
    calc
      ((s.card : ℝ≥0) : ℝ) = (s.card : ℝ) := by push_cast; ring
      _ ≤ ((windowPackingConst * a ^ (-windowPackingExp) : ℝ≥0) : ℝ) := hfinal
  exact_mod_cast hreal

/-- **The plank-count input of GWZ Lemma 6.11, proved from the Lemma 6.13 hypotheses.**

There are absolute constants `Cwin > 0` and `Dwin ≥ 0` — quantified before the index type, the
finite index set, the scales `a ≤ b ≤ 1` and the family itself — such that any family of
`a × b × 1` planks with `0 < a` that lies in the fixed Section 6 working window
(`Plank.IsWindowedFamily`) and has pairwise essentially distinct carriers satisfies
`(s.card : ℝ≥0) ≤ Cwin · a ^ (-Dwin)`.

This is exactly the shape of the `hcard` hypothesis of
`Kakeya.findingTypicalAngleOfIntersection_stable_reserve`, with `C₀ := Cwin` and `Nexp := Dwin`.
The witnesses are `Plank.windowPackingConst = 1538 ^ 12` and `Plank.windowPackingExp = 12`. -/
theorem card_le_of_windowed_essentiallyDistinct :
    ∃ (Cwin : ℝ≥0) (Dwin : ℝ), 0 < Cwin ∧ 0 ≤ Dwin ∧
      ∀ {ι : Type*} (s : Finset ι) {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (P : ι → Plank a b hab hb1),
        0 < a →
        IsWindowedFamily s P →
        (s : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (P i).carrier (P j).carrier) →
        (s.card : ℝ≥0) ≤ Cwin * a ^ (-Dwin) := by
  refine ⟨windowPackingConst, windowPackingExp, windowPackingConst_pos, windowPackingExp_nonneg, ?_⟩
  intro ι s a b hab hb1 P ha0 hwin hed
  apply card_le_windowPackingConst s P ha0 hwin
  intro i hi j hj hne
  have h := hed (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) hne
  simpa [PrismNDim.IsEssentiallyDistinct] using h

/-- The `ShadedPlank` form of `Plank.card_le_of_windowed_essentiallyDistinct`, phrased against the
hypotheses `Kakeya.plankReduction` actually carries.  The shading and the plank share a carrier, so
this is the plank statement composed with `ShadedPlank.planks_carrier`. -/
theorem card_le_of_windowed_essentiallyDistinct_shaded :
    ∃ (Cwin : ℝ≥0) (Dwin : ℝ), 0 < Cwin ∧ 0 ≤ Dwin ∧
      ∀ {ι : Type*} (s : Finset ι) {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (Y : ι → ShadedPlank a b hab hb1),
        0 < a →
        IsWindowedFamily s (ShadedPlank.planks Y) →
        (s : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (Y i).carrier (Y j).carrier) →
        (s.card : ℝ≥0) ≤ Cwin * a ^ (-Dwin) := by
  obtain ⟨Cwin, Dwin, hC, hD, h⟩ := Plank.card_le_of_windowed_essentiallyDistinct
  refine ⟨Cwin, Dwin, hC, hD, ?_⟩
  intro ι s a b hab hb1 Y ha0 hwin hED
  apply h s (ShadedPlank.planks Y) ha0 hwin
  simpa [ShadedPlank.planks_carrier] using hED

end Plank

end
