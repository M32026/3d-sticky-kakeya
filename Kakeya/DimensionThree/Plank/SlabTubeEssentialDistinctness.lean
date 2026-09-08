/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabFibreGeometry
public import Kakeya.DimensionThree.Plank.SlabAssignment
public import Kakeya.Tube.EDPacking.AxialAngle
public import Kakeya.Tube.EDUpToMult

/-!
# The anisotropic essential-distinctness packing bridge for GWZ Section 6

`Plank.normaliseSlabFamilyToTubes` exports pairwise essential distinctness of the *cores*
`g '' Q.carrier` — an affine invariant of the fibre's own essential distinctness — but not of the
enclosing tubes, which inflate the cores by a fixed factor. `Kakeya.FrostmanEstimate` (GWZ Lemma
3.9) wants pairwise essentially distinct tubes, and `Kakeya.IsEDUpToMult` is the honest bridge:
only boundedly many members of the family fail to be essentially distinct from any one of them.

This file supplies the prism-level packing estimate that the bridge rests on. It is the
anisotropic analogue of GWZ Lemma 3.8 (`Kakeya.badAgainstSet_count_le_of_ED_thinBox`, which is
stated for tubes and already assumes tube-level pairwise essential distinctness, so cannot be
reused as it stands).

## Contents

* `Plank.not_essentiallyDistinct_of_anisotropicPose_close`: the *anisotropic* separation input.
  Two planks whose frames and centres agree, measured against a common reference plank `P₀` at the
  weights `w = (a, b, 1)`, to within `w q / (96 R)` resp. `w q / (48 R)`, are not essentially
  distinct.
* `Plank.card_le_of_anisotropicConfined_pairwiseED`: the resulting packing bound. A pairwise
  essentially distinct family of `a × b × 1` planks whose poses are `R`-confined against a single
  reference plank, at the anisotropic weights, has at most `(768 R² + 2) ^ 12` members — a bound
  depending only on `R`.

## Why the confinement hypothesis has to be symmetric

The confinement is stated as `max (w j) (w k) · |⟪e j, e' k⟫| ≤ R · min (w j) (w k)`, not in the
one-sided form `w j · |⟪e j, e' k⟫| ≤ R · w k`. The one-sided form leaves the off-diagonal entry
unconstrained when `w q ≫ w k`, and the cross terms of the frame expansion in
`Plank.not_essentiallyDistinct_of_anisotropicPose_close` then fail to close. Both directions are
available at the intended call site, because the normalising map of `Plank.slabTube` is exactly the
one that makes a slab fibre's anisotropy isotropic.

Contrast `Plank.ThickenedRepr.phi_packing_bound`, which uses the same metric packing engine
(`Plank.card_le_of_pose_confined_separated`) but normalises all twelve pose coordinates at the
*shortest* half-width and therefore only reaches `a ^ (-12)`.
-/

@[expose] public section

open MeasureTheory Kakeya
open scoped NNReal Real Classical

noncomputable section

namespace Plank

/-- **Anisotropic pose closeness implies failure of essential distinctness.** If `P` and `P'` have
frames and centres that agree, at the anisotropic weights `w = (a, b, 1)` and against a reference
frame `P₀`, to within `w q / (96 R)` and `w q / (48 R)` respectively, and if `P'` itself is
`R`-confined against `P₀` in the symmetric anisotropic sense, then `P` and `P'` are not essentially
distinct.

This converts control measured in the *reference* frame `P₀.basis` into the two hypotheses of
`Plank.plank_not_essentiallyDistinct_of_pose_close`, which are measured in `P'`'s own frame. The
conversion is the frame expansion `Kakeya.inner_eq_sum_frame`: the diagonal term of that expansion
is controlled by the closeness hypothesis alone, and each off-diagonal term by the product of the
closeness hypothesis with the confinement of `P'`, whose two cases `w q ≥ w k` and `w q < w k` both
collapse to `w k / 96` — which is why `hfrm₀` must be symmetric. -/
theorem not_essentiallyDistinct_of_anisotropicPose_close {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (ha0 : 0 < a) (P P' P₀ : Plank a b hab hb1) {R : ℝ} (hR : 1 ≤ R)
    (hfrm₀ : ∀ j k : Fin 3, j ≠ k →
      max ((![a, b, 1] j : ℝ≥0) : ℝ) ((![a, b, 1] k : ℝ≥0) : ℝ)
          * |inner ℝ (P'.basis j) (P₀.basis k)|
        ≤ R * min ((![a, b, 1] j : ℝ≥0) : ℝ) ((![a, b, 1] k : ℝ≥0) : ℝ))
    (hfrmΔ : ∀ p q : Fin 3,
      ((![a, b, 1] p : ℝ≥0) : ℝ)
          * |inner ℝ (P.basis p) (P₀.basis q) - inner ℝ (P'.basis p) (P₀.basis q)|
        ≤ ((![a, b, 1] q : ℝ≥0) : ℝ) / (96 * R))
    (hcenΔ : ∀ q : Fin 3,
      |inner ℝ (P₀.basis q) (P.center -ᵥ P'.center)| ≤ ((![a, b, 1] q : ℝ≥0) : ℝ) / (48 * R)) :
    ¬ PrismNDim.IsEssentiallyDistinct P.toPrismNDim P'.toPrismNDim := by
  let w : Fin 3 → ℝ := fun k => ((![a, b, 1] k : ℝ≥0) : ℝ)
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hw0 : ∀ k : Fin 3, 0 < w k := by
    intro k
    fin_cases k
    · dsimp [w]; exact_mod_cast ha0
    · dsimp [w]; exact_mod_cast hb0
    · dsimp [w]; norm_num
  have hw0n : ∀ k : Fin 3, 0 ≤ w k := fun k => (hw0 k).le
  have hRne : R ≠ 0 := ne_of_gt hRpos
  have hwk0 : ∀ k : Fin 3, w k ≠ 0 := fun k => ne_of_gt (hw0 k)
  have h96Rpos : 0 < 96 * R := mul_pos (by norm_num) hRpos
  have h48Rpos : 0 < 48 * R := mul_pos (by norm_num) hRpos
  -- identity: expanding both sides in the reference frame P₀.basis and subtracting
  have hident : ∀ j k : Fin 3, j ≠ k →
      inner ℝ (P.basis j) (P'.basis k)
        = ∑ q : Fin 3, inner ℝ (P₀.basis q) (P'.basis k)
            * (inner ℝ (P.basis j) (P₀.basis q) - inner ℝ (P'.basis j) (P₀.basis q)) := by
    intro j k hjk
    have h1 := inner_eq_sum_frame P₀.basis (P.basis j) (P'.basis k)
    have h2 := inner_eq_sum_frame P₀.basis (P'.basis j) (P'.basis k)
    have hzero : inner ℝ (P'.basis j) (P'.basis k) = 0 := P'.basis.orthonormal.2 hjk
    calc
      inner ℝ (P.basis j) (P'.basis k)
          = ∑ q, inner ℝ (P₀.basis q) (P'.basis k) * inner ℝ (P.basis j) (P₀.basis q) := h1
      _ = ∑ q, inner ℝ (P₀.basis q) (P'.basis k) * inner ℝ (P.basis j) (P₀.basis q)
          - ∑ q, inner ℝ (P₀.basis q) (P'.basis k) * inner ℝ (P'.basis j) (P₀.basis q) := by
        rw [← h2, hzero, sub_zero]
      _ = ∑ q, (inner ℝ (P₀.basis q) (P'.basis k) * inner ℝ (P.basis j) (P₀.basis q)
          - inner ℝ (P₀.basis q) (P'.basis k) * inner ℝ (P'.basis j) (P₀.basis q)) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ q, inner ℝ (P₀.basis q) (P'.basis k)
            * (inner ℝ (P.basis j) (P₀.basis q) - inner ℝ (P'.basis j) (P₀.basis q)) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
  -- STEP 1: frame bound
  have hfrm : ∀ j k : Fin 3, j ≠ k →
      w j * |inner ℝ (P.basis j) (P'.basis k)| ≤ w k / 32 := by
    intro j k hjk
    -- |inner (P.basis j) (P'.basis k)| ≤ ∑ q, |inner (P₀.basis q) (P'.basis k)| * |Δ j q|
    have hsum_le : |inner ℝ (P.basis j) (P'.basis k)|
        ≤ ∑ q : Fin 3, |inner ℝ (P₀.basis q) (P'.basis k)|
            * |inner ℝ (P.basis j) (P₀.basis q) - inner ℝ (P'.basis j) (P₀.basis q)| := by
      rw [hident j k hjk]
      calc
        |∑ x : Fin 3, inner ℝ (P₀.basis x) (P'.basis k)
            * (inner ℝ (P.basis j) (P₀.basis x) - inner ℝ (P'.basis j) (P₀.basis x))|
            ≤ ∑ x : Fin 3, |inner ℝ (P₀.basis x) (P'.basis k)
                * (inner ℝ (P.basis j) (P₀.basis x) - inner ℝ (P'.basis j) (P₀.basis x))| :=
              Finset.abs_sum_le_sum_abs
                (fun x : Fin 3 => inner ℝ (P₀.basis x) (P'.basis k)
                  * (inner ℝ (P.basis j) (P₀.basis x) - inner ℝ (P'.basis j) (P₀.basis x))) _
        _ = ∑ x : Fin 3, |inner ℝ (P₀.basis x) (P'.basis k)|
            * |inner ℝ (P.basis j) (P₀.basis x) - inner ℝ (P'.basis j) (P₀.basis x)| := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [abs_mul]
    -- w j * |inner| ≤ ∑ q, |A_q| * (w j * |Δ j q|)
    have hbound : w j * |inner ℝ (P.basis j) (P'.basis k)|
        ≤ ∑ q : Fin 3, |inner ℝ (P₀.basis q) (P'.basis k)|
            * (w j * |inner ℝ (P.basis j) (P₀.basis q) - inner ℝ (P'.basis j) (P₀.basis q)|) := by
      calc
        w j * |inner ℝ (P.basis j) (P'.basis k)|
            ≤ w j * (∑ q : Fin 3, |inner ℝ (P₀.basis q) (P'.basis k)|
                * |inner ℝ (P.basis j) (P₀.basis q) - inner ℝ (P'.basis j) (P₀.basis q)|) :=
              mul_le_mul_of_nonneg_left hsum_le (hw0n j)
        _ = ∑ q : Fin 3, w j * (|inner ℝ (P₀.basis q) (P'.basis k)|
            * |inner ℝ (P.basis j) (P₀.basis q) - inner ℝ (P'.basis j) (P₀.basis q)|) := by
              rw [Finset.mul_sum]
        _ = ∑ q : Fin 3, |inner ℝ (P₀.basis q) (P'.basis k)|
            * (w j * |inner ℝ (P.basis j) (P₀.basis q) - inner ℝ (P'.basis j) (P₀.basis q)|) := by
              refine Finset.sum_congr rfl fun q _ => ?_
              ring
    -- per-term bound: each summand ≤ w k / 96
    have hterm : ∀ q : Fin 3, |inner ℝ (P₀.basis q) (P'.basis k)|
        * (w j * |inner ℝ (P.basis j) (P₀.basis q) - inner ℝ (P'.basis j) (P₀.basis q)|) ≤ w k / 96 := by
      intro q
      have hΔ : w j * |inner ℝ (P.basis j) (P₀.basis q) - inner ℝ (P'.basis j) (P₀.basis q)|
          ≤ w q / (96 * R) := hfrmΔ j q
      by_cases hqk : q = k
      · subst q
        calc
          |inner ℝ (P₀.basis k) (P'.basis k)|
              * (w j * |inner ℝ (P.basis j) (P₀.basis k) - inner ℝ (P'.basis j) (P₀.basis k)|)
              ≤ |inner ℝ (P₀.basis k) (P'.basis k)| * (w k / (96 * R)) := by
                exact mul_le_mul_of_nonneg_left hΔ (abs_nonneg _)
          _ ≤ 1 * (w k / (96 * R)) := by
                exact mul_le_mul_of_nonneg_right
                  (by simpa using (abs_inner_basis_le_one P₀.basis P'.basis k k))
                  (div_nonneg (hw0n k) (le_of_lt h96Rpos))
          _ = w k / (96 * R) := by rw [one_mul]
          _ ≤ w k / 96 := by
                have h96le : (96 : ℝ) ≤ 96 * R := by
                  calc (96 : ℝ) = 96 * 1 := by ring
                    _ ≤ 96 * R := mul_le_mul_of_nonneg_left hR (by norm_num)
                exact div_le_div_of_nonneg_left (hw0n k) (by norm_num : (0 : ℝ) < 96) h96le
      · have hA : |inner ℝ (P₀.basis q) (P'.basis k)|
            ≤ R * min (w k) (w q) / max (w k) (w q) := by
          have hkq : k ≠ q := fun h => hqk h.symm
          have hfq := hfrm₀ k q hkq
          have hmaxpos : 0 < max (w k) (w q) := lt_max_of_lt_left (hw0 k)
          rw [show |inner ℝ (P₀.basis q) (P'.basis k)| = |inner ℝ (P'.basis k) (P₀.basis q)|
            by rw [real_inner_comm]]
          rw [le_div_iff₀ hmaxpos, mul_comm]
          exact hfq
        have hprod : (R * min (w k) (w q) / max (w k) (w q)) * (w q / (96 * R)) ≤ w k / 96 := by
          rcases le_total (w k) (w q) with hkwq | hqwk
          · have hprod_eq : (R * min (w k) (w q) / max (w k) (w q)) * (w q / (96 * R)) = w k / 96 := by
              rw [min_eq_left hkwq, max_eq_right hkwq]
              field_simp [hRne, hwk0 q]
            rw [hprod_eq]
          · calc
              (R * min (w k) (w q) / max (w k) (w q)) * (w q / (96 * R))
                  = w q * w q / (96 * w k) := by
                    rw [min_eq_right hqwk, max_eq_left hqwk]
                    field_simp [hRne, hwk0 k]
              _ ≤ w k * w k / (96 * w k) := by
                    exact div_le_div_of_nonneg_right
                      (mul_le_mul hqwk hqwk (hw0n q) (hw0n k))
                      (le_of_lt (mul_pos (by norm_num) (hw0 k)))
              _ = w k / 96 := by
                    field_simp [hwk0 k]
        calc
          |inner ℝ (P₀.basis q) (P'.basis k)|
              * (w j * |inner ℝ (P.basis j) (P₀.basis q) - inner ℝ (P'.basis j) (P₀.basis q)|)
              ≤ (R * min (w k) (w q) / max (w k) (w q)) * (w q / (96 * R)) := by
                exact mul_le_mul hA hΔ (mul_nonneg (hw0n j) (abs_nonneg _))
                  (div_nonneg (mul_nonneg (le_of_lt hRpos) (le_min (hw0n k) (hw0n q)))
                    (le_of_lt (lt_max_of_lt_left (hw0 k))))
          _ ≤ w k / 96 := hprod
    -- sum of the three terms
    have hsum : (∑ q : Fin 3, |inner ℝ (P₀.basis q) (P'.basis k)|
          * (w j * |inner ℝ (P.basis j) (P₀.basis q) - inner ℝ (P'.basis j) (P₀.basis q)|)) ≤ 3 * (w k / 96) := by
      rw [Fin.sum_univ_three]
      nlinarith [hterm 0, hterm 1, hterm 2]
    calc
      w j * |inner ℝ (P.basis j) (P'.basis k)|
          ≤ ∑ q : Fin 3, |inner ℝ (P₀.basis q) (P'.basis k)|
              * (w j * |inner ℝ (P.basis j) (P₀.basis q) - inner ℝ (P'.basis j) (P₀.basis q)|) := hbound
      _ ≤ 3 * (w k / 96) := hsum
      _ = w k / 32 := by ring
  -- STEP 2: centre bound
  have hcen : ∀ k : Fin 3,
      |inner ℝ (P'.basis k) (P.center -ᵥ P'.center)| ≤ w k / 16 := by
    intro k
    have hsum_le : |inner ℝ (P'.basis k) (P.center -ᵥ P'.center)|
        ≤ ∑ q : Fin 3, |inner ℝ (P₀.basis q) (P.center -ᵥ P'.center)|
            * |inner ℝ (P'.basis k) (P₀.basis q)| := by
      rw [inner_eq_sum_frame P₀.basis (P'.basis k) (P.center -ᵥ P'.center)]
      calc
        |∑ x : Fin 3, inner ℝ (P₀.basis x) (P.center -ᵥ P'.center)
            * inner ℝ (P'.basis k) (P₀.basis x)|
            ≤ ∑ x : Fin 3, |inner ℝ (P₀.basis x) (P.center -ᵥ P'.center)
                * inner ℝ (P'.basis k) (P₀.basis x)| :=
              Finset.abs_sum_le_sum_abs
                (fun x : Fin 3 => inner ℝ (P₀.basis x) (P.center -ᵥ P'.center)
                  * inner ℝ (P'.basis k) (P₀.basis x)) _
        _ = ∑ x : Fin 3, |inner ℝ (P₀.basis x) (P.center -ᵥ P'.center)|
            * |inner ℝ (P'.basis k) (P₀.basis x)| := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [abs_mul]
    -- per-term bound: each term ≤ w k / 48
    have hterm : ∀ q : Fin 3, |inner ℝ (P₀.basis q) (P.center -ᵥ P'.center)|
        * |inner ℝ (P'.basis k) (P₀.basis q)| ≤ w k / 48 := by
      intro q
      have hC : |inner ℝ (P₀.basis q) (P.center -ᵥ P'.center)| ≤ w q / (48 * R) := hcenΔ q
      by_cases hqk : q = k
      · subst q
        calc
          |inner ℝ (P₀.basis k) (P.center -ᵥ P'.center)| * |inner ℝ (P'.basis k) (P₀.basis k)|
              ≤ (w k / (48 * R)) * |inner ℝ (P'.basis k) (P₀.basis k)| := by
                exact mul_le_mul_of_nonneg_right hC (abs_nonneg _)
          _ ≤ (w k / (48 * R)) * 1 := by
                exact mul_le_mul_of_nonneg_left
                  (by simpa using (abs_inner_basis_le_one P'.basis P₀.basis k k))
                  (div_nonneg (hw0n k) (le_of_lt h48Rpos))
          _ = w k / (48 * R) := by rw [mul_one]
          _ ≤ w k / 48 := by
                have h48le : (48 : ℝ) ≤ 48 * R := by
                  calc (48 : ℝ) = 48 * 1 := by ring
                    _ ≤ 48 * R := mul_le_mul_of_nonneg_left hR (by norm_num)
                exact div_le_div_of_nonneg_left (hw0n k) (by norm_num : (0 : ℝ) < 48) h48le
      · have hkq : k ≠ q := fun h => hqk h.symm
        have hA : |inner ℝ (P'.basis k) (P₀.basis q)|
            ≤ R * min (w k) (w q) / max (w k) (w q) := by
          have hfq := hfrm₀ k q hkq
          have hmaxpos : 0 < max (w k) (w q) := lt_max_of_lt_left (hw0 k)
          rw [le_div_iff₀ hmaxpos, mul_comm]
          exact hfq
        have hprod : (R * min (w k) (w q) / max (w k) (w q)) * (w q / (48 * R)) ≤ w k / 48 := by
          rcases le_total (w k) (w q) with hkwq | hqwk
          · have hprod_eq : (R * min (w k) (w q) / max (w k) (w q)) * (w q / (48 * R)) = w k / 48 := by
              rw [min_eq_left hkwq, max_eq_right hkwq]
              field_simp [hRne, hwk0 q]
            rw [hprod_eq]
          · calc
              (R * min (w k) (w q) / max (w k) (w q)) * (w q / (48 * R))
                  = w q * w q / (48 * w k) := by
                    rw [min_eq_right hqwk, max_eq_left hqwk]
                    field_simp [hRne, hwk0 k]
              _ ≤ w k * w k / (48 * w k) := by
                    exact div_le_div_of_nonneg_right
                      (mul_le_mul hqwk hqwk (hw0n q) (hw0n k))
                      (le_of_lt (mul_pos (by norm_num) (hw0 k)))
              _ = w k / 48 := by
                    field_simp [hwk0 k]
        calc
          |inner ℝ (P₀.basis q) (P.center -ᵥ P'.center)| * |inner ℝ (P'.basis k) (P₀.basis q)|
              ≤ (w q / (48 * R)) * (R * min (w k) (w q) / max (w k) (w q)) := by
                exact mul_le_mul hC hA (abs_nonneg _)
                  (div_nonneg (hw0n q) (le_of_lt h48Rpos))
          _ ≤ w k / 48 := by
                rw [mul_comm]
                exact hprod
    have hsum : (∑ q : Fin 3, |inner ℝ (P₀.basis q) (P.center -ᵥ P'.center)|
          * |inner ℝ (P'.basis k) (P₀.basis q)|) ≤ 3 * (w k / 48) := by
      rw [Fin.sum_univ_three]
      nlinarith [hterm 0, hterm 1, hterm 2]
    calc
      |inner ℝ (P'.basis k) (P.center -ᵥ P'.center)|
          ≤ ∑ q : Fin 3, |inner ℝ (P₀.basis q) (P.center -ᵥ P'.center)|
              * |inner ℝ (P'.basis k) (P₀.basis q)| := hsum_le
      _ ≤ 3 * (w k / 48) := hsum
      _ = w k / 16 := by ring
  exact plank_not_essentiallyDistinct_of_pose_close ha0 hb0 P P' hfrm hcen

/-- The twelve-dimensional **anisotropic pose** of a plank `W`, read in the reference frame of a
plank `P₀`: the nine frame inner products `⟪W.basis p, P₀.basis q⟫`, normalised by
`96 R · w p / w q`, together with the three offset coordinates
`⟪P₀.basis q, W.center -ᵥ P₀.center⟫`, normalised by `48 R / w q`, where `w = (a, b, 1)`.

The anisotropic normalisation is what makes both the confinement radius and the separation radius
absolute: contrast `Plank.ThickenedRepr.phi_packing_bound`, which normalises all twelve coordinates
at the shortest half-width `a` and therefore only reaches `a ^ (-12)`. -/
private noncomputable def anisoPose {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P₀ : Plank a b hab hb1) (R : ℝ) (W : Plank a b hab hb1) :
    EuclideanSpace ℝ ((Fin 3 × Fin 3) ⊕ Fin 3) :=
  WithLp.toLp 2 <| Sum.elim
    (fun pq : Fin 3 × Fin 3 =>
      96 * R * (((![a, b, 1] pq.1 : ℝ≥0) : ℝ) / ((![a, b, 1] pq.2 : ℝ≥0) : ℝ))
        * inner ℝ (W.basis pq.1) (P₀.basis pq.2))
    (fun q : Fin 3 =>
      48 * R / ((![a, b, 1] q : ℝ≥0) : ℝ) * inner ℝ (P₀.basis q) (W.center -ᵥ P₀.center))

/-- The frame coordinates of `Plank.anisoPose`. -/
private lemma anisoPose_inl {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P₀ : Plank a b hab hb1) (R : ℝ) (W : Plank a b hab hb1) (p q : Fin 3) :
    anisoPose P₀ R W (Sum.inl (p, q))
      = 96 * R * (((![a, b, 1] p : ℝ≥0) : ℝ) / ((![a, b, 1] q : ℝ≥0) : ℝ))
          * inner ℝ (W.basis p) (P₀.basis q) := by
  rfl

/-- The offset coordinates of `Plank.anisoPose`. -/
private lemma anisoPose_inr {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P₀ : Plank a b hab hb1) (R : ℝ) (W : Plank a b hab hb1) (q : Fin 3) :
    anisoPose P₀ R W (Sum.inr q)
      = 48 * R / ((![a, b, 1] q : ℝ≥0) : ℝ)
          * inner ℝ (P₀.basis q) (W.center -ᵥ P₀.center) := by
  rfl

/-- The scalar core of the off-diagonal confinement bound: if `max x y · A ≤ R · min x y` with
`x, y > 0`, `A ≥ 0` and `R ≥ 1`, then `96 R (x / y) A ≤ 96 R²`.

Both cases are tight in one direction: for `x ≤ y` the left side is `96 R² (x / y)²`, and for
`y ≤ x` it is exactly `96 R²`. -/
private lemma aniso_ratio_bound {x y A R : ℝ} (hx : 0 < x) (hy : 0 < y) (hR : 1 ≤ R)
    (hA : 0 ≤ A) (h : max x y * A ≤ R * min x y) :
    96 * R * (x / y) * A ≤ 96 * R ^ 2 := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hR0 : R ≠ 0 := ne_of_gt hRpos
  have hcoef_nonneg : 0 ≤ 96 * R * (x / y) := by positivity
  have hA_nonneg : 0 ≤ A := hA
  rcases le_total x y with hxy | hyx
  · rw [max_eq_right hxy, min_eq_left hxy] at h
    have hA' : A ≤ R * x / y := by
      rw [le_div_iff₀ hy, mul_comm]
      exact h
    have hratio1 : x / y ≤ 1 := by
      rw [div_le_iff₀ hy]
      simpa using hxy
    have h96R2 : 0 ≤ 96 * R ^ 2 := by positivity
    have hsq : (x / y) ^ 2 ≤ 1 := by
      nlinarith [hratio1, le_of_lt (div_pos hx hy), hA_nonneg]
    calc
      96 * R * (x / y) * A ≤ 96 * R * (x / y) * (R * x / y) := by
        exact mul_le_mul_of_nonneg_left hA' hcoef_nonneg
      _ = 96 * R ^ 2 * (x / y) ^ 2 := by
        field_simp [hx0, hy0, hR0]
      _ ≤ 96 * R ^ 2 := by
        calc
          96 * R ^ 2 * (x / y) ^ 2 ≤ 96 * R ^ 2 * 1 := mul_le_mul_of_nonneg_left hsq h96R2
          _ = 96 * R ^ 2 := by ring
  · rw [max_eq_left hyx, min_eq_right hyx] at h
    have hA' : A ≤ R * y / x := by
      rw [le_div_iff₀ hx, mul_comm]
      exact h
    calc
      96 * R * (x / y) * A ≤ 96 * R * (x / y) * (R * y / x) := by
        exact mul_le_mul_of_nonneg_left hA' hcoef_nonneg
      _ = 96 * R ^ 2 := by
        field_simp [hx0, hy0, hR0]

/-- The scalar core of the diagonal confinement bound: the weight ratio is `1` and Cauchy–Schwarz
gives `A ≤ 1`, so the normalised entry is at most `96 R ≤ 96 R²`. -/
private lemma aniso_diag_bound {x A R : ℝ} (hx : 0 < x) (hR : 1 ≤ R) (hA : 0 ≤ A) (h : A ≤ 1) :
    96 * R * (x / x) * A ≤ 96 * R ^ 2 := by
  rw [div_self (ne_of_gt hx)]
  have h96R_nonneg : 0 ≤ 96 * R := by
    exact mul_nonneg (by norm_num) (le_of_lt (lt_of_lt_of_le zero_lt_one hR))
  have hRA_nonneg : 0 ≤ 96 * R * A := mul_nonneg h96R_nonneg hA
  nlinarith [hR, h, hRA_nonneg]

/-- The scalar core of the offset confinement bound: `(48 R / y) · A ≤ 48 R² ≤ 96 R²` whenever
`A ≤ R y` with `y > 0` and `R ≥ 1`. -/
private lemma aniso_offset_bound {y A R : ℝ} (hy : 0 < y) (hR : 1 ≤ R) (hA : 0 ≤ A)
    (h : A ≤ R * y) :
    48 * R / y * A ≤ 96 * R ^ 2 := by
  calc
    48 * R / y * A ≤ 48 * R / y * (R * y) := by
      exact mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 48 * R / y)
    _ = 48 * R ^ 2 := by
      field_simp [ne_of_gt hy]
    _ ≤ 96 * R ^ 2 := by
      nlinarith [sq_nonneg R]

/-- **Confinement of the anisotropic pose.** A plank whose frame is `R`-confined against `P₀` in
the symmetric anisotropic sense and whose centre offset is bounded by `R · w k` in every reference
coordinate has all twelve pose coordinates bounded by `96 R²`.

For `p ≠ q` the symmetric hypothesis gives `|⟪e p, f q⟫| ≤ R · min (w p) (w q) / max (w p) (w q)`,
so the normalised entry is `96 R · (w p / w q) · R · min / max`, which equals `96 R² (w p / w q)²`
when `w p ≤ w q` and exactly `96 R²` when `w q ≤ w p`. For `p = q` the weight ratio is `1` and
Cauchy–Schwarz bounds the entry by `96 R ≤ 96 R²`. The offset coordinates are at most
`(48 R / w q) · R · w q = 48 R²`. -/
private lemma abs_anisoPose_le {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (ha0 : 0 < a) (P₀ W : Plank a b hab hb1) {R : ℝ} (hR : 1 ≤ R)
    (hfrm : ∀ j k : Fin 3, j ≠ k →
      max ((![a, b, 1] j : ℝ≥0) : ℝ) ((![a, b, 1] k : ℝ≥0) : ℝ)
          * |inner ℝ (W.basis j) (P₀.basis k)|
        ≤ R * min ((![a, b, 1] j : ℝ≥0) : ℝ) ((![a, b, 1] k : ℝ≥0) : ℝ))
    (hcen : ∀ k : Fin 3,
      |inner ℝ (P₀.basis k) (W.center -ᵥ P₀.center)| ≤ R * ((![a, b, 1] k : ℝ≥0) : ℝ)) :
    ∀ p, |anisoPose P₀ R W p| ≤ 96 * R ^ 2 := by
  let w : Fin 3 → ℝ := fun k => ((![a, b, 1] k : ℝ≥0) : ℝ)
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hw0 : ∀ k : Fin 3, 0 < w k := by
    intro k
    fin_cases k
    · dsimp [w]; exact_mod_cast ha0
    · dsimp [w]; exact_mod_cast hb0
    · dsimp [w]; norm_num
  rintro (⟨p, q⟩ | q)
  · rw [anisoPose_inl]
    change |96 * R * (w p / w q) * inner ℝ (W.basis p) (P₀.basis q)| ≤ 96 * R ^ 2
    by_cases hpq : p = q
    · subst q
      have hcoef : 0 ≤ 96 * R * (w p / w p) := by
        positivity
      have hin : |inner ℝ (W.basis p) (P₀.basis p)| ≤ 1 :=
        abs_inner_basis_le_one W.basis P₀.basis p p
      rw [abs_mul, abs_of_nonneg hcoef]
      exact aniso_diag_bound (hw0 p) hR (abs_nonneg _) hin
    · have hcoef : 0 ≤ 96 * R * (w p / w q) := by
        positivity
      have hA : max (w p) (w q) * |inner ℝ (W.basis p) (P₀.basis q)|
          ≤ R * min (w p) (w q) := by
        simpa [w] using hfrm p q hpq
      rw [abs_mul, abs_of_nonneg hcoef]
      exact aniso_ratio_bound (hw0 p) (hw0 q) hR (abs_nonneg _) hA
  · rw [anisoPose_inr]
    change |48 * R / w q * inner ℝ (P₀.basis q) (W.center -ᵥ P₀.center)| ≤ 96 * R ^ 2
    have hcoef : 0 ≤ 48 * R / w q := by
      positivity
    have hA : |inner ℝ (P₀.basis q) (W.center -ᵥ P₀.center)| ≤ R * w q := by
      simpa [w] using hcen q
    rw [abs_mul, abs_of_nonneg hcoef]
    exact aniso_offset_bound (hw0 q) hR (abs_nonneg _) hA

/-- **Separation of the anisotropic pose.** Two planks confined against `P₀` whose anisotropic
poses agree to within `1` in every coordinate fail to be essentially distinct.

Reading the `Sum.inl (p, q)` coordinate difference gives
`96 R (w p / w q) · |Δ⟪e p, f q⟫| ≤ 1`, i.e. `w p · |Δ| ≤ w q / (96 R)`, and the `Sum.inr q`
coordinate difference gives `|⟪f q, c -ᵥ c'⟫| ≤ w q / (48 R)` (the two `-ᵥ P₀.center` terms cancel).
These are exactly the two closeness hypotheses of
`Plank.not_essentiallyDistinct_of_anisotropicPose_close`. -/
private lemma not_essentiallyDistinct_of_anisoPose_close {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (ha0 : 0 < a) (P₀ W W' : Plank a b hab hb1) {R : ℝ} (hR : 1 ≤ R)
    (hfrm' : ∀ j k : Fin 3, j ≠ k →
      max ((![a, b, 1] j : ℝ≥0) : ℝ) ((![a, b, 1] k : ℝ≥0) : ℝ)
          * |inner ℝ (W'.basis j) (P₀.basis k)|
        ≤ R * min ((![a, b, 1] j : ℝ≥0) : ℝ) ((![a, b, 1] k : ℝ≥0) : ℝ))
    (hclose : ∀ p, |anisoPose P₀ R W p - anisoPose P₀ R W' p| ≤ 1) :
    ¬ PrismNDim.IsEssentiallyDistinct W.toPrismNDim W'.toPrismNDim := by
  let w : Fin 3 → ℝ := fun k => ((![a, b, 1] k : ℝ≥0) : ℝ)
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hw0 : ∀ k : Fin 3, 0 < w k := by
    intro k
    fin_cases k
    · dsimp [w]; exact_mod_cast ha0
    · dsimp [w]; exact_mod_cast hb0
    · dsimp [w]; norm_num
  have hw0n : ∀ k : Fin 3, 0 ≤ w k := fun k => (hw0 k).le
  have hRne : R ≠ 0 := ne_of_gt hRpos
  have hwk0 : ∀ k : Fin 3, w k ≠ 0 := fun k => ne_of_gt (hw0 k)
  have h96Rpos : 0 < 96 * R := mul_pos (by norm_num) hRpos
  have h48Rpos : 0 < 48 * R := mul_pos (by norm_num) hRpos
  have hfrmΔ : ∀ p q : Fin 3,
      w p * |inner ℝ (W.basis p) (P₀.basis q) - inner ℝ (W'.basis p) (P₀.basis q)|
        ≤ w q / (96 * R) := by
    intro p q
    have hc : |anisoPose P₀ R W (Sum.inl (p, q)) - anisoPose P₀ R W' (Sum.inl (p, q))| ≤ 1 :=
      hclose (Sum.inl (p, q))
    rw [anisoPose_inl P₀ R W p q, anisoPose_inl P₀ R W' p q] at hc
    have hc' : |96 * R * (w p / w q)
        * (inner ℝ (W.basis p) (P₀.basis q) - inner ℝ (W'.basis p) (P₀.basis q))| ≤ 1 := by
      rw [← mul_sub] at hc
      simpa [mul_sub, mul_assoc, mul_left_comm, mul_comm] using hc
    have ha_pos : 0 < 96 * R * (w p / w q) := by
      exact mul_pos h96Rpos (div_pos (hw0 p) (hw0 q))
    have ha_nonneg : 0 ≤ 96 * R * (w p / w q) := le_of_lt ha_pos
    have hc2 : (96 * R * (w p / w q))
        * |inner ℝ (W.basis p) (P₀.basis q) - inner ℝ (W'.basis p) (P₀.basis q)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ha_nonneg] at hc'
      exact hc'
    have hle : |inner ℝ (W.basis p) (P₀.basis q) - inner ℝ (W'.basis p) (P₀.basis q)|
        ≤ 1 / (96 * R * (w p / w q)) := by
      rw [le_div_iff₀ ha_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hc2
    have hcalc : w p * (1 / (96 * R * (w p / w q))) = w q / (96 * R) := by
      field_simp [hRne, hwk0 p, hwk0 q]
    calc
      w p * |inner ℝ (W.basis p) (P₀.basis q) - inner ℝ (W'.basis p) (P₀.basis q)|
          ≤ w p * (1 / (96 * R * (w p / w q))) := mul_le_mul_of_nonneg_left hle (hw0n p)
      _ = w q / (96 * R) := hcalc
  have hcenΔ : ∀ q : Fin 3,
      |inner ℝ (P₀.basis q) (W.center -ᵥ W'.center)| ≤ w q / (48 * R) := by
    intro q
    have hc : |anisoPose P₀ R W (Sum.inr q) - anisoPose P₀ R W' (Sum.inr q)| ≤ 1 :=
      hclose (Sum.inr q)
    rw [anisoPose_inr P₀ R W q, anisoPose_inr P₀ R W' q] at hc
    have hcancel : (W.center -ᵥ P₀.center) - (W'.center -ᵥ P₀.center) = W.center -ᵥ W'.center := by
      exact vsub_sub_vsub_cancel_right W.center W'.center P₀.center
    have hc' : |48 * R / w q
        * inner ℝ (P₀.basis q) (W.center -ᵥ W'.center)| ≤ 1 := by
      rw [← mul_sub] at hc
      rw [← inner_sub_right] at hc
      rw [hcancel] at hc
      simpa [mul_assoc] using hc
    have hb_pos : 0 < 48 * R / w q := div_pos h48Rpos (hw0 q)
    have hb_nonneg : 0 ≤ 48 * R / w q := le_of_lt hb_pos
    have hc2 : (48 * R / w q) * |inner ℝ (P₀.basis q) (W.center -ᵥ W'.center)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hb_nonneg] at hc'
      exact hc'
    have hle : |inner ℝ (P₀.basis q) (W.center -ᵥ W'.center)| ≤ 1 / (48 * R / w q) := by
      rw [le_div_iff₀ hb_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hc2
    have hcalc : 1 / (48 * R / w q) = w q / (48 * R) := by
      field_simp [hRne, hwk0 q]
    rw [hcalc] at hle
    exact hle
  exact not_essentiallyDistinct_of_anisotropicPose_close ha0 W W' P₀ hR hfrm' hfrmΔ hcenΔ

/-- **Pose separation of two essentially distinct confined planks.** Contrapositive of
`Plank.not_essentiallyDistinct_of_anisoPose_close`: if two `R`-confined planks *are* essentially
distinct then their anisotropic poses are at distance more than `1`.

Every coordinate of a pair of poses at distance at most `1` is within `1`, by `PiLp.dist_apply_le`. -/
private lemma one_lt_dist_anisoPose {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (ha0 : 0 < a) (P₀ W W' : Plank a b hab hb1) {R : ℝ} (hR : 1 ≤ R)
    (hfrm' : ∀ j k : Fin 3, j ≠ k →
      max ((![a, b, 1] j : ℝ≥0) : ℝ) ((![a, b, 1] k : ℝ≥0) : ℝ)
          * |inner ℝ (W'.basis j) (P₀.basis k)|
        ≤ R * min ((![a, b, 1] j : ℝ≥0) : ℝ) ((![a, b, 1] k : ℝ≥0) : ℝ))
    (hED : PrismNDim.IsEssentiallyDistinct W.toPrismNDim W'.toPrismNDim) :
    (1 : ℝ) < dist (anisoPose P₀ R W) (anisoPose P₀ R W') := by
  by_contra! h
  exact (not_essentiallyDistinct_of_anisoPose_close ha0 P₀ W W' hR hfrm'
    (fun p : (Fin 3 × Fin 3) ⊕ Fin 3 => by
      have hp := PiLp.dist_apply_le (anisoPose P₀ R W) (anisoPose P₀ R W') p
      rw [Real.dist_eq] at hp
      exact hp.trans h)) hED

/-- **Anisotropic essential-distinctness packing for planks** (the prism analogue of GWZ Lemma 3.8).

A family of `a × b × 1` planks that is pairwise essentially distinct and whose frames and centres
are `R`-confined, at the anisotropic weights `w = (a, b, 1)`, against a single reference plank `P₀`
has at most `(768 R² + 2) ^ 12` members — a bound depending only on `R`, and in particular
independent of `a`, `b` and of the family.

The proof feeds `Plank.card_le_of_pose_confined_separated` with the twelve-dimensional pose that
reads the frame entries of `P i` against `P₀` with the anisotropic normalisation
`96 R · w p / w q`, and the centre coordinates with `48 R / w q`:

* *confinement.* For `p ≠ q` the symmetric hypothesis gives `|⟪e p, f q⟫| ≤ R · min / max`, so the
  normalised entry is at most `96 R · (w p / w q) · R · min (w p) (w q) / max (w p) (w q) ≤ 96 R²`
  in both cases `w p ≤ w q` and `w q < w p`; for `p = q` it is at most `96 R ≤ 96 R²`. The centre
  coordinates are at most `48 R · R = 48 R²`. So `K = 96 R²` works.
* *separation.* At separation radius `r = 1`, two poses at distance `≤ 1` have every coordinate
  within `1`, which is exactly `hfrmΔ` and `hcenΔ` of
  `Plank.not_essentiallyDistinct_of_anisotropicPose_close`; that lemma then contradicts pairwise
  essential distinctness.

The engine returns `(2 (4 K + r) / r) ^ 12 = (768 R² + 2) ^ 12`. -/
theorem card_le_of_anisotropicConfined_pairwiseED {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {ι : Type*} (ha0 : 0 < a) (F : Finset ι) (P : ι → Plank a b hab hb1)
    (P₀ : Plank a b hab hb1) {R : ℝ} (hR : 1 ≤ R)
    (hfrm : ∀ i ∈ F, ∀ j k : Fin 3, j ≠ k →
      max ((![a, b, 1] j : ℝ≥0) : ℝ) ((![a, b, 1] k : ℝ≥0) : ℝ)
          * |inner ℝ ((P i).basis j) (P₀.basis k)|
        ≤ R * min ((![a, b, 1] j : ℝ≥0) : ℝ) ((![a, b, 1] k : ℝ≥0) : ℝ))
    (hcen : ∀ i ∈ F, ∀ k : Fin 3,
      |inner ℝ (P₀.basis k) ((P i).center -ᵥ P₀.center)| ≤ R * ((![a, b, 1] k : ℝ≥0) : ℝ))
    (hED : ∀ i ∈ F, ∀ i' ∈ F, i ≠ i' →
      PrismNDim.IsEssentiallyDistinct (P i).toPrismNDim (P i').toPrismNDim) :
    (F.card : ℝ) ≤ (768 * R ^ 2 + 2) ^ 12 := by
  have hcard := card_le_of_pose_confined_separated F (fun i => anisoPose P₀ R (P i))
    (K := 96 * R ^ 2) (r := (1 : ℝ≥0)) (by positivity) (by norm_num)
    (fun i hi p => abs_anisoPose_le ha0 P₀ (P i) hR (hfrm i hi) (hcen i hi) p)
    (fun i hi i' hi' hne =>
      by simpa using one_lt_dist_anisoPose ha0 P₀ (P i) (P i') hR (hfrm i' hi') (hED i hi i' hi' hne))
  have hbound : 2 * (4 * (96 * R ^ 2) + ((1 : ℝ≥0) : ℝ)) / ((1 : ℝ≥0) : ℝ)
      = 768 * R ^ 2 + 2 := by
    rw [NNReal.coe_one]
    ring_nf
  calc
    (F.card : ℝ) ≤ (2 * (4 * (96 * R ^ 2) + ((1 : ℝ≥0) : ℝ)) / ((1 : ℝ≥0) : ℝ)) ^ 12 := hcard
    _ = (768 * R ^ 2 + 2) ^ 12 := by
      rw [hbound]

end Plank

/-! ## Tube geometry: failure of essential distinctness forces axis proximity

The EDPacking files run the implication in the direction *essential distinctness ⟹ separation*
(`Kakeya.ed_midpoint_perp_separation`, `Tube.nearly_parallel_sliding`). The bridge needs the
opposite direction: two equal-radius tubes that are **not** essentially distinct have nearly
parallel axes and nearly coincident axis lines. That is what this section supplies. -/

namespace Kakeya

open Metric

/-- Two `δ`-tubes with disjoint carriers are essentially distinct, since their intersection is
null. Contrapositive: a failure of essential distinctness produces a common point. -/
theorem exists_mem_inter_of_not_isEssentiallyDistinct {δ : ℝ≥0}
    (T₁ T₂ : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (h : ¬ IsEssentiallyDistinct T₁.carrier T₂.carrier) :
    ∃ x, x ∈ T₁.carrier ∧ x ∈ T₂.carrier := by
  by_contra hne
  push Not at hne
  apply h
  have hempty : T₁.carrier ∩ T₂.carrier = ∅ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    exact hne y
  rw [IsEssentiallyDistinct, hempty, measure_empty]
  apply zero_le

/-- Every point of a `δ`-tube lies within `δ` of a point `T.midpoint + s • T.direction` of the
axis with `|s| ≤ 1 / 2`. This is the axial parametrisation of `Tube.carrier_eq`: a point of the
core segment is `T.midpoint + (β - 1/2) • T.direction` for some `β ∈ [0, 1]`. -/
theorem exists_axis_param_of_mem_carrier {δ : ℝ≥0}
    {T : Tube δ (EuclideanSpace ℝ (Fin 3))} {p : EuclideanSpace ℝ (Fin 3)} (hp : p ∈ T.carrier) :
    ∃ s : ℝ, |s| ≤ 1 / 2 ∧ ‖p - T.midpoint - s • T.direction‖ ≤ (δ : ℝ) := by
  rw [T.carrier_eq] at hp
  obtain ⟨z, hz_seg, hpz⟩ := Set.mem_iUnion₂.mp hp
  obtain ⟨α, β, h0α, h0β, hαβ, hz_eq⟩ := hz_seg
  refine ⟨β - 1 / 2, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> linarith only [h0β, hαβ, h0α]
  · have hz_alt : z = T.midpoint + (β - 1 / 2) • T.direction := by
      rw [← hz_eq]
      change α • T.x + β • T.y = (1/2 : ℝ) • (T.x + T.y) + (β - 1/2) • (T.y - T.x)
      rw [show α = 1 - β from by linarith only [hαβ]]
      module
    rw [show p - T.midpoint - (β - 1 / 2) • T.direction = p - z from by rw [hz_alt]; abel,
      ← dist_eq_norm]
    exact hpz

/-- The transverse part `u - ⟪u, d⟫ • d` of a vector against a unit vector `d` is no longer than
`u` itself: the two summands of the orthogonal decomposition `u = (u - ⟪u,d⟫ d) + ⟪u,d⟫ d` are
orthogonal, so `‖u - ⟪u,d⟫ d‖² = ‖u‖² - ⟪u,d⟫²`. -/
theorem norm_transverse_le {d u : EuclideanSpace ℝ (Fin 3)} (hd : ‖d‖ = 1) :
    ‖u - (inner ℝ u d : ℝ) • d‖ ≤ ‖u‖ := by
  have h1 : inner ℝ u ((inner ℝ u d : ℝ) • d) = (inner ℝ u d) ^ 2 := by
    rw [real_inner_smul_right]
    ring
  have hnorm_eq : ‖(inner ℝ u d : ℝ) • d‖ = |inner ℝ u d| := by
    rw [norm_smul, hd]
    rw [Real.norm_eq_abs]
    simp
  have h2 : ‖(inner ℝ u d : ℝ) • d‖ ^ 2 = (inner ℝ u d) ^ 2 := by
    rw [hnorm_eq, sq_abs]
  have hsq : ‖u - (inner ℝ u d : ℝ) • d‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [norm_sub_sq_real]
    rw [h1, h2]
    nlinarith [sq_nonneg (inner ℝ u d)]
  have ha : 0 ≤ ‖u - (inner ℝ u d : ℝ) • d‖ := norm_nonneg _
  have hb : 0 ≤ ‖u‖ := norm_nonneg _
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb]
  exact Real.sqrt_le_sqrt hsq

/-- **Axis proximity from a common point.** If two `δ`-tubes share a point then the component of
their midpoint offset transverse to `T₂.direction` is at most `2 δ` plus half the projective
angular distance of the two directions.

Writing `x = m₁ + s₁ d₁ + e₁ = m₂ + s₂ d₂ + e₂` with `|sᵢ| ≤ 1/2` and `‖eᵢ‖ ≤ δ`, the transverse
projection `Π v = v - ⟪v, d₂⟫ • d₂` kills `s₂ d₂` and is `1`-Lipschitz, so
`‖Π (m₁ - m₂)‖ ≤ ‖e₂ - e₁‖ + |s₁| ‖Π d₁‖ ≤ 2 δ + (1/2) ‖d₁ - ⟪d₁, d₂⟫ d₂‖`, and the orthogonal
projection is the best approximation of `d₁` in `ℝ d₂`, so `‖d₁ - ⟪d₁, d₂⟫ d₂‖` is at most both
`‖d₁ - d₂‖` and `‖d₁ + d₂‖`. -/
theorem norm_transverse_midpoint_le_of_mem_inter {δ : ℝ≥0}
    (T₁ T₂ : Tube δ (EuclideanSpace ℝ (Fin 3))) {x : EuclideanSpace ℝ (Fin 3)}
    (hx₁ : x ∈ T₁.carrier) (hx₂ : x ∈ T₂.carrier) :
    ‖(T₁.midpoint - T₂.midpoint)
        - (inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction) • T₂.direction‖
      ≤ 2 * (δ : ℝ) + min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖ := by
  obtain ⟨s₁, hs₁_abs, hs₁⟩ := exists_axis_param_of_mem_carrier hx₁
  obtain ⟨s₂, hs₂_abs, hs₂⟩ := exists_axis_param_of_mem_carrier hx₂
  let W : EuclideanSpace ℝ (Fin 3) :=
    (T₁.midpoint + s₁ • T₁.direction) - (T₂.midpoint + s₂ • T₂.direction)
  have hW : ‖W‖ ≤ 2 * (δ : ℝ) := by
    have hW' : W = (x - T₂.midpoint - s₂ • T₂.direction)
        - (x - T₁.midpoint - s₁ • T₁.direction) := by
      dsimp [W]
      module
    calc
      ‖W‖ ≤ ‖x - T₂.midpoint - s₂ • T₂.direction‖
          + ‖x - T₁.midpoint - s₁ • T₁.direction‖ := by
        rw [hW']
        exact norm_sub_le _ _
      _ ≤ (δ : ℝ) + (δ : ℝ) := add_le_add hs₂ hs₁
      _ = 2 * (δ : ℝ) := by ring
  have hd2 : ‖T₂.direction‖ = 1 := T₂.norm_direction
  let Pi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun u => u - (inner ℝ u T₂.direction) • T₂.direction
  have hPi_d2 : Pi T₂.direction = 0 := by
    dsimp [Pi]
    rw [real_inner_self_eq_norm_sq, hd2]
    norm_num
  have hPi_add : ∀ u v : EuclideanSpace ℝ (Fin 3), Pi (u + v) = Pi u + Pi v := by
    intro u v
    dsimp [Pi]
    rw [inner_add_left]
    module
  have hPi_sub : ∀ u v : EuclideanSpace ℝ (Fin 3), Pi (u - v) = Pi u - Pi v := by
    intro u v
    dsimp [Pi]
    rw [inner_sub_left]
    module
  have hPi_smul : ∀ (a : ℝ) (u : EuclideanSpace ℝ (Fin 3)), Pi (a • u) = a • Pi u := by
    intro a u
    dsimp [Pi]
    rw [real_inner_smul_left]
    module
  have hm12 : T₁.midpoint - T₂.midpoint = W - s₁ • T₁.direction + s₂ • T₂.direction := by
    dsimp [W]
    module
  have hPi_mid : Pi (T₁.midpoint - T₂.midpoint) = Pi W - s₁ • Pi T₁.direction := by
    have hPi_s2 : Pi (s₂ • T₂.direction) = 0 := by
      rw [hPi_smul, hPi_d2]
      module
    calc
      Pi (T₁.midpoint - T₂.midpoint)
          = Pi (W - s₁ • T₁.direction + s₂ • T₂.direction) := by rw [hm12]
      _ = Pi (W - s₁ • T₁.direction) + Pi (s₂ • T₂.direction) := by rw [hPi_add]
      _ = Pi (W - s₁ • T₁.direction) := by rw [hPi_s2]; module
      _ = Pi W - s₁ • Pi T₁.direction := by rw [hPi_sub, hPi_smul]
  have hprojW : ‖Pi W‖ ≤ ‖W‖ := by
    simpa [Pi] using norm_transverse_le hd2
  have hPi_dsub : Pi (T₁.direction - T₂.direction) = Pi T₁.direction := by
    dsimp [Pi]
    rw [inner_sub_left, real_inner_self_eq_norm_sq, hd2]
    module
  have hPi_dadd : Pi (T₁.direction + T₂.direction) = Pi T₁.direction := by
    dsimp [Pi]
    rw [inner_add_left, real_inner_self_eq_norm_sq, hd2]
    module
  have hPid1_le_sub : ‖Pi T₁.direction‖ ≤ ‖T₁.direction - T₂.direction‖ := by
    rw [← hPi_dsub]
    simpa [Pi] using norm_transverse_le hd2
  have hPid1_le_add : ‖Pi T₁.direction‖ ≤ ‖T₁.direction + T₂.direction‖ := by
    rw [← hPi_dadd]
    simpa [Pi] using norm_transverse_le hd2
  have hPid1_bound : ‖Pi T₁.direction‖ ≤
      min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖ := by
    exact le_min hPid1_le_sub hPid1_le_add
  calc
    ‖Pi (T₁.midpoint - T₂.midpoint)‖ ≤ ‖Pi W‖ + |s₁| * ‖Pi T₁.direction‖ := by
      rw [hPi_mid]
      calc
        ‖Pi W - s₁ • Pi T₁.direction‖ ≤ ‖Pi W‖ + ‖s₁ • Pi T₁.direction‖ := norm_sub_le _ _
        _ = ‖Pi W‖ + |s₁| * ‖Pi T₁.direction‖ := by
          rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖W‖ + (1 / 2 : ℝ) * ‖Pi T₁.direction‖ := by
      nlinarith [hprojW, hs₁_abs, norm_nonneg (Pi T₁.direction)]
    _ ≤ 2 * (δ : ℝ) + (1 / 2 : ℝ) * min ‖T₁.direction - T₂.direction‖
          ‖T₁.direction + T₂.direction‖ := by
      nlinarith [hW, hPid1_bound]
    _ ≤ 2 * (δ : ℝ) + min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖ := by
      have hmin_nonneg : (0 : ℝ) ≤ min ‖T₁.direction - T₂.direction‖
          ‖T₁.direction + T₂.direction‖ := le_min (norm_nonneg _) (norm_nonneg _)
      nlinarith

/-- **Failure of essential distinctness forces axis proximity** — the tube-level input of the
anisotropic ED-packing bridge.

There is an absolute constant `Ctub > 0` (dimensional only: it is the constant of
`Kakeya.bad_axial_angle_le` in dimension three, inflated by the fixed density threshold `1/2` and
by the `2 δ` of `Kakeya.norm_transverse_midpoint_le_of_mem_inter`) such that any two `δ`-tubes
that are *not* essentially distinct have

* projective angular distance of directions at most `Ctub · δ`, and
* transverse midpoint offset at most `Ctub · δ`.

Both statements are sharp in order of magnitude: two `δ`-tubes sharing an axis but rotated by
`≫ δ`, or translated transversally by `≫ δ`, do become essentially distinct.

The angular half is `Kakeya.bad_axial_angle_le` run at the density threshold `c = 1/2`, which
`¬ IsEssentiallyDistinct` supplies directly (the intersection carries more than half the volume of
`T₁`, and `T₂.carrier ⊆ cthickening (99 δ) T₂.carrier`). The positional half then follows from
`Kakeya.exists_mem_inter_of_not_isEssentiallyDistinct` and
`Kakeya.norm_transverse_midpoint_le_of_mem_inter`. -/
theorem exists_notED_tube_axis_bound :
    ∃ Ctub : ℝ, 0 < Ctub ∧
      ∀ {δ : ℝ≥0}, 0 < δ → δ ≤ 1 →
        ∀ T₁ T₂ : Tube δ (EuclideanSpace ℝ (Fin 3)),
          ¬ IsEssentiallyDistinct T₁.carrier T₂.carrier →
          min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖ ≤ Ctub * (δ : ℝ) ∧
          ‖(T₁.midpoint - T₂.midpoint)
              - (inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction) • T₂.direction‖
            ≤ Ctub * (δ : ℝ) := by
  have hfr : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by simp
  obtain ⟨C, hC, hbound⟩ := bad_axial_angle_le (E := EuclideanSpace ℝ (Fin 3)) hfr
  refine ⟨2 * C + 2, by positivity, ?_⟩
  intro δ hδ0 hδ1 T₁ T₂ h
  have hδ_pos : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hδ_nonneg : 0 ≤ (δ : ℝ) := le_of_lt hδ_pos
  have hlt : (1 / 2 : ENNReal) * max (volume T₁.carrier) (volume T₂.carrier)
      < volume (T₁.carrier ∩ T₂.carrier) := by
    exact not_le.mp (by simpa [IsEssentiallyDistinct] using h)
  have hbad : ENNReal.ofReal (1 / 2 : ℝ) * volume T₁.carrier
      ≤ volume (T₁.carrier ∩ Metric.cthickening (99 * (δ : ℝ)) T₂.carrier) := by
    have ho : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [ho]
    calc
      (1 / 2 : ENNReal) * volume T₁.carrier
          ≤ (1 / 2 : ENNReal) * max (volume T₁.carrier) (volume T₂.carrier) := by
            gcongr
            exact le_max_left _ _
      _ ≤ volume (T₁.carrier ∩ T₂.carrier) := hlt.le
      _ ≤ volume (T₁.carrier ∩ Metric.cthickening (99 * (δ : ℝ)) T₂.carrier) := by
            exact measure_mono
              (Set.inter_subset_inter_right _ (Metric.self_subset_cthickening _))
  have hdir : min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖
      ≤ C * (δ : ℝ) / (1 / 2) := by
    exact hbound hδ0 hδ1 T₁ T₂ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hbad
  have hdir2 : min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖
      ≤ 2 * C * (δ : ℝ) := by
    have hCδ : C * (δ : ℝ) / (1 / 2) = 2 * C * (δ : ℝ) := by
      field_simp
    rw [hCδ] at hdir
    exact hdir
  have hc1 : min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖
      ≤ (2 * C + 2) * (δ : ℝ) := by
    calc
      min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖ ≤ 2 * C * (δ : ℝ) := hdir2
      _ ≤ (2 * C + 2) * (δ : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by norm_num : (2 * C : ℝ) ≤ 2 * C + 2) hδ_nonneg
  obtain ⟨x, hx₁, hx₂⟩ := exists_mem_inter_of_not_isEssentiallyDistinct T₁ T₂ h
  have hpos := norm_transverse_midpoint_le_of_mem_inter T₁ T₂ hx₁ hx₂
  have hc2 : ‖(T₁.midpoint - T₂.midpoint)
      - (inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction) • T₂.direction‖
      ≤ (2 * C + 2) * (δ : ℝ) := by
    calc
      ‖(T₁.midpoint - T₂.midpoint)
          - (inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction) • T₂.direction‖
          ≤ 2 * (δ : ℝ) + min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖ := hpos
      _ ≤ 2 * (δ : ℝ) + 2 * C * (δ : ℝ) := by
        exact add_le_add_right hdir2 (2 * (δ : ℝ))
      _ = (2 * C + 2) * (δ : ℝ) := by ring
  exact ⟨hc1, hc2⟩

end Kakeya

/-! ## Pulling tube axis proximity back to the slab frame

`Kakeya.exists_notED_tube_axis_bound` controls the two tubes' axes in the *normalised* picture.
The anisotropic packing bound of `Plank.card_le_of_anisotropicConfined_pairwiseED` wants control of
the two prisms' frames and centres in the *source* picture, at the weights `w = (θ b, b, 1)`. The
lemmas below are the dictionary. They rest on the fact that the linear part of
`Slab.normalizeScaled S κ` is diagonal in `S.basis`, with entries `(κ/θ, κ, κ)`: a bound on
`‖L v‖` therefore gives a bound `θ ‖L v‖ / κ` on the `S.basis 0`-component of `v` and `‖L v‖ / κ`
on the other two — exactly the anisotropy `(θ b, b, b)` that the packing bound consumes. -/

namespace Plank

/-- The linear part of `Slab.normalizeScaled S κ` is diagonal in `S.basis` with entries
`(κ/θ, κ, κ)`. -/
theorem inner_basis_normalizeScaled_linear {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (κ : ℝ≥0)
    (hθ0 : 0 < θ) (hκ : 0 < κ) (k : Fin 3) (v : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (S.basis k) ((Slab.normalizeScaled S κ hθ0 hκ).linear v)
      = (![(κ : ℝ) * (θ : ℝ)⁻¹, (κ : ℝ), (κ : ℝ)] k) * inner ℝ (S.basis k) v := by
  have h : (Slab.normalizeScaled S κ hθ0 hκ).linear v
      = Kakeya.frameDiagLinear S.basis ![(κ : ℝ) * (θ : ℝ)⁻¹, (κ : ℝ), (κ : ℝ)] v := by
    rfl
  rw [h, ← OrthonormalBasis.repr_apply_apply, ← OrthonormalBasis.repr_apply_apply,
    Kakeya.repr_frameDiagLinear]

/-- **The anisotropic dictionary.** A bound `‖L v‖ ≤ M` on the normalised image of `v` bounds the
`S.basis 0`-component of `v` by `M θ / κ` and the other two components by `M / κ`. -/
theorem abs_inner_basis_le_of_norm_linear_le {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (κ : ℝ≥0)
    (hθ0 : 0 < θ) (hκ : 0 < κ) {v : EuclideanSpace ℝ (Fin 3)} {M : ℝ}
    (hM : ‖(Slab.normalizeScaled S κ hθ0 hκ).linear v‖ ≤ M) :
    |inner ℝ (S.basis 0) v| ≤ M * (θ : ℝ) / (κ : ℝ) ∧
      |inner ℝ (S.basis 1) v| ≤ M / (κ : ℝ) ∧
      |inner ℝ (S.basis 2) v| ≤ M / (κ : ℝ) := by
  have hκR : 0 < (κ : ℝ) := NNReal.coe_pos.mpr hκ
  have hθR : 0 < (θ : ℝ) := NNReal.coe_pos.mpr hθ0
  have hγ : (κ : ℝ) ≠ 0 := ne_of_gt hκR
  have hτ0 : (θ : ℝ) ≠ 0 := ne_of_gt hθR
  have ho0 : 0 < (κ : ℝ) * (θ : ℝ)⁻¹ := mul_pos hκR (inv_pos.mpr hθR)
  let L : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (Slab.normalizeScaled S κ hθ0 hκ).linear
  -- k = 1, 2: the diagonal entry is κ
  have hmain : ∀ k : Fin 3, k ≠ 0 →
      |inner ℝ (S.basis k) v| ≤ M / (κ : ℝ) := by
    intro k hk0
    have hcs : |inner ℝ (S.basis k) (L v)| ≤ ‖S.basis k‖ * ‖L v‖ :=
      abs_real_inner_le_norm (S.basis k) (L v)
    have hb : ‖L v‖ ≤ M := by
      simpa [L] using hM
    have hcsw : |inner ℝ (S.basis k) (L v)| ≤ ‖L v‖ := by
      simpa [S.basis.norm_eq_one k] using hcs
    have hind : |inner ℝ (S.basis k) (L v)| ≤ M := hcsw.trans hb
    have hdict := inner_basis_normalizeScaled_linear S κ hθ0 hκ k v
    have hdict' : inner ℝ (S.basis k) (L v) = (κ : ℝ) * inner ℝ (S.basis k) v := by
      fin_cases k
      · contradiction
      · simpa [L] using hdict
      · simpa [L] using hdict
    rw [hdict'] at hind
    have hlle : (κ : ℝ) * |inner ℝ (S.basis k) v| ≤ M := by
      simpa [abs_mul, abs_of_pos hκR] using hind
    rw [le_div_iff₀ hκR, mul_comm]
    exact hlle
  constructor
  · -- k = 0: the diagonal entry is κ / θ
    have hcs : |inner ℝ (S.basis 0) (L v)| ≤ ‖S.basis 0‖ * ‖L v‖ :=
      abs_real_inner_le_norm (S.basis 0) (L v)
    have hb : ‖L v‖ ≤ M := by
      simpa [L] using hM
    have hcsw : |inner ℝ (S.basis 0) (L v)| ≤ ‖L v‖ := by
      simpa [S.basis.norm_eq_one 0] using hcs
    have hind : |inner ℝ (S.basis 0) (L v)| ≤ M := hcsw.trans hb
    have hdict := inner_basis_normalizeScaled_linear S κ hθ0 hκ 0 v
    have hdict' : inner ℝ (S.basis 0) (L v) = (κ : ℝ) * (θ : ℝ)⁻¹ * inner ℝ (S.basis 0) v := by
      simpa [L] using hdict
    rw [hdict'] at hind
    have hlle : (κ : ℝ) * (θ : ℝ)⁻¹ * |inner ℝ (S.basis 0) v| ≤ M := by
      simpa [abs_mul, abs_of_pos ho0] using hind
    have hle : |inner ℝ (S.basis 0) v| ≤ M / ((κ : ℝ) * (θ : ℝ)⁻¹) := by
      rw [le_div_iff₀ ho0, mul_comm]
      exact hlle
    have hEq : M / ((κ : ℝ) * (θ : ℝ)⁻¹) = M * (θ : ℝ) / (κ : ℝ) := by
      field_simp [hγ, hτ0]
    rw [hEq] at hle
    exact hle
  · constructor
    · exact hmain 1 (by decide)
    · exact hmain 2 (by decide)

/-- A vector is no longer than the sum of the absolute values of its coordinates in an orthonormal
frame. -/
theorem norm_le_sum_abs_inner_basis
    (B : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) (v : EuclideanSpace ℝ (Fin 3)) :
    ‖v‖ ≤ |inner ℝ (B 0) v| + |inner ℝ (B 1) v| + |inner ℝ (B 2) v| := by
  calc
    ‖v‖ = ‖∑ i : Fin 3, (inner ℝ (B i) v) • B i‖ := by
      rw [B.sum_repr' v]
    _ ≤ ∑ i : Fin 3, ‖(inner ℝ (B i) v) • B i‖ := by
      simpa using (norm_sum_le (Finset.univ : Finset (Fin 3))
        (fun i : Fin 3 => (inner ℝ (B i) v) • B i))
    _ = ∑ i : Fin 3, |inner ℝ (B i) v| := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_smul, B.norm_eq_one, mul_one, Real.norm_eq_abs]
    _ = |inner ℝ (B 0) v| + |inner ℝ (B 1) v| + |inner ℝ (B 2) v| := by
      rw [Fin.sum_univ_three]

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ : θ ≤ 1}

/-- The midpoint of `Plank.slabTube` is the normalised image of the plank's centre. -/
theorem slabTube_midpoint (P : Plank a b hab hb1) (S : Slab θ hθ) (κ : ℝ≥0) (hθ0 : 0 < θ)
    (hκ : 0 < κ) :
    (P.slabTube S κ hθ0 hκ).midpoint = Slab.normalizeScaled S κ hθ0 hκ P.center := by
  simp [Plank.slabTube, Tube.midpoint]
  module

/-- The direction of `Plank.slabTube` is `Plank.slabTubeDir`. -/
theorem slabTube_direction (P : Plank a b hab hb1) (S : Slab θ hθ) (κ : ℝ≥0) (hθ0 : 0 < θ)
    (hκ : 0 < κ) :
    (P.slabTube S κ hθ0 hκ).direction = P.slabTubeDir S κ hθ0 hκ := by
  simp [Plank.slabTube, Tube.direction]
  module

/-- **Direction closeness, pulled back.** If the two normalised tube directions are within `ε` in
projective distance, then the long axis of `P` agrees with a *multiple* of the long axis of `P₀` to
within `ε ‖L u₂‖` after normalisation. The scalar `t` is `± ‖L u₂‖ / ‖L u₂'‖`, so it is nonzero and
its size is pinned by the two image lengths — which the tangency hypothesis bounds above and below
by absolute multiples of `κ`. -/
theorem exists_axis_scalar (P P₀ : Plank a b hab hb1) (S : Slab θ hθ) (κ : ℝ≥0) (hθ0 : 0 < θ)
    (hκ : 0 < κ) {ε : ℝ}
    (hdir : min ‖P.slabTubeDir S κ hθ0 hκ - P₀.slabTubeDir S κ hθ0 hκ‖
              ‖P.slabTubeDir S κ hθ0 hκ + P₀.slabTubeDir S κ hθ0 hκ‖ ≤ ε) :
    ∃ t : ℝ,
      |t| * ‖(Slab.normalizeScaled S κ hθ0 hκ).linear (P₀.basis 2)‖
          = ‖(Slab.normalizeScaled S κ hθ0 hκ).linear (P.basis 2)‖ ∧
      ‖(Slab.normalizeScaled S κ hθ0 hκ).linear (P.basis 2 - t • P₀.basis 2)‖
          ≤ ‖(Slab.normalizeScaled S κ hθ0 hκ).linear (P.basis 2)‖ * ε := by
  let L : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (Slab.normalizeScaled S κ hθ0 hκ).linear
  let u : EuclideanSpace ℝ (Fin 3) := P.basis 2
  let u₀ : EuclideanSpace ℝ (Fin 3) := P₀.basis 2
  let n : ℝ := ‖L u‖
  let n₀ : ℝ := ‖L u₀‖
  let d : EuclideanSpace ℝ (Fin 3) := P.slabTubeDir S κ hθ0 hκ
  let d₀ : EuclideanSpace ℝ (Fin 3) := P₀.slabTubeDir S κ hθ0 hκ
  have hu : ‖u‖ = 1 := by simpa [u] using OrthonormalBasis.norm_eq_one P.basis 2
  have hu₀ : ‖u₀‖ = 1 := by simpa [u₀] using OrthonormalBasis.norm_eq_one P₀.basis 2
  have hn : 0 < n := by
    have hle : (κ : ℝ) ≤ n := le_norm_normalizeScaled_linear S κ hθ0 hκ hu
    linarith [NNReal.coe_pos.mpr hκ]
  have hn₀ : 0 < n₀ := by
    have hle : (κ : ℝ) ≤ n₀ := le_norm_normalizeScaled_linear S κ hθ0 hκ hu₀
    linarith [NNReal.coe_pos.mpr hκ]
  have hd : d = n⁻¹ • L u := by simp [d, slabTubeDir, L, u, n]
  have hd₀ : d₀ = n₀⁻¹ • L u₀ := by simp [d₀, slabTubeDir, L, u₀, n₀]
  have hn_ne : n ≠ 0 := ne_of_gt hn
  have hn₀_ne : n₀ ≠ 0 := ne_of_gt hn₀
  have hn_nonneg : 0 ≤ n := le_of_lt hn
  have hLd : L u = n • d := by
    rw [hd, smul_smul, mul_inv_cancel₀ hn_ne, one_smul]
  have hLd₀ : L u₀ = n₀ • d₀ := by
    rw [hd₀, smul_smul, mul_inv_cancel₀ hn₀_ne, one_smul]
  change ∃ t : ℝ, |t| * n₀ = n ∧ ‖L (u - t • u₀)‖ ≤ n * ε
  rcases min_le_iff.mp hdir with hcase | hcase
  · refine ⟨n / n₀, ?_, ?_⟩
    · rw [abs_div, abs_of_pos hn, abs_of_pos hn₀, div_mul_cancel₀ _ hn₀_ne]
    · have hvec : L (u - (n / n₀) • u₀) = n • (d - d₀) := by
        rw [map_sub, map_smul, hLd, hLd₀, smul_smul]
        rw [div_mul_cancel₀ _ hn₀_ne]
        module
      rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_nonneg hn_nonneg]
      exact mul_le_mul_of_nonneg_left hcase hn_nonneg
  · refine ⟨-(n / n₀), ?_, ?_⟩
    · rw [abs_neg, abs_div, abs_of_pos hn, abs_of_pos hn₀, div_mul_cancel₀ _ hn₀_ne]
    · have hvec : L (u - (-(n / n₀)) • u₀) = n • (d + d₀) := by
        rw [map_sub, map_smul, hLd, hLd₀, smul_smul]
        rw [neg_mul, div_mul_cancel₀ _ hn₀_ne]
        module
      rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_nonneg hn_nonneg]
      exact mul_le_mul_of_nonneg_left hcase hn_nonneg

/-- **Position closeness, pulled back.** If the transverse part of the two normalised tube
midpoints is at most `ε`, then the centre offset of the two planks agrees with a multiple of the
long axis of `P₀` to within `ε` after normalisation. -/
theorem exists_center_scalar (P P₀ : Plank a b hab hb1) (S : Slab θ hθ) (κ : ℝ≥0) (hθ0 : 0 < θ)
    (hκ : 0 < κ) {ε : ℝ}
    (hpos : ‖((P.slabTube S κ hθ0 hκ).midpoint - (P₀.slabTube S κ hθ0 hκ).midpoint)
        - (inner ℝ ((P.slabTube S κ hθ0 hκ).midpoint - (P₀.slabTube S κ hθ0 hκ).midpoint)
            (P₀.slabTube S κ hθ0 hκ).direction) • (P₀.slabTube S κ hθ0 hκ).direction‖ ≤ ε) :
    ∃ r : ℝ,
      ‖(Slab.normalizeScaled S κ hθ0 hκ).linear
          ((P.center -ᵥ P₀.center) - r • P₀.basis 2)‖ ≤ ε := by
  let g : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    Slab.normalizeScaled S κ hθ0 hκ
  let L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) := g.linear
  let u0 : EuclideanSpace ℝ (Fin 3) := P₀.basis 2
  let d0 : EuclideanSpace ℝ (Fin 3) := P₀.slabTubeDir S κ hθ0 hκ
  let Delta : EuclideanSpace ℝ (Fin 3) := P.center -ᵥ P₀.center
  let s : ℝ := inner ℝ (L Delta) d0
  let r : ℝ := s / ‖L u0‖
  have hm : g P.center - g P₀.center = L Delta := by
    simpa [L, g, Delta, vsub_eq_sub] using
      (AffineMap.linearMap_vsub
        (Slab.normalizeScaled S κ hθ0 hκ : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ]
          EuclideanSpace ℝ (Fin 3)) P.center P₀.center).symm
  have hd0 : d0 = ‖L u0‖⁻¹ • L u0 := by
    simp [d0, slabTubeDir, L, u0, g]
  have hsd : s • d0 = L (r • u0) := by
    rw [hd0]
    calc
      s • (‖L u0‖⁻¹ • L u0) = (s * ‖L u0‖⁻¹) • L u0 := by rw [smul_smul]
      _ = (s / ‖L u0‖) • L u0 := rfl
      _ = r • L u0 := rfl
      _ = L (r • u0) := by rw [← map_smul]
  have h1 : ‖L Delta - s • d0‖ ≤ ε := by
    rw [slabTube_midpoint P S κ hθ0 hκ, slabTube_midpoint P₀ S κ hθ0 hκ,
      slabTube_direction P₀ S κ hθ0 hκ] at hpos
    change ‖(g P.center - g P₀.center)
        - (inner ℝ (g P.center - g P₀.center) d0) • d0‖ ≤ ε at hpos
    simp only [hm] at hpos
    simpa [s] using hpos
  have hrewrite : L (Delta - r • u0) = L Delta - s • d0 := by
    rw [map_sub]
    congr 1
    exact hsd.symm
  exact ⟨r, by
    change ‖L (Delta - r • u0)‖ ≤ ε
    rw [hrewrite]
    exact h1⟩

/-! ### From slab-frame profiles to anisotropic pose confinement

The two `exists_*_scalar` lemmas turn tube axis proximity into control of the `S`-frame components
of `v := u₂ - t · u₂'` and `z := (c - c') - r · u₂'`, with the anisotropic profile
`(θ b, b, b)`. The two lemmas below convert such a profile into the *symmetric anisotropic*
confinement hypotheses of `Plank.card_le_of_anisotropicConfined_pairwiseED`. They are pure
inner-product algebra: no measure theory and no tube left. -/

/-- **Frame expansion against a tangential axis.** If `x` is almost orthogonal to the two long
directions of `S` (`|⟪x, S.basis j⟫| ≤ c` for `j ≠ 0`, the tangency profile of a fibre prism's
short axis) and the `S`-frame components of `v` are bounded by `A₀, A₁, A₂`, then
`|⟪x, v⟫| ≤ A₀ + (A₁ + A₂) c`. Only the `S.basis 0` component of `v` enters at full strength. -/
theorem abs_inner_le_of_slab_profile {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    (x v : EuclideanSpace ℝ (Fin 3)) {c A₀ A₁ A₂ : ℝ} (hc : 0 ≤ c)
    (hx0 : |inner ℝ x (S.basis 0)| ≤ 1)
    (hx1 : |inner ℝ x (S.basis 1)| ≤ c) (hx2 : |inner ℝ x (S.basis 2)| ≤ c)
    (h0 : |inner ℝ (S.basis 0) v| ≤ A₀) (h1 : |inner ℝ (S.basis 1) v| ≤ A₁)
    (h2 : |inner ℝ (S.basis 2) v| ≤ A₂) (hA1 : 0 ≤ A₁) (hA2 : 0 ≤ A₂) :
    |inner ℝ x v| ≤ A₀ + (A₁ + A₂) * c := by
  have hframe := abs_inner_le_sum_frame S.basis x v
  have hA0nn : 0 ≤ A₀ := le_trans (abs_nonneg _) h0
  have hterm0 : |inner ℝ (S.basis 0) v| * |inner ℝ x (S.basis 0)| ≤ A₀ * 1 := by
    exact mul_le_mul h0 hx0 (abs_nonneg _) hA0nn
  have hterm1 : |inner ℝ (S.basis 1) v| * |inner ℝ x (S.basis 1)| ≤ A₁ * c := by
    exact mul_le_mul h1 hx1 (abs_nonneg _) hA1
  have hterm2 : |inner ℝ (S.basis 2) v| * |inner ℝ x (S.basis 2)| ≤ A₂ * c := by
    exact mul_le_mul h2 hx2 (abs_nonneg _) hA2
  calc
    |inner ℝ x v| ≤ |inner ℝ (S.basis 0) v| * |inner ℝ x (S.basis 0)|
        + |inner ℝ (S.basis 1) v| * |inner ℝ x (S.basis 1)|
        + |inner ℝ (S.basis 2) v| * |inner ℝ x (S.basis 2)| := hframe
    _ ≤ A₀ * 1 + A₁ * c + A₂ * c := by
      nlinarith [hterm0, hterm1, hterm2]
    _ = A₀ + (A₁ + A₂) * c := by ring

/-- **Numerical assembly of the six off-diagonal frame entries.** At the weights
`w = (θ b, b, 1)` with `θ b ≤ b ≤ 1`, the symmetric anisotropic confinement
`max (w j) (w k) · |⟪e j, f k⟫| ≤ R · min (w j) (w k)` unwinds to exactly six scalar bounds: the
two entries in the `(0,1)` block need `|⟪·,·⟫| ≤ R θ`, the two entries pairing index `2` with
index `0` need `≤ R θ b`, and the two pairing index `2` with index `1` need `≤ R b`. -/
theorem frame_confined_of_entries {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}
    (Q Q₀ : ThickenedPlank θ b hθ1 hb1) {R : ℝ} (hb0 : 0 < b) (hR : 0 ≤ R)
    (h01 : |inner ℝ (Q.basis 0) (Q₀.basis 1)| ≤ R * (θ : ℝ))
    (h10 : |inner ℝ (Q.basis 1) (Q₀.basis 0)| ≤ R * (θ : ℝ))
    (h02 : |inner ℝ (Q.basis 0) (Q₀.basis 2)| ≤ R * (θ : ℝ) * (b : ℝ))
    (h20 : |inner ℝ (Q.basis 2) (Q₀.basis 0)| ≤ R * (θ : ℝ) * (b : ℝ))
    (h12 : |inner ℝ (Q.basis 1) (Q₀.basis 2)| ≤ R * (b : ℝ))
    (h21 : |inner ℝ (Q.basis 2) (Q₀.basis 1)| ≤ R * (b : ℝ)) :
    ∀ j k : Fin 3, j ≠ k →
      max ((![θ * b, b, 1] j : ℝ≥0) : ℝ) ((![θ * b, b, 1] k : ℝ≥0) : ℝ)
          * |inner ℝ (Q.basis j) (Q₀.basis k)|
        ≤ R * min ((![θ * b, b, 1] j : ℝ≥0) : ℝ) ((![θ * b, b, 1] k : ℝ≥0) : ℝ) := by
  have hth : (θ : ℝ) ≤ 1 := NNReal.coe_le_coe.mpr hθ1
  have hth0 : (0 : ℝ) ≤ (θ : ℝ) := (θ : ℝ≥0).coe_nonneg
  have hbb : (b : ℝ) ≤ 1 := NNReal.coe_le_coe.mpr hb1
  have hb' : (0 : ℝ) < (b : ℝ) := NNReal.coe_pos.mpr hb0
  have hb0' : (0 : ℝ) ≤ (b : ℝ) := le_of_lt hb'
  have hprod : (θ : ℝ) * (b : ℝ) ≤ (b : ℝ) := by nlinarith [hth, hb']
  have hθb1 : (θ : ℝ) * (b : ℝ) ≤ 1 := by nlinarith [hprod, hbb]
  intro j k hjk
  fin_cases j <;> fin_cases k
  · exact absurd rfl hjk
  · -- (0,1): need b * |inner| ≤ Rθb, from h01
    have h01b : (b : ℝ) * |inner ℝ (Q.basis 0) (Q₀.basis 1)| ≤
        R * ((θ : ℝ) * (b : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left h01 hb0'
      nlinarith
    simpa [max_eq_right hprod, min_eq_left hprod] using h01b
  · -- (0,2): need 1 * |inner| ≤ Rθb, from h02
    have h02b : 1 * |inner ℝ (Q.basis 0) (Q₀.basis 2)| ≤
        R * ((θ : ℝ) * (b : ℝ)) := by
      nlinarith [h02]
    simpa [max_eq_right hθb1, min_eq_left hθb1] using h02b
  · -- (1,0): need b * |inner| ≤ Rθb, from h10
    have h10b : (b : ℝ) * |inner ℝ (Q.basis 1) (Q₀.basis 0)| ≤
        R * ((θ : ℝ) * (b : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left h10 hb0'
      nlinarith
    simpa [max_eq_left hprod, min_eq_right hprod] using h10b
  · exact absurd rfl hjk
  · -- (1,2): need 1 * |inner| ≤ Rb, from h12
    have h12b : 1 * |inner ℝ (Q.basis 1) (Q₀.basis 2)| ≤ R * (b : ℝ) := by
      nlinarith [h12]
    simpa [max_eq_right hbb, min_eq_left hbb] using h12b
  · -- (2,0): need 1 * |inner| ≤ Rθb, from h20
    have h20b : 1 * |inner ℝ (Q.basis 2) (Q₀.basis 0)| ≤
        R * ((θ : ℝ) * (b : ℝ)) := by
      nlinarith [h20]
    simpa [max_eq_left hθb1, min_eq_right hθb1] using h20b
  · -- (2,1): need 1 * |inner| ≤ Rb, from h21
    have h21b : 1 * |inner ℝ (Q.basis 2) (Q₀.basis 1)| ≤ R * (b : ℝ) := by
      nlinarith [h21]
    simpa [max_eq_left hbb, min_eq_right hbb] using h21b
  · exact absurd rfl hjk

/-- **Inverting the comparison scalar.** If `x` is orthogonal to `Q`'s long axis, then testing `x`
against the *reference* long axis is the same as testing it against
`v = Q.basis 2 - t • Q₀.basis 2`, up to the factor `t⁻¹`. -/
theorem abs_inner_ref_longAxis_le {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}
    (Q Q₀ : ThickenedPlank θ b hθ1 hb1) {t T M : ℝ} (ht0 : t ≠ 0) (htinv : |t⁻¹| ≤ T)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : inner ℝ x (Q.basis 2) = 0)
    (hM : |inner ℝ x (Q.basis 2 - t • Q₀.basis 2)| ≤ M) :
    |inner ℝ x (Q₀.basis 2)| ≤ T * M := by
  have hexp : inner ℝ x (Q.basis 2 - t • Q₀.basis 2)
      = - (t * inner ℝ x (Q₀.basis 2)) := by
    rw [inner_sub_right, real_inner_smul_right, hx]; ring
  have hval : inner ℝ x (Q₀.basis 2) = -(t⁻¹ * inner ℝ x (Q.basis 2 - t • Q₀.basis 2)) := by
    rw [hexp]; field_simp [ht0]
  rw [hval, abs_neg, abs_mul]
  let w : ℝ := inner ℝ x (Q.basis 2 - t • Q₀.basis 2)
  have hM' : |w| ≤ M := by simpa [w] using hM
  change |t⁻¹| * |w| ≤ T * M
  have hw0 : (0:ℝ) ≤ |w| := abs_nonneg _
  have hprod : |t⁻¹| * |w| ≤ T * |w| := mul_le_mul_of_nonneg_right htinv hw0
  have hT0 : (0:ℝ) ≤ T := le_trans (abs_nonneg _) htinv
  exact hprod.trans (mul_le_mul_of_nonneg_left hM' hT0)

/-- **The dual step.** If `y` is orthogonal to the reference long axis, then testing `Q`'s long
axis against `y` is the same as testing `v = Q.basis 2 - t • Q₀.basis 2` against `y`. -/
theorem inner_longAxis_eq_of_orthogonal {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}
    (Q Q₀ : ThickenedPlank θ b hθ1 hb1) (t : ℝ) (y : EuclideanSpace ℝ (Fin 3))
    (hy : inner ℝ (Q₀.basis 2) y = 0) :
    inner ℝ (Q.basis 2) y = inner ℝ (Q.basis 2 - t • Q₀.basis 2) y := by
  rw [inner_sub_left, real_inner_smul_left, hy]
  ring

/-- **A tangential short axis against a long axis.** If `x` is almost orthogonal to the two long
directions of `S` and `y` is almost orthogonal to the short direction of `S`, then
`|⟪x, y⟫| ≤ 3 Ctan θ`. This covers the `(0,1)` and `(1,0)` entries. -/
theorem abs_inner_short_long_le {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) {Ctan : ℝ}
    (hCtan : 0 ≤ Ctan) (x y : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hx1 : |inner ℝ x (S.basis 1)| ≤ Ctan * (θ : ℝ))
    (hx2 : |inner ℝ x (S.basis 2)| ≤ Ctan * (θ : ℝ))
    (hy0 : |inner ℝ (S.basis 0) y| ≤ Ctan * (θ : ℝ)) :
    |inner ℝ x y| ≤ 3 * Ctan * (θ : ℝ) := by
  have hc : 0 ≤ Ctan * (θ : ℝ) := mul_nonneg hCtan (θ : ℝ≥0).coe_nonneg
  have hx0 : |inner ℝ x (S.basis 0)| ≤ 1 := by
    calc
      |inner ℝ x (S.basis 0)| ≤ ‖x‖ * ‖S.basis 0‖ := abs_real_inner_le_norm x (S.basis 0)
      _ = 1 * 1 := by rw [hx, S.basis.norm_eq_one 0]
      _ = 1 := by ring
  have h1 : |inner ℝ (S.basis 1) y| ≤ 1 := by
    calc
      |inner ℝ (S.basis 1) y| ≤ ‖S.basis 1‖ * ‖y‖ := abs_real_inner_le_norm (S.basis 1) y
      _ = 1 * 1 := by rw [S.basis.norm_eq_one 1, hy]
      _ = 1 := by ring
  have h2 : |inner ℝ (S.basis 2) y| ≤ 1 := by
    calc
      |inner ℝ (S.basis 2) y| ≤ ‖S.basis 2‖ * ‖y‖ := abs_real_inner_le_norm (S.basis 2) y
      _ = 1 * 1 := by rw [S.basis.norm_eq_one 2, hy]
      _ = 1 := by ring
  have hle := abs_inner_le_of_slab_profile S x y
    (c := Ctan * (θ : ℝ)) (A₀ := Ctan * (θ : ℝ)) (A₁ := 1) (A₂ := 1)
    hc hx0 hx1 hx2 hy0 h1 h2 zero_le_one zero_le_one
  nlinarith [hle, hc]

/-- **A tangential short axis against the comparison vector.** With the anisotropic profile
`(A θ b, A b, A b)` for `v`, a tangential axis sees `v` only at the scale `θ b`. This covers the
`(0,2)` and `(2,0)` entries. -/
theorem abs_inner_short_profile_le {θ b : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    {Ctan A : ℝ} (hCtan : 0 ≤ Ctan) (hA : 0 ≤ A)
    (x v : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1)
    (hx1 : |inner ℝ x (S.basis 1)| ≤ Ctan * (θ : ℝ))
    (hx2 : |inner ℝ x (S.basis 2)| ≤ Ctan * (θ : ℝ))
    (hv0 : |inner ℝ (S.basis 0) v| ≤ A * (θ : ℝ) * (b : ℝ))
    (hv1 : |inner ℝ (S.basis 1) v| ≤ A * (b : ℝ))
    (hv2 : |inner ℝ (S.basis 2) v| ≤ A * (b : ℝ)) :
    |inner ℝ x v| ≤ A * (1 + 2 * Ctan) * (θ : ℝ) * (b : ℝ) := by
  have hx0 : |inner ℝ x (S.basis 0)| ≤ 1 := by
    have hcs : |inner ℝ x (S.basis 0)| ≤ ‖x‖ * ‖S.basis 0‖ :=
      abs_real_inner_le_norm x (S.basis 0)
    simpa [hx, S.basis.norm_eq_one 0] using hcs
  have hle := abs_inner_le_of_slab_profile S x v
    (c := Ctan * (θ : ℝ)) (A₀ := A * (θ : ℝ) * (b : ℝ))
    (A₁ := A * (b : ℝ)) (A₂ := A * (b : ℝ))
    (mul_nonneg hCtan (θ : ℝ≥0).coe_nonneg) hx0 hx1 hx2 hv0 hv1 hv2
    (mul_nonneg hA (b : ℝ≥0).coe_nonneg) (mul_nonneg hA (b : ℝ≥0).coe_nonneg)
  calc
    |inner ℝ x v| ≤ A * (θ : ℝ) * (b : ℝ) + (A * (b : ℝ) + A * (b : ℝ)) * (Ctan * (θ : ℝ)) := hle
    _ = A * (1 + 2 * Ctan) * (θ : ℝ) * (b : ℝ) := by ring

/-- The comparison vector has length `≤ 3 A b`: its `S`-frame profile is `(A θ b, A b, A b)` and
`θ ≤ 1`. -/
theorem norm_le_of_slab_profile {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    {A : ℝ} {b : ℝ≥0} (hA : 0 ≤ A) (v : EuclideanSpace ℝ (Fin 3))
    (hv0 : |inner ℝ (S.basis 0) v| ≤ A * (θ : ℝ) * (b : ℝ))
    (hv1 : |inner ℝ (S.basis 1) v| ≤ A * (b : ℝ))
    (hv2 : |inner ℝ (S.basis 2) v| ≤ A * (b : ℝ)) :
    ‖v‖ ≤ 3 * A * (b : ℝ) := by
  have h := norm_le_sum_abs_inner_basis S.basis v
  have hθ : (θ : ℝ) ≤ 1 := NNReal.coe_le_coe.mpr hθ1
  have hb0 : 0 ≤ (b : ℝ) := (b : ℝ≥0).coe_nonneg
  have hbound : A * (θ : ℝ) * (b : ℝ) + A * (b : ℝ) + A * (b : ℝ) ≤ 3 * A * (b : ℝ) := by
    have hθ2 : (θ : ℝ) + 2 ≤ 3 := by nlinarith [hθ]
    have hab2 : 0 ≤ A * (b : ℝ) := mul_nonneg hA hb0
    calc
      A * (θ : ℝ) * (b : ℝ) + A * (b : ℝ) + A * (b : ℝ) = (A * (b : ℝ)) * ((θ : ℝ) + 2) := by ring
      _ ≤ (A * (b : ℝ)) * 3 := mul_le_mul_of_nonneg_left hθ2 hab2
      _ = 3 * A * (b : ℝ) := by ring
  nlinarith

/-- **Anisotropic centre confinement from a slab profile.** If the centre offset
`Δ = Q.center -ᵥ Q₀.center` differs from a multiple of `Q₀.basis 2` by a vector `z` with the
anisotropic profile `(B θ b, B b, B b)` in the `S` frame, and `‖Δ‖ ≤ D`, then the three reference
coordinates of `Δ` obey the anisotropic bound at the weights `(θ b, b, 1)`.

For `k = 0, 1` the multiple of `Q₀.basis 2` is annihilated by `⟪Q₀.basis k, ·⟫`, so the coordinate
is the corresponding coordinate of `z`; the long coordinate `k = 2` is controlled crudely by
`‖Δ‖`, which is all that is needed since its weight is `1`. -/
theorem center_confined_of_slab_profile {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}
    (S : Slab θ hθ1) (Q Q₀ : ThickenedPlank θ b hθ1 hb1)
    {Ctan B D r : ℝ} (hb0 : 0 < b) (hCtan : 0 ≤ Ctan) (hB : 0 ≤ B)
    (htanQ₀ : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (Q₀.basis 0) (S.basis j)| ≤ Ctan * (θ : ℝ))
    (hΔ : ‖(Q.center -ᵥ Q₀.center : EuclideanSpace ℝ (Fin 3))‖ ≤ D)
    (hz0 : |inner ℝ (S.basis 0)
        ((Q.center -ᵥ Q₀.center : EuclideanSpace ℝ (Fin 3)) - r • Q₀.basis 2)|
      ≤ B * (θ : ℝ) * (b : ℝ))
    (hz1 : |inner ℝ (S.basis 1)
        ((Q.center -ᵥ Q₀.center : EuclideanSpace ℝ (Fin 3)) - r • Q₀.basis 2)| ≤ B * (b : ℝ))
    (hz2 : |inner ℝ (S.basis 2)
        ((Q.center -ᵥ Q₀.center : EuclideanSpace ℝ (Fin 3)) - r • Q₀.basis 2)| ≤ B * (b : ℝ)) :
    ∀ k : Fin 3,
      |inner ℝ (Q₀.basis k) (Q.center -ᵥ Q₀.center)|
        ≤ (D + 3 * B * (1 + 2 * Ctan)) * ((![θ * b, b, 1] k : ℝ≥0) : ℝ) := by
  let z : EuclideanSpace ℝ (Fin 3) := (Q.center -ᵥ Q₀.center) - r • Q₀.basis 2
  have hbRpos : 0 < (b : ℝ) := NNReal.coe_pos.mpr hb0
  have hbR0 : 0 ≤ (b : ℝ) := le_of_lt hbRpos
  have hθR0 : 0 ≤ (θ : ℝ) := NNReal.coe_nonneg θ
  have hθR1 : (θ : ℝ) ≤ 1 := by exact_mod_cast hθ1
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) hΔ
  have hzadd : (Q.center -ᵥ Q₀.center : EuclideanSpace ℝ (Fin 3))
      = z + r • Q₀.basis 2 := by
    dsimp [z]
    abel
  have hintern : ∀ k : Fin 3, k ≠ 2 →
      inner ℝ (Q₀.basis k) (Q.center -ᵥ Q₀.center) = inner ℝ (Q₀.basis k) z := by
    intro k hk
    rw [hzadd]
    rw [inner_add_right, real_inner_smul_right]
    rw [Q₀.basis.orthonormal.2 hk]
    ring
  intro k
  fin_cases k
  · -- k = 0, weight θ * b
    have hw0 : ((![θ * b, b, 1] 0 : ℝ≥0) : ℝ) = (θ : ℝ) * (b : ℝ) := by
      simp
    have hx0 : |inner ℝ (Q₀.basis 0) (S.basis 0)| ≤ 1 := by
      simpa [Q₀.basis.norm_eq_one 0, S.basis.norm_eq_one 0] using
        (abs_real_inner_le_norm (Q₀.basis 0) (S.basis 0))
    have hle := abs_inner_le_of_slab_profile S (Q₀.basis 0) z
      (c := Ctan * (θ : ℝ)) (A₀ := B * (θ : ℝ) * (b : ℝ)) (A₁ := B * (b : ℝ)) (A₂ := B * (b : ℝ))
      (mul_nonneg hCtan hθR0) hx0
      (htanQ₀ 1 (by decide : (1 : Fin 3) ≠ 0))
      (htanQ₀ 2 (by decide : (2 : Fin 3) ≠ 0))
      hz0 hz1 hz2 (mul_nonneg hB hbR0) (mul_nonneg hB hbR0)
    have hθb0 : 0 ≤ (θ : ℝ) * (b : ℝ) := mul_nonneg hθR0 hbR0
    have hBθb0 : 0 ≤ B * ((θ : ℝ) * (b : ℝ)) := mul_nonneg hB hθb0
    have hBCθb0 : 0 ≤ B * Ctan * (θ : ℝ) * (b : ℝ) := by
      positivity
    have hDθb0 : 0 ≤ D * ((θ : ℝ) * (b : ℝ)) := mul_nonneg hD0 hθb0
    calc
      |inner ℝ (Q₀.basis 0) (Q.center -ᵥ Q₀.center)| = |inner ℝ (Q₀.basis 0) z| := by
        rw [hintern 0 (by decide : (0 : Fin 3) ≠ 2)]
      _ ≤ B * (θ : ℝ) * (b : ℝ) + (B * (b : ℝ) + B * (b : ℝ)) * (Ctan * (θ : ℝ)) := hle
      _ ≤ (D + 3 * B * (1 + 2 * Ctan)) * ((![θ * b, b, 1] 0 : ℝ≥0) : ℝ) := by
        rw [hw0]
        nlinarith [hBθb0, hBCθb0, hDθb0]
  · -- k = 1, weight b
    have hw1 : ((![θ * b, b, 1] 1 : ℝ≥0) : ℝ) = (b : ℝ) := by
      simp
    have hcs : |inner ℝ (Q₀.basis 1) z| ≤ ‖Q₀.basis 1‖ * ‖z‖ :=
      abs_real_inner_le_norm (Q₀.basis 1) z
    have hz0' : |inner ℝ (S.basis 0) z| ≤ B * (θ : ℝ) * (b : ℝ) := by simpa [z] using hz0
    have hz1' : |inner ℝ (S.basis 1) z| ≤ B * (b : ℝ) := by simpa [z] using hz1
    have hz2' : |inner ℝ (S.basis 2) z| ≤ B * (b : ℝ) := by simpa [z] using hz2
    have hn : ‖z‖ ≤ B * (θ : ℝ) * (b : ℝ) + B * (b : ℝ) + B * (b : ℝ) := by
      have h := norm_le_sum_abs_inner_basis S.basis z
      nlinarith [hz0', hz1', hz2']
    have hBb0 : 0 ≤ B * (b : ℝ) := mul_nonneg hB hbR0
    have h1mθ : 0 ≤ 1 - (θ : ℝ) := sub_nonneg.mpr hθR1
    have hn3 : ‖z‖ ≤ 3 * B * (b : ℝ) := by
      nlinarith [hn, hBb0, h1mθ, hB, hbR0]
    have hBCb0 : 0 ≤ B * Ctan * (b : ℝ) := mul_nonneg (mul_nonneg hB hCtan) hbR0
    have hDb0 : 0 ≤ D * (b : ℝ) := mul_nonneg hD0 hbR0
    calc
      |inner ℝ (Q₀.basis 1) (Q.center -ᵥ Q₀.center)| = |inner ℝ (Q₀.basis 1) z| := by
        rw [hintern 1 (by decide : (1 : Fin 3) ≠ 2)]
      _ ≤ ‖Q₀.basis 1‖ * ‖z‖ := hcs
      _ ≤ ‖z‖ := by simp [Q₀.basis.norm_eq_one 1]
      _ ≤ 3 * B * (b : ℝ) := hn3
      _ ≤ (D + 3 * B * (1 + 2 * Ctan)) * ((![θ * b, b, 1] 1 : ℝ≥0) : ℝ) := by
        rw [hw1]
        nlinarith [hBCb0, hDb0]
  · -- k = 2, weight 1
    have hw2 : ((![θ * b, b, 1] 2 : ℝ≥0) : ℝ) = (1 : ℝ) := by
      simp
    have hcs : |inner ℝ (Q₀.basis 2) (Q.center -ᵥ Q₀.center)| ≤
        ‖Q₀.basis 2‖ * ‖(Q.center -ᵥ Q₀.center : EuclideanSpace ℝ (Fin 3))‖ :=
      abs_real_inner_le_norm (Q₀.basis 2) (Q.center -ᵥ Q₀.center)
    have hBC1 : 0 ≤ 3 * B * (1 + 2 * Ctan) := by
      nlinarith [mul_nonneg hB hCtan, hB]
    calc
      |inner ℝ (Q₀.basis 2) (Q.center -ᵥ Q₀.center)| ≤
          ‖Q₀.basis 2‖ * ‖(Q.center -ᵥ Q₀.center : EuclideanSpace ℝ (Fin 3))‖ := hcs
      _ ≤ ‖(Q.center -ᵥ Q₀.center : EuclideanSpace ℝ (Fin 3))‖ := by
        simp [Q₀.basis.norm_eq_one 2]
      _ ≤ D := hΔ
      _ ≤ (D + 3 * B * (1 + 2 * Ctan)) * ((![θ * b, b, 1] 2 : ℝ≥0) : ℝ) := by
        rw [hw2]
        nlinarith [hBC1, hD0]

end Plank

end
