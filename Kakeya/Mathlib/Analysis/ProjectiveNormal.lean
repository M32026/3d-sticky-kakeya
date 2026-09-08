/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The projective distance between normals

A plane normal is only defined up to sign, so the natural distance between two normals is the
sign-blind chord `min ‖u - v‖ ‖u + v‖`.  This file collects its basic API: nonnegativity, the
identity `d² = 2 - 2|⟪u,v⟫|` for unit vectors, the triangle inequality, and the fact that flipping
one vector into the half-space of the other realises the minimum.

The same expression appears in `Kakeya.card_le_of_projective_separated_in_cap`
(`Kakeya.Mathlib.Analysis.ProjectivePacking`), where it is written out inline.
-/

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Projective distance** between two vectors: `min ‖u - v‖ ‖u + v‖`.  For unit vectors this is
the smaller chord to `v` or `-v`, hence sign-blind — the natural distance on plane normals, whose
sign is ambiguous. -/
noncomputable def projNormalDist (u v : E) : ℝ :=
  min ‖u - v‖ ‖u + v‖

omit [InnerProductSpace ℝ E] in
theorem projNormalDist_nonneg (u v : E) : 0 ≤ projNormalDist u v :=
  le_min (norm_nonneg _) (norm_nonneg _)

/-- For unit vectors the projective chord satisfies `d² = 2 - 2|⟪u,v⟫|`: the sign-blind minimum
picks whichever of `‖u ∓ v‖² = 2 ∓ 2⟪u,v⟫` is smaller. -/
lemma projNormalDist_sq (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    projNormalDist u v ^ 2 = 2 - 2 * |inner ℝ u v| := by
  have hsub : ‖u - v‖ ^ 2 = 2 - 2 * inner ℝ u v := by rw [norm_sub_sq_real, hu, hv]; ring
  have hadd : ‖u + v‖ ^ 2 = 2 + 2 * inner ℝ u v := by rw [norm_add_sq_real, hu, hv]; ring
  unfold projNormalDist
  rcases le_total (0 : ℝ) (inner ℝ u v) with h | h
  · rw [min_eq_left (le_of_sq_le_sq (by linarith) (norm_nonneg _)), abs_of_nonneg h]
    linarith
  · rw [min_eq_right (le_of_sq_le_sq (by linarith) (norm_nonneg _)), abs_of_nonpos h]
    linarith

omit [InnerProductSpace ℝ E] in
/-- **Projective triangle inequality.**  `projNormalDist` is a pseudometric: the four sign choices
each reduce to the ordinary triangle inequality. -/
theorem projNormalDist_triangle (u v w : E) :
    projNormalDist u w ≤ projNormalDist u v + projNormalDist v w := by
  have e1 : ‖u - w‖ ≤ ‖u - v‖ + ‖v - w‖ := by
    rw [show u - w = (u - v) + (v - w) from by abel]; exact norm_add_le _ _
  have e2 : ‖u + w‖ ≤ ‖u - v‖ + ‖v + w‖ := by
    rw [show u + w = (u - v) + (v + w) from by abel]; exact norm_add_le _ _
  have e3 : ‖u + w‖ ≤ ‖u + v‖ + ‖v - w‖ := by
    rw [show u + w = (u + v) - (v - w) from by abel]; exact norm_sub_le _ _
  have e4 : ‖u - w‖ ≤ ‖u + v‖ + ‖v + w‖ := by
    rw [show u - w = (u + v) - (v + w) from by abel]; exact norm_sub_le _ _
  unfold projNormalDist
  rcases le_total ‖u - v‖ ‖u + v‖ with hA | hA <;>
    rcases le_total ‖v - w‖ ‖v + w‖ with hB | hB
  · exact (min_le_left _ _).trans (by rw [min_eq_left hA, min_eq_left hB]; exact e1)
  · exact (min_le_right _ _).trans (by rw [min_eq_left hA, min_eq_right hB]; exact e2)
  · exact (min_le_right _ _).trans (by rw [min_eq_right hA, min_eq_left hB]; exact e3)
  · exact (min_le_left _ _).trans (by rw [min_eq_right hA, min_eq_right hB]; exact e4)

/-- **Oriented normal**: flip `u` (a plane normal, up to sign) so it points into the same
half-space as the reference `r` (`⟪u, r⟫ ≥ 0`). -/
noncomputable def orientedNormal (r u : E) : E :=
  if 0 ≤ inner ℝ u r then u else -u

/-- For unit vectors, the oriented normal realises the projective distance: the sign chosen by
`orientedNormal` is exactly the one minimising the chord to `r`. -/
theorem orientedNormal_sub_norm_eq_projNormalDist
    (r u : E) (hu : ‖u‖ = 1) (hr : ‖r‖ = 1) :
    ‖orientedNormal r u - r‖ = projNormalDist u r := by
  unfold orientedNormal projNormalDist
  have hsub : ‖u - r‖ ^ 2 = 2 - 2 * inner ℝ u r := by rw [norm_sub_sq_real, hu, hr]; ring
  have hadd : ‖u + r‖ ^ 2 = 2 + 2 * inner ℝ u r := by rw [norm_add_sq_real, hu, hr]; ring
  by_cases h : (0 : ℝ) ≤ inner ℝ u r
  · rw [if_pos h, min_eq_left (by nlinarith [norm_nonneg (u - r), norm_nonneg (u + r)])]
  · rw [if_neg h, min_eq_right (by
      nlinarith [norm_nonneg (u - r), norm_nonneg (u + r), lt_of_not_ge h]),
      show -u - r = -(u + r) from by abel, norm_neg]

/-- Projective distance is bounded by the chord obtained after orienting both vectors towards the
same reference direction.  The oriented chord is one of the two representatives in the defining
minimum. -/
theorem projNormalDist_le_norm_orientedNormal_sub (r u v : E) :
    projNormalDist u v ≤ ‖orientedNormal r u - orientedNormal r v‖ := by
  unfold projNormalDist orientedNormal
  by_cases hu : 0 ≤ inner ℝ u r
  · by_cases hv : 0 ≤ inner ℝ v r
    · rw [if_pos hu, if_pos hv]
      exact min_le_left _ _
    · rw [if_pos hu, if_neg hv, sub_neg_eq_add]
      exact min_le_right _ _
  · by_cases hv : 0 ≤ inner ℝ v r
    · rw [if_neg hu, if_pos hv, show -u - v = -(u + v) by abel, norm_neg]
      exact min_le_right _ _
    · rw [if_neg hu, if_neg hv, show -u - -v = -(u - v) by abel, norm_neg]
      exact min_le_left _ _

/-- Orienting two unit vectors into the half-space of a unit reference is bi-Lipschitz to their
orthogonal coordinates inside the projective half-cap of radius `1 / 2`.

The factor `2` comes from the unit-sphere graph: on this cap, the axial coordinate varies by at
most half the full chord, so the full chord is at most twice its orthogonal projection. -/
theorem norm_orientedNormal_sub_le_two_mul_norm_orthogonal_sub
    (r u v : E) (hr : ‖r‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hur : projNormalDist u r ≤ 1 / 2) (hvr : projNormalDist v r ≤ 1 / 2) :
    ‖orientedNormal r u - orientedNormal r v‖ ≤
      2 * ‖(orientedNormal r u - (inner ℝ r (orientedNormal r u) : ℝ) • r) -
        (orientedNormal r v - (inner ℝ r (orientedNormal r v) : ℝ) • r)‖ := by
  let u' := orientedNormal r u
  let v' := orientedNormal r v
  let pu := u' - (inner ℝ r u' : ℝ) • r
  let pv := v' - (inner ℝ r v' : ℝ) • r
  have hu'norm : ‖u'‖ = 1 := by
    dsimp [u', orientedNormal]
    split_ifs <;> simp [hu]
  have hv'norm : ‖v'‖ = 1 := by
    dsimp [v', orientedNormal]
    split_ifs <;> simp [hv]
  have hu'r : ‖u' - r‖ ≤ 1 / 2 := by
    rw [show ‖u' - r‖ = projNormalDist u r by
      exact orientedNormal_sub_norm_eq_projNormalDist r u hu hr]
    exact hur
  have hv'r : ‖v' - r‖ ≤ 1 / 2 := by
    rw [show ‖v' - r‖ = projNormalDist v r by
      exact orientedNormal_sub_norm_eq_projNormalDist r v hv hr]
    exact hvr
  have hinner_u : (inner ℝ r u' : ℝ) = 1 - ‖u' - r‖ ^ 2 / 2 := by
    have hsq := norm_sub_sq_real u' r
    rw [hu'norm, hr] at hsq
    rw [real_inner_comm] at hsq
    linarith
  have hinner_v : (inner ℝ r v' : ℝ) = 1 - ‖v' - r‖ ^ 2 / 2 := by
    have hsq := norm_sub_sq_real v' r
    rw [hv'norm, hr] at hsq
    rw [real_inner_comm] at hsq
    linarith
  have hnormdiff : |‖u' - r‖ - ‖v' - r‖| ≤ ‖u' - v'‖ := by
    calc
      |‖u' - r‖ - ‖v' - r‖| ≤ ‖(u' - r) - (v' - r)‖ := abs_norm_sub_norm_le _ _
      _ = ‖u' - v'‖ := by congr 1; abel
  have hsum : ‖u' - r‖ + ‖v' - r‖ ≤ 1 := by linarith
  have haxial : |(inner ℝ r u' : ℝ) - inner ℝ r v'| ≤ ‖u' - v'‖ / 2 := by
    rw [hinner_u, hinner_v]
    have hfactor : |‖v' - r‖ ^ 2 - ‖u' - r‖ ^ 2| =
        (‖u' - r‖ + ‖v' - r‖) * |‖u' - r‖ - ‖v' - r‖| := by
      rw [sq_sub_sq]
      rw [abs_mul, abs_sub_comm, abs_of_nonneg (by positivity)]
      ring
    rw [show (1 - ‖u' - r‖ ^ 2 / 2) - (1 - ‖v' - r‖ ^ 2 / 2) =
      (‖v' - r‖ ^ 2 - ‖u' - r‖ ^ 2) / 2 by ring, abs_div,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), hfactor]
    gcongr
    exact (mul_le_of_le_one_left (abs_nonneg _) hsum).trans hnormdiff
  have hdecomp : u' - v' = (pu - pv) +
      ((inner ℝ r u' : ℝ) - inner ℝ r v') • r := by
    dsimp [pu, pv]
    module
  have htri : ‖u' - v'‖ ≤ ‖pu - pv‖ + |(inner ℝ r u' : ℝ) - inner ℝ r v'| := by
    rw [hdecomp]
    calc
      ‖pu - pv + ((inner ℝ r u' : ℝ) - inner ℝ r v') • r‖ ≤
          ‖pu - pv‖ + ‖((inner ℝ r u' : ℝ) - inner ℝ r v') • r‖ := norm_add_le _ _
      _ = ‖pu - pv‖ + |(inner ℝ r u' : ℝ) - inner ℝ r v'| := by
        rw [norm_smul, Real.norm_eq_abs, hr, mul_one]
  dsimp [u', v', pu, pv] at htri haxial ⊢
  linarith

end
