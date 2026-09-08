import MyLeanRepo.Kakeya.Streamlined.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Quantitative inverse bounds for projective direction tensors

A unit direction `u : Point3` is represented without choosing an orientation
by the rank-one tensor with entries `u i * u j`.  This module proves that this
encoding has a linear quantitative inverse in dimension three: entrywise
tensor error at most `ε` gives projective direction error at most `18 * ε`.

The proof is elementary and deliberately independent of any tube hierarchy.
It first bounds the residual

`u - inner ℝ u v • v`

coordinatewise, then chooses the sign of `v` only inside the proof.  Thus the
public conclusion remains invariant under `v ↦ -v`.
-/

noncomputable section

namespace Kakeya.Streamlined

open scoped BigOperators

private lemma point3_inner_eq_sum (u v : Point3) :
    inner ℝ u v = ∑ j : Fin 3, u j * v j := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp
  ring

private lemma point3_norm_sq (x : Point3) :
    ‖x‖ ^ 2 = ∑ i : Fin 3, (x i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, point3_inner_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma abs_coord_le_one_of_norm_eq_one
    {u : Point3} (hu : ‖u‖ = 1) (i : Fin 3) :
    |u i| ≤ 1 := by
  have hcoord : |u i| ≤ ‖u‖ := by
    have hsq : (u i) ^ 2 ≤ ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum
        (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
    nlinarith [sq_abs (u i), abs_nonneg (u i), norm_nonneg u]
  simpa [hu] using hcoord

/--
Applying the rank-one tensor difference to its first unit direction gives the
orthogonal residual from the second direction.
-/
theorem directionTensorResidual_coordinate
    {u v : Point3} (hu : ‖u‖ = 1) (i : Fin 3) :
    (u - inner ℝ u v • v) i =
      ∑ j : Fin 3, (u i * u j - v i * v j) * u j := by
  have hsum_u : ∑ j : Fin 3, u j ^ 2 = 1 := by
    rw [← point3_norm_sq, hu]
    norm_num
  have hinner : inner ℝ u v = ∑ j : Fin 3, u j * v j :=
    point3_inner_eq_sum u v
  rw [hinner]
  calc
    u i - (∑ j : Fin 3, u j * v j) * v i
        = u i * (∑ j : Fin 3, u j ^ 2) -
            v i * (∑ j : Fin 3, u j * v j) := by
          rw [hsum_u]
          ring
    _ = ∑ j : Fin 3, (u i * u j - v i * v j) * u j := by
      simp only [Fin.sum_univ_three]
      ring

/--
An entrywise rank-one tensor bound controls every coordinate of the projection
residual.
-/
theorem directionTensorResidual_coordinate_abs_le
    {u v : Point3} {epsilon : ℝ}
    (hu : ‖u‖ = 1)
    (hentry :
      ∀ i j : Fin 3,
        |u i * u j - v i * v j| ≤ epsilon)
    (i : Fin 3) :
    |(u - inner ℝ u v • v) i| ≤ 3 * epsilon := by
  have hepsilon : 0 ≤ epsilon :=
    (abs_nonneg (u i * u 0 - v i * v 0)).trans (hentry i 0)
  rw [directionTensorResidual_coordinate hu, Fin.sum_univ_three]
  calc
    |(u i * u 0 - v i * v 0) * u 0 +
        (u i * u 1 - v i * v 1) * u 1 +
        (u i * u 2 - v i * v 2) * u 2|
        ≤ |(u i * u 0 - v i * v 0) * u 0| +
            |(u i * u 1 - v i * v 1) * u 1| +
            |(u i * u 2 - v i * v 2) * u 2| := by
          exact (abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)
    _ = |u i * u 0 - v i * v 0| * |u 0| +
          |u i * u 1 - v i * v 1| * |u 1| +
          |u i * u 2 - v i * v 2| * |u 2| := by
          simp only [abs_mul]
    _ ≤ epsilon * 1 + epsilon * 1 + epsilon * 1 := by
          exact add_le_add
            (add_le_add
              (mul_le_mul (hentry i 0)
                (abs_coord_le_one_of_norm_eq_one hu 0)
                (abs_nonneg _) hepsilon)
              (mul_le_mul (hentry i 1)
                (abs_coord_le_one_of_norm_eq_one hu 1)
                (abs_nonneg _) hepsilon))
            (mul_le_mul (hentry i 2)
              (abs_coord_le_one_of_norm_eq_one hu 2)
              (abs_nonneg _) hepsilon)
    _ = 3 * epsilon := by ring

/--
In dimension three, an entrywise rank-one tensor bound controls the norm of
the projection residual linearly.
-/
theorem directionTensorResidual_norm_le
    {u v : Point3} {epsilon : ℝ}
    (hu : ‖u‖ = 1)
    (hepsilon : 0 ≤ epsilon)
    (hentry :
      ∀ i j : Fin 3,
        |u i * u j - v i * v j| ≤ epsilon) :
    ‖u - inner ℝ u v • v‖ ≤ 9 * epsilon := by
  let residual : Point3 := u - inner ℝ u v • v
  have hcoord : ∀ i : Fin 3, |residual i| ≤ 3 * epsilon := by
    intro i
    exact directionTensorResidual_coordinate_abs_le hu hentry i
  have hsquare : ‖residual‖ ^ 2 =
      residual 0 ^ 2 + residual 1 ^ 2 + residual 2 ^ 2 := by
    rw [point3_norm_sq, Fin.sum_univ_three]
  have hthree : 0 ≤ 3 * epsilon :=
    mul_nonneg (by norm_num) hepsilon
  have h0 : residual 0 ^ 2 ≤ (3 * epsilon) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (residual 0)) hthree).2 (hcoord 0)
  have h1 : residual 1 ^ 2 ≤ (3 * epsilon) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (residual 1)) hthree).2 (hcoord 1)
  have h2 : residual 2 ^ 2 ≤ (3 * epsilon) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (residual 2)) hthree).2 (hcoord 2)
  have hresidual : 0 ≤ ‖residual‖ := norm_nonneg _
  have htarget : 0 ≤ 9 * epsilon := mul_nonneg (by norm_num) hepsilon
  dsimp only [residual] at hsquare ⊢
  nlinarith

private lemma unit_direction_sub_le_two_residual
    {u w : Point3} {a : ℝ}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖u - w‖ ≤ 2 * ‖u - a • w‖ := by
  have hscaled : ‖a • w - w‖ = 1 - a := by
    calc
      ‖a • w - w‖ = ‖(a - 1) • w‖ := by
        congr 1
        module
      _ = |a - 1| * ‖w‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = 1 - a := by
        rw [hw, mul_one, abs_of_nonpos (sub_nonpos.mpr ha1)]
        ring
  have hgap : 1 - a ≤ ‖u - a • w‖ := by
    have h := norm_sub_norm_le u (a • w)
    rw [hu, norm_smul, hw, mul_one, Real.norm_eq_abs,
      abs_of_nonneg ha0] at h
    exact h
  calc
    ‖u - w‖ ≤ ‖u - a • w‖ + ‖a • w - w‖ := by
      have h := norm_add_le (u - a • w) (a • w - w)
      simpa only [sub_add_sub_cancel] using h
    _ = ‖u - a • w‖ + (1 - a) := by rw [hscaled]
    _ ≤ ‖u - a • w‖ + ‖u - a • w‖ := add_le_add le_rfl hgap
    _ = 2 * ‖u - a • w‖ := by ring

/--
Orient one projective direction toward a reference direction.  This relative
choice is used only after the orientation-invariant tensor cell has been
selected; it is not a canonical hemisphere convention.
-/
def alignProjectiveDirection (reference candidate : Point3) : Point3 :=
  if 0 ≤ inner ℝ reference candidate then candidate else -candidate

/--
The relative orientation selected by `alignProjectiveDirection` is linearly
close whenever the orientation-invariant rank-one tensors are entrywise close.
-/
theorem alignProjectiveDirection_dist_le_of_rankOne_entrywise_le
    {u v : Point3} {epsilon : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hepsilon : 0 ≤ epsilon)
    (hentry :
      ∀ i j : Fin 3,
        |u i * u j - v i * v j| ≤ epsilon) :
    ‖u - alignProjectiveDirection u v‖ ≤ 18 * epsilon := by
  have hresidual :
      ‖u - inner ℝ u v • v‖ ≤ 9 * epsilon :=
    directionTensorResidual_norm_le hu hepsilon hentry
  have habsInner : |inner ℝ u v| ≤ 1 := by
    have h := abs_real_inner_le_norm u v
    simpa [hu, hv] using h
  by_cases hc : 0 ≤ inner ℝ u v
  · have hdirection :
        ‖u - v‖ ≤ 2 * ‖u - inner ℝ u v • v‖ :=
      unit_direction_sub_le_two_residual hu hv hc
        ((le_abs_self _).trans habsInner)
    rw [alignProjectiveDirection, if_pos hc]
    calc
      ‖u - v‖
      _ ≤ 2 * ‖u - inner ℝ u v • v‖ := hdirection
      _ ≤ 2 * (9 * epsilon) :=
        mul_le_mul_of_nonneg_left hresidual (by norm_num)
      _ = 18 * epsilon := by ring
  · have hcneg : inner ℝ u v < 0 := lt_of_not_ge hc
    have hnegUnit : ‖-v‖ = 1 := by simp [hv]
    have hdirection :
        ‖u - (-v)‖ ≤
          2 * ‖u - (-inner ℝ u v) • (-v)‖ :=
      unit_direction_sub_le_two_residual hu hnegUnit
        (by linarith)
        ((neg_le_abs _).trans habsInner)
    have hresidualNeg :
        ‖u - (-inner ℝ u v) • (-v)‖ =
          ‖u - inner ℝ u v • v‖ := by
      congr 1
      module
    rw [alignProjectiveDirection, if_neg hc]
    calc
      ‖u - -v‖
      _ ≤ 2 * ‖u - (-inner ℝ u v) • (-v)‖ := hdirection
      _ = 2 * ‖u - inner ℝ u v • v‖ := by rw [hresidualNeg]
      _ ≤ 2 * (9 * epsilon) :=
        mul_le_mul_of_nonneg_left hresidual (by norm_num)
      _ = 18 * epsilon := by ring

/--
The orientation-invariant rank-one encoding gives one of the two possible
oriented direction bounds.
-/
theorem direction_close_or_close_neg_of_rankOne_entrywise_le
    {u v : Point3} {epsilon : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hepsilon : 0 ≤ epsilon)
    (hentry :
      ∀ i j : Fin 3,
        |u i * u j - v i * v j| ≤ epsilon) :
    ‖u - v‖ ≤ 18 * epsilon ∨
      ‖u + v‖ ≤ 18 * epsilon := by
  have haligned :=
    alignProjectiveDirection_dist_le_of_rankOne_entrywise_le
      hu hv hepsilon hentry
  by_cases hc : 0 ≤ inner ℝ u v
  · left
    simpa [alignProjectiveDirection, hc] using haligned
  · right
    simpa [alignProjectiveDirection, hc, sub_neg_eq_add] using haligned

/--
The orientation-invariant rank-one encoding has a linear quantitative inverse
on unit directions in `Point3`.
-/
theorem projectiveDirection_dist_le_of_rankOne_entrywise_le
    {u v : Point3} {epsilon : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hepsilon : 0 ≤ epsilon)
    (hentry :
      ∀ i j : Fin 3,
        |u i * u j - v i * v j| ≤ epsilon) :
    min ‖u - v‖ ‖u + v‖ ≤ 18 * epsilon := by
  rcases direction_close_or_close_neg_of_rankOne_entrywise_le
      hu hv hepsilon hentry with hsame | hopposite
  · exact (min_le_left _ _).trans hsame
  · exact (min_le_right _ _).trans hopposite

end Kakeya.Streamlined
