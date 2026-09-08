/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionN.Prism
public import Kakeya.Mathlib.Analysis.InnerProductSpace

/-!
# The planar angle between two planar prisms

For two planar prisms `Q`, `Q'` (terms of `PrismNDim 2 E E`, with orthonormal axes
`Q.basis`, `Q'.basis`) we define `PrismNDim.planarAngle Q Q'`, an orientation-free measure of how
transverse the two prisms are.  Geometrically it is `sin α` for `α` the angle between the two
frames.  It is defined as the absolute inner product `|⟪Q.basis 0, Q'.basis 1⟫|` between the first
axis of `Q` and the second axis of `Q'`, and the API records that this equals

* `|ω (Q.basis i) (Q'.basis i)|` for either `i` (the absolute signed area between the two long axes,
  or between the two short axes), for *any* orientation `o` with `ω = o.areaForm`
  (`planarAngle_eq_abs_areaForm`);
* `|⟪Q.basis i, Q'.basis i.rev⟫|` for either `i` (the absolute inner product between a long axis of
  one and the short axis of the other) (`planarAngle_eq_abs_inner`).

The point of `planarAngle` is to avoid choosing an orientation: `o.areaForm` flips sign under
`o ↦ -o`, but its absolute value, and hence `planarAngle`, does not depend on `o`.
-/

open Module

@[expose] public section

namespace PrismNDim

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

instance : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_two

/-- The **planar angle** between two planar prisms `Q`, `Q'`: an orientation-free measure of their
transversality (`sin` of the angle between their frames), defined as the absolute inner product
between the first axis of `Q` and the second axis of `Q'`. -/
noncomputable def planarAngle (Q Q' : PrismNDim 2 E E) : ℝ :=
  |inner ℝ (Q.basis 0) (Q'.basis 1)|

omit [Fact (finrank ℝ E = 2)] in
theorem planarAngle_def (Q Q' : PrismNDim 2 E E) :
    Q.planarAngle Q' = |inner ℝ (Q.basis 0) (Q'.basis 1)| := rfl

omit [Fact (finrank ℝ E = 2)] in
/-- The planar angle is nonnegative (it is an absolute value). -/
theorem planarAngle_nonneg (Q Q' : PrismNDim 2 E E) : 0 ≤ Q.planarAngle Q' :=
  abs_nonneg _

omit [Fact (finrank ℝ E = 2)] in
/-- The planar angle is at most `1`: it is the absolute inner product of two unit axes, so
Cauchy–Schwarz bounds it by the product of the norms, which is `1`. -/
theorem planarAngle_le_one (Q Q' : PrismNDim 2 E E) : Q.planarAngle Q' ≤ 1 :=
  (abs_real_inner_le_norm ..).trans_eq (by rw [Q.basis.norm_eq_one, Q'.basis.norm_eq_one, mul_one])

omit [Fact (finrank ℝ E = 2)] in
/-- The two cross inner products of the prism axes have equal absolute value:
`|⟪Q.basis 1, Q'.basis 0⟫| = |⟪Q.basis 0, Q'.basis 1⟫|`.  This is the orthogonality of the change
of basis between the two orthonormal frames, obtained from Parseval applied in both frames. -/
theorem abs_inner_basis_swap (Q Q' : PrismNDim 2 E E) :
    |inner ℝ (Q.basis 1) (Q'.basis 0)| = |inner ℝ (Q.basis 0) (Q'.basis 1)| := by
  have e1 := Q.basis.inner_sq_add_inner_sq (Q'.basis 1)
  have e2 := Q'.basis.inner_sq_add_inner_sq (Q.basis 1)
  simp only [OrthonormalBasis.norm_eq_one, real_inner_comm _ (Q'.basis 1)] at e1 e2
  exact (sq_eq_sq_iff_abs_eq_abs ..).mp (add_right_cancel (e2.trans e1.symm))

omit [Fact (finrank ℝ E = 2)] in
/-- `planarAngle Q Q'` equals the absolute inner product between the `i`-th axis of `Q` and the
*other* (`i.rev`-th) axis of `Q'`, for either `i`.  For `i = 0` this is the defining inner product;
for `i = 1` it is the symmetric one (`abs_inner_basis_swap`). -/
theorem planarAngle_eq_abs_inner (Q Q' : PrismNDim 2 E E) (i : Fin 2) :
    Q.planarAngle Q' = |inner ℝ (Q.basis i) (Q'.basis i.rev)| :=
  match i with
  | 0 => rfl
  | 1 => (Q.abs_inner_basis_swap Q').symm

/-- `planarAngle Q Q'` equals the absolute signed area `|o.areaForm (Q.basis i) (Q'.basis i)|`
between the two `i`-th axes, for either `i` and *any* orientation `o`.  (Taking `i = 0` gives the
two long axes, `i = 1` the two short axes, in the decreasing-thickness convention.) -/
theorem planarAngle_eq_abs_areaForm (o : Orientation ℝ E (Fin 2)) (Q Q' : PrismNDim 2 E E)
    (i : Fin 2) :
    Q.planarAngle Q' = |o.areaForm (Q.basis i) (Q'.basis i)| :=
  (Q.planarAngle_eq_abs_inner Q' i).trans (o.abs_areaForm_basis_eq_abs_inner ..).symm

end PrismNDim
