/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard

open Matrix

/-- The determinant of the identity matrix with the `i`-th row replaced by `v` is `v i`. -/
lemma det_updateRow_one_row {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
    (i : n) (v : n → R) :
    ((1 : Matrix n n R).updateRow i v).det = v i := by
  let w : n → R := ∑ k : n, (v k) • (1 : Matrix n n R) k
  have h1 : w = v := by
    ext j
    simp [w, Matrix.one_apply, Finset.sum_apply, Pi.smul_apply]
  have h2 : ((1 : Matrix n n R).updateRow i w).det = (v i) • (1 : Matrix n n R).det :=
    Matrix.det_updateRow_sum (1 : Matrix n n R) i v
  rw [h1] at h2
  simpa [smul_eq_mul] using h2

end ForMathlib.Analysis.Calculus.Sard
