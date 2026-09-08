/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# AffineSubspace
-/

@[expose] public section

variable
  {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A nonempty affine subspace of an inner product space over `ℝ` whose direction has dimension `1`
is isometric to `ℝ`, with any chosen base point sent to `0`. -/
theorem AffineSubspace.exists_isometryEquiv_real_of_direction_finrank_eq_one
    {L : AffineSubspace ℝ E} [Nonempty L]
    (h : Module.finrank ℝ L.direction = 1) (x : L) :
    ∃ f : ℝ ≃ᵢ ↥L, f 0 = x := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ L.direction)) ℝ L.direction :=
    stdOrthonormalBasis ℝ L.direction
  have hpos : 0 < Module.finrank ℝ ↥L.direction := by rw [h]; norm_num
  let v : ↥L.direction := b ⟨0, hpos⟩
  have hv : ‖v‖ = 1 := b.norm_eq_one _
  let φ : ℝ →ₗᵢ[ℝ] ↥L.direction := LinearIsometry.toSpanSingleton ℝ ↥L.direction hv
  let ψ : ℝ ≃ₗᵢ[ℝ] ↥L.direction :=
    φ.toLinearIsometryEquiv (by rw [Module.finrank_self, h])
  let g : ℝ ≃ᵃⁱ[ℝ] ↥L := ψ.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ x)
  refine ⟨g.toIsometryEquiv, ?_⟩
  change ψ.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ x) 0 = x
  simp [ψ, φ, LinearIsometry.toSpanSingleton, LinearMap.toSpanSingleton]

/-- **The slide map is a homothety** (blueprint `lem:slideMapIsHomothety`).

The affine map `z ↦ p + v + lam • (z - p)` has linear part `lam • id`, so for `lam ≠ 1` it is
the homothety of ratio `lam` centred at `p + (1 - lam)⁻¹ • v`.  Only `lam ≠ 1` is used, so that
the centre exists; the hypothesis is stated as `lam < 1`, which is the form in which the
consumers have it. -/
theorem eq_homothety_of_smul_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p v : F) {lam : ℝ} (hlam : lam < 1) :
    (fun z => p + v + lam • (z - p)) = ⇑(AffineMap.homothety (p + (1 - lam)⁻¹ • v) lam) := by
  funext z
  let c : F := (1 - lam)⁻¹ • v
  have hnon : 1 - lam ≠ 0 := by linarith
  have hsmul : (1 - lam) • c = v := by
    simpa [c] using (smul_inv_smul₀ hnon v)
  change p + v + lam • (z - p) = lam • (z - (p + c)) + (p + c)
  rw [← hsmul]
  rw [sub_smul, one_smul]
  module

/-- The affine isometry equivalence `z ↦ p' + R (z - p)` attached to a linear isometry
equivalence `R` and two base points `p`, `p'` (blueprint `lem:affineFromLinearIsometry`): the
composite of the translation by `-p`, of `R`, and of the translation by `p'`. -/
noncomputable def AffineIsometryEquiv.ofLinearIsometryEquiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (R : F ≃ₗᵢ[ℝ] F) (p p' : F) : F ≃ᵃⁱ[ℝ] F :=
  ((AffineIsometryEquiv.constVAdd ℝ F (-p)).trans R.toAffineIsometryEquiv).trans
    (AffineIsometryEquiv.constVAdd ℝ F p')

/-- **An affine isometry equivalence from a linear one and two base points** (blueprint
`lem:affineFromLinearIsometry`).  In particular `Φ p = p'` and `Φ (p + w) = p' + R w`, obtained
from this formula by `simp`. -/
theorem AffineIsometryEquiv.ofLinearIsometryEquiv_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (R : F ≃ₗᵢ[ℝ] F) (p p' z : F) :
    AffineIsometryEquiv.ofLinearIsometryEquiv R p p' z = p' + R (z - p) := by
  simp [AffineIsometryEquiv.ofLinearIsometryEquiv, add_comm, sub_eq_add_neg]
