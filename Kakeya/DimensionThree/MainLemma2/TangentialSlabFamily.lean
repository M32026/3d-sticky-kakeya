/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.TangentialSlabDegenerate

/-!
# The anisotropic change of variables of the tangential slab step (row G9)

Row G9 of the general `(a, b)` branch: the tangential slab package
`Kakeya.VeryNotSticky.SlabPackage` at a general pair of plank dimensions `(a, b)`, of which the
existing `Kakeya.VeryNotSticky.exists_slabPackage_degenerate_of_margin`
(`MainLemma2/TangentialSlabDegenerate.lean`) is the `a = b` instance.

GWZ (`gwz.txt` l.2352–2385) cover the ball `B` by a maximal family `𝕊` of essentially distinct
slabs of dimensions `(a/b) r₁ × r₁ × r₁`, sort the bodies of `𝕎''_B` into the subfamilies
`𝕎''_S` of equation (28), and, for a dense slab `S`, make "a linear change of variables that
converts `S` to `B₁` and converts `𝕎''_S` to a set `𝕋̃` of `ρ₂`-tubes in `B₁`". At `a = b` that
change of variables is the isotropic homothety `Kakeya.VeryNotSticky.plankRescale`; at general
`(a, b)` it must stretch by `b/(a r₁)` along the normal `n(S)` of the slab and by `1/r₁` in the
plane `n(S)^⊥`, since the slab is thin exactly in the direction `n(S)`.

This file builds that map and everything the package needs that does **not** depend on the slab
family being constructed:

* `Kakeya.VeryNotSticky.aniLin`, `Kakeya.VeryNotSticky.aniLinEquiv`,
  `Kakeya.VeryNotSticky.aniRescale` — the anisotropic change of variables, with its composition
  law, its norm identity, its two Lipschitz constants and its inverse;
* `Kakeya.VeryNotSticky.slabRescale` — the instance at `(α, β) = (1/r₁, b/(a r₁))` that GWZ's
  step uses, together with `Kakeya.VeryNotSticky.slabRescale_eq_plankRescale`, which says that at
  `a = b` it **is** `Kakeya.VeryNotSticky.degenerateRescale`, so the degenerate file's map is the
  degenerate value of this one and nothing is duplicated;
* `Kakeya.VeryNotSticky.generalSlab` — the slab of dimensions `∼ (r₁, r₁, (a/b) r₁)` carried
  *exactly* onto the unit ball by `slabRescale`, so that clause (A1) of
  `Kakeya.VeryNotSticky.IsAnisotropicSlabRescale` is an equality and not an estimate;
* clause (A1') from a margin hypothesis, in the same form as for
  the degenerate route, and clauses `Cμ`, `CΔ`, (A3) which are already `(a, b)`-free in the existing
  degenerate file and are re-exported here rather than re-proved.

## What is **not** here, and why — the two obstructions of row G9

**(i) Clause (A2) is four-sixths a theorem and two-sixths an obligation.** The transport of a
thickness profile under an *isotropic* map is an exact rescaling
(`Kakeya.VeryNotSticky.hasThicknesses_plankRescale_image` carries `C₀` to `C₀`), which is why the
degenerate file closes (A2) with no loss. Under `aniRescale` no thickness scales exactly: the
sharp unconditional brackets are `α τ_k(X) ≤ τ_k(L X) ≤ β τ_k(X)`
(`Kakeya.VeryNotSticky.thickness_aniRescale_image_mem`), with `α = 1/r₁` and `β = b/(a r₁)`.
Against (A2)'s six inequalities that settles four of them, and
`Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_two` proves exactly those four:
rank `0` upper (from clause (A1)), rank `0` lower, rank `1` lower, and rank `2` upper — the last
being the one place the anisotropy pays, `β · C₀ a = C₀ b/r₁ = C₀ ρ₂` exactly.

The two that remain are **rank `1` upper** and **rank `2` lower**. The rank-`2` lower gap is
arithmetic: the transport gives `τ₂(L X) ≥ a/(C₀ r₁)` and (A2) demands `ρ₂/C₀ = b/(C₀ r₁)`, and
`Kakeya.VeryNotSticky.aniLin_rank_two_gap` compiles the strict inequality between them at every
`a < b`; they coincide exactly at `a = b`. Both missing halves are paid by the same geometric
input — the body's thin direction must lie within `∼ a/b` of `n(S)` — quantified by
`Kakeya.VeryNotSticky.norm_aniLin_le_of_inner_le`. What `Kakeya.VeryNotSticky.IsDenseSlab`
supplies instead is `axisAngle (bd.Wb j) S ≤ 2θ`, and the only upper bound on `θ` in
`Kakeya.VeryNotSticky.TypicalAngleData` is `hθ1 : θ ≤ 1` — vacuous relative to `a/b` as soon as
`a < b`, and *exactly* the needed bound when `a = b`. So (A2) at general `(a, b)` needs either a
new upper bound on the typical angle or a re-cut of the clause at a constant `C(bd.C₀)` rather
than `bd.C₀`, in the way (A2') already reads at `2 bd.C₀`. It is therefore carried here as an
explicit hypothesis of `Kakeya.VeryNotSticky.exists_slabPackage_general`, in the byte-exact shape
of the field, and reported rather than forced.

**(ii) Clauses (S3) and (S4) of `Kakeya.VeryNotSticky.IsSlabFamily` constrained one another —
RULED and RE-CUT.** As originally written, (S4) asked that *distinct* slabs of
`𝕊` have `c(C₀) (a/b)`-separated normals, so `𝕊` contained no two distinct **parallel** slabs;
(S3) asks that every body of `𝕎''_B` be *contained* in its assigned slab. At `a = b` the one slab
is the ball itself and both are trivial; at `a < b` a slab is thin, so the bodies of one normal
direction that are spread across `B` need many slabs, all of which the old (S4) forced to be
mutually tilted. Against the source that is decisive: GWZ's family is "a maximal set of
essentially disjoint slabs `S ⊂ B`" (`gwz.txt` l.2337-2339), which contains `∼ b/a` **parallel
translates** per direction, so the old (S4) excluded GWZ's own family.

The separation in (S4) is required only of slabs whose
`C₀ a`-thickenings meet, which is the only situation GWZ use it in and the only situation the sole
consumer `Kakeya.VeryNotSticky.tangentialSlabFibreCount` reads it in. The compiled form of the old
collision is preserved here, with the guard added:
`Kakeya.VeryNotSticky.IsSlabFamily.eq_of_bodyNormal_eq_of_overlap` and
`Kakeya.VeryNotSticky.IsSlabFamily.subset_common_slab_of_bodyNormal_eq`. Under the re-cut the
guard is a genuine restriction and the family is no longer excluded by its own clauses; the
family itself is still not constructed here.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter
open scoped NNReal ENNReal RealInnerProductSpace

universe u

/-- Shorthand for the ambient space of the tangential case. -/
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

noncomputable section

/-! ### The anisotropic change of variables -/

/-- **The linear part of the anisotropic rescaling**: the self-map of `ℝ³` that multiplies the
component along the unit vector `n` by `β` and the component in `n^⊥` by `α`, written without a
choice of orthonormal frame as `v ↦ α v + (β - α) ⟪n, v⟫ n`.

At `α = β` it is the homothety `α • ·`, which is why the degenerate case of the tangential step
(`Kakeya.VeryNotSticky.degenerateRescale`) is the value of this construction at `a = b`; see
`Kakeya.VeryNotSticky.slabRescale_eq_plankRescale`. -/
def aniLin (n : E₃) (α β : ℝ) : E₃ →ₗ[ℝ] E₃ :=
  α • LinearMap.id + (β - α) • ((innerSL ℝ n).smulRight n : E₃ →L[ℝ] E₃).toLinearMap

theorem aniLin_apply (n : E₃) (α β : ℝ) (v : E₃) :
    aniLin n α β v = α • v + ((β - α) * ⟪n, v⟫) • n := by
  simp [aniLin, mul_smul]

/-- At `α = β` the map is the homothety of ratio `α`, with no reference to `n`. -/
theorem aniLin_self (n : E₃) (α : ℝ) (v : E₃) : aniLin n α α v = α • v := by
  rw [aniLin_apply]; simp

theorem aniLin_one (n : E₃) (v : E₃) : aniLin n 1 1 v = v := by
  rw [aniLin_self, one_smul]

/-- **The composition law**: two anisotropic maps about the same unit normal compose
coordinatewise. This is what makes clause (A1) an exact statement about the slab of
`Kakeya.VeryNotSticky.generalSlab`. -/
theorem aniLin_aniLin (n : E₃) (hn : ‖n‖ = 1) (α β α' β' : ℝ) (v : E₃) :
    aniLin n α β (aniLin n α' β' v) = aniLin n (α * α') (β * β') v := by
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  rw [aniLin_apply, aniLin_apply, aniLin_apply, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, hnn, smul_add, smul_smul, smul_smul, mul_smul, smul_smul,
    add_assoc, ← add_smul]
  have hcoef : α * ((β' - α') * ⟪n, v⟫) + (β - α) * (α' * ⟪n, v⟫ + (β' - α') * ⟪n, v⟫ * 1)
      = (β * β' - α * α') * ⟪n, v⟫ := by ring
  rw [hcoef]

/-- **The norm identity**: the anisotropic map scales the component along `n` by `β` and the
component in `n^⊥` by `α`, and the two are orthogonal. -/
theorem norm_sq_aniLin (n : E₃) (hn : ‖n‖ = 1) (α β : ℝ) (v : E₃) :
    ‖aniLin n α β v‖ ^ 2 = α ^ 2 * (‖v‖ ^ 2 - ⟪n, v⟫ ^ 2) + β ^ 2 * ⟪n, v⟫ ^ 2 := by
  rw [aniLin_apply, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm v n, hn]
  simp only [Real.norm_eq_abs, mul_one, mul_pow, sq_abs]
  ring

/-- The Cauchy–Schwarz bound that keeps the two summands of `norm_sq_aniLin` nonnegative. -/
theorem inner_sq_le_norm_sq (n : E₃) (hn : ‖n‖ = 1) (v : E₃) : ⟪n, v⟫ ^ 2 ≤ ‖v‖ ^ 2 := by
  have h := abs_real_inner_le_norm n v
  rw [hn, one_mul] at h
  calc ⟪n, v⟫ ^ 2 = |⟪n, v⟫| ^ 2 := (sq_abs _).symm
    _ ≤ ‖v‖ ^ 2 := by nlinarith [abs_nonneg (⟪n, v⟫), norm_nonneg v]

/-- **The Lipschitz bound**: `‖L v‖ ≤ max α β · ‖v‖`. The map is a diagonal dilation in the
orthogonal frame `(n^⊥, n)`, so its operator norm is the larger of the two ratios. -/
theorem norm_aniLin_le_max (n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (v : E₃) : ‖aniLin n α β v‖ ≤ max α β * ‖v‖ := by
  have hM : 0 ≤ max α β := le_max_of_le_left hα
  have hαM : α ^ 2 ≤ max α β ^ 2 := by nlinarith [le_max_left α β]
  have hβM : β ^ 2 ≤ max α β ^ 2 := by nlinarith [le_max_right α β]
  have hcs := inner_sq_le_norm_sq n hn v
  have hsq : ‖aniLin n α β v‖ ^ 2 ≤ (max α β * ‖v‖) ^ 2 := by
    rw [norm_sq_aniLin n hn, mul_pow]
    nlinarith [sq_nonneg (⟪n, v⟫), sub_nonneg.mpr hcs]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- **The lower Lipschitz bound**: `min α β · ‖v‖ ≤ ‖L v‖`. -/
theorem min_mul_le_norm_aniLin (n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (v : E₃) : min α β * ‖v‖ ≤ ‖aniLin n α β v‖ := by
  have hm : 0 ≤ min α β := le_min hα hβ
  have hαm : min α β ^ 2 ≤ α ^ 2 := by nlinarith [min_le_left α β]
  have hβm : min α β ^ 2 ≤ β ^ 2 := by nlinarith [min_le_right α β]
  have hcs := inner_sq_le_norm_sq n hn v
  have hsq : (min α β * ‖v‖) ^ 2 ≤ ‖aniLin n α β v‖ ^ 2 := by
    rw [norm_sq_aniLin n hn, mul_pow]
    nlinarith [sq_nonneg (⟪n, v⟫), sub_nonneg.mpr hcs]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp hsq

/-- `‖L v‖ ≤ β ‖v‖` in the ordered case `0 ≤ α ≤ β`. -/
theorem norm_aniLin_le (n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β)
    (v : E₃) : ‖aniLin n α β v‖ ≤ β * ‖v‖ := by
  have h := norm_aniLin_le_max n hn hα (hα.trans hαβ) v
  rwa [max_eq_right hαβ] at h

/-- `α ‖v‖ ≤ ‖L v‖` in the ordered case `0 ≤ α ≤ β`. -/
theorem le_norm_aniLin (n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β)
    (v : E₃) : α * ‖v‖ ≤ ‖aniLin n α β v‖ := by
  have h := min_mul_le_norm_aniLin n hn hα (hα.trans hαβ) v
  rwa [min_eq_left hαβ] at h

/-- **The alignment estimate.** The anisotropic map inflates only the part of a displacement
that lies along `n`: if the component of `v` along `n` is at most `s`, then
`‖L v‖ ≤ α ‖v‖ + β s`.

This is the quantitative form of the alignment obligation of row G9. Applied to the long edge of
a body of profile `(r₁, b, a)` inside a slab of normal `n`, at `α = 1/r₁` and `β = b/(a r₁)`, it
gives `‖L v‖ ≤ 1 + (b/(a r₁)) s`; the clause (A2) target for that edge is `∼ 1`, so the edge's
component along `n(S)` must be `s ≲ a r₁ / b`, i.e. the tilt must be `≲ a/b`. The only bound
`Kakeya.VeryNotSticky.IsDenseSlab` supplies is `axisAngle ≤ 2θ` with `θ ≤ 1`
(`Kakeya.VeryNotSticky.TypicalAngleData.hθ1`), which at `a < b` is weaker by the factor `b/a`. -/
theorem norm_aniLin_le_of_inner_le (n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (v : E₃) {s : ℝ} (hs : |⟪n, v⟫| ≤ s) : ‖aniLin n α β v‖ ≤ α * ‖v‖ + β * s := by
  have hs0 : 0 ≤ s := le_trans (abs_nonneg _) hs
  have hts : ⟪n, v⟫ ^ 2 ≤ s ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hs 2
  have hcs := inner_sq_le_norm_sq n hn v
  have hsq : ‖aniLin n α β v‖ ^ 2 ≤ (α * ‖v‖ + β * s) ^ 2 := by
    rw [norm_sq_aniLin n hn]
    nlinarith [norm_nonneg v, mul_nonneg (mul_nonneg hα hβ) (mul_nonneg (norm_nonneg v) hs0),
      sq_nonneg (⟪n, v⟫), sq_nonneg α, sq_nonneg β]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (by positivity) two_ne_zero).mp hsq

/-- **The anisotropic rescaling as a linear equivalence.** Its inverse is the anisotropic map
with the reciprocal ratios, by `Kakeya.VeryNotSticky.aniLin_aniLin`. -/
def aniLinEquiv (n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) : E₃ ≃ₗ[ℝ] E₃ :=
  LinearEquiv.ofLinear (aniLin n α β) (aniLin n α⁻¹ β⁻¹)
    (LinearMap.ext fun v => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
      rw [aniLin_aniLin n hn, mul_inv_cancel₀ hα, mul_inv_cancel₀ hβ, aniLin_one])
    (LinearMap.ext fun v => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
      rw [aniLin_aniLin n hn, inv_mul_cancel₀ hα, inv_mul_cancel₀ hβ, aniLin_one])

@[simp] theorem aniLinEquiv_apply (n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (v : E₃) : aniLinEquiv n hn hα hβ v = aniLin n α β v := rfl

@[simp] theorem aniLinEquiv_symm_apply (n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : α ≠ 0)
    (hβ : β ≠ 0) (v : E₃) : (aniLinEquiv n hn hα hβ).symm v = aniLin n α⁻¹ β⁻¹ v := rfl

/-- **The anisotropic change of variables about the centre `c` and the unit normal `n`**: GWZ's
"linear change of variables that converts `S` to `B₁`" (`gwz.txt` l.2378–2379) at general
`(a, b)`. It is `Kakeya.VeryNotSticky.plankRescale` when `α = β`. -/
def aniRescale (c n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) : E₃ ≃ᵃ[ℝ] E₃ :=
  (AffineEquiv.vaddConst ℝ c).symm.trans (aniLinEquiv n hn hα hβ).toAffineEquiv

theorem aniRescale_apply (c n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (x : E₃) :
    aniRescale c n hn hα hβ x = aniLin n α β (x - c) := by
  simp [aniRescale]

theorem aniRescale_symm_apply (c n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (z : E₃) : (aniRescale c n hn hα hβ).symm z = c + aniLin n α⁻¹ β⁻¹ z := by
  rw [eq_comm, ← AffineEquiv.apply_eq_iff_eq_symm_apply, aniRescale_apply, add_sub_cancel_left,
    aniLin_aniLin n hn, mul_inv_cancel₀ hα, mul_inv_cancel₀ hβ, aniLin_one]

/-! ### The change of variables of GWZ's tangential step, and its degenerate value -/

/-- **The change of variables attached to a slab** (`gwz.txt` l.2378–2379 at general `(a, b)`):
the affine map that stretches by `1/(θ r₁)` along the normal `n` of the slab and by `1/r₁` in
the plane `n^⊥`, where `θ = a/b` is the aspect ratio of the slab's profile
`(r₁, r₁, (a/b) r₁)`. At `a = b` the two ratios coincide and the map is the isotropic homothety
of `Kakeya.VeryNotSticky.plankRescale`; see
`Kakeya.VeryNotSticky.slabRescale_eq_plankRescale`. -/
def slabRescale (c n : E₃) (hn : ‖n‖ = 1) {r₁ ratio : ℝ} (hr₁ : 0 < r₁) (hratio : 0 < ratio) :
    E₃ ≃ᵃ[ℝ] E₃ :=
  aniRescale c n hn (inv_ne_zero hr₁.ne') (inv_ne_zero (mul_pos hratio hr₁).ne')

theorem slabRescale_apply (c n : E₃) (hn : ‖n‖ = 1) {r₁ ratio : ℝ} (hr₁ : 0 < r₁)
    (hratio : 0 < ratio) (x : E₃) :
    slabRescale c n hn hr₁ hratio x = aniLin n r₁⁻¹ (ratio * r₁)⁻¹ (x - c) :=
  aniRescale_apply _ _ _ _ _ _

/-- **The degenerate value of the general change of variables.** At `ratio = 1` — i.e. at
`a = b`, where GWZ's slab dimensions `(a/b) r₁ × r₁ × r₁` degenerate to the ball — the
anisotropic map *is* `Kakeya.VeryNotSticky.plankRescale`, hence is
`Kakeya.VeryNotSticky.degenerateRescale`. This is the sense in which the existing degenerate
package is the `a = b` instance of this row and nothing is duplicated. -/
theorem slabRescale_eq_plankRescale (c n : E₃) (hn : ‖n‖ = 1) {r₁ : ℝ} (hr₁ : 0 < r₁) (x : E₃) :
    slabRescale c n hn hr₁ (zero_lt_one' ℝ) x = plankRescale c hr₁.ne' x := by
  rw [slabRescale_apply, one_mul, aniLin_self, plankRescale_apply]

/-- The degenerate change of variables of `MainLemma2/TangentialSlabDegenerate.lean` is the
value of `Kakeya.VeryNotSticky.slabRescale` at aspect ratio `1`, for **every** unit normal `n`:
at `a = b` the map does not see the slab's direction. -/
theorem slabRescale_eq_degenerateRescale (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (B : bd.bι) (n : E₃) (hn : ‖n‖ = 1) (x : E₃) :
    slabRescale (bd.ctr B) n hn (r₁_pos cfg) (zero_lt_one' ℝ) x = degenerateRescale cfg B x :=
  slabRescale_eq_plankRescale _ _ _ _ _

/-! ### The slab carried exactly onto the unit ball -/

/-- **The slab of GWZ's family, in the shape the change of variables normalises exactly**: the
ellipsoid of centre `c`, semi-axes `r₁` in the plane `n^⊥` and `ratio · r₁` along `n`. It is the
preimage of the unit ball under `Kakeya.VeryNotSticky.slabRescale`, so clause (A1) of
`Kakeya.VeryNotSticky.IsAnisotropicSlabRescale` holds for it as an **equality**
(`Kakeya.VeryNotSticky.slabRescale_image_generalSlab`) rather than as an estimate. -/
def generalSlab (c n : E₃) (hn : ‖n‖ = 1) {r₁ ratio : ℝ} (hr₁ : 0 < r₁) (hratio : 0 < ratio) :
    ConvexSpaceBody E₃ :=
  (ConvexSpaceBody.closedBall (0 : E₃) 1 zero_le_one).mapAffine
    (slabRescale c n hn hr₁ hratio).symm

theorem generalSlab_carrier (c n : E₃) (hn : ‖n‖ = 1) {r₁ ratio : ℝ} (hr₁ : 0 < r₁)
    (hratio : 0 < ratio) :
    (generalSlab c n hn hr₁ hratio).carrier =
      (slabRescale c n hn hr₁ hratio).symm '' Metric.closedBall (0 : E₃) 1 := by
  rw [generalSlab, ConvexSpaceBody.mapAffine_carrier, ConvexSpaceBody.closedBall_carrier]

theorem mem_generalSlab_iff (c n : E₃) (hn : ‖n‖ = 1) {r₁ ratio : ℝ} (hr₁ : 0 < r₁)
    (hratio : 0 < ratio) (x : E₃) :
    x ∈ (generalSlab c n hn hr₁ hratio).carrier ↔ ‖aniLin n r₁⁻¹ (ratio * r₁)⁻¹ (x - c)‖ ≤ 1 := by
  rw [generalSlab_carrier]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← slabRescale_apply c n hn hr₁ hratio, AffineEquiv.apply_symm_apply]
    simpa using hz
  · intro hx
    refine ⟨slabRescale c n hn hr₁ hratio x, ?_, AffineEquiv.symm_apply_apply _ _⟩
    simpa [slabRescale_apply] using hx

/-- **Clause (A1), exactly**: the change of variables carries the slab *onto* the unit ball. -/
theorem slabRescale_image_generalSlab (c n : E₃) (hn : ‖n‖ = 1) {r₁ ratio : ℝ} (hr₁ : 0 < r₁)
    (hratio : 0 < ratio) :
    slabRescale c n hn hr₁ hratio '' (generalSlab c n hn hr₁ hratio).carrier =
      Metric.closedBall (0 : E₃) 1 := by
  rw [generalSlab_carrier, Set.image_image]
  simp only [AffineEquiv.apply_symm_apply]
  exact Set.image_id _

/-- The slab lies in the ball of radius `r₁` about its centre, when `ratio ≤ 1`. -/
theorem generalSlab_subset_closedBall (c n : E₃) (hn : ‖n‖ = 1) {r₁ ratio : ℝ} (hr₁ : 0 < r₁)
    (hratio : 0 < ratio) (hratio1 : ratio ≤ 1) :
    (generalSlab c n hn hr₁ hratio).carrier ⊆ Metric.closedBall c r₁ := by
  intro x hx
  rw [mem_generalSlab_iff] at hx
  have hpos : (0 : ℝ) < ratio * r₁ := mul_pos hratio hr₁
  have hle : r₁⁻¹ ≤ (ratio * r₁)⁻¹ :=
    (inv_le_inv₀ hr₁ hpos).2 (by nlinarith)
  have h := le_norm_aniLin n hn (le_of_lt (inv_pos.mpr hr₁)) hle (x - c)
  rw [mem_closedBall, dist_eq_norm]
  have h2 : r₁⁻¹ * ‖x - c‖ ≤ 1 := h.trans hx
  have := mul_le_mul_of_nonneg_left h2 hr₁.le
  rwa [← mul_assoc, mul_inv_cancel₀ hr₁.ne', one_mul, mul_one] at this

/-- The slab contains the ball of radius `ratio · r₁` about its centre. -/
theorem closedBall_subset_generalSlab (c n : E₃) (hn : ‖n‖ = 1) {r₁ ratio : ℝ} (hr₁ : 0 < r₁)
    (hratio : 0 < ratio) (hratio1 : ratio ≤ 1) :
    Metric.closedBall c (ratio * r₁) ⊆ (generalSlab c n hn hr₁ hratio).carrier := by
  intro x hx
  rw [mem_closedBall, dist_eq_norm] at hx
  rw [mem_generalSlab_iff]
  have hpos : (0 : ℝ) < ratio * r₁ := mul_pos hratio hr₁
  have hle : r₁⁻¹ ≤ (ratio * r₁)⁻¹ :=
    (inv_le_inv₀ hr₁ hpos).2 (by nlinarith)
  have h := norm_aniLin_le n hn (le_of_lt (inv_pos.mpr hr₁)) hle (x - c)
  calc ‖aniLin n r₁⁻¹ (ratio * r₁)⁻¹ (x - c)‖ ≤ (ratio * r₁)⁻¹ * ‖x - c‖ := h
    _ ≤ (ratio * r₁)⁻¹ * (ratio * r₁) := by
        exact mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr hpos))
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-! ### The two-sided thickness profile of the slab — clause (S2) -/

/-- **A contained disc forces the rank-`1` thickness, with no loss at all.**

If `X` contains the disc of radius `R` about `c` in the plane `n^⊥`, then `X` is not within `R`
of any line. This is the tool clause (S2) of `Kakeya.VeryNotSticky.IsSlabFamily` needs, and it
**replaces the volume route**:  item 4 asked for the determinant of a
rank-one update (`LinearMap.det (id + c • (n ⊗ n))`) so that
`Kakeya.volume_le_prod_thickness` could be run backwards; Mathlib has no such lemma (`loogle`
on `LinearMap.det (LinearMap.id + _)`, `Matrix.det_one_add_col_mul_row`,
`LinearMap.det_one_add_smulRight`: all empty). This is sharper anyway — the volume route returns
the rank-`1` bound at `π/6 ≈ 0.52` of the truth, this one at `1`.

**The proof is two points and a parallelogram.** Given `X ⊆ N_r(A)` with `A` of rank ≤ 1, pick a
unit `u` orthogonal to *both* `n` and `A.direction` (available since
`dim(ℝ∙n ⊔ A.direction) ≤ 2 < 3`). The two disc points `c ± R u` lie in `X`, so each is within
`r + ε` of some `y± ∈ A`; and `⟪c - y₊, u⟫ = ⟪c - y₋, u⟫` because `y₊ - y₋ ∈ A.direction ⊥ u`, so
the two squared distances sum to `‖c-y₊‖² + ‖c-y₋‖² + 2R² ≥ 2R²`. Hence `2(r+ε)² ≥ 2R²`. -/
theorem le_thickness_one_of_disc {X : Set E₃} {c n : E₃} (hn : ‖n‖ = 1) {R : ℝ} (hR : 0 ≤ R)
    (hXb : Bornology.IsBounded X)
    (hD : ∀ w : E₃, ⟪n, w⟫ = 0 → ‖w‖ = R → c + w ∈ X) :
    R ≤ Metric.thickness ℝ X 1 := by
  rcases eq_or_lt_of_le hR with h0 | hRpos
  · rw [← h0]; exact Metric.thickness_nonneg _ _
  have hn0 : n ≠ 0 := by intro h; rw [h] at hn; simp at hn
  refine le_csInf ?_ ?_
  · obtain ⟨r₀, hr₀pos, hsub⟩ := hXb.subset_closedBall_lt 0 c
    refine ⟨r₀, hr₀pos.le, affineSpan ℝ {c}, ?_, ?_⟩
    · rw [direction_affineSpan, vectorSpan_singleton]; simp
    · exact hsub.trans (Metric.closedBall_subset_cthickening (by simp) r₀)
  · rintro r ⟨hr0, A, hArank, hsub⟩
    -- a unit vector orthogonal to `n` and to `A.direction`
    have hfr1 : Module.finrank ℝ A.direction ≤ 1 := by
      have h1 : (Module.finrank ℝ A.direction : Cardinal) ≤ (1 : Cardinal) := by
        rw [Module.finrank_eq_rank]; exact hArank
      exact_mod_cast h1
    have hsp : Module.finrank ℝ ((ℝ ∙ n) ⊔ A.direction : Submodule ℝ E₃) ≤ 2 := by
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq (ℝ ∙ n) A.direction
      have hone : Module.finrank ℝ (ℝ ∙ n : Submodule ℝ E₃) = 1 := finrank_span_singleton hn0
      omega
    have hrk : Module.rank ℝ (AffineSubspace.mk' c ((ℝ ∙ n) ⊔ A.direction)).direction
        ≤ (2 : ℕ) := by
      rw [AffineSubspace.direction_mk', ← Module.finrank_eq_rank]
      exact_mod_cast hsp
    obtain ⟨u, hu_mem, hu_norm⟩ := Metric.exists_unit_orthogonal_of_rank_lt
      (AffineSubspace.mk' c ((ℝ ∙ n) ⊔ A.direction)) hrk
      (by rw [finrank_euclideanSpace_fin]; norm_num)
    rw [AffineSubspace.direction_mk'] at hu_mem
    have hun : ⟪n, u⟫ = (0 : ℝ) :=
      hu_mem n ((le_sup_left : (ℝ ∙ n) ≤ (ℝ ∙ n) ⊔ A.direction)
        (Submodule.mem_span_singleton_self n))
    have huA : ∀ v ∈ A.direction, ⟪v, u⟫ = (0 : ℝ) := fun v hv =>
      hu_mem v ((le_sup_right : A.direction ≤ (ℝ ∙ n) ⊔ A.direction) hv)
    -- the two disc points
    have hxp : c + R • u ∈ X := hD (R • u) (by rw [real_inner_smul_right, hun, mul_zero])
      (by rw [norm_smul, hu_norm, mul_one, Real.norm_eq_abs, abs_of_pos hRpos])
    have hxm : c + (-R) • u ∈ X := hD ((-R) • u) (by rw [real_inner_smul_right, hun, mul_zero])
      (by rw [norm_smul, hu_norm, mul_one, Real.norm_eq_abs, abs_of_neg (by linarith), neg_neg])
    have hAne : (A : Set E₃).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have := hsub hxp
      rw [hemp, Metric.cthickening_empty] at this
      exact this
    -- near-optimal points
    have hnear : ∀ x ∈ X, ∀ ε : ℝ, 0 < ε → ∃ y ∈ (A : Set E₃), dist x y < r + ε := by
      intro x hx ε hε
      have h1 : Metric.infEDist x (A : Set E₃) ≤ ENNReal.ofReal r :=
        Metric.mem_cthickening_iff.mp (hsub hx)
      have h2 : Metric.infEDist x (A : Set E₃) < ENNReal.ofReal (r + ε) :=
        lt_of_le_of_lt h1 (ENNReal.ofReal_lt_ofReal_iff (by linarith)|>.mpr (by linarith))
      obtain ⟨y, hy, hdy⟩ := Metric.infEDist_lt_iff.mp h2
      exact ⟨y, hy, by rwa [edist_lt_ofReal] at hdy⟩
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨yp, hyp, hdp⟩ := hnear _ hxp ε hε
    obtain ⟨ym, hym, hdm⟩ := hnear _ hxm ε hε
    have hkap : ⟪c - yp, u⟫ = ⟪c - ym, u⟫ := by
      have hdir : ym - yp ∈ A.direction := by
        have := AffineSubspace.vsub_mem_direction hym hyp
        simpa [vsub_eq_sub] using this
      have := huA _ hdir
      have hsplit : ⟪c - yp, u⟫ - ⟪c - ym, u⟫ = ⟪ym - yp, u⟫ := by
        rw [← inner_sub_left]; congr 1; abel
      linarith [hsplit ▸ this]
    have hep : dist (c + R • u) yp ^ 2 = ‖c - yp‖ ^ 2 + 2 * (R * ⟪c - yp, u⟫) + R ^ 2 := by
      rw [dist_eq_norm, show c + R • u - yp = (c - yp) + R • u by abel, norm_add_sq_real,
        real_inner_smul_right, norm_smul, hu_norm, mul_one, Real.norm_eq_abs,
        abs_of_pos hRpos]
    have hem : dist (c + (-R) • u) ym ^ 2 = ‖c - ym‖ ^ 2 - 2 * (R * ⟪c - ym, u⟫) + R ^ 2 := by
      rw [dist_eq_norm, show c + (-R) • u - ym = (c - ym) - R • u by
        rw [neg_smul]; abel, norm_sub_sq_real, real_inner_smul_right, norm_smul, hu_norm,
        mul_one, Real.norm_eq_abs, abs_of_pos hRpos]
    nlinarith [dist_nonneg (x := c + R • u) (y := yp), dist_nonneg (x := c + (-R) • u) (y := ym),
      sq_nonneg (‖c - yp‖), sq_nonneg (‖c - ym‖), norm_nonneg (c - yp), norm_nonneg (c - ym)]


/-- the `n`-component of a point of the slab is at most `ratio * r₁` -/
theorem abs_inner_le_of_mem_generalSlab (c n : E₃) (hn : ‖n‖ = 1) {r₁ ratio : ℝ} (hr₁ : 0 < r₁)
    (hratio : 0 < ratio) {x : E₃} (hx : x ∈ (generalSlab c n hn hr₁ hratio).carrier) :
    |⟪n, x - c⟫| ≤ ratio * r₁ := by
  rw [mem_generalSlab_iff] at hx
  have hpos : (0 : ℝ) < ratio * r₁ := mul_pos hratio hr₁
  have hsq := norm_sq_aniLin n hn r₁⁻¹ (ratio * r₁)⁻¹ (x - c)
  have hle : ‖aniLin n r₁⁻¹ (ratio * r₁)⁻¹ (x - c)‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (aniLin n r₁⁻¹ (ratio * r₁)⁻¹ (x - c))]
  have hcs := inner_sq_le_norm_sq n hn (x - c)
  have hα : (0 : ℝ) < r₁⁻¹ := inv_pos.mpr hr₁
  have hβ : (0 : ℝ) < (ratio * r₁)⁻¹ := inv_pos.mpr hpos
  have hkey : ((ratio * r₁)⁻¹) ^ 2 * ⟪n, x - c⟫ ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (r₁⁻¹), sub_nonneg.mpr hcs]
  have h2 : ⟪n, x - c⟫ ^ 2 ≤ (ratio * r₁) ^ 2 := by
    have : ((ratio * r₁)⁻¹) ^ 2 = ((ratio * r₁) ^ 2)⁻¹ := by rw [← inv_pow]
    rw [this] at hkey
    have hp2 : (0 : ℝ) < (ratio * r₁) ^ 2 := by positivity
    calc ⟪n, x - c⟫ ^ 2 = ((ratio * r₁) ^ 2) * (((ratio * r₁) ^ 2)⁻¹ * ⟪n, x - c⟫ ^ 2) := by
          field_simp
      _ ≤ ((ratio * r₁) ^ 2) * 1 := by exact mul_le_mul_of_nonneg_left hkey hp2.le
      _ = (ratio * r₁) ^ 2 := mul_one _
  calc |⟪n, x - c⟫| = Real.sqrt (⟪n, x - c⟫ ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((ratio * r₁) ^ 2) := Real.sqrt_le_sqrt h2
    _ = ratio * r₁ := by rw [Real.sqrt_sq hpos.le]

/-- the equatorial disc of radius `r₁` is inside the slab -/
theorem disc_subset_generalSlab (c n : E₃) (hn : ‖n‖ = 1) {r₁ ratio : ℝ} (hr₁ : 0 < r₁)
    (hratio : 0 < ratio) {w : E₃} (hw : ⟪n, w⟫ = (0 : ℝ)) (hnw : ‖w‖ = r₁) :
    c + w ∈ (generalSlab c n hn hr₁ hratio).carrier := by
  rw [mem_generalSlab_iff, show c + w - c = w by abel]
  have hsq := norm_sq_aniLin n hn r₁⁻¹ (ratio * r₁)⁻¹ w
  rw [hw, hnw] at hsq
  have : ‖aniLin n r₁⁻¹ (ratio * r₁)⁻¹ w‖ ^ 2 = 1 := by
    rw [hsq]; field_simp; ring
  nlinarith [norm_nonneg (aniLin n r₁⁻¹ (ratio * r₁)⁻¹ w)]


theorem thickness_two_generalSlab_le (c n : E₃) (hn : ‖n‖ = 1) {r₁ ratio : ℝ} (hr₁ : 0 < r₁)
    (hratio : 0 < ratio) :
    Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 2 ≤ ratio * r₁ := by
  have hn0 : n ≠ 0 := by intro h; rw [h] at hn; simp at hn
  have hrk : Module.rank ℝ (AffineSubspace.mk' c ((ℝ ∙ n)ᗮ)).direction ≤ (2 : ℕ) := by
    rw [AffineSubspace.direction_mk', ← Module.finrank_eq_rank]
    have hsum := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (ℝ ∙ n)
    have hone : Module.finrank ℝ (ℝ ∙ n : Submodule ℝ E₃) = 1 := finrank_span_singleton hn0
    have h3 : Module.finrank ℝ E₃ = 3 := finrank_euclideanSpace_fin
    rw [hone, h3] at hsum
    exact_mod_cast (by omega : Module.finrank ℝ ((ℝ ∙ n)ᗮ : Submodule ℝ E₃) ≤ 2)
  refine Metric.thickness_le_of_cthickening (by positivity) hrk ?_
  intro x hx
  refine Metric.mem_cthickening_of_dist_le x (x - ⟪n, x - c⟫ • n) _ _ ?_ ?_
  · rw [AffineSubspace.mem_coe, AffineSubspace.mem_mk',
      Submodule.mem_orthogonal_singleton_iff_inner_right]
    rw [vsub_eq_sub, show x - ⟪n, x - c⟫ • n - c = (x - c) - ⟪n, x - c⟫ • n by abel,
      inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hn]
    ring
  · rw [dist_eq_norm, show x - (x - ⟪n, x - c⟫ • n) = ⟪n, x - c⟫ • n by abel, norm_smul, hn,
      mul_one, Real.norm_eq_abs]
    exact abs_inner_le_of_mem_generalSlab c n hn hr₁ hratio hx

theorem hasThicknesses_generalSlab (c n : E₃) (hn : ‖n‖ = 1) {r₁ ratio : ℝ} (hr₁ : 0 < r₁)
    (hratio : 0 < ratio) (hratio1 : ratio ≤ 1) {C : NNReal} (hC : 1 ≤ C) :
    Kakeya.HasThicknesses (generalSlab c n hn hr₁ hratio).carrier C ![r₁, r₁, ratio * r₁] := by
  have hbdd : Bornology.IsBounded (generalSlab c n hn hr₁ hratio).carrier :=
    (generalSlab c n hn hr₁ hratio).isCompact'.isBounded
  have hC' : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hCpos : (0 : ℝ) < (C : ℝ) := lt_of_lt_of_le one_pos hC'
  have hCinv : ((C : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC'
  have h1l : r₁ ≤ Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 1 :=
    le_thickness_one_of_disc hn hr₁.le hbdd
      (fun w hw hnw => disc_subset_generalSlab c n hn hr₁ hratio hw hnw)
  have h10 : Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 1 ≤
      Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 0 :=
    Metric.thickness_antitone hbdd (by norm_num)
  have h0u : Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 0 ≤ r₁ := by
    exact Metric.thickness_le_of_subset_closedBall (x := c)
      (generalSlab_subset_closedBall c n hn hr₁ hratio hratio1) hr₁.le 0
  have h1u : Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 1 ≤ r₁ := h10.trans h0u
  have h0l : r₁ ≤ Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 0 := h1l.trans h10
  have h2u : Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 2 ≤ ratio * r₁ :=
    thickness_two_generalSlab_le c n hn hr₁ hratio
  have h2l : ratio * r₁ ≤ Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 2 := by
    have hm : Metric.thickness ℝ (Metric.closedBall c (ratio * r₁)) 2 ≤
        Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 2 :=
      Metric.thickness_monotone hbdd
        (closedBall_subset_generalSlab c n hn hr₁ hratio hratio1) 2
    exact le_trans (Metric.thickness_closedBall_ge (by positivity)
      (by rw [finrank_euclideanSpace_fin]; norm_num)) hm
  have hr₁0 : (0 : ℝ) ≤ r₁ := hr₁.le
  have hrr : (0 : ℝ) ≤ ratio * r₁ := by positivity
  have hA0l : ((C : ℝ))⁻¹ * r₁ ≤
      Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 0 := by nlinarith
  have hA0u : Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 0 ≤
      (C : ℝ) * r₁ := by nlinarith
  have hA1l : ((C : ℝ))⁻¹ * r₁ ≤
      Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 1 := by nlinarith
  have hA1u : Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 1 ≤
      (C : ℝ) * r₁ := by nlinarith
  have hA2l : ((C : ℝ))⁻¹ * (ratio * r₁) ≤
      Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 2 := by nlinarith
  have hA2u : Metric.thickness ℝ (generalSlab c n hn hr₁ hratio).carrier 2 ≤
      (C : ℝ) * (ratio * r₁) := by nlinarith
  intro k
  fin_cases k
  · exact ⟨hA0l, hA0u⟩
  · exact ⟨hA1l, hA1u⟩
  · exact ⟨hA2l, hA2u⟩

/-! ### Clauses (A1) and (A1') from a containment in the slab -/

/-- **Clauses (A1) and (A1') in one line.** Anything inside the slab is carried into the unit
ball; (A1) is this at `X = S`, and (A1') is this at `X = N_{τ₂(W)}(W)`, which is exactly the
margin hypothesis in conjunct 1 for the degenerate route.
The general branch inherits the same obligation in the same shape, with the ball `B̄(ctr B, r₁)`
of the degenerate file replaced by the slab. -/
theorem slabRescale_image_subset_closedBall (c n : E₃) (hn : ‖n‖ = 1) {r₁ ratio : ℝ}
    (hr₁ : 0 < r₁) (hratio : 0 < ratio) {X : Set E₃}
    (hX : X ⊆ (generalSlab c n hn hr₁ hratio).carrier) :
    slabRescale c n hn hr₁ hratio '' X ⊆ Metric.closedBall (0 : E₃) 1 := by
  rw [← slabRescale_image_generalSlab c n hn hr₁ hratio]
  exact Set.image_mono hX

/-! ### The sharp unconditional thickness comparison, and the (A2) gap -/

/-- The displacement formula for the rescaling. -/
theorem aniRescale_dist (c n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (y z : E₃) :
    dist (aniRescale c n hn hα hβ y) (aniRescale c n hn hα hβ z) = ‖aniLin n α β (y - z)‖ := by
  rw [dist_eq_norm, aniRescale_apply, aniRescale_apply, ← map_sub,
    show y - c - (z - c) = y - z by abel]

/-- The linear part of the rescaling, as an affine map — the form
`Kakeya.LipschitzWith.ethickness_image_le` consumes. -/
def aniAffMap (n : E₃) (α β : ℝ) : E₃ →ᵃ[ℝ] E₃ := (aniLin n α β).toAffineMap

@[simp] theorem aniAffMap_apply (n : E₃) (α β : ℝ) (v : E₃) :
    aniAffMap n α β v = aniLin n α β v := rfl

/-- The anisotropic linear map is `max α β`-Lipschitz. -/
theorem lipschitzWith_aniAffMap (n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    LipschitzWith (Real.toNNReal (max α β)) (aniAffMap n α β : E₃ → E₃) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [dist_eq_norm, aniAffMap_apply, aniAffMap_apply, ← map_sub, dist_eq_norm,
    Real.coe_toNNReal _ (le_max_of_le_left hα)]
  exact norm_aniLin_le_max n hn hα hβ _

/-- **The upper half of the transport**: `τ_k(L X) ≤ max α β · τ_k(X)`. -/
theorem ethickness_aniLin_image_le (n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (X : Set E₃) (k : ℕ) :
    Metric.ethickness ℝ (aniLin n α β '' X) k
      ≤ ENNReal.ofReal (max α β) * Metric.ethickness ℝ X k := by
  have h := (LipschitzWith.ethickness_image_le (f := aniAffMap n α β)
    (C := Real.toNNReal (max α β)) (lipschitzWith_aniAffMap n hn hα hβ) X) k
  simpa [aniAffMap, Pi.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.ofReal] using h

/-- **The lower half of the transport**: `α τ_k(X) ≤ τ_k(L X)`.

This is the *only* unconditional lower bound the anisotropic map admits, and it is where clause
(A2) of `Kakeya.VeryNotSticky.IsAnisotropicSlabRescale` fails at general `(a, b)`: applied to a
body of profile `(r₁, b, a)` at `α = 1/r₁` it returns `τ₂(L W) ≥ a/(C₀ r₁)`, whereas (A2) demands
`τ₂(L W) ≥ ρ₂/C₀ = b/(C₀ r₁)`. The two agree exactly when `a = b`, which is why the degenerate
file closes (A2) with the *isotropic*
`Kakeya.VeryNotSticky.hasThicknesses_plankRescale_image` and this file cannot. -/
theorem ethickness_aniLin_image_ge (n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (X : Set E₃) (k : ℕ) :
    ENNReal.ofReal α * Metric.ethickness ℝ X k ≤ Metric.ethickness ℝ (aniLin n α β '' X) k := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hinv : β⁻¹ ≤ α⁻¹ := (inv_le_inv₀ hβ hα).2 hαβ
  have hcomp : ∀ v : E₃, aniLin n α⁻¹ β⁻¹ (aniLin n α β v) = v := fun v => by
    rw [aniLin_aniLin n hn, inv_mul_cancel₀ hα.ne', inv_mul_cancel₀ hβ.ne', aniLin_one]
  have himg : aniLin n α⁻¹ β⁻¹ '' (aniLin n α β '' X) = X := by
    rw [Set.image_image]
    simp only [hcomp]
    exact Set.image_id _
  have h := ethickness_aniLin_image_le n hn (inv_pos.mpr hα).le (inv_pos.mpr hβ).le
    (aniLin n α β '' X) k
  rw [himg, max_eq_left hinv] at h
  calc ENNReal.ofReal α * Metric.ethickness ℝ X k
      ≤ ENNReal.ofReal α * (ENNReal.ofReal α⁻¹ * Metric.ethickness ℝ (aniLin n α β '' X) k) := by
        gcongr
    _ = ENNReal.ofReal (α * α⁻¹) * Metric.ethickness ℝ (aniLin n α β '' X) k := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hα.le]
    _ = Metric.ethickness ℝ (aniLin n α β '' X) k := by
        rw [mul_inv_cancel₀ hα.ne', ENNReal.ofReal_one, one_mul]

/-- The real-valued two-sided form, for a bounded set: `α τ_k(X) ≤ τ_k(L X) ≤ β τ_k(X)`. -/
theorem thickness_aniLin_image_mem (n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    {X : Set E₃} (hX : Bornology.IsBounded X) (k : ℕ) :
    α * Metric.thickness ℝ X k ≤ Metric.thickness ℝ (aniLin n α β '' X) k ∧
      Metric.thickness ℝ (aniLin n α β '' X) k ≤ β * Metric.thickness ℝ X k := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have himg : Bornology.IsBounded (aniLin n α β '' X) :=
    LipschitzWith.isBounded_image (lipschitzWith_aniAffMap n hn hα.le hβ.le) hX
  rw [← Metric.toReal_ethickness hX k, ← Metric.toReal_ethickness himg k]
  constructor
  · calc α * (Metric.ethickness ℝ X k).toReal
        = (ENNReal.ofReal α * Metric.ethickness ℝ X k).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hα.le]
      _ ≤ (Metric.ethickness ℝ (aniLin n α β '' X) k).toReal :=
          ENNReal.toReal_mono (Metric.ethickness_ne_top himg k)
            (ethickness_aniLin_image_ge n hn hα hαβ X k)
  · calc (Metric.ethickness ℝ (aniLin n α β '' X) k).toReal
        ≤ (ENNReal.ofReal β * Metric.ethickness ℝ X k).toReal := by
          have hup := ethickness_aniLin_image_le n hn hα.le hβ.le X k
          rw [max_eq_right hαβ] at hup
          refine ENNReal.toReal_mono ?_ hup
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Metric.ethickness_ne_top hX k)
      _ = β * (Metric.ethickness ℝ X k).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hβ.le]


/-! ### The affine transport, and the four unconditional halves of clause (A2) -/

/-- Translation, as a function. -/
theorem coe_constVAdd (v : E₃) :
    ((AffineEquiv.constVAdd ℝ E₃ v).toAffineMap : E₃ → E₃) = fun x => v + x := rfl

/-- Translation is a `1`-Lipschitz affine self-map of `ℝ³`. -/
theorem lipschitzWith_constVAdd (v : E₃) :
    LipschitzWith 1 ((AffineEquiv.constVAdd ℝ E₃ v).toAffineMap : E₃ → E₃) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [coe_constVAdd, NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm,
    show v + y - (v + z) = y - z by abel]

/-- **`ethickness` is translation invariant.** -/
theorem ethickness_constVAdd_image (v : E₃) (X : Set E₃) (k : ℕ) :
    Metric.ethickness ℝ ((fun x => v + x) '' X) k = Metric.ethickness ℝ X k := by
  have key : ∀ (w : E₃) (Y : Set E₃),
      Metric.ethickness ℝ ((fun x => w + x) '' Y) k ≤ Metric.ethickness ℝ Y k := by
    intro w Y
    have h := (LipschitzWith.ethickness_image_le
      (f := (AffineEquiv.constVAdd ℝ E₃ w).toAffineMap) (C := 1)
      (lipschitzWith_constVAdd w) Y) k
    rw [coe_constVAdd] at h
    simpa [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] using h
  refine le_antisymm (key v X) ?_
  have hback : (fun x : E₃ => -v + x) '' ((fun x : E₃ => v + x) '' X) = X := by
    rw [Set.image_image]
    simp
  calc Metric.ethickness ℝ X k
      = Metric.ethickness ℝ ((fun x : E₃ => -v + x) '' ((fun x : E₃ => v + x) '' X)) k := by
        rw [hback]
    _ ≤ Metric.ethickness ℝ ((fun x : E₃ => v + x) '' X) k := key _ _

/-- Translation preserves boundedness. -/
theorem isBounded_constVAdd_image (v : E₃) {X : Set E₃} (hX : Bornology.IsBounded X) :
    Bornology.IsBounded ((fun x : E₃ => v + x) '' X) := by
  have h := LipschitzWith.isBounded_image (lipschitzWith_constVAdd v) hX
  rwa [coe_constVAdd] at h

/-- The affine rescaling's image is the linear map's image of the translated set. -/
theorem aniRescale_image_eq (c n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (X : Set E₃) :
    aniRescale c n hn hα hβ '' X = aniLin n α β '' ((fun x => -c + x) '' X) := by
  rw [Set.image_image]
  refine Set.image_congr (fun x _ => ?_)
  rw [aniRescale_apply]
  congr 1
  abel

/-- **The affine two-sided transport.** The same brackets as
`Kakeya.VeryNotSticky.thickness_aniLin_image_mem`, transported to the affine map that the
package's field `L` carries. -/
theorem thickness_aniRescale_image_mem (c n : E₃) (hn : ‖n‖ = 1) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) {X : Set E₃} (hX : Bornology.IsBounded X) (k : ℕ) :
    α * Metric.thickness ℝ X k
        ≤ Metric.thickness ℝ (aniRescale c n hn hα.ne' (lt_of_lt_of_le hα hαβ).ne' '' X) k ∧
      Metric.thickness ℝ (aniRescale c n hn hα.ne' (lt_of_lt_of_le hα hαβ).ne' '' X) k
        ≤ β * Metric.thickness ℝ X k := by
  have hXt : Bornology.IsBounded ((fun x : E₃ => -c + x) '' X) := isBounded_constVAdd_image _ hX
  have hth : Metric.thickness ℝ ((fun x : E₃ => -c + x) '' X) k = Metric.thickness ℝ X k := by
    rw [← Metric.toReal_ethickness hXt k, ← Metric.toReal_ethickness hX k,
      ethickness_constVAdd_image]
  have h := thickness_aniLin_image_mem n hn hα hαβ hXt k
  rw [hth] at h
  rwa [aniRescale_image_eq c n hn hα.ne' (lt_of_lt_of_le hα hαβ).ne' X]

/-- **Four of the six inequalities of clause (A2), unconditionally.**

For a body `X` of profile `(r₁, b, a)` at comparison constant `C₀`, contained in the slab that
`Kakeya.VeryNotSticky.slabRescale` normalises, the change of variables gives without any further
hypothesis:

* rank `0`, upper: `τ₀(L X) ≤ 1 ≤ C₀ · 1`, because `L X ⊆ B₁` (clause (A1));
* rank `0`, lower: `C₀⁻¹ · 1 ≤ τ₀(L X)`, from `τ₀(X) ≥ r₁/C₀` and `α = 1/r₁`;
* rank `1`, lower: `C₀⁻¹ ρ₂ ≤ τ₁(L X)`, from `τ₁(X) ≥ b/C₀` and `α = 1/r₁`;
* rank `2`, upper: `τ₂(L X) ≤ C₀ ρ₂`, from `τ₂(X) ≤ C₀ a` and `β = b/(a r₁)` — this is the one
  place the anisotropy *helps*, `β · a = b/r₁ = ρ₂` exactly.

The two that remain — rank `1` upper and rank `2` lower — are the hypotheses `h1` and `h2`, and
they are exactly the two that need the body's thin direction to be aligned with the slab's normal
to within `∼ a/b`; `Kakeya.VeryNotSticky.IsDenseSlab` bounds that angle only by `2θ`, and `θ ≤ 1`
is the only upper bound `Kakeya.VeryNotSticky.TypicalAngleData` carries. -/
theorem hasThicknesses_slabRescale_image_of_two (c n : E₃) (hn : ‖n‖ = 1)
    {r₁ ratio a b : ℝ} {C₀ : NNReal} (hr₁ : 0 < r₁) (hratio : 0 < ratio) (hratio1 : ratio ≤ 1)
    (hb : 0 < b) (hrb : ratio * b = a) (hC₀ : 1 ≤ C₀)
    {X : Set E₃} (hXbdd : Bornology.IsBounded X) (hX : HasThicknesses X C₀ ![r₁, b, a])
    (hsub : X ⊆ (generalSlab c n hn hr₁ hratio).carrier)
    (h1 : Metric.thickness ℝ (slabRescale c n hn hr₁ hratio '' X) 1 ≤ (C₀ : ℝ) * (b / r₁))
    (h2 : ((C₀ : ℝ))⁻¹ * (b / r₁) ≤ Metric.thickness ℝ (slabRescale c n hn hr₁ hratio '' X) 2) :
    HasThicknesses (slabRescale c n hn hr₁ hratio '' X) C₀ ![1, b / r₁, b / r₁] := by
  have hpos : (0 : ℝ) < ratio * r₁ := mul_pos hratio hr₁
  have hαpos : (0 : ℝ) < r₁⁻¹ := inv_pos.mpr hr₁
  have hαβ : r₁⁻¹ ≤ (ratio * r₁)⁻¹ := (inv_le_inv₀ hr₁ hpos).2 (by nlinarith)
  have hC₀' : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  have hC₀pos : (0 : ℝ) < (C₀ : ℝ) := lt_of_lt_of_le zero_lt_one hC₀'
  have hbr : (ratio * r₁)⁻¹ * a = b / r₁ := by
    rw [← hrb]; field_simp
  have hX0 := (hX 0).1
  have hX1 := (hX 1).1
  have hX2 := (hX 2).2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hX0 hX1 hX2
  have h0l : ((C₀ : ℝ))⁻¹ * 1 ≤ Metric.thickness ℝ (slabRescale c n hn hr₁ hratio '' X) 0 := by
    have hlow := (thickness_aniRescale_image_mem c n hn hαpos hαβ hXbdd 0).1
    calc ((C₀ : ℝ))⁻¹ * 1 = r₁⁻¹ * (((C₀ : ℝ))⁻¹ * r₁) := by field_simp
      _ ≤ r₁⁻¹ * Metric.thickness ℝ X 0 := mul_le_mul_of_nonneg_left hX0 hαpos.le
      _ ≤ _ := hlow
  have h0u : Metric.thickness ℝ (slabRescale c n hn hr₁ hratio '' X) 0 ≤ (C₀ : ℝ) * 1 := by
    have hball := slabRescale_image_subset_closedBall c n hn hr₁ hratio hsub
    rw [mul_one]
    exact (Metric.thickness_le_of_subset_closedBall hball zero_le_one 0).trans hC₀'
  have h1l : ((C₀ : ℝ))⁻¹ * (b / r₁)
      ≤ Metric.thickness ℝ (slabRescale c n hn hr₁ hratio '' X) 1 := by
    have hlow := (thickness_aniRescale_image_mem c n hn hαpos hαβ hXbdd 1).1
    calc ((C₀ : ℝ))⁻¹ * (b / r₁) = r₁⁻¹ * (((C₀ : ℝ))⁻¹ * b) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ r₁⁻¹ * Metric.thickness ℝ X 1 := mul_le_mul_of_nonneg_left hX1 hαpos.le
      _ ≤ _ := hlow
  have h2u : Metric.thickness ℝ (slabRescale c n hn hr₁ hratio '' X) 2 ≤ (C₀ : ℝ) * (b / r₁) := by
    have hup := (thickness_aniRescale_image_mem c n hn hαpos hαβ hXbdd 2).2
    calc Metric.thickness ℝ (slabRescale c n hn hr₁ hratio '' X) 2
        ≤ (ratio * r₁)⁻¹ * Metric.thickness ℝ X 2 := hup
      _ ≤ (ratio * r₁)⁻¹ * ((C₀ : ℝ) * a) := mul_le_mul_of_nonneg_left hX2 (inv_pos.mpr hpos).le
      _ = (C₀ : ℝ) * ((ratio * r₁)⁻¹ * a) := by ring
      _ = (C₀ : ℝ) * (b / r₁) := by rw [hbr]
  intro k
  fin_cases k
  · exact ⟨h0l, h0u⟩
  · exact ⟨h1l, h1⟩
  · exact ⟨h2, h2u⟩

/-! ### Clauses (A1) and (A1′) produced, for a family of normalising slabs -/

/-- **(A1) and (A1′), produced.** For a slab that *is* the normalising ellipsoid of
`Kakeya.VeryNotSticky.generalSlab`, both clauses of `Kakeya.VeryNotSticky.IsAnisotropicSlabRescale`
that speak about the unit ball are theorems, the first outright and the second modulo the margin
— the same margin as in conjunct 1 for the degenerate route,
here read against the slab rather than against the ball.

This is what discharges the binders `hA1`, `hA1'` of
`Kakeya.VeryNotSticky.exists_slabPackage_general` once a family of such slabs exists: neither is
an obligation of the general branch, they were binders only because `𝕊` was. -/
theorem slabRescale_A1_and_A1' (cfg : VeryNotSticky.{u}) {bd : BallData cfg} (c n : E₃)
    (hn : ‖n‖ = 1) {r₁ ratio : ℝ} (hr₁ : 0 < r₁) (hratio : 0 < ratio) {Wd : Finset bd.ω}
    (hmargin : ∀ j ∈ Wd, ((bd.Wb j).cthickening (bd.Wb j).scale).carrier ⊆
      (generalSlab c n hn hr₁ hratio).carrier) :
    slabRescale c n hn hr₁ hratio '' (generalSlab c n hn hr₁ hratio).carrier ⊆
        Metric.closedBall (0 : E₃) 1 ∧
      ∀ j ∈ Wd, slabRescale c n hn hr₁ hratio ''
        ((bd.Wb j).cthickening (bd.Wb j).scale).carrier ⊆ Metric.closedBall (0 : E₃) 1 :=
  ⟨(slabRescale_image_generalSlab c n hn hr₁ hratio).le,
    fun j hj => slabRescale_image_subset_closedBall c n hn hr₁ hratio (hmargin j hj)⟩

/-- **Clause (S2), produced.** The normalising ellipsoid has *exactly* the profile
`(r₁, r₁, (a/b) r₁)` that clause (S2) of `Kakeya.VeryNotSticky.IsSlabFamily` asks for, at every
comparison constant `C ≥ 1` — in particular at `bd.C₀`, with no loss and no side condition beyond
`(a/b) ≤ 1`. Both halves of (S2) are theorems for it:
`Kakeya.VeryNotSticky.generalSlab_subset_closedBall` is the ball half at the slab's own centre,
and this is the profile half. -/
theorem hasThicknesses_generalSlab_C₀ (cfg : VeryNotSticky.{u}) {bd : BallData cfg} (c n : E₃)
    (hn : ‖n‖ = 1) {r₁ ratio : ℝ} (hr₁ : 0 < r₁) (hratio : 0 < ratio) (hratio1 : ratio ≤ 1) :
    HasThicknesses (generalSlab c n hn hr₁ hratio).carrier bd.C₀ ![r₁, r₁, ratio * r₁] :=
  hasThicknesses_generalSlab c n hn hr₁ hratio hratio1 bd.hC₀

/-! ### The output theorem: the slab package at general `(a, b)` -/

/-- **`exists_slabPackage_general` — the tangential slab package at a general `(a, b)`.**

Row G9's output. The three constants and clause (A3) are supplied here from the existing
degenerate file, where they are already free of `a` and `b`:

* `Cμ := degenerateCμ bd.C₀ ta.Ctyp` is the least admissible value of
  `Kakeya.VeryNotSticky.IsSlabDecompMultConstant`, a function of `bd.C₀` and `ta.Ctyp` only;
* `CΔ := degenerateCΔ bd.C₀ bd.Cbias = 2^10 C₀³ Cbias` is the `δ`-free
  constant;
* clause (A3) is `Kakeya.VeryNotSticky.isKatzTao_affineImage_of_antiClustering`, which holds for **every** affine equivalence `L`, hence for the anisotropic one.

What is *not* supplied is the slab family and the two thickness clauses (A2), (A2'): they are the
binders `hfam`, `hA2`, `hA2'`, stated in the byte-exact texts of the fields of
`Kakeya.VeryNotSticky.IsSlabFamily` and `Kakeya.VeryNotSticky.IsAnisotropicSlabRescale`. See the
module docstring for why each is an obligation and not a gap in this proof. -/
theorem exists_slabPackage_general (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {τ' : ℝ} {B : bd.bι} {hB : B ∈ bd.bs}
    (ta : TypicalAngleData cfg tc hB τ')
    (hCμ : ((degenerateCμ bd.C₀ ta.Ctyp : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-τ'))
    (hCΔ : ((degenerateCΔ (latticeRescaleConstant bd.C₀) bd.Cbias : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)))
    (𝕊 : Set (ConvexSpaceBody E₃)) (slabOf : bd.ω → ConvexSpaceBody E₃)
    (hfam : IsSlabFamily cfg B ta.sel ta.θ 𝕊 slabOf)
    (L : ConvexSpaceBody E₃ → (E₃ ≃ᵃ[ℝ] E₃))
    (hA1 : ∀ (S : ConvexSpaceBody E₃) (Wd : Finset bd.ω), IsDenseSlab cfg ta 𝕊 S Wd →
      ∀ j ∈ Wd, L S '' (bd.Wb j).carrier ⊆ Metric.closedBall 0 1)
    (hA1' : ∀ (S : ConvexSpaceBody E₃) (Wd : Finset bd.ω), IsDenseSlab cfg ta 𝕊 S Wd →
      ∀ j ∈ Wd, L S '' ((bd.Wb j).cthickening (bd.Wb j).scale).carrier ⊆ Metric.closedBall 0 1)
    (hA2 : ∀ (S : ConvexSpaceBody E₃) (Wd : Finset bd.ω), IsDenseSlab cfg ta 𝕊 S Wd →
      ∀ j ∈ Wd, HasThicknesses (L S '' (bd.Wb j).carrier) (latticeRescaleConstant bd.C₀)
        ![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)])
    (hA2' : ∀ (S : ConvexSpaceBody E₃) (Wd : Finset bd.ω), IsDenseSlab cfg ta 𝕊 S Wd →
      ∀ j ∈ Wd, HasThicknesses (L S '' ((bd.Wb j).cthickening (bd.Wb j).scale).carrier)
        (2 * (latticeRescaleConstant bd.C₀)) ![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)]) :
    Nonempty (SlabPackage cfg ta) :=
  ⟨{ 𝕊 := 𝕊
     slabOf := slabOf
     isSlabFamily := hfam
     Cμ := degenerateCμ bd.C₀ ta.Ctyp
     CμAdmissible := isSlabDecompMultConstant_degenerateCμ _ _
     Cμ_le := hCμ
     L := L
     CΔ := degenerateCΔ (latticeRescaleConstant bd.C₀) bd.Cbias
     CΔAdmissible := isSlabDeltamaxConstant_degenerateCΔ
       (one_le_latticeRescaleConstant bd.hC₀) bd.hCbias
     CΔ_le := hCΔ
     rescale := fun S Wd hslab =>
       { A1 := hA1 S Wd hslab
         A1' := hA1' S Wd hslab
         A2 := hA2 S Wd hslab
         A2' := hA2' S Wd hslab
         A3 := isKatzTao_affineImage_of_antiClustering cfg tc hB ta hslab.subset (L S)
           (Cbias_le_degenerateCΔ bd.Cbias
             (one_le_latticeRescaleConstant bd.hC₀)) } }⟩

/-! ### The existing degenerate package is the `a = b` instance -/

/-- **The degenerate package, re-derived from the general theorem.** Every hypothesis of
`Kakeya.VeryNotSticky.exists_slabPackage_general` is discharged at `a = b = δ` from the existing
degenerate file: `hfam` by `Kakeya.VeryNotSticky.isSlabFamily_degenerate`, `hA1`/`hA1'` by
`Kakeya.VeryNotSticky.degenerateRescale_image_subset_ball` (the second one through the margin),
and `hA2`/`hA2'` by `Kakeya.VeryNotSticky.hasThicknesses_degenerateRescale_body` and
`Kakeya.VeryNotSticky.hasThicknesses_degenerateRescale_cthickening`.

The conclusion is byte-identical to that of the existing
`Kakeya.VeryNotSticky.exists_slabPackage_degenerate_of_margin`, so this is a tripwire: it fails
to elaborate if the general theorem's binders stop covering the degenerate route. Together with
`Kakeya.VeryNotSticky.slabRescale_eq_degenerateRescale` — the change of variables of the general
row *is* the degenerate one at `a = b` — this is the sense in which the existing degenerate package
is the `a = b` instance of row G9. -/
theorem exists_slabPackage_degenerate_of_margin_of_general (cfg : VeryNotSticky.{u})
    {bd : BallData cfg} (tc : ThinConfig cfg bd) (ha : cfg.a = cfg.δ) (hb : cfg.b = cfg.δ)
    {τ' : ℝ}
    (hCμ : ∀ Ctyp : NNReal, Ctyp ≤ (cfg.δ ^ (1 - cfg.exscal)) ^ (-(cfg.η / 256)) →
      ((degenerateCμ bd.C₀ Ctyp : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-τ'))
    (hCΔ : ((degenerateCΔ (latticeRescaleConstant bd.C₀) bd.Cbias : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)))
    {B : bd.bι} (hB : B ∈ bd.bs)
    (hmargin : ∀ j ∈ bd.bodies B,
      Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
        Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ))
    (ta : TypicalAngleData cfg tc hB τ') :
    Nonempty (SlabPackage cfg ta) := by
  have hab : cfg.a = cfg.b := ha.trans hb.symm
  have hjB : ∀ (Wd : Finset bd.ω), Wd ⊆ ta.sel → ∀ j ∈ Wd, j ∈ bd.bodies B := by
    intro Wd hWd j hj
    exact (tc.thinBall hB).bodies'_subset (ta.hsel (hWd hj))
  have hCal : bd.C₀ ≤ latticeRescaleConstant bd.C₀ :=
    le_latticeRescaleConstant bd.hC₀
  have hC₀pos : (0 : NNReal) < bd.C₀ := lt_of_lt_of_le zero_lt_one bd.hC₀
  have htk : ∀ k : Fin 3, (0 : ℝ) ≤ (![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)]) k := by
    intro k
    fin_cases k <;> simp
  refine exists_slabPackage_general cfg ta (hCμ ta.Ctyp ta.hCtyp) hCΔ
    {degenerateSlab cfg B} (fun _ => degenerateSlab cfg B)
    (isSlabFamily_degenerate cfg tc hB ta hab) (fun _ => degenerateRescale cfg B)
    (fun S Wd hslab j hj => degenerateRescale_image_subset_ball cfg B
      (bd.bodies_subset_ball B hB j (hjB Wd hslab.subset j hj)))
    (fun S Wd hslab j hj => ?_) (fun S Wd hslab j hj => ?_) (fun S Wd hslab j hj => ?_)
  · rw [ConvexSpaceBody.cthickening_carrier]
    exact degenerateRescale_image_subset_ball cfg B (hmargin j (hjB Wd hslab.subset j hj))
  · exact hasThicknesses_mono_const hC₀pos hCal htk
      (hasThicknesses_degenerateRescale_body cfg hB (hjB Wd hslab.subset j hj) ha hb)
  · exact hasThicknesses_mono_const (by positivity) (by gcongr) htk
      (hasThicknesses_degenerateRescale_cthickening cfg hB (hjB Wd hslab.subset j hj) ha hb)

/-! ### The two obstructions, compiled -/

/-- **Obstruction (ii), first half, under the guard of the re-cut (S4′).** Two slabs of `𝕊`
whose `C₀ a`-thickenings meet and whose normals agree are equal, because (S4′) separates their
normals by `c(C₀) (a/b) > 0`.

Without the overlap guard, the separation would force at most one slab
per normal direction and collided with (S3)'s containment demand; the guard is exactly what the
re-cut adds, and the collision is gone. What survives is the true and useful statement: a family
cannot contain two distinct parallel slabs *that overlap*. -/
theorem IsSlabFamily.eq_of_bodyNormal_eq_of_overlap {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    {B : bd.bι} {Wb' : Finset bd.ω} {θ : NNReal} {𝕊 : Set (ConvexSpaceBody E₃)}
    {slabOf : bd.ω → ConvexSpaceBody E₃} (_hS : IsSlabFamily cfg B Wb' θ 𝕊 slabOf)
    {S S' : ConvexSpaceBody E₃} (hS1 : S ∈ 𝕊) (hS2 : S' ∈ 𝕊)
    (hov : (Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∩
      Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S'.carrier).Nonempty)
    (hsep : 𝕊.Pairwise fun S S' ↦
      (Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∩
          Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S'.carrier).Nonempty →
        (slabAxisSeparationConstant bd.C₀ : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ) ≤ axisAngle S S')
    (h : bodyNormal S = bodyNormal S') : S = S' := by
  by_contra hne
  have h4 : (slabAxisSeparationConstant bd.C₀ : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ)
      ≤ axisAngle S S' := hsep hS1 hS2 hne hov
  have hzero : axisAngle S S' = 0 := by
    rw [axisAngle_eq_lineAngle, h, NonSlab.lineAngle_self (bodyNormal_ne_zero S')]
  have hb0 : (0 : NNReal) < cfg.b := lt_of_lt_of_le cfg.hδ (cfg.hdims.1.trans cfg.hdims.2.1)
  have ha0 : (0 : NNReal) < cfg.a := lt_of_lt_of_le cfg.hδ cfg.hdims.1
  have hratio : (0 : ℝ) < ((cfg.a / cfg.b : NNReal) : ℝ) := by
    have : (0 : NNReal) < cfg.a / cfg.b := div_pos ha0 hb0
    exact_mod_cast this
  have hcpos : (0 : ℝ) < (slabAxisSeparationConstant bd.C₀ : ℝ) := by
    have := slabAxisSeparationConstant_pos bd.hC₀
    exact_mod_cast this
  rw [hzero] at h4
  nlinarith

/-- **Obstruction (ii), first half, in `Set.InjOn` form**: a slab family all of whose members
pairwise overlap has at most one slab per normal direction. This is the old, unguarded
`injOn_bodyNormal` with the hypothesis the re-cut (S4′) now requires; a family confined to one
overlapping cluster is still direction-injective. -/
theorem IsSlabFamily.injOn_bodyNormal_of_overlap {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    {B : bd.bι} {Wb' : Finset bd.ω} {θ : NNReal} {𝕊 : Set (ConvexSpaceBody E₃)}
    {slabOf : bd.ω → ConvexSpaceBody E₃} (hS : IsSlabFamily cfg B Wb' θ 𝕊 slabOf)
    (hov : ∀ S ∈ 𝕊, ∀ S' ∈ 𝕊,
      (Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∩
        Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S'.carrier).Nonempty)
    (hsep : 𝕊.Pairwise fun S S' ↦
      (Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∩
          Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S'.carrier).Nonempty →
        (slabAxisSeparationConstant bd.C₀ : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ) ≤
          axisAngle S S') :
    Set.InjOn bodyNormal 𝕊 :=
  fun _ hS1 _ hS2 h => hS.eq_of_bodyNormal_eq_of_overlap hS1 hS2 (hov _ hS1 _ hS2) hsep h

/-- **Obstruction (ii), second half.** Two bodies of `𝕎''_B` whose assigned slabs overlap and are
parallel are contained in one and the same slab, hence — by clause (S2) — within `C₀ (a/b) r₁` of
one and the same plane. -/
theorem IsSlabFamily.subset_common_slab_of_bodyNormal_eq {cfg : VeryNotSticky.{u}}
    {bd : BallData cfg} {B : bd.bι} {Wb' : Finset bd.ω} {θ : NNReal}
    {𝕊 : Set (ConvexSpaceBody E₃)} {slabOf : bd.ω → ConvexSpaceBody E₃}
    (hS : IsSlabFamily cfg B Wb' θ 𝕊 slabOf) {j k : bd.ω} (hj : j ∈ Wb') (hk : k ∈ Wb')
    (hov : (Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) (slabOf j).carrier ∩
      Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) (slabOf k).carrier).Nonempty)
    (hsep : 𝕊.Pairwise fun S S' ↦
      (Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∩
          Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S'.carrier).Nonempty →
        (slabAxisSeparationConstant bd.C₀ : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ) ≤
          axisAngle S S')
    (h : bodyNormal (slabOf j) = bodyNormal (slabOf k)) :
    slabOf j = slabOf k ∧ (bd.Wb j).carrier ⊆ (slabOf j).carrier ∧
      (bd.Wb k).carrier ⊆ (slabOf j).carrier := by
  have heq : slabOf j = slabOf k :=
    hS.eq_of_bodyNormal_eq_of_overlap (hS.S3 j hj).1 (hS.S3 k hk).1 hov hsep h
  refine ⟨heq, (hS.S3 j hj).2.1, ?_⟩
  rw [heq]
  exact (hS.S3 k hk).2.1

/-- **Obstruction (i), as arithmetic.** The unconditional rank-`2` lower bound that
`Kakeya.VeryNotSticky.ethickness_aniLin_image_ge` delivers for a body of profile `(r₁, b, a)` at
comparison constant `C₀`, namely `(1/r₁)·(a/C₀)`, is **strictly below** what clause (A2) demands,
namely `ρ₂/C₀ = (b/r₁)/C₀`, at every `a < b`; the two coincide exactly at `a = b`. So (A2) at the
constant `bd.C₀` is not a consequence of the transport alone at general `(a, b)`, and the
alignment of the body's thin direction with `n(S)` — which `Kakeya.VeryNotSticky.IsDenseSlab`
bounds only by `2θ`, with `θ ≤ 1` its only upper bound — is what would have to pay for it, at a
constant that is then a polynomial in `C₀`. -/
theorem aniLin_rank_two_gap {r₁ a b C₀ : ℝ} (hr₁ : 0 < r₁) (ha : 0 < a) (hab : a < b)
    (hC₀ : 0 < C₀) : r₁⁻¹ * (a / C₀) < (b / r₁) / C₀ := by
  have hpos : (0 : ℝ) < r₁ * C₀ := mul_pos hr₁ hC₀
  have e1 : r₁⁻¹ * (a / C₀) = a / (r₁ * C₀) := by field_simp
  have e2 : (b / r₁) / C₀ = b / (r₁ * C₀) := by rw [div_div]
  rw [e1, e2]
  gcongr

end

end Kakeya.VeryNotSticky
