/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.WolffHairbrush
public import Kakeya.DimensionThree.MainLemma2.WangZahl.EquivDE

/-!
# Guardrails for `Kakeya.WangZahl.WolffHairbrushBroad`

Leaf 2 of the Wang--Zahl Proposition 1.10 decomposition
(`Kakeya.DimensionThree.MainLemma2.WangZahl.WolffHairbrush`) was **refuted** in
the form it had at commit `3dce3ef1a`.  This file is the compiler-checked record
of that refutation, kept inside the `Kakeya` target so that a silent revert of
the repair breaks the build.

## The defect

The pre-repair `WolffHairbrushBroad` asked, for each `eps > 0`, for `kappa, nu > 0`
such that every family of essentially distinct `delta`-tubes contained in a
common `theta`-tube, `delta^nu`-dense and `nu`-broad at scale `theta`, obeys

```
kappa * delta^{eps/2} * delta^{3/2} * theta^{1/2} * (#T)^{1/2} <= |union of Y(T)|.
```

It carried **no** Katz--Tao convex Wolff hypothesis.  Wolff's hairbrush theorem
`\cite{Wol95}` is a bound for families of `delta`-**separated directions**, i.e.
`#T <~ delta^{-2}` after rescaling; the leaf as written admitted any essentially
distinct family, hence up to `delta^{-4}` tubes.  Two independent refutations:

* `not_wolffHairbrushBroadAt_of_half_lt` / `nu_le_half_of_wolffHairbrushBroadAt`:
  for a fixed `eps` no quality `nu > eps/2` is admissible at all.  Witness:
  `theta = delta`, the one-element family `centredTube delta` shaded by
  `tubeBox delta (4 delta^nu)`; the shaded volume `8 delta^{nu+2}` falls below the
  demanded `kappa delta^{2+eps/2}`.  (This is a defect of the *split*, not of the
  source: the source keeps the density exponent `3 eta` and the broadness quality
  `eta` distinct, and the split collapsed them into one `nu`.)
* `not_wolffHairbrushBroad_of_packing`: applied at `eps = 1/2`, the first
  refutation forces `nu <= 1/4 <= 2`, `card_le_of_wolffHairbrushBroadAt` caps every
  admissible family by `#T <= (|B(0,1)|/kappa)^2 delta^{-7/2}` at `theta = 1`, and
  the standard `delta`-tube packing of the unit ball (`ExistsBroadPacking`)
  supplies an admissible family with `#T >= C delta^{-7/2}`.

## The repair

`WolffHairbrushBroad` now carries the hypothesis
`katzTaoConvexWolffConstant s T <= delta^{-nu}` (`wolffHairbrushBroad_eq` is the
tripwire that pins the repaired statement).  It is inherited verbatim by every
class of the cover of `HairbrushCover`
(`katzTaoConvexWolffConstant_le_of_subset`), and it is exactly what excludes the
packing: `packing_violates_katzTaoHypothesis` shows the packing family has
`CKT >= 2 delta^{-nu}` for every `nu <= 3/2`, so the second refutation no longer
applies to the repaired leaf.  The first refutation does not apply either, since
`nu` is now also the Katz--Tao budget; but note that it still constrains the
repaired leaf to `nu <= eps/2` whenever the Katz--Tao hypothesis is satisfiable
at that `nu`, which is why `wolffHairbrushBroad_holds` remains open.

The Frostman slab hypothesis `FS(T) <= delta^{-eta}` is deliberately **not**
handed down to the class: a class sits inside a single `theta`-tube, hence inside
a slab of volume `~ theta`, which forces `FS(class) >= c theta^{-1}`.  Handing the
normalized Frostman bound down would create an inconsistent hypothesis bundle at
small `theta` -- green in the compiler, vacuous in content.  See the discussion in
`WolffHairbrush.lean`.
-/

@[expose] public section

open MeasureTheory Metric

namespace Kakeya.WangZahl

noncomputable section

universe u

/-- The axis-aligned box of half-widths `(L, δ/2, δ/2)` centred at the origin.
For `L ≤ 1/2` it is contained in the carrier of `centredTube δ`, and its volume
is exactly `2Lδ²`; it is the shading used by
`not_wolffHairbrushBroadAt_of_half_lt`. -/
noncomputable def tubeBox (δ L : NNReal) : PrismNDim 3 Space3 Space3 :=
  PrismNDim.mk' (0 : Space3) (EuclideanSpace.basisFun (Fin 3) ℝ) ![L, δ/2, δ/2]

/-- The volume of `tubeBox δ L` is `2Lδ²` (`8` times the product of the
half-widths). -/
theorem volume_tubeBox (δ L : NNReal) :
    volume (tubeBox δ L).carrier = 2 * (L:ENNReal) * (δ:ENNReal)^2 := by
  rw [tubeBox, PrismNDim.volume_carrier, finrank_euclideanSpace_fin, Fin.prod_univ_three]
  simp only [PrismNDim.thicknesses_mk', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, ENNReal.coe_div,
    ENNReal.coe_ofNat]
  have hN : (2:NNReal)^3 * (L * (δ/2) * (δ/2)) = 2 * L * δ^2 := by ring
  calc (2:ENNReal)^3 * ((L:ENNReal) * ((δ/2 : NNReal):ENNReal) * ((δ/2 : NNReal):ENNReal))
      = (((2:NNReal)^3 * (L * (δ/2) * (δ/2)) : NNReal) : ENNReal) := by push_cast; ring
    _ = (((2 * L * δ^2 : NNReal)) : ENNReal) := by rw [hN]
    _ = 2 * (L:ENNReal) * (δ:ENNReal)^2 := by push_cast; ring

/-- For `L ≤ 1/2` the box `tubeBox δ L` lies inside the centred `δ`-tube: its
points are within `δ/√2` of the point of the core with the same first
coordinate. -/
theorem tubeBox_subset_centredTube (δ L : NNReal) (hL : L ≤ 1/2) :
    (tubeBox δ L).carrier ⊆ (centredTube δ).carrier := by
  intro x hx
  rw [tubeBox, PrismNDim.mem_carrier_iff] at hx
  simp only [PrismNDim.basis_mk', PrismNDim.thicknesses_mk', PrismNDim.center_mk',
    vsub_eq_sub, sub_zero, EuclideanSpace.basisFun_repr] at hx
  have h0 : |x 0| ≤ (L:ℝ) := by simpa using hx 0
  have h1 : |x 1| ≤ ((δ/2 : NNReal):ℝ) := by simpa using hx 1
  have h2 : |x 2| ≤ ((δ/2 : NNReal):ℝ) := by simpa using hx 2
  rw [(centredTube δ).carrier_eq]
  refine Set.mem_biUnion (show ((x 0) • EuclideanSpace.single (0 : Fin 3) (1:ℝ)) ∈
      segment ℝ (centredTube δ).x (centredTube δ).y from ?_) ?_
  · -- segment membership
    refine ⟨1/2 - x 0, 1/2 + x 0, ?_, ?_, by ring, ?_⟩
    · have : |x 0| ≤ (1:ℝ)/2 := le_trans h0 (by exact_mod_cast hL)
      cases abs_le.mp this; linarith
    · have : |x 0| ≤ (1:ℝ)/2 := le_trans h0 (by exact_mod_cast hL)
      cases abs_le.mp this; linarith
    · show (1/2 - x 0) • (centredTube δ).x + (1/2 + x 0) • (centredTube δ).y = _
      simp only [centredTube, Tube.mk']
      module
  · rw [mem_closedBall, EuclideanSpace.dist_eq]
    have hcoord : ∀ i : Fin 3, (x - (x 0) • EuclideanSpace.single (0:Fin 3) (1:ℝ)) i
        = if i = 0 then 0 else x i := by
      intro i
      fin_cases i <;> simp
    rw [show (Finset.univ.sum fun i => dist (x i) (((x 0) • EuclideanSpace.single (0:Fin 3) (1:ℝ)) i) ^ 2)
        = dist (x 0) (((x 0) • EuclideanSpace.single (0:Fin 3) (1:ℝ)) 0) ^ 2 +
          dist (x 1) (((x 0) • EuclideanSpace.single (0:Fin 3) (1:ℝ)) 1) ^ 2 +
          dist (x 2) (((x 0) • EuclideanSpace.single (0:Fin 3) (1:ℝ)) 2) ^ 2 from Fin.sum_univ_three _]
    have e0 : ((x 0) • EuclideanSpace.single (0:Fin 3) (1:ℝ)) 0 = x 0 := by simp
    have e1 : ((x 0) • EuclideanSpace.single (0:Fin 3) (1:ℝ)) 1 = 0 := by simp
    have e2 : ((x 0) • EuclideanSpace.single (0:Fin 3) (1:ℝ)) 2 = 0 := by simp
    rw [e0, e1, e2, dist_self, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]
    have hd2 : ((δ/2 : NNReal):ℝ) = (δ:ℝ)/2 := by push_cast; ring
    rw [hd2] at h1 h2
    have habs1 : |x 1| ^ 2 ≤ ((δ:ℝ)/2)^2 := by
      have := abs_nonneg (x 1); nlinarith
    have habs2 : |x 2| ^ 2 ≤ ((δ:ℝ)/2)^2 := by
      have := abs_nonneg (x 2); nlinarith
    have hsum : (0:ℝ) ^ 2 + |x 1| ^ 2 + |x 2| ^ 2 ≤ (δ:ℝ)^2 := by nlinarith
    calc Real.sqrt ((0:ℝ) ^ 2 + |x 1| ^ 2 + |x 2| ^ 2)
        ≤ Real.sqrt ((δ:ℝ)^2) := Real.sqrt_le_sqrt hsum
      _ = (δ:ℝ) := Real.sqrt_sq δ.coe_nonneg

/-! ### The refuted pre-repair form of Leaf 2 -/

/-- The **refuted** pre-repair form of `Kakeya.WangZahl.WolffHairbrushBroad`:
Leaf 2 of Wang--Zahl Proposition 1.10 *without* the Katz--Tao convex Wolff
hypothesis on the class.  This is a verbatim copy of the statement as it stood
at commit `3dce3ef1a`; `not_wolffHairbrushBroad_of_packing` below refutes it,
conditionally on the standard tube packing `ExistsBroadPacking`.

Nothing in the development may depend on this Prop.  It exists so that the
refutation stays compiled, and so that re-dropping the Katz--Tao hypothesis from
`WolffHairbrushBroad` is a build failure (`wolffHairbrushBroad_eq`) rather than a
silent regression. -/
def WolffHairbrushBroadNoKatzTao : Prop :=
  ∀ ε > (0 : ℝ), ∃ κ : NNReal, ∃ ν : ℝ, 0 < κ ∧ 0 < ν ∧
    ∀ (δ : NNReal), 0 < δ → δ ≤ 1 → ∀ (θ : NNReal), 0 < θ → θ ≤ 1 →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        IsTubeShadingFamily s T →
        ∀ R : Tube θ Space3, (∀ i ∈ s, (T i).carrier ⊆ R.carrier) →
        IsDense s T ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ →
        IsBroadAtScale s T θ ν →
        (κ : ENNReal) * (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
            (θ : ENNReal) ^ ((1 : ℝ) / 2) * ((s.card : ENNReal) ^ ((1 : ℝ) / 2)) ≤
          volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

/-- **Tripwire on the repaired statement.**  This is `Iff.rfl`, so it stops
typechecking the moment the statement of `Kakeya.WangZahl.WolffHairbrushBroad`
changes, in body or in quantifier prefix.  If it breaks, read the module
docstring before "fixing" it: the form without
`katzTaoConvexWolffConstant s T ≤ δ^{-ν}` is refuted below. -/
theorem wolffHairbrushBroad_eq :
    WolffHairbrushBroad.{u} ↔
      ∀ ε > (0 : ℝ), ∃ κ : NNReal, ∃ ν : ℝ, 0 < κ ∧ 0 < ν ∧
        ∀ (δ : NNReal), 0 < δ → δ ≤ 1 → ∀ (θ : NNReal), 0 < θ → θ ≤ 1 →
          ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
            IsTubeShadingFamily s T →
            ∀ R : Tube θ Space3, (∀ i ∈ s, (T i).carrier ⊆ R.carrier) →
            IsDense s T ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ →
            katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-ν) →
            IsBroadAtScale s T θ ν →
            (κ : ENNReal) * (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
                (θ : ENNReal) ^ ((1 : ℝ) / 2) * ((s.card : ENNReal) ^ ((1 : ℝ) / 2)) ≤
              volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) :=
  Iff.rfl

/-- The refuted form implies the repaired one: the repair only *adds* a
hypothesis, so nothing that used to be available downstream was lost.  (The
converse is false, by `not_wolffHairbrushBroad_of_packing` together with the
fact that `wolffHairbrushBroad_holds` is treated separately.) -/
theorem wolffHairbrushBroad_of_noKatzTao (H : WolffHairbrushBroadNoKatzTao.{u}) :
    WolffHairbrushBroad.{u} := by
  intro ε hε
  obtain ⟨κ, ν, hκ, hν, h⟩ := H ε hε
  refine ⟨κ, ν, hκ, hν, ?_⟩
  intro δ hδ hδ1 θ hθ hθ1 ι s T hfam R hR hdense _hckt hbroad
  exact h δ hδ hδ1 θ hθ hθ1 s T hfam R hR hdense hbroad

/-- The body of the **refuted** form `WolffHairbrushBroadNoKatzTao` at a fixed
triple `(ε, κ, ν)`.  Definitionally `WolffHairbrushBroadNoKatzTao ↔ ∀ ε > 0,
∃ κ ν, 0 < κ ∧ 0 < ν ∧ WolffHairbrushBroadAt ε κ ν`
(`wolffHairbrushBroadNoKatzTao_iff`). -/
def WolffHairbrushBroadAt (ε : ℝ) (κ : NNReal) (ν : ℝ) : Prop :=
  ∀ (δ : NNReal), 0 < δ → δ ≤ 1 → ∀ (θ : NNReal), 0 < θ → θ ≤ 1 →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      IsTubeShadingFamily s T →
      ∀ R : Tube θ Space3, (∀ i ∈ s, (T i).carrier ⊆ R.carrier) →
      IsDense s T ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ →
      IsBroadAtScale s T θ ν →
      (κ : ENNReal) * (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
          (θ : ENNReal) ^ ((1 : ℝ) / 2) * ((s.card : ENNReal) ^ ((1 : ℝ) / 2)) ≤
        volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)


/-- The refuted form `WolffHairbrushBroadNoKatzTao` is exactly the existential
closure of `WolffHairbrushBroadAt`. -/
theorem wolffHairbrushBroadNoKatzTao_iff :
    WolffHairbrushBroadNoKatzTao.{u} ↔
      ∀ ε > (0:ℝ), ∃ κ : NNReal, ∃ ν : ℝ, 0 < κ ∧ 0 < ν ∧
        WolffHairbrushBroadAt.{u} ε κ ν := Iff.rfl

/-- The body of the **repaired** `Kakeya.WangZahl.WolffHairbrushBroad` at a fixed
triple `(ε, κ, ν)`: `WolffHairbrushBroadAt` plus the restored Katz--Tao convex
Wolff hypothesis.  Definitionally `WolffHairbrushBroad ↔ ∀ ε > 0, ∃ κ ν,
0 < κ ∧ 0 < ν ∧ WolffHairbrushBroadAtKT ε κ ν` (`wolffHairbrushBroad_iff`). -/
def WolffHairbrushBroadAtKT (ε : ℝ) (κ : NNReal) (ν : ℝ) : Prop :=
  ∀ (δ : NNReal), 0 < δ → δ ≤ 1 → ∀ (θ : NNReal), 0 < θ → θ ≤ 1 →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      IsTubeShadingFamily s T →
      ∀ R : Tube θ Space3, (∀ i ∈ s, (T i).carrier ⊆ R.carrier) →
      IsDense s T ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ →
      katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-ν) →
      IsBroadAtScale s T θ ν →
      (κ : ENNReal) * (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
          (θ : ENNReal) ^ ((1 : ℝ) / 2) * ((s.card : ENNReal) ^ ((1 : ℝ) / 2)) ≤
        volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

/-- The repaired leaf is exactly the existential closure of
`WolffHairbrushBroadAtKT`. -/
theorem wolffHairbrushBroad_iff :
    WolffHairbrushBroad.{u} ↔
      ∀ ε > (0:ℝ), ∃ κ : NNReal, ∃ ν : ℝ, 0 < κ ∧ 0 < ν ∧
        WolffHairbrushBroadAtKT.{u} ε κ ν := Iff.rfl

/-- Adding a hypothesis weakens: the refuted body implies the repaired body. -/
theorem wolffHairbrushBroadAtKT_of_broadAt {ε : ℝ} {κ : NNReal} {ν : ℝ}
    (H : WolffHairbrushBroadAt.{u} ε κ ν) : WolffHairbrushBroadAtKT.{u} ε κ ν := by
  intro δ hδ hδ1 θ hθ hθ1 ι s T hfam R hR hdense _hckt hbroad
  exact H δ hδ hδ1 θ hθ hθ1 s T hfam R hR hdense hbroad


/-- Scale selection for `not_wolffHairbrushBroadAt_of_half_lt`: for `ν > 0` with
`ν > ε/2` and any `κ > 0` there is a scale `δ` at which the density budget
`4δ^ν` is admissible (`≤ 1/2`) while `8δ^{ν-ε/2} < κ`. -/
theorem exists_scale_for_broadRefutation {ε ν : ℝ} (hν0 : 0 < ν) (hpn : 0 < ν - ε/2) {κ : NNReal} (hκ : 0 < κ) :
    ∃ δ : NNReal, 0 < δ ∧ (δ:ℝ) ≤ 1/2 ∧ 4 * (δ:ℝ) ^ ν ≤ 1/2 ∧
      8 * (δ:ℝ) ^ (ν - ε/2) < (κ:ℝ) := by
  set p := ν - ε/2 with hp
  have h1 : (0:ℝ) < (1/8 : ℝ) ^ (1/ν) := Real.rpow_pos_of_pos (by norm_num) _
  have h2 : (0:ℝ) < ((κ:ℝ)/16) ^ (1/p) := Real.rpow_pos_of_pos (by positivity) _
  set t : ℝ := min (1/2) (min ((1/8:ℝ) ^ (1/ν)) (((κ:ℝ)/16) ^ (1/p))) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (lt_min h1 h2)
  refine ⟨⟨t, ht0.le⟩, ht0, min_le_left _ _, ?_, ?_⟩
  · have hle : t ≤ (1/8:ℝ) ^ (1/ν) := le_trans (min_le_right _ _) (min_le_left _ _)
    have hkey : t ^ ν ≤ (1/8:ℝ) := by
      calc t ^ ν ≤ ((1/8:ℝ) ^ (1/ν)) ^ ν := Real.rpow_le_rpow ht0.le hle hν0.le
        _ = (1/8:ℝ) := by
            rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hν0.ne', Real.rpow_one]
    change 4 * t ^ ν ≤ 1/2
    linarith
  · have hle : t ≤ ((κ:ℝ)/16) ^ (1/p) := le_trans (min_le_right _ _) (min_le_right _ _)
    have hkey : t ^ p ≤ (κ:ℝ)/16 := by
      calc t ^ p ≤ (((κ:ℝ)/16) ^ (1/p)) ^ p := Real.rpow_le_rpow ht0.le hle hpn.le
        _ = (κ:ℝ)/16 := by
            rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hpn.ne', Real.rpow_one]
    change 8 * t ^ p < (κ:ℝ)
    have : (0:ℝ) < (κ:ℝ) := hκ
    linarith

/-- **The second hairbrush leaf is false at every broadness quality `ν > ε/2`.**

Witness: `θ = δ`, the one-element family consisting of `centredTube δ` shaded by
`tubeBox δ (4δ^ν)`.  All hypotheses hold — `IsBroadAtScale` because `θ ≤ δ`
(`isBroadAtScale_of_le_delta`), `IsDense` because
`|tubeBox δ (4δ^ν)| = 8δ^ν · δ² ≥ δ^ν · |T|` — while the shaded volume `8δ^{ν+2}`
is smaller than the demanded `κ δ^{2+ε/2}` as soon as `8δ^{ν-ε/2} < κ`.

Since `ε` is chosen before `ν` in `WolffHairbrushBroad`, this is a genuine
constraint on the leaf and not a repairable constant: see the discussion above. -/
theorem not_wolffHairbrushBroadAtKT_of_half_lt {ε : ℝ} {κ : NNReal} (hκ : 0 < κ)
    {ν : ℝ} (hν0 : 0 < ν) (hνε : ε / 2 < ν) :
    ¬ WolffHairbrushBroadAtKT.{u} ε κ ν := by
  intro H
  obtain ⟨δ, hδ0, hδ2, hL2, hcontr⟩ := exists_scale_for_broadRefutation (ε := ε) hν0 (by linarith) hκ
  have hδ2' : δ ≤ 1/2 := hδ2
  have hδ1 : δ ≤ 1 := le_trans hδ2' (by norm_num)
  set dν : NNReal := ⟨(δ:ℝ)^ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ with hdν
  set L : NNReal := 4 * dν with hLdef
  have hLle : L ≤ 1/2 := by
    change (4 : NNReal) * dν ≤ 1/2
    have hco : ((4 * dν : NNReal) : ℝ) = 4 * (δ:ℝ)^ν := by
      rw [hdν]; norm_num; rfl
    have : ((4 * dν : NNReal) : ℝ) ≤ ((1/2 : NNReal) : ℝ) := by
      rw [hco]; simpa using hL2
    exact_mod_cast this
  set ST : ShadedTube δ Space3 :=
    { toTube := centredTube δ
      shade := (tubeBox δ L).carrier
      measurableSet_shade := (tubeBox δ L).measurableSet_carrier
      shade_subset := tubeBox_subset_centredTube δ L hLle } with hST
  have hfam : IsTubeShadingFamily (Finset.univ : Finset (ULift.{u} (Fin 1))) (fun _ => ST) := by
    refine ⟨fun i _ => centredTube_subset_ball hδ2', ?_⟩
    intro i _ j _ hij
    exact absurd (Subsingleton.elim i j) hij
  have hvolY : volume (tubeBox δ L).carrier = 8 * (δ:ENNReal) ^ ν * (δ:ENNReal)^2 := by
    rw [volume_tubeBox]
    have : ((L : NNReal) : ENNReal) = 4 * (δ:ENNReal) ^ ν := by
      rw [hLdef]
      rw [show (dν : NNReal) = δ ^ ν from rfl, ENNReal.coe_mul,
        ENNReal.coe_rpow_of_ne_zero hδ0.ne']
      norm_num
    rw [this]; ring
  have hcarrier : volume ST.carrier ≤ 8 * (δ:ENNReal)^2 := by
    refine le_trans (Tube.volume_carrier_le (centredTube δ)) ?_
    have : ((1:ENNReal)/2 + (δ:ENNReal)) ≤ 1 := by
      have : (δ:ENNReal) ≤ 1/2 := by
        simpa using (ENNReal.coe_le_coe.mpr hδ2')
      calc (1:ENNReal)/2 + (δ:ENNReal) ≤ 1/2 + 1/2 := by gcongr
        _ = 1 := by rw [ENNReal.div_add_div_same, show (1:ENNReal)+1 = 2 by norm_num, ENNReal.div_self (by norm_num) (by norm_num)]
    calc 8 * (δ:ENNReal)^2 * (1/2 + (δ:ENNReal)) ≤ 8 * (δ:ENNReal)^2 * 1 := by gcongr
      _ = 8 * (δ:ENNReal)^2 := by ring
  have hdense : IsDense (Finset.univ : Finset (ULift.{u} (Fin 1))) (fun _ => ST)
      ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ := by
    rw [IsDense]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_ulift, Fintype.card_fin,
      one_smul]
    have hdcoe : (dν : ENNReal) = (δ:ENNReal) ^ ν :=
      ENNReal.coe_rpow_of_ne_zero hδ0.ne' ν
    change (dν : ENNReal) * volume ST.carrier ≤ volume ST.shade
    rw [hdcoe]
    have hshade : volume ST.shade = 8 * (δ:ENNReal) ^ ν * (δ:ENNReal)^2 := hvolY
    rw [hshade]
    calc (δ:ENNReal) ^ ν * volume ST.carrier
        ≤ (δ:ENNReal) ^ ν * (8 * (δ:ENNReal)^2) := by gcongr
      _ = 8 * (δ:ENNReal) ^ ν * (δ:ENNReal)^2 := by ring
  have key := H δ hδ0 hδ1 δ hδ0 hδ1 (Finset.univ : Finset (ULift.{u} (Fin 1)))
    (fun _ => ST) hfam (centredTube δ) (fun i _ => subset_rfl) hdense
    (le_trans (katzTaoConvexWolffConstant_le_one_of_card_le_one hδ0 (by simp) _)
      (one_le_rpow_neg hδ1 hν0.le))
    (isBroadAtScale_of_le_delta _ _ hδ0 le_rfl ν)
  -- the union of shades of the one-element family is the shade itself
  have hunion : volume (ShadedBody.iUnionShade (Finset.univ : Finset (ULift.{u} (Fin 1)))
      fun i => (ST : ShadedTube δ Space3).toShadedBody) = 8 * (δ:ENNReal) ^ ν * (δ:ENNReal)^2 := by
    have : (ShadedBody.iUnionShade (Finset.univ : Finset (ULift.{u} (Fin 1)))
        fun i => (ST : ShadedTube δ Space3).toShadedBody) = ST.shade := by
      simp [ShadedBody.iUnionShade]
    rw [this]
    exact hvolY
  rw [hunion] at key
  -- the left-hand side is `κ δ^{ε/2} δ²`
  have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hcard : ((Finset.univ : Finset (ULift.{u} (Fin 1))).card : ENNReal) ^ ((1:ℝ)/2) = 1 := by
    simp
  rw [hcard, mul_one] at key
  have hsplit : (δ:ENNReal) ^ ((3:ℝ)/2) * (δ:ENNReal) ^ ((1:ℝ)/2) = (δ:ENNReal)^2 := by
    rw [← ENNReal.rpow_add _ _ hδ0E hδtopE]
    norm_num
  have key2 : (κ:ENNReal) * (δ:ENNReal) ^ (ε/2) * (δ:ENNReal)^2
      ≤ 8 * (δ:ENNReal) ^ ν * (δ:ENNReal)^2 := by
    calc (κ:ENNReal) * (δ:ENNReal) ^ (ε/2) * (δ:ENNReal)^2
        = (κ:ENNReal) * (δ:ENNReal) ^ (ε/2) * ((δ:ENNReal) ^ ((3:ℝ)/2) * (δ:ENNReal) ^ ((1:ℝ)/2)) := by
          rw [hsplit]
      _ = (κ:ENNReal) * (δ:ENNReal) ^ (ε/2) * (δ:ENNReal) ^ ((3:ℝ)/2) * (δ:ENNReal) ^ ((1:ℝ)/2) := by
          ring
      _ ≤ _ := key
  -- but the scale was chosen so that the reverse strict inequality holds
  have hδR : (0:ℝ) < (δ:ℝ) := hδ0
  have hR : 8 * (δ:ℝ)^ν < (κ:ℝ) * (δ:ℝ)^(ε/2) := by
    have hpos : (0:ℝ) < (δ:ℝ)^(ε/2) := Real.rpow_pos_of_pos hδR _
    have := mul_lt_mul_of_pos_right hcontr hpos
    rwa [mul_assoc, ← Real.rpow_add hδR, sub_add_cancel] at this
  have hN : (8:NNReal) * δ^ν < κ * δ^(ε/2) := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    exact hR
  have hE : (8:ENNReal) * (δ:ENNReal)^ν < (κ:ENNReal) * (δ:ENNReal)^(ε/2) := by
    have := ENNReal.coe_lt_coe.mpr hN
    rwa [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδ0.ne',
      ENNReal.coe_rpow_of_ne_zero hδ0.ne', ENNReal.coe_ofNat] at this
  have hsq0 : (δ:ENNReal)^2 ≠ 0 := pow_ne_zero _ hδ0E
  have hsqtop : (δ:ENNReal)^2 ≠ ⊤ := by
    simp [hδtopE, ENNReal.pow_ne_top]
  have hfinal : 8 * (δ:ENNReal) ^ ν * (δ:ENNReal)^2
      < (κ:ENNReal) * (δ:ENNReal) ^ (ε/2) * (δ:ENNReal)^2 := by
    have h := ENNReal.mul_lt_mul_right hsq0 hsqtop hE
    calc 8 * (δ:ENNReal) ^ ν * (δ:ENNReal)^2
        = (δ:ENNReal)^2 * (8 * (δ:ENNReal) ^ ν) := by ring
      _ < (δ:ENNReal)^2 * ((κ:ENNReal) * (δ:ENNReal) ^ (ε/2)) := h
      _ = (κ:ENNReal) * (δ:ENNReal) ^ (ε/2) * (δ:ENNReal)^2 := by ring
  exact absurd key2 (not_le.mpr hfinal)

/-- Consequently, for each `ε` the broadness quality that `WolffHairbrushBroad`
can supply to `HairbrushCover` is at most `ε/2`. -/
theorem not_wolffHairbrushBroadAt_of_half_lt {ε : ℝ} {κ : NNReal} (hκ : 0 < κ)
    {ν : ℝ} (hν0 : 0 < ν) (hνε : ε / 2 < ν) :
    ¬ WolffHairbrushBroadAt.{u} ε κ ν := fun H =>
  not_wolffHairbrushBroadAtKT_of_half_lt hκ hν0 hνε (wolffHairbrushBroadAtKT_of_broadAt H)

/-- The same bound for the **repaired** leaf: restoring the Katz--Tao hypothesis
does *not* rescue the range `ν > ε/2`, because the refuting witness is a
one-tube family, whose Katz--Tao constant is at most `1 ≤ δ^{-ν}`
(`katzTaoConvexWolffConstant_le_one_of_card_le_one`).  So `WolffHairbrushBroad`
can only ever be proved with a broadness quality `ν ≤ ε/2`.  That is compatible
with `HairbrushCover`, which takes `ν` as an input and whose obligations only get
easier as `ν` shrinks. -/
theorem nu_le_half_of_wolffHairbrushBroadAtKT {ε : ℝ} {κ : NNReal} (hκ : 0 < κ)
    {ν : ℝ} (hν0 : 0 < ν) (H : WolffHairbrushBroadAtKT.{u} ε κ ν) : ν ≤ ε / 2 := by
  by_contra hcon
  exact not_wolffHairbrushBroadAtKT_of_half_lt hκ hν0 (lt_of_not_ge hcon) H

theorem nu_le_half_of_wolffHairbrushBroadAt {ε : ℝ} {κ : NNReal} (hκ : 0 < κ)
    {ν : ℝ} (hν0 : 0 < ν) (H : WolffHairbrushBroadAt.{u} ε κ ν) : ν ≤ ε / 2 :=
  nu_le_half_of_wolffHairbrushBroadAtKT hκ hν0 (wolffHairbrushBroadAtKT_of_broadAt H)


/-- **What the leaf asserts about cardinalities.**  All shadings of an admissible
family lie in the unit ball, so `WolffHairbrushBroadAt ε κ ν` caps the number of
tubes:  `κ δ^{3/2+ε/2} θ^{1/2} (#𝕋)^{1/2} ≤ |B(0,1)|`, i.e.
`#𝕋 ≤ (|B|/κ)² δ^{-3-ε} θ^{-1}`.

A `θ`-tube contains `≍ (θ/δ)^4` essentially distinct `δ`-tubes, and that maximal
family is `1`-dense and broad at every quality `ν ≤ 2`; for `θ ≍ 1` this exceeds
the cap.  Exhibiting that packing in Lean is the remaining half of the
refutation. -/
theorem card_le_of_wolffHairbrushBroadAt {ε : ℝ} {κ : NNReal} {ν : ℝ}
    (H : WolffHairbrushBroadAt.{u} ε κ ν) {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {θ : NNReal} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3)
    (hfam : IsTubeShadingFamily s T) (R : Tube θ Space3)
    (hR : ∀ i ∈ s, (T i).carrier ⊆ R.carrier)
    (hdense : IsDense s T ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩)
    (hbroad : IsBroadAtScale s T θ ν) :
    (κ : ENNReal) * (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
        (θ : ENNReal) ^ ((1 : ℝ) / 2) * ((s.card : ENNReal) ^ ((1 : ℝ) / 2)) ≤
      volume (Metric.closedBall (0 : Space3) 1) := by
  refine le_trans (H δ hδ0 hδ1 θ hθ0 hθ1 s T hfam R hR hdense hbroad) ?_
  refine measure_mono ?_
  intro x hx
  simp only [ShadedBody.iUnionShade, Set.mem_iUnion] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  exact hfam.1 i hi ((T i).shade_subset hxi)



/-! ### The refutation of Leaf 2, modulo the standard tube packing

`nu_le_half_of_wolffHairbrushBroatAt` above shows that only `ν ≤ ε/2` can occur.
That is exactly the range in which the *other* obstruction bites.

`card_le_of_wolffHairbrushBroadAt` says that an admissible `(ε, κ, ν)` caps the
size of every admissible family: at `θ = 1`,
`κ δ^{3/2+ε/2} (#𝕋)^{1/2} ≤ |B(0,1)|`, i.e. `#𝕋 ≤ (|B(0,1)|/κ)² δ^{-3-ε}`.
But the unit ball contains `≍ δ^{-4}` essentially distinct `δ`-tubes, and the
full packing is `1`-dense and broad at scale `1` for every quality `ν ≤ 2`
(through a point of the shaded core the directions fill the sphere, so the
fraction of them within chordal distance `r` of a given `w` is `r²/2 ≤ r^ν`).
Since `ν ≤ ε/2 ≤ 2` for `ε ≤ 4`, the packing is admissible and `δ^{-4}` beats
`(|B|/κ)² δ^{-3-ε}` at every small `δ` as soon as `ε < 1`.

So Leaf 2 is **false as split**: `not_wolffHairbrushBroad_of_packing` derives
`¬ WolffHairbrushBroad` from `ExistsBroadPacking`, and `ExistsBroadPacking` is
the standard packing count.  What is missing from the leaf is precisely what the
source's class `𝕋[T_θ]` inherits and this statement drops: the Katz--Tao convex
Wolff bound `CKT(𝕋) ≤ δ^{-η}` (the full packing has `CKT ≍ δ^{-2}`) and the
Frostman slab bound `FS(𝕋) ≤ δ^{-η}`.  Wolff's theorem `\cite{Wol95}` is a bound
for families of **`δ`-separated directions** (`#𝕋 ≲ δ^{-2}`); the passage to
`#𝕋` up to `δ^{-4}` in the leaf has no counterpart in `\cite{Wol95}`.  Any repair
of `hairbrushDecomposition_of_cover_of_broad` must hand those two hypotheses
down from `HairbrushCover` to `WolffHairbrushBroad`. -/

/-- **The standard `δ`-tube packing of the unit ball, isolated as a leaf.**

For every quality `ν ∈ (0,2]` and every constant `C` there is a scale `δ` and a
family of essentially distinct `δ`-tubes in the unit ball, contained in a common
`1`-tube, which is `δ^ν`-dense, broad at scale `1` with quality `ν`, and has at
least `C δ^{-7/2}` members.

Witness (not formalized here): fix a `2δ`-separated maximal net of directions on
`S²` (`≍ δ^{-2}` of them) and, for each direction, the `δ`-tubes whose core
segment is centred on a `2δ`-net of the transverse disc of radius `1/16`
(`≍ δ^{-2}` of them); shade each tube by its intersection with `B(0,1/32)`.
The family has `≍ δ^{-4} ≫ C δ^{-7/2}` members for small `δ`; every point of
`B(0,1/32)` lies in `≍ δ^{-2}` of the shadings with directions filling the
sphere, so the broadness ratio is the spherical-cap fraction `r²/2 ≤ r^ν`; and
each shading is a constant fraction of its tube, hence `≥ δ^ν` of it.
Shading only the inner ball is what makes broadness hold at *every* shaded
point: near `∂B(0,1)` a tube of the unit ball can only be nearly radial, so the
directions there do not fill the sphere.

Reference: the `δ`-tube packing count is the standard four-parameter count for
`δ`-tubes in `B(0,1) ⊆ ℝ³`; see e.g. Katz--Tao and Wolff `\cite{Wol95}`, where
the restriction to `≍ δ^{-2}` tubes is imposed exactly by `δ`-separation of
directions. -/
def ExistsBroadPacking : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 2 → ∀ C : NNReal, ∃ δ : NNReal, 0 < δ ∧ δ ≤ 1 ∧
    ∃ (ι : Type u) (s : Finset ι) (T : ι → ShadedTube δ Space3) (R : Tube 1 Space3),
      IsTubeShadingFamily s T ∧
      (∀ i ∈ s, (T i).carrier ⊆ R.carrier) ∧
      IsDense s T ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ ∧
      IsBroadAtScale s T 1 ν ∧
      (C : ENNReal) * (δ : ENNReal) ^ (-(7 : ℝ) / 2) ≤ (s.card : ENNReal)

/-- **Leaf 2 of Proposition 1.10 is false**, given the standard packing count.

Applied at `ε = 1/2`: any admissible pair `(κ, ν)` has `ν ≤ 1/4 ≤ 2`
(`nu_le_half_of_wolffHairbrushBroadAt`), so the packing family of
`ExistsBroadPacking` satisfies every hypothesis of `WolffHairbrushBroad`, and
its conclusion at `θ = 1` reads

`κ δ^{1/4} δ^{3/2} (#𝕋)^{1/2} ≤ |B(0,1)|`,

while `#𝕋 ≥ C δ^{-7/2}` makes the left side at least `κ C^{1/2}`, which exceeds
`|B(0,1)|` for `C := (|B(0,1)| / κ + 1)²`. -/
theorem not_wolffHairbrushBroad_of_packing (HP : ExistsBroadPacking.{u}) :
    ¬ WolffHairbrushBroadNoKatzTao.{u} := by
  intro H
  obtain ⟨κ, ν, hκ, hν, hW⟩ := H (1 / 2 : ℝ) (by norm_num)
  have hAt : WolffHairbrushBroadAt.{u} (1 / 2 : ℝ) κ ν := hW
  have hν2 : ν ≤ 2 :=
    le_trans (nu_le_half_of_wolffHairbrushBroadAt hκ hν hAt) (by norm_num)
  set B : ENNReal := volume (Metric.closedBall (0 : Space3) 1) with hBdef
  have hBtop : B ≠ ⊤ := measure_closedBall_lt_top.ne
  set c : NNReal := B.toNNReal / κ + 1 with hcdef
  have hlt : B.toNNReal < κ * c := by
    have h1 : κ * (B.toNNReal / κ) = B.toNNReal := by
      field_simp
    have : κ * c = B.toNNReal + κ := by rw [hcdef, mul_add, h1, mul_one]
    rw [this]
    simpa using hκ
  obtain ⟨δ, hδ0, hδ1, ι, s, T, R, hfam, hR, hdense, hbroad, hcard⟩ := HP ν hν hν2 (c ^ 2)
  have key := card_le_of_wolffHairbrushBroadAt hAt hδ0 hδ1
    (θ := 1) one_pos le_rfl s T hfam R hR hdense hbroad
  rw [← hBdef] at key
  have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- rewrite the `θ = 1` factor away
  have hone : (((1 : NNReal) : ENNReal)) ^ ((1 : ℝ) / 2) = 1 := by
    rw [ENNReal.coe_one, ENNReal.one_rpow]
  rw [hone, mul_one] at key
  -- lower bound for the cardinality factor
  have hcardhalf : ((c : ENNReal) * (δ : ENNReal) ^ (-(7 : ℝ) / 4))
      ≤ ((s.card : ENNReal) ^ ((1 : ℝ) / 2)) := by
    refine le_trans (le_of_eq ?_)
      (ENNReal.rpow_le_rpow hcard (by norm_num : (0:ℝ) ≤ 1 / 2))
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2)]
    congr 1
    · rw [hcdef]
      rw [ENNReal.coe_pow, ← ENNReal.rpow_natCast ((B.toNNReal / κ + 1 : NNReal) : ENNReal) 2,
        ← ENNReal.rpow_mul]
      norm_num
    · rw [← ENNReal.rpow_mul]
      norm_num
  -- assemble
  have hexp : (δ : ENNReal) ^ ((1 / 2 : ℝ) / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
      (δ : ENNReal) ^ (-(7 : ℝ) / 4) = 1 := by
    rw [← ENNReal.rpow_add _ _ hδ0E hδtopE, ← ENNReal.rpow_add _ _ hδ0E hδtopE]
    norm_num
  have hstep : (κ : ENNReal) * (c : ENNReal) ≤
      (κ : ENNReal) * (δ : ENNReal) ^ ((1 / 2 : ℝ) / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
        ((s.card : ENNReal) ^ ((1 : ℝ) / 2)) := by
    calc (κ : ENNReal) * (c : ENNReal)
          = (κ : ENNReal) * ((δ : ENNReal) ^ ((1 / 2 : ℝ) / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
              (δ : ENNReal) ^ (-(7 : ℝ) / 4)) * (c : ENNReal) := by rw [hexp, mul_one]
        _ = (κ : ENNReal) * (δ : ENNReal) ^ ((1 / 2 : ℝ) / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
              ((c : ENNReal) * (δ : ENNReal) ^ (-(7 : ℝ) / 4)) := by ring
        _ ≤ (κ : ENNReal) * (δ : ENNReal) ^ ((1 / 2 : ℝ) / 2) * (δ : ENNReal) ^ ((3 : ℝ) / 2) *
              ((s.card : ENNReal) ^ ((1 : ℝ) / 2)) := by gcongr
  have hfinal : ((κ * c : NNReal) : ENNReal) ≤ B := by
    rw [ENNReal.coe_mul]
    exact le_trans hstep key
  have hBcoe : B = ((B.toNNReal : NNReal) : ENNReal) := (ENNReal.coe_toNNReal hBtop).symm
  rw [hBcoe, ENNReal.coe_le_coe] at hfinal
  exact absurd hfinal (not_le.mpr hlt)

/-! ### The repair kills the counterexample

The refutation above is powered by `ExistsBroadPacking`, whose family has
`#T ≍ δ^{-4}` tubes inside the unit ball.  Its Katz--Tao convex Wolff constant is
therefore at least `#T · |T| / |B(0,1)| ≍ δ^{-2}`, far above the budget `δ^{-ν}`
that the repaired `WolffHairbrushBroad` now demands.  The family is consequently
**not** admissible for the repaired leaf, so the refutation does not transfer. -/

/-- A lower bound for the Katz--Tao convex Wolff constant: testing the defining
estimate against the unit ball, which contains every tube of the family, gives
`#𝕋 · |T| ≤ CKT(𝕋) · |B(0,1)|`. -/
theorem card_mul_tubeVolume_le_katzTaoConvexWolffConstant {δ : NNReal} (hδ : 0 < δ)
    {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3)
    (hfam : IsTubeShadingFamily s T) :
    (s.card : ENNReal) * tubeVolume δ ≤
      katzTaoConvexWolffConstant s T * volume (Metric.closedBall (0 : Space3) 1) := by
  obtain ⟨hV0, hVtop⟩ := tubeVolume_pos_and_ne_top hδ
  set B : ENNReal := volume (Metric.closedBall (0 : Space3) 1) with hB
  have hB0 : B ≠ 0 := volume_unitBall_ne_zero
  have hBtop : B ≠ ⊤ := volume_unitBall_ne_top
  set W : ConvexTestSet :=
    ⟨Metric.closedBall (0 : Space3) 1, convex_closedBall (0 : Space3) 1⟩ with hW
  have hfilter : (@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s) = s := by
    refine @Finset.filter_true_of_mem ι (fun i => (T i).carrier ⊆ W.carrier)
      (Classical.decPred _) s ?_
    intro i hi
    exact hfam.1 i hi
  have key : ∀ C ∈ {C : ENNReal | 0 < C ∧ ∀ W : ConvexTestSet,
      ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s).card : ENNReal) ≤
        C * volume W.carrier * (tubeVolume δ)⁻¹},
      (s.card : ENNReal) * tubeVolume δ / B ≤ C := by
    rintro C ⟨-, hC⟩
    have hCB := hC W
    rw [hfilter] at hCB
    refine ENNReal.div_le_of_le_mul ?_
    calc (s.card : ENNReal) * tubeVolume δ
        ≤ (C * B * (tubeVolume δ)⁻¹) * tubeVolume δ := by
          exact mul_le_mul_right' hCB _
      _ = C * B * ((tubeVolume δ)⁻¹ * tubeVolume δ) := by ring
      _ = C * B := by rw [ENNReal.inv_mul_cancel hV0.ne' hVtop, mul_one]
  have hdiv : (s.card : ENNReal) * tubeVolume δ / B ≤ katzTaoConvexWolffConstant s T :=
    le_sInf key
  have := mul_le_mul_right' hdiv B
  refine le_trans (le_of_eq ?_) this
  rw [ENNReal.div_mul_cancel hB0 hBtop]

/-- **The repaired hypothesis excludes the packing.**

The family supplied by `ExistsBroadPacking` at the constant
`C = 2|B(0,1)|/c₃ + 1` satisfies every hypothesis of the *pre-repair* leaf and
violates the restored Katz--Tao hypothesis `CKT(𝕋) ≤ δ^{-ν}` — indeed
`CKT(𝕋) ≥ 2δ^{-ν}` — for every quality `ν ≤ 3/2`.  So the refutation
`not_wolffHairbrushBroad_of_packing` does **not** transfer to the repaired
`WolffHairbrushBroad`. -/
theorem packing_violates_katzTaoHypothesis (HP : ExistsBroadPacking.{u})
    {ν : ℝ} (hν0 : 0 < ν) (hν : ν ≤ 3 / 2) :
    ∃ δ : NNReal, 0 < δ ∧ δ ≤ 1 ∧
      ∃ (ι : Type u) (s : Finset ι) (T : ι → ShadedTube δ Space3) (R : Tube 1 Space3),
        IsTubeShadingFamily s T ∧
        (∀ i ∈ s, (T i).carrier ⊆ R.carrier) ∧
        IsDense s T ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ ∧
        IsBroadAtScale s T 1 ν ∧
        ¬ katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-ν) := by
  set B : ENNReal := volume (Metric.closedBall (0 : Space3) 1) with hB
  have hB0 : B ≠ 0 := volume_unitBall_ne_zero
  have hBtop : B ≠ ⊤ := volume_unitBall_ne_top
  set c : NNReal := Tube.le_volume.c 3 with hc
  have hc0 : 0 < c := Tube.le_volume.c_pos 3
  set C : NNReal := 2 * B.toNNReal / c + 1 with hC
  have hCc : 2 * B ≤ (C : ENNReal) * (c : ENNReal) := by
    have hNN : 2 * B.toNNReal ≤ C * c := by
      rw [hC, add_mul, div_mul_cancel₀ _ hc0.ne']
      exact le_self_add
    have : ((2 * B.toNNReal : NNReal) : ENNReal) ≤ ((C * c : NNReal) : ENNReal) := by
      exact_mod_cast hNN
    rw [ENNReal.coe_mul, ENNReal.coe_mul] at this
    simpa [ENNReal.coe_toNNReal hBtop] using this
  obtain ⟨δ, hδ0, hδ1, ι, s, T, R, hfam, hR, hdense, hbroad, hcard⟩ :=
    HP ν hν0 (by linarith) C
  refine ⟨δ, hδ0, hδ1, ι, s, T, R, hfam, hR, hdense, hbroad, ?_⟩
  have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hrpow0 : (δ : ENNReal) ^ (-ν) ≠ 0 := (ENNReal.rpow_pos (by simpa using hδ0) hδtopE).ne'
  have hrpowtop : (δ : ENNReal) ^ (-ν) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hδ0E hδtopE
  -- `CKT * B ≥ #s * |T| ≥ (C δ^{-7/2})(c δ²) = C c δ^{-3/2} ≥ 2 B δ^{-ν}`
  have hstep : 2 * B * (δ : ENNReal) ^ (-ν) ≤ katzTaoConvexWolffConstant s T * B := by
    refine le_trans ?_ (card_mul_tubeVolume_le_katzTaoConvexWolffConstant hδ0 s T hfam)
    have hexp : (δ : ENNReal) ^ (-(7 : ℝ) / 2) * (δ : ENNReal) ^ (2 : ℝ)
        = (δ : ENNReal) ^ (-(3 : ℝ) / 2) := by
      rw [← ENNReal.rpow_add _ _ hδ0E hδtopE]; norm_num
    have hmono : (δ : ENNReal) ^ (-ν) ≤ (δ : ENNReal) ^ (-(3 : ℝ) / 2) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδ1E (by rw [neg_div]; linarith)
    calc 2 * B * (δ : ENNReal) ^ (-ν)
        ≤ (C : ENNReal) * (c : ENNReal) * (δ : ENNReal) ^ (-(3 : ℝ) / 2) := by
          gcongr
      _ = ((C : ENNReal) * (δ : ENNReal) ^ (-(7 : ℝ) / 2)) *
            ((c : ENNReal) * (δ : ENNReal) ^ (2 : ℝ)) := by
          rw [← hexp]; ring
      _ ≤ (s.card : ENNReal) * tubeVolume δ := by
          exact mul_le_mul' hcard tubeVolume_lower
  intro hcon
  set X : ENNReal := B * (δ : ENNReal) ^ (-ν) with hX
  have hX0 : X ≠ 0 := mul_ne_zero hB0 hrpow0
  have hXtop : X ≠ ⊤ := ENNReal.mul_ne_top hBtop hrpowtop
  have hle : 2 * X ≤ X := by
    calc 2 * X = 2 * B * (δ : ENNReal) ^ (-ν) := by rw [hX]; ring
      _ ≤ katzTaoConvexWolffConstant s T * B := hstep
      _ ≤ (δ : ENNReal) ^ (-ν) * B := by gcongr
      _ = X := by rw [hX]; ring
  have hlt : X < 2 * X := by
    nth_rewrite 1 [← one_mul X]
    exact ENNReal.mul_lt_mul_left hX0 hXtop (by norm_num)
  exact absurd hle (not_le.mpr hlt)


/-! ## Refutation of `Kakeya.WangZahl.BalancedBroadCover`

Leaf 1b of the Wang--Zahl Proposition 1.10 decomposition, `BalancedBroadCover`,
is **false** as stated.  The defect is its last conjunct, the encoding of the
used half of the source's display `broadAtScaleTheta`,

```
sum_j |union_{T in part j} Y(T)|  <=  |union_{T in T} Y(T)|,
```

which carries **no constant and no power of `delta`**, whereas the source's
display is only an approximate identity.  The counting budget `delta^{-eps/16}`
that sits next to it is not enough slack: it tends to `1` as `eps -> 0` at a
fixed `delta`, while the covering multiplicity does not.

**The witness.** Take `delta = theta = 1/256` and the family of *two* orthogonal,
fully shaded `delta`-tubes through the origin (`crossedFamily`).  It satisfies
every hypothesis of the leaf at `nu = 1`:

* both carriers lie in the unit ball (`axisTube_subset_ball`);
* they are essentially distinct (`isEssentiallyDistinct_axisTube`): the
  intersection lies in `closedBall 0 (2 delta)`, of volume `24 c delta^3`, while
  each tube has volume at least `c delta^2`, and `48 delta <= 1`;
* the family is `delta^1`-dense, since the shadings are the whole carriers;
* `CKT <= #T = 2 <= 256 = delta^{-1}` (`katzTaoConvexWolffConstant_le_card`);
* broadness at `theta = delta` is automatic (`isBroadAtScale_of_le_delta`).

**Why no cover works.**  No `delta`-tube contains both members
(`not_union_axisTube_subset`): all `delta`-tubes have the same volume `V`, and
essential distinctness forces `|T_0 union T_1| >= 3V/2 > V`.  So every class of
every cover has at most one member, and the counting conjunct
`2 <= delta^{-1/16} * sum_j #part j` — with `delta^{-1/16} = 256^{1/16} =
sqrt 2 < 2` — forces at least **two** nonempty classes.  Each nonempty class
contributes the full `V` to the left-hand side of the disjointness conjunct, so
that side is at least `2V`, while the right-hand side is
`|T_0 union T_1| = 2V - |T_0 cap T_1| < 2V`, the two tubes sharing the ball
`closedBall 0 delta`.

**What the corrected statement has to say.**  A constant, or a factor
`delta^{-eps/16}`, in front of `|union Y|` does *not* repair the leaf: at
`theta = delta` a planar family of `~delta^{-2}` essentially distinct tubes has
`sum_j |union_{part j} Y| ~ delta^{-2} delta^2 = 1` against
`|union Y| ~ delta`, a ratio `delta^{-1}` that beats every fixed power
`delta^{-c eps}`.  What the source actually does at this point is *shrink the
shadings*: "after a further refinement, we may suppose that each set `T^{T_theta}`
is `delta^{3 eta}`-dense" assigns each point of the union to one class, which is
what makes the classes' shadings disjoint and what the density loss pays for.
The faithful encoding therefore has to let the cover return a shading refinement
`Y_j(T) subset Y(T)`, per class, with the classes' refined shadings pairwise
disjoint and each class `delta^nu`-dense *for its refined shading*; Leaf 2 is
then applied to the refined shadings.  `BalancedBroadCover` as written has no
room for that, since the shaded tubes `T` are fixed.
-/


/-- The unit segment centred at the origin along the `k`-th coordinate axis. -/
def axisTube (δ : NNReal) (k : Fin 3) : Tube δ Space3 :=
  Tube.mk' δ (x := -((1 : ℝ) / 2) • EuclideanSpace.single k (1 : ℝ))
    (y := ((1 : ℝ) / 2) • EuclideanSpace.single k (1 : ℝ)) (by
      have h : (-((1 : ℝ) / 2) • EuclideanSpace.single k (1 : ℝ) -
          ((1 : ℝ) / 2) • EuclideanSpace.single k (1 : ℝ) : Space3) =
          -(EuclideanSpace.single k (1 : ℝ)) := by module
      rw [dist_eq_norm, h, norm_neg, PiLp.norm_single, norm_one])

theorem axisTube_subset_ball {δ : NNReal} (hδ : δ ≤ 1 / 2) (k : Fin 3) :
    (axisTube δ k).carrier ⊆ closedBall (0 : Space3) 1 := by
  have hδR : (δ : ℝ) ≤ 1 / 2 := by exact_mod_cast hδ
  have hseg : segment ℝ (axisTube δ k).x (axisTube δ k).y ⊆
      closedBall (0 : Space3) (1 / 2) := by
    refine (convex_closedBall (0 : Space3) (1 / 2)).segment_subset ?_ ?_ <;>
      simp [axisTube, Metric.mem_closedBall, dist_eq_norm, norm_smul, PiLp.norm_single]
  rw [(axisTube δ k).carrier_eq_cthickening]
  refine (cthickening_subset_of_subset _ hseg).trans ?_
  rw [cthickening_closedBall (by positivity) (by norm_num)]
  exact closedBall_subset_closedBall (by linarith)

/-- Off the axis `k`, every point of the tube `axisTube δ k` has coordinate at most `δ`. -/
theorem abs_apply_le_of_mem_axisTube {δ : NNReal} {k : Fin 3} {p : Space3}
    (hp : p ∈ (axisTube δ k).carrier) {i : Fin 3} (hik : i ≠ k) : |p i| ≤ (δ : ℝ) := by
  rw [(axisTube δ k).carrier_eq] at hp
  simp only [Set.mem_iUnion, exists_prop] at hp
  obtain ⟨z, hz, hpz⟩ := hp
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  have hzi : (a • (axisTube δ k).x + b • (axisTube δ k).y : Space3) i = 0 := by
    simp [axisTube, Tube.mk', hik]
  have h1 : |p i - (a • (axisTube δ k).x + b • (axisTube δ k).y : Space3) i| ≤
      ‖p - (a • (axisTube δ k).x + b • (axisTube δ k).y : Space3)‖ := by
    simpa [Real.norm_eq_abs] using
      PiLp.norm_apply_le (p := 2) (x := p - (a • (axisTube δ k).x + b • (axisTube δ k).y : Space3)) i
  rw [mem_closedBall, dist_eq_norm] at hpz
  rw [hzi, sub_zero] at h1
  exact h1.trans hpz

theorem closedBall_subset_axisTube {δ : NNReal} (k : Fin 3) :
    closedBall (0 : Space3) (δ : ℝ) ⊆ (axisTube δ k).carrier := by
  intro p hp
  rw [(axisTube δ k).carrier_eq]
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨(0 : Space3), ?_, ?_⟩
  · refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    simp only [axisTube, Tube.mk']
    module
  · simpa using hp

theorem inter_axisTube_subset_closedBall {δ : NNReal} :
    (axisTube δ 0).carrier ∩ (axisTube δ 1).carrier ⊆
      closedBall (0 : Space3) (2 * (δ : ℝ)) := by
  intro p ⟨hp0, hp1⟩
  have h1 : |p 1| ≤ (δ:ℝ) := abs_apply_le_of_mem_axisTube hp0 (by decide)
  have h2 : |p 2| ≤ (δ:ℝ) := abs_apply_le_of_mem_axisTube hp0 (by decide)
  have h0 : |p 0| ≤ (δ:ℝ) := abs_apply_le_of_mem_axisTube hp1 (by decide)
  rw [mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  have hδ0 : (0:ℝ) ≤ (δ:ℝ) := δ.coe_nonneg
  have hsum : ∑ i : Fin 3, ‖p i‖ ^ 2 ≤ (2 * (δ:ℝ))^2 := by
    rw [Fin.sum_univ_three]
    simp only [Real.norm_eq_abs]
    nlinarith [abs_nonneg (p 0), abs_nonneg (p 1), abs_nonneg (p 2), sq_abs (p 0), sq_abs (p 1), sq_abs (p 2)]
  calc Real.sqrt (∑ i : Fin 3, ‖p i‖ ^ 2) ≤ Real.sqrt ((2 * (δ:ℝ))^2) := Real.sqrt_le_sqrt hsum
    _ = 2 * (δ:ℝ) := Real.sqrt_sq (by positivity)

/-- Volume of a centred ball of `Space3`, in the spelling `3 * Tube.le_volume.c 3`. -/
theorem volume_closedBall_space3 {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall (0 : Space3) r)
      = ENNReal.ofReal (r ^ 3) * ((3 * Tube.le_volume.c 3 : NNReal) : ENNReal) := by
  have hb : volume (closedBall (0 : Space3) 1) = ((3 * Tube.le_volume.c 3 : NNReal) : ENNReal) := by
    have h := ConvexSpaceBody.volume_closedUnitBall_eq (E := Space3)
    simp only [ConvexSpaceBody.closedUnitBall_carrier] at h
    rw [show Module.finrank ℝ Space3 = 3 by simp] at h
    exact h
  have h := Measure.addHaar_closedBall (volume : Measure Space3) (0 : Space3) hr
  rw [show Module.finrank ℝ Space3 = 3 by simp] at h
  rw [h, ← Measure.addHaar_closedBall_eq_addHaar_ball (volume : Measure Space3) (0:Space3) 1, hb]

/-- A crude but sufficient upper bound for the Katz--Tao convex Wolff constant:
it never exceeds the cardinality of a nonempty family. -/
theorem katzTaoConvexWolffConstant_le_card {δ : NNReal} (hδ : 0 < δ) {ι : Type u}
    {s : Finset ι} (hs : s.Nonempty) (T : ι → ShadedTube δ Space3) :
    katzTaoConvexWolffConstant s T ≤ (s.card : ENNReal) := by
  obtain ⟨hV0, hVtop⟩ := tubeVolume_pos_and_ne_top hδ
  refine sInf_le ⟨?_, ?_⟩
  · exact_mod_cast Nat.pos_of_ne_zero (Finset.card_ne_zero.mpr hs)
  · intro W
    classical
    rcases Finset.eq_empty_or_nonempty (@Finset.filter ι
        (fun i => (T i).carrier ⊆ W.carrier) (Classical.decPred _) s) with he | ⟨i₀, hi₀⟩
    · simp [he]
    · have hi₀' := (@Finset.mem_filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s i₀).mp hi₀
      have hVW : tubeVolume δ ≤ volume W.carrier := by
        rw [← volume_carrier_eq_tubeVolume T i₀]
        exact measure_mono hi₀'.2
      have hone : (1 : ENNReal) ≤ volume W.carrier * (tubeVolume δ)⁻¹ := by
        calc (1 : ENNReal) = tubeVolume δ * (tubeVolume δ)⁻¹ :=
              (ENNReal.mul_inv_cancel hV0.ne' hVtop).symm
          _ ≤ volume W.carrier * (tubeVolume δ)⁻¹ := by gcongr
      calc ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
              (Classical.decPred _) s).card : ENNReal)
          ≤ (s.card : ENNReal) := by
            exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        _ = (s.card : ENNReal) * 1 := (mul_one _).symm
        _ ≤ (s.card : ENNReal) * (volume W.carrier * (tubeVolume δ)⁻¹) := by gcongr
        _ = (s.card : ENNReal) * volume W.carrier * (tubeVolume δ)⁻¹ := by ring

theorem volume_inter_axisTube_le {δ : NNReal} (hδ : δ ≤ 1 / 48) :
    volume ((axisTube δ 0).carrier ∩ (axisTube δ 1).carrier) ≤ (1 / 2) * tubeVolume δ := by
  set c : NNReal := Tube.le_volume.c 3 with hc
  have hlow : ((c : NNReal) : ENNReal) * (δ : ENNReal) ^ (2 : ℕ) ≤ tubeVolume δ := by
    simpa [tubeVolume] using Tube.le_volume (modelTube δ)
  have hball : volume ((axisTube δ 0).carrier ∩ (axisTube δ 1).carrier) ≤
      ENNReal.ofReal ((2 * (δ : ℝ)) ^ 3) * ((3 * c : NNReal) : ENNReal) := by
    refine (measure_mono inter_axisTube_subset_closedBall).trans ?_
    exact le_of_eq (volume_closedBall_space3 (by positivity))
  refine hball.trans ?_
  have hofReal : ENNReal.ofReal ((2 * (δ : ℝ)) ^ 3) = (((2 * δ) ^ 3 : NNReal) : ENNReal) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    norm_cast
  rw [hofReal]
  have hkey : ((2 * δ) ^ 3 * (3 * c) : NNReal) ≤ (1 / 2 : NNReal) * (c * δ ^ 2) := by
    have hδR : (δ : ℝ) ≤ 1 / 48 := by exact_mod_cast hδ
    have h0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
    have hc0 : (0 : ℝ) ≤ (c : ℝ) := c.coe_nonneg
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith [sq_nonneg (δ : ℝ), mul_nonneg hc0 (sq_nonneg (δ : ℝ))]
  calc (((2 * δ) ^ 3 : NNReal) : ENNReal) * ((3 * c : NNReal) : ENNReal)
      = (((2 * δ) ^ 3 * (3 * c) : NNReal) : ENNReal) := by push_cast; ring
    _ ≤ (((1 / 2 : NNReal) * (c * δ ^ 2) : NNReal) : ENNReal) := by exact_mod_cast hkey
    _ = (1 / 2 : ENNReal) * ((c : ENNReal) * (δ : ENNReal) ^ (2 : ℕ)) := by
        push_cast
        norm_num
    _ ≤ (1 / 2 : ENNReal) * tubeVolume δ := by gcongr

/-- The two crossed axis tubes are essentially distinct. -/
theorem isEssentiallyDistinct_axisTube {δ : NNReal} (hδ48 : δ ≤ 1 / 48) :
    IsEssentiallyDistinct (axisTube δ 0).carrier (axisTube δ 1).carrier := by
  have h0 : volume (axisTube δ 0).carrier = tubeVolume δ :=
    Tube.volume_carrier_eq_volume_carrier _ (modelTube δ)
  have h1 : volume (axisTube δ 1).carrier = tubeVolume δ :=
    Tube.volume_carrier_eq_volume_carrier _ (modelTube δ)
  rw [IsEssentiallyDistinct, h0, h1, max_self]
  exact volume_inter_axisTube_le hδ48

/-- No `δ`-tube contains both crossed axis tubes. -/
theorem not_union_axisTube_subset {δ : NNReal} (hδ : 0 < δ) (hδ48 : δ ≤ 1 / 48)
    (R : Tube δ Space3) :
    ¬ ((axisTube δ 0).carrier ∪ (axisTube δ 1).carrier ⊆ R.carrier) := by
  intro hsub
  obtain ⟨hV0, hVtop⟩ := tubeVolume_pos_and_ne_top hδ
  set V : ENNReal := tubeVolume δ with hVdef
  have h0 : volume (axisTube δ 0).carrier = V :=
    Tube.volume_carrier_eq_volume_carrier _ (modelTube δ)
  have h1 : volume (axisTube δ 1).carrier = V :=
    Tube.volume_carrier_eq_volume_carrier _ (modelTube δ)
  have hR : volume R.carrier = V := Tube.volume_carrier_eq_volume_carrier _ (modelTube δ)
  have hmeas : MeasurableSet (axisTube δ 1).carrier :=
    (axisTube δ 1).isCompact'.measurableSet
  have hadd := measure_union_add_inter (μ := (volume : Measure Space3))
    (axisTube δ 0).carrier hmeas
  rw [h0, h1] at hadd
  have hun : volume ((axisTube δ 0).carrier ∪ (axisTube δ 1).carrier) ≤ V := by
    rw [← hR]; exact measure_mono hsub
  have hint : volume ((axisTube δ 0).carrier ∩ (axisTube δ 1).carrier) ≤ (1 / 2) * V :=
    volume_inter_axisTube_le hδ48
  have : V + V ≤ V + (1 / 2) * V := by
    rw [← hadd]; exact add_le_add hun hint
  have hVV : V ≤ (1 / 2) * V := (ENNReal.add_le_add_iff_left hVtop).mp this
  have hlt : (1 / 2) * V < V := by
    rw [one_div, ← ENNReal.div_eq_inv_mul]
    exact ENNReal.half_lt_self hV0.ne' hVtop
  exact absurd hVV (not_le.mpr hlt)

/-- The crossed two-element family: two orthogonal `δ`-tubes through the origin,
fully shaded. -/
def crossedFamily (δ : NNReal) : ULift.{u} (Fin 2) → ShadedTube δ Space3 :=
  fun i => fullShadedTube (axisTube δ (if i.down = 0 then 0 else 1))

theorem not_balancedBroadCover : ¬ BalancedBroadCover.{u} := by
  classical
  intro H
  obtain ⟨δ, hδdef⟩ : ∃ δ : NNReal, δ = 1 / 256 := ⟨_, rfl⟩
  have hfin2 : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
  have hδ0 : 0 < δ := by rw [hδdef]; norm_num
  have hδ48 : δ ≤ 1 / 48 := by rw [hδdef, ← NNReal.coe_le_coe]; push_cast; norm_num
  have hδhalf : δ ≤ 1 / 2 := by rw [hδdef, ← NNReal.coe_le_coe]; push_cast; norm_num
  have hδ1 : δ ≤ 1 := by rw [hδdef, ← NNReal.coe_le_coe]; push_cast; norm_num
  obtain ⟨hV0, hVtop⟩ := tubeVolume_pos_and_ne_top hδ0
  set V : ENNReal := tubeVolume δ with hVdef
  set A : Set Space3 := (axisTube δ 0).carrier with hA
  set B : Set Space3 := (axisTube δ 1).carrier with hB
  set T : ULift.{u} (Fin 2) → ShadedTube δ Space3 := crossedFamily δ with hT
  set s : Finset (ULift.{u} (Fin 2)) := Finset.univ with hs
  -- basic facts about the family
  have hcarr : ∀ i : ULift.{u} (Fin 2), (T i).carrier = if i.down = 0 then A else B := by
    intro i; by_cases h : i.down = 0 <;> simp [hT, crossedFamily, fullShadedTube, h, hA, hB]
  have hshade : ∀ i : ULift.{u} (Fin 2), (T i).shade = (T i).carrier := by
    intro i; rfl
  have hcard : s.card = 2 := by simp [hs]
  have hAV : volume A = V := Tube.volume_carrier_eq_volume_carrier _ (modelTube δ)
  have hBV : volume B = V := Tube.volume_carrier_eq_volume_carrier _ (modelTube δ)
  have hunionshade : ShadedBody.iUnionShade s (fun i => (T i).toShadedBody) = A ∪ B := by
    ext x
    simp only [ShadedBody.iUnionShade, Set.mem_iUnion, Set.mem_union, exists_prop, hs,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hx⟩
      have := hx
      rw [hshade i, hcarr i] at this
      by_cases h : i.down = 0
      · simp [h] at this; exact Or.inl this
      · simp [h] at this; exact Or.inr this
    · rintro (hx | hx)
      · exact ⟨⟨0⟩, by rw [hshade _, hcarr]; simpa using hx⟩
      · exact ⟨⟨1⟩, by rw [hshade _, hcarr]; simpa using hx⟩

  -- the hypotheses of `BalancedBroadCover`
  have hfam : IsTubeShadingFamily s T := by
    refine ⟨?_, ?_⟩
    · intro i _
      rw [hcarr i]
      by_cases h : i.down = 0
      · rw [if_pos h, hA]; exact axisTube_subset_ball hδhalf _
      · rw [if_neg h, hB]; exact axisTube_subset_ball hδhalf _
    · intro i _ j _ hij
      have hd : i.down ≠ j.down := fun h => hij (by cases i; cases j; simpa using h)
      rw [hcarr i, hcarr j]
      rcases hfin2 i.down j.down hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [if_pos h1, if_neg (by rw [h2]; decide)]
        exact isEssentiallyDistinct_axisTube hδ48
      · rw [if_neg (by rw [h1]; decide), if_pos h2]
        exact isEssentiallyDistinct_symm (isEssentiallyDistinct_axisTube hδ48)
  have hdense : IsDense s T ⟨(δ : ℝ) ^ (1 : ℝ), Real.rpow_nonneg δ.coe_nonneg 1⟩ := by
    rw [IsDense]
    set d : NNReal := ⟨(δ : ℝ) ^ (1 : ℝ), Real.rpow_nonneg δ.coe_nonneg 1⟩ with hddef
    have hd1 : d ≤ 1 := by
      have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
      rw [hddef, ← NNReal.coe_le_coe]
      show (δ : ℝ) ^ (1 : ℝ) ≤ ((1 : NNReal) : ℝ)
      rw [Real.rpow_one, NNReal.coe_one]
      exact hδ1R
    have hd1E : (d : ENNReal) ≤ 1 := by exact_mod_cast hd1
    have heq : ∀ i ∈ s, volume (T i).carrier = volume (T i).shade := fun i _ => by rw [hshade i]
    rw [Finset.sum_congr rfl heq]
    calc (d : ENNReal) * ∑ i ∈ s, volume (T i).shade
        ≤ 1 * ∑ i ∈ s, volume (T i).shade := by gcongr
      _ = ∑ i ∈ s, volume (T i).shade := one_mul _
  have hckt : katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-(1 : ℝ)) := by
    refine (katzTaoConvexWolffConstant_le_card hδ0 ⟨⟨0⟩, Finset.mem_univ _⟩ T).trans ?_
    rw [hcard, hδdef]
    rw [show ((1 / 256 : NNReal) : ENNReal) ^ (-(1 : ℝ)) = 256 by
      rw [ENNReal.rpow_neg_one]; norm_num]
    norm_num
  have hbroad : IsBroadAtScale s T δ 1 := isBroadAtScale_of_le_delta s T hδ0 le_rfl 1
  obtain ⟨J, P, parent, part, hpart, hcount, hbal, hdensj, hbroadj, hadd⟩ :=
    H 1 one_pos 1 one_pos δ hδ0 δ le_rfl hδ1 s T hfam hdense hckt hbroad
  -- Step 1: no class can contain both tubes
  have hcardpart : ∀ j ∈ P, (part j).card ≤ 1 := by
    intro j hj
    by_contra hc
    push_neg at hc
    obtain ⟨i, hi, i', hi', hii⟩ := Finset.one_lt_card.mp hc
    have hsub : ∀ i₀ ∈ part j, (T i₀).carrier ⊆ (parent j).carrier := by
      intro i₀ hi₀
      exact (Finset.mem_filter.mp (hpart j hj hi₀)).2
    have hd : i.down ≠ i'.down := fun h => hii (by cases i; cases i'; simpa using h)
    refine not_union_axisTube_subset hδ0 hδ48 (parent j) ?_
    rcases hfin2 i.down i'.down hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Set.union_subset ?_ ?_
      · have := hsub i hi; rwa [hcarr i, if_pos h1] at this
      · have := hsub i' hi'; rwa [hcarr i', if_neg (by rw [h2]; decide)] at this
    · refine Set.union_subset ?_ ?_
      · have := hsub i' hi'; rwa [hcarr i', if_pos h2] at this
      · have := hsub i hi; rwa [hcarr i, if_neg (by rw [h1]; decide)] at this
  -- Step 2: the counting budget forces at least two nonempty classes
  have hsum2 : 2 ≤ ∑ j ∈ P, (part j).card := by
    by_contra hc
    push_neg at hc
    have hle : (∑ j ∈ P, ((part j).card : ENNReal)) ≤ 1 := by
      rw [← Nat.cast_sum]
      exact_mod_cast Nat.lt_succ_iff.mp hc
    rw [hcard] at hcount
    have hx : (2 : ENNReal) ≤ (δ : ENNReal) ^ (-((1 : ℝ) / 16)) := by
      calc (2 : ENNReal) ≤ (δ : ENNReal) ^ (-((1 : ℝ) / 16)) *
            (∑ j ∈ P, ((part j).card : ENNReal)) := by exact_mod_cast hcount
        _ ≤ (δ : ENNReal) ^ (-((1 : ℝ) / 16)) * 1 := by gcongr
        _ = (δ : ENNReal) ^ (-((1 : ℝ) / 16)) := mul_one _
    have hpow : ((δ : ENNReal) ^ (-((1 : ℝ) / 16))) ^ (16 : ℕ) = 256 := by
      rw [hδdef, ← ENNReal.rpow_natCast _ 16, ← ENNReal.rpow_mul]
      norm_num
      rw [ENNReal.rpow_neg_one]
      norm_num
    have h216 : (2 : ENNReal) ^ (16 : ℕ) ≤ ((δ : ENNReal) ^ (-((1 : ℝ) / 16))) ^ (16 : ℕ) := by
      gcongr
    rw [hpow] at h216
    norm_num at h216
  -- Step 3: at least two classes have positive shaded volume `V`
  have hP'card : 2 ≤ (P.filter (fun j => (part j).Nonempty)).card := by
    calc 2 ≤ ∑ j ∈ P, (part j).card := hsum2
      _ ≤ ∑ j ∈ P, (if (part j).Nonempty then 1 else 0) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          by_cases h : (part j).Nonempty
          · rw [if_pos h]; exact hcardpart j hj
          · rw [if_neg h, Finset.not_nonempty_iff_eq_empty.mp h]; simp
      _ = (P.filter (fun j => (part j).Nonempty)).card := (Finset.card_filter _ _).symm
  have hvolj : ∀ j ∈ P.filter (fun j => (part j).Nonempty),
      V ≤ volume (ShadedBody.iUnionShade (part j) fun i => (T i).toShadedBody) := by
    intro j hj
    obtain ⟨-, hne⟩ := Finset.mem_filter.mp hj
    obtain ⟨i, hi⟩ := hne
    have hsub : (T i).shade ⊆ ShadedBody.iUnionShade (part j) fun i => (T i).toShadedBody := by
      intro x hx
      exact Set.mem_biUnion hi hx
    calc V = volume (T i).carrier := (volume_carrier_eq_tubeVolume T i).symm
      _ = volume (T i).shade := by rw [hshade i]
      _ ≤ _ := measure_mono hsub
  have hbig : 2 * V ≤ ∑ j ∈ P, volume (ShadedBody.iUnionShade (part j)
      fun i => (T i).toShadedBody) := by
    calc 2 * V ≤ ((P.filter (fun j => (part j).Nonempty)).card : ENNReal) * V := by
          gcongr
          exact_mod_cast hP'card
      _ = ∑ _j ∈ P.filter (fun j => (part j).Nonempty), V := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ P.filter (fun j => (part j).Nonempty),
            volume (ShadedBody.iUnionShade (part j) fun i => (T i).toShadedBody) :=
          Finset.sum_le_sum hvolj
      _ ≤ ∑ j ∈ P, volume (ShadedBody.iUnionShade (part j) fun i => (T i).toShadedBody) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  -- Step 4: contradiction with the essential-disjointness conjunct
  rw [hunionshade] at hadd
  have hfinal : 2 * V ≤ volume (A ∪ B) := hbig.trans hadd
  have hmeasB : MeasurableSet B := (axisTube δ 1).isCompact'.measurableSet
  have hsplit := measure_union_add_inter (μ := (volume : Measure Space3)) A hmeasB
  rw [hAV, hBV] at hsplit
  have hpos : 0 < volume (A ∩ B) := by
    have hsub : closedBall (0 : Space3) (δ : ℝ) ⊆ A ∩ B :=
      Set.subset_inter (closedBall_subset_axisTube 0) (closedBall_subset_axisTube 1)
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    exact measure_closedBall_pos _ _ (by exact_mod_cast hδ0)
  have hcancel : 2 * V + volume (A ∩ B) ≤ 2 * V + 0 := by
    rw [add_zero]
    calc 2 * V + volume (A ∩ B) ≤ volume (A ∪ B) + volume (A ∩ B) := by gcongr
      _ = V + V := hsplit
      _ = 2 * V := by ring
  have h2Vtop : 2 * V ≠ ⊤ := by finiteness
  have hzero := (ENNReal.add_le_add_iff_left h2Vtop).mp hcancel
  exact absurd (nonpos_iff_eq_zero.mp hzero) hpos.ne'



/-! ## A satisfiability certificate at a **non-degenerate** scale `θ > δ`

Every certificate on record so far sits at `θ = δ`, where the broadness
condition is vacuous (`isBroadAtScale_of_le_delta`: the range `r ∈ [δ, θ]`
collapses to `r = θ`, and the bound reads `#{...} ≤ 1 · #𝕋_Y(x)`).  A certificate
at `θ > δ` is strictly stronger, because there `IsBroadAtScale` really does have
to be verified, and it carries the pointwise multiplicity demand
`#𝕋_Y(x) ≥ (θ/δ)^ν` of `rpow_le_multiplicity_of_isBroadAtScale`.

The witness is the crossed pair again, but with the shadings taken to be the
ball `closedBall 0 δ` that **both** tubes contain, so that every point of every
shading has multiplicity `2`:

* `θ = (5/4) δ`, `ν = 2`, so `(θ/δ)^ν = 25/16 ≤ 2` and the multiplicity demand
  is met with equality-to-spare;
* the count of tubes within `r` of a direction `w` never reaches `2`, because
  the two directions are orthogonal: `‖σ e₀ - τ e₁‖ = √2 ≥ 1` for either choice
  of signs (`one_le_norm_sub_signed`), so two tubes in the count force
  `1 ≤ 2r`, i.e. `r ≥ 1/2`, while `r ≤ θ ≤ 5/192`;
* `δ^ν`-density holds because `|closedBall 0 δ| ≍ δ³` beats `δ² |T| ≍ δ⁴`, which
  is what fixes `ν = 2` (at `ν = 1` the density fails: two transverse `δ`-tubes
  meet in volume `≍ δ³`, only a `δ`-fraction of `|T|`);
* `CKT ≤ #𝕋 = 2 ≤ δ^{-2}`.

**How far this can be pushed, and why not further here.**  The two constraints
fight: the multiplicity demand `(θ/δ)^ν ≤ #𝕋_Y(x)` pushes `ν` down, and the
density demand `δ^ν ≲ |Y|/|T|` pushes `ν` up.  For a family of *bounded* size
the shadings must sit in the pairwise intersections, whose volume is `≍ δ |T|`,
forcing `ν ≳ 1` and hence `θ/δ ≤ (#𝕋)^{1/ν} = O(1)`.  So no `O(1)`-size witness
reaches `θ ≫ δ`, and `rpow_le_card_of_isBroadAtScale` is the mechanical form of
that obstruction: a broad family has `#𝕋 ≥ (θ/δ)^ν`.  A witness at `θ ≍ 1` has
to be a genuine `≍ 1/δ`-tube arrangement — three families of parallel `δ`-tubes
at mutual angle `60°` in a plane is the smallest design that works, since the
count-equals-multiplicity case forces the directions at a point to leave no
unit vector within angle `arcsin(θ/2)` of all of them — and building it in Lean
is a separate steps. -/

def crossedBallFamily (δ : NNReal) : ULift.{u} (Fin 2) → ShadedTube δ Space3 :=
  fun i =>
    { toTube := axisTube δ (if i.down = 0 then 0 else 1)
      shade := closedBall (0 : Space3) (δ : ℝ)
      measurableSet_shade := measurableSet_closedBall
      shade_subset := closedBall_subset_axisTube _ }

theorem direction_axisTube {δ : NNReal} (k : Fin 3) :
    (axisTube δ k).direction = EuclideanSpace.single k (1 : ℝ) := by
  simp only [Tube.direction, axisTube, Tube.mk']
  module

/-- Two orthogonal unit axis vectors, with either sign, are at distance at least `1`. -/
theorem one_le_norm_sub_signed {σ τ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    (1 : ℝ) ≤ ‖σ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
      - τ • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)‖ := by
  rw [EuclideanSpace.norm_eq]
  have h : ∑ i : Fin 3, ‖(σ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
      - τ • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) i‖ ^ 2 = 2 := by
    simp [Fin.sum_univ_three]
    rcases hσ with h | h <;> rcases hτ with h' | h' <;> simp [h, h'] <;> norm_num
  rw [h, show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- The broadness condition holds for `crossedBallFamily` at every scale
`θ ∈ [δ, 1/2)` with `(θ/δ)^2 ≤ 2`. -/
theorem isBroadAtScale_crossedBallFamily {δ θ : NNReal} (hδ0 : 0 < δ) (hδθ : δ ≤ θ)
    (hθhalf : (θ : ℝ) < 1 / 2)
    (hq : (1 : ENNReal) ≤ ((δ / θ : NNReal) : ENNReal) ^ (2 : ℝ) * 2) :
    IsBroadAtScale (Finset.univ : Finset (ULift.{u} (Fin 2))) (crossedBallFamily.{u} δ) θ 2 := by
  classical
  intro x w hw r hrδ hrθ
  set T : ULift.{u} (Fin 2) → ShadedTube δ Space3 := crossedBallFamily.{u} δ with hT
  have hshade : ∀ i : ULift.{u} (Fin 2), (T i).shade = closedBall (0 : Space3) (δ : ℝ) :=
    fun _ => rfl
  set F := @Finset.filter (ULift.{u} (Fin 2))
    (fun i => x ∈ (T i).shade ∧
      min ‖w - (T i).toTube.direction‖ ‖w + (T i).toTube.direction‖ ≤ (r : ℝ))
    (Classical.decPred _) Finset.univ with hF
  set G := @Finset.filter (ULift.{u} (Fin 2)) (fun i => x ∈ (T i).shade)
    (Classical.decPred _) Finset.univ with hG
  by_cases hx : x ∈ closedBall (0 : Space3) (δ : ℝ)
  · -- the shadings all contain `x`, so `#G = 2`; and `#F ≤ 1`
    have hGuniv : G = Finset.univ := by
      refine @Finset.filter_true_of_mem (ULift.{u} (Fin 2)) _ (Classical.decPred _) _ ?_
      intro i _
      rw [hshade i]; exact hx
    have hGcard : (G.card : ENNReal) = 2 := by rw [hGuniv]; simp
    have hFcard : F.card ≤ 1 := by
      by_contra hc
      push_neg at hc
      obtain ⟨i, hi, i', hi', hii⟩ := Finset.one_lt_card.mp hc
      have hmem : ∀ m ∈ F, min ‖w - (T m).toTube.direction‖ ‖w + (T m).toTube.direction‖
          ≤ (r : ℝ) := by
        intro m hm
        exact ((@Finset.mem_filter (ULift.{u} (Fin 2)) _ (Classical.decPred _) _ m).mp hm).2.2
      have hdir : ∀ m : ULift.{u} (Fin 2), (T m).toTube.direction
          = EuclideanSpace.single (if m.down = 0 then (0 : Fin 3) else 1) (1 : ℝ) := by
        intro m
        show (axisTube δ (if m.down = 0 then (0 : Fin 3) else 1)).direction = _
        exact direction_axisTube _
      have hsign : ∀ m ∈ F, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
          ‖w - σ • (T m).toTube.direction‖ ≤ (r : ℝ) := by
        intro m hm
        rcases min_le_iff.mp (hmem m hm) with h | h
        · exact ⟨1, Or.inl rfl, by simpa using h⟩
        · refine ⟨-1, Or.inr rfl, ?_⟩
          have : w - (-1 : ℝ) • (T m).toTube.direction = w + (T m).toTube.direction := by
            module
          rw [this]; exact h
      obtain ⟨σ, hσ, hσle⟩ := hsign i hi
      obtain ⟨τ, hτ, hτle⟩ := hsign i' hi'
      -- the two tubes are the two different axes
      have hdown : i.down ≠ i'.down := fun h => hii (by cases i; cases i'; simpa using h)
      have hfin2 : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
      have hkey : ∀ (u v : Space3), ‖w - u‖ ≤ (r:ℝ) → ‖w - v‖ ≤ (r:ℝ) → ‖u - v‖ ≤ 2 * r := by
        intro u v hu hv
        have : u - v = (w - v) - (w - u) := by module
        rw [this]
        calc ‖(w - v) - (w - u)‖ ≤ ‖w - v‖ + ‖w - u‖ := norm_sub_le _ _
          _ ≤ (r:ℝ) + (r:ℝ) := add_le_add hv hu
          _ = 2 * r := by ring
      have hbig : (1 : ℝ) ≤ 2 * (r : ℝ) := by
        rcases hfin2 i.down i'.down hdown with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hdi : (T i).toTube.direction = EuclideanSpace.single (0 : Fin 3) (1:ℝ) := by
            rw [hdir i, if_pos h1]
          have hdi' : (T i').toTube.direction = EuclideanSpace.single (1 : Fin 3) (1:ℝ) := by
            rw [hdir i', if_neg (by rw [h2]; decide)]
          rw [hdi] at hσle; rw [hdi'] at hτle
          exact le_trans (one_le_norm_sub_signed hσ hτ) (hkey _ _ hσle hτle)
        · have hdi : (T i).toTube.direction = EuclideanSpace.single (1 : Fin 3) (1:ℝ) := by
            rw [hdir i, if_neg (by rw [h1]; decide)]
          have hdi' : (T i').toTube.direction = EuclideanSpace.single (0 : Fin 3) (1:ℝ) := by
            rw [hdir i', if_pos h2]
          rw [hdi] at hσle; rw [hdi'] at hτle
          have := le_trans (one_le_norm_sub_signed hτ hσ) (hkey _ _ hτle hσle)
          linarith
      have hrlt : (r : ℝ) < 1 / 2 := lt_of_le_of_lt (by exact_mod_cast hrθ) hθhalf
      linarith
    -- assemble
    have hle1 : (F.card : ENNReal) ≤ 1 := by exact_mod_cast hFcard
    refine hle1.trans ?_
    rw [hGcard]
    refine hq.trans ?_
    gcongr
  · have hFempty : F = ∅ := by
      refine Finset.eq_empty_of_forall_notMem ?_
      intro m hm
      have := ((@Finset.mem_filter (ULift.{u} (Fin 2)) _ (Classical.decPred _) _ m).mp hm).2.1
      rw [hshade m] at this
      exact hx this
    rw [hFempty]
    simp

theorem isTubeShadingFamily_crossedBallFamily {δ : NNReal} (hδ48 : δ ≤ 1 / 48) :
    IsTubeShadingFamily (Finset.univ : Finset (ULift.{u} (Fin 2))) (crossedBallFamily.{u} δ) := by
  classical
  have hδhalf : δ ≤ 1 / 2 := le_trans hδ48 (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  have hfin2 : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
  have hcarr : ∀ i : ULift.{u} (Fin 2), (crossedBallFamily.{u} δ i).carrier
      = (axisTube δ (if i.down = 0 then 0 else 1)).carrier := fun _ => rfl
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [hcarr i]; exact axisTube_subset_ball hδhalf _
  · intro i _ j _ hij
    have hd : i.down ≠ j.down := fun h => hij (by cases i; cases j; simpa using h)
    rw [hcarr i, hcarr j]
    rcases hfin2 i.down j.down hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos h1, if_neg (by rw [h2]; decide)]
      exact isEssentiallyDistinct_axisTube hδ48
    · rw [if_neg (by rw [h1]; decide), if_pos h2]
      exact isEssentiallyDistinct_symm (isEssentiallyDistinct_axisTube hδ48)

theorem isDense_crossedBallFamily {δ : NNReal} (hδ0 : 0 < δ) (hδ48 : δ ≤ 1 / 48)
    (hδc : 16 * δ ≤ 3 * Tube.le_volume.c 3) :
    IsDense (Finset.univ : Finset (ULift.{u} (Fin 2))) (crossedBallFamily.{u} δ)
      ⟨(δ : ℝ) ^ (2 : ℝ), Real.rpow_nonneg δ.coe_nonneg 2⟩ := by
  classical
  have hδ1 : δ ≤ 1 := le_trans hδ48 (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  set T : ULift.{u} (Fin 2) → ShadedTube δ Space3 := crossedBallFamily.{u} δ with hT
  have hc : ∀ i : ULift.{u} (Fin 2), volume (T i).carrier = tubeVolume δ := fun _ =>
    Tube.volume_carrier_eq_volume_carrier _ (modelTube δ)
  have hs : ∀ i : ULift.{u} (Fin 2), volume (T i).shade
      = volume (closedBall (0 : Space3) (δ : ℝ)) := fun _ => rfl
  have hd : (⟨(δ : ℝ) ^ (2 : ℝ), Real.rpow_nonneg δ.coe_nonneg 2⟩ : NNReal) = δ ^ 2 := by
    refine Subtype.ext ?_
    show (δ : ℝ) ^ (2 : ℝ) = ((δ ^ 2 : NNReal) : ℝ)
    rw [NNReal.coe_pow, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [IsDense, hd, Finset.sum_congr rfl (fun i _ => hc i),
    Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_const, Finset.sum_const,
    Finset.card_univ]
  have hcard : Fintype.card (ULift.{u} (Fin 2)) = 2 := by simp
  rw [hcard, nsmul_eq_mul, nsmul_eq_mul]
  -- reduce to `δ² · |T| ≤ |B(0,δ)|`
  have hball : volume (closedBall (0 : Space3) (δ : ℝ))
      = ((δ ^ 3 * (3 * Tube.le_volume.c 3) : NNReal) : ENNReal) := by
    rw [volume_closedBall_space3 δ.coe_nonneg]
    rw [show ENNReal.ofReal ((δ : ℝ) ^ 3) = ((δ ^ 3 : NNReal) : ENNReal) by
      rw [← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal]]
    rw [← ENNReal.coe_mul]
  have hV : tubeVolume δ ≤ ((16 * δ ^ 2 : NNReal) : ENNReal) := by
    refine (tubeVolume_le hδ1).trans (le_of_eq ?_)
    rw [ENNReal.coe_mul, ENNReal.coe_pow]
    norm_num
  have hkey : ((δ ^ 2 : NNReal) : ENNReal) * tubeVolume δ ≤
      volume (closedBall (0 : Space3) (δ : ℝ)) := by
    rw [hball]
    refine le_trans (mul_le_mul_left' hV _) ?_
    rw [← ENNReal.coe_mul]
    refine ENNReal.coe_le_coe.mpr ?_
    calc δ ^ 2 * (16 * δ ^ 2) = δ ^ 3 * (16 * δ) := by ring
      _ ≤ δ ^ 3 * (3 * Tube.le_volume.c 3) := by gcongr
  calc ((δ ^ 2 : NNReal) : ENNReal) * (2 * tubeVolume δ)
      = 2 * (((δ ^ 2 : NNReal) : ENNReal) * tubeVolume δ) := by ring
    _ ≤ 2 * volume (closedBall (0 : Space3) (δ : ℝ)) := by gcongr

theorem katzTao_crossedBallFamily {δ : NNReal} (hδ0 : 0 < δ) (hδ48 : δ ≤ 1 / 48) :
    katzTaoConvexWolffConstant (Finset.univ : Finset (ULift.{u} (Fin 2)))
      (crossedBallFamily.{u} δ) ≤ (δ : ENNReal) ^ (-(2 : ℝ)) := by
  classical
  refine (katzTaoConvexWolffConstant_le_card hδ0 ⟨⟨0⟩, Finset.mem_univ _⟩ _).trans ?_
  have hcard : ((Finset.univ : Finset (ULift.{u} (Fin 2))).card : ENNReal) = 2 := by simp
  rw [hcard, ENNReal.rpow_neg]
  have hsq : (δ : ENNReal) ^ (2 : ℝ) ≤ 1 / 2 := by
    have h1 : (δ : ENNReal) ^ (2 : ℝ) = ((δ ^ 2 : NNReal) : ENNReal) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, ENNReal.coe_pow]
    have h2 : (δ ^ 2 : NNReal) ≤ 1 / 2 := by
      have hle : δ ≤ 1 / 48 := hδ48
      calc δ ^ 2 ≤ (1 / 48 : NNReal) ^ 2 := by gcongr
        _ ≤ 1 / 2 := by rw [← NNReal.coe_le_coe]; push_cast; norm_num
    rw [h1]
    calc ((δ ^ 2 : NNReal) : ENNReal) ≤ ((1 / 2 : NNReal) : ENNReal) :=
          ENNReal.coe_le_coe.mpr h2
      _ = 1 / 2 := by simp
  have : ((1 : ENNReal) / 2)⁻¹ ≤ ((δ : ENNReal) ^ (2 : ℝ))⁻¹ :=
    ENNReal.inv_le_inv.mpr hsq
  simpa using this

/-- **A satisfiability certificate at a non-degenerate scale `θ > δ`.** -/
theorem crossedBall_hypotheses_satisfiable_nondegenerate {δ : NNReal} (hδ0 : 0 < δ)
    (hδ48 : δ ≤ 1 / 48) (hδc : 16 * δ ≤ 3 * Tube.le_volume.c 3) :
    ∃ θ : NNReal, δ < θ ∧ θ ≤ 1 ∧
      (Finset.univ : Finset (ULift.{u} (Fin 2))).Nonempty ∧
      IsTubeShadingFamily (Finset.univ : Finset (ULift.{u} (Fin 2))) (crossedBallFamily.{u} δ) ∧
      IsDense (Finset.univ : Finset (ULift.{u} (Fin 2))) (crossedBallFamily.{u} δ)
        ⟨(δ : ℝ) ^ (2 : ℝ), Real.rpow_nonneg δ.coe_nonneg 2⟩ ∧
      katzTaoConvexWolffConstant (Finset.univ : Finset (ULift.{u} (Fin 2)))
        (crossedBallFamily.{u} δ) ≤ (δ : ENNReal) ^ (-(2 : ℝ)) ∧
      IsBroadAtScale (Finset.univ : Finset (ULift.{u} (Fin 2)))
        (crossedBallFamily.{u} δ) θ 2 := by
  classical
  refine ⟨(5 / 4 : NNReal) * δ, ?_, ?_, ⟨⟨0⟩, Finset.mem_univ _⟩,
    isTubeShadingFamily_crossedBallFamily hδ48, isDense_crossedBallFamily hδ0 hδ48 hδc,
    katzTao_crossedBallFamily hδ0 hδ48, ?_⟩
  · calc δ = 1 * δ := (one_mul _).symm
      _ < (5 / 4 : NNReal) * δ := by
          refine mul_lt_mul_of_pos_right ?_ hδ0
          rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  · have : (5 / 4 : NNReal) * δ ≤ (5 / 4 : NNReal) * (1 / 48) := by gcongr
    refine this.trans ?_
    rw [← NNReal.coe_le_coe]; push_cast; norm_num
  · have hδθ : δ ≤ (5 / 4 : NNReal) * δ := by
      calc δ = 1 * δ := (one_mul _).symm
        _ ≤ (5 / 4 : NNReal) * δ := by
            refine mul_le_mul_right' ?_ _
            rw [← NNReal.coe_le_coe]; push_cast; norm_num
    refine isBroadAtScale_crossedBallFamily hδ0 hδθ ?_ ?_
    · have h1 : ((5 / 4 : NNReal) * δ : ℝ) ≤ (5 / 4 : ℝ) * (1 / 48) := by
        have : (5 / 4 : NNReal) * δ ≤ (5 / 4 : NNReal) * (1 / 48) := by gcongr
        have := NNReal.coe_le_coe.mpr this
        push_cast at this ⊢
        linarith
      push_cast at h1 ⊢
      linarith
    · have hratio : (δ / ((5 / 4 : NNReal) * δ) : NNReal) = 4 / 5 := by
        rw [mul_comm, ← div_div, div_self hδ0.ne']
        rw [← NNReal.coe_inj]; push_cast; norm_num
      rw [hratio]
      have h1 : ((4 / 5 : NNReal) : ENNReal) ^ (2 : ℝ) = ((16 / 25 : NNReal) : ENNReal) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, ← ENNReal.coe_pow]
        congr 1
        rw [← NNReal.coe_inj]; push_cast; norm_num
      rw [h1]
      rw [show (2 : ENNReal) = ((2 : NNReal) : ENNReal) by simp, ← ENNReal.coe_mul,
        show ((1 : ENNReal)) = ((1 : NNReal) : ENNReal) by simp]
      refine ENNReal.coe_le_coe.mpr ?_
      rw [← NNReal.coe_le_coe]; push_cast; norm_num

/-- The certificate applies at every sufficiently small `δ`: `Tube.le_volume.c 3`
is positive, so `δ₀ = min (1/48) (3 c₃ / 16)` is a positive threshold. -/
theorem exists_nondegenerate_broad_witness :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ →
      ∃ θ : NNReal, δ < θ ∧ θ ≤ 1 ∧
        (Finset.univ : Finset (ULift.{u} (Fin 2))).Nonempty ∧
        IsTubeShadingFamily (Finset.univ : Finset (ULift.{u} (Fin 2)))
          (crossedBallFamily.{u} δ) ∧
        IsDense (Finset.univ : Finset (ULift.{u} (Fin 2))) (crossedBallFamily.{u} δ)
          ⟨(δ : ℝ) ^ (2 : ℝ), Real.rpow_nonneg δ.coe_nonneg 2⟩ ∧
        katzTaoConvexWolffConstant (Finset.univ : Finset (ULift.{u} (Fin 2)))
          (crossedBallFamily.{u} δ) ≤ (δ : ENNReal) ^ (-(2 : ℝ)) ∧
        IsBroadAtScale (Finset.univ : Finset (ULift.{u} (Fin 2)))
          (crossedBallFamily.{u} δ) θ 2 := by
  have hc : (0 : NNReal) < Tube.le_volume.c 3 := Tube.le_volume.c_pos 3
  refine ⟨min (1 / 48) (3 * Tube.le_volume.c 3 / 16), ?_, ?_⟩
  · refine lt_min ?_ ?_
    · rw [← NNReal.coe_lt_coe]; push_cast; norm_num
    · positivity
  · intro δ hδ0 hδ
    refine crossedBall_hypotheses_satisfiable_nondegenerate hδ0 (le_trans hδ (min_le_left _ _)) ?_
    have h := le_trans hδ (min_le_right _ _)
    calc (16 : NNReal) * δ ≤ 16 * (3 * Tube.le_volume.c 3 / 16) := by gcongr
      _ = 3 * Tube.le_volume.c 3 := by
          rw [mul_div_assoc']
          rw [mul_comm]
          exact mul_div_cancel_right₀ _ (by norm_num)

/-! ## The shading refinement repairs the refutation

`not_balancedBroadCover` above refutes the fixed-shading covering leaf at the
crossed family: `δ = θ = 1/256`, `ν = 1`, `ε = 1`, two orthogonal fully shaded
`δ`-tubes `A`, `B` through the origin.  No `δ`-tube contains both
(`not_union_axisTube_subset`), so every class of any cover holds at most one of
them; the counting conjunct then forces two nonempty classes, contributing
`|A| + |B| = 2V` on the left of the essential-disjointness conjunct, against
`|A ∪ B| = 2V - |A ∩ B| < 2V` on the right.

The theorem below is the compiler-checked statement that the restatement is the
right repair: at *the same witness*, and for every admissible `δ`, the
conclusion of `Kakeya.WangZahl.RefinedBalancedBroadCover` — all seven conjuncts,
at `θ = δ`, `ν = 1`, `ε = 1` — **is** achievable, by handing the class of `A`
the refined shading `A \ B` and the class of `B` the shading `B`.  The
essential-disjointness conjunct then holds with equality,
`|A \ B| + |B| = |A ∪ B|`, which is exactly the slack the fixed-shading form
did not have.

The refined shading is still `δ^ν`-dense, `ν = 1`: `|A \ B| ≥ |A| - |A ∩ B| ≥
V/2 ≥ δ V` by `volume_inter_axisTube_le`.  So the repair is not bought by
letting the shadings collapse. -/

theorem exists_refinedCover_crossedFamily {δ : NNReal} (hδ0 : 0 < δ) (hδ48 : δ ≤ 1 / 48) :
    ∃ (P : Finset (ULift.{u} (Fin 2))) (parent : ULift.{u} (Fin 2) → Tube δ Space3)
      (part : ULift.{u} (Fin 2) → Finset (ULift.{u} (Fin 2)))
      (Y : ULift.{u} (Fin 2) → ULift.{u} (Fin 2) → ShadedTube δ Space3),
      (∀ j ∈ P, part j ⊆
        @Finset.filter (ULift.{u} (Fin 2))
          (fun i => (crossedFamily.{u} δ i).carrier ⊆ (parent j).carrier)
          (Classical.decPred _) Finset.univ) ∧
      ((Finset.univ : Finset (ULift.{u} (Fin 2))).card : ENNReal) ≤
        (δ : ENNReal) ^ (-((1 : ℝ) / 16)) * (∑ j ∈ P, ((part j).card : ENNReal)) ∧
      (∀ j ∈ P, ∀ j' ∈ P, ((part j').card : ENNReal) ≤ 2 * ((part j).card : ENNReal)) ∧
      (∀ j ∈ P, IsShadingRefinement (part j) (Y j) (crossedFamily.{u} δ)) ∧
      (∀ j ∈ P, IsDense (part j) (Y j)
        ⟨(δ : ℝ) ^ (1 : ℝ), Real.rpow_nonneg δ.coe_nonneg 1⟩) ∧
      (∀ j ∈ P, IsBroadAtScale (part j) (Y j) δ 1) ∧
      (∑ j ∈ P, volume (ShadedBody.iUnionShade (part j)
          fun i => (Y j i).toShadedBody)) ≤
        volume (ShadedBody.iUnionShade (Finset.univ : Finset (ULift.{u} (Fin 2)))
          fun i => (crossedFamily.{u} δ i).toShadedBody) := by
  classical
  set T : ULift.{u} (Fin 2) → ShadedTube δ Space3 := crossedFamily.{u} δ with hT
  set A : Set Space3 := (axisTube δ 0).carrier with hA
  set B : Set Space3 := (axisTube δ 1).carrier with hB
  have hmeasB : MeasurableSet B := (axisTube δ 1).isCompact'.measurableSet
  have hcarr : ∀ i : ULift.{u} (Fin 2), (T i).carrier = if i.down = 0 then A else B := by
    intro i; by_cases h : i.down = 0 <;> simp [hT, crossedFamily, fullShadedTube, h, hA, hB]
  have hshade : ∀ i : ULift.{u} (Fin 2), (T i).shade = (T i).carrier := fun _ => rfl
  refine ⟨Finset.univ, fun j => axisTube δ (if j.down = 0 then 0 else 1),
    fun j => {j}, fun j i => if j.down = 0 then restrictShadedTube (T i) Bᶜ hmeasB.compl else T i,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _ i hi
    have : i = j := Finset.mem_singleton.mp hi
    subst this
    refine (@Finset.mem_filter (ULift.{u} (Fin 2)) _ (Classical.decPred _) Finset.univ i).mpr
      ⟨Finset.mem_univ _, ?_⟩
    rw [hcarr i]
    by_cases h : i.down = 0 <;> simp [h, hA, hB]
  · -- counting: `2 ≤ δ^{-1/16} · 2`
    have hδ1 : δ ≤ 1 := le_trans hδ48 (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    have h1 : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-((1 : ℝ) / 16)) :=
      one_le_rpow_neg hδ1 (by norm_num)
    calc ((Finset.univ : Finset (ULift.{u} (Fin 2))).card : ENNReal)
        = 1 * (∑ _j ∈ (Finset.univ : Finset (ULift.{u} (Fin 2))),
            (({_j} : Finset (ULift.{u} (Fin 2))).card : ENNReal)) := by simp
      _ ≤ (δ : ENNReal) ^ (-((1 : ℝ) / 16)) *
            (∑ _j ∈ (Finset.univ : Finset (ULift.{u} (Fin 2))),
              (({_j} : Finset (ULift.{u} (Fin 2))).card : ENNReal)) := by gcongr
  · intro j _ j' _; simp
  · intro j _
    by_cases h : j.down = 0
    · simp only [h, if_pos]
      exact fun i _ => ⟨rfl, Set.inter_subset_left⟩
    · simp only [h, if_false]
      exact fun i _ => ⟨rfl, subset_rfl⟩
  · -- density of the refined shadings
    intro j _
    have hδ1 : δ ≤ 1 := le_trans hδ48 (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    have hd : (⟨(δ : ℝ) ^ (1 : ℝ), Real.rpow_nonneg δ.coe_nonneg 1⟩ : NNReal) = δ :=
      Subtype.ext (Real.rpow_one _)
    rw [IsDense, hd, Finset.sum_singleton, Finset.sum_singleton]
    by_cases h : j.down = 0
    · -- the class of `A`: its shading is refined to `A \ B`
      simp only [h, if_pos]
      have hcarrA : (restrictShadedTube (T j) Bᶜ hmeasB.compl).carrier = A := by
        rw [show (restrictShadedTube (T j) Bᶜ hmeasB.compl).carrier = (T j).carrier from rfl,
          hcarr j, if_pos h]
      have hshA : (restrictShadedTube (T j) Bᶜ hmeasB.compl).shade = A \ B := by
        rw [shade_restrictShadedTube, hshade j, hcarr j, if_pos h, Set.sdiff_eq]
      rw [hcarrA, hshA]
      set V : ENNReal := tubeVolume δ with hV
      obtain ⟨hV0, hVtop⟩ := tubeVolume_pos_and_ne_top hδ0
      have hAV : volume A = V := Tube.volume_carrier_eq_volume_carrier _ (modelTube δ)
      have hsplit : volume (A \ B) + volume (A ∩ B) = volume A :=
        measure_sdiff_add_inter A hmeasB
      have hint : volume (A ∩ B) ≤ (1 / 2) * V := volume_inter_axisTube_le hδ48
      have hone : (1 / 2 : ENNReal) + 1 / 2 = 1 := by
        rw [ENNReal.div_add_div_same, show (1 : ENNReal) + 1 = 2 by norm_num]
        exact ENNReal.div_self (by norm_num : (2 : ENNReal) ≠ 0) (by finiteness)
      have hhalf : (1 / 2 : ENNReal) * V + (1 / 2 : ENNReal) * V = V := by
        rw [← add_mul, hone, one_mul]
      have hhalftop : (1 / 2 : ENNReal) * V ≠ ⊤ := by
        refine ENNReal.mul_ne_top (by norm_num) hVtop
      have hge : (1 / 2 : ENNReal) * V ≤ volume (A \ B) := by
        refine (ENNReal.add_le_add_iff_right hhalftop).mp ?_
        rw [hhalf]
        calc V = volume (A \ B) + volume (A ∩ B) := by rw [hsplit, hAV]
          _ ≤ volume (A \ B) + (1 / 2 : ENNReal) * V := by gcongr
      refine le_trans ?_ hge
      rw [hAV]
      have hδhalf : (δ : ENNReal) ≤ 1 / 2 := by
        have h : δ ≤ 1 / 2 := le_trans hδ48 (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
        have h2 : ((δ : NNReal) : ENNReal) ≤ ((1 / 2 : NNReal) : ENNReal) :=
          ENNReal.coe_le_coe.mpr h
        simpa using h2
      gcongr
    · -- the class of `B`: its shading is unchanged
      simp only [h, if_false]
      have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
      rw [hshade j]
      calc (δ : ENNReal) * volume (T j).carrier ≤ 1 * volume (T j).carrier := by gcongr
        _ = volume (T j).carrier := one_mul _
  · intro j _
    exact isBroadAtScale_of_le_delta _ _ hδ0 le_rfl 1
  · -- essential disjointness, now with equality
    have huniv : (Finset.univ : Finset (ULift.{u} (Fin 2))) = {⟨0⟩, ⟨1⟩} := by
      ext i
      simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
      rcases i with ⟨d⟩
      fin_cases d <;> simp
    have hne : (⟨0⟩ : ULift.{u} (Fin 2)) ∉ ({⟨1⟩} : Finset (ULift.{u} (Fin 2))) := by decide
    have hshadeU : ShadedBody.iUnionShade (Finset.univ : Finset (ULift.{u} (Fin 2)))
        (fun i => (T i).toShadedBody) = A ∪ B := by
      ext x
      simp only [ShadedBody.iUnionShade, Set.mem_iUnion, Set.mem_union, exists_prop,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hx⟩
        have hx' := hx
        rw [hshade i, hcarr i] at hx'
        by_cases h : i.down = 0
        · rw [if_pos h] at hx'; exact Or.inl hx'
        · rw [if_neg h] at hx'; exact Or.inr hx'
      · rintro (hx | hx)
        · exact ⟨⟨0⟩, by rw [hshade _, hcarr]; simpa using hx⟩
        · exact ⟨⟨1⟩, by rw [hshade _, hcarr]; simpa using hx⟩
    rw [hshadeU, huniv, Finset.sum_insert hne, Finset.sum_singleton]
    have h0 : ShadedBody.iUnionShade ({(⟨0⟩ : ULift.{u} (Fin 2))})
        (fun i => (if (⟨0⟩ : ULift.{u} (Fin 2)).down = 0 then
          restrictShadedTube (T i) Bᶜ hmeasB.compl else T i).toShadedBody) = A \ B := by
      simp only [ShadedBody.iUnionShade, Finset.set_biUnion_singleton, if_true]
      rw [shade_restrictShadedTube, hshade _, hcarr]
      simp [Set.sdiff_eq]
    have h1 : ShadedBody.iUnionShade ({(⟨1⟩ : ULift.{u} (Fin 2))})
        (fun i => (if (⟨1⟩ : ULift.{u} (Fin 2)).down = 0 then
          restrictShadedTube (T i) Bᶜ hmeasB.compl else T i).toShadedBody) = B := by
      simp only [ShadedBody.iUnionShade, Finset.set_biUnion_singleton]
      rw [if_neg (by decide : ¬ ((⟨1⟩ : ULift.{u} (Fin 2)).down = 0))]
      rw [hshade _, hcarr]
      simp
    rw [h0, h1]
    have hdisj : Disjoint (A \ B) B := Set.disjoint_sdiff_left
    rw [← measure_union hdisj hmeasB, Set.diff_union_self]

/-! ## Tripwires for the shading-refinement restatement of Leaf 1

`Kakeya.WangZahl.HairbrushCover` and `Kakeya.WangZahl.BroadScaleRefinement` were
restated so that the cover / the reduction returns a **per-class shading
refinement**, the source's "After a further refinement, we may suppose that each
set `𝕋^{T_θ}` is `δ^{3η}`-dense" (`blueprint/src/WZ2/250224e_K3.tex:5748`).

Two independent defects of the fixed-shading forms motivated it.

1. The fixed-shading covering leaf `Kakeya.WangZahl.BalancedBroadCover` is
   **false** (`not_balancedBroadCover` above), and no constant and no `δ^{-cε}`
   factor repairs it: at `θ = δ` a planar family of `≍ δ^{-2}` essentially
   distinct tubes has `∑_j |∪_{part j} Y| ≍ 1` against `|∪ Y| ≍ δ`.  What the
   source does at exactly this point is shrink the shadings.

2. `IsBroadAtScale s T θ ν` applied to a *fixed* shading is an over-demand.
   Tested at `r = δ` and `w = dir T_{i₀}` it puts `T_{i₀}` into its own
   left-hand count (`rpow_le_multiplicity_of_isBroadAtScale` below), so it says
   that every point of every shading is covered by at least `(θ/δ)^ν` tubes.
   The source's condition has the same consequence, but only for the shading it
   has already refined.  The predicate `IsBroadAtScale` is therefore **not**
   changed; what changed is that the leaves apply it to the refined shadings.

The two `Prop`s below are the verbatim pre-change statements, at commit
`c422600eb`.  Nothing in the development may depend on them; they exist so that
the restatement stays honest (`hairbrushCover_eq`, `broadScaleRefinement_eq` are
`Iff.rfl` and break the build if the restated text moves) and so that the
restatements are certified to be *weakenings*
(`hairbrushCover_of_fixedShading`, `broadScaleRefinement_of_fixedShading`):
the fixed-shading forms imply the restated ones by taking the refinement to be
the identity, so nothing available to a downstream consumer was lost. -/

/-- The **pre-restatement**, fixed-shading form of
`Kakeya.WangZahl.HairbrushCover`, verbatim at commit `c422600eb`. -/
def HairbrushCoverFixedShading : Prop :=
  ∀ ε > (0 : ℝ), ∀ ν > (0 : ℝ), ∃ η : ℝ, 0 < η ∧ η ≤ ν ∧
    ∀ (δ : NNReal), 0 < δ → δ ≤ 1 →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        IsTubeShadingFamily s T →
        IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ →
        katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        frostmanSlabWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        ∃ θ : NNReal, 0 < θ ∧ θ ≤ 1 ∧
          ∃ (J : Type u) (P : Finset J) (parent : J → Tube θ Space3) (part : J → Finset ι),
            (∀ j ∈ P, part j ⊆
              @Finset.filter ι (fun i => (T i).carrier ⊆ (parent j).carrier)
                (Classical.decPred _) s) ∧
            (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 8)) *
              (∑ j ∈ P, ((part j).card : ENNReal)) ∧
            (∀ j ∈ P, ∀ j' ∈ P, ((part j').card : ENNReal) ≤ 2 * ((part j).card : ENNReal)) ∧
            (∀ j ∈ P,
              IsDense (part j) T ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩) ∧
            (∀ j ∈ P, IsBroadAtScale (part j) T θ ν) ∧
            (∑ j ∈ P, volume (ShadedBody.iUnionShade (part j)
                fun i => (T i).toShadedBody)) ≤
              volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

/-- **Tripwire on the restated `Kakeya.WangZahl.HairbrushCover`.**  This is
`Iff.rfl`; it stops typechecking the moment the statement changes, in body or in
quantifier prefix.  If it breaks, read the section docstring before "fixing" it:
the per-class shading refinement `Y` is the source's, and the fixed-shading form
of the companion covering leaf is refuted by `not_balancedBroadCover`. -/
theorem hairbrushCover_eq :
    HairbrushCover.{u} ↔
      ∀ ε > (0 : ℝ), ∀ ν > (0 : ℝ), ∃ η : ℝ, 0 < η ∧ η ≤ ν ∧
        ∀ (δ : NNReal), 0 < δ → δ ≤ 1 →
          ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
            IsTubeShadingFamily s T →
            IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ →
            katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
            frostmanSlabWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
            ∃ θ : NNReal, 0 < θ ∧ θ ≤ 1 ∧
              ∃ (J : Type u) (P : Finset J) (parent : J → Tube θ Space3)
                (part : J → Finset ι) (Y : J → ι → ShadedTube δ Space3),
                (∀ j ∈ P, part j ⊆
                  @Finset.filter ι (fun i => (T i).carrier ⊆ (parent j).carrier)
                    (Classical.decPred _) s) ∧
                (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 8)) *
                  (∑ j ∈ P, ((part j).card : ENNReal)) ∧
                (∀ j ∈ P, ∀ j' ∈ P,
                  ((part j').card : ENNReal) ≤ 2 * ((part j).card : ENNReal)) ∧
                (∀ j ∈ P, IsShadingRefinement (part j) (Y j) T) ∧
                (∀ j ∈ P,
                  IsDense (part j) (Y j) ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩) ∧
                (∀ j ∈ P, IsBroadAtScale (part j) (Y j) θ ν) ∧
                (∑ j ∈ P, volume (ShadedBody.iUnionShade (part j)
                    fun i => (Y j i).toShadedBody)) ≤
                  volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) :=
  Iff.rfl

/-- **The restatement only weakens Leaf 1.**  The fixed-shading form implies the
restated one: take the refinement to be the identity, `Y j = T`. -/
theorem hairbrushCover_of_fixedShading (H : HairbrushCoverFixedShading.{u}) :
    HairbrushCover.{u} := by
  intro ε hε ν hν
  obtain ⟨η, hη, hην, h⟩ := H ε hε ν hν
  refine ⟨η, hη, hην, ?_⟩
  intro δ hδ hδ1 ι s T hfam hdens hckt hFS
  obtain ⟨θ, hθ0, hθ1, J, P, parent, part, hpart, hcount, hbal, hdensj, hbroadj, hadd⟩ :=
    h δ hδ hδ1 s T hfam hdens hckt hFS
  exact ⟨θ, hθ0, hθ1, J, P, parent, part, fun _ => T, hpart, hcount, hbal,
    fun j _ => IsShadingRefinement.rfl' _ T, hdensj, hbroadj, hadd⟩

/-- The **pre-restatement**, fixed-shading form of
`Kakeya.WangZahl.BroadScaleRefinement`, verbatim at commit `c422600eb`. -/
def BroadScaleRefinementFixedShading : Prop :=
  ∀ ε > (0 : ℝ), ∀ ν > (0 : ℝ), ∃ η : ℝ, 0 < η ∧ η ≤ ν ∧
    ∀ (δ : NNReal), 0 < δ → δ ≤ 1 →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        IsTubeShadingFamily s T →
        IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ →
        katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        frostmanSlabWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        ∃ θ : NNReal, δ ≤ θ ∧ θ ≤ 1 ∧
          ∃ s' : Finset ι, s' ⊆ s ∧
            (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 16)) * (s'.card : ENNReal) ∧
            IsDense s' T ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ ∧
            IsBroadAtScale s' T θ ν

/-- **Tripwire on the restated `Kakeya.WangZahl.BroadScaleRefinement`.** -/
theorem broadScaleRefinement_eq :
    BroadScaleRefinement.{u} ↔
      ∀ ε > (0 : ℝ), ∀ ν > (0 : ℝ), ∃ η : ℝ, 0 < η ∧ η ≤ ν ∧
        ∀ (δ : NNReal), 0 < δ → δ ≤ 1 →
          ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
            IsTubeShadingFamily s T →
            IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ →
            katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
            frostmanSlabWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
            ∃ θ : NNReal, δ ≤ θ ∧ θ ≤ 1 ∧
              ∃ (s' : Finset ι) (T' : ι → ShadedTube δ Space3), s' ⊆ s ∧
                IsShadingRefinement s' T' T ∧
                (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 16)) * (s'.card : ENNReal) ∧
                IsDense s' T' ⟨(δ : ℝ) ^ ν, Real.rpow_nonneg δ.coe_nonneg ν⟩ ∧
                IsBroadAtScale s' T' θ ν :=
  Iff.rfl

/-- **The restatement only weakens Leaf 1a**: take `T' = T`. -/
theorem broadScaleRefinement_of_fixedShading (H : BroadScaleRefinementFixedShading.{u}) :
    BroadScaleRefinement.{u} := by
  intro ε hε ν hν
  obtain ⟨η, hη, hην, h⟩ := H ε hε ν hν
  refine ⟨η, hη, hην, ?_⟩
  intro δ hδ hδ1 ι s T hfam hdens hckt hFS
  obtain ⟨θ, hδθ, hθ1, s', hss, hcount, hdens', hbroad'⟩ := h δ hδ hδ1 s T hfam hdens hckt hFS
  exact ⟨θ, hδθ, hθ1, s', T, hss, IsShadingRefinement.rfl' _ T, hcount, hdens', hbroad'⟩


/-! ## `IsBroadAtScale` is a pointwise multiplicity hypothesis

A second fidelity issue with the encoding of Leaf 1, recorded here because it
bears on any future restatement of `HairbrushCover`.

`Kakeya.WangZahl.IsBroadAtScale s T θ ν` quantifies over **every** point `x`,
not over a typical one and not over a refined shading.  Testing it at `r = δ`
and at `w = dir T_{i₀}` for a tube `T_{i₀}` whose shading contains `x` puts
`T_{i₀}` itself into the left-hand count, so the left-hand side is at least `1`
and the condition reads

```
1 <= (delta/theta)^nu * #{i : x in Y(T_i)}.
```

That is: **every point of every shading must be covered by at least
`(theta/delta)^nu` tubes of the family.**  For `theta = delta` this is empty
(`isBroadAtScale_of_le_delta`), which is why the only satisfiability certificate
on record, `wolffHairbrushBroad_hypotheses_satisfiable`, is at `theta = delta`.
For `theta >> delta` it is a strong pointwise requirement that a family with a
*fixed* shading generally fails: the far end of a tube of a bush has
multiplicity `1`.  The source's "2-broad" condition is obtained after refining
the shadings to their high-multiplicity part, which the fixed-shading encoding
cannot express -- the same missing degree of freedom that makes
`BalancedBroadCover` false.
-/


/-- **Broadness at a scale `θ > δ` is a multiplicity lower bound.** -/
theorem rpow_le_multiplicity_of_isBroadAtScale {δ θ : NNReal} (hδ : 0 < δ) (hθ : δ ≤ θ)
    {ν : ℝ} {ι : Type u} {s : Finset ι} {T : ι → ShadedTube δ Space3}
    (hbroad : IsBroadAtScale s T θ ν) {x : Space3} {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hx : x ∈ (T i₀).shade) :
    (((θ / δ : NNReal)) : ENNReal) ^ ν ≤
      ((@Finset.filter ι (fun i => x ∈ (T i).shade) (Classical.decPred _) s).card : ENNReal) := by
  classical
  have hθ0 : 0 < θ := lt_of_lt_of_le hδ hθ
  have hmem : i₀ ∈ @Finset.filter ι
      (fun i => x ∈ (T i).shade ∧
        min ‖(T i₀).toTube.direction - (T i).toTube.direction‖
          ‖(T i₀).toTube.direction + (T i).toTube.direction‖ ≤ ((δ : NNReal) : ℝ))
      (Classical.decPred _) s := by
    refine (@Finset.mem_filter ι _ (Classical.decPred _) s i₀).mpr ⟨hi₀, hx, ?_⟩
    refine le_trans (min_le_left _ _) ?_
    simp
  have hone : (1 : ENNReal) ≤ ((@Finset.filter ι
      (fun i => x ∈ (T i).shade ∧
        min ‖(T i₀).toTube.direction - (T i).toTube.direction‖
          ‖(T i₀).toTube.direction + (T i).toTube.direction‖ ≤ ((δ : NNReal) : ℝ))
      (Classical.decPred _) s).card : ENNReal) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero_of_mem hmem)
  have hb := hbroad x (T i₀).toTube.direction (T i₀).toTube.norm_direction δ le_rfl hθ
  have hkey : (1 : ENNReal) ≤ (((δ / θ : NNReal)) : ENNReal) ^ ν *
      ((@Finset.filter ι (fun i => x ∈ (T i).shade) (Classical.decPred _) s).card : ENNReal) :=
    hone.trans hb
  -- multiply through by `(θ/δ)^ν`
  have hdt : ((δ / θ : NNReal) : ENNReal) = ((θ / δ : NNReal) : ENNReal)⁻¹ := by
    rw [← ENNReal.coe_inv (by positivity)]
    congr 1
    rw [inv_div]
  have hpos : ((θ / δ : NNReal) : ENNReal) ≠ 0 := by
    simp only [ne_eq, ENNReal.coe_eq_zero]
    positivity
  have htop : ((θ / δ : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  set y : ENNReal := ((θ / δ : NNReal) : ENNReal) with hy
  rw [hdt, ← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul] at hkey
  set M : ENNReal :=
    ((@Finset.filter ι (fun i => x ∈ (T i).shade) (Classical.decPred _) s).card : ENNReal) with hM
  have hstep : y ^ ν * 1 ≤ y ^ ν * (y ^ (-1 * ν) * M) := by gcongr
  rw [mul_one] at hstep
  refine hstep.trans (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.rpow_add _ _ hpos htop]
  norm_num

/-- **Consequence: a broad family is large.**  If some shading is nonempty then
`IsBroadAtScale s T θ ν` forces `#𝕋 ≥ (θ/δ)^ν`. -/
theorem rpow_le_card_of_isBroadAtScale {δ θ : NNReal} (hδ : 0 < δ) (hθ : δ ≤ θ)
    {ν : ℝ} {ι : Type u} {s : Finset ι} {T : ι → ShadedTube δ Space3}
    (hbroad : IsBroadAtScale s T θ ν) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hne : ((T i₀).shade).Nonempty) :
    (((θ / δ : NNReal)) : ENNReal) ^ ν ≤ (s.card : ENNReal) := by
  classical
  obtain ⟨x, hx⟩ := hne
  refine (rpow_le_multiplicity_of_isBroadAtScale hδ hθ hbroad hi₀ hx).trans ?_
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)



/-! ### The `θ`-cap clause of the source's reduction has teeth

`Kakeya.WangZahl.IsCapConcentrated` is the clause of `250224e_K3.tex:5741` that
the first transcription of Leaf 1a dropped ("there is a vector `v = v(x)` so
that `∠(v, dir T) ≤ θ` for each `T ∈ 𝕋` with `x ∈ Y(T)`").  It is not implied
by the broadness clause: the two-tube witness of
`crossedBall_hypotheses_satisfiable_nondegenerate`, which *is* broad at
`θ = (5/4)δ`, fails it at every `θ < 1/2`.  So adding the cap to Leaf 1a is a
genuine strengthening of that leaf, and correspondingly a genuine weakening of
Leaf 1b (`Kakeya.WangZahl.cappedBalancedBroadCover_of_refined`). -/

/-- **The `θ`-cap condition is not vacuous, and is not implied by broadness.**

At `x = 0` both shadings of `crossedBallFamily` contain `x`, and the two
directions are the orthogonal axis vectors `e₀`, `e₁`.  A unit vector `v`
within chordal distance `θ` of `±e₀` and of `±e₁` would put two signed axis
vectors within `2θ` of each other, whereas `one_le_norm_sub_signed` bounds that
distance below by `1`; hence `θ ≥ 1/2`. -/
theorem not_isCapConcentrated_crossedBallFamily {δ θ : NNReal} (hθ : (θ : ℝ) < 1 / 2) :
    ¬ IsCapConcentrated (Finset.univ : Finset (ULift.{u} (Fin 2)))
        (crossedBallFamily.{u} δ) θ := by
  classical
  intro H
  obtain ⟨v, hv, hcap⟩ := H (0 : Space3)
  have hx0 : (0 : Space3) ∈ closedBall (0 : Space3) (δ : ℝ) := by
    simp [Metric.mem_closedBall]
  have h0 := hcap (ULift.up 0) (Finset.mem_univ _) hx0
  have h1 := hcap (ULift.up 1) (Finset.mem_univ _) hx0
  rw [show ((crossedBallFamily.{u} δ) (ULift.up 0)).toTube.direction
      = EuclideanSpace.single (0 : Fin 3) (1 : ℝ) by
    simpa [crossedBallFamily] using direction_axisTube (δ := δ) (0 : Fin 3)] at h0
  rw [show ((crossedBallFamily.{u} δ) (ULift.up 1)).toTube.direction
      = EuclideanSpace.single (1 : Fin 3) (1 : ℝ) by
    simpa [crossedBallFamily] using direction_axisTube (δ := δ) (1 : Fin 3)] at h1
  obtain ⟨σ, hσ, hσle⟩ :
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        ‖v - σ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ ≤ (θ : ℝ) := by
    rcases min_le_iff.mp h0 with h | h
    · exact ⟨1, Or.inl rfl, by simpa using h⟩
    · exact ⟨-1, Or.inr rfl, by simpa [sub_neg_eq_add] using h⟩
  obtain ⟨τ, hτ, hτle⟩ :
      ∃ τ : ℝ, (τ = 1 ∨ τ = -1) ∧
        ‖v - τ • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)‖ ≤ (θ : ℝ) := by
    rcases min_le_iff.mp h1 with h | h
    · exact ⟨1, Or.inl rfl, by simpa using h⟩
    · exact ⟨-1, Or.inr rfl, by simpa [sub_neg_eq_add] using h⟩
  have hkey : (1 : ℝ) ≤ ‖σ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
      - τ • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)‖ := one_le_norm_sub_signed hσ hτ
  have htri : ‖σ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
      - τ • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)‖ ≤ (θ : ℝ) + (θ : ℝ) := by
    calc ‖σ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
            - τ • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)‖
        = ‖(σ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) - v)
            + (v - τ • EuclideanSpace.single (1 : Fin 3) (1 : ℝ))‖ := by
          congr 1; abel
      _ ≤ ‖σ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) - v‖
            + ‖v - τ • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)‖ := norm_add_le _ _
      _ ≤ (θ : ℝ) + (θ : ℝ) := by
          refine add_le_add ?_ hτle
          rw [norm_sub_rev]; exact hσle
  linarith


end

end Kakeya.WangZahl
