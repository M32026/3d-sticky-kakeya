/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.AngularMuBridge

/-!
# `hlow` settled: the residue of conjunct 6 is an AXIAL COVERING NUMBER, and it is polynomial

`Kakeya.VeryNotSticky.angularFibre_card_le_fibreMult_of_mu`
(`MainLemma2/AngularMuBridge.lean`) reduces conjunct 6 of
`Kakeya.VeryNotSticky.SideDataObligations` to GWZ's (86) — which the tree already produces —
together with one residue,

`hlow : μ (2 ρ) ≤ C₁ * 𝒱.branchingN k`  (`gwz.txt` l.1993, upper half).

This file settles `hlow` for an **arbitrary exact uniform hierarchy**, and the answer is
**negative with an explicit true form**.

## The proposed route, and where it breaks

The natural route is: the tubes through a point `x` that are pairwise within angle `2ρ_k` all lie
in one common `ρ_{k'}`-tube `V` for a coarser level `k'`; `Tube.UniformTubeSet.boundedOverlap`
then says at most `C` level-`k'` nodes contain a member of `s` lying in `V`; the class brackets
finish. **The first step is false**, and it is false for the reason the whole R18 route exists:
in this formalisation a `Tube` has **unit length**, while the angular cone at `x` has axial
extent `≈ 1` — the members' midpoints are spread along the common direction over an interval of
length `1 + 2δ`, and a unit-length `ρ_{k'}`-tube pins a member's midpoint to within `3ρ_{k'}`
(`Tube.endpoints_close_of_body_le`). `Kakeya.LooseUniform.bush_obstruction` already builds the
witness, and `Kakeya.LooseUniform.exists_bush_forcing_exactCover` below turns it into the sharp
quantitative statement: for **every** dilation factor and every `M`, covering the cone by `M`
exact `ρ`-tubes forces `M ≥ ⌊1/(6ρ)⌋`.

So the correct bookkeeping is not a *product over the levels between `ρ_k` and `K ρ_k`*: at this
tree's grid there are no such levels to speak of — `Tube.sixteen_mul_gridScale_succ_le` gives
`16 ρ_{k+1} ≤ ρ_k`, so **one** grid step already spans a factor `≥ 16`, and in fact
`ρ_{k+1}/ρ_k = δ^{1/N}` with `N = Tube.ssfGridLen δ = ⌈log log (1/δ)⌉`, which is far smaller than
any fixed `K`. The loss is not multi-level branching; it is the **axial covering number** of the
cone, and that is polynomial in `1/ρ_k`, not sub-polynomial.

## What is proved here

* `Kakeya.VeryNotSticky.angularFibre_card_le_of_exactCover` — **the positive half, sharp.**
  If the angular cone at `(x, v)` is covered by `M` exact `ρ_k`-tubes, then it has at most
  `M · C³ · 𝒱.branchingN k` members.  Only `Tube.UniformTubeSet.boundedOverlap` (through
  `Tube.UniformTubeSet.meetingNodes`) and the two Definition-2.2 shade brackets are used; `1 ≤ C`
  is **not** needed.
* `Kakeya.VeryNotSticky.angularFibre_card_le_fibreMult_of_exactCover`,
  `exists_Cang_angularFibre_le_of_exactCover`, `eventually_conjunct6_of_exactCover` — the
  corrected bridge: conjunct 6's conclusion, **verbatim**, with
  `Cang = M · C₀⁵` in place of `Cmu · C₁ · C₀²`.  The constant `C⁵` is the same one
  `Kakeya.LooseUniform.angularCone_card_le_of_loose` (PC) produces in the loose model — with the
  loose `boundedOverlapDil`'s single container replaced by the `M` exact containers.  This route
  does **not** use `μ` at all, so it is independent of (86).
* `Kakeya.LooseUniform.exists_bush_forcing_exactCover` and
  `exists_bush_forcing_exactCover_floor` — **the sharp negative.**  On the bush family the axial
  covering number is `≥ ⌊1/(6ρ)⌋`, so no `M ≤ δ^{-η}` is available at the split level
  `ρ_k ≥ ρ₂*`, and `Kakeya.LooseUniform.not_exists_common_tube_of_bush` kills the single-`V`
  reading outright.

## The residue, stated exactly

Conjunct 6 now has **one** honest sufficient condition in the exact model, and it is

```
∀ x v : EuclideanSpace ℝ (Fin 3),
  ∃ W : Fin M → Tube (Tube.gridScale cfg.δ N k) (EuclideanSpace ℝ (Fin 3)),
    ∀ i ∈ cfg.angularFibre x v ρ, ∃ m,
      (cfg.T i).toConvexSpaceBody ≤ (W m).toConvexSpaceBody
```

with `(M : NNReal) * cfg.C₀ ^ 5 ≤ δ^{-η}`.  It is a statement about **containers**, not about
counting, and the compiled negative says it fails on the bush.  Whether it fails for every
admissible `Kakeya.VeryNotSticky` configuration is **not** decided here — that needs the bush
family to be shown admissible, which is a separate and uncompiled question.  Nothing in this file may be cited as a refutation of conjunct 6.

**Nothing here changes, weakens or restates any existing declaration**, and in particular
`MainLemma2/AngularMuBridge.lean` is untouched: every statement below is new.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

open scoped NNReal ENNReal

namespace Kakeya

namespace VeryNotSticky

universe u

/-! ### The positive half: bounded overlap gives the cone bound, one container at a time -/

open scoped Classical in
/-- **The angular cone, counted through exact containers.**

If every member of the angular cone at `(x, v)` of radius `ρ` lies in one of `M` exact
`ρ_k`-tubes `W m`, then the cone has at most `M · C³ · 𝒱.branchingN k` members.

The proof is GWZ's, with the containers supplied rather than constructed: the nodes the cone
uses lie in `⋃ m, meetingNodes k (W m)`, so there are at most `M · C` of them
(`Tube.UniformTubeSet.card_meetingNodes_le`, i.e. Definition 2.1(ii)); each contributes at most
`C · localN x k ≤ C² · 𝒱.branchingN k` members shading `x`
(`ShadedTube.ShadedUniformTubeSet.card_shadeClass_le` and `le_branchingN`, i.e. Definition 2.2).

`1 ≤ C` is not used. -/
theorem angularFibre_card_le_of_exactCover (cfg : VeryNotSticky.{u}) {N : ℕ} {C : NNReal}
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T N C)
    {k : ℕ} (hk : k ≤ N) {ρ : ℝ} {M : ℕ} (x v : EuclideanSpace ℝ (Fin 3))
    (W : Fin M → Tube (Tube.gridScale cfg.δ N k) (EuclideanSpace ℝ (Fin 3)))
    (hcov : ∀ i ∈ cfg.angularFibre x v ρ, ∃ m,
      (cfg.T i).toConvexSpaceBody ≤ (W m).toConvexSpaceBody) :
    (((cfg.angularFibre x v ρ).card : ℕ) : NNReal) ≤ (M : NNReal) * C ^ 3 * 𝒱.branchingN k := by
  classical
  set 𝒰 := 𝒱.tubeUniform with h𝒰
  set A := cfg.angularFibre x v ρ with hA
  rcases A.eq_empty_or_nonempty with hemp | ⟨i₀, hi₀⟩
  · simp [hemp]
  obtain ⟨hi₀s, hxi₀, -⟩ := Finset.mem_filter.mp hi₀
  have hxU : x ∈ ⋃ i ∈ cfg.s, (cfg.T i).shade := Set.mem_iUnion₂.mpr ⟨i₀, hi₀s, hxi₀⟩
  set J := A.image (𝒰.cover.assign k) with hJ
  have hsub : A ⊆
      J.biUnion (fun j' => ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k) j' x) := by
    intro i hi
    obtain ⟨his, hxi, -⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_biUnion.mpr ⟨𝒰.cover.assign k i, Finset.mem_image_of_mem _ hi, ?_⟩
    simp only [ShadedTube.shadeClass, Finset.mem_filter]
    exact ⟨by simp [Tube.coverClass, his], hxi⟩
  have hJcard : (J.card : NNReal) ≤ (M : NNReal) * C := by
    have hJsub : J ⊆
        (Finset.univ : Finset (Fin M)).biUnion (fun m => 𝒰.meetingNodes k (W m)) := by
      intro j' hj'
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
      obtain ⟨his, -, -⟩ := Finset.mem_filter.mp hi
      obtain ⟨m, hm⟩ := hcov i hi
      refine Finset.mem_biUnion.mpr ⟨m, Finset.mem_univ m, ?_⟩
      simp only [Tube.UniformTubeSet.meetingNodes, Finset.mem_filter]
      exact ⟨𝒰.cover.assign_mem k hk i his, i, his, 𝒰.cover.le_tube_assign k hk i his, hm⟩
    calc (J.card : NNReal)
        ≤ ((((Finset.univ : Finset (Fin M)).biUnion
              (fun m => 𝒰.meetingNodes k (W m))).card : ℕ) : NNReal) := by
          exact_mod_cast Finset.card_le_card hJsub
      _ ≤ ((∑ m : Fin M, (𝒰.meetingNodes k (W m)).card : ℕ) : NNReal) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ m : Fin M, ((𝒰.meetingNodes k (W m)).card : NNReal) := by push_cast; rfl
      _ ≤ ∑ _m : Fin M, C := Finset.sum_le_sum (fun m _ => 𝒰.card_meetingNodes_le hk (W m))
      _ = (M : NNReal) * C := by simp [Finset.sum_const, nsmul_eq_mul]
  have hterm : ∀ j' ∈ J,
      ((ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k) j' x).card : NNReal)
        ≤ C * (C * 𝒱.branchingN k) := by
    intro j' hj'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
    obtain ⟨his, hxi, -⟩ := Finset.mem_filter.mp hi
    calc ((ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k)
            (𝒰.cover.assign k i) x).card : NNReal)
        ≤ C * 𝒱.localN x k := 𝒱.card_shadeClass_le x hxU k hk i his hxi
      _ ≤ C * (C * 𝒱.branchingN k) := by gcongr; exact 𝒱.le_branchingN x hxU k hk
  calc ((A.card : ℕ) : NNReal)
      ≤ (((J.biUnion (fun j' =>
            ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k) j' x)).card : ℕ) : NNReal) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((∑ j' ∈ J,
          (ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k) j' x).card : ℕ) : NNReal) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ j' ∈ J,
          ((ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k) j' x).card : NNReal) := by
        push_cast; rfl
    _ ≤ ∑ _j' ∈ J, C * (C * 𝒱.branchingN k) := Finset.sum_le_sum hterm
    _ = (J.card : NNReal) * (C * (C * 𝒱.branchingN k)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((M : NNReal) * C) * (C * (C * 𝒱.branchingN k)) := by gcongr
    _ = (M : NNReal) * C ^ 3 * 𝒱.branchingN k := by ring

/-! ### The corrected bridge to conjunct 6 -/

open scoped Classical in
/-- **Conjunct 6's inequality from an exact axial cover**, at `Cang = M · C⁵`.

`Kakeya.VeryNotSticky.angularFibre_card_le_of_exactCover` gives `M · C³ · 𝒱.branchingN k`, and
`Kakeya.VeryNotSticky.branchingN_le_multiplicity_of_shadedUniform` (`AngularMuBridge.lean`)
converts the branching number into the multiplicity of an active class at the cost of `C²`.
The constant `C⁵` is exactly the one `Kakeya.LooseUniform.angularCone_card_le_of_loose` gets in
the loose model; the whole difference between the two models is the factor `M`, which the loose
`boundedOverlapDil` sets to `1` and which the exact model cannot. -/
theorem angularFibre_card_le_fibreMult_of_exactCover (cfg : VeryNotSticky.{u}) {N : ℕ} {C : NNReal}
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T N C) (hC : 1 ≤ C)
    {k : ℕ} (hk : k ≤ N) {ρ : ℝ} {M : ℕ} (x v : EuclideanSpace ℝ (Fin 3))
    (W : Fin M → Tube (Tube.gridScale cfg.δ N k) (EuclideanSpace ℝ (Fin 3)))
    (hcov : ∀ i ∈ cfg.angularFibre x v ρ, ∃ m,
      (cfg.T i).toConvexSpaceBody ≤ (W m).toConvexSpaceBody)
    {j : cfg.ι} (hj : j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k) :
    (((cfg.angularFibre x v ρ).card : ℕ) : ENNReal) ≤
      (((M : NNReal) * C ^ 5 : NNReal) : ENNReal) *
        ShadedBody.multiplicity (cfg.tubeFibre 𝒱.tubeUniform k j)
          (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  have h1 := cfg.angularFibre_card_le_of_exactCover 𝒱 hk x v W hcov
  have h2 : (((cfg.angularFibre x v ρ).card : ℕ) : ENNReal) ≤
      (((M : NNReal) * C ^ 3 : NNReal) : ENNReal) * ((𝒱.branchingN k : NNReal) : ENNReal) := by
    have := ENNReal.coe_le_coe.mpr h1
    simpa [ENNReal.coe_mul] using this
  calc (((cfg.angularFibre x v ρ).card : ℕ) : ENNReal)
      ≤ (((M : NNReal) * C ^ 3 : NNReal) : ENNReal) * ((𝒱.branchingN k : NNReal) : ENNReal) := h2
    _ ≤ (((M : NNReal) * C ^ 3 : NNReal) : ENNReal) * ((C : ENNReal) ^ 2 *
          ShadedBody.multiplicity (cfg.tubeFibre 𝒱.tubeUniform k j)
            (fun i ↦ (cfg.T i).toShadedBody)) := by
        gcongr
        exact cfg.branchingN_le_multiplicity_of_shadedUniform 𝒱 hC hk hj
    _ = (((M : NNReal) * C ^ 5 : NNReal) : ENNReal) *
          ShadedBody.multiplicity (cfg.tubeFibre 𝒱.tubeUniform k j)
            (fun i ↦ (cfg.T i).toShadedBody) := by push_cast; ring

open scoped Classical in
/-- **Conjunct 6's `∃ Cang` clause from the axial cover**, at the configuration's own
Definition-2.2 datum.  `hbud` is the budget `M · C₀⁵ ≤ δ^{-η}`; the compiled negative
`Kakeya.LooseUniform.exists_bush_forcing_exactCover_floor` says `M ≥ ⌊1/(6ρ_k)⌋` on the bush, so
`hbud` is where this route stands or falls. -/
theorem exists_Cang_angularFibre_le_of_exactCover (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    {k M : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hcov : ∀ x v : EuclideanSpace ℝ (Fin 3),
      ∃ W : Fin M → Tube (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
        (EuclideanSpace ℝ (Fin 3)),
        ∀ i ∈ cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ), ∃ m,
          (cfg.T i).toConvexSpaceBody ≤ (W m).toConvexSpaceBody)
    (hbud : (((M : NNReal) * cfg.C₀ ^ 5 : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η)) :
    ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
      ∀ j ∈ cfg.activeTubeNodes cfg.splitHierarchy k,
        ∀ x v : EuclideanSpace ℝ (Fin 3),
          (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
            (Cang : ENNReal) *
              ShadedBody.multiplicity (cfg.tubeFibre cfg.splitHierarchy k j)
                (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  refine ⟨(M : NNReal) * cfg.C₀ ^ 5, hbud, ?_⟩
  intro j hj x v
  obtain ⟨W, hW⟩ := hcov x v
  exact cfg.angularFibre_card_le_fibreMult_of_exactCover cfg.uniform.some cfg.hC₀ hk x v W hW hj

open scoped Classical in
/-- **Conjunct 6 of `Kakeya.VeryNotSticky.SideDataObligations`, verbatim**, from the axial-cover
residue alone — no `μ`, no (86), no loose hierarchy.  Compare
`Kakeya.VeryNotSticky.eventually_conjunct6_of_angularMultiplicity` (the `μ` route) and
`Kakeya.VeryNotSticky.eventually_conjunct6_of_looseUniform` (the loose route): all three reach
the same clause, and this one has the smallest hypothesis — a covering statement about
containers.  The `∀ᶠ` is vacuous, as in the other two. -/
theorem eventually_conjunct6_of_exactCover {exscal ϱ η : ℝ} (C₀bd : NNReal) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = d → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      ∀ (M : ℕ),
        (((M : NNReal) * cfg.C₀ ^ 5 : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) →
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        (∀ x v : EuclideanSpace ℝ (Fin 3),
          ∃ W : Fin M → Tube (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
            (EuclideanSpace ℝ (Fin 3)),
            ∀ i ∈ cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ), ∃ m,
              (cfg.T i).toConvexSpaceBody ≤ (W m).toConvexSpaceBody) →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
          ∀ j ∈ cfg.activeTubeNodes cfg.splitHierarchy k,
            ∀ x v : EuclideanSpace ℝ (Fin 3),
              (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
                (Cang : ENNReal) *
                  ShadedBody.multiplicity (cfg.tubeFibre cfg.splitHierarchy k j)
                    (fun i ↦ (cfg.T i).toShadedBody) :=
  Filter.Eventually.of_forall fun _ cfg bd _ _ _ _ _ _ _ hbud _ hk hcov _ _ ↦
    cfg.exists_Cang_angularFibre_le_of_exactCover bd hk hcov hbud

/-! ### The unconditional route: `maxDensity_le` caps the cone outright

The residue above is a covering statement, and the compiled negatives say it is not payable.  But
conjunct 6's left-hand side has a second, hierarchy-free ceiling that costs nothing: GWZ's
Katz-Tao density field `Kakeya.VeryNotSticky.maxDensity_le`.  Every member of the angular cone at
`(x, v)` of radius `ρ` lies in the `4`-dilate of a single `ρ`-tube through `x`
(`Kakeya.LooseUniform.le_dilate_of_through_point`), a body of volume `≍ ρ²`, so the cone has at
most `Δ_max · |4·V| / (c₃ δ²) ≍ δ^{-η} (ρ/δ)²` members.  Since an *active* class has multiplicity
at least `1` (`Kakeya.VeryNotSticky.one_le_multiplicity_tubeFibre`), that alone gives conjunct 6's
inequality — for **every** configuration and **every** hierarchy, with no `μ`, no cover and no
loose datum.

The price is the constant: `Cang ≍ δ^{-η} (ρ₂*/δ)²`, and `ρ₂*/δ = 2⁷ C₀⁴ / r₁` in the degenerate
regime `b = δ`.  This is what decides conjunct 6: the clause is **true**, and only its budget
`Cang ≤ δ^{-η}` is not.
-/

open scoped Classical in
theorem card_angularFibre_mul_le (cfg : VeryNotSticky.{u}) {ρ : NNReal} (hρ1 : ρ ≤ 1)
    (hδρ : 4 * (cfg.δ : ℝ) ≤ (ρ : ℝ)) (x v : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ = 1) :
    (((cfg.angularFibre x v (ρ : ℝ)).card : ℕ) : ENNReal) *
        ((Tube.le_volume.c 3 : ENNReal) * (cfg.δ : ENNReal) ^ 2)
      ≤ (cfg.δ : ENNReal) ^ (-cfg.η) *
          ((64 : ENNReal) * (Tube.volume_le.C 3 : ENNReal) * (ρ : ENNReal) ^ 2) := by
  classical
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hδ0 : (0 : ℝ) < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
  have hρ0 : (0 : NNReal) < ρ := by
    have : (0 : ℝ) < (ρ : ℝ) := by linarith
    exact_mod_cast this
  set V : Tube ρ (EuclideanSpace ℝ (Fin 3)) := LooseUniform.bushTube ρ x v hv 0 with hV
  set K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := Kakeya.Tube.dilate V 4 with hK
  set t := cfg.angularFibre x v (ρ : ℝ) with ht
  have hts : t ⊆ cfg.s := fun i hi => (Finset.mem_filter.mp hi).1
  have hVc : V.center = x := by
    have : V.center = midpoint ℝ (x + ((0 : ℝ) - 1 / 2) • v) (x + ((0 : ℝ) + 1 / 2) • v) := rfl
    rw [this, midpoint_eq_smul_add, invOf_eq_inv]; module
  -- every member of the cone lies in the `4`-dilate of `V`
  have hcont : ∀ i ∈ t, (cfg.T i).toConvexSpaceBody ≤ K := by
    intro i hi
    obtain ⟨his, hxi, hang⟩ := Finset.mem_filter.mp hi
    have hVd : V.direction = v := LooseUniform.bushTube_direction ρ x v hv 0
    have hw : ‖V.direction‖ = 1 := by rw [hVd]; exact hv
    have hang' : NonSlab.lineAngle (cfg.T i).direction V.direction ≤ (ρ : ℝ) := by
      rw [hVd]; exact hang
    obtain ⟨σ, hσ, hnorm⟩ := LooseUniform.exists_sign_norm_sub_le_of_lineAngle_le
      (Tube.norm_direction (cfg.T i).toTube) hw hang'
    refine LooseUniform.le_dilate_of_through_point V (K' := 4) (r := 0) (θ := (ρ : ℝ))
      (by norm_num) (s₀ := 0) (by norm_num) ?_ (cfg.T i).toTube ((cfg.T i).shade_subset hxi)
      hσ hnorm (by linarith)
    rw [hVc, zero_smul, add_zero, dist_self]
  -- volume of the container
  have hVvol : volume V.carrier
      ≤ ((Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2 := by
    have := Tube.volume_le hρ1 V
    rw [hfr] at this
    calc volume V.carrier
        ≤ (((Tube.volume_le.C 3 * ρ ^ (3 - 1) : NNReal)) : ENNReal) := this
      _ = ((Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2 := by push_cast; ring
  have hKvol : volume K.carrier
      ≤ (64 : ENNReal) * ((Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2 := by
    have hdil := Tube.tubeDilateVolume (E := EuclideanSpace ℝ (Fin 3)) V (C := 4) (by norm_num)
    rw [hfr] at hdil
    have h64 : ENNReal.ofReal (Tube.tubeDilateVolume.C' 3 4) = (64 : ENNReal) := by
      unfold Tube.tubeDilateVolume.C'
      rw [show ((4 : ℝ) ^ 3) = 64 by norm_num]
      simp [ENNReal.ofReal_ofNat]
    rw [hK, hdil, h64]
    calc (64 : ENNReal) * volume V.carrier
        ≤ (64 : ENNReal) * (((Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2) := by
          gcongr
      _ = (64 : ENNReal) * ((Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2 := by ring
  have hKvol_ne_top : volume K.carrier ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hKvol
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hKvol_ne_zero : volume K.carrier ≠ 0 := by
    have hsub : V.carrier ⊆ K.carrier := by
      rw [hK]; exact fun z hz => Tube.subset_dilate V (by norm_num) hz
    have hlow := Tube.le_volume (E := EuclideanSpace ℝ (Fin 3)) V
    rw [hfr] at hlow
    have hpos : ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ (3 - 1) ≠ 0 := by
      refine mul_ne_zero (by exact_mod_cast (Tube.le_volume.c_pos 3).ne') ?_
      exact pow_ne_zero _ (by exact_mod_cast hρ0.ne')
    exact fun h0 => hpos (le_antisymm (by
      calc ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ (3 - 1)
          ≤ volume V.carrier := hlow
        _ ≤ volume K.carrier := measure_mono hsub
        _ = 0 := h0) bot_le)
  -- the density bound
  have hdens : (∑ i ∈ t, volume (cfg.T i).carrier)
      ≤ (cfg.δ : ENNReal) ^ (-cfg.η) * volume K.carrier := by
    have h1 : (∑ i ∈ t, volume (cfg.T i).carrier)
        ≤ ∑ i ∈ {i ∈ cfg.s | (fun i => (cfg.T i).toConvexSpaceBody) i ≤ K},
            volume ((fun i => (cfg.T i).toConvexSpaceBody) i).carrier := by
      refine Finset.sum_le_sum_of_subset ?_
      intro i hi
      exact Finset.mem_filter.mpr ⟨hts hi, hcont i hi⟩
    have h2 : densityIn cfg.s (fun i => (cfg.T i).toConvexSpaceBody) K
        ≤ (cfg.δ : ENNReal) ^ (-cfg.η) :=
      le_trans (le_maxDensity cfg.s (fun i => (cfg.T i).toConvexSpaceBody) K) cfg.maxDensity_le
    rw [densityIn, ENNReal.div_le_iff_le_mul (Or.inl hKvol_ne_zero) (Or.inl hKvol_ne_top)] at h2
    exact le_trans h1 h2
  -- the volume lower bound, summed
  have hlow : ((t.card : ℕ) : ENNReal) * ((Tube.le_volume.c 3 : ENNReal) * (cfg.δ : ENNReal) ^ 2)
      ≤ ∑ i ∈ t, volume (cfg.T i).carrier := by
    have hpt : ∀ i ∈ t, ((Tube.le_volume.c 3 : ENNReal) * (cfg.δ : ENNReal) ^ 2)
        ≤ volume (cfg.T i).carrier := by
      intro i _
      have := Tube.le_volume (E := EuclideanSpace ℝ (Fin 3)) (cfg.T i).toTube
      rw [hfr] at this
      calc ((Tube.le_volume.c 3 : ENNReal) * (cfg.δ : ENNReal) ^ 2)
          = ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ (3 - 1) := by norm_num
        _ ≤ volume (cfg.T i).carrier := this
    calc ((t.card : ℕ) : ENNReal) * ((Tube.le_volume.c 3 : ENNReal) * (cfg.δ : ENNReal) ^ 2)
        = ∑ _i ∈ t, ((Tube.le_volume.c 3 : ENNReal) * (cfg.δ : ENNReal) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ t, volume (cfg.T i).carrier := Finset.sum_le_sum hpt
  calc ((t.card : ℕ) : ENNReal) * ((Tube.le_volume.c 3 : ENNReal) * (cfg.δ : ENNReal) ^ 2)
      ≤ ∑ i ∈ t, volume (cfg.T i).carrier := hlow
    _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) * volume K.carrier := hdens
    _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) *
          ((64 : ENNReal) * ((Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2) := by
        gcongr

open scoped Classical in
/-- **The cone cap at an arbitrary direction.**  `Kakeya.VeryNotSticky.angularInnerCount` puts the
fibre at an arbitrary `v` inside the fibre at a *tube* through `x`, at the doubled angle; the
direction of a tube is a unit vector, which is what
`Kakeya.VeryNotSticky.card_angularFibre_mul_le` needs.  Conjunct 6 quantifies over all `v`, unit
or not, so this step is not cosmetic. -/
theorem card_angularFibre_mul_le_of_any_dir (cfg : VeryNotSticky.{u}) {ρ : NNReal}
    (h2ρ1 : 2 * ρ ≤ 1) (hδρ : 4 * (cfg.δ : ℝ) ≤ (ρ : ℝ)) (x v : EuclideanSpace ℝ (Fin 3)) :
    (((cfg.angularFibre x v (ρ : ℝ)).card : ℕ) : ENNReal) *
        ((Tube.le_volume.c 3 : ENNReal) * (cfg.δ : ENNReal) ^ 2)
      ≤ (cfg.δ : ENNReal) ^ (-cfg.η) *
          ((64 : ENNReal) * (Tube.volume_le.C 3 : ENNReal) * ((2 * ρ : NNReal) : ENNReal) ^ 2) := by
  classical
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
  rcases cfg.angularInnerCount x v hρ0 with hemp | ⟨i₀, hi₀s, hxi₀, hsub⟩
  · rw [hemp]; simp
  have hcard : ((cfg.angularFibre x v (ρ : ℝ)).card : ℕ)
      ≤ ((cfg.angularFibre x (cfg.T i₀).direction (2 * (ρ : ℝ))).card : ℕ) :=
    Finset.card_le_card hsub
  have hcast : ((2 * ρ : NNReal) : ℝ) = 2 * (ρ : ℝ) := by push_cast; ring
  have hstep := cfg.card_angularFibre_mul_le (ρ := 2 * ρ) h2ρ1 (by rw [hcast]; linarith) x
    (cfg.T i₀).direction (Tube.norm_direction (cfg.T i₀).toTube)
  rw [hcast] at hstep
  refine le_trans (mul_le_mul_left ?_ _) hstep
  exact_mod_cast hcard

open scoped Classical in
/-- **Conjunct 6's `∃ Cang` clause, unconditionally, at the density-forced constant.**

No hypothesis beyond the configuration itself and the two angular side conditions.  The constant
is `Cang = δ^{-η} · 64 · C₃ · (2ρ₂*)² / (c₃ · δ²)`, i.e. `≍ δ^{-η} (ρ₂*/δ)²`, and it is returned
in closed form so that the exponent can be read off.  Conjunct 6 as existing asks for
`Cang ≤ δ^{-η}`; this route gives `δ^{-η}(ρ₂*/δ)²`, and `ρ₂*/δ = 2⁷C₀⁴/r₁` in the degenerate
regime.  So conjunct 6 is true and its **budget** is what needs re-cutting. -/
theorem exists_Cang_angularFibre_le_of_maxDensity (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (h2ρ1 : 2 * cfg.rho2Star bd.C₀ ≤ 1) (k : ℕ) :
    ∃ Cang : NNReal,
      Cang = cfg.δ ^ (-cfg.η) * (64 * Tube.volume_le.C 3 * (2 * cfg.rho2Star bd.C₀) ^ 2) /
          (Tube.le_volume.c 3 * cfg.δ ^ 2) ∧
      ∀ j ∈ cfg.activeTubeNodes cfg.splitHierarchy k,
        ∀ x v : EuclideanSpace ℝ (Fin 3),
          (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
            (Cang : ENNReal) *
              ShadedBody.multiplicity (cfg.tubeFibre cfg.splitHierarchy k j)
                (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  set ρ : NNReal := cfg.rho2Star bd.C₀ with hρ
  set b : NNReal := Tube.le_volume.c 3 * cfg.δ ^ 2 with hb
  set D : NNReal := cfg.δ ^ (-cfg.η) * (64 * Tube.volume_le.C 3 * (2 * ρ) ^ 2) with hD
  have hδne : (cfg.δ : NNReal) ≠ 0 := cfg.hδ.ne'
  have hbne : b ≠ 0 := by
    refine mul_ne_zero (Tube.le_volume.c_pos 3).ne' (pow_ne_zero _ hδne)
  have hbE : (b : ENNReal) = (Tube.le_volume.c 3 : ENNReal) * (cfg.δ : ENNReal) ^ 2 := by
    rw [hb]; push_cast; ring
  have hDE : (D : ENNReal) = (cfg.δ : ENNReal) ^ (-cfg.η) *
      ((64 : ENNReal) * (Tube.volume_le.C 3 : ENNReal) * ((2 * ρ : NNReal) : ENNReal) ^ 2) := by
    rw [hD, ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδne]
    push_cast
    ring
  have hδρ : 4 * (cfg.δ : ℝ) ≤ (ρ : ℝ) := cfg.four_mul_delta_le_rho2Star bd.hC₀
  refine ⟨D / b, rfl, ?_⟩
  intro j hj x v
  have hmain := cfg.card_angularFibre_mul_le_of_any_dir (ρ := ρ) h2ρ1 hδρ x v
  rw [← hbE, ← hDE] at hmain
  have hdiv : (((cfg.angularFibre x v (ρ : ℝ)).card : ℕ) : ENNReal)
      ≤ (D : ENNReal) / (b : ENNReal) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hbne)) (Or.inl ENNReal.coe_ne_top)]
    exact hmain
  have hcoe : ((D / b : NNReal) : ENNReal) = (D : ENNReal) / (b : ENNReal) :=
    ENNReal.coe_div hbne
  calc (((cfg.angularFibre x v (ρ : ℝ)).card : ℕ) : ENNReal)
      ≤ (D : ENNReal) / (b : ENNReal) := hdiv
    _ = ((D / b : NNReal) : ENNReal) := hcoe.symm
    _ = ((D / b : NNReal) : ENNReal) * 1 := (mul_one _).symm
    _ ≤ ((D / b : NNReal) : ENNReal) *
          ShadedBody.multiplicity (cfg.tubeFibre cfg.splitHierarchy k j)
            (fun i ↦ (cfg.T i).toShadedBody) := by
        gcongr
        exact cfg.one_le_multiplicity_tubeFibre cfg.splitHierarchy hj

open scoped Classical in
/-- Everything but the budget clause is byte-identical to the existing conjunct; the only change is
`(Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η)` becoming `… ^ (-α)`.  The hypothesis `hbud`
names the honest constant in closed form: `δ^{-η} · 64 · C₃ · (2ρ₂*)² / (c₃ δ²)`.  Because
`ρ₂*/δ = 2⁷C₀⁴/r₁` in the degenerate regime `b = δ`, `α = 2·exscal + 3η` suffices once `r₁ =
δ^{exscal}` and the absolute constants are absorbed — the arithmetic is left to the caller so
that no threshold is hidden here.

There is **no residual obligation**: `hbud` is a statement about numerals and the configuration's
own parameters, not about the family. -/
theorem eventually_conjunct6_of_maxDensity {exscal ϱ η α : ℝ} (C₀bd : NNReal) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = d → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      2 * cfg.rho2Star bd.C₀ ≤ 1 →
      ((cfg.δ ^ (-cfg.η) * (64 * Tube.volume_le.C 3 * (2 * cfg.rho2Star bd.C₀) ^ 2) /
          (Tube.le_volume.c 3 * cfg.δ ^ 2) : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-α) →
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-α) ∧
          ∀ j ∈ cfg.activeTubeNodes cfg.splitHierarchy k,
            ∀ x v : EuclideanSpace ℝ (Fin 3),
              (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
                (Cang : ENNReal) *
                  ShadedBody.multiplicity (cfg.tubeFibre cfg.splitHierarchy k j)
                    (fun i ↦ (cfg.T i).toShadedBody) := by
  refine Filter.Eventually.of_forall ?_
  intro _ cfg bd _ _ _ _ _ _ h2ρ hbud k _ _ _
  obtain ⟨Cang, hCeq, hCang⟩ := cfg.exists_Cang_angularFibre_le_of_maxDensity bd h2ρ k
  exact ⟨Cang, by rw [hCeq]; exact hbud, hCang⟩

end VeryNotSticky

namespace LooseUniform

/-! ### The sharp negative: the axial covering number is polynomial -/

/-- **The bush forces the axial covering number.**  The `n` unit `δ`-tubes of
`Kakeya.LooseUniform.bush_obstruction` all pass through `x` and share a direction — so they lie
in **every** angular cone at `x` — and are pairwise contained in no common exact `ρ`-tube.  Hence
any family of exact `ρ`-tubes covering them has at least `n` members: the choice function
`i ↦ (an index whose tube contains `T i`)` is injective. -/
theorem exists_bush_forcing_exactCover {δ ρ : NNReal} (hδρ : 4 * (δ : ℝ) ≤ ρ)
    (x v : E3) (hv : ‖v‖ = 1) (n : ℕ) {sp : ℝ}
    (hsp : 2 * (ρ : ℝ) < sp) (hn : (n : ℝ) * sp ≤ 1 / 2) :
    ∃ T : Fin n → Tube δ E3,
      (∀ i, x ∈ (T i).carrier) ∧
      (∀ i j, (T i).direction = (T j).direction) ∧
      ∀ (M : ℕ) (W : Fin M → Tube ρ E3),
        (∀ i, ∃ m, (T i).toConvexSpaceBody ≤ (W m).toConvexSpaceBody) → n ≤ M := by
  classical
  obtain ⟨T, V, hx, hdir, hpair, -⟩ := bush_obstruction hδρ x v hv n hsp hn
  refine ⟨T, hx, fun i j => by rw [hdir i, hdir j], ?_⟩
  intro M W hcov
  choose f hf using hcov
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact hpair i j hne ⟨W (f i), hf i, by rw [hij]; exact hf j⟩
  simpa using Fintype.card_le_of_injective f hinj

/-- **The axial covering number is at least `⌊1/(6ρ)⌋`.**  `sp := 3ρ` in
`Kakeya.LooseUniform.exists_bush_forcing_exactCover`.  At the split level, where
`ρ ≥ ρ₂* ≥ 4δ` is a *power* of `δ`, this is polynomially larger than any `δ^{-η}`, so the
residue of `Kakeya.VeryNotSticky.exists_Cang_angularFibre_le_of_exactCover` is not payable from
the budget on this family. -/
theorem exists_bush_forcing_exactCover_floor {δ ρ : NNReal} (hρ : 0 < (ρ : ℝ))
    (hδρ : 4 * (δ : ℝ) ≤ ρ) (x v : E3) (hv : ‖v‖ = 1) :
    ∃ T : Fin ⌊1 / (6 * (ρ : ℝ))⌋₊ → Tube δ E3,
      (∀ i, x ∈ (T i).carrier) ∧
      (∀ i j, (T i).direction = (T j).direction) ∧
      ∀ (M : ℕ) (W : Fin M → Tube ρ E3),
        (∀ i, ∃ m, (T i).toConvexSpaceBody ≤ (W m).toConvexSpaceBody) →
        ⌊1 / (6 * (ρ : ℝ))⌋₊ ≤ M := by
  refine exists_bush_forcing_exactCover hδρ x v hv _ (sp := 3 * (ρ : ℝ)) (by linarith) ?_
  have hfl : ((⌊1 / (6 * (ρ : ℝ))⌋₊ : ℕ) : ℝ) ≤ 1 / (6 * (ρ : ℝ)) :=
    Nat.floor_le (by positivity)
  have h6 : (0 : ℝ) < 6 * (ρ : ℝ) := by linarith
  calc ((⌊1 / (6 * (ρ : ℝ))⌋₊ : ℕ) : ℝ) * (3 * (ρ : ℝ))
      ≤ (1 / (6 * (ρ : ℝ))) * (3 * (ρ : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hfl (by linarith)
    _ = 1 / 2 := by field_simp; ring

/-- **The single-container reading is false.**  Two distinct bush tubes already lie in no common
exact `ρ`-tube, so "the angular cone lies in one common `ρ`-tube" fails as soon as
`2 ≤ ⌊1/(6ρ)⌋`, i.e. for every `ρ ≤ 1/12`. -/
theorem not_exists_common_tube_of_bush {δ ρ : NNReal} (hρ : 0 < (ρ : ℝ))
    (hρ12 : (ρ : ℝ) ≤ 1 / 12) (hδρ : 4 * (δ : ℝ) ≤ ρ) (x v : E3) (hv : ‖v‖ = 1) :
    ∃ T : Fin ⌊1 / (6 * (ρ : ℝ))⌋₊ → Tube δ E3,
      (∀ i, x ∈ (T i).carrier) ∧
      (∀ i j, (T i).direction = (T j).direction) ∧
      ¬ ∃ W : Tube ρ E3, ∀ i, (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody := by
  obtain ⟨T, hx, hdir, hM⟩ := exists_bush_forcing_exactCover_floor hρ hδρ x v hv
  refine ⟨T, hx, hdir, ?_⟩
  rintro ⟨W, hW⟩
  have h2 : 2 ≤ ⌊1 / (6 * (ρ : ℝ))⌋₊ := by
    have : (2 : ℝ) ≤ 1 / (6 * (ρ : ℝ)) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    exact_mod_cast Nat.le_floor (by exact_mod_cast this)
  have := hM 1 (fun _ => W) (fun i => ⟨0, hW i⟩)
  omega

end LooseUniform

end Kakeya
