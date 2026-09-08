/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.AngularMuHierarchy
public import Kakeya.Tube.Rescale

/-!
# Conjunct 6 from GWZ Definition 2.1(ii): the covering number `M` is a dimensional constant
once the parents are **essentially distinct**

`Kakeya.VeryNotSticky.angularFibre_card_le_of_exactCover`
(`MainLemma2/AngularMuHierarchy.lean`) bounds the angular cone by `M · C³ · branchingN k`,
where `M` is the number of exact `ρ_k`-containers the cone needs, and
`Kakeya.LooseUniform.exists_bush_forcing_exactCover_floor` shows `M ≥ ⌊1/(6ρ_k)⌋` if the
containers are supplied as an arbitrary cover.  That is the whole residue of conjunct 6, and
 left it there.

This file settles it: **`M` is bounded by a dimensional constant as soon as the level-`k`
*nodes* are pairwise essentially distinct**, which is GWZ Definition 2.1(ii) verbatim
(`gwz.txt` l.181-182: "The tubes `𝕋_ρ` are essentially distinct.  Therefore each `T ∈ 𝕋` lies in
`T_ρ` for `∼1` choice of `T_ρ`") — the clause `Tube.UniformTubeSet` replaced by
`boundedOverlap`.  The count is the existing
`Tube.essDistinctTubesInSelfDilate`, and the geometry that feeds it is the existing
`Kakeya.LooseUniform.le_dilate_of_through_point`.

## The chain

* `exists_sign_norm_direction_sub_le_of_body_le` — exact containment of one unit-length tube in
  another pins their directions to `6 s`, up to sign (from `Tube.endpoints_close_of_body_le`).
* `tube_le_dilate_of_mem_angularFibre` — **the keystone geometry.**  *Any* `σ`-tube (`ρ ≤ σ`)
  containing a member of the angular cone at `(x, v)` of radius `ρ` lies in the `10`-dilate of the
  *single* `σ`-tube centred at `x` in the direction of a fixed cone member.  The cone's **members**
  lie in no common `σ`-tube (`Kakeya.LooseUniform.not_exists_common_tube_of_bush`); the `σ`-tubes
  that **contain** them do lie in one bounded dilate, and that is the asymmetry the exact-cover
  route missed.  No hierarchy is mentioned.
* `card_le_essDistinctConstant_of_edFamily` — **the keystone count**, on an arbitrary pairwise
  essentially distinct family: `M ≤ C_ED(3, 10) := Tube.essDistinctTubesInSelfDilate.C 3 10`, a
  dimensional constant, no `δ`.  Per  the datum belongs on **the family the
  consumer dilates**, so the family is a parameter;
  `card_filter_meets_angularFibre_le_of_essDistinct` is the same statement in the shape
  `Kakeya.VeryNotSticky.RhoParentData`'s fifth conjunct carries,
  and `card_image_assign_angularFibre_le_of_essDistinct` is the specialisation to a hierarchy's
  nodes — recorded, but **not claimed inhabited**:  measures that the existing
  uniformiser's nodes come from `Tube.grid_net_tight`'s `ρ/32`-separated net and are not
  essentially distinct.
* `angularFibre_card_le_of_essDistinct`, `angularFibre_card_le_fibreMult_of_essDistinct` —
  the cone bound at `C_ED · C²·branchingN k` and conjunct 6's inequality at `Cang = C_ED · C⁴`.
* `coe_C₀_pow_four_le_rpow_neg_half_eta` — `C₀⁴ ≤ δ^{-η/2}` (the square root of
  `coe_C₀_pow_eight_le_rpow_neg_eta`, in the pattern of `coe_C₀_sq_le_rpow_neg_quarter_eta`).
* `exists_Cang_angularFibre_le_of_essDistinct`, `eventually_conjunct6_of_essDistinct` —
  **conjunct 6 of `Kakeya.VeryNotSticky.SideDataObligations`, verbatim, with no unpaid budget**:
  `C₀⁴ ≤ δ^{-η/2}` is the configuration's own `aScaleData_absorb` and `C_ED(3,10) ≤ δ^{-η/2}`
  holds below a threshold in `η` alone (`Kakeya.AngularCover.exists_const_threshold`), so the
  product fits the clause's `δ^{-η}` exactly.  **No consumer text moves**: `SplitInputs`,
  `Kakeya.VeryNotSticky.tubeFibre`, `nonslabPointwiseBound`, `nonslabKKTPow` and
  `nonslabSplitBound` are untouched, and neither the refinement `Y′` of `gwz.txt` l.1985-1993
  nor the angular multiplicity `μ(ρ)` is needed.
* `card_le_essDistinctConstant_of_no_common_tube` — **the price, compiled.**  The same
  hypothesis caps at `C_ED(3,10)` the number of cone members that are pairwise in no common
  exact `ρ_k`-tube.  `Kakeya.LooseUniform.bush_obstruction` produces `n ≈ 1/(2ρ_k)` such members
  through a point, and `Kakeya.VeryNotSticky.card_le_of_bush` permits an admissible
  configuration up to `733·δ^{-η}` of them.  So in the **exact**-containment model the
  hypothesis is a strong axial-coherence condition and is *not* free: the parents of an axially
  spread bush are forced to be axial translates at spacing `ρ_k`, and unit-length tubes at
  axial spacing below `1/2` overlap in more than half their volume, i.e. are not essentially
  distinct.  Under GWZ's own reading of "lies in" (`gwz.txt` l.163-166, containment up to an
  absolute-constant dilate) one parent absorbs the whole bush and Definition 2.1(ii) is free —
  which is exactly the model change  proposes.

## The loose port, and why it pays for itself

The last section of this file runs the same two steps in `Kakeya.LooseUniform`'s model, at
`K = 4`, where a member lies in the `K`-dilate of its node rather than in the node.  There
essential distinctness of the nodes proves **two of the three non-data fields** of
`Kakeya.LooseUniform.LooseUniformTubeSet`:

* `boundedOverlapDil` — `Kakeya.LooseUniform.card_filter_le_of_essDistinct`, at
  `Tube.essDistinctTubesInSelfDilate.C 3 130`, in the field's own text;
* `tube_injOn` — `Kakeya.LooseUniform.injOn_of_essDistinct`, since a tube of positive finite
  volume is not essentially distinct from itself.

`Kakeya.LooseUniform.LooseUniformTubeSet.ofEssDistinct` bundles that: a producer of the loose
hierarchy owes a `LooseGridCoverSystem`, a branching function, GWZ Definition 2.1(ii) and GWZ
Definition 2.1(iii) — and nothing else.  So adopting the source's essential-distinctness clause
*removes* producer obligations rather than adding one.  The one new geometric lemma this needs,
`exists_sign_norm_direction_sub_le_of_le_dilate` (direction control from containment in a
dilate), is proved here too: `Tube.endpoints_close_of_body_le` does not cover it, because
`Kakeya.Tube.dilate V c` is a `ConvexSpaceBody` and not a `Tube`.

## The `boundedOverlap`-only route: stated, and refuted at its covering step

Because the essential-distinctness clause is not available on the existing hierarchy, the obvious
alternative is to bound `Q` from `Tube.UniformTubeSet.boundedOverlap` alone.  Both halves are
here, and the route does not close:

* `card_image_assign_angularFibre_le_of_exactCover` — **the positive half**: if the cone's
  *members* are covered by `M` exact `ρ_k`-tubes then `Q ≤ M · C`, from `boundedOverlap` alone.
  `boundedOverlap`'s "some member of `s` lies in both the node and `V`" clause does **not** block:
  the witness is the cone member that put the node in the count.
* `Kakeya.LooseUniform.exists_bush_forcing_dilate_cover` — **the covering step is false**, already
  at the `4`-dilate: no family of exact `σ`-tubes with fewer than `⌊1/(6σ)⌋` members contains
  every unit `δ`-tube through `x` with the common direction lying in `Tube.dilate V 4`.  So `M`
  is not a dimensional constant, and `Q ≤ M·C` is polynomial.
  `Kakeya.LooseUniform.le_dilate_bushTube_of_through_point_dir` records that such tubes really do
  fill the dilate, so the refutation is about the region the route names and not a weaker one.

The obstruction is **length, not radius**: `boundedOverlap`'s container is a `Tube`, of unit
length, so it sees an `O(σ)` axial slice of a cone with axial extent `≈ 1`; a `Tube (2σ)` is no
better.  `Kakeya.LooseUniform.LooseUniformTubeSet.boundedOverlapDil`'s container is a *dilate*, of
length `K`, and one of those holds the whole cone.

## D-b's licence-independent half, and the finding

 relocates GWZ Definition 2.1(ii) onto the family the consumer dilates and notes
that `Kakeya.VeryNotSticky.RhoParentData`'s fifth conjunct already carries one.  The bridge from
such a family to conjunct 6's clause is here — `angularFibre_card_le_of_edCover` and
`angularFibre_le_edFibreMult` — with the missing clauses named as hypotheses, and so is the
measurement that the fifth conjunct supplies **none** of them: it has no assignment, no cover of
`sPar`, no Definition 2.1(iii) class bracket, no Definition 2.2 shading bracket, and its index type
`κ` is existentially quantified, hence not `ι`, so `Tube.GridCoverSystem` cannot express it as a
hierarchy.  **The ED family has no classes**, so its classes cannot serve as the consumers' fibre.

The consumers themselves, by contrast, need **no twins at all**, and that is compiled:
`nonslabPointwiseBound_on_edFamily` and `nonslabKKTPow_on_edFamily` instantiate the two existing
consumers on an arbitrary ED-family fibre without changing a token of their text —
`Kakeya.VeryNotSticky.nonslabPointwiseBound` reads its angular input as an abstract `A : ENNReal`,
and `Kakeya.VeryNotSticky.nonslabKKTPow` reads an arbitrary `sub ⊆ cfg.s` and a *free* node count
`N : ℕ`, whose `hcount` the fifth conjunct discharges verbatim at `Ccnt = 1`.  So the whole residue
of D-b is two clauses on the ED family's fibre: the fullness floor, and GWZ Definition 2.1(iii).

## What this decides, and what it does not

Decided: the residue of conjunct 6 is **one named clause**, essential distinctness of the
level-`k` parents; it is GWZ's own Definition 2.1(ii); it suffices, at a dimensional constant,
with the budget paid; and in the loose model it is cheaper than the fields it replaces.  Not
decided: whether that clause is producible on any hierarchy.  In the exact model the price
theorem says it is not, for any family with an axially spread bush — but that family has never
been exhibited as an admissible `Kakeya.VeryNotSticky`, so nothing here refutes the clause.

**Nothing here changes, weakens or restates any existing declaration**: every statement below is
new, and no protected or pinned text is touched.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

open scoped NNReal ENNReal

namespace Kakeya

namespace VeryNotSticky

open Kakeya.LooseUniform

universe u

theorem exists_sign_norm_direction_sub_le_of_body_le {δ' s : NNReal}
    (A : Tube δ' E3) (B : Tube s E3)
    (hAB : A.toConvexSpaceBody ≤ B.toConvexSpaceBody) :
    ∃ σ : ℝ, |σ| = 1 ∧ ‖A.direction - σ • B.direction‖ ≤ 6 * (s : ℝ) := by
  rcases _root_.Tube.endpoints_close_of_body_le A B hAB with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨1, by norm_num, ?_⟩
    have heq : A.direction - (1 : ℝ) • B.direction = (A.y - B.y) - (A.x - B.x) := by
      simp only [Tube.direction]
      module
    rw [heq]
    calc ‖(A.y - B.y) - (A.x - B.x)‖ ≤ ‖A.y - B.y‖ + ‖A.x - B.x‖ := norm_sub_le _ _
      _ ≤ 3 * (s : ℝ) + 3 * (s : ℝ) := add_le_add h2 h1
      _ = 6 * (s : ℝ) := by ring
  · refine ⟨-1, by norm_num, ?_⟩
    have heq : A.direction - (-1 : ℝ) • B.direction = (A.y - B.x) - (A.x - B.y) := by
      simp only [Tube.direction]
      module
    rw [heq]
    calc ‖(A.y - B.x) - (A.x - B.y)‖ ≤ ‖A.y - B.x‖ + ‖A.x - B.y‖ := norm_sub_le _ _
      _ ≤ 3 * (s : ℝ) + 3 * (s : ℝ) := add_le_add h2 h1
      _ = 6 * (s : ℝ) := by ring

/-- **Direction transfer from a dilate.**  A unit-length `δ`-tube inside the `c`-dilate of a
`ρ`-tube has its direction within `4 c ρ` of the `ρ`-tube's, up to sign.  Unlike
`Tube.endpoints_close_of_body_le` this works for `Kakeya.Tube.dilate`, which is a
`ConvexSpaceBody` and not a `Tube`. -/
theorem exists_sign_norm_direction_sub_le_of_le_dilate {δ ρ : NNReal}
    (T : Tube δ E3) (V : Tube ρ E3) {c : ℝ} (hc : 0 < c)
    (h : T.toConvexSpaceBody ≤ Kakeya.Tube.dilate V c) :
    ∃ σ : ℝ, |σ| = 1 ∧ ‖T.direction - σ • V.direction‖ ≤ 4 * c * (ρ : ℝ) := by
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
  have hVdir : ‖V.direction‖ = 1 := Tube.norm_direction V
  have hTdir : ‖T.direction‖ = 1 := Tube.norm_direction T
  by_cases hbig : (1 : ℝ) ≤ 2 * c * (ρ : ℝ)
  · refine ⟨1, by norm_num, ?_⟩
    rw [one_smul]
    calc ‖T.direction - V.direction‖ ≤ ‖T.direction‖ + ‖V.direction‖ := norm_sub_le _ _
      _ = 2 := by rw [hTdir, hVdir]; norm_num
      _ ≤ 4 * c * (ρ : ℝ) := by linarith
  rw [not_le] at hbig
  obtain ⟨a, ha, hxa⟩ := exists_axis_point_of_mem_dilate V hc (h (_root_.Tube.x_mem_carrier T))
  obtain ⟨b, hb, hyb⟩ := exists_axis_point_of_mem_dilate V hc (h (_root_.Tube.y_mem_carrier T))
  set e : E3 := (T.y - (V.center + b • V.direction)) - (T.x - (V.center + a • V.direction)) with he
  have hesplit : T.direction - (b - a) • V.direction = e := by
    simp only [he, Tube.direction]
    module
  have hea : ‖T.x - (V.center + a • V.direction)‖ ≤ c * (ρ : ℝ) := by
    rw [← dist_eq_norm]; exact hxa
  have heb : ‖T.y - (V.center + b • V.direction)‖ ≤ c * (ρ : ℝ) := by
    rw [← dist_eq_norm]; exact hyb
  have hebound : ‖e‖ ≤ 2 * (c * (ρ : ℝ)) := by
    calc ‖e‖ ≤ ‖T.y - (V.center + b • V.direction)‖ + ‖T.x - (V.center + a • V.direction)‖ :=
        norm_sub_le _ _
      _ ≤ c * (ρ : ℝ) + c * (ρ : ℝ) := add_le_add heb hea
      _ = 2 * (c * (ρ : ℝ)) := by ring
  -- the coefficient `b - a` is within `2cρ` of `±1`
  have hcoef : |(b - a)| = ‖(b - a) • V.direction‖ := by
    rw [norm_smul, Real.norm_eq_abs, hVdir, mul_one]
  have hclose : |(|b - a|) - 1| ≤ 2 * (c * (ρ : ℝ)) := by
    have h1 : ‖(b - a) • V.direction‖ ≤ ‖T.direction‖ + ‖e‖ := by
      have : (b - a) • V.direction = T.direction - e := by rw [← hesplit]; module
      rw [this]
      exact (norm_sub_le _ _).trans (by simp)
    have h2 : ‖T.direction‖ ≤ ‖(b - a) • V.direction‖ + ‖e‖ := by
      have : T.direction = (b - a) • V.direction + e := by rw [← hesplit]; module
      rw [this]
      exact norm_add_le _ _
    rw [← hcoef] at h1 h2
    rw [hTdir] at h1 h2
    rw [abs_le]
    constructor <;> linarith
  have hne : b - a ≠ 0 := by
    intro h0
    rw [h0] at hclose
    simp only [abs_zero, zero_sub, abs_neg, abs_one] at hclose
    linarith
  refine ⟨if 0 < b - a then 1 else -1, by split <;> norm_num, ?_⟩
  have hkey : ∀ σ : ℝ, |σ| = 1 → |(b - a) - σ| ≤ 2 * (c * (ρ : ℝ)) →
      ‖T.direction - σ • V.direction‖ ≤ 4 * c * (ρ : ℝ) := by
    intro σ hσ hσc
    have hsplit2 : T.direction - σ • V.direction = e + ((b - a) - σ) • V.direction := by
      rw [← hesplit]; module
    rw [hsplit2]
    calc ‖e + ((b - a) - σ) • V.direction‖ ≤ ‖e‖ + ‖((b - a) - σ) • V.direction‖ :=
        norm_add_le _ _
      _ = ‖e‖ + |(b - a) - σ| := by rw [norm_smul, Real.norm_eq_abs, hVdir, mul_one]
      _ ≤ 2 * (c * (ρ : ℝ)) + 2 * (c * (ρ : ℝ)) := add_le_add hebound hσc
      _ = 4 * c * (ρ : ℝ) := by ring
  by_cases hpos : 0 < b - a
  · simp only [hpos, if_pos]
    refine hkey 1 (by norm_num) ?_
    rw [abs_of_pos hpos] at hclose
    exact hclose
  · simp only [hpos, if_neg, not_false_iff]
    refine hkey (-1) (by norm_num) ?_
    have hneg : b - a < 0 := lt_of_le_of_ne (not_lt.mp hpos) hne
    rw [abs_of_neg hneg] at hclose
    have : |(b - a) - (-1)| = |(-(b-a)) - 1| := by
      rw [abs_sub_comm]
      congr 1
      ring
    rw [this]
    exact hclose

open scoped Classical in
/-- **The keystone geometry, on an arbitrary containing family.**  If `P` is *any* `σ`-tube
(`ρ ≤ σ`) containing a member `i` of the angular cone at `(x, v)` of radius `ρ`, then `P` lies in
the `10`-dilate of the *single* `σ`-tube centred at `x` in the direction of a fixed cone member
`i₀`.  The cone's **members** lie in no common `σ`-tube
(`Kakeya.LooseUniform.not_exists_common_tube_of_bush`); the `σ`-tubes that **contain** them all lie
in one bounded dilate, and that asymmetry is what the exact-cover route missed.

Nothing here mentions a hierarchy: per  the essential-distinctness datum must sit
on the family the consumer dilates, so the geometry is stated for an arbitrary `P`. -/
theorem tube_le_dilate_of_mem_angularFibre (cfg : VeryNotSticky.{u}) {σ : NNReal} {ρ : ℝ}
    (hρ : ρ ≤ (σ : ℝ))
    (x v : EuclideanSpace ℝ (Fin 3)) {i₀ : cfg.ι} (hi₀ : i₀ ∈ cfg.angularFibre x v ρ)
    {i : cfg.ι} (hi : i ∈ cfg.angularFibre x v ρ)
    (P : Tube σ (EuclideanSpace ℝ (Fin 3)))
    (hP : ((cfg.T i).toTube).toConvexSpaceBody ≤ P.toConvexSpaceBody) :
    (P.toConvexSpaceBody : ConvexSpaceBody _) ≤
      Kakeya.Tube.dilate (bushTube σ x (cfg.T i₀).direction
        (Tube.norm_direction (cfg.T i₀).toTube) 0) 10 := by
  classical
  set u : E3 := (cfg.T i₀).direction with hu
  have hu1 : ‖u‖ = 1 := Tube.norm_direction (cfg.T i₀).toTube
  set W : Tube σ E3 := bushTube σ x u hu1 0 with hW
  obtain ⟨-, hxi, hiang⟩ := Finset.mem_filter.mp hi
  obtain ⟨-, -, hi₀ang⟩ := Finset.mem_filter.mp hi₀
  -- `x` is on the member `T i`, hence on the container `P`
  have hxT : x ∈ (cfg.T i).carrier := (cfg.T i).shade_subset hxi
  have hnode : ((cfg.T i).toTube).toConvexSpaceBody ≤ P.toConvexSpaceBody := hP
  have hxV : x ∈ P.carrier := hnode hxT
  -- the member's direction is within `2ρ` of `u`
  have hang2 : NonSlab.lineAngle (cfg.T i).direction u ≤ 2 * ρ := by
    have := NonSlab.lineAngle_le_add (cfg.T i).direction v u
    have h2 : NonSlab.lineAngle v u ≤ ρ := (NonSlab.lineAngle_comm v u).trans_le hi₀ang
    linarith
  obtain ⟨σ₂, hσ₂, hd₂⟩ := exists_sign_norm_sub_le_of_lineAngle_le
    (Tube.norm_direction (cfg.T i).toTube) hu1 hang2
  -- the node's direction is within `6ρk` of the member's
  obtain ⟨σ₁, hσ₁, hd₁⟩ := exists_sign_norm_direction_sub_le_of_body_le
    ((cfg.T i).toTube) P hnode
  -- combine
  have hsq : σ₁ * σ₁ = 1 := by
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hσ₁ with h | h <;> rw [h] <;> norm_num
  have hdir : ‖P.direction - (σ₁ * σ₂) • W.direction‖
      ≤ 8 * (σ : ℝ) := by
    have hWd : W.direction = u := bushTube_direction σ x u hu1 0
    have habs : ∀ d w z : E3, d - (σ₁ * σ₂) • z = σ₁ • ((σ₁ • d - w) + (w - σ₂ • z)) := by
      intro d w z
      rw [show (σ₁ • d - w) + (w - σ₂ • z) = σ₁ • d - σ₂ • z by module, smul_sub, smul_smul,
        hsq, one_smul, smul_smul]
    rw [hWd, habs _ (cfg.T i).direction _, norm_smul, Real.norm_eq_abs, hσ₁, one_mul]
    have hfirst : ‖(σ₁ • P.direction)
        - (cfg.T i).direction‖ ≤ 6 * (σ : ℝ) := by
      rw [show (σ₁ • P.direction) - (cfg.T i).direction
          = -((cfg.T i).direction - σ₁ • P.direction) by
        module, norm_neg]
      exact hd₁
    calc ‖((σ₁ • P.direction) - (cfg.T i).direction)
            + ((cfg.T i).direction - σ₂ • u)‖
        ≤ ‖(σ₁ • P.direction) - (cfg.T i).direction‖
          + ‖(cfg.T i).direction - σ₂ • u‖ := norm_add_le _ _
      _ ≤ 6 * (σ : ℝ) + 2 * ρ := add_le_add hfirst hd₂
      _ ≤ 8 * (σ : ℝ) := by linarith
  have hσprod : |σ₁ * σ₂| = 1 := by rw [abs_mul, hσ₁, hσ₂]; norm_num
  refine le_dilate_of_through_point W (K' := 10) (r := 0) (θ := 8 * (σ : ℝ))
    (by norm_num) (s₀ := 0) (by norm_num) ?_ _ hxV (σ := σ₁ * σ₂) hσprod
    hdir (by linarith [σ.coe_nonneg])
  · have hc : W.center = x := by
      rw [hW, Kakeya.LooseUniform.NonVacuity.bushTube_center]; module
    rw [hc]
    simp


open scoped Classical in
/-- **The keystone count, on an arbitrary essentially distinct family.**  At most
`C_ED(3,10) := Tube.essDistinctTubesInSelfDilate.C 3 10` — a *dimensional* constant, `δ`-free and
independent of `cfg` — members of a pairwise essentially distinct family
of `σ`-tubes (`ρ ≤ σ`) can contain a member of the angular cone at `(x, v)` of radius `ρ`.

**This is `M`.**  's covering number is polynomial
(`Kakeya.LooseUniform.exists_bush_forcing_exactCover_floor`) because it counts an arbitrary *cover*
of the cone; the number of *essentially distinct containers* is bounded outright, because they all
lie in one `10`-dilate (`tube_le_dilate_of_mem_angularFibre`) and
`Tube.essDistinctTubesInSelfDilate` counts an essentially distinct family in a dilate.

The family is arbitrary on purpose:  rules that the essential-distinctness datum
belongs on **the family the consumer dilates**, not on the hierarchy's nodes — the uniformiser's
nodes come from `Tube.grid_net_tight`'s `ρ/32`-spaced net and are not it, while
`Kakeya.VeryNotSticky.RhoParentData`'s last conjunct already carries an essentially distinct,
all-used `ρ`-family in exactly this shape. -/
theorem card_le_essDistinctConstant_of_edFamily (cfg : VeryNotSticky.{u}) {κ : Type*}
    {σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) {ρ : ℝ} (hρ : ρ ≤ (σ : ℝ))
    (x v : EuclideanSpace ℝ (Fin 3))
    (t : Finset κ) (P : κ → Tube σ (EuclideanSpace ℝ (Fin 3)))
    (hED : (t : Set κ).Pairwise fun a b =>
      IsEssentiallyDistinct (P a).carrier (P b).carrier)
    (hmeet : ∀ j ∈ t, ∃ i ∈ cfg.angularFibre x v ρ,
      ((cfg.T i).toTube).toConvexSpaceBody ≤ (P j).toConvexSpaceBody) :
    ((t.card : ℕ) : ENNReal) ≤
      ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ENNReal) := by
  classical
  rcases t.eq_empty_or_nonempty with hemp | ⟨j₀, hj₀⟩
  · simp [hemp]
  obtain ⟨i₀, hi₀, -⟩ := hmeet j₀ hj₀
  have hUT : ∀ j ∈ t, (P j).carrier ⊆
      (Kakeya.Tube.dilate (bushTube σ x (cfg.T i₀).direction
        (Tube.norm_direction (cfg.T i₀).toTube) 0) 10).carrier := by
    intro j hj
    obtain ⟨i, hi, hiP⟩ := hmeet j hj
    exact cfg.tube_le_dilate_of_mem_angularFibre hρ x v hi₀ hi (P j) hiP
  have hmain := _root_.Tube.essDistinctTubesInSelfDilate
    (E := EuclideanSpace ℝ (Fin 3)) (ι := κ) (c := 10)
    (by norm_num) hσ0 hσ1
    (bushTube σ x (cfg.T i₀).direction (Tube.norm_direction (cfg.T i₀).toTube) 0) t P hED hUT
  simpa using hmain

open scoped Classical in
/-- **The keystone count in the shape `Kakeya.VeryNotSticky.RhoParentData` carries.**  Given *any*
pairwise essentially distinct family of `σ`-tubes `Tρ` indexed by `tρ` — the fifth conjunct of
`RhoParentData` produces exactly such a family, and /§3.3 rules that this, not the
hierarchy's nodes, is where the tree's essential distinctness lives — at most `C_ED(3,10)` of its
members contain a member of the angular cone at `(x, v)` of radius `ρ ≤ σ`.

No "all-used" clause is needed: the statement is about the members that *do* meet the cone. -/
theorem card_filter_meets_angularFibre_le_of_essDistinct (cfg : VeryNotSticky.{u}) {κ : Type*}
    {σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) {ρ : ℝ} (hρ : ρ ≤ (σ : ℝ))
    (x v : EuclideanSpace ℝ (Fin 3))
    (tρ : Finset κ) (Tρ : κ → Tube σ (EuclideanSpace ℝ (Fin 3)))
    (hED : (tρ : Set κ).Pairwise fun a b =>
      IsEssentiallyDistinct (Tρ a).carrier (Tρ b).carrier) :
    (((tρ.filter (fun j => ∃ i ∈ cfg.angularFibre x v ρ,
        ((cfg.T i).toTube).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody)).card : ℕ) : ENNReal) ≤
      ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ENNReal) := by
  classical
  refine cfg.card_le_essDistinctConstant_of_edFamily hσ0 hσ1 hρ x v _ Tρ
    (hED.mono (by exact_mod_cast Finset.filter_subset _ tρ)) ?_
  intro j hj
  exact (Finset.mem_filter.mp hj).2

open scoped Classical in
/-- **The keystone count, specialised to a hierarchy whose level-`k` nodes happen to be
essentially distinct.**  Recorded because it is the shape `angularFibre_card_le_of_nodeCount`
consumes;  measures that the *existing* uniformiser's nodes are **not** essentially
distinct (they are `Tube.grid_net_tight`'s `ρ/32`-separated net), so this specialisation is not
claimed to be inhabited — `card_le_essDistinctConstant_of_edFamily` is the usable form. -/
theorem card_image_assign_angularFibre_le_of_essDistinct (cfg : VeryNotSticky.{u}) {N : ℕ}
    {C : NNReal} (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C)
    {k : ℕ} (hk : k ≤ N) (hδ0 : 0 < cfg.δ) (hδ1 : cfg.δ ≤ 1)
    (hED : ((𝒰.cover.indexSet k : Finset cfg.ι) : Set cfg.ι).Pairwise fun a b =>
      IsEssentiallyDistinct (𝒰.cover.tube k a).carrier (𝒰.cover.tube k b).carrier)
    {ρ : ℝ} (hρ : ρ ≤ (Tube.gridScale cfg.δ N k : ℝ))
    (x v : EuclideanSpace ℝ (Fin 3)) :
    ((((cfg.angularFibre x v ρ).image (𝒰.cover.assign k)).card : ℕ) : ENNReal) ≤
      ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ENNReal) := by
  classical
  have hJsub : (cfg.angularFibre x v ρ).image (𝒰.cover.assign k) ⊆ 𝒰.cover.indexSet k := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact 𝒰.cover.assign_mem k hk i (Finset.mem_filter.mp hi).1
  refine cfg.card_le_essDistinctConstant_of_edFamily (Tube.gridScale_pos hδ0 N k)
    (Tube.gridScale_le_one hδ1 N k) hρ x v _ (𝒰.cover.tube k)
    (hED.mono (by exact_mod_cast hJsub)) ?_
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact ⟨i, hi, 𝒰.cover.le_tube_assign k hk i (Finset.mem_filter.mp hi).1⟩

open scoped Classical in
/-- **Conjunct 6 *is* the node count.**  Whatever bounds the number of level-`k` nodes the
angular cone meets bounds the cone itself, at the cost of Definition 2.2's `C²`.  This is the
exact-model statement of what  calls `M`: `angularFibre_card_le_of_exactCover`
supplies `M` from a *cover* of the cone by containers and pays `M · C³`; here `Q` is the number
of **nodes**, and the price is `Q · C²`.  Every route to conjunct 6 in the exact model factors
through this lemma. -/
theorem angularFibre_card_le_of_nodeCount (cfg : VeryNotSticky.{u}) {N : ℕ} {C : NNReal}
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T N C)
    {k : ℕ} (hk : k ≤ N) {Q : NNReal} {ρ : ℝ}
    (x v : EuclideanSpace ℝ (Fin 3))
    (hQ : ((((cfg.angularFibre x v ρ).image (𝒱.tubeUniform.cover.assign k)).card : ℕ) : ENNReal)
      ≤ (Q : ENNReal)) :
    (((cfg.angularFibre x v ρ).card : ℕ) : ENNReal) ≤
      (Q : ENNReal) * (C : ENNReal) ^ 2 * ((𝒱.branchingN k : NNReal) : ENNReal) := by
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
  have hJcard := hQ
  have hterm : ∀ j' ∈ J,
      (((ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k) j' x).card : ℕ) : ENNReal)
        ≤ (C : ENNReal) * ((C : ENNReal) * ((𝒱.branchingN k : NNReal) : ENNReal)) := by
    intro j' hj'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
    obtain ⟨his, hxi, -⟩ := Finset.mem_filter.mp hi
    have h1 : ((ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k)
        (𝒰.cover.assign k i) x).card : NNReal) ≤ C * (C * 𝒱.branchingN k) := by
      calc ((ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k)
              (𝒰.cover.assign k i) x).card : NNReal)
          ≤ C * 𝒱.localN x k := 𝒱.card_shadeClass_le x hxU k hk i his hxi
        _ ≤ C * (C * 𝒱.branchingN k) := by gcongr; exact 𝒱.le_branchingN x hxU k hk
    have := ENNReal.coe_le_coe.mpr h1
    simpa [ENNReal.coe_mul] using this
  calc ((A.card : ℕ) : ENNReal)
      ≤ (((J.biUnion (fun j' =>
            ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k) j' x)).card : ℕ) : ENNReal) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((∑ j' ∈ J,
          (ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k) j' x).card : ℕ) : ENNReal) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ j' ∈ J,
          (((ShadedTube.shadeClass cfg.s cfg.T (𝒰.cover.assign k) j' x).card : ℕ) : ENNReal) := by
        push_cast; rfl
    _ ≤ ∑ _j' ∈ J, (C : ENNReal) * ((C : ENNReal) * ((𝒱.branchingN k : NNReal) : ENNReal)) :=
        Finset.sum_le_sum hterm
    _ = ((J.card : ℕ) : ENNReal) *
          ((C : ENNReal) * ((C : ENNReal) * ((𝒱.branchingN k : NNReal) : ENNReal))) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ENNReal) *
          ((C : ENNReal) * ((C : ENNReal) * ((𝒱.branchingN k : NNReal) : ENNReal))) := by
        gcongr
    _ = (Q : ENNReal) * (C : ENNReal) ^ 2 * ((𝒱.branchingN k : NNReal) : ENNReal) := by ring

open scoped Classical in
/-- **The angular cone, counted through essentially distinct nodes.**  With the level-`k` nodes
pairwise essentially distinct, the cone has at most `C_ED · C² · branchingN k` members: the
`C_ED` nodes it meets (`card_image_assign_angularFibre_le_of_essDistinct`) each contribute at
most `C · localN x k ≤ C² · branchingN k` members shading `x` (Definition 2.2). -/
theorem angularFibre_card_le_of_essDistinct (cfg : VeryNotSticky.{u}) {N : ℕ} {C : NNReal}
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T N C)
    {k : ℕ} (hk : k ≤ N) (hδ0 : 0 < cfg.δ) (hδ1 : cfg.δ ≤ 1)
    (hED : ((𝒱.tubeUniform.cover.indexSet k : Finset cfg.ι) : Set cfg.ι).Pairwise fun a b =>
      IsEssentiallyDistinct (𝒱.tubeUniform.cover.tube k a).carrier
        (𝒱.tubeUniform.cover.tube k b).carrier)
    {ρ : ℝ} (hρ : ρ ≤ (Tube.gridScale cfg.δ N k : ℝ))
    (x v : EuclideanSpace ℝ (Fin 3)) :
    (((cfg.angularFibre x v ρ).card : ℕ) : ENNReal) ≤
      ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ENNReal) * (C : ENNReal) ^ 2 *
        ((𝒱.branchingN k : NNReal) : ENNReal) :=
  cfg.angularFibre_card_le_of_nodeCount 𝒱 hk x v
    (cfg.card_image_assign_angularFibre_le_of_essDistinct 𝒱.tubeUniform hk hδ0 hδ1 hED hρ x v)


/-- `C₀⁴ ≤ δ^{-η/2}`, the square root of
`Kakeya.VeryNotSticky.coe_C₀_pow_eight_le_rpow_neg_eta`. -/
theorem coe_C₀_pow_four_le_rpow_neg_half_eta (cfg : VeryNotSticky.{u}) :
    (cfg.C₀ : ENNReal) ^ 4 ≤ (cfg.δ : ENNReal) ^ (-(cfg.η / 2)) := by
  have h := ENNReal.rpow_le_rpow (coe_C₀_pow_eight_le_rpow_neg_eta cfg)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hl : ((cfg.C₀ : ENNReal) ^ 8) ^ ((1 : ℝ) / 2) = (cfg.C₀ : ENNReal) ^ 4 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hr : ((cfg.δ : ENNReal) ^ (-cfg.η)) ^ ((1 : ℝ) / 2) =
      (cfg.δ : ENNReal) ^ (-(cfg.η / 2)) := by
    rw [← ENNReal.rpow_mul]; congr 1; ring
  rwa [hl, hr] at h

open scoped Classical in
/-- **Conjunct 6's inequality from essentially distinct nodes**, at `Cang = C_ED · C⁴`. -/
theorem angularFibre_card_le_fibreMult_of_essDistinct (cfg : VeryNotSticky.{u}) {N : ℕ}
    {C : NNReal} (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T N C) (hC : 1 ≤ C)
    {k : ℕ} (hk : k ≤ N) (hδ0 : 0 < cfg.δ) (hδ1 : cfg.δ ≤ 1)
    (hED : ((𝒱.tubeUniform.cover.indexSet k : Finset cfg.ι) : Set cfg.ι).Pairwise fun a b =>
      IsEssentiallyDistinct (𝒱.tubeUniform.cover.tube k a).carrier
        (𝒱.tubeUniform.cover.tube k b).carrier)
    {ρ : ℝ} (hρ : ρ ≤ (Tube.gridScale cfg.δ N k : ℝ))
    (x v : EuclideanSpace ℝ (Fin 3))
    {j : cfg.ι} (hj : j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k) :
    (((cfg.angularFibre x v ρ).card : ℕ) : ENNReal) ≤
      (((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 * C ^ 4 : NNReal)) : ENNReal) *
        ShadedBody.multiplicity (cfg.tubeFibre 𝒱.tubeUniform k j)
          (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  have h1 := cfg.angularFibre_card_le_of_essDistinct 𝒱 hk hδ0 hδ1 hED hρ x v
  calc (((cfg.angularFibre x v ρ).card : ℕ) : ENNReal)
      ≤ ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ENNReal) *
          (C : ENNReal) ^ 2 * ((𝒱.branchingN k : NNReal) : ENNReal) := h1
    _ ≤ ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ENNReal) *
          (C : ENNReal) ^ 2 * ((C : ENNReal) ^ 2 *
            ShadedBody.multiplicity (cfg.tubeFibre 𝒱.tubeUniform k j)
              (fun i ↦ (cfg.T i).toShadedBody)) := by
        gcongr
        exact cfg.branchingN_le_multiplicity_of_shadedUniform 𝒱 hC hk hj
    _ = (((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 * C ^ 4 : NNReal)) : ENNReal) *
          ShadedBody.multiplicity (cfg.tubeFibre 𝒱.tubeUniform k j)
            (fun i ↦ (cfg.T i).toShadedBody) := by push_cast; ring


open scoped Classical in
/-- **Conjunct 6's `∃ Cang` clause from essentially distinct nodes**, budget included.
`hthr` is the (δ-only) threshold `C_ED ≤ δ^{-η/2}`; `C₀⁴ ≤ δ^{-η/2}` is the configuration's own
`aScaleData_absorb`. -/
theorem exists_Cang_angularFibre_le_of_essDistinct (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hED : ((cfg.splitHierarchy.cover.indexSet k : Finset cfg.ι) : Set cfg.ι).Pairwise fun a b =>
      IsEssentiallyDistinct (cfg.splitHierarchy.cover.tube k a).carrier
        (cfg.splitHierarchy.cover.tube k b).carrier)
    (hρ : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
    (hthr : ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(cfg.η / 2))) :
    ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
      ∀ j ∈ cfg.activeTubeNodes cfg.splitHierarchy k,
        ∀ x v : EuclideanSpace ℝ (Fin 3),
          (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
            (Cang : ENNReal) *
              ShadedBody.multiplicity (cfg.tubeFibre cfg.splitHierarchy k j)
                (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := by
    simpa using (ne_of_gt cfg.hδ)
  have hbud : ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 * cfg.C₀ ^ 4 : NNReal) : ENNReal)
      ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := by
    have hsum : (cfg.δ : ENNReal) ^ (-(cfg.η / 2)) * (cfg.δ : ENNReal) ^ (-(cfg.η / 2))
        = (cfg.δ : ENNReal) ^ (-cfg.η) := by
      rw [← ENNReal.rpow_add _ _ hδ0 ENNReal.coe_ne_top]
      congr 1; ring
    calc ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 * cfg.C₀ ^ 4 : NNReal) : ENNReal)
        = ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ENNReal) *
            (cfg.C₀ : ENNReal) ^ 4 := by push_cast; ring
      _ ≤ (cfg.δ : ENNReal) ^ (-(cfg.η / 2)) * (cfg.δ : ENNReal) ^ (-(cfg.η / 2)) :=
          mul_le_mul' hthr cfg.coe_C₀_pow_four_le_rpow_neg_half_eta
      _ = (cfg.δ : ENNReal) ^ (-cfg.η) := hsum
  refine ⟨_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 * cfg.C₀ ^ 4, hbud, ?_⟩
  intro j hj x v
  exact cfg.angularFibre_card_le_fibreMult_of_essDistinct cfg.uniform.some cfg.hC₀ hk cfg.hδ
    cfg.hδ1 hED (by exact_mod_cast hρ) x v hj

open scoped Classical in
/-- **Conjunct 6 of `Kakeya.VeryNotSticky.SideDataObligations`, verbatim, from GWZ Definition
2.1(ii) alone** — the essential distinctness of the level-`k` parents, which
`Tube.UniformTubeSet` replaced by `boundedOverlap`.  No `μ`, no (86), no loose hierarchy, no
covering number, and **no unpaid budget**: the constant is `C_ED(3,10) · C₀⁴`, `C₀⁴ ≤ δ^{-η/2}`
is the configuration's `aScaleData_absorb` and `C_ED(3,10) ≤ δ^{-η/2}` holds below a threshold
depending on `η` alone.  Contrast `eventually_conjunct6_of_exactCover`, whose `M` is polynomial
(`Kakeya.LooseUniform.exists_bush_forcing_exactCover_floor`). -/
theorem eventually_conjunct6_of_essDistinct {exscal ϱ η : ℝ} (C₀bd : NNReal) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = d → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        (((cfg.splitHierarchy.cover.indexSet k : Finset cfg.ι) : Set cfg.ι).Pairwise fun a b =>
          IsEssentiallyDistinct (cfg.splitHierarchy.cover.tube k a).carrier
            (cfg.splitHierarchy.cover.tube k b).carrier) →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
          ∀ j ∈ cfg.activeTubeNodes cfg.splitHierarchy k,
            ∀ x v : EuclideanSpace ℝ (Fin 3),
              (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
                (Cang : ENNReal) *
                  ShadedBody.multiplicity (cfg.tubeFibre cfg.splitHierarchy k j)
                    (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  by_cases hη : 0 < η
  · obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := AngularCover.exists_const_threshold
      (C := ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ℝ))
      (η := η / 2) (by positivity) (by linarith)
    filter_upwards [Ioc_mem_nhdsGT hδ₀pos] with d hd
    intro cfg bd hδd hηc _ _ _ _ k hk hED hρ _
    refine cfg.exists_Cang_angularFibre_le_of_essDistinct bd hk hED hρ ?_
    have hdpos : 0 < cfg.δ := cfg.hδ
    have hdR : (0 : ℝ) < (cfg.δ : ℝ) := by exact_mod_cast hdpos
    have hle : (cfg.δ : ℝ) ^ (-(η / 2)) ≤ (cfg.δ : ℝ) ^ (-(cfg.η / 2)) := by
      rw [hηc]
    have hthrR := hδ₀ cfg.δ hdpos (by rw [hδd]; exact hd.2)
    rw [ennreal_coe_nnreal_rpow hdR]
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ℝ)
        ≤ (cfg.δ : ℝ) ^ (-(η / 2)) := hthrR
      _ ≤ (cfg.δ : ℝ) ^ (-(cfg.η / 2)) := hle
  · refine Filter.Eventually.of_forall ?_
    intro d cfg bd _ hηc _ _ _ _ k hk hED hρ _
    exact absurd (hηc ▸ cfg.hη) hη


open scoped Classical in
/-- **The price of the clause, compiled.**  Under the same essential-distinctness hypothesis, an
angular cone can contain at most `C_ED(3,10)` members that are *pairwise in no common exact
`ρ_k`-tube*.  `Kakeya.LooseUniform.bush_obstruction` builds `n ≈ 1/(2ρ_k)` such members through a
point for any `ρ_k`, and `Kakeya.VeryNotSticky.card_le_of_bush` allows an admissible
configuration up to `733·δ^{-η}` of them; so the hypothesis is a genuine axial-coherence
condition on `cfg.s`, not a free re-reading.  This is GWZ Definition 2.1(ii) doing its work and
also showing what it costs in the *exact*-containment model, where the parents of an axially
spread bush are forced to be axial translates at spacing `ρ_k` and hence not essentially
distinct. -/
theorem card_le_essDistinctConstant_of_no_common_tube (cfg : VeryNotSticky.{u}) {N : ℕ}
    {C : NNReal} (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C)
    {k : ℕ} (hk : k ≤ N) (hδ0 : 0 < cfg.δ) (hδ1 : cfg.δ ≤ 1)
    (hED : ((𝒰.cover.indexSet k : Finset cfg.ι) : Set cfg.ι).Pairwise fun a b =>
      IsEssentiallyDistinct (𝒰.cover.tube k a).carrier (𝒰.cover.tube k b).carrier)
    {ρ : ℝ} (hρ : ρ ≤ (Tube.gridScale cfg.δ N k : ℝ))
    (x v : EuclideanSpace ℝ (Fin 3)) (t : Finset cfg.ι) (hts : t ⊆ cfg.angularFibre x v ρ)
    (hpair : (t : Set cfg.ι).Pairwise fun i i' =>
      ¬ ∃ W : Tube (Tube.gridScale cfg.δ N k) (EuclideanSpace ℝ (Fin 3)),
        (cfg.T i).toConvexSpaceBody ≤ W.toConvexSpaceBody ∧
        (cfg.T i').toConvexSpaceBody ≤ W.toConvexSpaceBody) :
    ((t.card : ℕ) : ENNReal) ≤
      ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ENNReal) := by
  classical
  have hinj : Set.InjOn (𝒰.cover.assign k) (t : Set cfg.ι) := by
    intro i hi i' hi' heq
    by_contra hne
    refine hpair hi hi' hne ⟨𝒰.cover.tube k (𝒰.cover.assign k i), ?_, ?_⟩
    · exact 𝒰.cover.le_tube_assign k hk i
        (Finset.mem_filter.mp (hts (by exact_mod_cast hi))).1
    · rw [heq]
      exact 𝒰.cover.le_tube_assign k hk i'
        (Finset.mem_filter.mp (hts (by exact_mod_cast hi'))).1
  have hcard : t.card = (t.image (𝒰.cover.assign k)).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hsub : t.image (𝒰.cover.assign k) ⊆
      (cfg.angularFibre x v ρ).image (𝒰.cover.assign k) := Finset.image_subset_image hts
  calc ((t.card : ℕ) : ENNReal)
      = (((t.image (𝒰.cover.assign k)).card : ℕ) : ENNReal) := by rw [hcard]
    _ ≤ ((((cfg.angularFibre x v ρ).image (𝒰.cover.assign k)).card : ℕ) : ENNReal) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ENNReal) :=
        cfg.card_image_assign_angularFibre_le_of_essDistinct 𝒰 hk hδ0 hδ1 hED hρ x v

open scoped Classical in
/-- **The `boundedOverlap` route, positive half.**  If the members of the angular cone at
`(x, v)` are covered by `M` exact `ρ_k`-tubes, the cone meets at most `M · C` level-`k` nodes —
from `Tube.UniformTubeSet.boundedOverlap` alone, with no essential distinctness anywhere.
`boundedOverlap`'s "some member of `s` lies in both the node and `V`" clause does **not** block:
the witness is the cone member that put the node in the count. -/
theorem card_image_assign_angularFibre_le_of_exactCover (cfg : VeryNotSticky.{u}) {N : ℕ}
    {C : NNReal} (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C)
    {k : ℕ} (hk : k ≤ N) {ρ : ℝ} {M : ℕ} (x v : EuclideanSpace ℝ (Fin 3))
    (W : Fin M → Tube (Tube.gridScale cfg.δ N k) (EuclideanSpace ℝ (Fin 3)))
    (hcov : ∀ i ∈ cfg.angularFibre x v ρ, ∃ m,
      (cfg.T i).toConvexSpaceBody ≤ (W m).toConvexSpaceBody) :
    ((((cfg.angularFibre x v ρ).image (𝒰.cover.assign k)).card : ℕ) : ENNReal) ≤
      (((M : NNReal) * C : NNReal) : ENNReal) := by
  classical
  set J := (cfg.angularFibre x v ρ).image (𝒰.cover.assign k) with hJ
  have hJsub : J ⊆ (Finset.univ : Finset (Fin M)).biUnion (fun m => 𝒰.meetingNodes k (W m)) := by
    intro j' hj'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
    obtain ⟨his, -, -⟩ := Finset.mem_filter.mp hi
    obtain ⟨m, hm⟩ := hcov i hi
    refine Finset.mem_biUnion.mpr ⟨m, Finset.mem_univ m, ?_⟩
    simp only [Tube.UniformTubeSet.meetingNodes, Finset.mem_filter]
    exact ⟨𝒰.cover.assign_mem k hk i his, i, his, 𝒰.cover.le_tube_assign k hk i his, hm⟩
  have hNN : ((J.card : ℕ) : NNReal) ≤ (M : NNReal) * C := by
    calc ((J.card : ℕ) : NNReal)
        ≤ ((((Finset.univ : Finset (Fin M)).biUnion
              (fun m => 𝒰.meetingNodes k (W m))).card : ℕ) : NNReal) := by
          exact_mod_cast Finset.card_le_card hJsub
      _ ≤ ((∑ m : Fin M, (𝒰.meetingNodes k (W m)).card : ℕ) : NNReal) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ m : Fin M, ((𝒰.meetingNodes k (W m)).card : NNReal) := by push_cast; rfl
      _ ≤ ∑ _m : Fin M, C := Finset.sum_le_sum (fun m _ => 𝒰.card_meetingNodes_le hk (W m))
      _ = (M : NNReal) * C := by simp [Finset.sum_const, nsmul_eq_mul]
  exact_mod_cast ENNReal.coe_le_coe.mpr hNN

/-! ### The essentially distinct parent family in `RhoParentData`

At each admissible `ρ`, the fifth conjunct of `RhoParentData` supplies a
type `κ`, a finite family `tρ : Finset κ`, and tubes `Tρ : κ → Tube ρ E3`.
They are pairwise essentially distinct, satisfy the all-used condition
`∀ j ∈ tρ, ∃ i ∈ sPar, T i ≤ Tρ j`, and obey
`ρ^(-2 - ζ) ≤ |tρ|`.

These conditions supply no assignment, cover of `sPar`, class-size bracket
(Definition 2.1(iii)), or shading bracket (Definition 2.2). The all-used
condition runs from parent tubes to members of `sPar`, rather than covering
every member of `sPar`. Moreover, `κ` is existentially quantified, whereas
`Tube.GridCoverSystem` uses the original index type `ι` for both its
assignment and node tubes. The fourth conjunct supplies a
`Tube.UniformTubeSet sPar …`, but does not identify its nodes with this
essentially distinct family.

The following two theorems derive the angular clause from a parent family
with the necessary assignments and brackets given explicitly as hypotheses.
-/

open scoped Classical in
/-- **The D-b bridge: conjunct 6's left-hand side against an essentially distinct parent family.**
Given a pairwise essentially distinct family `Tρ` on `tρ` — `Kakeya.VeryNotSticky.RhoParentData`'s
fifth conjunct — an assignment `a` of the members into it, and a bound `B` on the members of one
parent's class shading `x`, the angular cone has at most `C_ED(3,10) · B` members.

**The three hypotheses `hmem`, `hcov`, `hB` are exactly what `RhoParentData`'s fifth conjunct does
NOT carry** (`VeryNotSticky.lean:96-113`): its clauses are pairwise essential distinctness, the
*all-used* clause `∀ j ∈ tρ, ∃ i ∈ sPar, T i ≤ Tρ j` — which runs the other way and is not a cover
— and the parent count `ρ^{-2-ζ} ≤ |tρ|`.  There is no assignment, no cover, no class-size bracket
and no shading bracket, and `κ` is existentially quantified, so it is not `ι` and
`Tube.GridCoverSystem` (whose `assign : ℕ → ι → ι` and `tube : ℕ → ι → Tube …` are `ι`-indexed)
cannot express the family as a hierarchy at all. -/
theorem angularFibre_card_le_of_edCover (cfg : VeryNotSticky.{u}) {κ : Type*}
    {σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) {ρ : ℝ} (hρ : ρ ≤ (σ : ℝ))
    (x v : EuclideanSpace ℝ (Fin 3))
    (tρ : Finset κ) (Tρ : κ → Tube σ (EuclideanSpace ℝ (Fin 3)))
    (hED : (tρ : Set κ).Pairwise fun p q =>
      IsEssentiallyDistinct (Tρ p).carrier (Tρ q).carrier)
    (a : cfg.ι → κ)
    (hmem : ∀ i ∈ cfg.s, a i ∈ tρ)
    (hcov : ∀ i ∈ cfg.s, ((cfg.T i).toTube).toConvexSpaceBody ≤ (Tρ (a i)).toConvexSpaceBody)
    {B : ENNReal}
    (hB : ∀ i ∈ cfg.angularFibre x v ρ,
      (((cfg.s.filter (fun i' => a i' = a i ∧ x ∈ (cfg.T i').shade)).card : ℕ) : ENNReal) ≤ B) :
    (((cfg.angularFibre x v ρ).card : ℕ) : ENNReal) ≤
      ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ENNReal) * B := by
  classical
  set A := cfg.angularFibre x v ρ with hA
  set J := A.image a with hJ
  -- the cone is covered by the shade classes of the parents it meets
  have hsub : A ⊆ J.biUnion
      (fun j => cfg.s.filter (fun i' => a i' = j ∧ x ∈ (cfg.T i').shade)) := by
    intro i hi
    obtain ⟨his, hxi, -⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_biUnion.mpr ⟨a i, Finset.mem_image_of_mem _ hi,
      Finset.mem_filter.mpr ⟨his, rfl, hxi⟩⟩
  -- at most `C_ED` parents are met
  have hJcard : ((J.card : ℕ) : ENNReal) ≤
      ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ENNReal) := by
    refine cfg.card_le_essDistinctConstant_of_edFamily hσ0 hσ1 hρ x v J Tρ
      (hED.mono ?_) ?_
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hj)
      exact hmem i (Finset.mem_filter.mp hi).1
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨i, hi, hcov i (Finset.mem_filter.mp hi).1⟩
  -- and each contributes at most `B`
  have hterm : ∀ j ∈ J,
      (((cfg.s.filter (fun i' => a i' = j ∧ x ∈ (cfg.T i').shade)).card : ℕ) : ENNReal) ≤ B := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact hB i hi
  calc ((A.card : ℕ) : ENNReal)
      ≤ (((J.biUnion
            (fun j => cfg.s.filter (fun i' => a i' = j ∧ x ∈ (cfg.T i').shade))).card : ℕ)
              : ENNReal) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((∑ j ∈ J,
          (cfg.s.filter (fun i' => a i' = j ∧ x ∈ (cfg.T i').shade)).card : ℕ) : ENNReal) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ j ∈ J,
          (((cfg.s.filter (fun i' => a i' = j ∧ x ∈ (cfg.T i').shade)).card : ℕ) : ENNReal) := by
        push_cast; rfl
    _ ≤ ∑ _j ∈ J, B := Finset.sum_le_sum hterm
    _ = ((J.card : ℕ) : ENNReal) * B := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ENNReal) * B := by
        gcongr


open scoped Classical in
/-- **Conjunct 6's clause, in the shape D-b would have to pin it: on the ED parent family's own
fibre.**  `edFibre a j := {i ∈ cfg.s | a i = j}` is written out rather than named, so no new
definition is introduced.  The single remaining hypothesis `hbr` is Definition 2.1(iii) together
with Definition 2.2 read on that family — the per-point class bracket against the fibre's
multiplicity — and it is precisely what `Kakeya.VeryNotSticky.RhoParentData`'s fifth conjunct does
not carry.  Everything else, including the `M`-free constant `C_ED(3,10)`, is discharged. -/
theorem angularFibre_le_edFibreMult (cfg : VeryNotSticky.{u}) {κ : Type*}
    {σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) {ρ : ℝ} (hρ : ρ ≤ (σ : ℝ))
    (tρ : Finset κ) (Tρ : κ → Tube σ (EuclideanSpace ℝ (Fin 3)))
    (hED : (tρ : Set κ).Pairwise fun p q =>
      IsEssentiallyDistinct (Tρ p).carrier (Tρ q).carrier)
    (a : cfg.ι → κ)
    (hmem : ∀ i ∈ cfg.s, a i ∈ tρ)
    (hcov : ∀ i ∈ cfg.s, ((cfg.T i).toTube).toConvexSpaceBody ≤ (Tρ (a i)).toConvexSpaceBody)
    (D : NNReal) (j : κ)
    (hbr : ∀ x v : EuclideanSpace ℝ (Fin 3), ∀ i ∈ cfg.angularFibre x v ρ,
      (((cfg.s.filter (fun i' => a i' = a i ∧ x ∈ (cfg.T i').shade)).card : ℕ) : ENNReal) ≤
        (D : ENNReal) * ShadedBody.multiplicity (cfg.s.filter (fun i' => a i' = j))
          (fun i ↦ (cfg.T i).toShadedBody)) :
    ∀ x v : EuclideanSpace ℝ (Fin 3),
      (((cfg.angularFibre x v ρ).card : ℕ) : ENNReal) ≤
        (((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 * D : NNReal)) : ENNReal) *
          ShadedBody.multiplicity (cfg.s.filter (fun i' => a i' = j))
            (fun i ↦ (cfg.T i).toShadedBody) := by
  intro x v
  have h := cfg.angularFibre_card_le_of_edCover hσ0 hσ1 hρ x v tρ Tρ hED a hmem hcov (hbr x v)
  calc (((cfg.angularFibre x v ρ).card : ℕ) : ENNReal)
      ≤ ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ENNReal) *
          ((D : ENNReal) * ShadedBody.multiplicity (cfg.s.filter (fun i' => a i' = j))
            (fun i ↦ (cfg.T i).toShadedBody)) := h
    _ = (((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 * D : NNReal)) : ENNReal) *
          ShadedBody.multiplicity (cfg.s.filter (fun i' => a i' = j))
            (fun i ↦ (cfg.T i).toShadedBody) := by push_cast; ring

open scoped Classical in
/-- **`Kakeya.VeryNotSticky.nonslabKKTPow` needs no twin.**  It is already stated for an arbitrary
subfamily `sub ⊆ cfg.s` and a *free* node count `N : ℕ`; instantiating `N := tρ.card` discharges
its `hcount` from `Kakeya.VeryNotSticky.RhoParentData`'s fifth conjunct **verbatim** and at
`Ccnt = 1`.  The residue is therefore exactly two clauses on the ED family's fibre: the fullness
floor `hfull`, and `hfib` — which is GWZ Definition 2.1(iii), `|𝕋_ρ| · |𝕋[T_ρ]| ≤ K |𝕋|`.
Neither is in the fifth conjunct. -/
theorem nonslabKKTPow_on_edFamily (cfg : VeryNotSticky.{u}) (hβ1 : cfg.β ≤ 1)
    (hKT : cfg.KTScaleData cfg.ϱ) {K : NNReal} {M : ℝ} (hM : 0 ≤ M)
    (hCδ : (K : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(M * cfg.η)))
    {κ : Type*} (tρ : Finset κ)
    (hcount : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (tρ.card : ℝ))
    {sub : Finset cfg.ι} (hsub : sub ⊆ cfg.s)
    (hfull : ShadedBody.fullness sub (fun i ↦ (cfg.T i).toShadedBody) ≥ cfg.δ ^ (2 * cfg.η))
    (hfib : (tρ.card : ℝ) * (sub.card : ℝ) ≤ (K : ℝ) * (cfg.s.card : ℝ)) :
    ShadedBody.multiplicity sub (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ + M * cfg.η)) *
        ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β := by
  refine cfg.nonslabKKTPow hβ1 hKT (K := K) (Ccnt := 1) hM (by simpa using hCδ) hsub hfull
    tρ.card hfib ?_
  simpa using hcount

open scoped Classical in
/-- **`Kakeya.VeryNotSticky.nonslabPointwiseBound` needs no twin either.**  Its angular input is a
bound on `cfg.angularFibre` by an *abstract* `A : ENNReal`; it never reads a fibre.  So the output
of `angularFibre_card_le_of_edCover` — `#cone ≤ C_ED(3,10) · Bnd` for whatever `Bnd` the ED
family's shade class supplies — plugs straight in, with the consumer's text unchanged. -/
theorem nonslabPointwiseBound_on_edFamily (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (hBmax : ∀ B' (hB' : B' ∈ bd.bs),
      ShadedBody.multiplicity (tc.thinBall hB').bodies' (tc.thinBall hB').W ≤
        ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W)
    {Bnd : ENNReal}
    (hang : ∀ x v : EuclideanSpace ℝ (Fin 3),
      (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
        ((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ENNReal) * Bnd)
    (hδρ : (cfg.δ : ℝ) ≤ (cfg.rho2Star bd.C₀ : ℝ))
    (hρ1 : (cfg.rho2Star bd.C₀ : ℝ) ≤ 1)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ShadedBody.iUnionShade cfg.s tc.Y'Body) :
    (ShadedBody.pointwiseMultiplicity cfg.s tc.Y'Body x : ENNReal) ≤
      ((tc.C : ENNReal) *
          ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W) *
        (((_root_.Tube.essDistinctTubesInSelfDilate.C 3 10 : NNReal) : ENNReal) * Bnd) :=
  cfg.nonslabPointwiseBound tc hB hBmax hang hδρ hρ1 hx

end VeryNotSticky

/-! ### The loose port: `boundedOverlapDil` is a theorem of Definition 2.1(ii)

The same two steps run in `Kakeya.LooseUniform`'s loose model, where the member lies in the
`K`-dilate of its node rather than in the node.  There they prove something the exact model
cannot use: the assumed field
`Kakeya.LooseUniform.LooseUniformTubeSet.boundedOverlapDil` — the bounded-overlap clause that
`Kakeya.LooseUniform.angularCone_card_le_of_loose` consumes and that  lists as
a producer obligation — **follows from the essential distinctness of the loose nodes**, i.e.
from GWZ Definition 2.1(ii) verbatim.  So on the loose route this is not a new assumption but a
replacement of an assumed field by the source's own clause. -/

namespace LooseUniform

variable {ι : Type*}

/-- A loose node whose class has a member inside `dilate V 8` lies inside `dilate V 130`. -/
theorem node_le_dilate_of_member_le_dilate {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E3}
    {N : ℕ} (cover : LooseGridCoverSystem s T N 4) {k : ℕ} (hk : k ≤ N)
    (V : Tube (Tube.gridScale δ N k) E3) {i : ι} (hi : i ∈ s)
    (hiV : (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V 8) :
    (cover.tube k (cover.assign k i)).toConvexSpaceBody ≤ Kakeya.Tube.dilate V 130 := by
  classical
  have hρ0 : (0 : ℝ) ≤ ((Tube.gridScale δ N k : NNReal) : ℝ) := NNReal.coe_nonneg _
  -- (a) the member's direction is within `4·8·ρ_k` of `V`'s
  obtain ⟨σ₁, hσ₁, hd₁⟩ :=
    Kakeya.VeryNotSticky.exists_sign_norm_direction_sub_le_of_le_dilate (T i) V
      (by norm_num : (0:ℝ) < 8) hiV
  -- (b) and within `ρ_k/4` of the node's
  obtain ⟨σ₂, hσ₂, hd₂⟩ := cover.dir_close_tube_assign k hk i hi
  have hsq₂ : σ₂ * σ₂ = 1 := by
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hσ₂ with h | h <;> rw [h] <;> norm_num
  have hσ : |σ₂ * σ₁| = 1 := by rw [abs_mul, hσ₂, hσ₁]; norm_num
  have hσcase : σ₂ * σ₁ = 1 ∨ σ₂ * σ₁ = -1 := (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hσ
  have hdir : ‖(cover.tube k (cover.assign k i)).direction - (σ₂ * σ₁) • V.direction‖
      ≤ 33 * ((Tube.gridScale δ N k : NNReal) : ℝ) := by
    have habs : ∀ a b c : E3, a - (σ₂ * σ₁) • c = σ₂ • ((σ₂ • a - b) + (b - σ₁ • c)) := by
      intro a b c
      rw [show (σ₂ • a - b) + (b - σ₁ • c) = σ₂ • a - σ₁ • c by module, smul_sub, smul_smul,
        hsq₂, one_smul, smul_smul]
    rw [habs _ (T i).direction _, norm_smul, Real.norm_eq_abs, hσ₂, one_mul]
    have hfirst : ‖σ₂ • (cover.tube k (cover.assign k i)).direction - (T i).direction‖
        ≤ ((Tube.gridScale δ N k : NNReal) : ℝ) / 4 := by
      rw [show σ₂ • (cover.tube k (cover.assign k i)).direction - (T i).direction
          = -((T i).direction - σ₂ • (cover.tube k (cover.assign k i)).direction) by module,
        norm_neg]
      exact hd₂
    calc ‖(σ₂ • (cover.tube k (cover.assign k i)).direction - (T i).direction)
            + ((T i).direction - σ₁ • V.direction)‖
        ≤ ‖σ₂ • (cover.tube k (cover.assign k i)).direction - (T i).direction‖
          + ‖(T i).direction - σ₁ • V.direction‖ := norm_add_le _ _
      _ ≤ ((Tube.gridScale δ N k : NNReal) : ℝ) / 4
            + 4 * 8 * ((Tube.gridScale δ N k : NNReal) : ℝ) := add_le_add hfirst hd₁
      _ ≤ 33 * ((Tube.gridScale δ N k : NNReal) : ℝ) := by linarith
  -- (c) position
  obtain ⟨t, ht, hqt⟩ := exists_axis_point_of_mem_dilate (cover.tube k (cover.assign k i))
    (by norm_num : (0:ℝ) < 4)
    (cover.le_dilate_tube_assign k hk i hi (_root_.Tube.x_mem_carrier (T i)))
  obtain ⟨t', ht', hqt'⟩ := exists_axis_point_of_mem_dilate V (by norm_num : (0:ℝ) < 8)
    (hiV (_root_.Tube.x_mem_carrier (T i)))
  have ht2 := abs_le.mp ht
  have ht'2 := abs_le.mp ht'
  have habs_t : |t + 1 / 2| ≤ 5 / 2 := by rw [abs_le]; constructor <;> linarith
  have hs₀ : |t' - (t + 1 / 2) * (σ₂ * σ₁)| ≤ 130 / 2 - 1 := by
    rw [abs_le]
    rcases hσcase with h | h <;> rw [h] <;> constructor <;> linarith
  have hxV : dist (cover.tube k (cover.assign k i)).x
      (V.center + (t' - (t + 1 / 2) * (σ₂ * σ₁)) • V.direction)
      ≤ 95 * ((Tube.gridScale δ N k : NNReal) : ℝ) := by
    have hndx : (cover.tube k (cover.assign k i)).x
        = (cover.tube k (cover.assign k i)).center
          - (1 / 2 : ℝ) • (cover.tube k (cover.assign k i)).direction := by
      have hc : (cover.tube k (cover.assign k i)).center
          = midpoint ℝ (cover.tube k (cover.assign k i)).x
              (cover.tube k (cover.assign k i)).y := rfl
      rw [hc, midpoint_eq_smul_add, invOf_eq_inv, one_div]
      simp only [Tube.direction]
      module
    have hq1 : ‖(T i).x - ((cover.tube k (cover.assign k i)).center
        + t • (cover.tube k (cover.assign k i)).direction)‖
        ≤ 4 * ((Tube.gridScale δ N k : NNReal) : ℝ) := by
      rw [← dist_eq_norm]; exact hqt
    have hq2 : ‖(T i).x - (V.center + t' • V.direction)‖
        ≤ 8 * ((Tube.gridScale δ N k : NNReal) : ℝ) := by
      rw [← dist_eq_norm]; exact hqt'
    have hb1 : ‖((cover.tube k (cover.assign k i)).center
          + t • (cover.tube k (cover.assign k i)).direction) - (T i).x‖
        ≤ 4 * ((Tube.gridScale δ N k : NNReal) : ℝ) := by
      rw [show ((cover.tube k (cover.assign k i)).center
            + t • (cover.tube k (cover.assign k i)).direction) - (T i).x
          = -((T i).x - ((cover.tube k (cover.assign k i)).center
              + t • (cover.tube k (cover.assign k i)).direction)) by module, norm_neg]
      exact hq1
    have hb3 : ‖(-(t + 1 / 2)) • ((cover.tube k (cover.assign k i)).direction
          - (σ₂ * σ₁) • V.direction)‖
        ≤ (5 / 2) * (33 * ((Tube.gridScale δ N k : NNReal) : ℝ)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg]
      exact mul_le_mul habs_t hdir (norm_nonneg _) (by norm_num)
    have hexp : (cover.tube k (cover.assign k i)).x
        - (V.center + (t' - (t + 1 / 2) * (σ₂ * σ₁)) • V.direction)
        = ((((cover.tube k (cover.assign k i)).center
              + t • (cover.tube k (cover.assign k i)).direction) - (T i).x)
            + ((T i).x - (V.center + t' • V.direction)))
          + (-(t + 1 / 2)) • ((cover.tube k (cover.assign k i)).direction
              - (σ₂ * σ₁) • V.direction) := by
      rw [hndx]
      module
    rw [dist_eq_norm, hexp]
    calc ‖((((cover.tube k (cover.assign k i)).center
              + t • (cover.tube k (cover.assign k i)).direction) - (T i).x)
            + ((T i).x - (V.center + t' • V.direction)))
          + (-(t + 1 / 2)) • ((cover.tube k (cover.assign k i)).direction
              - (σ₂ * σ₁) • V.direction)‖
        ≤ ‖(((cover.tube k (cover.assign k i)).center
              + t • (cover.tube k (cover.assign k i)).direction) - (T i).x)
            + ((T i).x - (V.center + t' • V.direction))‖
          + ‖(-(t + 1 / 2)) • ((cover.tube k (cover.assign k i)).direction
              - (σ₂ * σ₁) • V.direction)‖ := norm_add_le _ _
      _ ≤ (‖((cover.tube k (cover.assign k i)).center
              + t • (cover.tube k (cover.assign k i)).direction) - (T i).x‖
            + ‖(T i).x - (V.center + t' • V.direction)‖)
          + (5 / 2) * (33 * ((Tube.gridScale δ N k : NNReal) : ℝ)) :=
          add_le_add (norm_add_le _ _) hb3
      _ ≤ (4 * ((Tube.gridScale δ N k : NNReal) : ℝ)
            + 8 * ((Tube.gridScale δ N k : NNReal) : ℝ))
          + (5 / 2) * (33 * ((Tube.gridScale δ N k : NNReal) : ℝ)) :=
          add_le_add (add_le_add hb1 hq2) le_rfl
      _ ≤ 95 * ((Tube.gridScale δ N k : NNReal) : ℝ) := by linarith
  exact le_dilate_of_through_point V (K' := 130)
    (r := 95 * ((Tube.gridScale δ N k : NNReal) : ℝ))
    (θ := 33 * ((Tube.gridScale δ N k : NNReal) : ℝ))
    (by norm_num) hs₀ hxV (cover.tube k (cover.assign k i))
    (_root_.Tube.x_mem_carrier _) hσ hdir (by linarith)


open scoped Classical in
/-- **`Kakeya.LooseUniform.LooseUniformTubeSet.boundedOverlapDil` is a THEOREM of GWZ
Definition 2.1(ii).**  At `K = 4`, if the level-`k` loose nodes are pairwise essentially
distinct then at most `Tube.essDistinctTubesInSelfDilate.C 3 130` of their classes have a
member inside the `(K+4)`-dilate of an arbitrary `ρ_k`-tube `V`.  The assumed field of
`LooseUniformTubeSet` can therefore be *derived* rather than produced, which removes one
obligation from the R18 producer and replaces it by the source's own clause. -/
theorem card_filter_le_of_essDistinct {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E3}
    {N : ℕ} (cover : LooseGridCoverSystem s T N 4) {k : ℕ} (hk : k ≤ N)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hED : ((cover.indexSet k : Finset ι) : Set ι).Pairwise fun a b =>
      IsEssentiallyDistinct (cover.tube k a).carrier (cover.tube k b).carrier)
    (V : Tube (Tube.gridScale δ N k) E3) :
    ((((cover.indexSet k).filter (fun j => ∃ i ∈ s, cover.assign k i = j ∧
        (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V ((4 : ℝ) + 4))).card : ℕ) : NNReal)
      ≤ _root_.Tube.essDistinctTubesInSelfDilate.C 3 130 := by
  classical
  set F := (cover.indexSet k).filter (fun j => ∃ i ∈ s, cover.assign k i = j ∧
    (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V ((4 : ℝ) + 4)) with hF
  have hFsub : F ⊆ cover.indexSet k := Finset.filter_subset _ _
  have hUED : ((F : Finset ι) : Set ι).Pairwise fun a b =>
      IsEssentiallyDistinct (cover.tube k a).carrier (cover.tube k b).carrier :=
    hED.mono (by exact_mod_cast hFsub)
  have hUT : ∀ j ∈ F, (cover.tube k j).carrier ⊆ (Kakeya.Tube.dilate V 130).carrier := by
    intro j hj
    obtain ⟨-, i, hi, hij, hiV⟩ := Finset.mem_filter.mp hj
    have hiV8 : (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V 8 := by
      have : ((4 : ℝ) + 4) = 8 := by norm_num
      rwa [this] at hiV
    have := node_le_dilate_of_member_le_dilate cover hk V hi hiV8
    rwa [hij] at this
  have hmain := _root_.Tube.essDistinctTubesInSelfDilate (E := E3) (ι := ι) (c := 130)
    (by norm_num) (Tube.gridScale_pos hδ0 N k) (Tube.gridScale_le_one hδ1 N k)
    V F (cover.tube k) hUED hUT
  have hfr : Module.finrank ℝ E3 = 3 := by
    simp [E3]
  rw [hfr] at hmain
  have hcast : ((F.card : ℕ) : ENNReal)
      = ((((F.card : ℕ) : NNReal)) : ENNReal) := by push_cast; rfl
  rw [hcast] at hmain
  exact_mod_cast hmain

/-- **`tube_injOn` is a consequence of Definition 2.1(ii) too.**  Essentially distinct nodes are
distinct as tubes, because a tube of positive finite volume is not essentially distinct from
itself (`not_isEssentiallyDistinct_self`). -/
theorem injOn_of_essDistinct {σ : NNReal} (hσ : 0 < σ) {J : Finset ι} {W : ι → Tube σ E3}
    (hED : ((J : Finset ι) : Set ι).Pairwise fun a b =>
      IsEssentiallyDistinct (W a).carrier (W b).carrier) :
    Set.InjOn W (J : Set ι) := by
  intro a ha b hb hab
  by_contra hne
  have h : IsEssentiallyDistinct (W a).carrier (W b).carrier := hED ha hb hne
  rw [hab] at h
  refine not_isEssentiallyDistinct_self ?_ ?_ h
  · have hvol := Tube.le_volume (E := E3) (W b)
    have hpos : (0 : ENNReal) < (Tube.le_volume.c (Module.finrank ℝ E3) : ENNReal)
        * (σ : ENNReal) ^ ((Module.finrank ℝ E3 : ℕ) - 1) := by
      refine ENNReal.mul_pos ?_ ?_
      · simpa using (ne_of_gt (Tube.le_volume.c_pos (Module.finrank ℝ E3)))
      · simp only [ne_eq, pow_eq_zero_iff', not_and, not_not]
        intro h0
        exact absurd (by exact_mod_cast h0 : σ = 0) (ne_of_gt hσ)
    exact ne_of_gt (lt_of_lt_of_le hpos hvol)
  · exact ne_top_of_le_ne_top (W b).isCompact.measure_ne_top le_rfl

open scoped Classical in
/-- **A `LooseUniformTubeSet` from GWZ Definition 2.1(ii) plus the two class brackets.**  Both
`tube_injOn` and `boundedOverlapDil` are supplied by essential distinctness of the nodes, so a
producer of the loose hierarchy owes only the cover, the branching function, and Definition
2.1(iii)'s two-sided class bracket. -/
noncomputable def LooseUniformTubeSet.ofEssDistinct {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E3}
    {N : ℕ} (cover : LooseGridCoverSystem s T N 4) (branchingN : ℕ → NNReal) {C : NNReal}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hED : ∀ k ≤ N, ((cover.indexSet k : Finset ι) : Set ι).Pairwise fun a b =>
      IsEssentiallyDistinct (cover.tube k a).carrier (cover.tube k b).carrier)
    (hup : ∀ k ≤ N, ∀ j ∈ cover.indexSet k,
      ((Tube.coverClass s (cover.assign k) j).card : NNReal) ≤ C * branchingN k)
    (hlo : ∀ k ≤ N, ∀ j ∈ cover.indexSet k,
      branchingN k ≤ C * ((Tube.coverClass s (cover.assign k) j).card : NNReal)) :
    LooseUniformTubeSet s T N 4 (max C (_root_.Tube.essDistinctTubesInSelfDilate.C 3 130)) where
  cover := cover
  branchingN := branchingN
  tube_injOn k hk := injOn_of_essDistinct (Tube.gridScale_pos hδ0 N k) (hED k hk)
  boundedOverlapDil k hk V :=
    (card_filter_le_of_essDistinct cover hk hδ0 hδ1 (hED k hk) V).trans (le_max_right _ _)
  card_class_le k hk j hj :=
    (hup k hk j hj).trans (mul_le_mul' (le_max_left _ _) le_rfl)
  le_card_class k hk j hj :=
    (hlo k hk j hj).trans (mul_le_mul' (le_max_left _ _) le_rfl)
/-- Every unit `δ`-tube through `x` with direction exactly `v` lies in the `10`-dilate of the
`σ`-tube centred at `x` in the direction `v`, as soon as `4δ ≤ σ`. -/
theorem le_dilate_bushTube_of_through_point_dir {δ σ : NNReal} (hδσ : 4 * (δ : ℝ) ≤ σ)
    (x v : E3) (hv : ‖v‖ = 1) (T : Tube δ E3) (hx : x ∈ T.carrier) (hdir : T.direction = v) :
    T.toConvexSpaceBody ≤ Kakeya.Tube.dilate (bushTube σ x v hv 0) 10 := by
  have hσ0 : (0 : ℝ) ≤ (σ : ℝ) := σ.coe_nonneg
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  refine le_dilate_of_through_point (bushTube σ x v hv 0) (K' := 10) (r := 0) (θ := 0)
    (by norm_num) (s₀ := 0) (by norm_num) ?_ T hx (σ := 1) (by norm_num) ?_ (by linarith)
  · have hc : (bushTube σ x v hv 0).center = x := by
      rw [Kakeya.LooseUniform.NonVacuity.bushTube_center]; module
    rw [hc]; simp
  · rw [one_smul, bushTube_direction, hdir, sub_self, norm_zero]

/-- **The covering step of the `boundedOverlap`-only route is FALSE, at the `4`-dilate already.**
There is no dimensional-constant family of exact `σ`-tubes containing every unit `δ`-tube that
passes through `x`, has direction `V.direction`, and lies inside `Tube.dilate V 4`: any such
family has at least `⌊1/(6σ)⌋` members.  The witness is
`Kakeya.LooseUniform.bush_obstruction`'s parallel bush, every member of which satisfies all three
conditions.

The reason is structural, and it is the whole exact-vs-loose gap:
`Tube.UniformTubeSet.boundedOverlap` is stated against a container of **unit length**, so it can
only ever see an `O(σ)` axial slice of a cone whose axial extent is `≈ 1`, and `⌊1/(6σ)⌋` slices
are needed; `Kakeya.LooseUniform.LooseUniformTubeSet.boundedOverlapDil` is stated against a
**dilate**, whose length is `K`, and one of those covers the whole cone
(`Kakeya.LooseUniform.cone_tube_le_dilate`).  Enlarging the radius does not help: a `Tube (2σ)`
still has unit length, so the same count applies at every radius. -/
theorem exists_bush_forcing_dilate_cover {δ σ : NNReal} (hσ : 0 < (σ : ℝ))
    (hδσ : 4 * (δ : ℝ) ≤ σ) (x v : E3) (hv : ‖v‖ = 1) :
    ∃ V : Tube σ E3,
      ∀ (M : ℕ) (W : Fin M → Tube σ E3),
        (∀ T : Tube δ E3, x ∈ T.carrier → T.direction = V.direction →
          T.toConvexSpaceBody ≤ Kakeya.Tube.dilate V 4 →
          ∃ m, T.toConvexSpaceBody ≤ (W m).toConvexSpaceBody) →
        ⌊1 / (6 * (σ : ℝ))⌋₊ ≤ M := by
  classical
  obtain ⟨T, V, hx, hdir, hpair, hle⟩ :=
    bush_obstruction hδσ x v hv ⌊1 / (6 * (σ : ℝ))⌋₊ (sp := 3 * (σ : ℝ)) (by linarith) (by
      have hfl : ((⌊1 / (6 * (σ : ℝ))⌋₊ : ℕ) : ℝ) ≤ 1 / (6 * (σ : ℝ)) :=
        Nat.floor_le (by positivity)
      calc ((⌊1 / (6 * (σ : ℝ))⌋₊ : ℕ) : ℝ) * (3 * (σ : ℝ))
          ≤ (1 / (6 * (σ : ℝ))) * (3 * (σ : ℝ)) :=
            mul_le_mul_of_nonneg_right hfl (by linarith)
        _ = 1 / 2 := by field_simp; ring)
  refine ⟨V, fun M W hcov => ?_⟩
  choose f hf using fun i => hcov (T i) (hx i) (hdir i) (hle i)
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact hpair i j hne ⟨W (f i), hf i, by rw [hij]; exact hf j⟩
  simpa using Fintype.card_le_of_injective f hinj

end LooseUniform

end Kakeya
