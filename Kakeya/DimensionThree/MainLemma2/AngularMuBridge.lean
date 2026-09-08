/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.LooseUniform

/-!
# Conjunct 6 from GWZ's own object: the angular multiplicity function `μ(ρ)`

Conjunct 6 of `Kakeya.VeryNotSticky.SideDataObligations` is GWZ's composed angular bound
(`gwz.txt` l.2321-2322): the tubes of `𝕋_Y(x)` within angle `ρ₂*` of an arbitrary direction
number at most `Cang` times the multiplicity of the class of an active level-`k` node.  GWZ
derive it from **two** facts, and the tree already owns the harder one:

* **(86)** (`gwz.txt` l.1984-1993) — the *per-point angular uniformity*: after a refinement of the
  shading alone, `#{T ∈ 𝕋_{Y'}(x) : ∠(T, T₀) ≤ ρ} ≈ μ(ρ)` for **every** `T₀ ∈ 𝕋` and every
  `x ∈ Y'(T₀)`.  In the tree this is `Kakeya.VeryNotSticky.IsAngularMultiplicity`, and it is
  **produced** — with GWZ's own mass retention `ShadedBody.IsCRefinement` at `δ^η ≤ c ≤ 1` and
  with `1 ≤ C ≤ δ^{-η}` — by the existing, axiom-clean theorem
  `Kakeya.VeryNotSticky.exists_angularMultiplicity`, for **every** configuration below a
  threshold depending on `η` alone.  Nothing in this file re-proves it.
* **`gwz.txt` l.1993** — the *identification* `μ(𝕋[T_ρ], Y') ≈ μ(ρ)`: the angular multiplicity
  at scale `ρ` is comparable to the shading multiplicity of a parent's fibre.  This is **not**
  in the tree, and the docstring of `exists_angularMultiplicity` says so ("Neither
  `murhoTwoScale` nor the comparison of `μ(𝕋, Y')` with `μ(1)` is part of this existence
  statement").

This file compiles the reduction of conjunct 6 to those two, in the **existing vocabulary**
(`cfg.angularFibre`, `cfg.activeTubeNodes cfg.splitHierarchy k`,
`cfg.tubeFibre cfg.splitHierarchy k j`) and with **no loose hierarchy anywhere**.  Concretely:

* `Kakeya.VeryNotSticky.branchingN_le_multiplicity_of_shadedUniform` — the *lower* half of
  l.1993 is free from the Definition-2.2 datum the configuration already carries
  (`Kakeya.VeryNotSticky.uniform`): the multiplicity of an **active** class is at least
  `𝒱.branchingN k / C²`.  This is the second half of the proof of
  `Kakeya.LooseUniform.angularCone_card_le_of_loose`, read on the **exact** datum, where it is
  equally valid — the loose model is needed only for the *covering* half, which (86) replaces.
* `Kakeya.VeryNotSticky.angularFibre_card_le_fibreMult_of_mu` — the composition.  Conjunct 6's
  inequality holds with `Cang = C_μ · C₁ · C²`, where `C_μ` is (86)'s constant and `C₁` is the
  constant of the **single remaining scalar hypothesis**

  `μ (2 ρ) ≤ C₁ · 𝒱.branchingN k`.

  That hypothesis is exactly l.1993's upper half in the tree's vocabulary: the angular branching
  number at the scale `2ρ` is at most `C₁` times the shading branching number of the
  Definition-2.2 datum at the grid level `k`.
* `Kakeya.VeryNotSticky.eventually_conjunct6_of_angularMultiplicity` — conjunct 6 of
  `Kakeya.VeryNotSticky.SideDataObligations` **verbatim**, conditional on (86) at the
  configuration's own shading, on that scalar hypothesis, on `2ρ₂* ≤ 1`, and on the budget
  `C_μ · C₁ · C₀² ≤ δ^{-η}`.
* `Kakeya.VeryNotSticky.two_mul_rho2Star_le_one` — the side condition `2ρ₂* ≤ 1`, from the
  threshold of `Kakeya.VeryNotSticky.rho2Star_range` with `4` in place of `2`.

## What this does and does not discharge

It **discharges nothing** on its own: (86) is produced only on a *refinement* `Y'` of the
configuration's shading, so using it at the configuration's own shading is the "abusing
notation" step of `gwz.txt` l.1993 and must be threaded through the configuration rebuild, and the scalar hypothesis `μ (2ρ) ≤ C₁ · 𝒱.branchingN k` has no
producer anywhere in the tree.  What it does establish, by the compiler, is that **the residue
of conjunct 6 beyond GWZ's own (86) is one scalar comparison between two branching numbers**,
not a hierarchy: no sparse net, no loose multiscale tree, no pruning adaptation and no joint
fixed point.

**Nothing here changes, weakens or restates any existing declaration.**  Every statement is new
and every existing name it mentions is used, not modified.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

open scoped NNReal ENNReal

namespace Kakeya

namespace VeryNotSticky

universe u

/-! ### The lower half of `gwz.txt` l.1993, from the exact Definition-2.2 datum -/

open scoped Classical in
/-- **The multiplicity of an active class is at least `branchingN k / C²`.**

`ShadedTube.ShadedUniformTubeSet.le_card_shadeClass` bounds `localN x k` by `C` times the number
of class members shading `x`, and `branchingN_le` bounds `branchingN k` by `C · localN x k`;
the two together bound the *pointwise* multiplicity of the class from below at **every** point
of the union of its shades, and `ShadedBody.le_multiplicity_of_le_pointwiseMultiplicity`
integrates that to the multiplicity.  Activity of the node is what makes the union nonempty of
positive measure (`Kakeya.VeryNotSticky.volume_shade_ne_zero`).

This is the second half of the proof of `Kakeya.LooseUniform.angularCone_card_le_of_loose` (PC),
read on the **exact** datum.  Nothing loose is used: the two brackets it consumes have the same
statement in both models, and the loose model is needed only for the covering half — which,
on the route of this file, GWZ's `μ(ρ)` supplies instead. -/
theorem branchingN_le_multiplicity_of_shadedUniform (cfg : VeryNotSticky.{u}) {N : ℕ} {C : NNReal}
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T N C) (hC : 1 ≤ C)
    {k : ℕ} (hk : k ≤ N) {j : cfg.ι} (hj : j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k) :
    ((𝒱.branchingN k : NNReal) : ENNReal) ≤ (C : ENNReal) ^ 2 *
      ShadedBody.multiplicity (cfg.tubeFibre 𝒱.tubeUniform k j)
        (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  set G := 𝒱.tubeUniform.cover with hG
  set F := cfg.tubeFibre 𝒱.tubeUniform k j with hF
  have hFeq : F = Tube.coverClass cfg.s (G.assign k) j := rfl
  have hFs : F ⊆ cfg.s := fun i hi => (Finset.mem_filter.mp hi).1
  have hjne : F.Nonempty := (Finset.mem_filter.mp hj).2
  have hne : volume (⋃ i ∈ F, ((fun i ↦ (cfg.T i).toShadedBody) i).shade) ≠ 0 := by
    obtain ⟨i', hi'⟩ := hjne
    intro h0
    exact cfg.volume_shade_ne_zero (hFs hi') (measure_mono_null (Set.subset_iUnion₂
      (s := fun i _ => ((fun i ↦ (cfg.T i).toShadedBody) i).shade) i' hi') h0)
  have hC0 : (C : ENNReal) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hC).ne'
  have hC2 : ((C : ENNReal) ^ 2) ≠ 0 := pow_ne_zero _ hC0
  have hC2top : ((C : ENNReal) ^ 2) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hpt : ∀ y ∈ ⋃ i ∈ F, ((fun i ↦ (cfg.T i).toShadedBody) i).shade,
      (𝒱.branchingN k : ENNReal) / (C : ENNReal) ^ 2 ≤
        (ShadedBody.pointwiseMultiplicity F (fun i ↦ (cfg.T i).toShadedBody) y : ENNReal) := by
    intro y hy
    obtain ⟨i', hi', hyi'⟩ := Set.mem_iUnion₂.mp hy
    have hi's : i' ∈ cfg.s := hFs hi'
    have hji' : G.assign k i' = j := (Finset.mem_filter.mp hi').2
    have hyi'' : y ∈ (cfg.T i').shade := hyi'
    have hyU : y ∈ ⋃ i ∈ cfg.s, (cfg.T i).shade := Set.mem_iUnion₂.mpr ⟨i', hi's, hyi''⟩
    have h1 := 𝒱.le_card_shadeClass y hyU k hk i' hi's hyi''
    have h2 := 𝒱.branchingN_le y hyU k hk
    rw [hji'] at h1
    have hcard : (ShadedTube.shadeClass cfg.s cfg.T (G.assign k) j y).card =
        ShadedBody.pointwiseMultiplicity F (fun i ↦ (cfg.T i).toShadedBody) y := by
      simp only [ShadedTube.shadeClass, ShadedBody.pointwiseMultiplicity, hFeq]
    have hNN : 𝒱.branchingN k ≤
        C ^ 2 * (ShadedBody.pointwiseMultiplicity F
          (fun i ↦ (cfg.T i).toShadedBody) y : NNReal) := by
      rw [← hcard]
      calc 𝒱.branchingN k ≤ C * 𝒱.localN y k := h2
        _ ≤ C * (C * ((ShadedTube.shadeClass cfg.s cfg.T (G.assign k) j y).card : NNReal)) := by
            gcongr
        _ = C ^ 2 * ((ShadedTube.shadeClass cfg.s cfg.T (G.assign k) j y).card : NNReal) := by
            ring
    rw [ENNReal.div_le_iff hC2 hC2top, mul_comm]
    exact_mod_cast hNN
  have hlow := ShadedBody.le_multiplicity_of_le_pointwiseMultiplicity F
    (fun i ↦ (cfg.T i).toShadedBody) hne hpt
  calc ((𝒱.branchingN k : NNReal) : ENNReal)
      = (C : ENNReal) ^ 2 * ((𝒱.branchingN k : ENNReal) / (C : ENNReal) ^ 2) :=
        (ENNReal.mul_div_cancel hC2 hC2top).symm
    _ ≤ (C : ENNReal) ^ 2 * ShadedBody.multiplicity F
          (fun i ↦ (cfg.T i).toShadedBody) := by gcongr

/-! ### The composition: (86) plus one scalar comparison give conjunct 6's inequality -/

open scoped Classical in
/-- **Conjunct 6's inequality from GWZ's `μ(ρ)`.**

`Kakeya.VeryNotSticky.angularFibre_card_le_mul_mu` — which is
`Kakeya.VeryNotSticky.angularInnerCount` (the passage from an arbitrary direction `v` to a tube
`T₀` shading `x`, at the doubled angle) composed with (86) — bounds the angular fibre by
`C_μ · μ(2ρ)`; the hypothesis `hlow` converts `μ(2ρ)` into the Definition-2.2 branching number;
and `Kakeya.VeryNotSticky.branchingN_le_multiplicity_of_shadedUniform` converts that into the
multiplicity of the class.  The empty-fibre case is inside
`Kakeya.VeryNotSticky.angularInnerCount`.

`hlow` is the only hypothesis with no producer in the tree.  It is the upper half of
`gwz.txt` l.1993 (`μ(𝕋[T_ρ], Y) ≈ μ(ρ)`) in the tree's vocabulary. -/
theorem angularFibre_card_le_fibreMult_of_mu (cfg : VeryNotSticky.{u}) {N : ℕ} {C Cmu C₁ : NNReal}
    {μ : ℝ → NNReal}
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T N C) (hC : 1 ≤ C)
    (ham : cfg.IsAngularMultiplicity (fun i ↦ (cfg.T i).toShadedBody) Cmu μ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hδ : (cfg.δ : ℝ) ≤ 2 * ρ) (hone : 2 * ρ ≤ 1)
    {k : ℕ} (hk : k ≤ N) (hlow : μ (2 * ρ) ≤ C₁ * 𝒱.branchingN k)
    {j : cfg.ι} (hj : j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k)
    (x v : EuclideanSpace ℝ (Fin 3)) :
    (((cfg.angularFibre x v ρ).card : ℕ) : ENNReal) ≤
      ((Cmu * C₁ * C ^ 2 : NNReal) : ENNReal) *
        ShadedBody.multiplicity (cfg.tubeFibre 𝒱.tubeUniform k j)
          (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  have h1 : (((cfg.angularFibre x v ρ).card : ℕ) : NNReal) ≤ Cmu * μ (2 * ρ) :=
    cfg.angularFibre_card_le_mul_mu ham x v hρ hδ hone
  have h2 : (((cfg.angularFibre x v ρ).card : ℕ) : NNReal) ≤ Cmu * C₁ * 𝒱.branchingN k := by
    calc (((cfg.angularFibre x v ρ).card : ℕ) : NNReal) ≤ Cmu * μ (2 * ρ) := h1
      _ ≤ Cmu * (C₁ * 𝒱.branchingN k) := by gcongr
      _ = Cmu * C₁ * 𝒱.branchingN k := by ring
  have h3 : (((cfg.angularFibre x v ρ).card : ℕ) : ENNReal) ≤
      ((Cmu * C₁ : NNReal) : ENNReal) * ((𝒱.branchingN k : NNReal) : ENNReal) := by
    have := (ENNReal.coe_le_coe.mpr h2)
    simpa [ENNReal.coe_mul] using this
  calc (((cfg.angularFibre x v ρ).card : ℕ) : ENNReal)
      ≤ ((Cmu * C₁ : NNReal) : ENNReal) * ((𝒱.branchingN k : NNReal) : ENNReal) := h3
    _ ≤ ((Cmu * C₁ : NNReal) : ENNReal) * ((C : ENNReal) ^ 2 *
          ShadedBody.multiplicity (cfg.tubeFibre 𝒱.tubeUniform k j)
            (fun i ↦ (cfg.T i).toShadedBody)) := by
        gcongr
        exact cfg.branchingN_le_multiplicity_of_shadedUniform 𝒱 hC hk hj
    _ = ((Cmu * C₁ * C ^ 2 : NNReal) : ENNReal) *
          ShadedBody.multiplicity (cfg.tubeFibre 𝒱.tubeUniform k j)
            (fun i ↦ (cfg.T i).toShadedBody) := by push_cast; ring

/-! ### The angular side condition `2 ρ₂* ≤ 1` -/

/-- **`2ρ₂* ≤ 1`.**  `Kakeya.VeryNotSticky.rho2Star_range` proves `ρ₂* ≤ 1` from the fixed-scale
threshold `δ^{exscal} ≤ (2 C_{lem:ml2bodyAngle}(C₀))⁻¹`; the same three lines with `4` in place
of `2` give the doubled form, which is what
`Kakeya.VeryNotSticky.angularFibre_card_le_mul_mu` needs at the angular scale `ρ₂*` itself
(rather than at `ρ₂*/2`, the scale `Kakeya.VeryNotSticky.rho2Star_range` prepares).  The cost is
a factor `2` in a threshold on `δ`, nothing else. -/
theorem two_mul_rho2Star_le_one (cfg : VeryNotSticky.{u}) (hδ : 0 < cfg.δ)
    {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    (hscale : cfg.δ ^ cfg.exscal ≤ (4 * NonSlab.bodyAngleConstant C₀)⁻¹)
    (hnotslab : cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁) :
    2 * cfg.rho2Star C₀ ≤ 1 := by
  have hr₁0 : 0 < cfg.r₁ := NNReal.rpow_pos hδ
  have h4le : (4 : NNReal) ≤ 4 * NonSlab.bodyAngleConstant C₀ := by
    simpa using mul_le_mul_right (NonSlab.one_le_bodyAngleConstant hC₀) 4
  have hne : (4 * NonSlab.bodyAngleConstant C₀) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) h4le)
  calc 2 * cfg.rho2Star C₀ = (4 * NonSlab.bodyAngleConstant C₀) * cfg.rho2 := by
        simp only [VeryNotSticky.rho2Star]; ring
    _ ≤ (4 * NonSlab.bodyAngleConstant C₀) * (cfg.δ ^ cfg.exscal) :=
        mul_le_mul_right ((div_le_iff₀ hr₁0).2 hnotslab) _
    _ ≤ (4 * NonSlab.bodyAngleConstant C₀) * (4 * NonSlab.bodyAngleConstant C₀)⁻¹ :=
        mul_le_mul_right hscale _
    _ = 1 := mul_inv_cancel₀ hne

/-! ### The low-cardinality branch: conjunct 6 outright, no hypotheses beyond `|𝕋| ≤ δ^{-η}` -/

open scoped Classical in
/-- **The multiplicity of an active class is at least `1`.**  Its members' shades have positive
volume (`Kakeya.VeryNotSticky.volume_shade_ne_zero`), so `ShadedBody.one_le_multiplicity`
applies. -/
theorem one_le_multiplicity_tubeFibre (cfg : VeryNotSticky.{u}) {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C)
    {k : ℕ} {j : cfg.ι} (hj : j ∈ cfg.activeTubeNodes 𝒰 k) :
    1 ≤ ShadedBody.multiplicity (cfg.tubeFibre 𝒰 k j) (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  obtain ⟨i₀, hi₀⟩ : (cfg.tubeFibre 𝒰 k j).Nonempty := (Finset.mem_filter.mp hj).2
  refine ShadedBody.one_le_multiplicity _ _ (fun hall => ?_)
  exact cfg.volume_shade_ne_zero (Finset.mem_filter.mp hi₀).1 (hall i₀ hi₀)

open scoped Classical in
/-- **Conjunct 6 of `Kakeya.VeryNotSticky.SideDataObligations` on the low-cardinality branch,
unconditionally.**

If `|𝕋| ≤ δ^{-η}` then `Cang := |𝕋|` works: the angular fibre is a subfamily of `𝕋` and the
class of an *active* node has multiplicity at least `1`.  No angular hypothesis, no hierarchy,
no refinement.  This is the elementary branch that
`Kakeya.VeryNotSticky.exists_isAngularMultiplicity_of_card_le` already isolates for `μ`.

It is also the **firing control** for the whole clause: conjunct 6's conclusion is satisfiable,
so a `∀`-quantified consumer of it is not reasoning about an empty set of witnesses.  On Lemma
9.1's own configurations the branch is expected to be vacuous — `eventually_card_of_count` puts
`|𝕋|` above `δ^{-1-α}` — so this discharges conjunct 6 only where it is easy, and the
high-cardinality branch is the one the rest of this file addresses. -/
theorem exists_Cang_angularFibre_le_of_card_le (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (hcard : (cfg.s.card : NNReal) ≤ cfg.δ ^ (-cfg.η)) (k : ℕ) :
    ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
      ∀ j ∈ cfg.activeTubeNodes cfg.splitHierarchy k,
        ∀ x v : EuclideanSpace ℝ (Fin 3),
          (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
            (Cang : ENNReal) *
              ShadedBody.multiplicity (cfg.tubeFibre cfg.splitHierarchy k j)
                (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  refine ⟨(cfg.s.card : NNReal), ?_, ?_⟩
  · calc ((cfg.s.card : NNReal) : ENNReal) ≤ ((cfg.δ ^ (-cfg.η) : NNReal) : ENNReal) :=
        ENNReal.coe_le_coe.mpr hcard
      _ = (cfg.δ : ENNReal) ^ (-cfg.η) := ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne' _
  · intro j hj x v
    have hsub : cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ) ⊆ cfg.s :=
      fun i hi => (Finset.mem_filter.mp hi).1
    have hcard' : (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
        ((cfg.s.card : NNReal) : ENNReal) := by
      exact_mod_cast Finset.card_le_card hsub
    calc (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal)
        ≤ ((cfg.s.card : NNReal) : ENNReal) := hcard'
      _ = ((cfg.s.card : NNReal) : ENNReal) * 1 := (mul_one _).symm
      _ ≤ ((cfg.s.card : NNReal) : ENNReal) *
            ShadedBody.multiplicity (cfg.tubeFibre cfg.splitHierarchy k j)
              (fun i ↦ (cfg.T i).toShadedBody) := by
          gcongr
          exact cfg.one_le_multiplicity_tubeFibre cfg.splitHierarchy hj

/-! ### Conjunct 6 of `SideDataObligations`, verbatim, from (86) -/

open scoped Classical in
/-- **Conjunct 6's `∃ Cang` clause, at the configuration's own Definition-2.2 datum.**

`cfg.splitHierarchy` is by definition `cfg.uniform.some.tubeUniform`, so the class and the
active-node set here are literally conjunct 6's.  `hbud` is the budget: conjunct 6 asks for
`Cang ≤ δ^{-η}`, and the route delivers `Cang = C_μ · C₁ · C₀²`.  Since
`Kakeya.VeryNotSticky.coe_C₀_pow_eight_le_rpow_neg_eta` spends the whole `δ^{-η}` on `C₀^8`
alone, closing at `δ^{-η}` is an exponent re-budget across the three factors, not a further
mathematical obligation; the budget is left explicit rather than fixed here so that the
re-budget stays the caller's. -/
theorem exists_Cang_angularFibre_le_of_mu (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    {Cmu C₁ : NNReal} {μ : ℝ → NNReal}
    (ham : cfg.IsAngularMultiplicity (fun i ↦ (cfg.T i).toShadedBody) Cmu μ)
    (hone : 2 * (cfg.rho2Star bd.C₀ : ℝ) ≤ 1)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hlow : μ (2 * (cfg.rho2Star bd.C₀ : ℝ)) ≤ C₁ * cfg.uniform.some.branchingN k)
    (hbud : ((Cmu * C₁ * cfg.C₀ ^ 2 : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η)) :
    ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
      ∀ j ∈ cfg.activeTubeNodes cfg.splitHierarchy k,
        ∀ x v : EuclideanSpace ℝ (Fin 3),
          (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
            (Cang : ENNReal) *
              ShadedBody.multiplicity (cfg.tubeFibre cfg.splitHierarchy k j)
                (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  have hδ2 : (cfg.δ : ℝ) ≤ 2 * (cfg.rho2Star bd.C₀ : ℝ) := by
    have h4 : 4 * (cfg.δ : ℝ) ≤ (cfg.rho2Star bd.C₀ : ℝ) :=
      cfg.four_mul_delta_le_rho2Star bd.hC₀
    have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := cfg.δ.coe_nonneg
    linarith
  have hρ0 : (0 : ℝ) ≤ (cfg.rho2Star bd.C₀ : ℝ) := (cfg.rho2Star bd.C₀).coe_nonneg
  refine ⟨Cmu * C₁ * cfg.C₀ ^ 2, hbud, ?_⟩
  intro j hj x v
  exact cfg.angularFibre_card_le_fibreMult_of_mu cfg.uniform.some cfg.hC₀ ham hρ0 hδ2 hone hk
    hlow hj x v

open scoped Classical in
/-- **Conjunct 6 of `Kakeya.VeryNotSticky.SideDataObligations`, verbatim**, conditional on GWZ's
`μ(ρ)` at the configuration's own shading, on the scalar comparison `hlow`
(= `gwz.txt` l.1993, upper half), on `2ρ₂* ≤ 1` and on the budget.

Compare `Kakeya.VeryNotSticky.eventually_conjunct6_of_looseUniform`, which reaches the same
conclusion from a loose Definition-2.2 hierarchy on `cfg.s` — an object with no producer and,
per , a ≈3-5k-line one.  The hypotheses here are (86), which **is** produced
(`Kakeya.VeryNotSticky.exists_angularMultiplicity`, on a `⪆1` refinement of the shading), plus
one inequality between two numbers. -/
theorem eventually_conjunct6_of_angularMultiplicity {exscal ϱ η : ℝ} (C₀bd : NNReal) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = d → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      ∀ (Cmu C₁ : NNReal) (μ : ℝ → NNReal),
        cfg.IsAngularMultiplicity (fun i ↦ (cfg.T i).toShadedBody) Cmu μ →
        2 * (cfg.rho2Star bd.C₀ : ℝ) ≤ 1 →
        ((Cmu * C₁ * cfg.C₀ ^ 2 : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) →
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        μ (2 * (cfg.rho2Star bd.C₀ : ℝ)) ≤ C₁ * cfg.uniform.some.branchingN k →
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
  Filter.Eventually.of_forall fun _ cfg bd _ _ _ _ _ _ _ _ _ ham hone hbud _ hk hlow _ _ ↦
    cfg.exists_Cang_angularFibre_le_of_mu bd ham hone hk hlow hbud

end VeryNotSticky

end Kakeya
