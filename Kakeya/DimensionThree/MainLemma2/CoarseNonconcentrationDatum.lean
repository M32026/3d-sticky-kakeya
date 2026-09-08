/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.AScaleGuardrails

/-!
# The non-concentration datum of the Section-5 residue: siting it, and the tests it must pass

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` is the Section-5 residue.  Its two
conjuncts pull on the same quantity from opposite sides, and the difficulty is entirely in the
ball conjunct.  This file names the exact datum that closes it, proves the closure **verbatim**
— at the residue's own placeholder constant, with no restatement — and then runs on that exact
wording the two tests a candidate structure field has to pass before it may be added:

* the **re-encoding test**: is the datum a multiplicity bound in disguise?
* the **budget test**: does the datum *buy* anything against the loss budget the configuration
  already grants, or is it short by a power of `δ`?

The verdicts are recorded as theorems, not as prose.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

universe u

open MeasureTheory Metric Set ShadedBody
open scoped ENNReal NNReal

/-! ## The datum -/

/-- **The non-concentration datum of the Section-5 residue**, with all binders explicit.

This is the ball conjunct of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` read at the
*saturated* coarse shading, i.e. with the outer shaded union replaced by the union of the node
carriers `⋃ 𝕋_ρ`.  It is a statement about the configuration and its hierarchy alone: no shaded
factor family occurs in it.

It is strictly weaker than the `∀ x` form: the centre `x` is restricted to `⋃ 𝕋_ρ`, which is
where the residue's own ball conjunct quantifies it. -/
def CoarseBallNonconcentration (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    (k : ℕ) (ρ : NNReal) : Prop :=
  ∀ x ∈ ⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier,
    (cfg.δ : ENNReal) ^ cfg.η *
        (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
            volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
              (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) *
          (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
            volume (ball x (ρ : ℝ)))) ≤
      volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)

/-! ## The datum closes the residue, verbatim -/

/-- **THE RESIDUE, CLOSED FROM THE DATUM — AT ITS OWN CONSTANT, WITH NO RESTATEMENT.**

Every conjunct of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` is reproduced here
character for character, including the placeholder loss constant
`ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1`.  The only difference from the
sorried statement is the added hypothesis `hnc`.

The witness is the *saturated* coarse shading of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_saturated`, whose outer fullness is `1`
and therefore clears the fullness conjunct at every loss constant `≥ 1`, in particular at the
placeholder.  Its outer shaded union is contained in `⋃ 𝕋_ρ`, so the ball conjunct is `hnc`
together with monotonicity of `volume` — no constant is spent, and nothing is restated.

Two consequences worth stating separately.  First, no companion repair of
`Kakeya.DimensionThree.MainLemma2.AScaleConstants` is needed: the datum closes the residue at
the constant the tree already carries, so the tripwire
`Kakeya.VeryNotSticky.RepairedCoarseShadedFamilyStatement` survives byte for byte.  Second,
the difficulty of the residue is *exactly* `hnc`: it is sufficient here, and
`Kakeya.VeryNotSticky.coarseBallNonconcentration_forces_shading_budget` below records what
it costs. -/
theorem exists_coarseShadedFamilyAtGrid_of_coarseBallNonconcentration (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1)
    (hnc : CoarseBallNonconcentration cfg 𝒱 k ρ) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  obtain ⟨G, hinner, hbody, houterSet, houterBody, hfull⟩ :=
    exists_coarseShadedFamilyAtGrid_saturated cfg 𝒱 hk
  -- the inner shaded union of `G` is the configuration's own
  have hUin : (⋃ i ∈ G.innerSet, (G.innerBody i).shade)
      = ⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade := by
    rw [hinner]
    refine Set.iUnion_congr fun i => Set.iUnion_congr fun hi => ?_
    rw [hbody i hi]
  -- the outer shaded union of `G` sits inside the union of the node carriers
  have hUout : (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
      ⊆ ⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier := by
    intro y hy
    obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.1 hy
    refine Set.mem_biUnion (houterSet ▸ hj) ?_
    have hcar : (G.outerBody j).carrier
        = (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier :=
      congrArg ConvexSpaceBody.carrier (houterBody j hj)
    exact hcar ▸ (G.outerBody j).shade_subset hyj
  refine ⟨G, hinner, hbody, houterSet, houterBody, ?_, ?_⟩
  · rw [shadingMultiplicityEstimateForRhoTubes.C, mul_one]
    exact hfull
  · intro x hx
    have hxmem := hUout hx
    rw [hUin]
    refine le_trans ?_ (hnc x hxmem)
    gcongr

/-! ## The universal form, and the pin to the residue's exact statement

A tripwire that reads a *field* cannot survive that field changing, so the statement under test
is hoisted into a `Prop` of its own — the `Kakeya.ThinCase.Refute.statement_of_universal_loc`
shape that `Kakeya.VeryNotSticky.RigidFullnessField` uses for the same reason.
-/

/-- The datum in universal form: what a field of `Kakeya.VeryNotSticky` asserting it would
say, hoisted out of the structure. -/
def UniversalCoarseBallNonconcentration : Prop :=
  ∀ (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    (k : ℕ), k ≤ Tube.ssfGridLen cfg.δ →
    ∀ ρ : NNReal, Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ →
    ρ ∈ Set.Icc cfg.δ 1 → CoarseBallNonconcentration cfg 𝒱 k ρ

/-- **The datum, universally, gives the residue on the nose.**

The right-hand side is `Kakeya.VeryNotSticky.RepairedCoarseShadedFamilyStatement`, the `Prop`
that `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` is pinned to by the tripwire in
`Kakeya.DimensionThree.MainLemma2.AScaleGuardrails`.  So this line is the mechanical statement
that the datum closes the residue *as it stands*: if the residue's statement ever drifts, this
stops elaborating. -/
theorem repairedCoarseShadedFamilyStatement_of_universal
    (H : UniversalCoarseBallNonconcentration.{u}) :
    RepairedCoarseShadedFamilyStatement.{u} := by
  intro cfg 𝒱 k hk ρ hgrid hρ
  exact exists_coarseShadedFamilyAtGrid_of_coarseBallNonconcentration cfg 𝒱 hk hgrid hρ
    (H cfg 𝒱 k hk ρ hgrid hρ)

/-! ## The re-encoding test, run on the exact wording above

The standing test of this run: before adding a datum, ask whether it is the conclusion in
disguise.  Round 7 of  ran it on the *sum* form `a · ∑_j |T_{ρ,j}| ≤ |U(𝕋, Y)|` and it
came back positive — that hypothesis is equivalent to a multiplicity bound, and at the top grid
index to an absolute one.  The datum above is the *union* form.  The three theorems in this
section locate the difference exactly, and it is not a matter of taste: the sum form implies the
datum unconditionally, while the converse costs precisely one bound on the **coarse family's own
multiplicity** `µ(𝕋_ρ) = (∑_j |T_{ρ,j}|)/|⋃_j T_{ρ,j}|`, a quantity no field of
`Kakeya.VeryNotSticky` constrains.
-/

/-- The **coarse node multiplicity** `µ(𝕋_ρ)` at grid level `k`: the multiplicity of the node
family shaded by the whole of each node tube, `Kakeya.VeryNotSticky.fullyShadedNodeFamily`. -/
noncomputable def coarseNodeMultiplicity (cfg : VeryNotSticky.{u})
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) cfg.C₀)
    (k : ℕ) : ENNReal :=
  ShadedBody.multiplicity (cfg.fullyShadedNodeFamily 𝒰 k).outerSet
    (cfg.fullyShadedNodeFamily 𝒰 k).outerBody

/-- `∑_j |T_{ρ,j}| = µ(𝕋_ρ) · |⋃_j T_{ρ,j}|`: the sum and the union of the node carriers differ
by exactly the coarse family's own multiplicity.  This is the whole of the difference between
the refuted sum form and the datum. -/
theorem sum_volume_nodeCarrier_eq_coarseNodeMultiplicity_mul (cfg : VeryNotSticky.{u})
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ) :
    ∑ j ∈ cfg.activeTubeNodes 𝒰 k, volume (𝒰.cover.tube k j).toConvexSpaceBody.carrier
      = cfg.coarseNodeMultiplicity 𝒰 k *
        volume (⋃ j ∈ cfg.activeTubeNodes 𝒰 k,
          (𝒰.cover.tube k j).toConvexSpaceBody.carrier) := by
  classical
  set G := cfg.fullyShadedNodeFamily 𝒰 k with hG
  have hshade : ∀ j, (G.outerBody j).shade
      = (𝒰.cover.tube k j).toConvexSpaceBody.carrier := fun _ => rfl
  have hout : G.outerSet = cfg.activeTubeNodes 𝒰 k := rfl
  have hU : (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
      = ⋃ j ∈ cfg.activeTubeNodes 𝒰 k,
          (𝒰.cover.tube k j).toConvexSpaceBody.carrier := rfl
  have hsum : (∑ j ∈ G.outerSet, volume (G.outerBody j).shade)
      = ∑ j ∈ cfg.activeTubeNodes 𝒰 k,
          volume (𝒰.cover.tube k j).toConvexSpaceBody.carrier := rfl
  have hU0 : volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) ≠ 0 := by
    obtain ⟨j, hj⟩ := activeTubeNodes_nonempty cfg 𝒰 hk (s_nonempty cfg)
    intro h0
    refine absurd (measure_mono_null (fun y hy => Set.mem_biUnion (hout ▸ hj) ?_) h0)
      (ne_of_gt (volume_nodeTube_pos cfg 𝒰 k j))
    exact hy
  have hUtop : volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) ≠ ⊤ :=
    ShadedBody.volume_iUnion_shade_ne_top _ _
  rw [← hsum, ← hU, coarseNodeMultiplicity, ← hG, ShadedBody.multiplicity_eq_div]
  exact (ENNReal.div_mul_cancel hU0 hUtop).symm

/-- **Direction 1 of the test: the refuted *sum* form implies the datum, unconditionally.**

`Kakeya.VeryNotSticky.multiplicity_le_of_coarseVolumeComparison` records that a hypothesis of
the shape `δ^η · ∑_j |T_{ρ,j}| ≤ |U(𝕋, Y)|` is a multiplicity bound in disguise, and 's
round 7 showed that at the top grid index it is an *absolute* one.  That hypothesis gives the
datum in one line, because the union is at most the sum and the ball density is at most `1`.

So the datum is **weaker** than the refuted form.  How much weaker is the next theorem. -/
theorem coarseBallNonconcentration_of_sum_le (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    (k : ℕ) (ρ : NNReal)
    (hsum : (cfg.δ : ENNReal) ^ cfg.η *
        ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          volume (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier
      ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)) :
    CoarseBallNonconcentration cfg 𝒱 k ρ := by
  classical
  intro x _
  refine le_trans ?_ hsum
  have hden : volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
      volume (ball x (ρ : ℝ)) ≤ 1 := by
    refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul]
    exact measure_mono Set.inter_subset_right
  have hUsum : volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
        (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
      ≤ ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          volume (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier :=
    measure_biUnion_finset_le _ _
  rw [shadingMultiplicityEstimateForRhoTubes.C]
  calc (cfg.δ : ENNReal) ^ cfg.η *
        (((1 : NNReal) : ENNReal)⁻¹ *
            volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
              (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) *
          (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
            volume (ball x (ρ : ℝ))))
      ≤ (cfg.δ : ENNReal) ^ cfg.η *
        (((1 : NNReal) : ENNReal)⁻¹ *
            (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
              volume (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) * 1) := by
        gcongr
    _ = (cfg.δ : ENNReal) ^ cfg.η *
          ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            volume (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier := by
        push_cast
        rw [inv_one, one_mul, mul_one]


/-- **What the datum yields once a density floor is named.**

The datum is an inequality about a *ratio*; on its own it bounds nothing, because the ratio may
be `0`.  Everything the datum implies passes through a **density floor**: a centre `x₀` in
`⋃ 𝕋_ρ` at which the shaded union occupies at least a `γ` fraction of the `ρ`-ball.  Given one,
the datum becomes the lower bound `δ^η · γ · |⋃ 𝕋_ρ| ≤ |U(𝕋, Y)|`.

Naming the floor is the whole content of the re-encoding test: the datum is a lower bound on
`|U(𝕋, Y)|` **only to the extent that a floor is available**, and the tree bounds `γ` below by
nothing at all. -/
theorem le_volume_innerShade_of_coarseBallNonconcentration (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} {ρ : NNReal} (hnc : CoarseBallNonconcentration cfg 𝒱 k ρ)
    {x₀ : EuclideanSpace ℝ (Fin 3)}
    (hx₀ : x₀ ∈ ⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
    (hρ0 : 0 < (ρ : ℝ)) {γ : ENNReal}
    (hγ : γ * volume (ball x₀ (ρ : ℝ)) ≤
      volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x₀ (ρ : ℝ))) :
    (cfg.δ : ENNReal) ^ cfg.η * γ *
        volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
      ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) := by
  classical
  have hB0 : volume (ball x₀ (ρ : ℝ)) ≠ 0 := (Metric.measure_ball_pos volume x₀ hρ0).ne'
  have hBtop : volume (ball x₀ (ρ : ℝ)) ≠ ⊤ :=
    ne_of_lt (MeasureTheory.measure_ball_lt_top (x := x₀) (r := (ρ : ℝ)))
  have hratio : γ ≤ volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x₀ (ρ : ℝ)) /
      volume (ball x₀ (ρ : ℝ)) :=
    (ENNReal.le_div_iff_mul_le (.inl hB0) (.inl hBtop)).2 hγ
  refine le_trans ?_ (hnc x₀ hx₀)
  rw [shadingMultiplicityEstimateForRhoTubes.C]
  push_cast
  rw [inv_one, one_mul]
  calc (cfg.δ : ENNReal) ^ cfg.η * γ *
          volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
      = (cfg.δ : ENNReal) ^ cfg.η *
          (volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) * γ) := by ring
    _ ≤ (cfg.δ : ENNReal) ^ cfg.η *
          (volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
              (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) *
            (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x₀ (ρ : ℝ)) /
              volume (ball x₀ (ρ : ℝ)))) := by gcongr

/-- **Direction 2 of the test: the converse costs exactly a coarse multiplicity bound.**

Given a density floor and a bound `µ(𝕋_ρ) ≤ m` on the coarse family's own multiplicity, the
datum returns the sum form at the constant `δ^η γ / m`.  Together with
`Kakeya.VeryNotSticky.coarseBallNonconcentration_of_sum_le` this is the exact accounting: the
datum and the refuted sum form differ by the two factors `γ` and `m`, and **`m` is the only one
of them that carries multiplicity content**.

So the datum is *not* the refuted hypothesis in disguise.  It becomes that hypothesis only once
`µ(𝕋_ρ)` is bounded — and `µ(𝕋_ρ)` is a lower bound on the volume of `⋃ 𝕋_ρ` in disguise, i.e.
the *unshaded* Kakeya problem at scale `ρ`, which is not what
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge` concludes and is not a field of the
configuration. -/
theorem sum_le_of_coarseBallNonconcentration (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ) {ρ : NNReal}
    (hnc : CoarseBallNonconcentration cfg 𝒱 k ρ)
    {x₀ : EuclideanSpace ℝ (Fin 3)}
    (hx₀ : x₀ ∈ ⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
    (hρ0 : 0 < (ρ : ℝ)) {γ : ENNReal}
    (hγ : γ * volume (ball x₀ (ρ : ℝ)) ≤
      volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x₀ (ρ : ℝ)))
    {m : ENNReal} (hm : cfg.coarseNodeMultiplicity 𝒱.tubeUniform k ≤ m) :
    (cfg.δ : ENNReal) ^ cfg.η * γ *
        ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          volume (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier
      ≤ m * volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) := by
  classical
  have hkey := le_volume_innerShade_of_coarseBallNonconcentration cfg 𝒱 hnc hx₀ hρ0 hγ
  rw [sum_volume_nodeCarrier_eq_coarseNodeMultiplicity_mul cfg 𝒱.tubeUniform hk]
  calc (cfg.δ : ENNReal) ^ cfg.η * γ *
        (cfg.coarseNodeMultiplicity 𝒱.tubeUniform k *
          volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier))
      ≤ (cfg.δ : ENNReal) ^ cfg.η * γ *
        (m * volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)) := by gcongr
    _ = m * ((cfg.δ : ENNReal) ^ cfg.η * γ *
            volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
              (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)) := by ring
    _ ≤ m * volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) := by gcongr

/-- **The multiplicity bound the datum does yield**, in the currency of
`Kakeya.KatzTaoEstimate`, and with its constant written out.

`µ(𝕋, Y) ≤ (∑_i |Y(T_i)|) / (δ^η γ |⋃ 𝕋_ρ|)`.  Compare the conclusion of
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`, `µ ≤ δ^{ν-η} |𝕋|^β`.  The bound here has
`|⋃ 𝕋_ρ|` — a *union*, at most `|B(0,4)|` and at least `|U(𝕋, Y)|` — in the denominator, so it
is an estimate **relative to the coarse union**, not an absolute one.  That is what distinguishes
it from the round-7 verdict on the sum form, where the denominator was `∑_j |T_{ρ,j}|` and the
bound came out absolute. -/
theorem multiplicity_le_of_coarseBallNonconcentration (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} {ρ : NNReal} (hnc : CoarseBallNonconcentration cfg 𝒱 k ρ)
    {x₀ : EuclideanSpace ℝ (Fin 3)}
    (hx₀ : x₀ ∈ ⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
    (hρ0 : 0 < (ρ : ℝ)) {γ : ENNReal}
    (hγ : γ * volume (ball x₀ (ρ : ℝ)) ≤
      volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x₀ (ρ : ℝ))) :
    ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody)
      ≤ (∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).shade) /
        ((cfg.δ : ENNReal) ^ cfg.η * γ *
          volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)) := by
  rw [ShadedBody.multiplicity_eq_div]
  exact ENNReal.div_le_div_left
    (le_volume_innerShade_of_coarseBallNonconcentration cfg 𝒱 hnc hx₀ hρ0 hγ) _

/-! ## The budget test

S9-66A's lesson: "non-vacuous" is not a fidelity certificate — check that the inequality still
*buys* something, by comparing the claimed gain against the loss budget already granted.  Run on
the datum, the comparison is between the `δ^η` the residue's ball conjunct grants and the
shading density `lam`, whose only guarantee is `Kakeya.VeryNotSticky.lam_ge`, `Cd δ^{2η} ≤ lam`.
-/

/-- **What the datum must buy.** With a density floor `γ` in hand, the datum forces

`δ^η · γ · |⋃ 𝕋_ρ| ≤ Cd · lam · ∑_i |T_i|`,

by `Kakeya.VeryNotSticky.shading_ub`.  The right-hand side is the configuration's entire shading
mass; the left is the coarse union discounted by `δ^η`.  So the datum is affordable exactly when
`γ · |⋃ 𝕋_ρ| / ∑_i |T_i| ≤ Cd · lam · δ^{-η}` — and `lam_ge` guarantees only `lam ≥ Cd δ^{2η}`,
i.e. only `Cd² δ^{η}` on the right. -/
theorem coarseBallNonconcentration_forces_shading_budget (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} {ρ : NNReal} (hnc : CoarseBallNonconcentration cfg 𝒱 k ρ)
    {x₀ : EuclideanSpace ℝ (Fin 3)}
    (hx₀ : x₀ ∈ ⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
    (hρ0 : 0 < (ρ : ℝ)) {γ : ENNReal}
    (hγ : γ * volume (ball x₀ (ρ : ℝ)) ≤
      volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x₀ (ρ : ℝ))) :
    (cfg.δ : ENNReal) ^ cfg.η * γ *
        volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
      ≤ (cfg.Cd : ENNReal) *
          ((cfg.lam : ENNReal) * ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).carrier) := by
  classical
  refine le_trans (le_volume_innerShade_of_coarseBallNonconcentration cfg 𝒱 hnc hx₀ hρ0 hγ) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  simpa [mul_assoc] using cfg.shading_ub i hi

/-- **The refutation vector, stated as a criterion.**

If the configuration's whole shading mass is *smaller* than what the datum demands, the datum is
false — not merely unproved.  Combined with the previous theorem this is a complete test: a
configuration refutes the datum exactly when

`Cd · lam · ∑_i |T_i| < δ^η · γ · |⋃ 𝕋_ρ|`

at some grid index, for some centre with density floor `γ`.  Since `lam` may be as small as
`Cd δ^{2η}` (`Kakeya.VeryNotSticky.lam_ge` is a lower bound only, and
`Kakeya.VeryNotSticky.rescaleDensity` shows only `Cd⁻¹ lam` is a quantity of the data), the test
is passed by any configuration whose coarse union, discounted by the achievable density `γ`, is
comparable to its total tube mass.  That is the shape of the obstruction, and it is a
*quantitative* one: the residue's ball conjunct grants `δ^η`, and the shading budget is
`δ^{2η}`. -/
theorem not_coarseBallNonconcentration_of_budget_short (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} {ρ : NNReal} {x₀ : EuclideanSpace ℝ (Fin 3)}
    (hx₀ : x₀ ∈ ⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
    (hρ0 : 0 < (ρ : ℝ)) {γ : ENNReal}
    (hγ : γ * volume (ball x₀ (ρ : ℝ)) ≤
      volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x₀ (ρ : ℝ)))
    (hshort : (cfg.Cd : ENNReal) *
        ((cfg.lam : ENNReal) * ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).carrier)
      < (cfg.δ : ENNReal) ^ cfg.η * γ *
          volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)) :
    ¬ CoarseBallNonconcentration cfg 𝒱 k ρ := fun hnc =>
  absurd (coarseBallNonconcentration_forces_shading_budget cfg 𝒱 hnc hx₀ hρ0 hγ) (not_le.2 hshort)


/-! ## The other direction of the re-encoding test: is the datum derivable *from* Katz–Tao?

`Kakeya.VeryNotSticky.ktEstimate` is a **field** of the configuration, so if the datum followed
from `Kakeya.KatzTaoEstimate` it would be free and no new datum would be needed at all.  The
transport below names the exact constant a Katz–Tao conclusion would have to reach, and the
arithmetic that follows shows it is missed by a full power of `δ`.
-/

/-- **What Katz–Tao would have to supply, and at what constant.**

`Kakeya.KatzTaoEstimate` concludes `∑_i |Y(T_i)| ≤ B · |U(𝕋, Y)|` at `B = δ^{-ε} |𝕋|^β`.  Read
as a lower bound on the shaded union it gives `|U| ≥ B⁻¹ ∑_i |Y(T_i)|`, and the datum needs
`δ^η |⋃ 𝕋_ρ| ≤ |U|`, since the ball density is at most `1`.  So a Katz–Tao conclusion at
constant `B` yields the datum **exactly when** `B · δ^η · |⋃ 𝕋_ρ| ≤ ∑_i |Y(T_i)|`.

*That threshold is missed, and by a full power of `δ`.*  The configuration's whole shading mass
is at most `Cd · lam · ∑_i |T_i| ≤ Cd · lam · δ^{-η} |B_1|`
(`Kakeya.VeryNotSticky.sum_volume_carrier_le`), with `lam ≤ Cd`; while at the top grid index
`|⋃ 𝕋_ρ|` is bounded below by the volume of one radius-`1` node tube.  The threshold therefore
demands `B ≲ Cd² δ^{-η} · |B_1| / (δ^η · c)`, i.e. `B ≲ δ^{-2η}` up to dimensional constants,
whereas `Kakeya.KatzTaoEstimate β` supplies `B = δ^{-ε} |𝕋|^β` with `|𝕋| ≥ δ^{-1}`
(`Kakeya.VeryNotSticky.tube_count`).  Since `η` is the *smallest* positive exponent of the
section and `ε`, `β` are fixed before it, `δ^{-ε}|𝕋|^β ≫ δ^{-2η}`.

**So the datum is not derivable from Katz–Tao at the configuration's own exponent**, and the two
directions of the re-encoding test come out asymmetric: the datum neither implies a usable
multiplicity estimate (it implies one only relative to `µ(𝕋_ρ)`, see
`Kakeya.VeryNotSticky.sum_le_of_coarseBallNonconcentration`) nor follows from one.  It is a
genuine, independent hypothesis about the configuration — which is the verdict the test is for,
and the opposite of the round-7 verdict on the sum form. -/
theorem coarseBallNonconcentration_of_katzTao_shape (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    (k : ℕ) (ρ : NNReal) {B : ENNReal} (hB0 : B ≠ 0) (hBtop : B ≠ ⊤)
    (hKT : ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).shade
      ≤ B * volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade))
    (hthr : B * ((cfg.δ : ENNReal) ^ cfg.η *
        ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          volume (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
      ≤ ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).shade) :
    CoarseBallNonconcentration cfg 𝒱 k ρ := by
  refine coarseBallNonconcentration_of_sum_le cfg 𝒱 k ρ ?_
  refine (ENNReal.mul_le_mul_iff_right hB0 hBtop).1 (le_trans hthr hKT)


/-- **The shortfall, made arithmetic: `δ^η` granted against `δ^{2η}` guaranteed.**

`Kakeya.VeryNotSticky.lam_ge` is a *lower* bound, `Cd δ^{2η} ≤ lam`; nothing in the structure
bounds `lam` above except `Kakeya.VeryNotSticky.lam_le_Cd`, and
`Kakeya.VeryNotSticky.rescaleDensity` shows only `Cd⁻¹ lam` is a quantity of the data.  So a
configuration sitting at that endpoint, `lam ≤ Cd δ^{2η}`, is admissible, and there the datum
demands

`Cd² · δ^{2η} · ∑_i |T_i| ≥ δ^η · γ · |⋃ 𝕋_ρ|`,   i.e.   `γ · |⋃ 𝕋_ρ| ≤ Cd² · δ^{η} · ∑_i |T_i|`.

The residue's ball conjunct grants `δ^η`; the shading budget the structure guarantees is
`δ^{2η}`.  **The datum is short by exactly one factor of `δ^η`** — the same `η`-accounting that
forced `Kakeya.VeryNotSticky.lam_ge` from `δ^η` to `δ^{2η}` in the first place.

This is the S9-66A test — does the inequality *buy* anything against the budget already granted
— and the datum fails it at an endpoint the structure itself permits. -/
theorem not_coarseBallNonconcentration_of_lam_endpoint (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} {ρ : NNReal} {x₀ : EuclideanSpace ℝ (Fin 3)}
    (hx₀ : x₀ ∈ ⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
    (hρ0 : 0 < (ρ : ℝ)) {γ : ENNReal}
    (hγ : γ * volume (ball x₀ (ρ : ℝ)) ≤
      volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x₀ (ρ : ℝ)))
    (hlam : cfg.lam ≤ cfg.Cd * cfg.δ ^ (2 * cfg.η))
    (hgap : (cfg.Cd : ENNReal) * ((cfg.Cd : ENNReal) *
        ((cfg.δ : ENNReal) ^ (2 * cfg.η) *
          ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).carrier))
      < (cfg.δ : ENNReal) ^ cfg.η * γ *
          volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)) :
    ¬ CoarseBallNonconcentration cfg 𝒱 k ρ := by
  refine not_coarseBallNonconcentration_of_budget_short cfg 𝒱 hx₀ hρ0 hγ
    (lt_of_le_of_lt ?_ hgap)
  have hlam' : (cfg.lam : ENNReal)
      ≤ (cfg.Cd : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) := by
    have h := ENNReal.coe_le_coe.2 hlam
    simpa [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne'] using h
  calc (cfg.Cd : ENNReal) *
        ((cfg.lam : ENNReal) * ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).carrier)
      ≤ (cfg.Cd : ENNReal) *
        (((cfg.Cd : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
          ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).carrier) := by gcongr
    _ = (cfg.Cd : ENNReal) * ((cfg.Cd : ENNReal) *
          ((cfg.δ : ENNReal) ^ (2 * cfg.η) *
            ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).carrier)) := by ring

end Kakeya.VeryNotSticky
