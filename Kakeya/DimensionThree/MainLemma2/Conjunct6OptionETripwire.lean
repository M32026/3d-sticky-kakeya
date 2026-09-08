/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SplitInputsLoosePlug

/-!
# Conjunct 6 in its after-text (Option E): a compiled tripwire

 licenses conjunct 6 of `Kakeya.VeryNotSticky.SideDataObligations`
in the shape `∀ᶠ δ, ∀ cfg bd, params → ∃ (C : NNReal) (𝒱 : ShadedUniformTubeSet cfg.s cfg.T N C),
1 ≤ C ∧ C ≤ δ^{-η} ∧ (the angular clause on 𝒱.tubeUniform.toPartitionBrackets)`, reading the
`∃` as "the obligation is to *produce* the line-ED hierarchy".  This leaf records, as a theorem,
that the `∃` cannot do that job by itself: the hierarchy ranges over `cfg.s` with `cfg.T` —
it cannot change the tubes — and for a configuration containing

* a **large angular fibre** at some `(x, v)` — more than `δ^{-η}` members shading `x` with
  direction within `ρ₂*` of `v` (the *twisted bush* of `Conjunct6Refutation.lean`, compiled
  there at `n ≈ ρ₂*/(16δ)` and shown compatible with `maxDensity_le` ), and
* one **isolated** member `i₀` — its midpoint farther than `1 + 2ρ_k` from every other member's —

the clause fails for **every** `𝒱`: `i₀`'s class is a singleton in any exact hierarchy (two
members of one class lie inside one unit `ρ_k`-node, so their midpoints are within `1 + 2ρ_k`),
the multiplicity of a one-tube shaded family is `1`, and the clause at that node says
`#angularFibre ≤ Cang ≤ δ^{-η}`.

The content is `Kakeya.VeryNotSticky.not_conjunct6OptionEClause`.  What is *not* compiled here is
a full `VeryNotSticky` record carrying both features; that existence has the same status as the
twisted bush of  .
No field of `VeryNotSticky` is axial (`VeryNotSticky.lean:393–880`).

The pin `conjunct6OptionEClause_pin` checks by `Iff.rfl` that `conjunct6OptionEClause` is the
licensed block's inner text verbatim (from `∃ (C : NNReal)` on).
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody Filter Topology
open scoped NNReal ENNReal

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open scoped Classical in
/-- The inner clause of conjunct 6 in the after-text (Option E), verbatim from
`∃ (C : NNReal)` on; pinned by `conjunct6OptionEClause_pin`. -/
def conjunct6OptionEClause (cfg : VeryNotSticky.{u}) (bd : BallData cfg) : Prop :=
  ∃ (C : NNReal) (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) C),
  1 ≤ C ∧ (C : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
  ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
    cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
    Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
    ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
      ∀ j ∈ cfg.pbActiveTubeNodes 𝒱.tubeUniform.toPartitionBrackets k,
        ∀ x v : E3,
          (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
            (Cang : ENNReal) *
              ShadedBody.multiplicity
                (cfg.pbTubeFibre 𝒱.tubeUniform.toPartitionBrackets k j)
                (fun i ↦ (cfg.T i).toShadedBody)

open scoped Classical in
/-- **Pin.** The licensed block of  (its text from the `∀ᶠ` to the end, with
the parameter implications) is, definitionally, `∀ᶠ δ, ∀ cfg bd, params → conjunct6OptionEClause`.
If the after-text or this definition moves, this stops typechecking. -/
theorem conjunct6OptionEClause_pin {exscal ϱ η : ℝ} {C₀bd : NNReal} :
    (∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ → bd.C₀ = C₀bd →
      ∃ (C : NNReal) (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) C),
      1 ≤ C ∧ (C : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
          ∀ j ∈ cfg.pbActiveTubeNodes 𝒱.tubeUniform.toPartitionBrackets k,
            ∀ x v : E3,
              (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
                (Cang : ENNReal) *
                  ShadedBody.multiplicity
                    (cfg.pbTubeFibre 𝒱.tubeUniform.toPartitionBrackets k j)
                    (fun i ↦ (cfg.T i).toShadedBody)) ↔
    (∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ → bd.C₀ = C₀bd →
      conjunct6OptionEClause cfg bd) :=
  Iff.rfl

/-! ## The two ingredients -/

/-- **The multiplicity of a one-member shaded family is `1`** (the tree's
`multiplicity_singleton` of `MainLemma1/Factoring.lean`, restated locally to avoid the import). -/
theorem multiplicity_singleton' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ι : Type*} (i₀ : ι)
    (V : ι → ShadedBody E) (h : volume (V i₀).shade ≠ 0) :
    ShadedBody.multiplicity ({i₀} : Finset ι) V = 1 := by
  rw [ShadedBody.multiplicity_eq_div, Finset.sum_singleton, Finset.set_biUnion_singleton]
  exact ENNReal.div_self h
    (ne_top_of_le_ne_top (V i₀).isCompact.measure_ne_top (measure_mono (V i₀).shade_subset))

open scoped Classical in
/-- **An isolated member has a singleton class in every exact hierarchy.**  Two members of one
class lie inside the class's unit `ρ_k`-node, whose carrier is within `1/2 + ρ_k` of its
midpoint; so their midpoints are within `1 + 2ρ_k` of each other. -/
theorem pbTubeFibre_eq_singleton_of_isolated (cfg : VeryNotSticky.{u}) {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C) {k : ℕ} (hk : k ≤ N)
    {i₀ : cfg.ι} (hi₀ : i₀ ∈ cfg.s)
    (hiso : ∀ i ∈ cfg.s, i ≠ i₀ →
      1 + 2 * ((Tube.gridScale cfg.δ N k : NNReal) : ℝ) <
        dist (cfg.T i).midpoint (cfg.T i₀).midpoint) :
    cfg.pbTubeFibre 𝒰.toPartitionBrackets k (𝒰.cover.assign k i₀) = {i₀} := by
  ext i
  simp only [pbTubeFibre, Tube.UniformTubeSet.toPartitionBrackets_assign, Tube.coverClass,
    Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hi, hassign⟩
    by_contra hne
    set W := 𝒰.cover.tube k (𝒰.cover.assign k i₀) with hW
    have hi₀W := 𝒰.cover.le_tube_assign k hk i₀ hi₀
    have hiW := 𝒰.cover.le_tube_assign k hk i hi
    rw [hassign] at hiW
    have hm₀ : (cfg.T i₀).midpoint ∈ W.carrier :=
      hi₀W (Tube.midpoint_mem_carrier cfg.hδ (cfg.T i₀).toTube)
    have hm : (cfg.T i).midpoint ∈ W.carrier :=
      hiW (Tube.midpoint_mem_carrier cfg.hδ (cfg.T i).toTube)
    have hb₀ := Tube.carrier_subset_closedBall_midpoint _ W hm₀
    have hb := Tube.carrier_subset_closedBall_midpoint _ W hm
    rw [Metric.mem_closedBall] at hb₀ hb
    have htri := dist_triangle_right (cfg.T i).midpoint (cfg.T i₀).midpoint (midpoint ℝ W.x W.y)
    have := hiso i hi hne
    linarith
  · rintro rfl
    exact ⟨hi₀, rfl⟩

open scoped Classical in
/-- The node of a member is an active node. -/
theorem assign_mem_pbActiveTubeNodes (cfg : VeryNotSticky.{u}) {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C) {k : ℕ} (hk : k ≤ N)
    {i₀ : cfg.ι} (hi₀ : i₀ ∈ cfg.s) :
    𝒰.cover.assign k i₀ ∈ cfg.pbActiveTubeNodes 𝒰.toPartitionBrackets k := by
  unfold pbActiveTubeNodes
  refine Finset.mem_filter.mpr ⟨𝒰.toPartitionBrackets.assign_mem k hk i₀ hi₀, i₀, ?_⟩
  simp only [pbTubeFibre, Tube.UniformTubeSet.toPartitionBrackets_assign, Tube.coverClass,
    Finset.mem_filter]
  exact ⟨hi₀, trivial⟩

/-! ## The tripwire -/

/-- **Option E's clause fails, for every hierarchy, on a configuration with a large angular fibre
and an isolated member.**  At the level `k` of the window, the clause at the isolated member's
node reads `#angularFibre x v ρ₂* ≤ Cang · 1 ≤ δ^{-η}`, against `#angularFibre > δ^{-η}`.

**What this record shows after  (§13 R1):** read together with
`Kakeya.VeryNotSticky.eventually_conjunct6OptionEClause_of_centred` (`Conjunct6LineED.lean`), which proves the same clause
for every *centred* configuration at small `δ`, this refutation shows that D1's centredness binder
`∀ i ∈ s, (T i).toTube.IsCentred` is **load-bearing**: without it the clause — and with it the line-ED datum the split inputs
need — has no producer. Conjunct 6 itself was deleted from `SideDataObligations` (R1); this theorem is kept as the record. -/
theorem not_conjunct6OptionEClause (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
    (hle : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀)
    (x v : E3)
    (hbig : (cfg.δ : ENNReal) ^ (-cfg.η) <
      ((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ENNReal))
    {i₀ : cfg.ι} (hi₀ : i₀ ∈ cfg.s)
    (hiso : ∀ i ∈ cfg.s, i ≠ i₀ →
      1 + 2 * ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ℝ) <
        dist (cfg.T i).midpoint (cfg.T i₀).midpoint) :
    ¬ conjunct6OptionEClause cfg bd := by
  rintro ⟨C, 𝒱, -, -, hclause⟩
  obtain ⟨Cang, hCang, hang⟩ := hclause k hk hge hle
  have hfib := pbTubeFibre_eq_singleton_of_isolated cfg 𝒱.tubeUniform hk hi₀ hiso
  have hact := assign_mem_pbActiveTubeNodes cfg 𝒱.tubeUniform hk hi₀
  have h := hang _ hact x v
  rw [hfib, multiplicity_singleton' i₀ _ (volume_shade_ne_zero cfg hi₀), mul_one] at h
  exact absurd (lt_of_lt_of_le hbig (h.trans hCang)) (lt_irrefl _)

end Kakeya.VeryNotSticky
