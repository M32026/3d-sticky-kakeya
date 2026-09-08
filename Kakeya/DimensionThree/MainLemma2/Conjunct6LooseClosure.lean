/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SplitInputsLoosePlug
public import Kakeya.DimensionThree.MainLemma2.Conjunct6OptionETripwire

/-!
# Conjunct 6 by the loose route (B): the compiled residue

 (round 2).  The existing conjunct 6 of
`Kakeya.VeryNotSticky.SideDataObligations` (`SetupSideData.lean:455–469`, body pin
`45e79ec355c42540474689e9ceb8e538`) asks, for **every** configuration, for a loose Def 2.2
bundle `𝒱 : LooseShadedUniformTubeSet cfg.s cfg.T N edCoverDilateConstant (edCoverConstant cfg.C₀)`
with the angular clause.  The existing `eventually_conjunct6_of_looseDatum` reduces the clause to
the bundle; so the whole conjunct is the single obligation

* `LooseDatumObligation` — the bundle on `cfg.s` itself, for every `cfg`,

and `conjunct6_of_loose_route` closes the conjunct, byte for byte, from it.  What the banked
producers give is the bundle on a **subfamily** (`exists_looseShaded_subfamily_of_config`,
`LooseUniformAnchorNet.lean:1500`; J1's `exists_joint_refinement`, both exact and loose data on
one subfamily), never on `cfg.s`.  That gap is not a proof gap: `not_looseShaded_of_bigAngularFibre`
shows that on a configuration with a `> C⁵` angular fibre at some `(x, v)` and one member whose
direction is `ρ_k/2`-isolated from all others, **no** loose bundle at constant `C` exists — the
existing PC theorem `angularCone_card_le_of_loose` applied to that member's class (a singleton, by
`LooseGridCoverSystem.dir_close_tube_assign`) bounds the fibre by `C⁵`.  The twisted bush of
`Conjunct6Refutation.lean` supplies the fibre.  So the loose obligation, like the exact Option E of
`Conjunct6OptionETripwire.lean`, is unsatisfiable as a `∀ cfg` statement; only a config
*producer* can carry the datum, and that producer's own residue is the local-mass clause, which the bush does not touch.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody Filter Topology
open scoped NNReal ENNReal

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The obligation, and conjunct 6 from it -/

/-- **The loose-datum obligation**: for every configuration with the parameters, a loose Def 2.2
bundle on `cfg.s` itself at the conjunct's constants. -/
def LooseDatumObligation (exscal ϱ η : ℝ) (C₀bd : NNReal) : Prop :=
  ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
    cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ → bd.C₀ = C₀bd →
    Nonempty (LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ)
      edCoverDilateConstant (edCoverConstant cfg.C₀))

/-- **Conjunct 6 (existing text, `SetupSideData.lean:455–469`) from the loose-datum obligation.**
The conclusion is the conjunct's text verbatim. -/
theorem conjunct6_of_loose_route {exscal ϱ η : ℝ} (hη : 0 < η) (C₀bd : NNReal)
    (hobl : LooseDatumObligation.{u} exscal ϱ η C₀bd) :
  (∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ → bd.C₀ = C₀bd →
      ∃ 𝒱 : LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ)
          edCoverDilateConstant (edCoverConstant cfg.C₀),
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
                    (fun i ↦ (cfg.T i).toShadedBody)) := by
  filter_upwards [eventually_conjunct6_of_looseDatum.{u} (exscal := exscal) (ϱ := ϱ) hη C₀bd,
    hobl] with δ h1 h2
  intro cfg bd hδ hη' hex hϱ hb hC₀
  exact h1 cfg bd hδ hη' hex hϱ hb hC₀ (h2 cfg bd hδ hη' hex hϱ hb hC₀)

/-! ## The obligation against the twisted bush -/

open scoped Classical in
/-- **A direction-isolated member has a singleton class in every loose hierarchy.**  Members of
one class have directions within `ρ_k/4` of the node's, up to sign
(`LooseGridCoverSystem.dir_close_tube_assign`), hence within `ρ_k/2` of each other up to sign.
(Position isolation is useless in the loose model: `Kakeya.Tube.dilate` at factor `K` is a
thickened segment of length `K`.) -/
theorem looseCoverClass_eq_singleton_of_dir_isolated (cfg : VeryNotSticky.{u}) {N : ℕ} {K : ℝ}
    {C : NNReal} (𝒰 : LooseUniform.LooseUniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N K C)
    {k : ℕ} (hk : k ≤ N) {i₀ : cfg.ι} (hi₀ : i₀ ∈ cfg.s)
    (hiso : ∀ i ∈ cfg.s, i ≠ i₀ → ∀ σ : ℝ, |σ| = 1 →
      ((Tube.gridScale cfg.δ N k : NNReal) : ℝ) / 2 <
        ‖(cfg.T i).direction - σ • (cfg.T i₀).direction‖) :
    Tube.coverClass cfg.s (𝒰.cover.assign k) (𝒰.cover.assign k i₀) = {i₀} := by
  ext i
  simp only [Tube.coverClass, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hi, hassign⟩
    by_contra hne
    obtain ⟨σ₁, hσ₁, h₁⟩ := 𝒰.cover.dir_close_tube_assign k hk i hi
    obtain ⟨σ₂, hσ₂, h₂⟩ := 𝒰.cover.dir_close_tube_assign k hk i₀ hi₀
    rw [hassign] at h₁
    set dj := (𝒰.cover.tube k (𝒰.cover.assign k i₀)).direction with hdj
    have hσ₂sq : σ₂ * σ₂ = 1 := by
      have := sq_abs σ₂; rw [hσ₂] at this; nlinarith [this]
    -- `‖σ₁ • dj - (σ₁ * σ₂) • dir i₀‖ = ‖dir i₀ - σ₂ • dj‖`
    have hmid : ‖σ₁ • dj - (σ₁ * σ₂) • (cfg.T i₀).direction‖ =
        ‖(cfg.T i₀).direction - σ₂ • dj‖ := by
      have : σ₁ • dj - (σ₁ * σ₂) • (cfg.T i₀).direction =
          -((σ₁ * σ₂) • ((cfg.T i₀).direction - σ₂ • dj)) := by
        rw [smul_sub (σ₁ * σ₂) (cfg.T i₀).direction (σ₂ • dj), smul_smul, mul_assoc, hσ₂sq,
          mul_one, neg_sub]
      rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_mul, hσ₁, hσ₂, one_mul, one_mul]
    have hσ : |σ₁ * σ₂| = 1 := by rw [abs_mul, hσ₁, hσ₂, one_mul]
    have h := hiso i hi hne (σ₁ * σ₂) hσ
    have htri := norm_sub_le_norm_sub_add_norm_sub (cfg.T i).direction (σ₁ • dj)
      ((σ₁ * σ₂) • (cfg.T i₀).direction)
    rw [hmid] at htri
    linarith
  · rintro rfl
    exact ⟨hi₀, rfl⟩

/-- **No loose bundle at constant `C` on a configuration with a `> C⁵` angular fibre and a
direction-isolated member.**  The existing PC theorem `angularCone_card_le_of_loose`, read at the
isolated member's (singleton) class. -/
theorem not_looseShaded_of_bigAngularFibre (cfg : VeryNotSticky.{u}) {N : ℕ} {K : ℝ}
    {C : NNReal} (𝒱 : LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T N K C) (hK : 0 < K)
    (hC : 1 ≤ C) {k : ℕ} (hk : k ≤ N)
    (hδρ : 4 * (cfg.δ : ℝ) ≤ (Tube.gridScale cfg.δ N k : ℝ))
    {ρ : ℝ} (hρk : ρ ≤ (Tube.gridScale cfg.δ N k : ℝ)) (x v : E3)
    (hbig : (C : ENNReal) ^ 5 < ((cfg.angularFibre x v ρ).card : ENNReal))
    {i₀ : cfg.ι} (hi₀ : i₀ ∈ cfg.s)
    (hiso : ∀ i ∈ cfg.s, i ≠ i₀ → ∀ σ : ℝ, |σ| = 1 →
      ((Tube.gridScale cfg.δ N k : NNReal) : ℝ) / 2 <
        ‖(cfg.T i).direction - σ • (cfg.T i₀).direction‖) : False := by
  classical
  have hfib := looseCoverClass_eq_singleton_of_dir_isolated cfg 𝒱.tubeUniform hk hi₀ hiso
  have hne : (Tube.coverClass cfg.s (𝒱.tubeUniform.cover.assign k)
      (𝒱.tubeUniform.cover.assign k i₀)).Nonempty := by
    rw [hfib]; exact Finset.singleton_nonempty _
  have h := LooseUniform.angularCone_card_le_of_loose 𝒱 hK hC hk hδρ hρk
    (fun i hi ↦ volume_shade_ne_zero cfg hi) hne x v
  rw [hfib, multiplicity_singleton' i₀ _ (volume_shade_ne_zero cfg hi₀), mul_one] at h
  have h' : ((cfg.angularFibre x v ρ).card : ENNReal) ≤ (C : ENNReal) ^ 5 := h
  exact absurd (lt_of_lt_of_le hbig h') (lt_irrefl _)

/-- **The obligation's instance at such a configuration is false**, at the conjunct's own
constants: `Nonempty (LooseShadedUniformTubeSet cfg.s cfg.T N edCoverDilateConstant
(edCoverConstant cfg.C₀))` fails once the angular fibre exceeds `(edCoverConstant cfg.C₀)⁵` at a
window level.  Cardinality of the fibre is measured at `ρ₂*`, the conjunct's own radius. -/
theorem not_looseDatum_of_bigAngularFibre (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
    (hδρ : 4 * (cfg.δ : ℝ) ≤ (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ))
    (x v : E3)
    (hbig : ((edCoverConstant cfg.C₀ : NNReal) : ENNReal) ^ 5 <
      ((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ENNReal))
    {i₀ : cfg.ι} (hi₀ : i₀ ∈ cfg.s)
    (hiso : ∀ i ∈ cfg.s, i ≠ i₀ → ∀ σ : ℝ, |σ| = 1 →
      ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ℝ) / 2 <
        ‖(cfg.T i).direction - σ • (cfg.T i₀).direction‖) :
    ¬ Nonempty (LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ)
      edCoverDilateConstant (edCoverConstant cfg.C₀)) := by
  rintro ⟨𝒱⟩
  exact not_looseShaded_of_bigAngularFibre cfg 𝒱 edCoverDilateConstant_pos
    (one_le_edCoverConstant cfg.hC₀) hk hδρ (by exact_mod_cast hge) x v hbig hi₀ hiso

end Kakeya.VeryNotSticky
