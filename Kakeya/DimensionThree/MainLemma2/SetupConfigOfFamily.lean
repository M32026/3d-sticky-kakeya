/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupIslandCut

/-!
# The configuration of a refined family, named

`Kakeya.VeryNotSticky.exists_veryNotSticky_of_rhoCount` (SetupAssembly) builds Configuration
`hyp:ml2setup` from a refined family `(s', T')` and its data, but returns it existentially. The
side-data construction (`Kakeya.VeryNotSticky.SideDataResidue`) has to build `BallData` and
`CaseSideData` *on* that configuration, so it needs the configuration as a **term** whose fields
reduce: this file factors the record body of that proof out as a `noncomputable def`,
`Kakeya.VeryNotSticky.ofFamily`, with `rfl` lemmas for the data fields, and proves the comparison
clause `Kakeya.VeryNotSticky.ofFamily_isCRefinement` in the form the original theorem produces it.

The second half packages the configuration of the **island-cut family**: from the slack clauses of
residue 1 (`Kakeya.VeryNotSticky.BandUniformRefinementLocalMassSlack`, SetupLocalMassFinal) for a
refinement `(s', T')` and the floor/mass/local-mass conclusions of the island cut
(`Kakeya.VeryNotSticky.eventually_exists_lightPieceCut`, SetupIslandCut) for the cut family
`fun i ↦ Kakeya.VeryNotSticky.deleteShadeTube (T' i) Light hL`,
`Kakeya.VeryNotSticky.eventually_exists_config_of_slackCut` produces, for all small `δ`, a
configuration with the prescribed parameters comparing to the input family at
`c' = 2⁻¹ δ^{η/2} ≥ δ^η`, whose index set is `s'`, whose shades are the cut shades, and whose
working dimensions are `a = b = δ` (the degenerate regime of the side-data plan). The thresholds are
discharged exactly as in `Kakeya.VeryNotSticky.eventually_exists_veryNotSticky_of_localMass`:

* the uniformity constant is enlarged to `C₁ = max C₀ (Tube.coverCountLoss 3)`, still below the
  cap `δ^{-η'}` for small `δ`, and the uniform hierarchy of `(s', T')` is transported to the cut
  family by `Kakeya.VeryNotSticky.shadedUniform_deleteShadeTube` (a common cut is invisible to
  every shade class at a surviving point);
* the `ρ`-count field is `Kakeya.VeryNotSticky.rhoParentData_of_binders`;
* the per-tube floor `δ^{2η}|T| ≤ |Y'(i) \ Light|` is the island cut's clause (ii), the local-mass
  clause at exponent `η` its clause (iv), and the retention `2⁻¹ δ^{η/2}` chains the slack's
  `δ^{η/2}` with the cut's `1/2` (clause (iii)); `δ^η ≤ 2⁻¹ δ^{η/2}` once `2 δ^{η/2} ≤ 1`.

Nothing in the tree is edited: `exists_veryNotSticky_of_rhoCount` keeps its statement and its
proof (it sits upstream of this leaf), and the `example` after `ofFamily_isCRefinement` pins that
`ofFamily` re-derives its conclusion.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody
open scoped NNReal ENNReal
open Produce

universe u

/-! ### The configuration of a refined family, as a term -/

section OfFamily

variable {β ζ exscal ϱ η : ℝ} {δ : NNReal}
  (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
  (hδ : 0 < δ) (hδ1 : δ ≤ 1)
  (hKT : KatzTaoEstimate.{u} E3 β) (hF : FrostmanEstimate.{u} E3 β)
  (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal)
  (hwδ : 6 * δ ^ (exscal - η) ≤ w.wρ)
  {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
  (hgrid : 1 ≤ η * (Tube.ssfGridLen δ : ℝ))
  (habs : (aScaleDataConstant C₀ 1 : ENNReal) ^ 2 ≤ (δ : ENNReal) ^ (-η))
  {ι : Type u} {s : Finset ι} {T : ι → ShadedTube δ E3}
  (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
  (hmax : maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η))
  {s' : Finset ι} (hs' : s' ⊆ s) {T' : ι → ShadedTube δ E3}
  (htube : ∀ i, (T' i).toTube = (T i).toTube)
  (hrho : RhoParentData δ ζ exscal η s' T')
  (huni : Nonempty (ShadedTube.ShadedUniformTubeSet s' T' (Tube.ssfGridLen δ) C₀))
  (hpt : ∀ i ∈ s', (δ : ENNReal) ^ (2 * η) * volume (T' i).toShadedBody.carrier
    ≤ volume (T' i).toShadedBody.shade)
  (htc : (1 : ENNReal) ≤ (δ : ENNReal) * (s'.card : ENNReal))
  (hloss : ((_root_.ShadedBody.rhoTubesSection9Loss 3 s'.card δ : NNReal) : ENNReal)
    ≤ (δ : ENNReal) ^ (-η))
  (hindloss : ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal)
    ≤ (δ : ENNReal) ^ (-η))
  (hclm : LocalMassAt δ η s' T')
  {a b : NNReal}
  (hdims : δ ≤ a ∧ a ≤ b ∧ b ≤ δ ^ exscal)

/-- **Configuration `hyp:ml2setup` of a refined family, as a term.** The record body of
`Kakeya.VeryNotSticky.exists_veryNotSticky_of_rhoCount` with `ι := ι`, `s := s'`, `T := T'`, and the
same binders (the two binders that theorem spends only on the comparison clause, `hsh` and `hmass`,
are not needed for the record and are taken by `Kakeya.VeryNotSticky.ofFamily_isCRefinement`).

The density band `lam`, `Cd` is `Kakeya.VeryNotSticky.exists_band_of_pointwise_two_eta` at the
per-tube floor `hpt`, chosen with `Exists.choose`; the fullness field is the aggregate of the same
floor (`Kakeya.VeryNotSticky.le_fullness_of_pointwise`); `D₀ = 1`; the coarse K_KT datum is the
window at the radius clause `hwδ`. Every data field other than `lam` and `Cd` is read off by a `rfl`
lemma below. -/
noncomputable def ofFamily : VeryNotSticky.{u} :=
  have hbody : ∀ i, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody :=
    fun i => congrArg Tube.toConvexSpaceBody (htube i)
  have hcarset : ∀ i, (T' i).carrier = (T i).carrier :=
    fun i => congrArg ConvexSpaceBody.carrier (hbody i)
  have hball' : ∀ i ∈ s, (T' i).carrier ⊆ Metric.closedBall 0 1 :=
    fun i hi => (hcarset i).symm ▸ hball i hi
  have hmax' : maxDensity s (fun i ↦ (T' i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) :=
    (maxDensity_congr (fun i _ => hbody i)).symm ▸ hmax
  have hmaxs' : maxDensity s' (fun i ↦ (T' i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) :=
    le_trans (maxDensity_mono _ hs') hmax'
  have hband := exists_band_of_pointwise_two_eta hδ hδ1 hη T' hpt
  have hfull : (δ ^ (2 * η) : NNReal) ≤ ShadedBody.fullness s' (fun i ↦ (T' i).toShadedBody) := by
    have hs'ne : s'.Nonempty := by
      rcases Finset.eq_empty_or_nonempty s' with h | h
      · rw [h] at htc; simp at htc
      · exact h
    obtain ⟨i₀, hi₀⟩ := hs'ne
    have hvpos : 0 < volume (T' i₀).carrier := by
      refine lt_of_lt_of_le ?_ (Tube.le_volume (T' i₀).toTube)
      have hc : ((Tube.le_volume.c (Module.finrank ℝ E3) : NNReal) : ENNReal) ≠ 0 := by
        simpa using (Tube.le_volume.c_pos (Module.finrank ℝ E3)).ne'
      have hd : ((δ : ENNReal) ^ (Module.finrank ℝ E3 - 1)) ≠ 0 :=
        pow_ne_zero _ (by simpa using hδ.ne')
      exact pos_iff_ne_zero.mpr (mul_ne_zero hc hd)
    have hsumne : ∑ i ∈ s', volume (T' i).toShadedBody.carrier ≠ 0 := by
      refine ne_of_gt (lt_of_lt_of_le hvpos ?_)
      exact Finset.single_le_sum (f := fun i => volume (T' i).toShadedBody.carrier)
        (fun i _ => bot_le) hi₀
    refine le_fullness_of_pointwise hsumne (fun i hi => ?_)
    rw [ENNReal.coe_rpow_of_ne_zero hδ.ne']
    exact hpt i hi
  { β := β, hβ := hβ, hβ1 := hβ1, ζ := ζ, hζ := hζ, δ := δ, hδ := hδ, hδ1 := hδ1,
    exscalb := exscal, hexscalb := hexscal, exscal := exscal, hexscal := hexscal,
    hscale := rfl, η := η, hη := hη, ι := ι, decidableEq := Classical.decEq ι,
    s := s', T := T',
    contained := fun i hi => hball' i (hs' hi),
    C₀ := C₀,
    hC₀ := hC₀,
    D₀ := 1, hD₀ := le_rfl, ckt := w.toData hwδ,
    uniform := huni,
    maxDensity_le := hmaxs',
    fullness_ge := hfull,
    lam := hband.choose, Cd := hband.choose_spec.choose,
    hCd := hband.choose_spec.choose_spec.1,
    lam_ge := hband.choose_spec.choose_spec.2.1,
    shading_lb := hband.choose_spec.choose_spec.2.2.1,
    shading_ub := hband.choose_spec.choose_spec.2.2.2,
    rho_count := hrho,
    ktEstimate := hKT, fEstimate := hF,
    ϱ := ϱ, hϱ := hϱ, a := a, b := b, hdims := hdims,
    tube_count := htc,
    aScaleData_absorb := habs,
    coarseLoss_absorb := hloss,
    inducedFullnessLoss_absorb := hindloss,
    coarseLocalMass := hclm,
    gridFine := hgrid }

@[simp] theorem ofFamily_ι :
    (ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
      hrho huni hpt htc hloss hindloss hclm hdims).ι = ι := rfl

@[simp] theorem ofFamily_s :
    (ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
      hrho huni hpt htc hloss hindloss hclm hdims).s = s' := rfl

@[simp] theorem ofFamily_T :
    (ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
      hrho huni hpt htc hloss hindloss hclm hdims).T = T' := rfl

@[simp] theorem ofFamily_δ :
    (ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
      hrho huni hpt htc hloss hindloss hclm hdims).δ = δ := rfl

@[simp] theorem ofFamily_β :
    (ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
      hrho huni hpt htc hloss hindloss hclm hdims).β = β := rfl

@[simp] theorem ofFamily_ζ :
    (ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
      hrho huni hpt htc hloss hindloss hclm hdims).ζ = ζ := rfl

@[simp] theorem ofFamily_exscal :
    (ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
      hrho huni hpt htc hloss hindloss hclm hdims).exscal = exscal := rfl

@[simp] theorem ofFamily_exscalb :
    (ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
      hrho huni hpt htc hloss hindloss hclm hdims).exscalb = exscal := rfl

@[simp] theorem ofFamily_ϱ :
    (ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
      hrho huni hpt htc hloss hindloss hclm hdims).ϱ = ϱ := rfl

@[simp] theorem ofFamily_η :
    (ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
      hrho huni hpt htc hloss hindloss hclm hdims).η = η := rfl

@[simp] theorem ofFamily_C₀ :
    (ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
      hrho huni hpt htc hloss hindloss hclm hdims).C₀ = C₀ := rfl

@[simp] theorem ofFamily_D₀ :
    (ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
      hrho huni hpt htc hloss hindloss hclm hdims).D₀ = 1 := rfl

@[simp] theorem ofFamily_a :
    (ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
      hrho huni hpt htc hloss hindloss hclm hdims).a = a := rfl

@[simp] theorem ofFamily_b :
    (ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
      hrho huni hpt htc hloss hindloss hclm hdims).b = b := rfl

@[simp] theorem ofFamily_ckt :
    (ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
      hrho huni hpt htc hloss hindloss hclm hdims).ckt = w.toData hwδ := rfl

/-- **The comparison clause of `Kakeya.VeryNotSticky.ofFamily`**, in the form
`Kakeya.VeryNotSticky.exists_veryNotSticky_of_rhoCount` produces it (index equivalence
`Equiv.refl ι`): the configuration is a `c`-refinement of the input family `(s, T)` as soon as the
shades are cut (`hsh`) and the mass retention holds at `c` (`hmass`). -/
theorem ofFamily_isCRefinement (hsh : ∀ i, (T' i).shade ⊆ (T i).shade) {c : NNReal}
    (hmass : (c : ENNReal) * ∑ i ∈ s, volume (T i).shade
      ≤ ∑ i ∈ s', volume (T' i).shade) :
    ShadedBody.IsCRefinement
      ((ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
        hrho huni hpt htc hloss hindloss hclm hdims).s.map (Equiv.refl ι).toEmbedding)
      (fun i ↦ ((ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax
        hs' htube hrho huni hpt htc hloss hindloss hclm hdims).T
          ((Equiv.refl ι).symm i)).toShadedBody)
      s (fun i ↦ (T i).toShadedBody) c := by
  have hbody : ∀ i, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody :=
    fun i => congrArg Tube.toConvexSpaceBody (htube i)
  simp only [Equiv.refl_toEmbedding, Finset.map_refl, Equiv.refl_symm, Equiv.refl_apply,
    ofFamily_s, ofFamily_T]
  exact ⟨⟨hs', fun i _ => ⟨hbody i, hsh i⟩⟩, hmass⟩

/-- **Tripwire**: `ofFamily` with `ofFamily_isCRefinement` re-derives the conclusion of
`Kakeya.VeryNotSticky.exists_veryNotSticky_of_rhoCount` from its binders — the factoring is
faithful to the record body. If either statement moves, this stops typechecking. -/
example (hsh : ∀ i, (T' i).shade ⊆ (T i).shade) {c : NNReal}
    (hmass : (c : ENNReal) * ∑ i ∈ s, volume (T i).shade
      ≤ ∑ i ∈ s', volume (T' i).shade) :
    ∃ (cfg : VeryNotSticky.{u}) (e : cfg.ι ≃ ι),
      (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧ cfg.η = η) ∧
      ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
        (fun i ↦ (cfg.T (e.symm i)).toShadedBody) s (fun i ↦ (T i).toShadedBody) c :=
  ⟨ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax hs' htube
      hrho huni hpt htc hloss hindloss hclm hdims,
    Equiv.refl ι, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ofFamily_isCRefinement hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid habs hball hmax
      hs' htube hrho huni hpt htc hloss hindloss hclm hdims hsh hmass⟩

end OfFamily

/-! ### The configuration of the island-cut family -/

/-- **Configuration `hyp:ml2setup` of the island-cut family, for all small `δ`.**

Inputs, at a scale `δ` below the thresholds: the target's binders on `(s, T)` (carriers in the
unit ball, `maxDensity ≤ δ^{-η}`, the repaired `ρ`-count clause); a refinement `(s', T')` with the
clauses of `Kakeya.VeryNotSticky.BandUniformRefinementLocalMassSlack` that the construction reads —
index subset, tubes unchanged, shades cut, Definition 2.2 at `1 ≤ C₀ ≤ δ^{-η'}`, tube count
`1 ≤ δ|s'|`, mass retention `δ^{η/2}` (the doubled floor and the local-mass clause at `η/2` are
spent by the island cut, not here); and a measurable set `Light` with the island cut's
conclusions (ii)–(iv) of `Kakeya.VeryNotSticky.eventually_exists_lightPieceCut` for the cut family
`fun i ↦ Kakeya.VeryNotSticky.deleteShadeTube (T' i) Light hL`: the per-tube floor
`δ^{2η}|T| ≤ |Y'(i) \ Light|`, the retention `1/2`, and GWZ (87) at exponent `η`.

Output: a configuration `cfg'` (namely `Kakeya.VeryNotSticky.ofFamily` of the cut family at the
uniformity constant `max C₀ (Tube.coverCountLoss 3)`) with the prescribed parameters, comparing to
`(s, T)` at `c' = 2⁻¹ δ^{η/2} ≥ δ^η`, whose index set is `s'`, whose shades are the cut shades
`Y'(i) \ Light`, and whose working dimensions are `a = b = δ`. The last three clauses are what
the side-data
construction (`Kakeya.VeryNotSticky.SideDataResidue`) needs in order to build `BallData cfg'` from
the island cut's cover and to place itself in the degenerate regime. -/
theorem eventually_exists_config_of_slackCut {β ζ exscal ϱ η η' τ τ' : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (hη' : 0 < η') (h8 : 8 * η' < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    (hKT : KatzTaoEstimate.{u} E3 β) (hF : FrostmanEstimate.{u} E3 β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∀ i ∈ s, (T i).toTube.IsCentred) →
        (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        ∀ (s' : Finset ι) (T' : ι → ShadedTube δ E3) (Light : Set E3)
          (hL : MeasurableSet Light),
          -- the slack clauses read here: (a) index subset, tubes, shades; (c) Def 2.2;
          -- (e) tube count; (f) retention `δ^{η/2}`
          s' ⊆ s →
          (∀ i, (T' i).toTube = (T i).toTube) →
          (∀ i, (T' i).shade ⊆ (T i).shade) →
          (∃ C₀ : NNReal, 1 ≤ C₀ ∧ (C₀ : ENNReal) ≤ (δ : ENNReal) ^ (-η') ∧
            Nonempty (ShadedTube.ShadedUniformTubeSet s' T' (Tube.ssfGridLen δ) C₀)) →
          (1 : ENNReal) ≤ (δ : ENNReal) * (s'.card : ENNReal) →
          (δ : ENNReal) ^ (η / 2) * ∑ i ∈ s, volume (T i).shade ≤
            ∑ i ∈ s', volume (T' i).shade →
          -- the island cut's (ii) floor, (iii) retention `1/2`, (iv) GWZ (87) at `η`
          (∀ i ∈ s', (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier ≤
              volume ((T' i).shade \ Light)) →
          (2 : ENNReal)⁻¹ * ∑ i ∈ s', volume (T' i).shade ≤
              ∑ i ∈ s', volume ((T' i).shade \ Light) →
          LocalMassAt δ η s' (fun i ↦ deleteShadeTube (T' i) Light hL) →
          ∃ (cfg' : VeryNotSticky.{u}) (e' : cfg'.ι ≃ ι) (c' : NNReal),
            (cfg'.β = β ∧ cfg'.ζ = ζ ∧ cfg'.δ = δ ∧ cfg'.exscal = exscal ∧ cfg'.ϱ = ϱ ∧
                cfg'.η = η) ∧
            ShadedBody.IsCRefinement (cfg'.s.map e'.toEmbedding)
              (fun i ↦ (cfg'.T (e'.symm i)).toShadedBody) s (fun i ↦ (T i).toShadedBody) c' ∧
            (δ : ENNReal) ^ η ≤ (c' : ENNReal) ∧
            cfg'.s.map e'.toEmbedding = s' ∧
            (∀ i, (cfg'.T (e'.symm i)).shade = (T' i).shade \ Light) ∧
            cfg'.a = δ ∧ cfg'.b = δ ∧
            (∀ j ∈ cfg'.s, (cfg'.T j).toTube.IsCentred) := by
  classical
  have hη1 : η ≤ 1 := by
    have h1 := params.slabDensity
    have h2 := params.scale
    linarith
  have hexscal1 : exscal ≤ 1 := le_of_lt (lt_trans params.scale (by norm_num))
  set Lc : NNReal := Tube.coverCountLoss 3 with hLc_def
  filter_upwards [eventually_gridFine hη,
      eventually_aScaleData_absorb_of_le 1 h8,
      eventually_coarseLoss_absorb (η := η) (K := (4 : ℝ)) hη (by norm_num),
      Kakeya.ML2Assembly.eventually_card_thresholds,
      Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
        (K := ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal))
        ENNReal.coe_ne_top hη,
      Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg (K := ((Lc : NNReal) : ENNReal))
        ENNReal.coe_ne_top hη',
      w.eventually_radius (by linarith [params.slabDensity, hη] : (0:ℝ) < exscal - η),
      eventually_nnreal_mul_rpow_le_const 2 1 one_pos (half_pos hη)] with
    δ hgrid habs hcoarse hthr hindloss hLcap hwδ hhalf
  obtain ⟨hδ, hδ1, hδC⟩ := hthr
  intro ι s T hball hcen huni hmax hfull hcount s' T' Light hL hs' htube hsh ⟨C₀, hC₀, hcap, ⟨𝒱⟩⟩
    htc hmass hfloor hmass2 hclm
  -- the enlarged uniformity constant, transported to the cut family
  set C₁ : NNReal := max C₀ Lc with hC₁_def
  have hC₁ : 1 ≤ C₁ := le_trans hC₀ (le_max_left _ _)
  have hcap₁ : (C₁ : ENNReal) ≤ (δ : ENNReal) ^ (-η') := by
    rw [hC₁_def, ENNReal.coe_max]
    exact max_le hcap hLcap
  have huni₁ : Nonempty (ShadedTube.ShadedUniformTubeSet s'
      (fun i ↦ deleteShadeTube (T' i) Light hL) (Tube.ssfGridLen δ) C₁) :=
    ⟨shadedUniform_deleteShadeTube (𝒱.mono (le_max_left _ _)) Light hL⟩
  -- carriers of the cut family are the original carriers
  have htube'' : ∀ i, (deleteShadeTube (T' i) Light hL).toTube = (T i).toTube := fun i => htube i
  have hsh'' : ∀ i, (deleteShadeTube (T' i) Light hL).shade ⊆ (T i).shade :=
    fun i => Set.sdiff_subset.trans (hsh i)
  have hbody'' : ∀ i, (deleteShadeTube (T' i) Light hL).toConvexSpaceBody =
      (T i).toConvexSpaceBody :=
    fun i => congrArg Tube.toConvexSpaceBody (htube'' i)
  have hcarset'' : ∀ i, (deleteShadeTube (T' i) Light hL).carrier = (T i).carrier :=
    fun i => congrArg ConvexSpaceBody.carrier (hbody'' i)
  have hball'' : ∀ i ∈ s, (deleteShadeTube (T' i) Light hL).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi; rw [hcarset'' i]; exact hball i hi
  have hmax'' : maxDensity s (fun i ↦ (deleteShadeTube (T' i) Light hL).toConvexSpaceBody) ≤
      (δ : ENNReal) ^ (-η) := by
    rw [maxDensity_congr (fun i _ => hbody'' i)]; exact hmax
  have hmaxs'' : maxDensity s' (fun i ↦ (deleteShadeTube (T' i) Light hL).toConvexSpaceBody) ≤
      (δ : ENNReal) ^ (-η) :=
    le_trans (maxDensity_mono _ hs') hmax''
  -- the `ρ`-count datum: the count on the parent `s` itself, with the parent's hierarchy at
  -- Lemma 9.1's constant and the retention `δ^{2η}|s| ≤ |s'|`
  have hret : (δ : ENNReal) ^ (2 * η) * (s.card : ENNReal) ≤ (s'.card : ENNReal) :=
    card_retention_of_mass hδ hδ1 hs' htube hfull
      (ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.coe_le_one_iff.mpr hδ1) (by linarith)) hmass
  have hrho : RhoParentData δ ζ exscal η s' (fun i ↦ deleteShadeTube (T' i) Light hL) :=
    rhoParentData_of_binders hs' htube'' hball hmax huni hcount hret
  -- the cardinality budget, from the binders
  have hcardR : (s'.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) :=
    Kakeya.ML2Assembly.card_le_rpow_neg_four hδ hδ1 hδC s'
      (fun i ↦ deleteShadeTube (T' i) Light hL) (fun i hi => hball'' i (hs' hi)) hη1 hmaxs''
  have hcardN : ((s'.card : NNReal)) ≤ δ ^ (-(4 : ℝ)) := by
    have h : ((s'.card : NNReal) : ℝ) ≤ ((δ ^ (-(4 : ℝ)) : NNReal) : ℝ) := by
      rw [NNReal.coe_natCast, NNReal.coe_rpow]; exact hcardR
    exact_mod_cast h
  have hs'ne : s'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s' with h | h
    · rw [h] at htc; simp at htc
    · exact h
  obtain ⟨i₀, hi₀⟩ := hs'ne
  have hloss := hcoarse s'.card (Finset.card_pos.mpr ⟨i₀, hi₀⟩) hcardN
  -- the working dimensions, at `a = b = δ`
  have hdd : δ ≤ δ ^ exscal := by
    have h := NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 hexscal1
    simpa using h
  -- the per-tube floor of the cut family, in the record's form
  have hpt'' : ∀ i ∈ s', (δ : ENNReal) ^ (2 * η) *
      volume (deleteShadeTube (T' i) Light hL).toShadedBody.carrier ≤
      volume (deleteShadeTube (T' i) Light hL).toShadedBody.shade :=
    fun i hi => hfloor i hi
  -- the retention constant `c' = 2⁻¹ δ^{η/2}`
  have hδE0 : (δ : ENNReal) ≠ 0 := by exact_mod_cast hδ.ne'
  have hc'coe : (((2 : NNReal)⁻¹ * δ ^ (η / 2) : NNReal) : ENNReal) =
      (2 : ENNReal)⁻¹ * (δ : ENNReal) ^ (η / 2) := by
    rw [ENNReal.coe_mul, ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat,
      ENNReal.coe_rpow_of_ne_zero hδ.ne']
  have hmass'' : (((2 : NNReal)⁻¹ * δ ^ (η / 2) : NNReal) : ENNReal) *
      ∑ i ∈ s, volume (T i).shade ≤
      ∑ i ∈ s', volume (deleteShadeTube (T' i) Light hL).shade := by
    rw [hc'coe]
    calc (2 : ENNReal)⁻¹ * (δ : ENNReal) ^ (η / 2) * ∑ i ∈ s, volume (T i).shade
        = (2 : ENNReal)⁻¹ * ((δ : ENNReal) ^ (η / 2) * ∑ i ∈ s, volume (T i).shade) := by ring
      _ ≤ (2 : ENNReal)⁻¹ * ∑ i ∈ s', volume (T' i).shade := by gcongr
      _ ≤ ∑ i ∈ s', volume ((T' i).shade \ Light) := hmass2
  have hgain : (δ : ENNReal) ^ η ≤ (((2 : NNReal)⁻¹ * δ ^ (η / 2) : NNReal) : ENNReal) := by
    rw [hc'coe]
    have hhalf' : (δ : ENNReal) ^ (η / 2) ≤ (2 : ENNReal)⁻¹ := by
      have h2 : ((2 * δ ^ (η / 2) : NNReal) : ENNReal) ≤ 1 := by exact_mod_cast hhalf
      rw [ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_rpow_of_ne_zero hδ.ne'] at h2
      rw [ENNReal.le_inv_iff_mul_le, mul_comm]
      exact h2
    calc (δ : ENNReal) ^ η = (δ : ENNReal) ^ (η / 2) * (δ : ENNReal) ^ (η / 2) := by
          rw [← ENNReal.rpow_add _ _ hδE0 ENNReal.coe_ne_top]; congr 1; ring
      _ ≤ (2 : ENNReal)⁻¹ * (δ : ENNReal) ^ (η / 2) := by gcongr
  refine ⟨ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₁ hgrid (habs C₁ hC₁ hcap₁)
      hball hmax hs' htube'' hrho huni₁ hpt'' htc hloss hindloss hclm (a := δ) (b := δ)
      ⟨le_rfl, le_rfl, hdd⟩,
    Equiv.refl ι, (2 : NNReal)⁻¹ * δ ^ (η / 2), ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ofFamily_isCRefinement hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₁ hgrid
      (habs C₁ hC₁ hcap₁) hball hmax hs' htube'' hrho huni₁ hpt'' htc hloss hindloss hclm
      ⟨le_rfl, le_rfl, hdd⟩ hsh'' hmass'',
    hgain, ?_, fun _ => rfl, rfl, rfl, ?_⟩
  -- the index equivalence is the identity; the implicit type arguments of `toEmbedding` are the
  -- configuration's `ι`, so re-state the goal over `ι` before simplifying
  · change Finset.map (Equiv.refl ι).toEmbedding s' = s'
    simp only [Equiv.refl_toEmbedding, Finset.map_refl]
  · intro j hj
    change (deleteShadeTube (T' j) Light hL).toTube.IsCentred
    rw [htube'' j]
    exact hcen j (hs' hj)

end Kakeya.VeryNotSticky
