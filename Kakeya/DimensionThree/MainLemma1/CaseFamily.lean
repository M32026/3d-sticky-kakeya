/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.RelativePlank
public import Kakeya.Factoring.Pigeonhole

/-!
# The input reduction of GWZ Lemma 8.1: producing a uniform family

`Kakeya.ml1Boot.IsCaseFamily` is the standing hypothesis of both branches of GWZ Lemma 8.1,
and `Kakeya.FrostmanEstimate` supplies nothing of the kind: its families are pairwise
essentially distinct and live in `B₁`, but they are neither uniform along the grid of GWZ
Definition 2.2 nor banded in shade density.  This file is the passage between the two.

The construction is three pigeonholes, in the one order that works.

1. **Band the shade volumes** (`Kakeya.ml1Boot.exists_massBand`).  This cuts the index set and
   leaves the shading alone, so the band it produces is a statement about the *given* shading.
   Its role here is not the band itself — `Kakeya.ml1Boot.IsCaseFamily` has no band field — but
   the *conversion of counts into mass* that the band makes available at the next step.
2. **Uniformize the tubes** (`Tube.exists_uniformTubeSet_subfamily_ssf`) at the grid length
   `Tube.ssfGridLen δ`.  This cuts the index set again and returns only a *cardinality*
   retention; the band of step 1 restricts to the smaller index set, being a per-tube
   statement, and converts that cardinality retention into the mass retention the multiplicity
   and fullness clauses need (`Kakeya.ShadedBody.card_le_iff_isCRefinement_of_comparable`).
3. **Refine the shading** (`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet`).  This is
   the step that must come last: it does *not* move the index set, and it builds its bundle on
   the hierarchy handed to it, so the tube-level work of step 2 survives it verbatim.

The uniformity constant that comes out is exactly `ShadedTube.ssfUniformConst n`: step 2 lands
at `Tube.uniformConst n` and step 3 weakens it to `max (Tube.uniformConst n) 4`, which is that
constant by definition.  That matters downstream — it is what
`Kakeya.ml1Boot.multiplicity_le_of_frostmanAtEveryScale` caps its `Cunif` by.

## What this does not supply, and why

`Kakeya.ml1Boot.IsCaseTwoInput` carries, besides the clauses about the dichotomy, a **shade
density band** on the family `Kakeya.ml1Boot.IsCaseFamily` is asserted of.  This file does not
produce one, and no composition of the tools in the development does: step 3 shrinks the
shadings, and it shrinks them by an amount that is controlled only in aggregate (a fullness
comparison), never tube by tube, so the band of step 1 does not survive it.  Re-banding
afterwards restores the band and destroys the bundle, since
`ShadedTube.ShadedUniformTubeSet.le_card_shadeClass` is a *lower* bound on a filtered
cardinality and shrinks under restriction; the two pigeonholes do not commute and neither
order terminates.

Closing that gap needs a shaded uniformization that preserves a supplied per-tube density band
— the same "simultaneous, nesting-preserving uniformization" that
`Kakeya.ml1Boot.exists_uniformFactorCore` is blocked on, one level down.  It is recorded here
rather than worked around because a reader of the docstring of
`Kakeya.ml1Boot.IsCaseTwoInput.band` would otherwise conclude that the band comes for free with
the uniformization ("the banding is asserted of a family that has already been pigeonholed to a
dyadic shade-density band"), which is not something any declaration provides.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

noncomputable section

namespace Kakeya

namespace ml1Boot

universe u

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


/-! ### Converting a cardinality retention into a mass retention -/

/-- **A banded family turns a cardinality share into a shade-mass share.**

`Tube.exists_uniformTubeSet_subfamily_ssf` retains a `δ ^ α` share of the *count*, and says
nothing about the shading.  On a family whose shade densities are banded at `λ_*` — which is
what `Kakeya.ml1Boot.exists_massBand` supplies, at ratio `Λ = 2` — that is the same thing as
retaining a `δ ^ α / 4` share of the shade *mass*, all `δ`-tubes having one common volume.

This is `Kakeya.ShadedBody.card_le_iff_isCRefinement_of_comparable` at `Λ = 2` and `μ₀ = λ_*`,
with the cardinality hypothesis restated in the real-valued form the uniformization produces
and the band in the form `Kakeya.ml1Boot.exists_massBand` produces. -/
theorem isCRefinement_of_card_le_of_band [Nontrivial E] {δ : NNReal} (hδ0 : 0 < δ) {ι : Type*}
    {s s' : Finset ι} (T : ι → ShadedTube δ E) (hs : s.Nonempty) (hs' : s' ⊆ s)
    (hs'ne : s'.Nonempty) {lam : NNReal} (hlam : 0 < lam)
    (hband : ∀ i ∈ s, (lam : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ 2 * (lam : ENNReal) * volume (T i).carrier)
    {κ : NNReal} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hcard : κ * s.card ≤ (s'.card : NNReal)) :
    ShadedBody.IsCRefinement s' (fun i => (T i).toShadedBody) s (fun i => (T i).toShadedBody)
      (κ * ((2 : NNReal) ^ 2)⁻¹) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hs
  set v : ENNReal := volume (T i₀).carrier with hv_def
  have hvol : ∀ i ∈ s, volume ((T i).toShadedBody).carrier = v := by
    intro i _
    simpa [hv_def] using
      _root_.Tube.volume_carrier_eq_volume_carrier (T i).toTube (T i₀).toTube
  have hv_pos : 0 < v := by
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hδp : 0 < (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ0) (Module.finrank ℝ E - 1)
    exact lt_of_lt_of_le (ENNReal.mul_pos hc.ne' hδp.ne')
      (by simpa [hv_def] using _root_.Tube.le_volume (T i₀).toTube)
  have hlow : ∀ i ∈ s, ((2 : NNReal) : ENNReal)⁻¹ * (lam : ENNReal) * v
      ≤ volume ((T i).toShadedBody).shade := by
    intro i hi
    refine le_trans ?_ (hband i hi).1
    have hcar : volume (T i).carrier = v := hvol i hi
    rw [hcar]
    have hinv : ((2 : NNReal) : ENNReal)⁻¹ ≤ 1 := by
      rw [ENNReal.inv_le_one]
      exact_mod_cast (by norm_num : (1 : NNReal) ≤ 2)
    calc ((2 : NNReal) : ENNReal)⁻¹ * (lam : ENNReal) * v
        ≤ 1 * (lam : ENNReal) * v := by gcongr
      _ = (lam : ENNReal) * v := by rw [one_mul]
  have hupp : ∀ i ∈ s, volume ((T i).toShadedBody).shade
      ≤ ((2 : NNReal) : ENNReal) * (lam : ENNReal) * v := by
    intro i hi
    have h := (hband i hi).2
    rw [hvol i hi] at h
    simpa [mul_assoc] using h
  exact (ShadedBody.card_le_iff_isCRefinement_of_comparable (V := fun i => (T i).toShadedBody)
    ⟨i₀, hi₀⟩ hvol hv_pos.ne' (by norm_num) (ENNReal.coe_ne_zero.mpr hlam.ne')
    ENNReal.coe_ne_top hlow hupp hs' hs'ne).2 κ hκ0 hκ1 hcard

/-! ### The input reduction -/

/-- **From a `K_F`-shaped family to a uniform one** (the producer of
`Kakeya.ml1Boot.IsCaseFamily`, blueprint `lem:ml1bootCaseFamily`).

`Kakeya.FrostmanEstimate` hands out a family of pairwise essentially distinct shaded `δ`-tubes
in `B₁` of fullness at least `δ ^ η`, and nothing else.  This lemma turns it into a family
carrying GWZ Definition 2.2 at the grid length `Tube.ssfGridLen δ` and the dimension-only
constant `ShadedTube.ssfUniformConst n`, at a loss `δ ^ (-α)` in each of the four quantities the
rest of Section 8 reads — the cardinality, the Frostman constant, the fullness and the
multiplicity — for every `α > 0`, every `0 < η ≤ α / 4`, and all sufficiently small `δ`.

The output keeps the *tubes* (`hT₁tube`) and only shrinks the shadings (`hT₁shade`), so
essential distinctness, the `B₁` containment and every geometric hypothesis of the caller
descend to it verbatim.

## The fullness hypothesis is what makes this true

The four clauses are not independent of it, and it is not a convenience.  Transporting a
Frostman *upper* bound to a subfamily costs the ratio of cardinalities
(`ConvexSpaceBody.frostmanConstIn_subfamily_le`, and that is sharp, the constant being
normalized by the family's own count), so the Frostman clause needs a **cardinality** share,
whereas the fullness and multiplicity clauses need a **shade-mass** share.  On a general family
no pigeonhole delivers both:

> one tube shaded fully, together with `N` tubes each shaded to a fraction `N ^ (-2)` of its
> volume.  The mass sits on the first tube and the count on the other `N`, and a subfamily on
> which the shade densities are comparable lies in one group or the other.

That family has fullness `≈ 1 / N`, so at `N ≈ δ ^ (-7)` — the packing bound
`Kakeya.ml1Boot.eventually_card_le_rpow_neg_seven` for essentially distinct tubes in `B₁ ⊆ ℝ³` —
its fullness is `≈ δ ^ 7`, and the hypothesis `δ ^ η ≤ λ` with `η ≤ α / 4` small excludes it.
That is exactly the gap the first step exploits.

## The three pigeonholes, in the one order that works

1. **Discard the tubes of below-average shade density**
   (`Kakeya.ShadedBody.discardLowShading` at level `1/2`).  This keeps half the shade mass, and
   on what it keeps the shade densities lie in `[λ/2, 1]` — a band of ratio `2/λ ≤ 2 δ ^ (-η)`,
   subpolynomial by the fullness hypothesis and *not* a bounded ratio.  Because every shade is
   at most a tube volume, keeping half the mass also keeps a `λ/2` share of the **count**: this
   is the step that supplies the cardinality share, and it is available only here.
2. **Uniformize the tubes** (`Tube.exists_uniformTubeSet_subfamily_ssf`) at the grid length
   `Tube.ssfGridLen δ`.  This returns only a cardinality retention; the band of step 1 restricts
   to the smaller index set, being a per-tube statement, and converts that retention into the
   mass retention the fullness and multiplicity clauses need.
3. **Refine the shading** (`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet`).  This is
   the step that must come last: it does *not* move the index set, and it builds its bundle on
   the hierarchy handed to it, so the tube-level work of step 2 survives it verbatim.

The uniformity constant that comes out is exactly `ShadedTube.ssfUniformConst n`: step 2 lands
at `Tube.uniformConst n` and step 3 weakens it to `max (Tube.uniformConst n) 4`, which is that
constant by definition.  That matters downstream — it is what
`Kakeya.ml1Boot.multiplicity_le_of_frostmanAtEveryScale` caps its `Cunif` by.

At budget `α` each of the four losses is run at `α / 4`: the band ratio `2 δ ^ (-η)` of step 1,
the prescribed `δ ^ (-α/4)` of step 2, the `Kakeya.relativePlankShadeLoss` of step 3 (absorbed
by `Kakeya.exists_threshold_relativePlankTotalLoss_le`, the shade loss being a factor of the
total one), and the numeral `4` collecting the two halvings.

## What this does not supply

No band of *bounded* ratio on the output.  Step 1 gives ratio `2 δ ^ (-η)`, which is what the
Frostman and count clauses are proved from, but `Kakeya.ml1Boot.IsCaseTwoInput.band` asks for
ratio `2`, and cutting down to a dyadic sub-band after step 3 breaks the bundle:
`ShadedTube.ShadedUniformTubeSet.le_card_shadeClass` is a *lower* bound on a filtered
cardinality and does not survive a restriction of the index set, while step 3 shrinks the
shadings by an amount controlled only in aggregate and so does not preserve a band supplied
before it.  The two pigeonholes do not commute and alternating them does not terminate.  That
is the same obstruction `Kakeya.ml1Boot.exists_uniformFactorCore` is blocked on one level down,
where `IsUniformFactorCore.fine_unif` and `.fine_dens` make the same pair of demands. -/
theorem exists_caseFamily [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (hηα : η ≤ α / 4) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (δ : ENNReal) ^ η
          ≤ (ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal) →
        ∃ s₁ ⊆ s, ∃ T₁ : ι → ShadedTube δ E,
          (∀ i, (T₁ i).toTube = (T i).toTube) ∧
          (∀ i, (T₁ i).shade ⊆ (T i).shade) ∧
          s₁.Nonempty ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s₁ T₁ (Tube.ssfGridLen δ)
            (ShadedTube.ssfUniformConst (Module.finrank ℝ E))) ∧
          (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-α) * (s₁.card : ENNReal) ∧
          frostmanConstIn s₁ (fun i => (T₁ i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall
            ≤ (δ : ENNReal) ^ (-α)
              * frostmanConstIn s (fun i => (T i).toConvexSpaceBody)
                  ConvexSpaceBody.closedUnitBall ∧
          (δ : ENNReal) ^ α * (ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal)
            ≤ (ShadedBody.fullness s₁ (fun i => (T₁ i).toShadedBody) : ENNReal) ∧
          ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
            ≤ (δ : ENNReal) ^ (-α)
              * ShadedBody.multiplicity s₁ (fun i => (T₁ i).toShadedBody) := by
  classical
  have hα4 : (0 : ℝ) < α / 4 := by positivity
  obtain ⟨δU, hδUpos, hδUle1, hU⟩ :=
    Tube.exists_uniformTubeSet_subfamily_ssf (E := E) 7 (α / 4) hα4
  obtain ⟨δS, hδSpos, hδSle1, hSthr⟩ :=
    exists_threshold_relativePlankTotalLoss_le 7 (α / 4) hα4
  obtain ⟨δG, hδGpos, hδGle1, hGthr⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le 1 le_rfl 0 1 1 one_pos
  obtain ⟨δ4, hδ4pos, hδ4le1, h4thr⟩ := exists_threshold_natCast_le_rpow 4 (α / 4) hα4
  filter_upwards [eventually_card_le_rpow_neg_seven (E := E) hdim,
      eventually_le_nhdsGT (c := δU) hδUpos,
      eventually_le_nhdsGT (c := δS) hδSpos,
      eventually_le_nhdsGT (c := δG) hδGpos,
      eventually_le_nhdsGT (c := δ4) hδ4pos,
      eventually_le_nhdsGT (c := (1 : NNReal)) one_pos,
      self_mem_nhdsWithin]
    with δ hcard7 hδU hδS hδG hδ4 hδ1 hδmem
  have hδ0 : (0 : NNReal) < δ := hδmem
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδe0 : (δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hδ0).ne'
  have hδetop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h4E : (4 : ENNReal) ≤ (δ : ENNReal) ^ (-(α / 4)) := by
    rw [ennreal_coe_nnreal_rpow hδR (-(α / 4)),
      show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by simp]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast h4thr hδ0 hδ4)
  have h2E : (2 : ENNReal) ≤ (δ : ENNReal) ^ (-(α / 4)) :=
    le_trans (by norm_num) h4E
  intro ι s T hball hED hfull
  set F : ENNReal := (ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal) with hF_def
  have hFtop : F ≠ ⊤ := by rw [hF_def]; exact ENNReal.coe_ne_top
  have hFpos : 0 < F :=
    lt_of_lt_of_le (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ0) hδetop) hfull
  have hs : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with rfl | h
    · exact absurd hFpos (by simp [hF_def])
    · exact h
  obtain ⟨j₀, hj₀⟩ := hs
  set v : ENNReal := volume (T j₀).carrier with hv_def
  have hvpos : 0 < v := by
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hδp : 0 < (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ0) (Module.finrank ℝ E - 1)
    exact lt_of_lt_of_le (ENNReal.mul_pos hc.ne' hδp.ne')
      (by simpa [hv_def] using _root_.Tube.le_volume (T j₀).toTube)
  have hvtop : v ≠ ⊤ := (T j₀).isCompact.measure_ne_top
  have hcarr : ∀ i, volume (T i).carrier = v := fun i => by
    simpa [hv_def] using
      _root_.Tube.volume_carrier_eq_volume_carrier (T i).toTube (T j₀).toTube
  have hsumcar : ∀ X : Finset ι, ∑ i ∈ X, volume (T i).carrier = (X.card : ENNReal) * v :=
    fun X => by
      simpa [hv_def] using
        _root_.Tube.sum_volume_carrier_eq_card_mul (fun i => (T i).toTube) (T j₀).toTube X
  -- `M = F · #s · v`
  have hM : ∑ i ∈ s, volume (T i).shade = F * ((s.card : ENNReal) * v) := by
    rw [← hsumcar s, hF_def]
    exact ShadedBody.sum_volumeReal_shade_eq_fullness_mul s (fun i => (T i).toShadedBody)
  -- **Step 1.**  Discard the tubes of below-average shade density.
  set sa : Finset ι :=
    ShadedBody.discardLowShading s (fun i => (T i).toShadedBody) (2⁻¹ : NNReal) with hsa_def
  have hsa_sub : sa ⊆ s := ShadedBody.discardLowShading_subset _ _ _
  have hmass_a : (2 : ENNReal)⁻¹ * (∑ i ∈ s, volume (T i).shade)
      ≤ ∑ i ∈ sa, volume (T i).shade := by
    have h := ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading s
      (fun i => (T i).toShadedBody) (c := (2⁻¹ : NNReal)) (by norm_num)
    have hhalf : ((1 - (2⁻¹ : NNReal) : NNReal) : ENNReal) = (2 : ENNReal)⁻¹ := by
      norm_num
    rwa [hhalf] at h
  have hband_a : ∀ i ∈ sa, (2 : ENNReal)⁻¹ * F * v ≤ volume (T i).shade := by
    intro i hi
    have h := ShadedBody.le_volume_shade_of_mem_discardLowShading (c := (2⁻¹ : NNReal)) hi
    have hc : (((2⁻¹ : NNReal)) : ENNReal) = (2 : ENNReal)⁻¹ := by norm_num
    rwa [hc, ← hF_def, hcarr i] at h
  -- the count share of step 1
  have hcount_a : (2 : ENNReal)⁻¹ * F * (s.card : ENNReal) ≤ (sa.card : ENNReal) := by
    have hupper : ∑ i ∈ sa, volume (T i).shade ≤ (sa.card : ENNReal) * v := by
      calc ∑ i ∈ sa, volume (T i).shade
          ≤ ∑ i ∈ sa, volume (T i).carrier :=
            Finset.sum_le_sum fun i _ => measure_mono (T i).shade_subset
        _ = (sa.card : ENNReal) * v := hsumcar sa
    have hchain : (2 : ENNReal)⁻¹ * F * (s.card : ENNReal) * v ≤ (sa.card : ENNReal) * v := by
      calc (2 : ENNReal)⁻¹ * F * (s.card : ENNReal) * v
          = (2 : ENNReal)⁻¹ * (F * ((s.card : ENNReal) * v)) := by ring
        _ = (2 : ENNReal)⁻¹ * (∑ i ∈ s, volume (T i).shade) := by rw [hM]
        _ ≤ ∑ i ∈ sa, volume (T i).shade := hmass_a
        _ ≤ (sa.card : ENNReal) * v := hupper
    exact (ENNReal.mul_le_mul_iff_right hvpos.ne' hvtop).mp
      (by simpa [mul_comm] using hchain)
  have hsane : sa.Nonempty := by
    rw [← Finset.card_pos, ← Nat.cast_pos (α := ENNReal)]
    refine lt_of_lt_of_le ?_ hcount_a
    have hcs : (0 : ENNReal) < (s.card : ENNReal) := by
      exact_mod_cast Finset.card_pos.mpr ⟨j₀, hj₀⟩
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (show ((2 : ENNReal))⁻¹ ≠ 0 by simp) hFpos.ne').ne' hcs.ne'
  -- **Step 2.**  Uniformize the tubes on the truncated index set.
  have hcards : (s.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) :=
    hcard7 δ le_rfl s (fun i => (T i).toTube) (by simpa using hball) (by simpa using hED)
  have hcards_a : (sa.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) :=
    le_trans (by exact_mod_cast Finset.card_le_card hsa_sub) hcards
  obtain ⟨s₁, h₁a, hcardret, hunif⟩ :=
    hU hδ0 hδU sa (fun i => (T i).toTube)
      (fun i hi => by simpa using hball i (hsa_sub hi)) hcards_a
  have hs₁s : s₁ ⊆ s := h₁a.trans hsa_sub
  have hs₁ne : s₁.Nonempty := by
    rw [← Finset.card_pos]
    rcases Nat.eq_zero_or_pos s₁.card with hz | hpos
    · exfalso
      have h2 : (0 : ℝ) < (sa.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hsane
      rw [hz] at hcardret
      norm_num at hcardret
      exact (Finset.not_nonempty_iff_eq_empty.mpr hcardret) hsane
    · exact hpos
  -- **Step 3.**  Refine the shading against the hierarchy just built.
  have hNpos : 0 < Tube.ssfGridLen δ := (hGthr hδ0 hδG).1
  obtain ⟨T₁, hT₁tube, hT₁shade, hfullloss, 𝒱, _hix, _has, _htu, _hbn⟩ :=
    ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet (V := T) hunif.some hNpos
      (Nat.log 2 s.card)
      (fun t ht => Nat.log_mono_right (Finset.card_le_card (ht.trans hs₁s)))
  -- Notation for the two remaining losses.
  set L₃ : ENNReal := ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * Tube.ssfGridLen δ + 2)
    with hL₃_def
  have hL₃ : L₃ ≤ (δ : ENNReal) ^ (-(α / 4)) := by
    have hnat : ((relativePlankShadeLoss s.card (Tube.ssfGridLen δ) : ℕ) : ℝ)
        ≤ (δ : ℝ) ^ (-(α / 4)) := by
      refine le_trans ?_ (hSthr hδ0 hδS s.card hcards)
      exact_mod_cast Nat.le_mul_of_pos_left _
        (one_le_relativePlankJointLoss s.card (Tube.ssfGridLen δ))
    have hcast : L₃ = ((relativePlankShadeLoss s.card (Tube.ssfGridLen δ) : ℕ) : ENNReal) := by
      rw [hL₃_def, relativePlankShadeLoss, relativePlankBucket]
      push_cast
      ring
    rw [hcast, ennreal_coe_nnreal_rpow hδR (-(α / 4)), ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hnat
  have hL₃0 : L₃ ≠ 0 := by
    rw [hL₃_def]
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))
  have hL₃top : L₃ ≠ ⊤ := by
    rw [hL₃_def]; exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  -- `F⁻¹` is subpolynomial, by the fullness hypothesis.
  have hFinv : F⁻¹ ≤ (δ : ENNReal) ^ (-η) := by
    rw [ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.mpr hfull
  -- the cardinality retention of step 2, in `ENNReal`
  have hcardE : (sa.card : ENNReal) ≤ (δ : ENNReal) ^ (-(α / 4)) * (s₁.card : ENNReal) := by
    rw [ennreal_coe_nnreal_rpow hδR (-(α / 4)), ← ENNReal.ofReal_natCast sa.card,
      ← ENNReal.ofReal_natCast s₁.card, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδR.le _)]
    exact ENNReal.ofReal_le_ofReal hcardret
  -- the band of step 1, on the retained index set
  have hband₁ : ∀ i ∈ s₁, (2 : ENNReal)⁻¹ * F * v ≤ volume (T i).shade :=
    fun i hi => hband_a i (h₁a hi)
  have hmass₁ : (2 : ENNReal)⁻¹ * F * ((s₁.card : ENNReal) * v)
      ≤ ∑ i ∈ s₁, volume (T i).shade := by
    calc (2 : ENNReal)⁻¹ * F * ((s₁.card : ENNReal) * v)
        = ∑ _i ∈ s₁, (2 : ENNReal)⁻¹ * F * v := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ s₁, volume (T i).shade := Finset.sum_le_sum hband₁
  -- the four `α / 4` slots
  have hquarter : ∀ x y : ℝ, x = -(α / 4) → y = -(α / 4) →
      (δ : ENNReal) ^ x * (δ : ENNReal) ^ y = (δ : ENNReal) ^ (x + y) := by
    intro x y _ _; rw [← ENNReal.rpow_add _ _ hδe0 hδetop]
  have hηq : (δ : ENNReal) ^ (-η) ≤ (δ : ENNReal) ^ (-(α / 4)) :=
    ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1) (by linarith)
  -- **The cardinality clause.**
  have hcount : (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-α) * (s₁.card : ENNReal) := by
    have hsplit : (s.card : ENNReal) = (2 * F⁻¹) * ((2 : ENNReal)⁻¹ * F * (s.card : ENNReal)) := by
      rw [show (2 * F⁻¹) * ((2 : ENNReal)⁻¹ * F * (s.card : ENNReal))
          = (2 * (2 : ENNReal)⁻¹) * (F⁻¹ * F) * (s.card : ENNReal) by ring,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
        ENNReal.inv_mul_cancel hFpos.ne' hFtop, one_mul, one_mul]
    calc (s.card : ENNReal)
        = (2 * F⁻¹) * ((2 : ENNReal)⁻¹ * F * (s.card : ENNReal)) := hsplit
      _ ≤ (2 * F⁻¹) * ((δ : ENNReal) ^ (-(α / 4)) * (s₁.card : ENNReal)) :=
          mul_le_mul_right (hcount_a.trans hcardE) _
      _ ≤ ((δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4)))
            * ((δ : ENNReal) ^ (-(α / 4)) * (s₁.card : ENNReal)) :=
          mul_le_mul_left (mul_le_mul' h2E (hFinv.trans hηq)) _
      _ = (δ : ENNReal) ^ (-(3 * α / 4)) * (s₁.card : ENNReal) := by
          rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδe0 hδetop,
            ← ENNReal.rpow_add _ _ hδe0 hδetop]
          ring_nf
      _ ≤ (δ : ENNReal) ^ (-α) * (s₁.card : ENNReal) :=
          mul_le_mul_left (ENNReal.rpow_le_rpow_of_exponent_ge
            (show ((δ : NNReal) : ENNReal) ≤ 1 by exact_mod_cast hδ1) (by linarith)) _
  -- the shade refinement, as a mass inequality
  have hDcar₁ : ∑ i ∈ s₁, volume (T₁ i).carrier = ∑ i ∈ s₁, volume (T i).carrier :=
    Finset.sum_congr rfl fun i _ =>
      congrArg (fun U : _root_.Tube δ E => volume U.carrier) (hT₁tube i)
  have hDpos : ∑ i ∈ s₁, volume (T i).carrier ≠ 0 := by
    rw [hsumcar s₁]
    exact (ENNReal.mul_pos (by exact_mod_cast Finset.card_ne_zero.mpr hs₁ne) hvpos.ne').ne'
  have hDtop : ∑ i ∈ s₁, volume (T i).carrier ≠ ⊤ := by
    rw [hsumcar s₁]; exact ENNReal.mul_ne_top (by simp) hvtop
  have hshadeMass : ∑ i ∈ s₁, volume (T i).shade
      ≤ L₃ * ∑ i ∈ s₁, volume (T₁ i).shade := by
    have h := hfullloss
    simp only [ShadedBody.fullness'] at h
    rw [show (∑ i ∈ s₁, volume ((T₁ i).toShadedBody).carrier)
        = ∑ i ∈ s₁, volume (T i).carrier from hDcar₁] at h
    set D : ENNReal := ∑ i ∈ s₁, volume (T i).carrier
    calc ∑ i ∈ s₁, volume (T i).shade
        = (∑ i ∈ s₁, volume (T i).shade) / D * D :=
          (ENNReal.div_mul_cancel hDpos hDtop).symm
      _ ≤ L₃ * ((∑ i ∈ s₁, volume (T₁ i).shade) / D) * D := mul_le_mul_left h D
      _ = L₃ * ((∑ i ∈ s₁, volume (T₁ i).shade) / D * D) := by ring
      _ = L₃ * ∑ i ∈ s₁, volume (T₁ i).shade := by
          rw [ENNReal.div_mul_cancel hDpos hDtop]
  have hbodies : ∀ i, (T₁ i).toConvexSpaceBody = (T i).toConvexSpaceBody := fun i =>
    congrArg Tube.toConvexSpaceBody (hT₁tube i)
  have h3q : (δ : ENNReal) ^ (-(3 * α / 4)) ≤ (δ : ENNReal) ^ (-α) :=
    ENNReal.rpow_le_rpow_of_exponent_ge
      (show ((δ : NNReal) : ENNReal) ≤ 1 by exact_mod_cast hδ1) (by linarith)
  refine ⟨s₁, hs₁s, T₁, hT₁tube, hT₁shade, hs₁ne, ⟨𝒱⟩, hcount, ?_, ?_, ?_⟩
  -- **The Frostman clause.**
  · have hκpos : ((δ : ENNReal) ^ α) ≠ 0 :=
      (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ0) hδetop).ne'
    have hκcard : (δ : ENNReal) ^ α * (s.card : ENNReal) ≤ (s₁.card : ENNReal) := by
      calc (δ : ENNReal) ^ α * (s.card : ENNReal)
          ≤ (δ : ENNReal) ^ α * ((δ : ENNReal) ^ (-α) * (s₁.card : ENNReal)) :=
            mul_le_mul_right hcount _
        _ = (s₁.card : ENNReal) := by
            rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδe0 hδetop]
            simp
    have hWK : ∀ i ∈ s, (T i).toConvexSpaceBody
        ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
      intro i hi
      change (T i).carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      rw [ConvexSpaceBody.closedUnitBall_carrier]
      exact hball i hi
    have hf := ConvexSpaceBody.frostmanConstIn_subfamily_le
      (s := s) (s' := s₁) (W := fun i => (T i).toConvexSpaceBody)
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
      (κ := (δ : ENNReal) ^ α) (v := v) ⟨j₀, hj₀⟩ (fun i _ => hcarr i) hWK hs₁s hκpos hκcard
    simp only [hbodies]
    rwa [← ENNReal.rpow_neg] at hf
  -- **The fullness clause.**
  · have hfull₁T : (2 : ENNReal)⁻¹ * F
        ≤ ShadedBody.fullness' s₁ (fun i => (T i).toShadedBody) := by
      simp only [ShadedBody.fullness']
      rw [ENNReal.le_div_iff_mul_le (Or.inl hDpos) (Or.inl hDtop), hsumcar s₁]
      exact hmass₁
    have hkey : L₃ * ((δ : ENNReal) ^ α * F)
        ≤ L₃ * ShadedBody.fullness' s₁ (fun i => (T₁ i).toShadedBody) := by
      calc L₃ * ((δ : ENNReal) ^ α * F)
          ≤ (δ : ENNReal) ^ (-(α / 4)) * ((δ : ENNReal) ^ α * F) := mul_le_mul_left hL₃ _
        _ = (δ : ENNReal) ^ (3 * α / 4) * F := by
            rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδe0 hδetop]
            ring_nf
        _ ≤ (2 : ENNReal)⁻¹ * F := by
            refine mul_le_mul_left ?_ F
            have h2big : (2 : ENNReal) ≤ ((δ : ENNReal) ^ (3 * α / 4))⁻¹ := by
              rw [← ENNReal.rpow_neg]
              refine le_trans h2E (ENNReal.rpow_le_rpow_of_exponent_ge
                (show ((δ : NNReal) : ENNReal) ≤ 1 by exact_mod_cast hδ1) (by linarith))
            have hinv := ENNReal.inv_le_inv.mpr h2big
            rwa [inv_inv] at hinv
        _ ≤ L₃ * ShadedBody.fullness' s₁ (fun i => (T₁ i).toShadedBody) :=
            le_trans hfull₁T hfullloss
    rw [ShadedBody.coe_fullness]
    refine (ENNReal.mul_le_mul_iff_left hL₃0 hL₃top).mp ?_
    simpa [mul_comm] using hkey
  -- **The multiplicity clause.**
  · have hMa : ∑ i ∈ s, volume (T i).shade ≤ 2 * ∑ i ∈ sa, volume (T i).shade := by
      calc ∑ i ∈ s, volume (T i).shade
          = 2 * ((2 : ENNReal)⁻¹ * ∑ i ∈ s, volume (T i).shade) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ 2 * ∑ i ∈ sa, volume (T i).shade := mul_le_mul_right hmass_a _
    have hSaUp : ∑ i ∈ sa, volume (T i).shade
        ≤ (δ : ENNReal) ^ (-(α / 4)) * ((s₁.card : ENNReal) * v) := by
      calc ∑ i ∈ sa, volume (T i).shade
          ≤ ∑ i ∈ sa, volume (T i).carrier :=
            Finset.sum_le_sum fun i _ => measure_mono (T i).shade_subset
        _ = (sa.card : ENNReal) * v := hsumcar sa
        _ ≤ ((δ : ENNReal) ^ (-(α / 4)) * (s₁.card : ENNReal)) * v :=
            mul_le_mul_left hcardE v
        _ = (δ : ENNReal) ^ (-(α / 4)) * ((s₁.card : ENNReal) * v) := by ring
    have hS1 : (s₁.card : ENNReal) * v
        ≤ 2 * F⁻¹ * ∑ i ∈ s₁, volume (T i).shade := by
      calc (s₁.card : ENNReal) * v
          = (2 * F⁻¹) * ((2 : ENNReal)⁻¹ * F * ((s₁.card : ENNReal) * v)) := by
            rw [show (2 * F⁻¹) * ((2 : ENNReal)⁻¹ * F * ((s₁.card : ENNReal) * v))
                = (2 * (2 : ENNReal)⁻¹) * (F⁻¹ * F) * ((s₁.card : ENNReal) * v) by ring,
              ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
              ENNReal.inv_mul_cancel hFpos.ne' hFtop, one_mul, one_mul]
        _ ≤ (2 * F⁻¹) * ∑ i ∈ s₁, volume (T i).shade := mul_le_mul_right hmass₁ _
        _ = 2 * F⁻¹ * ∑ i ∈ s₁, volume (T i).shade := by ring
    have hnum : ∑ i ∈ s, volume (T i).shade
        ≤ (δ : ENNReal) ^ (-α) * ∑ i ∈ s₁, volume (T₁ i).shade := by
      calc ∑ i ∈ s, volume (T i).shade
          ≤ 2 * ∑ i ∈ sa, volume (T i).shade := hMa
        _ ≤ 2 * ((δ : ENNReal) ^ (-(α / 4)) * ((s₁.card : ENNReal) * v)) :=
            mul_le_mul_right hSaUp _
        _ ≤ 2 * ((δ : ENNReal) ^ (-(α / 4))
              * (2 * F⁻¹ * ∑ i ∈ s₁, volume (T i).shade)) := by
            exact mul_le_mul_right (mul_le_mul_right hS1 _) _
        _ ≤ 2 * ((δ : ENNReal) ^ (-(α / 4))
              * (2 * F⁻¹ * (L₃ * ∑ i ∈ s₁, volume (T₁ i).shade))) := by
            exact mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hshadeMass _) _) _
        _ = (2 * 2) * ((δ : ENNReal) ^ (-(α / 4)) * (F⁻¹ * L₃))
              * ∑ i ∈ s₁, volume (T₁ i).shade := by ring
        _ ≤ ((δ : ENNReal) ^ (-(α / 4)))
              * ((δ : ENNReal) ^ (-(α / 4))
                * ((δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4))))
              * ∑ i ∈ s₁, volume (T₁ i).shade := by
            refine mul_le_mul_left (mul_le_mul' ?_ (mul_le_mul' le_rfl ?_)) _
            · exact_mod_cast h4E
            · exact mul_le_mul' (hFinv.trans hηq) hL₃
        _ = (δ : ENNReal) ^ (-α) * ∑ i ∈ s₁, volume (T₁ i).shade := by
            rw [← ENNReal.rpow_add _ _ hδe0 hδetop, ← ENNReal.rpow_add _ _ hδe0 hδetop,
              ← ENNReal.rpow_add _ _ hδe0 hδetop]
            ring_nf
    have hden : volume (⋃ i ∈ s₁, (T₁ i).shade) ≤ volume (⋃ i ∈ s, (T i).shade) :=
      measure_mono (Set.iUnion₂_subset fun i hi =>
        (hT₁shade i).trans
          (Set.subset_iUnion₂ (s := fun i (_ : i ∈ s) => (T i).shade) i (hs₁s hi)))
    calc ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
        = (∑ i ∈ s, volume (T i).shade) / volume (⋃ i ∈ s, (T i).shade) := rfl
      _ ≤ ((δ : ENNReal) ^ (-α) * ∑ i ∈ s₁, volume (T₁ i).shade)
            / volume (⋃ i ∈ s₁, (T₁ i).shade) := ENNReal.div_le_div hnum hden
      _ = (δ : ENNReal) ^ (-α)
            * ShadedBody.multiplicity s₁ (fun i => (T₁ i).toShadedBody) := by
          rw [ShadedBody.multiplicity, mul_div_assoc]

/-- **The banded input reduction** (blueprint `lem:ml1bootCaseFamily`, in the form Case (ii)
consumes).

The same passage as `Kakeya.ml1Boot.exists_caseFamily`, with the third pigeonhole — the
refinement of the *shading* against the hierarchy — deleted, and the first two replaced by the
single mass banding `Kakeya.ml1Boot.exists_massBand`.  The shading is therefore **not touched**:
the conclusion speaks about the given `T` throughout, only the index set is cut down.

That is what makes the two clauses `Kakeya.ml1Boot.IsCaseTwoInput.band` (a band of ratio `2`,
which `exists_caseFamily` explicitly cannot produce) and `Kakeya.ml1Boot.IsCaseTwoInput.card_le`
simultaneously available, and with them `Kakeya.ml1Boot.IsCaseTwoInput.refine_mass` through
`Kakeya.ShadedBody.card_le_iff_isCRefinement_of_comparable`.  What is given up is the *shaded*
uniformity of GWZ Definition 2.2: the bundle returned here is the tube-level
`Tube.UniformTubeSet` only.  Case (i) does not lose by this — it rebuilds the shaded bundle on
the hierarchy the dichotomy hands it, through
`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet`, which is where the shading
refinement now happens and where the band is no longer needed.

The four `α / 4` slots are: the literal `2` of the band, the banding loss
`Kakeya.ml1Boot.bandLoss #s` (subpolynomial by
`Kakeya.ml1Boot.eventually_bandLoss_le_rpow_neg` together with the packing bound
`Kakeya.ml1Boot.eventually_card_le_rpow_neg_seven`), the inverse fullness `λ⁻¹ ≤ δ ^ (-η)` of
the hypothesis, and the prescribed loss of `Tube.exists_uniformTubeSet_subfamily_ssf`. -/
theorem exists_caseFamilyBanded [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (hηα : η ≤ α / 4) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (δ : ENNReal) ^ η
          ≤ (ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal) →
        ∃ s₁ ⊆ s, s₁.Nonempty ∧
          Nonempty (Tube.UniformTubeSet s₁ (fun i => (T i).toTube) (Tube.ssfGridLen δ)
            (Tube.uniformConst (Module.finrank ℝ E))) ∧
          (∃ lam : NNReal, 0 < lam ∧
            (δ : ENNReal) ^ α
                * (ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal)
              ≤ (lam : ENNReal) ∧
            ∀ i ∈ s₁,
            (lam : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
              volume (T i).shade ≤ 2 * (lam : ENNReal) * volume (T i).carrier) ∧
          (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-α) * (s₁.card : ENNReal) ∧
          frostmanConstIn s₁ (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall
            ≤ (δ : ENNReal) ^ (-α)
              * frostmanConstIn s (fun i => (T i).toConvexSpaceBody)
                  ConvexSpaceBody.closedUnitBall ∧
          (δ : ENNReal) ^ α
              * (ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal)
            ≤ (ShadedBody.fullness s₁ (fun i => (T i).toShadedBody) : ENNReal) ∧
          ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
            ≤ (δ : ENNReal) ^ (-α)
              * ShadedBody.multiplicity s₁ (fun i => (T i).toShadedBody) := by
  classical
  have hα4 : (0 : ℝ) < α / 4 := by positivity
  obtain ⟨δU, hδUpos, hδUle1, hU⟩ :=
    Tube.exists_uniformTubeSet_subfamily_ssf (E := E) 7 (α / 4) hα4
  obtain ⟨δ4, hδ4pos, hδ4le1, h4thr⟩ := exists_threshold_natCast_le_rpow 4 (α / 4) hα4
  filter_upwards [eventually_card_le_rpow_neg_seven (E := E) hdim,
      eventually_bandLoss_le_rpow_neg (η := α / 4) hα4,
      eventually_le_nhdsGT (c := δU) hδUpos,
      eventually_le_nhdsGT (c := δ4) hδ4pos,
      eventually_le_nhdsGT (c := (1 : NNReal)) one_pos,
      self_mem_nhdsWithin]
    with δ hcard7 hbandL hδU hδ4 hδ1 hδmem
  have hδ0 : (0 : NNReal) < δ := hδmem
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδe0 : (δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hδ0).ne'
  have hδetop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδE1 : ((δ : NNReal) : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have h4E : (4 : ENNReal) ≤ (δ : ENNReal) ^ (-(α / 4)) := by
    rw [ennreal_coe_nnreal_rpow hδR (-(α / 4)),
      show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by simp]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast h4thr hδ0 hδ4)
  have h2E : (2 : ENNReal) ≤ (δ : ENNReal) ^ (-(α / 4)) := le_trans (by norm_num) h4E
  intro ι s T hball hED hfull
  set F : ENNReal := (ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal) with hF_def
  have hFtop : F ≠ ⊤ := by rw [hF_def]; exact ENNReal.coe_ne_top
  have hFpos : 0 < F :=
    lt_of_lt_of_le (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ0) hδetop) hfull
  have hs : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with rfl | h
    · exact absurd hFpos (by simp [hF_def])
    · exact h
  obtain ⟨j₀, hj₀⟩ := hs
  set v : ENNReal := volume (T j₀).carrier with hv_def
  have hvpos : 0 < v := by
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hδp : 0 < (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ0) (Module.finrank ℝ E - 1)
    exact lt_of_lt_of_le (ENNReal.mul_pos hc.ne' hδp.ne')
      (by simpa [hv_def] using _root_.Tube.le_volume (T j₀).toTube)
  have hvtop : v ≠ ⊤ := (T j₀).isCompact.measure_ne_top
  have hcarr : ∀ i, volume (T i).carrier = v := fun i => by
    simpa [hv_def] using
      _root_.Tube.volume_carrier_eq_volume_carrier (T i).toTube (T j₀).toTube
  have hsumcar : ∀ X : Finset ι, ∑ i ∈ X, volume (T i).carrier = (X.card : ENNReal) * v :=
    fun X => by
      simpa [hv_def] using
        _root_.Tube.sum_volume_carrier_eq_card_mul (fun i => (T i).toTube) (T j₀).toTube X
  have hM : ∑ i ∈ s, volume (T i).shade = F * ((s.card : ENNReal) * v) := by
    rw [← hsumcar s, hF_def]
    exact ShadedBody.sum_volumeReal_shade_eq_fullness_mul s (fun i => (T i).toShadedBody)
  have hscard0 : ((s.card : ENNReal)) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨j₀, hj₀⟩
  -- **Step 1.**  Band the shade volumes at ratio `2`.
  have hmasspos : 0 < ∑ i ∈ s, volume (T i).shade := by
    rw [hM]
    exact ENNReal.mul_pos hFpos.ne' (ENNReal.mul_pos hscard0 hvpos.ne').ne'
  obtain ⟨s₂, hs₂sub, lam, hlampos, hs₂ne, hband₂, hmass₂, hFlam⟩ :=
    exists_massBand (σ := δ) hδ0 s T hmasspos
  have hlam1 : (lam : ENNReal) ≤ 1 := by
    obtain ⟨i, hi⟩ := hs₂ne
    have h := le_trans (hband₂ i hi).1 (measure_mono (T i).shade_subset)
    rw [hcarr i] at h
    exact (ENNReal.mul_le_mul_iff_left hvpos.ne' hvtop).mp (by simpa using h)
  -- **Step 2.**  Uniformize the tubes on the banded index set.
  have hcards : (s.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) :=
    hcard7 δ le_rfl s (fun i => (T i).toTube) (by simpa using hball) (by simpa using hED)
  have hcards₂ : (s₂.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) :=
    le_trans (by exact_mod_cast Finset.card_le_card hs₂sub) hcards
  obtain ⟨s₁, h₁₂, hcardret, hunif⟩ :=
    hU hδ0 hδU s₂ (fun i => (T i).toTube)
      (fun i hi => by simpa using hball i (hs₂sub hi)) hcards₂
  have hs₁s : s₁ ⊆ s := h₁₂.trans hs₂sub
  have hs₁ne : s₁.Nonempty := by
    rw [← Finset.card_pos]
    rcases Nat.eq_zero_or_pos s₁.card with hz | hpos
    · exfalso
      rw [hz] at hcardret
      norm_num at hcardret
      exact (Finset.not_nonempty_iff_eq_empty.mpr hcardret) hs₂ne
    · exact hpos
  have hL : bandLoss s.card ≤ (δ : ENNReal) ^ (-(α / 4)) := hbandL s.card hcards
  have hFinv : F⁻¹ ≤ (δ : ENNReal) ^ (-(α / 4)) := by
    have h1 : F⁻¹ ≤ (δ : ENNReal) ^ (-η) := by
      rw [ENNReal.rpow_neg]; exact ENNReal.inv_le_inv.mpr hfull
    exact h1.trans
      (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith))
  have hcardE : (s₂.card : ENNReal) ≤ (δ : ENNReal) ^ (-(α / 4)) * (s₁.card : ENNReal) := by
    rw [ennreal_coe_nnreal_rpow hδR (-(α / 4)), ← ENNReal.ofReal_natCast s₂.card,
      ← ENNReal.ofReal_natCast s₁.card, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδR.le _)]
    exact ENNReal.ofReal_le_ofReal hcardret
  -- The band, restricted to the uniformized index set.
  have hband₁ : ∀ i ∈ s₁, (lam : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ 2 * (lam : ENNReal) * volume (T i).carrier :=
    fun i hi => hband₂ i (h₁₂ hi)
  have hsum₁low : (lam : ENNReal) * ((s₁.card : ENNReal) * v) ≤ ∑ i ∈ s₁, volume (T i).shade := by
    calc (lam : ENNReal) * ((s₁.card : ENNReal) * v)
        = ∑ _i ∈ s₁, (lam : ENNReal) * v := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ s₁, volume (T i).shade :=
          Finset.sum_le_sum fun i hi => by simpa [hcarr i] using (hband₁ i hi).1
  have hsum₂up : ∑ i ∈ s₂, volume (T i).shade
      ≤ 2 * (lam : ENNReal) * ((s₂.card : ENNReal) * v) := by
    calc ∑ i ∈ s₂, volume (T i).shade
        ≤ ∑ _i ∈ s₂, 2 * (lam : ENNReal) * v :=
          Finset.sum_le_sum fun i hi => by simpa [hcarr i] using (hband₂ i hi).2
      _ = 2 * (lam : ENNReal) * ((s₂.card : ENNReal) * v) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- **The shade-mass chain**, used for the cardinality and multiplicity clauses.
  have hmasschain : ∑ i ∈ s, volume (T i).shade
      ≤ (δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4))
          * ((lam : ENNReal) * ((s₁.card : ENNReal) * v)) := by
    calc ∑ i ∈ s, volume (T i).shade
        ≤ bandLoss s.card * ∑ i ∈ s₂, volume (T i).shade := hmass₂
      _ ≤ bandLoss s.card * (2 * (lam : ENNReal) * ((s₂.card : ENNReal) * v)) :=
          mul_le_mul_right hsum₂up _
      _ ≤ bandLoss s.card * (2 * (lam : ENNReal)
            * (((δ : ENNReal) ^ (-(α / 4)) * (s₁.card : ENNReal)) * v)) :=
          mul_le_mul_right (mul_le_mul_right (mul_le_mul_left hcardE v) _) _
      _ = (bandLoss s.card * 2 * (δ : ENNReal) ^ (-(α / 4)))
            * ((lam : ENNReal) * ((s₁.card : ENNReal) * v)) := by ring
      _ ≤ ((δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4)))
            * ((lam : ENNReal) * ((s₁.card : ENNReal) * v)) :=
          mul_le_mul_left (mul_le_mul_left (mul_le_mul' hL h2E) _) _
  -- **The cardinality clause.**
  have hcount : (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-α) * (s₁.card : ENNReal) := by
    have hcancelv : F * (s.card : ENNReal)
        ≤ (δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4))
            * (lam : ENNReal) * (s₁.card : ENNReal) := by
      refine (ENNReal.mul_le_mul_iff_left hvpos.ne' hvtop).mp ?_
      calc F * (s.card : ENNReal) * v = ∑ i ∈ s, volume (T i).shade := by rw [hM]; ring
        _ ≤ (δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4))
              * ((lam : ENNReal) * ((s₁.card : ENNReal) * v)) := hmasschain
        _ = (δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4))
              * (δ : ENNReal) ^ (-(α / 4)) * (lam : ENNReal) * (s₁.card : ENNReal) * v := by ring
    calc (s.card : ENNReal) = F⁻¹ * (F * (s.card : ENNReal)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hFpos.ne' hFtop, one_mul]
      _ ≤ F⁻¹ * ((δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4))
            * (δ : ENNReal) ^ (-(α / 4)) * (lam : ENNReal) * (s₁.card : ENNReal)) :=
          mul_le_mul_right hcancelv _
      _ ≤ (δ : ENNReal) ^ (-(α / 4)) * ((δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4))
            * (δ : ENNReal) ^ (-(α / 4)) * 1 * (s₁.card : ENNReal)) :=
          mul_le_mul' hFinv (mul_le_mul_left (mul_le_mul_right hlam1 _) _)
      _ = (δ : ENNReal) ^ (-α) * (s₁.card : ENNReal) := by
          rw [mul_one]
          rw [show (δ : ENNReal) ^ (-(α / 4)) * ((δ : ENNReal) ^ (-(α / 4))
                * (δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4))
                * (s₁.card : ENNReal))
              = ((δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4))
                * ((δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4))))
                * (s₁.card : ENNReal) by ring]
          congr 1
          rw [← ENNReal.rpow_add _ _ hδe0 hδetop, ← ENNReal.rpow_add _ _ hδe0 hδetop]
          ring_nf
  -- **The band constant dominates the fullness**, the form the caller reads it in.
  have hlamlower : (δ : ENNReal) ^ α * F ≤ (lam : ENNReal) := by
    calc (δ : ENNReal) ^ α * F
        ≤ (δ : ENNReal) ^ (α / 4) * F :=
          mul_le_mul_left (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)) _
      _ ≤ (δ : ENNReal) ^ (α / 4) * (bandLoss s.card * (lam : ENNReal)) := by
          refine mul_le_mul_right ?_ _
          rw [hF_def]
          exact hFlam
      _ ≤ (δ : ENNReal) ^ (α / 4) * ((δ : ENNReal) ^ (-(α / 4)) * (lam : ENNReal)) :=
          mul_le_mul_right (mul_le_mul_left hL _) _
      _ = (lam : ENNReal) := by
          rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδe0 hδetop]
          simp
  refine ⟨s₁, hs₁s, hs₁ne, hunif, ⟨lam, hlampos, hlamlower, hband₁⟩, hcount, ?_, ?_, ?_⟩
  -- **The Frostman clause.**
  · have hκpos : ((δ : ENNReal) ^ α) ≠ 0 :=
      (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ0) hδetop).ne'
    have hκcard : (δ : ENNReal) ^ α * (s.card : ENNReal) ≤ (s₁.card : ENNReal) := by
      calc (δ : ENNReal) ^ α * (s.card : ENNReal)
          ≤ (δ : ENNReal) ^ α * ((δ : ENNReal) ^ (-α) * (s₁.card : ENNReal)) :=
            mul_le_mul_right hcount _
        _ = (s₁.card : ENNReal) := by
            rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδe0 hδetop]
            simp
    have hWK : ∀ i ∈ s, (T i).toConvexSpaceBody
        ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
      intro i hi
      change (T i).carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      rw [ConvexSpaceBody.closedUnitBall_carrier]
      exact hball i hi
    have hf := ConvexSpaceBody.frostmanConstIn_subfamily_le
      (s := s) (s' := s₁) (W := fun i => (T i).toConvexSpaceBody)
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
      (κ := (δ : ENNReal) ^ α) (v := v) ⟨j₀, hj₀⟩ (fun i _ => hcarr i) hWK hs₁s hκpos hκcard
    rwa [← ENNReal.rpow_neg] at hf
  -- **The fullness clause.**
  · have hDpos : ∑ i ∈ s₁, volume (T i).carrier ≠ 0 := by
      rw [hsumcar s₁]
      exact (ENNReal.mul_pos (by exact_mod_cast Finset.card_ne_zero.mpr hs₁ne) hvpos.ne').ne'
    have hDtop : ∑ i ∈ s₁, volume (T i).carrier ≠ ⊤ := by
      rw [hsumcar s₁]; exact ENNReal.mul_ne_top (by simp) hvtop
    have hlamfull : (lam : ENNReal) ≤ ShadedBody.fullness' s₁ (fun i => (T i).toShadedBody) := by
      simp only [ShadedBody.fullness']
      rw [ENNReal.le_div_iff_mul_le (Or.inl hDpos) (Or.inl hDtop), hsumcar s₁]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hsum₁low
    rw [ShadedBody.coe_fullness]
    exact le_trans hlamlower hlamfull
  -- **The multiplicity clause.**
  · have hnum : ∑ i ∈ s, volume (T i).shade
        ≤ (δ : ENNReal) ^ (-α) * ∑ i ∈ s₁, volume (T i).shade := by
      calc ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4))
              * (δ : ENNReal) ^ (-(α / 4)) * ((lam : ENNReal) * ((s₁.card : ENNReal) * v)) :=
            hmasschain
        _ ≤ (δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4))
              * (δ : ENNReal) ^ (-(α / 4)) * (∑ i ∈ s₁, volume (T i).shade) :=
            mul_le_mul_right hsum₁low _
        _ ≤ (δ : ENNReal) ^ (-α) * (∑ i ∈ s₁, volume (T i).shade) := by
            refine mul_le_mul_left ?_ _
            calc (δ : ENNReal) ^ (-(α / 4)) * (δ : ENNReal) ^ (-(α / 4))
                  * (δ : ENNReal) ^ (-(α / 4))
                = (δ : ENNReal) ^ (-(3 * α / 4)) := by
                  rw [← ENNReal.rpow_add _ _ hδe0 hδetop, ← ENNReal.rpow_add _ _ hδe0 hδetop]
                  ring_nf
              _ ≤ (δ : ENNReal) ^ (-α) :=
                  ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
    have hden : volume (⋃ i ∈ s₁, (T i).shade) ≤ volume (⋃ i ∈ s, (T i).shade) :=
      measure_mono (Set.biUnion_subset_biUnion_left (Finset.coe_subset.mpr hs₁s))
    calc ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
        = (∑ i ∈ s, volume (T i).shade) / volume (⋃ i ∈ s, (T i).shade) := rfl
      _ ≤ ((δ : ENNReal) ^ (-α) * ∑ i ∈ s₁, volume (T i).shade)
            / volume (⋃ i ∈ s₁, (T i).shade) := ENNReal.div_le_div hnum hden
      _ = (δ : ENNReal) ^ (-α)
            * ShadedBody.multiplicity s₁ (fun i => (T i).toShadedBody) := by
          rw [ShadedBody.multiplicity, mul_div_assoc]

end ml1Boot

end Kakeya

#print axioms Kakeya.ml1Boot.exists_caseFamilyBanded
#print axioms Kakeya.ml1Boot.isCRefinement_of_card_le_of_band
