/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimates
public import Kakeya.ShadedUniform
public import Kakeya.Factorization
public import Kakeya.DimensionThree.MainLemma2.AScaleConstants
public import Kakeya.DimensionThree.MainLemma2.UniformWindow
public import Kakeya.Factoring.RhoTubesSection9
public import Kakeya.Tube.CoverCountComparable

/-!
The setup of the very-not-sticky case of Main Lemma 2.
-/

@[expose] public section

namespace Kakeya

universe u

namespace VeryNotSticky

open MeasureTheory Metric Set ShadedBody

/-! ### The `ρ`-count clause, hoisted out of the structure

The `Prop`s below are stated *before* `Kakeya.VeryNotSticky` because the field
`Kakeya.VeryNotSticky.rho_count` is `RhoParentData`, of which
`RhoCountParent` is the derived form. `RhoCountOn` and `RhoCountParent` were first written in
`Kakeya.DimensionThree.MainLemma2.BallCountRepair`, which is downstream of this file, so using
them here would be an import cycle; everything else in that file stays there. They mention only
`Tube`, `ShadedTube`, `Kakeya.maxDensity` and `IsEssentiallyDistinct`, all
already in this file's import closure.
-/

/-- **The `ρ`-count clause on a named index set, with a named constant.**

`RhoCountOn δ ζ exscalb s T Ccount` is `|𝕋_ρ| ≥ Ccount⁻¹ ρ^{-2-ζ}` for every essentially
distinct family of `ρ`-tubes covering `s`, over the window `ρ ∈ [δ^{1-exscalb}, δ^{exscalb}]`.
At `Ccount := 1` it is `Kakeya.VeryNotSticky.RhoCountFieldOldStatement`, the form the field
`rho_count` used to carry; `Kakeya.VeryNotSticky.rhoCountFieldOldStatement_iff_rhoCountOn_one`
records that identification and
`Kakeya.VeryNotSticky.not_rhoCountFieldOldStatement_empty` records why it had to go. -/
def RhoCountOn (δ : NNReal) (ζ exscalb : ℝ) {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Ccount : NNReal) : Prop :=
  ∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscalb)) (δ ^ exscalb) →
    ∀ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      (∀ i ∈ s, ∃ j ∈ tρ, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) →
      (tρ : Set κ).Pairwise
        (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) →
      (ρ : ℝ) ^ (-2 - ζ) ≤ (Ccount : ℝ) * (tρ.card : ℝ)

/-- **The `ρ`-count clause on a parent family** — the field `Kakeya.VeryNotSticky.rho_count`
in its derived parent-count form (`Kakeya.VeryNotSticky.rhoCountParent_of_rhoParentData`, at any constant
`≥ Tube.coverCountLoss 3`): the field itself is `Kakeya.VeryNotSticky.RhoParentData`.

The configuration's family sits inside a *parent* family `sPar` which satisfies Lemma 9.1's own
hypotheses — containment in `B_1` and `Δ_max ≤ δ^{-η}` — and whose covering families obey the
count, up to the constant `Ccount`.

This is what GWZ actually have: in subsection *proofoverview* the setup pigeonholes refine the
*shading*, not the tube family, so `𝕋` at the point where the count is used is still the `𝕋` of
the lemma's hypothesis ("abusing notation, we will continue to refer to this as `(𝕋, Y)`"). The
Lean configuration cannot keep that family in `cfg.s` — the per-tube shading band
`shading_lb`/`shading_ub`/`lam_ge` cannot be met without dropping tubes, since the aggregate
binder `hfull` bounds no summand — so it has to *name* it.

Taking `sPar := s`, the family the binder speaks about, discharges the clause with `Ccount = 1`
and no argument at all: `Kakeya.VeryNotSticky.rhoCountParent_of_binders`. The padding cheat is
closed by construction, because `sPar` must itself obey the containment and the `Δ_max` bound,
so it cannot be inflated with irrelevant tubes (`δ^{-4}` tubes in `B_1` force
`Δ_max ≥ δ^{-2}`). -/
def RhoCountParent (δ : NNReal) (ζ exscalb η : ℝ) {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Ccount : NNReal) : Prop :=
  ∃ sPar : Finset ι, s ⊆ sPar ∧
    (∀ i ∈ sPar, (T i).carrier ⊆ Metric.closedBall 0 1) ∧
    maxDensity sPar (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) ∧
    RhoCountOn δ ζ exscalb sPar T Ccount

/-- **The `ρ`-count on the family's own parent, with the parent's uniform hierarchy and the
retention** (GWZ Lemma 9.1, l.1775–1781, read on a `⪆1`-refinement as GWZ do at l.1790 and
l.1994–1998). The configuration's family `s` sits inside a parent `sPar` satisfying Lemma 9.1's
hypotheses — containment in `B₁`, `Δ_max ≤ δ^{-η}`, GWZ Definition 2.1 on the standard grid at a
constant `1 ≤ Cpar ≤ δ^{-η}`, and the count clause in its 
`∃`-form — and `s` retains a `δ^{2η}` fraction of `sPar`. The three together are what lets the
count be spent on `s`'s own hierarchy ( (α),(β),(γ)); the previous field
`RhoCountParent` carried the count alone, in a `∀`-over-essentially-distinct-covers form, and was
unusable for that purpose. -/
def RhoParentData (δ : NNReal) (ζ exscalb η : ℝ) {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ sPar : Finset ι, s ⊆ sPar ∧
    (∀ i ∈ sPar, (T i).carrier ⊆ Metric.closedBall 0 1) ∧
    maxDensity sPar (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) ∧
    (δ : ENNReal) ^ (2 * η) * (sPar.card : ENNReal) ≤ (s.card : ENNReal) ∧
    (∃ Cpar : NNReal, 1 ≤ Cpar ∧ (Cpar : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
      Nonempty (Tube.UniformTubeSet sPar (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cpar)) ∧
    (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscalb)) (δ ^ exscalb) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ).Pairwise
          (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ sPar, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ))

/-- **The `∀`-over-covers count from the `∃`-form**, at any constant `≥ Tube.coverCountLoss 3`:
against an arbitrary essentially distinct cover of `s` by `ρ`-tubes, the essentially distinct
all-used family the `∃`-clause supplies has at most `Tube.coverCountLoss 3` times as many members
(`Tube.count_of_canonicalCover_shadedTube`). The essential distinctness of the competitor cover is
not used. -/
theorem rhoCountOn_of_count {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ζ exscal : ℝ}
    (hexscal0 : 0 ≤ exscal) {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {Ccount : NNReal}
    (hL : Tube.coverCountLoss 3 ≤ Ccount)
    (hcount : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ).Pairwise
          (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) :
    RhoCountOn δ ζ exscal s T Ccount := by
  intro ρ hρ κ' tρ' Tρ' hcov _
  obtain ⟨κ, tρ, Tρ, hED, hused, hcard⟩ := hcount ρ hρ
  have hρ0 : 0 < ρ := lt_of_lt_of_le (NNReal.rpow_pos hδ) hρ.1
  have hρ1 : ρ ≤ 1 := hρ.2.trans (NNReal.rpow_le_one hδ1 hexscal0)
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  set L : NNReal := Tube.coverCountLoss 3 with hL_def
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
    rw [hL_def]; exact Tube.one_le_coverCountLossAt_real 3 1
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le one_pos hL1
  set c : ℝ := (ρ : ℝ) ^ (-2 - ζ) / (L : ℝ) with hc_def
  have hlow : (L : ℝ) * c ≤ (tρ.card : ℝ) := by
    rw [hc_def, mul_div_cancel₀ _ hLpos.ne']; exact hcard
  have h := Tube.count_of_canonicalCover_shadedTube (E := EuclideanSpace ℝ (Fin 3)) hρ0 hρ1
    T s tρ Tρ hED hused (by rw [hfr]; exact hlow) tρ' Tρ' hcov
  have hLC : (L : ℝ) ≤ (Ccount : ℝ) := by exact_mod_cast hL
  calc (ρ : ℝ) ^ (-2 - ζ) = (L : ℝ) * c := by
        rw [hc_def, mul_div_cancel₀ _ hLpos.ne']
    _ ≤ (L : ℝ) * (tρ'.card : ℝ) := by gcongr
    _ ≤ (Ccount : ℝ) * (tρ'.card : ℝ) := by gcongr

/-- **No consumer is lost**: the datum yields the previous field form `RhoCountParent` at any
constant `≥ Tube.coverCountLoss 3`. -/
theorem rhoCountParent_of_rhoParentData {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ζ exscalb η : ℝ} (hex : 0 ≤ exscalb) {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {Ccount : NNReal}
    (hL : Tube.coverCountLoss 3 ≤ Ccount)
    (h : RhoParentData δ ζ exscalb η s T) : RhoCountParent δ ζ exscalb η s T Ccount := by
  obtain ⟨sPar, hsub, hball, hmax, -, -, hcount⟩ := h
  exact ⟨sPar, hsub, hball, hmax, rhoCountOn_of_count hδ hδ1 hex hL hcount⟩

/-- The tube-level hierarchy of a shaded family transports to any family with the same tubes
(the shades play no role in `Tube.UniformTubeSet`). -/
theorem tubeUniform_of_shaded {δ : NNReal} {ι : Type u} {s : Finset ι}
    {T T' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {N : ℕ} {C : NNReal}
    (htube : ∀ i, (T' i).toTube = (T i).toTube)
    (h : Nonempty (ShadedTube.ShadedUniformTubeSet s T N C)) :
    Nonempty (Tube.UniformTubeSet s (fun i ↦ (T' i).toTube) N C) := by
  obtain ⟨𝒱⟩ := h
  have hfun : (fun i ↦ (T' i).toTube) = fun i ↦ (T i).toTube := funext htube
  rw [hfun]
  exact ⟨𝒱.tubeUniform⟩

/-- **Producibility at the cut.** From Lemma 9.1's binders on the input `(s, T)` — the bounded
uniformity, containment, `Δ_max`, the `∃`-form count — and a cut
`s' ⊆ s` with tubes unchanged and the cardinality retention `δ^{2η}|s| ≤ |s'|`
(`Kakeya.VeryNotSticky.card_retention_of_mass`), the datum holds on the cut family with
`sPar := s`. -/
theorem rhoParentData_of_binders {δ : NNReal} {ζ exscal η : ℝ} {ι : Type u} {s s' : Finset ι}
    {T T' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hsub : s' ⊆ s)
    (htube : ∀ i, (T' i).toTube = (T i).toTube)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hmax : maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η))
    (huni : ∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C))
    (hcount : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ).Pairwise
          (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ))
    (hret : (δ : ENNReal) ^ (2 * η) * (s.card : ENNReal) ≤ (s'.card : ENNReal)) :
    RhoParentData δ ζ exscal η s' T' := by
  have hbody : ∀ i, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody :=
    fun i => congrArg Tube.toConvexSpaceBody (htube i)
  have hcar : ∀ i, (T' i).carrier = (T i).carrier :=
    fun i => congrArg ConvexSpaceBody.carrier (hbody i)
  obtain ⟨C, hC1, hCδ, huni'⟩ := huni
  refine ⟨s, hsub, fun i hi => (hcar i) ▸ hball i hi, ?_, hret,
    ⟨C, hC1, hCδ, tubeUniform_of_shaded htube huni'⟩, ?_⟩
  · rw [Kakeya.maxDensity_congr (fun i _ => hbody i)]; exact hmax
  · intro ρ hρ
    obtain ⟨κ, tρ, Tρ, hED, hused, hcard⟩ := hcount ρ hρ
    refine ⟨κ, tρ, Tρ, hED, fun j hj => ?_, hcard⟩
    obtain ⟨i, hi, hle⟩ := hused j hj
    exact ⟨i, hi, by rw [hbody i]; exact hle⟩

/-- **Cardinality retention from mass retention and fullness** (the retention clause of
`Kakeya.VeryNotSticky.RhoParentData` at the producers). If a subfamily `s' ⊆ s` with the same
tubes keeps a `c ≥ δ^η` fraction of the shade mass of `s`, and `s` has aggregate fullness
`≥ δ^η`, then `δ^{2η}|s| ≤ |s'|`: the shade mass of `s` is `≥ δ^η |s| v` with `v` the common
carrier volume of a `δ`-tube (`ShadedBody.coe_fullness_mul_le_sum_volume_shade`,
`Tube.volume_carrier_eq_volume_carrier`), and that of `s'` is `≤ |s'| v`. No volume constant is
lost, because the carriers all have exactly the volume `v`; compare
`Kakeya.VeryNotSticky.card_parent_le_of_isCRefinement`. -/
theorem card_retention_of_mass {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {η : ℝ}
    {ι : Type u} {s s' : Finset ι} {T T' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hsub : s' ⊆ s) (htube : ∀ i, (T' i).toTube = (T i).toTube)
    (hfull : δ ^ η ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody))
    {c : ENNReal} (hc : (δ : ENNReal) ^ η ≤ c)
    (hmass : c * ∑ i ∈ s, volume (T i).shade ≤ ∑ i ∈ s', volume (T' i).shade) :
    (δ : ENNReal) ^ (2 * η) * (s.card : ENNReal) ≤ (s'.card : ENNReal) := by
  classical
  rcases s.eq_empty_or_nonempty with hs | ⟨i₀, hi₀⟩
  · simp [hs]
  have hbody : ∀ i, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody :=
    fun i => congrArg Tube.toConvexSpaceBody (htube i)
  -- the common carrier volume of the `δ`-tubes
  set v : ENNReal := volume (T i₀).carrier with hv_def
  have hvol : ∀ i ∈ s, volume (T i).carrier = v := fun i _ =>
    Tube.volume_carrier_eq_volume_carrier (T i).toTube (T i₀).toTube
  have hv0 : v ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le ?_ (Tube.le_volume (T i₀).toTube))
    have hc' : ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal) :
        ENNReal) ≠ 0 := by
      simpa using (Tube.le_volume.c_pos (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))).ne'
    have hd : ((δ : ENNReal) ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1)) ≠ 0 :=
      pow_ne_zero _ (by simpa using hδ.ne')
    exact pos_iff_ne_zero.mpr (mul_ne_zero hc' hd)
  have hvtop : v ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (Tube.volume_le hδ1 (T i₀).toTube) ?_)
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
  -- the shade mass of `s` is at least `δ^η · |s| · v`
  have hlow : ((δ ^ η : NNReal) : ENNReal) * ((s.card : ENNReal) * v) ≤
      ∑ i ∈ s, volume (T i).shade :=
    ShadedBody.coe_fullness_mul_le_sum_volume_shade s (fun i ↦ (T i).toShadedBody) hfull
      (fun i hi ↦ (hvol i hi).ge)
  -- the shade mass of `s'` is at most `|s'| · v`
  have hupp : ∑ i ∈ s', volume (T' i).shade ≤ (s'.card : ENNReal) * v := by
    refine (Finset.sum_le_card_nsmul s' _ v ?_).trans_eq ?_
    · intro i hi
      have hc' : (T' i).carrier = (T i).carrier := congrArg ConvexSpaceBody.carrier (hbody i)
      calc volume (T' i).shade ≤ volume (T' i).carrier := measure_mono (T' i).shade_subset
        _ = volume (T i).carrier := by rw [hc']
        _ = v := hvol i (hsub hi)
    · simp [nsmul_eq_mul]
  have hδE0 : (δ : ENNReal) ≠ 0 := by exact_mod_cast hδ.ne'
  have hcoe : ((δ ^ η : NNReal) : ENNReal) = (δ : ENNReal) ^ η :=
    ENNReal.coe_rpow_of_ne_zero hδ.ne' η
  rw [hcoe] at hlow
  have hchain : ((δ : ENNReal) ^ (2 * η) * (s.card : ENNReal)) * v ≤ (s'.card : ENNReal) * v := by
    calc ((δ : ENNReal) ^ (2 * η) * (s.card : ENNReal)) * v
        = (δ : ENNReal) ^ η * ((δ : ENNReal) ^ η * ((s.card : ENNReal) * v)) := by
          rw [show (2 : ℝ) * η = η + η by ring, ENNReal.rpow_add _ _ hδE0 ENNReal.coe_ne_top]
          ring
      _ ≤ c * ((δ : ENNReal) ^ η * ((s.card : ENNReal) * v)) := by gcongr
      _ ≤ c * ∑ i ∈ s, volume (T i).shade := by gcongr
      _ ≤ ∑ i ∈ s', volume (T' i).shade := hmass
      _ ≤ (s'.card : ENNReal) * v := hupp
  exact (ENNReal.mul_le_mul_iff_left hv0 hvtop).mp hchain

end VeryNotSticky

/-- **The coarse Katz--Tao window datum of a configuration.**

The retirement of the refuted `Kakeya.VeryNotSticky.coarseKatzTaoBound` needs its proved
replacement `Kakeya.VeryNotSticky.coarseKatzTaoBound_general_at` to be instantiated at a
threshold pair, and that pair must be *fixed before `η` and `δ`* or the density-versus-accuracy
circularity returns.  This bundle is that pair together with everything the instantiation asks
of it.  It carries **data**, not just propositions: `wη` and `wρ` are the two thresholds, and
they are ordinary numbers on the configuration rather than values of a choice function, which is
what lets a single pair serve a whole window of exponents.

* `wb` is the bottom of the exponent window the pair was chosen for, and `hwb` places `β` above
  it.  Nothing here mentions any exponent above `wb`, which is what makes the clauses
  `β`-free and hence transportable by `Kakeya.VNSUniform.CaseParams.mono_beta`.
* `we` is the loss exponent at which the windowed bound is read.  The bound
  `hwe : we ≤ ϱ² wb / 1440` is **forced**: `we` has to sit below `ν/180` at both gains of the
  case split — the thick gain `ϱβτ/8` and the transverse gain `τ'β/2` — *and* be fixed before
  `η`.  If `we` were allowed to shrink with `η` then `wη` would shrink with it and `hηKT` would
  become self-referential; that circularity is one of the routes this development has already
  refuted.  With `Kakeya.VNSUniform.CaseParams.rhoLeTau` (`ϱ ≤ τ`) and `hwb`, the displayed
  bound gives `we ≤ ν/180` at both gains.
* `hwin` is the windowed Katz--Tao bound at `(β, we)` at those thresholds, `hηKT` the fullness
  threshold, and `hδrad` the radius threshold in the shape
  `Kakeya.VeryNotSticky.coarseRadius_of_grid` consumes.

Every field is *supplied* by the producer of a configuration, not proved by it: see
`Kakeya.exists_uniformWindowPair`, which produces a pair valid on a whole window from no
hypotheses at all. -/
structure CoarseKTWindow (β ϱ η exscal : ℝ) where
  /-- The bottom of the exponent window the threshold pair was chosen for. -/
  wb : ℝ
  /-- The window bottom is positive. -/
  hwb0 : 0 < wb
  /-- The configuration's exponent lies above the window bottom. -/
  hwb : wb ≤ β
  /-- The loss exponent at which the windowed Katz--Tao bound is read. -/
  we : ℝ
  /-- The loss exponent is positive. -/
  hwe0 : 0 < we
  /-- The loss exponent is below `ν/180` at both gains; see the structure docstring. -/
  hwe : we ≤ ϱ ^ 2 * wb / 1440
  /-- The fullness exponent of the threshold pair. -/
  wη : ℝ
  /-- The fullness exponent is positive. -/
  hwη : 0 < wη
  /-- The radius threshold of the threshold pair. -/
  wρ : NNReal
  /-- The radius threshold is positive. -/
  hwρ0 : 0 < wρ
  /-- The radius threshold is at most `1/2`, which is what the off-family default tube needs. -/
  hwρhalf : wρ ≤ 1 / 2
  /-- The windowed Katz--Tao multiplicity bound at window radius `4`, at those thresholds. -/
  hwin : Kakeya.WindowFour.{u} (EuclideanSpace ℝ (Fin 3)) β we wη wρ
  /-- `η` is small enough for the fullness threshold. -/
  hηKT : 3 * η ≤ exscal * wη
  /-- `η` is small enough for the *budget* clause of
  `Kakeya.VeryNotSticky.coarseKatzTaoBound_general_at`.

  Stated against `ϱ² wb / 1440` — the same `β`- and `η`-free quantity that bounds `we` — rather
  than against the gain, so that it lives here rather than on
  `Kakeya.VeryNotSticky.CaseParams`.  With `Kakeya.VNSUniform.CaseParams.rhoLeTau` and `hwb` it
  yields `3 η (1-β) ≤ exscal · (ν/90 - we)` at both gains, which is exactly the `hbudget` that
  theorem asks for.  Stated against `we` rather than against `ϱ² wb / 1440` so that the
  conversion runs in the usable direction: `hwe` bounds `we` from *above*. -/
  hηbud : 3 * η ≤ exscal * we

/-- **The window datum at a scale.**  `Kakeya.CoarseKTWindow` is `δ`-free — every one of its
fields is fixed before `δ` — and this is that datum together with the one clause that is a
condition on `δ`.  The split is what lets a producer take the window as a *single input* and
arrange the scale clause itself inside the `∀ᶠ δ` it already carries
(`Kakeya.CoarseKTWindow.eventually_radius`). -/
structure CoarseKTData (β ϱ η exscal : ℝ) (δ : NNReal)
    extends CoarseKTWindow.{u} β ϱ η exscal where
  /-- `δ` is small enough for the radius threshold. -/
  hδrad : 6 * δ ^ (exscal - η) ≤ toCoarseKTWindow.wρ

/-- **The scale clause is a plain smallness condition on `δ`.**  Since `wρ > 0` and
`exscal - η > 0`, the bound `6 δ^{exscal-η} ≤ wρ` holds for all sufficiently small `δ`.  So a
producer that already quantifies `∀ᶠ δ in 𝓝[>] 0` can take the `δ`-free
`Kakeya.CoarseKTWindow` as an input and arrange `Kakeya.CoarseKTData` itself, which is why the
new configuration field is *supplied* rather than owed. -/
theorem CoarseKTWindow.eventually_radius {β ϱ η exscal : ℝ}
    (w : CoarseKTWindow.{u} β ϱ η exscal) (he : 0 < exscal - η) :
    ∀ᶠ d : NNReal in nhdsWithin 0 (Set.Ioi 0), 6 * d ^ (exscal - η) ≤ w.wρ := by
  set e : ℝ := exscal - η with he_def
  set d₀ : NNReal := (w.wρ / 6) ^ (1 / e) with hd₀_def
  have hρ6 : (0 : NNReal) < w.wρ / 6 := by
    have := w.hwρ0
    positivity
  have hd₀ : (0 : NNReal) < d₀ := by rw [hd₀_def]; exact NNReal.rpow_pos hρ6
  filter_upwards [Ioo_mem_nhdsGT hd₀] with d hd
  have hstep : d ^ e ≤ d₀ ^ e := NNReal.rpow_le_rpow (le_of_lt hd.2) he.le
  have hd₀e : d₀ ^ e = w.wρ / 6 := by
    rw [hd₀_def, ← NNReal.rpow_mul, one_div, inv_mul_cancel₀ he.ne', NNReal.rpow_one]
  rw [hd₀e] at hstep
  calc 6 * d ^ e ≤ 6 * (w.wρ / 6) := by gcongr
    _ = w.wρ := by rw [mul_div_cancel₀]; norm_num

/-- The window datum becomes a scale datum at any scale meeting the radius clause. -/
def CoarseKTWindow.toData {β ϱ η exscal : ℝ} (w : CoarseKTWindow.{u} β ϱ η exscal)
    {δ : NNReal} (h : 6 * δ ^ (exscal - η) ≤ w.wρ) : CoarseKTData.{u} β ϱ η exscal δ :=
  { toCoarseKTWindow := w, hδrad := h }

open MeasureTheory Topology Filter ShadedBody in
/-- The shared configuration for the very-not-sticky case of Main Lemma 2, i.e. the
"configuration of Subsection `subsecproofoverview`" that Lemmas `lem:ml2thick`,
`lem:ml2slab`, `lem:ml2transverse`, `lem:ml2tangential` all adopt.

The blueprint introduces this configuration through a long sequence of proof-internal
pigeonholing refinements rather than as a standalone interface, so we bundle it: the
base uniform family `(T, Y)` of `δ`-tubes in `B_1` (with the same hypotheses as
`multiplicity_le_of_card_isEssDistinct_ge` — the `Δ_max`, fullness, and `ρ`-tube counting bounds),
the ambient Katz–Tao and Frostman estimates `K_KT(β)`, `K_F(β)`, the bias `ϱ` of the per-ball
biased maximal density factoring (blueprint `def:biasedFactoring`), and the working dimensions
`a`, `b` with `δ ≤ a ≤ b ≤ r_1 = δ^{exscal}` (`hdims`). GWZ §9.3 factors **per ball**: Lemma 9.2
is applied to `𝕋_B`, and by pigeonholing the bodies `W ∈ 𝕎_B` have dimensions `a × b × r_1`
for every ball `B` (`gwz.txt` l.2036-2041). There is no global factoring of `𝕋`; the per-ball
one is data of `Kakeya.VeryNotSticky.BallData` (C4). The case lemmas below branch on `a`, `b`
(and a typical angle `θ`).

Two names occur for the coarse scale: `exscalb` is the exponent `ϖ` governing the
`rho_count` window, while `exscal` fixes the ball radius `r₁ = δ^{exscal}`. Definition
`hyp:ml2params` identifies them. We retain both fields to keep their two roles visible, and
record their equality in `hscale`; this is what makes the non-slab angular scale admissible
for `rho_count`. -/
structure VeryNotSticky where
  /-- The exponent `β` of the Katz–Tao/Frostman estimates. -/
  β : ℝ
  /-- Positivity of `β`. -/
  hβ : 0 < β
  /-- `β ≤ 1`, the other half of the normalisation `0 < β ≤ 1` that Configuration
  `hyp:ml2setup` fixes.

  It is not implied by `hβ`, and it is used throughout the section: by the thick branch
  through `Kakeya.VeryNotSticky.goalMult_of_a_ge`, by the non-slab leaves through
  `Kakeya.VeryNotSticky.nonslabKKTPow`, and by the scale-`r` layer through
  `Kakeya.VeryNotSticky.aScaleVolume`. Those statements continue to take it as an explicit
  hypothesis `hβ1`, which their callers discharge with this field; only
  `Kakeya.VeryNotSticky.exists_aScaleData`, whose signature has no room for such a binder,
  reads it directly. -/
  hβ1 : β ≤ 1
  /-- The tube-counting exponent `ζ > 0`. -/
  ζ : ℝ
  /-- Positivity of `ζ`. -/
  hζ : 0 < ζ
  /-- The tube thickness `δ` (taken sufficiently small). -/
  δ : NNReal
  /-- Positivity of `δ`. Definition `hyp:ml2params` closes by choosing `0 < δ ≤ 1` after all
  exponent parameters and below the fixed-scale thresholds used by the leaves. Positivity is not
  derivable from any other field — nothing else forbids `δ = 0` — and it is consumed by
  `Kakeya.VeryNotSticky.exists_thinConfig`, `Kakeya.VeryNotSticky.nonslabKKT` and, through
  `Kakeya.VeryNotSticky.plankPresentation`, by
  `Kakeya.findingTypicalAngleOfIntersection_perScale`. -/
  hδ : 0 < δ
  /-- `δ ≤ 1`, from the final scale choice of Definition `hyp:ml2params`. As the blueprint
  stresses, "`δ ≤ 1` is used every
  time we combine two cases: it is exactly what makes `ν ↦ δ^ν` antitone", so it is consumed
  by every assembly lemma of the case split (`Kakeya.VeryNotSticky.exists_goalMult`,
  `Kakeya.goalMult_of_a_le`, `Kakeya.VeryNotSticky.goalMult_of_b_le`,
  `Kakeya.VeryNotSticky.goalMult_of_multBodies_ge`). -/
  hδ1 : δ ≤ 1
  /-- The `ρ`-scale exponent `\exscalb` fixing the `rho_count` window
  `[δ^{1-exscalb}, δ^{exscalb}]` (the constant `ϖ` of `lemmain2vns`). -/
  exscalb : ℝ
  /-- Positivity of `exscalb`. -/
  hexscalb : 0 < exscalb
  /-- The coarse-scale exponent `\exscal` fixing the ball radius `r_1 = δ^{exscal}`
  (used in `hdims` and the `δ^{2·exscal}` case splits). -/
  exscal : ℝ
  /-- Positivity of `exscal`. -/
  hexscal : 0 < exscal
  /-- The ball-scale exponent is the exponent in the tube-counting window, as required by
  Definition `hyp:ml2params` (P1). -/
  hscale : exscal = exscalb
  /-- The density/multiplicity exponent `η`. -/
  η : ℝ
  /-- Positivity of `η`. -/
  hη : 0 < η
  /-- The index type of the tube family. -/
  ι : Type u
  /-- Decidable equality on the index type (used by the per-ball constructions downstream). -/
  [decidableEq : DecidableEq ι]
  /-- The finite index set of the tube family. -/
  s : Finset ι
  /-- The uniform family of shaded `δ`-tubes `(T, Y)`. -/
  T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))
  /-- All tubes lie in the unit ball `B_1`. -/
  contained : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1
  /-- The branching constant `C₀` of blueprint `uniformSetOfTubes`(iii), at which the family
  `(T, Y)` is uniform on the standard multiscale grid.

  It is a field rather than an existential inside `uniform` because the accumulated comparison
  constant of the scale-`r` layer is a function of it, so it has to be nameable in order for
  the clause `aScaleData_absorb` below to be stated at all. It is fixed before `δ`: the
  producer of the bundle in the field `uniform` is the *shaded* uniformization lemma
  `Kakeya.ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, which quantifies its constant
  `Cu` before the scale. (The tube-level
  `Tube.exists_uniformTubeSet_subfamily_ssf` does the same, but it is not the
  applicable lemma here: `uniform` asks for a
  `Kakeya.ShadedTube.ShadedUniformTubeSet`, which carries the per-point shading data that the
  tube-level bundle does not have.)

  That quantifier order is what makes `aScaleData_absorb` below arrangeable, since the
  threshold it imposes on `δ` is a function of `C₀` and `D₀`. It is also why
  `Kakeya.VeryNotSticky.coe_C₀_le_rpow_neg_eta` holds: the absorption forces `C₀ ≤ δ^{-η}`, so
  every loss proportional to `C₀` in the scale-`r` layer is sub-polynomial. -/
  C₀ : NNReal
  /-- `1 ≤ C₀`. -/
  hC₀ : 1 ≤ C₀
  /-- The bounded-overlap constant `D₀` of blueprint `uniformSetOfTubes`(ii).

  In the Lean bundle `Tube.UniformTubeSet` the assignment is a function, so its
  classes partition `𝕋` and the overlap is `1`; `D₀` is carried as a free parameter bounded
  below by `1` so that the constants of blueprint `def:ml2DeltamaxScaleAConstant` and
  `def:ml2aScaleVolumeConstant` read as the blueprint writes them. -/
  D₀ : NNReal
  /-- `1 ≤ D₀`. -/
  hD₀ : 1 ≤ D₀
  /-- `(T, Y)` is a uniform family on the standard multiscale grid, with branching constant
  `C₀`. -/
  uniform : Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C₀)
  /-- `Δ_max(T) ≤ δ^{-η}`. -/
  maxDensity_le : maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η)
  /-- **`λ(T, Y) ≥ δ^{2η}`**, the aggregate fullness of the configuration's family.

  **Why `2η` and not `η` — the exponent was rigid, and the rigidity is a defect.** GWZ write
  `λ(𝕋_a, Y_{𝕋_a}) ⪆ λ(𝕋, Y) ≥ δ^η` for the refined family; this development rendered the `⪆`
  as `≥` with constant `1`, i.e. asserted this clause at *exactly* the `δ^η` of the binder
  `hfull` of `Kakeya.VeryNotSticky.exists_setup_caseSideData`. At that exponent the clause is
  **rigid**: `ShadedBody.IsRefinement` keeps carriers equal and only shrinks shadings, so a
  producer handed a family whose aggregate fullness is exactly `δ^η` — a *flat* family, every
  tube of shading density exactly `δ^η`, which meets the binder with equality — may not delete
  **one atom of positive shading mass** from any tube it keeps. The mechanism is
  `Kakeya.VeryNotSticky.volume_shade_eq_of_fullness_ge`
  (`Kakeya.DimensionThree.MainLemma2.BallJoint`), stated about a bare family so that it survives
  this field, and the refutation it powers is
  `Kakeya.VeryNotSticky.not_rigidFullnessField_of_flat_island`
  (`Kakeya.DimensionThree.MainLemma2.SetupIslandRefute`) — a refutation of the **old** form of
  this field, which is hoisted there as `Kakeya.VeryNotSticky.RigidFullnessField` precisely so
  that this repair could not silently retire it.

  It is a defect and not merely a strong hypothesis because the joint construction must delete
  mass: every other clause of the configuration and of
  `Kakeya.VeryNotSticky.CaseSideData` is met by *discarding* the parts of the shading that
  obstruct it, and the budget for discarding is the target's own conjunct `δ^η ≤ c`, which
  permits losing up to a `1 - δ^η` fraction. Quantitatively the obstruction is cheap: a family
  of `|𝕋|` tubes each carrying an isolated island of shading of measure `δ^{2η}|B_δ|` has all
  its islands together of measure at most `δ^{2η+3}|𝕋|` against a total shading mass
  `≍ δ^{η+2}|𝕋|`, a `δ^{η+1}` fraction — cheaper *by a factor `δ`* than the refinement budget
  allows. Nothing but this clause forbade deleting them.

  **Why `2η` is the right repair, and why it is the same repair as `lam_ge`'s.** At `δ^{2η}`
  this clause is not an extra demand at all — **it is a consequence of clauses the structure
  already carries**, and that is compiler-checked, not asserted: `shading_lb` and `lam_ge`
  compose to `δ^{2η} · |T| ≤ |Y(T)|` for every `T ∈ 𝕋`
  (`Kakeya.VeryNotSticky.rpow_two_eta_mul_volume_carrier_le_volume_shade`), and summing that
  over `𝕋` and dividing by `∑|T| ∈ (0, ∞)` gives this field outright:
  `Kakeya.VeryNotSticky.rpow_two_eta_le_fullness`, which does **not** read this field. So the
  configuration's two fullness levels now agree and the field is consistent by construction,
  whereas at the old `δ^η` it was strictly stronger than anything the band gives — which is the
  rigidity. The `δ^η` of slack the repair creates is precisely the room the refinement needs.

  This is the same move, for the same reason, that took `lam_ge` from `Cd δ^η ≤ lam` to
  `Cd δ^{2η} ≤ lam`. And the repaired exponent is not merely affordable but **free**:
  `Kakeya.VeryNotSticky.fullness_two_eta_of_isCRefinement` derives it from the target's own
  conjuncts `hfull` and `δ^η ≤ c` alone, with no property of the construction entering, while
  `Kakeya.VeryNotSticky.lt_rpow_of_fullness_loss` shows the budget at `δ^η` is exactly `1`.

  **What it costs downstream, in full.** Three declarations read this field, and each loses one
  `η`: `Kakeya.VeryNotSticky.goalUnion_of_goalMult` now delivers the volume form at gain
  `ν - 2η` instead of `ν - η` (it has no term-level users), and
  `Kakeya.VeryNotSticky.exists_full_fibre` now delivers `δ^{2η} ≤ λ(𝕋[T_{ρ₂*}])`, which moves
  the fullness antecedent of `Kakeya.VeryNotSticky.KTScaleData` — a *hypothesis* of the
  Katz–Tao cross-section, so weakening it makes that predicate stronger, and it stays available
  because `Kakeya.VeryNotSticky.ktScaleData_of_le` needs only `2η ≤ η₁` where the Katz–Tao
  exponent threshold `η₁` is chosen after `η`. The third,
  `Kakeya.VeryNotSticky.iUnionShade_nonempty`, uses only positivity. -/
  fullness_ge : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ (2 * η)
  /-- **The common per-tube shading density `λ` of blueprint
  `shadingMultiplicityEstimateForRhoTubes`.**

  `fullness_ge` above is the *aggregate* ratio `(∑_T |Y(T)|)/(∑_T |T|)`, and a ratio of sums
  bounds no individual summand: it does not say that any one tube is `δ^η`-full. Section 5 asks
  for more, namely that all tubes of `𝕋` have *comparable* shading density — the hypotheses
  `hlam_lb` and `hlam_ub` of `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes`, at a
  density `lam` and a comparison constant `Cd`. That data is recorded here, on the
  configuration, because it is a property of the pair `(𝕋, Y)` and of nothing else, and because
  the bundle `Kakeya.ShadedTube.ShadedUniformTubeSet` in `uniform` does not carry it: its
  fields `card_shadeClass_le`, `le_card_shadeClass`, `branchingN_le` and `le_branchingN` compare
  *per-point branching counts* of Definition 2.2, which say nothing about `|Y(T)|` for a single
  tube `T`.

  Recording it here is the standing abuse of notation of the blueprint made explicit: the
  dyadic pigeonholing that makes the shading densities comparable is performed *while*
  Configuration `hyp:ml2setup` is assembled (blueprint `lem:ml2setupexists` lists
  `shadingMultiplicityEstimateForRhoTubes` among its inputs), so the pair recorded by this
  structure is already the pigeonholed one, at the band `lam` and the band ratio `Cd`. -/
  lam : NNReal
  /-- The comparison constant of the per-tube shading density, the `Cd` of
  `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes`.

  It arrives *with* `δ`, not before it, and this costs nothing: `Cd` occurs in no threshold on
  `δ` — not in `aScaleData_absorb`, not in `gridFine` — and it does not occur in the conclusion
  of any statement of the scale-`r` layer. A dyadic band gives `Cd = 2`. -/
  Cd : NNReal
  /-- `1 ≤ Cd`: the density comparison is a comparison constant. -/
  hCd : 1 ≤ Cd
  /-- **The pigeonholed density is at least `Cd · δ^{2η}`.**

  This is *not* implied by `fullness_ge` together with `shading_lb`/`shading_ub`: those give
  only `λ(T, Y) ≤ Cd · lam`, hence `lam ≥ Cd⁻¹ δ^η`. It is what
  `Kakeya.VeryNotSticky.exists_aScaleInputs` spends to convert the outer-fullness conclusion of
  Section 5, which is stated at `Cd⁻¹ · lam`, into the `δ^{2η}` that
  `Kakeya.VeryNotSticky.coarseMassBound` consumes. The producer arranges it by pigeonholing
  into a band whose members are individually at least `δ^{2η}`-full.

  **Why `2η` and not `η` — the exponent was wrong, and this is compiler-verified.** With
  `δ^η` here, this field and `shading_lb` compose (the `Cd` cancels) to make *every* tube of
  `cfg.s` individually `δ^η`-full; `ShadedBody.IsRefinement` keeps carriers equal, so every
  parent tube inherits it, and `tube_count` then forces at least `δ^{-1}` of the *original*
  tubes to be individually `δ^η`-full. But the only fullness hypothesis a producer of this
  structure has — the binder `hfull` of `Kakeya.VeryNotSticky.exists_setup_caseSideData` — is
  the *aggregate* ratio `λ(𝕋, Y) = (∑|Y(T)|)/(∑|T|) ≥ δ^η`, and a weighted average bounds no
  summand: `N` tubes with one fully shaded and the rest at `(Nδ^η - 1)/(N-1) < δ^η` have
  aggregate fullness exactly `δ^η` and exactly one individually-`δ^η`-full member. At `δ^{2η}`
  the demand is met: the tubes of individual density `< δ^{2η}` carry less than
  `δ^{2η} ∑|T| ≤ δ^η ∑|Y|` of the shade mass, so discarding them costs a `δ^η` fraction and
  keeps all but a `δ^η` fraction of the tubes. See
  `Kakeya.VeryNotSticky.rpow_two_eta_mul_volume_carrier_le_volume_shade` and
  `Kakeya.VeryNotSticky.tubeCount_of_setupCaseSideDataStatement` in
  `Kakeya.DimensionThree.MainLemma2.SetupAbsorption`, and the Markov bound
  `Kakeya.VeryNotSticky.sum_volume_shade_lowDensity_le` there, which is the mechanical check
  that the repaired exponent *is* deliverable from the aggregate binder.

  The extra `η` is paid for downstream and costs nothing: the one consumer,
  `Kakeya.VeryNotSticky.exists_aScaleInputs`, hands it to
  `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale`, whose budget `hνη : 90 η ≤ ν` already
  discards a spare `δ^η` inside `Kakeya.VeryNotSticky.coarseVolumeLower_right`; the gain
  `δ^{2η+ν/90}` of `Kakeya.VeryNotSticky.coarseVolumeLower` and the statement of
  `Kakeya.VeryNotSticky.aScaleVolume` are unchanged.

  **Why the `Cd`, and why the bare `δ^η ≤ lam` was the wrong clause.** The pair `(lam, Cd)`
  is not pinned by the rest of the structure: the rescaling `(lam, Cd) ↦ (t·lam, t·Cd)`,
  `1 ≤ t`, carries any configuration to another one — see
  `Kakeya.VeryNotSticky.rescaleDensity` in
  `Kakeya.DimensionThree.MainLemma2.AScaleGuardrails`. Both `shading_lb` and `shading_ub` are
  invariant, the first because it depends on `(lam, Cd)` only through `Cd⁻¹ · lam`, the second
  because it only weakens. So `lam` alone is not a quantity of the data, and a clause reading
  the bare `lam`, such as the earlier `δ^η ≤ lam`, constrains nothing: it can always be met by
  rescaling. The scale-invariant combination is `Cd⁻¹ · lam`, and this clause is exactly
  `δ^{2η} ≤ Cd⁻¹ · lam` cleared of the inverse. That invariance is also what makes the fullness
  conjunct of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` a non-refutable
  statement, and it is what the `⪆` of GWZ §9 (`λ(𝕋_a, Y_{𝕋_a}) ⪆ λ(𝕋, Y) ≥ δ^η`) hides: the
  band-comparison constant of the dyadic pigeonholing, `Cd = 2`. -/
  lam_ge : Cd * δ ^ (2 * η) ≤ lam
  /-- `Cd⁻¹ · lam · |T| ≤ |Y(T)|` for every `T ∈ 𝕋`, the hypothesis `hlam_lb` of
  `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes`. -/
  shading_lb : ∀ i ∈ s,
    (Cd : ENNReal)⁻¹ * ((lam : ENNReal) * volume (T i).toShadedBody.carrier) ≤
      volume (T i).toShadedBody.shade
  /-- `|Y(T)| ≤ Cd · lam · |T|` for every `T ∈ 𝕋`, the hypothesis `hlam_ub` of
  `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes`. -/
  shading_ub : ∀ i ∈ s,
    volume (T i).toShadedBody.shade ≤
      (Cd : ENNReal) * ((lam : ENNReal) * volume (T i).toShadedBody.carrier)
  /-- **The `ρ`-tube count bound of blueprint `lemmain2vns`, read on the family's own parent,
  with the parent's uniform hierarchy and the cardinality retention** — the datum
  `Kakeya.VeryNotSticky.RhoParentData`: a parent `sPar ⊇ s` in `B₁` with
  `Δ_max ≤ δ^{-η}`, GWZ Definition 2.1 on the standard grid at a constant `1 ≤ Cpar ≤ δ^{-η}`,
  the count `|𝕋_ρ| ≥ ρ^{-2-ζ}` in its  `∃`-form over `ρ ∈ [δ^{1-exscalb}, δ^{exscalb}]`,
  and `δ^{2η}|sPar| ≤ |s|`.

  **Why not `RhoCountOn δ ζ exscalb s T 1`, the literal third bullet of `lemmain2vns`.** That
  form — `Kakeya.VeryNotSticky.RhoCountFieldOldStatement`, which this field used to carry — is
  not merely unproved from the binders of
  `Kakeya.VeryNotSticky.exists_setup_caseSideData`; it is **false at a legal refinement**, and
  no constant repairs it. The clause is *antitone* in the index set
  (`Kakeya.VeryNotSticky.rhoCountOn_mono_index`: a family covering `s` also covers every
  `s' ⊆ s`, so the covers of `s'` are a superset and a lower bound over all of them is the
  stronger statement), and the producer must deliver it for `cfg.s ⊆ s` while being handed it
  for `s` — the implication runs the wrong way. At the extreme legal refinement `cfg.s = ∅` the
  empty family of `ρ`-tubes covers it vacuously and is pairwise essentially distinct vacuously,
  so the clause demands `ρ^{-2-ζ} ≤ Ccount · 0`, which fails for **every** `Ccount`:
  `Kakeya.VeryNotSticky.not_rhoCountFieldOldStatement_empty`. So this is a wrong-*family*
  defect, not a wrong-constant one, and the `lam_ge` precedent (a `≥` with the wrong constant,
  repaired by a constant) does not transfer.

  **Why the parent carries its hierarchy and the retention.** The previous
  form of this field, `Kakeya.VeryNotSticky.RhoCountParent`, carried the count alone — in a
  `∀`-over-essentially-distinct-covers form, on a parent linked to `s` by `⊆` and nothing else —
  and the configuration could not compare `s`'s own hierarchy with the parent's count. GWZ's link is the
  *input's* `∼1`-uniformity, which the three added clauses restore (
  (α),(β),(γ)). The hierarchy is tube-level (`Tube.UniformTubeSet`), because the cut family's
  shades differ from the input's and only the tube part transports
  (`Kakeya.VeryNotSticky.tubeUniform_of_shaded`); its constant `Cpar` is separate from `C₀`,
  because `aScaleData_absorb` would break if `C₀` absorbed the input's constant. The previous
  form is recovered at the constant `max C₀ (Tube.coverCountLoss 3)` by
  `Kakeya.VeryNotSticky.rhoCountParent_of_rhoParentData`, so no consumer is lost, and the datum
  is produced at the cut from Lemma 9.1's binders by
  `Kakeya.VeryNotSticky.rhoParentData_of_binders`, the retention coming from the mass retention
  of the cut and the input's fullness (`Kakeya.VeryNotSticky.card_retention_of_mass`). -/
  rho_count : VeryNotSticky.RhoParentData δ ζ exscalb η s T
  /-- The Katz–Tao estimate `K_KT(β)` holds. -/
  ktEstimate : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β
  /-- The Frostman estimate `K_F(β)` holds. -/
  fEstimate : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β
  /-- The factoring bias exponent `ϱ` (blueprint `\exfact`). -/
  ϱ : ℝ
  /-- Positivity of `ϱ`. -/
  hϱ : 0 < ϱ
  /-- Smallest working dimension `a` of the per-ball factoring bodies `W ∈ 𝕎_B`.

  GWZ §9.3 (`gwz.txt` l.2036-2041) applies Lemma 9.2 to `𝕋_B` for each ball `B` and, by
  pigeonholing, takes the bodies `W ∈ 𝕎_B` to have dimensions `a × b × r₁` with `a ≤ b ≤ r₁`
  for every `B`. There is no global factoring of `𝕋`. The six global-factoring fields this
  structure once carried (`Cϱ`, `factoring`, `Wpart`, `hWpart`, `ha_dim`, `hb_dim`) would constrain a global factorization; a singleton realization forces `a = b = δ`. The per-ball factoring is data of
  `Kakeya.VeryNotSticky.BallData`; here `a`, `b` are free scales constrained only by `hdims`,
  pinned by `Kakeya.VeryNotSticky.statement_of_universal_vns_fields`. -/
  a : NNReal
  /-- Middle working dimension `b` of the per-ball factoring bodies `W ∈ 𝕎_B` (see `a`). -/
  b : NNReal
  /-- The working dimensions satisfy `δ ≤ a ≤ b ≤ r_1 = δ^{exscal}` (GWZ l.2040, `a ≤ b ≤ r₁`;
  `δ ≤ a` because the bodies contain `δ`-tubes). -/
  hdims : δ ≤ a ∧ a ≤ b ∧ b ≤ δ ^ exscal
  /-- (C1) The family is large at the fixed scale `δ`: `1 ≤ δ |𝕋|`, the division-free form of
  `|𝕋| ≥ δ^{-1}`.

  This is the fixed-scale consequence of `rho_count` at the coarse endpoint `ρ = δ^{1-exscal}`,
  which lies in the admissible window because `exscal < 1/2`. It is recorded as data rather
  than derived because the count of `rho_count` lives on the parent `sPar`, and passing from
  `|sPar| ≥ δ^{-1-α}` to `|s|` costs the retention `δ^{2η}`
  (`Kakeya.VeryNotSticky.tubeCount_of_parent_of_retention`), whereas the producers read
  `1 ≤ δ|s|` directly off the refinement they build (`Kakeya.VeryNotSticky.BandUniformRefinement`,
  `Kakeya.VeryNotSticky.BandUniformRefinementLocalMass`). It is spent once, in
  `Kakeya.VeryNotSticky.slabVolumeGoal`. -/
  tube_count : (1 : ENNReal) ≤ (δ : ENNReal) * (s.card : ENNReal)
  /-- **The absorption of the scale-`r` comparison constant** (blueprint
  `def:ml2aScaleDataThreshold`): the accumulated constant
  `C_⋆(C₀, D₀) = max(C_{lem:ml2aScaleBall}, C_{lem:ml2aScaleVolume}(C₀, D₀))` of the scale-`r`
  layer satisfies `C_⋆² ≤ δ^{-η}`.

  It is the eighth clause of Configuration `hyp:ml2scale`, and it is recorded here, on the
  configuration, rather than on `Kakeya.VeryNotSticky.ScaleThresholds`, because it is not
  expressible on that bundle. The blueprint writes the threshold as a function of
  `ν, β, ζ, η, C₀, D₀` precisely because the bundle is chosen *after* the configuration and
  its uniformity constants; `Kakeya.VeryNotSticky.ScaleThresholds.aScale` takes only the gain
  `ν`, so the implication `δ ≤ aScale ν → C_⋆(C₀, D₀)² ≤ δ^{-η}` quantified over `C₀, D₀`
  would be **false**, `C_⋆` being unbounded in `C₀`. Stated here, against this configuration's
  own `C₀` and `D₀`, it is a condition on `δ` alone, arrangeable because `C₀`, `D₀` and `η`
  are all fixed before `δ`; and it is what makes clause (iii) of blueprint
  `lem:ml2aScaleData` provable rather than refutable at `δ` near `1`.

  It is the one clause of `hyp:ml2scale` that Configuration `hyp:ml2setup` carries. The
  divergence is forced, and it is confined: the companion clause
  `Kakeya.VeryNotSticky.CaseScale.aScaleData_threshold` is unchanged and is still spent, so
  the gain-dependent half of the threshold continues to travel with the case split. -/
  aScaleData_absorb : (aScaleDataConstant C₀ D₀ : ENNReal) ^ 2 ≤ (δ : ENNReal) ^ (-η)
  /-- **The absorption of the honest Section-5 loss constant** (blueprint `lem:ml2rhoTubes`
  read at this configuration): the loss `Kakeya.VeryNotSticky.coarseLoss` that GWZ Lemma 5.11
  actually charges satisfies `coarseLoss ≤ δ^{-η}`.

  `coarseLoss cfg = ShadedBody.rhoTubesSection9Loss 3 |𝕋| δ` is *not* a closed constant: by
  `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox` it is only `δ^{-o(1)}`,
  a function of both `δ` and `|𝕋|`. That is why it cannot be carried by
  `Kakeya.aScaleDataConstant`, which is by design a function of `C₀` and `D₀` alone so that
  `C_⋆` may be fixed *before* `δ` (see `aScaleData_absorb` above); and it is why the residue
  `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` cannot be restated at the honest loss
  without this clause. Compare
  `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_subfamily`, which is *proved* and
  carries `coarseLoss` outright, against the residue, which is stated at the placeholder
  numeral `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1`: this clause is
  exactly the currency that closes the gap between the two.

  It is a condition on `δ` alone once `η` and a polynomial cardinality budget `|𝕋| ≤ δ^{-K}`
  are fixed, by `ShadedBody.rhoTubesSection9Loss_le_rpow_neg`; the arrangeability certificate
  is `Kakeya.VeryNotSticky.eventually_coarseLoss_absorb` in
  `Kakeya.DimensionThree.MainLemma2.SetupAbsorption`, of exactly the same shape as the proved
  `Kakeya.VeryNotSticky.eventually_aScaleData_absorb`. So it does not disturb the quantifier
  order that `aScaleData_absorb` depends on.

  The exponent budget pays for it with room: the standing `hνη : 90 η ≤ ν` of
  `Kakeya.VeryNotSticky.exists_aScaleData` tolerates a coarse fullness exponent up to `9 η`
  and no more, which is
  `Kakeya.VeryNotSticky.coarseLossExponentHeadroom` together with
  `Kakeya.VeryNotSticky.coarseLossExponentHeadroom_sharp`; the layer runs at `2 η`, so one
  further `η` leaves six spare. -/
  coarseLoss_absorb :
    ((_root_.ShadedBody.rhoTubesSection9Loss 3 s.card δ : NNReal) : ENNReal) ≤
      (δ : ENNReal) ^ (-η)
  /-- **The purely dimensional fullness loss of the coarse family is absorbed by `δ^{-η}`.**

  `ShadedBody.rhoTubesInducedFullnessLoss 3 = max 1 (Kakeya.Tube.dilateFullness.C 3)` is the loss
  of the *fullness* clause of GWZ Lemma 5.11 on the whole coarse family
  (`ShadedBody.exists_rhoTubesSection9_fullFamily`), and unlike
  `Kakeya.VeryNotSticky.coarseLoss` it depends on neither `δ` nor `|𝕋|` — it is a single
  dimensional constant. So this clause is a condition on `δ` alone with no quantifier subtlety at
  all: the certificate is `Kakeya.VeryNotSticky.eventually_inducedFullnessLoss_absorb`, an
  instance of `Kakeya.VeryNotSticky.eventually_nnreal_le_rpow_neg` at that constant, and it needs
  no cardinality budget, unlike `coarseLoss_absorb` above.

  **What it buys.** `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` states its fullness
  conjunct at this loss — GWZ write `λ(𝕋_a, Y_{𝕋_a}) ⪆ λ`, and §2.2 defines `⪆` as permitting a
  sub-polynomial factor, so a loss is faithful and the numeral `1` was not. This clause is what
  converts that conjunct back into the `δ`-power the scale-`r` layer consumes: with
  `Kakeya.VeryNotSticky.lam_ge` it gives `δ^{3η} ≤ λ(𝕋_ρ, Y_{𝕋_ρ})`, one `η` weaker than the
  `δ^{2η}` the placeholder afforded. The exponent budget has room for exactly that and five more:
  see `Kakeya.VeryNotSticky.coarseLossExponentHeadroom`. -/
  inducedFullnessLoss_absorb :
    ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal) ≤
      (δ : ENNReal) ^ (-η)
  /-- **GWZ (87): the local mass of the shaded union at every grid scale.**

  GWZ §9.3 p. 36: "Next we apply Lemma 5.11 to `(𝕋, Y)` and `𝕋_a`, for `a = δ^{ηj}` … We obtain
  an `a ≈ 1` refinement of `(𝕋, Y)` … so that for each `x ∈ U(𝕋_a, Y_{𝕋_a})` we have
  `|U(𝕋,Y)| ⪆ |U(𝕋_a, Y_{𝕋_a})| · |U(𝕋,Y) ∩ B(x,a)| / |B(x,a)|`."  That is this clause, with the
  `⪆` read at the gain `δ^η`.

  It is an **input**, not an obligation of the layer: the refinement GWZ perform is done while
  the configuration is assembled, and no field of this structure records that it happened, so the
  layer cannot re-derive it. `Metric.cthickening (2ρ) (U(𝕋, Y))` is the configuration-nameable
  upper bound for the coarse union `U(𝕋_ρ, Y_{𝕋_ρ})`: the structure holds the hierarchy only as a
  `Nonempty`, so it cannot name that union, while the induced coarse shading
  `Y_{𝕋_ρ}(T_ρ) = T_ρ ∩ N_{2ρ}(⋃_{T ∈ 𝕋[T_ρ]} Y(T))` sits inside it by construction
  (`ShadedBody.iUnion_inducedCoarseShading_subset_cthickening`).

  Exponent `η`, not `2η`: the ball conjunct's loss constant is `≥ 1`, so its inverse is `≤ 1` and
  the field at `η` covers the conjunct at any honest constant. Quantifying `x` over the whole
  space rather than over the coarse union costs nothing, since `|U ∩ B(x,ρ)| = 0` far from `U`,
  and is what makes the clause statable without naming the hierarchy.

  **Where it is free and where it is not.** At `k = 0` (`ρ = 1`) the clause reduces to
  `27 δ^η ≤ 1`, a `δ`-smallness condition of the `aScaleData_absorb` shape, because `U ⊆ B₁` by
  `contained` and `ShadedBody.shade_subset`. At `k = ⌈log log 1/δ⌉` (`ρ = δ`) it becomes
  `δ^η |N_{2δ}(U)| ≤ |U|` at a point where `U` contains a full `δ`-ball; that holds when `U` is a
  union of `δ`-balls, which is the regime GWZ's §2.2 convention puts shadings in ("any shading
  `Y(V)` with small measure … can be replaced by `Y(V) = ∅`"), but it is a real hypothesis and not
  a triviality. It is the producer's to check, not the layer's. -/
  coarseLocalMass : ∀ k : ℕ, k ≤ Tube.ssfGridLen δ →
    ∀ x : EuclideanSpace ℝ (Fin 3),
      (δ : ENNReal) ^ η *
          (volume (Metric.cthickening
                (2 * (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ))
                (⋃ i ∈ s, (T i).toShadedBody.shade)) *
            (volume ((⋃ i ∈ s, (T i).toShadedBody.shade) ∩
                  Metric.ball x (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ)) /
              volume (Metric.ball x (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ)))) ≤
        volume (⋃ i ∈ s, (T i).toShadedBody.shade)
  /-- **The multiscale grid is fine enough that one grid step costs at most `δ^η`**:
  `1 ≤ η ⌈log log 1/δ⌉`.

  The family `(T, Y)` is uniform on the grid of GWZ Definition 2.1, whose scales are the
  `δ^{k/N}` with `N = ⌈log log 1/δ⌉`, and whose consecutive scales therefore differ by the
  single factor `δ^{1/N}`. This clause says that that factor is at most `δ^{-η}`, which is
  what lets an arbitrary radius `r ∈ [δ, 1]` be *rounded up* to a grid scale at a cost the
  exponent budgets of the scale-`r` layer can pay for
  (`Kakeya.StickyKakeya.exists_gridScale_ge`, and `Kakeya.StickyKakeya.rpow_neg_div_le_rpow_neg`
  for the accounting). It is the clause that makes
  `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` a statement about a *grid* family rather
  than about a family at a radius the hierarchy does not know.

  It is a condition on `δ` alone: `η` is fixed before `δ`, and
  `Kakeya.StickyKakeya.exists_ssfGridLen_threshold` produces, for that `η`, a threshold below
  which it holds, because `⌈log log 1/δ⌉ → ∞` as `δ → 0⁺`. In particular it does not tie `δ`
  to any constant produced *after* `δ`, so it does not disturb the quantifier order that
  `aScaleData_absorb` above depends on. Both clauses are of the shape `δ ≤ δ_*` with `δ_*`
  determined by data fixed before `δ`, so they are met simultaneously by taking the smaller
  threshold; neither constrains the other. Sub-polynomiality of the grid step is the design
  intent of the grid length `log log 1/δ`, and is the same computation already recorded in the
  docstring of `Kakeya.ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, the producer of
  the bundle in `uniform`, and of its tube-level counterparts
  `Tube.exists_uniformTubeSet_subfamily` and
  `Tube.exists_uniformTubeSet_subfamily_ssf`.

  GWZ arrange the same thing by hand at p. 41, choosing a radius of the form `δ^{ηj}` between
  `θ b` and `δ^{-η} θ b` and paying `δ^{3η}` for the change of ball radius; rounding to the
  Definition 2.1 grid is strictly cheaper, since `δ^{1/N} ≥ δ^{η}` is exactly this clause. -/
  gridFine : 1 ≤ η * (Tube.ssfGridLen δ : ℝ)
  /-- **The coarse Katz--Tao window datum** (`Kakeya.CoarseKTData`).

  This is what replaces the refuted `Kakeya.VeryNotSticky.coarseKatzTaoBound`: with it,
  `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` is proved from the *repaired*
  `Kakeya.VeryNotSticky.coarseKatzTaoBound_general_at`.

  Like `ktEstimate` and `gridFine` it is an **input** to the producer of a configuration, not
  something the producer must construct: its `δ`-free part `Kakeya.CoarseKTWindow` is handed in,
  and the one scale clause is arranged by `Kakeya.CoarseKTWindow.eventually_radius` inside the
  `∀ᶠ δ` every producer already carries. -/
  ckt : Kakeya.CoarseKTData.{u} β ϱ η exscal δ

namespace VeryNotSticky

/-! ### The dimension block of `VeryNotSticky`

GWZ Section 9.3 factors separately in each ball (`gwz.txt` l.2036-2041).
The configuration therefore carries the scales `a`, `b`, and `hdims`;
the factorization data belong to `BallData`. The named proposition below
records exactly the scale range `δ ≤ a ≤ b ≤ r₁`.
-/

/-- **The retained dimension block of `Kakeya.VeryNotSticky`, as a
named `Prop`**: two free scales `a b : NNReal` (the fields `Kakeya.VeryNotSticky.a`,
`Kakeya.VeryNotSticky.b`) constrained only by `δ ≤ a ≤ b ≤ r₁ = δ^{exscal}`, the text of
`Kakeya.VeryNotSticky.hdims` verbatim. No field of the configuration ties `a`, `b` to a
global factoring of `𝕋`. -/
def statement_of_universal_vns_fields (cfg : VeryNotSticky.{u}) : Prop :=
  cfg.δ ≤ cfg.a ∧ cfg.a ≤ cfg.b ∧ cfg.b ≤ cfg.δ ^ cfg.exscal

/-- **The pin.** The field `Kakeya.VeryNotSticky.hdims` is `statement_of_universal_vns_fields`
by unfolding and nothing else: the proof term is the projection itself. -/
theorem statement_of_universal_vns_fields_pinned (cfg : VeryNotSticky.{u}) :
    statement_of_universal_vns_fields cfg :=
  cfg.hdims

/-- A fixed bookkeeping coefficient used to replace the `O(·)` loss in the tangential
branch by an explicit exponent budget. It bounds the accumulated exponent loss in the tangential estimate. -/
def parameterSeparationConstant : ℝ := 2 ^ 20

/-- Explicit admissibility conditions for the parameters in the Main Lemma 2 case split.

The inequalities are the exponent budgets used by the five leaves. Strict inequalities leave
a positive margin in which fixed multiplicative constants can be absorbed after restricting
to a sufficiently small scale.

This structure deliberately contains no condition on `δ`: scale-dependent thresholds, such
as the bound making `ρ₂* ≤ 1`, are packaged separately in
`Kakeya.VeryNotSticky.CaseScale`. -/
structure CaseParams (β ζ exscal ϱ η τ τ' : ℝ) : Prop where
  /-- Positivity of the thick/thin threshold exponent. -/
  hτ : 0 < τ
  /-- The transverse/tangential exponent is larger than the thick/thin exponent. -/
  hτ' : τ < τ'
  /-- The coarse-scale window is nonempty. -/
  scale : exscal < 1 / 2
  /-- The rescaled thin parameter `a / r₁` tends to zero with `δ`. -/
  thinScale : τ + exscal < 1
  /-- The thin/coarse window is inside the *lower half*: `τ + exscal ≤ 1/2`.

  Strictly stronger than `scale` and `thinScale` together, and free at the existing choices of
  `Kakeya.VeryNotSticky.exists_caseParams` (`exscal ≤ 1/100`, `τ ≤ exscal/2`, whence
  `τ + exscal ≤ (3/2)·exscal ≤ 3/200`). It is what makes the fixed multiple `16` of the O5
  fullness exponent (`Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness`) closable
  against the derivable fullness `δ^{7η + exscal·η}`: one needs
  `(1 − τ − exscal)·16η > 7η + exscal·η`, which holds at `τ + exscal ≤ 1/2` and for which no
  fixed multiple works under `thinScale` alone. -/
  thinHalf : τ + exscal ≤ 1 / 2
  /-- Density loss is small compared with the factoring bias. -/
  densityBias : parameterSeparationConstant * η < ϱ
  /-- The slab estimate can use the density lower bound at exponent `exscal`: `6η < exscal`,
  chained against `Kakeya.ThinCase.ThinBall.fullness_bodies` at the `tb` index `2η` of
  `Kakeya.VeryNotSticky.ThinConfig.tb`, i.e. `δ^{6η}` (the (C5) exponent in the density clause); discharged from `η ≤ exscal/8` in
  `Kakeya.VeryNotSticky.exists_caseParams`. -/
  slabDensity : 6 * η < exscal
  /-- The biased-factorization loss can be absorbed in the slab estimate. -/
  slabBias : parameterSeparationConstant * ϱ < exscal
  /-- Budget producing the thick-case gain `ϱ β τ / 8`. -/
  thick : parameterSeparationConstant * η < ϱ * β * τ
  /-- Budget producing the slab-case gain `β / 2`.

  `12η + 12 exscal + 3τ` and not GWZ's `9η + 10 exscal + 3τ` (`gwz.txt` l.2216-2217, "we choose
  `τ, η, ϵ_scal ≪ β`"): the repaired segment-mass clause (T7),
  `Kakeya.VeryNotSticky.ThinConfig.segment_mass`, costs `2η` in the exponent and the fibre
  count `Cm · m` on the right, budgeted at `δ^{-(η+2 exscal)}`;
  the `4η` of margin `Kakeya.VeryNotSticky.slabVolumeGoal` then kept is spent by the (C5)
  exponent `2η` in the density clause: the slab chain reaches the honest
  `11η + 10 exscal + 3τ` with no margin left, and the sum is the exponent of
  `Kakeya.VeryNotSticky.SlabScale.final`. Like every other
  field it bounds `η`, `exscal`, `τ` from above only, so
  `Kakeya.VeryNotSticky.exists_caseParams` absorbs it by shrinking `η`. -/
  slab : 12 * η + 12 * exscal + 3 * τ < β / 2
  /-- Budget producing the small-multiplicity gain `exscal β`.

  The small-multiplicity branch `Kakeya.VeryNotSticky.goalMult_of_multBodies_le` spends `η`
  on its multiplicity hypothesis and a further `η` on the step raising the fibre count to the
  `β`-th power, which `Kakeya.VeryNotSticky.nonslabKKT` already carries; together with the
  factoring bias `ϱ` this is `2η + ϱ`, and the gain `exscal β` is what remains of
  `exscal(2+ζ)β` after it.

  Hence `2η` and not the `η` of earlier versions: the surplus `exscal(1+ζ)β - (η+ϱ)` of the
  weaker form is positive but is not known to exceed `η`, and `η` is fixed before `δ`, so it
  cannot be shrunk afterwards. The strengthening is free, for the reason recorded under
  `transverse` below: `η` is chosen last and every field here bounds it from above only. -/
  smallMultiplicity : 17 * η + ϱ < exscal * (1 + ζ) * β
  /-- Budget producing the transverse gain `τ' β / 2`.

  The transverse chain spends `5η` at `Kakeya.VeryNotSticky.transverseFill` — `4η` from Item 1
  of `ShadedPlank.reduction_to_slab` plus the auxiliary exponent `ε` of that lemma, which is
  free but positive and is applied at `ε = η/256`, the largest value the exponent gap
  `128ε ≤ ε' = η/2` permits; since `a ≤ 1` and `ε ≤ η` the gain `a^{4η+ε}` is at least `a^{5η}`,
  so `5η` is the budget — and a further `2η` at the transfer (`Kakeya.ThinCase.transfer_thin`
  at the `tb` index `2η` of `Kakeya.VeryNotSticky.ThinConfig.tb`, F8), so
  `Kakeya.VeryNotSticky.transverseBallFill` reaches `3τ + 7η`.

  A further `3η` is spent by the absorption hypothesis `hM'` of
  `Kakeya.VeryNotSticky.exists_aScaleData`, applied at `M = Cbf` and `e = τ'β - 3τ - 7η`:
  namely `2η` for the sub-polynomial bound `Cbf ≤ δ^{-2η}` of
  `Kakeya.VeryNotSticky.transverseBallFill`, plus the fixed exponent `η = ν_{lem:ml2aScaleData}`
  that `exists_aScaleData` spends on its own constant in its conjunct `C² ≤ δ^{-η}`. This is
  blueprint `lem:ml2transverseAbsorbBudget`, which therefore needs `2η ≤ e - η`, that is
  `3τ + 10η ≤ τ' β`.

  The remaining `2η` is *reserved*, not surplus: it is what pays for the enlargement to an
  admissible radius if the eventual proof of `Kakeya.VeryNotSticky.exists_aScaleData` needs it
  (blueprint `lem:ml2transverseDensity`, second remark). Hence `3τ + 12η` and not the `3τ + 9η`
  of the earlier version, which was the value with the reserve unreleased.

  The strengthening is free: `η` is chosen after `β`, `ζ`, `exscal`, `ϱ`, `τ` and `τ'`, and
  every field of this structure bounds `η` from above only, so the system stays satisfiable.
  The one other consumer of this budget, the tangential slab decomposition, uses only the
  consequence `7η < τ' β`, which the larger value still gives. -/
  transverse : 3 * τ + 87 * η < τ' * β
  /-- Explicit replacement for the `O(ϱ + τ')` loss in the tangential branch. -/
  tangential : parameterSeparationConstant * (ϱ + τ') < exscal * β * ζ / 2
  /-- **The bias exponent is below the thick/thin threshold exponent**, `ϱ ≤ τ`.

  This is what converts the configuration-only bound `Kakeya.CoarseKTData.hwe`
  (`we ≤ ϱ² wb / 1440`) into `we ≤ ν/180` at the *thick* gain `ν = ϱβτ/8`: with `wb ≤ β` it
  gives `ϱ² wb ≤ ϱ β τ`.  At the transverse gain `ν = τ'β/2` the conversion needs only
  `ϱ ≤ τ'`, which `hτ'` and `slabBias` already provide.

  It costs nothing: `Kakeya.VeryNotSticky.exists_caseParams` builds `ϱ` as a `min`, and every
  other clause of this structure bounds `ϱ` from *above*, so one more term in that `min` is
  free.  It mentions neither `β` nor `η`, so `Kakeya.VNSUniform.CaseParams.mono_beta` and
  `Kakeya.VNSUniform.CaseParams.mono_eta` carry it unchanged. -/
  rhoLeTau : ϱ ≤ τ

/-- **The node radius inherits the nominal radius bound**, at the cost of the one grid step
`δ^{-η}` that `Kakeya.VeryNotSticky.exists_gridIndex` pays.  This is what turns a bound on `r`
into the hypothesis `hρ₀` of `coarseKatzTaoBound_of_etaBudget_atThresholds`. -/
theorem coarseRadius_of_grid (cfg : VeryNotSticky.{u}) {r ρ : NNReal}
    (hρr : ρ ≤ cfg.δ ^ (-cfg.η) * r) (hr : r ≤ 6 * cfg.δ ^ cfg.exscal) :
    ρ ≤ 6 * cfg.δ ^ (cfg.exscal - cfg.η) := by
  refine le_trans hρr ?_
  calc cfg.δ ^ (-cfg.η) * r ≤ cfg.δ ^ (-cfg.η) * (6 * cfg.δ ^ cfg.exscal) := by gcongr
    _ = 6 * (cfg.δ ^ (-cfg.η) * cfg.δ ^ cfg.exscal) := by ring
    _ = 6 * cfg.δ ^ (cfg.exscal - cfg.η) := by
        rw [← NNReal.rpow_add cfg.hδ.ne']
        congr 2
        ring

/-- **The thick branch supplies the nominal radius bound.**  It invokes the scale-`r` layer at
`r = cfg.a`, and `cfg.hdims` gives `a ≤ b ≤ δ^{exscal}`. -/
theorem thickRadius_le_six_rpow_exscal (cfg : VeryNotSticky.{u}) :
    cfg.a ≤ 6 * cfg.δ ^ cfg.exscal := by
  have h : cfg.a ≤ cfg.δ ^ cfg.exscal := le_trans cfg.hdims.2.1 cfg.hdims.2.2
  calc cfg.a ≤ cfg.δ ^ cfg.exscal := h
    _ = 1 * cfg.δ ^ cfg.exscal := (one_mul _).symm
    _ ≤ 6 * cfg.δ ^ cfg.exscal := by gcongr; norm_num

/-- **The loss exponent sits below `ν/180` at the thick gain** `ν = ϱβτ/8`.

`Kakeya.CoarseKTData.hwe` bounds `we` by `ϱ² wb / 1440`, and `Kakeya.CoarseKTData.hwb` together
with `Kakeya.VeryNotSticky.CaseParams.rhoLeTau` turns `ϱ² wb` into `ϱ β τ`.  This is one of the
two binders that `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` asks of its call sites. -/
theorem ckt_we_le_thickGain (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ') :
    cfg.ckt.we ≤ cfg.ϱ * cfg.β * τ / 8 / 180 := by
  have hϱ : 0 < cfg.ϱ := cfg.hϱ
  have hβ : 0 < cfg.β := cfg.hβ
  have hwb0 : 0 < cfg.ckt.wb := cfg.ckt.hwb0
  have hwb : cfg.ckt.wb ≤ cfg.β := cfg.ckt.hwb
  have hρτ : cfg.ϱ ≤ τ := params.rhoLeTau
  have hkey : cfg.ϱ * cfg.ckt.wb ≤ τ * cfg.β := by nlinarith
  have hsq : cfg.ϱ ^ 2 * cfg.ckt.wb ≤ cfg.ϱ * (τ * cfg.β) := by
    have := mul_le_mul_of_nonneg_left hkey hϱ.le
    nlinarith
  have hwe := cfg.ckt.hwe
  linarith

/-- **The loss exponent sits below `ν/180` at the transverse gain** `ν = τ'β/2`.  Companion of
`Kakeya.VeryNotSticky.ckt_we_le_thickGain`; here `ϱ ≤ τ < τ'` and `ϱ ≤ 1` suffice, the latter
from `Kakeya.VeryNotSticky.CaseParams.slabBias` and `Kakeya.VeryNotSticky.CaseParams.scale`. -/
theorem ckt_we_le_transverseGain (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ') :
    cfg.ckt.we ≤ τ' * cfg.β / 2 / 180 := by
  have hϱ : 0 < cfg.ϱ := cfg.hϱ
  have hβ : 0 < cfg.β := cfg.hβ
  have hwb0 : 0 < cfg.ckt.wb := cfg.ckt.hwb0
  have hwb : cfg.ckt.wb ≤ cfg.β := cfg.ckt.hwb
  have hρτ : cfg.ϱ ≤ τ := params.rhoLeTau
  have hττ' : τ < τ' := params.hτ'
  have hτ0 : 0 < τ := params.hτ
  have hsb : parameterSeparationConstant * cfg.ϱ < cfg.exscal := params.slabBias
  have hsc : cfg.exscal < 1 / 2 := params.scale
  have hc : (parameterSeparationConstant : ℝ) = 2 ^ 20 := rfl
  have hϱ1 : cfg.ϱ ≤ 1 := by rw [hc] at hsb; nlinarith
  have hτ'0 : 0 < τ' := lt_trans hτ0 hττ'
  have hsq : cfg.ϱ ^ 2 ≤ cfg.ϱ := by nlinarith
  have h1 : cfg.ϱ ^ 2 * cfg.ckt.wb ≤ cfg.ϱ * cfg.ckt.wb :=
    mul_le_mul_of_nonneg_right hsq hwb0.le
  have h2 : cfg.ϱ * cfg.ckt.wb ≤ cfg.ϱ * cfg.β := mul_le_mul_of_nonneg_left hwb hϱ.le
  have h3 : cfg.ϱ * cfg.β ≤ τ' * cfg.β :=
    mul_le_mul_of_nonneg_right (le_trans hρτ hττ'.le) hβ.le
  have hkey : cfg.ϱ ^ 2 * cfg.ckt.wb ≤ 4 * (τ' * cfg.β) := by nlinarith
  have hwe := cfg.ckt.hwe
  linarith


end VeryNotSticky

namespace VNSUniform

open VeryNotSticky

/-- **`CaseParams` is antitone in `η`.**  Every field bounds `η` from above only, which is the
fact `Kakeya.VeryNotSticky.exists_caseParams` relies on when it takes `η` to be a minimum of
eight quantities, and which lets a further upper bound be imposed on `η` after the fact. -/
theorem CaseParams.mono_eta {β ζ exscal ϱ η η' τ τ' : ℝ} (hη' : η' ≤ η)
    (h : CaseParams β ζ exscal ϱ η τ τ') :
    CaseParams β ζ exscal ϱ η' τ τ' := by
  have hc : (0 : ℝ) < parameterSeparationConstant := by
    unfold parameterSeparationConstant; norm_num
  refine { h with
    densityBias := ?_, slabDensity := ?_, thick := ?_, slab := ?_,
    smallMultiplicity := ?_, transverse := ?_ }
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hη' hc.le) h.densityBias
  · exact lt_of_le_of_lt (by linarith) h.slabDensity
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hη' hc.le) h.thick
  · exact lt_of_le_of_lt (by linarith) h.slab
  · exact lt_of_le_of_lt (by linarith) h.smallMultiplicity
  · exact lt_of_le_of_lt (by linarith) h.transverse


end VNSUniform

namespace VeryNotSticky

/-- **The by-choice smallness thresholds of Configuration `hyp:ml2scale`** (blueprint
`def:ml2aScaleDataThreshold`, `def:ml2typicalangleThreshold`,
`def:ml2transverseFillThreshold`).

Three clauses of Configuration `hyp:ml2scale` — the eighth, ninth and eleventh — are of the
shape `δ ≤ δ_*` rather than a comparison of two terms, because the quantity each of them
bounds (the constant of blueprint `lem:ml2goalfromdens`, the typicality constant of
`lem:ml2typicalangle`, the constant `c₁` of `lemmaredplanktube`) is supplied only
existentially, so there is no term to put on the left of a `· ≤ δ^{-η}`. Their thresholds are
therefore *definitions by choice*, and the blueprint prescribes that they be carried as
indices of `Kakeya.VeryNotSticky.CaseScale` rather than as terms; this structure is that
bundle of indices.

It is declared beside `Kakeya.VeryNotSticky.CaseParams` and not beside
`Kakeya.VeryNotSticky.CaseScale`, whose eighth, ninth and eleventh clauses read its fields,
because its first consumer is `Kakeya.VeryNotSticky.exists_aScaleData` in the goal-reduction
layer, which is upstream of the file declaring `CaseScale`. Like `CaseParams` it mentions no
data beyond quantities fixed before `δ`, so the earlier point costs nothing and avoids an
import edge from the configuration layer to the goal layer.

What matters mathematically is that all three depend only on data fixed *before* `δ` — on
`ν, β, ζ, η, C₀, D₀` for `aScale`, on `β, ζ, η, exscal, ϱ` for `typical`, and on
`η, exscal, ϱ` for `fill` — and in particular that none of them mentions the thin-case
comparison constant `C` or the biased-factoring constant `Cbias`, the two constants of this
development produced after `δ`. That is what lets the clauses reading them be arranged by
shrinking `δ`, and it is why they may be threaded from blueprint `lem:ml2casesplit` at no cost
to any branch.

**The first threshold carries its defining property; the other two do not yet.** Blueprint
`def:ml2aScaleDataThreshold` fixes `δ_{lem:ml2aScaleData}` by the implication

`δ ≤ δ_{lem:ml2aScaleData}(ν, β, ζ, η, C₀, D₀) → C_⋆(ν, C₀, D₀)² ≤ δ^{-η}`,

with `C_⋆ = max(C_{lem:ml2aScaleBall}, C_{lem:ml2aScaleVolume})` the accumulated comparison
constant that the proof of blueprint `lem:ml2aScaleData` exhibits. That implication is the
field `aScale_absorb`, and the constant it absorbs is the companion field `aScaleConst`.

Carrying the absorbed constant *on this bundle* is forced, and the reason is worth recording.
The blueprint's threshold is a function of `ν, β, ζ, η, C₀, D₀`, of which only `ν` is an
argument of `aScale`; and the property may not be quantified over the remaining data instead,
because at a fixed threshold value it is **false** for large `C₀`, `D₀` and for small `η`.
Nor may `C_⋆` be named by a formula here: `Kakeya.aScaleBallConstant` and
`Kakeya.aScaleVolumeConstant` are declared downstream of this file, and the first of them
reads a constant that blueprint `def:leApprox` supplies only existentially. So the bundle
names the constant it absorbs, at each gain `ν` and each exponent `η`, and asserts the
absorption at that pair. The clause `cfg.δ ≤ thr.aScale ν` then carries information: it forces
`thr.aScaleConst ν cfg.η ≤ cfg.δ^{-cfg.η/2}`, which is exactly what
`Kakeya.VeryNotSticky.exists_aScaleData` spends to produce its conjunct `C ^ 2 ≤ δ^{-η}`.

What is *not* secured by this is the link between `aScaleConst` and the constants of the
scale-`r` layer: no field says that `C_⋆` is at most `thr.aScaleConst ν cfg.η`, and none can,
since `aScale` does not see `C₀` and `D₀` and the quantified form is false. That half of
blueprint `def:ml2aScaleDataThreshold` is carried instead by the configuration, as the field
`Kakeya.VeryNotSticky.aScaleData_absorb`, which absorbs `Kakeya.aScaleDataConstant C₀ D₀` at
the configuration's own uniformity constants; see the docstring of that field for why it
cannot live here. The two clauses are complementary and both are spent:
`Kakeya.VeryNotSticky.exists_aScaleData` produces the maximum of the two absorbed constants
and reads the conjunct `C ^ 2 ≤ δ^{-η}` off both absorptions.

The remaining two fields, `typical` and `fill`, still carry no defining property, for the
reason the blueprint gives: their consumers, the Lean forms of blueprint `lem:ml2typicalangle`
and `lem:ml2transverseFill`, do not assert the sub-polynomial bounds those clauses pay
for, so there is as yet no constant for them to absorb.

Of the three fields only `aScale` is consumed by a declaration today —
`Kakeya.VeryNotSticky.exists_aScaleData` takes it as `hthr`, and
`Kakeya.VeryNotSticky.CaseScale.aScaleData_threshold` discharges that hypothesis in the
transverse chain. The other two are carried by the ninth and eleventh clauses of `CaseScale`
and are not used by these estimates: the Lean forms of blueprint `lem:ml2typicalangle` and
`lem:ml2transverseFill` do not assert the sub-polynomial bounds those clauses pay for. They
are threaded ahead of their consumers deliberately, so that adding the bounds is a change to
those two statements alone and not to every declaration between them and the case split.

The one property that *is* recorded is membership in `(0, 1]`, which the three blueprint
definitions all assert. It is not idle: without `0 < ·` the clauses `cfg.δ ≤ thr.aScale ν`
and its two siblings would be *unsatisfiable* at `thr.aScale ν = 0`, since `cfg.hδ` gives
`0 < cfg.δ`, and a bundle containing an unsatisfiable clause makes every leaf consuming it
vacuous — the opposite failure from the trivial satisfiability discussed above, and a worse
one. The upper bound `· ≤ 1` records that a threshold never licenses `δ > 1`, which
`cfg.hδ1` already forbids; it is carried so that the Lean structure says exactly what
`(0, 1]` says in the blueprint. -/
structure ScaleThresholds where
  /-- `δ_{lem:ml2aScaleData}(ν, β, ζ, η, C₀, D₀)` of blueprint `def:ml2aScaleDataThreshold`,
  as a function of the gain `ν` at which blueprint `lem:ml2aScaleData` is invoked. It is a
  function of `ν` because the case split arranges Configuration `hyp:ml2scale` at the two
  gains `ν_{lem:ml2thick}` and `ν_{lem:ml2transverse}`, both of which are fixed before `δ`. -/
  aScale : ℝ → NNReal
  /-- `δ_{lem:ml2aScaleData}(ν, …) ∈ (0, 1]`, at every gain. -/
  aScale_mem : ∀ ν : ℝ, aScale ν ∈ Set.Ioc (0 : NNReal) 1
  /-- `C_⋆(ν, η)` of blueprint `def:ml2aScaleDataThreshold`: the accumulated comparison
  constant of the scale-`r` layer at the gain `ν`, which the threshold `aScale ν` is chosen to
  absorb at the exponent `η`. In the blueprint it is
  `max(C_{lem:ml2aScaleBall}(ν), C_{lem:ml2aScaleVolume}(C₀, D₀))`; it is carried as a field
  because neither constant can be named at this point of the development, and because the
  threshold may not be quantified over the data `C₀, D₀, η` they depend on without becoming
  false. The exponent `η` is an argument for the same reason: at a fixed threshold the
  absorption fails as `η ↓ 0`. -/
  aScaleConst : ℝ → ℝ → NNReal
  /-- `1 ≤ C_⋆(ν, η)`: the absorbed constant is a comparison constant. -/
  one_le_aScaleConst : ∀ ν η : ℝ, 1 ≤ aScaleConst ν η
  /-- **The defining property of `aScale`** (blueprint `def:ml2aScaleDataThreshold`): below
  the threshold at the gain `ν`, the accumulated constant of the layer fits inside
  `δ^{-η/2}`, i.e. `C_⋆(ν, η) ^ 2 ≤ δ^{-η}`. This is what
  `Kakeya.VeryNotSticky.exists_aScaleData` spends to produce its conjunct `C ^ 2 ≤ δ^{-η}`,
  and it is what makes the clause `cfg.δ ≤ thr.aScale ν` carry information rather than being
  satisfied by any threshold whatsoever. -/
  aScale_absorb : ∀ ν η : ℝ, 0 < η → ∀ δ : NNReal, 0 < δ → δ ≤ aScale ν →
    (aScaleConst ν η : ENNReal) ^ 2 ≤ (δ : ENNReal) ^ (-η)
  /-- `δ_{lem:ml2typicalangle}(β, ζ, η, exscal, ϱ)` of blueprint
  `def:ml2typicalangleThreshold`. -/
  typical : NNReal
  /-- `δ_{lem:ml2typicalangle}(β, ζ, η, exscal, ϱ) ∈ (0, 1]`. -/
  typical_mem : typical ∈ Set.Ioc (0 : NNReal) 1
  /-- `δ_{lem:ml2transverseFill}(η, exscal, ϱ)` of blueprint
  `def:ml2transverseFillThreshold`, the threshold that converts the smallness hypothesis of
  `lemmaredplanktube` at the rescaled scale `δ/r₁` into one at `δ`. -/
  fill : NNReal
  /-- `δ_{lem:ml2transverseFill}(η, exscal, ϱ) ∈ (0, 1]`. -/
  fill_mem : fill ∈ Set.Ioc (0 : NNReal) 1

/-- **The threshold bundle is satisfiable.**

Every hypothesis of the shape `cfg.δ ≤ thr.aScale ν` is asserted under a `ScaleThresholds`,
so a bundle with an unsatisfiable field would make every declaration reading it vacuous. The
witness takes all three thresholds equal to `1` and absorbs the constant `1`, for which
`aScale_absorb` reads `1 ≤ δ^{-η}` and holds because `0 < δ ≤ 1` and `η > 0`. It is of course
not the bundle the blueprint intends — that one absorbs the true constants of the scale-`r`
layer — but it certifies that the fields are consistent. -/
theorem nonempty_scaleThresholds : Nonempty ScaleThresholds := by
  let t : ScaleThresholds :=
    { aScale := fun _ => 1,
      aScale_mem := by
        intro ν
        norm_num,
      aScaleConst := fun _ _ => 1,
      one_le_aScaleConst := by
        intro ν η
        rfl,
      aScale_absorb := by
        intro ν η hη δ hδ hδa
        have hd0 : (0 : ENNReal) < (δ : ENNReal) := ENNReal.coe_pos.mpr hδ
        have hd1 : (δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr hδa
        have hneg : -η < 0 := neg_lt_zero.mpr hη
        have hone : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-η) :=
          ENNReal.one_le_rpow_of_pos_of_le_one_of_neg hd0 hd1 hneg
        simpa using hone,
      typical := 1,
      typical_mem := by
        norm_num,
      fill := 1,
      fill_mem := by
        norm_num }
  exact ⟨t⟩

open MeasureTheory ShadedBody in
/-- The common goal of every case: the multiplicity bound `μ(T, Y) ≤ δ^ν |T|^β`
(blueprint `eqgoalmuT`), which is the conclusion of `lemmain2vns` for a positive
gain `ν`. Each case establishes this (directly, or via one of the equivalent
density/union forms `eqgoaldens`/`eqgoalUT`). -/
def goalMult (cfg : VeryNotSticky) (ν : ℝ) : Prop :=
  multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤
    (cfg.δ : ENNReal) ^ ν * (cfg.s.card : ENNReal) ^ cfg.β

open MeasureTheory ShadedBody in
/-- The *volume form* of the goal (blueprint Definition `def:ml2goalUnion`, equation
`eqgoalUT`): `|U(T, Y)| ≥ δ^{-ν} |T| |𝕋|^{1-β}`.

The Lean form clears the division and the negative exponents, so that it is a statement about
`[0, ∞]`-valued quantities needing no side conditions:

`∑_{T ∈ 𝕋} |T| ≤ δ^ν |U(T, Y)| |𝕋|^β`.

Since the tubes have the common volume `|T|`, the left-hand side is `|T| |𝕋|`, and for
`|U(T,Y)|` and `|𝕋|` positive and finite the displayed inequality is equivalent to
`eqgoalUT`. Writing it as the sum rather than as `|T| |𝕋|` also makes it independent of a
choice of reference tube.

Deliberately no comparison constant appears: the `⪆` of `eqgoalUT` is absorbed into the gain
`ν`, exactly as the `⪅` of `eqgoalmuT` already is in `Kakeya.VeryNotSticky.goalMult`. This is
what makes the conversion `Kakeya.VeryNotSticky.goalMult_of_goalUnion` /
`Kakeya.VeryNotSticky.goalUnion_of_goalMult` an exact equivalence, with no constant to carry
from one currency to the other. -/
def goalUnion (cfg : VeryNotSticky) (ν : ℝ) : Prop :=
  ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier ≤
    (cfg.δ : ENNReal) ^ ν * volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) *
      (cfg.s.card : ENNReal) ^ cfg.β

open MeasureTheory ShadedBody in
/-- The *density form* of the goal (blueprint Definition `def:ml2goalDensity`, equation
`eqgoaldens`), at a ball of the variable radius `r`: there is a ball `B_r` of radius `r` with

`|U(T, Y) ∩ B_r| / |B_r| ≥ C δ^{-2ν} (δ/r)^{2β}`,

rendered without division or negative exponents as

`C δ^{2β} |B_r| ≤ δ^{2ν} |U(T, Y) ∩ B_r| r^{2β}`.

The radius is a parameter rather than the fixed scale `cfg.a`. The two branches that produce
this currency produce it at different scales: the thick case
(`Kakeya.VeryNotSticky.goalDensity_of_denseInBody`) at `r = cfg.a` exactly, the transverse
case (`Kakeya.VeryNotSticky.transverseDensity`) at `r = θ b ≥ δ^{-τ'} a`, and the two are not
interchangeable — the requirement at radius `a` carries the factor `(δ/a)^{2β}`, which the
transverse branch cannot make small since it bounds `a` only by `a ≥ δ`. Consumers pair this
predicate with `Kakeya.VeryNotSticky.AScaleData` *at the same radius*, under `cfg.a ≤ r`.

Unlike the other two currencies this one *does* carry a comparison constant `C`, and it
carries it as a parameter rather than as a defined quantity: the `⪆` of `eqgoaldens`
ultimately comes from `Kakeya.LEApprox`, which supplies its constants only existentially, so
there is no formula to substitute. The predicate is antitone in `C` — a larger constant is a
stronger requirement — and the value at which
`Kakeya.VeryNotSticky.goalUnion_of_goalDensity` consumes it is `C^2` for the `C` produced by
`Kakeya.VeryNotSticky.exists_aScaleData`. That squaring is what makes the reduction to the
volume form exact rather than valid only below a further scale threshold: the two losses of
the reduction are paid for by the hypothesis.

The gain is doubled, `δ^{-2ν}` rather than `δ^{-ν}`, because the passage to the volume form
spends the two factors `δ^{ν/9}` of `Kakeya.VeryNotSticky.AScaleData` and must still leave a
gain `ν`; doubling leaves the surplus `2ν - 2ν/9 = 16ν/9 ≥ ν`.

No condition is placed on the centre of the ball: the estimate is required of *some*
`r`-ball. The cost of moving to a ball centred at a shaded point, which is what
`eqlowerBoundTTScaleAAndABall` needs, is charged to `AScaleData` (blueprint
`lem:ml2ballRecentre`). -/
def goalDensity (cfg : VeryNotSticky) (C : ENNReal) (r : NNReal) (ν : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℝ (Fin 3),
    C * (cfg.δ : ENNReal) ^ (2 * cfg.β) * volume (Metric.ball x (r : ℝ)) ≤
      (cfg.δ : ENNReal) ^ (2 * ν) *
        volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ Metric.ball x (r : ℝ)) *
        (r : ENNReal) ^ (2 * cfg.β)

/-! ### The exponent budgets of the tangential case

Three purely arithmetic checks against the single budget
`Kakeya.VeryNotSticky.parameterSeparationConstant`, `C_sep = 2^20`, which
`Kakeya.VeryNotSticky.CaseParams.tangential` constrains by
`C_sep (ϱ + τ') < exscal β ζ / 2`. They mention no geometry, so they live here beside
`CaseParams` rather than in the tangential file, where their consumers are.
-/

/-- **The exponent budget of the slab decomposition** (blueprint
`lem:ml2tangentialSlabDecompExponent`).

The three powers of `δ` that the multiplicity clause of
`Kakeya.VeryNotSticky.tangentialSlabDecomp` spends — the `δ^{-2τ'}` of the fibre count, the
`δ^{-τ'}` paying for the admissible constant `Cμ`, and the `δ^{-2η}` of the passage to the
`c`-refinement — fit inside the quarter budget `C_sep τ'/4 = 2^18 τ'`.

The one genuine relation between the parameters used is
`CaseParams.transverse`, `3τ + 87η < τ' β`; together with `hτ : 0 < τ` it gives `87η < τ' β`,
and `β ≤ 1` with `τ' > 0` converts this into `12η < τ'` once `0 ≤ η` (for `η < 0` the two
conclusions are immediate from `0 < τ'`). Everything else is the generosity of
`C_sep/4 = 2^18 ≥ 4`. Neither `CaseParams.densityBias` nor `CaseParams.slabDensity` would do,
since neither mentions `τ'`. -/
theorem tangentialSlabDecompExponent {β ζ exscal ϱ η τ τ' : ℝ}
    (params : CaseParams β ζ exscal ϱ η τ τ') (hβ1 : β ≤ 1) :
    7 * η < τ' ∧ 3 * τ' + 2 * η ≤ parameterSeparationConstant * τ' / 4 := by
  have hτ'pos : 0 < τ' := lt_trans params.hτ params.hτ'
  -- `CaseParams.transverse` with `0 < τ` gives `87η < τ' β`, and `β ≤ 1` with `0 < τ'`
  -- converts this into `12η < τ'` when `0 ≤ η`; for `η < 0` it is immediate.
  have h12 : 12 * η < τ' := by
    rcases le_or_gt 0 η with hη | hη
    · have h87β : 87 * η < τ' * β := by
        nlinarith [params.transverse, params.hτ]
      have hτ'βle : τ' * β ≤ τ' := by
        nlinarith [hτ'pos, hβ1]
      nlinarith [h87β, hτ'βle, hη]
    · nlinarith [hτ'pos, hη]
  constructor
  · -- `7η < τ'`: either `0 ≤ η` (so `7η ≤ 12η < τ'`) or `η < 0` (so `7η < 0 < τ'`).
    nlinarith [h12, hτ'pos]
  · -- `3τ' + 2η ≤ C_sep τ'/4 = 2^18 τ'`, from `12η < τ'` and `0 < τ'`.
    unfold parameterSeparationConstant
    norm_num
    nlinarith [h12, hτ'pos]

/-- **Absorbing finitely many constants and powers into a quarter budget** (blueprint
`lem:ml2tangentialSlabMultAbsorb`).

Each multiplicative constant `C j` is disposed of by a fixed-scale threshold
`C j ≤ δ^{-ϱ}` — never by the exponent budget, since `δ` is allowed up to `1` and a factor
`δ^{-s}` with `s > 0` is `≥ 1` but does not dominate a given constant — and only the resulting
powers of `δ^{-ϱ}` are charged to the quarter budget `C_sep ϱ/4 = 2^18 ϱ`. The bound
`k + m ≤ 2^17` is what makes "finitely many" precise.

Stated in `ℝ≥0∞`, the type of `ShadedBody.multiplicity`, rather than in the blueprint's
positive reals: no positivity of `X` or `R` is then needed, and the conclusion is directly
consumable by `Kakeya.VeryNotSticky.tangentialSlabMult`, which applies it with `k = 2` and
`m = 4`. -/
theorem tangentialSlabMultAbsorb {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ϱ : ℝ} (hϱ : 0 < ϱ)
    {k m : ℕ} (hkm : k + m ≤ 2 ^ 17) (C : Fin k → NNReal)
    (hC : ∀ j, (C j : ENNReal) ≤ (δ : ENNReal) ^ (-ϱ)) {X R : ENNReal}
    (hX : X ≤ (∏ j, (C j : ENNReal)) * (δ : ENNReal) ^ (-((m : ℝ) * ϱ)) * R) :
    X ≤ (δ : ENNReal) ^ (-(parameterSeparationConstant * ϱ / 4)) * R := by
  let d : ENNReal := (δ : ENNReal)
  have hd0 : d ≠ 0 := (ENNReal.coe_pos.mpr hδ).ne'
  have hd_top : d ≠ ⊤ := ENNReal.coe_ne_top
  have hd_le_one : d ≤ 1 := ENNReal.coe_le_one_iff.mpr hδ1
  -- The product of the `C j` is bounded by a single power of `d`.
  have hprod : (∏ j : Fin k, d ^ (-ϱ)) = d ^ (-((k : ℝ) * ϱ)) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← ENNReal.rpow_natCast]
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  have hCprod : (∏ j : Fin k, (C j : ENNReal)) ≤ d ^ (-((k : ℝ) * ϱ)) := by
    calc
      (∏ j : Fin k, (C j : ENNReal)) ≤ ∏ j : Fin k, d ^ (-ϱ) :=
        Finset.prod_le_prod' (fun i hi => hC i)
      _ = d ^ (-((k : ℝ) * ϱ)) := hprod
  -- The exponent budget: `(k + m)ϱ ≤ 2^18 ϱ = C_sep ϱ / 4`.
  have hExp : ((k : ℝ) + (m : ℝ)) * ϱ ≤ parameterSeparationConstant * ϱ / 4 := by
    unfold parameterSeparationConstant
    have hkm_real : (k : ℝ) + (m : ℝ) ≤ (2 : ℝ) ^ 17 := by exact_mod_cast hkm
    have hkm18 : (k : ℝ) + (m : ℝ) ≤ (2 : ℝ) ^ 18 := by
      exact le_trans hkm_real (by norm_num)
    calc
      ((k : ℝ) + (m : ℝ)) * ϱ ≤ (2 : ℝ) ^ 18 * ϱ :=
        mul_le_mul_of_nonneg_right hkm18 (le_of_lt hϱ)
      _ = parameterSeparationConstant * ϱ / 4 := by
        unfold parameterSeparationConstant
        ring
  have hExpNeg : -(parameterSeparationConstant * ϱ / 4) ≤ -(((k : ℝ) + (m : ℝ)) * ϱ) := by
    nlinarith [hExp]
  have hpowGoal : d ^ (-(((k : ℝ) + (m : ℝ)) * ϱ)) ≤
      d ^ (-(parameterSeparationConstant * ϱ / 4)) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hd_le_one hExpNeg
  -- Combine the `δ^{kϱ}` and `δ^{mϱ}` powers (legitimate since `0 < δ ≤ 1`).
  have hAbs : d ^ (-((k : ℝ) * ϱ)) * d ^ (-((m : ℝ) * ϱ)) =
      d ^ (-(((k : ℝ) + (m : ℝ)) * ϱ)) := by
    calc
      d ^ (-((k : ℝ) * ϱ)) * d ^ (-((m : ℝ) * ϱ))
          = d ^ (-((k : ℝ) * ϱ) + -((m : ℝ) * ϱ)) :=
            (ENNReal.rpow_add (-((k : ℝ) * ϱ)) (-((m : ℝ) * ϱ)) hd0 hd_top).symm
      _ = d ^ (-(((k : ℝ) + (m : ℝ)) * ϱ)) := by
            congr 1
            ring
  have hbound2 : (∏ j : Fin k, (C j : ENNReal)) * d ^ (-((m : ℝ) * ϱ)) ≤
      d ^ (-(parameterSeparationConstant * ϱ / 4)) := by
    calc
      (∏ j : Fin k, (C j : ENNReal)) * d ^ (-((m : ℝ) * ϱ))
          ≤ d ^ (-((k : ℝ) * ϱ)) * d ^ (-((m : ℝ) * ϱ)) := mul_le_mul' hCprod le_rfl
      _ = d ^ (-(((k : ℝ) + (m : ℝ)) * ϱ)) := hAbs
      _ ≤ d ^ (-(parameterSeparationConstant * ϱ / 4)) := hpowGoal
  -- Shoot `hX` through the bound.
  calc
    X ≤ (∏ j : Fin k, (C j : ENNReal)) * d ^ (-((m : ℝ) * ϱ)) * R := by
      simpa [d] using hX
    _ ≤ d ^ (-(parameterSeparationConstant * ϱ / 4)) * R := mul_le_mul' hbound2 le_rfl

/-- **The accumulated budget of the tangential case** (blueprint `lem:ml2tangentialBudget`).

The tangential leaf spends three quarter budgets — `τ'` in
`Kakeya.VeryNotSticky.tangentialSlabDecomp`, `ϱ` in
`Kakeya.VeryNotSticky.tangentialSlabMult` and `ϱ + η` in
`Kakeya.VeryNotSticky.nonslabSplitBound` — so its accumulated exponent loss is
`L = ¼ C_sep (τ' + ϱ + (ϱ + η))`. This is at most the tangential budget
`C_sep (ϱ + τ')` of `Kakeya.VeryNotSticky.CaseParams.tangential`, which therefore leaves the
gain `ν = ½ exscal β ζ` of `Kakeya.VeryNotSticky.goalMult_of_theta_lt`.

`hη : 0 < η` is a hypothesis rather than a field of `CaseParams`, which constrains `η` only
from above; it is `cfg.hη` at every call site. With it, `CaseParams.densityBias` gives
`η < ϱ` and `CaseParams.slabBias` gives `0 < exscal`. -/
theorem tangentialAccumulatedBudget {β ζ exscal ϱ η τ τ' : ℝ}
    (params : CaseParams β ζ exscal ϱ η τ τ') (hη : 0 < η) :
    parameterSeparationConstant * (τ' + ϱ + (ϱ + η)) / 4 ≤
        parameterSeparationConstant * (ϱ + τ') ∧
      exscal * β * ζ / 2 ≤
        exscal * β * ζ - parameterSeparationConstant * (τ' + ϱ + (ϱ + η)) / 4 := by
  let Csep : ℝ := parameterSeparationConstant
  have hCsep : 0 < Csep := by
    dsimp [Csep]
    unfold parameterSeparationConstant
    norm_num
  have hCsep1 : (1 : ℝ) ≤ Csep := by
    dsimp [Csep]
    unfold parameterSeparationConstant
    norm_num
  -- Positivity of `τ'` and `ϱ`.
  have hτ'pos : 0 < τ' := lt_trans params.hτ params.hτ'
  have hϱpos : 0 < ϱ := by
    have hpos : 0 < Csep * η := by positivity
    exact lt_of_lt_of_le hpos (le_of_lt params.densityBias)
  -- `η < ϱ` from `1 ≤ C_sep`, `0 < η` and `densityBias`.
  have hηϱ : η < ϱ := by
    have hle : η ≤ Csep * η := by nlinarith [hCsep1, hη]
    exact lt_of_le_of_lt hle params.densityBias
  -- First conjunct: `C_sep (τ' + ϱ + (ϱ + η)) / 4 ≤ C_sep (ϱ + τ')`.
  have h1 : Csep * (τ' + ϱ + (ϱ + η)) / 4 ≤ Csep * (ϱ + τ') := by
    have hAux : τ' + 2 * ϱ + η ≤ 4 * ϱ + 4 * τ' := by
      nlinarith [hηϱ, hϱpos, hτ'pos]
    nlinarith [hCsep, hAux]
  -- Second conjunct: chain the first conjunct with the tangential budget.
  have h2 : Csep * (τ' + ϱ + (ϱ + η)) / 4 ≤ exscal * β * ζ / 2 :=
    le_trans h1 (le_of_lt params.tangential)
  constructor
  · exact h1
  · nlinarith [h2]

/-- **The exponent budget of the small-multiplicity leaf** (blueprint
`lem:ml2smallmultBudget`).

The inequality the small-multiplicity leaf
`Kakeya.VeryNotSticky.goalMult_of_multBodies_le` actually spends. Its loss is the `η` of the
multiplicity hypothesis plus the quarter budget `C_sep(ϱ+η)/4` that
`Kakeya.VeryNotSticky.nonslabSplitBound` produces, and the gain it must leave is `exscal·β`
out of `exscal(2+ζ)β`.

**This is not `CaseParams.smallMultiplicity`.** That field reads `2η + ϱ < exscal(1+ζ)β` and
carries no factor `C_sep`, so it does not dominate `C_sep(ϱ+η)/4 = 2^18(ϱ+η)`; nor does any
combination of `densityBias`, `slabBias` and `slab`, all of which leave `β` free to be small.
The budget is supplied instead by `CaseParams.tangential`, exactly as for the tangential leaf,
whose accumulated loss `Kakeya.VeryNotSticky.tangentialAccumulatedBudget` already contains this
same quarter budget from `nonslabSplitBound`.

The route is: `CaseParams.transverse` with `β ≤ 1` and `CaseParams.hτ` gives `12η < τ'`, hence
`η < τ'`; `hη` gives `0 < ϱ` through `densityBias`; `C_sep/4 = 2^18 ≥ 1` then yields
`η + C_sep(ϱ+η)/4 ≤ C_sep(ϱ+τ')/2`, and `CaseParams.tangential` closes it against
`exscal(1+ζ)β` since `ζ/4 ≤ 1+ζ`.

`hη` is an explicit hypothesis rather than a field of `CaseParams`, which bounds `η` only from
above, exactly as for `Kakeya.VeryNotSticky.tangentialAccumulatedBudget`; it is `cfg.hη` at the
call site. -/
theorem smallMultiplicityBudget {β ζ exscal ϱ η τ τ' : ℝ}
    (params : CaseParams β ζ exscal ϱ η τ τ') (hβ : 0 < β) (hβ1 : β ≤ 1) (hη : 0 < η) :
    16 * η + parameterSeparationConstant * (ϱ + η) / 4 ≤ exscal * (1 + ζ) * β := by
  let Csep : ℝ := parameterSeparationConstant
  have hCsep : 0 < Csep := by
    dsimp [Csep]
    unfold parameterSeparationConstant
    norm_num
  have hCsep16 : (1 : ℝ) ≤ Csep / 4 := by
    dsimp [Csep]
    unfold parameterSeparationConstant
    norm_num
  have hC4pos : 0 < Csep / 4 := by positivity
  -- `CaseParams.transverse` with `β ≤ 1` and `0 < τ` gives `87η < τ'`, hence `16η ≤ τ'`
  --.
  have hτ'pos : 0 < τ' := lt_trans params.hτ params.hτ'
  have h87 : 87 * η < τ' * β := by
    nlinarith [params.transverse, params.hτ]
  have hτ'βle : τ' * β ≤ τ' := by
    nlinarith [hτ'pos, hβ1]
  have h87' : 87 * η < τ' := lt_of_lt_of_le h87 hτ'βle
  have h16leτ' : 16 * η ≤ τ' := by
    nlinarith [h87', hη]
  have hηltτ' : η < τ' := by
    nlinarith [h87', hη]
  have hηleτ' : η ≤ τ' := le_of_lt hηltτ'
  -- Positivity of `ϱ` and `exscal` from `densityBias` and `slabBias`.
  have hϱpos : 0 < ϱ := by
    have hpos : 0 < Csep * η := by positivity
    exact lt_of_lt_of_le hpos (le_of_lt params.densityBias)
  have hexscalpos : 0 < exscal := by
    have hpos : 0 < Csep * ϱ := by positivity
    exact lt_of_lt_of_le hpos (le_of_lt params.slabBias)
  -- The tangential budget forces `0 < ζ`.
  have hζpos : 0 < ζ := by
    have hpos : 0 < Csep * (ϱ + τ') := by positivity
    have hb : 0 < exscal * β * ζ / 2 := lt_of_lt_of_le hpos (le_of_lt params.tangential)
    have ha : 0 < exscal * β := mul_pos hexscalpos hβ
    nlinarith [hb, ha]
  -- The chain: `16η + C_sep(ϱ+η)/4 ≤ C_sep(ϱ+τ')/2 < exscal·β·ζ/4 ≤ exscal(1+ζ)β`.
  have hmid : Csep * (ϱ + τ') / 2 < exscal * β * ζ / 4 := by
    nlinarith [params.tangential]
  have hleft : exscal * β * ζ / 4 ≤ exscal * (1 + ζ) * β := by
    have hle : ζ / 4 ≤ 1 + ζ := by nlinarith [hζpos]
    have hqb : 0 ≤ exscal * β := mul_nonneg (le_of_lt hexscalpos) (le_of_lt hβ)
    have hstep : exscal * β * ζ / 4 ≤ exscal * β * (1 + ζ) := by
      simpa [show exscal * β * ζ / 4 = exscal * β * (ζ / 4) by ring] using
        mul_le_mul_of_nonneg_left hle hqb
    simpa [mul_assoc, mul_comm, mul_left_comm] using hstep
  have hfinal : Csep * (ϱ + τ') / 2 ≤ exscal * (1 + ζ) * β :=
    le_of_lt (lt_of_lt_of_le hmid hleft)
  have h1 : 16 * η + Csep * (ϱ + η) / 4 ≤ τ' + Csep * (ϱ + τ') / 4 := by
    nlinarith [hηleτ', h16leτ', hC4pos]
  have h2 : τ' + Csep * (ϱ + τ') / 4 ≤ Csep * τ' / 4 + Csep * (ϱ + τ') / 4 := by
    nlinarith [hτ'pos, hCsep16]
  have h3 : Csep * τ' / 4 + Csep * (ϱ + τ') / 4 ≤ Csep * (ϱ + τ') / 2 := by
    nlinarith [hCsep, hϱpos]
  exact le_trans (le_trans (le_trans h1 h2) h3) hfinal

end VeryNotSticky

end Kakeya
