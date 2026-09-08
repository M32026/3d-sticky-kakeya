/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Asymptotics
public import Kakeya.Frostman
public import Kakeya.Shading
public import Kakeya.Tube.Dilate
public import Kakeya.Pigeonhole

/-!
# Main Lemma 1, Case (ii): counts, shade mass, and fullness

Blueprint `lem:ml1bootCaseTwoInputMassFromCard` and `lem:ml1bootCaseTwoInputFullness`(b).

`Kakeya.ml1Boot.IsCaseTwoInput` carries two shading clauses alongside its cardinality clause —
the shade-mass retention `refine_mass` and the banded shade density `band` — because the
cardinality clause alone says nothing about the shading and the Case (ii) conclusion
`Kakeya.ml1Boot.IsCaseTwoData.refine_fullness` is a statement about shade mass; blueprint
`note:ml1bootCaseIIRefineFullnessGap` is the counterexample that forced them.

This file holds the two shading facts that make that arrangement work, both of which are about a
family of shaded `δ`-tubes and *neither* of which mentions the Case (ii) bundle:

* `Kakeya.ml1Boot.isCRefinement_of_card_le_of_banded` is the **supplier** side: for a banded
  shading, a cardinality share *is* a shade-mass share, up to the factor `4` the band costs.  It
  is why `refine_mass` is not a new obligation on the suppliers of the bundle, which are unshaded
  and price counts only.
* `Kakeya.ml1Boot.fullness_le_of_isCRefinement` is the **consumer** side: fullness descends along
  an arbitrary `c`-refinement of a `δ`-tube family, with the same constant `c`.  It is stated at
  an arbitrary link `u ⊆ s` rather than at `s' ⊆ s` because the consumer applies it *once*, to the
  composed chain `s₀ ⊆ s₂ ⊆ s' ⊆ s`: fullness at an intermediate link does not compose, whereas
  the refinement does (`ShadedBody.IsCRefinement.trans`).

Both rest on the one geometric input that all `δ`-tubes have a common positive volume, which is
what turns a ratio of counts into a ratio of masses and back.
-/

@[expose] public section

open MeasureTheory

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **A cardinality share is a shade-mass share, for a banded shading** (blueprint
`lem:ml1bootCaseTwoInputMassFromCard`).

Let `(𝕋, Y) = ((T i, Y i))_{i ∈ s}` be a nonempty family of shaded `δ`-tubes whose shade
densities are banded, `λ_* |T i| ≤ |Y i| ≤ 2 λ_* |T i|` for a single `λ_* > 0` — that is, the
field `Kakeya.ml1Boot.IsCaseTwoInput.band` — and let `s' ⊆ s` be nonempty with
`|s| ≤ δ ^ (-ε') |s'|`, the field `Kakeya.ml1Boot.IsCaseTwoInput.card_le`.  Then `(𝕋|_{s'}, Y)` is
a `δ ^ ε' / 4`-refinement of `(𝕋, Y)`, and hence — as soon as `δ ^ ε' ≤ 1 / 4`, which holds for
all small `δ` — a `δ ^ (2 ε')`-refinement.

So a supplier meeting the cardinality clause at accuracy `ε' / 2` together with the banding
clause meets the shade-mass clause `Kakeya.ml1Boot.IsCaseTwoInput.refine_mass` at accuracy `ε'`,
and that clause is not an obligation any supplier has to discharge separately.  This is the whole
of the supplier-side argument of blueprint `note:ml1bootCaseIIRefineFullnessGap`.

All `δ`-tubes have one common volume `|T| > 0`, so the banding hypothesis is that of
`ShadedBody.card_le_iff_isCRefinement_of_comparable` at `Λ = 2` and `μ₀ = λ_*`, whose second half
converts the count share into the mass share; the factor `Λ ⁻² = 1 / 4` is what the band costs and
is not claimed optimal.  The positivity `0 < δ` is needed for `|T| ≠ 0`, without which every
family is trivially banded at every `λ_*` and the conclusion fails.  The upper bound `δ ≤ 1` is
what makes `κ = δ ^ ε' ≤ 1`, the hypothesis of the refinement lemma. -/
theorem isCRefinement_of_card_le_of_banded {ι : Type*} {δ : NNReal} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {ε' : ℝ} (hε' : 0 < ε') {s s' : Finset ι} (T : ι → ShadedTube δ E)
    {lam : NNReal} (hlam : 0 < lam)
    (hband : ∀ i ∈ s, (lam : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ 2 * (lam : ENNReal) * volume (T i).carrier)
    (hs : s.Nonempty) (hsub : s' ⊆ s) (hs' : s'.Nonempty)
    (hcard : (s.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s'.card : ℝ)) :
    ShadedBody.IsCRefinement s' (fun i => (T i).toShadedBody) s
        (fun i => (T i).toShadedBody) (⟨(δ : ℝ) ^ ε', by positivity⟩ / 4) ∧
      ((δ : ℝ) ^ ε' ≤ 1 / 4 →
        ShadedBody.IsCRefinement s' (fun i => (T i).toShadedBody) s
          (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hs
  let κ : NNReal := ⟨(δ : ℝ) ^ ε', by positivity⟩
  let V : ι → ShadedBody E := fun i => (T i).toShadedBody
  let v : ENNReal := volume (T i₀).carrier
  have hδ_pos : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := le_of_lt hδ_pos
  have hδle1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hε0 : (0 : ℝ) ≤ ε' := le_of_lt hε'
  have hvolT : ∀ i ∈ s, volume (T i).carrier = v := by
    intro i hi
    simpa [v] using (Tube.volume_carrier_eq_volume_carrier (T i).toTube (T i₀).toTube)
  have hvol : ∀ i ∈ s, volume (V i).carrier = v := by
    intro i hi
    simpa [V] using hvolT i hi
  have hv : v ≠ 0 := by
    have hpos : 0 < volume (T i₀).carrier :=
      (Tube.volume_pos_and_lt_top hδ hδ1 (T i₀).toTube).1
    simpa [v] using ne_of_gt hpos
  have hlam0 : (lam : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hlam)
  have hlam_top : (lam : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hlow : ∀ i ∈ s, ((2 : NNReal) : ENNReal)⁻¹ * (lam : ENNReal) * v ≤ volume (V i).shade := by
    intro i hi
    have h2inv : (((2 : NNReal) : ENNReal)⁻¹) ≤ 1 := by norm_num
    calc
      ((2 : NNReal) : ENNReal)⁻¹ * (lam : ENNReal) * v
          ≤ (lam : ENNReal) * v := by
            calc
              ((2 : NNReal) : ENNReal)⁻¹ * (lam : ENNReal) * v
                  = ((2 : NNReal) : ENNReal)⁻¹ * ((lam : ENNReal) * v) := by ring
              _ ≤ 1 * ((lam : ENNReal) * v) := by
                exact mul_le_mul' h2inv le_rfl
              _ = (lam : ENNReal) * v := by rw [one_mul]
      _ = (lam : ENNReal) * volume (T i).carrier := by rw [← hvolT i hi]
      _ ≤ volume (T i).shade := (hband i hi).1
      _ = volume (V i).shade := by simp [V]
  have hupp : ∀ i ∈ s, volume (V i).shade ≤ (2 : ENNReal) * (lam : ENNReal) * v := by
    intro i hi
    calc
      volume (V i).shade = volume (T i).shade := by simp [V]
      _ ≤ 2 * (lam : ENNReal) * volume (T i).carrier := (hband i hi).2
      _ = 2 * (lam : ENNReal) * v := by rw [hvolT i hi]
  have hκpos : 0 < κ := by
    dsimp [κ]
    exact Real.rpow_pos_of_pos hδ_pos ε'
  have hle1 : (δ : ℝ) ^ ε' ≤ 1 := by
    have hle : (δ : ℝ) ^ ε' ≤ (1 : ℝ) ^ ε' := Real.rpow_le_rpow hδ0 hδle1 hε0
    rwa [Real.one_rpow] at hle
  have hκ1 : κ ≤ 1 := by
    dsimp [κ]
    exact_mod_cast hle1
  have hcard_r : (κ : ℝ) * (s.card : ℝ) ≤ (s'.card : ℝ) := by
    calc
      (κ : ℝ) * (s.card : ℝ) = (δ : ℝ) ^ ε' * (s.card : ℝ) := by rfl
      _ ≤ (δ : ℝ) ^ ε' * ((δ : ℝ) ^ (-ε') * (s'.card : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hcard (Real.rpow_nonneg hδ0 ε')
      _ = ((δ : ℝ) ^ ε' * (δ : ℝ) ^ (-ε')) * (s'.card : ℝ) := by ring
      _ = 1 * (s'.card : ℝ) := by
        rw [← Real.rpow_add hδ_pos, add_neg_cancel, Real.rpow_zero]
      _ = (s'.card : ℝ) := by ring
  have hκcard : κ * (s.card : NNReal) ≤ (s'.card : NNReal) := by
    exact_mod_cast hcard_r
  have hmain : ShadedBody.IsCRefinement s' V s V (κ * ((2 : NNReal) ^ 2)⁻¹) :=
    (ShadedBody.card_le_iff_isCRefinement_of_comparable (s := s) (s' := s') (V := V)
        (v := v) (μ₀ := (lam : ENNReal)) (Λ := 2) ⟨i₀, hi₀⟩ hvol hv
        (by norm_num : 1 ≤ (2 : NNReal)) hlam0 hlam_top hlow hupp hsub hs').2
      κ hκpos hκ1 hκcard
  have hcref : ShadedBody.IsCRefinement s' V s V (κ / 4) := by
    simpa [div_eq_mul_inv, show ((2 : NNReal) ^ 2) = 4 by norm_num] using hmain
  constructor
  · simpa [V, κ] using hcref
  · intro hsmall
    have hrr : (δ : ℝ) ^ (2 * ε') ≤ ((δ : ℝ) ^ ε') / 4 := by
      calc
        (δ : ℝ) ^ (2 * ε') = (δ : ℝ) ^ (ε' + ε') := by rw [show 2 * ε' = ε' + ε' by ring]
        _ = (δ : ℝ) ^ ε' * (δ : ℝ) ^ ε' := by rw [Real.rpow_add hδ_pos]
        _ ≤ (1 / 4 : ℝ) * (δ : ℝ) ^ ε' := by
          exact mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hδ0 ε')
        _ = ((δ : ℝ) ^ ε') / 4 := by ring
    let k2 : NNReal := ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
    have hcc'_nn : k2 ≤ κ / 4 := by
      dsimp [k2, κ]
      exact_mod_cast hrr
    have hcc'_enn : (k2 : ENNReal) ≤ ((κ / 4 : NNReal) : ENNReal) := by
      exact ENNReal.coe_le_coe.mpr hcc'_nn
    refine ⟨hcref.1, ?_⟩
    exact le_trans (mul_le_mul' hcc'_enn le_rfl) hcref.2

omit [Nontrivial E] in
/-- **Fullness descends along a `c`-refinement of a `δ`-tube family** (blueprint
`lem:ml1bootCaseTwoInputFullness`(b)).

If `(𝕋, Y)` is a nonempty family of shaded `δ`-tubes with `λ(𝕋, Y) > 0` and `(𝕋|_u, Y)` is a
`c`-refinement of it for some `c > 0`, then `u` is nonempty and `λ(𝕋|_u, Y) ≥ c λ(𝕋, Y)`.

Read at `c = δ ^ ε'` and `λ(𝕋, Y) ≥ δ ^ (η(γ))` this is exactly
`Kakeya.ml1Boot.IsCaseTwoData.refine_fullness`, `δ ^ (ε' + η(γ)) ≤ λ(𝕋|_u, Y)`; that is what the
clause `Kakeya.ml1Boot.IsCaseTwoInput.refine_mass` was added to supply, and it is the reason the
Case (ii) repair's fullness conclusion is no longer unsupported.

Two features of the shape.

* *The link is arbitrary.*  The bound is stated at an arbitrary `u ⊆ s` and not at the bundle's
  `s'`, because the consumer applies it once to the whole composed chain `s₀ ⊆ s₂ ⊆ s' ⊆ s`.
  Stating it only at `u = s'` would not serve: fullness at an intermediate link does not compose,
  whereas the refinement does, by `ShadedBody.IsCRefinement.trans`.  The nonemptiness half *is*
  read at the intermediate links, being just the positivity of the retained shade mass.
* *No upper bound `c ≤ 1` is assumed.*  The blueprint states the lemma for `c ∈ (0, 1]`, but the
  argument — `λ(𝕋|_u, Y) = (∑_{i ∈ u} |Y i|)/(|u| |T|) ≥ c (∑_{i ∈ s} |Y i|)/(|s| |T|)`, using
  `|u| ≤ |s|` — never uses it, and a `c`-refinement with `c > 1` and positive mass is impossible
  anyway, so the hypothesis would be vacuous where it is not free.

The subset `u ⊆ s` is not a separate hypothesis: it is the first clause of
`ShadedBody.IsRefinement` inside `href`.  Neither `0 < δ` nor `s.Nonempty` is one either: the
argument is a comparison of two `ENNReal` ratios and never needs the common tube volume to be
nonzero, while `s` is nonempty because `hfull` is, so both were dropped once the proof was
written. -/
theorem fullness_le_of_isCRefinement {ι : Type*} {δ : NNReal}
    {s u : Finset ι} (T : ι → ShadedTube δ E)
    (hfull : 0 < ShadedBody.fullness s (fun i => (T i).toShadedBody))
    {c : NNReal} (hc : 0 < c)
    (href : ShadedBody.IsCRefinement u (fun i => (T i).toShadedBody) s
      (fun i => (T i).toShadedBody) c) :
    u.Nonempty ∧
      c * ShadedBody.fullness s (fun i => (T i).toShadedBody)
        ≤ ShadedBody.fullness u (fun i => (T i).toShadedBody) := by
  let V : ι → ShadedBody E := fun i => (T i).toShadedBody
  have hu : u ⊆ s := href.1.1
  have hmass : (c : ENNReal) * (∑ i ∈ s, volume (V i).shade) ≤
      ∑ i ∈ u, volume (V i).shade := by
    simpa [V] using href.2
  have hfullENN : (0 : ENNReal) < (ShadedBody.fullness s V : ENNReal) := by
    simpa [V] using (ENNReal.coe_pos).mpr hfull
  have hAsum_pos : (0 : ENNReal) < ∑ i ∈ s, volume (V i).shade := by
    by_contra hnotpos
    have hAs : (∑ i ∈ s, volume (V i).shade) = 0 :=
      le_antisymm (not_lt.mp hnotpos) (by positivity)
    rw [ShadedBody.coe_fullness] at hfullENN
    simp [hAs] at hfullENN
  have hcmul_pos : (0 : ENNReal) < (c : ENNReal) * (∑ i ∈ s, volume (V i).shade) :=
    ENNReal.mul_pos (ne_of_gt (ENNReal.coe_pos.mpr hc)) (ne_of_gt hAsum_pos)
  have husum_pos : (0 : ENNReal) < ∑ i ∈ u, volume (V i).shade := by
    exact lt_of_lt_of_le hcmul_pos hmass
  have hu_ne : u ≠ ∅ := by
    intro huempty
    have : (∑ i ∈ u, volume (V i).shade) = 0 := by
      rw [huempty]
      simp
    exact (ne_of_gt husum_pos) this
  constructor
  · exact Finset.nonempty_iff_ne_empty.mpr hu_ne
  · rw [← ENNReal.coe_le_coe]
    rw [ENNReal.coe_mul, ShadedBody.coe_fullness, ShadedBody.coe_fullness]
    calc
      (c : ENNReal) * ShadedBody.fullness' s V
          = (c : ENNReal) * ((∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier)) := rfl
      _ = ((c : ENNReal) * ∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier) := by
          simp [div_eq_mul_inv, mul_assoc]
      _ ≤ (∑ i ∈ u, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier) := by
          exact ENNReal.div_le_div_right hmass _
      _ ≤ (∑ i ∈ u, volume (V i).shade) / (∑ i ∈ u, volume (V i).carrier) := by
          exact ENNReal.div_le_div_left (Finset.sum_le_sum_of_subset hu) _
      _ = ShadedBody.fullness' u V := rfl

omit [Nontrivial E] in
/-- **Case (ii) repair, the mass chain: the three links compose to a refinement of `(𝕋, Y)`**
(blueprint `lem:ml1bootRepairFullnessChain`).

Let `(𝕋, Y) = ((T i, Y i))_{i ∈ s}` be a family of shaded `δ`-tubes with `λ(𝕋, Y) ≥ δ ^ η`, and
let `s₀ ⊆ s₂ ⊆ s' ⊆ s` be such that each of `(𝕋|_{s'}, Y)`, `(𝕋|_{s₂}, Y)`, `(𝕋|_{s₀}, Y)` is a
`δ ^ ε'`-refinement of its predecessor.  Then `(𝕋|_{s₀}, Y)` is a `δ ^ (3 ε')`-refinement of
`(𝕋, Y)`, `s₀` is nonempty, and `λ(𝕋|_{s₀}, Y) ≥ δ ^ (3 ε' + η)`.

This is what the Case (ii) consumer reads for its fullness bullet: it is applied at `ε' / 4`, so
that the three links cost `3 ε' / 4 ≤ ε'` in total, with the middle link `s₂ ⊆ s'` itself a
composite.  The three links are kept separate — rather than the lemma being stated for a chain of
arbitrary length — because that is the shape of the repair: an outer uniformization pass, the
essential-distinctness deletion, and an inner uniformization pass.

Two applications of `ShadedBody.IsCRefinement.trans` compose the links (note its argument order:
the *inner* refinement comes first, and the constant of the composite is the product), and
`Kakeya.ml1Boot.fullness_le_of_isCRefinement` descends the fullness along the composite in one
step.  Descending link by link would not work: fullness at an intermediate link does not compose.

The blueprint additionally assumes `ε' > 0`, `η ≥ 0` and `s ≠ ∅`; none of the three is used.  The
first two are irrelevant to the arithmetic `δ ^ (3 ε') δ ^ η = δ ^ (3 ε' + η)`, which needs only
`0 < δ`, and `s ≠ ∅` follows from `hfull`, an empty family having fullness `0 / 0 = 0` while
`δ ^ η > 0`. -/
theorem repairFullnessChain {ι : Type*} {δ : NNReal} (hδ : 0 < δ) {ε' η : ℝ}
    {s s' s₂ s₀ : Finset ι} (T : ι → ShadedTube δ E)
    (hfull : (δ : ENNReal) ^ η ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody))
    (h₁ : ShadedBody.IsCRefinement s' (fun i => (T i).toShadedBody) s
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩)
    (h₂ : ShadedBody.IsCRefinement s₂ (fun i => (T i).toShadedBody) s'
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩)
    (h₃ : ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s₂
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩) :
    ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s
        (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (3 * ε'), by positivity⟩ ∧
      s₀.Nonempty ∧
      (δ : ENNReal) ^ (3 * ε' + η)
        ≤ ShadedBody.fullness s₀ (fun i => (T i).toShadedBody) := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδE : (0 : ENNReal) < (δ : ENNReal) := by
    simpa using hδ
  have hmul : (⟨(δ : ℝ) ^ ε', by positivity⟩ : NNReal) * ⟨(δ : ℝ) ^ ε', by positivity⟩
      * ⟨(δ : ℝ) ^ ε', by positivity⟩ = ⟨(δ : ℝ) ^ (3 * ε'), by positivity⟩ := by
    refine NNReal.coe_injective ?_
    change (δ : ℝ) ^ ε' * (δ : ℝ) ^ ε' * (δ : ℝ) ^ ε' = (δ : ℝ) ^ (3 * ε')
    rw [← Real.rpow_add hδR, ← Real.rpow_add hδR]
    congr 1
    ring
  have hcomp : ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (3 * ε'), by positivity⟩ := by
    rw [← hmul]
    exact h₃.trans (h₂.trans h₁)
  have hκ3pos : (0 : NNReal) < ⟨(δ : ℝ) ^ (3 * ε'), by positivity⟩ := by
    refine NNReal.coe_pos.mp ?_
    change (0 : ℝ) < (δ : ℝ) ^ (3 * ε')
    positivity
  have hfullpos : 0 < ShadedBody.fullness s (fun i => (T i).toShadedBody) :=
    ENNReal.coe_pos.mp (lt_of_lt_of_le (ENNReal.rpow_pos hδE ENNReal.coe_ne_top) hfull)
  obtain ⟨hne, hle⟩ := fullness_le_of_isCRefinement T hfullpos hκ3pos hcomp
  refine ⟨hcomp, hne, ?_⟩
  have hR : (δ : ℝ) ^ (3 * ε')
      * ((ShadedBody.fullness s (fun i => (T i).toShadedBody) : NNReal) : ℝ)
      ≤ ((ShadedBody.fullness s₀ (fun i => (T i).toShadedBody) : NNReal) : ℝ) := by
    have h := NNReal.coe_le_coe.mpr hle
    push_cast at h
    exact h
  have hleE : (δ : ENNReal) ^ (3 * ε')
      * ↑(ShadedBody.fullness s (fun i => (T i).toShadedBody))
      ≤ ↑(ShadedBody.fullness s₀ (fun i => (T i).toShadedBody)) := by
    have h := ENNReal.ofReal_le_ofReal hR
    rwa [ENNReal.ofReal_mul (by positivity), ← ennreal_coe_nnreal_rpow hδR,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal] at h
  calc (δ : ENNReal) ^ (3 * ε' + η)
      = (δ : ENNReal) ^ (3 * ε') * (δ : ENNReal) ^ η :=
        ENNReal.rpow_add _ _ (ne_of_gt hδE) ENNReal.coe_ne_top
    _ ≤ (δ : ENNReal) ^ (3 * ε')
          * ↑(ShadedBody.fullness s (fun i => (T i).toShadedBody)) :=
        mul_le_mul' le_rfl hfull
    _ ≤ ↑(ShadedBody.fullness s₀ (fun i => (T i).toShadedBody)) := hleE

/-- **Case (ii) repair, the count chain, and the Frostman bound at `B₁`** (blueprint
`lem:ml1bootRepairCountChain`).

Let `(𝕋, Y)` be a family of shaded `δ`-tubes in `B₁` whose shade densities are banded,
`λ_* |T i| ≤ |Y i| ≤ 2 λ_* |T i|` for a single `λ_* > 0` — the field
`Kakeya.ml1Boot.IsCaseTwoInput.band`, verbatim — and let `s₀ ⊆ s₂ ⊆ s' ⊆ s` with `s₀` nonempty
satisfy `|s| ≤ δ ^ (-ε') |s'|`, `(𝕋|_{s₂}, Y)` a `δ ^ ε'`-refinement of `(𝕋|_{s'}, Y)`, and
`|s₂| ≤ δ ^ (-ε') |s₀|`.  Then `|s| ≤ δ ^ (-4 ε') |s₀|` and
`C_F(𝕋|_{s₀}, B₁) ≤ δ ^ (-4 ε') C_F(𝕋, B₁)`.

*Why the middle link costs `2 ε'` and the outer two `ε'` each.*  The middle link is the
essential-distinctness deletion, and by blueprint `note:ml1bootEssDistinctParents` a selection
retains a share of *one* weight only; the mass chain
`Kakeya.ml1Boot.repairFullnessChain` having taken the shade mass, this chain gets no count bound
at that link and must buy one back.  `ShadedBody.card_le_iff_isCRefinement_of_comparable`(i) at
`Λ = 2` converts the mass share into a count share at the fixed price `Λ ² = 4`, and the side
condition `δ ^ ε' ≤ 1 / 4`, i.e. `4 ≤ δ ^ (-ε')`, absorbs that `4` into one further `ε'`.  The
total `4 ε'` is what the consumer budgets.  Blueprint `note:ml1bootCaseIIRefineCountGap` is the
record of the hole this repairs; a reader who drops the banding hypothesis as redundant breaks
this chain and not the mass one.

*Binder count.*  The signature is long because a three-link chain has three link hypotheses and
each of the two moves it prices has its own side data; there is no shared mathematical concept
to bundle them under, `band` and `card_le` already living in
`Kakeya.ml1Boot.IsCaseTwoInput` and the middle link in neither.  Only `s₀.Nonempty` is assumed of
the four index sets, the other three following along the inclusions; and the blueprint's `ε' > 0`
is not used, `δ ^ ε' ≤ 1 / 4` being all the arithmetic needs.  The blueprint leaves the scale
range of `δ` implicit; `0 < δ ≤ 1` is stated here because it is exactly what makes the common
tube volume positive, and without it the banding clause holds vacuously at every `λ_*`.

All `δ`-tubes have one common positive volume, which is what both halves rest on: it makes the
banding hypothesis that of `ShadedBody.card_le_iff_isCRefinement_of_comparable`, and it is the
`hvol` hypothesis of `ConvexSpaceBody.frostmanConstIn_subfamily_le`, applied at
`κ = δ ^ (4 ε')`. -/
theorem repairCountChain {ι : Type*} {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε' : ℝ}
    (hsmall : (δ : ℝ) ^ ε' ≤ 1 / 4) {s s' s₂ s₀ : Finset ι} (T : ι → ShadedTube δ E)
    (hs₀ : s₀.Nonempty) (hsub' : s' ⊆ s) (hsub₂ : s₂ ⊆ s') (hsub₀ : s₀ ⊆ s₂)
    (hball : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ ConvexSpaceBody.closedUnitBall)
    {lam : NNReal} (hlam : 0 < lam)
    (hband : ∀ i ∈ s, (lam : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ 2 * (lam : ENNReal) * volume (T i).carrier)
    (hcard₁ : (s.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s'.card : ℝ))
    (hmid : ShadedBody.IsCRefinement s₂ (fun i => (T i).toShadedBody) s'
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩)
    (hcard₂ : (s₂.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s₀.card : ℝ)) :
    (s.card : ℝ) ≤ (δ : ℝ) ^ (-(4 * ε')) * (s₀.card : ℝ) ∧
      ConvexSpaceBody.frostmanConstIn s₀ (fun i => (T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall
        ≤ (δ : ENNReal) ^ (-(4 * ε'))
          * ConvexSpaceBody.frostmanConstIn s (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall := by
  classical
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hs₂ : s₂.Nonempty := hs₀.mono hsub₀
  have hs' : s'.Nonempty := hs₂.mono hsub₂
  have hs : s.Nonempty := hs'.mono hsub'
  obtain ⟨i₀, hi₀⟩ := id hs'
  let v : ENNReal := volume (T i₀).carrier
  have hvolT : ∀ i ∈ s, volume (T i).carrier = v := by
    intro i _
    simpa [v] using (Tube.volume_carrier_eq_volume_carrier (T i).toTube (T i₀).toTube)
  have hv : v ≠ 0 := by
    have hvpos : 0 < volume (T i₀).carrier :=
      (Tube.volume_pos_and_lt_top hδ hδ1 (T i₀).toTube).1
    simpa [v] using ne_of_gt hvpos
  -- the middle link, converted from a mass share to a count share
  have hvol' : ∀ i ∈ s', volume ((fun i => (T i).toShadedBody) i).carrier = v := by
    intro i hi
    simpa using hvolT i (hsub' hi)
  have hlow : ∀ i ∈ s', (((2 : NNReal) : ENNReal))⁻¹ * (lam : ENNReal) * v
      ≤ volume ((fun i => (T i).toShadedBody) i).shade := by
    intro i hi
    have h2inv : (((2 : NNReal) : ENNReal))⁻¹ ≤ 1 := by norm_num
    calc (((2 : NNReal) : ENNReal))⁻¹ * (lam : ENNReal) * v
        = (((2 : NNReal) : ENNReal))⁻¹ * ((lam : ENNReal) * v) := by ring
      _ ≤ 1 * ((lam : ENNReal) * v) := mul_le_mul' h2inv le_rfl
      _ = (lam : ENNReal) * volume (T i).carrier := by
          rw [one_mul, hvolT i (hsub' hi)]
      _ ≤ volume (T i).shade := (hband i (hsub' hi)).1
  have hupp : ∀ i ∈ s', volume ((fun i => (T i).toShadedBody) i).shade
      ≤ ((2 : NNReal) : ENNReal) * (lam : ENNReal) * v := by
    intro i hi
    calc volume (T i).shade
        ≤ 2 * (lam : ENNReal) * volume (T i).carrier := (hband i (hsub' hi)).2
      _ = ((2 : NNReal) : ENNReal) * (lam : ENNReal) * v := by
          rw [hvolT i (hsub' hi)]
          norm_num
  have hpos : (0 : ℝ) < (δ : ℝ) ^ ε' := Real.rpow_pos_of_pos hδR ε'
  have hκpos : (0 : NNReal) < ⟨(δ : ℝ) ^ ε', by positivity⟩ := by
    refine NNReal.coe_pos.mp ?_
    change (0 : ℝ) < (δ : ℝ) ^ ε'
    exact hpos
  have hκ1 : (⟨(δ : ℝ) ^ ε', by positivity⟩ : NNReal) ≤ 1 := by
    refine NNReal.coe_le_coe.mp ?_
    change (δ : ℝ) ^ ε' ≤ ((1 : NNReal) : ℝ)
    rw [NNReal.coe_one]
    linarith
  have hmidcard := (ShadedBody.card_le_iff_isCRefinement_of_comparable
      (s := s') (s' := s₂) (V := fun i => (T i).toShadedBody) (v := v) (μ₀ := (lam : ENNReal))
      (Λ := 2) hs' hvol' hv (by norm_num) (ENNReal.coe_ne_zero.mpr (ne_of_gt hlam))
      ENNReal.coe_ne_top hlow hupp hsub₂ hs₂).1
    ⟨(δ : ℝ) ^ ε', by positivity⟩ hκpos hκ1 hmid
  have hne0 : (δ : ℝ) ^ ε' ≠ 0 := ne_of_gt hpos
  have hmidR : (δ : ℝ) ^ ε' * ((2 : ℝ) ^ 2)⁻¹ * (s'.card : ℝ) ≤ (s₂.card : ℝ) := by
    have h := NNReal.coe_le_coe.mpr hmidcard
    push_cast at h
    exact h
  -- `4 ≤ δ ^ (-ε')`
  have hinv4 : (4 : ℝ) ≤ ((δ : ℝ) ^ ε')⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hsmall (le_of_lt (inv_pos.mpr hpos))
    rw [inv_mul_cancel₀ (ne_of_gt hpos)] at h
    linarith
  have hnegR : (δ : ℝ) ^ (-ε') = ((δ : ℝ) ^ ε')⁻¹ := Real.rpow_neg hδR.le ε'
  have h4 : (4 : ℝ) ≤ (δ : ℝ) ^ (-ε') := by rw [hnegR]; exact hinv4
  have hnegpos : (0 : ℝ) < (δ : ℝ) ^ (-ε') := Real.rpow_pos_of_pos hδR (-ε')
  -- middle link at price `2 ε'`
  have hcardmid : (s'.card : ℝ) ≤ (δ : ℝ) ^ (-(2 * ε')) * (s₂.card : ℝ) := by
    have hsplit : (δ : ℝ) ^ (-(2 * ε')) = (δ : ℝ) ^ (-ε') * (δ : ℝ) ^ (-ε') := by
      rw [← Real.rpow_add hδR]; congr 1; ring
    have hstep : (s'.card : ℝ) ≤ 4 * (δ : ℝ) ^ (-ε') * (s₂.card : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hmidR
        (by positivity : (0 : ℝ) ≤ 4 * ((δ : ℝ) ^ ε')⁻¹)
      have hL : 4 * ((δ : ℝ) ^ ε')⁻¹ * ((δ : ℝ) ^ ε' * ((2 : ℝ) ^ 2)⁻¹ * (s'.card : ℝ))
          = (s'.card : ℝ) := by
        field_simp
        ring
      rw [hL] at hmul
      rw [hnegR]
      linarith
    calc (s'.card : ℝ) ≤ 4 * (δ : ℝ) ^ (-ε') * (s₂.card : ℝ) := hstep
      _ ≤ (δ : ℝ) ^ (-ε') * (δ : ℝ) ^ (-ε') * (s₂.card : ℝ) := by
          have hmm : (4 : ℝ) * (δ : ℝ) ^ (-ε') ≤ (δ : ℝ) ^ (-ε') * (δ : ℝ) ^ (-ε') :=
            mul_le_mul_of_nonneg_right h4 hnegpos.le
          exact mul_le_mul_of_nonneg_right hmm (by positivity)
      _ = (δ : ℝ) ^ (-(2 * ε')) * (s₂.card : ℝ) := by rw [hsplit]
  -- chain the three counts
  have hchain : (s.card : ℝ) ≤ (δ : ℝ) ^ (-(4 * ε')) * (s₀.card : ℝ) := by
    have hsplit4 : (δ : ℝ) ^ (-(4 * ε'))
        = (δ : ℝ) ^ (-ε') * ((δ : ℝ) ^ (-(2 * ε')) * (δ : ℝ) ^ (-ε')) := by
      rw [← Real.rpow_add hδR, ← Real.rpow_add hδR]; congr 1; ring
    have h2pos : (0 : ℝ) < (δ : ℝ) ^ (-(2 * ε')) := Real.rpow_pos_of_pos hδR _
    calc (s.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s'.card : ℝ) := hcard₁
      _ ≤ (δ : ℝ) ^ (-ε') * ((δ : ℝ) ^ (-(2 * ε')) * (s₂.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hcardmid hnegpos.le
      _ ≤ (δ : ℝ) ^ (-ε') * ((δ : ℝ) ^ (-(2 * ε')) * ((δ : ℝ) ^ (-ε') * (s₀.card : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hcard₂ h2pos.le) hnegpos.le
      _ = (δ : ℝ) ^ (-(4 * ε')) * (s₀.card : ℝ) := by rw [hsplit4]; ring
  refine ⟨hchain, ?_⟩
  -- the Frostman bound
  have hcardE : (δ : ENNReal) ^ (4 * ε') * (s.card : ENNReal) ≤ (s₀.card : ENNReal) := by
    have hposR : (0 : ℝ) < (δ : ℝ) ^ (4 * ε') := Real.rpow_pos_of_pos hδR _
    have hR : (δ : ℝ) ^ (4 * ε') * (s.card : ℝ) ≤ (s₀.card : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hchain hposR.le
      have hL : (δ : ℝ) ^ (4 * ε') * ((δ : ℝ) ^ (-(4 * ε')) * (s₀.card : ℝ))
          = (s₀.card : ℝ) := by
        rw [← mul_assoc, ← Real.rpow_add hδR]
        norm_num
      calc (δ : ℝ) ^ (4 * ε') * (s.card : ℝ)
          ≤ (δ : ℝ) ^ (4 * ε') * ((δ : ℝ) ^ (-(4 * ε')) * (s₀.card : ℝ)) := hmul
        _ = (s₀.card : ℝ) := hL
    have hE := ENNReal.ofReal_le_ofReal hR
    rwa [ENNReal.ofReal_mul hposR.le, ← ennreal_coe_nnreal_rpow hδR,
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast] at hE
  have hκne : ((δ : ENNReal) ^ (4 * ε')) ≠ 0 := by
    have hδE : (0 : ENNReal) < (δ : ENNReal) := by simpa using hδ
    exact ne_of_gt (ENNReal.rpow_pos hδE ENNReal.coe_ne_top)
  have hsub₀s : s₀ ⊆ s := hsub₀.trans (hsub₂.trans hsub')
  have hvolW : ∀ i ∈ s, volume ((fun i => (T i).toConvexSpaceBody) i).carrier = v := by
    intro i hi
    simpa using hvolT i hi
  have hmain := ConvexSpaceBody.frostmanConstIn_subfamily_le
    (s := s) (s' := s₀) (W := fun i => (T i).toConvexSpaceBody)
    (K := ConvexSpaceBody.closedUnitBall) (v := v) (κ := (δ : ENNReal) ^ (4 * ε'))
    hs hvolW hball hsub₀s hκne hcardE
  rwa [← ENNReal.rpow_neg] at hmain

end ml1Boot

end Kakeya
