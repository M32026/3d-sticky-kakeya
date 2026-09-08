/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupIslandRefute
public import Kakeya.ShadedUniform

/-!
# The fullness budget of the setup statement

`Kakeya.VeryNotSticky.fullness_ge` asserts the aggregate fullness of the *produced*
configuration at exactly `δ^η`, the same exponent, with no comparison constant, at which the
binder `hfull` of `Kakeya.VeryNotSticky.exists_setup_caseSideData` asserts it for the *given*
family.  This file measures what that costs, in one direction and the other.

* `Kakeya.VeryNotSticky.rpow_add_le_fullness_of_isCRefinement` and
  `Kakeya.VeryNotSticky.fullness_two_eta_of_isCRefinement`: at the exponent `2η` the field is
  **free** — it follows from the two conjuncts the target already carries, `hfull` and
  `δ^η ≤ c`, by `ShadedBody.IsCRefinement.mul_fullness_le`.  Nothing else is needed: no
  property of the construction, no geometry.
* `Kakeya.VeryNotSticky.lt_rpow_of_fullness_loss` and
  `Kakeya.VeryNotSticky.rpow_two_eta_le_of_fullness_loss`: the budget the field grants for a
  refinement's fullness loss is **exactly `1` at the exponent `η`** — any loss factor below
  `1` is fatal — and `δ^η` at the exponent `2η`.
* `Kakeya.VeryNotSticky.rpow_mul_fullness_le_of_fullness'_le`: the loss of the tree's only
  producer of the field `Kakeya.VeryNotSticky.uniform`,
  `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, in the form the budget above reads.
  That lemma's fullness clause is a `δ^{-α'}` comparison with `0 < α'` a *hypothesis of the
  lemma*, so the loss is a positive power of `δ` and cannot be zero.
* `Kakeya.VeryNotSticky.exists_uniform_refinement_fullness_two_eta`: the composition — the
  Markov step of the density-band pigeonhole followed by the shaded uniformization — delivering
  `uniform` at the dimension-only constant `ShadedTube.ssfUniformConst` **together with**
  aggregate fullness `δ^{2η}`, from the aggregate binder alone.  So the pair (`uniform`,
  `fullness_ge`) is jointly satisfiable at the repaired exponent, and (by the two budget lemmas
  above) not at the exponent as written.
* `Kakeya.VeryNotSticky.caseSideData_localDensity`: the demand side, unconditional — the side
  data forces the produced shading to be `δ^{3η}`-dense at scale `r₁` around *every* one of its
  own points, which is what a construction has to arrange by deleting the shading that is not.

Read together: the construction's mandatory steps all lose a positive power of `δ` of the
fullness, the field as written grants none, and at `δ^{2η}` it grants more than they spend.

**Not settled here, and recorded so that it is not mistaken for settled.**  The composition
above stops short of the two-sided density bracket
`Kakeya.VeryNotSticky.shading_lb`/`Kakeya.VeryNotSticky.shading_ub`.  Those come from the dyadic
band (`Kakeya.VeryNotSticky.eventually_exists_shadingBand_eta`, which already delivers them
together with the target's own conjunct `δ^η ≤ c`), and the band is a *selection of an index
subset*, under which `ShadedTube.ShadedUniformTubeSet` is not hereditary: its two lower brackets
`le_card_shadeClass` and `le_branchingN` are lower bounds on shade-class cardinalities.  Running
the band after the uniformization therefore breaks `uniform`, and running it before means the
uniformization's per-tube shade deletion — controlled only in the aggregate — breaks
`shading_lb`.  The exact missing input is a *class-dense* density pigeonhole, in the sense of
the criterion Section 8 records for the same obstruction at
`Kakeya.ml1Boot.exists_uniformFactorCore`.  This file makes no claim about it.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody

universe u

/-! ### The budget at `2η`: free from the target's own conjuncts -/

/-- **A `c`-refinement adds the exponents.**

If the given family is `δ^a`-full and the refinement constant is at least `δ^b`, the refined
family is `δ^{a+b}`-full.  This is `ShadedBody.IsCRefinement.mul_fullness_le` — a `c`-refinement
retains a `c` fraction of the fullness, because the carrier sum can only shrink — read at
powers of `δ`. -/
theorem rpow_add_le_fullness_of_isCRefinement {ι : Type*} {s s' : Finset ι}
    {V V' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {δ c : NNReal} {a b : ℝ}
    (hδ : δ ≠ 0)
    (hcar : 0 < ∑ i ∈ s, volume (V i).carrier)
    (hfull : δ ^ a ≤ ShadedBody.fullness s V)
    (hc : δ ^ b ≤ c)
    (href : ShadedBody.IsCRefinement s' V' s V c) :
    δ ^ (a + b) ≤ ShadedBody.fullness s' V' := by
  have h1 : δ ^ (a + b) = δ ^ b * δ ^ a := by
    rw [NNReal.rpow_add hδ]; ring
  rw [h1]
  exact le_trans (mul_le_mul' hc hfull)
    (ShadedBody.IsCRefinement.mul_fullness_le _ _ _ _ hcar href)

/-- **The field `Kakeya.VeryNotSticky.fullness_ge` at the exponent `2η` is free.**

Every producer of `Kakeya.VeryNotSticky.exists_setup_caseSideData` must exhibit its
configuration as a `c`-refinement of the given family with `δ^η ≤ c` — that is the target's own
conjunct — and must assume `hfull`, `δ^η ≤ λ(𝕋, Y)` — that is the target's own binder.  Those
two alone give aggregate fullness `δ^{2η}` for the refined family.

So the repair of the field recorded in the Section 9 field queue, `δ^{2η} ≤ λ(cfg)`, costs a
producer **nothing**: it is discharged by the data the producer already has, before any of the
construction is done.  At the exponent `η` as written the field instead demands a refinement
that loses *no* fullness at all; see `Kakeya.VeryNotSticky.lt_rpow_of_fullness_loss`. -/
theorem fullness_two_eta_of_isCRefinement {ι : Type*} {s s' : Finset ι}
    {V V' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {δ c : NNReal} {η : ℝ}
    (hδ : δ ≠ 0)
    (hcar : 0 < ∑ i ∈ s, volume (V i).carrier)
    (hfull : δ ^ η ≤ ShadedBody.fullness s V)
    (hc : δ ^ η ≤ c)
    (href : ShadedBody.IsCRefinement s' V' s V c) :
    δ ^ (2 * η) ≤ ShadedBody.fullness s' V' := by
  have h2 : (2 : ℝ) * η = η + η := by ring
  rw [h2]
  exact rpow_add_le_fullness_of_isCRefinement hδ hcar hfull hc href

/-! ### The budget at `η`: exactly zero -/

/-- **At the exponent `η` the field grants no loss whatever.**

If the given family is *exactly* `δ^η`-full — which the binder `hfull` permits, being an
inequality — then a refinement that retains a factor `q < 1` of the fullness fails
`Kakeya.VeryNotSticky.fullness_ge` as written.  There is no `q` strictly below `1` that the
field tolerates: its budget for the loss is the number `1`.

This is the precise sense in which the missing comparison constant of the field is fatal rather
than cosmetic.  Every pigeonholing step of the construction of Configuration `hyp:ml2setup`
loses a positive power of `δ`: the dyadic density band loses `(1 + log₂ θ^{-1})^{-1}`
(`Kakeya.VeryNotSticky.exists_shadingBand`), and the shaded uniformization loses `δ^{α'}` with
`0 < α'` (`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, whose `hα'` is a hypothesis of
the lemma, so the loss cannot be taken to be zero). -/
theorem lt_rpow_of_fullness_loss {ι : Type*} {s s' : Finset ι}
    {V V' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {δ q : NNReal} {η : ℝ}
    (hδ : 0 < δ)
    (hpar : ShadedBody.fullness s V = δ ^ η)
    (hq : q < 1)
    (hloss : ShadedBody.fullness s' V' ≤ q * ShadedBody.fullness s V) :
    ShadedBody.fullness s' V' < δ ^ η := by
  have hpos : 0 < δ ^ η := NNReal.rpow_pos hδ
  calc ShadedBody.fullness s' V' ≤ q * ShadedBody.fullness s V := hloss
    _ = q * δ ^ η := by rw [hpar]
    _ < 1 * δ ^ η := by
        exact mul_lt_mul_of_pos_right hq hpos
    _ = δ ^ η := one_mul _

/-- **At the exponent `2η` the budget for the loss is `δ^η`.**

A refinement that retains a factor `δ^ε` of the fullness, `ε ≤ η`, meets the repaired field.
Compare `Kakeya.VeryNotSticky.lt_rpow_of_fullness_loss`: the same refinement fails the field as
written for every `ε > 0`. -/
theorem rpow_two_eta_le_of_fullness_loss {ι : Type*} {s s' : Finset ι}
    {V V' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {δ : NNReal} {η ε : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : ε ≤ η)
    (hfull : δ ^ η ≤ ShadedBody.fullness s V)
    (hloss : δ ^ ε * ShadedBody.fullness s V ≤ ShadedBody.fullness s' V') :
    δ ^ (2 * η) ≤ ShadedBody.fullness s' V' := by
  have hmono : δ ^ η ≤ δ ^ ε := NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 hε
  have h2 : δ ^ (2 * η) = δ ^ η * δ ^ η := by
    rw [← NNReal.rpow_add hδ.ne']; ring_nf
  calc δ ^ (2 * η) = δ ^ η * δ ^ η := h2
    _ ≤ δ ^ ε * ShadedBody.fullness s V := mul_le_mul' hmono hfull
    _ ≤ ShadedBody.fullness s' V' := hloss

/-! ### The loss of the two mandatory steps, and the composition -/

/-- **Pointwise density gives aggregate fullness.**

The converse direction of the Markov step: a family every member of which is individually
`θ`-full is `θ`-full in the aggregate.  This is what makes the shaded uniformization's
*relative* fullness clause usable — that clause compares the new shading with the old one on
the **same** subfamily, and says nothing about how full the subfamily was to begin with. -/
theorem le_fullness_of_pointwise {ι : Type*} {s : Finset ι}
    {V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {θ : NNReal}
    (hne : ∑ i ∈ s, volume (V i).carrier ≠ 0)
    (h : ∀ i ∈ s, (θ : ENNReal) * volume (V i).carrier ≤ volume (V i).shade) :
    θ ≤ ShadedBody.fullness s V := by
  have htop : ∑ i ∈ s, volume (V i).carrier ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun i _ ↦ (V i).isCompact.measure_lt_top).ne
  rw [← ENNReal.coe_le_coe, ShadedBody.coe_fullness]
  refine (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl htop)).2 ?_
  calc (θ : ENNReal) * ∑ i ∈ s, volume (V i).carrier
      = ∑ i ∈ s, (θ : ENNReal) * volume (V i).carrier := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, volume (V i).shade := Finset.sum_le_sum h

/-- **The fullness loss of the shaded uniformization, in the budget's vocabulary.**

`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` states its fullness clause as
`λ(s', Y) ≤ δ^{-α'} λ(s', Y')`.  Cleared of the inverse power that reads: the uniformized
shading retains a `δ^{α'}` fraction of the fullness of the subfamily it was cut from.  The
hypothesis `0 < α'` of that lemma is not removable — the uniformization deletes shading — so
the retained fraction is a *positive power* of `δ`, strictly below `1`, which is exactly what
`Kakeya.VeryNotSticky.lt_rpow_of_fullness_loss` shows the field as written cannot absorb. -/
theorem rpow_mul_fullness_le_of_fullness'_le {ι : Type*} {s : Finset ι}
    {V V' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {δ : NNReal} {α : ℝ} (hδ : 0 < δ)
    (h : ShadedBody.fullness' s V
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-α)) * ShadedBody.fullness' s V') :
    δ ^ α * ShadedBody.fullness s V ≤ ShadedBody.fullness s V' := by
  have hcoe : ENNReal.ofReal ((δ : ℝ) ^ (-α)) = ((δ ^ (-α) : NNReal) : ENNReal) := by
    rw [← NNReal.coe_rpow, ENNReal.ofReal_coe_nnreal]
  rw [hcoe, ← ShadedBody.coe_fullness, ← ShadedBody.coe_fullness, ← ENNReal.coe_mul,
    ENNReal.coe_le_coe] at h
  have hmul : δ ^ α * (δ ^ (-α) * ShadedBody.fullness s V') = ShadedBody.fullness s V' := by
    rw [← mul_assoc, ← NNReal.rpow_add hδ.ne']
    simp
  calc δ ^ α * ShadedBody.fullness s V
      ≤ δ ^ α * (δ ^ (-α) * ShadedBody.fullness s V') := by
        exact mul_le_mul' le_rfl h
    _ = ShadedBody.fullness s V' := hmul

open ShadedTube in
/-- **`uniform` and `fullness_ge` at the repaired exponent are jointly deliverable from the
aggregate binder alone.**

The composition the construction of Configuration `hyp:ml2setup` has to run at this point:

1. the Markov step of the density-band pigeonhole
   (`Kakeya.VeryNotSticky.exists_isCRefinement_pointwise_density`) at the floor `δ^{3η/2}`,
   which makes every retained tube individually `δ^{3η/2}`-full;
2. the shaded uniformization
   (`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`) at both loss exponents `η/2`,
   which delivers the bundle of the field `Kakeya.VeryNotSticky.uniform` at the
   **dimension-only** constant `ShadedTube.ssfUniformConst`, hence at a constant fixed before
   `δ`, which is what makes `Kakeya.VeryNotSticky.aScaleData_absorb` a plain threshold on `δ`
   (`Kakeya.VeryNotSticky.eventually_aScaleData_absorb`).

The aggregate fullness that survives is `δ^{η/2} · δ^{3η/2} = δ^{2η}`, and the two steps'
losses exhaust the `δ^η` the repaired field grants **exactly**, with the choice `α = α' = η/2`.
Nothing here is `δ`-geometric: the input is the target's binder `hfull` together with the two
side conditions the uniformization asks for (the family lies in the unit ball, and its
cardinality is at most a fixed power of `δ`).

So the field `Kakeya.VeryNotSticky.fullness_ge` at `δ^{2η}` is not merely affordable, it is
*paid for* by this composition; at `δ^η` no composition can pay for it, because the
uniformization's loss exponent `α'` is required to be positive. -/
theorem exists_uniform_refinement_fullness_two_eta {η : ℝ} (hη : 0 < η) (K₀ : ℕ) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
        δ ^ η ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) →
        ∃ s' ⊆ s, ∃ T' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)),
          (∀ i, (T' i).toTube = (T i).toTube) ∧
          (∀ i, (T' i).shade ⊆ (T i).shade) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s' T' (Tube.ssfGridLen δ)
            (ShadedTube.ssfUniformConst
              (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))) ∧
          ShadedBody.IsRefinement s' (fun i ↦ (T' i).toShadedBody) s
            (fun i ↦ (T i).toShadedBody) ∧
          δ ^ (2 * η) ≤ ShadedBody.fullness s' (fun i ↦ (T' i).toShadedBody) := by
  classical
  obtain ⟨δ₁, hδ₁pos, hδ₁le1, H⟩ :=
    ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf
      (E := EuclideanSpace ℝ (Fin 3)) K₀ (η / 2) (η / 2) (by linarith) (by linarith)
  refine ⟨min δ₁ (1 / 2), lt_min hδ₁pos (by norm_num), le_trans (min_le_right _ _) (by norm_num),
    ?_⟩
  intro ι δ hδ hδmin s T hball hcard hfull
  have hδδ₁ : δ ≤ δ₁ := le_trans hδmin (min_le_left _ _)
  have hδhalf : δ ≤ 1 / 2 := le_trans hδmin (min_le_right _ _)
  have hδlt1 : δ < 1 := lt_of_le_of_lt hδhalf (by norm_num)
  have hδ1 : δ ≤ 1 := hδlt1.le
  set V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun i ↦ (T i).toShadedBody with hVdef
  have ha : 0 < δ ^ η := NNReal.rpow_pos hδ
  have hq1 : δ ^ (η / 2) ≤ 1 := NNReal.rpow_le_one hδ1 (by linarith)
  have hqlt1 : δ ^ (η / 2) < 1 := NNReal.rpow_lt_one hδlt1 (by linarith)
  have hθq : δ ^ (η + η / 2) ≤ δ ^ (η / 2) * δ ^ η := by
    rw [← NNReal.rpow_add hδ.ne']
    apply le_of_eq
    congr 1
    ring
  obtain ⟨s₁, hs₁s, hdense, href₁⟩ :=
    exists_isCRefinement_pointwise_density (s := s) (V := V) (a := δ ^ η)
      (θ := δ ^ (η + η / 2)) (q := δ ^ (η / 2)) ha hfull hq1 hθq
  -- the given family carries positive shade mass, so the Markov subfamily is nonempty
  have hXne : ∑ i ∈ s, volume (V i).shade ≠ 0 := by
    intro h0
    have hz : ShadedBody.fullness s V = 0 := by
      have hc := ShadedBody.fullness_def s V
      have hzz : ((ShadedBody.fullness s V : NNReal) : ENNReal) = 0 := by
        rw [hc, h0, ENNReal.zero_div]
      exact_mod_cast hzz
    rw [hz] at hfull
    exact absurd (le_antisymm hfull (by simp)) ha.ne'
  have hs₁ne : s₁.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s₁ with hemp | hne
    · exfalso
      have hm := href₁.2
      rw [hemp] at hm
      simp only [Finset.sum_empty, nonpos_iff_eq_zero] at hm
      rcases mul_eq_zero.mp hm with h | h
      · have : (1 : NNReal) - δ ^ (η / 2) ≠ 0 := (tsub_pos_of_lt hqlt1).ne'
        exact this (by exact_mod_cast h)
      · exact hXne h
    · exact hne
  have hcard₁ : (s₁.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) :=
    le_trans (by exact_mod_cast Nat.cast_le.2 (Finset.card_le_card hs₁s)) hcard
  obtain ⟨s', hs's₁, T', htube, hshade, hcardcmp, hfullcmp, huni⟩ :=
    H hδ hδδ₁ s₁ T (fun i hi ↦ hball i (hs₁s hi)) hcard₁
  refine ⟨s', hs's₁.trans hs₁s, T', htube, hshade, huni,
    ⟨hs's₁.trans hs₁s, fun i _ ↦ ⟨congrArg Tube.toConvexSpaceBody (htube i), hshade i⟩⟩, ?_⟩
  -- `s'` is nonempty, by the cardinality comparison of the uniformization
  have hs'ne : s'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s' with hemp | hne
    · exfalso
      rw [hemp] at hcardcmp
      simp only [Finset.card_empty, Nat.cast_zero, mul_zero] at hcardcmp
      have h1 : (1 : ℝ) ≤ (s₁.card : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (Finset.card_ne_zero_of_mem hs₁ne.choose_spec)
      linarith
    · exact hne
  -- the carriers of a nonempty tube family have positive total volume
  have hcarne : ∑ i ∈ s', volume (V i).carrier ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ := hs'ne
    have hpos : 0 < volume (V i₀).carrier :=
      (Tube.volume_pos_and_lt_top hδ hδ1 (T i₀).toTube).1
    refine ne_of_gt (lt_of_lt_of_le hpos ?_)
    exact Finset.single_le_sum (f := fun i ↦ volume (V i).carrier)
      (fun i _ ↦ zero_le) hi₀
  -- every tube of `s'` is individually `δ^{3η/2}`-full, hence so is the aggregate
  have hpt : δ ^ (η + η / 2) ≤ ShadedBody.fullness s' V :=
    le_fullness_of_pointwise hcarne (fun i hi ↦ hdense i (hs's₁ hi))
  have hloss := rpow_mul_fullness_le_of_fullness'_le (s := s')
    (V := V) (V' := fun i ↦ (T' i).toShadedBody) (α := η / 2) hδ hfullcmp
  have hsplit : δ ^ (2 * η) = δ ^ (η / 2) * δ ^ (η + η / 2) := by
    rw [← NNReal.rpow_add hδ.ne']
    congr 1
    ring
  calc δ ^ (2 * η) = δ ^ (η / 2) * δ ^ (η + η / 2) := hsplit
    _ ≤ δ ^ (η / 2) * ShadedBody.fullness s' V := mul_le_mul' le_rfl hpt
    _ ≤ ShadedBody.fullness s' (fun i ↦ (T' i).toShadedBody) := hloss

/-! ### The demand side: what the produced shading must satisfy at every one of its points -/

open scoped Classical in
/-- **The side data forces the produced shading to be `δ^{3η}`-dense at scale `r₁` around every
point of its *working* shading `Y_g`.**

Unconditional, and the statement of what a construction has to *arrange*.  The cover of (C2)
covers the working shading `Y_g(T) ⊆ Y(T)` of every retained tube, each
of its pieces lies in an `r₁`-ball (`Kakeya.VeryNotSticky.BallData.P_subset_ball`), and each
carries shading of measure at least `δ^{3η}|B_δ|`
(`Kakeya.VeryNotSticky.caseSideData_pieceMass`; `denseBall` at the `tb` index `2η`, F8, times
`C ≤ δ^{-η}`).  So no point of the working shading may sit in
a `2r₁`-ball where the produced shading is lighter than `δ^{3η}|B_δ|`.  A point of
`Y(T) \ Y_g(T)` is *not* constrained: that the demand weakens from `Y` to the working shading
is the point of the repair — GWZ delete the light pieces from the shading they continue to call
`Y` (`gwz.txt` l.2029-2030), and the hypothesis `hx` now reads `x ∈ bd.Yg i` .

The only tool a construction has for meeting this is to **delete** the shading that fails it —
carriers are fixed by `ShadedBody.IsRefinement`, so nothing else can move.  That deletion costs
shading mass, and the budget for that cost is `Kakeya.VeryNotSticky.fullness_ge`: zero as the
field is written, `δ^η` at the repaired exponent
(`Kakeya.VeryNotSticky.lt_rpow_of_fullness_loss`,
`Kakeya.VeryNotSticky.rpow_two_eta_le_of_fullness_loss`). -/
theorem caseSideData_localDensity {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {τ τ' : ℝ}
    (sd : CaseSideData cfg bd τ τ') {i : cfg.ι} (hi : i ∈ cfg.s)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ bd.Yg i) :
    (cfg.δ : ENNReal) ^ (3 * cfg.η) *
        volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (cfg.δ : ℝ))
      ≤ volume (closedBall x (2 * (cfg.r₁ : ℝ)) ∩ ⋃ j ∈ cfg.s, (cfg.T j).shade) := by
  classical
  obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 (bd.P_cover i hi hx)
  have hxctr : dist x (bd.ctr B) ≤ (cfg.r₁ : ℝ) :=
    Metric.mem_closedBall.1 (bd.P_subset_ball B hB hxB)
  have hPsub : bd.P B ⊆ closedBall x (2 * (cfg.r₁ : ℝ)) := by
    intro z hz
    have hzctr : dist z (bd.ctr B) ≤ (cfg.r₁ : ℝ) :=
      Metric.mem_closedBall.1 (bd.P_subset_ball B hB hz)
    refine Metric.mem_closedBall.2 ?_
    calc dist z x ≤ dist z (bd.ctr B) + dist (bd.ctr B) x := dist_triangle _ _ _
      _ = dist z (bd.ctr B) + dist x (bd.ctr B) := by rw [dist_comm (bd.ctr B) x]
      _ ≤ (cfg.r₁ : ℝ) + (cfg.r₁ : ℝ) := by gcongr
      _ = 2 * (cfg.r₁ : ℝ) := by ring
  refine le_trans (caseSideData_pieceMass sd hB) (measure_mono ?_)
  intro z hz
  exact ⟨hPsub hz.1, hz.2⟩

end Kakeya.VeryNotSticky
