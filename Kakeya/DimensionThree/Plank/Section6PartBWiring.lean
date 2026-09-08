/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Section6PartBPlankOutput
public import Kakeya.DimensionThree.Plank.PartBBlockCount

/-!
# The Part-(B) wiring: the block pigeonhole composed with the plank presentation

Two independent gaps of GWZ Proposition 6.6(B) were closed separately:

* the **block-size pigeonhole** — GWZ Part (A)'s uniformization step, which Part (B) omits —
  giving a sub-datum `Kakeya.BlockCount.restrictCells D cells' hsub` obtained by discarding whole
  cells, on which the fibre sizes are comparable with the **absolute** constant `2` and the
  cardinality clause `|𝒲'| · |𝒯_W| ≤ 2 · |𝒯|` holds for **every** surviving cell
  (`Kakeya.BlockCount.exists_restrictCells_block_equalised`);
* the **plank presentation** of the constructed Proposition-5.1 output
  (`Kakeya.Section6PartBData.exists_plank_presented_prop51_split`), which puts the outer family on
  genuine `Kakeya.ShadedPlank a b`s in the fixed radius-`4` window, with Katz--Tao, and with the
  multiplicity split unchanged because the presenting homothety leaves
  `Kakeya.ShadedBody.multiplicity` invariant.

This file composes them, and the composition is the point: the pigeonhole discards whole cells, so
*every* hypothesis of the plank presentation restricts to the sub-datum verbatim, and the only price
paid on the way back to the full fine family is the single logarithmic factor
`Kakeya.dyadicPigeonholeNatConstant |𝒯| = Nat.log 2 |𝒯| + 1`.

## Why this is the whole of the "swap the datum" step, and what remains

The queued next action was phrased as four steps: swap `Remark53Prop51` for the same hypothesis on
the restricted datum, delete the `fiber_card_comparable` field, take `Ccard := 2`, re-price fullness
by `L`.  It is **five**: swapping the datum does not swap the *conclusion*.  The exported statement
of the Section-6 assembly is over the **full** `𝒯` — it names
`ShadedBody.multiplicity q (fun i ↦ (T i).toShadedBody)`, `q.card` and `maxDensity q …` — so the
conclusion has to be carried back from the restricted fine family to `𝒯`, and that is where `L`
actually enters.  Each exported quantity is checked here:

| exported quantity | how it comes back |
|---|---|
| `μ(𝒯, Y)` | `Kakeya.BlockCount.multiplicity_le_mul_of_subset`, one factor `L` |
| `\|𝒲'\| · \|𝒯_W\| ≤ Ccard · \|𝒯\|` | `|ts| ≤ |cells'|`, `|fib j| ≤ |block|`, `|𝒯''| ≤ |𝒯|` — all in the safe direction, `Ccard = 2` |
| `IsRefinement … 𝒯` | the ambient set only grows, and `Kakeya.ShadedBody.IsRefinement`'s pointwise clauses do not mention it |
| pairwise essential distinctness, `carrier ⊆ B₁`, `maxDensity` | monotone in the index set |
| `λ(𝒯, Y) ≥ δ^η` | `L⁻¹ λ(𝒯, Y) ≤ λ(𝒯'', Y)`, so `η` must absorb `L` — **the fifth step** |

The fifth step is arithmetic, and it needs an a-priori bound on `|𝒯|` in terms of `δ`, because `L`
depends on the configuration while `η` is fixed before it.  That bound is available from hypotheses
6.6(B) already has, and it is supplied here as
`Kakeya.Section6PartBData.dyadicPigeonholeNatConstant_le_of_pairwise_essDistinct`:
`Tube.card_le_of_EssDistinct` gives `|𝒯| ≤ C₃ · δ^{-6}` from the unit-ball containment and
the pairwise essential distinctness of the fine tubes, so `L = O(log(1/δ))`.  Note the exponent is
**`6`**, not `4`: the tree's counting constant is deliberately crude (its own docstring says the
geometric truth is `(r/δ)^n`).  Nothing depends on which, since only `log |𝒯|` is used, but the
ledger should record what the compiler accepts.

## What is deliberately *not* done here

No field of any structure is changed.

Also provided, because the next step needs it and it is free:
`Kakeya.Section6PartBData.withShades`, the substitution of the fine shadings.  The Part-(B) datum
mentions the fine family `T` in exactly one place — `Section6CoarseTubeDecomposition.leaf_le_parent`,
which is about *carriers* — so shrinking the shadings of the fine tubes produces another Part-(B)
datum with the same `decomp.assign` and the same `factor`.  That is what will let the *refined*
inner family of Proposition 5.1 (whose bodies are the fine tubes' bodies and whose shadings are
smaller) be fed to the tree's existing inner pipeline
(`Kakeya.exists_partB_selected_inner_ED_package`), which is hard-wired to `D.fineOutput` and hence
to a shaded-tube family.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal ENNReal Classical

noncomputable section

namespace Kakeya

namespace Section6PartBData

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {m Cfib CF C₀ : ℝ≥0}

/-! ## Substituting the fine shadings -/

/-- Re-shade a shaded tube: same tube, smaller shading. -/
def _root_.ShadedTube.reshade {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [MeasurableSpace E] {δ' : ℝ≥0} (S : ShadedTube δ' E)
    (Y : Set E) (hY : MeasurableSet Y) (hsub : Y ⊆ S.carrier) : ShadedTube δ' E :=
  { S with shade := Y, measurableSet_shade := hY, shade_subset := hsub }

@[simp] theorem _root_.ShadedTube.reshade_shade {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] [MeasurableSpace E] {δ' : ℝ≥0} (S : ShadedTube δ' E)
    (Y : Set E) (hY : MeasurableSet Y) (hsub : Y ⊆ S.carrier) :
    (S.reshade Y hY hsub).shade = Y := rfl

@[simp] theorem _root_.ShadedTube.reshade_toTube {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] [MeasurableSpace E] {δ' : ℝ≥0} (S : ShadedTube δ' E)
    (Y : Set E) (hY : MeasurableSet Y) (hsub : Y ⊆ S.carrier) :
    (S.reshade Y hY hsub).toTube = S.toTube := rfl

/-- **The Part-(B) datum is insensitive to the fine shadings.**

`Kakeya.Section6PartBData` mentions its fine family `T` in exactly one field,
`Kakeya.Section6CoarseTubeDecomposition.leaf_le_parent`, and that field is about *carriers*.  So
shrinking (or replacing) the shadings produces another Part-(B) datum, with the *same*
`decomp.assign`, the same `factor`, and hence the same cells, blocks and coarse fibres.

This is the bridge the honest Proposition-5.1 output needs: its refined inner family has the fine
tubes' bodies and smaller shadings, and the tree's inner pipeline consumes a *shaded-tube* family
through `Kakeya.Section6PartBData.fineOutput`. -/
def withShades (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)
    (Y : ι → Set (EuclideanSpace ℝ (Fin 3)))
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (T i).carrier) :
    Section6PartBData a b hab hb1 q (fun i => (T i).reshade (Y i) (hY i) (hsub i))
      coarseSet R m Cfib CF C₀ where
  decomp :=
    { assign := D.decomp.assign
      assign_mem := D.decomp.assign_mem
      leaf_le_parent := D.decomp.leaf_le_parent
      one_le_Cfib := D.decomp.one_le_Cfib
      m_pos := D.decomp.m_pos
      fibre_nonempty := D.decomp.fibre_nonempty
      le_card_fibre := D.decomp.le_card_fibre
      card_fibre_le := D.decomp.card_fibre_le }
  factor := D.factor

@[simp] theorem withShades_factor (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)
    (Y : ι → Set (EuclideanSpace ℝ (Fin 3)))
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (T i).carrier) :
    (D.withShades Y hY hsub).factor = D.factor := rfl

@[simp] theorem withShades_cellOfFine
    (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)
    (Y : ι → Set (EuclideanSpace ℝ (Fin 3)))
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (T i).carrier) (i : ι) :
    (D.withShades Y hY hsub).cellOfFine i = D.cellOfFine i := rfl

@[simp] theorem withShades_fineFibre
    (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)
    (Y : ι → Set (EuclideanSpace ℝ (Fin 3)))
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (T i).carrier) (x : D.factor.Cell) :
    (D.withShades Y hY hsub).fineFibre x = D.fineFibre x := rfl

/-! ## The composition -/

variable (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)

/-- **A surviving cell keeps its whole coarse fibre**, in the form the plank presentation wants.
`Kakeya.BlockCount.filter_restrictCoarse_cellOf_eq` with the cell bound at the *original* datum, so
that the implicit `D` of that lemma is not accidentally instantiated at the restricted one. -/
theorem restrictCells_coarseFibre_eq {cells' : Finset D.factor.Cell}
    (hsub : cells' ⊆ D.factor.cells) {x : D.factor.Cell} (hx : x ∈ cells') :
    (BlockCount.restrictCells D cells' hsub).factor.coarseFibre x = D.factor.coarseFibre x := by
  classical
  show ({k ∈ BlockCount.restrictCoarse D cells' | D.factor.cellOf k = x} : Finset κ)
    = D.factor.coarseFibre x
  rw [BlockCount.filter_restrictCoarse_cellOf_eq hx]
  rfl

open Classical in
/-- **GWZ Proposition 6.6(B): the Proposition-5.1 multiplicity split on exact `a × b × 1` shaded
planks, with the block-size cardinality clause, over the whole fine family.**

The two previously independent gaps, composed.  Explicitly:

* `cells'` is the dyadic block class of the pigeonhole and `ts ⊆ cells'` the productive cells of the
  Proposition-5.1 output;
* `W` is an outer family of **genuine `Kakeya.ShadedPlank a b hab hb1`s** in the fixed radius-`4`
  Section-6 window, carrying Katz--Tao with two absolute losses (the collar doubling constant and
  the exact-envelope volume ratio) times the datum's own `C₀`;
* the cardinality clause holds with the **absolute constant `2`**, for **every** retained cell —
  which is what `Kakeya.factoringAndMultPropGlobal` needs of its `Ccard`, since that constant sits
  in the outermost existential and must be fixed before the configuration;
* the multiplicity split is over the **full** `𝒯`, and the entire price of the pigeonhole is the
  single explicit factor `Kakeya.dyadicPigeonholeNatConstant q.card = Nat.log 2 |𝒯| + 1`.

No `Kakeya.Section6PartBData.Remark53Prop51` anywhere.  The only hypothesis beyond those
`Kakeya.Section6PartBData.exists_prop51SelectScale` already carries is
`IsPlankOfDimensions Cw a b (D.factor.body x)`, produced by
`Kakeya.GlobalPlankFactorization.exists_isPlankFamilyOfDimensions` at a re-declared thin half-width
`a' ≤ a` (which only weakens the `(a/b)^β` gain, so nothing is lost). -/
theorem exists_plank_presented_split_of_blockPigeonhole
    (hδ0 : 0 < δ) (hδhalf : (δ : ℝ) ≤ 1 / 2) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδa : δ ≤ a) (ha0 : 0 < a) (hb0 : 0 < b)
    (hball : ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 1)
    (hmass : 0 < ∑ i ∈ q, volume (T i).shade)
    (hsmall : δ + 2 * a ≤ 1)
    (hcfne : ∀ x ∈ D.factor.cells, (D.factor.coarseFibre x).Nonempty)
    {Cw : ℝ≥0} (hCw : 1 ≤ Cw)
    (hdimK : ∀ x ∈ D.factor.cells, IsPlankOfDimensions Cw a b (D.factor.body x)) :
    ∃ (Cs : ℝ≥0) (cells' ts : Finset D.factor.Cell)
      (W : D.factor.Cell → ShadedPlank a b hab hb1)
      (isub : Finset ι) (Oin : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (fib : D.factor.Cell → Finset ι),
      1 ≤ Cs ∧
      cells' ⊆ D.factor.cells ∧ ts ⊆ cells' ∧
      (∀ j ∈ ts, ((W j).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ Metric.closedBall 0 ((plankWindowRadius : ℝ≥0) : ℝ)) ∧
      ShadedBody.IsRefinement isub Oin q (fun i => (T i).toShadedBody) ∧
      ConvexSpaceBody.IsKatzTao ts (fun j => (W j).toConvexSpaceBody)
        ((flatPrismEnvelopeVolumeRatio.C
            (windowPlankEnvelope.windowConst plankWindowRadius Cw) : ENNReal)
          * ((Metric.volume_comparison.C 3 : ENNReal) * (C₀ : ENNReal))) ∧
      (∀ j ∈ ts, (ts.card : ENNReal) * ((fib j).card : ENNReal)
        ≤ (2 : ℝ≥0) * (q.card : ENNReal)) ∧
      (∀ j ∈ ts, ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
        ≤ (Kakeya.dyadicPigeonholeNatConstant q.card : ENNReal) * (Cs : ENNReal)
            * ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
            * ShadedBody.multiplicity (fib j) Oin) := by
  classical
  -- the block pigeonhole
  obtain ⟨cells', hsub, -, -, hcount, href, hmult⟩ :=
    BlockCount.exists_restrictCells_block_equalised D
  have hq'sub : BlockCount.restrictFine D cells' ⊆ q :=
    fun i hi => (BlockCount.mem_restrictFine_iff.mp hi).1
  have hball' : ∀ i ∈ BlockCount.restrictFine D cells',
      ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 1 :=
    fun i hi => hball i (hq'sub hi)
  have hLne : (Kakeya.dyadicPigeonholeNatConstant q.card : ℝ≥0) ≠ 0 := by
    simp [Kakeya.dyadicPigeonholeNatConstant]
  have hmass' : 0 < ∑ i ∈ BlockCount.restrictFine D cells', volume (T i).shade := by
    refine lt_of_lt_of_le ?_ href.2
    exact ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr (inv_ne_zero hLne)) hmass.ne'
  -- every hypothesis of the plank presentation restricts verbatim
  have hcfne' : ∀ x ∈ (BlockCount.restrictCells D cells' hsub).factor.cells,
      ((BlockCount.restrictCells D cells' hsub).factor.coarseFibre x).Nonempty := by
    intro x hx
    have hx' : x ∈ cells' := hx
    rw [restrictCells_coarseFibre_eq D hsub hx']
    exact hcfne x (hsub hx')
  have hdimK' : ∀ x ∈ (BlockCount.restrictCells D cells' hsub).factor.cells,
      IsPlankOfDimensions Cw a b
        ((BlockCount.restrictCells D cells' hsub).factor.body x) := by
    intro x hx
    have hx' : x ∈ cells' := hx
    exact hdimK x (hsub hx')
  obtain ⟨Cs, ts, W, isub, Oin, fib, hCs, htssub, hwin, href2, hfibsub, hKT, hsplit⟩ :=
    (BlockCount.restrictCells D cells' hsub).exists_plank_presented_prop51_split
      hδ0 hδhalf hρ0 hρ1 hδa ha0 hb0 hball' hmass' hsmall hcfne' hCw hdimK'
  refine ⟨Cs, cells', ts, W, isub, Oin, fib, hCs, hsub, htssub, hwin, ?_, hKT, ?_, ?_⟩
  · -- the refinement, read against the whole fine family
    exact ⟨href2.1.trans hq'sub, href2.2⟩
  · -- the cardinality clause, with the absolute constant `2`
    intro j hj
    have hj' : j ∈ cells' := htssub hj
    have h1 : (ts.card : ENNReal) ≤ (cells'.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card htssub
    have h2 : ((fib j).card : ENNReal)
        ≤ (((BlockCount.restrictCells D cells' hsub).fineOutput.fiber j).card : ENNReal) := by
      have hfj : fib j ⊆ (BlockCount.restrictCells D cells' hsub).fineFibre j := hfibsub j
      exact_mod_cast Finset.card_le_card hfj
    have h3 : (((BlockCount.restrictFine D cells').card : ENNReal)) ≤ (q.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card hq'sub
    calc
      (ts.card : ENNReal) * ((fib j).card : ENNReal)
          ≤ (cells'.card : ENNReal)
              * (((BlockCount.restrictCells D cells' hsub).fineOutput.fiber j).card : ENNReal) :=
            mul_le_mul' h1 h2
      _ ≤ (2 : ℝ≥0) * ((BlockCount.restrictFine D cells').card : ENNReal) := hcount j hj'
      _ ≤ (2 : ℝ≥0) * (q.card : ENNReal) := mul_le_mul_left' h3 _
  · -- the split, carried back to the full fine family
    intro j hj
    calc
      ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
          ≤ (Kakeya.dyadicPigeonholeNatConstant q.card : ENNReal)
              * ShadedBody.multiplicity (BlockCount.restrictFine D cells')
                  (fun i => (T i).toShadedBody) := hmult
      _ ≤ (Kakeya.dyadicPigeonholeNatConstant q.card : ENNReal)
              * ((Cs : ENNReal) * ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
                  * ShadedBody.multiplicity (fib j) Oin) :=
            mul_le_mul_left' (hsplit j hj) _
      _ = (Kakeya.dyadicPigeonholeNatConstant q.card : ENNReal) * (Cs : ENNReal)
              * ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
              * ShadedBody.multiplicity (fib j) Oin := by ring

/-! ## The fifth step: the pigeonhole loss is sub-polynomial

`L = Kakeya.dyadicPigeonholeNatConstant |𝒯| = Nat.log 2 |𝒯| + 1` depends on the *configuration*,
whereas the fullness exponent `η` of `Kakeya.factoringAndMultPropGlobal` is fixed **before** it.
So absorbing `L` into a `δ`-power is not a matter of enlarging a constant: it needs an a-priori
bound on `|𝒯|` in terms of `δ`, derived rather than assumed.

Both hypotheses that supply it are already present in the assembly: the fine tubes lie in the unit
ball and are pairwise essentially distinct.  `Tube.card_le_of_EssDistinct` then gives
`|𝒯| ≤ C₃ · δ^{-6}`, with `C₃ = Tube.card_le_of_EssDistinct.C 3` absolute.  The exponent is
`6`, not `4`: that lemma's own docstring records that its counting is deliberately crude (the
geometric truth is `(r/δ)^n`).  Only `log |𝒯|` is used, so the value is immaterial — but the ledger
should say what the compiler accepts. -/

section Absorb

/-- The `∃ δ₀` reading of an `∀ᶠ δ in 𝓝[>] 0` statement.

A deliberate copy of `Kakeya.StickyKakeya.exists_threshold_of_eventually_nhdsGT`, repeated here
rather than imported: that lemma sits in `Kakeya/StickyKakeya/Constants.lean`, whose import closure
carries `Kakeya.Sticky` and with it the only `axiom` of the development.  Importing it into the
Section-6 plank files would put that axiom on the import path of a file that has no business
depending on it. -/
private lemma exists_threshold_of_eventually' {p : ℝ≥0 → Prop}
    (h : ∀ᶠ x : ℝ≥0 in nhdsWithin (0 : ℝ≥0) (Set.Ioi 0), p x) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ x : ℝ≥0, 0 < x → x ≤ δ₀ → p x := by
  rw [Filter.eventually_iff, mem_nhdsWithin] at h
  obtain ⟨U, hU_open, hU_mem0, hU_sub⟩ := h
  obtain ⟨t, ht_pos, ht_sub⟩ := nhds_bot_basis.mem_iff.mp (hU_open.mem_nhds hU_mem0)
  refine ⟨t / 2, div_pos ht_pos (by norm_num), fun x hx_pos hx_le => ?_⟩
  have hx_lt : x < t := lt_of_le_of_lt hx_le (div_lt_self ht_pos (by norm_num))
  exact hU_sub ⟨ht_sub hx_lt, hx_pos⟩

/-- **`1 + log₂ N ≤ (1 + log₂(1/δ))^m` when `N ≤ (1/δ)^m` and `δ ≤ 1/2`.**

The composition step named in the docstring of
`ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg`: a cardinality factor bounded by a
fixed power of `1/δ` is covered by that lemma with the exponent enlarged, and needs no separate
asymptotic argument.  Bernoulli does the work. -/
theorem one_add_logb_le_pow_of_le_pow {δ : ℝ} (hδ2 : 2 ≤ 1 / δ) {N : ℝ} (hN1 : 1 ≤ N)
    {m : ℕ} (hm : N ≤ (1 / δ) ^ m) :
    1 + Real.logb 2 N ≤ (1 + Real.logb 2 (1 / δ)) ^ m := by
  have hone : (1 : ℝ) < 2 := by norm_num
  have hL1 : 1 ≤ Real.logb 2 (1 / δ) := by
    have h := Real.logb_le_logb_of_le (b := 2) hone (by norm_num) hδ2
    rwa [Real.logb_self_eq_one hone] at h
  have hlog : Real.logb 2 N ≤ (m : ℝ) * Real.logb 2 (1 / δ) := by
    calc
      Real.logb 2 N ≤ Real.logb 2 ((1 / δ) ^ m) :=
        Real.logb_le_logb_of_le (b := 2) hone (by linarith) hm
      _ = (m : ℝ) * Real.logb 2 (1 / δ) := by rw [Real.logb_pow]
  have hbern : 1 + (m : ℝ) * Real.logb 2 (1 / δ)
      ≤ (1 + Real.logb 2 (1 / δ)) ^ m := by
    have := one_add_mul_le_pow (a := Real.logb 2 (1 / δ)) (by linarith) m
    linarith
  linarith

/-- **The pigeonhole loss, bounded by a fixed power of `1 + log₂(1/δ)`.** -/
theorem dyadicPigeonholeNatConstant_le_pow_one_add_logb
    {δ : ℝ} (hδ2 : 2 ≤ 1 / δ) {N : ℕ} {m : ℕ} (hm : (N : ℝ) ≤ (1 / δ) ^ m) :
    ((Kakeya.dyadicPigeonholeNatConstant N : ℕ) : ℝ)
      ≤ (1 + Real.logb 2 (1 / δ)) ^ (m + 1) := by
  have hL0 : (0 : ℝ) ≤ Real.logb 2 (1 / δ) := by
    have hone : (1 : ℝ) < 2 := by norm_num
    have h := Real.logb_le_logb_of_le (b := 2) hone (by norm_num) hδ2
    rw [Real.logb_self_eq_one hone] at h
    linarith
  have hbase : (1 : ℝ) ≤ 1 + Real.logb 2 (1 / δ) := by linarith
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : ((Kakeya.dyadicPigeonholeNatConstant 0 : ℕ) : ℝ) = 1 := by
      simp [Kakeya.dyadicPigeonholeNatConstant]
    rw [this]
    exact one_le_pow₀ hbase
  · have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hfloor : (Nat.log 2 N : ℝ) ≤ Real.logb 2 (N : ℝ) := by
      have heq : ⌊Real.logb 2 (N : ℝ)⌋₊ = Nat.log 2 N := by
        simpa using Real.natFloor_logb_natCast 2 N
      have hnn : (0 : ℝ) ≤ Real.logb 2 (N : ℝ) := Real.logb_nonneg (by norm_num) hN1
      calc (Nat.log 2 N : ℝ) = (⌊Real.logb 2 (N : ℝ)⌋₊ : ℝ) := by rw [heq]
        _ ≤ Real.logb 2 (N : ℝ) := Nat.floor_le hnn
    have hstep : ((Kakeya.dyadicPigeonholeNatConstant N : ℕ) : ℝ)
        ≤ 1 + Real.logb 2 (N : ℝ) := by
      have : ((Kakeya.dyadicPigeonholeNatConstant N : ℕ) : ℝ) = (Nat.log 2 N : ℝ) + 1 := by
        simp [Kakeya.dyadicPigeonholeNatConstant]
      rw [this]
      linarith
    calc ((Kakeya.dyadicPigeonholeNatConstant N : ℕ) : ℝ)
        ≤ 1 + Real.logb 2 (N : ℝ) := hstep
      _ ≤ (1 + Real.logb 2 (1 / δ)) ^ m := one_add_logb_le_pow_of_le_pow hδ2 hN1 hm
      _ ≤ (1 + Real.logb 2 (1 / δ)) ^ (m + 1) := by
          exact pow_le_pow_right₀ hbase (Nat.le_succ m)

end Absorb

open Filter Topology in
/-- **The fifth step of the wiring: the block-pigeonhole loss is absorbed by an arbitrarily small
negative power of the scale.**

`L = Kakeya.dyadicPigeonholeNatConstant |𝒯|` is configuration-dependent, so this cannot be an
absorption of a constant; it needs the a-priori count `|𝒯| ≤ C₃ · δ^{-6}` of
`Tube.card_le_of_EssDistinct`, which is available from exactly the two hypotheses the
Section-6 assembly already carries — the fine tubes lie in `B₁`, and they are pairwise essentially
distinct.  With that, `L ≤ (1 + log₂(1/δ))^8` and
`ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg` finishes.

This is what lets a caller shrink `η` once, before the configuration, and still absorb `L`. -/
theorem exists_threshold_dyadicPigeonholeNatConstant_le_rpow_neg {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧
      ∀ δ' : ℝ≥0, 0 < δ' → δ' ≤ δ₀ →
        ∀ {ι' : Type*} (q' : Finset ι') (T' : ι' → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))),
          (∀ i ∈ q', ((T' i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            ⊆ Metric.closedBall 0 1) →
          (q' : Set ι').Pairwise (fun i j => _root_.IsEssentiallyDistinct
            ((T' i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            ((T' j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
          ((Kakeya.dyadicPigeonholeNatConstant q'.card : ℕ) : ENNReal) ≤ (δ' : ENNReal) ^ (-ε) := by
  classical
  have hC₃ : 0 < _root_.Tube.card_le_of_EssDistinct.C 3 :=
    _root_.Tube.card_le_of_EssDistinct.C_pos
  refine exists_threshold_of_eventually' ?_
  have hev1 := ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg hε 8
  have hev2 : ∀ᶠ (x : ℝ≥0) in 𝓝[>] (0 : ℝ≥0), x < 1 / 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
  have hev3 : ∀ᶠ (x : ℝ≥0) in 𝓝[>] (0 : ℝ≥0),
      x < (Real.toNNReal (_root_.Tube.card_le_of_EssDistinct.C 3))⁻¹ := by
    refine nhdsWithin_le_nhds (Iio_mem_nhds ?_)
    have : 0 < Real.toNNReal (_root_.Tube.card_le_of_EssDistinct.C 3) :=
      Real.toNNReal_pos.mpr hC₃
    exact inv_pos.mpr this
  filter_upwards [self_mem_nhdsWithin, hev1, hev2, hev3] with δ' hδ0 h1 h2 h3
  intro ι' q' T' hball hED
  have hδ0' : 0 < δ' := hδ0
  have hδR : (0 : ℝ) < (δ' : ℝ) := by exact_mod_cast hδ0'
  -- `2 ≤ 1 / δ`
  have hδhalfR : (δ' : ℝ) < 1 / 2 := by
    have := NNReal.coe_lt_coe.mpr h2
    simpa using this
  have hδ2 : (2 : ℝ) ≤ 1 / (δ' : ℝ) := by
    rw [le_div_iff₀ hδR]
    linarith
  -- `C₃ ≤ 1 / δ`
  have hCinv : _root_.Tube.card_le_of_EssDistinct.C 3 ≤ 1 / (δ' : ℝ) := by
    have hlt := NNReal.coe_lt_coe.mpr h3
    rw [NNReal.coe_inv, Real.coe_toNNReal _ hC₃.le] at hlt
    rw [le_div_iff₀ hδR]
    rw [lt_inv_comm₀ hδR hC₃] at hlt
    have hprod := mul_lt_mul_of_pos_right hlt hδR
    rw [inv_mul_cancel₀ (ne_of_gt hδR)] at hprod
    linarith
  -- the a-priori count
  have hcard0 : (q'.card : ℝ) ≤ _root_.Tube.card_le_of_EssDistinct.C 3 * (1 / (δ' : ℝ)) ^ 6 := by
    have h' := _root_.Tube.card_le_of_EssDistinct (E := EuclideanSpace ℝ (Fin 3)) hδ0' (1 : ℝ)
      q' (fun i => (T' i).toTube) hball hED
    simpa [finrank_euclideanSpace_fin] using h'
  have hcard : (q'.card : ℝ) ≤ (1 / (δ' : ℝ)) ^ 7 := by
    calc
      (q'.card : ℝ) ≤ _root_.Tube.card_le_of_EssDistinct.C 3 * (1 / (δ' : ℝ)) ^ 6 := hcard0
      _ ≤ (1 / (δ' : ℝ)) * (1 / (δ' : ℝ)) ^ 6 := by
          exact mul_le_mul_of_nonneg_right hCinv (by positivity)
      _ = (1 / (δ' : ℝ)) ^ 7 := by ring
  -- the logarithmic bound
  have hlog := dyadicPigeonholeNatConstant_le_pow_one_add_logb (δ := (δ' : ℝ)) hδ2
    (N := q'.card) (m := 7) hcard
  have hLnn : (0 : ℝ) ≤ 1 + Real.logb 2 (1 / (δ' : ℝ)) := by
    have hone : (1 : ℝ) < 2 := by norm_num
    have h := Real.logb_le_logb_of_le (b := 2) hone (by norm_num) hδ2
    rw [Real.logb_self_eq_one hone] at h
    linarith
  calc
    ((Kakeya.dyadicPigeonholeNatConstant q'.card : ℕ) : ENNReal)
        = ENNReal.ofReal ((Kakeya.dyadicPigeonholeNatConstant q'.card : ℕ) : ℝ) := by
          rw [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((1 + Real.logb 2 (1 / (δ' : ℝ))) ^ (7 + 1)) :=
          ENNReal.ofReal_le_ofReal hlog
    _ = ENNReal.ofReal (1 + Real.logb 2 (1 / (δ' : ℝ))) ^ 8 := by
          rw [ENNReal.ofReal_pow hLnn]
    _ ≤ (δ' : ENNReal) ^ (-ε) := h1


end Section6PartBData

end Kakeya

end

end
