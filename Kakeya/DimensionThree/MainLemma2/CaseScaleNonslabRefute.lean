/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyCase
public import Kakeya.DimensionThree.MainLemma2.SetupCarrierIsland
public import Kakeya.DimensionThree.MainLemma2.SetupAbsorption
public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.Thickness.Volume

/-!
# O5 as it stood was false in the non-slab regime: the refutation, and the repaired clause pinned

**What this file establishes.** The clause
`Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness` (blueprint obligation **O5** of
Configuration `hyp:ml2thinsetup`, the fullness `λ(𝒫, Y_𝒫) ⪆ (a')^η` of the plank family that
GWZ feed to Lemma 6.13, `gwz.txt` lines 979–980 and 2224–2236, where the `⪆` is rendered as a
plain `≥` with constant `1`) **without a transverse guard or a fixed middle dimension** — unguarded, with the
middle plank dimension `b'` unpinned — is **false** for every configuration in the non-slab
regime `cfg.b ≤ δ^{2·exscal}`, for every `bd`, every thin ball `tb`, and every sufficiently
small `δ`. That is `Kakeya.VeryNotSticky.false_of_transverseFill_fullness`, which takes the old
clause verbatim as its hypothesis `hO5` and is kept here as the compiled record of the refuted
text.

**The repair .**
The live field now carries the transverse-case guard `δ^{-τ'} a/b ≤ 1` (GWZ invoke Lemma 6.13
only when `θ ≥ δ^{-τ'} a/b`, l.2224, and `θ ≤ 1`) and the *upper* pin `b' ≤ C₀ (b/r₁)` beside
the two pins on `a'`, at the unchanged exponent `cfg.η`. Its exact text is pinned below as
`Kakeya.VeryNotSticky.statement_of_universal_caseScale_O5`, with
`Kakeya.VeryNotSticky.statement_of_universal_caseScale_O5_pinned` checking that the field is
that proposition and nothing else (the `statement_of_universal_*` device of
`Kakeya.ThinCase.Refute.statement_of_universal_loc`: a plain tripwire survives a binder added
in lockstep, this does not).

Their content survives as
`false_of_transverseFill_fullness` (the mathematics) and as the ledger fact that *both*
producers of a `Kakeya.VeryNotSticky` in the tree
(`Kakeya.VeryNotSticky.eventually_exists_veryNotSticky_of_localMass` through
`Kakeya.VeryNotSticky.exists_veryNotSticky_of_rhoCount`, and
`Kakeya.VeryNotSticky.eventually_exists_veryNotSticky` through
`Kakeya.VeryNotSticky.exists_veryNotSticky_of_data`, each with `hdims := ⟨le_rfl, le_rfl, _⟩`
on a singleton factoring part) set `a = b = δ`; the arithmetic lemma `caseParams_nonslab_gap`
they shared is kept, being true and independent of the clause.

**The argument** (`Kakeya.VeryNotSticky.false_of_transverseFill_fullness`). The plank family
`SP` in the old O5 is universally quantified with the middle plank dimension `b'` *unpinned*
(`{a' b'} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}`): only `a'` is tied to `a / r₁`. Take
`a' := a / r₁`, `b' := 1`, `t := tb.bodies'`, and for `SP i` the axis-aligned
`a' × 1 × 1` prism centred at `0` (`PrismNDim.mk'`) carrying a measurable shade of volume
exactly `|Y_{𝕎'_B}(W_i)| / (2 r₁)^3` (`Kakeya.VeryNotSticky.exists_subset_volume_eq`), which
is what the transport pin demands. Each body shade has volume
`≤ C_{vol}(3) · 8 · C₀^3 · r₁ · b · a`
(`Kakeya.ThinCase.ThinBall.W_le_cthickening`, `ConvexSpaceBody.volume_cthickening_le`,
`volume_le_prod_thickness`, `BallData.bodies_thickness`), while every plank carrier has volume
`8 a'` (`ShadedPlank.volume_carrier`); so the plank fullness is at most
`C_{vol}(3) · C₀^3 · b / (8 r₁) ≤ C_{vol}(3) · C₀^3 · r₁ / 8` in the non-slab regime, and
`CaseScale.transverse_fill` caps `C₀^3 ≤ δ^{-η/2}`. The old O5 demands `(a')^η ≥ (δ/r₁)^η =
δ^{(1-exscal)η}`; since `(3/2 - exscal)·η < exscal` (`CaseParams.slabDensity : 3η < exscal`
with `exscal < 1/2`), the two bounds are incompatible for all small `δ`.

Nothing here refutes the *repaired* clause, and nothing here bears on the exponent question
(plan §4.1; ruled on separately, (c)).
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody

universe u

/-- The volume-comparison constant of `ConvexSpaceBody.volume_cthickening_le` in `ℝ³`: the
only constant the refutation needs, and the constant in its smallness threshold. -/
noncomputable def nonslabRefuteConstant : NNReal := Metric.volume_comparison.C 3

/-- `C₀^3 ≤ X` from the clause shape `27 · max(1, C₀/3)^3 ≤ X` of
`Kakeya.VeryNotSticky.CaseScale.transverse_fill`. -/
lemma cube_le_of_transverse_fill {C₀ X : NNReal} (h : 27 * max 1 (C₀ / 3) ^ 3 ≤ X) :
    C₀ ^ 3 ≤ X := by
  calc C₀ ^ 3 = 27 * (C₀ / 3) ^ 3 := by
        rw [div_pow]
        have h27 : ((3 : NNReal) ^ 3) = 27 := by norm_num
        rw [h27, mul_div_cancel₀ _ (by norm_num : (27 : NNReal) ≠ 0)]
    _ ≤ 27 * max 1 (C₀ / 3) ^ 3 := by gcongr; exact le_max_right _ _
    _ ≤ X := h

/-- **The shade of a retained factoring body has volume `≤ C_{vol}(3) · 8 · C₀^3 · r₁ · b · a`.**
The outer shaded body of `Kakeya.ThinCase.ThinBall` sits inside the `scale`-thickening of the
geometric body (`W_le_cthickening`), whose volume is at most `C_{vol}(3)` times that of the body
(`ConvexSpaceBody.volume_cthickening_le`), and the body has thickness profile
`∼ (r₁, b, a)` at constant `C₀` (`BallData.bodies_thickness`), so its volume is at most
`2^3 · (C₀ r₁)(C₀ b)(C₀ a)` (`volume_le_prod_thickness`). -/
theorem thinBall_volume_shade_le (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {C : NNReal}
    {B : bd.bι} (hB : B ∈ bd.bs)
    (tb : ThinCase.ThinBall C bd.C₀ (bd.segs B) bd.Y (bd.bodies B) bd.Wb bd.blk
      cfg.δ cfg.a cfg.η)
    {j : bd.ω} (hj : j ∈ tb.bodies') :
    volume (tb.W j).shade ≤
      ((nonslabRefuteConstant * 8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.b * cfg.a : NNReal) : ENNReal) := by
  have hj' : j ∈ bd.bodies B := tb.bodies'_subset hj
  have ht := bd.bodies_thickness B hB j hj'
  have hsc : (0 : ℝ) ≤ (bd.Wb j).scale := Metric.thickness_nonneg _ _
  have h1 : volume (tb.W j).shade ≤
      volume ((bd.Wb j).cthickening (bd.Wb j).scale).carrier := by
    refine measure_mono ((tb.W j).shade_subset.trans ?_)
    exact SetLike.coe_subset_coe.mpr (tb.W_le_cthickening j hj)
  have h2 := ConvexSpaceBody.volume_cthickening_le (bd.Wb j) ⟨(bd.Wb j).scale, hsc⟩ le_rfl
  have h3 := volume_le_prod_thickness (bd.Wb j).isBounded
  rw [finrank_euclideanSpace_fin] at h2 h3
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul] at h3
  have e0 : Metric.thickness ℝ (bd.Wb j).carrier 0 ≤ (bd.C₀ : ℝ) * cfg.r₁ := by
    simpa using (ht 0).2
  have e1 : Metric.thickness ℝ (bd.Wb j).carrier 1 ≤ (bd.C₀ : ℝ) * cfg.b := by
    simpa using (ht 1).2
  have e2 : Metric.thickness ℝ (bd.Wb j).carrier 2 ≤ (bd.C₀ : ℝ) * cfg.a := by
    simpa using (ht 2).2
  have f0 : ENNReal.ofReal (Metric.thickness ℝ (bd.Wb j).carrier 0) ≤
      (bd.C₀ : ENNReal) * (cfg.r₁ : ENNReal) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    exact ENNReal.ofReal_le_ofReal e0
  have f1 : ENNReal.ofReal (Metric.thickness ℝ (bd.Wb j).carrier 1) ≤
      (bd.C₀ : ENNReal) * (cfg.b : ENNReal) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    exact ENNReal.ofReal_le_ofReal e1
  have f2 : ENNReal.ofReal (Metric.thickness ℝ (bd.Wb j).carrier 2) ≤
      (bd.C₀ : ENNReal) * (cfg.a : ENNReal) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    exact ENNReal.ofReal_le_ofReal e2
  calc volume (tb.W j).shade
      ≤ volume ((bd.Wb j).cthickening (bd.Wb j).scale).carrier := h1
    _ ≤ (Metric.volume_comparison.C 3 : ENNReal) * volume (bd.Wb j).carrier := h2
    _ ≤ (Metric.volume_comparison.C 3 : ENNReal) *
          (2 ^ 3 * (ENNReal.ofReal (Metric.thickness ℝ (bd.Wb j).carrier 0) *
            ENNReal.ofReal (Metric.thickness ℝ (bd.Wb j).carrier 1) *
            ENNReal.ofReal (Metric.thickness ℝ (bd.Wb j).carrier 2))) := by
        gcongr
        exact h3
    _ ≤ (Metric.volume_comparison.C 3 : ENNReal) *
          (2 ^ 3 * (((bd.C₀ : ENNReal) * (cfg.r₁ : ENNReal)) *
            ((bd.C₀ : ENNReal) * (cfg.b : ENNReal)) *
            ((bd.C₀ : ENNReal) * (cfg.a : ENNReal)))) := by gcongr
    _ = ((nonslabRefuteConstant * 8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.b * cfg.a : NNReal) :
          ENNReal) := by
        simp only [nonslabRefuteConstant]
        push_cast
        ring

/-- **The pre-repair O5 is false in the non-slab regime — the core.** From the clause
`Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness` **without a transverse guard or a fixed middle dimension** (here the hypothesis `hO5`, verbatim: no transverse guard, `b'` unpinned),
the cap `C₀^3 ≤ δ^{-η/2}` (from `CaseScale.transverse_fill` via
`Kakeya.VeryNotSticky.cube_le_of_transverse_fill`), the non-slab hypothesis
`b ≤ δ^{2·exscal}` and the smallness threshold
`C_{vol}(3) · δ^{exscal - η/2} ≤ δ^{(1 - exscal)·η}`, a contradiction.

The plank family is `a' := a/r₁`, `b' := 1`, `t := tb.bodies'`, and `SP i` the axis-aligned
`a' × 1 × 1` prism at `0` with a shade of volume exactly `|Y_{𝕎'_B}(W_i)| / (2r₁)^3`.

This statement is kept as the record of the refuted text. The live field is
`Kakeya.VeryNotSticky.statement_of_universal_caseScale_O5` below; it does not entail `hO5`
(the guard fails at `a = b`, and the upper pin excludes `b' = 1`), so no corollary about a
`CaseScale` or a `CaseSideData` follows from this theorem any more. -/
theorem false_of_transverseFill_fullness (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    {C : NNReal} {B : bd.bι} (hB : B ∈ bd.bs)
    (tb : ThinCase.ThinBall C bd.C₀ (bd.segs B) bd.Y (bd.bodies B) bd.Wb bd.blk
      cfg.δ cfg.a cfg.η)
    (hb : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    (hexscal1 : cfg.exscal ≤ 1)
    (hsmall : nonslabRefuteConstant * cfg.δ ^ (cfg.exscal - cfg.η / 2) ≤
      cfg.δ ^ ((1 - cfg.exscal) * cfg.η))
    (hC3 : bd.C₀ ^ 3 ≤ cfg.δ ^ (-(cfg.η / 2)))
    (hO5 : ∀ {a' b' : NNReal} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}
      (t : Finset bd.ω) (SP : bd.ω → ShadedPlank a' b' hab' hb1'),
      t ⊆ tb.bodies' →
      bd.C₀⁻¹ * (cfg.a / cfg.r₁) ≤ a' → a' ≤ bd.C₀ * (cfg.a / cfg.r₁) →
      ((plankSelectionConstant bd.C₀ : ENNReal))⁻¹ *
          (∑ i ∈ tb.bodies', volume (tb.W i).shade) ≤ ∑ i ∈ t, volume (tb.W i).shade →
      (∀ i ∈ t, volume (ShadedPlank.bodies SP i).shade * ENNReal.ofReal ((2 * (cfg.r₁ : ℝ)) ^ 3)
        = volume (tb.W i).shade) →
      a' ^ cfg.η ≤ ShadedBody.fullness t (ShadedPlank.bodies SP)) : False := by
  classical
  -- scales
  have hd0 : 0 < cfg.δ := cfg.hδ
  have hdne : cfg.δ ≠ 0 := hd0.ne'
  have hr₁ : cfg.r₁ = cfg.δ ^ cfg.exscal := rfl
  have hr0 : 0 < cfg.r₁ := by rw [hr₁]; exact NNReal.rpow_pos hd0
  have hrne : cfg.r₁ ≠ 0 := hr0.ne'
  obtain ⟨hδa, hab, hbr⟩ := cfg.hdims
  have hbr' : cfg.b ≤ cfg.r₁ := by rw [hr₁]; exact hbr
  have har : cfg.a ≤ cfg.r₁ := hab.trans hbr'
  have hb2 : cfg.b ≤ cfg.r₁ ^ 2 := by
    refine hb.trans (le_of_eq ?_)
    rw [hr₁, mul_comm, NNReal.rpow_mul, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      NNReal.rpow_natCast]
  -- the short plank dimension
  set a' : NNReal := cfg.a / cfg.r₁ with ha'
  have hab' : a' ≤ 1 := div_le_one_of_le₀ har zero_le
  -- the two constants of the bound
  set Xn : NNReal := nonslabRefuteConstant * bd.C₀ ^ 3 * cfg.b / (8 * cfg.r₁) with hXn
  set Mn : NNReal := nonslabRefuteConstant * 8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.b * cfg.a with hMn
  have hMX : Mn = Xn * (8 * a') * (2 * cfg.r₁) ^ 3 := by
    rw [hMn, hXn, ha']
    apply NNReal.coe_injective
    push_cast
    have : (cfg.r₁ : ℝ) ≠ 0 := by exact_mod_cast hrne
    field_simp
    ring
  have hXle : Xn ≤ cfg.δ ^ ((1 - cfg.exscal) * cfg.η) / 8 := by
    have hpow : cfg.δ ^ (cfg.exscal - cfg.η / 2) = cfg.r₁ * cfg.δ ^ (-(cfg.η / 2)) := by
      rw [sub_eq_add_neg, NNReal.rpow_add hdne, hr₁]
    calc Xn = nonslabRefuteConstant * bd.C₀ ^ 3 * cfg.b / (8 * cfg.r₁) := rfl
      _ ≤ nonslabRefuteConstant * cfg.δ ^ (-(cfg.η / 2)) * cfg.r₁ ^ 2 / (8 * cfg.r₁) := by
          gcongr
      _ = nonslabRefuteConstant * cfg.δ ^ (cfg.exscal - cfg.η / 2) / 8 := by
          rw [hpow]
          apply NNReal.coe_injective
          push_cast
          have : (cfg.r₁ : ℝ) ≠ 0 := by exact_mod_cast hrne
          field_simp
      _ ≤ cfg.δ ^ ((1 - cfg.exscal) * cfg.η) / 8 := by gcongr
  have hX1 : Xn ≤ 1 := by
    refine hXle.trans ?_
    have h1 : cfg.δ ^ ((1 - cfg.exscal) * cfg.η) ≤ 1 :=
      NNReal.rpow_le_one cfg.hδ1 (mul_nonneg (by linarith) cfg.hη.le)
    calc cfg.δ ^ ((1 - cfg.exscal) * cfg.η) / 8 ≤ 1 / 8 := by gcongr
      _ ≤ 1 := div_le_one_of_le₀ (by norm_num) zero_le
  -- the plank: the axis-aligned `a' × 1 × 1` prism at the origin
  let P : Plank a' 1 hab' le_rfl :=
    { toPrismNDim := PrismNDim.mk' (0 : EuclideanSpace ℝ (Fin 3))
        (EuclideanSpace.basisFun (Fin 3) ℝ) ![a', 1, 1]
      thicknesses_eq := rfl }
  have hPvol : volume P.carrier = 8 * (a' : ENNReal) := by
    rw [Prism3D.volume_carrier]; simp
  have hPmeas : MeasurableSet P.carrier := PrismNDim.measurableSet_carrier _
  have hPball : P.carrier ⊆ closedBall 0 (∑ i, (P.thicknesses i : ℝ)) :=
    PrismNDim.carrier_subset_closedBall P.toPrismNDim
  -- the prescribed shade volumes
  set c3 : NNReal := (2 * cfg.r₁) ^ 3 with hc3
  have hc3ne : c3 ≠ 0 := by rw [hc3]; positivity
  have hc3E : ENNReal.ofReal ((2 * (cfg.r₁ : ℝ)) ^ 3) = (c3 : ENNReal) := by
    rw [← ENNReal.ofReal_coe_nnreal, hc3]; push_cast; ring_nf
  let m : bd.ω → ENNReal := fun i => volume (tb.W i).shade / (c3 : ENNReal)
  have hm_le : ∀ i ∈ tb.bodies', m i ≤ ((Xn * (8 * a') : NNReal) : ENNReal) := by
    intro i hi
    have h := thinBall_volume_shade_le cfg bd hB tb hi
    calc m i = volume (tb.W i).shade / (c3 : ENNReal) := rfl
      _ ≤ (Mn : ENNReal) / (c3 : ENNReal) := by gcongr
      _ = ((Mn / c3 : NNReal) : ENNReal) := (ENNReal.coe_div hc3ne).symm
      _ = ((Xn * (8 * a') : NNReal) : ENNReal) := by
          rw [hMX, hc3, mul_div_cancel_right₀ _ hc3ne]
  have hm_adm : ∀ i ∈ tb.bodies', m i ≤ volume P.carrier := by
    intro i hi
    calc m i ≤ ((Xn * (8 * a') : NNReal) : ENNReal) := hm_le i hi
      _ ≤ (((1 : NNReal) * (8 * a') : NNReal) : ENNReal) := by gcongr
      _ = 8 * (a' : ENNReal) := by push_cast; ring
      _ = volume P.carrier := hPvol.symm
  have hex : ∀ i : bd.ω, ∃ S : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet S ∧
      S ⊆ P.carrier ∧ (i ∈ tb.bodies' → volume S = m i) := by
    intro i
    by_cases hi : i ∈ tb.bodies'
    · obtain ⟨S, hS1, hS2, hS3⟩ := exists_subset_volume_eq hPmeas
        (Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _) hPball (hm_adm i hi)
      exact ⟨S, hS1, hS2, fun _ => hS3⟩
    · exact ⟨∅, MeasurableSet.empty, empty_subset _, fun h => absurd h hi⟩
  choose S hSm hSsub hSvol using hex
  let SP : bd.ω → ShadedPlank a' 1 hab' le_rfl := fun i =>
    { toPrism3D := P
      shade := S i
      measurableSet_shade := hSm i
      shade_subset := hSsub i }
  -- the four pins
  have hpin1 : bd.C₀⁻¹ * (cfg.a / cfg.r₁) ≤ a' :=
    mul_le_of_le_one_left zero_le (inv_le_one_of_one_le₀ bd.hC₀)
  have hpin2 : a' ≤ bd.C₀ * (cfg.a / cfg.r₁) := le_mul_of_one_le_left zero_le bd.hC₀
  have hret : ((plankSelectionConstant bd.C₀ : ENNReal))⁻¹ *
      (∑ i ∈ tb.bodies', volume (tb.W i).shade) ≤ ∑ i ∈ tb.bodies', volume (tb.W i).shade :=
    mul_le_of_le_one_left zero_le
      (ENNReal.inv_le_one.mpr (by exact_mod_cast one_le_plankSelectionConstant bd.C₀))
  have hvol : ∀ i ∈ tb.bodies', volume (ShadedPlank.bodies SP i).shade *
      ENNReal.ofReal ((2 * (cfg.r₁ : ℝ)) ^ 3) = volume (tb.W i).shade := by
    intro i hi
    change volume (S i) * _ = _
    rw [hSvol i hi, hc3E]
    exact ENNReal.div_mul_cancel (by exact_mod_cast hc3ne) ENNReal.coe_ne_top
  have hO5' : a' ^ cfg.η ≤ ShadedBody.fullness tb.bodies' (ShadedPlank.bodies SP) :=
    hO5 tb.bodies' SP subset_rfl hpin1 hpin2 hret hvol
  -- the fullness of the plank family is at most `Xn`
  have hfull : ShadedBody.fullness tb.bodies' (ShadedPlank.bodies SP) ≤ Xn := by
    rw [← ENNReal.coe_le_coe, ShadedBody.fullness_def]
    apply ENNReal.div_le_of_le_mul
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hcar : volume (ShadedPlank.bodies SP i).carrier = 8 * (a' : ENNReal) := by
      change volume (SP i).carrier = _
      rw [ShadedPlank.volume_carrier]; simp
    rw [hcar]
    change volume (S i) ≤ _
    rw [hSvol i hi]
    calc m i ≤ ((Xn * (8 * a') : NNReal) : ENNReal) := hm_le i hi
      _ = (Xn : ENNReal) * (8 * (a' : ENNReal)) := by push_cast; ring
  -- `(δ/r₁)^η ≤ (a')^η`
  have hlow : cfg.δ ^ ((1 - cfg.exscal) * cfg.η) ≤ a' ^ cfg.η := by
    rw [NNReal.rpow_mul]
    apply NNReal.rpow_le_rpow _ cfg.hη.le
    rw [NNReal.rpow_sub hdne, NNReal.rpow_one, ha', ← hr₁]
    gcongr
  -- the contradiction: `x ≤ x / 8` with `x > 0`
  have hfinal : cfg.δ ^ ((1 - cfg.exscal) * cfg.η) ≤ cfg.δ ^ ((1 - cfg.exscal) * cfg.η) / 8 :=
    hlow.trans (hO5'.trans (hfull.trans hXle))
  have hpos : 0 < cfg.δ ^ ((1 - cfg.exscal) * cfg.η) := NNReal.rpow_pos hd0
  exact absurd hfinal (not_le.mpr (div_lt_self hpos (by norm_num)))

/-- The exponent gap `(1 - exscal)·η < exscal - η/2` follows from the case-split budget
`Kakeya.VeryNotSticky.CaseParams.slabDensity : 6η < exscal` (with `0 < η`, `0 < exscal`). -/
lemma caseParams_nonslab_gap {β ζ exscal ϱ η τ τ' : ℝ} (params : CaseParams β ζ exscal ϱ η τ τ')
    (hη : 0 < η) (hexscal : 0 < exscal) : (1 - exscal) * η < exscal - η / 2 := by
  have h1 := params.slabDensity
  have h2 : 0 ≤ exscal * η := mul_nonneg hexscal.le hη.le
  nlinarith

/-! ### The repaired clause, pinned

The `statement_of_universal_*` device (`Kakeya.ThinCase.Refute.statement_of_universal_loc`,
`Kakeya.Prop66BScale.statement_of_universal_prop66B_essDistinct`): the licensed text of the
field is a named `Prop`, and a theorem checks that the field *is* that proposition. A later
change to the field in either direction — a binder dropped, a pin removed, the guard weakened,
an exponent moved — fails to elaborate here, which a plain tripwire on a consumer would not
notice when the change is made in lockstep. -/

/-- **The clause O5 with its thin and transverse guards, as a named `Prop`**: the thin
guard `a ≤ δ^{1-τ}` (GWZ l.2176, the definition of §9.5's case) and the transverse guard
`δ^{-τ'} a/b ≤ 1` in front (GWZ l.2224, `θ ≤ 1`), the two pins on `a'` and the *upper* pin
`b' ≤ C₀ (b/r₁)` on `b'`, the two pins on `t` and `SP`, and the conclusion at the unchanged
exponent `cfg.η`. It is the text of `Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness`
verbatim, at the parameters `(cfg, bd, τ, τ', C)` the field reads. -/
def statement_of_universal_caseScale_O5 (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (τ τ' : ℝ) (C : NNReal) : Prop :=
  cfg.a ≤ cfg.δ ^ (1 - τ) →
    cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ 1 →
    ∀ (B : bd.bι) (_hB : B ∈ bd.bs)
    (tb : ThinCase.ThinBall C bd.C₀ (bd.segs B) bd.Y (bd.bodies B) bd.Wb bd.blk
      cfg.δ cfg.a (2 * cfg.η))
    {a' b' : NNReal} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}
    (t : Finset bd.ω) (SP : bd.ω → ShadedPlank a' b' hab' hb1'),
    t ⊆ tb.bodies' →
    bd.C₀⁻¹ * (cfg.a / cfg.r₁) ≤ a' → a' ≤ bd.C₀ * (cfg.a / cfg.r₁) →
    b' ≤ bd.C₀ * (cfg.b / cfg.r₁) →
    ((plankSelectionConstant bd.C₀ : ENNReal))⁻¹ *
        (∑ i ∈ tb.bodies', volume (tb.W i).shade) ≤ ∑ i ∈ t, volume (tb.W i).shade →
    (∀ i ∈ t, volume (ShadedPlank.bodies SP i).shade * ENNReal.ofReal ((2 * (cfg.r₁ : ℝ)) ^ 3)
      = volume (tb.W i).shade) →
    a' ^ (16 * cfg.η) ≤ ShadedBody.fullness t (ShadedPlank.bodies SP)

/-- **The pin.** The field `Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness` is
`statement_of_universal_caseScale_O5` by unfolding and nothing else: the proof term is the
projection itself. -/
theorem statement_of_universal_caseScale_O5_pinned (cfg : VeryNotSticky.{u})
    (bd : BallData cfg) {τ τ' ν : ℝ} {C : NNReal} {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' ν C thr) :
    statement_of_universal_caseScale_O5 cfg bd τ τ' C :=
  scale.transverseFill_fullness

end Kakeya.VeryNotSticky
