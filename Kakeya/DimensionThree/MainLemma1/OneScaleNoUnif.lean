/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization

/-!
# GWZ Lemma 5.11 without Definition 2.2, and without an upper density bound

`Kakeya.ml1Boot.exists_factorOneScale` states GWZ Lemma 5.11 at the *interface* its intended
callers were expected to point at: a `ShadedTube.ShadedUniformTubeSet` witness, a bounded-overlap
witness, `0 < λ ≤ 1`, and a **two-sided** per-tube density bracket.  Its own docstring records
that "`_hunif`, `_hov` and the upper density bound in `hdens` are inert for every conclusion
below", and the underscores make that mechanical: the proof term does not mention them.

This file is that observation turned into a statement.  `Kakeya.ml1Boot.exists_factorOneScale_avg`
is `Kakeya.ml1Boot.exists_factorOneScale` with those four binders removed — same conclusion,
same proof, verified by the compiler.

## Why it matters, and why it is not cosmetic

The demand that a family be Definition 2.2 shaded-uniform *and* carry a two-sided per-tube
density bracket at the same time is the Main Lemma 1 blocker: it is
`Kakeya.ml1Boot.exists_uniformFactorCore`, and it is unavailable in either order — the shaded
uniformizer `ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` keeps the index set but
shrinks the shades, destroying a density lower bound proved beforehand, while the density
pigeonhole drops members with *nonempty* shading, which is exactly what
`ShadedTube.ShadedUniformTubeSet.restrict_of_shade_eq_empty` cannot absorb.

Blueprint §4 removes that demand from the *consumers*.  This file removes it from the
*producer*: after it, a one-scale factoring step needs only

* the carrier facts (`hball`, `hparent`, `hs0`), and
* a **one-sided** density lower bound `C_d⁻¹ λ |T| ≤ |Y(T)|`,

which is precisely the half of the bracket that `Kakeya.ml1Boot.regularizeOnFixedTree` supplies
on a fixed tree, and which — unlike the upper half — survives passing to a subfamily.  No
Definition 2.2 witness is needed at any point of the chain
`exists_factorOneScale_avg → B2 → B1 → B2 → B3`.

Nothing here weakens the conclusion: items (i)–(iv) are verbatim those of
`Kakeya.ml1Boot.exists_factorOneScale`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **GWZ Lemma 5.11 with the inert binders removed** (blueprint §4, producer side).

This is `Kakeya.ml1Boot.exists_factorOneScale` without its `ShadedUniformTubeSet` witness,
without its bounded-overlap witness, without `0 < λ ≤ 1`, and with the per-tube density
hypothesis reduced to its **lower** half.  The conclusion — items (i)–(iv) — is unchanged, and
the proof is the original one; those four binders never appear in it.

Consequently the one-scale factoring step consumes only what
`Kakeya.ml1Boot.regularizeOnFixedTree` produces on a fixed tree, and the chain to blueprint
`B3` never asks for GWZ Definition 2.2. -/
theorem exists_factorOneScale_avg (hdim : Module.finrank ℝ E = 3)
    {σ ρ : NNReal} (hσ0 : 0 < σ) (hσρ : σ ≤ ρ) (hρ1 : ρ ≤ 1)
    {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {t : Finset κ}
    (V : ι → ShadedTube σ E) (Vρ : κ → Tube ρ E) (p : ι → κ)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    {lam Cd : NNReal} (hCd : 1 ≤ Cd)
    (hdens : ∀ i ∈ s, (Cd : ENNReal)⁻¹ * (lam : ENNReal) * volume (V i).carrier
        ≤ volume (V i).shade)
    (hs0 : ∑ i ∈ s, volume (V i).carrier ≠ 0)
    (hparent : IsParentFamily s (fun i => (V i).toTube) t Vρ p) :
    ∃ t' ⊆ t, ∃ (Zρ : κ → ShadedTube ρ E) (Z' : ι → ShadedTube σ E),
      (∀ k ∈ t', (Zρ k).toTube = Vρ k) ∧
      (∀ i ∈ s, p i ∈ t' → (Z' i).toTube = (V i).toTube) ∧
      -- (i)
      ((Cd * factorOneScale.C s.card σ : NNReal) : ENNReal)⁻¹ * (lam : ENNReal)
          ≤ ShadedBody.fullness t' (fun k => (Zρ k).toShadedBody) ∧
      -- (ii)
      ((∀ i ∈ s, p i ∈ t' → (Z' i).shade ⊆ (V i).shade) ∧
        ShadedBody.IsCRefinement (s.filter fun i => p i ∈ t')
          (fun i => (Z' i).toShadedBody) s (fun i => (V i).toShadedBody)
          (factorOneScale.C s.card σ)⁻¹) ∧
      -- (iii)
      (∀ i ∈ s, p i ∈ t' → (Z' i).shade ⊆ (Zρ (p i)).shade) ∧
      -- (iv)
      ∀ k ∈ t', ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
        ≤ (factorOneScale.C s.card σ : ENNReal)
          * ShadedBody.multiplicity t' (fun k' => (Zρ k').toShadedBody)
          * ShadedBody.multiplicity (fibre (s.filter fun i => p i ∈ t') p k)
              (fun i => (Z' i).toShadedBody) := by
  classical
  haveI : Nontrivial E := Module.finrank_pos_iff.mp (by rw [hdim]; norm_num)
  have hcover : ∀ i ∈ s, (V i).toShadedBody.toConvexSpaceBody ≤ (Vρ (p i)).toConvexSpaceBody := by
    intro i hi
    simpa using hparent.le_parent i hi
  have hlam_lb : ∀ i ∈ s,
      (Cd : ENNReal)⁻¹ * ((lam : ENNReal) * volume (V i).toShadedBody.carrier)
        ≤ volume (V i).shade := by
    intro i hi
    simpa [mul_assoc] using hdens i hi
  let F : ShadedBody.FactorFamily E ι κ :=
    { innerSet := s
      innerBody := fun i => (V i).toShadedBody
      outerSet := t
      outerBody := fun k => (Vρ k).toConvexSpaceBody
      parent := p
      parent_mem := hparent.mapsTo
      inner_le_parent := hcover }
  have hinner : ∀ i ∈ F.innerSet, F.innerBody i = (V i).toShadedBody := by
    intro i hi
    rfl
  have houter : ∀ j ∈ F.outerSet, F.outerBody j = (Vρ j).toConvexSpaceBody := by
    intro j hj
    rfl
  have hCd0 : Cd ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hCd)
  obtain ⟨G, hG_outer, hG_inner, hG_parent, hSρ_bodyC, hT'_body, _hne, hfull, hcref, hmult,
      hpt, _hvol⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam hσ0 ⟨hσρ, hρ1⟩ hCd0 F V Vρ
      hinner houter
      (by
        intro i hi
        simpa [F] using hball i hi)
      (by simpa [F] using hs0)
      hlam_lb
  let t' : Finset κ := G.outerSet
  let Sρ : κ → ShadedBody E := G.outerBody
  let T' : ι → ShadedBody E := G.innerBody
  have ht'sub : t' ⊆ t := by simpa [t'] using hG_outer
  have hG_inner' : G.innerSet = s.filter (fun i => p i ∈ t') := by
    simpa [F, t'] using hG_inner
  have hSρ_body : ∀ k ∈ t', (Sρ k).carrier = (Vρ k).carrier := by
    intro k hk
    have hh := hSρ_bodyC k hk
    simpa [t', Sρ, F] using congrArg (fun b : ConvexSpaceBody E => b.carrier) hh
  let Zρ : κ → ShadedTube ρ E := fun k =>
    if hk : k ∈ t' then
      { toTube := Vρ k
        shade := (Sρ k).shade
        measurableSet_shade := (Sρ k).measurableSet_shade
        shade_subset := by
          rw [← hSρ_body k hk]
          exact (Sρ k).shade_subset }
    else
      { toTube := Vρ k
        shade := ∅
        measurableSet_shade := MeasurableSet.empty
        shade_subset := by simp }
  let Z' : ι → ShadedTube σ E := fun i =>
    if hi : i ∈ s.filter (fun i => p i ∈ t') then
      { toTube := (V i).toTube
        shade := (T' i).shade
        measurableSet_shade := (T' i).measurableSet_shade
        shade_subset := by
          have hi_s : i ∈ s := (Finset.mem_filter.mp hi).1
          have hbody : (T' i).toConvexSpaceBody = (V i).toConvexSpaceBody := by
            simpa using hT'_body i hi_s
          change (T' i).shade ⊆ (V i).toConvexSpaceBody.carrier
          rw [← hbody]
          exact (T' i).shade_subset }
    else
      { toTube := (V i).toTube
        shade := ∅
        measurableSet_shade := MeasurableSet.empty
        shade_subset := by simp }
  have hZρ_shade : ∀ k ∈ t', (Zρ k).shade = (Sρ k).shade := by
    intro k hk
    simp [Zρ, hk]
  have hZρ_carrier : ∀ k ∈ t', (Zρ k).carrier = (Sρ k).carrier := by
    intro k hk
    have hZ : (Zρ k).carrier = (Vρ k).carrier := by simp [Zρ, hk]
    rw [hZ, hSρ_body k hk]
  have hZ'_shade : ∀ i ∈ s.filter (fun i => p i ∈ t'), (Z' i).shade = (T' i).shade := by
    intro i hi
    have hi' : i ∈ s ∧ p i ∈ t' := Finset.mem_filter.mp hi
    simp [Z', hi']
  have hZ'_body : ∀ i ∈ s.filter (fun i => p i ∈ t'),
      (Z' i).toConvexSpaceBody = (T' i).toConvexSpaceBody := by
    intro i hi
    have hi' : i ∈ s ∧ p i ∈ t' := Finset.mem_filter.mp hi
    have hZ : (Z' i).toConvexSpaceBody = (V i).toConvexSpaceBody := by simp [Z', hi']
    rw [hZ]
    exact (hT'_body i hi'.1).symm
  refine ⟨t', ht'sub, Zρ, Z', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    simp [Zρ, hk]
  · intro i hi_s hip
    simp [Z', hi_s, hip]
  · -- (i)
    have hsum_shade : (∑ k ∈ t', volume ((Zρ k).toShadedBody).shade)
        = ∑ k ∈ t', volume (Sρ k).shade := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [hZρ_shade k hk]
    have hsum_carrier : (∑ k ∈ t', volume ((Zρ k).toShadedBody).carrier)
        = ∑ k ∈ t', volume (Sρ k).carrier := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [hZρ_carrier k hk]
    rw [show ShadedBody.fullness t' (fun k => (Zρ k).toShadedBody)
        = ShadedBody.fullness t' Sρ from by
          unfold ShadedBody.fullness ShadedBody.fullness'
          simp [hsum_shade, hsum_carrier]]
    have hC0 : Cd * factorOneScale.C s.card σ ≠ 0 := by
      unfold factorOneScale.C
      exact mul_ne_zero (ne_of_gt (lt_of_lt_of_le (by norm_num) hCd))
        (ne_of_gt (lt_of_lt_of_le (by norm_num)
          (ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.one_le_C 3 s.card σ 1)))
    have hfullNN : (Cd * factorOneScale.C s.card σ)⁻¹ * lam
        ≤ ShadedBody.fullness t' Sρ := by
      simpa [factorOneScale.C, hdim] using hfull
    rw [← ENNReal.coe_inv hC0, ← ENNReal.coe_mul]
    exact_mod_cast hfullNN
  · -- (ii)
    constructor
    · intro i hi_s hip
      have hi' : i ∈ G.innerSet := by
        rw [hG_inner']
        exact Finset.mem_filter.mpr ⟨hi_s, hip⟩
      simpa [Z', hi_s, hip] using (hcref.1.2 i hi').2
    · -- IsCRefinement
      constructor
      · constructor
        · rw [← hG_inner']
          simpa using hcref.1.1
        · intro i hi
          have hi' : i ∈ G.innerSet := by
            rw [hG_inner']
            exact hi
          constructor
          · simpa [hZ'_body i hi] using (hcref.1.2 i hi').1
          · simpa [hZ'_shade i hi] using (hcref.1.2 i hi').2
      · calc
          (factorOneScale.C s.card σ)⁻¹ * ∑ i ∈ s, volume ((V i).toShadedBody).shade
              ≤ ∑ i ∈ s.filter (fun i => p i ∈ t'), volume (T' i).shade := by
                simpa [factorOneScale.C, hdim, ← hG_inner'] using hcref.2
          _ = ∑ i ∈ s.filter (fun i => p i ∈ t'), volume ((Z' i).toShadedBody).shade := by
                apply Finset.sum_congr rfl
                intro i hi
                simp [hZ'_shade i hi]
  · -- (iii)
    intro i hi_s hip
    have hi : i ∈ s.filter (fun i => p i ∈ t') := Finset.mem_filter.mpr ⟨hi_s, hip⟩
    have hi' : i ∈ G.innerSet := by
      rw [hG_inner']
      exact hi
    simpa [Z', Zρ, hi_s, hip] using hpt i hi'
  · -- (iv)
    intro k hk
    have hfibre : fibre (s.filter fun i => p i ∈ t') p k = s.filter (fun i => p i = k) := by
      unfold fibre
      rw [Finset.filter_filter]
      exact Finset.filter_congr (fun i hi => by
        constructor
        · intro h; exact h.2
        · intro h; exact ⟨by rw [h]; exact hk, h⟩)
    have hG_fiber : (ShadedBody.ShadedFactorFamily.fiber G k : Finset ι) =
        fibre (s.filter fun i => p i ∈ t') p k := by
      simp [ShadedBody.ShadedFactorFamily.fiber, fibre, F, hG_inner', hG_parent]
    have hm := hmult k hk
    have hm' : ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
        ≤ (factorOneScale.C s.card σ : ENNReal)
          * ShadedBody.multiplicity t' Sρ
          * ShadedBody.multiplicity (s.filter (fun i => p i = k)) T' := by
      simpa [factorOneScale.C, hdim, F, t', Sρ, T', hG_fiber, hfibre] using hm
    have hmulZρ : ShadedBody.multiplicity t' (fun k' => (Zρ k').toShadedBody)
        = ShadedBody.multiplicity t' Sρ := by
      unfold ShadedBody.multiplicity
      congr 1
      · apply Finset.sum_congr rfl; intro k' hk'; simp [hZρ_shade k' hk']
      · apply congrArg volume
        apply Set.iUnion₂_congr
        intro k' hk'
        simp [hZρ_shade k' hk']
    have hmulZ' : ShadedBody.multiplicity (fibre (s.filter fun i => p i ∈ t') p k)
        (fun i => (Z' i).toShadedBody)
        = ShadedBody.multiplicity (s.filter (fun i => p i = k)) T' := by
      rw [hfibre]
      unfold ShadedBody.multiplicity
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        have hi' : i ∈ s.filter (fun i => p i ∈ t') := by
          have hi_s : i ∈ s := (Finset.mem_filter.mp hi).1
          have hpik : p i = k := (Finset.mem_filter.mp hi).2
          exact Finset.mem_filter.mpr ⟨hi_s, by rw [hpik]; exact hk⟩
        simp [hZ'_shade i hi']
      · apply congrArg volume
        apply Set.iUnion₂_congr
        intro i hi
        have hi' : i ∈ s.filter (fun i => p i ∈ t') := by
          have hi_s : i ∈ s := (Finset.mem_filter.mp hi).1
          have hpik : p i = k := (Finset.mem_filter.mp hi).2
          exact Finset.mem_filter.mpr ⟨hi_s, by rw [hpik]; exact hk⟩
        simp [hZ'_shade i hi']
    calc
      ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
          ≤ (factorOneScale.C s.card σ : ENNReal)
            * ShadedBody.multiplicity t' Sρ
            * ShadedBody.multiplicity (s.filter (fun i => p i = k)) T' := by
              exact hm'
      _ = (factorOneScale.C s.card σ : ENNReal)
            * ShadedBody.multiplicity t' (fun k' => (Zρ k').toShadedBody)
            * ShadedBody.multiplicity (fibre (s.filter fun i => p i ∈ t') p k)
                (fun i => (Z' i).toShadedBody) := by
            rw [hmulZρ, hmulZ']

/-! ## `B2` from the uniformity-free one-scale step

`Kakeya.ml1Boot.exists_factorOneScale_avg` supplies the carrier, retention and
fullness fields used by `B2`. The construction does not use `fine_unif`,
`coarse_unif`, `fibreUnif`, `frostman`, or a per-tube output bracket, so it
does not require GWZ Definition 2.2. -/
section B2

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- **`B2` from the uniformity-free one-scale step** (blueprint Section 9, Step 3).

The selected certificate uses `Kakeya.ml1Boot.exists_factorOneScale_avg` and
`Kakeya.ml1Boot.exists_selected_fibre`, with raw carrier data and the one-sided
density lower bound supplied by `Kakeya.ml1Boot.regularizeOnFixedTree`.

The retention is `c = C⁻¹` at `C = factorOneScale.C #act σ`, and the scalar
factor is `L = C`; the parent average fullness is item (i), at `(C_d C)⁻¹ λ`.
`hpos` is blueprint `B0`: nothing positive is produced from a null shading. -/
theorem exists_isOneScaleSelected_of_dens [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {σ ρ : NNReal} (hσ0 : 0 < σ) (hσρ : σ ≤ ρ) (hρ1 : ρ ≤ 1)
    {amb act : Finset ι} (hact : act ⊆ amb) {tAmb : Finset κ}
    (V : ι → ShadedTube σ E) (Vρ : κ → Tube ρ E) (p : ι → κ)
    (hoff : ∀ i ∈ amb, i ∉ act → (V i).shade = ∅)
    (hball : ∀ i ∈ act, (V i).carrier ⊆ Metric.closedBall 0 1)
    {lam Cd : NNReal} (hCd : 1 ≤ Cd)
    (hdens : ∀ i ∈ act, (Cd : ENNReal)⁻¹ * (lam : ENNReal) * volume (V i).carrier
      ≤ volume (V i).shade)
    (hs0 : ∑ i ∈ act, volume (V i).carrier ≠ 0)
    (hparent : IsParentFamily act (fun i => (V i).toTube) tAmb Vρ p)
    (hpos : 0 < ∑ i ∈ act, volume (V i).shade) :
    ∃ (act' : Finset ι) (Z' : ι → ShadedTube σ E) (tAct : Finset κ)
      (Zρ : κ → ShadedTube ρ E) (k₀ : κ) (lamF : NNReal),
      IsOneScaleSelected (((factorOneScale.C act.card σ)⁻¹ : NNReal) : ENNReal)
        ((factorOneScale.C act.card σ : NNReal) : ENNReal)
        amb act V tAmb Vρ p act' Z' tAct Zρ k₀
        ((Cd * factorOneScale.C act.card σ)⁻¹ * lam) lamF := by
  classical
  set C : NNReal := factorOneScale.C act.card σ with hC
  have hC1 : (1 : NNReal) ≤ C := one_le_factorOneScale_C _ _
  have hC0 : (0 : NNReal) < C := lt_of_lt_of_le one_pos hC1
  obtain ⟨t', ht'sub, Zρ, Z', hZρtube, hZ'tube, hfullP, hrefine, hcontain, hprod⟩ :=
    exists_factorOneScale_avg hdim hσ0 hσρ hρ1 V Vρ p hball hCd hdens hs0 hparent
  set act' : Finset ι := act.filter (fun i => p i ∈ t') with hact'
  have hact'sub : act' ⊆ act := Finset.filter_subset _ _
  have hact'amb : act' ⊆ amb := hact'sub.trans hact
  have hmaps : ∀ i ∈ act', p i ∈ t' := fun i hi => (Finset.mem_filter.mp hi).2
  -- positive child mass, from the true retention
  have hret : ((C⁻¹ : NNReal) : ENNReal) * ∑ i ∈ act, volume (V i).shade
      ≤ ∑ i ∈ act', volume (Z' i).shade := hrefine.2.2
  have hposZ : 0 < ∑ i ∈ act', volume (Z' i).shade := by
    refine lt_of_lt_of_le ?_ hret
    exact ENNReal.mul_pos (by simpa using (ENNReal.coe_pos.mpr (by positivity)).ne')
      hpos.ne'
  obtain ⟨k₀, hk₀, hk₀ne, hsel⟩ :=
    exists_selected_fibre (E := E) hσ0 hact'amb (p := p) (t := t') hmaps
      (fun i => (V i).toTube) Z' hposZ
  refine ⟨act', Z', t', Zρ, k₀,
    ShadedBody.fullness (fibre amb p k₀)
      (fun i => (selectedShade act' V Z' i).toShadedBody), ?_⟩
  have hmultamb : ShadedBody.multiplicity amb (fun i => (V i).toShadedBody)
      = ShadedBody.multiplicity act (fun i => (V i).toShadedBody) :=
    multiplicity_eq_of_shade_empty_off hact V hoff
  have hsummamb : ∑ i ∈ amb, volume (V i).shade = ∑ i ∈ act, volume (V i).shade :=
    sum_shade_eq_of_shade_empty_off hact V hoff
  refine
    { active_subset := hact
      shade_off := hoff
      child_subset := hact'sub
      child_shade := fun i hi =>
        ⟨hZ'tube i (hact'sub hi) (hmaps i hi), hrefine.1 i (hact'sub hi) (hmaps i hi)⟩
      child_retention := hret
      parent_subset := ht'sub
      parent_mapsTo := hmaps
      parent_tube := hZρtube
      parent_contain := fun i hi => hcontain i (hact'sub hi) (hmaps i hi)
      parent_fullness := ?_
      scalar := ?_
      sel_mem := hk₀
      sel_nonempty := hk₀ne
      sel_fullness := le_rfl
      sel_fullness_lb := ?_ }
  · -- item (i), with the `ℝ≥0` coercion of the constant
    have hcoe : (((Cd * C)⁻¹ * lam : NNReal) : ENNReal)
        = ((Cd * C : NNReal) : ENNReal)⁻¹ * (lam : ENNReal) := by
      rw [ENNReal.coe_mul, ENNReal.coe_inv (by positivity)]
    rw [hcoe]
    exact hfullP
  · intro k hk
    rw [hmultamb]
    exact hprod k hk
  · -- the ambient fullness comparison, with the retention `C⁻¹`
    refine le_trans ?_ hsel
    rw [ShadedBody.coe_fullness, ShadedBody.coe_fullness]
    have hnum : ∑ i ∈ amb, volume (selectedShade act' V Z' i).shade
        = ∑ i ∈ act', volume (Z' i).shade :=
      sum_volume_shade_zeroExtend_of_subset hact'amb _ Z'
    have hden : ∑ i ∈ amb, volume (selectedShade act' V Z' i).carrier
        = ∑ i ∈ amb, volume (V i).carrier :=
      Finset.sum_congr rfl fun i _ => volume_carrier_zeroExtend _ _ _ i
    show ((C⁻¹ : NNReal) : ENNReal)
        * ((∑ i ∈ amb, volume (V i).shade) / (∑ i ∈ amb, volume (V i).carrier))
      ≤ (∑ i ∈ amb, volume (selectedShade act' V Z' i).shade)
        / (∑ i ∈ amb, volume (selectedShade act' V Z' i).carrier)
    rw [hnum, hden, ← mul_div_assoc]
    refine ENNReal.div_le_div_right ?_ _
    rw [hsummamb]
    exact hret

end B2


end ml1Boot

end Kakeya

end
