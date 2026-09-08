/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.ShadedRestrict
public import Kakeya.Pigeonhole
public import Kakeya.Tube.Dilate
public import Kakeya.Factoring.Pigeonhole

/-!
# Definition 2.2 and a density bracket at once, for a disjointly shaded family

`Kakeya.ml1Boot.exists_uniformFactorCore` needs a family that is *simultaneously* GWZ
Definition 2.2 uniform and two-sidedly density-banded.  The recorded obstruction is that the two
demands destroy each other: the shaded uniformizers of `Kakeya/ShadedUniform.lean` obtain
Definition 2.2 by *cutting shadings*, which destroys any per-tube volume band, while the density
band is obtained by a pigeonhole that *moves the index set*, which destroys Definition 2.2 —
`ShadedTube.ShadedUniformTubeSet` is not hereditary, its two lower brackets
`le_card_shadeClass` and `le_branchingN` failing under restriction.

`ShadedTube.nonempty_shadedUniformTubeSet_of_pairwiseDisjoint` breaks that circle for a family
whose shadings are **pairwise disjoint**: for such a family Definition 2.2 is a consequence of
tube uniformity alone, and — this is the point — *disjointness is hereditary*, so the conclusion
survives every later pigeonhole on the index set.  The theorem below is the resulting composite:
density band first, tube uniformization second, Definition 2.2 read off at the end.

## What it costs, and why that is the whole remaining question

Nothing here loses more than a polylogarithm *given* the disjointness.  The route to disjointness
is `ShadedTube.exists_shade_disjointification`, which retains
`|⋃_{i ∈ s} Y(V_i)|` out of `∑_{i ∈ s} |Y(V_i)|`, that is a `1 / µ(𝕍, Y)` fraction, where `µ` is
the multiplicity of the original family.  So this route supplies the Section 2 interface with
total loss `δ^{-o(1)} · µ(𝕍, Y)`, in place of the `δ^{-o(1)}` the interface is stated at.

`µ(𝕍, Y)` is exactly the quantity Main Lemma 1 exists to bound, so on the **fine** family of
`Kakeya.ml1Boot.IsUniformFactorCore` this trade is circular and the route does not close
`fine_refinement`.  It is *not* circular wherever the multiplicity of the family being uniformized
is already controlled — in particular for the coarse and middle families of the two-scale chain,
whose multiplicities are the outputs of `Kakeya.ml1Boot.exists_factorOneScale`, which is proved.
Whether that is enough is the sharp remaining question at
`Kakeya.ml1Boot.exists_uniformFactorCore`; this file makes it a question about one number rather
than about the existence of an interface.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

universe u

namespace ShadedTube

variable
  {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-- **A disjointly shaded family has a density-banded, Definition 2.2 uniform refinement, at
polylogarithmic cost.**

The input is a family of shaded `δ`-tubes in the unit ball whose shadings are pairwise disjoint
and bounded below in density by `a`; the cardinality budget `#s ≤ δ^{-K₀}` is the one
`Tube.exists_uniformTubeSet_subfamily_ssf` charges.  The output is a *subfamily* — the shadings
are never touched — carrying

* a two-sided density band at a level `lam ≥ a`;
* GWZ Definition 2.2 at the grid length `Tube.ssfGridLen δ` and the constant
  `ShadedTube.ssfUniformConst`;
* mass retention `∑_{i ∈ s} |Y(V_i)| ≤ 2 δ^{-α} (1 + log₂ (1/a)) ∑_{i ∈ s'} |Y(V_i)|`.

The two selections are made in the order that lets both conclusions stand: the density band
first, since it is hereditary, and the tube uniformization second, since Definition 2.2 is then
read off the retained tube hierarchy and the retained disjointness by
`ShadedTube.nonempty_shadedUniformTubeSet_of_pairwiseDisjoint`.  Reversing the order would lose
the uniformity at the density pigeonhole; that reversal is the recorded blocker of
`Kakeya.ml1Boot.exists_uniformFactorCore`.

The band pigeonhole loses mass and not cardinality, and the uniformizer loses cardinality and not
mass; the band is what converts the second into the first, at the factor `2` of its own
bracket. -/
theorem exists_shadedUniform_banded_of_pairwiseDisjoint (K₀ : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (s : Finset ι) (W : ι → ShadedTube δ E) (a : NNReal),
      (∀ i ∈ s, (W i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (s.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
      s.Nonempty → 0 < a → a ≤ 1 →
      (∀ i ∈ s, (a : ENNReal) * volume (W i).carrier ≤ volume (W i).shade) →
      (s : Set ι).Pairwise (fun i j => Disjoint (W i).shade (W j).shade) →
      ∃ s' ⊆ s, ∃ lam : NNReal, a ≤ lam ∧
        (∀ i ∈ s', (lam : ENNReal) * volume (W i).carrier ≤ volume (W i).shade ∧
          volume (W i).shade ≤ 2 * (lam : ENNReal) * volume (W i).carrier) ∧
        (∑ i ∈ s, volume (W i).shade)
            ≤ ENNReal.ofReal (2 * (δ : ℝ) ^ (-α) * (1 + Real.logb 2 ((a : ℝ))⁻¹))
              * ∑ i ∈ s', volume (W i).shade ∧
        Nonempty (ShadedUniformTubeSet s' W (Tube.ssfGridLen δ)
          (ssfUniformConst (Module.finrank ℝ E))) := by
  classical
  obtain ⟨δ₀, hδ₀pos, hδ₀le1, hunif⟩ :=
    Tube.exists_uniformTubeSet_subfamily_ssf (E := E) K₀ α hα
  refine ⟨δ₀, hδ₀pos, hδ₀le1, ?_⟩
  intro ι δ hδ hδδ₀ s W a hball hcard hs ha0 ha1 hdens hdisj
  -- the common carrier volume of a `δ`-tube
  obtain ⟨i₀, hi₀⟩ := hs
  set v : ENNReal := volume (W i₀).carrier with hv_def
  have hvol : ∀ i ∈ s, volume ((fun i => (W i).toShadedBody) i).carrier = v := by
    intro i _
    rw [hv_def]
    exact Tube.volume_carrier_eq_volume_carrier (W i).toTube (W i₀).toTube
  have hvpos : 0 < v := by
    rw [hv_def]
    have hle := Tube.le_volume (W i₀).toTube
    have hc : 0 < (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) :=
      ENNReal.coe_pos.mpr (Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hδp : 0 < (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ) _
    exact lt_of_lt_of_le (ENNReal.mul_pos (ne_of_gt hc) (ne_of_gt hδp)) (by simpa using hle)
  have hvne : v ≠ 0 := ne_of_gt hvpos
  -- Step 1: the dyadic density band.
  obtain ⟨s₂, hs₂sub, lam, hlam0, hcref, hband, halam, _hfull⟩ :=
    ShadedBody.exists_isCRefinement_comparable_density (s := s)
      (V := fun i => (W i).toShadedBody) (v := v) (a := a) ⟨i₀, hi₀⟩ hvol hvne ha0 ha1 hdens
  -- Step 2: tube uniformization of the banded subfamily.
  have hball₂ : ∀ i ∈ s₂, ((fun i => (W i).toTube) i).carrier ⊆ Metric.closedBall (0 : E) 1 :=
    fun i hi => hball i (hs₂sub hi)
  have hcard₂ : (s₂.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) :=
    le_trans (by exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hs₂sub)) hcard
  obtain ⟨s₃, hs₃sub, hcard₃, hU⟩ :=
    hunif hδ hδδ₀ s₂ (fun i => (W i).toTube) hball₂ hcard₂
  have hs₃s : s₃ ⊆ s := fun i hi => hs₂sub (hs₃sub hi)
  -- Step 3: Definition 2.2 on `s₃`, from tube uniformity and the retained disjointness.
  have hdisj₃ : (s₃ : Set ι).Pairwise fun i j => Disjoint (W i).shade (W j).shade :=
    hdisj.mono (by exact_mod_cast hs₃s)
  have hstruct : Nonempty (ShadedUniformTubeSet s₃ W (Tube.ssfGridLen δ)
      (ssfUniformConst (Module.finrank ℝ E))) :=
    nonempty_shadedUniformTubeSet_of_pairwiseDisjoint hU.some
      (uniformConst_le_ssfUniformConst _) (one_le_ssfUniformConst _) hdisj₃
  refine ⟨s₃, hs₃s, lam, halam, fun i hi => hband i (hs₃sub hi), ?_, hstruct⟩
  -- Step 4: the mass accounting.
  set L : ℝ := 1 + Real.logb 2 ((a : ℝ))⁻¹ with hL_def
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have haR1 : (a : ℝ) ≤ 1 := by exact_mod_cast ha1
  have hlogb : (0 : ℝ) ≤ Real.logb 2 ((a : ℝ))⁻¹ := by
    apply Real.logb_nonneg (by norm_num)
    rw [le_inv_comm₀ (by norm_num) haR]
    simpa using haR1
  have hL1 : (1 : ℝ) ≤ L := by rw [hL_def]; linarith
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  -- the band refinement, in multiplicative form
  have hmass₂ : (∑ i ∈ s, volume (W i).shade)
      ≤ ENNReal.ofReal L * ∑ i ∈ s₂, volume (W i).shade := by
    have h := hcref.2
    have hcoe : ((L.toNNReal : NNReal) : ENNReal) = ENNReal.ofReal L := by
      simp [Real.toNNReal, ENNReal.ofReal]
    have hne : (L.toNNReal : NNReal) ≠ 0 := by
      simp only [ne_eq, Real.toNNReal_eq_zero]
      exact not_le.mpr hLpos
    have h' : ((L.toNNReal)⁻¹ : NNReal) * (∑ i ∈ s, volume ((W i).toShadedBody).shade : ENNReal)
        ≤ ∑ i ∈ s₂, volume ((W i).toShadedBody).shade := by
      simpa [hL_def] using h
    rw [ENNReal.coe_inv hne, ← ENNReal.div_eq_inv_mul, ENNReal.div_le_iff_le_mul
      (Or.inl (by simpa [hcoe] using (ENNReal.ofReal_pos.mpr hLpos).ne'))
      (Or.inl (by simp [hcoe]))] at h'
    calc (∑ i ∈ s, volume (W i).shade)
        ≤ (∑ i ∈ s₂, volume ((W i).toShadedBody).shade) * ((L.toNNReal : NNReal) : ENNReal) := h'
      _ = ENNReal.ofReal L * ∑ i ∈ s₂, volume (W i).shade := by
          rw [hcoe]; ring
  -- from cardinality to mass, using the band
  have hlamv : (0 : ENNReal) < (lam : ENNReal) * v :=
    ENNReal.mul_pos (by exact_mod_cast (lt_of_lt_of_le ha0 halam).ne') hvne
  have hbandv : ∀ i ∈ s₂, (lam : ENNReal) * v ≤ volume (W i).shade ∧
      volume (W i).shade ≤ 2 * (lam : ENNReal) * v := by
    intro i hi
    have h := hband i hi
    rw [hvol i (hs₂sub hi)] at h
    exact h
  have hsum₂le : (∑ i ∈ s₂, volume (W i).shade)
      ≤ (s₂.card : ENNReal) * (2 * (lam : ENNReal) * v) := by
    calc (∑ i ∈ s₂, volume (W i).shade)
        ≤ ∑ _i ∈ s₂, 2 * (lam : ENNReal) * v :=
          Finset.sum_le_sum fun i hi => (hbandv i hi).2
      _ = (s₂.card : ENNReal) * (2 * (lam : ENNReal) * v) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hsum₃ge : (s₃.card : ENNReal) * ((lam : ENNReal) * v) ≤ ∑ i ∈ s₃, volume (W i).shade := by
    calc (s₃.card : ENNReal) * ((lam : ENNReal) * v)
        = ∑ _i ∈ s₃, (lam : ENNReal) * v := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s₃, volume (W i).shade :=
          Finset.sum_le_sum fun i hi => (hbandv i (hs₃sub hi)).1
  have hcardE : (s₂.card : ENNReal)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-α)) * (s₃.card : ENNReal) := by
    have h := hcard₃
    have h' : ENNReal.ofReal (s₂.card : ℝ)
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-α) * (s₃.card : ℝ)) := ENNReal.ofReal_le_ofReal h
    rwa [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast] at h'
  have hmass₃ : (∑ i ∈ s₂, volume (W i).shade)
      ≤ ENNReal.ofReal (2 * (δ : ℝ) ^ (-α)) * ∑ i ∈ s₃, volume (W i).shade := by
    have hstep : (∑ i ∈ s₂, volume (W i).shade)
        ≤ (ENNReal.ofReal ((δ : ℝ) ^ (-α)) * (s₃.card : ENNReal)) * (2 * (lam : ENNReal) * v) :=
      le_trans hsum₂le (mul_le_mul_right' hcardE _)
    refine le_trans hstep ?_
    have : (ENNReal.ofReal ((δ : ℝ) ^ (-α)) * (s₃.card : ENNReal)) * (2 * (lam : ENNReal) * v)
        = ENNReal.ofReal (2 * (δ : ℝ) ^ (-α))
            * ((s₃.card : ENNReal) * ((lam : ENNReal) * v)) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      ring
    rw [this]
    exact mul_le_mul_left' hsum₃ge _
  calc (∑ i ∈ s, volume (W i).shade)
      ≤ ENNReal.ofReal L * ∑ i ∈ s₂, volume (W i).shade := hmass₂
    _ ≤ ENNReal.ofReal L * (ENNReal.ofReal (2 * (δ : ℝ) ^ (-α))
          * ∑ i ∈ s₃, volume (W i).shade) := mul_le_mul_left' hmass₃ _
    _ = ENNReal.ofReal (2 * (δ : ℝ) ^ (-α) * L) * ∑ i ∈ s₃, volume (W i).shade := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hLpos)]
        ring_nf

/-- **The Section 2 interface, at the union volume in place of the shade mass.**

Every family of shaded `δ`-tubes in the unit ball with the cardinality budget `#s ≤ δ^{-K₀}` has a
shade-refinement `Z` — tubes unchanged, shadings only shrunk — and a subfamily `s'` on which

* the shading densities are two-sidedly banded at a level `lam > 0`, which is
  `Kakeya.ml1Boot.IsUniformFactorCore.fine_dens`;
* GWZ Definition 2.2 holds at `Tube.ssfGridLen δ` and `ShadedTube.ssfUniformConst`, which is
  `Kakeya.ml1Boot.IsUniformFactorCore.fine_unif` up to the constant; and
* `|⋃_{i ∈ s} Y(V_i)| ≤ 4 δ^{-α} (1 + log₂ (2/a)) ∑_{i ∈ s'} |Z(V_i)|`.

The hypothesis `a ∑_{i ∈ s} |V_i| ≤ |⋃_{i ∈ s} Y(V_i)|` is a lower bound on the *union* density,
and it is the only quantitative input; the loss is polylogarithmic in `1/a`.

**This is not `Kakeya.ml1Boot.exists_uniformFactorCore`, and the gap is one factor.**  That
statement's `fine_refinement` is stated against `∑_{i ∈ s} |Y(V_i)|`, whereas the retention here
is against `|⋃_{i ∈ s} Y(V_i)|`, and the two differ by exactly the multiplicity
`µ(𝕍, Y) = ∑ |Y(V_i)| / |⋃ Y(V_i)|`.  The step that costs it is
`ShadedTube.exists_shade_disjointification`, and it is the step that buys the hereditary
Definition 2.2 of `ShadedTube.nonempty_shadedUniformTubeSet_of_pairwiseDisjoint` — without which
the density band and the uniformity destroy each other, which is the recorded blocker.

So the Section 2 interface is available whenever the multiplicity of the family being uniformized
is inside the refinement budget of its consumer, and only then.  On the fine family of
`Kakeya.ml1Boot.IsUniformFactorCore` the multiplicity is the very quantity Main Lemma 1 bounds, so
this does not close `fine_refinement`; on the middle and coarse families of the two-scale chain the
multiplicity is an output of the proved `Kakeya.ml1Boot.exists_factorOneScale`. -/
theorem exists_shadedUniform_banded (K₀ : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (s : Finset ι) (V : ι → ShadedTube δ E) (a : NNReal),
      (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (s.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
      s.Nonempty → 0 < a → 2 * a ≤ 1 →
      (a : ENNReal) * (∑ i ∈ s, volume (V i).carrier)
          ≤ volume (⋃ i ∈ s, (V i).shade) →
      ∃ s' ⊆ s, ∃ (Z : ι → ShadedTube δ E) (lam : NNReal),
        (∀ i, (Z i).toTube = (V i).toTube) ∧
        (∀ i, (Z i).shade ⊆ (V i).shade) ∧
        0 < lam ∧
        (∀ i ∈ s', (lam : ENNReal) * volume (V i).carrier ≤ volume (Z i).shade ∧
          volume (Z i).shade ≤ 2 * (lam : ENNReal) * volume (V i).carrier) ∧
        volume (⋃ i ∈ s, (V i).shade)
            ≤ ENNReal.ofReal
                (4 * (δ : ℝ) ^ (-α) * (1 + Real.logb 2 (2 * ((a : ℝ))⁻¹)))
              * ∑ i ∈ s', volume (Z i).shade ∧
        Nonempty (ShadedUniformTubeSet s' Z (Tube.ssfGridLen δ)
          (ssfUniformConst (Module.finrank ℝ E))) := by
  classical
  obtain ⟨δ₀, hδ₀pos, hδ₀le1, hmain⟩ :=
    exists_shadedUniform_banded_of_pairwiseDisjoint (E := E) K₀ α hα
  refine ⟨δ₀, hδ₀pos, hδ₀le1, ?_⟩
  intro ι δ hδ hδδ₀ s V a hball hcard hs ha0 ha1 hlow
  obtain ⟨Z, hZtube, hZsub, hZdisj, _hZunion, hZmass⟩ :=
    exists_shade_disjointification (E := E) s V
  have hcar : ∀ i, volume (Z i).carrier = volume (V i).carrier := by
    intro i
    exact congrArg (fun T : Tube δ E => volume T.carrier) (hZtube i)
  -- the disjointified family has union density at least `a`
  have hcarpos : ∀ i : ι, 0 < volume (V i).carrier := by
    intro i
    have hle := Tube.le_volume (V i).toTube
    have hcpos : 0 < (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) :=
      ENNReal.coe_pos.mpr (Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hδp : 0 < (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ) _
    exact lt_of_lt_of_le (ENNReal.mul_pos (ne_of_gt hcpos) (ne_of_gt hδp)) (by simpa using hle)
  have hden0 : (∑ i ∈ s, volume ((Z i).toShadedBody).carrier) ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ := hs
    refine ne_of_gt (lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun i => volume ((Z i).toShadedBody).carrier) (fun i _ => zero_le) hi₀))
    rw [hcar i₀]
    exact hcarpos i₀
  have hdentop : (∑ i ∈ s, volume ((Z i).toShadedBody).carrier) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (Finset.sum_le_sum
      (fun i _ => le_of_eq (hcar i))) ?_)
    exact ENNReal.sum_lt_top.mpr fun i _ => lt_of_le_of_ne le_top (V i).isCompact.measure_ne_top
  have hfull : a ≤ ShadedBody.fullness s (fun i => (Z i).toShadedBody) := by
    rw [← ENNReal.coe_le_coe, ShadedBody.coe_fullness]
    refine (ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdentop)).mpr ?_
    calc (a : ENNReal) * (∑ i ∈ s, volume ((Z i).toShadedBody).carrier)
        = (a : ENNReal) * (∑ i ∈ s, volume (V i).carrier) := by
          refine congrArg _ (Finset.sum_congr rfl fun i _ => hcar i)
      _ ≤ volume (⋃ i ∈ s, (V i).shade) := hlow
      _ = ∑ i ∈ s, volume ((Z i).toShadedBody).shade := hZmass.symm
  -- discard the tubes of low relative shading; the survivors have density at least `a / 2`
  set s₁ : Finset ι :=
    ShadedBody.discardLowShading s (fun i => (Z i).toShadedBody) (1 / 2 : NNReal) with hs₁_def
  have hs₁sub : s₁ ⊆ s := ShadedBody.discardLowShading_subset _ _ _
  have hdens₁ : ∀ i ∈ s₁,
      ((a / 2 : NNReal) : ENNReal) * volume (Z i).carrier ≤ volume (Z i).shade := by
    intro i hi
    refine le_trans ?_ (ShadedBody.le_volume_shade_of_mem_discardLowShading hi)
    refine mul_le_mul_right' ?_ _
    have : ((a / 2 : NNReal) : ENNReal)
        = ((1 / 2 : NNReal) : ENNReal) * (a : ENNReal) := by
      rw [← ENNReal.coe_mul]; congr 1; ring
    rw [this]
    exact mul_le_mul_left' (by exact_mod_cast hfull) _
  have hmass₁ : (∑ i ∈ s, volume ((Z i).toShadedBody).shade)
      ≤ 2 * ∑ i ∈ s₁, volume ((Z i).toShadedBody).shade := by
    have h := ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading
      s (fun i => (Z i).toShadedBody) (c := (1 / 2 : NNReal)) (by norm_num)
    have hc : ((1 - (1 / 2 : NNReal) : NNReal) : ENNReal) = (2 : ENNReal)⁻¹ := by
      rw [show (1 : NNReal) - (1 / 2 : NNReal) = (2 : NNReal)⁻¹ by
        rw [tsub_eq_iff_eq_add_of_le (by norm_num : (1 / 2 : NNReal) ≤ 1)]; norm_num]
      simp
    rw [hc] at h
    calc (∑ i ∈ s, volume ((Z i).toShadedBody).shade)
        = 2 * ((2 : ENNReal)⁻¹ * ∑ i ∈ s, volume ((Z i).toShadedBody).shade) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ 2 * ∑ i ∈ s₁, volume ((Z i).toShadedBody).shade := mul_le_mul_left' h 2
  -- nonemptiness of the survivors
  have hunionpos : 0 < volume (⋃ i ∈ s, (V i).shade) := by
    refine lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr ha0.ne') ?_) hlow
    obtain ⟨i₀, hi₀⟩ := hs
    refine ne_of_gt (lt_of_lt_of_le (hcarpos i₀) (Finset.single_le_sum
      (f := fun i => volume (V i).carrier) (fun i _ => zero_le) hi₀))
  have hs₁ne : s₁.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty] at hmass₁
    simp only [Finset.sum_empty, mul_zero] at hmass₁
    rw [← hZmass] at hunionpos
    exact (ne_of_gt hunionpos) (le_antisymm hmass₁ zero_le)
  -- apply the disjoint uniformizer on the survivors
  have hball₁ : ∀ i ∈ s₁, (Z i).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro i hi
    have : (Z i).carrier = (V i).carrier :=
      congrArg (fun T : Tube δ E => T.carrier) (hZtube i)
    rw [this]; exact hball i (hs₁sub hi)
  have hcard₁ : (s₁.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) :=
    le_trans (by exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hs₁sub)) hcard
  have ha20 : 0 < (a / 2 : NNReal) := by positivity
  have ha_le1 : a ≤ 1 :=
    le_trans (le_mul_of_one_le_left (zero_le : (0 : NNReal) ≤ a)
      (by norm_num : (1 : NNReal) ≤ 2)) ha1
  have ha21 : (a / 2 : NNReal) ≤ 1 := by
    rw [div_le_one (by norm_num : (0 : NNReal) < 2)]
    exact le_trans ha_le1 (by norm_num)
  obtain ⟨s', hs'₁, lam, halam, hband, hmass', hstruct⟩ :=
    hmain hδ hδδ₀ s₁ Z (a / 2) hball₁ hcard₁ hs₁ne ha20 ha21 hdens₁
      (hZdisj.mono (by exact_mod_cast hs₁sub))
  refine ⟨s', fun i hi => hs₁sub (hs'₁ hi), Z, lam, hZtube, hZsub,
    lt_of_lt_of_le ha20 halam, ?_, ?_, hstruct⟩
  · intro i hi
    have h := hband i hi
    rw [hcar i] at h
    exact h
  · have hchain : volume (⋃ i ∈ s, (V i).shade)
        ≤ 2 * (ENNReal.ofReal
            (2 * (δ : ℝ) ^ (-α) * (1 + Real.logb 2 (((a / 2 : NNReal) : ℝ))⁻¹))
              * ∑ i ∈ s', volume (Z i).shade) := by
      rw [← hZmass]
      exact le_trans hmass₁ (mul_le_mul_left' hmass' 2)
    refine le_trans hchain (le_of_eq ?_)
    have hpos : (0 : ℝ) ≤ 2 * (δ : ℝ) ^ (-α)
        * (1 + Real.logb 2 (((a / 2 : NNReal) : ℝ))⁻¹) := by
      have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
      have haR1 : (a : ℝ) ≤ 1 := by
        have : (2 : NNReal) * a ≤ 1 := ha1
        have h2 : (2 : ℝ) * (a : ℝ) ≤ 1 := by exact_mod_cast this
        linarith
      have hlogb : (0 : ℝ) ≤ Real.logb 2 (((a / 2 : NNReal) : ℝ))⁻¹ := by
        apply Real.logb_nonneg (by norm_num)
        rw [le_inv_comm₀ (by push_cast; positivity) (by push_cast; linarith)]
        push_cast
        linarith
      have : (0 : ℝ) < (δ : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by exact_mod_cast hδ) _
      nlinarith
    rw [← mul_assoc, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 2
    have : ((a / 2 : NNReal) : ℝ) = (a : ℝ) / 2 := by push_cast; ring
    rw [this]
    rw [show ((a : ℝ) / 2)⁻¹ = 2 * ((a : ℝ))⁻¹ by field_simp]
    ring

end ShadedTube

end
