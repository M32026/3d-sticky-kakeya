/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Goals
public import Kakeya.DimensionThree.MainLemma2.ShadingBandFree

/-!
# The subfamily form of the Section-5 coarse-shading interface, and what it does not reach

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` is the coarse-shading statement; the *proved*
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_subfamily` is GWZ Lemma 5.11 at the same
configuration and the same grid scale, differing from it — so a long line of notes said — in
"exactly two places": the two equalities `G.outerSet = 𝕋_ρ` and `G.innerSet = 𝕋`, and the
placeholder loss `ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1` in place of the
honest `Kakeya.VeryNotSticky.coarseLoss`.  The programme that follows from that reading is:
weaken the two equalities to a containment and the induced subset, state the residue at
`coarseLoss`, and repair the counting consumer.

**This file carries out the repairable half of that programme and shows why the other half is
not a repair.**  Three facts, each compiled:

1. *The two weakenings are not independent.*
   `Kakeya.VeryNotSticky.outerSet_eq_activeTubeNodes_of_innerSet_eq`: a fully shaded factor
   family whose parent map is the hierarchy's assignment and whose inner set is all of `𝕋`
   has `G.outerSet = 𝕋_ρ` **on the nose** as soon as `G.outerSet ⊆ 𝕋_ρ`, because
   `ShadedBody.ShadedFactorFamily.parent_mem` forces every parent of a retained member into
   the outer set and every active node carries one.  So weakening only the outer equality is
   vacuous: the inner set must shrink with it.

2. *The counting consumer is repairable, at an absorbable price.*
   `Kakeya.VeryNotSticky.card_le_card_activeTubeNodes_mul` is the one conjunct of
   `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` that does not transport to a
   sub-collection of nodes for free — its left-hand side is the **full** `|𝕋|`.  It is
   repaired here in two steps.
   `Kakeya.VeryNotSticky.card_le_of_isCRefinement_of_tubeVolumeBand` converts the *mass*
   retention that GWZ Lemma 5.11 delivers, `ShadedBody.IsCRefinement`, into *cardinality*
   retention, using the
   configuration's aggregate fullness `Kakeya.VeryNotSticky.fullness_ge` on the small side and
   the dimensional tube-volume bound `Tube.volume_le` on the large side — so the density
   comparison constant `Kakeya.VeryNotSticky.Cd`, which no field bounds above, does not enter.
   `Kakeya.VeryNotSticky.card_filter_le_card_mul` is the branching count restricted to a
   sub-collection of nodes, which holds verbatim.
   `Kakeya.VeryNotSticky.card_le_card_subfamilyNodes_mul` combines them: the price is one
   factor `δ^{3η}`, sub-polynomial by `Kakeya.VeryNotSticky.coarseLoss_absorb`.
   The other conjunct, `Kakeya.VeryNotSticky.maxDensity_activeTubeNodes_le`, transports for
   free (`Kakeya.VeryNotSticky.maxDensity_subfamilyNodes_le`), by `Kakeya.maxDensity_mono`.

3. *The obstruction is one clause further down, and it is local.*
   `Kakeya.VeryNotSticky.exists_aScaleInputs` feeds
   `Kakeya.VeryNotSticky.aScaleData_of_ballEstimate`, whose target
   `Kakeya.VeryNotSticky.AScaleData` is stated at the configuration's own pair `(𝕋, Y)`: its
   first clause compares `|U(𝕋, Y) ∩ B(x, r)|` with `|U(𝕋, Y)|` at **every** centre.  A
   subfamily supplies that comparison for its own, smaller shaded union
   (`Kakeya.VeryNotSticky.iUnionShade_subset_of_isCRefinement`), and the only bridge GWZ
   Lemma 5.11 offers between the two is `ShadedBody.IsCRefinement`, an inequality between two
   **global** volume sums.  `Kakeya.VeryNotSticky.aScaleData_of_ballEstimate_subfamily`
   isolates exactly what is missing: a **ball-wise** comparison
   `|U(𝕋, Y) ∩ B(x, r)| ≤ K · |U(𝕋', Y') ∩ B(x, r)|`, uniform in the centre.  Nothing in the
   eleven conclusions of `ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam`
   implies it, and `Kakeya.VeryNotSticky.two_mul_pow_le_coarseLoss` says why no soft argument
   will: the loss of Lemma 5.11 is at least `ShadedBody.rhoTubesBallLoss 3 = 2 · 10⁶`, so the
   pigeonhole is entitled to discard all but a `5 · 10⁻⁷` fraction of the shaded mass, and a
   discarded region can be an entire `r`-ball.

There is a third difference between the two statements, not previously recorded and not
removable either: `exists_coarseShadedFamilyAtGrid` asks for `G.innerBody i = (T i)` as
*shaded* bodies, while Lemma 5.11 identifies inner bodies only as convex bodies and shrinks
their shades (`ShadedBody.IsRefinement`'s second clause).

The remaining structural route is the one blueprint `lem:ml2setupexists` already takes — carry
the refinement at the level of the configuration and transport the *conclusion* back, which is
what `Kakeya.VeryNotSticky.exists_setup_caseSideData` does once with its own
`ShadedBody.IsCRefinement` clause.  Its first brick is here:
`Kakeya.VeryNotSticky.multiplicity_le_coarseLoss_mul_of_isCRefinement`, since multiplicity —
unlike a ball-wise volume comparison — *does* transport across a `c`-refinement
(`ShadedBody.IsCRefinement.mul_multiplicity_le`).

Nothing in this file changes a statement, and nothing in it is used by an existing
declaration; it is additive.
-/

@[expose] public section

open MeasureTheory Metric Set ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

universe u

/-- **The two weakenings of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` are not
independent: relaxing the outer equality alone is vacuous.**

If `G.innerSet` is all of `𝕋` and `G.parent` is the hierarchy's own assignment, then
`ShadedBody.ShadedFactorFamily.parent_mem` puts the parent of every member of `𝕋` into
`G.outerSet`; and every node of `Kakeya.VeryNotSticky.activeTubeNodes` is, by definition of
`Kakeya.VeryNotSticky.tubeFibre`, the parent of some member.  So `G.outerSet ⊆ 𝕋_ρ` upgrades
to equality with no hypothesis on the shadings at all.

Consequently a restatement of the residue that keeps `G.innerSet = cfg.s` and only weakens the
outer clause to `⊆` is the *same statement*, and any genuine weakening must shrink the inner
set to the members the pigeonhole retains. -/
theorem outerSet_eq_activeTubeNodes_of_innerSet_eq (cfg : VeryNotSticky.{u}) {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C) {k : ℕ}
    (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι)
    (hinner : G.innerSet = cfg.s)
    (hparent : G.parent = 𝒰.cover.assign k)
    (houter : G.outerSet ⊆ cfg.activeTubeNodes 𝒰 k) :
    G.outerSet = cfg.activeTubeNodes 𝒰 k := by
  classical
  refine Finset.Subset.antisymm houter ?_
  intro j hj
  have hj' : (cfg.tubeFibre 𝒰 k j).Nonempty := (Finset.mem_filter.mp hj).2
  obtain ⟨i, hi⟩ := hj'
  have his : i ∈ cfg.s ∧ 𝒰.cover.assign k i = j := by
    simpa [tubeFibre, Tube.coverClass, Finset.mem_filter] using hi
  have hiG : i ∈ G.innerSet := hinner ▸ his.1
  have := G.parent_mem i hiG
  rw [hparent] at this
  rwa [his.2] at this


/-- **GWZ Lemma 5.11 at the configuration's hierarchy, with the two conclusions that
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_subfamily` throws away.**

`ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam` produces eleven conclusions;
that lemma destructures them and keeps seven.  Two of the four it drops are the ones a
counting consumer needs, and they are surfaced here:

* `ShadedBody.IsCRefinement G.innerSet G.innerBody 𝕋 Y coarseLoss⁻¹` — GWZ's own
  "`(𝕋', Y')` is a `C⁻¹`-refinement of `(𝕋, Y)`", at the loss
  `Kakeya.VeryNotSticky.coarseLoss`, which `Kakeya.VeryNotSticky.coarseLoss_absorb` makes
  sub-polynomial.  It is a comparison of two **sums** of shaded volumes, not of two unions and
  not of two intersections with a ball; that is exactly its reach, and exactly its limit.
* `boundMuTTYAcrossTwoScales`, whose left-hand side
  `ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody)` is the multiplicity of the
  **full** inner family, not the subfamily's.

Everything else is `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_subfamily` verbatim,
and the proof is that lemma's proof with two more components kept. -/
theorem exists_coarseShadedFamilyAtGrid_subfamily_refinement (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.outerSet ⊆ cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      G.innerSet = {i ∈ cfg.s | 𝒱.tubeUniform.cover.assign k i ∈ G.outerSet} ∧
      G.parent = 𝒱.tubeUniform.cover.assign k ∧
      (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody =
        (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (∀ i ∈ cfg.s, (G.innerBody i).toConvexSpaceBody = (cfg.T i).toConvexSpaceBody) ∧
      (cfg.Cd * cfg.coarseLoss)⁻¹ * cfg.lam ≤ ShadedBody.fullness G.outerSet G.outerBody ∧
      ShadedBody.IsCRefinement G.innerSet G.innerBody cfg.s
        (fun i ↦ (cfg.T i).toShadedBody) cfg.coarseLoss⁻¹ ∧
      (∀ j ∈ G.outerSet,
        ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤
          (cfg.coarseLoss : ENNReal) * ShadedBody.multiplicity G.outerSet G.outerBody *
            ShadedBody.multiplicity (G.fiber j) G.innerBody) ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.coarseLoss : ENNReal)⁻¹ *
            volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  subst hgrid
  let F : ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι :=
    cfg.nodeFactorFamily 𝒱.tubeUniform hk
  have hFi : F.innerSet = cfg.s := rfl
  have hFp : F.parent = 𝒱.tubeUniform.cover.assign k := rfl
  have hFo : F.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k := rfl
  have hFb : ∀ i, F.innerBody i = (cfg.T i).toShadedBody := fun _ => rfl
  have hFob : ∀ j, F.outerBody j = (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody :=
    fun _ => rfl
  have hCd : cfg.Cd ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
  obtain ⟨G, h1, h2, h3, h4, h5, h6, hfull, h8, h9, h10, h11, _h12⟩ :=
    _root_.ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam
      (E := EuclideanSpace ℝ (Fin 3)) (δ := cfg.δ) (Cd := cfg.Cd) (lam := cfg.lam)
      cfg.hδ hρ hCd F cfg.T (𝒱.tubeUniform.cover.tube k)
      (fun i _ => rfl) (fun j _ => rfl)
      (fun i hi => cfg.contained i hi)
      cfg.sum_volume_carrier_ne_zero
      cfg.shading_lb
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hloss : _root_.ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) F.innerSet.card cfg.δ 1
      = cfg.coarseLoss := by
    rw [hfr, hFi]
  refine ⟨G, hFo ▸ h1, (by rw [h2]; congr 1), hFp ▸ h3, fun j hj => (hFob _) ▸ h4 j hj,
    fun i hi => by simpa [hFb] using h5 i (hFi ▸ hi), ?_, ?_, ?_, ?_⟩
  · rw [← hloss]; exact hfull
  · rw [← hloss]; exact h8
  · rw [← hloss]; exact h9
  · rw [← hloss]; exact h11


/-- **A `c`-refinement of the configuration's pair retains a `c · δ^{2η}` fraction of the
*cardinality*, not merely of the mass.**

`ShadedBody.IsCRefinement` is a statement about shaded mass; the counting conjunct of
`Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` is a statement about `|𝕋|`.  The bridge
is that all tubes of the configuration have comparable volume, so mass and cardinality differ
by a bounded factor: the small side uses the aggregate fullness
`Kakeya.VeryNotSticky.fullness_ge` through
`ShadedBody.coe_fullness_mul_le_sum_volume_shade` and the dimensional lower bound
`Tube.le_volume`, the large side uses `ShadedBody.shade_subset` and the dimensional upper
bound `Tube.volume_le`.

**The per-tube density band is deliberately not used.**  Running the same argument through
`Kakeya.VeryNotSticky.shading_lb` and `Kakeya.VeryNotSticky.shading_ub` would leave a factor
`Cd²`, and `Kakeya.VeryNotSticky.Cd` is bounded below by `1` and above by nothing, so that
form would be useless.  The aggregate fullness is bounded below by `δ^{2η}` and that is the
whole price.

**Why `Kakeya.card_le_of_isCRefinement_of_fullness` is not used.**  That lemma is the same
conversion, and it was found by a duplicate scan before this one was written; but it takes a
*single* reference volume `v`, bounding the original carriers from below and the retained
shades from above by the same number.  A family of `δ`-tubes has a two-sided volume band with
*different* constants, `Tube.le_volume.c 3 · δ² ≤ |T| ≤ Tube.volume_le.C 3 · δ²`, and neither
endpoint serves both roles.  The statement here therefore carries the ratio of the two
dimensional constants where that one carries none. -/
theorem card_le_of_isCRefinement_of_tubeVolumeBand (cfg : VeryNotSticky.{u}) {s' : Finset cfg.ι}
    {V' : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {c : NNReal}
    (href : ShadedBody.IsCRefinement s' V' cfg.s (fun i ↦ (cfg.T i).toShadedBody) c) :
    (c : ENNReal) * ((cfg.δ : ENNReal) ^ (2 * cfg.η) *
        ((Tube.le_volume.c 3 : ENNReal) * (cfg.s.card : ENNReal)))
      ≤ (Tube.volume_le.C 3 : ENNReal) * (s'.card : ENNReal) := by
  classical
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  set d2 : ENNReal := (cfg.δ : ENNReal) ^ 2 with hd2
  have hd20 : d2 ≠ 0 := by
    simpa [hd2] using pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr (ne_of_gt cfg.hδ))
  have hd2top : d2 ≠ ⊤ := by
    exact ENNReal.pow_ne_top (a := (cfg.δ : ENNReal)) ENNReal.coe_ne_top
  -- the lower bound on the shaded mass of the full family, from `fullness_ge`
  have hcar : ∀ i ∈ cfg.s, (Tube.le_volume.c 3 : ENNReal) * d2 ≤
      volume ((cfg.T i).toShadedBody.carrier) := by
    intro i _
    simpa [hd2, hfin] using (Tube.le_volume (cfg.T i).toTube)
  have hlow : ((cfg.δ ^ (2 * cfg.η) : NNReal) : ENNReal) *
      ((cfg.s.card : ENNReal) * ((Tube.le_volume.c 3 : ENNReal) * d2)) ≤
      ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody.shade) :=
    ShadedBody.coe_fullness_mul_le_sum_volume_shade cfg.s (fun i ↦ (cfg.T i).toShadedBody)
      cfg.fullness_ge hcar
  -- the upper bound on the shaded mass of the refinement, from the tube volume bound
  have hup : ∑ i ∈ s', volume ((V' i).shade) ≤
      (s'.card : ENNReal) * ((Tube.volume_le.C 3 : ENNReal) * d2) := by
    calc ∑ i ∈ s', volume ((V' i).shade)
        ≤ ∑ i ∈ s', ((Tube.volume_le.C 3 : ENNReal) * d2) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hcarrier : (V' i).carrier = (cfg.T i).toShadedBody.carrier :=
            congrArg ConvexSpaceBody.carrier (href.1.2 i hi).1
          calc volume ((V' i).shade) ≤ volume ((V' i).carrier) :=
                measure_mono (V' i).shade_subset
            _ = volume ((cfg.T i).toShadedBody.carrier) := by rw [hcarrier]
            _ ≤ (Tube.volume_le.C 3 : ENNReal) * d2 := by
                simpa [hd2, hfin] using (Tube.volume_le cfg.hδ1 (cfg.T i).toTube)
      _ = (s'.card : ENNReal) * ((Tube.volume_le.C 3 : ENNReal) * d2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- combine
  have hkey : ((c : ENNReal) * ((cfg.δ : ENNReal) ^ (2 * cfg.η) *
      ((Tube.le_volume.c 3 : ENNReal) * (cfg.s.card : ENNReal)))) * d2 ≤
      ((Tube.volume_le.C 3 : ENNReal) * (s'.card : ENNReal)) * d2 := by
    have hcoe : ((cfg.δ ^ (2 * cfg.η) : NNReal) : ENNReal) = (cfg.δ : ENNReal) ^ (2 * cfg.η) :=
      ENNReal.coe_rpow_of_ne_zero (ne_of_gt cfg.hδ) _
    calc ((c : ENNReal) * ((cfg.δ : ENNReal) ^ (2 * cfg.η) *
            ((Tube.le_volume.c 3 : ENNReal) * (cfg.s.card : ENNReal)))) * d2
        = (c : ENNReal) * (((cfg.δ ^ (2 * cfg.η) : NNReal) : ENNReal) *
            ((cfg.s.card : ENNReal) * ((Tube.le_volume.c 3 : ENNReal) * d2))) := by
          rw [hcoe]; ring
      _ ≤ (c : ENNReal) * ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody.shade) := by
          gcongr
      _ ≤ ∑ i ∈ s', volume ((V' i).shade) := href.2
      _ ≤ (s'.card : ENNReal) * ((Tube.volume_le.C 3 : ENNReal) * d2) := hup
      _ = ((Tube.volume_le.C 3 : ENNReal) * (s'.card : ENNReal)) * d2 := by ring
  exact (ENNReal.mul_le_mul_iff_left hd20 hd2top).mp (by simpa [mul_comm] using hkey)

open scoped Classical in
/-- **The branching count of `Kakeya.VeryNotSticky.card_le_card_activeTubeNodes_mul` holds
verbatim on a sub-collection of nodes, for the members that sub-collection retains.**

The members retained by a sub-collection `A` of the active nodes are exactly the disjoint
union of the fibres over `A`, so the fibrewise counting identity and the two-parent comparison
`Kakeya.VeryNotSticky.card_tubeFibre_le_card_tubeFibre` apply unchanged.  What is *not*
verbatim is the left-hand side: it is `|{i ∈ 𝕋 | parent i ∈ A}|`, not `|𝕋|`, and closing that
gap is what `Kakeya.VeryNotSticky.card_le_of_isCRefinement_of_tubeVolumeBand` is for. -/
theorem card_filter_le_card_mul (cfg : VeryNotSticky.{u}) {N : ℕ} {C₀ : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C₀) {k : ℕ} (hk : k ≤ N)
    {A : Finset cfg.ι} (hA : A ⊆ cfg.activeTubeNodes 𝒰 k)
    {j : cfg.ι} (hj : j ∈ 𝒰.cover.indexSet k) :
    ((({i ∈ cfg.s | 𝒰.cover.assign k i ∈ A} : Finset cfg.ι)).card : NNReal) ≤
      C₀ ^ 2 * ((A.card : NNReal) * ((cfg.tubeFibre 𝒰 k j).card : NNReal)) := by
  classical
  have hdisj : (A : Set cfg.ι).PairwiseDisjoint (cfg.tubeFibre 𝒰 k) := by
    intro j₁ _ j₂ _ hj₁j₂
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi₁ hi₂
    have h₁ : 𝒰.cover.assign k i = j₁ := by
      simp only [tubeFibre, Tube.coverClass, Finset.mem_filter] at hi₁
      exact hi₁.2
    have h₂ : 𝒰.cover.assign k i = j₂ := by
      simp only [tubeFibre, Tube.coverClass, Finset.mem_filter] at hi₂
      exact hi₂.2
    exact hj₁j₂ (h₁.symm.trans h₂)
  have hbi : ({i ∈ cfg.s | 𝒰.cover.assign k i ∈ A} : Finset cfg.ι)
      = A.biUnion (cfg.tubeFibre 𝒰 k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_biUnion, tubeFibre, Tube.coverClass]
    constructor
    · rintro ⟨his, hiA⟩
      exact ⟨𝒰.cover.assign k i, hiA, by simp [his]⟩
    · rintro ⟨j', hj'A, his, hij'⟩
      exact ⟨his, hij' ▸ hj'A⟩
  have hcard : ({i ∈ cfg.s | 𝒰.cover.assign k i ∈ A} : Finset cfg.ι).card
      = ∑ j' ∈ A, (cfg.tubeFibre 𝒰 k j').card := by
    rw [hbi, Finset.card_biUnion]
    intro j₁ hj₁ j₂ hj₂ h
    exact hdisj hj₁ hj₂ h
  have hle : ∀ j' ∈ A, ((cfg.tubeFibre 𝒰 k j').card : NNReal) ≤
      C₀ ^ 2 * ((cfg.tubeFibre 𝒰 k j).card : NNReal) := by
    intro j' hj'
    have hj'k : j' ∈ 𝒰.cover.indexSet k := (Finset.mem_filter.mp (hA hj')).1
    exact card_tubeFibre_le_card_tubeFibre cfg 𝒰 hk hj'k hj
  calc ((({i ∈ cfg.s | 𝒰.cover.assign k i ∈ A} : Finset cfg.ι)).card : NNReal)
      = ∑ j' ∈ A, ((cfg.tubeFibre 𝒰 k j').card : NNReal) := by
        rw [hcard, Nat.cast_sum]
    _ ≤ ∑ _j' ∈ A, C₀ ^ 2 * ((cfg.tubeFibre 𝒰 k j).card : NNReal) := Finset.sum_le_sum hle
    _ = C₀ ^ 2 * ((A.card : NNReal) * ((cfg.tubeFibre 𝒰 k j).card : NNReal)) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring


/-- `δ^{η} ≤ coarseLoss⁻¹`: the honest Section-5 loss is sub-polynomial, so its reciprocal
costs at most one factor `δ^{η}`.  This is `Kakeya.VeryNotSticky.coarseLoss_le_rpow_neg_eta`,
i.e. the configuration field `Kakeya.VeryNotSticky.coarseLoss_absorb`, read on the other
side. -/
theorem rpow_eta_le_coarseLoss_inv (cfg : VeryNotSticky.{u}) :
    (cfg.δ : ENNReal) ^ cfg.η ≤ ((cfg.coarseLoss : ENNReal))⁻¹ := by
  have h := cfg.coarseLoss_le_rpow_neg_eta
  have hinv : ((cfg.δ : ENNReal) ^ (-cfg.η))⁻¹ ≤ ((cfg.coarseLoss : ENNReal))⁻¹ :=
    ENNReal.inv_le_inv' h
  rwa [ENNReal.rpow_neg, inv_inv] at hinv

open scoped Classical in
/-- **The counting conjunct survives the pigeonhole of GWZ Lemma 5.11, at the cost of one
factor `δ^{3η}` and one dimensional ratio.**

This is the repair the counting consumer needs: with `A` the retained nodes and the retained
members those assigned to `A`, the full `|𝕋|` is still bounded by `C₀² |A| · |𝕋[T_ρ]|`, at the
extra price `δ^{-3η} · Tube.volume_le.C 3 / Tube.le_volume.c 3`.  The `δ^{-3η}` is `δ^{-η}`
from `Kakeya.VeryNotSticky.coarseLoss_absorb` and `δ^{-2η}` from
`Kakeya.VeryNotSticky.fullness_ge`; the ratio is dimensional, with no `δ` and no `|𝕋|` in it.

**The price is affordable where the conjunct is spent.**  It is spent in
`Kakeya.VeryNotSticky.aScaleVolume`, whose gain is weakened from `δ^{2η + ν/90}` to `δ^{ν/9}`
by `Kakeya.aScaleExponentBudget`; the surplus is `ν/9 - ν/90 - 2η = ν/10 - 2η ≥ 7η` under the
standing `90 η ≤ ν`, and `3η` of that suffices.  It is *not* affordable inside the constant:
`Kakeya.VeryNotSticky.aScaleData_absorb` gives `(aScaleDataConstant C₀ D₀)² ≤ δ^{-η}` with no
room, so the factor has to be paid out of the exponent budget and not folded into `C₀`. -/
theorem card_le_card_subfamilyNodes_mul (cfg : VeryNotSticky.{u})
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {A : Finset cfg.ι} (hA : A ⊆ cfg.activeTubeNodes 𝒰 k)
    {j : cfg.ι} (hj : j ∈ 𝒰.cover.indexSet k)
    {V' : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    (href : ShadedBody.IsCRefinement ({i ∈ cfg.s | 𝒰.cover.assign k i ∈ A} : Finset cfg.ι) V'
      cfg.s (fun i ↦ (cfg.T i).toShadedBody) cfg.coarseLoss⁻¹) :
    (Tube.le_volume.c 3 : ENNReal) *
        ((cfg.δ : ENNReal) ^ (3 * cfg.η) * (cfg.s.card : ENNReal))
      ≤ (Tube.volume_le.C 3 : ENNReal) *
        ((cfg.C₀ : ENNReal) ^ 2 *
          ((A.card : ENNReal) * ((cfg.tubeFibre 𝒰 k j).card : ENNReal))) := by
  classical
  have hL0 : cfg.coarseLoss ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.one_le_coarseLoss)
  have hcoe : ((cfg.coarseLoss⁻¹ : NNReal) : ENNReal) = ((cfg.coarseLoss : ENNReal))⁻¹ :=
    ENNReal.coe_inv hL0
  have hmass := card_le_of_isCRefinement_of_tubeVolumeBand cfg href
  rw [hcoe] at hmass
  have hsplit : (cfg.δ : ENNReal) ^ (3 * cfg.η) =
      (cfg.δ : ENNReal) ^ cfg.η * (cfg.δ : ENNReal) ^ (2 * cfg.η) := by
    rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr (ne_of_gt cfg.hδ)) ENNReal.coe_ne_top]
    ring_nf
  have hstep : (Tube.le_volume.c 3 : ENNReal) *
      ((cfg.δ : ENNReal) ^ (3 * cfg.η) * (cfg.s.card : ENNReal))
      ≤ (Tube.volume_le.C 3 : ENNReal) *
        ((({i ∈ cfg.s | 𝒰.cover.assign k i ∈ A} : Finset cfg.ι)).card : ENNReal) := by
    refine le_trans ?_ hmass
    rw [hsplit]
    calc (Tube.le_volume.c 3 : ENNReal) *
          (((cfg.δ : ENNReal) ^ cfg.η * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
            (cfg.s.card : ENNReal))
        = (cfg.δ : ENNReal) ^ cfg.η *
            ((cfg.δ : ENNReal) ^ (2 * cfg.η) *
              ((Tube.le_volume.c 3 : ENNReal) * (cfg.s.card : ENNReal))) := by ring
      _ ≤ ((cfg.coarseLoss : ENNReal))⁻¹ *
            ((cfg.δ : ENNReal) ^ (2 * cfg.η) *
              ((Tube.le_volume.c 3 : ENNReal) * (cfg.s.card : ENNReal))) := by
            gcongr
            exact rpow_eta_le_coarseLoss_inv cfg
  refine le_trans hstep ?_
  gcongr
  have := card_filter_le_card_mul cfg 𝒰 hk hA hj
  have hcast : ((({i ∈ cfg.s | 𝒰.cover.assign k i ∈ A} : Finset cfg.ι)).card : ENNReal) ≤
      (cfg.C₀ : ENNReal) ^ 2 *
        ((A.card : ENNReal) * ((cfg.tubeFibre 𝒰 k j).card : ENNReal)) := by
    exact_mod_cast (ENNReal.coe_le_coe.mpr this)
  simpa using hcast


/-- **The free half of the transport: the two-scale multiplicity bound of
`Kakeya.VeryNotSticky.maxDensity_activeTubeNodes_le` holds on any sub-collection of the active
nodes, at the same constant.**

`Kakeya.maxDensity_mono` is `Monotone fun s ↦ maxDensity s W`, and the right-hand side
`deltamaxScaleAConstant C₀ D₀ · ρ²` does not mention the family, so nothing is paid.  The
monotonicity lemma lives in the root `Kakeya` namespace, not under `ConvexSpaceBody`. -/
theorem maxDensity_subfamilyNodes_le (cfg : VeryNotSticky.{u}) {N : ℕ} {C₀ : NNReal}
    (hC₀ : 1 ≤ C₀)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C₀) {k : ℕ} (hk : k ≤ N)
    {D₀ : NNReal} (hD₀ : 1 ≤ D₀) {j : cfg.ι} (hj : j ∈ 𝒰.cover.indexSet k)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ N k = ρ) (hρ1 : ρ ≤ 1)
    {A : Finset cfg.ι} (hA : A ⊆ cfg.activeTubeNodes 𝒰 k) :
    maxDensity A (fun j' ↦ (𝒰.cover.tube k j').toConvexSpaceBody) *
          ((cfg.tubeFibre 𝒰 k j).card : ENNReal) * (cfg.δ : ENNReal) ^ cfg.η *
          (cfg.δ : ENNReal) ^ 2 ≤
      (deltamaxScaleAConstant C₀ D₀ : ENNReal) * (ρ : ENNReal) ^ 2 := by
  refine le_trans ?_ (maxDensity_activeTubeNodes_le cfg hC₀ 𝒰 hk hD₀ hj hgrid hρ1)
  gcongr
  exact Kakeya.maxDensity_mono (fun j' ↦ (𝒰.cover.tube k j').toConvexSpaceBody) hA

/-- The shades of a `c`-refinement only shrink, so its shaded union is *contained* in the
configuration's own — which is the direction that makes the first clause of
`Kakeya.VeryNotSticky.AScaleData` go the wrong way: the union appears both inside the
intersection with the ball, where a smaller set is a weaker hypothesis, and on the large side,
where a smaller set is a stronger conclusion. -/
theorem iUnionShade_subset_of_isCRefinement (cfg : VeryNotSticky.{u}) {s' : Finset cfg.ι}
    {V' : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {c : NNReal}
    (href : ShadedBody.IsCRefinement s' V' cfg.s (fun i ↦ (cfg.T i).toShadedBody) c) :
    (⋃ i ∈ s', (V' i).shade) ⊆ ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade := by
  refine Set.iUnion₂_subset fun i hi => ?_
  exact Set.subset_iUnion₂_of_subset i (href.1.1 hi) (href.1.2 i hi).2

/-- **Estimate (i) of `Kakeya.VeryNotSticky.AScaleData` from a *subfamily* ball estimate, and
the exact extra hypothesis it costs.**

`Kakeya.VeryNotSticky.aScaleData_of_ballEstimate` takes the ball estimate at a family whose
inner layer *is* the configuration's pair, and uses that identification to rewrite
`⋃ i ∈ G.innerSet, (G.innerBody i).shade` into `U(𝕋, Y)`.  With a subfamily there is no such
identification, and this lemma isolates precisely what replaces it: the ball-wise comparison
`hlocal`, asserting `|U(𝕋, Y) ∩ B(x, r)| ≤ K · |U(𝕋', Y') ∩ B(x, r)|` with one `K` valid at
**every** centre.  Given it, the rest goes through: `Kakeya.aScaleBall` is applied to the
subfamily, the containment of unions is used on the large side, and the constant becomes
`K · aScaleBallConstant Cb`.

**`hlocal` is what GWZ Lemma 5.11 does not supply.**  Its refinement clause
`ShadedBody.IsCRefinement` compares two sums of volumes globally; nothing in it is uniform in
a ball, and by `Kakeya.VeryNotSticky.two_mul_pow_le_coarseLoss` the pigeonhole may legitimately
discard all but a `5 · 10⁻⁷` fraction of the shaded mass — in particular everything inside one
`r`-ball, where `hlocal` then fails for every finite `K`.  So this hypothesis is the residue of
the subfamily route, and it is not a constant that can be absorbed.

The degenerate case is handled without `hlocal` being vacuous: if the subfamily's union misses
the ball, `hlocal` forces the configuration's union to miss it too, up to measure zero. -/
theorem aScaleData_of_ballEstimate_subfamily (cfg : VeryNotSticky.{u}) {κ : Type*}
    (G : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι κ)
    (hsub : (⋃ i ∈ G.innerSet, (G.innerBody i).shade) ⊆
      ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade)
    {Cb : NNReal} (hCb : 0 < Cb) {r : NNReal} (hr : 0 < (r : ℝ)) {ν : ℝ}
    (hvol : ∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
      (cfg.δ : ENNReal) ^ (ν / 9) *
          ((Cb : ENNReal)⁻¹ * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
            (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (r : ℝ)) /
              volume (ball x (r : ℝ)))) ≤
        volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade))
    {K : ENNReal}
    (hlocal : ∀ x : EuclideanSpace ℝ (Fin 3),
      volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ ball x (r : ℝ)) ≤
        K * volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (r : ℝ)))
    {C : ENNReal} (hC : K * (aScaleBallConstant Cb : ENNReal) ≤ C)
    (hcoarse : (cfg.δ : ENNReal) ^ (ν / 9) * (r : ENNReal) ^ (2 * cfg.β) *
        ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier ≤
      C * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) * (cfg.δ : ENNReal) ^ (2 * cfg.β) *
        (cfg.s.card : ENNReal) ^ cfg.β) :
    cfg.AScaleData C r ν := by
  classical
  refine ⟨⋃ j ∈ G.outerSet, (G.outerBody j).shade, ?_, hcoarse⟩
  intro x _
  by_cases hne' : ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (r : ℝ)).Nonempty
  · have hball := Kakeya.aScaleBall G hCb hr hvol x hne'
    have hUle : volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade) ≤
        volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) := measure_mono hsub
    calc (cfg.δ : ENNReal) ^ (ν / 9) *
            volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
            volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ ball x (r : ℝ))
        ≤ (cfg.δ : ENNReal) ^ (ν / 9) *
            volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
            (K * volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (r : ℝ))) := by
          gcongr
          exact hlocal x
      _ = K * ((cfg.δ : ENNReal) ^ (ν / 9) *
            volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
            volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (r : ℝ))) := by ring
      _ ≤ K * ((aScaleBallConstant Cb : ENNReal) *
            volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade) * volume (ball x (r : ℝ))) := by
          gcongr
      _ = (K * (aScaleBallConstant Cb : ENNReal)) *
            volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade) * volume (ball x (r : ℝ)) := by
          ring
      _ ≤ C * volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) * volume (ball x (r : ℝ)) := by
          gcongr
  · have hz : volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (r : ℝ)) = 0 := by
      rw [Set.not_nonempty_iff_eq_empty.mp hne']
      simp
    have hz' : volume ((⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) ∩ ball x (r : ℝ)) = 0 := by
      refine le_antisymm ?_ bot_le
      simpa [hz] using hlocal x
    simp [hz']


/-- **The pigeonhole of GWZ Lemma 5.11 is entitled to discard almost everything.**

`Kakeya.VeryNotSticky.coarseLoss` is bounded below by `ShadedBody.rhoTubesBallLoss 3`, the
bounded-overlap loss of Step 5, which is `2 · 100³ = 2 · 10⁶`
(`ShadedBody.two_mul_pow_le_rhoTubesSection9Loss`).  So the refinement clause guarantees only
that a `5 · 10⁻⁷` fraction of `∑_T |Y(T)|` survives.  This is the quantitative reason a
subfamily cannot be treated as "the same family up to a constant" in any *local* estimate,
and it is independent of `δ` and of `|𝕋|`: it is a floor, not a threshold. -/
theorem two_mul_pow_le_coarseLoss (cfg : VeryNotSticky.{u}) : 2 * 100 ^ 3 ≤ cfg.coarseLoss :=
  _root_.ShadedBody.two_mul_pow_le_rhoTubesSection9Loss 3 cfg.s.card cfg.δ


/-- **The transport brick for the other structural route.**

Unlike a ball-wise volume comparison, a multiplicity bound *does* transport across a
`c`-refinement: `ShadedBody.IsCRefinement.mul_multiplicity_le` gives
`c · μ(𝕋, Y) ≤ μ(𝕋', Y')`, so a bound proved for the refined pair yields one for the original
at the price `coarseLoss`, which `Kakeya.VeryNotSticky.coarseLoss_absorb` absorbs.

That is the shape of the route blueprint `lem:ml2setupexists` already takes, and which
`Kakeya.VeryNotSticky.exists_setup_caseSideData` records with its own
`ShadedBody.IsCRefinement` clause: refine once, prove the multiplicity bound for the
refinement, transport back.  Carrying it at the scale-`r` layer instead would mean producing
`Kakeya.VeryNotSticky.AScaleData` for a refined configuration and transporting the *conclusion*
of `Kakeya.VeryNotSticky.exists_aScaleData_of_le_one`, not its inputs. -/
theorem multiplicity_le_coarseLoss_mul_of_isCRefinement (cfg : VeryNotSticky.{u})
    {s' : Finset cfg.ι} {V' : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    (href : ShadedBody.IsCRefinement s' V' cfg.s (fun i ↦ (cfg.T i).toShadedBody)
      cfg.coarseLoss⁻¹) :
    ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.coarseLoss : ENNReal) * ShadedBody.multiplicity s' V' := by
  have hL0 : cfg.coarseLoss ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.one_le_coarseLoss)
  have h := href.mul_multiplicity_le
  rw [ENNReal.coe_inv hL0] at h
  refine (ENNReal.inv_mul_le_iff (ENNReal.coe_ne_zero.mpr hL0) ENNReal.coe_ne_top).mp ?_
  exact h


/-- **The exponent budget of `Kakeya.VeryNotSticky.aScaleVolume` affords the `δ^{3η}` that
`Kakeya.VeryNotSticky.card_le_card_subfamilyNodes_mul` costs — and the margin is `4η`.**

`Kakeya.aScaleExponentBudget` weakens the gain of `Kakeya.VeryNotSticky.coarseVolumeLower`
from `δ^{2η + ν/90}` to `δ^{ν/9}`; what is left over is `ν/9 - ν/90 - 2η = ν/10 - 2η`, which
under the standing `90 η ≤ ν` of Configuration `hyp:ml2setup` is at least `7η`.  Reading a
margin off a docstring is how this development has been wrong before, so it is compiled. -/
theorem three_eta_le_aScaleVolume_surplus {η ν : ℝ} (hη : 0 < η) (hνη : 90 * η ≤ ν) :
    3 * η ≤ ν / 9 - (ν / 90 + 2 * η) := by nlinarith

/-- **The margin is `7η` exactly, so `8η` is not affordable.**  The witness is the endpoint
`ν = 90 η` of `hνη`, where `ν/9 - ν/90 - 2η = 10η - η - 2η = 7η`. -/
theorem not_eight_eta_le_aScaleVolume_surplus :
    ¬ (∀ η ν : ℝ, 0 < η → 90 * η ≤ ν → 8 * η ≤ ν / 9 - (ν / 90 + 2 * η)) := by
  intro h
  have := h 1 90 one_pos (by norm_num)
  norm_num at this

end Kakeya.VeryNotSticky
