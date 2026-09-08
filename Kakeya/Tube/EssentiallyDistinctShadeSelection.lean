/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.EssentiallyDistinctReduction
public import Kakeya.Multiplicity

/-!
# The essentially-distinct selection, made aware of the shading

`Kakeya.Tube.refineToEssDistinctLeaves` extracts from any finite family of `δ`-tubes a pairwise
essentially distinct subfamily at the cardinality loss `C_n · Δ_max`.  It selects by geometry alone,
so its conclusion is a share of the *indices*, and
`Kakeya.ML2Inputs.no_mass_share_of_essDistinct_refinement` shows that a share of the indices does
**not** imply a share of the shaded mass: on a two-element family whose first tube carries all the
shading, the subfamily consisting of the second tube keeps half the indices and none of the mass.

That refutation is about *deducing* mass from cardinality.  It leaves open — and this file settles —
whether the selection itself can be made to keep the mass.  It can, at the same constant and with no
extra datum:

**`exists_pairwise_essDistinct_subfamily_sum_shade_le`**: every finite family of shaded `δ`-tubes
with `Δ_max ≤ D` has a pairwise essentially distinct subfamily `u ⊆ s` with

  `∑_{i ∈ s} |Y_i| ≤ (1 + C_n · D) · ∑_{i ∈ u} |Y_i|`.

In particular the pointwise hypothesis `Kakeya.ML2Shaded.HasDenseShading`, which
`Kakeya.ML2Inputs.sum_shade_le_of_essDistinct_refinement` needs, is **not** required in order to
obtain a mass share: it is required only in order to read one off a *given* selection.

## The argument

Choose `u` to be a pairwise essentially distinct subset of `s` **maximising the retained shaded
mass** `∑_{i ∈ u} |Y_i|` (the pairwise essentially distinct subsets form a nonempty finite family,
so a maximiser exists).  For `j ∈ s \ u` let `N j = {i ∈ u | ¬ ED (T i) (T j)}` be the members of
`u` that conflict with `j`.  Then `(u \ N j) ∪ {j}` is again pairwise essentially distinct — `j` is
essentially distinct from every retained member outside `N j` by definition — so maximality gives

  `∑_{u \ N j} |Y| + |Y_j| ≤ ∑_{u \ N j} |Y| + ∑_{N j} |Y|`,  i.e.  `|Y_j| ≤ ∑_{i ∈ N j} |Y_i|`.

Summing over `j ∈ s \ u` and exchanging the order of summation replaces the left side by the
discarded mass and the right side by `∑_{i ∈ u} #{j ∈ s | ¬ ED (T i) (T j)} · |Y_i|`, and the
conflict degree `#{j ∈ s | ¬ ED (T i) (T j)}` is at most `C_n · Δ_max` — the same count, with the
same constant, that `Kakeya.Tube.refineToEssDistinctLeaves` performs internally, here exported as
`Kakeya.Tube.card_conflictClass_le`.

## What this does and does not settle for GWZ Proposition 6.6(B)

`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData` demands leaf-scale essential
distinctness of the fine family, and `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` did not
supply it when this file was written — nor could its other hypotheses imply it, since they are all
invariant under duplicating a tube while essential distinctness is not
(`Kakeya.not_pairwise_essDistinct_of_carrier_eq`).  The statement
carries the binder itself (GWZ Definition 2.1(ii) at `ρ = δ`, entailed by "uniform"), so the
reduction below is no longer needed to close it; it remains the tool for any caller that holds a
non-distinct family.  This file supplies the two transports that reduction needs on the *shaded*
side, both at the single loss `1 + C_n · D`:

* the multiplicity, `exists_pairwise_essDistinct_subfamily_multiplicity_le`;
* the fullness, `fullness'_le_mul_of_essDistinct_shadeSelection`.

Independently of the loss, a subfamily does not inherit
`Tube.IsUniformAtScale` or `Tube.UniformTubeSet`: their branching brackets are two-sided, so a
subfamily that empties one node breaks the lower half. That is why the tree re-uniformizes rather
than restricts (`Tube.exists_uniformTubeSet_subfamily_ssf`,
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`), at a further loss of its own.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {ι : Type*}

/-! ### The conflict class of a tube, and its size -/

open Classical in
/-- **The conflict class of `T i` inside `s`**: the members of the family that are *not* essentially
distinct from `T i`.  It contains `i` itself whenever `i ∈ s` and `0 < δ`, since a tube of positive
finite volume is not essentially distinct from itself. -/
def Tube.conflictClass {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) (i : ι) : Finset ι :=
  {j ∈ s | ¬ IsEssentiallyDistinct (T i).carrier (T j).carrier}

omit [Nontrivial E] in
theorem Tube.mem_conflictClass_iff {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {i j : ι} :
    j ∈ Tube.conflictClass s T i ↔
      j ∈ s ∧ ¬ IsEssentiallyDistinct (T i).carrier (T j).carrier := by
  classical
  simp [Tube.conflictClass]

/-- **The conflict degree of a tube family is at most `C_n · Δ_max`.**

A tube that is not essentially distinct from `T i` meets `T i` in more than half of `|T i|`, hence
lies inside the bounded dilate `K` provided by `Kakeya.Tube.overlapContainment`; the number of
members of the family inside a convex body is controlled by the maximal density through
`Kakeya.card_familyIn_le`.  This is the count that
`Kakeya.Tube.refineToEssDistinctLeaves` performs inside its own proof, with the same constant,
stated on the conflict class rather than on a covering piece. -/
theorem Tube.card_conflictClass_le {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (s : Finset ι) (T : ι → Tube δ E) {D : ENNReal}
    (hD : maxDensity s (fun k => (T k).toConvexSpaceBody) ≤ D) (i : ι) :
    ((Tube.conflictClass s T i).card : ENNReal)
      ≤ Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) * D := by
  classical
  set n := Module.finrank ℝ E with hn
  set L := (Tube.le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1) with hL
  have hLpos : L ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Tube.le_volume.c_pos n).ne')
      (pow_ne_zero _ (by exact_mod_cast hδ0.ne'))
  have hLfin : L ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  obtain ⟨K, hKvol, hKcont⟩ := Tube.overlapContainment hδ0 hδ1 (T i)
  -- the conflict class sits inside the family contained in `K`
  have hsub : Tube.conflictClass s T i ⊆ familyIn s (fun k => (T k).toConvexSpaceBody) K := by
    intro j hj
    rw [Tube.mem_conflictClass_iff] at hj
    obtain ⟨hjs, hnot⟩ := hj
    have hnot_unfold : (1 / 2 : ENNReal) * max (volume (T i).carrier) (volume (T j).carrier) <
        volume ((T i).carrier ∩ (T j).carrier) := lt_of_not_ge hnot
    have hhalf : (1 / 2 : ENNReal) * volume (T i).carrier <
        volume ((T i).carrier ∩ (T j).carrier) := by
      calc
        (1 / 2 : ENNReal) * volume (T i).carrier ≤
            (1 / 2 : ENNReal) * max (volume (T i).carrier) (volume (T j).carrier) := by
          gcongr; exact le_max_left _ _
        _ < volume ((T i).carrier ∩ (T j).carrier) := hnot_unfold
    have hcont : (T j).carrier ⊆ K.carrier := hKcont (T j) hhalf
    simp only [familyIn, Finset.mem_filter]
    exact ⟨hjs, hcont⟩
  -- and that family is counted by the density
  obtain ⟨oc, hoc⟩ : ∃ x, Tube.overlapContainment.C n = x := ⟨_, rfl⟩
  obtain ⟨Cn, hCn⟩ : ∃ x, Tube.refineToEssDistinctLeaves.C n = x := ⟨_, rfl⟩
  have hCc : Cn * (Tube.le_volume.c n : ENNReal) = oc * (Tube.volume_le.C n : ENNReal) := by
    rw [← hCn]
    dsimp only [Tube.refineToEssDistinctLeaves.C]
    rw [hoc]
    exact ENNReal.div_mul_cancel (by exact_mod_cast (Tube.le_volume.c_pos n).ne')
      ENNReal.coe_ne_top
  have hKv : volume K.carrier ≤ oc * volume (T i).carrier := by rw [← hoc, hn]; exact hKvol
  rw [hCn]
  have hcards : ((Tube.conflictClass s T i).card : ENNReal)
      ≤ ((familyIn s (fun k => (T k).toConvexSpaceBody) K).card : ENNReal) := by
    exact_mod_cast Finset.card_le_card hsub
  have hineq : ((Tube.conflictClass s T i).card : ENNReal) * L ≤ Cn * D * L := by
    calc
      ((Tube.conflictClass s T i).card : ENNReal) * L
          ≤ ((familyIn s (fun k => (T k).toConvexSpaceBody) K).card : ENNReal) * L := by
            gcongr
        _ ≤ maxDensity s (fun k => (T k).toConvexSpaceBody) * volume K.carrier :=
            card_familyIn_le s T K
        _ ≤ D * volume K.carrier := by gcongr
        _ ≤ D * (oc * volume (T i).carrier) := by gcongr
        _ ≤ D * (oc * ((Tube.volume_le.C n : ENNReal) * (δ : ENNReal) ^ (n - 1))) := by
            gcongr
            exact Tube.volume_le hδ1 (T i)
        _ = Cn * D * L := by
            rw [hL]
            rw [show D * (oc * ((Tube.volume_le.C n : ENNReal) * (δ : ENNReal) ^ (n - 1)))
                = oc * (Tube.volume_le.C n : ENNReal) * D * (δ : ENNReal) ^ (n - 1) from by ring,
              ← hCc]
            ring
  have hcomm : L * ((Tube.conflictClass s T i).card : ENNReal) ≤ L * (Cn * D) := by
    rw [mul_comm L ((Tube.conflictClass s T i).card : ENNReal), mul_comm L (Cn * D)]; exact hineq
  exact (ENNReal.mul_le_mul_iff_right hLpos hLfin).mp hcomm

/-! ### Essential distinctness is not invariant under duplication -/

/-- **Two members with the same carrier destroy pairwise essential distinctness.**

A `δ`-tube with `0 < δ` has positive finite volume, and no such set is essentially distinct from
itself.  This is why no *other* hypothesis of `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`
can imply essential distinctness of its fine family: each of them (containment in the unit ball,
grid uniformity, fullness, the factorisation datum) is satisfied by a family in which one tube has
been listed twice, and this is not — which is why, since, the statement carries the
binder explicitly. -/
theorem not_pairwise_essDistinct_of_carrier_eq {δ : NNReal} (hδ0 : 0 < δ)
    {s : Finset ι} {T : ι → Tube δ E} {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (hne : i ≠ j)
    (heq : (T i).carrier = (T j).carrier) :
    ¬ (s : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) := by
  intro hpair
  have hvol_pos : volume (T i).carrier ≠ 0 := by
    have h1 : (0 : NNReal) <
        Tube.le_volume.c (Module.finrank ℝ E) * δ ^ (Module.finrank ℝ E - 1) :=
      mul_pos (Tube.le_volume.c_pos _) (pow_pos hδ0 _)
    exact ne_of_gt (lt_of_lt_of_le (by exact_mod_cast h1) (Tube.le_volume (T i)))
  have hED : IsEssentiallyDistinct (T i).carrier (T j).carrier := hpair hi hj hne
  rw [← heq] at hED
  exact not_isEssentiallyDistinct_self hvol_pos (T i).isCompact.measure_lt_top.ne hED

/-! ### The shade-maximising selection -/

/-- **The essentially-distinct selection, keeping the shaded mass.**

Every finite family of shaded `δ`-tubes with maximal density at most `D` has a pairwise essentially
distinct subfamily retaining all but a factor `1 + C_n · D` of the shaded mass.  No hypothesis on
the shading is used: the selection is made by maximising the retained mass, not by geometry alone.
See the module docstring for the argument and for how this relates to
`Kakeya.ML2Inputs.no_mass_share_of_essDistinct_refinement`, which it does not contradict. -/
theorem exists_pairwise_essDistinct_subfamily_sum_shade_le {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (s : Finset ι) (V : ι → ShadedTube δ E) {D : ENNReal}
    (hD : maxDensity s (fun i => (V i).toTube.toConvexSpaceBody) ≤ D) :
    ∃ u ⊆ s,
      (u : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ∧
      ∑ i ∈ s, volume (V i).shade
        ≤ (1 + Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) * D)
            * ∑ i ∈ u, volume (V i).shade := by
  classical
  set T : ι → Tube δ E := fun i => (V i).toTube with hT
  set Cn := Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) with hCn
  -- shade volumes are finite
  have hfin : ∀ i : ι, volume (V i).shade ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (V i).isCompact.measure_ne_top (measure_mono (V i).shade_subset)
  have hsumfin : ∀ w : Finset ι, (∑ i ∈ w, volume (V i).shade) ≠ ⊤ := by
    intro w
    exact ENNReal.sum_ne_top.mpr fun i _ => hfin i
  -- the pairwise essentially distinct subsets of `s`
  set F : Finset (Finset ι) :=
    s.powerset.filter (fun w => (w : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier)) with hF
  have hFne : F.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [hF]
  obtain ⟨u, huF, hmax⟩ := Finset.exists_max_image F (fun w => ∑ i ∈ w, volume (V i).shade) hFne
  have hus : u ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp huF).1
  have hupair : (u : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) :=
    (Finset.mem_filter.mp huF).2
  refine ⟨u, hus, hupair, ?_⟩
  -- the conflicting part of `u` for a discarded index
  set N : ι → Finset ι := fun j =>
    u.filter (fun i => ¬ IsEssentiallyDistinct (V i).carrier (V j).carrier) with hN
  have hNsub : ∀ j, N j ⊆ u := fun j => Finset.filter_subset _ _
  -- the key exchange step
  have hkey : ∀ j ∈ s, j ∉ u → volume (V j).shade ≤ ∑ i ∈ N j, volume (V i).shade := by
    intro j hjs hju
    set w : Finset ι := (u \ N j) ∪ {j} with hw
    have hwF : w ∈ F := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · refine Finset.union_subset ?_ ?_
        · exact (Finset.sdiff_subset).trans hus
        · simpa using hjs
      · intro x hx y hy hxy
        simp only [hw, Finset.coe_union, Finset.coe_sdiff, Finset.coe_singleton,
          Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff] at hx hy
        have hmemED : ∀ z : ι, z ∈ u → z ∉ N j →
            IsEssentiallyDistinct (V z).carrier (V j).carrier := by
          intro z hzu hzN
          by_contra hc
          exact hzN (Finset.mem_filter.mpr ⟨hzu, hc⟩)
        rcases hx with hx | hx
        · rcases hy with hy | hy
          · exact hupair hx.1 hy.1 hxy
          · subst hy
            exact hmemED x hx.1 (by simpa using hx.2)
        · subst hx
          rcases hy with hy | hy
          · exact isEssentiallyDistinct_symm (hmemED y hy.1 (by simpa using hy.2))
          · exact absurd hy.symm hxy
    have hdisj : Disjoint (u \ N j) ({j} : Finset ι) := by
      simp only [Finset.disjoint_singleton_right, Finset.mem_sdiff]
      exact fun h => hju h.1
    have hsumw : ∑ i ∈ w, volume (V i).shade
        = (∑ i ∈ u \ N j, volume (V i).shade) + volume (V j).shade := by
      rw [hw, Finset.sum_union hdisj, Finset.sum_singleton]
    have hsumu : (∑ i ∈ u \ N j, volume (V i).shade) + ∑ i ∈ N j, volume (V i).shade
        = ∑ i ∈ u, volume (V i).shade := Finset.sum_sdiff (hNsub j)
    have hle := hmax w hwF
    rw [hsumw, ← hsumu] at hle
    exact (ENNReal.add_le_add_iff_left (hsumfin (u \ N j))).mp hle
  -- the discarded mass, bounded by the conflict degrees
  have hswap : ∑ j ∈ s \ u, volume (V j).shade ≤ Cn * D * ∑ i ∈ u, volume (V i).shade := by
    have h1 : ∑ j ∈ s \ u, volume (V j).shade
        ≤ ∑ j ∈ s \ u, ∑ i ∈ N j, volume (V i).shade := by
      refine Finset.sum_le_sum fun j hj => ?_
      rw [Finset.mem_sdiff] at hj
      exact hkey j hj.1 hj.2
    have h2 : ∑ j ∈ s \ u, ∑ i ∈ N j, volume (V i).shade
        = ∑ i ∈ u,
            (((s \ u).filter
              (fun j => ¬ IsEssentiallyDistinct (V i).carrier (V j).carrier)).card : ENNReal)
              * volume (V i).shade := by
      calc ∑ j ∈ s \ u, ∑ i ∈ N j, volume (V i).shade
          = ∑ j ∈ s \ u, ∑ i ∈ u,
              (if ¬ IsEssentiallyDistinct (V i).carrier (V j).carrier
                then volume (V i).shade else 0) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hN]
            exact (Finset.sum_filter _ _)
        _ = ∑ i ∈ u, ∑ j ∈ s \ u,
              (if ¬ IsEssentiallyDistinct (V i).carrier (V j).carrier
                then volume (V i).shade else 0) := Finset.sum_comm
        _ = ∑ i ∈ u,
              (((s \ u).filter
                (fun j => ¬ IsEssentiallyDistinct (V i).carrier (V j).carrier)).card : ENNReal)
                * volume (V i).shade := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have h3 : ∀ i ∈ u,
        (((s \ u).filter
          (fun j => ¬ IsEssentiallyDistinct (V i).carrier (V j).carrier)).card : ENNReal)
          * volume (V i).shade ≤ Cn * D * volume (V i).shade := by
      intro i _
      have hcardle : (((s \ u).filter
          (fun j => ¬ IsEssentiallyDistinct (V i).carrier (V j).carrier)).card : ENNReal)
            ≤ Cn * D := by
        refine le_trans ?_ (Tube.card_conflictClass_le hδ0 hδ1 s T hD i)
        have hsub' : ((s \ u).filter
            (fun j => ¬ IsEssentiallyDistinct (V i).carrier (V j).carrier))
              ⊆ Tube.conflictClass s T i := by
          intro j hj
          rw [Finset.mem_filter, Finset.mem_sdiff] at hj
          rw [Tube.mem_conflictClass_iff]
          exact ⟨hj.1.1, hj.2⟩
        exact_mod_cast Finset.card_le_card hsub'
      exact mul_le_mul' hcardle le_rfl
    calc ∑ j ∈ s \ u, volume (V j).shade
        ≤ ∑ j ∈ s \ u, ∑ i ∈ N j, volume (V i).shade := h1
      _ = ∑ i ∈ u,
            (((s \ u).filter
              (fun j => ¬ IsEssentiallyDistinct (V i).carrier (V j).carrier)).card : ENNReal)
              * volume (V i).shade := h2
      _ ≤ ∑ i ∈ u, Cn * D * volume (V i).shade := Finset.sum_le_sum h3
      _ = Cn * D * ∑ i ∈ u, volume (V i).shade := by rw [Finset.mul_sum]
  -- assemble
  have hsplit : (∑ i ∈ s \ u, volume (V i).shade) + ∑ i ∈ u, volume (V i).shade
      = ∑ i ∈ s, volume (V i).shade := Finset.sum_sdiff hus
  calc ∑ i ∈ s, volume (V i).shade
      = (∑ i ∈ s \ u, volume (V i).shade) + ∑ i ∈ u, volume (V i).shade := hsplit.symm
    _ ≤ Cn * D * (∑ i ∈ u, volume (V i).shade) + ∑ i ∈ u, volume (V i).shade := by
        gcongr
    _ = (1 + Cn * D) * ∑ i ∈ u, volume (V i).shade := by ring

/-- **The multiplicity transports across the shade-maximising selection**, at the same loss.

`ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset` needs exactly the mass share and
the containment of shading unions, and a subfamily supplies the second for free. -/
theorem exists_pairwise_essDistinct_subfamily_multiplicity_le {δ : NNReal}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (s : Finset ι) (V : ι → ShadedTube δ E) {D : ENNReal}
    (hD : maxDensity s (fun i => (V i).toTube.toConvexSpaceBody) ≤ D) :
    ∃ u ⊆ s,
      (u : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ∧
      ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
        ≤ (1 + Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) * D)
            * ShadedBody.multiplicity u (fun i => (V i).toShadedBody) := by
  obtain ⟨u, hus, hpair, hmass⟩ :=
    exists_pairwise_essDistinct_subfamily_sum_shade_le hδ0 hδ1 s V hD
  refine ⟨u, hus, hpair, ?_⟩
  refine ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset
    s (fun i => (V i).toShadedBody) u (fun i => (V i).toShadedBody) _ ?_ hmass
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨i, hus hi, hxi⟩

/-- **The essentially-distinct reduction of a GWZ-shaped multiplicity bound, priced.**

Suppose the bound

  `µ(𝕋', Y) ≤ A · Δ_max(𝕋')^{1-β} · #𝕋'^β`

is known for every pairwise essentially distinct subfamily `𝕋' ⊆ 𝕋`.  Then it holds for `𝕋`
itself with `A` replaced by `(1 + C_n · D) · A`, where `D` is any bound on `Δ_max(𝕋)`.  The three
transports are: the multiplicity, through
`Kakeya.exists_pairwise_essDistinct_subfamily_multiplicity_le`; the density, through
`Kakeya.maxDensity_mono`; and the cardinality, through `Finset.card_le_card`.  Nothing else about
the family is used, and nothing else is available: a subfamily inherits neither
`Tube.IsUniformAtScale` nor `Tube.UniformTubeSet`, both being pigeonhole conclusions, and it does
not carry a factorisation datum.

**This is the exact price of the leaf-scale essential-distinctness hypothesis of
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData`.**  It is polynomial in `Δ_max`,
whereas the conclusion of `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` prices `Δ_max` at the
exponent `1 - β` and grants only the subpolynomial slack `δ^{-ε}`; so the reduction is payable
exactly where a subpolynomial bound on `Δ_max` is in hand. -/
theorem multiplicity_le_of_essDistinct_subfamily_bound {δ : NNReal}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (s : Finset ι) (V : ι → ShadedTube δ E) {D : ENNReal}
    (hD : maxDensity s (fun i => (V i).toTube.toConvexSpaceBody) ≤ D)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {A : ENNReal}
    (hbound : ∀ u ⊆ s, (u : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) →
      ShadedBody.multiplicity u (fun i => (V i).toShadedBody)
        ≤ A * (maxDensity u (fun i => (V i).toTube.toConvexSpaceBody)) ^ (1 - β)
            * (u.card : ENNReal) ^ β) :
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
      ≤ (1 + Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) * D) * A
          * (maxDensity s (fun i => (V i).toTube.toConvexSpaceBody)) ^ (1 - β)
          * (s.card : ENNReal) ^ β := by
  obtain ⟨u, hus, hpair, hmult⟩ :=
    exists_pairwise_essDistinct_subfamily_multiplicity_le hδ0 hδ1 s V hD
  have hdens : maxDensity u (fun i => (V i).toTube.toConvexSpaceBody)
      ≤ maxDensity s (fun i => (V i).toTube.toConvexSpaceBody) :=
    maxDensity_mono (fun i => (V i).toTube.toConvexSpaceBody) hus
  have hcard : (u.card : ENNReal) ≤ (s.card : ENNReal) := by
    exact_mod_cast Finset.card_le_card hus
  calc ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
      ≤ (1 + Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) * D)
          * ShadedBody.multiplicity u (fun i => (V i).toShadedBody) := hmult
    _ ≤ (1 + Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) * D)
          * (A * (maxDensity u (fun i => (V i).toTube.toConvexSpaceBody)) ^ (1 - β)
              * (u.card : ENNReal) ^ β) := by
        exact mul_le_mul' le_rfl (hbound u hus hpair)
    _ ≤ (1 + Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) * D)
          * (A * (maxDensity s (fun i => (V i).toTube.toConvexSpaceBody)) ^ (1 - β)
              * (s.card : ENNReal) ^ β) := by
        gcongr
    _ = (1 + Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) * D) * A
          * (maxDensity s (fun i => (V i).toTube.toConvexSpaceBody)) ^ (1 - β)
          * (s.card : ENNReal) ^ β := by ring

/-- **The fullness transports across the shade-maximising selection**, at the same loss.

The retained mass is at least `(1 + C_n · D)⁻¹` of the total while the retained carrier mass is at
most the total, so the ratio drops by at most that factor. -/
theorem fullness'_le_mul_of_essDistinct_shadeSelection {δ : NNReal}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (s : Finset ι) (V : ι → ShadedTube δ E) {D : ENNReal}
    (hD : maxDensity s (fun i => (V i).toTube.toConvexSpaceBody) ≤ D) :
    ∃ u ⊆ s,
      (u : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ∧
      ShadedBody.fullness' s (fun i => (V i).toShadedBody)
        ≤ (1 + Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) * D)
            * ShadedBody.fullness' u (fun i => (V i).toShadedBody) := by
  obtain ⟨u, hus, hpair, hmass⟩ :=
    exists_pairwise_essDistinct_subfamily_sum_shade_le hδ0 hδ1 s V hD
  refine ⟨u, hus, hpair, ?_⟩
  have hcar : ∑ i ∈ u, volume (V i).carrier ≤ ∑ i ∈ s, volume (V i).carrier :=
    Finset.sum_le_sum_of_subset hus
  calc ShadedBody.fullness' s (fun i => (V i).toShadedBody)
      = (∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier) := rfl
    _ ≤ ((1 + Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) * D)
          * ∑ i ∈ u, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier) := by
        gcongr
    _ ≤ ((1 + Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) * D)
          * ∑ i ∈ u, volume (V i).shade) / (∑ i ∈ u, volume (V i).carrier) := by
        gcongr
    _ = (1 + Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) * D)
          * ShadedBody.fullness' u (fun i => (V i).toShadedBody) := by
        simp only [ShadedBody.fullness', div_eq_mul_inv, mul_assoc]

end

end Kakeya

end
