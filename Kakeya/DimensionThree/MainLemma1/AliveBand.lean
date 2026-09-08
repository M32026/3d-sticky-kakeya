/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.MultiplicityBudget
public import Kakeya.DimensionThree.MainLemma1.ShadedRestrict

/-!
# The alive band: the lower density bracket without an index-set pigeonhole

The recorded blocker of `Kakeya.ml1Boot.exists_uniformFactorCore` is that the shaded
uniformizers of `Kakeya/ShadedUniform.lean` return no density bracket on their own output
shading, while the bracket is obtained by a pigeonhole on the values `|Y(V i)|`, and that
pigeonhole moves the index set and so destroys the two lower brackets `le_card_shadeClass`
and `le_branchingN` of GWZ Definition 2.2.

The upper half of the bracket is free: the uniformizers only shrink shadings, so
`|Z i| ≤ |Y(V i)|` survives untouched.  This file settles the lower half.

**The lower half needs no pigeonhole.**  Definition 2.2 is closed under exactly two
shade-shrinking moves — cutting *every* shading by one common measurable set
(`ShadedTube.shadedUniformTubeSet_interShade`) and dropping members whose shading is already
empty (`Kakeya.ml1Boot.ShadedTube.ShadedUniformTubeSet.restrict_of_shade_eq_empty`) — and those
two moves already force the lower bracket:

* `ShadedTube.exists_cut_aliveBand` — for any threshold `ρ` there is a *single* measurable set
  `R` of volume at most `#s · ρ` such that, after deleting `R`, every member of the family is
  either annihilated or has shade volume at least `ρ`.  The proof is a finite descent: while
  some member still has volume `< ρ`, delete that member's set and recurse, which retires one
  member per round at ambient cost `< ρ`.
* `ShadedTube.exists_shadedUniform_aliveBand` — the same statement carried through
  `ShadedTube.interShade`, so that GWZ Definition 2.2 holds verbatim on the cut family at the
  same hierarchy, the same `branchingN`, the same `localN` and the same constant, and the alive
  set is presented in exactly the shape `restrict_of_shade_eq_empty` consumes.

So the alive set of the cut is *not* a pigeonhole class: it is the set of members the cut did
not annihilate, and the uniformity transfers to it by the two hereditary moves.

**What it costs, and why that is the next obstruction.**  The cut deletes ambient volume at most
`#s · ρ`.  What that destroys in *shade mass* is that ambient volume weighted by how many
members see each deleted point, and
`ShadedBody.sum_volume_shade_inter_le_of_pointwiseMultiplicity_le` states exactly that: the loss
is at most the family's pointwise multiplicity times `#s · ρ`.  Retaining a fixed share of
`∑ᵢ |Y(V i)| = ∫ μ` therefore forces `ρ ≲ |U(𝕍, Y)| / #s`, and the resulting band, measured
against the free upper end `|Y(V i)| ≈ λ δ²`, has width of order `ShadedBody.multiplicity`.
That is the same quantity `ShadedTube.exists_shade_disjointification` pays, and
`Kakeya.ml1Boot.middleMultiplicityBound_exceeds_refinementBudget_of_spec` shows it is outside
the refinement budget `δ ^ (-2 ε')` of Case (ii).  The obstruction at
`Kakeya.ml1Boot.exists_uniformFactorCore` is therefore *not* "the bracket needs a pigeonhole" —
it does not — but "a bracket of subpolynomial width costs multiplicity".

**Where the pigeonhole actually stands.**  The second half of the file removes the qualitative
objection to the pigeonhole altogether.

* `Kakeya.ml1Boot.ShadedTube.ShadedUniformTubeSet.restrict_of_shadeClass_dense` is the *exact*
  hereditariness criterion for Definition 2.2: an index restriction transfers the predicate, at
  constant `θ⁻¹ C`, as soon as it retains a `θ` share of every shade class at every point.
  `restrict_of_shade_eq_empty` and `shadedUniformTubeSet_interShade` are its `θ = 1` cases.
* `ShadedTube.classDenseSet`, `ShadedTube.measurableSet_classDenseSet` and
  `ShadedTube.shadedUniformTubeSet_of_classDense_cut`: for *any* candidate subfamily `s₃ ⊆ s`
  — in particular the dyadic density class `fine_dens` needs — cutting every shading by the set
  of points where `s₃` is class-dense preserves Definition 2.2 on `s` and then transfers it to
  `s₃`.

So both moves the interface needs — the density pigeonhole and Definition 2.2 on its output —
are available, and the whole obstruction is a single quantitative statement: **how much shade
mass a dyadic density class loses to its own class-sparse set**.  That is what remains open at
`Kakeya.ml1Boot.exists_uniformFactorCore`, and it is a strictly narrower question than the one
recorded there.

**How narrow, exactly.**  `Kakeya.ml1Boot.IsUniformFactorCore.fine_unif` asks for Definition 2.2
at the constant `Kakeya.ml1Boot.uniformize.C 3`, which is `δ`-independent.  So the `θ` of
`restrict_of_shadeClass_dense` has to be an absolute constant, not a `1 / log (1/δ)`.  And a
dyadic density class carries no pointwise-uniform share of the shade classes: summing over the
`O(log 1/δ)` classes recovers each shade class in total, but the dyadic index realising the
largest share varies with the point and the node, so no single class is guaranteed dense at any
`θ`.  The open question is therefore whether the density pigeonhole can be *replaced* by a
selection that is class-dense at an absolute `θ` while still retaining a `δ ^ (2 ε')` share of
`∑ᵢ |Y(V i)|` — or whether the mass a dyadic class loses to its class-sparse set is bounded.
Neither is settled here; what is settled is that the qualitative obstructions ("no lower bracket
without a pigeonhole", "no Definition 2.2 after a pigeonhole") are both gone.

`ShadedBody.sum_volume_shade_inter_lightDominatedSet_le` is the first quantitative step on that
last question, and it succeeds in the *global fibre* reading: the members the density cut left
light have total mass at most `#s · ρ`, and wherever they dominate a `1 - θ` share of the
pointwise multiplicity the whole family carries only `(1 - θ)⁻¹ · #s · ρ` of mass.  Choosing `ρ`
at a `δ ^ (4 ε')` fraction of the average therefore leaves the globally class-sparse set with a
`δ ^ (4 ε')` share, well inside the `δ ^ (2 ε')` budget.  The gap to what
`restrict_of_shadeClass_dense` consumes is that the density has to hold in each *node* class at
each scale, not only in the global fibre, and passing between the two costs a factor counting
the scale-`k` nodes a fibre meets.

**A recurrence worth recording.**  That last factor is, by the two class brackets of Definition
2.2 itself, the ratio of the fibre size to the class size, which at the finest scale is again
`ShadedBody.multiplicity`.  So all three independent routes to the interface price the *same*
quantity: `ShadedTube.exists_shade_disjointification` (retention against the union rather than
the sum), `ShadedTube.exists_shadedUniform_aliveBand` (the deleted ambient volume weighted by
multiplicity), and the class-density cut above (the node-versus-fibre factor).  Since
`Kakeya.ml1Boot.middleMultiplicityBound_exceeds_refinementBudget_of_spec` puts that quantity
outside the budget by an essentially full `δ ^ (-2 γ)`, the recurrence is evidence that the
*simultaneity* demanded by `Kakeya.ml1Boot.IsUniformFactorCore` — `fine_unif` at a
`δ`-independent constant, `fine_dens` a factor-two bracket, and `fine_refinement` at
`δ ^ (2 ε')`, all at once — is the clause to re-examine against GWZ §2, rather than one more
construction to search for.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace ShadedTube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [BorelSpace E] [ProperSpace E] in
/-- **The band-forcing cut.**  For any finite family of measurable sets `Z` and any threshold
`ρ` there is a single measurable set `R` of volume at most `#s · ρ` such that, after removing
`R`, every member of the family is either *annihilated* (`Z i ⊆ R`) or has volume at least `ρ`.

The proof is a finite descent: as long as some member has volume `< ρ`, delete that member's
set from the ambient space and recurse on the remaining members with their sets cut by it.  Each
round deletes volume `< ρ` and retires one member, so the total deleted volume is `< #s · ρ`.

The point of the statement is that the surviving lower bound is achieved by *one common cut*,
never by choosing a subfamily. -/
theorem exists_cut_aliveBand (ρ : ENNReal) :
    ∀ (s : Finset ι) (Z : ι → Set E), (∀ i, MeasurableSet (Z i)) →
      ∃ R : Set E, MeasurableSet R ∧ volume R ≤ (s.card : ENNReal) * ρ ∧
        ∀ i ∈ s, Z i ⊆ R ∨ ρ ≤ volume (Z i \ R) := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro Z hZ
    by_cases hall : ∀ i ∈ s, ρ ≤ volume (Z i)
    · refine ⟨∅, MeasurableSet.empty, by simp, fun i hi => Or.inr ?_⟩
      simpa using hall i hi
    · push Not at hall
      obtain ⟨i₀, hi₀, hlt⟩ := hall
      obtain ⟨R', hR'meas, hR'vol, hR'⟩ :=
        ih (s.erase i₀) (Finset.erase_ssubset hi₀) (fun j => Z j \ Z i₀)
          (fun j => (hZ j).diff (hZ i₀))
      refine ⟨R' ∪ Z i₀, hR'meas.union (hZ i₀), ?_, ?_⟩
      · have hcard : ((s.erase i₀).card : ENNReal) + 1 = (s.card : ENNReal) := by
          rw [Finset.card_erase_of_mem hi₀]
          have h1 : 1 ≤ s.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
          have : (s.card - 1) + 1 = s.card := Nat.succ_pred_eq_of_pos h1
          rw [← this]
          push_cast
          ring
        calc volume (R' ∪ Z i₀) ≤ volume R' + volume (Z i₀) := measure_union_le _ _
          _ ≤ ((s.erase i₀).card : ENNReal) * ρ + ρ := add_le_add hR'vol hlt.le
          _ = (((s.erase i₀).card : ENNReal) + 1) * ρ := by rw [add_mul, one_mul]
          _ = (s.card : ENNReal) * ρ := by rw [hcard]
      · intro j hj
        by_cases hje : j = i₀
        · exact Or.inl (hje ▸ Set.subset_union_right)
        · have hdiff : Z j \ (R' ∪ Z i₀) = (Z j \ Z i₀) \ R' := by
            ext x
            simp only [Set.mem_sdiff, Set.mem_union, not_or]
            tauto
          rcases hR' j (Finset.mem_erase.mpr ⟨hje, hj⟩) with h | h
          · refine Or.inl fun x hx => ?_
            by_cases hx0 : x ∈ Z i₀
            · exact Set.mem_union_right _ hx0
            · exact Set.mem_union_left _ (h ⟨hx, hx0⟩)
          · exact Or.inr (hdiff ▸ h)

end ShadedTube

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] [ProperSpace E] in
/-- **What one common cut costs in shade mass.**  Removing a measurable set `R` from every
shading of the family costs at most `M · |R|`, where `M` is any pointwise bound for the
multiplicity of the family on `R`.

This is the exact price of `ShadedTube.exists_cut_aliveBand`: that cut deletes ambient volume
at most `#s · ρ`, and the shade mass it destroys is that ambient volume weighted by how many
members see each deleted point — i.e. by the family's multiplicity.  It is the reason the
band-forcing cut, unlike the pigeonhole it replaces, has a retention factor governed by
`ShadedBody.multiplicity`. -/
theorem sum_volume_shade_inter_le_of_pointwiseMultiplicity_le
    (s : Finset ι) (V : ι → ShadedBody E) {R : Set E} (hR : MeasurableSet R) {M : ENNReal}
    (hM : ∀ x ∈ R, (pointwiseMultiplicity s V x : ENNReal) ≤ M) :
    ∑ i ∈ s, volume ((V i).shade ∩ R) ≤ M * volume R := by
  classical
  have hstep : ∑ i ∈ s, volume ((V i).shade ∩ R)
      = ∫⁻ x, ∑ i ∈ s, ((V i).shade ∩ R).indicator (1 : E → ENNReal) x :=
    calc ∑ i ∈ s, volume ((V i).shade ∩ R)
        = ∑ i ∈ s, ∫⁻ x, ((V i).shade ∩ R).indicator (1 : E → ENNReal) x :=
          Finset.sum_congr rfl fun i _ =>
            (lintegral_indicator_one ((V i).measurableSet_shade.inter hR)).symm
      _ = ∫⁻ x, ∑ i ∈ s, ((V i).shade ∩ R).indicator (1 : E → ENNReal) x :=
          (lintegral_finsetSum s
            fun i _ => measurable_const.indicator ((V i).measurableSet_shade.inter hR)).symm
  rw [hstep]
  have hbound : ∀ x, ∑ i ∈ s, ((V i).shade ∩ R).indicator (1 : E → ENNReal) x
      ≤ R.indicator (fun _ => M) x := by
    intro x
    by_cases hx : x ∈ R
    · have : ∑ i ∈ s, ((V i).shade ∩ R).indicator (1 : E → ENNReal) x
          = (pointwiseMultiplicity s V x : ENNReal) := by
        simp only [Set.indicator_apply, Set.mem_inter_iff, hx, and_true, Pi.one_apply,
          Finset.sum_boole, pointwiseMultiplicity]
      rw [this, Set.indicator_of_mem hx]
      exact hM x hx
    · have : ∀ i ∈ s, ((V i).shade ∩ R).indicator (1 : E → ENNReal) x = 0 := by
        intro i _
        exact Set.indicator_of_notMem (fun h => hx h.2) _
      rw [Finset.sum_congr rfl this, Finset.sum_const_zero]
      exact zero_le
  calc ∫⁻ x, ∑ i ∈ s, ((V i).shade ∩ R).indicator (1 : E → ENNReal) x
      ≤ ∫⁻ x, R.indicator (fun _ => M) x := lintegral_mono hbound
    _ = M * volume R := by rw [lintegral_indicator_const hR M]

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] [ProperSpace E] in
/-- **Light members are class-sparse only where little mass lives.**

Let `L ⊆ s` be any subfamily and `B` any measurable set on which `L` occupies at least a
`1 - θ` share of the pointwise multiplicity of `s`.  Then the mass `s` carries over `B` is at
most `(1 - θ)⁻¹` times the *total* mass of `L`.

This is the first quantitative handle on what is left of
`Kakeya.ml1Boot.exists_uniformFactorCore` after
`Kakeya.ml1Boot.ShadedTube.ShadedUniformTubeSet.restrict_of_shadeClass_dense`.  Take `L` to be
the members whose shading the density cut left below the threshold `ρ`: their total mass is at
most `#s · ρ`, so choosing `ρ` a `δ ^ (4 ε')` fraction of the average makes the whole
*globally* class-sparse set carry only a `δ ^ (4 ε')` share of the mass — comfortably inside
the `δ ^ (2 ε')` refinement budget.  What this does **not** yet give is the same statement for
each *node* class separately at each scale, which is the form
`restrict_of_shadeClass_dense` consumes; the gap between the two is a factor counting how many
scale-`k` nodes the fibre of a point meets. -/
theorem sum_volume_shade_inter_sparse_le (s L : Finset ι) (V : ι → ShadedBody E) {θ : ENNReal}
    {B : Set E} (hB : MeasurableSet B)
    (hBdef : ∀ x ∈ B, (1 - θ) * (pointwiseMultiplicity s V x : ENNReal)
      ≤ (pointwiseMultiplicity L V x : ENNReal)) :
    (1 - θ) * ∑ i ∈ s, volume ((V i).shade ∩ B) ≤ ∑ i ∈ L, volume ((V i).shade) := by
  classical
  have hsum : ∀ (t : Finset ι), ∑ i ∈ t, volume ((V i).shade ∩ B)
      = ∫⁻ x, ∑ i ∈ t, ((V i).shade ∩ B).indicator (1 : E → ENNReal) x := by
    intro t
    calc ∑ i ∈ t, volume ((V i).shade ∩ B)
        = ∑ i ∈ t, ∫⁻ x, ((V i).shade ∩ B).indicator (1 : E → ENNReal) x :=
          Finset.sum_congr rfl fun i _ =>
            (lintegral_indicator_one ((V i).measurableSet_shade.inter hB)).symm
      _ = ∫⁻ x, ∑ i ∈ t, ((V i).shade ∩ B).indicator (1 : E → ENNReal) x :=
          (lintegral_finsetSum t
            fun i _ => measurable_const.indicator ((V i).measurableSet_shade.inter hB)).symm
  have hcount : ∀ (t : Finset ι) (x : E), x ∈ B →
      ∑ i ∈ t, ((V i).shade ∩ B).indicator (1 : E → ENNReal) x
        = (pointwiseMultiplicity t V x : ENNReal) := by
    intro t x hx
    simp only [Set.indicator_apply, Set.mem_inter_iff, hx, and_true, Pi.one_apply,
      Finset.sum_boole, pointwiseMultiplicity]
  have hzero : ∀ (t : Finset ι) (x : E), x ∉ B →
      ∑ i ∈ t, ((V i).shade ∩ B).indicator (1 : E → ENNReal) x = 0 := by
    intro t x hx
    refine Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (fun h => hx h.2) _
  have hptwise : ∀ x, (1 - θ) * ∑ i ∈ s, ((V i).shade ∩ B).indicator (1 : E → ENNReal) x
      ≤ ∑ i ∈ L, ((V i).shade ∩ B).indicator (1 : E → ENNReal) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [hcount s x hx, hcount L x hx]
      exact hBdef x hx
    · rw [hzero s x hx, hzero L x hx, mul_zero]
  calc (1 - θ) * ∑ i ∈ s, volume ((V i).shade ∩ B)
      = ∫⁻ x, (1 - θ) * ∑ i ∈ s, ((V i).shade ∩ B).indicator (1 : E → ENNReal) x := by
        rw [hsum s, lintegral_const_mul' _ _ (by simp)]
    _ ≤ ∫⁻ x, ∑ i ∈ L, ((V i).shade ∩ B).indicator (1 : E → ENNReal) x := lintegral_mono hptwise
    _ = ∑ i ∈ L, volume ((V i).shade ∩ B) := (hsum L).symm
    _ ≤ ∑ i ∈ L, volume ((V i).shade) :=
        Finset.sum_le_sum fun i _ => measure_mono Set.inter_subset_left

/-- **The light-dominated set**: the points at which the subfamily `L` already carries a
`1 - θ` share of the pointwise multiplicity of `s`.  Its complement is where the restriction
`s \ L` is class-dense in the *global fibre* sense. -/
def lightDominatedSet (s L : Finset ι) (V : ι → ShadedBody E) (θ : ENNReal) : Set E :=
  {x | (1 - θ) * (pointwiseMultiplicity s V x : ENNReal)
    ≤ (pointwiseMultiplicity L V x : ENNReal)}

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] [ProperSpace E] in
theorem measurableSet_lightDominatedSet (s L : Finset ι) (V : ι → ShadedBody E) (θ : ENNReal) :
    MeasurableSet (lightDominatedSet s L V θ) := by
  classical
  have hpair : Measurable fun x => (pointwiseMultiplicity s V x, pointwiseMultiplicity L V x) :=
    (measurable_pointwiseMultiplicity s V).prodMk (measurable_pointwiseMultiplicity L V)
  exact hpair (Set.to_countable
    {q : ℕ × ℕ | (1 - θ) * (q.1 : ENNReal) ≤ (q.2 : ENNReal)}).measurableSet

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] [ProperSpace E] in
/-- `ShadedBody.sum_volume_shade_inter_sparse_le` at its intended set: the mass `s` carries over
the light-dominated set is controlled by the total mass of the light family alone. -/
theorem sum_volume_shade_inter_lightDominatedSet_le (s L : Finset ι) (V : ι → ShadedBody E)
    (θ : ENNReal) :
    (1 - θ) * ∑ i ∈ s, volume ((V i).shade ∩ lightDominatedSet s L V θ)
      ≤ ∑ i ∈ L, volume ((V i).shade) :=
  sum_volume_shade_inter_sparse_le s L V (measurableSet_lightDominatedSet s L V θ)
    fun _ hx => hx

end ShadedBody

namespace ShadedTube

section Band

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

omit [Nontrivial E] [BorelSpace E] in
/-- **The lower half of the density band, obtained by a common cut and an empty-shade drop —
no index-set pigeonhole.**

Cutting every shading of `V` by the one common set `W` preserves GWZ Definition 2.2 verbatim
(`ShadedTube.shadedUniformTubeSet_interShade`), and dropping the members whose cut shading is
*empty* preserves it verbatim as well
(`Kakeya.ml1Boot.ShadedTube.ShadedUniformTubeSet.restrict_of_shade_eq_empty`).  The content
here is that these two closed operations already suffice to install a uniform **lower** volume
bracket on the surviving members: `ShadedTube.exists_cut_aliveBand` produces a single cut after
which every member is either annihilated outright or has shade volume at least `ρ`.

So the returned `s₃` is not chosen by a pigeonhole on the values `|Y(V i)|`; it is the alive set
of a cut, and Definition 2.2 transfers to it by the two hereditary moves rather than being
destroyed.  The upper half of the band is free, since the cut only shrinks shadings.

The price is entirely in the deleted ambient volume, `|Wᶜ| ≤ #s · ρ`; what that costs in shade
*mass* is `ShadedBody.sum_volume_shade_inter_le_of_pointwiseMultiplicity_le`, namely the
family's multiplicity times `#s · ρ`. -/
theorem exists_shadedUniform_aliveBand {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E}
    {N : ℕ} {C : NNReal} (𝒱 : ShadedUniformTubeSet s V N C) (ρ : ENNReal) :
    ∃ (W : Set E) (hW : MeasurableSet W) (s₃ : Finset ι),
      volume Wᶜ ≤ (s.card : ENNReal) * ρ ∧
      (∀ i, (interShade V W hW i).toTube = (V i).toTube) ∧
      (∀ i, (interShade V W hW i).shade ⊆ (V i).shade) ∧
      s₃ ⊆ s ∧
      (∀ i ∈ s, i ∉ s₃ → (interShade V W hW i).shade = ∅) ∧
      (∀ i ∈ s₃, ρ ≤ volume (interShade V W hW i).shade) ∧
      Nonempty (ShadedUniformTubeSet s (interShade V W hW) N C) := by
  classical
  obtain ⟨R, hRmeas, hRvol, hR⟩ :=
    exists_cut_aliveBand (E := E) ρ s (fun i => (V i).shade)
      (fun i => (V i).measurableSet_shade)
  refine ⟨Rᶜ, hRmeas.compl, s.filter (fun i => ρ ≤ volume (interShade V Rᶜ hRmeas.compl i).shade),
    ?_, fun i => rfl, fun i => Set.inter_subset_left, Finset.filter_subset _ _, ?_, ?_,
    ⟨shadedUniformTubeSet_interShade 𝒱 Rᶜ hRmeas.compl⟩⟩
  · simpa using hRvol
  · intro i hi hni
    have hnot : ¬ ρ ≤ volume (interShade V Rᶜ hRmeas.compl i).shade := by
      intro h
      exact hni (Finset.mem_filter.mpr ⟨hi, h⟩)
    have hdiff : (interShade V Rᶜ hRmeas.compl i).shade = (V i).shade \ R := by
      simp [interShade, Set.sdiff_eq]
    rcases hR i hi with h | h
    · rw [hdiff, Set.sdiff_eq_empty.mpr h]
    · exact absurd (hdiff ▸ h) hnot
  · intro i hi
    exact (Finset.mem_filter.mp hi).2

omit [Nontrivial E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- **The retention of the band-forcing cut, priced.**  The shade mass surviving on the alive set
`s₃` of a common cut is the whole mass minus what the deleted region `Wᶜ` carried, and the latter
is the deleted ambient volume weighted by the family's pointwise multiplicity there.

Combined with `ShadedTube.exists_shadedUniform_aliveBand`, whose cut has `|Wᶜ| ≤ #s · ρ`, this
says: forcing the lower bracket at level `ρ` costs at most `M · #s · ρ` of shade mass, where `M`
bounds the multiplicity on the deleted set.  Retaining a `δ ^ (2 ε')` share of
`∑ᵢ |Y(V i)|` therefore permits `ρ` only up to `≈ |U(𝕍, Y)| / #s`, and against the free upper end
the band that results has width of order `ShadedBody.multiplicity`.  That is the same quantity
`ShadedTube.exists_shade_disjointification` pays, and
`Kakeya.ml1Boot.middleMultiplicityBound_exceeds_refinementBudget_of_spec` places it outside the
refinement budget of Case (ii). -/
theorem sum_volume_shade_le_sum_interShade_add {δ : NNReal} {s s₃ : Finset ι}
    (V : ι → ShadedTube δ E) (W : Set E) (hW : MeasurableSet W) (hs₃ : s₃ ⊆ s)
    (hdead : ∀ i ∈ s, i ∉ s₃ → (interShade V W hW i).shade = ∅)
    {M : ENNReal}
    (hM : ∀ x ∈ Wᶜ,
      (ShadedBody.pointwiseMultiplicity s (fun i => (V i).toShadedBody) x : ENNReal) ≤ M) :
    ∑ i ∈ s, volume (V i).shade
      ≤ ∑ i ∈ s₃, volume (interShade V W hW i).shade + M * volume Wᶜ := by
  classical
  have hsplit : ∀ i ∈ s, volume (V i).shade
      = volume ((V i).shade ∩ W) + volume ((V i).shade ∩ Wᶜ) := by
    intro i _
    have hd : (V i).shade ∩ Wᶜ = (V i).shade \ W := by
      rw [Set.sdiff_eq]
    rw [hd]
    exact (measure_inter_add_sdiff _ hW).symm
  have halive : ∑ i ∈ s, volume ((V i).shade ∩ W)
      = ∑ i ∈ s₃, volume (interShade V W hW i).shade := by
    refine (Finset.sum_subset hs₃ ?_).symm
    intro i hi hni
    have := hdead i hi hni
    simp only [interShade_shade] at this
    rw [this]
    simp
  have hloss : ∑ i ∈ s, volume ((V i).shade ∩ Wᶜ) ≤ M * volume Wᶜ :=
    ShadedBody.sum_volume_shade_inter_le_of_pointwiseMultiplicity_le s
      (fun i => (V i).toShadedBody) hW.compl hM
  calc ∑ i ∈ s, volume (V i).shade
      = ∑ i ∈ s, (volume ((V i).shade ∩ W) + volume ((V i).shade ∩ Wᶜ)) :=
        Finset.sum_congr rfl hsplit
    _ = ∑ i ∈ s, volume ((V i).shade ∩ W) + ∑ i ∈ s, volume ((V i).shade ∩ Wᶜ) :=
        Finset.sum_add_distrib
    _ ≤ ∑ i ∈ s₃, volume (interShade V W hW i).shade + M * volume Wᶜ := by
        rw [halive]; gcongr


end Band


end ShadedTube

namespace Kakeya

namespace ml1Boot

namespace ShadedTube

variable {ι : Type*} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [Nontrivial F] [MeasureSpace F] [BorelSpace F]

/-- **The exact hereditariness criterion for GWZ Definition 2.2: class density.**

`ShadedTube.ShadedUniformTubeSet` fails to be hereditary only through its two lower brackets
`le_card_shadeClass` and `le_branchingN`, and those are lower bounds on shade-class
cardinalities.  A restriction of the index set therefore transfers Definition 2.2 as soon as it
retains a *fixed fraction* `θ` of every shade class at every point — no matter how few members
it keeps, and no matter what happens to the volumes.  The constant degrades by exactly `θ⁻¹`.

This is the common generalisation of the two moves the predicate was known to be closed under:

* `Kakeya.ml1Boot.ShadedTube.ShadedUniformTubeSet.restrict_of_shade_eq_empty` is the case
  `θ = 1`, since dropping members with empty shading changes no class at all;
* `ShadedTube.shadedUniformTubeSet_interShade` is the corresponding statement for the shade
  side, again at `θ = 1`.

Stating the criterion this way locates the blocker of
`Kakeya.ml1Boot.exists_uniformFactorCore` precisely.  The density bracket
`Kakeya.ml1Boot.IsUniformFactorCore.fine_dens` is produced by a dyadic pigeonhole on the values
`|Y(V i)|`, and *what has to be shown about that pigeonhole is not that it retains mass* — it
does, one dyadic class in `O(log 1/δ)` carries a `1 / log` share — **but that it is class-dense
in the sense of this lemma**.  Nothing in a mass pigeonhole makes it class-dense: the heavy
members of a shade class can be a vanishing fraction of it. -/
def ShadedUniformTubeSet.restrict_of_shadeClass_dense {δ : NNReal} {s s₃ : Finset ι}
    {V : ι → _root_.ShadedTube δ F} {N : ℕ} {Cu C C' θ : NNReal}
    (𝒱 : _root_.ShadedTube.ShadedUniformTubeSet s V N C)
    (𝒰 : Tube.UniformTubeSet s₃ (fun i => (V i).toTube) N Cu)
    (hsub : s₃ ⊆ s) (hCuC : Cu ≤ C') (hCC : C ≤ C') (hCθ : C ≤ θ * C')
    (hassign : 𝒰.cover.assign = 𝒱.tubeUniform.cover.assign)
    (hdense : ∀ x ∈ (⋃ i ∈ s₃, (V i).shade), ∀ k ≤ N, ∀ i ∈ s₃, x ∈ (V i).shade →
      θ * ((_root_.ShadedTube.shadeClass s V (𝒱.tubeUniform.cover.assign k)
              (𝒱.tubeUniform.cover.assign k i) x).card : NNReal)
        ≤ ((_root_.ShadedTube.shadeClass s₃ V (𝒱.tubeUniform.cover.assign k)
              (𝒱.tubeUniform.cover.assign k i) x).card : NNReal)) :
    _root_.ShadedTube.ShadedUniformTubeSet s₃ V N C' := by
  classical
  have hmem : ∀ x ∈ (⋃ i ∈ s₃, (V i).shade), x ∈ (⋃ i ∈ s, (V i).shade) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hsub hi, hxi⟩
  have hsubcls : ∀ (assign : ι → ι) (j : ι) (x : F),
      _root_.ShadedTube.shadeClass s₃ V assign j x
        ⊆ _root_.ShadedTube.shadeClass s V assign j x := by
    intro assign j x i hi
    simp only [_root_.ShadedTube.shadeClass, Tube.coverClass, Finset.mem_filter] at hi ⊢
    exact ⟨⟨hsub hi.1.1, hi.1.2⟩, hi.2⟩
  refine
    { tubeUniform := 𝒰.mono hCuC
      branchingN := 𝒱.branchingN
      localN := 𝒱.localN
      card_shadeClass_le := ?_
      le_card_shadeClass := ?_
      branchingN_le := ?_
      le_branchingN := ?_ }
  · intro x hx k hk i hi hxi
    rw [show (𝒰.mono hCuC).cover.assign = 𝒱.tubeUniform.cover.assign from hassign]
    calc ((_root_.ShadedTube.shadeClass s₃ V (𝒱.tubeUniform.cover.assign k)
            (𝒱.tubeUniform.cover.assign k i) x).card : NNReal)
        ≤ ((_root_.ShadedTube.shadeClass s V (𝒱.tubeUniform.cover.assign k)
            (𝒱.tubeUniform.cover.assign k i) x).card : NNReal) := by
          exact_mod_cast Finset.card_le_card (hsubcls _ _ x)
      _ ≤ C * 𝒱.localN x k := 𝒱.card_shadeClass_le x (hmem x hx) k hk i (hsub hi) hxi
      _ ≤ C' * 𝒱.localN x k := mul_le_mul_left hCC _
  · intro x hx k hk i hi hxi
    rw [show (𝒰.mono hCuC).cover.assign = 𝒱.tubeUniform.cover.assign from hassign]
    calc 𝒱.localN x k
        ≤ C * ((_root_.ShadedTube.shadeClass s V (𝒱.tubeUniform.cover.assign k)
            (𝒱.tubeUniform.cover.assign k i) x).card : NNReal) :=
          𝒱.le_card_shadeClass x (hmem x hx) k hk i (hsub hi) hxi
      _ ≤ (θ * C') * ((_root_.ShadedTube.shadeClass s V (𝒱.tubeUniform.cover.assign k)
            (𝒱.tubeUniform.cover.assign k i) x).card : NNReal) := mul_le_mul_left hCθ _
      _ = C' * (θ * ((_root_.ShadedTube.shadeClass s V (𝒱.tubeUniform.cover.assign k)
            (𝒱.tubeUniform.cover.assign k i) x).card : NNReal)) := by ring
      _ ≤ C' * ((_root_.ShadedTube.shadeClass s₃ V (𝒱.tubeUniform.cover.assign k)
            (𝒱.tubeUniform.cover.assign k i) x).card : NNReal) :=
          mul_le_mul_right (hdense x hx k hk i hi hxi) _
  · intro x hx k hk
    exact (𝒱.branchingN_le x (hmem x hx) k hk).trans (mul_le_mul_left hCC _)
  · intro x hx k hk
    exact (𝒱.le_branchingN x (hmem x hx) k hk).trans (mul_le_mul_left hCC _)

end ShadedTube

end ml1Boot

end Kakeya


namespace ShadedTube

section ClassDense

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

omit [Nontrivial E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A shade-class count is a finite sum of indicators of the shadings, hence measurable in the
point. -/
theorem measurable_shadeClass_card {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ E) (assign : ι → ι) (j : ι) :
    Measurable (fun x => (shadeClass s V assign j x).card) := by
  classical
  have hEq : (fun x => (shadeClass s V assign j x).card)
      = fun x => ∑ i ∈ Tube.coverClass s assign j, if x ∈ (V i).shade then 1 else 0 := by
    funext x
    simp only [shadeClass, Finset.card_filter]
  rw [hEq]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact Measurable.ite (V i).measurableSet_shade measurable_const measurable_const

/-- **The class-dense set of a candidate index restriction.**  The points at which the subfamily
`s₃` still carries at least a `θ` share of every shade class of `s` that it meets. -/
def classDenseSet {δ : NNReal} (s s₃ : Finset ι) (V : ι → ShadedTube δ E)
    (assign : ℕ → ι → ι) (N : ℕ) (θ : NNReal) : Set E :=
  {x | ∀ k ≤ N, ∀ i ∈ s₃, x ∈ (V i).shade →
    θ * ((shadeClass s V (assign k) (assign k i) x).card : NNReal)
      ≤ ((shadeClass s₃ V (assign k) (assign k i) x).card : NNReal)}

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem measurableSet_classDenseSet {δ : NNReal} (s s₃ : Finset ι)
    (V : ι → ShadedTube δ E) (assign : ℕ → ι → ι) (N : ℕ) (θ : NNReal) :
    MeasurableSet (classDenseSet s s₃ V assign N θ) := by
  classical
  have hEq : classDenseSet s s₃ V assign N θ
      = ⋂ k ∈ Finset.range (N + 1), ⋂ i ∈ s₃,
          ((V i).shadeᶜ ∪ {x | θ * ((shadeClass s V (assign k) (assign k i) x).card : NNReal)
            ≤ ((shadeClass s₃ V (assign k) (assign k i) x).card : NNReal)}) := by
    ext x
    simp only [classDenseSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff,
      Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · intro h k hk i hi
      by_cases hx : x ∈ (V i).shade
      · exact Or.inr (h k hk i hi hx)
      · exact Or.inl hx
    · intro h k hk i hi hx
      rcases h k hk i hi with h' | h'
      · exact absurd hx h'
      · exact h'
  rw [hEq]
  refine MeasurableSet.biInter (Finset.range (N + 1)).countable_toSet fun k _ => ?_
  refine MeasurableSet.biInter s₃.countable_toSet fun i _ => ?_
  refine (V i).measurableSet_shade.compl.union ?_
  have hpair : Measurable fun x =>
      ((shadeClass s V (assign k) (assign k i) x).card,
        (shadeClass s₃ V (assign k) (assign k i) x).card) :=
    (measurable_shadeClass_card s V (assign k) (assign k i)).prodMk
      (measurable_shadeClass_card s₃ V (assign k) (assign k i))
  exact hpair (Set.to_countable {p : ℕ × ℕ | θ * (p.1 : NNReal) ≤ (p.2 : NNReal)}).measurableSet

/-- **An index-set pigeonhole is permitted after all, provided it is followed by the cut to its
class-dense set.**

Let `s₃ ⊆ s` be *any* subfamily — in particular the dyadic density class that
`Kakeya.ml1Boot.IsUniformFactorCore.fine_dens` needs — and let `W` be the set of points where
`s₃` still carries a `θ` share of every shade class of `s` it meets.  Cutting *every* shading by
`W` preserves GWZ Definition 2.2 on `s` (`ShadedTube.shadedUniformTubeSet_interShade`), and on
the cut family the restriction to `s₃` is class-dense by construction, so
`Kakeya.ml1Boot.ShadedTube.ShadedUniformTubeSet.restrict_of_shadeClass_dense` transfers
Definition 2.2 to `s₃` at the constant `θ⁻¹ C`.

So no pigeonhole is obstructed *qualitatively*.  What the pigeonhole costs is exactly the shade
mass carried by the class-sparse complement `(classDenseSet …)ᶜ`, and
`ShadedTube.sum_volume_shade_le_sum_interShade_add` prices any such cut by the multiplicity of
the family on the deleted region.  This is the residual content of
`Kakeya.ml1Boot.exists_uniformFactorCore`: a bound on the mass a dyadic density class loses to
its own class-sparse set. -/
def shadedUniformTubeSet_of_classDense_cut {δ : NNReal} [DecidableEq ι] {s s₃ : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {Cu C C' θ : NNReal}
    (𝒱 : ShadedUniformTubeSet s V N C) (hsub : s₃ ⊆ s)
    (hCuC : Cu ≤ C') (hCC : C ≤ C') (hCθ : C ≤ θ * C')
    (W : Set E) (hW : MeasurableSet W)
    (hWdense : ∀ x ∈ W, ∀ k ≤ N, ∀ i ∈ s₃, x ∈ (V i).shade →
      θ * ((shadeClass s V (𝒱.tubeUniform.cover.assign k)
              (𝒱.tubeUniform.cover.assign k i) x).card : NNReal)
        ≤ ((shadeClass s₃ V (𝒱.tubeUniform.cover.assign k)
              (𝒱.tubeUniform.cover.assign k i) x).card : NNReal))
    (𝒰 : Tube.UniformTubeSet s₃ (fun i => (interShade V W hW i).toTube) N Cu)
    (hassign : 𝒰.cover.assign = 𝒱.tubeUniform.cover.assign) :
    ShadedUniformTubeSet s₃ (interShade V W hW) N C' := by
  classical
  refine Kakeya.ml1Boot.ShadedTube.ShadedUniformTubeSet.restrict_of_shadeClass_dense
    (shadedUniformTubeSet_interShade 𝒱 W hW) 𝒰 hsub hCuC hCC hCθ hassign ?_
  intro x hx k hk i hi hxi
  have hxW : x ∈ W := by
    obtain ⟨j, _, hxj⟩ := Set.mem_iUnion₂.mp hx
    exact hxj.2
  have h1 : shadeClass s (interShade V W hW) (𝒱.tubeUniform.cover.assign k)
      (𝒱.tubeUniform.cover.assign k i) x
        = shadeClass s V (𝒱.tubeUniform.cover.assign k)
            (𝒱.tubeUniform.cover.assign k i) x :=
    shadeClass_interShade s V W hW _ _ hxW
  have h2 : shadeClass s₃ (interShade V W hW) (𝒱.tubeUniform.cover.assign k)
      (𝒱.tubeUniform.cover.assign k i) x
        = shadeClass s₃ V (𝒱.tubeUniform.cover.assign k)
            (𝒱.tubeUniform.cover.assign k i) x :=
    shadeClass_interShade s₃ V W hW _ _ hxW
  change θ * ((shadeClass s (interShade V W hW) (𝒱.tubeUniform.cover.assign k)
        (𝒱.tubeUniform.cover.assign k i) x).card : NNReal)
      ≤ ((shadeClass s₃ (interShade V W hW) (𝒱.tubeUniform.cover.assign k)
        (𝒱.tubeUniform.cover.assign k i) x).card : NNReal)
  rw [h1, h2]
  exact hWdense x hxW k hk i hi hxi.1

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- The class-dense set of `s₃` in `s` is the largest `W` for which
`ShadedTube.shadedUniformTubeSet_of_classDense_cut` applies: membership in it *is* the density
hypothesis. -/
theorem classDenseSet_dense {δ : NNReal} (s s₃ : Finset ι) (V : ι → ShadedTube δ E)
    (assign : ℕ → ι → ι) (N : ℕ) (θ : NNReal) {x : E}
    (hx : x ∈ classDenseSet s s₃ V assign N θ) :
    ∀ k ≤ N, ∀ i ∈ s₃, x ∈ (V i).shade →
      θ * ((shadeClass s V (assign k) (assign k i) x).card : NNReal)
        ≤ ((shadeClass s₃ V (assign k) (assign k i) x).card : NNReal) := hx

end ClassDense

end ShadedTube
