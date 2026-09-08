/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.ShadedDisjointUniform
public import Kakeya.DimensionThree.MainLemma1.Setup

/-!
# The multiplicity price of disjointification, weighed against the refinement budget

`ShadedTube.exists_shadedUniform_banded` delivers, for the first time in this development, GWZ
Definition 2.2 (`ShadedTube.ShadedUniformTubeSet`) and a two-sided density bracket **at once**,
by disjointifying the shading first (`ShadedTube.exists_shade_disjointification`) and reading
Definition 2.2 off the retained disjointness
(`ShadedTube.nonempty_shadedUniformTubeSet_of_pairwiseDisjoint`).  Its retention is stated
against the union volume `|⋃_{i ∈ s} Y(V_i)|`, whereas every consumer in the factoring chain —
`Kakeya.ml1Boot.IsUniformFactorCore.fine_refinement`,
`Kakeya.ml1Boot.IsFactorTwoScales.fine_refinement` — is stated against the shade mass
`∑_{i ∈ s} |Y(V_i)|`.  The two differ by exactly `ShadedBody.multiplicity s V`.

So the route closes for a given family **iff** that family's multiplicity is inside its
consumer's refinement budget.  On the fine family the multiplicity is the very quantity Main
Lemma 1 bounds, so the trade is circular there.  It is *not* circular for the middle and coarse
families of the two-scale chain, whose multiplicities are outputs of the proved
`Kakeya.ml1Boot.exists_factorOneScale`, and the question left open at
`Kakeya.ml1Boot.exists_factorTwoScales_of_frostmanDividingBlock` was whether **those** numbers
are inside the budget.

## The verdict recorded in this file: they are not

`Kakeya.ml1Boot.middleMultiplicityBound_exceeds_refinementBudget` is the certificate.  The
refinement budget of the fine clause is `δ ^ (2 ε')` and the density budget of
`Kakeya.ml1Boot.IsFactorTwoScales.mid_fullness` is `δ ^ ε'`, i.e. the admissible multiplicity
loss is `δ ^ (-2 ε')` with `ε' = p.ε' = p.η 0 / 16`, a *subpolynomial* budget.  The only bound
on the middle multiplicity that the leaf carries is its own middle clause,

  `ShadedBody.multiplicity (fibre t'τ pθ l₀) Yτ`
      `≤ δ ^ (10 av) * (τ/θ) ^ (-2 γ) * (#(fibre t'τ pθ l₀) * (τ/θ) ^ 2) ^ (1 - γ / 2)`,

and at the block end `τ / θ = δ` — permitted, since the leaf only asks `δ ≤ τ ≤ θ ≤ 1` — with a
fibre of the maximal cardinality `#fibre ≥ (τ/θ) ^ (-2)` that right-hand side is at least
`δ ^ (10 av - 2 γ)`.  Since the rung satisfies `10 av < 2 (γ - ε')` for every rung the ladder can
select once `p.η 0` is small relative to `γ` — which is exactly what `Kakeya.ml1Boot.Params.Spec`
supplies — the permitted middle multiplicity exceeds the budget by the *polynomial* factor
`δ ^ (-(2 γ - 2 ε' - 10 av))`.

The certificate is therefore: no proof of "the middle multiplicity is inside the refinement
budget" can be derived from the data the leaf carries, because the leaf's own middle clause
already permits values a fixed positive power of `1/δ` above it.  The answer is the same for the
coarse clause, whose right-hand side `δ ^ (-4 av') * θ ^ (-2 γ) * (#t'θ * θ ^ 2) ^ (1 - γ / 2)`
is *larger* still (`av' ≥ 0` makes `δ ^ (-4 av') ≥ 1`), and which at `θ = δ` and
`#t'θ ≥ θ ^ (-2)` is at least `δ ^ (-2 γ)`.

## The second, unconditional obstruction: disjointness fights `contain`

Even where the arithmetic happened to close, disjointifying the *middle* family is incompatible
with the nesting clauses `Kakeya.ml1Boot.IsFactorTwoScales.contain_fine` and `.contain_mid`
unless the fine shadings are cut to match, and that cut costs the fine family a second factor of
the middle multiplicity against the budget `δ ^ (2 ε')` of `fine_refinement`.  What the
disjointification *does* buy is recorded positively below in
`Kakeya.ml1Boot.disjoint_shade_of_parent_ne_of_pairwiseDisjoint`: with a disjointly shaded
parent family the fine shadings become disjoint **across fibres**, so the global fine
multiplicity collapses to the fibrewise one.  That is a genuine gain, and it is the only part of
the disjointification route that survives this file's verdict.
-/

@[expose] public section

open MeasureTheory

namespace Kakeya

namespace ml1Boot

/-! ### The arithmetic certificate -/

/-- **The middle-multiplicity clause of
`Kakeya.ml1Boot.exists_factorTwoScales_of_frostmanDividingBlock` permits values a fixed positive
power of `1/δ` above the refinement budget `δ ^ (-2 ε')`.**

Stated at the extreme block `τ / θ = δ` and at a fibre of the maximal cardinality
`#fibre ≥ (τ/θ) ^ (-2)`, both of which the leaf's hypotheses permit.  The hypothesis
`10 * av < 2 * (γ - ε')` is the ladder's rung constraint: `av` is the blueprint's `η_{j-1}`,
bounded by `p.η 0 = 16 ε'`, so it holds as soon as `162 * ε' < 2 * γ`, i.e. as soon as `p.η 0`
is small relative to `γ`.

This is the negative answer to the question left open at
`Kakeya.ml1Boot.exists_factorTwoScales_of_frostmanDividingBlock`: the middle multiplicity is
**not** inside the refinement budget, so the disjointification route of
`ShadedTube.exists_shadedUniform_banded` does not close the leaf on the middle family either. -/
theorem middleMultiplicityBound_exceeds_refinementBudget
    {γ ε' av M δ : ℝ} (hγ1 : γ ≤ 1) (_hav0 : 0 ≤ av)
    (hrung : 10 * av < 2 * (γ - ε'))
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hM : δ ^ (-2 : ℝ) ≤ M) :
    δ ^ (-2 * ε')
      < δ ^ (10 * av) * δ ^ (-2 * γ) * (M * δ ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  have hδ0' : (0:ℝ) < δ := hδ0
  -- `M * δ ^ 2 ≥ 1`
  have hδsq : δ ^ (2 : ℕ) = δ ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast δ 2]; norm_num
  have hone : (1 : ℝ) ≤ M * δ ^ (2 : ℕ) := by
    have h := mul_le_mul_of_nonneg_right hM (le_of_lt (pow_pos hδ0 2))
    refine le_trans (le_of_eq ?_) h
    rw [hδsq, ← Real.rpow_add hδ0]
    norm_num
  -- hence `(M * δ ^ 2) ^ (1 - γ / 2) ≥ 1`
  have hexp : (0 : ℝ) ≤ 1 - γ / 2 := by linarith
  have hpow : (1 : ℝ) ≤ (M * δ ^ (2 : ℕ)) ^ (1 - γ / 2) :=
    Real.one_le_rpow hone hexp
  -- and `δ ^ (10 av) * δ ^ (-2 γ) = δ ^ (10 av - 2 γ) > δ ^ (-2 ε')`
  have hcomb : δ ^ (10 * av) * δ ^ (-2 * γ) = δ ^ (10 * av + -2 * γ) :=
    (Real.rpow_add hδ0 _ _).symm
  have hstrict : δ ^ (-2 * ε') < δ ^ (10 * av + -2 * γ) := by
    refine Real.rpow_lt_rpow_of_exponent_gt hδ0 hδ1 ?_
    linarith
  calc δ ^ (-2 * ε') < δ ^ (10 * av + -2 * γ) := hstrict
    _ = δ ^ (10 * av) * δ ^ (-2 * γ) := hcomb.symm
    _ ≤ δ ^ (10 * av) * δ ^ (-2 * γ) * (M * δ ^ (2 : ℕ)) ^ (1 - γ / 2) := by
        refine le_mul_of_one_le_right ?_ hpow
        positivity

/-- **The coarse clause is weaker still.**  At `θ = δ` and `#t'θ ≥ θ ^ (-2)` the right-hand side
of the coarse multiplicity clause of
`Kakeya.ml1Boot.exists_factorTwoScales_of_frostmanDividingBlock` is at least `δ ^ (-2 γ)`, which
exceeds the budget `δ ^ (-2 ε')` whenever `ε' < γ`.  The loss exponent `av'` only helps the
bound, `δ ^ (-4 av') ≥ 1` for `av' ≥ 0`, so no rung choice rescues it. -/
theorem coarseMultiplicityBound_exceeds_refinementBudget
    {γ ε' av' M δ : ℝ} (hγ1 : γ ≤ 1) (hav0 : 0 ≤ av')
    (hεγ : ε' < γ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hM : δ ^ (-2 : ℝ) ≤ M) :
    δ ^ (-2 * ε')
      < δ ^ (-4 * av') * δ ^ (-2 * γ) * (M * δ ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  have hbase :=
    middleMultiplicityBound_exceeds_refinementBudget (γ := γ) (ε' := ε') (av := 0) (M := M)
      (δ := δ) hγ1 le_rfl (by linarith) hδ0 hδ1 hM
  refine lt_of_lt_of_le hbase ?_
  have h1 : δ ^ (10 * (0:ℝ)) ≤ δ ^ (-4 * av') := by
    refine Real.rpow_le_rpow_of_exponent_ge hδ0 (le_of_lt hδ1) ?_
    nlinarith
  have h2 : (0:ℝ) ≤ δ ^ (-2 * γ) := le_of_lt (Real.rpow_pos_of_pos hδ0 _)
  have h3 : (0:ℝ) ≤ (M * δ ^ (2 : ℕ)) ^ (1 - γ / 2) :=
    Real.rpow_nonneg (by nlinarith [Real.rpow_pos_of_pos hδ0 (-2:ℝ), pow_pos hδ0 2]) _
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h2) h3
  exact this

/-! ### The rung hypothesis is supplied by `Params.Spec`, with room to spare -/

/-- **`Kakeya.ml1Boot.Params.Spec` supplies the rung hypothesis of
`Kakeya.ml1Boot.middleMultiplicityBound_exceeds_refinementBudget`, by a factor of nearly `200`.**

Every rung of the ladder satisfies `η_j ≤ η_N ≤ ε / 5`, while `γ ≥ γ₀ ≥ 192 ε`: the clause
`ninetySixEpsLe` reads `96 ε ≤ gap β γ₀ = γ₀ - max β (γ₀ / 2) ≤ γ₀ / 2`.  Hence
`10 η_j ≤ 2 ε` and `2 (γ - ε') ≥ 384 ε - ε / 40`, and the gap between them is a factor of
about `190`.

This is the verification the leaf's route note asked for: the condition "`η 0` small relative
to `γ`" is not a borderline numerical demand on the package — the ladder is geometric,
`η_j = κ ^ (N - j + 1)` with `κ ≤ ε² / 200` and `N ≥ 4096`, so `η 0` is smaller than `γ` by an
astronomical margin.  Consequently the verdict of
`Kakeya.ml1Boot.middleMultiplicityBound_exceeds_refinementBudget` is *not* an artefact of a
tight parameter choice: the middle multiplicity clause permits values above the refinement
budget by essentially the full factor `δ ^ (-2 γ)`. -/
theorem ten_eta_lt_two_gamma_sub_epsPrime {β γ₀ γ : ℝ} {p : Params} (hspec : p.Spec β γ₀)
    (hγ : γ ∈ Set.Icc γ₀ 1) {j : ℕ} (hj : j ≤ p.N) :
    10 * p.η j < 2 * (γ - p.ε') := by
  have hε : 0 < p.ε := hspec.epsPos
  have hjN : p.η j ≤ p.η p.N := hspec.etaMono (Set.mem_Iic.mpr hj) (Set.mem_Iic.mpr le_rfl) hj
  have h0N : p.η 0 ≤ p.η p.N :=
    hspec.etaMono (Set.mem_Iic.mpr (Nat.zero_le _)) (Set.mem_Iic.mpr le_rfl) (Nat.zero_le _)
  have htop : p.η p.N ≤ p.ε / 5 := hspec.etaTop
  have hη0 : 0 < p.η 0 := hspec.etaZeroPos
  have hgap : 96 * p.ε ≤ gap β γ₀ := hspec.ninetySixEpsLe
  have hgapLe : gap β γ₀ ≤ γ₀ / 2 := by
    have : γ₀ / 2 ≤ betaPrime β γ₀ := le_max_right _ _
    simp only [gap]
    linarith
  have hγ₀ : 192 * p.ε ≤ γ₀ := by linarith
  have hγγ₀ : γ₀ ≤ γ := hγ.1
  have hε' : p.ε' = p.η 0 / 16 := hspec.epsPrimeEq
  linarith

/-- **The verdict, at the parameters the leaf actually carries.**

Combining `Kakeya.ml1Boot.middleMultiplicityBound_exceeds_refinementBudget` with
`Kakeya.ml1Boot.ten_eta_lt_two_gamma_sub_epsPrime`: for *every* rung `j ≤ p.N` the ladder can
select, at the extreme block `τ / θ = δ` and a fibre of maximal cardinality, the middle
multiplicity clause of `Kakeya.ml1Boot.exists_factorTwoScales_of_frostmanDividingBlock` permits
values strictly above the refinement budget `δ ^ (-2 ε')`.

**So the answer to the question left open there is no**, and the disjointification route of
`ShadedTube.exists_shadedUniform_banded` is closed for the middle family of the two-scale chain
as well as for the fine one — for the fine family by circularity, for the middle family by this
inequality. -/
theorem middleMultiplicityBound_exceeds_refinementBudget_of_spec
    {β γ₀ γ : ℝ} {p : Params} (hspec : p.Spec β γ₀) (hγ : γ ∈ Set.Icc γ₀ 1)
    {j : ℕ} (hj : j ≤ p.N) {M δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hM : δ ^ (-2 : ℝ) ≤ M) :
    δ ^ (-2 * p.ε')
      < δ ^ (10 * p.η j) * δ ^ (-2 * γ) * (M * δ ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  have h0j : p.η 0 ≤ p.η j :=
    hspec.etaMono (Set.mem_Iic.mpr (Nat.zero_le _)) (Set.mem_Iic.mpr hj) (Nat.zero_le _)
  have hηj : 0 ≤ p.η j := le_trans (le_of_lt hspec.etaZeroPos) h0j
  exact middleMultiplicityBound_exceeds_refinementBudget hγ.2 hηj
    (ten_eta_lt_two_gamma_sub_epsPrime hspec hγ hj) hδ0 hδ1 hM

end ml1Boot

end Kakeya

namespace Kakeya

namespace ml1Boot

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### What the disjointification does buy: cross-fibre disjointness -/

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **A disjointly shaded parent family forces the child shadings to be disjoint across
fibres.**

If the middle shadings `Yτ` are pairwise disjoint on `t'` and the fine shadings are nested in
them along the parent map (`Kakeya.ml1Boot.IsFactorTwoScales.contain_fine`), then two fine
members with *different* parents have disjoint shadings.  Consequently the global fine
multiplicity is controlled by the fibrewise ones alone — the only part of the disjointification
route that survives the verdict of
`Kakeya.ml1Boot.middleMultiplicityBound_exceeds_refinementBudget`. -/
theorem disjoint_shade_of_parent_ne_of_pairwiseDisjoint
    {ι κ : Type*} {s' : Finset ι} {t' : Finset κ}
    {Y' : ι → ShadedBody E} {Yτ : κ → ShadedBody E} {p : ι → κ}
    (hmaps : ∀ i ∈ s', p i ∈ t')
    (hcontain : ∀ i ∈ s', (Y' i).shade ⊆ (Yτ (p i)).shade)
    (hdisj : (t' : Set κ).Pairwise fun k k' => Disjoint (Yτ k).shade (Yτ k').shade)
    {i j : ι} (hi : i ∈ s') (hj : j ∈ s') (hne : p i ≠ p j) :
    Disjoint (Y' i).shade (Y' j).shade :=
  Disjoint.mono (hcontain i hi) (hcontain j hj)
    (hdisj (by exact_mod_cast hmaps i hi) (by exact_mod_cast hmaps j hj) hne)

/-! ### A hereditariness that does hold: dropping members whose shading is already empty -/

namespace ShadedTube

variable {ι : Type*} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]

omit [Nontrivial F] in
/-- **Shade classes do not see members with empty shading.**  If every member of `s` outside
`s₃` has empty shading then the shade class of any node at any point is literally the same
computed in `s₃` as in `s`. -/
theorem shadeClass_restrict_of_shade_eq_empty {δ : NNReal} {s s₃ : Finset ι}
    (V : ι → ShadedTube δ F) (hsub : s₃ ⊆ s)
    (hdead : ∀ i ∈ s, i ∉ s₃ → (V i).shade = ∅)
    (assign : ι → ι) (j : ι) (x : F) :
    ShadedTube.shadeClass s₃ V assign j x = ShadedTube.shadeClass s V assign j x := by
  classical
  ext i
  simp only [ShadedTube.shadeClass, Tube.coverClass, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hi3, hja⟩, hx⟩
    exact ⟨⟨hsub hi3, hja⟩, hx⟩
  · rintro ⟨⟨his, hja⟩, hx⟩
    refine ⟨⟨?_, hja⟩, hx⟩
    by_contra hn
    rw [hdead i his hn] at hx
    exact hx

/-- **Definition 2.2 is hereditary along the drop of empty-shaded members.**

`ShadedTube.ShadedUniformTubeSet` fails to be hereditary in general — the recorded blocker at
`Kakeya.ml1Boot.exists_uniformFactorCore` — because its two lower brackets
`le_card_shadeClass` and `le_branchingN` are lower bounds on filtered cardinalities and shrink
under restriction.  They do **not** shrink when the dropped members carry no shading at all: by
`ShadedTube.shadeClass_restrict_of_shade_eq_empty` every shade class is unchanged, and the shade
union is unchanged, so all four brackets transfer verbatim at the same `branchingN` and the same
`localN`.

Only the *tube* hierarchy has to be re-supplied on `s₃`, and it must carry the same assignment
maps, which is what a restriction in the sense of
`Kakeya.MultiScaleFac.exists_restrict_uniformTubeSet_band` produces.

This is the exact hereditariness the output of
`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` needs: that uniformizer keeps the
index set fixed and implements its fibre pruning by *emptying* the pruned members' shadings, so
its alive set may be split off afterwards for free — in particular a two-sided density bracket
may be asked for on the alive set without destroying Definition 2.2.  It is *not* enough to close
`Kakeya.ml1Boot.exists_uniformFactorCore`, since the surviving members can still have
incomparable shade volumes; see the header of this file. -/
def ShadedUniformTubeSet.restrict_of_shade_eq_empty {δ : NNReal} {s s₃ : Finset ι}
    {V : ι → ShadedTube δ F} {N : ℕ} {Cu C : NNReal}
    (𝒱 : ShadedTube.ShadedUniformTubeSet s V N C)
    (𝒰 : Tube.UniformTubeSet s₃ (fun i => (V i).toTube) N Cu)
    (hsub : s₃ ⊆ s) (hCuC : Cu ≤ C)
    (hdead : ∀ i ∈ s, i ∉ s₃ → (V i).shade = ∅)
    (hassign : 𝒰.cover.assign = 𝒱.tubeUniform.cover.assign) :
    ShadedTube.ShadedUniformTubeSet s₃ V N C := by
  classical
  have hunion : (⋃ i ∈ s₃, (V i).shade) = (⋃ i ∈ s, (V i).shade) := by
    apply Set.Subset.antisymm
    · exact Set.iUnion₂_subset fun i hi => Set.subset_iUnion₂_of_subset i (hsub hi) le_rfl
    · refine Set.iUnion₂_subset fun i hi => ?_
      by_cases h3 : i ∈ s₃
      · exact Set.subset_iUnion₂_of_subset i h3 le_rfl
      · rw [hdead i hi h3]; exact Set.empty_subset _
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
    rw [shadeClass_restrict_of_shade_eq_empty V hsub hdead _ _ x]
    exact 𝒱.card_shadeClass_le x (hunion ▸ hx) k hk i (hsub hi) hxi
  · intro x hx k hk i hi hxi
    rw [show (𝒰.mono hCuC).cover.assign = 𝒱.tubeUniform.cover.assign from hassign]
    rw [shadeClass_restrict_of_shade_eq_empty V hsub hdead _ _ x]
    exact 𝒱.le_card_shadeClass x (hunion ▸ hx) k hk i (hsub hi) hxi
  · intro x hx k hk
    exact 𝒱.branchingN_le x (hunion ▸ hx) k hk
  · intro x hx k hk
    exact 𝒱.le_branchingN x (hunion ▸ hx) k hk

/-! ### The mass retention the interface needs is already available, without disjointification -/

/-- **Definition 2.2 with mass retention against the shade *sum*, at subpolynomial cost and at a
fixed index set.**

This is `ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` with its `fullness'`
conclusion read as a mass inequality: the tubes are untouched by that uniformizer, so the two
`fullness'` quotients have the same denominator `∑_{i ∈ s} |V_i|`, which is positive and finite,
and the retention transfers to the numerators.

The point is what it shows about the shape of the remaining gap.  The retention here is against
`∑_{i ∈ s} |Y(V_i)|` — exactly what `Kakeya.ml1Boot.IsUniformFactorCore.fine_refinement` and
`Kakeya.ml1Boot.IsFactorTwoScales.fine_refinement` ask for — and the loss `(clamp+1)^{2N+2}` is
subpolynomial at `N = Tube.ssfGridLen δ = ⌈log log (1/δ)⌉`.  **No multiplicity appears.**  So the
`µ(𝕍, Y)` price of `ShadedTube.exists_shade_disjointification` — the price this file's verdict
`Kakeya.ml1Boot.middleMultiplicityBound_exceeds_refinementBudget` rules out of budget — is a
price of that *route* and not of the interface: mass retention with Definition 2.2 does not need
disjointification at all.

What the route through this lemma does **not** deliver is the *lower* half of the density
bracket `Kakeya.ml1Boot.IsUniformFactorCore.fine_dens`.  The uniformizer shrinks shadings
per tube, and only the average density is retained, so an individual member may keep an
arbitrarily small fraction of its shading — including none at all.  Its upper half survives for
free, `|Z_i| ≤ |Y(V_i)| ≤ 2 λ |V_i|` for any band the input carried, and the band pigeonhole that
would restore the lower half moves the index set and so destroys the two lower brackets of
Definition 2.2.

That is the residual gap, and it is strictly narrower than the one recorded at
`Kakeya.ml1Boot.exists_uniformFactorCore`: **not** "a shaded uniformizer that returns a density
bracket", but "a two-sided volume band on the alive output of a shaded uniformizer that already
returns everything else".
`Kakeya.ml1Boot.ShadedTube.ShadedUniformTubeSet.restrict_of_shade_eq_empty` above disposes of
the members the uniformizer kills outright; what is left is the spread among the survivors. -/
theorem sum_shade_le_of_shadedUniform_of_uniformTubeSet {δ : NNReal} (hδ : 0 < δ)
    {s : Finset ι} {V : ι → ShadedTube δ F} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s (fun i => (V i).toTube) N C) (hN : 0 < N)
    (clamp : ℕ) (hclamp : ∀ t : Finset ι, t ⊆ s → Nat.log 2 t.card ≤ clamp)
    (hs : s.Nonempty) :
    ∃ V' : ι → ShadedTube δ F,
      (∀ i, (V' i).toTube = (V i).toTube) ∧
      (∀ i, (V' i).shade ⊆ (V i).shade) ∧
      (∑ i ∈ s, volume (V i).shade)
          ≤ ((clamp + 1 : ℕ) : ENNReal) ^ (2 * N + 2) * ∑ i ∈ s, volume (V' i).shade ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s V' N (max C 4)) := by
  classical
  obtain ⟨V', hVto, hVsub, hfull, 𝒱, -, -, -, -⟩ :=
    ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet 𝒰 hN clamp hclamp
  refine ⟨V', hVto, hVsub, ?_, ⟨𝒱⟩⟩
  set K : ENNReal := ((clamp + 1 : ℕ) : ENNReal) ^ (2 * N + 2) with hK
  set D : ENNReal := ∑ i ∈ s, volume ((V i).toShadedBody).carrier with hD
  have hcarpos : ∀ i : ι, 0 < volume (V i).carrier := by
    intro i
    have hle := Tube.le_volume (V i).toTube
    have hcpos : 0 < (Tube.le_volume.c (Module.finrank ℝ F) : ENNReal) :=
      ENNReal.coe_pos.mpr (Tube.le_volume.c_pos (Module.finrank ℝ F))
    have hδp : 0 < (δ : ENNReal) ^ (Module.finrank ℝ F - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ) _
    exact lt_of_lt_of_le (ENNReal.mul_pos (ne_of_gt hcpos) (ne_of_gt hδp)) (by simpa using hle)
  have hD0 : D ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ := hs
    refine ne_of_gt (lt_of_lt_of_le (hcarpos i₀) ?_)
    exact Finset.single_le_sum (f := fun i => volume ((V i).toShadedBody).carrier)
      (fun i _ => zero_le) hi₀
  have hDtop : D ≠ ⊤ :=
    ne_of_lt (ENNReal.sum_lt_top.mpr fun i _ =>
      lt_of_le_of_ne le_top (V i).isCompact.measure_ne_top)
  have hDeq : (∑ i ∈ s, volume ((V' i).toShadedBody).carrier) = D := by
    rw [hD]
    exact Finset.sum_congr rfl fun i _ =>
      congrArg (fun T : Tube δ F => volume T.carrier) (hVto i)
  have hfull' : (∑ i ∈ s, volume (V i).shade) / D
      ≤ K * ((∑ i ∈ s, volume (V' i).shade) / D) := by
    simpa [ShadedBody.fullness', hD, hDeq, hK] using hfull
  have hmul := mul_le_mul_left hfull' D
  rwa [ENNReal.div_mul_cancel hD0 hDtop, mul_assoc,
    ENNReal.div_mul_cancel hD0 hDtop] at hmul

end ShadedTube

end ml1Boot

end Kakeya
