/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupLocalMass
public import Kakeya.DimensionThree.MainLemma2.ShadeClassBand
public import Kakeya.DimensionThree.Plank.RelativeMultiplicity

/-!
# Transport of GWZ (87) through later refinements

The multi-scale chain for the residue `Kakeya.VeryNotSticky.LocalMassRefinementResidue` applies
the one-scale bridge `Kakeya.VeryNotSticky.localMassAt_clause_of_rhoTubesSection9` at a sparse
set of grid indices, each application refining the family further. The clause established at
index `j` for the family `(s_m, T_m)` must survive every *later* refinement down to the final
family `(s*, T*)`. This file certifies that it does, with explicit constants and **no**
re-uniformisation between bridge steps.

* **T1 — the clause is monotone on the left.** `LocalMassClauseRel` freezes the right-hand side
  of `Kakeya.VeryNotSticky.LocalMassClauseAt` at a volume `Vol`. Its left-hand side is monotone
  in the shade union (`Metric.cthickening` and `∩ ball` are monotone), so a clause recorded
  relative to `|U₀|` transports to any sub-refinement (`LocalMassClauseRel.mono_union`), and turns
  back into a clause for that sub-refinement once `Vol ≤ Λ · |U*|` (`LocalMassClauseRel.toClauseAt`,
  gain `Λ⁻¹ · g`, no positivity of `Λ` needed). `pointwiseMultiplicity_mono` is the fibre
  monotonicity `pm* ≤ pm₀`.
* **T2 — the two-sided multiplicity bracket at the coarsest grid index.** For a family carrying
  `ShadedTube.ShadedUniformTubeSet s V N C` (GWZ Definition 2.2) in the unit ball, at every point
  `x` of the shade union
  `branchingN 0 ≤ C² · pm(x)` and `pm(x) ≤ C³ · branchingN 0`
  (`ShadedTube.ShadedUniformTubeSet.pointwiseMultiplicity_bracket_zero`). The lower half is
  `branchingN_le ∘ le_card_shadeClass` on any member of the fibre; the upper half is
  `card_fibre_eq_sum_card_shadeClass` with each class `≤ C · localN ≤ C² · branchingN` and the
  number of scale-`0` nodes met by the fibre `≤ C` by `Tube.UniformTubeSet.boundedOverlap` at
  `k = 0` tested against a unit tube containing `closedBall 0 1`
  (`ShadedTube.card_nodes_met_zero_le`). **The true power is `C² · C³ = C⁵`**, with
  `C = ShadedTube.ssfUniformConst 3` at the chain's first family.
* **T3 — the volume comparison.** For the first (uniformised) family `(s₀, T₀)` and any
  refinement `(s₁, T₁)` (index subset, shades cut) retaining a `c`-fraction of the total shading
  mass, `|U₀| ≤ (C⁵ / c) · |U₁|` (`volume_biUnion_shade_le_of_shadedUniform_of_retention`):
  layer cake on both unions (`Plank.sum_volume_shade_inter_eq_lintegral_multiplicity`), the lower
  bracket on `U₀`, fibre monotonicity plus the upper bracket on `U₁`, and the retention; the
  branching number cancels. The uniformity of the *final* family is not consumed. The
  `ShadedBody.IsCRefinement` forms and the `IsCRefinement.trans` composition give the total
  retention `c_{0→*}` of the chain, and `LocalMassClauseAt.transport_of_isCRefinement` is the
  transport in the shape the chain uses: the clause for an intermediate family at gain `g` gives
  the clause for the final family at gain `(C⁵ / (c₁ c₂))⁻¹ · g`.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

/-! ### T2: the coarsest-scale bracket for a shaded-uniform family -/

namespace ShadedTube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] in
/-- A tube of the coarsest grid radius `ρ_0 = Tube.gridScale δ N 0 = 1` whose carrier contains
the closed unit ball: `Tube.ofMidpointDirection` at midpoint `0`. -/
theorem exists_tube_gridScale_zero_closedBall_subset (δ : ℝ≥0) (N : ℕ) :
    ∃ V : Tube (Tube.gridScale δ N 0) E, closedBall (0 : E) 1 ⊆ V.carrier := by
  rcases exists_ne (0 : E) with ⟨v, hv⟩
  let u : E := (‖v‖)⁻¹ • v
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
    exact inv_mul_cancel₀ (ne_of_gt (norm_pos_iff.mpr hv))
  let V : Tube (Tube.gridScale δ N 0) E :=
    Tube.ofMidpointDirection (Tube.gridScale δ N 0) 0 u hu
  have hx : V.x = -((1 / 2 : ℝ) • u) := by simp [V, Tube.ofMidpointDirection]
  have hy : V.y = (1 / 2 : ℝ) • u := by simp [V, Tube.ofMidpointDirection]
  have h0 : (0 : E) ∈ segment ℝ V.x V.y := by
    rw [hx, hy]
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    module
  refine ⟨V, ?_⟩
  rw [V.carrier_eq]
  refine Set.subset_iUnion₂_of_subset (0 : E) h0 ?_
  rw [Tube.gridScale_zero]
  simp

omit [BorelSpace E] in
open scoped Classical in
/-- **At the coarsest grid index the fibre of any point meets at most `C` nodes.** Every node
met by the fibre of `x` shares a member with the unit tube of
`exists_tube_gridScale_zero_closedBall_subset` (all carriers lie in the unit ball), so
`Tube.UniformTubeSet.boundedOverlap` at `k = 0` bounds their number by `C`. -/
theorem card_nodes_met_zero_le [DecidableEq ι] {δ : ℝ≥0} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : ℝ≥0}
    (𝒰 : Tube.UniformTubeSet s (fun i => (V i).toTube) N C)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ closedBall (0 : E) 1) (x : E) :
    (((s.filter (fun i => x ∈ (V i).shade)).image (𝒰.cover.assign 0)).card : ℝ≥0) ≤ C := by
  obtain ⟨W, hW⟩ := exists_tube_gridScale_zero_closedBall_subset (E := E) δ N
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_))
    (𝒰.boundedOverlap 0 (Nat.zero_le N) W)
  intro j hj
  obtain ⟨i, hiF, rfl⟩ := Finset.mem_image.mp hj
  have hi : i ∈ s := (Finset.mem_filter.mp hiF).1
  refine Finset.mem_filter.mpr ⟨𝒰.cover.assign_mem 0 (Nat.zero_le N) i hi, i, hi,
    𝒰.cover.le_tube_assign 0 (Nat.zero_le N) i hi, ?_⟩
  change ((V i).toTube.toConvexSpaceBody : Set E) ⊆ (W.toConvexSpaceBody : Set E)
  exact (hball i hi).trans hW

omit [BorelSpace E] in
open scoped Classical in
/-- **T2: the two-sided bracket of the pointwise multiplicity at the coarsest grid index**
(GWZ (86), `µ(𝕋, Y) ≈ µ(1)`). For a family carrying `ShadedUniformTubeSet s V N C` in the unit
ball and any point `x` of its shade union,
`branchingN 0 ≤ C² · pm(x)` and `pm(x) ≤ C³ · branchingN 0`.

Lower half: `branchingN_le` then `le_card_shadeClass` on a member of the fibre, whose class lies
in the fibre (`card_shadeClass_le_pointwiseMultiplicity`). Upper half: the fibre is the disjoint
union of its classes over the nodes it meets (`card_fibre_eq_sum_card_shadeClass`), each class is
`≤ C · localN ≤ C² · branchingN 0` (`card_shadeClass_le`, `le_branchingN`), and the fibre meets at
most `C` nodes (`card_nodes_met_zero_le`). The powers are the ones the structure's fields afford:
two `C`s per side for the class/branching brackets, one for the node count. -/
theorem ShadedUniformTubeSet.pointwiseMultiplicity_bracket_zero {δ : ℝ≥0} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : ℝ≥0} (𝒱 : ShadedUniformTubeSet s V N C)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ closedBall (0 : E) 1) {x : E}
    (hx : x ∈ ⋃ i ∈ s, (V i).shade) :
    𝒱.branchingN 0 ≤
        C ^ 2 * (ShadedBody.pointwiseMultiplicity s (fun i => (V i).toShadedBody) x : ℝ≥0) ∧
      (ShadedBody.pointwiseMultiplicity s (fun i => (V i).toShadedBody) x : ℝ≥0) ≤
        C ^ 3 * 𝒱.branchingN 0 := by
  set assign : ι → ι := 𝒱.tubeUniform.cover.assign 0 with hassign
  set F : Finset ι := s.filter (fun i => x ∈ (V i).shade) with hF
  have hpm : ShadedBody.pointwiseMultiplicity s (fun i => (V i).toShadedBody) x = F.card := by
    simp [ShadedBody.pointwiseMultiplicity, hF]
  obtain ⟨i₀, hi₀, hxi₀⟩ := Set.mem_iUnion₂.mp hx
  constructor
  · have h1 := 𝒱.branchingN_le x hx 0 (Nat.zero_le N)
    have h2 := 𝒱.le_card_shadeClass x hx 0 (Nat.zero_le N) i₀ hi₀ hxi₀
    have h3 : ((shadeClass s V assign (assign i₀) x).card : ℝ≥0) ≤
        (ShadedBody.pointwiseMultiplicity s (fun i => (V i).toShadedBody) x : ℝ≥0) := by
      exact_mod_cast card_shadeClass_le_pointwiseMultiplicity s V assign (assign i₀) x
    calc 𝒱.branchingN 0 ≤ C * 𝒱.localN x 0 := h1
      _ ≤ C * (C * ((shadeClass s V assign (assign i₀) x).card : ℝ≥0)) := by gcongr
      _ ≤ C * (C * (ShadedBody.pointwiseMultiplicity s (fun i => (V i).toShadedBody) x : ℝ≥0)) := by
          gcongr
      _ = C ^ 2 * (ShadedBody.pointwiseMultiplicity s (fun i => (V i).toShadedBody) x : ℝ≥0) := by
          ring
  · have hnodes := card_nodes_met_zero_le 𝒱.tubeUniform hball x
    have hterm : ∀ j ∈ F.image assign,
        ((shadeClass s V assign j x).card : ℝ≥0) ≤ C ^ 2 * 𝒱.branchingN 0 := by
      intro j hj
      obtain ⟨i, hiF, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hi, hxi⟩ := Finset.mem_filter.mp hiF
      calc ((shadeClass s V assign (assign i) x).card : ℝ≥0) ≤ C * 𝒱.localN x 0 :=
            𝒱.card_shadeClass_le x hx 0 (Nat.zero_le N) i hi hxi
        _ ≤ C * (C * 𝒱.branchingN 0) := by
            gcongr
            exact 𝒱.le_branchingN x hx 0 (Nat.zero_le N)
        _ = C ^ 2 * 𝒱.branchingN 0 := by ring
    calc (ShadedBody.pointwiseMultiplicity s (fun i => (V i).toShadedBody) x : ℝ≥0)
        = ((F.card : ℕ) : ℝ≥0) := by rw [hpm]
      _ = ((∑ j ∈ F.image assign, (shadeClass s V assign j x).card : ℕ) : ℝ≥0) := by
          rw [card_fibre_eq_sum_card_shadeClass (V := V) assign x]
      _ = ∑ j ∈ F.image assign, ((shadeClass s V assign j x).card : ℝ≥0) := by push_cast; rfl
      _ ≤ ∑ _j ∈ F.image assign, C ^ 2 * 𝒱.branchingN 0 := Finset.sum_le_sum hterm
      _ = ((F.image assign).card : ℝ≥0) * (C ^ 2 * 𝒱.branchingN 0) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ C * (C ^ 2 * 𝒱.branchingN 0) := mul_le_mul_left hnodes _
      _ = C ^ 3 * 𝒱.branchingN 0 := by ring

omit [Nontrivial E] [BorelSpace E] in
/-- The coarsest branching number of a shaded-uniform family is positive as soon as its shade
union is nonempty: a member of the fibre lies in its own class, so `1 ≤ C · localN ≤ C² ·
branchingN 0`. -/
theorem ShadedUniformTubeSet.branchingN_zero_pos {δ : ℝ≥0} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : ℝ≥0} (𝒱 : ShadedUniformTubeSet s V N C)
    (hne : (⋃ i ∈ s, (V i).shade).Nonempty) : 0 < 𝒱.branchingN 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  set assign : ι → ι := 𝒱.tubeUniform.cover.assign 0 with hassign
  have h1 : (1 : ℝ≥0) ≤ ((shadeClass s V assign (assign i) x).card : ℝ≥0) :=
    one_le_card_shadeClass_self assign hi hxi
  have h2 := 𝒱.card_shadeClass_le x hx 0 (Nat.zero_le N) i hi hxi
  have h3 := 𝒱.le_branchingN x hx 0 (Nat.zero_le N)
  have h : (1 : ℝ≥0) ≤ C * (C * 𝒱.branchingN 0) :=
    h1.trans (h2.trans (mul_le_mul_right h3 C))
  rw [pos_iff_ne_zero]
  intro hb
  rw [hb, mul_zero, mul_zero] at h
  exact absurd h (by norm_num)

end ShadedTube

namespace Kakeya.VeryNotSticky

open ShadedBody Produce

/-! ### Monotonicity of the shade union and of the fibre under refinement -/

/-- An index selection with the shades cut shrinks the shade union. -/
theorem biUnion_shade_mono {ι : Type*} {δ : ℝ≥0} {s s' : Finset ι} {T T' : ι → ShadedTube δ E3}
    (hs : s' ⊆ s) (hsh : ∀ i ∈ s', (T' i).shade ⊆ (T i).shade) :
    (⋃ i ∈ s', (T' i).toShadedBody.shade) ⊆ ⋃ i ∈ s, (T i).toShadedBody.shade :=
  Set.iUnion₂_subset fun i hi =>
    (hsh i hi).trans (Set.subset_iUnion₂_of_subset i (hs hi) subset_rfl)

/-- **Fibre monotonicity `pm* ≤ pm₀`**: the pointwise multiplicity is monotone under an index
selection with the shades cut. -/
theorem pointwiseMultiplicity_mono {ι : Type*} {δ : ℝ≥0} {s₀ s₁ : Finset ι}
    {T₀ T₁ : ι → ShadedTube δ E3} (hs : s₁ ⊆ s₀)
    (hsh : ∀ i ∈ s₁, (T₁ i).shade ⊆ (T₀ i).shade) (x : E3) :
    pointwiseMultiplicity s₁ (fun i => (T₁ i).toShadedBody) x ≤
      pointwiseMultiplicity s₀ (fun i => (T₀ i).toShadedBody) x := by
  classical
  unfold pointwiseMultiplicity
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hs hi.1, hsh i hi.1 hi.2⟩

/-! ### T1: the clause relative to a frozen volume -/

/-- **The clause of `LocalMassAt` at one index, with the right-hand side frozen at a volume
`Vol`.** `Kakeya.VeryNotSticky.LocalMassClauseAt δ N k g s T` is this at `Vol = |U|`,
`U = ⋃_{i ∈ s} Y(T_i)`. In the chain every bridge clause is stored relative to `|U₀|`, the shade
union of the *first* family. -/
def LocalMassClauseRel {ι : Type*} (δ : ℝ≥0) (N k : ℕ) (g : ℝ≥0∞) (s : Finset ι)
    (T : ι → ShadedTube δ E3) (Vol : ℝ≥0∞) : Prop :=
  ∀ x : E3,
    g * (volume (cthickening (2 * (Tube.gridScale δ N k : ℝ))
          (⋃ i ∈ s, (T i).toShadedBody.shade)) *
        (volume ((⋃ i ∈ s, (T i).toShadedBody.shade) ∩ ball x (Tube.gridScale δ N k : ℝ)) /
          volume (ball x (Tube.gridScale δ N k : ℝ)))) ≤ Vol

/-- A clause is a relative clause at any `Vol ≥ |U|`. -/
theorem LocalMassClauseAt.toRel {ι : Type*} {δ : ℝ≥0} {N k : ℕ} {g : ℝ≥0∞} {s : Finset ι}
    {T : ι → ShadedTube δ E3} (h : LocalMassClauseAt δ N k g s T) {Vol : ℝ≥0∞}
    (hV : volume (⋃ i ∈ s, (T i).toShadedBody.shade) ≤ Vol) :
    LocalMassClauseRel δ N k g s T Vol :=
  fun x => (h x).trans hV

/-- The relative clause is monotone in the gain. -/
theorem LocalMassClauseRel.mono_gain {ι : Type*} {δ : ℝ≥0} {N k : ℕ} {g g' : ℝ≥0∞}
    {s : Finset ι} {T : ι → ShadedTube δ E3} {Vol : ℝ≥0∞} (hg : g' ≤ g)
    (h : LocalMassClauseRel δ N k g s T Vol) : LocalMassClauseRel δ N k g' s T Vol :=
  fun x => le_trans (mul_le_mul_left hg _) (h x)

/-- The relative clause is monotone in the frozen volume. -/
theorem LocalMassClauseRel.mono_vol {ι : Type*} {δ : ℝ≥0} {N k : ℕ} {g : ℝ≥0∞}
    {s : Finset ι} {T : ι → ShadedTube δ E3} {Vol Vol' : ℝ≥0∞} (hV : Vol ≤ Vol')
    (h : LocalMassClauseRel δ N k g s T Vol) : LocalMassClauseRel δ N k g s T Vol' :=
  fun x => (h x).trans hV

/-- **T1, the transport: the clause is monotone on the left in the shade union.** A relative
clause for `(s, T)` is a relative clause, at the same gain and the same frozen volume, for every
`(s', T')` whose shade union is contained in that of `(s, T)`: `N_{2ρ}(U') ⊆ N_{2ρ}(U)` and
`U' ∩ B ⊆ U ∩ B`. -/
theorem LocalMassClauseRel.mono_union {ι : Type*} {δ : ℝ≥0} {N k : ℕ} {g : ℝ≥0∞}
    {s s' : Finset ι} {T T' : ι → ShadedTube δ E3} {Vol : ℝ≥0∞}
    (h : LocalMassClauseRel δ N k g s T Vol)
    (hU : (⋃ i ∈ s', (T' i).toShadedBody.shade) ⊆ ⋃ i ∈ s, (T i).toShadedBody.shade) :
    LocalMassClauseRel δ N k g s' T' Vol := by
  intro x
  refine le_trans ?_ (h x)
  gcongr
  exact cthickening_subset_of_subset _ hU

/-- **Back from the frozen volume to the clause, at the price of the volume comparison.** If
`Vol ≤ Λ · |U|` then a relative clause at gain `g` is a clause at gain `Λ⁻¹ · g`. No positivity
of `Λ` is needed: at `Λ = 0` the hypothesis forces `Vol = 0`, hence every left-hand side is `0`. -/
theorem LocalMassClauseRel.toClauseAt {ι : Type*} {δ : ℝ≥0} {N k : ℕ} {g : ℝ≥0∞}
    {s : Finset ι} {T : ι → ShadedTube δ E3} {Vol : ℝ≥0∞}
    (h : LocalMassClauseRel δ N k g s T Vol) {Λ : ℝ≥0}
    (hvol : Vol ≤ (Λ : ℝ≥0∞) * volume (⋃ i ∈ s, (T i).toShadedBody.shade)) :
    LocalMassClauseAt δ N k ((Λ : ℝ≥0∞)⁻¹ * g) s T := by
  intro x
  rw [mul_assoc]
  rcases eq_or_ne Λ 0 with hΛ | hΛ
  · subst hΛ
    have h0 : Vol = 0 := by simpa using hvol
    rw [le_antisymm ((h x).trans h0.le) zero_le, mul_zero]
    exact zero_le
  · have hΛ0 : (Λ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hΛ
    calc (Λ : ℝ≥0∞)⁻¹ * (g * (volume (cthickening (2 * (Tube.gridScale δ N k : ℝ))
            (⋃ i ∈ s, (T i).toShadedBody.shade)) *
          (volume ((⋃ i ∈ s, (T i).toShadedBody.shade) ∩ ball x (Tube.gridScale δ N k : ℝ)) /
            volume (ball x (Tube.gridScale δ N k : ℝ)))))
        ≤ (Λ : ℝ≥0∞)⁻¹ * Vol := mul_le_mul_right (h x) _
      _ ≤ (Λ : ℝ≥0∞)⁻¹ * ((Λ : ℝ≥0∞) * volume (⋃ i ∈ s, (T i).toShadedBody.shade)) :=
          mul_le_mul_right hvol _
      _ = volume (⋃ i ∈ s, (T i).toShadedBody.shade) :=
          ENNReal.inv_mul_cancel_left hΛ0 ENNReal.coe_ne_top

/-- **T1 in one piece**: the clause for `(s, T)` at gain `g` gives the clause for any `(s', T')`
with `U' ⊆ U` at gain `Λ⁻¹ · g`, provided `|U| ≤ Λ · |U'|`. -/
theorem LocalMassClauseAt.transport {ι : Type*} {δ : ℝ≥0} {N k : ℕ} {g : ℝ≥0∞}
    {s s' : Finset ι} {T T' : ι → ShadedTube δ E3} (h : LocalMassClauseAt δ N k g s T)
    (hU : (⋃ i ∈ s', (T' i).toShadedBody.shade) ⊆ ⋃ i ∈ s, (T i).toShadedBody.shade) {Λ : ℝ≥0}
    (hvol : volume (⋃ i ∈ s, (T i).toShadedBody.shade) ≤
      (Λ : ℝ≥0∞) * volume (⋃ i ∈ s', (T' i).toShadedBody.shade)) :
    LocalMassClauseAt δ N k ((Λ : ℝ≥0∞)⁻¹ * g) s' T' :=
  ((h.toRel le_rfl).mono_union hU).toClauseAt hvol

/-! ### T3: the volume comparison `|U₀| ≤ (C⁵ / c) · |U₁|` -/

/-- **T3, division-free form.** For the first family `(s₀, T₀)`, carrying
`ShadedTube.ShadedUniformTubeSet s₀ T₀ N C` in the unit ball, and a refinement `(s₁, T₁)`
(index subset, shades cut) retaining a `c`-fraction of the total shading mass,
`c · |U₀| ≤ C⁵ · |U₁|`.

Layer cake on both unions; `b := branchingN 0` satisfies `b · |U₀| ≤ ∫_{U₀} C² pm₀ = C² ∑_{s₀}|Y₀|`
(lower bracket), `∑_{s₁}|Y₁| = ∫_{U₁} pm₁ ≤ ∫_{U₁} C³ b` (fibre monotonicity and the upper bracket
on `U₁ ⊆ U₀`), and the retention closes the chain `c b |U₀| ≤ C² c ∑|Y₀| ≤ C² ∑|Y₁| ≤ C⁵ b |U₁|`;
`b > 0` when `U₀ ≠ ∅` cancels. The uniformity of `(s₁, T₁)` is not used. -/
theorem volume_biUnion_shade_mul_le_of_shadedUniform_of_retention {ι : Type*} {δ : ℝ≥0}
    {s₀ s₁ : Finset ι} {T₀ T₁ : ι → ShadedTube δ E3} {N : ℕ} {C : ℝ≥0}
    (𝒱 : ShadedTube.ShadedUniformTubeSet s₀ T₀ N C)
    (hball : ∀ i ∈ s₀, (T₀ i).carrier ⊆ closedBall (0 : E3) 1)
    (hs : s₁ ⊆ s₀) (hsh : ∀ i ∈ s₁, (T₁ i).shade ⊆ (T₀ i).shade) (c : ℝ≥0)
    (hret : (c : ℝ≥0∞) * ∑ i ∈ s₀, volume (T₀ i).toShadedBody.shade ≤
      ∑ i ∈ s₁, volume (T₁ i).toShadedBody.shade) :
    (c : ℝ≥0∞) * volume (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade) ≤
      (C : ℝ≥0∞) ^ 5 * volume (⋃ i ∈ s₁, (T₁ i).toShadedBody.shade) := by
  classical
  have hU₁₀ : (⋃ i ∈ s₁, (T₁ i).toShadedBody.shade) ⊆ ⋃ i ∈ s₀, (T₀ i).toShadedBody.shade :=
    biUnion_shade_mono hs hsh
  rcases (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade).eq_empty_or_nonempty with hUe | hUne
  · rw [hUe, measure_empty, mul_zero]
    exact zero_le
  have hb : 0 < 𝒱.branchingN 0 := 𝒱.branchingN_zero_pos hUne
  have hU₀m : MeasurableSet (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade) :=
    Finset.measurableSet_biUnion s₀ fun i _ => (T₀ i).toShadedBody.measurableSet_shade
  have hU₁m : MeasurableSet (⋃ i ∈ s₁, (T₁ i).toShadedBody.shade) :=
    Finset.measurableSet_biUnion s₁ fun i _ => (T₁ i).toShadedBody.measurableSet_shade
  -- layer cake on both unions
  have hlc₀ : ∑ i ∈ s₀, volume (T₀ i).toShadedBody.shade =
      ∫⁻ x in (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade),
        (pointwiseMultiplicity s₀ (fun i => (T₀ i).toShadedBody) x : ℝ≥0∞) := by
    rw [← Plank.sum_volume_shade_inter_eq_lintegral_multiplicity]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hsub : (T₀ i).toShadedBody.shade ⊆ ⋃ i ∈ s₀, (T₀ i).toShadedBody.shade :=
      Set.subset_iUnion₂_of_subset i hi subset_rfl
    rw [Set.inter_eq_left.mpr hsub]
  have hlc₁ : ∑ i ∈ s₁, volume (T₁ i).toShadedBody.shade =
      ∫⁻ x in (⋃ i ∈ s₁, (T₁ i).toShadedBody.shade),
        (pointwiseMultiplicity s₁ (fun i => (T₁ i).toShadedBody) x : ℝ≥0∞) := by
    rw [← Plank.sum_volume_shade_inter_eq_lintegral_multiplicity]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hsub : (T₁ i).toShadedBody.shade ⊆ ⋃ i ∈ s₁, (T₁ i).toShadedBody.shade :=
      Set.subset_iUnion₂_of_subset i hi subset_rfl
    rw [Set.inter_eq_left.mpr hsub]
  -- the lower bracket integrated over `U₀`
  have hA : (𝒱.branchingN 0 : ℝ≥0∞) * volume (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade) ≤
      (C : ℝ≥0∞) ^ 2 * ∑ i ∈ s₀, volume (T₀ i).toShadedBody.shade := by
    calc (𝒱.branchingN 0 : ℝ≥0∞) * volume (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade)
        = ∫⁻ _ in (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade), (𝒱.branchingN 0 : ℝ≥0∞) :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade),
            (C : ℝ≥0∞) ^ 2 *
              (pointwiseMultiplicity s₀ (fun i => (T₀ i).toShadedBody) x : ℝ≥0∞) := by
          refine setLIntegral_mono' hU₀m fun x hx => ?_
          have h := (𝒱.pointwiseMultiplicity_bracket_zero hball hx).1
          have h' : ((𝒱.branchingN 0 : ℝ≥0) : ℝ≥0∞) ≤
              ((C ^ 2 * (pointwiseMultiplicity s₀ (fun i => (T₀ i).toShadedBody) x : ℝ≥0) :
                ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr h
          simpa [ENNReal.coe_mul, ENNReal.coe_pow] using h'
      _ = (C : ℝ≥0∞) ^ 2 * ∫⁻ x in (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade),
            (pointwiseMultiplicity s₀ (fun i => (T₀ i).toShadedBody) x : ℝ≥0∞) :=
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      _ = (C : ℝ≥0∞) ^ 2 * ∑ i ∈ s₀, volume (T₀ i).toShadedBody.shade := by rw [hlc₀]
  -- fibre monotonicity and the upper bracket integrated over `U₁`
  have hC : ∑ i ∈ s₁, volume (T₁ i).toShadedBody.shade ≤
      (C : ℝ≥0∞) ^ 3 * (𝒱.branchingN 0 : ℝ≥0∞) *
        volume (⋃ i ∈ s₁, (T₁ i).toShadedBody.shade) := by
    calc ∑ i ∈ s₁, volume (T₁ i).toShadedBody.shade
        = ∫⁻ x in (⋃ i ∈ s₁, (T₁ i).toShadedBody.shade),
            (pointwiseMultiplicity s₁ (fun i => (T₁ i).toShadedBody) x : ℝ≥0∞) := hlc₁
      _ ≤ ∫⁻ _ in (⋃ i ∈ s₁, (T₁ i).toShadedBody.shade),
            ((C : ℝ≥0∞) ^ 3 * (𝒱.branchingN 0 : ℝ≥0∞)) := by
          refine setLIntegral_mono' hU₁m fun x hx => ?_
          have h1 := pointwiseMultiplicity_mono hs hsh x
          have h2 := (𝒱.pointwiseMultiplicity_bracket_zero hball (hU₁₀ hx)).2
          have h2' : ((pointwiseMultiplicity s₀ (fun i => (T₀ i).toShadedBody) x : ℝ≥0) : ℝ≥0∞)
              ≤ ((C ^ 3 * 𝒱.branchingN 0 : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr h2
          calc (pointwiseMultiplicity s₁ (fun i => (T₁ i).toShadedBody) x : ℝ≥0∞)
              ≤ (pointwiseMultiplicity s₀ (fun i => (T₀ i).toShadedBody) x : ℝ≥0∞) := by
                exact_mod_cast h1
            _ ≤ (C : ℝ≥0∞) ^ 3 * (𝒱.branchingN 0 : ℝ≥0∞) := by
                simpa [ENNReal.coe_mul, ENNReal.coe_pow] using h2'
      _ = (C : ℝ≥0∞) ^ 3 * (𝒱.branchingN 0 : ℝ≥0∞) *
            volume (⋃ i ∈ s₁, (T₁ i).toShadedBody.shade) := setLIntegral_const _ _
  -- chain, then cancel the branching number
  have hchain : (𝒱.branchingN 0 : ℝ≥0∞) *
      ((c : ℝ≥0∞) * volume (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade)) ≤
      (𝒱.branchingN 0 : ℝ≥0∞) *
        ((C : ℝ≥0∞) ^ 5 * volume (⋃ i ∈ s₁, (T₁ i).toShadedBody.shade)) := by
    calc (𝒱.branchingN 0 : ℝ≥0∞) * ((c : ℝ≥0∞) * volume (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade))
        = (c : ℝ≥0∞) * ((𝒱.branchingN 0 : ℝ≥0∞) *
            volume (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade)) := by ring
      _ ≤ (c : ℝ≥0∞) * ((C : ℝ≥0∞) ^ 2 * ∑ i ∈ s₀, volume (T₀ i).toShadedBody.shade) := by
          gcongr
      _ = (C : ℝ≥0∞) ^ 2 * ((c : ℝ≥0∞) * ∑ i ∈ s₀, volume (T₀ i).toShadedBody.shade) := by ring
      _ ≤ (C : ℝ≥0∞) ^ 2 * ∑ i ∈ s₁, volume (T₁ i).toShadedBody.shade := by gcongr
      _ ≤ (C : ℝ≥0∞) ^ 2 * ((C : ℝ≥0∞) ^ 3 * (𝒱.branchingN 0 : ℝ≥0∞) *
            volume (⋃ i ∈ s₁, (T₁ i).toShadedBody.shade)) := by gcongr
      _ = (𝒱.branchingN 0 : ℝ≥0∞) *
            ((C : ℝ≥0∞) ^ 5 * volume (⋃ i ∈ s₁, (T₁ i).toShadedBody.shade)) := by ring
  exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast hb.ne') ENNReal.coe_ne_top).mp hchain

/-- **T3: the volume comparison `|U₀| ≤ (C⁵ / c) · |U₁|`** between the first (uniformised)
family and any later refinement retaining a `c`-fraction of the shading mass, `0 < c`. The
constant is `C⁵ / c` with `C` the first family's Definition-2.2 constant — δ-free for
`C = ShadedTube.ssfUniformConst 3` — and `c` the total retention; no constant of the later
family enters. -/
theorem volume_biUnion_shade_le_of_shadedUniform_of_retention {ι : Type*} {δ : ℝ≥0}
    {s₀ s₁ : Finset ι} {T₀ T₁ : ι → ShadedTube δ E3} {N : ℕ} {C : ℝ≥0}
    (𝒱 : ShadedTube.ShadedUniformTubeSet s₀ T₀ N C)
    (hball : ∀ i ∈ s₀, (T₀ i).carrier ⊆ closedBall (0 : E3) 1)
    (hs : s₁ ⊆ s₀) (hsh : ∀ i ∈ s₁, (T₁ i).shade ⊆ (T₀ i).shade) {c : ℝ≥0} (hc : 0 < c)
    (hret : (c : ℝ≥0∞) * ∑ i ∈ s₀, volume (T₀ i).toShadedBody.shade ≤
      ∑ i ∈ s₁, volume (T₁ i).toShadedBody.shade) :
    volume (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade) ≤
      ((C ^ 5 / c : ℝ≥0) : ℝ≥0∞) * volume (⋃ i ∈ s₁, (T₁ i).toShadedBody.shade) := by
  have h := volume_biUnion_shade_mul_le_of_shadedUniform_of_retention 𝒱 hball hs hsh c hret
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  rw [ENNReal.mul_le_iff_le_inv hc0 ENNReal.coe_ne_top] at h
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.coe_div hc.ne', ENNReal.coe_pow, div_eq_mul_inv]
  ring

/-- T3 for a `ShadedBody.IsCRefinement`: the refinement supplies the index subset, the cut
shades and the retention. -/
theorem volume_biUnion_shade_le_of_shadedUniform_of_isCRefinement {ι : Type*} {δ : ℝ≥0}
    {s₀ s₁ : Finset ι} {T₀ T₁ : ι → ShadedTube δ E3} {N : ℕ} {C : ℝ≥0}
    (𝒱 : ShadedTube.ShadedUniformTubeSet s₀ T₀ N C)
    (hball : ∀ i ∈ s₀, (T₀ i).carrier ⊆ closedBall (0 : E3) 1) {c : ℝ≥0} (hc : 0 < c)
    (href : IsCRefinement s₁ (fun i ↦ (T₁ i).toShadedBody) s₀ (fun i ↦ (T₀ i).toShadedBody) c) :
    volume (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade) ≤
      ((C ^ 5 / c : ℝ≥0) : ℝ≥0∞) * volume (⋃ i ∈ s₁, (T₁ i).toShadedBody.shade) :=
  volume_biUnion_shade_le_of_shadedUniform_of_retention 𝒱 hball href.1.1
    (fun i hi => (href.1.2 i hi).2) hc href.2

/-- T3 with the total retention `c₁ · c₂` composed from two refinements by
`ShadedBody.IsCRefinement.trans` — the shape of the chain, first family → intermediate → final. -/
theorem volume_biUnion_shade_le_of_shadedUniform_of_isCRefinement_trans {ι : Type*} {δ : ℝ≥0}
    {s₀ s₁ s₂ : Finset ι} {T₀ T₁ T₂ : ι → ShadedTube δ E3} {N : ℕ} {C : ℝ≥0}
    (𝒱 : ShadedTube.ShadedUniformTubeSet s₀ T₀ N C)
    (hball : ∀ i ∈ s₀, (T₀ i).carrier ⊆ closedBall (0 : E3) 1) {c₁ c₂ : ℝ≥0} (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂)
    (h₁ : IsCRefinement s₁ (fun i ↦ (T₁ i).toShadedBody) s₀ (fun i ↦ (T₀ i).toShadedBody) c₁)
    (h₂ : IsCRefinement s₂ (fun i ↦ (T₂ i).toShadedBody) s₁ (fun i ↦ (T₁ i).toShadedBody) c₂) :
    volume (⋃ i ∈ s₀, (T₀ i).toShadedBody.shade) ≤
      ((C ^ 5 / (c₁ * c₂) : ℝ≥0) : ℝ≥0∞) * volume (⋃ i ∈ s₂, (T₂ i).toShadedBody.shade) :=
  volume_biUnion_shade_le_of_shadedUniform_of_isCRefinement 𝒱 hball (mul_pos hc₁ hc₂)
    (h₂.trans h₁)

/-! ### The transport in the shape the chain uses -/

/-- **T1 + T3.** The clause at index `k` at gain `g`, established for an intermediate family
`(s₁, T₁)` with `U₁ ⊆ U₀`, transports to any later family `(s₂, T₂)` with `U₂ ⊆ U₁` which is a
`c`-refinement of the *first* family `(s₀, T₀)`, at gain `(C⁵ / c)⁻¹ · g`, `C` the first family's
uniformity constant. Nothing about `(s₁, T₁)` or `(s₂, T₂)` beyond the inclusions and the
retention is consumed: no re-uniformisation between bridge steps. -/
theorem LocalMassClauseAt.transport_of_shadedUniform {ι : Type*} {δ : ℝ≥0} {N k : ℕ}
    {g : ℝ≥0∞} {C : ℝ≥0} {s₀ s₁ s₂ : Finset ι} {T₀ T₁ T₂ : ι → ShadedTube δ E3}
    (𝒱 : ShadedTube.ShadedUniformTubeSet s₀ T₀ N C)
    (hball : ∀ i ∈ s₀, (T₀ i).carrier ⊆ closedBall (0 : E3) 1)
    (h : LocalMassClauseAt δ N k g s₁ T₁)
    (hU₁ : (⋃ i ∈ s₁, (T₁ i).toShadedBody.shade) ⊆ ⋃ i ∈ s₀, (T₀ i).toShadedBody.shade)
    (hU₂ : (⋃ i ∈ s₂, (T₂ i).toShadedBody.shade) ⊆ ⋃ i ∈ s₁, (T₁ i).toShadedBody.shade)
    {c : ℝ≥0} (hc : 0 < c)
    (href : IsCRefinement s₂ (fun i ↦ (T₂ i).toShadedBody) s₀ (fun i ↦ (T₀ i).toShadedBody) c) :
    LocalMassClauseAt δ N k (((C ^ 5 / c : ℝ≥0) : ℝ≥0∞)⁻¹ * g) s₂ T₂ :=
  ((h.toRel (measure_mono hU₁)).mono_union hU₂).toClauseAt
    (volume_biUnion_shade_le_of_shadedUniform_of_isCRefinement 𝒱 hball hc href)

/-- **The transport through two refinements**: `(s₁, T₁)` a `c₁`-refinement of the first family
`(s₀, T₀)` and `(s₂, T₂)` a `c₂`-refinement of `(s₁, T₁)`; the inclusions are read off the
refinements and the total retention is `c₁ · c₂` (`ShadedBody.IsCRefinement.trans`). The clause
at gain `g` for `(s₁, T₁)` gives the clause at gain `(C⁵ / (c₁ c₂))⁻¹ · g` for `(s₂, T₂)`. -/
theorem LocalMassClauseAt.transport_of_isCRefinement {ι : Type*} {δ : ℝ≥0} {N k : ℕ}
    {g : ℝ≥0∞} {C : ℝ≥0} {s₀ s₁ s₂ : Finset ι} {T₀ T₁ T₂ : ι → ShadedTube δ E3}
    (𝒱 : ShadedTube.ShadedUniformTubeSet s₀ T₀ N C)
    (hball : ∀ i ∈ s₀, (T₀ i).carrier ⊆ closedBall (0 : E3) 1)
    (h : LocalMassClauseAt δ N k g s₁ T₁) {c₁ c₂ : ℝ≥0} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h₁ : IsCRefinement s₁ (fun i ↦ (T₁ i).toShadedBody) s₀ (fun i ↦ (T₀ i).toShadedBody) c₁)
    (h₂ : IsCRefinement s₂ (fun i ↦ (T₂ i).toShadedBody) s₁ (fun i ↦ (T₁ i).toShadedBody) c₂) :
    LocalMassClauseAt δ N k (((C ^ 5 / (c₁ * c₂) : ℝ≥0) : ℝ≥0∞)⁻¹ * g) s₂ T₂ :=
  h.transport_of_shadedUniform 𝒱 hball
    (biUnion_shade_mono h₁.1.1 fun i hi => (h₁.1.2 i hi).2)
    (biUnion_shade_mono h₂.1.1 fun i hi => (h₂.1.2 i hi).2) (mul_pos hc₁ hc₂) (h₂.trans h₁)

/-- The transported gain, in the exponent bookkeeping's currency: `(C⁵ / c)⁻¹ = c / C⁵`. -/
theorem inv_coe_pow_five_div {C c : ℝ≥0} (hc : c ≠ 0) :
    ((C ^ 5 / c : ℝ≥0) : ℝ≥0∞)⁻¹ = (c : ℝ≥0∞) / (C : ℝ≥0∞) ^ 5 := by
  rw [ENNReal.coe_div hc, ENNReal.coe_pow]
  exact ENNReal.inv_div (Or.inl ENNReal.coe_ne_top) (Or.inl (ENNReal.coe_ne_zero.mpr hc))

end Kakeya.VeryNotSticky
