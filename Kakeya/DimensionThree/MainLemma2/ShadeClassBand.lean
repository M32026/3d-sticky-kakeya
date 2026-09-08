/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.AliveBand
public import Kakeya.DimensionThree.MainLemma1.OneSidedUniform

/-!
# The hereditary shade band, and the node count Definition 2.2 already brackets
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace ShadedTube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- A member of the fibre of `x` lies in its own shade class. -/
theorem mem_shadeClass_self {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E}
    (assign : ι → ι) {i : ι} (hi : i ∈ s) {x : E} (hxi : x ∈ (V i).shade) :
    i ∈ shadeClass s V assign (assign i) x := by
  classical
  simp only [shadeClass, coverClass, Finset.mem_filter]
  exact ⟨⟨hi, trivial⟩, hxi⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- The shade class of a member of the fibre is nonempty. -/
theorem one_le_card_shadeClass_self {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E}
    (assign : ι → ι) {i : ι} (hi : i ∈ s) {x : E} (hxi : x ∈ (V i).shade) :
    (1 : NNReal) ≤ ((shadeClass s V assign (assign i) x).card : NNReal) := by
  have : 1 ≤ (shadeClass s V assign (assign i) x).card :=
    Finset.card_pos.mpr ⟨i, mem_shadeClass_self assign hi hxi⟩
  exact_mod_cast this

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- **Shade-class cardinality is monotone in the index set** — the companion that makes the
`B ≡ 1` band of `nonempty_shadedUniformTubeSet_of_shadeClass_card_le` hereditary: the class
inclusion is `Kakeya.ml1Boot.shadeClass_subset_of_subset`, already in the tree. -/
theorem card_shadeClass_le_of_subset {δ : NNReal} {s s' : Finset ι} (hs' : s' ⊆ s)
    (V : ι → ShadedTube δ E) (assign : ι → ι) (j : ι) (x : E) :
    (shadeClass s' V assign j x).card ≤ (shadeClass s V assign j x).card :=
  Finset.card_le_card (Kakeya.ml1Boot.shadeClass_subset_of_subset hs' V assign j x)

omit [Nontrivial E] [BorelSpace E] in
/-- **Definition 2.2 from a one-sided upper bound on the shade classes.** -/
theorem nonempty_shadedUniformTubeSet_of_shadeClass_card_le {δ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {Cu A C : NNReal}
    (𝒰 : UniformTubeSet s (fun i => (V i).toTube) N Cu)
    (hCuC : Cu ≤ C) (hAC : A ≤ C) (hC1 : 1 ≤ C)
    (hmult : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, ∀ i ∈ s, x ∈ (V i).shade →
      ((shadeClass s V (𝒰.cover.assign k) (𝒰.cover.assign k i) x).card : NNReal) ≤ A) :
    Nonempty (ShadedUniformTubeSet s V N C) := by
  classical
  refine nonempty_shadedUniformTubeSet_of_band 𝒰 hCuC hAC hC1 (fun _ => 1) ?_
  intro x hx k hk i hi hxi
  refine ⟨one_le_card_shadeClass_self _ hi hxi, ?_⟩
  simpa using hmult x hx k hk i hi hxi

/-! ### The node count Definition 2.2 already brackets -/

open scoped Classical in
omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- The fibre of `x` is the disjoint union, over the scale-`k` nodes it meets, of its shade
classes.  Restated as a cardinality identity. -/
theorem card_fibre_eq_sum_card_shadeClass [DecidableEq ι] {δ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E} (assign : ι → ι) (x : E) :
    (s.filter (fun i => x ∈ (V i).shade)).card
      = ∑ j ∈ (s.filter (fun i => x ∈ (V i).shade)).image assign,
          (shadeClass s V assign j x).card := by
  classical
  rw [Finset.card_eq_sum_card_image assign (s.filter (fun i => x ∈ (V i).shade))]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ext i
  simp only [shadeClass, coverClass, Finset.mem_filter]
  tauto

open scoped Classical in
omit [Nontrivial E] [BorelSpace E] in
/-- **The number of scale-`k` nodes the fibre of `x` meets is bracketed by Definition 2.2
itself.**

At a point `x` of the shade union the fibre partitions into the shade classes of the nodes it
meets, and each of those classes has at least `C⁻²·branchingN k` members — `le_card_shadeClass`
composed with `branchingN_le`.  Summing over the nodes met gives the multiplicative form below;
`card_nodes_met_le_of_shadedUniform` is the same statement divided through.

This is the factor that the passage from a global-fibre density to a per-node class density
costs, and the point of the lemma is that it is *readable off the bundle* rather than an
unknown: it is `C² · pointwiseMultiplicity x / branchingN k`. -/
theorem card_nodes_met_mul_branchingN_le [DecidableEq ι] {δ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal}
    (𝒱 : ShadedUniformTubeSet s V N C) {x : E} (hx : x ∈ ⋃ i ∈ s, (V i).shade)
    {k : ℕ} (hk : k ≤ N) :
    (((s.filter (fun i => x ∈ (V i).shade)).image
        (𝒱.tubeUniform.cover.assign k)).card : NNReal) * 𝒱.branchingN k
      ≤ C ^ 2 * (ShadedBody.pointwiseMultiplicity s (fun i => (V i).toShadedBody) x : NNReal) := by
  classical
  set assign : ι → ι := 𝒱.tubeUniform.cover.assign k with hassigndef
  set F : Finset ι := s.filter (fun i => x ∈ (V i).shade) with hFdef
  set I : Finset ι := F.image assign with hIdef
  have hlow : ∀ j ∈ I, 𝒱.branchingN k ≤ C ^ 2 * ((shadeClass s V assign j x).card : NNReal) := by
    intro j hj
    obtain ⟨i, hiF, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hi, hxi⟩ := Finset.mem_filter.mp hiF
    calc 𝒱.branchingN k ≤ C * 𝒱.localN x k := 𝒱.branchingN_le x hx k hk
      _ ≤ C * (C * ((shadeClass s V assign (assign i) x).card : NNReal)) :=
          mul_le_mul_right (𝒱.le_card_shadeClass x hx k hk i hi hxi) C
      _ = C ^ 2 * ((shadeClass s V assign (assign i) x).card : NNReal) := by ring
  have hpm : (ShadedBody.pointwiseMultiplicity s (fun i => (V i).toShadedBody) x) = F.card := by
    simp [ShadedBody.pointwiseMultiplicity, hFdef]
  calc ((I.card : ℕ) : NNReal) * 𝒱.branchingN k
      = ∑ _j ∈ I, 𝒱.branchingN k := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ I, C ^ 2 * ((shadeClass s V assign j x).card : NNReal) := Finset.sum_le_sum hlow
    _ = C ^ 2 * ∑ j ∈ I, ((shadeClass s V assign j x).card : NNReal) := by rw [Finset.mul_sum]
    _ = C ^ 2 * ((F.card : ℕ) : NNReal) := by
        rw [card_fibre_eq_sum_card_shadeClass (V := V) assign x]
        push_cast
        rfl
    _ = C ^ 2 * (ShadedBody.pointwiseMultiplicity s (fun i => (V i).toShadedBody) x : NNReal) := by
        rw [hpm]

open scoped Classical in
omit [Nontrivial E] [BorelSpace E] in
/-- **`card_nodes_met_mul_branchingN_le`, divided through.**  The number of scale-`k` nodes met
by the fibre of `x` is at most `C² · pointwiseMultiplicity x / branchingN k`. -/
theorem card_nodes_met_le_of_shadedUniform [DecidableEq ι] {δ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal}
    (𝒱 : ShadedUniformTubeSet s V N C) {x : E} (hx : x ∈ ⋃ i ∈ s, (V i).shade)
    {k : ℕ} (hk : k ≤ N) (hb : 0 < 𝒱.branchingN k) :
    (((s.filter (fun i => x ∈ (V i).shade)).image
        (𝒱.tubeUniform.cover.assign k)).card : NNReal)
      ≤ C ^ 2 * (ShadedBody.pointwiseMultiplicity s (fun i => (V i).toShadedBody) x : NNReal)
          / 𝒱.branchingN k := by
  rw [le_div_iff₀ hb]
  exact card_nodes_met_mul_branchingN_le 𝒱 hx hk

/-! ### What the `B ≡ 1` route costs: it is priced at the multiplicity -/

open scoped Classical in
omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- A shade class is contained in the fibre, so its cardinality is at most the pointwise
multiplicity.  This is the step by which a pointwise-multiplicity cut discharges the band
hypothesis of `nonempty_shadedUniformTubeSet_of_shadeClass_card_le`. -/
theorem card_shadeClass_le_pointwiseMultiplicity {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ E) (assign : ι → ι) (j : ι) (x : E) :
    (shadeClass s V assign j x).card
      ≤ ShadedBody.pointwiseMultiplicity s (fun i => (V i).toShadedBody) x := by
  classical
  refine Finset.card_le_card ?_
  intro i hi
  simp only [shadeClass, coverClass, Finset.mem_filter] at hi
  simpa [ShadedBody.pointwiseMultiplicity, Finset.mem_filter] using ⟨hi.1.1, hi.2⟩

/-! ### The class-density obligation is empty at every scale with small branching -/

omit [Nontrivial E] [BorelSpace E] in
/-- **A shade class that is already smaller than `θ⁻¹` is `θ`-dense in every subfamily that
meets it.**

`ShadedTube.shadedUniformTubeSet_of_classDense_cut` asks, at each scale `k ≤ N` and each member
`i` of the candidate subfamily `s₃` whose shading covers `x`, that `s₃` retain a `θ` share of
the ambient shade class.  The member `i` lies in its own `s₃`-class
(`one_le_card_shadeClass_self`), so the `s₃`-side is at least `1`; and Definition 2.2's two
upper brackets bound the ambient side by `C² · branchingN k`.  Hence the whole obligation is
**vacuous at every scale where `θ · C² · branchingN k ≤ 1`** — no geometry, no pigeonhole, and
no hypothesis on `s₃` beyond `s₃ ⊆ s`.

Together with `card_nodes_met_le_of_shadedUniform`, which bounds the number of scale-`k` nodes a
fibre meets by `C² · pm(x) / branchingN k`, this brackets the class-density obligation from both
ends: it is empty where `branchingN k ≤ (θ C²)⁻¹`, and where `branchingN k` is large the fibre
meets few nodes.  Only the band `(θ C²)⁻¹ < branchingN k` with `branchingN k` small compared to
`pm(x)` carries any content. -/
theorem classDense_of_branchingN_le {δ : NNReal} {s s₃ : Finset ι} (hs₃ : s₃ ⊆ s)
    {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal} (𝒱 : ShadedUniformTubeSet s V N C)
    {θ : NNReal} {k : ℕ} (hk : k ≤ N) (hfine : θ * (C ^ 2 * 𝒱.branchingN k) ≤ 1)
    {i : ι} (hi : i ∈ s₃) {x : E} (hxi : x ∈ (V i).shade) :
    θ * ((shadeClass s V (𝒱.tubeUniform.cover.assign k)
            (𝒱.tubeUniform.cover.assign k i) x).card : NNReal)
      ≤ ((shadeClass s₃ V (𝒱.tubeUniform.cover.assign k)
            (𝒱.tubeUniform.cover.assign k i) x).card : NNReal) := by
  have his : i ∈ s := hs₃ hi
  have hx : x ∈ ⋃ j ∈ s, (V j).shade := Set.mem_iUnion₂.mpr ⟨i, his, hxi⟩
  have hupper : ((shadeClass s V (𝒱.tubeUniform.cover.assign k)
      (𝒱.tubeUniform.cover.assign k i) x).card : NNReal) ≤ C ^ 2 * 𝒱.branchingN k := by
    calc ((shadeClass s V (𝒱.tubeUniform.cover.assign k)
            (𝒱.tubeUniform.cover.assign k i) x).card : NNReal)
        ≤ C * 𝒱.localN x k := 𝒱.card_shadeClass_le x hx k hk i his hxi
      _ ≤ C * (C * 𝒱.branchingN k) := mul_le_mul_right (𝒱.le_branchingN x hx k hk) C
      _ = C ^ 2 * 𝒱.branchingN k := by ring
  calc θ * ((shadeClass s V (𝒱.tubeUniform.cover.assign k)
          (𝒱.tubeUniform.cover.assign k i) x).card : NNReal)
      ≤ θ * (C ^ 2 * 𝒱.branchingN k) := mul_le_mul_right hupper θ
    _ ≤ 1 := hfine
    _ ≤ ((shadeClass s₃ V (𝒱.tubeUniform.cover.assign k)
          (𝒱.tubeUniform.cover.assign k i) x).card : NNReal) :=
        one_le_card_shadeClass_self _ hi hxi

omit [Nontrivial E] [BorelSpace E] in
/-- **`classDenseSet` is everything when the branching numbers are uniformly below
`(θ C²)⁻¹`.**  The `classDenseSet` form of `classDense_of_branchingN_le`, in exactly the shape
`ShadedTube.shadedUniformTubeSet_of_classDense_cut` and
`ShadedTube.measurableSet_classDenseSet` consume. -/
theorem classDenseSet_eq_univ_of_branchingN_le {δ : NNReal} {s s₃ : Finset ι} (hs₃ : s₃ ⊆ s)
    {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal} (𝒱 : ShadedUniformTubeSet s V N C)
    {θ : NNReal} (hfine : ∀ k ≤ N, θ * (C ^ 2 * 𝒱.branchingN k) ≤ 1) :
    classDenseSet s s₃ V 𝒱.tubeUniform.cover.assign N θ = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  intro k hk i hi hxi
  exact classDense_of_branchingN_le hs₃ 𝒱 hk (hfine k hk) hi hxi

/-! ### The alive band, in the shape clause (f) asks for -/

omit [Nontrivial E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- **The band-forcing cut, stated as a retention rather than a loss.**

`ShadedTube.sum_volume_shade_le_sum_interShade_add` prices the cut of
`ShadedTube.exists_shadedUniform_aliveBand` from above — the surviving mass is the whole mass
minus `M · |Wᶜ|`. Clause (f) of `Kakeya.VeryNotSticky.BandUniformRefinement` asks for the
opposite shape, `θ · ∑ |Y(V i)| ≤ ∑_{s₃} |Y(V' i)|`, and that shape is what a producer must
hand over. This is the conversion, and the whole of clause (f) for the alive-band route is the
single scalar hypothesis `hbudget`.

The alive band supplies everything else outright: clause (d) is its per-tube floor
`ρ ≤ volume (interShade V W hW i).shade`, clauses (a) and (b) are `interShade_toTube` and
`interShade_shade_subset`, and clause (c) is its own `ShadedUniformTubeSet` output moved to the
alive set by `Kakeya.ml1Boot.ShadedTube.ShadedUniformTubeSet.restrict_of_shade_eq_empty`. So
this lemma isolates the entire remaining obligation of that route into `hbudget`. -/
theorem sum_volume_shade_ge_of_interShade_budget {δ : NNReal} {s s₃ : Finset ι}
    (V : ι → ShadedTube δ E) (W : Set E) (hW : MeasurableSet W) (hs₃ : s₃ ⊆ s)
    (hdead : ∀ i ∈ s, i ∉ s₃ → (interShade V W hW i).shade = ∅)
    {M θ ρ : ENNReal}
    (hM : ∀ x ∈ Wᶜ,
      (ShadedBody.pointwiseMultiplicity s (fun i => (V i).toShadedBody) x : ENNReal) ≤ M)
    (hvol : volume Wᶜ ≤ (s.card : ENNReal) * ρ)
    (hfin : M * ((s.card : ENNReal) * ρ) ≠ ⊤)
    (hbudget : M * ((s.card : ENNReal) * ρ) + θ * (∑ i ∈ s, volume (V i).shade)
      ≤ ∑ i ∈ s, volume (V i).shade) :
    θ * ∑ i ∈ s, volume (V i).shade
      ≤ ∑ i ∈ s₃, volume (interShade V W hW i).shade := by
  have hloss := sum_volume_shade_le_sum_interShade_add V W hW hs₃ hdead hM
  have hMle : M * volume Wᶜ ≤ M * ((s.card : ENNReal) * ρ) := mul_le_mul_left' hvol M
  have hchain :
      θ * (∑ i ∈ s, volume (V i).shade) + M * ((s.card : ENNReal) * ρ)
        ≤ (∑ i ∈ s₃, volume (interShade V W hW i).shade) + M * ((s.card : ENNReal) * ρ) := by
    calc θ * (∑ i ∈ s, volume (V i).shade) + M * ((s.card : ENNReal) * ρ)
        = M * ((s.card : ENNReal) * ρ) + θ * (∑ i ∈ s, volume (V i).shade) := by
          rw [add_comm]
      _ ≤ ∑ i ∈ s, volume (V i).shade := hbudget
      _ ≤ (∑ i ∈ s₃, volume (interShade V W hW i).shade) + M * volume Wᶜ := hloss
      _ ≤ (∑ i ∈ s₃, volume (interShade V W hW i).shade)
            + M * ((s.card : ENNReal) * ρ) := by gcongr
  exact (ENNReal.add_le_add_iff_right hfin).mp hchain

omit [Nontrivial E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- **The budget of `sum_volume_shade_ge_of_interShade_budget`, read as a cap on the
multiplicity of the deleted region.**

`M · #s · ρ ≤ ∑ᵢ |Y(V i)|` is a *necessary* consequence of the budget, and it is the sharp form
of `AliveBand.lean`'s "`ρ ≲ |U(𝕍, Y)| / #s`": at the per-tube floor `ρ = δ^{2η} v` that clause
(d) forces, and with the aggregate fullness `δ^η · (#s · v) ≤ ∑ᵢ |Y(V i)|` the section's binders
supply, it reads `M ≤ δ^{-η}`.

So the alive-band route to clause (c) is admissible exactly when the pointwise multiplicity of
the family **on the deleted region `Wᶜ`** is sub-polynomially bounded. That is a *different* set
from the one in `multiplicity_le_of_pointwiseMultiplicity_le_of_mass_retention`, which bounds
the multiplicity on the *retained* union and is therefore circular; nothing here forces the two
to coincide, and this one is open. -/
theorem multiplicity_cap_of_interShade_budget {δ : NNReal} {s : Finset ι}
    (V : ι → ShadedTube δ E) {M θ ρ : ENNReal}
    (hbudget : M * ((s.card : ENNReal) * ρ) + θ * (∑ i ∈ s, volume (V i).shade)
      ≤ ∑ i ∈ s, volume (V i).shade) :
    M * ((s.card : ENNReal) * ρ) ≤ ∑ i ∈ s, volume (V i).shade :=
  le_trans le_self_add hbudget

/-! ### (A) settled: the alive band cannot be rescued by a better cut -/

omit [Nontrivial E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- **A member already lighter than the threshold can never be alive.**

The cut only shrinks: `volume (interShade V W hW i).shade ≤ volume (V i).shade`. So a member
that already fails the per-tube floor `ρ` — which at `ρ = δ^{2η} · v` is exactly a member failing
clause (d) of `Kakeya.VeryNotSticky.BandUniformRefinement` in the *original* shading — fails it
after every cut, and the alive band must annihilate it. -/
theorem not_mem_alive_of_volume_shade_lt {δ : NNReal} {s₃ : Finset ι}
    (V : ι → ShadedTube δ E) (W : Set E) (hW : MeasurableSet W) {ρ : ENNReal}
    (hfloor : ∀ i ∈ s₃, ρ ≤ volume (interShade V W hW i).shade)
    {i : ι} (hlt : volume (V i).shade < ρ) : i ∉ s₃ := by
  intro hi
  exact absurd ((hfloor i hi).trans (measure_mono Set.inter_subset_left)) (not_le.mpr hlt)

omit [Nontrivial E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- **…and annihilating it deletes its whole shade from every other member.**

`ShadedTube.interShade` is a **common** cut, so `(V i).shade ∩ W = ∅` is a statement about `W`,
not about `i`: the region `(V i).shade` is removed from the shading of *every* member. This is
the precise mechanism by which the alive band pays the multiplicity. -/
theorem shade_subset_compl_of_volume_shade_lt {δ : NNReal} {s s₃ : Finset ι}
    (V : ι → ShadedTube δ E) (W : Set E) (hW : MeasurableSet W) {ρ : ENNReal}
    (hfloor : ∀ i ∈ s₃, ρ ≤ volume (interShade V W hW i).shade)
    (hdead : ∀ i ∈ s, i ∉ s₃ → (interShade V W hW i).shade = ∅)
    {i : ι} (his : i ∈ s) (hlt : volume (V i).shade < ρ) : (V i).shade ⊆ Wᶜ := by
  have hemp : (V i).shade ∩ W = ∅ :=
    hdead i his (not_mem_alive_of_volume_shade_lt V W hW hfloor hlt)
  intro x hx
  exact fun hxW => absurd (Set.eq_empty_iff_forall_notMem.mp hemp x ⟨hx, hxW⟩) (by simp)

omit [Nontrivial E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- **(A), settled: the alive band's retention ceiling.**

Let `L` be *any* set of members lighter than the floor `ρ`.  Then **every** cut realising the
alive band — not merely the greedy one built by `ShadedTube.exists_cut_aliveBand` — retains at
most the shade mass lying outside `⋃_{j ∈ L} Y(V j)`:

`∑_{i ∈ s₃} |Y(interShade V W hW i)| ≤ ∑_{i ∈ s} |Y(V i) \ ⋃_{j ∈ L} Y(V j)|`.

By `Kakeya.Plank.sum_volume_shade_inter_eq_lintegral_multiplicity` the mass this deletes is
`∫_{⋃_{j ∈ L} Y(V j)} µ(𝕍, Y)`, the pointwise multiplicity integrated over the light members'
region — so the loss is that region's volume **weighted by how many members see it**.

This settles the question the alive-band branch turned on. The obstruction is not the greedy
algorithm's choices and cannot be repaired by a cleverer cut: light members must be annihilated
(`not_mem_alive_of_volume_shade_lt`), the cut is common
(`shade_subset_compl_of_volume_shade_lt`), and therefore their region is lost to everybody. -/
theorem sum_volume_interShade_le_sum_sdiff_light {δ : NNReal} {s s₃ : Finset ι}
    (V : ι → ShadedTube δ E) (W : Set E) (hW : MeasurableSet W) {ρ : ENNReal}
    (hs₃ : s₃ ⊆ s)
    (hfloor : ∀ i ∈ s₃, ρ ≤ volume (interShade V W hW i).shade)
    (hdead : ∀ i ∈ s, i ∉ s₃ → (interShade V W hW i).shade = ∅)
    {L : Finset ι} (hL : L ⊆ s) (hlight : ∀ j ∈ L, volume (V j).shade < ρ) :
    ∑ i ∈ s₃, volume (interShade V W hW i).shade
      ≤ ∑ i ∈ s, volume ((V i).shade \ (⋃ j ∈ L, (V j).shade)) := by
  classical
  have hZW : (⋃ j ∈ L, (V j).shade) ⊆ Wᶜ := by
    refine Set.iUnion₂_subset fun j hj => ?_
    exact shade_subset_compl_of_volume_shade_lt V W hW hfloor hdead (hL hj) (hlight j hj)
  have hstep : ∀ i, (interShade V W hW i).shade
      ⊆ (V i).shade \ (⋃ j ∈ L, (V j).shade) := by
    intro i x hx
    refine ⟨hx.1, fun hxZ => ?_⟩
    exact absurd hx.2 (hZW hxZ)
  calc ∑ i ∈ s₃, volume (interShade V W hW i).shade
      ≤ ∑ i ∈ s, volume (interShade V W hW i).shade :=
        Finset.sum_le_sum_of_subset_of_nonneg hs₃ (fun _ _ _ => bot_le)
    _ ≤ ∑ i ∈ s, volume ((V i).shade \ (⋃ j ∈ L, (V j).shade)) :=
        Finset.sum_le_sum fun i _ => measure_mono (hstep i)

omit [Nontrivial E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- **The price of the alive band, as a necessary condition on the family alone.**

If the alive band retains a `θ` share of the shade mass, then the light members' region carries
at most `1 - θ` of it, *counted with multiplicity*.  The left-hand sum is
`∫_{⋃_{j ∈ L} Y(V j)} µ(𝕍, Y)` by
`Kakeya.Plank.sum_volume_shade_inter_eq_lintegral_multiplicity`.

This is the exact residue of the alive-band branch, and — unlike the greedy cut's deleted region
`Wᶜ` — it refers only to the input family: **the members that already fail clause (d) must not
carry, with multiplicity, more than a `1 - θ` share of the mass.**  A one-line pigeonhole gives
that the light members carry at most `δ^η` of the mass *without* multiplicity, so the whole
question is the multiplicity on their region — which is the same quantity every other route to
clause (c) prices. -/
theorem lintegral_light_add_le_of_retention {δ : NNReal} {s s₃ : Finset ι}
    (V : ι → ShadedTube δ E) (W : Set E) (hW : MeasurableSet W) {ρ θ : ENNReal}
    (hs₃ : s₃ ⊆ s)
    (hfloor : ∀ i ∈ s₃, ρ ≤ volume (interShade V W hW i).shade)
    (hdead : ∀ i ∈ s, i ∉ s₃ → (interShade V W hW i).shade = ∅)
    {L : Finset ι} (hL : L ⊆ s) (hlight : ∀ j ∈ L, volume (V j).shade < ρ)
    (hret : θ * (∑ i ∈ s, volume (V i).shade)
      ≤ ∑ i ∈ s₃, volume (interShade V W hW i).shade) :
    ∑ i ∈ s, volume ((V i).shade ∩ (⋃ j ∈ L, (V j).shade))
        + θ * (∑ i ∈ s, volume (V i).shade)
      ≤ ∑ i ∈ s, volume (V i).shade := by
  classical
  have hZ : MeasurableSet (⋃ j ∈ L, (V j).shade) :=
    Finset.measurableSet_biUnion _ fun j _ => (V j).measurableSet_shade
  have hsplit : ∑ i ∈ s, volume (V i).shade
      = ∑ i ∈ s, volume ((V i).shade ∩ (⋃ j ∈ L, (V j).shade))
        + ∑ i ∈ s, volume ((V i).shade \ (⋃ j ∈ L, (V j).shade)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (measure_inter_add_diff _ hZ).symm
  calc ∑ i ∈ s, volume ((V i).shade ∩ (⋃ j ∈ L, (V j).shade))
          + θ * (∑ i ∈ s, volume (V i).shade)
      ≤ ∑ i ∈ s, volume ((V i).shade ∩ (⋃ j ∈ L, (V j).shade))
          + ∑ i ∈ s, volume ((V i).shade \ (⋃ j ∈ L, (V j).shade)) := by
        gcongr
        exact hret.trans
          (sum_volume_interShade_le_sum_sdiff_light V W hW hs₃ hfloor hdead hL hlight)
    _ = ∑ i ∈ s, volume (V i).shade := hsplit.symm

omit [Nontrivial E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- **(A) refuted: a family whose sub-threshold members cover the shade union retains nothing,
under every cut.**

If the members that already fail the per-tube floor `ρ` between them cover `⋃_{i ∈ s} Y(V i)`,
then the alive band at threshold `ρ` retains **zero** shade mass — not for the greedy cut of
`ShadedTube.exists_cut_aliveBand`, but for *every* `W` satisfying the alive-band dichotomy.
Clause (f) then fails at every positive `θ`.

Such configurations are compatible with the aggregate fullness binder, which is what makes this
a refutation rather than a curiosity: fullness is driven by the heavy members' shade *volume*,
whereas the light members only have to *cover*, and covering a region of volume `|B|` costs
`2|B|/ρ` extra members — a dilution of the fullness by `1 + 2|B|/(ρ · #heavy)`, which tends to
`1`. So no amount of aggregate fullness rules the configuration out.

The mechanism is entirely in the two lemmas above: light members cannot be alive, so they must
be annihilated; and `ShadedTube.interShade` is a *common* cut, so annihilating them removes
their region from every other member as well. -/
theorem sum_volume_interShade_eq_zero_of_light_cover {δ : NNReal} {s s₃ : Finset ι}
    (V : ι → ShadedTube δ E) (W : Set E) (hW : MeasurableSet W) {ρ : ENNReal}
    (hs₃ : s₃ ⊆ s)
    (hfloor : ∀ i ∈ s₃, ρ ≤ volume (interShade V W hW i).shade)
    (hdead : ∀ i ∈ s, i ∉ s₃ → (interShade V W hW i).shade = ∅)
    {L : Finset ι} (hL : L ⊆ s) (hlight : ∀ j ∈ L, volume (V j).shade < ρ)
    (hcover : ∀ i ∈ s, (V i).shade ⊆ ⋃ j ∈ L, (V j).shade) :
    ∑ i ∈ s₃, volume (interShade V W hW i).shade = 0 := by
  refine le_antisymm ?_ bot_le
  refine (sum_volume_interShade_le_sum_sdiff_light V W hW hs₃ hfloor hdead hL hlight).trans ?_
  refine le_of_eq (Finset.sum_eq_zero fun i hi => ?_)
  rw [Set.diff_eq_empty.mpr (hcover i hi)]
  simp

omit [Nontrivial E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- **Why the Markov pigeonhole does not rescue the alive band: it bounds the wrong side.**

The pigeonhole that the aggregate fullness binder supplies controls `∑_{j ∈ L} |Y(V j)|` — the
light members' *own* mass, which at `ρ = δ^{2η} v` and fullness `≥ δ^η` is at most a `δ^η` share.
What `ShadedTube.lintegral_light_add_le_of_retention` needs bounded is
`∑_{i ∈ s} |Y(V i) ∩ ⋃_{j ∈ L} Y(V j)|`, the mass of their *region*, and this lemma records that
the second dominates the first.

The two differ by exactly the pointwise multiplicity on that region — the quantity
`AliveBand.lean`'s header calls the recurrence, and the one every route to clause (c) prices. -/
theorem sum_volume_shade_light_le_sum_inter_light {δ : NNReal} {s : Finset ι}
    (V : ι → ShadedTube δ E) {L : Finset ι} (hL : L ⊆ s) :
    ∑ j ∈ L, volume (V j).shade
      ≤ ∑ i ∈ s, volume ((V i).shade ∩ (⋃ j ∈ L, (V j).shade)) := by
  classical
  have hEq : ∀ j ∈ L, volume (V j).shade
      = volume ((V j).shade ∩ (⋃ k ∈ L, (V k).shade)) := by
    intro j hj
    have hjj : (V j).shade ∩ (⋃ k ∈ L, (V k).shade) = (V j).shade :=
      Set.inter_eq_left.mpr fun x hx => Set.mem_iUnion₂.mpr ⟨j, hj, hx⟩
    rw [hjj]
  calc ∑ j ∈ L, volume (V j).shade
      = ∑ j ∈ L, volume ((V j).shade ∩ (⋃ k ∈ L, (V k).shade)) := Finset.sum_congr rfl hEq
    _ ≤ ∑ i ∈ s, volume ((V i).shade ∩ (⋃ j ∈ L, (V j).shade)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hL (fun _ _ _ => bot_le)

end ShadedTube

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- **A pointwise-multiplicity bound on a mass-retaining refinement bounds the multiplicity of
the original family.**

If `s' ⊆ s` with the shadings only shrunk, the refinement retains a `θ` share of the shade mass,
and the *pointwise* multiplicity of the refinement is at most `A` on its own shade union, then
`µ(s, V) ≤ θ⁻¹ A`.

This is the exact price of discharging the band hypothesis of
`ShadedTube.nonempty_shadedUniformTubeSet_of_shadeClass_card_le` through a pointwise
multiplicity cut.  `ShadedTube.card_shadeClass_le_pointwiseMultiplicity` is the route from a
pointwise multiplicity bound to a shade-class bound, and every shade class of the retained
family must be at most the uniformity constant `C`; so such a discharge *forces*
`µ(s, V) ≤ θ⁻¹ C`.  At the mass-retention exponent `θ = δ^η` and a subpolynomial `C ≤ δ^(-η')`
that reads `µ ≤ δ^(-(η + η'))` — a multiplicity bound far stronger than the `δ^ν |𝕋|^β` the
section is trying to prove.  So the route is not merely unsupported by the aggregate binders:
it is unavailable. -/
theorem multiplicity_le_of_pointwiseMultiplicity_le_of_mass_retention
    {s s' : Finset ι} {V V' : ι → ShadedBody E} (hs' : s' ⊆ s)
    (hshade : ∀ i ∈ s', (V' i).shade ⊆ (V i).shade) {θ A : ENNReal}
    (hθ0 : θ ≠ 0) (hθtop : θ ≠ ⊤)
    (hmass : θ * ∑ i ∈ s, volume (V i).shade ≤ ∑ i ∈ s', volume (V' i).shade)
    (hpm : ∀ x ∈ (⋃ i ∈ s', (V' i).shade),
      (pointwiseMultiplicity s' V' x : ENNReal) ≤ A) :
    multiplicity s V ≤ θ⁻¹ * A := by
  classical
  have hU'meas : MeasurableSet (⋃ i ∈ s', (V' i).shade) :=
    Finset.measurableSet_biUnion _ fun i _ => (V' i).measurableSet_shade
  have hAU' : ∑ i ∈ s', volume (V' i).shade
      ≤ A * volume (⋃ i ∈ s', (V' i).shade) := by
    refine le_trans (le_of_eq ?_)
      (sum_volume_shade_inter_le_of_pointwiseMultiplicity_le s' V' hU'meas hpm)
    refine Finset.sum_congr rfl fun i hi => ?_
    have hii : (V' i).shade ∩ (⋃ j ∈ s', (V' j).shade) = (V' i).shade :=
      Set.inter_eq_left.mpr fun x hx => Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩
    rw [hii]
  have hvolU : volume (⋃ i ∈ s', (V' i).shade) ≤ volume (⋃ i ∈ s, (V i).shade) := by
    refine measure_mono ?_
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hs' hi, hshade i hi hxi⟩
  rw [multiplicity_le_iff]
  calc ∑ i ∈ s, volume (V i).shade
      = θ⁻¹ * (θ * ∑ i ∈ s, volume (V i).shade) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hθ0 hθtop, one_mul]
    _ ≤ θ⁻¹ * (A * volume (⋃ i ∈ s, (V i).shade)) :=
        mul_le_mul_right (hmass.trans (hAU'.trans (mul_le_mul_right hvolU A))) θ⁻¹
    _ = θ⁻¹ * A * volume (⋃ i ∈ s, (V i).shade) := by rw [mul_assoc]

/-- **The price, read at the section's own exponents.**  A refinement of `s` that keeps a
`δ^η` share of the shade mass and has pointwise multiplicity at most `A` on its own shade union
forces `µ(s, V) ≤ δ^(-η) · A`.

Instantiated at the uniformity constant of GWZ Definition 2.2 — `A = ShadedTube.ssfUniformConst 3`
(absolute) or `A = δ^(-η')` (subpolynomial) — this says that discharging clause (c) through a
pointwise multiplicity cut is *strictly stronger* than the multiplicity bound
`Kakeya.VeryNotSticky.goalMult` that Section 9 exists to prove. -/
theorem multiplicity_le_rpow_of_pointwiseMultiplicity_le_of_mass_retention
    {δ : NNReal} (hδ0 : 0 < δ) {η : ℝ} {s s' : Finset ι} {V V' : ι → ShadedBody E}
    (hs' : s' ⊆ s) (hshade : ∀ i ∈ s', (V' i).shade ⊆ (V i).shade) {A : ENNReal}
    (hmass : (δ : ENNReal) ^ η * ∑ i ∈ s, volume (V i).shade
      ≤ ∑ i ∈ s', volume (V' i).shade)
    (hpm : ∀ x ∈ (⋃ i ∈ s', (V' i).shade),
      (pointwiseMultiplicity s' V' x : ENNReal) ≤ A) :
    multiplicity s V ≤ (δ : ENNReal) ^ (-η) * A := by
  have hδE : (0 : ENNReal) < (δ : ENNReal) := by exact_mod_cast hδ0
  have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h0 : ((δ : ENNReal) ^ η) ≠ 0 := (ENNReal.rpow_pos hδE hδtop).ne'
  have htop : ((δ : ENNReal) ^ η) ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hδE.ne' hδtop
  have h := multiplicity_le_of_pointwiseMultiplicity_le_of_mass_retention
    hs' hshade h0 htop hmass hpm
  rwa [ENNReal.rpow_neg]

/-! ### …and the price is the theorem itself -/

/-- **`δ^(-η)`-scale multiplicity bounds already imply `goalMult`.**

If a family with `δ^{-1}` members — clause (e) of
`Kakeya.VeryNotSticky.BandUniformRefinement`, and the `tube_count` field of the configuration —
has multiplicity at most `δ^(-η) · A` with `A ≤ δ^(-η')`, then it satisfies the conclusion
`µ ≤ δ^ν |𝕋|^β` of `Kakeya.VeryNotSticky.goalMult` for every gain `ν ≤ β - η - η'`.

Composed with `multiplicity_le_rpow_of_pointwiseMultiplicity_le_of_mass_retention`, this says
that discharging clause (c) by a **pointwise multiplicity cut** on the retained family would
already prove Main Lemma 2's own conclusion for that family.  The route is therefore not merely
hard: it is circular, and no amount of pigeonholing inside the setup can supply it.  Note
`Kakeya.VeryNotSticky.CaseParams.slab` gives `9η < β/2`, so `η` is genuinely far below `β` and
the hypothesis `ν ≤ β - η - η'` is satisfiable at the section's own parameters. -/
theorem multiplicity_le_goalMult_of_le_rpow_neg
    {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {β ν η η' : ℝ} (hβ : 0 ≤ β)
    {s : Finset ι} {V : ι → ShadedBody E} {A : ENNReal}
    (htube : (1 : ENNReal) ≤ (δ : ENNReal) * (s.card : ENNReal))
    (hA : A ≤ (δ : ENNReal) ^ (-η'))
    (hmult : multiplicity s V ≤ (δ : ENNReal) ^ (-η) * A)
    (hν : ν ≤ β - η - η') :
    multiplicity s V ≤ (δ : ENNReal) ^ ν * (s.card : ENNReal) ^ β := by
  have hδE : (0 : ENNReal) < (δ : ENNReal) := by exact_mod_cast hδ0
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- `δ^{-1} ≤ |s|`, from the tube count
  have hcard : (δ : ENNReal) ^ (-1 : ℝ) ≤ (s.card : ENNReal) := by
    rw [ENNReal.rpow_neg_one]
    calc (δ : ENNReal)⁻¹ = (δ : ENNReal)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (δ : ENNReal)⁻¹ * ((δ : ENNReal) * (s.card : ENNReal)) := mul_le_mul_right htube _
      _ = (s.card : ENNReal) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hδE.ne' hδtop, one_mul]
  -- hence `δ^{-β} ≤ |s|^β`
  have hcardβ : (δ : ENNReal) ^ (-β) ≤ (s.card : ENNReal) ^ β := by
    have h := ENNReal.rpow_le_rpow hcard hβ
    rwa [← ENNReal.rpow_mul, neg_one_mul] at h
  -- the multiplicity bound, cleared of `A`
  have hstep : multiplicity s V ≤ (δ : ENNReal) ^ (-η - η') := by
    refine hmult.trans ?_
    calc (δ : ENNReal) ^ (-η) * A ≤ (δ : ENNReal) ^ (-η) * (δ : ENNReal) ^ (-η') :=
          mul_le_mul_right hA _
      _ = (δ : ENNReal) ^ (-η + -η') := (ENNReal.rpow_add _ _ hδE.ne' hδtop).symm
      _ = (δ : ENNReal) ^ (-η - η') := by ring_nf
  refine hstep.trans ?_
  calc (δ : ENNReal) ^ (-η - η') ≤ (δ : ENNReal) ^ (ν - β) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
    _ = (δ : ENNReal) ^ ν * (δ : ENNReal) ^ (-β) := by
        rw [← ENNReal.rpow_add _ _ hδE.ne' hδtop]; ring_nf
    _ ≤ (δ : ENNReal) ^ ν * (s.card : ENNReal) ^ β := mul_le_mul_right hcardβ _

/-- **The circularity, in one statement.**

Suppose clause (f) of `Kakeya.VeryNotSticky.BandUniformRefinement` (a `δ^η` share of the shade
mass retained by `s'`, shadings only shrunk), clause (e) (`1 ≤ δ|s|`, which clause (e) on `s'`
implies since `s' ⊆ s`), and a **pointwise multiplicity bound `δ^(-η')` on the retained family**
— which is what a dyadic level-set cut of `ShadedBody.pointwiseMultiplicity` delivers, and the
only route from such a cut to the band hypothesis of
`ShadedTube.nonempty_shadedUniformTubeSet_of_shadeClass_card_le`.  Then the original family
already satisfies `Kakeya.VeryNotSticky.goalMult` at every gain `ν ≤ β - η - η'`.

So that route to clause (c) cannot be an ingredient of the proof of Main Lemma 2: it *is* the
conclusion.  This is a sharper verdict than "the aggregate binders do not bound the pointwise
multiplicity" — they do not, and moreover nothing inside the setup could, because a proof would
be a proof of the theorem. -/
theorem goalMult_of_pointwiseMultiplicity_le_of_mass_retention
    {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {β ν η η' : ℝ} (hβ : 0 ≤ β)
    {s s' : Finset ι} {V V' : ι → ShadedBody E} (hs' : s' ⊆ s)
    (hshade : ∀ i ∈ s', (V' i).shade ⊆ (V i).shade)
    (htube : (1 : ENNReal) ≤ (δ : ENNReal) * (s.card : ENNReal))
    (hmass : (δ : ENNReal) ^ η * ∑ i ∈ s, volume (V i).shade
      ≤ ∑ i ∈ s', volume (V' i).shade)
    (hpm : ∀ x ∈ (⋃ i ∈ s', (V' i).shade),
      (pointwiseMultiplicity s' V' x : ENNReal) ≤ (δ : ENNReal) ^ (-η'))
    (hν : ν ≤ β - η - η') :
    multiplicity s V ≤ (δ : ENNReal) ^ ν * (s.card : ENNReal) ^ β :=
  multiplicity_le_goalMult_of_le_rpow_neg hδ0 hδ1 hβ htube le_rfl
    (multiplicity_le_rpow_of_pointwiseMultiplicity_le_of_mass_retention
      hδ0 hs' hshade hmass hpm) hν

/-- **The refutation at the constant `Kakeya.VeryNotSticky.BandUniformRefinement` actually
fixes.**  That definition demands `ShadedTube.ShadedUniformTubeSet s' T' (Tube.ssfGridLen δ)
(ShadedTube.ssfUniformConst 3)` — a *dimension-only, `δ`-free* constant.  So the band hypothesis
of `ShadedTube.nonempty_shadedUniformTubeSet_of_shadeClass_card_le` would have to hold at
`A = ShadedTube.ssfUniformConst 3`, and a pointwise multiplicity cut delivering it already
proves the section's own conclusion for the family.

`hA` is the only `δ`-dependent input and it is the trivial "for all small `δ`" fact that an
absolute constant is below `δ^(-η')`; every eventually-statement in the section carries it. -/
theorem goalMult_of_pointwiseMultiplicity_le_ssfUniformConst
    {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {β ν η η' : ℝ} (hβ : 0 ≤ β)
    {s s' : Finset ι} {V V' : ι → ShadedBody E} (hs' : s' ⊆ s)
    (hshade : ∀ i ∈ s', (V' i).shade ⊆ (V i).shade)
    (htube : (1 : ENNReal) ≤ (δ : ENNReal) * (s.card : ENNReal))
    (hmass : (δ : ENNReal) ^ η * ∑ i ∈ s, volume (V i).shade
      ≤ ∑ i ∈ s', volume (V' i).shade)
    (hA : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ : ENNReal) ^ (-η'))
    (hpm : ∀ x ∈ (⋃ i ∈ s', (V' i).shade),
      (pointwiseMultiplicity s' V' x : ENNReal)
        ≤ ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal))
    (hν : ν ≤ β - η - η') :
    multiplicity s V ≤ (δ : ENNReal) ^ ν * (s.card : ENNReal) ^ β :=
  multiplicity_le_goalMult_of_le_rpow_neg hδ0 hδ1 hβ htube hA
    (multiplicity_le_rpow_of_pointwiseMultiplicity_le_of_mass_retention
      hδ0 hs' hshade hmass hpm) hν

end ShadedBody
