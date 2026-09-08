/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FibreCommon
public import Kakeya.Tube.Dilate

/-!
# Frostman-at-every-scale transfers across a re-uniformization

`Tube.UniformTubeSet.IsFrostmanAtEveryScale` anchors the Frostman condition to the *nodes* of
one hierarchy.  Re-uniformizing a subfamily (`Tube.exists_uniformTubeSet_subfamily_ssf`) builds a
fresh hierarchy whose nodes are all different, so the condition does not restate itself; this
file proves that it *transfers*, with the loss `C'^3 * C''^3 * L` where `C'`, `C''` are the two
hierarchy constants and `L` is the cardinality share of the subfamily.

## Why no local mass-share hypothesis is needed

The bound a consumer fears is the local one: a class of the old hierarchy could be large while
contributing few leaves to a given new class.  Both halves of the branching bracket
(`Tube.UniformTubeSet.card_class_le` and `Tube.UniformTubeSet.le_card_class`) rule this out:
at a fixed grid index every old class has size `C'`-comparable to the old branching number and
every new class has size `C''`-comparable to the new one, so the local comparison reduces to the
comparison `branchingN' ≲ branchingN''` of the two branching numbers, which is *global* — it
follows from the cardinality share together with a two-way node count
(`Tube.UniformTubeSet.card_indexSet_le_card_indexSet`), where each hierarchy's `boundedOverlap`
field bounds how many nodes of one hierarchy meet a node of the other through the subfamily.

The volume side is free: tubes of one scale are congruent
(`Tube.volume_carrier_eq_volume_carrier`), and the two hierarchies share the grid, so members and
nodes convert between mass and cardinality with no loss.

## The three statements

* `Tube.UniformTubeSet.card_indexSet_le_card_indexSet`: at each grid index the new hierarchy has
  at most `C''` times as many nodes as the old one.
* `Tube.UniformTubeSet.branchingN_le_of_card_le`: the old branching number is at most
  `C' * L * C''^2` times the new one.
* `Tube.UniformTubeSet.IsFrostmanAtEveryScale.transfer`: the every-scale Frostman condition
  moves from the old hierarchy to the new one at the loss `C'^3 * C''^3 * L`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Tube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ : NNReal}

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Node counting across two hierarchies on nested families.**  At each grid index the
hierarchy on the subfamily has at most `C''` times as many nodes as the hierarchy on the ambient
family: every node of the former meets, through the subfamily, the node of the latter that any
member of its class is assigned to, and `boundedOverlap` caps how many nodes share a common
`ρ_k`-tube. -/
theorem UniformTubeSet.card_indexSet_le_card_indexSet
    {s' s'' : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C' C'' : NNReal}
    (𝒰' : UniformTubeSet s' T N C') (𝒰'' : UniformTubeSet s'' T N C'')
    (hsub : s'' ⊆ s') (hs'' : s''.Nonempty) {k : ℕ} (hk : k ≤ N) :
    ((𝒰''.cover.indexSet k).card : NNReal) ≤ C'' * ((𝒰'.cover.indexSet k).card : NNReal) := by
  classical
  -- Each new node meets, through `s''`, the old node of any member of its class.
  have hcov : 𝒰''.cover.indexSet k ⊆
      (𝒰'.cover.indexSet k).biUnion (fun j' =>
        (𝒰''.cover.indexSet k).filter (fun j => ∃ i ∈ s'',
          (T i).toConvexSpaceBody ≤ (𝒰''.cover.tube k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ (𝒰'.cover.tube k j').toConvexSpaceBody)) := by
    intro j'' hj''
    obtain ⟨i, hi⟩ := Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰'' hk hs'' hj''
    simp only [coverClass, Finset.mem_filter] at hi
    obtain ⟨his'', hassign⟩ := hi
    refine Finset.mem_biUnion.mpr
      ⟨𝒰'.cover.assign k i, 𝒰'.cover.assign_mem k hk i (hsub his''),
        Finset.mem_filter.mpr ⟨hj'', i, his'', ?_,
          𝒰'.cover.le_tube_assign k hk i (hsub his'')⟩⟩
    have h := 𝒰''.cover.le_tube_assign k hk i his''
    rwa [hassign] at h
  calc ((𝒰''.cover.indexSet k).card : NNReal)
      ≤ ((∑ j' ∈ 𝒰'.cover.indexSet k,
          ((𝒰''.cover.indexSet k).filter (fun j => ∃ i ∈ s'',
            (T i).toConvexSpaceBody ≤ (𝒰''.cover.tube k j).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ (𝒰'.cover.tube k j').toConvexSpaceBody)).card : ℕ)
          : NNReal) := by
        exact_mod_cast (Finset.card_le_card hcov).trans (Finset.card_biUnion_le)
    _ = ∑ j' ∈ 𝒰'.cover.indexSet k,
          (((𝒰''.cover.indexSet k).filter (fun j => ∃ i ∈ s'',
            (T i).toConvexSpaceBody ≤ (𝒰''.cover.tube k j).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ (𝒰'.cover.tube k j').toConvexSpaceBody)).card : NNReal) := by
        push_cast
        rfl
    _ ≤ ∑ _j' ∈ 𝒰'.cover.indexSet k, C'' :=
        Finset.sum_le_sum fun j' _ => 𝒰''.boundedOverlap k hk (𝒰'.cover.tube k j')
    _ = ((𝒰'.cover.indexSet k).card : NNReal) * C'' := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = C'' * ((𝒰'.cover.indexSet k).card : NNReal) := mul_comm _ _

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The branching numbers of two hierarchies on nested families are comparable.**  If the
subfamily retains a `1/L` share of the cardinality, the branching number of the ambient
hierarchy is at most `C' * L * C''^2` times that of the subfamily's hierarchy at every grid
index.  This is the global comparison to which the two-sided class brackets reduce every local
class-size comparison. -/
theorem UniformTubeSet.branchingN_le_of_card_le
    {s' s'' : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C' C'' : NNReal}
    (𝒰' : UniformTubeSet s' T N C') (𝒰'' : UniformTubeSet s'' T N C'')
    (hsub : s'' ⊆ s') (hs'' : s''.Nonempty) {L : NNReal}
    (hL : (s'.card : NNReal) ≤ L * (s''.card : NNReal)) {k : ℕ} (hk : k ≤ N) :
    𝒰'.branchingN k ≤ C' * L * C'' ^ 2 * 𝒰''.branchingN k := by
  classical
  have hs' : s'.Nonempty := hs''.mono hsub
  -- the classes of each hierarchy partition its family
  have hpart' : s'.card = ∑ j ∈ 𝒰'.cover.indexSet k,
      (coverClass s' (𝒰'.cover.assign k) j).card := by
    simp only [coverClass]
    exact Finset.card_eq_sum_card_fiberwise fun i hi => 𝒰'.cover.assign_mem k hk i hi
  have hpart'' : s''.card = ∑ j ∈ 𝒰''.cover.indexSet k,
      (coverClass s'' (𝒰''.cover.assign k) j).card := by
    simp only [coverClass]
    exact Finset.card_eq_sum_card_fiberwise fun i hi => 𝒰''.cover.assign_mem k hk i hi
  -- lower half on the old side: many nodes force a small branching number
  have hE1 : ((𝒰'.cover.indexSet k).card : NNReal) * 𝒰'.branchingN k
      ≤ C' * (s'.card : NNReal) := by
    calc ((𝒰'.cover.indexSet k).card : NNReal) * 𝒰'.branchingN k
        = ∑ _j ∈ 𝒰'.cover.indexSet k, 𝒰'.branchingN k := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ 𝒰'.cover.indexSet k,
            C' * ((coverClass s' (𝒰'.cover.assign k) j).card : NNReal) :=
          Finset.sum_le_sum fun j hj => 𝒰'.le_card_class k hk j hj
      _ = C' * (s'.card : NNReal) := by
          rw [← Finset.mul_sum, hpart']
          push_cast
          ring
  -- upper half on the new side: the family is carried by its nodes
  have hE2 : (s''.card : NNReal)
      ≤ ((𝒰''.cover.indexSet k).card : NNReal) * (C'' * 𝒰''.branchingN k) := by
    calc (s''.card : NNReal)
        = ∑ j ∈ 𝒰''.cover.indexSet k,
            ((coverClass s'' (𝒰''.cover.assign k) j).card : NNReal) := by
          rw [hpart'']
          push_cast
          rfl
      _ ≤ ∑ _j ∈ 𝒰''.cover.indexSet k, C'' * 𝒰''.branchingN k :=
          Finset.sum_le_sum fun j hj => 𝒰''.card_class_le k hk j hj
      _ = ((𝒰''.cover.indexSet k).card : NNReal) * (C'' * 𝒰''.branchingN k) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hE3 := card_indexSet_le_card_indexSet 𝒰' 𝒰'' hsub hs'' hk
  have hP'pos : 0 < ((𝒰'.cover.indexSet k).card : NNReal) := by
    obtain ⟨i₀, hi₀⟩ := hs'
    exact_mod_cast Finset.card_pos.mpr ⟨_, 𝒰'.cover.assign_mem k hk i₀ hi₀⟩
  refine le_of_mul_le_mul_right ?_ hP'pos
  calc 𝒰'.branchingN k * ((𝒰'.cover.indexSet k).card : NNReal)
      = ((𝒰'.cover.indexSet k).card : NNReal) * 𝒰'.branchingN k := mul_comm _ _
    _ ≤ C' * (s'.card : NNReal) := hE1
    _ ≤ C' * (L * (s''.card : NNReal)) := mul_le_mul_right hL C'
    _ ≤ C' * (L * (((𝒰''.cover.indexSet k).card : NNReal) * (C'' * 𝒰''.branchingN k))) := by
        gcongr
    _ ≤ C' * (L * ((C'' * ((𝒰'.cover.indexSet k).card : NNReal))
          * (C'' * 𝒰''.branchingN k))) := by gcongr
    _ = C' * L * C'' ^ 2 * 𝒰''.branchingN k * ((𝒰'.cover.indexSet k).card : NNReal) := by
        ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Transport of a hierarchy along an equality of tube maps.**  The nodes, the assignment,
the branching numbers and all bounds are those of `𝒰`; only the tube map named in the type
changes, to one pointwise equal to it.  The use case is `Kakeya.ml1Boot.exists_caseFamily`,
which returns a refined family `T₁` whose tubes are *equal* to the input tubes but whose tube
map is a different function, so a hierarchy on the input family does not typecheck against it
verbatim. -/
def UniformTubeSet.copyTubes {s : Finset ι} {T T' : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) (hT : ∀ i, T' i = T i) : UniformTubeSet s T' N C where
  cover :=
    { indexSet := 𝒰.cover.indexSet
      assign := 𝒰.cover.assign
      tube := 𝒰.cover.tube
      assign_mem := 𝒰.cover.assign_mem
      le_tube_assign := fun k hk i hi => by
        rw [hT i]
        exact 𝒰.cover.le_tube_assign k hk i hi
      nested := 𝒰.cover.nested
      tube_nested := 𝒰.cover.tube_nested }
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlap := fun k hk V => by
    simpa only [hT] using 𝒰.boundedOverlap k hk V
  card_class_le := 𝒰.card_class_le
  le_card_class := 𝒰.le_card_class

/-- The every-scale Frostman condition is invariant under
`Tube.UniformTubeSet.copyTubes`: the classes, the node tubes and the member bodies are all
unchanged (the latter pointwise, by the defining equality). -/
theorem UniformTubeSet.IsFrostmanAtEveryScale.copyTubes {s : Finset ι} {T T' : ι → Tube δ E}
    {N : ℕ} {C : NNReal} {𝒰 : UniformTubeSet s T N C} {A : ENNReal}
    (h : 𝒰.IsFrostmanAtEveryScale A) (hT : ∀ i, T' i = T i) :
    (𝒰.copyTubes hT).IsFrostmanAtEveryScale A := by
  have hW : (fun i => (T' i).toConvexSpaceBody) = (fun i => (T i).toConvexSpaceBody) := by
    funext i
    rw [hT i]
  intro k hk j hj
  rw [hW]
  exact h k hk j hj

/-- **Frostman at every scale transfers across a re-uniformization** (at the loss
`C'^3 * C''^3 * L`).

`𝒰'` is a hierarchy on `s'` with constant `C'` and `𝒰''` a hierarchy on a subfamily
`s'' ⊆ s'` with constant `C''`, over the *same* grid; `L` is the cardinality share.  The
every-scale Frostman condition on the nodes of `𝒰'` yields the condition on the nodes of `𝒰''`:

* a class of `𝒰''` is covered by the classes of the at most `C'` nodes of `𝒰'` that meet its
  node through `s'` (`boundedOverlap` of `𝒰'`, one factor `C'`), so its density in any test
  body is at most the sum of theirs, and each of those is Frostman against its own node;
* each old class has cardinality at most `C' * branchingN'` (upper class bracket, the second
  `C'`), the branching numbers compare at `C' * L * C''^2`
  (`Tube.UniformTubeSet.branchingN_le_of_card_le`, the third `C'` and two of the `C''`), and the
  new class has cardinality at least `branchingN'' / C''` (lower class bracket, the last `C''`);
* tubes of one scale are congruent (`Tube.volume_carrier_eq_volume_carrier`), so member masses
  and the volumes of the old and new anchor nodes coincide and the density comparison is exactly
  the cardinality comparison.

No local mass-share hypothesis appears: the two-sided class brackets make every class of a
hierarchy comparable to its branching number, which is what turns the global cardinality share
into the local one this statement needs. -/
theorem UniformTubeSet.IsFrostmanAtEveryScale.transfer
    {s' s'' : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C' C'' : NNReal}
    {𝒰' : UniformTubeSet s' T N C'} (𝒰'' : UniformTubeSet s'' T N C'')
    {A : ENNReal} (h : 𝒰'.IsFrostmanAtEveryScale A)
    (hsub : s'' ⊆ s') {L : NNReal}
    (hL : (s'.card : NNReal) ≤ L * (s''.card : NNReal)) :
    𝒰''.IsFrostmanAtEveryScale
      ((C' : ENNReal) ^ 3 * (C'' : ENNReal) ^ 3 * (L : ENNReal) * A) := by
  classical
  intro k hk j'' hj''
  rcases s''.eq_empty_or_nonempty with rfl | hs''
  · intro K' _
    simp [coverClass]
  set W : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody with hW
  -- a reference member, for the common member volume
  obtain ⟨i₀, hi₀⟩ := Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰'' hk hs'' hj''
  set v : ENNReal := volume (W i₀).carrier with hv
  set Knew : ConvexSpaceBody E := (𝒰''.cover.tube k j'').toConvexSpaceBody with hKnew
  set u : ENNReal := volume Knew.carrier with hu
  -- membership in the new class, unpacked
  have hc''mem : ∀ i ∈ coverClass s'' (𝒰''.cover.assign k) j'',
      i ∈ s'' ∧ 𝒰''.cover.assign k i = j'' := by
    intro i hi
    simpa [coverClass, Finset.mem_filter] using hi
  have hcW : ∀ i ∈ coverClass s'' (𝒰''.cover.assign k) j'', W i ≤ Knew := by
    intro i hi
    obtain ⟨his'', hia⟩ := hc''mem i hi
    have h := 𝒰''.cover.le_tube_assign k hk i his''
    rwa [hia] at h
  -- the closed form of the density against the new node
  have hvols : ∀ i ∈ coverClass s'' (𝒰''.cover.assign k) j'', volume (W i).carrier = v :=
    fun i _ => volume_carrier_eq_volume_carrier (T i) (T i₀)
  have hRHS : Kakeya.densityIn (coverClass s'' (𝒰''.cover.assign k) j'') W Knew
      = ((coverClass s'' (𝒰''.cover.assign k) j'').card : ENNReal) * v / u := by
    rw [Kakeya.densityIn_of_all_le hcW, Finset.sum_congr rfl hvols, Finset.sum_const,
      nsmul_eq_mul]
  intro K' hK'
  -- the old nodes carrying the counted members: the assignment image of the counted set
  set F : Finset ι :=
    {i ∈ coverClass s'' (𝒰''.cover.assign k) j'' | W i ≤ K'} with hF
  set J₀ : Finset ι := F.image (𝒰'.cover.assign k) with hJ₀
  have hFmem : ∀ i ∈ F, i ∈ s'' ∧ 𝒰''.cover.assign k i = j'' ∧ W i ≤ K' := by
    intro i hi
    obtain ⟨hic, hiK'⟩ := Finset.mem_filter.mp hi
    obtain ⟨his'', hia⟩ := hc''mem i hic
    exact ⟨his'', hia, hiK'⟩
  have hJ₀mem : ∀ j' ∈ J₀, j' ∈ 𝒰'.cover.indexSet k := by
    intro j' hj'
    obtain ⟨i, hiF, rfl⟩ := Finset.mem_image.mp hj'
    exact 𝒰'.cover.assign_mem k hk i (hsub (hFmem i hiF).1)
  -- the old nodes involved all meet the new node through `s'`
  have hJ₀card : (J₀.card : NNReal) ≤ C' := by
    refine le_trans ?_ (𝒰'.boundedOverlap k hk (𝒰''.cover.tube k j''))
    refine mod_cast Finset.card_le_card ?_
    intro j' hj'
    obtain ⟨i, hiF, rfl⟩ := Finset.mem_image.mp hj'
    obtain ⟨his'', hia, _⟩ := hFmem i hiF
    refine Finset.mem_filter.mpr
      ⟨𝒰'.cover.assign_mem k hk i (hsub his''), i, hsub his'',
        𝒰'.cover.le_tube_assign k hk i (hsub his''), ?_⟩
    have h := 𝒰''.cover.le_tube_assign k hk i his''
    rwa [hia] at h
  -- Step 1: the counted mass is dominated by the old classes of the meeting nodes.
  have hnum : ∑ i ∈ F, volume (W i).carrier
      ≤ ∑ j' ∈ J₀, ∑ i ∈ coverClass s' (𝒰'.cover.assign k) j' with W i ≤ K',
          volume (W i).carrier := by
    have hfib : ∑ j' ∈ J₀, ∑ i ∈ F with 𝒰'.cover.assign k i = j', volume (W i).carrier
        = ∑ i ∈ F, volume (W i).carrier :=
      Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi)
        (fun i => volume (W i).carrier)
    rw [← hfib]
    refine Finset.sum_le_sum fun j' _ => Finset.sum_le_sum_of_subset ?_
    intro i hi
    obtain ⟨hiF, hia'⟩ := Finset.mem_filter.mp hi
    obtain ⟨his'', _, hiK'⟩ := hFmem i hiF
    simp only [coverClass, Finset.mem_filter]
    exact ⟨⟨hsub his'', hia'⟩, hiK'⟩
  have hstep1 : Kakeya.densityIn (coverClass s'' (𝒰''.cover.assign k) j'') W K'
      ≤ ∑ j' ∈ J₀, Kakeya.densityIn (coverClass s' (𝒰'.cover.assign k) j') W K' := by
    calc Kakeya.densityIn (coverClass s'' (𝒰''.cover.assign k) j'') W K'
        = (∑ i ∈ F, volume (W i).carrier) / volume K'.carrier := rfl
      _ ≤ (∑ j' ∈ J₀, ∑ i ∈ coverClass s' (𝒰'.cover.assign k) j' with W i ≤ K',
            volume (W i).carrier) / volume K'.carrier := ENNReal.div_le_div_right hnum _
      _ = ∑ j' ∈ J₀, Kakeya.densityIn (coverClass s' (𝒰'.cover.assign k) j') W K' := by
          simp only [Kakeya.densityIn, div_eq_mul_inv, Finset.sum_mul]
  -- Step 2: each old class is Frostman against its own node, for every test body.
  have hstep2 : ∀ j' ∈ J₀,
      Kakeya.densityIn (coverClass s' (𝒰'.cover.assign k) j') W K'
        ≤ A * Kakeya.densityIn (coverClass s' (𝒰'.cover.assign k) j') W
            ((𝒰'.cover.tube k j').toConvexSpaceBody) := by
    intro j' hj'
    have hWnode : ∀ i ∈ coverClass s' (𝒰'.cover.assign k) j',
        W i ≤ (𝒰'.cover.tube k j').toConvexSpaceBody := by
      intro i hi
      simp only [coverClass, Finset.mem_filter] at hi
      have h := 𝒰'.cover.le_tube_assign k hk i hi.1
      rwa [hi.2] at h
    exact (Kakeya.le_maxDensity _ _ K').trans
      ((h k hk j' (hJ₀mem j' hj')).maxDensity_le_of_carrier_subset hWnode)
  -- Step 3: the density of an old class in its node is dominated by that of the new class.
  have hstep3 : ∀ j' ∈ J₀,
      Kakeya.densityIn (coverClass s' (𝒰'.cover.assign k) j') W
          ((𝒰'.cover.tube k j').toConvexSpaceBody)
        ≤ ((C' : ENNReal) ^ 2 * (L : ENNReal) * (C'' : ENNReal) ^ 3)
            * Kakeya.densityIn (coverClass s'' (𝒰''.cover.assign k) j'') W Knew := by
    intro j' hj'
    have hWnode : ∀ i ∈ coverClass s' (𝒰'.cover.assign k) j',
        W i ≤ (𝒰'.cover.tube k j').toConvexSpaceBody := by
      intro i hi
      simp only [coverClass, Finset.mem_filter] at hi
      have h := 𝒰'.cover.le_tube_assign k hk i hi.1
      rwa [hi.2] at h
    have hvols' : ∀ i ∈ coverClass s' (𝒰'.cover.assign k) j', volume (W i).carrier = v :=
      fun i _ => volume_carrier_eq_volume_carrier (T i) (T i₀)
    have hunode : volume ((𝒰'.cover.tube k j').toConvexSpaceBody).carrier = u :=
      volume_carrier_eq_volume_carrier (𝒰'.cover.tube k j') (𝒰''.cover.tube k j'')
    -- the cardinality core: an old class against the new class
    have hcardN : ((coverClass s' (𝒰'.cover.assign k) j').card : NNReal)
        ≤ C' ^ 2 * L * C'' ^ 3
            * ((coverClass s'' (𝒰''.cover.assign k) j'').card : NNReal) := by
      calc ((coverClass s' (𝒰'.cover.assign k) j').card : NNReal)
          ≤ C' * 𝒰'.branchingN k := 𝒰'.card_class_le k hk j' (hJ₀mem j' hj')
        _ ≤ C' * (C' * L * C'' ^ 2 * 𝒰''.branchingN k) :=
            mul_le_mul_right (branchingN_le_of_card_le 𝒰' 𝒰'' hsub hs'' hL hk) C'
        _ ≤ C' * (C' * L * C'' ^ 2
              * (C'' * ((coverClass s'' (𝒰''.cover.assign k) j'').card : NNReal))) := by
            gcongr
            exact 𝒰''.le_card_class k hk j'' hj''
        _ = C' ^ 2 * L * C'' ^ 3
              * ((coverClass s'' (𝒰''.cover.assign k) j'').card : NNReal) := by ring
    have hcard : ((coverClass s' (𝒰'.cover.assign k) j').card : ENNReal)
        ≤ (C' : ENNReal) ^ 2 * (L : ENNReal) * (C'' : ENNReal) ^ 3
            * ((coverClass s'' (𝒰''.cover.assign k) j'').card : ENNReal) := by
      exact_mod_cast hcardN
    calc Kakeya.densityIn (coverClass s' (𝒰'.cover.assign k) j') W
          ((𝒰'.cover.tube k j').toConvexSpaceBody)
        = ((coverClass s' (𝒰'.cover.assign k) j').card : ENNReal) * v / u := by
          rw [Kakeya.densityIn_of_all_le hWnode, Finset.sum_congr rfl hvols',
            Finset.sum_const, nsmul_eq_mul, hunode]
      _ ≤ ((C' : ENNReal) ^ 2 * (L : ENNReal) * (C'' : ENNReal) ^ 3
            * ((coverClass s'' (𝒰''.cover.assign k) j'').card : ENNReal)) * v / u := by
          gcongr
      _ = ((C' : ENNReal) ^ 2 * (L : ENNReal) * (C'' : ENNReal) ^ 3)
            * (((coverClass s'' (𝒰''.cover.assign k) j'').card : ENNReal) * v / u) := by
          rw [mul_assoc, mul_div_assoc]
      _ = ((C' : ENNReal) ^ 2 * (L : ENNReal) * (C'' : ENNReal) ^ 3)
            * Kakeya.densityIn (coverClass s'' (𝒰''.cover.assign k) j'') W Knew := by
          rw [hRHS]
  -- Assemble: sum over the at most `C'` meeting nodes.
  calc Kakeya.densityIn (coverClass s'' (𝒰''.cover.assign k) j'') W K'
      ≤ ∑ j' ∈ J₀, Kakeya.densityIn (coverClass s' (𝒰'.cover.assign k) j') W K' := hstep1
    _ ≤ ∑ j' ∈ J₀, A * (((C' : ENNReal) ^ 2 * (L : ENNReal) * (C'' : ENNReal) ^ 3)
          * Kakeya.densityIn (coverClass s'' (𝒰''.cover.assign k) j'') W Knew) :=
        Finset.sum_le_sum fun j' hj' =>
          (hstep2 j' hj').trans (mul_le_mul_right (hstep3 j' hj') A)
    _ = (J₀.card : ENNReal) * (A * (((C' : ENNReal) ^ 2 * (L : ENNReal) * (C'' : ENNReal) ^ 3)
          * Kakeya.densityIn (coverClass s'' (𝒰''.cover.assign k) j'') W Knew)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C' : ENNReal) * (A * (((C' : ENNReal) ^ 2 * (L : ENNReal) * (C'' : ENNReal) ^ 3)
          * Kakeya.densityIn (coverClass s'' (𝒰''.cover.assign k) j'') W Knew)) := by
        gcongr
        exact_mod_cast hJ₀card
    _ = (C' : ENNReal) ^ 3 * (C'' : ENNReal) ^ 3 * (L : ENNReal) * A
          * Kakeya.densityIn (coverClass s'' (𝒰''.cover.assign k) j'') W Knew := by
        ring

end Tube
