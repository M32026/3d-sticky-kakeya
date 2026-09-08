/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Factorization
public import Kakeya.RelativePlankRepair
public import Kakeya.ShadedUniform
public import Kakeya.MultiScaleLoss

/-!
# One tube family that is both multiscale shaded-uniform and plank-structured

GWZ Section 8 needs a single family of tubes carrying, *at one global pair* `(a, b)`, both the
multiscale shaded uniformity of GWZ Definition 2.2 and the plank factorization of GWZ
Proposition 6.6.  The two selections producing those properties are each two-sided — each brackets
class sizes from above *and* below — so neither survives being run after the other.

The order used here is:

1. uniformize the tubes;
2. run the plank pigeonhole, fixing a global `(a, b)`;
3. regularize the grid partitions *and* the plank-block partition **together**, in one finite
   hypergraph cleaning (`Kakeya.exists_jointPartitionRegularization`);
4. keep the outer plank bodies **fixed** and restrict only their fibres
   (`Kakeya.PersistentPlankFactorization`);
5. refine the shading last, which touches no partition
   (`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet`).

Steps 4 and 5 are mechanical given step 3, because
`Kakeya.MultiScaleFac.exists_restrict_uniformTubeSet_band` rebuilds tube uniformity on an
*arbitrary* subfamily from a supplied two-sided bracket, and the shaded uniformization does not
move the index set.
-/

@[expose] public section

open MeasureTheory Metric Kakeya Convexity ConvexSpaceBody
open scoped ENNReal NNReal

noncomputable section

universe u

namespace Kakeya

/-! ### Restricting a uniform hierarchy along a supplied band -/

namespace MultiScaleFac

/-- The constant used when restricting a uniform hierarchy along a supplied class-size band. -/
noncomputable def relativePlankBandRestrictConst (C A : ℝ≥0) : ℝ≥0 := max C (max A 1)

/-- The band-restriction constant is at least the original uniformity constant. -/
theorem le_relativePlankBandRestrictConst {C A : ℝ≥0} : C ≤ relativePlankBandRestrictConst C A :=
  le_max_left _ _

/-- The band-restriction constant is at least the supplied band ratio. -/
theorem band_le_relativePlankBandRestrictConst {C A : ℝ≥0} : A ≤ relativePlankBandRestrictConst C A :=
  le_max_of_le_right (le_max_left _ _)

/-- The band-restriction constant is at least one. -/
theorem one_le_relativePlankBandRestrictConst {C A : ℝ≥0} : 1 ≤ relativePlankBandRestrictConst C A :=
  le_max_of_le_right (le_max_right _ _)

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

open scoped Classical in
omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Restrict a `UniformTubeSet` to an arbitrary subfamily whose class sizes satisfy a supplied
two-sided band.  All geometric fields descend to the subfamily; the band replaces the two
branching-number fields.

**Name note.** This declaration owns the name
`Kakeya.MultiScaleFac.exists_restrict_uniformTubeSet_band`.  Until  an identically-stated
theorem of the same name -- in fact with the identical proof term -- also lived in
`Kakeya/MultiScaleFac/GridUniformBand.lean`; since neither module imports the other and both are
imported by `Kakeya.lean`, the two were merged silently by the import machinery.  That copy is now
`Kakeya.MultiScaleFac.exists_restrict_uniformTubeSet_of_supplied_band`.  Note that this file
declares into the `Kakeya.MultiScaleFac` namespace while living outside `Kakeya/MultiScaleFac/`,
which is what made the collision easy to create. -/
theorem exists_restrict_uniformTubeSet_band {δ : ℝ≥0} {s s' : Finset ι} {T : ι → Tube δ E}
    {M : ℕ} {Cu A C : ℝ≥0} (𝒰 : Tube.UniformTubeSet s T M Cu) (hs' : s' ⊆ s)
    (hCuC : Cu ≤ C) (hAC : A ≤ C) (hC1 : 1 ≤ C) (b : ℕ → ℝ≥0)
    (hband : ∀ k ≤ M, ∀ j ∈ s'.image (𝒰.cover.assign k),
      b k ≤ ((Tube.coverClass s' (𝒰.cover.assign k) j).card : ℝ≥0) ∧
        ((Tube.coverClass s' (𝒰.cover.assign k) j).card : ℝ≥0) ≤ A * b k) :
    ∃ 𝒰' : Tube.UniformTubeSet s' T M C,
      (∀ k, 𝒰'.cover.indexSet k = s'.image (𝒰.cover.assign k)) ∧
        (∀ k, 𝒰'.cover.assign k = 𝒰.cover.assign k) ∧
          (∀ k, 𝒰'.cover.tube k = 𝒰.cover.tube k) ∧
            (∀ k, 𝒰'.branchingN k = b k) := by
  refine ⟨⟨⟨fun k ↦ s'.image (𝒰.cover.assign k), 𝒰.cover.assign, 𝒰.cover.tube,
      (fun k hk i hi ↦ Finset.mem_image_of_mem (𝒰.cover.assign k) hi),
      (fun k hk i hi ↦ 𝒰.cover.le_tube_assign k hk i (hs' hi)),
      (fun k hk i hi j hj h ↦ 𝒰.cover.nested k hk i (hs' hi) j (hs' hj) h),
      (fun k hk i hi ↦ 𝒰.cover.tube_nested k hk i (hs' hi))⟩,
      b, ?_, ?_, ?_, ?_⟩, fun k ↦ rfl, fun k ↦ rfl, fun k ↦ rfl, fun k ↦ rfl⟩
  · intro k hk
    refine Set.InjOn.mono ?_ (𝒰.tube_injOn k hk)
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    exact 𝒰.cover.assign_mem k hk i (hs' hi)
  · intro k hk V
    refine le_trans ?_ ((𝒰.boundedOverlap k hk V).trans hCuC)
    refine Nat.cast_le.mpr (Finset.card_le_card ?_)
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    obtain ⟨hjm, i, hi, hb⟩ := hj
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hjm
    exact ⟨𝒰.cover.assign_mem k hk i' (hs' hi'), i, hs' hi, hb⟩
  · exact fun k hk j hj ↦
      (hband k hk j hj).2.trans (mul_le_mul_of_nonneg_right hAC zero_le)
  · exact fun k hk j hj ↦ (hband k hk j hj).1.trans (le_mul_of_one_le_left zero_le hC1)

end MultiScaleFac

/-! ### The constants of the joint regularization -/

/-- **The dyadic bucket count of a family of size `n`**: the number of dyadic classes a subset
cardinality bounded by `n` can fall into.  Every pigeonhole below pays one factor of this. -/
def relativePlankBucket (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- **The number of partitions cleaned jointly**: the `M + 1` grid levels together with the single
plank-block partition. -/
def relativePlankRounds (M : ℕ) : ℕ := M + 2

/-- **The low-degree deletion threshold of the joint cleaning.**

A class is deleted when its size drops below `1 / relativePlankThreshold` of the current dyadic
bucket value.  The threshold is chosen so that the charging argument spends at most a quarter of the
family: one partition deletes at most `|u| / (4 * relativePlankRounds M)` members, and there are
`relativePlankRounds M` partitions. -/
def relativePlankThreshold (n M : ℕ) : ℕ :=
  4 * relativePlankRounds M * relativePlankBucket n ^ relativePlankRounds M

/-- **The two-sided class-band ratio produced by the joint cleaning**: an upper bound of `2 * N`
against a lower bound of `N / relativePlankThreshold`, so the ratio between the two is
`2 * relativePlankThreshold`.  This is the `A` handed to
`Kakeya.MultiScaleFac.exists_restrict_uniformTubeSet_band`. -/
def relativePlankBandRatio (n M : ℕ) : ℕ := 2 * relativePlankThreshold n M

/-- **The cardinality loss of the joint cleaning**: one dyadic bucketing per partition, plus the
factor `2` for the quarter of the family spent on deletions. -/
def relativePlankJointLoss (n M : ℕ) : ℕ := 2 * relativePlankBucket n ^ relativePlankRounds M

/-- **The fullness loss of the terminal shade-only refinement**, namely the
`(clamp + 1) ^ (2 * M + 2)` of `ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` at
`clamp = Nat.log 2 n`. -/
def relativePlankShadeLoss (n M : ℕ) : ℕ := relativePlankBucket n ^ (2 * M + 2)

/-- **The total loss of the relative plank selection**: the joint cleaning followed by the
shade-only refinement. -/
def relativePlankTotalLoss (n M : ℕ) : ℕ := relativePlankJointLoss n M * relativePlankShadeLoss n M

/-- The bucket count is at least `1`. -/
theorem one_le_relativePlankBucket (n : ℕ) : 1 ≤ relativePlankBucket n :=
  Nat.le_add_left 1 (Nat.log 2 n)

/-- The number of jointly cleaned partitions is at least `1`. -/
theorem one_le_relativePlankRounds (M : ℕ) : 1 ≤ relativePlankRounds M := by
  simp only [relativePlankRounds]; omega

/-- The deletion threshold is at least `1`. -/
theorem one_le_relativePlankThreshold (n M : ℕ) : 1 ≤ relativePlankThreshold n M := by
  have hb : 1 ≤ relativePlankBucket n ^ relativePlankRounds M :=
    Nat.one_le_pow _ _ (one_le_relativePlankBucket n)
  have hr : 1 ≤ 4 * relativePlankRounds M := by
    simp only [relativePlankRounds]; omega
  simpa only [relativePlankThreshold] using Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hr) (Nat.one_le_iff_ne_zero.mp hb))

/-- The class-band ratio is at least `1`. -/
theorem one_le_relativePlankBandRatio (n M : ℕ) : 1 ≤ relativePlankBandRatio n M := by
  have h := one_le_relativePlankThreshold n M
  simp only [relativePlankBandRatio]; omega

/-- The cardinality loss of the joint cleaning is at least `1`. -/
theorem one_le_relativePlankJointLoss (n M : ℕ) : 1 ≤ relativePlankJointLoss n M := by
  have hb : 1 ≤ relativePlankBucket n ^ relativePlankRounds M :=
    Nat.one_le_pow _ _ (one_le_relativePlankBucket n)
  simp only [relativePlankJointLoss]; omega

/-- The fullness loss of the shade-only refinement is at least `1`. -/
theorem one_le_relativePlankShadeLoss (n M : ℕ) : 1 ≤ relativePlankShadeLoss n M :=
  Nat.one_le_pow _ _ (one_le_relativePlankBucket n)

/-- The total loss is at least `1`. -/
theorem one_le_relativePlankTotalLoss (n M : ℕ) : 1 ≤ relativePlankTotalLoss n M :=
  Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp (one_le_relativePlankJointLoss n M))
      (Nat.one_le_iff_ne_zero.mp (one_le_relativePlankShadeLoss n M)))

/-! ### The joint regularization of several partitions -/

/-- **One dyadic bucketing round, keeping whole classes.**

Bucketing the nonempty `g`-classes of `w` by `Nat.log 2` of their cardinality and keeping the
heaviest bucket costs a factor `Nat.log 2 w.card + 1 ≤ C` in cardinality and leaves every retained
class with cardinality in `[N, 2 * N)`, *measured in the input set `w`*.  That the band is measured
in `w` rather than in `w'` is what makes the protected clause of
`Kakeya.exists_jointPartitionRegularization` available for the round run first. -/
theorem exists_dyadicClassRound {ι ν : Type*} [DecidableEq ν]
    (w : Finset ι) (g : ι → ν) (C : ℕ) (hC : Nat.log 2 w.card + 1 ≤ C) :
    ∃ w' ⊆ w, ∃ N : ℕ, 1 ≤ N ∧ w.card ≤ C * w'.card ∧
      ∀ v ∈ w'.image g, N ≤ {i ∈ w | g i = v}.card ∧ {i ∈ w | g i = v}.card < 2 * N := by
  obtain ⟨kh, khle, hsum⟩ :=
    Nat.dyadic_pigeonhole w (fun _ => 1) (fun i => {i' ∈ w | g i' = g i}.card)
      (fun i hi => ⟨Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩,
        Finset.card_le_card (Finset.filter_subset _ _)⟩)
  let wsub := {i ∈ w | 2 ^ kh ≤ {i' ∈ w | g i' = g i}.card ∧
      {i' ∈ w | g i' = g i}.card < 2 ^ (kh + 1)}
  refine ⟨wsub, Finset.filter_subset _ _, 2 ^ kh, Nat.one_le_two_pow, ?_, ?_⟩
  · have hcard : w.card ≤ (Nat.log 2 w.card + 1) * wsub.card := by
      simpa [Kakeya.dyadicPigeonholeNatConstant] using hsum
    exact hcard.trans (Nat.mul_le_mul_right _ hC)
  · intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hwi, rfl⟩
    have hmem := (Finset.mem_filter.mp hwi).2
    exact ⟨hmem.1, by simpa [pow_succ, Nat.mul_comm] using hmem.2⟩

/-- **Counting the classes that meet a subfamily.**

If every `g`-class meeting `u` has at least `N` elements of the ambient set `w`, then, the classes
being disjoint, there are at most `w.card / N` of them.  Stated multiplicatively, so that no
natural-number division occurs. -/
theorem mul_card_image_le_card_of_le_class_card {ι ν : Type*} [DecidableEq ν]
    {w u : Finset ι} (hu : u ⊆ w) (g : ι → ν) (N : ℕ)
    (h : ∀ v ∈ u.image g, N ≤ {i ∈ w | g i = v}.card) :
    N * (u.image g).card ≤ w.card := by
  calc
    N * (u.image g).card
        ≤ ∑ v ∈ u.image g, {i ∈ w | g i = v}.card := by
          simpa [nsmul_eq_mul, mul_comm] using
            Finset.card_nsmul_le_sum (u.image g) (fun v => {i ∈ w | g i = v}.card) N h
    _ ≤ ∑ v ∈ w.image g, {i ∈ w | g i = v}.card := by
          exact Finset.sum_le_sum_of_subset
            (Finset.image_subset_image hu)
    _ = w.card := (Finset.card_eq_sum_card_image g w).symm

/-- **Iterating the dyadic bucketing over `n + 1` partitions.**

Running `Kakeya.exists_dyadicClassRound` once per partition, partition `0` **first**, produces a
decreasing chain whose terminal set `u` costs `C ^ (n + 1)` in cardinality and on which every
partition has a two-sided class band.  Three of the four conclusions are stated on `u` itself; the
fourth records that partition `0`, having been bucketed on the original `w`, retains its band
*against `w`*. -/
theorem exists_dyadicClassChain {ι ν : Type*} [DecidableEq ν]
    (n : ℕ) (C : ℕ) (g : ℕ → ι → ν) (w : Finset ι) (hC : Nat.log 2 w.card + 1 ≤ C) :
    ∃ u ⊆ w, ∃ Nb : ℕ → ℕ,
      w.card ≤ C ^ (n + 1) * u.card ∧
      (∀ p ≤ n, 1 ≤ Nb p) ∧
      (∀ p ≤ n, Nb p * (u.image (g p)).card ≤ w.card) ∧
      (∀ p ≤ n, ∀ v ∈ u.image (g p), {i ∈ u | g p i = v}.card < 2 * Nb p) ∧
      (∀ v ∈ u.image (g 0), Nb 0 ≤ {i ∈ w | g 0 i = v}.card ∧
        {i ∈ w | g 0 i = v}.card < 2 * Nb 0) := by
  suffices hkey : ∀ (k : ℕ) (g : ℕ → ι → ν) (wH : Finset ι),
      Nat.log 2 wH.card + 1 ≤ C → ∃ u ⊆ wH, ∃ Nb : ℕ → ℕ,
        wH.card ≤ C ^ (k + 1) * u.card ∧
          (∀ p ≤ k, 1 ≤ Nb p) ∧
          (∀ p ≤ k, Nb p * (u.image (g p)).card ≤ wH.card) ∧
          (∀ p ≤ k, ∀ v ∈ u.image (g p), {i ∈ u | g p i = v}.card < 2 * Nb p) ∧
          (∀ v ∈ u.image (g 0), Nb 0 ≤ {i ∈ wH | g 0 i = v}.card ∧
            {i ∈ wH | g 0 i = v}.card < 2 * Nb 0)
    by
      exact hkey n g w hC
  intro k
  induction k with
  | zero =>
      intro g w hH0
      rcases exists_dyadicClassRound w (g 0) C hH0 with ⟨w', hw', N, hN0, hle, hband⟩
      refine ⟨w', hw', (fun _ => N), ?r, ?on1, ?cnt, ?upb, ?last⟩
      · simpa [pow_one] using hle
      · intro p hp
        simpa using hN0
      · intro p hp
        have hp0 : p = 0 := by omega
        subst hp0
        simpa using mul_card_image_le_card_of_le_class_card hw' (g 0) N
          (fun v hv => (hband v hv).1)
      · intro p hp
        have hp0 : p = 0 := by omega
        subst hp0
        intro v hv
        have hin : ({i ∈ w' | g 0 i = v} : Finset ι) ⊆ ({i ∈ w | g 0 i = v} : Finset ι) := by
          intro i hi
          exact Finset.mem_filter.mpr
            ⟨hw' (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
        simpa using lt_of_le_of_lt (Finset.card_le_card hin) (hband v hv).2
      · intro v hv
        simpa using hband v hv
  | succ n ih =>
      intro g w hC0
      rcases exists_dyadicClassRound w (g 0) C hC0 with ⟨w', hw', N, hN0, hle, hband⟩
      have hC1 : Nat.log 2 w'.card + 1 ≤ C := by
        have hwc : w'.card ≤ w.card := Finset.card_le_card hw'
        have hlog : Nat.log 2 w'.card ≤ Nat.log 2 w.card := Nat.log_mono_right hwc
        omega
      let gS : ℕ → ι → ν := fun p => g (p + 1)
      rcases ih gS w' hC1 with ⟨u, hu, Nb', hretw, honeP, hcountP, hupP, _⟩
      let Nb : ℕ → ℕ := fun p => if p = 0 then N else Nb' (p - 1)
      have hu_w : u ⊆ w := hu.trans hw'
      refine ⟨u, hu_w, Nb, ?r1, ?o1, ?c1, ?u1, ?z1⟩
      · have hmul : C * w'.card ≤ C * (C ^ (n + 1) * u.card) :=
          Nat.mul_le_mul_left _ hretw
        calc
          w.card ≤ C * w'.card := hle
          _ ≤ C * (C ^ (n + 1) * u.card) := hmul
          _ = C ^ (n + 1 + 1) * u.card := by
            rw [← mul_assoc, ← pow_succ']
      · intro p hp
        cases p with
        | zero => simpa [Nb] using hN0
        | succ q =>
            have hq : q ≤ n := by omega
            simpa [Nb] using honeP q hq
      · intro p hp
        cases p with
        | zero =>
            have hlow : ∀ a ∈ u.image (g 0), N ≤ {i ∈ w | g 0 i = a}.card := by
              intro a ha
              have ha' : a ∈ w'.image (g 0) := Finset.image_subset_image hu ha
              exact (hband a ha').1
            simpa [Nb] using mul_card_image_le_card_of_le_class_card hu_w (g 0) N hlow
        | succ q =>
            have hq : q ≤ n := by omega
            have hcore : Nb' q * (u.image (gS q)).card ≤ w'.card := hcountP q hq
            simpa [Nb, gS] using le_trans hcore (Finset.card_le_card hw')
      · intro p hp
        cases p with
        | zero =>
            intro v hv
            have hv' : v ∈ w'.image (g 0) := Finset.image_subset_image hu hv
            have hin : ({i ∈ u | g 0 i = v} : Finset ι) ⊆ ({i ∈ w | g 0 i = v} : Finset ι) := by
              intro i hi
              exact Finset.mem_filter.mpr
                ⟨hu_w (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
            simpa [Nb] using lt_of_le_of_lt (Finset.card_le_card hin) (hband v hv').2
        | succ q =>
            have hq : q ≤ n := by omega
            intro v hv
            have hvS : v ∈ u.image (gS q) := by simpa [gS] using hv
            simpa [Nb, gS] using hupP q hq v hvS
      · intro v hv
        have hv' : v ∈ w'.image (g 0) := Finset.image_subset_image hu hv
        simpa [Nb] using hband v hv'

/-- **The charging potential of the joint cleaning**: the number of active classes of each
partition, weighted by that partition's dyadic scale.  Deleting one whole class of partition `p`
drops the potential by at least `Nb p`, which is what pays for the deletion. -/
def jointPotential {ι ν : Type*} [DecidableEq ν] {R : ℕ}
    (Nb : Fin R → ℕ) (f : Fin R → ι → ν) (w : Finset ι) : ℕ :=
  ∑ p : Fin R, Nb p * (w.image (f p)).card

/-- **Deleting a whole class drops the potential by the scale of its partition.** -/
theorem jointPotential_add_le_of_deletion {ι ν : Type*} [DecidableEq ν] {R : ℕ}
    (Nb : Fin R → ℕ) (f : Fin R → ι → ν) (u : Finset ι) (p : Fin R) {v : ν}
    (hv : v ∈ u.image (f p)) :
    jointPotential Nb f {i ∈ u | f p i ≠ v} + Nb p ≤ jointPotential Nb f u := by
  let w : Finset ι := {i ∈ u | f p i ≠ v}
  have hwu : w ⊆ u := by
    dsimp [w]
    exact Finset.filter_subset (s := u) (p := fun i => f p i ≠ v)
  have hvnw : v ∉ w.image (f p) := by
    intro hb
    rcases Finset.mem_image.mp hb with ⟨i, hiw, hfp⟩
    have hne : f p i ≠ v := (Finset.mem_filter.mp hiw).2
    exact hne hfp
  have hAsub : w.image (f p) ⊆ u.image (f p) :=
    Finset.image_subset_image hwu
  have hssub : w.image (f p) ⊂ u.image (f p) := by
    exact (Finset.ssubset_iff_of_subset hAsub).mpr ⟨v, by simpa [w] using hv, hvnw⟩
  have hA0 : Nb p * (w.image (f p)).card + Nb p ≤ Nb p * (u.image (f p)).card := by
    have hlt : (w.image (f p)).card < (u.image (f p)).card := Finset.card_lt_card hssub
    simpa [Nat.mul_add, mul_one] using (Nat.mul_le_mul_left (Nb p) hlt)
  unfold jointPotential
  let A : Fin R → ℕ := fun q => Nb q * (w.image (f q)).card
  let B : Fin R → ℕ := fun q => Nb q * (u.image (f q)).card
  have hA : A p + Nb p ≤ B p := by
    simpa [A, B] using hA0
  have hB : ∀ q, A q ≤ B q := by
    intro q
    exact Nat.mul_le_mul_left (Nb q)
      (Finset.card_le_card (Finset.image_subset_image hwu))
  calc
    (∑ q : Fin R, A q) + Nb p = (A p + Nb p) + ∑ q ∈ Finset.univ.erase p, A q := by
      rw [← Finset.add_sum_erase Finset.univ A (Finset.mem_univ p)]
      ac_rfl
    _ ≤ B p + ∑ q ∈ Finset.univ.erase p, B q := by
      exact Nat.add_le_add hA (Finset.sum_le_sum (fun q hq => hB q))
    _ = ∑ q : Fin R, B q := by
      exact (Finset.add_sum_erase Finset.univ B (Finset.mem_univ p))

/-- **The potential of the chain terminus is affordable**: each of the `R` partitions contributes at
most `n`, by `Kakeya.mul_card_image_le_card_of_le_class_card`. -/
theorem jointPotential_le_mul {ι ν : Type*} [DecidableEq ν] {R : ℕ}
    (Nb : Fin R → ℕ) (f : Fin R → ι → ν) (u : Finset ι) (n : ℕ)
    (h : ∀ p : Fin R, Nb p * (u.image (f p)).card ≤ n) :
    jointPotential Nb f u ≤ R * n := by
  simp only [jointPotential]
  simpa [nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] using
    Finset.sum_le_card_nsmul Finset.univ (fun p : Fin R => Nb p * (u.image (f p)).card) n
      (fun p _hp => h p)

/-- **Iterated low-degree deletion.**

Repeatedly delete a whole class whose cardinality has dropped below `Nb p / T`, until none remains.
The terminal family satisfies the reverse inequality `Nb p ≤ T * card` for every active class, and
the total cost of the deletions is charged against `Kakeya.jointPotential`: this is the invariant
`T * u.card + Φ s' ≤ T * s'.card + Φ u`, which telescopes over the recursion because each single
deletion of a class of size `c` obeys `T * c < Nb p ≤ Φ w - Φ w'`. -/
theorem exists_stableClassDeletion {ι ν : Type*} [DecidableEq ν] {R : ℕ}
    (T : ℕ) (Nb : Fin R → ℕ) (f : Fin R → ι → ν) (u : Finset ι) :
    ∃ s' ⊆ u,
      (∀ p : Fin R, ∀ v ∈ s'.image (f p), Nb p ≤ T * {i ∈ s' | f p i = v}.card) ∧
      T * u.card + jointPotential Nb f s' ≤ T * s'.card + jointPotential Nb f u := by
  classical
  induction u using Finset.strongInductionOn with
  | _ u IH =>
    by_cases hex : ∃ (p : Fin R) (v : ν), v ∈ u.image (f p) ∧
        T * {i ∈ u | f p i = v}.card < Nb p
    · obtain ⟨p, v, hv, hlt⟩ := hex
      let u₁ : Finset ι := {i ∈ u | f p i ≠ v}
      have hsub₁ : u₁ ⊆ u := Finset.filter_subset (fun i => f p i ≠ v) u
      have hssub : u₁ ⊂ u := by
        obtain ⟨x, hxu, hfx⟩ := Finset.mem_image.mp hv
        refine (Finset.ssubset_iff_of_subset hsub₁).mpr ⟨x, hxu, ?_⟩
        intro hx
        exact (Finset.mem_filter.mp hx).2 hfx
      obtain ⟨s', hs'u₁, hStab, hinv⟩ := IH u₁ hssub
      refine ⟨s', hs'u₁.trans hsub₁, hStab, ?_⟩
      have hFn : {i ∈ u | f p i = v}.card + u₁.card = u.card :=
        Finset.card_filter_add_card_filter_not (s := u) (p := fun i => f p i = v)
      have hTmul : T * u.card = T * {i ∈ u | f p i = v}.card + T * u₁.card := by
        rw [← hFn, Nat.mul_add]
      have hdel : jointPotential Nb f u₁ + Nb p ≤ jointPotential Nb f u :=
        jointPotential_add_le_of_deletion Nb f u p hv
      omega
    · refine ⟨u, subset_rfl, ?_, le_rfl⟩
      intro p v hv
      by_contra! hcon
      exact hex ⟨p, v, hv, hcon⟩

/-- **The smallest active class of each partition**, with the value `0` when the partition has no
active class.  This is the `N` of `Kakeya.exists_jointPartitionRegularization`. -/
theorem exists_min_class_card {ι ν : Type*} [DecidableEq ν] {R : ℕ}
    (t : Finset ι) (g : Fin R → ι → ν) :
    ∃ N : Fin R → ℕ, ∀ p : Fin R,
      (∀ v ∈ t.image (g p), N p ≤ {i ∈ t | g p i = v}.card) ∧
      (∀ v₀ ∈ t.image (g p), ∃ v ∈ t.image (g p), {i ∈ t | g p i = v}.card ≤ N p) := by
  have key : ∀ p : Fin R,
      ∃ N : ℕ,
        (∀ v ∈ t.image (g p), N ≤ {i ∈ t | g p i = v}.card) ∧
          (∀ v₀ ∈ t.image (g p), ∃ v ∈ t.image (g p),
            {i ∈ t | g p i = v}.card ≤ N) := by
    intro p
    by_cases hne : (t.image (g p)).Nonempty
    · rcases Finset.exists_min_image (t.image (g p))
        (fun v : ν => {i ∈ t | g p i = v}.card) hne with ⟨v₁, hvmem, hvmin⟩
      refine ⟨{i ∈ t | g p i = v₁}.card, ?_, ?_⟩
      · intro v hv
        exact hvmin v hv
      · intro hvn0 hv0
        refine ⟨v₁, hvmem, le_rfl⟩
    · refine ⟨0, ?_, ?_⟩
      · intro v hv
        exact Nat.zero_le _
      · intro v0 hv0
        exact False.elim (hne ⟨v0, hv0⟩)
  choose N hN using key
  exact ⟨N, hN⟩

/-- **The charging arithmetic of the joint cleaning.**

With `T = 4 * R * Bp` the deletion charge `T * b ≤ T * c + R * a` against the chain retention
`a ≤ Bp * b` forces `3 * b ≤ 4 * c`, hence `a ≤ 2 * Bp * c`.  Here `a`, `b`, `c` are the
cardinalities of the original family, the chain terminus and the cleaned family. -/
theorem card_le_of_jointCharge {T R Bp a b c : ℕ} (hR : 1 ≤ R) (hBp : 1 ≤ Bp)
    (hT : T = 4 * R * Bp) (hab : T * b ≤ T * c + R * a) (ha : a ≤ Bp * b) :
    a ≤ 2 * Bp * c := by
  subst hT
  set K : ℕ := R * Bp with hK
  have hRpos : 0 < R := by omega
  have hBppos : 0 < Bp := by omega
  have hKpos : 0 < K := by rw [hK]; exact Nat.mul_pos hRpos hBppos
  have hRa : R * a ≤ K * b := by
    calc
      R * a ≤ R * (Bp * b) := Nat.mul_le_mul_left R ha
      _ = K * b := by rw [← Nat.mul_assoc, hK]
  have habK : (4 * K) * b ≤ (4 * K) * c + K * b := by
    calc
      (4 * K) * b ≤ (4 * K) * c + R * a := by
        simpa [mul_assoc, mul_comm, mul_left_comm, hK] using hab
      _ ≤ (4 * K) * c + K * b := by
        exact Nat.add_le_add_left hRa ((4 * K) * c)
  have h3 : 3 * K * b ≤ 4 * K * c := by
    nlinarith
  have h24 : 3 * b ≤ 4 * c := by
    have : K * (3 * b) ≤ K * (4 * c) := by nlinarith [h3]
    exact Nat.le_of_mul_le_mul_left this hKpos
  have hacs : 3 * a ≤ 3 * (2 * Bp * c) := by
    calc
      3 * a ≤ 3 * (Bp * b) := Nat.mul_le_mul_left 3 ha
      _ = Bp * (3 * b) := by ring
      _ ≤ Bp * (4 * c) := Nat.mul_le_mul_left Bp h24
      _ = 4 * (Bp * c) := by ring
      _ ≤ 3 * (2 * Bp * c) := by nlinarith
  exact Nat.le_of_mul_le_mul_left hacs (by omega : 0 < 3)

/-- **Joint regularization of `M + 2` partitions of one finite family.**

This is *one* finite-hypergraph cleaning, not two alternating pigeonholes: alternating them would
destroy each bracket with the next selection, since every bracket here is two-sided.  After one
dyadic bucketing per partition — partition `0` **first**, and performed on the original `s`, which
is what makes the last clause available — whole low-degree classes are deleted repeatedly until the
configuration is stable.

The charge is affordable because the *upper* bounds on class sizes only descend: partition `p`
therefore has at most `|u p| / N p` active classes, and deleting each at cost
`N p / relativePlankThreshold` spends at most `|u p| / relativePlankThreshold` in total.

Partition index `0` is the plank-block partition and is **protected**: its clause is stated against
the *original* family `s`, so the retained fibre of every surviving plank block is a definite
fraction of the original fibre.  Partitions `p + 1` are the grid levels, for which only the
two-sided band on the retained family is needed. -/
theorem exists_jointPartitionRegularization {ι ν : Type*} [DecidableEq ν]
    (s : Finset ι) (M : ℕ) (f : Fin (M + 2) → ι → ν) :
    ∃ s' ⊆ s, ∃ N : Fin (M + 2) → ℕ,
      s.card ≤ relativePlankJointLoss s.card M * s'.card ∧
      (∀ p : Fin (M + 2), ∀ v ∈ s'.image (f p),
        N p ≤ {i ∈ s' | f p i = v}.card ∧
          {i ∈ s' | f p i = v}.card ≤ relativePlankBandRatio s.card M * N p) ∧
      (∀ v ∈ s'.image (f 0), {i ∈ s | f 0 i = v}.card ≤
        relativePlankBandRatio s.card M * {i ∈ s' | f 0 i = v}.card) := by
  classical
  let B : ℕ := relativePlankBucket s.card
  let g : ℕ → ι → ν := fun p => if hp : p < M + 2 then f ⟨p, hp⟩ else f 0
  have hC : Nat.log 2 s.card + 1 ≤ B := by
    exact le_rfl
  rcases exists_dyadicClassChain (M + 1) B g s hC with ⟨u, hus, Nb, hret, hone, hcnt, hup, hprot⟩
  have hple : ∀ p : Fin (M + 2), (p : ℕ) ≤ M + 1 := by
    intro p
    exact Nat.le_of_lt_succ p.isLt
  have hidx : ∀ p : Fin (M + 2), g (p : ℕ) = f p := by
    intro p
    dsimp [g]
    exact dif_pos p.isLt
  let Nbf : Fin (M + 2) → ℕ := fun p => Nb (p : ℕ)
  have hcntF : ∀ p : Fin (M + 2), Nbf p * (u.image (f p)).card ≤ s.card := by
    intro p
    have hg : g (p : ℕ) = f p := hidx p
    simpa [Nbf, hg] using hcnt (p : ℕ) (hple p)
  have hupF : ∀ p : Fin (M + 2), ∀ v ∈ u.image (f p),
      {i ∈ u | f p i = v}.card < 2 * Nbf p := by
    intro p v hv
    have hg : g (p : ℕ) = f p := hidx p
    have hv' : v ∈ u.image (g (p : ℕ)) := by simpa [hg] using hv
    simpa [Nbf, hg] using hup (p : ℕ) (hple p) v hv'
  have hg0 : g 0 = f 0 := by
    dsimp [g]
  have hprotF : ∀ v ∈ u.image (f 0), Nbf 0 ≤ {i ∈ s | f 0 i = v}.card ∧
      {i ∈ s | f 0 i = v}.card < 2 * Nbf 0 := by
    intro v hv
    have hv' : v ∈ u.image (g 0) := by simpa [hg0] using hv
    have hprot0 := hprot v hv'
    have hN0 : Nbf 0 = Nb 0 := by
      dsimp [Nbf]
    simpa [hg0, hN0] using hprot0
  let T : ℕ := relativePlankThreshold s.card M
  rcases exists_stableClassDeletion T Nbf f u with ⟨s', hs'u, hstab, hinv⟩
  have hs's : s' ⊆ s := hs'u.trans hus
  have hΦu : jointPotential Nbf f u ≤ (M + 2) * s.card := by
    exact jointPotential_le_mul Nbf f u s.card hcntF
  have hcharge : T * u.card ≤ T * s'.card + (M + 2) * s.card := by
    omega
  have hBp : 1 ≤ B ^ (M + 2) := by
    exact Nat.one_le_pow _ _ (by dsimp [B]; exact one_le_relativePlankBucket s.card)
  have hT : T = 4 * (M + 2) * B ^ (M + 2) := by
    dsimp [T, B]
    simp [relativePlankThreshold, relativePlankRounds]
  have hret' : s.card ≤ B ^ (M + 2) * u.card := by
    simpa using hret
  have hcard : s.card ≤ 2 * B ^ (M + 2) * s'.card := by
    exact card_le_of_jointCharge (R := M + 2) (Bp := B ^ (M + 2)) (T := T)
      (a := s.card) (b := u.card) (c := s'.card)
      (by omega : 1 ≤ M + 2) hBp hT hcharge hret'
  have hretention : s.card ≤ relativePlankJointLoss s.card M * s'.card := by
    simpa [relativePlankJointLoss, relativePlankRounds, B] using hcard
  rcases exists_min_class_card s' f with ⟨N, hN⟩
  refine ⟨s', hs's, N, hretention, ?band, ?prot⟩
  · intro p v hv
    have hNlo : N p ≤ {i ∈ s' | f p i = v}.card := (hN p).1 v hv
    rcases (hN p).2 v hv with ⟨v₁, hv₁, hmin⟩
    have hstab1 : Nbf p ≤ T * {i ∈ s' | f p i = v₁}.card := hstab p v₁ hv₁
    have hNbf_le : Nbf p ≤ T * N p := by
      calc
        Nbf p ≤ T * {i ∈ s' | f p i = v₁}.card := hstab1
        _ ≤ T * N p := Nat.mul_le_mul_left T hmin
    have hv_u : v ∈ u.image (f p) := Finset.image_subset_image hs'u hv
    have hsub : ({i ∈ s' | f p i = v} : Finset ι) ⊆ ({i ∈ u | f p i = v} : Finset ι) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨hs'u (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
    have hcard_le : {i ∈ s' | f p i = v}.card ≤ {i ∈ u | f p i = v}.card :=
      Finset.card_le_card hsub
    have hup1 : {i ∈ u | f p i = v}.card < 2 * Nbf p := hupF p v hv_u
    have hup2 : {i ∈ s' | f p i = v}.card < 2 * Nbf p := lt_of_le_of_lt hcard_le hup1
    have hup3 : 2 * Nbf p ≤ 2 * (T * N p) := Nat.mul_le_mul_left 2 hNbf_le
    have hup4 : {i ∈ s' | f p i = v}.card < 2 * (T * N p) := lt_of_lt_of_le hup2 hup3
    have hup5 : 2 * (T * N p) = (2 * T) * N p := by ring
    have hup6 : {i ∈ s' | f p i = v}.card < (2 * T) * N p := by simpa [hup5] using hup4
    have hBT : 2 * T = relativePlankBandRatio s.card M := by
      dsimp [T]
      simp [relativePlankBandRatio, relativePlankThreshold, relativePlankRounds]
    have hup7 : {i ∈ s' | f p i = v}.card ≤ relativePlankBandRatio s.card M * N p := by
      rw [← hBT]
      exact Nat.le_of_lt hup6
    exact ⟨hNlo, hup7⟩
  · intro v hv
    have hv_u : v ∈ u.image (f 0) := Finset.image_subset_image hs'u hv
    have hprot0 := hprotF v hv_u
    have hlt : {i ∈ s | f 0 i = v}.card < 2 * Nbf 0 := hprot0.2
    have hstab0 : Nbf 0 ≤ T * {i ∈ s' | f 0 i = v}.card := hstab 0 v hv
    have hlt2 : {i ∈ s | f 0 i = v}.card < 2 * (T * {i ∈ s' | f 0 i = v}.card) := by
      calc
        {i ∈ s | f 0 i = v}.card < 2 * Nbf 0 := hlt
        _ ≤ 2 * (T * {i ∈ s' | f 0 i = v}.card) := Nat.mul_le_mul_left 2 hstab0
    have hBT : 2 * T = relativePlankBandRatio s.card M := by
      dsimp [T]
      simp [relativePlankBandRatio, relativePlankThreshold, relativePlankRounds]
    have hlt3 : {i ∈ s | f 0 i = v}.card ≤
        relativePlankBandRatio s.card M * {i ∈ s' | f 0 i = v}.card := by
      rw [← hBT]
      have h5 : 2 * (T * {i ∈ s' | f 0 i = v}.card) = (2 * T) * {i ∈ s' | f 0 i = v}.card := by ring
      rw [← h5]
      exact Nat.le_of_lt hlt2
    exact hlt3

/-! ### Factorizations through fixed plank bodies

`Kakeya.PersistentPlankFactorization`, the replacement for `Kakeya.PlankFactorization` used
throughout this file, is declared in `Kakeya/DimensionThree/Plank/Factorization.lean` next to
`PlankFactorization` itself, because GWZ Proposition 6.6(B) is stated there and needs it. -/

namespace Plank

/-- An `a × b × 1` plank contained in a radius-`ρ` tube forces `ρ ≥ 1 / 2`.

This records the longitudinal-scale obstruction in the exact `Plank` model: the plank has
half-length one, whereas a length-one `ρ`-tube lies in a ball of radius `1 / 2 + ρ`. -/
theorem half_le_of_toConvexSpaceBody_le_tube {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : Plank a b hab hb1) (R : Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (h : P.toConvexSpaceBody ≤ R.toConvexSpaceBody) : 1 / 2 ≤ ρ := by
  have hplank : (1 : ℝ≥0∞) ≤ Metric.ethickness ℝ P.carrier 0 := by
    simpa using Prism3D.c_le_ethickness_zero P
  have hsub : P.carrier ⊆ R.carrier := SetLike.coe_subset_coe.mpr h
  have htube : Metric.ethickness ℝ R.carrier 0 ≤ (1 / 2 + ρ : ℝ≥0) := by
    calc
      Metric.ethickness ℝ R.carrier 0 ≤
          Metric.ethickness ℝ
            (Metric.closedBall (midpoint ℝ R.x R.y) (1 / 2 + (ρ : ℝ))) 0 :=
        Metric.ethickness_monotone (Tube.carrier_subset_closedBall_midpoint _ R) 0
      _ ≤ (1 / 2 + ρ : ℝ≥0) := by
        simpa using Metric.ethickness_closedBall_le
          (𝕜 := ℝ) (x := midpoint ℝ R.x R.y) (1 / 2 + ρ) 0
  have hone : (1 : ℝ≥0∞) ≤ (1 / 2 + ρ : ℝ≥0) :=
    hplank.trans ((Metric.ethickness_monotone hsub 0).trans htube)
  have hone' : (1 : ℝ) ≤ 1 / 2 + (ρ : ℝ) := by exact_mod_cast hone
  exact_mod_cast (show (1 / 2 : ℝ) ≤ ρ by linarith)

/-! ### The corner obstruction: a hull of tubes is never an exact plank

`Kakeya.PlankFactorization` asks for `part.convexHull_biUnion V = Q.toConvexSpaceBody`, an
*equality* between the convex hull of a block of inner bodies and an exact `a × b × 1` plank.  The
three lemmas below show that this equality is unsatisfiable as soon as the inner bodies are
`δ`-tubes with `δ > 0` and the block is nonempty — so every statement quantifying over such a
`PlankFactorization` is vacuous.  See `Kakeya.not_plankFactorization_of_tube`.

The argument is elementary and needs no extreme-point theory.  A plank is a box with half-widths
`(a, b, 1)` in its own orthonormal frame.  Every point of a `δ`-tube inside the box is within `δ` of
a point `c` of the tube's core segment, and `closedBall c δ` is inside the box, so `c` misses each
of the three pairs of faces by at least `δ`.  Reading this against the diagonal functional
`⟪e₀ + e₁, ·⟫` costs `2δ` at `c` and buys back at most `√2 δ ≤ 3δ/2` on the way from `c` to the
point, so the functional stays `δ/2` below its maximum on the whole union of tubes — hence, the
sublevel set being convex, on the hull as well.  But the hull is the box, on which the maximum is
attained, at the vertex `center + a e₀ + b e₁ + e₂`.  Contradiction. -/

/-- **A closed ball inside a plank is `δ`-deep in every coordinate.**

If `Metric.closedBall c δ ⊆ Q.carrier` then, in the plank's own orthonormal frame and relative to
its centre, the `j`-th coordinate of `c` misses the `j`-th half-width by at least `δ`.  This is the
only geometric input of `Kakeya.Plank.convexHull_biUnion_ne_of_tube` beyond Pythagoras. -/
theorem abs_repr_add_le_of_closedBall_subset {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (Q : Plank a b hab hb1) {c : EuclideanSpace ℝ (Fin 3)} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : Metric.closedBall c δ ⊆ Q.carrier) (j : Fin 3) :
    |Q.basis.repr (c -ᵥ Q.center) j| + δ ≤ (Q.thicknesses j : ℝ) := by
  let r : ℝ := Q.basis.repr (c -ᵥ Q.center) j
  let s : ℝ := if 0 ≤ r then 1 else -1
  have hs : |s| = 1 := by
    by_cases hr : 0 ≤ r
    · simp [s, hr]
    · simp [s, hr]
  have hsr : |r + s * δ| = |r| + δ := by
    by_cases hr : 0 ≤ r
    · have hs1 : s = 1 := by simp [s, hr]
      rw [hs1, one_mul, abs_of_nonneg (add_nonneg hr hδ), abs_of_nonneg hr]
    · have hneg : r < 0 := lt_of_not_ge hr
      have hsm : s = -1 := by simp [s, hr]
      rw [hsm, show r + -1 * δ = r - δ by ring]
      have hrδ : r - δ < 0 := by linarith
      rw [abs_of_neg hrδ, abs_of_neg hneg]
      ring
  let p : EuclideanSpace ℝ (Fin 3) := c + (s * δ) • Q.basis j
  have hp_mem_ball : p ∈ Metric.closedBall c δ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [show p - c = (s * δ) • Q.basis j by simp [p]]
    rw [norm_smul, Real.norm_eq_abs, abs_mul, hs, abs_of_nonneg hδ, one_mul,
      Q.basis.norm_eq_one j, mul_one]
  have hpblk : p ∈ Q.carrier := h hp_mem_ball
  have hpcar : |Q.basis.repr (p -ᵥ Q.center) j| ≤ (Q.thicknesses j : ℝ) :=
    (Q.mem_carrier_iff p).1 hpblk j
  have hrepr : Q.basis.repr (p -ᵥ Q.center) j = r + s * δ := by
    dsimp [p, r]
    rw [show c + (s * δ) • Q.basis j - Q.center
        = (c - Q.center) + (s * δ) • Q.basis j by abel]
    simp only [map_add, map_smul, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [show Q.basis.repr (Q.basis j) j = 1 by simp]
    simp [mul_one]
  rw [hrepr] at hpcar
  rw [hsr] at hpcar
  simpa [r] using hpcar

/-- **Two coordinates of an orthonormal expansion are dominated by the norm** (Pythagoras in the
frame of the plank).  Used to convert the `δ`-bound on `‖p - c‖` into the diagonal bound
`repr (p - c) 0 + repr (p - c) 1 ≤ 3 δ / 2`. -/
theorem sq_add_sq_repr_le {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (Q : Plank a b hab hb1) (w : EuclideanSpace ℝ (Fin 3)) :
    (Q.basis.repr w 0) ^ 2 + (Q.basis.repr w 1) ^ 2 ≤ ‖w‖ ^ 2 := by
  calc
    (Q.basis.repr w 0) ^ 2 + (Q.basis.repr w 1) ^ 2
        ≤ ∑ i : Fin 3, (Q.basis.repr w i) ^ 2 := by
          rw [Fin.sum_univ_three]
          nlinarith [sq_nonneg (Q.basis.repr w 2)]
    _ = ‖Q.basis.repr w‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq (Q.basis.repr w)).symm
    _ = ‖w‖ ^ 2 := by rw [LinearIsometryEquiv.norm_map]

/-- **A `δ`-tube inside a plank stays `δ / 2` below the plank's diagonal maximum.**

The diagonal functional here is `x ↦ repr (x - centre) 0 + repr (x - centre) 1`, whose maximum over
the plank is `a + b`.  A point of the tube is within `δ` of a core point `c`, and `c` is `δ`-deep by
`Kakeya.Plank.abs_repr_add_le_of_closedBall_subset`, which costs `2 δ`; Pythagoras
(`Kakeya.Plank.sq_add_sq_repr_le`) buys back at most `3 δ / 2` over the last `δ`.  The net `δ / 2`
is the whole obstruction. -/
theorem repr_add_repr_le_of_tube_subset {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (Q : Plank a b hab hb1) (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hT : T.carrier ⊆ Q.carrier) {p : EuclideanSpace ℝ (Fin 3)} (hp : p ∈ T.carrier) :
    Q.basis.repr (p -ᵥ Q.center) 0 + Q.basis.repr (p -ᵥ Q.center) 1
      ≤ (a : ℝ) + (b : ℝ) - (δ : ℝ) / 2 := by
  rw [T.carrier_eq] at hp
  obtain ⟨c, hc, hpc⟩ := Set.mem_iUnion₂.mp hp
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := NNReal.coe_nonneg δ
  have hclInT : Metric.closedBall c (δ : ℝ) ⊆ T.carrier := by
    intro q hq
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr ⟨c, hc, hq⟩
  have hclQ : Metric.closedBall c (δ : ℝ) ⊆ Q.carrier := hclInT.trans hT
  have h0f : |Q.basis.repr (c -ᵥ Q.center) 0| + (δ : ℝ) ≤ (a : ℝ) := by
    simpa [Q.thicknesses_eq] using abs_repr_add_le_of_closedBall_subset Q hδ0 hclQ 0
  have h1f : |Q.basis.repr (c -ᵥ Q.center) 1| + (δ : ℝ) ≤ (b : ℝ) := by
    simpa [Q.thicknesses_eq] using abs_repr_add_le_of_closedBall_subset Q hδ0 hclQ 1
  have hc0 : Q.basis.repr (c -ᵥ Q.center) 0 ≤ (a : ℝ) - (δ : ℝ) := by
    have h' : |Q.basis.repr (c -ᵥ Q.center) 0| ≤ (a : ℝ) - (δ : ℝ) := by
      nlinarith
    exact (le_abs_self _).trans h'
  have hc1 : Q.basis.repr (c -ᵥ Q.center) 1 ≤ (b : ℝ) - (δ : ℝ) := by
    have h' : |Q.basis.repr (c -ᵥ Q.center) 1| ≤ (b : ℝ) - (δ : ℝ) := by
      nlinarith
    exact (le_abs_self _).trans h'
  let r0 : ℝ := Q.basis.repr (p -ᵥ c) 0
  let r1 : ℝ := Q.basis.repr (p -ᵥ c) 1
  have hsq : r0 ^ 2 + r1 ^ 2 ≤ ‖p -ᵥ c‖ ^ 2 := by
    simpa [r0, r1] using sq_add_sq_repr_le Q (p -ᵥ c)
  have hnorm : ‖p -ᵥ c‖ ≤ (δ : ℝ) := by
    have h : dist p c ≤ (δ : ℝ) := Metric.mem_closedBall.mp hpc
    simpa [dist_eq_norm_vsub] using h
  have hsq2 : ‖p -ᵥ c‖ ^ 2 ≤ (δ : ℝ) ^ 2 := by
    have h' : |‖p -ᵥ c‖| ≤ |(δ : ℝ)| := by
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hδ0]
      exact hnorm
    exact (sq_le_sq.mpr h')
  have hrt : (r0 + r1) ^ 2 ≤ (3 / 2 * (δ : ℝ)) ^ 2 := by
    have h12 : (r0 + r1) ^ 2 ≤ 2 * (r0 ^ 2 + r1 ^ 2) := by
      nlinarith [sq_nonneg (r0 - r1)]
    have h23 : 2 * (r0 ^ 2 + r1 ^ 2) ≤ 2 * (δ : ℝ) ^ 2 := by
      have h : r0 ^ 2 + r1 ^ 2 ≤ (δ : ℝ) ^ 2 := hsq.trans hsq2
      nlinarith
    have h34 : 2 * (δ : ℝ) ^ 2 ≤ (3 / 2 * (δ : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (δ : ℝ)]
    nlinarith
  have hrr : r0 + r1 ≤ 3 / 2 * (δ : ℝ) := by
    have hpos : 0 ≤ 3 / 2 * (δ : ℝ) := by positivity
    have h : |r0 + r1| ≤ |3 / 2 * (δ : ℝ)| := (sq_le_sq.mp hrt)
    have h' : |r0 + r1| ≤ 3 / 2 * (δ : ℝ) := by
      rw [abs_of_nonneg hpos] at h
      exact h
    exact (le_abs_self _).trans h'
  have hvec : p -ᵥ Q.center = (c -ᵥ Q.center) + (p -ᵥ c) := by
    rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub]
    abel
  calc
    Q.basis.repr (p -ᵥ Q.center) 0 + Q.basis.repr (p -ᵥ Q.center) 1
        = (Q.basis.repr (c -ᵥ Q.center) 0 + Q.basis.repr (c -ᵥ Q.center) 1) +
            (r0 + r1) := by
          rw [hvec]
          simp only [map_add, WithLp.ofLp_add, Pi.add_apply, r0, r1]
          ring
    _ ≤ ((a : ℝ) - (δ : ℝ)) + ((b : ℝ) - (δ : ℝ)) + (3 / 2 * (δ : ℝ)) := by
      nlinarith
    _ = (a : ℝ) + (b : ℝ) - (δ : ℝ) / 2 := by ring

/-- **The plank attains its diagonal maximum**, at the vertex `centre + a e₀ + b e₁ + e₂`. -/
theorem exists_mem_carrier_repr_add_repr_eq {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (Q : Plank a b hab hb1) :
    ∃ v ∈ Q.carrier,
      Q.basis.repr (v -ᵥ Q.center) 0 + Q.basis.repr (v -ᵥ Q.center) 1 = (a : ℝ) + (b : ℝ) := by
  let v : EuclideanSpace ℝ (Fin 3) :=
    Q.center + ((a : ℝ) • Q.basis 0 + (b : ℝ) • Q.basis 1 + (1 : ℝ) • Q.basis 2)
  have hrepr : ∀ i : Fin 3,
      Q.basis.repr (v -ᵥ Q.center) i =
        (if i = 0 then (a : ℝ) else if i = 1 then (b : ℝ) else (1 : ℝ)) := by
    intro i
    dsimp [v]
    rw [add_sub_cancel_left]
    simp only [map_add, map_smul, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    fin_cases i <;> simp
  refine ⟨v, ?_, ?_⟩
  · rw [Q.mem_carrier_iff]
    intro i
    rw [hrepr i, Q.thicknesses_eq]
    fin_cases i <;> simp [abs_of_nonneg]
  · rw [hrepr 0, hrepr 1]
    simp

/-- **The convex hull of a nonempty family of positive-radius tubes is never an exact plank.**

This is the obstruction that makes `Kakeya.PlankFactorization` unsatisfiable over tube families;
see the section comment above for the proof and `Kakeya.not_plankFactorization_of_tube` for the
consequence.  No relation between `δ` and `a, b` is assumed: the depth bound derived from a single
core point already forces `δ ≤ a`, so the degenerate regime `a < δ` is covered too. -/
theorem convexHull_biUnion_ne_of_tube {ι : Type*} {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (hδ : 0 < δ) {t : Finset ι} (ht : t.Nonempty)
    (V : ι → Tube δ (EuclideanSpace ℝ (Fin 3))) (Q : Plank a b hab hb1) :
    t.convexHull_biUnion (fun i => (V i).toConvexSpaceBody) ≠ Q.toConvexSpaceBody := by
  intro heq
  let f : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => Q.basis.repr x 0 + Q.basis.repr x 1
  have hlin : IsLinearMap ℝ f := by
    constructor
    · intro x y
      simp only [f, map_add, WithLp.ofLp_add, Pi.add_apply]
      ring
    · intro c x
      simp only [f, map_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      ring
  let K : ℝ := (a : ℝ) + (b : ℝ) - (δ : ℝ) / 2 + f Q.center
  let B : Set (EuclideanSpace ℝ (Fin 3)) := {x | f x ≤ K}
  have hB : Convexity.IsConvexSet ℝ B := by
    simpa [B] using (convex_halfSpace_le hlin K).isConvexSet
  have hbridge : ∀ x : EuclideanSpace ℝ (Fin 3),
      f x - f Q.center = Q.basis.repr (x -ᵥ Q.center) 0 + Q.basis.repr (x -ᵥ Q.center) 1 := by
    intro x
    dsimp [f]
    simp only [map_sub, WithLp.ofLp_sub, Pi.sub_apply]
    ring
  have hB_iff : ∀ x : EuclideanSpace ℝ (Fin 3),
      x ∈ B ↔ Q.basis.repr (x -ᵥ Q.center) 0 + Q.basis.repr (x -ᵥ Q.center) 1
        ≤ (a : ℝ) + (b : ℝ) - (δ : ℝ) / 2 := by
    intro x
    constructor
    · intro hx
      have hle : f x - f Q.center ≤ (a : ℝ) + (b : ℝ) - (δ : ℝ) / 2 := by
        dsimp [B, K] at hx
        linarith
      rwa [hbridge x] at hle
    · intro hx
      dsimp [B, K]
      have hle : f x - f Q.center ≤ (a : ℝ) + (b : ℝ) - (δ : ℝ) / 2 := by
        rwa [hbridge x]
      linarith
  have hV_le_B : ∀ i ∈ t, ((V i).toConvexSpaceBody).carrier ⊆ B := by
    intro i hi p hp
    have hV_le_hull : (V i).toConvexSpaceBody ≤
        t.convexHull_biUnion (fun i => (V i).toConvexSpaceBody) :=
      Finset.le_convexHull_biUnion (fun i => (V i).toConvexSpaceBody) hi
    have hV_le_Q : (V i).toConvexSpaceBody ≤ Q.toConvexSpaceBody := by
      rwa [heq] at hV_le_hull
    have hVQ : (V i).carrier ⊆ Q.carrier := by
      intro q hq
      exact hV_le_Q hq
    have hle : Q.basis.repr (p -ᵥ Q.center) 0 + Q.basis.repr (p -ᵥ Q.center) 1
        ≤ (a : ℝ) + (b : ℝ) - (δ : ℝ) / 2 :=
      repr_add_repr_le_of_tube_subset Q (V i) hVQ hp
    exact (hB_iff p).2 hle
  have hhull : (t.convexHull_biUnion (fun i => (V i).toConvexSpaceBody)).carrier ⊆ B :=
    (ht.convexHull_biUnion_subset_iff (fun i => (V i).toConvexSpaceBody) hB).2 hV_le_B
  have hQsubB : Q.carrier ⊆ B := by
    intro q hq
    have hq' : q ∈ (t.convexHull_biUnion (fun i => (V i).toConvexSpaceBody)).carrier := by
      rw [heq]
      exact hq
    exact hhull hq'
  obtain ⟨v, hvQ, hvEq⟩ := exists_mem_carrier_repr_add_repr_eq Q
  have hvB : v ∈ B := hQsubB hvQ
  have hle : (a : ℝ) + (b : ℝ) ≤ (a : ℝ) + (b : ℝ) - (δ : ℝ) / 2 := by
    rw [hB_iff v] at hvB
    rwa [hvEq] at hvB
  have hδle0 : (δ : ℝ) ≤ 0 := by linarith
  exact (not_le_of_gt (NNReal.coe_pos.mpr hδ)) hδle0

end Plank

/-- **`Kakeya.PlankFactorization` is uninhabited on a nonempty family of positive-radius tubes.**

A `PlankFactorization` extends a `Finpartition` of `s`, whose parts are nonempty and cover `s`, and
requires the convex hull of each part to *equal* an `a × b × 1` plank.  By
`Kakeya.Plank.convexHull_biUnion_ne_of_tube` no such equality can hold for `δ`-tubes with `δ > 0`,
so a nonempty `s` admits no `PlankFactorization` at all, at any constant and any `a ≤ b ≤ 1`.

**This is the recorded vacuity.**  Every statement of the form "for all
`PlankFactorization … (fun i => (V i).toConvexSpaceBody) …`, `P`" whose ambient hypotheses force the
tube radius positive and the index set nonempty is vacuously true and establishes nothing about `P`.
Two statements in this development were of exactly that shape and have been restated over
`Kakeya.PersistentPlankFactorization` instead: `Kakeya.exists_relativePlankSelection` and
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` (GWZ 6.6(B)).  `PersistentPlankFactorization`
carries the outer bodies as free data on a `ConvexSpaceBody.FactorFamily` rather than as hulls of
the inner blocks, which is what removes the obstruction. -/
theorem not_plankFactorization_of_tube {ι : Type*} [DecidableEq ι] {δ a b : ℝ≥0}
    {hab : a ≤ b} {hb1 : b ≤ 1} (hδ : 0 < δ) {s : Finset ι} (hs : s.Nonempty)
    (V : ι → Tube δ (EuclideanSpace ℝ (Fin 3))) (C₀ : ℝ≥0) :
    IsEmpty (PlankFactorization a b hab hb1 s (fun i => (V i).toConvexSpaceBody) C₀) := by
  refine ⟨fun F => ?_⟩
  have hparts : F.parts.Nonempty := F.parts_nonempty (by
    simpa using (Finset.nonempty_iff_ne_empty.mp hs))
  rcases hparts with ⟨part, hpart⟩
  have hpartne : part.Nonempty := F.nonempty_of_mem_parts hpart
  rcases F.parts_are_planks part hpart with ⟨Q, hQ⟩
  exact (Plank.convexHull_biUnion_ne_of_tube hδ hpartne V Q) hQ

/-- **The shaded reading of `Kakeya.not_plankFactorization_of_tube`**, which is the form the
consumers of GWZ Proposition 6.6 present: their inner family is a family of `ShadedTube`s, whose
underlying convex body is that of the tube it bundles. -/
theorem not_plankFactorization_of_shadedTube {ι : Type*} [DecidableEq ι] {δ a b : ℝ≥0}
    {hab : a ≤ b} {hb1 : b ≤ 1} (hδ : 0 < δ) {s : Finset ι} (hs : s.Nonempty)
    (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (C₀ : ℝ≥0) :
    IsEmpty (PlankFactorization a b hab hb1 s (fun i => (V i).toConvexSpaceBody) C₀) := by
  simpa using not_plankFactorization_of_tube (a := a) (b := b) (hab := hab) (hb1 := hb1)
    hδ hs (fun i => (V i).toTube) C₀

open Classical in
/-- **The parents actually used form a subfamily of the outer family.**  This is the inclusion that
turns each clause of a factorization, stated over the whole outer index set, into the corresponding
clause of `Kakeya.PersistentPlankFactorization`, stated over the parents attained on the inner
set. -/
theorem image_parent_subset_outerSet {ι ω : Type*}
    (F : ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι ω) :
    F.innerSet.image F.parent ⊆ F.outerSet := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact F.parent_mem i hi

/-- **Every plank factorization is persistent**, with the same constant: the block outer bodies of
a `Kakeya.PlankFactorization` are planks by `parts_are_planks`, and the two remaining clauses are
`isKatzTao` and `maxDensity_le_mul` read on the underlying factor family. -/
theorem PlankFactorization.toPersistent {ι : Type*} [DecidableEq ι] {a b : ℝ≥0} {hab : a ≤ b}
    {hb1 : b ≤ 1} {s : Finset ι} {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {C₀ : ℝ≥0}
    (F : PlankFactorization a b hab hb1 s V C₀) :
    PersistentPlankFactorization F.toFactorization.toFactorFamily a b hab hb1 C₀ := by
  classical
  refine ⟨?_, F.toFactorization.toFactorFamily_isKatzTao.subset
    (image_parent_subset_outerSet _), ?_⟩
  · intro j hj
    exact F.parts_are_planks j (image_parent_subset_outerSet _ hj)
  · intro j hj
    exact F.toFactorization.toFactorFamily_maxDensity_le_mul j
      (image_parent_subset_outerSet _ hj)

open Classical in
/-- **The fibres of a restricted factor family**: restricting the inner set to `s'` intersects
every fibre with `s'`, the parent map being untouched by `ConvexSpaceBody.FactorFamily.ofSubset`. -/
theorem fiber_ofSubset_eq_inter {ι ω : Type*}
    (F : ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι ω)
    {s' : Finset ι} (hs' : s' ⊆ F.innerSet) (j : ω) :
    (F.ofSubset hs').fiber j = F.fiber j ∩ s' := by
  ext i
  simp only [ConvexSpaceBody.FactorFamily.fiber, Finset.mem_filter, Finset.mem_inter,
    ConvexSpaceBody.FactorFamily.ofSubset]
  constructor
  · rintro ⟨hi, hp⟩
    exact ⟨⟨hs' hi, hp⟩, hi⟩
  · rintro ⟨⟨_, hp⟩, hi⟩
    exact ⟨hi, hp⟩

open Classical in
/-- **The volume share retained by a restricted fibre.**

This is the step converting a *cardinality* retention into a *volume* retention.  If the retained
part of the fibre over `j` is a `1 / A` fraction of that fibre, and all inner bodies of the family
have volume comparable up to `Cvol`, then the retained part still carries a `1 / (A * Cvol)` share
of the fibre's total inner volume.  Both hypotheses are needed: cardinality alone says nothing about
volume, and volume comparability alone says nothing about how many members were kept. -/
theorem sum_volume_fiber_le_mul_sum_volume_inter {ι ω : Type*}
    {F : ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι ω}
    {A Cvol : ℝ≥0} {s' : Finset ι} (hs' : s' ⊆ F.innerSet) {j : ω}
    (hj : j ∈ s'.image F.parent)
    (hA : ((F.fiber j).card : ℝ≥0) ≤ A * (((F.fiber j) ∩ s').card : ℝ≥0))
    (hvol : ∀ i ∈ F.innerSet, ∀ i' ∈ F.innerSet,
      volume (F.innerBody i).carrier ≤ (Cvol : ℝ≥0∞) * volume (F.innerBody i').carrier) :
    ∑ i ∈ F.fiber j, volume (F.innerBody i).carrier ≤
      ((A * Cvol : ℝ≥0) : ℝ≥0∞) * ∑ i ∈ F.fiber j ∩ s', volume (F.innerBody i).carrier := by
  let t := F.fiber j ∩ s'
  have ht : t.Nonempty := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    refine ⟨i, ?_⟩
    simp only [t, Finset.mem_inter, ConvexSpaceBody.FactorFamily.fiber,
      Finset.mem_filter]
    exact ⟨⟨hs' hi, trivial⟩, hi⟩
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image t
    (fun i ↦ volume (F.innerBody i).carrier) ht
  have hi₀inner : i₀ ∈ F.innerSet := by
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hi₀).1).1
  have hupper : ∑ i ∈ F.fiber j, volume (F.innerBody i).carrier ≤
      ((F.fiber j).card : ℝ≥0∞) *
        ((Cvol : ℝ≥0∞) * volume (F.innerBody i₀).carrier) := by
    simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul (F.fiber j)
      (fun i ↦ volume (F.innerBody i).carrier)
      ((Cvol : ℝ≥0∞) * volume (F.innerBody i₀).carrier) fun i hi ↦
        hvol i (Finset.mem_filter.mp hi).1 i₀ hi₀inner
  have hcard : ((F.fiber j).card : ℝ≥0∞) ≤
      (A : ℝ≥0∞) * (t.card : ℝ≥0∞) := by
    exact_mod_cast hA
  have hlower : (t.card : ℝ≥0∞) * volume (F.innerBody i₀).carrier ≤
      ∑ i ∈ t, volume (F.innerBody i).carrier := by
    simpa only [nsmul_eq_mul] using Finset.card_nsmul_le_sum t
      (fun i ↦ volume (F.innerBody i).carrier) (volume (F.innerBody i₀).carrier)
      fun i hi ↦ hmin i hi
  calc
    ∑ i ∈ F.fiber j, volume (F.innerBody i).carrier
        ≤ ((F.fiber j).card : ℝ≥0∞) *
            ((Cvol : ℝ≥0∞) * volume (F.innerBody i₀).carrier) := hupper
    _ ≤ ((A : ℝ≥0∞) * (t.card : ℝ≥0∞)) *
          ((Cvol : ℝ≥0∞) * volume (F.innerBody i₀).carrier) := by gcongr
    _ = ((A * Cvol : ℝ≥0) : ℝ≥0∞) *
          ((t.card : ℝ≥0∞) * volume (F.innerBody i₀).carrier) := by
      push_cast
      ac_rfl
    _ ≤ ((A * Cvol : ℝ≥0) : ℝ≥0∞) *
          ∑ i ∈ t, volume (F.innerBody i).carrier := by gcongr
    _ = ((A * Cvol : ℝ≥0) : ℝ≥0∞) *
          ∑ i ∈ F.fiber j ∩ s', volume (F.innerBody i).carrier := by rfl

open Classical in
/-- **The density share retained by a restricted fibre**, the reading of
`Kakeya.sum_volume_fiber_le_mul_sum_volume_inter` in terms of `Kakeya.densityIn`.  The outer body
`F.outerBody j` is the *same* body on both sides, which is what makes this a statement about
densities at all: only the numerator moves. -/
theorem densityIn_fiber_le_mul_densityIn_inter {ι ω : Type*}
    {F : ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι ω}
    {A Cvol : ℝ≥0} {s' : Finset ι} (hs' : s' ⊆ F.innerSet) {j : ω}
    (hj : j ∈ s'.image F.parent)
    (hA : ((F.fiber j).card : ℝ≥0) ≤ A * (((F.fiber j) ∩ s').card : ℝ≥0))
    (hvol : ∀ i ∈ F.innerSet, ∀ i' ∈ F.innerSet,
      volume (F.innerBody i).carrier ≤ (Cvol : ℝ≥0∞) * volume (F.innerBody i').carrier) :
    densityIn (F.fiber j) F.innerBody (F.outerBody j) ≤
      ((A * Cvol : ℝ≥0) : ℝ≥0∞) *
        densityIn (F.fiber j ∩ s') F.innerBody (F.outerBody j) := by
  apply densityIn_le_of_sum_le
  rw [Finset.filter_eq_self.mpr, Finset.filter_eq_self.mpr]
  · exact sum_volume_fiber_le_mul_sum_volume_inter hs' hj hA hvol
  · intro i hi
    have hifiber := (Finset.mem_inter.mp hi).1
    obtain ⟨hiinner, hiparent⟩ := Finset.mem_filter.mp hifiber
    simpa only [hiparent] using F.inner_le_parent i hiinner
  · intro i hi
    obtain ⟨hiinner, hiparent⟩ := Finset.mem_filter.mp hi
    simpa only [hiparent] using F.inner_le_parent i hiinner

open Classical in
/-- **Restricting a persistent plank factorization to a subfamily, with the outer bodies fixed.**

This is the step at which a *cardinality* retention is converted into a *density* lower bound: the
retained fibre of a block is a fraction `1 / A` of the original fibre, and all inner bodies have
comparable volume (constant `Cvol`), so the retained block still fills its unchanged outer body to
within `A * Cvol`.  Nothing is claimed about the convex hull of the retained fibre, which is exactly
the clause `Kakeya.PlankFactorization` could not keep.

The hypothesis `1 ≤ A * Cvol` is needed, and only, for the Katz--Tao clause: that clause is an
upper bound on the *outer* family, which is unchanged here, so it descends with the *old* constant
`C₀` and has to be weakened to `C₀ * A * Cvol` by monotonicity in the constant.  Without it the
statement is false, `A = 1` and `Cvol = 0` being admissible when every inner body is degenerate
while the outer planks are not. -/
theorem PersistentPlankFactorization.ofSubset {ι ω : Type*}
    {F : ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι ω}
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {C₀ A Cvol : ℝ≥0}
    (hF : PersistentPlankFactorization F a b hab hb1 C₀) (hAvol : 1 ≤ A * Cvol)
    {s' : Finset ι} (hs' : s' ⊆ F.innerSet)
    (hA : ∀ j ∈ s'.image F.parent,
      ((F.fiber j).card : ℝ≥0) ≤ A * (((F.fiber j) ∩ s').card : ℝ≥0))
    (hvol : ∀ i ∈ F.innerSet, ∀ i' ∈ F.innerSet,
      volume (F.innerBody i).carrier ≤ (Cvol : ℝ≥0∞) * volume (F.innerBody i').carrier) :
    PersistentPlankFactorization (F.ofSubset hs') a b hab hb1 (C₀ * A * Cvol) := by
  have hparents : (F.ofSubset hs').innerSet.image (F.ofSubset hs').parent ⊆
      F.innerSet.image F.parent := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_image.mpr ⟨i, hs' hi, rfl⟩
  have hconst : (C₀ : ℝ≥0∞) ≤ ((C₀ * A * Cvol : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast (show C₀ ≤ C₀ * A * Cvol from calc
      C₀ = C₀ * 1 := (mul_one C₀).symm
      _ ≤ C₀ * (A * Cvol) := mul_le_mul_right hAvol C₀
      _ = C₀ * A * Cvol := by ac_rfl)
  refine ⟨?_, (hF.outer_isKatzTao.subset hparents).mono hconst, ?_⟩
  · intro j hj
    simpa only [ConvexSpaceBody.FactorFamily.ofSubset] using hF.outer_are_planks j (hparents hj)
  · intro j hj
    have hj' : j ∈ s'.image F.parent := by
      simpa only [ConvexSpaceBody.FactorFamily.ofSubset] using hj
    have hdensity := densityIn_fiber_le_mul_densityIn_inter hs' hj' (hA j hj') hvol
    change maxDensity s' F.innerBody ≤
      ((C₀ * A * Cvol : ℝ≥0) : ℝ≥0∞) *
        densityIn ((F.ofSubset hs').fiber j) F.innerBody (F.outerBody j)
    rw [fiber_ofSubset_eq_inter F hs' j]
    calc
      maxDensity s' F.innerBody ≤ maxDensity F.innerSet F.innerBody :=
        maxDensity_mono F.innerBody hs'
      _ ≤ (C₀ : ℝ≥0∞) * densityIn (F.fiber j) F.innerBody (F.outerBody j) :=
        hF.maxDensity_le_mul j (hparents hj)
      _ ≤ (C₀ : ℝ≥0∞) * (((A * Cvol : ℝ≥0) : ℝ≥0∞) *
          densityIn (F.fiber j ∩ s') F.innerBody (F.outerBody j)) := by gcongr
      _ = ((C₀ * A * Cvol : ℝ≥0) : ℝ≥0∞) *
          densityIn (F.fiber j ∩ s') F.innerBody (F.outerBody j) := by
        push_cast
        ac_rfl

/-! ### The joint selection -/

open Classical in
/-- **The output of the joint grid/plank regularization.**

One retained subfamily `kept`, one refined shading, and *one* pair `(a, b)` carrying, at the same
time, the multiscale shaded uniformity of GWZ Definition 2.2 on `kept` and a persistent plank
factorization of each retained plank block.

`activeParents = kept.image assign` is stated as an equation rather than as three separate clauses:
it already says that every retained tube lies in a retained parent, that every retained parent is
actually used, and that a plank block emptied by the cleaning disappears from the outer family.

## A removed clause, and why it had to go

This structure used to carry a further field

    factorFamily_outer_le_parent : ∀ k ∈ activeParents,
      ∀ j ∈ (factorFamily k).innerSet.image (factorFamily k).parent,
        (factorFamily k).outerBody j ≤ (R k).toConvexSpaceBody

"every active outer plank remains inside the coarse tube of its block".  **That clause makes the
structure uninhabited whenever `kept ≠ ∅` and `0 < ρ ≤ a`**, which is exactly the regime the only
consumer `Kakeya.multiplicity_le_of_relativePlankSelection` runs in, so keeping it would have
replaced one vacuity by another.  It had no consumer: no field of the structure and no downstream
theorem, in particular not `Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation`, ever read
it.

The obstruction, in two steps.  `persistentFactorization` makes the outer body an exact
`a × b × 1` plank, so the removed clause asserts `plank ⊆ ρ-tube`.

* Along the plank's long axis the plank has extent `2` while a `ρ`-tube of core length one has
  extent at most `1 + 2 ρ`, so `1 / 2 ≤ ρ`.  This half is proved:
  `Kakeya.half_le_of_persistentPlankFactorization` below, via
  `Kakeya.Plank.half_le_of_toConvexSpaceBody_le_tube`.
* Transversally to the tube's core the tube has width exactly `2 ρ`, while the plank's transverse
  cross-section is a `2 a × 2 b` rectangle, whose width in the diagonal direction is
  `√2 · min a b` at least.  With `ρ ≤ a ≤ b` this gives `b ≤ ρ ≤ a ≤ b`, hence `a = b = ρ`, and
  then the diagonal direction gives `ρ √2 ≤ ρ`, i.e. `ρ = 0`.  This half is *not* formalized; it is
  recorded here as the reason the clause is gone, not as a Lean fact.

The mathematical content the clause was trying to express — that the planks are attached to the
coarse tube `R k` — is not available at `ρ ≤ a`, because there the planks are *fatter* than the
coarse tube.  It is carried instead by `activeParents_eq` together with the caller's own
`(V i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody`, which is a statement about the fine
tubes and is satisfiable. -/
structure RelativePlankSelection {ι κ : Type*} {δ ρ a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
    (s q : Finset ι) (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (assign : ι → κ)
    (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (r : Finset κ) (M : ℕ) (uniformConst factorConst : ℝ≥0) (totalLoss : ℕ) where
  /-- The retained subfamily. -/
  kept : Finset ι
  /-- The retained subfamily is a subfamily. -/
  kept_subset : kept ⊆ s
  /-- Every retained tube belongs to the plank-selected input family. -/
  kept_subset_plank : kept ⊆ q
  /-- The refined shading.  Only the shades move; see `sameTube`. -/
  shading : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))
  /-- The underlying tubes are untouched, so all geometry proved before the selection survives. -/
  sameTube : ∀ i, (shading i).toTube = (V i).toTube
  /-- The refined shades are contained in the original ones. -/
  shade_subset : ∀ i, (shading i).shade ⊆ (V i).shade
  /-- The plank blocks still carrying a retained tube. -/
  activeParents : Finset κ
  /-- The active blocks are exactly the blocks of the retained tubes. -/
  activeParents_eq : activeParents = kept.image assign
  /-- The active blocks come from the original block family. -/
  activeParents_subset : activeParents ⊆ r
  /-- The retained family, with its refined shading, is shaded-uniform at every grid level. -/
  shadedUniform : ShadedTube.ShadedUniformTubeSet kept shading M uniformConst
  /-- The factor family of each block: outer bodies fixed, fibre restricted to `kept`. -/
  factorFamily : κ → ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι (Finset ι)
  /-- Its inner set is the retained part of the block. -/
  factorFamily_innerSet : ∀ k ∈ activeParents,
    (factorFamily k).innerSet = {i ∈ kept | assign i = k}
  /-- Its inner bodies are the original tubes. -/
  factorFamily_innerBody : ∀ k, (factorFamily k).innerBody = fun i => (V i).toConvexSpaceBody
  /-- Each active block is still a plank factorization in the persistent sense. -/
  persistentFactorization : ∀ k ∈ activeParents,
    PersistentPlankFactorization (factorFamily k) a b hab hb1 factorConst
  /-- The retained family is a definite fraction of the original one. -/
  card_retention : s.card ≤ totalLoss * kept.card
  /-- So is the retained shade mass. -/
  shading_mass_retention : ∑ i ∈ s, volume (V i).shade ≤
    (totalLoss : ℝ≥0∞) * ∑ i ∈ kept, volume (shading i).shade

open Classical in
/-- **The joint grid/plank regularization.**

Both inputs are already available: `𝒰` is the multiscale uniformization of the full family, and
`q`, `r`, `R`, `F`, `Fz` are the output of the plank pigeonhole at the global pair `(a, b)`, heavy
in `s` with loss `Lp`.  The conclusion is a single family that is simultaneously shaded-uniform at
all `M + 1` grid levels and plank-factored at that same `(a, b)`.

The uniformity constant is `max (relativePlankBandRestrictConst Cu (relativePlankBandRatio s.card M)) 4`: the
band restriction supplies the first argument and the shaded uniformization weakens `C` to
`max C 4`.  The factor constant picks up the band ratio (fibre retention) and `Cvol` (volume
comparability), by `Kakeya.PersistentPlankFactorization.ofSubset`.

## Why the plank hypothesis is `PersistentPlankFactorization` and not `PlankFactorization`

**This statement previously took `Fz : ∀ k ∈ r, PlankFactorization a b hab hb1
{i ∈ q | assign i = k} (fun i => (V i).toConvexSpaceBody) C₀`, and in that form it was
vacuous.**  A `PlankFactorization`
requires the convex hull of each block to *equal* an exact `a × b × 1` plank, and by
`Kakeya.not_plankFactorization_of_shadedTube` no such object exists over a nonempty family of
`δ`-tubes with `δ > 0` — which is the only regime the consumer
`Kakeya.multiplicity_le_of_relativePlankSelection` runs in, since it assumes `0 < δ ≤ ρ ≤ a`.  So
the old hypothesis forced `q = ∅`, and the retention clause `s.card ≤ Lp * q.card` then forced
`s = ∅`: the theorem was proved, and said nothing.

The plank data is now supplied the way the downstream proposition
`Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation` already consumes it: as a family `F` of
`ConvexSpaceBody.FactorFamily`s whose outer bodies are *free data* required only to be planks
(`Kakeya.PersistentPlankFactorization`), plus the three bookkeeping clauses tying `F` to `q`, `V`
and `R`.  The proof body is unchanged in substance — the joint regularization never looked at the
hull equality, only at the parent map, the inner set, the inner bodies and the three persistent
clauses.

The output structure lost the field `factorFamily_outer_le_parent` in the same change, because with
free outer bodies that field is an assertion `plank ⊆ ρ-tube` which is unsatisfiable at `ρ ≤ a`;
see the docstring of `Kakeya.RelativePlankSelection` and the proved half
`Kakeya.half_le_of_persistentPlankFactorization`.  Nothing downstream read it, so no hypothesis of
this theorem has to supply it. -/
theorem exists_relativePlankSelection {ι κ : Type*} {δ ρ a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
    {M : ℕ} (hM : 0 < M) {s q : Finset ι} (hq : q ⊆ s) {Cu C₀ Cvol : ℝ≥0}
    (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (𝒰 : Tube.UniformTubeSet s (fun i => (V i).toTube) M Cu)
    (assign : ι → κ) (r : Finset κ) (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (hparent : ∀ i ∈ q, assign i ∈ r ∧
      (V i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody)
    (F : κ → ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι (Finset ι))
    (hFinner : ∀ k ∈ r, (F k).innerSet = {i ∈ q | assign i = k})
    (hFbody : ∀ k ∈ r, (F k).innerBody = fun i => (V i).toConvexSpaceBody)
    (Fz : ∀ k ∈ r, PersistentPlankFactorization (F k) a b hab hb1 C₀)
    (Lp : ℕ) (hplankHeavy : s.card ≤ Lp * q.card)
    (hCvol : 1 ≤ Cvol)
    (hvol : ∀ i ∈ s, ∀ i' ∈ s, volume (V i).carrier ≤ (Cvol : ℝ≥0∞) * volume (V i').carrier)
    (hshadeComp : ∀ i ∈ s, ∀ i' ∈ s, volume (V i).shade ≤ 2 * volume (V i').shade) :
    Nonempty (RelativePlankSelection hab hb1 s q V assign R r M
      (max (MultiScaleFac.relativePlankBandRestrictConst Cu
        ((relativePlankBandRatio s.card M : ℕ) : ℝ≥0)) 4)
      (C₀ * ((relativePlankBandRatio s.card M : ℕ) : ℝ≥0) * Cvol)
      (2 * Lp * relativePlankTotalLoss s.card M)) := by
  letI : DecidableEq (Finset ι) := Classical.decEq _
  let emptyF : ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι (Finset ι) :=
    { innerSet := ∅
      innerBody := fun i ↦ (V i).toConvexSpaceBody
      outerSet := ∅
      outerBody := fun _ ↦ ConvexSpaceBody.closedUnitBall
      parent := fun _ ↦ ∅
      parent_mem := by simp
      inner_le_parent := by simp }
  let base : κ → ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι (Finset ι) :=
    fun k ↦ if hk : k ∈ r then F k else emptyF
  have hbase_inner : ∀ k ∈ r, (base k).innerSet = {i ∈ q | assign i = k} := by
    intro k hk
    simp only [base, hk, ↓reduceDIte]
    exact hFinner k hk
  have hbase_body : ∀ k ∈ r, (base k).innerBody = fun i => (V i).toConvexSpaceBody := by
    intro k hk
    simp only [base, hk, ↓reduceDIte]
    exact hFbody k hk
  have hbase_persistent : ∀ k ∈ r, PersistentPlankFactorization (base k) a b hab hb1 C₀ := by
    intro k hk
    simp only [base, hk, ↓reduceDIte]
    exact Fz k hk
  let plankPart : ι → Finset ι := fun i ↦ (base (assign i)).parent i
  let f : Fin (M + 2) → ι → Sum (κ × Finset ι) ι := fun p i ↦
    if p.1 = 0 then Sum.inl (assign i, plankPart i)
    else Sum.inr (𝒰.cover.assign (p.1 - 1) i)
  obtain ⟨kept, hkeptq, N, hcard, hband, hprotected⟩ :=
    exists_jointPartitionRegularization q M f
  have hkepts : kept ⊆ s := hkeptq.trans hq
  have hbucket : relativePlankBucket q.card ≤ relativePlankBucket s.card := by
    exact Nat.add_le_add_right (Nat.log_mono_right (Finset.card_le_card hq)) 1
  have hbandRatio : relativePlankBandRatio q.card M ≤ relativePlankBandRatio s.card M := by
    simp only [relativePlankBandRatio, relativePlankThreshold, relativePlankRounds]
    exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (4 * (M + 2))
      (Nat.pow_le_pow_left hbucket _))
  have hjointLoss : relativePlankJointLoss q.card M ≤ relativePlankJointLoss s.card M := by
    simp only [relativePlankJointLoss, relativePlankRounds]
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hbucket _)
  let A : ℝ≥0 := ((relativePlankBandRatio s.card M : ℕ) : ℝ≥0)
  let C : ℝ≥0 := MultiScaleFac.relativePlankBandRestrictConst Cu A
  let branch : ℕ → ℝ≥0 := fun k ↦ if hk : k ≤ M then (N ⟨k + 1, by omega⟩ : ℕ) else 1
  have hgridBand : ∀ k ≤ M, ∀ j ∈ kept.image (𝒰.cover.assign k),
      branch k ≤ ((Tube.coverClass kept (𝒰.cover.assign k) j).card : ℝ≥0) ∧
        ((Tube.coverClass kept (𝒰.cover.assign k) j).card : ℝ≥0) ≤ A * branch k := by
    intro k hk j hj
    let p : Fin (M + 2) := ⟨k + 1, by omega⟩
    have hjf : Sum.inr j ∈ kept.image (f p) := by
      obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
      refine Finset.mem_image.mpr ⟨i, hi, ?_⟩
      have hp0 : p.1 ≠ 0 := by simp [p]
      have hpred : p.1 - 1 = k := by simp [p]
      simp only [f, hp0, ↓reduceIte, hpred]
      exact congrArg Sum.inr hij
    have hb := hband p (Sum.inr j) hjf
    have hclass : {i ∈ kept | f p i = Sum.inr j} =
        Tube.coverClass kept (𝒰.cover.assign k) j := by
      ext i
      simp [f, p, Tube.coverClass]
    have hbranch : branch k = ((N p : ℕ) : ℝ≥0) := by simp [branch, hk, p]
    rw [← hclass]
    rw [hbranch]
    dsimp only [A]
    constructor
    · exact_mod_cast hb.1
    · exact_mod_cast hb.2.trans (Nat.mul_le_mul_right (N p) hbandRatio)
  obtain ⟨𝒰', _, _, _, _⟩ := MultiScaleFac.exists_restrict_uniformTubeSet_band 𝒰 hkepts
    MultiScaleFac.le_relativePlankBandRestrictConst MultiScaleFac.band_le_relativePlankBandRestrictConst
    MultiScaleFac.one_le_relativePlankBandRestrictConst branch hgridBand
  obtain ⟨V', hV'tube, hV'shade, hfull, 𝒱, _, _, _, _⟩ :=
    ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet 𝒰' hM
      (Nat.log 2 s.card) (fun t ht ↦ Nat.log_mono_right
        (Finset.card_le_card (ht.trans hkepts)))
  let fibre : κ → Finset ι := fun k ↦ {i ∈ kept | assign i = k}
  have hfibre_base : ∀ k, fibre k ⊆ (base k).innerSet := by
    intro k i hi
    obtain ⟨hikept, hiassign⟩ := Finset.mem_filter.mp hi
    have hiq : i ∈ q := hkeptq hikept
    have hkr : k ∈ r := by simpa only [← hiassign] using (hparent i hiq).1
    rw [hbase_inner k hkr]
    exact Finset.mem_filter.mpr ⟨hiq, hiassign⟩
  let FF : κ → ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι (Finset ι) :=
    fun k ↦ (base k).ofSubset (hfibre_base k)
  have hactive : kept.image assign ⊆ r := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact (hparent i (hkeptq hi)).1
  have hratio : ∀ k ∈ kept.image assign, ∀ j ∈ (FF k).innerSet.image (FF k).parent,
      (((base k).fiber j).card : ℝ≥0) ≤ A * ((((base k).fiber j) ∩ fibre k).card : ℝ≥0) := by
    intro k hk j hj
    have hkr : k ∈ r := hactive hk
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
    have hifibre : i ∈ fibre k := by
      simpa only [FF, ConvexSpaceBody.FactorFamily.ofSubset] using hi
    obtain ⟨hikept, hiassign⟩ := Finset.mem_filter.mp hifibre
    have hiq : i ∈ q := hkeptq hikept
    have hparent_eq : (base k).parent i = j := by
      simpa only [FF, ConvexSpaceBody.FactorFamily.ofSubset] using hij
    have hpart : plankPart i = j := by
      simpa only [plankPart, hiassign] using hparent_eq
    have hf0 : ∀ x, f 0 x = Sum.inl (assign x, plankPart x) := by
      intro x
      simp [f]
    have hjlabel : Sum.inl (k, j) ∈ kept.image (f 0) := by
      refine Finset.mem_image.mpr ⟨i, hikept, ?_⟩
      rw [hf0]
      exact congrArg Sum.inl (Prod.ext hiassign hpart)
    have hclass : {i ∈ q | f 0 i = Sum.inl (k, j)} = (base k).fiber j := by
      ext x
      simp only [Finset.mem_filter, ConvexSpaceBody.FactorFamily.fiber]
      constructor
      · intro hx
        obtain ⟨hxq, hxlabel⟩ := hx
        have hxpair : (assign x, plankPart x) = (k, j) := by
          rw [hf0] at hxlabel
          exact Sum.inl.inj hxlabel
        have hxassign : assign x = k := congrArg Prod.fst hxpair
        have hxpart : plankPart x = j := congrArg Prod.snd hxpair
        have hxparent : (base k).parent x = j := by
          simpa only [plankPart, hxassign] using hxpart
        exact ⟨by
          rw [hbase_inner k hkr]
          exact Finset.mem_filter.mpr ⟨hxq, hxassign⟩, hxparent⟩
      · intro hx
        obtain ⟨hxinner, hxparent⟩ := hx
        have hxqassign : x ∈ q ∧ assign x = k := by
          rw [hbase_inner k hkr] at hxinner
          exact Finset.mem_filter.mp hxinner
        refine ⟨hxqassign.1, ?_⟩
        have hxpart : plankPart x = j := by
          simpa only [plankPart, hxqassign.2] using hxparent
        rw [hf0]
        exact congrArg Sum.inl (Prod.ext hxqassign.2 hxpart)
    have hclassKept : {i ∈ kept | f 0 i = Sum.inl (k, j)} =
        (base k).fiber j ∩ fibre k := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_inter, ConvexSpaceBody.FactorFamily.fiber]
      constructor
      · intro hx
        have hxq : x ∈ q := hkeptq hx.1
        have hxpair : (assign x, plankPart x) = (k, j) := by
          rw [hf0] at hx
          exact Sum.inl.inj hx.2
        have hxassign : assign x = k := congrArg Prod.fst hxpair
        have hxpart : plankPart x = j := congrArg Prod.snd hxpair
        have hxparent : (base k).parent x = j := by
          simpa only [plankPart, hxassign] using hxpart
        refine ⟨⟨?_, hxparent⟩, ?_⟩
        · rw [hbase_inner k hkr]
          exact Finset.mem_filter.mpr ⟨hxq, hxassign⟩
        · exact Finset.mem_filter.mpr ⟨hx.1, hxassign⟩
      · rintro ⟨⟨_, hxparent⟩, hxfibre⟩
        obtain ⟨hxkept, hxassign⟩ := Finset.mem_filter.mp hxfibre
        have hxq : x ∈ q := hkeptq hxkept
        refine ⟨hxkept, ?_⟩
        have hxpart : plankPart x = j := by
          simpa only [plankPart, hxassign] using hxparent
        rw [hf0]
        exact congrArg Sum.inl (Prod.ext hxassign hxpart)
    have hp := hprotected (Sum.inl (k, j)) hjlabel
    rw [hclass, hclassKept] at hp
    dsimp only [A]
    exact_mod_cast hp.trans (Nat.mul_le_mul_right _ hbandRatio)
  have hpersistent : ∀ k ∈ kept.image assign,
      PersistentPlankFactorization (FF k) a b hab hb1
        (C₀ * ((relativePlankBandRatio s.card M : ℕ) : ℝ≥0) * Cvol) := by
    intro k hk
    have hkr : k ∈ r := hactive hk
    have hold : PersistentPlankFactorization (base k) a b hab hb1 C₀ :=
      hbase_persistent k hkr
    have hAone : 1 ≤ A := by
      dsimp only [A]
      exact_mod_cast one_le_relativePlankBandRatio s.card M
    have hAvol : 1 ≤ A * Cvol := by
      calc 1 = 1 * 1 := (mul_one 1).symm
        _ ≤ A * Cvol := mul_le_mul' hAone hCvol
    have hvolbase : ∀ i ∈ (base k).innerSet, ∀ i' ∈ (base k).innerSet,
        volume ((base k).innerBody i).carrier ≤
          (Cvol : ℝ≥0∞) * volume ((base k).innerBody i').carrier := by
      intro i hi i' hi'
      have hiq : i ∈ q := by
        exact (show i ∈ q ∧ assign i = k by
          rw [hbase_inner k hkr] at hi
          exact Finset.mem_filter.mp hi).1
      have hiq' : i' ∈ q := by
        exact (show i' ∈ q ∧ assign i' = k by
          rw [hbase_inner k hkr] at hi'
          exact Finset.mem_filter.mp hi').1
      rw [hbase_body k hkr]
      simpa using hvol i (hq hiq) i' (hq hiq')
    have hnew := hold.ofSubset hAvol (hfibre_base k) (fun j hj ↦ by
      apply hratio k hk
      simpa only [FF, ConvexSpaceBody.FactorFamily.ofSubset] using hj) hvolbase
    simpa only [FF, A] using hnew
  have hjoint_to_total : relativePlankJointLoss q.card M ≤ relativePlankTotalLoss s.card M := by
    calc
      relativePlankJointLoss q.card M ≤ relativePlankJointLoss s.card M := hjointLoss
      _ ≤ relativePlankJointLoss s.card M * relativePlankShadeLoss s.card M :=
        Nat.le_mul_of_pos_right _ (lt_of_lt_of_le Nat.zero_lt_one
          (one_le_relativePlankShadeLoss s.card M))
      _ = relativePlankTotalLoss s.card M := by rfl
  have hcardFinal : s.card ≤ Lp * relativePlankTotalLoss s.card M * kept.card := by
    calc
      s.card ≤ Lp * q.card := hplankHeavy
      _ ≤ Lp * (relativePlankJointLoss q.card M * kept.card) :=
        Nat.mul_le_mul_left Lp hcard
      _ ≤ Lp * (relativePlankTotalLoss s.card M * kept.card) :=
        Nat.mul_le_mul_left Lp (Nat.mul_le_mul_right kept.card hjoint_to_total)
      _ = Lp * relativePlankTotalLoss s.card M * kept.card := by simp [Nat.mul_assoc]
  have hshadeStep : ∑ i ∈ kept, volume (V i).shade ≤
      ((relativePlankShadeLoss s.card M : ℕ) : ℝ≥0∞) *
        ∑ i ∈ kept, volume (V' i).shade := by
    rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul kept
      (fun i ↦ (V i).toShadedBody)]
    rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul kept
      (fun i ↦ (V' i).toShadedBody)]
    have hden : (∑ i ∈ kept, volume (V i).carrier) =
        ∑ i ∈ kept, volume (V' i).carrier := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      calc
        (V i).carrier = (V i).toTube.carrier := rfl
        _ = (V' i).toTube.carrier := by rw [hV'tube i]
        _ = (V' i).carrier := rfl
    rw [← hden]
    have hfull' : ShadedBody.fullness' kept (fun i ↦ (V i).toShadedBody) ≤
        ((relativePlankShadeLoss s.card M : ℕ) : ℝ≥0∞) *
          ShadedBody.fullness' kept (fun i ↦ (V' i).toShadedBody) := by
      simpa only [relativePlankShadeLoss, relativePlankBucket, Nat.cast_pow] using hfull
    calc
      (ShadedBody.fullness kept fun i ↦ (V i).toShadedBody) *
          ∑ i ∈ kept, volume (V i).carrier
          ≤ (((relativePlankShadeLoss s.card M : ℕ) : ℝ≥0∞) *
              ShadedBody.fullness' kept (fun i ↦ (V' i).toShadedBody)) *
                ∑ i ∈ kept, volume (V i).carrier := by
            rw [ShadedBody.coe_fullness]
            gcongr
      _ = ((relativePlankShadeLoss s.card M : ℕ) : ℝ≥0∞) *
          ((ShadedBody.fullness kept fun i ↦ (V' i).toShadedBody) *
            ∑ i ∈ kept, volume (V i).carrier) := by
            rw [ShadedBody.coe_fullness]
            ac_rfl
  have hmassBefore : ∑ i ∈ s, volume (V i).shade ≤
      ((2 * Lp * relativePlankJointLoss s.card M : ℕ) : ℝ≥0∞) *
        ∑ i ∈ kept, volume (V i).shade := by
    by_cases hkept : kept.Nonempty
    · obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image kept
        (fun i ↦ volume (V i).shade) hkept
      have hupper : ∑ i ∈ s, volume (V i).shade ≤
          (s.card : ℝ≥0∞) * (2 * volume (V i₀).shade) := by
        simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul s
          (fun i ↦ volume (V i).shade) (2 * volume (V i₀).shade)
          (fun i hi ↦ hshadeComp i hi i₀ (hkepts hi₀))
      have hcardSJ : s.card ≤ Lp * relativePlankJointLoss s.card M * kept.card := by
        calc
          s.card ≤ Lp * q.card := hplankHeavy
          _ ≤ Lp * (relativePlankJointLoss q.card M * kept.card) :=
            Nat.mul_le_mul_left Lp hcard
          _ ≤ Lp * (relativePlankJointLoss s.card M * kept.card) :=
            Nat.mul_le_mul_left Lp (Nat.mul_le_mul_right kept.card hjointLoss)
          _ = Lp * relativePlankJointLoss s.card M * kept.card := by simp [Nat.mul_assoc]
      have hlower : (kept.card : ℝ≥0∞) * volume (V i₀).shade ≤
          ∑ i ∈ kept, volume (V i).shade := by
        simpa only [nsmul_eq_mul] using Finset.card_nsmul_le_sum kept
          (fun i ↦ volume (V i).shade) (volume (V i₀).shade) (fun i hi ↦ hmin i hi)
      calc
        ∑ i ∈ s, volume (V i).shade
            ≤ (s.card : ℝ≥0∞) * (2 * volume (V i₀).shade) := hupper
        _ ≤ ((Lp * relativePlankJointLoss s.card M * kept.card : ℕ) : ℝ≥0∞) *
              (2 * volume (V i₀).shade) := by
            gcongr
        _ = ((2 * Lp * relativePlankJointLoss s.card M : ℕ) : ℝ≥0∞) *
              ((kept.card : ℝ≥0∞) * volume (V i₀).shade) := by
            simp only [Nat.cast_mul, Nat.cast_ofNat]
            ring
        _ ≤ ((2 * Lp * relativePlankJointLoss s.card M : ℕ) : ℝ≥0∞) *
              ∑ i ∈ kept, volume (V i).shade := by gcongr
    · have hkept0 : kept = ∅ := Finset.not_nonempty_iff_eq_empty.mp hkept
      have hq0 : q = ∅ := Finset.card_eq_zero.mp (by
        rw [hkept0] at hcard
        simpa using hcard)
      have hs0 : s = ∅ := Finset.card_eq_zero.mp (by
        rw [hq0] at hplankHeavy
        simpa using hplankHeavy)
      simp [hs0, hkept0]
  have hmassFinal : ∑ i ∈ s, volume (V i).shade ≤
      ((2 * Lp * relativePlankTotalLoss s.card M : ℕ) : ℝ≥0∞) *
        ∑ i ∈ kept, volume (V' i).shade := by
    calc
      ∑ i ∈ s, volume (V i).shade
          ≤ ((2 * Lp * relativePlankJointLoss s.card M : ℕ) : ℝ≥0∞) *
              ∑ i ∈ kept, volume (V i).shade := hmassBefore
      _ ≤ ((2 * Lp * relativePlankJointLoss s.card M : ℕ) : ℝ≥0∞) *
            (((relativePlankShadeLoss s.card M : ℕ) : ℝ≥0∞) *
              ∑ i ∈ kept, volume (V' i).shade) := by gcongr
      _ = ((2 * Lp * relativePlankTotalLoss s.card M : ℕ) : ℝ≥0∞) *
            ∑ i ∈ kept, volume (V' i).shade := by
          simp only [relativePlankTotalLoss]
          simp only [Nat.cast_mul, Nat.cast_ofNat]
          ring
  refine ⟨{
    kept := kept
    kept_subset := hkepts
    kept_subset_plank := hkeptq
    shading := V'
    sameTube := hV'tube
    shade_subset := hV'shade
    activeParents := kept.image assign
    activeParents_eq := rfl
    activeParents_subset := hactive
    shadedUniform := ?_
    factorFamily := FF
    factorFamily_innerSet := ?_
    factorFamily_innerBody := ?_
    persistentFactorization := hpersistent
    card_retention := ?_
    shading_mass_retention := ?_ }⟩
  · simpa only [C, A, MultiScaleFac.relativePlankBandRestrictConst] using 𝒱
  · intro k hk
    rfl
  · intro k
    funext i
    simp only [FF, ConvexSpaceBody.FactorFamily.ofSubset, base]
    split
    · next hk =>
        rw [hFbody k hk]
    · rfl
  · calc
      s.card ≤ Lp * relativePlankTotalLoss s.card M * kept.card := hcardFinal
      _ ≤ (2 * Lp * relativePlankTotalLoss s.card M) * kept.card := by
        apply Nat.mul_le_mul_right
        nlinarith
  · simpa only [Nat.cast_mul] using hmassFinal

open Classical in
/-- **The scale constraint carried by `Kakeya.RelativePlankSelection`.**

This is the guardrail against reintroducing the clause `outerBody j ≤ (R k).toConvexSpaceBody` that
`Kakeya.RelativePlankSelection` used to carry; see that structure's docstring for the full account.
The outer body of a used parent of a `Kakeya.PersistentPlankFactorization` *is* an `a × b × 1`
plank, so confining it to a `ρ`-tube pits the plank's half-length one against the tube's
`1 / 2 + ρ`, and `Kakeya.Plank.half_le_of_toConvexSpaceBody_le_tube` yields `1 / 2 ≤ ρ`.

This is only the long-axis half of the obstruction.  The transverse half upgrades it to an outright
contradiction as soon as `ρ ≤ a` and `0 < a`; that half is argued in the `RelativePlankSelection`
docstring and is *not* formalized. -/
theorem half_le_of_persistentPlankFactorization {ι ω : Type*} {ρ a b : ℝ≥0} {hab : a ≤ b}
    {hb1 : b ≤ 1} {C₀ : ℝ≥0}
    {F : ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι ω}
    (hF : PersistentPlankFactorization F a b hab hb1 C₀)
    {j : ω} (hj : j ∈ F.innerSet.image F.parent) (R : Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (hle : F.outerBody j ≤ R.toConvexSpaceBody) : 1 / 2 ≤ ρ := by
  obtain ⟨Q, hQ⟩ := hF.outer_are_planks j hj
  rw [hQ] at hle
  exact Plank.half_le_of_toConvexSpaceBody_le_tube Q R hle

/-- **The retained family is a `totalLoss⁻¹`-refinement of the original.**

`Kakeya.RelativePlankSelection` carries its two retention clauses separately, as a cardinality
bound and a shade-mass bound.  The shade-mass bound, together with `kept_subset`, `sameTube` and
`shade_subset`, is exactly `ShadedBody.IsCRefinement` at `c = totalLoss⁻¹`, which is the interface
the transfer lemmas of `Kakeya/Multiplicity.lean` read: `ShadedBody.IsCRefinement.multiplicity_le`
turns a multiplicity bound on the retained family into one on the original, and
`ShadedBody.IsCRefinement.coe_mul_fullness_le` transports the fullness.

No positivity of `totalLoss` is needed: at `totalLoss = 0` the `NNReal` inverse is `0` and the
mass clause is vacuous. -/
theorem RelativePlankSelection.isCRefinement {ι κ : Type*} {δ ρ a b : ℝ≥0} {hab : a ≤ b}
    {hb1 : b ≤ 1} {s q : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {assign : ι → κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))} {r : Finset κ} {M : ℕ}
    {uniformConst factorConst : ℝ≥0} {totalLoss : ℕ}
    (S : RelativePlankSelection hab hb1 s q V assign R r M uniformConst factorConst totalLoss) :
    ShadedBody.IsCRefinement S.kept (fun i => (S.shading i).toShadedBody) s
      (fun i => (V i).toShadedBody) ((totalLoss : ℝ≥0))⁻¹ := by
  refine ShadedBody.isCRefinement_of_isRefinement_of_sum_le
    (s' := S.kept) (V' := fun i => (S.shading i).toShadedBody)
    (s := s) (V := fun i => (V i).toShadedBody)
    (C := (totalLoss : ℝ≥0)) ?_ ?_
  · refine ⟨S.kept_subset, ?_⟩
    intro i hi
    constructor
    · simpa using congrArg Tube.toConvexSpaceBody (S.sameTube i)
    · exact S.shade_subset i
  · simpa using S.shading_mass_retention

/-! ### GWZ Proposition 6.6(A) for persistent factorizations -/

open Classical in
/-- **GWZ Proposition 6.6(A) with the outer bodies only fixed, not spanned.**

The hypothesis is `Kakeya.PersistentPlankFactorization` rather than
`Kakeya.PlankFactorization`.  The weakening is harmless: the proof of 6.6(A) feeds each block to
GWZ Lemma 5.1 and to the plank estimate GWZ Lemma 6.4, and neither uses `parts_are_planks` in its
equality form.  Lemma 6.4 takes a family of shaded planks and no inner family, and Lemma 5.1 needs
only that the inner bodies of a block lie in that block's outer plank together with a Frostman
constant for the block — both of which are fields of `PersistentPlankFactorization`.

## Which 6.6(A) this is, and which it is not

An earlier revision of this docstring said "the conclusion is that of
`Kakeya.tubeMultiplicityOfLocalPlankFactorisation`".  **That declaration does not exist**: it was
deleted, and the record of what it said and why it went is in the comment block at
`Kakeya/DimensionThree/Plank/Factorization.lean`, section "GWZ Proposition 6.6(A)".  The
mathematical content of the old sentence was right — this is the persistent-hypothesis variant of
the deleted statement, in the *same* scale regime, `δ ≤ ρ ≤ a ≤ b ≤ 1`, with the coarse scale
*below* the plank widths.

That regime is **not** the one of `Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'`, which is
the surviving general form of 6.6(A) and runs at `σ ≤ a ≤ b ≤ ρ ≤ 1`.  [GWZ] imposes no ordering
between `ρ` and `a, b`, so neither statement implies the other; they are two restrictions of one
paper result and both have to be proved separately.  Two further divergences from that form: the
ambient space here is fixed at `EuclideanSpace ℝ (Fin 3)` rather than an abstract `E` with
`Module.finrank ℝ E = 3`, and the outer bodies are exact planks up to the persistence clause
rather than planks up to a comparability constant `Kakeya.IsPlankFamilyOfDimensions`.

Its consumer is `Kakeya.multiplicity_le_of_relativePlankSelection`, just below.

## The essential-distinctness clause, and the two hypotheses that went

An earlier revision of this statement carried **no essential-distinctness clause** on the fine
family `(T i)_{i ∈ q}` and no bound on `#q`, and in that form it is **false**: take `N` copies of
one fully shaded `δ`-tube at `ρ = a = b = δ`, one block, one outer plank; the multiplicity is
exactly `N` while the right-hand side is `N`-free.  That refutation is
`Kakeya.PersistPlankCE.not_payload`, and `Kakeya.PersistPlankCE.false_of_target` shows the old
form is false rather than vacuous, since `Kakeya.KatzTao_one` and `Kakeya.frostmanEstimate_one`
prove its two partial-estimate hypotheses at `β = 1`.

So the clause
`(q : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)` is now
present.  This is **leaf-scale** essential distinctness, on the fine tubes `T i` at scale `δ`, not
parent-scale essential distinctness on the coarse tubes `R k`; see the erratum against GWZ
Definition 2.1(ii) in `blueprint/src/GWZAdapted/section2.tex`, which states that essential
distinctness is required and supplied at the leaf scale and never at the parent scale.  Every
other form of this estimate in the development carries it: it is a hypothesis of
`Kakeya.FrostmanEstimate.multiplicity_bound_of_mem`, the base estimate this reduces to, and the
field `essDistinct` of `Kakeya.IsFlatPrismFamily`.

Two hypotheses of the earlier revision have **gone**, which strengthens the statement: the
Katz--Tao estimate `K_KT(β)`, and the two-sided shaded uniformity
`ShadedTube.ShadedUniformTubeSet` at the grid length `Tube.ssfGridLen δ`.  Neither is used: in the
regime `δ ≤ ρ ≤ a ≤ b ≤ 1` the factorisation carries no aspect-ratio information beyond its own
constant `C₀`, so the claimed plank gain `(a/b) ^ (3β/2)` is a `δ ^ (-ε)`-absorbable loss and the
whole statement reduces to `K_F(β)`.  The proof is
`Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation_of_essDistinct`
(`Kakeya/RelativePlankRepair.lean`), of which this is a restatement; the index universe is tied to
the universe of `K_F(β)` because that is the universe the base estimate is read at. -/
theorem tubeMultiplicityOfLocalPersistentPlankFactorisation {β : ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0),
      ∀ {ι : Type u} (q : Finset ι) {δ : ℝ≥0} (hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        δ ≤ δ₀ →
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (q : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
          {κ : Type} (r : Finset κ)
          (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (assign : ι → κ),
          δ ≤ ρ → ρ ≤ a →
          (∀ i ∈ q, assign i ∈ r ∧
            (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody) →
          ∀ (C₀ : ℝ≥0), C₀ ≤ δ ^ (-η) →
            ∀ (F : κ → ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι (Finset ι)),
              (∀ k ∈ r, (F k).innerSet = {i ∈ q | assign i = k}) →
              (∀ k ∈ r, (F k).innerBody = fun i => (T i).toConvexSpaceBody) →
              (∀ k ∈ r, PersistentPlankFactorization (F k) a b hab hb1 C₀) →
          ∀ (CF : ENNReal), 1 ≤ CF → CF ≠ ⊤ →
            IsFrostmanIn q (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall CF →
            ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
              (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2)
                * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
                * (δ : ENNReal) ^ (-2 * β)
                * ((δ : ENNReal) ^ 2 * (q.card : ENNReal)) ^ (1 - β / 2) :=
  tubeMultiplicityOfLocalPersistentPlankFactorisation_of_essDistinct hβpos hβle hKF

open Classical in
/-- **The joint regularization feeds the persistent form of GWZ Proposition 6.6(A).**

The composite of `Kakeya.exists_relativePlankSelection` with
`Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation`.  It is pure plumbing: the selection
produces, on a retained subfamily `kept ⊆ q` at a refined shading `T`, exactly the package the
persistent proposition consumes — one `Kakeya.PersistentPlankFactorization` per surviving plank
block with its outer bodies inside the coarse tubes — and the retention clauses are repackaged as
a `ShadedBody.IsCRefinement`, which is what carries the conclusion back to the original family.

## Essential distinctness is threaded, not manufactured

`Kakeya.tubeMultiplicityOfLocalPersistentPlankFactorisation` now demands leaf-scale essential
distinctness of the fine tubes.  `Kakeya.exists_relativePlankSelection` does **not** produce that
clause out of nothing and carries no such hypothesis; what it does is *preserve* it.  The
selection only shrinks the index set (`RelativePlankSelection.kept_subset_plank : kept ⊆ q`) and
never moves a tube (`RelativePlankSelection.sameTube : (shading i).toTube = (V i).toTube`, hence
`(shading i).carrier = (V i).carrier`), so a `Set.Pairwise` property of `(V i)_{i ∈ q}` restricts
verbatim to `(shading i)_{i ∈ kept}`.  Accordingly the clause is a hypothesis here, on the
original family, and the proof restricts it.

The Katz--Tao estimate `K_KT(β)` and the constant hypothesis
`max (relativePlankBandRestrictConst Cu …) 4 ≤ δ ^ (-η)` are gone from this statement too: the
first because the persistent proposition no longer takes it, the second because it existed only to
feed that proposition's `ShadedTube.ShadedUniformTubeSet` clause, which is likewise gone.  The
`Tube.UniformTubeSet` argument `𝒰` stays, since `Kakeya.exists_relativePlankSelection` still needs
it.

The three side conditions on constants are read on the constants the selection actually produces.
They are not restrictive: `Kakeya.exists_threshold_relativePlankUniformConst_le`,
`Kakeya.exists_threshold_relativePlankFactorConst_le` and
`Kakeya.exists_threshold_relativePlankTotalLoss_le` discharge them below a threshold, given
subpolynomial `Cu`, `C₀`, `Cvol`, `Lp` and `#s`.

The scale regime is the one the persistent proposition is stated in, `δ ≤ ρ ≤ a ≤ b ≤ 1`; see its
docstring.  It is *not* the regime of `Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'`, and
neither implies the other.

The Frostman constant is quantified inside the existential because the set it is read on, `kept`,
is produced by the selection and cannot be named in advance.

## The plank hypothesis was vacuous and has been replaced

This statement used to take `∀ k ∈ r, PlankFactorization a b hab hb1 {i ∈ q | assign i = k}
(fun i => (V i).toConvexSpaceBody) C₀`.  Together with `0 < δ` that hypothesis is unsatisfiable
unless `q = ∅` — see `Kakeya.not_plankFactorization_of_shadedTube` — and `s.card ≤ Lp * q.card`
then forces `s = ∅`, so the whole implication was vacuously true.  It now takes the same
`Kakeya.PersistentPlankFactorization` package as
`Kakeya.exists_relativePlankSelection`, which is satisfiable; see that theorem's docstring for the
full account, and `Kakeya.half_le_of_persistentPlankFactorization` for the scale constraint that
made the old `factorFamily_outer_le_parent` clause of `Kakeya.RelativePlankSelection` untenable. -/
theorem multiplicity_le_of_relativePlankSelection {β : ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0),
      ∀ {ι : Type u} {κ : Type} {δ ρ a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
        {s q : Finset ι} (hq : q ⊆ s) {Cu C₀ Cvol : ℝ≥0}
        (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (𝒰 : Tube.UniformTubeSet s (fun i => (V i).toTube) (Tube.ssfGridLen δ) Cu)
        (assign : ι → κ) (r : Finset κ) (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (Lp : ℕ)
        (F : κ → ConvexSpaceBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι (Finset ι)),
        0 < δ → δ ≤ δ₀ → 0 < Tube.ssfGridLen δ → δ ≤ ρ → ρ ≤ a → 0 < Lp → 1 ≤ Cvol →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
        (q : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        (∀ i ∈ q, assign i ∈ r ∧
          (V i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody) →
        (∀ k ∈ r, (F k).innerSet = {i ∈ q | assign i = k}) →
        (∀ k ∈ r, (F k).innerBody = fun i => (V i).toConvexSpaceBody) →
        (∀ k ∈ r, PersistentPlankFactorization (F k) a b hab hb1 C₀) →
        s.card ≤ Lp * q.card →
        (∀ i ∈ s, ∀ i' ∈ s, volume (V i).carrier ≤ (Cvol : ℝ≥0∞) * volume (V i').carrier) →
        (∀ i ∈ s, ∀ i' ∈ s, volume (V i).shade ≤ 2 * volume (V i').shade) →
        C₀ * ((relativePlankBandRatio s.card (Tube.ssfGridLen δ) : ℕ) : ℝ≥0) * Cvol ≤ δ ^ (-η) →
        (((2 * Lp * relativePlankTotalLoss s.card (Tube.ssfGridLen δ) : ℕ) : ℝ≥0∞)
            * ((δ : ℝ≥0) ^ η : ℝ≥0)
          ≤ (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ℝ≥0)) →
        ∃ kept : Finset ι, ∃ T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)),
          kept ⊆ q ∧ (∀ i, (T i).toTube = (V i).toTube) ∧
          ShadedBody.IsCRefinement kept (fun i => (T i).toShadedBody) s
            (fun i => (V i).toShadedBody)
            (((2 * Lp * relativePlankTotalLoss s.card (Tube.ssfGridLen δ) : ℕ) : ℝ≥0))⁻¹ ∧
          ∀ CF : ENNReal, 1 ≤ CF → CF ≠ ⊤ →
            IsFrostmanIn kept (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall CF →
            ShadedBody.multiplicity kept (fun i => (T i).toShadedBody) ≤
              (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2)
                * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
                * (δ : ENNReal) ^ (-2 * β)
                * ((δ : ENNReal) ^ 2 * (kept.card : ENNReal)) ^ (1 - β / 2) := by
  intro ε hε
  obtain ⟨η, hη, δ₀, hδ₀, hTM⟩ :=
    tubeMultiplicityOfLocalPersistentPlankFactorisation hβpos hβle hKF ε hε
  refine ⟨η, hη, δ₀, hδ₀, ?_⟩
  intro ι κ δ ρ a b hab hb1 s q hq Cu C₀ Cvol V 𝒰 assign r R Lp F
    hδ0 hδδ0 hssf hδρ hρa hLp hCvol hcarrier hED hassign hFinner hFbody hFz hcard hvol hshade
    hFactorConst hFullness
  obtain ⟨S⟩ := exists_relativePlankSelection (M := Tube.ssfGridLen δ) (hM := hssf)
    (hab := hab) (hb1 := hb1) (hq := hq) (Cu := Cu) (C₀ := C₀) (Cvol := Cvol)
    (V := V) (𝒰 := 𝒰) (assign := assign) (r := r) (R := R) (hparent := hassign)
    (F := F) (hFinner := hFinner) (hFbody := hFbody)
    (Fz := hFz) (Lp := Lp) (hplankHeavy := hcard) (hCvol := hCvol) (hvol := hvol)
    (hshadeComp := hshade)
  refine ⟨S.kept, S.shading, S.kept_subset_plank, S.sameTube, S.isCRefinement, ?_⟩
  intro CF hCF1 hCFtop hFrost
  refine hTM (q := S.kept) (hδ0 := hδ0) (T := S.shading) hδδ0 ?_ ?_ ?_
    ρ a b hab hb1 (r := S.activeParents) R assign hδρ hρa ?_
    (C₀ := C₀ * ((relativePlankBandRatio s.card (Tube.ssfGridLen δ) : ℕ) : ℝ≥0) * Cvol)
    hFactorConst (F := S.factorFamily) ?_ ?_ ?_ CF hCF1 hCFtop hFrost
  · intro i hi
    have hc : (S.shading i).carrier = (V i).carrier := by
      simpa using congrArg (fun t : Tube δ (EuclideanSpace ℝ (Fin 3)) => t.carrier) (S.sameTube i)
    exact hc.trans_le (hcarrier i (S.kept_subset hi))
  · have hcar : ∀ i, (S.shading i).carrier = (V i).carrier := by
      intro i
      simpa using congrArg (fun t : Tube δ (EuclideanSpace ℝ (Fin 3)) => t.carrier) (S.sameTube i)
    intro i hi j hj hij
    have hiq : i ∈ (q : Set ι) := by
      exact_mod_cast S.kept_subset_plank (by exact_mod_cast hi)
    have hjq : j ∈ (q : Set ι) := by
      exact_mod_cast S.kept_subset_plank (by exact_mod_cast hj)
    simpa [hcar] using hED hiq hjq hij
  · let L : ℕ := 2 * Lp * relativePlankTotalLoss s.card (Tube.ssfGridLen δ)
    let x : ℝ≥0 := (δ : ℝ≥0) ^ η
    have hTLpos : 0 < relativePlankTotalLoss s.card (Tube.ssfGridLen δ) := by
      exact lt_of_lt_of_le zero_lt_one (one_le_relativePlankTotalLoss s.card (Tube.ssfGridLen δ))
    have hL0 : 0 < L := by
      change (0 : ℕ) < 2 * Lp * relativePlankTotalLoss s.card (Tube.ssfGridLen δ)
      exact Nat.mul_pos (by omega) hTLpos
    have hLne : (L : ℝ≥0) ≠ 0 := by
      exact_mod_cast (ne_of_gt hL0)
    have hLne0 : (L : ℝ≥0∞) ≠ 0 := by
      simpa using ENNReal.coe_ne_zero.mpr hLne
    have hLtop : (L : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top L
    have hCref : ((((L : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
          (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ℝ≥0∞) ≤
        (ShadedBody.fullness S.kept (fun i => (S.shading i).toShadedBody) : ℝ≥0∞) :=
      S.isCRefinement.coe_mul_fullness_le
    have hδle : (x : ℝ≥0∞) ≤
        (ShadedBody.fullness S.kept (fun i => (S.shading i).toShadedBody) : ℝ≥0∞) := by
      calc
        (x : ℝ≥0∞) = (L : ℝ≥0∞)⁻¹ * ((L : ℝ≥0∞) * (x : ℝ≥0∞)) := by
          rw [ENNReal.inv_mul_cancel_left hLne0 hLtop]
        _ ≤ (L : ℝ≥0∞)⁻¹ *
            (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ℝ≥0∞) := by
          exact mul_le_mul_right hFullness (L : ℝ≥0∞)⁻¹
        _ ≤ (ShadedBody.fullness S.kept (fun i => (S.shading i).toShadedBody) : ℝ≥0∞) := by
          simpa [ENNReal.coe_inv hLne] using hCref
    exact ENNReal.coe_le_coe.mp hδle
  · intro i hi
    constructor
    · rw [S.activeParents_eq]
      exact Finset.mem_image_of_mem assign hi
    · have hc : (S.shading i).toConvexSpaceBody = (V i).toConvexSpaceBody := by
        simpa using congrArg Tube.toConvexSpaceBody (S.sameTube i)
      exact hc.trans_le (hassign i (S.kept_subset_plank hi)).2
  · intro k hk
    exact S.factorFamily_innerSet k hk
  · intro k hk
    rw [S.factorFamily_innerBody k]
    funext i
    simpa using (congrArg Tube.toConvexSpaceBody (S.sameTube i)).symm
  · intro k hk
    exact S.persistentFactorization k hk

/-! ### Absorption of the losses -/

/-- **One monomial in the bucket count is one grid loss.**

The shared arithmetic behind both reductions below.  A quantity of the shape `d * B ^ e`, with `B`
bounded by `c * (1 - log δ)`, is at most `StickyKakeya.gridLoss A K δ` as soon as the constant part
`d * c ^ e` fits under the base raised to `M + 1` and the exponent `e` fits under the
polylogarithmic exponent `K * (M + 1) ^ 2`.  Isolating it keeps the two reductions free of any
manipulation of `StickyKakeya.gridLoss`. -/
theorem mul_pow_le_gridLoss {A : ℝ≥0} {K : ℕ} {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {B c d : ℝ} (hd : 0 ≤ d) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hBc : B ≤ c * (1 - Real.log (δ : ℝ))) {e : ℕ}
    (hdc : d * c ^ e ≤ (A : ℝ) ^ (Tube.ssfGridLen δ + 1))
    (he : e ≤ K * (Tube.ssfGridLen δ + 1) ^ 2) :
    d * B ^ e ≤ StickyKakeya.gridLoss A K δ := by
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hW : 1 ≤ 1 - Real.log (δ : ℝ) := by
    linarith [Real.log_nonpos (by exact_mod_cast hδ0.le) hδ1']
  have hcW : 0 ≤ c * (1 - Real.log (δ : ℝ)) := mul_nonneg hc (by linarith)
  have hpowB : B ^ e ≤ (c * (1 - Real.log (δ : ℝ))) ^ e :=
    pow_le_pow_left₀ hB hBc e
  have hpowW : (1 - Real.log (δ : ℝ)) ^ e ≤
      (1 - Real.log (δ : ℝ)) ^ (K * (Tube.ssfGridLen δ + 1) ^ 2) :=
    pow_le_pow_right₀ hW he
  rw [StickyKakeya.gridLoss]
  calc
    d * B ^ e ≤ d * (c * (1 - Real.log (δ : ℝ))) ^ e :=
      mul_le_mul_of_nonneg_left hpowB hd
    _ = (d * c ^ e) * (1 - Real.log (δ : ℝ)) ^ e := by rw [mul_pow]; ring
    _ ≤ (A : ℝ) ^ (Tube.ssfGridLen δ + 1) *
        (1 - Real.log (δ : ℝ)) ^ e := by gcongr
    _ ≤ (A : ℝ) ^ (Tube.ssfGridLen δ + 1) *
        (1 - Real.log (δ : ℝ)) ^ (K * (Tube.ssfGridLen δ + 1) ^ 2) := by gcongr

/-- **Three factors at a third of the budget make one factor at the budget.**  The arithmetic of
`Kakeya.exists_threshold_relativePlankFactorConst_le`, isolated because there the three sources
genuinely multiply, unlike the nested maximum of the uniformity constant. -/
theorem mul_mul_le_rpow_neg_of_third {δ : ℝ≥0} (hδ0 : 0 < δ) {α x y z : ℝ}
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z)
    (hx : x ≤ (δ : ℝ) ^ (-(α / 3))) (hy : y ≤ (δ : ℝ) ^ (-(α / 3)))
    (hz : z ≤ (δ : ℝ) ^ (-(α / 3))) :
    x * y * z ≤ (δ : ℝ) ^ (-α) := by
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hp : 0 < (δ : ℝ) ^ (-(α / 3)) := Real.rpow_pos_of_pos hδR _
  calc
    x * y * z ≤ ((δ : ℝ) ^ (-(α / 3)) * (δ : ℝ) ^ (-(α / 3))) *
        (δ : ℝ) ^ (-(α / 3)) := by
      exact mul_le_mul (mul_le_mul hx hy hy0 (hx0.trans hx)) hz hz0 (mul_nonneg hp.le hp.le)
    _ = (δ : ℝ) ^ (-α) := by
      rw [← Real.rpow_add hδR, ← Real.rpow_add hδR]
      congr 1
      ring

/-- **The dyadic bucket count of a polynomially bounded family is logarithmic in `1 / δ`.**

With `n ≤ δ ^ (-K)` one has `log₂ n ≤ K log₂(1/δ)`, and `log 2 > 1/2` turns the base-`2` logarithm
into at most `2 K log(1/δ)`. -/
theorem relativePlankBucket_le_mul_one_sub_log (K : ℕ) {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (hn : (n : ℝ) ≤ (δ : ℝ) ^ (-(K : ℝ))) :
    ((relativePlankBucket n : ℕ) : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) * (1 - Real.log (δ : ℝ)) := by
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hlogδ : Real.log (δ : ℝ) ≤ 0 := Real.log_nonpos hδR.le hδR1
  have hW : (1 : ℝ) ≤ 1 - Real.log (δ : ℝ) := by linarith
  by_cases hn0 : n = 0
  · subst n
    simp only [relativePlankBucket, Nat.log_zero_right, zero_add, Nat.cast_one]
    calc
      (1 : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * K + 1)
      _ ≤ ((2 * K + 1 : ℕ) : ℝ) * (1 - Real.log (δ : ℝ)) :=
        le_mul_of_one_le_right (by positivity) hW
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
    have hlogn : Real.log (n : ℝ) ≤ (-(K : ℝ)) * Real.log (δ : ℝ) := by
      have h := Real.log_le_log hnpos hn
      rw [Real.log_rpow hδR] at h
      exact h
    have hnatlog : (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
      have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      rw [le_div_iff₀ hlog2pos, ← Real.log_pow]
      exact Real.log_le_log (by positivity) (by
        exact_mod_cast Nat.pow_log_le_self 2 (Nat.pos_of_ne_zero hn0).ne')
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 :=
      lt_trans (by norm_num : (1 / 2 : ℝ) < 0.6931471803) Real.log_two_gt_d9
    have hnat0 : (0 : ℝ) ≤ Nat.log 2 n := by positivity
    have hmul : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
      exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp hnatlog
    have hhalf : (Nat.log 2 n : ℝ) * (1 / 2) ≤
        (Nat.log 2 n : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2.le hnat0
    have hnatKL : (Nat.log 2 n : ℝ) ≤
        2 * (K : ℝ) * (-Real.log (δ : ℝ)) := by
      have hK : (0 : ℝ) ≤ K := by positivity
      nlinarith
    simp only [relativePlankBucket, Nat.cast_add, Nat.cast_one]
    have hK : (0 : ℝ) ≤ K := by positivity
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith

/-- **The total loss is dominated by one grid loss.**

`relativePlankTotalLoss n M = 2 * B ^ (3 M + 4)` with `B = relativePlankBucket n`, and
`Kakeya.relativePlankBucket_le_mul_one_sub_log` bounds `B` by `(2 K + 1) (1 - log δ)`.  Collecting
the constant part into a base raised to `M + 1` and the logarithmic part into the polylogarithmic
exponent puts the whole expression under `StickyKakeya.gridLoss`, whose subpolynomiality is already
available as `StickyKakeya.exists_threshold_gridLoss_le`. -/
theorem relativePlankTotalLoss_le_gridLoss (K : ℕ) {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (hn : (n : ℝ) ≤ (δ : ℝ) ^ (-(K : ℝ))) :
    ((relativePlankTotalLoss n (Tube.ssfGridLen δ) : ℕ) : ℝ) ≤
      StickyKakeya.gridLoss ((2 * (2 * K + 1) ^ 4 : ℕ) : ℝ≥0) 4 δ := by
  let M := Tube.ssfGridLen δ
  let B : ℝ := relativePlankBucket n
  let c : ℝ := 2 * K + 1
  have hc1 : (1 : ℝ) ≤ c := by
    dsimp [c]
    have hK : (0 : ℝ) ≤ K := by positivity
    linarith
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hBc : B ≤ c * (1 - Real.log (δ : ℝ)) := by
    simpa only [B, c, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      relativePlankBucket_le_mul_one_sub_log K hδ0 hδ1 n hn
  have he₁ : 3 * M + 4 ≤ 4 * (M + 1) := by omega
  have he₂ : 4 * (M + 1) ≤ 4 * (M + 1) ^ 2 := by
    apply Nat.mul_le_mul_left 4
    rw [pow_two]
    exact Nat.le_mul_of_pos_left (M + 1) (Nat.zero_lt_succ M)
  have hcpow : c ^ (3 * M + 4) ≤ c ^ (4 * (M + 1)) :=
    pow_le_pow_right₀ hc1 he₁
  have h2pow : (2 : ℝ) ≤ 2 ^ (M + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ M + 1)
  have hdc : 2 * c ^ (3 * M + 4) ≤
      (((2 * (2 * K + 1) ^ 4 : ℕ) : ℝ≥0) : ℝ) ^ (M + 1) := by
    calc
      2 * c ^ (3 * M + 4) ≤ 2 * c ^ (4 * (M + 1)) := by gcongr
      _ ≤ 2 ^ (M + 1) * c ^ (4 * (M + 1)) := by gcongr
      _ = (((2 * (2 * K + 1) ^ 4 : ℕ) : ℝ≥0) : ℝ) ^ (M + 1) := by
        dsimp [c]
        push_cast
        rw [mul_pow, ← pow_mul]
  have hmain := mul_pow_le_gridLoss (A := ((2 * (2 * K + 1) ^ 4 : ℕ) : ℝ≥0))
    (K := 4) hδ0 hδ1 (B := B) (c := c) (d := 2) (e := 3 * M + 4)
    (by norm_num) (by positivity) hB0 hBc hdc (he₁.trans he₂)
  rw [show ((relativePlankTotalLoss n (Tube.ssfGridLen δ) : ℕ) : ℝ) =
      2 * B ^ (3 * M + 4) by
    simp only [relativePlankTotalLoss, relativePlankJointLoss, relativePlankShadeLoss,
      relativePlankRounds, B, M, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    rw [mul_assoc, ← pow_add]
    congr 2
    omega]
  exact hmain

/-- **The class-band ratio is dominated by one grid loss.**

`relativePlankBandRatio n M = 8 (M + 2) B ^ (M + 2)`, so besides the power of the bucket count
there is one factor linear in the number of grid levels; it is absorbed by `M + 2 ≤ 2 ^ (M + 1)`.
The shape is otherwise that of `Kakeya.relativePlankTotalLoss_le_gridLoss`. -/
theorem relativePlankBandRatio_le_gridLoss (K : ℕ) {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (hn : (n : ℝ) ≤ (δ : ℝ) ^ (-(K : ℝ))) :
    ((relativePlankBandRatio n (Tube.ssfGridLen δ) : ℕ) : ℝ) ≤
      StickyKakeya.gridLoss ((16 * (2 * K + 1) ^ 2 : ℕ) : ℝ≥0) 2 δ := by
  let M := Tube.ssfGridLen δ
  let B : ℝ := relativePlankBucket n
  let c : ℝ := 2 * K + 1
  have hc1 : (1 : ℝ) ≤ c := by
    dsimp [c]
    have hK : (0 : ℝ) ≤ K := by positivity
    linarith
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hBc : B ≤ c * (1 - Real.log (δ : ℝ)) := by
    simpa only [B, c, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      relativePlankBucket_le_mul_one_sub_log K hδ0 hδ1 n hn
  have hM2 : M + 2 ≤ 2 ^ (M + 1) := by
    induction M with
    | zero => norm_num
    | succ M ih =>
        rw [pow_succ]
        omega
  have hcPow : c ^ (M + 2) ≤ c ^ (2 * M + 2) :=
    pow_le_pow_right₀ hc1 (by omega)
  have hcoef : (8 : ℝ) * 2 ^ (M + 1) ≤ 16 ^ (M + 1) := by
    calc
      (8 : ℝ) * 2 ^ (M + 1) = 2 ^ (M + 4) := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add]
        congr 1
        omega
      _ ≤ 2 ^ (4 * (M + 1)) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      _ = 16 ^ (M + 1) := by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]
  have hdc : (8 * (M + 2) : ℕ) * c ^ (M + 2) ≤
      (((16 * (2 * K + 1) ^ 2 : ℕ) : ℝ≥0) : ℝ) ^ (M + 1) := by
    have hM2R : ((M + 2 : ℕ) : ℝ) ≤ 2 ^ (M + 1) := by exact_mod_cast hM2
    calc
      (8 * (M + 2) : ℕ) * c ^ (M + 2)
          ≤ ((8 : ℝ) * 2 ^ (M + 1)) * c ^ (M + 2) := by
            norm_num only [Nat.cast_mul, Nat.cast_ofNat]
            gcongr
      _ ≤ 16 ^ (M + 1) * c ^ (2 * M + 2) := by gcongr
      _ = (((16 * (2 * K + 1) ^ 2 : ℕ) : ℝ≥0) : ℝ) ^ (M + 1) := by
        dsimp [c]
        push_cast
        rw [show 2 * M + 2 = 2 * (M + 1) by omega]
        rw [mul_pow, ← pow_mul]
  have he : M + 2 ≤ 2 * (M + 1) ^ 2 := by
    calc
      M + 2 ≤ 2 * (M + 1) := by omega
      _ ≤ 2 * (M + 1) ^ 2 := by
        apply Nat.mul_le_mul_left 2
        rw [pow_two]
        exact Nat.le_mul_of_pos_left (M + 1) (Nat.zero_lt_succ M)
  have hmain := mul_pow_le_gridLoss (A := ((16 * (2 * K + 1) ^ 2 : ℕ) : ℝ≥0))
    (K := 2) hδ0 hδ1 (B := B) (c := c) (d := (8 * (M + 2) : ℕ)) (e := M + 2)
    (by positivity) (by positivity) hB0 hBc hdc he
  rw [show ((relativePlankBandRatio n (Tube.ssfGridLen δ) : ℕ) : ℝ) =
      (8 * (M + 2) : ℕ) * B ^ (M + 2) by
    simp only [relativePlankBandRatio, relativePlankThreshold, relativePlankRounds,
      B, M, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    ring]
  exact hmain

/-- **The class-band ratio is subpolynomial.**  This is the shared workhorse of the uniformity and
factor constants below: in both of them the band ratio is the only factor depending on `δ`. -/
theorem exists_threshold_relativePlankBandRatio_le (K : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : ℝ≥0}, 0 < δ → δ ≤ δ₀ → ∀ n : ℕ, (n : ℝ) ≤ (δ : ℝ) ^ (-(K : ℝ)) →
        ((relativePlankBandRatio n (Tube.ssfGridLen δ) : ℕ) : ℝ) ≤ (δ : ℝ) ^ (-α) := by
  let A : ℝ≥0 := ((16 * (2 * K + 1) ^ 2 : ℕ) : ℝ≥0)
  have hA : 1 ≤ A := by
    dsimp [A]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by norm_num) (pow_ne_zero _ (by omega)))
  obtain ⟨δ₀, hδ₀, hδ₀1, hgrid⟩ :=
    StickyKakeya.exists_threshold_gridLoss_le A hA 2 α hα
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hδle n hn
  exact (relativePlankBandRatio_le_gridLoss K hδ (hδle.trans hδ₀1) n hn).trans
    (hgrid hδ hδle)

/-- **A fixed constant is subpolynomial.**  Used for the literal `4` of the shaded
uniformization, which does not depend on `δ`. -/
theorem exists_threshold_natCast_le_rpow (c : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : ℝ≥0}, 0 < δ → δ ≤ δ₀ → (c : ℝ) ≤ (δ : ℝ) ^ (-α) := by
  let A : ℝ≥0 := max (c : ℝ≥0) 1
  have hA : 1 ≤ A := le_max_right _ _
  have hcA : (c : ℝ≥0) ≤ A := le_max_left _ _
  obtain ⟨δ₀, hδ₀, hδ₀1, hgrid⟩ :=
    StickyKakeya.exists_threshold_gridLoss_le A hA 0 α hα
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hδle
  have hpow : (A : ℝ) ≤ (A : ℝ) ^ (Tube.ssfGridLen δ + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by exact_mod_cast hA)
      (by omega : 1 ≤ Tube.ssfGridLen δ + 1)
  have hcgrid : (c : ℝ) ≤ StickyKakeya.gridLoss A 0 δ := by
    rw [StickyKakeya.gridLoss]
    simp only [zero_mul, pow_zero, mul_one]
    have hcAR : (c : ℝ) ≤ (A : ℝ) := by exact_mod_cast hcA
    exact hcAR.trans hpow
  exact hcgrid.trans (hgrid hδ hδle)

/-- **The total loss of the relative plank selection is subpolynomial.**

The cardinality is bounded by `δ ^ (-K)` and the grid has `Tube.ssfGridLen δ ≈ log log 1/δ` levels,
so the logarithm of `relativePlankTotalLoss` is `O((log log 1/δ)^2)`, still `o(log 1/δ)`. -/
theorem exists_threshold_relativePlankTotalLoss_le (K : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : ℝ≥0}, 0 < δ → δ ≤ δ₀ → ∀ n : ℕ, (n : ℝ) ≤ (δ : ℝ) ^ (-(K : ℝ)) →
        ((relativePlankTotalLoss n (Tube.ssfGridLen δ) : ℕ) : ℝ) ≤ (δ : ℝ) ^ (-α) := by
  let A : ℝ≥0 := ((2 * (2 * K + 1) ^ 4 : ℕ) : ℝ≥0)
  have hA : 1 ≤ A := by
    dsimp [A]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by norm_num) (pow_ne_zero _ (by omega)))
  obtain ⟨δ₀, hδ₀, hδ₀1, hgrid⟩ :=
    StickyKakeya.exists_threshold_gridLoss_le A hA 4 α hα
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hδle n hn
  exact (relativePlankTotalLoss_le_gridLoss K hδ (hδle.trans hδ₀1) n hn).trans
    (hgrid hδ hδle)

/-- **The uniformity constant of the relative plank selection is subpolynomial**, given that the
incoming uniformity constant is.  The band restriction constant is a maximum, so the two sources do
not multiply; each is absorbed at half the budget. -/
theorem exists_threshold_relativePlankUniformConst_le (K : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : ℝ≥0}, 0 < δ → δ ≤ δ₀ → ∀ n : ℕ, (n : ℝ) ≤ (δ : ℝ) ^ (-(K : ℝ)) →
        ∀ Cu : ℝ≥0, (Cu : ℝ) ≤ (δ : ℝ) ^ (-(α / 2)) →
          ((max (MultiScaleFac.relativePlankBandRestrictConst Cu
              ((relativePlankBandRatio n (Tube.ssfGridLen δ) : ℕ) : ℝ≥0)) 4 : ℝ≥0) : ℝ)
            ≤ (δ : ℝ) ^ (-α) := by
  have hα2 : 0 < α / 2 := by positivity
  obtain ⟨δB, hδB, hδB1, hband⟩ :=
    exists_threshold_relativePlankBandRatio_le K (α / 2) hα2
  obtain ⟨δ4, hδ4, hδ41, hfour⟩ := exists_threshold_natCast_le_rpow 4 α hα
  let δ₀ := min δB δ4
  have hδ₀ : 0 < δ₀ := lt_min hδB hδ4
  have hδ₀1 : δ₀ ≤ 1 := (min_le_left _ _).trans hδB1
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hδle n hn Cu hCu
  have hδB_le : δ ≤ δB := hδle.trans (min_le_left _ _)
  have hδ4_le : δ ≤ δ4 := hδle.trans (min_le_right _ _)
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδle.trans hδ₀1
  have hhalf : (δ : ℝ) ^ (-(α / 2)) ≤ (δ : ℝ) ^ (-α) :=
    Real.rpow_le_rpow_of_exponent_ge hδR hδR1 (by linarith)
  have hCu' : (Cu : ℝ) ≤ (δ : ℝ) ^ (-α) := hCu.trans hhalf
  have hband' : ((relativePlankBandRatio n (Tube.ssfGridLen δ) : ℕ) : ℝ) ≤
      (δ : ℝ) ^ (-α) := (hband hδ hδB_le n hn).trans hhalf
  have hfour' := hfour hδ hδ4_le
  have hone : (1 : ℝ) ≤ (δ : ℝ) ^ (-α) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδR hδR1 (by linarith)
  rw [MultiScaleFac.relativePlankBandRestrictConst]
  push_cast
  exact max_le (max_le hCu' (max_le hband' hone)) hfour'

/-- **The factor constant of the relative plank selection is subpolynomial**, given that the
incoming factorization constant and the volume-comparability constant are.  Here the three sources
do multiply, so each is absorbed at a third of the budget. -/
theorem exists_threshold_relativePlankFactorConst_le (K : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : ℝ≥0}, 0 < δ → δ ≤ δ₀ → ∀ n : ℕ, (n : ℝ) ≤ (δ : ℝ) ^ (-(K : ℝ)) →
        ∀ C₀ Cvol : ℝ≥0, (C₀ : ℝ) ≤ (δ : ℝ) ^ (-(α / 3)) → (Cvol : ℝ) ≤ (δ : ℝ) ^ (-(α / 3)) →
          ((C₀ * ((relativePlankBandRatio n (Tube.ssfGridLen δ) : ℕ) : ℝ≥0) * Cvol : ℝ≥0) : ℝ)
            ≤ (δ : ℝ) ^ (-α) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hband⟩ :=
    exists_threshold_relativePlankBandRatio_le K (α / 3) (by positivity)
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hδle n hn C₀ Cvol hC₀ hCvol
  have hb := hband hδ hδle n hn
  push_cast
  exact mul_mul_le_rpow_neg_of_third hδ (by positivity) (by positivity) (by positivity)
    hC₀ hb hCvol

end Kakeya

end
