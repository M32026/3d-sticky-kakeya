/-
Wang--Zahl Proposition `factoringConvexSetsProp` (:1029): the structure theorem
that produces, for an arbitrary finite family of congruent convex sets, a
refinement `U'` together with a `K`-balanced, `K`-almost partitioning cover `W`
that factors `U'` from above with respect to the Katz--Tao Convex Wolff axioms
and from below with respect to the Frostman Convex Wolff axioms.

Source: `blueprint/src/WZ2/250224e_K3.tex`, Section `factorConvexSetsSec`.
  * Definition `defnOfCover` (:919): cover, `K`-almost partitioning cover,
    `K`-balanced cover;
  * Definition `factoringDefn` (:1001/:1004): factoring from above / below;
  * Proposition `factoringConvexSetsProp` (:1029);
  * Lemma `graphRefinementLemma` (:1076): the iterated graph pruning lemma the
    proof runs on.

Every branch of the source's proof of Proposition `tubeTricotProp` applies
`factoringConvexSetsProp` (:2497 and :2589, whose output is then re-described
at :2506 and used at :2602), so this is the missing input under
`tubeTricotProp`.

The cover produced here is a family of `Frame3` *boxes* rather than of John
ellipsoids.  The source's Step 3 (:1125) replaces each `W` by a congruent copy
of the ellipsoid `W_0` whose axes are the pigeonholed lengths `a_1,...,a_n`;
replacing that ellipsoid by its circumscribed box enlarges every member by a
bounded factor, which the source's own remark that "the exact shape of `K` is
not important" absorbs, and it is the box form that every downstream use needs
(at :2506 the output is described as a set of `a/d_i x b/d_i x 1` prisms).

**The output is boxes; the input is not, and cannot be made so.**  At each of
the downstream sites the family fed to this proposition is
`rescaleCarriers (tubeFrame3 _ T_rho) (fun i => (T i).carrier)`: the images
under `phi_{T_rho}` of the `delta`-tubes inside a parent tube.  A
`Tube.carrier` is `⋃ z ∈ segment x y, closedBall z delta`, a spherical
cylinder, and its image under the anisotropic `phi_{T_rho}` is an ellipsoidal
cylinder.  Neither is a box.  So a *box-input* specialisation of this
proposition is not merely inconvenient downstream, it is unsatisfiable there.
It would also not help: the source's Step 3 pigeonholes the John ellipsoids of
the covering sets `W_j in W_0` produced by Step 2's maximiser, not of the input
family, so constraining the input leaves Step 3 untouched.  See
`FactoringBoxes.lean` for what Step 3 does reduce to.
-/
module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.TubeTrichotomy

@[expose] public section

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

/-! ### Elementary facts about the box of a frame

`Frame3.box` is the convex set the source's `phi_W` normalises.  Nothing below
about it is in `Rescaling.lean`, so it is collected here.
-/

namespace Frame3

/-- The cube `[-1,1]^3`, the normalised image of every box under its own
`phi_W` (`mem_box_iff_map_mem_cube`). -/
def unitCube : Set Space3 := {y | ∀ i, |y i| ≤ 1}

theorem convex_unitCube : Convex ℝ unitCube := by
  intro x hx y hy a b ha hb hab
  simp only [unitCube, Set.mem_setOf_eq] at hx hy ⊢
  intro i
  have hxi := hx i
  have hyi := hy i
  have hval : (a • x + b • y : Space3) i = a * x i + b * y i := by
    simp
  rw [hval]
  calc |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add_le _ _
    _ = a * |x i| + b * |y i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := by gcongr
    _ = 1 := by rw [mul_one, mul_one, hab]

theorem box_eq_preimage_unitCube (F : Frame3) : F.box = F.map ⁻¹' unitCube := by
  ext z
  exact mem_box_iff_map_mem_cube z

/-- The box of a frame is convex. -/
theorem convex_box (F : Frame3) : Convex ℝ F.box := by
  rw [box_eq_preimage_unitCube]
  exact F.convex_preimage convex_unitCube

/-- `phi_W` is surjective: its diagonal part is invertible because the
half-widths are positive. -/
theorem map_surjective (F : Frame3) : Function.Surjective F.map := by
  intro y
  refine ⟨F.basis.repr.symm ((WithLp.toLp 2) fun i => y i * F.len i) + F.center, ?_⟩
  ext i
  rw [map_apply, add_sub_cancel_right, LinearIsometryEquiv.apply_symm_apply]
  have hlen : F.len i ≠ 0 := (F.len_pos i).ne'
  field_simp

/-- `phi_W` takes the box exactly onto the cube `[-1,1]^3`. -/
theorem map_image_box (F : Frame3) : F.map '' F.box = unitCube := by
  rw [box_eq_preimage_unitCube, Set.image_preimage_eq _ F.map_surjective]

end Frame3

/-! ### Covers: the two quantitative clauses of Definition `defnOfCover` -/

/-- **Wang--Zahl Definition `defnOfCover`(B)** (:928): `W` is a `K`-*almost
partitioning cover* of `U` if it is a cover and each `U in U` lies in at most
`K` members of `W`. -/
def IsAlmostPartitioningCover {ι κ : Type u} (s : Finset ι) (U : ι → Set Space3)
    (w : Finset κ) (W : κ → Set Space3) (K : ENNReal) : Prop :=
  IsCoverOf s U w W ∧
    ∀ i ∈ s,
      (((@Finset.filter κ (fun k => U i ⊆ W k) (Classical.decPred _) w).card : ENNReal)) ≤ K

/-- **Wang--Zahl Definition `defnOfCover`(D)** (:930): `W` is a `K`-*balanced
cover* of `U` if it is a cover and the numbers `|W|⁻¹ sum_{U in U[W]} |U|`,
`W in W`, all lie in a single multiplicative window of width `K`.  The window
is recorded here by its lower endpoint `L`, and the inequalities are cleared of
the division by `|W|`. -/
def IsBalancedCover {ι κ : Type u} (s : Finset ι) (U : ι → Set Space3)
    (w : Finset κ) (W : κ → Set Space3) (K : ENNReal) : Prop :=
  IsCoverOf s U w W ∧
    ∃ L : ENNReal, ∀ k ∈ w,
      L * volume (W k) ≤ ∑ i ∈ subfamilyIn s U (W k), volume (U i) ∧
        ∑ i ∈ subfamilyIn s U (W k), volume (U i) ≤ K * L * volume (W k)

/-- **Wang--Zahl Definition :1001(A)** for the Katz--Tao Convex Wolff axioms:
`W` covers `U`, and `W` itself satisfies those axioms with error `K`.  The
Frostman counterpart is `FactorsFromAboveFCW`. -/
def FactorsFromAboveCKT {ι κ : Type u} (s : Finset ι) (U : ι → Set Space3)
    (w : Finset κ) (F : κ → Frame3) (K : ENNReal) : Prop :=
  IsCoverOf s U w (fun k => (F k).box) ∧
    katzTaoConvexWolffConstantSets w (fun k => (F k).box) ≤ K

/-- **Wang--Zahl Definition :1004(B)** for the Katz--Tao Convex Wolff axioms:
`W` covers `U`, and each rescaled family `U^W` satisfies those axioms with
error `K`. -/
def FactorsFromBelowCKT {ι κ : Type u} (s : Finset ι) (U : ι → Set Space3)
    (w : Finset κ) (F : κ → Frame3) (K : ENNReal) : Prop :=
  IsCoverOf s U w (fun k => (F k).box) ∧
    ∀ k ∈ w, katzTaoConvexWolffConstantSets
        (subfamilyIn s U (F k).box) (rescaleCarriers (F k) U) ≤ K

/-! ### Lemma `graphRefinementLemma`: iterated graph pruning

Wang--Zahl Lemma `graphRefinementLemma` (:1076).  A bipartite graph is encoded
here by its edge set `E : Finset (a x b)`; the induced subgraph on `A' x B'` is
`edgeRestrict`.  This is the only genuinely combinatorial input to the proof of
Proposition `factoringConvexSetsProp`, and it is proved below.
-/

/-- The edges of `E` induced on `A' x B'`. -/
def edgeRestrict {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (A' : Finset α) (B' : Finset β) : Finset (α × β) :=
  E.filter (fun e => e.1 ∈ A' ∧ e.2 ∈ B')

/-- The edges of the induced subgraph at the left vertex `a`; its cardinality is
the degree of `a`. -/
def edgeRestrictLeft {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (A' : Finset α) (B' : Finset β) (a : α) : Finset (α × β) :=
  (edgeRestrict E A' B').filter (fun e => e.1 = a)

/-- The edges of the induced subgraph at the right vertex `b`. -/
def edgeRestrictRight {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (A' : Finset α) (B' : Finset β) (b : β) : Finset (α × β) :=
  (edgeRestrict E A' B').filter (fun e => e.2 = b)

theorem edgeRestrict_mono_left {α β : Type*} [DecidableEq α] [DecidableEq β]
    {E : Finset (α × β)} {A₁ A₂ : Finset α} (h : A₁ ⊆ A₂) (B' : Finset β) :
    edgeRestrict E A₁ B' ⊆ edgeRestrict E A₂ B' := by
  intro e he
  rw [edgeRestrict, Finset.mem_filter] at he ⊢
  exact ⟨he.1, h he.2.1, he.2.2⟩

theorem edgeRestrict_mono_right {α β : Type*} [DecidableEq α] [DecidableEq β]
    {E : Finset (α × β)} (A' : Finset α) {B₁ B₂ : Finset β} (h : B₁ ⊆ B₂) :
    edgeRestrict E A' B₁ ⊆ edgeRestrict E A' B₂ := by
  intro e he
  rw [edgeRestrict, Finset.mem_filter] at he ⊢
  exact ⟨he.1, he.2.1, h he.2.2⟩

/-- Deleting a left vertex removes exactly its edges. -/
theorem card_edgeRestrict_erase_left {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (A' : Finset α) (B' : Finset β) (a : α) :
    (edgeRestrict E A' B').card
      = (edgeRestrict E (A'.erase a) B').card + (edgeRestrictLeft E A' B' a).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := edgeRestrict E A' B') (p := fun e => e.1 = a)
  have hneg : (edgeRestrict E A' B').filter (fun e => ¬ e.1 = a)
      = edgeRestrict E (A'.erase a) B' := by
    ext e
    simp only [edgeRestrict, Finset.mem_filter, Finset.mem_erase]
    tauto
  rw [edgeRestrictLeft, ← hsplit, hneg, Nat.add_comm]

/-- Deleting a right vertex removes exactly its edges. -/
theorem card_edgeRestrict_erase_right {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (A' : Finset α) (B' : Finset β) (b : β) :
    (edgeRestrict E A' B').card
      = (edgeRestrict E A' (B'.erase b)).card + (edgeRestrictRight E A' B' b).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := edgeRestrict E A' B') (p := fun e => e.2 = b)
  have hneg : (edgeRestrict E A' B').filter (fun e => ¬ e.2 = b)
      = edgeRestrict E A' (B'.erase b) := by
    ext e
    simp only [edgeRestrict, Finset.mem_filter, Finset.mem_erase]
    tauto
  rw [edgeRestrictRight, ← hsplit, hneg, Nat.add_comm]

/-- **The pruning induction.**  Repeatedly delete a vertex of degree below its
threshold.  The accounting term charges every deletion to its own threshold,
which is what makes the total loss controllable. -/
theorem exists_pruned_subgraph {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) {dA dB : ℝ} (_hdA : 0 ≤ dA) (_hdB : 0 ≤ dB) :
    ∀ n : ℕ, ∀ A' : Finset α, ∀ B' : Finset β, A'.card + B'.card ≤ n →
      ∃ A'' ⊆ A', ∃ B'' ⊆ B',
        (∀ a ∈ A'', dA ≤ ((edgeRestrictLeft E A'' B'' a).card : ℝ)) ∧
        (∀ b ∈ B'', dB ≤ ((edgeRestrictRight E A'' B'' b).card : ℝ)) ∧
        ((edgeRestrict E A' B').card : ℝ) ≤ (edgeRestrict E A'' B'').card
          + ((A'.card : ℝ) - A''.card) * dA + ((B'.card : ℝ) - B''.card) * dB := by
  classical
  intro n
  induction n with
  | zero =>
      intro A' B' hcard
      have hA : A' = ∅ := Finset.card_eq_zero.mp (by omega)
      have hB : B' = ∅ := Finset.card_eq_zero.mp (by omega)
      refine ⟨A', Finset.Subset.refl _, B', Finset.Subset.refl _, ?_, ?_, ?_⟩
      · intro a ha; rw [hA] at ha; exact absurd ha (Finset.notMem_empty a)
      · intro b hb; rw [hB] at hb; exact absurd hb (Finset.notMem_empty b)
      · simp
  | succ n ih =>
      intro A' B' hcard
      by_cases hgoodA : ∀ a ∈ A', dA ≤ ((edgeRestrictLeft E A' B' a).card : ℝ)
      · by_cases hgoodB : ∀ b ∈ B', dB ≤ ((edgeRestrictRight E A' B' b).card : ℝ)
        · exact ⟨A', Finset.Subset.refl _, B', Finset.Subset.refl _, hgoodA, hgoodB,
            by simp⟩
        · -- a right vertex of small degree: delete it
          push Not at hgoodB
          obtain ⟨b, hbB, hblow⟩ := hgoodB
          have hcard' : A'.card + (B'.erase b).card ≤ n := by
            have := Finset.card_erase_of_mem hbB
            have hb1 : 1 ≤ B'.card := Finset.card_pos.mpr ⟨b, hbB⟩
            omega
          obtain ⟨A'', hA'', B'', hB'', hdegA, hdegB, hloss⟩ :=
            ih A' (B'.erase b) hcard'
          refine ⟨A'', hA'', B'', hB''.trans (Finset.erase_subset _ _), hdegA, hdegB, ?_⟩
          have hsplit : ((edgeRestrict E A' B').card : ℝ)
              = (edgeRestrict E A' (B'.erase b)).card
                + (edgeRestrictRight E A' B' b).card := by
            exact_mod_cast congrArg (Nat.cast : ℕ → ℝ)
              (card_edgeRestrict_erase_right E A' B' b)
          have hbcard : ((B'.erase b).card : ℝ) = (B'.card : ℝ) - 1 := by
            rw [Finset.card_erase_of_mem hbB]
            have hb1 : 1 ≤ B'.card := Finset.card_pos.mpr ⟨b, hbB⟩
            push_cast [Nat.cast_sub hb1]
            ring
          rw [hbcard] at hloss
          have hexp : ((B'.card : ℝ) - 1 - B''.card) * dB
              = ((B'.card : ℝ) - B''.card) * dB - dB := by ring
          rw [hexp] at hloss
          rw [hsplit]
          linarith [hblow.le]
      · -- a left vertex of small degree: delete it
        push Not at hgoodA
        obtain ⟨a, haA, halow⟩ := hgoodA
        have hcard' : (A'.erase a).card + B'.card ≤ n := by
          have := Finset.card_erase_of_mem haA
          have ha1 : 1 ≤ A'.card := Finset.card_pos.mpr ⟨a, haA⟩
          omega
        obtain ⟨A'', hA'', B'', hB'', hdegA, hdegB, hloss⟩ :=
          ih (A'.erase a) B' hcard'
        refine ⟨A'', hA''.trans (Finset.erase_subset _ _), B'', hB'', hdegA, hdegB, ?_⟩
        have hsplit : ((edgeRestrict E A' B').card : ℝ)
            = (edgeRestrict E (A'.erase a) B').card
              + (edgeRestrictLeft E A' B' a).card := by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℝ)
            (card_edgeRestrict_erase_left E A' B' a)
        have hacard : ((A'.erase a).card : ℝ) = (A'.card : ℝ) - 1 := by
          rw [Finset.card_erase_of_mem haA]
          have ha1 : 1 ≤ A'.card := Finset.card_pos.mpr ⟨a, haA⟩
          push_cast [Nat.cast_sub ha1]
          ring
        rw [hacard] at hloss
        have hexp : ((A'.card : ℝ) - 1 - A''.card) * dA
            = ((A'.card : ℝ) - A''.card) * dA - dA := by ring
        rw [hexp] at hloss
        rw [hsplit]
        linarith [halow.le]

/-- **Wang--Zahl Lemma `graphRefinementLemma`**
(`blueprint/src/WZ2/250224e_K3.tex:1076`).

*Let `G = (A u B, E)` be a bipartite graph.  Then there is a subgraph
`G' = (A' u B', E')` so that `#E' >= #E/2`; each vertex in `A'` has degree at
least `#E/(4 #A)`; and each vertex in `B'` has degree at least `#E/(4 #B)`.*

`G'` is the subgraph *induced* on `A' x B'`, which is what the source's proof
(iteratively removing low-degree vertices) produces and what Step 4 of the
proof of Proposition `factoringConvexSetsProp` (:1156) uses. -/
theorem graphRefinementLemma {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (E : Finset (α × β)) (hE : E ⊆ A ×ˢ B) :
    ∃ A'' ⊆ A, ∃ B'' ⊆ B,
      (E.card : ℝ) / 2 ≤ (edgeRestrict E A'' B'').card ∧
      (∀ a ∈ A'', (E.card : ℝ) / (4 * A.card)
          ≤ ((edgeRestrictLeft E A'' B'' a).card : ℝ)) ∧
      (∀ b ∈ B'', (E.card : ℝ) / (4 * B.card)
          ≤ ((edgeRestrictRight E A'' B'' b).card : ℝ)) := by
  classical
  set dA : ℝ := (E.card : ℝ) / (4 * A.card) with hdAdef
  set dB : ℝ := (E.card : ℝ) / (4 * B.card) with hdBdef
  have hdA : 0 ≤ dA := by positivity
  have hdB : 0 ≤ dB := by positivity
  obtain ⟨A'', hA'', B'', hB'', hdegA, hdegB, hloss⟩ :=
    exists_pruned_subgraph E hdA hdB (A.card + B.card) A B le_rfl
  refine ⟨A'', hA'', B'', hB'', ?_, hdegA, hdegB⟩
  -- the whole edge set is already induced on `A x B`
  have hfull : edgeRestrict E A B = E := by
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro e he
    have := Finset.mem_product.mp (hE he)
    exact Finset.mem_filter.mpr ⟨he, this.1, this.2⟩
  rw [hfull] at hloss
  -- the total loss is at most `#E/4 + #E/4`
  have hAloss : ((A.card : ℝ) - A''.card) * dA ≤ (E.card : ℝ) / 4 := by
    rcases Nat.eq_zero_or_pos A.card with h0 | hpos
    · have : A''.card = 0 := Nat.le_zero.mp (h0 ▸ Finset.card_le_card hA'')
      simp [h0, this, hdAdef]
      positivity
    · have hApos : (0 : ℝ) < A.card := by exact_mod_cast hpos
      have hle : ((A.card : ℝ) - A''.card) ≤ A.card := by
        have : (0 : ℝ) ≤ A''.card := Nat.cast_nonneg _
        linarith
      have hstep : ((A.card : ℝ) - A''.card) * dA ≤ (A.card : ℝ) * dA :=
        mul_le_mul_of_nonneg_right hle hdA
      refine hstep.trans (le_of_eq ?_)
      rw [hdAdef]
      field_simp
  have hBloss : ((B.card : ℝ) - B''.card) * dB ≤ (E.card : ℝ) / 4 := by
    rcases Nat.eq_zero_or_pos B.card with h0 | hpos
    · have : B''.card = 0 := Nat.le_zero.mp (h0 ▸ Finset.card_le_card hB'')
      simp [h0, this, hdBdef]
      positivity
    · have hBpos : (0 : ℝ) < B.card := by exact_mod_cast hpos
      have hle : ((B.card : ℝ) - B''.card) ≤ B.card := by
        have : (0 : ℝ) ≤ B''.card := Nat.cast_nonneg _
        linarith
      have hstep : ((B.card : ℝ) - B''.card) * dB ≤ (B.card : ℝ) * dB :=
        mul_le_mul_of_nonneg_right hle hdB
      refine hstep.trans (le_of_eq ?_)
      rw [hdBdef]
      field_simp
  linarith

/-! ### Named leaves of the proof

The source's proof of Proposition `factoringConvexSetsProp` runs in five steps
(:1085--:1195).  The pieces that are independent of the pigeonholing are proved
here; each carries its source line.
-/

/-- `U[W]` is monotone in the family. -/
theorem subfamilyIn_mono {ι : Type u} {s t : Finset ι} (hst : s ⊆ t)
    (U : ι → Set Space3) (W : Set Space3) :
    subfamilyIn s U W ⊆ subfamilyIn t U W := by
  intro i hi
  obtain ⟨his, hiW⟩ := mem_subfamilyIn.mp hi
  exact mem_subfamilyIn.mpr ⟨hst his, hiW⟩

/-- **`CKT` is inherited by subfamilies verbatim** (Remark
`FrostmanWolffInheritedUpwardsDownwards`(B), :980; used at :1187,
"`U' subset U_0`, so `CKT(U') <= CKT(U_0)`").  Unlike the Frostman constants,
`CKT` carries no `#U` normalisation, so no factor appears. -/
theorem katzTaoConvexWolffConstantSets_le_of_subset {ι : Type u} {s t : Finset ι}
    (hst : s ⊆ t) (U : ι → Set Space3) :
    katzTaoConvexWolffConstantSets s U ≤ katzTaoConvexWolffConstantSets t U := by
  refine sInf_le_sInf ?_
  rintro C ⟨hC0, hC⟩
  refine ⟨hC0, fun W => le_trans ?_ (hC W)⟩
  exact Finset.sum_le_sum_of_subset (subfamilyIn_mono hst U W.carrier)

/-- **`CKT >= 1` for a nonempty family of convex sets** (used at :1093, "since
`CKT(U_0) >= 1`").  The test set is the member itself. -/
theorem one_le_katzTaoConvexWolffConstantSets {ι : Type u} {s : Finset ι}
    (U : ι → Set Space3) {i : ι} (hi : i ∈ s) (hconv : Convex ℝ (U i))
    (hne : volume (U i) ≠ 0) (htop : volume (U i) ≠ ⊤) :
    1 ≤ katzTaoConvexWolffConstantSets s U := by
  refine le_sInf ?_
  rintro C ⟨_, hC⟩
  have hle : volume (U i) ≤ ∑ j ∈ subfamilyIn s U (U i), volume (U j) :=
    Finset.single_le_sum (f := fun j => volume (U j)) (fun _ _ => bot_le)
      (mem_subfamilyIn.mpr ⟨hi, subset_rfl⟩)
  have hfin : volume (U i) ≤ C * volume (U i) :=
    hle.trans (hC ⟨U i, hconv⟩)
  have hfin' : 1 * volume (U i) ≤ C * volume (U i) := by rwa [one_mul]
  exact (ENNReal.mul_le_mul_iff_left hne htop).mp hfin'

/-- **The approximate maximiser of Step 2** (:1102, `sizeOfWmCalU`).  The source
selects `W_j` maximising `#U[W]/|W|` and notes in a footnote that approximating
the maximum within a constant factor works equally well; that approximate form
is exactly the statement that `CKT` is an infimum, and it is what is proved
here.  No compactness argument is needed. -/
theorem exists_convexTestSet_of_lt_katzTao {ι : Type u} (s : Finset ι)
    (U : ι → Set Space3) {C : ENNReal} (hC0 : 0 < C)
    (hC : C < katzTaoConvexWolffConstantSets s U) :
    ∃ W : ConvexTestSet,
      C * volume W.carrier < ∑ i ∈ subfamilyIn s U W.carrier, volume (U i) := by
  by_contra hcon
  push Not at hcon
  have hle : katzTaoConvexWolffConstantSets s U ≤ C := by
    rw [katzTaoConvexWolffConstantSets]
    exact sInf_le ⟨hC0, hcon⟩
  exact absurd hle (not_le.mpr hC)

/-- The quantity minimised in Step 1 of the proof (:1090):
`exp[(log(#U/#U'))^2] CKT(U')`. -/
def step1Objective {ι : Type u} (s t : Finset ι) (U : ι → Set Space3) : ENNReal :=
  ENNReal.ofReal (Real.exp ((Real.log ((s.card : ℝ) / (t.card : ℝ))) ^ 2))
    * katzTaoConvexWolffConstantSets t U

/-- **Step 1 of the proof** (:1090): the minimiser `U_0` exists.  The
minimisation is over the nonempty subsets of a finite family, so this is a
finite minimum and needs no compactness. -/
theorem exists_step1_minimizer {ι : Type u} [DecidableEq ι] (s : Finset ι)
    (hs : s.Nonempty) (U : ι → Set Space3) :
    ∃ t : Finset ι, t ⊆ s ∧ t.Nonempty ∧
      ∀ t' : Finset ι, t' ⊆ s → t'.Nonempty →
        step1Objective s t U ≤ step1Objective s t' U := by
  classical
  set P : Finset (Finset ι) :=
    @Finset.filter (Finset ι) (fun t => t.Nonempty) (Classical.decPred _) s.powerset with hP
  have hmemP : ∀ t : Finset ι, t ∈ P ↔ (t ⊆ s ∧ t.Nonempty) := by
    intro t
    rw [hP]
    rw [@Finset.mem_filter (Finset ι) (fun t => t.Nonempty) (Classical.decPred _)]
    exact and_congr_left' Finset.mem_powerset
  have hne : P.Nonempty := ⟨s, (hmemP s).mpr ⟨Finset.Subset.refl s, hs⟩⟩
  obtain ⟨t, ht, hmin⟩ := P.exists_min_image (fun t => step1Objective s t U) hne
  obtain ⟨hts, htne⟩ := (hmemP t).mp ht
  exact ⟨t, hts, htne, fun t' hsub hne' => hmin t' ((hmemP t').mpr ⟨hsub, hne'⟩)⟩

/-- **Step 5, Conclusion (iv)** (:1189--:1195), before the rescaling is undone.

The source's derivation is
`#(U'[W])[V] <= #U'[V] <= CKT(U')|V||U|^{-1}` compared with
`#U'[W] >= K^{-1} CKT(U')|W||U|^{-1}`, giving
`#(U'[W])[V] <= K |V||W|^{-1} (#U'[W])`, "precisely the statement that
`CFC((U')^W) <= K`".  Here `m` plays the role of `CKT(U')|U|^{-1}` (the source's
constant already divided by the common volume), `hm` is the Katz--Tao bound and
`hlots` is clause (ii)'s inequality `lotsOfUinW` (:1035). -/
theorem frostmanConvexWolffConstantSets_subfamilyIn_le {ι : Type u}
    (s' : Finset ι) (U : ι → Set Space3) (W : Set Space3) {K m : ENNReal}
    (hK0 : K ≠ 0) (hKtop : K ≠ ⊤)
    (hW0 : volume W ≠ 0) (hWtop : volume W ≠ ⊤)
    (hm : ∀ V : ConvexTestSet,
      ∑ i ∈ subfamilyIn s' U V.carrier, volume (U i) ≤ m * volume V.carrier)
    (hlots : K⁻¹ * m * volume W
      ≤ ∑ i ∈ subfamilyIn s' U W, volume (U i)) :
    frostmanConvexWolffConstantSets (subfamilyIn s' U W) U ≤ K * (volume W)⁻¹ := by
  refine sInf_le ⟨?_, fun V => ?_⟩
  · exact pos_iff_ne_zero.mpr
      (mul_ne_zero hK0 (ENNReal.inv_ne_zero.mpr hWtop))
  · -- the left-hand side is bounded by the Katz--Tao estimate on the big family
    have hstep : ∑ i ∈ subfamilyIn (subfamilyIn s' U W) U V.carrier, volume (U i)
        ≤ m * volume V.carrier :=
      le_trans (Finset.sum_le_sum_of_subset
        (subfamilyIn_mono (subfamilyIn_subset s' U W) U V.carrier)) (hm V)
    refine hstep.trans ?_
    calc m * volume V.carrier
        = K * (volume W)⁻¹ * volume V.carrier * (K⁻¹ * m * volume W) := by
          rw [show K * (volume W)⁻¹ * volume V.carrier * (K⁻¹ * m * volume W)
              = (K * K⁻¹) * ((volume W)⁻¹ * volume W) * (m * volume V.carrier) from by
            ring, ENNReal.mul_inv_cancel hK0 hKtop,
            ENNReal.inv_mul_cancel hW0 hWtop, one_mul, one_mul]
      _ ≤ K * (volume W)⁻¹ * volume V.carrier
            * ∑ i ∈ subfamilyIn s' U W, volume (U i) := by gcongr

/-- **Step 5, Conclusion (iii)** (:1180--:1185): the cover itself satisfies the
Katz--Tao Convex Wolff axioms.

The source's derivation compares
`#U'[V] >= kap^{-1} sum_{W in W[V]} #U'[W] >= kap^{-1} beta (#W[V])` (:1181,
`lowerBdUInV`, which uses that each `U in U'` lies in at most `kap` of the
classes) with `#U'[V] <= CKT(U')|V||U|^{-1}` (:1184, `upperBdUInV`), and
concludes `#W[V] <= K|V||W_0|^{-1}`.

Here `beta` is the lower bound of clause (ii) on each class, `m` is the
Katz--Tao bound on `U'` (already divided by the common volume `|U|`), `vW` is
an upper bound for the common volume `|W_0|`, and `hC` is the resulting
arithmetic `kap * m * vW <= C * beta`.  The double counting is done in the
volume language, so no congruence of the `U` is needed. -/
theorem katzTaoConvexWolffConstantSets_cover_le {ι κ : Type u}
    (s' : Finset ι) (U : ι → Set Space3) (w : Finset κ) (W : κ → Set Space3)
    {kap beta m vW C : ENNReal}
    (hbeta0 : beta ≠ 0) (hbetatop : beta ≠ ⊤) (hC0 : 0 < C)
    (hmulti : ∀ i ∈ s',
      ((@Finset.filter κ (fun k => U i ⊆ W k) (Classical.decPred _) w).card : ENNReal)
        ≤ kap)
    (hbeta : ∀ k ∈ w, beta ≤ ∑ i ∈ subfamilyIn s' U (W k), volume (U i))
    (hm : ∀ V : ConvexTestSet,
      ∑ i ∈ subfamilyIn s' U V.carrier, volume (U i) ≤ m * volume V.carrier)
    (hvW : ∀ k ∈ w, volume (W k) ≤ vW)
    (hC : kap * m * vW ≤ C * beta) :
    katzTaoConvexWolffConstantSets w W ≤ C := by
  classical
  refine sInf_le ⟨hC0, fun V => ?_⟩
  set A : Finset κ := subfamilyIn w W V.carrier with hA
  have hAw : A ⊆ w := subfamilyIn_subset w W V.carrier
  -- the count of classes inside `V` is bounded below by `beta`
  have hlow : beta * (A.card : ENNReal)
      ≤ ∑ k ∈ A, ∑ i ∈ subfamilyIn s' U (W k), volume (U i) := by
    calc beta * (A.card : ENNReal) = ∑ _k ∈ A, beta := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ k ∈ A, ∑ i ∈ subfamilyIn s' U (W k), volume (U i) :=
          Finset.sum_le_sum fun k hk => hbeta k (hAw hk)
  -- double counting: each `U` is counted at most `kap` times
  have hcount : ∀ i : ι,
      ((@Finset.filter κ (fun k => U i ⊆ W k) (Classical.decPred _) A).card : ENNReal)
        * volume (U i)
      = ∑ k ∈ A, (if U i ⊆ W k then volume (U i) else 0) := by
    intro i
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hswap : ∑ k ∈ A, ∑ i ∈ subfamilyIn s' U (W k), volume (U i)
      = ∑ i ∈ s',
        ((@Finset.filter κ (fun k => U i ⊆ W k) (Classical.decPred _) A).card : ENNReal)
          * volume (U i) := by
    have h1 : ∀ k, ∑ i ∈ subfamilyIn s' U (W k), volume (U i)
        = ∑ i ∈ s', (if U i ⊆ W k then volume (U i) else 0) := by
      intro k
      rw [subfamilyIn, ← Finset.sum_filter]
    simp only [h1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (hcount i).symm
  -- outside `U'[V]` the count vanishes
  have hvanish : ∀ i ∈ s', i ∉ subfamilyIn s' U V.carrier →
      ((@Finset.filter κ (fun k => U i ⊆ W k) (Classical.decPred _) A).card : ENNReal)
        * volume (U i) = 0 := by
    intro i his hiV
    have hempty : (@Finset.filter κ (fun k => U i ⊆ W k) (Classical.decPred _) A) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun k hk => ?_
      have hk' := (@Finset.mem_filter κ (fun k => U i ⊆ W k) (Classical.decPred _) _ _).mp hk
      have hkA := mem_subfamilyIn.mp (hA ▸ hk'.1)
      exact hiV (mem_subfamilyIn.mpr ⟨his, hk'.2.trans hkA.2⟩)
    simp [hempty]
  have hkap : ∑ i ∈ s',
      ((@Finset.filter κ (fun k => U i ⊆ W k) (Classical.decPred _) A).card : ENNReal)
        * volume (U i)
      ≤ kap * ∑ i ∈ subfamilyIn s' U V.carrier, volume (U i) := by
    rw [← Finset.sum_subset (subfamilyIn_subset s' U V.carrier) hvanish, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have his := (mem_subfamilyIn.mp hi).1
    refine mul_le_mul_right' (le_trans ?_ (hmulti i his)) _
    exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card
      (Finset.filter_subset_filter _ hAw))
  -- assemble
  have hmain : beta * (A.card : ENNReal) ≤ kap * (m * volume V.carrier) :=
    le_trans (le_trans hlow (le_of_eq hswap))
      (le_trans hkap (mul_le_mul_left' (hm V) kap))
  have hgoal : ∑ k ∈ A, volume (W k) ≤ (A.card : ENNReal) * vW := by
    calc ∑ k ∈ A, volume (W k) ≤ ∑ _k ∈ A, vW :=
          Finset.sum_le_sum fun k hk => hvW k (hAw hk)
      _ = (A.card : ENNReal) * vW := by rw [Finset.sum_const, nsmul_eq_mul]
  refine hgoal.trans ?_
  refine (ENNReal.mul_le_mul_iff_right hbeta0 hbetatop).mp ?_
  calc beta * ((A.card : ENNReal) * vW) = beta * (A.card : ENNReal) * vW := by ring
    _ ≤ kap * (m * volume V.carrier) * vW := by gcongr
    _ = kap * m * vW * volume V.carrier := by ring
    _ ≤ C * beta * volume V.carrier := by gcongr
    _ = beta * (C * volume V.carrier) := by ring

/-! ### The volume of the normalised cube -/

/-- The cube `[-1,1]^3` has volume `8`. -/
theorem volume_unitCube : volume Frame3.unitCube = 8 := by
  have hset : Frame3.unitCube
      = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹' (Set.univ.pi fun _ => Set.Icc (-1 : ℝ) 1) := by
    ext y
    simp only [Frame3.unitCube, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, forall_const, Set.mem_Icc]
    exact forall_congr' fun i => abs_le
  have hmeas : MeasurableSet (Set.univ.pi fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  rw [hset, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage hmeas.nullMeasurableSet,
    volume_pi_pi]
  simp only [Real.volume_Icc]
  norm_num

theorem one_le_volume_unitCube : 1 ≤ volume Frame3.unitCube := by
  rw [volume_unitCube]; norm_num

/-- **Conclusion (iv) of Proposition `factoringConvexSetsProp`, with the
rescaling undone** (:1195: "This is precisely the statement that
`CFC((U')^W) <= K`").

Given the Katz--Tao upper bound `hm` on `U'` and clause (ii)'s counting
inequality `hlots`, the rescaled family `(U')^W` obeys the Frostman Convex
Wolff axioms with error `K`.  The Jacobian of `phi_W` and the volume `|W|`
cancel against each other exactly: `volumeFactor * |W| = |[-1,1]^3| = 8`, so
the bound actually obtained is `K/8`. -/
theorem frostmanConvexWolffConstantSets_rescale_le {ι : Type u} (F : Frame3)
    (s' : Finset ι) (U : ι → Set Space3) {K m : ENNReal}
    (hK0 : K ≠ 0) (hKtop : K ≠ ⊤)
    (hW0 : volume F.box ≠ 0) (hWtop : volume F.box ≠ ⊤)
    (hm : ∀ V : ConvexTestSet,
      ∑ i ∈ subfamilyIn s' U V.carrier, volume (U i) ≤ m * volume V.carrier)
    (hlots : K⁻¹ * m * volume F.box
      ≤ ∑ i ∈ subfamilyIn s' U F.box, volume (U i)) :
    frostmanConvexWolffConstantSets (subfamilyIn s' U F.box) (rescaleCarriers F U)
      ≤ K := by
  have hkey := frostmanConvexWolffConstantSets_subfamilyIn_le s' U F.box
    hK0 hKtop hW0 hWtop hm hlots
  have hres := frostmanConvexWolffConstantSets_rescale F (subfamilyIn s' U F.box) U
  have hcube : F.volumeFactor * volume F.box = volume Frame3.unitCube := by
    rw [← F.volume_image_map' F.box, F.map_image_box]
  have h1 : frostmanConvexWolffConstantSets (subfamilyIn s' U F.box)
      (rescaleCarriers F U) * F.volumeFactor ≤ K * (volume F.box)⁻¹ := by
    rw [hres]; exact hkey
  calc frostmanConvexWolffConstantSets (subfamilyIn s' U F.box) (rescaleCarriers F U)
      ≤ frostmanConvexWolffConstantSets (subfamilyIn s' U F.box) (rescaleCarriers F U)
          * (F.volumeFactor * volume F.box) := by
        rw [hcube]
        exact le_mul_of_one_le_right' one_le_volume_unitCube
    _ = frostmanConvexWolffConstantSets (subfamilyIn s' U F.box) (rescaleCarriers F U)
          * F.volumeFactor * volume F.box := by ring
    _ ≤ K * (volume F.box)⁻¹ * volume F.box := by gcongr
    _ = K := by rw [mul_assoc, ENNReal.inv_mul_cancel hW0 hWtop, mul_one]

/-! ### The error constant -/

/-- The error constant of Proposition `factoringConvexSetsProp` (:1029) in
dimension `n = 3`: `K = 100^3 exp(100 sqrt(log(d^{-1} #U)))`.  The source notes
that its exact shape does not matter; what matters is that
`#U <= d^{-100}` forces `K <~~_d 1`. -/
def factoringError (δ : ℝ) (N : ℕ) : ℝ :=
  100 ^ (3 : ℕ) * Real.exp (100 * Real.sqrt (Real.log (δ⁻¹ * N)))

theorem one_le_factoringError (δ : ℝ) (N : ℕ) : 1 ≤ factoringError δ N := by
  rw [factoringError]
  have h1 : (1 : ℝ) ≤ 100 ^ (3 : ℕ) := by norm_num
  have h2 : (1 : ℝ) ≤ Real.exp (100 * Real.sqrt (Real.log (δ⁻¹ * N))) :=
    Real.one_le_exp (by positivity)
  nlinarith

theorem factoringError_pos (δ : ℝ) (N : ℕ) : 0 < factoringError δ N :=
  lt_of_lt_of_le one_pos (one_le_factoringError δ N)

/-! ### Proposition `factoringConvexSetsProp` -/



/-! ### Non-vacuity of the conclusion bundle

A hypothesis bundle nobody satisfies makes a proposition vacuously true while
`#print axioms` sees nothing, and the same is true of a conclusion bundle that
is internally inconsistent: `factoringConvexSetsProp` would then be
unprovable-but-innocent-looking.  The certificates below exhibit an explicit
**nonempty** family `U` and an explicit **nonempty** cover `W` satisfying every
hypothesis and every conclusion of the proposition simultaneously.
-/

/-- The cube frame of half-width `d` at the origin, in the standard axes. -/
def cubeFrame (δ : ℝ) (hδ : 0 < δ) : Frame3 where
  center := 0
  basis := EuclideanSpace.basisFun (Fin 3) ℝ
  len := fun _ => δ
  len_pos := fun _ => hδ

@[simp] theorem cubeFrame_len (δ : ℝ) (hδ : 0 < δ) :
    (cubeFrame δ hδ).len = fun _ => δ := rfl

theorem mem_cubeFrame_box_iff {δ : ℝ} (hδ : 0 < δ) (z : Space3) :
    z ∈ (cubeFrame δ hδ).box ↔ ∀ i, |z i| ≤ δ := by
  simp [Frame3.box, cubeFrame, EuclideanSpace.basisFun_repr]

/-- The cube of half-width `d` sits inside the unit ball once `d <= 1/2`. -/
theorem cubeFrame_box_subset_closedBall {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    (cubeFrame δ hδ).box ⊆ Metric.closedBall (0 : Space3) 1 := by
  intro z hz
  rw [mem_cubeFrame_box_iff] at hz
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  refine Real.sqrt_le_sqrt ?_
  have hbound : ∀ i : Fin 3, ‖z i‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    intro i
    have h1 : ‖z i‖ ≤ 1 / 2 := (Real.norm_eq_abs _ ▸ hz i).trans hδ2
    have h0 : (0 : ℝ) ≤ ‖z i‖ := norm_nonneg _
    nlinarith
  calc ∑ i : Fin 3, ‖z i‖ ^ 2 ≤ ∑ _i : Fin 3, (1 / 2 : ℝ) ^ 2 :=
        Finset.sum_le_sum fun i _ => hbound i
    _ ≤ 1 := by norm_num

/-- The ball of radius `d` sits inside the cube of half-width `d`. -/
theorem closedBall_subset_cubeFrame_box {δ : ℝ} (hδ : 0 < δ) :
    Metric.closedBall (0 : Space3) δ ⊆ (cubeFrame δ hδ).box := by
  intro z hz
  rw [mem_cubeFrame_box_iff]
  intro i
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  calc |z i| = ‖z i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖z‖ := PiLp.norm_apply_le z i
    _ ≤ δ := hz

/-- The cube of half-width `d` is compact. -/
theorem isCompact_cubeFrame_box {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    IsCompact (cubeFrame δ hδ).box := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Space3) 1) ?_
    (cubeFrame_box_subset_closedBall hδ hδ2)
  have hset : (cubeFrame δ hδ).box = ⋂ i : Fin 3, {z : Space3 | |z i| ≤ δ} := by
    ext z
    simp [mem_cubeFrame_box_iff hδ, Set.mem_iInter]
  rw [hset]
  refine isClosed_iInter fun i => ?_
  exact isClosed_le ((EuclideanSpace.proj i).continuous.abs) continuous_const

theorem closedBall_one_subset_unitCube :
    Metric.closedBall (0 : Space3) 1 ⊆ Frame3.unitCube := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  intro i
  calc |z i| = ‖z i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖z‖ := PiLp.norm_apply_le z i
    _ ≤ 1 := hz

theorem unitCube_subset_closedBall :
    Frame3.unitCube ⊆ Metric.closedBall (0 : Space3) 2 := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  rw [show (2 : ℝ) = Real.sqrt 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  refine Real.sqrt_le_sqrt ?_
  have hbound : ∀ i : Fin 3, ‖z i‖ ^ 2 ≤ (1 : ℝ) := by
    intro i
    have h1 : ‖z i‖ ≤ 1 := Real.norm_eq_abs _ ▸ hz i
    have h0 : (0 : ℝ) ≤ ‖z i‖ := norm_nonneg _
    nlinarith
  calc ∑ i : Fin 3, ‖z i‖ ^ 2 ≤ ∑ _i : Fin 3, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => hbound i
    _ ≤ 4 := by norm_num

theorem volume_unitCube_ne_zero : volume Frame3.unitCube ≠ 0 := by
  rw [volume_unitCube]; norm_num

theorem volume_unitCube_ne_top : volume Frame3.unitCube ≠ ⊤ := by
  rw [volume_unitCube]; norm_num



/-- The Katz--Tao convex Wolff constant of a family with at most one member is
at most `1`: any convex test set that contains the member has at least its
volume. -/
theorem katzTaoConvexWolffConstantSets_le_one_of_subsingleton {ι : Type u}
    (s : Finset ι) (U : ι → Set Space3) (hs : ∀ i ∈ s, ∀ j ∈ s, i = j) :
    katzTaoConvexWolffConstantSets s U ≤ 1 := by
  refine sInf_le ⟨one_pos, fun W => ?_⟩
  rcases Finset.eq_empty_or_nonempty (subfamilyIn s U W.carrier) with he | ⟨i₀, hi₀⟩
  · simp [he]
  · have hi₀' := mem_subfamilyIn.mp hi₀
    have hsingle : subfamilyIn s U W.carrier = {i₀} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hi₀, fun j hj => hs j (mem_subfamilyIn.mp hj).1 i₀ hi₀'.1⟩
    rw [hsingle, Finset.sum_singleton, one_mul]
    exact measure_mono hi₀'.2

/-- **The conclusion bundle of `factoringConvexSetsProp` is satisfiable, with a
nonempty family and a nonempty cover.**

Every hypothesis and every conclusion of the proposition is exhibited
simultaneously for the one-element family `U = {Q}`, `Q` the cube of half-width
`d`, covered by the one-element family `W = {Q}`.  The error `K` is
existentially quantified and finite, which is what rules out an inconsistent
bundle; the proposition's own `K` is larger than the `K` produced here as soon
as `d` is small, since `factoringError` grows. -/
theorem factoringConvexSets_bundle_satisfiable {δ : ℝ} (hδ0 : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    ∃ (K : ENNReal) (s : Finset Unit) (U : Unit → Set Space3) (vU : ENNReal)
      (w : Finset Unit) (F : Unit → Frame3),
      K = ENNReal.ofReal (factoringError δ s.card) ∧
      1 ≤ K ∧ K ≠ ⊤ ∧ s.Nonempty ∧ w.Nonempty ∧ vU ≠ 0 ∧ vU ≠ ⊤ ∧
      (∀ i ∈ s, Convex ℝ (U i)) ∧
      (∀ i ∈ s, IsCompact (U i)) ∧
      (∀ i ∈ s, U i ⊆ Metric.closedBall 0 1) ∧
      (∀ i ∈ s, ∃ c : Space3, Metric.closedBall c δ ⊆ U i) ∧
      (∀ i ∈ s, ∀ j ∈ s, ∃ f : Space3 ≃ᵃⁱ[ℝ] Space3, f '' U i = U j) ∧
      (∀ i ∈ s, volume (U i) = vU) ∧
      (∃ len : Fin 3 → ℝ, ∀ k ∈ w, (F k).len = len) ∧
      K⁻¹ * (s.card : ENNReal) ≤ (s.card : ENNReal) ∧
      IsBalancedCover s U w (fun k => (F k).box) K ∧
      IsAlmostPartitioningCover s U w (fun k => (F k).box) K ∧
      (∀ k ∈ w, K⁻¹ * katzTaoConvexWolffConstantSets s U * volume (F k).box
          ≤ ((subfamilyIn s U (F k).box).card : ENNReal) * vU) ∧
      FactorsFromAboveCKT s U w F K ∧
      FactorsFromBelowFCW s U w F K := by
  classical
  set Q : Frame3 := cubeFrame δ hδ0 with hQ
  set vU : ENNReal := volume Q.box with hvU
  have hvU0 : vU ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le ?_
      (measure_mono (closedBall_subset_cubeFrame_box hδ0)))
    exact Metric.measure_closedBall_pos volume (0 : Space3) hδ0
  have hvUtop : vU ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne
      (measure_mono (cubeFrame_box_subset_closedBall hδ0 hδ2))
  set K : ENNReal := ENNReal.ofReal (factoringError δ 1) with hK
  have hK1 : 1 ≤ K := by
    rw [hK, show (1 : ENNReal) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
    exact ENNReal.ofReal_le_ofReal (one_le_factoringError δ 1)
  have hKtop : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have hKinv : K⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hK1
  -- the family and the cover
  refine ⟨K, {()}, fun _ => Q.box, vU, {()}, fun _ => Q, by simp [hK], hK1, hKtop,
    ⟨(), Finset.mem_singleton_self _⟩, ⟨(), Finset.mem_singleton_self _⟩,
    hvU0, hvUtop, fun _ _ => Q.convex_box, fun _ _ => isCompact_cubeFrame_box hδ0 hδ2,
    fun _ _ => cubeFrame_box_subset_closedBall hδ0 hδ2,
    fun _ _ => ⟨0, closedBall_subset_cubeFrame_box hδ0⟩,
    fun _ _ _ _ => ⟨AffineIsometryEquiv.refl ℝ Space3, by simp⟩,
    fun _ _ => rfl, ⟨fun _ => δ, fun _ _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (i) the refinement keeps all of the family
  · exact mul_le_of_le_one_left' hKinv
  all_goals
    have hcov : IsCoverOf ({()} : Finset Unit) (fun _ => Q.box) ({()} : Finset Unit)
        (fun _ => Q.box) := fun i _ => ⟨(), Finset.mem_singleton_self _, subset_rfl⟩
    have hsub : subfamilyIn ({()} : Finset Unit) (fun _ => Q.box) Q.box = {()} := by
      ext i; simp [mem_subfamilyIn]
    have hsum : ∑ _i ∈ subfamilyIn ({()} : Finset Unit) (fun _ => Q.box) Q.box,
        volume Q.box = volume Q.box := by rw [hsub]; simp
    have hCKT : katzTaoConvexWolffConstantSets ({()} : Finset Unit)
        (fun _ => Q.box) ≤ 1 :=
      katzTaoConvexWolffConstantSets_le_one_of_subsingleton _ _
        (fun i _ j _ => Subsingleton.elim i j)
    first
      | -- (ii) balanced cover, with the window `[|W|, K |W|]`
        (refine ⟨hcov, 1, fun k _ => ⟨?_, ?_⟩⟩
         · rw [one_mul, hsum]
         · rw [hsum, mul_one]
           calc volume Q.box = 1 * volume Q.box := (one_mul _).symm
             _ ≤ K * volume Q.box := by gcongr)
      | -- (ii) almost partitioning cover: each member lies in exactly one box
        (refine ⟨hcov, fun i _ => le_trans ?_ hK1⟩
         have hc : (@Finset.filter Unit (fun k => Q.box ⊆ Q.box)
             (Classical.decPred _) {()}).card ≤ 1 :=
           le_trans (Finset.card_filter_le _ _) (by simp)
         exact_mod_cast hc)
      | -- (ii) the counting inequality `lotsOfUinW`
        (intro k _
         rw [hsub]
         simp only [Finset.card_singleton, Nat.cast_one, one_mul, hvU]
         exact mul_le_of_le_one_left' (mul_le_one' hKinv hCKT))
      | -- (iii) factoring from above, Katz--Tao
        exact ⟨hcov, le_trans hCKT hK1⟩
      | -- (iv) factoring from below, Frostman
        (refine ⟨hcov, fun k _ => ?_⟩
         refine le_trans (frostmanConvexWolffConstantSets_le_inv _ _
           volume_unitCube_ne_zero volume_unitCube_ne_top (fun i _ => ?_)) ?_
         · rw [rescaleCarriers_apply, Q.map_image_box]
         · exact le_trans (ENNReal.inv_le_one.mpr one_le_volume_unitCube) hK1)

end

end Kakeya.WangZahl

#print axioms Kakeya.WangZahl.Frame3.convex_unitCube
#print axioms Kakeya.WangZahl.Frame3.convex_box
#print axioms Kakeya.WangZahl.Frame3.map_surjective
#print axioms Kakeya.WangZahl.Frame3.map_image_box
#print axioms Kakeya.WangZahl.card_edgeRestrict_erase_left
#print axioms Kakeya.WangZahl.card_edgeRestrict_erase_right
#print axioms Kakeya.WangZahl.exists_pruned_subgraph
#print axioms Kakeya.WangZahl.graphRefinementLemma
#print axioms Kakeya.WangZahl.katzTaoConvexWolffConstantSets_le_of_subset
#print axioms Kakeya.WangZahl.one_le_katzTaoConvexWolffConstantSets
#print axioms Kakeya.WangZahl.exists_convexTestSet_of_lt_katzTao
#print axioms Kakeya.WangZahl.exists_step1_minimizer
#print axioms Kakeya.WangZahl.frostmanConvexWolffConstantSets_subfamilyIn_le
#print axioms Kakeya.WangZahl.katzTaoConvexWolffConstantSets_cover_le
#print axioms Kakeya.WangZahl.volume_unitCube
#print axioms Kakeya.WangZahl.frostmanConvexWolffConstantSets_rescale_le
#print axioms Kakeya.WangZahl.one_le_factoringError
#print axioms Kakeya.WangZahl.isCompact_cubeFrame_box
#print axioms Kakeya.WangZahl.cubeFrame_box_subset_closedBall
#print axioms Kakeya.WangZahl.closedBall_subset_cubeFrame_box
#print axioms Kakeya.WangZahl.volume_unitCube_ne_zero
#print axioms Kakeya.WangZahl.volume_unitCube_ne_top
#print axioms Kakeya.WangZahl.katzTaoConvexWolffConstantSets_le_one_of_subsingleton
#print axioms Kakeya.WangZahl.factoringConvexSets_bundle_satisfiable
