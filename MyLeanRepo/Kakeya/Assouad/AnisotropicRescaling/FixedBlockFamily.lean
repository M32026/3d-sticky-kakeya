import MyLeanRepo.Kakeya.Assouad.Statements

/-!
# Fixed-card block families

Flatten one fixed-card tube family for each block index.  The resulting
product indexing retains the block and slot projections explicitly, so
relation-valued induced shadings can refer to a block without inventing a
single containing parent tube.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Flatten one `m`-tube family for each of `n` block indices. -/
def flattenFixedBlocks
    {rho : ℝ} {n m : ℕ}
    (block : Fin n → Kakeya.Streamlined.TubeFamily rho)
    (hcard : ∀ j, (block j).card = m) :
    Kakeya.Streamlined.TubeFamily rho where
  card := n * m
  tube q :=
    let pair := finProdFinEquiv.symm q
    (block pair.1).tube (Fin.cast (hcard pair.1).symm pair.2)

@[simp] lemma flattenFixedBlocks_card
    {rho : ℝ} {n m : ℕ}
    (block : Fin n → Kakeya.Streamlined.TubeFamily rho)
    (hcard : ∀ j, (block j).card = m) :
    (flattenFixedBlocks block hcard).card = n * m := rfl

/-- Block index underlying one flattened fixed-block index. -/
def fixedBlockIndex {n m : ℕ} (q : Fin (n * m)) : Fin n :=
  (finProdFinEquiv.symm q).1

/-- Slot index underlying one flattened fixed-block index. -/
def fixedBlockSlot {n m : ℕ} (q : Fin (n * m)) : Fin m :=
  (finProdFinEquiv.symm q).2

@[simp] lemma fixedBlockIndex_finProdFinEquiv
    {n m : ℕ} (j : Fin n) (k : Fin m) :
    fixedBlockIndex (finProdFinEquiv (j, k)) = j := by
  simp [fixedBlockIndex]

@[simp] lemma fixedBlockSlot_finProdFinEquiv
    {n m : ℕ} (j : Fin n) (k : Fin m) :
    fixedBlockSlot (finProdFinEquiv (j, k)) = k := by
  simp [fixedBlockSlot]

/-- A flattened tube is exactly its recorded block member. -/
lemma flattenFixedBlocks_tube
    {rho : ℝ} {n m : ℕ}
    (block : Fin n → Kakeya.Streamlined.TubeFamily rho)
    (hcard : ∀ j, (block j).card = m)
    (j : Fin n) (k : Fin m) :
    (flattenFixedBlocks block hcard).tube
        (finProdFinEquiv (j, k)) =
      (block j).tube (Fin.cast (hcard j).symm k) := by
  have hpair :
      finProdFinEquiv.symm (finProdFinEquiv (j, k)) = (j, k) :=
    finProdFinEquiv.left_inv (j, k)
  change
    (block (finProdFinEquiv.symm
      (finProdFinEquiv (j, k))).1).tube
        (Fin.cast
          (hcard (finProdFinEquiv.symm
            (finProdFinEquiv (j, k))).1).symm
          (finProdFinEquiv.symm
            (finProdFinEquiv (j, k))).2) =
      (block j).tube (Fin.cast (hcard j).symm k)
  rw [hpair]

/-- Arbitrary-index version of `flattenFixedBlocks_tube`. -/
lemma flattenFixedBlocks_tube_block_slot
    {rho : ℝ} {n m : ℕ}
    (block : Fin n → Kakeya.Streamlined.TubeFamily rho)
    (hcard : ∀ j, (block j).card = m)
    (q : Fin (n * m)) :
    (flattenFixedBlocks block hcard).tube q =
      (block (fixedBlockIndex q)).tube
        (Fin.cast (hcard (fixedBlockIndex q)).symm
          (fixedBlockSlot q)) := by
  rfl

/-- Every member of one block occurs in the flattened family. -/
lemma block_union_subset_flattenFixedBlocks
    {rho : ℝ} {n m : ℕ}
    (block : Fin n → Kakeya.Streamlined.TubeFamily rho)
    (hcard : ∀ j, (block j).card = m)
    (j : Fin n) :
    (block j).toBodyFamily.union ⊆
      (flattenFixedBlocks block hcard).toBodyFamily.union := by
  intro point hpoint
  rcases hpoint with ⟨k, hk⟩
  change point ∈ ((block j).tube k).carrier at hk
  let slot : Fin m := Fin.cast (hcard j) k
  change ∃ q : Fin (n * m),
    point ∈ ((flattenFixedBlocks block hcard).tube q).carrier
  refine ⟨finProdFinEquiv (j, slot), ?_⟩
  rw [flattenFixedBlocks_tube]
  simpa [slot] using hk

/-- A block-union cover induces a cover by the flattened family union. -/
lemma family_union_subset_flattenFixedBlocks
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    {n m : ℕ}
    (parent : Fin fine.card → Fin n)
    (block : Fin n → Kakeya.Streamlined.TubeFamily rho)
    (hcard : ∀ j, (block j).card = m)
    (hcover : ∀ i,
      (fine.tube i).carrier ⊆
        (block (parent i)).toBodyFamily.union) :
    fine.toBodyFamily.union ⊆
      (flattenFixedBlocks block hcard).toBodyFamily.union := by
  intro point hpoint
  rcases hpoint with ⟨i, hi⟩
  exact block_union_subset_flattenFixedBlocks
    block hcard (parent i) (hcover i hi)

/-- Flattening preserves a uniform basepoint bound on all block members. -/
lemma flattenFixedBlocks_hasBoundedBase
    {rho R : ℝ} {n m : ℕ}
    (block : Fin n → Kakeya.Streamlined.TubeFamily rho)
    (hcard : ∀ j, (block j).card = m)
    (hbase : ∀ j, ∀ k : Fin (block j).card,
      ‖((block j).tube k).base‖ ≤ R) :
    HasBoundedBase (flattenFixedBlocks block hcard) R := by
  intro q
  rw [flattenFixedBlocks_tube_block_slot]
  exact hbase _ _

/-- Flattening preserves the vertical chart on all block members. -/
lemma flattenFixedBlocks_isInVerticalChart
    {rho : ℝ} {n m : ℕ}
    (block : Fin n → Kakeya.Streamlined.TubeFamily rho)
    (hcard : ∀ j, (block j).card = m)
    (hvertical : ∀ j, ∀ k : Fin (block j).card,
      (1 / 2 : ℝ) ≤ |((block j).tube k).direction (2 : Fin 3)|) :
    IsInVerticalChart (flattenFixedBlocks block hcard) := by
  intro q
  rw [flattenFixedBlocks_tube_block_slot]
  exact hvertical _ _

/-- Flattening preserves a blockwise supporting-line provenance statement. -/
lemma flattenFixedBlocks_axis
    {rho : ℝ} {n m : ℕ}
    (block : Fin n → Kakeya.Streamlined.TubeFamily rho)
    (hcard : ∀ j, (block j).card = m)
    (axis : Fin n → Set Point3)
    (haxis : ∀ j, ∀ k : Fin (block j).card,
      tubeAxisLine ((block j).tube k) = axis j)
    (q : Fin (n * m)) :
    tubeAxisLine ((flattenFixedBlocks block hcard).tube q) =
      axis (fixedBlockIndex q) := by
  rw [flattenFixedBlocks_tube_block_slot]
  exact haxis _ _

/--
Relation connecting a fine index to every flattened member of its assigned
block.
-/
def fixedBlockRelation
    {fineCard n m : ℕ}
    (parent : Fin fineCard → Fin n)
    (i : Fin fineCard) (q : Fin (n * m)) : Prop :=
  fixedBlockIndex q = parent i

@[simp] lemma fixedBlockRelation_finProdFinEquiv
    {fineCard n m : ℕ}
    (parent : Fin fineCard → Fin n)
    (i : Fin fineCard) (j : Fin n) (k : Fin m) :
    fixedBlockRelation parent i (finProdFinEquiv (j, k)) ↔
      j = parent i := by
  simp [fixedBlockRelation]

/--
Dependent package returned by the selected-scale four-block assembly.

The flattened family and relation are derived definitions below, preventing
downstream code from repeating product-index casts.
-/
structure SelectedScaleFourBlockData
    {delta : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (rho : ℝ) where
  selected : Finset (Fin fine.card)
  parent : Fin fine.card → Fin selected.card
  block : Fin selected.card → Kakeya.Streamlined.TubeFamily rho
  envelope : Fin selected.card → Kakeya.Streamlined.Body
  selected_distinct :
    ∀ i ∈ selected, ∀ j ∈ selected, i ≠ j →
      (fine.tube i).EssentiallyDistinct (fine.tube j)
  representative_conflict :
    ∀ i,
      ¬(fine.tube i).EssentiallyDistinct
        (fine.tube (selected.equivFin.symm (parent i)).1)
  parent_surjective : Function.Surjective parent
  block_card : ∀ j, (block j).card = 4
  block_distinct : ∀ j, (block j).IsEssentiallyDistinct
  block_axis :
    ∀ j, ∀ k : Fin (block j).card,
      tubeAxisLine ((block j).tube k) =
        tubeAxisLine (fine.tube (selected.equivFin.symm j).1)
  block_vertical :
    ∀ j, ∀ k : Fin (block j).card,
      |((block j).tube k).direction (2 : Fin 3)| =
        |(fine.tube
          (selected.equivFin.symm j).1).direction (2 : Fin 3)|
  block_base :
    ∀ j, ∀ k : Fin (block j).card,
      ‖((block j).tube k).base‖ ≤
        ‖(fine.tube (selected.equivFin.symm j).1).base‖ + 1
  envelope_eq_union :
    ∀ j, (envelope j).carrier = (block j).toBodyFamily.union
  envelope_measurable : ∀ j, (envelope j).IsMeasurable
  envelope_convex : ∀ j, (envelope j).IsConvex
  envelope_dimensions :
    ∀ j, (envelope j).HasDimensions rho rho 4 3
  cover :
    ∀ i,
      (fine.tube i).carrier ⊆
        (envelope (parent i)).carrier

namespace SelectedScaleFourBlockData

/-- Flatten all four-member blocks into one indexed coarse family. -/
def coarse
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho) :
    Kakeya.Streamlined.TubeFamily rho :=
  flattenFixedBlocks data.block data.block_card

/-- Relate a fine index to every member of its assigned four-member block. -/
def relation
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (i : Fin fine.card) (q : Fin data.coarse.card) : Prop :=
  fixedBlockIndex q = data.parent i

/-- Every fine index is related to at least one flattened coarse index. -/
lemma relation_nonempty
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (i : Fin fine.card) :
    ∃ q, data.relation i q := by
  let slot : Fin 4 := 0
  change ∃ q : Fin (data.selected.card * 4),
    fixedBlockIndex q = data.parent i
  exact ⟨finProdFinEquiv (data.parent i, slot),
    fixedBlockIndex_finProdFinEquiv (data.parent i) slot⟩

/-- Every fine carrier is covered by its related flattened coarse carriers. -/
lemma carrier_subset_relation_union
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (i : Fin fine.card) :
    (fine.tube i).carrier ⊆
      {point | ∃ q, data.relation i q ∧
        point ∈ (data.coarse.tube q).carrier} := by
  intro point hpoint
  have hblock :
      point ∈ (data.block (data.parent i)).toBodyFamily.union := by
    rw [← data.envelope_eq_union]
    exact data.cover i hpoint
  rcases hblock with ⟨k, hk⟩
  change point ∈ ((data.block (data.parent i)).tube k).carrier at hk
  let slot : Fin 4 := Fin.cast (data.block_card (data.parent i)) k
  change ∃ q : Fin (data.selected.card * 4),
    fixedBlockIndex q = data.parent i ∧
      point ∈
        ((flattenFixedBlocks data.block data.block_card).tube q).carrier
  refine ⟨finProdFinEquiv (data.parent i, slot), ?_, ?_⟩
  · exact fixedBlockIndex_finProdFinEquiv (data.parent i) slot
  · rw [flattenFixedBlocks_tube]
    simpa [slot] using hk

/-- Flattening preserves the source basepoint window with one-unit loss. -/
lemma coarse_hasBoundedBase
    {delta rho R : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (hbase : HasBoundedBase fine R) :
    HasBoundedBase data.coarse (R + 1) := by
  apply flattenFixedBlocks_hasBoundedBase
  intro j k
  exact (data.block_base j k).trans (by
    have h := hbase (data.selected.equivFin.symm j).1
    linarith)

/-- Flattening preserves the vertical chart of the source family. -/
lemma coarse_isInVerticalChart
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (hvertical : IsInVerticalChart fine) :
    IsInVerticalChart data.coarse := by
  apply flattenFixedBlocks_isInVerticalChart
  intro j k
  rw [data.block_vertical j k]
  exact hvertical (data.selected.equivFin.symm j).1

/-- Each flattened coarse tube retains its representative supporting line. -/
lemma coarse_axis
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (q : Fin data.coarse.card) :
    tubeAxisLine (data.coarse.tube q) =
      tubeAxisLine
        (fine.tube
          (data.selected.equivFin.symm (fixedBlockIndex q)).1) := by
  exact flattenFixedBlocks_axis data.block data.block_card
    (fun j => tubeAxisLine
      (fine.tube (data.selected.equivFin.symm j).1))
    data.block_axis q

/-- Package the nested existential output of the frozen block conclusion. -/
theorem exists_of_conclusion
    (hblocks : RepresentativeFourBlockCoverAtScaleConclusion)
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hdelta_rho : 3000 * delta ≤ rho)
    (hrho : rho ≤ 1 / 8)
    (fine : Kakeya.Streamlined.TubeFamily delta) :
    Nonempty (SelectedScaleFourBlockData fine rho) := by
  rcases hblocks delta rho hdelta hdelta_rho hrho fine with
    ⟨selected, parent, block, envelope, hselected, hconflict, hsurjective,
      hcard, hdistinct, haxis, hvertical, hbase, henvelope, hmeasurable,
      hconvex, hdimensions, hcover⟩
  exact ⟨{
    selected := selected
    parent := parent
    block := block
    envelope := envelope
    selected_distinct := hselected
    representative_conflict := hconflict
    parent_surjective := hsurjective
    block_card := hcard
    block_distinct := hdistinct
    block_axis := haxis
    block_vertical := hvertical
    block_base := hbase
    envelope_eq_union := henvelope
    envelope_measurable := hmeasurable
    envelope_convex := hconvex
    envelope_dimensions := hdimensions
    cover := hcover
  }⟩

end SelectedScaleFourBlockData

end Kakeya.Assouad
