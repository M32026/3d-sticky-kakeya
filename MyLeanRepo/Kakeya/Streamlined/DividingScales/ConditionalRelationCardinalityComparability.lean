import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalRelationExactProfileIdentity

/-!
# Cardinality comparability for represented conditional relations

Finite-depth conditional uniformity already controls the cardinality profile
of one relation edge.  A represented relation cardinality is the number of
scale-`r` parents appearing inside one historical cell and one scale-`s`
endpoint cell.

The endpoint cells are comparable by one power of `uniformity`.  Their
subcells obtained by additionally fixing the scale-`r` parent are comparable
by another power.  Double-counting the two endpoint partitions and cancelling
one positive endpoint-cell cardinality therefore gives

```text
relationCard(i, r, s)
  <= uniformity^2 * relationCard(i', r, s).
```

Thus the existing conditional structure supplies all edgewise max/min
comparability needed by the v5 density telescope.  What it does not supply is
an exact nested branching identity across several independently chosen
scales.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace FrostmanConditionalFactorScope

/-- Fine indices in an endpoint cell with one additional scale-`r` parent. -/
def relationFiberCell
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    Finset (Fin F.card) :=
  (P.endpointCell i s).filter fun original =>
    (U.cover r).parent original = j

@[simp] lemma mem_relationFiberCell_iff
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (i original : Fin F.card)
    (r s : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    original ∈ P.relationFiberCell i r s j ↔
      original ∈ P.endpointCell i s ∧
        (U.cover r).parent original = j := by
  simp [relationFiberCell]

/-- Every parent represented by the relation has a nonempty fine-index
fiber. -/
lemma relationFiberCell_nonempty_of_mem
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card)
    (hj : j ∈ P.relationIndices i r s) :
    (P.relationFiberCell i r s j).Nonempty := by
  rcases (P.mem_relationIndices_iff i r s j).mp hj with
    ⟨original, hhistory, hs, hr⟩
  refine ⟨original, ?_⟩
  rw [P.mem_relationFiberCell_iff]
  exact
    ⟨(P.mem_endpointCell_iff i original s).mpr
        ⟨hhistory, hs⟩,
      hr⟩

/-- The endpoint cell is the disjoint union of its represented scale-`r`
parent fibers, in cardinality form. -/
lemma endpointCell_card_eq_sum_relationFiberCell
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    ((P.endpointCell i s).card : ENNReal) =
      ∑ j ∈ P.relationIndices i r s,
        ((P.relationFiberCell i r s j).card : ENNReal) := by
  classical
  have hmaps :
      Set.MapsTo (U.cover r).parent
        (↑(P.endpointCell i s) : Set (Fin F.card))
        (↑(P.relationIndices i r s) :
          Set (Fin (U.coarse r).card)) := by
    intro original horiginal
    change (U.cover r).parent original ∈
      (P.endpointCell i s).image (U.cover r).parent
    exact Finset.mem_image.mpr
      ⟨original, horiginal, rfl⟩
  have hnat :=
    Finset.card_eq_sum_card_fiberwise hmaps
  exact_mod_cast hnat

/-- An endpoint cell is the conditional cell obtained by appending its
scale-`s` parent to the historical coordinates. -/
lemma endpointCell_eq_conditionalParentCell_append
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (s : UniformScaleIndex delta) :
    P.endpointCell i s =
      conditionalParentCell U.coarse U.cover
        (appendConditionalScale P.scale s)
        (appendConditionalParent (P.parentOf i)
          ((U.cover s).parent i).val) := by
  classical
  ext original
  rw [P.mem_endpointCell_iff]
  rw [mem_conditionalParentCell_append_iff]
  constructor
  · rintro ⟨hhistory, hs⟩
    exact ⟨hhistory, congrArg Fin.val hs⟩
  · rintro ⟨hhistory, hs⟩
    exact ⟨hhistory, Fin.ext hs⟩

/-- A relation fiber cell is the conditional cell obtained by appending both
endpoint parent coordinates to the history. -/
lemma relationFiberCell_eq_conditionalParentCell_append
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    P.relationFiberCell i r s j =
      conditionalParentCell U.coarse U.cover
        (appendConditionalScale
          (appendConditionalScale P.scale s) r)
        (appendConditionalParent
          (appendConditionalParent (P.parentOf i)
            ((U.cover s).parent i).val)
          j.val) := by
  classical
  ext original
  constructor
  · intro horiginal
    rcases (P.mem_relationFiberCell_iff i original r s j).mp horiginal with
      ⟨hendpoint, hr⟩
    apply (mem_conditionalParentCell_append_iff
      U.coarse U.cover
      (appendConditionalScale P.scale s)
      (appendConditionalParent (P.parentOf i)
        ((U.cover s).parent i).val)
      r j.val original).mpr
    refine ⟨?_, congrArg Fin.val hr⟩
    rw [← P.endpointCell_eq_conditionalParentCell_append i s]
    exact hendpoint
  · intro horiginal
    rcases (mem_conditionalParentCell_append_iff
      U.coarse U.cover
      (appendConditionalScale P.scale s)
      (appendConditionalParent (P.parentOf i)
        ((U.cover s).parent i).val)
      r j.val original).mp horiginal with
      ⟨hendpoint, hr⟩
    apply (P.mem_relationFiberCell_iff i original r s j).mpr
    refine ⟨?_, Fin.ext hr⟩
    rw [P.endpointCell_eq_conditionalParentCell_append i s]
    exact hendpoint

/-- Endpoint-cell cardinalities are comparable with one conditional
uniformity loss. -/
lemma endpointCell_card_le_uniformity_mul
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (i i' : Fin F.card)
    (s : UniformScaleIndex delta) :
    ((P.endpointCell i s).card : ENNReal) ≤
      U.uniformity * ((P.endpointCell i' s).card : ENNReal) := by
  let scale :=
    appendConditionalScale P.scale s
  let parent :=
    appendConditionalParent (P.parentOf i)
      ((U.cover s).parent i).val
  let parent' :=
    appendConditionalParent (P.parentOf i')
      ((U.cover s).parent i').val
  have hcell :
      conditionalParentCell U.coarse U.cover scale parent =
        P.endpointCell i s := by
    symm
    exact P.endpointCell_eq_conditionalParentCell_append i s
  have hcell' :
      conditionalParentCell U.coarse U.cover scale parent' =
        P.endpointCell i' s := by
    symm
    exact P.endpointCell_eq_conditionalParentCell_append i' s
  have h :=
    U.conditionalUniform
      (show 1 ≤ P.coordinateCount + 1 by omega)
      (show P.coordinateCount + 1 ≤ depth + 1 by
        exact Nat.succ_le_succ P.coordinateCount_le)
      scale parent parent'
      (by
        rw [hcell]
        exact Finset.card_pos.mpr
          ⟨i, P.mem_endpointCell_self i s⟩)
      (by
        rw [hcell']
        exact Finset.card_pos.mpr
          ⟨i', P.mem_endpointCell_self i' s⟩)
  have hassigned :
      ((P.endpointCell i s).card : ENNReal) ≤
        U.assignedUniformity *
          ((P.endpointCell i' s).card : ENNReal) := by
    simpa [hcell, hcell'] using h
  exact hassigned.trans <| by
    gcongr
    exact U.assignedUniformity_le_uniformity

/-- Nonempty relation-fiber cell cardinalities are comparable with one
conditional uniformity loss. -/
lemma relationFiberCell_card_le_uniformity_mul
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount + 1 ≤ depth)
    (i i' : Fin F.card)
    (r s : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card)
    (j' : Fin (U.coarse r).card)
    (hj : j ∈ P.relationIndices i r s)
    (hj' : j' ∈ P.relationIndices i' r s) :
    ((P.relationFiberCell i r s j).card : ENNReal) ≤
      U.uniformity *
        ((P.relationFiberCell i' r s j').card : ENNReal) := by
  let scale :=
    appendConditionalScale
      (appendConditionalScale P.scale s) r
  let parent :=
    appendConditionalParent
      (appendConditionalParent (P.parentOf i)
        ((U.cover s).parent i).val)
      j.val
  let parent' :=
    appendConditionalParent
      (appendConditionalParent (P.parentOf i')
        ((U.cover s).parent i').val)
      j'.val
  have hcell :
      conditionalParentCell U.coarse U.cover scale parent =
        P.relationFiberCell i r s j := by
    symm
    exact P.relationFiberCell_eq_conditionalParentCell_append i r s j
  have hcell' :
      conditionalParentCell U.coarse U.cover scale parent' =
        P.relationFiberCell i' r s j' := by
    symm
    exact P.relationFiberCell_eq_conditionalParentCell_append i' r s j'
  have h :=
    U.conditionalUniform
      (show 1 ≤ P.coordinateCount + 2 by omega)
      (show P.coordinateCount + 2 ≤ depth + 1 by
        omega)
      scale parent parent'
      (by
        rw [hcell]
        exact
          (P.relationFiberCell_nonempty_of_mem
            i r s j hj).card_pos)
      (by
        rw [hcell']
        exact
          (P.relationFiberCell_nonempty_of_mem
            i' r s j' hj').card_pos)
  have hassigned :
      ((P.relationFiberCell i r s j).card : ENNReal) ≤
        U.assignedUniformity *
          ((P.relationFiberCell i' r s j').card : ENNReal) := by
    simpa [hcell, hcell'] using h
  exact hassigned.trans <| by
    gcongr
    exact U.assignedUniformity_le_uniformity

/-- Any two represented relation cardinalities differ by at most two powers
of the conditional uniformity. -/
lemma representedRelationCard_le_uniformity_sq_mul
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount + 1 ≤ depth)
    (i i' : Fin F.card)
    (r s : UniformScaleIndex delta) :
    P.representedRelationCard i r s ≤
      U.uniformity ^ 2 *
        P.representedRelationCard i' r s := by
  let source := P.relationIndices i r s
  let target := P.relationIndices i' r s
  let sourceCell : Fin (U.coarse r).card → ENNReal :=
    fun j => (P.relationFiberCell i r s j).card
  let targetCell : Fin (U.coarse r).card → ENNReal :=
    fun j => (P.relationFiberCell i' r s j).card
  have hsourceSum :
      ((P.endpointCell i s).card : ENNReal) =
        ∑ j ∈ source, sourceCell j := by
    exact P.endpointCell_card_eq_sum_relationFiberCell i r s
  have htargetSum :
      ((P.endpointCell i' s).card : ENNReal) =
        ∑ j ∈ target, targetCell j := by
    exact P.endpointCell_card_eq_sum_relationFiberCell i' r s
  have hdouble :
      (source.card : ENNReal) *
          ((P.endpointCell i' s).card : ENNReal) ≤
        U.uniformity * (target.card : ENNReal) *
          ((P.endpointCell i s).card : ENNReal) := by
    rw [htargetSum, hsourceSum]
    calc
      (source.card : ENNReal) *
            (∑ j' ∈ target, targetCell j')
          =
        ∑ j ∈ source,
          ∑ j' ∈ target, targetCell j' := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤
        ∑ j ∈ source,
          ∑ j' ∈ target,
            U.uniformity * sourceCell j := by
              apply Finset.sum_le_sum
              intro j hj
              apply Finset.sum_le_sum
              intro j' hj'
              exact
                P.relationFiberCell_card_le_uniformity_mul
                  hroom i' i r s j' j hj' hj
      _ =
        U.uniformity * (target.card : ENNReal) *
          ∑ j ∈ source, sourceCell j := by
            simp [Finset.sum_const, nsmul_eq_mul,
              Finset.mul_sum]
            ring_nf
  have hendpoint :
      ((P.endpointCell i s).card : ENNReal) ≤
        U.uniformity *
          ((P.endpointCell i' s).card : ENNReal) :=
    P.endpointCell_card_le_uniformity_mul i i' s
  have hcross :
      P.representedRelationCard i r s *
          ((P.endpointCell i' s).card : ENNReal) ≤
        (U.uniformity ^ 2 *
          P.representedRelationCard i' r s) *
          ((P.endpointCell i' s).card : ENNReal) := by
    calc
      P.representedRelationCard i r s *
            ((P.endpointCell i' s).card : ENNReal)
          ≤
        U.uniformity *
            P.representedRelationCard i' r s *
          ((P.endpointCell i s).card : ENNReal) := by
            simpa [representedRelationCard, source, target] using hdouble
      _ ≤
        U.uniformity *
            P.representedRelationCard i' r s *
          (U.uniformity *
            ((P.endpointCell i' s).card : ENNReal)) := by
              gcongr
      _ =
        (U.uniformity ^ 2 *
          P.representedRelationCard i' r s) *
          ((P.endpointCell i' s).card : ENNReal) := by
            ring
  have hendpointZero :
      ((P.endpointCell i' s).card : ENNReal) ≠ 0 := by
    exact_mod_cast
      (Finset.card_pos.mpr
        ⟨i', P.mem_endpointCell_self i' s⟩).ne'
  have hendpointTop :
      ((P.endpointCell i' s).card : ENNReal) ≠ ⊤ :=
    ENNReal.coe_ne_top
  exact
    (ENNReal.mul_le_mul_iff_left
      hendpointZero hendpointTop).mp hcross

/-- Edge cardinality maximum and minimum differ by at most
`uniformity^2`. -/
theorem relationCardMax_le_uniformity_sq_mul_min
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount + 1 ≤ depth)
    (hF : F.Nonempty)
    (r s : UniformScaleIndex delta) :
    P.relationCardMax hF r s ≤
      U.uniformity ^ 2 *
        P.relationCardMin hF r s := by
  let indices : Finset (Fin F.card) := Finset.univ
  have hindices : indices.Nonempty := by
    let i : Fin F.card := ⟨0, hF⟩
    exact ⟨i, Finset.mem_univ i⟩
  rcases
      Finset.exists_mem_eq_inf' hindices
        (fun i => P.representedRelationCard i r s) with
    ⟨imin, _himin, himin⟩
  apply Finset.sup'_le
  intro i _hi
  have hcompare :=
    P.representedRelationCard_le_uniformity_sq_mul
      hroom i imin r s
  simpa [relationCardMin, indices, himin] using hcompare

end FrostmanConditionalFactorScope

end Kakeya.Streamlined
