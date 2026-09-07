import MyLeanRepo.Kakeya.Cinematic.Section5.FineCarrierMeasurableAssignment

/-!
# Mass lower bounds for disjoint assigned pieces

The first coarse-fiber multiplicity estimate in PYZ Lemma 43 sums the
disjoint assigned pieces lying over one coarse parent.  If every retained
piece has mass at least `Lambda` and their union lies in one coarse
neighborhood, then the fiber cardinality times `Lambda` is bounded by the
measure of that neighborhood.
-/

open MeasureTheory

namespace Kakeya.Cinematic

lemma card_mul_le_measure_of_disjoint_pieces
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type*} [DecidableEq ι]
    (piece : ι → Set α)
    (hpiece_measurable : ∀ i, MeasurableSet (piece i))
    (hpiece_disjoint : Set.PairwiseDisjoint Set.univ piece)
    (selected : Finset ι) (Lambda : ENNReal)
    (A : Set α)
    (hpiece_sub : ∀ i ∈ selected, piece i ⊆ A)
    (hpiece_lower : ∀ i ∈ selected, Lambda ≤ μ (piece i)) :
    (selected.card : ENNReal) * Lambda ≤ μ A := by
  have hselected_disjoint :
      (selected : Set ι).PairwiseDisjoint piece := by
    intro i _ j _ hij
    exact hpiece_disjoint (Set.mem_univ i) (Set.mem_univ j) hij
  have hmeasure_union :
      μ (⋃ i ∈ selected, piece i) =
        ∑ i ∈ selected, μ (piece i) :=
    measure_biUnion_finset hselected_disjoint
      (fun i _ => hpiece_measurable i)
  have hcard_lower :
      (selected.card : ENNReal) * Lambda ≤
        ∑ i ∈ selected, μ (piece i) := by
    calc
      (selected.card : ENNReal) * Lambda =
          ∑ _i ∈ selected, Lambda := by simp
      _ ≤ ∑ i ∈ selected, μ (piece i) := by
        exact Finset.sum_le_sum fun i hi => hpiece_lower i hi
  have hunion_sub : (⋃ i ∈ selected, piece i) ⊆ A := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hi, hx⟩
    exact hpiece_sub i hi hx
  calc
    (selected.card : ENNReal) * Lambda
        ≤ ∑ i ∈ selected, μ (piece i) := hcard_lower
    _ = μ (⋃ i ∈ selected, piece i) := hmeasure_union.symm
    _ ≤ μ A := measure_mono hunion_sub

lemma card_le_of_ennreal_card_mul_le_ofReal
    {card : ℕ} {Lambda : ENNReal} {area : ℝ}
    (hLambda_pos : 0 < Lambda)
    (hLambda_ne_top : Lambda ≠ ⊤)
    (harea : 0 ≤ area)
    (hmass : (card : ENNReal) * Lambda ≤ ENNReal.ofReal area) :
    (card : ℝ) ≤ area / Lambda.toReal := by
  have hleft_ne_top :
      (card : ENNReal) * Lambda ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top card) hLambda_ne_top
  have hreal :
      ((card : ENNReal) * Lambda).toReal ≤
        (ENNReal.ofReal area).toReal :=
    (ENNReal.toReal_le_toReal hleft_ne_top ENNReal.ofReal_ne_top).2 hmass
  have hLambda_real_pos : 0 < Lambda.toReal :=
    ENNReal.toReal_pos hLambda_pos.ne' hLambda_ne_top
  have hmul :
      (card : ℝ) * Lambda.toReal ≤ area := by
    simpa [ENNReal.toReal_mul, harea] using hreal
  exact (le_div_iff₀ hLambda_real_pos).2 hmul

end Kakeya.Cinematic
