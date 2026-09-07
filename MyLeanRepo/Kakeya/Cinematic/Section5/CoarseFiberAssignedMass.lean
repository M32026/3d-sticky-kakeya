import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseGrouping
import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseFiberCarrierContainmentInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.DisjointPieceMass

/-!
# Assigned mass over one coarse fiber

This module composes the geometric carrier-containment input with the closed
finite measure lemma.  It leaves the coarse-neighborhood geometry explicit
and converts it into the first coarse-fiber multiplicity bound used in PYZ
Lemma 43.
-/

open MeasureTheory

namespace Kakeya.Cinematic

lemma coarse_fiber_assigned_piece_mass
    (hContain : CoarseFiberCarrierContainmentStatement)
    (hCommon : CommonTangentRectangleStatement)
    (hComparable : ComparableRectanglesStatement)
    {K D C_shading : ℝ}
    (hK : 1 ≤ K) (hD : 1 ≤ D) (hC_shading : 1 ≤ C_shading) :
    ∃ C_out : ℝ,
      1 ≤ C_out ∧
      ∀ {family : Set C2Function}
        {E₂ : Set (ℝ × ℝ)}
        {I : ParameterInterval}
        {delta t Delta C_R : ℝ}
        {pointData :
          FineRectangleAssignmentData family E₂ K delta t Delta C_R}
        {fine : RectangleFamily
          delta (C_R * t * Delta / delta)}
        (data : CoarseRectangleGroupingData
          family E₂ K I delta t Delta C_R pointData fine),
        IsCinematicFamily family K D →
        I.IsControlled K →
        0 < delta →
        delta ≤ Delta →
        Delta ≤ t →
        1 ≤ C_R →
        ∀
          (U : Fin fine.card →
            CurvilinearRectangle
              (C_shading * delta)
              (C_R * t * Delta / delta)),
          (∀ i, (U i).function = (fine.rectangle i).function) →
          (∀ i,
            (U i).interval.midpoint =
              (fine.rectangle i).interval.midpoint) →
          ∀ piece : Fin fine.card → Set (ℝ × ℝ),
            (∀ i, MeasurableSet (piece i)) →
            Set.PairwiseDisjoint
              (Set.univ : Set (Fin fine.card)) piece →
            (∀ i, piece i ⊆ (U i).realCarrier) →
            ∀ selected : Finset (Fin fine.card),
              ∀ Lambda : ENNReal,
                (∀ i ∈ selected, Lambda ≤ volume (piece i)) →
                ∀ j : Fin data.coarse.card,
                  (((selected.filter fun i => data.parent i = j).card :
                      ℕ) : ENNReal) * Lambda ≤
                    ENNReal.ofReal
                      (4 * C_out ^ 2 * Delta *
                        (data.coarse.rectangle j).interval.length) := by
  rcases hContain hCommon hComparable K D C_shading hK hD hC_shading with
    ⟨C_out, hC_out, hContain_main⟩
  refine ⟨C_out, hC_out, ?_⟩
  intro family E₂ I delta t Delta C_R pointData fine data
    hfamily hI hdelta hdelta_Delta hDelta_t hC_R
    U hU_function hU_midpoint piece hpiece_measurable
    hpiece_disjoint hpiece_sub selected Lambda hpiece_lower j
  let fiber := selected.filter fun i => data.parent i = j
  let neighborhood :=
    coarseFiberRealNeighborhood (data.coarse.rectangle j) C_out
  have hpiece_sub_neighborhood :
      ∀ i ∈ fiber, piece i ⊆ neighborhood := by
    intro i hi
    have hi_selected : i ∈ selected := (Finset.mem_filter.mp hi).1
    have hi_parent : data.parent i = j := (Finset.mem_filter.mp hi).2
    have henlarged_family :
        (data.enlarged i).function ∈ family := by
      rw [data.enlarged_function i, data.fine_eq_source i,
        pointData.rectangle_function]
      exact pointData.center_mem (data.source i)
    have hparent_family :
        (data.coarse.rectangle j).function ∈ family :=
      data.coarse_centers j
    have hrelation :
        data.enlarged i = data.coarse.rectangle j ∨
          (data.enlarged i).AreLambdaComparable
            (data.coarse.rectangle j) family 100 := by
      simpa [hi_parent] using data.parent_relation i
    have hU_function_enlarged :
        (U i).function = (data.enlarged i).function := by
      rw [hU_function i, data.enlarged_function i]
    have hU_midpoint_enlarged :
        (U i).interval.midpoint =
          (data.enlarged i).interval.midpoint := by
      rw [hU_midpoint i, data.enlarged_midpoint i]
    have hcarrier :=
      (hContain_main hfamily hI hdelta hdelta_Delta hDelta_t
        hC_R (U i) (data.enlarged i)
        (data.coarse.rectangle j) hU_function_enlarged
        hU_midpoint_enlarged henlarged_family hparent_family
        (data.enlarged_central i) (data.coarse_central j)
        hrelation).1
    exact (hpiece_sub i).trans hcarrier
  have hpiece_lower_fiber :
      ∀ i ∈ fiber, Lambda ≤ volume (piece i) := by
    intro i hi
    exact hpiece_lower i (Finset.mem_filter.mp hi).1
  have hmass :=
    card_mul_le_measure_of_disjoint_pieces
      piece hpiece_measurable hpiece_disjoint fiber Lambda
      neighborhood hpiece_sub_neighborhood hpiece_lower_fiber
  have hvolume :=
    (hContain_main hfamily hI hdelta hdelta_Delta hDelta_t
      hC_R
      (U (data.representative j))
      (data.enlarged (data.representative j))
      (data.coarse.rectangle j)
      (by
        rw [hU_function, data.enlarged_function])
      (by
        rw [hU_midpoint, data.enlarged_midpoint])
      (by
        rw [data.enlarged_function, data.fine_eq_source,
          pointData.rectangle_function]
        exact pointData.center_mem (data.source (data.representative j)))
      (data.coarse_centers j)
      (data.enlarged_central (data.representative j))
      (data.coarse_central j)
      (Or.inl (by
        rw [data.coarse_eq_enlarged]))).2
  change (fiber.card : ENNReal) * Lambda ≤
    ENNReal.ofReal
      (4 * C_out ^ 2 * Delta *
        (data.coarse.rectangle j).interval.length)
  exact hmass.trans_eq hvolume

lemma coarse_selected_assigned_piece_mass
    (hContain : CoarseFiberCarrierContainmentStatement)
    (hCommon : CommonTangentRectangleStatement)
    (hComparable : ComparableRectanglesStatement)
    {K D C_shading : ℝ}
    (hK : 1 ≤ K) (hD : 1 ≤ D) (hC_shading : 1 ≤ C_shading) :
    ∃ C_out : ℝ,
      1 ≤ C_out ∧
      ∀ {family : Set C2Function}
        {E₂ : Set (ℝ × ℝ)}
        {I : ParameterInterval}
        {delta t Delta C_R : ℝ}
        {pointData :
          FineRectangleAssignmentData family E₂ K delta t Delta C_R}
        {fine : RectangleFamily
          delta (C_R * t * Delta / delta)}
        (data : CoarseRectangleGroupingData
          family E₂ K I delta t Delta C_R pointData fine),
        IsCinematicFamily family K D →
        I.IsControlled K →
        0 < delta →
        delta ≤ Delta →
        Delta ≤ t →
        1 ≤ C_R →
        ∀
          (U : Fin fine.card →
            CurvilinearRectangle
              (C_shading * delta)
              (C_R * t * Delta / delta)),
          (∀ i, (U i).function = (fine.rectangle i).function) →
          (∀ i,
            (U i).interval.midpoint =
              (fine.rectangle i).interval.midpoint) →
          ∀ piece : Fin fine.card → Set (ℝ × ℝ),
            (∀ i, MeasurableSet (piece i)) →
            Set.PairwiseDisjoint
              (Set.univ : Set (Fin fine.card)) piece →
            (∀ i, piece i ⊆ (U i).realCarrier) →
            ∀ selected : Finset (Fin fine.card),
              ∀ Lambda : ENNReal,
                (∀ i ∈ selected, Lambda ≤ volume (piece i)) →
                (selected.card : ENNReal) * Lambda ≤
                  (data.coarse.card : ENNReal) *
                    ENNReal.ofReal
                      (4 * C_out ^ 2 * Delta *
                        Real.sqrt (Delta / (C_R * t))) := by
  rcases coarse_fiber_assigned_piece_mass
      hContain hCommon hComparable hK hD hC_shading with
    ⟨C_out, hC_out, hfiber⟩
  refine ⟨C_out, hC_out, ?_⟩
  intro family E₂ I delta t Delta C_R pointData fine data
    hfamily hI hdelta hdelta_Delta hDelta_t hC_R
    U hU_function hU_midpoint piece hpiece_measurable
    hpiece_disjoint hpiece_sub selected Lambda hpiece_lower
  have hsum_card :
      (selected.card : ENNReal) =
        ∑ j : Fin data.coarse.card,
          ((selected.filter fun i => data.parent i = j).card :
            ENNReal) := by
    exact_mod_cast (data.sum_selected_parent_card selected).symm
  rw [hsum_card, Finset.sum_mul]
  calc
    ∑ j : Fin data.coarse.card,
        ((selected.filter fun i => data.parent i = j).card :
          ENNReal) * Lambda
        ≤ ∑ _j : Fin data.coarse.card,
            ENNReal.ofReal
              (4 * C_out ^ 2 * Delta *
                Real.sqrt (Delta / (C_R * t))) := by
      apply Finset.sum_le_sum
      intro j _
      have hj :=
        hfiber data hfamily hI hdelta hdelta_Delta hDelta_t hC_R
          U hU_function hU_midpoint piece
          hpiece_measurable hpiece_disjoint hpiece_sub selected Lambda
          hpiece_lower j
      rw [(data.coarse.rectangle j).interval_length] at hj
      exact hj
    _ = (data.coarse.card : ENNReal) *
          ENNReal.ofReal
            (4 * C_out ^ 2 * Delta *
              Real.sqrt (Delta / (C_R * t))) := by
      simp [Finset.sum_const]

lemma coarse_fiber_assigned_piece_card
    (hContain : CoarseFiberCarrierContainmentStatement)
    (hCommon : CommonTangentRectangleStatement)
    (hComparable : ComparableRectanglesStatement)
    {K D C_shading : ℝ}
    (hK : 1 ≤ K) (hD : 1 ≤ D) (hC_shading : 1 ≤ C_shading) :
    ∃ C_out : ℝ,
      1 ≤ C_out ∧
      ∀ {family : Set C2Function}
        {E₂ : Set (ℝ × ℝ)}
        {I : ParameterInterval}
        {delta t Delta C_R : ℝ}
        {pointData :
          FineRectangleAssignmentData family E₂ K delta t Delta C_R}
        {fine : RectangleFamily
          delta (C_R * t * Delta / delta)}
        (data : CoarseRectangleGroupingData
          family E₂ K I delta t Delta C_R pointData fine),
        IsCinematicFamily family K D →
        I.IsControlled K →
        0 < delta →
        delta ≤ Delta →
        Delta ≤ t →
        1 ≤ C_R →
        ∀
          (U : Fin fine.card →
            CurvilinearRectangle
              (C_shading * delta)
              (C_R * t * Delta / delta)),
          (∀ i, (U i).function = (fine.rectangle i).function) →
          (∀ i,
            (U i).interval.midpoint =
              (fine.rectangle i).interval.midpoint) →
          ∀ piece : Fin fine.card → Set (ℝ × ℝ),
            (∀ i, MeasurableSet (piece i)) →
            Set.PairwiseDisjoint
              (Set.univ : Set (Fin fine.card)) piece →
            (∀ i, piece i ⊆ (U i).realCarrier) →
            ∀ selected : Finset (Fin fine.card),
              ∀ Lambda : ENNReal,
                0 < Lambda →
                Lambda ≠ ⊤ →
                (∀ i ∈ selected, Lambda ≤ volume (piece i)) →
                ∀ j : Fin data.coarse.card,
                  ((selected.filter fun i => data.parent i = j).card :
                      ℝ) ≤
                    (4 * C_out ^ 2 * Delta *
                        Real.sqrt (Delta / (C_R * t))) /
                      Lambda.toReal := by
  rcases coarse_fiber_assigned_piece_mass
      hContain hCommon hComparable hK hD hC_shading with
    ⟨C_out, hC_out, hmass⟩
  refine ⟨C_out, hC_out, ?_⟩
  intro family E₂ I delta t Delta C_R pointData fine data
    hfamily hI hdelta hdelta_Delta hDelta_t hC_R
    U hU_function hU_midpoint piece hpiece_measurable
    hpiece_disjoint hpiece_sub selected Lambda hLambda_pos
    hLambda_ne_top hpiece_lower j
  have hmass_j :=
    hmass data hfamily hI hdelta hdelta_Delta hDelta_t hC_R
      U hU_function hU_midpoint piece
      hpiece_measurable hpiece_disjoint hpiece_sub selected Lambda
      hpiece_lower j
  have harea :
      0 ≤
        4 * C_out ^ 2 * Delta *
          (data.coarse.rectangle j).interval.length := by
    have hC_out_nonneg : 0 ≤ C_out := by linarith
    have hDelta_nonneg : 0 ≤ Delta := by linarith
    have hcoefficient : 0 ≤ 4 * C_out ^ 2 := by positivity
    exact mul_nonneg
      (mul_nonneg hcoefficient hDelta_nonneg)
      (data.coarse.rectangle j).interval.length_nonneg
  have hcard :=
    card_le_of_ennreal_card_mul_le_ofReal
      hLambda_pos hLambda_ne_top harea hmass_j
  rw [(data.coarse.rectangle j).interval_length] at hcard
  exact hcard

lemma coarse_selected_assigned_piece_card
    (hContain : CoarseFiberCarrierContainmentStatement)
    (hCommon : CommonTangentRectangleStatement)
    (hComparable : ComparableRectanglesStatement)
    {K D C_shading : ℝ}
    (hK : 1 ≤ K) (hD : 1 ≤ D) (hC_shading : 1 ≤ C_shading) :
    ∃ C_out : ℝ,
      1 ≤ C_out ∧
      ∀ {family : Set C2Function}
        {E₂ : Set (ℝ × ℝ)}
        {I : ParameterInterval}
        {delta t Delta C_R : ℝ}
        {pointData :
          FineRectangleAssignmentData family E₂ K delta t Delta C_R}
        {fine : RectangleFamily
          delta (C_R * t * Delta / delta)}
        (data : CoarseRectangleGroupingData
          family E₂ K I delta t Delta C_R pointData fine),
        IsCinematicFamily family K D →
        I.IsControlled K →
        0 < delta →
        delta ≤ Delta →
        Delta ≤ t →
        1 ≤ C_R →
        ∀
          (U : Fin fine.card →
            CurvilinearRectangle
              (C_shading * delta)
              (C_R * t * Delta / delta)),
          (∀ i, (U i).function = (fine.rectangle i).function) →
          (∀ i,
            (U i).interval.midpoint =
              (fine.rectangle i).interval.midpoint) →
          ∀ piece : Fin fine.card → Set (ℝ × ℝ),
            (∀ i, MeasurableSet (piece i)) →
            Set.PairwiseDisjoint
              (Set.univ : Set (Fin fine.card)) piece →
            (∀ i, piece i ⊆ (U i).realCarrier) →
            ∀ selected : Finset (Fin fine.card),
              ∀ Lambda : ENNReal,
                0 < Lambda →
                Lambda ≠ ⊤ →
                (∀ i ∈ selected, Lambda ≤ volume (piece i)) →
                (selected.card : ℝ) ≤
                  (data.coarse.card : ℝ) *
                    ((4 * C_out ^ 2 * Delta *
                        Real.sqrt (Delta / (C_R * t))) /
                      Lambda.toReal) := by
  rcases coarse_fiber_assigned_piece_card
      hContain hCommon hComparable hK hD hC_shading with
    ⟨C_out, hC_out, hfiber⟩
  refine ⟨C_out, hC_out, ?_⟩
  intro family E₂ I delta t Delta C_R pointData fine data
    hfamily hI hdelta hdelta_Delta hDelta_t hC_R
    U hU_function hU_midpoint piece hpiece_measurable
    hpiece_disjoint hpiece_sub selected Lambda hLambda_pos
    hLambda_ne_top hpiece_lower
  apply data.selected_card_le_coarse_card_mul_real selected
  intro j
  exact hfiber data hfamily hI hdelta hdelta_Delta hDelta_t hC_R
    U hU_function hU_midpoint piece hpiece_measurable
    hpiece_disjoint hpiece_sub selected Lambda hLambda_pos hLambda_ne_top
    hpiece_lower j

end Kakeya.Cinematic
