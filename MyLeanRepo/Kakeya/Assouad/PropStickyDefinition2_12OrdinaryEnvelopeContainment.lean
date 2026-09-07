import MyLeanRepo.Kakeya.Assouad.WZ1.Factor2Packing

/-!
# Ordinary common-child envelope containment

This module gives the ordinary unit-segment tube geometry needed to compare
two parents of one fine tube.  The envelope only relabels the radius: it
preserves the coarse tube's base and direction exactly.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric

/-- Relabel the radius of an ordinary tube without changing its axis segment. -/
def wz2PaperOrdinaryRadiusRelabel
    {rho : ℝ} (targetRadius : ℝ) (tube : Kakeya.DeltaTube rho) :
    Kakeya.DeltaTube targetRadius where
  base := tube.base
  direction := tube.direction
  direction_unit := tube.direction_unit

@[simp] theorem wz2PaperOrdinaryRadiusRelabel_base
    {rho targetRadius : ℝ} (tube : Kakeya.DeltaTube rho) :
    (wz2PaperOrdinaryRadiusRelabel targetRadius tube).base = tube.base :=
  rfl

@[simp] theorem wz2PaperOrdinaryRadiusRelabel_direction
    {rho targetRadius : ℝ} (tube : Kakeya.DeltaTube rho) :
    (wz2PaperOrdinaryRadiusRelabel targetRadius tube).direction =
      tube.direction :=
  rfl

@[simp] theorem wz2PaperOrdinaryRadiusRelabel_carrier
    {rho targetRadius : ℝ} (tube : Kakeya.DeltaTube rho) :
    (wz2PaperOrdinaryRadiusRelabel targetRadius tube).carrier =
      Metric.cthickening targetRadius
        (Kakeya.unitSegment tube.base tube.direction) :=
  rfl

/-- The fixed same-axis envelope used for a coarse `sigma`-tube. -/
def wz2PaperOrdinaryEnvelope
    {sigma : ℝ} (coarse : Kakeya.DeltaTube sigma) :
    Kakeya.DeltaTube (19 * sigma) :=
  wz2PaperOrdinaryRadiusRelabel (19 * sigma) coarse

@[simp] theorem wz2PaperOrdinaryEnvelope_base
    {sigma : ℝ} (coarse : Kakeya.DeltaTube sigma) :
    (wz2PaperOrdinaryEnvelope coarse).base = coarse.base :=
  rfl

@[simp] theorem wz2PaperOrdinaryEnvelope_direction
    {sigma : ℝ} (coarse : Kakeya.DeltaTube sigma) :
    (wz2PaperOrdinaryEnvelope coarse).direction = coarse.direction :=
  rfl

@[simp] theorem wz2PaperOrdinaryEnvelope_carrier
    {sigma : ℝ} (coarse : Kakeya.DeltaTube sigma) :
    (wz2PaperOrdinaryEnvelope coarse).carrier =
      Metric.cthickening (19 * sigma)
        (Kakeya.unitSegment coarse.base coarse.direction) :=
  rfl

/-- Apply the ordinary envelope pointwise, preserving the indexed family. -/
def wz2PaperOrdinaryEnvelopeFamily
    {sigma : ℝ} (coarse : Kakeya.Streamlined.TubeFamily sigma) :
    Kakeya.Streamlined.TubeFamily (19 * sigma) where
  card := coarse.card
  tube index := wz2PaperOrdinaryEnvelope (coarse.tube index)

@[simp] theorem wz2PaperOrdinaryEnvelopeFamily_card
    {sigma : ℝ} (coarse : Kakeya.Streamlined.TubeFamily sigma) :
    (wz2PaperOrdinaryEnvelopeFamily coarse).card = coarse.card :=
  rfl

@[simp] theorem wz2PaperOrdinaryEnvelopeFamily_tube
    {sigma : ℝ} (coarse : Kakeya.Streamlined.TubeFamily sigma)
    (index : Fin coarse.card) :
    (wz2PaperOrdinaryEnvelopeFamily coarse).tube index =
      wz2PaperOrdinaryEnvelope (coarse.tube index) :=
  rfl

/-- The pointwise envelope retains the source index definitionally. -/
def wz2PaperOrdinaryEnvelopeFamilySourceIndex
    {sigma : ℝ} (coarse : Kakeya.Streamlined.TubeFamily sigma) :
    Fin (wz2PaperOrdinaryEnvelopeFamily coarse).card → Fin coarse.card :=
  fun index => index

@[simp] theorem wz2PaperOrdinaryEnvelopeFamilySourceIndex_apply
    {sigma : ℝ} (coarse : Kakeya.Streamlined.TubeFamily sigma)
    (index : Fin (wz2PaperOrdinaryEnvelopeFamily coarse).card) :
    wz2PaperOrdinaryEnvelopeFamilySourceIndex coarse index = index :=
  rfl

@[simp] theorem wz2PaperOrdinaryEnvelopeFamily_tube_sourceIndex
    {sigma : ℝ} (coarse : Kakeya.Streamlined.TubeFamily sigma)
    (index : Fin (wz2PaperOrdinaryEnvelopeFamily coarse).card) :
    (wz2PaperOrdinaryEnvelopeFamily coarse).tube index =
      wz2PaperOrdinaryEnvelope
        (coarse.tube
          (wz2PaperOrdinaryEnvelopeFamilySourceIndex coarse index)) :=
  rfl

/--
Two ordinary parents of one fine tube have close axis parameters, either in
the same orientation or in opposite orientations.
-/
theorem wz2PaperOrdinary_commonChild_alignment_bound
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hrhoSigma : rho ≤ sigma)
    (fine : Kakeya.DeltaTube delta)
    (middle : Kakeya.DeltaTube rho)
    (coarse : Kakeya.DeltaTube sigma)
    (hFineMiddle : fine.carrier ⊆ middle.carrier)
    (hFineCoarse : fine.carrier ⊆ coarse.carrier) :
    (‖middle.direction - coarse.direction‖ ≤ 8 * sigma ∧
        ‖middle.base - coarse.base‖ ≤ 6 * sigma) ∨
      (‖middle.direction + coarse.direction‖ ≤ 8 * sigma ∧
        ‖middle.base - (coarse.base + coarse.direction)‖ ≤
          10 * sigma) := by
  rcases
      containment_alignment_bound hdelta.le hrho
        fine middle hFineMiddle with
    hMiddleSame | hMiddleReversed
  · rcases
        containment_alignment_bound hdelta.le hsigma
          fine coarse hFineCoarse with
      hCoarseSame | hCoarseReversed
    · left
      constructor
      · rw [show
          middle.direction - coarse.direction =
            (middle.direction - fine.direction) +
              (fine.direction - coarse.direction) by abel]
        refine (norm_add_le _ _).trans ?_
        have hMiddleDirection :
            ‖middle.direction - fine.direction‖ ≤ 4 * rho := by
          simpa [norm_sub_rev] using hMiddleSame.1
        linarith
      · rw [show
          middle.base - coarse.base =
            (middle.base - fine.base) +
              (fine.base - coarse.base) by abel]
        refine (norm_add_le _ _).trans ?_
        have hMiddleBase :
            ‖middle.base - fine.base‖ ≤ 3 * rho := by
          simpa [norm_sub_rev] using hMiddleSame.2
        have hCoarseBase :
            ‖fine.base - coarse.base‖ ≤ 3 * sigma := by
          simpa [norm_sub_rev] using hCoarseSame.2
        linarith
    · right
      constructor
      · rw [show
          middle.direction + coarse.direction =
            (middle.direction - fine.direction) +
              (fine.direction + coarse.direction) by abel]
        refine (norm_add_le _ _).trans ?_
        have hMiddleDirection :
            ‖middle.direction - fine.direction‖ ≤ 4 * rho := by
          simpa [norm_sub_rev] using hMiddleSame.1
        linarith
      · rw [show
          middle.base - (coarse.base + coarse.direction) =
            (middle.base - fine.base) +
              ((fine.base + fine.direction) - coarse.base) -
              (fine.direction + coarse.direction) by abel]
        calc
          ‖(middle.base - fine.base) +
              ((fine.base + fine.direction) - coarse.base) -
              (fine.direction + coarse.direction)‖
              ≤
                ‖middle.base - fine.base‖ +
                  ‖(fine.base + fine.direction) - coarse.base‖ +
                  ‖fine.direction + coarse.direction‖ := by
            calc
              _ ≤
                  ‖(middle.base - fine.base) +
                      ((fine.base + fine.direction) - coarse.base)‖ +
                    ‖fine.direction + coarse.direction‖ :=
                norm_sub_le _ _
              _ ≤
                  (‖middle.base - fine.base‖ +
                      ‖(fine.base + fine.direction) - coarse.base‖) +
                    ‖fine.direction + coarse.direction‖ := by
                gcongr
                exact norm_add_le _ _
          _ ≤ 10 * sigma := by
            have hMiddleBase :
                ‖middle.base - fine.base‖ ≤ 3 * rho := by
              simpa [norm_sub_rev] using hMiddleSame.2
            have hCoarseBase :
                ‖(fine.base + fine.direction) - coarse.base‖ ≤
                  3 * sigma := by
              simpa [norm_sub_rev] using hCoarseReversed.2
            linarith
  · rcases
        containment_alignment_bound hdelta.le hsigma
          fine coarse hFineCoarse with
      hCoarseSame | hCoarseReversed
    · right
      constructor
      · rw [show
          middle.direction + coarse.direction =
            (middle.direction + fine.direction) +
              (coarse.direction - fine.direction) by abel]
        refine (norm_add_le _ _).trans ?_
        have hCoarseDirection :
            ‖coarse.direction - fine.direction‖ ≤ 4 * sigma := by
          simpa [norm_sub_rev] using hCoarseSame.1
        have hMiddleDirection :
            ‖middle.direction + fine.direction‖ ≤ 4 * rho := by
          simpa [add_comm] using hMiddleReversed.1
        linarith
      · rw [show
          middle.base - (coarse.base + coarse.direction) =
            (middle.base - (fine.base + fine.direction)) +
              (fine.base - coarse.base) +
              (fine.direction - coarse.direction) by abel]
        calc
          ‖(middle.base - (fine.base + fine.direction)) +
              (fine.base - coarse.base) +
              (fine.direction - coarse.direction)‖
              ≤
                ‖middle.base - (fine.base + fine.direction)‖ +
                  ‖fine.base - coarse.base‖ +
                  ‖fine.direction - coarse.direction‖ := by
            calc
              _ ≤
                  ‖(middle.base - (fine.base + fine.direction)) +
                      (fine.base - coarse.base)‖ +
                    ‖fine.direction - coarse.direction‖ :=
                norm_add_le _ _
              _ ≤
                  (‖middle.base - (fine.base + fine.direction)‖ +
                      ‖fine.base - coarse.base‖) +
                    ‖fine.direction - coarse.direction‖ := by
                gcongr
                exact norm_add_le _ _
          _ ≤ 10 * sigma := by
            have hMiddleBase :
                ‖middle.base - (fine.base + fine.direction)‖ ≤
                  3 * rho := by
              simpa [norm_sub_rev] using hMiddleReversed.2
            have hCoarseBase :
                ‖fine.base - coarse.base‖ ≤ 3 * sigma := by
              simpa [norm_sub_rev] using hCoarseSame.2
            linarith
    · left
      constructor
      · rw [show
          middle.direction - coarse.direction =
            (middle.direction + fine.direction) -
              (fine.direction + coarse.direction) by abel]
        refine (norm_sub_le _ _).trans ?_
        have hMiddleDirection :
            ‖middle.direction + fine.direction‖ ≤ 4 * rho := by
          simpa [add_comm] using hMiddleReversed.1
        linarith
      · rw [show
          middle.base - coarse.base =
            (middle.base - (fine.base + fine.direction)) +
              ((fine.base + fine.direction) - coarse.base) by abel]
        refine (norm_add_le _ _).trans ?_
        have hMiddleBase :
            ‖middle.base - (fine.base + fine.direction)‖ ≤
              3 * rho := by
          simpa [norm_sub_rev] using hMiddleReversed.2
        have hCoarseBase :
            ‖(fine.base + fine.direction) - coarse.base‖ ≤
              3 * sigma := by
          simpa [norm_sub_rev] using hCoarseReversed.2
        linarith

/--
If a fine ordinary tube lies in both a middle and a coarser tube, then the
middle carrier lies in the fixed same-axis radius-`19 * sigma` envelope of
the coarser tube.
-/
theorem wz2_paper_ordinary_middle_carrier_subset_envelope
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hrhoSigma : rho ≤ sigma)
    (fine : Kakeya.DeltaTube delta)
    (middle : Kakeya.DeltaTube rho)
    (coarse : Kakeya.DeltaTube sigma)
    (hFineMiddle : fine.carrier ⊆ middle.carrier)
    (hFineCoarse : fine.carrier ⊆ coarse.carrier) :
    middle.carrier ⊆ (wz2PaperOrdinaryEnvelope coarse).carrier := by
  have hsegmentCompact :
      IsCompact (Kakeya.unitSegment middle.base middle.direction) :=
    isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  rcases
      wz2PaperOrdinary_commonChild_alignment_bound
        hdelta hrho hsigma hrhoSigma fine middle coarse
        hFineMiddle hFineCoarse with
    hSame | hReversed
  · intro point hpoint
    change point ∈
      Metric.cthickening rho
        (Kakeya.unitSegment middle.base middle.direction) at hpoint
    rw [hsegmentCompact.cthickening_eq_biUnion_closedBall hrho.le] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨axisPoint, hAxisPoint, hPointAxis⟩
    rcases hAxisPoint with ⟨parameter, hParameter, rfl⟩
    let coarseAxisPoint :=
      coarse.base + parameter • coarse.direction
    have hCoarseAxisPoint :
        coarseAxisPoint ∈
          Kakeya.unitSegment coarse.base coarse.direction :=
      ⟨parameter, hParameter, rfl⟩
    have hPointMiddleAxis :
        dist point (middle.base + parameter • middle.direction) ≤ rho := by
      simpa [Metric.mem_closedBall] using hPointAxis
    have hAxisDistance :
        dist (middle.base + parameter • middle.direction)
            coarseAxisPoint ≤ 14 * sigma := by
      rw [dist_eq_norm]
      have hDecompose :
          middle.base + parameter • middle.direction - coarseAxisPoint =
            (middle.base - coarse.base) +
              parameter • (middle.direction - coarse.direction) := by
        dsimp only [coarseAxisPoint]
        module
      rw [hDecompose]
      calc
        ‖(middle.base - coarse.base) +
            parameter • (middle.direction - coarse.direction)‖
            ≤
              ‖middle.base - coarse.base‖ +
                ‖parameter •
                  (middle.direction - coarse.direction)‖ :=
          norm_add_le _ _
        _ =
            ‖middle.base - coarse.base‖ +
              parameter *
                ‖middle.direction - coarse.direction‖ := by
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonneg hParameter.1]
        _ ≤ 14 * sigma := by
          have hParameterDirection :
              parameter *
                  ‖middle.direction - coarse.direction‖ ≤
                8 * sigma := by
            calc
              parameter *
                    ‖middle.direction - coarse.direction‖
                  ≤ parameter * (8 * sigma) :=
                mul_le_mul_of_nonneg_left hSame.1 hParameter.1
              _ ≤ 1 * (8 * sigma) :=
                mul_le_mul_of_nonneg_right hParameter.2
                  (by positivity)
              _ = 8 * sigma := by ring
          linarith
    change point ∈
      Metric.cthickening (19 * sigma)
        (Kakeya.unitSegment coarse.base coarse.direction)
    apply Metric.mem_cthickening_of_dist_le
      point coarseAxisPoint (19 * sigma)
      (Kakeya.unitSegment coarse.base coarse.direction)
      hCoarseAxisPoint
    calc
      dist point coarseAxisPoint ≤
          dist point (middle.base + parameter • middle.direction) +
            dist (middle.base + parameter • middle.direction)
              coarseAxisPoint :=
        dist_triangle _ _ _
      _ ≤ rho + 14 * sigma := by gcongr
      _ ≤ 19 * sigma := by linarith
  · intro point hpoint
    change point ∈
      Metric.cthickening rho
        (Kakeya.unitSegment middle.base middle.direction) at hpoint
    rw [hsegmentCompact.cthickening_eq_biUnion_closedBall hrho.le] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨axisPoint, hAxisPoint, hPointAxis⟩
    rcases hAxisPoint with ⟨parameter, hParameter, rfl⟩
    let coarseAxisPoint :=
      coarse.base + (1 - parameter) • coarse.direction
    have hCoarseAxisPoint :
        coarseAxisPoint ∈
          Kakeya.unitSegment coarse.base coarse.direction :=
      ⟨1 - parameter, by
        constructor
        · linarith [hParameter.2]
        · linarith [hParameter.1], rfl⟩
    have hPointMiddleAxis :
        dist point (middle.base + parameter • middle.direction) ≤ rho := by
      simpa [Metric.mem_closedBall] using hPointAxis
    have hAxisDistance :
        dist (middle.base + parameter • middle.direction)
            coarseAxisPoint ≤ 18 * sigma := by
      rw [dist_eq_norm]
      have hDecompose :
          middle.base + parameter • middle.direction - coarseAxisPoint =
            (middle.base - (coarse.base + coarse.direction)) +
              parameter • (middle.direction + coarse.direction) := by
        dsimp only [coarseAxisPoint]
        module
      rw [hDecompose]
      calc
        ‖(middle.base - (coarse.base + coarse.direction)) +
            parameter • (middle.direction + coarse.direction)‖
            ≤
              ‖middle.base - (coarse.base + coarse.direction)‖ +
                ‖parameter •
                  (middle.direction + coarse.direction)‖ :=
          norm_add_le _ _
        _ =
            ‖middle.base - (coarse.base + coarse.direction)‖ +
              parameter *
                ‖middle.direction + coarse.direction‖ := by
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonneg hParameter.1]
        _ ≤ 18 * sigma := by
          have hParameterDirection :
              parameter *
                  ‖middle.direction + coarse.direction‖ ≤
                8 * sigma := by
            calc
              parameter *
                    ‖middle.direction + coarse.direction‖
                  ≤ parameter * (8 * sigma) :=
                mul_le_mul_of_nonneg_left hReversed.1 hParameter.1
              _ ≤ 1 * (8 * sigma) :=
                mul_le_mul_of_nonneg_right hParameter.2
                  (by positivity)
              _ = 8 * sigma := by ring
          linarith
    change point ∈
      Metric.cthickening (19 * sigma)
        (Kakeya.unitSegment coarse.base coarse.direction)
    apply Metric.mem_cthickening_of_dist_le
      point coarseAxisPoint (19 * sigma)
      (Kakeya.unitSegment coarse.base coarse.direction)
      hCoarseAxisPoint
    calc
      dist point coarseAxisPoint ≤
          dist point (middle.base + parameter • middle.direction) +
            dist (middle.base + parameter • middle.direction)
              coarseAxisPoint :=
        dist_triangle _ _ _
      _ ≤ rho + 18 * sigma := by gcongr
      _ ≤ 19 * sigma := by linarith

end Kakeya.Assouad
