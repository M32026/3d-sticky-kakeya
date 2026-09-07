import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicFineAssignmentData

/-!
# Restrict dyadic fine-assignment data to a subset

Ambient-ball pigeonholing replaces the retained point set by a measurable
subset.  All pointwise fine rectangles, fibers, exact scales, and two-ends
certificates restrict by reindexing along the subset inclusion.  This module
packages that transport canonically.
-/

noncomputable section

namespace Kakeya.Cinematic

def FineRectangleAssignmentData.restrict
    {family : Set C2Function}
    {E E' : Set (ℝ × ℝ)}
    {K delta t Delta C_R : ℝ}
    (data : FineRectangleAssignmentData
      family E K delta t Delta C_R)
    (hsub : E' ⊆ E) :
    FineRectangleAssignmentData
      family E' K delta t Delta C_R where
  interval := data.interval
  intervalControlled := data.intervalControlled
  point := fun p => data.point ⟨p, hsub p.property⟩
  point_coe := fun p => data.point_coe ⟨p, hsub p.property⟩
  center := fun p => data.center ⟨p, hsub p.property⟩
  center_mem := fun p => data.center_mem ⟨p, hsub p.property⟩
  fiber := fun p => data.fiber ⟨p, hsub p.property⟩
  fiber_subset := fun p => data.fiber_subset ⟨p, hsub p.property⟩
  rectangle := fun p => data.rectangle ⟨p, hsub p.property⟩
  rectangle_function := fun p =>
    data.rectangle_function ⟨p, hsub p.property⟩
  rectangle_midpoint := fun p =>
    data.rectangle_midpoint ⟨p, hsub p.property⟩
  rectangle_midpoint_central := fun p =>
    data.rectangle_midpoint_central ⟨p, hsub p.property⟩
  point_mem_rectangle := fun p =>
    data.point_mem_rectangle ⟨p, hsub p.property⟩
  rectangle_central := fun p =>
    data.rectangle_central ⟨p, hsub p.property⟩
  fiber_tangent := fun p =>
    data.fiber_tangent ⟨p, hsub p.property⟩

namespace FineRectangleAssignmentData

variable
    {family : Set C2Function}
    {E E' : Set (ℝ × ℝ)}
    {K delta t Delta C_R : ℝ}
    (data : FineRectangleAssignmentData
      family E K delta t Delta C_R)
    (hsub : E' ⊆ E)

@[simp]
lemma restrict_interval :
    (data.restrict hsub).interval = data.interval := rfl

@[simp]
lemma restrict_center (p : E') :
    (data.restrict hsub).center p =
      data.center ⟨p, hsub p.property⟩ := rfl

@[simp]
lemma restrict_fiber (p : E') :
    (data.restrict hsub).fiber p =
      data.fiber ⟨p, hsub p.property⟩ := rfl

@[simp]
lemma restrict_rectangle (p : E') :
    (data.restrict hsub).rectangle p =
      data.rectangle ⟨p, hsub p.property⟩ := rfl

end FineRectangleAssignmentData

def DyadicFineAssignmentData.restrict
    {family : Set C2Function}
    {E E' : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)
    (hsub : E' ⊆ E)
    (hE' : MeasurableSet E') :
    DyadicFineAssignmentData
      family E' K delta diameter epsilon eta tRep DeltaRep C_R where
  interval := data.interval
  assignment := data.assignment.restrict hsub
  assignment_interval := data.assignment_interval
  exactT := fun p => data.exactT ⟨p, hsub p.property⟩
  exactDelta := fun p => data.exactDelta ⟨p, hsub p.property⟩
  ambientSource := data.ambientSource
  ambientSource_subset := data.ambientSource_subset
  separationScale := data.separationScale
  separationScale_pos := data.separationScale_pos
  ambientSource_separated := data.ambientSource_separated
  source := fun p => data.source ⟨p, hsub p.property⟩
  source_subset_ambient := fun p =>
    data.source_subset_ambient ⟨p, hsub p.property⟩
  metricFiber := fun p => data.metricFiber ⟨p, hsub p.property⟩
  tangencyFiber := fun p =>
    data.tangencyFiber ⟨p, hsub p.property⟩
  metricCenter := fun p => data.metricCenter ⟨p, hsub p.property⟩
  tangencyCenter := fun p =>
    data.tangencyCenter ⟨p, hsub p.property⟩
  tangencyCenter_ball_measurable := by
    intro center radius
    let target :=
      {q : ℝ × ℝ | ∃ hq : q ∈ E',
        data.tangencyCenter
          ⟨q, hsub hq⟩ ∈ c2Ball center radius}
    have htarget :
        target =
          E' ∩
            {q : ℝ × ℝ | ∃ hq : q ∈ E,
              data.tangencyCenter
                ⟨q, hq⟩ ∈ c2Ball center radius} := by
      ext q
      constructor
      · rintro ⟨hq, hcenter⟩
        exact ⟨hq, ⟨hsub hq, by
          simpa only using hcenter⟩⟩
      · rintro ⟨hq, hcenter⟩
        rcases hcenter with ⟨hqE, hcenter⟩
        exact ⟨hq, by simpa only using hcenter⟩
    change MeasurableSet target
    rw [htarget]
    exact hE'.inter
      (data.tangencyCenter_ball_measurable center radius)
  epsilon_pos := data.epsilon_pos
  eta_pos := data.eta_pos
  mu := data.mu
  mu_pos := data.mu_pos
  mu_le_source := fun p => data.mu_le_source ⟨p, hsub p.property⟩
  certificate := fun p => data.certificate ⟨p, hsub p.property⟩
  delta_le_DeltaRep := data.delta_le_DeltaRep
  DeltaRep_le_tRep := data.DeltaRep_le_tRep
  tRep_pos := data.tRep_pos
  four_exactT_le_rep := fun p =>
    data.four_exactT_le_rep ⟨p, hsub p.property⟩
  exactDelta_le_rep := fun p =>
    data.exactDelta_le_rep ⟨p, hsub p.property⟩
  rep_le_eight_exactT := fun p =>
    data.rep_le_eight_exactT ⟨p, hsub p.property⟩
  repDelta_le_two_exactDelta := fun p =>
    data.repDelta_le_two_exactDelta ⟨p, hsub p.property⟩
  assignment_center := fun p =>
    data.assignment_center ⟨p, hsub p.property⟩
  assignment_fiber := fun p =>
    data.assignment_fiber ⟨p, hsub p.property⟩

namespace DyadicFineAssignmentData

variable
    {family : Set C2Function}
    {E E' : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)
    (hsub : E' ⊆ E)
    (hE' : MeasurableSet E')

@[simp]
lemma restrict_interval :
    (data.restrict hsub hE').interval = data.interval := rfl

@[simp]
lemma restrict_mu :
    (data.restrict hsub hE').mu = data.mu := rfl

@[simp]
lemma restrict_ambientSource :
    (data.restrict hsub hE').ambientSource = data.ambientSource := rfl

@[simp]
lemma restrict_source (p : E') :
    (data.restrict hsub hE').source p =
      data.source ⟨p, hsub p.property⟩ := rfl

@[simp]
lemma restrict_metricFiber (p : E') :
    (data.restrict hsub hE').metricFiber p =
      data.metricFiber ⟨p, hsub p.property⟩ := rfl

@[simp]
lemma restrict_tangencyFiber (p : E') :
    (data.restrict hsub hE').tangencyFiber p =
      data.tangencyFiber ⟨p, hsub p.property⟩ := rfl

@[simp]
lemma restrict_exactT (p : E') :
    (data.restrict hsub hE').exactT p =
      data.exactT ⟨p, hsub p.property⟩ := rfl

@[simp]
lemma restrict_exactDelta (p : E') :
    (data.restrict hsub hE').exactDelta p =
      data.exactDelta ⟨p, hsub p.property⟩ := rfl

end DyadicFineAssignmentData

end Kakeya.Cinematic
