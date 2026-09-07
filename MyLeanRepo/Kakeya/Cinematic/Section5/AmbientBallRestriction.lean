import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientBallInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicFineAssignmentData
import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicFineAssignmentRestriction

/-!
# Restrict dyadic pointwise data to fixed ambient balls

This module connects the bounded-overlap ambient cover to the pointwise
two-ends data. Each bin is measurable, the bins cover the point set, and every
pointwise retained fiber lies in the corresponding triple-dilated ambient
family.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Cinematic

namespace DyadicFineAssignmentData

variable
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)

def ambientBin (center : C2Function) (radius : ℝ) :
    Set (ℝ × ℝ) :=
  {q | ∃ hq : q ∈ E,
    data.assignment.center ⟨q, hq⟩ ∈ c2Ball center radius}

lemma measurableSet_ambientBin
    (center : C2Function) (radius : ℝ) :
    MeasurableSet (data.ambientBin center radius) := by
  have heq :
      data.ambientBin center radius =
        {q : ℝ × ℝ | ∃ hq : q ∈ E,
          data.tangencyCenter ⟨q, hq⟩ ∈ c2Ball center radius} := by
    ext q
    constructor
    · rintro ⟨hq, hmem⟩
      refine ⟨hq, ?_⟩
      rw [← data.assignment_center ⟨q, hq⟩]
      exact hmem
    · rintro ⟨hq, hmem⟩
      refine ⟨hq, ?_⟩
      rw [data.assignment_center ⟨q, hq⟩]
      exact hmem
  rw [heq]
  exact data.tangencyCenter_ball_measurable center radius

lemma center_mem_ambient (p : E) :
    data.assignment.center p ∈ data.ambientSource.carrier := by
  have hmetric := data.center_mem_metric p
  have hsource :
      data.assignment.center p ∈ (data.source p).carrier :=
    ((data.certificate p).metric_subset hmetric).1
  exact data.source_subset_ambient p hsource

end DyadicFineAssignmentData

lemma ambient_ball_restriction_setup
    (hCover : FiniteAmbientBallCoverStatement)
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K D delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (hD : 1 ≤ D)
    (hdelta : 0 < delta)
    (hfamily : IsCinematicFamily family K D)
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R) :
    ∃ centers : Finset C2Function,
      (centers : Set C2Function) ⊆ data.ambientSource.carrier ∧
      (∀ c ∈ centers,
        MeasurableSet (data.ambientBin c tRep)) ∧
      E ⊆ ⋃ c ∈ (centers : Set C2Function),
        data.ambientBin c tRep ∧
      (∀ c ∈ centers,
        (data.ambientSource.cluster c (3 * tRep)).carrier ⊆ family) ∧
      (∀ c ∈ centers,
        ∀ f ∈ (data.ambientSource.cluster c (3 * tRep)).carrier,
          ∀ g ∈ (data.ambientSource.cluster c (3 * tRep)).carrier,
            c2Distance f g ≤ 6 * tRep) ∧
      (∀ c ∈ centers, ∀ q : ℝ × ℝ, ∀ hq : q ∈ E,
        q ∈ data.ambientBin c tRep →
          (data.assignment.fiber ⟨q, hq⟩).carrier ⊆
            (data.ambientSource.cluster c (3 * tRep)).carrier) ∧
      (∑ c ∈ centers,
        ((data.ambientSource.cluster c (3 * tRep)).card : ℝ)) ≤
          D ^ 3 * (data.ambientSource.card : ℝ) := by
  rcases hCover hD data.tRep_pos hfamily data.ambientSource
      data.ambientSource_subset with
    ⟨centers, hcenters_sub, hcover, _hseparated,
      hcluster_sub, hdiameter, hcard⟩
  refine ⟨centers, hcenters_sub, ?_, ?_, hcluster_sub,
    hdiameter, ?_, hcard⟩
  · intro c hc
    exact data.measurableSet_ambientBin c tRep
  · intro q hq
    let p : E := ⟨q, hq⟩
    rcases hcover (data.assignment.center p) (data.center_mem_ambient p) with
      ⟨c, hc, hdist⟩
    exact Set.mem_iUnion₂.mpr ⟨c, hc,
      show q ∈ data.ambientBin c tRep from
        ⟨hq, by rwa [mem_c2Ball]⟩⟩
  · intro c hc q hq hqbin
    rcases hqbin with ⟨hq', hcenter⟩
    have hp : (⟨q, hq'⟩ : E) = ⟨q, hq⟩ := by
      apply Subtype.ext
      rfl
    rw [hp] at hcenter
    have hcenter' :
        c2Distance (data.assignment.center ⟨q, hq⟩) c ≤ tRep := by
      rwa [mem_c2Ball] at hcenter
    exact data.fiber_subset_ambient_cluster hdelta
      ⟨q, hq⟩ hcenter' (by linarith [data.tRep_pos])

def ambientRestrictedSet
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)
    (center : C2Function) : Set (ℝ × ℝ) :=
  E ∩ data.ambientBin center tRep

def ambientRestrictedData
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)
    (center : C2Function)
    (hE : MeasurableSet E) :
    DyadicFineAssignmentData
      family (ambientRestrictedSet data center)
        K delta diameter epsilon eta tRep DeltaRep C_R :=
  data.restrict
    (fun _ hq => hq.1)
    (hE.inter (data.measurableSet_ambientBin center tRep))

lemma measurableSet_ambientRestrictedSet
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)
    (center : C2Function)
    (hE : MeasurableSet E) :
    MeasurableSet (ambientRestrictedSet data center) :=
  hE.inter (data.measurableSet_ambientBin center tRep)

lemma ambientRestrictedSet_subset
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)
    (center : C2Function) :
    ambientRestrictedSet data center ⊆ E :=
  Set.inter_subset_left

lemma ambientRestrictedData_fiber_subset_cluster
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)
    (hdelta : 0 < delta)
    (center : C2Function)
    (hE : MeasurableSet E)
    (p : ambientRestrictedSet data center) :
    ((ambientRestrictedData data center hE).assignment.fiber p).carrier ⊆
      (data.ambientSource.cluster center (3 * tRep)).carrier := by
  let original : E := ⟨p, p.property.1⟩
  have hbin :
      (p : ℝ × ℝ) ∈ data.ambientBin center tRep :=
    p.property.2
  have hcenter :
      c2Distance (data.assignment.center original) center ≤ tRep := by
    rcases hbin with ⟨hp, hmem⟩
    have horiginal : (⟨p, hp⟩ : E) = original := by
      apply Subtype.ext
      rfl
    rw [horiginal] at hmem
    rwa [mem_c2Ball] at hmem
  have hfiber :
      (ambientRestrictedData data center hE).assignment.fiber p =
        data.assignment.fiber original := rfl
  rw [hfiber]
  exact data.fiber_subset_ambient_cluster hdelta original hcenter
    (by linarith [data.tRep_pos])

lemma ambientRestrictedData_cluster_diameter
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)
    (center : C2Function) :
    ∀ f ∈ (data.ambientSource.cluster center (3 * tRep)).carrier,
      ∀ g ∈ (data.ambientSource.cluster center (3 * tRep)).carrier,
        c2Distance f g ≤ 6 * tRep := by
  intro f hf g hg
  have hf' : c2Distance f center ≤ 3 * tRep := by
    simpa only [mem_c2Ball] using hf.2
  have hg' : c2Distance g center ≤ 3 * tRep := by
    simpa only [mem_c2Ball] using hg.2
  have htriangle :
      c2Distance f g ≤
        c2Distance f center + c2Distance center g :=
    dist_triangle f center g
  have hsymm : c2Distance center g = c2Distance g center :=
    dist_comm center g
  rw [hsymm] at htriangle
  linarith

lemma ambientRestrictedData_cluster_card_pos
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)
    (hdelta : 0 < delta)
    (center : C2Function)
    (hE : MeasurableSet E)
    (hbin : (ambientRestrictedSet data center).Nonempty) :
    0 <
      (data.ambientSource.cluster center (3 * tRep)).card := by
  rcases hbin with ⟨q, hq⟩
  let p : ambientRestrictedSet data center := ⟨q, hq⟩
  rcases
      (ambientRestrictedData data center hE).fiber_nonempty
        hdelta p with
    ⟨f, hf⟩
  have hfcluster :
      f ∈
        (data.ambientSource.cluster center (3 * tRep)).carrier :=
    ambientRestrictedData_fiber_subset_cluster
      data hdelta center hE p hf
  exact
    (Set.ncard_pos
      (data.ambientSource.cluster center (3 * tRep)).finite).2
      ⟨f, hfcluster⟩

lemma ambientRestrictedSet_small_volume_exit
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)
    (hdelta : 0 < delta)
    (center : C2Function)
    (hE : MeasurableSet E)
    (hbin : (ambientRestrictedSet data center).Nonempty)
    (localTarget : ℝ)
    (hvolume :
      volume (ambientRestrictedSet data center) ≤
        ENNReal.ofReal localTarget) :
    volume (ambientRestrictedSet data center) ≤
      ENNReal.ofReal localTarget *
        (data.ambientSource.cluster center (3 * tRep)).card := by
  have hcard :
      1 ≤
        (data.ambientSource.cluster center (3 * tRep)).card :=
    ambientRestrictedData_cluster_card_pos
      data hdelta center hE hbin
  calc
    volume (ambientRestrictedSet data center) ≤
        ENNReal.ofReal localTarget := hvolume
    _ = ENNReal.ofReal localTarget * 1 := by simp
    _ ≤
        ENNReal.ofReal localTarget *
          (data.ambientSource.cluster center (3 * tRep)).card := by
      gcongr
      exact_mod_cast hcard

lemma ambient_ball_restricted_dyadic_decomposition
    (hCover : FiniteAmbientBallCoverStatement)
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K D delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (hD : 1 ≤ D)
    (hdelta : 0 < delta)
    (hfamily : IsCinematicFamily family K D)
    (hE : MeasurableSet E)
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R) :
    ∃ centers : Finset C2Function,
      E ⊆ ⋃ c ∈ (centers : Set C2Function),
        ambientRestrictedSet data c ∧
      (∀ c ∈ centers,
        MeasurableSet (ambientRestrictedSet data c)) ∧
      (∀ c ∈ centers,
        ambientRestrictedSet data c ⊆ E) ∧
      (∀ c ∈ centers,
        (data.ambientSource.cluster c (3 * tRep)).carrier ⊆ family) ∧
      (∀ c ∈ centers,
        ∀ f ∈ (data.ambientSource.cluster c (3 * tRep)).carrier,
          ∀ g ∈ (data.ambientSource.cluster c (3 * tRep)).carrier,
            c2Distance f g ≤ 6 * tRep) ∧
      (∀ c ∈ centers,
        ∀ p : ambientRestrictedSet data c,
          ((ambientRestrictedData data c hE).assignment.fiber p).carrier ⊆
            (data.ambientSource.cluster c (3 * tRep)).carrier) ∧
      (∑ c ∈ centers,
        ((data.ambientSource.cluster c (3 * tRep)).card : ℝ)) ≤
          D ^ 3 * (data.ambientSource.card : ℝ) := by
  rcases ambient_ball_restriction_setup
      hCover hD hdelta hfamily data with
    ⟨centers, hcentersSub, _hbinsMeasurable, hcover,
      hclusterSub, hdiameter, _hfiber, hcard⟩
  refine
    ⟨centers, ?_, ?_, ?_, hclusterSub,
      hdiameter, ?_, hcard⟩
  · intro q hq
    have hbin := hcover hq
    rcases Set.mem_iUnion₂.mp hbin with ⟨c, hc, hqbin⟩
    exact Set.mem_iUnion₂.mpr
      ⟨c, hc, ⟨hq, hqbin⟩⟩
  · intro c _
    exact measurableSet_ambientRestrictedSet data c hE
  · intro c _
    exact ambientRestrictedSet_subset data c
  · intro c _ p
    exact ambientRestrictedData_fiber_subset_cluster
      data hdelta c hE p

end Kakeya.Cinematic
