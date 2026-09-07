module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.SlopeCells
public import MyLeanRepo.InductionOnScales.SeparatedPacketsEstimate
public import MyLeanRepo.InductionOnScales.SeparatedPacketsEstimateGeneral
public import MyLeanRepo.InductionOnScales.GeometricDisjointness
public import MyLeanRepo.InductionOnScales.Homothety
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped BigOperators

/-!
# Estimate 3 Bridge: Packet Function for Separated Packets Estimate

Connects the fine configuration (local tubes) to the global TQ_local via
a packet function, enabling application of `separated_packets_estimate`.

## Main result

`estimate3_bridge`: Given fine and global families with slope-cell
preservation and uniform packet sizes, constructs the packet function and
proves `|TQ_local| ≥ |fineTubes| * m_Q / 8`.

## Packet definition

For each local tube `U`, choose a local point `q_U` containing `U`. Let
`p_U` be the corresponding global point. Then:

```
packet(U) := globalFamily(p_U).filter (T ↦ localSlopeCellIndex m T.a = U.a)
```

## Properties proved

1. **Subset**: `packet(U) ⊆ TQ_local`
2. **Size**: `|packet(U)| = m_Q` (by uniformity and slope preservation)
3. **Disjointness for different slope cells**: intrinsic (a tube has one slope cell)
4. **Disjointness for same slope cell, far intercepts**: taken as hypothesis
   `h_geo_disjoint` (geometric lemma, OS Lemma 3)

## Whiteprint node
Helper for Step 12 of the induction on scales.
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales

/-- Bridge lemma for estimate 3 (OS 5.5 intermediate bound).

Constructs the packet function from local tubes to global tube sets and
applies `separated_packets_estimate`.

### Inputs

- `finePoints`, `fineFamily`: local fine configuration (per-point families)
- `fineTubes`: union of all local point families
- `globalPoints`, `globalFamily`: global retained families (e.g. uniformFamily)
- `p_of_q`: maps local square `q` to corresponding global square `p`
- `m_Q`: uniform number of global tubes per slope cell
- `pointForTube`: chooses a containing local point for each local tube
- `h_geo_disjoint`: geometric disjointness for same-slope separated tubes

### Output

`|TQ_local| ≥ |fineTubes| * m_Q / 8`
-/
lemma estimate3_bridge
    {n m : ℕ} (hnm : m ≤ n)
    {k : ℕ}
    -- Fine (local) configuration
    (finePoints : Finset (DyadicSquare k))
    (fineFamily : (q : DyadicSquare k) → q ∈ finePoints → Finset (DyadicTube k))
    (fineTubes : Finset (DyadicTube k))
    (h_fineTubes_eq : fineTubes = finePoints.biUnion (fun q =>
      if hq : q ∈ finePoints then fineFamily q hq else ∅))
    -- Global configuration
    (globalPoints : Finset (DyadicSquare n))
    (globalFamily : (p : DyadicSquare n) → p ∈ globalPoints → Finset (DyadicTube n))
    -- Point correspondence
    (p_of_q : (q : DyadicSquare k) → q ∈ finePoints → DyadicSquare n)
    (h_p_of_q_sub : ∀ q hq, p_of_q q hq ∈ globalPoints)
    -- Uniformity
    (m_Q : ℕ) (hmQ_pos : 0 < m_Q)
    (h_slope_preservation : ∀ (q : DyadicSquare k) (hq : q ∈ finePoints),
        (fineFamily q hq).image (fun U : DyadicTube k => U.a) =
        (globalFamily (p_of_q q hq) (h_p_of_q_sub q hq)).image
          (fun T : DyadicTube n => localSlopeCellIndex m T.a))
    (h_uniform : ∀ (q : DyadicSquare k) (hq : q ∈ finePoints) (a : ℤ),
        ((globalFamily (p_of_q q hq) (h_p_of_q_sub q hq)).filter
          (fun T : DyadicTube n => localSlopeCellIndex m T.a = a)).card =
        if a ∈ (globalFamily (p_of_q q hq) (h_p_of_q_sub q hq)).image
          (fun T : DyadicTube n => localSlopeCellIndex m T.a) then m_Q else 0)
    -- TQ_local
    (TQ_local : Finset (DyadicTube n))
    (h_subset_TQ : ∀ (p : DyadicSquare n) (hp : p ∈ globalPoints),
        globalFamily p hp ⊆ TQ_local)
    -- Point selection for each local tube
    (pointForTube : DyadicTube k → DyadicSquare k)
    (h_point_in : ∀ (U : DyadicTube k) (hU : U ∈ fineTubes),
        pointForTube U ∈ finePoints)
    (h_U_in_family : ∀ (U : DyadicTube k) (hU : U ∈ fineTubes),
        U ∈ fineFamily (pointForTube U) (h_point_in U hU))
    -- Geometric disjointness for same slope cell, far intercepts
    (h_geo_disjoint : ∀ (U1 U2 : DyadicTube k)
        (q1 q2 : DyadicSquare k) (hq1 : q1 ∈ finePoints) (hq2 : q2 ∈ finePoints),
        U1.a = U2.a → |U1.b - U2.b| ≥ 8 →
        Disjoint
          ((globalFamily (p_of_q q1 hq1) (h_p_of_q_sub q1 hq1)).filter
            (fun T : DyadicTube n => localSlopeCellIndex m T.a = U1.a))
          ((globalFamily (p_of_q q2 hq2) (h_p_of_q_sub q2 hq2)).filter
            (fun T : DyadicTube n => localSlopeCellIndex m T.a = U2.a))) :
    (TQ_local.card : ℝ) ≥ (fineTubes.card : ℝ) * (m_Q : ℝ) / 8 := by
  -- Define packet function
  let packet : DyadicTube k → Finset (DyadicTube n) := fun U =>
    if hU : U ∈ fineTubes then
      let q := pointForTube U
      let hq : q ∈ finePoints := h_point_in U hU
      (globalFamily (p_of_q q hq) (h_p_of_q_sub q hq)).filter
        (fun T : DyadicTube n => localSlopeCellIndex m T.a = U.a)
    else
      ∅

  -- Helper: for U ∈ fineTubes, packet U is the filter at the chosen point
  have h_packet_def (U : DyadicTube k) (hU : U ∈ fineTubes) :
      packet U =
        (globalFamily (p_of_q (pointForTube U) (h_point_in U hU))
          (h_p_of_q_sub (pointForTube U) (h_point_in U hU))).filter
          (fun T : DyadicTube n => localSlopeCellIndex m T.a = U.a) := by
    simp [packet, hU]
    <;> rfl

  -- 1. Subset: packet U ⊆ TQ_local
  have h_subset : ∀ U ∈ fineTubes, packet U ⊆ TQ_local := by
    intro U hU
    rw [h_packet_def U hU]
    let q := pointForTube U
    let hq : q ∈ finePoints := h_point_in U hU
    let p := p_of_q q hq
    let hp : p ∈ globalPoints := h_p_of_q_sub q hq
    have h1 : (globalFamily p hp).filter (fun T => localSlopeCellIndex m T.a = U.a) ⊆
        globalFamily p hp := Finset.filter_subset _ _
    have h2 : globalFamily p hp ⊆ TQ_local := h_subset_TQ p hp
    exact Finset.Subset.trans h1 h2

  -- 2. Size: |packet U| = m_Q
  have h_size : ∀ U ∈ fineTubes, (packet U).card = m_Q := by
    intro U hU
    rw [h_packet_def U hU]
    let q := pointForTube U
    let hq : q ∈ finePoints := h_point_in U hU
    let p := p_of_q q hq
    let hp : p ∈ globalPoints := h_p_of_q_sub q hq
    have hU_in_family : U ∈ fineFamily q hq := h_U_in_family U hU
    have hUa_in_image : U.a ∈ (fineFamily q hq).image (fun U : DyadicTube k => U.a) :=
      Finset.mem_image.mpr ⟨U, hU_in_family, rfl⟩
    have hUa_in_global_image : U.a ∈ (globalFamily p hp).image
        (fun T : DyadicTube n => localSlopeCellIndex m T.a) := by
      rw [←h_slope_preservation q hq]
      exact hUa_in_image
    have h_card_eq : ((globalFamily p hp).filter
        (fun T : DyadicTube n => localSlopeCellIndex m T.a = U.a)).card = m_Q := by
      rw [h_uniform q hq U.a]
      rw [if_pos hUa_in_global_image]
    exact h_card_eq

  have h_size' : ∀ U ∈ fineTubes, (packet U).card ≥ m_Q := by
    intro U hU
    have h : (packet U).card = m_Q := h_size U hU
    rw [h]

  -- 3. Disjointness for separated tubes
  have h_disjoint : ∀ U1 ∈ fineTubes, ∀ U2 ∈ fineTubes,
      U1 ≠ U2 → AreSeparated U1 U2 → Disjoint (packet U1) (packet U2) := by
    intro U1 hU1 U2 hU2 hne hsep
    rcases hsep with (h_diff_slope | h_far)
    · -- Case 1: different slope cells
      rw [h_packet_def U1 hU1, h_packet_def U2 hU2]
      rw [Finset.disjoint_left]
      intro T hT1 hT2
      have h1 : localSlopeCellIndex m T.a = U1.a := (Finset.mem_filter.mp hT1).2
      have h2 : localSlopeCellIndex m T.a = U2.a := (Finset.mem_filter.mp hT2).2
      rw [h1] at h2
      exact h_diff_slope h2
    · -- Case 2: same slope cell, far intercepts
      by_cases h_same_slope : U1.a = U2.a
      · -- same slope cell, far intercepts
        rw [h_packet_def U1 hU1, h_packet_def U2 hU2]
        let q1 := pointForTube U1
        let hq1 : q1 ∈ finePoints := h_point_in U1 hU1
        let q2 := pointForTube U2
        let hq2 : q2 ∈ finePoints := h_point_in U2 hU2
        exact h_geo_disjoint U1 U2 q1 q2 hq1 hq2 h_same_slope h_far
      · -- different slope cells (even though AreSeparated gave far intercepts,
        -- we can still use the slope cell argument)
        rw [h_packet_def U1 hU1, h_packet_def U2 hU2]
        rw [Finset.disjoint_left]
        intro T hT1 hT2
        have h1 : localSlopeCellIndex m T.a = U1.a := (Finset.mem_filter.mp hT1).2
        have h2 : localSlopeCellIndex m T.a = U2.a := (Finset.mem_filter.mp hT2).2
        rw [h1] at h2
        exact h_same_slope h2

  -- Apply separated_packets_estimate
  exact separated_packets_estimate fineTubes TQ_local m_Q hmQ_pos
    packet h_subset h_size' h_disjoint

/-- Convenience version that automatically constructs `pointForTube` from
the biUnion property using Classical.choose. -/
lemma estimate3_bridge_auto
    {n m : ℕ} (hnm : m ≤ n)
    {k : ℕ}
    -- Fine (local) configuration
    (finePoints : Finset (DyadicSquare k))
    (fineFamily : (q : DyadicSquare k) → q ∈ finePoints → Finset (DyadicTube k))
    (fineTubes : Finset (DyadicTube k))
    (h_fineTubes_eq : fineTubes = finePoints.biUnion (fun q =>
      if hq : q ∈ finePoints then fineFamily q hq else ∅))
    -- Global configuration
    (globalPoints : Finset (DyadicSquare n))
    (globalFamily : (p : DyadicSquare n) → p ∈ globalPoints → Finset (DyadicTube n))
    -- Point correspondence
    (p_of_q : (q : DyadicSquare k) → q ∈ finePoints → DyadicSquare n)
    (h_p_of_q_sub : ∀ q hq, p_of_q q hq ∈ globalPoints)
    -- Uniformity
    (m_Q : ℕ) (hmQ_pos : 0 < m_Q)
    (h_slope_preservation : ∀ (q : DyadicSquare k) (hq : q ∈ finePoints),
        (fineFamily q hq).image (fun U : DyadicTube k => U.a) =
        (globalFamily (p_of_q q hq) (h_p_of_q_sub q hq)).image
          (fun T : DyadicTube n => localSlopeCellIndex m T.a))
    (h_uniform : ∀ (q : DyadicSquare k) (hq : q ∈ finePoints) (a : ℤ),
        ((globalFamily (p_of_q q hq) (h_p_of_q_sub q hq)).filter
          (fun T : DyadicTube n => localSlopeCellIndex m T.a = a)).card =
        if a ∈ (globalFamily (p_of_q q hq) (h_p_of_q_sub q hq)).image
          (fun T : DyadicTube n => localSlopeCellIndex m T.a) then m_Q else 0)
    -- TQ_local
    (TQ_local : Finset (DyadicTube n))
    (h_subset_TQ : ∀ (p : DyadicSquare n) (hp : p ∈ globalPoints),
        globalFamily p hp ⊆ TQ_local)
    -- Geometric disjointness for same slope cell, far intercepts
    (h_geo_disjoint : ∀ (U1 U2 : DyadicTube k)
        (q1 q2 : DyadicSquare k) (hq1 : q1 ∈ finePoints) (hq2 : q2 ∈ finePoints),
        U1.a = U2.a → |U1.b - U2.b| ≥ 8 →
        Disjoint
          ((globalFamily (p_of_q q1 hq1) (h_p_of_q_sub q1 hq1)).filter
            (fun T : DyadicTube n => localSlopeCellIndex m T.a = U1.a))
          ((globalFamily (p_of_q q2 hq2) (h_p_of_q_sub q2 hq2)).filter
            (fun T : DyadicTube n => localSlopeCellIndex m T.a = U2.a))) :
    (TQ_local.card : ℝ) ≥ (fineTubes.card : ℝ) * (m_Q : ℝ) / 8 := by
  -- Total version of fineFamily
  let fineFamily' (q : DyadicSquare k) : Finset (DyadicTube k) :=
    if hq : q ∈ finePoints then fineFamily q hq else ∅
  -- Existence of a containing point for each U ∈ fineTubes
  have h_exists : ∀ (U : DyadicTube k), U ∈ fineTubes →
      ∃ (q : DyadicSquare k), q ∈ finePoints ∧ U ∈ fineFamily' q := by
    intro U hU
    have h1 : U ∈ finePoints.biUnion fineFamily' := by
      rw [←h_fineTubes_eq] <;> exact hU
    rcases Finset.mem_biUnion.mp h1 with ⟨q, hq, hU_in⟩
    exact ⟨q, hq, hU_in⟩
  -- Choose a point for each tube
  let pointForTube : DyadicTube k → DyadicSquare k := fun U =>
    if hU : U ∈ fineTubes then
      Classical.choose (h_exists U hU)
    else
      (⟨0, 0⟩ : DyadicSquare k)
  have h_point_in : ∀ (U : DyadicTube k) (hU : U ∈ fineTubes),
      pointForTube U ∈ finePoints := by
    intro U hU
    have h2 : pointForTube U = Classical.choose (h_exists U hU) := by
      simp [pointForTube, hU]
    have h3 := Classical.choose_spec (h_exists U hU)
    rw [h2]
    exact h3.1
  have h_U_in_family' : ∀ (U : DyadicTube k) (hU : U ∈ fineTubes),
      U ∈ fineFamily' (pointForTube U) := by
    intro U hU
    have h2 : pointForTube U = Classical.choose (h_exists U hU) := by
      simp [pointForTube, hU]
    have h3 := Classical.choose_spec (h_exists U hU)
    rw [h2]
    exact h3.2
  have h_U_in_family : ∀ (U : DyadicTube k) (hU : U ∈ fineTubes),
      U ∈ fineFamily (pointForTube U) (h_point_in U hU) := by
    intro U hU
    have h4 : U ∈ fineFamily' (pointForTube U) := h_U_in_family' U hU
    have h5 : fineFamily' (pointForTube U) =
        fineFamily (pointForTube U) (h_point_in U hU) := by
      simp [fineFamily', h_point_in U hU]
    rw [h5] at h4
    exact h4
  exact estimate3_bridge hnm finePoints fineFamily fineTubes h_fineTubes_eq
    globalPoints globalFamily p_of_q h_p_of_q_sub m_Q hmQ_pos
    h_slope_preservation h_uniform TQ_local h_subset_TQ
    pointForTube h_point_in h_U_in_family h_geo_disjoint

/-- **Finalized estimate 3 bridge** with geometric disjointness proved internally.

Uses 9-separation (factor 9) via `separated_packets_estimate_general` with c=8.
The geometric disjointness for same-slope-cell, far-intercept tubes is proved
by `packet_geo_disjointness_core`.

### Inputs

- Fine and global families with slope preservation and uniform packet sizes
- Coarse square Q containing all global points
- Homothety image properties mapping global squares to local squares
- Incidence, parameter strip, and boundedness properties from both configurations
- Scale relation `dyadicDelta k = 2^m * dyadicDelta n`

### Output

`|TQ_local| ≥ |fineTubes| * m_Q / 9`
-/
lemma estimate3_bridge_geo
    {n m : ℕ} (hnm : m ≤ n)
    {k : ℕ}
    (hδ_k_eq : dyadicDelta k = (2 ^ m : ℝ) * dyadicDelta n)
    -- Fine (local) configuration
    (finePoints : Finset (DyadicSquare k))
    (fineFamily : (q : DyadicSquare k) → q ∈ finePoints → Finset (DyadicTube k))
    (fineTubes : Finset (DyadicTube k))
    (h_fineTubes_eq : fineTubes = finePoints.biUnion (fun q =>
      if hq : q ∈ finePoints then fineFamily q hq else ∅))
    -- Global configuration
    (globalPoints : Finset (DyadicSquare n))
    (globalFamily : (p : DyadicSquare n) → p ∈ globalPoints → Finset (DyadicTube n))
    -- Point correspondence
    (p_of_q : (q : DyadicSquare k) → q ∈ finePoints → DyadicSquare n)
    (h_p_of_q_sub : ∀ q hq, p_of_q q hq ∈ globalPoints)
    -- Uniformity
    (m_Q : ℕ) (hmQ_pos : 0 < m_Q)
    (h_slope_preservation : ∀ (q : DyadicSquare k) (hq : q ∈ finePoints),
        (fineFamily q hq).image (fun U : DyadicTube k => U.a) =
        (globalFamily (p_of_q q hq) (h_p_of_q_sub q hq)).image
          (fun T : DyadicTube n => localSlopeCellIndex m T.a))
    (h_uniform : ∀ (q : DyadicSquare k) (hq : q ∈ finePoints) (a : ℤ),
        ((globalFamily (p_of_q q hq) (h_p_of_q_sub q hq)).filter
          (fun T : DyadicTube n => localSlopeCellIndex m T.a = a)).card =
        if a ∈ (globalFamily (p_of_q q hq) (h_p_of_q_sub q hq)).image
          (fun T : DyadicTube n => localSlopeCellIndex m T.a) then m_Q else 0)
    -- TQ_local
    (TQ_local : Finset (DyadicTube n))
    (h_subset_TQ : ∀ (p : DyadicSquare n) (hp : p ∈ globalPoints),
        globalFamily p hp ⊆ TQ_local)
    -- Geometric data
    (Q : DyadicSquare m)
    (hQ_bounded : Q.toSet ⊆ unitSquare)
    (h_contained : ∀ q hq, squareContained hnm (p_of_q q hq) Q)
    (h_image : ∀ q hq, ∀ (x : InductionPlane), x ∈ (p_of_q q hq).toSet →
        homothetyS_Q m Q x ∈ q.toSet)
    (h_local_bounded : ∀ (q : DyadicSquare k) (hq : q ∈ finePoints), q.toSet ⊆ unitSquare)
    (h_global_strip : ∀ p hp T, T ∈ globalFamily p hp → T.IsInAllowedParameterStrip)
    (h_global_inc : ∀ p hp T, T ∈ globalFamily p hp →
        (T.toSet ∩ p.toSet).Nonempty)
    (h_local_strip : ∀ q hq U, U ∈ fineFamily q hq → U.IsInAllowedParameterStrip)
    (h_local_inc : ∀ q hq U, U ∈ fineFamily q hq →
        (U.toSet ∩ q.toSet).Nonempty) :
    (TQ_local.card : ℝ) ≥ (fineTubes.card : ℝ) * (m_Q : ℝ) / 9 := by
  -- Total version of fineFamily
  let fineFamily' (q : DyadicSquare k) : Finset (DyadicTube k) :=
    if hq : q ∈ finePoints then fineFamily q hq else ∅
  -- Existence of a containing point for each U ∈ fineTubes
  have h_exists : ∀ (U : DyadicTube k), U ∈ fineTubes →
      ∃ (q : DyadicSquare k), q ∈ finePoints ∧ U ∈ fineFamily' q := by
    intro U hU
    have h1 : U ∈ finePoints.biUnion fineFamily' := by
      rw [←h_fineTubes_eq] <;> exact hU
    rcases Finset.mem_biUnion.mp h1 with ⟨q, hq, hU_in⟩
    exact ⟨q, hq, hU_in⟩
  -- Choose a point for each tube
  let pointForTube : DyadicTube k → DyadicSquare k := fun U =>
    if hU : U ∈ fineTubes then
      Classical.choose (h_exists U hU)
    else
      (⟨0, 0⟩ : DyadicSquare k)
  have h_point_in : ∀ (U : DyadicTube k) (hU : U ∈ fineTubes),
      pointForTube U ∈ finePoints := by
    intro U hU
    have h2 : pointForTube U = Classical.choose (h_exists U hU) := by
      simp [pointForTube, hU]
    have h3 := Classical.choose_spec (h_exists U hU)
    rw [h2]
    exact h3.1
  have h_U_in_family' : ∀ (U : DyadicTube k) (hU : U ∈ fineTubes),
      U ∈ fineFamily' (pointForTube U) := by
    intro U hU
    have h2 : pointForTube U = Classical.choose (h_exists U hU) := by
      simp [pointForTube, hU]
    have h3 := Classical.choose_spec (h_exists U hU)
    rw [h2]
    exact h3.2
  have h_U_in_family : ∀ (U : DyadicTube k) (hU : U ∈ fineTubes),
      U ∈ fineFamily (pointForTube U) (h_point_in U hU) := by
    intro U hU
    have h4 : U ∈ fineFamily' (pointForTube U) := h_U_in_family' U hU
    have h5 : fineFamily' (pointForTube U) =
        fineFamily (pointForTube U) (h_point_in U hU) := by
      simp [fineFamily', h_point_in U hU]
    rw [h5] at h4
    exact h4

  -- Define packet function
  let packet : DyadicTube k → Finset (DyadicTube n) := fun U =>
    if hU : U ∈ fineTubes then
      let q := pointForTube U
      let hq : q ∈ finePoints := h_point_in U hU
      (globalFamily (p_of_q q hq) (h_p_of_q_sub q hq)).filter
        (fun T : DyadicTube n => localSlopeCellIndex m T.a = U.a)
    else
      ∅

  have h_packet_def (U : DyadicTube k) (hU : U ∈ fineTubes) :
      packet U =
        (globalFamily (p_of_q (pointForTube U) (h_point_in U hU))
          (h_p_of_q_sub (pointForTube U) (h_point_in U hU))).filter
          (fun T : DyadicTube n => localSlopeCellIndex m T.a = U.a) := by
    simp [packet, hU] <;> rfl

  -- Subset: packet U ⊆ TQ_local
  have h_subset : ∀ U ∈ fineTubes, packet U ⊆ TQ_local := by
    intro U hU
    rw [h_packet_def U hU]
    let q := pointForTube U
    let hq : q ∈ finePoints := h_point_in U hU
    let p := p_of_q q hq
    let hp : p ∈ globalPoints := h_p_of_q_sub q hq
    have h1 : (globalFamily p hp).filter (fun T => localSlopeCellIndex m T.a = U.a) ⊆
        globalFamily p hp := Finset.filter_subset _ _
    have h2 : globalFamily p hp ⊆ TQ_local := h_subset_TQ p hp
    exact Finset.Subset.trans h1 h2

  -- Size: |packet U| = m_Q
  have h_size : ∀ U ∈ fineTubes, (packet U).card ≥ m_Q := by
    intro U hU
    rw [h_packet_def U hU]
    let q := pointForTube U
    let hq : q ∈ finePoints := h_point_in U hU
    let p := p_of_q q hq
    let hp : p ∈ globalPoints := h_p_of_q_sub q hq
    have hU_in_family : U ∈ fineFamily q hq := h_U_in_family U hU
    have hUa_in_image : U.a ∈ (fineFamily q hq).image (fun U : DyadicTube k => U.a) :=
      Finset.mem_image.mpr ⟨U, hU_in_family, rfl⟩
    have hUa_in_global_image : U.a ∈ (globalFamily p hp).image
        (fun T : DyadicTube n => localSlopeCellIndex m T.a) := by
      rw [←h_slope_preservation q hq]
      exact hUa_in_image
    have h_card_eq : ((globalFamily p hp).filter
        (fun T : DyadicTube n => localSlopeCellIndex m T.a = U.a)).card = m_Q := by
      rw [h_uniform q hq U.a]
      rw [if_pos hUa_in_global_image]
    rw [h_card_eq]

  -- Disjointness using geometric lemma
  have h_disjoint : ∀ U1 ∈ fineTubes, ∀ U2 ∈ fineTubes,
      U1 ≠ U2 → AreSeparatedN 8 U1 U2 → Disjoint (packet U1) (packet U2) := by
    intro U1 hU1 U2 hU2 hne hsep
    rcases hsep with (h_diff_slope | h_far)
    · -- Different slope cells
      rw [h_packet_def U1 hU1, h_packet_def U2 hU2]
      rw [Finset.disjoint_left]
      intro T hT1 hT2
      have h1 : localSlopeCellIndex m T.a = U1.a := (Finset.mem_filter.mp hT1).2
      have h2 : localSlopeCellIndex m T.a = U2.a := (Finset.mem_filter.mp hT2).2
      rw [h1] at h2
      exact h_diff_slope h2
    · -- Same slope cell, far intercepts (≥ 9)
      by_cases h_same_slope : U1.a = U2.a
      · rw [h_packet_def U1 hU1, h_packet_def U2 hU2]
        rw [Finset.disjoint_left]
        intro T hT1 hT2
        let q1 := pointForTube U1
        let hq1 : q1 ∈ finePoints := h_point_in U1 hU1
        let q2 := pointForTube U2
        let hq2 : q2 ∈ finePoints := h_point_in U2 hU2
        let p1 := p_of_q q1 hq1
        let hp1 : p1 ∈ globalPoints := h_p_of_q_sub q1 hq1
        let p2 := p_of_q q2 hq2
        let hp2 : p2 ∈ globalPoints := h_p_of_q_sub q2 hq2
        have hT_in1 : T ∈ globalFamily p1 hp1 := (Finset.mem_filter.mp hT1).1
        have hT_in2 : T ∈ globalFamily p2 hp2 := (Finset.mem_filter.mp hT2).1
        have h_slope_cell1 : localSlopeCellIndex m T.a = U1.a :=
          (Finset.mem_filter.mp hT1).2
        exact packet_geo_disjointness_core hnm hδ_k_eq Q q1 q2 p1 p2
          (h_contained q1 hq1) (h_contained q2 hq2)
          (h_image q1 hq1) (h_image q2 hq2)
          (h_local_bounded q1 hq1) (h_local_bounded q2 hq2) hQ_bounded
          T (h_global_strip p1 hp1 T hT_in1)
          (h_global_inc p1 hp1 T hT_in1)
          (h_global_inc p2 hp2 T hT_in2)
          U1 U2
          (h_local_strip q1 hq1 U1 (h_U_in_family U1 hU1))
          (h_local_strip q2 hq2 U2 (h_U_in_family U2 hU2))
          (h_local_inc q1 hq1 U1 (h_U_in_family U1 hU1))
          (h_local_inc q2 hq2 U2 (h_U_in_family U2 hU2))
          h_same_slope h_slope_cell1 h_far
      · -- Different slope cells (fallback)
        rw [h_packet_def U1 hU1, h_packet_def U2 hU2]
        rw [Finset.disjoint_left]
        intro T hT1 hT2
        have h1 : localSlopeCellIndex m T.a = U1.a := (Finset.mem_filter.mp hT1).2
        have h2 : localSlopeCellIndex m T.a = U2.a := (Finset.mem_filter.mp hT2).2
        rw [h1] at h2
        exact h_same_slope h2

  have h_main := separated_packets_estimate_general 8 fineTubes TQ_local m_Q hmQ_pos
    packet h_subset h_size h_disjoint
  have h9 : ((8 : ℝ) + 1) = (9 : ℝ) := by norm_num
  simpa [h9] using h_main

end InductionOnScales
