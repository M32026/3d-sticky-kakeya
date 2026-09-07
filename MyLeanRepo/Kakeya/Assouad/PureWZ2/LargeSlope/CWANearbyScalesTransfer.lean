import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# CWA nearby-scales transfer through a covering

Transfer `WZ2PaperPureCWAAtNearbyScales` from an old (source) tube family to a
new (target) tube family related by a finite fiber covering.

## Strategy

Given:
- `oldFamily` at scale `δ`, `newFamily` at scale `δ'`
- `coverMap : Fin newFamily.card → Fin oldFamily.card`
- Each old tube has exactly `N` new tubes in its fiber
- Geometric hypotheses relating new tube carriers to old tube carriers

We transfer each component of `WZ2PaperPureCWAAtNearbyScales`:

1. **Finite error constant**: preserved (same or adjusted constant)
2. **Essentially distinct**: new tubes from different old fibers are separated
3. **Nearby scale cover data**: for each requested scale `rho₀`, map the old
   coarse family and partitioning cover to new ones.

### Cover data transfer

For each old scale-cover datum `(coarse, cover, uniform, rescaledFiber)`:
- Define a new coarse family (typically the same old coarse family, or a
  rescaled version depending on the geometric transformation)
- The new partitioning cover maps each new tube `i` to the same coarse parent
  as its source `coverMap i`
- Full fiber uniformity: the new fiber over a coarse parent has size
  `N × old_fiber_size`, so the uniform constant scales by `N`
- Rescaled fiber data: transfer through the nested covering

### Geometric hypotheses needed

The transfer requires:
- `h_cover_contain`: if `oldCarrier j ⊆ coarseCarrier k`, then
  `newCarrier i ⊆ coarseCarrier k` for all `i` with `coverMap i = j`
  (or containment in a slightly dilated coarse carrier)
- `h_distinct_fibers`: new tubes from different source fibers are not
  contained in each other's 2× dilations
- `h_dilated_disjoint`: doubled fibers remain disjoint under the transfer

These hypotheses are provided by the covering family construction.
-/

namespace Kakeya.Assouad

open Metric Set Finset

/--
Transfer of essentially-distinct property through a covering.

Requires both cross-fiber and same-fiber distinctness hypotheses from the
covering construction.
-/
lemma essentially_distinct_transfer
    {δ δ' : ℝ}
    {oldFamily : Kakeya.Streamlined.TubeFamily δ}
    {newFamily : Kakeya.Streamlined.TubeFamily δ'}
    (coverMap : Fin newFamily.card → Fin oldFamily.card)
    (h_cross_fiber_ed :
      ∀ (i1 i2 : Fin newFamily.card),
        coverMap i1 ≠ coverMap i2 →
        ¬ (newFamily.tube i1).carrier ⊆
            wz2PaperCenteredDilatedCarrier 2 (newFamily.tube i2) ∧
        ¬ (newFamily.tube i2).carrier ⊆
            wz2PaperCenteredDilatedCarrier 2 (newFamily.tube i1))
    (h_same_fiber_ed :
      ∀ (i1 i2 : Fin newFamily.card),
        i1 ≠ i2 → coverMap i1 = coverMap i2 →
        ¬ (newFamily.tube i1).carrier ⊆
            wz2PaperCenteredDilatedCarrier 2 (newFamily.tube i2) ∧
        ¬ (newFamily.tube i2).carrier ⊆
            wz2PaperCenteredDilatedCarrier 2 (newFamily.tube i1)) :
    WZ2PaperOrdinaryIsEssentiallyDistinct newFamily := by
  intro i1 i2 hne
  by_cases h : coverMap i1 = coverMap i2
  · exact h_same_fiber_ed i1 i2 hne h
  · exact h_cross_fiber_ed i1 i2 h

/--
Transfer a partitioning cover from old to new family.

Given an old partitioning cover `(oldFamily, coarse)`, define the new cover
by mapping each new tube to the same coarse parent as its source tube.

Requires: if `oldCarrier j ⊆ coarseCarrier k`, then `newCarrier i ⊆ coarseCarrier k`
for all `i` in the fiber of `j`.
-/
lemma partitioning_cover_transfer
    {δ δ' rho : ℝ}
    {oldFamily : Kakeya.Streamlined.TubeFamily δ}
    {newFamily : Kakeya.Streamlined.TubeFamily δ'}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (coverMap : Fin newFamily.card → Fin oldFamily.card)
    (h_old_cover : WZ2PaperPurePartitioningCover oldFamily coarse)
    (h_containment :
      ∀ (i : Fin newFamily.card) (k : Fin coarse.card),
        (oldFamily.tube (coverMap i)).carrier ⊆ (coarse.tube k).carrier →
        (newFamily.tube i).carrier ⊆ (coarse.tube k).carrier)
    (h_dilated_disjoint :
      ∀ (k1 k2 : Fin coarse.card), k1 ≠ k2 →
        Disjoint
          (wz2PaperOrdinaryDilatedFiberIndices (2 : ℝ) newFamily coarse k1)
          (wz2PaperOrdinaryDilatedFiberIndices (2 : ℝ) newFamily coarse k2)) :
    WZ2PaperPurePartitioningCover newFamily coarse := by
  refine' {
    covers := by
      intro i
      have h_old_covers : ∃ (k : Fin coarse.card),
          coverMap i ∈ wz2PaperOrdinaryFullFiberIndices oldFamily coarse k :=
        h_old_cover.covers (coverMap i)
      rcases h_old_covers with ⟨k, hk⟩
      have h_in_fiber : (oldFamily.tube (coverMap i)).carrier ⊆ (coarse.tube k).carrier := by
        simpa [wz2PaperOrdinaryFullFiberIndices, Finset.mem_filter] using hk
      refine ⟨k, ?_⟩
      simp only [wz2PaperOrdinaryFullFiberIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h_containment i k h_in_fiber
    doubled_fibers_disjoint := h_dilated_disjoint
  }

/--
Full fiber uniformity transfer.

If the new full fiber over each coarse parent has exactly `N` times the old
full fiber count (because each old tube contributes exactly `N` new tubes and
containment is preserved exactly), then the uniformity constant is preserved.

Requires both forward and reverse containment:
- Forward: old tube in coarse fiber → all its new tubes are in the coarse fiber
- Reverse: new tube in coarse fiber → its source is in the coarse fiber
-/
lemma full_fiber_uniform_transfer
    {δ δ' rho : ℝ}
    {oldFamily : Kakeya.Streamlined.TubeFamily δ}
    {newFamily : Kakeya.Streamlined.TubeFamily δ'}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (coverMap : Fin newFamily.card → Fin oldFamily.card)
    (N : ℕ) (hN_pos : 0 < N)
    (C : ENNReal)
    (h_fiber : ∀ j, (Finset.filter (fun i => coverMap i = j) Finset.univ).card = N)
    (h_forward :
      ∀ (i : Fin newFamily.card) (k : Fin coarse.card),
        (oldFamily.tube (coverMap i)).carrier ⊆ (coarse.tube k).carrier →
        (newFamily.tube i).carrier ⊆ (coarse.tube k).carrier)
    (h_reverse :
      ∀ (i : Fin newFamily.card) (k : Fin coarse.card),
        (newFamily.tube i).carrier ⊆ (coarse.tube k).carrier →
        (oldFamily.tube (coverMap i)).carrier ⊆ (coarse.tube k).carrier)
    (h_old_uniform : WZ2PaperPureFullFibersAreCUniform oldFamily coarse C) :
    WZ2PaperPureFullFibersAreCUniform newFamily coarse C := by
  have h_exact : ∀ (k : Fin coarse.card),
      (wz2PaperOrdinaryFullFiberIndices newFamily coarse k).card =
        N * (wz2PaperOrdinaryFullFiberIndices oldFamily coarse k).card := by
    intro k
    let oldFiber := wz2PaperOrdinaryFullFiberIndices oldFamily coarse k
    let newFiber := wz2PaperOrdinaryFullFiberIndices newFamily coarse k
    let fiberOf := fun j : Fin oldFamily.card =>
      Finset.filter (fun i => coverMap i = j) Finset.univ
    have h1 : newFiber = Finset.biUnion oldFiber fiberOf := by
      ext i
      simp only [newFiber, oldFiber, wz2PaperOrdinaryFullFiberIndices,
        Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · intro hni
        have hj : (oldFamily.tube (coverMap i)).carrier ⊆ (coarse.tube k).carrier :=
          h_reverse i k hni
        exact ⟨coverMap i, hj, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩
      · rintro ⟨j, hj_old, h_in_fiber⟩
        have hcov : coverMap i = j := (Finset.mem_filter.mp h_in_fiber).2
        have hj' : (oldFamily.tube (coverMap i)).carrier ⊆ (coarse.tube k).carrier := by
          simpa [hcov] using hj_old
        exact h_forward i k hj'
    have h_disj : ∀ j1 ∈ oldFiber, ∀ j2 ∈ oldFiber, j1 ≠ j2 → Disjoint (fiberOf j1) (fiberOf j2) := by
      intro j1 _ j2 _ hne
      apply Finset.disjoint_left.mpr
      intro i hi1 hi2
      have h1 : coverMap i = j1 := (Finset.mem_filter.mp hi1).2
      have h2 : coverMap i = j2 := (Finset.mem_filter.mp hi2).2
      rw [h1] at h2
      exact hne h2
    have h_card : newFiber.card = ∑ j ∈ oldFiber, (fiberOf j).card := by
      rw [h1, Finset.card_biUnion h_disj]
    rw [h_card]
    have h_sum : ∑ j ∈ oldFiber, (fiberOf j).card = N * oldFiber.card := by
      rw [Finset.sum_congr rfl (fun j _ => h_fiber j)]
      simp [Finset.sum_const]
      <;> ring
    exact h_sum
  intro first second
  have h_old := h_old_uniform first second
  have h_main : (wz2PaperOrdinaryFullFiberCount newFamily coarse first) ≤
      C * (wz2PaperOrdinaryFullFiberCount newFamily coarse second) := by
    simp only [wz2PaperOrdinaryFullFiberCount] at h_old ⊢
    rw [h_exact first, h_exact second]
    have h1 : ((N : ENNReal) * ((wz2PaperOrdinaryFullFiberIndices oldFamily coarse first).card : ENNReal)) ≤
        (N : ENNReal) * (C * ((wz2PaperOrdinaryFullFiberIndices oldFamily coarse second).card : ENNReal)) := by
      gcongr
      <;> exact h_old
    have h2 : (N : ENNReal) * (C * ((wz2PaperOrdinaryFullFiberIndices oldFamily coarse second).card : ENNReal)) =
        C * ((N : ENNReal) * ((wz2PaperOrdinaryFullFiberIndices oldFamily coarse second).card : ENNReal)) := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    simpa [h2] using h1
  exact h_main

/--
A tube carrier is contained in its 2× centered dilation.

Proof: carrier is convex and contains its midpoint c. For any y in carrier,
x = (y+c)/2 is in carrier by convexity, and homothety(c,2)(x) = y.
-/
lemma tube_carrier_self_dilated {rho : ℝ} (hrho_pos : 0 < rho)
    (tube : Kakeya.DeltaTube rho) :
    tube.carrier ⊆ wz2PaperCenteredDilatedCarrier 2 tube := by
  have h_conv : Convex ℝ tube.carrier := wz2_paper_ordinary_tube_carrier_convex tube
  let c : Point3 := wz2PaperTubeMidpoint tube
  have h_mid_in : c ∈ tube.carrier := by
    have h_seg : c ∈ Kakeya.unitSegment tube.base tube.direction := by
      refine ⟨1 / 2, by norm_num, ?_⟩
      simp [c, wz2PaperTubeMidpoint]
    have h_sub : Kakeya.unitSegment tube.base tube.direction ⊆ tube.carrier := by
      intro x hx
      have h0 : Metric.infEDist x (Kakeya.unitSegment tube.base tube.direction) = 0 :=
        Metric.infEDist_zero_of_mem hx
      have h1 : Metric.infEDist x (Kakeya.unitSegment tube.base tube.direction) ≤ ENNReal.ofReal rho := by
        rw [h0] <;> simp
      exact h1
    exact h_sub h_seg
  intro y hy
  let x : Point3 := (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • c
  have hx_in : x ∈ tube.carrier := h_conv hy h_mid_in (by norm_num) (by norm_num) (by norm_num)
  have h_goal : (AffineMap.homothety c (2 : ℝ)) x = y := by
    have h1 : (AffineMap.homothety c (2 : ℝ)) x = (2 : ℝ) • (x - c) + c := by
      simp [AffineMap.homothety_apply] <;> rfl
    rw [h1]
    have h2x : (2 : ℝ) • x = y + c := by
      calc (2 : ℝ) • x
        = (2 : ℝ) • ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • c) := by rfl
      _ = (2 : ℝ) • ((1 / 2 : ℝ) • y) + (2 : ℝ) • ((1 / 2 : ℝ) • c) := by rw [smul_add]
      _ = y + c := by
        have h11 : (2 : ℝ) • ((1 / 2 : ℝ) • y) = y := by
          rw [smul_smul] <;> simp
        have h12 : (2 : ℝ) • ((1 / 2 : ℝ) • c) = c := by
          rw [smul_smul] <;> simp
        rw [h11, h12]
    have h_main : (2 : ℝ) • (x - c) + c = y := by
      have h3 : (2 : ℝ) • (x - c) = (2 : ℝ) • x - (2 : ℝ) • c := by rw [smul_sub]
      rw [h3, h2x]
      have h4 : (2 : ℝ) • c = c + c := by
        simp [two_smul] <;> abel
      rw [h4] <;> abel
    exact h_main
  exact ⟨x, hx_in, h_goal⟩

/--
Full fiber uniformity transfer via doubled-fiber disjointness.

Does NOT require pointwise reverse containment. Instead:
1. Old partitioning cover ⇒ every old tube in exactly one old full fiber
2. New doubled fibers disjoint ⇒ new full fibers pairwise disjoint
3. Forward containment ⇒ old tube in fiber k → all N new tubes in fiber k
4. Therefore new tube i in fiber k ⟺ old tube coverMap i in fiber k
5. Hence newFiber.card = N * oldFiber.card for every k
-/
lemma full_fiber_uniform_via_disjointness
    {δ δ' rho : ℝ}
    (hrho_pos : 0 < rho)
    {oldFamily : Kakeya.Streamlined.TubeFamily δ}
    {newFamily : Kakeya.Streamlined.TubeFamily δ'}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (coverMap : Fin newFamily.card → Fin oldFamily.card)
    (N : ℕ) (hN_pos : 0 < N)
    (C : ENNReal)
    (h_fiber : ∀ j, (Finset.filter (fun i => coverMap i = j) Finset.univ).card = N)
    (h_old_cover : WZ2PaperPurePartitioningCover oldFamily coarse)
    (h_forward :
      ∀ (i : Fin newFamily.card) (k : Fin coarse.card),
        (oldFamily.tube (coverMap i)).carrier ⊆ (coarse.tube k).carrier →
        (newFamily.tube i).carrier ⊆ (coarse.tube k).carrier)
    (h_new_dilated_disjoint :
      ∀ (k1 k2 : Fin coarse.card), k1 ≠ k2 →
        Disjoint
          (wz2PaperOrdinaryDilatedFiberIndices (2 : ℝ) newFamily coarse k1)
          (wz2PaperOrdinaryDilatedFiberIndices (2 : ℝ) newFamily coarse k2))
    (h_old_uniform : WZ2PaperPureFullFibersAreCUniform oldFamily coarse C) :
    WZ2PaperPureFullFibersAreCUniform newFamily coarse C := by
  let oldFiber := fun k : Fin coarse.card =>
    wz2PaperOrdinaryFullFiberIndices oldFamily coarse k
  let newFiber := fun k : Fin coarse.card =>
    wz2PaperOrdinaryFullFiberIndices newFamily coarse k
  let fiberOf := fun j : Fin oldFamily.card =>
    Finset.filter (fun i : Fin newFamily.card => coverMap i = j) (Finset.univ : Finset (Fin newFamily.card))

  -- Full fiber ⊆ 2-dilated fiber
  have h_old_full_sub_dilated : ∀ (k' : Fin coarse.card),
      oldFiber k' ⊆ wz2PaperOrdinaryDilatedFiberIndices (2 : ℝ) oldFamily coarse k' := by
    intro k' j hj
    have h1 : (oldFamily.tube j).carrier ⊆ (coarse.tube k').carrier := by
      simpa [oldFiber, wz2PaperOrdinaryFullFiberIndices] using hj
    have h2 : (coarse.tube k').carrier ⊆ wz2PaperCenteredDilatedCarrier (2 : ℝ) (coarse.tube k') :=
      tube_carrier_self_dilated hrho_pos (coarse.tube k')
    have h3 : (oldFamily.tube j).carrier ⊆ wz2PaperCenteredDilatedCarrier (2 : ℝ) (coarse.tube k') :=
      subset_trans h1 h2
    simpa [wz2PaperOrdinaryDilatedFiberIndices] using h3
  have h_new_full_sub_dilated : ∀ (k' : Fin coarse.card),
      newFiber k' ⊆ wz2PaperOrdinaryDilatedFiberIndices (2 : ℝ) newFamily coarse k' := by
    intro k' j hj
    have h1 : (newFamily.tube j).carrier ⊆ (coarse.tube k').carrier := by
      simpa [newFiber, wz2PaperOrdinaryFullFiberIndices] using hj
    have h2 : (coarse.tube k').carrier ⊆ wz2PaperCenteredDilatedCarrier (2 : ℝ) (coarse.tube k') :=
      tube_carrier_self_dilated hrho_pos (coarse.tube k')
    have h3 : (newFamily.tube j).carrier ⊆ wz2PaperCenteredDilatedCarrier (2 : ℝ) (coarse.tube k') :=
      subset_trans h1 h2
    simpa [wz2PaperOrdinaryDilatedFiberIndices] using h3

  -- New full fibers pairwise disjoint
  have h_new_full_disjoint : ∀ (k1 k2 : Fin coarse.card), k1 ≠ k2 →
      Disjoint (newFiber k1) (newFiber k2) := by
    intro k1 k2 hne
    have h1 : newFiber k1 ⊆ wz2PaperOrdinaryDilatedFiberIndices (2 : ℝ) newFamily coarse k1 :=
      h_new_full_sub_dilated k1
    have h2 : newFiber k2 ⊆ wz2PaperOrdinaryDilatedFiberIndices (2 : ℝ) newFamily coarse k2 :=
      h_new_full_sub_dilated k2
    exact Disjoint.mono h1 h2 (h_new_dilated_disjoint k1 k2 hne)

  -- Forward: biUnion (oldFiber k) fiberOf ⊆ newFiber k
  have h_forward_fiber : ∀ (k : Fin coarse.card),
      Finset.biUnion (oldFiber k) fiberOf ⊆ newFiber k := by
    intro k i hi
    rcases Finset.mem_biUnion.mp hi with ⟨j, hj_old, hj_fiber⟩
    have hcov : coverMap i = j := (Finset.mem_filter.mp hj_fiber).2
    have h_old_in : (oldFamily.tube j).carrier ⊆ (coarse.tube k).carrier := by
      simpa [oldFiber, wz2PaperOrdinaryFullFiberIndices] using hj_old
    have h_old_in' : (oldFamily.tube (coverMap i)).carrier ⊆ (coarse.tube k).carrier := by
      rw [hcov] <;> exact h_old_in
    have h_new_in : (newFamily.tube i).carrier ⊆ (coarse.tube k).carrier :=
      h_forward i k h_old_in'
    simpa [newFiber, wz2PaperOrdinaryFullFiberIndices] using h_new_in

  -- Reverse: newFiber k ⊆ biUnion (oldFiber k) fiberOf
  have h_reverse_fiber : ∀ (i : Fin newFamily.card) (k : Fin coarse.card),
      i ∈ newFiber k → coverMap i ∈ oldFiber k := by
    intro i k hi
    let j := coverMap i
    have h_exists : ∃ (k' : Fin coarse.card), j ∈ oldFiber k' :=
      h_old_cover.covers j
    rcases h_exists with ⟨k', hk'⟩
    have h_j_in : (oldFamily.tube j).carrier ⊆ (coarse.tube k').carrier := by
      simpa [oldFiber, wz2PaperOrdinaryFullFiberIndices] using hk'
    have h_i_in_k' : i ∈ newFiber k' := by
      have h_i_in : (newFamily.tube i).carrier ⊆ (coarse.tube k').carrier :=
        h_forward i k' h_j_in
      simpa [newFiber, wz2PaperOrdinaryFullFiberIndices] using h_i_in
    by_cases h : k = k'
    · rw [h] at *; exact hk'
    · exfalso
      have h_disj : Disjoint (newFiber k) (newFiber k') := h_new_full_disjoint k k' h
      have h_inter : i ∈ (newFiber k) ∩ (newFiber k') :=
        Finset.mem_inter.mpr ⟨hi, h_i_in_k'⟩
      have h_empty : (newFiber k) ∩ (newFiber k') = ∅ :=
        Finset.disjoint_iff_inter_eq_empty.mp h_disj
      rw [h_empty] at h_inter
      simpa using h_inter

  -- Exact equality
  have h_exact : ∀ (k : Fin coarse.card),
      newFiber k = Finset.biUnion (oldFiber k) fiberOf := by
    intro k
    apply Finset.Subset.antisymm
    · intro i hi
      have h_j_in : coverMap i ∈ oldFiber k := h_reverse_fiber i k hi
      have h_i_in_fiber : i ∈ fiberOf (coverMap i) := by
        simp only [fiberOf, Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
      exact Finset.mem_biUnion.mpr ⟨coverMap i, h_j_in, h_i_in_fiber⟩
    · exact h_forward_fiber k

  -- Card equality
  have h_card : ∀ (k : Fin coarse.card),
      (newFiber k).card = N * (oldFiber k).card := by
    intro k
    rw [h_exact k]
    have h_disj : ∀ j1 ∈ oldFiber k, ∀ j2 ∈ oldFiber k, j1 ≠ j2 →
        Disjoint (fiberOf j1) (fiberOf j2) := by
      intro j1 _ j2 _ hne
      apply Finset.disjoint_left.mpr
      intro i hi1 hi2
      have h1 : coverMap i = j1 := (Finset.mem_filter.mp hi1).2
      have h2 : coverMap i = j2 := (Finset.mem_filter.mp hi2).2
      rw [h1] at h2
      exact hne h2
    rw [Finset.card_biUnion h_disj]
    rw [Finset.sum_congr rfl (fun j _ => h_fiber j)]
    simp [Finset.sum_const] <;> ring

  -- Uniformity transfer
  intro first second
  have h_old := h_old_uniform first second
  have h_main : (newFiber first).card ≤ C * (newFiber second).card := by
    simp only [wz2PaperOrdinaryFullFiberCount] at h_old ⊢
    rw [h_card first, h_card second]
    have h1 : ((N : ENNReal) * ((oldFiber first).card : ENNReal)) ≤
        (N : ENNReal) * (C * ((oldFiber second).card : ENNReal)) := by
      gcongr <;> exact h_old
    have h2 : (N : ENNReal) * (C * ((oldFiber second).card : ENNReal)) =
        C * ((N : ENNReal) * ((oldFiber second).card : ENNReal)) := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    simpa [h2] using h1
  exact h_main

/--
Full CWA nearby-scales transfer theorem.

Transfers `WZ2PaperPureCWAAtNearbyScales` from old to new family, given
geometric hypotheses from the covering construction.
-/
theorem cwa_nearby_scales_transfer
    {δ δ' : ℝ}
    {oldFamily : Kakeya.Streamlined.TubeFamily δ}
    {newFamily : Kakeya.Streamlined.TubeFamily δ'}
    (coverMap : Fin newFamily.card → Fin oldFamily.card)
    (N : ℕ) (hN_pos : 0 < N)
    (h_fiber : ∀ j, (Finset.filter (fun i => coverMap i = j) Finset.univ).card = N)
    (C_old C_new : ENNReal)
    (h_C_scale : (N : ENNReal) * C_old ≤ C_new)
    (h_old_cwa : WZ2PaperPureCWAAtNearbyScales oldFamily C_old)
    -- Geometric hypotheses
    (h_fiber_ed :
      ∀ (i1 i2 : Fin newFamily.card),
        coverMap i1 ≠ coverMap i2 →
        ¬ (newFamily.tube i1).carrier ⊆
            wz2PaperCenteredDilatedCarrier 2 (newFamily.tube i2) ∧
        ¬ (newFamily.tube i2).carrier ⊆
            wz2PaperCenteredDilatedCarrier 2 (newFamily.tube i1))
    (h_same_fiber_ed :
      ∀ (i1 i2 : Fin newFamily.card),
        i1 ≠ i2 → coverMap i1 = coverMap i2 →
        ¬ (newFamily.tube i1).carrier ⊆
            wz2PaperCenteredDilatedCarrier 2 (newFamily.tube i2) ∧
        ¬ (newFamily.tube i2).carrier ⊆
            wz2PaperCenteredDilatedCarrier 2 (newFamily.tube i1))
    (h_containment :
      ∀ (rho : ℝ) (coarse : Kakeya.Streamlined.TubeFamily rho)
        (i : Fin newFamily.card) (k : Fin coarse.card),
        (oldFamily.tube (coverMap i)).carrier ⊆ (coarse.tube k).carrier →
        (newFamily.tube i).carrier ⊆ (coarse.tube k).carrier)
    (h_dilated_disjoint :
      ∀ (rho : ℝ) (coarse : Kakeya.Streamlined.TubeFamily rho)
        (k1 k2 : Fin coarse.card), k1 ≠ k2 →
        Disjoint
          (wz2PaperOrdinaryDilatedFiberIndices (2 : ℝ) newFamily coarse k1)
          (wz2PaperOrdinaryDilatedFiberIndices (2 : ℝ) newFamily coarse k2))
    (hδ'_pos : 0 < δ')
    (hC_new_ne_top : C_new ≠ ⊤)
    (hδ_le_one : δ ≤ 1)
    (h_scale_gap : C_old * ENNReal.ofReal δ ≤ C_new * ENNReal.ofReal δ')
    (h_rescaled_fiber_transfer :
      ∀ (rho : ℝ) (coarse : Kakeya.Streamlined.TubeFamily rho)
        (h_old_cover : WZ2PaperPurePartitioningCover oldFamily coarse)
        (h_new_cover : WZ2PaperPurePartitioningCover newFamily coarse)
        (parent : Fin coarse.card),
        Nonempty (WZ2PaperPureUnitRescaledFullFiberData
          (fine := oldFamily) (coarse := coarse) parent C_old) →
        Nonempty (WZ2PaperPureUnitRescaledFullFiberData
          (fine := newFamily) (coarse := coarse) parent C_new)) :
    WZ2PaperPureCWAAtNearbyScales newFamily C_new := by
  have hδ_pos : 0 < δ := h_old_cwa.1
  have h1 : 0 < δ' := hδ'_pos
  have h_old_const : WZ2PaperFiniteErrorConstant C_old := h_old_cwa.2.1
  have h2 : WZ2PaperFiniteErrorConstant C_new := by
    have h_one_le : 1 ≤ C_new := by
      have h1 : 1 ≤ C_old := h_old_const.1
      have hN_one : (1 : ENNReal) ≤ (N : ENNReal) := by exact_mod_cast hN_pos
      have h_mul : C_old ≤ (N : ENNReal) * C_old := by
        have h : (1 : ENNReal) * C_old ≤ (N : ENNReal) * C_old := mul_le_mul_right' hN_one C_old
        simpa using h
      calc (1 : ENNReal)
        ≤ C_old := h1
      _ ≤ (N : ENNReal) * C_old := h_mul
      _ ≤ C_new := h_C_scale
    exact ⟨h_one_le, hC_new_ne_top⟩
  have h3 : WZ2PaperOrdinaryIsEssentiallyDistinct newFamily := by
    intro i1 i2 hne
    by_cases h : coverMap i1 = coverMap i2
    · exact h_same_fiber_ed i1 i2 hne h
    · exact h_fiber_ed i1 i2 h
  have h_C_old_le_new : C_old ≤ C_new := by
    have hN_one : (1 : ENNReal) ≤ (N : ENNReal) := by exact_mod_cast hN_pos
    have h_mul : C_old ≤ (N : ENNReal) * C_old := by
      have h : (1 : ENNReal) * C_old ≤ (N : ENNReal) * C_old := mul_le_mul_right' hN_one C_old
      simpa using h
    exact le_trans h_mul h_C_scale
  have h4 : ∀ (rho₀ : WZ2PaperRequestedScale δ'),
      Nonempty (WZ2PaperPureNearbyScaleCoverData newFamily rho₀ C_new) := by
    intro rho₀
    let r0 : ℝ := rho₀.val
    have hr0_pos : 0 < r0 := by linarith [hδ'_pos, rho₀.property.1]
    have hr0_le_one : r0 ≤ 1 := rho₀.property.2
    have hδ'_le_r0 : δ' ≤ r0 := rho₀.property.1
    by_cases h_case : δ ≤ r0
    · -- Case 1: r0 ≥ δ, request old cover at scale r0
      have hδ_le_r0 : δ ≤ r0 := h_case
      let rho_old : WZ2PaperRequestedScale δ := ⟨r0, hδ_le_r0, hr0_le_one⟩
      have h_old_data : Nonempty (WZ2PaperPureNearbyScaleCoverData oldFamily rho_old C_old) :=
        h_old_cwa.2.2.2 rho_old
      rcases h_old_data with ⟨oldNearby⟩
      let rho : ℝ := oldNearby.rho
      let coarse := oldNearby.scaleData.coarse
      let oldCover := oldNearby.scaleData.cover
      have hrho_pos : 0 < rho := oldNearby.scaleData.rho_pos
      have h_requested_le : r0 ≤ rho := oldNearby.requested_le
      have h_within_old : ENNReal.ofReal rho < C_old * ENNReal.ofReal r0 :=
        oldNearby.within_factor
      have h_within_new : ENNReal.ofReal rho < C_new * ENNReal.ofReal r0 := by
        have h_le : C_old * ENNReal.ofReal r0 ≤ C_new * ENNReal.ofReal r0 := by
          gcongr <;> exact h_C_old_le_new
        exact lt_of_lt_of_le h_within_old h_le
      have h_new_cover : WZ2PaperPurePartitioningCover newFamily coarse :=
        { covers := by
            intro i
            have h_old : ∃ (k : Fin coarse.card),
                coverMap i ∈ wz2PaperOrdinaryFullFiberIndices oldFamily coarse k :=
              oldCover.covers (coverMap i)
            rcases h_old with ⟨k, hk⟩
            have h_cont : (oldFamily.tube (coverMap i)).carrier ⊆ (coarse.tube k).carrier := by
              simpa [wz2PaperOrdinaryFullFiberIndices] using hk
            have h_new_cont : (newFamily.tube i).carrier ⊆ (coarse.tube k).carrier :=
              h_containment rho coarse i k h_cont
            refine ⟨k, ?_⟩
            simpa [wz2PaperOrdinaryFullFiberIndices] using h_new_cont
          doubled_fibers_disjoint := h_dilated_disjoint rho coarse }
      have h_new_uniform_old : WZ2PaperPureFullFibersAreCUniform newFamily coarse C_old :=
        full_fiber_uniform_via_disjointness
          hrho_pos coverMap N hN_pos C_old h_fiber oldCover
          (fun i k h => h_containment rho coarse i k h)
          (h_dilated_disjoint rho coarse)
          oldNearby.scaleData.full_fiber_uniform
      have h_new_uniform : WZ2PaperPureFullFibersAreCUniform newFamily coarse C_new := by
        intro first second
        have h := h_new_uniform_old first second
        calc (wz2PaperOrdinaryFullFiberIndices newFamily coarse first).card
          ≤ C_old * (wz2PaperOrdinaryFullFiberIndices newFamily coarse second).card := h
        _ ≤ C_new * (wz2PaperOrdinaryFullFiberIndices newFamily coarse second).card := by
          gcongr <;> exact h_C_old_le_new
      have h_new_rescaled : ∀ (parent : Fin coarse.card),
          Nonempty (WZ2PaperPureUnitRescaledFullFiberData
            (fine := newFamily) (coarse := coarse) parent C_new) := by
        intro parent
        have h_old_rescaled : Nonempty (WZ2PaperPureUnitRescaledFullFiberData
            (fine := oldFamily) (coarse := coarse) parent C_old) :=
          oldNearby.scaleData.rescaledFiber parent
        exact h_rescaled_fiber_transfer rho coarse oldCover h_new_cover parent h_old_rescaled
      let scaleData : WZ2PaperPureScaleCoverData newFamily rho C_new :=
        { delta_pos := hδ'_pos
          rho_pos := hrho_pos
          coarse := coarse
          cover := h_new_cover
          full_fiber_uniform := h_new_uniform
          rescaledFiber := h_new_rescaled }
      have h_nearby : WZ2PaperPureNearbyScaleCoverData newFamily rho₀ C_new :=
        { rho := rho
          requested_le := h_requested_le
          within_factor := h_within_new
          scaleData := scaleData }
      exact ⟨h_nearby⟩
    · -- Case 2: r0 < δ, request old cover at scale δ
      have h_r0_lt_delta : r0 < δ := by linarith
      let rho_old : WZ2PaperRequestedScale δ := ⟨δ, by linarith, hδ_le_one⟩
      have h_old_data : Nonempty (WZ2PaperPureNearbyScaleCoverData oldFamily rho_old C_old) :=
        h_old_cwa.2.2.2 rho_old
      rcases h_old_data with ⟨oldNearby⟩
      let rho : ℝ := oldNearby.rho
      let coarse := oldNearby.scaleData.coarse
      let oldCover := oldNearby.scaleData.cover
      have hrho_pos : 0 < rho := oldNearby.scaleData.rho_pos
      have h_requested_le : δ ≤ rho := oldNearby.requested_le
      have h_r0_le_rho : r0 ≤ rho := by linarith
      have h_within_old : ENNReal.ofReal rho < C_old * ENNReal.ofReal δ :=
        oldNearby.within_factor
      have h_scale_gap_r0 : C_old * ENNReal.ofReal δ ≤ C_new * ENNReal.ofReal r0 := by
        have h1 : C_old * ENNReal.ofReal δ ≤ C_new * ENNReal.ofReal δ' := h_scale_gap
        have h2 : ENNReal.ofReal δ' ≤ ENNReal.ofReal r0 :=
          ENNReal.ofReal_le_ofReal (by linarith)
        have h3 : C_new * ENNReal.ofReal δ' ≤ C_new * ENNReal.ofReal r0 := by
          gcongr
        exact le_trans h1 h3
      have h_within_new : ENNReal.ofReal rho < C_new * ENNReal.ofReal r0 :=
        lt_of_lt_of_le h_within_old h_scale_gap_r0
      have h_new_cover : WZ2PaperPurePartitioningCover newFamily coarse :=
        { covers := by
            intro i
            have h_old : ∃ (k : Fin coarse.card),
                coverMap i ∈ wz2PaperOrdinaryFullFiberIndices oldFamily coarse k :=
              oldCover.covers (coverMap i)
            rcases h_old with ⟨k, hk⟩
            have h_cont : (oldFamily.tube (coverMap i)).carrier ⊆ (coarse.tube k).carrier := by
              simpa [wz2PaperOrdinaryFullFiberIndices] using hk
            have h_new_cont : (newFamily.tube i).carrier ⊆ (coarse.tube k).carrier :=
              h_containment rho coarse i k h_cont
            refine ⟨k, ?_⟩
            simpa [wz2PaperOrdinaryFullFiberIndices] using h_new_cont
          doubled_fibers_disjoint := h_dilated_disjoint rho coarse }
      have h_new_uniform_old : WZ2PaperPureFullFibersAreCUniform newFamily coarse C_old :=
        full_fiber_uniform_via_disjointness
          hrho_pos coverMap N hN_pos C_old h_fiber oldCover
          (fun i k h => h_containment rho coarse i k h)
          (h_dilated_disjoint rho coarse)
          oldNearby.scaleData.full_fiber_uniform
      have h_new_uniform : WZ2PaperPureFullFibersAreCUniform newFamily coarse C_new := by
        intro first second
        have h := h_new_uniform_old first second
        calc (wz2PaperOrdinaryFullFiberIndices newFamily coarse first).card
          ≤ C_old * (wz2PaperOrdinaryFullFiberIndices newFamily coarse second).card := h
        _ ≤ C_new * (wz2PaperOrdinaryFullFiberIndices newFamily coarse second).card := by
          gcongr <;> exact h_C_old_le_new
      have h_new_rescaled : ∀ (parent : Fin coarse.card),
          Nonempty (WZ2PaperPureUnitRescaledFullFiberData
            (fine := newFamily) (coarse := coarse) parent C_new) := by
        intro parent
        have h_old_rescaled : Nonempty (WZ2PaperPureUnitRescaledFullFiberData
            (fine := oldFamily) (coarse := coarse) parent C_old) :=
          oldNearby.scaleData.rescaledFiber parent
        exact h_rescaled_fiber_transfer rho coarse oldCover h_new_cover parent h_old_rescaled
      let scaleData : WZ2PaperPureScaleCoverData newFamily rho C_new :=
        { delta_pos := hδ'_pos
          rho_pos := hrho_pos
          coarse := coarse
          cover := h_new_cover
          full_fiber_uniform := h_new_uniform
          rescaledFiber := h_new_rescaled }
      have h_nearby : WZ2PaperPureNearbyScaleCoverData newFamily rho₀ C_new :=
        { rho := rho
          requested_le := h_r0_le_rho
          within_factor := h_within_new
          scaleData := scaleData }
      exact ⟨h_nearby⟩
  exact ⟨h1, h2, h3, h4⟩

end Kakeya.Assouad
